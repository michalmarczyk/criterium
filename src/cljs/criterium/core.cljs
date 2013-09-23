;;;; Copyright (c) Hugo Duncan. All rights reserved.

;;;; The use and distribution terms for this software are covered by the
;;;; Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;;;; which can be found in the file epl-v10.html at the root of this distribution.
;;;; By using this software in any fashion, you are agreeing to be bound by
;;;; the terms of this license.
;;;; You must not remove this notice, or any other, from this software.


;;;; Criterium - measures expression computation time over multiple invocations

;;;; Inspired by Brent Broyer's
;;;; http://www.ellipticgroup.com/html/benchmarkingArticle.html
;;;; and also Haskell's Criterion

;;;; Unlike java solutions, this can benchmark general expressions rather than
;;;; just functions.

(ns ^{:author "Hugo Duncan"
      :see-also
      [["http://github.com/hugoduncan/criterium" "Source code"]
       ["http://hugoduncan.github.com/criterium" "API Documentation"]]}
  criterium.core
  "Criterium measures the computation time of an expression.  It is
designed to address some of the pitfalls of benchmarking, and benchmarking on
the JVM in particular.

This includes:
  - statistical processing of multiple evaluations
  - inclusion of a warm-up period, designed to allow the JIT compiler to
    optimise its code
  - purging of gc before testing, to isolate timings from GC state prior
    to testing
  - a final forced GC after testing to estimate impact of cleanup on the
    timing results

Usage:
  (use 'criterium.core)
  (bench (Thread/sleep 1000) :verbose)
  (with-progress-reporting (bench (Thread/sleep 1000) :verbose))
  (report-result (benchmark (Thread/sleep 1000)) :verbose)
  (report-result (quick-bench (Thread/sleep 1000)))

References:
See http://www.ellipticgroup.com/html/benchmarkingArticle.html for a Java
benchmarking library.  The accompanying article describes many of the JVM
benchmarking pitfalls.

See http://hackage.haskell.org/package/criterion for a Haskell benchmarking
library that applies many of the same statistical techniques."
  (:refer-clojure :exclude [format])
  (:use [criterium.stats :only [sqr bootstrap-sample bootstrap-estimate
                                bca-nonparametric quartiles quantile
                                boxplot-outlier-thresholds mean variance
                                bca-to-estimate scale-bootstrap-estimate]])
  (:require criterium.well
            [clojure.set :as set]
            [goog.string :as gstring]
            goog.string.format)
  (:use-macros [criterium.cljs-macros
                :only [timestamp time-body with-progress-reporting
                       benchmark benchmark-round-robin quick-benchmark
                       bench quick-bench]]))

(defn format [& args]
  (apply gstring/format args))

(def ^{:dynamic true} *use-mxbean-for-times* nil)

(def ^{:doc "Fraction of excution time allowed for final cleanup before a
             warning is issued."
       :dynamic true}
  *final-gc-problem-threshold* 0.01)

(def s-to-ms 1000) ; in ms
(def ms-to-s 1e-3) ; in ms

(def ^{:doc "Time period used to let the code run so that jit compiler can do
             its work."
       :dynamic true}
  *warmup-jit-period* (* 10 s-to-ms)) ; in ms

(def ^{:doc "Number of executions required"
       :dynamic true} *sample-count* 60)

(def ^{:doc "Target elapsed time for execution for a single measurement."
       :dynamic true}
  *target-execution-time* (* 1 s-to-ms)) ; in ms

(def ^{:dynamic true}
  *default-benchmark-opts*
  {:max-gc-attempts *max-gc-attempts*
   :samples *sample-count*
   :target-execution-time *target-execution-time*
   :warmup-jit-period *warmup-jit-period*
   :tail-quantile 0.025
   :bootstrap-size 1000})

(def ^{:dynamic true}
  *default-quick-bench-opts*
  {:max-gc-attempts *max-gc-attempts*
   :samples (/ *sample-count* 10)
   :target-execution-time (/ *target-execution-time* 10)
   :warmup-jit-period (/ *warmup-jit-period* 2)
   :tail-quantile 0.025
   :bootstrap-size 500})

;;; Progress reporting
(def ^{:dynamic true} *report-progress* nil)

(defn #^{:skip-wiki true}
  progress
  "Conditionally report progress to *out*."
  [& message]
  (when *report-progress*
    (apply println message)))

(def ^{:dynamic true} *report-debug* nil)

(defn #^{:skip-wiki true}
  debug
  "Conditionally report debug to *out*."
  [& message]
  (when *report-debug*
    (apply println message)))

(def ^{:dynamic true} *report-warn* nil)

(defn #^{:skip-wiki true}
  warn
  "Conditionally report warn to *out*."
  [& message]
  (when *report-warn*
    (apply println "WARNING:" message)))

(defn replace-ret-val-in-time-body-result
  [[elapsed-time _] new-ret-val]
  [elapsed-time new-ret-val])

;;; Memory management
(defn gc-available? []
  (this-as this (exists? (.-gc this))))

(defn gc-function []
  (if (gc-available?)
    ((this-as this (.-gc this)))))

(defn force-gc
  "Force garbage collection and finalisers so that execution time associated
   with this is not incurred later. Up to max-attempts are made.
"
  ([] (force-gc *max-gc-attempts*))
  ([max-attempts]
     (if (gc-available?)
       (gc-function))))

(defn final-gc
  "Time a final clean up of JVM memory. If this time is significant compared to
  the runtime, then the runtime should maybe include this time."
  []
  (when (gc-available?)
    (progress "Final GC...")
    (first (time-body (force-gc)))))

(defn final-gc-warn
  [execution-time final-gc-time]
  (progress "Checking GC...")
  (when (gc-available?)
    (let [fractional-time (/ final-gc-time execution-time)
          final-gc-result [(> fractional-time *final-gc-problem-threshold*)
                           fractional-time
                           final-gc-time]]
      (when (first final-gc-result)
        (println
         "WARNING: Final GC required"
         (* 100.0 (second final-gc-result))
         "% of runtime"))
      final-gc-result)))

;;; ## Core timing loop

;;; A mutable field is used to store the result of each function call, to
;;; prevent JIT optimising away the expression entirely.

(defprotocol MutablePlace
  "Provides a mutable place"
  (set-place [_ v] "Set mutable field to value.")
  (get-place [_] "Get mutable field value."))

(deftype Unsynchronized [^:mutable v]
  MutablePlace
  (set-place [_ value] (set! v value))
  (get-place [_] v))

(deftype UidPlace [^:mutable v]
  MutablePlace
  (set-place [_ value]
    (let [h (goog/getUid value)]
      (set! v (bit-xor v h))))
  (get-place [_]
    v))

#_
(def mutable-place (Unsynchronized. nil))

(def mutable-place (UidPlace. 0))

(defn execute-expr-core-timed-part
 "Performs the part of execute-expr where we actually measure the elapsed run
  time.  Evaluates `(f)` `n` times, each time saving the return value as an
  Object in `mutable-place`.

  The idea is that except for the call to (f), the only things done during each
  iteration are a few arithmetic operations and comparisons to 0 on primitive
  longs, and the storage of the return value.

  The JVM is not free to optimize away the calls to f because the return values
  are saved in `mutable-place`.

  This array is at most +max-obj-array-size+ elements long, to save
  memory.  An artificially intelligent JVM might be able to determine
  that if n is larger than +max-obj-array-size+, some of the return
  values are overwritten and thus those calls need not be made.  I
  doubt we will see that kind of optimization any time soon, and
  perhaps some JVM rules even prohibit doing so since the writes to
  ret-vals-arr could potentially be read by a different thread."
  [n f]
  (time-body
   (loop [i (long (dec n))
          v (f)]
     (set-place mutable-place v)
     (if (pos? i)
       (recur (unchecked-dec i) (f))
       v))))

;;; ## Execution
(defn execute-expr
  "Time the execution of `n` invocations of `f`. See
  `execute-expr-core-timed-part`."
  [n f]
  (let [time-and-ret (execute-expr-core-timed-part n f)]
    (get-place mutable-place) ;; just for good measure, use the mutable value
    time-and-ret))

(defn collect-samples
  [sample-count execution-count f gc-before-sample]
  {:pre [(pos? sample-count)]}
  (let [result (object-array sample-count)]
    (loop [i (long 0)]
      (if (< i sample-count)
        (do
          (when gc-before-sample
            (force-gc))
          (aset result i (execute-expr execution-count f))
          (recur (unchecked-inc i)))
        result))))

;;; Compilation
(defn warmup-for-jit
  "Run expression for the given amount of time to enable JIT compilation."
  [warmup-period f]
  (progress "Warming up for JIT optimisations" warmup-period "...")
  (let [t (max 1 (first (time-body (f))))
        _ (debug "  initial t" t)
        [t n] (if (< t 0.1)           ; 100us
                (let [n (/ 1 t)]
                  [(first (execute-expr n f)) n])
                [t 1])
        p (/ warmup-period t)
        c (long (max 1 (* n (/ p 5))))]
    (debug "  using t" t "n" n)
    (debug "  using execution-count" c)
    (loop [elapsed (long t)
           count (long n)]
      (debug "  elapsed" elapsed " count" count)
      (if (> elapsed warmup-period)
        [elapsed count]
        (recur (+ elapsed (long (first (execute-expr c f))))
               (+ count c))))))

;;; Execution parameters
(defn estimate-execution-count
  "Estimate the number of executions required in order to have at least the
   specified execution period, check for the jvm to have constant class loader
   and compilation state."
  [period f gc-before-sample estimated-fn-time]
  (progress "Estimating execution count ...")
  (debug " estimated-fn-time" estimated-fn-time)
  (loop [n (max 1 (long (/ period estimated-fn-time 5)))]
    (let [t (ffirst (collect-samples 1 n f gc-before-sample))
          ;; It is possible for small n and a fast expression to get
          ;; t=0 nsec back from collect-samples.  This is likely due
          ;; to how (System/nanoTime) quantizes the time on some
          ;; systems.
          t (max 1 t)]
      (debug " ..." n)
      (if (>= t period)
        n
        (recur (if (>= t period)
                 n
                 (min (* 2 n) (inc (long (* n (/ period t)))))))))))


;; benchmark
(defn run-benchmark
  "Benchmark an expression. This tries its best to eliminate sources of error.
   This also means that it runs for a while.  It will typically take 70s for a
   quick test expression (less than 1s run time) or 10s plus 60 run times for
   longer running expressions."
  [sample-count warmup-jit-period target-execution-time f gc-before-sample
   overhead]
  (force-gc)
  (let [first-execution (time-body (f))
        [warmup-t warmup-n] (warmup-for-jit warmup-jit-period f)
        n-exec (estimate-execution-count
                target-execution-time f gc-before-sample
                (max (long (/ warmup-t warmup-n)) 1e-3))
        total-overhead (long (* (or overhead 0) 1e3 n-exec))
        _   (progress "Sampling ...")
        _   (debug
             "Running with\n sample-count" sample-count \newline
             "exec-count" n-exec \newline
             "overhead[s]" overhead \newline
             "total-overhead[ns]" total-overhead)
        _   (force-gc)
        samples (collect-samples sample-count n-exec f gc-before-sample)
        final-gc-time (final-gc)
        sample-times (->> samples
                          (map first)
                          (map #(- % total-overhead)))
        total (reduce + 0 sample-times)
        final-gc-result (final-gc-warn total final-gc-time)]
    {:execution-count n-exec
     :sample-count sample-count
     :samples sample-times
     :results (map second samples)
     :total-time (/ total 1e3)
     :warmup-time warmup-t
     :warmup-executions warmup-n
     :final-gc-time final-gc-time
     :overhead overhead}))


(defn run-benchmarks-round-robin
  "Benchmark multiple expressions in a 'round robin' fashion.  Very
similar to run-benchmark, except it takes multiple expressions in a
sequence instead of only one (each element of the sequence should be a
map with keys :f and :expr-string).  It runs the following steps in
sequence:

1. Execute each expr once

2. Run expression 1 for at least warmup-jit-period nanoseconds so the
   JIT has an opportunity to optimize it.  Then do the same for each
   of the other expressions.

3. Run expression 1 many times to estimate how many times it must be
   executed to take a total of target-execution-time nanoseconds.  The
   result is a number of iterations n-exec1 for expression 1.  Do the
   same for each of the other expressions, each with the same
   target-execution-time, each resulting in its own independent number
   of executions.

4. Run expression 1 n-exec1 times, measuring the total elapsed time.
   Do the same for the rest of the expressions.

5. Repeat step 4 a total of sample-count times."
  [sample-count warmup-jit-period target-execution-time exprs gc-before-sample]
  (force-gc)
  (let [first-executions (map (fn [{:keys [f]}] (time-body (f))) exprs)]
    (progress (format "Warming up %d expression for %.2e sec each:"
                      (count exprs) (/ warmup-jit-period 1.0e3)))
    (doseq [{:keys [f expr-string]} exprs]
      (progress (format "    %s..." expr-string))
      (warmup-for-jit warmup-jit-period f))
    (progress
     (format
      "Estimating execution counts for %d expressions.  Target execution time = %.2e sec:"
                      (count exprs) (/ target-execution-time 1.0e3)))
    (let [exprs (map-indexed
                 (fn [idx {:keys [f expr-string] :as expr}]
                   (progress (format "    %s..." expr-string))
                   (assoc expr :index idx
                          :n-exec (estimate-execution-count
                                   target-execution-time f
                                   gc-before-sample
                                   nil)))
                 exprs)
;;          _   (progress
;;               "Running with sample-count" sample-count
;;               "exec-count" n-exec  ; tbd: update)
          all-samples (doall
                       (for [i (range sample-count)]
                         (do
                           (progress
                            (format
                             "    Running sample %d/%d for %d expressions:"
                             (inc i) sample-count (count exprs)))
                           (doall
                            (for [{:keys [f n-exec expr-string] :as expr} exprs]
                              (do
                                (progress (format "        %s..." expr-string))
                                (assoc expr
                                  :sample (first
                                           (collect-samples
                                            1 n-exec f gc-before-sample)))))))))

          ;; 'transpose' all-samples so that all samples for a
          ;; particular expression are in a sequence together, and
          ;; all-samples is a sequence of one map per expression.
          all-samples (group-by :index (apply concat all-samples))
          all-samples
          (map (fn [[idx data-seq]]
                 (let [expr (dissoc (first data-seq) :sample)
                       n-exec (:n-exec expr)
                       samples (map :sample data-seq)
                       final-gc-time (final-gc)
                       sample-times (map first samples)
                       total (reduce + 0 sample-times)
                       ;; TBD: Doesn't make much sense to attach final
                       ;; GC warning to the expression that happened
                       ;; to be first in the sequence, but that is
                       ;; what this probably does right now.  Think
                       ;; what might be better to do.
                       final-gc-result (final-gc-warn total final-gc-time)]
                   {:execution-count n-exec
                    :sample-count sample-count
                    :samples sample-times
                    :results (map second samples)
                    :total-time (/ total 1e9)}))
               all-samples)]
      all-samples)))


(defn bootstrap-bca
  "Bootstrap a statistic. Statistic can produce multiple statistics as a vector
   so you can use juxt to pass multiple statistics.
   http://en.wikipedia.org/wiki/Bootstrapping_(statistics)"
  [data statistic size alpha rng-factory]
  (progress "Bootstrapping ...")
  (let [bca (bca-nonparametric data statistic size alpha rng-factory)]
    (if (vector? bca)
      (bca-to-estimate alpha bca)
      (map (partial bca-to-estimate alpha) bca))))

(defn bootstrap
  "Bootstrap a statistic. Statistic can produce multiple statistics as a vector
   so you can use juxt to pass multiple statistics.
   http://en.wikipedia.org/wiki/Bootstrapping_(statistics)"
  [data statistic size rng-factory]
  (progress "Bootstrapping ...")
  (let [samples (bootstrap-sample data statistic size rng-factory)
        transpose (fn [data] (apply map vector data))]
    (if (vector? (first samples))
      (map bootstrap-estimate samples)
      (bootstrap-estimate samples))))

;;; Outliers

(defn outlier-effect
  "Return a keyword describing the effect of outliers on the estimate of mean
  runtime."
  [var-out-min]
  (cond
    (< var-out-min 0.01) :unaffected
    (< var-out-min 0.1) :slight
    (< var-out-min 0.5) :moderate
    :else :severe))

(defn point-estimate [estimate]
  (first estimate))

(defn point-estimate-ci [estimate]
  (last estimate))

(defn outlier-significance
  "Find the significance of outliers given boostrapped mean and variance
estimates.
See http://www.ellipticgroup.com/misc/article_supplement.pdf, p17."
  [mean-estimate variance-estimate n]
  (progress "Checking outlier significance")
  (let [mean-block (point-estimate mean-estimate)
        variance-block (point-estimate variance-estimate)
        std-dev-block (js/Math.sqrt variance-block)
        mean-action (/ mean-block n)
        mean-g-min (/ mean-action 2)
        sigma-g (min (/ mean-g-min 4) (/ std-dev-block (js/Math.sqrt n)))
        variance-g (* sigma-g sigma-g)
        c-max (fn [t-min]
                (let [j0 (- mean-action t-min)
                      k0 (- (* n n j0 j0))
                      k1 (+ variance-block (- (* n variance-g)) (* n j0 j0))
                      det (- (* k1 k1) (* 4 variance-g k0))]
                  (js/Math.floor (/ (* -2 k0) (+ k1 (js/Math.sqrt det))))))
        var-out (fn [c]
                  (let [nmc (- n c)]
                    (* (/ nmc n) (- variance-block (* nmc variance-g)))))
        min-f (fn [f q r]
                (min (f q) (f r)))
        ]
    (/ (min-f var-out 1 (min-f c-max 0 mean-g-min)) variance-block)))


(defrecord OutlierCount [low-severe low-mild high-mild high-severe])

(defn outlier-count
  [low-severe low-mild high-mild high-severe]
  (OutlierCount. low-severe low-mild high-mild high-severe))


(defn add-outlier [low-severe low-mild high-mild high-severe counts x]
  (outlier-count
   (if (<= x low-severe)
     (inc (:low-severe counts))
     (:low-severe counts))
   (if (< low-severe x low-mild)
     (inc (:low-mild counts))
     (:low-mild counts))
   (if (> high-severe x high-mild)
     (inc (:high-mild counts))
     (:high-mild counts))
   (if (>= x high-severe)
     (inc (:high-severe counts))
     (:high-severe counts))))

(defn outliers
  "Find the outliers in the data using a boxplot technique."
  [data]
  (progress "Finding outliers ...")
  (reduce (apply partial add-outlier
                 (apply boxplot-outlier-thresholds
                        ((juxt first last) (quartiles (sort data)))))
          (outlier-count 0 0 0 0)
          data))

;;; options
(defn extract-report-options
  "Extract reporting options from the given options vector.  Returns a two
  element vector containing the reporting options followed by the non-reporting
  options"
  [opts]
  (let [known-options #{:os :runtime :verbose}
        option-set (set opts)]
    [(set/intersection known-options option-set)
     (remove #(contains? known-options %1) opts)]))

(defn add-default-options [options defaults]
  (let [time-periods #{:warmup-jit-period :target-execution-time}]
    (merge defaults
           (into {} (map #(if (contains? time-periods (first %1))
                            [(first %1) (* (second %1) s-to-ms)]
                            %1)
                         options)))))

;;; User top level functions
(defn benchmark-stats [times opts]
  (let [outliers (outliers (:samples times))
        tail-quantile (:tail-quantile opts)
        stats (bootstrap-bca
               (map double (:samples times))
               (juxt
                mean
                variance
                (partial quantile tail-quantile)
                (partial quantile (- 1.0 tail-quantile)))
               (:bootstrap-size opts) [0.5 tail-quantile (- 1.0 tail-quantile)]
               criterium.well/well-rng-1024a)
        analysis (outlier-significance (first stats) (second stats)
                                       (:sample-count times))
        sqr (fn [x] (* x x))
        m (mean (map double (:samples times)))
        s (js/Math.sqrt (variance (map double (:samples times))))]
    (merge times
           {:outliers outliers
            :mean (scale-bootstrap-estimate
                   (first stats) (/ 1e-3 (:execution-count times)))
            :sample-mean (scale-bootstrap-estimate
                          [m [(- m (* 3 s)) (+ m (* 3 s))]]
                          (/ 1e-3 (:execution-count times)))
            :variance (scale-bootstrap-estimate
                       (second stats) (sqr (/ 1e-3 (:execution-count times))))
            :sample-variance (scale-bootstrap-estimate
                              [ (sqr s) [0 0]]
                              (sqr (/ 1e-3 (:execution-count times))))
            :lower-q (scale-bootstrap-estimate
                       (nth stats 2) (/ 1e-3 (:execution-count times)))
            :upper-q (scale-bootstrap-estimate
                       (nth stats 3) (/ 1e-3 (:execution-count times)))
            :outlier-variance analysis
            :tail-quantile (:tail-quantile opts)
            :options opts})))

(defn benchmark*
  "Benchmark a function. This tries its best to eliminate sources of error.
   This also means that it runs for a while.  It will typically take 70s for a
   fast test expression (less than 1s run time) or 10s plus 60 run times for
   longer running expressions."
  [f {:keys [samples warmup-jit-period target-execution-time gc-before-sample
             overhead] :as options}]
  (let [{:keys [samples warmup-jit-period target-execution-time
                gc-before-sample overhead] :as opts}
        (merge *default-benchmark-opts* options)
        times (run-benchmark
               samples warmup-jit-period target-execution-time f opts overhead)]
    (benchmark-stats times opts)))

(defn benchmark-round-robin*
  [exprs options]
  (let [opts (merge *default-benchmark-opts* options)
        times (run-benchmarks-round-robin
               (:samples opts)
               (:warmup-jit-period opts)
               (:target-execution-time opts)
               exprs
               (:gc-before-sample opts))]
    (map #(benchmark-stats % opts) times)))

(defn quick-benchmark*
  "Benchmark an expression. Less rigorous benchmark (higher uncertainty)."
  [f {:as options}]
  (benchmark* f (merge *default-quick-bench-opts* options)))

(defn report
  "Print format output"
  [format-string & values]
  (print (apply format format-string values)))

(defn scale-time
  "Determine a scale factor and unit for displaying a time."
  [measurement]
  (cond
   (> measurement 60) [(/ 60) "min"]
   (< measurement 1e-6) [1e9 "ns"]
   (< measurement 1e-3) [1e6 "µs"]
   (< measurement 1) [1e3 "ms"]
   :else [1 "sec"]))

(defn format-value [value scale unit]
  (format "%f %s" (* scale value) unit))

(defn report-estimate
  [msg estimate significance]
  (let [mean (first estimate)
        [factor unit] (scale-time mean)]
    (apply
     report "%32s : %s  %2.1f%% CI: (%s, %s)\n"
     msg
     (format-value mean factor unit)
     (* significance 100)
     (map #(format-value % factor unit) (last estimate)))))

(defn report-point-estimate
  ([msg estimate]
     (let [mean (first estimate)
           [factor unit] (scale-time mean)]
       (report "%32s : %s\n" msg (format-value mean factor unit))))
  ([msg estimate quantile]
     (let [mean (first estimate)
           [factor unit] (scale-time mean)]
       (report
        "%32s : %s (%4.1f%%)\n"
        msg (format-value mean factor unit) (* quantile 100)))))

(defn report-estimate-sqrt
  [msg estimate significance]
  (let [mean (js/Math.sqrt (first estimate))
        [factor unit] (scale-time mean)]
    (apply
     report "%32s : %s  %2.1f%% CI: (%s, %s)\n"
     msg
     (format-value mean factor unit)
     (* significance 100)
     (map #(format-value (js/Math.sqrt %) factor unit) (last estimate)))))

(defn report-point-estimate-sqrt
  [msg estimate]
  (let [mean (js/Math.sqrt (first estimate))
        [factor unit] (scale-time mean)]
    (report "%32s : %s\n" msg (format-value mean factor unit))))

(defn report-outliers [results]
  (let [outliers (:outliers results)
        values (vals outliers)
        labels {:unaffected "unaffected"
                :slight "slightly inflated"
                :moderate "moderately inflated"
                :severe "severely inflated"}
        sample-count (:sample-count results)
        types ["low-severe" "low-mild" "high-mild" "high-severe"]]
    (when (some pos? values)
      (let [sum (reduce + values)]
        (report
         "\nFound %d outliers in %d samples (%2.4f %%)\n"
         sum sample-count (* 100.0 (/ sum sample-count))))
      (doseq [[v c] (partition 2 (interleave (filter pos? values) types))]
        (report "\t%s\t %d (%2.4f %%)\n" c v (* 100.0 (/ v sample-count))))
      (report " Variance from outliers : %2.4f %%"
              (* (:outlier-variance results) 100.0))
      (report " Variance is %s by outliers\n"
              (-> (:outlier-variance results) outlier-effect labels)))))

(defn report-result [results & opts]
  (let [verbose (some #(= :verbose %) opts)]
    (println "Evaluation count :" (* (:execution-count results)
                                     (:sample-count results))
             "in" (:sample-count results) "samples of"
             (:execution-count results) "calls.")

    (when verbose
      (report-point-estimate
       "Execution time sample mean" (:sample-mean results)))
    (report-point-estimate "Execution time mean" (:mean results))
    (when verbose
      (report-point-estimate-sqrt
       "Execution time sample std-deviation" (:sample-variance results)))
    (report-point-estimate-sqrt
     "Execution time std-deviation" (:variance results))
    (report-point-estimate
     "Execution time lower quantile"
     (:lower-q results) (:tail-quantile results))
    (report-point-estimate
     "Execution time upper quantile"
     (:upper-q results) (- 1.0 (:tail-quantile results)))
    (when-let [overhead (:overhead results)]
      (when (pos? overhead)
        (report-point-estimate "Overhead used" [overhead])))
    (report-outliers results)))

(defn estimate-overhead
  "Calculate a conservative estimate of the timing loop overhead."
  []
  (-> (benchmark 0 {:warmup-jit-period (* 10 s-to-ms)
                    :samples 10
                    :target-execution-time (* 0.5 s-to-ms)
                    :overhead 0})
      :lower-q
      first))

(def estimatated-overhead-cache (atom nil))

(defn estimatated-overhead!
  "Sets the estimated overhead."
  []
  (progress "Estimating sampling overhead")
  (swap! estimatated-overhead-cache (constantly (estimate-overhead))))

(defn estimatated-overhead
  []
  (or @estimatated-overhead-cache
      (estimatated-overhead!)))
