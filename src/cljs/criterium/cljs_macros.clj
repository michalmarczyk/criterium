(ns criterium.cljs-macros
  (:use [criterium.core :exclude [timestamp time-body with-progress-reporting
                                  benchmark benchmark-round-robin
                                  quick-benchmark extract-report-options
                                  bench quick-bench]])
  (:require [clojure.set :as set]))

;;; Time reporting
(defmacro timestamp
  "Obtain a timestamp"
  []
  `(.getTime (js/Date.)))

;;; Execution timing
(defmacro time-body
  "Returns a vector containing execution time and result of specified function."
  ([expr pre]
     `(do ~pre
          (time-body ~expr)))
  ([expr]
     `(let [start# (timestamp)
            ret# ~expr
            finish# (timestamp)]
        [(- finish# start#) ret#])))

;;; User top level functions
(defmacro with-progress-reporting
  "Macro to enable progress reporting during the benchmark."
  [expr]
  `(binding [criterium.core/*report-progress* true]
     ~expr))

(defmacro benchmark
  "Benchmark an expression. This tries its best to eliminate sources of error.
   This also means that it runs for a while.  It will typically take 70s for a
   fast test expression (less than 1s run time) or 10s plus 60 run times for
   longer running expressions."
  [expr options]
  `(criterium.core/benchmark* (fn [] ~expr) ~options))

(defmacro benchmark-round-robin
  [exprs options]
  (let [wrap-exprs (fn [exprs]
                     (cons 'list
                           (map (fn [expr]
                                  {:f `(fn [] ~expr)
                                   :expr-string (str expr)})
                                exprs)))]
    `(benchmark-round-robin* ~(wrap-exprs exprs) ~options)))

(defmacro quick-benchmark
  "Benchmark an expression. Less rigorous benchmark (higher uncertainty)."
  [expr options]
  `(quick-benchmark* (fn [] ~expr) ~options))

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

(defmacro bench
  "Convenience macro for benchmarking an expression, expr.  Results are reported
  to *out* in human readable format. Options for report format are: :os,
:runtime, and :verbose."
  [expr & opts]
  (let [[report-options options] (extract-report-options opts)]
    `(report-result
      (benchmark
       ~expr
       (merge {:overhead (criterium.core/estimatated-overhead)}
              ~(when (seq options) (apply hash-map options))))
      ~@report-options)))

(defmacro quick-bench
  "Convenience macro for benchmarking an expression, expr.  Results are reported
to *out* in human readable format. Options for report format are: :os,
:runtime, and :verbose."
  [expr & opts]
  (let [[report-options options] (extract-report-options opts)]
    `(report-result
      (quick-benchmark
       ~expr
       (merge {:overhead (estimatated-overhead)}
              ~(when (seq options) (apply hash-map options))))
      ~@report-options)))

;;; Macros to help convert unsigned algorithm to our implementation with signed
;;; integers.
;;; unsign is used to convert the [0.5,-0.5] range back onto [1,0]
(defmacro unsign
  "Convert a result based on a signed integer, and convert it to what it would
   have been for an unsigned integer."
  [x]
  `(let [v# ~x]
     (if (neg? v#) (+ 1 v#) v#)))

(def int-max (bit-or (bit-shift-left Integer/MAX_VALUE 1) 1))

(defmacro limit-bits [x]
  `(bit-and ~int-max ~x))

(defmacro mat0-pos [t v]
  `(let [v# ~v] (bit-xor v# (bit-shift-right v# ~t))))

(defmacro mat0-neg [t v]
  `(let [v# ~v]
     (long (bit-xor v# (limit-bits (bit-shift-left v# (- ~t)))))))

(defmacro add-mod-32 [a b]
  `(long (bit-and (+ ~a ~b) 0x01f)))
