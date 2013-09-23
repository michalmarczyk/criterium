(defproject criterium "0.4.3-SNAPSHOT"
  :description "Benchmarking library"
  :url "https://github.com/hugoduncan/criterium"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :scm {:url "git@github.com:hugoduncan/criterium.git"}
  :dependencies [[org.clojure/clojure "1.5.1"]]
  :local-repo-classpath true
  :source-paths ["src/clj" "src/cljs"]
  :profiles {:dev {:dependencies [[org.clojure/clojure "1.5.1"]
                                  [org.clojure/clojurescript "0.0-1889"]]
                   :plugins [[lein-cljdbuild "0.3.3"]]}})
