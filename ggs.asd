(asdf:defsystem #:ggs
  :description "Rewrite based optimizations"
  :author "Qiantan Hong <qthong@stanford.edu>"
  :license "MIT License"
  :depends-on (:ggs/common :ggs/eqsat :ggs/stochastic)
  :components ((:file "ggs")))

(asdf:defsystem #:ggs/common
  :serial t
  :depends-on (:alexandria
               :serapeum
               :metabang-bind
               :cl-environments)
  :components ((:file "common")
               (:file "util")))

(asdf:defsystem #:ggs/eqsat
  :pathname "eqsat/"
  :serial t
  :depends-on (:alexandria
               :serapeum
               :ggs/common
               :metabang-bind
               :lp-hash-table
               :trivial-garbage
               :trivial-package-local-nicknames
               :linear-programming)
  :components ((:file "package")
               (:file "egraph")
               (:file "match")
               (:file "analysis")
               (:file "run")
               (:file "extract"))
  :in-order-to ((test-op (test-op "ggs/eqsat/tests"))))

(asdf:defsystem #:ggs/stochastic
  :pathname "stochastic/"
  :serial t
  :depends-on (:alexandria
               :serapeum
               :ggs/common
               :lp-hash-table
               :metabang-bind
               :float-features
               :bordeaux-threads)
  :components ((:file "package")
               (:file "node")
               (:file "match")
               (:file "run")))

(asdf:defsystem #:ggs/eqsat/tests
  :pathname "eqsat/tests/"
  :serial t
  :depends-on (:ggs/eqsat
               :fiveam
               :trivial-benchmark)
  :components ((:file "simple")
               (:file "math")
               (:file "matmul"))
  :perform (test-op (o c) (symbol-call :fiveam '#:run! :ggs/eqsat)))

(asdf:defsystem #:ggs/eqsat/benchmark
  :depends-on (:ggs/eqsat/tests)
  :perform (test-op (o c) (symbol-call :fiveam '#:run! :ggs/eqsat/bench)))
