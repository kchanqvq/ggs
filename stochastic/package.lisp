(uiop:define-package :ggs/stochastic
    (:use #:cl #:alexandria #:ggs/common)
  (:import-from #:serapeum #:eval-always #:collecting #:partition)
  (:import-from #:metabang-bind #:bind)
  (:export #:stochastic-search
           #:define-tree-sum-cost #:defrw #:defrw* #:precompile-rule-set #:yield-rewrite))
