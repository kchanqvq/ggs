(uiop:define-package :ggs/stochastic
    (:use #:cl #:alexandria #:ggs/util #:ggs/common)
  (:import-from #:serapeum #:eval-always #:collecting #:partition #:assort
                #:lret #:defvar-unbound #:with-collectors)
  (:import-from #:metabang-bind #:bind)
  (:reexport #:ggs/common)
  (:export #:stochastic-search #:precompile-stochastic-rule-set))
