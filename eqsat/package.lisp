(uiop:define-package :ggs/eqsat
    (:use #:cl #:alexandria #:ggs/util #:ggs/common)
  (:import-from #:serapeum #:lret #:lret* #:-> #:collecting #:defvar-unbound)
  (:import-from #:bind #:bind)
  (:reexport #:ggs/common)
  (:export #:make-enode #:enode-fsym #:enode-arg #:enode-n-args
           #:do-enode-args #:map-enode-args #:make-egraph #:list-enodes
           #:enode-representative-p #:enode-canonical-p #:enode-eclass-info
           #:*egraph* #:enode-find #:enode-merge #:egraph-rebuild #:check-egraph
           #:egraph-n-enodes #:egraph-n-eclasses #:enode-analysis-data
           #:precompile-eqsat-rule-set #:term-enode #:run-rewrites
           #:build-term #:greedy-select #:greedy-extract #:lp-select #:lp-extract))

(serapeum:eval-always
  (trivial-package-local-nicknames:add-package-local-nickname
   '#:lp '#:linear-programming '#:ggs/eqsat))
