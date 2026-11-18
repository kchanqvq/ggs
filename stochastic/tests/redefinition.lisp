(in-package :ggs/stochastic/tests)

;;; Compiled rule sets are cached.  Redefining an analysis or a rule set must
;;; not reuse code compiled for the old definition, and redefining it back must
;;; give the old behaviour again.

(def-suite* :stochastic-redefinition :in :ggs/stochastic)

(defun redefine (&rest forms)
  (dolist (form forms) (eval form)))

(defun redef-cost-form (f g)
  `(define-analysis (redef-cost :merge #'min :bottom +inf-cost+ :type cost)
     ((f ?x) (+ ,f (redef-cost ?x)))
     ((g ?x) (+ ,g (redef-cost ?x)))
     ((?f) 1)))

(def-test redefine-cost-analysis ()
  (redefine '(defrw* redef-swap ((f ?x) (g ?x)) ((g ?x) (f ?x))))
  (flet ((best (f g)
           (redefine (redef-cost-form f g))
           (subseq (multiple-value-list (search* '(f x) 'redef-swap 'redef-cost)) 0 2)))
    (is (equal '((f x) 2) (best 1 5)))
    (is (equal '((g x) 2) (best 5 1)))
    (is (equal '((f x) 2) (best 1 5)))))

(def-test redefine-rule-set ()
  (redefine '(define-analysis (redef-weight :merge #'min :bottom +inf-cost+ :type cost)
              ((f ?x) (+ 5 (redef-weight ?x)))
              ((g ?x) (+ 3 (redef-weight ?x)))
              ((h ?x) (+ 1 (redef-weight ?x)))
              ((?f) 1)))
  (redefine '(defrw* redef-rules ((f ?x) (g ?x))))
  (is (equal '(g x) (search* '(f x) 'redef-rules 'redef-weight)))
  (redefine '(defrw* redef-rules ((f ?x) (h ?x))))
  (is (equal '(h x) (search* '(f x) 'redef-rules 'redef-weight)))
  (redefine '(defrw* redef-rules ((f ?x) (g ?x))))
  (is (equal '(g x) (search* '(f x) 'redef-rules 'redef-weight))))

(defun redef-sign-form (sign type)
  `(define-analysis (redef-sign :merge #'min :bottom 0 :type ,type)
     ((?f) ,sign)))

(def-test redefine-guard-analysis-type ()
  ;; With :TYPE (INTEGER 0 1) the guard (< (REDEF-SIGN ?X) 0) folds to false at
  ;; compile time, so a cached rule set would keep the rewrite disabled after
  ;; the type and values change.
  (redefine '(define-analysis (redef-weight :merge #'min :bottom +inf-cost+ :type cost)
              ((f ?x) (+ 5 (redef-weight ?x)))
              ((g ?x) (+ 3 (redef-weight ?x)))
              ((h ?x) (+ 1 (redef-weight ?x)))
              ((?f) 1))
            '(defrw* redef-guarded ((f ?x) (g ?x) :guard (< (redef-sign ?x) 0))))
  (flet ((best (sign type)
           (redefine (redef-sign-form sign type))
           (search* '(f x) 'redef-guarded 'redef-weight :analyses '(redef-sign))))
    (is (equal '(f x) (best 1 '(integer 0 1))))
    (is (equal '(g x) (best -1 '(integer -1 1))))
    (is (equal '(f x) (best 1 '(integer 0 1))))))
