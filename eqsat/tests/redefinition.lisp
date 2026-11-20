(uiop:define-package :ggs/eqsat/tests/redefinition
    (:use #:cl #:ggs/eqsat #:alexandria)
  (:import-from #:fiveam #:def-suite* #:def-test #:is))

(in-package :ggs/eqsat/tests/redefinition)

;;; Compiled analyses and rules are cached.  Redefining an analysis or a rule
;;; set must not reuse code compiled for the old definition, and redefining it
;;; back must give the old behaviour again.

(def-suite* :redefinition :in :ggs/eqsat)

(defun redefine (&rest forms)
  (dolist (form forms) (eval form)))

(defmacro with-egraph ((&rest analyses) &body body)
  `(handler-bind ((runtime-compile-warning #'muffle-warning))
     (let ((*egraph* (make-egraph :analyses ',analyses)))
       ,@body)))

(defun redef-size-form (leaf)
  `(define-analysis (redef-size :merge #'min :bottom +inf-cost+ :type cost)
     ((?f ?x ?y) (+ 1 (redef-size ?x) (redef-size ?y)))
     ((?f) ,leaf)))

(def-test redefine-analysis ()
  (flet ((size-of (leaf term)
           (redefine (redef-size-form leaf))
           (with-egraph (redef-size)
             (let ((enode (term-enode term)))
               (egraph-rebuild)
               (enode-analysis-data 'redef-size enode)))))
    (is (= 3 (size-of 1 '(f x y))))
    (is (= 21 (size-of 10 '(f x y))))
    (is (= 3 (size-of 1 '(f x y))))))

(def-test redefine-rule-set ()
  (flet ((merged-with (rule-rhs)
           (redefine `(defrw* redef-rules ((f ?x) ,rule-rhs)))
           (with-egraph ()
             (let ((f (term-enode '(f x)))
                   (g (term-enode '(g x)))
                   (h (term-enode '(h x))))
               (egraph-rebuild)
               (loop repeat 3 until (run-rewrites 'redef-rules))
               (list (eq (enode-find f) (enode-find g))
                     (eq (enode-find f) (enode-find h)))))))
    (is (equal '(t nil) (merged-with '(g ?x))))
    (is (equal '(nil t) (merged-with '(h ?x))))
    (is (equal '(t nil) (merged-with '(g ?x))))))

(defun redef-sign-form (sign type)
  `(define-analysis (redef-sign :merge #'min :bottom 0 :type ,type)
     ((?f) ,sign)))

(def-test redefine-guard-analysis-type ()
  ;; With :TYPE (INTEGER 0 1) the guard (< (REDEF-SIGN ?X) 0) folds to false at
  ;; compile time, so a cached rule would keep the rewrite disabled after the
  ;; type and values change.
  (redefine '(defrw* redef-guarded ((f ?x) (g ?x) :guard (< (redef-sign ?x) 0))))
  (flet ((fires (sign type)
           (redefine (redef-sign-form sign type))
           (with-egraph (redef-sign)
             (let ((f (term-enode '(f x)))
                   (g (term-enode '(g x))))
               (egraph-rebuild)
               (loop repeat 3 until (run-rewrites 'redef-guarded))
               (eq (enode-find f) (enode-find g))))))
    (is (not (fires 1 '(integer 0 1))))
    (is (fires -1 '(integer -1 1)))
    (is (not (fires 1 '(integer 0 1))))))

(def-test redefine-cost-extraction ()
  (redefine '(defrw* redef-swap ((f ?x) (g ?x))))
  (flet ((extract (f g)
           (redefine `(define-analysis (redef-cost :merge #'min :bottom +inf-cost+ :type cost)
                        ((f ?x) (+ ,f (redef-cost ?x)))
                        ((g ?x) (+ ,g (redef-cost ?x)))
                        ((?f) 1)))
           (with-egraph (redef-cost)
             (let ((f (term-enode '(f x))))
               (egraph-rebuild)
               (loop repeat 3 until (run-rewrites 'redef-swap))
               (greedy-extract f 'redef-cost)))))
    (is (equal '(f x) (extract 1 5)))
    (is (equal '(g x) (extract 5 1)))
    (is (equal '(f x) (extract 1 5)))))
