(uiop:define-package :ggs/stochastic/tests
    (:use #:cl #:ggs/stochastic #:alexandria)
  (:import-from #:fiveam
                #:def-suite* #:def-test #:is #:signals #:skip))

(in-package :ggs/stochastic/tests)

(def-suite* :ggs/stochastic)

;;; Analyses, with plain Lisp references to check them against

(define-analysis (size :merge #'min :bottom +inf-cost+ :type cost)
  ((?f ?x ?y ?z) (+ 1 (size ?x) (size ?y) (size ?z)))
  ((?f ?x ?y) (+ 1 (size ?x) (size ?y)))
  ((?f ?x) (+ 1 (size ?x)))
  ((?f) 1))

(define-analysis (depth :merge #'min :bottom +inf-cost+ :type cost)
  ((?f ?x ?y ?z) (+ 1 (max (depth ?x) (depth ?y) (depth ?z))))
  ((?f ?x ?y) (+ 1 (max (depth ?x) (depth ?y))))
  ((?f ?x) (+ 1 (depth ?x)))
  ((?f) 1))

;; POW costs 5.  Both clauses match a POW node and the merge takes the
;; minimum, so the generic clause gives POW the infinite cost.
(define-analysis (weighted :merge #'min :bottom +inf-cost+ :type cost)
  ((?f ?x ?y ?z) (+ 1 (weighted ?x) (weighted ?y) (weighted ?z)))
  ((pow ?x ?y) (+ 5 (weighted ?x) (weighted ?y)))
  ((?f ?x ?y) (if (eq ?f 'pow) +inf-cost+ (+ 1 (weighted ?x) (weighted ?y))))
  ((?f ?x) (+ 1 (weighted ?x)))
  ((?f) 1))

(defun tree-size (term)
  (if (consp term) (1+ (reduce #'+ (mapcar #'tree-size (cdr term)))) 1))

(defun tree-depth (term)
  (if (consp term) (1+ (reduce #'max (mapcar #'tree-depth (cdr term)))) 1))

(defun tree-weighted (term)
  (if (consp term)
      (+ (if (eq (car term) 'pow) 5 1) (reduce #'+ (mapcar #'tree-weighted (cdr term))))
      1))

(defparameter *references*
  '((size . tree-size) (depth . tree-depth) (weighted . tree-weighted)))

(defun reference-cost (analysis term)
  (funcall (cdr (assoc analysis *references*)) term))

;;; Rule sets

(defrw* cancel
  ((+ (- ?a) ?a) 0)
  ((+ ?a ?b) (+ ?b ?a))
  ((+ (+ ?a ?b) ?c) (+ ?a (+ ?b ?c)))
  ((+ ?a (+ ?b ?c)) (+ (+ ?a ?b) ?c))
  ((+ ?a 0) ?a))

(defrw* reassoc
  ((+ (+ ?a ?b) ?c) (+ ?a (+ ?b ?c)))
  ((+ ?a (+ ?b ?c)) (+ (+ ?a ?b) ?c))
  ((+ ?a ?b) (+ ?b ?a)))

(defrw* powers
  ((* ?a ?a) (pow ?a 2))
  ((pow ?a 2) (* ?a ?a))
  ((* ?a ?b) (* ?b ?a)))

(precompile-stochastic-rule-set cancel size)

(defun search* (term rule-set cost &rest args)
  "STOCHASTIC-SEARCH with a small deterministic budget unless ARGS override it."
  (handler-bind ((runtime-compile-warning #'muffle-warning))
    (apply #'stochastic-search term rule-set cost
           (append args (list :max-restart 2 :max-stall 500 :seed 0)))))

;;; Search results

(def-test readme-example ()
  (multiple-value-bind (cost term) (search* '(+ (+ (- x) (+ y (- x))) (+ (- y) x)) 'cancel 'size)
    (is (= 2 cost))
    (is (equal '(- x) term))))

(def-test constant-term ()
  (multiple-value-bind (cost term plist) (search* 'x 'cancel 'size)
    (is (= 1 cost))
    (is (eq 'x term))
    (is (= 0 (getf plist :n-accepted)))))

(def-test deterministic ()
  (let ((term '(+ (+ (+ (+ a b) c) d) e)))
    (is (equal (multiple-value-list (search* term 'reassoc 'depth))
               (multiple-value-list (search* term 'reassoc 'depth))))))

(def-test reported-cost-is-cost-of-term ()
  (loop for (term rule-set analysis) in '(((+ (+ (- x) (+ y (- x))) (+ (- y) x)) cancel size)
                                          ((+ (+ (+ (+ a b) c) d) e) reassoc depth)
                                          ((+ (+ (+ (+ a b) c) d) e) reassoc size)
                                          ((* (* x x) (* y y)) powers weighted)
                                          ((* (pow x 2) y) powers weighted))
        do (multiple-value-bind (cost best) (search* term rule-set analysis)
             (is (= (reference-cost analysis best) cost)
                 "~a of ~s is ~a, but the search reported ~a"
                 analysis best (reference-cost analysis best) cost)
             (is (<= cost (reference-cost analysis term))))))

(def-test full-history-costs ()
  ;; Every accepted move's cost is the cost of the term it produced: node
  ;; analyses stay right through path copies and RECOMPUTE-ROSE.
  (multiple-value-bind (cost term plist)
      (search* '(* (* x x) (+ (* y y) z)) 'powers 'weighted :save-full-history t)
    (declare (ignore cost term))
    (let ((entries (loop for run in (getf plist :full-history)
                         append (remove-if-not #'consp run))))
      (is (< 1 (length entries)))
      (dolist (entry entries)
        (is (= (reference-cost 'weighted (getf entry :term)) (getf entry :cost))
            "history term ~s has cost ~a, recorded ~a"
            (getf entry :term) (reference-cost 'weighted (getf entry :term)) (getf entry :cost))))))

(def-test cost-history ()
  (multiple-value-bind (cost term plist)
      (search* '(+ (+ (+ (+ a b) c) d) e) 'reassoc 'depth :save-cost-history t)
    (declare (ignore term))
    (let ((costs (mapcar #'second (getf plist :cost-history))))
      (is (not (null costs)))
      (is (apply #'> (reference-cost 'depth '(+ (+ (+ (+ a b) c) d) e)) costs))
      (is (= cost (lastcar costs))))))

(def-test target-cost ()
  (multiple-value-bind (cost) (search* '(+ (+ (+ (+ a b) c) d) e) 'reassoc 'depth
                                       :target-cost 4 :max-restart 64)
    (is (<= cost 4))))

(def-test proxy-cost ()
  ;; Minimises DEPTH, sampling rewrites by SIZE: the result is reported in DEPTH.
  (multiple-value-bind (cost term)
      (search* '(+ (+ (+ (+ a b) c) d) e) 'reassoc 'depth :proxy-cost 'size)
    (is (= (tree-depth term) cost))
    (is (< cost 5))))

(def-test parallel ()
  (let ((term '(+ (+ (- x) (+ y (- x))) (+ (- y) x))))
    ;; Single-threaded first: an error inside a worker thread escapes the test
    ;; framework and ends the whole run, so let it surface here instead.
    (search* term 'cancel 'size)
    (multiple-value-bind (cost best) (search* term 'cancel 'size :nproc 2)
      (is (= 2 cost))
      (is (equal '(- x) best)))))

(def-test no-processes ()
  (multiple-value-bind (cost term) (search* '(+ x 0) 'cancel 'size :nproc 0)
    (is (= +inf-cost+ cost))
    (is (equal '(+ x 0) term))))

(def-test beta-too-large ()
  (signals error (search* '(+ x 0) 'cancel 'size :beta 80.0)))

(def-test precompiled ()
  (let ((warned nil))
    (handler-bind ((runtime-compile-warning (lambda (c) (setq warned t) (muffle-warning c))))
      (stochastic-search '(+ x 0) 'cancel 'size :max-restart 1 :max-stall 10))
    (is (not warned) "CANCEL was precompiled for SIZE, yet the search compiled it again")))

;;; Patterns

(defrw* repeated
  ((- ?a ?a) 0)
  ((d (?x) (?x)) 0))

(def-test repeated-variables ()
  (is (eql 0 (nth-value 1 (search* '(- (f x) (f x)) 'repeated 'size))))
  (is (equal '(- (f x) (f y)) (nth-value 1 (search* '(- (f x) (f y)) 'repeated 'size))))
  (is (eql 0 (nth-value 1 (search* '(d x x) 'repeated 'size))))
  (is (equal '(d x y) (nth-value 1 (search* '(d x y) 'repeated 'size)))))

(defrw* first-arg ((f ?x ??rest) ?x))

(def-test sequence-variable-in-pattern ()
  (is (equal '(g a) (nth-value 1 (search* '(f (g a) b c) 'first-arg 'size)))))

(def-test sequence-variable-in-template ()
  (skip "A sequence variable in a right-hand side hits the (ERROR \"TODO\") branches of
static matching in stochastic/match.lisp"))

(defrw* fold
  ((+ (?a) (?b))
   :eval (when (and (numberp ?a) (numberp ?b))
           (let ((?n (+ ?a ?b)))
             (yield-rewrite (?n))))))

(def-test eval-rule ()
  (is (eql 9 (nth-value 1 (search* '(+ 2 (+ 3 4)) 'fold 'size)))))

(defrw* guarded
  ((+ ?a ?b) (+ ?b ?a))
  ((+ ?a 0) ?a :guard (<= (depth ?a) 1)))

(def-test guard-reads-analysis ()
  (is (eq 'x (nth-value 1 (search* '(+ x 0) 'guarded 'size :analyses '(depth)))))
  (is (= 5 (search* '(+ (f (g x)) 0) 'guarded 'size :analyses '(depth))))
  ;; DEPTH is not among the stored analyses (quiet the compiler's report of it)
  (let ((*error-output* (make-broadcast-stream)))
    (signals error (search* '(+ x 0) 'guarded 'size))))

;;; Infinite cost

;; FOO cannot be costed
(define-analysis (no-foo :merge #'min :bottom +inf-cost+ :type cost)
  ((?f ?x ?y) (+ 1 (no-foo ?x) (no-foo ?y)))
  ((?f ?x) (if (eq ?f 'foo) +inf-cost+ (+ 1 (no-foo ?x))))
  ((?f) 1))

(defrw* remove-foo
  ((foo ?x) (bar ?x))
  ((+ ?a ?b) (+ ?b ?a))
  ((+ ?a 0) ?a))

(def-test escape-infinite-cost ()
  (multiple-value-bind (cost term) (search* '(+ (foo x) 0) 'remove-foo 'no-foo)
    (is (= 2 cost))
    (is (equal '(bar x) term))))

(define-analysis (untyped-size :merge #'min :bottom +inf-cost+)
  ((?f ?x ?y) (+ 1 (untyped-size ?x) (untyped-size ?y)))
  ((?f) 1))

(def-test untyped-cost-warns ()
  (signals style-warning
    (ggs/stochastic::compute-rule-set-lambda
     (ggs/util:get-rules 'cancel) 'untyped-size 'untyped-size
     (ggs/stochastic::analyses-alist 'untyped-size 'untyped-size nil) nil)))
