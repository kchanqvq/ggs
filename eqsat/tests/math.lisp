(uiop:define-package :ggs/eqsat/tests/math
    (:use #:cl #:ggs/eqsat #:alexandria)
  (:import-from #:fiveam #:def-suite* #:def-test #:is #:in-suite)
  (:import-from #:serapeum #:collecting))

(serapeum:eval-always
  (trivial-package-local-nicknames:add-package-local-nickname
   "BENCHMARK" "ORG.SHIRAKUMO.TRIVIAL-BENCHMARK" "GGS/EQSAT/TESTS/MATH"))

(in-package :ggs/eqsat/tests/math)

(def-suite* :math :in :ggs/eqsat)

(defun non-zero-p (enode)
  (not (find 0 (list-enodes enode) :key #'enode-fsym)))

(defrw* const-fold
  ((+ (?a) (?b)) :eval
   (when (and (numberp ?a) (numberp ?b))
     (let ((?n (+ ?a ?b)))
       (yield-rewrite (?n)))))
  ((* (?a) (?b)) :eval
   (when (and (numberp ?a) (numberp ?b))
     (let ((?n (* ?a ?b)))
       (yield-rewrite (?n)))))
  ((- (?a) (?b)) :eval
   (when (and (numberp ?a) (numberp ?b))
     (let ((?n (- ?a ?b)))
       (yield-rewrite (?n)))))
  ((/ (?a) (?b)) :eval
   (when (and (numberp ?a) (numberp ?b) (not (= ?b 0)))
     (let ((?n (/ ?a ?b)))
       (yield-rewrite (?n))))))

(defrw commute-add (+ ?a ?b) (+ ?b ?a))
(defrw commute-mul (* ?a ?b) (* ?b ?a))
(defrw assoc-add (+ ?a (+ ?b ?c)) (+ (+ ?a ?b) ?c))
(defrw assoc-mul (* ?a (* ?b ?c)) (* (* ?a ?b) ?c))

(defrw sub-canon (- ?a ?b) (+ ?a (* -1 ?b)))
(defrw div-canon (/ ?a ?b) (* ?a (pow ?b -1)) :guard (non-zero-p ?b))

(defrw add-0 (+ ?a 0) ?a)
(defrw mul-0 (* ?a 0) 0)
(defrw mul-1 (* ?a 1) ?a)

(defrw -add-0 ?a (+ ?a 0))
(defrw -mul-1 ?a (* ?a 1))

(defrw sub-cancel (- ?a ?a) 0)
(defrw div-cancel (/ ?a ?a) 1 :guard (non-zero-p ?a))

(defrw distribute (* ?a (+ ?b ?c)) (+ (* ?a ?b) (* ?a ?c)))
(defrw factor (+ (* ?a ?b) (* ?a ?c)) (* ?a (+ ?b ?c)))

(defrw pow-mul (* (pow ?a ?b) (pow ?a ?c)) (pow ?a (+ ?b ?c)))
(defrw pow-0 (pow ?a 0) 1 :guard (non-zero-p ?a))
(defrw pow-1 (pow ?a 1) ?a)
(defrw pow-2 (pow ?a 2) (* ?a ?a))
(defrw pow-recip (pow ?a -1) (/ 1 ?a) :guard (non-zero-p ?a))
(defrw recip-mul-div (* ?x (/ 1 ?x)) 1 :guard (non-zero-p ?x))

(declaim (inline pow))
(defun pow (x y) (expt x y))

(defrw* math-base
  COMMUTE-ADD COMMUTE-MUL ASSOC-ADD ASSOC-MUL SUB-CANON DIV-CANON ADD-0 MUL-0 MUL-1 -ADD-0 -MUL-1 SUB-CANCEL
  DIV-CANCEL DISTRIBUTE FACTOR POW-MUL POW-0 POW-1 POW-2 POW-RECIP RECIP-MUL-DIV)

(defrw d-var (d (?x) (?x)) 1 :guard (symbolp ?x))
(defrw d-const (d (?x) (?c)) 0 :guard (or (numberp ?c)
                                          (and (symbolp ?x) (symbolp ?c)
                                               (not (eq ?x ?c)))))
(defrw d-add (d ?x (+ ?a ?b)) (+ (d ?x ?a) (d ?x ?b)))
(defrw d-mul (d ?x (* ?a ?b)) (+ (* ?a (d ?x ?b)) (* ?b (d ?x ?a))))
(defrw d-sin (d ?x (sin ?x)) (cos ?x))
(defrw d-cos (d ?x (cos ?x)) (* -1 (sin ?x)))
(defrw d-ln (d ?x (ln ?x)) (/ 1 ?x) :guard (non-zero-p ?x))
(defrw d-pow (d ?x (pow ?f ?g)) (* (pow ?f ?g) (+ (* (d ?x ?f) (/ ?g ?f)) (* (d ?x ?g) (ln ?f))))
  :guard (and (non-zero-p ?f) (non-zero-p ?g)))

(defrw* math-diff
  D-VAR D-CONST D-ADD D-MUL D-SIN D-COS D-LN D-POW)

(defrw i-one (i 1 ?x) ?x)
(defrw i-pow-const (i (pow ?x (?c)) ?x)
  (/ (pow ?x (+ (?c) 1)) (+ (?c) 1)) :guard (typep ?c 'fixnum))
(defrw i-cos (i (cos ?x) ?x) (sin ?x))
(defrw i-sin (i (sin ?x) ?x) (* -1 (cos ?x)))
(defrw i-sum (i (+ ?f ?g) ?x) (+ (i ?f ?x) (i ?g ?x)))
(defrw i-dif (i (- ?f ?g) ?x) (- (i ?f ?x) (i ?g ?x)))
(defrw i-parts (i (* ?a ?b) ?x) (- (* ?a (i ?b ?x)) (i (* (d ?x ?a) (i ?b ?x)) ?x)))

(defrw* math-integral
  I-ONE I-POW-CONST I-COS I-SIN I-SUM I-DIF I-PARTS)

(defun const-value (enode)
  (let ((n (find-if (lambda (n) (and (zerop (enode-n-args n)) (numberp (enode-fsym n))))
                    (list-enodes enode))))
    (and n (enode-fsym n))))

(defrw* math-all
  const-fold math-base math-diff math-integral)
(precompile-rule-set math-all)

(defun ast-size-no-d-or-i (fsym arg-costs)
  (when (every #'identity arg-costs)
    (+ (if (member fsym '(d i)) 100 1) (reduce #'+ arg-costs))))

(defmacro def-math-test (name () lhs rhs)
  `(def-test ,name ()
     (let* ((*egraph* (make-egraph))
            (lhs (make-term ',lhs)))
       (egraph-rebuild)
       (run-rewrites 'math-all :max-iter 10 :initial-match-limit 1000 :prune-constant #'numberp)
       ;; enodes are cyclic (:type vector) structs; bound printing so a failing
       ;; IS doesn't overflow the stack rendering the enode (see diff-power-harder).
       (let ((*print-circle* t) (*print-level* 6) (*print-length* 12))
         (is (eq (enode-find (make-term ',rhs)) (enode-find lhs)))))))

(def-math-test math.simplify-root ()
  (/ 1 (- (/ (+ 1 (sqrt five)) 2)
          (/ (- 1 (sqrt five)) 2)))
  (/ 1 (sqrt five)))

(def-math-test math.simplify-factor ()
  (* (+ x 3) (+ x 1)) (+ (+ (* x x) (* 4 x)) 3))

(def-math-test math.diff-power-simple ()
  (d x (pow x 3)) (* 3 (pow x 2)))

(def-test math.diff-power-harder ()
  (let* ((*egraph* (make-egraph))
         (a (make-term '(d x (- (pow x 3) (* 7 (pow x 2))))))
         (b (make-term '(* x (- (* 3 x) 14)))))
    (egraph-rebuild)
    (run-rewrites 'math-all :max-iter 10 :initial-match-limit 1000 :prune-constant #'numberp)
    (let ((*print-circle* t) (*print-level* 6) (*print-length* 12))
      (is (eq (enode-find b) (enode-find a))))))

(def-test bench.math.diff (:suite :ggs/eqsat/bench)
  (let ((timer (make-instance 'benchmark:timer)))
    (loop for i from 1 to 5 do
      (let ((*egraph* (make-egraph)))
        (format t "~&Benchmark run ~a." i)
        (trivial-garbage:gc :full t)
        (make-term '(d x (- (pow x 3) (* 7 (pow x 2)))))
        (egraph-rebuild)
        (benchmark:with-sampling (timer)
          (run-rewrites 'math-all :max-iter 15 :prune-constant #'numberp))))
    (benchmark:report timer)))

(def-math-test math.integral-part.1 ()
  (i (* x (cos x)) x) (+ (* x (sin x)) (cos x)))

(def-math-test math.integral-part.2 ()
  (i (* (cos x) x) x) (+ (* x (sin x)) (cos x)))

(def-math-test math.integral-part.3 ()
  (i (ln x) x) (- (* x (ln x)) x))

(def-test math.lp-extract ()
  (let* ((*egraph* (make-egraph))
         (a (make-term '(pow (+ x (+ x x)) (+ x x)))))
    (egraph-rebuild)
    (run-rewrites 'math-all :max-iter 10 :initial-match-limit 1000 :prune-constant #'numberp)
    (is (member (greedy-extract a #'ast-size-no-d-or-i)
                '((pow (* 3 x) (+ x x))
                  (pow (* x 3) (+ x x)))
                :test 'equal))
    (is (member (lp-extract a (constantly 1))
                '((pow (+ x (+ x x)) (+ x x))
                  (pow (+ (+ x x) x) (+ x x)))
                :test 'equal))))
