(uiop:define-package :ggs/eqsat/tests
    (:use #:cl #:ggs/eqsat #:alexandria)
  (:import-from #:fiveam
                #:def-suite* #:def-suite
                #:def-test #:is #:signals #:in-suite)
  (:import-from #:serapeum #:collecting))

(serapeum:eval-always
 (trivial-package-local-nicknames:add-package-local-nickname
  "BENCHMARK" "ORG.SHIRAKUMO.TRIVIAL-BENCHMARK" "GGS/EQSAT/TESTS"))

(in-package :ggs/eqsat/tests)

(def-suite* :ggs/eqsat)
(def-suite :ggs/eqsat/bench)

;;; E-graph data structure and rebuild

(def-test union-find ()
  (let* ((*egraph* (make-egraph))
         (x (make-enode 1))
         (y (make-enode 2)))
    (is (eq (enode-find x) x))
    (is (eq (enode-find y) y))
    (enode-merge x y)
    (is (eq (enode-find x) (enode-find y)))

    (let ((results (list-enodes x)))
      (is (= 2 (length results)))
      (is (member x results))
      (is (member y results)))

    (let ((results (list-enodes y)))
      (is (= 2 (length results)))
      (is (member x results))
      (is (member y results)))

    (egraph-rebuild)
    (is (eq (enode-find x) (enode-find y)))
    (check-egraph)))

(def-test rebuild ()
  (let* ((*egraph* (make-egraph))
         (a (make-enode 'a))
         (b (make-enode 'b))
         (f-a (make-enode 'f a))
         (f-b (make-enode 'f b))
         (g-a (make-enode 'g a))
         (g-b (make-enode 'g b))
         (f-f-a (make-enode 'f f-a))
         (f-f-b (make-enode 'f f-b)))
    (enode-merge a b)
    (is (eq (enode-find a) (enode-find b)))
    (is (every #'enode-canonical-p (list-enodes a)))
    (egraph-rebuild)
    (is (eq (enode-find f-a) (enode-find f-b)))
    (is (eq (enode-find f-f-a) (enode-find f-f-b)))
    (is (eq (enode-find g-a) (enode-find g-b)))
    (is (not (eq (enode-find a) (enode-find f-a))))
    (is (not (eq (enode-find f-a) (enode-find g-a))))
    (is (not (eq (enode-find f-a) (enode-find f-f-a))))
    (is (every #'enode-canonical-p (list-enodes a)))
    (is (every #'enode-canonical-p (list-enodes f-a)))
    (is (every #'enode-canonical-p (list-enodes g-a)))
    (is (every #'enode-canonical-p (list-enodes f-f-a)))
    (check-egraph)
    (enode-merge f-a g-a)
    (egraph-rebuild)
    (is (eq (enode-find f-a) (enode-find g-a)))
    (is (eq (enode-find f-b) (enode-find g-b)))
    (check-egraph)))

(def-test rebuild-cyclic ()
  (let* ((*egraph* (make-egraph))
         (a (make-enode 'a))
         (f-a (make-enode 'f a))
         (f-f-a (make-enode 'f f-a))
         (f-f-f-a (make-enode 'f f-f-a)))
    (enode-merge a f-a)
    (egraph-rebuild)
    (is (eq (enode-find a) (enode-find f-a)))
    (is (eq (enode-find a) (enode-find f-f-a)))
    (is (eq (enode-find a) (enode-find f-f-f-a)))
    (check-egraph)))

;;; Pattern compiler

(defrw commute-add (+ ?a ?b) (+ ?b ?a))
(defrw commute-mul (* ?a ?b) (* ?b ?a))
(defrw add-0 (+ ?a 0) ?a)
(defrw mul-0 (* ?a 0) 0)
(defrw mul-1 (* ?a 1) ?a)

(define-analysis (ast-size :merge #'min-maybe)
  ((?f ?x ?y) (+ 1 (ast-size ?x) (ast-size ?y)))
  ((?f ?x) (+ 1 (ast-size ?x)))
  ((?f) 1))

(def-test simple.1 ()
  (let* ((*egraph* (make-egraph :analyses 'ast-size))
         (a (term-enode '(* 0 42)))
         (b (term-enode 0)))
    (egraph-rebuild)
    (is (eq :saturate
            (run-rewrites '(commute-add commute-mul add-0 mul-0 mul-1)
                          :check t :max-iter 10)))
    (is (eq (enode-find a) (enode-find b)))
    (is (equal 0 (greedy-extract a 'ast-size)))))

(def-test simple.2 ()
  (let* ((*egraph* (make-egraph :analyses 'ast-size))
         (a (term-enode '(+ 0 (* 1 foo))))
         (b (term-enode 'foo)))
    (egraph-rebuild)
    (is (eq :saturate
            (run-rewrites '(commute-add commute-mul add-0 mul-0 mul-1)
                          :check t :max-iter 10)))
    (is (eq (enode-find a) (enode-find b)))
    (is (equal 'foo (greedy-extract a 'ast-size)))))

(defrw assoc-add (+ ?a (+ ?b ?c)) (+ (+ ?a ?b) ?c))
(defrw assoc-mul (* ?a (* ?b ?c)) (* (* ?a ?b) ?c))

(def-test ac ()
  (let ((*egraph* (make-egraph)))
    (term-enode '(+ 0 (+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))))
    (egraph-rebuild)
    (is (eq :saturate
            (run-rewrites '(commute-add assoc-add)
                          :check t :max-iter 10)))
    (is (= 6058 (egraph-n-enodes *egraph*)))
    (is (= 255 (egraph-n-eclasses *egraph*)))))

(defrw sub-cancel (- ?a ?a) 0)
(defrw div-cancel (/ (?a) (?a)) 1 :guard (not (eql ?a 0)))
(defrw add-2 (+ ?a ?a) (* 2 ?a))

(def-test nonlinear.1 ()
  (let* ((*egraph* (make-egraph :analyses 'ast-size))
         (a (term-enode '(- (+ a b) (+ b a))))
         (b (term-enode '(- (+ a a) (* 2 a))))
         (c (term-enode '(+ a (- b (* 1 b))))))
    (egraph-rebuild)
    (is (eq :saturate
            (run-rewrites '(sub-cancel add-2
                            commute-add commute-mul add-0 mul-0 mul-1)
                          :check t :max-iter 10)))
    (is (equal 0 (greedy-extract a 'ast-size)))
    (is (equal 0 (greedy-extract b 'ast-size)))
    (is (equal 'a (greedy-extract c 'ast-size)))))

(def-test nonlinear.2 ()
  (let* ((*egraph* (make-egraph :analyses 'ast-size))
         (a (term-enode '(/ (- a a) (- a a))))
         (b (term-enode '(/ 3 5)))
         (c (term-enode '(/ 5 5))))
    (egraph-rebuild)
    (is (eq :saturate
            (run-rewrites '(sub-cancel div-cancel
                            commute-add commute-mul add-0 mul-0 mul-1)
                          :check t :max-iter 10)))
    (is (equal '(/ 0 0) (greedy-extract a 'ast-size)))
    (is (equal '(/ 3 5) (greedy-extract b 'ast-size)))
    (is (equal 1 (greedy-extract c 'ast-size)))))

(defrw d-sin (d ?x (sin ?x)) (cos ?x))
(defrw d-cos (d ?x (cos ?x)) (* -1 (sin ?x)))

(def-test ground ()
  (let* ((*egraph* (make-egraph :analyses 'ast-size))
         (a (term-enode '(d a (sin a))))
         (b (term-enode '(d (+ a b) (sin (+ b a)))))
         (b-1 (term-enode '(cos (+ a b))))
         (c (term-enode '(d a (d a (sin a)))))
         (c-1 (term-enode '(* -1 (sin a)))))
    (egraph-rebuild)
    (is (eq :saturate
            (run-rewrites '(d-sin d-cos
                            commute-add commute-mul add-0 mul-0 mul-1)
                          :check t :max-iter 10)))
    (is (equal '(cos a) (greedy-extract a 'ast-size)))
    (is (eq (enode-find b-1) (enode-find b)))
    (is (eq (enode-find c-1) (enode-find c)))))

(defrw -add-0 ?a (+ ?a 0))

(def-test single-var-pat ()
  (let* ((*egraph* (make-egraph))
         (a (term-enode 'a))
         (b (term-enode '(+ (+ (+ a 0) 0) 0))))
    (egraph-rebuild)
    (is (eq :saturate
            (run-rewrites '-add-0 :check t :max-iter 10)))
    (is (eq (enode-find a) (enode-find b)))))

(defrw* const-fold
  ((+ (?a) (?b)) :eval
   (when (and (numberp ?a) (numberp ?b))
     (let ((?n (+ ?a ?b)))
       (yield-rewrite (?n)))))
  ((* (?a) (?b)) :eval
   (when (and (numberp ?a) (numberp ?b))
     (let ((?n (* ?a ?b)))
       (yield-rewrite (?n))))))

(def-test const-fold ()
  (let* ((*egraph* (make-egraph :analyses 'ast-size))
         (a (term-enode '(+ 3 (+ 2 a))))
         (b (term-enode '(+ a 5)))
         (c (term-enode '(+ 2 (* 3 5)))))
    (egraph-rebuild)
    (is (eq :saturate
            (run-rewrites '(commute-add commute-mul assoc-add assoc-mul const-fold)
                          :prune-constant #'numberp :check t :max-iter 10)))
    (is (eq (enode-find a) (enode-find b)))
    (is (equal 17 (greedy-extract c 'ast-size)))))

(defrw d-var (d (?x) (?x)) 1 :guard (symbolp ?x))
(defrw d-const (d (?x) (?c)) 0 :guard (or (numberp ?c)
                                          (and (symbolp ?x) (symbolp ?c)
                                               (not (eq ?x ?c)))))

(def-test deriv ()
  (let* ((*egraph* (make-egraph))
         (a (term-enode '(+ (d x (+ 1 2)) (d y y)))))
    (egraph-rebuild)
    (run-rewrites '(commute-add assoc-add d-var d-const const-fold) :max-iter 10)
    (is (eq (enode-find (term-enode 1)) (enode-find a)))))

(defrw seq-swap (f ?a ??x ?b) (f ?b ??x ?a))

(def-test seq-var.middle ()
  (let* ((*egraph* (make-egraph))
         (a (term-enode '(f 1 2 3 4)))
         (b (term-enode '(f 1 2)))
         (c (term-enode '(f 1))))
    (egraph-rebuild)
    (is (eq :saturate (run-rewrites 'seq-swap :check t :max-iter 10)))
    (is (eq (enode-find a) (enode-find (term-enode '(f 4 2 3 1)))))
    ;; ??X matches no argument
    (is (eq (enode-find b) (enode-find (term-enode '(f 2 1)))))
    ;; Too few arguments to match
    (is (= 1 (length (list-enodes c))))))

(defrw seq-rotate (f ??x ?b) (g ?b ??x))

(def-test seq-var.first ()
  (let* ((*egraph* (make-egraph))
         (a (term-enode '(f 1 2 3)))
         (b (term-enode '(f 1))))
    (egraph-rebuild)
    (is (eq :saturate (run-rewrites 'seq-rotate :check t :max-iter 10)))
    (is (eq (enode-find a) (enode-find (term-enode '(g 3 1 2)))))
    (is (eq (enode-find b) (enode-find (term-enode '(g 1)))))))

(defrw seq-wrap (h ??x) (k (h ??x) 0))

(def-test seq-var.template ()
  (let* ((*egraph* (make-egraph))
         (a (term-enode '(h x y)))
         (b (term-enode '(k (h x y) 0)))
         (n-enodes (progn (egraph-rebuild) (egraph-n-enodes *egraph*))))
    (is (eq :saturate (run-rewrites 'seq-wrap :check t :max-iter 10)))
    (is (eq (enode-find a) (enode-find b)))
    ;; The RHS is hash-consed to the existing enodes
    (is (= n-enodes (egraph-n-enodes *egraph*)))))

(defrw seq-same (p (f ??x) (f ??x)) yes)

(def-test seq-var.nonlinear ()
  (let* ((*egraph* (make-egraph))
         (yes (term-enode 'yes))
         (same (term-enode '(p (f a b) (f a b))))
         (differ (term-enode '(p (f a b) (f a c))))
         (prefix-1 (term-enode '(p (f a b) (f a b c))))
         (prefix-2 (term-enode '(p (f a b c) (f a b)))))
    (egraph-rebuild)
    (is (eq :saturate (run-rewrites 'seq-same :check t :max-iter 10)))
    (is (eq (enode-find yes) (enode-find same)))
    (is (not (eq (enode-find yes) (enode-find differ))))
    (is (not (eq (enode-find yes) (enode-find prefix-1))))
    (is (not (eq (enode-find yes) (enode-find prefix-2))))))

(defrw seq-fsym (q (?g ??x)) (r (?g ??x)))

(def-test seq-var.fsym ()
  (let* ((*egraph* (make-egraph))
         (a (term-enode '(q (h 1 2))))
         (b (term-enode '(q (j)))))
    (egraph-rebuild)
    (is (eq :saturate (run-rewrites 'seq-fsym :check t :max-iter 10)))
    (is (eq (enode-find a) (enode-find (term-enode '(r (h 1 2))))))
    (is (eq (enode-find b) (enode-find (term-enode '(r j)))))))

;;; Type checks

(defvar *not-an-enode* 'x "Type unknown at compile time.")

(def-test type-check.make-enode ()
  (let* ((*egraph* (make-egraph))
         (a (make-enode 'a))
         (x *not-an-enode*)
         (xs (list x)))
    (signals type-error (make-enode 'f a x))
    (signals type-error (funcall 'make-enode 'f a x))
    (signals type-error (ggs/eqsat::make-enode-from-args 'f (list a x)))
    (signals type-error (funcall 'ggs/eqsat::make-enode-from-args 'f (list a x)))
    ;; Elements of a sequence argument
    (signals type-error (ggs/eqsat::make-enode-from-args 'f (append (list a) xs)))))

(def-test type-check.enode-merge ()
  (let* ((*egraph* (make-egraph))
         (a (make-enode 'a))
         (x *not-an-enode*))
    (signals type-error (enode-merge a x))
    (signals type-error (enode-merge x a))
    (signals type-error (enode-merge a (make-enode 'f x)))))

;;; Micro benchmark

(defrw sub-canon (- ?a ?b) (+ ?a (* -1 ?b)))

(defrw distribute (* ?a (+ ?b ?c)) (+ (* ?a ?b) (* ?a ?c)))
(defrw factor (+ (* ?a ?b) (* ?a ?c)) (* ?a (+ ?b ?c)))

(defrw d-add (d ?x (+ ?a ?b)) (+ (d ?x ?a) (d ?x ?b)))
(defrw d-mul (d ?x (* ?a ?b)) (+ (* ?a (d ?x ?b)) (* ?b (d ?x ?a))))

(defrw i-const (i ?x 1) ?x)
(defrw i-cos (i ?x (cos ?x)) (sin ?x))
(defrw i-sin (i ?x (sin ?x)) (* -1 (cos ?x)))
(defrw i-add (i ?x (+ ?f ?g)) (+ (i ?x ?f) (i ?x ?g)))
(defrw i-sub (i ?x (- ?f ?g)) (- (i ?x ?f) (i ?x ?g)))
(defrw i-part (i ?x (* ?a ?b)) (- (* ?a (i ?x ?b)) (i ?x (* (d ?x ?a) (i ?x ?b)))))

(defrw* math-all
  commute-add commute-mul add-0 mul-0 mul-1
  assoc-add assoc-mul sub-canon sub-cancel distribute factor
  d-add d-mul d-sin d-cos
  i-const i-cos i-sin i-add i-sub i-part)
(precompile-eqsat-rule-set math-all)

(def-test bench.math (:suite :ggs/eqsat/bench)
  (let ((timer (make-instance 'benchmark:timer)))
    (loop for i from 1 to 5 do
      (let ((*egraph* (make-egraph)))
        (format t "~&Benchmark run ~a." i)
        (trivial-garbage:gc :full t)
        (term-enode '(i x (ln x)))
        (term-enode '(i x (+ x (cos x))))
        (term-enode '(i x (* (cos x) x)))
        (term-enode '(d x (+ 1 (* 2 x))))
        (term-enode '(d x (- (pow x 3) (* 7 (pow x 2)))))
        (term-enode '(+ (* y (+ x y)) (- (+ x 2) (+ x x))))
        (term-enode '(/ 1 (- (/ (+ 1 (sqrt five)) 2) (/ (- 1 (sqrt five)) 2))))
        (egraph-rebuild)
        (benchmark:with-sampling (timer)
          (run-rewrites 'math-all :max-iter 11))
        (is (= 443792 (egraph-n-eclasses *egraph*)))
        (is (= 1047556 (egraph-n-enodes *egraph*)))))
    (benchmark:report timer)))

#+nil (def-test bench.analysis-ac (:suite :ggs/eqsat/bench)
  (let ((timer (make-instance 'benchmark:timer)))
    (loop for i from 1 to 5 do
      (let ((*egraph* (make-egraph :analyses 'const)))
        (format t "~&Benchmark run ~a." i)
        (trivial-garbage:gc :full t)
        (term-enode '(+ 0 (+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 (+ 7 (+ x (+ y (+ z w))))))))))))
        (egraph-rebuild)
        (benchmark:with-sampling (timer)
          (run-rewrites '(commute-add assoc-add)))
        (is (= 479 (egraph-n-eclasses *egraph*)))
        (is (= 39088 (egraph-n-enodes *egraph*)))))
    (benchmark:report timer)))
