(uiop:define-package :ggs/eqsat/tests/matmul
    (:use #:cl #:ggs/eqsat #:alexandria)
  (:import-from #:fiveam #:def-suite* #:def-test #:is #:in-suite))

(serapeum:eval-always
 (trivial-package-local-nicknames:add-package-local-nickname
  "BENCHMARK" "ORG.SHIRAKUMO.TRIVIAL-BENCHMARK" "GGS/EQSAT/TESTS/MATMUL"))

(in-package :ggs/eqsat/tests/matmul)

(def-suite* :matmul :in :ggs/eqsat)

(defrw assoc-matmul (matmul ?x (matmul ?y ?z)) (matmul (matmul ?x ?y) ?z))
(defrw -assoc-matmul (matmul (matmul ?x ?y) ?z) (matmul ?x (matmul ?y ?z)))

(define-analysis (row :merge #'or-eql)
  ((matmul ?x ?y) (row ?x))
  ((mat (?row) ?x) ?row))

(define-analysis (col :merge #'or-eql)
  ((matmul ?x ?y) (col ?y))
  ((mat ?x (?col)) ?col))

(define-analysis (matmul-cost :merge #'min :bottom +inf-cost+ :type cost)
  ((matmul ?x ?y)
   (if-let ((m (row ?x)) (n (col ?x)) (k (col ?y)))
     (+ (matmul-cost ?x) (matmul-cost ?y) (* m n k))
     +inf-cost+))
  ((mat ?x ?y) 0))

(defun make-matmul-term (dims)
  (labels ((process (dims)
             (if (cdddr dims)
                 `(matmul (mat ,(car dims) ,(cadr dims))
                          ,(process (cdr dims)))
                 `(matmul (mat ,(car dims) ,(cadr dims))
                          (mat ,(cadr dims) ,(caddr dims))))))
    (process dims)))

(def-test matmul.1 ()
  (let* ((*egraph* (make-egraph :analyses '(row col matmul-cost)))
         (a (term-enode
             (make-matmul-term '(10 14 12 9 13 16 1 6 13 14 7 7 3 14 15 15 19 12 19 8)))))
    (egraph-rebuild)
    (is (eq :saturate (run-rewrites 'assoc-matmul)))
    (is (= 2619 (enode-analysis-data 'matmul-cost a)))))

;;; Benchmark

(defun bench-matmul-dims (n)
  "Dimensions of a chain of N matrices, from a fixed pseudo-random sequence."
  (let ((seed 1))
    (loop repeat (1+ n)
          collect (+ 2 (mod (setq seed (mod (* seed 48271) 2147483647)) 30)))))

(def-test bench.matmul (:suite :ggs/eqsat/bench)
  (let ((timer (make-instance 'benchmark:timer)))
    (loop for i from 1 to 5 do
      (let ((*egraph* (make-egraph :analyses '(row col matmul-cost))))
        (format t "~&Benchmark run ~a." i)
        (trivial-garbage:gc :full t)
        (let ((a (term-enode (make-matmul-term (bench-matmul-dims 60)))))
          (egraph-rebuild)
          (benchmark:with-sampling (timer)
            (run-rewrites '(assoc-matmul -assoc-matmul)))
          (is (= 1849 (egraph-n-eclasses *egraph*)))
          (is (= 36069 (egraph-n-enodes *egraph*)))
          (is (= 30764 (enode-analysis-data 'matmul-cost a))))))
    (benchmark:report timer)))

(def-test bench.matmul-plain (:suite :ggs/eqsat/bench)
  "Like `bench.matmul' without analyses, on a longer chain."
  (let ((timer (make-instance 'benchmark:timer)))
    (loop for i from 1 to 5 do
      (let ((*egraph* (make-egraph)))
        (format t "~&Benchmark run ~a." i)
        (trivial-garbage:gc :full t)
        (term-enode (make-matmul-term (bench-matmul-dims 80)))
        (egraph-rebuild)
        (benchmark:with-sampling (timer)
          (is (eq :saturate (run-rewrites '(assoc-matmul -assoc-matmul)))))
        (is (= 3258 (egraph-n-eclasses *egraph*)))
        (is (= 85418 (egraph-n-enodes *egraph*)))))
    (benchmark:report timer)))
