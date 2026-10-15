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

(define-analysis shape
  :make (lambda (enode)
          (case (enode-fsym enode)
            (matmul (list (car (shape (enode-arg 0 enode))) (cadr (shape (enode-arg 1 enode)))))
            (mat (map-enode-args #'enode-fsym enode))))
  :merge (make-orp #'equal))

(define-analysis cost
  :make (lambda (enode)
          (case (enode-fsym enode)
            (matmul
             (let ((x (enode-arg 0 enode))
                   (y (enode-arg 1 enode)))
               (+ (cost x) (cost y)
                  (let ((mn (shape x)) (nk (shape y)))
                    (* (car mn) (cadr mn) (cadr nk))))))
            (t 0)))
  :merge #'min)

(defun make-matmul-term (dims)
  (labels ((process (dims)
             (if (cdddr dims)
                 `(matmul (mat ,(car dims) ,(cadr dims))
                          ,(process (cdr dims)))
                 `(matmul (mat ,(car dims) ,(cadr dims))
                          (mat ,(cadr dims) ,(caddr dims))))))
    (process dims)))

(def-test matmul.1 ()
  (let* ((*egraph* (make-egraph :analyses '(cost shape)))
         (a (make-term
             (make-matmul-term '(10 14 12 9 13 16 1 6 13 14 7 7 3 14 15 15 19 12 19 8)))))
    (egraph-rebuild)
    (is (eq :saturate (run-rewrites 'assoc-matmul)))
    (is (= 2619 (cost a)))))

;;; Benchmark

(defun bench-matmul-dims (n)
  "Dimensions of a chain of N matrices, from a fixed pseudo-random sequence."
  (let ((seed 1))
    (loop repeat (1+ n)
          collect (+ 2 (mod (setq seed (mod (* seed 48271) 2147483647)) 30)))))

(def-test bench.matmul (:suite :ggs/eqsat/bench)
  (let ((timer (make-instance 'benchmark:timer)))
    (loop for i from 1 to 5 do
      (let ((*egraph* (make-egraph :analyses '(cost shape))))
        (format t "~&Benchmark run ~a." i)
        (trivial-garbage:gc :full t)
        (let ((a (make-term (make-matmul-term (bench-matmul-dims 60)))))
          (egraph-rebuild)
          (benchmark:with-sampling (timer)
            (run-rewrites '(assoc-matmul -assoc-matmul)))
          (is (= 1849 (egraph-n-eclasses *egraph*)))
          (is (= 36069 (egraph-n-enodes *egraph*)))
          (is (= 30764 (cost a))))))
    (benchmark:report timer)))

(def-test bench.matmul-plain (:suite :ggs/eqsat/bench)
  "Like `bench.matmul' without analyses, on a longer chain."
  (let ((timer (make-instance 'benchmark:timer)))
    (loop for i from 1 to 5 do
      (let ((*egraph* (make-egraph)))
        (format t "~&Benchmark run ~a." i)
        (trivial-garbage:gc :full t)
        (make-term (make-matmul-term (bench-matmul-dims 80)))
        (egraph-rebuild)
        (benchmark:with-sampling (timer)
          (is (eq :saturate (run-rewrites '(assoc-matmul -assoc-matmul)))))
        (is (= 3258 (egraph-n-eclasses *egraph*)))
        (is (= 85418 (egraph-n-enodes *egraph*)))))
    (benchmark:report timer)))
