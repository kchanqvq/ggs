;;; Compare compiled weights with the proof disabled/enabled on the same search.
(require :asdf)
(asdf:load-asd (merge-pathnames "../../ggs.asd" *load-truename*))
(ql:quickload :ggs/stochastic/tests :silent t)
(in-package :ggs/stochastic/tests)

(defun balanced-term (leaves)
  (if (null (cdr leaves)) (car leaves)
      (let ((middle (floor (length leaves) 2)))
        (list '+ (balanced-term (subseq leaves 0 middle)) (balanced-term (subseq leaves middle))))))

(defparameter *weight-bench-cases*
  (list (list "reassoc-32" (balanced-term (loop for i below 32 collect i)) 'reassoc 'size)
        (list "reassoc-256" (balanced-term (loop for i below 256 collect i)) 'reassoc 'size)
        (list "powers-64" (balanced-term (loop for i below 64 collect `(* (f ,i) (f ,i)))) 'powers 'weighted)))

(defrw* weight-bench-ternary ((f ?a ?b ?c) (f ?b ?c ?a)))
(progn
  (setf *weight-bench-cases*
        (append *weight-bench-cases*
                (list (list "symbols-256"
                            (balanced-term (loop for i below 256 collect (intern (format nil "LEAF~d" i))))
                            'reassoc 'size)
                      (list "ternary-81"
                            (labels ((build (n)
                                       (if (zerop n) 1
                                           (list 'f (build (1- n)) (build (1- n)) (build (1- n))))))
                              (build 4))
                            'weight-bench-ternary 'size)
                      (list "constructors-64"
                            (balanced-term (loop for i below 64 collect (list (intern (format nil "CTOR~d" i)) i)))
                            'reassoc 'size)))))


(defun weight-bench-run (case steps seed)
  (search* (second case) (third case) (fourth case)
           :max-restart 1 :max-stall steps :seed seed :target-cost 0))

(defun weight-bench-measure (case cache steps seed)
  (sb-ext:gc :full t)
  (let ((bytes (sb-ext:get-bytes-consed))
        (wall (get-internal-real-time)) (cpu (get-internal-run-time)))
    (let ((result (with-weight-test-cache (cache)
                    (multiple-value-list (weight-bench-run case steps seed)))))
      (list :wall (/ (- (get-internal-real-time) wall) (float internal-time-units-per-second 1d0))
            :cpu (/ (- (get-internal-run-time) cpu) (float internal-time-units-per-second 1d0))
            :bytes (- (sb-ext:get-bytes-consed) bytes) :result result))))

(let ((steps (parse-integer (or (uiop:getenv "WEIGHT_STEPS") "1000000")))
      (rounds (parse-integer (or (uiop:getenv "WEIGHT_ROUNDS") "6")))
      (start (parse-integer (or (uiop:getenv "WEIGHT_SEED_START") "0"))))
  (dolist (case *weight-bench-cases*)
    (let ((old (weight-test-cache (third case) (fourth case) nil))
          (new (weight-test-cache (third case) (fourth case) t)))
      (dolist (cache (list old new))
        (with-weight-test-cache (cache) (weight-bench-run case 2000 0))
        (assert (= 1 (hash-table-count cache))))
      (dotimes (round rounds)
        (let ((seed (+ start round)) (results nil))
          (dolist (optimize (if (evenp round) '(nil t) '(t nil)))
            (let* ((cache (if optimize new old))
                   (sample (weight-bench-measure case cache steps seed))
                   (result (getf sample :result)) (stats (third result)))
              (assert (= 1 (hash-table-count cache)))
              (push result results)
              (format t "~&ROW ~a ~a ~d ~d wall=~,6f cpu=~,6f bytes=~d moves=~d cost=~d~%"
                      (first case) (if optimize "ON" "OFF") steps seed
                      (getf sample :wall) (getf sample :cpu) (getf sample :bytes)
                      (getf stats :n-accepted) (first result))
              (finish-output)))
          (assert (equal (comparable-result (first results)) (comparable-result (second results)))))))))
