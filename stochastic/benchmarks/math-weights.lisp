;;; Stochastic port of eqsat/tests/math.lisp, retaining its operator-weighted cost.
(require :asdf)
(asdf:load-asd (merge-pathnames "../../ggs.asd" *load-truename*))
(ql:quickload :ggs/stochastic/tests :silent t)
(uiop:define-package :ggs/stochastic/benchmarks/math
    (:use :cl :ggs/stochastic :alexandria))
(in-package :ggs/stochastic/benchmarks/math)

;;; An AST has one representation, not an e-class. As in the original guard,
;;; reject known literal 0 and allow unknown symbolic/compound values.
(defun non-zero-p (term) (not (eql term 0)))

;;; Read the shared definitions in this package. Do not load or run eqsat.
(let* ((source (uiop:read-file-string (merge-pathnames "../../eqsat/tests/math.lisp" *load-truename*)))
       (begin (search "(defrw* const-fold" source))
       (end (search "(defmacro def-math-test" source)))
  (assert (and begin end))
  (let ((*package* (find-package :ggs/stochastic/benchmarks/math)))
    (with-input-from-string (in (subseq source begin end))
      (loop for form = (read in nil :eof) until (eq form :eof)
            when (and (consp form) (member (car form) '(defrw defrw* define-analysis)))
              do (eval form)))))

(defparameter *math-cases*
  '(("simplify-root" (/ 1 (- (/ (+ 1 (sqrt five)) 2) (/ (- 1 (sqrt five)) 2))))
    ("simplify-factor" (* (+ x 3) (+ x 1)))
    ("diff-power-simple" (d x (pow x 3)))
    ("diff-power-harder" (d x (- (pow x 3) (* 7 (pow x 2)))))
    ("integral-part-1" (i (* x (cos x)) x))
    ("integral-part-2" (i (* (cos x) x) x))
    ("integral-part-3" (i (ln x) x))
    ("extract-power" (pow (+ x (+ x x)) (+ x x)))))

(defun math-search (case cache stall seed &optional history)
  (ggs/stochastic/tests::with-weight-test-cache (cache)
    (ggs/stochastic:stochastic-search
     (second case) 'math-all 'ast-size-no-d-or-i :max-restart 1 :max-stall stall
     :seed seed :hard-walk 20 :soft-walk 20 :soft-stall 1000
     :target-cost 0 :save-full-history history)))

(defun generated-form-text (form)
  ;; SBCL quasiquote forms contain comma objects, so EQUAL on the raw forms
  ;; compares their identity. Compare their complete readable Lisp instead.
  (with-standard-io-syntax (write-to-string form)))

(let* ((rules (ggs/stochastic::get-rules-resolve-symbols 'math-all))
       (cost 'ast-size-no-d-or-i)
       (analysis (ggs/util:get-analysis cost))
       (model (ggs/stochastic::additive-cost-model cost analysis))
       (layout (ggs/stochastic::analyses-alist cost cost nil))
       (decls (ggs/util:get-user-decls nil))
       (forms-off (ggs/stochastic::compute-rule-set-lambda rules cost cost layout decls :optimize-invariant-weights nil))
       (forms-on (ggs/stochastic::compute-rule-set-lambda rules cost cost layout decls :optimize-invariant-weights t))
       (caches (loop for optimize in (if (uiop:getenv "MATH_REVERSE_COMPILE") '(t nil) '(nil t))
                     collect (cons optimize (ggs/stochastic/tests::weight-test-cache 'math-all cost optimize))))
       (old (cdr (assoc nil caches)))
       (new (cdr (assoc t caches)))
       (start-seed (parse-integer (or (uiop:getenv "MATH_SEED_START") "0")))
       (stall (parse-integer (or (uiop:getenv "MATH_STALL") "1000000")))
       (rounds (parse-integer (or (uiop:getenv "MATH_ROUNDS") "6"))))
  (format t "~&COVERAGE rules=~d specialized=~d model=~s identical-generated-text=~s~%"
          (length rules)
          (count-if (lambda (r) (not (equal r (ggs/stochastic::specialize-invariant-rule-weight r model)))) rules)
          (not (null model)) (equal (generated-form-text forms-off) (generated-form-text forms-on)))
  (assert (null model))
  (assert (equal (generated-form-text forms-off) (generated-form-text forms-on)))
  (dolist (case *math-cases*)
    ;; Verify complete trajectories separately from the timed runs.
    (dotimes (seed 3)
      (assert (equal (ggs/stochastic/tests::comparable-result (multiple-value-list (math-search case old 100 seed t)))
                     (ggs/stochastic/tests::comparable-result (multiple-value-list (math-search case new 100 seed t))))))
    (dolist (cache (list old new)) (math-search case cache 1000 0))
    (loop for seed from start-seed below (+ start-seed rounds) do
      (let ((results nil))
        (dolist (optimize (if (evenp seed) '(nil t) '(t nil)))
          (sb-ext:gc :full t)
          (let* ((start (get-internal-real-time)) (cpu (get-internal-run-time))
                 (result (multiple-value-list (math-search case (if optimize new old) stall seed)))
                 (wall (/ (- (get-internal-real-time) start) (float internal-time-units-per-second 1d0)))
                 (cpu (/ (- (get-internal-run-time) cpu) (float internal-time-units-per-second 1d0)))
                 (stats (third result)))
            (push result results)
            (format t "~&MATH ~a ~a ~d stall=~d wall=~,6f cpu=~,6f moves=~d cost=~d restarts=~d~%"
                    (first case) (if optimize "ON" "OFF") seed stall wall cpu
                    (getf stats :n-accepted) (first result) (getf stats :n-restart))
            (finish-output)))
        (assert (equal (ggs/stochastic/tests::comparable-result (first results))
                       (ggs/stochastic/tests::comparable-result (second results)))))))
  (assert (= 1 (hash-table-count old) (hash-table-count new))))
