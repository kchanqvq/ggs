(in-package :ggs/stochastic/tests)
(def-suite* :stochastic-cost-model :in :ggs/stochastic)

(defun comparable-result (result)
  (destructuring-bind (cost term stats) result
    (list cost term (getf stats :n-accepted) (getf stats :n-restart) (getf stats :full-history))))

;;; Both modes use the same search loop and a separately compiled function cache.
(defun weight-test-cache (rules cost optimize &key (proxy-cost cost) analyses)
  (let* ((layout (ggs/stochastic::analyses-alist cost proxy-cost analyses))
         (rules (ggs/stochastic::get-rules-resolve-symbols rules))
         (decls (ggs/util:get-user-decls nil))
         (key (list rules cost proxy-cost layout decls))
         (forms (ggs/stochastic::compute-rule-set-lambda
                 rules cost proxy-cost layout decls :optimize-invariant-weights optimize))
         (cache (make-hash-table :test 'equal)))
    (setf (gethash key cache)
          (loop for (name form) on forms by #'cddr
                collect name collect (compile nil form)))
    cache))

(defmacro with-weight-test-cache ((cache) &body body)
  `(let ((ggs/stochastic::*compiled-rule-sets* ,cache)) ,@body))

(define-analysis (capped-size :merge #'min :bottom 7 :type (integer 0 7))
  ((?f ?x ?y) (+ 1 (capped-size ?x) (capped-size ?y)))
  ((?f ?x) (+ 1 (capped-size ?x)))
  ((?f) 1))
(define-analysis (duplicated-cost :merge #'min :bottom +inf-cost+ :type cost)
  ((?f ?x ?y) (+ 1 (duplicated-cost ?x) (duplicated-cost ?y)))
  ((?f ?x) (+ 1 (duplicated-cost ?x) (duplicated-cost ?x)))
  ((?f) 1))
(define-analysis (literal-clause-cost :merge #'min :bottom +inf-cost+ :type cost)
  ((?f ?x) (+ 1 (literal-clause-cost ?x)))
  (a 1))
(define-analysis (negative-summand-cost :merge #'min :bottom +inf-cost+ :type cost)
  ((?f ?x) (+ -1 (negative-summand-cost ?x)))
  ((?f) 1))
(define-analysis (floating-cost :merge #'min :bottom 1e20 :type single-float)
  ((?f ?x) (+ 1.0 (floating-cost ?x)))
  ((?f) 1.0))

(define-analysis (ignored-child-cost :merge #'min :bottom 7 :type (integer 0 7))
  ((?f ?x) 1)
  ((?f ?x ?y) 2)
  ((?f) 1))
(defrw* unwrap-variable-head ((f ?x) (?x)))

(def-test invariant-cost-proof ()
  (flet ((model (name) (ggs/stochastic::additive-cost-model name (ggs/util:get-analysis name))))
    (dolist (analysis '(size capped-size duplicated-cost))
      (let ((m (model analysis)))
        (is (not (null m)))
        (is (ggs/stochastic::model-cost-invariant-p m '(+ (+ ?a ?b) ?c) '(+ ?a (+ ?b ?c))))
        (is (ggs/stochastic::model-cost-invariant-p m '(+ ?a ?b) '(+ ?b ?a)))
        (is (not (ggs/stochastic::model-cost-invariant-p m '(+ ?a ?b) '?a)))
        (is (not (ggs/stochastic::model-cost-invariant-p m '(f ?a ??rest) '(f ??rest ?a))))))
    (is (not (ggs/stochastic::model-cost-invariant-p
              (model 'ignored-child-cost) '(f ?x) '(?x))))
    (dolist (analysis '(depth weighted fanout literal-clause-cost negative-summand-cost floating-cost))
      (is (null (model analysis))))))

(defrw* invariant-mutating-guard
  ((+ ?a ?b) (+ ?b ?a) :guard (progn (setq ?a 0) t)))
(defrw* invariant-mutating-body
  ((+ ?a ?b) :eval (setq ?a 0) (yield-rewrite (+ ?b ?a))))
(def-test invariant-proof-keeps-arbitrary-rule-code ()
  (let ((model (ggs/stochastic::additive-cost-model 'size (ggs/util:get-analysis 'size))))
    (dolist (name '(invariant-mutating-guard invariant-mutating-body fold))
      (dolist (rule (ggs/stochastic::get-rules-resolve-symbols name))
        (is (equal rule (ggs/stochastic::specialize-invariant-rule-weight rule model))))))
  (is (= (ggs/stochastic::fastexp2 0 1) (ggs/stochastic::fastexp2 0 10000)))
  ;; The approximate exponential at zero must not be replaced with 1.0.
  (is (/= 1.0 (ggs/stochastic::fastexp2 0 1))))

(def-test invariant-weight-trajectories ()
  (let ((large (loop repeat 35 for x = '(f a) then (list 'f x) finally (return x))))
    (dolist (case (append
                  '(((f (g a b)) unwrap-variable-head ignored-child-cost)
                    ((+ (+ 1 2) (+ 3 4)) reassoc size)
                    ((+ (+ 1 2) (+ 3 4)) reassoc capped-size)
                    ((+ (+ 1 2) (+ 3 4)) reassoc depth :proxy-cost size)
                    ((* (* x x) (* y y)) powers weighted)
                    ((+ (+ a b) (+ c d)) invariant-mutating-guard size)
                    ((+ (+ a b) (+ c d)) invariant-mutating-body size)
                    ((+ (f (g x)) 0) guarded size :analyses (depth))
                    ((f a b c) rest-args size)
                    ((+ 2 (+ 3 4)) fold size))
                  (list (list `(+ (+ ,large b) c) 'reassoc 'duplicated-cost))))
      (destructuring-bind (term rules cost &rest options) case
        (let ((old (apply #'weight-test-cache rules cost nil options))
              (new (apply #'weight-test-cache rules cost t options)))
          (dolist (seed '(0 1 17))
            (dolist (walk '(0 20))
              (let* ((args (append options (list :seed seed :hard-walk walk :max-stall 80
                                                :max-restart 2 :target-cost 0 :save-full-history t)))
                     (before (with-weight-test-cache (old)
                               (multiple-value-list (apply #'search* term rules cost args)))))
                (is (equal (comparable-result before)
                           (comparable-result
                            (with-weight-test-cache (new)
                              (multiple-value-list (apply #'search* term rules cost args)))))
                    "weight optimization changed ~s seed ~a walk ~a" case seed walk)))))))))

(defun invariant-node-metadata (node)
  (if (ggs/stochastic::rose-node-p node)
      (list (ggs/stochastic::rose-node-fsym node)
            (float-features:single-float-bits (ggs/stochastic::rose-node-weight node))
            (ggs/stochastic::rose-node-n-rewrites node)
            (aref node 3)
            (loop for i from 4 below (length node) collect (invariant-node-metadata (aref node i))))
      node))

(def-test invariant-finalizer-exact-weights ()
  ;; Compare every node's float bits and counts, including saturation, zero
  ;; beta, and a unary analysis that doubles costs up to the 10^10 bound.
  (let* ((large (loop repeat 35 for x = '(f a) then (list 'f x) finally (return x)))
         (pieces (list 'a 0 '(f b) '(+ a b) large))
         (terms (loop for a in pieces append
                      (loop for b in pieces collect `(+ (+ ,a ,b) (+ ,b ,a))))))
    (dolist (analysis '(size capped-size duplicated-cost ignored-child-cost))
      (let* ((old (weight-test-cache 'reassoc analysis nil))
             (new (weight-test-cache 'reassoc analysis t))
             (old-functions (loop for value being the hash-values of old return value))
             (new-functions (loop for value being the hash-values of new return value)))
        (dolist (beta '(0 1 1000000))
          (dolist (term terms)
            (is (equal (invariant-node-metadata
                        (ggs/stochastic::term-node term 4 (getf old-functions 'ggs/stochastic::finalize-node) beta))
                       (invariant-node-metadata
                        (ggs/stochastic::term-node term 4 (getf new-functions 'ggs/stochastic::finalize-node) beta))))))))))
