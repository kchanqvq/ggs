(in-package :ggs/stochastic/tests)

;;; The analysis compiler: a right-hand side's cost is computed at compile time
;;; by matching the template statically (do-match* on a term form), while a new
;;; node's analyses are computed at run time by RECOMPUTE-ROSE.  Both must agree
;;; with each other and with the reference.

(def-suite* :stochastic-analysis :in :ggs/stochastic)

(defmacro def-template-rules (name &body rules)
  `(progn
     (defparameter ,(symbolicate '* name '*) ',rules)
     (defrw* ,name ,@rules)))

(def-template-rules templates
  ((tan ?x) (/ (sin ?x) (cos ?x)))
  ((/ (sin ?x) (cos ?x)) (tan ?x))
  ((- 1 (pow (cos ?x) 2)) (pow (sin ?x) 2))
  ((* (+ ?a ?b) (+ ?a ?b)) (pow (+ ?a ?b) 2))
  ((pow ?a 2) (* ?a ?a))
  ((+ ?a ?b) (+ ?b ?a))
  ((+ ?a 0) ?a)
  (?a (+ ?a 0))
  ((* ?a 1) ?a)
  ((* ?a 0) 0)
  ((f ?x ?y ?z) (g ?z (pow ?y ?x) ?x)))

(precompile-stochastic-rule-set templates size)
(precompile-stochastic-rule-set templates weighted)

(defparameter *sample-bindings*
  '(c 5 (h c) (k (h c) d) (pow c 3))
  "Terms bound to the template variables, constants and nodes alike.")

(defun template-vars (template)
  (remove-duplicates (remove-if-not #'ggs/util:var-p (flatten template))))

(defun instantiate (template bindings)
  (sublis bindings template))

(defun rule-set-context (rule-set analysis)
  "Offset, analyses alist and compiled rule set used by STOCHASTIC-SEARCH."
  (let* ((alist (ggs/stochastic::analyses-alist analysis analysis nil))
         (offset (+ ggs/stochastic::+rose-node-args-offset+ (length alist))))
    (values offset alist
            (handler-bind ((runtime-compile-warning #'muffle-warning))
              (ggs/stochastic::compiled-rule-set rule-set analysis analysis alist)))))

(defun make-node (term offset rule-set-plist)
  "TERM as rose nodes with their analyses filled in."
  (let ((node (ggs/stochastic::term-node term offset)))
    (ggs/stochastic::recompute-rose node offset (getf rule-set-plist 'ggs/stochastic::compute-weights)
                                    (ggs/stochastic::constant-for-fastexp2 (exp 1.0)))
    node))

(defun static-cost (template analysis offset alist bindings rule-set-plist)
  "ANALYSIS of TEMPLATE computed the way a rule's weight computes it."
  (let* ((vars (mapcar #'car bindings))
         (f (handler-bind ((warning #'muffle-warning))
              (compile nil `(lambda ,vars
                              (declare (ignorable ,@vars))
                              (macrolet ((ggs/common::get-analysis-data (name term &environment env)
                                           (ggs/stochastic::expand-analysis-access
                                            ,offset name ',alist term env)))
                                (ggs/common::get-analysis-data ,analysis (ggs/util:term ,template))))))))
    (apply f (mapcar (lambda (b) (make-node (cdr b) offset rule-set-plist)) bindings))))

(defun dynamic-cost (term offset rule-set-plist)
  "ANALYSIS of TERM computed on its node, the way the search reads its objective."
  (funcall (getf rule-set-plist 'ggs/stochastic::get-cost) (make-node term offset rule-set-plist)))

(defun check-templates (rule-set rules analysis)
  (multiple-value-bind (offset alist plist) (rule-set-context rule-set analysis)
    (loop for (lhs rhs) in rules
          do (loop for shift below (length *sample-bindings*)
                   for bindings = (loop for var in (template-vars lhs)
                                        for i from shift
                                        collect (cons var (nth (mod i (length *sample-bindings*))
                                                               *sample-bindings*)))
                   for instance = (instantiate rhs bindings)
                   for expected = (reference-cost analysis instance)
                   do (is (= expected (static-cost rhs analysis offset alist bindings plist))
                          "static ~a of ~s with ~s" analysis rhs bindings)
                      (is (= expected (dynamic-cost instance offset plist))
                          "node ~a of ~s" analysis instance)))))

(def-test template-costs-size ()
  (check-templates 'templates *templates* 'size))

(def-test template-costs-weighted ()
  (check-templates 'templates *templates* 'weighted))

(def-test constant-analysis ()
  ;; A constant has no node; its analysis comes from the constant clauses.
  (multiple-value-bind (offset alist plist) (rule-set-context 'templates 'weighted)
    (declare (ignore alist))
    (is (= 1 (dynamic-cost 'c offset plist)))
    (is (= 1 (dynamic-cost 5 offset plist)))))
