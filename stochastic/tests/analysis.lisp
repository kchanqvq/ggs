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

(defparameter *sample-sequences*
  '(() (c) (5 (h c)) ((k (h c) d) c (pow c 3)))
  "Term lists bound to the sequence variables.")

(defun template-vars (template)
  (remove-duplicates (remove-if-not #'ggs/util:var-p (flatten template))))

(defun instantiate (template bindings)
  "TEMPLATE with BINDINGS substituted, splicing sequence variables.  A compound
term left without arguments is its function symbol, as in EXPAND-TEMPLATE."
  (cond ((consp template)
         (let ((term (mapcan (lambda (x)
                               (if (ggs/util:seq-var-p x)
                                   (copy-list (cdr (assoc x bindings)))
                                   (list (instantiate x bindings))))
                             template)))
           (if (cdr term) term (car term))))
        ((assoc template bindings) (cdr (assoc template bindings)))
        (t template)))

(defun sample-bindings (vars shift)
  (loop for var in vars
        for i from shift
        for pool = (if (ggs/util:seq-var-p var) *sample-sequences* *sample-bindings*)
        collect (cons var (nth (mod i (length pool)) pool))))

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
                              ;; The MACROLETS of COMPUTE-RULE-SET-LAMBDA
                              (macrolet ((ggs/common::get-analysis-data (name term &environment env)
                                           (ggs/stochastic::expand-analysis-access
                                            ,offset name ',alist term env))
                                         (ggs/util:term (tmpl)
                                           (ggs/stochastic::expand-template tmpl ',alist)))
                                (ggs/common::get-analysis-data ,analysis (ggs/util:term ,template))))))))
    (apply f (mapcar (lambda (b)
                       (if (ggs/util:seq-var-p (car b))
                           (mapcar (lambda (term) (make-node term offset rule-set-plist)) (cdr b))
                           (make-node (cdr b) offset rule-set-plist)))
                     bindings))))

(defun dynamic-cost (term offset rule-set-plist)
  "ANALYSIS of TERM computed on its node, the way the search reads its objective."
  (funcall (getf rule-set-plist 'ggs/stochastic::get-cost) (make-node term offset rule-set-plist)))

(defun check-templates (rule-set rules analysis)
  (multiple-value-bind (offset alist plist) (rule-set-context rule-set analysis)
    (loop for (lhs rhs) in rules
          do (loop for shift below (length *sample-bindings*)
                   for bindings = (sample-bindings (template-vars lhs) shift)
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

;; Sequence variables in templates, and arguments matched by the sequence
;; variables of FANOUT and LAST-HEAVY.  Those need every argument at run time,
;; so these templates have no compound arguments.
(def-template-rules seq-templates
  ((f ?x ??xs) (g ??xs))
  ((f ?x ??xs) (g ?x ??xs))
  ((f ?x ??xs) (g ??xs ?x 0))
  ((f ?x ??xs) (g ??xs a ??xs))
  ((f ?x ?y) (g ?y ?x a)))

(def-test template-costs-sequence-variables ()
  ;; SIZE and WEIGHTED have clauses for up to three arguments
  (let ((*sample-sequences* '(() (c) ((k (h c) d)))))
    (check-templates 'seq-templates *seq-templates* 'size)
    (check-templates 'seq-templates *seq-templates* 'weighted))
  (check-templates 'seq-templates *seq-templates* 'fanout)
  (check-templates 'seq-templates *seq-templates* 'last-heavy))

(def-test constant-analysis ()
  ;; A constant has no node; its analysis comes from the constant clauses.
  (multiple-value-bind (offset alist plist) (rule-set-context 'templates 'weighted)
    (declare (ignore alist))
    (is (= 1 (dynamic-cost 'c offset plist)))
    (is (= 1 (dynamic-cost 5 offset plist)))))

(def-test template-with-variable-fsym ()
  ;; ?G is only known at run time, but the template has arguments, so only the
  ;; compound clauses apply: the constant clause ((?F) 1) must not.
  (multiple-value-bind (offset alist plist) (rule-set-context 'templates 'weighted)
    (dolist (g '(h pow))
      (let ((bindings `((?g . ,g) (?x . c))))
        (is (= (tree-weighted (instantiate '(?g ?x (f ?x)) bindings))
               (static-cost '(?g ?x (f ?x)) 'weighted offset alist bindings plist))
            "static weighted of (?g ?x (f ?x)) with ?g = ~a" g)))))
