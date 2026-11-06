(in-package :ggs/stochastic/tests)

;;; The analysis compiler, through the public interface.  A rule's weight uses
;;; the analysis of its right-hand side computed at compile time, by matching
;;; the template statically, while the search reports the analysis of the node
;;; it builds.  Both must agree with each other and with the reference.
;;;
;;; A probe rule reads the static analysis: its :EVAL body is compiled with the
;;; same macros as a rule's weight, so (SIZE (TERM <template>)) there is the
;;; cost a weight would use.  The probe never rewrites.

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

(defun probe-vars (lhs)
  "The variables of LHS, the sequence variable last."
  (let ((vars (remove-duplicates (remove-if-not #'ggs/util:var-p (flatten lhs)))))
    (append (remove-if #'ggs/util:seq-var-p vars) (remove-if-not #'ggs/util:seq-var-p vars))))

(defun instantiate (template bindings)
  "TEMPLATE with BINDINGS substituted, splicing sequence variables.  A compound
term left without arguments is its function symbol, as the search builds it."
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

(defvar *probed* '()
  "(INDEX . ANALYSIS) recorded by probe rules.")

(defun probe-rule-set (name rules analysis)
  "Define rule set NAME with a probe for each of RULES.  Probe I matches
\(PROBE I . <variables of the left-hand side>) and records ANALYSIS of the
right-hand side."
  (eval `(defrw* ,name
           ,@(loop for (lhs rhs) in rules
                   for i from 0
                   collect `((probe ,i ,@(probe-vars lhs))
                             :eval (push (cons ,i (,analysis (ggs/util:term ,rhs))) *probed*)))))
  name)

(defun static-analysis (rule-set analysis i lhs bindings)
  "ANALYSIS of the right-hand side of probe I in RULE-SET with BINDINGS for
the variables of LHS, as a rule's weight computes it."
  (let ((*probed* '()))
    (search* `(probe ,i ,@(loop for var in (probe-vars lhs)
                                for value = (cdr (assoc var bindings))
                                if (ggs/util:seq-var-p var) append value
                                  else collect value))
             rule-set analysis)
    (assert (= 1 (length *probed*)) () "Probe ~a ran ~a times" i (length *probed*))
    (cdar *probed*)))

(defun node-analysis (term analysis)
  "ANALYSIS of TERM as the search reports it."
  (nth-value 0 (search* term 'no-rules analysis)))

(defun check-templates (name rules analysis)
  (let ((rule-set (probe-rule-set (symbolicate name '- analysis '-probes) rules analysis)))
    (loop for (lhs rhs) in rules
          for i from 0
          do (loop for shift below (length *sample-bindings*)
                   for bindings = (sample-bindings (probe-vars lhs) shift)
                   for instance = (instantiate rhs bindings)
                   for expected = (reference-cost analysis instance)
                   do (is (= expected (static-analysis rule-set analysis i lhs bindings))
                          "static ~a of ~s with ~s" analysis rhs bindings)
                      (is (= expected (node-analysis instance analysis))
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
  (is (= 1 (node-analysis 'c 'weighted)))
  (is (= 1 (node-analysis 5 'weighted))))

(def-test template-with-variable-fsym ()
  ;; ?G is only known at run time, but the template has arguments, so only the
  ;; compound clauses apply: the constant clause ((?F) 1) must not.
  (let* ((lhs '(p ?g ?x))
         (rhs '(?g ?x (f ?x)))
         (rule-set (probe-rule-set 'fsym-probes `((,lhs ,rhs)) 'weighted)))
    (dolist (g '(h pow))
      (let ((bindings `((?g . ,g) (?x . c))))
        (is (= (tree-weighted (instantiate rhs bindings))
               (static-analysis rule-set 'weighted 0 lhs bindings))
            "static weighted of ~s with ?g = ~a" rhs g)))))
