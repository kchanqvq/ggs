(uiop:define-package :ggs/common
    (:use #:cl)
  (:import-from #:serapeum #:eval-always)
  (:export #:defrw #:defrw* #:yield-rewrite
           #:define-analysis #:make-or-test #:or-eql #:or-equal
           #:+inf-cost+ #:cost
           #:runtime-compile-warning))

(in-package :ggs/common)

(defmacro defrw (name &rest rule)
  "Define ruleset NAME consisting of a single RULE.

Equivalent to (DEFRW* NAME RULE), See DEFRW* for rule format."
  `(defrw* ,name ,rule))

(defmacro defrw* (name &body rules)
  "Define ruleset NAME consisting of RULES.

Each RULE can be either:

- A symbol that names another ruleset. It will be included in NAME.

- A list of form (LHS RHS [:guard CONDITION]). This defines a rule that match
  LHS pattern and rewrite to RHS, if CONDITION evaluates to true.

- A list of form (LHS :eval BODY...). This defines a rule that match LHS pattern
  and evaluate BODY for each match. BODY may use YIELD-REWRITE to yield
  candidate rewrites, potentially multiple times.

The rule (lhs rhs :guard condition) is equivalent to the :EVAL rule
\(lhs :eval (when condition (yield-rewrite rhs)))."
  (labels ((canonicalize (rule)
             (cond ((symbolp rule) rule)
                   ((eql (cadr rule) :eval)
                    (cons (car rule) (cddr rule)))
                   (t
                    (destructuring-bind (rhs &key (guard t)) (rest rule)
                      `(,(car rule)
                        (when ,guard (yield-rewrite ,rhs))))))))
    `(eval-always (setf (get ',name 'rules) ',(mapcar #'canonicalize rules)))))

(defmacro yield-rewrite (rhs)
  "Inside :EVAL rules, yield a candidate rewrite with RHS as template."
  (declare (ignore rhs))
  (error "YIELD-REWRITE must be used in :EVAL rules in `defrw' or `defrw*'."))

(defmacro get-analysis-data (name term)
  "What analysis accessor NAME expands to.

Backends should `macrolet' bind this placeholder inside `defrw', `defrw*' and `define-analysis'."
  (declare (ignore term))
  (error "Analysis accessor ~S can only be used inside `defrw', `defrw*' or `define-analysis'."
         name))

(defmacro define-analysis ((name &key merge bottom (type t)) &body clauses)
  "Define analysis NAME and a macro NAME that takes a single term argument and
returns its NAME analysis value. The macro can only be used inside `defrw',
`defrw*' or `define-analysis'.

MERGE should evaluate to a function that takes two arguments and return their
lattice merge, and BOTTOM should evaluate to the lattice bottom element.

Each CLAUSE should be of form (PAT BODY...). BODY should evaluates to the
analysis value for the term matching PAT."
  `(progn
     (defmacro ,name (term)
       ,(format nil "Return ~A analysis value for TERM.

Can only be used inside `defrw', `defrw*' or `define-analysis'."
                name)
       `(get-analysis-data ,',name ,term))
     (eval-always
       (setf (get ',name 'analysis)
             (list #+nil :merge #+nil ,merge :merge-form ',merge :bottom ,bottom :type ',type
                   :clauses '(,@clauses))))))

(define-condition runtime-compile-warning (warning)
  ((form :initarg :form))
  (:report (lambda (c s)
             (format s "~@<Compiling at runtime, precompile it with ~S~:@>"
                     (slot-value c 'form)))))

;;; Convenient merge functions

(declaim (inline make-or-test or-eql or-equal))
(defun make-or-test (test)
  (lambda (x y)
    (if x (if y (if (funcall test x y) x (error "Conflicting values: ~S vs ~S" x y)) x) y)))

;; At least SBCL has no problem fully inline these...
(defun or-eql (x y)
  "Like OR, but check (EQL X Y) if they are both non-nil."
  (funcall (make-or-test #'eql) x y))

(defun or-equal (x y)
  "Like OR, but check (EQUAL X Y) if they are both non-nil."
  (funcall (make-or-test #'equal) x y))

(defconstant +inf-cost+ (expt 10 10))

(deftype cost ()
  "Value type for cost analyses expected by stochastic backend."
  `(integer 0 ,+inf-cost+))

