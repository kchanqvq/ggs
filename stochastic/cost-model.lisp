(in-package :ggs/stochastic)

;;; A deliberately small proof language for cost invariance. Recognize pure,
;;; constructor-independent nonnegative integer sums, merged with MIN against a
;;; nonnegative bound. Unknown syntax fails closed; no user code is evaluated.
;;; All formulas denote MIN(bound, constant + SUM(coefficient * variable-cost)).
;;; Flattening nested clamps is valid because coefficients are positive integers
;;; and every remaining summand is nonnegative. Variables already lie in [0,B].
(defun additive-cost-model (name analysis)
  (block recognize
    (let ((bound (getf analysis :bottom)) (clauses (getf analysis :clauses)) (arities nil))
      (unless (and (equal (getf analysis :merge-form) '(function min))
                   (typep bound '(integer 0 #.most-positive-fixnum))
                   (subtypep (getf analysis :type) '(integer 0 *)))
        (return-from recognize nil))
      (dolist (clause clauses)
        (let* ((pattern (car clause)) (args (when (consp pattern) (cdr pattern))))
          (unless (and (listp pattern) pattern (every #'var-p pattern)
                       (notany #'seq-var-p pattern)
                       (= (length pattern) (length (remove-duplicates pattern)))
                       (= (length (cdr clause)) 1)
                       (not (assoc (length args) arities)))
            (return-from recognize nil))
          (let ((constant 0) (coefficients (make-list (length args) :initial-element 0)))
            (labels ((sum-form (form)
                       (cond ((typep form '(integer 0 *)) (incf constant form))
                             ((and (consp form) (eq (car form) '+))
                              (mapc #'sum-form (cdr form)))
                             ((and (consp form) (eq (car form) name)
                                   (= (length form) 2) (member (second form) args))
                              (incf (nth (position (second form) args) coefficients)))
                             (t (return-from recognize nil)))))
              (sum-form (second clause)))
            (push (list (length args) constant coefficients) arities))))
      (list bound arities))))

(defun model-cost-formula (model term)
  "Return a clamped affine formula and true, or NIL/NIL for unsupported syntax."
  (block unsupported
    (destructuring-bind (bound arities) model
      (labels ((normalize (constant coefficients)
                 (if (>= constant bound) (list bound nil)
                     (list constant (remove-if (lambda (x) (zerop (cdr x))) coefficients))))
               (walk (term)
                 (cond ((seq-var-p term) (return-from unsupported (values nil nil)))
                       ((var-p term) (normalize 0 (list (cons term 1))))
                       ;; A zero-argument template returns its head unchanged.
                       ;; A variable head may itself hold a compound node.
                       ((and (consp term) (null (cdr term))) (walk (car term)))
                       (t
                        (when (and (consp term) (seq-var-p (car term)))
                          (return-from unsupported (values nil nil)))
                        (let* ((args (when (consp term) (cdr term)))
                               (schema (assoc (length args) arities)))
                          ;; No matching analysis clause means BOTTOM.
                          (unless schema (return-from walk (list bound nil)))
                          (let ((constant (second schema)) (coefficients nil))
                            (loop for arg in args for scale in (third schema)
                                  unless (zerop scale) do
                                    (destructuring-bind (k terms) (walk arg)
                                      (incf constant (* scale k))
                                      (dolist (entry terms)
                                        (let ((previous (assoc (car entry) coefficients)))
                                          (if previous (incf (cdr previous) (* scale (cdr entry)))
                                              (push (cons (car entry) (* scale (cdr entry))) coefficients))))))
                            (normalize constant coefficients)))))))
        ;; Reject sequence splices even if their analysis coefficient is zero:
        ;; their length can change constructor arity and constant/compound status.
        (when (find-if #'seq-var-p (flatten term)) (return-from unsupported (values nil nil)))
        (values (walk term) t)))))

(defun model-cost-invariant-p (model lhs rhs)
  (when model
    (multiple-value-bind (left left-p) (model-cost-formula model lhs)
      (multiple-value-bind (right right-p) (model-cost-formula model rhs)
        (and left-p right-p (= (first left) (first right))
             (null (set-exclusive-or (second left) (second right) :test #'equal)))))))

(defun unconditional-rewrite-template (body)
  "Recognize a single unconditional YIELD-REWRITE without mutable bindings/guards."
  (when (= (length body) 1)
    (let ((form (first body)))
      (when (consp form)
        (case (car form)
          (yield-rewrite (when (= (length form) 2) (values (second form) t)))
          (when (when (eq (second form) t) (unconditional-rewrite-template (cddr form))))
          (symbol-macrolet
           ;; GET-RULES-RESOLVE-SYMBOLS adds precisely this history annotation.
           (when (and (= (length (second form)) 1)
                      (eq (caaadr form) '%current-ruleset%)
                      (equal (caadr (first (second form))) 'quote))
             (unconditional-rewrite-template (cddr form)))))))))

(defun specialize-invariant-rule-weight (rule model)
  (multiple-value-bind (rhs unconditional-p) (unconditional-rewrite-template (cdr rule))
    (if (and unconditional-p (model-cost-invariant-p model (car rule) rhs))
        `(,(car rule)
          (macrolet ((rewrite-weight (rhs)
                       (declare (ignore rhs)) '(fastexp2 0 beta-constant)))
            ,@(cdr rule)))
        rule)))
