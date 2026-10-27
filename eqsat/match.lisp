(in-package :ggs/eqsat)

(defun parse-pattern (pat eclass-var)
  "Convert PAT into a list of the form ((eclass-var fsym arg-var...) ...)."
  (cond ((consp pat)
         (let* ((fsym (car pat))
                (arg-vars (mapcar (lambda (arg) (if (var-p arg) arg (gensym-1 fsym))) (cdr pat))))
           (cons (list* eclass-var fsym arg-vars)
                 (mapcan (lambda (arg var)
                           (unless (var-p arg)
                             (parse-pattern arg var)))
                         (cdr pat) arg-vars))))
        ((var-p pat) (error "Single variable pattern should not be handled here."))
        (t ;; Non-variable atoms are short hand for 0-arity function symbol
         (parse-pattern (list pat) eclass-var))))

(defun expand-match (bound-vars subst-alist cont-expr)
  "Generate code that solves for SUBST-ALIST (as returned by `parse-pattern') then
evaluate CONT-EXPR."
  (if subst-alist
      (bind ((((var fsym . arg-vars) . rest) subst-alist)
             ((:flet lisp-var (var))
              (if (member var bound-vars)
                  (gensym-1 fsym)
                  (progn (push var bound-vars) var)))
             (lisp-arg-vars (mapcar #'lisp-var arg-vars))
             (lhs-bound-p (member var bound-vars))
             (fsym-var (and (var-p fsym) (lisp-var fsym)))
             (node-var (lisp-var var))
             ;; What happens after NODE-VAR is bound
             (body
              ;; We check arity first, and SBCL seems to know to eliminate SVREF
              ;; bound checks in the body
              `(when (= (enode-n-args ,node-var) ,(length arg-vars))
                 (let (,@(when fsym-var `((,fsym-var (enode-fsym ,node-var))))
                       ,@(mapcar (lambda (lisp-arg-var i)
                                   `(,lisp-arg-var (svref ,node-var ,i)))
                                 lisp-arg-vars
                                 (iota (length lisp-arg-vars) :start +enode-args-offset+)))
                   (declare (ignorable ,@(when fsym-var `(,fsym-var)) ,@lisp-arg-vars)
                            (type enode ,@lisp-arg-vars))
                   (when (and ,@(when fsym-var `((eq ,fsym-var ,fsym)))
                              ,@(mapcan (lambda (lisp-var var)
                                          (when (and (var-p var) (not (var-p lisp-var)))
                                            `((eq ,lisp-var ,var))))
                                        lisp-arg-vars arg-vars))
                     ,(expand-match bound-vars rest cont-expr))))))

        ;; Currently we use indexes (`egraph-fsym-index' and
        ;; `eclass-info-fsym-index') as single source of truth
        ;; for matching, thus no-need to `enode-find' representative of VAR
        ;; (even if VAR is non-rep, it once was when we built the index in
        ;; `egraph-rebuild'
        (cond (fsym-var
               (assert lhs-bound-p)
               `(dolist (%entry (eclass-info-fsym-index (enode-class-info ,var)))
                  (dolist (,node-var (cdr %entry))
                    (declare (type enode ,node-var))
                    ,body)))
              (lhs-bound-p
               `(dolist (,node-var (assoc-value (eclass-info-fsym-index (enode-class-info ,var))
                                                ',fsym))
                  (declare (type enode ,node-var))
                  ,body))
              (t `(dolist (%list (gethash ',fsym (egraph-fsym-index *egraph*)))
                    (dolist (,node-var %list)
                      (declare (type enode ,node-var))
                      ,body)))))
      cont-expr))

(defun expand-template (tmpl)
  "Generate code that creates an enode according to TMPL (rhs of rewrite rule)."
  (labels ((process (tmpl)
             (cond ((consp tmpl)
                    `(make-enode ,(if (var-p (car tmpl)) (car tmpl) `',(car tmpl))
                                 ,@(mapcar #'process (cdr tmpl))))
                   ((var-p tmpl) tmpl)
                   (t (process (list tmpl))))))
    (process tmpl)))

(defmacro do-match-all ((top-node-var pat) &body body)
  "Evaluate BODY for every PAT match in EGRAPH.

BODY is evaluated with variables in PAT bound to matched eclasses and
TOP-NODE-VAR bound to the enode matching PAT."
  (if (var-p pat) ; Special case for single variable PAT that scans all enodes
      `(dolist (,pat (egraph-class-list *egraph*))
         (let ((,top-node-var ,pat))
           (declare (ignorable ,top-node-var) (type enode ,pat ,top-node-var))
           ,@body))
      (expand-match nil (parse-pattern pat top-node-var)
                    `(locally ,@body))))
