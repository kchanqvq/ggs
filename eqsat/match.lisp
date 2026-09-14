(in-package :ggs/eqsat)

(defvar *fsym-info-var-alist*)

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
             (fsym-info-var (unless (var-p fsym)
                              (serapeum:ensure (assoc-value *fsym-info-var-alist* fsym)
                                (gensym-1 fsym))))
             (lhs-bound-p (member var bound-vars))
             (fsym-var-p (var-p fsym))
             (node-var (lisp-var var)))
        ;; FIXME: No index for ?fsym queries yet. Do we want one?

        ;; Currently we use indexes (in `fsym-info') as single source of truth
        ;; for matching, thus no-need to `enode-find' representative of VAR
        ;; (even if VAR is non-rep, it once was when we built the index in
        ;; `egraph-rebuild'
        `(dolist (,node-var
                  ,(cond (fsym-var-p
                          (assert lhs-bound-p)
                          `(list-enodes ,var))
                         (lhs-bound-p
                          `(gethash ,var (fsym-info-node-table ,fsym-info-var)))
                         (t `(fsym-info-nodes ,fsym-info-var))))
           ;; We check arity first, and SBCL seems to know to eliminate SVREF
           ;; bound checks in the body
           (when (= (enode-n-args ,node-var) ,(length arg-vars))
             (let (,@(when fsym-var-p
                       `((,fsym (enode-fsym ,node-var))))
                   ,@(mapcar (lambda (lisp-arg-var i)
                               `(,lisp-arg-var (svref ,node-var ,i)))
                             lisp-arg-vars (iota (length lisp-arg-vars) :start +enode-args-offset+)))
               (declare (ignorable ,@(when fsym-var-p `(,fsym)) ,@lisp-arg-vars))
               (when (and ,@(mapcan (lambda (lisp-var var)
                                      (when (and (var-p var) (not (var-p lisp-var)))
                                        `((eq ,lisp-var ,var))))
                                    lisp-arg-vars arg-vars))
                 ,(expand-match bound-vars rest cont-expr))))))
      cont-expr))

(defun expand-template (tmpl)
  "Generate code that creates an enode according to TMPL (rhs of rewrite rule)."
  (labels ((process (tmpl)
             (cond ((and (consp tmpl) (eql (car tmpl) :eval))
                    ;;; FIXME: assumes :eval only result in atoms
                    `(let ((key-node (vector nil 3 0 ,(cadr tmpl))))
                       (declare (dynamic-extent key-node))
                       (intern-enode key-node)))
                   ((consp tmpl)
                    `(let ((key-node (vector nil 3 0 ',(car tmpl) ,@(mapcar #'process (cdr tmpl)))))
                       (declare (dynamic-extent key-node))
                       (intern-enode key-node)))
                   ((var-p tmpl) tmpl)
                   (t (process (list tmpl))))))
    (process tmpl)))

(defmacro do-matches ((top-node-var pat) &body body)
  "Evaluate BODY for every PAT match in EGRAPH.

BODY is evaluated with variables in PAT bound to matched eclasses and
TOP-NODE-VAR bound to the enode matching PAT."
  (if (var-p pat) ; Special case for single variable PAT that scans all enodes
      `(maphash-keys
        (lambda (,pat)
          (let ((,top-node-var ,pat))
            (declare (ignorable ,top-node-var))
            ,@body))
        (egraph-classes *egraph*))
      (let* ((*fsym-info-var-alist* nil)
             (match-body
               (expand-match nil (parse-pattern pat top-node-var)
                             `(locally ,@body))))
        `(let ,(mapcar (lambda (kv) `(,(cdr kv)
                                      (ensure-gethash ',(car kv) (egraph-fsym-table *egraph*)
                                                      (make-fsym-info))))
                       *fsym-info-var-alist*)
           ,match-body))))
