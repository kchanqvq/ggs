;;;; Pattern matching compiler
;;;
;;; `do-match*' compiles multiple (PAT BODY...) clauses into a single decision
;;; tree. This is used for both matching all rules in a rule-set simultaneously,
;;; and for compiling analyses. For the analyses use case, the compiler also
;;; partial evaluates over partially static subject. Therefore, analysis values
;;; (especially cost analysis) over (TERM TMPL) can be computed without
;;; materializing the term.
;;;
;;; `do-match*' itself handles renaming non-linear variables in lhs patterns and
;;; renaming variables in partially static subject, then outsource to
;;; `%do-match*'. The latter calls a number of functions (`expand-*') to compute
;;; the expansion in essentially one macroexpand step. It would be tempting to
;;; write some of these functions as macros to decompose into multiple
;;; macroexpand steps. However, between macros, it's much easier to pass
;;; information down than up (impossible?). Consider what would happen to
;;; `*need-args*'.

(in-package :ggs/stochastic)

(defmacro do-match* (offset category subject &body clauses &environment env)
  "Match SUBJECT against CLAUSES, each of the form (PAT BODY...).

At runtime, SUBJECT should be either an unboxed constant or a variadic structure
inheriting `rose-node', and OFFSET should be an expansion-time constant number
that locates ARGS slots in SUBJECT. Partial evaluate if SUBJECT is partially
static, i.e. of form (TERM TMPL).

CATEGORY can be one of T, CONSTANT, COMPOUND. If CATEGORY is CONSTANT, SUBJECT
is assumed to be an unboxed constant at runtime; similarly for COMPOUND. If
CATEGORY is T, assume either of the two cases may happen."
  (bind ((subject (term-form-from-env subject env))
         ;; Rename any variables in SUBJECT to avoid variable capture
         ((:values bindings subject)
          (if (term-form-p subject)
              (let ((renames (mapcar (lambda (var) (cons var (gensym-1 var)))
                                     (remove-duplicates
                                      (remove-if-not #'var-p (flatten subject))))))
                (values (mapcar (lambda (r) (list (cdr r) (car r))) renames)
                        (sublis renames subject)))
              (let ((var (gensym "SUBJECT")))
                (values `((,var ,subject)) var)))))
    `(let ,bindings
       (declare (ignorable ,@(mapcar #'car bindings)))
       (%do-match* ,offset ,category (,subject)
         ,@(mapcar (lambda (clause)
                     (bind (((pat . body) clause))
                       (multiple-value-list
                        (decompose-consistency-check pat offset body))))
                   clauses)))))

(defun decompose-consistency-check (pat offset body)
  "For a `do-match*' clause like (PAT BODY...), rename all non-linear variables
in PAT to distinct linear ones, and wrap BODY with variable consistency checks.
Return the renamed pattern and wrapped BODY (a single form)."
  (let (vars checks)
    (labels ((process-var (var)
               (cond ((member var vars)
                      (lret ((new-var (gensym-1 var)))
                        (push `(,(if (seq-var-p var) 'seq-equal 'node-equal)
                                ,var ,new-var ,offset)
                              checks)))
                     (t (push var vars)
                        var)))
             (process (pat)
               (cond ((consp pat)
                      (cons (if (var-p (car pat)) (process-var (car pat)) (car pat))
                            (mapcar #'process (cdr pat))))
                     ((var-p pat) (process-var pat))
                     (t pat))))
      (values (process pat) `(when (and ,@checks) ,@body)))))

(defvar-unbound *need-args*
  "Ask `%do-match*' to generate an %arg variable binding that reify the
argument list.")

(defun arity-info (pat)
  (if (consp pat)
      (list (1- (length pat)) (seq-var-pos (cdr pat)))
      '(0 nil)))

(defmacro %do-match* (offset category subject-list &body pat-mat &environment env)
  "Assume patterns are linear, do simultaneous match against SUBJECT-LIST."

  (cond ((null pat-mat)
         (return-from %do-match* nil))
        ((null subject-list)
         (return-from %do-match*
           `(progn ,@(mapcar #'serapeum:only-elt pat-mat))))
        ((not (or (eq category t) (= (length subject-list) 1)))
         (error "CATEGORY only make sense for single subject.")))

  (bind (((:values subject-list pat-mat) (select-pat-column subject-list pat-mat))
         ((subject . rest) subject-list)
         (subject (term-form-from-env subject env))
         *need-args*
         ((:values bind-rows constructor-rows) (partition #'var-p pat-mat :key #'car))
         (fsym-groups (assort constructor-rows :key (compose #'ensure-car #'car)))
         (fsym-arity-groups (mapcar (rcurry #'assort :key (compose #'arity-info #'car))
                                    fsym-groups))
         ((:values compound-clauses constant-clauses)
          (groups-to-fsym-clauses offset subject rest fsym-arity-groups)))

    `(let ,(when *need-args*
             `((%args (append ,@(mapcar (lambda (a)
                                          (if (seq-var-p a) a `(list (term ,a))))
                                        (cdadr subject))))))
       ,@(expand-bind-rows offset subject rest bind-rows)
       ,@(ecase category
           ((t) (cond ((term-form-p subject)
                       `(,@(expand-constant-clauses subject constant-clauses)
                         ,@(expand-compound-clauses subject compound-clauses)))
                      ((or constant-clauses compound-clauses)
                       `((if (rose-node-p ,subject)
                             (progn ,@(expand-compound-clauses subject compound-clauses))
                             (progn ,@(expand-constant-clauses subject constant-clauses)))))))
           (constant (expand-constant-clauses subject constant-clauses))
           (compound (expand-compound-clauses subject compound-clauses))))))

(defun expand-bind-rows (offset subject rest bind-rows)
  (when bind-rows
    `((%do-match* ,offset t ,rest
        ,@(mapcar (lambda (pat-row)
                    `(,@(butlast (cdr pat-row))
                      (let/static ((,(car pat-row) ,subject))
                        (declare (ignorable ,(car pat-row)))
                        ,(lastcar pat-row))))
                  bind-rows)))))

(defun arity-check-form (offset subject n-args allow-more
                         &aux (cmp (if allow-more '>= '=)))
  "Compute a form that check if SUBJECT has exactly N-ARGS, or if ALLOW-MORE is
non-nil, at least N-ARGS."
  (trivia:ematch subject
    ((type symbol)
     `(,cmp (n-variadic-slots ,offset ,subject) ,n-args))
    ((list 'term (list* _ args))
     (bind (((:values seq-var-args normal-args) (partition #'seq-var-p args))
            (seq-var-length-form `(+ ,@(mapcar (lambda (a) `(length ,a)) seq-var-args))))
       (if seq-var-args
           `(,cmp ,seq-var-length-form ,(- n-args (length normal-args)))
           (funcall cmp (length args) n-args))))))

(defun first-seq-var-pos (args)
  (or (position-if #'seq-var-p args) (length args)))

(defun last-seq-var-pos (args)
  (or (position-if #'seq-var-p args :from-end t) -1))

(defun arg-form (offset subject i)
  "Return a form that computes argument I of SUBJECT."
  (trivia:ematch subject
    ((type symbol) `(get-variadic-slot ,i ,offset ,subject))
    ((list 'term (list* _ args))
     (cond ((< i (first-seq-var-pos args))
            (normalize-term-form `(term ,(nth i args))))
           (t (setq *need-args* t)
              `(nth ,i %args))))))

(defun arg-from-end-form (subject from-end)
  "Return a form that computes argument FROM-END of SUBJECT counting from the end."
  (trivia:ematch subject
    ((type symbol) `(variadic-slot-from-end ,from-end ,subject))
    ((list 'term (list* _ args))
     (let ((j (- (length args) (1+ from-end))))
       (cond ((> j (last-seq-var-pos args))
              (normalize-term-form `(term ,(nth j args))))
             (t (setq *need-args* t)
                `(nth (- (length %args) ,(1+ from-end)) %args)))))))

(defun args-between-form (offset subject i from-end)
  "Return a form that computes the list of arguments of SUBJECT from I to FROM-END."
  (trivia:ematch subject
    ((type symbol) `(variadic-slots-between ,i ,from-end ,offset ,subject))
    ((list 'term (list* _ args))
     (let ((j (- (length args) (1+ from-end))))
       (cond ((and (<= i (first-seq-var-pos args))
                   (<= (last-seq-var-pos args) j))
              `(append ,@(mapcar (lambda (arg)
                                   (if (seq-var-p arg) arg `(list (term ,arg))))
                                 (subseq args i (1+ j)))))
             (t (setq *need-args* t)
                `(subseq %args ,i (- (length %args) ,from-end))))))))

(defun select-pat-column (subject-list pat-mat)
  "Pattern column selection heuristics."
  (let* ((pat-mat (copy-tree pat-mat))
         (subject-list (copy-list subject-list))
         (columns (butlast (apply #'mapcar #'list pat-mat)))
         (column-n-tested (mapcar (lambda (c)
                                    (count-if-not #'var-p (mapcar #'ensure-car c)))
                                  columns))
         (selected (position (reduce #'max column-n-tested)
                             column-n-tested)))
    (rotatef (car subject-list) (nth selected subject-list))
    (dolist (row pat-mat)
      (rotatef (car row) (nth selected row)))
    (values subject-list pat-mat)))

(defun groups-to-fsym-clauses (offset subject rest groups)
  (with-collectors (compound-clauses constant-clauses)
    (dolist (arity-groups groups)
      (let ((fsym (ensure-car (caaar arity-groups))))
        (with-collectors (compound-clauses-1 constant-clauses-1)
          (dolist (pat-rows arity-groups)
            (bind (((n-args seq-var-pos) (arity-info (caar pat-rows)))
                   (arg-vars (make-gensym-list n-args (prin1-to-string fsym))))

              (when (> n-args 0)
                (when-let (check (if seq-var-pos
                                     (arity-check-form offset subject (1- n-args) t)
                                     (arity-check-form offset subject n-args nil)))
                  (compound-clauses-1
                   `(when ,check
                      (let/static
                          ,(loop for var in arg-vars
                                 for i from 0
                                 collect
                                 `(,var
                                   ,(case (if seq-var-pos (signum (- i seq-var-pos)) -1)
                                      (-1 (arg-form offset subject i))
                                      (0 (args-between-form offset subject i (- n-args i 1)))
                                      (1 (arg-from-end-form subject (- n-args i 1))))))
                        (%do-match* ,offset t ,(append arg-vars rest)
                          ,@(mapcar (lambda (pat-row)
                                      (append (cdar pat-row) (cdr pat-row)))
                                    pat-rows)))))))

              (when (= n-args 0)
                (constant-clauses-1
                 `(%do-match* ,offset t ,rest ,@(mapcar #'cdr pat-rows))))

              ;; Single SEQ-VAR matches constant and binds to NIL
              (when (and (= n-args 1) (eql seq-var-pos 0))
                (constant-clauses-1
                 `(%do-match* ,offset t ,(cons nil rest)
                    ,@(mapcar (lambda (pat-row)
                                (append (cdar pat-row) (cdr pat-row)))
                              pat-rows))))))

          (when (compound-clauses-1)
            (compound-clauses `((,fsym) ,@(compound-clauses-1))))
          (when (constant-clauses-1)
            (constant-clauses `((,fsym) ,@(constant-clauses-1)))))))))

(defun expand-fsym-clauses (fsym clauses)
  "Like (CASE/BIND FSYM CLAUSES...), but partial evaluate if FSYM is static."
  (if (var-p fsym)
      `((case/bind ,fsym ,@clauses))
      (mappend (lambda (c)
                 (cond ((eql (caar c) fsym) (cdr c))
                       ((var-p (caar c))
                        `((symbol-macrolet ((,(caar c) ',fsym))
                            ,@(cdr c))))))
               clauses)))

(defun expand-constant-clauses (subject constant-clauses)
  "Like (CASE/BIND SUBJECT CLAUSES...), but assume SUBJECT is a constant and
partial evaluate if SUBJECT is partially static."
  (unless constant-clauses
    (return-from expand-constant-clauses nil))
  (trivia:ematch subject
    ((type symbol) `((case/bind ,subject ,@constant-clauses)))
    ((list 'term (list* fsym args))
     (when (every #'seq-var-p args)
       `((unless (or ,@args)
           ,@(expand-fsym-clauses fsym constant-clauses)))))))

(defun expand-compound-clauses (subject compound-clauses)
  "Like (CASE/BIND (ROSE-NODE-FSYM SUBJECT) CLAUSES...), but assume SUBJECT is a
compound (rose-node) and partial evaluate if SUBJECT is partially static."
  (unless compound-clauses
    (return-from expand-compound-clauses nil))
  (trivia:ematch subject
    ((type symbol) `((case/bind (rose-node-fsym ,subject) ,@compound-clauses)))
    ((list 'term (list* fsym args))
     (when args
       (if (every #'seq-var-p args)
           `((when (or ,@args)
               ,@(expand-fsym-clauses fsym compound-clauses)))
           (expand-fsym-clauses fsym compound-clauses))))))
