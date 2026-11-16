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
;;; `%do-match*'. `%do-match*' decompose the matching task recursively:
;;; `%do-match-1' handle one level of fsym and arity matching, remaining levels
;;; become recursive invocation of `%do-match*'.

(in-package :ggs/stochastic)

(defun term-form-p (form)
  (and (consp form) (eq (car form) 'term)
       (or (= (length form) 2) (error "Illegal term form: ~S" form))))

(defun resolve-term-form (form env)
  "Try to expand FORM to (TERM ...) in ENV and normalize it to (TERM (FSYM
ARGS...)). (TERM ?VAR) normalizes to bare ?VAR (no longer a term form)."
  (labels ((try (form)
             (cond ((not (term-form-p form))
                    (multiple-value-bind (form-1 expanded) (macroexpand-1 form env)
                      (if expanded (try form-1) form)))
                   ((var-p (cadr form)) (cadr form))
                   ((not (consp (cadr form))) `(term (,(cadr form))))
                   (t form))))
    (try form)))

(defun expand-to-term-form-p (form env)
  (term-form-p (resolve-term-form form env)))

(defmacro do-match* (offset category subject &body clauses &environment env)
  "Match SUBJECT against CLAUSES, each of the form (PAT BODY...).

At runtime, SUBJECT should be either an unboxed constant or a variadic structure
inheriting `rose-node'. Partial evaluate if SUBJECT is partially
static, i.e. of form (TERM TMPL).

CATEGORY can be one of T, CONSTANT, COMPOUND. If CATEGORY is CONSTANT, SUBJECT
is assumed to be an unboxed constant at runtime; similarly for COMPOUND. If
CATEGORY is T, assume either of the two cases may happen.

OFFSET should be a literal constant number that locates argument slots in
SUBJECT. `do-match*' binds a symbol macro `%offset%' to this number to save us
from passing it around between macros."
  (bind ((subject (resolve-term-form subject env))
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
       (symbol-macrolet ((%offset% ,offset))
         (%do-match* ,category (,subject)
           ,@(mapcar (lambda (clause)
                       (bind (((pat . body) clause))
                         (multiple-value-list
                          (decompose-consistency-check pat body))))
                     clauses))))))

(defun decompose-consistency-check (pat body)
  "For a `do-match*' clause like (PAT BODY...), rename all non-linear variables
in PAT to distinct linear ones, and wrap BODY with variable consistency checks.
Return the renamed pattern and wrapped BODY (a single form)."
  (let (vars checks)
    (labels ((process-var (var)
               (cond ((member var vars)
                      (lret ((new-var (gensym-1 var)))
                        (push `(,(if (seq-var-p var) 'seq-equal 'node-equal)
                                ,var ,new-var %offset%)
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

(defun fsym-arity-info (pat)
  (if (consp pat)
      (list (car pat) (1- (length pat)) (seq-var-pos (cdr pat)))
      (list pat 0 nil)))

(defmacro %do-match* (category subject-list &body pat-mat)
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
         ((:values bind-rows constructor-rows) (partition #'var-p pat-mat :key #'car)))
    `(progn
       ,(when bind-rows
          `(%do-match* t ,rest
             ,@(mapcar (lambda (pat-row)
                         `(,@(butlast (cdr pat-row))
                           (symbol-macrolet ((,(car pat-row) ,subject))
                             ,(lastcar pat-row))))
                       bind-rows)))
       (%do-match-1 ,category ,subject
         ,@(mapcar
           (lambda (rows)
             (bind (((fsym . arg-pats) (ensure-list (caar rows)))
                    (arg-vars (mapcar (lambda (pat)
                                        (gensym (if (seq-var-p pat) "??ARGS" "?ARG")))
                                      arg-pats)))
               `((,fsym ,@arg-vars)
                 (%do-match* t ,(append arg-vars rest)
                   ,@(mapcar (lambda (row)
                               (append (cdr (ensure-list (car row))) (cdr row)))
                             rows)))))
           (assort constructor-rows :key (compose #'fsym-arity-info #'car)
                                    :test #'equal))))))

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

(defun merge-similar-clauses (clauses)
  (mapcar (lambda (fsym-group) (cons (caar fsym-group) (mappend #'cdr fsym-group)))
          (assort clauses :key (compose #'ensure-car #'car))))

(defmacro %do-match-1 (category subject &body clauses &environment env)
  "Match SUBJECT against CLAUSES of the form ((FSYM VAR...) BODY...)."
  (bind (compound-clauses constant-clauses)

    (dolist (clause clauses)
      (bind (((pat . body) clause)
             ((fsym n-args seq-var-pos) (fsym-arity-info pat)))

        (when (> n-args 0)
          (when-let (check (macroexpand
                            (if seq-var-pos
                                `(arity-check/static >= ,subject ,(1- n-args))
                                `(arity-check/static = ,subject ,n-args))
                            env))
            (push `((,fsym)
                    (when ,check
                      (let/static expand-to-term-form-p
                          ,(loop for var in (cdr pat)
                                 for i from 0
                                 collect
                                 `(,var
                                   ,(case (if seq-var-pos (signum (- i seq-var-pos)) -1)
                                      (-1 `(get-arg/static ,subject ,i))
                                      (0 `(get-args-between/static ,subject ,i ,(- n-args i 1)))
                                      (1 `(get-arg-from-end/static ,subject ,(- n-args i 1))))))
                        (declare (ignorable ,@(cdr pat)))
                        ,@body)))
                  compound-clauses)))

        (when (= n-args 0)
          (push `((,fsym) ,@body) constant-clauses))

        ;; Single SEQ-VAR matches constant and binds to NIL
        (when (and (= n-args 1) seq-var-pos)
          (push `((,fsym)
                  (symbol-macrolet ((,(cadr pat) nil)) ,@body))
                constant-clauses))))

    (setq compound-clauses (merge-similar-clauses (nreverse compound-clauses))
          constant-clauses (merge-similar-clauses (nreverse constant-clauses)))

    (ecase category
      ((t) (cond ((expand-to-term-form-p subject env)
                  `(progn (case/bind/constant ,subject ,@constant-clauses)
                          (case/bind/compound ,subject ,@compound-clauses)))
                 ((or constant-clauses compound-clauses)
                  `(if (rose-node-p ,subject)
                       (case/bind/compound ,subject ,@compound-clauses)
                       (case/bind/constant ,subject ,@constant-clauses)))))
      (constant `(case/bind/constant ,subject ,@constant-clauses))
      (compound `(case/bind/compound ,subject ,@compound-clauses)))))

(defmacro case/bind/static (fsym &body clauses)
  "Like (CASE/BIND FSYM CLAUSES...), but partial evaluate if FSYM is constant."
  (if (var-p fsym)
      `(case/bind ,fsym ,@clauses)
      `(progn
         ,@(mappend (lambda (c)
                      (cond ((eql (caar c) fsym) (cdr c))
                            ((var-p (caar c))
                             `((symbol-macrolet ((,(caar c) ',fsym))
                                 ,@(cdr c))))))
                    clauses))))

(defmacro case/bind/constant (subject &body clauses &environment env)
  "Like (CASE/BIND SUBJECT CLAUSES...), but assume SUBJECT is an unboxed constant
and partial evaluate if SUBJECT expands to (TERM ...)."
  (trivia:ematch (resolve-term-form subject env)
    ((type symbol) `(case/bind ,subject ,@clauses))
    ((list 'term (list* fsym args))
     (when (every #'seq-var-p args)
       `(unless (or ,@args)
          (case/bind/static ,fsym ,@clauses))))))

(defmacro case/bind/compound (subject &body clauses &environment env)
  "Like (CASE/BIND (ROSE-NODE-FSYM SUBJECT) CLAUSES...), but assume SUBJECT is a
compound (rose-node) and partial evaluate if SUBJECT expands to (TERM ...).

Bind a lexical variable `%args%' around its expansion, which is useful for
reifying argument list of SUBJECT on demand. Also bind a `%ensure-args%' macro
that reifies the argument list and store into `%args%' if `%args%' is NIL,
otherwise use memoized `%args%'. `get-arg*/static' use these."
  (trivia:ematch (resolve-term-form subject env)
    ((type symbol) `(case/bind (rose-node-fsym ,subject) ,@clauses))
    ((list 'term (list* fsym args))
     (when args
       `(let (%args%)
          (declare (ignorable %args%))
          (macrolet ((%ensure-args% ()
                       `(or %args%
                            (setq %args%
                                  (append ,@',(mapcar (lambda (a)
                                                        (if (seq-var-p a) a `(list (term ,a))))
                                                      args))))))

            ,(if (every #'seq-var-p args)
                 `(when (or ,@args)
                    (case/bind/static ,fsym ,@clauses))
                 `(case/bind/static ,fsym ,@clauses))))))))

(defmacro arity-check/static (cmp subject n-args &environment env)
  "Like (CMP (N-VARIADIC-SLOTS %OFFSET% SUBJECT) N-ARGS), but partial evaluate if
SUBJECT expands to (TERM ...)."
  (trivia:ematch (resolve-term-form subject env)
    ((type symbol)
     `(,cmp (n-variadic-slots %offset% ,subject) ,n-args))
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

(defmacro get-arg/static (subject i &environment env)
  "Like (GET-VARIADIC-SLOT I %OFFSET% SUBJECT), but partial evaluate if SUBJECT
expands to (TERM ...)."
  (trivia:ematch (resolve-term-form subject env)
    ((type symbol) `(get-variadic-slot ,i %offset% ,subject))
    ((list 'term (list* _ args))
     (cond ((< i (first-seq-var-pos args))
            `(term ,(nth i args)))
           (t `(nth ,i (%ensure-args%)))))))

(defmacro get-arg-from-end/static (subject from-end &environment env)
  "Like (VARIADIC-SLOT-FROM-END FROM-END SUBJECT), but partial evaluate if SUBJECT
expands to (TERM ...)."
  (trivia:ematch (resolve-term-form subject env)
    ((type symbol) `(variadic-slot-from-end ,from-end ,subject))
    ((list 'term (list* _ args))
     (let ((j (- (length args) (1+ from-end))))
       (cond ((> j (last-seq-var-pos args))
              `(term ,(nth j args)))
             (t `(nth (- (length (%ensure-args%)) ,(1+ from-end)) %args%)))))))

(defmacro get-args-between/static (subject i from-end &environment env)
  "Like (VARIADIC-SLOTS-BETWEEN I FROM-END %OFFSET% SUBJECT), but partial evaluate if
SUBJECT expands to (TERM ...)."
  (trivia:ematch (resolve-term-form subject env)
    ((type symbol) `(variadic-slots-between ,i ,from-end %offset% ,subject))
    ((list 'term (list* _ args))
     (let ((j (- (length args) (1+ from-end))))
       (cond ((and (<= i (first-seq-var-pos args))
                   (<= (last-seq-var-pos args) j))
              `(append ,@(mapcar (lambda (arg)
                                   (if (seq-var-p arg) arg `(list (term ,arg))))
                                 (subseq args i (1+ j)))))
             (t `(subseq (%ensure-args%) ,i (- (length %args%) ,from-end))))))))
