(in-package :ggs/stochastic)

(defvar-unbound *need-args*
  "Ask `do-match-internal' to generate an %arg variable binding that reify the
argument list.")

(defmacro do-match-internal (offset category subject-list &body pat-mat &environment env)
  "Assume patterns are linear, do simultaneous match against SUBJECT-LIST.

CATEGORY can be one of T, CONSTANT, COMPOUND."

  (cond ((null pat-mat)
         (return-from do-match-internal nil))
        ((null subject-list)
         (return-from do-match-internal
           `(progn ,@(mapcar #'serapeum:only-elt pat-mat))))
        ((not (or (eq category t) (= (length subject-list) 1)))
         (error "CATEGORY only make sense for single subject.")))

  (bind (((:values subject-list pat-mat) (select-pat-column subject-list pat-mat))
         ((subject . rest) subject-list)
         (subject (term-form-from-env subject env))
         *need-args*
         ((:values groups bind-rows) (group-by-fsym-and-arity pat-mat))
         ((:values compound-clauses constant-clauses)
          (groups-to-fsym-clauses offset subject rest groups)))

    `(let ,(when *need-args*
             `((%args (append ,@(mapcar (lambda (a)
                                          (if (seq-var-p a) a `(list (term ,a))))
                                        (cdadr subject))))))
       ,@(when bind-rows
           `((do-match-internal ,offset t ,rest
               ,@(mapcar (lambda (pat-row)
                           (subst-row subject (car pat-row) (cdr pat-row)))
                         bind-rows))))
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

(defun subst-row (new old pat-row)
  `(,@(butlast pat-row)
    (let/static ((,old ,new))
      (declare (ignorable ,old))
      ,(lastcar pat-row))))

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
  "A form that computes argument I of SUBJECT."
  (trivia:ematch subject
    ((type symbol) `(get-variadic-slot ,i ,offset ,subject))
    ((list 'term (list* _ args))
     (cond ((< i (first-seq-var-pos args))
            (normalize-term-form `(term ,(nth i args))))
           (t (setq *need-args* t)
              `(nth ,i %args))))))

(defun arg-from-end-form (subject from-end)
  "A form that computes argument FROM-END of SUBJECT counting from the end."
  (trivia:ematch subject
    ((type symbol) `(variadic-slot-from-end ,from-end ,subject))
    ((list 'term (list* _ args))
     (let ((j (- (length args) (1+ from-end))))
       (cond ((> j (last-seq-var-pos args))
              (normalize-term-form `(term ,(nth j args))))
             (t (setq *need-args* t)
                `(nth (- (length %args) ,(1+ from-end)) %args)))))))

(defun args-between-form (offset subject i from-end)
  "A form that computes the list of arguments of SUBJECT from I to FROM-END."
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

(lp-hash-table:define-hash-table ordered-table sxhash equal :optimize ())

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
    (mapc (lambda (row)
            (rotatef (car row) (nth selected row)))
          pat-mat)
    (values subject-list pat-mat)))

(defun group-by-fsym-and-arity (pat-mat)
  "Classify PAT-MAT into GROUPS of destructuring rows and BIND-ROWS.

GROUPS is a two-level hash table: FSYM -> (N-ARGS SEQ-VAR-POS) -> PAT-ROWS."
  (let ((groups (make-ordered-table))
        bind-rows)
    (macrolet ((push-to-group (row fsym arity-info)
                 `(let ((table (or (ordered-table-get ,fsym groups)
                                   (ordered-table-put ,fsym  (make-ordered-table) groups))))
                    (ordered-table-put ,arity-info
                                       (cons ,row (ordered-table-get ,arity-info table))
                                       table))))
      (dolist (pat-row pat-mat)
        (let ((pat (car pat-row)))
          (cond ((consp pat)
                 (push-to-group pat-row (car pat)
                                (list (1- (length pat)) (seq-var-pos (cdr pat)))))
                ((var-p pat) (push pat-row bind-rows))
                (t (push-to-group (cons (list (car pat-row)) (cdr pat-row)) pat '(0 nil)))))))
    (values groups bind-rows)))

(defun groups-to-fsym-clauses (offset subject rest groups
                               &aux compound-clauses constant-clauses)
  "Convert GROUPS as returned by `group-by-fsym-and-arity' into clauses of the
form ((FSYM-OR-VAR) BODY...) (as expected by `case/bind'). Remaining patterns in
grouped rows are matched recursively via `do-match-internal' in BODY."
  (map-ordered-table
   (lambda (fsym arity-groups)
     (let (compound-clauses-1 constant-clauses-1)
       (map-ordered-table
        (lambda (arity-info pat-rows)
          (bind (((n-args seq-var-pos) arity-info)
                 (arg-vars (make-gensym-list n-args (prin1-to-string fsym))))

            (when (> n-args 0)
              (when-let (check (if seq-var-pos
                                   (arity-check-form offset subject (1- n-args) t)
                                   (arity-check-form offset subject n-args nil)))
                (push `(when ,check
                         (let/static
                             ,(loop for var in arg-vars
                                    for i from 0
                                    collect
                                    `(,var
                                      ,(case (if seq-var-pos (signum (- i seq-var-pos)) -1)
                                         (-1 (arg-form offset subject i))
                                         (0 (args-between-form offset subject i (- n-args i 1)))
                                         (1 (arg-from-end-form subject (- n-args i 1))))))
                           (do-match-internal ,offset t ,(append arg-vars rest)
                             ,@(mapcar (lambda (pat-row)
                                         (append (cdar pat-row) (cdr pat-row)))
                                       pat-rows))))
                      compound-clauses-1)))

            (when (= n-args 0)
              (push `(do-match-internal ,offset t ,rest ,@(mapcar #'cdr pat-rows))
                    constant-clauses-1))

            ;; Single SEQ-VAR matches constant and binds to NIL
            (when (and (= n-args 1) (eql seq-var-pos 0))
              (push `(do-match-internal ,offset t ,(cons nil rest)
                       ,@(mapcar (lambda (pat-row)
                                   (append (cdar pat-row) (cdr pat-row)))
                                 pat-rows))
                    constant-clauses-1))))
        arity-groups)

       (when compound-clauses-1
         (push `((,fsym) ,@(nreverse compound-clauses-1)) compound-clauses))
       (when constant-clauses-1
         (push `((,fsym) ,@(nreverse constant-clauses-1)) constant-clauses))))
   groups)

  (values compound-clauses constant-clauses))

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
partial evaluate if SUBJECT is static."
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

(defun node-equal (x y offset)
  (labels ((process (x y)
             (cond
               ((eq x y) t)
               ((and (not (rose-node-p x)) (not (rose-node-p y))) (eql x y))
               ((and (rose-node-p x) (rose-node-p y))
                (unless (= (length x) (length y))
                  (return-from process nil))
                (unless (eql (rose-node-fsym x) (rose-node-fsym y))
                  (return-from process nil))
                (loop for i from offset below (length x)
                      always (process (svref x i) (svref y i)))))))
    (process x y)))

(declaim (inline seq-equal))
(defun seq-equal (xs ys offset)
  (declare (type list xs ys))
  (and (= (length xs) (length ys))
       (every (lambda (x y) (node-equal x y offset)) xs ys)))

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

(defmacro do-match* (offset category subject &body clauses &environment env)
  (setq subject (term-form-from-env subject env))

  (multiple-value-bind (bindings subject-1)
      (if (term-form-p subject)
          (let ((renames (mapcar (lambda (var) (cons var (gensym-1 var)))
                                 (remove-duplicates (remove-if-not #'var-p (flatten subject))))))
            (values (mapcar (lambda (r) (list (cdr r) (car r))) renames)
                    (sublis renames subject)))
          (let ((var (gensym "SUBJECT")))
            (values `((,var ,subject)) var)))

    `(let ,bindings
       (declare (ignorable ,@(mapcar #'car bindings)))
       (do-match-internal ,offset ,category (,subject-1)
         ,@(mapcar (lambda (clause)
                     (bind (((pat . body) clause))
                       (multiple-value-list
                        (decompose-consistency-check pat offset body))))
                   clauses)))))
