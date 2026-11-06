(in-package :ggs/stochastic)

(defun subst-row (new old pat-row)
  `(,@(butlast pat-row)
    (let/static ((,old ,new))
      (declare (ignorable ,old))
      ,(lastcar pat-row))))

(defun arity-check-form (offset subject n-args seq-var-pos)
  (trivia:ematch subject
    ((type symbol)
     (if seq-var-pos
         `(>= (n-variadic-slots ,offset ,subject) ,(1- n-args))
         `(= (n-variadic-slots ,offset ,subject) ,n-args)))
    ((list 'term (list* _ args))
     (bind (((:values seq-var-args normal-args) (partition #'seq-var-p args))
            (seq-var-length-form `(+ ,@(mapcar (lambda (a) `(length ,a)) seq-var-args))))
       (if seq-var-args
           (if seq-var-pos
               `(>= ,seq-var-length-form ,(- n-args 1 (length normal-args)))
               `(= ,seq-var-length-form ,(- n-args (length normal-args))))
           (if seq-var-pos
               (>= (length args) (1- n-args))
               (= (length args) n-args)))))))

(defvar-unbound *need-args*
  "Ask `groups-to-fsym-clauses' to generate an %arg variable binding that reify the
argument list.")

(defun arg-form (offset subject i n-args seq-var-pos)
  (trivia:ematch subject
    ((type symbol)
     (case (if seq-var-pos (signum (- i seq-var-pos)) -1)
       (-1 `(get-variadic-slot ,i ,offset ,subject))
       (0 `(variadic-slots-between ,i ,(- n-args i) ,offset ,subject))
       (1 `(variadic-slot-from-end ,(- n-args i) ,subject))))
    ((list 'term (list* _ args))
     (cond ((some #'seq-var-p args)
            ;; FIXME: not the fastest way to handle seq vars in args
            (setq *need-args* t)
            (case (if seq-var-pos (signum (- i seq-var-pos)) -1)
              (-1 `(nth ,i %args))
              (0 `(subseq  %args ,i (1+ (- (length %args) ,(- n-args i)))))
              (1 `(nth (- (length %args) ,(- n-args i)) %args))))
           (t (let ((i-from-end (+ (- (length args) n-args) i)))
                (case (if seq-var-pos (signum (- i seq-var-pos)) -1)
                  (-1 (normalize-term-form `(term ,(nth i args))))
                  (0 `(list ,@(loop for j from i to i-from-end
                                    collect `(term ,(nth j args)))))
                  (1 (normalize-term-form `(term ,(nth i-from-end args)))))))))))

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
  "GROUPS is a two-level hash table: FSYM -> (N-ARGS SEQ-VAR-POS) -> CLAUSES."
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
  (map-ordered-table
   (lambda (fsym arity-groups)
     (let (compound-clauses-1 constant-clauses-1)
       (map-ordered-table
        (lambda (arity-info pat-rows)
          (bind (((n-args seq-var-pos) arity-info)
                 (arg-vars (make-gensym-list n-args (prin1-to-string fsym))))

            (when (> n-args 0)
              (when-let (check (arity-check-form offset subject n-args seq-var-pos))
                (push `(when ,check
                         (let/static
                             ,(loop for var in arg-vars
                                    for i from 0
                                    collect
                                    `(,var ,(arg-form offset subject i n-args seq-var-pos)))
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

(defun expand-fsym-clause (fsym body)
  (if (var-p fsym)
      `((case/bind ,fsym ,@body))
      (mappend (lambda (c)
                 (cond ((eql (caar c) fsym) (cdr c))
                       ((var-p (caar c))
                        `((symbol-macrolet ((,(caar c) ',fsym))
                            ,@(cdr c))))))
               body)))

(defun expand-constant-clauses (subject constant-clauses)
  (unless constant-clauses
    (return-from expand-constant-clauses nil))
  (trivia:ematch subject
    ((type symbol) `((case/bind ,subject ,@constant-clauses)))
    ((list 'term (list* fsym args))
     (when (every #'seq-var-p args)
       `((unless (or ,@args)
           ,@(expand-fsym-clause fsym constant-clauses)))))))

(defun expand-compound-clauses (subject compound-clauses)
  (unless compound-clauses
    (return-from expand-compound-clauses nil))
  (trivia:ematch subject
    ((type symbol) `((case/bind (rose-node-fsym ,subject) ,@compound-clauses)))
    ((list 'term (list* fsym args))
     (when args
       (if (every #'seq-var-p args)
           `((when (or ,@args)
               ,@(expand-fsym-clause fsym compound-clauses)))
           (expand-fsym-clause fsym compound-clauses))))))

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

(defun decompose-consistency-check (pat offset cont-expr)
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
      (values (process pat)
              `(when (and ,@checks)
                 ,cont-expr)))))

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
                        (decompose-consistency-check pat offset `(progn ,@body)))))
                   clauses)))))
