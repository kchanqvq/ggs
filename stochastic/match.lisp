(in-package :ggs/stochastic)

(defun subst-row (new old pat-row)
  (append (butlast pat-row)
          (list `(let/static ((,old ,new))
                   (declare (ignorable ,old))
                   ,(lastcar pat-row)))))

(defun arity-check-form (offset subject n-args seq-var-pos)
  (cond ((symbolp subject)
         (if seq-var-pos
             `(>= (n-variadic-slots ,offset ,subject) ,(1- n-args))
             `(= (n-variadic-slots ,offset ,subject) ,n-args)))
        ((not (term-form-p subject))
         (error "Should not reach here"))
        ((some #'seq-var-p (cdadr subject))
         (error "TODO"))
        (seq-var-pos (>= (length (cdadr subject)) (1- n-args)))
        (t (= (length (cdadr subject)) n-args))))

(defun arg-form (offset subject i n-args seq-var-pos)
  (cond ((symbolp subject)
         (case (if seq-var-pos (signum (- i seq-var-pos)) -1)
           (-1 `(get-variadic-slot ,i ,offset ,subject))
           (0 `(variadic-slots-between ,i ,(- n-args i) ,offset ,subject))
           (1 `(variadic-slot-from-end ,(- n-args i) ,subject))))
        ((not (term-form-p subject))
         (error "Should not reach here"))
        ((some #'seq-var-p (cdadr subject))
         (error "TODO"))
        (seq-var-pos (error "TODO"))
        (t (normalize-term-form `(term ,(nth i (cdadr subject)))))))

(lp-hash-table:define-hash-table ordered-table sxhash equal :optimize ())

(defmacro do-match-internal (offset category subject-list &body pat-mat &environment env)
  "Assume patterns are linear, do simultaneous match against SUBJECT-LIST."
  (unless subject-list
    (return-from do-match-internal
      `(progn ,@(mapcar #'serapeum:only-elt pat-mat))))

  (unless (or (eq category t) (= (length subject-list) 1))
    (error "CATEGORY only make sense for single subject."))

  ;; pattern column selection heuristics
  (when pat-mat
    (setq pat-mat (copy-tree pat-mat)
          subject-list (copy-list subject-list))
    (let* ((columns (butlast (apply #'mapcar #'list pat-mat)))
           (column-n-tested (mapcar (lambda (c)
                                      (count-if-not #'var-p (mapcar #'ensure-car c)))
                                    columns))
           (selected (position (reduce #'max column-n-tested)
                               column-n-tested)))
      (rotatef (car subject-list) (nth selected subject-list))
      (mapc (lambda (row)
              (rotatef (car row) (nth selected row)))
            pat-mat)))

  ;; GROUPS is a two-level hash table: FSYM -> (N-ARGS SEQ-VAR-POS) -> CLAUSES.
  (bind ((groups (make-ordered-table))
         ((subject . rest) subject-list)
         (maybe-constant (member category '(constant t)))
         (maybe-compound (member category '(compound t)))
         bind-rows compound-clauses constant-clauses)

    (setq subject (term-form-from-env subject env))

    (macrolet ((push-to-group (row fsym arity-info)
                 `(let ((table (or (ordered-table-get ,fsym groups)
                                   (ordered-table-put ,fsym  (make-ordered-table) groups))))
                    (ordered-table-put ,arity-info
                                       (cons ,row (ordered-table-get ,arity-info table)) table))))
      (dolist (pat-row pat-mat)
        (let ((pat (car pat-row)))
          (cond ((consp pat)
                 (push-to-group pat-row (car pat)
                                (list (1- (length pat)) (seq-var-pos (cdr pat)))))
                ((var-p pat) (push pat-row bind-rows))
                (t (push-to-group (cons (list (car pat-row)) (cdr pat-row)) pat '(0 nil)))))))

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
                                      collect `(,var ,(arg-form offset subject
                                                                i n-args seq-var-pos)))
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

    `(progn
       ,@(when bind-rows
           `((do-match-internal ,offset t ,rest
               ,@(mapcar (lambda (pat-row)
                           (subst-row subject (car pat-row) (cdr pat-row)))
                         bind-rows))))
       ,@(when (or (and maybe-constant constant-clauses)
                   (and maybe-compound compound-clauses))
           (cond ((symbolp subject)
                  (cond ((and maybe-constant maybe-compound)
                         `((if (rose-node-p ,subject)
                               (case/bind (rose-node-fsym ,subject) ,@compound-clauses)
                               (case/bind ,subject ,@constant-clauses))))
                        (maybe-constant
                         `((case/bind ,subject ,@constant-clauses)))
                        (maybe-compound
                         `((case/bind (rose-node-fsym ,subject) ,@compound-clauses)))))
                 ((not (term-form-p subject))
                  (error "Should not reach here"))
                 ((var-p (caadr subject))
                  (cond ((and maybe-constant maybe-compound)
                         `((case/bind ,(caadr subject)
                             ,@(if (cdadr subject) compound-clauses constant-clauses))))
                        (maybe-constant
                         `((case/bind ,(caadr subject) ,@constant-clauses)))
                        (maybe-compound
                         `((case/bind ,(caadr subject) ,@compound-clauses)))))
                 (t (bind (((fsym . args) (cadr subject)))
                      (mappend (lambda (c)
                                 (cond ((eql (caar c) fsym) (cdr c))
                                       ((var-p (caar c))
                                        `((symbol-macrolet ((,(caar c) ',fsym))
                                            ,@(cdr c))))))
                               (if args
                                   (and maybe-compound compound-clauses)
                                   (and maybe-constant constant-clauses))))))))))

(defun expand-template (tmpl offset)
  "Build TMPL's rose nodes with args starting at OFFSET.  Only the structure is
filled in, see RECOMPUTE-ROSE."
  (let ((pad (make-list (- offset +rose-node-args-offset+) :initial-element '(list 0))))
    (labels ((process (tmpl)
               (cond
                 ((consp tmpl)
                  ;; The APPEND may look atrocious but it does not actually cons
                  ;; at all, because :ARGS to MAEK-ROSE-NODE optimizes any mix of
                  ;; APPEND and LIST (compiler macro generated by
                  ;; DEFINE-VARIADIC-STRUCTURE)
                  (let ((fsym (if (var-p (car tmpl)) (car tmpl) `',(car tmpl)))
                        (args `(append ,@pad
                                       ,@(mapcar (lambda (arg)
                                                   (if (seq-var-p arg) arg `(list ,(process arg))))
                                                 (cdr tmpl)))))
                    `(if ,(if (find-if-not #'seq-var-p (cdr tmpl)) t `(or ,@(cdr tmpl)))
                         (make-rose-node :fsym ,fsym :args ,args)
                         ,fsym)))
                 ((var-p tmpl) tmpl)
                 (t `',tmpl))))
      (process tmpl))))

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
