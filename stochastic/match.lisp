(in-package :ggs/stochastic)

(defun subst-row (new old pat-row)
  (append (butlast pat-row)
          (list `(let ((,old ,new))
                   (declare (ignorable ,old))
                   ,(lastcar pat-row)))))

(defmacro case/bind (keyform &body cases)
  "Like CASE, but also support ((?VAR) ...) clauses, which run before
everything else and bind ?VAR."
  (multiple-value-bind (bind-clauses real-cases)
      (partition (lambda (case) (and (consp (car case)) (var-p (caar case))))
                 cases)
    (let ((bind-forms (mapcar (lambda (clause)
                                `(let ((,(caar clause) ,keyform))
                                   ,@(cdr clause)))
                              bind-clauses)))
      (cond ((and bind-forms real-cases)
             `(progn ,@bind-forms (case ,keyform ,@real-cases)))
            (bind-forms `(progn ,@bind-forms))
            (real-cases `(case ,keyform ,@real-cases))))))

(declaim (inline rose-node-arg-between rose-node-arg-from-end))
(defun rose-node-arg-between (from-start from-end node)
  (loop for i from (+ +rose-node-args-offset+ from-start)
          to (- (length node) from-end)
        collect (svref node i)))
(defun rose-node-arg-from-end (from-end node)
  (svref node (- (length node) from-end)))

(lp-hash-table:define-hash-table ordered-table sxhash equal :optimize ())

(defun expand-match (var-list pat-mat)
  (unless var-list
    (return-from expand-match
      (mapcar #'serapeum:only-elt pat-mat)))
  ;; pattern column selection heuristics
  (when pat-mat
    (setq pat-mat (copy-tree pat-mat)
          var-list (copy-list var-list))
    (let* ((columns (butlast (apply #'mapcar #'list pat-mat)))
           (column-n-tested (mapcar (lambda (c)
                                      (count-if-not #'var-p (mapcar #'ensure-car c)))
                                    columns))
           (selected (position (reduce #'max column-n-tested)
                               column-n-tested)))
      (rotatef (car var-list) (nth selected var-list))
      (mapc (lambda (row)
              (rotatef (car row) (nth selected row)))
            pat-mat)))
  ;; GROUPS is a two-level hash table: FSYM -> (N-ARGS SEQ-VAR-POS) -> CLAUSES.
  (let ((groups (make-ordered-table))
        (var (car var-list))
        bind-rows
        compound-clauses
        constant-clauses)
    (macrolet ((push-to-group (row fsym arity-info)
                 `(let ((table (or (ordered-table-get ,fsym groups)
                                   (ordered-table-put ,fsym  (make-ordered-table) groups))))
                    (ordered-table-put ,arity-info (cons ,row (ordered-table-get ,arity-info table)) table))))
      (dolist (pat-row pat-mat)
        (let ((pat (car pat-row)))
          (cond ((consp pat)
                 (let ((seq-var-pos (position-if #'seq-var-p (cdr pat))))
                   (when (and seq-var-pos
                              (find-if #'seq-var-p (cdr pat) :start (1+ seq-var-pos)))
                     (error "Multiple sequence variables in ~A." pat))
                   (push-to-group pat-row (car pat) (list (1- (length pat)) seq-var-pos))))
                ((var-p pat)
                 (push pat-row bind-rows))
                (t
                 (push-to-group (cons (list (car pat-row)) (cdr pat-row)) pat '(0 nil)))))))
    (map-ordered-table
     (lambda (fsym arity-groups)
       (let (compound-clauses-1
             constant-clauses-1)
         (map-ordered-table
          (lambda (arity-info pat-rows)
            (let* ((n-args (car arity-info))
                   (arg-vars (make-gensym-list (car arity-info) (prin1-to-string fsym)))
                   (seq-var-pos (cadr arity-info)))
              (when (> n-args 0)
                (push `(when ,(if seq-var-pos
                                  `(>= (rose-node-n-args ,var) ,(1- n-args))
                                  `(= (rose-node-n-args ,var) ,n-args))
                         (let ,(mapcar
                                (lambda (i arg-var)
                                  (case (if seq-var-pos (signum (- i seq-var-pos)) -1)
                                    (-1 `(,arg-var (rose-node-arg ,i ,var)))
                                    (0 `(,arg-var (rose-node-arg-between ,i ,(- n-args i) ,var)))
                                    (1 `(,arg-var (rose-node-arg-from-end ,(- n-args i) ,var)))))
                                (iota n-args) arg-vars)
                           ,@(expand-match
                              (append arg-vars (cdr var-list))
                              (mapcar (lambda (pat-row)
                                        (append (cdar pat-row) (cdr pat-row)))
                                      pat-rows))))
                      compound-clauses-1))
              (when (= n-args 0)
                (nconcf constant-clauses-1
                        (expand-match
                         (cdr var-list)
                         (mapcar #'cdr pat-rows))))
              ;; Single SEQ-VAR matches constant and binds to NIL
              (when (and (= n-args 1) (eql seq-var-pos 0))
                (nconcf constant-clauses-1
                        (expand-match
                         (cons nil (cdr var-list))
                         (mapcar (lambda (pat-row)
                                   (append (cdar pat-row) (cdr pat-row)))
                                 pat-rows))))))
          arity-groups)
         (when compound-clauses-1
           (push `((,fsym) ,@compound-clauses-1) compound-clauses))
         (when constant-clauses-1
           (push `((,fsym) ,@constant-clauses-1) constant-clauses))))
     groups)
    (append
     (expand-match
      (cdr var-list)
      (mapcar (lambda (pat-row)
                (subst-row var (car pat-row) (cdr pat-row)))
              bind-rows))
     (when (or constant-clauses compound-clauses)
       `((if (rose-node-p ,var)
             (case/bind (rose-node-fsym ,var) ,@compound-clauses)
             (case/bind ,var ,@constant-clauses)))))))

(defun expand-template (tmpl cost-fn)
  (labels ((process (tmpl)
             (cond
               ((consp tmpl)
                (let* ((fsym (if (var-p (car tmpl)) (car tmpl) `',(car tmpl)))
                       (first-seq-var-pos (position-if #'seq-var-p (cdr tmpl)))
                       (head-args (subseq (cdr tmpl) 0 first-seq-var-pos))
                       (tail-args (and first-seq-var-pos (subseq (cdr tmpl) first-seq-var-pos))))
                  `(if ,(if (find-if-not #'seq-var-p (cdr tmpl)) t `(or ,@(cdr tmpl)))
                       (let ((new-node
                               (apply #'vector 0.0 -1 1 ,fsym
                                      ,@(mapcar #'process head-args)
                                      (append ,@(mapcar
                                                 (lambda (arg)
                                                   (if (seq-var-p arg)
                                                       arg
                                                       `(list ,(process arg))))
                                                 tail-args)))))
                         (setf (rose-node-cost new-node) (,cost-fn new-node))
                         new-node)
                       ,fsym)))
               ((var-p tmpl) tmpl)
               (t `',tmpl))))
    (process tmpl)))

(defun node-equal (x y)
  (labels ((process (x y)
             (cond
               ((and (not (rose-node-p x)) (not (rose-node-p y))) (eql x y))
               ((and (rose-node-p x) (rose-node-p y))
                (unless (= (length x) (length y))
                  (return-from node-equal nil))
                (loop for i from (1- +rose-node-args-offset+) below (length x)
                      always (node-equal (svref x i) (svref y i)))))))
    (process x y)))

(defun decompose-consistency-check (pat cont-expr)
  (let (vars checks)
    (labels ((process (pat)
               (cond ((consp pat)
                      (cons (car pat)
                            (mapcar #'process (cdr pat))))
                     ((var-p pat)
                      (if (member pat vars)
                          (let ((new-var (gensym-1 pat)))
                            (push `(node-equal ,pat ,new-var) checks)
                            new-var)
                          (progn
                            (push pat vars)
                            pat)))
                     (t pat))))
      (values (process pat)
              `(when (and ,@checks)
                 ,cont-expr)))))

(defmacro do-matches* (top-node-var &body clauses)
  `(progn ,@(expand-match
             (list top-node-var)
             (mapcar (lambda (clause)
                       (bind (((pat . body) clause))
                             (multiple-value-list
                              (decompose-consistency-check pat `(progn ,@body)))))
                     clauses))))
