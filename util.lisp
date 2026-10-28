(uiop:define-package :ggs/util
    (:use #:cl #:alexandria #:ggs/common)
  (:import-from #:serapeum #:with-collector #:string-prefix-p #:eval-always #:->
                #:partition #:lret)
  (:import-from #:metabang-bind #:bind)
  (:import-from #:ggs/common #:get-analysis-data)
  (:export #:define-variadic-structure #:do-variadic-slots #:n-variadic-slots
           #:get-variadic-slot #:variadic-slots-between #:variadic-slot-from-end
           #:list-form-items #:single-item-p
           #:var-p #:seq-var-p #:seq-var-pos #:gensym-1 #:case/bind
           #:get-rules #:get-analysis #:get-user-decls #:get-analysis-data
           #:warn-compile-rule-set #:alist-like-get))

(in-package :ggs/util)

(defmacro do-variadic-slots ((slot-var offset variadic-structure &optional result) &body body)
  (destructuring-bind (slot-var &optional index-var) (ensure-list slot-var)
    (once-only (variadic-structure)
      (with-gensyms (i)
        `(loop for ,i of-type fixnum from ,offset below (length (the simple-vector ,variadic-structure))
               ,@(when index-var `(for ,index-var of-type fixnum from 0))
               do (let ((,slot-var (svref ,variadic-structure ,i)))
                    ,@body)
               finally (return ,result))))))

(declaim (inline n-variadic-slots))
(defun n-variadic-slots (offset variadic-structure)
  (- (length (the simple-vector variadic-structure)) offset))

(defmacro get-variadic-slot (i offset variadic-structure)
  `(svref ,variadic-structure (+ ,i ,offset)))

(declaim (inline variadic-slots-between variadic-slot-from-end))
(defun variadic-slots-between (from-start from-end offset node)
  (loop for i from (+ offset from-start)
          to (- (length node) from-end)
        collect (svref node i)))
(defun variadic-slot-from-end (from-end node)
  (svref node (- (length node) from-end)))

(defun list-form-items (form)
  "Normalize mix of `append', `list' and `list*' into a list of (LIST SINGLE-ITEM)
or MULTIPLE-ITEM."
  (typecase form
    (null '())
    ((cons (eql list)) (mapcar (lambda (f) `(list ,f)) (cdr form)))
    ((cons (eql list*)) (append (list-form-items `(list ,@(butlast (cdr form))))
                                (list-form-items (lastcar (cdr form)))))
    ((cons (eql append)) (mappend #'list-form-items (cdr form)))
    (t (list form))))

(defun single-item-p (item)
  (and (consp item) (eq (car item) 'list)))

(defun expand-make (args fixed offset)
  (let* ((items (list-form-items args))
         (vars (make-gensym-list (length items))))
    (if (notevery #'single-item-p items)
        `(let* (,@(mapcar (lambda (item var)
                            `(,var ,(if (single-item-p item) (second item) item)))
                          items vars)
                (new (make-array
                      (+ ,(+ offset (count-if #'single-item-p items))
                         ,@(mappend (lambda (item var)
                                      (unless (single-item-p item) `((length ,var))))
                                    items vars))))
                (i ,offset))
           (declare (fixnum i))
           (setf ,@(loop for f in fixed
                         for k from 0
                         append `((svref new ,k) ,f)))
           ,@(mappend (lambda (item var)
                        (if (single-item-p item)
                            `((setf (svref new i) ,var)
                              (incf i))
                            `((dolist (x ,var)
                                (setf (svref new i) x)
                                (incf i)))))
                      items vars)
           new)
        `(vector ,@fixed ,@(mapcar #'second items)))))

(defmacro define-variadic-structure (name-and-options &body slot-and-options)
  "Supports :INCLUDE, child structures inherits all slots *except* the variadic
slot. To access variadic slot generically, caller need to know the exact structure
type at runtime, and pass in the corresponding offset using GET-VARIADIC-SLOT and
alike"
  (bind (((name . options) (ensure-list name-and-options))
         (doc (and (stringp (car slot-and-options)) (pop slot-and-options)))
         (slot-and-options (mapcar #'ensure-list slot-and-options))
         (include (cadr (assoc :include options)))
         (own-slots (mapcar #'ensure-list (butlast slot-and-options)))
         (ordinary-slots (append (when include
                                   (or (get include 'variadic-structure-slots)
                                       (error "~S is not a variadic structure." include)))
                                 own-slots))
         (last-slot (lastcar slot-and-options))
         (singular (if (listp (car last-slot)) (caar last-slot) (car last-slot)))
         (plural (if (listp (car last-slot)) (cadar last-slot) (format nil "~aS" (car last-slot))))
         (offset-const (format-symbol t "+~a-~a-OFFSET+" name plural))
         (do-args (format-symbol t "DO-~a-~a" name plural))
         (predicate (format-symbol t "~a-P" name))
         (constructor-option (assoc :constructor options))
         (make (if constructor-option (cadr constructor-option) (format-symbol t "MAKE-~a" name)))
         (arg-var (format-symbol t "~a-VAR" singular))
         (name-var (format-symbol t "~a-VAR" name))
         (map-args (format-symbol t "MAP-~a-~a" name plural))
         (n-args (format-symbol t "~a-N-~a" name plural))
         (get-arg (format-symbol t "~a-~a" name singular)))
    (assert make)
    `(progn
       (declaim (inline ,predicate ,make ,map-args ,n-args ,get-arg))
       (defstruct (,name (:type vector) (:constructor nil)
                         ,@(when include `((:include ,include))))
         ,@(and doc (list doc))
         ,@own-slots)
       (eval-always
         (setf (get ',name 'variadic-structure-slots) ',ordinary-slots))
       (defconstant ,offset-const ,(length ordinary-slots))
       (deftype ,name (&optional n)
         (cond ((eq n '*) 'simple-vector)
               (t `(simple-vector ,(+ n ,offset-const)))))
       (defun ,predicate (obj)
         (and (typep obj 'simple-vector) (>= (length obj) ,offset-const)))
       (defun ,make (&key ,@(mapcar (lambda (slot) `(,(car slot) ,(cadr slot)))
                                    ordinary-slots)
                       (n-args nil n-args-p) (args nil args-p))
         (declare (list args))
         (when (and n-args-p args-p)
           (error "Can't specify both :N-ARGS and :ARGS."))
         (let ((new (make-array (+ ,offset-const (if args-p (length args) (or n-args 0))))))
           (setf ,@(loop for slot in ordinary-slots
                         for i from 0
                         appending `((svref new ,i) ,(car slot))))
           (loop for a in args for i of-type fixnum from ,offset-const
                 do (setf (svref new i) a))
           new))
       (define-compiler-macro ,make
           (&whole form &key ,@(mapcar (lambda (slot) `(,(car slot) ',(cadr slot))) ordinary-slots)
                          (n-args nil n-args-p) (args nil args-p))
         (declare (ignore n-args))
         (when (and n-args-p args-p)
           (error "Can't specify both :N-ARGS and :ARGS."))
         (if args-p
             (expand-make args (list ,@(mapcar #'car ordinary-slots)) ,offset-const)
             form))
       (defmacro ,do-args ((,arg-var ,name-var &optional result) &body body)
         `(do-variadic-slots (,,arg-var ,',offset-const ,,name-var ,result) ,@body))
       (defun ,map-args (function ,name)
         (with-collector (collect)
           (,do-args (arg ,name)
             (collect (funcall function arg)))))
       (defun ,n-args (,name) (n-variadic-slots ,offset-const ,name))
       (defmacro ,get-arg (i ,name)
         `(get-variadic-slot ,i ,',offset-const ,,name)))))

(defun var-p (object)
  (and (symbolp object) (string-prefix-p "?" (symbol-name object))))

(defun seq-var-p (object)
  (and (symbolp object) (string-prefix-p "??" (symbol-name object))))

(defun seq-var-pos (args)
  (lret ((seq-var-pos (position-if #'seq-var-p args)))
    (when (and seq-var-pos (find-if #'seq-var-p args :start (1+ seq-var-pos)))
      (error "Multiple sequence variables in ~A." args))))

(defun gensym-1 (thing)
  (make-gensym (princ-to-string thing)))

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

(defun get-rules (name)
  (lret ((rules (get name 'ggs/common::rules '%unbound)))
    (when (eql rules '%unbound)
      (error "Undefined rule set ~A" name))))

(defun get-analysis (name)
  (lret ((analysis (get name 'ggs/common::analysis '%unbound)))
    (when (eql analysis '%unbound)
      (error "Undefined analysis ~A" name))))

(defun get-user-decls (env &optional (policies '(speed safety)))
  `((optimize ,@(remove-if-not (lambda (policy) (member (car policy) policies))
                               (cl-environments:declaration-information 'optimize env)))))

(defun warn-compile-rule-set (precompile-form)
  (when *warn-runtime-compile*
    (warn "~@<Compiling a rule set at runtime, you can precompile it with ~S~:@>"
          precompile-form)))

(defun alist-like-get (key alist-like &optional default)
  (typecase alist-like
    (cons (if-let (entry (assoc key alist-like))
            (cdr entry)
            (if-let (entry (assoc t alist-like))
              (cdr entry) default)))
    (t alist-like)))
