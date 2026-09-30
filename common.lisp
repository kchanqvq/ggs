(uiop:define-package :ggs/common
    (:use #:cl #:alexandria)
  (:import-from #:serapeum #:with-collector #:string-prefix-p #:eval-always #:-> #:partition)
  (:import-from #:metabang-bind #:bind)
  (:export #:define-variadic-structure
           #:do-variadic-slots #:n-variadic-slots #:get-variadic-slot
           #:var-p #:seq-var-p #:gensym-1 #:get-rules #:defrw #:defrw* #:yield-rewrite))

(in-package :ggs/common)

(defmacro do-variadic-slots ((slot-var offset variadic-structure &optional result) &body body)
  (destructuring-bind (slot-var &optional index-var) (ensure-list slot-var)
    (once-only (variadic-structure)
      (with-gensyms (i)
        `(loop for ,i from ,offset below (length ,variadic-structure)
               ,@(when index-var `(for ,index-var of-type fixnum from 0))
               do (let ((,slot-var (svref ,variadic-structure ,i)))
                    ,@body)
               finally (return ,result))))))

(declaim (inline n-variadic-slots))
(defun n-variadic-slots (offset variadic-structure)
  (- (length variadic-structure) offset))

(defmacro get-variadic-slot (i offset variadic-structure)
  `(svref ,variadic-structure (+ ,i ,offset)))

(defun expand-make (args fixed offset)
  (labels ((items (form)
             (typecase form
               (null '())
               ((cons (eql list)) (mapcar (lambda (f) `(list ,f)) (cdr form)))
               ((cons (eql list*)) (append (items `(list ,@(butlast (cdr form))))
                                           (items (lastcar (cdr form)))))
               ((cons (eql append)) (mapcan #'items (cdr form)))
               (t (list form))))
           (single-item-p (item)
             (and (consp item) (eq (car item) 'list))))
    (let* ((items (items args))
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
          `(vector ,@fixed ,@(mapcar #'second items))))))

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

(defun gensym-1 (thing)
  (make-gensym (princ-to-string thing)))

(defun get-rules (name)
  (let ((rules (get name 'rules '%unbound)))
    (when (eql rules '%unbound)
      (error "Undefined rule set ~A" name))
    rules))

(defmacro defrw (name &rest rule)
  "Define ruleset NAME consisting of a single RULE.

Equivalent to (DEFRW* NAME RULE), See DEFRW* for rule format."
  `(defrw* ,name ,rule))

(defmacro defrw* (name &body rules)
  "Define ruleset NAME consisting of RULES.

Each RULE can be either:

- A symbol that names another ruleset. It will be included in NAME.

- A list of form (LHS RHS [:guard CONDITION]). This defines a rule that match
  LHS pattern and rewrite to RHS, if CONDITION evaluates to true.

- A list of form (LHS :eval BODY...). This defines a rule that match LHS pattern
  and evaluate BODY for each match. BODY may use YIELD-REWRITE to yield
  candidate rewrites, potentially multiple times.

The rule (lhs rhs :guard condition) is equivalent to the :EVAL rule
\(lhs :eval (when condition (yield-rewrite rhs)))."
  (labels ((canonicalize (rule)
             (cond ((symbolp rule) rule)
                   ((eql (cadr rule) :eval)
                    (cons (car rule) (cddr rule)))
                   (t
                    (destructuring-bind (rhs &key (guard t)) (rest rule)
                      `(,(car rule)
                        (when ,guard (yield-rewrite ,rhs))))))))
    `(eval-always (setf (get ',name 'rules) ',(mapcar #'canonicalize rules)))))

(defmacro yield-rewrite (rhs)
  "Inside :EVAL rules, yield a candidate rewrite with RHS as template."
  (error "YIELD-REWRITE must be used in :EVAL rules in DEFRW/DEFRW*."))
