(uiop:define-package :ggs/common
    (:use #:cl #:alexandria)
  (:import-from #:serapeum #:with-collector #:string-prefix-p #:eval-always #:-> #:partition)
  (:export #:define-variadic-structure
           #:var-p #:gensym-1 #:ensure-cache
           #:get-rules #:defrw #:defrw*))

(in-package :ggs/common)

(defmacro define-variadic-structure (name &rest slot-and-options)
  (let* ((doc (and (stringp (car slot-and-options)) (pop slot-and-options)))
         (slot-and-options (mapcar #'ensure-list slot-and-options))
         (ordinary-slots (butlast slot-and-options))
         (last-slot (lastcar slot-and-options))
         (singular (if (listp (car last-slot)) (caar last-slot) (car last-slot)))
         (plural (if (listp (car last-slot)) (cadar last-slot) (format nil "~aS" (car last-slot))))
         (offset-const (format-symbol t "+~a-~a-OFFSET+" name plural))
         (do-args (format-symbol t "DO-~a-~a" name plural))
         (predicate (format-symbol t "~a-P" name))
         (arg-var (format-symbol t "~a-VAR" singular))
         (name-var (format-symbol t "~a-VAR" name))
         (map-args (format-symbol t "MAP-~a-~a" name plural))
         (n-args (format-symbol t "~a-N-~a" name plural))
         (get-arg (format-symbol t "~a-~a" name singular)))
    `(progn
       (declaim (inline ,predicate ,map-args ,n-args ,get-arg))
       (defstruct (,name (:type vector) (:constructor nil))
         ,@(and doc (list doc))
         ,@ordinary-slots)
       (defconstant ,offset-const ,(length ordinary-slots))
       (deftype ,name (&optional n)
         (cond ((eq n '*) 'simple-vector)
               (t `(simple-vector ,(+ n ,offset-const)))))
       (defun ,predicate (obj)
         (and (typep obj 'simple-vector) (>= (length obj) ,offset-const)))
       (defmacro ,do-args ((,arg-var ,name-var &optional result) &body body)
         (destructuring-bind (,arg-var &optional index-var) (ensure-list ,arg-var)
           (once-only (,name-var)
             (with-gensyms (i)
               `(loop for ,i from ,,offset-const below (length ,,name-var)
                      ,@(when index-var `(for ,index-var of-type fixnum from 0))
                      do (let ((,,arg-var (svref ,,name-var ,i)))
                           ,@body)
                      finally (return ,result))))))
       (defun ,map-args (function ,name)
         (with-collector (collect)
           (,do-args (arg ,name)
                     (collect (funcall function arg)))))
       (defun ,n-args (,name)
         (- (length ,name) ,offset-const))
       (defmacro ,get-arg (i ,name)
         `(svref ,,name (+ ,i ,',offset-const))))))

(defun var-p (object)
  (typecase object
    (symbol (string-prefix-p "?" (symbol-name object)))))

(defun gensym-1 (thing)
  (make-gensym (princ-to-string thing)))

(defmacro ensure-cache (place key newval)
  "Helper for cache maintenance. If PLACE contains a list (OLDKEY OLDVAL) and
OLDKEY is equal to KEY, return OLDVAL.  Otherwise evaluate NEWVAL, store (KEY
NEWVAL) into PLACE and return NEWVAL."
  `(if (equal (first ,place) ,key)
       (second ,place)
       (second (setf ,place (list ,key ,newval)))))

(defun get-rules (name)
  (let ((rules (get name 'rules '%unbound)))
    (when (eql rules '%unbound)
      (error "Undefined rule set ~A" name))
    rules))

(defmacro defrw (name &rest rule)
  `(defrw* ,name ,rule))

(defmacro defrw* (name &body rules)
  `(eval-always (setf (get ',name 'rules) ',rules)))
