(in-package :ggs/stochastic)

(define-variadic-structure rose-node
  "N-REWRITES = -1 means the rose tree data hasn't been computed for
 this node."
  (weight 0.0 :type single-float)
  (n-rewrites -1 :type fixnum)
  (cost 0 :type non-negative-fixnum)
  (fsym)
  (arg))

(defun term-node (term cost-fn)
  (labels ((process (term)
             (cond ((atom term) term)
                   ((null (cdr term)) (car term))
                   (t (let ((new-node (make-rose-node :fsym (car term)
                                                      :args (mapcar #'process (cdr term)))))
                        (setf (rose-node-cost new-node)
                              (funcall cost-fn new-node +rose-node-args-offset+))
                        new-node)))))
    (process term)))

(defun node-term (term)
  (if (rose-node-p term)
      (cons (rose-node-fsym term)
            (map-rose-node-args #'node-term term))
      term))

(declaim (inline node-replace-arg))
(defun node-replace-arg (node i new-arg cost-fn offset)
  (declare (optimize (speed 3) (safety 0))
           (rose-node node)
           ((function (t fixnum) fixnum) cost-fn)
           (fixnum i offset))
  (let* ((n (length node))
         (new-node (make-array n))
         (i-1 (+ i offset)))
    (setf (rose-node-weight new-node) 0.0
          (rose-node-n-rewrites new-node) -1
          (rose-node-fsym new-node) (rose-node-fsym node)
          (rose-node-cost new-node) 0)
    (loop for j of-type fixnum from offset below n
          for old-arg = (svref node j)
          do (setf (svref new-node j) (if (= i-1 j) new-arg old-arg)))
    (setf (rose-node-cost new-node) (funcall cost-fn new-node offset))
    new-node))

(defmacro def-search-rewrite (name accessor type)
  `(progn
     (declaim (ftype (function ( rose-node fixnum ,type (function (t fixnum) fixnum)
                                 (function (t ,type) t))
                               t)
                     ,name))
     (defun ,name (node offset value cost-fn rewrite-fn)
       (labels ((process (node value)
                  (declare (optimize speed)
                           (rose-node node)
                           (,type value))
                  (do-variadic-slots ((arg i) offset node)
                    (when (rose-node-p arg)
                      (let ((a-value (,accessor arg)))
                        (if (<= a-value value)
                            (decf value a-value)
                            (return-from process
                              (node-replace-arg node i (process arg value) cost-fn offset))))))
                  (return-from process (funcall rewrite-fn node value))))
         (process node value)))))

(declaim (inline search-rewrite-n-rewrites search-rewrite-weight))
(def-search-rewrite search-rewrite-n-rewrites rose-node-n-rewrites fixnum)
(def-search-rewrite search-rewrite-weight rose-node-weight single-float)
