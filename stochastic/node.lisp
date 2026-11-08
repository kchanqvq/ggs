(in-package :ggs/stochastic)

(define-variadic-structure rose-node
  "N-REWRITES = -1 means the rose tree data hasn't been computed for
 this node."
  (weight 0.0 :type single-float)
  (n-rewrites -1 :type fixnum)
  (fsym)
  (arg))

(deftype finalize-node-fn ()
  `(function (rose-node fixnum) rose-node))

(defun term-node (term offset finalize-node beta-constant)
  (labels ((process (term)
             (cond ((atom term) term)
                   ((null (cdr term)) (car term))
                   (t (funcall finalize-node
                               (make-rose-node :offset offset
                                               :fsym (car term)
                                               :args (mapcar #'process (cdr term)))
                               beta-constant)))))
    (process term)))

(defun node-term (term offset)
  (if (rose-node-p term)
      (cons (rose-node-fsym term)
            (map-variadic-slots (lambda (a) (node-term a offset)) offset term))
      term))

(declaim (inline node-replace-arg))
(defun node-replace-arg (node i new-arg offset)
  (declare (optimize (speed 3) (safety 0))
           (rose-node node)
           (fixnum i offset))
  (let* ((n (length node))
         (new-node (make-array n))
         (i-1 (+ i offset)))
    (setf (rose-node-weight new-node) 0.0
          (rose-node-n-rewrites new-node) -1
          (rose-node-fsym new-node) (rose-node-fsym node))
    (loop for j of-type fixnum from offset below n
          for old-arg = (svref node j)
          do (setf (svref new-node j) (if (= i-1 j) new-arg old-arg)))
    new-node))

(defmacro def-search-rewrite (name accessor type)
  `(progn
     (declaim (ftype (function (rose-node fixnum ,type
                                (function (t ,type finalize-node-fn fixnum) t)
                                finalize-node-fn fixnum)
                               t)
                     ,name))
     (defun ,name (node offset value rewrite-fn finalize-node beta-constant)
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
                              (funcall finalize-node
                                       (node-replace-arg node i (process arg value) offset)
                                       beta-constant))))))
                  (return-from process
                    (funcall rewrite-fn node value finalize-node beta-constant))))
         (process node value)))))

(declaim (inline search-rewrite-n-rewrites search-rewrite-weight))
(def-search-rewrite search-rewrite-n-rewrites rose-node-n-rewrites fixnum)
(def-search-rewrite search-rewrite-weight rose-node-weight single-float)

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
