(in-package :ggs/stochastic)

(declaim (inline fastlog2 fastexp2))
(serapeum:eval-always
  (defun fastlog2 (p)
    "Compute log2(P) approximately for *positive* integer P."
    (declare (optimize speed) (fixnum p))
    (let* ((exponent (1- (integer-length p)))
           (x (scale-float (coerce p 'single-float) (- exponent))))
      (declare (type single-float x))
      (+ exponent (- (* -0.4326728 x (- x 5.261706)) 1.8439242)))))

(declaim (inline fastexp2))
(defun constant-for-fastexp2 (base)
  (values (floor (* (expt 2 23) (log base 2)))))
(defun fastexp2 (p base-constant)
  (declare (optimize speed (safety 0))
           (fixnum p base-constant))
  (min (float-features:bits-single-float
        (max 0 (min #x7F800000 (+ (the fixnum (* p base-constant))
                                  (- (ash 127 23) 366393)))))
       1e20))

(declaim (inline cost))
(defun cost (cost-fn node)
  (if (rose-node-p node)
      (rose-node-cost node)
      (funcall cost-fn node)))

(defconstant +inf-cost+ 100000000)
(deftype cost () `(integer 0 ,+inf-cost+))

(defun compute-rule-set-lambda (cost-fn rules)
  (let ((matcher
          (macroexpand-1
           `(do-matches* subject
              ,@(mapcar (lambda (rule)
                          (destructuring-bind (lhs rhs &key (guard t)) rule
                            (list lhs
                                  (if-let (expand-fn (get cost-fn 'expand-cost-fn))
                                    `(when ,guard
                                       (yield-rewrite ,(funcall expand-fn rhs)
                                                      ,(expand-template rhs cost-fn)))
                                    `(when ,guard
                                       (let ((candidate ,(expand-template rhs cost-fn)))
                                         (yield-rewrite (cost #',cost-fn candidate) candidate)))))))
                        rules)))))
    `(compute-weights
      (lambda (subject node beta-constant)
        (declare (optimize speed)
                 (rose-node node)
                 (fixnum beta-constant))
        (let ((cost (cost #',cost-fn subject)))
          (declare (ignorable cost))
          (macrolet ((yield-rewrite (cost-expr constructor)
                       (declare (ignore constructor))
                       `(locally (declare (optimize (safety 0)))
                          (incf (rose-node-n-rewrites node))
                          (incf (rose-node-weight node)
                                (fastexp2 (- cost ,cost-expr) beta-constant)))))
            ,matcher)))
      sample-inf-temp
      (lambda (subject n-rewrites)
        (declare (optimize speed)
                 (fixnum n-rewrites))
        (block sample
          (macrolet ((yield-rewrite (cost-expr constructor)
                       (declare (ignore cost-expr))
                       `(locally (declare (optimize (safety 0)))
                          (decf n-rewrites)
                          (when (minusp n-rewrites)
                            (return-from sample (values n-rewrites ,constructor))))))
            ,matcher)
          (values n-rewrites nil)))
      sample-fin-temp
      (lambda (subject weight beta-constant)
        (declare (optimize speed)
                 (single-float weight)
                 (fixnum beta-constant))
        (block sample
          (let ((cost (cost #',cost-fn subject)))
            (declare (ignorable cost))
            (macrolet ((yield-rewrite (cost-expr constructor)
                         `(locally (declare (optimize (safety 0)))
                            (decf weight (fastexp2 (- cost ,cost-expr) beta-constant))
                            (when (minusp weight)
                              (return-from sample (values weight ,constructor))))))
              ,matcher))
          (values weight nil))))))

(defun get-rules-resolve-symbols (name)
  (mapcan (lambda (rule)
            (if (symbolp rule)
                (get-rules-resolve-symbols rule)
                (list rule)))
          (get-rules name)))

(defmacro precompile-rule-set (name cost-fn)
  (let ((rules (get-rules-resolve-symbols name)))
    `(let ((rules (get-rules-resolve-symbols ',name)))
       (assert (equal rules ',rules))
       (ensure-cache (assoc-value (get ',name 'compiled-rules) ',cost-fn) rules
                     (list ,@(collecting
                               (doplist (key lambda (compute-rule-set-lambda cost-fn rules))
                                        (collect `',key)
                                 (collect lambda))))))))

(defun compiled-rule-set (name cost-fn)
  (let ((rules (get-rules-resolve-symbols name)))
    (ensure-cache (assoc-value (get name 'compiled-rules) cost-fn) rules
                  (collecting
                    (doplist (key lambda (compute-rule-set-lambda cost-fn (get-rules-resolve-symbols name)))
                             (collect key)
                      (collect (compile nil lambda)))))))

;;; FIXME: the following assumes:
;;; 1. :eval only result in constants, never compound terms
;;; 2. non 0-ary function symbols are never reused as constants
;;; 3. constants are all in the T case

(defun get-case (key cases)
  (dolist (case cases)
    (cond ((eql (first case) t)
           (return (second case)))
          ((member key (ensure-list (first case)))
           (return (second case))))))

(defun default-case (cases)
  (second (assoc t cases)))

(defun expand-tree-sum-cost (tmpl cases)
  (let ((coefficients (make-hash-table))
        (secant 0))
    (labels ((process (tmpl)
               (cond ((and (consp tmpl) (eql (car tmpl) :eval))
                      (incf secant (default-case cases)))
                     ((consp tmpl)
                      (incf secant (get-case (car tmpl) cases))
                      (mapc #'process (cdr tmpl)))
                     ((var-p tmpl)
                      (incf (gethash tmpl coefficients 0)))
                     (t (incf secant (default-case cases))))))
      (process tmpl)
      `(+ ,secant
          ,@(serapeum:collecting
              (maphash (lambda (var c)
                         (collect `(the cost
                                        (* ,c (if (rose-node-p ,var)
                                                  (rose-node-cost ,var)
                                                  ,(default-case cases))))))
                       coefficients))))))

(defmacro define-tree-sum-cost (name &rest cases)
  `(progn
     (defun ,name (node)
       (if (rose-node-p node)
           (let ((sum (case (rose-node-fsym node) ,@cases)))
             (declare (cost sum))
             (do-rose-node-args (arg node)
               (incf sum (if (rose-node-p arg)
                             (rose-node-cost arg)
                             ,(default-case cases))))
             sum)
           ,(default-case cases)))
     (eval-always
       (setf (get ',name 'expand-cost-fn)
             (lambda (tmpl) (expand-tree-sum-cost tmpl ',cases))))))

(defun recompute-rose (node compute-weights beta-constant)
  (declare (optimize speed (safety 0))
           ((function (rose-node rose-node fixnum) t) compute-weights))
  (labels ((process (node)
             (declare (rose-node node))
             (flet ((consider-rewrites (subject)
                      (funcall compute-weights subject node beta-constant)))
               (setf (rose-node-n-rewrites node) 0)
               (do-rose-node-args (arg node)
                 (if (rose-node-p arg)
                     (progn
                       (when (minusp (rose-node-n-rewrites arg))
                         (process arg))
                       (incf (rose-node-n-rewrites node) (rose-node-n-rewrites arg))
                       (incf (rose-node-weight node) (rose-node-weight arg)))
                     ;; Probability weight of constant symbol children
                     ;; are counted together
                     (consider-rewrites arg)))
               (consider-rewrites node))))
    (when (rose-node-p node)
      (when (minusp (rose-node-n-rewrites node))
        (process node)))))

(declaim (inline sample-rewrite-inf-temp sample-rewrite-fin-temp))

;; PROXY-COST-FN is still needed because SEARCH-ROSE-N-REWRITES need
;; to construct new nodes along the spine, whose cost need to be
;; computed
(defun sample-rewrite-inf-temp (root sample-fn proxy-cost-fn)
  (declare (optimize speed)
           ((function (t) cost) proxy-cost-fn)
           ((function (t fixnum) (values fixnum t)) sample-fn))
  (search-rewrite-n-rewrites
   root (random (rose-node-n-rewrites root)) proxy-cost-fn
   (lambda (subject n-rewrites)
     (declare (rose-node subject)
              (fixnum n-rewrites))
     (block sample
       (let (result)
         ;; rewrites for this rose node
         (setf (values n-rewrites result)
               (funcall sample-fn subject n-rewrites))
         (when (minusp n-rewrites)
           (return-from sample result))
         ;; rewrites for constant symbol children
         (do-rose-node-args ((arg i) subject)
           (unless (rose-node-p arg)
             (setf (values n-rewrites result) (funcall sample-fn arg n-rewrites))
             (when (minusp n-rewrites)
               (return-from sample (node-replace-arg subject i result proxy-cost-fn))))))
       subject))))

(defun sample-rewrite-fin-temp (root sample-fn proxy-cost-fn beta-constant)
  (declare (optimize speed)
           ((function (t) cost) proxy-cost-fn)
           ((function (t single-float fixnum) (values single-float t)) sample-fn)
           (fixnum beta-constant))
  (search-rewrite-weight
   root (random (rose-node-weight root)) proxy-cost-fn
   (lambda (subject weight)
     (declare (rose-node subject)
              (single-float weight))
     (block sample
       (let (result)
         ;; rewrites for this rose node
         (setf (values weight result)
               (funcall sample-fn subject weight beta-constant))
         (when (minusp weight)
           (return-from sample result))
         ;; rewrites for constant symbol children
         (do-rose-node-args ((arg i) subject)
           (unless (rose-node-p arg)
             (setf (values weight result)
                   (funcall sample-fn arg weight beta-constant))
             (when (minusp weight)
               (return-from sample (node-replace-arg subject i result proxy-cost-fn)))))
         subject)))))

(defun stochastic-search-1
    (term rule-set cost-fn
     &key (finish-flag (list nil)) (seed 0) (stride 1)
       (beta 2.0) (inf-temp-period 100) (inf-temp-iters 3)
       (max-stall 16000) (max-restart 64)
       (target-cost 0) max-time
       (proxy-cost-fn cost-fn)
       verbose)
  (declare ((or null fixnum) inf-temp-period)
           ((or null fixnum) inf-temp-iters)
           (single-float beta))
  (bind ((end-time (and max-time
                        (+ (get-internal-real-time)
                           (* max-time internal-time-units-per-second))))
         ((compute-weights sample-inf-temp sample-fin-temp)
          (mapcar (curry #'getf (compiled-rule-set rule-set proxy-cost-fn))
                  '(compute-weights sample-inf-temp sample-fin-temp)))
         (cost-fn (ensure-function cost-fn))
         (proxy-cost-fn (ensure-function proxy-cost-fn))
         (beta-constant (constant-for-fastexp2 (exp (/ beta 2))))
         (init-node (term-node term proxy-cost-fn))
         (init-cost (funcall cost-fn init-node))
         (best-term (node-term init-node))
         (best-cost init-cost)
         (n-accepted 0)
         (n-restart 0))
    (declare ((function (t) cost) cost-fn proxy-cost-fn))
    (float-features:with-float-traps-masked t
      ;; Outer loop: restart with different seeds
      (block solve
        (loop for seed from seed below (+ seed max-restart) by stride do
          ;; Inner loop: one run of stochastic search
          (let* ((*random-state* (sb-ext:seed-random-state seed))
                 (node init-node)
                 (best-cost-1 init-cost)
                 (n-stall 0))
            (declare (fixnum n-accepted n-restart))
            (incf n-restart)
            (loop for i of-type fixnum from 0 do
              (progn
                (when (or (car finish-flag)
                          ;; Check time every 1024 iters, because
                          ;; GET-INTERNAL-REAL-TIME is slow
                          (and end-time (zerop (mod i 1024)) (>= (get-internal-real-time) end-time)))
                  (return-from solve))
                (recompute-rose node compute-weights beta-constant)

                ;; FIXME: a constant top-level NODE might still be rewritable,
                ;; although this probably is not usually useful.
                (when (or (not (rose-node-p node))
                          (zerop (rose-node-n-rewrites node)))
                  (return))

                (if (and inf-temp-period inf-temp-iters
                         (< (mod i inf-temp-period)
                            inf-temp-iters))
                    (setq node (sample-rewrite-inf-temp node sample-inf-temp proxy-cost-fn))
                    (setq node (sample-rewrite-fin-temp node sample-fin-temp proxy-cost-fn beta-constant)))

                (incf n-accepted)
                (let ((cost (funcall cost-fn node)))
                  ;; Check for cost function decrease
                  (if (< cost best-cost-1)
                      (progn
                        (when verbose
                          (format t "~&Iteration ~a/~a found ~a ~a~%"
                                  seed i cost (node-term node)))
                        (setq best-cost-1 cost
                              n-stall 0)
                        (when (< cost best-cost)
                          (setq best-cost cost
                                best-term (node-term node))
                          (when (<= cost target-cost)
                            (setf (car finish-flag) t)
                            (return-from solve))))
                      (incf n-stall))
                  ;; Check for restart
                  (unless (and (< n-stall max-stall)
                               (< cost +inf-cost+))
                    (when verbose
                      (format t "~&Iteration ~a/~a restart ~a ~a~%"
                              seed i cost (node-term node)))
                    (return)))))))))
    (values best-cost best-term (list :n-accepted n-accepted :n-restart n-restart))))

(defun reduce-stochastic-result (results-1 results-2)
  (destructuring-bind (bc1 bt1 (&key ((:n-accepted na1)) ((:n-restart nr1)))) results-1
    (destructuring-bind (bc2 bt2 (&key ((:n-accepted na2)) ((:n-restart nr2)))) results-2
      (append (if (< bc1 bc2)
                  (list bc1 bt1)
                  (list bc2 bt2))
              (list (list :n-accepted (+ na1 na2) :n-restart (+ nr1 nr2)))))))

(defun worker-loop ()
  (with-standard-io-syntax
    (loop
      (handler-case
          (prin1 (cons :result (multiple-value-list (eval (read)))))
        (serious-condition (c)
          (prin1 (cons :error (princ-to-string c)))))
      (terpri)
      (finish-output))))

(defun stochastic-search (term rule-set cost-fn &rest args
                          &key (seed 0) (stride 1)
                            (beta 2.0) (inf-temp-period 100) (inf-temp-iters 3)
                            (max-stall 16000) (max-restart 64)
                            (target-cost 0) max-time
                            (proxy-cost-fn cost-fn)
                            verbose
                            (nproc 1) workers)
  (declare (ignore beta inf-temp-period inf-temp-iters
                   max-stall max-restart
                   target-cost max-time
                   verbose))
  (cond (workers
         (let ((n-workers (length workers)))
           (multiple-value-bind (nproc rem) (floor nproc n-workers)
             (loop for proc in workers
                   for i from 0
                   for nproc-1 = (if (< i rem) (1+ nproc) nproc)
                   do (with-standard-io-syntax
                        (write `(apply #'stochastic-search
                                       ',term ',rule-set ',cost-fn
                                       :seed ',(+ seed (* i stride))
                                       :stride ',(* n-workers stride)
                                       :nproc ',nproc-1
                                       ',(remove-from-plist args :workers :nproc :seed :stride))
                               :stream (uiop:process-info-input proc))
                        (terpri (uiop:process-info-input proc))
                        (finish-output (uiop:process-info-input proc)))))
           (values-list
            (reduce #'reduce-stochastic-result workers :key
                    (lambda (proc)
                      (let ((result (with-standard-io-syntax
                                      (read (uiop:process-info-output proc)))))
                        (ecase (car result)
                          (:result (cdr result))
                          (:error (error "Error in worker: ~a" (cadr result))))))))))
        ((> nproc 1)
         ;; Compile rule sets in main thread only
         (compiled-rule-set rule-set proxy-cost-fn)
         (let* ((finish-flag (list nil))
                (threads (mapcar (lambda (i)
                                   (bt:make-thread
                                    (lambda ()
                                      (multiple-value-list
                                       (apply #'stochastic-search-1 term rule-set cost-fn
                                              :seed (+ seed (* i stride))
                                              :stride (* nproc stride)
                                              :finish-flag finish-flag
                                              (remove-from-plist args :workers :nproc :seed :stride))))
                                    :name (format nil "search worker ~a" i)))
                                 (iota nproc))))
           (unwind-protect
                (values-list (reduce #'reduce-stochastic-result threads :key #'bt:join-thread))
             (setf (car finish-flag) t))))
        ((= nproc 0) (values +inf-cost+ term (list :n-accepted 0 :n-restart 0)))
        (t (apply #'stochastic-search-1
                  term rule-set cost-fn
                  (remove-from-plist args :nproc :workers)))))
