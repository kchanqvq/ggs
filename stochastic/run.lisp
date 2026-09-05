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
  (let* ((pat-rows (mapcar (lambda (rule)
                             (destructuring-bind (lhs rhs &key (guard t)) rule
                               (multiple-value-list
                                (decompose-occur-check
                                 lhs
                                 (if-let (expand-fn (get cost-fn 'expand-cost-fn))
                                   `(when ,guard
                                      (yield-rewrite ,(funcall expand-fn rhs)
                                                     ,(expand-template rhs cost-fn)))
                                   `(when ,guard
                                      (let ((candidate ,(expand-template rhs cost-fn)))
                                        (yield-rewrite (cost #',cost-fn candidate) candidate))))))))
                           rules))
         (body (expand-match (list 'subject) pat-rows)))
    `(compute-weights
      (lambda (subject node cost beta-constant)
        (declare (optimize speed)
                 (rose-node node) (cost cost) (fixnum beta-constant))
        (macrolet ((yield-rewrite (cost-expr constructor)
                     (declare (ignore constructor))
                     `(locally (declare (optimize (safety 0)))
                        (incf (rose-node-n-rewrites node))
                        (incf (rose-node-weight node)
                              (fastexp2 (- cost ,cost-expr) beta-constant)))))
          ,@body))
      sample-inf-temp
      (lambda (subject context n-rewrites)
        (declare (optimize speed)
                 (function context) (fixnum n-rewrites))
        (macrolet ((yield-rewrite (cost-expr constructor)
                     (declare (ignore cost-expr))
                     `(locally (declare (optimize (safety 0)))
                        (decf n-rewrites)
                        (when (minusp n-rewrites)
                          (setq *node* (funcall context ,constructor))
                          (throw 'sample nil)))))
          ,@body)
        n-rewrites)
      sample-fin-temp
      (lambda (subject context weight cost beta-constant)
        (declare (optimize speed)
                 (function context) (single-float weight)
                 (cost cost) (fixnum beta-constant))
        (macrolet ((yield-rewrite (cost-expr constructor)
                     `(locally (declare (optimize (safety 0)))
                        (decf weight (fastexp2 (- cost ,cost-expr) beta-constant))
                        (when (minusp weight)
                          (setq *node* (funcall context ,constructor))
                          (throw 'sample nil)))))
          ,@body)
        weight))))

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

(defun recompute-rose (node compute-weights cost-fn beta-constant)
  (declare (optimize speed (safety 0))
           ((function (t) cost) cost-fn)
           ((function (rose-node rose-node cost fixnum) t) compute-weights))
  (labels ((process (node)
             (declare (rose-node node))
             (flet ((consider-rewrites (subject)
                      (funcall compute-weights subject node
                               (cost cost-fn subject) beta-constant)))
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

;; PROXY-COST-FN is still needed because SEARCH-ROSE-N-REWRITES need
;; to construct new nodes along the spine, whose cost need to be
;; computed
(defun sample-rewrite-inf-temp (sample-fn proxy-cost-fn)
  (declare (optimize speed)
           ((function (t) cost) proxy-cost-fn)
           ((function (t function fixnum) fixnum) sample-fn))
  (catch 'sample
    (multiple-value-bind (subject context n-rewrites)
        (search-rose-n-rewrites *node* (random (rose-node-n-rewrites *node*)) proxy-cost-fn)
      (declare (fixnum n-rewrites))
      ;; rewrites for this rose node
      (setq n-rewrites (funcall sample-fn subject context n-rewrites))
      ;; rewrites for constant symbol children
      (do-rose-node-args ((arg i) subject)
        (unless (rose-node-p arg)
          (klet ((context (candidate)
                   (funcall context (node-replace-arg subject i candidate proxy-cost-fn))))
            (setq n-rewrites (funcall sample-fn arg #'context n-rewrites))))))))

(defun sample-rewrite-fin-temp (sample-fn proxy-cost-fn beta-constant)
  (declare (optimize speed)
           ((function (t) cost) proxy-cost-fn)
           ((function (t function single-float cost fixnum) single-float) sample-fn)
           (fixnum beta-constant))
  (catch 'sample
    (multiple-value-bind (subject context weight)
        (search-rose-weight *node* (random (rose-node-weight *node*)) proxy-cost-fn)
      (declare (single-float weight))
      ;; rewrites for this rose node
      (let ((cost-1 (cost proxy-cost-fn subject)))
        (setq weight (funcall sample-fn subject context weight cost-1 beta-constant)))
      ;; rewrites for constant symbol children
      (do-rose-node-args ((arg i) subject)
        (unless (rose-node-p arg)
          (klet ((context (candidate)
                   (funcall context (node-replace-arg subject i candidate proxy-cost-fn))))
            (let ((cost-1 (cost proxy-cost-fn arg)))
              (setq weight (funcall sample-fn arg #'context weight cost-1 beta-constant)))))))))

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
                 (*node* init-node)
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
                (recompute-rose *node* compute-weights proxy-cost-fn beta-constant)

                ;; FIXME: a constant top-level *node* might still be rewritable,
                ;; although this probably is not usually useful.
                (when (or (not (rose-node-p *node*))
                          (zerop (rose-node-n-rewrites *node*)))
                  (return))

                (if (and inf-temp-period inf-temp-iters
                         (< (mod i inf-temp-period)
                            inf-temp-iters))
                    (sample-rewrite-inf-temp sample-inf-temp proxy-cost-fn)
                    (sample-rewrite-fin-temp sample-fin-temp proxy-cost-fn beta-constant))

                (incf n-accepted)
                (let ((cost (funcall cost-fn *node*)))
                  ;; Check for cost function decrease
                  (if (< cost best-cost-1)
                      (progn
                        (when verbose
                          (format t "~&Iteration ~a/~a found ~a ~a~%"
                                  seed i cost (node-term *node*)))
                        (setq best-cost-1 cost
                              n-stall 0)
                        (when (< cost best-cost)
                          (setq best-cost cost
                                best-term (node-term *node*))
                          (when (<= cost target-cost)
                            (setf (car finish-flag) t)
                            (return-from solve))))
                      (incf n-stall))
                  ;; Check for restart
                  (unless (and (< n-stall max-stall)
                               (< cost +inf-cost+))
                    (when verbose
                      (format t "~&Iteration ~a/~a restart ~a ~a~%"
                              seed i cost (node-term *node*)))
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
