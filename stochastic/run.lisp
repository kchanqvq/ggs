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

(defun get-user-decls (env)
  `((optimize ,@(remove-if-not (lambda (policy)
                                 (member (car policy) '(speed safety)))
                               (cl-environments:declaration-information 'optimize env)))))

(defun compute-rule-set-lambda (rules cost-fn user-decls)
  (bind (((:flet match-clause (rule))
          (destructuring-bind (lhs rhs &key (guard t)) rule
            (list lhs
                  `(when (locally (declare ,@user-decls) ,guard)
                     (yield-rewrite ,(funcall (get cost-fn 'expand-cost-fn) rhs)
                                    ,(expand-template rhs cost-fn user-decls))))))
         ;; Partition rules into that may match compound terms, and may match
         ;; constant.  The partition might not be disjoint, e.g. top-level ?a
         ;; matches both compound terms and constants.
         (compound-rules
          (remove-if-not (lambda (lhs) (if (consp lhs) (cdr lhs) (var-p lhs)))
                         rules :key #'car))
         (compound-matcher
          (macroexpand-1 `(do-matches* subject ,@(mapcar #'match-clause compound-rules))))
         (constant-rules
          ;; Turn ?a into (?a) so it only match constants.  For stochastic
          ;; backend, "constant term" and "constant function symbol" happens to
          ;; be the same because of unboxed representation.
          (mapcar (lambda (rule) (cons (ensure-list (car rule)) (cdr rule)))
                  (remove-if-not (lambda (lhs) (if (consp lhs) (null (cdr lhs)) t))
                                 rules :key #'car)))
         (constant-matcher
          (macroexpand-1 `(do-matches* arg ,@(mapcar #'match-clause constant-rules)))))

    `(compute-weights
      (lambda (subject beta-constant)
        (declare (optimize speed (safety 0))
                 (rose-node subject)
                 (fixnum beta-constant))
        (let ((cost (cost #',cost-fn subject)))
          (declare (ignorable cost))
          (macrolet ((yield-rewrite (cost-expr constructor)
                       (declare (ignore constructor))
                       `(progn
                          (incf (rose-node-n-rewrites subject))
                          (incf (rose-node-weight subject)
                                (fastexp2 (- cost ,cost-expr) beta-constant)))))
            ,compound-matcher))
        ,(when constant-rules
           `(do-rose-node-args (arg subject)
              ;; FIXME: assume all constant has the same cost
              (let ((cost ,(funcall (get cost-fn 'expand-cost-fn) 0)
                          #+nil (cost #',cost-fn arg)))
                (macrolet ((yield-rewrite (cost-expr constructor)
                             (declare (ignore constructor))
                             `(progn
                                (incf (rose-node-n-rewrites subject))
                                (incf (rose-node-weight subject)
                                      (fastexp2 (- cost ,cost-expr) beta-constant)))))
                  ,constant-matcher)))))

      sample-inf-temp
      (lambda (subject n-rewrites)
        (declare (optimize speed (safety 0))
                 (rose-node subject)
                 (fixnum n-rewrites))
        (block sample
          (macrolet ((yield-rewrite (cost-expr constructor)
                       (declare (ignore cost-expr))
                       `(progn
                          (decf n-rewrites)
                          (when (minusp n-rewrites)
                            (return-from sample ,constructor)))))
            ,compound-matcher)
          ,(when constant-rules
             `(do-rose-node-args ((arg i) subject)
                (macrolet ((yield-rewrite (cost-expr constructor)
                             (declare (ignore cost-expr))
                             `(progn
                                (decf n-rewrites)
                                (when (minusp n-rewrites)
                                  (return-from sample
                                    (node-replace-arg subject i ,constructor #',',cost-fn))))))
                  ,constant-matcher)))
          subject))

      sample-fin-temp
      (lambda (subject weight beta-constant)
        (declare (optimize speed (safety 0))
                 (rose-node subject)
                 (single-float weight)
                 (fixnum beta-constant))
        (block sample
          (let ((cost (cost #',cost-fn subject)))
            (declare (ignorable cost))
            (macrolet ((yield-rewrite (cost-expr constructor)
                         `(progn
                            (decf weight (fastexp2 (- cost ,cost-expr) beta-constant))
                            (when (minusp weight)
                              (return-from sample ,constructor)))))
              ,compound-matcher))
          ,(when constant-rules
             `(do-rose-node-args ((arg i) subject)
                ;; FIXME: assume all constant has the same cost
                (let ((cost ,(funcall (get cost-fn 'expand-cost-fn) 0)))
                  (macrolet ((yield-rewrite (cost-expr constructor)
                               `(progn
                                  (decf weight (fastexp2 (- cost ,cost-expr) beta-constant))
                                  (when (minusp weight)
                                    (return-from sample
                                      (node-replace-arg subject i ,constructor #',',cost-fn))))))
                    ,constant-matcher))))
          subject)))))

(defun get-rules-resolve-symbols (name)
  (mapcan (lambda (rule)
            (if (symbolp rule)
                (get-rules-resolve-symbols rule)
                (list rule)))
          (get-rules name)))

(defvar *compiled-rule-sets* (make-hash-table :test 'equal))

(defmacro precompile-rule-set (name cost-fn &environment env)
  (let ((rules (get-rules-resolve-symbols name))
        (user-decls (get-user-decls env)))
    `(let ((rules ',rules))
       (unless (equal rules (get-rules-resolve-symbols ',name))
         (warn "Rule set ~A changed between compile and load time" ',name))
       (setf (gethash (list rules ',cost-fn ',user-decls)
                      *compiled-rule-sets*)
             (list ,@(collecting
                       (doplist (key lambda (compute-rule-set-lambda
                                             rules cost-fn user-decls))
                         (collect `',key)
                         (collect lambda))))))))

(defun compiled-rule-set (name cost-fn)
  (let ((rules (get-rules-resolve-symbols name))
        (user-decls (get-user-decls nil)))
    (ensure-gethash (list rules cost-fn user-decls)
                    *compiled-rule-sets*
                    (collecting
                      (doplist (key lambda (compute-rule-set-lambda
                                            rules cost-fn user-decls))
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
           ((function (rose-node fixnum) null) compute-weights))
  (labels ((process (node)
             (declare (rose-node node))
             (setf (rose-node-n-rewrites node) 0)
             (do-rose-node-args (arg node)
               (when (rose-node-p arg)
                 (when (minusp (rose-node-n-rewrites arg))
                   (process arg))
                 (incf (rose-node-n-rewrites node) (rose-node-n-rewrites arg))
                 (incf (rose-node-weight node) (rose-node-weight arg))))
             ;; Probability weight of constant symbol children
             ;; are counted together
             (funcall compute-weights node beta-constant)))
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
           ((function (t fixnum) t) sample-fn))
  (search-rewrite-n-rewrites
   root (random (rose-node-n-rewrites root)) proxy-cost-fn
   sample-fn))

(defun sample-rewrite-fin-temp (root sample-fn proxy-cost-fn beta-constant)
  (declare (optimize speed)
           ((function (t) cost) proxy-cost-fn)
           ((function (t single-float fixnum) t) sample-fn)
           (fixnum beta-constant))
  (search-rewrite-weight
   root (random (rose-node-weight root)) proxy-cost-fn
   (lambda (subject weight)
     (funcall sample-fn subject weight beta-constant))))

(defun stochastic-search-1
    (term rule-set cost-fn
     &key (finish-flag (list nil)) (seed 0) (stride 1)
       (beta 2.0)
       (soft-walk 0) (soft-stall nil) (hard-walk soft-walk) (max-stall 16000)
       (target-cost 0) max-time (max-restart 64)
       (proxy-cost-fn cost-fn)
       verbose save-cost-history)
  (declare ((or null integer) soft-stall max-restart)
           (integer hard-walk soft-walk)
           (single-float beta))
  (bind ((start-time (get-internal-real-time))
         (end-time (and max-time
                        (+ start-time
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
         (n-restart 0)
         (cost-history '()))
    (declare ((function (t) cost) cost-fn proxy-cost-fn))
    (float-features:with-float-traps-masked t
      ;; Outer loop: restart with different seeds
      (block solve
        (loop for seed-1 from seed by stride do
          ;; Inner loop: one run of stochastic search
          (let* ((*random-state* (sb-ext:seed-random-state seed-1))
                 (node init-node)
                 (best-cost-1 init-cost)
                 (n-stall 0)
                 (best-cost-soft init-cost)
                 (n-stall-soft 0)
                 (n-walk hard-walk))
            (declare (integer n-accepted n-restart n-stall n-stall-soft n-walk))
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

                (cond ((plusp n-walk)
                       (decf n-walk)
                       (setq node
                             (search-rewrite-n-rewrites
                              node (random (rose-node-n-rewrites node))
                              proxy-cost-fn sample-inf-temp)))
                      (t
                       (setq node
                             (search-rewrite-weight
                              node (random (rose-node-weight node))
                              proxy-cost-fn
                              (lambda (subject weight)
                                (funcall sample-fin-temp subject weight beta-constant))))))

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
                          (when save-cost-history
                            (push (list (- (get-internal-real-time) start-time) cost)
                                  cost-history))
                          (when (<= cost target-cost)
                            (setf (car finish-flag) t)
                            (return-from solve))))
                      (incf n-stall))

                  ;; inf-temp walk (soft restart) bookkeeping
                  (if (or (plusp n-walk) (< cost best-cost-soft))
                      (setq best-cost-soft cost
                            n-stall-soft 0)
                      (incf n-stall-soft))
                  (when (and soft-stall (>= n-stall-soft soft-stall))
                    (setq n-walk soft-walk
                          n-stall-soft 0))

                  ;; Check for restart
                  (unless (and (< n-stall max-stall)
                               (< cost +inf-cost+))
                    (when verbose
                      (format t "~&Iteration ~a/~a restart ~a ~a~%"
                              seed i cost (node-term node)))
                    (return))

                  (when (and max-restart (>= seed-1 (+ seed max-restart)))
                    (return-from solve)))))))))
    (values best-cost best-term
            `( :n-accepted ,n-accepted :n-restart ,n-restart
               ,@(when save-cost-history `(:cost-history ,(nreverse cost-history)))))))

(defun merge-cost-history (st1 st2)
  "Merge two time-ordered (TIME COST) lists, keeping only strict improvements."
  (let ((st '())
        (best-cost +inf-cost+))
    (loop
      (when (or (not st1) (and st2 (>= (caar st1) (caar st2))))
        (rotatef st1 st2))
      (when (not st1) (return))
      (when (< (cadar st1) best-cost)
        (setq best-cost (cadar st1))
        (push (car st1) st))
      (pop st1))
    (nreverse st)))

(defun reduce-stochastic-result (results-1 results-2)
  (bind (((bc1 bt1 plist1) results-1)
         ((bc2 bt2 plist2) results-2)
         ((:plist (na1 :n-accepted) (nr1 :n-restart) (st1 :cost-history 'unbound)) plist1)
         ((:plist (na2 :n-accepted) (nr2 :n-restart) (st2 :cost-history 'unbound)) plist2))
    `(,@(if (< bc1 bc2) (list bc1 bt1) (list bc2 bt2))
      ( :n-accepted ,(+ na1 na2) :n-restart ,(+ nr1 nr2)
        ,@(unless (eq st1 'unbound)
            `(:cost-history ,(merge-cost-history st1 st2)))))))

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
                            (beta 2.0)
                            (soft-walk 0) (soft-stall nil) (hard-walk soft-walk) (max-restart 64)
                            (target-cost 0) max-time (max-stall 16000)
                            (proxy-cost-fn cost-fn)
                            verbose save-cost-history
                            (nproc 1) workers)
  (declare (ignore beta
                   max-stall max-restart soft-stall hard-walk
                   target-cost max-time
                   verbose save-cost-history))
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
