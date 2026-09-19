(in-package :ggs/eqsat)

(define-condition match-limit-exceeded (error)
  ((name :initarg :name)
   (rule :initarg :rule)
   (match-limit :initarg :match-limit))
  (:report (lambda (c s)
             (format s "Match limit ~a for rule ~a ~a exceeded."
                     (slot-value c 'match-limit)
                     (slot-value c 'name)
                     (slot-value c 'rule)))))

(defun compute-rule-lambda (name rule)
  `(lambda (&key match-limit)
     (when match-limit
       (let ((remaining match-limit))
         (do-matches (top-node ,(car rule))
           (decf remaining)
           (when (minusp remaining)
             (error 'match-limit-exceeded
                    :name ',name :rule ',rule :match-limit match-limit)))))
     (do-matches (top-node ,(car rule))
       (macrolet ((yield-rewrite (rhs)
                    `(enode-merge top-node ,(expand-template rhs))))
         ,@(cdr rule)))))

(defvar *compiled-rules* (make-hash-table :test 'equal))

(defmacro precompile-rule-set (name)
  (let ((rules (get-rules name)))
    `(let ((rules (get-rules ',name)))
       (unless (equal rules ',rules)
         (warn "Rule set ~A changed between compile and load time" ',name))
       ,@(mapcar (lambda (rule)
                   (if (symbolp rule)
                       `(precompile-rule-set ,rule)
                       `(setf (gethash '(,name ,rule) *compiled-rules*)
                              ,(compute-rule-lambda name rule))))
                 rules)
       ',name)))

(defun compiled-rules (name)
  (mappend (lambda (rule)
             (if (symbolp rule)
                 (compiled-rules rule)
                 (list
                  (ensure-gethash (list name rule) *compiled-rules*
                                  (compile nil (compute-rule-lambda name rule))))))
           (get-rules name)))

(defun run-rewrites (rule-sets &key max-iter max-time check verbose
                                 initial-match-limit
                                 (initial-ban-length 5)
                                 prune-constant)
  "Run RULE-SETS repeatly on `*egraph*' until some stop criterion.

RULE-SETS can be a symbol naming a single rule set, or a list of such symbols.

Returns the reason for termination: one of :max-iter, :saturate.

If INITIAL-MATCH-LIMIT is non-nil, schedule rules in the style of
egg's BackoffScheduler.

Note: this function does not call `egraph-rebuild' upfront. Particularly, if you
have added some terms to EGRAPH, you MUST call `egraph-rebuild' before calling
this function."
  (let ((n-enodes (egraph-n-enodes *egraph*))
        (n-eclasses (egraph-n-eclasses *egraph*))
        (n-iter 0)
        (ban-until-table (make-hash-table))
        (ban-times-table (make-hash-table))
        (start-time (get-internal-real-time))
        (rules (mappend #'compiled-rules (ensure-list rule-sets))))
    (catch 'stop
      (loop
        (when (and max-iter (>= n-iter max-iter))
          (return :max-iter))
        (when (and max-time (>= (/ (- (get-internal-real-time) start-time)
                                   internal-time-units-per-second)
                                max-time))
          (return :max-time))
        (when verbose (format t "Iteration ~d: " n-iter))
        (when verbose (format t "Applying rules... "))
        (unwind-protect
             (dolist (rule rules)
               (let* ((ban-until (gethash rule ban-until-table))
                      (ban-times (gethash rule ban-times-table 0))
                      (match-limit (and initial-match-limit
                                        (ash initial-match-limit ban-times))))
                 (unless (and ban-until (< n-iter ban-until))
                   (remhash rule ban-until-table)
                   (handler-case (funcall rule :match-limit match-limit)
                     (match-limit-exceeded (c)
                       (when verbose (format t "~&~a~%" c))
                       (setf (gethash rule ban-until-table)
                             (+ n-iter (ash initial-ban-length ban-times)))
                       (incf (gethash rule ban-times-table 0)))))))
          (when verbose (format t "Rebuilding... "))
          (egraph-rebuild :prune-constant prune-constant))
        (when check (check-egraph))
        (incf n-iter)
        (let ((n-enodes-1 (egraph-n-enodes *egraph*))
              (n-eclasses-1 (egraph-n-eclasses *egraph*)))
          (when verbose
            (format t "Done. ~a enodes, ~a eclasses~%" n-enodes-1 n-eclasses-1))
          (cond ((not (and (= n-enodes n-enodes-1) (= n-eclasses n-eclasses-1)))
                 (setq n-enodes n-enodes-1 n-eclasses n-eclasses-1))
                ;; Some rules are still banned, skip till they reactivate
                ((plusp (hash-table-count ban-until-table)))
                (t (return :saturate))))))))
