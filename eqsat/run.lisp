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

(defun compute-rule-lambda (name rule user-decls)
  `(lambda (&key match-limit)
     (declare (optimize speed (safety 0)))
     (macrolet ((get-analysis-data (name enode)
                  `(the ,(getf (get-analysis name) :type)
                        (enode-analysis-data ',name ,enode))))
       (when match-limit
         (let ((remaining match-limit))
           (declare (type fixnum remaining))
           (do-match-all (top-node ,(car rule))
             (decf remaining)
             (when (minusp remaining)
               (error 'match-limit-exceeded
                      :name ',name :rule ',rule :match-limit match-limit)))))
       (do-match-all (top-node ,(car rule))
         (macrolet ((yield-rewrite (rhs)
                      `(enode-merge top-node ,(expand-template rhs))))
           (locally (declare ,@user-decls) ,@(cdr rule)))))))

(defparameter *compiled-rules* (make-hash-table :test 'equal))

(defmacro precompile-eqsat-rule-set (name &environment env)
  (let ((rules (get-rules name))
        (user-decls (get-user-decls env)))
    `(let ((rules (get-rules ',name)))
       (unless (equal rules ',rules)
         (warn "Rule set ~A changed between compile and load time" ',name))
       ,@(mapcar (lambda (rule)
                   (if (symbolp rule)
                       `(precompile-eqsat-rule-set ,rule)
                       `(setf (gethash '(,name ,rule ,user-decls) *compiled-rules*)
                              ,(compute-rule-lambda name rule user-decls))))
                 rules)
       ',name)))

(defun compiled-rules (name)
  "Return an ALIST of ((LAMBDA INCLUDED-FROM...) ...)."
  (bind ((user-decls (get-user-decls nil))
         (warned nil)
         ((:labels process (rule-set))
          (mapcar (rcurry #'append (list rule-set))
                  (mappend
                   (lambda (rule)
                     (if (symbolp rule)
                         (process rule)
                         `((,(ensure-gethash
                              (list rule-set rule user-decls) *compiled-rules*
                              (progn
                                (unless warned
                                  (warn 'runtime-compile-warning
                                        :form `(precompile-eqsat-rule-set ,name))
                                  (setq warned t))
                                (compile nil (compute-rule-lambda rule-set rule user-decls))))))))
                   (get-rules rule-set)))))
    (process name)))

(defstruct (backoff-state
            (:constructor make-backoff-state (&key (initial-match-limit 1000)
                                                (initial-ban-length 5))))
  "Can be passed as `:backoff-state' argument to `run-rewrites' to schedule rules
in the style of egg's BackoffScheduler. INITIAL-MATCH-LIMIT and
INITIAL-BAN-LENGTH can either be numbers that specify the respective values for
all rules, or alists of form ((RULE . VALUE) ...) that provide rule-specific
configurations. If RULE names a rule set, VALUE applies to each individual rule
included in that rule set. Explicit NIL VALUE disables backoff scheduling for
applicable rules. If RULE is T, VALUE specifies the default value for all
rules. When multiple configuration values are applicable for a rule, the most
specific one takes precedence. INITIAL-BAN-LENGTH defaults to 5 when no value is
specified and INITIAL-MATCH-LIMIT defaults to 1000 when no value is specified."
  (ban-until-table (make-hash-table))
  (ban-times-table (make-hash-table))
  initial-match-limit initial-ban-length)

(defun run-rewrites (rule-sets &key verbose prune-constant backoff-state)
  "Run RULE-SETS on `*egraph*' for one iteration. RULE-SETS can be a symbol naming
a single rule set, or a list of such symbols. Return T if running RULE-SETS with
the same options repeatedly will no longer change `*egraph*', i.e. `*egraph*' is
saturated. PRUNE-CONSTANT can be nil or a predicate, such that if some constant
satisfies it, all other enodes within the same eclass are deleted. BACKOFF-STATE
can be nil or an object made by `make-backoff-state' which enables scheduling in
the style of egg's BackoffScheduler.

Note: this function does not call `egraph-rebuild' upfront. Particularly, if you
have added some terms to EGRAPH, you MUST call `egraph-rebuild' before calling
this function."
  (bind ((n-enodes (egraph-n-enodes *egraph*))
         (n-eclasses (egraph-n-eclasses *egraph*))
         (rules (mappend #'compiled-rules (ensure-list rule-sets))))
    (when verbose (format t "Applying rules... "))
    (unwind-protect
         (loop for (rule . included-names) in rules do
           (cond (backoff-state
                  (bind (((:struct backoff-state- ban-until-table ban-times-table
                                   initial-match-limit initial-ban-length)
                          backoff-state)
                         (ban-until (gethash rule ban-until-table))
                         (ban-times (gethash rule ban-times-table 0))
                         (initial-match-limit (alist-like-get included-names initial-match-limit 1000))
                         (initial-ban-length (alist-like-get included-names initial-ban-length 5))
                         ;; FIXME: will we ever want match-limit greater than
                         ;; `most-positive-fixnum'?
                         (match-limit (and initial-match-limit initial-ban-length
                                           (min (ash initial-match-limit ban-times)
                                                most-positive-fixnum))))
                    (cond ((not ban-until)
                           (handler-case (funcall rule :match-limit match-limit)
                             (match-limit-exceeded (c)
                               (when verbose (format t "~&~a~%" c))
                               (setf (gethash rule ban-until-table)
                                     (1- (ash initial-ban-length ban-times)))
                               (incf (gethash rule ban-times-table 0)))))
                          ((> ban-until 1) (decf (gethash rule ban-until-table)))
                          (ban-until (remhash rule ban-until-table)))))
                 (t (funcall rule))))
      (when verbose (format t "Rebuilding... "))
      (egraph-rebuild :prune-constant prune-constant))
    (let ((n-enodes-1 (egraph-n-enodes *egraph*))
          (n-eclasses-1 (egraph-n-eclasses *egraph*)))
      (when verbose
        (format t "Done. ~a enodes, ~a eclasses~%" n-enodes-1 n-eclasses-1))
      (and (= n-enodes n-enodes-1) (= n-eclasses n-eclasses-1)
           ;; If some rules are still banned, continue till they reactivate
           (or (not backoff-state)
               (zerop (hash-table-count (backoff-state-ban-until-table backoff-state))))))))
