(in-package :ggs/eqsat)

(defun build-term (enode selections)
  (let ((memo (make-hash-table)))       ; used to preserve sharing
    (labels ((process (class)
               (case (gethash class memo)
                 (visiting (error "Cycle"))
                 ((nil)
                  (setf (gethash class memo) 'visiting)
                  (setf (gethash class memo)
                        (let ((enode (gethash class selections)))
                          (if (plusp (enode-n-args enode))
                              (cons (enode-fsym enode) (map-enode-args #'process enode))
                              (enode-fsym enode)))))
                 (t (gethash class memo)))))
      (process (enode-find enode)))))

(defun graph-cost (enode selections cost-fn)
  (let ((memo (make-hash-table))
        (cost 0))
    (labels ((process (class)
               (ensure-gethash
                class memo
                (let ((enode (gethash class selections)))
                  (incf cost (funcall cost-fn enode))
                  (do-enode-args (arg enode)
                    (process arg))
                  t))))
      (process (enode-find enode))
      cost)))

(defun tree-cost (enode selections cost-fn)
  (let ((memo (make-hash-table)))
    (labels ((process (class)
               (ensure-gethash
                class memo
                (let ((enode (gethash class selections))
                      (cost (funcall cost-fn enode)))
                  (do-enode-args (arg enode cost)
                    (incf cost (process arg)))))))
      (process (enode-find enode)))))

(defun greedy-select (cost-fn)
  (let ((costs (make-hash-table))        ; map eclass to cost
        (selections (make-hash-table)))  ; map eclass to enode
    (loop
      (let (dirty)
        (dolist (class (egraph-class-list *egraph*))
          (let ((selection (gethash class selections))
                (cost (gethash class costs)))
            (dolist (enode (list-enodes class))
              (let ((new-cost
                      (funcall cost-fn enode
                               (map-enode-args (rcurry #'gethash costs)
                                               enode))))
                (when (if cost (and new-cost (< new-cost cost))
                          new-cost)
                  (setf selection enode
                        cost new-cost
                        dirty t))))
            (setf (gethash class selections) selection
                  (gethash class costs) cost)))
        (unless dirty (return))))
    (values selections costs)))

(defun greedy-extract (enode cost-fn)
  "Greedy extract a term for ENODE from `*egraph*' using COST-FN.

COST-FN should accept 2 arguments: the enode and a list of costs for each
argument eclass. It should return a number. The cost of an extraction is the
cost of its root node."
  (build-term enode (greedy-select cost-fn)))

(defun lp-select (enode cost-fn)
  (let ((class-vars (make-hash-table))  ; map eclass to lp var or 'visiting
        (enode-vars (make-hash-table))
        (objective-terms nil)
        (constraints nil))
    (labels ((visit-class (class)
               (ensure-gethash
                class class-vars
                (progn
                  ;; Mark the eclass as 'visiting to detect back edge from
                  ;; enode, so that we can ensure acyclicity
                  (setf (gethash class class-vars) 'visiting)
                  (lret ((var (gensym-1 'class)))
                    (push `(lp:<=
                            ,var
                            (lp:+ ,@ (remove-if #'not (mapcar #'visit-enode (list-enodes class)))))
                          constraints)))))
             (visit-enode (enode)
               ;; Return a lp var or NIL. NIL is returned if there's back edge
               ;; to a visiting eclass, therefore this enode is not processed
               (do-enode-args (class enode)
                 (when (eq (gethash class class-vars) 'visiting) (return-from visit-enode)))
               (lret ((cost (funcall cost-fn enode))
                      (var (gensym-1 (enode-fsym enode))))
                 (setf (gethash enode enode-vars) var)
                 (push `(lp:* ,cost ,var) objective-terms)
                 (do-enode-args (class enode)
                   (push `(lp:<= ,var ,(visit-class class)) constraints)))))
      (dolist (enode (ensure-list enode))
        (push `(lp:<= 1 ,(visit-class (enode-find enode))) constraints)))
    (lret ((solution
            (lp:solve-problem
             (lp:parse-linear-problem
              `(lp:min (lp:+ ,@objective-terms))
              `(,@constraints
                (lp:binary ,@ (hash-table-values class-vars))
                (lp:binary ,@ (hash-table-values enode-vars))))))
           (selections (make-hash-table)))
      (maphash
       (lambda (enode var)
         (when (plusp (lp:solution-variable solution var))
           (setf (gethash (enode-find enode) selections) enode)))
       enode-vars))))

(defun lp-extract (enode cost-fn)
  "Extract a term for ENODE from `*egraph*' using ILP.

COST-FN should accept 1 argument: the enode. It should return a number. The cost
of an extraction is the sum of costs of the enodes it contains. Note that
different from `greedy-extract', the cost model is implicitly additive."
  (build-term enode (lp-select enode cost-fn)))
