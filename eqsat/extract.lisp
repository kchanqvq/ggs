(in-package :ggs/eqsat)

(defun build-term (enode selections)
  (memo-labels ((process (class)
                  (let ((enode (gethash class selections)))
                    (if (plusp (enode-n-args enode))
                        (cons (enode-fsym enode) (map-enode-args #'process enode))
                        (enode-fsym enode)))))
    (process (enode-find enode))))

;; FIXME: The extraction functions can take analysis not in `*egraph*', as long
;; as they don't *use* analysis not in `*egraph*' (including themselves! so they
;; cannot be recursive). This should either be fixed or documented.

(defun greedy-select (cost-analysis)
  (let ((analysis-make (analysis-info-make (compiled-analysis cost-analysis)))
        (selections (make-hash-table))) ; map eclass to enode
    (dolist (class (egraph-class-list *egraph*))
      (let (best-cost best-node)
        (loop for node in (eclass-info-nodes (enode-class-info class))
              for cost = (funcall analysis-make node)
              when (or (not best-cost) (and cost (< cost best-cost)))
                do (setf best-cost cost best-node node))
        (setf (gethash class selections) best-node)))
    selections))

(defun greedy-extract (enode cost-analysis)
  "Greedy extract a term for ENODE from `*egraph*' using COST-ANALYSIS."
  (build-term enode (greedy-select cost-analysis)))

(defun lp-select (enode weight-analysis)
  (let ((class-vars (make-hash-table))  ; map eclass to lp var or 'visiting
        (enode-vars (make-hash-table))
        (analysis-make (analysis-info-make (compiled-analysis weight-analysis)))
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
               (lret ((cost (funcall analysis-make enode))
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

(defun lp-extract (enode weight-analysis)
  "Extract a term for ENODE from `*egraph*' using ILP.

WEIGHT-ANALYSIS should compute the weight of each enode. Note that different
from `greedy-extract', the cost model is implicitly additive."
  (build-term enode (lp-select enode weight-analysis)))
