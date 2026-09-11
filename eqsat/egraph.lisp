(in-package :ggs/eqsat)

(define-variadic-structure eclass-info
  "Metadata for the eclass.

Should only appear in reprensetative enode's PARENT slot.

NODES and PARENTS only store canonical enodes after `egraph-rebuild'."
  (n-parents 0 :type fixnum)
  (parents nil :type list)
  (nodes nil :type list)
  ((datum data)))

(define-variadic-structure enode
  "PARENT is either another enode in the same eclass, or an `eclass-info' if this
enode is the representative of its own eclass.

Set CANONICAL-FLAG to NIL to mark the node as non-canonical. `egraph-rebuild'
trusts this information to avoid testing all term arguments for
representativeness."
  (parent)
  (flags 3 :type fixnum)
  (hash-code 0 :type fixnum)
  (fsym)
  (arg))

(defmacro enode-canonical-flag (enode)
  `(ldb (byte 1 0) (enode-flags ,enode)))

;; Be aware that representative enode might be non-canonical!
(defmacro enode-representative-flag (enode)
  `(ldb (byte 1 1) (enode-flags ,enode)))

(defun enode-canonical-p (enode)
  "This doesn't trust CANONICAL-FLAG, for sanity check."
  (do-enode-args (arg enode t)
    (unless (plusp (enode-representative-flag arg)) (return))))

(declaim (inline term-equal))
(defun term-equal (x y)
  (declare (optimize speed (safety 0)))
  (unless (and (eql (enode-fsym x) (enode-fsym y))
               (= (length x) (length y)))
    (return-from term-equal nil))
  (loop for i from +enode-args-offset+ below (length x)
        always (eq (svref x i) (svref y i))))

(declaim (inline term-hash))
(defun term-hash (x)
  (declare (optimize speed (safety 0)))
  (let ((hash (sxhash (enode-fsym x)))
        (mul (logand 3622009729038463111 most-positive-fixnum))
        (xor (logand 608948948376289905 most-positive-fixnum)))
    (declare (type non-negative-fixnum hash))
    (do-enode-args (arg x)
      (setq hash (logand (+ hash (* (enode-hash-code arg) mul)) most-positive-fixnum))
      (setq hash (logand (logxor xor hash (ash hash -5)) most-positive-fixnum)))
    hash))

(lp-hash-table:define-hash-set hash-cons enode-hash-code term-equal)

(declaim (inline enode-eclass-info
                 make-analysis-data merge-analysis-data modify-analysis-data
                 get-analysis-data egraph-n-enodes egraph-n-eclasses))

(defun enode-eclass-info (enode)
  (enode-parent (enode-find enode)))

(defstruct fsym-info
  "Index data for specific function symbol.

NODES store all enodes with this function symbol.

NODE-TABLE maps eclasses (i.e. representative enodes) to member enodes with this
function symbol."
  (nodes nil :type list)
  (node-table (make-hash-table :test 'eq) :type hash-table))

(defvar *analysis-info-registry* (trivial-garbage:make-weak-hash-table))

(defstruct analysis-info
  "Data for e-analysis."
  (name (required-argument :name) :type symbol)
  (make (required-argument :make) :type (function (enode) t))
  (merge (required-argument :merge) :type function)
  (modify (required-argument :modify) :type function))

(defmacro define-analysis (name &key make merge (modify '(constantly nil)))
  `(progn
     (setf (gethash ',name *analysis-info-registry*)
           (make-analysis-info :name ',name :make ,make :merge ,merge :modify ,modify))
     (declaim (inline name))
     (defun ,name (enode) (get-analysis-data enode ',name))))

(defstruct (egraph (:constructor make-egraph (&key analyses)))
  "HASH-CONS stores all canonical enodes. CLASSES stores all
eclass (i.e. representative enodes). FSYM-TABLE stores a `fsym-info' entry for
every encountered function symbol.

CLASSES and FSYM-TABLE are only up-to-date after `egraph-rebuild'."
  (hash-cons (make-hash-cons) :type hash-cons)
  (classes (make-hash-table :test 'eq) :type hash-table)
  (fsym-table (make-hash-table) :type hash-table)
  (work-list nil :type list)
  (analysis-info-list
   (mapcar (lambda (name) (or (gethash name *analysis-info-registry*)
                              (error "No analysis named ~a." name)))
           (ensure-list analyses))
   :type list)
  (analysis-work-list nil :type list))

(defvar *egraph*)
(setf (documentation '*egraph* 'variable) "Current egraph under operation.")

(-> enode-find (enode) enode)
(defun enode-find (enode)
  (if (plusp (enode-representative-flag enode))
      enode
      (let ((parent (enode-parent enode)))
        (loop
          (when (plusp (enode-representative-flag parent))
            (return parent))
          (let ((grandparent (enode-parent parent)))
            (psetf (enode-parent enode) grandparent
                   parent grandparent
                   enode parent))))))

(defun make-analysis-data (eclass-info enode)
  (let ((analysis-info-list (egraph-analysis-info-list *egraph*)))
    (dotimes (i (eclass-info-n-data eclass-info))
      (setf (eclass-info-datum i eclass-info)
            (funcall (analysis-info-make (pop analysis-info-list)) enode)))))

(defun merge-analysis-data (eclass new-class-info)
  (let* ((data-changed nil)
         (class-info (enode-parent eclass)))
    (loop for analysis-info in (egraph-analysis-info-list *egraph*)
          for i from +eclass-info-data-offset+ below (length class-info)
          for old-data = (svref class-info i)
          for new-data = (funcall (analysis-info-merge analysis-info)
                                  old-data (svref new-class-info i))
          do (setf (svref class-info i) new-data
                   data-changed (or data-changed (not (eq old-data new-data)))))
    (when data-changed
      (push eclass (egraph-analysis-work-list *egraph*)))))

(defun modify-analysis-data (eclass)
  (let ((analysis-info-list (egraph-analysis-info-list *egraph*)))
    (do-eclass-info-data (datum (enode-parent eclass))
      (funcall (analysis-info-modify (pop analysis-info-list)) eclass datum)
      ;; modify hook might make ECLASS no longer representative
      (setf eclass (enode-find eclass)))))

(-> get-analysis-data (enode symbol) t)
(defun get-analysis-data (enode name)
  (eclass-info-datum (or (position name (egraph-analysis-info-list *egraph*) :key #'analysis-info-name)
                         (error "Analysis ~a missing from egraph." name))
                     (enode-eclass-info enode)))

(-> intern-enode (enode) enode)
(defun intern-enode (key-node)
  (do-enode-args ((arg i) key-node)
    (setf (enode-arg i key-node) (enode-find arg)))
  (let ((hc (egraph-hash-cons *egraph*))
        (hash (term-hash key-node)))
    (setf (enode-hash-code key-node) hash)
    ;; Probe with the (dynamic-extent) KEY-NODE; only cons a real enode on miss.
    (or (hash-cons-get key-node hc)
        (lret ((eclass-info (make-array (+ +eclass-info-data-offset+
                                           (length (egraph-analysis-info-list *egraph*)))
                                        :initial-element 'unbound))
               (enode (copy-seq key-node)))
          (setf (eclass-info-n-parents eclass-info) 0
                (eclass-info-parents eclass-info) nil
                (eclass-info-nodes eclass-info) (list enode)
                (enode-parent enode) eclass-info)
          (do-enode-args (arg enode)
            (push enode (eclass-info-parents (enode-parent arg)))
            (incf (eclass-info-n-parents (enode-parent arg))))
          (hash-cons-put enode hc)
          (make-analysis-data eclass-info enode)
          (modify-analysis-data enode)))))

(defun make-enode (fsym &rest args)
  (let ((key-node (apply #'vector nil 3 0 fsym args)))
    (declare (dynamic-extent key-node))
    (intern-enode key-node)))

(-> enode-merge (enode enode) null)
(defun enode-merge (x y)
  (let ((x (enode-find x))
        (y (enode-find y)))
    (unless (eq x y)
      (let ((px (enode-parent x))
            (py (enode-parent y)))
        (when (< (eclass-info-n-parents px)
                 (eclass-info-n-parents py))
          (rotatef x y)
          (rotatef px py))
        (dolist (parent (eclass-info-parents py))
          (when (plusp (enode-canonical-flag parent))
            (setf (enode-canonical-flag parent) 0)
            (push parent (egraph-work-list *egraph*))))
        (setf (eclass-info-nodes px)
              (nreconc (eclass-info-nodes py) (eclass-info-nodes px))
              (enode-parent y) x
              (enode-representative-flag y) 0)
        (merge-analysis-data x py)
        (modify-analysis-data x)
        nil))))

(defun egraph-rebuild (&key prune-constant)
  ;; Upward propagation

  ;; Note: we allow duplicates in `egraph-work-list'. Currently we don't bother
  ;; `remove-duplicate' beforehand because doing such seem to actually slow
  ;; things down a bit.
  (loop
    (let ((enode (pop (egraph-work-list *egraph*))))
      (unless enode (return))
      (hash-cons-rem enode (egraph-hash-cons *egraph*))
      (enode-merge
       (let ((key-node (copy-seq enode)))
         (declare (dynamic-extent key-node))
         (setf (enode-parent key-node) nil
               (enode-flags key-node) 3)
         (intern-enode key-node))
       enode)))
  ;; Update analysis
  (loop
    (let ((enode (pop (egraph-analysis-work-list *egraph*))))
      (unless enode (return))
      (when (plusp (enode-representative-flag enode))
        (let ((info (enode-parent enode)))
          (dolist (parent (eclass-info-parents info))
            (when (plusp (enode-canonical-flag parent))
              (let ((new-class-info (make-array (+ +eclass-info-data-offset+
                                                   (length (egraph-analysis-info-list *egraph*)))
                                                :initial-element 'unbound))
                    (eclass (enode-find parent)))
                (declare (dynamic-extent new-class-info))
                (make-analysis-data new-class-info parent)
                (merge-analysis-data eclass new-class-info)
                (modify-analysis-data eclass))))))))
  ;; Build eclass index by collecting all representative enodes of canonical
  ;; enodes in `egraph-hash-cons'. Note we really need to `enode-find' here,
  ;; because canon-enodes might be non-rep, while rep-enodes might not be canon
  ;; thus not appear in `egraph-hash-cons' either so we can't simply test for
  ;; `enode-representative-flag'.
  (clrhash (egraph-classes *egraph*))
  (map-hash-cons (lambda (node)
                   (setf (gethash (enode-find node) (egraph-classes *egraph*)) t))
                 (egraph-hash-cons *egraph*))
  ;; Build various node index. We used to also prune non-canonical enodes from
  ;; eclass-info-parents here, but not doing it seems faster
  (clrhash (egraph-fsym-table *egraph*))
  (maphash-keys (lambda (class)
                  (let ((info (enode-parent class)))
                    (setf (eclass-info-nodes info)
                          (delete-if-not (lambda (n) (plusp (enode-canonical-flag n))) (eclass-info-nodes info)))
                    (when prune-constant
                      (dolist (node (eclass-info-nodes info))
                        (when (funcall prune-constant (enode-fsym node))
                          (setf (eclass-info-nodes info) (list node))
                          (return))))
                    (dolist (node (eclass-info-nodes info))
                      (let ((fsym-info (ensure-gethash (enode-fsym node) (egraph-fsym-table *egraph*)
                                                       (make-fsym-info))))
                        (push node (gethash class (fsym-info-node-table fsym-info)))
                        (push node (fsym-info-nodes fsym-info))))))
                (egraph-classes *egraph*)))

;;; Utils

(defun hash-table-keys-difference (table-1 table-2)
  (let ((results nil))
    (maphash-keys (lambda (class)
                    (unless (gethash class table-2)
                      (push class results)))
                  table-1)
    results))

(defun check-egraph ()
  "Various sanity check."
  (declare (optimize (debug 3)))
  (let ((classes (make-hash-table))
        (n-parent-list 0)
        (n-parent-list-distinct 0)
        (n-parent-list-non-canonical 0))
    (map-hash-cons (lambda (node)
                     (setf (gethash (enode-find node) classes) t))
                   (egraph-hash-cons *egraph*))
    (format t "~&There're ~a eclasses.~%" (hash-table-count classes))
    (when-let (diff (hash-table-keys-difference classes (egraph-classes *egraph*)))
      (error "Missing eclasses:~% ~a" diff))
    (when-let (diff (hash-table-keys-difference (egraph-classes *egraph*) classes))
      (error "Extra eclasses:~% ~a" diff))
    (dolist (class (hash-table-keys classes))
      (let ((nodes (list-enodes class)))
        (dolist (node nodes)
          (if (enode-canonical-p node)
              (do-enode-args (arg node)
                (unless (member node (eclass-info-parents (enode-parent arg)))
                  (error "Missing parent link from ~a to ~a" arg node)))
              (error "Non canonical node ~a on ~a's node list" node class)))
        (unless (= (length nodes)
                   (length (remove-duplicates nodes :test 'term-equal)))
          (warn "Duplicates in ~a's enodes:~% ~a" class nodes)))
      (let ((parents (eclass-info-parents (enode-parent class))))
        (dolist (node parents)
          (if (enode-canonical-p node)
              (unless (do-enode-args (arg node)
                        (when (eq class arg) (return t)))
                (error "Extra parent link from ~a to ~a" class node))
              ;; We allow non-canonical enodes in parent list (and ignore them)
              (incf n-parent-list-non-canonical)))
        ;; Currently we allow duplicates in parent list
        (incf n-parent-list (length parents))
        (incf n-parent-list-distinct (length (remove-duplicates parents)))))
    (unless (zerop n-parent-list-non-canonical)
      (format t "~a/~a (~,2$%) elements in parent list are non-canonical.~%"
              n-parent-list-non-canonical n-parent-list (* 100 (/ n-parent-list-non-canonical n-parent-list))))
    (let ((n-dup (- n-parent-list n-parent-list-distinct)))
      (unless (zerop n-dup)
        (format t "~a/~a (~,2$%) elements in parent list are duplicates.~%"
                n-dup n-parent-list (* 100 (/ n-dup n-parent-list)))))))

(defun list-enodes (enode)
  "List of enodes equivalent to ENODE.

Only contains canonical enodes after `egraph-rebuild'."
  (eclass-info-nodes (enode-eclass-info enode)))

(defun egraph-n-enodes (egraph)
  (hash-cons-count (egraph-hash-cons egraph)))

(defun egraph-n-eclasses (egraph)
  (hash-table-count (egraph-classes egraph)))
