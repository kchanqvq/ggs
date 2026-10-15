(in-package :ggs/eqsat)

;; FIXME: currently, `fsym-index' is always an alist (no hash-table
;; promotion). This may fare badly if an eclass contain may different fsyms.
;; From what I've seen so far this is rare in practice.
(define-variadic-structure eclass-info
  "Metadata for the eclass.

FSYM-INDEX stores an alist of the form ((fsym . nodes) ...) for NODES after the
last `egraph-rebuild'. Matching must use the snapshot in FSYM-INDEX, as NODES
may be written between rebuilds by rule applications. NODES and PARENTS only
store canonical enodes after `egraph-rebuild'."
  (n-parents 0 :type fixnum)
  (parents nil :type list)
  (nodes nil :type list)
  (fsym-index nil :type list)
  ((datum data)))

;; Right now, we use vector representation for variadic structure that
;; internally pays 2 word overhead. Because SBCL double-word align objects, it
;; doesn't hurt to store an extra `class-info' to make 0/2-ary node (the most
;; common) have even number of slots -- it is free.
;;
;; I could abuse regular structure for variadic structure by setting a longer
;; `sb-kernel:%instance-length'. This has 1 word instead of 2 word overhead.
;; However, GC seems to scan it slower than `simple-vector'.
;;
;; In the future, if we go that route, it would be better to have an odd number
;; of slots. Ideas saved for that future:
;;
;; - Put real representative `class-info' on `parent', then Store merged-away
;; `class-info' in a separate EQ hash-table. This is often cheaper than you
;; would think because merged away eclass makes up a small portion.
;;
;; - Put both real and merged-away `class-info' on `parent'. In that case
;; we would want to path compress across merged-away `class-info' because
;; otherwise even regular enode pays for the longer path. Therefore, make
;; `class-info' have a parent pointer, and make it look like:
;;
;; merged-away-eclass -> class-info -> other-enode -> ... -> real-eclass-> class-info
;; other-enode -------------------------^

(define-variadic-structure (enode (:constructor %make-enode))
  "CLASS-INFO is the `eclass-info' of a representative enode. A representative
merged away since the last `egraph-rebuild' keeps its CLASS-INFO, for matches to
see its FSYM-INDEX.

FLAGS packs `enode-hash-code' above `+enode-flag-bits+' flag bits.

Set CANONICAL-FLAG to NIL to mark the node as non-canonical. `egraph-rebuild'
trusts this information to avoid testing all term arguments for
representativeness."
  (parent nil :type (or enode null))
  (class-info)
  (hash-code-and-flags 1 :type fixnum)
  (fsym)
  (arg))

(defconstant +enode-flag-bits+ 2)
(defconstant +enode-hash-bits+ 32)

(defmacro enode-hash-code (enode)
  `(ldb (byte +enode-hash-bits+ +enode-flag-bits+) (enode-hash-code-and-flags ,enode)))

(defmacro enode-canonical-flag (enode)
  `(ldb (byte 1 0) (enode-hash-code-and-flags ,enode)))

(declaim (inline enode-representative-p))
(defun enode-representative-p (enode)
  "Be aware that representative enode might be non-canonical!"
  (null (enode-parent enode)))

;; `egraph-rebuild' use this to deduplicate eclasses while scanning the hash
;; cons.
(defmacro eclass-seen-flag (enode)
  `(ldb (byte 1 1) (enode-hash-code-and-flags ,enode)))

(defun enode-canonical-p (enode)
  "This doesn't trust CANONICAL-FLAG, for sanity check."
  (do-enode-args (arg enode t)
    (unless (enode-representative-p arg) (return))))

(declaim (inline term-equal))
(-> term-equal (enode enode) boolean)
(defun term-equal (x y)
  (declare (optimize speed (safety 0)))
  (unless (and (eql (enode-fsym x) (enode-fsym y))
               (= (length x) (length y)))
    (return-from term-equal nil))
  (loop for i from +enode-args-offset+ below (length x)
        always (eq (svref x i) (svref y i))))

(declaim (inline term-hash))
(-> term-hash (enode) non-negative-fixnum)
(defun term-hash (x)
  (declare (optimize speed (safety 0)))
  (let ((hash (sxhash (enode-fsym x)))
        (mul (logand 3622009729038463111 most-positive-fixnum))
        (xor (logand 608948948376289905 most-positive-fixnum)))
    (do-enode-args (arg x)
      (setq hash (logand (+ hash (* (enode-hash-code arg) mul)) most-positive-fixnum))
      (setq hash (logand (logxor xor hash (ash hash -5)) most-positive-fixnum)))
    (ldb (byte +enode-hash-bits+ 0) hash)))

(declaim (inline hash-cons-get hash-cons-put))
(lp-hash-table:define-hash-set hash-cons enode-hash-code term-equal
  :optimize (speed (safety 0)))

(-> %enode-find (enode) enode)
(defun %enode-find (enode)
  "Slow path of `enode-find' when ENODE is not representative."
  (declare (optimize speed (safety 0)))
  (let ((parent (enode-parent enode)))
    (loop
      (let ((grandparent (enode-parent parent)))
        (unless grandparent (return parent))
        (psetf (enode-parent enode) grandparent
               parent grandparent
               enode parent)))))

(declaim (inline enode-find))
(defun enode-find (enode)
  (check-type enode enode)
  (if (enode-representative-p enode) enode (%enode-find enode)))

(declaim (inline make-analysis-data merge-analysis-data modify-analysis-data
                 get-analysis-data egraph-n-enodes egraph-n-eclasses))

(defvar *analysis-info-registry* (trivial-garbage:make-weak-hash-table))

(defstruct analysis-info
  "Data for e-analysis."
  (name (required-argument :name) :type symbol)
  (make (required-argument :make) :type (function (enode) t))
  (merge (required-argument :merge) :type function)
  (modify (required-argument :modify) :type function))

(defmacro define-analysis (name &key make merge (modify '(constantly nil)))
  ;; Define the accessor first: MAKE, MERGE and MODIFY may call it
  `(progn
     (declaim (inline ,name))
     (defun ,name (enode) (get-analysis-data enode ',name))
     (setf (gethash ',name *analysis-info-registry*)
           (make-analysis-info :name ',name :make ,make :merge ,merge :modify ,modify))))

(defstruct (egraph (:constructor make-egraph (&key analyses)))
  "HASH-CONS stores all canonical enodes. CLASS-LIST lists all
eclass (i.e. representative enodes) and N-ECLASSES is its length. FSYM-INDEX
maps every function symbol to a list of lists containing all enodes with it
(it is represented as a list of lists just to share structure with
`class-info-fsym-index', conceptually it stands for the flattened list).

CLASS-LIST, N-ECLASSES and FSYM-INDEX are only up-to-date after
`egraph-rebuild'."
  (hash-cons (make-hash-cons) :type hash-cons)
  (class-list nil :type list)
  (n-eclasses 0 :type fixnum)
  (fsym-index (make-hash-table) :type hash-table)
  (work-list nil :type list)
  (analysis-info-list
   (mapcar (lambda (name) (or (gethash name *analysis-info-registry*)
                              (error "No analysis named ~a." name)))
           (ensure-list analyses))
   :type list)
  (analysis-work-list nil :type list))

(defvar *egraph*)
(setf (documentation '*egraph* 'variable) "Current egraph under operation.")

(defun make-analysis-data (eclass-info enode)
  (let ((analysis-info-list (egraph-analysis-info-list *egraph*)))
    (dotimes (i (eclass-info-n-data eclass-info))
      (setf (eclass-info-datum i eclass-info)
            (funcall (analysis-info-make (pop analysis-info-list)) enode)))))

(defun merge-analysis-data (eclass new-class-info)
  (let* ((data-changed nil)
         (class-info (enode-class-info eclass)))
    (declare (type eclass-info class-info))
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
    (do-eclass-info-data (datum (enode-class-info eclass))
      (funcall (analysis-info-modify (pop analysis-info-list)) eclass datum)
      ;; modify hook might make ECLASS no longer representative
      (setf eclass (enode-find eclass)))))

(-> get-analysis-data (enode symbol) t)
(defun get-analysis-data (enode name)
  (eclass-info-datum (or (position name (egraph-analysis-info-list *egraph*) :key #'analysis-info-name)
                         (error "Analysis ~a missing from egraph." name))
                     (enode-class-info (enode-find enode))))

(declaim (inline canonicalize-key-node))
(defun canonicalize-key-node (key-node)
  (do-enode-args ((arg i) key-node)
    (unless (enode-representative-p arg)
      (setf (enode-arg i key-node) (%enode-find arg))))
  ;; Key nodes are canonical, with no other flag
  (setf (enode-hash-code-and-flags key-node)
        (logior (ash (term-hash key-node) +enode-flag-bits+) 1)))

(-> intern-enode (enode) enode)
(defun intern-enode (key-node)
  (declare (optimize speed (safety 0)))
  (canonicalize-key-node key-node)
  (let ((hc (egraph-hash-cons *egraph*)))
    ;; Probe with the (dynamic-extent) KEY-NODE; only cons a real enode on miss.
    (or (hash-cons-get key-node hc)
        (lret ((eclass-info (make-eclass-info
                             :n-parents 0 :parents nil :nodes nil
                             :n-args (length (egraph-analysis-info-list *egraph*))))
               (enode (copy-seq key-node)))
          (loop for i of-type fixnum from +eclass-info-data-offset+ below (length eclass-info)
                do (setf (svref eclass-info i) 'unbound))
          (setf (eclass-info-nodes eclass-info) (list enode)
                (enode-parent enode) nil
                (enode-class-info enode) eclass-info)
          (do-enode-args (arg enode)
            (push enode (eclass-info-parents (enode-class-info arg)))
            (incf (eclass-info-n-parents (enode-class-info arg))))
          (hash-cons-put enode hc)
          (make-analysis-data eclass-info enode)
          (modify-analysis-data enode)))))

(-> %intern-merge-enode (enode enode) null)
(defun %intern-merge-enode (eclass key-node)
  "Fusion of (enode-merge ECLASS (intern-enode KEY-NODE)).

Analysis modify hooks run only on ECLASS because KEY-NODE is never actually
interned."
  (declare (optimize speed (safety 0)))
  (canonicalize-key-node key-node)
  (let ((hc (egraph-hash-cons *egraph*)))
    (if-let (existing (hash-cons-get key-node hc))
      (%enode-merge eclass existing)
      (let* ((eclass (enode-find eclass))
             (info (enode-class-info eclass))
             (enode (copy-seq key-node)))
        (setf (enode-parent enode) eclass)
        (push enode (eclass-info-nodes info))
        (do-enode-args (arg enode)
          (push enode (eclass-info-parents (enode-class-info arg)))
          (incf (eclass-info-n-parents (enode-class-info arg))))
        (hash-cons-put enode hc)
        (when (egraph-analysis-info-list *egraph*)
          (let ((new-class-info (make-eclass-info
                                 :n-args (length (egraph-analysis-info-list *egraph*)))))
            (declare (dynamic-extent new-class-info))
            (make-analysis-data new-class-info enode)
            (merge-analysis-data eclass new-class-info)
            (modify-analysis-data eclass)))))))

(defun make-enode (fsym &rest args)
  (let ((key-node (%make-enode :fsym fsym :args args)))
    (declare (dynamic-extent key-node))
    (intern-enode key-node)))

(declaim (inline enode-merge))
(defun enode-merge (x y)
  "Merge the eclasses of enodes X and Y."
  (check-type x enode)
  (check-type y enode)
  (%enode-merge x y))

(-> %enode-merge (enode enode) null)
(defun %enode-merge (x y)
  (declare (optimize speed (safety 0)))
  (let ((x (enode-find x))
        (y (enode-find y)))
    (unless (eq x y)
      (let ((px (enode-class-info x))
            (py (enode-class-info y)))
        (when (< (eclass-info-n-parents px)
                 (eclass-info-n-parents py))
          (rotatef x y)
          (rotatef px py))
        (let ((g *egraph*))
          (dolist (parent (eclass-info-parents py))
            (when (plusp (enode-canonical-flag parent))
              (setf (enode-canonical-flag parent) 0)
              (push parent (egraph-work-list g)))))
        (setf (eclass-info-nodes px)
              (nreconc (eclass-info-nodes py) (eclass-info-nodes px))
              (enode-parent y) x)
        (merge-analysis-data x py)
        (modify-analysis-data x)
        nil))))

(defun egraph-rebuild (&key prune-constant)
  (declare (optimize speed (safety 0)))
  (check-type *egraph* egraph)
  (setf prune-constant (and prune-constant (ensure-function prune-constant)))

  ;; Upward propagation

  ;; Note: we allow duplicates in `egraph-work-list'. Currently we don't bother
  ;; `remove-duplicate' beforehand because doing such seem to actually slow
  ;; things down a bit.
  (loop
    (let ((enode (pop (egraph-work-list *egraph*))))
      (declare (type (or null enode) enode))
      (unless enode (return))
      (hash-cons-rem enode (egraph-hash-cons *egraph*))
      (%enode-merge
       (let ((key-node (copy-seq enode)))
         (declare (dynamic-extent key-node))
         (intern-enode key-node))
       enode)))

  ;; Update analysis
  (loop
    (let ((enode (pop (egraph-analysis-work-list *egraph*))))
      (unless enode (return))
      (when (enode-representative-p enode)
        (let ((info (enode-class-info enode)))
          (dolist (parent (eclass-info-parents info))
            (when (plusp (enode-canonical-flag parent))
              (let ((new-class-info (make-eclass-info
                                     :n-args (length (egraph-analysis-info-list *egraph*))))
                    (eclass (enode-find parent)))
                (declare (dynamic-extent new-class-info))
                (loop for i of-type fixnum from +eclass-info-data-offset+ below (length new-class-info)
                      do (setf (svref new-class-info i) 'unbound))
                (make-analysis-data new-class-info parent)
                (merge-analysis-data eclass new-class-info)
                (modify-analysis-data eclass))))))))

  ;; Build eclass index by collecting all representative enodes of canonical
  ;; enodes in `egraph-hash-cons'. Note we really need to `enode-find' here,
  ;; because canon-enodes might be non-rep, while rep-enodes might not be canon
  ;; thus not appear in `egraph-hash-cons' either so we can't simply test for
  ;; `enode-representative-p'.
  (let ((classes nil)
        (n-eclasses 0))
    (declare (type fixnum n-eclasses))
    (map-hash-cons (lambda (node)
                     (let ((class (enode-find node)))
                       ;; Clear merged-away eclass-info
                       (unless (eq class node)
                         (setf (enode-class-info node) nil))

                       (when (zerop (eclass-seen-flag class))
                         (setf (eclass-seen-flag class) 1)
                         (push class classes)
                         (incf n-eclasses))))
                   (egraph-hash-cons *egraph*))
    ;; make `egraph-class-list' match insertion order
    (setf (egraph-class-list *egraph*) (nreverse classes)
          (egraph-n-eclasses *egraph*) n-eclasses))

  ;; Build various node index. We used to also prune non-canonical enodes from
  ;; eclass-info-parents here, but not doing it seems faster
  (let ((fsym-index (egraph-fsym-index *egraph*)))
    (clrhash fsym-index)
    (dolist (class (egraph-class-list *egraph*))
      (setf (eclass-seen-flag class) 0)
      (let ((info (enode-class-info class))
            (alist nil))
        ;; Drop non-canonical enodes, preserving order
        (do* ((head (cons nil (eclass-info-nodes info)))
              (prev head)
              (cell (cdr prev) (cdr prev)))
             ((null cell)
              (setf (eclass-info-nodes info) (cdr head)))
          (declare (dynamic-extent head))
          (if (plusp (enode-canonical-flag (car cell)))
              (setq prev cell)
              (setf (cdr prev) (cdr cell))))

        (when prune-constant
          (dolist (node (eclass-info-nodes info))
            (when (funcall prune-constant (enode-fsym node))
              (setf (eclass-info-nodes info) (list node))
              (return))))

        (dolist (node (eclass-info-nodes info))
          (let* ((fsym (enode-fsym node))
                 (entry (or (assoc fsym alist) (car (push (list fsym) alist)))))
            (push node (cdr entry))))
        (setf (eclass-info-fsym-index info) alist)
        (loop for (fsym . nodes) in alist
              do (push nodes (gethash fsym fsym-index)))))))

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
    (let ((index (make-hash-table :test 'eq)))
      (dolist (class (egraph-class-list *egraph*))
        (setf (gethash class index) t))
      (unless (= (hash-table-count index) (egraph-n-eclasses *egraph*))
        (error "Duplicate eclasses in class list."))
      (unless (= (length (egraph-class-list *egraph*)) (egraph-n-eclasses *egraph*))
        (error "N-ECLASSES ~a disagrees with class list length ~a."
               (egraph-n-eclasses *egraph*) (length (egraph-class-list *egraph*))))
      (when-let (diff (hash-table-keys-difference classes index))
        (error "Missing eclasses:~% ~a" diff))
      (when-let (diff (hash-table-keys-difference index classes))
        (error "Extra eclasses:~% ~a" diff)))
    (dolist (class (hash-table-keys classes))
      (let ((nodes (list-enodes class)))
        (dolist (node nodes)
          (if (enode-canonical-p node)
              (do-enode-args (arg node)
                (unless (member node (eclass-info-parents (enode-class-info arg)))
                  (error "Missing parent link from ~a to ~a" arg node)))
              (error "Non canonical node ~a on ~a's node list" node class)))
        (unless (= (length nodes)
                   (length (remove-duplicates nodes :test 'term-equal)))
          (warn "Duplicates in ~a's enodes:~% ~a" class nodes)))
      (let ((parents (eclass-info-parents (enode-class-info class))))
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
  (eclass-info-nodes (enode-class-info (enode-find enode))))

(defun egraph-n-enodes (egraph)
  (hash-cons-count (egraph-hash-cons egraph)))
