(in-package :ggs/eqsat)

(defun compute-analysis-clause (fsym clauses merge)
  `((,fsym)
    ,@(when (var-p fsym) `((declare (ignorable ,fsym))))
    ,@(mapcar
       (lambda (clause)
         (bind ((body (cdr clause))
                ((fsym-1 . args) (ensure-list (car clause))))
           (assert (eql fsym-1 fsym))
           (labels ((process (args i)
                      (if args
                          (if (var-p (car args))
                              `(let ((,(car args) (enode-arg ,i top-enode)))
                                 (declare (ignorable ,(car args)))
                                 ,(process (cdr args) (1+ i)))
                              `(let ((arg-enode (enode-arg ,i top-enode)))
                                 (declare (ignorable arg-enode))
                                 ,(expand-match
                                   (list 'arg-enode) (parse-pattern (car args) 'arg-enode)
                                   (process (cdr args) (1+ i)))))
                          `(setf result (funcall ,merge result (locally ,@body))))))
             `(when (= (enode-n-args top-enode) ,(length args))
                ,(process args 0)))))
       clauses)))

(defun compute-make-lambda (merge bottom type clauses)
  (bind (((:values var-clauses fsym-clauses) (partition #'var-p clauses :key #'car))
         (clauses-by-fsym (assort fsym-clauses :key (compose #'ensure-car #'car))))
    `(lambda (top-enode)
       (macrolet ((get-analysis-data (name enode)
                    `(the ,(getf (get-analysis name) :type)
                          (enode-analysis-data ',name ,enode))))
         (let ((result ,bottom))
           (declare (type ,type result))
           ,@(mapcar (lambda (clause)
                       `(let ((,(car clause) top-enode))
                          (declare (ignorable ,(car clause)))
                          (setf result (funcall ,merge result (locally ,@(cdr clause))))))
                     (nreverse var-clauses))
           (case/bind (enode-fsym top-enode)
             ,@(mapcar
                (lambda (clauses)
                  (compute-analysis-clause (ensure-car (caar clauses)) clauses merge))
                clauses-by-fsym))
           result)))))

(defparameter *compiled-makes* (make-hash-table :test 'equal))

(defun compiled-analysis (name)
  (bind (((:plist merge-form bottom clauses type) (get-analysis name))
         (merge (eval merge-form)))
    (make-analysis-info
     :name name :merge merge :bottom bottom
     :make (ensure-gethash (list merge bottom type clauses) *compiled-makes*
                           (compile nil (compute-make-lambda merge bottom type clauses))))))
