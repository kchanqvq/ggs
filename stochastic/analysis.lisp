(in-package :ggs/stochastic)

(defun expand-analysis (offset analysis category subject)
  ;; MERGE-FORM rather than MERGE's value: the value (a function object) can't
  ;; be dumped by PRECOMPILE-STOCHASTIC-RULE-SET, and the form lets it inline.
  (bind (((:plist merge-form bottom type clauses) analysis))
    `(let ((result ',bottom))
       (declare (type ,type result))
       (do-match* ,offset ,category ,subject
         ,@(mapcar (lambda (clause)
                     `(,(car clause)
                       (setf result (funcall ,merge-form result (locally ,@(cdr clause))))))
                   clauses))
       result)))

(defun expand-analysis-access (offset name analyses-alist subject env)
  (let* ((subject (term-form-from-env subject env))
         (index (or (position name analyses-alist :key #'car)
                    (error "Analysis ~S not present." name)))
         (analysis (assoc-value analyses-alist name)))
    (if (term-form-p subject)
        (expand-analysis offset analysis t subject)
        `(the ,(getf analysis :type)
              (if (rose-node-p ,subject)
                  (svref ,subject (+ +rose-node-args-offset+ ,index))
                  ,(expand-analysis offset analysis 'constant subject))))))
