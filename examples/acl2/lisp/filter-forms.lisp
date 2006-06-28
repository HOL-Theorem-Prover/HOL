(in-package "ACL2")

; To run this on axioms.lisp:
; (include-book "filter-forms")
; :q
; (setf (cadr (assoc 'global-value (get 'untouchables *current-acl2-world-key*))) nil)
; (lp!)
; (write-forms "<dir>/axioms.lisp" "defaxioms.lisp.trans" nil state)
; (write-forms "<dir>/axioms.lisp" "defaxioms.lisp.untrans" t state)

(program)
(set-state-ok t)

(include-book "misc/file-io" :dir :system)

; In what follows, basic-only means that we only want defaxiom, defthm, and
; logic-mode defun forms, though we always allow input using progn and
; mutual-recursion.  We never expect to see local forms.

; Either way, we drop all hints.  That could be changed.

(defun expand-form (form untrans-flg basic-only state)
  (declare (xargs :guard (true-listp form)))
  (let* ((wrld (w state))
         (event-type (car form))
         (body (case event-type
                 ((defun defund) (car (last form)))
                 ((defaxiom defthm) (third form)))))
    (er-let* ((tbody (translate body t t t 'top-level wrld state)))
             (let ((new-body
                    (if untrans-flg
                        (untranslate tbody nil wrld)
                      tbody)))
               (value
                (case event-type
                  ((defun defund) (list 'defun
                                        (cadr form)
                                        (caddr form)
                                        new-body))
                  ((defaxiom defthm) (list event-type
                                           (cadr form)
                                           new-body))
                  (otherwise (and (not basic-only) form))))))))

(defun expand-forms (forms acc untrans-flg basic-only state)

; Result is in reverse order.

  (declare (xargs :guard (true-listp forms)))
  (if (endp forms)
      (value acc)
    (er-let* ((new-acc
               (let ((form (car forms)))
                 (cond ((atom form) (value acc))
                       (t (case (car form)
                            ((progn mutual-recursion encapsulate)
                             (let ((sub-forms (if (eq (car form) 'encapsulate)
                                                  (cddr form)
                                                (cdr form))))
                               (er-let* ((defs (expand-forms sub-forms nil
                                                             untrans-flg
                                                             basic-only
                                                             state)))
                                        (value
                                         (if (null defs) ; expect basic-only
                                             acc
                                           (append (reverse defs)
                                                   acc))))))
                            ((defaxiom defthm defun)
                             (if (and basic-only
                                      (eq (car form) 'defun)
                                      (eq (symbol-class (cadr form) (w state))
                                          :program))
                                 (value acc)
                               (er-let*
                                ((x (expand-form form untrans-flg basic-only
                                                 state)))
                                (value (cons x acc)))))
                            (t (value acc))))))))
             (expand-forms (cdr forms) new-acc untrans-flg basic-only state))))

(defun push-defuns-to-front (forms non-defuns defuns)

; Note: This also pushes progn to the end, even if there are theorems in the
; progn.  But for our intended application, we expect progn to disappear
; anyhow.

  (cond ((endp forms)
         (revappend defuns (reverse non-defuns)))
        ((and (consp (car forms))
              (member-eq (caar forms) '(defun mutual-recursion progn)))
         (push-defuns-to-front (cdr forms) non-defuns (cons (car forms) defuns)))
        (t
         (push-defuns-to-front (cdr forms) (cons (car forms) non-defuns) defuns))))

(defun write-forms (infile outfile untrans-flg state)
  (let ((ctx 'write-forms))
    (er-let* ((forms (read-list infile ctx state))
              (axioms (expand-forms forms nil untrans-flg t state)))
             (write-list (push-defuns-to-front (reverse axioms) nil nil) outfile ctx
                         state))))
