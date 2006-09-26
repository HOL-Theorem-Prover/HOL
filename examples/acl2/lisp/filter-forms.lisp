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
; logic-mode defun (and defund) forms, though we always allow input using
; progn, mutual-recursion, and encapsulate with nil signature.  We drop local
; forms.

; Either way, we drop all hints.  That could be changed.

(defun expand-form (form untrans-flg state)
  (declare (xargs :guard (true-listp form)))
  (let* ((wrld (w state))
         (event-type (car form))
         (body (case event-type
                 ((defun defund) (car (last form)))
                 ((defaxiom defthm defthmd) (third form)))))
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
                  ((defaxiom defthm defthmd) (list event-type
                                                   (cadr form)
                                                   new-body))
                  (otherwise (er hard 'expand-form
                                 "Unexpected form type: ~x0"
                                 form))))))))

(defun my-unparse-signature (x)

; Unlike built-in function unparse-signature, here we don't care about outputs,
; but we do care about all formals names.

  (let* ((fn (car x))
         (formals (cadr x)))
    `(,fn ,formals)))

(defun my-unparse-signature-lst (lst)
  (if (endp lst)
      nil
    (cons (my-unparse-signature (car lst))
          (my-unparse-signature-lst (cdr lst)))))

(defun expand-forms (forms acc untrans-flg basic-only ctx wrld state)

; Result is in reverse order.

  (declare (xargs :guard (true-listp forms)))
  (if (endp forms)
      (value acc)
    (er-let* ((new-acc
               (let ((form (car forms)))
                 (cond ((atom form) (value acc))
                       (t (case (car form)
                            (local (value acc))
                            ((progn mutual-recursion)
                             (er-let* ((defs (expand-forms (cdr form) nil
                                                           untrans-flg
                                                           basic-only
                                                           ctx wrld state)))
                                      (value
                                       (if (null defs) ; expect basic-only
                                           acc
                                         (cons (cons (car form)
                                                     (reverse defs))
                                               acc)))))
                            (encapsulate
                             (cond
                              ((null (cadr form))
                               (expand-forms (cddr form) acc untrans-flg
                                             basic-only ctx wrld state))
                              (t
                               (er-let*
                                ((pair
                                  (state-global-let*
                                   ((ld-redefinition-action
                                     '(:doit! . :overwrite)))
                                   (chk-signatures (cadr form) ctx wrld
                                                   state)))
                                 (forms (expand-forms (cddr form) nil untrans-flg
                                                      basic-only ctx wrld
                                                      state)))
                                (value (cons (list* 'encap
                                                    (my-unparse-signature-lst
                                                     (car pair))
                                                    (reverse forms))
                                             acc))))))
                            ((defaxiom defthm defthmd defun defund)
                             (if (and basic-only
                                      (member-eq (car form) '(defun defund))
                                      (eq (symbol-class (cadr form) (w state))
                                          :program))
                                 (value acc)
                               (er-let*
                                ((x (expand-form form untrans-flg state)))
                                (value (cons x acc)))))
                            (t (if basic-only
                                   (value acc)
                                 (value (cons form acc))))))))))
             (expand-forms (cdr forms) new-acc untrans-flg basic-only ctx wrld
                           state))))

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
              (axioms (expand-forms forms nil untrans-flg t ctx (w state) state)))
             (write-list (reverse axioms)
                         ;; (push-defuns-to-front (reverse axioms) nil nil)
                         outfile ctx state))))
