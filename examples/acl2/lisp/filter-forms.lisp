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

(defconst *events-to-skip*
  (cons
   'local
   (set-difference-eq
    *primitive-event-macros*

; Below is *primitive-event-macros*, but with those commented out that we know
; we can skip.

    '(
      defun
      #+:non-standard-analysis
      defun-std
      mutual-recursion
      defuns ; maybe don't really care, though
      defthm
      #+:non-standard-analysis
      defthm-std
      defaxiom
;     defconst ; ok to skip because it's translated away
      defstobj
      defpkg ; not actually in *primitive-event-macros*
;     deflabel
;     defdoc
;     deftheory
      defchoose
;     verify-guards
      defmacro
;     in-theory
;     in-arithmetic-theory
;     push-untouchable
;     table
      encapsulate
      include-book
;     theory-invariant
      verify-termination
      logic
      program
;     add-default-hints!
;     add-match-free-override
      add-include-book-dir
      delete-include-book-dir
;     remove-default-hints!
;     set-match-free-default
;     set-enforce-redundancy
;     set-verify-guards-eagerness
;     set-non-linearp
;     set-compile-fns
;     set-measure-function
;     set-well-founded-relation
;     set-invisible-fns-table
;     set-backchain-limit
;     set-bogus-mutual-recursion-ok
;     set-irrelevant-formals-ok
;     set-ignore-ok
;     set-inhibit-warnings
;     set-state-ok
;     set-let*-abstractionp
;     set-nu-rewriter-mode
;     set-case-split-limitations
;     set-default-hints!
;     set-rewrite-stack-limit
;     comp
      ))))

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
                             (if (and (eq (car form) 'encapsulate)
                                      (cadr form))
                                 (value (cons form acc)) ; just punt
                               (er-let* ((defs (expand-forms
                                                (if (eq (car form)
                                                        'encapsulate)
                                                    (cddr form)
                                                  (cdr form))
                                                nil
                                                untrans-flg
                                                basic-only
                                                state)))
                                        (value
                                         (cond
                                          ((null defs) ; expect basic-only
                                           acc)
                                          ((eq (car form) 'encapsulate)
                                           (append defs acc))
                                          (t
                                           (cons (cons (car form)
                                                       (reverse defs))
                                                 acc)))))))
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
                            (t (if (member-eq (car form)
                                              *events-to-skip*)
                                   (value acc)
                                 (value (cons form acc))))))))))
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
