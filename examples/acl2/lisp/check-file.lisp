;;; Given a file, check that each of its forms is essentially redundant.  Here,
;;; "essentially redundant" means that they represent the same logical formula.
;;; Thus, we might include an ACL2 book and then check that the resulting
;;; round-trip file (created by ACL2 -> HOL/SEXP -> ACL2) contains only
;;; essentially redundant forms.

;;; Example use:
; (include-book "~/projects/HOL/examples/acl2/lisp/check-file")
; (include-book "~/projects/HOL/examples/acl2/tests/inputs/pkg-test")
; (check-file "~/Downloads/pkg_test.lisp")

(in-package "ACL2")

(program)
(set-state-ok t)

(mutual-recursion

(defun fold-conses (term)
  (cond ((or (variablep term)
             (fquotep term))
         term)
        (t (let ((args (fold-conses-lst (fargs term))))
             (cond ((and (eq (ffn-symb term) 'cons)
                         (quotep (car args))
                         (quotep (cadr args)))
                    (kwote (cons (unquote (car args))
                                 (unquote (cadr args)))))
                   ((flambdap (ffn-symb term))
                    (cons-term (make-lambda
                                (lambda-formals (ffn-symb term))
                                (fold-conses-lst
                                 (lambda-body (ffn-symb term))))
                               args))
                   (t (cons-term (ffn-symb term)
                                 args)))))))

(defun fold-conses-lst (x)
  (cond ((endp x) nil)
        (t (cons (fold-conses (car x))
                 (fold-conses-lst (cdr x))))))
)

(defun check-form (form ctx wrld state)
  (case-match form
    (('defun fn args . rest)
     (cond
      ((not (equal args (formals fn wrld)))
       (er soft ctx
           "Formals mismatch for ~X01"
           fn nil))
      (t
       (er-let*
           ((x (translate (car (last rest))
                          t   ; stobjs-out
                          t   ; logic-modep
                          nil ; known-stobjs
                          ctx wrld state)))
         (cond ((equal
                 (fold-conses x)
                 (fold-conses
                  (getprop fn 'unnormalized-body
                           '(:error "translate-form didn't find a value.")
                           'current-acl2-world wrld)))
                (value nil))
               (t
                (er soft ctx
                    "Body mismatch for ~x0.~%Loaded:~|~Y12~|File:~|~Y32~|"
                    fn
                    (fold-conses
                     (getprop fn 'unnormalized-body
                              '(:error "translate-form didn't find a value.")
                              'current-acl2-world wrld))
                    nil
                    (fold-conses x))))))))
    (('defthm name body . &)
     (er-let*
         ((x (translate body
                        t     ; stobjs-out
                        t     ; logic-modep
                        nil   ; known-stobjs
                        ctx wrld state)))
       (cond ((equal (fold-conses x)
                     (fold-conses
                      (getprop name 'theorem
                               '(:error "translate-form didn't find a value.")
                               'current-acl2-world wrld)))
              (value nil))
             (t
              (er soft ctx
                  "Body mismatch for ~x0.~%Loaded:~|~Y12~|File:~|~Y32~|"
                  name
                  (fold-conses
                   (getprop name 'theorem
                            '(:error "translate-form didn't find a value.")
                            'current-acl2-world wrld))
                  nil
                  (fold-conses x))))))
    (('in-package . &)
     (value nil))
    (&
     (er soft ctx
         "Unrecognized form (expected (defun ...): ~x0"
         form))))

(defun check-form-lst (lst ignore-errors ctx wrld state)
  (cond ((endp lst)
         (value nil))
        (t (mv-let (erp val state)
                   (check-form (car lst) ctx wrld state)
                   (declare (ignore val))
                   (cond ((and erp (not ignore-errors))
                          (silent-error state))
                         (t (check-form-lst (cdr lst) ignore-errors ctx wrld
                                            state)))))))

(defun check-file1 (infile ignore-errors state)
  (let ((ctx 'check-file)
        (wrld (w state)))
    (er-let*
        ((forms (read-file infile state)))
      (check-form-lst forms ignore-errors ctx wrld state))))

(defmacro check-file (infile &optional (show-all 't))
  `(check-file1 ,infile ,show-all state))
