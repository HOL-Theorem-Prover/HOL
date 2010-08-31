;;; Translate a file of defuns into readable defp forms.  We want to translate
;;; first both as a sanity check on the input and to be sure that we have
;;; proper internal form; and then we untranslate into pretty user-level
;;; syntax.

;;; For simplicity, our implementation loads the input file first in order to
;;; get ACL2 to know about the new names.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; INSTRUCTIONS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; BEFORE USE, start ACL2 and certify this book in this directory:

;;; (certify-book "untranslate-file")

;;; FOR EACH USE, start ACL2 and do the following.

;;; 1. Include this book:

;;; (include-book "untranslate-file")

;;; 2. Include the necessary books before running this tool, e.g.:

;;; (include-book "models/jvm/m1/m1-story" :dir :system)

;;; 3. Then run the tool with specified input file to read, output file to write,
;;;    and the package into which to write the output file.  For example:

;;; (untranslate-file "fact.lisp" "fact-out.lisp" "M1")

;;; 4. Optionally, as a sanity check, restart ACL2 and certify the resulting
;;;    book, after including the book from step 2.  For example:

;;; (include-book "models/jvm/m1/m1-story" :dir :system)
;;; (certify-book "fact-out" ?)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(in-package "ACL2")

(program)
(set-state-ok t)

(mutual-recursion

(defun merge-lets-lst (form)
  (cond ((atom form) form)
        (t (cons (merge-lets (car form) nil)
                 (merge-lets-lst (cdr form))))))

(defun merge-lets (form bindings)

; Warning: This is a hack, as it operates on untranslated forms, which might
; have macro calls!  But in our intended application, we expect only harmless
; macros (like append, and, etc.).

; Form is an untranslated form.  We feel secure in replacing repeated (let
; ((var val)) ...) by let*, provided there are no declare forms and a unique
; variable bound each time.

  (case-match form
    (('let ((var val)) body)
     (merge-lets body (cons (list var val) bindings)))
    (&
     (let ((new-form (cond ((atom form) form)
                           (t (cons (car form)
                                    (merge-lets-lst (cdr form)))))))
       (cond ((cdr bindings)
              `(let* ,(reverse bindings)
                 ,new-form))
             (bindings
              `(let (,(car bindings))
                 ,new-form))
             (t new-form))))))

)

(defun untranslate-form (form ctx wrld)
  (case-match form
    (('defun fn args . &)
     `(defp ,fn ,args
        ,(merge-lets (untranslate
                      (getprop fn 'unnormalized-body
                               '(:error "translate-form didn't find a value.")
                               'current-acl2-world wrld)
                      nil wrld)
                     nil)))
    (&
     (er hard ctx
         "Unrecognized form (expected (defun ...): ~x0"
         form))))

(defun untranslate-form-lst (lst ctx wrld acc)
  (cond ((endp lst)
         (reverse acc))
        (t (untranslate-form-lst (cdr lst) ctx wrld
                                 (cons (untranslate-form (car lst) ctx wrld)
                                       acc)))))

(defun set-current-package-state (val state)
  (mv-let (erp val state)
          (set-current-package val state)
          (declare (ignore val))
          (cond (erp (prog2$ (er hard 'set-current-package-state
                                 "Aborting")
                             state))
                (t state))))

(defun pprint-objects (lst ch state)
  (cond ((null lst) state)
        (t (pprogn (fms "~x0~|" (list (cons #\0 (car lst))) ch state nil)
                   (pprint-objects (cdr lst) ch state)))))

(defun untranslate-file1 (infile outfile pkg state)
  (let ((ctx 'untranslate-file))
    (state-global-let*
     ((current-package pkg set-current-package-state))
     (er-let*
      ((forms (read-file infile state)))
      (mv-let (chan state)
              (open-output-channel outfile :object state)
              (cond ((null chan)
                     (er soft ctx
                         "Unable to write to ~x0"
                         outfile))
                    (t
                     (pprogn
                      (fms "(in-package ~x0)~|" (list (cons #\0 pkg)) chan
                           state nil)
                      (pprint-objects
                       (list* '(include-book "misc/defp" :dir :system)
                              (untranslate-form-lst forms ctx (w state) nil))
                       chan state)
                      (close-output-channel chan state)
                      (value (list :written-to outfile))))))))))

(defmacro untranslate-file (infile outfile pkg)
  `(ld '((program)
         (ld ,infile)
         (untranslate-file1 ,infile ,outfile ,pkg state))))
