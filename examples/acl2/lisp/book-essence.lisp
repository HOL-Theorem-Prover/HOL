(in-package "ACL2")

; In what follows, logic-only means that we only want events with logical
; content, such as defaxiom, defthm, and logic-mode defun (and defund) forms,
; but not including program-mode definitions, table events, etc.

; We drop local forms, regardless of logic-only.

; Either way, we drop all hints.  That could be changed.

(program)
(set-state-ok t)

(defun read-portcullis-cmds1 (chan cert-file ctx state acc)
  (mv-let (eofp form state)
          (read-object chan state)
          (cond (eofp (er soft ctx
                          "Reached end of file ~x0 before reaching ~
                           :END-PORTCULLIS-CMDS."
                          cert-file))
                ((eq form :END-PORTCULLIS-CMDS)
                 (if (eq acc :start)
                     (er soft ctx
                         "In file ~x0, reached :END-PORTCULLIS-CMDS before ~
                          reaching :BEGIN-PORTCULLIS-CMDS."
                          cert-file)
                   (value (reverse acc))))
                ((eq form :BEGIN-PORTCULLIS-CMDS)
                 (if (eq acc :start)
                     (read-portcullis-cmds1 chan cert-file ctx state nil)
                   (er soft ctx
                       "In file ~x0, reached :BEGIN-PORTCULLIS-CMDS twice."
                       cert-file)))
                ((eq acc :start)
                 (read-portcullis-cmds1 chan cert-file ctx state acc))
                (t (read-portcullis-cmds1 chan cert-file ctx state
                                          (cons form acc))))))

(defun read-portcullis-cmds (book-name cert-optional-p ctx state)
  (let ((cert-file (concatenate 'string
                                (extend-pathname (cbd) book-name state)
                                ".cert")))
    (mv-let (chan state)
            (open-input-channel cert-file :object state)
            (cond ((null chan)
                   (if cert-optional-p
                       (value nil)
                     (er soft ctx
                         "Unable to open certificate file ~x0."
                         cert-file)))
                  (t (mv-let
                      (erp forms state)
                      (read-portcullis-cmds1 chan cert-file ctx state :start)
                      (pprogn (close-input-channel chan state)
                              (cond (erp (mv erp forms state))
                                    (t (value forms))))))))))

(defun expand-to-event (form ctx state)
  (let ((orig-form form)
        (wrld (w state))
        (names

; Warning: If you add a name here, handle it in essential-events (and hence
; perhaps essential-basic-event).

         (list* 'defun-sk ; given custom handling here
                'in-package
                'defpkg

; The following for translating axioms.lisp; you won't find them in a book.

                'value 'set-ld-skip-proofsp
                (primitive-event-macros)))
        (portcullisp nil)     ; ok to be generous
        (in-local-flg nil)    ; ok to be generous
        (in-encapsulatep nil) ; ok to be generous
        (make-event-chk nil)  ; we will handle make-event issues ourselves
        )
    (chk-embedded-event-form form orig-form wrld ctx state names portcullisp
                             in-local-flg in-encapsulatep make-event-chk)))

(defmacro internal-error (ctx string &rest args)
  `(er soft ,ctx
       "Internal error: ~@0"
       (msg ,string ,@args)))

(defun essential-basic-event (form ctx state)
  (declare (xargs :guard (true-listp form)))
  (let* ((name (cadr form))
         (wrld (w state))
         (event-type (car form)))
    (case event-type
      ((defun defun-sk)
       (cond
        ((eq (defun-mode name wrld) :logic)
         (let ((tbody (getprop name 'unnormalized-body nil 'current-acl2-world
                               wrld)))
           (cond ((null tbody)
                  (internal-error
                   ctx
                   "Missing 'unnormalized-body property for ~x0."
                   name))
                 ((eq event-type 'defun)
                  (value (list 'defun name (caddr form) tbody)))
                 (t
                  (case-match form
                    (('defun-sk !name formals
                       (quant vars &) . &)
                     (let ((vars
                            (if (symbolp vars) (list vars) vars)))
                       (cond
                        ((null (cdr vars))
                         (case-match tbody
                           (('prog2$ ('throw-nonexec-error . &)
                                     (('lambda & matrix) . &))
                            (value (list 'defun-sk name formals
                                         (list quant vars matrix))))
                           (& (internal-error ctx
                                              "Unexpected form of ~
                                             'unnormalized-body property for ~
                                             ~x0:~|~%  ~x1"
                                              name tbody))))
                        (t ; at least two vars
                         (case-match tbody
                           (('prog2$ ('throw-nonexec-error . &)
                                     (('lambda ('mv . &)
                                        (('lambda & matrix) . &))
                                      . &))
                            (value (list 'defun-sk name formals
                                         (list quant vars matrix))))
                           (& (internal-error ctx
                                              "Unexpected form of ~
                                             'unnormalized-body property for ~
                                             ~x0:~|~%  ~x1"
                                              name tbody)))))))
                    (& (internal-error ctx
                                       "Expected defun-sk of a certain form, ~
                                        but got:~|~%  ~x1."
                                       name
                                       form)))))))
        (t
; Don't cause an error -- maybe we needed this function in order to define
; macros or constants.
         (value nil))))
      ((defaxiom defthm)
       (let ((tbody (getprop name 'theorem nil 'current-acl2-world wrld)))
         (value (and tbody
                     (list event-type
                           (cadr form)
                           tbody)))))
      (defpkg
        (let ((pkg-entry (assoc-equal name
                                      (known-package-alist
                                       state))))
          (cond (pkg-entry (value (list event-type
                                        (cadr form)
                                        (kwote (package-entry-imports
                                                pkg-entry)))))
                (t (internal-error
                    ctx
                    "Missing package entry for ~x0 in the ~
                              known-package-alist."
                    name)))))
      (in-package (value form))
      (include-book

; !! Should we deal with :ttags too?

       (let* ((kwd-args (cddr form))
              (dir (cadr (assoc-keyword :dir kwd-args))))
         (cond
          ((eq dir :system)
           (value `(include-book ,(cadr form) :dir :system)))
          (dir

; Warning: Keep the following in sync with ACL2 source function
; include-book-fn.

           (er-let*
            ((dir-value
              (include-book-dir-with-chk soft ctx dir)))
            (mv-let
             (full-book-name directory-name familiar-name)
             (parse-book-name dir-value (cadr form) ".lisp" state)
             (declare (ignore directory-name familiar-name))
             (value `(include-book ,full-book-name)))))
          (t (value `(include-book ,(cadr form)))))))
      (otherwise (er soft ctx
                     "Unexpected form type in ~x0: ~x1"
                     'essential-basic-event form)))))

(defun cons-to-all (a x)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) nil)
        (t (cons (cons a (car x))
                 (cons-to-all a (cdr x))))))

(defun fix-signature (sig)

; Convert a signature to a list (fn . arity).

  (declare (xargs :guard t))
  (case-match sig
    (((name . formals) . &)
     (list name (length formals)))
    ((name formals . &)
     (list name (length formals)))
    (& (er hard 'fix-signature
           "Unexpexpected signature, ~x0"
           sig))))

(defun fix-signatures (sigs)
  (declare (xargs :guard (true-listp sigs)))
  (cond ((endp sigs) nil)
        (t (cons (fix-signature (car sigs))
                 (fix-signatures (cdr sigs))))))

(defun essential-events (forms acc ctx state)

; Warning: state global 'ld-skip-proofsp should be 'local before calling this
; function.

  (cond
   ((atom forms)
    (value (reverse acc)))
   (t
    (er-let*
     ((form (expand-to-event (car forms) ctx state)))
     (cond
      ((null form)
       (essential-events (cdr forms) acc ctx state))
      (t
       (case (car form)
         (progn
           (essential-events (append (cdr form) (cdr forms)) acc ctx state))
         (with-output
          (essential-events (cons (car (last form)) (cdr forms)) acc ctx state))
         (skip-proofs ; !! special annotation needed?
          (essential-events (cons (cadr form) (cdr forms)) acc ctx state))
         (make-event
          (let ((exp (cadr (assoc-keyword :check-expansion (cddr form)))))
            (cond ((consp exp)
                   (essential-events (cons exp (cdr forms)) acc ctx state))
                  (t
                   (er soft ctx
                       "Encountered make-event form without expansion stored ~
                        in :check-expansion field, which we cannot currently ~
                        handle:~|~%~x0"
                       form)))))
         (encapsulate
          (let ((signatures (cadr form)))
            (cond (signatures
                   (er-let*
                    ((events (essential-events (cddr form) nil ctx state)))
                    (essential-events (cdr forms)
                                      (cons (list* 'encap
                                                   (fix-signatures (cadr form))
                                                   events)
                                            acc)
                                      ctx state)))
                  (t (essential-events (append (cddr form) (cdr forms)) acc ctx
                                       state)))))
         ((mutual-recursion defuns)
          (let ((defs (if (eq (car form) 'mutual-recursion)
                          (cdr form)
                        (cons-to-all 'defun (cdr form)))))
            (er-let*
             ((events (essential-events defs nil ctx state)))
             (essential-events (cdr forms)
                               (if events
                                   (cons (cons 'mutual-recursion events) acc)
                                 acc)
                               ctx state))))
         ((defun defthm defaxiom in-package defpkg include-book defun-sk)
          (er-let* ((new-form (essential-basic-event form ctx state)))
                   (essential-events (cdr forms)
                                     (if new-form (cons new-form acc) acc)
                                     ctx
                                     state)))
         (table

; Even :program mode event can be skipped.  We'll check modes in
; essential-basic-event.

          (essential-events (cdr forms) acc ctx state))
         (

; We want to cause an error for every remaining event that has logical content.
; (But we are handling the defun-mode already, so we can skip (logic) and
; (program).)  The following is the value of the following expression after
; (push :non-standard-analysis *features*).  With this approach, if ACL2 later
; contains new logical events that we use then we will see an error.  If we
; used the other possible parity, taking the short list below as teh list on
; which to cause an error, then we would miss that additional logical event
; rather than causing an error.
#||
 (set-difference-eq (primitive-event-macros)
                    '(#+:non-standard-analysis
                      defun-std
                      #+:non-standard-analysis
                      defthm-std
                      defstobj
                      defchoose
                      progn!
                      defttag))
||#

          (value set-ld-skip-proofsp ; see expand-to-event
           DEFUN MUTUAL-RECURSION DEFUNS DEFTHM DEFAXIOM
           DEFCONST DEFLABEL DEFDOC DEFTHEORY
           VERIFY-GUARDS DEFMACRO IN-THEORY
           IN-ARITHMETIC-THEORY PUSH-UNTOUCHABLE
           REMOVE-UNTOUCHABLE RESET-PREHISTORY
           SET-BODY TABLE PROGN ENCAPSULATE
           INCLUDE-BOOK ADD-CUSTOM-KEYWORD-HINT
           ADD-INCLUDE-BOOK-DIR
           DELETE-INCLUDE-BOOK-DIR
           COMP VERIFY-TERMINATION VERIFY-TERMINATION-BOOT-STRAP
           ADD-MATCH-FREE-OVERRIDE
           THEORY-INVARIANT LOGIC PROGRAM
           ADD-DEFAULT-HINTS! REMOVE-DEFAULT-HINTS!
           SET-MATCH-FREE-DEFAULT
           SET-ENFORCE-REDUNDANCY
           SET-VERIFY-GUARDS-EAGERNESS
           SET-NON-LINEARP
           SET-COMPILE-FNS SET-MEASURE-FUNCTION
           SET-WELL-FOUNDED-RELATION
           SET-INVISIBLE-FNS-TABLE
           SET-BACKCHAIN-LIMIT
           SET-BOGUS-DEFUN-HINTS-OK
           SET-BOGUS-MUTUAL-RECURSION-OK
           SET-DEFAULT-BACKCHAIN-LIMIT
           SET-IRRELEVANT-FORMALS-OK
           SET-IGNORE-OK SET-INHIBIT-WARNINGS
           SET-STATE-OK SET-LET*-ABSTRACTIONP
           SET-NU-REWRITER-MODE
           SET-CASE-SPLIT-LIMITATIONS
           SET-DEFAULT-HINTS!
           SET-REWRITE-STACK-LIMIT VALUE-TRIPLE
           defattach)
          (essential-events (cdr forms) acc ctx state))
         (otherwise
          (er soft ctx
              "~x0 is not yet implemented, hence the following form is ~
               illegal:~|~%  ~x1"
              (car form)
              (car forms))))))))))

(defun print-objects-pretty-rec (lst ch state)
  (cond ((null lst) state)
        (t (mv-let (col state)
                   (fmt1 "~X01~|"
                         (list (cons #\0 (car lst)) (cons #\1 nil))
                         0 ch state nil)
                   (declare (ignore col))
                   (pprogn (if (cdr lst)
                               (newline ch state)
                             state)
                           (print-objects-pretty-rec (cdr lst) ch state))))))

(defun print-objects-pretty (lst ch state)
  (mv-let (erp val state)
          (state-global-let* ((write-for-read t))
                             (pprogn (print-objects-pretty-rec lst ch state)
                                     (value :invisible)))
          (declare (ignore erp val))
          state))

(defun set-ld-skip-proofsp-state (val state)
  (mv-let (erp x state)
          (set-ld-skip-proofsp val state)
          (declare (ignore erp x))
          state))

(defun print-book-essence (book-name infile outfile cert-optional-p ctx state)
  (state-global-let*
   ((ld-skip-proofsp 'include-book set-ld-skip-proofsp-state))
   (er-let*
       ((portcullis-cmds
         (if (eq cert-optional-p :skip)
             (value nil)
           (read-portcullis-cmds book-name cert-optional-p ctx state)))
        (forms (read-object-file infile ctx state))
        (events1 (essential-events portcullis-cmds nil ctx
                                   state))
        (events2 (essential-events forms nil ctx state)))
     (mv-let (chan state)
             (open-output-channel outfile :object state)
             (cond ((null chan)
                    (er soft ctx
                        "Unable to open file ~x0 for output."
                        outfile))
                   (t (pprogn
                       (print-objects-pretty events1 chan state)
                       (cond (events1
                              (pprogn
                               (newline chan state)
                               (princ$ "; NOTE: Only the forms above are evaluated (as opposed the ones below,"
                                       chan state)
                               (newline chan state)
                               (princ$ "; which merely are read) when translating to ML."
                                       chan state)))
                             (t state))
                       (assert$
                        (and (consp (car events2))
                             (eq (caar events2) 'in-package))
                        (cond
                         ((equal (cadar events2) "ACL2") state)
                         (t
                          (pprogn
                           (assert$
                            events1 ; else we could not have a new package here
                            (princ$ "  On a related note:"
                                    chan state))
                           (newline chan state)
                           (princ$ "; the following IN-PACKAGE form is for use by a2ml, but all forms in"
                                   chan state)
                           (newline chan state)
                           (princ$ "; this file assume that the current package is actually \"ACL2\"."
                                   chan state)))))
                       (cond (events1
                              (pprogn (newline chan state)
                                      (newline chan state)))
                             (t state))
                       (print-objects-pretty events2 chan state)
                       (close-output-channel chan state)
                       (value :invisible))))))))

(defmacro book-essence (infile &optional outfile cert-optional-p infile-keywords)
  (declare (ignore infile-keywords)) ; add later for parameters, like ttags
  (let* ((outfile (or outfile (concatenate 'string infile ".essence")))
         (len (length infile))
         (book-name
          (cond ((eq cert-optional-p :skip) nil)
                ((and (< 5 len)
                      (equal (subseq infile (- len 5) len)
                             ".lisp"))
                 (subseq infile 0 (- len 5)))
                (t (er hard 'book-essence
                       "Input file ~x0 did not end in ~s1 ."
                       infile ".lisp")))))
    `(ld '((reset-prehistory)
           (include-book ,book-name)
           (print-book-essence ,book-name ,infile ,outfile ,cert-optional-p
                               'book-essence state)
           (ubt! 1)
           (ubt-prehistory)))))

; Modification for creating essence file for ACL2 source file axioms.lisp:

(defmacro axioms-essence (&optional (outfile '"defaxioms.lisp.trans"))
  `(progn
     (defttag :pprint-axioms)
     (progn!
      :state-global-bindings
      ((temp-touchable-vars t set-temp-touchable-vars)
       (temp-touchable-fns t set-temp-touchable-fns))
      (set-raw-mode-on state)
      (let ((*features* (cons :acl2-loop-only *features*))
            (ctx 'axioms-essence))
        (er-let*
         ((acl2-src-dir
           (getenv$ "ACL2_SRC" state)))
         (cond ((null acl2-src-dir)
                (er soft ctx
                    "Environment variable ACL2_SRC needs to be set."))
               (t (print-book-essence nil
                                      (concatenate 'string acl2-src-dir
                                                   "/axioms.lisp")
                                      ,outfile :skip
                                      ctx state))))))))
