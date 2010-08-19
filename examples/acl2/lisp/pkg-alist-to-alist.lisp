(in-package "ACL2")

; Evaluation of (print-kpa lisp-filename ml-filename) prints to the indicated
; filenames corresponding representations (Lisp and ML) of the current package
; structure.  In each case (Lisp and ML) there are two forms (which in the case
; of ML are ML definitions).  The form first provides a list of triples

; <symbol-name, known-pkg-name, actual-pkg-name>

; the idea being that when symbol-name is interned into known-pkg-name, the
; resulting symbol's package name is actual-pkg-name.  That is, the symbol with
; name symbol-name and package-name actual-pkg-name is imported into package
; known-pkg-name.  The second form is a list of known package names.  Note that
; packages with empty import lists will not be mentioned in any second or third
; component of a triple.

(set-state-ok t)

(program)

(defun triplesp (x)
  (if (consp x)
      (and (true-listp (car x))
           (equal (length (car x)) 3)
           (triplesp (cdr x)))
    (null x)))

(defun kpa-to-triples-aux (pkg-name imports acc)
  (declare (xargs :guard (and (symbol-listp imports)
                              (triplesp acc))))
  (cond ((endp imports) acc)
        (t (cons (list (symbol-name (car imports))
                       pkg-name
                       (symbol-package-name (car imports)))
                 (kpa-to-triples-aux pkg-name (cdr imports) acc)))))

(defun kpa-to-triples (kpa acc)
  (declare (xargs :guard (and (alistp kpa) ; should be stronger
                              (triplesp acc))))
  (cond ((endp kpa) acc)
        (t (kpa-to-triples (cdr kpa)
                           (kpa-to-triples-aux
                            (package-entry-name (car kpa))
                            (package-entry-imports (car kpa))
                            acc)))))

(defun print-string-triples-rec (triples chan state)
  (declare (xargs :stobjs state
                  :guard (and (triplesp triples)
                              (symbolp chan)
                              (open-output-channel-p chan :character state))))
  (cond ((endp triples) state)
        (t (pprogn (fms "    (~x0 , ~x1 , ~x2)~s3"
                        (list (cons #\0 (nth 0 (car triples)))
                              (cons #\1 (nth 1 (car triples)))
                              (cons #\2 (nth 2 (car triples)))
                              (cons #\3 (if (cdr triples) ";" "")))
                        chan state nil)
                   (print-string-triples-rec (cdr triples) chan state)))))

(defun print-objs-rec (objs chan state)
  (declare (xargs :stobjs state
                  :guard (and (true-listp objs)
                              (symbolp chan)
                              (open-output-channel-p chan :character state))))
  (cond ((endp objs) state)
        (t (pprogn (fms "    ~x0~s1"
                        (list (cons #\0 (car objs))
                              (cons #\1 (if (cdr objs) ";" "")))
                        chan state nil)
                   (print-objs-rec (cdr objs) chan state)))))

(defun print-ml-string-triples-and-known-pkgs (triples pkg-names filename ctx
                                                       state)
  (declare (xargs :stobjs state))
  (mv-let (chan state)
    (open-output-channel filename :character state)
    (cond ((null chan)
           (er soft ctx
               "Unable to open file ~x0 for output.~|"
               filename))
          (t (pprogn (princ$ "Define" chan state)
                     (newline chan state)
                     (princ$ " `ACL2_PACKAGE_ALIST =" chan state)
                     (newline chan state)
                     (princ$ "   [" chan state)
                     (print-string-triples-rec triples chan state)
                     (princ$ "]`;" chan state)
                     (newline chan state)
                     (newline chan state)
                     (princ$ "Define" chan state)
                     (newline chan state)
                     (princ$ " `ACL2_KNOWN_PACKAGES =" chan state)
                     (newline chan state)
                     (princ$ "   [" chan state)
                     (print-objs-rec pkg-names chan state)
                     (princ$ "]`;" chan state)
                     (newline chan state)
                     (value :invisible))))))

(defun imports-alist-from-kpa (kpa)
  (cond ((endp kpa) nil)
        (t (let* ((entry (car kpa))
                  (name (package-entry-name entry))
                  (imports (package-entry-imports entry)))
             (acons name imports (imports-alist-from-kpa (cdr kpa)))))))

(defun print-imports-alist (filename ctx state)
  (mv-let
   (channel state)
   (open-output-channel filename :object state)
   (cond ((null channel)
          (er soft ctx
              "Unable to open file ~s0 for :character output."
              filename))
         (t (pprogn (print-object$ (imports-alist-from-kpa
                                    (known-package-alist state))
                                   channel state)
                    (newline channel state)
                    (close-output-channel channel state)
                    (value :invisible))))))

(defmacro print-kpa (lisp-filename ml-filename)
  `(let* ((lisp-filename ,lisp-filename)
          (ml-filename ,ml-filename)
          (kpa (known-package-alist state))
          (triples (kpa-to-triples kpa nil))
          (pkg-names (strip-cars kpa)))
     (er-progn (print-imports-alist lisp-filename 'print-kpa state)
               (print-ml-string-triples-and-known-pkgs
                triples pkg-names ml-filename 'print-kpa state)
               (pprogn (fms "Wrote files ~x0 and ~x1.~|"
                            (list (cons #\0 lisp-filename)
                                  (cons #\1 ml-filename))
                            (standard-co state) state nil)
                       (value :invisible)))))

; A test (remove the NOT to see that this is a well-formed test):

#|
(loop for x in (kpa-to-triples (known-package-alist state) nil)
      when (not (equal (symbol-package-name (intern (car x) (cadr x))) (caddr x)))
      do (print x))
|#

; Now we check that the current known-package-alist agrees with the
; known-package-alist from a given lisp file, such as was written above.

(defun chk-known-package-alist (pkg-file state)
  (let ((ctx 'chk-known-package-alist))
    (er-let* ((lst (read-file pkg-file state)))
      (cond ((not (and (true-listp lst)
                       (eql (len lst) 1)
                       (alistp (car lst))))
             (er soft ctx
                 "Unexpected form for package file, ~x0."
                 pkg-file))
            (t (let* ((full-imports-alist (car lst))
                      (full-pkg-list (strip-cars full-imports-alist))
                      (current-imports-alist
                       (imports-alist-from-kpa (known-package-alist state)))
                      (bad-keys
                       (set-difference-equal (strip-cars current-imports-alist)
                                             full-pkg-list)))
                 (cond (bad-keys
                        (er soft ctx
                            "Known package~#0~[ ~&0 is~/s ~&0 are~] is ~
                             missing in package file ~x1."
                            bad-keys pkg-file))
                       ((subsetp-equal current-imports-alist full-imports-alist)
                        (pprogn
                         (fms "Chk-known-package-alist: PASSED~|"
                              nil (standard-co state) state nil)
                         (value :invisible)))
                       (t (let* ((diff
                                  (set-difference-equal current-imports-alist
                                                        full-imports-alist))
                                 (current-imports (cdar diff))
                                 (key (caar diff))
                                 (full-imports
                                  (cdr (assoc-equal key full-imports-alist))))
                            (er soft ctx
                                "The current value of ~x0 is not contained in ~
                                 the known-package-alist stored in file ~x1.  ~
                                 For example, compare the symbols imported ~
                                 into package ~x2, as follows.~|~%For the ~
                                 current known-package-alist:~| ~
                                 ~X35.~|~%Stored in the above file:~| ~X45.~|"
                                '(known-package-alist state)
                                pkg-file
                                key
                                current-imports
                                full-imports
                                nil))))))))))

(defun note-chk-known-package-alist-success (filename state)
  (mv-let
   (channel state)
   (open-output-channel filename :character state)
   (cond ((null channel)
          (er soft 'note-chk-known-package-alist-success
              "Unable to open file ~s0 for :character output."
              filename))
         (t (pprogn (princ$ "Success!" channel state)
                    (newline channel state)
                    (close-output-channel channel state)
                    (value :invisible))))))

