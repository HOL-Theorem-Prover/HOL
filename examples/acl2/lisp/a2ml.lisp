; Input file: ACL2 s-expressions.

; Output file: val acl2_list = [x1,x2,...,xk] where each xi is the translation
; of the i-th input file expression.

(in-package "ACL2")
(set-state-ok t)
(program)

(defconst *mksym*  'mksym)
(defconst *mk_chars_str*  'mk_chars_str)
(defconst *mkchr*  'mkchr)
(defconst *mknum*  'mknum)
(defconst *mkpair* 'mkpair)

(defun i2s (n)
  (coerce (explode-atom n 10) 'string))

(defun s2conses (s n result)
  (declare (xargs :guard (and (stringp s)
                              (natp n)
                              (< n (length s)))))
  (if (zp n)
      result
    (let ((k (1- n)))
      (s2conses s k (list 'cons (char-code (char s k)) result)))))

(defun sexp-to-ml (x)
  (cond ((characterp x)
         (list *mkchr* (char-code x)))
        ((stringp x)
         (list *mk_chars_str*
               (list 'chars_to_string
                     (s2conses x (length x) nil))))
        ((acl2-numberp x)
         (let ((rp (realpart x))
               (ip (imagpart x)))
           (list *mknum*
                 (i2s (numerator rp)) (i2s (denominator rp))
                 (i2s (numerator ip)) (i2s (denominator ip)))))
        ((symbolp x)
         (list *mksym* (symbol-package-name x) (symbol-name x)))
        ((atom x)
         (er hard 'sexp-to-ml
             "Unknown atom, ~x0"
             x))
        (t ; consp case
         (list *mkpair*
               (sexp-to-ml (car x))
               (sexp-to-ml (cdr x))))))

(include-book "misc/file-io" :dir :system)

#|
(defun pprint-object (obj channel state)
  (mv-let (erp val state)
          (state-global-let*
           ((write-for-read t))
           (pprogn (ppr2 (ppr1 obj (acl2-print-base) 80 0 state t)
                         0 channel state t)
                   (value nil)))
          (declare (ignore erp val))
          state))
|#

(defun pprint-object (obj channel state)
  (mv-let (erp val state)
    (state-global-let*
     ((write-for-read t))
     (pprogn (fms "~f0" (list (cons #\0 obj)) channel state nil)
             (value nil)))
    (declare (ignore erp val))
    state))

(defun pprint-objects-to-ml (list sep channel state)
  (if (endp list)
      state
    (pprogn (pprint-object (sexp-to-ml (car list)) channel state)
            (newline channel state)
            (if (endp (cdr list)) state (princ$ sep channel state))
            (newline channel state)
            (pprint-objects-to-ml (cdr list) sep channel state))))

(defun a2ml-fn (infile outfile state)
  (declare (xargs :guard (and (stringp infile)
                              (stringp outfile))
                  :stobjs state))
  (downcase
   (let ((ctx 'a2ml))
     (er-let*
      ((list (read-list infile ctx state)))
      (mv-let (channel state)
              (open-output-channel outfile :character state)
              (if channel
                  (mv-let
                   (col state)
                   (fmt1 "Writing ml file ~x0.~%" (list (cons #\0 outfile))
                         0 (standard-co state) state nil)
                   (declare (ignore col))
                   (pprogn (princ$ "val acl2_list = [" channel state)
                           (newline channel state)
                           (let ((state (pprint-objects-to-ml
                                         list "," channel state)))
                             (pprogn (princ$ "];" channel state)
                                     (newline channel state)
                                     (close-output-channel channel state)
                                     (value :invisible)))))
                (er soft ctx
                    "Unable to open file ~s0 for :character output."
                    outfile)))))))

(defmacro a2ml (infile outfile)
  (declare (xargs :guard (and (stringp infile)
                              (stringp outfile))))
  `(a2ml-fn ,infile ,outfile state))
