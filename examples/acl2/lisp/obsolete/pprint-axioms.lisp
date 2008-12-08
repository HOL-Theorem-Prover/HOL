(in-package "ACL2")

(include-book "pprint-file")

(program)
(set-state-ok t)

(defun pprint-axioms-fn (outfile state)
  (er-let* ((acl2-books-dir
             (getenv$ "ACL2_SYSTEM_BOOKS" state)))
           (let* ((len (length acl2-books-dir))
                  (acl2-src-dir
                   (if (and (< 6 len)
                            (equal (subseq acl2-books-dir (- len 6) len)
                                   "/books"))
                       (subseq acl2-books-dir 0 (- len 5))
                     (er hard 'top-level
                         "Environment variable ACL2_SYSTEM_BOOKS has illegal ~
                          or unbound value, ~x0"
                         acl2-books-dir))))
             (write-forms (concatenate 'string acl2-src-dir "axioms.lisp")
                          outfile nil state))))

(defmacro pprint-axioms (&optional (outfile '"defaxioms.lisp.trans"))
  `(progn
     (defttag :pprint-axioms)
     (progn!
      :state-global-bindings
      ((temp-touchable-vars t set-temp-touchable-vars)
       (temp-touchable-fns t set-temp-touchable-fns))
      (set-raw-mode-on state)
      (let ((*features* (cons :acl2-loop-only *features*)))
        (pprint-axioms-fn ,outfile state)))))

