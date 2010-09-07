; (defpkg "MY-PKG" '(defun cons))

(in-package "MY-PKG")

(defun f1 (x)
  (cons x x))

(defun f2 (x)
  (acl2::append x x))

(defun consts ()
  '(x defun cons))

#!acl2
(defthm test0
  (let ((lst (my-pkg::consts)))
    (and (equal (car lst) 'my-pkg::x)
         (not (equal (car lst) 'acl2::x))
         (equal (cadr lst) 'my-pkg::defun)
         (equal (cadr lst) 'acl2::defun)
         (equal (cadr lst) 'common-lisp::defun)
         (equal (caddr lst) 'my-pkg::cons)
         (equal (caddr lst) 'acl2::cons)
         (equal (caddr lst) 'common-lisp::cons)))
  :rule-classes nil)

#!acl2
(defthm test1a
  (equal (symbol-package-name 'my-pkg::c)
         "MY-PKG")
  :rule-classes nil)

#!acl2
(defthm test1b
  (equal (symbol-name 'my-pkg::c)
         "C")
  :rule-classes nil)

#!acl2
(defthm test2a
  (equal (symbol-package-name 'my-pkg::defun)
         "COMMON-LISP")
  :rule-classes nil)

#!acl2
(defthm test2b
  (equal (symbol-name 'my-pkg::defun)
         "DEFUN")
  :rule-classes nil)

#!acl2
(defthm test3a
  (equal (symbol-package-name 'my-pkg::|defun|)
         "MY-PKG")
  :rule-classes nil)

#!acl2
(defthm test3b
  (equal (symbol-name 'my-pkg::|defun|)
         "defun")
  :rule-classes nil)

#!acl2
(defthm test4
  (equal (intern-in-package-of-symbol "DEFUN" 'my-pkg::c)
         (intern-in-package-of-symbol "DEFUN" 'common-lisp::c))
  :rule-classes nil)

#!acl2
(defthm test5
  (not (equal (intern-in-package-of-symbol "defun" 'my-pkg::c)
              (intern-in-package-of-symbol "defun" 'common-lisp::c)))
  :rule-classes nil)

#!acl2
(defthm test6
  (not (equal (intern-in-package-of-symbol "D" 'my-pkg::c)
              (intern-in-package-of-symbol "D" 'common-lisp::c)))
  :rule-classes nil)

; Test of quoted constants:

(defun fun0 ()
  '(a defun b))

(defun fun1 ()
  '(a defun b . c))

(acl2::defthm
 fun0-thm
 (acl2::equal (fun0)
              (cons 'a (cons 'defun (cons 'b acl2::nil)))))

(acl2::defthm
 fun1-thm
 (acl2::equal (fun1)
              (cons 'a (cons 'defun (cons 'b 'c)))))
