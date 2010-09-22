val _ = sexp.acl2_list_ref := [

(mkpair (mksym "ACL2" "DEFPKG") (mkpair (mk_chars_str (chars_to_string (cons 
77 (cons 89 (cons 45 (cons 80 (cons 75 (cons 71 nil)))))))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mksym "COMMON-LISP" "DEFUN") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "MY-PKG" "F1") (mkpair (
mkpair (mksym "MY-PKG" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mksym "MY-PKG" "X") (mkpair (mksym 
"MY-PKG" "X") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "MY-PKG" "F2") (mkpair (
mkpair (mksym "MY-PKG" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "MY-PKG" "BINARY-APPEND") (mkpair (mksym "MY-PKG" "X") (mkpair (mksym 
"MY-PKG" "X") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))

];

val _ = current_package :=
 implode(map chr 
(cons 77 (cons 89 (cons 45 (cons 80 (cons 75 (cons 71 nil)))))));
