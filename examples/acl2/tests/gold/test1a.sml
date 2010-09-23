open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;

val package =
 implode(map chr (cons 65 (cons 67 (cons 76 (cons 50 nil)))));

val events = [

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "FOO") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "FOO-PROP") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mkpair (mksym "ACL2" "FOO") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"X") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "BAR") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"ACL2" "FOO") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "H") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"ACL2" "BAR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))))

];
