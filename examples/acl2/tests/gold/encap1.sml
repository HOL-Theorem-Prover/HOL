open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;

val package =
 implode(map chr (cons 65 (cons 67 (cons 76 (cons 50 nil)))));

val events = [

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "CAR-CONS-1") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "ACL2" "X") (
mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "CAR-CONS-2") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "ACL2" "X") (
mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "F1") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mksym "ACL2" 
"X") (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "CAR-CONS-3") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "ACL2" "X") (
mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "F2") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mksym "ACL2" 
"X") (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "ENCAP") (mkpair (mkpair (mkpair (mksym "ACL2" "G1") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym 
"ACL2" "INTEGERP-G1") (mkpair (mkpair (mksym "COMMON-LISP" "INTEGERP") (
mkpair (mkpair (mksym "ACL2" "G1") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "ENCAP") (mkpair (mkpair (mkpair (mksym "ACL2" "G2") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym 
"ACL2" "INTEGERP-FIRST-G2") (mkpair (mkpair (mksym "COMMON-LISP" "INTEGERP") (
mkpair (mkpair (mksym "ACL2" "MV-NTH") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "ACL2" "G2") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "ENCAP") (mkpair (mkpair (mkpair (mksym "ACL2" "H1") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "H2") (mkpair (mknum "2" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "DEFTHM") (mkpair (
mksym "ACL2" "H1-PROP") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "INTEGERP") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "INTEGERP") (
mkpair (mkpair (mksym "ACL2" "H1") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"DEFTHM") (mkpair (mksym "ACL2" "H2-PROP") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "INTEGERP") (mkpair (mksym 
"ACL2" "Y") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "INTEGERP") (mkpair (mkpair (mksym "ACL2" "MV-NTH") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "H2") (mkpair (mksym 
"ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "ENCAP") (mkpair (mkpair (mkpair (mksym "ACL2" "H3") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "H4") (mkpair (mknum "2" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "DEFTHM") (mkpair (
mksym "ACL2" "H3-PROP") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "INTEGERP") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "INTEGERP") (
mkpair (mkpair (mksym "ACL2" "H3") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"DEFUN") (mkpair (mksym "ACL2" "H5") (mkpair (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "ACL2" "H3") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "H4-H5-PROP") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" 
"INTEGERP") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "INTEGERP") (mkpair (mkpair (mksym "ACL2" "H5") (
mkpair (mkpair (mksym "ACL2" "MV-NTH") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "ACL2" "H4") (mkpair (mksym "ACL2" "X") (mkpair (mksym 
"ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))))

];
