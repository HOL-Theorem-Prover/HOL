open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;

val package =
 implode(map chr (cons 65 (cons 67 (cons 76 (cons 50 nil)))));

val events = [

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "<<") (mkpair (
mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "LEXORDER") (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "X") (
mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "<<-IRREFLEXIVE") (
mkpair (mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym "ACL2" "<<") (
mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "<<-TRANSITIVE") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "ACL2" "<<") (mkpair (mksym "ACL2" "X") (mkpair (
mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"ACL2" "<<") (mkpair (mksym "ACL2" "Y") (mkpair (mksym "ACL2" "Z") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "ACL2" "<<") (mkpair (mksym "ACL2" "X") (
mkpair (mksym "ACL2" "Z") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "<<-ASYMMETRIC") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "ACL2" "<<") (
mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym 
"ACL2" "<<") (mkpair (mksym "ACL2" "Y") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "<<-TRICHOTOMY") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym 
"ACL2" "<<") (mkpair (mksym "ACL2" "Y") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "NOT") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" "<<") (mkpair (mksym 
"ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "<<-IMPLIES-LEXORDER") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "ACL2" "<<") (
mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "LEXORDER") (mkpair (mksym "ACL2" "X") (
mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))

];
