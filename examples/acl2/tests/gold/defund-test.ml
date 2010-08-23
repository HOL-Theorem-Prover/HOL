val _ = sexp.acl2_list_ref := [

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "FOO") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mksym "ACL2" 
"X") (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "BAR") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mksym "ACL2" 
"X") (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "MUTUAL-RECURSION") (mkpair (mkpair (mksym 
"COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "EVENLP") (mkpair (mkpair (mksym 
"ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "CONSP") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "ODDLP") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "ODDLP") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" 
"CONSP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "ACL2" "EVENLP") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "MUTUAL-RECURSION") (mkpair (mkpair (mksym 
"COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "EVENLP2") (mkpair (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "ACL2" 
"PROG2$") (mkpair (mkpair (mksym "ACL2" "THROW-NONEXEC-ERROR") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "ACL2" "EVENLP2") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "CONSP") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "ODDLP2") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "DEFUN") (
mkpair (mksym "ACL2" "ODDLP2") (mkpair (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "ACL2" "PROG2$") (mkpair (mkpair (
mksym "ACL2" "THROW-NONEXEC-ERROR") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "ACL2" "ODDLP2") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "ACL2" "X") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "CONSP") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "EVENLP2") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))

];

val _ = current_package :=
 implode(map chr (cons 65 (cons 67 (cons 76 (cons 50 nil)))));
