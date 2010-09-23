open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;

val package =
 implode(map chr (cons 65 (cons 67 (cons 76 (cons 50 nil)))));

val events = [

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "MEMBERP") (
mkpair (mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "CONSP") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "A") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "MEMBERP") (
mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "DROP") (mkpair (
mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "A") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"ACL2" "DROP") (mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "DROP") (mkpair (mksym 
"ACL2" "A") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" 
"X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "INSERT") (mkpair (
mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "ACL2" "A") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" 
"EQUAL") (mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "<<") (mkpair (mksym "ACL2" 
"A") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" 
"X") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "INSERT") (mkpair (
mksym "ACL2" "A") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym 
"ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "ORDEREDP") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "<<") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "ORDEREDP") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "UNIQUEP") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "NOT") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" 
"X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "UNIQUEP") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "MEMBERP-INSERT-SAME") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" 
"MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym "ACL2" "INSERT") (
mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "MEMBERP-INSERT-DIFF") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" 
"NOT") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" 
"A") (mkpair (mksym "ACL2" "B") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mkpair (
mksym "ACL2" "INSERT") (mkpair (mksym "ACL2" "B") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "MEMBERP-DROP-SAME") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" 
"MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym "ACL2" "DROP") (
mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "MEMBERP-DROP-DIFF") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" 
"NOT") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" 
"A") (mkpair (mksym "ACL2" "B") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mkpair (
mksym "ACL2" "DROP") (mkpair (mksym "ACL2" "B") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"ORDERED-IMPLIES-UNIQUE") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "ACL2" "ORDEREDP") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "UNIQUEP") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"MEMBERP-YES-REDUCE-INSERT") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ORDEREDP") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "ACL2" "INSERT") (mkpair (mksym "ACL2" "A") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"MEMBERP-NO-REDUCE-DROP") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "TRUE-LISTP") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mksym "ACL2" "A") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "ACL2" "DROP") (mkpair (mksym "ACL2" "A") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"DROP-PRESERVES-ORDEREDP") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "ACL2" "ORDEREDP") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "ORDEREDP") (mkpair (
mkpair (mksym "ACL2" "DROP") (mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" 
"X") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"INSERT-PRESERVES-ORDEREDP") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "ACL2" "ORDEREDP") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "ORDEREDP") (mkpair (
mkpair (mksym "ACL2" "INSERT") (mkpair (mksym "ACL2" "A") (mkpair (mksym 
"ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"DROP-OF-INSERT-IS-SAME") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "TRUE-LISTP") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mksym "ACL2" "A") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "ACL2" "DROP") (mkpair (mksym "ACL2" "A") (mkpair (
mkpair (mksym "ACL2" "INSERT") (mkpair (mksym "ACL2" "A") (mkpair (mksym 
"ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"INSERT-OF-DROP-IS-SAME") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ORDEREDP") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "TRUE-LISTP") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" 
"MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" 
"INSERT") (mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym "ACL2" "DROP") (
mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"INSERT-RETURNS-TRUE-LISTS") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "ACL2" "TRUE-LISTP") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "TRUE-LISTP") (mkpair (
mkpair (mksym "ACL2" "INSERT") (mkpair (mksym "ACL2" "A") (mkpair (mksym 
"ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))

];
