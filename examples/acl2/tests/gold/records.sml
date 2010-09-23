open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;

val package =
 implode(map chr (cons 65 (cons 67 (cons 76 (cons 50 nil)))));

val events = [

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "RCDP") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "NULL") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "NULL") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "CONSP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "CONSP") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"RCDP") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "NULL") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "NULL") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "ACL2" "<<") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "IFRP") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (mkpair (
mkpair (mksym "ACL2" "RCDP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"NOT") (mkpair (mkpair (mksym "ACL2" "RCDP") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "CONSP") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "NULL") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "CONSP") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "NULL") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "IFRP") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "ACL2->RCD") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "IFRP") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "RCD->ACL2") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "IFRP") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "G-AUX") (mkpair (
mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "ACL2" "<<") (mkpair (mksym "ACL2" "A") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "A") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "ACL2" "G-AUX") (mkpair (mksym "ACL2" "A") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "G") (mkpair (
mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "ACL2" "G-AUX") (mkpair (mksym "ACL2" "A") (
mkpair (mkpair (mksym "ACL2" "ACL2->RCD") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "S-AUX") (mkpair (
mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" 
"R") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "R") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "R") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "<<") (mkpair (mksym 
"ACL2" "A") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "R") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mksym "ACL2" "V") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "ACL2" "A") (mkpair (mksym 
"ACL2" "V") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "R") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "R") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "R") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mksym "ACL2" "V") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "ACL2" "A") (
mkpair (mksym "ACL2" "V") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "R") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"CDR") (mkpair (mksym "ACL2" "R") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "R") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "S-AUX") (mkpair (mksym 
"ACL2" "A") (mkpair (mksym "ACL2" "V") (mkpair (mkpair (mksym "COMMON-LISP" 
"CDR") (mkpair (mksym "ACL2" "R") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "S") (mkpair (
mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" 
"X") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "RCD->ACL2") (
mkpair (mkpair (mksym "ACL2" "S-AUX") (mkpair (mksym "ACL2" "A") (mkpair (
mksym "ACL2" "V") (mkpair (mkpair (mksym "ACL2" "ACL2->RCD") (mkpair (mksym 
"ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "KEYS-AUX") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "ACL2" "KEYS-AUX") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "KEYS") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"ACL2" "KEYS-AUX") (mkpair (mkpair (mksym "ACL2" "ACL2->RCD") (mkpair (mksym 
"ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "G-SAME-S") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym "ACL2" "S") (mkpair (mksym 
"ACL2" "A") (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" "R") (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" 
"V") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "G-DIFF-S") (mkpair (
mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "A") (
mkpair (mksym "ACL2" "B") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym 
"ACL2" "G") (mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym "ACL2" "S") (
mkpair (mksym "ACL2" "B") (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" 
"R") (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "ACL2" "G") (mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" 
"R") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "G-OF-S-REDUX") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym "ACL2" "S") (mkpair (mksym 
"ACL2" "B") (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" "R") (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "B") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mksym "ACL2" "V") (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "R") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "S-SAME-G") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "S") (
mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mksym 
"ACL2" "A") (mkpair (mksym "ACL2" "R") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mksym "ACL2" "R") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mksym "ACL2" "R") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "S-SAME-S") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "S") (
mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "Y") (mkpair (mkpair (mksym 
"ACL2" "S") (mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "X") (mkpair (
mksym "ACL2" "R") (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "ACL2" "S") (mkpair (mksym "ACL2" "A") (mkpair (mksym 
"ACL2" "Y") (mkpair (mksym "ACL2" "R") (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "S-DIFF-S") (mkpair (
mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "A") (
mkpair (mksym "ACL2" "B") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym 
"ACL2" "S") (mkpair (mksym "ACL2" "B") (mkpair (mksym "ACL2" "Y") (mkpair (
mkpair (mksym "ACL2" "S") (mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" 
"X") (mkpair (mksym "ACL2" "R") (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" "S") (mkpair (mksym 
"ACL2" "A") (mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym "ACL2" "S") (
mkpair (mksym "ACL2" "B") (mkpair (mksym "ACL2" "Y") (mkpair (mksym "ACL2" 
"R") (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "G-KEYS-RELATIONSHIP") (
mkpair (mkpair (mksym "ACL2" "IFF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (
mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym "ACL2" "KEYS") (mkpair (
mksym "ACL2" "R") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mksym "ACL2" "A") (mkpair (mksym 
"ACL2" "R") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "S-KEYS-REDUCTION") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" 
"KEYS") (mkpair (mkpair (mksym "ACL2" "S") (mkpair (mksym "ACL2" "A") (mkpair (
mksym "ACL2" "V") (mkpair (mksym "ACL2" "R") (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mksym "ACL2" "V") (mkpair (mkpair (mksym "ACL2" "INSERT") (mkpair (
mksym "ACL2" "A") (mkpair (mkpair (mksym "ACL2" "KEYS") (mkpair (mksym "ACL2" 
"R") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "ACL2" "DROP") (mkpair (mksym "ACL2" "A") (mkpair (mkpair (
mksym "ACL2" "KEYS") (mkpair (mksym "ACL2" "R") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "KEYS-ARE-ORDERED") (
mkpair (mkpair (mksym "ACL2" "ORDEREDP") (mkpair (mkpair (mksym "ACL2" "KEYS") (
mkpair (mksym "ACL2" "R") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "G-OF-NIL-IS-NIL") (
mkpair (mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"S-NON-NIL-CANNOT-BE-NIL") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mksym "ACL2" "V") (mkpair (mkpair (mksym "ACL2" "S") (mkpair (mksym "ACL2" 
"A") (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" "R") (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "NON-NIL-IF-G-NON-NIL") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "R") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mksym "ACL2" "R") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"S-SAME-G-BACK-CHAINING") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "V") (mkpair (
mkpair (mksym "ACL2" "G") (mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" 
"R") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "S") (
mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" 
"R") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mksym "ACL2" "R") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "UPDATE-MACRO") (
mkpair (mkpair (mksym "ACL2" "UPDS") (mkpair (mksym "ACL2" "RESULT") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "UPDS") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "RESULT") (mkpair (mkpair (mksym 
"ACL2" "UPDATE-MACRO") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "UPDS") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "ACL2" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "UPDS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "UPDS") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mksym "ACL2" "RESULT") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))))

];
