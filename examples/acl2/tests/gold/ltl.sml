open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;

val package =
 implode(map chr (cons 65 (cons 67 (cons 76 (cons 50 nil)))));

val events = [

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "LTL-CONSTANTP") (
mkpair (mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" 
"EQUAL") (mkpair (mksym "ACL2" "F") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "ACL2" "TRUE") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mksym "ACL2" "F") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "ACL2" "TRUE") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "F") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "ACL2" "FALSE") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "LTL-VARIABLEP") (
mkpair (mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" 
"SYMBOLP") (mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (
mkpair (mksym "ACL2" "F") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mkpair (mksym "COMMON-LISP" "+") (mkpair (mksym "ACL2" "&") (mkpair (
mksym "ACL2" "U") (mkpair (mksym "ACL2" "W") (mkpair (mksym "ACL2" "X") (
mkpair (mksym "ACL2" "F") (mkpair (mksym "ACL2" "G") (mksym "COMMON-LISP" 
"NIL")))))))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "LTL-FORMULAP") (
mkpair (mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ATOM") (
mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "LTL-CONSTANTP") (
mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "LTL-CONSTANTP") (mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "ACL2" "LTL-VARIABLEP") (mkpair (mksym "ACL2" 
"F") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" 
"EQUAL") (mkpair (mkpair (mksym "ACL2" "LEN") (mkpair (mksym "ACL2" "F") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "3" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "MEMBERP") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "F") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mkpair (mksym "COMMON-LISP" "+") (mkpair (
mksym "ACL2" "&") (mkpair (mksym "ACL2" "U") (mkpair (mksym "ACL2" "W") (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "LTL-FORMULAP") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "LTL-FORMULAP") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "F") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "LEN") (
mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "2" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (mksym 
"ACL2" "~") (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "F") (mkpair (
mksym "ACL2" "G") (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "LTL-FORMULAP") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"RESTRICTED-FORMULAP") (mkpair (mkpair (mksym "ACL2" "F") (mkpair (mksym 
"ACL2" "V-LIST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ATOM") (mkpair (
mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "LTL-CONSTANTP") (mkpair (
mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" 
"LTL-CONSTANTP") (mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"LTL-VARIABLEP") (mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "F") (mkpair (
mksym "ACL2" "V-LIST") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "LEN") (mkpair (mksym 
"ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "3" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (mksym "ACL2" 
"&") (mkpair (mksym "COMMON-LISP" "+") (mkpair (mksym "ACL2" "U") (mkpair (
mksym "ACL2" "W") (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "RESTRICTED-FORMULAP") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "V-LIST") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "RESTRICTED-FORMULAP") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "V-LIST") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mkpair (mksym "ACL2" "LEN") (mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "2" "1" 
"0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "F") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mkpair (mksym "ACL2" "~") (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" 
"F") (mkpair (mksym "ACL2" "G") (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"ACL2" "RESTRICTED-FORMULAP") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "F") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"V-LIST") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"RESTRICTED-FORMULA-IS-AN-LTL-FORMULA") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "ACL2" "RESTRICTED-FORMULAP") (mkpair (
mksym "ACL2" "F") (mkpair (mksym "ACL2" "V-LIST") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "LTL-FORMULAP") (mkpair (mksym "ACL2" "F") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"CREATE-RESTRICTED-VAR-SET") (mkpair (mkpair (mksym "ACL2" "F") (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ATOM") (mkpair (mksym "ACL2" "F") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "LTL-CONSTANTP") (mkpair (mksym "ACL2" "F") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mksym "ACL2" "F") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "LEN") (mkpair (mksym 
"ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "3" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"SET-UNION") (mkpair (mkpair (mksym "ACL2" "CREATE-RESTRICTED-VAR-SET") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "F") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"ACL2" "CREATE-RESTRICTED-VAR-SET") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mkpair (mksym "ACL2" "LEN") (mkpair (mksym "ACL2" "F") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "2" "1" 
"0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "ACL2" "CREATE-RESTRICTED-VAR-SET") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"LTL-FORMULA-IS-A-RESTRICTED-FORMULA") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "ACL2" "LTL-FORMULAP") (mkpair (mksym 
"ACL2" "F") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" 
"RESTRICTED-FORMULAP") (mkpair (mksym "ACL2" "F") (mkpair (mkpair (mksym 
"ACL2" "CREATE-RESTRICTED-VAR-SET") (mkpair (mksym "ACL2" "F") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "NEXT-STATEP") (
mkpair (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "Q") (mkpair (mksym 
"ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"MEMBERP") (mkpair (mksym "ACL2" "Q") (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mksym "ACL2" "P") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "TRANSITION") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "INITIAL-STATEP") (
mkpair (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "M") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mksym "ACL2" "P") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "INITIAL-STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "LABEL-OF") (
mkpair (mkpair (mksym "ACL2" "S") (mkpair (mksym "ACL2" "M") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mksym 
"ACL2" "S") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "LABEL-FN") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"NEXT-STATES-IN-STATES") (mkpair (mkpair (mksym "ACL2" "M") (mkpair (mksym 
"ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (
mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "SUBSET") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "TRANSITION") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"NEXT-STATES-IN-STATES") (mkpair (mksym "ACL2" "M") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"NEXT-STATES-IN-STATES-CLARIFIED-AUX") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "MEMBERP") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "STATES") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "NEXT-STATES-IN-STATES") (mkpair (mksym "ACL2" 
"M") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "ACL2" "NEXT-STATEP") (mkpair (mksym "ACL2" "P") (mkpair (mksym 
"ACL2" "Q") (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "Q") (mkpair (mkpair (mksym 
"ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"KEYWORD" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"NEXT-STATES-IN-STATES-CLARIFIED") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"NEXT-STATES-IN-STATES") (mkpair (mksym "ACL2" "M") (mkpair (mkpair (mksym 
"ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"KEYWORD" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mksym "ACL2" "P") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "NEXT-STATEP") (
mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" 
"M") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mksym "ACL2" "Q") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))

];
