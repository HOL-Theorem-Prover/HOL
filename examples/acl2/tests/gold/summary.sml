open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;

val package =
 implode(map chr (cons 65 (cons 67 (cons 76 (cons 50 nil)))));

val events = [

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
,

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

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "SUBSET") (mkpair (
mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"ACL2" "SUBSET") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym 
"ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "Y") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "SET-INTERSECT") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "ACL2" "SET-INTERSECT") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "SET-INTERSECT") (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "SET-UNION") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "Y") (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "ACL2" "SET-UNION") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "SET-UNION") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "SET-EQUAL") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "SUBSET") (mkpair (mksym "ACL2" "X") (mkpair (mksym 
"ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"SUBSET") (mkpair (mksym "ACL2" "Y") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

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

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "EVALUATION-EQ") (
mkpair (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "Q") (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "P") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "Q") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "EVALUATION-EQ") (mkpair (mksym "ACL2" "P") (mkpair (mksym 
"ACL2" "Q") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"EVALUATION-EQ-MEMBER-P") (mkpair (mkpair (mksym "ACL2" "ST") (mkpair (mksym 
"ACL2" "STATES") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "EVALUATION-EQ") (mkpair (
mksym "ACL2" "ST") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym 
"ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "ACL2" "EVALUATION-EQ-MEMBER-P") (mkpair (mksym "ACL2" "ST") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"EVALUATION-EQ-MEMBER") (mkpair (mkpair (mksym "ACL2" "ST") (mkpair (mksym 
"ACL2" "STATES") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "EVALUATION-EQ") (mkpair (
mksym "ACL2" "ST") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym 
"ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "EVALUATION-EQ-MEMBER") (mkpair (mksym "ACL2" "ST") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFUN-SK") (mkpair (mksym "ACL2" "STRICT-EVALUATION-P") (
mkpair (mkpair (mksym "ACL2" "ST") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "FORALL") (mkpair (
mkpair (mksym "ACL2" "V") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (
mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (
mksym "ACL2" "V") (mkpair (mksym "ACL2" "ST") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"STRICT-EVALUATION-LIST-P") (mkpair (mkpair (mksym "ACL2" "VARS") (mkpair (
mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (
mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "STRICT-EVALUATION-P") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"STRICT-EVALUATION-LIST-P") (mkpair (mksym "ACL2" "VARS") (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "EVALUATION-P") (
mkpair (mkpair (mksym "ACL2" "ST") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "BOOLEANP") (mkpair (mkpair (
mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "ST") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "EVALUATION-P") (mkpair (mksym "ACL2" "ST") (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"ONLY-EVALUATIONS-P") (mkpair (mkpair (mksym "ACL2" "STATES") (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (
mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "EVALUATION-P") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"ONLY-EVALUATIONS-P") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFUN-SK") (mkpair (mksym "ACL2" "ALL-EVALUATIONS-P") (
mkpair (mkpair (mksym "ACL2" "STATES") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "FORALL") (mkpair (
mkpair (mksym "ACL2" "ST") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "ACL2" "EVALUATION-P") (mkpair (
mksym "ACL2" "ST") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "EVALUATION-EQ-MEMBER-P") (mkpair (mksym "ACL2" 
"ST") (mkpair (mksym "ACL2" "STATES") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"EVALUATION-EQ-SUBSET-P") (mkpair (mkpair (mksym "ACL2" "M-STATES") (mkpair (
mksym "ACL2" "N-STATES") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "M-STATES") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "EVALUATION-EQ-MEMBER-P") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "M-STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "N-STATES") (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ-SUBSET-P") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "M-STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"N-STATES") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"EVALUATION-EQ-SUBSET-TO-MEMBER") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ-SUBSET-P") (mkpair (mksym "ACL2" "M-STATES") (mkpair (mksym 
"ACL2" "N-STATES") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "P") (mkpair (
mksym "ACL2" "M-STATES") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "EVALUATION-EQ-MEMBER-P") (mkpair (mksym "ACL2" "P") (mkpair (mksym 
"ACL2" "N-STATES") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "TRUTHP-LABEL") (
mkpair (mkpair (mksym "ACL2" "LABEL") (mkpair (mksym "ACL2" "S") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "LABEL") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "LABEL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "S") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "TRUTHP-LABEL") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "LABEL") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "S") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "ONLY-TRUTH-P") (
mkpair (mkpair (mksym "ACL2" "STATES") (mkpair (mksym "ACL2" "M") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "TRUTHP-LABEL") (mkpair (
mkpair (mksym "ACL2" "LABEL-OF") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"ONLY-TRUTH-P") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym 
"ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"ALL-TRUTHSP-LABEL") (mkpair (mkpair (mksym "ACL2" "LABEL") (mkpair (mksym 
"ACL2" "S") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (
mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "S") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "MEMBERP") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"LABEL") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "ALL-TRUTHSP-LABEL") (mkpair (mksym "ACL2" 
"LABEL") (mkpair (mksym "ACL2" "S") (mkpair (mkpair (mksym "COMMON-LISP" 
"CDR") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"ONLY-ALL-TRUTHS-P") (mkpair (mkpair (mksym "ACL2" "STATES") (mkpair (mksym 
"ACL2" "M") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ALL-TRUTHSP-LABEL") (
mkpair (mkpair (mksym "ACL2" "LABEL-OF") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "ACL2" "ONLY-ALL-TRUTHS-P") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "M") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"LABEL-SUBSET-VARS") (mkpair (mkpair (mksym "ACL2" "STATES") (mkpair (mksym 
"ACL2" "M") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (mkpair (
mksym "ACL2" "LABEL-OF") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"M") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "LABEL-SUBSET-VARS") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFUN-SK") (mkpair (mksym "ACL2" 
"WELL-FORMED-TRANSITION-P") (mkpair (mkpair (mksym "ACL2" "STATES-M") (mkpair (
mksym "ACL2" "TRANS-M") (mkpair (mksym "ACL2" "STATES-N") (mkpair (mksym 
"ACL2" "TRANS-N") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))))) (
mkpair (mkpair (mksym "ACL2" "FORALL") (mkpair (mkpair (mksym "ACL2" "P") (
mkpair (mksym "ACL2" "Q") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "EVALUATION-EQ") (mkpair (mksym "ACL2" "P") (mkpair (
mksym "ACL2" "Q") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-P") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "P") (mkpair (
mksym "ACL2" "STATES-M") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mksym "ACL2" "Q") (mkpair (mksym "ACL2" "STATES-N") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "EVALUATION-P") (mkpair (mksym "ACL2" 
"Q") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "EVALUATION-EQ-SUBSET-P") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (
mksym "ACL2" "P") (mkpair (mksym "ACL2" "TRANS-M") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mksym "ACL2" "Q") (mkpair (mksym 
"ACL2" "TRANS-N") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"TRANSITION-SUBSET-P") (mkpair (mkpair (mksym "ACL2" "STATES") (mkpair (mksym 
"ACL2" "STATES-PRIME") (mkpair (mksym "ACL2" "TRANS") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (mkpair (
mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym 
"ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "TRANS") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "STATES-PRIME") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "TRANSITION-SUBSET-P") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "STATES-PRIME") (mkpair (
mksym "ACL2" "TRANS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "CIRCUIT-MODELP") (
mkpair (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"ONLY-EVALUATIONS-P") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "KEYWORD" "VARIABLES") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "ALL-EVALUATIONS-P") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "VARIABLES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "STRICT-EVALUATION-LIST-P") (mkpair (mkpair (
mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "KEYWORD" "VARIABLES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" 
"STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ONLY-ALL-TRUTHS-P") (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "KEYWORD" "STATES") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym 
"ACL2" "M") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "VARIABLES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "ONLY-TRUTH-P") (mkpair (mkpair (mksym "ACL2" 
"G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" 
"STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"LABEL-SUBSET-VARS") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "ACL2" "M") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "VARIABLES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "TRANSITION-SUBSET-P") (mkpair (mkpair (mksym 
"ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"KEYWORD" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "TRANSITION") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" 
"INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "CONSP") (mkpair (mkpair (mksym 
"ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"KEYWORD" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "NEXT-STATES-IN-STATES") (mkpair (mksym "ACL2" "M") (mkpair (
mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "KEYWORD" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "C-BISIM-EQUIV") (
mkpair (mkpair (mksym "ACL2" "M") (mkpair (mksym "ACL2" "N") (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "CIRCUIT-MODELP") (mkpair (
mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "CIRCUIT-MODELP") (mkpair (
mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (mksym 
"ACL2" "VARS") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "VARIABLES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (mksym "ACL2" "VARS") (mkpair (
mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "KEYWORD" "VARIABLES") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"WELL-FORMED-TRANSITION-P") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "TRANSITION") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "KEYWORD" "STATES") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "KEYWORD" "TRANSITION") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL"))))))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "WELL-FORMED-TRANSITION-P") (mkpair (mkpair (
mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "KEYWORD" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"N") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" 
"TRANSITION") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "N") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "KEYWORD" "TRANSITION") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "EVALUATION-EQ-SUBSET-P") (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "KEYWORD" "INITIAL-STATES") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "KEYWORD" "INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ-SUBSET-P") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "INITIAL-STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "INITIAL-STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "CIRCUIT-BISIM") (
mkpair (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "M") (mkpair (mksym 
"ACL2" "Q") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL")))))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "CIRCUIT-MODELP") (mkpair (mksym "ACL2" "M") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "CIRCUIT-MODELP") (mkpair (mksym "ACL2" "N") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "P") (mkpair (mkpair (
mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "KEYWORD" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"M") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (
mkpair (mksym "ACL2" "Q") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "WELL-FORMED-TRANSITION-P") (mkpair (mkpair (
mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "KEYWORD" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"M") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" 
"TRANSITION") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "KEYWORD" "TRANSITION") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "WELL-FORMED-TRANSITION-P") (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "KEYWORD" "STATES") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "KEYWORD" "TRANSITION") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" 
"STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "TRANSITION") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ-SUBSET-P") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "INITIAL-STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "INITIAL-STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ-SUBSET-P") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "INITIAL-STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "INITIAL-STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (
mksym "ACL2" "VARS") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "VARIABLES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (mksym "ACL2" "VARS") (mkpair (
mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "KEYWORD" "VARIABLES") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "EVALUATION-EQ") (mkpair (mksym "ACL2" "P") (
mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "FIND-VARIABLES") (
mkpair (mkpair (mksym "ACL2" "EQUATION") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "ATOM") (mkpair (mksym "ACL2" "EQUATION") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (
mkpair (mkpair (mksym "ACL2" "BOOLEANP") (mkpair (mksym "ACL2" "EQUATION") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mksym "ACL2" "EQUATION") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "LEN") (
mkpair (mksym "ACL2" "EQUATION") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "3" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"ACL2" "MEMBERP") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "EQUATION") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mkpair (mksym "ACL2" "&") (mkpair (mksym 
"COMMON-LISP" "+") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" "SET-UNION") (mkpair (
mkpair (mksym "ACL2" "FIND-VARIABLES") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mksym "ACL2" "EQUATION") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "FIND-VARIABLES") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "EQUATION") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" 
"EQUAL") (mkpair (mkpair (mksym "ACL2" "LEN") (mkpair (mksym "ACL2" 
"EQUATION") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "2" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" 
"EQUATION") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "ACL2" "~") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" "FIND-VARIABLES") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "EQUATION") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "ACL2" "DEFUN-SK") (mkpair (mksym "ACL2" 
"CONSISTENT-EQUATION-RECORD-P") (mkpair (mkpair (mksym "ACL2" "VARS") (mkpair (
mksym "ACL2" "EQUATIONS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "FORALL") (mkpair (mkpair (mksym "ACL2" "V") (mkpair (mksym 
"ACL2" "EQUATION") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (
mksym "ACL2" "UNIQUEP") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "MEMBERP") (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "MEMBERP") (
mkpair (mksym "ACL2" "EQUATION") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (
mksym "ACL2" "V") (mkpair (mksym "ACL2" "EQUATIONS") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (
mkpair (mksym "ACL2" "FIND-VARIABLES") (mkpair (mksym "ACL2" "EQUATION") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "CONS-LIST-P") (
mkpair (mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" "EQUATIONS") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" 
"CONSP") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "EQUATIONS") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "CONS-LIST-P") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "EQUATIONS") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "CIRCUITP") (
mkpair (mkpair (mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"ONLY-EVALUATIONS-P") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "INITIAL-STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "C") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "VARIABLES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "STRICT-EVALUATION-LIST-P") (mkpair (mkpair (
mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "KEYWORD" "VARIABLES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "C") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" 
"INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "C") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "UNIQUEP") (mkpair (
mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "KEYWORD" "VARIABLES") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"CONS-LIST-P") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "VARIABLES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "KEYWORD" "EQUATIONS") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "CONSISTENT-EQUATION-RECORD-P") (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "KEYWORD" "VARIABLES") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "KEYWORD" "EQUATIONS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "C") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "ASSIGN-T") (
mkpair (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "ACL2" "S") (mkpair (mksym 
"ACL2" "V") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" 
"ASSIGN-T") (mkpair (mksym "ACL2" "V") (mkpair (mkpair (mksym "COMMON-LISP" 
"CDR") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "ASSIGN-NIL") (
mkpair (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "ACL2" "S") (mkpair (mksym 
"ACL2" "V") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" 
"ASSIGN-NIL") (mkpair (mksym "ACL2" "V") (mkpair (mkpair (mksym "COMMON-LISP" 
"CDR") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"CREATE-ALL-EVALUATIONS") (mkpair (mkpair (mksym "ACL2" "VARS") (mkpair (
mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"STATES") (mkpair (mkpair (mkpair (mksym "COMMON-LISP" "LAMBDA") (mkpair (
mkpair (mksym "ACL2" "REC-STATES") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "BINARY-APPEND") (mkpair (
mkpair (mksym "ACL2" "ASSIGN-T") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "REC-STATES") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"ACL2" "ASSIGN-NIL") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"REC-STATES") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"CREATE-ALL-EVALUATIONS") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"STATES") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "LABEL-FN-OF-ST") (
mkpair (mkpair (mksym "ACL2" "ST") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "ST") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" 
"LABEL-FN-OF-ST") (mkpair (mksym "ACL2" "ST") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "LABEL-FN-OF-ST") (mkpair (mksym "ACL2" "ST") (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "CREATE-LABEL-FN") (
mkpair (mkpair (mksym "ACL2" "STATES") (mkpair (mksym "ACL2" "VARS") (mkpair (
mksym "ACL2" "LABEL") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (
mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"LABEL") (mkpair (mkpair (mksym "ACL2" "CREATE-LABEL-FN") (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "VARS") (mkpair (mkpair (mksym 
"ACL2" "S") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" 
"STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" 
"LABEL-FN-OF-ST") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym 
"ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "LABEL") (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "APPLY-EQUATION") (
mkpair (mkpair (mksym "ACL2" "EQUATION") (mkpair (mksym "ACL2" "ST") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ATOM") (mkpair (mksym "ACL2" "EQUATION") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "BOOLEANP") (mkpair (mksym "ACL2" "EQUATION") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "EQUATION") (mkpair (mkpair (
mksym "ACL2" "G") (mkpair (mksym "ACL2" "EQUATION") (mkpair (mksym "ACL2" 
"ST") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" 
"EQUAL") (mkpair (mkpair (mksym "ACL2" "LEN") (mkpair (mksym "ACL2" 
"EQUATION") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "2" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mkpair (mksym 
"COMMON-LISP" "LAMBDA") (mkpair (mkpair (mksym "ACL2" 
"CASE-DO-NOT-USE-ELSEWHERE") (mkpair (mksym "ACL2" "ST") (mkpair (mksym 
"ACL2" "EQUATION") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQL") (mkpair (
mksym "ACL2" "CASE-DO-NOT-USE-ELSEWHERE") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "ACL2" "~") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (
mkpair (mkpair (mksym "ACL2" "APPLY-EQUATION") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "EQUATION") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "ST") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "EQUATION") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "ST") (mkpair (mksym "ACL2" "EQUATION") (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "LEN") (
mkpair (mksym "ACL2" "EQUATION") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "3" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mkpair (
mksym "COMMON-LISP" "LAMBDA") (mkpair (mkpair (mksym "ACL2" 
"CASE-DO-NOT-USE-ELSEWHERE") (mkpair (mksym "ACL2" "ST") (mkpair (mksym 
"ACL2" "EQUATION") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQL") (mkpair (
mksym "ACL2" "CASE-DO-NOT-USE-ELSEWHERE") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "ACL2" "&") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "APPLY-EQUATION") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "EQUATION") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "ST") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "ACL2" "APPLY-EQUATION") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "EQUATION") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mksym "ACL2" "ST") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQL") (mkpair (
mksym "ACL2" "CASE-DO-NOT-USE-ELSEWHERE") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "+") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "ACL2" "APPLY-EQUATION") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "EQUATION") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "ST") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "ACL2" "APPLY-EQUATION") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mksym "ACL2" "EQUATION") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "ST") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "APPLY-EQUATION") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "EQUATION") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mksym "ACL2" "ST") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mksym "ACL2" "EQUATION") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "ST") (mkpair (mksym "ACL2" 
"EQUATION") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"PRODUCE-NEXT-STATE") (mkpair (mkpair (mksym "ACL2" "VARS") (mkpair (mksym 
"ACL2" "ST") (mkpair (mksym "ACL2" "EQUATIONS") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "ST") (mkpair (mkpair (mksym "ACL2" "S") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "APPLY-EQUATION") (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "EQUATIONS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "ST") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"PRODUCE-NEXT-STATE") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "ST") (
mkpair (mksym "ACL2" "EQUATIONS") (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"CONSISTENT-P-EQUATIONS") (mkpair (mkpair (mksym "ACL2" "VARS") (mkpair (
mksym "ACL2" "EQN") (mkpair (mksym "ACL2" "EQUATIONS") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mkpair (
mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "EQN") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "EQUATIONS") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"ACL2" "CONSISTENT-P-EQUATIONS") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "EQN") (mkpair (mksym "ACL2" "EQUATIONS") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFUN-SK") (mkpair (mksym "ACL2" "NEXT-STATE-IS-OK") (
mkpair (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "Q") (mkpair (mksym 
"ACL2" "VARS") (mkpair (mksym "ACL2" "EQUATIONS") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "ACL2" "EXISTS") (mkpair (mkpair (mksym "ACL2" "EQN") (
mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "CONSISTENT-P-EQUATIONS") (mkpair (mksym "ACL2" 
"VARS") (mkpair (mksym "ACL2" "EQN") (mkpair (mksym "ACL2" "EQUATIONS") (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" "EVALUATION-EQ") (
mkpair (mksym "ACL2" "Q") (mkpair (mkpair (mksym "ACL2" "PRODUCE-NEXT-STATE") (
mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" 
"EQN") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"CREATE-NEXT-STATES-OF-P") (mkpair (mkpair (mksym "ACL2" "P") (mkpair (mksym 
"ACL2" "STATES") (mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" 
"EQUATIONS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (
mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "NEXT-STATE-IS-OK") (mkpair (mksym "ACL2" "P") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" 
"EQUATIONS") (mksym "COMMON-LISP" "NIL")))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"ACL2" "CREATE-NEXT-STATES-OF-P") (mkpair (mksym "ACL2" "P") (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" 
"EQUATIONS") (mksym "COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "CREATE-NEXT-STATES-OF-P") (mkpair (mksym "ACL2" 
"P") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" 
"STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "VARS") (mkpair (
mksym "ACL2" "EQUATIONS") (mksym "COMMON-LISP" "NIL")))))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"CREATE-NEXT-STATES") (mkpair (mkpair (mksym "ACL2" "STATES") (mkpair (mksym 
"ACL2" "STATES-PRIME") (mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" 
"EQUATIONS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (
mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "S") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" 
"CREATE-NEXT-STATES-OF-P") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "STATES-PRIME") (mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" 
"EQUATIONS") (mksym "COMMON-LISP" "NIL")))))) (mkpair (mkpair (mksym "ACL2" 
"CREATE-NEXT-STATES") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"STATES-PRIME") (mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" 
"EQUATIONS") (mksym "COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "CREATE-KRIPKE") (
mkpair (mkpair (mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mkpair (mksym "COMMON-LISP" "LAMBDA") (mkpair (mkpair (mksym "ACL2" 
"VARS") (mkpair (mksym "ACL2" "EQUATIONS") (mkpair (mksym "ACL2" 
"INITIAL-STATES") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mkpair (
mksym "COMMON-LISP" "LAMBDA") (mkpair (mkpair (mksym "ACL2" "STATES") (mkpair (
mksym "ACL2" "EQUATIONS") (mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" 
"INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mkpair (
mksym "COMMON-LISP" "LAMBDA") (mkpair (mkpair (mksym "ACL2" "LABEL-FN") (
mkpair (mksym "ACL2" "EQUATIONS") (mkpair (mksym "ACL2" "VARS") (mkpair (
mksym "ACL2" "STATES") (mkpair (mksym "ACL2" "INITIAL-STATES") (mksym 
"COMMON-LISP" "NIL")))))) (mkpair (mkpair (mkpair (mksym "COMMON-LISP" 
"LAMBDA") (mkpair (mkpair (mksym "ACL2" "TRANSITION") (mkpair (mksym "ACL2" 
"STATES") (mkpair (mksym "ACL2" "INITIAL-STATES") (mkpair (mksym "ACL2" 
"LABEL-FN") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))))) (
mkpair (mkpair (mksym "ACL2" "S") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "KEYWORD" "VARIABLES") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "VARS") (mkpair (mkpair (mksym "ACL2" "S") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "TRANSITION") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "TRANSITION") (mkpair (
mkpair (mksym "ACL2" "S") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "KEYWORD" "LABEL-FN") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mksym "ACL2" "LABEL-FN") (mkpair (mkpair (mksym "ACL2" "S") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "INITIAL-STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "INITIAL-STATES") (mkpair (
mkpair (mksym "ACL2" "S") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "KEYWORD" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "ACL2" "SET-UNION") (mkpair (mksym "ACL2" "INITIAL-STATES") (
mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "CREATE-NEXT-STATES") (mkpair (mkpair (mksym "ACL2" "SET-UNION") (
mkpair (mksym "ACL2" "INITIAL-STATES") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "SET-UNION") (mkpair (
mksym "ACL2" "INITIAL-STATES") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" 
"EQUATIONS") (mksym "COMMON-LISP" "NIL")))))) (mkpair (mksym "ACL2" "STATES") (
mkpair (mksym "ACL2" "INITIAL-STATES") (mkpair (mksym "ACL2" "LABEL-FN") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "CREATE-LABEL-FN") (
mkpair (mkpair (mksym "ACL2" "SET-UNION") (mkpair (mksym "ACL2" 
"INITIAL-STATES") (mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "ACL2" "VARS") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mksym "ACL2" "EQUATIONS") (mkpair (mksym 
"ACL2" "VARS") (mkpair (mksym "ACL2" "STATES") (mkpair (mksym "ACL2" 
"INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))))))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "CREATE-ALL-EVALUATIONS") (mkpair (
mksym "ACL2" "VARS") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" 
"EQUATIONS") (mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" 
"INITIAL-STATES") (mksym "COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "KEYWORD" "VARIABLES") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "KEYWORD" "EQUATIONS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "C") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" 
"INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "C") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "FIND-VARIABLES*") (
mkpair (mkpair (mksym "ACL2" "EQUATION-LIST") (mksym "COMMON-LISP" "NIL")) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "EQUATION-LIST") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "SET-UNION") (mkpair (mkpair (mksym "ACL2" "FIND-VARIABLES") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" 
"EQUATION-LIST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "ACL2" "FIND-VARIABLES*") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "EQUATION-LIST") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"FIND-ALL-VARIABLES-1-PASS") (mkpair (mkpair (mksym "ACL2" "VARS") (mkpair (
mksym "ACL2" "EQUATIONS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "SET-UNION") (mkpair (
mkpair (mksym "ACL2" "FIND-VARIABLES*") (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "EQUATIONS") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"ACL2" "FIND-ALL-VARIABLES-1-PASS") (mkpair (mkpair (mksym "COMMON-LISP" 
"CDR") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mksym "ACL2" "EQUATIONS") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"FIND-ALL-VARIABLES") (mkpair (mkpair (mksym "ACL2" "VARS") (mkpair (mksym 
"ACL2" "VARIABLES") (mkpair (mksym "ACL2" "EQUATIONS") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (mkpair (
mkpair (mksym "ACL2" "UNIQUEP") (mkpair (mksym "ACL2" "VARIABLES") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "NOT") (mkpair (mkpair (mksym "ACL2" "UNIQUEP") (mkpair (mksym 
"ACL2" "VARIABLES") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "NOT") (mkpair (mkpair (mksym "ACL2" "UNIQUEP") (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym "ACL2" 
"UNIQUEP") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (mkpair (
mkpair (mksym "ACL2" "SUBSET") (mkpair (mksym "ACL2" "VARS") (mkpair (mksym 
"ACL2" "VARIABLES") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mksym 
"ACL2" "VARS") (mkpair (mkpair (mkpair (mksym "COMMON-LISP" "LAMBDA") (mkpair (
mkpair (mksym "ACL2" "NEW-VARS") (mkpair (mksym "ACL2" "EQUATIONS") (mkpair (
mksym "ACL2" "VARS") (mkpair (mksym "ACL2" "VARIABLES") (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "NOT") (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (mksym 
"ACL2" "NEW-VARS") (mkpair (mksym "ACL2" "VARIABLES") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"SET-EQUAL") (mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" "NEW-VARS") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "VARS") (mkpair (mkpair (
mksym "ACL2" "FIND-ALL-VARIABLES") (mkpair (mksym "ACL2" "NEW-VARS") (mkpair (
mksym "ACL2" "VARIABLES") (mkpair (mksym "ACL2" "EQUATIONS") (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"SET-UNION") (mkpair (mkpair (mksym "ACL2" "FIND-ALL-VARIABLES-1-PASS") (
mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" "EQUATIONS") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mksym "ACL2" "EQUATIONS") (mkpair (mksym "ACL2" "VARS") (
mkpair (mksym "ACL2" "VARIABLES") (mksym "COMMON-LISP" "NIL")))))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"FIND-ALL-EQUATIONS") (mkpair (mkpair (mksym "ACL2" "VARS") (mkpair (mksym 
"ACL2" "EQUATIONS") (mkpair (mksym "ACL2" "EQ-REC") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "EQ-REC") (mkpair (mkpair (mksym "ACL2" 
"FIND-ALL-EQUATIONS") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" 
"EQUATIONS") (mkpair (mkpair (mksym "ACL2" "S") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "EQUATIONS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" 
"EQ-REC") (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"REMOVE-DUPLICATE-OCCURRENCES") (mkpair (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" 
"X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "ACL2" "REMOVE-DUPLICATE-OCCURRENCES") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" 
"REMOVE-DUPLICATE-OCCURRENCES") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"CORRESPONDING-STATE") (mkpair (mkpair (mksym "ACL2" "INIT") (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "S") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "INIT") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "CORRESPONDING-STATE") (mkpair (mksym "ACL2" "INIT") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"CORRESPONDING-STATES") (mkpair (mkpair (mksym "ACL2" "INITS") (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (
mksym "ACL2" "INITS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mkpair (mksym "ACL2" "CORRESPONDING-STATE") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "INITS") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "ACL2" "CORRESPONDING-STATES") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "INITS") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "CONE-VARIABLES") (
mkpair (mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" "C") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "FIND-ALL-VARIABLES") (
mkpair (mkpair (mksym "ACL2" "SET-INTERSECT") (mkpair (mkpair (mksym "ACL2" 
"REMOVE-DUPLICATE-OCCURRENCES") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "VARIABLES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "VARIABLES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "C") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "EQUATIONS") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"CONE-OF-INFLUENCE-REDUCTION") (mkpair (mkpair (mksym "ACL2" "C") (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mkpair (
mksym "COMMON-LISP" "LAMBDA") (mkpair (mkpair (mksym "ACL2" "VARIABLES") (
mkpair (mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "S") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "KEYWORD" "EQUATIONS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "FIND-ALL-EQUATIONS") (mkpair (mksym "ACL2" "VARIABLES") (mkpair (
mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "KEYWORD" "EQUATIONS") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "S") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"KEYWORD" "INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "CORRESPONDING-STATES") (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" 
"INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "C") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "VARIABLES") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "S") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "VARIABLES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "VARIABLES") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "CONE-VARIABLES") (mkpair (mksym "ACL2" "VARS") (
mkpair (mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym 
"ACL2" "C") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"CONE-OF-INFLUENCE-REDUCTION-IS-CIRCUIT-P") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "ACL2" "CIRCUITP") (mkpair (mksym "ACL2" 
"C") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "CIRCUITP") (
mkpair (mkpair (mksym "ACL2" "CONE-OF-INFLUENCE-REDUCTION") (mkpair (mksym 
"ACL2" "C") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"CONE-OF-INFLUENCE-IS-C-BISIMI-EQUIV") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "ACL2" "CIRCUITP") (mkpair (mksym "ACL2" 
"C") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" 
"C-BISIM-EQUIV") (mkpair (mkpair (mksym "ACL2" "CREATE-KRIPKE") (mkpair (
mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" 
"CREATE-KRIPKE") (mkpair (mkpair (mksym "ACL2" "CONE-OF-INFLUENCE-REDUCTION") (
mkpair (mksym "ACL2" "C") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" 
"CONE-VARIABLES") (mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" "C") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"CREATE-KRIPKE-PRODUCES-CIRCUIT-MODEL") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "ACL2" "CIRCUITP") (mkpair (mksym "ACL2" 
"C") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" 
"CIRCUIT-MODELP") (mkpair (mkpair (mksym "ACL2" "CREATE-KRIPKE") (mkpair (
mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"C-BISIMILAR-INITIAL-STATE-WITNESS-M->N") (mkpair (mkpair (mksym "ACL2" "S") (
mkpair (mksym "ACL2" "M") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ-MEMBER") (mkpair (mksym "ACL2" "S") (mkpair (mkpair (mksym 
"ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"KEYWORD" "INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"C-BISIMILAR-INITIAL-STATE-WITNESS-N->M") (mkpair (mkpair (mksym "ACL2" "M") (
mkpair (mksym "ACL2" "S") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ-MEMBER") (mkpair (mksym "ACL2" "S") (mkpair (mkpair (mksym 
"ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"KEYWORD" "INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"C-BISIMILAR-TRANSITION-WITNESS-M->N") (mkpair (mkpair (mksym "ACL2" "P") (
mkpair (mksym "ACL2" "R") (mkpair (mksym "ACL2" "M") (mkpair (mksym "ACL2" 
"Q") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))))))) (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ-MEMBER") (mkpair (mksym "ACL2" "R") (mkpair (mkpair (mksym 
"ACL2" "G") (mkpair (mksym "ACL2" "Q") (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" 
"TRANSITION") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "N") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"C-BISIMILAR-TRANSITION-WITNESS-N->M") (mkpair (mkpair (mksym "ACL2" "P") (
mkpair (mksym "ACL2" "M") (mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" 
"R") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))))))) (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ-MEMBER") (mkpair (mksym "ACL2" "R") (mkpair (mkpair (mksym 
"ACL2" "G") (mkpair (mksym "ACL2" "P") (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" 
"TRANSITION") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"C-BISIMILAR-EQUIV-IMPLIES-INIT->INIT-M->N") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "C-BISIM-EQUIV") (mkpair (mksym "ACL2" "M") (mkpair (mksym "ACL2" "N") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "S") (mkpair (mkpair (mksym 
"ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"KEYWORD" "INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "ACL2" "MEMBERP") (mkpair (mkpair (mksym "ACL2" 
"C-BISIMILAR-INITIAL-STATE-WITNESS-M->N") (mkpair (mksym "ACL2" "S") (mkpair (
mksym "ACL2" "M") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL")))))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" 
"INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "N") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"C-BISIMILAR-EQUIV-IMPLIES-INIT->INIT-N->M") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "C-BISIM-EQUIV") (mkpair (mksym "ACL2" "M") (mkpair (mksym "ACL2" "N") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "S") (mkpair (mkpair (mksym 
"ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"KEYWORD" "INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "ACL2" "MEMBERP") (mkpair (mkpair (mksym "ACL2" 
"C-BISIMILAR-INITIAL-STATE-WITNESS-N->M") (mkpair (mksym "ACL2" "M") (mkpair (
mksym "ACL2" "S") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL")))))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" 
"INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"C-BISIMILAR-EQUIV-IMPLIES-BISIMILAR-INITIAL-STATES-M->N") (mkpair (mkpair (
mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "C-BISIM-EQUIV") (mkpair (mksym "ACL2" "M") (mkpair (
mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "S") (mkpair (
mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "KEYWORD" "INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "ACL2" "CIRCUIT-BISIM") (mkpair (mksym "ACL2" "S") (
mkpair (mksym "ACL2" "M") (mkpair (mkpair (mksym "ACL2" 
"C-BISIMILAR-INITIAL-STATE-WITNESS-M->N") (mkpair (mksym "ACL2" "S") (mkpair (
mksym "ACL2" "M") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL")))))) (mkpair (mksym "ACL2" "N") (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"C-BISIMILAR-EQUIV-IMPLIES-BISIMILAR-INITIAL-STATES-N->M") (mkpair (mkpair (
mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "C-BISIM-EQUIV") (mkpair (mksym "ACL2" "M") (mkpair (
mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "S") (mkpair (
mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "KEYWORD" "INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "ACL2" "CIRCUIT-BISIM") (mkpair (mkpair (mksym "ACL2" 
"C-BISIMILAR-INITIAL-STATE-WITNESS-N->M") (mkpair (mksym "ACL2" "M") (mkpair (
mksym "ACL2" "S") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL")))))) (mkpair (mksym "ACL2" "M") (mkpair (mksym 
"ACL2" "S") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))))))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"C-BISIMILAR-STATES-HAVE-LABELS-EQUAL") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "ACL2" "CIRCUIT-BISIM") (mkpair (mksym 
"ACL2" "P") (mkpair (mksym "ACL2" "M") (mkpair (mksym "ACL2" "Q") (mkpair (
mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))))) (
mkpair (mkpair (mksym "ACL2" "SET-EQUAL") (mkpair (mkpair (mksym "ACL2" 
"SET-INTERSECT") (mkpair (mkpair (mksym "ACL2" "LABEL-OF") (mkpair (mksym 
"ACL2" "Q") (mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"ACL2" "SET-INTERSECT") (mkpair (mkpair (mksym "ACL2" "LABEL-OF") (mkpair (
mksym "ACL2" "P") (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"C-BISIMILAR-WITNESS-MEMBER-OF-STATES-M->N") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "CIRCUIT-BISIM") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "M") (
mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL"))))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "NEXT-STATEP") (mkpair (
mksym "ACL2" "P") (mkpair (mksym "ACL2" "R") (mkpair (mksym "ACL2" "M") (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" "MEMBERP") (
mkpair (mksym "ACL2" "R") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mkpair (mksym "ACL2" "C-BISIMILAR-TRANSITION-WITNESS-M->N") (mkpair (mksym 
"ACL2" "P") (mkpair (mksym "ACL2" "R") (mkpair (mksym "ACL2" "M") (mkpair (
mksym "ACL2" "Q") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL")))))))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"C-BISIMILAR-WITNESS-MEMBER-OF-STATES-N->M") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "CIRCUIT-BISIM") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "M") (
mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL"))))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "NEXT-STATEP") (mkpair (
mksym "ACL2" "Q") (mkpair (mksym "ACL2" "R") (mkpair (mksym "ACL2" "N") (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" "MEMBERP") (
mkpair (mksym "ACL2" "R") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mkpair (mksym "ACL2" "C-BISIMILAR-TRANSITION-WITNESS-N->M") (mkpair (mksym 
"ACL2" "P") (mkpair (mksym "ACL2" "M") (mkpair (mksym "ACL2" "Q") (mkpair (
mksym "ACL2" "R") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL")))))))) (mkpair (mkpair (mksym "ACL2" "G") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"C-BISIMILAR-WITNESS-PRODUCES-BISIMILAR-STATES-M->N") (mkpair (mkpair (mksym 
"ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (
mksym "ACL2" "CIRCUIT-BISIM") (mkpair (mksym "ACL2" "P") (mkpair (mksym 
"ACL2" "M") (mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "N") (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))))) (mkpair (mkpair (mksym 
"ACL2" "NEXT-STATEP") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "R") (
mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "CIRCUIT-BISIM") (mkpair (mksym "ACL2" "R") (mkpair (mksym "ACL2" "M") (
mkpair (mkpair (mksym "ACL2" "C-BISIMILAR-TRANSITION-WITNESS-M->N") (mkpair (
mksym "ACL2" "P") (mkpair (mksym "ACL2" "R") (mkpair (mksym "ACL2" "M") (
mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL")))))))) (mkpair (mksym "ACL2" "N") (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"C-BISIMILAR-WITNESS-PRODUCES-BISIMILAR-STATES-N->M") (mkpair (mkpair (mksym 
"ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (
mksym "ACL2" "CIRCUIT-BISIM") (mkpair (mksym "ACL2" "P") (mkpair (mksym 
"ACL2" "M") (mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "N") (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))))) (mkpair (mkpair (mksym 
"ACL2" "NEXT-STATEP") (mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "R") (
mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "CIRCUIT-BISIM") (mkpair (mkpair (mksym "ACL2" 
"C-BISIMILAR-TRANSITION-WITNESS-N->M") (mkpair (mksym "ACL2" "P") (mkpair (
mksym "ACL2" "M") (mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "R") (
mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL")))))))) (mkpair (mksym "ACL2" "M") (mkpair (mksym "ACL2" "R") (mkpair (
mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"C-BISIMILAR-WITNESS-MATCHES-TRANSITION-M->N") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "CIRCUIT-BISIM") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "M") (
mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL"))))))) (mkpair (mkpair (mksym "ACL2" 
"NEXT-STATEP") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "R") (mkpair (
mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "NEXT-STATEP") (mkpair (mksym "ACL2" "Q") (mkpair (mkpair (mksym 
"ACL2" "C-BISIMILAR-TRANSITION-WITNESS-M->N") (mkpair (mksym "ACL2" "P") (
mkpair (mksym "ACL2" "R") (mkpair (mksym "ACL2" "M") (mkpair (mksym "ACL2" 
"Q") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL")))))))) (mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"C-BISIMILAR-WITNESS-MATCHES-TRANSITION-N->M") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "CIRCUIT-BISIM") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "M") (
mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL"))))))) (mkpair (mkpair (mksym "ACL2" 
"NEXT-STATEP") (mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "R") (mkpair (
mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "NEXT-STATEP") (mkpair (mksym "ACL2" "P") (mkpair (mkpair (mksym 
"ACL2" "C-BISIMILAR-TRANSITION-WITNESS-N->M") (mkpair (mksym "ACL2" "P") (
mkpair (mksym "ACL2" "M") (mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" 
"R") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL")))))))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))

];
