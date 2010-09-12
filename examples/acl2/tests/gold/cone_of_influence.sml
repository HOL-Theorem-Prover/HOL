open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;

val package =
 implode(map chr (cons 65 (cons 67 (cons 76 (cons 50 nil)))));

val events = [

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

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "DEL") (mkpair (
mkpair (mksym "ACL2" "E") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "E") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "ACL2" "DEL") (mkpair (mksym "ACL2" "E") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" 
"INDUCTION-HINT-FOR-LEN-<=") (mkpair (mkpair (mksym "ACL2" "X") (mkpair (
mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mksym "ACL2" "Y") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "INDUCTION-HINT-FOR-LEN-<=") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "DEL") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
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
"EVALUATION-EQ-MEMBERP-FROM-ALL-EVALUATIONS-P") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "ALL-EVALUATIONS-P") (mkpair (mksym "ACL2" "STATES-CONE") (mkpair (
mksym "ACL2" "VARS-CONE") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "EVALUATION-P") (
mkpair (mksym "ACL2" "S") (mkpair (mksym "ACL2" "VARS-CONE") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "CONSISTENT-P-EQUATIONS") (mkpair (mksym "ACL2" 
"VARS-CONE") (mkpair (mksym "ACL2" "EQN") (mkpair (mksym "ACL2" 
"EQUATIONS-CONE") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "EVALUATION-EQ") (mkpair (mksym "ACL2" "S") (mkpair (mkpair (mksym 
"ACL2" "PRODUCE-NEXT-STATE") (mkpair (mksym "ACL2" "VARS-CONE") (mkpair (
mksym "ACL2" "Q") (mkpair (mksym "ACL2" "EQN") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mksym "ACL2" "VARS-CONE") (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "EVALUATION-EQ-MEMBER-P") (mkpair (mksym "ACL2" "S") (mkpair (mkpair (
mksym "ACL2" "CREATE-NEXT-STATES-OF-P") (mkpair (mksym "ACL2" "Q") (mkpair (
mksym "ACL2" "STATES-CONE") (mkpair (mksym "ACL2" "VARS-CONE") (mkpair (mksym 
"ACL2" "EQUATIONS-CONE") (mksym "COMMON-LISP" "NIL")))))) (mkpair (mksym 
"ACL2" "VARS-CONE") (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
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

];
