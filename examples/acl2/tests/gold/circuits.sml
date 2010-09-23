open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;

val package =
 implode(map chr (cons 65 (cons 67 (cons 76 (cons 50 nil)))));

val events = [

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

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"CREATE-KRIPKE-PRODUCES-CIRCUIT-MODEL") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "ACL2" "CIRCUITP") (mkpair (mksym "ACL2" 
"C") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" 
"CIRCUIT-MODELP") (mkpair (mkpair (mksym "ACL2" "CREATE-KRIPKE") (mkpair (
mksym "ACL2" "C") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))

];
