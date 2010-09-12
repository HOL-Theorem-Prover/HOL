open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;

val package =
 implode(map chr (cons 65 (cons 67 (cons 76 (cons 50 nil)))));

val events = [

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

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"EVALUATION-EQ-IS-SYMMETRIC") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "ACL2" "EVALUATION-EQ") (mkpair (mksym "ACL2" "P") (
mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "ACL2" "EVALUATION-EQ") (mkpair (mksym 
"ACL2" "Q") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))
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

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "MEMBER-IS-MEMBERP") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ-MEMBER-P") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" 
"STATES") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ-MEMBER") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" 
"STATES") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"MEMBER-IS-EVALUATION-EQ") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "ACL2" "EVALUATION-EQ-MEMBER-P") (mkpair (mksym "ACL2" "P") (
mkpair (mksym "ACL2" "STATES") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" "EVALUATION-EQ") (
mkpair (mksym "ACL2" "P") (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ-MEMBER") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" 
"STATES") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
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

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"STRICT-EVALUATION-P-EXPANDED") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"STRICT-EVALUATION-P") (mkpair (mksym "ACL2" "ST") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"NOT") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "V") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym 
"ACL2" "G") (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" "ST") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
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

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"ALL-TRUTHSP-LABEL-EXPANDED") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"ALL-TRUTHSP-LABEL") (mkpair (mksym "ACL2" "LABEL") (mkpair (mksym "ACL2" "S") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mksym "ACL2" "V") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" 
"G") (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" "S") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "V") (mkpair (mksym 
"ACL2" "LABEL") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))
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

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"LABEL-SUBSET-SUBSET-REDUCTION") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"LABEL-SUBSET-VARS") (mkpair (mksym "ACL2" "STATES") (mkpair (mksym "ACL2" 
"M") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "P") (mkpair (mksym 
"ACL2" "STATES") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "SUBSET") (mkpair (mkpair (mksym "ACL2" "LABEL-OF") (mkpair (mksym 
"ACL2" "P") (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
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

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"WELL-FORMED-TRANSITION-P-EXPANDED") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"WELL-FORMED-TRANSITION-P") (mkpair (mksym "ACL2" "STATES-M") (mkpair (mksym 
"ACL2" "TRANS-M") (mkpair (mksym "ACL2" "STATES-N") (mkpair (mksym "ACL2" 
"TRANS-N") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "Q") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "EVALUATION-P") (
mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "MEMBERP") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "STATES-M") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "Q") (mkpair (
mksym "ACL2" "STATES-N") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "EVALUATION-P") (mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ-SUBSET-P") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mksym 
"ACL2" "P") (mkpair (mksym "ACL2" "TRANS-M") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mksym "ACL2" "Q") (mkpair (mksym 
"ACL2" "TRANS-N") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
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

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"TRANSITION-SUBSET-P-EXPANDED") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"TRANSITION-SUBSET-P") (mkpair (mksym "ACL2" "STATES") (mkpair (mksym "ACL2" 
"STATES-PRIME") (mkpair (mksym "ACL2" "TRANS") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"MEMBERP") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mksym "ACL2" "R") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mksym "ACL2" 
"P") (mkpair (mksym "ACL2" "TRANS") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "R") (mkpair (
mksym "ACL2" "STATES-PRIME") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
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

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"ALL-EVALUATIONS-CONSIDERS-AN-EVALUATION-A-MEMBER") (mkpair (mkpair (mksym 
"ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (
mksym "ACL2" "EVALUATION-P") (mkpair (mksym "ACL2" "ST") (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"ALL-EVALUATIONS-P") (mkpair (mksym "ACL2" "STATES") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ-MEMBER-P") (mkpair (mksym "ACL2" "ST") (mkpair (mksym "ACL2" 
"STATES") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"TRUTHP-LABEL-FROM-ONLY-TRUTHP") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"ONLY-TRUTH-P") (mkpair (mksym "ACL2" "STATES") (mkpair (mksym "ACL2" "M") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "MEMBERP") (
mkpair (mksym "ACL2" "S") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "ACL2" "TRUTHP-LABEL") (mkpair (mkpair (
mksym "ACL2" "LABEL-OF") (mkpair (mksym "ACL2" "S") (mkpair (mksym "ACL2" "M") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "S") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"ALL-TRUTHS-P-FROM-ONLY-ALL-TRUTHS-P") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "ONLY-ALL-TRUTHS-P") (mkpair (mksym "ACL2" "STATES") (mkpair (mksym 
"ACL2" "M") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "S") (mkpair (
mksym "ACL2" "STATES") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "ALL-TRUTHSP-LABEL") (mkpair (mkpair (mksym "ACL2" "LABEL-OF") (mkpair (
mksym "ACL2" "S") (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "ACL2" "S") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"MEMBERP-TO-INTERSECT-REDUCTION") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "V") (mkpair (
mkpair (mksym "ACL2" "SET-INTERSECT") (mkpair (mksym "ACL2" "X") (mkpair (
mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"MEMBERP") (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mksym "ACL2" "V") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"EVALUATION-EQ-VARS-REDUCTION") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "Q") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mksym "ACL2" "V") (mkpair (mksym 
"ACL2" "P") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" "Q") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"VARIABLES-IN-LABEL-ARE-T-IN-Q") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"MEMBERP") (mkpair (mksym "ACL2" "V") (mkpair (mkpair (mksym "ACL2" 
"SET-INTERSECT") (mkpair (mksym "ACL2" "LABEL") (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "TRUTHP-LABEL") (
mkpair (mksym "ACL2" "LABEL") (mkpair (mksym "ACL2" "P") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "EVALUATION-EQ") (mkpair (mksym 
"ACL2" "P") (mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "ACL2" "G") (mkpair (mksym "ACL2" "V") (mkpair (mksym 
"ACL2" "Q") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"ONLY-TRUTHSP-AND-SUBSET-TO-SUBSET") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mksym 
"ACL2" "V") (mkpair (mksym "ACL2" "Q") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym 
"ACL2" "V") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"SUBSET") (mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" "VARIABLES") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"ALL-TRUTHSP-LABEL") (mkpair (mksym "ACL2" "LABEL") (mkpair (mksym "ACL2" "Q") (
mkpair (mksym "ACL2" "VARIABLES") (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "MEMBERP") (mkpair (mksym "ACL2" "V") (mkpair (mksym "ACL2" "LABEL") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"TRUTHP-LABEL-TO-SUBSET") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (
mkpair (mksym "ACL2" "V") (mkpair (mkpair (mksym "ACL2" "SET-INTERSECT") (
mkpair (mksym "ACL2" "LP") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "ACL2" "TRUTHP-LABEL") (mkpair (mksym "ACL2" 
"LP") (mkpair (mksym "ACL2" "P") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "Q") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (
mksym "ACL2" "VARS") (mkpair (mksym "ACL2" "VARIABLES") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "ALL-TRUTHSP-LABEL") (mkpair (mksym 
"ACL2" "LQ") (mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "VARIABLES") (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mksym "ACL2" "V") (mkpair (mksym "ACL2" "LQ") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"TRUTHP-LABEL-IS-A-SUBSET") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"TRUTHP-LABEL") (mkpair (mksym "ACL2" "LP") (mkpair (mksym "ACL2" "P") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "EVALUATION-EQ") (mkpair (mksym "ACL2" "P") (mkpair (
mksym "ACL2" "Q") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"SUBSET") (mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" "VARIABLES") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"ALL-TRUTHSP-LABEL") (mkpair (mksym "ACL2" "LQ") (mkpair (mksym "ACL2" "Q") (
mkpair (mksym "ACL2" "VARIABLES") (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "SUBSET") (mkpair (mkpair (mksym "ACL2" "SET-INTERSECT") (mkpair (
mksym "ACL2" "LP") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "ACL2" "LQ") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
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
"EVALUATIONP-FOR-SUBSET") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-P") (mkpair (mksym "ACL2" "ST") (mkpair (mksym "ACL2" "VARIABLES") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (
mksym "ACL2" "VARS") (mkpair (mksym "ACL2" "VARIABLES") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "ACL2" "EVALUATION-P") (mkpair (mksym "ACL2" "ST") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"EVALUATION-P-ONLY-EVALUATIONS-REDUCTION") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "ONLY-EVALUATIONS-P") (mkpair (mksym "ACL2" "STATES") (mkpair (mksym 
"ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"MEMBERP") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "STATES") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "ACL2" "EVALUATION-P") (mkpair (mksym 
"ACL2" "P") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"R-IS-EVALUATION-EQ-MEMBER-P") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"EVALUATION-EQ") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "Q") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"WELL-FORMED-TRANSITION-P") (mkpair (mksym "ACL2" "STATES-M") (mkpair (mksym 
"ACL2" "TRANS-M") (mkpair (mksym "ACL2" "STATES-N") (mkpair (mksym "ACL2" 
"TRANS-N") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"MEMBERP") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "STATES-M") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "Q") (mkpair (
mksym "ACL2" "STATES-N") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "EVALUATION-P") (
mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"ACL2" "EVALUATION-P") (mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"MEMBERP") (mkpair (mksym "ACL2" "R") (mkpair (mkpair (mksym "ACL2" "G") (
mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "TRANS-M") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
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
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "EVALUATION-EQ-MEMBER-P") (mkpair (mksym "ACL2" "R") (mkpair (mkpair (
mksym "ACL2" "G") (mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "TRANS-N") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "VARS") (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))
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
