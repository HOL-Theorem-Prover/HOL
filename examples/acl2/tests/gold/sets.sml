open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;

val package =
 implode(map chr (cons 65 (cons 67 (cons 76 (cons 50 nil)))));

val events = [

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

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "SUBSET-IS-REFLEXIVE") (
mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (mksym "ACL2" "X") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "SUBSET-IS-TRANSITIVE") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (mksym "ACL2" "X") (
mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "SUBSET") (mkpair (mksym "ACL2" "Y") (mkpair (mksym "ACL2" "Z") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (
mksym "ACL2" "X") (mkpair (mksym "ACL2" "Z") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"SUBSET-OF-EMPTY-IS-EMPTY") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (
mkpair (mkpair (mksym "COMMON-LISP" "CONSP") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "SUBSET") (mkpair (mksym "ACL2" "Y") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (mkpair (
mkpair (mksym "COMMON-LISP" "CONSP") (mkpair (mksym "ACL2" "Y") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"SET-EQUAL-IS-AN-EQUIVALENCE") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "BOOLEANP") (mkpair (mkpair (mksym "ACL2" 
"SET-EQUAL") (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "SET-EQUAL") (mkpair (mksym 
"ACL2" "X") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "ACL2" "SET-EQUAL") (mkpair (mksym "ACL2" "X") (mkpair (
mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"ACL2" "SET-EQUAL") (mkpair (mksym "ACL2" "Y") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "SET-EQUAL") (mkpair (mksym "ACL2" "X") (mkpair (mksym 
"ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"SET-EQUAL") (mkpair (mksym "ACL2" "Y") (mkpair (mksym "ACL2" "Z") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "ACL2" "SET-EQUAL") (mkpair (mksym "ACL2" 
"X") (mkpair (mksym "ACL2" "Z") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"SUBSET-IS-ANTISYMMETRIC") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "SUBSET") (
mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (mksym "ACL2" "Y") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "SET-EQUAL") (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"INTERSECT-IS-A-SUBSET-1") (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (
mkpair (mksym "ACL2" "SET-INTERSECT") (mkpair (mksym "ACL2" "X") (mkpair (
mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"INTERSECT-IS-A-SUBSET-2") (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (
mkpair (mksym "ACL2" "SET-INTERSECT") (mkpair (mksym "ACL2" "X") (mkpair (
mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "Y") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "UNION-IS-A-SUBSET-1") (
mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (mksym "ACL2" "X") (mkpair (
mkpair (mksym "ACL2" "SET-UNION") (mkpair (mksym "ACL2" "X") (mkpair (mksym 
"ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "UNION-IS-A-SUBSET-2") (
mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (mksym "ACL2" "Y") (mkpair (
mkpair (mksym "ACL2" "SET-UNION") (mkpair (mksym "ACL2" "X") (mkpair (mksym 
"ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"SUPERSET-CONTAINS-EVERYTHING") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"MEMBERP") (mkpair (mksym "ACL2" "E") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (
mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "E") (mkpair (mksym 
"ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "SUBSET-OF-NIL-IS-NIL") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym 
"COMMON-LISP" "CONSP") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (
mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym "COMMON-LISP" 
"CONSP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "PROPER-SUBSET") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "SUBSET") (mkpair (mksym "ACL2" "X") (mkpair (mksym 
"ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "NOT") (mkpair (mkpair (mksym "ACL2" "SUBSET") (mkpair (mksym 
"ACL2" "Y") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"PROPER-SUBSET-IS-IRREFLEXIVE") (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (
mkpair (mkpair (mksym "ACL2" "PROPER-SUBSET") (mkpair (mksym "ACL2" "X") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"PROPER-SUBSET-IS-TRANSITIVE") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"PROPER-SUBSET") (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "PROPER-SUBSET") (
mkpair (mksym "ACL2" "Y") (mkpair (mksym "ACL2" "Z") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "ACL2" "PROPER-SUBSET") (mkpair (mksym "ACL2" "X") (
mkpair (mksym "ACL2" "Z") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"PROPER-SUBSET-IS-STRONGER-THAN-SUBSET") (mkpair (mkpair (mksym "ACL2" 
"IMPLIES") (mkpair (mkpair (mksym "ACL2" "PROPER-SUBSET") (mkpair (mksym 
"ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "ACL2" "SUBSET") (mkpair (mksym "ACL2" "X") (mkpair (mksym 
"ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))

];
