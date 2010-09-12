open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;

val package =
 implode(map chr (cons 65 (cons 67 (cons 76 (cons 50 nil)))));

val events = [

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"RANGE-TRANSITION-RELATION") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (
mkpair (mksym "ACL2" "P") (mkpair (mkpair (mksym "ACL2" "G") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" "STATES") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "NEXT-STATEP") (mkpair (mksym "ACL2" "P") (
mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "ACL2" "CIRCUIT-MODELP") (mkpair (mksym 
"ACL2" "M") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "MEMBERP") (mkpair (mksym "ACL2" "Q") (mkpair (mkpair (mksym "ACL2" 
"G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "KEYWORD" 
"STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "M") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"SUBSET-IMPLIES-MEMBERP") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "SUBSET") (
mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "A") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"ACL2" "MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "Y") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"INITIAL-STATE-IS-STATE") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" 
"CIRCUIT-MODELP") (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "S0") (mkpair (
mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "KEYWORD" "INITIAL-STATES") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "S0") (mkpair (
mkpair (mksym "ACL2" "G") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "KEYWORD" "STATES") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "MEMBERP-SET-UNION") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" 
"MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym "ACL2" 
"SET-UNION") (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym 
"ACL2" "A") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mksym 
"ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "Y") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "MEMBERP-SET-INTERSECT") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" 
"MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym "ACL2" 
"SET-INTERSECT") (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym 
"ACL2" "A") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mksym 
"ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"SUBSET-PRESERVES-MEMBERP") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "SUBSET") (
mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "A") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mksym "ACL2" "A") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" 
"SET-EQUAL-IMPLIES-EQUAL-MEMBERP") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "ACL2" "SET-EQUAL") (mkpair (mksym "ACL2" "X") (mkpair (
mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mksym 
"ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mksym "ACL2" "Y") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "BISIM-LEMMA-1-LEMMA") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "ACL2" 
"CIRCUIT-BISIM") (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "M") (
mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" 
"VARS") (mksym "COMMON-LISP" "NIL"))))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mksym "ACL2" "A") (mkpair (mkpair (mksym "ACL2" "SET-INTERSECT") (mkpair (
mkpair (mksym "ACL2" "LABEL-OF") (mkpair (mksym "ACL2" "P") (mkpair (mksym 
"ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "ACL2" "VARS") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "A") (mkpair (mkpair (mksym 
"ACL2" "SET-INTERSECT") (mkpair (mkpair (mksym "ACL2" "LABEL-OF") (mkpair (
mksym "ACL2" "Q") (mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "BISIM-LEMMA-1") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (mksym "ACL2" "A") (
mkpair (mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "ACL2" "CIRCUIT-BISIM") (mkpair (mksym "ACL2" "P") (mkpair (mksym 
"ACL2" "M") (mkpair (mksym "ACL2" "Q") (mkpair (mksym "ACL2" "N") (mkpair (
mksym "ACL2" "VARS") (mksym "COMMON-LISP" "NIL"))))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mksym "ACL2" "A") (mkpair (mkpair (mksym "ACL2" "LABEL-OF") (mkpair (mksym 
"ACL2" "P") (mkpair (mksym "ACL2" "M") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "MEMBERP") (mkpair (
mksym "ACL2" "A") (mkpair (mkpair (mksym "ACL2" "LABEL-OF") (mkpair (mksym 
"ACL2" "Q") (mkpair (mksym "ACL2" "N") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))

];
