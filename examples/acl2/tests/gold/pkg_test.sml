open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;

val package =
 implode(map chr 
(cons 77 (cons 89 (cons 45 (cons 80 (cons 75 (cons 71 nil)))))));

val events = [

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "MY-PKG" "F1") (mkpair (
mkpair (mksym "MY-PKG" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mksym "MY-PKG" "X") (mkpair (mksym 
"MY-PKG" "X") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "MY-PKG" "F2") (mkpair (
mkpair (mksym "MY-PKG" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "ACL2" "BINARY-APPEND") (mkpair (mksym "MY-PKG" "X") (mkpair (mksym 
"MY-PKG" "X") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "MY-PKG" "CONSTS") (
mkpair (mksym "COMMON-LISP" "NIL") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mkpair (mksym "MY-PKG" "X") (mkpair (mksym "COMMON-LISP" 
"DEFUN") (mkpair (mksym "COMMON-LISP" "CONS") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "TEST0") (mkpair (
mkpair (mkpair (mksym "COMMON-LISP" "LAMBDA") (mkpair (mkpair (mksym "ACL2" 
"LST") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "MY-PKG" "X") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "ACL2" "X") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "LST") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "DEFUN") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "DEFUN") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" 
"LST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "DEFUN") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "CONS") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "CONS") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "CONS") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
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
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "MY-PKG" "CONSTS") (mksym "COMMON-LISP" 
"NIL")) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "TEST1A") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" 
"SYMBOL-PACKAGE-NAME") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "MY-PKG" "C") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mk_chars_str (
chars_to_string (cons 77 (cons 89 (cons 45 (cons 80 (cons 75 (cons 71 nil)))))))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "TEST1B") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" 
"SYMBOL-NAME") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"MY-PKG" "C") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mk_chars_str (
chars_to_string (cons 67 nil))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "TEST2A") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" 
"SYMBOL-PACKAGE-NAME") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "DEFUN") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mk_chars_str (chars_to_string (cons 67 (cons 79 (cons 77 (cons 77 (cons 79 (
cons 78 (cons 45 (cons 76 (cons 73 (cons 83 (cons 80 nil))))))))))))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "TEST2B") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" 
"SYMBOL-NAME") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "DEFUN") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mk_chars_str (
chars_to_string (cons 68 (cons 69 (cons 70 (cons 85 (cons 78 nil))))))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "TEST3A") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" 
"SYMBOL-PACKAGE-NAME") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "MY-PKG" "defun") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mk_chars_str (
chars_to_string (cons 77 (cons 89 (cons 45 (cons 80 (cons 75 (cons 71 nil)))))))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "TEST3B") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" 
"SYMBOL-NAME") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"MY-PKG" "defun") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mk_chars_str (
chars_to_string (cons 100 (cons 101 (cons 102 (cons 117 (cons 110 nil))))))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "TEST4") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "ACL2" 
"INTERN-IN-PACKAGE-OF-SYMBOL") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mk_chars_str (chars_to_string (cons 68 (cons 69 (cons 70 (cons 85 (
cons 78 nil))))))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "MY-PKG" "C") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"INTERN-IN-PACKAGE-OF-SYMBOL") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mk_chars_str (chars_to_string (cons 68 (cons 69 (cons 70 (cons 85 (
cons 78 nil))))))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "C") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "TEST5") (mkpair (
mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym "COMMON-LISP" 
"EQUAL") (mkpair (mkpair (mksym "ACL2" "INTERN-IN-PACKAGE-OF-SYMBOL") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mk_chars_str (chars_to_string (
cons 100 (cons 101 (cons 102 (cons 117 (cons 110 nil))))))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "MY-PKG" "C") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "INTERN-IN-PACKAGE-OF-SYMBOL") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mk_chars_str (chars_to_string (cons 100 (
cons 101 (cons 102 (cons 117 (cons 110 nil))))))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "C") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "ACL2" "TEST6") (mkpair (
mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym "COMMON-LISP" 
"EQUAL") (mkpair (mkpair (mksym "ACL2" "INTERN-IN-PACKAGE-OF-SYMBOL") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mk_chars_str (chars_to_string (
cons 68 nil))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "MY-PKG" "C") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"INTERN-IN-PACKAGE-OF-SYMBOL") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mk_chars_str (chars_to_string (cons 68 nil))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "C") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "MY-PKG" "FUN0") (mkpair (
mksym "COMMON-LISP" "NIL") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mkpair (mksym "MY-PKG" "A") (mkpair (mksym "COMMON-LISP" "DEFUN") (
mkpair (mksym "MY-PKG" "B") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "MY-PKG" "FUN1") (mkpair (
mksym "COMMON-LISP" "NIL") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mkpair (mksym "MY-PKG" "A") (mkpair (mksym "COMMON-LISP" "DEFUN") (
mkpair (mksym "MY-PKG" "B") (mksym "MY-PKG" "C")))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "MY-PKG" "FUN0-THM") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "MY-PKG" "FUN0") (
mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "MY-PKG" "A") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"DEFUN") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"CONS") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "MY-PKG" 
"B") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "MY-PKG" "FUN1-THM") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "MY-PKG" "FUN1") (
mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "MY-PKG" "A") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"DEFUN") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"CONS") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "MY-PKG" 
"B") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "MY-PKG" "C") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))

];
