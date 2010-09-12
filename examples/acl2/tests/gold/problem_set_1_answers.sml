open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;

val package =
 implode(map chr (cons 77 (cons 49 nil)));

val events = [

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "PUSH") (mkpair (
mkpair (mksym "M1" "X") (mkpair (mksym "M1" "Y") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "X") (mkpair (
mksym "M1" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "TOP") (mkpair (
mkpair (mksym "M1" "STACK") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "M1" "STACK") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "POP") (mkpair (
mkpair (mksym "M1" "STACK") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mksym "M1" "STACK") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "NTH") (mkpair (
mkpair (mksym "M1" "N") (mkpair (mksym "COMMON-LISP" "LIST") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "ZP") (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym 
"COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "NTH") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "-1" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "COMMON-LISP" "LIST") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "MAKE-STATE") (
mkpair (mkpair (mksym "M1" "PC") (mkpair (mksym "M1" "LOCALS") (mkpair (mksym 
"M1" "STACK") (mkpair (mksym "M1" "PROGRAM") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "PC") (mkpair (
mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "LOCALS") (mkpair (
mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "STACK") (mkpair (
mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "PROGRAM") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "PC") (mkpair (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" 
"1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "LOCALS") (mkpair (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "1" 
"1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "STACK") (mkpair (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "2" 
"1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "PROGRAM") (mkpair (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "3" 
"1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "OP-CODE") (mkpair (
mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "ARG1") (mkpair (
mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" 
"INST") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "ARG2") (mkpair (
mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "2" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" 
"INST") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "ARG3") (mkpair (
mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "3" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" 
"INST") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "LEN") (mkpair (
mkpair (mksym "M1" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (
mksym "M1" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "LEN") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "M1" "X") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "APP") (mkpair (
mkpair (mksym "M1" "X") (mkpair (mksym "M1" "Y") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "M1" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "M1" "Y") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "M1" "X") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "APP") (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mksym "M1" "X") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "M1" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "REV") (mkpair (
mkpair (mksym "M1" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (
mksym "M1" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "APP") (mkpair (mkpair (
mksym "M1" "REV") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym 
"M1" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" 
"CAR") (mkpair (mksym "M1" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "REV1") (mkpair (
mkpair (mksym "M1" "X") (mkpair (mksym "M1" "A") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "M1" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "M1" "A") (mkpair (mkpair (mksym "M1" "REV1") (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mksym "M1" "X") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "M1" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "M1" "A") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "FREV") (mkpair (
mkpair (mksym "M1" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"M1" "REV1") (mkpair (mksym "M1" "X") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "REPEAT") (mkpair (
mkpair (mksym "M1" "TH") (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ZP") (
mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mksym "M1" "TH") (mkpair (mkpair (mksym "M1" "REPEAT") (mkpair (mksym "M1" 
"TH") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "-1" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "POPN") (mkpair (
mkpair (mksym "M1" "N") (mkpair (mksym "M1" "STK") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ZP") (
mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" 
"STK") (mkpair (mkpair (mksym "M1" "POPN") (mkpair (mkpair (mksym "ACL2" 
"BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "-1" 
"1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "N") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "POP") (mkpair (mksym 
"M1" "STK") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "UPDATE-NTH") (
mkpair (mkpair (mksym "M1" "N") (mkpair (mksym "M1" "V") (mkpair (mksym 
"COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ZP") (mkpair (mksym "M1" 
"N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"CONS") (mkpair (mksym "M1" "V") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mksym "COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "COMMON-LISP" "LIST") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "UPDATE-NTH") (
mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "-1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "M1" 
"V") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "COMMON-LISP" 
"LIST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "MEMBER") (mkpair (
mkpair (mksym "M1" "E") (mkpair (mksym "COMMON-LISP" "LIST") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "COMMON-LISP" "LIST") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" 
"EQUAL") (mkpair (mksym "M1" "E") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "MEMBER") (mkpair (mksym "M1" "E") (mkpair (mkpair (mksym "COMMON-LISP" 
"CDR") (mkpair (mksym "COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "INDEX") (mkpair (
mkpair (mksym "M1" "E") (mkpair (mksym "M1" "LST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "M1" "LST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "M1" "E") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "M1" "LST") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "INDEX") (mkpair (mksym "M1" "E") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "M1" "LST") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "SUPPLIEDP") (
mkpair (mkpair (mksym "M1" "KEY") (mkpair (mksym "M1" "ARGS") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "M1" "ARGS") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mksym "M1" "KEY") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "M1" "ARGS") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "SUPPLIEDP") (mkpair (
mksym "M1" "KEY") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mksym "M1" "ARGS") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "ACTUAL") (mkpair (
mkpair (mksym "M1" "KEY") (mkpair (mksym "M1" "ARGS") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "M1" "ARGS") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "M1" "KEY") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "M1" "ARGS") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "M1" "ARGS") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ACTUAL") (mkpair (mksym "M1" "KEY") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mksym "M1" "ARGS") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "BOUNDP") (mkpair (
mkpair (mksym "M1" "VAR") (mkpair (mksym "M1" "ALIST") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "M1" "ALIST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "M1" "VAR") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "M1" "ALIST") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "BOUNDP") (mkpair (mksym 
"M1" "VAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "M1" 
"ALIST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "BINDING") (mkpair (
mkpair (mksym "M1" "VAR") (mkpair (mksym "M1" "ALIST") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "M1" "ALIST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "M1" "VAR") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "M1" "ALIST") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "M1" "ALIST") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "BINDING") (mkpair (mksym 
"M1" "VAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "M1" 
"ALIST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "BIND") (mkpair (
mkpair (mksym "M1" "VAR") (mkpair (mksym "M1" "VAL") (mkpair (mksym "M1" 
"ALIST") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "M1" 
"ALIST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" 
"VAR") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "VAL") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mksym "M1" "VAR") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "M1" "ALIST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "VAR") (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "VAL") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "M1" "ALIST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "M1" "ALIST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "BIND") (mkpair (mksym "M1" "VAR") (mkpair (mksym 
"M1" "VAL") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "M1" 
"ALIST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "U-FIX") (mkpair (
mkpair (mksym "M1" "X") (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "MOD") (mkpair (mksym "M1" "X") (mkpair (
mkpair (mksym "COMMON-LISP" "EXPT") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "2" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "S-FIX") (mkpair (
mkpair (mksym "M1" "X") (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mkpair (mksym "COMMON-LISP" "LAMBDA") (mkpair (mkpair (mksym 
"M1" "TEMP") (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "<") (
mkpair (mksym "M1" "TEMP") (mkpair (mkpair (mksym "COMMON-LISP" "EXPT") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "2" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "BINARY-+") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "-1" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "M1" "TEMP") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (
mksym "M1" "TEMP") (mkpair (mkpair (mksym "ACL2" "UNARY--") (mkpair (mkpair (
mksym "COMMON-LISP" "EXPT") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "2" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"M1" "N") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "MOD") (mkpair (mksym "M1" "X") (
mkpair (mkpair (mksym "COMMON-LISP" "EXPT") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "2" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "U-BIG1") (mkpair (
mkpair (mksym "M1" "LST") (mkpair (mksym "M1" "ACC") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "M1" "LST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "M1" "ACC") (mkpair (mkpair (mksym "M1" "U-BIG1") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "M1" "LST") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (
mkpair (mksym "M1" "U-FIX") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "M1" "LST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "8" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"ACL2" "BINARY-*") (mkpair (mkpair (mksym "COMMON-LISP" "EXPT") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "2" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "8" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mksym "M1" "ACC") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "U-BIG") (mkpair (
mkpair (mksym "M1" "LST") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"M1" "U-BIG1") (mkpair (mksym "M1" "LST") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "S-BIG") (mkpair (
mkpair (mksym "M1" "LST") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"M1" "S-FIX") (mkpair (mkpair (mksym "M1" "U-BIG") (mkpair (mksym "M1" "LST") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "BINARY-*") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "8" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "LEN") (mkpair (
mksym "M1" "LST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "NEXTN") (mkpair (
mkpair (mksym "M1" "N") (mkpair (mksym "M1" "LST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ZP") (
mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "M1" "LST") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "NEXTN") (mkpair (mkpair (
mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "-1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"M1" "N") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"CDR") (mkpair (mksym "M1" "LST") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "SKIPN") (mkpair (
mkpair (mksym "M1" "N") (mkpair (mksym "M1" "LST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ZP") (
mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" 
"LST") (mkpair (mkpair (mksym "M1" "SKIPN") (mkpair (mkpair (mksym "ACL2" 
"BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "-1" 
"1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "N") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "M1" "LST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))

];
