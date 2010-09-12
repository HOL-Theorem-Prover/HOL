open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;

val package =
 implode(map chr (cons 77 (cons 49 nil)));

val events = [

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "NEXT-INST") (
mkpair (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "M1" "NTH") (mkpair (mkpair (mksym "M1" "PC") (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "PROGRAM") (mkpair (
mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "EXECUTE-ICONST") (
mkpair (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (
mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "M1" "PC") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "LOCALS") (mkpair (
mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"PUSH") (mkpair (mkpair (mksym "M1" "ARG1") (mkpair (mksym "M1" "INST") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "STACK") (mkpair (
mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "M1" "PROGRAM") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "EXECUTE-ILOAD") (
mkpair (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (
mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "M1" "PC") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "LOCALS") (mkpair (
mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"PUSH") (mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (mksym "M1" "ARG1") (
mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "M1" "LOCALS") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "STACK") (mkpair (
mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "M1" "PROGRAM") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "EXECUTE-IADD") (
mkpair (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (
mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "M1" "PC") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "LOCALS") (mkpair (
mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"PUSH") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "M1" 
"TOP") (mkpair (mkpair (mksym "M1" "POP") (mkpair (mkpair (mksym "M1" "STACK") (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "TOP") (
mkpair (mkpair (mksym "M1" "STACK") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "M1" "POP") (mkpair (mkpair (mksym "M1" 
"POP") (mkpair (mkpair (mksym "M1" "STACK") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "PROGRAM") (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "EXECUTE-ISTORE") (
mkpair (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (
mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "M1" "PC") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "UPDATE-NTH") (
mkpair (mkpair (mksym "M1" "ARG1") (mkpair (mksym "M1" "INST") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "TOP") (mkpair (mkpair (
mksym "M1" "STACK") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "LOCALS") (mkpair (
mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "M1" "POP") (mkpair (mkpair (mksym "M1" "STACK") (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "PROGRAM") (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "EXECUTE-ISUB") (
mkpair (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (
mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "M1" "PC") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "LOCALS") (mkpair (
mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"PUSH") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "M1" 
"TOP") (mkpair (mkpair (mksym "M1" "POP") (mkpair (mkpair (mksym "M1" "STACK") (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" 
"UNARY--") (mkpair (mkpair (mksym "M1" "TOP") (mkpair (mkpair (mksym "M1" 
"STACK") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "M1" "POP") (mkpair (mkpair (mksym "M1" 
"POP") (mkpair (mkpair (mksym "M1" "STACK") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "PROGRAM") (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "EXECUTE-IMUL") (
mkpair (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (
mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "M1" "PC") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "LOCALS") (mkpair (
mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"PUSH") (mkpair (mkpair (mksym "ACL2" "BINARY-*") (mkpair (mkpair (mksym "M1" 
"TOP") (mkpair (mkpair (mksym "M1" "POP") (mkpair (mkpair (mksym "M1" "STACK") (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "TOP") (
mkpair (mkpair (mksym "M1" "STACK") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "M1" "POP") (mkpair (mkpair (mksym "M1" 
"POP") (mkpair (mkpair (mksym "M1" "STACK") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "PROGRAM") (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "EXECUTE-GOTO") (
mkpair (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (
mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "M1" "ARG1") (mkpair (
mksym "M1" "INST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"PC") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "LOCALS") (mkpair (mksym 
"M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "STACK") (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "PROGRAM") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "EXECUTE-IFLE") (
mkpair (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (
mkpair (mkpair (mksym "COMMON-LISP" "<") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "TOP") (mkpair (mkpair (mksym "M1" "STACK") (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "M1" "ARG1") (mkpair (
mksym "M1" "INST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"PC") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "PC") (mkpair (mksym "M1" 
"S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "M1" "LOCALS") (mkpair (mksym 
"M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "POP") (
mkpair (mkpair (mksym "M1" "STACK") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "PROGRAM") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "DO-INST") (mkpair (
mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "OP-CODE") (mkpair (mksym 
"M1" "INST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "M1" "ICONST") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" 
"EXECUTE-ICONST") (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "OP-CODE") (
mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "M1" "ILOAD") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"M1" "EXECUTE-ILOAD") (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"OP-CODE") (mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "M1" "ISTORE") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"M1" "EXECUTE-ISTORE") (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"OP-CODE") (mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "M1" "IADD") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"M1" "EXECUTE-IADD") (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"OP-CODE") (mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "M1" "ISUB") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"M1" "EXECUTE-ISUB") (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"OP-CODE") (mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "M1" "IMUL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"M1" "EXECUTE-IMUL") (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"OP-CODE") (mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "M1" "GOTO") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"M1" "EXECUTE-GOTO") (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"OP-CODE") (mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "M1" "IFLE") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"M1" "EXECUTE-IFLE") (mkpair (mksym "M1" "INST") (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "STEP") (mkpair (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"M1" "DO-INST") (mkpair (mkpair (mksym "M1" "NEXT-INST") (mkpair (mksym "M1" 
"S") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "RUN") (mkpair (
mkpair (mksym "M1" "SCHED") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "M1" "SCHED") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "M1" "S") (mkpair (mkpair (mksym "M1" "RUN") (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mksym "M1" "SCHED") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "STEP") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "FACTORIAL-EXAMPLE-0") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"RUN") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (mknum 
"0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" 
"1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (
mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" 
"0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (
mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum 
"0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" 
"1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (
mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" 
"0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (
mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum 
"0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" 
"1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (
mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" 
"0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (
mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum 
"0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" 
"1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (
mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" 
"0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (
mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum 
"0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" 
"1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (
mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" 
"0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (
mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum 
"0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" 
"1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (
mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" 
"0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (
mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum 
"0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" 
"1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (
mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" 
"0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (
mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum 
"0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" 
"1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (
mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" 
"0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (
mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum 
"0" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "0" "1" "0" 
"1") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mkpair (mknum "5" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum 
"1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "IFLE") (mkpair (mknum "10" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "IMUL") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ISUB") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "GOTO") (mkpair (mknum 
"-10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "HALT") (mksym "COMMON-LISP" "NIL")) (mksym 
"COMMON-LISP" "NIL")))))))))))))))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (mknum "14" "1" "0" "1") (mkpair (
mkpair (mknum "0" "1" "0" "1") (mkpair (mknum "120" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mknum "120" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mkpair (mksym "M1" "ICONST") (mkpair (
mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "ISTORE") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "IFLE") (mkpair (mknum 
"10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "IMUL") (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum 
"1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISUB") (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"GOTO") (mkpair (mknum "-10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "HALT") (mksym 
"COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL")))))))))))))))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "IFACT-LOOP-SCHED") (
mkpair (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ZP") (mkpair (mksym 
"M1" "N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "REPEAT") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "4" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "APP") (mkpair (mkpair (
mksym "M1" "REPEAT") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "11" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" 
"IFACT-LOOP-SCHED") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "-1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "IFACT-SCHED") (
mkpair (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "M1" "APP") (mkpair (mkpair (mksym "M1" "REPEAT") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "2" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "M1" "IFACT-LOOP-SCHED") (mkpair (mksym "M1" 
"N") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "!") (mkpair (
mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ZP") (mkpair (mksym "M1" 
"N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "ACL2" "BINARY-*") (mkpair (mksym "M1" "N") (mkpair (
mkpair (mksym "M1" "!") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "-1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "TEST-IFACT") (
mkpair (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "M1" "TOP") (mkpair (mkpair (mksym "M1" "STACK") (mkpair (mkpair (mksym 
"M1" "RUN") (mkpair (mkpair (mksym "M1" "IFACT-SCHED") (mkpair (mksym "M1" 
"N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mksym "M1" "N") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (mkpair (mksym 
"M1" "ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"IFLE") (mkpair (mknum "10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"IMUL") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "M1" "ISTORE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "M1" "ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "1" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISUB") (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"GOTO") (mkpair (mknum "-10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "HALT") (mksym 
"COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL")))))))))))))))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "FACTORIAL-EXAMPLE-1") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"TEST-IFACT") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum 
"5" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "!") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "5" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "FACTORIAL-EXAMPLE-2") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"TEST-IFACT") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum 
"1000" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "!") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "1000" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "EVEN-SCHED") (
mkpair (mkpair (mksym "M1" "I") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ZP") (mkpair (mksym 
"M1" "I") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "REPEAT") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "4" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "M1" "I") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"M1" "REPEAT") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "8" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "APP") (
mkpair (mkpair (mksym "M1" "REPEAT") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "11" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "M1" "EVEN-SCHED") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "-2" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "I") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "TEST-EVEN") (
mkpair (mkpair (mksym "M1" "I") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "M1" "TOP") (mkpair (mkpair (mksym "M1" "STACK") (mkpair (mkpair (mksym 
"M1" "RUN") (mkpair (mkpair (mksym "M1" "EVEN-SCHED") (mkpair (mksym "M1" "I") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mksym "M1" "I") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (
mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "IFLE") (mkpair (mknum "12" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum 
"1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ISUB") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "M1" "IFLE") (
mkpair (mknum "6" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "M1" "ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "2" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISUB") (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"GOTO") (mkpair (mknum "-10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "HALT") (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum 
"1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"HALT") (mksym "COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL")))))))))))))))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "TEST-EVEN-THEOREM") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "TEST-EVEN") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "18" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym 
"M1" "TEST-EVEN") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "19" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" 
"0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" 
"EQUAL") (mkpair (mkpair (mksym "M1" "TEST-EVEN") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "235" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mkpair (mksym "M1" "TEST-EVEN") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "234" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "COLLECT-AT-END") (
mkpair (mkpair (mksym "COMMON-LISP" "LIST") (mkpair (mksym "M1" "E") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "M1" "MEMBER") (mkpair (mksym "M1" "E") (mkpair (mksym 
"COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym 
"COMMON-LISP" "LIST") (mkpair (mkpair (mksym "M1" "APP") (mkpair (mksym 
"COMMON-LISP" "LIST") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mksym "M1" "E") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "NTH-NIL") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "NTH") (
mkpair (mksym "M1" "N") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "ACL2-COUNT-NTH") (mkpair (
mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "CONSP") (
mkpair (mksym "COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "<") (mkpair (mkpair (mksym "ACL2" "ACL2-COUNT") (
mkpair (mkpair (mksym "M1" "NTH") (mkpair (mksym "M1" "N") (mkpair (mksym 
"COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "ACL2" "ACL2-COUNT") (mkpair (mksym 
"COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" 
"COLLECT-VARS-IN-EXPR") (mkpair (mkpair (mksym "M1" "VARS") (mkpair (mksym 
"M1" "EXPR") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ATOM") (mkpair (
mksym "M1" "EXPR") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "SYMBOLP") (mkpair (
mksym "M1" "EXPR") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"COLLECT-AT-END") (mkpair (mksym "M1" "VARS") (mkpair (mksym "M1" "EXPR") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "M1" "VARS") (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "M1" "COLLECT-VARS-IN-EXPR") (
mkpair (mkpair (mksym "M1" "COLLECT-VARS-IN-EXPR") (mkpair (mksym "M1" "VARS") (
mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "M1" "EXPR") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "2" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "EXPR") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "MUTUAL-RECURSION") (mkpair (mkpair (mksym 
"COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "COLLECT-VARS-IN-STMT*") (mkpair (
mkpair (mksym "M1" "VARS") (mkpair (mksym "M1" "STMT-LIST") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "M1" "STMT-LIST") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "VARS") (mkpair (mkpair (mksym 
"M1" "COLLECT-VARS-IN-STMT*") (mkpair (mkpair (mksym "M1" 
"COLLECT-VARS-IN-STMT") (mkpair (mksym "M1" "VARS") (mkpair (mkpair (mksym 
"COMMON-LISP" "CAR") (mkpair (mksym "M1" "STMT-LIST") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"CDR") (mkpair (mksym "M1" "STMT-LIST") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" 
"COLLECT-VARS-IN-STMT") (mkpair (mkpair (mksym "M1" "VARS") (mkpair (mksym 
"M1" "STMT") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mkpair (mksym "M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"M1" "STMT") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "M1" "=") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" 
"COLLECT-VARS-IN-EXPR") (mkpair (mkpair (mksym "M1" "COLLECT-AT-END") (mkpair (
mksym "M1" "VARS") (mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "M1" "STMT") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "2" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "STMT") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" 
"0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "STMT") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "M1" "WHILE") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "M1" "COLLECT-VARS-IN-STMT*") (mkpair (mkpair (mksym 
"M1" "COLLECT-VARS-IN-EXPR") (mkpair (mksym "M1" "VARS") (mkpair (mkpair (
mksym "M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" 
"STMT") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mksym "M1" "STMT") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym 
"M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" 
"1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "STMT") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "M1" "RETURN") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "M1" "COLLECT-VARS-IN-EXPR") (mkpair (mksym "M1" "VARS") (
mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "M1" "STMT") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mksym "M1" "VARS") (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "OP!") (mkpair (
mkpair (mksym "M1" "OP") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mksym "M1" "OP") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "+") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (mkpair (mksym 
"M1" "IADD") (mksym "COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL")) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "M1" "OP") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "-") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mkpair (mkpair (mksym "M1" "ISUB") (mksym 
"COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mksym "M1" "OP") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "*") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mkpair (mkpair (mksym "M1" "IMUL") (mksym "COMMON-LISP" 
"NIL")) (mksym "COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (mkpair (mksym "M1" 
"ILLEGAL") (mksym "COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL")) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "ILOAD!") (mkpair (
mkpair (mksym "M1" "VARS") (mkpair (mksym "M1" "VAR") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "M1" "ILOAD") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mkpair (mksym "M1" "INDEX") (mkpair (mksym 
"M1" "VAR") (mkpair (mksym "M1" "VARS") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "ICONST!") (mkpair (
mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "M1" "ICONST") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mksym "M1" "N") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "EXPR!") (mkpair (
mkpair (mksym "M1" "VARS") (mkpair (mksym "M1" "EXPR") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ATOM") (mkpair (mksym "M1" "EXPR") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "SYMBOLP") (mkpair (mksym "M1" "EXPR") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD!") (mkpair (mksym "M1" "VARS") (
mkpair (mksym "M1" "EXPR") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "M1" "ICONST!") (mkpair (mksym "M1" "EXPR") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "M1" "APP") (mkpair (
mkpair (mksym "M1" "EXPR!") (mkpair (mksym "M1" "VARS") (mkpair (mkpair (
mksym "M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" 
"EXPR") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "M1" "APP") (mkpair (mkpair (mksym "M1" "EXPR!") (mkpair (mksym 
"M1" "VARS") (mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "2" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "M1" "EXPR") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "OP!") (mkpair (mkpair (
mksym "M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" 
"EXPR") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "IFLE!") (mkpair (
mkpair (mksym "M1" "OFFSET") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "M1" "IFLE") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mksym "M1" "OFFSET") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "GOTO!") (mkpair (
mkpair (mksym "M1" "OFFSET") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "M1" "GOTO") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mksym "M1" "OFFSET") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "WHILE!") (mkpair (
mkpair (mksym "M1" "TEST-CODE") (mkpair (mksym "M1" "BODY-CODE") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "APP") (mkpair (mksym "M1" 
"TEST-CODE") (mkpair (mkpair (mksym "M1" "APP") (mkpair (mkpair (mksym "M1" 
"IFLE!") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "2" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "LEN") (mkpair (mksym "M1" "BODY-CODE") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "APP") (mkpair (mksym "M1" 
"BODY-CODE") (mkpair (mkpair (mksym "M1" "GOTO!") (mkpair (mkpair (mksym 
"ACL2" "UNARY--") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (
mksym "M1" "LEN") (mkpair (mksym "M1" "TEST-CODE") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "LEN") (mkpair (mksym "M1" "BODY-CODE") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "TEST!") (mkpair (
mkpair (mksym "M1" "VARS") (mkpair (mksym "M1" "TEST") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "TEST") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" ">") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "2" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "M1" "TEST") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"M1" "EXPR!") (mkpair (mksym "M1" "VARS") (mkpair (mkpair (mksym "M1" "NTH") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "TEST") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "APP") (
mkpair (mkpair (mksym "M1" "EXPR!") (mkpair (mksym "M1" "VARS") (mkpair (
mkpair (mksym "M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"M1" "TEST") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "M1" "APP") (mkpair (mkpair (mksym "M1" "EXPR!") (
mkpair (mksym "M1" "VARS") (mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "2" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "TEST") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mkpair (mkpair (mksym "M1" "ISUB") (mksym "COMMON-LISP" "NIL")) (
mksym "COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (
mkpair (mksym "M1" "ILLEGAL") (mksym "COMMON-LISP" "NIL")) (mksym 
"COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "ISTORE!") (mkpair (
mkpair (mksym "M1" "VARS") (mkpair (mksym "M1" "VAR") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "M1" "ISTORE") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mkpair (mksym "M1" "INDEX") (mkpair (mksym 
"M1" "VAR") (mkpair (mksym "M1" "VARS") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "MUTUAL-RECURSION") (mkpair (mkpair (mksym 
"COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "STMT*!") (mkpair (mkpair (mksym 
"M1" "VARS") (mkpair (mksym "M1" "STMT-LIST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "ENDP") (mkpair (mksym "M1" "STMT-LIST") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "APP") (mkpair (mkpair (mksym "M1" "STMT!") (mkpair (mksym "M1" "VARS") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "M1" "STMT-LIST") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "M1" "STMT*!") (mkpair (mksym "M1" "VARS") (mkpair (mkpair (mksym 
"COMMON-LISP" "CDR") (mkpair (mksym "M1" "STMT-LIST") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "STMT!") (mkpair (mkpair (
mksym "M1" "VARS") (mkpair (mksym "M1" "STMT") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "STMT") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "M1" "=") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"M1" "APP") (mkpair (mkpair (mksym "M1" "EXPR!") (mkpair (mksym "M1" "VARS") (
mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "2" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "M1" "STMT") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "ISTORE!") (mkpair (mksym 
"M1" "VARS") (mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "M1" "STMT") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mkpair (mksym "M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"M1" "STMT") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "M1" "WHILE") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "WHILE!") (
mkpair (mkpair (mksym "M1" "TEST!") (mkpair (mksym "M1" "VARS") (mkpair (
mkpair (mksym "M1" "NTH") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"M1" "STMT") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "M1" "STMT*!") (mkpair (mksym "M1" "VARS") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mksym "M1" "STMT") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "STMT") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "M1" "RETURN") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "M1" "APP") (mkpair (mkpair (mksym "M1" "EXPR!") (mkpair (mksym "M1" 
"VARS") (mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "M1" "STMT") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mkpair (mkpair (mksym "M1" "HALT") (mksym "COMMON-LISP" "NIL")) (mksym 
"COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (
mkpair (mksym "M1" "ILLEGAL") (mksym "COMMON-LISP" "NIL")) (mksym 
"COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "COMPILE") (mkpair (
mkpair (mksym "M1" "FORMALS") (mkpair (mksym "M1" "STMT-LIST") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "STMT*!") (mkpair (mkpair (
mksym "M1" "COLLECT-VARS-IN-STMT*") (mkpair (mksym "M1" "FORMALS") (mkpair (
mksym "M1" "STMT-LIST") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "M1" 
"STMT-LIST") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "EXAMPLE-COMPILATION-1") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"COMPILE") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (
mksym "M1" "N") (mksym "COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (mkpair (mksym 
"M1" "A") (mkpair (mksym "M1" "=") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "WHILE") (mkpair (mkpair (
mksym "M1" "N") (mkpair (mksym "COMMON-LISP" ">") (mkpair (mknum "0" "1" "0" 
"1") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "A") (mkpair (
mksym "M1" "=") (mkpair (mkpair (mksym "M1" "N") (mkpair (mksym "COMMON-LISP" 
"*") (mkpair (mksym "M1" "A") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "N") (mkpair (mksym "M1" 
"=") (mkpair (mkpair (mksym "M1" "N") (mkpair (mksym "COMMON-LISP" "-") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "M1" "RETURN") (mkpair (mksym "M1" "A") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum 
"1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "IFLE") (mkpair (mknum "10" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "IMUL") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ISUB") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "GOTO") (mkpair (mknum 
"-10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "HALT") (mksym "COMMON-LISP" "NIL")) (mksym 
"COMMON-LISP" "NIL")))))))))))))))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "EXAMPLE-COMPILATION-2") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"COMPILE") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (
mksym "M1" "N") (mkpair (mksym "M1" "K") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mkpair (mkpair (mksym "M1" "A") (mkpair (mksym "M1" "=") (mkpair (mknum "0" 
"1" "0" "1") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" 
"WHILE") (mkpair (mkpair (mksym "M1" "N") (mkpair (mksym "COMMON-LISP" ">") (
mkpair (mksym "M1" "K") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"M1" "A") (mkpair (mksym "M1" "=") (mkpair (mkpair (mksym "M1" "A") (mkpair (
mksym "COMMON-LISP" "+") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "N") (
mkpair (mksym "M1" "=") (mkpair (mkpair (mksym "M1" "N") (mkpair (mksym 
"COMMON-LISP" "-") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "M1" "RETURN") (mkpair (mksym "M1" "A") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum 
"2" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISUB") (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "M1" "IFLE") (mkpair (mknum "10" 
"1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "2" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "IADD") (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum 
"2" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISUB") (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"GOTO") (mkpair (mknum "-12" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum "2" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "HALT") (mksym 
"COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL")))))))))))))))))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "EXAMPLE-EXECUTION-1") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"TOP") (mkpair (mkpair (mksym "M1" "STACK") (mkpair (mkpair (mksym "M1" "RUN") (
mkpair (mkpair (mksym "M1" "REPEAT") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "1000" "1" "0" 
"1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "M1" "MAKE-STATE") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (mknum "5" "1" "0" "1") (mkpair (
mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "COMPILE") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (
mksym "M1" "N") (mksym "COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (mkpair (mksym 
"M1" "A") (mkpair (mksym "M1" "=") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "WHILE") (mkpair (mkpair (
mksym "M1" "N") (mkpair (mksym "COMMON-LISP" ">") (mkpair (mknum "0" "1" "0" 
"1") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "A") (mkpair (
mksym "M1" "=") (mkpair (mkpair (mksym "M1" "N") (mkpair (mksym "COMMON-LISP" 
"*") (mkpair (mksym "M1" "A") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "N") (mkpair (mksym "M1" 
"=") (mkpair (mkpair (mksym "M1" "N") (mkpair (mksym "COMMON-LISP" "-") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "M1" "RETURN") (mkpair (mksym "M1" "A") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "120" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "EXAMPLE-EXECUTION-2") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"TOP") (mkpair (mkpair (mksym "M1" "STACK") (mkpair (mkpair (mksym "M1" "RUN") (
mkpair (mkpair (mksym "M1" "REPEAT") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "1000" "1" "0" 
"1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "M1" "MAKE-STATE") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (mknum "10" "1" "0" "1") (mkpair (
mknum "4" "1" "0" "1") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "COMPILE") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mkpair (mksym "M1" "N") (mkpair (mksym "M1" "K") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mkpair (mkpair (mksym "M1" "A") (mkpair (
mksym "M1" "=") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "M1" "WHILE") (mkpair (mkpair (mksym "M1" "N") (mkpair (
mksym "COMMON-LISP" ">") (mkpair (mksym "M1" "K") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "M1" "A") (mkpair (mksym "M1" "=") (mkpair (mkpair (
mksym "M1" "A") (mkpair (mksym "COMMON-LISP" "+") (mkpair (mknum "1" "1" "0" 
"1") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "M1" "N") (mkpair (mksym "M1" "=") (mkpair (mkpair (mksym "M1" 
"N") (mkpair (mksym "COMMON-LISP" "-") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))) (mkpair (mkpair (mksym "M1" "RETURN") (mkpair (mksym "M1" "A") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "6" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "STACKS") (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "M1" "TOP") (mkpair (mkpair (mksym "M1" "PUSH") (mkpair (
mksym "M1" "X") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "X") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "POP") (mkpair (mkpair (
mksym "M1" "PUSH") (mkpair (mksym "M1" "X") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"TOP") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "X") (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "M1" "X") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "POP") (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "X") (mkpair (
mksym "M1" "S") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" 
"NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "STATES") (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "M1" "PC") (mkpair (mkpair (mksym "M1" "MAKE-STATE") (
mkpair (mksym "M1" "PC") (mkpair (mksym "M1" "LOCALS") (mkpair (mksym "M1" 
"STACK") (mkpair (mksym "M1" "PROGRAM") (mksym "COMMON-LISP" "NIL")))))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "PC") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "LOCALS") (mkpair (mkpair (
mksym "M1" "MAKE-STATE") (mkpair (mksym "M1" "PC") (mkpair (mksym "M1" 
"LOCALS") (mkpair (mksym "M1" "STACK") (mkpair (mksym "M1" "PROGRAM") (mksym 
"COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" 
"LOCALS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym 
"M1" "STACK") (mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (mksym "M1" 
"PC") (mkpair (mksym "M1" "LOCALS") (mkpair (mksym "M1" "STACK") (mkpair (
mksym "M1" "PROGRAM") (mksym "COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mksym "M1" "STACK") (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" 
"EQUAL") (mkpair (mkpair (mksym "M1" "PROGRAM") (mkpair (mkpair (mksym "M1" 
"MAKE-STATE") (mkpair (mksym "M1" "PC") (mkpair (mksym "M1" "LOCALS") (mkpair (
mksym "M1" "STACK") (mkpair (mksym "M1" "PROGRAM") (mksym "COMMON-LISP" "NIL")))))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "PROGRAM") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "PC") (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "PC") (mkpair (
mksym "M1" "X") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "M1" "PC") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "M1" "LOCALS") (mkpair (mkpair (mksym "COMMON-LISP" 
"CONS") (mkpair (mksym "M1" "PC") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mksym "M1" "LOCALS") (mkpair (mksym "M1" "X") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "M1" "LOCALS") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "M1" "STACK") (mkpair (mkpair (mksym "COMMON-LISP" 
"CONS") (mkpair (mksym "M1" "PC") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mksym "M1" "LOCALS") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mksym "M1" "STACK") (mkpair (mksym "M1" "X") (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "STACK") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mkpair (mksym "M1" "PROGRAM") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mksym "M1" "PC") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mksym "M1" "LOCALS") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mksym "M1" "STACK") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mksym "M1" "PROGRAM") (mkpair (mksym "M1" "X") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" 
"PROGRAM") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
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
"NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "STEP-OPENER") (mkpair (
mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "CONSP") (
mkpair (mkpair (mksym "M1" "NEXT-INST") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "STEP") (mkpair (mksym 
"M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "DO-INST") (
mkpair (mkpair (mksym "M1" "NEXT-INST") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "RUN-APP") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "RUN") (
mkpair (mkpair (mksym "M1" "APP") (mkpair (mksym "M1" "A") (mkpair (mksym 
"M1" "B") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "RUN") (mkpair (mksym 
"M1" "B") (mkpair (mkpair (mksym "M1" "RUN") (mkpair (mksym "M1" "A") (mkpair (
mksym "M1" "S") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "RUN-OPENER") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" 
"EQUAL") (mkpair (mkpair (mksym "M1" "RUN") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "RUN") (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "TH") (mkpair (mksym "M1" 
"SCHED") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "RUN") (mkpair (mksym 
"M1" "SCHED") (mkpair (mkpair (mksym "M1" "STEP") (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "NTH-ADD1!") (mkpair (
mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "ACL2" "NATP") (mkpair (
mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "NTH") (mkpair (mkpair (
mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym 
"M1" "N") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "COMMON-LISP" "LIST") (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "NTH") (mkpair (
mksym "M1" "N") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym 
"COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "NTH-UPDATE-NTH") (mkpair (
mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "NATP") (mkpair (mksym "M1" "I") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "NATP") (mkpair (mksym 
"M1" "J") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "M1" "NTH") (mkpair (mksym "M1" "I") (mkpair (mkpair (
mksym "M1" "UPDATE-NTH") (mkpair (mksym "M1" "J") (mkpair (mksym "M1" "V") (
mkpair (mksym "COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "M1" "I") (mkpair (mksym 
"M1" "J") (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "M1" "V") (mkpair (
mkpair (mksym "M1" "NTH") (mkpair (mksym "M1" "I") (mkpair (mksym 
"COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "UPDATE-NTH-UPDATE-NTH-1") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "ACL2" "NATP") (mkpair (mksym "M1" "I") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "ACL2" "NATP") (mkpair (mksym "M1" "J") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mksym "M1" "I") (mkpair (mksym "M1" "J") (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "UPDATE-NTH") (mkpair (
mksym "M1" "I") (mkpair (mksym "M1" "V") (mkpair (mkpair (mksym "M1" 
"UPDATE-NTH") (mkpair (mksym "M1" "J") (mkpair (mksym "M1" "W") (mkpair (
mksym "COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "M1" "UPDATE-NTH") (mkpair (
mksym "M1" "J") (mkpair (mksym "M1" "W") (mkpair (mkpair (mksym "M1" 
"UPDATE-NTH") (mkpair (mksym "M1" "I") (mkpair (mksym "M1" "V") (mkpair (
mksym "COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "UPDATE-NTH-UPDATE-NTH-2") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"UPDATE-NTH") (mkpair (mksym "M1" "I") (mkpair (mksym "M1" "V") (mkpair (
mkpair (mksym "M1" "UPDATE-NTH") (mkpair (mksym "M1" "I") (mkpair (mksym "M1" 
"W") (mkpair (mksym "COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "M1" "UPDATE-NTH") (
mkpair (mksym "M1" "I") (mkpair (mksym "M1" "V") (mkpair (mksym "COMMON-LISP" 
"LIST") (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "!") (mkpair (
mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym 
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ZP") (mkpair (mksym "M1" 
"N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "ACL2" "BINARY-*") (mkpair (mksym "M1" "N") (mkpair (
mkpair (mksym "M1" "!") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "-1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "IFACT") (mkpair (
mkpair (mksym "M1" "N") (mkpair (mksym "M1" "A") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ZP") (
mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "A") (
mkpair (mkpair (mksym "M1" "IFACT") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "-1" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "ACL2" "BINARY-*") (mkpair (mksym "M1" "N") (
mkpair (mksym "M1" "A") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "IFACT-LOOP-SCHED") (
mkpair (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ZP") (mkpair (mksym 
"M1" "N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "REPEAT") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "4" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "APP") (mkpair (mkpair (
mksym "M1" "REPEAT") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "11" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" 
"IFACT-LOOP-SCHED") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "-1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "IFACT-SCHED") (
mkpair (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "M1" "APP") (mkpair (mkpair (mksym "M1" "REPEAT") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "2" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "M1" "IFACT-LOOP-SCHED") (mkpair (mksym "M1" 
"N") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "TEST-IFACT") (
mkpair (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (
mksym "M1" "TOP") (mkpair (mkpair (mksym "M1" "STACK") (mkpair (mkpair (mksym 
"M1" "RUN") (mkpair (mkpair (mksym "M1" "IFACT-SCHED") (mkpair (mksym "M1" 
"N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mksym "M1" "N") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (mkpair (mksym 
"M1" "ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"IFLE") (mkpair (mknum "10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"IMUL") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "M1" "ISTORE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "M1" "ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "1" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISUB") (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"GOTO") (mkpair (mknum "-10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "HALT") (mksym 
"COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL")))))))))))))))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "TEST-IFACT-EXAMPLES") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "TEST-IFACT") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "5" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "!") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "5" 
"1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"TEST-IFACT") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum 
"10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "!") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "TEST-IFACT") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "100" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "!") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "100" 
"1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "IFACT-LOOP-LEMMA") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "ACL2" "NATP") (mkpair (mksym "M1" "N") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "NATP") (mkpair (mksym 
"M1" "A") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "M1" "RUN") (mkpair (mkpair (mksym "M1" 
"IFACT-LOOP-SCHED") (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "2" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "N") (mkpair (
mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "A") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mksym "M1" "STACK") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "1" "1" 
"0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISTORE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "M1" "ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "IFLE") (mkpair (mknum "10" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (
mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "IMUL") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ISUB") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "GOTO") (mkpair (mknum 
"-10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "HALT") (mksym "COMMON-LISP" "NIL")) (mksym 
"COMMON-LISP" "NIL")))))))))))))))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "M1" "MAKE-STATE") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "14" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "M1" "IFACT") (mkpair (
mksym "M1" "N") (mkpair (mksym "M1" "A") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "PUSH") (mkpair (mkpair (
mksym "M1" "IFACT") (mkpair (mksym "M1" "N") (mkpair (mksym "M1" "A") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mksym "M1" "STACK") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (
mkpair (mksym "M1" "ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum 
"1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "IFLE") (mkpair (mknum "10" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "IMUL") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ISUB") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "GOTO") (mkpair (mknum 
"-10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "HALT") (mksym "COMMON-LISP" "NIL")) (mksym 
"COMMON-LISP" "NIL")))))))))))))))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "IFACT-LEMMA") (mkpair (
mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "ACL2" "NATP") (mkpair (
mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "RUN") (mkpair (mkpair (
mksym "M1" "IFACT-SCHED") (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "N") (mkpair (
mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "A") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mksym "M1" "STACK") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "1" "1" 
"0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISTORE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "M1" "ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "IFLE") (mkpair (mknum "10" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (
mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "IMUL") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ISUB") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "GOTO") (mkpair (mknum 
"-10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "HALT") (mksym "COMMON-LISP" "NIL")) (mksym 
"COMMON-LISP" "NIL")))))))))))))))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "M1" "MAKE-STATE") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "14" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "M1" "IFACT") (mkpair (
mksym "M1" "N") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum 
"1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "PUSH") (mkpair (mkpair (
mksym "M1" "IFACT") (mkpair (mksym "M1" "N") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "M1" "STACK") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum 
"1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "IFLE") (mkpair (mknum "10" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "IMUL") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ISUB") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "GOTO") (mkpair (mknum 
"-10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "HALT") (mksym "COMMON-LISP" "NIL")) (mksym 
"COMMON-LISP" "NIL")))))))))))))))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "IFACT-IS-FACTORIAL") (
mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "COMMON-LISP" 
"IF") (mkpair (mkpair (mksym "ACL2" "NATP") (mkpair (mksym "M1" "N") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "NATP") (mkpair (mksym 
"M1" "A") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mkpair (mksym "M1" "IFACT") (mkpair (mksym "M1" "N") (mkpair (mksym 
"M1" "A") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" 
"BINARY-*") (mkpair (mkpair (mksym "M1" "!") (mkpair (mksym "M1" "N") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "A") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "IFACT-CORRECT") (mkpair (
mkpair (mksym "ACL2" "IMPLIES") (mkpair (mkpair (mksym "ACL2" "NATP") (mkpair (
mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" "RUN") (mkpair (mkpair (
mksym "M1" "IFACT-SCHED") (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "N") (mkpair (
mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "A") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mksym "M1" "STACK") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "1" "1" 
"0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISTORE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "M1" "ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "IFLE") (mkpair (mknum "10" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (
mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "IMUL") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ISUB") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "GOTO") (mkpair (mknum 
"-10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "HALT") (mksym "COMMON-LISP" "NIL")) (mksym 
"COMMON-LISP" "NIL")))))))))))))))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "M1" "MAKE-STATE") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "14" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "M1" "!") (mkpair (mksym 
"M1" "N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "M1" "PUSH") (mkpair (mkpair (mksym "M1" "!") (mkpair (mksym "M1" "N") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "STACK") (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum 
"1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "IFLE") (mkpair (mknum "10" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "IMUL") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ISUB") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "M1" "ISTORE") (mkpair (mknum "0" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "GOTO") (mkpair (mknum 
"-10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "HALT") (mksym "COMMON-LISP" "NIL")) (mksym 
"COMMON-LISP" "NIL")))))))))))))))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" 
"IFACT-CORRECT-COROLLARY-1") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "ACL2" "NATP") (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym 
"M1" "TOP") (mkpair (mkpair (mksym "M1" "STACK") (mkpair (mkpair (mksym "M1" 
"RUN") (mkpair (mkpair (mksym "M1" "IFACT-SCHED") (mkpair (mksym "M1" "N") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mksym "M1" "N") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mksym "M1" "A") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "M1" "STACK") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (mkpair (mksym "M1" "ICONST") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "M1" "ISTORE") (mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum "0" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "IFLE") (mkpair (
mknum "10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "IMUL") (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum 
"1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"ILOAD") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ICONST") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "ISUB") (mksym 
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "M1" "ISTORE") (mkpair (mknum 
"0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"GOTO") (mkpair (mknum "-10" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "ILOAD") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "HALT") (mksym 
"COMMON-LISP" "NIL")) (mksym "COMMON-LISP" "NIL")))))))))))))))) (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "M1" "!") (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" 
"IFACT-CORRECT-COROLLARY-2") (mkpair (mkpair (mksym "ACL2" "IMPLIES") (mkpair (
mkpair (mksym "ACL2" "NATP") (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym 
"M1" "TOP") (mkpair (mkpair (mksym "M1" "STACK") (mkpair (mkpair (mksym "M1" 
"RUN") (mkpair (mkpair (mksym "M1" "IFACT-SCHED") (mkpair (mksym "M1" "N") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mksym "M1" "N") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mksym "M1" "A") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mksym "M1" "STACK") (mkpair (mkpair (
mksym "M1" "COMPILE") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL")) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mkpair (
mkpair (mksym "M1" "A") (mkpair (mksym "M1" "=") (mkpair (mknum "1" "1" "0" 
"1") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "WHILE") (
mkpair (mkpair (mksym "M1" "N") (mkpair (mksym "COMMON-LISP" ">") (mkpair (
mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"M1" "A") (mkpair (mksym "M1" "=") (mkpair (mkpair (mksym "M1" "N") (mkpair (
mksym "COMMON-LISP" "*") (mkpair (mksym "M1" "A") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "N") (mkpair (mksym 
"M1" "=") (mkpair (mkpair (mksym "M1" "N") (mkpair (mksym "COMMON-LISP" "-") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "M1" "RETURN") (mkpair (mksym "M1" "A") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "M1" "!") (mkpair (mksym "M1" "N") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "EXAMPLE-MODIFY-1") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"MAKE-STATE") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "PC") (mkpair (mksym "M1" 
"S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "M1" "LOCALS") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "PUSH") (mkpair (mkpair (mksym "M1" 
"ARG1") (mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "M1" "STACK") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "PROGRAM") (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (mkpair (mksym 
"ACL2" "BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "PC") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "LOCALS") (mkpair (mksym 
"M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "PUSH") (
mkpair (mkpair (mksym "M1" "ARG1") (mkpair (mksym "M1" "INST") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "STACK") (mkpair (mksym 
"M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "M1" "PROGRAM") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "EXAMPLE-MODIFY-2") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"MAKE-STATE") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "1" "1" "0" "1") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "PC") (mkpair (mksym "M1" 
"S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "M1" "UPDATE-NTH") (mkpair (mkpair (mksym "M1" "ARG1") (mkpair (
mksym "M1" "INST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"TOP") (mkpair (mkpair (mksym "M1" "STACK") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "LOCALS") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "M1" "POP") (mkpair (mkpair (
mksym "M1" "STACK") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "PROGRAM") (mkpair (
mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))) (
mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (mkpair (mksym "ACL2" 
"BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "1" 
"1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "PC") (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "M1" "UPDATE-NTH") (mkpair (mkpair (mksym 
"M1" "ARG1") (mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "TOP") (mkpair (mkpair (mksym "M1" "STACK") (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "LOCALS") (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "M1" "POP") (mkpair (mkpair (mksym "M1" "STACK") (mkpair (mksym "M1" 
"S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "M1" "PROGRAM") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" 
"NIL"))) (mksym "COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "EXAMPLE-MODIFY-3") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mksym "M1" 
"MAKE-STATE") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (
mksym "M1" "ARG1") (mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "M1" "PC") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"M1" "LOCALS") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "M1" "STACK") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "PROGRAM") (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))) (mkpair (mkpair (
mksym "M1" "MAKE-STATE") (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (
mkpair (mksym "M1" "ARG1") (mkpair (mksym "M1" "INST") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "PC") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"M1" "LOCALS") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "M1" "STACK") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "PROGRAM") (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "PATTERN-BINDINGS") (
mkpair (mkpair (mksym "M1" "VARS") (mkpair (mksym "M1" "ARG-EXPRESSIONS") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "M1" "VARS") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" 
"CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "M1" 
"VARS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" 
"CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "M1" 
"ARG-EXPRESSIONS") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "M1" "PATTERN-BINDINGS") (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mksym "M1" "VARS") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "M1" 
"ARG-EXPRESSIONS") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "ACL2" "DEFTHM") (mkpair (mksym "M1" "EXAMPLE-SEMANTICS-1") (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mkpair (mkpair (mksym 
"COMMON-LISP" "LAMBDA") (mkpair (mkpair (mksym "M1" "C") (mkpair (mksym "M1" 
"-PC-") (mkpair (mksym "M1" "-LOCALS-") (mkpair (mksym "M1" "-STACK-") (
mkpair (mksym "M1" "-PROGRAM-") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" 
"NIL"))))))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (mkpair (mksym 
"ACL2" "BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "PC") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "LOCALS") (mkpair (mksym 
"M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "PUSH") (
mkpair (mksym "M1" "C") (mkpair (mksym "M1" "-STACK-") (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "M1" "PROGRAM") (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))) (mksym 
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "ARG1") (mkpair (mksym 
"M1" "INST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "PC") (
mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"M1" "LOCALS") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "M1" "STACK") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" 
"NIL"))) (mkpair (mkpair (mksym "M1" "PROGRAM") (mkpair (mksym "M1" "S") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" 
"NIL")))))))) (mkpair (mkpair (mksym "M1" "MAKE-STATE") (mkpair (mkpair (
mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "M1" "PC") (mkpair (mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "M1" "LOCALS") (mkpair (
mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" 
"PUSH") (mkpair (mkpair (mksym "M1" "ARG1") (mkpair (mksym "M1" "INST") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "M1" "STACK") (mkpair (
mksym "M1" "S") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "M1" "PROGRAM") (mkpair (mksym "M1" "S") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL"))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "CONCAT-SYMBOLS") (
mkpair (mkpair (mksym "M1" "PART1") (mkpair (mksym "M1" "PART2") (mksym 
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" 
"INTERN-IN-PACKAGE-OF-SYMBOL") (mkpair (mkpair (mksym "COMMON-LISP" "COERCE") (
mkpair (mkpair (mksym "M1" "APP") (mkpair (mkpair (mksym "COMMON-LISP" 
"COERCE") (mkpair (mkpair (mksym "COMMON-LISP" "SYMBOL-NAME") (mkpair (mksym 
"M1" "PART1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "LIST") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym 
"COMMON-LISP" "COERCE") (mkpair (mkpair (mksym "COMMON-LISP" "SYMBOL-NAME") (
mkpair (mksym "M1" "PART2") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "LIST") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "STRING") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" 
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "M1" 
"RUN") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "M1" "MAKE-DEFUN") (
mkpair (mkpair (mksym "M1" "NAME") (mkpair (mksym "M1" "ARGS") (mkpair (mksym 
"M1" "DCL") (mkpair (mksym "M1" "BODY") (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mksym "M1" "DCL") (mkpair (
mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" 
"QUOTE") (mkpair (mksym "COMMON-LISP" "DEFUN") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "NAME") (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "ARGS") (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "DCL") (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mksym "M1" "BODY") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" 
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym 
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" 
"CONS") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym 
"COMMON-LISP" "DEFUN") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mksym "M1" "NAME") (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mksym "M1" "ARGS") (mkpair (mkpair (mksym 
"COMMON-LISP" "CONS") (mkpair (mksym "M1" "BODY") (mkpair (mkpair (mksym 
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym 
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" 
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))

];
