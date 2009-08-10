(* File created from HOL using print_acl2_defun_script on Mon Jun 19 15:43:10 2006 *)

open HolKernel Parse boolLib bossLib;
open stringLib complex_rationalTheory gcdTheory sexp sexpTheory;
val _ = new_theory "basic_defaxioms";

val name_alist =
[("acl2_colon__colon_iff","ACL2::IFF"),("acl2_colon__colon_booleanp","ACL2::BOOLEANP"),("acl2_colon__colon_implies","ACL2::IMPLIES"),("common_lisp_colon__colon_not","COMMON-LISP::NOT"),("acl2_colon__colon_hide","ACL2::HIDE"),("common_lisp_colon__colon_eq","COMMON-LISP::EQ"),("acl2_colon__colon_true_listp","ACL2::TRUE-LISTP"),("acl2_colon__colon_list_macro","ACL2::LIST-MACRO"),("acl2_colon__colon_and_macro","ACL2::AND-MACRO"),("acl2_colon__colon_or_macro","ACL2::OR-MACRO"),("acl2_colon__colon_integer_abs","ACL2::INTEGER-ABS"),("acl2_colon__colon_xxxjoin","ACL2::XXXJOIN"),("acl2_colon__colon_len","ACL2::LEN"),("common_lisp_colon__colon_length","COMMON-LISP::LENGTH"),("acl2_colon__colon_acl2_count","ACL2::ACL2-COUNT"),("acl2_colon__colon_cond_clausesp","ACL2::COND-CLAUSESP"),("acl2_colon__colon_cond_macro","ACL2::COND-MACRO"),("acl2_colon__colon_eqlablep","ACL2::EQLABLEP"),("acl2_colon__colon_eqlable_listp","ACL2::EQLABLE-LISTP"),("common_lisp_colon__colon_atom","COMMON-LISP::ATOM"),("acl2_colon__colon_make_character_list","ACL2::MAKE-CHARACTER-LIST"),("acl2_colon__colon_eqlable_alistp","ACL2::EQLABLE-ALISTP"),("acl2_colon__colon_alistp","ACL2::ALISTP"),("common_lisp_colon__colon_acons","COMMON-LISP::ACONS"),("common_lisp_colon__colon_endp","COMMON-LISP::ENDP"),("acl2_colon__colon_must_be_equal","ACL2::MUST-BE-EQUAL"),("acl2_colon__colon_member_equal","ACL2::MEMBER-EQUAL"),("acl2_colon__colon_union_equal","ACL2::UNION-EQUAL"),("acl2_colon__colon_subsetp_equal","ACL2::SUBSETP-EQUAL"),("acl2_colon__colon_symbol_listp","ACL2::SYMBOL-LISTP"),("common_lisp_colon__colon_null","COMMON-LISP::NULL"),("acl2_colon__colon_member_eq","ACL2::MEMBER-EQ"),("acl2_colon__colon_subsetp_eq","ACL2::SUBSETP-EQ"),("acl2_colon__colon_symbol_alistp","ACL2::SYMBOL-ALISTP"),("acl2_colon__colon_assoc_eq","ACL2::ASSOC-EQ"),("acl2_colon__colon_assoc_equal","ACL2::ASSOC-EQUAL"),("acl2_colon__colon_assoc_eq_equal_alistp","ACL2::ASSOC-EQ-EQUAL-ALISTP"),("acl2_colon__colon_assoc_eq_equal","ACL2::ASSOC-EQ-EQUAL"),("acl2_colon__colon_no_duplicatesp_equal","ACL2::NO-DUPLICATESP-EQUAL"),("acl2_colon__colon_strip_cars","ACL2::STRIP-CARS"),("common_lisp_colon__colon_eql","COMMON-LISP::EQL"),("common_lisp_colon__colon__eq_","COMMON-LISP::="),("common_lisp_colon__colon__slash__eq_","COMMON-LISP::/="),("acl2_colon__colon_zp","ACL2::ZP"),("acl2_colon__colon_zip","ACL2::ZIP"),("common_lisp_colon__colon_nth","COMMON-LISP::NTH"),("common_lisp_colon__colon_char","COMMON-LISP::CHAR"),("acl2_colon__colon_proper_consp","ACL2::PROPER-CONSP"),("acl2_colon__colon_improper_consp","ACL2::IMPROPER-CONSP"),("common_lisp_colon__colon_conjugate","COMMON-LISP::CONJUGATE"),("acl2_colon__colon_prog2_dollar_","ACL2::PROG2$"),("acl2_colon__colon_time_dollar_","ACL2::TIME$"),("acl2_colon__colon_fix","ACL2::FIX"),("acl2_colon__colon_force","ACL2::FORCE"),("acl2_colon__colon_immediate_force_modep","ACL2::IMMEDIATE-FORCE-MODEP"),("acl2_colon__colon_case_split","ACL2::CASE-SPLIT"),("acl2_colon__colon_synp","ACL2::SYNP"),("common_lisp_colon__colon_member","COMMON-LISP::MEMBER"),("acl2_colon__colon_no_duplicatesp","ACL2::NO-DUPLICATESP"),("common_lisp_colon__colon_assoc","COMMON-LISP::ASSOC"),("acl2_colon__colon_r_eqlable_alistp","ACL2::R-EQLABLE-ALISTP"),("common_lisp_colon__colon_rassoc","COMMON-LISP::RASSOC"),("acl2_colon__colon_rassoc_equal","ACL2::RASSOC-EQUAL"),("acl2_colon__colon_r_symbol_alistp","ACL2::R-SYMBOL-ALISTP"),("acl2_colon__colon_rassoc_eq","ACL2::RASSOC-EQ")];


val _ = current_package :=
 implode(map chr (cons 65 (cons 67 (cons 76 (cons 50 nil)))));

val _ = sexp.acl2_list_ref := [

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "IFF") (mkpair (
mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "Q") (mksym "COMMON-LISP"
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mksym "ACL2" "P") (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mksym "ACL2" "Q") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mksym "ACL2"
"Q") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "BOOLEANP") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"EQUAL") (mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP"
"QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "X") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "IMPLIES") (
mkpair (mkpair (mksym "ACL2" "P") (mkpair (mksym "ACL2" "Q") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mksym "ACL2" "P") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mksym
"ACL2" "Q") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym
"COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP" "NOT") (
mkpair (mkpair (mksym "ACL2" "P") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mksym "ACL2" "P") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "HIDE") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mksym "ACL2"
"X") (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP" "EQ") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "TRUE-LISTP") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"CONSP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "ACL2" "TRUE-LISTP") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "EQ") (mkpair (mksym "ACL2" "X") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP"
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "LIST-MACRO") (
mkpair (mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"CONSP") (mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP"
"QUOTE") (mkpair (mksym "COMMON-LISP" "CONS") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "ACL2"
"LIST-MACRO") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym
"ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP"
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP"
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "AND-MACRO") (
mkpair (mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"CONSP") (mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"CONSP") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2"
"LST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP"
"QUOTE") (mkpair (mksym "COMMON-LISP" "IF") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "ACL2"
"AND-MACRO") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym
"ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "OR-MACRO") (
mkpair (mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"CONSP") (mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"CONSP") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2"
"LST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP"
"QUOTE") (mkpair (mksym "COMMON-LISP" "IF") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "ACL2"
"OR-MACRO") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2"
"LST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP"
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2"
"LST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "INTEGER-ABS") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"INTEGERP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "<") (
mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "ACL2" "UNARY--") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "XXXJOIN") (
mkpair (mkpair (mksym "ACL2" "FN") (mkpair (mksym "ACL2" "ARGS") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mksym "ACL2" "ARGS") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mksym "ACL2" "FN") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "ARGS") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mkpair (mksym "ACL2" "XXXJOIN") (mkpair (mksym "ACL2" "FN") (mkpair (mkpair (
mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "ARGS") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP"
"QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mksym "ACL2" "FN") (mkpair (mksym "ACL2" "ARGS") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "LEN") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "CONSP") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2"
"BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "1"
"1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2"
"LEN") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mknum "0" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP" "LENGTH") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"STRINGP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "ACL2" "LEN") (mkpair (mkpair (mksym "COMMON-LISP" "COERCE") (
mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"ACL2" "LEN") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "ACL2-COUNT") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"CONSP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mknum "1" "1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym "ACL2" "ACL2-COUNT") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"ACL2" "ACL2-COUNT") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "RATIONALP") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "INTEGERP") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "INTEGER-ABS") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP"
"NIL"))) (mkpair (mkpair (mksym "ACL2" "BINARY-+") (mkpair (mkpair (mksym
"ACL2" "INTEGER-ABS") (mkpair (mkpair (mksym "COMMON-LISP" "NUMERATOR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "DENOMINATOR") (mkpair (mksym
"ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "ACL2" "COMPLEX-RATIONALP") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "BINARY-+") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "1" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "BINARY-+") (
mkpair (mkpair (mksym "ACL2" "ACL2-COUNT") (mkpair (mkpair (mksym
"COMMON-LISP" "REALPART") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2"
"ACL2-COUNT") (mkpair (mkpair (mksym "COMMON-LISP" "IMAGPART") (mkpair (mksym
"ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "STRINGP") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "LENGTH") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP"
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1"
"0" "1") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP"
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "COND-CLAUSESP") (
mkpair (mkpair (mksym "ACL2" "CLAUSES") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"CONSP") (mkpair (mksym "ACL2" "CLAUSES") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym
"COMMON-LISP" "CONSP") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "CLAUSES") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym
"ACL2" "TRUE-LISTP") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "CLAUSES") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym
"COMMON-LISP" "<") (mkpair (mkpair (mksym "ACL2" "LEN") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "CLAUSES") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mknum "3" "1" "0" "1") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP"
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQ") (mkpair (mkpair (mksym
"COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "CLAUSES") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym
"COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "EQ") (mkpair (mkpair (mksym
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "CLAUSES") (mksym "COMMON-LISP"
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "COND-CLAUSESP") (mkpair (mkpair (mksym
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "CLAUSES") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP"
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym
"COMMON-LISP" "EQ") (mkpair (mksym "ACL2" "CLAUSES") (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP"
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "COND-MACRO") (
mkpair (mkpair (mksym "ACL2" "CLAUSES") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"CONSP") (mkpair (mksym "ACL2" "CLAUSES") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym
"COMMON-LISP" "EQ") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "CLAUSES") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP"
"IF") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "CLAUSES") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP"
"CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "CLAUSES") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "CLAUSES") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym
"COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "IF") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "CLAUSES") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "CLAUSES") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP"
"CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "CLAUSES") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "CLAUSES") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym
"COMMON-LISP" "CONS") (mkpair (mkpair (mksym "ACL2" "COND-MACRO") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "CLAUSES") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP"
"NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "EQLABLEP") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2"
"ACL2-NUMBERP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "ACL2" "ACL2-NUMBERP") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (
mkpair (mkpair (mksym "COMMON-LISP" "SYMBOLP") (mkpair (mksym "ACL2" "X") (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "SYMBOLP") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "CHARACTERP") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP"
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "EQLABLE-LISTP") (
mkpair (mkpair (mksym "ACL2" "L") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"CONSP") (mkpair (mksym "ACL2" "L") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "EQLABLEP") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "L") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"ACL2" "EQLABLE-LISTP") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "L") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP"
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "L") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP" "ATOM") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym "COMMON-LISP"
"CONSP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2"
"MAKE-CHARACTER-LIST") (mkpair (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ATOM") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "CHARACTERP") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2"
"MAKE-CHARACTER-LIST") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (
mkpair (mkpair (mksym "COMMON-LISP" "CODE-CHAR") (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2"
"MAKE-CHARACTER-LIST") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "EQLABLE-ALISTP") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ATOM") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "X") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "CONSP") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "EQLABLEP") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2"
"EQLABLE-ALISTP") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym
"ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP"
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "ALISTP") (mkpair (
mkpair (mksym "ACL2" "L") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ATOM") (mkpair (
mksym "ACL2" "L") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "EQ") (mkpair (mksym "ACL2" "L") (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "CONSP") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "L") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"ACL2" "ALISTP") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym
"ACL2" "L") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP"
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP" "ACONS") (
mkpair (mkpair (mksym "ACL2" "KEY") (mkpair (mksym "ACL2" "DATUM") (mkpair (
mksym "ACL2" "ALIST") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym
"COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mksym "ACL2" "KEY") (mkpair (mksym "ACL2" "DATUM") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "ACL2" "ALIST") (mksym "COMMON-LISP" "NIL")))) (mksym
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP" "ENDP") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "ATOM") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "MUST-BE-EQUAL") (
mkpair (mkpair (mksym "ACL2" "LOGIC") (mkpair (mksym "ACL2" "EXEC") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "LOGIC") (mksym "COMMON-LISP"
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "MEMBER-EQUAL") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "LST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "LST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "ACL2" "LST") (mkpair (mkpair (mksym "ACL2" "MEMBER-EQUAL") (
mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "UNION-EQUAL") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "Y") (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBER-EQUAL") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "UNION-EQUAL") (mkpair (mkpair (mksym
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "CONS") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "UNION-EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2"
"Y") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP"
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "SUBSETP-EQUAL") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBER-EQUAL") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "SUBSETP-EQUAL") (mkpair (mkpair (mksym
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP"
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "SYMBOL-LISTP") (
mkpair (mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ATOM") (
mkpair (mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "EQ") (mkpair (mksym "ACL2" "LST") (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "SYMBOLP") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "LST") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"ACL2" "SYMBOL-LISTP") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP"
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP" "NULL") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "EQ") (mkpair (mksym "ACL2" "X") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP"
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "MEMBER-EQ") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "LST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "LST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQ") (mkpair (
mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym
"ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "ACL2" "LST") (mkpair (mkpair (mksym "ACL2" "MEMBER-EQ") (
mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "LST") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "SUBSETP-EQ") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBER-EQ") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "ACL2" "SUBSETP-EQ") (mkpair (mkpair (mksym
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP"
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "SYMBOL-ALISTP") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ATOM") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "EQ") (mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "CONSP") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "SYMBOLP") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2"
"SYMBOL-ALISTP") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym
"ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP"
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "ASSOC-EQ") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQ") (mkpair (
mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2"
"ALIST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2"
"ASSOC-EQ") (mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP"
"CDR") (mkpair (mksym "ACL2" "ALIST") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP"
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "ASSOC-EQUAL") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2"
"ALIST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2"
"ASSOC-EQUAL") (mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "ALIST") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2"
"ASSOC-EQ-EQUAL-ALISTP") (mkpair (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ATOM") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "EQ") (mkpair (
mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym
"COMMON-LISP" "CONSP") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym
"COMMON-LISP" "SYMBOLP") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym
"COMMON-LISP" "CONSP") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))) (mkpair (mkpair (mksym "ACL2" "ASSOC-EQ-EQUAL-ALISTP") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP"
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "ASSOC-EQ-EQUAL") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mkpair (mksym
"ACL2" "ALIST") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (
mksym "ACL2" "ALIST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQ") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "ALIST") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "ALIST") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP"
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "ASSOC-EQ-EQUAL") (
mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mkpair (mkpair (mksym
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "ALIST") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2"
"NO-DUPLICATESP-EQUAL") (mkpair (mkpair (mksym "ACL2" "L") (mksym
"COMMON-LISP" "NIL")) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "L") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "MEMBER-EQUAL") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "L") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "L") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP"
"NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2"
"NO-DUPLICATESP-EQUAL") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "L") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "STRIP-CARS") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "CONS") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))) (mkpair (mkpair (mksym "ACL2" "STRIP-CARS") (mkpair (mkpair (mksym
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP" "EQL") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP" "=") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (
mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP" "/=") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "NOT") (mkpair (
mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "X") (mkpair (
mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "ZP") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "INTEGERP") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "NOT") (mkpair (mkpair (mksym "COMMON-LISP" "<") (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (
mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "ZIP") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "INTEGERP") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "=") (mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP"
"QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP" "NTH") (
mkpair (mkpair (mksym "ACL2" "N") (mkpair (mksym "ACL2" "L") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "L") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ZP") (mkpair (mksym
"ACL2" "N") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "L") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "NTH") (mkpair (mkpair (mksym "ACL2"
"BINARY-+") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "-1"
"1" "0" "1") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "N") (mksym
"COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "L") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP" "CHAR") (
mkpair (mkpair (mksym "ACL2" "S") (mkpair (mksym "ACL2" "N") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "NTH") (mkpair (
mksym "ACL2" "N") (mkpair (mkpair (mksym "COMMON-LISP" "COERCE") (mkpair (
mksym "ACL2" "S") (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "LIST") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP"
"NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "PROPER-CONSP") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"CONSP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "ACL2" "TRUE-LISTP") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "IMPROPER-CONSP") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"CONSP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "NOT") (mkpair (mkpair (mksym "ACL2" "TRUE-LISTP") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP"
"CONJUGATE") (mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (
mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2"
"COMPLEX-RATIONALP") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "COMPLEX") (mkpair (mkpair (mksym
"COMMON-LISP" "REALPART") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP"
"NIL"))) (mkpair (mkpair (mksym "ACL2" "UNARY--") (mkpair (mkpair (mksym
"COMMON-LISP" "IMAGPART") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "PROG2$") (mkpair (
mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP"
"NIL"))) (mkpair (mksym "ACL2" "Y") (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "TIME$") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mksym "ACL2"
"X") (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "FIX") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "ACL2-NUMBERP") (mkpair (
mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mksym "ACL2" "X") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mknum "0" "1" "0" "1") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "FORCE") (mkpair (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mksym "ACL2"
"X") (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2"
"IMMEDIATE-FORCE-MODEP") (mkpair (mksym "COMMON-LISP" "NIL") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mk_chars_str (chars_to_string (cons 83 (
cons 101 (cons 101 (cons 32 (cons 58 (cons 68 (cons 79 (cons 67 (cons 32 (
cons 105 (cons 109 (cons 109 (cons 101 (cons 100 (cons 105 (cons 97 (cons 116 (
cons 101 (cons 45 (cons 102 (cons 111 (cons 114 (cons 99 (cons 101 (cons 45 (
cons 109 (cons 111 (cons 100 (cons 101 (cons 112 (cons 46 nil))))))))))))))))))))))))))))))))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "CASE-SPLIT") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (mksym
"ACL2" "X") (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "SYNP") (mkpair (
mkpair (mksym "ACL2" "VARS") (mkpair (mksym "ACL2" "FORM") (mkpair (mksym
"ACL2" "TERM") (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP" "MEMBER") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "L") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "L") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQL") (mkpair (
mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym
"ACL2" "L") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mkpair (mksym "ACL2" "L") (mkpair (mkpair (mksym "COMMON-LISP" "MEMBER") (
mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mksym "ACL2" "L") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym
"COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "NO-DUPLICATESP") (
mkpair (mkpair (mksym "ACL2" "L") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ENDP") (
mkpair (mksym "ACL2" "L") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "T") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "MEMBER") (mkpair (mkpair (mksym "COMMON-LISP"
"CAR") (mkpair (mksym "ACL2" "L") (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "L") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym
"COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2" "NO-DUPLICATESP") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "L") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP" "ASSOC") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQL") (mkpair (
mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2"
"ALIST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP"
"ASSOC") (mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP"
"CDR") (mkpair (mksym "ACL2" "ALIST") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP"
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2"
"R-EQLABLE-ALISTP") (mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP"
"NIL")) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym
"COMMON-LISP" "ATOM") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "X") (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP"
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP"
"CONSP") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2"
"X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "ACL2" "EQLABLEP") (
mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym
"COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "ACL2" "R-EQLABLE-ALISTP") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym
"COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP"
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "COMMON-LISP" "RASSOC") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQL") (mkpair (
mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2"
"ALIST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP"
"RASSOC") (mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP"
"CDR") (mkpair (mksym "ACL2" "ALIST") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP"
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "RASSOC-EQUAL") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQUAL") (
mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2"
"ALIST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2"
"RASSOC-EQUAL") (mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym
"COMMON-LISP" "CDR") (mkpair (mksym "ACL2" "ALIST") (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (
mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "R-SYMBOL-ALISTP") (
mkpair (mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL")) (mkpair (
mkpair (mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "ATOM") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "EQUAL") (mkpair (mksym "ACL2" "X") (mkpair (mkpair (
mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL")))) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "CONSP") (mkpair (
mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "X") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym
"COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "SYMBOLP") (mkpair (
mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (
mkpair (mksym "ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL"))) (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2"
"R-SYMBOL-ALISTP") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mksym
"ACL2" "X") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (
mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP"
"NIL") (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mkpair (
mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (mksym "COMMON-LISP" "NIL") (
mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))))) (mksym
"COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP" "NIL")))))
,

(mkpair (mksym "COMMON-LISP" "DEFUN") (mkpair (mksym "ACL2" "RASSOC-EQ") (
mkpair (mkpair (mksym "ACL2" "X") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "IF") (mkpair (
mkpair (mksym "COMMON-LISP" "ENDP") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "COMMON-LISP" "QUOTE") (mkpair (
mksym "COMMON-LISP" "NIL") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (
mksym "COMMON-LISP" "IF") (mkpair (mkpair (mksym "COMMON-LISP" "EQ") (mkpair (
mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP" "CDR") (mkpair (mkpair (
mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2" "ALIST") (mksym
"COMMON-LISP" "NIL"))) (mksym "COMMON-LISP" "NIL"))) (mksym "COMMON-LISP"
"NIL")))) (mkpair (mkpair (mksym "COMMON-LISP" "CAR") (mkpair (mksym "ACL2"
"ALIST") (mksym "COMMON-LISP" "NIL"))) (mkpair (mkpair (mksym "ACL2"
"RASSOC-EQ") (mkpair (mksym "ACL2" "X") (mkpair (mkpair (mksym "COMMON-LISP"
"CDR") (mkpair (mksym "ACL2" "ALIST") (mksym "COMMON-LISP" "NIL"))) (mksym
"COMMON-LISP" "NIL")))) (mksym "COMMON-LISP" "NIL"))))) (mksym "COMMON-LISP"
"NIL"))))) (mksym "COMMON-LISP" "NIL")))))

];

val thl = map (install_and_print o mk_acl2def) (!acl2_list_ref);

val _ = (acl2_simps := (!acl2_simps) @ thl);

val _ = export_acl2_theory();

