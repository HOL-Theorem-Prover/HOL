(*****************************************************************************)
(* HOL proofs of defthms in defaxioms.lisp.trans.                            *)
(*****************************************************************************)

(* The commented out stuff below should be loaded in interactive sessions
quietdec := true;
map
 load
 ["stringLib","complex_rationalTheory","gcdTheory",
  "sexp","sexpTheory","hol_defaxiomsTheory"];
open stringLib complex_rationalTheory gcdTheory
     sexp sexpTheory hol_defaxiomsTheory;
Globals.checking_const_names := false;
quietdec := false;
*)

Theory hol_defaxioms_thms
Ancestors
  complex_rational gcd sexp hol_defaxioms
Libs
  stringLib sexp

(*
     [oracles: DEFTHM ACL2::CHARACTER-LISTP-FORWARD-TO-EQLABLE-LISTP]
     [axioms: ] [] |- |= implies (character_listp x) (eqlable_listp x),
*)

Theorem character_listp_forward_to_eqlable_listp_defaxiom:
     |= implies (character_listp x) (eqlable_listp x)
Proof
   SIMP_TAC arith_ss [implies]
    THEN Induct_on `x`
    THENL
     [ACL2_SIMP_TAC [itel_def],
      ACL2_SIMP_TAC [itel_def],
      ACL2_SIMP_TAC [itel_def],
      ACL2_SIMP_TAC [itel_def],
      ONCE_REWRITE_TAC[character_listp_def,eqlable_listp_def]
       THEN ACL2_SIMP_TAC [itel_def]
       THEN FULL_SIMP_TAC arith_ss [GSYM ACL2_TRUE,GSYM nil_def]
       THEN Cases_on `x`
       THEN ACL2_FULL_SIMP_TAC [characterp_def]]
QED

(*
     [oracles: DEFTHM ACL2::STANDARD-CHAR-LISTP-FORWARD-TO-CHARACTER-LISTP]
     [axioms: ] [] |- |= implies (standard_char_listp x) (character_listp x),
*)

Theorem standard_char_listp_forward_to_character_listp_defaxiom:
     |= implies (standard_char_listp x) (character_listp x)
Proof
   SIMP_TAC arith_ss [implies]
    THEN Induct_on `x`
    THEN ONCE_REWRITE_TAC[character_listp_def,standard_char_listp_def]
    THENL
     [ACL2_SIMP_TAC [],
      ACL2_SIMP_TAC [],
      ACL2_SIMP_TAC [],
      ACL2_SIMP_TAC [],
      ACL2_SIMP_TAC []
       THEN FULL_SIMP_TAC std_ss [GSYM nil_def,GSYM ACL2_TRUE]]
QED


(*
     [oracles: DEFAXIOM ACL2::CHARACTER-LISTP-COERCE, DISK_THM] [axioms: ] []
     |- |= character_listp (coerce acl2_str (csym "LIST")),
*)

Theorem character_listp_list_to_sexp:
     !l. |= character_listp(list_to_sexp chr l)
Proof
   Induct
    THEN ACL2_SIMP_TAC[list_to_sexp_def]
    THEN ACL2_FULL_SIMP_TAC[ACL2_TRUE,nil_def]
QED

Theorem character_listp_coerce_defaxiom:
     |= character_listp (coerce acl2_str (csym "LIST"))
Proof
   Cases_on `acl2_str`
    THEN ACL2_SIMP_TAC
          [csym_def,COMMON_LISP_def,coerce_string_to_list_def,
           coerce_list_to_string_def,list_to_sexp_def,
           EVAL ``EXPLODE ""``,stringTheory.EXPLODE_EQNS,
           make_character_list_def]
    THEN PROVE_TAC[character_listp_list_to_sexp,nil_def,ACL2_TRUE]
QED

Theorem assoc_nil:
     assoc x nil = nil
Proof
   CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[assoc_def]))
    THEN ACL2_SIMP_TAC[itel_def]
QED

Theorem assoc_cons:
     assoc x (cons (cons x' y) l) =
      if |= equal x x' then cons x' y else assoc x l
Proof
   CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[assoc_def]))
    THEN ACL2_SIMP_TAC[itel_def]
QED

(*
val lower_case_p_char_downcase_defaxiom =
 store_thm
  ("lower_case_p_char_downcase_defaxiom",
   ``|= implies (andl [upper_case_p x; characterp x])
                (lower_case_p (char_downcase x))``,
   REWRITE_TAC[implies]
    THEN STRIP_TAC
    THEN SIMP_TAC std_ss [char_downcase_def,assoc_cons,List_def]
    THEN CONV_TAC(DEPTH_CONV(pairLib.let_CONV))
    THEN SIMP_TAC std_ss [itel_def,ite_def]
    THEN ACL2_FULL_SIMP_TAC[assoc_cons,assoc_nil]
    THEN REWRITE_TAC[COND_RAND]
*)


val _ = export_acl2_theory();
