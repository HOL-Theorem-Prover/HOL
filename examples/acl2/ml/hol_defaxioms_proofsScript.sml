
(*****************************************************************************)
(* HOL proofs of the ACL2 defaxioms in defaxioms.lisp.trans.                 *)
(*                                                                           *)
(* Note that many of the proofs were starting by cutting-and-pasting         *)
(* earlier proofs, so there are likely to use bloated tactics                *)
(* (e.g. many irrelevant rewrites). There may also be some unused lemmas.    *)
(*                                                                           *)
(*                                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Ignore everything up to "END BOILERPLATE"                                 *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE NEEDED FOR COMPILATION                                  *)
(*****************************************************************************)

(******************************************************************************
* Load theories
******************************************************************************)
(* The commented out stuff below should be loaded in interactive sessions
quietdec := true;
map 
 load  
 ["intLib","stringLib","complex_rationalTheory","gcdTheory",
  "sexp","sexpTheory","hol_defaxiomsTheory","translateTheory"];
open stringLib complex_rationalTheory gcdTheory 
     sexp sexpTheory hol_defaxiomsTheory 
     acl2_packageTheory translateTheory;
Globals.checking_const_names := false;
set_trace "Subgoal number" 100;
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation: open HOL4 systems modules.
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories (including ratTheory from Jens Brandt).
******************************************************************************)
open stringLib complex_rationalTheory gcdTheory sexp sexpTheory
     acl2_packageTheory hol_defaxiomsTheory translateTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

val _ = new_theory "hol_defaxioms_proofs";

(*****************************************************************************)
(* Only save theorem in theory if save_thm_flag is true                      *)
(* (flag initially false).                                                   *)
(*****************************************************************************)
val save_thm_flag = ref false;

fun if_save_thm (name,thm) =
 if !save_thm_flag then save_thm(name,thm) else thm;

fun if_store_thm(name,term,tac) =
 if !save_thm_flag then store_thm(name,term,tac) else prove(term,tac);

(*****************************************************************************)
(* Usefull lemmas for eliminating equations between conditionals             *)
(*****************************************************************************)
val if_t_nil =
 if_store_thm
  ("if_t_nil",
   ``(((if p then t else q) = nil) = ~p /\ (q = nil))
     /\
     (((if p then q else nil) = t) = p  /\ (q = t))
     /\
     (((if p then q else t) = nil) = p  /\ (q = nil))
     /\
     (((if p then nil else q) = t) = ~p /\ (q = t))
     /\
     (~((if p then q else nil) = nil) = p /\ ~(q = nil))
     /\
     (~((if p then nil else q) = nil) = ~p /\ ~(q = nil))
     /\
     (~((if p then q else t) = t) = p /\ ~(q = t))
     /\
     (~((if p then t else q) = t) = ~p /\ ~(q = t))``,
  PROVE_TAC [EVAL ``t = nil``]);

val t_nil_if =
 if_store_thm
  ("t_nil_if",
   ``((nil = (if p then t else q)) = ~p /\ (q = nil))
     /\
     ((t = (if p then q else nil)) = p  /\ (q = t))
     /\
     ((nil = (if p then q else t)) = p  /\ (q = nil))
     /\
     ((t = (if p then nil else q)) = ~p /\ (q = t))
     /\
     (~(nil = (if p then q else nil)) = p /\ ~(q = nil))
     /\
     (~(nil = (if p then nil else q)) = ~p /\ ~(q = nil))
     /\
     (~(t = (if p then q else t)) = p /\ ~(q = t))
     /\
     (~(t = (if p then t else q)) = ~p /\ ~(q = t))``,
  PROVE_TAC [EVAL ``t = nil``]);

val if_eq_imp =
 if_store_thm
  ("if_eq_imp",
   ``((if p then a else b) = c) = (p ==> (a = c)) /\ (~p ==> (b = c))``,
  PROVE_TAC []);

val eq_imp_if =
 if_store_thm
  ("eq_imp_if",
   ``(c = (if p then a else b)) = (p ==> (a = c)) /\ (~p ==> (b = c))``,
  PROVE_TAC []);

(*****************************************************************************)
(* Proof of ACL2 axioms                                                      *)
(*****************************************************************************)

(*****************************************************************************)
(* Add some theorems from translateTheory to theorems used by ACL2_SIMP_TAC  *)
(*****************************************************************************)
val _ = add_acl2_simps (CONJUNCTS translateTheory.JUDGEMENT_THMS);

(*
     [oracles: DEFAXIOM ACL2::CLOSURE, DISK_THM] [axioms: ] []
     |- |= andl
             [acl2_numberp (add x y); acl2_numberp (mult x y);
              acl2_numberp (unary_minus x); acl2_numberp (reciprocal x)],
*)

val closure_defaxiom =
 store_thm
  ("closure_defaxiom",
   ``|= andl
         [acl2_numberp (add x y); acl2_numberp (mult x y);
          acl2_numberp (unary_minus x); acl2_numberp (reciprocal x)]``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC [int_def,cpx_def]);

(*
     [oracles: DEFAXIOM ACL2::ASSOCIATIVITY-OF-+] [axioms: ] []
     |- |= equal (add (add x y) z) (add x (add y z)),
*)

val associativity_of_plus_defaxiom =
 store_thm
  ("associativity_of_plus_defaxiom",
   ``|= equal (add (add x y) z) (add x (add y z))``,
   Cases_on `x` THEN Cases_on `y` THEN Cases_on `z`
    THEN ACL2_SIMP_TAC [int_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN TRY(Cases_on `c'`)
    THEN TRY(Cases_on `c''`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,complex_rational_11,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_LID,
           ratTheory.RAT_ADD_RID,ratTheory.RAT_0,
           ratTheory.RAT_ADD_ASSOC]);

(*
     [oracles: DEFAXIOM ACL2::COMMUTATIVITY-OF-+] [axioms: ] []
     |- |= equal (add x y) (add y x),
*)

val commutativity_of_plus_defaxiom =
 store_thm
  ("commutativity_of_plus_defaxiom",
   ``|= equal (add x y) (add y x)``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC [int_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN TRY(Cases_on `c'`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,complex_rational_11,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_LID,
           ratTheory.RAT_ADD_RID,ratTheory.RAT_0,ratTheory.RAT_ADD_COMM]);

(*
     [oracles: DEFAXIOM ACL2::UNICITY-OF-0, DISK_THM] [axioms: ] []
     |- |= equal (add (nat 0) x) (fix x),
*)

val unicity_of_0_defaxiom =
 store_thm
  ("unicity_of_0_defaxiom",
   ``|= equal (add (nat 0) x) (fix x)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC [int_def,nat_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,complex_rational_11,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,com_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_LID,
           ratTheory.RAT_SUB_LID,ratTheory.RAT_ADD_RINV,
           ratTheory.RAT_ADD_RID,ratTheory.RAT_0,ratTheory.RAT_ADD_COMM]);

(*
     [oracles: DEFAXIOM ACL2::INVERSE-OF-+, DISK_THM] [axioms: ] []
     |- |= equal (add x (unary_minus x)) (nat 0),
*)

val inverse_of_plus_defaxiom =
 store_thm
  ("inverse_of_plus_defaxiom",
   ``|= equal (add x (unary_minus x)) (nat 0)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC [int_def,nat_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,complex_rational_11,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,com_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_LID,
           ratTheory.RAT_SUB_LID,ratTheory.RAT_ADD_RINV,
           ratTheory.RAT_ADD_RID,ratTheory.RAT_0,ratTheory.RAT_ADD_COMM]);

(*
     [oracles: DEFAXIOM ACL2::ASSOCIATIVITY-OF-*] [axioms: ] []
     |- |= equal (mult (mult x y) z) (mult x (mult y z)),
*)

val associativity_of_star_defaxiom =
 store_thm
  ("associativity_of_star_defaxiom",
   ``|= equal (mult (mult x y) z) (mult x (mult y z))``,
   Cases_on `x` THEN Cases_on `y` THEN Cases_on `z`
    THEN ACL2_SIMP_TAC [int_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN TRY(Cases_on `c'`)
    THEN TRY(Cases_on `c''`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_MULT_def,complex_rational_11,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL]
    THEN METIS_TAC[ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_ADD_COMM]);

(*
     [oracles: DEFAXIOM ACL2::COMMUTATIVITY-OF-*] [axioms: ] []
     |- |= equal (mult x y) (mult y x),
*)

val commutativity_of_star_defaxiom =
 store_thm
  ("commutativity_of_star_defaxiom",
   ``|= equal (mult x y) (mult y x)``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC [int_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN TRY(Cases_on `c'`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_MULT_def,complex_rational_11,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL]
    THEN METIS_TAC[ratTheory.RAT_MUL_COMM,ratTheory.RAT_ADD_COMM]);

(*
     [oracles: DEFAXIOM ACL2::UNICITY-OF-1, DISK_THM] [axioms: ] []
     |- |= equal (mult (nat 1) x) (fix x),
*)

val unicity_of_1_defaxiom =
 store_thm
  ("unicity_of_1_defaxiom",
   ``|= equal (mult (nat 1) x) (fix x)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC [int_def,nat_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,sexpTheory.rat_def,
           GSYM fracTheory.frac_1_def,com_1_def,
           GSYM ratTheory.rat_1,ratTheory.RAT_ADD_LID,
           GSYM fracTheory.frac_0_def,GSYM ratTheory.rat_0,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_SUB_RID,
           ratTheory.RAT_SUB_LID,ratTheory.RAT_ADD_RINV,ratTheory.RAT_MUL_LID,
           ratTheory.RAT_ADD_RID,ratTheory.RAT_1,ratTheory.RAT_ADD_COMM]);

(*
     [oracles: DEFAXIOM ACL2::INVERSE-OF-*, DISK_THM] [axioms: ] []
     |- |= implies (andl [acl2_numberp x; not (equal x (nat 0))])
             (equal (mult x (reciprocal x)) (nat 1)),
*)

val RAT_SQ_SGN =
 if_store_thm
  ("RAT_SQ_SGN",
   ``!(r:rat). 0 <= rat_sgn(r*r)``,
   RW_TAC arith_ss [ratTheory.RAT_SGN_MUL,integerTheory.INT_LE_SQUARE]);

val RAT_SQ_NONNEG =
 if_store_thm
  ("RAT_SQ_NONNEG",
   ``!(r:rat). 0 <= r*r``,
   GEN_TAC
    THEN Cases_on `r*r = 0`
    THEN RW_TAC arith_ss [ratTheory.RAT_MUL_LZERO,ratTheory.RAT_LEQ_REF]
    THEN `0 <= rat_sgn(r*r)` by PROVE_TAC[RAT_SQ_SGN]
    THEN DISJ_CASES_TAC(ISPEC ``(r:rat) * r`` ratTheory.RAT_SGN_TOTAL)
    THENL
     [PROVE_TAC[Cooper.COOPER_PROVE ``~(0 <= (n:int) /\ (n = ~1))``],
      POP_ASSUM DISJ_CASES_TAC
       THEN FULL_SIMP_TAC arith_ss 
             [ratTheory.RAT_SGN_MUL,ratTheory.RAT_SGN_CLAUSES,
              ratTheory.RAT_LES_IMP_LEQ,ratTheory.rat_gre_def,
              integerTheory.INT_ENTIRE]]);

val RAT_SQ_POS =
 if_store_thm
  ("RAT_SQ_POS",
   ``!(r:rat). ~(r = 0) ==> 0 < r*r``,
   GEN_TAC
    THEN `0 <= r*r` by PROVE_TAC[RAT_SQ_NONNEG]
    THEN FULL_SIMP_TAC arith_ss [ratTheory.rat_leq_def]
    THEN POP_ASSUM(ASSUME_TAC o GSYM)
    THEN FULL_SIMP_TAC arith_ss [GSYM ratTheory.RAT_NO_ZERODIV]);

val RAT_SUM_SQ_POS =
 if_store_thm
  ("RAT_SUM_SQ_POS",
   ``~(r1 = 0) /\ ~(r2 = 0) ==> 0 < r1*r1 + r2*r2``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC RAT_SQ_POS
    THEN RW_TAC std_ss [ratTheory.RAT_0LES_0LES_ADD]);

(* Would expect to be able to improve on the following proof                 *)
val inverse_of_star_defaxiom = 
 store_thm
  ("inverse_of_star_defaxiom",
   ``|= implies (andl [acl2_numberp x; not (equal x (nat 0))])
             (equal (mult x (reciprocal x)) (nat 1))``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC [int_def,nat_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN ACL2_FULL_SIMP_TAC
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_RECIPROCAL_def,
           complex_rational_11,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,com_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_LID,
           ratTheory.RAT_SUB_LID,ratTheory.RAT_ADD_RINV,
           ratTheory.RAT_ADD_RID,ratTheory.RAT_0,ratTheory.RAT_ADD_COMM]
    THEN Cases_on `r = 0` THEN Cases_on `r0 = 0`
    THEN ACL2_SIMP_TAC[]
    THENL
     [ASSUM_LIST(fn thl => ACL2_FULL_SIMP_TAC[el 3 thl] THEN ASSUME_TAC (el 3 thl)),
      ASSUM_LIST(fn thl => ACL2_FULL_SIMP_TAC[el 3 thl] THEN ASSUME_TAC (el 3 thl)),
      ASSUM_LIST(fn thl => ACL2_FULL_SIMP_TAC[el 1 thl,el 2 thl] 
                            THEN ASSUME_TAC (el 1 thl) THEN ASSUME_TAC (el 2 thl))]
    THEN ACL2_FULL_SIMP_TAC
          [ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,
           ratTheory.RAT_DIV_MULMINV,COMPLEX_MULT_def,
           GSYM fracTheory.frac_1_def,GSYM ratTheory.rat_1,
           complex_rational_11,ratTheory.RAT_AINV_0,
           ratTheory.RAT_MUL_ASSOC,GSYM ratTheory.RAT_AINV_LMUL,
           GSYM ratTheory.RAT_AINV_RMUL]
    THEN IMP_RES_TAC
          (PROVE[ratTheory.RAT_NO_ZERODIV_NEG]``~(r=0) ==> ~((r*r) = 0)``)
    THEN ACL2_FULL_SIMP_TAC
          [ratTheory.RAT_MUL_RINV,ratTheory.RAT_SUB_LID,
           ratTheory.RAT_AINV_AINV,ratTheory.RAT_SUB_RID]
    THEN `(r0 * r * rat_minv (r * r + r0 * r0) +
            ~(r * r0 * rat_minv (r * r + r0 * r0)) = 0)`
          by PROVE_TAC[ratTheory.RAT_ADD_RINV,ratTheory.RAT_MUL_COMM]
    THEN POP_ASSUM(fn th => FULL_SIMP_TAC std_ss [th])
    THEN ACL2_FULL_SIMP_TAC
          [ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_AINV,
           GSYM ratTheory.RAT_RDISTRIB,ratTheory.RAT_MUL_RINV]
    THEN Cases_on `r * r + r0 * r0 = 0`
    THEN ACL2_FULL_SIMP_TAC
          [ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_AINV,
           GSYM ratTheory.RAT_RDISTRIB,ratTheory.RAT_MUL_RINV]
    THEN `0 < r * r + r0 * r0` by PROVE_TAC[RAT_SUM_SQ_POS]
    THEN PROVE_TAC[ratTheory.RAT_LES_REF]);

(*
     [oracles: DEFAXIOM ACL2::DISTRIBUTIVITY] [axioms: ] []
     |- |= equal (mult x (add y z)) (add (mult x y) (mult x z)),
*)

val distributivity_defaxiom =
 store_thm
  ("distributivity_defaxiom",
   ``|= equal (mult x (add y z)) (add (mult x y) (mult x z))``,
   Cases_on `x` THEN Cases_on `y` THEN Cases_on `z`
    THEN ACL2_SIMP_TAC [int_def,nat_def,cpx_def]
    THEN ACL2_FULL_SIMP_TAC
          [COMPLEX_ADD_def,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_LID]
    THEN TRY(Cases_on `c`)
    THEN TRY(Cases_on `c'`)
    THEN TRY(Cases_on `c''`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_MULT_def,complex_rational_11,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL]
    THEN PROVE_TAC[ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_ADD_COMM]);

(*
     [oracles: DEFAXIOM ACL2::<-ON-OTHERS, DISK_THM] [axioms: ] []
     |- |= equal (less x y) (less (add x (unary_minus y)) (nat 0)),
*)

val less_on_others_defaxiom =
 store_thm
  ("less_on_others_defaxiom",
   ``|= equal (less x y) (less (add x (unary_minus y)) (nat 0))``,
   Cases_on `x` THEN Cases_on `y` 
    THEN ACL2_SIMP_TAC [int_def,nat_def,cpx_def]
    THEN ACL2_FULL_SIMP_TAC
          [COMPLEX_ADD_def,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,ratTheory.RAT_LES_REF,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_LID]
    THEN TRY(Cases_on `c`)
    THEN TRY(Cases_on `c'`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_0]
    THEN Cases_on `0 < r`
    THEN FULL_SIMP_TAC arith_ss [eq_imp_if]
    THEN PROVE_TAC
          [ratTheory.RAT_LEQ_LES,ratTheory.RAT_AINV_0,ratTheory.RAT_LES_AINV,
           ratTheory.rat_leq_def,ratTheory.RAT_LES_TOTAL,
           ratTheory.RAT_ADD_LINV,ratTheory.RAT_ADD_RINV,
           ratTheory.RAT_LES_LADD,ratTheory.RAT_LES_RADD]);

(*
     [oracles: DEFAXIOM ACL2::ZERO, DISK_THM] [axioms: ] []
     |- |= not (less (nat 0) (nat 0)),
*)

val zero_defaxiom =
 store_thm
  ("zero_defaxiom",
   ``|= not (less (nat 0) (nat 0))``,
   ACL2_SIMP_TAC [int_def,nat_def,cpx_def,ratTheory.RAT_LES_REF]);

(*
     [oracles: DEFAXIOM ACL2::TRICHOTOMY, DISK_THM] [axioms: ] []
     |- |= andl
             [implies (acl2_numberp x)
                (itel
                   [(less (nat 0) x,less (nat 0) x);
                    (equal x (nat 0),equal x (nat 0))]
                   (less (nat 0) (unary_minus x)));
              ite (not (less (nat 0) x)) (not (less (nat 0) x))
                (not (less (nat 0) (unary_minus x)))],
*)

val trichotomy_defaxiom =
 store_thm
  ("trichotomy_defaxiom",
   ``|= andl
         [implies 
           (acl2_numberp x)
           (itel
             [(less (nat 0) x,less (nat 0) x);
              (equal x (nat 0),equal x (nat 0))]
              (less (nat 0) (unary_minus x)));
              ite (not (less (nat 0) x)) 
                  (not (less (nat 0) x))
                  (not (less (nat 0) (unary_minus x)))]``,
   Cases_on `x` 
    THEN ACL2_SIMP_TAC [int_def,nat_def,cpx_def]
    THEN ACL2_FULL_SIMP_TAC
          [COMPLEX_ADD_def,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,ratTheory.RAT_LES_REF,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_LID]
    THEN TRY(Cases_on `c`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_0]
    THEN Cases_on `0 < r`
    THEN FULL_SIMP_TAC arith_ss 
          [eq_imp_if,itel_def,sexp_11,T_NIL,ite_def,t_def,nil_def]
    THEN RW_TAC arith_ss []
    THEN METIS_TAC
          [ratTheory.RAT_LEQ_LES,ratTheory.RAT_AINV_0,ratTheory.RAT_LES_AINV,
           ratTheory.rat_leq_def,ratTheory.RAT_LES_TOTAL,
           ratTheory.RAT_ADD_LINV,ratTheory.RAT_ADD_RINV,
           ratTheory.RAT_LES_LADD,ratTheory.RAT_LES_RADD]);

(*
     [oracles: DEFAXIOM ACL2::POSITIVE, DISK_THM] [axioms: ] []
     |- |= andl
             [implies (andl [less (nat 0) x; less (nat 0) y])
                (less (nat 0) (add x y));
              implies
                (andl
                   [rationalp x; rationalp y; less (nat 0) x;
                    less (nat 0) y]) (less (nat 0) (mult x y))],
*)

val positive_defaxiom =
 time store_thm
  ("positive_defaxiom",
   ``|= andl
         [implies 
           (andl [less (nat 0) x; less (nat 0) y])
           (less (nat 0) (add x y));
          implies
           (andl
             [rationalp x; rationalp y; less (nat 0) x;
              less (nat 0) y]) 
           (less (nat 0) (mult x y))]``,
   Cases_on `x`  THEN Cases_on `y`
    THEN ACL2_SIMP_TAC [int_def,nat_def,cpx_def]
    THEN ACL2_FULL_SIMP_TAC
          [COMPLEX_ADD_def,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,ratTheory.RAT_LES_REF,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_LID]
    THEN TRY(Cases_on `c`)
    THEN TRY(Cases_on `c'`)
    THEN TRY(Cases_on `0 < r`) 
    THEN TRY(Cases_on `0 < r'`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,rationalp_def,
           t_def,nil_def]
    THEN RW_TAC arith_ss []
    THEN METIS_TAC
          [ratTheory.RAT_LEQ_LES,ratTheory.RAT_AINV_0,ratTheory.RAT_LES_AINV,
           ratTheory.rat_leq_def,ratTheory.RAT_LES_TOTAL,
           ratTheory.RAT_ADD_LINV,ratTheory.RAT_ADD_RINV,
           ratTheory.RAT_LES_LADD,ratTheory.RAT_LES_RADD,
           ratTheory.RAT_0LES_0LES_ADD,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_LES_RMUL_POS]);

(*
     [oracles: DEFAXIOM ACL2::RATIONAL-IMPLIES1, DISK_THM] [axioms: ] []
     |- |= implies (rationalp x)
             (andl
                [integerp (denominator x); integerp (numerator x);
                 less (nat 0) (denominator x)]),
*)

(*****************************************************************************)
(* Note: Some of the auxiliary theorems below turned out not to be           *)
(*       needed. I'm leaving them here as they might find uses later.        *)
(*       May tidy up when all the axioms are proved.                         *)
(*****************************************************************************)

val Num_EQ_0 =
 if_store_thm
  ("Num_EQ_0",
   ``0 <= n ==> ((Num n = 0) = (n = 0))``,
   STRIP_TAC
    THEN EQ_TAC
    THEN RW_TAC arith_ss [integerTheory.NUM_OF_INT]
    THEN Cases_on `n = 0`
    THEN RW_TAC arith_ss []
    THEN `0 < n`  by intLib.ARITH_TAC
    THEN `1 <= n` by intLib.ARITH_TAC
    THEN `1 <= Num n` by PROVE_TAC[integerTheory.LE_NUM_OF_INT]
    THEN intLib.ARITH_TAC);

val Num_pos =
 if_store_thm
  ("Num_pos",
   ``0 < n ==> 0 < Num n``,
   STRIP_TAC
    THEN `0 <= n`  by intLib.ARITH_TAC
    THEN `0 <= Num n` by PROVE_TAC[integerTheory.LE_NUM_OF_INT]
    THEN Cases_on `0 = Num n`
    THEN IMP_RES_TAC Num_EQ_0
    THEN Cooper.COOPER_TAC);

val num_init_0_lemma =
 if_store_thm
  ("num_init_0_lemma",
   ``!n:num. ~(n = 0) ==> ~((&n):int = 0)``,
   Cooper.COOPER_TAC);

val div_pos =
 if_store_thm
  ("div_pos",
   ``!m n:int. 0 < n /\ n <= m  ==> 0 < (m/n)``,
   RW_TAC arith_ss 
    [Cooper.COOPER_PROVE ``(0:int) < n ==> ~(n = 0)``,
     integerTheory.int_div,Cooper.COOPER_PROVE ``(0:int) = & 0``,
     integerTheory.INT_LT,integerTheory.INT_ADD_CALCULATE]
    THEN RW_TAC std_ss 
          [integerTheory.int_div,Cooper.COOPER_PROVE ``(0:int) = ~& 0``,
           integerTheory.INT_LT_CALCULATE]
    THEN TRY Cooper.COOPER_TAC
    THEN IMP_RES_TAC Num_pos
    THEN RW_TAC arith_ss [arithmeticTheory.X_LT_DIV]
    THEN RW_TAC arith_ss [GSYM integerTheory.INT_LE]
    THEN `0 <= n` by Cooper.COOPER_TAC
    THEN `&(Num n) = n` by PROVE_TAC[integerTheory.INT_OF_NUM]
    THEN `&(Num m) = m` by PROVE_TAC[integerTheory.INT_OF_NUM]
    THEN RW_TAC std_ss []);

(* Also proved (differently) in translateScript.sml *)
val gcd_less_eq =
 if_store_thm
  ("gcd_less_eq",
   ``0 < n ==> gcd m n <= n``,
   Cases_on `m = 0` THEN Cases_on `n = 0`
    THEN RW_TAC arith_ss [gcdTheory.gcd_def]
    THEN `?p q. (n = p * gcd n m) /\ (m = q * gcd n m) /\ (gcd p q = 1)`
          by METIS_TAC[gcdTheory.FACTOR_OUT_GCD]
    THEN `~(p = 0)` by METIS_TAC[arithmeticTheory.MULT_CLAUSES]
    THEN `?a. p = SUC a` by Cooper.COOPER_TAC
    THEN RW_TAC arith_ss []
    THEN FULL_SIMP_TAC arith_ss [arithmeticTheory.MULT_CLAUSES]
    THEN `?b. n = b + gcd m n` by METIS_TAC[gcdTheory.GCD_SYM]
    THEN DECIDE_TAC);

val gcd_mod1 =
 if_store_thm
  ("gcd_mod1",
  ``!m n. ~(n = 0) /\ ~(m = 0) ==> (&m % &(gcd m n) = 0)``,
  RW_TAC std_ss []
   THEN `?p q. (m = p * gcd m n) /\ (n = q * gcd m n) /\ (gcd p q = 1)`
         by METIS_TAC[FACTOR_OUT_GCD]
   THEN `~(gcd m n = 0)` by METIS_TAC[gcdTheory.GCD_EQ_0]
   THEN `(& m):int = (& ( p * (gcd m n)))` by METIS_TAC[]
   THEN FULL_SIMP_TAC std_ss [GSYM integerTheory.INT_MUL]
   THEN `~((&(gcd m n)):int = 0)` by Cooper.COOPER_TAC
   THEN METIS_TAC[integerTheory.INT_MOD_EQ0]);

val gcd_mod2 =
 if_store_thm
  ("gcd_mod2",
  ``!m n. ~(n = 0) /\ ~(m = 0) ==> (&n % &(gcd m n) = 0)``,
  METIS_TAC[gcd_mod1,gcdTheory.GCD_SYM]);

(* From translateScript.sml *)
local open integerTheory Cooper 
in
val num_abs_nz = 
 if_store_thm
  ("num_abs_nz",
   ``0 < b \/ ~(b = 0) ==> ~(Num (ABS b) = 0)``,
   DISCH_TAC THEN ONCE_REWRITE_TAC [GSYM INT_EQ_CALCULATE] THEN
    RW_TAC std_ss 
     [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_ABS_POS] THEN
    COOPER_TAC)
end;

(* From translateScript.sml, where it is called "r2" *)
local open integerTheory Cooper 
in
val eq_num = 
 if_store_thm
  ("eq_num",
   ``0 < a ==> (a = & (Num a))``,
   METIS_TAC [INT_NEG_GT0,INT_OF_NUM,INT_LT_IMP_LE]);
end;

val abs_rat_reduce =
 if_store_thm
  ("abs_rat_reduce",
   ``0 < n 
     ==> 
     (abs_rat(abs_frac(reduce(m,n))) = abs_rat(abs_frac(m,n)))``,
   RW_TAC std_ss 
    [reduce_def,ratTheory.RAT_ABS_EQUIV,ratTheory.rat_equiv_def,
     fracTheory.NMR,fracTheory.DNM]
    THEN `0 <= n /\ ~(n =0)` by Cooper.COOPER_TAC
    THEN `~(gcd (Num (ABS m)) (Num (ABS n)) = 0)`
          by PROVE_TAC [integerTheory.INT_ABS_EQ0,
                        integerTheory.INT_ABS_POS,
                        Num_EQ_0,gcdTheory.GCD_EQ_0]
    THEN IMP_RES_TAC num_init_0_lemma 
    THEN `~(n' = 0)` 
          by PROVE_TAC[markerTheory.Abbrev_def]
    THEN `0 < Num(ABS n)` 
          by PROVE_TAC[intExtensionTheory.ABS_NOT_0_POSITIVE,Num_pos]
    THEN `gcd (Num (ABS m)) (Num (ABS n)) <= Num (ABS n)`
          by METIS_TAC[gcd_less_eq]
    THEN IMP_RES_TAC
          (Cooper.COOPER_PROVE ``(m:num) <= n ==> (&m):int <= &n``)
    THEN `n' <= &(Num (ABS n))` by PROVE_TAC[markerTheory.Abbrev_def]
    THEN `0 < ABS n` 
          by PROVE_TAC[intExtensionTheory.ABS_NOT_0_POSITIVE]
    THEN `0 <= ABS n` by Cooper.COOPER_TAC
    THEN `n' <= ABS n` by PROVE_TAC[integerTheory.INT_OF_NUM]
    THEN `n' <= n` by Cooper.COOPER_TAC
    THEN `0 <= n'` 
          by PROVE_TAC
              [Cooper.COOPER_PROVE ``(0:int) <= & n``,
               markerTheory.Abbrev_def]
    THEN `0 < n'` by Cooper.COOPER_TAC
    THEN `0 < n/n'` by PROVE_TAC[div_pos]
    THEN RW_TAC std_ss [fracTheory.NMR,fracTheory.DNM]
    THEN `(m / n' * n = m * (n / n')) = 
           ((m / n' * n') * n = m * ((n / n') * n'))`
          by PROVE_TAC
           [Q.SPECL 
             [`m / n' * n `, `m * (n / n')`,`n'`]
             intExtensionTheory.INT_EQ_RMUL_EXP,
            integerTheory.INT_MUL_ASSOC,
            integerTheory.INT_MUL_COMM]
    THEN ASM_REWRITE_TAC[]
    THEN POP_ASSUM(K ALL_TAC)
    THEN Cases_on `m = 0`
    THEN RW_TAC arith_ss 
          [integerTheory.INT_MUL_REDUCE,integerTheory.INT_DIV_0]
    THEN `& (Num (ABS m)) % n' = 0`
          by METIS_TAC
              [Q.SPECL[`Num(ABS m)`,`Num(ABS n)`]gcd_mod1,
               markerTheory.Abbrev_def,num_abs_nz]
    THEN `n % n' = 0`
          by METIS_TAC
              [Q.SPECL[`Num(ABS m)`,`Num(ABS n)`]gcd_mod2,
               markerTheory.Abbrev_def,num_abs_nz,eq_num,
               integerTheory.INT_ABS_EQ_ID]
    THEN RW_TAC arith_ss [integerTheory.INT_DIV_MUL_ID]
    THEN Cases_on `0 < m`
    THENL
     [`0 <= m` by Cooper.COOPER_TAC
       THEN `m % n' = 0` 
             by METIS_TAC[eq_num,integerTheory.INT_ABS_EQ_ID]
       THEN RW_TAC arith_ss [integerTheory.INT_DIV_MUL_ID],
      `m < 0` by Cooper.COOPER_TAC      
       THEN `?m'. 0 < m' /\ (m = ~m')` by Cooper.COOPER_TAC
       THEN RW_TAC arith_ss []
       THEN FULL_SIMP_TAC arith_ss [integerTheory.INT_ABS_NEG]
       THEN `0 <= m'` by Cooper.COOPER_TAC
       THEN `m' % n' = 0` 
             by METIS_TAC[eq_num,integerTheory.INT_ABS_EQ_ID]
       THEN `m'/n' * n' = m'` 
             by METIS_TAC[integerTheory.INT_DIV_MUL_ID]
       THEN `~m' = (~1)*m'` 
             by PROVE_TAC[integerTheory.INT_NEG_MINUS1]
       THEN RW_TAC arith_ss [integerTheory.INT_MUL_DIV]
       THEN METIS_TAC[integerTheory.INT_MUL_ASSOC]]);

val frac_dnm_pos = 
 if_store_thm
   ("frac_dnm_pos",
    ``0 < frac_dnm n``,
    METIS_TAC[fracTheory.frac_dnm_def,fracTheory.frac_bij]);

(*****************************************************************************)
(*   |- abs_rat (abs_frac (reduce (rep_frac (rep_rat r)))) = r               *)
(*****************************************************************************)
val abs_rat_reduce_cor =
 if_save_thm
  ("abs_rat_reduce_cor",
   SIMP_RULE std_ss
    [GSYM fracTheory.frac_dnm_def,frac_dnm_pos,fracTheory.frac_bij,
     ratTheory.RAT]
    (Q.SPECL 
      [`SND(rep_frac(rep_rat r))`,`FST(rep_frac (rep_rat r))`]
      (GEN_ALL abs_rat_reduce)));

(* From translateScript.sml *)
local open integerTheory
in
val num_nz = 
 prove
  (``0 < a ==> ~(Num a = 0)``,
   ONCE_REWRITE_TAC [GSYM INT_EQ_CALCULATE] 
   THEN RW_TAC std_ss 
         [snd (EQ_IMP_RULE (SPEC_ALL INT_OF_NUM)),INT_LT_IMP_LE] 
   THEN Cooper.COOPER_TAC)
end;

(* From translateScript.sml *)
local 
open intLib integerTheory fracTheory 
     intExtensionTheory arithmeticTheory
in
val reduced_dnm_pos = 
 if_store_thm
   ("reduced_dnm_pos",
    ``0 < reduced_dnm x``,
    FULL_SIMP_TAC int_ss [reduced_dnm_def] 
     THEN SUBGOAL_THEN 
           ``rep_frac (rep_rat x) = (frac_nmr (rep_rat x),frac_dnm (rep_rat x))`` 
           SUBST_ALL_TAC 
     THEN1 RW_TAC std_ss [frac_nmr_def,frac_dnm_def] 
     THEN FULL_SIMP_TAC (int_ss ++ boolSimps.LET_ss) [reduce_def] 
     THEN RW_TAC int_ss 
           [FRAC_DNMPOS,INT_ABS_CALCULATE_POS,num_nz,gcdTheory.GCD_EQ_0,int_div] 
     THEN FULL_SIMP_TAC arith_ss 
           [num_nz,gcdTheory.GCD_EQ_0,DECIDE ``~(0 < a) = (a = 0n)``,
            FRAC_DNMPOS,X_LT_DIV,gcd_less_eq,DECIDE ``~(a = 0n) ==> 0 < a``])
end;

val rational_implies1_defaxiom =
 time store_thm
  ("rational_implies1_defaxiom",
   ``|= implies 
         (rationalp x)
         (andl
           [integerp (denominator x); integerp (numerator x);
            less (nat 0) (denominator x)])``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC [int_def,nat_def,cpx_def]
    THEN ACL2_FULL_SIMP_TAC
          [COMPLEX_ADD_def,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,ratTheory.RAT_LES_REF,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_LID]
    THEN TRY(Cases_on `c`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,
           t_def,nil_def]
    THEN RW_TAC arith_ss []
    THEN FULL_SIMP_TAC std_ss 
          [GSYM t_def,GSYM nil_def,integerp_def,
           reduced_nmr_def,reduced_dnm_def,if_t_nil,(* DIVIDES_def, *)
           IS_INT_EXISTS,ratTheory.RAT_0,less_def,ratTheory.RAT_LES_REF]
    THEN Cases_on `0 < abs_rat (abs_frac (SND (reduce (rep_frac (rep_rat r))),1))`
    THEN TRY (METIS_TAC [])
    THEN FULL_SIMP_TAC intLib.int_ss 
          [GSYM reduced_dnm_def,ratTheory.rat_les_def,
           ratTheory.RAT_SUB_RID,ratTheory.RAT_SGN_CALCULATE,
           fracTheory.FRAC_SGN_CALCULATE,intExtensionTheory.INT_SGN_CLAUSES,
           integerTheory.int_gt,reduced_dnm_pos]);

(*
     [oracles: DEFAXIOM ACL2::RATIONAL-IMPLIES2] [axioms: ] []
     |- |= implies (rationalp x)
             (equal (mult (reciprocal (denominator x)) (numerator x)) x),
*)

(* From translateScript.sml *)
local open ratTheory
in
val rat_divshiftthm = 
 if_store_thm
  ("rat_divshiftthm",
   ``a * (b / c) = a * b / c:rat``,
   RW_TAC std_ss [RAT_DIV_MULMINV,RAT_MUL_ASSOC]);
end;

(* From translateScript.sml *)
local 
open ratTheory fracTheory translateTheory
in
val RAT_DIV = 
 if_store_thm
  ("RAT_DIV",
   ``!a b. ~(b = 0) ==> (rat (a / b) = mult (rat a) (reciprocal (rat b)))``,
   RW_TAC std_ss 
     [translateTheory.rat_def,mult_def,reciprocal_def,COMPLEX_RECIPROCAL_def,rat_0_def,
      GSYM rat_0,COMPLEX_MULT_def,RAT_MUL_RZERO,
      RAT_ADD_RID,RAT_MUL_LZERO,RAT_ADD_LID,RAT_AINV_0,int_def,
      RAT_SUB_RID,com_0_def,complex_rational_11,cpx_def,sexpTheory.rat_def,
      GSYM frac_0_def,RAT_LDIV_EQ,rat_divshiftthm,RAT_NO_ZERODIV_NEG,
      RAT_RDIV_EQ,RAT_MUL_ASSOC] 
    THEN CONV_TAC (AC_CONV (RAT_MUL_ASSOC,RAT_MUL_COMM)));
end;

val rationalp_rat =
 if_store_thm
  ("rationalp_rat",
   ``(|= rationalp x) = ?a. x = rat a``,
   Cases_on `x`
    THEN RW_TAC std_ss [ACL2_TRUE,rationalp_def,translateTheory.rat_def]
    THEN Cases_on `c`
    THEN ACL2_FULL_SIMP_TAC []
    THEN Cases_on `r0 = rat_0`
    THEN ACL2_FULL_SIMP_TAC [complex_rational_11]
    THEN METIS_TAC[]);

val mult_comm =
 if_store_thm
  ("mult_comm",
   ``mult x y = mult y x``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC []
    THEN METIS_TAC[complex_rationalTheory.COMPLEX_MULT_COMM]);

(* From translateScript.sml *)
val nmr_dnm_rewrite = 
 if_store_thm
  ("nmr_dnm_rewrite",
   ``(numerator (rat a) = int (reduced_nmr a))
     /\ 
     (denominator (rat a) = int (reduced_dnm a))``,
   RW_TAC std_ss 
    [numerator_def,denominator_def,translateTheory.rat_def]);

val nz_rat_1 =
 if_store_thm
  ("nz_rat_1",
   ``0 < a ==> ~(abs_rat (abs_frac (a,1)) = 0)``,
   RW_TAC intLib.int_ss
     [ratTheory.rat_0,ratTheory.RAT_ABS_EQUIV,ratTheory.rat_equiv_def,
      fracTheory.NMR,fracTheory.DNM,fracTheory.frac_0_def]
    THEN Cooper.COOPER_TAC);

val rational_implies2_defaxiom =
 time store_thm
  ("rational_implies2_defaxiom",
   ``|= implies
         (rationalp x)
         (equal (mult (reciprocal (denominator x)) (numerator x)) x)``,
   RW_TAC std_ss 
    [implies,rationalp_rat,GSYM translateTheory.COM_THMS]
    THEN ONCE_REWRITE_TAC[mult_comm]
    THEN RW_TAC intLib.int_ss
          [nmr_dnm_rewrite,int_def,cpx_def,sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,GSYM ratTheory.rat_0_def,
           GSYM translateTheory.rat_def]
    THEN `0 < reduced_dnm a` by METIS_TAC[reduced_dnm_pos]
    THEN `~(abs_rat (abs_frac (reduced_dnm a,1)) = 0)` by METIS_TAC[nz_rat_1]
    THEN  RW_TAC std_ss [GSYM RAT_DIV]
    THEN `~(frac_nmr(abs_frac (reduced_dnm a,1)) = 0)`
          by METIS_TAC
              [Cooper.COOPER_PROVE``(0:int) < 1``,
               Cooper.COOPER_PROVE``(0:int) < n ==> ~(n = 0)``,
               fracTheory.NMR]
    THEN RW_TAC intLib.int_ss [ratTheory.RAT_DIV_CALCULATE]
    THEN `(0:int) < 1` by Cooper.COOPER_TAC
    THEN `~(reduced_dnm a = 0)` by Cooper.COOPER_TAC
    THEN RW_TAC intLib.int_ss [fracTheory.FRAC_DIV_CALCULATE]
    THEN RW_TAC intLib.int_ss [GSYM translateTheory.RAT_THMS,translateTheory.TRUTH_REWRITES]
    THEN `ABS (reduced_dnm a) = reduced_dnm a` by Cooper.COOPER_TAC
    THEN `reduced_dnm a > 0 ` by Cooper.COOPER_TAC
    THEN `SGN (reduced_dnm a) = 1` by METIS_TAC[intExtensionTheory.INT_SGN_CLAUSES]
    THEN RW_TAC intLib.int_ss []
    THEN RW_TAC std_ss [reduced_nmr_def,reduced_dnm_def,abs_rat_reduce_cor]);

(*
     [oracles: DEFAXIOM ACL2::INTEGER-IMPLIES-RATIONAL] [axioms: ] []
     |- |= implies (integerp x) (rationalp x),
*)

val integer_implies_rational_defaxiom =
 store_thm
  ("integer_implies_rational_defaxiom",
   ``|= implies (integerp x) (rationalp x)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC []
    THEN Cases_on `c`
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,
           t_def,nil_def,IS_INT_EXISTS]);

(*
     [oracles: DEFAXIOM ACL2::COMPLEX-IMPLIES1, DISK_THM] [axioms: ] []
     |- |= andl [rationalp (realpart x); rationalp (imagpart x)],
*)

val complex_implies1_defaxiom =
 store_thm
  ("complex_implies1_defaxiom",
   ``|= andl [rationalp (realpart x); rationalp (imagpart x)]``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC []
    THEN TRY(Cases_on `c`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,realpart_def,imagpart_def,
           t_def,nil_def,IS_INT_EXISTS]);

(*
     [oracles: DEFAXIOM ACL2::COMPLEX-DEFINITION, DISK_THM] [axioms: ] []
     |- |= implies (andl [rationalp x; rationalp y])
             (equal (complex x y) (add x (mult (cpx 0 1 1 1) y))),
*)

val complex_definition_defaxiom =
 store_thm
  ("complex_definition_defaxiom",
   ``|= implies 
          (andl [rationalp x; rationalp y])
          (equal (complex x y) (add x (mult (cpx 0 1 1 1) y)))``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC []
    THEN TRY(Cases_on `c`)
    THEN TRY(Cases_on `c'`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,realpart_def,imagpart_def,
           t_def,nil_def,IS_INT_EXISTS,
           complex_def,add_def,mult_def]
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss 
          [ratTheory.RAT_MUL_RZERO,ratTheory.RAT_AINV_0,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,
           GSYM fracTheory.frac_1_def,GSYM ratTheory.rat_1,
           ratTheory.RAT_MUL_LID]);

(*
     [oracles: DEFAXIOM ACL2::NONZERO-IMAGPART, DISK_THM] [axioms: ] []
     |- |= implies (complex_rationalp x) (not (equal (nat 0) (imagpart x))),
*)

val nonzero_imagpart_defaxiom =
 store_thm
  ("non_zero_imagpart_defaxiom",
   ``|= implies (complex_rationalp x) (not (equal (nat 0) (imagpart x)))``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC []
    THEN Cases_on `c`
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,realpart_def,imagpart_def,
           t_def,nil_def,IS_INT_EXISTS,
           complex_def,add_def,mult_def,complex_rationalp_def,
           nat_def,int_def,cpx_def]
    THEN RW_TAC std_ss []);

(*
     [oracles: DEFAXIOM ACL2::REALPART-IMAGPART-ELIM] [axioms: ] []
     |- |= implies (acl2_numberp x)
             (equal (complex (realpart x) (imagpart x)) x),
*)

val realpart_imagpart_elim_defaxiom =
 store_thm
  ("realpart_imagpart_elim_defaxiom",
   ``|= implies 
         (acl2_numberp x)
         (equal (complex (realpart x) (imagpart x)) x)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC []
    THEN Cases_on `c`
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,realpart_def,imagpart_def,
           t_def,nil_def,IS_INT_EXISTS,
           complex_def,add_def,mult_def,complex_rationalp_def,
           nat_def,int_def,cpx_def]
    THEN RW_TAC std_ss []);

(*
     [oracles: DEFAXIOM ACL2::REALPART-COMPLEX, DISK_THM] [axioms: ] []
     |- |= implies (andl [rationalp x; rationalp y])
             (equal (realpart (complex x y)) x),
*)

val realpart_complex_defaxiom =
 store_thm
  ("realpart_complex_defaxiom",
   ``|= implies 
         (andl [rationalp x; rationalp y])
         (equal (realpart (complex x y)) x)``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC []
    THEN Cases_on `c`
    THEN Cases_on `c'`
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,realpart_def,imagpart_def,
           t_def,nil_def,IS_INT_EXISTS,
           complex_def,add_def,mult_def,complex_rationalp_def,
           nat_def,int_def,cpx_def]
    THEN RW_TAC std_ss []);

(*
     [oracles: DEFAXIOM ACL2::IMAGPART-COMPLEX, DISK_THM] [axioms: ] []
     |- |= implies (andl [rationalp x; rationalp y])
             (equal (imagpart (complex x y)) y),
*)

val imagpart_complex_defaxiom =
 store_thm
  ("imagpart_complex_defaxiom",
   ``|= implies 
         (andl [rationalp x; rationalp y])
         (equal (imagpart (complex x y)) y)``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC []
    THEN Cases_on `c`
    THEN Cases_on `c'`
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,realpart_def,imagpart_def,
           t_def,nil_def,IS_INT_EXISTS,
           complex_def,add_def,mult_def,complex_rationalp_def,
           nat_def,int_def,cpx_def]
    THEN RW_TAC std_ss []);

(*
     [oracles: DEFAXIOM ACL2::NONNEGATIVE-PRODUCT, DISK_THM] [axioms: ] []
     |- |= implies (rationalp x)
             (andl [rationalp (mult x x); not (less (mult x x) (nat 0))]),
*)

val nonnegative_product_defaxiom =
 store_thm
  ("nonnegative_product_defaxiom",
   ``|= implies 
         (rationalp x)
         (andl [rationalp (mult x x); not (less (mult x x) (nat 0))])``,
   Cases_on `x` 
    THEN ACL2_SIMP_TAC []
    THEN Cases_on `c`
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,realpart_def,imagpart_def,
           t_def,nil_def,IS_INT_EXISTS,
           complex_def,add_def,mult_def,complex_rationalp_def,
           nat_def,int_def,cpx_def]
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss 
          [ratTheory.RAT_MUL_RZERO,ratTheory.RAT_AINV_0,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,
           GSYM fracTheory.frac_1_def,GSYM ratTheory.rat_1,
           ratTheory.RAT_MUL_LID,ratTheory.RAT_MUL_LZERO]
    THEN METIS_TAC[RAT_SQ_NONNEG,ratTheory.RAT_LEQ_LES]);

(*
     [oracles: DEFAXIOM ACL2::INTEGER-0, DISK_THM] [axioms: ] []
     |- |= integerp (nat 0),
*)

val integer_0_defaxiom =
 store_thm
  ("integer_0_defaxiom",
   ``|= integerp (nat 0)``,
   ACL2_SIMP_TAC
    [nat_def,int_def,cpx_def,
     translateTheory.IS_INT_EXISTS,
     sexpTheory.rat_def,ratTheory.rat_0_def,fracTheory.frac_0_def]
    THEN PROVE_TAC[]);

(*
     [oracles: DEFAXIOM ACL2::INTEGER-1, DISK_THM] [axioms: ] []
     |- |= integerp (nat 1),
*)

val integer_1_defaxiom =
 store_thm
  ("integer_1_defaxiom",
   ``|= integerp (nat 1)``,
   ACL2_SIMP_TAC
    [nat_def,int_def,cpx_def,
     translateTheory.IS_INT_EXISTS,
     sexpTheory.rat_def,ratTheory.rat_0_def,ratTheory.rat_1_def,
     fracTheory.frac_0_def,fracTheory.frac_1_def]
    THEN PROVE_TAC[]);

(*
     [oracles: DEFAXIOM ACL2::INTEGER-STEP, DISK_THM] [axioms: ] []
     |- |= implies (integerp x)
             (andl [integerp (add x (nat 1)); integerp (add x (int ~1))]),
*)

val integer_step_defaxiom =
 store_thm
  ("integer_step_defaxiom",
   ``|= implies
         (integerp x)
         (andl [integerp (add x (nat 1)); integerp (add x (int ~1))])``,
   Cases_on `x` 
    THEN ACL2_SIMP_TAC []
    THEN Cases_on `c`
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,realpart_def,imagpart_def,
           t_def,nil_def,IS_INT_EXISTS,
           complex_def,add_def,mult_def,complex_rationalp_def,
           nat_def,int_def,cpx_def]
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC intLib.int_ss
          [ratTheory.RAT_MUL_RZERO,ratTheory.RAT_AINV_0,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,
           ratTheory.RAT_MUL_LID,ratTheory.RAT_MUL_LZERO,
           ratTheory.RAT_ADD_CALCULATE,fracTheory.FRAC_ADD_CALCULATE]
    THEN `!c'. ~(abs_rat (abs_frac (c + ~1,1)) = abs_rat (abs_frac (c',1)))`
          by METIS_TAC[]
    THEN FULL_SIMP_TAC intLib.int_ss
          [ratTheory.RAT_EQ_CALCULATE,fracTheory.NMR,fracTheory.DNM]);

(*
     [oracles: DEFAXIOM ACL2::LOWEST-TERMS, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [integerp n; rationalp x; integerp r; integerp q;
                 less (nat 0) n; equal (numerator x) (mult n r);
                 equal (denominator x) (mult n q)]) (equal n (nat 1)),
*)

val div_eq_mult =
 if_store_thm
  ("div_eq_mult",
   ``!m n p:int. ~(n = 0) /\ (m % n = 0) ==> ((m / n = p) = (m = p * n))``,
   RW_TAC intLib.int_ss []
    THEN IMP_RES_TAC integerTheory.INT_DIV_MUL_ID
    THEN EQ_TAC
    THEN RW_TAC intLib.int_ss []
    THEN FULL_SIMP_TAC std_ss [integerTheory.INT_EQ_RMUL]
    THEN METIS_TAC[]);

val num_abs_mod_0 =
 if_store_thm
  ("num_abs_mod_0",
   ``~(n = 0) ==> ((& (Num (ABS m)) % n = 0) = (m % n = 0))``,
   RW_TAC intLib.int_ss [integerTheory.INT_MOD_EQ0]
    THEN EQ_TAC
    THEN RW_TAC intLib.int_ss [] 
    THENL
     [`0 <= ABS m` by Cooper.COOPER_TAC
       THEN `ABS m = k * n` by METIS_TAC[integerTheory.INT_OF_NUM]
       THEN Cases_on `0 <= m`
       THENL
        [`ABS m = m` by Cooper.COOPER_TAC
          THEN PROVE_TAC[],
         `m = (~1 * k) * n` by Cooper.COOPER_TAC
          THEN PROVE_TAC[]],
      Cases_on `0 <= k * n`
       THEN `0 <= ABS(k * n)` by Cooper.COOPER_TAC
       THEN `& (Num (ABS (k * n))) = ABS (k * n)` 
             by METIS_TAC[integerTheory.INT_OF_NUM]
       THENL
        [`ABS(k * n) = k * n` by Cooper.COOPER_TAC
          THEN METIS_TAC[],
         `ABS(k * n) = (~1 * k) * n` by Cooper.COOPER_TAC
          THEN METIS_TAC[]]]);

val and_num_abs =
 if_store_thm
  ("and_num_abs",
   ``!n:int. &(Num(ABS n)) = ABS n``,
   METIS_TAC[integerTheory.INT_OF_NUM,integerTheory.INT_ABS_POS]);

val reduce0 =
 if_store_thm
  ("reduce0",
   ``!n. ~(n = 0) ==> (reduce(0,n) = (0,SGN n))``,
   RW_TAC intLib.int_ss [reduce_def]
    THEN FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def,gcdTheory.GCD_0L]
    THEN `0 <= ABS n` by Cooper.COOPER_TAC
    THEN `&(Num(ABS n)) = ABS n` by PROVE_TAC[integerTheory.INT_OF_NUM]
    THEN RW_TAC intLib.int_ss []
    THEN `~(ABS n = 0)` by Cooper.COOPER_TAC
    THEN RW_TAC intLib.int_ss [integerTheory.INT_DIV_0]
    THEN Cases_on `0 < n`
    THENL
     [`ABS n = n` by Cooper.COOPER_TAC
       THEN RW_TAC intLib.int_ss 
             [integerTheory.INT_DIV_ID,intExtensionTheory.INT_SGN_CLAUSES]
       THEN Cooper.COOPER_TAC,
      `(ABS n = ~n) /\ n < 0` by Cooper.COOPER_TAC
       THEN `SGN n = ~1` by METIS_TAC[intExtensionTheory.INT_SGN_CLAUSES]
       THEN RW_TAC intLib.int_ss [integerTheory.INT_DIV_NEG]
       THEN `~n = ~1 * n` by Cooper.COOPER_TAC
       THEN RW_TAC intLib.int_ss [integerTheory.INT_DIV_RMUL]]);

val reduce_lowest_terms =
 if_store_thm
  ("reduce_lowest_terms",
   ``~(SND r = 0) /\ (reduce r = (m*n1,m*n2)) ==> (Num (ABS m) = 1)``,
   Cases_on `(FST r = 0)`
    THENL
     [Cases_on `r`
       THEN FULL_SIMP_TAC std_ss []
       THEN RW_TAC std_ss []
       THEN `reduce (0,r') = (0, SGN r')` by METIS_TAC[reduce0]
       THEN `(m*n1 = 0) /\ (m*n2 = SGN r')` by METIS_TAC[pairTheory.CLOSED_PAIR_EQ]
       THEN Cases_on `r' > 0`
       THENL
        [`m * n2 = 1` 
          by METIS_TAC
              [intExtensionTheory.INT_SGN_CLAUSES]
          THEN FULL_SIMP_TAC intLib.int_ss [integerTheory.INT_MUL_EQ_1],
         `r' < 0` by Cooper.COOPER_TAC
          THEN `m * n2 = ~1` by METIS_TAC[intExtensionTheory.INT_SGN_CLAUSES]
          THEN `~(~(1:int) = 0)` by Cooper.COOPER_TAC
          THEN `m * (~1 * n2) = ~1 * ~1` 
                by METIS_TAC
                    [integerTheory.INT_EQ_LMUL2,
                     integerTheory.INT_MUL_ASSOC,integerTheory.INT_MUL_COMM]
          THEN `m * (~1 * n2) = 1` by Cooper.COOPER_TAC
          THEN FULL_SIMP_TAC intLib.int_ss [integerTheory.INT_MUL_EQ_1]
          THEN TRY(Cooper.COOPER_TAC)
          THEN `ABS(SGN r') = 1` by Cooper.COOPER_TAC
          THEN RW_TAC intLib.int_ss []],
      Cases_on `r`
       THEN FULL_SIMP_TAC std_ss [reduce_def,LET_DEF]
       THEN RW_TAC std_ss []
       THEN Cases_on `& (gcd (Num (ABS q)) (Num (ABS r'))) = 0:int`
       THENL
        [FULL_SIMP_TAC intLib.int_ss 
          [Cooper.COOPER_PROVE ``((&(n:num)):int = 0) = (n = 0)``,
           gcdTheory.GCD_EQ_0]
          THEN METIS_TAC[num_abs_nz],
         `~(Num (ABS q) = 0) /\ ~(Num (ABS r') = 0)`
          by METIS_TAC[num_abs_nz]
          THEN `0 < Num (ABS q) /\ 0 < Num (ABS r') /\ 0 <= ABS q /\ 0 <= ABS r'` 
                by Cooper.COOPER_TAC
          THEN `&(Num (ABS q))  = ABS q`  by METIS_TAC [integerTheory.INT_OF_NUM]
          THEN `&(Num (ABS r')) = ABS r'` by METIS_TAC [integerTheory.INT_OF_NUM]
          THEN `& (Num (ABS q))  % & (gcd (Num (ABS q)) (Num (ABS r'))) = 0`
                by METIS_TAC[gcd_mod1]
          THEN `& (Num (ABS r')) % & (gcd (Num (ABS q)) (Num (ABS r'))) = 0`
                by METIS_TAC[gcd_mod2]
          THEN `q % &  (gcd (Num (ABS q)) (Num (ABS r'))) = 0`
                by METIS_TAC[num_abs_mod_0]
          THEN `r' % & (gcd (Num (ABS q)) (Num (ABS r'))) = 0`
                by METIS_TAC[num_abs_mod_0]
          THEN `(m * n1 * & (gcd (Num (ABS q)) (Num (ABS r'))) = q)
                /\
                (m * n2 * & (gcd (Num (ABS q)) (Num (ABS r'))) = r')` 
                by METIS_TAC[div_eq_mult]
          THEN `(ABS m * ABS n1 * (& (gcd (Num (ABS q)) (Num (ABS r')))) = ABS q)
                /\
                (ABS m * ABS n2 * (& (gcd (Num (ABS q)) (Num (ABS r')))) = ABS r')` 
                by METIS_TAC[integerTheory.INT_ABS_MUL,integerTheory.INT_ABS_NUM]
          THEN `(&(Num(ABS m)) * &(Num(ABS n1)) * (& (gcd (Num (ABS q)) (Num (ABS r')))) :int =
                 &(Num(ABS q)))
                /\
                (&(Num(ABS m)) * &(Num(ABS n2)) * (& (gcd (Num (ABS q)) (Num (ABS r')))) :int = 
                 &(Num(ABS r')))` 
                by RW_TAC std_ss [and_num_abs]
          THEN FULL_SIMP_TAC std_ss [integerTheory.INT_MUL,integerTheory.INT_EQ_CALCULATE]
          THEN `divides (Num (ABS m) * gcd (Num (ABS q)) (Num (ABS r'))) (Num (ABS q))`
                by METIS_TAC
                    [dividesTheory.divides_def,arithmeticTheory.MULT_ASSOC,arithmeticTheory.MULT_COMM]
          THEN `divides (Num (ABS m) * gcd (Num (ABS q)) (Num (ABS r'))) (Num (ABS r'))`
                by METIS_TAC
                    [dividesTheory.divides_def,arithmeticTheory.MULT_ASSOC,arithmeticTheory.MULT_COMM]
          THEN `divides 
                  (Num (ABS m) * gcd (Num (ABS q)) (Num (ABS r')))
                  (gcd (Num (ABS q)) (Num (ABS r')))`
                by METIS_TAC[gcdTheory.GCD_IS_GCD,gcdTheory.is_gcd_def]
          THEN FULL_SIMP_TAC intLib.int_ss [dividesTheory.DIVIDES_MULT_LEFT]
          THEN RES_TAC
          THEN RW_TAC std_ss []]]);

val lowest_terms_defaxiom =
 time store_thm
  ("lowest_terms_defaxiom",
   ``|= implies
         (andl
           [integerp n; rationalp x; integerp r; integerp q;
            less (nat 0) n; equal (numerator x) (mult n r);
            equal (denominator x) (mult n q)])
         (equal n (nat 1))``,
   Cases_on `n`  THEN Cases_on `x` THEN Cases_on `r` THEN Cases_on `q` 
    THEN ACL2_SIMP_TAC []
    THEN TRY(Cases_on `c`)
    THEN TRY(Cases_on `c'`)
    THEN TRY(Cases_on `c''`)
    THEN TRY(Cases_on `c'''`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,realpart_def,imagpart_def,
           t_def,nil_def,IS_INT_EXISTS,
           complex_def,add_def,mult_def,complex_rationalp_def,
           nat_def,int_def,cpx_def]
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC intLib.int_ss
          [ratTheory.RAT_EQ_CALCULATE,fracTheory.NMR,fracTheory.DNM,
           ratTheory.RAT_MUL_CALCULATE,fracTheory.FRAC_MULT_CALCULATE]
    THEN `reduce (rep_frac (rep_rat r')) = (c*c',c*c'')`
          by METIS_TAC[reduced_nmr_def,reduced_dnm_def,pairTheory.PAIR]
    THEN `0 < SND(rep_frac (rep_rat r'))` 
          by METIS_TAC[fracTheory.FRAC_DNMPOS,fracTheory.frac_dnm_def]
    THEN `~(SND(rep_frac (rep_rat r')) = 0)`  by Cooper.COOPER_TAC
    THEN `&(Num (ABS c)):int = & 1` 
          by METIS_TAC[integerTheory.INT_EQ_CALCULATE,reduce_lowest_terms]
    THEN `0 <= ABS c` by Cooper.COOPER_TAC
    THEN `ABS c = 1` by METIS_TAC[integerTheory.INT_OF_NUM]
    THEN FULL_SIMP_TAC intLib.int_ss
          [GSYM ratTheory.RAT_0,ratTheory.rat_0_def,ratTheory.RAT_LES_CALCULATE,
           fracTheory.frac_0_def,fracTheory.frac_nmr_def,fracTheory.frac_dnm_def,
           SIMP_RULE intLib.int_ss [] (Q.SPEC `(0,1)` (CONJUNCT2 fracTheory.frac_bij)),
           SIMP_RULE intLib.int_ss [] (Q.SPEC `(c,1)` (CONJUNCT2 fracTheory.frac_bij))]
    THEN `c = 1` by Cooper.COOPER_TAC);


(*
     [oracles: DEFAXIOM ACL2::CAR-CDR-ELIM] [axioms: ] []
     |- |= implies (consp x) (equal (cons (car x) (cdr x)) x),
*)

val car_cdr_elim_defaxiom =
 store_thm
  ("car_dr_elim_defaxiom",
   ``|= implies (consp x) (equal (cons (car x) (cdr x)) x)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[]);

(*
     [oracles: DEFAXIOM ACL2::CAR-CONS] [axioms: ] []
     |- |= equal (car (cons x y)) x,
*)

val car_cons_defaxiom =
 store_thm
  ("car_cons_defaxiom",
   ``|= equal (car (cons x y)) x``,
   ACL2_SIMP_TAC []);

(*
     [oracles: DEFAXIOM ACL2::CDR-CONS] [axioms: ] []
     |- |= equal (cdr (cons x y)) y,
*)

val cdr_cons_defaxiom =
 store_thm
  ("cdr_cons_defaxiom",
   ``|= equal (cdr (cons x y)) y``,
   ACL2_SIMP_TAC []);

(*
     [oracles: DEFAXIOM ACL2::CONS-EQUAL, DISK_THM] [axioms: ] []
     |- |= equal (equal (cons x1 y1) (cons x2 y2))
             (andl [equal x1 x2; equal y1 y2]),
*)

val cons_equal_defaxiom =
 store_thm
  ("cons_equal_defaxiom",
   ``|= equal (equal (cons x1 y1) (cons x2 y2))
              (andl [equal x1 x2; equal y1 y2])``,
   ACL2_SIMP_TAC []
    THEN PROVE_TAC[sexp_11,T_NIL]);

(*
     [oracles: DEFAXIOM ACL2::BOOLEANP-CHARACTERP] [axioms: ] []
     |- |= booleanp (characterp x),
*)

val booleanp_characterp_defaxiom =
 store_thm
  ("booleanp_characterp_defaxiom",
   ``|= booleanp (characterp x)``,
   ACL2_SIMP_TAC []
    THEN Cases_on `x`
    THEN ACL2_FULL_SIMP_TAC[]);

(*
     [oracles: DEFAXIOM ACL2::CHARACTERP-PAGE] [axioms: ] []
     |- |= characterp (chr #"\f"),
*)

val characterp_page_defaxiom =
 store_thm
  ("characterp_page_defaxiom",
   ``|= characterp (chr #"\f")``,
   ACL2_SIMP_TAC []);

(*
     [oracles: DEFAXIOM ACL2::CHARACTERP-TAB] [axioms: ] []
     |- |= characterp (chr #"\t"),
*)

val characterp_tab_defaxiom =
 store_thm
  ("characterp_tab_defaxiom",
   ``|= characterp (chr #"\t")``,  
   ACL2_SIMP_TAC []);

(*
     [oracles: DEFAXIOM ACL2::CHARACTERP-RUBOUT] [axioms: ] []
     |- |= characterp (chr #"\127"),
*)

val characterp_rubout_defaxiom =
 store_thm
  ("characterp_rubout_defaxiom",
   ``|= characterp (chr #"\127")``,  
   ACL2_SIMP_TAC []);

(*
     [oracles: DEFAXIOM ACL2::COERCE-INVERSE-1, DISK_THM] [axioms: ] []
     |- |= implies (character_listp x)
             (equal (coerce (coerce x (csym "STRING")) (csym "LIST")) x),
*)

val list_EXPLODE_coerce =
 if_store_thm
  ("list_EXPLODE_coerce",
   ``!s. (|= character_listp s)
         ==>
         (list_to_sexp 
           chr
           (EXPLODE(coerce_list_to_string(make_character_list s))) = s)``,
   Induct
    THEN ACL2_SIMP_TAC
          [csym_def,COMMON_LISP_def,coerce_string_to_list_def,
           coerce_list_to_string_def,list_to_sexp_def,
           EVAL ``EXPLODE ""``,make_character_list_def]
    THEN FULL_SIMP_TAC std_ss [GSYM nil_def, GSYM ACL2_TRUE]
    THEN Cases_on `s`
    THEN ACL2_FULL_SIMP_TAC
          [make_character_list_def,coerce_list_to_string_def,
           stringTheory.EXPLODE_EQNS,list_to_sexp_def]);

val coerce_inverse_1_defaxiom =
 store_thm
  ("coerce_inverse_1_defaxiom",
   ``|= implies
          (character_listp x)
          (equal (coerce (coerce x (csym "STRING")) (csym "LIST")) x)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC
          [csym_def,COMMON_LISP_def,coerce_string_to_list_def,
           list_to_sexp_def,EVAL ``EXPLODE ""``]
    THENL
     [PROVE_TAC[sexp_11],
      Cases_on `characterp s = sym "COMMON-LISP" "NIL"`
       THEN ACL2_FULL_SIMP_TAC[make_character_list_def]
       THEN Cases_on `s`
       THEN ACL2_FULL_SIMP_TAC
             [make_character_list_def,coerce_list_to_string_def,
              stringTheory.EXPLODE_EQNS,list_to_sexp_def]
       THEN PROVE_TAC[T_NIL,sexp_11,ACL2_TRUE,list_EXPLODE_coerce,nil_def]]);

(*
     [oracles: DEFAXIOM ACL2::COERCE-INVERSE-2, DISK_THM] [axioms: ] []
     |- |= implies (stringp x)
             (equal (coerce (coerce x (csym "LIST")) (csym "STRING")) x),
*)

val true_listp_list_to_sexp = (* This is not used *)
 if_store_thm
  ("true_listp_list_to_sexp",
   ``!l. |= true_listp(list_to_sexp f l)``,
   Induct
    THEN ACL2_SIMP_TAC[list_to_sexp_def]
    THEN ONCE_REWRITE_TAC[true_listp_def]
    THEN ACL2_FULL_SIMP_TAC[ACL2_TRUE]);

val coerce_list_EXPLODE =
 if_store_thm
  ("coerce_list_EXPLODE",
   ``!s. coerce 
          (list_to_sexp chr (EXPLODE s))
          (sym "COMMON-LISP" "STRING") =
         str s``,
   Induct
    THEN ACL2_SIMP_TAC
          [csym_def,COMMON_LISP_def,coerce_string_to_list_def,
           coerce_list_to_string_def,list_to_sexp_def,
           EVAL ``EXPLODE ""``,stringTheory.EXPLODE_EQNS,
           make_character_list_def]
    THEN Cases_on `EXPLODE s`
    THEN ACL2_FULL_SIMP_TAC
          [make_character_list_def,coerce_list_to_string_def,
           stringTheory.EXPLODE_EQNS,list_to_sexp_def,
           stringTheory.EXPLODE_EQ_NIL,EVAL ``"STRING" = "LIST"``]);

val coerce_inverse_2_defaxiom =
 store_thm
  ("coerce_inverse_2_defaxiom",
   ``|= implies
         (stringp x)
         (equal (coerce (coerce x (csym "LIST")) (csym "STRING")) x)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC
          [csym_def,COMMON_LISP_def,coerce_string_to_list_def,
           list_to_sexp_def,EVAL ``EXPLODE ""``]
    THEN PROVE_TAC[coerce_list_EXPLODE,sexp_11,T_NIL]);

(*
     [oracles: DEFAXIOM ACL2::CHARACTER-LISTP-COERCE, DISK_THM] [axioms: ] []
     |- |= character_listp (coerce acl2_str (csym "LIST")),
*)

val character_listp_list_to_sexp = 
 if_store_thm
  ("character_listp_list_to_sexp",
   ``!l. |= character_listp(list_to_sexp chr l)``,
   Induct
    THEN ACL2_SIMP_TAC[list_to_sexp_def]
    THEN ACL2_FULL_SIMP_TAC[ACL2_TRUE,nil_def]);

val character_listp_coerce_defaxiom =
 store_thm
  ("character_listp_coerce_defaxiom",
   ``|= character_listp (coerce acl2_str (csym "LIST"))``,
   Cases_on `acl2_str`
    THEN ACL2_SIMP_TAC
          [csym_def,COMMON_LISP_def,coerce_string_to_list_def,
           coerce_list_to_string_def,list_to_sexp_def,
           EVAL ``EXPLODE ""``,stringTheory.EXPLODE_EQNS,
           make_character_list_def]
    THEN PROVE_TAC[character_listp_list_to_sexp,nil_def,ACL2_TRUE]);

(*
     [oracles: DEFTHM ACL2::LOWER-CASE-P-CHAR-DOWNCASE, DISK_THM] [axioms: ]
     []
     |- |= implies (andl [upper_case_p x; characterp x])
             (lower_case_p (char_downcase x))
*)

val assoc_nil =
 if_store_thm
  ("assoc_nil",
   ``assoc x nil = nil``,
   CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[assoc_def]))
    THEN ACL2_SIMP_TAC[itel_def]);

val assoc_cons =
 if_store_thm
  ("assoc_cons",
   ``assoc x (cons (cons x' y) l) = 
      if |= equal x x' then cons x' y else assoc x l``,
   CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[assoc_def]))
    THEN ACL2_SIMP_TAC[itel_def]);

val member_nil =
 if_store_thm
  ("member_nil",
   ``member x nil = nil``,
   CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[member_def]))
    THEN ACL2_SIMP_TAC[itel_def]);

val member_cons =
 if_store_thm
  ("member_cons",
   ``member x (cons x' y) = 
      if |= equal x x' then cons x' y else member x y``,
   CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[member_def]))
    THEN ACL2_SIMP_TAC[itel_def]);

val lower_case_p_char_downcase_defaxiom =
 store_thm
  ("lower_case_p_char_downcase_defaxiom",
   ``|= implies (andl [upper_case_p x; characterp x])
                (lower_case_p (char_downcase x))``,
   RW_TAC std_ss
    [implies,upper_case_p_def,List_def,member_nil,member_cons,
     ACL2_TRUE,andl_def,ite_def,equal_def,
     if_t_nil,if_eq_imp]
    THEN SIMP_TAC std_ss 
          [List_def,assoc_nil,assoc_cons,char_downcase_def,equal_def,EVAL ``t = nil``,
           ACL2_TRUE,if_t_nil,sexp_11]
    THEN CONV_TAC(DEPTH_CONV char_EQ_CONV)
    THEN SIMP_TAC std_ss []
    THEN CONV_TAC(DEPTH_CONV(pairLib.let_CONV))
    THEN SIMP_TAC std_ss 
          [itel_def,lower_case_p_def,andl_def,List_def,cdr_def,ite_def,
           member_nil,member_cons,equal_def,ACL2_TRUE,EVAL ``t = nil``,
           EVAL ``cons x y = nil``,sexp_11]
    THEN CONV_TAC(DEPTH_CONV char_EQ_CONV)
    THEN SIMP_TAC std_ss [EVAL ``cons x y = nil``,EVAL ``t = nil``]);

(*
     [oracles: DEFAXIOM ACL2::STRINGP-SYMBOL-PACKAGE-NAME] [axioms: ] []
     |- |= stringp (symbol_package_name x),
*)

val stringp_symbol_package_name_defaxiom =
 store_thm
  ("stringp_symbol_package_name_defaxiom",
   ``|= stringp (symbol_package_name x)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[]);

(*
     [oracles: DEFAXIOM ACL2::SYMBOLP-INTERN-IN-PACKAGE-OF-SYMBOL] [axioms: ]
     [] |- |= symbolp (intern_in_package_of_symbol x y),
*)

(*****************************************************************************)
(* val LOOKUP_NIL =                                                          *)
(*  |- LOOKUP "COMMON-LISP" ACL2_PACKAGE_ALIST "NIL" = "COMMON-LISP"         *)
(*****************************************************************************)
val LOOKUP_NIL = 
 if_save_thm
  ("LOOKUP_NIL",
   time EVAL ``LOOKUP "COMMON-LISP" ACL2_PACKAGE_ALIST "NIL"``);

val symbolp_intern_in_package_of_symbol_defaxiom =
 store_thm
  ("symbolp_intern_in_package_of_symbol_defaxiom",
   ``|= symbolp (intern_in_package_of_symbol x y)``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC[BASIC_INTERN_def,LOOKUP_NIL]
    THEN METIS_TAC
           [GSYM t_def,GSYM nil_def,if_t_nil,VALID_ACL2_PACKAGE_ALIST,
            LOOKUP_NOT_EMPTY_STRING,LOOKUP_IDEMPOTENT]);

(*
     [oracles: DEFAXIOM ACL2::SYMBOLP-PKG-WITNESS] [axioms: ] []
     |- |= symbolp (pkg_witness x),
*)

(*****************************************************************************)
(* |- LOOKUP s ACL2_PACKAGE_ALIST "ACL2-PKG-WITNESS" = s                     *)
(*****************************************************************************)
val LOOKUP_PKG_WITNESS =
 if_store_thm
  ("LOOKUP_PKG_WITNESS",
   ``LOOKUP s ACL2_PACKAGE_ALIST "ACL2-PKG-WITNESS" = s``,
   CONV_TAC EVAL);

val symbolp_nil =
 if_store_thm
  ("symbolp_nil",
   ``~(symbolp nil = nil)``,
   CONV_TAC EVAL);

val symbolp_pkg_witness_defaxiom =
 store_thm
  ("symbolp_pkg_witness_defaxiom",
   ``|= symbolp (pkg_witness x)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[]
    THEN FULL_SIMP_TAC std_ss [GSYM nil_def,markerTheory.Abbrev_def]
    THEN SIMP_TAC std_ss [BASIC_INTERN_def]
    THEN SIMP_TAC std_ss 
          [BASIC_INTERN_def,
           symbolp_def,sexp_11,if_t_nil,LOOKUP_PKG_WITNESS]
    THEN CONV_TAC EVAL
    THEN Cases_on  `s = ""`
    THEN RW_TAC std_ss [symbolp_nil,GSYM nil_def]
    THEN CONV_TAC EVAL
    THEN RW_TAC std_ss []);

(*
     [oracles: DEFAXIOM ACL2::INTERN-IN-PACKAGE-OF-SYMBOL-SYMBOL-NAME,
                DISK_THM]
     [axioms: ] []
     |- |= implies
             (andl
                [symbolp x;
                 equal (symbol_package_name x) (symbol_package_name y)])
             (equal (intern_in_package_of_symbol (symbol_name x) y) x),
*)

val intern_in_package_of_symbol_symbol_name_defaxiom =
 store_thm
  ("intern_in_package_of_symbol_symbol_name_defaxiom",
   ``|= implies
         (andl
           [symbolp x;
            equal (symbol_package_name x) (symbol_package_name y)])
         (equal (intern_in_package_of_symbol (symbol_name x) y) x)``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC []
    THEN FULL_SIMP_TAC arith_ss 
          [if_t_nil,GSYM t_def, GSYM nil_def,BASIC_INTERN_def]
    THEN `~(intern_in_package_of_symbol (str s0) (sym s' s0') = sym s s0)` by METIS_TAC[]
    THEN ACL2_FULL_SIMP_TAC[]
    THEN FULL_SIMP_TAC arith_ss 
          [if_t_nil,sexp_11,if_eq_imp,BASIC_INTERN_def,T_NIL]
    THEN RW_TAC std_ss []
    THEN TRY(`~(intern_in_package_of_symbol (str "") (sym s' so') = sym s s0)`
              by METIS_TAC[])
    THEN TRY(METIS_TAC[]));

(*
     [oracles: DEFAXIOM ACL2::SYMBOL-NAME-PKG-WITNESS] [axioms: ] []
     |- |= equal (symbol_name (pkg_witness pkg_name))
             (str "ACL2-PKG-WITNESS"),
*)

val symbol_name_pkg_witness_defaxiom =
 time store_thm
  ("symbol_name_pkg_witness_defaxiom",
   ``|= equal (symbol_name (pkg_witness pkg_name)) (str "ACL2-PKG-WITNESS")``,
   Cases_on `pkg_name`
    THEN ACL2_SIMP_TAC[BASIC_INTERN_def]
    THEN FULL_SIMP_TAC arith_ss 
          [if_t_nil,GSYM t_def, GSYM nil_def,BASIC_INTERN_def]
    THEN FULL_SIMP_TAC arith_ss 
          [if_eq_imp,sexp_11,LET_DEF,LOOKUP_PKG_WITNESS]
    THEN TRY
          (METIS_TAC
            [VALID_ACL2_PACKAGE_ALIST,LOOKUP_NOT_EMPTY_STRING,
             LOOKUP_PKG_WITNESS,LOOKUP_IDEMPOTENT,
             EVAL``"ACL2" = ""``])
    THEN FULL_SIMP_TAC arith_ss 
          [if_t_nil,GSYM t_def, GSYM nil_def,BASIC_INTERN_def]
    THEN FULL_SIMP_TAC arith_ss 
          [if_eq_imp,sexp_11,LET_DEF,LOOKUP_PKG_WITNESS]
    THEN Cases_on `s = ""`
    THEN FULL_SIMP_TAC std_ss
          [if_t_nil,GSYM t_def, GSYM nil_def,BASIC_INTERN_def]
    THEN RW_TAC std_ss []
    THEN ACL2_FULL_SIMP_TAC[]
    THEN FULL_SIMP_TAC arith_ss 
          [if_eq_imp,sexp_11,LET_DEF,LOOKUP_PKG_WITNESS,BASIC_INTERN_def,
           T_NIL,EVAL ``"" = "ACL2-PKG-WITNESS"``,EVAL``"ACL2" = ""``]
    THEN ACL2_FULL_SIMP_TAC[]
    THEN FULL_SIMP_TAC arith_ss 
          [if_eq_imp,sexp_11,LET_DEF,LOOKUP_PKG_WITNESS,BASIC_INTERN_def,
           T_NIL,EVAL ``"" = "ACL2-PKG-WITNESS"``,EVAL``"ACL2" = ""``]);

(*
     [oracles: DEFAXIOM ACL2::SYMBOL-PACKAGE-NAME-PKG-WITNESS-NAME, DISK_THM]
     [axioms: ] []
     |- |= equal (symbol_package_name (pkg_witness pkg_name))
             (ite (stringp pkg_name) pkg_name (str ACL2)),

Above turned out not to be true, so at Matt Kaufmann's suggestion the
axiom was revised to:

(defaxiom symbol-package-name-pkg-witness-name
  (equal (symbol-package-name (pkg-witness pkg-name))
         (if (and (stringp pkg-name)
                  (not (equal pkg-name "")) ;;; NEW!!
                  )
             pkg-name
           "ACL2")))

*)

val symbol_package_name_pkg_witness_name_defaxiom =
 store_thm
  ("symbol_package_name_pkg_witness_name_defaxiom",
   ``|= equal (symbol_package_name (pkg_witness pkg_name))
              (ite (andl[stringp pkg_name;not (equal pkg_name (str ""))])
                   pkg_name
                   (str ACL2))``,
   Cases_on `pkg_name`
    THEN ACL2_SIMP_TAC[BASIC_INTERN_def,ACL2_def]
    THEN FULL_SIMP_TAC arith_ss 
          [if_t_nil,GSYM t_def, GSYM nil_def,BASIC_INTERN_def]
    THEN FULL_SIMP_TAC arith_ss 
          [if_eq_imp,sexp_11,LET_DEF,LOOKUP_PKG_WITNESS]
    THEN TRY
          (METIS_TAC
            [VALID_ACL2_PACKAGE_ALIST,LOOKUP_NOT_EMPTY_STRING,
             LOOKUP_PKG_WITNESS,LOOKUP_IDEMPOTENT,
             EVAL``"ACL2" = ""``])
    THEN FULL_SIMP_TAC arith_ss 
          [if_t_nil,GSYM t_def, GSYM nil_def,BASIC_INTERN_def]
    THEN FULL_SIMP_TAC arith_ss 
          [if_eq_imp,sexp_11,LET_DEF,LOOKUP_PKG_WITNESS]
    THEN Cases_on `s = ""`
    THEN FULL_SIMP_TAC std_ss
          [if_t_nil,GSYM t_def, GSYM nil_def,BASIC_INTERN_def]
    THEN RW_TAC std_ss []
    THEN ACL2_FULL_SIMP_TAC[]
    THEN FULL_SIMP_TAC arith_ss 
          [if_eq_imp,sexp_11,LET_DEF,LOOKUP_PKG_WITNESS,BASIC_INTERN_def,
           T_NIL,EVAL ``"" = "ACL2-PKG-WITNESS"``,EVAL``"ACL2" = ""``]
    THEN ACL2_FULL_SIMP_TAC[]
    THEN FULL_SIMP_TAC arith_ss 
          [if_eq_imp,sexp_11,LET_DEF,LOOKUP_PKG_WITNESS,BASIC_INTERN_def,
           T_NIL,EVAL ``"" = "ACL2-PKG-WITNESS"``,EVAL``"ACL2" = ""``]);

(*
     [oracles: DEFAXIOM ACL2::SYMBOL-NAME-INTERN-IN-PACKAGE-OF-SYMBOL,
                DISK_THM]
     [axioms: ] []
     |- |= implies (andl [stringp s; symbolp any_symbol])
             (equal (symbol_name (intern_in_package_of_symbol s any_symbol))
                s),
*)

val symbol_name_intern_in_package_of_symbol_defaxiom =
 store_thm
  ("symbol_name_intern_in_package_of_symbol_defaxiom",
   ``|= implies 
          (andl [stringp s; symbolp any_symbol])
          (equal 
            (symbol_name (intern_in_package_of_symbol s any_symbol)) 
            s)``,
   Cases_on `s` THEN Cases_on `any_symbol`
    THEN ACL2_SIMP_TAC[]
    THEN FULL_SIMP_TAC arith_ss 
          [if_t_nil,GSYM t_def, GSYM nil_def,BASIC_INTERN_def]
    THEN ACL2_FULL_SIMP_TAC
          [if_eq_imp,sexp_11,LET_DEF,LOOKUP_PKG_WITNESS,BASIC_INTERN_def]
    THEN METIS_TAC
          [VALID_ACL2_PACKAGE_ALIST,LOOKUP_NOT_EMPTY_STRING,
           LOOKUP_PKG_WITNESS,LOOKUP_IDEMPOTENT]);

(*
     [oracles: DEFAXIOM ACL2::ACL2-INPUT-CHANNEL-PACKAGE, DISK_THM]
     [axioms: ] []
     |- |= implies
             (andl
                [stringp x; symbolp y;
                 equal (symbol_package_name y) (str "ACL2-INPUT-CHANNEL")])
             (equal (symbol_package_name (intern_in_package_of_symbol x y))
                (str "ACL2-INPUT-CHANNEL")),
*)

val LOOKUP_INPUT = 
 if_save_thm
  ("LOOKUP_INPUT",
   time EVAL ``LOOKUP "ACL2-INPUT-CHANNEL" ACL2_PACKAGE_ALIST s0``);

val acl2_input_channel_package_defaxiom =
 store_thm
  ("acl2_input_channel_package_defaxiom",
   ``|= implies
         (andl
           [stringp x; symbolp y;
            equal (symbol_package_name y) (str "ACL2-INPUT-CHANNEL")])
         (equal (symbol_package_name (intern_in_package_of_symbol x y))
                (str "ACL2-INPUT-CHANNEL"))``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC[]
    THEN FULL_SIMP_TAC arith_ss 
          [if_t_nil,GSYM t_def, GSYM nil_def,BASIC_INTERN_def]
    THEN ACL2_FULL_SIMP_TAC
          [if_eq_imp,sexp_11,LET_DEF,LOOKUP_PKG_WITNESS,BASIC_INTERN_def]
    THEN RW_TAC std_ss []
    THEN ACL2_FULL_SIMP_TAC
          [if_eq_imp,sexp_11,LET_DEF,LOOKUP_PKG_WITNESS,BASIC_INTERN_def,
           LOOKUP_INPUT]);

(*
     [oracles: DEFAXIOM ACL2::ACL2-OUTPUT-CHANNEL-PACKAGE, DISK_THM]
     [axioms: ] []
     |- |= implies
             (andl
                [stringp x; symbolp y;
                 equal (symbol_package_name y) (str ACL2_OUTPUT_CHANNEL)])
             (equal (symbol_package_name (intern_in_package_of_symbol x y))
                (str ACL2_OUTPUT_CHANNEL)),
*)

val LOOKUP_OUTPUT = 
 if_save_thm
  ("LOOKUP_OUTPUT",
   time EVAL ``LOOKUP "ACL2-OUTPUT-CHANNEL" ACL2_PACKAGE_ALIST s0``);

val acl2_output_channel_package_defaxiom =
 store_thm
  ("acl2_output_channel_package_defaxiom",
   ``|= implies
         (andl
           [stringp x; symbolp y;
            equal (symbol_package_name y) (str ACL2_OUTPUT_CHANNEL)])
         (equal (symbol_package_name (intern_in_package_of_symbol x y))
                (str ACL2_OUTPUT_CHANNEL))``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC[ACL2_OUTPUT_CHANNEL_def]
    THEN FULL_SIMP_TAC arith_ss 
          [if_t_nil,GSYM t_def, GSYM nil_def,BASIC_INTERN_def]
    THEN ACL2_FULL_SIMP_TAC
          [if_eq_imp,sexp_11,LET_DEF,LOOKUP_PKG_WITNESS,BASIC_INTERN_def]
    THEN RW_TAC std_ss []
    THEN ACL2_FULL_SIMP_TAC
          [if_eq_imp,sexp_11,LET_DEF,LOOKUP_PKG_WITNESS,BASIC_INTERN_def,
           LOOKUP_OUTPUT]);

(*
     [oracles: DEFAXIOM ACL2::ACL2-PACKAGE, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [stringp x;
                 not
                   (member_symbol_name x
                      (List
                         [csym "&ALLOW-OTHER-KEYS";
                          csym "*PRINT-MISER-WIDTH*"; csym "&AUX";
                          csym "*PRINT-PPRINT-DISPATCH*"; csym "&BODY";
                          csym "*PRINT-PRETTY*"; csym "&ENVIRONMENT";
                          csym "*PRINT-RADIX*"; csym "&KEY";
                          csym "*PRINT-READABLY*"; csym "&OPTIONAL";
                          csym "*PRINT-RIGHT-MARGIN*"; csym "&REST";
                          csym "*QUERY-IO*"; csym "&WHOLE";
                          csym "*RANDOM-STATE*"; csym "*";
                          csym "*READ-BASE*"; csym "**";
                          csym "*READ-DEFAULT-FLOAT-FORMAT*"; csym "***";
                          csym "*READ-EVAL*"; csym "*BREAK-ON-SIGNALS*";
                          csym "*READ-SUPPRESS*";
                          csym "*COMPILE-FILE-PATHNAME*"; csym "*READTABLE*";
                          csym "*COMPILE-FILE-TRUENAME*";
                          csym "*STANDARD-INPUT*"; csym "*COMPILE-PRINT*";
                          csym "*STANDARD-OUTPUT*"; csym "*COMPILE-VERBOSE*";
                          csym "*TERMINAL-IO*"; csym "*DEBUG-IO*";
                          csym "*TRACE-OUTPUT*"; csym "*DEBUGGER-HOOK*";
                          csym "+"; csym "*DEFAULT-PATHNAME-DEFAULTS*";
                          csym "++"; 5~csym "*ERROR-OUTPUT*"; csym "+++";
                          csym "*FEATURES*"; csym "-";
                          csym "*GENSYM-COUNTER*"; csym "/";
                          csym "*LOAD-PATHNAME*"; csym "//";
                          csym "*LOAD-PRINT*"; csym "///";
                          csym "*LOAD-TRUENAME*"; csym "/=";
                          csym "*LOAD-VERBOSE*"; csym "1+";
                          csym "*MACROEXPAND-HOOK*"; csym "1-";
                          csym "*MODULES*"; csym "<"; csym "*PACKAGE*";
                          csym "<="; csym "*PRINT-ARRAY*"; csym "=";
                          csym "*PRINT-BASE*"; csym ">"; csym "*PRINT-CASE*";
                          csym ">="; csym "*PRINT-CIRCLE*"; csym "ABORT";
                          csym "*PRINT-ESCAPE*"; csym "ABS";
                          csym "*PRINT-GENSYM*"; csym "ACONS";
                          csym "*PRINT-LENGTH*"; csym "ACOS";
                          csym "*PRINT-LEVEL*"; csym "ACOSH";
                          csym "*PRINT-LINES*"; csym "ADD-METHOD";
                          csym "ADJOIN"; csym "ATOM"; csym "BOUNDP";
                          csym "ADJUST-ARRAY"; csym "BASE-CHAR";
                          csym "BREAK"; csym "ADJUSTABLE-ARRAY-P";
                          csym "BASE-STRING"; csym "BROADCAST-STREAM";
                          csym "ALLOCATE-INSTANCE"; csym "BIGNUM";
                          csym "BROADCAST-STREAM-STREAMS";
                          csym "ALPHA-CHAR-P"; csym "BIT";
                          csym "BUILT-IN-CLASS"; csym "ALPHANUMERICP";
                          csym "BIT-AND"; csym "BUTLAST"; csym "AND";
                          csym "BIT-ANDC1"; csym "BYTE"; csym "APPEND";
                          csym "BIT-ANDC2"; csym "BYTE-POSITION";
                          csym "APPLY"; csym "BIT-EQV"; csym "BYTE-SIZE";
                          csym "APROPOS"; csym "BIT-IOR"; csym "CAAAAR";
                          csym "APROPOS-LIST"; csym "BIT-NAND";
                          csym "CAAADR"; csym "AREF"; csym "BIT-NOR";
                          csym "CAAAR"; csym "ARITHMETIC-ERROR";
                          csym "BIT-NOT"; csym "CAADAR";
                          csym "ARITHMETIC-ERROR-OPERANDS"; csym "BIT-ORC1";
                          csym "CAADDR"; csym "ARITHMETIC-ERROR-OPERATION";
                          csym "BIT-ORC2"; csym "CAADR"; csym "ARRAY";
                          csym "BIT-VECTOR"; csym "CAAR";
                          csym "ARRAY-DIMENSION"; csym "BIT-VECTOR-P";
                          csym "CADAAR"; csym "ARRAY-DIMENSION-LIMIT";
                          csym "BIT-XOR"; csym "CADADR";
                          csym "ARRAY-DIMENSIONS"; csym "BLOCK";
                          csym "CADAR"; csym "ARRAY-DISPLACEMENT";
                          csym "BOOLE"; csym "CADDAR";
                          csym "ARRAY-ELEMENT-TYPE"; csym "BOOLE-1";
                          csym "CADDDR"; csym "ARRAY-HAS-FILL-POINTER-P";
                          csym "BOOLE-2"; csym "CADDR";
                          csym "ARRAY-IN-BOUNDS-P"; csym "BOOLE-AND";
                          csym "CADR"; csym "ARRAY-RANK"; csym "BOOLE-ANDC1";
                          csym "CALL-ARGUMENTS-LIMIT";
                          csym "ARRAY-RANK-LIMIT"; csym "BOOLE-ANDC2";
                          csym "CALL-METHOD"; csym "ARRAY-ROW-MAJOR-INDEX";
                          csym "BOOLE-C1"; csym "CALL-NEXT-METHOD";
                          csym "ARRAY-TOTAL-SIZE"; csym "BOOLE-C2";
                          csym "CAR"; csym "ARRAY-TOTAL-SIZE-LIMIT";
                          csym "BOOLE-CLR"; csym "CASE"; csym "ARRAYP";
                          csym "BOOLE-EQV"; csym "CATCH"; csym "ASH";
                          csym "BOOLE-IOR"; csym "CCASE"; csym "ASIN";
                          csym "BOOLE-NAND"; csym "CDAAAR"; csym "ASINH";
                          csym "BOOLE-NOR"; csym "CDAADR"; csym "ASSERT";
                          csym "BOOLE-ORC1"; csym "CDAAR"; csym "ASSOC";
                          csym "BOOLE-ORC2"; csym "CDADAR"; csym "ASSOC-IF";
                          csym "BOOLE-SET"; csym "CDADDR";
                          csym "ASSOC-IF-NOT"; csym "BOOLE-XOR";
                          csym "CDADR"; csym "ATAN"; csym "BOOLEAN";
                          csym "CDAR"; csym "ATANH"; csym "BOTH-CASE-P";
                          csym "CDDAAR"; csym "CDDADR"; csym "CLEAR-INPUT";
                          csym "COPY-TREE"; csym "CDDAR";
                          csym "CLEAR-OUTPUT"; csym "COS"; csym "CDDDAR";
                          csym "CLOSE"; csym "COSH"; csym "CDDDDR";
                          csym "CLRHASH"; csym "COUNT"; csym "CDDDR";
                          csym "CODE-CHAR"; csym "COUNT-IF"; csym "CDDR";
                          csym "COERCE"; csym "COUNT-IF-NOT"; csym "CDR";
                          csym "COMPILATION-SPEED"; csym "CTYPECASE";
                          csym "CEILING"; csym "COMPILE"; csym "DEBUG";
                          csym "CELL-ERROR"; csym "COMPILE-FILE";
                          csym "DECF"; csym "CELL-ERROR-NAME";
                          csym "COMPILE-FILE-PATHNAME"; csym "DECLAIM";
                          csym "CERROR"; csym "COMPILED-FUNCTION";
                          csym "DECLARATION"; csym "CHANGE-CLASS";
                          csym "COMPILED-FUNCTION-P"; csym "DECLARE";
                          csym "CHAR"; csym "COMPILER-MACRO";
                          csym "DECODE-FLOAT"; csym "CHAR-CODE";
                          csym "COMPILER-MACRO-FUNCTION";
                          csym "DECODE-UNIVERSAL-TIME";
                          csym "CHAR-CODE-LIMIT"; csym "COMPLEMENT";
                          csym "DEFCLASS"; csym "CHAR-DOWNCASE";
                          csym "COMPLEX"; csym "DEFCONSTANT";
                          csym "CHAR-EQUAL"; csym "COMPLEXP";
                          csym "DEFGENERIC"; csym "CHAR-GREATERP";
                          csym "COMPUTE-APPLICABLE-METHODS";
                          csym "DEFINE-COMPILER-MACRO"; csym "CHAR-INT";
                          csym "COMPUTE-RESTARTS"; csym "DEFINE-CONDITION";
                          csym "CHAR-LESSP"; csym "CONCATENATE";
                          csym "DEFINE-METHOD-COMBINATION"; csym "CHAR-NAME";
                          csym "CONCATENATED-STREAM";
                          csym "DEFINE-MODIFY-MACRO"; csym "CHAR-NOT-EQUAL";
                          csym "CONCATENATED-STREAM-STREAMS";
                          csym "DEFINE-SETF-EXPANDER";
                          csym "CHAR-NOT-GREATERP"; csym "COND";
                          csym "DEFINE-SYMBOL-MACRO"; csym "CHAR-NOT-LESSP";
                          csym "CONDITION"; csym "DEFMACRO";
                          csym "CHAR-UPCASE"; csym "CONJUGATE";
                          csym "DEFMETHOD"; csym "CHAR/="; csym "CONS";
                          csym "DEFPACKAGE"; csym "CHAR<"; csym "CONSP";
                          csym "DEFPARAMETER"; csym "CHAR<=";
                          csym "CONSTANTLY"; csym "DEFSETF"; csym "CHAR=";
                          csym "CONSTANTP"; csym "DEFSTRUCT"; csym "CHAR>";
                          csym "CONTINUE"; csym "DEFTYPE"; csym "CHAR>=";
                          csym "CONTROL-ERROR"; csym "DEFUN";
                          csym "CHARACTER"; csym "COPY-ALIST"; csym "DEFVAR";
                          csym "CHARACTERP"; csym "COPY-LIST"; csym "DELETE";
                          csym "CHECK-TYPE"; csym "COPY-PPRINT-DISPATCH";
                          csym "DELETE-DUPLICATES"; csym "CIS";
                          csym "COPY-READTABLE"; csym "DELETE-FILE";
                          csym "CLASS"; csym "COPY-SEQ"; csym "DELETE-IF";
                          csym "CLASS-NAME"; csym "COPY-STRUCTURE";
                          csym "DELETE-IF-NOT"; csym "CLASS-OF";
                          csym "COPY-SYMBOL"; csym "DELETE-PACKAGE";
                          csym "DENOMINATOR"; csym "EQ";
                          csym "DEPOSIT-FIELD"; csym "EQL"; csym "DESCRIBE";
                          csym "EQUAL"; csym "DESCRIBE-OBJECT";
                          csym "EQUALP"; csym "DESTRUCTURING-BIND";
                          csym "ERROR"; csym "DIGIT-CHAR"; csym "ETYPECASE";
                          csym "DIGIT-CHAR-P"; csym "EVAL"; csym "DIRECTORY";
                          csym "EVAL-WHEN"; csym "DIRECTORY-NAMESTRING";
                          csym "EVENP"; csym "DISASSEMBLE"; csym "EVERY";
                          csym "DIVISION-BY-ZERO"; csym "EXP"; csym "DO";
                          csym "EXPORT"; csym "DO*"; csym "EXPT";
                          csym "DO-ALL-SYMBOLS"; csym "EXTENDED-CHAR";
                          csym "DO-EXTERNAL-SYMBOLS"; csym "FBOUNDP";
                          csym "DO-SYMBOLS"; csym "FCEILING";
                          csym "DOCUMENTATION"; csym "FDEFINITION";
                          csym "DOLIST"; csym "FFLOOR"; csym "DOTIMES";
                          csym "FIFTH"; csym "DOUBLE-FLOAT";
                          csym "FILE-AUTHOR"; csym "DOUBLE-FLOAT-EPSILON";
                          csym "FILE-ERROR";
                          csym "DOUBLE-FLOAT-NEGATIVE-EPSILON";
                          csym "FILE-ERROR-PATHNAME"; csym "DPB";
                          csym "FILE-LENGTH"; csym "DRIBBLE";
                          csym "FILE-NAMESTRING"; csym "DYNAMIC-EXTENT";
                          csym "FILE-POSITION"; csym "ECASE";
                          csym "FILE-STREAM"; csym "ECHO-STREAM";
                          csym "FILE-STRING-LENGTH";
                          csym "ECHO-STREAM-INPUT-STREAM";
                          csym "FILE-WRITE-DATE";
                          csym "ECHO-STREAM-OUTPUT-STREAM"; csym "FILL";
                          csym "ED"; csym "FILL-POINTER"; csym "EIGHTH";
                          csym "FIND"; csym "ELT"; csym "FIND-ALL-SYMBOLS";
                          csym "ENCODE-UNIVERSAL-TIME"; csym "FIND-CLASS";
                          csym "END-OF-FILE"; csym "FIND-IF"; csym "ENDP";
                          csym "FIND-IF-NOT"; csym "ENOUGH-NAMESTRING";
                          csym "FIND-METHOD";
                          csym "ENSURE-DIRECTORIES-EXIST";
                          csym "FIND-PACKAGE";
                          csym "ENSURE-GENERIC-FUNCTION";
                          csym "FIND-RESTART"; csym "FIND-SYMBOL";
                          csym "GET-INTERNAL-RUN-TIME"; csym "FINISH-OUTPUT";
                          csym "GET-MACRO-CHARACTER"; csym "FIRST";
                          csym "GET-OUTPUT-STREAM-STRING"; csym "FIXNUM";
                          csym "GET-PROPERTIES"; csym "FLET";
                          csym "GET-SETF-EXPANSION"; csym "FLOAT";
                          csym "GET-UNIVERSAL-TIME"; csym "FLOAT-DIGITS";
                          csym "GETF"; csym "FLOAT-PRECISION";
                          csym "GETHASH"; csym "FLOAT-RADIX"; csym "GO";
                          csym "FLOAT-SIGN"; csym "GRAPHIC-CHAR-P";
                          csym "FLOATING-POINT-INEXACT"; csym "HANDLER-BIND";
                          csym "FLOATING-POINT-INVALID-OPERATION";
                          csym "HANDLER-CASE";
                          csym "FLOATING-POINT-OVERFLOW"; csym "HASH-TABLE";
                          csym "FLOATING-POINT-UNDERFLOW";
                          csym "HASH-TABLE-COUNT"; csym "FLOATP";
                          csym "HASH-TABLE-P"; csym "FLOOR";
                          csym "HASH-TABLE-REHASH-SIZE"; csym "FMAKUNBOUND";
                          csym "HASH-TABLE-REHASH-THRESHOLD";
                          csym "FORCE-OUTPUT"; csym "HASH-TABLE-SIZE";
                          csym "FORMAT"; csym "HASH-TABLE-TEST";
                          csym "FORMATTER"; csym "HOST-NAMESTRING";
                          csym "FOURTH"; csym "IDENTITY"; csym "FRESH-LINE";
                          csym "IF"; csym "FROUND"; csym "IGNORABLE";
                          csym "FTRUNCATE"; csym "IGNORE"; csym "FTYPE";
                          csym "IGNORE-ERRORS"; csym "FUNCALL";
                          csym "IMAGPART"; csym "FUNCTION"; csym "IMPORT";
                          csym "FUNCTION-KEYWORDS"; csym "IN-PACKAGE";
                          csym "FUNCTION-LAMBDA-EXPRESSION"; csym "INCF";
                          csym "FUNCTIONP"; csym "INITIALIZE-INSTANCE";
                          csym "GCD"; csym "INLINE"; csym "GENERIC-FUNCTION";
                          csym "INPUT-STREAM-P"; csym "GENSYM";
                          csym "INSPECT"; csym "GENTEMP"; csym "INTEGER";
                          csym "GET"; csym "INTEGER-DECODE-FLOAT";
                          csym "GET-DECODED-TIME"; csym "INTEGER-LENGTH";
                          csym "GET-DISPATCH-MACRO-CHARACTER";
                          csym "INTEGERP"; csym "GET-INTERNAL-REAL-TIME";
                          csym "INTERACTIVE-STREAM-P"; csym "INTERN";
                          csym "LISP-IMPLEMENTATION-TYPE";
                          csym "INTERNAL-TIME-UNITS-PER-SECOND";
                          csym "LISP-IMPLEMENTATION-VERSION";
                          csym "INTERSECTION"; csym "LIST";
                          csym "INVALID-METHOD-ERROR"; csym "LIST*";
                          csym "INVOKE-DEBUGGER"; csym "LIST-ALL-PACKAGES";
                          csym "INVOKE-RESTART"; csym "LIST-LENGTH";
                          csym "INVOKE-RESTART-INTERACTIVELY"; csym "LISTEN";
                          csym "ISQRT"; csym "LISTP"; csym KEYWORD;
                          csym "LOAD"; csym "KEYWORDP";
                          csym "LOAD-LOGICAL-PATHNAME-TRANSLATIONS";
                          csym "LABELS"; csym "LOAD-TIME-VALUE";
                          csym "LAMBDA"; csym "LOCALLY";
                          csym "LAMBDA-LIST-KEYWORDS"; csym "LOG";
                          csym "LAMBDA-PARAMETERS-LIMIT"; csym "LOGAND";
                          csym "LAST"; csym "LOGANDC1"; csym "LCM";
                          csym "LOGANDC2"; csym "LDB"; csym "LOGBITP";
                          csym "LDB-TEST"; csym "LOGCOUNT"; csym "LDIFF";
                          csym "LOGEQV"; csym "LEAST-NEGATIVE-DOUBLE-FLOAT";
                          csym "LOGICAL-PATHNAME";
                          csym "LEAST-NEGATIVE-LONG-FLOAT";
                          csym "LOGICAL-PATHNAME-TRANSLATIONS";
                          csym "LEAST-NEGATIVE-NORMALIZED-DOUBLE-FLOAT";
                          csym "LOGIOR";
                          csym "LEAST-NEGATIVE-NORMALIZED-LONG-FLOAT";
                          csym "LOGNAND";
                          csym "LEAST-NEGATIVE-NORMALIZED-SHORT-FLOAT";
                          csym "LOGNOR";
                          csym "LEAST-NEGATIVE-NORMALIZED-SINGLE-FLOAT";
                          csym "LOGNOT"; csym "LEAST-NEGATIVE-SHORT-FLOAT";
                          csym "LOGORC1"; csym "LEAST-NEGATIVE-SINGLE-FLOAT";
                          csym "LOGORC2"; csym "LEAST-POSITIVE-DOUBLE-FLOAT";
                          csym "LOGTEST"; csym "LEAST-POSITIVE-LONG-FLOAT";
                          csym "LOGXOR";
                          csym "LEAST-POSITIVE-NORMALIZED-DOUBLE-FLOAT";
                          csym "LONG-FLOAT";
                          csym "LEAST-POSITIVE-NORMALIZED-LONG-FLOAT";
                          csym "LONG-FLOAT-EPSILON";
                          csym "LEAST-POSITIVE-NORMALIZED-SHORT-FLOAT";
                          csym "LONG-FLOAT-NEGATIVE-EPSILON";
                          csym "LEAST-POSITIVE-NORMALIZED-SINGLE-FLOAT";
                          csym "LONG-SITE-NAME";
                          csym "LEAST-POSITIVE-SHORT-FLOAT"; csym "LOOP";
                          csym "LEAST-POSITIVE-SINGLE-FLOAT";
                          csym "LOOP-FINISH"; csym "LENGTH";
                          csym "LOWER-CASE-P"; csym "LET";
                          csym "MACHINE-INSTANCE"; csym "LET*";
                          csym "MACHINE-TYPE"; csym "MACHINE-VERSION";
                          csym "MASK-FIELD"; csym "MACRO-FUNCTION";
                          csym "MAX"; csym "MACROEXPAND"; csym "MEMBER";
                          csym "MACROEXPAND-1"; csym "MEMBER-IF";
                          csym "MACROLET"; csym "MEMBER-IF-NOT";
                          csym "MAKE-ARRAY"; csym "MERGE";
                          csym "MAKE-BROADCAST-STREAM";
                          csym "MERGE-PATHNAMES";
                          csym "MAKE-CONCATENATED-STREAM"; csym "METHOD";
                          csym "MAKE-CONDITION"; csym "METHOD-COMBINATION";
                          csym "MAKE-DISPATCH-MACRO-CHARACTER";
                          csym "METHOD-COMBINATION-ERROR";
                          csym "MAKE-ECHO-STREAM"; csym "METHOD-QUALIFIERS";
                          csym "MAKE-HASH-TABLE"; csym "MIN";
                          csym "MAKE-INSTANCE"; csym "MINUSP";
                          csym "MAKE-INSTANCES-OBSOLETE"; csym "MISMATCH";
                          csym "MAKE-LIST"; csym "MOD";
                          csym "MAKE-LOAD-FORM";
                          csym "MOST-NEGATIVE-DOUBLE-FLOAT";
                          csym "MAKE-LOAD-FORM-SAVING-SLOTS";
                          csym "MOST-NEGATIVE-FIXNUM"; csym "MAKE-METHOD";
                          csym "MOST-NEGATIVE-LONG-FLOAT";
                          csym "MAKE-PACKAGE";
                          csym "MOST-NEGATIVE-SHORT-FLOAT";
                          csym "MAKE-PATHNAME";
                          csym "MOST-NEGATIVE-SINGLE-FLOAT";
                          csym "MAKE-RANDOM-STATE";
                          csym "MOST-POSITIVE-DOUBLE-FLOAT";
                          csym "MAKE-SEQUENCE"; csym "MOST-POSITIVE-FIXNUM";
                          csym "MAKE-STRING";
                          csym "MOST-POSITIVE-LONG-FLOAT";
                          csym "MAKE-STRING-INPUT-STREAM";
                          csym "MOST-POSITIVE-SHORT-FLOAT";
                          csym "MAKE-STRING-OUTPUT-STREAM";
                          csym "MOST-POSITIVE-SINGLE-FLOAT";
                          csym "MAKE-SYMBOL"; csym "MUFFLE-WARNING";
                          csym "MAKE-SYNONYM-STREAM";
                          csym "MULTIPLE-VALUE-BIND";
                          csym "MAKE-TWO-WAY-STREAM";
                          csym "MULTIPLE-VALUE-CALL"; csym "MAKUNBOUND";
                          csym "MULTIPLE-VALUE-LIST"; csym "MAP";
                          csym "MULTIPLE-VALUE-PROG1"; csym "MAP-INTO";
                          csym "MULTIPLE-VALUE-SETQ"; csym "MAPC";
                          csym "MULTIPLE-VALUES-LIMIT"; csym "MAPCAN";
                          csym "NAME-CHAR"; csym "MAPCAR"; csym "NAMESTRING";
                          csym "MAPCON"; csym "NBUTLAST"; csym "MAPHASH";
                          csym "NCONC"; csym "MAPL"; csym "NEXT-METHOD-P";
                          csym "MAPLIST"; nil; csym "NINTERSECTION";
                          csym "PACKAGE-ERROR"; csym "NINTH";
                          csym "PACKAGE-ERROR-PACKAGE";
                          csym "NO-APPLICABLE-METHOD"; csym "PACKAGE-NAME";
                          csym "NO-NEXT-METHOD"; csym "PACKAGE-NICKNAMES";
                          csym "NOT"; csym "PACKAGE-SHADOWING-SYMBOLS";
                          csym "NOTANY"; csym "PACKAGE-USE-LIST";
                          csym "NOTEVERY"; csym "PACKAGE-USED-BY-LIST";
                          csym "NOTINLINE"; csym "PACKAGEP"; csym "NRECONC";
                          csym "PAIRLIS"; csym "NREVERSE";
                          csym "PARSE-ERROR"; csym "NSET-DIFFERENCE";
                          csym "PARSE-INTEGER"; csym "NSET-EXCLUSIVE-OR";
                          csym "PARSE-NAMESTRING"; csym "NSTRING-CAPITALIZE";
                          csym "PATHNAME"; csym "NSTRING-DOWNCASE";
                          csym "PATHNAME-DEVICE"; csym "NSTRING-UPCASE";
                          csym "PATHNAME-DIRECTORY"; csym "NSUBLIS";
                          csym "PATHNAME-HOST"; csym "NSUBST";
                          csym "PATHNAME-MATCH-P"; csym "NSUBST-IF";
                          csym "PATHNAME-NAME"; csym "NSUBST-IF-NOT";
                          csym "PATHNAME-TYPE"; csym "NSUBSTITUTE";
                          csym "PATHNAME-VERSION"; csym "NSUBSTITUTE-IF";
                          csym "PATHNAMEP"; csym "NSUBSTITUTE-IF-NOT";
                          csym "PEEK-CHAR"; csym "NTH"; csym "PHASE";
                          csym "NTH-VALUE"; csym "PI"; csym "NTHCDR";
                          csym "PLUSP"; csym "NULL"; csym "POP";
                          csym "NUMBER"; csym "POSITION"; csym "NUMBERP";
                          csym "POSITION-IF"; csym "NUMERATOR";
                          csym "POSITION-IF-NOT"; csym "NUNION";
                          csym "PPRINT"; csym "ODDP"; csym "PPRINT-DISPATCH";
                          csym "OPEN"; csym "PPRINT-EXIT-IF-LIST-EXHAUSTED";
                          csym "OPEN-STREAM-P"; csym "PPRINT-FILL";
                          csym "OPTIMIZE"; csym "PPRINT-INDENT"; csym "OR";
                          csym "PPRINT-LINEAR"; csym "OTHERWISE";
                          csym "PPRINT-LOGICAL-BLOCK";
                          csym "OUTPUT-STREAM-P"; csym "PPRINT-NEWLINE";
                          csym "PACKAGE"; csym "PPRINT-POP";
                          csym "PPRINT-TAB"; csym "READ-CHAR";
                          csym "PPRINT-TABULAR"; csym "READ-CHAR-NO-HANG";
                          csym "PRIN1"; csym "READ-DELIMITED-LIST";
                          csym "PRIN1-TO-STRING"; csym "READ-FROM-STRING";
                          csym "PRINC"; csym "READ-LINE";
                          csym "PRINC-TO-STRING";
                          csym "READ-PRESERVING-WHITESPACE"; csym "PRINT";
                          csym "READ-SEQUENCE"; csym "PRINT-NOT-READABLE";
                          csym "READER-ERROR";
                          csym "PRINT-NOT-READABLE-OBJECT"; csym "READTABLE";
                          csym "PRINT-OBJECT"; csym "READTABLE-CASE";
                          csym "PRINT-UNREADABLE-OBJECT"; csym "READTABLEP";
                          csym "PROBE-FILE"; csym "REAL"; csym "PROCLAIM";
                          csym "REALP"; csym "PROG"; csym "REALPART";
                          csym "PROG*"; csym "REDUCE"; csym "PROG1";
                          csym "REINITIALIZE-INSTANCE"; csym "PROG2";
                          csym "REM"; csym "PROGN"; csym "REMF";
                          csym "PROGRAM-ERROR"; csym "REMHASH"; csym "PROGV";
                          csym "REMOVE"; csym "PROVIDE";
                          csym "REMOVE-DUPLICATES"; csym "PSETF";
                          csym "REMOVE-IF"; csym "PSETQ";
                          csym "REMOVE-IF-NOT"; csym "PUSH";
                          csym "REMOVE-METHOD"; csym "PUSHNEW";
                          csym "REMPROP"; csym "QUOTE"; csym "RENAME-FILE";
                          csym "RANDOM"; csym "RENAME-PACKAGE";
                          csym "RANDOM-STATE"; csym "REPLACE";
                          csym "RANDOM-STATE-P"; csym "REQUIRE";
                          csym "RASSOC"; csym "REST"; csym "RASSOC-IF";
                          csym "RESTART"; csym "RASSOC-IF-NOT";
                          csym "RESTART-BIND"; csym "RATIO";
                          csym "RESTART-CASE"; csym "RATIONAL";
                          csym "RESTART-NAME"; csym "RATIONALIZE";
                          csym "RETURN"; csym "RATIONALP";
                          csym "RETURN-FROM"; csym "READ"; csym "REVAPPEND";
                          csym "READ-BYTE"; csym "REVERSE"; csym "ROOM";
                          csym "SIMPLE-BIT-VECTOR"; csym "ROTATEF";
                          csym "SIMPLE-BIT-VECTOR-P"; csym "ROUND";
                          csym "SIMPLE-CONDITION"; csym "ROW-MAJOR-AREF";
                          csym "SIMPLE-CONDITION-FORMAT-ARGUMENTS";
                          csym "RPLACA";
                          csym "SIMPLE-CONDITION-FORMAT-CONTROL";
                          csym "RPLACD"; csym "SIMPLE-ERROR"; csym "SAFETY";
                          csym "SIMPLE-STRING"; csym "SATISFIES";
                          csym "SIMPLE-STRING-P"; csym "SBIT";
                          csym "SIMPLE-TYPE-ERROR"; csym "SCALE-FLOAT";
                          csym "SIMPLE-VECTOR"; csym "SCHAR";
                          csym "SIMPLE-VECTOR-P"; csym "SEARCH";
                          csym "SIMPLE-WARNING"; csym "SECOND"; csym "SIN";
                          csym "SEQUENCE"; csym "SINGLE-FLOAT";
                          csym "SERIOUS-CONDITION";
                          csym "SINGLE-FLOAT-EPSILON"; csym "SET";
                          csym "SINGLE-FLOAT-NEGATIVE-EPSILON";
                          csym "SET-DIFFERENCE"; csym "SINH";
                          csym "SET-DISPATCH-MACRO-CHARACTER"; csym "SIXTH";
                          csym "SET-EXCLUSIVE-OR"; csym "SLEEP";
                          csym "SET-MACRO-CHARACTER"; csym "SLOT-BOUNDP";
                          csym "SET-PPRINT-DISPATCH"; csym "SLOT-EXISTS-P";
                          csym "SET-SYNTAX-FROM-CHAR";
                          csym "SLOT-MAKUNBOUND"; csym "SETF";
                          csym "SLOT-MISSING"; csym "SETQ";
                          csym "SLOT-UNBOUND"; csym "SEVENTH";
                          csym "SLOT-VALUE"; csym "SHADOW";
                          csym "SOFTWARE-TYPE"; csym "SHADOWING-IMPORT";
                          csym "SOFTWARE-VERSION"; csym "SHARED-INITIALIZE";
                          csym "SOME"; csym "SHIFTF"; csym "SORT";
                          csym "SHORT-FLOAT"; csym "SPACE";
                          csym "SHORT-FLOAT-EPSILON"; csym "SPECIAL";
                          csym "SHORT-FLOAT-NEGATIVE-EPSILON";
                          csym "SPECIAL-OPERATOR-P"; csym "SHORT-SITE-NAME";
                          csym "SPEED"; csym "SIGNAL"; csym "SQRT";
                          csym "SIGNED-BYTE"; csym "STABLE-SORT";
                          csym "SIGNUM"; csym "STANDARD";
                          csym "SIMPLE-ARRAY"; csym "STANDARD-CHAR";
                          csym "SIMPLE-BASE-STRING"; csym "STANDARD-CHAR-P";
                          csym "STANDARD-CLASS"; csym "SUBLIS";
                          csym "STANDARD-GENERIC-FUNCTION"; csym "SUBSEQ";
                          csym "STANDARD-METHOD"; csym "SUBSETP";
                          csym "STANDARD-OBJECT"; csym "SUBST"; csym "STEP";
                          csym "SUBST-IF"; csym "STORAGE-CONDITION";
                          csym "SUBST-IF-NOT"; csym "STORE-VALUE";
                          csym "SUBSTITUTE"; csym "STREAM";
                          csym "SUBSTITUTE-IF"; csym "STREAM-ELEMENT-TYPE";
                          csym "SUBSTITUTE-IF-NOT"; csym "STREAM-ERROR";
                          csym "SUBTYPEP"; csym "STREAM-ERROR-STREAM";
                          csym "SVREF"; csym "STREAM-EXTERNAL-FORMAT";
                          csym "SXHASH"; csym "STREAMP"; csym "SYMBOL";
                          csym "STRING"; csym "SYMBOL-FUNCTION";
                          csym "STRING-CAPITALIZE"; csym "SYMBOL-MACROLET";
                          csym "STRING-DOWNCASE"; csym "SYMBOL-NAME";
                          csym "STRING-EQUAL"; csym "SYMBOL-PACKAGE";
                          csym "STRING-GREATERP"; csym "SYMBOL-PLIST";
                          csym "STRING-LEFT-TRIM"; csym "SYMBOL-VALUE";
                          csym "STRING-LESSP"; csym "SYMBOLP";
                          csym "STRING-NOT-EQUAL"; csym "SYNONYM-STREAM";
                          csym "STRING-NOT-GREATERP";
                          csym "SYNONYM-STREAM-SYMBOL";
                          csym "STRING-NOT-LESSP"; t;
                          csym "STRING-RIGHT-TRIM"; csym "TAGBODY";
                          csym "STRING-STREAM"; csym "TAILP";
                          csym "STRING-TRIM"; csym "TAN";
                          csym "STRING-UPCASE"; csym "TANH"; csym "STRING/=";
                          csym "TENTH"; csym "STRING<"; csym "TERPRI";
                          csym "STRING<="; csym "THE"; csym "STRING=";
                          csym "THIRD"; csym "STRING>"; csym "THROW";
                          csym "STRING>="; csym "TIME"; csym "STRINGP";
                          csym "TRACE"; csym "STRUCTURE";
                          csym "TRANSLATE-LOGICAL-PATHNAME";
                          csym "STRUCTURE-CLASS"; csym "TRANSLATE-PATHNAME";
                          csym "STRUCTURE-OBJECT"; csym "TREE-EQUAL";
                          csym "STYLE-WARNING"; csym "TRUENAME";
                          csym "TRUNCATE"; csym "VALUES-LIST";
                          csym "TWO-WAY-STREAM"; csym "VARIABLE";
                          csym "TWO-WAY-STREAM-INPUT-STREAM"; csym "VECTOR";
                          csym "TWO-WAY-STREAM-OUTPUT-STREAM";
                          csym "VECTOR-POP"; csym "TYPE"; csym "VECTOR-PUSH";
                          csym "TYPE-ERROR"; csym "VECTOR-PUSH-EXTEND";
                          csym "TYPE-ERROR-DATUM"; csym "VECTORP";
                          csym "TYPE-ERROR-EXPECTED-TYPE"; csym "WARN";
                          csym "TYPE-OF"; csym "WARNING"; csym "TYPECASE";
                          csym "WHEN"; csym "TYPEP"; csym "WILD-PATHNAME-P";
                          csym "UNBOUND-SLOT"; csym "WITH-ACCESSORS";
                          csym "UNBOUND-SLOT-INSTANCE";
                          csym "WITH-COMPILATION-UNIT";
                          csym "UNBOUND-VARIABLE";
                          csym "WITH-CONDITION-RESTARTS";
                          csym "UNDEFINED-FUNCTION";
                          csym "WITH-HASH-TABLE-ITERATOR"; csym "UNEXPORT";
                          csym "WITH-INPUT-FROM-STRING"; csym "UNINTERN";
                          csym "WITH-OPEN-FILE"; csym "UNION";
                          csym "WITH-OPEN-STREAM"; csym "UNLESS";
                          csym "WITH-OUTPUT-TO-STRING"; csym "UNREAD-CHAR";
                          csym "WITH-PACKAGE-ITERATOR"; csym "UNSIGNED-BYTE";
                          csym "WITH-SIMPLE-RESTART"; csym "UNTRACE";
                          csym "WITH-SLOTS"; csym "UNUSE-PACKAGE";
                          csym "WITH-STANDARD-IO-SYNTAX";
                          csym "UNWIND-PROTECT"; csym "WRITE";
                          csym "UPDATE-INSTANCE-FOR-DIFFERENT-CLASS";
                          csym "WRITE-BYTE";
                          csym "UPDATE-INSTANCE-FOR-REDEFINED-CLASS";
                          csym "WRITE-CHAR";
                          csym "UPGRADED-ARRAY-ELEMENT-TYPE";
                          csym "WRITE-LINE";
                          csym "UPGRADED-COMPLEX-PART-TYPE";
                          csym "WRITE-SEQUENCE"; csym "UPPER-CASE-P";
                          csym "WRITE-STRING"; csym "USE-PACKAGE";
                          csym "WRITE-TO-STRING"; csym "USE-VALUE";
                          csym "Y-OR-N-P"; csym "USER-HOMEDIR-PATHNAME";
                          csym "YES-OR-NO-P"; csym "VALUES"; csym "ZEROP"]));
                 symbolp y; equal (symbol_package_name y) (str ACL2)])
             (equal (symbol_package_name (intern_in_package_of_symbol x y))
                (str ACL2)),
*)

val pkg_thm_for_initial_pkg_system_lemma =
 prove
  (``!pkg_system pkg x.
      ~(MEM x (imported_symbol_names pkg pkg_system))
      ==>
      (LOOKUP pkg pkg_system x = pkg)``,
   Induct
    THEN RW_TAC std_ss [LOOKUP_def]
    THEN Cases_on `h` THEN Cases_on `r`
    THEN RW_TAC list_ss [LOOKUP_def]
    THEN FULL_SIMP_TAC list_ss [imported_symbol_names_def]
    THEN Cases_on `pkg = q'`
    THEN RW_TAC list_ss []
    THEN METIS_TAC[]);

val STAR_COMMON_LISP_SYMBOLS_FROM_MAIN_LISP_PACKAGE_STAR = 
 time EVAL ``imported_symbol_names "ACL2" ACL2_PACKAGE_ALIST``;

val COMMON_LISP_SYMBOLS =
 if_save_thm
  ("COMMON_LISP_SYMBOLS",
   REWRITE_CONV
    [STAR_COMMON_LISP_SYMBOLS_FROM_MAIN_LISP_PACKAGE_STAR,
     rich_listTheory.MAP]
    ``List(MAP csym (imported_symbol_names "ACL2" ACL2_PACKAGE_ALIST))``);

val member_symbol_name_MEM =
 if_store_thm
  ("member_symbol_name_MEM",
   ``!l s. (|= member_symbol_name s (List l)) = MEM s (MAP symbol_name l)``,
   REWRITE_TAC[ACL2_TRUE]
     THEN Induct
     THEN RW_TAC list_ss [List_def]
     THEN Cases_on `s`
     THEN ACL2_SIMP_TAC[]
     THEN FULL_SIMP_TAC std_ss [GSYM nil_def]
     THEN ONCE_REWRITE_TAC[member_symbol_name_def]
     THEN ACL2_FULL_SIMP_TAC[]
     THEN FULL_SIMP_TAC std_ss 
           [GSYM nil_def,GSYM t_def,if_t_nil,itel_def,ite_def,
            EVAL ``"COMMON-LISP" = ""``,EVAL ``t = nil``]
     THEN Cases_on `h`
     THEN ACL2_FULL_SIMP_TAC[sexp_11,BASIC_INTERN_def]
     THEN FULL_SIMP_TAC std_ss 
           [sexp_11,sexp_distinct,GSYM nil_def,GSYM t_def,eq_imp_if,
            EVAL``t=nil``,EVAL``"T" = "NIL"``]
     THEN TRY(METIS_TAC[]));

val not_member_symbol_name_MEM =
 if_store_thm
  ("not_member_symbol_name_MEM",
   ``(member_symbol_name s (List l) = nil) = ~(MEM s (MAP symbol_name l))``,
   METIS_TAC[ACL2_TRUE,member_symbol_name_MEM]);

(*****************************************************************************)
(* |- LOOKUP "COMMON-LISP" ACL2_PACKAGE_ALIST s = "COMMON-LISP" : thm        *)
(*****************************************************************************)
val LOOKUP_COMMON_LISP =
 if_save_thm
  ("LOOKUP_COMMON_LISP",
   EVAL ``LOOKUP "COMMON-LISP" ACL2_PACKAGE_ALIST s``);

val symbol_name_csym =
 if_store_thm
  ("symbol_name_csym",
   ``symbol_name(csym s) = str s``,
   ACL2_SIMP_TAC[csym_def,BASIC_INTERN_def,COMMON_LISP_def,LOOKUP_COMMON_LISP]);

val MEM_MAP_MAP =
 if_store_thm
  ("MEM_MAP_MAP",
   ``!l. MEM (str s) (MAP symbol_name (MAP csym l)) = MEM s l``,
   Induct
    THEN RW_TAC list_ss [symbol_name_csym]);

val conspList =
 if_store_thm
  ("conspList",
   ``|= consp(List(x :: l))``,
   ACL2_SIMP_TAC[List_def]);

val acl2_package_defaxiom =
 store_thm
  ("acl2_package_defaxiom",
   ``|= implies
             (andl
                [stringp x;
                 not
                   (member_symbol_name x
                      (List
                         [csym "&ALLOW-OTHER-KEYS";
                          csym "*PRINT-MISER-WIDTH*"; csym "&AUX";
                          csym "*PRINT-PPRINT-DISPATCH*"; csym "&BODY";
                          csym "*PRINT-PRETTY*"; csym "&ENVIRONMENT";
                          csym "*PRINT-RADIX*"; csym "&KEY";
                          csym "*PRINT-READABLY*"; csym "&OPTIONAL";
                          csym "*PRINT-RIGHT-MARGIN*"; csym "&REST";
                          csym "*QUERY-IO*"; csym "&WHOLE";
                          csym "*RANDOM-STATE*"; csym "*";
                          csym "*READ-BASE*"; csym "**";
                          csym "*READ-DEFAULT-FLOAT-FORMAT*"; csym "***";
                          csym "*READ-EVAL*"; csym "*BREAK-ON-SIGNALS*";
                          csym "*READ-SUPPRESS*";
                          csym "*COMPILE-FILE-PATHNAME*"; csym "*READTABLE*";
                          csym "*COMPILE-FILE-TRUENAME*";
                          csym "*STANDARD-INPUT*"; csym "*COMPILE-PRINT*";
                          csym "*STANDARD-OUTPUT*"; csym "*COMPILE-VERBOSE*";
                          csym "*TERMINAL-IO*"; csym "*DEBUG-IO*";
                          csym "*TRACE-OUTPUT*"; csym "*DEBUGGER-HOOK*";
                          csym "+"; csym "*DEFAULT-PATHNAME-DEFAULTS*";
                          csym "++"; csym "*ERROR-OUTPUT*"; csym "+++";
                          csym "*FEATURES*"; csym "-";
                          csym "*GENSYM-COUNTER*"; csym "/";
                          csym "*LOAD-PATHNAME*"; csym "//";
                          csym "*LOAD-PRINT*"; csym "///";
                          csym "*LOAD-TRUENAME*"; csym "/=";
                          csym "*LOAD-VERBOSE*"; csym "1+";
                          csym "*MACROEXPAND-HOOK*"; csym "1-";
                          csym "*MODULES*"; csym "<"; csym "*PACKAGE*";
                          csym "<="; csym "*PRINT-ARRAY*"; csym "=";
                          csym "*PRINT-BASE*"; csym ">"; csym "*PRINT-CASE*";
                          csym ">="; csym "*PRINT-CIRCLE*"; csym "ABORT";
                          csym "*PRINT-ESCAPE*"; csym "ABS";
                          csym "*PRINT-GENSYM*"; csym "ACONS";
                          csym "*PRINT-LENGTH*"; csym "ACOS";
                          csym "*PRINT-LEVEL*"; csym "ACOSH";
                          csym "*PRINT-LINES*"; csym "ADD-METHOD";
                          csym "ADJOIN"; csym "ATOM"; csym "BOUNDP";
                          csym "ADJUST-ARRAY"; csym "BASE-CHAR";
                          csym "BREAK"; csym "ADJUSTABLE-ARRAY-P";
                          csym "BASE-STRING"; csym "BROADCAST-STREAM";
                          csym "ALLOCATE-INSTANCE"; csym "BIGNUM";
                          csym "BROADCAST-STREAM-STREAMS";
                          csym "ALPHA-CHAR-P"; csym "BIT";
                          csym "BUILT-IN-CLASS"; csym "ALPHANUMERICP";
                          csym "BIT-AND"; csym "BUTLAST"; csym "AND";
                          csym "BIT-ANDC1"; csym "BYTE"; csym "APPEND";
                          csym "BIT-ANDC2"; csym "BYTE-POSITION";
                          csym "APPLY"; csym "BIT-EQV"; csym "BYTE-SIZE";
                          csym "APROPOS"; csym "BIT-IOR"; csym "CAAAAR";
                          csym "APROPOS-LIST"; csym "BIT-NAND";
                          csym "CAAADR"; csym "AREF"; csym "BIT-NOR";
                          csym "CAAAR"; csym "ARITHMETIC-ERROR";
                          csym "BIT-NOT"; csym "CAADAR";
                          csym "ARITHMETIC-ERROR-OPERANDS"; csym "BIT-ORC1";
                          csym "CAADDR"; csym "ARITHMETIC-ERROR-OPERATION";
                          csym "BIT-ORC2"; csym "CAADR"; csym "ARRAY";
                          csym "BIT-VECTOR"; csym "CAAR";
                          csym "ARRAY-DIMENSION"; csym "BIT-VECTOR-P";
                          csym "CADAAR"; csym "ARRAY-DIMENSION-LIMIT";
                          csym "BIT-XOR"; csym "CADADR";
                          csym "ARRAY-DIMENSIONS"; csym "BLOCK";
                          csym "CADAR"; csym "ARRAY-DISPLACEMENT";
                          csym "BOOLE"; csym "CADDAR";
                          csym "ARRAY-ELEMENT-TYPE"; csym "BOOLE-1";
                          csym "CADDDR"; csym "ARRAY-HAS-FILL-POINTER-P";
                          csym "BOOLE-2"; csym "CADDR";
                          csym "ARRAY-IN-BOUNDS-P"; csym "BOOLE-AND";
                          csym "CADR"; csym "ARRAY-RANK"; csym "BOOLE-ANDC1";
                          csym "CALL-ARGUMENTS-LIMIT";
                          csym "ARRAY-RANK-LIMIT"; csym "BOOLE-ANDC2";
                          csym "CALL-METHOD"; csym "ARRAY-ROW-MAJOR-INDEX";
                          csym "BOOLE-C1"; csym "CALL-NEXT-METHOD";
                          csym "ARRAY-TOTAL-SIZE"; csym "BOOLE-C2";
                          csym "CAR"; csym "ARRAY-TOTAL-SIZE-LIMIT";
                          csym "BOOLE-CLR"; csym "CASE"; csym "ARRAYP";
                          csym "BOOLE-EQV"; csym "CATCH"; csym "ASH";
                          csym "BOOLE-IOR"; csym "CCASE"; csym "ASIN";
                          csym "BOOLE-NAND"; csym "CDAAAR"; csym "ASINH";
                          csym "BOOLE-NOR"; csym "CDAADR"; csym "ASSERT";
                          csym "BOOLE-ORC1"; csym "CDAAR"; csym "ASSOC";
                          csym "BOOLE-ORC2"; csym "CDADAR"; csym "ASSOC-IF";
                          csym "BOOLE-SET"; csym "CDADDR";
                          csym "ASSOC-IF-NOT"; csym "BOOLE-XOR";
                          csym "CDADR"; csym "ATAN"; csym "BOOLEAN";
                          csym "CDAR"; csym "ATANH"; csym "BOTH-CASE-P";
                          csym "CDDAAR"; csym "CDDADR"; csym "CLEAR-INPUT";
                          csym "COPY-TREE"; csym "CDDAR";
                          csym "CLEAR-OUTPUT"; csym "COS"; csym "CDDDAR";
                          csym "CLOSE"; csym "COSH"; csym "CDDDDR";
                          csym "CLRHASH"; csym "COUNT"; csym "CDDDR";
                          csym "CODE-CHAR"; csym "COUNT-IF"; csym "CDDR";
                          csym "COERCE"; csym "COUNT-IF-NOT"; csym "CDR";
                          csym "COMPILATION-SPEED"; csym "CTYPECASE";
                          csym "CEILING"; csym "COMPILE"; csym "DEBUG";
                          csym "CELL-ERROR"; csym "COMPILE-FILE";
                          csym "DECF"; csym "CELL-ERROR-NAME";
                          csym "COMPILE-FILE-PATHNAME"; csym "DECLAIM";
                          csym "CERROR"; csym "COMPILED-FUNCTION";
                          csym "DECLARATION"; csym "CHANGE-CLASS";
                          csym "COMPILED-FUNCTION-P"; csym "DECLARE";
                          csym "CHAR"; csym "COMPILER-MACRO";
                          csym "DECODE-FLOAT"; csym "CHAR-CODE";
                          csym "COMPILER-MACRO-FUNCTION";
                          csym "DECODE-UNIVERSAL-TIME";
                          csym "CHAR-CODE-LIMIT"; csym "COMPLEMENT";
                          csym "DEFCLASS"; csym "CHAR-DOWNCASE";
                          csym "COMPLEX"; csym "DEFCONSTANT";
                          csym "CHAR-EQUAL"; csym "COMPLEXP";
                          csym "DEFGENERIC"; csym "CHAR-GREATERP";
                          csym "COMPUTE-APPLICABLE-METHODS";
                          csym "DEFINE-COMPILER-MACRO"; csym "CHAR-INT";
                          csym "COMPUTE-RESTARTS"; csym "DEFINE-CONDITION";
                          csym "CHAR-LESSP"; csym "CONCATENATE";
                          csym "DEFINE-METHOD-COMBINATION"; csym "CHAR-NAME";
                          csym "CONCATENATED-STREAM";
                          csym "DEFINE-MODIFY-MACRO"; csym "CHAR-NOT-EQUAL";
                          csym "CONCATENATED-STREAM-STREAMS";
                          csym "DEFINE-SETF-EXPANDER";
                          csym "CHAR-NOT-GREATERP"; csym "COND";
                          csym "DEFINE-SYMBOL-MACRO"; csym "CHAR-NOT-LESSP";
                          csym "CONDITION"; csym "DEFMACRO";
                          csym "CHAR-UPCASE"; csym "CONJUGATE";
                          csym "DEFMETHOD"; csym "CHAR/="; csym "CONS";
                          csym "DEFPACKAGE"; csym "CHAR<"; csym "CONSP";
                          csym "DEFPARAMETER"; csym "CHAR<=";
                          csym "CONSTANTLY"; csym "DEFSETF"; csym "CHAR=";
                          csym "CONSTANTP"; csym "DEFSTRUCT"; csym "CHAR>";
                          csym "CONTINUE"; csym "DEFTYPE"; csym "CHAR>=";
                          csym "CONTROL-ERROR"; csym "DEFUN";
                          csym "CHARACTER"; csym "COPY-ALIST"; csym "DEFVAR";
                          csym "CHARACTERP"; csym "COPY-LIST"; csym "DELETE";
                          csym "CHECK-TYPE"; csym "COPY-PPRINT-DISPATCH";
                          csym "DELETE-DUPLICATES"; csym "CIS";
                          csym "COPY-READTABLE"; csym "DELETE-FILE";
                          csym "CLASS"; csym "COPY-SEQ"; csym "DELETE-IF";
                          csym "CLASS-NAME"; csym "COPY-STRUCTURE";
                          csym "DELETE-IF-NOT"; csym "CLASS-OF";
                          csym "COPY-SYMBOL"; csym "DELETE-PACKAGE";
                          csym "DENOMINATOR"; csym "EQ";
                          csym "DEPOSIT-FIELD"; csym "EQL"; csym "DESCRIBE";
                          csym "EQUAL"; csym "DESCRIBE-OBJECT";
                          csym "EQUALP"; csym "DESTRUCTURING-BIND";
                          csym "ERROR"; csym "DIGIT-CHAR"; csym "ETYPECASE";
                          csym "DIGIT-CHAR-P"; csym "EVAL"; csym "DIRECTORY";
                          csym "EVAL-WHEN"; csym "DIRECTORY-NAMESTRING";
                          csym "EVENP"; csym "DISASSEMBLE"; csym "EVERY";
                          csym "DIVISION-BY-ZERO"; csym "EXP"; csym "DO";
                          csym "EXPORT"; csym "DO*"; csym "EXPT";
                          csym "DO-ALL-SYMBOLS"; csym "EXTENDED-CHAR";
                          csym "DO-EXTERNAL-SYMBOLS"; csym "FBOUNDP";
                          csym "DO-SYMBOLS"; csym "FCEILING";
                          csym "DOCUMENTATION"; csym "FDEFINITION";
                          csym "DOLIST"; csym "FFLOOR"; csym "DOTIMES";
                          csym "FIFTH"; csym "DOUBLE-FLOAT";
                          csym "FILE-AUTHOR"; csym "DOUBLE-FLOAT-EPSILON";
                          csym "FILE-ERROR";
                          csym "DOUBLE-FLOAT-NEGATIVE-EPSILON";
                          csym "FILE-ERROR-PATHNAME"; csym "DPB";
                          csym "FILE-LENGTH"; csym "DRIBBLE";
                          csym "FILE-NAMESTRING"; csym "DYNAMIC-EXTENT";
                          csym "FILE-POSITION"; csym "ECASE";
                          csym "FILE-STREAM"; csym "ECHO-STREAM";
                          csym "FILE-STRING-LENGTH";
                          csym "ECHO-STREAM-INPUT-STREAM";
                          csym "FILE-WRITE-DATE";
                          csym "ECHO-STREAM-OUTPUT-STREAM"; csym "FILL";
                          csym "ED"; csym "FILL-POINTER"; csym "EIGHTH";
                          csym "FIND"; csym "ELT"; csym "FIND-ALL-SYMBOLS";
                          csym "ENCODE-UNIVERSAL-TIME"; csym "FIND-CLASS";
                          csym "END-OF-FILE"; csym "FIND-IF"; csym "ENDP";
                          csym "FIND-IF-NOT"; csym "ENOUGH-NAMESTRING";
                          csym "FIND-METHOD";
                          csym "ENSURE-DIRECTORIES-EXIST";
                          csym "FIND-PACKAGE";
                          csym "ENSURE-GENERIC-FUNCTION";
                          csym "FIND-RESTART"; csym "FIND-SYMBOL";
                          csym "GET-INTERNAL-RUN-TIME"; csym "FINISH-OUTPUT";
                          csym "GET-MACRO-CHARACTER"; csym "FIRST";
                          csym "GET-OUTPUT-STREAM-STRING"; csym "FIXNUM";
                          csym "GET-PROPERTIES"; csym "FLET";
                          csym "GET-SETF-EXPANSION"; csym "FLOAT";
                          csym "GET-UNIVERSAL-TIME"; csym "FLOAT-DIGITS";
                          csym "GETF"; csym "FLOAT-PRECISION";
                          csym "GETHASH"; csym "FLOAT-RADIX"; csym "GO";
                          csym "FLOAT-SIGN"; csym "GRAPHIC-CHAR-P";
                          csym "FLOATING-POINT-INEXACT"; csym "HANDLER-BIND";
                          csym "FLOATING-POINT-INVALID-OPERATION";
                          csym "HANDLER-CASE";
                          csym "FLOATING-POINT-OVERFLOW"; csym "HASH-TABLE";
                          csym "FLOATING-POINT-UNDERFLOW";
                          csym "HASH-TABLE-COUNT"; csym "FLOATP";
                          csym "HASH-TABLE-P"; csym "FLOOR";
                          csym "HASH-TABLE-REHASH-SIZE"; csym "FMAKUNBOUND";
                          csym "HASH-TABLE-REHASH-THRESHOLD";
                          csym "FORCE-OUTPUT"; csym "HASH-TABLE-SIZE";
                          csym "FORMAT"; csym "HASH-TABLE-TEST";
                          csym "FORMATTER"; csym "HOST-NAMESTRING";
                          csym "FOURTH"; csym "IDENTITY"; csym "FRESH-LINE";
                          csym "IF"; csym "FROUND"; csym "IGNORABLE";
                          csym "FTRUNCATE"; csym "IGNORE"; csym "FTYPE";
                          csym "IGNORE-ERRORS"; csym "FUNCALL";
                          csym "IMAGPART"; csym "FUNCTION"; csym "IMPORT";
                          csym "FUNCTION-KEYWORDS"; csym "IN-PACKAGE";
                          csym "FUNCTION-LAMBDA-EXPRESSION"; csym "INCF";
                          csym "FUNCTIONP"; csym "INITIALIZE-INSTANCE";
                          csym "GCD"; csym "INLINE"; csym "GENERIC-FUNCTION";
                          csym "INPUT-STREAM-P"; csym "GENSYM";
                          csym "INSPECT"; csym "GENTEMP"; csym "INTEGER";
                          csym "GET"; csym "INTEGER-DECODE-FLOAT";
                          csym "GET-DECODED-TIME"; csym "INTEGER-LENGTH";
                          csym "GET-DISPATCH-MACRO-CHARACTER";
                          csym "INTEGERP"; csym "GET-INTERNAL-REAL-TIME";
                          csym "INTERACTIVE-STREAM-P"; csym "INTERN";
                          csym "LISP-IMPLEMENTATION-TYPE";
                          csym "INTERNAL-TIME-UNITS-PER-SECOND";
                          csym "LISP-IMPLEMENTATION-VERSION";
                          csym "INTERSECTION"; csym "LIST";
                          csym "INVALID-METHOD-ERROR"; csym "LIST*";
                          csym "INVOKE-DEBUGGER"; csym "LIST-ALL-PACKAGES";
                          csym "INVOKE-RESTART"; csym "LIST-LENGTH";
                          csym "INVOKE-RESTART-INTERACTIVELY"; csym "LISTEN";
                          csym "ISQRT"; csym "LISTP"; csym KEYWORD;
                          csym "LOAD"; csym "KEYWORDP";
                          csym "LOAD-LOGICAL-PATHNAME-TRANSLATIONS";
                          csym "LABELS"; csym "LOAD-TIME-VALUE";
                          csym "LAMBDA"; csym "LOCALLY";
                          csym "LAMBDA-LIST-KEYWORDS"; csym "LOG";
                          csym "LAMBDA-PARAMETERS-LIMIT"; csym "LOGAND";
                          csym "LAST"; csym "LOGANDC1"; csym "LCM";
                          csym "LOGANDC2"; csym "LDB"; csym "LOGBITP";
                          csym "LDB-TEST"; csym "LOGCOUNT"; csym "LDIFF";
                          csym "LOGEQV"; csym "LEAST-NEGATIVE-DOUBLE-FLOAT";
                          csym "LOGICAL-PATHNAME";
                          csym "LEAST-NEGATIVE-LONG-FLOAT";
                          csym "LOGICAL-PATHNAME-TRANSLATIONS";
                          csym "LEAST-NEGATIVE-NORMALIZED-DOUBLE-FLOAT";
                          csym "LOGIOR";
                          csym "LEAST-NEGATIVE-NORMALIZED-LONG-FLOAT";
                          csym "LOGNAND";
                          csym "LEAST-NEGATIVE-NORMALIZED-SHORT-FLOAT";
                          csym "LOGNOR";
                          csym "LEAST-NEGATIVE-NORMALIZED-SINGLE-FLOAT";
                          csym "LOGNOT"; csym "LEAST-NEGATIVE-SHORT-FLOAT";
                          csym "LOGORC1"; csym "LEAST-NEGATIVE-SINGLE-FLOAT";
                          csym "LOGORC2"; csym "LEAST-POSITIVE-DOUBLE-FLOAT";
                          csym "LOGTEST"; csym "LEAST-POSITIVE-LONG-FLOAT";
                          csym "LOGXOR";
                          csym "LEAST-POSITIVE-NORMALIZED-DOUBLE-FLOAT";
                          csym "LONG-FLOAT";
                          csym "LEAST-POSITIVE-NORMALIZED-LONG-FLOAT";
                          csym "LONG-FLOAT-EPSILON";
                          csym "LEAST-POSITIVE-NORMALIZED-SHORT-FLOAT";
                          csym "LONG-FLOAT-NEGATIVE-EPSILON";
                          csym "LEAST-POSITIVE-NORMALIZED-SINGLE-FLOAT";
                          csym "LONG-SITE-NAME";
                          csym "LEAST-POSITIVE-SHORT-FLOAT"; csym "LOOP";
                          csym "LEAST-POSITIVE-SINGLE-FLOAT";
                          csym "LOOP-FINISH"; csym "LENGTH";
                          csym "LOWER-CASE-P"; csym "LET";
                          csym "MACHINE-INSTANCE"; csym "LET*";
                          csym "MACHINE-TYPE"; csym "MACHINE-VERSION";
                          csym "MASK-FIELD"; csym "MACRO-FUNCTION";
                          csym "MAX"; csym "MACROEXPAND"; csym "MEMBER";
                          csym "MACROEXPAND-1"; csym "MEMBER-IF";
                          csym "MACROLET"; csym "MEMBER-IF-NOT";
                          csym "MAKE-ARRAY"; csym "MERGE";
                          csym "MAKE-BROADCAST-STREAM";
                          csym "MERGE-PATHNAMES";
                          csym "MAKE-CONCATENATED-STREAM"; csym "METHOD";
                          csym "MAKE-CONDITION"; csym "METHOD-COMBINATION";
                          csym "MAKE-DISPATCH-MACRO-CHARACTER";
                          csym "METHOD-COMBINATION-ERROR";
                          csym "MAKE-ECHO-STREAM"; csym "METHOD-QUALIFIERS";
                          csym "MAKE-HASH-TABLE"; csym "MIN";
                          csym "MAKE-INSTANCE"; csym "MINUSP";
                          csym "MAKE-INSTANCES-OBSOLETE"; csym "MISMATCH";
                          csym "MAKE-LIST"; csym "MOD";
                          csym "MAKE-LOAD-FORM";
                          csym "MOST-NEGATIVE-DOUBLE-FLOAT";
                          csym "MAKE-LOAD-FORM-SAVING-SLOTS";
                          csym "MOST-NEGATIVE-FIXNUM"; csym "MAKE-METHOD";
                          csym "MOST-NEGATIVE-LONG-FLOAT";
                          csym "MAKE-PACKAGE";
                          csym "MOST-NEGATIVE-SHORT-FLOAT";
                          csym "MAKE-PATHNAME";
                          csym "MOST-NEGATIVE-SINGLE-FLOAT";
                          csym "MAKE-RANDOM-STATE";
                          csym "MOST-POSITIVE-DOUBLE-FLOAT";
                          csym "MAKE-SEQUENCE"; csym "MOST-POSITIVE-FIXNUM";
                          csym "MAKE-STRING";
                          csym "MOST-POSITIVE-LONG-FLOAT";
                          csym "MAKE-STRING-INPUT-STREAM";
                          csym "MOST-POSITIVE-SHORT-FLOAT";
                          csym "MAKE-STRING-OUTPUT-STREAM";
                          csym "MOST-POSITIVE-SINGLE-FLOAT";
                          csym "MAKE-SYMBOL"; csym "MUFFLE-WARNING";
                          csym "MAKE-SYNONYM-STREAM";
                          csym "MULTIPLE-VALUE-BIND";
                          csym "MAKE-TWO-WAY-STREAM";
                          csym "MULTIPLE-VALUE-CALL"; csym "MAKUNBOUND";
                          csym "MULTIPLE-VALUE-LIST"; csym "MAP";
                          csym "MULTIPLE-VALUE-PROG1"; csym "MAP-INTO";
                          csym "MULTIPLE-VALUE-SETQ"; csym "MAPC";
                          csym "MULTIPLE-VALUES-LIMIT"; csym "MAPCAN";
                          csym "NAME-CHAR"; csym "MAPCAR"; csym "NAMESTRING";
                          csym "MAPCON"; csym "NBUTLAST"; csym "MAPHASH";
                          csym "NCONC"; csym "MAPL"; csym "NEXT-METHOD-P";
                          csym "MAPLIST"; nil; csym "NINTERSECTION";
                          csym "PACKAGE-ERROR"; csym "NINTH";
                          csym "PACKAGE-ERROR-PACKAGE";
                          csym "NO-APPLICABLE-METHOD"; csym "PACKAGE-NAME";
                          csym "NO-NEXT-METHOD"; csym "PACKAGE-NICKNAMES";
                          csym "NOT"; csym "PACKAGE-SHADOWING-SYMBOLS";
                          csym "NOTANY"; csym "PACKAGE-USE-LIST";
                          csym "NOTEVERY"; csym "PACKAGE-USED-BY-LIST";
                          csym "NOTINLINE"; csym "PACKAGEP"; csym "NRECONC";
                          csym "PAIRLIS"; csym "NREVERSE";
                          csym "PARSE-ERROR"; csym "NSET-DIFFERENCE";
                          csym "PARSE-INTEGER"; csym "NSET-EXCLUSIVE-OR";
                          csym "PARSE-NAMESTRING"; csym "NSTRING-CAPITALIZE";
                          csym "PATHNAME"; csym "NSTRING-DOWNCASE";
                          csym "PATHNAME-DEVICE"; csym "NSTRING-UPCASE";
                          csym "PATHNAME-DIRECTORY"; csym "NSUBLIS";
                          csym "PATHNAME-HOST"; csym "NSUBST";
                          csym "PATHNAME-MATCH-P"; csym "NSUBST-IF";
                          csym "PATHNAME-NAME"; csym "NSUBST-IF-NOT";
                          csym "PATHNAME-TYPE"; csym "NSUBSTITUTE";
                          csym "PATHNAME-VERSION"; csym "NSUBSTITUTE-IF";
                          csym "PATHNAMEP"; csym "NSUBSTITUTE-IF-NOT";
                          csym "PEEK-CHAR"; csym "NTH"; csym "PHASE";
                          csym "NTH-VALUE"; csym "PI"; csym "NTHCDR";
                          csym "PLUSP"; csym "NULL"; csym "POP";
                          csym "NUMBER"; csym "POSITION"; csym "NUMBERP";
                          csym "POSITION-IF"; csym "NUMERATOR";
                          csym "POSITION-IF-NOT"; csym "NUNION";
                          csym "PPRINT"; csym "ODDP"; csym "PPRINT-DISPATCH";
                          csym "OPEN"; csym "PPRINT-EXIT-IF-LIST-EXHAUSTED";
                          csym "OPEN-STREAM-P"; csym "PPRINT-FILL";
                          csym "OPTIMIZE"; csym "PPRINT-INDENT"; csym "OR";
                          csym "PPRINT-LINEAR"; csym "OTHERWISE";
                          csym "PPRINT-LOGICAL-BLOCK";
                          csym "OUTPUT-STREAM-P"; csym "PPRINT-NEWLINE";
                          csym "PACKAGE"; csym "PPRINT-POP";
                          csym "PPRINT-TAB"; csym "READ-CHAR";
                          csym "PPRINT-TABULAR"; csym "READ-CHAR-NO-HANG";
                          csym "PRIN1"; csym "READ-DELIMITED-LIST";
                          csym "PRIN1-TO-STRING"; csym "READ-FROM-STRING";
                          csym "PRINC"; csym "READ-LINE";
                          csym "PRINC-TO-STRING";
                          csym "READ-PRESERVING-WHITESPACE"; csym "PRINT";
                          csym "READ-SEQUENCE"; csym "PRINT-NOT-READABLE";
                          csym "READER-ERROR";
                          csym "PRINT-NOT-READABLE-OBJECT"; csym "READTABLE";
                          csym "PRINT-OBJECT"; csym "READTABLE-CASE";
                          csym "PRINT-UNREADABLE-OBJECT"; csym "READTABLEP";
                          csym "PROBE-FILE"; csym "REAL"; csym "PROCLAIM";
                          csym "REALP"; csym "PROG"; csym "REALPART";
                          csym "PROG*"; csym "REDUCE"; csym "PROG1";
                          csym "REINITIALIZE-INSTANCE"; csym "PROG2";
                          csym "REM"; csym "PROGN"; csym "REMF";
                          csym "PROGRAM-ERROR"; csym "REMHASH"; csym "PROGV";
                          csym "REMOVE"; csym "PROVIDE";
                          csym "REMOVE-DUPLICATES"; csym "PSETF";
                          csym "REMOVE-IF"; csym "PSETQ";
                          csym "REMOVE-IF-NOT"; csym "PUSH";
                          csym "REMOVE-METHOD"; csym "PUSHNEW";
                          csym "REMPROP"; csym "QUOTE"; csym "RENAME-FILE";
                          csym "RANDOM"; csym "RENAME-PACKAGE";
                          csym "RANDOM-STATE"; csym "REPLACE";
                          csym "RANDOM-STATE-P"; csym "REQUIRE";
                          csym "RASSOC"; csym "REST"; csym "RASSOC-IF";
                          csym "RESTART"; csym "RASSOC-IF-NOT";
                          csym "RESTART-BIND"; csym "RATIO";
                          csym "RESTART-CASE"; csym "RATIONAL";
                          csym "RESTART-NAME"; csym "RATIONALIZE";
                          csym "RETURN"; csym "RATIONALP";
                          csym "RETURN-FROM"; csym "READ"; csym "REVAPPEND";
                          csym "READ-BYTE"; csym "REVERSE"; csym "ROOM";
                          csym "SIMPLE-BIT-VECTOR"; csym "ROTATEF";
                          csym "SIMPLE-BIT-VECTOR-P"; csym "ROUND";
                          csym "SIMPLE-CONDITION"; csym "ROW-MAJOR-AREF";
                          csym "SIMPLE-CONDITION-FORMAT-ARGUMENTS";
                          csym "RPLACA";
                          csym "SIMPLE-CONDITION-FORMAT-CONTROL";
                          csym "RPLACD"; csym "SIMPLE-ERROR"; csym "SAFETY";
                          csym "SIMPLE-STRING"; csym "SATISFIES";
                          csym "SIMPLE-STRING-P"; csym "SBIT";
                          csym "SIMPLE-TYPE-ERROR"; csym "SCALE-FLOAT";
                          csym "SIMPLE-VECTOR"; csym "SCHAR";
                          csym "SIMPLE-VECTOR-P"; csym "SEARCH";
                          csym "SIMPLE-WARNING"; csym "SECOND"; csym "SIN";
                          csym "SEQUENCE"; csym "SINGLE-FLOAT";
                          csym "SERIOUS-CONDITION";
                          csym "SINGLE-FLOAT-EPSILON"; csym "SET";
                          csym "SINGLE-FLOAT-NEGATIVE-EPSILON";
                          csym "SET-DIFFERENCE"; csym "SINH";
                          csym "SET-DISPATCH-MACRO-CHARACTER"; csym "SIXTH";
                          csym "SET-EXCLUSIVE-OR"; csym "SLEEP";
                          csym "SET-MACRO-CHARACTER"; csym "SLOT-BOUNDP";
                          csym "SET-PPRINT-DISPATCH"; csym "SLOT-EXISTS-P";
                          csym "SET-SYNTAX-FROM-CHAR";
                          csym "SLOT-MAKUNBOUND"; csym "SETF";
                          csym "SLOT-MISSING"; csym "SETQ";
                          csym "SLOT-UNBOUND"; csym "SEVENTH";
                          csym "SLOT-VALUE"; csym "SHADOW";
                          csym "SOFTWARE-TYPE"; csym "SHADOWING-IMPORT";
                          csym "SOFTWARE-VERSION"; csym "SHARED-INITIALIZE";
                          csym "SOME"; csym "SHIFTF"; csym "SORT";
                          csym "SHORT-FLOAT"; csym "SPACE";
                          csym "SHORT-FLOAT-EPSILON"; csym "SPECIAL";
                          csym "SHORT-FLOAT-NEGATIVE-EPSILON";
                          csym "SPECIAL-OPERATOR-P"; csym "SHORT-SITE-NAME";
                          csym "SPEED"; csym "SIGNAL"; csym "SQRT";
                          csym "SIGNED-BYTE"; csym "STABLE-SORT";
                          csym "SIGNUM"; csym "STANDARD";
                          csym "SIMPLE-ARRAY"; csym "STANDARD-CHAR";
                          csym "SIMPLE-BASE-STRING"; csym "STANDARD-CHAR-P";
                          csym "STANDARD-CLASS"; csym "SUBLIS";
                          csym "STANDARD-GENERIC-FUNCTION"; csym "SUBSEQ";
                          csym "STANDARD-METHOD"; csym "SUBSETP";
                          csym "STANDARD-OBJECT"; csym "SUBST"; csym "STEP";
                          csym "SUBST-IF"; csym "STORAGE-CONDITION";
                          csym "SUBST-IF-NOT"; csym "STORE-VALUE";
                          csym "SUBSTITUTE"; csym "STREAM";
                          csym "SUBSTITUTE-IF"; csym "STREAM-ELEMENT-TYPE";
                          csym "SUBSTITUTE-IF-NOT"; csym "STREAM-ERROR";
                          csym "SUBTYPEP"; csym "STREAM-ERROR-STREAM";
                          csym "SVREF"; csym "STREAM-EXTERNAL-FORMAT";
                          csym "SXHASH"; csym "STREAMP"; csym "SYMBOL";
                          csym "STRING"; csym "SYMBOL-FUNCTION";
                          csym "STRING-CAPITALIZE"; csym "SYMBOL-MACROLET";
                          csym "STRING-DOWNCASE"; csym "SYMBOL-NAME";
                          csym "STRING-EQUAL"; csym "SYMBOL-PACKAGE";
                          csym "STRING-GREATERP"; csym "SYMBOL-PLIST";
                          csym "STRING-LEFT-TRIM"; csym "SYMBOL-VALUE";
                          csym "STRING-LESSP"; csym "SYMBOLP";
                          csym "STRING-NOT-EQUAL"; csym "SYNONYM-STREAM";
                          csym "STRING-NOT-GREATERP";
                          csym "SYNONYM-STREAM-SYMBOL";
                          csym "STRING-NOT-LESSP"; t;
                          csym "STRING-RIGHT-TRIM"; csym "TAGBODY";
                          csym "STRING-STREAM"; csym "TAILP";
                          csym "STRING-TRIM"; csym "TAN";
                          csym "STRING-UPCASE"; csym "TANH"; csym "STRING/=";
                          csym "TENTH"; csym "STRING<"; csym "TERPRI";
                          csym "STRING<="; csym "THE"; csym "STRING=";
                          csym "THIRD"; csym "STRING>"; csym "THROW";
                          csym "STRING>="; csym "TIME"; csym "STRINGP";
                          csym "TRACE"; csym "STRUCTURE";
                          csym "TRANSLATE-LOGICAL-PATHNAME";
                          csym "STRUCTURE-CLASS"; csym "TRANSLATE-PATHNAME";
                          csym "STRUCTURE-OBJECT"; csym "TREE-EQUAL";
                          csym "STYLE-WARNING"; csym "TRUENAME";
                          csym "TRUNCATE"; csym "VALUES-LIST";
                          csym "TWO-WAY-STREAM"; csym "VARIABLE";
                          csym "TWO-WAY-STREAM-INPUT-STREAM"; csym "VECTOR";
                          csym "TWO-WAY-STREAM-OUTPUT-STREAM";
                          csym "VECTOR-POP"; csym "TYPE"; csym "VECTOR-PUSH";
                          csym "TYPE-ERROR"; csym "VECTOR-PUSH-EXTEND";
                          csym "TYPE-ERROR-DATUM"; csym "VECTORP";
                          csym "TYPE-ERROR-EXPECTED-TYPE"; csym "WARN";
                          csym "TYPE-OF"; csym "WARNING"; csym "TYPECASE";
                          csym "WHEN"; csym "TYPEP"; csym "WILD-PATHNAME-P";
                          csym "UNBOUND-SLOT"; csym "WITH-ACCESSORS";
                          csym "UNBOUND-SLOT-INSTANCE";
                          csym "WITH-COMPILATION-UNIT";
                          csym "UNBOUND-VARIABLE";
                          csym "WITH-CONDITION-RESTARTS";
                          csym "UNDEFINED-FUNCTION";
                          csym "WITH-HASH-TABLE-ITERATOR"; csym "UNEXPORT";
                          csym "WITH-INPUT-FROM-STRING"; csym "UNINTERN";
                          csym "WITH-OPEN-FILE"; csym "UNION";
                          csym "WITH-OPEN-STREAM"; csym "UNLESS";
                          csym "WITH-OUTPUT-TO-STRING"; csym "UNREAD-CHAR";
                          csym "WITH-PACKAGE-ITERATOR"; csym "UNSIGNED-BYTE";
                          csym "WITH-SIMPLE-RESTART"; csym "UNTRACE";
                          csym "WITH-SLOTS"; csym "UNUSE-PACKAGE";
                          csym "WITH-STANDARD-IO-SYNTAX";
                          csym "UNWIND-PROTECT"; csym "WRITE";
                          csym "UPDATE-INSTANCE-FOR-DIFFERENT-CLASS";
                          csym "WRITE-BYTE";
                          csym "UPDATE-INSTANCE-FOR-REDEFINED-CLASS";
                          csym "WRITE-CHAR";
                          csym "UPGRADED-ARRAY-ELEMENT-TYPE";
                          csym "WRITE-LINE";
                          csym "UPGRADED-COMPLEX-PART-TYPE";
                          csym "WRITE-SEQUENCE"; csym "UPPER-CASE-P";
                          csym "WRITE-STRING"; csym "USE-PACKAGE";
                          csym "WRITE-TO-STRING"; csym "USE-VALUE";
                          csym "Y-OR-N-P"; csym "USER-HOMEDIR-PATHNAME";
                          csym "YES-OR-NO-P"; csym "VALUES"; csym "ZEROP"]));
                 symbolp y; equal (symbol_package_name y) (str ACL2)])
             (equal (symbol_package_name (intern_in_package_of_symbol x y))
                (str ACL2))``,
   RW_TAC std_ss 
    [GSYM COMMON_LISP_SYMBOLS,t_def,nil_def,GSYM csym_def,GSYM COMMON_LISP_def,KEYWORD_def]
    THEN Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC[]
    THEN FULL_SIMP_TAC arith_ss 
          [if_t_nil,GSYM t_def, GSYM nil_def,BASIC_INTERN_def]
    THEN ACL2_FULL_SIMP_TAC
          [if_eq_imp,sexp_11,LET_DEF,LOOKUP_PKG_WITNESS,
           BASIC_INTERN_def,ACL2_def,EVAL ``"ACL2" = ""``]
    THEN RW_TAC std_ss []
    THEN ASSUM_LIST
          (fn thl => POP_ASSUM(K ALL_TAC) THEN ASSUME_TAC(SIMP_RULE std_ss [el 2 thl] (el 1 thl)))
    THEN ACL2_FULL_SIMP_TAC
          [if_eq_imp,sexp_11,LET_DEF,LOOKUP_PKG_WITNESS,BASIC_INTERN_def]
    THEN FULL_SIMP_TAC std_ss [GSYM nil_def,not_member_symbol_name_MEM,MEM_MAP_MAP]
    THEN METIS_TAC
          [VALID_ACL2_PACKAGE_ALIST,LOOKUP_NOT_EMPTY_STRING,
           LOOKUP_PKG_WITNESS,LOOKUP_IDEMPOTENT,
           pkg_thm_for_initial_pkg_system_lemma]);

(*****************************************************************************)
(* val LOOKUP_EMPTY = |- LOOKUP "" ACL2_PACKAGE_ALIST s = "" : thm           *)
(*****************************************************************************)
val LOOKUP_EMPTY = 
 if_save_thm("LOOKUP_EMPTY", EVAL ``LOOKUP "" ACL2_PACKAGE_ALIST s``);

(*
     [oracles: DEFAXIOM ACL2::KEYWORD-PACKAGE, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [stringp x; symbolp y;
                 equal (symbol_package_name y) (str KEYWORD)])
             (equal (symbol_package_name (intern_in_package_of_symbol x y))
                (str KEYWORD)),
*)

val LOOKUP_KEYWORD = 
 if_save_thm
  ("LOOKUP_KEYWORD",
   time EVAL ``LOOKUP "KEYWORD" ACL2_PACKAGE_ALIST s``);

val keyword_package_defaxiom =
 store_thm
  ("keyword_package_defaxiom",
   ``|= implies
         (andl
           [stringp x; symbolp y;
            equal (symbol_package_name y) (str KEYWORD)])
          (equal (symbol_package_name (intern_in_package_of_symbol x y))
                 (str KEYWORD))``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC[BASIC_INTERN_def]
    THEN FULL_SIMP_TAC std_ss
          [GSYM t_def,GSYM nil_def,if_t_nil]
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss
          [LOOKUP_KEYWORD,KEYWORD_def,EVAL``"KEYWORD" = ""``]
    THEN ACL2_FULL_SIMP_TAC[]
    THEN FULL_SIMP_TAC std_ss
          [BASIC_INTERN_def,GSYM t_def,GSYM nil_def,if_t_nil,EVAL``"KEYWORD" = ""``,
           LOOKUP_KEYWORD,EVAL ``t = nil``]);

(*
     [oracles: DEFAXIOM ACL2::STRING-IS-NOT-CIRCULAR, DISK_THM] [axioms: ] []
     |- |= equal (csym "STRING")
             (intern_in_package_of_symbol
                (coerce
                   (cons (chr #"S")
                      (cons (chr #"T")
                         (cons (chr #"R")
                            (cons (chr #"I")
                               (cons (chr #"N")
                                  (cons (chr #"G") (nat 0)))))))
                   (cons (chr #"S")
                      (cons (chr #"T")
                         (cons (chr #"R")
                            (cons (chr #"I")
                               (cons (chr #"N")
                                  (cons (chr #"G") (nat 0))))))))
                (intern_in_package_of_symbol (nat 0) (nat 0))),
*)

val string_is_not_circular_defaxiom =
 time store_thm
  ("string_is_not_circular_defaxiom",
   ``|= equal (csym "STRING")
              (intern_in_package_of_symbol
                (coerce
                   (cons (chr #"S")
                      (cons (chr #"T")
                         (cons (chr #"R")
                            (cons (chr #"I")
                               (cons (chr #"N")
                                  (cons (chr #"G") (nat 0)))))))
                   (cons (chr #"S")
                      (cons (chr #"T")
                         (cons (chr #"R")
                            (cons (chr #"I")
                               (cons (chr #"N")
                                  (cons (chr #"G") (nat 0))))))))
                (intern_in_package_of_symbol (nat 0) (nat 0)))``,
   CONV_TAC EVAL);

(*
     [oracles: DEFAXIOM ACL2::NIL-IS-NOT-CIRCULAR, DISK_THM] [axioms: ] []
     |- |= equal nil
             (intern_in_package_of_symbol
                (coerce
                   (cons (chr #"N")
                      (cons (chr #"I") (cons (chr #"L") (nat 0))))
                   (csym "STRING")) (csym "STRING")),
*)

val nil_is_not_circular_defaxiom =
 time store_thm
  ("nil_is_not_circular_defaxiom",
   ``|= equal nil
             (intern_in_package_of_symbol
                (coerce
                   (cons (chr #"N")
                      (cons (chr #"I") (cons (chr #"L") (nat 0))))
                   (csym "STRING")) (csym "STRING"))``,
   CONV_TAC EVAL);

(*
     [oracles: DEFAXIOM ACL2::CHAR-CODE-LINEAR, DISK_THM] [axioms: ] []
     |- |= less (char_code x) (nat 256),
*)

val abs_rat_reduce_pos =
 if_store_thm
  ("abs_rat_reduce_pos",
   ``!a b.
      0 < b
      ==>
      (reduce(rep_frac(rep_rat(abs_rat(abs_frac (a,b))))) = reduce(a,b))``,
   METIS_TAC [rat_of_int_div_pos,pos_reduce_rat]);

val rat_0_nmr =
 if_store_thm
  ("rat_0_nmr",
   ``rat_nmr 0 = 0``,
   RW_TAC intLib.int_ss
    [GSYM integerTheory.INT_LE_ANTISYM,ratTheory.RAT_LEQ_REF,
     GSYM ratTheory.RAT_LEQ0_NMR,GSYM ratTheory.RAT_0LEQ_NMR]);

val SGN1 =
 if_store_thm
  ("SGN1",
   ``SGN 1 = 1``,
   METIS_TAC[EVAL ``(1:int) > 0``,intExtensionTheory.INT_SGN_CLAUSES]);

val abs_rat_reduce0 =
 if_store_thm
  ("abs_rat_reduce0",
   ``reduce(rep_frac(rep_rat 0)) = (0,1)``,
   RW_TAC intLib.int_ss 
    [GSYM ratTheory.RAT_0,ratTheory.rat_0_def,fracTheory.frac_0_def,
     abs_rat_reduce_pos,reduce0,SGN1]);

val reduced_nmr_0 =
 if_store_thm
  ("reduced_nmr_0",
   ``reduced_nmr 0 = 0``,
   RW_TAC std_ss 
    [reduced_nmr_def,abs_rat_reduce0]);

val gcd1 =
 if_store_thm
  ("gcd1",
   ``!n. (gcd n 1 = 1) /\ (gcd 1 n = 1)``,
   Induct
    THEN RW_TAC std_ss [gcd_def]
    THEN ONCE_REWRITE_TAC [DECIDE ``1 = SUC 0``]
    THEN RW_TAC std_ss [gcd_def]);

val abs_less =
 if_store_thm
  ("abs_less",
   ``abs_rat (abs_frac (m,1)) < abs_rat (abs_frac (n,1)) = m < n``,
   RW_TAC intLib.int_ss 
    [ratTheory.RAT_LES_CALCULATE,fracTheory.NMR,fracTheory.DNM]);
   
val reduce_int =
 if_store_thm
  ("reduce_int",
   ``!c. reduce(c,1) = (c,1)``,
   RW_TAC std_ss [reduce_def]
    THEN FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def]
    THEN `ABS 1 = 1` by Cooper.COOPER_TAC
    THEN FULL_SIMP_TAC std_ss [integerTheory.NUM_OF_INT,gcd1,integerTheory.INT_DIV_1]);

val char_code_linear_defaxiom =
 store_thm
  ("char_code_linear_defaxiom",
   ``|= less (char_code x) (nat 256)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[nat_def,int_def,cpx_def]
    THEN FULL_SIMP_TAC intLib.int_ss 
           [IS_INT_def,complex_rationalTheory.DIVIDES_def,
            sexpTheory.rat_def,ratTheory.rat_0_def,fracTheory.frac_0_def]
    THEN FULL_SIMP_TAC intLib.int_ss 
           [GSYM ratTheory.rat_0_def,GSYM fracTheory.frac_0_def,ratTheory.RAT_0,rat_0_nmr,
            reduced_nmr_0]
    THEN FULL_SIMP_TAC arith_ss 
          [if_t_nil,GSYM t_def, GSYM nil_def,BASIC_INTERN_def,
           reduced_nmr_def,abs_rat_reduce_pos,reduce_int,abs_less,
           GSYM ratTheory.RAT_0,ratTheory.rat_0_def,fracTheory.frac_0_def,
           ratTheory.RAT_ABS_EQUIV,ratTheory.rat_equiv_def]
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,realpart_def,imagpart_def,
           t_def,nil_def,IS_INT_EXISTS,
           complex_def,add_def,mult_def,complex_rationalp_def,
           nat_def,int_def,cpx_def,code_char_def]
    THEN FULL_SIMP_TAC intLib.int_ss
          [fracTheory.frac_0_def,fracTheory.frac_nmr_def,fracTheory.frac_dnm_def,
           stringTheory.ORD_BOUND,
           SIMP_RULE intLib.int_ss [] (Q.SPEC `(0,1)`        (CONJUNCT2 fracTheory.frac_bij)),
           SIMP_RULE intLib.int_ss [] (Q.SPEC `(256,1)`      (CONJUNCT2 fracTheory.frac_bij)),
           SIMP_RULE intLib.int_ss [] (Q.SPEC `(&(ORD c),1)` (CONJUNCT2 fracTheory.frac_bij))]
    THEN `ORD c < 256` by PROVE_TAC[stringTheory.ORD_BOUND]
    THEN Cooper.COOPER_TAC);

(*
     [oracles: DEFAXIOM ACL2::CODE-CHAR-TYPE] [axioms: ] []
     |- |= characterp (code_char n),
*)

val code_char_type_defaxiom =
 store_thm
  ("code_char_type_defaxiom",
   ``|= characterp (code_char n)``,
   Cases_on `n`
    THEN ACL2_SIMP_TAC[nat_def,int_def,cpx_def]
    THEN Cases_on `c`
    THEN FULL_SIMP_TAC intLib.int_ss 
           [IS_INT_def,complex_rationalTheory.DIVIDES_def,
            sexpTheory.rat_def,ratTheory.rat_0_def,fracTheory.frac_0_def]
    THEN FULL_SIMP_TAC intLib.int_ss 
           [GSYM ratTheory.rat_0_def,GSYM fracTheory.frac_0_def,ratTheory.RAT_0,rat_0_nmr,
            reduced_nmr_0]
    THEN FULL_SIMP_TAC arith_ss 
          [if_t_nil,GSYM t_def, GSYM nil_def,BASIC_INTERN_def,
           reduced_nmr_def,abs_rat_reduce_pos,reduce_int,abs_less,
           GSYM ratTheory.RAT_0,ratTheory.rat_0_def,fracTheory.frac_0_def,
           ratTheory.RAT_ABS_EQUIV,ratTheory.rat_equiv_def]
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,realpart_def,imagpart_def,
           t_def,nil_def,IS_INT_EXISTS,
           complex_def,add_def,mult_def,complex_rationalp_def,
           nat_def,int_def,cpx_def,code_char_def]
    THEN Cases_on `r0 = 0`
    THEN RW_TAC intLib.int_ss []
    THEN ACL2_FULL_SIMP_TAC[]);

(*
     [oracles: DEFAXIOM ACL2::CODE-CHAR-CHAR-CODE-IS-IDENTITY] [axioms: ] []
     |- |= implies (force (characterp c)) (equal (code_char (char_code c)) c),
*)

val code_char_char_code_is_identity_defaxiom =
 store_thm
  ("code_char_char_code_is_identity_defaxiom",
   ``|= implies (force (characterp c)) (equal (code_char (char_code c)) c)``,
   Cases_on `c`
    THEN ACL2_SIMP_TAC[nat_def,int_def,cpx_def,force_def]
    THEN Cases_on `c' = CHR 0`
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC intLib.int_ss 
           [translateTheory.IS_INT_EXISTS,
            sexpTheory.rat_def,ratTheory.rat_0_def,fracTheory.frac_0_def,
            if_t_nil,GSYM t_def, GSYM nil_def,
            reduced_nmr_def,abs_rat_reduce_pos,reduce_int,abs_less,
            stringTheory.char_BIJ,stringTheory.ORD_BOUND,
            arithmeticTheory.DIVMOD_ID,EVAL ``t = nil``]
    THEN `ORD c' < 256` by PROVE_TAC[stringTheory.ORD_BOUND]
    THEN `~(ORD c' = 0)` by METIS_TAC[stringTheory.ORD_CHR,stringTheory.char_BIJ]
    THEN `0 < ORD c'` by DECIDE_TAC
    THEN FULL_SIMP_TAC intLib.int_ss
          [ratTheory.rat_nmr_def,ratTheory.rat_dnm_def,
           fracTheory.frac_nmr_def,fracTheory.frac_dnm_def,if_eq_imp]
    THEN METIS_TAC[]);

(*
     [oracles: DEFAXIOM ACL2::CHAR-CODE-CODE-CHAR-IS-IDENTITY, DISK_THM]
     [axioms: ] []
     |- |= implies
             (andl
                [force (integerp n); force (not (less n (nat 0)));
                 force (less n (nat 256))])
             (equal (char_code (code_char n)) n),
*)

val Num_less =
 if_store_thm
  ("Num_less",
   ``!m n. 0 <= n /\ n < & m ==> Num n < m``,
   REPEAT STRIP_TAC
    THEN `ABS n = n` by intLib.ARITH_TAC
    THEN ONCE_REWRITE_TAC[GSYM integerTheory.INT_LT]
    THEN POP_ASSUM(fn th => ONCE_REWRITE_TAC[GSYM th])
    THEN REWRITE_TAC[and_num_abs]
    THEN Cooper.COOPER_TAC);

val char_code_code_char_is_identity_defaxiom =
 time store_thm
  ("char_code_code_char_is_identity_defaxiom",
   ``|= implies
          (andl
            [force (integerp n); force (not (less n (nat 0)));
             force (less n (nat 256))])
          (equal (char_code (code_char n)) n)``,
   Cases_on `n`
    THEN ACL2_SIMP_TAC[nat_def,int_def,cpx_def,force_def]
    THEN Cases_on `c`
    THEN RW_TAC intLib.int_ss []
    THEN FULL_SIMP_TAC intLib.int_ss 
           [translateTheory.IS_INT_EXISTS,if_eq_imp,
            nat_def,int_def,cpx_def,
            sexp_11,T_NIL,less_def,char_code_def,code_char_def,
            Q.ISPEC `char_code` COND_RAND,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_RID,ratTheory.RAT_0,
           reduced_nmr_def,reduced_dnm_def,
           abs_rat_reduce_pos]
    THEN RW_TAC intLib.int_ss []
    THEN FULL_SIMP_TAC intLib.int_ss 
           [abs_rat_reduce_pos,reduce_int,stringTheory.ORD_CHR_RWT,
           fracTheory.frac_0_def,ratTheory.rat_0,abs_less,
           ratTheory.RAT_ADD_RID,ratTheory.RAT_0]
    THEN TRY(Cooper.COOPER_TAC)
    THEN TRY(METIS_TAC[])
    THEN `Num c' < 256` by PROVE_TAC[Num_less]
    THEN `&(Num c') = c'` by PROVE_TAC[integerTheory.INT_OF_NUM]
    THEN POP_ASSUM
          (fn th => 
            FULL_SIMP_TAC intLib.int_ss 
             [th,stringTheory.ORD_CHR_RWT,integerTheory.INT_OF_NUM]));

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-+, DISK_THM] [axioms: ] []
     |- |= equal (add x y)
             (itel
                [(acl2_numberp x,ite (acl2_numberp y) (add x y) x);
                 (acl2_numberp y,y)] (nat 0)),
*)

val completion_of_plus_defaxiom =
 store_thm
  ("completion_of_plus_defaxiom",
   ``|= equal (add x y)
              (itel
                [(acl2_numberp x,ite (acl2_numberp y) (add x y) x);
                 (acl2_numberp y,y)] (nat 0))``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC [itel_def,int_def,cpx_def,nat_def]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-*, DISK_THM] [axioms: ] []
     |- |= equal (mult x y)
             (ite (acl2_numberp x) (ite (acl2_numberp y) (mult x y) (nat 0))
                (nat 0)),
*)

val completion_of_star_defaxiom =
 store_thm
  ("completion_of_star_defaxiom",
   ``|= equal (mult x y)
              (ite (acl2_numberp x) 
                   (ite (acl2_numberp y) (mult x y) (nat 0))
                   (nat 0))``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC [itel_def,int_def,cpx_def,nat_def]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-UNARY-MINUS, DISK_THM] [axioms: ]
     []
     |- |= equal (unary_minus x)
             (ite (acl2_numberp x) (unary_minus x) (nat 0)),
*)

val completion_of_unary_minus_defaxiom =
 store_thm
  ("completion_of_unary_minus_defaxiom",
   ``|= equal (unary_minus x)
              (ite (acl2_numberp x) (unary_minus x) (nat 0))``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC [itel_def,int_def,cpx_def,nat_def]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-UNARY-/, DISK_THM] [axioms: ] []
     |- |= equal (reciprocal x)
             (ite (andl [acl2_numberp x; not (equal x (nat 0))])
                (reciprocal x) (nat 0)),
*)

val completion_of_unary_slash_defaxiom =
 store_thm
  ("completion_of_unary_slash_defaxiom",
   ``|= equal (reciprocal x)
              (ite (andl [acl2_numberp x; not (equal x (nat 0))])
                   (reciprocal x) 
                   (nat 0))``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC [itel_def,int_def,cpx_def,nat_def]
    THEN FULL_SIMP_TAC std_ss
          [GSYM t_def,GSYM nil_def,if_t_nil,
           com_0_def,ratTheory.RAT_0,sexpTheory.rat_def,
           GSYM ratTheory.rat_0_def,GSYM fracTheory.frac_0_def]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-<, DISK_THM] [axioms: ] []
     |- |= equal (less x y)
             (itel
                [(andl [rationalp x; rationalp y],less x y);
                 (less (realpart (ite (acl2_numberp x) x (nat 0)))
                    (realpart (ite (acl2_numberp y) y (nat 0))),
                  less (realpart (ite (acl2_numberp x) x (nat 0)))
                    (realpart (ite (acl2_numberp y) y (nat 0))))]
                (andl
                   [equal (realpart (ite (acl2_numberp x) x (nat 0)))
                      (realpart (ite (acl2_numberp y) y (nat 0)));
                    less (imagpart (ite (acl2_numberp x) x (nat 0)))
                      (imagpart (ite (acl2_numberp y) y (nat 0)))])),
*)

val completion_of_less_defaxiom =
 time store_thm
  ("completion_of_less_defaxiom",
   ``|= equal (less x y)
              (itel
                [(andl [rationalp x; rationalp y],less x y);
                 (less (realpart (ite (acl2_numberp x) x (nat 0)))
                       (realpart (ite (acl2_numberp y) y (nat 0))),
                  less (realpart (ite (acl2_numberp x) x (nat 0)))
                       (realpart (ite (acl2_numberp y) y (nat 0))))]
                (andl
                  [equal (realpart (ite (acl2_numberp x) x (nat 0)))
                         (realpart (ite (acl2_numberp y) y (nat 0)));
                   less  (imagpart (ite (acl2_numberp x) x (nat 0)))
                         (imagpart (ite (acl2_numberp y) y (nat 0)))]))``,
   Cases_on `x` THEN Cases_on `y`
    THEN TRY(Cases_on `c`)
    THEN TRY(Cases_on `c'`)
    THEN ACL2_SIMP_TAC [itel_def,int_def,cpx_def,nat_def]
    THEN FULL_SIMP_TAC std_ss
          [GSYM t_def,GSYM nil_def,if_t_nil,ratTheory.RAT_LES_REF,
           com_0_def,ratTheory.RAT_0,sexpTheory.rat_def,
           GSYM ratTheory.rat_0_def,GSYM fracTheory.frac_0_def,less_def,
           if_eq_imp]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-CAR, DISK_THM] [axioms: ] []
     |- |= equal (car x) (andl [consp x; car x]),
*)

val completion_of_car_defaxiom =
 store_thm
  ("completion_of_car_defaxiom",
   ``|= equal (car x) (andl [consp x; car x])``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-CDR, DISK_THM] [axioms: ] []
     |- |= equal (cdr x) (andl [consp x; cdr x]),
*)

val completion_of_cdr_defaxiom =
 store_thm
  ("completion_of_cdr_defaxiom",
   ``|= equal (cdr x) (andl [consp x; cdr x])``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-CHAR-CODE, DISK_THM] [axioms: ]
     [] |- |= equal (char_code x) (ite (characterp x) (char_code x) (nat 0)),
*)

val completion_of_char_code_defaxiom =
 store_thm
  ("completion_of_char_code_defaxiom",
   ``|= equal (char_code x) (ite (characterp x) (char_code x) (nat 0))``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[nat_def]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-CODE-CHAR, DISK_THM] [axioms: ]
     []
     |- |= equal (code_char x)
             (ite (andl [integerp x; not (less x (nat 0)); less x (nat 256)])
                (code_char x) (code_char (nat 0))),
*)

val RAT_LEQ_ANTISYM_EQ = (* Not used *)
 if_store_thm
  ("RAT_LEQ_ANTISYM_EQ",
   ``!r1 r2:rat. (r1 = r2) = r1 <= r2 /\ r2 <= r1``,
   REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN RW_TAC std_ss [ratTheory.RAT_LEQ_REF,ratTheory.RAT_LEQ_ANTISYM]);

val completion_of_code_char_defaxiom =
 store_thm
  ("completion_of_code_char_defaxiom",
   ``|= equal 
         (code_char x)
         (ite (andl [integerp x; not (less x (nat 0)); less x (nat 256)])
              (code_char x) 
              (code_char (nat 0)))``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[nat_def,int_def,cpx_def]
    THEN FULL_SIMP_TAC intLib.int_ss 
           [IS_INT_def,complex_rationalTheory.DIVIDES_def,
            sexpTheory.rat_def,ratTheory.rat_0_def,fracTheory.frac_0_def]
    THEN FULL_SIMP_TAC intLib.int_ss 
           [GSYM ratTheory.rat_0_def,GSYM fracTheory.frac_0_def,ratTheory.RAT_0,rat_0_nmr,
            reduced_nmr_0]
    THEN FULL_SIMP_TAC arith_ss 
          [if_t_nil,GSYM t_def, GSYM nil_def,BASIC_INTERN_def]
    THEN Cases_on `c`
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,realpart_def,imagpart_def,
           t_def,nil_def,IS_INT_EXISTS,
           complex_def,add_def,mult_def,complex_rationalp_def,
           nat_def,int_def,cpx_def,
           code_char_def]
    THEN RW_TAC intLib.int_ss []
    THEN FULL_SIMP_TAC intLib.int_ss 
          [reduced_nmr_def,abs_rat_reduce_pos,reduce_int,abs_less,
           GSYM ratTheory.RAT_0,ratTheory.rat_0_def,fracTheory.frac_0_def]
    THEN `~(c < 0)` by Cooper.COOPER_TAC
    THEN METIS_TAC[]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-COMPLEX, DISK_THM] [axioms: ] []
     |- |= equal (complex x y)
             (complex (ite (rationalp x) x (nat 0))
                (ite (rationalp y) y (nat 0))),
*)

val completion_of_complex_defaxiom =
 store_thm
  ("completion_of_complex_defaxiom",
   ``|= equal 
         (complex x y)
         (complex (ite (rationalp x) x (nat 0))
                  (ite (rationalp y) y (nat 0)))``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC[nat_def,int_def,cpx_def]
    THEN FULL_SIMP_TAC intLib.int_ss 
           [IS_INT_def,complex_rationalTheory.DIVIDES_def,
            sexpTheory.rat_def,ratTheory.rat_0_def,fracTheory.frac_0_def]
    THEN FULL_SIMP_TAC intLib.int_ss 
           [GSYM ratTheory.rat_0_def,GSYM fracTheory.frac_0_def,ratTheory.RAT_0,rat_0_nmr,
            reduced_nmr_0]
    THEN FULL_SIMP_TAC arith_ss 
          [if_t_nil,GSYM t_def, GSYM nil_def,BASIC_INTERN_def]
    THEN TRY(Cases_on `c`)
    THEN TRY(Cases_on `c'`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,realpart_def,imagpart_def,
           t_def,nil_def,IS_INT_EXISTS,
           complex_def,add_def,mult_def,complex_rationalp_def,
           nat_def,int_def,cpx_def,
           code_char_def]
    THEN RW_TAC intLib.int_ss []
    THEN Cases_on `r0 = 0`
    THEN RW_TAC intLib.int_ss []
    THEN FULL_SIMP_TAC intLib.int_ss 
          [complex_def,sexp_11,ratTheory.RAT_0]
    THEN Cases_on `r0' = 0`
    THEN RW_TAC intLib.int_ss []
    THEN FULL_SIMP_TAC intLib.int_ss 
          [complex_def,sexp_11,ratTheory.RAT_0]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-COERCE, DISK_THM] [axioms: ] []
     |- |= equal (coerce x y)
             (ite (equal y (csym "LIST"))
                (andl [stringp x; coerce x (csym "LIST")])
                (coerce (acl2_make_character_list x) (csym "STRING"))),
*)

val code_chr_int =
 if_store_thm
  ("code_chr_int",
   ``0 <= n /\ n < 256 ==> (code_char(int n) = chr(CHR(Num n)))``,
   RW_TAC std_ss 
    [int_def,cpx_def,IS_INT_EXISTS,code_char_def,
     sexpTheory.rat_def,reduced_nmr_def]
    THEN FULL_SIMP_TAC intLib.int_ss 
          [abs_rat_reduce_pos,reduce_int,if_eq_imp,sexp_11,
           ratTheory.rat_0_def,fracTheory.frac_0_def]
    THEN METIS_TAC[]);

val coerce_if =
 prove
  (``coerce(if b then x else y) = if b then coerce x else coerce y``,
   RW_TAC std_ss []);

val abs_exists_0 =
 prove
  (``?c. 0 = abs_rat (abs_frac (c,1))``,
   METIS_TAC
    [ratTheory.RAT_0,ratTheory.rat_0_def,fracTheory.frac_0_def]);

val characterp_make_character_list =
 prove
  (``(characterp s = nil)
     ==> 
     (make_character_list(cons s s') = 
       cons (chr(CHR 0)) (make_character_list s'))``,
   Cases_on `s`
    THEN ACL2_SIMP_TAC [make_character_list_def]
    THEN FULL_SIMP_TAC intLib.int_ss [code_chr_int]);

val not_characterp_make_character_list =
 prove
  (``~(characterp s = nil)
     ==> 
     (make_character_list(cons s s') = 
       cons s (make_character_list s'))``,
   Cases_on `s`
    THEN ACL2_SIMP_TAC [make_character_list_def]
    THEN FULL_SIMP_TAC intLib.int_ss [code_chr_int]);

val make_character_list_acl2_make_character_list =
 prove
  (``!s. make_character_list(acl2_make_character_list s) = 
          make_character_list s``,
   Induct
    THEN ACL2_SIMP_TAC[make_character_list_def,nat_def]
    THEN FULL_SIMP_TAC intLib.int_ss 
          [code_chr_int,GSYM nil_def]
    THEN RW_TAC intLib.int_ss 
          [characterp_make_character_list,make_character_list_def,
           not_characterp_make_character_list]);

val completion_of_coerce_defaxiom =
 time store_thm
  ("completion_of_coerce_defaxiom",
   ``|= equal (coerce x y)
              (ite
                (equal y (csym "LIST"))
                (andl [stringp x; coerce x (csym "LIST")])
                (coerce (acl2_make_character_list x) (csym "STRING")))``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC[]
    THEN FULL_SIMP_TAC std_ss 
          [GSYM nil_def,GSYM t_def,if_t_nil,sexp_11]
    THEN FULL_SIMP_TAC std_ss 
          [sexp_11,if_eq_imp,csym_def,COMMON_LISP_def,t_def,nil_def]
    THEN RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss [EVAL ``"STRING" = "LIST"``,coerce_if,coerce_def]
    THEN FULL_SIMP_TAC std_ss [if_eq_imp]
    THEN TRY(Cases_on `s`)
    THEN TRY(Cases_on `s0`)
    THEN FULL_SIMP_TAC intLib.int_ss
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,characterp_def,reduced_nmr_0,
           sexpTheory.rat_def,sexp_11,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,ratTheory.RAT_LES_REF,com_0_def,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,less_def,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_0,eq_imp_if,itel_def,T_NIL,ite_def,
           rationalp_def,integerp_def,numerator_def,denominator_def,
           int_def,cpx_def,realpart_def,imagpart_def,
           t_def,nil_def,IS_INT_EXISTS,
           complex_def,add_def,mult_def,complex_rationalp_def,
           nat_def,int_def,cpx_def,code_char_def,
           make_character_list_def,coerce_list_to_string_def,
           abs_exists_0,acl2_make_character_list,coerce_def,sexp_11,
           EVAL ``"STRING" = "LIST"``]
    THEN RW_TAC intLib.int_ss []
    THEN FULL_SIMP_TAC std_ss [GSYM nil_def]
    THEN Cases_on `characterp s = nil`
    THEN FULL_SIMP_TAC std_ss 
          [characterp_make_character_list,
           not_characterp_make_character_list,
           make_character_list_acl2_make_character_list]
    THEN FULL_SIMP_TAC std_ss 
          [make_character_list_def,
           make_character_list_acl2_make_character_list]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-DENOMINATOR, DISK_THM] [axioms: ]
     []
     |- |= equal (denominator x) (ite (rationalp x) (denominator x) (nat 1)),
*)

val completion_of_denominator_defaxiom =
 store_thm
  ("completion_of_denominator_defaxiom",
   ``|= equal (denominator x) (ite (rationalp x) (denominator x) (nat 1))``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[nat_def]
    THEN Cases_on `c`
    THEN ACL2_FULL_SIMP_TAC[nat_def]
    THEN Cases_on `r0 = rat_0`
    THEN ACL2_FULL_SIMP_TAC[nat_def]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-IMAGPART, DISK_THM] [axioms: ] []
     |- |= equal (imagpart x) (ite (acl2_numberp x) (imagpart x) (nat 0)),
*)

val completion_of_imagpart_defaxiom =
 store_thm
  ("completion_of_imagpart_defaxiom",
   ``|= equal (imagpart x) (ite (acl2_numberp x) (imagpart x) (nat 0))``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[nat_def]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-INTERN-IN-PACKAGE-OF-SYMBOL,
                DISK_THM]
     [axioms: ] []
     |- |= equal (intern_in_package_of_symbol x y)
             (andl [stringp x; symbolp y; intern_in_package_of_symbol x y]),
*)

val completion_of_intern_in_package_of_symbol_defaxiom =
 store_thm
  ("completion_of_intern_in_package_of_symbol_defaxiom",
   ``|= equal (intern_in_package_of_symbol x y)
              (andl [stringp x; symbolp y; intern_in_package_of_symbol x y])``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC[]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-NUMERATOR, DISK_THM] [axioms: ]
     [] |- |= equal (numerator x) (ite (rationalp x) (numerator x) (nat 0)),
*)

val completion_of_numerator_defaxiom =
 store_thm
  ("completion_of_numerator_defaxiom",
   ``|= equal (numerator x) (ite (rationalp x) (numerator x) (nat 0))``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[nat_def]
    THEN Cases_on `c`
    THEN ACL2_FULL_SIMP_TAC[nat_def]
    THEN Cases_on `r0 = rat_0`
    THEN ACL2_FULL_SIMP_TAC[nat_def]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-REALPART, DISK_THM] [axioms: ] []
     |- |= equal (realpart x) (ite (acl2_numberp x) (realpart x) (nat 0)),
*)

val completion_of_realpart_defaxiom =
 store_thm
  ("completion_of_realpart_defaxiom",
   ``|= equal (realpart x) (ite (acl2_numberp x) (realpart x) (nat 0))``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[nat_def]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-SYMBOL-NAME, DISK_THM] [axioms: ]
     []
     |- |= equal (symbol_name x) (ite (symbolp x) (symbol_name x) (str "")),
*)

val completion_of_symbol_name_defaxiom =
 store_thm
  ("completion_of_symbol_name_defaxiom",
   ``|= equal (symbol_name x) (ite (symbolp x) (symbol_name x) (str ""))``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-SYMBOL-PACKAGE-NAME, DISK_THM]
     [axioms: ] []
     |- |= equal (symbol_package_name x)
             (ite (symbolp x) (symbol_package_name x) (str "")),
*)

val completion_of_symbol_package_name_defaxiom =
 store_thm
  ("completion_of_symbol_package_name_defaxiom",
   ``|= equal (symbol_package_name x)
             (ite (symbolp x) (symbol_package_name x) (str ""))``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[]);

(*
     [oracles: DEFAXIOM ACL2::BOOLEANP-BAD-ATOM<=, DISK_THM] [axioms: ] []
     |- |= ite (equal (bad_atom_less_equal x y) t)
             (equal (bad_atom_less_equal x y) t)
             (equal (bad_atom_less_equal x y) nil),
*)

val booleanp_bad_atom_less_equal_defaxiom =
 store_thm
  ("booleanp_bad_atom_less_equal_defaxiom",
   ``|= ite (equal (bad_atom_less_equal x y) t)
            (equal (bad_atom_less_equal x y) t)
            (equal (bad_atom_less_equal x y) nil)``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC[SEXP_SYM_LESS_EQ_def,SEXP_SYM_LESS_def]
    THEN FULL_SIMP_TAC std_ss 
          [GSYM nil_def, GSYM t_def, if_t_nil,
           EVAL ``t = nil``, EVAL ``nil = t``]);

(*
     [oracles: DEFAXIOM ACL2::BAD-ATOM<=-ANTISYMMETRIC, DISK_THM] [axioms: ]
     []
     |- |= implies
             (andl
                [bad_atom x; bad_atom y; bad_atom_less_equal x y;
                 bad_atom_less_equal y x]) (equal x y),
*)

val bad_atom_less_equal_antisymmetric_defaxiom =
 time store_thm
  ("bad_atom_less_equal_antisymmetric_defaxiom",
   ``|= implies
         (andl
            [bad_atom x; bad_atom y; 
             bad_atom_less_equal x y;
             bad_atom_less_equal y x]) 
         (equal x y)``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC[]
    THEN FULL_SIMP_TAC std_ss 
          [GSYM nil_def, GSYM t_def, if_t_nil,itel_def,ite_def,
           EVAL ``t = nil``, EVAL ``nil = t``]
    THEN FULL_SIMP_TAC std_ss 
          [BASIC_INTERN_def,sexp_11,if_t_nil,
           SEXP_SYM_LESS_def,SEXP_SYM_LESS_EQ_def]
    THEN RW_TAC std_ss []
    THEN IMP_RES_TAC STRING_LESS_SYM);

(*
     [oracles: DEFAXIOM ACL2::BAD-ATOM<=-TRANSITIVE, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [bad_atom_less_equal x y; bad_atom_less_equal y z;
                 bad_atom x; bad_atom y; bad_atom z])
             (bad_atom_less_equal x z),
*)

val bad_atom_less_equal_transitive_defaxiom =
 time store_thm
  ("bad_atom_less_equal_transitive_defaxiom",
   ``|= implies
         (andl
           [bad_atom_less_equal x y; 
            bad_atom_less_equal y z;
            bad_atom x; bad_atom y; bad_atom z])
         (bad_atom_less_equal x z)``,
   Cases_on `x` THEN Cases_on `y` THEN Cases_on `z`
    THEN ACL2_SIMP_TAC[]
    THEN FULL_SIMP_TAC std_ss 
          [GSYM nil_def, GSYM t_def, if_t_nil,itel_def,ite_def,
           EVAL ``t = nil``, EVAL ``nil = t``]
    THEN FULL_SIMP_TAC std_ss 
          [BASIC_INTERN_def,sexp_11,if_t_nil,
           SEXP_SYM_LESS_def,SEXP_SYM_LESS_EQ_def]
    THEN RW_TAC std_ss []
    THEN IMP_RES_TAC STRING_LESS_TRANS
    THEN METIS_TAC[]);

(*
     [oracles: DEFAXIOM ACL2::BAD-ATOM<=-TOTAL, DISK_THM] [axioms: ] []
     |- |= implies (andl [bad_atom x; bad_atom y])
             (ite (bad_atom_less_equal x y) (bad_atom_less_equal x y)
                (bad_atom_less_equal y x)),
*)

val bad_atom_less_equal_total_defaxiom =
 time store_thm
  ("bad_atom_less_equal_total_defaxiom",
   ``|= implies
         (andl [bad_atom x; bad_atom y])
         (ite (bad_atom_less_equal x y) 
              (bad_atom_less_equal x y)
              (bad_atom_less_equal y x))``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC[]
    THEN FULL_SIMP_TAC std_ss 
          [GSYM nil_def, GSYM t_def, if_t_nil,andl_def,itel_def,ite_def,
           EVAL ``t = nil``, EVAL ``nil = t``]
    THEN FULL_SIMP_TAC std_ss 
          [BASIC_INTERN_def,sexp_11,if_t_nil,
           SEXP_SYM_LESS_def,SEXP_SYM_LESS_EQ_def]
    THEN FULL_SIMP_TAC list_ss [if_eq_imp,nil_def]
    THEN FULL_SIMP_TAC list_ss [sexp_11]
    THEN RW_TAC std_ss []
    THEN METIS_TAC
          [LOOKUP_NIL,STRING_LESS_TRICHOTOMY,STRING_LESS_ANTISYM,
           EVAL ``"COMMON-LISP" = ""``]);

val _ = export_theory();


