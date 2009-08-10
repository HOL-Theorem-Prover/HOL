structure numScript =
struct

open HolKernel Parse boolLib boolTheory;

infix THEN THENL;

val _ = new_theory "num";

(*---------------------------------------------------------------------------
 * Define successor `SUC_REP:ind->ind` on ind.
 *---------------------------------------------------------------------------*)

val SUC_REP_DEF = new_specification
   ("SUC_REP_DEF",["SUC_REP"], boolTheory.INFINITY_AX);


val ZERO_REP_EXISTS = prove(
  Term`?z. !y. ~(z = SUC_REP y)`,
  Q.X_CHOOSE_THEN `zrep` ASSUME_TAC ((CONV_RULE NOT_FORALL_CONV o
                                      REWRITE_RULE [ONTO_THM] o
                                      CONJUNCT2) SUC_REP_DEF) THEN
  POP_ASSUM (ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV) THEN
  Q.EXISTS_TAC `zrep` THEN POP_ASSUM ACCEPT_TAC);

(*---------------------------------------------------------------------------
 * `ZERO_REP:ind` represents `0:num`
 *---------------------------------------------------------------------------*)

val ZERO_REP_DEF = new_specification
  ("ZERO_REP_DEF",["ZERO_REP"], ZERO_REP_EXISTS);


(*---------------------------------------------------------------------------*)
(* `IS_NUM:ind->bool` defines the subset of `:ind` used to represent 	     *)
(* numbers.  It is the smallest subset containing `ZERO_REP` and closed	     *)
(* under `SUC_REP`.                                                          *)
(*---------------------------------------------------------------------------*)

val IS_NUM_REP = new_definition("IS_NUM_REP",
     --`IS_NUM_REP m =
      !P:ind->bool. (P ZERO_REP /\ (!n. P n ==> P(SUC_REP n))) ==> P m`--);

(*---------------------------------------------------------------------------
 * Prove that there is a representation in :ind of at least one number.
 *---------------------------------------------------------------------------*)

val EXISTS_NUM_REP = TAC_PROOF(([],--`?n. IS_NUM_REP n`--),
     PURE_REWRITE_TAC [IS_NUM_REP] THEN
     EXISTS_TAC (--`ZERO_REP`--) THEN
     REPEAT STRIP_TAC);

(*---------------------------------------------------------------------------
 * Make the type definition.
 *---------------------------------------------------------------------------*)

val num_TY_DEF = new_type_definition ("num", EXISTS_NUM_REP);

val num_ISO_DEF = define_new_type_bijections
                   {name = "num_ISO_DEF",
                    ABS = "ABS_num",
                    REP = "REP_num",
                    tyax =  num_TY_DEF};

val R_11   = prove_rep_fn_one_one num_ISO_DEF
and R_ONTO = prove_rep_fn_onto    num_ISO_DEF
and A_11   = prove_abs_fn_one_one num_ISO_DEF
and A_ONTO = prove_abs_fn_onto    num_ISO_DEF;

(*---------------------------------------------------------------------------
 * Define ZERO.
 *---------------------------------------------------------------------------*)

val zero = mk_var("0", mk_thy_type{Tyop="num",Thy="num",Args=[]});

val ZERO_DEF = new_definition("ZERO_DEF", --`^zero = ABS_num ZERO_REP`--);


(*---------------------------------------------------------------------------
 * Define the successor function on num.
 *---------------------------------------------------------------------------*)

val SUC_DEF = new_definition("SUC_DEF",
 --`SUC m = ABS_num(SUC_REP(REP_num m))`--);

(*---------------------------------------------------------------------------
 * Prove that IS_NUM_REP ZERO_REP.
 *---------------------------------------------------------------------------*)

val IS_NUM_REP_ZERO =
    TAC_PROOF
    (([], --`IS_NUM_REP ZERO_REP`--),
     REWRITE_TAC [IS_NUM_REP] THEN REPEAT STRIP_TAC);

(*---------------------------------------------------------------------------
 * Prove that IS_NUM_REP (SUC_REP x).
 *---------------------------------------------------------------------------*)

val IS_NUM_SUC_REP =
    TAC_PROOF
    (([], --`!i. IS_NUM_REP i ==> IS_NUM_REP (SUC_REP i)`--),
     REWRITE_TAC [IS_NUM_REP] THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC);

val IS_NUM_REP_SUC_REP =
    TAC_PROOF
    (([], --`!n. IS_NUM_REP(SUC_REP(REP_num n))`--),
      GEN_TAC THEN MATCH_MP_TAC IS_NUM_SUC_REP THEN
      REWRITE_TAC [R_ONTO] THEN
      EXISTS_TAC (--`n:num`--) THEN REFL_TAC);

(*---------------------------------------------------------------------------
 * |- !x1 x2. (SUC_REP x1 = SUC_REP x2) ==> (x1 = x2)
 *---------------------------------------------------------------------------*)

val SUC_REP_11 = CONJUNCT1 (REWRITE_RULE [ONE_ONE_THM] SUC_REP_DEF);

(*---------------------------------------------------------------------------
 *  |- !x. ~(SUC_REP x = ZERO_REP)
 *---------------------------------------------------------------------------*)

val NOT_SUC_ZERO = GSYM ZERO_REP_DEF;

(*----------------------------------------------------------------------*)
(* Proof of NOT_SUC : |- !n. ~(SUC n = ZERO)				*)
(* ---------------------------------------------------------------------*)

val NOT_SUC = store_thm("NOT_SUC",
    --`!n. ~(SUC n = 0)`--,
     PURE_REWRITE_TAC [SUC_DEF,ZERO_DEF] THEN GEN_TAC THEN
     MP_TAC (SPECL [--`SUC_REP(REP_num n)`--,--`ZERO_REP`--] A_11) THEN
     REWRITE_TAC [IS_NUM_REP_ZERO,IS_NUM_REP_SUC_REP] THEN
     DISCH_THEN SUBST1_TAC THEN
     MATCH_ACCEPT_TAC NOT_SUC_ZERO);

(* ---------------------------------------------------------------------*)
(* Prove that |-  !m n. (SUC m = SUC n) ==> (m = n)			*)
(* ---------------------------------------------------------------------*)

val INV_SUC = store_thm("INV_SUC",
    --`!m n. (SUC m = SUC n) ==> (m = n)`--,
     REPEAT GEN_TAC THEN REWRITE_TAC [SUC_DEF] THEN
     MP_TAC (SPECL [--`SUC_REP(REP_num m)`--,
                    --`SUC_REP(REP_num n)`--] A_11) THEN
     REWRITE_TAC [IS_NUM_REP_SUC_REP] THEN DISCH_THEN SUBST1_TAC THEN
     DISCH_THEN (MP_TAC o MATCH_MP SUC_REP_11) THEN
     REWRITE_TAC [R_11]);

(* ---------------------------------------------------------------------*)
(* Prove induction theorem.						*)
(* ---------------------------------------------------------------------*)

val ind_lemma1 =
    TAC_PROOF
    (([], --`!P. P ZERO_REP /\ (!i. P i ==> P(SUC_REP i))
                 ==>
	      !i. IS_NUM_REP i ==> P i`--),
     PURE_ONCE_REWRITE_TAC [IS_NUM_REP] THEN
     REPEAT STRIP_TAC THEN RES_TAC);

val lemma =
    TAC_PROOF(([], --`(A ==> (A /\ B)) = (A ==> B)`--),
               ASM_CASES_TAC (--`A:bool`--) THEN ASM_REWRITE_TAC []);

val ind_lemma2 = TAC_PROOF(([],
  --`!P. P ZERO_REP /\ (!i. IS_NUM_REP i /\ P i ==> P(SUC_REP i))
           ==>
         !i. IS_NUM_REP i ==> P i`--),
     GEN_TAC THEN STRIP_TAC THEN
     MP_TAC (SPEC (--`\i. IS_NUM_REP i /\ P i`--) ind_lemma1) THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC [lemma] THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [IS_NUM_REP_ZERO] THEN
     REPEAT STRIP_TAC THEN IMP_RES_TAC IS_NUM_SUC_REP THEN
     RES_TAC);

val lemma1 =
    TAC_PROOF
    (([], --`(!i. IS_NUM_REP i ==> P(ABS_num i)) = (!n. P n)`--),
     EQ_TAC THEN REPEAT STRIP_TAC THENL
     [STRIP_ASSUME_TAC (SPEC (--`n:num`--) A_ONTO) THEN
      RES_TAC THEN ASM_REWRITE_TAC [],
      POP_ASSUM MP_TAC THEN REWRITE_TAC [R_ONTO] THEN
      STRIP_GOAL_THEN (STRIP_THM_THEN SUBST1_TAC) THEN
      ASM_REWRITE_TAC []]);

val INDUCTION = store_thm("INDUCTION",
    --`!P. P 0 /\ (!n. P n ==> P(SUC n)) ==> !n. P n`--,
     GEN_TAC THEN STRIP_TAC THEN
     MP_TAC (SPEC (--`\i. ((P(ABS_num i)):bool)`--) ind_lemma2) THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC [SYM ZERO_DEF,lemma1] THEN
     DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC,
      REWRITE_TAC [R_ONTO] THEN
      GEN_TAC THEN  CONV_TAC ANTE_CONJ_CONV THEN
      DISCH_THEN (STRIP_THM_THEN SUBST1_TAC) THEN
      ASM_REWRITE_TAC [num_ISO_DEF,SYM (SPEC_ALL SUC_DEF)]]);

val _ = export_theory();

end;
