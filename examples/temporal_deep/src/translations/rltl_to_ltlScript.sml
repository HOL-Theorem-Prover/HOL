(* -*- Mode: holscript; -*- ***************************************************)
(*                                                                            *)
(*        Translation from Reset Linear Temporal Logic (RLTL) to LTL          *)
(*                                                                            *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open rltlTheory full_ltlTheory prop_logicTheory pred_setTheory;

open Sanity;

val _ = new_theory "rltl_to_ltl";

val RLTL_TO_LTL_def = Define (* see [1, p.35] *)
  `(RLTL_TO_LTL a r (RLTL_PROP b) = LTL_PROP(P_OR(a, P_AND(b, P_NOT r)))) /\
   (RLTL_TO_LTL a r (RLTL_NOT f) = LTL_NOT(RLTL_TO_LTL r a f)) /\
   (RLTL_TO_LTL a r (RLTL_AND(f1,f2)) =
      LTL_AND(RLTL_TO_LTL a r f1, RLTL_TO_LTL a r f2)) /\
   (RLTL_TO_LTL a r (RLTL_NEXT f) =
      LTL_OR(LTL_PROP a, LTL_AND(LTL_NEXT(RLTL_TO_LTL a r f), LTL_NOT(LTL_PROP r)))) /\
   (RLTL_TO_LTL a r (RLTL_SUNTIL(f1, f2)) =
      LTL_SUNTIL(RLTL_TO_LTL a r f1, RLTL_TO_LTL a r f2)) /\
   (RLTL_TO_LTL a r (RLTL_ACCEPT (f, b)) =
      RLTL_TO_LTL (P_OR(a, P_AND(b, P_NOT(r)))) r f)`;

Theorem RLTL_TO_LTL_REWRITES :
  !a r f1 f2.
    (RLTL_TO_LTL a r (RLTL_OR(f1,f2)) = LTL_OR(RLTL_TO_LTL a r f1, RLTL_TO_LTL a r f2)) /\
    (RLTL_TO_LTL a r (RLTL_IMPL(f1,f2)) = LTL_IMPL(RLTL_TO_LTL r a f1, RLTL_TO_LTL a r f2)) /\
    (RLTL_TO_LTL a r (RLTL_BEFORE(f1,f2)) = LTL_BEFORE(RLTL_TO_LTL a r f1, RLTL_TO_LTL r a f2)) /\
    (RLTL_TO_LTL a r (RLTL_SBEFORE(f1,f2)) = LTL_SBEFORE(RLTL_TO_LTL a r f1, RLTL_TO_LTL r a f2))
Proof
    EVAL_TAC THEN PROVE_TAC[]
QED

Theorem LTL_USED_VARS___RLTL_TO_LTL :
    !f a r. LTL_USED_VARS (RLTL_TO_LTL a r f) =
            (RLTL_USED_VARS f) UNION (P_USED_VARS a) UNION (P_USED_VARS r)
Proof
    INDUCT_THEN rltl_induct ASSUME_TAC
 >> rpt STRIP_TAC
 >| [ SIMP_TAC std_ss [RLTL_TO_LTL_def, LTL_USED_VARS_EVAL, P_USED_VARS_EVAL,
                       RLTL_USED_VARS_def, EXTENSION, IN_UNION] THEN
      PROVE_TAC[],

      ASM_SIMP_TAC std_ss [RLTL_TO_LTL_def, LTL_USED_VARS_def,
                           RLTL_USED_VARS_def] THEN
      SIMP_TAC std_ss [EXTENSION, IN_UNION] THEN
      PROVE_TAC[],


      ASM_SIMP_TAC std_ss [RLTL_TO_LTL_def, LTL_USED_VARS_def,
                           RLTL_USED_VARS_def] THEN
      SIMP_TAC std_ss [EXTENSION, IN_UNION] THEN
      PROVE_TAC[],

      ASM_SIMP_TAC std_ss [RLTL_TO_LTL_def, LTL_USED_VARS_def,
                           RLTL_USED_VARS_def, LTL_OR_def] THEN
      SIMP_TAC std_ss [EXTENSION, IN_UNION] THEN
      PROVE_TAC[],

      ASM_SIMP_TAC std_ss [RLTL_TO_LTL_def, LTL_USED_VARS_def,
                           RLTL_USED_VARS_def] THEN
      SIMP_TAC std_ss [EXTENSION, IN_UNION] THEN
      PROVE_TAC[],

      ASM_SIMP_TAC std_ss [RLTL_TO_LTL_def, LTL_USED_VARS_def,
                           RLTL_USED_VARS_def, P_USED_VARS_EVAL] THEN
      SIMP_TAC std_ss [EXTENSION, IN_UNION] THEN
      PROVE_TAC[] ]
QED

Theorem RLTL_TO_LTL_THM :
    !f v a r t. RLTL_SEM_TIME t v a r f = LTL_SEM_TIME t v (RLTL_TO_LTL a r f)
Proof
    INDUCT_THEN rltl_induct ASSUME_TAC
 >> rpt STRIP_TAC
 >> SIMP_TAC std_ss [LTL_SEM_THM, RLTL_SEM_THM, RLTL_TO_LTL_def, P_SEM_THM]
 >> METIS_TAC []
QED

Theorem RLTL_TO_LTL_THM___KS_SEM :
    !f k. (RLTL_KS_SEM k f = LTL_KS_SEM k (RLTL_TO_LTL P_FALSE P_FALSE f))
Proof
    SIMP_TAC std_ss [RLTL_KS_SEM_def, LTL_KS_SEM_def, RLTL_SEM_def, LTL_SEM_def,
                     RLTL_TO_LTL_THM]
QED

val FUTURE_LTL_TO_RLTL_def = Define
  `(FUTURE_LTL_TO_RLTL (LTL_PROP b) = (RLTL_PROP b)) /\
   (FUTURE_LTL_TO_RLTL (LTL_NOT f) = (RLTL_NOT (FUTURE_LTL_TO_RLTL f))) /\
   (FUTURE_LTL_TO_RLTL (LTL_AND(f1,f2)) =
     (RLTL_AND(FUTURE_LTL_TO_RLTL f1, FUTURE_LTL_TO_RLTL f2))) /\
   (FUTURE_LTL_TO_RLTL (LTL_NEXT f) = (RLTL_NEXT (FUTURE_LTL_TO_RLTL f))) /\
   (FUTURE_LTL_TO_RLTL (LTL_SUNTIL(f1,f2)) =
     (RLTL_SUNTIL(FUTURE_LTL_TO_RLTL f1, FUTURE_LTL_TO_RLTL f2)))`;

Theorem FUTURE_LTL_TO_RLTL_THM :
    !f v t. IS_FUTURE_LTL f ==>
           (LTL_SEM_TIME t v f = RLTL_SEM_TIME t v P_FALSE P_FALSE (FUTURE_LTL_TO_RLTL f))
Proof
    INDUCT_THEN ltl_induct ASSUME_TAC
 >> REPEAT STRIP_TAC
 >> FULL_SIMP_TAC std_ss [LTL_SEM_THM, RLTL_SEM_THM, FUTURE_LTL_TO_RLTL_def,
                          P_SEM_THM, IS_FUTURE_LTL_def]
QED

Theorem IS_RLTL_LTL_THM :
    !f a r. (IS_RLTL_G f = IS_LTL_G (RLTL_TO_LTL a r f)) /\
            (IS_RLTL_F f = IS_LTL_F (RLTL_TO_LTL a r f)) /\
            (IS_RLTL_GF f = IS_LTL_GF (RLTL_TO_LTL a r f)) /\
            (IS_RLTL_FG f = IS_LTL_FG (RLTL_TO_LTL a r f)) /\
            (IS_RLTL_PREFIX f = IS_LTL_PREFIX (RLTL_TO_LTL a r f)) /\
            (IS_RLTL_STREET f = IS_LTL_STREET (RLTL_TO_LTL a r f))
Proof
    INDUCT_THEN rltl_induct STRIP_ASSUME_TAC
 >> REWRITE_TAC [IS_RLTL_THM, IS_LTL_THM, RLTL_TO_LTL_def, LTL_OR_def]
 >> ASM_REWRITE_TAC []
 >> METIS_TAC []
QED

Theorem IS_LTL_RLTL_THM :
    !f. IS_FUTURE_LTL f ==>
       (IS_LTL_G f = IS_RLTL_G (FUTURE_LTL_TO_RLTL f)) /\
       (IS_LTL_F f = IS_RLTL_F (FUTURE_LTL_TO_RLTL f)) /\
       (IS_LTL_GF f = IS_RLTL_GF (FUTURE_LTL_TO_RLTL f)) /\
       (IS_LTL_FG f = IS_RLTL_FG (FUTURE_LTL_TO_RLTL f)) /\
       (IS_LTL_PREFIX f = IS_RLTL_PREFIX (FUTURE_LTL_TO_RLTL f)) /\
       (IS_LTL_STREET f = IS_RLTL_STREET (FUTURE_LTL_TO_RLTL f))
Proof
    INDUCT_THEN ltl_induct STRIP_ASSUME_TAC
 >> FULL_SIMP_TAC std_ss [IS_RLTL_THM, IS_LTL_THM, IS_FUTURE_LTL_def,
                          FUTURE_LTL_TO_RLTL_def, LTL_OR_def]
QED

val _ = export_theory();

(* References:

  [1] Tuerk, T., Schneider, K.: A hierarchy for Accellera's property specification language, (2005).
 *)
