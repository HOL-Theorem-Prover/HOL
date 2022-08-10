(******************************************************************************)
(*                                                                            *)
(*    Translation from Property Specification Language (PSL) to Reset LTL     *)
(*                                                                            *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open FinitePSLPathTheory PSLPathTheory UnclockedSemanticsTheory SyntacticSugarTheory
     LemmasTheory RewritesTheory ModelTheory rltl_to_ltlTheory
     RewritesPropertiesTheory ProjectionTheory SyntacticSugarTheory
     arithmeticTheory psl_lemmataTheory
     listTheory numLib intLib rich_listTheory pred_setTheory prop_logicTheory
     infinite_pathTheory temporal_deep_mixedTheory
     rltlTheory full_ltlTheory tuerk_tacticsLib res_quanTools;

open Sanity;

val _ = intLib.deprecate_int();

val _ = new_theory "psl_to_rltl";

val TRANSLATE_TOP_BOTTOM_def = Define
  `(TRANSLATE_TOP_BOTTOM (t:'prop) (b:'prop) TOP   = (\x.x = t)) /\
   (TRANSLATE_TOP_BOTTOM (t:'prop) (b:'prop) BOTTOM   = (\x.x = b)) /\
   (TRANSLATE_TOP_BOTTOM (t:'prop) (b:'prop) (STATE s) = s)`;

val TRANSLATE_STATE_def = Define
   `TRANSLATE_STATE (STATE s) = s`;

val CONVERT_PATH_PSL_LTL_def = Define
   `CONVERT_PATH_PSL_LTL (t:'prop) (b:'prop) =
     (\p.\n. if (n < LENGTH p) then ((TRANSLATE_TOP_BOTTOM t b) (ELEM p n)) else EMPTY)`;

val CONVERT_PATH_PSL_LTL___NO_TOP_BOT_def = Define
   `CONVERT_PATH_PSL_LTL___NO_TOP_BOT =
     (\p.\n. if (n < LENGTH p) then (TRANSLATE_STATE (ELEM p n)) else EMPTY)`;

val CONVERT_PATH_LTL_PSL_def = Define
   `CONVERT_PATH_LTL_PSL = (\p. INFINITE (\n. STATE (p n)))`;

val BEXP_TO_PROP_LOGIC_def = Define
  `(BEXP_TO_PROP_LOGIC (B_PROP b) = P_PROP b) /\
   (BEXP_TO_PROP_LOGIC (B_TRUE) = P_TRUE) /\
   (BEXP_TO_PROP_LOGIC (B_FALSE) = P_FALSE) /\
   (BEXP_TO_PROP_LOGIC (B_NOT p) = P_NOT (BEXP_TO_PROP_LOGIC p)) /\
   (BEXP_TO_PROP_LOGIC (B_AND (p1, p2)) = P_AND(BEXP_TO_PROP_LOGIC p1,BEXP_TO_PROP_LOGIC p2))`;

val PROP_LOGIC_TO_BEXP_def = Define
  `(PROP_LOGIC_TO_BEXP (P_PROP b) = B_PROP b) /\
   (PROP_LOGIC_TO_BEXP (P_TRUE) = B_TRUE) /\
   (PROP_LOGIC_TO_BEXP (P_NOT p) = B_NOT (PROP_LOGIC_TO_BEXP p)) /\
   (PROP_LOGIC_TO_BEXP (P_AND (p1, p2)) = B_AND(PROP_LOGIC_TO_BEXP p1,PROP_LOGIC_TO_BEXP p2))`;

val PSL_TO_RLTL_def = Define (* see [1, p.31] *)
  `(PSL_TO_RLTL (F_STRONG_BOOL b) = RLTL_PROP (BEXP_TO_PROP_LOGIC b)) /\
   (PSL_TO_RLTL (F_WEAK_BOOL b)   = RLTL_PROP (BEXP_TO_PROP_LOGIC b)) /\
   (PSL_TO_RLTL (F_NOT f)         = RLTL_NOT (PSL_TO_RLTL f)) /\
   (PSL_TO_RLTL (F_AND(f1,f2))    = RLTL_AND(PSL_TO_RLTL f1,PSL_TO_RLTL f2)) /\
   (PSL_TO_RLTL (F_NEXT f)        = RLTL_NEXT(PSL_TO_RLTL f)) /\
   (PSL_TO_RLTL (F_UNTIL(f1,f2))  = RLTL_SUNTIL(PSL_TO_RLTL f1,PSL_TO_RLTL f2)) /\
   (PSL_TO_RLTL (F_ABORT (f,b))   = RLTL_ACCEPT(PSL_TO_RLTL f, BEXP_TO_PROP_LOGIC b))`;

val PSL_TO_LTL_def = Define
   `PSL_TO_LTL f = (RLTL_TO_LTL P_FALSE P_FALSE (PSL_TO_RLTL f))`;

val PSL_TO_LTL_CLOCK_def = Define
   `PSL_TO_LTL_CLOCK c f = (RLTL_TO_LTL P_FALSE P_FALSE (PSL_TO_RLTL (F_CLOCK_COMP c f)))`;

val CONVERT_PATH_PSL_LTL___NO_TOP_BOT_LEMMA =
 store_thm
   ("CONVERT_PATH_PSL_LTL___NO_TOP_BOT_LEMMA",
    ``!v b t. IS_INFINITE_TOP_BOTTOM_FREE_PATH v ==>
              (CONVERT_PATH_PSL_LTL t b v = CONVERT_PATH_PSL_LTL___NO_TOP_BOT v)``,

   SIMP_TAC std_ss [IS_INFINITE_TOP_BOTTOM_FREE_PATH_def,
                    CONVERT_PATH_PSL_LTL_def,
                    CONVERT_PATH_PSL_LTL___NO_TOP_BOT_def] THEN
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
   ASM_SIMP_TAC std_ss [LENGTH_def, LS, ELEM_INFINITE] THEN
   GEN_TAC THEN
   `?s. p x = STATE s` by PROVE_TAC[] THEN
   ASM_SIMP_TAC std_ss [TRANSLATE_STATE_def, TRANSLATE_TOP_BOTTOM_def]);


val CONVERT_PATH_LTL_PSL___IS_INFINITE_TOP_BOTTOM_FREE =
 store_thm
   ("CONVERT_PATH_LTL_PSL___IS_INFINITE_TOP_BOTTOM_FREE",
      ``!p. IS_INFINITE_TOP_BOTTOM_FREE_PATH (CONVERT_PATH_LTL_PSL p)``,

      SIMP_TAC std_ss [IS_INFINITE_TOP_BOTTOM_FREE_PATH_def,
        CONVERT_PATH_LTL_PSL_def, path_11, letter_11]);

val CONVERT_PATH_LTL_PSL___CONVERT_PATH_PSL_LTL =
 store_thm
   ("CONVERT_PATH_LTL_PSL___CONVERT_PATH_PSL_LTL",
      ``(!p. CONVERT_PATH_PSL_LTL___NO_TOP_BOT (CONVERT_PATH_LTL_PSL p) = p) /\
        (!p t b. CONVERT_PATH_PSL_LTL t b (CONVERT_PATH_LTL_PSL p) = p)``,

      SIMP_TAC std_ss [CONVERT_PATH_LTL_PSL_def,
                       CONVERT_PATH_PSL_LTL_def,
                       CONVERT_PATH_PSL_LTL___NO_TOP_BOT_def,
                       LENGTH_def, LS, ELEM_INFINITE,
                       TRANSLATE_STATE_def,
                       TRANSLATE_TOP_BOTTOM_def] THEN
      METIS_TAC[]);


val BEXP_TO_PROP_LOGIC_THM =
 store_thm
  ("BEXP_TO_PROP_LOGIC_THM",
   ``!p s. (P_SEM s (BEXP_TO_PROP_LOGIC p)) = (B_SEM (STATE s) p)``,

   INDUCT_THEN bexp_induct ASSUME_TAC THEN
   ASM_SIMP_TAC std_ss [B_SEM_def, BEXP_TO_PROP_LOGIC_def, P_SEM_THM]
);


val PROP_LOGIC_TO_BEXP_THM =
 store_thm
  ("PROP_LOGIC_TO_BEXP_THM",
   ``!p s. (P_SEM s p) = (B_SEM (STATE s) (PROP_LOGIC_TO_BEXP p))``,

   INDUCT_THEN prop_logic_induct ASSUME_TAC THEN
   ASM_SIMP_TAC std_ss [B_SEM_def, PROP_LOGIC_TO_BEXP_def, P_SEM_THM]
);


val CONVERT_PATH_PSL_LTL_COMPLEMENT =
 store_thm
  ("CONVERT_PATH_PSL_LTL_COMPLEMENT",
   ``!t b f. CONVERT_PATH_PSL_LTL b t (COMPLEMENT f) = CONVERT_PATH_PSL_LTL t b f``,

   SIMP_TAC std_ss [CONVERT_PATH_PSL_LTL_def, COMPLEMENT_def, LENGTH_COMPLEMENT, ELEM_COMPLEMENT] THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   REPEAT STRIP_TAC THEN
   SIMP_TAC std_ss [] THEN
   Cases_on `x < LENGTH f` THENL [
      ASM_SIMP_TAC std_ss [] THEN
      Cases_on `ELEM f x` THEN
      REWRITE_TAC[COMPLEMENT_LETTER_def, TRANSLATE_TOP_BOTTOM_def],

      ASM_SIMP_TAC std_ss []
   ]);



val CONVERT_PATH_PSL_LTL_ELEM_INFINITE =
 store_thm
  ("CONVERT_PATH_PSL_LTL_ELEM_INFINITE",
   ``!p t b t'. ((CONVERT_PATH_PSL_LTL t b (INFINITE p)) t' = TRANSLATE_TOP_BOTTOM t b (p t'))``,

   SIMP_TAC std_ss [LENGTH_def, LESS_def, CONVERT_PATH_PSL_LTL_def, ELEM_INFINITE, LS]);



val CONVERT_PATH_PSL_LTL___NAND_ON_PATH =
 store_thm
  ("CONVERT_PATH_PSL_LTL___NAND_ON_PATH",

   ``!t' t b v. (~(t=b) /\ PATH_PROP_FREE t v /\ PATH_PROP_FREE b v) ==> NAND_ON_PATH_RESTN t' (CONVERT_PATH_PSL_LTL t b v) (P_PROP t) (P_PROP b)``,

   SIMP_TAC std_ss [NAND_ON_PATH_RESTN_def, CONVERT_PATH_PSL_LTL_def] THEN
   REPEAT STRIP_TAC THEN
   Cases_on `t'' < LENGTH v` THENL [
      ASM_REWRITE_TAC [] THEN
      Cases_on `ELEM v t''` THENL [
         ASM_SIMP_TAC std_ss [IN_DEF, TRANSLATE_TOP_BOTTOM_def, P_SEM_def],
         ASM_SIMP_TAC std_ss [IN_DEF, TRANSLATE_TOP_BOTTOM_def, P_SEM_def],

         REWRITE_ALL_TAC [PATH_PROP_FREE_def, TRANSLATE_TOP_BOTTOM_def, P_SEM_def] THEN
         PROVE_TAC[IN_DEF]
      ],

      ASM_REWRITE_TAC [NOT_IN_EMPTY, P_SEM_def]
   ]);



val PSL_TO_RLTL_THM =
 store_thm
  ("PSL_TO_RLTL_THM",
   ``!f v b t. ((IS_INFINITE_PROPER_PATH v) /\ (F_CLOCK_SERE_FREE f) /\ ~(t = b) /\ (PATH_PROP_FREE t v) /\ (PATH_PROP_FREE b v)) ==>
   ((UF_SEM v f) = (RLTL_SEM_TIME 0 (CONVERT_PATH_PSL_LTL t b v) (P_PROP t) (P_PROP b) (PSL_TO_RLTL f)))``,


INDUCT_THEN fl_induct ASSUME_TAC THENL [

   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [IS_INFINITE_PROPER_PATH_def, PSL_TO_RLTL_def, UF_SEM_def, LENGTH_def, GT,
     ELEM_INFINITE, RLTL_SEM_TIME_def, CONVERT_PATH_PSL_LTL_def, LS, BEXP_TO_PROP_LOGIC_THM, P_SEM_THM] THEN
   Cases_on `p 0` THENL [
      ASM_SIMP_TAC std_ss [IN_DEF, CONVERT_PATH_PSL_LTL_def, TRANSLATE_TOP_BOTTOM_def, B_SEM_def],
      ASM_SIMP_TAC std_ss [IN_DEF, CONVERT_PATH_PSL_LTL_def, TRANSLATE_TOP_BOTTOM_def, B_SEM_def],

      ASM_SIMP_TAC std_ss [IN_DEF, CONVERT_PATH_PSL_LTL_def, TRANSLATE_TOP_BOTTOM_def, BEXP_TO_PROP_LOGIC_THM] THEN
      PROVE_TAC[PATH_PROP_FREE_SEM]
   ],


   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [IS_INFINITE_PROPER_PATH_def, PSL_TO_RLTL_def, UF_SEM_def, LENGTH_def, GT,
     ELEM_INFINITE, RLTL_SEM_TIME_def, CONVERT_PATH_PSL_LTL_def, LS, BEXP_TO_PROP_LOGIC_THM, P_SEM_THM,
     xnum_distinct] THEN
   Cases_on `p 0` THENL [
      ASM_SIMP_TAC std_ss [IN_DEF, CONVERT_PATH_PSL_LTL_def, TRANSLATE_TOP_BOTTOM_def, B_SEM_def],
      ASM_SIMP_TAC std_ss [IN_DEF, CONVERT_PATH_PSL_LTL_def, TRANSLATE_TOP_BOTTOM_def, B_SEM_def],

      ASM_SIMP_TAC std_ss [IN_DEF, CONVERT_PATH_PSL_LTL_def, TRANSLATE_TOP_BOTTOM_def, BEXP_TO_PROP_LOGIC_THM] THEN
      PROVE_TAC[PATH_PROP_FREE_SEM]
   ],


   REWRITE_ALL_TAC[UF_SEM_def, PSL_TO_RLTL_def, RLTL_SEM_TIME_def, F_CLOCK_SERE_FREE_def,
      F_CLOCK_FREE_def, F_SERE_FREE_def] THEN
   METIS_TAC[CONVERT_PATH_PSL_LTL_COMPLEMENT, IS_INFINITE_PROPER_PATH___COMPLEMENT, PATH_PROP_FREE_COMPLEMENT],


   REWRITE_ALL_TAC[UF_SEM_def, PSL_TO_RLTL_def, RLTL_SEM_def, RLTL_SEM_TIME_def, F_CLOCK_SERE_FREE_def,
      F_CLOCK_FREE_def, F_SERE_FREE_def] THEN
   METIS_TAC[],


   REWRITE_TAC[F_CLOCK_SERE_FREE_def, F_SERE_FREE_def],
   REWRITE_TAC[F_CLOCK_SERE_FREE_def, F_SERE_FREE_def],


   REPEAT STRIP_TAC THEN
   REWRITE_ALL_TAC[UF_SEM_def, PSL_TO_RLTL_def, RLTL_SEM_THM, F_CLOCK_SERE_FREE_def, F_CLOCK_SERE_FREE_def, F_SERE_FREE_def, F_CLOCK_FREE_def] THEN
   `?p. v = INFINITE p` by METIS_TAC[IS_INFINITE_PROPER_PATH_def] THEN
   ASM_REWRITE_TAC[LENGTH_def, GT, CONVERT_PATH_PSL_LTL_ELEM_INFINITE] THEN
   `ELEM v 0 = p 0` by METIS_TAC[ELEM_INFINITE] THEN
   Cases_on `p 0` THENL [
      `0:num <= 1` by DECIDE_TAC THEN
      `RESTN (INFINITE p) 1 = TOP_OMEGA` by PROVE_TAC [INFINITE_PROPER_PATH___RESTN_TOP_BOTTOM_OMEGA] THEN
      ASM_SIMP_TAC std_ss [TRANSLATE_TOP_BOTTOM_def, IN_DEF, P_SEM_THM, RLTL_SEM_TIME_def] THEN
      PROVE_TAC[UF_SEM___F_CLOCK_SERE_FREE___OMEGA_TOP_BOTTOM, F_CLOCK_SERE_FREE_def],


      `0:num <= 1` by DECIDE_TAC THEN
      `RESTN (INFINITE p) 1 = BOTTOM_OMEGA` by PROVE_TAC [INFINITE_PROPER_PATH___RESTN_TOP_BOTTOM_OMEGA] THEN
      ASM_SIMP_TAC std_ss [TRANSLATE_TOP_BOTTOM_def, IN_DEF, P_SEM_THM, RLTL_SEM_TIME_def] THEN
      PROVE_TAC[UF_SEM___F_CLOCK_SERE_FREE___OMEGA_TOP_BOTTOM, F_CLOCK_SERE_FREE_def],


      `(~f' b) /\ (~f' t)` by PROVE_TAC[PATH_PROP_FREE_def, IN_DEF, LS, LENGTH_def] THEN
      ASM_SIMP_TAC std_ss [P_SEM_def, TRANSLATE_TOP_BOTTOM_def, IN_DEF] THEN
      `1 < LENGTH (INFINITE p)` by EVAL_TAC THEN
      `?v'. v' = RESTN (INFINITE p) 1` by PROVE_TAC[] THEN
      `IS_INFINITE_PROPER_PATH v'` by PROVE_TAC[IS_INFINITE_PROPER_PATH_RESTN] THEN
      `PATH_PROP_FREE t v'` by PROVE_TAC [PATH_PROP_FREE_RESTN] THEN
      `PATH_PROP_FREE b v'` by PROVE_TAC [PATH_PROP_FREE_RESTN] THEN
      `(UF_SEM (RESTN (INFINITE p) 1) f = RLTL_SEM_TIME 0 (CONVERT_PATH_PSL_LTL t b v') (P_PROP t) (P_PROP b) (PSL_TO_RLTL f))` by
         METIS_TAC[] THEN
      ONCE_REWRITE_TAC [RLTL_SEM_TIME___TIME_ELIM] THEN
      ASM_SIMP_TAC arith_ss [CONVERT_PATH_PSL_LTL_def, LENGTH_def, LS, ELEM_INFINITE, RESTN_INFINITE,
        PATH_RESTN_def]
   ],



   REPEAT STRIP_TAC THEN
   SUBGOAL_TAC `(!k. (UF_SEM (RESTN v k) f) = (RLTL_SEM_TIME 0 (CONVERT_PATH_PSL_LTL t b (RESTN v k)) (P_PROP t) (P_PROP b) (PSL_TO_RLTL f))) /\
                (!k. (UF_SEM (RESTN v k) f') = (RLTL_SEM_TIME 0 (CONVERT_PATH_PSL_LTL t b (RESTN v k)) (P_PROP t) (P_PROP b) (PSL_TO_RLTL f')))` THEN1 (
      SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN
      GEN_TAC THEN
      `IS_INFINITE_PROPER_PATH (RESTN v k)` by METIS_TAC[IS_INFINITE_PROPER_PATH_RESTN] THEN
      `F_CLOCK_SERE_FREE f /\ F_CLOCK_SERE_FREE f'` by FULL_SIMP_TAC std_ss [F_CLOCK_SERE_FREE_def, F_SERE_FREE_def, F_CLOCK_FREE_def] THEN
      `k < LENGTH v` by FULL_SIMP_TAC std_ss [LENGTH_def, LS, IS_INFINITE_PROPER_PATH_def] THEN
      `PATH_PROP_FREE t (RESTN v k)` by METIS_TAC[PATH_PROP_FREE_RESTN] THEN
      `PATH_PROP_FREE b (RESTN v k)` by METIS_TAC[PATH_PROP_FREE_RESTN] THEN
      METIS_TAC[]
   ) THEN
   SIMP_ASSUMPTIONS_TAC std_ss [IS_INFINITE_PROPER_PATH_def] THEN
   ASM_SIMP_TAC (std_ss++resq_SS) [CONVERT_PATH_PSL_LTL_def, PSL_TO_RLTL_def, UF_SEM_def, LENGTH_def, LS, IN_LESSX,
    RLTL_SEM_TIME_def, LS, IN_LESSX, ELEM_INFINITE, IN_LESS, RESTN_INFINITE] THEN
   ONCE_REWRITE_TAC [RLTL_SEM_TIME___TIME_ELIM] THEN
   SIMP_TAC std_ss [PATH_RESTN_def],


   REPEAT STRIP_TAC THEN
   `?p. v = INFINITE p` by METIS_TAC[IS_INFINITE_PROPER_PATH_def] THEN
   FULL_SIMP_TAC (std_ss++resq_SS) [PSL_TO_RLTL_def, UF_SEM_def, LENGTH_def, IN_LESSX,
     ELEM_INFINITE, F_CLOCK_SERE_FREE_def, F_CLOCK_FREE_def, F_SERE_FREE_def, RLTL_SEM_TIME_def] THEN
   Cases_on `UF_SEM (INFINITE p) f` THENL [
      ASM_REWRITE_TAC[] THEN
      `RLTL_SEM_TIME 0 (CONVERT_PATH_PSL_LTL t b v) (P_PROP t) (P_PROP b) (PSL_TO_RLTL f)` by METIS_TAC[] THEN

      `NAND_ON_PATH_RESTN 0 (CONVERT_PATH_PSL_LTL t b v) (P_PROP t) (P_PROP b)` by
         METIS_TAC[CONVERT_PATH_PSL_LTL___NAND_ON_PATH] THEN
      `NAND_ON_PATH_RESTN 0 (CONVERT_PATH_PSL_LTL t b v) (P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b))) (P_PROP b)` by
      (REWRITE_TAC [NAND_ON_PATH_RESTN_def, P_SEM_THM]   THEN METIS_TAC[]) THEN

      METIS_TAC [RLTL_SEM_TIME___ACCEPT_OR_THM, RLTL_SEM_def],




      `~RLTL_SEM_TIME 0 (CONVERT_PATH_PSL_LTL t b (INFINITE p)) (P_PROP t) (P_PROP b) (PSL_TO_RLTL f)` by METIS_TAC[RLTL_SEM_def] THEN
      ASM_REWRITE_TAC[] THEN
      EQ_TAC THENL [
         REPEAT STRIP_TAC THEN
         Cases_on `j = 0` THENL [
            REMAINS_TAC `(P_SEM ((CONVERT_PATH_PSL_LTL t b v) 0) (BEXP_TO_PROP_LOGIC p_2)) /\
                        ~(P_SEM ((CONVERT_PATH_PSL_LTL t b v) 0) (P_PROP b))` THEN1 (
              METIS_TAC[RLTL_ACCEPT_REJECT_THM, P_SEM_THM]
            ) THEN

            Cases_on `p 0` THENL [
              `!t:num. 0 <= t` by DECIDE_TAC THEN
              `v = TOP_OMEGA` by METIS_TAC [INFINITE_PROPER_PATH___RESTN_TOP_BOTTOM_OMEGA, RESTN_def, ELEM_INFINITE] THEN
              METIS_TAC[UF_SEM___F_CLOCK_SERE_FREE___OMEGA_TOP_BOTTOM, TOP_OMEGA_def],

              FULL_SIMP_TAC std_ss [B_SEM_def],

              FULL_SIMP_TAC std_ss [B_SEM_def, BEXP_TO_PROP_LOGIC_THM, TRANSLATE_TOP_BOTTOM_def,
                CONVERT_PATH_PSL_LTL_def, LENGTH_def, LS, ELEM_INFINITE, P_SEM_def, IN_DEF] THEN
              PROVE_TAC[PATH_PROP_FREE_SEM]
            ],


            (*Case ~(j = 0)*)
            `?v'. (CAT (SEL v (0,j - 1),TOP_OMEGA)) = v'` by METIS_TAC[] THEN
            FULL_SIMP_TAC std_ss [] THEN
            SUBGOAL_TAC `RLTL_EQUIV_PATH_STRONG 0 (CONVERT_PATH_PSL_LTL t b v) (CONVERT_PATH_PSL_LTL t b v') (P_OR (P_PROP t, P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b)))) (P_PROP b)` THEN1 (

               `LENGTH v' = INFINITY` by PROVE_TAC[LENGTH_CAT_SEL_TOP_OMEGA] THEN
               ASM_SIMP_TAC std_ss [RLTL_EQUIV_PATH_STRONG_def, CONVERT_PATH_PSL_LTL_def, LENGTH_def, LS] THEN

               SUBGOAL_THEN ``ELEM v' j = TOP`` ASSUME_TAC THEN1(
                  `j > j-1` by DECIDE_TAC THEN
                  `!x. ELEM TOP_OMEGA x = TOP` by REWRITE_TAC [TOP_OMEGA_def, ELEM_INFINITE] THEN
                  METIS_TAC [ELEM_CAT_SEL___GREATER]
               ) THEN

               SUBGOAL_THEN ``!l:num. l < j:num ==> ((ELEM (v':'a letter path) l) = (ELEM v l))`` ASSUME_TAC THEN1 (
                  REPEAT STRIP_TAC THEN
                  `l <= j-1` by DECIDE_TAC THEN
                  METIS_TAC[ELEM_CAT_SEL___LESS_EQ]
               ) THEN

               EXISTS_TAC ``j:num`` THEN
               ASM_SIMP_TAC std_ss [TRANSLATE_TOP_BOTTOM_def, IN_DEF, ELEM_INFINITE, P_SEM_THM] THEN

               Cases_on `p j` THENL [
                  ASM_SIMP_TAC std_ss [TRANSLATE_TOP_BOTTOM_def],
                  REWRITE_ASSUMPTIONS_TAC [B_SEM_def],

                  FULL_SIMP_TAC std_ss [TRANSLATE_TOP_BOTTOM_def, BEXP_TO_PROP_LOGIC_THM] THEN
                  METIS_TAC[PATH_PROP_FREE_SEM, IN_DEF]
               ]
            ) THEN


            SUBGOAL_TAC `RLTL_SEM_TIME 0 (CONVERT_PATH_PSL_LTL t b v') (P_PROP t) (P_PROP b) (PSL_TO_RLTL f)` THEN1 (
               `~(ELEM v j = BOTTOM)` by METIS_TAC[B_SEM_def, ELEM_INFINITE] THEN
               `IS_INFINITE_PROPER_PATH v'` by METIS_TAC[IS_INFINITE_PROPER_PATH___CAT_SEL_TOP_OMEGA] THEN
               `?p. INFINITE p = v` by METIS_TAC[IS_INFINITE_PROPER_PATH_def] THEN
               `PATH_PROP_FREE t v'` by METIS_TAC[PATH_PROP_FREE___CAT_SEL_INFINITE___IMPLIES] THEN
               `PATH_PROP_FREE b v'` by METIS_TAC[PATH_PROP_FREE___CAT_SEL_INFINITE___IMPLIES] THEN

               METIS_TAC[]
            ) THEN

            SUBGOAL_TAC `IMP_ON_PATH_RESTN 0 (CONVERT_PATH_PSL_LTL t b v') (P_PROP t) (P_OR
                (P_PROP t,P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b))))` THEN1 (
                REWRITE_TAC[IMP_ON_PATH_RESTN_def, P_SEM_THM] THEN
                METIS_TAC[]
            ) THEN


            `RLTL_SEM_TIME 0 (CONVERT_PATH_PSL_LTL t b v')
               (P_OR (P_PROP t,P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b))))
               (P_PROP b) (PSL_TO_RLTL f)` by
                  METIS_TAC[RLTL_SEM_TIME___ACCEPT_REJECT_IMP_ON_PATH, RLTL_SEM_def] THEN
            METIS_TAC[RLTL_EQUIV_PATH_STRONG_THM]
         ],




         `NAND_ON_PATH_RESTN 0 (CONVERT_PATH_PSL_LTL t b (INFINITE p)) (P_PROP t) (P_PROP b)` by METIS_TAC[CONVERT_PATH_PSL_LTL___NAND_ON_PATH] THEN
         `NAND_ON_PATH_RESTN 0 (CONVERT_PATH_PSL_LTL t b (INFINITE p)) (P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b))) (P_PROP b)` by   (REWRITE_TAC [NAND_ON_PATH_RESTN_def, P_SEM_THM]   THEN METIS_TAC[]) THEN

         ASM_SIMP_TAC std_ss [RLTL_SEM_TIME___ACCEPT_OR_THM] THEN
         REPEAT STRIP_TAC THEN

         SUBGOAL_TAC `?j. (P_SEM ((CONVERT_PATH_PSL_LTL t b v) j) (P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b)))) /\
            !j'. (j' < j) ==> (~(P_SEM ((CONVERT_PATH_PSL_LTL t b v) j') (P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b)))) /\ ~(P_SEM ((CONVERT_PATH_PSL_LTL t b v) j') (P_PROP t)))` THEN1 (

            `IS_ON_PATH_RESTN 0 (CONVERT_PATH_PSL_LTL t b v) (P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b)))` by METIS_TAC[RLTL_SEM_TIME___ACCEPT_REJECT_IS_ON_PATH] THEN
            SIMP_ASSUMPTIONS_TAC std_ss [IS_ON_PATH_RESTN_def, NOT_ON_PATH_RESTN_def] THEN

            `?j. P_SEM (CONVERT_PATH_PSL_LTL t b v j) (P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b))) /\
                  !j'. j' < j ==>  ~P_SEM (CONVERT_PATH_PSL_LTL t b v j') (P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b)))` by
            METIS_TAC [EXISTS_LEAST_CONV ``?j. P_SEM (CONVERT_PATH_PSL_LTL t b v j) (P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b)))``] THEN

            EXISTS_TAC ``j:num`` THEN
            ASM_SIMP_TAC std_ss [] THEN
            `BEFORE_ON_PATH_RESTN_STRONG 0 (CONVERT_PATH_PSL_LTL t b v) (P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b))) (P_PROP t)` by METIS_TAC[RLTL_SEM_TIME___ACCEPT_REJECT_BEFORE_ON_PATH_STRONG] THEN

            CCONTR_TAC THEN
            SIMP_ASSUMPTIONS_TAC std_ss [BEFORE_ON_PATH_RESTN_STRONG_def] THEN
            `?u. u < j' /\
               P_SEM (CONVERT_PATH_PSL_LTL t b v u)
                 (P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b)))` by METIS_TAC[] THEN
            `u < j` by DECIDE_TAC THEN
            METIS_TAC[]) THEN

         SIMP_ASSUMPTIONS_TAC std_ss [P_SEM_THM] THEN
         EXISTS_TAC ``j:num`` THEN
         REPEAT STRIP_TAC THENL [
            Cases_on `p j` THENL [
               REWRITE_TAC [B_SEM_def],

               UNDISCH_TAC ``~(b IN CONVERT_PATH_PSL_LTL t b v j)`` THEN
               ASM_SIMP_TAC std_ss [CONVERT_PATH_PSL_LTL_def, IN_DEF, TRANSLATE_TOP_BOTTOM_def, LENGTH_def, LS, ELEM_INFINITE],

               UNDISCH_TAC ``P_SEM (CONVERT_PATH_PSL_LTL t b v j)
                  (BEXP_TO_PROP_LOGIC p_2)`` THEN
               ASM_SIMP_TAC std_ss [CONVERT_PATH_PSL_LTL_def, TRANSLATE_TOP_BOTTOM_def, BEXP_TO_PROP_LOGIC_THM, LS,
                 LENGTH_def, LESS_def, ELEM_INFINITE]
            ],


            Cases_on `j=0` THEN ASM_REWRITE_TAC[] THEN1 (
               METIS_TAC[UF_SEM___F_CLOCK_SERE_FREE___OMEGA_TOP_BOTTOM, F_CLOCK_SERE_FREE_def]
            ) THEN

            `?v'. (CAT (SEL (INFINITE p) (0,j - 1),TOP_OMEGA)) = v'` by METIS_TAC[] THEN
            SUBGOAL_TAC `~(ELEM v j = BOTTOM)` THEN1 (
               UNDISCH_TAC ``~(b IN CONVERT_PATH_PSL_LTL t b v j)`` THEN
               Cases_on `p j` THEN
               ASM_SIMP_TAC std_ss [CONVERT_PATH_PSL_LTL_def, IN_DEF, TRANSLATE_TOP_BOTTOM_def, ELEM_INFINITE,
                 letter_distinct, LENGTH_def, LS]
            ) THEN
            SUBGOAL_TAC `UF_SEM v' f = RLTL_SEM_TIME 0 (CONVERT_PATH_PSL_LTL t b v') (P_PROP t) (P_PROP b) (PSL_TO_RLTL f)` THEN1 (
               `IS_INFINITE_PROPER_PATH v'` by METIS_TAC[IS_INFINITE_PROPER_PATH___CAT_SEL_TOP_OMEGA] THEN
               `PATH_PROP_FREE t v'` by METIS_TAC[PATH_PROP_FREE___CAT_SEL_INFINITE___IMPLIES] THEN
               `PATH_PROP_FREE b v'` by METIS_TAC[PATH_PROP_FREE___CAT_SEL_INFINITE___IMPLIES] THEN

               METIS_TAC[]
            ) THEN
            ASM_REWRITE_TAC[] THEN

            `!k:num. k < LENGTH v'` by METIS_TAC [LENGTH_CAT_SEL_TOP_OMEGA, LS, IS_INFINITE_PROPER_PATH_def] THEN
            SUBGOAL_TAC `RLTL_EQUIV_PATH_STRONG 0 (CONVERT_PATH_PSL_LTL t b v) (CONVERT_PATH_PSL_LTL t b v') (P_OR (P_PROP t, P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b)))) (P_PROP b)` THEN1 (

               ASM_SIMP_TAC std_ss [RLTL_EQUIV_PATH_STRONG_def, CONVERT_PATH_PSL_LTL_def, LENGTH_def, LS] THEN

               SUBGOAL_TAC `ELEM v' j = TOP` THEN1(
                  `j > j-1` by DECIDE_TAC THEN
                  `!x. ELEM TOP_OMEGA x = TOP` by REWRITE_TAC [TOP_OMEGA_def, ELEM_INFINITE] THEN
                  METIS_TAC [ELEM_CAT_SEL___GREATER]
               ) THEN

               SUBGOAL_TAC `!l:num. l < j:num ==> ((ELEM (v':'a letter path) l) = (ELEM v l))` THEN1 (
                  REPEAT STRIP_TAC THEN
                  `l <= j-1` by DECIDE_TAC THEN
                  METIS_TAC[ELEM_CAT_SEL___LESS_EQ]
               ) THEN

               EXISTS_TAC ``j:num`` THEN
               ASM_SIMP_TAC std_ss [TRANSLATE_TOP_BOTTOM_def, IN_DEF, ELEM_INFINITE, P_SEM_THM,
                BEXP_TO_PROP_LOGIC_THM] THEN

               Cases_on `p j` THENL [
                  ASM_SIMP_TAC std_ss [TRANSLATE_TOP_BOTTOM_def],
                  METIS_TAC[ELEM_INFINITE],

                  SUBGOAL_TAC `B_SEM (STATE (TRANSLATE_TOP_BOTTOM t b (STATE f'))) p_2` THEN1(
                     UNDISCH_TAC ``P_SEM (CONVERT_PATH_PSL_LTL t b v j) (BEXP_TO_PROP_LOGIC p_2)`` THEN
                     ASM_SIMP_TAC std_ss [CONVERT_PATH_PSL_LTL_def, LENGTH_def, LS, ELEM_INFINITE, BEXP_TO_PROP_LOGIC_THM]
                  ) THEN
                  FULL_SIMP_TAC std_ss [TRANSLATE_TOP_BOTTOM_def] THEN
                  METIS_TAC[PATH_PROP_FREE_SEM]
               ]
            ) THEN

            SUBGOAL_TAC `RLTL_SEM_TIME 0 (CONVERT_PATH_PSL_LTL t b v')
               (P_OR(P_PROP t, (P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b))))) (P_PROP b)
               (PSL_TO_RLTL f)` THEN1 (

               `IMP_ON_PATH_RESTN 0 (CONVERT_PATH_PSL_LTL t b v) (P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b))) (P_OR(P_PROP t, (P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b)))))` by
               (REWRITE_TAC[IMP_ON_PATH_RESTN_def, P_SEM_THM] THEN METIS_TAC[]) THEN
               METIS_TAC[RLTL_SEM_TIME___ACCEPT_REJECT_IMP_ON_PATH, RLTL_EQUIV_PATH_STRONG_THM]) THEN

            SUBGOAL_TAC `IMP_ON_PATH_RESTN 0 (CONVERT_PATH_PSL_LTL t b v') (P_OR(P_PROP t, (P_AND (BEXP_TO_PROP_LOGIC p_2,P_NOT (P_PROP b))))) (P_PROP t)` THEN1 (
               REWRITE_TAC[IMP_ON_PATH_RESTN_def, P_SEM_THM] THEN
               REPEAT STRIP_TAC THEN
               Cases_on `t' <= j-1` THENL [
                  SUBGOAL_TAC `CONVERT_PATH_PSL_LTL t b v' t' = CONVERT_PATH_PSL_LTL t b v t'` THEN1 (
                     ASM_SIMP_TAC std_ss [CONVERT_PATH_PSL_LTL_def, LENGTH_def, LS] THEN
                     METIS_TAC[ELEM_CAT_SEL___LESS_EQ]
                  ) THEN
                  `t' < j` by DECIDE_TAC THEN
                  METIS_TAC[],


                  SUBGOAL_TAC `ELEM v' t' = TOP` THEN1 (
                     `t' > j-1` by DECIDE_TAC THEN
                     `ELEM v' t' = ELEM (TOP_OMEGA) (t' - (SUC (j-1)))` by
                        METIS_TAC[ELEM_CAT_SEL___GREATER] THEN
                     ASM_SIMP_TAC std_ss [TOP_OMEGA_def, ELEM_INFINITE]
                  ) THEN
                  ASM_SIMP_TAC std_ss [CONVERT_PATH_PSL_LTL_def, IN_DEF, TRANSLATE_TOP_BOTTOM_def]
               ]
            ) THEN

            METIS_TAC [RLTL_SEM_TIME___ACCEPT_REJECT_IMP_ON_PATH]
         ]
      ]
   ],


   REWRITE_TAC[F_CLOCK_SERE_FREE_def, F_CLOCK_FREE_def],
   REWRITE_TAC[F_CLOCK_SERE_FREE_def, F_SERE_FREE_def]
]);



val P_USED_VARS___BEXP_TO_PROP_LOGIC =
 store_thm
  ("P_USED_VARS___BEXP_TO_PROP_LOGIC",
  ``!b. P_USED_VARS (BEXP_TO_PROP_LOGIC b) = B_USED_VARS b``,

  INDUCT_THEN bexp_induct ASSUME_TAC THEN (
    ASM_SIMP_TAC std_ss [P_USED_VARS_def, BEXP_TO_PROP_LOGIC_def,
                    B_USED_VARS_def, P_FALSE_def]
  ));


val RLTL_USED_VARS___PSL_TO_RLTL =
 store_thm
  ("RLTL_USED_VARS___PSL_TO_RLTL",
  ``!f. F_CLOCK_SERE_FREE f ==>
    (RLTL_USED_VARS (PSL_TO_RLTL f) = F_USED_VARS f)``,

REWRITE_TAC[F_CLOCK_SERE_FREE_def] THEN
INDUCT_THEN fl_induct ASSUME_TAC THEN (
  ASM_SIMP_TAC std_ss [RLTL_USED_VARS_def,
                   F_USED_VARS_def,
                   F_CLOCK_FREE_def, F_SERE_FREE_def,
                   PSL_TO_RLTL_def, P_USED_VARS___BEXP_TO_PROP_LOGIC]
));



val PSL_TO_RLTL___F_USED_VARS =
 store_thm
  ("PSL_TO_RLTL___F_USED_VARS",
   ``!f v b t. ((IS_INFINITE_PROPER_PATH v) /\ (F_CLOCK_SERE_FREE f) /\ ~(t = b) /\ (~(t IN F_USED_VARS f)) /\ (~(b IN F_USED_VARS f))) ==>
   ((UF_SEM v f) = (RLTL_SEM_TIME 0 (CONVERT_PATH_PSL_LTL t b (PATH_LETTER_RESTRICT (F_USED_VARS f) v)) (P_PROP t) (P_PROP b) (PSL_TO_RLTL f)))``,

  REPEAT STRIP_TAC THEN
  `?w. w = PATH_LETTER_RESTRICT ((F_USED_VARS f)) v` by METIS_TAC[] THEN
  `UF_SEM v f = UF_SEM w f` by
    PROVE_TAC[F_USED_VARS_INTER_SUBSET_THM, SUBSET_REFL, F_CLOCK_SERE_FREE_def] THEN
  SUBGOAL_TAC `PATH_PROP_FREE t w /\ PATH_PROP_FREE b w` THEN1 (
      ASM_SIMP_TAC std_ss [PATH_PROP_FREE_def,
        PATH_LETTER_RESTRICT_def, LENGTH_PATH_MAP, ELEM_PATH_MAP, GT_LS,
        GSYM FORALL_AND_THM] THEN
      REPEAT GEN_TAC THEN
      Cases_on `ELEM v n` THEN (
        SIMP_TAC std_ss [LETTER_RESTRICT_def, letter_distinct, letter_11] THEN
        PROVE_TAC[IN_INTER]
      )
  ) THEN


  SUBGOAL_TAC `IS_INFINITE_PROPER_PATH w` THEN1 (
    SIMP_ALL_TAC std_ss [IS_INFINITE_PROPER_PATH_def] THEN
    ASM_SIMP_TAC std_ss [PATH_LETTER_RESTRICT_def, psl_lemmataTheory.PATH_MAP_def, path_11,
      LETTER_RESTRICT_Cases]
  ) THEN

  ASSUME_TAC PSL_TO_RLTL_THM THEN
  Q_SPECL_NO_ASSUM 0 [`f`, `w`, `b`, `t`] THEN
  UNDISCH_HD_TAC THEN
  ASM_SIMP_TAC std_ss []);


val PSL_TO_RLTL___ELIM_ACCEPT_REJECT_THM =
 store_thm
  ("PSL_TO_RLTL___ELIM_ACCEPT_REJECT_THM",
   ``!f v b t. ((IS_INFINITE_PROPER_PATH v) /\ ~(t = b) /\ (PATH_PROP_FREE t v) /\ (PATH_PROP_FREE b v)) ==>
    (RLTL_SEM (CONVERT_PATH_PSL_LTL t b v) (RLTL_ACCEPT (RLTL_REJECT (f,P_PROP b), P_PROP t)) = (RLTL_SEM_TIME 0 (CONVERT_PATH_PSL_LTL t b v) (P_PROP t) (P_PROP b) f))``,

   REPEAT STRIP_TAC THEN
   SIMP_TAC std_ss [RLTL_SEM_def, RLTL_SEM_TIME_def, RLTL_REJECT_def] THEN

   REMAINS_TAC `(EQUIV_ON_PATH_RESTN 0 (CONVERT_PATH_PSL_LTL t b v) (P_OR (P_FALSE,P_AND (P_PROP t,P_NOT P_FALSE))) (P_PROP t)) /\
                (EQUIV_ON_PATH_RESTN 0 (CONVERT_PATH_PSL_LTL t b v) (P_OR (P_FALSE, P_AND (P_PROP b, P_NOT (P_OR (P_FALSE,P_AND (P_PROP t,P_NOT P_FALSE)))))) (P_PROP b))`  THEN1 (
      METIS_TAC[RLTL_SEM_TIME___ACCEPT_REJECT_EQUIV_ON_PATH]
   ) THEN

   `NAND_ON_PATH_RESTN 0 (CONVERT_PATH_PSL_LTL t b v) (P_PROP t) (P_PROP b)` by PROVE_TAC[CONVERT_PATH_PSL_LTL___NAND_ON_PATH] THEN
   FULL_SIMP_TAC std_ss [NAND_ON_PATH_RESTN_def, EQUIV_ON_PATH_RESTN_def, P_SEM_THM] THEN
   PROVE_TAC[]);


val PSL_TO_RLTL___CLOCKED_THM =
 store_thm
  ("PSL_TO_RLTL___CLOCKED_THM",
   ``!f v b t c. ((IS_INFINITE_PROPER_PATH v) /\ (F_SERE_FREE f) /\ ~(t = b) /\
                  (PATH_PROP_FREE t v) /\ (PATH_PROP_FREE b v)) ==>
     ((F_SEM v c f) = (RLTL_SEM_TIME 0 (CONVERT_PATH_PSL_LTL t b v) (P_PROP t) (P_PROP b) (PSL_TO_RLTL (F_CLOCK_COMP c f))))``,

   PROVE_TAC[PSL_TO_RLTL_THM, F_CLOCK_COMP_CORRECT, F_CLOCK_SERE_FREE_def,
             F_SERE_FREE___IMPLIES___F_SERE_FREE_F_CLOCK_COMP,
             F_CLOCK_FREE___F_CLOCK_COMP]);


val P_VAR_RENAMING___BEXP_TO_PROP_LOGIC =
 store_thm
  ("P_VAR_RENAMING___BEXP_TO_PROP_LOGIC",

    ``!f g. P_VAR_RENAMING g (BEXP_TO_PROP_LOGIC f) =
        BEXP_TO_PROP_LOGIC (B_VAR_RENAMING g f)``,

INDUCT_THEN bexp_induct ASSUME_TAC THEN (
    ASM_SIMP_TAC std_ss [BEXP_TO_PROP_LOGIC_def,
                               P_VAR_RENAMING_def,
                               B_VAR_RENAMING_def,
                               P_FALSE_def]
))

val RLTL_VAR_RENAMING___PSL_TO_RLTL =
 store_thm
  ("RLTL_VAR_RENAMING___PSL_TO_RLTL",

    ``!f g.  F_CLOCK_SERE_FREE f ==> (
        RLTL_VAR_RENAMING g (PSL_TO_RLTL f) =
        PSL_TO_RLTL (F_VAR_RENAMING g f))``,

    INDUCT_THEN fl_induct ASSUME_TAC THEN (
        ASM_SIMP_TAC std_ss [PSL_TO_RLTL_def, RLTL_VAR_RENAMING_def,
                                    PSL_TO_RLTL_def, F_VAR_RENAMING_def,
                                    P_VAR_RENAMING___BEXP_TO_PROP_LOGIC,
                                    F_CLOCK_SERE_FREE_def, F_CLOCK_FREE_def,
                                    F_SERE_FREE_def]
    ));




(*Prove the semantic with additional variables t and b first, then
   move to a universe, where enough variables exist and eliminate t and b*)
val PSL_TO_RLTL___NO_TOP_BOT_THM___WITH_T_B =
 prove (
   ``!f t b v. (IS_INFINITE_TOP_BOTTOM_FREE_PATH v) /\ (F_CLOCK_SERE_FREE f) /\ ~(t = b) /\ (PATH_PROP_FREE t v) /\ (PATH_PROP_FREE b v)==>
    ((UF_SEM v f) = RLTL_SEM (CONVERT_PATH_PSL_LTL___NO_TOP_BOT v) (PSL_TO_RLTL f))``,

    REPEAT STRIP_TAC THEN
    `IS_INFINITE_PROPER_PATH v` by PROVE_TAC[IS_INFINITE_TOP_BOTTOM_FREE_PATH___IMPLIES___IS_INFINITE_PROPER_PATH] THEN
    `CONVERT_PATH_PSL_LTL___NO_TOP_BOT v = CONVERT_PATH_PSL_LTL t b v` by
      PROVE_TAC[CONVERT_PATH_PSL_LTL___NO_TOP_BOT_LEMMA] THEN
    `UF_SEM v f = RLTL_SEM_TIME 0 (CONVERT_PATH_PSL_LTL t b v) (P_PROP t) (P_PROP b) (PSL_TO_RLTL f)` by
      PROVE_TAC[PSL_TO_RLTL_THM] THEN
    ASM_REWRITE_TAC[RLTL_SEM_def] THEN
    REMAINS_TAC `(EQUIV_ON_PATH_RESTN 0 (CONVERT_PATH_PSL_LTL t b (v:'a letter path)) (P_PROP t) P_FALSE) /\
                 (EQUIV_ON_PATH_RESTN 0 (CONVERT_PATH_PSL_LTL t b (v:'a letter path)) (P_PROP b) P_FALSE)` THEN1 (
      PROVE_TAC[RLTL_SEM_TIME___ACCEPT_REJECT_EQUIV_ON_PATH]
    ) THEN

    FULL_SIMP_TAC arith_ss [EQUIV_ON_PATH_RESTN_def, GSYM FORALL_AND_THM, CONVERT_PATH_PSL_LTL_def, IS_INFINITE_TOP_BOTTOM_FREE_PATH_def,
      LENGTH_def, LS, P_SEM_THM, ELEM_INFINITE] THEN
    GEN_TAC THEN
    `?s. p t' = STATE s` by PROVE_TAC[] THEN
    ASM_SIMP_TAC std_ss [TRANSLATE_TOP_BOTTOM_def, IN_DEF] THEN
    PROVE_TAC[PATH_PROP_FREE_SEM]
  );



val PSL_TO_RLTL___NO_TOP_BOT_THM =
 store_thm
  ("PSL_TO_RLTL___NO_TOP_BOT_THM",
   ``!f v. (IS_INFINITE_TOP_BOTTOM_FREE_PATH v) /\ (F_CLOCK_SERE_FREE f) ==>
    ((UF_SEM v f) = RLTL_SEM (CONVERT_PATH_PSL_LTL___NO_TOP_BOT v) (PSL_TO_RLTL f))``,

    REPEAT STRIP_TAC THEN
    REMAINS_TAC `UF_SEM (PATH_LETTER_RESTRICT (F_USED_VARS f) v) f =
        RLTL_SEM (CONVERT_PATH_PSL_LTL___NO_TOP_BOT (PATH_LETTER_RESTRICT (F_USED_VARS f) v)) (PSL_TO_RLTL f)` THEN1 (

        SUBGOAL_TAC `UF_SEM v f = UF_SEM (PATH_LETTER_RESTRICT (F_USED_VARS f) v) f` THEN1 (
            MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] F_USED_VARS_INTER_SUBSET_THM) THEN
            FULL_SIMP_TAC std_ss [F_CLOCK_SERE_FREE_def, SUBSET_REFL]
        ) THEN
        FULL_SIMP_TAC std_ss [RLTL_SEM_def] THEN
        ONCE_REWRITE_TAC[RLTL_USED_VARS_INTER_THM] THEN
        REPEAT AP_THM_TAC THEN AP_TERM_TAC THEN
        ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
        SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def,
            CONVERT_PATH_PSL_LTL___NO_TOP_BOT_def,
            LENGTH_PATH_LETTER_RESTRICT, EXTENSION, IN_INTER, IN_UNION,
            P_USED_VARS_EVAL, NOT_IN_EMPTY] THEN
        REPEAT STRIP_TAC  THEN
        BOOL_EQ_STRIP_TAC THEN
        Cases_on `x < LENGTH v` THEN ASM_REWRITE_TAC[] THEN
        SIMP_ALL_TAC std_ss [IS_INFINITE_TOP_BOTTOM_FREE_PATH_def] THEN
        `?s. p x = STATE s` by METIS_TAC[] THEN
        ASM_SIMP_TAC std_ss [ELEM_PATH_LETTER_RESTRICT, GT_LS, ELEM_INFINITE, TRANSLATE_STATE_def,
            LETTER_RESTRICT_def, IN_INTER] THEN
                `?s. p x = STATE s` by METIS_TAC[] THEN
        METIS_TAC [RLTL_USED_VARS___PSL_TO_RLTL]
    ) THEN

    SUBGOAL_TAC `?g. INJ g (F_USED_VARS f) UNIV /\
                             (!x. x IN F_USED_VARS f ==> (~(g x = 0) /\ ~(g x = 1:num)))` THEN1 (

        SUBGOAL_TAC `(INFINITE (UNIV:num set)):bool` THEN1 (
            REWRITE_TAC[INFINITE_UNIV] THEN
            Q_TAC EXISTS_TAC `\n. SUC n` THEN
            SIMP_TAC std_ss [] THEN
            EXISTS_TAC ``0:num`` THEN
            DECIDE_TAC
        ) THEN
        `?h:'a -> num.  INJ h (F_USED_VARS f) UNIV` by PROVE_TAC[FINITE_INJ_EXISTS, FINITE___F_USED_VARS] THEN
        Q_TAC EXISTS_TAC `\x. h x + 2` THEN
        SIMP_TAC arith_ss [] THEN
        UNDISCH_HD_TAC THEN
        SIMP_TAC std_ss [INJ_DEF, IN_UNIV]
    ) THEN

    SUBGOAL_TAC `UF_SEM (PATH_LETTER_RESTRICT (F_USED_VARS f) v) f =
      UF_SEM (PATH_VAR_RENAMING g (PATH_LETTER_RESTRICT (F_USED_VARS f) v)) (F_VAR_RENAMING g f)` THEN1 (
        MATCH_MP_TAC UF_SEM___VAR_RENAMING THEN
        FULL_SIMP_TAC std_ss [F_CLOCK_SERE_FREE_def] THEN
        UNDISCH_NO_TAC 1 THEN
        MATCH_MP_TAC set_lemmataTheory.INJ_SUBSET_DOMAIN THEN
        FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_UNION,
            PATH_LETTER_RESTRICT_def, IS_INFINITE_TOP_BOTTOM_FREE_PATH_def,
            psl_lemmataTheory.PATH_MAP_def, IN_ABS,
            psl_lemmataTheory.PATH_USED_VARS_def, LENGTH_def, GT, ELEM_INFINITE] THEN
        REPEAT STRIP_TAC THEN
        `?s. p n = STATE s` by PROVE_TAC[] THEN
        FULL_SIMP_TAC std_ss [LETTER_RESTRICT_def, LETTER_USED_VARS_def,
            IN_INTER]
    ) THEN
    ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

    SUBGOAL_TAC `UF_SEM (PATH_VAR_RENAMING g (PATH_LETTER_RESTRICT (F_USED_VARS f) v)) (F_VAR_RENAMING g f) =
    RLTL_SEM (CONVERT_PATH_PSL_LTL___NO_TOP_BOT ((PATH_VAR_RENAMING g (PATH_LETTER_RESTRICT (F_USED_VARS f) v)))) (PSL_TO_RLTL (F_VAR_RENAMING g f))` THEN1 (
        MATCH_MP_TAC PSL_TO_RLTL___NO_TOP_BOT_THM___WITH_T_B THEN
        EXISTS_TAC ``1:num`` THEN
        EXISTS_TAC ``0:num`` THEN
        FULL_SIMP_TAC std_ss [IS_INFINITE_TOP_BOTTOM_FREE_PATH_def,
            F_VAR_RENAMING___F_CLOCK_SERE_FREE,
            PATH_LETTER_RESTRICT_def, psl_lemmataTheory.PATH_VAR_RENAMING_def,
            psl_lemmataTheory.PATH_MAP_def, path_11,
            PATH_PROP_FREE_def, LENGTH_def, LS, ELEM_INFINITE,
            GSYM FORALL_AND_THM] THEN
        GEN_TAC THEN
        `?s. p n = STATE s` by PROVE_TAC[] THEN
        ASM_SIMP_TAC std_ss [LETTER_RESTRICT_def, LETTER_VAR_RENAMING_def,
            letter_11] THEN
        SIMP_TAC std_ss [EXTENSION, IN_IMAGE, IN_INTER] THEN
        PROVE_TAC[]
    ) THEN
    ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN


    ASSUME_TAC (ISPECL [``PSL_TO_RLTL (f:'a fl)``, ``(CONVERT_PATH_PSL_LTL___NO_TOP_BOT
         (PATH_LETTER_RESTRICT (F_USED_VARS f) v))``, ``g:'a -> num``] RLTL_SEM___VAR_RENAMING___PATH_RESTRICT) THEN
    UNDISCH_HD_TAC THEN
    ASM_SIMP_TAC std_ss [RLTL_USED_VARS___PSL_TO_RLTL] THEN
    DISCH_TAC THEN WEAKEN_HD_TAC THEN
    ASM_SIMP_TAC std_ss [RLTL_VAR_RENAMING___PSL_TO_RLTL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
    FULL_SIMP_TAC std_ss [CONVERT_PATH_PSL_LTL___NO_TOP_BOT_def,
                               IS_INFINITE_TOP_BOTTOM_FREE_PATH_def,
                               PATH_LETTER_RESTRICT_def,
                               psl_lemmataTheory.PATH_MAP_def,
                               psl_lemmataTheory.PATH_VAR_RENAMING_def,
                               LENGTH_def, LS, ELEM_INFINITE,
                               PATH_RESTRICT_def, PATH_MAP_def,
                               PATH_VAR_RENAMING_def] THEN
    GEN_TAC THEN
    `?s. p x = STATE s` by PROVE_TAC[] THEN
    ASM_SIMP_TAC std_ss [LETTER_RESTRICT_def, LETTER_VAR_RENAMING_def,
        TRANSLATE_STATE_def, set_lemmataTheory.INTER_INTER_ABSORPTION]
 );



val UF_KS_SEM_def =
 Define
   `UF_KS_SEM M f =
          (!p. IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p ==>
                UF_SEM (CONVERT_PATH_LTL_PSL p) f)`;

val F_KS_SEM_def =
 Define
   `F_KS_SEM M c f =
          (!p. IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p ==>
                F_SEM (CONVERT_PATH_LTL_PSL p) c f)`;


val PSL_TO_RLTL___UF_KS_SEM =
 store_thm
  ("PSL_TO_RLTL___UF_KS_SEM",
    ``!M f. F_CLOCK_SERE_FREE f
            ==>
            (UF_KS_SEM M f =
             RLTL_KS_SEM M (PSL_TO_RLTL f))``,



      REPEAT STRIP_TAC THEN
      SIMP_TAC std_ss [UF_KS_SEM_def,
        RLTL_KS_SEM_def] THEN
      FORALL_EQ_STRIP_TAC THEN
      BOOL_EQ_STRIP_TAC THEN
      SUBGOAL_TAC `IS_INFINITE_TOP_BOTTOM_FREE_PATH (CONVERT_PATH_LTL_PSL p)` THEN1 (
        SIMP_TAC std_ss [IS_INFINITE_TOP_BOTTOM_FREE_PATH_def,
          CONVERT_PATH_LTL_PSL_def, path_11, letter_11]
      ) THEN
      ASSUME_TAC PSL_TO_RLTL___NO_TOP_BOT_THM THEN
      Q_SPECL_NO_ASSUM 0 [`f`, `CONVERT_PATH_LTL_PSL p`] THEN
      UNDISCH_HD_TAC THEN ASM_SIMP_TAC std_ss [] THEN
      STRIP_TAC THEN WEAKEN_HD_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC std_ss [CONVERT_PATH_LTL_PSL_def,
                       CONVERT_PATH_PSL_LTL___NO_TOP_BOT_def,
                       LENGTH_def, LS, ELEM_INFINITE, TRANSLATE_STATE_def,
                       FUN_EQ_THM]);



val PSL_TO_RLTL___F_KS_SEM =
 store_thm
  ("PSL_TO_RLTL___F_KS_SEM",
    ``!M f c. F_SERE_FREE f
            ==>
            (F_KS_SEM M c f =
             RLTL_KS_SEM M (PSL_TO_RLTL (F_CLOCK_COMP c f)))``,


      REPEAT STRIP_TAC THEN
      SUBGOAL_TAC `RLTL_KS_SEM M (PSL_TO_RLTL (F_CLOCK_COMP c f)) =
                   UF_KS_SEM M (F_CLOCK_COMP c f)` THEN1 (
        SUBGOAL_TAC `F_CLOCK_SERE_FREE (F_CLOCK_COMP c f)` THEN1 (
          FULL_SIMP_TAC std_ss [F_CLOCK_SERE_FREE_def,
            F_CLOCK_FREE___F_CLOCK_COMP,
            F_SERE_FREE___IMPLIES___F_SERE_FREE_F_CLOCK_COMP]
        ) THEN
        METIS_TAC [PSL_TO_RLTL___UF_KS_SEM]
      ) THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC std_ss [F_KS_SEM_def, UF_KS_SEM_def,
                       F_CLOCK_COMP_CORRECT]);



val PSL_TO_RLTL___NO_TOP_BOT___CLOCKED_THM =
 store_thm
  ("PSL_TO_RLTL___NO_TOP_BOT___CLOCKED_THM",
   ``!f c v. ((IS_INFINITE_TOP_BOTTOM_FREE_PATH v) /\ (F_SERE_FREE f)) ==>
    ((F_SEM v c f) = RLTL_SEM (CONVERT_PATH_PSL_LTL___NO_TOP_BOT v) (PSL_TO_RLTL (F_CLOCK_COMP c f)))``,

   PROVE_TAC[PSL_TO_RLTL___NO_TOP_BOT_THM, F_CLOCK_COMP_CORRECT, F_CLOCK_SERE_FREE_def,
             F_SERE_FREE___IMPLIES___F_SERE_FREE_F_CLOCK_COMP,
             F_CLOCK_FREE___F_CLOCK_COMP]);



val PSL_TO_LTL_THM =
 store_thm
  ("PSL_TO_LTL_THM",
   ``!f v b t. ((IS_INFINITE_PROPER_PATH v) /\ (F_CLOCK_SERE_FREE f) /\ ~(t = b) /\ (PATH_PROP_FREE t v) /\ (PATH_PROP_FREE b v)) ==>
   ((UF_SEM v f) = (LTL_SEM (CONVERT_PATH_PSL_LTL t b v) (RLTL_TO_LTL (P_PROP t) (P_PROP b) (PSL_TO_RLTL f))))``,

   SIMP_TAC std_ss [LTL_SEM_def] THEN
   METIS_TAC[RLTL_TO_LTL_THM, PSL_TO_RLTL_THM]);



val PSL_TO_LTL___UF_KS_SEM =
 store_thm
  ("PSL_TO_LTL___UF_KS_SEM",
    ``!M f. F_CLOCK_SERE_FREE f ==>
            (UF_KS_SEM M f =
             LTL_KS_SEM M (PSL_TO_LTL f))``,

      SIMP_TAC std_ss [PSL_TO_LTL_def, PSL_TO_RLTL___UF_KS_SEM, RLTL_TO_LTL_THM___KS_SEM]);


val PSL_TO_LTL___F_KS_SEM =
 store_thm
  ("PSL_TO_LTL___F_KS_SEM",
    ``!M f c. F_SERE_FREE f ==>
            (F_KS_SEM M c f =
             LTL_KS_SEM M (PSL_TO_LTL_CLOCK c f))``,

      SIMP_TAC std_ss [PSL_TO_LTL_CLOCK_def, PSL_TO_RLTL___F_KS_SEM, RLTL_TO_LTL_THM___KS_SEM]);

val F_KS_SEM___TO___UF_KS_SEM =
 store_thm
  ("F_KS_SEM___TO___UF_KS_SEM",
    ``!M f c. (F_KS_SEM M c f =
               UF_KS_SEM M (F_CLOCK_COMP c f))``,

      SIMP_TAC std_ss [F_KS_SEM_def, UF_KS_SEM_def, F_CLOCK_COMP_CORRECT]);


val PSL_TO_LTL___UF_CONTRADICTION =
 store_thm
  ("PSL_TO_LTL___UF_CONTRADICTION",
    ``!f. F_CLOCK_SERE_FREE f ==>
            (UF_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE f =
             LTL_IS_CONTRADICTION (PSL_TO_LTL f))``,

      SIMP_TAC std_ss [PSL_TO_LTL_def, UF_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE_def,
                       LTL_IS_CONTRADICTION_def, PSL_TO_RLTL___NO_TOP_BOT_THM,
                       RLTL_SEM_def, LTL_SEM_def, RLTL_TO_LTL_THM] THEN
      REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
        Q_SPECL_NO_ASSUM 1 [`CONVERT_PATH_LTL_PSL v`] THEN
        SIMP_ALL_TAC std_ss [CONVERT_PATH_LTL_PSL___IS_INFINITE_TOP_BOTTOM_FREE,
                             CONVERT_PATH_LTL_PSL___CONVERT_PATH_PSL_LTL],

        PROVE_TAC[]
      ]);


val PSL_TO_LTL___UF_TAUTOLOGY =
 store_thm
  ("PSL_TO_LTL___UF_TAUTOLOGY",
    ``!f. F_CLOCK_SERE_FREE f ==>
            (UF_IS_TAUTOLOGY___INFINITE_TOP_BOTTOM_FREE f =
             LTL_IS_TAUTOLOGY (PSL_TO_LTL f))``,

      REPEAT STRIP_TAC THEN
      ASSUME_TAC PSL_TO_LTL___UF_CONTRADICTION THEN
      Q_SPEC_NO_ASSUM 0 `F_NOT f` THEN
      SIMP_ALL_TAC std_ss [UF_IS_TAUTOLOGY_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE___DUAL,
       LTL_TAUTOLOGY_CONTRADICTION_DUAL, PSL_TO_LTL_def, PSL_TO_RLTL_def,
       RLTL_TO_LTL_def, F_CLOCK_SERE_FREE_def, F_CLOCK_FREE_def, F_SERE_FREE_def] THEN
      PROVE_TAC[]);


val PSL_TO_LTL___UF_EQUIVALENT =
 store_thm
  ("PSL_TO_LTL___UF_EQUIVALENT",
    ``!f1 f2. F_CLOCK_SERE_FREE f1 ==> F_CLOCK_SERE_FREE f2 ==>
            (UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f1 f2 =
             LTL_IS_CONTRADICTION (LTL_NOT (LTL_EQUIV(PSL_TO_LTL f1, PSL_TO_LTL f2))))``,

      REWRITE_TAC[UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___TO___CONTRADICTION] THEN
      REPEAT STRIP_TAC THEN
      `F_CLOCK_SERE_FREE (F_NOT (F_IFF (f1,f2)))` by
        FULL_SIMP_TAC std_ss [F_CLOCK_SERE_FREE_def, F_CLOCK_FREE_def, F_SERE_FREE_def, F_IFF_def, F_OR_def, F_IMPLIES_def] THEN
      ASM_SIMP_TAC std_ss [PSL_TO_LTL___UF_CONTRADICTION] THEN
      SIMP_TAC std_ss [PSL_TO_LTL_def, F_IFF_def, F_OR_def, F_IMPLIES_def,
                       PSL_TO_RLTL_def, RLTL_TO_LTL_def,
                       LTL_IS_CONTRADICTION_def, LTL_SEM_THM] THEN
      PROVE_TAC[]);




val IS_PSL_RELATIONS =
 store_thm
  ("IS_PSL_RELATIONS",
   ``!f. ((IS_PSL_F f = IS_PSL_G (F_NOT f)) /\ (IS_PSL_G f = IS_PSL_F (F_NOT f)) /\
          (IS_PSL_FG f = IS_PSL_GF (F_NOT f)) /\ (IS_PSL_GF f = IS_PSL_FG (F_NOT f)) /\
          (IS_PSL_F f ==> IS_PSL_FG f) /\ (IS_PSL_G f ==> IS_PSL_GF f) /\
          (IS_PSL_G f ==> IS_PSL_FG f) /\ (IS_PSL_F f ==> IS_PSL_GF f) /\
          (IS_PSL_PREFIX f ==> (IS_PSL_FG f /\ IS_PSL_GF f)))``,

      INDUCT_THEN fl_induct ASSUME_TAC THEN
      FULL_SIMP_TAC std_ss [IS_PSL_G_def, IS_PSL_PREFIX_def, IS_PSL_GF_def] THEN
      METIS_TAC[]
  );


val IS_PSL___NOT_F_CLOCK_SERE_FREE =
 store_thm
  ("IS_PSL___NOT_F_CLOCK_SERE_FREE",

   ``!f. (~F_CLOCK_SERE_FREE f ==> (
          ~IS_PSL_G f /\ ~IS_PSL_F f /\ ~IS_PSL_GF f /\
          ~IS_PSL_FG f /\ ~IS_PSL_PREFIX f /\ ~IS_PSL_STREET f))``,

   INDUCT_THEN fl_induct STRIP_ASSUME_TAC THEN
   ASM_SIMP_TAC std_ss [F_CLOCK_SERE_FREE_def, F_CLOCK_FREE_def, F_SERE_FREE_def, IS_RLTL_THM, IS_PSL_THM, PSL_TO_RLTL_def] THEN
   PROVE_TAC[F_CLOCK_SERE_FREE_def]);



val IS_PSL_RLTL_THM =
 store_thm
  ("IS_PSL_RLTL_THM",

   ``!f. (F_CLOCK_SERE_FREE f ==> (
         (IS_PSL_G f = IS_RLTL_G (PSL_TO_RLTL f)) /\
         (IS_PSL_F f = IS_RLTL_F (PSL_TO_RLTL f)) /\
         (IS_PSL_GF f = IS_RLTL_GF (PSL_TO_RLTL f)) /\
         (IS_PSL_FG f = IS_RLTL_FG (PSL_TO_RLTL f)) /\
         (IS_PSL_PREFIX f = IS_RLTL_PREFIX (PSL_TO_RLTL f)) /\
         (IS_PSL_STREET f = IS_RLTL_STREET (PSL_TO_RLTL f))))``,

      INDUCT_THEN fl_induct STRIP_ASSUME_TAC THEN
      ASM_SIMP_TAC std_ss [F_CLOCK_SERE_FREE_def, F_CLOCK_FREE_def, F_SERE_FREE_def, IS_RLTL_THM, IS_PSL_THM, PSL_TO_RLTL_def]);



val IS_PSL_LTL_THM =
 store_thm
  ("IS_PSL_LTL_THM",

   ``!f a r. (F_CLOCK_SERE_FREE f ==> (
             (IS_PSL_G f = IS_LTL_G (RLTL_TO_LTL a r (PSL_TO_RLTL f))) /\
             (IS_PSL_F f = IS_LTL_F (RLTL_TO_LTL a r (PSL_TO_RLTL f))) /\
             (IS_PSL_GF f = IS_LTL_GF (RLTL_TO_LTL a r (PSL_TO_RLTL f))) /\
             (IS_PSL_FG f = IS_LTL_FG (RLTL_TO_LTL a r (PSL_TO_RLTL f))) /\
             (IS_PSL_PREFIX f = IS_LTL_PREFIX (RLTL_TO_LTL a r (PSL_TO_RLTL f))) /\
             (IS_PSL_STREET f = IS_LTL_STREET (RLTL_TO_LTL a r (PSL_TO_RLTL f)))))``,

      PROVE_TAC[IS_PSL_RLTL_THM, IS_RLTL_LTL_THM]);



val FUTURE_LTL_TO_PSL_def =
 Define
   `(FUTURE_LTL_TO_PSL (LTL_PROP b) = (F_STRONG_BOOL (PROP_LOGIC_TO_BEXP b))) /\
    (FUTURE_LTL_TO_PSL (LTL_NOT f) = (F_NOT (FUTURE_LTL_TO_PSL f))) /\
    (FUTURE_LTL_TO_PSL (LTL_AND(f1,f2)) = (F_AND(FUTURE_LTL_TO_PSL f1, FUTURE_LTL_TO_PSL f2))) /\
    (FUTURE_LTL_TO_PSL (LTL_NEXT f) = (F_NEXT (FUTURE_LTL_TO_PSL f))) /\
    (FUTURE_LTL_TO_PSL (LTL_SUNTIL(f1,f2)) = (F_UNTIL(FUTURE_LTL_TO_PSL f1, FUTURE_LTL_TO_PSL f2)))`;



val FUTURE_LTL_TO_PSL_THM =
 store_thm
  ("FUTURE_LTL_TO_PSL_THM",

   ``!f t v. (IS_FUTURE_LTL f) ==>
      ((LTL_SEM_TIME t v f) = (UF_SEM (RESTN (CONVERT_PATH_LTL_PSL v) t) (FUTURE_LTL_TO_PSL f)))``,


   INDUCT_THEN ltl_induct ASSUME_TAC THENL [
      SIMP_TAC std_ss [CONVERT_PATH_LTL_PSL_def, FUTURE_LTL_TO_PSL_def, UF_SEM_def,
      ELEM_INFINITE, RESTN_INFINITE, GSYM PROP_LOGIC_TO_BEXP_THM, LENGTH_def, GT, IS_FUTURE_LTL_def, LTL_SEM_TIME_def],


      FULL_SIMP_TAC std_ss [CONVERT_PATH_LTL_PSL_def, FUTURE_LTL_TO_PSL_def, UF_SEM_def, LTL_SEM_TIME_def,
                           IS_FUTURE_LTL_def, COMPLEMENT_def, COMPLEMENT_LETTER_def, RESTN_INFINITE, combinTheory.o_DEF],


      FULL_SIMP_TAC std_ss [CONVERT_PATH_LTL_PSL_def, FUTURE_LTL_TO_PSL_def, UF_SEM_def, IS_FUTURE_LTL_def, LTL_SEM_TIME_def],


      FULL_SIMP_TAC arith_ss [CONVERT_PATH_LTL_PSL_def, FUTURE_LTL_TO_PSL_def, UF_SEM_def, IS_FUTURE_LTL_def,
                                 RESTN_INFINITE, LENGTH_def, GT, LTL_SEM_TIME_def] THEN
      `!t. SUC t = (t+1)` by DECIDE_TAC THEN
      METIS_TAC[],


      FULL_SIMP_TAC (arith_ss++resq_SS) [CONVERT_PATH_LTL_PSL_def, FUTURE_LTL_TO_PSL_def, IS_FUTURE_LTL_def, RESTN_INFINITE,
        LTL_SEM_TIME_def, UF_SEM_def, LENGTH_def, IN_LESSX, IN_LESS] THEN
      REPEAT STRIP_TAC THEN
      EQ_TAC THEN REPEAT STRIP_TAC THENL [
         EXISTS_TAC ``k:num - t:num`` THEN
         REPEAT STRIP_TAC THENL [
            `!n:num. k - t + (n+t) = (k + n)` by DECIDE_TAC THEN
            ASM_SIMP_TAC arith_ss [],

            `?j'. j + t = j'` by PROVE_TAC[] THEN
            `(!n:num. j + (n+t) = (j' + n)) /\ (j' < k /\ t <= j')` by DECIDE_TAC THEN
            ASM_SIMP_TAC std_ss []
         ],

         EXISTS_TAC ``(k:num) + (t:num)`` THEN
         REPEAT STRIP_TAC THENL [
            DECIDE_TAC,

            ASM_SIMP_TAC arith_ss [],

            `?j'. j - t = j'` by PROVE_TAC[] THEN
            `(!n:num. j + n = (j' + (n + t))) /\ (j' < k)` by DECIDE_TAC THEN
            ASM_SIMP_TAC std_ss []
         ]
      ],

      REWRITE_TAC[IS_FUTURE_LTL_def],
      REWRITE_TAC[IS_FUTURE_LTL_def]
   ]);


val IS_LTL_PSL_THM =
 store_thm
  ("IS_LTL_PSL_THM",

   ``!f. (IS_FUTURE_LTL f) ==>
            ((IS_LTL_G f = IS_PSL_G (FUTURE_LTL_TO_PSL f)) /\
             (IS_LTL_F f = IS_PSL_F (FUTURE_LTL_TO_PSL f)) /\
             (IS_LTL_GF f = IS_PSL_GF (FUTURE_LTL_TO_PSL f)) /\
             (IS_LTL_FG f = IS_PSL_FG (FUTURE_LTL_TO_PSL f)) /\
             (IS_LTL_PREFIX f = IS_PSL_PREFIX (FUTURE_LTL_TO_PSL f)) /\
             (IS_LTL_STREET f = IS_PSL_STREET (FUTURE_LTL_TO_PSL f)))``,

      INDUCT_THEN ltl_induct STRIP_ASSUME_TAC THEN
      FULL_SIMP_TAC std_ss[IS_PSL_THM, IS_LTL_THM, IS_FUTURE_LTL_def, FUTURE_LTL_TO_PSL_def, LTL_OR_def]);

val _ = export_theory();

(* References:

  [1] Tuerk, T., Schneider, K.: A hierarchy for Accellera's property specification language, (2005).
 *)
