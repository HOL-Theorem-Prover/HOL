(* -*- Mode: holscript; -*- ***************************************************)
(*                                                                            *)
(*       Linear Temporal Logic (with both past and future operators           *)
(*                                                                            *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open pred_setTheory prop_logicTheory xprop_logicTheory infinite_pathTheory
     tuerk_tacticsLib numLib arithmeticTheory symbolic_kripke_structureTheory
     set_lemmataTheory;

open Sanity;

val _ = hide "S";
val _ = hide "I";

val _ = new_theory "full_ltl";

(*****************************************************************************)
(* Syntax                                                                    *)
(*****************************************************************************)

Datatype :
  ltl = LTL_PROP    ('prop prop_logic)
      | LTL_NOT      ltl
      | LTL_AND     (ltl # ltl)
      | LTL_NEXT     ltl         (* X in NuSMV *)
      | LTL_SUNTIL  (ltl # ltl)  (* U in NuSMV *)
      | LTL_PSNEXT   ltl         (* Y in NuSMV *)
      | LTL_PSUNTIL (ltl # ltl)  (* S in NuSMV *)
End

Theorem ltl_induct = Q.GEN `P`
   (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2)) ==> (A ==> B1)``)
     (SIMP_RULE
       std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P x ==> Q(x,y)) = !x. P x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P y ==> Q(x,y)) = !y. P y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P`,`\(f1,f2). P f1 /\ P f2`]
         (TypeBase.induction_of ``:'a ltl``))));

(*****************************************************************************)
(* Semantics                                                                 *)
(*****************************************************************************)

val LTL_SEM_TIME_def = Define
  `(LTL_SEM_TIME t v (LTL_NOT f) = ~(LTL_SEM_TIME t v f)) /\
   (LTL_SEM_TIME t v (LTL_AND (f1,f2)) =
     (LTL_SEM_TIME t v f1 /\ LTL_SEM_TIME t v f2)) /\
   (LTL_SEM_TIME t v (LTL_PROP b) = (P_SEM (v t) b)) /\
   (LTL_SEM_TIME t v (LTL_NEXT f) = LTL_SEM_TIME (SUC t) v f) /\
   (LTL_SEM_TIME t v (LTL_SUNTIL(f1,f2)) =
     ?k. k >= t /\ LTL_SEM_TIME k v f2 /\
        !j. (t <= j /\ j < k) ==> (LTL_SEM_TIME j v f1)) /\
   (LTL_SEM_TIME t v (LTL_PSNEXT f) =
     ((t > 0) /\ LTL_SEM_TIME (PRE t) v f)) /\
   (LTL_SEM_TIME t v (LTL_PSUNTIL(f1,f2)) =
     ?k. k <= t /\ LTL_SEM_TIME k v f2 /\
        !j. (k < j /\ j <= t) ==> (LTL_SEM_TIME j v f1))`;

val LTL_SEM_def = Define `LTL_SEM v f = LTL_SEM_TIME 0 v f`;

val LTL_KS_SEM_def = Define
   `LTL_KS_SEM M f =
      !p. IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M p ==> LTL_SEM p f`;

(******************************************************************************
* Syntactic Sugar
******************************************************************************)
val LTL_EQUIVALENT_def = Define
   `LTL_EQUIVALENT b1 b2 = !t w. (LTL_SEM_TIME t w b1) = (LTL_SEM_TIME t w b2)`;

val LTL_EQUIVALENT_INITIAL_def = Define
   `LTL_EQUIVALENT_INITIAL b1 b2 = !w. (LTL_SEM w b1) = (LTL_SEM w b2)`;

val LTL_OR_def = Define
   `LTL_OR(f1,f2) = LTL_NOT (LTL_AND((LTL_NOT f1),(LTL_NOT f2)))`;

val LTL_IMPL_def = Define
   `LTL_IMPL(f1, f2) = LTL_OR(LTL_NOT f1, f2)`;

val LTL_COND_def = Define
   `LTL_COND(c, f1, f2) = LTL_AND(LTL_IMPL(c, f1), LTL_IMPL(LTL_NOT c, f2))`;

val LTL_EQUIV_def = Define
   `LTL_EQUIV(b1, b2) = LTL_AND(LTL_IMPL(b1, b2),LTL_IMPL(b2, b1))`;

val LTL_EVENTUAL_def = Define
   `LTL_EVENTUAL f = LTL_SUNTIL (LTL_PROP(P_TRUE),f)`;

val LTL_ALWAYS_def = Define
   `LTL_ALWAYS f = LTL_NOT (LTL_EVENTUAL (LTL_NOT f))`;

val LTL_UNTIL_def = Define
   `LTL_UNTIL(f1,f2) = LTL_OR(LTL_SUNTIL(f1,f2),LTL_ALWAYS f1)`;

val LTL_BEFORE_def = Define
   `LTL_BEFORE(f1,f2) = LTL_NOT(LTL_SUNTIL(LTL_NOT f1,f2))`;

val LTL_SBEFORE_def = Define
   `LTL_SBEFORE(f1,f2) = LTL_SUNTIL(LTL_NOT f2,LTL_AND(f1, LTL_NOT f2))`;

val LTL_WHILE_def = Define
   `LTL_WHILE(f1,f2) = LTL_NOT(LTL_SUNTIL(LTL_OR(LTL_NOT f1, LTL_NOT f2),LTL_AND(f2, LTL_NOT f1)))`;

val LTL_SWHILE_def = Define
   `LTL_SWHILE(f1,f2) = LTL_SUNTIL(LTL_NOT f2,LTL_AND(f1, f2))`;

val LTL_PEVENTUAL_def = Define
   `LTL_PEVENTUAL f = LTL_PSUNTIL (LTL_PROP(P_TRUE),f)`;

val LTL_PALWAYS_def = Define
   `LTL_PALWAYS f = LTL_NOT (LTL_PEVENTUAL (LTL_NOT f))`;

val LTL_PUNTIL_def = Define
   `LTL_PUNTIL(f1,f2) = LTL_OR(LTL_PSUNTIL(f1,f2),LTL_PALWAYS f1)`;

val LTL_PNEXT_def = Define
   `LTL_PNEXT f = LTL_NOT(LTL_PSNEXT (LTL_NOT f))`;

val LTL_PBEFORE_def = Define
   `LTL_PBEFORE(f1,f2) = LTL_NOT(LTL_PSUNTIL(LTL_NOT f1,f2))`;

val LTL_PSBEFORE_def = Define
   `LTL_PSBEFORE(f1,f2) = LTL_PSUNTIL(LTL_NOT f2,LTL_AND(f1, LTL_NOT f2))`;

val LTL_PWHILE_def = Define
   `LTL_PWHILE(f1,f2) = LTL_NOT(LTL_PSUNTIL(LTL_OR(LTL_NOT f1, LTL_NOT f2),LTL_AND(f2, LTL_NOT f1)))`;

val LTL_PSWHILE_def = Define
   `LTL_PSWHILE(f1,f2) = LTL_PSUNTIL(LTL_NOT f2,LTL_AND(f1, f2))`;

val LTL_TRUE_def = Define
   `LTL_TRUE = LTL_PROP P_TRUE`;

val LTL_FALSE_def = Define
   `LTL_FALSE = LTL_PROP P_FALSE`;

val LTL_INIT_def = Define
   `LTL_INIT = LTL_NOT (LTL_PSNEXT (LTL_PROP P_TRUE))`;

(******************************************************************************
* Classes of LTL
******************************************************************************)

val IS_FUTURE_LTL_def = Define
  `(IS_FUTURE_LTL (LTL_PROP b) = T) /\
   (IS_FUTURE_LTL (LTL_NOT f) = IS_FUTURE_LTL f) /\
   (IS_FUTURE_LTL (LTL_AND(f1,f2)) = (IS_FUTURE_LTL f1 /\ IS_FUTURE_LTL f2)) /\
   (IS_FUTURE_LTL (LTL_NEXT f) = IS_FUTURE_LTL f) /\
   (IS_FUTURE_LTL (LTL_SUNTIL(f1,f2)) = (IS_FUTURE_LTL f1 /\ IS_FUTURE_LTL f2)) /\
   (IS_FUTURE_LTL (LTL_PSNEXT f) = F) /\
   (IS_FUTURE_LTL (LTL_PSUNTIL(f1,f2)) = F)`;

val IS_PAST_LTL_def = Define
  `(IS_PAST_LTL (LTL_PROP b) = T) /\
   (IS_PAST_LTL (LTL_NOT f) = IS_PAST_LTL f) /\
   (IS_PAST_LTL (LTL_AND(f1,f2)) = (IS_PAST_LTL f1 /\ IS_PAST_LTL f2)) /\
   (IS_PAST_LTL (LTL_PSNEXT f) = IS_PAST_LTL f) /\
   (IS_PAST_LTL (LTL_PSUNTIL(f1,f2)) = (IS_PAST_LTL f1 /\ IS_PAST_LTL f2)) /\
   (IS_PAST_LTL (LTL_NEXT f) = F) /\
   (IS_PAST_LTL (LTL_SUNTIL(f1,f2)) = F)`;

val IS_LTL_G_def = Define
  `(IS_LTL_G (LTL_PROP p) = T) /\
   (IS_LTL_G (LTL_NOT f) = IS_LTL_F f) /\
   (IS_LTL_G (LTL_AND (f,g)) = (IS_LTL_G f /\ IS_LTL_G g)) /\
   (IS_LTL_G (LTL_NEXT f) = IS_LTL_G f) /\
   (IS_LTL_G (LTL_SUNTIL(f,g)) = F) /\
   (IS_LTL_G (LTL_PSNEXT f) = IS_LTL_G f) /\
   (IS_LTL_G (LTL_PSUNTIL(f,g)) = (IS_LTL_G f /\ IS_LTL_G g)) /\

   (IS_LTL_F (LTL_PROP p) = T) /\
   (IS_LTL_F (LTL_NOT f) = IS_LTL_G f) /\
   (IS_LTL_F (LTL_AND (f,g)) = (IS_LTL_F f /\ IS_LTL_F g)) /\
   (IS_LTL_F (LTL_NEXT f) = IS_LTL_F f) /\
   (IS_LTL_F (LTL_SUNTIL(f,g)) = (IS_LTL_F f /\ IS_LTL_F g)) /\
   (IS_LTL_F (LTL_PSNEXT f) = IS_LTL_F f) /\
   (IS_LTL_F (LTL_PSUNTIL(f,g)) = (IS_LTL_F f /\ IS_LTL_F g))`;

(* (co)safety properties *)
val IS_LTL_PREFIX_def = Define
  `(IS_LTL_PREFIX (LTL_NOT f) = IS_LTL_PREFIX f) /\
   (IS_LTL_PREFIX (LTL_AND (f,g)) = (IS_LTL_PREFIX f /\ IS_LTL_PREFIX g)) /\
   (IS_LTL_PREFIX f = (IS_LTL_G f \/ IS_LTL_F f))`;

val IS_LTL_GF_def = Define
  `(IS_LTL_GF (LTL_PROP p) = T) /\
   (IS_LTL_GF (LTL_NOT f) = IS_LTL_FG f) /\
   (IS_LTL_GF (LTL_AND (f,g)) = (IS_LTL_GF f /\ IS_LTL_GF g)) /\
   (IS_LTL_GF (LTL_NEXT f) = IS_LTL_GF f) /\
   (IS_LTL_GF (LTL_SUNTIL(f,g)) = (IS_LTL_GF f /\ IS_LTL_F g)) /\
   (IS_LTL_GF (LTL_PSNEXT f) = IS_LTL_GF f) /\
   (IS_LTL_GF (LTL_PSUNTIL(f,g)) = (IS_LTL_GF f /\ IS_LTL_GF g)) /\

   (IS_LTL_FG (LTL_PROP p) = T) /\
   (IS_LTL_FG (LTL_NOT f) = IS_LTL_GF f) /\
   (IS_LTL_FG (LTL_AND (f,g)) = (IS_LTL_FG f /\ IS_LTL_FG g)) /\
   (IS_LTL_FG (LTL_NEXT f) = IS_LTL_FG f) /\
   (IS_LTL_FG (LTL_SUNTIL(f,g)) = (IS_LTL_FG f /\ IS_LTL_FG g)) /\
   (IS_LTL_FG (LTL_PSNEXT f) = IS_LTL_FG f) /\
   (IS_LTL_FG (LTL_PSUNTIL(f,g)) = (IS_LTL_FG f /\ IS_LTL_FG g))`;

val IS_LTL_STREET_def = Define
  `(IS_LTL_STREET (LTL_NOT f) = IS_LTL_STREET f) /\
   (IS_LTL_STREET (LTL_AND (f,g)) = (IS_LTL_STREET f /\ IS_LTL_STREET g)) /\
   (IS_LTL_STREET f = (IS_LTL_GF f \/ IS_LTL_FG f))`;

Theorem IS_LTL_THM = LIST_CONJ
   [IS_FUTURE_LTL_def,
    IS_PAST_LTL_def,
    IS_LTL_G_def,
    IS_LTL_GF_def,
    IS_LTL_PREFIX_def,
    IS_LTL_STREET_def];

Theorem IS_LTL_RELATIONS :
    !f. (IS_LTL_F f = IS_LTL_G (LTL_NOT f)) /\
        (IS_LTL_G f = IS_LTL_F (LTL_NOT f)) /\
        (IS_LTL_FG f = IS_LTL_GF (LTL_NOT f)) /\
        (IS_LTL_GF f = IS_LTL_FG (LTL_NOT f)) /\
        (IS_LTL_F f ==> IS_LTL_FG f) /\
        (IS_LTL_G f ==> IS_LTL_GF f) /\
        (IS_LTL_G f ==> IS_LTL_FG f) /\
        (IS_LTL_F f ==> IS_LTL_GF f) /\
        (IS_LTL_PREFIX f ==> IS_LTL_FG f /\ IS_LTL_GF f)
Proof
    INDUCT_THEN ltl_induct ASSUME_TAC
 >> REWRITE_TAC [IS_LTL_THM]
 >> METIS_TAC []
QED

(******************************************************************************
* Lemmata
******************************************************************************)
val LTL_USED_VARS_def = Define
  `(LTL_USED_VARS (LTL_PROP p) = P_USED_VARS p) /\
   (LTL_USED_VARS (LTL_NOT f) = LTL_USED_VARS f) /\
   (LTL_USED_VARS (LTL_AND (f,g)) = (LTL_USED_VARS f UNION LTL_USED_VARS g)) /\
   (LTL_USED_VARS (LTL_NEXT f) = LTL_USED_VARS f) /\
   (LTL_USED_VARS (LTL_SUNTIL(f,g)) = (LTL_USED_VARS f UNION LTL_USED_VARS g)) /\
   (LTL_USED_VARS (LTL_PSNEXT f) = LTL_USED_VARS f) /\
   (LTL_USED_VARS (LTL_PSUNTIL(f,g)) = (LTL_USED_VARS f UNION LTL_USED_VARS g))`;

Theorem LTL_USED_VARS_INTER_SUBSET_THM :
    !f t v S. (LTL_USED_VARS f) SUBSET S ==>
              (LTL_SEM_TIME t v f = LTL_SEM_TIME t (PATH_RESTRICT v S) f)
Proof
   INDUCT_THEN ltl_induct ASSUME_TAC THENL [
      SIMP_TAC arith_ss [LTL_SEM_TIME_def, LTL_USED_VARS_def, PATH_RESTRICT_def, PATH_MAP_def] THEN
      PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM],
      REWRITE_TAC[LTL_SEM_TIME_def, LTL_USED_VARS_def] THEN
      PROVE_TAC[],
      REWRITE_TAC[LTL_SEM_TIME_def, LTL_USED_VARS_def, UNION_SUBSET] THEN
      PROVE_TAC[],
      REWRITE_TAC[LTL_SEM_TIME_def, LTL_USED_VARS_def] THEN
      PROVE_TAC[],
      REWRITE_TAC[LTL_SEM_TIME_def, LTL_USED_VARS_def, UNION_SUBSET] THEN
      PROVE_TAC[],
      REWRITE_TAC[LTL_SEM_TIME_def, LTL_USED_VARS_def] THEN
      PROVE_TAC[],
      REWRITE_TAC[LTL_SEM_TIME_def, LTL_USED_VARS_def, UNION_SUBSET] THEN
      PROVE_TAC[]
   ]
QED

Theorem LTL_USED_VARS_INTER_THM :
    !f t v. (LTL_SEM_TIME t v f = LTL_SEM_TIME t (PATH_RESTRICT v (LTL_USED_VARS f)) f)
Proof
    METIS_TAC [LTL_USED_VARS_INTER_SUBSET_THM, SUBSET_REFL]
QED

Theorem FINITE___LTL_USED_VARS :
    !l. FINITE (LTL_USED_VARS l)
Proof
    INDUCT_THEN ltl_induct ASSUME_TAC
 >- REWRITE_TAC [LTL_USED_VARS_def, FINITE___P_USED_VARS]
 >> ASM_REWRITE_TAC [LTL_USED_VARS_def, FINITE_UNION]
QED

Theorem LTL_USED_VARS_EVAL :
    !p r r1 r2.
    (LTL_USED_VARS (LTL_PROP p) = P_USED_VARS p) /\
    (LTL_USED_VARS (LTL_NOT r) = LTL_USED_VARS r) /\
    (LTL_USED_VARS (LTL_AND (r1,r2)) = LTL_USED_VARS r1 UNION LTL_USED_VARS r2) /\
    (LTL_USED_VARS (LTL_NEXT r) = LTL_USED_VARS r) /\
    (LTL_USED_VARS (LTL_SUNTIL(r1,r2)) = LTL_USED_VARS r1 UNION LTL_USED_VARS r2) /\
    (LTL_USED_VARS (LTL_PSNEXT r) = LTL_USED_VARS r) /\
    (LTL_USED_VARS (LTL_PSUNTIL(r1,r2)) = LTL_USED_VARS r1 UNION LTL_USED_VARS r2) /\
    (LTL_USED_VARS (LTL_OR (r1,r2)) = LTL_USED_VARS r1 UNION LTL_USED_VARS r2) /\
    (LTL_USED_VARS (LTL_IMPL (r1,r2)) = LTL_USED_VARS r1 UNION LTL_USED_VARS r2) /\
    (LTL_USED_VARS (LTL_EQUIV (r1,r2)) = LTL_USED_VARS r1 UNION LTL_USED_VARS r2) /\
    (LTL_USED_VARS (LTL_ALWAYS r) = LTL_USED_VARS r) /\
    (LTL_USED_VARS (LTL_EVENTUAL r) = LTL_USED_VARS r) /\
    (LTL_USED_VARS (LTL_PNEXT r) = LTL_USED_VARS r) /\
    (LTL_USED_VARS LTL_TRUE  = EMPTY) /\
    (LTL_USED_VARS LTL_FALSE = EMPTY) /\
    (LTL_USED_VARS LTL_INIT = EMPTY) /\
    (LTL_USED_VARS (LTL_PALWAYS r) = LTL_USED_VARS r) /\
    (LTL_USED_VARS (LTL_PEVENTUAL r) = LTL_USED_VARS r) /\
    (LTL_USED_VARS (LTL_WHILE (r1,r2)) = LTL_USED_VARS r1 UNION LTL_USED_VARS r2) /\
    (LTL_USED_VARS (LTL_BEFORE (r1,r2)) = LTL_USED_VARS r1 UNION LTL_USED_VARS r2) /\
    (LTL_USED_VARS (LTL_SWHILE (r1,r2)) = LTL_USED_VARS r1 UNION LTL_USED_VARS r2) /\
    (LTL_USED_VARS (LTL_SBEFORE (r1,r2)) = LTL_USED_VARS r1 UNION LTL_USED_VARS r2) /\
    (LTL_USED_VARS (LTL_PWHILE (r1,r2)) = LTL_USED_VARS r1 UNION LTL_USED_VARS r2) /\
    (LTL_USED_VARS (LTL_PBEFORE (r1,r2)) = LTL_USED_VARS r1 UNION LTL_USED_VARS r2) /\
    (LTL_USED_VARS (LTL_PSWHILE (r1,r2)) = LTL_USED_VARS r1 UNION LTL_USED_VARS r2) /\
    (LTL_USED_VARS (LTL_PSBEFORE (r1,r2)) = LTL_USED_VARS r1 UNION LTL_USED_VARS r2)
Proof
    rpt GEN_TAC
 >> SIMP_TAC std_ss [LTL_USED_VARS_def, LTL_OR_def, LTL_IMPL_def, LTL_EQUIV_def,
                     LTL_ALWAYS_def, LTL_EVENTUAL_def, P_VAR_RENAMING_EVAL,
                     LTL_PNEXT_def, LTL_TRUE_def, LTL_FALSE_def, LTL_INIT_def,
                     LTL_PALWAYS_def, LTL_PEVENTUAL_def, LTL_WHILE_def,
                     LTL_SWHILE_def, LTL_PSWHILE_def, LTL_PWHILE_def,
                     LTL_BEFORE_def, LTL_SBEFORE_def, LTL_PSBEFORE_def,
                     LTL_PBEFORE_def, P_USED_VARS_EVAL, UNION_EMPTY]
 >> SIMP_TAC std_ss [EXTENSION, IN_UNION]
 >> PROVE_TAC []
QED

val LTL_VAR_RENAMING_def = Define
  `(LTL_VAR_RENAMING f (LTL_PROP p) = LTL_PROP (P_VAR_RENAMING f p)) /\
   (LTL_VAR_RENAMING f (LTL_NOT r) = LTL_NOT (LTL_VAR_RENAMING f r)) /\
   (LTL_VAR_RENAMING f (LTL_AND (r1,r2)) =
    LTL_AND(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2)) /\
   (LTL_VAR_RENAMING f (LTL_NEXT r) = LTL_NEXT (LTL_VAR_RENAMING f r)) /\
   (LTL_VAR_RENAMING f (LTL_SUNTIL(r1,r2)) =
    LTL_SUNTIL(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2)) /\
   (LTL_VAR_RENAMING f (LTL_PSNEXT r) = LTL_PSNEXT (LTL_VAR_RENAMING f r)) /\
   (LTL_VAR_RENAMING f (LTL_PSUNTIL(r1,r2)) =
    LTL_PSUNTIL(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2))`;

Theorem LTL_SEM_TIME___VAR_RENAMING___NOT_INJ :
    !f' t v f. LTL_SEM_TIME t v (LTL_VAR_RENAMING f f') =
               LTL_SEM_TIME t (\n x. f x IN v n) f'
Proof
    INDUCT_THEN ltl_induct ASSUME_TAC
 >> ASM_SIMP_TAC std_ss [LTL_VAR_RENAMING_def, LTL_SEM_TIME_def,
                         P_SEM___VAR_RENAMING___NOT_INJ]
QED

Theorem LTL_SEM_TIME___VAR_RENAMING :
    !f' t v f. INJ f (PATH_USED_VARS v UNION LTL_USED_VARS f') UNIV ==>
              (LTL_SEM_TIME t v f' =
               LTL_SEM_TIME t (PATH_VAR_RENAMING f v) (LTL_VAR_RENAMING f f'))
Proof
    INDUCT_THEN ltl_induct ASSUME_TAC
 >| [ SIMP_TAC std_ss [LTL_SEM_TIME_def,
                       LTL_VAR_RENAMING_def, PATH_VAR_RENAMING_def,
                       PATH_MAP_def] THEN
      rpt STRIP_TAC THEN
      MATCH_MP_TAC P_SEM___VAR_RENAMING THEN
      UNDISCH_HD_TAC THEN
      MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
      REWRITE_TAC [SUBSET_DEF, IN_UNION, LTL_USED_VARS_def,
        GSYM PATH_USED_VARS_THM] THEN
      PROVE_TAC[],

      ASM_SIMP_TAC std_ss [LTL_SEM_TIME_def, LTL_USED_VARS_def,
        LTL_VAR_RENAMING_def],

      SIMP_TAC std_ss [LTL_SEM_TIME_def, LTL_USED_VARS_def,
        LTL_VAR_RENAMING_def] THEN
      rpt STRIP_TAC THEN
      REMAINS_TAC `INJ f (PATH_USED_VARS v UNION LTL_USED_VARS f'') UNIV /\
                   INJ f (PATH_USED_VARS v UNION LTL_USED_VARS f') UNIV` THEN1 (
        RES_TAC THEN
        ASM_REWRITE_TAC[]
      ) THEN
      NTAC 2 (WEAKEN_NO_TAC 1) THEN
      STRIP_TAC THEN
      UNDISCH_HD_TAC THEN
      MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
      PROVE_TAC [],

      ASM_SIMP_TAC std_ss [LTL_SEM_TIME_def, LTL_USED_VARS_def,
                           LTL_VAR_RENAMING_def],

      SIMP_TAC std_ss [LTL_SEM_TIME_def, LTL_USED_VARS_def,
        LTL_VAR_RENAMING_def] THEN
      rpt STRIP_TAC THEN
      REMAINS_TAC `INJ f (PATH_USED_VARS v UNION LTL_USED_VARS f'') UNIV /\
                   INJ f (PATH_USED_VARS v UNION LTL_USED_VARS f') UNIV` THEN1 (
        RES_TAC THEN
        ASM_REWRITE_TAC[]
      ) THEN
      NTAC 2 (WEAKEN_NO_TAC 1) THEN
      STRIP_TAC THEN
      UNDISCH_HD_TAC THEN
      MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
      PROVE_TAC [],

      SIMP_TAC std_ss [LTL_SEM_TIME_def, LTL_USED_VARS_def,
        LTL_VAR_RENAMING_def] THEN
      Cases_on `t` THENL [
        SIMP_TAC std_ss [],
        ASM_SIMP_TAC std_ss []
      ],

      SIMP_TAC std_ss [LTL_SEM_TIME_def, LTL_USED_VARS_def,
        LTL_VAR_RENAMING_def] THEN
      rpt STRIP_TAC THEN
      REMAINS_TAC `INJ f (PATH_USED_VARS v UNION LTL_USED_VARS f'') UNIV /\
                   INJ f (PATH_USED_VARS v UNION LTL_USED_VARS f') UNIV` THEN1 (
        RES_TAC THEN
        ASM_REWRITE_TAC[]
      ) THEN
      NTAC 2 (WEAKEN_NO_TAC 1) THEN
      STRIP_TAC THEN
      UNDISCH_HD_TAC THEN
      MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
      PROVE_TAC [] ]
QED

Theorem LTL_SEM_TIME___VAR_RENAMING___PATH_RESTRICT :
    !f' t v f. INJ f (LTL_USED_VARS f') UNIV ==>
              (LTL_SEM_TIME t v f' =
               LTL_SEM_TIME t (PATH_VAR_RENAMING f (PATH_RESTRICT v (LTL_USED_VARS f')))
                              (LTL_VAR_RENAMING f f'))
Proof
    rpt STRIP_TAC
 >> CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [LTL_USED_VARS_INTER_THM]))
 >> MATCH_MP_TAC LTL_SEM_TIME___VAR_RENAMING
 >> UNDISCH_HD_TAC
 >> MATCH_MP_TAC INJ_SUBSET_DOMAIN
 >> SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, GSYM PATH_USED_VARS_THM,
                     PATH_RESTRICT_def, PATH_MAP_def, IN_INTER]
 >> PROVE_TAC []
QED

Theorem FUTURE_LTL_CONSIDERS_ONLY_FUTURE :
    !f t v. IS_FUTURE_LTL f ==> (LTL_SEM_TIME t v f <=> LTL_SEM (\t'. v (t'+t)) f)
Proof
    INDUCT_THEN ltl_induct ASSUME_TAC
 >> (SIMP_TAC std_ss [IS_FUTURE_LTL_def, LTL_SEM_TIME_def, LTL_SEM_def] \\
     REWRITE_TAC [GSYM LTL_SEM_def] \\
     ASM_SIMP_TAC std_ss [])
 >| [ (* NEXT *)
      ASM_SIMP_TAC arith_ss [arithmeticTheory.ADD1],
      (* SUNTIL *)
      rpt STRIP_TAC >> EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
      [ Q.EXISTS_TAC `k - t` \\
        FULL_SIMP_TAC arith_ss [] \\
        rpt STRIP_TAC \\
        Q.PAT_X_ASSUM `!j. _` (MP_TAC o Q.SPEC `j+t`) \\
        FULL_SIMP_TAC arith_ss [],
        Q.EXISTS_TAC `k + t` \\
        FULL_SIMP_TAC arith_ss [] \\
        rpt STRIP_TAC \\
        Q.PAT_X_ASSUM `!j. _` (MP_TAC o Q.SPEC `j-t`) \\
        FULL_SIMP_TAC arith_ss [] ] ]
QED

Theorem FUTURE_LTL_EQUIVALENT_INIT_IS_EQUIVALENT :
    !l1 l2. IS_FUTURE_LTL l1 /\ IS_FUTURE_LTL l2 ==>
           (LTL_EQUIVALENT_INITIAL l1 l2 <=> LTL_EQUIVALENT l1 l2)
Proof
    SIMP_TAC std_ss [LTL_EQUIVALENT_INITIAL_def,
                     LTL_EQUIVALENT_def, FUTURE_LTL_CONSIDERS_ONLY_FUTURE]
 >> rpt STRIP_TAC >> EQ_TAC >> rpt STRIP_TAC
 >- ASM_SIMP_TAC std_ss []
 >> Q.PAT_X_ASSUM `!t w. _` (MP_TAC o Q.SPECL [`0`, `w`])
 >> ASM_SIMP_TAC std_ss [ETA_THM]
QED

Theorem LTL_OR_SEM :
    !v f1 f2 t. LTL_SEM_TIME t v (LTL_OR(f1,f2)) <=>
                LTL_SEM_TIME t v f1 \/ LTL_SEM_TIME t v f2
Proof
    REWRITE_TAC [LTL_OR_def, LTL_SEM_TIME_def]
 >> SIMP_TAC arith_ss []
QED

Theorem LTL_IMPL_SEM :
    !v f1 f2 t. LTL_SEM_TIME t v (LTL_IMPL(f1,f2)) <=>
               (LTL_SEM_TIME t v f1 ==> LTL_SEM_TIME t v f2)
Proof
    REWRITE_TAC [LTL_OR_def, LTL_IMPL_def, LTL_SEM_TIME_def]
 >> METIS_TAC []
QED

Theorem LTL_EQUIV_SEM :
    !v f1 f2 t. LTL_SEM_TIME t v (LTL_EQUIV(f1,f2)) <=>
               (LTL_SEM_TIME t v f1 <=> LTL_SEM_TIME t v f2)
Proof
    REWRITE_TAC[LTL_EQUIV_def, LTL_IMPL_SEM, LTL_SEM_TIME_def]
 >> METIS_TAC []
QED

Theorem LTL_SBEFORE_SEM :
    !v f1 f2 t. LTL_SEM_TIME t v (LTL_SBEFORE(f1,f2)) <=>
       ?k. k >= t /\ (LTL_SEM_TIME k v f1) /\
           !j. t <= j /\ j <= k ==> ~(LTL_SEM_TIME j v f2)
Proof
    REWRITE_TAC [LTL_SBEFORE_def, LTL_SEM_TIME_def]
 >> rpt STRIP_TAC THEN
   EXISTS_EQ_STRIP_TAC THEN
   rpt BOOL_EQ_STRIP_TAC THEN
   EQ_TAC THEN rpt STRIP_TAC THENL [
     Cases_on `j < k` THENL [
       PROVE_TAC[],

       `j = k` by DECIDE_TAC THEN
       PROVE_TAC[]
     ],

     `t <= k /\ k <= k` by DECIDE_TAC THEN
     PROVE_TAC[],

     `j <= k` by DECIDE_TAC THEN
     PROVE_TAC[]
   ]
QED

Theorem LTL_PSBEFORE_SEM :
    !v f1 f2 t. LTL_SEM_TIME t v (LTL_PSBEFORE(f1,f2)) <=>
                ?k. k <= t /\ LTL_SEM_TIME k v f1 /\
                    !j. k <= j /\ j <= t ==> ~(LTL_SEM_TIME j v f2)
Proof
    REWRITE_TAC [LTL_PSBEFORE_def, LTL_SEM_TIME_def]
 >> rpt STRIP_TAC
 >> EXISTS_EQ_STRIP_TAC
 >> rpt BOOL_EQ_STRIP_TAC
 >> EQ_TAC >> rpt STRIP_TAC
 >| [ Cases_on `k < j` THENL [
       PROVE_TAC [],
       `j = k` by DECIDE_TAC THEN
       PROVE_TAC []
      ],

     `k <= k` by DECIDE_TAC THEN
      PROVE_TAC [],

     `k <= j` by DECIDE_TAC THEN
      PROVE_TAC [] ]
QED

Theorem LTL_EVENTUAL_SEM :
    !v f t. LTL_SEM_TIME t v (LTL_EVENTUAL f) = ?k. k >= t /\ LTL_SEM_TIME k v f
Proof
    EVAL_TAC >> SIMP_TAC arith_ss [P_SEM_THM]
QED

Theorem LTL_ALWAYS_SEM :
    !v f t. LTL_SEM_TIME t v (LTL_ALWAYS f) = !k. k >= t ==> LTL_SEM_TIME k v f
Proof
    EVAL_TAC >> SIMP_TAC arith_ss [P_SEM_THM]
 >> PROVE_TAC []
QED

Theorem LTL_PEVENTUAL_SEM :
    !v f t. LTL_SEM_TIME t v (LTL_PEVENTUAL f) =
            ?k:num. (0 <= k /\ k <= t) /\ LTL_SEM_TIME k v f
Proof
    EVAL_TAC >> SIMP_TAC arith_ss [P_SEM_THM]
QED

Theorem LTL_PALWAYS_SEM :
    !v f t. LTL_SEM_TIME t v (LTL_PALWAYS f) = !k. k <= t ==> LTL_SEM_TIME k v f
Proof
    EVAL_TAC >> SIMP_TAC arith_ss [P_SEM_THM] >> PROVE_TAC []
QED

Theorem LTL_PNEXT_SEM :
    !v f t. LTL_SEM_TIME t v (LTL_PNEXT f) = ((t = 0) \/ LTL_SEM_TIME (PRE t) v f)
Proof
    EVAL_TAC >> SIMP_TAC arith_ss [P_SEM_THM]
 >> `!t:num. (~(t > 0)) = (t = 0)` by DECIDE_TAC
 >> PROVE_TAC []
QED

Theorem LTL_TRUE_SEM :
    !v t. LTL_SEM_TIME t v LTL_TRUE
Proof
    REWRITE_TAC [LTL_TRUE_def, LTL_SEM_TIME_def, P_SEM_THM]
QED

Theorem LTL_FALSE_SEM :
    !v t. ~(LTL_SEM_TIME t v LTL_FALSE)
Proof
    REWRITE_TAC [LTL_FALSE_def, LTL_SEM_TIME_def, P_SEM_THM]
QED

Theorem LTL_INIT_SEM :
    !t v. (LTL_SEM_TIME t v LTL_INIT) = (t = 0)
Proof
    REWRITE_TAC [LTL_INIT_def, LTL_SEM_TIME_def, P_SEM_def]
 >> DECIDE_TAC
QED

Theorem LTL_SEM_THM = LIST_CONJ
   [LTL_SEM_def, LTL_SEM_TIME_def,
    LTL_OR_SEM,
    LTL_IMPL_SEM,
    LTL_EQUIV_SEM,
    LTL_ALWAYS_SEM,
    LTL_EVENTUAL_SEM,
    LTL_PNEXT_SEM,
    LTL_PEVENTUAL_SEM,
    LTL_PALWAYS_SEM,
    LTL_TRUE_SEM,
    LTL_FALSE_SEM,
    LTL_INIT_SEM,
    LTL_SBEFORE_SEM,
    LTL_PSBEFORE_SEM];

Theorem LTL_VAR_RENAMING_EVAL :
    (LTL_VAR_RENAMING f (LTL_PROP p) = LTL_PROP (P_VAR_RENAMING f p)) /\
    (LTL_VAR_RENAMING f (LTL_NOT r) = LTL_NOT (LTL_VAR_RENAMING f r)) /\
    (LTL_VAR_RENAMING f (LTL_AND (r1,r2)) = LTL_AND(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2)) /\
    (LTL_VAR_RENAMING f (LTL_NEXT r) = LTL_NEXT (LTL_VAR_RENAMING f r)) /\
    (LTL_VAR_RENAMING f (LTL_SUNTIL(r1,r2)) = LTL_SUNTIL(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2)) /\
    (LTL_VAR_RENAMING f (LTL_PSNEXT r) = LTL_PSNEXT (LTL_VAR_RENAMING f r)) /\
    (LTL_VAR_RENAMING f (LTL_PSUNTIL(r1,r2)) = LTL_PSUNTIL(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2)) /\
    (LTL_VAR_RENAMING f (LTL_OR (r1,r2)) = LTL_OR(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2)) /\
    (LTL_VAR_RENAMING f (LTL_IMPL (r1,r2)) = LTL_IMPL(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2)) /\
    (LTL_VAR_RENAMING f (LTL_EQUIV (r1,r2)) = LTL_EQUIV(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2)) /\
    (LTL_VAR_RENAMING f (LTL_ALWAYS r) = LTL_ALWAYS (LTL_VAR_RENAMING f r)) /\
    (LTL_VAR_RENAMING f (LTL_EVENTUAL r) = LTL_EVENTUAL (LTL_VAR_RENAMING f r)) /\
    (LTL_VAR_RENAMING f (LTL_PNEXT r) = LTL_PNEXT (LTL_VAR_RENAMING f r)) /\
    (LTL_VAR_RENAMING f LTL_TRUE  = LTL_TRUE) /\
    (LTL_VAR_RENAMING f LTL_FALSE = LTL_FALSE) /\
    (LTL_VAR_RENAMING f LTL_INIT = LTL_INIT) /\
    (LTL_VAR_RENAMING f (LTL_PALWAYS r) = LTL_PALWAYS (LTL_VAR_RENAMING f r)) /\
    (LTL_VAR_RENAMING f (LTL_PEVENTUAL r) = LTL_PEVENTUAL (LTL_VAR_RENAMING f r)) /\
    (LTL_VAR_RENAMING f (LTL_WHILE (r1,r2)) = LTL_WHILE(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2)) /\
    (LTL_VAR_RENAMING f (LTL_BEFORE (r1,r2)) = LTL_BEFORE(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2)) /\
    (LTL_VAR_RENAMING f (LTL_SWHILE (r1,r2)) = LTL_SWHILE(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2)) /\
    (LTL_VAR_RENAMING f (LTL_SBEFORE (r1,r2)) = LTL_SBEFORE(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2)) /\
    (LTL_VAR_RENAMING f (LTL_PWHILE (r1,r2)) = LTL_PWHILE(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2)) /\
    (LTL_VAR_RENAMING f (LTL_PBEFORE (r1,r2)) = LTL_PBEFORE(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2)) /\
    (LTL_VAR_RENAMING f (LTL_PSWHILE (r1,r2)) = LTL_PSWHILE(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2)) /\
    (LTL_VAR_RENAMING f (LTL_PSBEFORE (r1,r2)) = LTL_PSBEFORE(LTL_VAR_RENAMING f r1, LTL_VAR_RENAMING f r2))
Proof
    SIMP_TAC std_ss [LTL_VAR_RENAMING_def, LTL_OR_def, LTL_IMPL_def, LTL_EQUIV_def,
                     LTL_ALWAYS_def, LTL_EVENTUAL_def, P_VAR_RENAMING_EVAL,
                     LTL_PNEXT_def, LTL_TRUE_def, LTL_FALSE_def, LTL_INIT_def,
                     LTL_PALWAYS_def, LTL_PEVENTUAL_def, LTL_WHILE_def,
                     LTL_SWHILE_def, LTL_PSWHILE_def, LTL_PWHILE_def, LTL_BEFORE_def,
                     LTL_SBEFORE_def, LTL_PSBEFORE_def, LTL_PBEFORE_def]
QED

(* LTL_ALWAYS is usually defined as NOT EVENTUAL. However, this is simplified by
   the nnf rewrites defined in temporal_deep_simplifiactionsLib to ALWAYS again.
   Thus, the simplifier may loop. Therefore, here are direct definitions of ALWAYS
   and PALWAYS to use with the nnf rewrites.
 *)
Theorem LTL_ALWAYS_PALWAYS_ALTERNATIVE_DEFS :
    (!l. LTL_ALWAYS l = LTL_NOT (LTL_SUNTIL (LTL_TRUE, LTL_NOT l))) /\
    (!l. LTL_PALWAYS l = LTL_NOT (LTL_PSUNTIL (LTL_TRUE, LTL_NOT l)))
Proof
    SIMP_TAC std_ss [LTL_ALWAYS_def, LTL_EVENTUAL_def, LTL_TRUE_def,
                     LTL_PALWAYS_def, LTL_PEVENTUAL_def]
QED

val LTL_IS_CONTRADICTION_def = Define
   `LTL_IS_CONTRADICTION l = !v. ~(LTL_SEM v l)`;

val LTL_IS_TAUTOLOGY_def = Define
   `LTL_IS_TAUTOLOGY l = !v. LTL_SEM v l`;

Theorem LTL_TAUTOLOGY_CONTRADICTION_DUAL :
    (!l. LTL_IS_CONTRADICTION (LTL_NOT l) <=> LTL_IS_TAUTOLOGY l) /\
    (!l. LTL_IS_TAUTOLOGY (LTL_NOT l) <=> LTL_IS_CONTRADICTION l)
Proof
    REWRITE_TAC [LTL_IS_TAUTOLOGY_def, LTL_IS_CONTRADICTION_def,
                 LTL_SEM_TIME_def, LTL_SEM_def]
QED

Theorem LTL_TAUTOLOGY_CONTRADICTION___TO___EQUIVALENT_INITIAL :
    (!l. LTL_IS_CONTRADICTION l <=> LTL_EQUIVALENT_INITIAL l LTL_FALSE) /\
    (!l. LTL_IS_TAUTOLOGY l <=> LTL_EQUIVALENT_INITIAL l LTL_TRUE)
Proof
    REWRITE_TAC [LTL_IS_TAUTOLOGY_def, LTL_IS_CONTRADICTION_def, LTL_SEM_THM,
                 LTL_EQUIVALENT_INITIAL_def]
 >> PROVE_TAC []
QED

Theorem LTL_EQUIVALENT_INITIAL___TO___TAUTOLOGY :
    !l1 l2. LTL_EQUIVALENT_INITIAL l1 l2 <=> LTL_IS_TAUTOLOGY (LTL_EQUIV(l1, l2))
Proof
    REWRITE_TAC [LTL_IS_TAUTOLOGY_def, LTL_SEM_THM,
                 LTL_EQUIVALENT_INITIAL_def]
 >> PROVE_TAC []
QED

Theorem LTL_EQUIVALENT_INITIAL___TO___CONTRADICTION :
    !l1 l2. LTL_EQUIVALENT_INITIAL l1 l2 <=>
            LTL_IS_CONTRADICTION (LTL_NOT (LTL_EQUIV(l1, l2)))
Proof
    REWRITE_TAC [LTL_TAUTOLOGY_CONTRADICTION_DUAL,
                 LTL_EQUIVALENT_INITIAL___TO___TAUTOLOGY]
QED

Theorem LTL_EQUIVALENT___TO___CONTRADICTION :
    !l1 l2. LTL_EQUIVALENT l1 l2 <=>
            LTL_IS_CONTRADICTION (LTL_EVENTUAL (LTL_NOT (LTL_EQUIV (l1,l2))))
Proof
    SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_IS_CONTRADICTION_def, LTL_SEM_THM]
 >> PROVE_TAC []
QED

Theorem LTL_CONTRADICTION___VAR_RENAMING :
    !f' f. INJ f (LTL_USED_VARS f') UNIV ==>
          (LTL_IS_CONTRADICTION f' <=> LTL_IS_CONTRADICTION (LTL_VAR_RENAMING f f'))
Proof
    SIMP_TAC std_ss [LTL_IS_CONTRADICTION_def, LTL_SEM_def]
 >> rpt STRIP_TAC >> EQ_TAC
 >| [ SIMP_TAC std_ss [LTL_SEM_TIME___VAR_RENAMING___NOT_INJ],
      PROVE_TAC[LTL_SEM_TIME___VAR_RENAMING___PATH_RESTRICT] ]
QED

Theorem LTL_KS_SEM___VAR_RENAMING :
    !f' M f. INJ f (LTL_USED_VARS f' UNION (SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS M)) UNIV ==>
            (LTL_KS_SEM M f' <=> LTL_KS_SEM (SYMBOLIC_KRIPKE_STRUCTURE_VAR_RENAMING f M)
                                            (LTL_VAR_RENAMING f f'))
Proof
    SIMP_TAC std_ss [LTL_KS_SEM_def, LTL_SEM_def,
                     PATHS_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE___REWRITES,
                     SYMBOLIC_KRIPKE_STRUCTURE_VAR_RENAMING_def,
                     symbolic_kripke_structure_REWRITES]
 >> rpt STRIP_TAC >> EQ_TAC >> rpt STRIP_TAC
 >| [ SIMP_ALL_TAC std_ss [P_SEM___VAR_RENAMING___NOT_INJ,
                           XP_SEM___VAR_RENAMING___NOT_INJ,
                           LTL_SEM_TIME___VAR_RENAMING___NOT_INJ] THEN
      Q_SPEC_NO_ASSUM 2 `(\n x. f x IN p n)` THEN
      UNDISCH_HD_TAC THEN
      ASM_SIMP_TAC std_ss [],

     `?w. w = PATH_RESTRICT p (LTL_USED_VARS f' UNION
      SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS M)` by PROVE_TAC [] THEN
      SUBGOAL_TAC `(LTL_SEM_TIME 0 p f' = LTL_SEM_TIME 0 w f') /\
                   (P_SEM (p 0) M.S0 = P_SEM (w 0) M.S0) /\
                   !n. (XP_SEM M.R (p n,p (SUC n)) = XP_SEM M.R (w n,w (SUC n)))` THEN1 (
        rpt STRIP_TAC THENL [
          ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC LTL_USED_VARS_INTER_SUBSET_THM THEN
          SIMP_TAC std_ss [SUBSET_UNION],

          UNDISCH_HD_TAC THEN
          SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def] THEN
          DISCH_TAC THEN
          MATCH_MP_TAC P_USED_VARS_INTER_SUBSET_THM THEN
          SIMP_TAC std_ss [SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def, SUBSET_DEF,
            IN_UNION],

          UNDISCH_HD_TAC THEN
          SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def] THEN
          DISCH_TAC THEN
          MATCH_MP_TAC XP_USED_VARS_INTER_SUBSET_BOTH_THM THEN
          SIMP_TAC std_ss [SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def, SUBSET_DEF,
            IN_UNION]
        ]
      ) THEN
      `!n. w n SUBSET (LTL_USED_VARS f' UNION
                       SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS M)`
          by METIS_TAC[PATH_RESTRICT_SUBSET] THEN
      GSYM_NO_TAC 4 THEN
      FULL_SIMP_TAC std_ss [] THEN NTAC 3 (WEAKEN_NO_TAC 2) THEN
      Q_SPEC_NO_ASSUM 4 `PATH_VAR_RENAMING f w` THEN
      UNDISCH_HD_TAC THEN
      REMAINS_TAC `(!n.
        XP_SEM (XP_VAR_RENAMING f M.R)
          (PATH_VAR_RENAMING f w n,PATH_VAR_RENAMING f w (SUC n)) =
        XP_SEM M.R (w n, w (SUC n))) /\
        (P_SEM (PATH_VAR_RENAMING f w 0) (P_VAR_RENAMING f M.S0) =
         P_SEM (w 0) M.S0) /\
        (LTL_SEM_TIME 0 (PATH_VAR_RENAMING f w) (LTL_VAR_RENAMING f f') =
         LTL_SEM_TIME 0 w f')` THEN1 (
        FULL_SIMP_TAC std_ss []
      ) THEN

      rpt STRIP_TAC THENL [
        SIMP_TAC std_ss [PATH_VAR_RENAMING_def, PATH_MAP_def] THEN
        MATCH_MP_TAC (GSYM XP_SEM___VAR_RENAMING) THEN
        UNDISCH_NO_TAC 4 THEN
        MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
        SIMP_ALL_TAC std_ss [SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def,
                         IN_UNION, SUBSET_DEF] THEN
        PROVE_TAC [],

        SIMP_TAC std_ss [PATH_VAR_RENAMING_def, PATH_MAP_def] THEN
        MATCH_MP_TAC (GSYM P_SEM___VAR_RENAMING) THEN
        UNDISCH_NO_TAC 4 THEN
        MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
        SIMP_ALL_TAC std_ss [SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def,
                         IN_UNION, SUBSET_DEF] THEN
        PROVE_TAC [],

        MATCH_MP_TAC (GSYM LTL_SEM_TIME___VAR_RENAMING) THEN
        UNDISCH_NO_TAC 4 THEN
        MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
        SIMP_ALL_TAC std_ss [SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS_def,
                         IN_UNION, SUBSET_DEF, GSYM PATH_USED_VARS_THM] THEN
        PROVE_TAC []
      ]
    ]
QED

Theorem LTL_RECURSION_LAWS___LTL_ALWAYS :
    !f. LTL_EQUIVALENT (LTL_ALWAYS f)
                       (LTL_AND(f, LTL_NEXT(LTL_ALWAYS f)))
Proof
    REWRITE_TAC [LTL_EQUIVALENT_def, LTL_SEM_THM]
 >> rpt STRIP_TAC
 >> EQ_TAC >> rpt STRIP_TAC
 >| [ `t >= t` by DECIDE_TAC >> PROVE_TAC [],
      `k >= t` by DECIDE_TAC >> PROVE_TAC [],
      Cases_on `k = t` >|
      [ PROVE_TAC [],
       `k >= SUC t` by DECIDE_TAC \\
        PROVE_TAC [] ] ]
QED

Theorem LTL_RECURSION_LAWS___LTL_EVENTUAL :
    !f. LTL_EQUIVALENT (LTL_EVENTUAL f)
                       (LTL_OR(f, LTL_NEXT(LTL_EVENTUAL f)))
Proof
    REWRITE_TAC [LTL_EQUIVALENT_def, LTL_SEM_THM]
 >> rpt STRIP_TAC
 >> EQ_TAC >> rpt STRIP_TAC
 >| [ Cases_on `k = t` >|
      [ PROVE_TAC [],
       `k >= SUC t` by DECIDE_TAC >> PROVE_TAC [] ],
     `t >= t` by DECIDE_TAC >> PROVE_TAC [],
     `k >= t` by DECIDE_TAC >> PROVE_TAC [] ]
QED

Theorem LTL_RECURSION_LAWS___LTL_SUNTIL :
    !l1 l2. LTL_EQUIVALENT (LTL_SUNTIL (l1, l2))
                           (LTL_OR(l2, LTL_AND(l1, LTL_NEXT(LTL_SUNTIL (l1, l2)))))
Proof
    SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_SEM_THM]
 >> rpt STRIP_TAC THEN EQ_TAC THEN rpt STRIP_TAC THENL [
  Cases_on `k = t` THENL [
    PROVE_TAC[],

    DISJ2_TAC THEN
    rpt STRIP_TAC THENL [
      `t <= t /\ t < k` by DECIDE_TAC THEN
      PROVE_TAC[],

      EXISTS_TAC ``k:num`` THEN
      rpt STRIP_TAC THENL [
        DECIDE_TAC,
        ASM_REWRITE_TAC[],
        `t <= j` by DECIDE_TAC THEN PROVE_TAC[]
      ]
    ]
  ],

  EXISTS_TAC ``t:num`` THEN
  ASM_SIMP_TAC arith_ss [],

  EXISTS_TAC ``k:num`` THEN
  ASM_SIMP_TAC arith_ss [] THEN
  rpt STRIP_TAC THEN
  Cases_on `j = t` THENL [
    PROVE_TAC[],
    `SUC t <= j` by DECIDE_TAC THEN PROVE_TAC[]
  ]
]
QED

Theorem LTL_RECURSION_LAWS___LTL_PSUNTIL :
    !l1 l2. LTL_EQUIVALENT (LTL_PSUNTIL (l1, l2))
                           (LTL_OR(l2, LTL_AND(l1, LTL_PSNEXT(LTL_PSUNTIL (l1, l2)))))
Proof
    SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_SEM_THM]
 >> rpt STRIP_TAC THEN EQ_TAC THEN rpt STRIP_TAC THENL [
  Cases_on `k = t` THENL [
    PROVE_TAC[],

    DISJ2_TAC THEN
    Cases_on `t` THEN SIMP_ALL_TAC arith_ss [] THEN
    rpt STRIP_TAC THENL [
      `SUC n <= SUC n /\ k < SUC n` by DECIDE_TAC THEN
      PROVE_TAC[],

      EXISTS_TAC ``k:num`` THEN
      rpt STRIP_TAC THENL [
        DECIDE_TAC,
        ASM_REWRITE_TAC[],
        `j <= SUC n` by DECIDE_TAC THEN PROVE_TAC[]
      ]
    ]
  ],

  EXISTS_TAC ``t:num`` THEN
  ASM_SIMP_TAC arith_ss [],

  EXISTS_TAC ``k:num`` THEN
  ASM_SIMP_TAC arith_ss [] THEN
  rpt STRIP_TAC THEN
  Cases_on `j = t` THENL [
    PROVE_TAC[],
    `j <= PRE t` by DECIDE_TAC THEN PROVE_TAC[]
  ]
]
QED

Theorem LTL_EVENTUAL___PALWAYS :
    !k w p. LTL_SEM_TIME k w (LTL_EVENTUAL p) ==>
            !l. l <= k ==> LTL_SEM_TIME l w (LTL_EVENTUAL p)
Proof
    REWRITE_TAC [LTL_SEM_THM]
 >> rpt STRIP_TAC
 >> EXISTS_TAC ``k':num``
 >> ASM_REWRITE_TAC []
 >> DECIDE_TAC
QED

Theorem LTL_WEAK_UNTIL___ALTERNATIVE_DEF :
    !f1 f2. LTL_EQUIVALENT (LTL_UNTIL(f1,f2))
                           (LTL_NOT (LTL_SUNTIL(LTL_NOT f2, LTL_AND(LTL_NOT f1, LTL_NOT f2))))
Proof
    SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_UNTIL_def, LTL_SEM_THM]
 >> rpt STRIP_TAC
 >> EQ_TAC THEN rpt STRIP_TAC THENL [
      Cases_on `k < k'` THENL [
         `t <= k` by DECIDE_TAC THEN
         METIS_TAC[],

         Cases_on `~(k' >= t)` THEN1 ASM_REWRITE_TAC[] THEN
         Cases_on `k' = k`  THEN1 ASM_REWRITE_TAC[] THEN
         `t <= k' /\ k' < k` by DECIDE_TAC THEN
         METIS_TAC[]
      ],

      METIS_TAC[],

      Cases_on `!k. k >= t ==> LTL_SEM_TIME k w f1` THENL [
         PROVE_TAC[],

         DISJ1_TAC THEN
         SIMP_ASSUMPTIONS_TAC std_ss [] THEN
         SUBGOAL_TAC `?k. (k >= t /\ ~LTL_SEM_TIME k w f1) /\
                          !k'. k' < k ==> ~(k' >= t /\ ~LTL_SEM_TIME k' w f1)` THEN1 (
            ASSUME_TAC (EXISTS_LEAST_CONV ``?k. k >= t /\ ~LTL_SEM_TIME k w f1``) THEN
            RES_TAC THEN PROVE_TAC[]
         ) THEN
         SUBGOAL_TAC `?l:num. l >= t /\ l <= k' /\ LTL_SEM_TIME l w f2` THEN1 (
            Cases_on `LTL_SEM_TIME k' w f2` THENL [
               EXISTS_TAC ``k':num`` THEN
               ASM_SIMP_TAC arith_ss [],

               `?j. t <= j /\ j < k' /\ LTL_SEM_TIME j w f2` by METIS_TAC[] THEN
               EXISTS_TAC ``j:num`` THEN
               ASM_SIMP_TAC arith_ss []
            ]
         ) THEN
         EXISTS_TAC ``l:num`` THEN
         ASM_SIMP_TAC arith_ss [] THEN
         rpt STRIP_TAC THEN
         `j < k' /\ j >= t` by DECIDE_TAC THEN
         METIS_TAC[]
      ]
   ]
QED

Theorem LTL_PAST_WEAK_UNTIL___ALTERNATIVE_DEF :
    !f1 f2. LTL_EQUIVALENT (LTL_PUNTIL(f1,f2))
                           (LTL_NOT (LTL_PSUNTIL(LTL_NOT f2, LTL_AND(LTL_NOT f1, LTL_NOT f2))))
Proof
    SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_PUNTIL_def, LTL_SEM_THM]
 >> rpt STRIP_TAC
 >> EQ_TAC THEN rpt STRIP_TAC THENL [
      Cases_on `k' < k` THENL [
         `k' < k` by DECIDE_TAC THEN
         METIS_TAC[],

         Cases_on `~(k' <= t)` THEN1 ASM_REWRITE_TAC[] THEN
         Cases_on `k' = k`  THEN1 ASM_REWRITE_TAC[] THEN
         `k < k'` by DECIDE_TAC THEN
         METIS_TAC[]
      ],

      METIS_TAC[],

      LEFT_DISJ_TAC THEN
      SIMP_ALL_TAC std_ss [] THEN
      `?P. P = \k. k <= t /\ ~(LTL_SEM_TIME k w f1)` by METIS_TAC[] THEN
      SUBGOAL_TAC `?x. P x /\ !z. z > x ==> ~(P z)` THEN1 (
        ASM_SIMP_TAC std_ss [GSYM arithmeticTheory.EXISTS_GREATEST] THEN
        rpt STRIP_TAC THENL [
          METIS_TAC[],

          Q_TAC EXISTS_TAC `t` THEN
          SIMP_TAC arith_ss []
        ]
      ) THEN
      NTAC 2 (UNDISCH_HD_TAC) THEN
      ASM_SIMP_TAC std_ss [] THEN
      rpt STRIP_TAC THEN
      SUBGOAL_TAC `?x'. (x' >= x)  /\ (x' <= t) /\ LTL_SEM_TIME x' w f2` THEN1 (
        Q_SPEC_NO_ASSUM 6 `x` THEN
        CLEAN_ASSUMPTIONS_TAC THENL [
          EXISTS_TAC ``x:num`` THEN
          ASM_SIMP_TAC arith_ss [],

          EXISTS_TAC ``j:num`` THEN
          ASM_SIMP_TAC arith_ss []
        ]
      ) THEN
      Q_TAC EXISTS_TAC `x'` THEN
      ASM_SIMP_TAC arith_ss [] THEN
      rpt STRIP_TAC THEN
      `j > x` by DECIDE_TAC THEN
      METIS_TAC[]
  ]
QED

Theorem LTL_STRONG___WEAK__IMPL___UNTIL :
    !k w p1 p2. LTL_SEM_TIME k w (LTL_SUNTIL(p1, p2)) ==>
                LTL_SEM_TIME k w (LTL_UNTIL(p1, p2))
Proof
    REWRITE_TAC [LTL_UNTIL_def, LTL_OR_SEM]
 >> PROVE_TAC []
QED

Theorem LTL_COND___OR :
    !k w c p1 p2. LTL_SEM_TIME k w (LTL_COND (c, p1, p2)) ==>
                  LTL_SEM_TIME k w (LTL_OR (p1, p2))
Proof
    REWRITE_TAC [LTL_SEM_THM, LTL_COND_def]
 >> METIS_TAC []
QED

Theorem LTL_MONOTICITY_LAWS :
    !As Aw Bs Bw v. (!t. LTL_SEM_TIME t v Aw ==> LTL_SEM_TIME t v As) /\
                    (!t. LTL_SEM_TIME t v Bw ==> LTL_SEM_TIME t v Bs) ==>
         (!t. LTL_SEM_TIME t v (LTL_NOT As) ==> LTL_SEM_TIME t v (LTL_NOT Aw)) /\
         (!t. LTL_SEM_TIME t v (LTL_NEXT Aw) ==> LTL_SEM_TIME t v (LTL_NEXT As)) /\
         (!t. LTL_SEM_TIME t v (LTL_AND(Aw, Bw)) ==> LTL_SEM_TIME t v (LTL_AND(As, Bs))) /\
         (!t. LTL_SEM_TIME t v (LTL_OR(Aw, Bw)) ==> LTL_SEM_TIME t v (LTL_OR(As, Bs))) /\
         (!t. LTL_SEM_TIME t v (LTL_ALWAYS Aw) ==> LTL_SEM_TIME t v (LTL_ALWAYS As)) /\
         (!t. LTL_SEM_TIME t v (LTL_EVENTUAL Aw) ==> LTL_SEM_TIME t v (LTL_EVENTUAL As)) /\
         (!t. LTL_SEM_TIME t v (LTL_UNTIL(Aw, Bw)) ==> LTL_SEM_TIME t v (LTL_UNTIL(As, Bs))) /\
         (!t. LTL_SEM_TIME t v (LTL_SUNTIL(Aw, Bw)) ==> LTL_SEM_TIME t v (LTL_SUNTIL(As, Bs))) /\
         (!t. LTL_SEM_TIME t v (LTL_BEFORE(Aw, Bs)) ==> LTL_SEM_TIME t v (LTL_BEFORE(As, Bw))) /\
         (!t. LTL_SEM_TIME t v (LTL_SBEFORE(Aw, Bs)) ==> LTL_SEM_TIME t v (LTL_SBEFORE(As, Bw))) /\
         (!t. LTL_SEM_TIME t v (LTL_PNEXT Aw) ==> LTL_SEM_TIME t v (LTL_PNEXT As)) /\
         (!t. LTL_SEM_TIME t v (LTL_PSNEXT Aw) ==> LTL_SEM_TIME t v (LTL_PSNEXT As)) /\
         (!t. LTL_SEM_TIME t v (LTL_PALWAYS Aw) ==> LTL_SEM_TIME t v (LTL_PALWAYS As)) /\
         (!t. LTL_SEM_TIME t v (LTL_PEVENTUAL Aw) ==> LTL_SEM_TIME t v (LTL_PEVENTUAL As)) /\
         (!t. LTL_SEM_TIME t v (LTL_PUNTIL(Aw, Bw)) ==> LTL_SEM_TIME t v (LTL_PUNTIL(As, Bs))) /\
         (!t. LTL_SEM_TIME t v (LTL_PSUNTIL(Aw, Bw)) ==> LTL_SEM_TIME t v (LTL_PSUNTIL(As, Bs))) /\
         (!t. LTL_SEM_TIME t v (LTL_PBEFORE(Aw, Bs)) ==> LTL_SEM_TIME t v (LTL_PBEFORE(As, Bw))) /\
         (!t. LTL_SEM_TIME t v (LTL_PSBEFORE(Aw, Bs)) ==> LTL_SEM_TIME t v (LTL_PSBEFORE(As, Bw)))
Proof
    REWRITE_TAC [LTL_SEM_THM, LTL_UNTIL_def, LTL_BEFORE_def, LTL_SBEFORE_def,
                 LTL_PUNTIL_def, LTL_PBEFORE_def, LTL_PSBEFORE_def]
 >> METIS_TAC []
QED

val _ = export_theory();
