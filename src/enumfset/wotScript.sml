(* file wotScirpt.sml; author F.L.Morris; created as Script file. 2/24/10 *)
(* Proves the well-ordering theorem for an arbitrary HOL type, beginning
  with the existence of a total order, stealing ideas from the proof of
  Zorn's Lemma in Halmos's Naive Set Theory, and trying to streamline by
  using the whole (arbitrary) type 'x in place of an explicit set X. *)

(* ******************************************************************* *)
(* Revised Oct. 2013 to export just one theorem StrongWellOrderExists: *)
(*                                                                     *)
(*  |- ?R:'a reln. StrongLinearOrder R /\ WF R                         *)
(*                                                                     *)
(* expressed with constants from relationTheory.                       *)
(* ******************************************************************* *)

structure wotScript = struct

open HolKernel boolLib Parse bossLib;
val _ = set_trace "Unicode" 0;
open pred_setLib pred_setTheory relationTheory;

val _ = new_theory "wot";

val AR = ASM_REWRITE_TAC [];
fun ulist x = [x];

val _ = type_abbrev ("reln", ``:'a->'a->bool``);

(* Generalities that I don't find in pred_setTheory *)

val leibniz_law = prove (``!a b:'a. (a = b) <=> !P. P a <=> P b``,
REPEAT GEN_TAC THEN EQ_TAC THENL
[STRIP_TAC THEN AR
,CONV_TAC LEFT_IMP_FORALL_CONV THEN
 EXISTS_TAC ``\c:'a. a = c`` THEN CONV_TAC (ONCE_DEPTH_CONV BETA_CONV) THEN
 REWRITE_TAC []]);

val set_leibniz = prove (``!a b:'a. (a = b) = !Q. a IN Q = b IN Q``,
REWRITE_TAC [SPECIFICATION] THEN ACCEPT_TAC leibniz_law);

val PSUBSET_EXISTS = prove (
``!X Y:'a set. X PSUBSET Y ==> ?a. a IN Y /\ a NOTIN X``,
REWRITE_TAC [PSUBSET_DEF, EXTENSION, SUBSET_DEF, EQ_EXPAND] THEN
CONV_TAC (DEPTH_CONV NOT_FORALL_CONV) THEN
REWRITE_TAC [DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
EXISTS_TAC ``x:'a`` THEN AR THEN RES_TAC);

(* missing from relationTheory ( also the corresp. thm. for RC ): *)

val STRORD_trich = prove (
``!R:'a reln. trichotomous R <=> trichotomous (STRORD R)``,
RW_TAC (srw_ss ()) [STRORD, trichotomous] THEN METIS_TAC []);

(* A general set lemma, dual-ish to BIGUNION_SUBSET but only an ==> : *)

val SUBSET_BIGUNION = prove (
``!X:'a set P. (?Y. Y IN P /\ X SUBSET Y) ==> X SUBSET BIGUNION P``,
REPEAT GEN_TAC THEN REWRITE_TAC [SUBSET_DEF, BIGUNION] THEN
CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
REPEAT STRIP_TAC THEN EXISTS_TAC ``Y:'a set`` THEN RES_TAC THEN AR);

(* Make relation symbols to be defined here into infixes: *)

val _ = set_fixity "cpl" (Infixr 850);
val _ = set_fixity "mex_less_eq" (Infix (NONASSOC, 450));
val _ = set_fixity "mex_less" (Infix (NONASSOC, 450));

(* set comparability and inclusion chains: *)

val cpl_def = Define`A:'x set cpl B = A SUBSET B \/ B SUBSET A`;

val cpl_lem = prove (
``!A B:'x set. B cpl A ==> A SUBSET B \/ B PSUBSET A``,
REPEAT STRIP_TAC THEN IMP_RES_TAC cpl_def THEN AR THEN
Cases_on `B:'x set = A` THEN ASM_REWRITE_TAC [SUBSET_REFL, PSUBSET_DEF]);

val chain_def = Define
      `chain (C:'x set set) = !a b. a IN C /\ b IN C ==> a cpl b`;

(* define a "successor" on (all) subsets of 'x. *)

val mex_def = Define`mex (s:'x set) = CHOICE (COMPL s)`;

val setsuc_def = Define`setsuc (s:'x set) = mex s INSERT s`;

val setsuc_incr = prove (``!s:'x set. s SUBSET setsuc s``,
REWRITE_TAC [SUBSET_DEF, setsuc_def, IN_INSERT] THEN
REPEAT STRIP_TAC THEN AR);

(* define closure under "successor". *)

val succl_def = Define`succl (c:'x set set) = !s. s IN c ==> setsuc s IN c`;

(* and closure under unions of chains *)

val uncl_def = Define
`uncl (c:'x set set) = !w. w SUBSET c /\ chain w ==> BIGUNION w IN c`;

(* and the combination (uncl entails containing the empty set): *)

val tower_def = Define`tower (A:'x set set) = succl A /\ uncl A`;

(* We prefer to treat tower as a predicate: *)

val IN_tower = prove (``!r:'x set set. r IN tower <=> tower r``,
REWRITE_TAC [SPECIFICATION]);

(* Now the big move that also starts Zorn's lemma proof in Halmos: *)

val t0_def = Define`t0:'x set set = BIGINTER tower`;

(* We will prove, in imitation of Halmos/Zermelo/Zorn, chain (t0) . *)

(* No need here for general orders: SUBSET is it. *)

val tower_t0 = prove (``tower (t0:'x set set)``,
REWRITE_TAC [tower_def, t0_def, succl_def, uncl_def, IN_BIGINTER] THEN
REWRITE_TAC [IN_tower] THEN CONJ_TAC THENL
[REPEAT STRIP_TAC THEN IMP_RES_TAC tower_def THEN
 RES_TAC THEN IMP_RES_TAC succl_def
,REWRITE_TAC [BIGINTER, uncl_def, SUBSET_DEF] THEN
 CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
 REWRITE_TAC [IN_tower, tower_def] THEN REPEAT STRIP_TAC THEN
 MATCH_MP_TAC (REWRITE_RULE [uncl_def] (ASSUME ``uncl (P:'x set set)``)) THEN
 ASM_REWRITE_TAC [SUBSET_DEF] THEN REPEAT STRIP_TAC THEN RES_TAC]);

val least_t0 = prove (
``!t:'x set set. tower t ==> t0 SUBSET t``,
REPEAT STRIP_TAC THEN
REWRITE_TAC [t0_def, BIGINTER, SUBSET_DEF, IN_tower] THEN
GEN_TAC THEN CONV_TAC (LAND_CONV SET_SPEC_CONV) THEN
REPEAT STRIP_TAC THEN RES_TAC);

val [t0_succl, t0_uncl] = CONJ_LIST 2 (REWRITE_RULE [tower_def] tower_t0);

(*   t0_succl = |- succl t0            t0_uncl = |- uncl t0   *)

(* We set out to prove that t0 is a chain. *)

(* Try Halmos's "comparable" as a predicate, and not nec. only on t0. *)

val comparable_def = Define`comparable (p:'x set) = !q. q IN t0 ==> p cpl q`;

val psub_lem = prove (``!A B:'x set. A PSUBSET B ==> ~(B PSUBSET setsuc A)``,
REPEAT GEN_TAC THEN
REWRITE_TAC [setsuc_def, PSUBSET_DEF, SUBSET_DEF, IN_INSERT, EXTENSION] THEN
CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV NOT_FORALL_CONV) THENC
          RAND_CONV (ONCE_DEPTH_CONV (REWR_CONV EQ_IMP_THM))) THEN
REWRITE_TAC [EQ_EXPAND, DE_MORGAN_THM] THEN STRIP_TAC THEN
REWRITE_TAC [GSYM IMP_DISJ_THM] THEN STRIP_TAC THEN GEN_TAC THEN AR THENL
[RES_TAC THEN UNDISCH_THEN ``x:'x = mex A`` (SUBST1_TAC o SYM) THEN
 STRIP_TAC THEN AR THEN RES_TAC
,RES_TAC]);

val gAC_lem = prove (``!C:'x set. comparable C ==>
                        !A. A IN t0 /\ A PSUBSET C ==> setsuc A SUBSET C``,
REPEAT STRIP_TAC THEN
IMP_RES_TAC (REWRITE_RULE [succl_def] t0_succl) THEN
IMP_RES_TAC psub_lem THEN IMP_RES_TAC comparable_def THEN
IMP_RES_TAC cpl_lem);

(* Above, and all about U to follow now, straight steals from Halmos *)

val U_def = Define`U (C:'x set) = { A | A IN t0 /\
                                        (A SUBSET C \/ setsuc C SUBSET A)}`;

val IN_U = prove (``!C:'x set A. A IN U C <=>
                           A IN t0 /\ (A SUBSET C \/ setsuc C SUBSET A)``,
REPEAT GEN_TAC THEN REWRITE_TAC [U_def] THEN
CONV_TAC (LAND_CONV SET_SPEC_CONV) THEN REFL_TAC);

val U_lem = prove (``!C A:'x set. A IN U C ==> A cpl setsuc C``,
REPEAT GEN_TAC THEN REWRITE_TAC [cpl_def, IN_U] THEN STRIP_TAC THEN
AR THEN DISJ1_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
EXISTS_TAC ``C:'x set`` THEN ASM_REWRITE_TAC [setsuc_incr]);

val tower_U = prove (
``!C:'x set. C IN t0 /\ comparable C ==> tower (U C)``,
RW_TAC bool_ss [tower_def] THENL
[REWRITE_TAC [succl_def, IN_U] THEN
 GEN_TAC THEN STRIP_TAC THEN (CONJ_TAC THENL
       [IMP_RES_TAC (REWRITE_RULE [succl_def] t0_succl), ALL_TAC]) THENL
 [Cases_on `s:'x set PSUBSET C` THENL
  [DISJ1_TAC THEN IMP_RES_TAC gAC_lem
  ,DISJ2_TAC THEN
   IMP_RES_THEN (ASSUME_TAC o
                 CONV_RULE (CONTRAPOS_CONV THENC REWRITE_CONV [NOT_CLAUSES]))
                PSUBSET_DEF THEN
   RES_TAC THEN ASM_REWRITE_TAC [SUBSET_REFL]
  ]
 ,DISJ2_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC ``s:'x set`` THEN
  ASM_REWRITE_TAC [setsuc_incr]
 ]
,REWRITE_TAC [uncl_def, U_def] THEN
 GEN_TAC THEN CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV SUBSET_DEF)) THENC
                        ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
 REPEAT STRIP_TAC THENL
 [MATCH_MP_TAC (REWRITE_RULE [uncl_def] t0_uncl) THEN AR THEN
  REWRITE_TAC [SUBSET_DEF] THEN REPEAT STRIP_TAC THEN RES_TAC
 ,Cases_on `!A:'x set. A IN w ==> A SUBSET C` THENL
  [DISJ1_TAC THEN REWRITE_TAC [BIGUNION_SUBSET] THEN AR
  ,DISJ2_TAC THEN MATCH_MP_TAC SUBSET_BIGUNION THEN
   UNDISCH_TAC ``~!A:'x set. A IN w ==> A SUBSET C`` THEN
   CONV_TAC (LAND_CONV NOT_FORALL_CONV) THEN REWRITE_TAC [NOT_IMP] THEN
   STRIP_TAC THEN EXISTS_TAC ``A:'x set`` THEN AR THEN RES_TAC
]]]);

val U_conclusion = prove (
 ``!C:'x set. C IN t0 /\ comparable C ==> (U C = t0)``,
REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
[REWRITE_TAC  [IN_U, SUBSET_DEF] THEN REPEAT STRIP_TAC THEN AR
,IMP_RES_TAC tower_U THEN IMP_RES_TAC least_t0]);

(* Prepare to show (comparable INTER t0) is a tower. *)

val comp_setsuc_comp = prove (
     ``!C:'x set. C IN t0 /\ comparable C ==> comparable (setsuc C)``,
REPEAT STRIP_TAC THEN REWRITE_TAC [comparable_def] THEN GEN_TAC THEN
IMP_RES_TAC (GSYM U_conclusion) THEN AR THEN
REWRITE_TAC [U_def] THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
REWRITE_TAC [cpl_def] THEN STRIP_TAC THEN AR THEN
DISJ2_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC ``C:'x set`` THEN 
ASM_REWRITE_TAC [setsuc_incr]);

(* "Since the union of a chain of comparable sets is comparable... ." *)

val uchain_comp = prove (``uncl (comparable:'x set set)``,
REWRITE_TAC [uncl_def, chain_def, SUBSET_DEF] THEN GEN_TAC THEN
REWRITE_TAC [ISPEC ``comparable:'x set set`` SPECIFICATION] THEN
REWRITE_TAC [comparable_def, cpl_def] THEN
REPEAT STRIP_TAC THEN
Cases_on `!x:'x set. x IN w ==> x SUBSET q` THENL
[DISJ1_TAC THEN ASM_REWRITE_TAC [BIGUNION_SUBSET]
,DISJ2_TAC THEN UNDISCH_TAC ``~!x:'x set. x IN w ==> x SUBSET q`` THEN
 CONV_TAC (LAND_CONV NOT_FORALL_CONV) THEN REWRITE_TAC [NOT_IMP] THEN
 STRIP_TAC THEN MATCH_MP_TAC SUBSET_BIGUNION THEN
 EXISTS_TAC ``x:'x set`` THEN AR THEN RES_TAC
]);

val tower_comp = prove (
``tower (t0:'x set set INTER comparable)``,
REWRITE_TAC [tower_def, IN_INTER, succl_def, uncl_def] THEN
REWRITE_TAC [ISPEC ``comparable:'x set set`` SPECIFICATION] THEN
REWRITE_TAC [SUBSET_INTER] THEN REPEAT STRIP_TAC THENL
[IMP_RES_TAC (REWRITE_RULE [succl_def] t0_succl)
,IMP_RES_TAC comp_setsuc_comp
,IMP_RES_TAC (REWRITE_RULE [uncl_def] t0_uncl)
,IMP_RES_TAC (REWRITE_RULE [uncl_def, SPECIFICATION] uchain_comp)]);

val chain_t0 = prove (``chain (t0:'x set set)``,
SUBGOAL_THEN ``t0:'x set set SUBSET t0 INTER comparable``
             (MP_TAC o REWRITE_RULE [SUBSET_INTER, SUBSET_REFL]) THENL
[MATCH_MP_TAC least_t0 THEN ACCEPT_TAC tower_comp
,REWRITE_TAC [SUBSET_DEF, ISPEC ``comparable:'x set set`` SPECIFICATION] THEN
 REWRITE_TAC [chain_def, comparable_def] THEN
 REPEAT STRIP_TAC THEN RES_TAC]);

(* Existence of a maximal set in t0 is "UNIV IN t0", but not needed here. *)

(* Now we diverge from Zorn's lemma proof: prove SUBSET wellorders t0. *)

(* Imitation of gAC_lem for t0, now known to be a chain: *)

val psub_setsuc = prove (``!s t:'x set.
               s IN t0 /\ t IN t0 ==> s PSUBSET t ==> setsuc s SUBSET t``,
REPEAT STRIP_TAC THEN
IMP_RES_TAC (REWRITE_RULE [succl_def] t0_succl) THEN
IMP_RES_TAC psub_lem THEN
ASSUME_TAC (MATCH_MP (REWRITE_RULE [chain_def] chain_t0)
                     (CONJ (ASSUME ``t:'x set IN t0``)
                           (ASSUME ``setsuc (s:'x set) IN t0``))) THEN
IMP_RES_TAC cpl_lem);

(* just a lemma: *)

val dilemlem = prove (``!B:'x set set. (?a. !y. y IN B ==> a NOTIN y) ==>
                            setsuc (BIGUNION B) NOTIN B``,
GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [setsuc_def, mex_def] THEN
SUBGOAL_THEN ``CHOICE (COMPL (BIGUNION (B:'x set set))) IN
                       COMPL (BIGUNION (B))`` MP_TAC THENL
[MATCH_MP_TAC CHOICE_DEF THEN
 REWRITE_TAC [GSYM MEMBER_NOT_EMPTY, COMPL_DEF] THEN
 EXISTS_TAC ``a:'x`` THEN REWRITE_TAC [IN_DIFF, IN_UNIV, BIGUNION] THEN
 CONV_TAC (RAND_CONV SET_SPEC_CONV THENC NOT_EXISTS_CONV) THEN GEN_TAC THEN
 REWRITE_TAC [DE_MORGAN_THM, GSYM IMP_DISJ_THM] THEN STRIP_TAC THEN RES_TAC
,REWRITE_TAC [IN_COMPL, IN_BIGUNION] THEN
 CONV_TAC (LAND_CONV NOT_EXISTS_CONV) THEN
 REWRITE_TAC [DE_MORGAN_THM, GSYM IMP_DISJ_THM] THEN DISCH_TAC THEN
 SUBGOAL_THEN ``CHOICE (COMPL (BIGUNION (B:'x set set))) IN
                CHOICE (COMPL (BIGUNION (B))) INSERT BIGUNION B``
              (fn th => ASSUME_TAC th THEN RES_TAC) THEN
 REWRITE_TAC [IN_INSERT]
]);

(* Now show that t0 is well-ordered by SUBSET (not a case of WeakWellOrder
because it does not extend over all of 'x set); there look to be two
cases: If the union of the subsets of everybody in B is itself in B,
then it is the minimum of B; but if it is a limit set, it may not be in B,
in which case its successor is the minimum. "lub_sub" is that union. *)

val lub_sub_def = Define`lub_sub (B:'x set set) =
              BIGUNION {y | y IN t0 /\ !x. x IN B ==> y SUBSET x}`;

val lub_sub_in_t0 = prove (
``!B:'x set set. B SUBSET t0 ==> lub_sub B IN t0``,
REWRITE_TAC [SUBSET_DEF] THEN REPEAT STRIP_TAC THEN
REWRITE_TAC [lub_sub_def] THEN
MATCH_MP_TAC (REWRITE_RULE [uncl_def] t0_uncl) THEN
CONV_TAC (LAND_CONV (REWR_CONV SUBSET_DEF)) THEN
REWRITE_TAC [chain_def] THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
ASSUME_TAC (REWRITE_RULE [chain_def] chain_t0) THEN
REPEAT STRIP_TAC THEN AR THEN RES_TAC);

val setsuc_sub = prove (
``!B:'x set set. B SUBSET t0 /\ lub_sub B NOTIN B ==>
  !x. x IN B ==> lub_sub B PSUBSET x /\ setsuc (lub_sub B) SUBSET x``,
GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
SUBGOAL_THEN ``lub_sub B PSUBSET (x:'x set)`` ASSUME_TAC THENL
[REWRITE_TAC [PSUBSET_DEF] THEN CONJ_TAC THENL
 [REWRITE_TAC [lub_sub_def, SUBSET_DEF, IN_BIGUNION] THEN
  CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT STRIP_TAC THEN RES_TAC
 ,ONCE_REWRITE_TAC [set_leibniz] (* loops if not "ONCE_" *) THEN
  CONV_TAC NOT_FORALL_CONV THEN EXISTS_TAC ``B:'x set set`` THEN AR
 ]
,AR THEN
 IMP_RES_TAC (REWRITE_RULE [SUBSET_DEF] (ASSUME ``B:'x set set SUBSET t0``))
 THEN IMP_RES_TAC lub_sub_in_t0 THEN
 MATCH_MP_TAC (MATCH_MP psub_setsuc 
               (CONJ (ASSUME ``lub_sub (B:'x set set) IN t0``)
                     (ASSUME ``x:'x set IN t0``))) THEN AR
]);

(* The big fish, proof in two cases as advertised above: *)

val wellord_t0 = prove (``!B. B SUBSET t0 /\ B <> {} ==>
                           ?m:'x set. m IN B /\ !b. b IN B ==> m SUBSET b``,
REWRITE_TAC [GSYM MEMBER_NOT_EMPTY] THEN REPEAT STRIP_TAC THEN
EXISTS_TAC ``BIGINTER (B:'x set set)`` THEN
SUBGOAL_THEN ``BIGINTER (B:'x set set) IN B``
(fn BIN => REWRITE_TAC [BIN] THEN
 REWRITE_TAC [BIGINTER, SUBSET_DEF] THEN
 CONV_TAC (DEPTH_CONV SET_SPEC_CONV) THEN REPEAT STRIP_TAC THEN RES_TAC) THEN
Cases_on `lub_sub (B:'x set set) IN B` THENL
[SUBGOAL_THEN ``BIGINTER (B:'x set set) = lub_sub B``
              (ASM_REWRITE_TAC o ulist) THEN
 MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
 [REWRITE_TAC [BIGINTER, SUBSET_DEF] THEN
  GEN_TAC THEN
  CONV_TAC (LAND_CONV SET_SPEC_CONV THENC LEFT_IMP_FORALL_CONV) THEN
  EXISTS_TAC ``lub_sub (B:'x set set)`` THEN AR
 ,REWRITE_TAC [lub_sub_def, BIGINTER, SUBSET_DEF, IN_BIGUNION] THEN
  CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT STRIP_TAC THEN RES_TAC
 ]
,IMP_RES_TAC setsuc_sub THEN
 SUBGOAL_THEN ``setsuc (lub_sub (B:'x set set)) IN B`` ASSUME_TAC THENL
 [SUBGOAL_THEN ``setsuc (lub_sub (B:'x set set)) NOTIN B ==>
          setsuc (lub_sub B) IN {y | y IN t0 /\ !x. x IN B ==> y SUBSET x}``
               MP_TAC THENL
  [CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
   REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC (REWRITE_RULE [succl_def] t0_succl) THEN
    IMP_RES_TAC lub_sub_in_t0
   ,IMP_RES_TAC setsuc_sub
   ]
  ,CONV_TAC CONTRAPOS_CONV THEN
   DISCH_TAC THEN AR THEN
   REWRITE_TAC [lub_sub_def] THEN MATCH_MP_TAC dilemlem THEN
   IMP_RES_TAC PSUBSET_EXISTS THEN EXISTS_TAC ``a:'x`` THEN
   MP_TAC (ASSUME ``a:'x NOTIN lub_sub B``) THEN
   REWRITE_TAC [lub_sub_def, IN_BIGUNION] THEN
   CONV_TAC (LAND_CONV NOT_EXISTS_CONV THENC ONCE_DEPTH_CONV SET_SPEC_CONV)
   THEN REPEAT STRIP_TAC THEN RES_TAC
 ]
 ,SUBGOAL_THEN ``BIGINTER (B:'x set set) = setsuc (lub_sub B)``
              (ASM_REWRITE_TAC o ulist) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
  [REWRITE_TAC [BIGINTER, SUBSET_DEF] THEN
   GEN_TAC THEN
   CONV_TAC (LAND_CONV SET_SPEC_CONV THENC LEFT_IMP_FORALL_CONV) THEN
   EXISTS_TAC ``setsuc (lub_sub (B:'x set set))`` THEN AR
  ,REWRITE_TAC [SUBSET_BIGINTER] THEN GEN_TAC THEN
   DISCH_TAC THEN IMP_RES_TAC lub_sub_in_t0 THEN
   IMP_RES_TAC (REWRITE_RULE [SUBSET_DEF] (ASSUME ``B:'x set set SUBSET t0``))
   THEN MATCH_MP_TAC (MATCH_MP psub_setsuc (CONJ
                       (ASSUME ``(lub_sub B):'x set IN t0``)
                       (ASSUME ``Y:'x set IN t0``))) THEN
   IMP_RES_TAC setsuc_sub
]]]);

(* ***************************************************************** *)

(* Now to prove that the type 'x itself can be well-ordered:
   To each a in 'x we make correspond that set in t0 into which setsuc
   puts a, definable as the union of the a-less sets in t0. *)

val preds_def = Define
             `preds (a:'x) = BIGUNION {s:'x set | s IN t0 /\ a NOTIN s}`;

val preds_in_t0 = prove (``!a:'x. preds a IN t0``,
GEN_TAC THEN REWRITE_TAC [preds_def] THEN
MATCH_MP_TAC (REWRITE_RULE [uncl_def] t0_uncl) THEN CONJ_TAC THENL
 [REWRITE_TAC [SUBSET_DEF] THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT STRIP_TAC
 ,REWRITE_TAC [chain_def] THEN CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
  REPEAT STRIP_TAC THEN IMP_RES_TAC (REWRITE_RULE [chain_def] chain_t0)
 ]);

val a_in_suc_preds = prove (``!a:'x. a IN setsuc (preds a)``,
GEN_TAC THEN
PURE_ONCE_REWRITE_TAC [GSYM (CONJUNCT1 NOT_CLAUSES)] THEN DISCH_TAC THEN
SUBGOAL_THEN ``setsuc (preds (a:'x)) SUBSET preds a`` MP_TAC THENL
[CONV_TAC (RAND_CONV (REWR_CONV preds_def)) THEN
 MATCH_MP_TAC SUBSET_BIGUNION THEN EXISTS_TAC ``setsuc (preds (a:'x))`` THEN
 CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
 ASM_REWRITE_TAC [SUBSET_REFL] THEN
 MATCH_MP_TAC (REWRITE_RULE [succl_def] t0_succl) THEN
 MATCH_ACCEPT_TAC preds_in_t0
,REWRITE_TAC [SUBSET_DEF, setsuc_def, IN_INSERT] THEN
 CONV_TAC NOT_FORALL_CONV THEN EXISTS_TAC ``mex (preds (a:'x))`` THEN
 REWRITE_TAC [mex_def, GSYM IN_COMPL] THEN
 MATCH_MP_TAC CHOICE_DEF THEN
 REWRITE_TAC [GSYM MEMBER_NOT_EMPTY, IN_COMPL] THEN EXISTS_TAC ``a:'x`` THEN
 UNDISCH_TAC ``a:'x NOTIN setsuc (preds a)`` THEN
 REWRITE_TAC [setsuc_def, IN_INSERT, DE_MORGAN_THM] THEN STRIP_TAC]);

val mex_preds = prove (``!a:'x. mex (preds a) = a``,
GEN_TAC THEN CONV_TAC (REWR_CONV EQ_SYM_EQ) THEN
MP_TAC (SPEC_ALL a_in_suc_preds) THEN
REWRITE_TAC [setsuc_def, IN_INSERT] THEN
SUBGOAL_THEN ``a:'x NOTIN preds a`` (REWRITE_TAC o ulist) THEN
REWRITE_TAC [preds_def, IN_BIGUNION] THEN
CONV_TAC (NOT_EXISTS_CONV THENC ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
REPEAT STRIP_TAC);

(* Now define what will be the (weak) order on 'x *)

val mex_less_eq_def = Define`a:'x mex_less_eq b = preds a SUBSET preds b`;

val preds_one_one = prove (
``!x y:'x. (preds x = preds y) <=> (x = y)``,
REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
[CONV_TAC (BINOP_CONV (REWR_CONV (GSYM mex_preds))) THEN AR, AR]);

(* The following is an easy consequence of chain_t0 *)

val TotOrdTheorem = prove (``WeakLinearOrder ($mex_less_eq:'x reln)``,
REWRITE_TAC [WeakLinearOrder, trichotomous, WeakOrder,
      reflexive_def, antisymmetric_def, transitive_def, mex_less_eq_def] THEN
REWRITE_TAC [SUBSET_TRANS, SUBSET_REFL] THEN CONJ_TAC THENL
[REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [GSYM preds_one_one] THEN
 MATCH_ACCEPT_TAC SUBSET_ANTISYM
,REPEAT GEN_TAC THEN REWRITE_TAC [DISJ_ASSOC] THEN DISJ1_TAC
 THEN MATCH_MP_TAC (REWRITE_RULE [cpl_def, chain_def] chain_t0) THEN
 REWRITE_TAC [preds_in_t0]
]);

(* Likewise for the corresponding strong order on 'x *)

val mex_less_def = Define`$mex_less:'x reln = STRORD $mex_less_eq`;

val TotOrdTheorem_ALT = prove (``StrongLinearOrder ($mex_less:'x reln)``,
REWRITE_TAC [mex_less_def, StrongLinearOrder, GSYM STRORD_Strong,
             GSYM STRORD_trich] THEN
CONJ_TAC THENL [MATCH_MP_TAC WeakOrd_Ord, ALL_TAC] THEN
REWRITE_TAC [REWRITE_RULE [WeakLinearOrder] TotOrdTheorem]);

val WeakWellOrder = xDefine "WeakWellOrder"
 `WeakWellOrder (R:'a reln) = WeakOrder R /\ !B. B <> {} ==>
                          ?m. m IN B /\ !b. b IN B ==> R m b`;

val weakwell_weaklinear = prove (
``!R:'a reln. WeakWellOrder R ==> WeakLinearOrder R``,
GEN_TAC THEN REWRITE_TAC [WeakWellOrder, WeakLinearOrder_dichotomy] THEN
CONV_TAC ANTE_CONJ_CONV THEN DISCH_TAC THEN AR THEN
REWRITE_TAC [trichotomous] THEN
DISCH_THEN (fn fa => REPEAT GEN_TAC THEN MP_TAC fa) THEN
CONV_TAC LEFT_IMP_FORALL_CONV THEN EXISTS_TAC ``{a:'a; b}`` THEN
REWRITE_TAC [NOT_INSERT_EMPTY, IN_INSERT, NOT_IN_EMPTY] THEN
CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV EQ_SYM_EQ)) THEN
STRIP_TAC THEN AR THENL [DISJ1_TAC, DISJ2_TAC] THEN
UNDISCH_THEN ``!b':'a. (a = b') \/ (b = b') ==> R (m:'a) b'``
             MATCH_MP_TAC THEN REWRITE_TAC []);

(* The next definition is used only in the annoyingly long proof of the main
  result, which is really an immediate consequence of wellord_t0: *)

val preds_image_def = Define`preds_image (X:'x set) = {preds x | x IN X}`;

val WellOrd_mex_less_eq = prove (``WeakWellOrder ($mex_less_eq:'x reln)``,
REWRITE_TAC [WeakWellOrder, GSYM MEMBER_NOT_EMPTY] THEN
REPEAT STRIP_TAC THENL
[REWRITE_TAC [REWRITE_RULE [WeakLinearOrder] TotOrdTheorem]
,SUBGOAL_THEN
 ``?M. M IN preds_image (B:'x set) /\ !N. N IN preds_image B ==> M SUBSET N``
 STRIP_ASSUME_TAC THENL
 [MATCH_MP_TAC wellord_t0 THEN CONJ_TAC THENL
  [REWRITE_TAC [preds_image_def, SUBSET_DEF] THEN
   CONV_TAC (ONCE_DEPTH_CONV SET_SPEC_CONV) THEN
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [preds_in_t0]
  ,REWRITE_TAC [GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC ``preds (x:'x)`` THEN
   REWRITE_TAC [preds_image_def] THEN CONV_TAC SET_SPEC_CONV THEN
   EXISTS_TAC ``x:'x`` THEN AR
  ]
 ,EXISTS_TAC ``mex (M:'x set)`` THEN
  SUBGOAL_THEN ``?m:'x. (M = preds m) /\ m IN B`` STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC ``M:'x set IN preds_image B`` THEN
   REWRITE_TAC [preds_image_def] THEN CONV_TAC (LAND_CONV SET_SPEC_CONV) THEN
   REWRITE_TAC []
  ,ASM_REWRITE_TAC [mex_preds] THEN
   SUBGOAL_THEN ``!m:'x. m IN B ==> preds m IN preds_image B``
                ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC [preds_image_def] THEN
    CONV_TAC SET_SPEC_CONV THEN EXISTS_TAC ``m':'x`` THEN AR
   ,REPEAT STRIP_TAC THEN REWRITE_TAC [mex_less_eq_def] THEN
    UNDISCH_THEN ``M:'x set = preds m`` (SUBST1_TAC o SYM) THEN
    UNDISCH_THEN ``!N:'x set. N IN preds_image B ==> M SUBSET N``
                 MATCH_MP_TAC THEN RES_TAC
]]]]);

(* Now the same for the strong order. WF is from relationTheory. *)

val StrongWellOrder = xDefine "StrongWellOrder"
         `StrongWellOrder (R:'a reln) = StrongLinearOrder R /\ WF R`;

val weakwell_strongwell = prove (
``!R:'a reln. WeakWellOrder R ==> StrongWellOrder (STRORD R)``,
REPEAT STRIP_TAC THEN
IMP_RES_TAC (REWRITE_RULE [SPECIFICATION, GSYM MEMBER_NOT_EMPTY]
             WeakWellOrder) THEN
IMP_RES_TAC weakwell_weaklinear THEN IMP_RES_TAC WeakLinearOrder THEN
IMP_RES_TAC WeakOrd_Ord THEN IMP_RES_TAC Order THEN
REWRITE_TAC [StrongWellOrder, StrongLinearOrder] THEN
ASM_REWRITE_TAC [GSYM STRORD_trich, GSYM STRORD_Strong, WF_DEF] THEN
REPEAT STRIP_TAC THEN RES_TAC THEN
EXISTS_TAC ``m:'a`` THEN ASM_REWRITE_TAC [STRORD] THEN
GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC [] THEN
DISCH_THEN (ANTE_RES_THEN STRIP_ASSUME_TAC) THEN
STRIP_TAC THEN IMP_RES_TAC antisymmetric_def);

val WellOrd_mex_less = prove (``StrongWellOrder ($mex_less:'x reln)``,
REWRITE_TAC [mex_less_def] THEN MATCH_MP_TAC weakwell_strongwell THEN
ACCEPT_TAC WellOrd_mex_less_eq);

val StrongWellOrderExists = store_thm ("StrongWellOrderExists",
``?R:'a reln. StrongLinearOrder R /\ WF R``,
Q.EXISTS_TAC `$mex_less` THEN
REWRITE_TAC [WellOrd_mex_less, GSYM StrongWellOrder]);

val _ = export_theory ();
val _ = print_theory "-";

end;
