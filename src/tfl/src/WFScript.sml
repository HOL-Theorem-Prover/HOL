(*---------------------------------------------------------------------------
 * Theorems about various wellfounded relations relating to datatypes.
 *---------------------------------------------------------------------------*)
structure WFScript =
struct

open HolKernel Parse basicHol90Lib QLib Parse
     Num_induct Let_conv pairTools boolTools mesonLib;

infix ORELSE ORELSEC THEN THENC THENL |->;

val _ = new_theory "WF";

val WF_DEF = primWFTheory.WF_DEF;

(*---------------------------------------------------------------------------
 * Some number lemmas.
 *---------------------------------------------------------------------------*)

val NOT_LESS_0 = prim_recTheory.NOT_LESS_0;
val LESS_THM = prim_recTheory.LESS_THM;
val LESS_SUC_REFL = prim_recTheory.LESS_SUC_REFL;
val INV_SUC_EQ = prim_recTheory.INV_SUC_EQ;
val NOT_SUC = numTheory.NOT_SUC;

(*---------------------------------------------------------------------------
 * No infinite descending chains in 'a. Conceptually simpler (to some)
 * than the original definition, which is solely in terms of
 * predicates (and therefore logically simpler).
 *---------------------------------------------------------------------------*)
val wellfounded_def =
Q.new_definition
  ("wellfounded_def",
   `wellfounded (R:'a->'a->bool) = ~?f. !n. R (f (SUC n)) (f n)`);


(*---------------------------------------------------------------------------
 * First half of showing that the two definitions of wellfounded agree.
 *---------------------------------------------------------------------------*)
val WF_IMP_WELLFOUNDED = Q.prove
`!(R:'a->'a->bool). WF R ==> wellfounded R`
(GEN_TAC THEN CONV_TAC CONTRAPOS_CONV
 THEN REWRITE_TAC[wellfounded_def,WF_DEF]
 THEN STRIP_TAC THEN NNF_TAC
 THEN Q.EXISTS_TAC`\p:'a. ?n:num. p = f n`
 THEN BETA_TAC THEN CONJ_TAC THENL
  [MAP_EVERY Q.EXISTS_TAC [`(f:num->'a) n`,  `n`] THEN REFL_TAC,
   GEN_TAC THEN DISCH_THEN (CHOOSE_THEN SUBST1_TAC)
    THEN Q.EXISTS_TAC`f(SUC n)` THEN ASM_REWRITE_TAC[]
    THEN Q.EXISTS_TAC`SUC n` THEN REFL_TAC]);

(*---------------------------------------------------------------------------
 * Second half.
 *---------------------------------------------------------------------------*)
local val RW_TAC     = Rewrite.REWRITE_TAC
      val ASM_RW_TAC = Rewrite.ASM_REWRITE_TAC
in
val WELLFOUNDED_IMP_WF = Q.prove
`!(R:'a->'a->bool). wellfounded R ==> WF R`
(RW_TAC[wellfounded_def,WF_DEF]
  THEN GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN RW_TAC[]
  THEN NNF_TAC THEN REPEAT STRIP_TAC
  THEN Q.EXISTS_TAC`SIMP_REC w (\x. @q. R q x /\ B q)` THEN GEN_TAC
  THEN Q.SUBGOAL_THEN `!n. B(SIMP_REC w (\x. @q. R q x /\ B q) n)`
                      (ASSUME_TAC o SPEC_ALL)
  THENL [INDUCT_TAC,ALL_TAC]
  THEN ASM_RW_TAC[prim_recTheory.SIMP_REC_THM]
  THEN BETA_TAC THEN RES_TAC
  THEN IMP_RES_TAC(BETA_RULE
     (Q.SPEC `\q. R q (SIMP_REC w (\x. @q. R q x /\ B q) n) /\ B q`
              boolTheory.SELECT_AX)))
end;


val WF_IFF_WELLFOUNDED = Q.store_thm("WF_IFF_WELLFOUNDED",
`!(R:'a->'a->bool). WF R = wellfounded R`,
GEN_TAC THEN EQ_TAC THEN STRIP_TAC
  THENL [IMP_RES_TAC WF_IMP_WELLFOUNDED,
         IMP_RES_TAC WELLFOUNDED_IMP_WF]);



(*---------------------------------------------------------------------------
 * The lexicographic combination of two wellfounded orderings is wellfounded.
 * The minimal element of this relation is found by
 *
 *    1. Finding the set of first elements of the pairs in B
 *    2. That set is non-empty, so it has an R-minimal element, call it min
 *    3. Find the set of second elements of those pairs in B whose first
 *       element is min.
 *    4. This set is non-empty, so it has a Q-minimal element, call it min'.
 *    5. A minimal element is (min,min').
 *---------------------------------------------------------------------------*)
val LEX_DEF =
Q.new_infixr_definition
("LEX_DEF",
  `LEX (R1:'a->'a->bool)
     (R2:'b->'b->bool) = \(s,t) (u,v). R1 s u \/ (s=u) /\ R2 t v`, 450);
val WF_LEX = Q.store_thm("WF_LEX",
 `!(R:'a->'a->bool)
   (Q:'b->'b->bool). WF R /\ WF Q ==> WF (R LEX Q)`,
REWRITE_TAC [LEX_DEF, WF_DEF]
  THEN CONV_TAC (DEPTH_CONV LEFT_IMP_EXISTS_CONV)
  THEN REPEAT STRIP_TAC
  THEN Q.SUBGOAL_THEN `?w1. (\v. ?y. B (v,y)) w1`  STRIP_ASSUME_TAC THENL
  [BETA_TAC THEN MAP_EVERY Q.EXISTS_TAC [`FST w`, `SND w`]
     THEN ASM_REWRITE_TAC pairTheory.pair_rws,
   Q.SUBGOAL_THEN
   `?min. (\v. ?y. B (v,y)) min
         /\ !b. R b min ==>
               ~(\v. ?y. B (v,y)) b` STRIP_ASSUME_TAC THENL
   [RES_TAC THEN ASM_MESON_TAC[],
    Q.SUBGOAL_THEN
      `?w2:'b. (\z. B (min:'a,z)) w2` STRIP_ASSUME_TAC THENL
    [BETA_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN ASM_REWRITE_TAC[],
     Q.SUBGOAL_THEN
     `?min':'b. (\z. B (min,z)) min'
       /\  !b. Q b min' ==>
              ~((\z. B (min,z)) b)` STRIP_ASSUME_TAC THENL
     [RES_TAC THEN ASM_MESON_TAC[],
      EXISTS_TAC (Term`(min:'a, (min':'b))`)
       THEN CONV_TAC (DEPTH_CONV Let_conv.GEN_BETA_CONV)
       THEN RULE_ASSUM_TAC BETA_RULE
       THEN ASM_MESON_TAC pairTheory.pair_rws]]]]);

(*---------------------------------------------------------------------------
 * The relational product of two wellfounded relations is wellfounded. This
 * is a consequence of WF_X.
 *---------------------------------------------------------------------------*)
val RPROD_DEF =
Q.new_definition
("RPROD_DEF",
   `RPROD (R1:'a->'a->bool)
          (R2:'b->'b->bool) = \(s,t) (u,v). R1 s u /\ R2 t v`);


val WF_RPROD =
Q.store_thm("WF_RPROD",
 `!(R:'a->'a->bool) (Q:'b->'b->bool). WF R /\ WF Q  ==>  WF(RPROD R Q)`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC primWFTheory.WF_SUBSET
 THEN Q.EXISTS_TAC`R LEX Q`
 THEN CONJ_TAC
 THENL [MATCH_MP_TAC WF_LEX THEN ASM_REWRITE_TAC[],
        REWRITE_TAC[LEX_DEF,RPROD_DEF]
         THEN TUPLE_TAC(Term`(s,t):'a#'b`) THEN GEN_TAC THEN GEN_TAC
         THEN TUPLE_TAC(Term`(u,v):'a#'b`) THEN GEN_TAC THEN GEN_TAC
         THEN CONV_TAC (DEPTH_CONV PAIRED_BETA_CONV)
         THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);


(*---------------------------------------------------------------------------
 * Predecessor and "<" for "num" are wellfounded relations.
 *---------------------------------------------------------------------------*)

val WF_PRED =
Q.store_thm
("WF_PRED",
  `WF \x y. y = SUC x`,
 REWRITE_TAC[WF_DEF] THEN BETA_TAC THEN GEN_TAC
  THEN CONV_TAC(CONTRAPOS_CONV THENC NNF_CONV) THEN DISCH_TAC
  THEN INDUCT_TAC THEN CCONTR_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[])
  THEN RES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[INV_SUC_EQ, GSYM NOT_SUC])
  THENL (map FIRST_ASSUM [ACCEPT_TAC, MATCH_MP_TAC])
  THEN FILTER_ASM_REWRITE_TAC is_eq [] THEN ASM_REWRITE_TAC[]);


(*----------------------------------------------------------------------------
 * This theorem would be a lot nicer if < was defined as the transitive
 * closure of predecessor.
 *---------------------------------------------------------------------------*)
val WF_LESS = Q.store_thm("WF_LESS", `WF $<`,
REWRITE_TAC[WF_DEF]
 THEN GEN_TAC THEN CONV_TAC CONTRAPOS_CONV
 THEN DISCH_THEN (fn th1 =>
       SUBGOAL_THEN (--`^(concl th1) ==> !i j. j<i ==> ~B j`--)
                    (fn th => MP_TAC (MP th th1)))
 THEN CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN DISCH_TAC THENL
  [INDUCT_TAC THEN GEN_TAC THEN
    REWRITE_TAC[NOT_LESS_0,LESS_THM]
    THEN DISCH_THEN (DISJ_CASES_THENL[SUBST1_TAC, ASSUME_TAC])
    THEN STRIP_TAC THEN RES_TAC,
   GEN_TAC THEN FIRST_ASSUM MATCH_MP_TAC
    THEN Q.EXISTS_TAC`SUC w`
    THEN MATCH_ACCEPT_TAC LESS_SUC_REFL]);


(*---------------------------------------------------------------------------
 * Measure functions are definable as inverse image into (<). Every relation
 * arising from a measure function is wellfounded, which is really great!
 *---------------------------------------------------------------------------*)
val measure_def =
Q.new_definition
("measure_def",
  `measure:('a->num)->'a->'a->bool = inv_image $<`);


val WF_measure =
Q.store_thm
("WF_measure",
  `!m:'a->num. WF (measure m)`,
REWRITE_TAC[measure_def]
 THEN MATCH_MP_TAC primWFTheory.WF_inv_image
 THEN ACCEPT_TAC WF_LESS);


(*---------------------------------------------------------------------------
 * Wellfoundedness for lists
 *---------------------------------------------------------------------------*)

val LIST_INDUCT_TAC = INDUCT_THEN listTheory.list_INDUCT ASSUME_TAC;

val WF_LIST_PRED = Q.store_thm("WF_LIST_PRED",
`WF \L1 L2. ?h:'a. L2 = CONS h L1`,
REWRITE_TAC[WF_DEF] THEN BETA_TAC THEN GEN_TAC
  THEN CONV_TAC(CONTRAPOS_CONV THENC NNF_CONV) THEN DISCH_TAC THEN
  LIST_INDUCT_TAC THENL [ALL_TAC,GEN_TAC] THEN CCONTR_TAC THEN
  RULE_ASSUM_TAC (REWRITE_RULE[])  THEN RES_TAC
  THEN RULE_ASSUM_TAC(REWRITE_RULE[listTheory.NOT_NIL_CONS,
                                   listTheory.CONS_11])
  THENL (map FIRST_ASSUM [ACCEPT_TAC, MATCH_MP_TAC]) THEN
  FILTER_ASM_REWRITE_TAC is_conj [] THEN ASM_REWRITE_TAC[]);

val _ = export_theory();

end;
