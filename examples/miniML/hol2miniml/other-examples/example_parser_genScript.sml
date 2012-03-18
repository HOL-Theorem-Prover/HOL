open HolKernel Parse boolLib bossLib; val _ = new_theory "example_parser_gen";

open ml_translatorLib;
open slr_parser_genTheory;
open stringTheory listTheory;


val CHAR_def = Define `
  CHAR (c:char) = NUM (ORD c)`;

val _ = add_type_inv ``CHAR``

val EqualityType_CHAR = prove(
  ``EqualityType CHAR``,
  EVAL_TAC THEN SRW_TAC [] [] THEN EVAL_TAC) |> store_eq_thm;




(* register ptree -- begin *)

val _ = register_type ``:'a list``

(*

val list_CONG = store_thm("list_CONG",
  ``!l1 l2 P P'.
      (l1 = l2) /\ (!x. MEM x l2 ==> (P x = P' x)) ==>
      (list P l1 = list P' l2)``,
  Induct THEN Cases_on `l2` THEN SIMP_TAC (srw_ss()) [FUN_EQ_THM]
  THEN ONCE_REWRITE_TAC [fetch "-" "list_def"]
  THEN SIMP_TAC std_ss [] THEN METIS_TAC []);

*)

(* val _ = register_type ``:ptree`` *)

val ty = ``:ptree``

val _ = delete_const "ptree" handle _ => ()

val tm =
  ``(ptree (Leaf x1_1) v ⇔
   ∃v1_1. (v = Conv (SOME "LEAF") [v1_1]) ∧ list CHAR x1_1 v1_1) ∧
  (ptree (Node x2_1 x2_2) v ⇔
   ∃v2_1 v2_2.
     (v = Conv (SOME "NODE") [v2_1; v2_2]) ∧ list CHAR x2_1 v2_1 ∧
     list (\x v. if MEM x x2_2 then ptree x v else ARB) x2_2 v2_2)``

val inv_def = tDefine "ptree_def" [ANTIQUOTE tm]
 (WF_REL_TAC `measure (ptree_size o FST)`
  THEN STRIP_TAC THEN Induct
  THEN EVAL_TAC THEN SIMP_TAC std_ss []
  THEN REPEAT STRIP_TAC THEN RES_TAC
  THEN FULL_SIMP_TAC std_ss [] THEN DECIDE_TAC)

val list_SIMP = prove(
  ``!xs b. list (\x v. if b x \/ MEM x xs then p x v else q) xs = list p xs``,
  Induct
  THEN FULL_SIMP_TAC std_ss [FUN_EQ_THM,fetch "-" "list_def",MEM,DISJ_ASSOC])
  |> Q.SPECL [`xs`,`\x.F`] |> SIMP_RULE std_ss [];

val inv_def = inv_def |> SIMP_RULE std_ss [list_SIMP]
                      |> CONV_RULE (DEPTH_CONV ETA_CONV)

val _ = set_inv_def (ty,inv_def)

val _ = register_type ``:ptree``

(* register ptree -- end *)

val res = translate listTheory.HD;
val res = translate listTheory.TL;
val res = translate listTheory.LENGTH;
val res = translate listTheory.MAP;
val res = translate listTheory.APPEND;
val res = translate listTheory.REV_DEF;
val res = translate listTheory.REVERSE_REV;
val res = translate pairTheory.FST;
val res = translate pairTheory.SND;
val res = translate combinTheory.o_DEF;
val res = translate optionTheory.THE_DEF;
val res = translate LET_DEF;

val res = translate push_def;
val res = translate pop_def;
val res = translate take1_def;
val res = translate take_def;
val res = translate isNonTmnlSym_def;
val res = translate sym2Str_def;
val res = translate ruleRhs_def;
val res = translate ruleLhs_def;
val res = translate ptree2Sym_def;
val res = translate buildTree_def;
val res = translate addRule_def;
val res = translate stackSyms_def;
val res = translate findItemInRules_def;
val res = translate itemEqRuleList_def;
val res = translate getState_def;
val res = translate stackSyms_def;
val res = translate exitCond_def;
val res = translate init_def;
val res = translate doReduce_def;
val res = translate parse_def;

val _ = export_theory();

