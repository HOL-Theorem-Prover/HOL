open HolKernel Parse boolLib bossLib; val _ = new_theory "example_parser_gen";

open ml_translatorLib;
open slr_parser_genTheory;
open stringTheory listTheory;


val CHAR_def = Define `
  CHAR (c:char) = NUM (ORD c)`;

val _ = add_type_inv ``CHAR`` ``:num``

val EqualityType_CHAR = prove(
  ``EqualityType CHAR``,
  EVAL_TAC THEN SRW_TAC [] [] THEN EVAL_TAC) |> store_eq_thm;

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

