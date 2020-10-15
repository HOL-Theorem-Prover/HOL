structure preamble =
struct
open HolKernel Parse boolLib bossLib;
open ASCIInumbersTheory BasicProvers Defn HolKernel Parse SatisfySimps Tactic
     monadsyntax alistTheory alignmentTheory arithmeticTheory boolLib
     boolSimps bossLib containerTheory combinTheory dep_rewrite
     finite_mapTheory indexedListsTheory listTheory llistTheory
     markerLib mp_then optionTheory pairLib
     pairTheory pred_setTheory quantHeuristicsLib relationTheory
     rich_listTheory sortingTheory stringTheory sumTheory;
val wf_rel_tac = WF_REL_TAC;
val every_case_tac = BasicProvers.EVERY_CASE_TAC;
val full_case_tac = BasicProvers.FULL_CASE_TAC;
val sym_sub_tac = SUBST_ALL_TAC o SYM;
fun asm_match q = Q.MATCH_ASSUM_RENAME_TAC q;
val match_exists_tac = part_match_exists_tac (hd o strip_conj);
val asm_exists_tac = first_assum(match_exists_tac o concl);
val rveq = rpt var_eq_tac;
end
