open HolKernel Parse boolLib bossLib;

open transferTheory tcallUnifTheory nfmbstTheory
open pred_setTheory finite_mapTheory transferLib

val _ = new_theory "rmfmap";

Definition rcorevwalk_def:
  rcorevwalk b v = corevwalk (bst_to_fm b) v
End


Theorem NFMBST_corewalk[transfer_rule]:
  (NFMBST (=) |==> (=) |==> (=)) corevwalk rcorevwalk
Proof
  simp[FUN_REL_def, rcorevwalk_def] >> rpt strip_tac >>
  drule bst_to_fm_correct >> simp[]
QED

Definition TERMREL_def:
  (TERMREL AB (Var n) t ⇔ t = Var n) ∧
  (TERMREL AB (Pair t11 t12) t ⇔ ∃t21 t22. t = Pair t21 t22 ∧
                                           TERMREL AB t11 t21 ∧
                                           TERMREL AB t12 t22) ∧
  (TERMREL AB (Const c1) t ⇔ ∃c2. AB c1 c2 ∧ t = Const c2)
End

Theorem TERMREL_EQ[transfer_simp]:
  TERMREL (=) = (=)
Proof
  simp[FUN_EQ_THM] >> Induct >> simp[TERMREL_def] >> metis_tac[]
QED

Theorem term_CASE_CONG[transfer_rule]:
  (TERMREL AB |==> ((=) |==> CD) |==> (TERMREL AB |==> TERMREL AB |==> CD) |==>
   (AB |==> CD) |==> CD) term_CASE term_CASE
Proof
  simp[FUN_REL_def] >> Cases >> simp[TERMREL_def, PULL_EXISTS]
QED

(*
val _ = show_assums := true
val base = transfer_skeleton true (concl th)
val th = base

val rdb = global_ruledb()
val cleftp = true

val th0 = last (seq.take 3 (resolve_relhyps ["EXP"] true (global_ruledb()) th))
val th = seq.hd (resolve_relhyps ["vR"] true (global_ruledb()) th)

val th = th0
*)


Theorem rcorevwalk_thm =
  transfer_thm 5 ["corevwalk"] true (global_ruledb()) (GEN_ALL corevwalk_thm)

Definition rvR_def:
  rvR b u v = vR (bst_to_fm b) u v
End

Theorem NFMBST_rvR[transfer_rule]:
  (NFMBST (=) |==> (=) |==> (=) |==> (=)) vR rvR
Proof
  simp[FUN_REL_def, rvR_def] >> rpt strip_tac >>
  drule bst_to_fm_correct >> simp[]
QED

Theorem rvR_thm =
        transfer_thm 10 ["vR", "FLOOKUP", "option_CASE"]
                     true (global_ruledb())
                     (INST_TYPE [alpha |-> “:num”] substTheory.vR_def)


val _ = export_theory();

