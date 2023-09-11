open HolKernel Parse boolLib bossLib;

open transferTheory tcallUnifTheory fmspTheory
open pred_setTheory finite_mapTheory transferLib

val _ = new_theory "rmfmap";

Definition rcorevwalk_def:
  rcorevwalk sp v = corevwalk (sp2fm sp) v
End


Theorem FMSP_corewalk[transfer_rule]:
  (FMSP (=) (=) |==> (=) |==> (=)) corevwalk rcorevwalk
Proof
  simp[FUN_REL_def, rcorevwalk_def] >> rpt strip_tac >>
  gs[sp2fm_correct]
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
val th = GEN_ALL corevwalk_thm
val _ = show_assums := true
val base = transfer_skeleton true (concl th)
val th = base

val rdb = global_ruledb()
val cleftp = true

fun fpow f n x = if n <= 0 then x else fpow f (n - 1) (f x)

val F = seq.hd o resolve_relhyps ["vR"] true (global_ruledb())
val th = fpow F 8 th

th |> mkrelsyms_eq true |> eliminate_domrng true (global_ruledb())

*)


Theorem rcorevwalk_thm =
  transfer_thm 5 ["corevwalk"] true (global_ruledb()) (GEN_ALL corevwalk_thm)

Definition rvR_def:
  rvR sp u v = vR (sp2fm sp) u v
End

Theorem FMSP_rvR[transfer_rule]:
  (FMSP (=) (=) |==> (=) |==> (=) |==> (=)) vR rvR
Proof
  simp[FUN_REL_def, rvR_def] >> rpt strip_tac >>
  gs[sp2fm_correct]
QED

Theorem rvR_thm =
        transfer_thm 10 ["vR", "FLOOKUP", "option_CASE"]
                     true (global_ruledb())
                     (INST_TYPE [alpha |-> “:num”] substTheory.vR_def)


val _ = export_theory();

