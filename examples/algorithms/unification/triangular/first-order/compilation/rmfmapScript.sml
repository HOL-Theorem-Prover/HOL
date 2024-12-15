open HolKernel Parse boolLib bossLib;

open transferTheory fmspTheory unifDefTheory
open pred_setTheory finite_mapTheory transferLib

val _ = new_theory "rmfmap";

Theorem FUNREL_flipR:
  (AB |==> CD |==> EF) f (flip g) ⇔ (CD |==> AB |==> EF) (flip f) g
Proof
  simp[FUN_REL_def] >> metis_tac[]
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


Theorem term_CASE_EQCONG[transfer_rule]:
  ((=) |==>
       ((=) |==> CD) |==> (* Var *)
       ((=) |==> (=) |==> CD) |==> (* Pair *)
       ((=) |==> CD) |==> (* Const *)
       CD) term_CASE term_CASE
Proof
  simp[FUN_REL_def] >> Cases >> simp[]
QED

fun xfer th = time (transfer_thm 5 {force_imp = true, cleftp = true, hints = []}
                                 (global_ruledb()))
                                 (GEN_ALL th)

Definition svR_def:
  svR sp u v = vR (sp2fm sp) u v
End

Theorem FMSP_rvR[transfer_rule]:
  (FMSP (=) (=) |==> (=) |==> (=) |==> (=)) vR svR
Proof
  simp[FUN_REL_def, svR_def] >> rpt strip_tac >>
  gs[sp2fm_correct]
QED

Theorem svR_thm = xfer (INST_TYPE [alpha |-> “:num”] substTheory.vR_def)

Definition swfs_def:
  swfs sp = wfs (sp2fm sp)
End

Theorem FMSP_wfs[transfer_rule]:
  (FMSP (=) (=) |==> (=)) wfs swfs
Proof
  simp[FUN_REL_def, swfs_def, sp2fm_correct]
QED

Definition svwalk_def:
  svwalk sp t = vwalk (sp2fm sp) t
End

Theorem FMSP_vwalk[transfer_rule]:
  (FMSP (=) (=) |==> (=) |==> (=)) vwalk svwalk
Proof
  simp[FUN_REL_def, svwalk_def, sp2fm_correct]
QED

Theorem svwalk_thm = xfer walkTheory.vwalk_def

Definition swalk_def:
  swalk sp t = walk (sp2fm sp) t
End

Theorem FMSP_walk[transfer_rule]:
  (FMSP (=) (=) |==> (=) |==> (=)) walk swalk
Proof
  simp[FUN_REL_def, swalk_def, sp2fm_correct]
QED

Theorem swalk_thm = xfer walkTheory.walk_def

Definition soc_def:
  soc sp t v = oc (sp2fm sp) t v
End

Theorem FMSP_oc[transfer_rule]:
  (FMSP (=) (=) |==> (=) |==> (=) |==> (=)) oc soc
Proof
  simp[sp2fm_correct, FUN_REL_def, soc_def]
QED

Theorem soc_thm = xfer walkstarTheory.oc_thm
Theorem soc_walking = xfer walkstarTheory.oc_walking

(*
val th = GEN_ALL unifDefTheory.unify_def
val _ = show_assums := true
val base = transfer_skeleton true (concl th)
val th = base

val rdb = global_ruledb()
val cleftp = true

fun fpow f n x = if n <= 0 then x else fpow f (n - 1) (f x)

fun F th = seq.hd $ resolve_relhyps [] true (global_ruledb()) th
val th = fpow F 38 base

th |> mkrelsyms_eq true |> eliminate_domrng true (global_ruledb())

*)



Definition sunify_def:
  sunify sp t1 t2 = OPTION_MAP fm2sp (unify (sp2fm sp) t1 t2)
End

Theorem FMSP_unify[transfer_rule]:
  (FMSP (=) (=) |==> (=) |==> (=) |==> OPTREL (FMSP (=) (=))) unify sunify
Proof
  simp[sunify_def, FUN_REL_def, optionTheory.OPTREL_def, PULL_EXISTS,
       sp2fm_correct] >>
  metis_tac[optionTheory.option_CASES]
QED

Theorem sunify_thm =
        unifDefTheory.unify_def |> SRULE[ext_s_check_def]
                                |> xfer

val _ = export_theory();

