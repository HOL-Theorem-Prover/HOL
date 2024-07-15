open HolKernel Parse boolLib bossLib;

open pure_dBTheory transferTheory transferLib
open head_reductionTheory

val _ = new_theory "pdbTransfer";

Definition TPDB_def:
  TPDB (t : term) (d : pdb) ⇔ d = fromTerm t
End

Definition StNm_def:
  StNm (s:string) (n:num) ⇔ n = s2n s
End

Theorem total_TPDB[transfer_simp]:
  total TPDB
Proof
  simp[total_def, TPDB_def]
QED

Theorem total_StNm[transfer_simp]:
  total StNm
Proof
  simp[total_def, StNm_def]
QED

Theorem left_unique_TPDB[transfer_simp]:
  left_unique TPDB
Proof
  simp[left_unique_def, TPDB_def]
QED

Theorem right_unique_TPDB[transfer_simp]:
  right_unique TPDB
Proof
  simp[right_unique_def, TPDB_def]
QED

Theorem left_unique_StNm[transfer_simp]:
  left_unique StNm
Proof
  simp[left_unique_def, StNm_def]
QED

Theorem right_unique_StNm[transfer_simp]:
  right_unique StNm
Proof
  simp[right_unique_def, StNm_def]
QED

Theorem surj_TPDB[transfer_simp]:
  surj TPDB
Proof
  simp[surj_def, TPDB_def] >> metis_tac[fromTerm_onto]
QED

Theorem surj_StNm[transfer_simp]:
  surj StNm
Proof
  simp[surj_def, StNm_def] >> metis_tac[string_numTheory.s2n_onto]
QED

Theorem RRANGE_TPDB[transfer_simp]:
  RRANGE TPDB = K T
Proof
  simp[relationTheory.RRANGE, TPDB_def, FUN_EQ_THM] >>
  metis_tac[fromTerm_onto]
QED

Theorem RRANGE_StNm[transfer_simp]:
  RRANGE StNm = K T
Proof
  simp[relationTheory.RRANGE, StNm_def, FUN_EQ_THM] >>
  metis_tac[string_numTheory.s2n_onto]
QED

(* ----------------------------------------------------------------------
    Existing constants that pure_dBTheory already connects
   ---------------------------------------------------------------------- *)

Theorem TPDB_FV[transfer_rule]:
  (TPDB |==> (=)) FV dFVs
Proof
  simp[FUN_REL_def, TPDB_def]
QED

Theorem TPDB_SUB[transfer_rule]:
  (TPDB |==> StNm |==> TPDB |==> TPDB) SUB sub
Proof
  simp[FUN_REL_def, TPDB_def, StNm_def, fromTerm_subst]
QED

Theorem TPDB_ccbeta[transfer_rule]:
  (TPDB |==> TPDB |==> (=)) (compat_closure beta) dbeta
Proof
  simp[FUN_REL_def, TPDB_def, dbeta_ccbeta_eqn]
QED

Theorem TPDB_VAR[transfer_rule]:
  (StNm |==> TPDB) VAR dV
Proof
  simp[StNm_def, TPDB_def, FUN_REL_def]
QED

Theorem TPDB_APP[transfer_rule]:
  (TPDB |==> TPDB |==> TPDB) APP dAPP
Proof
  simp[TPDB_def, FUN_REL_def]
QED

Theorem TPDB_LAM[transfer_rule]:
  (StNm |==> TPDB |==> TPDB) LAM dLAM
Proof
  simp[TPDB_def, FUN_REL_def, StNm_def]
QED

Theorem TPDB_bnf[transfer_rule]:
  (TPDB |==> (=)) bnf dbnf
Proof
  simp[TPDB_def, FUN_REL_def]
QED

Theorem TPDB_cceta[transfer_rule]:
  (TPDB |==> TPDB |==> (=)) (compat_closure eta) eta
Proof
  simp[FUN_REL_def, TPDB_def, eta_eq_lam_eta]
QED

Theorem TPDB_is_abs[transfer_rule]:
  (TPDB |==> (=)) is_abs is_dABS
Proof
  simp[FUN_REL_def, TPDB_def]
QED

Theorem RTC_xfers[transfer_rule]:
  total AB ⇒ surj AB ⇒ right_unique AB ⇒ left_unique AB ==>
  ((AB |==> AB |==> (=)) |==> (AB |==> AB |==> (=))) RTC RTC
Proof
  rpt strip_tac >> simp[FUN_REL_def] >> qx_genl_tac [‘R1’, ‘R2’] >>
  strip_tac >> simp[EQ_IMP_THM, FORALL_AND_THM, PULL_FORALL] >>
  simp[IMP_CONJ_THM] >> simp[FORALL_AND_THM] >> conj_tac >>
  Induct_on‘RTC’ >> conj_tac
  >- metis_tac[right_unique_def, relationTheory.RTC_REFL]
  >- (qx_genl_tac [‘a0’, ‘a1’, ‘a’] >> strip_tac >>
      qx_genl_tac [‘b0’, ‘b’] >> rpt strip_tac >>
      metis_tac[total_def, relationTheory.RTC_RULES])
  >- metis_tac[left_unique_def, relationTheory.RTC_REFL]
  >- (qx_genl_tac [‘b0’, ‘b1’, ‘b’] >> strip_tac >>
      qx_genl_tac [‘a0’, ‘a’] >> rpt strip_tac >>
      metis_tac[surj_def, relationTheory.RTC_RULES])
QED

(* ----------------------------------------------------------------------
    Build more connections
   ---------------------------------------------------------------------- *)

Definition dhreduce1_def:
  dhreduce1 d1 d2 ⇔ hreduce1 (toTerm d1) (toTerm d2)
End

Theorem TPDB_hreduce1[transfer_rule]:
  (TPDB |==> TPDB |==> (=)) hreduce1 dhreduce1
Proof
  simp[dhreduce1_def, TPDB_def, FUN_REL_def]
QED

fun xfer th =
  time (transfer_thm 10 {hints = [], force_imp = true, cleftp = true}
                (global_ruledb())) (GEN_ALL th)


Theorem dhreduce1_APP = xfer hreduce1_APP
Theorem dhreduce1_BETA = xfer $ cj 1 hreduce1_rules
Theorem dhreduce1_LAM = xfer hreduce1_LAM
Theorem dhreduce1_substitutive = xfer hreduce1_substitutive
Theorem dhreduce1_rwts = xfer hreduce1_rwts
Theorem dhreduce_substitutive = xfer hreduce_substitutive

Definition dhnf_def:
  dhnf pd = hnf (toTerm pd)
End

Theorem dhnf_rule[transfer_rule]:
  (TPDB |==> (=)) hnf dhnf
Proof
  simp[FUN_REL_def, TPDB_def, dhnf_def]
QED

Theorem dhnf_dLAM_cases = xfer hnf_cases

val _ = transferLib.add_atomic_term ("termFV", “FV : term -> string set”)

Theorem dhreduce1_FV = xfer hreduce1_FV

(*
val _ = show_assums := true
val th = hreduce1_APP
val rdb = global_ruledb()
val base = transfer_skeleton rdb {force_imp=true,cleftp=true,hints=[]}
                (concl th)
val th = base

val cleftp = true

fun fpow f n x = if n <= 0 then x else fpow f (n - 1) (f x)

fun F x = seq.hd (resolve_relhyps [] true (global_ruledb()) x)
val th7 = fpow F 11 th

    fpow F 14 th

*)

val _ = export_theory();
