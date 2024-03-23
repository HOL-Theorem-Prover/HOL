open HolKernel Parse boolLib bossLib;

open monoidTheory transferTheory transferLib

val _ = new_theory "aatmonoid";

(* out-of-domain function *)
Definition oodf_def:
  oodf A f x y = if x ∈ A then if y ∈ A then f x y else y else x
End

Theorem oodf_idem[simp]:
  oodf A (oodf A f) = oodf A f
Proof
  rw[oodf_def, FUN_EQ_THM]
QED

Theorem oodf_UNIV[simp]:
  oodf UNIV f = f
Proof
  simp[FUN_EQ_THM, oodf_def]
QED

Definition fullmonoid_def:
  fullmonoid m ⇔ Monoid m ∧ oodf m.carrier m.op = m.op
End

Theorem fullmonoids_exist:
  ∃m. fullmonoid m
Proof
  REWRITE_TAC[fullmonoid_def] >>
  qexists ‘<| carrier := {ARB}; id := ARB; op := oodf {ARB} (K (K ARB)) |>’ >>
  simp[] >> REWRITE_TAC[Monoid_def] >> simp[] >>
  simp[oodf_def]
QED

val mrec as {absrep_id,...} =
       newtypeTools.rich_new_type {tyname = "monoid",
                                   exthm = fullmonoids_exist,
                                   ABS = "monoid_ABS",
                                   REP = "monoid_REP"};

Overload mkmonoid = “monoid_ABS”

Definition MTR_def:
  MTR m tm ⇔ monoid_REP tm = m
End

Definition tmop_def:
  tmop m = (monoid_REP m).op
End

Definition tmid_def:
  tmid m = (monoid_REP m).id
End

Definition tmcarrier_def:
  tmcarrier m = (monoid_REP m).carrier
End

Theorem FORALL_tmonoid:
  (∀m:α aatmonoid$monoid. P m) ⇔
  (∀m. Monoid m ∧ oodf m.carrier m.op = m.op ⇒ P (monoid_ABS m))
Proof
  simp[EQ_IMP_THM] >> rpt strip_tac >>
  ‘fullmonoid (monoid_REP m)’ by simp[#termP_term_REP mrec] >>
  first_x_assum $ qspec_then ‘monoid_REP m’ mp_tac >>
  gvs[absrep_id, fullmonoid_def]
QED

Theorem tmonoid_repabs_id:
  Monoid m ∧ oodf m.carrier m.op = m.op ⇒ monoid_REP (monoid_ABS m) = m
Proof
  strip_tac >> irule (#repabs_pseudo_id mrec) >> simp[fullmonoid_def]
QED

Theorem tmop_relates[transfer_rule]:
  (MTR |==> (=) |==> (=) |==> (=)) monoid_op tmop
Proof
  simp[FUN_REL_def, MTR_def, FORALL_tmonoid, tmonoid_repabs_id, tmop_def]
QED

Theorem tmid_relates[transfer_rule]:
  (MTR |==> (=)) monoid_id tmid
Proof
  simp[FUN_REL_def, MTR_def, FORALL_tmonoid, tmonoid_repabs_id, tmid_def]
QED

Theorem tmcarrier_relates[transfer_rule]:
  (MTR |==> (=)) monoid_carrier tmcarrier
Proof
  simp[FUN_REL_def, MTR_def, FORALL_tmonoid, tmonoid_repabs_id, tmcarrier_def]
QED

Theorem left_unique_MTR[transfer_simp]:
  left_unique MTR
Proof
  simp[left_unique_def, MTR_def]
QED

Theorem right_unique_MTR[transfer_simp]:
  right_unique MTR
Proof
  simp[right_unique_def, MTR_def, #term_REP_11 mrec]
QED

Theorem total_MTR[transfer_simp]:
  surj MTR
Proof
  simp[surj_def, MTR_def]
QED

Theorem RDOM_MTR[transfer_simp]:
  RDOM MTR = { m | Monoid m /\ oodf m.carrier m.op = m.op }
Proof
  simp[MTR_def, relationTheory.RDOM_DEF, Once FUN_EQ_THM] >>
  metis_tac[fullmonoid_def, #termP_exists mrec]
QED

Theorem tmonoid_assoc0:
  !m a b c. a ∈ tmcarrier m /\ b ∈ tmcarrier m /\ c ∈ tmcarrier m ⇒
            tmop m a (tmop m b c) = tmop m (tmop m a b) c
Proof
  xfer_back_tac [] >> simp[monoid_assoc]
QED

Theorem tmonoid_assoc:
  ∀m a b c. tmop m a (tmop m b c) = tmop m (tmop m a b) c
Proof
  xfer_back_tac [] >> simp[] >> qx_gen_tac ‘m’ >> strip_tac >>
  qx_genl_tac [‘a’, ‘b’, ‘c’] >>
  map_every (fn q => Cases_on (q @ ‘ ∈ m.carrier’)) [‘a’, ‘b’, ‘c’] >>
  simp[monoid_assoc] >> gvs[oodf_def, FUN_EQ_THM] >>
  metis_tac[Monoid_def]
QED

Theorem tmonoid_idL[simp]:
  ∀m x. tmop m (tmid m) x = x
Proof
  xfer_back_tac [] >> simp[oodf_def, FUN_EQ_THM] >>
  metis_tac[Monoid_def]
QED

Theorem tmonoid_idR[simp]:
  ∀m x. tmop m x (tmid m) = x
Proof
  xfer_back_tac [] >> simp[oodf_def, FUN_EQ_THM] >> metis_tac[Monoid_def]
QED

Theorem tmid_uniqueL:
  (∀x. tmop m e x = x) ⇔ e = tmid m
Proof
  metis_tac[tmonoid_idR, tmonoid_idL]
QED

Theorem tmid_uniqueR:
  (∀x. tmop m x e = x) ⇔ e = tmid m
Proof
  metis_tac[tmonoid_idL, tmonoid_idR]
QED

Definition list_monoid_def:
  list_monoid = mkmonoid <| carrier := UNIV; op := APPEND; id := [] |>
End

Theorem rep_list_monoid[simp,local]:
  monoid_REP list_monoid = <| carrier := UNIV; op := APPEND; id := [] |>
Proof
  simp[list_monoid_def] >> irule tmonoid_repabs_id >> simp[Monoid_def]
QED

Theorem tmop_list_monoid[simp]:
  tmop list_monoid = APPEND
Proof
  simp[tmop_def]
QED

Theorem tmid_list_monoid[simp]:
  tmid list_monoid = []
Proof
  simp[tmid_def]
QED

Theorem tmcarrier_list_monoid[simp]:
  tmcarrier list_monoid = UNIV
Proof
  simp[tmcarrier_def]
QED

Definition FiniteMonoid_def:
  FiniteMonoid m = monoid$FiniteMonoid (monoid_REP m)
End

Theorem FiniteMonoid_relates[transfer_rule]:
  (MTR |==> (=)) FiniteMonoid FiniteMonoid
Proof
  simp[FiniteMonoid_def, FUN_REL_def, MTR_def]
QED

Theorem FiniteMonoid_thm:
  !m. FiniteMonoid m = FINITE $ tmcarrier m
Proof
  xfer_back_tac[] >> simp[]
QED

Definition AbelianMonoid_def:
  AbelianMonoid m = monoid$AbelianMonoid (monoid_REP m)
End

Theorem AbelianMonoid_relates[transfer_rule]:
  (MTR |==> (=)) AbelianMonoid AbelianMonoid
Proof
  simp[AbelianMonoid_def, FUN_REL_def, MTR_def]
QED



val _ = export_theory();
