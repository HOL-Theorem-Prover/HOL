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

Theorem Monoid_monoid_REP[simp]:
  !m. Monoid (monoid_REP m)
Proof
  simp[FORALL_tmonoid, tmonoid_repabs_id]
QED

Theorem Monoid_relates[transfer_rule]:
  (MTR |==> (=)) Monoid (K T)
Proof
  simp[FUN_REL_def, MTR_def]
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

Theorem surj_MTR[transfer_simp]:
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

Definition FiniteAbelianMonoid_def:
  FiniteAbelianMonoid (m:α monoid) ⇔ FiniteMonoid m ∧ AbelianMonoid m
End

Theorem FiniteAbelianMonoid_relates[transfer_rule]:
  (MTR |==> (=)) FiniteAbelianMonoid FiniteAbelianMonoid
Proof
  simp[FiniteAbelianMonoid_def, monoidTheory.FiniteAbelianMonoid_def,
       FUN_REL_def, FiniteMonoid_def, MTR_def, AbelianMonoid_def] >>
  metis_tac[]
QED

Theorem FiniteAbelianMonoid_def_alt:
  ∀m. FiniteAbelianMonoid m ⇔
        FiniteMonoid m ∧
        ∀x y. x ∈ tmcarrier m ∧ y ∈ tmcarrier m ⇒ tmop m x y = tmop m y x
Proof
  xfer_back_tac[] >> simp[monoidTheory.FiniteAbelianMonoid_def_alt]
QED


fun prettify th =
  let val (vs, _) = strip_forall (concl th)
  in
    if #1 (dest_type $ type_of $ hd vs) = "monoid" then
      CONV_RULE (RENAME_VARS_CONV ["M"]) th
    else th
  end handle HOL_ERR _ => th
fun xfer hs th =
  th |> transfer_thm 10 ("Monoid"::hs) true (global_ruledb())
     |> prettify

Theorem monoid_carrier_nonempty[simp] =
        xfer [] monoidTheory.monoid_carrier_nonempty

Definition monoid_exp_def:
  monoid_exp m x n = monoid$monoid_exp (monoid_REP m) x n
End

Theorem monoid_exp_relates[transfer_rule]:
  (MTR |==> (=) |==> (=) |==> (=)) monoid_exp monoid_exp
Proof
  simp[FUN_REL_def, monoid_exp_def, MTR_def]
QED

Theorem monoid_exp_thm[simp]:
  !m x. monoid_exp m x 0 = tmid m /\
        !n. monoid_exp m x (SUC n) = tmop m x (monoid_exp m x n)
Proof
  xfer_back_tac []  >> simp[]
QED

Theorem monoid_exp_FUNPOW =
        xfer ["monoid_exp"] monoidTheory.monoid_exp_def

Theorem monoid_exp_element[simp] =
        xfer ["monoid_exp"] monoidTheory.monoid_exp_element

Theorem monoid_exp_1[simp] = xfer [] monoidTheory.monoid_exp_1
Theorem monoid_id_exp[simp] = xfer [] monoidTheory.monoid_id_exp

Theorem monoid_comm_exp:
  !m x y n.
    tmop m x y = tmop m y x ⇒
    tmop m (monoid_exp m x n) y = tmop m y (monoid_exp m x n)
Proof
  Induct_on ‘n’ >> simp[] >> metis_tac[tmonoid_assoc]
QED

Theorem monoid_exp_comm:
  !m x n.
    tmop m (monoid_exp m x n) x = tmop m x (monoid_exp m x n)
Proof
  Induct_on ‘n’ >> simp[] >> simp[GSYM tmonoid_assoc]
QED

Theorem monoid_comm_op_exp:
  !m n x y. tmop m x y = tmop m y x ⇒
            monoid_exp m (tmop m x y) n =
            tmop m (monoid_exp m x n) (monoid_exp m y n)
Proof
  Induct_on ‘n’ >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >> simp[] >>
  metis_tac[monoid_exp_comm, tmonoid_assoc, monoid_comm_exp]
QED

Theorem monoid_comm_exp_exp:
  !m n p x y. tmop m x y = tmop m y x ⇒
              tmop m (monoid_exp m x n) (monoid_exp m y p) =
              tmop m (monoid_exp m y p) (monoid_exp m x n)
Proof
  Induct_on ‘n’ >> simp[] >>
  metis_tac[tmonoid_assoc, monoid_comm_exp]
QED

Theorem monoid_exp_add:
  !m n p x.
    monoid_exp m x (n + p) = tmop m (monoid_exp m x n) (monoid_exp m x p)
Proof
  Induct_on ‘n’ >> simp[arithmeticTheory.ADD_CLAUSES, tmonoid_assoc]
QED

Theorem monoid_exp_mult:
  !m n p x.
    monoid_exp m x (n * p) = monoid_exp m (monoid_exp m x n) p
Proof
  Induct_on ‘p’ >> simp[arithmeticTheory.MULT_CLAUSES, monoid_exp_add]
QED

Theorem monoid_exp_mult_comm:
  !m x n p.
    monoid_exp m (monoid_exp m x n) p = monoid_exp m (monoid_exp m x p) n
Proof
  metis_tac[arithmeticTheory.MULT_COMM, monoid_exp_mult]
QED

(* ----------------------------------------------------------------------
    Finite monoids
   ---------------------------------------------------------------------- *)

Theorem finite_monoid_exp_not_distinct =
        xfer ["FiniteMonoid"] monoidTheory.finite_monoid_exp_not_distinct

(* ----------------------------------------------------------------------
    MITSET : iterating monoid operation over (finite) set of elements
   ---------------------------------------------------------------------- *)

Overload MITSET = “λm. ITSET (tmop m)”

Theorem abelian_monoid_op_closure_comm_assoc_fun =
        xfer ["AbelianMonoid"]
             monoidTheory.abelian_monoid_op_closure_comm_assoc_fun

Theorem COMMUTING_MITSET_INSERT =
        xfer ["AbelianMonoid"] COMMUTING_GITSET_INSERT

Theorem COMMUTING_MITSET_REDUCTION =
        xfer ["AbelianMonoid"] COMMUTING_GITSET_REDUCTION

Theorem COMMUTING_MITSET_RECURSES =
        xfer ["AbelianMonoid"] COMMUTING_GITSET_RECURSES

Overload MPROD_SET = “λm s. MITSET m s (tmid m)”

Theorem MPROD_SET_SING[simp]:
  !m x. MPROD_SET m {x} = x
Proof
  simp[]
QED

(* Interesting case where forward transfer breaks down
val th = GPROD_SET_PROPERTY

val _ = show_assums := true
val base = transfer_skeleton true (concl th)
val th = base
val rdb = global_ruledb()
val cleftp = true

fun fpow f n x = if n <= 0 then x else fpow f (n - 1) (f x)

fun F th = seq.hd $ resolve_relhyps ["AbelianMonoid"] true (global_ruledb()) th
val th = fpow F 11 base
*)


Theorem MPROD_SET_PROPERTY:
  !m s. AbelianMonoid m /\ FINITE s /\ s ⊆ tmcarrier m ⇒
        MPROD_SET m s ∈ tmcarrier m
Proof
  xfer_back_tac [] >> simp[GSYM GPROD_SET_def, GPROD_SET_PROPERTY]
QED

Definition tmextend_def:
  tmextend m = mkmonoid (extend (monoid_REP m))
End

Theorem tmextend_relates[transfer_rule]:
  (MTR |==> MTR) extend tmextend
Proof
  simp[FUN_REL_def, MTR_def, tmextend_def] >>
  strip_tac >> irule tmonoid_repabs_id >> simp[]
QED

Theorem tmextend_carrier[simp] = xfer ["extend"] (GEN_ALL extend_carrier)
Theorem tmextend_id[simp] = xfer ["extend"] (GEN_ALL extend_id)

Theorem tmextend_op = xfer ["extend"] (GEN_ALL extend_op)

Definition period_def:
  period m x k = monoidOrder$period (monoid_REP m) x k
End

Theorem period_relates[transfer_rule]:
  (MTR |==> (=) |==> (=) |==> (<=>)) period period
Proof
  simp[FUN_REL_def, period_def, MTR_def]
QED

Definition order_def:
  order m x = monoidOrder$order (monoid_REP m) x
End

Theorem order_relates[transfer_rule]:
  (MTR |==> (=) |==> (=)) order order
Proof
  simp[FUN_REL_def, order_def, MTR_def]
QED

Overload tord[local] = “aatmonoid$order m”

Theorem order_property =
        xfer ["order"] monoidOrderTheory.order_property
Theorem order_period = xfer ["period"] monoidOrderTheory.order_period
Theorem order_minimal = xfer ["order"] order_minimal
Theorem order_eq_0 = xfer ["order"] order_eq_0
Theorem order_thm = xfer ["order"] order_thm
Theorem monoid_order_id[simp] = xfer ["order"] monoid_order_id
Theorem monoid_order_eq_1 = xfer ["order"] monoid_order_eq_1
Theorem monoid_order_condition = xfer ["order"] monoid_order_condition
Theorem monoid_order_power_eq_0 = xfer ["order"] monoid_order_power_eq_0
Theorem monoid_order_power = xfer ["order"] monoid_order_power
Theorem monoid_order_power_eqn = xfer ["order"] monoid_order_power_eqn
Theorem monoid_order_power_coprime = xfer ["order"] monoid_order_power_coprime
Theorem monoid_order_cofactor = xfer ["order"] monoid_order_cofactor
Theorem monoid_order_divisor = xfer ["order"] monoid_order_divisor
Theorem monoid_order_common = xfer ["order"] monoid_order_common
Theorem monoid_order_common_coprime = xfer ["order"] monoid_order_common_coprime
Theorem monoid_exp_mod_order = xfer ["order"] monoid_exp_mod_order

val _ = export_theory();
