open HolKernel Parse boolLib bossLib;

open monoidTheory monoidOrderTheory transferTheory transferLib

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

Theorem monoid_carrier_nonempty[simp]:
  ∀m. tmcarrier m <> {}
Proof
  xfer_back_tac [] >> simp[monoid_carrier_nonempty]
QED

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

Theorem monoid_exp_FUNPOW:
  !m x n. monoid_exp m x n = FUNPOW (tmop m x) n (tmid m)
Proof
  xfer_back_tac [] >> simp[monoidTheory.monoid_exp_def]
QED

Theorem monoid_exp_element[simp]:
  !m x. x ∈ tmcarrier m ⇒ !n. monoid_exp m x n ∈ tmcarrier m
Proof
  xfer_back_tac [] >> simp[monoidTheory.monoid_exp_element]
QED

Theorem monoid_exp_1[simp]:
  !m x. monoid_exp m x 1 = x
Proof
  rewrite_tac[arithmeticTheory.ONE, monoid_exp_thm] >>
  simp[]
QED

Theorem monoid_id_exp[simp]:
  !m n. monoid_exp m (tmid m) n = tmid m
Proof
  xfer_back_tac [] >> simp[monoidTheory.monoid_id_exp]
QED

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

Theorem finite_monoid_exp_not_distinct:
  !m x. FiniteMonoid m /\ x ∈ tmcarrier m ⇒
        ∃h k. monoid_exp m x h = monoid_exp m x k /\ h ≠ k
Proof
  xfer_back_tac [] >> simp[] >>
  metis_tac[monoidTheory.finite_monoid_exp_not_distinct,
            monoidTheory.FiniteMonoid_def]
QED

(* ----------------------------------------------------------------------
    MITSET : iterating monoid operation over (finite) set of elements
   ---------------------------------------------------------------------- *)

Overload MITSET = “λm. ITSET (tmop m)”

Theorem abelian_monoid_op_closure_comm_assoc_fun:
  !m. AbelianMonoid m ⇒ closure_comm_assoc_fun (tmop m) (tmcarrier m)
Proof
  xfer_back_tac [] >>
  simp[monoidTheory.abelian_monoid_op_closure_comm_assoc_fun]
QED

Theorem COMMUTING_MITSET_INSERT:
  !m s. AbelianMonoid m /\ FINITE s /\ s ⊆ tmcarrier m ⇒
        !b x. b ∈ tmcarrier m /\ x ∈ tmcarrier m ⇒
              MITSET m (x INSERT s) b = MITSET m (s DELETE x) (tmop m x b)
Proof
  xfer_back_tac [] >> simp[COMMUTING_GITSET_INSERT]
QED

Theorem COMMUTING_MITSET_REDUCTION:
  !m s. AbelianMonoid m /\ FINITE s /\ s ⊆ tmcarrier m ⇒
        !b x. b ∈ tmcarrier m /\ x ∈ tmcarrier m ⇒
              MITSET m s (tmop m x b) = tmop m x (MITSET m s b)
Proof
  xfer_back_tac [] >> simp[COMMUTING_GITSET_REDUCTION]
QED

Theorem COMMUTING_MITSET_RECURSES:
  !m s. AbelianMonoid m /\ FINITE s /\ s ⊆ tmcarrier m ⇒
        !b x. b ∈ tmcarrier m /\ x ∈ tmcarrier m ⇒
              MITSET m (x INSERT s) b = tmop m x (MITSET m (s DELETE x) b)
Proof
  xfer_back_tac [] >> simp[COMMUTING_GITSET_RECURSES]
QED

Overload MPROD_SET = “λm s. MITSET m s (tmid m)”

Theorem MPROD_SET_SING[simp]:
  !m x. MPROD_SET m {x} = x
Proof
  simp[]
QED

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

Theorem tmextend_carrier[simp]:
  !m. tmcarrier (tmextend m) = UNIV
Proof
  xfer_back_tac [] >> simp[]
QED

Theorem tmextend_id[simp]:
  !m. tmid (tmextend m) = tmid m
Proof
  xfer_back_tac [] >> simp[]
QED

Theorem tmextend_op:
  !m x y. x ∈ tmcarrier m /\ y ∈ tmcarrier m ⇒
          tmop (tmextend m) x y = tmop m x y
Proof
  xfer_back_tac [] >> simp[extend_op]
QED

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

Theorem order_property:
  !m x. monoid_exp m x (tord x) = tmid m
Proof
  xfer_back_tac [] >> simp[monoidOrderTheory.order_property]
QED

Theorem order_period:
  !m x. 0 < tord x ⇒ period m x (tord x)
Proof
  xfer_back_tac [] >> simp[order_period]
QED

Theorem order_minimal:
  !m x n. 0 < n /\ n < tord x ⇒ monoid_exp m x n <> tmid m
Proof
  xfer_back_tac [] >> simp[order_minimal]
QED

Theorem order_eq_0:
  !m x. tord x = 0 ⇔ !n. 0 < n ==> monoid_exp m x n <> tmid m
Proof
  xfer_back_tac [] >> simp[order_eq_0]
QED

Theorem order_thm:
  !m x n. 0 < n ⇒
          (tord x = n ⇔ monoid_exp m x n = tmid m /\
                        !p. 0 < p /\ p < n ⇒ monoid_exp m x p <> tmid m)
Proof
  xfer_back_tac [] >> simp[order_thm]
QED

Theorem monoid_order_id[simp]:
  !m. tord (tmid m) = 1
Proof
  xfer_back_tac [] >> simp[monoid_order_id]
QED

Theorem monoid_order_eq_1:
  !m x. x ∈ tmcarrier m ⇒ (tord x = 1 ⇔ x = tmid m)
Proof
  xfer_back_tac [] >> simp[monoid_order_eq_1]
QED

Theorem monoid_order_condition:
  !m x. x ∈ tmcarrier m ⇒ !p. monoid_exp m x p = tmid m ⇔ tord x divides p
Proof
  xfer_back_tac [] >> simp[monoid_order_condition]
QED

Theorem monoid_order_power_eq_0:
  !m x. x ∈ tmcarrier m ⇒ !k. tord (monoid_exp m x k) = 0 ⇔ 0 < k /\ tord x = 0
Proof
  xfer_back_tac[] >> simp[monoid_order_power_eq_0]
QED

Theorem monoid_order_power:
  !m x. x ∈ tmcarrier m ⇒ !k. tord (monoid_exp m x k) * gcd (tord x) k = tord x
Proof
  xfer_back_tac[] >> simp[monoid_order_power]
QED

Theorem monoid_order_power_eqn:
  !m x k. x ∈ tmcarrier m /\ 0 < k ⇒
          tord (monoid_exp m x k) = tord x DIV gcd k (tord x)
Proof
  xfer_back_tac[] >> simp[monoid_order_power_eqn]
QED

Theorem monoid_order_power_coprime:
  !m x k. x ∈ tmcarrier m /\ coprime k (tord x) ⇒
          tord (monoid_exp m x k) = tord x
Proof
  xfer_back_tac[] >> simp[monoid_order_power_coprime]
QED

Theorem monoid_order_cofactor:
  !m x n. x ∈ tmcarrier m /\ 0 < tord x /\ n divides tord x ⇒
          tord (monoid_exp m x (tord x DIV n)) = n
Proof
  xfer_back_tac[] >> simp[monoid_order_cofactor]
QED

Theorem monoid_order_divisor:
  !m x n. x ∈ tmcarrier m /\ 0 < tord x /\ n divides tord x ⇒
          ∃y. y ∈ tmcarrier m /\ tord y = n
Proof
  xfer_back_tac[] >> simp[] >> metis_tac[monoid_order_divisor]
QED

Theorem monoid_order_common:
  !m x y. x ∈ tmcarrier m /\ y ∈ tmcarrier m /\ tmop m x y = tmop m y x ⇒
          ∃z. z ∈ tmcarrier m /\
              tord z * gcd (tord x) (tord y) = lcm (tord x) (tord y)
Proof
  xfer_back_tac[] >> simp[] >>
  metis_tac[monoid_order_common, arithmeticTheory.MULT_COMM]
QED

Theorem monoid_order_common_coprime:
  !m x y. x ∈ tmcarrier m /\ y ∈ tmcarrier m /\ tmop m x y = tmop m y x /\
          coprime (tord x) (tord y) ⇒
          ∃z. z ∈ tmcarrier m /\ tord z = tord x * tord y
Proof
  xfer_back_tac[] >> simp[] >> metis_tac[monoid_order_common_coprime]
QED

Theorem monoid_exp_mod_order:
  !m x n. x ∈ tmcarrier m /\ 0 < tord x ⇒
          monoid_exp m x n = monoid_exp m x (n MOD tord x)
Proof
  xfer_back_tac[] >> simp[] >> metis_tac[monoid_exp_mod_order]
QED

val _ = export_theory();
