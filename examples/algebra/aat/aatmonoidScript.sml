open HolKernel Parse boolLib bossLib;

open monoidTheory liftingTheory transferTheory transferLib
open pred_setTheory

val _ = new_theory "aatmonoid";

Definition mequiv_def:
  mequiv (m1:'a monoid$monoid) (m2:'a monoid$monoid) <=>
    Monoid m1 /\ Monoid m2 /\
    m1.id = m2.id /\ m1.carrier = m2.carrier /\
    !x y. x IN m2.carrier /\ y IN m2.carrier ==> m1.op x y = m2.op x y
End

Theorem mequiv_refl:
  ?m. mequiv m m
Proof
  simp[mequiv_def] >>
  qexists ‘<| carrier := {ARB}; id := ARB; op := K (K ARB) |>’ >>
  REWRITE_TAC[Monoid_def] >> simp[]
QED

Theorem mequiv_sym:
  mequiv m1 m2 ==> mequiv m2 m1
Proof
  simp[mequiv_def]
QED

Theorem mequiv_trans:
  mequiv m1 m2 /\ mequiv m2 m3 ==> mequiv m1 m3
Proof
  simp[mequiv_def]
QED

Theorem monoidclasses_exist:
  ∃M. (\M. ?m. m IN M /\ M = { n | mequiv m n }) M
Proof
  strip_assume_tac mequiv_refl >>
  qexists ‘{ m' | mequiv m' m}’ >>
  simp[EXTENSION] >> metis_tac[mequiv_sym]
QED

val mrec as {absrep_id,...} =
       newtypeTools.rich_new_type {tyname = "monoid",
                                   exthm = monoidclasses_exist,
                                   ABS = "monoidc_ABS",
                                   REP = "monoidc_REP"};

Definition mkmonoid_def:
  mkmonoid m = monoidc_ABS { n | mequiv m n }
End

Definition monoid_REP_def:
  monoid_REP m = CHOICE (monoidc_REP m)
End

Theorem mequiv_refl_EQ[simp]:
  mequiv c c = Monoid c
Proof
  simp[mequiv_def]
QED

Theorem exists_mequiv_Monoid[simp]:
  (?y. mequiv x y) <=> Monoid x
Proof
  simp[mequiv_def] >> metis_tac[]
QED

Definition MTR_def:
  MTR A m tm ⇔ Monoid m /\ mkmonoid m = tm ∧ A = m.carrier
End

Definition RstL_def:  (* restrict to a set on the left *)
  RstL A x y <=> x IN A /\ y = x
End

(*
Theorem Qt_monoid:
  Qt mequiv mkmonoid monoid_REP MTR
Proof
  simp[Qt_alt, monoid_REP_def, mkmonoid_def, MTR_def, FUN_EQ_THM] >>
  rpt strip_tac
  >- (DEEP_INTRO_TAC CHOICE_INTRO >>
      rename [‘monoidc_REP am’] >>
      qspec_then ‘am’ assume_tac (GEN_ALL $ #termP_term_REP mrec) >>
      gvs[PULL_EXISTS] >> irule_at Any $ iffRL mequiv_refl_EQ >> simp[] >>
      rpt strip_tac >>
      ‘{n | mequiv m.carrier m n} = {n | mequiv x.carrier x n}’
        by (simp[EXTENSION] >>
            pop_assum mp_tac >> simp[mequiv_def] >> metis_tac[]) >>
      metis_tac[#absrep_id mrec])
  >- (rename [‘monoidc_REP am’] >>
      qspec_then ‘am’ assume_tac (GEN_ALL $ #termP_term_REP mrec) >>
      gvs[] >> DEEP_INTRO_TAC CHOICE_INTRO >> simp[] >>
      metis_tac[mequiv_sym, mequiv_trans, mequiv_refl_EQ]) >>
  rw[EQ_IMP_THM]
  >- gvs[mequiv_def]
  >- gvs[mequiv_def]
  >- (AP_TERM_TAC >> simp[EXTENSION] >> metis_tac[mequiv_sym, mequiv_trans]) >>
  drule_at Any (iffLR $ #term_ABS_pseudo11 mrec) >>
  simp[] >> impl_tac
  >- (rpt (irule_at Any (iffRL mequiv_refl_EQ)) >> simp[]) >>
  simp[EXTENSION]
QED


Theorem funQ'[local] = SRULE[GSYM AND_IMP_INTRO] funQ |> GEN_ALL

Theorem HK_thm2'[local] = HK_thm2 |> GEN_ALL |> SRULE[]

Theorem carrier_respects:
  (mequiv ===> $=) monoid_carrier monoid_carrier
Proof
  simp[FUN_REL_def, FUN_EQ_THM, mequiv_def]
QED

fun grt th1 th2 = resolve_then.gen_resolve_then Any th1 th2 I

Theorem id_respects:
  (mequiv ===> $=) monoid_id monoid_id
Proof
  simp[FUN_REL_def, mequiv_def]
QED
*)

Definition tmcarrier_def:
  tmcarrier = (monoid_REP ---> I) monoid_carrier
End

Theorem repabs_pseudo_id = SRULE[PULL_EXISTS] (#repabs_pseudo_id mrec)

Theorem abs_pseudo_11:
  Monoid a /\ Monoid b ==>
  (monoidc_ABS {m | mequiv a m} = monoidc_ABS {m | mequiv b m} <=>
   mequiv a b)
Proof
  simp[SRULE[PULL_EXISTS] (GEN_ALL (#term_ABS_pseudo11 mrec))] >>
  rw[EQ_IMP_THM]
  >- gvs[EXTENSION] >>
  simp[EXTENSION] >> metis_tac[mequiv_sym, mequiv_trans]
QED

Theorem tmcarrier_relates[transfer_rule]:
  (MTR A ===> $=) monoid_carrier tmcarrier
Proof
  simp[FUN_REL_def, MTR_def, tmcarrier_def, mkmonoid_def, monoid_REP_def,
       repabs_pseudo_id] >>
  rpt strip_tac >> DEEP_INTRO_TAC CHOICE_INTRO >> simp[] >>
  simp[mequiv_def]
QED

Definition tmid_def:
  tmid = (monoid_REP ---> I) monoid_id
End

Theorem tmid_relates[transfer_rule]:
  (MTR A ===> $=) monoid_id tmid
Proof
  simp[FUN_REL_def, MTR_def, tmid_def, mkmonoid_def, monoid_REP_def,
       repabs_pseudo_id] >>
  rpt strip_tac >> DEEP_INTRO_TAC CHOICE_INTRO >> simp[] >>
  simp[mequiv_def]
QED

Definition tmop_def:
  tmop m x y = if x IN tmcarrier m then
                 if y IN tmcarrier m then (monoid_REP m).op x y
                 else y
               else x
End

Theorem FORALL_tmonoid:
  (∀m:α aatmonoid$monoid. P m) ⇔ (∀m. Monoid m ⇒ P (mkmonoid m))
Proof
  simp[EQ_IMP_THM] >> rpt strip_tac >>
  qspec_then ‘m’ mp_tac (GEN_ALL $ #termP_term_REP mrec) >>
  simp[SF CONJ_ss, PULL_EXISTS] >> gvs[mkmonoid_def] >>
  rpt strip_tac >> first_x_assum drule >>
  pop_assum (ASSUME_TAC o SYM) >> simp[#absrep_id mrec]
QED

Theorem Monoid_monoid_REP[simp]:
  !m. Monoid (monoid_REP m)
Proof
  simp[FORALL_tmonoid, repabs_pseudo_id, mkmonoid_def, monoid_REP_def] >>
  rpt strip_tac >> DEEP_INTRO_TAC CHOICE_INTRO >> simp[mequiv_def] >>
  metis_tac[]
QED

Theorem Monoid_relates[transfer_rule]:
  (MTR A |==> (=)) Monoid (K T)
Proof
  simp[FUN_REL_def, MTR_def]
QED

Theorem tmop_relates[transfer_rule]:
  (MTR A |==> RstL A |==> RstL A |==> RstL A) monoid_op tmop
Proof
  simp[FUN_REL_def, MTR_def, FORALL_tmonoid, repabs_pseudo_id, tmop_def,
       RstL_def, tmcarrier_def, mkmonoid_def, monoid_REP_def, abs_pseudo_11,
       SF CONJ_ss] >>
  rpt strip_tac >> DEEP_INTRO_TAC CHOICE_INTRO >> simp[] >>
  gvs[mequiv_def] >> metis_tac[]
QED

Theorem right_unique_MTR[transfer_simp]:
  right_unique (MTR A)
Proof
  simp[right_unique_def, MTR_def]
QED

Theorem RDOM_MTR[transfer_simp]:
  RDOM (MTR A) = { m | Monoid m /\ m.carrier = A }
Proof
  simp[MTR_def, relationTheory.RDOM_DEF, Once FUN_EQ_THM] >>
  metis_tac[]
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
  period m x k = monoid$period (monoid_REP m) x k
End

Theorem period_relates[transfer_rule]:
  (MTR |==> (=) |==> (=) |==> (<=>)) period period
Proof
  simp[FUN_REL_def, period_def, MTR_def]
QED

Definition order_def:
  order m x = monoid$order (monoid_REP m) x
End

Theorem order_relates[transfer_rule]:
  (MTR |==> (=) |==> (=)) order order
Proof
  simp[FUN_REL_def, order_def, MTR_def]
QED

Overload tord[local] = “aatmonoid$order M”

Theorem order_property = xfer ["order"] order_property
Theorem order_period = xfer ["period"] order_period
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
Theorem abelian_monoid_order_common = xfer ["order"] abelian_monoid_order_common
Theorem abelian_monoid_order_common_coprime =
        xfer ["order"] abelian_monoid_order_common_coprime
Theorem abelian_monoid_order_lcm = xfer ["order"] abelian_monoid_order_lcm


Definition orders_def:
  orders M n = {x | x IN tmcarrier M ∧ aatmonoid$order M x = n}
End

Theorem orders_relate[transfer_rule]:
  (MTR ===> (=) ===> (=)) orders orders
Proof
  simp[FUN_REL_def, orders_def, MTR_def, monoidTheory.orders_def,
       tmcarrier_def, order_def]
QED

Theorem orders_element = xfer ["orders"] orders_element
Theorem orders_subset = xfer ["orders"] orders_subset
Theorem orders_finite = xfer ["orders"] orders_finite
Theorem orders_eq_1 = xfer ["orders"] orders_eq_1

Overload maximal_order =
  “\M : 'a monoid. MAX_SET (IMAGE (order M) (tmcarrier M))”

Theorem maximal_order_alt = xfer ["order"] maximal_order_alt
Theorem monoid_order_divides_maximal =
        xfer ["order"] monoid_order_divides_maximal

Definition monoid_invertibles_def0:
  monoid_invertibles M = monoid$monoid_invertibles (monoid_REP M)
End

Theorem monoid_invertibles_relate[transfer_rule]:
  (MTR ===> (=)) monoid_invertibles monoid_invertibles
Proof
  simp[FUN_REL_def, monoid_invertibles_def0, MTR_def]
QED

Theorem monoid_invertibles_def:
  monoid_invertibles M =
  { x | x IN tmcarrier M ∧ ?y. y IN tmcarrier M ∧ tmop M x y = tmid M ∧
                               tmop M y x = tmid M }
Proof
  simp[monoid_invertibles_def0, tmcarrier_def, tmop_def, tmid_def] >>
  simp[monoidTheory.monoid_invertibles_def]
QED

Theorem monoid_invertibles_element =
        xfer ["monoid_invertibles"] monoid_invertibles_element
Theorem monoid_order_nonzero = xfer ["monoid_invertibles"] monoid_order_nonzero

(*
Definition InvertiblesM_def:
  InvertiblesM M = mkmonoid <| carrier := monoid_invertibles M;
                               op := oodf (monoid_invertibles M) (tmop M);
                               id := tmid M |>
End

Theorem Invertibles_relate[transfer_rule]:
  (MTR ===> MTR) Invertibles InvertiblesM
Proof
  simp[FUN_REL_def, MTR_def, InvertiblesM_def] >>
  strip_tac >> irule (#repabs_pseudo_id mrec) >>
  simp[fullmonoid_def]
QED
*)

val _ = export_theory();
