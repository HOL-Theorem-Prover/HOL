open HolKernel Parse boolLib bossLib;

open monoidTheory liftingTheory transferTheory transferLib liftLib
open pred_setTheory

val _ = new_theory "aatmonoid";

Definition mequiv_def:
  mequiv m1 m2 ⇔ m1 = m2 /\ Monoid m2
End

Theorem monoids_exist:
  ∃M:'a monoid$monoid. Monoid M
Proof
  qexists ‘<| carrier := {ARB}; op := λx y. ARB; id := ARB|>’ >>
  simp[Monoid_def]
QED

val mrec as {absrep_id,...} =
       newtypeTools.rich_new_type {tyname = "monoid",
                                   exthm = monoids_exist,
                                   ABS = "mkmonoid",
                                   REP = "monoid_REP"};

Theorem repabs_pseudo_id = #repabs_pseudo_id mrec

Definition MTR_def:
  MTR m tm ⇔ Monoid m /\ mkmonoid m = tm
End

Theorem Qt_monoid[liftQt]:
  Qt mequiv mkmonoid monoid_REP MTR
Proof
  simp[Qt_alt, MTR_def, FUN_EQ_THM, #absrep_id mrec, #termP_term_REP mrec,
       mequiv_def] >>
  rw[EQ_IMP_THM] >> gvs[#term_ABS_pseudo11 mrec]
QED

Theorem carrier_respects:
  (mequiv ===> $= ===> $=) monoid_carrier monoid_carrier
Proof
  simp[FUN_REL_def, FUN_EQ_THM, mequiv_def]
QED
val _ = liftdef carrier_respects "tmcarrier"

Theorem id_respects:
  (mequiv ===> $=) monoid_id monoid_id
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef id_respects "tmid"

Theorem op_respects:
  (mequiv ===> $= ===> $= ===> $=) monoid_op monoid_op
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef op_respects "tmop"

Theorem Monoid_monoid_REP[simp] = #termP_term_REP mrec

Theorem Monoid_relates[transfer_rule]:
  (MTR ===> (=)) Monoid (K T)
Proof
  simp[FUN_REL_def, MTR_def]
QED

Theorem right_unique_MTR[transfer_simp]:
  right_unique MTR
Proof
  simp[right_unique_def, MTR_def]
QED

Theorem MTReq_relates[transfer_rule]:
  (MTR ===> MTR ===> (=)) (=) (=)
Proof
  simp[MTR_def, FUN_REL_def, #term_ABS_pseudo11 mrec]
QED


Theorem RDOM_MTR[transfer_simp]:
  RDOM MTR = { m | Monoid m }
Proof
  simp[MTR_def, relationTheory.RDOM_DEF, Once FUN_EQ_THM] >>
  metis_tac[]
QED

Theorem surj_MTR[transfer_simp]:
  surj MTR
Proof
  simp[surj_def, MTR_def] >> qx_gen_tac ‘aM’ >> qexists ‘monoid_REP aM’ >>
  simp[#absrep_id mrec]
QED

(*
val th = monoid_assoc

val _ = show_assums := true
val base = transfer_skeleton true (concl th)
val th = base
val rdb = global_ruledb()
val cleftp = true

fun fpow f n x = if n <= 0 then x else fpow f (n - 1) (f x)

fun F th = seq.hd $ resolve_relhyps ["Monoid"] true (global_ruledb()) th
val th = fpow F 20 base
*)
fun prettify th =
  let val (vs, _) = strip_forall (concl th)
  in
    case vs of
      [] => th
    | v::_ => if #1 (dest_type $ type_of $ v) = "monoid" then
                CONV_RULE (RENAME_VARS_CONV ["M"]) th
              else th
end handle HOL_ERR _ => th
fun xfer th =
  th |> time (transfer_thm 10 {hints=[],force_imp=true,cleftp=true}
                              (global_ruledb()))
     |> prettify


Theorem tmonoid_assoc = xfer monoidTheory.monoid_assoc
Theorem tmonoid_lid = xfer monoidTheory.monoid_lid
Theorem tmonoid_rid = xfer monoidTheory.monoid_rid
Theorem tmonoid_id_unique = xfer monoidTheory.monoid_id_unique
Theorem tmonoid_id_element[simp] = xfer monoidTheory.monoid_id_element
Theorem tmonoid_op_element = xfer monoidTheory.monoid_op_element

Theorem lists_respect:
  mequiv lists lists
Proof
  simp[mequiv_def, lists_monoid]
QED
val _ = liftdef lists_respect "list_monoid"

Theorem tmop_list_monoid[simp]:
  tmop list_monoid = APPEND
Proof
  xfer_back_tac[] >> simp[lists_def]
QED

Theorem tmid_list_monoid[simp]:
  tmid list_monoid = []
Proof
  xfer_back_tac [] >> simp[lists_def]
QED

Theorem tmcarrier_list_monoid[simp]:
  tmcarrier list_monoid = UNIV
Proof
  xfer_back_tac [] >> simp[lists_def]
QED

Theorem FiniteMonoid_respect:
  (mequiv ===> (=)) FiniteMonoid FiniteMonoid
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef FiniteMonoid_respect "FiniteMonoid"

Theorem FiniteMonoid_thm = xfer monoidTheory.FiniteMonoid_def

Theorem AbelianMonoid_respect:
  (mequiv ===> (=)) AbelianMonoid AbelianMonoid
Proof simp[mequiv_def, FUN_REL_def]
QED
val _ = liftdef AbelianMonoid_respect "AbelianMonoid"


Theorem FiniteAbelianMonoid_respect:
  (mequiv ===> (=)) FiniteAbelianMonoid FiniteAbelianMonoid
Proof simp[mequiv_def, FUN_REL_def]
QED
val _ = liftdef FiniteAbelianMonoid_respect "FiniteAbelianMonoid"

Theorem FiniteAbelianMonoid_def[allow_rebind] =
        xfer monoidTheory.FiniteAbelianMonoid_def

Theorem FiniteAbelianMonoid_def_alt =
        xfer monoidTheory.FiniteAbelianMonoid_def_alt

Theorem monoid_carrier_nonempty[simp] =
        xfer monoidTheory.monoid_carrier_nonempty

Theorem monoid_exp_respect:
  (mequiv ===> (=) ===> (=) ===> (=)) monoid_exp monoid_exp
Proof
  simp[mequiv_def, FUN_REL_def]
QED
val _ = liftdef monoid_exp_respect "monoid_exp"

Theorem monoid_exp_thm[simp]:
  ∀m.
    (!x. monoid_exp m x 0 = tmid m) /\
    !x n. monoid_exp m x (SUC n) = tmop m x (monoid_exp m x n)
Proof
  xfer_back_tac []  >> simp[]
QED

Theorem monoid_exp_FUNPOW = xfer monoidTheory.monoid_exp_def

Theorem monoid_exp_element[simp] =
        xfer monoidTheory.monoid_exp_element

Theorem monoid_exp_1[simp] = xfer monoidTheory.monoid_exp_1
Theorem monoid_id_exp[simp] = xfer monoidTheory.monoid_id_exp

Theorem monoid_comm_exp = xfer monoidTheory.monoid_comm_exp
Theorem monoid_exp_comm = xfer monoidTheory.monoid_exp_comm
Theorem monoid_comm_op_exp = xfer monoidTheory.monoid_comm_op_exp
Theorem monoid_comm_exp_exp = xfer monoidTheory.monoid_comm_exp_exp
Theorem monoid_exp_add = xfer monoidTheory.monoid_exp_add
Theorem monoid_exp_mult = xfer monoidTheory.monoid_exp_mult
Theorem monoid_exp_mult_comm = xfer monoidTheory.monoid_exp_mult_comm

(* ----------------------------------------------------------------------
    Finite monoids
   ---------------------------------------------------------------------- *)

Theorem finite_monoid_exp_not_distinct =
        xfer monoidTheory.finite_monoid_exp_not_distinct

(* ----------------------------------------------------------------------
    MITSET : iterating monoid operation over (finite) set of elements
   ---------------------------------------------------------------------- *)

Overload MITSET = “λm. ITSET (tmop m)”

Theorem abelian_monoid_op_closure_comm_assoc_fun =
        xfer
             monoidTheory.abelian_monoid_op_closure_comm_assoc_fun

Theorem COMMUTING_MITSET_INSERT =
        xfer COMMUTING_GITSET_INSERT

Theorem COMMUTING_MITSET_REDUCTION =
        xfer COMMUTING_GITSET_REDUCTION

Theorem COMMUTING_MITSET_RECURSES =
        xfer COMMUTING_GITSET_RECURSES

Overload MPROD_SET = “λm s. MITSET m s (tmid m)”

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

Theorem extend_respect:
  (mequiv ===> mequiv) extend extend
Proof
  simp[mequiv_def, FUN_REL_def]
QED
val _ = liftdef extend_respect "tmextend"

Theorem tmextend_carrier[simp] = xfer (GEN_ALL extend_carrier)
Theorem tmextend_id[simp] = xfer (GEN_ALL extend_id)
Theorem tmextend_op = xfer (GEN_ALL extend_op)

Theorem period_respect:
  (mequiv ===> (=) ===> (=) ===> (=)) period period
Proof
  simp[mequiv_def, FUN_REL_def]
QED
val _ = liftdef period_respect "period"

Theorem order_respects:
  (mequiv ===> (=) ===> (=)) order order
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef order_respects "order"

Overload tord[local] = “aatmonoid$order M”

Theorem order_property = xfer order_property
Theorem order_period = xfer order_period
Theorem order_minimal = xfer order_minimal
Theorem order_eq_0 = xfer order_eq_0
Theorem order_thm = xfer order_thm
Theorem monoid_order_id[simp] = xfer monoid_order_id
Theorem monoid_order_eq_1 = xfer monoid_order_eq_1
Theorem monoid_order_condition = xfer monoid_order_condition
Theorem monoid_order_power_eq_0 = xfer monoid_order_power_eq_0
Theorem monoid_order_power = xfer monoid_order_power
Theorem monoid_order_power_eqn = xfer monoid_order_power_eqn
Theorem monoid_order_power_coprime = xfer monoid_order_power_coprime
Theorem monoid_order_cofactor = xfer monoid_order_cofactor
Theorem monoid_order_divisor = xfer monoid_order_divisor
Theorem monoid_order_common = xfer monoid_order_common
Theorem monoid_order_common_coprime = xfer monoid_order_common_coprime
Theorem monoid_exp_mod_order = xfer monoid_exp_mod_order
Theorem abelian_monoid_order_common = xfer abelian_monoid_order_common
Theorem abelian_monoid_order_common_coprime =
        xfer abelian_monoid_order_common_coprime
Theorem abelian_monoid_order_lcm = xfer abelian_monoid_order_lcm

Theorem orders_respects:
  (mequiv ===> (=) ===> (=)) orders orders
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef orders_respects "orders"

Theorem orders_def[allow_rebind] = xfer monoidTheory.orders_def

Theorem orders_element = xfer orders_element
Theorem orders_subset = xfer orders_subset
Theorem orders_finite = xfer orders_finite
Theorem orders_eq_1 = xfer orders_eq_1

Overload maximal_order =
  “\M : 'a monoid. MAX_SET (IMAGE (order M) (tmcarrier M))”

Theorem maximal_order_alt = xfer maximal_order_alt
Theorem monoid_order_divides_maximal =
        xfer monoid_order_divides_maximal

(* ----------------------------------------------------------------------
    Invertibles (prelude to groups)
   ---------------------------------------------------------------------- *)

Theorem monoid_invertibles_respects:
  (mequiv ===> (=)) monoid_invertibles monoid_invertibles
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef monoid_invertibles_respects "monoid_invertibles"

Theorem monoid_invertibles_def[allow_rebind] =
        xfer monoidTheory.monoid_invertibles_def
Theorem monoid_invertibles_element = xfer monoid_invertibles_element
Theorem monoid_order_nonzero = xfer monoid_order_nonzero

Theorem Invertibles_respects:
  (mequiv ===> mequiv) Invertibles Invertibles
Proof
  simp[FUN_REL_def, mequiv_def, monoid_invertibles_is_monoid]
QED
val _ = liftdef Invertibles_respects "Invertibles"

Theorem Invertibles_property[simp] = xfer monoidTheory.Invertibles_property
Theorem Invertibles_subset = xfer monoidTheory.Invertibles_subset
Theorem Invertibles_order = xfer monoidTheory.Invertibles_order

Theorem monoid_inv_from_invertibles =
        xfer monoidTheory.monoid_inv_from_invertibles

Theorem monoid_inv_respects[local]:
  (mequiv ===> (=) ===> (=)) monoid_inv monoid_inv
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef monoid_inv_respects "monoid_inv"

Theorem monoid_inv_def[allow_rebind] = xfer monoidTheory.monoid_inv_def
Theorem monoid_inv_def_alt = xfer monoidTheory.monoid_inv_def_alt
Theorem monoid_inv_element = xfer monoidTheory.monoid_inv_element
Theorem monoid_id_invertible[simp] = xfer monoidTheory.monoid_id_invertible
Theorem monoid_inv_op_invertible[simp] =
        xfer monoidTheory.monoid_inv_op_invertible
Theorem monoid_inv_invertible[simp] = xfer monoidTheory.monoid_inv_invertible

(* ----------------------------------------------------------------------
    Monoid Maps
   ---------------------------------------------------------------------- *)

Theorem MonoidHomo_respects[local]:
  (((=) ===> (=)) ===> mequiv ===> mequiv ===> (=)) MonoidHomo MonoidHomo
Proof
  simp[quotientTheory.FUN_REL_EQ] >> simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef MonoidHomo_respects "MonoidHomo"

Theorem MonoidHomo_def[allow_rebind] = xfer monoidTheory.MonoidHomo_def

Theorem MonoidIso_respects[local]:
  (((=) ===> (=)) ===> mequiv ===> mequiv ===> (=)) MonoidIso MonoidIso
Proof
  simp[quotientTheory.FUN_REL_EQ] >> simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef MonoidIso_respects "MonoidIso"
Theorem MonoidIso_def[allow_rebind] = xfer monoidTheory.MonoidIso_def

Theorem MonoidEndo_respects[local]:
  (((=) ===> (=)) ===> mequiv ===> (=)) MonoidEndo MonoidEndo
Proof
  simp[quotientTheory.FUN_REL_EQ] >> simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef MonoidEndo_respects "MonoidEndo"
Theorem MonoidEndo_def[allow_rebind] = xfer monoidTheory.MonoidEndo_def

Theorem MonoidAuto_respects[local]:
  (((=) ===> (=)) ===> mequiv ===> (=)) MonoidAuto MonoidAuto
Proof
  simp[quotientTheory.FUN_REL_EQ] >> simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef MonoidAuto_respects "MonoidAuto"
Theorem MonoidAuto_def[allow_rebind] = xfer monoidTheory.MonoidAuto_def

Theorem submonoid_respects[local]:
  (mequiv ===> mequiv ===> (=)) submonoid submonoid
Proof
  simp[quotientTheory.FUN_REL_EQ] >> simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef submonoid_respects "submonoid"
Theorem submonoid_def[allow_rebind] = xfer monoidTheory.submonoid_def

Theorem monoid_homo_id = xfer monoidTheory.monoid_homo_id
Theorem monoid_homo_element = xfer monoidTheory.monoid_homo_element
Theorem monoid_homo_cong = xfer monoidTheory.monoid_homo_cong
Theorem monoid_homo_I_refl = xfer monoidTheory.monoid_homo_I_refl
Theorem monoid_homo_trans = xfer monoidTheory.monoid_homo_trans
Theorem monoid_homo_sym = xfer monoidTheory.monoid_homo_sym
Theorem monoid_homo_sym_any = xfer (GEN_ALL monoidTheory.monoid_homo_sym_any)
Theorem monoid_homo_compose = monoid_homo_trans
Theorem monoid_homo_exp = xfer monoidTheory.monoid_homo_exp

Theorem monoid_iso_property = xfer monoidTheory.monoid_iso_property
Theorem monoid_iso_id = xfer monoidTheory.monoid_iso_id
Theorem monoid_iso_element = xfer monoidTheory.monoid_iso_element
Theorem monoid_iso_I_refl = xfer monoidTheory.monoid_iso_I_refl
Theorem monoid_iso_trans = xfer monoidTheory.monoid_iso_trans
Theorem monoid_iso_compose = monoid_iso_trans
Theorem monoid_iso_sym = xfer monoidTheory.monoid_iso_sym
Theorem monoid_iso_linv_iso = monoid_iso_sym
Theorem monoid_iso_exp = xfer monoidTheory.monoid_iso_exp
Theorem monoid_iso_bij = xfer monoidTheory.monoid_iso_bij
Theorem monoid_iso_eq_id = xfer monoidTheory.monoid_iso_eq_id
Theorem monoid_iso_order = xfer monoidTheory.monoid_iso_order
Theorem monoid_iso_card_eq = xfer monoidTheory.monoid_iso_card_eq

Theorem monoid_auto_id = xfer monoidTheory.monoid_auto_id
Theorem monoid_auto_element = xfer monoidTheory.monoid_auto_element
Theorem monoid_auto_compose = xfer monoidTheory.monoid_auto_compose
Theorem monoid_auto_exp = xfer monoidTheory.monoid_auto_exp
Theorem monoid_auto_I = xfer monoidTheory.monoid_auto_I
Theorem monoid_auto_linv_auto = xfer monoidTheory.monoid_auto_linv_auto
Theorem monoid_auto_bij = xfer monoidTheory.monoid_auto_bij
Theorem monoid_auto_order = xfer monoidTheory.monoid_auto_order

Theorem submonoid_eqn = xfer monoidTheory.submonoid_eqn
Theorem submonoid_subset = xfer monoidTheory.submonoid_subset
Theorem submonoid_homo_homo = xfer monoidTheory.submonoid_homo_homo
Theorem submonoid_refl = xfer monoidTheory.submonoid_refl
Theorem submonoid_trans = xfer monoidTheory.submonoid_refl
Theorem submonoid_I_antisym = xfer monoidTheory.submonoid_I_antisym
Theorem submonoid_carrier_antisym = xfer monoidTheory.submonoid_carrier_antisym
Theorem submonoid_order_eqn = xfer monoidTheory.submonoid_order_eqn

Theorem image_op_respects[local]:
  (mequiv ===> ((=) ===> (=)) ===> (=) ===> (=) ===> (=)) image_op image_op
Proof
  simp[quotientTheory.FUN_REL_EQ] >> simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef image_op_respects "image_op"

Theorem image_op_def[allow_rebind] = xfer monoidTheory.image_op_def
Theorem image_op_inj = xfer monoidTheory.image_op_inj

Theorem Monoid_trivial_monoid[simp]:
  Monoid (trivial_monoid e)
Proof
  metis_tac[monoidTheory.FiniteAbelianMonoid_def,
            monoidTheory.AbelianMonoid_def, trivial_monoid]
QED

Theorem trivial_monoid_respects[local]:
  ((=) ===> mequiv) trivial_monoid trivial_monoid
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef trivial_monoid_respects "trivial_monoid"

Theorem set_inter_respects[local]:
  mequiv set_inter set_inter
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef set_inter_respects "set_inter"

Theorem set_inter_abelian_monoid = xfer monoidTheory.set_inter_abelian_monoid

Theorem set_union_respects[local]:
  mequiv set_union set_union
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef set_union_respects "set_union"

Theorem set_union_abelian_monoid = xfer monoidTheory.set_union_abelian_monoid

Definition cmonoid_inj_image_def:
  cmonoid_inj_image f M =
  if INJ f M.carrier UNIV then monoid$monoid_inj_image M f
  else
    trivial_monoid (f M.id)
End
Theorem cmonoid_inj_image_respect[local]:
  (((=) ===> (=)) ===> mequiv ===> mequiv) cmonoid_inj_image cmonoid_inj_image
Proof
  simp[FUN_REL_def, mequiv_def] >> simp[GSYM FUN_EQ_THM] >>
  rw[cmonoid_inj_image_def, monoid_inj_image_monoid]
QED
val _ = liftdef cmonoid_inj_image_respect "monoid_inj_image"

Theorem monoid_inj_image_abelian_monoid:
  AbelianMonoid m ∧ INJ f (tmcarrier m) UNIV ⇒
  AbelianMonoid (monoid_inj_image f m)
Proof
  xfer_back_tac[] >>
  simp[cmonoid_inj_image_def, monoidTheory.monoid_inj_image_abelian_monoid]
QED

Theorem INJ_MonoidIso_exists:
  ∀f M. INJ f (tmcarrier M) UNIV ⇒ ∃N. MonoidIso f M N
Proof
  xfer_back_tac [] >> simp[] >> rpt strip_tac >>
  REWRITE_TAC[Monoid_def] >> rename [‘INJ f M.carrier _’] >>
  qexists
  ‘<| carrier := IMAGE f M.carrier;
      op := λn1 n2. f (M.op (LINV f M.carrier n1) (LINV f M.carrier n2));
      id := f M.id |>’ >>
  simp[PULL_EXISTS] >>
  drule_then strip_assume_tac LINV_DEF >> simp[] >> rpt strip_tac
  >- (irule_at Any EQ_REFL >> qpat_x_assum ‘Monoid _’ mp_tac >>
      REWRITE_TAC[Monoid_def] >> rpt strip_tac >> first_x_assum irule >>
      simp[])
  >- metis_tac[Monoid_def] >>
  simp[monoidTheory.MonoidIso_def] >>
  drule_then strip_assume_tac (SRULE[PULL_EXISTS] INJ_IMAGE_BIJ) >>
  simp[monoidTheory.MonoidHomo_def]
QED


(* ----------------------------------------------------------------------
    MITBAG (lifted from GITBAG)
   ---------------------------------------------------------------------- *)

Overload MITBAG = “λ(M:'a monoid) s b. ITBAG (tmop M) s b”

Theorem MITBAG_EMPTY = xfer monoidTheory.GITBAG_EMPTY
Theorem COMMUTING_MITBAG_INSERT = xfer monoidTheory.COMMUTING_GITBAG_INSERT
Theorem MITBAG_INSERT_THM = xfer monoidTheory.GITBAG_INSERT_THM
Theorem MITBAG_UNION = xfer monoidTheory.GITBAG_UNION
Theorem MITBAG_in_carrier = xfer monoidTheory.GITBAG_in_carrier

Overload MBAG = “λ(M:'a monoid) b. MITBAG M b (tmid M)”
Theorem MBAG_in_carrier = xfer monoidTheory.GBAG_in_carrier
Theorem MITBAG_MBAG = xfer monoidTheory.GITBAG_GBAG
Theorem MBAG_UNION = xfer (GEN_ALL monoidTheory.GBAG_UNION)
Theorem MITBAG_BAG_IMAGE_op = xfer monoidTheory.GITBAG_BAG_IMAGE_op
Theorem IMP_MBAG_EQ_ID = xfer $ GEN_ALL monoidTheory.IMP_GBAG_EQ_ID
Theorem MITBAG_CONG = xfer $ GEN_ALL monoidTheory.GITBAG_CONG

Theorem MBAG_IMAGE_PARTITION = xfer $ GEN_ALL GBAG_IMAGE_PARTITION


(*
val _ = show_assums := true
val rdb = global_ruledb()
val cleftp = true
val cfg = {force_imp = true, cleftp = true,
           hints = [ ]  :string list}
val base = transfer_skeleton rdb cfg (concl $ GEN_ALL GBAG_IMAGE_PARTITION)
val th = base


fun fpow f n x = if n <= 0 then x else fpow f (n - 1) (f x)

fun F th = seq.hd $ resolve_relhyps [] cleftp rdb th
val th = time (fpow F 50) base

    fpow F 18 base
*)



val _ = export_theory();
