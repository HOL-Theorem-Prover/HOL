open HolKernel Parse boolLib bossLib;

open monoidTheory liftingTheory transferTheory transferLib
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

Theorem Qt_monoid:
  Qt mequiv mkmonoid monoid_REP MTR
Proof
  simp[Qt_alt, MTR_def, FUN_EQ_THM, #absrep_id mrec, #termP_term_REP mrec,
       mequiv_def] >>
  rw[EQ_IMP_THM] >> gvs[#term_ABS_pseudo11 mrec]
QED

Theorem funQ'[local] = SRULE[GSYM AND_IMP_INTRO] funQ |> GEN_ALL

Theorem HK_thm2'[local] = HK_thm2 |> GEN_ALL |> SRULE[]

Theorem carrier_respects:
  (mequiv ===> $=) monoid_carrier monoid_carrier
Proof
  simp[FUN_REL_def, FUN_EQ_THM, mequiv_def]
QED

fun grt th1 th2 = resolve_then.gen_resolve_then Any th1 th2 I

fun tidy_tyvars th =
  let val tyvs = type_vars_in_term (concl th)
      val newvs =
        List.tabulate(length tyvs,
                      fn i => mk_vartype("'" ^ str (Char.chr(i + 97))))
  in
      INST_TYPE (ListPair.map(fn (ty1,ty2) => ty1 |-> ty2) (tyvs, newvs)) th
  end

fun opxfer res_th =
  grt res_th HK_thm2 |> repeat (grt funQ') |> repeat (grt Qt_monoid)
                     |> repeat (grt idQ) |> tidy_tyvars
                     |> CONV_RULE Unwind.UNWIND_FORALL_CONV

val xfer_carrier = opxfer carrier_respects
Definition tmcarrier_def:
  tmcarrier = ^(rand $ concl xfer_carrier)
End
Theorem tmcarrier_relates[transfer_rule] =
  SRULE[GSYM tmcarrier_def] xfer_carrier

Theorem id_respects:
  (mequiv ===> $=) monoid_id monoid_id
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val xfer_id = opxfer id_respects
Definition tmid_def:
  tmid = ^(rand $ concl xfer_id)
End
Theorem tmid_relates[transfer_rule] = SRULE[GSYM tmid_def] xfer_id

Theorem op_respects:
  (mequiv ===> $= ===> $= ===> $=) monoid_op monoid_op
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val xfer_op = opxfer op_respects
Definition tmop_def:
  tmop = ^(rand $ concl xfer_op)
End
Theorem tmop_relates[transfer_rule] = REWRITE_RULE[GSYM tmop_def] xfer_op

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

Definition list_monoid_def:
  list_monoid = mkmonoid <| carrier := UNIV; op := APPEND; id := [] |>
End

Theorem rep_list_monoid[simp,local]:
  monoid_REP list_monoid = <| carrier := UNIV; op := APPEND; id := [] |>
Proof
  simp[list_monoid_def] >> irule repabs_pseudo_id >> simp[Monoid_def]
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
  simp[FiniteMonoid_def, FUN_REL_def, MTR_def, repabs_pseudo_id]
QED

Theorem FiniteMonoid_thm = xfer monoidTheory.FiniteMonoid_def

Definition AbelianMonoid_def:
  AbelianMonoid m = monoid$AbelianMonoid (monoid_REP m)
End

Theorem AbelianMonoid_relates[transfer_rule]:
  (MTR |==> (=)) AbelianMonoid AbelianMonoid
Proof
  irule HK_thm2 >> irule_at Any funQ' >> irule_at Any Qt_monoid >>
  irule_at Any idQ >>
  simp[AbelianMonoid_def, FUN_REL_def, mequiv_def, FUN_EQ_THM]
QED

Definition FiniteAbelianMonoid_DEF:
  FiniteAbelianMonoid (m:α monoid) ⇔ monoid$FiniteAbelianMonoid (monoid_REP m)
End

Theorem FiniteAbelianMonoid_relates[transfer_rule]:
  (MTR |==> (=)) FiniteAbelianMonoid FiniteAbelianMonoid
Proof
  irule HK_thm2 >> irule_at Any funQ' >> irule_at Any Qt_monoid >>
  irule_at Any idQ >>
  simp[FiniteAbelianMonoid_DEF, FUN_REL_def, mequiv_def, FUN_EQ_THM]
QED

Theorem FiniteAbelianMonoid_def =
        xfer monoidTheory.FiniteAbelianMonoid_def

Theorem FiniteAbelianMonoid_def_alt =
        xfer monoidTheory.FiniteAbelianMonoid_def_alt

Theorem monoid_carrier_nonempty[simp] =
        xfer monoidTheory.monoid_carrier_nonempty

Definition monoid_exp_def:
  monoid_exp m x n = monoid$monoid_exp (monoid_REP m) x n
End

Theorem monoid_exp_relates[transfer_rule]:
  (MTR |==> (=) |==> (=) |==> (=)) monoid_exp monoid_exp
Proof
  irule HK_thm2 >> rpt $ irule_at Any funQ' >> irule_at Any Qt_monoid >>
  rpt $ irule_at Any idQ >>
  simp[monoid_exp_def, FUN_REL_def, mequiv_def, FUN_EQ_THM]
QED

Theorem monoid_exp_thm[simp]:
  !m x. monoid_exp m x 0 = tmid m /\
        !n. monoid_exp m x (SUC n) = tmop m x (monoid_exp m x n)
Proof
  xfer_back_tac []  >> simp[]
QED

Theorem monoid_exp_FUNPOW =
        xfer monoidTheory.monoid_exp_def

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

Definition tmextend_def:
  tmextend m = mkmonoid (extend (monoid_REP m))
End

Theorem tmextend_relates[transfer_rule]:
  (MTR |==> MTR) extend tmextend
Proof
  irule HK_thm2 >> rpt $ irule_at Any funQ' >> rpt $ irule_at Any Qt_monoid >>
  rpt $ irule_at Any idQ >>
  simp[tmextend_def, FUN_REL_def, mequiv_def, FUN_EQ_THM]
QED

Theorem tmextend_carrier[simp] = xfer (GEN_ALL extend_carrier)
Theorem tmextend_id[simp] = xfer (GEN_ALL extend_id)
Theorem tmextend_op = xfer (GEN_ALL extend_op)

Definition period_def:
  period m x k = monoid$period (monoid_REP m) x k
End

Theorem period_relates[transfer_rule]:
  (MTR |==> (=) |==> (=) |==> (<=>)) period period
Proof
  irule HK_thm2 >> rpt $ irule_at Any funQ' >> rpt $ irule_at Any Qt_monoid >>
  rpt $ irule_at Any idQ >>
  simp[period_def, FUN_REL_def, mequiv_def, FUN_EQ_THM]
QED

Theorem order_respects:
  (mequiv ===> (=) ===> (=)) order order
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val xfer_order = opxfer order_respects
Definition order_def:
  order = ^(rand $ concl xfer_order)
End
Theorem order_relates[transfer_rule] =
  REWRITE_RULE[GSYM order_def] xfer_order

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
val xfer_orders = opxfer orders_respects
Definition orders_DEF:
  orders = ^(rand $ concl xfer_orders)
End
Theorem orders_relates[transfer_rule] =
  REWRITE_RULE[GSYM orders_DEF] xfer_orders

Theorem orders_def = xfer monoidTheory.orders_def

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
val xfer_monoid_invertibles = opxfer monoid_invertibles_respects
Definition monoid_invertibles_DEF:
  monoid_invertibles = ^(rand $ concl xfer_monoid_invertibles)
End
Theorem monoid_invertibles_relate[transfer_rule] =
  REWRITE_RULE[GSYM monoid_invertibles_DEF] xfer_monoid_invertibles

Theorem monoid_invertibles_def :
  monoid_invertibles M =
  { x | x IN tmcarrier M ∧
        ∃y. y IN tmcarrier M ∧ tmop M x y = tmid M ∧
            tmop M y x = tmid M }
Proof
  qid_spec_tac ‘M’ >> xfer_back_tac [] >>
  simp[monoidTheory.monoid_invertibles_def]
QED

Theorem monoid_invertibles_element =
        xfer monoid_invertibles_element
Theorem monoid_order_nonzero = xfer monoid_order_nonzero

Theorem Invertibles_respects[local]:
  (mequiv ===> mequiv) Invertibles Invertibles
Proof
  simp[FUN_REL_def, mequiv_def, monoid_invertibles_is_monoid]
QED
val xfer_Invertibles = opxfer Invertibles_respects
Definition Invertibles_def:
  Invertibles = ^(rand $ concl xfer_Invertibles)
End
Theorem Invertibles_relate[transfer_rule] =
        REWRITE_RULE[GSYM Invertibles_def] xfer_Invertibles

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
val xfer_monoid_inv = opxfer monoid_inv_respects
Definition monoid_inv_def0:
  monoid_inv = ^(rand $ concl xfer_monoid_inv)
End

Theorem monoid_inv_relate[transfer_rule] =
        REWRITE_RULE[GSYM monoid_inv_def0] xfer_monoid_inv

Theorem monoid_inv_def = xfer monoidTheory.monoid_inv_def
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
val xfer_MonoidHomo = opxfer MonoidHomo_respects
Definition MonoidHomo_def0:
  MonoidHomo = ^(rand $ concl xfer_MonoidHomo)
End
Theorem MonoidHomo_relate[transfer_rule] =
        REWRITE_RULE[GSYM MonoidHomo_def0] xfer_MonoidHomo

Theorem MonoidHomo_def = xfer monoidTheory.MonoidHomo_def

Theorem MonoidIso_respects[local]:
  (((=) ===> (=)) ===> mequiv ===> mequiv ===> (=)) MonoidIso MonoidIso
Proof
  simp[quotientTheory.FUN_REL_EQ] >> simp[FUN_REL_def, mequiv_def]
QED
val xfer_MonoidIso = opxfer MonoidIso_respects
Definition MonoidIso_def0:
  MonoidIso = ^(rand $ concl xfer_MonoidIso)
End
Theorem MonoidIso_relate[transfer_rule] =
        REWRITE_RULE[GSYM MonoidIso_def0] xfer_MonoidIso
Theorem MonoidIso_def = xfer monoidTheory.MonoidIso_def

Theorem MonoidEndo_respects[local]:
  (((=) ===> (=)) ===> mequiv ===> (=)) MonoidEndo MonoidEndo
Proof
  simp[quotientTheory.FUN_REL_EQ] >> simp[FUN_REL_def, mequiv_def]
QED
val xfer_MonoidEndo = opxfer MonoidEndo_respects
Definition MonoidEndo_def0:
  MonoidEndo = ^(rand $ concl xfer_MonoidEndo)
End
Theorem MonoidEndo_relate[transfer_rule] =
        REWRITE_RULE[GSYM MonoidEndo_def0] xfer_MonoidEndo
Theorem MonoidEndo_def = xfer monoidTheory.MonoidEndo_def

Theorem MonoidAuto_respects[local]:
  (((=) ===> (=)) ===> mequiv ===> (=)) MonoidAuto MonoidAuto
Proof
  simp[quotientTheory.FUN_REL_EQ] >> simp[FUN_REL_def, mequiv_def]
QED
val xfer_MonoidAuto = opxfer MonoidAuto_respects
Definition MonoidAuto_def0:
  MonoidAuto = ^(rand $ concl xfer_MonoidAuto)
End
Theorem MonoidAuto_relate[transfer_rule] =
        REWRITE_RULE[GSYM MonoidAuto_def0] xfer_MonoidAuto
Theorem MonoidAuto_def = xfer monoidTheory.MonoidAuto_def

Theorem submonoid_respects[local]:
  (mequiv ===> mequiv ===> (=)) submonoid submonoid
Proof
  simp[quotientTheory.FUN_REL_EQ] >> simp[FUN_REL_def, mequiv_def]
QED
val xfer_submonoid = opxfer submonoid_respects
Definition submonoid_def0:
  submonoid = ^(rand $ concl xfer_submonoid)
End
Theorem submonoid_relate[transfer_rule] =
        REWRITE_RULE[GSYM submonoid_def0] xfer_submonoid
Theorem submonoid_def = xfer monoidTheory.submonoid_def

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
val xfer_image_op = opxfer image_op_respects
Definition image_op_def0:
  image_op = ^(rand $ concl xfer_image_op)
End
Theorem image_op_relate[transfer_rule] =
        REWRITE_RULE[GSYM image_op_def0] xfer_image_op

Theorem image_op_def = xfer monoidTheory.image_op_def
Theorem image_op_inj = xfer monoidTheory.image_op_inj

Theorem trivial_monoid_respects[local]:
  ((=) ===> mequiv) trivial_monoid trivial_monoid
Proof
  simp[FUN_REL_def, mequiv_def] >> qx_gen_tac ‘e’ >>
  qspec_then ‘e’ mp_tac trivial_monoid >>
  simp[monoidTheory.FiniteAbelianMonoid_def, monoidTheory.AbelianMonoid_def]
QED
val xfer_trivial_monoid = opxfer trivial_monoid_respects
Definition trivial_monoid_def0:
  trivial_monoid = ^(rand $ concl xfer_trivial_monoid)
End
Theorem trivial_monoid_relate[transfer_rule] =
        REWRITE_RULE[GSYM trivial_monoid_def0] xfer_trivial_monoid

Theorem set_inter_respects[local]:
  mequiv set_inter set_inter
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val xfer_set_inter = opxfer set_inter_respects
Definition set_inter_def0:
  set_inter = ^(rand $ concl xfer_set_inter)
End
Theorem set_inter_relate[transfer_rule] =
        REWRITE_RULE[GSYM set_inter_def0] xfer_set_inter

Theorem set_inter_abelian_monoid = xfer monoidTheory.set_inter_abelian_monoid

Theorem set_union_respects[local]:
  mequiv set_union set_union
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val xfer_set_union = opxfer set_union_respects
Definition set_union_def0:
  set_union = ^(rand $ concl xfer_set_union)
End
Theorem set_union_relate[transfer_rule] =
        REWRITE_RULE[GSYM set_union_def0] xfer_set_union

Theorem set_union_abelian_monoid = xfer monoidTheory.set_union_abelian_monoid

Definition monoid_inj_image_def:
  monoid_inj_image f M =
  if INJ f (tmcarrier M) UNIV then
    mkmonoid (monoid$monoid_inj_image (monoid_REP M) f)
  else
    trivial_monoid (f (tmid M))
End

Theorem INJ_MonoidIso_exists:
  ∀f M. INJ f (tmcarrier M) UNIV ⇒ ∃N. MonoidIso f M N
Proof
  xfer_back_tac [] >> simp[] >> rpt strip_tac >>
  REWRITE_TAC[Monoid_def] >>
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

Theorme MBAG_IMAGE_PARTITION = xfer $ GEN_ALL GBAG_IMAGE_PARTITION


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
