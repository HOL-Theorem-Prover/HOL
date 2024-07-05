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
    if #1 (dest_type $ type_of $ hd vs) = "monoid" then
      CONV_RULE (RENAME_VARS_CONV ["M"]) th
    else th
  end handle HOL_ERR _ => th
fun xfer hs th =
  th |> transfer_thm 10 ("Monoid"::hs) true (global_ruledb())
     |> prettify


Theorem tmonoid_assoc = xfer [] monoid_assoc
Theorem tmonoid_lid = xfer [] monoid_lid
Theorem tmonoid_rid = xfer [] monoid_rid
Theorem tmonoid_id_unique = xfer [] monoid_id_unique

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
        xfer ["FiniteAbelianMonoid"] monoidTheory.FiniteAbelianMonoid_def

Theorem FiniteAbelianMonoid_def_alt =
        xfer ["FiniteAbelianMonoid"] monoidTheory.FiniteAbelianMonoid_def_alt

Theorem monoid_carrier_nonempty[simp] =
        xfer [] monoidTheory.monoid_carrier_nonempty

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
        xfer ["monoid_exp"] monoidTheory.monoid_exp_def

Theorem monoid_exp_element[simp] =
        xfer ["monoid_exp"] monoidTheory.monoid_exp_element

Theorem monoid_exp_1[simp] = xfer [] monoidTheory.monoid_exp_1
Theorem monoid_id_exp[simp] = xfer [] monoidTheory.monoid_id_exp

Theorem monoid_comm_exp = xfer [] monoidTheory.monoid_comm_exp
Theorem monoid_exp_comm = xfer [] monoidTheory.monoid_exp_comm
Theorem monoid_comm_op_exp = xfer [] monoidTheory.monoid_comm_op_exp
Theorem monoid_comm_exp_exp = xfer [] monoidTheory.monoid_comm_exp_exp
Theorem monoid_exp_add = xfer [] monoidTheory.monoid_exp_add
Theorem monoid_exp_mult = xfer [] monoidTheory.monoid_exp_mult
Theorem monoid_exp_mult_comm = xfer [] monoidTheory.monoid_exp_mult_comm

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

Theorem tmextend_carrier[simp] = xfer ["extend"] (GEN_ALL extend_carrier)
Theorem tmextend_id[simp] = xfer ["extend"] (GEN_ALL extend_id)
Theorem tmextend_op = xfer ["extend"] (GEN_ALL extend_op)

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

Theorem orders_def = xfer ["orders"] monoidTheory.orders_def

Theorem orders_element = xfer ["orders"] orders_element
Theorem orders_subset = xfer ["orders"] orders_subset
Theorem orders_finite = xfer ["orders"] orders_finite
Theorem orders_eq_1 = xfer ["orders"] orders_eq_1

Overload maximal_order =
  “\M : 'a monoid. MAX_SET (IMAGE (order M) (tmcarrier M))”

Theorem maximal_order_alt = xfer ["order"] maximal_order_alt
Theorem monoid_order_divides_maximal =
        xfer ["order"] monoid_order_divides_maximal

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
        xfer ["monoid_invertibles"] monoid_invertibles_element
Theorem monoid_order_nonzero = xfer ["monoid_invertibles"] monoid_order_nonzero

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

val _ = export_theory();
