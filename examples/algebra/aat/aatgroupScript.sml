open HolKernel Parse boolLib bossLib;

open aatmonoidTheory groupTheory transferTheory transferLib liftingTheory

open liftLib

val _ = new_theory "aatgroup";

Theorem Group_respects[local]:
  (mequiv ===> (=)) Group Group
Proof
  simp[FUN_REL_def, mequiv_def]
QED
val _ = liftdef Group_respects "isgroup"

Definition gequiv_def:
  gequiv g1 g2 ⇔ g1 = g2 ∧ Group g2
End

Theorem groups_exist:
  ∃g:'a monoid$monoid. Group g
Proof
  simp[groupTheory.Group_def] >>
  qexists ‘<| carrier := {x}; id := x; op := λa b. x |>’ >>
  simp_tac (bool_ss ++ combinSimps.COMBIN_ss ++
            rewrites $ #rewrs $ TypeBase.simpls_of “:'a monoid$monoid”)
           [monoidTheory.Monoid_def] >>
  simp[monoidTheory.monoid_invertibles_def]
QED

val grec = newtypeTools.rich_new_type {tyname = "group",
                                       exthm = groups_exist,
                                       ABS = "mkgroup",
                                       REP = "destgroup"}


Definition GCA_def:
  GCA r a ⇔ Group r ∧ mkgroup r = a
End

Theorem Group_relates[transfer_rule]:
  (GCA ===> (=)) Group (K T)
Proof
  simp[FUN_REL_def, GCA_def]
QED

Theorem GCAeq_relates[transfer_rule]:
  (GCA ===> GCA ===> (=)) (=) (=)
Proof
  simp[GCA_def, FUN_REL_def, #termP_term_REP grec, #term_ABS_pseudo11 grec]
QED

Theorem right_unique_AR[transfer_simp]:
  right_unique GCA
Proof
  simp[right_unique_def, GCA_def, #term_REP_11 grec]
QED

Theorem surj_GCA[transfer_simp]:
  surj GCA
Proof
  simp[surj_def, GCA_def] >> qx_gen_tac ‘g’ >> qexists ‘destgroup g’ >>
  simp[#termP_term_REP grec, #absrep_id grec]
QED

Theorem RDOM_GCA[transfer_simp]:
  RDOM GCA = { gr | Group gr }
Proof
  simp[relationTheory.RDOM_DEF, Once FUN_EQ_THM, GCA_def]
QED

Theorem Qt_groups[liftQt]:
  Qt gequiv mkgroup destgroup GCA
Proof
  simp[Qt_alt, #absrep_id grec, GCA_def, FUN_EQ_THM, gequiv_def,
       #termP_term_REP grec] >>
  simp[#term_ABS_pseudo11 grec, SF CONJ_ss] >> metis_tac[]
QED

Theorem AbelianGroup_respect:
  (gequiv ===> (=)) AbelianGroup AbelianGroup
Proof
  simp[FUN_REL_def, gequiv_def]
QED
val _ = liftdef AbelianGroup_respect "AbelianGroup"

Theorem FiniteGroup_respect:
  (gequiv ===> (=)) FiniteGroup FiniteGroup
Proof
  simp[FUN_REL_def, gequiv_def]
QED
val _ = liftdef FiniteGroup_respect "FiniteGroup"

Theorem FiniteAbelianGroup_respect:
  (gequiv ===> (=)) FiniteAbelianGroup FiniteAbelianGroup
Proof
  simp[FUN_REL_def, gequiv_def]
QED
val _ = liftdef FiniteAbelianGroup_respect "FiniteAbelianGroup"


Theorem G2M[liftQt]:
  Qt (gequiv ===> mequiv)
     (destgroup ---> (mkmonoid: α monoid$monoid -> α monoid))
     ((mkgroup : α group$group -> α group) ---> monoid_REP)
     (GCA ===> MTR)
Proof
  irule funQ >> simp[Qt_groups, Qt_monoid]
QED

Definition G2M_def:
  G2M = (destgroup ---> mkmonoid) I
End

Theorem Rtt[local]:
  (gequiv ===> mequiv) I I
Proof
  simp[FUN_REL_def, gequiv_def, mequiv_def, Group_def]
QED

Theorem G2M_relates[transfer_rule] =
        MATCH_MP HK_thm2 (CONJ G2M (CONJ G2M_def Rtt))

(*
val _ = show_assums := true
val rdb = global_ruledb()
val cleftp = false
val cfg = {force_imp = false, cleftp = cleftp,
           hints = [ ]  :string list}
val base = transfer_skeleton rdb cfg (#2 (top_goal()))
val th = base


fun fpow f n x = if n <= 0 then x else fpow f (n - 1) (f x)

fun F th = seq.hd $ resolve_relhyps [] cleftp rdb th

    fpow F 7 th
*)

Theorem G2M_11[simp]:
  ∀g1 g2. G2M g1 = G2M g2 ⇔ g1 = g2
Proof
  xfer_back_tac []
QED

Theorem gcarrier_respect:
  (gequiv ===> (=) ===> (=)) monoid_carrier monoid_carrier
Proof
  simp[FUN_REL_def, gequiv_def]
QED
val _ = liftdef gcarrier_respect "carrier"

Theorem gid_respect:
  (gequiv ===> (=)) monoid_id monoid_id
Proof
  simp[FUN_REL_def, gequiv_def]
QED
val _ = liftdef gid_respect "id"

Theorem gop_respect:
  (gequiv ===> (=) ===> (=) ===> (=)) monoid_op monoid_op
Proof
  simp[FUN_REL_def, gequiv_def]
QED
val _ = liftdef gop_respect "opn"

Theorem group_all_invertible:
  ∀g. monoid_invertibles (G2M g) = carrier g
Proof
  xfer_back_tac[] >> simp[]
QED

val _ = permahide “aatmonoid$Invertibles”

Theorem Qt_m2g[liftQt]:
  Qt (mequiv ===> gequiv)
     (monoid_REP ---> (mkgroup : α monoid$monoid -> α group))
     ((mkmonoid : α monoid$monoid -> α monoid) ---> destgroup)
     (MTR ===> GCA)
Proof
  irule funQ >> simp[Qt_groups, Qt_monoid]
QED

Theorem Invertibles_respect:
  (mequiv ===> gequiv) monoid$Invertibles monoid$Invertibles
Proof
  simp[FUN_REL_def, mequiv_def, gequiv_def, monoid_invertibles_is_group]
QED

val _ = liftdef Invertibles_respect "Invertibles"

fun xfer th =
  th |> time (transfer_thm 10 {hints=[],force_imp=true,cleftp=true}
                              (global_ruledb()))

Theorem finite_monoid_invertibles_is_finite_group =
        xfer groupTheory.finite_monoid_invertibles_is_finite_group

Theorem FiniteAbelianGroup_def_alt =
        xfer groupTheory.FiniteAbelianGroup_def_alt
Theorem finite_group_is_finite_monoid:
  FiniteGroup g ⇒ FiniteMonoid (G2M g)
Proof
  xfer_back_tac [] >> simp[groupTheory.finite_group_is_finite_monoid]
QED
Theorem abelian_group_is_abelian_monoid:
  AbelianGroup g ⇒ AbelianMonoid (G2M g)
Proof
  xfer_back_tac [] >> simp[groupTheory.abelian_group_is_abelian_monoid]
QED
Theorem finite_abelian_group_is_finite_abelian_monoid:
  FiniteAbelianGroup g ⇒ FiniteAbelianMonoid (G2M g)
Proof
  xfer_back_tac [] >>
  simp[groupTheory.finite_abelian_group_is_finite_abelian_monoid]
QED

Theorem isgroup_G2M[simp]:
  isgroup (G2M g)
Proof
  xfer_back_tac[] >> simp[]
QED

Definition MGR_def:
  MGR m g ⇔ m = G2M g
End

Definition tmequiv_def:
  tmequiv m1 m2 ⇔ m1 = m2 ∧ isgroup m2
End

Theorem MGReq_relates[transfer_rule]:
  (MGR ===> MGR ===> (=)) (=) (=)
Proof
  simp[MGR_def, FUN_REL_def]
QED

Theorem right_unique_MGR[transfer_simp]:
  right_unique MGR
Proof
  simp[right_unique_def, MGR_def]
QED

Theorem surj_MGR[transfer_simp]:
  surj MGR
Proof
  simp[surj_def, MGR_def] >> xfer_back_tac[] >> simp[]
QED

Theorem RDOM_MGR[transfer_simp]:
  RDOM MGR = { m | isgroup m }
Proof
  simp[relationTheory.RDOM_DEF, Once FUN_EQ_THM, MGR_def] >>
  rw[EQ_IMP_THM] >> xfer_back_tac [] >> simp[]
QED

Theorem group_id_mrelates[transfer_rule]:
  (MGR ===> (=)) tmid id
Proof
  simp[FUN_REL_def, MGR_def] >> xfer_back_tac[]
QED

Theorem group_carrier_mrelates[transfer_rule]:
  (MGR ===> (=) ===> (=)) tmcarrier carrier
Proof
  simp[FUN_REL_def, MGR_def] >> xfer_back_tac []
QED

Theorem group_op_mrelates[transfer_rule]:
  (MGR ===> $= ===> $= ===> $=) tmop opn
Proof
  simp[FUN_REL_def, MGR_def] >> xfer_back_tac[]
QED

Theorem group_id_element[simp] = xfer tmonoid_id_element
Theorem group_op_element = xfer tmonoid_op_element
Theorem group_assoc = xfer tmonoid_assoc
Theorem group_lid = xfer tmonoid_lid
Theorem group_rid = xfer tmonoid_rid
Theorem group_id_unique = xfer tmonoid_id_unique

Theorem m2g_exists:
  ∀m. isgroup m ⇒ ∃g. G2M g = m
Proof
  xfer_back_tac[] >> simp[]
QED
val m2g_def = new_specification("m2g_def", ["m2g"],
                                SRULE[GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]
                                     m2g_exists)

Theorem m2g_G2M[simp]:
  m2g (G2M g) = g
Proof
  ‘isgroup (G2M g)’ by simp[] >> drule m2g_def >> simp[]
QED

Theorem m2g_pseudo11:
  ∀m1 m2. isgroup m1 ∧ isgroup m2 ⇒ (m2g m1 = m2g m2 ⇔ m1 = m2)
Proof
  rw[EQ_IMP_THM] >> rpt (dxrule m2g_def) >> simp[] >>
  rpt (disch_then (SUBST1_TAC o SYM)) >> simp[]
QED

Theorem Qt_tmequiv[liftQt]:
  Qt tmequiv m2g G2M MGR
Proof
  simp[Qt_alt, MGR_def, FUN_EQ_THM, tmequiv_def] >>
  simp[SF CONJ_ss, m2g_pseudo11, AC CONJ_ASSOC CONJ_COMM] >>
  simp[SF CONJ_ss] >> simp[EQ_IMP_THM, m2g_def]
QED

Theorem group_exp_respect[local]:
  (gequiv ===> $= ===> $= ===> $=) monoid_exp monoid_exp
Proof
  simp[FUN_REL_def, gequiv_def]
QED
val _ = liftdef group_exp_respect "group_exp"

Theorem group_exp_mrelates[transfer_rule]:
  (MGR ===> (=) ===> (=) ===> (=)) monoid_exp group_exp
Proof
  simp[FUN_REL_def, MGR_def] >> xfer_back_tac[]
QED

Theorem group_exp_element = xfer monoid_exp_element
Theorem group_exp_thm = xfer monoid_exp_thm
Theorem group_exp_1 = xfer monoid_exp_1
Theorem group_id_exp = xfer monoid_id_exp
Theorem group_comm_exp = xfer monoid_comm_exp
Theorem group_exp_comm = xfer monoid_exp_comm
Theorem group_comm_op_exp = xfer monoid_comm_op_exp
Theorem group_exp_add = xfer monoid_exp_add
Theorem group_exp_mult = xfer monoid_exp_mult

Theorem group_inv_respect:
  (gequiv ===> $= ===> $=) monoid$monoid_inv monoid$monoid_inv
Proof
  simp[FUN_REL_def, gequiv_def]
QED
val _ = liftdef group_inv_respect "group_inv"

Theorem group_inv_element = xfer group_inv_element
Theorem group_linv = xfer group_linv
Theorem group_rinv = xfer group_rinv
Theorem group_inv_thm = xfer group_inv_thm
Theorem group_carrier_nonempty = xfer group_carrier_nonempty
Theorem group_lcancel = xfer group_lcancel
Theorem group_rcancel = xfer group_rcancel
Theorem group_linv_assoc = GSYM $ xfer group_linv_assoc
Theorem group_rinv_assoc = GSYM $ xfer group_rinv_assoc
Theorem group_lsolve = xfer group_lsolve
Theorem group_rsolve = xfer group_rsolve
Theorem group_lid_unique = xfer group_lid_unique
Theorem group_rid_unique = xfer group_rid_unique
Theorem group_linv_unique = xfer group_linv_unique
Theorem group_rinv_unique = xfer group_rinv_unique
Theorem group_inv_inv = xfer group_inv_inv
Theorem group_inv_eq = xfer group_inv_eq
Theorem group_inv_eq_swap = xfer group_inv_eq_swap
Theorem group_inv_id[simp] = xfer group_inv_id
Theorem group_inv_op = xfer group_inv_op
Theorem group_pair_reduce = xfer group_pair_reduce
Theorem group_id_fix = xfer group_id_fix
Theorem group_op_linv_eq_id = xfer group_op_linv_eq_id
Theorem group_op_rinv_eq_id = xfer group_op_rinv_eq_id

Theorem Invertibles_inv = xfer Invertibles_inv
Theorem monoid_inv_id = xfer monoid_inv_id

Theorem group_axioms_alt = xfer group_def_alt

Theorem isgroup_by_inverse = xfer group_def_by_inverse
Theorem group_concise_axioms = xfer group_alt

(* not sure what, if anything, to do with excluding/including construction *)

Theorem group_exp_inv = xfer groupTheory.group_exp_inv

val _ = export_theory();
