open HolKernel boolLib bossLib
open relationSyntax relation_extraLib
open relation_extraTheory mmTheory mm_lemmasTheory
open arm8_commonTheory arm8_evTheory arm8_ecTheory arm8_egcTheory

val () = new_theory "arm8_equiv"

(* -------------------------------------------------------------------------
   Helper tactics
   ------------------------------------------------------------------------- *)

fun imp_res_or_assume thms =
  let
    val (l1, l2) = List.partition (boolSyntax.is_imp_only o Thm.concl) thms
  in
    map_every imp_res_tac l1
    \\ map_every (assume_tac o GEN_ALL) l2
  end

fun wf_tac thms1 thms2 =
  TRY strip_tac
  \\ qpat_assum `WellFormed G`
       (strip_assume_tac o SIMP_RULE (srw_ss()) (WellFormed::thms1))
  \\ imp_res_or_assume thms2

fun tac thms1 thms2 =
  rw thms1
  \\ imp_res_or_assume thms2
  \\ rpt (first_x_assum (SUBST1_TAC o SPEC_ALL))
  \\ xrw [] \\ simp []
  \\ eq_tac
  \\ xrw [] \\ simp []

fun simple_cond_rewr th (gl as (asl, w)) =
  let
    val pat =
      th |> Drule.SPEC_ALL |> Thm.concl |> boolSyntax.dest_imp_only |> #2 |> lhs
    val (s1, s2) = Term.match_term pat w
    val th' = Thm.INST s1 (Thm.INST_TYPE s2 th)
  in
    Tactical.SUBGOAL_THEN (#2 (boolSyntax.dest_imp_only (concl th')))
      (ONCE_REWRITE_TAC o Lib.list_of_singleton)
    \\ TRY (match_mp_tac th')
  end gl

(* -------------------------------------------------------------------------
   Theorems
   ------------------------------------------------------------------------- *)

(* - Mixed-size equivalence classes ---------------------------------------- *)

Theorem erln_trans:
  WellFormed G ==> transitive (erln G)
Proof
  wf_tac [wf_rff_def, functional] [wf_rfeD]
  \\ simp [erln, rfisw, rfi, si, ER, IR, relationTheory.RUNION_ASSOC,
           GSYM runion_rinter_r]
  \\ pop_assum SUBST1_TAC
  \\ xsimp [rfe, relationTheory.transitive_def,
            SIMP_RULE std_ss [relationTheory.reflexive_def] ext_si_refl]
  \\ metis_tac [ext_si_trans, relationTheory.transitive_def, label_distinct]
QED

Theorem erln_sym:
  symmetric (erln G)
Proof
  xsimp [erln, rfisw, relationTheory.symmetric_def]
  \\ metis_tac [si_sym, relationTheory.symmetric_def]
QED

Theorem erln_in_si:
  erln G RSUBSET si G
Proof
  xrw [erln, si]
  \\ simp []
  \\ metis_tac [ext_si_refl, relationTheory.reflexive_def]
QED

(* - Relations in graph ---------------------------------------------------- *)

Theorem wf_lrsE:
  lrs G = diag (E G) ⨾ lrs G ⨾ diag (E G)
Proof
  tac [lrs, po_loc] [wf_poE]
QED

Theorem wf_lwsE:
  lws G = diag (E G) ⨾ lws G ⨾ diag (E G)
Proof
  tac [lws, po_loc] [wf_poE]
QED

Theorem wf_obsE:
  WellFormed G ==> obs G = diag (E G) ⨾ obs G ⨾ diag (E G)
Proof
  tac [obs] [wf_rfeE, wf_coeE, wf_freE]
QED

Theorem wf_dobE:
  WellFormed G ==> dob G = diag (E G) ⨾ dob G ⨾ diag (E G)
Proof
  tac [dob] [wf_addrE, wf_dataE, wf_ctrlE, wf_poE, wf_lrsE]
QED

Theorem wf_aobE:
  WellFormed G ==> aob G = diag (E G) ⨾ aob G ⨾ diag (E G)
Proof
  tac [aob] [wf_rmwE, wf_lrsE]
QED

Theorem wf_bobE:
  WellFormed G ==> bob G = diag (E G) ⨾ bob G ⨾ diag (E G)
Proof
  tac [bob] [wf_poE]
QED

Theorem wf_lobE:
  WellFormed G ==> lob G = diag (E G) ⨾ lob G ⨾ diag (E G)
Proof
  REVERSE (rw [relationTheory.EqIsBothRSUBSET])
  >- xrw []
  \\ simp [lob]
  \\ rewrite inclusion_ct_seq_eqv_r
  \\ rewrite inclusion_ct_seq_eqv_l
  \\ match_mp_tac inclusion_t_t
  \\ tac [] [wf_dobE, wf_aobE, wf_bobE, wf_lwsE, wf_siE]
QED

(* - domains and co-domains ------------------------------------------------ *)

Theorem wf_lrsD:
  lrs G = diag (W G) ⨾ lrs G ⨾ diag (R G)
Proof
  tac [lrs] []
QED

Theorem wf_lwsD:
  lws G = diag (RW G) ⨾ lws G ⨾ diag (W G)
Proof
  tac [lws, po_loc, po, ext_sb] []
QED

Theorem wf_obsD:
  WellFormed G ==> obs G = diag (RW G) ⨾ obs G ⨾ diag (RW G)
Proof
  tac [obs] [wf_rfeD, wf_freD, wf_coeD]
QED

Theorem wf_dobD:
  WellFormed G ==> dob G = dob G ⨾ diag (RW G)
Proof
  wf_tac [wf_addrD_def, wf_dataD_def] []
  \\ tac [dob] [wf_lrsD]
QED

Theorem wf_aobD:
  WellFormed G ==> aob G = aob G ⨾ diag (RW G)
Proof
  wf_tac [wf_rmwD_def] []
  \\ tac [aob] []
QED

(* - Inclusions in program order ------------------------------------------- *)

Theorem lws_in_po:
  lws G RSUBSET po G
Proof
  xsimp [lws, po_loc]
QED

Theorem lrs_in_po:
  lrs G RSUBSET po G
Proof
  xsimp [lrs, po_loc]
QED

Theorem dob_in_po:
  WellFormed G ==> dob G RSUBSET po G
Proof
  wf_tac [addr_in_po_def, data_in_po_def, ctrl_in_po_def] [po_trans]
  \\ xfs [dob, lrs, po_loc, relationTheory.transitive_def]
  \\ rw []
  \\ simp []
  \\ metis_tac []
QED

Theorem aob_in_po:
  WellFormed G ==> aob G RSUBSET po G
Proof
  wf_tac [] [rmw_in_po, lrs_in_po]
  \\ xfs [aob]
  \\ rw []
  \\ simp []
QED

Theorem bob_in_po:
  WellFormed G ==> bob G RSUBSET po G
Proof
  wf_tac [] [amo_in_po, po_trans]
  \\ xfs [bob, relationTheory.transitive_def]
  \\ rw []
  \\ metis_tac []
QED

Theorem lob_in_po:
  WellFormed G ==> lob G RSUBSET po G
Proof
  wf_tac [] [dob_in_po, aob_in_po, bob_in_po, po_trans, po_si, lws_in_po]
  \\ simp [lob]
  \\ match_mp_tac tc_rsubset
  \\ xfs []
  \\ rw []
  \\ simp []
  \\ metis_tac []
QED

(* - Properties of consistent executions ----------------------------------- *)

Theorem wf_ecol:
  WellFormed G ==> eco G RSUBSET same_loc G
Proof
  wf_tac [wf_rfl_def, wf_col_def] [wf_frl, same_loc_trans]
  \\ xfs [eco, rc_runion, relationTheory.transitive_def]
  \\ rw []
  \\ simp []
  \\ metis_tac []
QED

Theorem InternalConsistent_sc_per_loc:
  WellFormed G /\ internal G ==> sc_per_loc G
Proof
  strip_tac
  \\ fs [internal, ca, relationTheory.RUNION_ASSOC, acyclic]
  \\ `irreflexive (po_loc G ⨾ eco G)`
  by (
    match_mp_tac relationTheory.irreflexive_RSUBSET
    \\ qexists_tac `TC (po_loc G RUNION fr G RUNION G.co RUNION G.rf)`
    \\ simp [eco_alt3]
    \\ qspec_then `(po_loc G RUNION fr G RUNION G.co RUNION G.rf) ⨾
                   TC (po_loc G RUNION fr G RUNION G.co RUNION G.rf)`
          match_mp_tac rsubset_trans
    \\ REVERSE strip_tac
    >- simp [seq_tc]
    \\ match_mp_tac inclusion_seq_mon
    \\ strip_tac
    >- xsimp []
    \\ match_mp_tac inclusion_t_t
    \\ xrw []
    \\ simp []
  )
  \\ qpat_x_assum `irreflexive (TC (r1 RUNION r2))` kall_tac
  \\ xrw [sc_per_loc, relationTheory.irreflexive_def]
  \\ spose_not_then strip_assume_tac
  \\ fs [po_loc, relationTheory.irreflexive_def]
  \\ qpat_x_assum `!x. p` mp_tac
  \\ xsimp []
  \\ qmatch_assum_rename_tac `po G x y`
  \\ qexistsl_tac [`x`, `y`]
  \\ simp []
  \\ imp_res_tac wf_ecol
  \\ xfs []
  \\ metis_tac [same_loc_sym, relationTheory.symmetric_def]
QED

Theorem obs_in_eco:
  obs G RSUBSET eco G
Proof
  MAP_EVERY assume_tac [rfe_in_eco, fre_in_eco, coe_in_eco]
  \\ xfs [obs]
  \\ metis_tac []
QED

Theorem in_po_obs_po:
  eco G RSUBSET RC (po G) ⨾ RC (obs G) ⨾ RC (obs G) ⨾ RC (po G)
Proof
  rw [eco_alt, cr_union_r, seq_runion_l]
  \\ simp [coi_union_coe, fri_union_fre, rfi_union_rfe]
  \\ MAP_EVERY assume_tac [coi_in_po, fri_in_po, rfi_in_po]
  \\ rw [runion_rsubset]
  \\ xfs [obs, rc_runion]
  \\ metis_tac []
QED

Theorem coi_lws:
  WellFormed G /\ sc_per_loc G ==> coi G = diag (W G) ⨾ lws G
Proof
  wf_tac [wf_coD_def, wf_col_def, wf_co_total_def, is_total] []
  \\ rw [coi, lws, po_loc]
  \\ first_x_assum SUBST1_TAC
  \\ rw [relationTheory.EqIsBothRSUBSET]
  \\ xfs []
  \\ rw []
  \\ qmatch_assum_rename_tac `same_loc G x y`
  \\ `x <> y` by metis_tac [po_irr, relationTheory.irreflexive_def]
  \\ rule_assum_tac (ONCE_REWRITE_RULE [wf_poE])
  \\ xfs []
  \\ first_x_assum (qspecl_then [`x`, `y`] assume_tac)
  \\ rfs [same_loc, sc_per_loc, relationTheory.irreflexive_def]
  \\ xfs [eco, rc_runion]
  \\ metis_tac []
QED

Theorem fri_lws:
  WellFormed G /\ complete G /\ sc_per_loc G ==> fri G = diag (R G) ⨾ lws G
Proof
  wf_tac [wf_col_def, wf_co_total_def, is_total, wf_rfD_def, wf_rfE_def,
          wf_rfl_def] [wf_frD, wf_frl]
  \\ rw [fri, lws, po_loc]
  \\ first_x_assum SUBST1_TAC
  \\ rw [relationTheory.EqIsBothRSUBSET]
  \\ xfs []
  \\ xrw [fr]
  \\ rule_assum_tac (ONCE_REWRITE_RULE [wf_poE])
  \\ xfs []
  \\ qmatch_assum_rename_tac `same_loc G x y`
  \\ `?w. G.rf w x`
  by xfs [complete, pred_setTheory.SUBSET_applied, pred_setTheory.SPECIFICATION]
  \\ `w <> y`
  by (
    xfs [sc_per_loc, relationTheory.irreflexive_def, eco, rc_runion]
    \\ metis_tac []
  )
  \\ rfs [same_loc, sc_per_loc, relationTheory.irreflexive_def]
  \\ xfs [eco, rc_runion]
  \\ metis_tac []
QED

Theorem lws_expand:
  WellFormed G /\ complete G /\ sc_per_loc G ==>
  diag (RW G) ⨾ lws G = coi G RUNION fri G
Proof
  strip_tac
  \\ MAP_EVERY imp_res_tac [fri_lws, coi_lws]
  \\ xfs []
  \\ metis_tac []
QED

Theorem bob_fri:
  WellFormed G ==> bob G ⨾ fri G RSUBSET bob G ⨾ RC (bob G)
Proof
  strip_tac
  \\ CONV_TAC (LAND_CONV (REWRITE_CONV [bob]))
  \\ simp [seq_runion_l, seq_assoc]
  \\ `diag (W G) ⨾ fri G RSUBSET REMPTY /\ diag (L G) ⨾ fri G RSUBSET REMPTY`
  by (
    strip_tac
    \\ rw [Once wf_friD]
    \\ xsimp []
    \\ metis_tac [label_distinct]
  )
  \\ qspec_then `po G ⨾ REMPTY` match_mp_tac runion_rsubset_r
  \\ strip_tac
  >- xfs []
  \\ simp [seq_empty_r, runion_empty_r]
  \\ qspec_then `diag (W G) ⨾ po G ⨾ diag (F_dmbst G) ⨾ po G ⨾ REMPTY`
       match_mp_tac runion_rsubset_r
  \\ strip_tac
  >- xfs []
  \\ simp [seq_empty_r, runion_empty_r]
  \\ MAP_EVERY assume_tac [fri_in_po, po_po]
  \\ rw [runion_rsubset]
  \\ xfs [bob, rc_runion]
  \\ metis_tac []
QED

Theorem co_in_ob:
  WellFormed G /\ sc_per_loc G ==> G.co RSUBSET obs G RUNION lob G
Proof
  strip_tac
  \\ simp [coi_union_coe, obs, lob, coi_lws]
  \\ xrw []
  \\ simp []
  \\ rename1 `coe G x y`
  \\ `si G y y`
  by (
    rule_assum_tac (ONCE_REWRITE_RULE [wf_lwsE])
    \\ xfs [lws, si]
    \\ metis_tac [relationTheory.reflexive_def, ext_si_refl]
  )
  \\ disj2_tac
  \\ match_mp_tac relationTheory.TC_SUBSET
  \\ xsimp []
  \\ metis_tac []
QED

Theorem fr_in_ob:
  WellFormed G /\ complete G /\ sc_per_loc G ==> fr G RSUBSET obs G RUNION lob G
Proof
  strip_tac
  \\ simp [fri_union_fre, obs, lob, fri_lws]
  \\ xrw []
  \\ simp []
  \\ rename1 `coe G x y`
  \\ `si G y y`
  by (
    rule_assum_tac (ONCE_REWRITE_RULE [wf_lwsE])
    \\ xfs [lws, si]
    \\ metis_tac [relationTheory.reflexive_def, ext_si_refl]
  )
  \\ disj2_tac
  \\ match_mp_tac relationTheory.TC_SUBSET
  \\ xsimp []
  \\ metis_tac []
QED

Theorem po_loc_ww:
  WellFormed G /\ sc_per_loc G /\ po G x y /\ W G x /\ W G y /\
  same_loc G x y ==> G.co x y
Proof
  wf_tac [wf_co_total_def, is_total] []
  \\ `x <> y` by metis_tac [po_irr, relationTheory.irreflexive_def]
  \\ rule_assum_tac (ONCE_REWRITE_RULE [wf_poE])
  \\ xfs [sc_per_loc, same_loc, eco, relationTheory.irreflexive_def, rc_runion]
  \\ metis_tac []
QED

Theorem im0_in_co:
  WellFormed G /\ sc_per_loc G ==> im0 G RSUBSET G.co
Proof
  wf_tac [wf_co_total_def, is_total] [init_w, no_co_to_init]
  \\ xrw [im0]
  \\ xfs [sc_per_loc, same_loc, eco, relationTheory.irreflexive_def, rc_runion]
  \\ metis_tac []
QED

Theorem no_obs_to_init:
  WellFormed G /\ sc_per_loc G ==> obs G RSUBSET (K T) RCROSS (COMPL is_init)
Proof
  strip_tac
  \\ MAP_EVERY imp_res_tac [no_rf_to_init, no_co_to_init, no_fr_to_init]
  \\ xfs [obs, rfe, fre, coe]
  \\ metis_tac []
QED

Theorem no_lob_to_init:
  WellFormed G ==> lob G RSUBSET (K T) RCROSS (COMPL is_init)
Proof
  strip_tac
  \\ imp_res_tac lob_in_po
  \\ xfs [Once no_po_to_init]
  \\ metis_tac []
QED

Theorem si_init:
  si G RSUBSET
  is_init RCROSS is_init RUNION ((COMPL is_init) RCROSS (COMPL is_init))
Proof
  xrw [si, ext_si]
  \\ rename1 `is_init x /\ is_init y`
  \\ Cases_on `x`
  \\ Cases_on `y`
  \\ fs [is_init]
QED

(* - Equivalence to external completion model ------------------------------ *)

Theorem L_si:
  WellFormed G ==> diag (L G) ⨾ si G = si G ⨾ diag (L G)
Proof
  wf_tac [wf_siD_def] []
  \\ xrw [relationTheory.EqIsBothRSUBSET]
  \\ qpat_x_assum `!x y. p` imp_res_tac
  \\ qmatch_assum_rename_tac `si G x y`
  \\ Cases_on `G.lab x`
  \\ Cases_on `G.lab y`
  \\ fs [si_matching_label, is_w, is_w_rel]
QED

Theorem A_si:
  WellFormed G ==> diag (A G) ⨾ si G = si G ⨾ diag (A G)
Proof
  wf_tac [wf_siD_def] []
  \\ xrw [relationTheory.EqIsBothRSUBSET]
  \\ qpat_x_assum `!x y. p` imp_res_tac
  \\ qmatch_assum_rename_tac `si G x y`
  \\ Cases_on `G.lab x`
  \\ Cases_on `G.lab y`
  \\ fs [si_matching_label, is_r, is_r_acqSC]
QED

Theorem Q_si:
  WellFormed G ==> diag (Q G) ⨾ si G = si G ⨾ diag (Q G)
Proof
  wf_tac [wf_siD_def] []
  \\ xrw [relationTheory.EqIsBothRSUBSET]
  \\ qpat_x_assum `!x y. p` imp_res_tac
  \\ qmatch_assum_rename_tac `si G x y`
  \\ Cases_on `G.lab x`
  \\ Cases_on `G.lab y`
  \\ fs [si_matching_label, is_r, is_r_acqPC]
QED

Theorem bob_si:
  WellFormed G ==> bob G ⨾ si G = bob G
Proof
  rw [bob, seq_runion_l, seq_assoc, L_si, A_si, W_si, po_si]
  \\ metis_tac [seq_assoc, L_si, A_si, W_si, po_si]
QED

Theorem scaob_scaob:
  WellFormed G ==> scaob G ⨾ scaob G = REMPTY
Proof
  wf_tac [wf_rff_def, functional] []
  \\ xsimp [scaob, ER, IR, rfe, rfi]
  \\ metis_tac []
QED

Theorem erln_refl:
  E G x ==> erln G x x
Proof
  xsimp [erln]
QED

Theorem erln_scaob:
  WellFormed G ==> erln G ⨾ scaob G = scaob G
Proof
  wf_tac [wf_rfD_def, wf_rff_def, functional] []
  \\ simp [relationTheory.EqIsBothRSUBSET, erln, scaob, rfisw]
  \\ xrw [Once wf_siE, IR, ER, rfi, rfe]
  \\ xfs []
  \\ metis_tac [si_trans, label_distinct, relationTheory.transitive_def]
QED

Theorem scaob_erln:
  WellFormed G ==> scaob G ⨾ erln G RSUBSET scaob G
Proof
  wf_tac [wf_rfD_def, wf_rff_def, functional] []
  \\ simp [relationTheory.EqIsBothRSUBSET, erln, scaob, rfisw]
  \\ xrw [Once wf_siE, IR, ER, rfi, rfe]
  \\ xfs []
  \\ metis_tac [si_trans, label_distinct, relationTheory.transitive_def]
QED

Triviality coh_helper:
  WellFormed G /\ sc_per_loc G /\ G.rf z y /\ po G z x /\ po G x y /\
  W G x /\ same_loc G x y ==> F
Proof
  wf_tac [wf_rfl_def, wf_rfD_def] []
  \\ qpat_x_assum `G.rf z y` mp_tac
  \\ first_x_assum SUBST1_TAC
  \\ strip_tac
  \\ `same_loc G z y` by xfs []
  \\ `same_loc G z x`
  by metis_tac [same_loc_trans, same_loc_sym, relationTheory.transitive_def,
                relationTheory.symmetric_def]
  \\ mp_tac (Q.INST [`x` |-> `z`, `y` |-> `x`] po_loc_ww)
  \\ xfs []
  \\ strip_tac
  \\ qpat_x_assum `sc_per_loc G` mp_tac
  \\ xsimp [sc_per_loc, relationTheory.irreflexive_def]
  \\ qexistsl_tac [`x`, `y`]
  \\ assume_tac fr_in_eco
  \\ xfs [fr]
  \\ metis_tac []
QED

Theorem lrs_erln:
  WellFormed G /\ sc_per_loc G ==>
  lrs G ⨾ erln G RSUBSET
  si G ⨾ lrs G RUNION TC (obs G ⨾ si G) RUNION is_init RCROSS COMPL is_init
Proof
  wf_tac [wf_rfl_def, wf_rfD_def, wf_rfE_def, wf_co_total_def, is_total,
          pred_setTheory.SPECIFICATION] []
  \\ simp [lrs, erln, rfisw, po_loc, intervening_write, ER, rfe, rfi]
  \\ first_assum SUBST1_TAC
  \\ last_x_assum SUBST1_TAC
  \\ CONV_TAC (PATH_CONV "lrlrrlrl" (ONCE_REWRITE_CONV [wf_poE]))
  \\ xrw []
  >- metis_tac [label_distinct]
  >- (
    qmatch_assum_rename_tac `~po G x0 y`
    \\ qmatch_assum_rename_tac `po G x z0`
    \\ qmatch_assum_rename_tac `G.rf x1 z0`
    \\ `same_loc G x1 z0` by xfs []
    \\ `x <> x1` by metis_tac []
    \\ `loc G x1 = loc G x` by fs [same_loc]
    \\ qpat_x_assum `!a b. p` (qspecl_then [`x`, `x1`] assume_tac)
    \\ REVERSE (rfs [])
    >- (
      spose_not_then kall_tac
      \\ qpat_x_assum `sc_per_loc G` mp_tac
      \\ xsimp [sc_per_loc, relationTheory.irreflexive_def]
      \\ qexistsl_tac [`x`, `z0`]
      \\ assume_tac fr_in_eco
      \\ xfs [fr]
      \\ metis_tac []
    )
    \\ Cases_on `is_init x`
    >- (
      disj2_tac
      \\ imp_res_tac no_rf_to_init
      \\ xfs []
      \\ metis_tac []
    )
    \\ disj1_tac
    \\ disj2_tac
    \\ match_mp_tac (CONJUNCT2 (SPEC_ALL relationTheory.TC_RULES))
    \\ qexists_tac `x1`
    \\ strip_tac
    \\ match_mp_tac (CONJUNCT1 (SPEC_ALL relationTheory.TC_RULES))
    >- (
      xsimp []
      \\ qexists_tac `x1`
      \\ xsimp [si_refl, obs]
      \\ disj2_tac
      \\ xsimp [coe]
      \\ strip_tac
      \\ assume_tac (Q.INST [`y` |-> `z0`, `z` |-> `x1`] po_semi_total_l)
      \\ rfs []
      >- (
        qpat_x_assum `sc_per_loc G` mp_tac
        \\ assume_tac rf_in_eco
        \\ xfs [sc_per_loc, relationTheory.irreflexive_def]
        \\ metis_tac []
      )
      \\ `si_matching_label (G.lab z0) (G.lab x1)` by metis_tac [wf_siD_def]
      \\ rfs [si_matching_label]
      \\ Cases_on `G.lab z0`
      \\ Cases_on `G.lab x1`
      \\ gs [is_r, is_w]
    )
    \\ xsimp [obs, rfe, fre, fr, coe]
    \\ metis_tac []
  )
  >- (
    qmatch_assum_rename_tac `po G z2 y`
    \\ qmatch_assum_rename_tac `si G z1 z2`
    \\ qmatch_assum_rename_tac `G.rf z1 z0`
    \\ `same_loc G z1 z0` by xfs []
    \\ assume_tac
         (Q.INST [`y` |-> `x`, `x` |-> `z0`, `z` |-> `z1`] po_semi_total_r)
    \\ rfs []
    >- metis_tac [same_loc]
    >- metis_tac [coh_helper]
    >- (
      `z1 = x`
      by (
        Cases_on `z1`
        \\ Cases_on `x`
        \\ Cases_on `G.lab z0`
        \\ gs [is_init, same_loc, wf_init_lab_def, loc, is_w, is_r]
      )
      \\ ntac 2 disj1_tac
      \\ qexists_tac `z2`
      \\ fs []
      \\ strip_tac
      >- xfs []
      \\ metis_tac [coh_helper]
    )
    \\ ntac 2 disj1_tac
    \\ qexists_tac `z2`
    \\ simp []
    \\ assume_tac si_si
    \\ xfs []
    \\ metis_tac [coh_helper]
  )
  \\ metis_tac [si_refl]
QED

Theorem dob_erln:
  WellFormed G /\ sc_per_loc G ==>
  dob G ⨾ erln G RSUBSET dob G RUNION dob G ⨾ TC (obs G ⨾ si G)
Proof
  wf_tac [addr_in_po_def, data_in_po_def]
     [erln_in_si, po_si, no_po_to_init, lrs_erln, R_si, W_si, addr_si,
      data_si, ctrl_si]
  \\ CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [dob]))
  \\ CONV_TAC (RAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [dob])))
  \\ simp [seq_runion_l, seq_assoc]
  \\ REVERSE (rw [runion_rsubset])
  \\ simp [GSYM relationTheory.RUNION_ASSOC]
  >- (
    qspec_then
       `G.data ⨾ (si G ⨾ lrs G RUNION TC (obs G ⨾ si G) RUNION
                  is_init RCROSS COMPL is_init)`
       match_mp_tac rsubset_trans
    \\ strip_tac
    >- metis_tac [inclusion_seq_mon, rsubset_refl]
    \\ xfs [dob]
    \\ metis_tac []
  )
  >- (
    qspec_then
      `G.addr ⨾ (si G ⨾ lrs G RUNION TC (obs G ⨾ si G) RUNION
                 is_init RCROSS COMPL is_init)`
       match_mp_tac rsubset_trans
    \\ strip_tac
    >- metis_tac [inclusion_seq_mon, rsubset_refl]
    \\ xfs [dob]
    \\ metis_tac []
  )
  \\ xfs []
  \\ metis_tac []
QED

Theorem rmw_in_lws:
  WellFormed G ==> rmw G RSUBSET lws G
Proof
  wf_tac [wf_rmwD_def] [rmw_in_po_loc]
  \\ xfs [lws, po_loc]
  \\ metis_tac []
QED

Theorem aob_erln:
  WellFormed G /\ sc_per_loc G ==>
  aob G ⨾ erln G RSUBSET
  TC (obs G ⨾ si G RUNION lob G) RUNION
  diag (W_ex G) ⨾ si G ⨾ aob G RUNION
  is_init RCROSS COMPL is_init
Proof
  wf_tac [] [erln_in_si, rmw_in_lws, lrs_erln, A_si, Q_si, W_ex_si]
  \\ simp [aob, GSYM W_ex, seq_runion_l, seq_assoc]
  \\ rw [runion_rsubset, GSYM relationTheory.RUNION_ASSOC]
  >- (
    match_mp_tac rsubset_runion
    \\ disj1_tac
    \\ match_mp_tac rsubset_tc
    \\ match_mp_tac rsubset_runion
    \\ disj2_tac
    \\ simp [lob]
    \\ match_mp_tac rsubset_tc
    \\ xfs []
    \\ metis_tac []
  )
  \\ qspec_then `diag (W_ex G) ⨾ lrs G ⨾ erln G ⨾ diag (A G UNION Q G)`
       match_mp_tac rsubset_trans
  \\ strip_tac
  >- (
    ntac 2 (match_mp_tac inclusion_seq_mon \\ simp [])
    \\ xfs []
    \\ metis_tac []
  )
  \\ qspec_then
       `diag (W_ex G) ⨾
        (si G ⨾ lrs G RUNION TC (obs G ⨾ si G) RUNION
         is_init RCROSS COMPL is_init) ⨾ diag (A G UNION Q G)`
       match_mp_tac rsubset_trans
  \\ strip_tac
  >- (
    xfs []
    \\ metis_tac []
  )
  \\ simp [seq_runion_l, seq_runion_r, seq_assoc]
  \\ rw [runion_rsubset]
  >- (
    xfs []
    \\ metis_tac []
  )
  >- (
    match_mp_tac rsubset_runion
    \\ disj1_tac
    \\ match_mp_tac inclusion_seq_eqv
    \\ match_mp_tac inclusion_t_t
    \\ xsimp []
  )
  >- (
    xfs []
    \\ metis_tac []
  )
QED

Theorem lrs_si_aob:
  WellFormed G ==> lrs G ⨾ si G ⨾ aob G RSUBSET lob G
Proof
  wf_tac [wf_rmwD_def] [si_rmw, rmw_in_po_loc, W_ex_si, W_ex_in_W]
  \\ qspec_then `lws G ⨾ si G` match_mp_tac rsubset_trans
  \\ REVERSE strip_tac
  >- (
    simp [lob]
    \\ match_mp_tac rsubset_tc
    \\ xsimp [lob]
  )
  \\ simp [Once lrs, lws, aob, po_loc, intervening_write, GSYM W_ex]
  \\ simp [seq_runion_r, seq_assoc]
  \\ qpat_assum `rmw G = xx` SUBST1_TAC
  \\ rw [runion_rsubset]
  >- (
    qspec_then
       `diag (W G) ⨾
        po G RINTER same_loc G RMINUS
        (po G RINTER same_loc G ⨾ diag (W G) ⨾ po G RINTER same_loc G) ⨾
        diag (R G) ⨾ (diag (R G) ⨾ po G RINTER same_loc G ⨾ diag (W G)) ⨾
        si G`
       match_mp_tac rsubset_trans
    \\ strip_tac
    >- (
      ntac 5 (match_mp_tac inclusion_seq_mon \\ simp [])
      \\ metis_tac [seq_rsubset_l, rsubset_refl]
    )
    \\ xrw []
    \\ qmatch_assum_rename_tac `si G z y`
    \\ qexists_tac `z`
    \\ simp []
    \\ metis_tac [po_trans, same_loc_trans, relationTheory.transitive_def]
  )
  \\ xfs []
  \\ metis_tac [label_distinct]
QED

Theorem dob_si_aob:
  WellFormed G ==> dob G ⨾ si G ⨾ aob G RSUBSET lob G
Proof
  wf_tac [] [lrs_si_aob, W_si, R_si, ctrl_si, addr_si, data_si, po_si]
  \\ `aob G RSUBSET lob G`
  by (
    simp [lob]
    \\ match_mp_tac rsubset_tc
    \\ xsimp []
  )
  \\ simp [dob, seq_runion_l, seq_assoc]
  \\ qspec_then `G.addr ⨾ lob G RUNION G.data ⨾ lob G`
       match_mp_tac runion_rsubset_r
  \\ strip_tac
  >- (xfs [] \\ metis_tac [])
  \\ simp [GSYM seq_assoc]
  \\ simp [seq_assoc]
  \\ `G.ctrl ⨾ diag (W G) ⨾ si G ⨾ aob G = G.ctrl ⨾ diag (W G) ⨾ aob G`
  by metis_tac [seq_assoc]
  \\ pop_assum SUBST1_TAC
  \\ `G.addr ⨾ po G ⨾ diag (W G) ⨾ si G ⨾ aob G =
      G.addr ⨾ po G ⨾ diag (W G) ⨾ aob G`
  by metis_tac [seq_assoc]
  \\ pop_assum SUBST1_TAC
  \\ `G.ctrl ⨾ diag (F_isb G) ⨾ po G ⨾ diag (R G) ⨾ si G ⨾ aob G =
      G.ctrl ⨾ diag (F_isb G) ⨾ po G ⨾ diag (R G) ⨾ aob G`
  by metis_tac [seq_assoc]
  \\ pop_assum SUBST1_TAC
  \\ `G.addr ⨾ po G ⨾ diag (F_isb G) ⨾ po G ⨾ diag (R G) ⨾ si G ⨾ aob G =
      G.addr ⨾ po G ⨾ diag (F_isb G) ⨾ po G ⨾ diag (R G) ⨾ aob G`
  by metis_tac [seq_assoc]
  \\ pop_assum SUBST1_TAC
  \\ qspec_then
       `G.addr ⨾ lob G RUNION G.data ⨾ lob G RUNION
        G.ctrl ⨾ diag (W G) ⨾ lob G RUNION
        (G.ctrl ⨾ diag (F_isb G) ⨾ po G ⨾ diag (R G) ⨾ lob G RUNION
         G.addr ⨾ po G ⨾ diag (F_isb G) ⨾ po G ⨾ diag (R G) ⨾ lob G) RUNION
        G.addr ⨾ po G ⨾ diag (W G) ⨾ lob G RUNION
        (G.addr ⨾ lob G RUNION G.data ⨾ lob G)`
       match_mp_tac rsubset_trans
  \\ strip_tac
  >- (xfs [] \\ metis_tac [])
  \\ simp [GSYM seq_runion_l, GSYM seq_assoc]
  \\ match_mp_tac inclusion_seq_trans
  \\ simp []
  \\ REVERSE strip_tac
  >- simp [lob]
  \\ qspec_then `dob G` match_mp_tac rsubset_trans
  \\ strip_tac
  >- (
    xrw [runion_rsubset, dob]
    \\ metis_tac []
  )
  \\ simp [lob]
  \\ match_mp_tac rsubset_tc
  \\ xsimp []
QED

Theorem aob_si_aob:
  WellFormed G ==> aob G ⨾ si G ⨾ aob G RSUBSET lob G RUNION si G ⨾ TC (aob G)
Proof
  strip_tac
  \\ map_every imp_res_tac [lrs_si_aob, GSYM si_rmw]
  \\ simp [Once aob, GSYM W_ex, seq_runion_l, seq_assoc]
  \\ qspec_then `lob G` match_mp_tac runion_rsubset_r
  \\ strip_tac
  >- (xfs [] \\ metis_tac [])
  \\ REVERSE (rw [runion_rsubset, GSYM seq_assoc])
  >- xsimp []
  \\ `rmw G RSUBSET RTC (aob G)`
  by (
    match_mp_tac rsubset_rtc
    \\ xsimp [aob]
  )
  \\ qspec_then `si G ⨾ RTC (aob G)` match_mp_tac seq_rsubset_l
  \\ strip_tac
  >- (xfs [] \\ metis_tac [])
  \\ simp [seq_assoc]
  \\ match_mp_tac rsubset_runion
  \\ disj2_tac
  \\ match_mp_tac inclusion_seq_mon
  \\ simp [ct_end]
QED

Theorem aob_Wex:
  WellFormed G ==> aob G ⨾ diag (W_ex G) RSUBSET lws G
Proof
  strip_tac
  \\ map_every imp_res_tac [rmw_in_lws, W_ex_in_W]
  \\ simp [aob, GSYM W_ex, seq_runion_l]
  \\ match_mp_tac runion_rsubset_l
  \\ qexists_tac `lws G ⨾ diag (W_ex G)`
  \\ strip_tac
  >- metis_tac [inclusion_seq_mon, rsubset_refl]
  \\ xfs [runion_rsubset]
  \\ metis_tac [label_distinct]
QED

Theorem lob_si_aob:
  WellFormed G ==>
  lob G ⨾ diag (W_ex G) ⨾ si G ⨾ aob G RSUBSET TC (obs G ⨾ si G RUNION lob G)
Proof
  wf_tac [] [aob_Wex, dob_si_aob, bob_si, inclusion_seq_eqv_l, si_si]
  \\ simp [Once lob, Once ct_end]
  \\ simp [Once (GSYM rt_ct), seq_assoc]
  \\ match_mp_tac inclusion_seq_mon
  \\ strip_tac
  >- metis_tac [inclusion_rt_rt, rsubset_runion, lob, rsubset_tc, rsubset_refl]
  \\ simp [seq_runion_l, seq_assoc]
  \\ qspec_then `lws G ⨾ si G ⨾ aob G RUNION lob G RUNION bob G ⨾ aob G`
       match_mp_tac rsubset_trans
  \\ strip_tac
  >- (xfs [] \\ metis_tac [])
  \\ `bob G RSUBSET lob G /\ lws G ⨾ si G RSUBSET lob G`
  by (
    rw [lob]
    \\ match_mp_tac rsubset_tc
    \\ xsimp []
  )
  \\ `aob G RSUBSET TC (lob G)`
  by (
    simp [lob]
    \\ match_mp_tac rsubset_tc
    \\ xsimp []
  )
  \\ rw [runion_rsubset]
  >- (
    qspec_then `TC (lob G)` match_mp_tac rsubset_trans
    \\ strip_tac
    >- (
      simp [GSYM seq_assoc]
      \\ match_mp_tac inclusion_seq_trans
      \\ simp [relationTheory.TC_TRANSITIVE, rsubset_tc]
    )
    \\ match_mp_tac inclusion_t_t
    \\ xsimp []
  )
  >- xsimp [rsubset_tc]
  \\ qspec_then `TC (lob G)` match_mp_tac rsubset_trans
  \\ strip_tac
  >- (
    match_mp_tac inclusion_seq_trans
    \\ simp [relationTheory.TC_TRANSITIVE]
    \\ simp [rsubset_tc]
  )
  \\ match_mp_tac inclusion_t_t
  \\ xsimp []
QED

Theorem ob_si_aob:
  WellFormed G ==>
  TC (obs G ⨾ si G RUNION lob G) ⨾ diag (W_ex G) ⨾ si G ⨾ aob G RSUBSET
  TC (obs G ⨾ si G RUNION lob G)
Proof
  wf_tac [] [lob_si_aob]
  \\ simp [Once ct_end, seq_assoc]
  \\ simp [Once (GSYM rt_ct)]
  \\ match_mp_tac inclusion_seq_mon
  \\ simp [seq_runion_l, seq_assoc]
  \\ simp [runion_rsubset]
  \\ qspec_then `obs G ⨾ si G ⨾ aob G` match_mp_tac rsubset_trans
  \\ strip_tac
  >- (
    map_every assume_tac [GEN_ALL inclusion_seq_eqv_l, si_si]
    \\ xfs []
    \\ metis_tac []
  )
  \\ `aob G RSUBSET RTC (lob G)`
  by (
    simp [lob, RTC_TC_RTC]
    \\ match_mp_tac rsubset_rtc
    \\ xsimp []
  )
  \\ qspec_then `obs G ⨾ si G ⨾ RTC (lob G)` match_mp_tac rsubset_trans
  \\ strip_tac
  >- (xfs [] \\ metis_tac [])
  \\ simp [ct_begin, GSYM seq_assoc]
  \\ match_mp_tac inclusion_seq_mon
  \\ strip_tac
  >- xsimp []
  \\ match_mp_tac inclusion_rt_rt
  \\ xsimp []
QED

Theorem lob_erln:
  WellFormed G /\ sc_per_loc G ==>
  lob G ⨾ erln G RSUBSET
  TC (obs G ⨾ si G RUNION lob G) RUNION diag (W_ex G) ⨾ si G ⨾ aob G RUNION
  is_init RCROSS COMPL is_init
Proof
  wf_tac [] [bob_si, dob_erln, aob_erln, lob_in_po, erln_in_si, si_si]
  \\ simp [Once lob, Once ct_end, seq_assoc]
  \\ `RTC (lws G ⨾ si G RUNION dob G RUNION aob G RUNION bob G) RSUBSET
      RC (lob G)`
  by simp [lob, relationTheory.TC_RC_EQNS]
  \\ qspec_then `RC (lob G)` match_mp_tac seq_rsubset_l
  \\ simp [seq_runion_l, seq_assoc]
  \\ `lws G ⨾ si G RSUBSET lob G /\ bob G RSUBSET lob G /\ dob G RSUBSET lob G`
  by (
    rw [lob]
    \\ match_mp_tac rsubset_tc
    \\ xsimp []
  )
  \\ qspec_then
       `RC (lob G) ⨾
        (lob G RUNION (lob G RUNION lob G ⨾ TC (obs G ⨾ si G)) RUNION
         aob G ⨾ erln G RUNION lob G)`
        match_mp_tac rsubset_trans
  \\ strip_tac
  >- (xfs [] \\ metis_tac [])
  \\ qspec_then
       `RC (lob G) ⨾
        (lob G RUNION (lob G RUNION lob G ⨾ TC (obs G ⨾ si G)) RUNION
         (TC (obs G ⨾ si G RUNION lob G) RUNION
          diag (W_ex G) ⨾ si G ⨾ aob G RUNION
          is_init RCROSS COMPL is_init) RUNION lob G)`
        match_mp_tac rsubset_trans
  \\ strip_tac
  >- (ntac 6 (pop_assum kall_tac) \\ xfs [] \\ metis_tac [])
  \\ simp [seq_runion_l, seq_runion_r]
  \\ `RC (lob G) ⨾ lob G RSUBSET lob G`
  by simp [lob, relationTheory.TC_RC_EQNS, rt_ct]
  \\ qspec_then
       `lob G RUNION
        (lob G RUNION lob G ⨾ TC (obs G ⨾ si G)) RUNION
        (RC (lob G) ⨾ TC (obs G ⨾ si G RUNION lob G) RUNION
         (RC (lob G) ⨾ diag (W_ex G) ⨾ si G ⨾ aob G RUNION
         RC (lob G) ⨾ is_init RCROSS COMPL is_init)) RUNION
        lob G`
        match_mp_tac rsubset_trans
  \\ strip_tac
  >- (xfs [] \\ metis_tac [])
  \\ rw [runion_rsubset]
  \\ TRY (
    ntac 2 (match_mp_tac rsubset_runion \\ disj1_tac)
    \\ match_mp_tac rsubset_tc
    \\ match_mp_tac rsubset_runion
    \\ disj2_tac
    \\ simp []
    \\ FAIL_TAC ""
  )
  >- (
    ntac 2 (match_mp_tac rsubset_runion \\ disj1_tac)
    \\ simp [Q.INST [`r` |-> `r1 RUNION r2`] ct_begin]
    \\ simp [seq_runion_l]
    \\ match_mp_tac rsubset_runion
    \\ disj2_tac
    \\ match_mp_tac inclusion_seq_mon
    \\ simp []
    \\ match_mp_tac tc_rsubset
    \\ simp [lob]
    \\ match_mp_tac rsubset_rtc
    \\ xsimp []
  )
  >- (
    ntac 2 (match_mp_tac rsubset_runion \\ disj1_tac)
    \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM rt_ct]))
    \\ match_mp_tac inclusion_seq_mon
    \\ simp [lob, relationTheory.TC_RC_EQNS]
    \\ match_mp_tac inclusion_rt_rt
    \\ match_mp_tac rsubset_runion
    \\ disj2_tac
    \\ simp [rsubset_tc]
  )
  >- (
    simp [rc_runion, seq_runion_l, diag_T_seq_l]
    \\ rw [runion_rsubset]
    >- xsimp []
    \\ metis_tac [lob_si_aob, rsubset_trans, rsubset_runion, rsubset_refl]
  )
  \\ qspec_then `RC (po G) ⨾ is_init RCROSS COMPL is_init`
       match_mp_tac rsubset_trans
  \\ strip_tac
  >- (xfs [rc_runion] \\ metis_tac [])
  \\ simp [Once no_po_to_init]
  \\ xsimp [rc_runion]
  \\ metis_tac []
QED

Theorem lrs_scaob:
  WellFormed G /\ sc_per_loc G ==>
  lrs G ⨾ scaob G RSUBSET TC (obs G ⨾ si G) RUNION is_init RCROSS COMPL is_init
Proof
  wf_tac [wf_rfD_def, wf_rfE_def, wf_rfl_def, wf_co_total_def, is_total,
          pred_setTheory.SPECIFICATION] []
  \\ simp [lrs, scaob, po_loc, intervening_write, ER, IR, rfe, rfi]
  \\ first_assum SUBST1_TAC
  \\ last_assum SUBST1_TAC
  \\ simp [Once wf_poE]
  \\ xrw []
  \\ qmatch_assum_rename_tac `po G x0 y`
  \\ qmatch_assum_rename_tac `~po G x1 z0`
  \\ `same_loc G x1 z0` by xfs []
  \\ `x <> x1` by metis_tac []
  \\ `G.co x1 x \/ G.co x x1` by metis_tac [same_loc]
  >- (
    spose_not_then (K (qpat_x_assum `sc_per_loc G` mp_tac))
    \\ xsimp [sc_per_loc, relationTheory.irreflexive_def]
    \\ qexistsl_tac [`x`, `z0`]
    \\ assume_tac fr_in_eco
    \\ xfs [fr]
    \\ metis_tac []
  )
  \\ Cases_on `is_init x`
  \\ simp []
  >- (
    disj2_tac
    \\ qpat_x_assum `po G x0 y` mp_tac
    \\ xsimp [Once no_po_to_init]
  )
  \\ simp [Once relationTheory.TC_CASES1]
  \\ disj2_tac
  \\ qexists_tac `x1`
  \\ strip_tac
  >- (
    xsimp []
    \\ qexists_tac `x1`
    \\ simp [si_refl]
    \\ xsimp [obs]
    \\ disj2_tac
    \\ xsimp [coe]
    \\ strip_tac
    \\ assume_tac (Q.INST [`y` |-> `x1`, `z` |-> `z0`] po_semi_total_l)
    \\ rfs []
    >- (
      qpat_x_assum `sc_per_loc G` mp_tac
      \\ assume_tac rf_in_eco
      \\ xfs [sc_per_loc, relationTheory.irreflexive_def]
      \\ metis_tac []
    )
    \\ `si_matching_label (G.lab x1) (G.lab z0)` by imp_res_tac wf_siD_def
    \\ rfs [si_matching_label, is_w, is_r]
    \\ Cases_on `G.lab x1`
    \\ Cases_on `G.lab z0`
    \\ gs []
  )
  \\ simp [Once relationTheory.TC_CASES2]
  \\ disj1_tac
  \\ xsimp [obs, rfe, fre, coe, fr]
  \\ metis_tac []
QED

Theorem dob_scaob:
  WellFormed G /\ sc_per_loc G ==>
  dob G ⨾ scaob G RSUBSET dob G RUNION dob G ⨾ TC (obs G ⨾ si G)
Proof
  wf_tac [addr_in_po_def, data_in_po_def]
    [W_si, R_si, addr_si, data_si, ctrl_si, lrs_scaob, po_si]
  \\ qpat_x_assum `G.addr RSUBSET po G`
       (assume_tac o ONCE_REWRITE_RULE [no_po_to_init])
  \\ qpat_x_assum `G.data RSUBSET po G`
       (assume_tac o ONCE_REWRITE_RULE [no_po_to_init])
  \\ simp [Ntimes dob 2, seq_runion_l, seq_assoc]
  \\ `scaob G RSUBSET si G` by xsimp [scaob]
  \\ qspec_then
       `G.addr RUNION G.data RUNION
        G.ctrl ⨾ diag (W G) RUNION
        (G.ctrl ⨾ diag (F_isb G) ⨾ po G ⨾ diag (R G) RUNION
         G.addr ⨾ po G ⨾ diag (F_isb G) ⨾ po G ⨾ diag (R G)) RUNION
        G.addr ⨾ po G ⨾ diag (W G) RUNION
        (G.addr ⨾ (TC (obs G ⨾ si G) RUNION is_init RCROSS COMPL is_init) RUNION
         G.data ⨾ (TC (obs G ⨾ si G) RUNION is_init RCROSS COMPL is_init))`
       match_mp_tac rsubset_trans
  \\ strip_tac
  >- (xfs [] \\ metis_tac [])
  \\ rw [seq_runion_r, runion_rsubset]
  \\ xfs [dob]
  \\ metis_tac []
QED

Theorem aob_scaob:
  WellFormed G /\ sc_per_loc G ==>
  aob G ⨾ scaob G RSUBSET diag (W_ex G) ⨾ TC (obs G ⨾ si G)
Proof
  wf_tac [wf_rmwD_def] [wf_rfeD, lrs_scaob, rmw_in_po]
  \\ simp [aob, seq_runion_l, seq_assoc, GSYM W_ex]
  \\ rw [runion_rsubset]
  >- (
    simp [scaob, ER, IR, fre]
    \\ ntac 2 (first_x_assum SUBST1_TAC)
    \\ xrw []
    \\ metis_tac [label_distinct]
  )
  \\ qspecl_then [`scaob G`, `A G UNION Q G`] assume_tac
       (GEN_ALL inclusion_seq_eqv_l)
  \\ qspec_then
       `diag (W_ex G) ⨾ (TC (obs G ⨾ si G) RUNION is_init RCROSS COMPL is_init)`
       match_mp_tac rsubset_trans
  \\ strip_tac
  >- (xfs [] \\ metis_tac [])
  \\ rw [seq_runion_r, runion_rsubset]
  \\ simp [Once W_ex]
  \\ assume_tac no_po_to_init
  \\ xfs []
  \\ metis_tac []
QED

Theorem lob_scaob:
  WellFormed G /\ sc_per_loc G ==>
  lob G ⨾ scaob G RSUBSET TC (obs G ⨾ si G RUNION lob G)
Proof
  wf_tac [] []
  \\ simp [Once lob, Once ct_end, seq_assoc]
  \\ `RTC (lws G ⨾ si G RUNION dob G RUNION aob G RUNION bob G) RSUBSET
      RC (lob G)`
  by simp [lob, relationTheory.TC_RC_EQNS]
  \\ pop_assum rewrite
  \\ simp [seq_runion_l, seq_assoc]
  \\ `si G ⨾ scaob G RSUBSET si G`
  by (
    mp_tac si_si
    \\ xsimp [scaob]
    \\ metis_tac []
  )
  \\ pop_assum left_rewrite
  \\ `bob G ⨾ scaob G RSUBSET bob G`
  by (
    mp_tac bob_si
    \\ xsimp [scaob]
    \\ metis_tac []
  )
  \\ pop_assum rewrite
  \\ imp_res_tac dob_scaob
  \\ pop_assum rewrite
  \\ imp_res_tac aob_scaob
  \\ pop_assum rewrite
  \\ `lws G ⨾ si G RSUBSET lob G /\ dob G RSUBSET lob G /\ bob G RSUBSET lob G`
  by (
    rw [lob]
    \\ match_mp_tac rsubset_tc
    \\ xsimp []
  )
  \\ ntac 3 (pop_assum left_rewrite)
  \\ simp [seq_runion_l, seq_runion_r]
  \\ `RC (lob G) ⨾ lob G RSUBSET lob G`
  by simp [lob, relationTheory.TC_RC_EQNS, rt_ct]
  \\ simp [GSYM seq_assoc]
  \\ pop_assum left_rewrite
  \\ simp [seq_assoc]
  \\ left_rewrite inclusion_seq_eqv_l
  \\ rw [runion_rsubset]
  \\ TRY (
    match_mp_tac rsubset_tc
    \\ xsimp []
    \\ FAIL_TAC ""
  )
  >- (
    simp [Q.INST [`r` |-> `r1 RUNION r2`] ct_begin, seq_runion_l]
    \\ match_mp_tac rsubset_runion
    \\ disj2_tac
    \\ rsubset_tac
    \\ match_mp_tac tc_rsubset
    \\ simp []
    \\ match_mp_tac rsubset_rtc
    \\ simp [rsubset_runion]
  )
  \\ simp [Once (Q.INST [`r` |-> `r1 RUNION r2`] (GSYM rt_ct))]
  \\ match_mp_tac inclusion_seq_mon
  \\ strip_tac
  >- (
    match_mp_tac rc_rsubset
    \\ simp []
    \\ match_mp_tac rsubset_rtc
    \\ simp [rsubset_runion]
  )
  \\ match_mp_tac inclusion_t_t
  \\ xsimp []
QED

Theorem erln_refl1:
  WellFormed G /\
  ((im0 G RUNION obs G ⨾ si G RUNION lob G RUNION scaob G) x y \/
   (im0 G RUNION obs G ⨾ si G RUNION lob G RUNION scaob G) y x) ==> erln G x x
Proof
  simp [im0, scaob, ER, IR, erln]
  \\ disch_tac
  \\ xsimp []
  \\ disj2_tac
  \\ xfs []
  \\ assume_tac wf_siE
  \\ map_every imp_res_tac [wf_lobE, wf_obsE]
  \\ xfs []
  \\ metis_tac []
QED

Theorem erln_refl2:
  WellFormed G ==> (erln G x x <=> E G x)
Proof
  xrw [erln]
  \\ eq_tac
  \\ rw []
  \\ assume_tac wf_siE
  \\ xfs []
  \\ metis_tac []
QED

Triviality acyclic_pre_helper:
  WellFormed G /\ sc_per_loc G /\ acyclic (obs G ⨾ si G RUNION lob G) ==>
  acyclic
    (diag (W_ex G) ⨾ si G ⨾ aob G RUNION
     (scaob G RUNION
      (TC (obs G ⨾ si G RUNION lob G) RUNION is_init RCROSS COMPL is_init)))
Proof
  strip_tac
  \\ map_every imp_res_tac
       [ob_si_aob, wf_rfiD, W_ex_in_W, aob_in_po, lob_in_po, aob_Wex, lob_scaob,
        no_obs_to_init, diag_rsubset]
  \\ simple_cond_rewr acyclic_absorb
  >- (
    disj2_tac
    \\ rw [runion_rsubset, seq_runion_l]
    >- (
      pop_assum rewrite
      \\ simp [scaob, ER, IR]
      \\ qpat_x_assum `rfi G = xx` SUBST1_TAC
      \\ xsimp []
      \\ metis_tac [label_distinct]
    )
    >- (
      last_x_assum left_rewrite
      \\ xsimp []
    )
    \\ qpat_x_assum `aob G RSUBSET po G` rewrite
    \\ simp [Once no_po_to_init]
    \\ xsimp []
    \\ metis_tac []
  )
  \\ strip_tac
  >- (
    simp [GSYM seq_assoc]
    \\ simp [Once acyclic_seqC]
    \\ simp [GSYM seq_assoc]
    \\ qspec_then `lws G ⨾ si G` match_mp_tac acyclic_mon
    \\ reverse strip_tac
    >- (
      qpat_x_assum `aob G ⨾ diag (W_ex G) RSUBSET lws G` left_rewrite
      \\ simp []
    )
    \\ `lws G ⨾ si G RSUBSET lob G`
    by (
      simp [lob]
      \\ match_mp_tac rsubset_tc
      \\ simp [rsubset_runion]
    )
    \\ metis_tac [acyclic_mon, rsubset_runion]
  )
  \\ simple_cond_rewr acyclic_absorb
  >- (
    disj2_tac
    \\ simp [Once ct_end, seq_runion_r, seq_runion_l, seq_assoc]
    \\ qpat_x_assum `lob G ⨾ scaob G RSUBSET TC (obs G ⨾ si G RUNION lob G)`
         left_rewrite
    \\ `scaob G RSUBSET si G` by xsimp [scaob]
    \\ pop_assum left_rewrite
    \\ simp [si_si, rt_ct]
    \\ rw [runion_rsubset, rsubset_runion]
    >- simp [ct_end, seq_runion_r, rsubset_runion]
    \\ left_rewrite si_init
    \\ xsimp []
    \\ metis_tac []
  )
  \\ strip_tac
  >- metis_tac [scaob_scaob, acyclic_disj, rsubset_refl]
  \\ simp [acyclic, ct_of_union_ct_l]
  \\ simp [GSYM acyclic]
  \\ simple_cond_rewr acyclic_absorb
  >- (
    disj2_tac
    \\ qpat_x_assum `lob G RSUBSET po G` rewrite
    \\ simp [Once no_po_to_init]
    \\ qpat_x_assum `obs G RSUBSET K T RCROSS COMPL is_init` rewrite
    \\ rewrite si_init
    \\ xsimp []
    \\ metis_tac []
  )
  \\ simp []
  \\ match_mp_tac acyclic_disj
  \\ xsimp []
  \\ metis_tac []
QED

Theorem acyclic_pre_ec:
  WellFormed G /\ sc_per_loc G /\ acyclic (obs G ⨾ si G RUNION lob G) ==>
  acyclic
    (lift (erln G) (im0 G RUNION obs G ⨾ si G RUNION lob G RUNION scaob G))
Proof
  strip_tac
  \\ map_every imp_res_tac [acyclic_pre_helper, lob_erln, scaob_erln]
  \\ simple_cond_rewr acyclic_lift
  >- (
    simp [refl, erln_sym, erln_trans]
    \\ metis_tac [erln_refl1]
  )
  \\ simp [seq_runion_l, seq_assoc]
  \\ ntac 2 (pop_assum rewrite)
  \\ rewrite erln_in_si
  \\ simp [si_si]
  \\ `im0 G ⨾ si G RSUBSET is_init RCROSS COMPL is_init`
  by (
    rewrite si_init
    \\ xsimp [im0]
    \\ metis_tac []
  )
  \\ pop_assum rewrite
  \\ qspec_then
       `diag (W_ex G) ⨾ si G ⨾ aob G RUNION
        (scaob G RUNION
            (TC (obs G ⨾ si G RUNION lob G) RUNION
             is_init RCROSS COMPL is_init))`
       match_mp_tac acyclic_mon
  \\ rw [runion_rsubset]
  \\ TRY (xsimp [] \\ FAIL_TAC "")
  \\ metis_tac [rsubset_runion, rsubset_tc, rsubset_refl, rsubset_runion]
QED

Theorem partial_order_pre_ec:
  WellFormed G /\ sc_per_loc G /\ acyclic (obs G ⨾ si G RUNION lob G) ==>
  StrongOrder
    (TC (lift (erln G) (im0 G RUNION obs G ⨾ si G RUNION lob G RUNION scaob G)))
Proof
  simp [relationTheory.StrongOrder, GSYM acyclic, acyclic_pre_ec]
QED

Theorem co_in_ob2:
  WellFormed G /\ sc_per_loc G ==> G.co RSUBSET obs G ⨾ si G RUNION lob G
Proof
  strip_tac
  \\ imp_res_tac co_in_ob
  \\ pop_assum rewrite
  \\ simp [Once wf_obsE]
  \\ xrw []
  \\ metis_tac [si_refl]
QED

Theorem fr_in_ob2:
  WellFormed G /\ complete G /\ sc_per_loc G ==>
  fr G RSUBSET obs G ⨾ si G RUNION lob G
Proof
  rw [fri_union_fre, fri_lws, obs, lob]
  \\ xrw [runion_rsubset, Once relationTheory.TC_CASES1]
  \\ `si G y y`
  by (
    rfs [Once wf_freE, Once wf_lwsE]
    \\ xfs [si]
    \\ metis_tac [relationTheory.reflexive_def, ext_si_refl]
  )
  \\ metis_tac []
QED

Triviality ArmConsistent_implies_ExtComp:
  arm_ev G ==> arm_ec G
Proof
  rw [arm_ev, arm_ec, external_completion, linearization_of, preorder_cb_lift,
      preorder_cb, MC, dcbl, rf_cb, co_cb]
  \\ fs [arm_common, external]
  \\ wf_tac [is_total, wf_co_total_def, wf_col_def, wf_coE_def, wf_coD_def,
             wf_rfE_def, wf_rfD_def, wf_rfl_def, pred_setTheory.SPECIFICATION]
       [wf_obsE, wf_lobE, wf_rfeD, InternalConsistent_sc_per_loc]
  \\ `?cb.
        TC (lift (erln G) (im0 G RUNION obs G ⨾ si G RUNION
                           lob G RUNION scaob G)) RSUBSET cb /\
        strict_total_order UNIV cb`
  by metis_tac [strict_total_order_UNIV, partial_order_pre_ec,
                set_relationTheory.StrongOrder_extends_to_StrongLinearOrder]
  \\ rule_assum_tac
       (SIMP_RULE std_ss [strict_total_order, relationTheory.StrongOrder])
  \\ fs []
  \\ qexists_tac `restr_rel (classes (erln G)) cb`
  \\ simp [rf_fwd, rf_nfwd, dcbl, delift_restr_classes]
  \\ `G.co = delift (erln G) cb RINTER same_loc G RINTER W G RCROSS W G`
  by (
    rw [relationTheory.EqIsBothRSUBSET]
    >- (
      ntac 2 (last_x_assum (Tactical.CHANGED_TAC o SUBST1_TAC))
      \\ qpat_assum `xx RSUBSET cb` rewrite
      \\ `refl (erln G) (im0 G RUNION obs G ⨾ si G RUNION lob G RUNION scaob G)`
      by (
        simp [refl]
        \\ metis_tac [refl, erln_refl1]
      )
      \\ simp [delift_ct_lift, erln_sym, erln_trans]
      \\ `G.co RSUBSET (obs G ⨾ si G RUNION lob G) RINTER G.co`
      by (imp_res_tac co_in_ob2 \\ xfs [])
      \\ pop_assum rewrite
      \\ qpat_x_assum `G.co RSUBSET same_loc G` left_rewrite
      \\ right_rewrite ct_step
      \\ xrw []
      \\ qmatch_assum_rename_tac `same_loc G x y`
      \\ qexists_tac `x`
      \\ simp [erln_refl]
      \\ qexists_tac `y`
      \\ simp [erln_refl]
      \\ metis_tac []
    )
    \\ xrw [delift]
    \\ qmatch_assum_rename_tac `same_loc G x y`
    \\ qpat_x_assum `!a b. p` (qspecl_then [`x`, `y`] assume_tac)
    \\ rfs [GSYM same_loc,
            Once (SIMP_RULE std_ss [relationTheory.symmetric_def] same_loc_sym)]
    \\ `acts_set G x /\ acts_set G y`
    by (
      map_every assume_tac [erln_in_si, wf_siE]
      \\ xfs []
      \\ metis_tac []
    )
    \\ fs []
    \\ Cases_on `x = y`
    >- gs [relationTheory.irreflexive_def]
    \\ fs []
    \\ spose_not_then kall_tac
    \\ qpat_x_assum `irreflexive cb` mp_tac
    \\ simp [relationTheory.irreflexive_def]
    \\ qsuff_tac
         `?x y. cb (erln G x) (erln G y) /\
                (im0 G RUNION obs G ⨾ si G RUNION lob G RUNION scaob G) y x`
    >- metis_tac [relationTheory.transitive_def, ct_step, step_lift2,
                  relationTheory.RSUBSET]
    \\ qexistsl_tac [`x`, `y`]
    \\ simp []
    \\ imp_res_tac co_in_ob2
    \\ xfs []
    \\ metis_tac []
  )
  \\ rw []
  >- (
    simp [restr_relEE, rsubset_rinter]
    \\ strip_tac
    >- (
      qpat_assum `xx RSUBSET cb` rewrite
      \\ match_mp_tac rsubset_tc
      \\ match_mp_tac lift_mori
      \\ xrw [runion_rsubset]
    )
    \\ xrw [lift, classes]
    \\ metis_tac []
  )
  >- (
    simp [strict_total_order, relationTheory.StrongOrder,
          irreflexive_restr, transitive_restr]
    \\ match_mp_tac is_total_restr
    \\ fs [is_total]
  )
  >- xsimp [restr_rel, classes]
  \\ last_assum (Tactical.CHANGED_TAC o SUBST1_TAC)
  \\ first_assum (Tactical.CHANGED_TAC o SUBST1_TAC)
  \\ simp [po_loc, intervening_write, GSYM runion_rinter_l]
  \\ xsimp [relationTheory.EqIsBothRSUBSET, delift]
  \\ ntac 4 strip_tac
  \\ simp []
  >- (
    qmatch_assum_rename_tac `G.rf x y`
    \\ `same_loc G x y` by xfs []
    \\ simp []
    \\ `!X Y. X = erln G x /\ Y = erln G y ==> cb X Y \/ cb Y X`
    by (
      ntac 3 strip_tac
      \\ qpat_x_assum `is_total UNIV cb`
           (match_mp_tac o SIMP_RULE std_ss [is_total])
      \\ xsimp []
      \\ qexists_tac `x`
      \\ simp [erln_refl]
      \\ xrw [erln, ER, rfe, label_distinct]
      \\ xfs [rfe]
      \\ metis_tac [label_distinct]
    )
    \\ pop_assum
         (qspecl_then [`erln G x`, `erln G y`]
           (strip_assume_tac o SIMP_RULE std_ss []))
    >- (
      disj2_tac
      \\ strip_tac
      >- simp [erln_refl]
      \\ spose_not_then strip_assume_tac
      \\ qmatch_assum_rename_tac `W G z`
      \\ `G.co x z`
      by (
        qpat_x_assum `p ==> po G z y` kall_tac
        \\ fs [DECIDE ``((a ==> b ==> ~c) ==> d) = (a /\ b /\ c \/ d)``]
        >- xsimp [delift]
        \\ first_x_assum (SUBST1_TAC o SYM)
        \\ match_mp_tac po_loc_ww
        \\ simp []
      )
      \\ qpat_x_assum `p ==> po G x z` kall_tac
      \\ fs [DECIDE ``((a ==> b ==> ~c) ==> d) = (a /\ b /\ c \/ d)``]
      >- (
        qpat_x_assum `irreflexive cb` mp_tac
        \\ simp [relationTheory.irreflexive_def]
        \\ qexists_tac `erln G z`
        \\ qpat_x_assum `transitive cb`
             (match_mp_tac o SIMP_RULE std_ss [relationTheory.transitive_def])
        \\ qexists_tac `erln G y`
        \\ simp []
        \\ qpat_x_assum `p RSUBSET cb`
             (match_mp_tac o SIMP_RULE std_ss [relationTheory.RSUBSET])
        \\ match_mp_tac relationTheory.TC_SUBSET
        \\ match_mp_tac step_lift2
        \\ imp_res_tac fr_in_ob2
        \\ xfs [fr]
        \\ metis_tac []
      )
      \\ qpat_x_assum `sc_per_loc G` mp_tac
      \\ simp [sc_per_loc, relationTheory.irreflexive_def]
      \\ qexists_tac `z`
      \\ simp [eco, fr]
      \\ first_x_assum (SUBST1_TAC o SYM)
      \\ xsimp [rc_runion]
      \\ metis_tac []
    )
    \\ disj1_tac
    \\ rw [erln_refl]
    >- (
      spose_not_then assume_tac
      \\ qpat_x_assum `irreflexive cb` mp_tac
      \\ simp [relationTheory.irreflexive_def]
      \\ qexists_tac `erln G y`
      \\ qpat_x_assum `transitive cb`
           (match_mp_tac o SIMP_RULE std_ss [relationTheory.transitive_def])
      \\ qexists_tac `erln G x`
      \\ simp []
      \\ qpat_x_assum `p RSUBSET cb`
           (match_mp_tac o SIMP_RULE std_ss [relationTheory.RSUBSET])
      \\ match_mp_tac relationTheory.TC_SUBSET
      \\ match_mp_tac step_lift2
      \\ xsimp [obs, rfe]
      \\ metis_tac [si_refl, relationTheory.reflexive_def]
    )
    >- fs [same_loc]
    \\ spose_not_then strip_assume_tac
    \\ qmatch_assum_rename_tac `po G z y`
    \\ `G.co x z` by imp_res_tac po_loc_ww
    \\ qpat_x_assum `sc_per_loc G` mp_tac
    \\ simp [sc_per_loc, relationTheory.irreflexive_def]
    \\ qexists_tac `z`
    \\ simp [eco, fr]
    \\ first_x_assum (SUBST1_TAC o SYM)
    \\ xsimp [rc_runion]
    \\ metis_tac []
  )
  >- (
    rename1 `G.rf x y`
    \\ `acts_set G x /\ acts_set G y`
    by (
      map_every assume_tac [erln_in_si, wf_siE]
      \\ xfs []
      \\ metis_tac []
    )
    \\ simp []
    \\ qpat_x_assum `po G x y`
         (strip_assume_tac o SIMP_RULE (rel_ss()) [Once wf_poE])
    \\ `?w. G.rf w y` by xfs [complete]
    \\ `same_loc G w y` by xfs [wf_rfl_def]
    \\ Cases_on `x = w`
    \\ simp []
    \\ `acts_set G w /\ W G w` by (xfs [] \\ metis_tac [])
    \\ spose_not_then kall_tac
    \\ Cases_on `is_init w`
    >- (
      `po G w x`
      by (
        xsimp [po, ext_sb]
        \\ Cases_on `x`
        \\ Cases_on `w`
        \\ gs [is_init, same_loc, loc, wf_init_lab_def]
        \\ metis_tac [optionTheory.SOME_11]
      )
      \\ `same_loc G w x` by fs [same_loc]
      \\ `G.co w x` by imp_res_tac po_loc_ww
      \\ qpat_x_assum `sc_per_loc G` mp_tac
      \\ simp [sc_per_loc, relationTheory.irreflexive_def, eco, fr]
      \\ first_x_assum (SUBST1_TAC o SYM)
      \\ xsimp [rc_runion]
      \\ metis_tac []
    )
    \\ `G.co w x \/ G.co x w`
    by (
      first_x_assum match_mp_tac
      \\ fs [same_loc]
    )
    >- (
      qpat_x_assum `sc_per_loc G` mp_tac
      \\ simp [sc_per_loc, relationTheory.irreflexive_def, eco, fr]
      \\ first_x_assum (SUBST1_TAC o SYM)
      \\ xsimp [rc_runion]
      \\ metis_tac []
    )
    \\ Cases_on `po G w y`
    >- (
      qpat_x_assum `!y. p` (qspec_then `w` strip_assume_tac)
      \\ TRY (rfs [same_loc] \\ FAIL_TAC "")
      \\ pop_assum mp_tac
      \\ mp_tac
           (Q.INST [`y` |-> `x`, `x` |-> `y`, `z` |-> `w`] po_semi_total_r)
      \\ rw []
      >- (
        spose_not_then kall_tac
        \\ qpat_x_assum `sc_per_loc G` mp_tac
        \\ simp [sc_per_loc, relationTheory.irreflexive_def, eco]
        \\ first_x_assum (SUBST1_TAC o SYM)
        \\ qexists_tac `w`
        \\ xsimp [rc_runion]
        \\ metis_tac []
      )
      \\ xfs [wf_sil_def]
      \\ metis_tac []
    )
    \\ qpat_x_assum `irreflexive cb` mp_tac
    \\ simp [relationTheory.irreflexive_def]
    \\ qsuff_tac `?z. cb (erln G x) z /\ cb z (erln G y)`
    >- metis_tac [relationTheory.transitive_def]
    \\ qexists_tac `erln G w`
    \\ imp_res_tac co_in_ob2
    \\ strip_tac
    \\ qpat_x_assum `p RSUBSET cb`
         (match_mp_tac o SIMP_RULE std_ss [relationTheory.RSUBSET])
    \\ match_mp_tac relationTheory.TC_SUBSET
    \\ match_mp_tac step_lift2
    >- (
      xfs []
      \\ metis_tac []
    )
    \\ qsuff_tac `(obs G ⨾ si G) w y`
    >- xsimp []
    \\ xsimp []
    \\ qexists_tac `y`
    \\ xsimp [si_refl, obs, rfe, fre, fr]
  )
  \\ qmatch_assum_rename_tac `same_loc G x y`
  \\ `acts_set G x /\ acts_set G y`
  by (
    map_every assume_tac [erln_in_si, wf_siE]
    \\ xfs []
    \\ metis_tac []
  )
  \\ simp []
  \\ `?w. G.rf w y` by xfs [complete]
  \\ `same_loc G w y` by xfs [wf_rfl_def]
  \\ Cases_on `x = w`
  \\ simp []
  \\ `acts_set G w /\ W G w` by (xfs [] \\ metis_tac [])
  \\ spose_not_then kall_tac
  \\ `G.co x w \/ G.co w x`
  by (
    first_x_assum match_mp_tac
    \\ fs [same_loc]
  )
  >- (
    qpat_x_assum `!y. p` (qspec_then `w` mp_tac)
    \\ simp []
    \\ strip_tac
    >- (
      rfs []
      \\ xfs [delift]
    )
    \\ Cases_on `po G w y`
    \\ simp [erln_refl]
    \\ qpat_x_assum `p RSUBSET cb`
         (match_mp_tac o SIMP_RULE std_ss [relationTheory.RSUBSET])
    \\ match_mp_tac relationTheory.TC_SUBSET
    \\ match_mp_tac step_lift2
    \\ qsuff_tac `(obs G ⨾ si G) w y`
    >- xsimp []
    \\ xsimp [obs, rfe, fre, fr, delift]
    \\ metis_tac [si_refl]
  )
  \\ qpat_x_assum `irreflexive cb` mp_tac
  \\ simp [relationTheory.irreflexive_def]
  \\ qsuff_tac `cb (erln G y) (erln G x)`
  >- metis_tac [relationTheory.transitive_def]
  \\ qpat_x_assum `p RSUBSET cb`
       (match_mp_tac o SIMP_RULE std_ss [relationTheory.RSUBSET])
  \\ match_mp_tac relationTheory.TC_SUBSET
  \\ match_mp_tac step_lift2
  \\ imp_res_tac fr_in_ob2
  \\ xfs [fr]
  \\ metis_tac []
QED

Theorem obs_si_scaob:
  WellFormed G /\ complete G ==>
  obs G ⨾ si G = obs G ⨾ erln G RUNION rfe G ⨾ scaob G
Proof
  wf_tac [wf_siD_def] []
  \\ reverse (rw [relationTheory.EqIsBothRSUBSET, obs])
  >- (
    left_rewrite erln_in_si
    \\ xsimp [scaob]
    \\ metis_tac []
  )
  \\ xrw [erln]
  \\ qmatch_assum_rename_tac `si G z y`
  \\ qpat_x_assum `!x y. p` imp_res_tac
  >- (
    rfs [Once wf_rfeD, Once wf_siE]
    \\ xfs []
    \\ `R G y`
    by (
      fs [si_matching_label]
      \\ Cases_on `G.lab y`
      \\ Cases_on `G.lab z`
      \\ fs [is_r]
    )
    \\ `?k. G.rf k y` by xfs [complete]
    \\ xfs [scaob, rfe, rfi, ER, IR]
    \\ metis_tac []
  )
  \\ rfs [Once wf_freD, Once wf_coeD]
  \\ xfs []
  \\ disj1_tac
  \\ qexists_tac `z`
  \\ simp []
  \\ ntac 3 disj1_tac
  \\ fs [si_matching_label]
  \\ Cases_on `G.lab y`
  \\ Cases_on `G.lab z`
  \\ fs [is_w]
QED

Theorem erln_rewrite:
  WellFormed G /\ erln G x y ==> erln G x = erln G y
Proof
  xrw []
  \\ metis_tac [erln_trans, erln_sym, relationTheory.transitive_def,
                relationTheory.symmetric_def]
QED

Theorem ArmConsistentExtComp_equiv:
  arm_ev = arm_ec
Proof
  simp [FUN_EQ_THM]
  \\ Q.X_GEN_TAC `G`
  \\ eq_tac
  >- simp [ArmConsistent_implies_ExtComp]
  \\ rw [arm_ev, arm_ec, external_completion, linearization_of,
         preorder_cb_lift, preorder_cb, MC, dcbl, rf_cb, co_cb]
  \\ fs [arm_common, external, strict_total_order, relationTheory.StrongOrder]
  \\ `rfe G RSUBSET delift (erln G) cb`
  by (
    simp [rfe, rf_fwd, rf_nfwd, po_loc, dcbl, intervening_write]
    \\ xsimp [rc_runion, delift]
    \\ metis_tac []
  )
  \\ `fr G RSUBSET delift (erln G) cb`
  by (
    xrw [fr, rf_fwd, rf_nfwd, po_loc, dcbl, intervening_write, rc_runion,
         delift]
    \\ simp []
    >- metis_tac [same_loc_trans, relationTheory.transitive_def]
    \\ fs [is_total, pred_setTheory.SPECIFICATION]
    \\ qmatch_rename_tac `cb (erln G x) (erln G y)`
    \\ `cb (erln G x) (erln G y) \/ cb (erln G y) (erln G x)`
    by (
      first_x_assum match_mp_tac
      \\ rw [classes]
      >- metis_tac []
      >- metis_tac []
      \\ simp [FUN_EQ_THM]
      \\ qexists_tac `x`
      \\ simp []
      \\ xsimp [erln]
      \\ spose_not_then strip_assume_tac
      \\ xfs [ER, rfe, rf_fwd, rf_nfwd, intervening_write, delift]
      \\ metis_tac [label_distinct]
    )
    \\ metis_tac [same_loc_trans, same_loc_sym, relationTheory.transitive_def,
                  relationTheory.symmetric_def]
  )
  \\ simp [acyclic]
  \\ match_mp_tac irreflexive_inclusion
  \\ qexists_tac `delift (erln G) cb`
  \\ reverse strip_tac
  >- fs [relationTheory.irreflexive_def, delift]
  \\ match_mp_tac tc_rsubset
  \\ reverse strip_tac
  >- (
    fs [relationTheory.transitive_def, delift]
    \\ metis_tac []
  )
  \\ simp [obs_si_scaob, obs, seq_runion_l]
  \\ qpat_assum `rfe G RSUBSET delift (erln G) cb` left_rewrite
  \\ rewrite coe_in_co
  \\ simp []
  \\ rewrite fre_in_fr
  \\ qpat_assum `fr G RSUBSET delift (erln G) cb` left_rewrite
  \\ simp [runion_idem]
  \\ xrw [delift, erln_refl2]
  \\ simp []
  \\ TRY (metis_tac [erln_rewrite])
  \\ TRY (
    map_every assume_tac [erln_in_si, wf_siE]
    \\ xfs []
    \\ metis_tac []
  )
  \\ TRY (
    xfs [scaob, si]
    \\ FAIL_TAC ""
  )
  \\ TRY (
    imp_res_tac lob_in_po
    \\ assume_tac wf_poE
    \\ xfs []
    \\ metis_tac []
  )
  >- (
    qmatch_rename_tac `cb (erln G x) (erln G y)`
    \\ qpat_x_assum `transitive cb`
         (match_mp_tac o SIMP_RULE std_ss [relationTheory.transitive_def])
    \\ qexists_tac `erln G y'`
    \\ xfs [lift]
    \\ metis_tac []
  )
  \\ xfs [lift]
  \\ metis_tac []
QED

(* - Equivalence to external global completion model ----------------------- *)

Theorem acyclic_pre_gcb1:
  WellFormed G /\ complete G /\ sc_per_loc G /\
  acyclic (obs G ⨾ si G RUNION lob G) ==>
  acyclic ((rfi G RUNION
            is_init RCROSS COMPL is_init RUNION
            scaob G RUNION
            erln G ⨾ obs G ⨾ si G RUNION
            erln G ⨾ (lob G RINTER gc_req G)) ⨾ erln G)
Proof
  wf_tac [wf_rfl_def, wf_col_def, wf_siD_def, wf_coD_def, wf_rfD_def,
          wf_rfE_def, wf_rff_def, functional] []
  \\ simp [seq_runion_l, seq_assoc]
  \\ `is_init RCROSS COMPL is_init ⨾ erln G RSUBSET
      is_init RCROSS COMPL is_init`
  by (
    rewrite erln_in_si
    \\ rewrite si_init
    \\ xsimp []
    \\ metis_tac []
  )
  \\ pop_assum rewrite
  \\ `si G ⨾ erln G RSUBSET si G`
  by (
    left_rewrite erln_in_si
    \\ simp [si_si]
  )
  \\ pop_assum rewrite
  \\ `rfi G ⨾ erln G ⨾ obs G RSUBSET
      is_init RCROSS COMPL is_init RUNION erln G ⨾ coe G`
  by (
    rw [obs, seq_runion_r, runion_rsubset]
    \\ TRY (
      left_rewrite erln_in_si
      \\ simp [Once wf_rfeD, Once wf_coeD, Once wf_rfiD]
      \\ xrw []
      \\ res_tac
      \\ qmatch_assum_rename_tac `si G v w`
      \\ Cases_on `G.lab v`
      \\ Cases_on `G.lab w`
      \\ fs [si_matching_label, is_r, is_w]
      \\ FAIL_TAC ""
    )
    \\ `rfi G ⨾ erln G RSUBSET si G ⨾ rfi G`
    by (
      simp [Once wf_rfiD, erln, rfisw, ER, rfe, rfi, fre]
      \\ xrw []
      \\ TRY (metis_tac [label_distinct, si_refl])
      \\ xfs [wf_rfE_def]
      \\ metis_tac [si_refl]
    )
    \\ simp [GSYM seq_assoc]
    \\ pop_assum rewrite
    \\ simp [seq_assoc, rfe, rfi, fre, fr, coe]
    \\ imp_res_tac no_co_to_init
    \\ pop_assum rewrite
    \\ first_x_assum SUBST1_TAC
    \\ qpat_x_assum `G.rf = xx` (fn th => simp [Once th])
    \\ xrw [erln]
    \\ qmatch_assum_rename_tac `si G x v`
    \\ qmatch_assum_rename_tac `G.rf v w`
    \\ qmatch_assum_rename_tac `G.rf z w`
    \\ qmatch_assum_rename_tac `G.co z y`
    \\ Cases_on `is_init x`
    \\ simp []
    \\ `W G x`
    by (
      res_tac
      \\ Cases_on `G.lab v`
      \\ Cases_on `G.lab x`
      \\ fs [si_matching_label, is_r, is_w]
    )
    \\ `z = v` by metis_tac []
    \\ pop_assum SUBST_ALL_TAC
    \\ qexists_tac `v`
    \\ simp []
    \\ strip_tac
    \\ assume_tac (Q.INST [`z` |-> `w`, `x` |-> `v`] po_semi_total_l)
    \\ rfs []
    >- (
      assume_tac si_init
      \\ xfs []
      \\ metis_tac []
    )
    >- (
      qpat_x_assum `sc_per_loc G` mp_tac
      \\ xsimp [sc_per_loc, eco, rc_runion, fr, relationTheory.irreflexive_def]
      \\ metis_tac []
    )
    \\ xfs [wf_sil_def, same_loc]
    \\ metis_tac [label_distinct]
  )
  \\ `rfi G ⨾ erln G ⨾ lob G RINTER gc_req G RSUBSET
      erln G ⨾ lob G RINTER gc_req G`
  by (
    `rfi G ⨾ erln G RSUBSET erln G ⨾ rfi G`
    by (
      map_every imp_res_tac [wf_rfeE, wf_rfiD]
      \\ xrw [erln, rfisw, ER, rfi, rfe]
      \\ xfs []
      \\ metis_tac [label_distinct, si_refl]
    )
    \\ simp [GSYM seq_assoc]
    \\ pop_assum rewrite
    \\ simp [seq_assoc, Once gc_req, Once wf_rfiD, rfe]
    \\ xrw [rfi]
    >- metis_tac [label_distinct]
    >- metis_tac [label_distinct]
    \\ xsimp [gc_req, rfi, rfe]
    \\ metis_tac []
  )
  \\ simp [GSYM relationTheory.RUNION_ASSOC]
  \\ simp [Once relationTheory.RUNION_COMM]
  \\ simple_cond_rewr acyclic_absorb
  >- (
    disj1_tac
    \\ simp [seq_runion_r, seq_assoc]
    \\ `erln G ⨾ erln G RSUBSET erln G`
    by (
      xsimp []
      \\ metis_tac [erln_trans, erln_sym, relationTheory.symmetric_def,
                    relationTheory.transitive_def]
    )
    \\ `!r: ActID -> ActID -> bool. erln G ⨾ erln G ⨾ r = (erln G ⨾ erln G) ⨾ r`
    by simp [seq_assoc]
    \\ pop_assum (fn th => rewrite_tac [th])
    \\ pop_assum left_rewrite
    \\ CONV_TAC (PATH_CONV "lrrr" (REWRITE_CONV [GSYM seq_assoc]))
    \\ ntac 2 (pop_assum (rewrite o REWRITE_RULE [GSYM seq_assoc]))
    \\ simp [seq_assoc, seq_runion_l]
    \\ gen_rewrite (1, 0) erln_in_si
    \\ gen_rewrite (2, 0) si_init
    \\ rw [runion_rsubset]
    \\ TRY (xsimp [] \\ metis_tac [])
    >- (
      simp [rfi, Once no_rf_to_init]
      \\ xsimp []
      \\ metis_tac []
    )
    >- (
      CONV_TAC (PATH_CONV "lrr" (REWRITE_CONV [GSYM seq_assoc]))
      \\ pop_assum (fn th => simp [th, erln_scaob])
      \\ xrw [scaob, ER, IR, rfe, rfi]
      \\ metis_tac []
    )
    \\ xsimp [obs]
    \\ metis_tac []
  )
  \\ reverse strip_tac
  >- (
    simp [Once wf_rfiD]
    \\ rewrite erln_in_si
    \\ match_mp_tac acyclic_disj
    \\ xrw []
    \\ spose_not_then strip_assume_tac
    \\ ntac 3 (pop_assum kall_tac)
    \\ qmatch_assum_rename_tac `si G z y`
    \\ res_tac
    \\ Cases_on `G.lab y`
    \\ Cases_on `G.lab z`
    \\ fs [si_matching_label, is_r, is_w]
  )
  \\ simple_cond_rewr acyclic_absorb
  >- (
    disj1_tac
    \\ simp [scaob, ER, IR]
    \\ imp_res_tac no_obs_to_init
    \\ pop_assum rewrite
    \\ rewrite erln_in_si
    \\ rewrite si_init
    \\ imp_res_tac lob_in_po
    \\ pop_assum rewrite
    \\ simp [Once no_po_to_init]
    \\ xsimp []
    \\ metis_tac []
  )
  \\ strip_tac
  >- (
    match_mp_tac acyclic_disj
    \\ xsimp []
    \\ metis_tac []
  )
  \\ imp_res_tac scaob_erln
  \\ pop_assum rewrite
  \\ simp [Once (GSYM erln_scaob), GSYM seq_runion_r, Once acyclic_seqC,
           seq_runion_l, seq_assoc]
  \\ `erln G ⨾ erln G RSUBSET erln G`
  by (
    xsimp []
    \\ metis_tac [erln_trans, erln_sym, relationTheory.symmetric_def,
                  relationTheory.transitive_def]
  )
  \\ pop_assum rewrite
  \\ imp_res_tac scaob_erln
  \\ pop_assum rewrite
  \\ gen_rewrite (1, 0) erln_in_si
  \\ simp [si_si]
  \\ `!r. lob G RINTER r RSUBSET lob G` by xsimp []
  \\ pop_assum (rewrite o SPEC_ALL)
  \\ imp_res_tac lob_erln
  \\ pop_assum rewrite
  \\ match_mp_tac acyclic_mon
  \\ qexists_tac
       `diag (W_ex G) ⨾ si G ⨾ aob G RUNION
        (scaob G RUNION
         (TC (obs G ⨾ si G RUNION lob G) RUNION
         is_init RCROSS COMPL is_init))`
  \\ simp [acyclic_pre_helper]
  \\ xrw [runion_rsubset]
  \\ ntac 2 disj2_tac
  \\ disj1_tac
  \\ match_mp_tac relationTheory.TC_SUBSET
  \\ xsimp []
  \\ metis_tac []
QED

Theorem erln_refl3:
  WellFormed G /\
  ((im0 G RUNION G.rf RUNION G.co RUNION fr G RUNION obs G ⨾ si G RUNION
    lob G RINTER gc_req G RUNION scaob G) x y \/
   (im0 G RUNION G.rf RUNION G.co RUNION fr G RUNION obs G ⨾ si G RUNION
    lob G RINTER gc_req G RUNION scaob G) y x) ==>
  erln G x x
Proof
  wf_tac [wf_rfE_def, wf_coE_def] []
  \\ qpat_x_assum `f (a: ActID) b` mp_tac
  \\ xrw [im0, scaob]
  \\ map_every imp_res_tac [wf_frE, lob_in_po, wf_obsE]
  \\ map_every assume_tac [wf_siE, wf_poE]
  \\ xfs [erln]
  \\ metis_tac []
QED

Theorem acyclic_pre_egc:
  WellFormed G /\ complete G /\ sc_per_loc G /\
  acyclic (obs G ⨾ si G RUNION lob G) ==>
  acyclic (lift (erln G)
             (im0 G RUNION
              G.rf RUNION
              G.co RUNION
              fr G RUNION
              obs G ⨾ si G RUNION
              lob G RINTER gc_req G
              RUNION scaob G))
Proof
  wf_tac [wf_rfD_def, wf_rfl_def] []
  \\ simple_cond_rewr acyclic_lift
  >- (
    simp [erln_sym, erln_trans, refl]
    \\ metis_tac [erln_refl3]
  )
  \\ imp_res_tac acyclic_pre_gcb1
  \\ match_mp_tac acyclic_mon
  \\ HINT_EXISTS_TAC
  \\ simp []
  \\ pop_assum kall_tac
  \\ match_mp_tac inclusion_seq_mon
  \\ simp []
  \\ `im0 G RSUBSET is_init RCROSS COMPL is_init` by xsimp [im0]
  \\ pop_assum left_rewrite
  \\ simp [rfi_union_rfe, coi_union_coe, fri_union_fre, coi_lws, fri_lws]
  \\ `diag (W G) ⨾ lws G RSUBSET lob G RINTER gc_req G`
  by (
    simp [Once lob, gc_req]
    \\ right_rewrite ct_step
    \\ xrw []
    \\ ntac 3 disj1_tac
    \\ HINT_EXISTS_TAC
    \\ simp []
    \\ match_mp_tac si_refl
    \\ map_every assume_tac [lws_in_po, wf_poE]
    \\ xfs []
    \\ metis_tac []
  )
  \\ pop_assum left_rewrite
  \\ `diag (R G) ⨾ lws G RSUBSET lob G RINTER gc_req G`
  by (
    simp [Once lob, gc_req]
    \\ right_rewrite ct_step
    \\ xsimp []
    \\ map_every Q.X_GEN_TAC [`x`, `y`]
    \\ strip_tac
    \\ `E G x /\ E G y`
    by (
      map_every assume_tac [lws_in_po, wf_poE]
      \\ xfs []
      \\ metis_tac []
    )
    \\ xrw []
    >- metis_tac [si_refl]
    \\ `?w. G.rf w x` by xfs [complete]
    \\ reverse (Cases_on `po G w x`)
    \\ xsimp [rfe, rfi]
    >- metis_tac []
    \\ disj2_tac
    \\ HINT_EXISTS_TAC
    \\ simp [lob]
    \\ match_mp_tac relationTheory.TC_SUBSET
    \\ first_x_assum (CHANGED_TAC o SUBST_ALL_TAC)
    \\ xfs [lws, po_loc]
    \\ ntac 3 disj1_tac
    \\ qexists_tac `y`
    \\ fs [si_refl, same_loc]
    \\ metis_tac [po_trans, relationTheory.transitive_def]
  )
  \\ pop_assum left_rewrite
  \\ `obs G RSUBSET erln G ⨾ obs G`
  by (
    xrw [Once wf_obsE]
    \\ HINT_EXISTS_TAC
    \\ simp [erln_refl2]
  )
  \\ simp [GSYM seq_assoc]
  \\ pop_assum right_rewrite
  \\ `rfe G RSUBSET obs G /\ fre G RSUBSET obs G /\ coe G RSUBSET obs G`
  by xsimp [obs]
  \\ ntac 3 (pop_assum left_rewrite)
  \\ `obs G RSUBSET obs G ⨾ si G`
  by (xsimp [Once wf_obsE] \\ metis_tac [si_refl])
  \\ pop_assum (gen_rewrite (3, 0))
  \\ `lob G RINTER gc_req G RSUBSET erln G ⨾ lob G RINTER gc_req G`
  by (
    xrw []
    \\ HINT_EXISTS_TAC
    \\ simp []
    \\ match_mp_tac erln_refl
    \\ imp_res_tac lob_in_po
    \\ xfs [Once wf_poE]
    \\ metis_tac []
  )
  \\ xrw [runion_rsubset]
  \\ xfs []
QED

Theorem partial_order_pre_egc:
  WellFormed G /\ complete G /\ sc_per_loc G /\
  acyclic (obs G ⨾ si G RUNION lob G) ==>
  StrongOrder
    (TC (lift (erln G)
           (im0 G RUNION G.rf RUNION G.co RUNION fr G RUNION obs G ⨾ si G RUNION
            lob G RINTER gc_req G RUNION scaob G)))
Proof
  rw [relationTheory.StrongOrder]
  \\ imp_res_tac acyclic_pre_egc
  \\ fs [acyclic]
QED

Triviality ArmConsistent_implies_GlobExtComp:
  arm_ev G ==> arm_egc G
Proof
  rw [arm_ev, arm_egc, external_global, linearization_of, preorder_gcb_lift,
      preorder_gcb, MC, dgcbl, rf_cb, co_cb]
  \\ fs [arm_common, external]
  \\ imp_res_tac InternalConsistent_sc_per_loc
  \\ wf_tac [wf_coE_def, wf_coD_def, wf_col_def] []
  \\ `?gcb.
        TC (lift (erln G)
          (im0 G RUNION G.rf RUNION G.co RUNION fr G RUNION obs G ⨾ si G RUNION
           lob G RINTER gc_req G RUNION scaob G)) RSUBSET gcb /\
        strict_total_order UNIV gcb`
  by metis_tac [strict_total_order_UNIV, partial_order_pre_egc,
                set_relationTheory.StrongOrder_extends_to_StrongLinearOrder]
  \\ rule_assum_tac
       (SIMP_RULE std_ss [strict_total_order, relationTheory.StrongOrder])
  \\ fs []
  \\ qexists_tac `restr_rel (classes (erln G)) gcb`
  \\ simp [rf_gcb, co_gcb, dgcbl, delift_restr_classes]
  \\ `G.co RSUBSET delift (erln G) gcb`
  by (
    qpat_assum `xx RSUBSET gcb` rewrite
    \\ right_rewrite ct_step
    \\ `refl (erln G)
           (im0 G RUNION G.rf RUNION G.co RUNION fr G RUNION
            obs G ⨾ si G RUNION lob G RINTER gc_req G RUNION scaob G)`
    by (
      simp [refl]
      \\ metis_tac [refl, erln_refl3]
    )
    \\ simp [delift_lift, erln_sym, erln_trans]
    \\ qpat_x_assum `G.co = diag (acts_set G) ⨾ G.co ⨾ diag (acts_set G)`
         (fn th => simp [Once th])
    \\ xrw []
    \\ metis_tac [erln_refl]
  )
  \\ `G.co = (W G RCROSS W G) RINTER delift (erln G) gcb RINTER same_loc G`
  by (
    rw [relationTheory.EqIsBothRSUBSET]
    >- (
      `G.co RSUBSET G.co RINTER delift (erln G) gcb` by xfs []
      \\ pop_assum rewrite
      \\ qpat_x_assum `G.co = diag (acts_set G) ⨾ G.co ⨾ diag (acts_set G)`
           (fn th => simp [Once th])
      \\ qpat_x_assum `G.co = xx` (fn th => simp [Once th])
      \\ qpat_x_assum `G.co RSUBSET same_loc G` left_rewrite
      \\ xsimp []
    )
    \\ xrw [delift]
    \\ qmatch_rename_tac `G.co x y`
    \\ `x <> y` by metis_tac [relationTheory.irreflexive_def]
    \\ rfs [erln_refl2, wf_co_total_def, is_total, pred_setTheory.SPECIFICATION]
    \\ `same_loc G y x`
    by metis_tac [same_loc_sym, relationTheory.symmetric_def]
    \\ qpat_x_assum `!a b. p` (qspecl_then [`x`, `y`] assume_tac)
    \\ rfs [GSYM same_loc]
    \\ spose_not_then kall_tac
    \\ `delift (erln G) gcb y x` by xfs []
    \\ pop_assum mp_tac
    \\ simp [delift, erln_refl]
    \\ metis_tac [relationTheory.irreflexive_def, relationTheory.transitive_def]
  )
  \\ simp []
  \\ rpt strip_tac
  >- (
    qpat_x_assum `TC xx RSUBSET gcb` rewrite
    \\ xrw [lift, restr_rel, classes]
    \\ TRY (metis_tac [])
    \\ match_mp_tac relationTheory.TC_SUBSET
    \\ xsimp [lift]
    \\ metis_tac []
  )
  >- (
    simp [strict_total_order, relationTheory.StrongOrder,
          irreflexive_restr, transitive_restr]
    \\ match_mp_tac is_total_restr
    \\ fs [is_total]
  )
  >- xsimp [restr_rel, classes]
  \\ pop_assum kall_tac
  \\ rw [relationTheory.EqIsBothRSUBSET]
  >- (
    fs [wf_rfE_def, wf_rfD_def, wf_rfl_def]
    \\ qpat_x_assum `G.rf = diag (acts_set G) ⨾ G.rf ⨾ diag (acts_set G)`
         SUBST1_TAC
    \\ qpat_x_assum `G.rf = diag (W G) ⨾ G.rf ⨾ diag (R G)` SUBST1_TAC
    \\ xrw [delift, erln_refl, intervening_write]
    \\ TRY (xfs [] \\ FAIL_TAC "")
    \\ qmatch_assum_rename_tac `G.rf x y`
    >- (
      qpat_x_assum `p RSUBSET cb`
           (match_mp_tac o SIMP_RULE std_ss [relationTheory.RSUBSET])
      \\ simple_cond_rewr ct_lift
      >- (
        simp [refl, erln_sym, erln_trans]
        \\ metis_tac [erln_refl3]
      )
      \\ xrw []
      \\ qexists_tac `x`
      \\ simp [erln_refl]
      \\ match_mp_tac relationTheory.TC_SUBSET
      \\ xsimp [fr]
      \\ metis_tac [erln_refl]
    )
    \\ spose_not_then strip_assume_tac
    \\ qmatch_assum_rename_tac `erln G z z`
    \\ rfs [erln_refl2]
    \\ `z <> x` by metis_tac [relationTheory.irreflexive_def]
    \\ `same_loc G z x` by fs [same_loc]
    \\ fs [wf_co_total_def, is_total, GSYM same_loc,
           pred_setTheory.SPECIFICATION]
    \\ qpat_x_assum `!a b. p /\ q ==> r` (qspecl_then [`z`, `x`] assume_tac)
    \\ rfs []
    >- (
      xfs [delift]
      \\ metis_tac [relationTheory.transitive_def,
                    relationTheory.irreflexive_def]
    )
    \\ `fr G y z` by (xsimp [fr] \\ metis_tac [])
    \\ qpat_x_assum `irreflexive gcb` mp_tac
    \\ simp [relationTheory.irreflexive_def]
    \\ qexists_tac `erln G z`
    \\ qpat_x_assum `transitive gcb`
         (match_mp_tac o SIMP_RULE std_ss [relationTheory.transitive_def])
    \\ HINT_EXISTS_TAC
    \\ simp []
    \\ qpat_x_assum `p RSUBSET cb`
           (match_mp_tac o SIMP_RULE std_ss [relationTheory.RSUBSET])
    \\ match_mp_tac relationTheory.TC_SUBSET
    \\ xsimp [lift]
    \\ metis_tac []
  )
  \\ xrw [intervening_write, delift]
  \\ rfs [erln_refl2, wf_rfE_def, wf_rfD_def]
  \\ qmatch_rename_tac `G.rf x y`
  \\ `?z. G.rf z y` by (xfs [complete] \\ metis_tac [])
  \\ `acts_set G z /\ W G z` by (xfs [] \\ metis_tac [])
  \\ Cases_on `z = x`
  \\ fs []
  \\ spose_not_then kall_tac
  \\ `same_loc G x z` by xfs [wf_rfl_def, same_loc]
  \\ rfs [wf_co_total_def, is_total, GSYM same_loc,
          pred_setTheory.SPECIFICATION]
  \\ qpat_x_assum `!a b. p /\ q ==> xx` (qspecl_then [`z`, `x`] assume_tac)
  \\ rfs []
  >- (
    qpat_x_assum `irreflexive gcb` mp_tac
    \\ simp [relationTheory.irreflexive_def]
    \\ qsuff_tac
         `?x y.
           gcb x y /\
           (lift (erln G)
             (im0 G RUNION G.rf RUNION G.co RUNION fr G RUNION
              obs G ⨾ si G RUNION lob G RINTER gc_req G RUNION scaob G)) y x`
    >- (
      xfs []
      \\ metis_tac [relationTheory.TC_SUBSET, relationTheory.transitive_def]
    )
    \\ xsimp [lift, fr]
    \\ metis_tac []
  )
  \\ `same_loc G z y` by fs [same_loc]
  \\ qpat_x_assum `!y. p` (qspec_then `z` strip_assume_tac)
  \\ pop_assum mp_tac
  \\ simp []
  \\ qpat_x_assum `TC xx RSUBSET gcb` (match_mp_tac o SIMP_RULE (rel_ss()) [])
  \\ (
    simple_cond_rewr ct_lift
    >- (
      simp [refl, erln_sym, erln_trans]
      \\ metis_tac [erln_refl3]
    )
    \\ xrw [Once relationTheory.TC_CASES1]
    \\ metis_tac [erln_refl]
  )
QED

Theorem scaob_aob:
  WellFormed G ==> scaob G ⨾ aob G RSUBSET lob G RINTER gc_req G
Proof
  rw [aob, gc_req, seq_runion_r, GSYM W_ex]
  \\ `scaob G RSUBSET diag (RRANGE (rfe G)) ⨾ si G` by xsimp [scaob, ER, IR]
  \\ pop_assum (gen_rewrite (1, 0))
  \\ simp [si_rmw, seq_assoc]
  \\ imp_res_tac rmw_in_lws
  \\ pop_assum rewrite
  \\ rw [runion_rsubset]
  >- (
    xrw [lob, Once relationTheory.TC_CASES1]
    \\ xfs [Once wf_lwsD]
  )
  \\ simp [scaob, ER, IR, seq_assoc, Once wf_rfiD]
  \\ imp_res_tac wf_rfiD
  \\ pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
  \\ imp_res_tac W_ex_in_W
  \\ imp_res_tac diag_rsubset
  \\ pop_assum rewrite
  \\ xrw []
  \\ metis_tac [label_distinct]
QED

Theorem si_dob:
  WellFormed G ==> si G ⨾ dob G RSUBSET dob G
Proof
  rw [dob, scaob, seq_runion_l, seq_runion_r]
  \\ metis_tac [seq_assoc, si_data, si_ctrl, si_addr, rsubset_refl]
QED

Theorem si_bob:
  WellFormed G ==> si G ⨾ bob G RSUBSET bob G
Proof
  rw [bob, scaob, diag_runion, seq_runion_l, seq_runion_r, GSYM seq_assoc,
      GSYM L_si, GSYM A_si, GSYM Q_si, GSYM W_si, GSYM R_si]
  \\ simp [Once seq_assoc, si_po]
  \\ rw [seq_assoc, runion_rsubset]
  \\ metis_tac [si_po, rsubset_runion, rsubset_refl, seq_assoc]
QED

Triviality scaob_lob_helper:
  WellFormed G ==>
  scaob G ⨾ (lob G RMINUS gc_req G) RSUBSET lob G RINTER gc_req G
Proof
  strip_tac
  \\ match_mp_tac rsubset_trans
  \\ qexists_tac `diag (RRANGE (rfe G)) ⨾ lob G`
  \\ reverse strip_tac
  >- (
    xsimp [Once wf_rfeD, gc_req]
    \\ metis_tac []
  )
  \\ `scaob G RSUBSET diag (RRANGE (rfe G)) ⨾ si G ⨾ diag (RRANGE (rfi G))`
  by xsimp [scaob, ER, IR]
  \\ pop_assum rewrite
  \\ simp [seq_assoc]
  \\ match_mp_tac inclusion_seq_mon
  \\ simp [Once lob, Once ct_begin]
  \\ `RTC (lws G ⨾ si G RUNION dob G RUNION aob G RUNION bob G) RSUBSET
      RC (lob G)`
  by simp [lob, relationTheory.TC_RC_EQNS]
  \\ pop_assum rewrite
  \\ simp [seq_runion_l, rminus_runion_l, seq_runion_r, seq_assoc]
  \\ rw [runion_rsubset]
  >- (
    simp [lws, gc_req, Once wf_rfiD]
    \\ imp_res_tac wf_rfiD
    \\ pop_assum (fn th => CONV_TAC (PATH_CONV "lrrr" (ONCE_REWRITE_CONV [th])))
    \\ xrw [po_loc, rc_runion]
    \\ spose_not_then kall_tac
    \\ pop_assum mp_tac
    \\ simp []
    \\ qmatch_assum_rename_tac `rfi G v w`
    \\ qmatch_assum_rename_tac `same_loc G w u`
    \\ qexists_tac `v`
    \\ simp []
    \\ TRY (
      qmatch_assum_rename_tac `lob G z y`
      \\ simp [lob]
      \\ match_mp_tac (CONJUNCT2 (Q.SPEC `r` relationTheory.TC_RULES))
      \\ qexists_tac `z`
      \\ reverse strip_tac
      >- xfs [lob]
    )
    \\ xsimp [lob, Once relationTheory.TC_CASES1]
    \\ ntac 4 disj1_tac
    \\ qexists_tac `u`
    \\ simp []
    \\ xfs [rfi, lws, po_loc]
    \\ (
      strip_tac
      >- metis_tac [po_trans, relationTheory.transitive_def]
      \\ xfs [WellFormed, wf_rfl_def, same_loc]
      \\ metis_tac []
    )
  )
  >- (
    left_rewrite inclusion_seq_eqv_l
    \\ left_rewrite inclusion_minus_rel
    \\ imp_res_tac si_dob
    \\ simp [GSYM seq_assoc]
    \\ pop_assum rewrite
    \\ `dob G RSUBSET lob G`
    by metis_tac [lob, rsubset_tc, rsubset_runion, rsubset_refl]
    \\ pop_assum left_rewrite
    \\ xrw [lob, rc_runion]
    \\ metis_tac [relationTheory.TC_RULES]
  )
  >- (
    simp [aob, gc_req, GSYM W_ex]
    \\ left_rewrite inclusion_minus_rel
    \\ simp [seq_runion_l, seq_runion_r]
    \\ gen_rewrite (1, 0) inclusion_seq_eqv_l
    \\ simp [GSYM seq_assoc, si_rmw]
    \\ imp_res_tac rmw_in_lws
    \\ pop_assum rewrite
    \\ `lws G ⨾ si G RSUBSET lob G`
    by metis_tac [lob, rsubset_tc, rsubset_runion, rsubset_refl]
    \\ pop_assum left_rewrite
    \\ rw [runion_rsubset]
    >- (
      xrw [lob, rc_runion]
      \\ metis_tac [relationTheory.TC_RULES]
    )
    \\ imp_res_tac wf_rfiD
    \\ pop_assum SUBST1_TAC
    \\ imp_res_tac W_ex_in_W
    \\ imp_res_tac diag_rsubset
    \\ pop_assum rewrite
    \\ xrw [rc_runion]
    \\ metis_tac [label_distinct]
  )
  \\ left_rewrite inclusion_seq_eqv_l
  \\ left_rewrite inclusion_minus_rel
  \\ imp_res_tac si_bob
  \\ simp [GSYM seq_assoc]
  \\ pop_assum rewrite
  \\ `bob G RSUBSET lob G`
  by metis_tac [lob, rsubset_tc, rsubset_runion, rsubset_refl]
  \\ pop_assum left_rewrite
  \\ xrw [lob, rc_runion]
  \\ metis_tac [relationTheory.TC_RULES]
QED

Theorem scaob_lob:
  WellFormed G ==> scaob G ⨾ lob G RSUBSET RC (scaob G) ⨾ lob G RINTER gc_req G
Proof
  strip_tac
  \\ `lob G RSUBSET (lob G RINTER gc_req G RUNION lob G RMINUS gc_req G)`
  by xsimp []
  \\ pop_assum rewrite
  \\ simp [seq_runion_r]
  \\ imp_res_tac scaob_lob_helper
  \\ pop_assum left_rewrite
  \\ xsimp [rc_runion]
  \\ metis_tac []
QED

Triviality transitive_tc_delift_erln:
  transitive gcb ==>
  !x y. TC (delift (erln G) gcb) x y ==> gcb (erln G x) (erln G y)
Proof
  strip_tac
  \\ ho_match_mp_tac relationTheory.TC_INDUCT
  \\ rw [delift]
  \\ metis_tac [relationTheory.transitive_def]
QED

Triviality transitive_tc_delift_erln_lob:
  lift (erln G)
    (im0 G RUNION lob G RINTER gc_req G RUNION scaob G) RSUBSET gcb /\
  transitive gcb ==>
  !x y.
    TC (TC (delift (erln G) gcb) ⨾ lob G RINTER gc_req G) x y ==>
    gcb (erln G x) (erln G y)
Proof
  strip_tac
  \\ ho_match_mp_tac relationTheory.TC_INDUCT
  \\ xrw [delift]
  >- (
    qpat_assum `transitive gcb`
      (match_mp_tac o SIMP_RULE std_ss [relationTheory.transitive_def])
    \\ qmatch_assum_rename_tac `gc_req G z y`
    \\ qexists_tac `erln G z`
    \\ strip_tac
    >- (
      ntac 2 (pop_assum kall_tac)
      \\ qmatch_rename_tac `gcb (erln G x) (erln G z)`
      \\ pop_assum mp_tac
      \\ Q.SPEC_TAC (`z`, `z`)
      \\ Q.SPEC_TAC (`x`, `x`)
      \\ ho_match_mp_tac relationTheory.TC_INDUCT
      \\ rw [delift]
      \\ metis_tac [relationTheory.transitive_def]
    )
    \\ qpat_x_assum `lift (erln G) p RSUBSET gcb`
         (match_mp_tac o SIMP_RULE (rel_ss()) [])
    \\ xsimp [lift]
    \\ metis_tac [erln_refl1]
  )
  \\ metis_tac [relationTheory.transitive_def]
QED

Theorem ArmConsistentGlobExtComp_equiv:
  arm_ev = arm_egc
Proof
  simp [FUN_EQ_THM]
  \\ Q.X_GEN_TAC `G`
  \\ eq_tac
  >- simp [ArmConsistent_implies_GlobExtComp]
  \\ rw [arm_ev, arm_egc, external_global, linearization_of,
         preorder_gcb_lift, preorder_gcb, MC, dgcbl, rf_gcb, co_gcb]
  \\ fs [arm_common, external, strict_total_order, relationTheory.StrongOrder]
  \\ wf_tac [] []
  \\ `obs G RSUBSET delift (erln G) gcb`
  by (
    xrw [obs, rfe, coe, fre, fr, delift, dgcbl, intervening_write]
    \\ simp []
    \\ qmatch_rename_tac `gcb (erln G x) (erln G y)`
    \\ qmatch_assum_rename_tac `same_loc G z y`
    \\ `classes (erln G) (erln G x) /\ classes (erln G) (erln G y)`
    by (xsimp [classes] \\ metis_tac [])
    \\ `erln G x <> erln G y`
    by (
      strip_tac
      \\ assume_tac erln_in_si
      \\ xfs [wf_siD_def]
      \\ `si_matching_label (G.lab y) (G.lab x)` by metis_tac []
      \\ Cases_on `G.lab x`
      \\ Cases_on `G.lab y`
      \\ gs [si_matching_label, is_w, is_r]
    )
    \\ fs [is_total, pred_setTheory.SPECIFICATION]
    \\ qpat_x_assum `!a b. p` (qspecl_then [`erln G x`, `erln G y`] assume_tac)
    \\ rfs []
    \\ qpat_x_assum `!y. p` (qspec_then `y` strip_assume_tac)
    \\ fs [same_loc]
  )
  \\ `obs G ⨾ si G RSUBSET delift (erln G) gcb`
  by (
    simp [obs_si_scaob]
    \\ pop_assum left_rewrite
    \\ rw [runion_rsubset]
    >- (
      xrw [delift]
      \\ metis_tac [erln_rewrite, erln_trans, erln_sym,
                    relationTheory.symmetric_def, relationTheory.transitive_def]
    )
    \\ xrw [rfe, delift, intervening_write]
    \\ simp []
    >- (
      qpat_x_assum `transitive gcb`
        (match_mp_tac o SIMP_RULE std_ss [relationTheory.transitive_def])
      \\ HINT_EXISTS_TAC
      \\ simp []
      \\ qpat_x_assum `xx RSUBSET gcb`
           (match_mp_tac o SIMP_RULE (rel_ss()) [])
      \\ xsimp [lift]
      \\ metis_tac []
    )
    \\ xfs [scaob, ER, IR, Once wf_siE, erln_refl]
  )
  \\ `transitive (lob G)` by simp [lob]
  \\ rw [acyclic_ut]
  \\ pop_assum kall_tac
  >- (
    pop_assum rewrite
    \\ simp [acyclic, relationTheory.irreflexive_def]
    \\ rpt strip_tac
    \\ qpat_x_assum `irreflexive gcb` mp_tac
    \\ simp [relationTheory.irreflexive_def]
    \\ metis_tac [transitive_tc_delift_erln]
  )
  >- (
    imp_res_tac lob_in_po
    \\ assume_tac po_irr
    \\ xfs []
    \\ metis_tac [relationTheory.irreflexive_def]
  )
  \\ simp [Once acyclic_seqC, ct_end, seq_assoc]
  \\ `obs G ⨾ si G ⨾ lob G RSUBSET obs G ⨾ si G ⨾ lob G RINTER gc_req G`
  by (
    simp [GSYM seq_assoc, Once obs_si_scaob, seq_runion_l]
    \\ simp [seq_assoc]
    \\ imp_res_tac scaob_lob
    \\ pop_assum rewrite
    \\ rw [runion_rsubset]
    >- (
      simp [obs, gc_req, erln, rfisw, ER,
            Once wf_rfeD, Once wf_coeD, Once wf_freD]
      \\ fs [wf_siD_def, wf_rff_def, functional]
      \\ xrw []
      \\ TRY (metis_tac [label_distinct, si_refl])
      \\ xfs [rfe, rfi]
      \\ metis_tac [si_refl]
    )
    \\ simp [Once wf_rfeE, GSYM seq_assoc]
    \\ gen_rewrite (1, 0) inclusion_seq_eqv_l
    \\ simp [seq_assoc]
    \\ match_mp_tac inclusion_seq_mon
    \\ strip_tac
    >- xsimp [obs]
    \\ simp [GSYM seq_assoc]
    \\ match_mp_tac inclusion_seq_mon
    \\ xrw [rc_runion, scaob]
    \\ simp [si_refl]
  )
  \\ pop_assum rewrite
  \\ qsuff_tac
       `acyclic ((RTC (obs G ⨾ si G) ⨾ (obs G ⨾ si G)) ⨾ lob G RINTER gc_req G)`
  >- simp [seq_assoc]
  \\ simp [GSYM ct_end]
  \\ pop_assum rewrite
  \\ rw [acyclic, relationTheory.irreflexive_def]
  \\ strip_tac
  \\ qpat_x_assum `irreflexive gcb` mp_tac
  \\ simp [relationTheory.irreflexive_def]
  \\ metis_tac [transitive_tc_delift_erln_lob]
QED

(* -------------------------------------------------------------------------
   End
   ------------------------------------------------------------------------- *)

val () = export_theory()
