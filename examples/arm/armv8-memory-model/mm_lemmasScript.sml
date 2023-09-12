open HolKernel boolLib bossLib
open relation_extraTheory mmTheory
open relation_extraLib

val () = new_theory "mm_lemmas"

(* -------------------------------------------------------------------------
   Helper tactics
   ------------------------------------------------------------------------- *)

fun wf_tac thms =
  strip_tac
  \\ qpat_assum `WellFormed G`
       (strip_assume_tac o SIMP_RULE (srw_ss()) (WellFormed::thms))

local
  fun dom_tac th thm =
    let
      val tm = thm |> SPEC_ALL |> concl |> lhs
      fun tac th = CONV_TAC (LAND_CONV (DEPTH_CONV (REWR_CONV th)))
    in
      PAT_X_ASSUM tm (tac o MATCH_MP th o SIMP_RULE std_ss [thm])
    end
in
  val dom_l_tac = dom_tac dom_l
  val dom_r_tac = dom_tac dom_r
end

(* -------------------------------------------------------------------------
   Theorems
   ------------------------------------------------------------------------- *)

Theorem label_distinct:
  ~(R G x /\ W G x) /\
  ~(R G x /\ Fence G x) /\
  ~(R G x /\ Br G x) /\
  ~(W G x /\ Fence G x) /\
  ~(W G x /\ Br G x) /\
  ~(Fence G x /\ Br G x)
Proof
  simp [is_r, is_w, is_f, is_br]
  \\ Cases_on `G.lab x`
  \\ simp []
QED

(* - same tid -------------------------------------------------------------- *)

Theorem loceq_same_tid:
  funeq tid r <=> r RSUBSET r RINTER same_tid
Proof
  xsimp [funeq, same_tid]
QED

(* - labels ---------------------------------------------------------------- *)

Theorem lab_rwf:
  is_r lab a \/ is_w lab a \/ is_f lab a \/ is_br lab a
Proof
  Cases_on `lab a` \\ simp [is_r, is_w, is_f, is_br]
QED

Theorem R_ex_in_R:
  R_ex lab SUBSET is_r lab
Proof
  xsimp [R_ex, is_r]
  \\ Q.X_GEN_TAC `x`
  \\ Cases_on `lab x`
  \\ simp []
QED

(* - same loc -------------------------------------------------------------- *)

Theorem loceq_same_loc:
  funeq (loc G) r <=> r RSUBSET r RINTER (same_loc G)
Proof
  xsimp [funeq, same_loc]
QED

Theorem same_loc_trans:
  transitive (same_loc lab)
Proof
  simp [relationTheory.transitive_def, same_loc]
QED

Theorem same_loc_sym:
  symmetric (same_loc lab)
Proof
  metis_tac [relationTheory.symmetric_def, same_loc]
QED

(* - values and location getters ------------------------------------------- *)

Theorem is_w_val:
  is_w lab x ==> ?v. value lab x = SOME v
Proof
  rw [is_w, value] \\ Cases_on `lab x` \\ fs []
QED

Theorem is_w_loc:
  is_w lab x ==> ?v. loc lab x = SOME v
Proof
  rw [is_w, loc] \\ Cases_on `lab x` \\ fs []
QED

Theorem is_r_val:
  is_r lab x ==> ?v. value lab x = SOME v
Proof
  rw [is_r, value] \\ Cases_on `lab x` \\ fs []
QED

Theorem is_r_loc:
  is_r lab x ==> ?v. loc lab x = SOME v
Proof
  rw [is_r, loc] \\ Cases_on `lab x` \\ fs []
QED

(* - Sequenced-Before ------------------------------------------------------ *)

Theorem ext_sb_trans:
  transitive ext_sb
Proof
  simp [relationTheory.transitive_def, ext_sb]
  \\ ntac 3 Cases
  \\ simp []
QED

Theorem ext_sb_irr:
  irreflexive ext_sb
Proof
  simp [relationTheory.irreflexive_def, ext_sb]
  \\ Cases
  \\ simp []
QED

Theorem ext_sb_to_non_init:
  ext_sb RSUBSET (ext_sb ⨾ diag (\x. ~is_init x))
Proof
  xsimp [ext_sb, is_init]
  \\ ntac 2 Cases
  \\ simp []
QED

Theorem ext_sb_semi_total_l:
  ~is_init x /\ index y <> index z /\ ext_sb x y /\ ext_sb x z ==>
  ext_sb y z \/ ext_sb z y
Proof
  simp [is_init, index, ext_sb]
  \\ MAP_EVERY Cases_on [`x`, `y`, `z`]
  \\ simp []
QED

Theorem ext_sb_semi_total_r:
  index y <> index z /\ ext_sb y x /\ ext_sb z x ==> ext_sb y z \/ ext_sb z y
Proof
  simp [is_init, index, ext_sb]
  \\ MAP_EVERY Cases_on [`x`, `y`, `z`]
  \\ simp []
QED

Theorem ext_sb_tid_init:
  ext_sb x y ==> tid x = tid y \/ is_init x
Proof
  simp [is_init, tid, ext_sb]
  \\ MAP_EVERY Cases_on [`x`, `y`]
  \\ simp []
QED

Theorem ext_sb_tid_init':
  ext_sb RSUBSET (ext_sb RINTER same_tid RUNION (diag is_init ⨾ ext_sb))
Proof
  xsimp [same_tid, ext_sb_tid_init]
QED

(* - Same Instruction ------------------------------------------------------ *)

Theorem ext_si_refl:
  reflexive ext_si
Proof
  simp [relationTheory.reflexive_def, ext_si]
  \\ Cases
  \\ simp []
QED

Theorem ext_si_sym:
  symmetric ext_si
Proof
  simp [relationTheory.symmetric_def, ext_si]
  \\ ntac 2 Cases
  \\ simp []
QED

Theorem ext_si_trans:
  transitive ext_si
Proof
  simp [relationTheory.transitive_def, ext_si]
  \\ ntac 2 Cases
  \\ simp []
QED

(* - is_init properties ---------------------------------------------------- *)

Theorem is_init_tid:
  is_init SUBSET (\x. tid x = tid_init)
Proof
  xsimp [is_init, tid]
  \\ Cases
  \\ simp []
QED

Theorem initninit_in_ext_sb:
  (is_init RCROSS COMPL is_init) RSUBSET ext_sb
Proof
  xsimp [ext_sb]
  \\ ntac 2 Cases
  \\ simp [pred_setTheory.SPECIFICATION, is_init]
QED

(* - Basic transitivity properties ----------------------------------------- *)

Theorem po_trans:
  transitive (po G)
Proof
  metis_tac [po, diag_trans, seq_diag_trans_l, seq_diag_trans_r, ext_sb_trans]
QED

Theorem po_po:
  po G ⨾ po G RSUBSET po G
Proof
  xsimp []
  \\ metis_tac [po_trans, relationTheory.transitive_def]
QED

Theorem po_same_loc_trans:
  transitive (po G RINTER same_loc G)
Proof
  metis_tac [relationTheory.transitive_RINTER, po_trans, same_loc_trans]
QED

Theorem po_same_loc_W_trans:
  transitive ((po G RINTER same_loc G) ⨾ diag (W G))
Proof
  metis_tac [seq_diag_trans_r, po_trans, same_loc_trans,
             relationTheory.transitive_RINTER]
QED

(* - Basic properties ------------------------------------------------------ *)

Theorem po_neq_loc_in_po:
  po G RMINUS same_loc G RSUBSET po G
Proof
  xsimp []
QED

Theorem fr_co:
  WellFormed G ==> ((fr G ⨾ G.co) RSUBSET (fr G))
Proof
  wf_tac [co_trans_def]
  \\ xfs [fr]
  \\ metis_tac [relationTheory.transitive_def]
QED

Theorem rmw_in_po:
  WellFormed G ==> (rmw G RSUBSET (po G))
Proof
  wf_tac [wf_rmwi_def]
  \\ xfs [relation_extraTheory.immediate]
QED

Theorem deps_in_po:
  WellFormed G ==> (deps G RSUBSET (po G))
Proof
  wf_tac [data_in_po_def, addr_in_po_def, ctrl_in_po_def]
  \\ simp [deps, runion_rsubset]
QED

Theorem amo_in_po:
  WellFormed G ==> (G.amo RSUBSET (po G))
Proof
  metis_tac [rmw_in_po, rmw, runion_rsubset]
QED

Theorem lxsx_in_po:
  WellFormed G ==> (G.lxsx RSUBSET (po G))
Proof
  metis_tac [rmw_in_po, rmw, runion_rsubset]
QED

(* - Same Location relations ----------------------------------------------- *)

Theorem loceq_rf:
  WellFormed G ==> funeq (loc G) G.rf
Proof
  wf_tac [wf_rfl_def]
  \\ xfs [same_loc, funeq]
QED

Theorem loceq_co:
  WellFormed G ==> funeq (loc G) G.co
Proof
  wf_tac [wf_col_def]
  \\ xfs [same_loc, funeq]
QED

Theorem loceq_rmw:
  WellFormed G ==> funeq (loc G) (rmw G)
Proof
  wf_tac [wf_rmwl_def]
  \\ xfs [same_loc, funeq]
QED

Theorem loceq_fr:
  WellFormed G ==> funeq (loc G) (fr G)
Proof
  xsimp [fr, funeq]
  \\ metis_tac [funeq, loceq_co, loceq_rf]
QED

Theorem wf_frl:
  WellFormed G ==> fr G RSUBSET same_loc G
Proof
  wf_tac [wf_rfl_def, wf_col_def]
  \\ xfs [fr, same_loc]
  \\ metis_tac []
QED

(* - Relations in graph ---------------------------------------------------- *)

Theorem wf_poE:
  po G = diag (E G) ⨾ po G ⨾ diag (E G)
Proof
  xrw [doms_helper, po]
QED

Theorem wf_dataE:
  WellFormed G ==> (G.data = diag (E G) ⨾ G.data ⨾ diag (E G))
Proof
  wf_tac [data_in_po_def]
  \\ xfs [Once wf_poE]
  \\ metis_tac []
QED

Theorem wf_addrE:
  WellFormed G ==> (G.addr = diag (E G) ⨾ G.addr ⨾ diag (E G))
Proof
  wf_tac [addr_in_po_def]
  \\ xfs [Once wf_poE]
  \\ metis_tac []
QED

Theorem wf_ctrlE:
  WellFormed G ==> (G.ctrl = diag (E G) ⨾ G.ctrl ⨾ diag (E G))
Proof
  wf_tac [ctrl_in_po_def]
  \\ xfs [Once wf_poE]
  \\ metis_tac []
QED

Theorem wf_depsE:
  WellFormed G ==> (deps G = diag (E G) ⨾ deps G ⨾ diag (E G))
Proof
  strip_tac
  \\ imp_res_tac deps_in_po
  \\ xfs [Once wf_poE]
  \\ metis_tac []
QED

Theorem wf_amoE:
  WellFormed G ==> (G.amo = diag (E G) ⨾ G.amo ⨾ diag (E G))
Proof
  strip_tac
  \\ imp_res_tac amo_in_po
  \\ xfs [Once wf_poE]
  \\ metis_tac []
QED

Theorem wf_lxsxE:
  WellFormed G ==> (G.lxsx = diag (E G) ⨾ G.lxsx ⨾ diag (E G))
Proof
  strip_tac
  \\ imp_res_tac lxsx_in_po
  \\ xfs [Once wf_poE]
  \\ metis_tac []
QED

Theorem wf_rmwE:
  WellFormed G ==> (rmw G = diag (E G) ⨾ rmw G ⨾ diag (E G))
Proof
  strip_tac
  \\ imp_res_tac rmw_in_po
  \\ xfs [Once wf_poE]
  \\ metis_tac []
QED

Theorem wf_frE:
  WellFormed G ==> (fr G = diag (E G) ⨾ fr G ⨾ diag (E G))
Proof
  wf_tac [wf_rfE_def, wf_coE_def]
  \\ xfs [fr]
  \\ metis_tac []
QED

Theorem wf_siE:
  si G = diag (E G) ⨾ si G ⨾ diag (E G)
Proof
  xsimp [si, doms_helper]
QED

(* - Domains and codomains ------------------------------------------------- *)

Theorem wf_frD:
  WellFormed G ==> (fr G = diag (R G) ⨾ fr G ⨾ diag (W G))
Proof
  wf_tac [wf_rfD_def, wf_coD_def]
  \\ match_mp_tac doms_helper
  \\ xfs [fr]
  \\ metis_tac []
QED

Theorem wf_depsD:
  WellFormed G ==> (deps G = diag (R G) ⨾ deps G)
Proof
  wf_tac [wf_dataD_def, wf_ctrlD_def, wf_addrD_def]
  \\ xfs [deps]
  \\ metis_tac []
QED

(* - Irreflexive relations ------------------------------------------------- *)

Theorem po_irr:
  irreflexive (po G)
Proof
  xsimp [relationTheory.irreflexive_def, po]
  \\ metis_tac [relationTheory.irreflexive_def, ext_sb_irr]
QED

Theorem fr_irr:
  WellFormed G ==> irreflexive (fr G)
Proof
  xsimp [Once wf_frD, relationTheory.irreflexive_def, fr]
  \\ metis_tac [label_distinct]
QED

(* - Same instruction ------------------------------------------------------ *)

Theorem si_po:
  si G ⨾ po G = po G
Proof
  xrw [si, po]
  \\ eq_tac
  \\ rw []
  \\ simp []
  >- (
    qmatch_rename_tac `ext_sb x z`
    \\ qmatch_assum_rename_tac `ext_sb y z`
    \\ MAP_EVERY Cases_on [`x`, `y`, `z`]
    \\ fs [ext_si, ext_sb]
  )
  \\ metis_tac [ext_si_refl, relationTheory.reflexive_def]
QED

Theorem po_si:
  po G ⨾ si G = po G
Proof
  xrw [FUN_EQ_THM, si, po]
  \\ eq_tac
  \\ rw []
  \\ simp []
  >- (
    qmatch_rename_tac `ext_sb x z`
    \\ qmatch_assum_rename_tac `ext_si y z`
    \\ MAP_EVERY Cases_on [`x`, `y`, `z`]
    \\ fs [ext_si, ext_sb]
  )
  \\ metis_tac [ext_si_refl, relationTheory.reflexive_def]
QED

Theorem si_refl:
  E G x ==> si G x x
Proof
  xsimp [si]
  \\ metis_tac [ext_si_refl, relationTheory.reflexive_def]
QED

Theorem si_sym:
  symmetric (si G)
Proof
  xsimp [si, relationTheory.symmetric_def]
  \\ metis_tac [ext_si_sym, relationTheory.symmetric_def]
QED

Theorem si_trans:
  transitive (si G)
Proof
  xsimp [si, relationTheory.transitive_def]
  \\ metis_tac [ext_si_trans, relationTheory.transitive_def]
QED

Theorem si_si:
  si G ⨾ si G = si G
Proof
  xrw [si]
  \\ eq_tac
  \\ rw []
  \\ simp []
  >- (
    qmatch_rename_tac `ext_si x z`
    \\ qmatch_assum_rename_tac `ext_si y z`
    \\ MAP_EVERY Cases_on [`x`, `y`, `z`]
    \\ fs [ext_si, ext_sb]
  )
  \\ metis_tac [ext_si_refl, relationTheory.reflexive_def]
QED

Theorem si_rmw:
  WellFormed G ==> si G ⨾ rmw G = rmw G ⨾ si G
Proof
  wf_tac [si_amo_def, si_lxsx_def]
  \\ simp [rmw, seq_runion_l, seq_runion_r]
QED

val si_tac =
  wf_tac [wf_si_addr_def, wf_si_ctrl_def, wf_si_data_def]
  \\ simp [Once wf_addrE, Once wf_ctrlE, Once wf_dataE]
  \\ simp [SimpRHS, Once wf_addrE, Once wf_ctrlE, Once wf_dataE]
  \\ assume_tac (GEN_ALL si_refl)
  \\ xfs [si]
  \\ metis_tac []

Theorem addr_si:
  WellFormed G ==> G.addr ⨾ si G = G.addr
Proof
  si_tac
QED

Theorem si_addr:
  WellFormed G ==> si G ⨾ G.addr = G.addr
Proof
  si_tac
QED

Theorem ctrl_si:
  WellFormed G ==> G.ctrl ⨾ si G = G.ctrl
Proof
  si_tac
QED

Theorem si_ctrl:
  WellFormed G ==> si G ⨾ G.ctrl = G.ctrl
Proof
  si_tac
QED

Theorem data_si:
  WellFormed G ==> G.data ⨾ si G = G.data
Proof
  si_tac
QED

Theorem si_data:
  WellFormed G ==> si G ⨾ G.data = G.data
Proof
  si_tac
QED

Theorem W_si:
  WellFormed G ==> diag (W G) ⨾ si G = si G ⨾ diag (W G)
Proof
  wf_tac [wf_siD_def]
  \\ xrw []
  \\ qmatch_goalsub_rename_tac `si G x y`
  \\ Cases_on `si G x y`
  \\ simp []
  \\ res_tac
  \\ Cases_on `G.lab x`
  \\ Cases_on `G.lab y`
  \\ fs [si_matching_label, is_w]
QED

Theorem R_si:
  WellFormed G ==> diag (R G) ⨾ si G = si G ⨾ diag (R G)
Proof
  wf_tac [wf_siD_def]
  \\ xrw []
  \\ qmatch_goalsub_rename_tac `si G x y`
  \\ Cases_on `si G x y`
  \\ simp []
  \\ res_tac
  \\ Cases_on `G.lab x`
  \\ Cases_on `G.lab y`
  \\ fs [si_matching_label, is_r]
QED

(* - Acyclic relations ----------------------------------------------------- *)

Theorem po_acyclic0:
  acyclic (po G)
Proof
  metis_tac [po_irr, po_trans, relation_extraTheory.acyclic,
             relationTheory.transitive_TC_identity]
QED

Theorem po_acyclic:
  WellFormed G ==> acyclic G.co
Proof
  rw [WellFormed, co_irr_def, co_trans_def]
  \\ metis_tac [relation_extraTheory.acyclic,
                relationTheory.transitive_TC_identity]
QED

(* - init ------------------------------------------------------------------ *)

Theorem init_w:
  WellFormed G ==> is_init SUBSET W G
Proof
  wf_tac [wf_init_lab_def]
  \\ xrw [is_w, is_init]
  \\ rename1 `G.lab x`
  \\ Cases_on `x`
  \\ fs []
QED

Theorem read_or_fence_is_not_init:
  WellFormed G /\ (R G a \/ Fence G a) ==> ~is_init a
Proof
  rpt strip_tac
  \\ imp_res_tac init_w
  \\ xfs [is_r, is_w, is_f]
  \\ res_tac
  \\ Cases_on `G.lab a`
  \\ fs []
QED

Theorem no_po_to_init:
  po G = (po G ⨾ diag (\x. ~is_init x))
Proof
  mp_tac ext_sb_to_non_init
  \\ xsimp [po]
  \\ metis_tac []
QED

Theorem no_rf_to_init:
  WellFormed G ==> G.rf = (G.rf ⨾ diag (\x. ~is_init x))
Proof
  wf_tac [wf_rfD_def]
  \\ assume_tac (Q.GEN `a` read_or_fence_is_not_init)
  \\ xfs []
  \\ metis_tac []
QED

Theorem rmw_from_non_init:
  WellFormed G ==> rmw G = diag (\x. ~is_init x) ⨾ rmw G
Proof
  wf_tac [wf_rmwD_def]
  \\ assume_tac (Q.GEN `a` read_or_fence_is_not_init)
  \\ xfs []
  \\ metis_tac []
QED

Theorem rmw_non_init_lr:
  WellFormed G ==> rmw G = diag (COMPL is_init) ⨾ rmw G ⨾ diag (COMPL is_init)
Proof
  strip_tac
  \\ MAP_EVERY mp_tac [rmw_from_non_init, rmw_in_po, no_po_to_init]
  \\ xrw []
  \\ metis_tac []
QED

Theorem init_same_loc:
  WellFormed G /\ is_init a /\ is_init b /\ loc G a = loc G b ==> a = b
Proof
  rw [WellFormed, wf_init_lab_def, is_init, loc]
  \\ Cases_on `a`
  \\ Cases_on `b`
  \\ rfs []
QED

(* - More properties ------------------------------------------------------- *)

Theorem po_semi_total_l:
  po G x y /\ po G x z ==>
  (is_init x /\ ~is_init y /\ ~is_init z \/
   po G y z \/
   po G z y \/
   si G y z)
Proof
  xsimp [po, si, ext_sb, ext_si, is_init]
  \\ MAP_EVERY Cases_on [`x`, `y`, `z`]
  \\ simp []
QED

Theorem po_semi_total_r:
  po G y x /\ po G z x ==>
  (po G y z \/
   po G z y \/
   is_init y /\ is_init z \/
   si G y z)
Proof
  xsimp [po, si, ext_sb, ext_si, is_init]
  \\ MAP_EVERY Cases_on [`x`, `y`, `z`]
  \\ simp []
QED

Theorem po_tid_init:
  po G x y ==> tid x = tid y \/ is_init x
Proof
  xsimp [po, tid, ext_sb, is_init]
  \\ Cases_on `x`
  \\ Cases_on `y`
  \\ simp []
QED

Theorem E_ntid_po_prcl:
  RDOM (diag (COMPL is_init) ⨾ po G ⨾ diag (E G INTER (\x. tid x <> t))) SUBSET
  (E G INTER (\x. tid x <> t))
Proof
  xsimp [relationTheory.RDOM_DEF, Once wf_poE]
  \\ metis_tac [po_tid_init]
QED

Theorem po_tid_init':
  po G = (po G RINTER same_tid) RUNION (diag is_init ⨾ po G)
Proof
  mp_tac ext_sb_tid_init'
  \\ xsimp [po]
  \\ metis_tac []
QED

Theorem ninit_po_same_tid:
  diag (COMPL is_init) ⨾ po G RSUBSET same_tid
Proof
  xrw [Once po_tid_init']
QED

Theorem same_tid_trans:
  transitive same_tid
Proof
  simp [relationTheory.transitive_def, same_tid]
QED

Theorem rf_rf:
  WellFormed G ==> G.rf ⨾ G.rf = REMPTY
Proof
  wf_tac [wf_rfD_def]
  \\ FIRST_ASSUM SUBST1_TAC
  \\ xsimp []
  \\ metis_tac [label_distinct]
QED

Theorem rf_co:
  WellFormed G ==> G.rf ⨾ G.co = REMPTY
Proof
  wf_tac [wf_rfD_def, wf_coD_def]
  \\ rpt (FIRST_X_ASSUM SUBST1_TAC)
  \\ xsimp []
  \\ metis_tac [label_distinct]
QED

Theorem co_transp_rf:
  WellFormed G ==> G.co ⨾ inv G.rf = REMPTY
Proof
  wf_tac [wf_rfD_def, wf_coD_def]
  \\ rpt (FIRST_X_ASSUM SUBST1_TAC)
  \\ xsimp []
  \\ metis_tac [label_distinct]
QED

Theorem co_fr:
  WellFormed G ==> G.co ⨾ fr G = REMPTY
Proof
  wf_tac [wf_coD_def]
  \\ imp_res_tac wf_frD
  \\ rpt (FIRST_X_ASSUM SUBST1_TAC)
  \\ xsimp []
  \\ metis_tac [label_distinct]
QED

Theorem fr_fr:
  WellFormed G ==> fr G ⨾ fr G = REMPTY
Proof
  strip_tac
  \\ imp_res_tac wf_frD
  \\ FIRST_X_ASSUM SUBST1_TAC
  \\ xsimp []
  \\ metis_tac [label_distinct]
QED

Theorem rf_transp_rf:
  WellFormed G ==> (G.rf ⨾ inv G.rf RSUBSET diag (K T))
Proof
  rw [WellFormed, wf_rff_def, functional_alt]
QED

Theorem rf_fr:
  WellFormed G ==> (G.rf ⨾ fr G RSUBSET G.co)
Proof
  wf_tac [wf_rff_def]
  \\ xfs [fr, functional]
  \\ metis_tac []
QED

Theorem rmw_in_po_loc:
  WellFormed G ==> rmw G RSUBSET po G RINTER (same_loc G)
Proof
  strip_tac
  \\ imp_res_tac loceq_rmw
  \\ imp_res_tac rmw_in_po
  \\ xfs [loceq_same_loc]
QED

Theorem rf_irr:
  WellFormed G ==> irreflexive G.rf
Proof
  wf_tac [wf_rfD_def]
  \\ FIRST_X_ASSUM SUBST1_TAC
  \\ xsimp [relationTheory.irreflexive_def]
  \\ metis_tac [label_distinct]
QED

Theorem co_co:
  WellFormed G ==> G.co ⨾ G.co RSUBSET G.co
Proof
  xsimp [WellFormed, co_trans_def, relationTheory.transitive_def]
QED

Theorem wf_rmwf:
  WellFormed G ==> functional (rmw G)
Proof
  wf_tac [wf_rmwi_def, wf_rmwl_def, wf_sil_def]
  \\ xfs [Once rmw_from_non_init, same_loc,
          relation_extraTheory.immediate, relation_extraTheory.functional]
  \\ metis_tac [po_semi_total_l]
QED

Theorem wf_rmw_invf:
  WellFormed G ==> functional (inv (rmw G))
Proof
  simp [Once rmw_from_non_init]
  \\ wf_tac [wf_rmwi_def, wf_rmwl_def, wf_sil_def]
  \\ xfs [relation_extraTheory.immediate, relation_extraTheory.functional,
          same_loc]
  \\ metis_tac [po_semi_total_r]
QED

(* - external-internal restrictions ---------------------------------------- *)

Theorem ri_union_re:
  r = r RINTER (po G) RUNION r RMINUS (po G)
Proof
  xsimp [po]
  \\ metis_tac []
QED

Theorem rfi_union_rfe:
  G.rf = rfi G RUNION rfe G
Proof
  metis_tac [ri_union_re, rfi, rfe]
QED

Theorem coi_union_coe:
  G.co = coi G RUNION coe G
Proof
  metis_tac [ri_union_re, coi, coe]
QED

Theorem fri_union_fre:
  fr G = fri G RUNION fre G
Proof
  metis_tac [ri_union_re, fri, fre]
QED

Theorem ri_dom:
  r = diag d1 ⨾ r ⨾ diag d2 ==>
  r RINTER po G RSUBSET diag d1 ⨾ (r RINTER po G) ⨾ diag d2
Proof
  strip_tac
  \\ pop_assum SUBST1_TAC
  \\ xsimp []
QED

Theorem re_dom:
  r = diag d1 ⨾ r ⨾ diag d2 ==>
  r RMINUS po G RSUBSET diag d1 ⨾ (r RMINUS po G) ⨾ diag d2
Proof
  strip_tac
  \\ pop_assum SUBST1_TAC
  \\ xsimp []
QED

Theorem wf_rfiE:
  WellFormed G ==> rfi G = diag (E G) ⨾ rfi G ⨾ diag (E G)
Proof
  wf_tac [wf_rfE_def]
  \\ imp_res_tac ri_dom
  \\ xfs [rfi]
  \\ metis_tac []
QED

Theorem wf_coiE:
  WellFormed G ==> coi G = diag (E G) ⨾ coi G ⨾ diag (E G)
Proof
  wf_tac [wf_coE_def]
  \\ imp_res_tac ri_dom
  \\ xfs [coi]
  \\ metis_tac []
QED

Theorem wf_friE:
  WellFormed G ==> fri G = diag (E G) ⨾ fri G ⨾ diag (E G)
Proof
  strip_tac
  \\ imp_res_tac wf_frE
  \\ imp_res_tac ri_dom
  \\ xfs [fri]
  \\ metis_tac []
QED

Theorem wf_rfeE:
  WellFormed G ==> rfe G = diag (E G) ⨾ rfe G ⨾ diag (E G)
Proof
  wf_tac [wf_rfE_def]
  \\ imp_res_tac re_dom
  \\ xfs [rfe]
  \\ metis_tac []
QED

Theorem wf_coeE:
  WellFormed G ==> coe G = diag (E G) ⨾ coe G ⨾ diag (E G)
Proof
  wf_tac [wf_coE_def]
  \\ imp_res_tac re_dom
  \\ xfs [coe]
  \\ metis_tac []
QED

Theorem wf_freE:
  WellFormed G ==> fre G = diag (E G) ⨾ fre G ⨾ diag (E G)
Proof
  strip_tac
  \\ imp_res_tac wf_frE
  \\ imp_res_tac re_dom
  \\ xfs [fre]
  \\ metis_tac []
QED

Theorem wf_rfiD:
  WellFormed G ==> rfi G = diag (W G) ⨾ rfi G ⨾ diag (R G)
Proof
  wf_tac [wf_rfD_def]
  \\ imp_res_tac ri_dom
  \\ xfs [rfi]
  \\ metis_tac []
QED

Theorem wf_coiD:
  WellFormed G ==> coi G = diag (W G) ⨾ coi G ⨾ diag (W G)
Proof
  wf_tac [wf_coD_def]
  \\ imp_res_tac ri_dom
  \\ xfs [coi]
  \\ metis_tac []
QED

Theorem wf_friD:
  WellFormed G ==> fri G = diag (R G) ⨾ fri G ⨾ diag (W G)
Proof
  strip_tac
  \\ imp_res_tac wf_frD
  \\ imp_res_tac ri_dom
  \\ xfs [fri]
  \\ metis_tac []
QED

Theorem wf_rfeD:
  WellFormed G ==> rfe G = diag (W G) ⨾ rfe G ⨾ diag (R G)
Proof
  wf_tac [wf_rfD_def]
  \\ imp_res_tac re_dom
  \\ xfs [rfe]
  \\ metis_tac []
QED

Theorem wf_coeD:
  WellFormed G ==> coe G = diag (W G) ⨾ coe G ⨾ diag (W G)
Proof
  wf_tac [wf_coD_def]
  \\ imp_res_tac re_dom
  \\ xfs [coe]
  \\ metis_tac []
QED

Theorem wf_freD:
  WellFormed G ==> fre G = diag (R G) ⨾ fre G ⨾ diag (W G)
Proof
  strip_tac
  \\ imp_res_tac wf_frD
  \\ imp_res_tac re_dom
  \\ xfs [fre]
  \\ metis_tac []
QED

Theorem rfi_in_po:
  rfi G RSUBSET po G
Proof
  xsimp [rfi]
QED

Theorem rfi_in_rf:
  rfi G RSUBSET G.rf
Proof
  xsimp [rfi]
QED

Theorem rfe_in_rf:
  rfe G RSUBSET G.rf
Proof
  xsimp [rfe]
QED

Theorem coi_in_po:
  coi G RSUBSET po G
Proof
  xsimp [coi]
QED

Theorem coi_in_co:
  coi G RSUBSET G.co
Proof
  xsimp [coi]
QED

Theorem coe_in_co:
  coe G RSUBSET G.co
Proof
  xsimp [coe]
QED

Theorem ninit_rfi_same_tid:
  diag (COMPL is_init) ⨾ rfi G RSUBSET same_tid
Proof
  assume_tac rfi_in_po
  \\ assume_tac ninit_po_same_tid
  \\ xfs [rfi]
  \\ metis_tac []
QED

Theorem coi_trans:
  WellFormed G ==> transitive (coi G)
Proof
  wf_tac [co_trans_def]
  \\ metis_tac [coi, po_trans, relationTheory.transitive_RINTER]
QED

Theorem fri_in_po:
  fri G RSUBSET po G
Proof
  xsimp [fri]
QED

Theorem fri_in_fr:
  fri G RSUBSET fr G
Proof
  xsimp [fri]
QED

Theorem fre_in_fr:
  fre G RSUBSET fr G
Proof
  xsimp [fre]
QED

Theorem fri_coi:
  WellFormed G ==> fri G ⨾ coi G RSUBSET fri G
Proof
  strip_tac
  \\ imp_res_tac fr_co
  \\ xfs [fri, coi]
  \\ metis_tac [po_trans, relationTheory.transitive_def]
QED

(* - properties of external/internal relations ----------------------------- *)

Theorem seq_ii:
  r1 ⨾ r2 RSUBSET r3 ==>
  (r1 RINTER po G) ⨾ (r2 RINTER po G) RSUBSET (r3 RINTER po G)
Proof
  xsimp []
  \\ metis_tac [po_trans, relationTheory.transitive_def]
QED

Theorem rfi_in_poloc:
  WellFormed G ==> G.rf RINTER po G RSUBSET restr_eq_rel (loc G) (po G)
Proof
  wf_tac [wf_rfl_def]
  \\ xfs [restr_eq_rel, same_loc]
QED

Theorem coi_in_poloc:
  WellFormed G ==> G.co RINTER po G RSUBSET restr_eq_rel (loc G) (po G)
Proof
  wf_tac [wf_col_def]
  \\ xfs [restr_eq_rel, same_loc]
QED

Theorem fri_in_poloc:
  WellFormed G ==> fr G RINTER po G RSUBSET restr_eq_rel (loc G) (po G)
Proof
  strip_tac
  \\ imp_res_tac loceq_fr
  \\ xfs [loceq_same_loc, restr_eq_rel, same_loc]
QED

Theorem rfi_in_poloc':
  WellFormed G ==> rfi G RSUBSET po G RINTER same_loc G
Proof
  wf_tac [wf_rfl_def]
  \\ xfs [rfi]
QED

Theorem coi_in_poloc':
  WellFormed G ==> coi G RSUBSET po G RINTER same_loc G
Proof
  wf_tac [wf_col_def]
  \\ xfs [coi]
QED

Theorem fri_in_poloc':
  WellFormed G ==> fri G RSUBSET po G RINTER same_loc G
Proof
  strip_tac
  \\ imp_res_tac wf_frl
  \\ xfs [fri]
QED

Theorem rf_rmw_po_minus_po:
  WellFormed G ==>
  (G.rf ⨾ rmw G ⨾ RC (po G) ⨾ diag (W G)) RMINUS po G RSUBSET
  (rfe G ⨾ rmw G ⨾ RC (po G) ⨾ diag (W G))
Proof
  strip_tac
  \\ imp_res_tac rmw_in_po
  \\ xfs [rfe, rc_runion]
  \\ metis_tac [relationTheory.transitive_def, po_trans]
QED

(* - exclusive reads/writes ------------------------------------------------ *)

Theorem W_ex_not_init:
  WellFormed G ==> W_ex G SUBSET (COMPL is_init)
Proof
  strip_tac
  \\ imp_res_tac rmw_in_po
  \\ xfs [W_ex, Once no_po_to_init]
QED

Theorem W_ex_in_W:
  WellFormed G ==> W_ex G SUBSET W G
Proof
  wf_tac [wf_rmwD_def]
  \\ simp [W_ex]
  \\ FIRST_ASSUM SUBST1_TAC
  \\ xrw []
QED

Theorem W_ex_in_E:
  WellFormed G ==> W_ex G SUBSET E G
Proof
  strip_tac
  \\ imp_res_tac wf_rmwE
  \\ simp [W_ex]
  \\ FIRST_ASSUM SUBST1_TAC
  \\ xrw []
QED

Theorem W_ex_eq_EW_W_ex:
  WellFormed G ==> W_ex G = E G INTER W G INTER W_ex G
Proof
  strip_tac
  \\ imp_res_tac W_ex_in_W
  \\ imp_res_tac W_ex_in_E
  \\ xfs []
  \\ metis_tac []
QED

Theorem rmw_W_ex:
  rmw G RSUBSET (rmw G ⨾ diag (W_ex G))
Proof
  xsimp [W_ex]
  \\ metis_tac []
QED

Theorem W_ex_si:
  WellFormed G ==> diag (W_ex G) ⨾ si G = si G ⨾ diag (W_ex G)
Proof
  strip_tac
  \\ imp_res_tac si_rmw
  \\ xfs [W_ex]
  \\ metis_tac [si_sym, relationTheory.symmetric_def]
QED

(* - rf ; rmw -------------------------------------------------------------- *)

Theorem wf_rfrmwE:
  WellFormed G ==> G.rf ⨾ rmw G = diag (E G) ⨾ (G.rf ⨾ rmw G) ⨾ diag (E G)
Proof
  wf_tac [wf_rfE_def]
  \\ imp_res_tac wf_rmwE
  \\ xfs []
  \\ metis_tac []
QED

Theorem wf_rfrmwD:
  WellFormed G ==> G.rf ⨾ rmw G = diag (W G) ⨾ (G.rf ⨾ rmw G) ⨾ diag (W G)
Proof
  xsimp [WellFormed, wf_rfD_def, wf_rmwD_def]
  \\ metis_tac []
QED

Theorem wf_rfrmwl:
  WellFormed G ==> G.rf ⨾ rmw G RSUBSET same_loc G
Proof
  xsimp [WellFormed, wf_rfl_def, wf_rmwl_def]
  \\ metis_tac [same_loc_trans, relationTheory.transitive_def]
QED

Theorem wf_rfrmwf:
  WellFormed G ==> functional (inv (G.rf ⨾ rmw G))
Proof
  wf_tac [wf_rff_def]
  \\ xsimp [transp_seq, functional_seq, wf_rmw_invf]
QED

Theorem wf_rfirmwf:
  WellFormed G ==> functional (inv (rfi G ⨾ rmw G))
Proof
  strip_tac
  \\ imp_res_tac wf_rfrmwf
  \\ assume_tac rfi_in_rf
  \\ xfs [functional]
  \\ metis_tac []
QED

Theorem wf_rfermwf:
  WellFormed G ==> functional (inv (rfe G ⨾ rmw G))
Proof
  strip_tac
  \\ imp_res_tac wf_rfrmwf
  \\ assume_tac rfe_in_rf
  \\ xfs [functional]
  \\ metis_tac []
QED

Theorem rfi_rmw_in_po_same_loc_W:
  WellFormed G ==> rfi G ⨾ rmw G RSUBSET (po G RINTER same_loc G) ⨾ diag (W G)
Proof
  wf_tac [wf_rmwD_def]
  \\ imp_res_tac rmw_in_po_loc
  \\ imp_res_tac rfi_in_poloc'
  \\ assume_tac po_same_loc_trans
  \\ xfs [relationTheory.transitive_def]
  \\ metis_tac []
QED

Theorem rfi_rmw_in_po_loc:
  WellFormed G ==> rfi G ⨾ rmw G RSUBSET (po G RINTER same_loc G)
Proof
  strip_tac
  \\ imp_res_tac rfi_rmw_in_po_same_loc_W
  \\ xfs []
QED

(* - extended coherence order (Basic Properties) --------------------------- *)

Theorem co_in_eco:
  G.co RSUBSET eco G
Proof
  xsimp [eco]
  \\ metis_tac [relationTheory.RC_REFL]
QED

Theorem rf_in_eco:
  G.rf RSUBSET eco G
Proof
  xsimp [eco]
QED

Theorem fr_in_eco:
  fr G RSUBSET eco G
Proof
  xsimp [eco]
  \\ metis_tac [relationTheory.RC_REFL]
QED

Theorem co_rf_in_eco:
  G.co ⨾ G.rf RSUBSET eco G
Proof
  xsimp [eco, fr]
  \\ metis_tac [relationTheory.RC_SUBSET]
QED

Theorem fr_rf_in_eco:
  fr G ⨾ G.rf RSUBSET eco G
Proof
  xsimp [eco, fr]
  \\ metis_tac [relationTheory.RC_SUBSET]
QED

Theorem rfe_in_eco:
  rfe G RSUBSET eco G
Proof
  metis_tac [rfe_in_rf, rf_in_eco, rsubset_trans]
QED

Theorem coe_in_eco:
  coe G RSUBSET eco G
Proof
  metis_tac [coe_in_co, co_in_eco, rsubset_trans]
QED

Theorem fre_in_eco:
  fre G RSUBSET eco G
Proof
  metis_tac [fre_in_fr, fr_in_eco, rsubset_trans]
QED

Theorem funeq_rc:
  funeq f r ==> funeq f (RC r)
Proof
  metis_tac [funeq, relationTheory.RC_DEF]
QED

Theorem loceq_eco:
  WellFormed G ==> funeq (loc G) (eco G)
Proof
  strip_tac
  \\ MAP_EVERY imp_res_tac [loceq_rf, loceq_fr, loceq_co, funeq_rc]
  \\ xfs [funeq, eco]
  \\ metis_tac []
QED

Theorem wf_ecoE:
  WellFormed G ==> eco G = diag (E G) ⨾ eco G ⨾ diag (E G)
Proof
  wf_tac [wf_rfE_def, wf_coE_def]
  \\ imp_res_tac wf_frE
  \\ xfs [eco, rc_runion]
  \\ metis_tac []
QED

Theorem wf_ecoD:
  WellFormed G ==> eco G = diag (RW G) ⨾ eco G ⨾ diag (RW G)
Proof
  wf_tac [wf_rfD_def, wf_coD_def]
  \\ imp_res_tac wf_frD
  \\ xfs [eco, rc_runion]
  \\ metis_tac []
QED

Theorem eco_alt:
  eco G = (G.co RUNION fr G) RUNION RC (G.co RUNION fr G) ⨾ G.rf
Proof
  xsimp [eco, fr, rc_runion]
  \\ metis_tac []
QED

Theorem eco_alt2:
  eco G = G.rf RUNION RC (inv G.rf) ⨾ G.co ⨾ RC G.rf
Proof
  xsimp [eco, fr, rc_runion]
  \\ metis_tac []
QED

Theorem eco_trans:
  WellFormed G ==> transitive (eco G)
Proof
  strip_tac
  \\ MAP_EVERY imp_res_tac [rf_rf, rf_fr, co_co, rf_co, co_fr, fr_fr, fr_co]
  \\ xfs [relationTheory.transitive_def, eco, rc_runion]
  \\ metis_tac []
QED

Theorem eco_irr:
  WellFormed G ==> irreflexive (eco G)
Proof
  wf_tac [co_irr_def]
  \\ MAP_EVERY imp_res_tac [rf_irr, fr_irr, rf_fr, rf_co]
  \\ xfs [relationTheory.irreflexive_def, eco, rc_runion]
  \\ metis_tac []
QED

Theorem eco_alt3:
  WellFormed G ==> eco G = TC (G.rf RUNION G.co RUNION fr G)
Proof
  strip_tac
  \\ match_mp_tac relationTheory.RSUBSET_ANTISYM
  \\ REVERSE strip_tac
  >- metis_tac [rf_in_eco, co_in_eco, fr_in_eco, tc_rsubset, eco_trans,
                runion_rsubset]
  \\ rw [eco, rc_runion, diag_T_seq_r, seq_runion_r, runion_rsubset]
  \\ metis_tac [inclusion_seq_trans, rsubset_runion, rsubset_tc, rsubset_refl,
                relationTheory.TC_TRANSITIVE]
QED

Theorem eco_f:
  WellFormed G ==> eco G ⨾ diag (Fence G) RSUBSET REMPTY
Proof
  xsimp [Once wf_ecoD]
  \\ metis_tac [label_distinct]
QED

fun co_tac a b (gl as (asl,w)) =
  let
    val parse = Parse.parse_in_context (free_varsl (w::asl))
    val a_tm = parse a
    val b_tm = parse b
  in
    TRY (Cases_on `^a_tm = ^b_tm` >- (xfs [eco] \\ metis_tac []))
    \\ `G.co ^a_tm ^b_tm \/ G.co ^b_tm ^a_tm`
    by (
      xfs [wf_co_total_def, is_total]
      \\ metis_tac []
    )
    \\ xsimp [eco, fr, rc_runion]
    \\ metis_tac []
  end gl

Theorem eco_almost_total:
  WellFormed G /\ complete G /\ E G x /\ E G y /\ RW G x /\ RW G y /\
  loc G x = loc G y /\ x <> y ==>
  (eco G x y \/ eco G y x \/ ?z. G.rf z x /\ G.rf z y)
Proof
  wf_tac [wf_rfE_def, wf_rfD_def]
  \\ imp_res_tac dom_dom
  \\ imp_res_tac loceq_rf
  \\ xfs [funeq, complete]
  \\ qpat_assum `!x'. p ==> ?x. q` (qspec_then `x` assume_tac)
  \\ qpat_x_assum `!x'. p ==> ?x. q` (qspec_then `y` assume_tac)
  \\ rfs []
  \\ TRY (qmatch_assum_rename_tac `G.rf wx x`)
  \\ TRY (qmatch_assum_rename_tac `G.rf wy y`)
  >- co_tac `wx` `wy`
  >- co_tac `wx` `y`
  >- co_tac `wy` `x`
  \\ co_tac `x` `y`
QED

Theorem transp_rf_rf_eco_in_eco:
  WellFormed G ==> inv G.rf ⨾ G.rf ⨾ eco G RSUBSET eco G
Proof
  rw [eco, fr, seq_runion_r, seq_runion_l, transp_seq, rf_rf]
  \\ metis_tac [inclusion_seq_mon, rsubset_refl, seq_assoc, rf_transp_rf,
                diag_T_seq_l, rsubset_runion, seq_empty_l, seq_empty_r,
                runion_empty_l, runion_empty_r, rf_co]
QED

Theorem eco_transp_rf_rf_in_eco:
  WellFormed G ==> eco G ⨾ inv G.rf ⨾ G.rf RSUBSET eco G
Proof
  rw [eco, fr, seq_runion_r, seq_runion_l, transp_seq, rf_rf, rc_runion,
      diag_T_seq_l, diag_T_seq_r, seq_assoc, runion_rsubset]
  \\ metis_tac [inclusion_seq_mon, rsubset_refl, seq_assoc,
                rf_transp_rf, co_transp_rf, diag_T_seq_l, diag_T_seq_r,
                rsubset_runion, seq_empty_l, seq_empty_r,
                runion_empty_l, runion_empty_r]
QED

(* - implications of SC_PER_LOC -------------------------------------------- *)

Theorem no_co_to_init:
  WellFormed G /\ sc_per_loc G ==> G.co RSUBSET G.co ⨾ diag (\x. ~is_init x)
Proof
  wf_tac [wf_coE_def]
  \\ imp_res_tac loceq_co
  \\ assume_tac (Q.GENL [`a`, `b`] init_same_loc)
  \\ FIRST_X_ASSUM (fn th => CONV_TAC (LAND_CONV (REWR_CONV th)))
  \\ mp_tac co_in_eco
  \\ xrw []
  \\ strip_tac
  \\ qpat_x_assum `sc_per_loc G` mp_tac
  \\ xsimp [sc_per_loc, relationTheory.irreflexive_def]
  \\ qmatch_assum_rename_tac `G.co x y`
  \\ qexistsl_tac [`y`, `x`]
  \\ xsimp [po]
  \\ suff_tac ``~is_init x``
  >- (Cases_on `x` \\ Cases_on `y` \\ fs [is_init, ext_sb])
  \\ strip_tac
  \\ `x = y` by fs [funeq]
  \\ fs [co_irr_def, relationTheory.irreflexive_def]
  \\ metis_tac []
QED

Theorem no_fr_to_init:
  WellFormed G /\ sc_per_loc G ==> fr G RSUBSET fr G ⨾ diag (\x. ~is_init x)
Proof
  rw [fr]
  \\ imp_res_tac no_co_to_init
  \\ xfs []
  \\ metis_tac []
QED

Theorem tot_ex:
  !dom. is_total dom mo /\ dom a /\ dom b /\ ~mo a b /\ a <> b ==> mo b a
Proof
  metis_tac [is_total, pred_setTheory.SPECIFICATION]
QED

Theorem co_from_init:
  WellFormed G /\ sc_per_loc G ==>
  diag (\x. is_init x) ⨾ (same_loc G RMINUS (=)) ⨾
  diag (E G INTER W G) RSUBSET G.co
Proof
  wf_tac [wf_co_total_def, wf_init_def, wf_init_lab_def]
  \\ xrw []
  \\ qmatch_rename_tac `G.co x y`
  \\ `W G x` by metis_tac [init_w, pred_setTheory.SUBSET_applied]
  \\ Q.ISPEC_THEN `(E G INTER W G INTER (\z. loc G z = loc G x))`
       match_mp_tac tot_ex
  \\ xrw []
  >- fs [same_loc]
  >- (
    Cases_on `x`
    \\ TRY (fs [is_init] \\ FAIL_TAC "")
    \\ rfs [same_loc]
    \\ FIRST_X_ASSUM match_mp_tac
    \\ rfs [loc]
    \\ metis_tac []
  )
  \\ strip_tac
  \\ imp_res_tac (SIMP_RULE std_ss [relationTheory.RSUBSET] no_co_to_init)
  \\ xfs []
QED

Theorem BasicRMW:
  WellFormed G /\ sc_per_loc G ==> irreflexive (RC G.co ⨾ G.rf ⨾ rmw G)
Proof
  strip_tac
  \\ imp_res_tac rmw_in_po
  \\ xfs [sc_per_loc, eco, rc_runion, relationTheory.irreflexive_def]
  \\ metis_tac []
QED

Theorem w_r_loc_w_in_co:
  WellFormed G /\ (r = diag (E G) ⨾ r ⨾ diag (E G)) /\ irreflexive r /\
  irreflexive (r ⨾ eco G) ==>
  diag (W G) ⨾ r RINTER same_loc G ⨾ diag (W G) RSUBSET G.co
Proof
  wf_tac [wf_co_total_def]
  \\ FIRST_ASSUM SUBST1_TAC
  \\ xrw []
  \\ Q.ISPEC_THEN `(E G INTER W G INTER (\z. loc G z = loc G x))`
       match_mp_tac tot_ex
  \\ xrw [is_w_loc]
  >- fs [same_loc]
  >- (
    strip_tac
    \\ qpat_x_assum `irreflexive (r ⨾ eco G)` mp_tac
    \\ xsimp [relationTheory.irreflexive_def, eco, rc_runion]
    \\ metis_tac []
  )
  \\ strip_tac
  \\ metis_tac [relationTheory.irreflexive_def]
QED

Theorem w_r_loc_r_in_co_rf:
  WellFormed G /\ complete G /\ (r = diag (E G) ⨾ r ⨾ diag (E G)) /\
  irreflexive (r ⨾ eco G) ==>
  diag (W G) ⨾ r RINTER same_loc G ⨾ diag (R G) RSUBSET RC G.co ⨾ G.rf
Proof
  wf_tac [wf_co_total_def]
  \\ imp_res_tac loceq_rf
  \\ FIRST_ASSUM SUBST1_TAC
  \\ qsuff_tac `diag (W G) ⨾ diag (E G) ⨾ r RINTER same_loc G ⨾
                diag (E G INTER R G) RSUBSET RC G.co ⨾ G.rf`
  >- xrw [rc_runion]
  \\ fs [complete, loceq_same_loc]
  \\ simp [GSYM seq_assoc]
  \\ qspec_then `diag (RRANGE G.rf)` match_mp_tac seq_rsubset_r
  \\ simp [seq_assoc, diag_rsubset]
  \\ dom_l_tac wf_rfD_def
  \\ dom_l_tac wf_rfE_def
  \\ simp [GSYM seq_assoc]
  \\ qspec_then
       `diag (RRANGE (diag (W G) ⨾ diag (E G) ⨾
        (G.rf RINTER same_loc G)))` match_mp_tac seq_rsubset_r
  \\ simp [seq_assoc]
  \\ strip_tac
  >- metis_tac [inclusion_seq_mon, rsubset_refl, rsubset_rrange, diag_rsubset]
  \\ xrw [rc_runion]
  \\ qmatch_assum_rename_tac `G.rf z y`
  \\ qexists_tac `z`
  \\ Cases_on `x = z`
  \\ simp []
  \\ Q.ISPEC_THEN `(E G INTER W G INTER (\z. loc G z = loc G x))`
       match_mp_tac tot_ex
  \\ xrw [is_w_loc]
  >- fs [same_loc]
  \\ strip_tac
  \\ qpat_x_assum `irreflexive (r ⨾ eco G)` mp_tac
  \\ xsimp [eco, relationTheory.irreflexive_def, rc_runion, fr]
  \\ metis_tac []
QED

Theorem r_r_loc_w_in_fr:
  WellFormed G /\ complete G /\ (r = diag (E G) ⨾ r ⨾ diag (E G)) /\
  irreflexive (r ⨾ eco G) ==>
  diag (R G) ⨾ r RINTER same_loc G ⨾ diag (W G) RSUBSET fr G
Proof
  wf_tac [wf_co_total_def]
  \\ imp_res_tac loceq_rf
  \\ FIRST_ASSUM SUBST1_TAC
  \\ qsuff_tac `diag (E G INTER R G) ⨾ r RINTER same_loc G ⨾
                diag (E G INTER W G) RSUBSET fr G`
  >- xrw [rc_runion]
  \\ fs [complete, loceq_same_loc]
  \\ qspec_then `diag (RRANGE G.rf)` match_mp_tac seq_rsubset_l
  \\ simp [diag_rsubset]
  \\ dom_l_tac wf_rfD_def
  \\ dom_l_tac wf_rfE_def
  \\ qspec_then
       `diag (RRANGE (diag (W G) ⨾ diag (E G) ⨾
        (G.rf RINTER same_loc G)))` match_mp_tac seq_rsubset_l
  \\ strip_tac
  >- metis_tac [inclusion_seq_mon, rsubset_refl, rsubset_rrange, diag_rsubset]
  \\ xrw [fr, rc_runion]
  \\ qmatch_assum_rename_tac `G.rf z x`
  \\ qexists_tac `z`
  \\ simp []
  \\ Q.ISPEC_THEN `(E G INTER W G INTER (\z. loc G z = loc G x))`
       match_mp_tac tot_ex
  \\ xrw []
  \\ fs [same_loc]
  \\ strip_tac
  \\ qpat_x_assum `irreflexive (r ⨾ eco G)` mp_tac
  \\ xsimp [eco, relationTheory.irreflexive_def, rc_runion, fr]
  \\ metis_tac []
QED

Theorem r_r_loc_r_in_fr_rf:
  WellFormed G /\ complete G /\ (r = diag (E G) ⨾ r ⨾ diag (E G)) /\
  irreflexive (r ⨾ eco G) ==>
  diag (R G) ⨾ r RINTER same_loc G ⨾ diag (R G) RSUBSET
  fr G ⨾ G.rf RUNION inv G.rf ⨾ G.rf
Proof
  wf_tac [wf_co_total_def]
  \\ imp_res_tac loceq_rf
  \\ FIRST_ASSUM SUBST1_TAC
  \\ qsuff_tac `diag (E G INTER R G) ⨾ r RINTER same_loc G ⨾
                diag (E G INTER R G) RSUBSET fr G ⨾ G.rf RUNION inv G.rf ⨾ G.rf`
  >- xrw [rc_runion]
  \\ fs [complete, loceq_same_loc]
  \\ qspec_then `diag (RRANGE G.rf)` match_mp_tac seq_rsubset_l
  \\ simp [diag_rsubset, GSYM seq_assoc]
  \\ qspec_then `diag (RRANGE G.rf)` match_mp_tac seq_rsubset_r
  \\ simp [diag_rsubset, seq_assoc]
  \\ dom_l_tac wf_rfD_def
  \\ dom_l_tac wf_rfE_def
  \\ qspec_then
       `diag (RRANGE (diag (W G) ⨾ diag (E G) ⨾
        (G.rf RINTER same_loc G)))` match_mp_tac seq_rsubset_l
  \\ strip_tac
  >- metis_tac [inclusion_seq_mon, rsubset_refl, rsubset_rrange, diag_rsubset]
  \\ simp [GSYM seq_assoc]
  \\ qspec_then
       `diag (RRANGE (diag (W G) ⨾ diag (E G) ⨾
        (G.rf RINTER same_loc G)))` match_mp_tac seq_rsubset_r
  \\ simp [seq_assoc]
  \\ strip_tac
  >- metis_tac [inclusion_seq_mon, rsubset_refl, rsubset_rrange, diag_rsubset]
  \\ xrw [rc_runion]
  \\ MAP_EVERY qmatch_assum_rename_tac [`r x y`, `G.rf v y`, `G.rf w x`]
  \\ Cases_on `v = w`
  >- metis_tac []
  \\ disj1_tac
  \\ qexists_tac `v`
  \\ xsimp [fr]
  \\ qexists_tac `w`
  \\ simp []
  \\ Q.ISPEC_THEN `(E G INTER W G INTER (\z. loc G z = loc G x))`
       match_mp_tac tot_ex
  \\ xrw []
  \\ fs [same_loc]
  \\ strip_tac
  \\ qpat_x_assum `irreflexive (r ⨾ eco G)` mp_tac
  \\ xsimp [eco, relationTheory.irreflexive_def, rc_runion, fr]
  \\ metis_tac []
QED

Theorem w_po_loc_w_in_coi:
  WellFormed G /\ sc_per_loc G ==>
  diag (W G) ⨾ po G RINTER same_loc G ⨾ diag (W G) RSUBSET coi G
Proof
  strip_tac
  \\ match_mp_tac rsubset_trans
  \\ qexists_tac
       `(diag (W G) ⨾ po G RINTER same_loc G ⨾ diag (W G)) RINTER po G`
  \\ strip_tac
  >- xsimp []
  \\ metis_tac [rinter_rsubset_l, w_r_loc_w_in_co, wf_poE, po_irr,
                sc_per_loc, coi, rsubset_refl]
QED

Theorem w_po_loc_r_in_co_rf:
  WellFormed G /\ sc_per_loc G /\ complete G ==>
  diag (W G) ⨾ po G RINTER same_loc G ⨾ diag (R G) RSUBSET RC G.co ⨾ G.rf
Proof
  metis_tac [w_r_loc_r_in_co_rf, wf_poE, sc_per_loc]
QED

Theorem r_po_loc_w_in_fri:
  WellFormed G /\ sc_per_loc G /\ complete G ==>
  diag (R G) ⨾ po G RINTER same_loc G ⨾ diag (W G) RSUBSET fri G
Proof
  strip_tac
  \\ match_mp_tac rsubset_trans
  \\ qexists_tac
       `(diag (R G) ⨾ po G RINTER same_loc G ⨾ diag (W G)) RINTER po G`
  \\ strip_tac
  >- xsimp []
  \\ metis_tac [rinter_rsubset_l, r_r_loc_w_in_fr, wf_poE, po_irr,
                sc_per_loc, fri, rsubset_refl]
QED

Theorem r_po_loc_r_in_fr_rf:
  WellFormed G /\ sc_per_loc G /\ complete G ==>
  diag (R G) ⨾ po G RINTER same_loc G ⨾ diag (R G) RSUBSET
  fr G ⨾ G.rf RUNION inv G.rf ⨾ G.rf
Proof
  metis_tac [r_r_loc_r_in_fr_rf, wf_poE, sc_per_loc]
QED

Theorem rmw_in_fri:
  WellFormed G /\ sc_per_loc G /\ complete G ==> rmw G RSUBSET fri G
Proof
  wf_tac [wf_rmwD_def]
  \\ metis_tac [r_po_loc_w_in_fri, inclusion_seq_mon, rsubset_refl,
                rmw_in_po_loc, rsubset_trans]
QED

Theorem rmw_in_fr:
  WellFormed G /\ sc_per_loc G /\ complete G ==> rmw G RSUBSET fr G
Proof
  metis_tac [rsubset_trans, rmw_in_fri, fri_in_fr]
QED

Triviality rf_rmw_in_co_helper:
  WellFormed G /\ sc_per_loc G ==> G.rf ⨾ rmw G RSUBSET G.co RUNION inv G.co
Proof
  wf_tac [wf_co_total_def, wf_rfl_def, wf_rmwl_def, is_total]
  \\ dom_l_tac wf_rfE_def
  \\ imp_res_tac wf_rmwE
  \\ pop_assum (SUBST1_TAC o MATCH_MP dom_r)
  \\ dom_l_tac wf_rfD_def
  \\ dom_r_tac wf_rmwD_def
  \\ xrw []
  \\ FIRST_ASSUM match_mp_tac
  \\ xfs []
  \\ strip_tac
  >- metis_tac [same_loc]
  \\ strip_tac
  \\ fs [sc_per_loc]
  \\ qpat_x_assum `irreflexive (po G ⨾ eco G)` mp_tac
  \\ MAP_EVERY assume_tac [rmw_in_po, rf_in_eco]
  \\ xfs [relationTheory.irreflexive_def]
  \\ metis_tac []
QED

Theorem rf_rmw_in_co:
  WellFormed G /\ sc_per_loc G ==> G.rf ⨾ rmw G RSUBSET G.co
Proof
  strip_tac
  \\ match_mp_tac rsubset_trans
  \\ qexists_tac `(G.rf ⨾ rmw G) RINTER (G.rf ⨾ rmw G)`
  \\ strip_tac
  >- xsimp []
  \\ match_mp_tac rinter_rsubset_l
  \\ qexists_tac `G.co RUNION inv G.co`
  \\ strip_tac
  >- metis_tac [rf_rmw_in_co_helper]
  \\ simp [runion_rinter_l, runion_rsubset]
  \\ strip_tac
  >- xsimp []
  \\ match_mp_tac rsubset_trans
  \\ qexists_tac `REMPTY`
  \\ REVERSE strip_tac
  >- xsimp []
  \\ xrw []
  \\ spose_not_then strip_assume_tac
  \\ qpat_x_assum `sc_per_loc G` (mp_tac o SIMP_RULE std_ss [sc_per_loc])
  \\ MAP_EVERY assume_tac [rmw_in_po, co_rf_in_eco]
  \\ xfs [relationTheory.irreflexive_def]
  \\ metis_tac []
QED

Theorem rf_rmw_ct_in_co:
  WellFormed G /\ sc_per_loc G ==> TC (G.rf ⨾ rmw G) RSUBSET G.co
Proof
  wf_tac [co_trans_def]
  \\ simp [tc_rsubset, rf_rmw_in_co]
QED

Theorem rf_rmw_rt_in_co:
  WellFormed G /\ sc_per_loc G ==> RTC (G.rf ⨾ rmw G) RSUBSET RC G.co
Proof
  wf_tac [co_trans_def]
  \\ simp [relationTheory.transitive_RC, rtc_rsubset, rf_rmw_in_co, rsubset_rc]
QED

(* - lift ------------------------------------------------------------------ *)

Theorem step_lift:
  refl eqv r /\ symmetric eqv /\ transitive eqv ==>
  lift eqv r (eqv x) (eqv y) = (eqv ⨾ r ⨾ eqv) x y
Proof
  xrw [refl, lift, relationTheory.transitive_def, relationTheory.symmetric_def]
  \\ eq_tac
  \\ rw []
  >- metis_tac []
  \\ qmatch_assum_rename_tac `r v w`
  \\ qexistsl_tac [`v`, `w`]
  \\ simp []
  \\ metis_tac []
QED

Theorem step_lift2:
  r x y ==> (lift eqv r) (eqv x) (eqv y)
Proof
  metis_tac [lift]
QED

Theorem ct_lift1:
  refl eqv r /\ symmetric eqv /\ transitive eqv /\ TC (lift eqv r) X Y ==>
  !x y. (X = eqv x) /\ (Y = eqv y) ==> (eqv ⨾ TC (r ⨾ eqv)) x y
Proof
  rpt strip_tac
  \\ ntac 2 (pop_assum mp_tac)
  \\ Q.SPEC_TAC (`y`, `y`)
  \\ Q.SPEC_TAC (`x`, `x`)
  \\ pop_assum mp_tac
  \\ Q.SPEC_TAC (`Y`, `Y`)
  \\ Q.SPEC_TAC (`X`, `X`)
  \\ ho_match_mp_tac relationTheory.TC_INDUCT_LEFT1
  \\ strip_tac
  >- (
    xrw [lift, Once relationTheory.TC_CASES1]
    \\ fs [refl, relationTheory.transitive_def, relationTheory.symmetric_def]
    \\ metis_tac []
  )
  \\ rpt strip_tac
  \\ rfs [lift]
  \\ qmatch_assum_rename_tac `r v w`
  \\ first_x_assum (qspecl_then [`w`, `y`] assume_tac)
  \\ rfs []
  \\ xsimp []
  \\ qexists_tac `v`
  \\ strip_tac
  >- (
    fs [refl, relationTheory.transitive_def, relationTheory.symmetric_def]
    \\ metis_tac []
  )
  \\ xfs []
  \\ match_mp_tac
        (SIMP_RULE std_ss [relationTheory.transitive_def]
           relationTheory.TC_TRANSITIVE)
  \\ qmatch_assum_rename_tac `eqv w z`
  \\ qexists_tac `z`
  \\ simp []
  \\ xsimp [Once relationTheory.TC_CASES1]
  \\ metis_tac []
QED

Theorem ct_lift:
  refl eqv r /\ symmetric eqv /\ transitive eqv ==>
  TC (lift eqv r) (eqv x) (eqv y) = (eqv ⨾ TC (r ⨾ eqv)) x y
Proof
  strip_tac
  \\ eq_tac
  >- metis_tac [ct_lift1]
  \\ xsimp []
  \\ strip_tac
  \\ qmatch_assum_rename_tac `eqv x z`
  \\ qpat_x_assum `eqv x z` mp_tac
  \\ Q.SPEC_TAC (`x`, `x`)
  \\ pop_assum mp_tac
  \\ Q.SPEC_TAC (`y`, `y`)
  \\ Q.SPEC_TAC (`z`, `z`)
  \\ ho_match_mp_tac relationTheory.TC_INDUCT_LEFT1
  \\ strip_tac
  >- (
    xrw [lift, Once relationTheory.TC_CASES1]
    \\ disj1_tac
    \\ qmatch_assum_rename_tac `r z v`
    \\ qexistsl_tac [`z`, `v`]
    \\ fs [refl, relationTheory.transitive_def, relationTheory.symmetric_def]
    \\ metis_tac []
  )
  \\ ntac 6 strip_tac
  \\ xfs []
  \\ match_mp_tac
        (SIMP_RULE std_ss [relationTheory.transitive_def]
           relationTheory.TC_TRANSITIVE)
  \\ qmatch_assum_rename_tac `r z v`
  \\ qmatch_assum_rename_tac `eqv v w`
  \\ qexists_tac `eqv v`
  \\ simp []
  \\ xsimp [Once relationTheory.TC_CASES1]
  \\ disj1_tac
  \\ simp [step_lift]
  \\ xsimp []
  \\ qexists_tac `z`
  \\ fs [refl]
  \\ metis_tac []
QED

Theorem ct_lift2:
  refl eqv r /\ symmetric eqv /\ transitive eqv ==>
  TC (lift eqv r) X Y = ?x y. X = eqv x /\ Y = eqv y /\ TC (r ⨾ eqv) x y
Proof
  strip_tac
  \\ eq_tac
  >- (
    Q.SPEC_TAC (`Y`, `Y`)
    \\ Q.SPEC_TAC (`X`, `X`)
    \\ ho_match_mp_tac relationTheory.TC_INDUCT
    \\ strip_tac
    >- (
      xrw [lift]
      \\ xfs [Once relationTheory.TC_CASES1, refl,
              relationTheory.transitive_def, relationTheory.symmetric_def]
      \\ metis_tac []
    )
    \\ ntac 4 strip_tac
    \\ qmatch_assum_rename_tac `Y = eqv w`
    \\ qmatch_assum_rename_tac `TC (r ⨾ eqv) v w`
    \\ qexistsl_tac [`x`, `w`]
    \\ simp []
    \\ match_mp_tac
          (SIMP_RULE std_ss [relationTheory.transitive_def]
             relationTheory.TC_TRANSITIVE)
    \\ qexists_tac `v`
    \\ simp []
    \\ qpat_x_assum `TC (r ⨾ eqv) x y` (assume_tac o SIMP_RULE std_ss [ct_end])
    \\ simp [ct_end]
    \\ xfs [refl, relationTheory.transitive_def, relationTheory.symmetric_def]
    \\ metis_tac []
  )
  \\ xrw []
  \\ ntac 2 (qpat_x_assum `!x. p` mp_tac)
  \\ Q.SPEC_TAC (`Y`, `Y`)
  \\ Q.SPEC_TAC (`X`, `X`)
  \\ pop_assum mp_tac
  \\ Q.SPEC_TAC (`y`, `y`)
  \\ Q.SPEC_TAC (`x`, `x`)
  \\ ho_match_mp_tac relationTheory.TC_INDUCT_LEFT1
  \\ xrw []
  >- (
    xfs [Once relationTheory.TC_CASES1, refl, lift,
         relationTheory.transitive_def, relationTheory.symmetric_def]
    \\ metis_tac []
  )
  \\ match_mp_tac
        (SIMP_RULE std_ss [relationTheory.transitive_def]
           relationTheory.TC_TRANSITIVE)
  \\ qmatch_assum_rename_tac `eqv v w`
  \\ qexists_tac `eqv w`
  \\ simp []
  \\ xsimp [Once relationTheory.TC_CASES1]
  \\ disj1_tac
  \\ fs [refl, lift, relationTheory.transitive_def,
         relationTheory.symmetric_def]
  \\ qexistsl_tac [`x`, `v`]
  \\ simp [FUN_EQ_THM]
  \\ metis_tac []
QED

Theorem acyclic_lift:
  refl eqv r /\ symmetric eqv /\ transitive eqv ==>
  acyclic (lift eqv r) = acyclic (r ⨾ eqv)
Proof
  rw [acyclic, relationTheory.irreflexive_def]
  \\ eq_tac
  \\ strip_tac
  \\ Q.X_GEN_TAC `x`
  \\ strip_tac
  >- (
    `eqv x x`
    by (
      xfs [Once relationTheory.TC_CASES1, refl, relationTheory.transitive_def,
           relationTheory.symmetric_def]
      \\ metis_tac []
    )
    \\ assume_tac (Q.INST [`y` |-> `x`] ct_lift)
    \\ xfs []
    \\ metis_tac []
  )
  \\ `?y. x = eqv y`
  by (
    pop_assum mp_tac
    \\ xsimp [Once relationTheory.TC_CASES1, lift]
    \\ metis_tac []
  )
  \\ assume_tac (Q.INST [`X` |-> `x`, `Y` |-> `x`] ct_lift1)
  \\ rfs []
  \\ pop_assum (qspecl_then [`y`, `y`] assume_tac)
  \\ rfs [semi]
  \\ qmatch_assum_rename_tac `eqv y z`
  \\ qpat_x_assum `!x. p` (qspec_then `z` mp_tac)
  \\ simp []
  \\ xfs [Once ct_end, refl, relationTheory.transitive_def,
          relationTheory.symmetric_def]
  \\ metis_tac []
QED

Theorem delift_restr_classes:
  delift eqv (restr_rel (classes eqv) rel) = delift eqv rel
Proof
  simp [refl, relationTheory.transitive_def, relationTheory.symmetric_def,
        delift, restr_rel, classes, FUN_EQ_THM]
  \\ metis_tac []
QED

Theorem delift_lift:
  refl eqv r /\ symmetric eqv /\ transitive eqv ==>
  delift eqv (lift eqv r) = (eqv ⨾ r ⨾ eqv)
Proof
  xrw [refl, relationTheory.transitive_def, relationTheory.symmetric_def,
       lift, delift, FUN_EQ_THM]
  \\ eq_tac
  \\ rw []
  \\ TRY (qmatch_assum_rename_tac `r y z` \\ qexistsl_tac [`y`, `z`])
  \\ metis_tac []
QED

Theorem delift_ct_lift:
  refl eqv r /\ symmetric eqv /\ transitive eqv ==>
  delift eqv (TC (lift eqv r)) = eqv ⨾ TC (r ⨾ eqv)
Proof
  rw [delift, ct_lift, FUN_EQ_THM]
  \\ eq_tac
  \\ rw []
  >- (
    xfs [Once relationTheory.TC_CASES1, refl, relationTheory.transitive_def,
         relationTheory.symmetric_def]
    \\ metis_tac []
  )
  \\ xfs [Once relationTheory.TC_CASES2, refl, relationTheory.transitive_def,
          relationTheory.symmetric_def]
  \\ metis_tac []
QED

(* -------------------------------------------------------------------------
   End
   ------------------------------------------------------------------------- *)

val () = export_theory()
