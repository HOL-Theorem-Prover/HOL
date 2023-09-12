open HolKernel Parse boolLib bossLib;

open pred_setTheory finite_mapTheory transferTheory transferLib

val _ = new_theory "nfmbst";

Datatype:
  bst = Lf | Nd bst num 'a bst
End

Definition bstdom_def[simp]:
  bstdom Lf = {} /\
  bstdom (Nd l k v r) = k INSERT (bstdom l UNION bstdom r)
End

Theorem bstdom_EQ_EMPTY[simp]:
  bstdom b = {} <=> b = Lf
Proof
  Cases_on ‘b’ >> simp[]
QED

Definition bstlookup_def[simp]:
  bstlookup Lf k = NONE /\
  bstlookup (Nd l k1 v r) k2 = if k1 = k2 then SOME v
                               else if k2 < k1 then bstlookup l k2
                               else bstlookup r k2
End

(* argument pattern mimicks fupdate (|+) *)
Definition bstinsert_def[simp]:
  bstinsert Lf (k, v) = Nd Lf k v Lf /\
  bstinsert (Nd l k2 v2 r) (k1, v1) =
  if k1 = k2 then Nd l k1 v1 r
  else if k1 < k2 then Nd (bstinsert l (k1, v1)) k2 v2 r
  else Nd l k2 v2 (bstinsert r (k1, v1))
End

Definition optrange_def[simp]:
  optrange NONE NONE        = UNIV /\
  optrange NONE (SOME hi)   = { x | x < hi} /\
  optrange (SOME lo) NONE   = { x | lo < x} /\
  optrange (SOME lo) (SOME hi) = { x | lo < x /\ x < hi}
End

Theorem optrange_UB:
  x IN optrange lo (SOME y) ==> x < y
Proof
  Cases_on ‘lo’ >> simp[]
QED

Theorem optrange_LB:
  x IN optrange (SOME y) hi ==> y < x
Proof
  Cases_on ‘hi’ >> simp[]
QED

Definition bstOK_def[simp]:
  bstOK lo_opt hi_opt Lf = T /\
  bstOK lo_opt hi_opt (Nd l k v r) =
  (k IN optrange lo_opt hi_opt /\
   bstOK lo_opt (SOME k) l /\
   bstOK (SOME k) hi_opt r)
End

Theorem bstOK_SOME2:
  !lo hi b. bstOK (SOME lo) (SOME hi) b ==> b = Lf \/ lo + 2 <= hi
Proof
  Induct_on ‘b’ >> simp[]
QED

Theorem bstOK_bstdom:
  !b loo hio.
    bstOK loo hio b ==> !k. k IN bstdom b ==> k IN optrange loo hio
Proof
  Induct_on ‘b’ >> simp[] >> rpt strip_tac
  >- metis_tac[] >>
  first_x_assum drule_all >>
  Cases_on ‘loo’ >> simp[] >> Cases_on ‘hio’ >> gs[]
QED

Theorem bstdom_bstlookup:
  !loo hio b k.
    bstOK loo hio b /\ k IN optrange loo hio /\ k IN bstdom b ==>
    ?v. bstlookup b k = SOME v
Proof
  Induct_on ‘b’ >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, AllCaseEqs(), EXISTS_OR_THM] >>
  rpt strip_tac >> simp[] >> rename [‘k1 <> k2’] >> Cases_on ‘k1 = k2’ >>
  simp[] >>
  drule_all_then strip_assume_tac bstOK_bstdom >>
  (drule optrange_LB ORELSE drule optrange_UB) >> simp[] >>
  strip_tac >> first_x_assum irule >> simp[] >>
  first_assum $ irule_at (Pat ‘bstOK _ _ _’) >> simp[]
QED

Theorem notin_bstdom_bstlookup:
  k NOTIN bstdom b ==> bstlookup b k = NONE
Proof
  Induct_on ‘b’ >> simp[]
QED

Definition extendlo_def[simp]:
  extendlo NONE k = NONE /\
  extendlo (SOME x) k = if x < k then SOME x else if k = 0 then NONE
                        else SOME (k-1)
End

Definition extendhi_def[simp]:
  extendhi k NONE = NONE /\
  extendhi k (SOME x) = if k < x then SOME x else SOME (k + 1)
End

Theorem extendlo_id:
  k IN optrange lo hi ==> extendlo lo k = lo
Proof
  Cases_on ‘lo’ >> simp[] >> strip_tac >> drule optrange_LB >> simp[]
QED

Theorem extendhi_id:
  k IN optrange lo hi ==> extendhi k hi = hi
Proof
  Cases_on ‘hi’ >> simp[] >> strip_tac >> drule optrange_UB >> simp[]
QED

Theorem bstOK_bstinsert:
  !lo hi b.
    bstOK lo hi b ==> bstOK (extendlo lo k) (extendhi k hi) (bstinsert b (k, v))
Proof
  Induct_on ‘b’ >> simp[]
  >- (map_every Cases_on [‘lo’, ‘hi’] >> simp[] >> rw[]) >>
  rpt strip_tac >> rw[]
  >- (map_every Cases_on [‘lo’, ‘hi’] >> gs[])
  >- (drule extendlo_id >> simp[])
  >- (drule extendhi_id >> simp[])
  >- (map_every Cases_on [‘lo’, ‘hi’] >> gs[] >> rw[])
  >- (rename [‘bstOK _ _ (bstinsert b _)’] >>
      first_assum (qpat_x_assum ‘bstOK _ _ b’ o mp_then Any mp_tac) >>
      simp[])
  >- (Cases_on ‘hi’ >> gvs[] >> drule_then assume_tac optrange_UB >> simp[])
  >- (map_every Cases_on [‘lo’, ‘hi’] >> gs[] >> rw[])
  >- (Cases_on ‘lo’ >> gvs[] >> drule_then assume_tac optrange_LB >> simp[])
  >- (‘extendlo (SOME n) k = SOME n’ suffices_by metis_tac[] >>
      simp[])
QED

Theorem bstdom_bstinsert[simp]:
  bstdom (bstinsert b (k, v)) = k INSERT bstdom b
Proof
  Induct_on ‘b’ >> simp[] >> rw[] >> SET_TAC[]
QED

Overload wfBST = “bstOK NONE NONE”

Theorem wfBST_bstinsert:
  wfBST b ==> wfBST (bstinsert b (k, v))
Proof
  strip_tac >> drule bstOK_bstinsert >> simp[]
QED

Theorem bstlookup_bstinsert_eqk[simp]:
  !k v b. bstlookup (bstinsert b (k, v)) k = SOME v
Proof
  Induct_on ‘b’ >> simp[] >> rw[]
QED

Theorem bstlookup_bstinsert_neq:
  !k1 k2 v b. k1 <> k2 ==> bstlookup (bstinsert b (k1, v)) k2 = bstlookup b k2
Proof
  Induct_on ‘b’ >> simp[] >> rw[]
QED

Definition bst_to_fm_def[simp]:
  bst_to_fm Lf = FEMPTY /\
  bst_to_fm (Nd l k v r) = FUNION (bst_to_fm l) (bst_to_fm r) |+ (k,v)
End

Definition NFMBST_def:
  NFMBST AB fm bst <=> bstOK NONE NONE bst /\
                       bstdom bst = FDOM fm /\
                       !k. k IN FDOM fm ==>
                           AB (fm ' k) (THE (bstlookup bst k))
End

Theorem FDOM_bst_to_fm[simp]:
  FDOM (bst_to_fm b) = bstdom b
Proof
  Induct_on ‘b’ >> simp[]
QED

Theorem FAPPLY_bst_to_fm:
  !b k lo hi.
    bstOK lo hi b /\ k IN bstdom b ==> bst_to_fm b ' k = THE (bstlookup b k)
Proof
  Induct >> simp[] >> rw[] >>
  simp[FAPPLY_FUPDATE_THM, FUNION_DEF]
  >- metis_tac[]
  >- (drule_all_then assume_tac bstOK_bstdom >>
      drule optrange_LB >> simp[])
  >- (drule_all_then assume_tac bstOK_bstdom >>
      drule optrange_UB >> simp[]) >>
  ‘k NOTIN bstdom b’ suffices_by metis_tac[] >> strip_tac >>
  pop_assum (mp_then (Pos last) (drule_then assume_tac) bstOK_bstdom) >>
  drule optrange_UB >> simp[]
QED

Theorem bst_to_fm_correct:
  !b fm. NFMBST (=) fm b ==> bst_to_fm b = fm
Proof
  Induct >> simp[NFMBST_def]
  >- metis_tac[finite_mapTheory.FDOM_EQ_EMPTY] >>
  rw[] >>
  simp[fmap_EXT, DISJ_IMP_THM, FORALL_AND_THM] >>
  rw[] >> simp[FAPPLY_FUPDATE_THM, FUNION_DEF, AllCaseEqs()]
  >- (‘x IN bstdom b’ suffices_by metis_tac[FAPPLY_bst_to_fm] >>
      ‘x NOTIN bstdom b'’ suffices_by metis_tac[IN_INSERT, IN_UNION] >>
      strip_tac >>
      pop_assum (mp_then (Pos last) (drule_then assume_tac) bstOK_bstdom) >>
      drule optrange_LB >> simp[])
  >- (‘x NOTIN bstdom b’
        suffices_by metis_tac[IN_INSERT, IN_UNION, FAPPLY_bst_to_fm] >>
      strip_tac >>
      pop_assum (mp_then (Pos last) (drule_then assume_tac) bstOK_bstdom) >>
      drule optrange_UB >> simp[])
QED


Theorem NFMBST_left_unique[transfer_safe]:
  left_unique AB ==> left_unique (NFMBST AB)
Proof
  simp[left_unique_def, NFMBST_def] >> rw[] >>
  simp[fmap_EXT] >> conj_tac
  >- metis_tac[] >>
  rpt (qpat_x_assum ‘bstdom _ = _’ (assume_tac o SYM)) >> gs[] >>
  rw[] >> metis_tac[]
QED

Theorem NFMBST_total[transfer_safe]:
  total AB ==> total (NFMBST AB)
Proof
  simp[total_def, NFMBST_def] >> strip_tac >>
  CONV_TAC (RAND_CONV (ALPHA_CONV “fm:num |-> 'a”)) >>
  Induct_on ‘fm’ >> simp[] >> rpt strip_tac >>
  rename [‘fm |+ (k,v)’, ‘bstdom b = FDOM fm’] >>
  ‘?v'. AB v v'’ by metis_tac[] >>
  qexists_tac ‘bstinsert b (k, v')’ >>
  simp[wfBST_bstinsert] >> rpt strip_tac >> simp[] >>
  rename [‘bstlookup (bstinsert b (k1, _)) k2’] >>
  Cases_on ‘k1 = k2’ >> simp[bstlookup_bstinsert_neq, FAPPLY_FUPDATE_THM]
QED

Theorem RRANGE_NFMBST[transfer_simp]:
  RRANGE (NFMBST (=)) b <=> wfBST b
Proof
  simp[NFMBST_def, relationTheory.RRANGE, EQ_IMP_THM, PULL_EXISTS] >>
  strip_tac >> qexists ‘bst_to_fm b’ >>
  drule_then assume_tac FAPPLY_bst_to_fm >> simp[]
QED

Theorem NFMBST_FEMPTY[transfer_rule]:
  NFMBST AB FEMPTY Lf
Proof
  simp[NFMBST_def]
QED

Theorem NFMBST_FDOM[transfer_rule]:
  (NFMBST AB |==> (=)) FDOM bstdom
Proof
  simp[FUN_REL_def, NFMBST_def]
QED

Theorem NFMBST_FUPDATE[transfer_rule]:
  (NFMBST AB |==> ((=) ### AB) |==> NFMBST AB) $|+ bstinsert
Proof
  simp[FUN_REL_def, NFMBST_def, pairTheory.FORALL_PROD, DISJ_IMP_THM,
       FORALL_AND_THM, bstlookup_bstinsert_neq, PAIR_REL_def,
       wfBST_bstinsert] >>
  rw[] >>
  rename [‘(fm |+ (k1,v)) ' k2’] >> Cases_on ‘k1 = k2’ >>
  simp[bstlookup_bstinsert_neq, FAPPLY_FUPDATE_THM]
QED

Theorem NFMBST_FLOOKUP[transfer_rule]:
  (NFMBST AB |==> (=) |==> OPTREL AB) FLOOKUP bstlookup
Proof
  simp[NFMBST_def, FUN_REL_def] >> rw[] >>
  rw[FLOOKUP_DEF]
  >- (drule bstdom_bstlookup >> simp[] >>
      disch_then drule >> simp[PULL_EXISTS] >>
      first_x_assum drule >> rpt strip_tac >> gs[]) >>
  simp[optionTheory.OPTREL_def, notin_bstdom_bstlookup]
QED

Theorem optrange_use_NONE:
  n IN optrange lo hi ==> n IN optrange NONE hi /\ n IN optrange lo NONE
Proof
  Cases_on ‘lo’ >> Cases_on ‘hi’ >> simp[]
QED

Theorem bstOK_use_NONE:
  !lo hi. bstOK lo hi b ==> bstOK NONE hi b /\ bstOK lo NONE b
Proof
  Induct_on ‘b’ >> simp[] >> rw[] >> metis_tac[optrange_use_NONE]
QED

Theorem bstOK_wfBST:
  !lo hi. bstOK lo hi b ==> wfBST b
Proof
  metis_tac[bstOK_use_NONE]
QED

Theorem bst_to_fm_bstinsert[simp]:
  wfBST b ==>
  bst_to_fm (bstinsert b (k,v)) = bst_to_fm b |+ (k,v)
Proof
  Induct_on ‘b’ >> simp[] >> rw[]
  >- (simp[fmap_EXT] >> conj_tac >- SET_TAC[] >>
      rw[] >> simp[FAPPLY_FUPDATE_THM, FUNION_DEF]
      >- (rpt $ dxrule bstOK_wfBST >> simp[])
      >- (rename [‘k2 IN bstdom b’] >>
          ‘wfBST b’ by metis_tac[bstOK_wfBST] >>
          simp[FAPPLY_FUPDATE_THM] >> rw[])
      >- (rename [‘bstinsert b (k,v)’] >>
          ‘wfBST b’ by metis_tac[bstOK_wfBST] >>
          simp[FAPPLY_FUPDATE_THM] >> rw[] >> gvs[])) >>
  simp[fmap_EXT] >> conj_tac >- SET_TAC[] >>
  rw[FAPPLY_FUPDATE_THM, FUNION_DEF]
  >- (drule_all_then assume_tac bstOK_bstdom >> gs[])
  >- (rename [‘bstinsert b (k,v)’] >> ‘wfBST b’ by metis_tac[bstOK_wfBST] >>
      simp[])
  >- (rename [‘bstinsert b (k,v)’] >> ‘wfBST b’ by metis_tac[bstOK_wfBST] >>
      simp[FAPPLY_FUPDATE_THM])
QED

Theorem bst_to_fm_surj:
  !fm. ?b. wfBST b /\ bst_to_fm b = fm
Proof
  Induct >> rw[] >- (qexists‘Lf’ >> simp[]) >>
  rename [‘bst_to_fm b |+ (k,v)’] >>
  qexists ‘bstinsert b (k,v)’ >>
  simp[bst_to_fm_bstinsert, wfBST_bstinsert]
QED

Theorem NFM_bst_to_fm:
  NFMBST (=) x y <=> x = bst_to_fm y /\ wfBST y
Proof
  iff_tac >> rw[]
  >- metis_tac[bst_to_fm_correct]
  >- gs[NFMBST_def] >>
  simp[NFMBST_def] >> metis_tac[FAPPLY_bst_to_fm]
QED

Theorem NFMEQ[transfer_rule]:
  (NFMBST (=) |==> NFMBST (=) |==> flip (==>)) (=) (=)
Proof
  simp[FUN_REL_def] >> simp[NFM_bst_to_fm]
QED

(* hard example

Definition foo_def:
  foo 0 = FEMPTY /\
  foo (SUC n) = foo n |+ (n, n)
End

Definition foo'_def:
  foo' n = @bst. bst_to_fm bst = foo n /\ wfBST bst
End

Theorem NFMfoo[transfer_rule]:
  ((=) |==> NFMBST (=)) foo foo'
Proof
  simp[FUN_REL_def, foo'_def] >> gen_tac >> SELECT_ELIM_TAC >> conj_tac
  >- metis_tac[bst_to_fm_surj] >>
  simp[NFM_bst_to_fm]
QED

*)


val _ = export_theory();
