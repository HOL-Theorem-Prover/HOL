open HolKernel Parse boolLib bossLib;
open quotient

open listTheory liftingTheory transferTheory transferLib

val _ = new_theory "finite_set";

Definition fsequiv_def:
  fsequiv l1 l2 <=> set l1 = set l2
End

Theorem fsequiv_refl[simp]:
  fsequiv l l
Proof
  simp[fsequiv_def]
QED

Theorem fsequiv_equiv:
  EQUIV fsequiv
Proof
  simp[quotientTheory.EQUIV_def, FUN_EQ_THM, fsequiv_def] >>
  metis_tac[]
QED

val _ = define_quotient_types
          {defs = [], old_thms = [],
           poly_preserves = [],
           poly_respects = [],
           respects = [],
           tyop_equivs = [],
           tyop_quotients = [],
           tyop_simps = [],
           types = [{equiv = fsequiv_equiv, name = "fset"}]}

(* map from list to set is fset_ABS, in other direction it's fset_REP *)
Theorem fset_ABS_REP_CLASS = theorem "fset_ABS_REP_CLASS"
Theorem bijection2 = fset_ABS_REP_CLASS
                       |> CONJUNCT2 |> SPEC_ALL |> EQ_IMP_RULE |> #1
                       |> GEN_ALL
                       |> SIMP_RULE bool_ss [PULL_EXISTS, fsequiv_refl]

Theorem REP_CLASS_11[simp]:
  fset_REP_CLASS fs1 = fset_REP_CLASS fs2 <=> fs1 = fs2
Proof
  metis_tac[fset_ABS_REP_CLASS]
QED

Theorem REP_ABS_equiv[simp]:
  fset_REP_CLASS (fset_ABS_CLASS (fsequiv r)) = fsequiv r
Proof
  simp[GSYM (CONJUNCT2 fset_ABS_REP_CLASS)] >> metis_tac[]
QED

Theorem ABS_CLASS_onto:
  !fs. ?r.  fs = fset_ABS_CLASS (fsequiv r)
Proof
  metis_tac[fset_ABS_REP_CLASS]
QED

Theorem REP_CLASS_NONEMPTY:
  !fs. ?x. fset_REP_CLASS fs x
Proof
  gen_tac >> qspec_then ‘fs’ (qx_choose_then ‘r’ assume_tac) ABS_CLASS_onto >>
  simp[] >> metis_tac[fsequiv_refl]
QED

Theorem fset_ABS_REP[simp]:
  fset_ABS (fset_REP s) = s
Proof
  simp[definition "fset_ABS_def", definition "fset_REP_def"] >>
  ‘fsequiv ($@ (fset_REP_CLASS s)) = fset_REP_CLASS s’
    suffices_by metis_tac[REP_CLASS_11, REP_ABS_equiv] >>
  simp[FUN_EQ_THM] >> qx_gen_tac ‘a’ >> SELECT_ELIM_TAC >> conj_tac
  >- metis_tac[REP_CLASS_NONEMPTY] >>
  rw[EQ_IMP_THM] >>
  qspec_then ‘s’ (qx_choose_then ‘r’ assume_tac) ABS_CLASS_onto >> fs[] >>
  metis_tac[quotientTheory.EQUIV_def, fsequiv_equiv]
QED

Theorem fset_REP_11[simp]:
  fset_REP fs1 = fset_REP fs2 <=> fs1 = fs2
Proof
  metis_tac[fset_ABS_REP]
QED

Theorem fset_ABS_onto:
  !fs. ?l. fset_ABS l = fs
Proof
  metis_tac[fset_ABS_REP]
QED

Definition FSET0_def:
  FSET0 l s <=> s = fset_ABS l
End

Theorem FSET0_right_unique:
  right_unique FSET0
Proof
  simp[FSET0_def, right_unique_def]
QED

Theorem FSET0_surj:
  surj FSET0
Proof
  simp[FSET0_def, surj_def] >> metis_tac[fset_ABS_onto]
QED

Theorem fset_ABS_11[simp]:
  fset_ABS l1 = fset_ABS l2 <=> fsequiv l1 l2
Proof
  rw[EQ_IMP_THM, definition "fset_ABS_def"]
  >- (pop_assum (mp_tac o Q.AP_TERM ‘fset_REP_CLASS’) >>
      simp[bijection2, Excl "REP_CLASS_11"]) >>
  ‘fsequiv l1 = fsequiv l2’ suffices_by metis_tac[bijection2, REP_CLASS_11] >>
  metis_tac[fsequiv_equiv, quotientTheory.EQUIV_def]
QED

Theorem total_FSET0[transfer_safe]:
  total FSET0
Proof
  simp[total_def, FSET0_def]
QED

Theorem RDOM_FSET0[simp,transfer_simp]:
  RDOM FSET0 = K T
Proof
  simp[pred_setTheory.EXTENSION, IN_DEF, relationTheory.RDOM_DEF, FSET0_def]
QED


Theorem fsetQ:
  Qt fsequiv fset_ABS fset_REP FSET0
Proof
  simp[Qt_def, relationTheory.O_DEF, relationTheory.inv_DEF, FUN_EQ_THM,
       FSET0_def]
QED

Theorem fsequiv_repabs:
  fsequiv (fset_REP (fset_ABS l)) l
Proof
  assume_tac fsetQ >>
  fs[Qt_def, relationTheory.O_DEF, relationTheory.inv_DEF, PULL_EXISTS,IN_DEF]>>
  qexists_tac ‘fset_ABS l’ >> simp[] >> simp[FSET0_def]
QED

(* important for predicates over the new type *)
Theorem RDOM_FSET0set[simp,transfer_simp]:
  RDOM (FSET0 |==> ($= : bool -> bool -> bool)) =
    \lP. (!l1 l2. lP l1 /\ fsequiv l1 l2 ==> lP l2)
Proof
  rw[relationTheory.RDOM_DEF, Once FUN_EQ_THM, FUN_REL_def, FSET0_def] >>
  eq_tac >> rw[]
  >- (fs[IN_DEF] >> metis_tac[fset_ABS_11]) >>
  qexists_tac ‘\fs. lP (fset_REP fs)’ >> simp[] >> fs[IN_DEF] >>
  metis_tac[fsequiv_repabs, fsequiv_equiv, quotientTheory.EQUIV_def]
QED

Definition fUNION_def:
  fUNION f1 f2 = fset_ABS (fset_REP f1 ++ fset_REP f2)
End

Theorem fUNION_relates[transfer_rule]:
  (FSET0 |==> FSET0 |==> FSET0) APPEND fUNION
Proof
  irule HK_thm2 >>
  map_every qexists_tac [
    ‘fset_REP ---> fset_REP ---> fset_ABS’,
    ‘fsequiv |==> fsequiv |==> fsequiv’,
    ‘fset_ABS ---> fset_ABS ---> fset_REP’
  ] >> rpt conj_tac
  >- simp[FUN_REL_def, fsequiv_def] (* respectfulness *)
  >- simp[FUN_EQ_THM, fUNION_def] (* the definition *) >>
  irule funQ >> simp[fsetQ] >> irule funQ >> simp[fsetQ]
QED

Theorem IN_UNION[simp]:
  !e s1 s2. fIN e (fUNION s1 s2) <=> fIN e s1 \/ fIN e s2
Proof
  xfer_back_tac >> simp[]
QED

Definition fEMPTY_def:
  fEMPTY = fset_ABS []
End

Theorem fEMPTY_relates[transfer_rule]:
  FSET0 [] fEMPTY
Proof
  irule HK_thm2 >>
  goal_assum (C (mp_then.mp_then (mp_then.Pos last) mp_tac) fsetQ) >>
  simp[fEMPTY_def, fsequiv_def]
QED

Definition fINSERT_def:
  fINSERT e s = fset_ABS (e :: fset_REP s)
End

Theorem fINSERT_relates[transfer_rule]:
  ((=) |==> FSET0 |==> FSET0) CONS fINSERT
Proof
  irule HK_thm2 >> map_every qexists_tac [
    ‘I ---> fset_REP ---> fset_ABS’,
    ‘(=) |==> fsequiv |==> fsequiv’,
    ‘I ---> fset_ABS ---> fset_REP’
  ] >> rw[]
  >- simp[FUN_REL_def, fsequiv_def]
  >- simp[FUN_EQ_THM, fINSERT_def] >>
  irule funQ >> simp[] >> irule funQ >> simp[fsetQ]
QED

Definition fIN_def:
  fIN e s <=> MEM e (fset_REP s)
End

Theorem fIN_relates[transfer_rule]:
  ((=) |==> FSET0 |==> (=)) MEM fIN
Proof
  irule HK_thm2 >> map_every qexists_tac [
    ‘I ---> fset_REP ---> I’, ‘(=) |==> fsequiv |==> (=)’,
    ‘I ---> fset_ABS ---> I’
  ] >> rw[]
  >- simp[FUN_REL_def, fsequiv_def]
  >- simp[FUN_EQ_THM, fIN_def] >>
  irule funQ >> simp[]>> irule funQ >> simp[fsetQ]
QED


Theorem surj_FSET0[transfer_safe] = MATCH_MP Qt_surj fsetQ
Theorem right_unique_FSET0[transfer_safe] = MATCH_MP Qt_right_unique fsetQ
Theorem FSETEQ[transfer_rule] = MATCH_MP Qt_EQ fsetQ

Theorem fset_cases:
  !s:'a fset. s = fEMPTY \/ ?e s0. s = fINSERT e s0 /\ ~fIN e s0
Proof
  xfer_back_tac >> simp[fsequiv_def] >> Cases >> simp[] >>
  rename [‘e INSERT set L = _ INSERT set _’] >> qexists_tac ‘e’ >>
  qexists_tac ‘FILTER ($~ o (=) e) L’ >>
  simp[MEM_FILTER, LIST_TO_SET_FILTER,
       pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

Theorem fINSERT_duplicates:
  !e s. fINSERT e (fINSERT e s) = fINSERT e s
Proof
  xfer_back_tac >> simp[fsequiv_def]
QED

Theorem fINSERT_commutes:
  !e1 e2 s. fINSERT e1 (fINSERT e2 s) = fINSERT e2 (fINSERT e1 s)
Proof
  xfer_back_tac >> simp[fsequiv_def, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem fset_induction:
  !P. P fEMPTY /\ (!e s. P s /\ ~fIN e s ==> P (fINSERT e s)) ==> !s. P s
Proof
  xfer_back_tac >> qx_gen_tac ‘P’ >> ntac 2 strip_tac >> Induct >> simp[] >>
  qx_gen_tac ‘h’ >> rename [‘P []’, ‘P (h::t)’] >>
  reverse (Cases_on ‘MEM h t’) >- simp[] >>
  ‘fsequiv t (h::t)’ suffices_by metis_tac[] >>
  simp[fsequiv_def, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem NOT_EMPTY_INSERT:
  !h t. fEMPTY <> fINSERT h t
Proof
  xfer_back_tac >> simp[fsequiv_def]
QED

Theorem fUNION_COMM:
  !s1 s2. fUNION s1 s2 = fUNION s2 s1
Proof
  xfer_back_tac >> simp[fsequiv_def, pred_setTheory.UNION_COMM]
QED

Theorem fUNION_ASSOC:
  !s1 s2 s3. fUNION s1 (fUNION s2 s3) = fUNION (fUNION s1 s2) s3
Proof
  xfer_back_tac >> simp[fsequiv_def, pred_setTheory.UNION_ASSOC]
QED

Definition fDELETE_def:
  fDELETE e fs = fset_ABS (FILTER ($~ o $= e) (fset_REP fs))
End

Theorem fDELETE_relates[transfer_rule]:
  ((=) |==> FSET0 |==> FSET0) (\e. FILTER ($~ o $= e)) fDELETE
Proof
  irule HK_thm2 >> map_every qexists_tac [
    ‘I ---> fset_REP ---> fset_ABS’, ‘(=) |==> fsequiv |==> fsequiv’,
    ‘I ---> fset_ABS ---> fset_REP’
  ] >> simp[] >> rw[]
  >- simp[FUN_REL_def, fsequiv_def, LIST_TO_SET_FILTER]
  >- simp[FUN_EQ_THM, fDELETE_def] >>
  irule funQ >> simp[] >> irule funQ >> simp[fsetQ]
QED

Definition fCARD_def:
  fCARD fs = LENGTH (nub (fset_REP fs))
End

Theorem fCARD_relates[transfer_rule]:
  (FSET0 |==> $=) (LENGTH o nub) fCARD
Proof
  irule HK_thm2 >> map_every qexists_tac [
    ‘fset_REP ---> I’, ‘fsequiv |==> (=)’, ‘fset_ABS ---> I’
  ] >> simp[] >> rw[]
  >- (simp[FUN_REL_def, fsequiv_def] >>
      Induct>> rw[nub_def]
      >- metis_tac[pred_setTheory.ABSORPTION_RWT] >>
      ‘MEM h b’ by metis_tac[pred_setTheory.IN_INSERT] >>
      pop_assum (strip_assume_tac o
                 SIMP_RULE (srw_ss()) [Once MEM_SPLIT_APPEND_first]) >>
      rw[length_nub_append, nub_def] >>
      qabbrev_tac ‘b' = pfx ++ FILTER (\x. ~MEM x pfx /\ x <> h) sfx’ >>
      ‘set a = set b'’
        by (simp[Abbr‘b'’, LIST_TO_SET_FILTER, pred_setTheory.EXTENSION]>>
            fs[pred_setTheory.EXTENSION] >> metis_tac[]) >>
      ‘LENGTH (nub b') = LENGTH (nub a)’ by metis_tac[] >>
      fs[Abbr‘b'’, length_nub_append, rich_listTheory.FILTER_FILTER] >>
      pop_assum mp_tac >> csimp[])
  >- simp[FUN_EQ_THM, fCARD_def] >>
  irule funQ >> simp[fsetQ]
QED

Theorem fCARD_THM[simp]:
  fCARD fEMPTY = 0 /\
  !e s. fCARD (fINSERT e s) = 1 + fCARD (fDELETE e s)
Proof
  xfer_back_tac >> simp[nub_def] >> rpt strip_tac >>
  rename [‘MEM h t’] >> rw[]
  >- (fs[Once MEM_SPLIT_APPEND_first] >>
      csimp[length_nub_append, nub_def, FILTER_APPEND_DISTRIB,
            MEM_FILTER, rich_listTheory.FILTER_FILTER] >>
      rename [‘~MEM h pfx’] >>
      ‘FILTER ($~ o $= h) pfx = pfx’ suffices_by (simp[] >> simp[EQ_SYM_EQ]) >>
      rw[] >> pop_assum mp_tac >> Induct_on ‘pfx’ >> simp[]) >>
  rename [‘~MEM h list’] >>
  ‘FILTER ($~ o $= h) list = list’ suffices_by (simp[] >> simp[EQ_SYM_EQ]) >>
  rw[] >> pop_assum mp_tac >> Induct_on ‘list’ >> simp[]
QED

Definition fIMAGE_def:
  fIMAGE f s = fset_ABS (MAP f (fset_REP s))
End

Theorem fIMAGE_relates[transfer_rule]:
  (((=) |==> (=)) |==> FSET0 |==> FSET0) MAP fIMAGE
Proof
  irule HK_thm2 >> map_every qexists_tac [
    ‘I ---> fset_REP ---> fset_ABS’, ‘(=) |==> fsequiv |==> fsequiv’,
    ‘I ---> fset_ABS ---> fset_REP’
  ] >> rw[]
  >- simp[FUN_REL_def, fsequiv_def, LIST_TO_SET_MAP]
  >- simp[fIMAGE_def, FUN_EQ_THM] >>
  ntac 2 (irule funQ >> simp[fsetQ])
QED

Theorem fIMAGE_thm[simp]:
  (!f. fIMAGE (f:'a -> 'b) fEMPTY = fEMPTY) /\
  (!(f:'a -> 'b) e s. fIMAGE f (fINSERT e s) = fINSERT (f e) (fIMAGE f s))
Proof
  xfer_back_tac >> simp[fsequiv_def]
QED

Definition fINTER_def:
  fINTER s1 s2 = fset_ABS (FILTER (\x. MEM x (fset_REP s2)) (fset_REP s1))
End

Theorem fINTER_relates[transfer_rule]:
  (FSET0 |==> FSET0 |==> FSET0) (\l1 l2. FILTER (combin$C MEM l2) l1) fINTER
Proof
  irule HK_thm2 >> map_every qexists_tac [
    ‘fset_REP ---> fset_REP ---> fset_ABS’, ‘fsequiv |==> fsequiv |==> fsequiv’,
    ‘fset_ABS ---> fset_ABS ---> fset_REP’
  ] >> rw[]
  >- simp[FUN_REL_def, fsequiv_def, LIST_TO_SET_FILTER]
  >- simp[fINTER_def, FUN_EQ_THM, combinTheory.C_DEF] >>
  ntac 2 (irule funQ >> simp[fsetQ])
QED

Theorem IN_INTER[simp]:
  !e s1 s2. fIN e (fINTER s1 s2) <=> fIN e s1 /\ fIN e s2
Proof
  xfer_back_tac >> simp[MEM_FILTER, CONJ_COMM]
QED

Definition fDIFF_def:
  fDIFF s1 s2 = fset_ABS (FILTER (\x. ~MEM x (fset_REP s2)) (fset_REP s1))
End

Theorem fDIFF_relates[transfer_rule]:
  (FSET0 |==> FSET0 |==> FSET0) (\l1 l2. FILTER (\x. ~MEM x l2) l1) fDIFF
Proof
  irule HK_thm2 >> map_every qexists_tac [
    ‘fset_REP ---> fset_REP ---> fset_ABS’, ‘fsequiv |==> fsequiv |==> fsequiv’,
    ‘fset_ABS ---> fset_ABS ---> fset_REP’
  ] >> rw[]
  >- simp[FUN_REL_def, fsequiv_def, LIST_TO_SET_FILTER]
  >- simp[fDIFF_def, FUN_EQ_THM] >>
  ntac 2 (irule funQ >> simp[fsetQ])
QED

Theorem IN_DIFF[simp]:
  !e s1 s2. fIN e (fDIFF s1 s2) <=> fIN e s1 /\ ~fIN e s2
Proof
  xfer_back_tac >> simp[MEM_FILTER, CONJ_COMM]
QED

Theorem NOT_IN_EMPTY[simp]:
  !e. ~fIN e fEMPTY
Proof
  xfer_back_tac >> simp[]
QED

Theorem IN_INSERT[simp]:
  !e1 e2 s. fIN e1 (fINSERT e2 s) <=> e1 = e2 \/ fIN e1 s
Proof
  xfer_back_tac >> simp[]
QED

Theorem EXTENSION:
  !s1 s2. (s1 = s2) <=> !e. fIN e s1 <=> fIN e s2
Proof
  xfer_back_tac >> simp[fsequiv_def, pred_setTheory.EXTENSION]
QED

val _ = export_theory();
