open HolKernel Parse boolLib bossLib;
open quotient

open listTheory liftingTheory transferTheory transferLib finite_mapTheory

val _ = new_theory "finite_set";

Theorem psEXTENSION[local] = pred_setTheory.EXTENSION

Theorem RSUBSET_I:
  R1 RSUBSET R2 ==> R1 x y ==> R2 x y
Proof
  simp[relationTheory.RSUBSET]
QED


Theorem FUN_REL_O:
  ((D1 |==> R1) O (D2 |==> R2)) RSUBSET ((D1 O D2) |==> (R1 O R2))
Proof
  simp[FUN_REL_def, relationTheory.O_DEF, relationTheory.RSUBSET] >> metis_tac[]
QED

Theorem RSUBSET_REFL[simp]:
  R RSUBSET R
Proof
  simp[relationTheory.RSUBSET]
QED

Theorem FUN_REL_RSUBSET[simp]:
  D2 RSUBSET D1 /\ R1 RSUBSET R2 ==> (D1 |==> R1) RSUBSET (D2 |==> R2)
Proof
  simp[relationTheory.RSUBSET, FUN_REL_def]>>metis_tac[]
QED

fun INTRO th =
    goal_assum (resolve_then.resolve_then resolve_then.Any mp_tac th)

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

Overload fromList = “fset_ABS”
Theorem fromList_11[simp]:
  fromList l1 = fromList l2 <=> fsequiv l1 l2
Proof
  simp[definition "fset_ABS_def"] >>
  metis_tac[bijection2, fsequiv_equiv, quotientTheory.EQUIV_def]
QED
Theorem fset_ABS_11 = fromList_11

Definition FSET_def:
  FSET AB al bfs <=> ?bl. LIST_REL AB al bl /\ bfs = fset_ABS bl
End

Theorem FSET_AB_eqn:
  FSET AB = FSET (=) O LIST_REL AB
Proof
  simp[FSET_def, FUN_EQ_THM, relationTheory.O_DEF]
QED

Theorem FSET_right_unique[transfer_safe]:
  right_unique AB ==> right_unique (FSET AB)
Proof
  simp[FSET_def, PULL_EXISTS, right_unique_def] >>
  metis_tac[LIST_REL_right_unique, right_unique_def, fsequiv_refl]
QED

Theorem FSET_surj[transfer_safe]:
  surj AB ==> surj (FSET AB)
Proof
  simp[FSET_def, surj_def] >> metis_tac[fset_ABS_onto, LIST_REL_surj, surj_def]
QED

Theorem total_FSET[transfer_safe]:
  total AB ==> total (FSET AB)
Proof
  simp[total_def, FSET_def] >> metis_tac[LIST_REL_total, total_def]
QED

Theorem RDOM_FSET0[simp,transfer_simp]:
  RDOM (FSET AB) = \al. !x. MEM x al ==> RDOM AB x
Proof
  simp[psEXTENSION, IN_DEF, relationTheory.RDOM_DEF, FSET_def] >>
  Induct >> simp[] >> simp[IN_DEF, relationTheory.RDOM_DEF] >> metis_tac[]
QED

Theorem fset0Q[simp]:
  Qt fsequiv fset_ABS fset_REP (FSET (=))
Proof
  simp[Qt_def, relationTheory.O_DEF, relationTheory.inv_DEF, FUN_EQ_THM,
       FSET_def]
QED

Overload FSET0[local] = “FSET $=”

(* important for predicates over the new type - generic version of this
   should be proved *)
Theorem RDOM_FSET0set[simp,transfer_simp]:
  RDOM (FSET0 |==> ($= : bool -> bool -> bool)) =
    \lP. (!l1 l2. lP l1 /\ fsequiv l1 l2 ==> lP l2)
Proof
  rw[relationTheory.RDOM_DEF, Once FUN_EQ_THM, FUN_REL_def, FSET_def] >>
  eq_tac >> rw[]
  >- metis_tac[fset_ABS_11] >>
  qexists_tac ‘\fs. lP (fset_REP fs)’ >> simp[] >>
  metis_tac[R_repabs, fsequiv_equiv, quotientTheory.EQUIV_def, fsequiv_refl,
            fset0Q]
QED

Theorem surj_FSET0[transfer_safe] = MATCH_MP Qt_surj fset0Q
Theorem right_unique_FSET0[transfer_safe] = MATCH_MP Qt_right_unique fset0Q
Theorem FSETEQ[transfer_rule] = MATCH_MP Qt_EQ fset0Q

Definition fIN_def:
  fIN = (I ---> fset_REP ---> I) MEM
End
val _ = set_mapped_fixity{
  fixity = Infix(NONASSOC, 425), term_name = "fIN", tok = "∈ᶠ"         (* UOK *)
}
Overload "∉ᶠ" = “\e s. ~(fIN e s)”                                     (* UOK *)
val _ = set_fixity "∉ᶠ" (Infix(NONASSOC, 425))                         (* UOK *)


Theorem MEM_transfers[transfer_rule]:
  bi_unique AB ==> (AB |==> LIST_REL AB |==> (=)) MEM MEM
Proof
  rw[FUN_REL_def] >> fs[LIST_REL_EL_EQN, MEM_EL]>>
  metis_tac[bi_unique_def, right_unique_def, left_unique_def]
QED

Theorem fIN_relates[transfer_rule]:
  bi_unique AB ==> (AB |==> FSET AB |==> (=)) MEM fIN
Proof
  strip_tac >> simp[Once FSET_AB_eqn] >> irule RSUBSET_I >>
  qexists_tac ‘(=) O AB |==> FSET0 O LIST_REL AB |==> (=) O (=)’ >>
  reverse conj_tac >- simp[] >> irule RSUBSET_I >>
  qexists_tac ‘$= O AB |==> ((FSET0 |==> (=)) O (LIST_REL AB |==> (=)))’ >>
  reverse conj_tac >- (irule FUN_REL_RSUBSET >> simp[FUN_REL_O]) >>
  irule RSUBSET_I >> INTRO FUN_REL_O >>
  simp[relationTheory.O_DEF] >> INTRO MEM_transfers >> simp[] >>
  irule HK_thm2 >> INTRO fIN_def >> INTRO funQ >> INTRO funQ >>
  INTRO fset0Q >> INTRO idQ >> INTRO idQ >>
  simp[FUN_REL_def, fsequiv_def]
QED

Theorem EXTENSION:
  !s1 s2. (s1 = s2) <=> !e. fIN e s1 <=> fIN e s2
Proof
  xfer_back_tac >> simp[fsequiv_def, psEXTENSION]
QED

Definition fUNION_def:
  fUNION = (fset_REP ---> fset_REP ---> fset_ABS) APPEND
End

val _ = set_mapped_fixity{
  fixity = Infixl 500, term_name = "fUNION", tok = "∪ᶠ"                (* UOK *)
}

Theorem fUNION_relates[transfer_rule]:
  (FSET0 |==> FSET0 |==> FSET0) APPEND fUNION
Proof
  map_every INTRO [HK_thm2, fUNION_def, funQ, funQ, fset0Q, fset0Q, fset0Q] >>
  (* respectfulness *)
  simp[FUN_REL_def, fsequiv_def]
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
  map_every INTRO [HK_thm2, fEMPTY_def, fset0Q] (* INTRO fsequiv_refl *) >>
  simp[]
QED

Theorem NOT_IN_EMPTY[simp]:
  !e. ~fIN e fEMPTY
Proof
  xfer_back_tac >> simp[]
QED

Definition fINSERT_def:
  fINSERT = (I ---> fset_REP ---> fset_ABS) CONS
End

val _ = add_listform {block_info = (PP.CONSISTENT, 2),
                      cons = "fINSERT",
                      leftdelim = [TOK "{"],
                      nilstr = "fEMPTY",
                      rightdelim = [TOK "}ᶠ"],                         (* UOK *)
                      separator = [TOK ";", BreakSpace(1,0)]}
Overload "∅ᶠ" = “fEMPTY”                                               (* UOK *)

Theorem fINSERT_relates[transfer_rule]:
  ((=) |==> FSET0 |==> FSET0) CONS fINSERT
Proof
  map_every INTRO [HK_thm2, fINSERT_def, funQ, funQ, fset0Q, fset0Q, idQ] >>
  simp[FUN_REL_def, fsequiv_def] (* respectfulness *)
QED

Theorem IN_INSERT[simp]:
  !e1 e2 s. fIN e1 (fINSERT e2 s) <=> e1 = e2 \/ fIN e1 s
Proof
  xfer_back_tac >> simp[]
QED

Theorem IN_KT[local,simp]: !x. x IN K T
Proof simp[IN_DEF]
QED

Theorem fset_cases:
  !s:'a fset. s = fEMPTY \/ ?e s0. s = fINSERT e s0 /\ ~fIN e s0
Proof
  xfer_back_tac >> simp[fsequiv_def, pred_setTheory.SUBSET_DEF] >> Cases >>
  simp[] >>
  rename [‘e INSERT set L = _ INSERT set _’] >> qexists_tac ‘e’ >>
  qexists_tac ‘FILTER ($~ o (=) e) L’ >>
  simp[MEM_FILTER, LIST_TO_SET_FILTER,
       psEXTENSION] >>
  metis_tac[]
QED

Theorem fINSERT_duplicates[simp]:
  !e s. fINSERT e (fINSERT e s) = fINSERT e s
Proof
  xfer_back_tac >> simp[fsequiv_def]
QED

Theorem fINSERT_commutes:
  !e1 e2 s. fINSERT e1 (fINSERT e2 s) = fINSERT e2 (fINSERT e1 s)
Proof
  xfer_back_tac >> simp[fsequiv_def, psEXTENSION] >> metis_tac[]
QED

Theorem fset_induction:
  !P. P fEMPTY /\ (!e s. P s /\ ~fIN e s ==> P (fINSERT e s)) ==> !s. P s
Proof
  xfer_back_tac >> qx_gen_tac ‘P’ >> ntac 2 strip_tac >> Induct >> simp[] >>
  qx_gen_tac ‘h’ >> rename [‘P []’, ‘P (h::t)’] >>
  reverse (Cases_on ‘MEM h t’) >- simp[] >>
  ‘fsequiv t (h::t)’ suffices_by metis_tac[] >>
  simp[fsequiv_def, psEXTENSION] >> metis_tac[]
QED


Theorem NOT_EMPTY_INSERT[simp]:
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
  fDELETE = (I ---> fset_REP ---> fset_ABS) (\e. FILTER ($~ o $= e))
End

Theorem fDELETE_relates[transfer_rule]:
  ((=) |==> FSET0 |==> FSET0) (\e. FILTER ($~ o $= e)) fDELETE
Proof
  map_every INTRO [HK_thm2, fDELETE_def, funQ, funQ, fset0Q, fset0Q, idQ] >>
  (* respectfulness *)
  simp[FUN_REL_def, fsequiv_def, LIST_TO_SET_FILTER]
QED

Theorem fDELETE_nonelement[simp]:
  !e s. ~fIN e s ==> fDELETE e s = s
Proof
  xfer_back_tac >> simp[fsequiv_def, psEXTENSION, MEM_FILTER] >>
  metis_tac[]
QED

Theorem IN_DELETE[simp]:
  !a b s. fIN a (fDELETE b s) <=> a <> b /\ fIN a s
Proof
  xfer_back_tac >> simp[MEM_FILTER] >> metis_tac[]
QED

Theorem INSERT_DELETE[simp]:
  !e s. fINSERT e (fDELETE e s) = fINSERT e s
Proof
  simp[EXTENSION] >> metis_tac[]
QED

Theorem DELETE_EMPTY[simp]:
  !e. fDELETE e fEMPTY = fEMPTY
Proof
  simp[EXTENSION]
QED

Definition fCARD_def:
  fCARD = (fset_REP ---> I) (LENGTH o nub)
End

Theorem fCARD_relates[transfer_rule]:
  (FSET0 |==> $=) (LENGTH o nub) fCARD
Proof
  map_every INTRO [HK_thm2, fCARD_def, funQ, idQ, fset0Q] >>
  simp[fsequiv_def, FUN_REL_def] >>
  (* respectfulness *)
  Induct>> rw[nub_def]
  >- metis_tac[pred_setTheory.ABSORPTION_RWT] >>
  ‘MEM h b’ by metis_tac[pred_setTheory.IN_INSERT] >>
  pop_assum (strip_assume_tac o
             SIMP_RULE (srw_ss()) [Once MEM_SPLIT_APPEND_first]) >>
  rw[length_nub_append, nub_def] >>
  qabbrev_tac ‘b' = pfx ++ FILTER (\x. ~MEM x pfx /\ x <> h) sfx’ >>
  ‘set a = set b'’
    by (simp[Abbr‘b'’, LIST_TO_SET_FILTER, psEXTENSION]>>
        fs[psEXTENSION] >> metis_tac[]) >>
  ‘LENGTH (nub b') = LENGTH (nub a)’ by metis_tac[] >>
  fs[Abbr‘b'’, length_nub_append, rich_listTheory.FILTER_FILTER] >>
  pop_assum mp_tac >> csimp[]
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

Theorem fCARD_EQ0[simp]:
  !s. fCARD s = 0 <=> s = fEMPTY
Proof
  xfer_back_tac >> simp[fsequiv_def]
QED

Definition fIMAGE_def:
  fIMAGE = ((I ---> I) ---> fset_REP ---> fset_ABS) MAP
End

Theorem MAP_relates[transfer_rule]:
  ((AB |==> CD) |==> LIST_REL AB |==> LIST_REL CD) MAP MAP
Proof
  rw[FUN_REL_def] >>
  rename [‘LIST_REL CD (MAP f l1) (MAP g l2)’] >>
  pop_assum mp_tac >> map_every qid_spec_tac [‘l2’, ‘l1’] >>
  Induct_on ‘LIST_REL’ >> simp[]
QED

Theorem fIMAGE_relates[transfer_rule]:
  ((AB |==> CD) |==> FSET AB |==> FSET CD) MAP fIMAGE
Proof
  irule RSUBSET_I >> INTRO FUN_REL_RSUBSET >>
  simp[Once FSET_AB_eqn, SimpL “FUN_REL”] >>
  simp[Once FSET_AB_eqn, SimpR “FUN_REL”] >>
  INTRO FUN_REL_O >>
  qexists_tac ‘(=) O (AB |==> CD)’ >> conj_tac >- simp[] >>
  irule RSUBSET_I >>
  INTRO FUN_REL_O >>
  simp[relationTheory.O_DEF] >> qexists_tac ‘MAP’ >> simp[MAP_relates] >>
  irule HK_thm2 >> rpt (INTRO funQ) >>
  INTRO fIMAGE_def >> simp[] >> rpt (INTRO fset0Q) >>
  INTRO idQ >> simp[FUN_REL_def, fsequiv_def, LIST_TO_SET_MAP]
QED

Theorem fIMAGE_thm[simp]:
  (!f. fIMAGE (f:'a -> 'b) fEMPTY = fEMPTY) /\
  (!(f:'a -> 'b) e s. fIMAGE f (fINSERT e s) = fINSERT (f e) (fIMAGE f s))
Proof
  xfer_back_tac >> simp[fsequiv_def]
QED

Theorem surjfns[transfer_safe]:
  surj AB /\ right_unique AB /\ surj CD ==> surj (AB |==> CD)
Proof
  rw[FUN_REL_def, surj_def, right_unique_def] >>
  qexists_tac ‘\a. let b = @b. AB a b in @c. CD c (y b)’ >>
  metis_tac[]
QED

Theorem IN_IMAGE[simp]:
  !f x s. fIN x (fIMAGE f s) <=> ?y. fIN y s /\ x = f y
Proof
  xfer_back_tac >> simp[MEM_MAP] >> metis_tac[]
QED

Definition fINTER_def:
  fINTER = (fset_REP ---> fset_REP ---> fset_ABS)
           (FILTER o combin$C MEM)
End
val _ = set_mapped_fixity {fixity = Infixl 600, term_name = "fINTER",
                           tok = "∩ᶠ"}                                 (* UOK *)

Theorem fINTER_relates[transfer_rule]:
  (FSET0 |==> FSET0 |==> FSET0) (FILTER o combin$C MEM) fINTER
Proof
  map_every INTRO [HK_thm2, fINTER_def, funQ, funQ, fset0Q, fset0Q, fset0Q] >>
  simp[FUN_REL_def, fsequiv_def, LIST_TO_SET_FILTER]
QED

Theorem IN_INTER[simp]:
  !e s1 s2. fIN e (fINTER s1 s2) <=> fIN e s1 /\ fIN e s2
Proof
  xfer_back_tac >> simp[MEM_FILTER, CONJ_COMM]
QED

Definition fFILTER_def:
  fFILTER = ((I ---> I) ---> fset_REP ---> fset_ABS) FILTER
End

Theorem fFILTER_relates[transfer_rule]:
  (((=) |==> (=)) |==> FSET0 |==> FSET0) FILTER fFILTER
Proof
  INTRO HK_thm2 >> INTRO fFILTER_def >> rpt (INTRO funQ) >> rpt (INTRO idQ) >>
  rpt (INTRO fset0Q) >>
  simp[FUN_REL_def, fsequiv_def, LIST_TO_SET_FILTER]
QED

Theorem fIN_FILTER[simp]:
  !e s P. fIN e (fFILTER P s) <=> fIN e s /\ P e
Proof
  xfer_back_tac >> simp[MEM_FILTER] >> metis_tac[]
QED

Definition fDIFF_def:
  fDIFF = (fset_REP ---> fset_REP ---> fset_ABS)
          (\l1 l2. FILTER (\x. ~MEM x l2) l1)
End

Theorem fDIFF_relates[transfer_rule]:
  (FSET0 |==> FSET0 |==> FSET0) (\l1 l2. FILTER (\x. ~MEM x l2) l1) fDIFF
Proof
  map_every INTRO [HK_thm2, fDIFF_def, funQ, funQ] >>
  rpt (INTRO fset0Q) >>
  simp[FUN_REL_def, fsequiv_def, LIST_TO_SET_FILTER]
QED

Theorem IN_DIFF[simp]:
  !e s1 s2. fIN e (fDIFF s1 s2) <=> fIN e s1 /\ ~fIN e s2
Proof
  xfer_back_tac >> simp[MEM_FILTER, CONJ_COMM]
QED


Definition fset_REL_def:
  fset_REL AB fs1 fs2 <=> !a b. AB a b ==> (fIN a fs1 <=> fIN b fs2)
End

Definition toSet_def:
  toSet fs = { x | fIN x fs }
End

Definition fromSet_def:
  fromSet s = fromList (SET_TO_LIST s)
End

Definition rel_set_def:
  rel_set AB A B <=>
    (!a. a IN A ==> ?b. b IN B /\ AB a b) /\
    (!b. b IN B ==> ?a. a IN A /\ AB a b)
End

Theorem rel_set_empty[simp]:
  rel_set AB {} {}
Proof
  simp[rel_set_def]
QED

Theorem LIST_TO_SET_rel_set:
  (LIST_REL AB |==> rel_set AB) set set
Proof
  simp[FUN_REL_def] >> Induct_on ‘LIST_REL’ >> simp[] >>
  simp[rel_set_def] >> metis_tac[]
QED

Theorem rel_set_RSUBSET:
  bi_unique AB ==>
  rel_set AB RSUBSET (AB |==> (=))
Proof
  simp[rel_set_def, relationTheory.RSUBSET, FUN_REL_def, IN_DEF,
       bi_unique_def, left_unique_def, right_unique_def] >>
  metis_tac[]
QED

Theorem RSUBSET_rel_set:
  bitotal AB ==>
  (AB |==> (=)) RSUBSET rel_set AB
Proof
  simp[rel_set_def, relationTheory.RSUBSET, FUN_REL_def, IN_DEF,
       bitotal_def, total_def, surj_def] >>
  metis_tac[]
QED


Theorem LIST_TO_SET_transfer:
  (LIST_REL AB |==> rel_set AB) set set
Proof
  simp[FUN_REL_def] >> Induct_on ‘LIST_REL’ >> simp[] >>
  simp[rel_set_def] >> metis_tac[]
QED

Theorem toSet_rel_set_relates[transfer_rule]:
  (FSET AB |==> rel_set AB) set toSet
Proof
  simp[Once FSET_AB_eqn] >>
  irule RSUBSET_I >>
  qexists_tac ‘(FSET0 |==> (=)) O (LIST_REL AB |==> rel_set AB)’ >>
  reverse conj_tac
  >- (simp[relationTheory.RSUBSET, relationTheory.O_DEF, FUN_REL_def] >>
      metis_tac[]) >>
  simp[relationTheory.O_DEF] >>
  map_every INTRO [LIST_TO_SET_transfer, HK_thm2, funQ, fset0Q, idQ] >>
  rw[]
  >- (simp[Once FUN_EQ_THM, toSet_def] >>
      simp[psEXTENSION, fIN_def]) >>
  simp[FUN_REL_def, fsequiv_def]
QED

Theorem toSet_relates:
  bi_unique AB ==>
  (FSET AB |==> AB |==> (=)) set toSet
Proof
  strip_tac >> simp[Once FSET_AB_eqn] >>
  irule RSUBSET_I >>
  qexists_tac ‘(FSET0 O LIST_REL AB) |==>
               (((=) |==> (=)) O (AB |==> (=)))’ >> reverse conj_tac
  >- simp[relationTheory.O_DEF, relationTheory.RSUBSET] >>
  irule RSUBSET_I >> INTRO FUN_REL_O >>
  simp[relationTheory.O_DEF] >>
  qexists_tac ‘set’ >>
  conj_tac
  >- (simp[FUN_REL_def, LIST_REL_EL_EQN] >>
      metis_tac[IN_DEF, MEM_EL, bi_unique_def, left_unique_def,
                right_unique_def]) >>
  map_every INTRO [HK_thm2, funQ, idQ, fset0Q] >> conj_tac
  >- simp[toSet_def, FUN_EQ_THM, fIN_def, IN_DEF] >>
  simp[FUN_REL_def, fsequiv_def]
QED

Definition fSIGMA_def:
  fSIGMA f s = SUM_IMAGE f (toSet s)
End

Theorem toSet_thm[simp]:
  toSet fEMPTY = {} /\
  toSet (fINSERT e s) = e INSERT toSet s /\
  toSet (fDELETE e s) = toSet s DELETE e
Proof
  simp[toSet_def, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem FINITE_toSet[simp]:
  !s. FINITE (toSet s)
Proof
  ho_match_mp_tac fset_induction >> simp[toSet_def, pred_setTheory.GSPEC_OR]
QED

Theorem fSIGMA_thm[simp]:
  fSIGMA f fEMPTY = 0 /\
  fSIGMA f (fINSERT e s) = f e + fSIGMA f (fDELETE e s)
Proof
  simp[fSIGMA_def, pred_setTheory.SUM_IMAGE_THM]
QED

val _ = TypeBase.export [
  TypeBasePure.mk_nondatatype_info (
    “:'a fset”, {
      nchotomy = SOME fset_cases,
      induction = SOME fset_induction,
      size = SOME(“fSIGMA”,fSIGMA_thm),
      encode = NONE
    }
  )
]

Definition fBIGUNION_def:
  fBIGUNION = ((MAP fset_REP o fset_REP) ---> fset_ABS) FLAT
End

Theorem Qt_composes:
  Qt R1 Abs1 Rep1 Tf1 /\ Qt R2 Abs2 Rep2 Tf2 ==>
  Qt (inv Tf1 O R2 O Tf1) (Abs2 o Abs1) (Rep1 o Rep2) (Tf2 O Tf1)
Proof
  simp[Qt_def, relationTheory.inv_DEF, relationTheory.O_DEF, FUN_EQ_THM] >>
  metis_tac[]
QED

Theorem MEM_FSET0:
  FSET0 l fs ==> (!a. MEM a l <=> fIN a fs)
Proof
  mp_tac (fIN_relates |> INST_TYPE [beta |-> alpha] |> Q.INST [‘AB’ |-> ‘$=’])>>
  simp[FUN_REL_def]
QED

Theorem LIST_REL_FSET0:
  Qt (LIST_REL fsequiv) (MAP fset_ABS) (MAP fset_REP) (LIST_REL FSET0)
Proof
  simp[listQ]
QED

Theorem LIST_REL_FSET0_Abs:
  LIST_REL FSET0 ll lfs ==> lfs = MAP fset_ABS ll
Proof
  metis_tac[LIST_REL_FSET0, Qt_def]
QED

Theorem FLAT_relates:
  (LIST_REL (LIST_REL AB) |==> LIST_REL AB) FLAT FLAT
Proof
  simp[FUN_REL_def] >> Induct_on ‘LIST_REL’ >> simp[] >>
  metis_tac[LIST_REL_APPEND]
QED

Theorem fBIGUNION_relates[transfer_rule]:
  (FSET (FSET AB) |==> FSET AB) FLAT fBIGUNION
Proof
  simp[Once FSET_AB_eqn, SimpL “FUN_REL”] >>
  simp[Once FSET_AB_eqn, SimpL “FUN_REL”, SimpR “$O”] >>
  simp[LIST_REL_O] >>
  simp[Once FSET_AB_eqn, SimpR “FUN_REL”] >>
  simp[relationTheory.O_ASSOC] >> irule RSUBSET_I >> INTRO FUN_REL_O >>
  simp[relationTheory.O_DEF] >>
  map_every INTRO [FLAT_relates, HK_thm2, fBIGUNION_def, funQ, fset0Q,
                   Qt_composes, fset0Q, listQ, fset0Q] >>
  rw[FUN_REL_def, relationTheory.O_DEF, relationTheory.inv_DEF,PULL_EXISTS]>>
  rename [‘fsequiv (FLAT l1) (FLAT l2)’, ‘LIST_REL _ l1 fsl1’,
          ‘LIST_REL _ l2 fsl2’] >>
  ‘fsl1 = MAP fset_ABS l1 /\ fsl2 = MAP fset_ABS l2’
    by metis_tac[LIST_REL_FSET0_Abs] >>
  fs[fsequiv_def, LIST_TO_SET_MAP, LIST_TO_SET_FLAT] >>
  simp[Once psEXTENSION, PULL_EXISTS] >>
  fs[Once psEXTENSION, EQ_IMP_THM, FORALL_AND_THM, PULL_EXISTS,
     fsequiv_def] >> metis_tac[]
QED

Theorem rel_setEQ[transfer_simp,simp]:
  rel_set $= = $=
Proof
  simp[FUN_EQ_THM, rel_set_def, IN_DEF] >> metis_tac[]
QED

Theorem BIGUNION_relates[transfer_rule]:
  (rel_set (rel_set AB) |==> rel_set AB) BIGUNION BIGUNION
Proof
  simp[FUN_REL_def, rel_set_def] >> metis_tac[]
QED

Theorem left_unique_rel_set[transfer_safe]:
  left_unique AB ==> left_unique (rel_set AB)
Proof
  simp[left_unique_def, rel_set_def] >> rw[] >>
  simp[psEXTENSION] >> metis_tac[]
QED

Theorem right_unique_rel_set[transfer_safe]:
  right_unique AB ==> right_unique (rel_set AB)
Proof
  simp[right_unique_def, rel_set_def] >> rw[] >>
  simp[psEXTENSION] >> metis_tac[]
QED

Theorem set_BIGUNION:
  !fss. toSet (fBIGUNION fss) = BIGUNION (toSet (fIMAGE toSet fss))
Proof
  xfer_back_tac >> simp[LIST_TO_SET_FLAT]
QED



Theorem toSet_11:
  !fs1 fs2. (toSet fs1 = toSet fs2) <=> fs1 = fs2
Proof
  xfer_back_tac >> simp[fsequiv_def]
QED

Theorem toSet_fset_ABS[simp]:
  toSet (fset_ABS l) = set l
Proof
  simp[toSet_def, fIN_def] >>
  simp[definition "fset_REP_def", definition "fset_ABS_def"] >>
  SELECT_ELIM_TAC >> simp[fsequiv_def] >> metis_tac[]
QED

Theorem equalityp_relset[transfer_safe]:
  equalityp AB ==> equalityp (rel_set AB)
Proof
  simp[equalityp_def]
QED

Theorem fIN_IN:
  !e fs. fIN e fs <=> e IN toSet fs
Proof
  xfer_back_tac
QED

Theorem IN_fromSet:
  FINITE s ==> (fIN x (fromSet s) <=> x IN s)
Proof
  simp[fromSet_def, fIN_IN]
QED

Theorem set_IMAGE:
  !f fs. toSet (fIMAGE f fs) = IMAGE f (toSet fs)
Proof
  xfer_back_tac >> simp[LIST_TO_SET_MAP, psEXTENSION]
QED

Theorem IN_BIGUNION:
  fIN e (fBIGUNION fss) = ?fs. fIN fs fss /\ fIN e fs
Proof
  simp[fIN_IN, set_BIGUNION, set_IMAGE, PULL_EXISTS] >> metis_tac[]
QED

Theorem BIGUNION_thm[simp]:
  fBIGUNION fEMPTY = fEMPTY /\
  !s ss. fBIGUNION (fINSERT s ss) = fUNION s (fBIGUNION ss)
Proof
  conj_tac >> dsimp[Once EXTENSION, IN_BIGUNION]
QED

Inductive fITSETr:
  fITSETr f fEMPTY A A /\
  (!e s A0 A1. fITSETr f s A0 A1 /\ ~fIN e s ==>
               fITSETr f (fINSERT e s) A0 (f e A1))
End

val _ = TypeBase.export [
      TypeBasePure.mk_nondatatype_info
        (“:'a fset”,
         {nchotomy = SOME fset_cases,
          induction = SOME fset_induction,
          size = NONE,
          encode=NONE})
    ]

Theorem fITSETr_total:
  !s f a0. ?a. fITSETr f s a0 a
Proof
  Induct >> metis_tac[fITSETr_rules]
QED

Theorem DECOMPOSITION:
  fIN e s <=> ?s0. s = fINSERT e s0 /\ ~fIN e s0
Proof
  Induct_on ‘s’ >> simp[] >> rw[] >> eq_tac >> rw[]
  >- metis_tac[]
  >- (fs[] >> rename [‘fINSERT e1 (fINSERT e2 ss) = fINSERT e2 _’] >>
      qexists_tac ‘fINSERT e1 ss’ >> simp[fINSERT_commutes]) >>
  rename [‘e1 = e2 \/ _’, ‘fINSERT e2 s2 = fINSERT e1 s1’] >>
  Cases_on ‘e1 = e2’ >> simp[] >>
  ‘fIN e1 s2’ by (fs[EXTENSION] >> metis_tac[]) >>
  pop_assum mp_tac >> simp[]
QED

Theorem fITSETr_functional:
  (!x y a. f x (f y a) = f y (f x a)) ==>
  !s a0 a1 a2. fITSETr f s a0 a1 /\ fITSETr f s a0 a2 ==> a1 = a2
Proof
  strip_tac >>
  completeInduct_on ‘fCARD s’ >> fs[PULL_FORALL] >>
  rpt gen_tac >>
  Cases_on ‘fCARD s = 0’ >> fs[] >> strip_tac >>
  ONCE_REWRITE_TAC [fITSETr_cases] >> simp[] >>
  disch_then $ CONJUNCTS_THEN2
                (qx_choosel_then [‘e1’, ‘s1’, ‘A1’] strip_assume_tac)
                (qx_choosel_then [‘e2’, ‘s2’, ‘A2’] strip_assume_tac) >>
  rw[] >> Cases_on ‘e1 = e2’ >> fs[]
  >- (‘s1 = s2’ suffices_by metis_tac[DECIDE “x < x + 1”] >>
      fs[EXTENSION] >> metis_tac[]) >>
  ‘fIN e1 s2 /\ fIN e2 s1’ by metis_tac[IN_INSERT, EXTENSION] >>
  ‘?s0. s1 = fINSERT e2 s0 /\ s2 = fINSERT e1 s0 /\ ~fIN e2 s0 /\ ~fIN e1 s0’
    by (‘?s0. s1 = fINSERT e2 s0 /\ ~fIN e2 s0’ by metis_tac[DECOMPOSITION] >>
        qexists_tac ‘s0’ >> simp[] >> rw[] >> fs[] >>
        qpat_x_assum ‘fINSERT _ _ = fINSERT _ _’ mp_tac >>
        simp[EXTENSION] >> metis_tac[]) >>
  fs[] >> ‘?a00. fITSETr f s0 a0 a00’ by metis_tac[fITSETr_total] >>
  ‘fITSETr f (fINSERT e1 s0) a0 (f e1 a00) /\
   fITSETr f (fINSERT e2 s0) a0 (f e2 a00)’
    by PROVE_TAC[fITSETr_rules] >>
  ‘A1 = f e2 a00 /\ A2 = f e1 a00’ suffices_by metis_tac[] >>
  conj_tac >> first_x_assum irule
  >- (qexistsl_tac [‘a0’, ‘fINSERT e2 s0’] >> simp[]) >>
  qexistsl_tac [‘a0’, ‘fINSERT e1 s0’] >> simp[]
QED

Definition fITSET_def:
  fITSET f s a0 = @a. fITSETr f s a0 a
End

Theorem fITSET_EMPTY[simp]:
  fITSET f fEMPTY a = a
Proof
  simp[fITSET_def, Once fITSETr_cases]
QED

Theorem fITSET_INSERT:
  (!x y a. f x (f y a) = f y (f x a)) ==>
  !e s a. fITSET f (fINSERT e s) a = f e (fITSET f (fDELETE e s) a)
Proof
  simp[fITSET_def] >> rpt strip_tac >> SELECT_ELIM_TAC >>
  conj_tac >- metis_tac[fITSETr_total] >> qx_gen_tac ‘a1’ >>
  SELECT_ELIM_TAC >> conj_tac >- metis_tac[fITSETr_total]>> qx_gen_tac ‘a2’ >>
  strip_tac >>
  drule_then (qspec_then ‘e’ mp_tac)(fITSETr_rules |> SPEC_ALL |> CONJUNCT2) >>
  simp[] >> PROVE_TAC[fITSETr_functional]
QED

Theorem fITSET_INSERT_tail:
  (!x y a. f x (f y a) = f y (f x a)) ==>
  !e s a. fITSET f (fINSERT e s) a = fITSET f (fDELETE e s) (f e a)
Proof
  strip_tac >> Induct_on ‘s’ >> rpt strip_tac >- simp[fITSET_INSERT] >>
  rename [‘fITSET _ (fINSERT e1 (fINSERT e2 _))’] >>
  Cases_on ‘e1 = e2’ >> simp[]
  >- (rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >> simp[EXTENSION] >> metis_tac[]) >>
  ‘fINSERT e1 (fINSERT e2 s) = fINSERT e2 (fINSERT e1 s)’
    by simp[fINSERT_commutes] >>
  pop_assum SUBST1_TAC >> simp[Once fITSET_INSERT] >>
  ‘fDELETE e1 (fINSERT e2 s) = fINSERT e2 (fDELETE e1 s)’
    by (simp[EXTENSION] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >> simp[fITSET_INSERT]
QED

(*
Definition FSET':
  FSET' AB l fs <=> (!a. MEM a l ==> ?b. AB a b /\ fIN b fs) /\
                    (!b. fIN b fs ==> ?a. AB a b /\ MEM a l)
End

Theorem fset_repabs =
  MATCH_MP R_repabs fset0Q |> SIMP_RULE (srw_ss()) [fsequiv_def]

Theorem FSET0:
  FSET' $= = FSET0
Proof
  simp[FSET', FUN_EQ_THM, fIN_def, FSET_def, EQ_IMP_THM] >> rw[fset_repabs] >>
  rename [‘fs = fset_ABS l’] >>
  ‘?l'. fs = fset_ABS l'’ by metis_tac[fset_ABS_onto] >>
  fs[fset_repabs, fsequiv_def, psEXTENSION] >> metis_tac[]
QED

Definition fSUB_def:
  fSUB fs1 fs2 <=> !e. fIN e fs1 ==> fIN e fs2
End

(* opposite direction doesn't hold:
     FSET' AB holds between [a] and set {b1,b2} if AB a b1 & AB a b2 hold
     but there's no LIST_REL possible between a and a list that has both
     b1 and b2 in it
*)
Theorem FSET'_decompose:
  FSET0 O LIST_REL AB RSUBSET FSET' AB
Proof
  simp[FSET', FUN_EQ_THM, relationTheory.O_DEF, fIN_def, FSET_def,
       relationTheory.RSUBSET, PULL_EXISTS, fset_repabs] >>
  simp[LIST_REL_EL_EQN] >> metis_tac[MEM_EL]
QED

Theorem FSET'_total:
  total AB ==> total (FSET' AB)
Proof
  simp[FSET', total_def, fIN_def, surj_def, bi_unique_def,
       right_unique_def] >> rw[] >>
  rename [‘MEM _ l ==> _ ’] >>
  qexists_tac ‘fset_ABS (MAP (\a. @b. AB a b) l)’ >>
  rw[fset_repabs, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem right_unique_fIN_relates[transfer_rule]:
  right_unique AB ==> (AB |==> FSET AB |==> $==>) MEM fIN
Proof
  simp[FUN_REL_def, FSET_def, fIN_def, PULL_EXISTS, fset_repabs,
       right_unique_def] >>
  simp[LIST_REL_EL_EQN] >> metis_tac[MEM_EL]
QED

Theorem IN_BIGUNION:
  !x fss. fIN x (fBIGUNION fss) = ?fs. fIN fs fss /\ fIN x fs
Proof

  xfer_back_tac
*)

Definition ffDOM_def:
  ffDOM fm = fromList (SET_TO_LIST (FDOM fm))
End
Overload "FDOMᶠ" = “ffDOM”

Theorem ffDOM_thm[simp]:
  FDOMᶠ FEMPTY = fEMPTY ∧
  FDOMᶠ (fm |+ (k,v)) = fINSERT k (FDOMᶠ fm)
Proof
  simp[ffDOM_def, EXTENSION, fIN_IN]
QED

Definition ffRANGE_def:
  ffRANGE fm = fromList (SET_TO_LIST (FRANGE fm))
End

Theorem ffRANGE_thm[simp]:
  ffRANGE FEMPTY = ∅ᶠ ∧
  ffRANGE (fm |+ (k,v)) = fINSERT v (ffRANGE (fm \\ k))
Proof
  simp[ffRANGE_def, fIN_IN, EXTENSION]
QED

Definition fSUBSET_def:
  fSUBSET fs1 fs2 <=> !x. fIN x fs1 ==> fIN x fs2
End

Overload "⊆ᶠ" = “fSUBSET”                                              (* UOK *)
val _ = set_fixity "⊆ᶠ" (Infix(NONASSOC, 450))                         (* UOK *)

val _ = export_theory();
