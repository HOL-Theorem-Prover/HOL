open HolKernel Parse boolLib bossLib;
open quotient

open listTheory liftingTheory transferTheory transferLib

val _ = new_theory "finite_set";


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

val GG = GEN_TYVARIFY o GEN_ALL

fun UDISCH' th =
    let
      val (l,r) = dest_imp (concl th)
      fun buildcth t =
          case Lib.total dest_conj t of
              SOME (l,r) => CONJ (buildcth l) (buildcth r)
            | NONE => ASSUME t
    in
      PROVE_HYP (buildcth l) (UNDISCH th)
    end handle HOL_ERR _ => let
      val (bv,_) = dest_forall (concl th)
    in
      SPEC bv th
    end

fun DISCHl tms th =
    let
      val cjt = list_mk_conj tms
    in
      List.foldl (fn (cth, th) => PROVE_HYP cth th) th (CONJUNCTS (ASSUME cjt))
                 |> DISCH cjt
    end

fun Uchain th1 hypth =
    let
      val fixed_tmvs =
          FVL [concl th1, concl hypth]
              (HOLset.union(hyp_frees th1, hyp_frees hypth))
      val fixed_tyvs =
          HOLset.foldl (fn (t, A) => HOLset.addList(A, type_vars_in_term t))
                       (HOLset.union(hyp_tyvars th1, hyp_tyvars hypth))
                       fixed_tmvs |> HOLset.listItems
      val fixed_tmvs_l = HOLset.listItems fixed_tmvs
      val th1' = repeat UDISCH' th1
      val hypth' = repeat UDISCH' hypth
      open optmonad
      fun INSTT (tyi,tmi) th = th |> INST_TYPE tyi |> INST tmi
      fun elimhyp h =
          case FullUnify.Env.fromEmpty
                 (FullUnify.unify fixed_tyvs fixed_tmvs_l (h, concl th1') >>
                  FullUnify.collapse)
           of
              NONE => NONE
            | SOME sigma =>
              SOME (PROVE_HYP (INSTT sigma th1') (INSTT sigma hypth'))
    in
      case Portable.first_opt (fn _ => elimhyp) (hyp hypth') of
          NONE => raise mk_HOL_ERR "transferLib" "Uchain" "No unifier found"
        | SOME newth =>
          let
            val dhyps = HOLset.difference(hypset newth, hypset hypth)
          in
            newth |> DISCHl (HOLset.listItems dhyps) |> GEN_ALL
          end
    end

fun INTRO th = goal_assum (mp_tac o Uchain (GG th))

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

Theorem fset_ABS_11[simp]:
  fset_ABS l1 = fset_ABS l2 <=> fsequiv l1 l2
Proof
  rw[EQ_IMP_THM, definition "fset_ABS_def"]
  >- (pop_assum (mp_tac o Q.AP_TERM ‘fset_REP_CLASS’) >>
      simp[bijection2, Excl "REP_CLASS_11"]) >>
  ‘fsequiv l1 = fsequiv l2’ suffices_by metis_tac[bijection2, REP_CLASS_11] >>
  metis_tac[fsequiv_equiv, quotientTheory.EQUIV_def]
QED

Theorem total_FSET[transfer_safe]:
  total AB ==> total (FSET AB)
Proof
  simp[total_def, FSET_def] >> metis_tac[LIST_REL_total, total_def]
QED

Theorem RDOM_FSET0[simp,transfer_simp]:
  RDOM (FSET AB) = \al. !x. MEM x al ==> RDOM AB x
Proof
  simp[pred_setTheory.EXTENSION, IN_DEF, relationTheory.RDOM_DEF, FSET_def] >>
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
  irule RSUBSET_I >> goal_assum (mp_tac o Uchain (GG FUN_REL_O)) >>
  simp[relationTheory.O_DEF] >>
  goal_assum (mp_tac o Uchain (GG MEM_transfers)) >> simp[] >>
  irule HK_thm2 >>
  goal_assum (mp_tac o Uchain (GG fIN_def)) >>
  goal_assum (mp_tac o Uchain (GG funQ)) >>
  goal_assum (mp_tac o Uchain (GG funQ)) >>
  goal_assum (mp_tac o Uchain (GG fset0Q)) >>
  goal_assum (mp_tac o Uchain (GG idQ)) >>
  goal_assum (mp_tac o Uchain (GG idQ)) >>
  simp[FUN_REL_def, fsequiv_def]
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
  irule HK_thm2 >>
  goal_assum (mp_tac o Uchain (GG fUNION_def)) >>
  ntac 2 (goal_assum (mp_tac o Uchain (GG funQ))) >>
  ntac 2 (goal_assum (mp_tac o Uchain (GG fset0Q))) >>
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
  irule HK_thm2 >>
  goal_assum (mp_tac o Uchain (GG fEMPTY_def)) >>
  goal_assum (mp_tac o Uchain (GG fset0Q)) >>
  simp[]
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
  irule HK_thm2 >>
  goal_assum (mp_tac o Uchain (GG fINSERT_def)) >>
  ntac 2 (goal_assum (mp_tac o Uchain (GG funQ))) >>
  ntac 2 (goal_assum (mp_tac o Uchain (GG fset0Q))) >>
  goal_assum (mp_tac o Uchain (GG idQ)) >>
  simp[FUN_REL_def, fsequiv_def] (* respectfulness *)
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
  irule HK_thm2 >>
  goal_assum (mp_tac o Uchain (GG fDELETE_def)) >>
  ntac 2 (goal_assum (mp_tac o Uchain (GG funQ))) >>
  ntac 2 (goal_assum (mp_tac o Uchain (GG fset0Q))) >>
  goal_assum (mp_tac o Uchain (GG idQ)) >>
  (* respectfulness *)
  simp[FUN_REL_def, fsequiv_def, LIST_TO_SET_FILTER]
QED

Theorem IN_DELETE[simp]:
  !e1 e2 s. fIN e1 (fDELETE e2 s) <=> e1 <> e2 /\ fIN e1 s
Proof
  xfer_back_tac >> simp[MEM_FILTER] >> metis_tac[]
QED

Definition fCARD_def:
  fCARD = (fset_REP ---> I) (LENGTH o nub)
End

Theorem fCARD_relates[transfer_rule]:
  (FSET0 |==> $=) (LENGTH o nub) fCARD
Proof
  irule HK_thm2 >> INTRO fCARD_def >> INTRO funQ >> INTRO idQ >> INTRO fset0Q >>
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
    by (simp[Abbr‘b'’, LIST_TO_SET_FILTER, pred_setTheory.EXTENSION]>>
        fs[pred_setTheory.EXTENSION] >> metis_tac[]) >>
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
  irule HK_thm2 >>
  goal_assum (mp_tac o Uchain (GG fINTER_def)) >>
  rpt (goal_assum (mp_tac o Uchain (GG funQ))) >>
  rpt (goal_assum (mp_tac o Uchain (GG idQ))) >>
  rpt (goal_assum (mp_tac o Uchain (GG fset0Q))) >>
  simp[] >>
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
  irule HK_thm2 >>
  goal_assum (mp_tac o Uchain (GG fFILTER_def)) >>
  rpt (goal_assum (mp_tac o Uchain (GG funQ))) >>
  rpt (goal_assum (mp_tac o Uchain (GG idQ))) >>
  rpt (goal_assum (mp_tac o Uchain (GG fset0Q))) >>
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
  irule HK_thm2 >>
  goal_assum (mp_tac o Uchain (GG fDIFF_def)) >>
  rpt (goal_assum (mp_tac o Uchain (GG funQ))) >>
  rpt (goal_assum (mp_tac o Uchain (GG idQ))) >>
  rpt (goal_assum (mp_tac o Uchain (GG fset0Q))) >>
  simp[] >>
  simp[FUN_REL_def, fsequiv_def, LIST_TO_SET_FILTER]
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

Definition fset_REL_def:
  fset_REL AB fs1 fs2 <=> !a b. AB a b ==> (fIN a fs1 <=> fIN b fs2)
End

Definition toSet_def:
  toSet fs = { x | fIN x fs }
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
  goal_assum (mp_tac o Uchain (GG LIST_TO_SET_transfer)) >>
  irule HK_thm2 >>
  goal_assum (mp_tac o Uchain (GG funQ)) >>
  goal_assum (mp_tac o Uchain (GG fset0Q)) >>
  goal_assum (mp_tac o Uchain (GG idQ)) >> simp[] >> rw[]
  >- (simp[Once FUN_EQ_THM, toSet_def] >>
      simp[pred_setTheory.EXTENSION, fIN_def]) >>
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
  irule RSUBSET_I >>
  goal_assum (mp_tac o Uchain (GG FUN_REL_O)) >>
  simp[relationTheory.O_DEF] >>
  qexists_tac ‘set’ >>
  conj_tac
  >- (simp[FUN_REL_def, LIST_REL_EL_EQN] >>
      metis_tac[IN_DEF, MEM_EL, bi_unique_def, left_unique_def,
                right_unique_def]) >>
  irule HK_thm2 >>
  goal_assum (mp_tac o Uchain (GG funQ)) >>
  goal_assum (mp_tac o Uchain (GG idQ)) >>
  goal_assum (mp_tac o Uchain (GG fset0Q)) >> conj_tac
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
  simp[relationTheory.O_ASSOC] >> irule RSUBSET_I >>
  goal_assum (mp_tac o Uchain (GG FUN_REL_O)) >>
  simp[relationTheory.O_DEF] >>
  goal_assum (mp_tac o Uchain (GG FLAT_relates)) >>
  irule HK_thm2 >>
  goal_assum (mp_tac o Uchain (GG fBIGUNION_def)) >>
  goal_assum (mp_tac o Uchain (GG funQ)) >>
  goal_assum (mp_tac o Uchain (GG fset0Q)) >>
  goal_assum (mp_tac o Uchain (GG Qt_composes)) >>
  goal_assum (mp_tac o Uchain (GG fset0Q)) >>
  goal_assum (mp_tac o Uchain (GG listQ)) >>
  goal_assum (mp_tac o Uchain (GG fset0Q)) >>
  rw[FUN_REL_def, relationTheory.O_DEF, relationTheory.inv_DEF,PULL_EXISTS]>>
  rename [‘fsequiv (FLAT l1) (FLAT l2)’, ‘LIST_REL _ l1 fsl1’,
          ‘LIST_REL _ l2 fsl2’] >>
  ‘fsl1 = MAP fset_ABS l1 /\ fsl2 = MAP fset_ABS l2’
    by metis_tac[LIST_REL_FSET0_Abs] >>
  fs[fsequiv_def, LIST_TO_SET_MAP, LIST_TO_SET_FLAT] >>
  simp[Once pred_setTheory.EXTENSION, PULL_EXISTS] >>
  fs[Once pred_setTheory.EXTENSION, EQ_IMP_THM, FORALL_AND_THM, PULL_EXISTS,
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
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem right_unique_rel_set[transfer_safe]:
  right_unique AB ==> right_unique (rel_set AB)
Proof
  simp[right_unique_def, rel_set_def] >> rw[] >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
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

Theorem set_IMAGE:
  !f fs. toSet (fIMAGE f fs) = IMAGE f (toSet fs)
Proof
  xfer_back_tac >> simp[LIST_TO_SET_MAP, pred_setTheory.EXTENSION]
QED

Theorem IN_BIGUNION:
  fIN e (fBIGUNION fss) = ?fs. fIN fs fss /\ fIN e fs
Proof
  simp[fIN_IN, set_BIGUNION, set_IMAGE, PULL_EXISTS] >> metis_tac[]
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
  fs[fset_repabs, fsequiv_def, pred_setTheory.EXTENSION] >> metis_tac[]
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

val _ = export_theory();
