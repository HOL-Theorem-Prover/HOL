Theory grammar
Ancestors
  list pred_set finite_map location relation
Libs
  boolSimps

val FLAT_APPEND = rich_listTheory.FLAT_APPEND
val rveq = rpt BasicProvers.VAR_EQ_TAC
fun asm_match q = Q.MATCH_ASSUM_RENAME_TAC q

val _ = type_abbrev("inf", ``:'a + num``)
Datatype: symbol = TOK 'a | NT ('b inf)
End

Definition isTOK_def[simp]:
  (isTOK (TOK tok) = T) ∧ (isTOK (NT n) = F)
End

Definition destTOK_def[simp]:
  (destTOK (TOK tk, _) = SOME tk) ∧
  (destTOK _ = NONE)
End

Datatype:
  grammar = <|
   start : 'b inf;
   rules : 'b inf |-> ('a,'b)symbol list set
  |>
End

Datatype:
  parsetree = Lf (('a,'b) symbol # 'locs)
            | Nd ('b inf # 'locs) (parsetree list)
End

Definition ptree_loc_def:
  ptree_loc (Lf(_,l)) = l ∧
  ptree_loc (Nd(_,l) _) = l
End

Definition ptree_list_loc_def:
  ptree_list_loc l = merge_list_locs (MAP ptree_loc l)
End

Definition ptree_head_def[simp]:
  (ptree_head (Lf (tok,l)) = tok) ∧
  (ptree_head (Nd (nt,l) children) = NT nt)
End

Definition valid_ptree_def[simp,nocompute]:
  (valid_ptree G (Lf _) ⇔ T) ∧
  (valid_ptree G (Nd (nt,l) children) ⇔
    nt ∈ FDOM G.rules ∧ MAP ptree_head children ∈ G.rules ' nt ∧
    ∀pt. pt ∈ set children ⇒ valid_ptree G pt)
End

Definition ptree_fringe_def:
  (ptree_fringe (Lf (t,_)) = [t]) ∧
  (ptree_fringe (Nd _ children) = FLAT (MAP ptree_fringe children))
End

Theorem ptree_fringe_def[simp,compute,allow_rebind] =
  CONV_RULE (DEPTH_CONV ETA_CONV) ptree_fringe_def

Definition complete_ptree_def:
  complete_ptree G pt ⇔
    valid_ptree G pt ∧ ptree_head pt = NT G.start ∧
    ∀t. t ∈ set (ptree_fringe pt) ⇒ isTOK t
End

(* loc-free parse tree *)
Type lfptree = “:(α,β,one) parsetree”

Definition real_fringe_def[simp]:
  (real_fringe (Lf t) = [t]) ∧
  (real_fringe (Nd n ptl) = FLAT (MAP real_fringe ptl))
End

Theorem MAP_TKI_11[simp]:
  (MAP (TOK ## I) l1 = MAP (TOK ## I) l2) ⇔ (l1 = l2)
Proof simp[listTheory.INJ_MAP_EQ_IFF, pred_setTheory.INJ_DEF, pairTheory.FORALL_PROD]
QED

Theorem ptree_fringe_real_fringe:
   ∀pt. ptree_fringe pt = MAP FST (real_fringe pt)
Proof
  ho_match_mp_tac real_fringe_ind >>
  simp[pairTheory.FORALL_PROD, MAP_FLAT, MAP_MAP_o, combinTheory.o_ABS_R] >>
  rpt strip_tac >> AP_TERM_TAC >> simp[MAP_EQ_f]
QED

Theorem LENGTH_real_fringe:
   ∀pt. LENGTH (real_fringe pt) = LENGTH (ptree_fringe pt)
Proof
  simp[ptree_fringe_real_fringe]
QED

val real_fringe_NIL_ptree_fringe = Q.prove(
  `∀pt. real_fringe pt = [] ⇔ ptree_fringe pt = []`,
  simp[ptree_fringe_real_fringe]);

val real_fringe_CONS_ptree_fringe = Q.prove(
  `∀pt rest. real_fringe pt = (TOK t, l) :: rest ⇒
             ∃rest'. ptree_fringe pt = TOK t :: rest'`,
  simp[ptree_fringe_real_fringe]);

Definition valid_locs_def[simp]:
  (valid_locs (Lf _) ⇔ T) ∧
  (valid_locs (Nd (_, l) children) ⇔
     l = merge_list_locs (MAP ptree_loc children) ∧
     ∀pt. MEM pt children ⇒ valid_locs pt)
End

Definition valid_lptree_def:
  valid_lptree G pt ⇔ valid_locs pt ∧ valid_ptree G pt
End

Theorem valid_lptree_thm[simp]:
  (valid_lptree G (Lf p) ⇔ T) ∧
  (valid_lptree G (Nd (n, l) children) ⇔
      l = merge_list_locs (MAP ptree_loc children) ∧
      n ∈ FDOM G.rules ∧ MAP ptree_head children ∈ G.rules ' n ∧
      ∀pt. MEM pt children ⇒ valid_lptree G pt)
Proof simp[valid_lptree_def] >> metis_tac[]
QED

Definition language_def:
  language G =
   { ts |
     ∃pt:(α,β)lfptree. complete_ptree G pt ∧ ptree_fringe pt = MAP TOK ts }
End

Definition derive_def:
  derive G sf1 sf2 ⇔
    ∃p sym rhs s. sf1 = p ++ [NT sym] ++ s ∧ sf2 = p ++ rhs ++ s ∧
                  sym ∈ FDOM G.rules ∧ rhs ∈ G.rules ' sym
End

val RTC1 = RTC_RULES |> Q.SPEC `R` |> CONJUNCT2 |> Q.GEN `R`
val qxch = Q.X_CHOOSE_THEN
fun qxchl [] ttac = ttac
  | qxchl (q::qs) ttac = qxch q (qxchl qs ttac)

Theorem derive_common_prefix:
    derive G sf1 sf2 ⇒ derive G (p ++ sf1) (p ++ sf2)
Proof
  rw[derive_def] >> metis_tac [APPEND_ASSOC]
QED
Theorem derive_common_suffix:
    derive G sf1 sf2 ⇒ derive G (sf1 ++ s) (sf2 ++ s)
Proof
  rw[derive_def] >> metis_tac [APPEND_ASSOC]
QED

Overload derives = “λG. RTC (derive G)”
Theorem derive_paste_horizontally:
  derive G sf11 sf12 ∧ derive G sf21 sf22 ⇒ derives G (sf11 ++ sf21) (sf12 ++ sf22)
Proof metis_tac [derive_common_prefix, derive_common_suffix,
                 RTC_RULES]
QED

Theorem derive_1NT[simp]: derive G [NT s] l ⇔ s ∈ FDOM G.rules ∧ l ∈ G.rules ' s
Proof rw[derive_def, APPEND_EQ_CONS]
QED

Theorem derives_common_prefix:
  ∀sf1 sf2 p. derives G sf1 sf2 ⇒ derives G (p ++ sf1) (p ++ sf2)
Proof
  simp[GSYM PULL_FORALL] >>
  ho_match_mp_tac RTC_INDUCT >> rw[] >>
  metis_tac [RTC_RULES, derive_common_prefix]
QED
Theorem derives_common_suffix:
  ∀sf1 sf2 s. derives G sf1 sf2 ⇒ derives G (sf1 ++ s) (sf2 ++ s)
Proof
  simp[GSYM PULL_FORALL] >>
  ho_match_mp_tac RTC_INDUCT >> rw[] >>
  metis_tac [RTC_RULES, derive_common_suffix]
QED

Theorem derives_paste_horizontally:
  derives G sf11 sf12 ∧ derives G sf21 sf22 ⇒ derives G (sf11 ++ sf21) (sf12 ++ sf22)
Proof metis_tac [RTC_CASES_RTC_TWICE, derives_common_suffix, derives_common_prefix]
QED

Theorem ptree_ind =
  TypeBase.induction_of ``:('a,'b,'l)parsetree``
     |> Q.SPECL [`P`, `λl. ∀pt. MEM pt l ⇒ P pt`]
     |> SIMP_RULE (srw_ss() ++ CONJ_ss) []
     |> SIMP_RULE (srw_ss()) [DISJ_IMP_THM, FORALL_AND_THM]
     |> Q.GEN `P`;

Theorem valid_ptree_derive:
  ∀pt. valid_ptree G pt ⇒ derives G [ptree_head pt] (ptree_fringe pt)
Proof
  ho_match_mp_tac ptree_ind >> rw[] >> Cases_on`pt` >> fs[] >>
  match_mp_tac RTC1 >> qexists_tac `MAP ptree_head l` >> rw[] >>
  qpat_x_assum `SS ∈ G.rules ' s` (K ALL_TAC) >> Induct_on `l` >> rw[] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  metis_tac [derives_paste_horizontally, APPEND]
QED

Theorem FLAT_EQ_APPEND:
  FLAT l = x ++ y ⇔
    (∃p s. l = p ++ s ∧ x = FLAT p ∧ y = FLAT s) ∨
    (∃p s ip is.
       l = p ++ [ip ++ is] ++ s ∧ ip ≠ [] ∧ is ≠ [] ∧
       x = FLAT p ++ ip ∧
       y = is ++ FLAT s)
Proof
  reverse eq_tac >- (rw[] >> rw[rich_listTheory.FLAT_APPEND]) >>
  map_every qid_spec_tac [`y`,`x`,`l`] >> Induct_on `l` >- simp[] >>
  simp[] >> map_every qx_gen_tac [`h`, `x`, `y`] >>
  simp[APPEND_EQ_APPEND] >>
  disch_then (DISJ_CASES_THEN (qxch `m` strip_assume_tac))
  >- (Cases_on `x = []`
      >- (fs[] >> map_every qexists_tac [`[]`, `m::l`] >> simp[]) >>
      Cases_on `m = []`
      >- (fs[] >> disj1_tac >> map_every qexists_tac [`[x]`, `l`] >>
          simp[]) >>
      disj2_tac >>
      map_every qexists_tac [`[]`, `l`, `x`, `m`] >> simp[]) >>
  `(∃p s. l = p ++ s ∧ FLAT p = m ∧ FLAT s = y) ∨
   (∃p s ip is.
       l = p ++ [ip ++ is] ++ s ∧ m = FLAT p ++ ip ∧ ip ≠ [] ∧ is ≠ [] ∧
       y = is ++ FLAT s)` by metis_tac[]
  >- (disj1_tac >> map_every qexists_tac [`h::p`, `s`] >> simp[]) >>
  disj2_tac >> map_every qexists_tac [`h::p`, `s`] >> simp[]
QED

Theorem FLAT_EQ_NIL: FLAT l = [] ⇔ ∀e. MEM e l ⇒ e = []
Proof simp[listTheory.FLAT_EQ_NIL, EVERY_MEM] >> metis_tac[]
QED

Theorem FLAT_EQ_SING:
  FLAT l = [x] ⇔
    ∃p s. l = p ++ [[x]] ++ s ∧ FLAT p = [] ∧ FLAT s = []
Proof
  Induct_on `l` >> simp[] >> simp[APPEND_EQ_CONS] >>
  simp_tac (srw_ss() ++ DNF_ss) [] >> metis_tac[]
QED

Theorem fringe_element:
    ∀pt:(α,β)lfptree p x s.
      ptree_fringe pt = p ++ [x] ++ s ⇒
      pt = Lf (x,()) ∧ p = [] ∧ s = [] ∨
      ∃nt ip is ts1 xpt ts2.
        pt = Nd (nt,()) (ts1 ++ [xpt] ++ ts2) ∧
        p = FLAT (MAP ptree_fringe ts1) ++ ip ∧
        s = is ++ FLAT (MAP ptree_fringe ts2) ∧
        ptree_fringe xpt = ip ++ [x] ++ is
Proof
  gen_tac >>
  `(∃tok. pt = Lf (tok,())) ∨ (∃sym ptl. pt = Nd sym ptl)`
    by (Cases_on `pt` >> Cases_on `p` >> simp[])
  >- simp[APPEND_EQ_CONS] >>
  simp[] >> pop_assum (K ALL_TAC) >> rpt gen_tac >>
  simp[Once FLAT_EQ_APPEND] >>
  disch_then
   (DISJ_CASES_THEN2 (qxchl [`fsp`, `fss`] strip_assume_tac) mp_tac)
  >| [
    Cases_on `sym` >> simp[] >>
    qpat_x_assum `p ++ [x] = FLAT fsp` mp_tac >>
    simp[Once FLAT_EQ_APPEND] >>
    disch_then
      (DISJ_CASES_THEN2 (qxchl [`fsp1`, `fsp2`] strip_assume_tac) mp_tac)
    >| [
      qpat_x_assum `[x] = FLAT fsp2` mp_tac >>
      simp[FLAT_EQ_SING] >>
      disch_then (qxchl [`nilps`, `nilss`] strip_assume_tac) >>
      rw[] >> qpat_x_assum `MAP ptree_fringe ptl = XX` mp_tac >>
      qabbrev_tac `fp = fsp1 ++ nilps` >>
      qabbrev_tac `fs = nilss ++ fss` >>
      `fsp1 ++ (nilps ++ [[x]] ++ nilss) ++ fss = fp ++ [[x]] ++ fs`
        by simp[] >>
      pop_assum SUBST_ALL_TAC >>
      simp[MAP_EQ_APPEND] >>
      disch_then (fn th =>
        `∃ts1 ts2 xpt. ptl = ts1 ++ [xpt] ++ ts2 ∧
                       fp = MAP ptree_fringe ts1 ∧
                       fs = MAP ptree_fringe ts2 ∧
                       [x] = ptree_fringe xpt`
        by metis_tac [th, APPEND_ASSOC]) >>
      map_every qexists_tac [`[]`, `[]`, `ts1`, `xpt`, `ts2`] >>
      simp[] >>
      `FLAT fs = FLAT fss ∧ FLAT fp = FLAT fsp1`
        by metis_tac [rich_listTheory.FLAT_APPEND, APPEND, APPEND_NIL] >>
      metis_tac[],

      simp[APPEND_EQ_CONS] >>
      simp[SimpL``(==>)``, LEFT_AND_OVER_OR, EXISTS_OR_THM,
           FLAT_EQ_SING] >>
      disch_then (qxchl [`f1`, `snils`, `xp`] strip_assume_tac) >>
      rw[] >> qabbrev_tac `f2 = snils ++ fss` >>
      `MAP ptree_fringe ptl = f1 ++ [xp ++ [x]] ++ f2` by simp[Abbr`f2`] >>
      pop_assum mp_tac >>
      simp_tac (srw_ss()) [MAP_EQ_APPEND] >>
      disch_then (fn th =>
        `∃pt1 pt2 ptx. ptl = pt1 ++ [ptx] ++ pt2 ∧
                       f1 = MAP ptree_fringe pt1 ∧
                       f2 = MAP ptree_fringe pt2 ∧
                       xp ++ [x] = ptree_fringe ptx`
        by metis_tac[th,APPEND_ASSOC]) >>
      map_every qexists_tac [`xp`, `[]`, `pt1`, `ptx`, `pt2`] >>
      simp[] >>
      `FLAT f2 = FLAT fss` by simp[Abbr`f2`, rich_listTheory.FLAT_APPEND] >>
      metis_tac[]
    ],

    disch_then (qxchl [`f1`, `f2`, `fpx`, `fs`] strip_assume_tac) >>
    `∃fp. fpx = fp ++ [x]`
       by (qpat_x_assum `p ++ [x] = XX` mp_tac >>
           simp[APPEND_EQ_APPEND, APPEND_EQ_CONS, DISJ_IMP_THM] >>
           metis_tac[]) >>
    qpat_x_assum `MAP ptree_fringe XX = YY` mp_tac >>
    simp[MAP_EQ_APPEND] >>
    disch_then (fn th =>
      `∃pt1 pt2 ptx. ptl = pt1 ++ [ptx] ++ pt2 ∧
                     f1 = MAP ptree_fringe pt1 ∧
                     f2 = MAP ptree_fringe pt2 ∧
                     fp ++ [x] ++ fs = ptree_fringe ptx`
      by metis_tac [th,APPEND_ASSOC]) >>
    Cases_on `sym` >> simp[] >>
    map_every qexists_tac [`fp`, `fs`, `pt1`, `ptx`, `pt2`] >>
    simp[] >> rw[] >> fs[]
  ]
QED

Theorem derive_fringe:
    ∀pt:(α,β)lfptree sf.
      derive G (ptree_fringe pt) sf ∧ valid_ptree G pt ⇒
      ∃pt' : (α,β)lfptree.
         ptree_head pt' = ptree_head pt ∧ valid_ptree G pt' ∧
         ptree_fringe pt' = sf
Proof
  ho_match_mp_tac ptree_ind>> rw[]
  >- (
      Cases_on `pt` >>
      fs[derive_def, APPEND_EQ_CONS] >>
      qexists_tac `Nd (sym,ARB) (MAP (\x. Lf(x, ARB)) sf)`
      >> rw[MEM_MAP,ptree_fringe_def]
      >- rw[MAP_MAP_o, combinTheory.o_DEF]
      >- rw[] >>
      rw[MAP_MAP_o, combinTheory.o_DEF] >>
      pop_assum (K ALL_TAC) >> Induct_on `sf` >> rw[]) >>
  rename [`Nd ntl pts`] >> Cases_on `ntl` >> rename [`Nd (rootnt,l) pts`] >>
  qpat_x_assum `derive G XX YY` mp_tac >>
  simp[derive_def] >>
  disch_then (qxchl [`pfx`, `nt`, `rhs`, `sfx`] strip_assume_tac) >>
  qspecl_then [`Nd (rootnt,l) pts`, `pfx`, `NT nt`, `sfx`]
    mp_tac fringe_element >>
  fs[] >>
  disch_then (qxchl [`ip`, `is`, `ts1`, `xpt`, `ts2`] strip_assume_tac) >>
  rw[] >>
  fs[FLAT_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
  `derive G (ip ++ [NT nt] ++ is) (ip ++ rhs ++ is)`
     by metis_tac [derive_def] >>
  pop_assum
    (fn th => first_x_assum
                (fn impth => mp_tac (MATCH_MP impth th))) >>
  disch_then (qxch `pt'` strip_assume_tac) >>
  qexists_tac `Nd (rootnt, ()) (ts1 ++ [pt'] ++ ts2)` >>
  simp[FLAT_APPEND, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem ptrees_derive_extensible:
    ∀pt:(α,β)lfptree sf.
      valid_ptree G pt ∧ derives G (ptree_fringe pt) sf ⇒
      ∃pt':(α,β)lfptree.
         valid_ptree G pt' ∧ ptree_head pt' = ptree_head pt ∧
         ptree_fringe pt' = sf
Proof
  qsuff_tac
    `∀sf1 sf2.
       derives G sf1 sf2 ⇒
       ∀pt:(α,β)lfptree.
          valid_ptree G pt ∧ ptree_fringe pt = sf1 ⇒
          ∃pt':(α,β)lfptree.
             valid_ptree G pt' ∧ ptree_head pt' = ptree_head pt ∧
             ptree_fringe pt' = sf2`
    >- metis_tac[] >>
  ho_match_mp_tac RTC_STRONG_INDUCT >> rw[] >>
  metis_tac [derive_fringe]
QED

Theorem singleton_derives_ptree:
    derives G [h] sf ⇒
    ∃pt:(α,β)lfptree.
      valid_ptree G pt ∧ ptree_head pt = h ∧ ptree_fringe pt = sf
Proof
  strip_tac >> qspec_then `Lf (h,l)` mp_tac ptrees_derive_extensible >> simp[]
QED

Theorem derives_language:
    language G = { ts | derives G [NT G.start] (MAP TOK ts) }
Proof
  rw[language_def, EXTENSION, complete_ptree_def] >> eq_tac
  >- metis_tac[valid_ptree_derive] >>
  strip_tac >>
  qspecl_then [`Lf (NT G.start, ())`, `MAP TOK x`] mp_tac
    ptrees_derive_extensible >> simp[] >>
  disch_then (qxch `pt` strip_assume_tac) >> qexists_tac `pt` >>
  simp[] >> dsimp[MEM_MAP]
QED

Theorem derives_leading_nonNT_E:
    N ∉ FDOM G.rules ∧ derives G (NT N :: rest) Y ⇒
    ∃rest'. Y = NT N :: rest' ∧ derives G rest rest'
Proof
  `∀X Y. derives G X Y ⇒
         ∀N rest. N ∉ FDOM G.rules ∧ X = NT N :: rest ⇒
                  ∃rest'. Y = NT N :: rest' ∧ derives G rest rest'`
    suffices_by metis_tac[] >>
  ho_match_mp_tac RTC_INDUCT >> simp[] >> rw[] >>
  fs[derive_def, Once APPEND_EQ_CONS] >>
  fs[APPEND_EQ_CONS] >> rw[] >> fs[] >>
  match_mp_tac RTC1 >> metis_tac [derive_def]
QED

Theorem derives_leading_nonNT:
    N ∉ FDOM G.rules ⇒
    (derives G (NT N :: rest) Y ⇔
     ∃rest'. Y = NT N :: rest' ∧ derives G rest rest')
Proof
  strip_tac >> eq_tac >- metis_tac [derives_leading_nonNT_E] >>
  rw[] >>
  metis_tac [APPEND, derives_paste_horizontally,
             RTC_REFL]
QED

val RTC_R_I = RTC_RULES |> SPEC_ALL |> CONJUNCT2 |> GEN_ALL
Theorem derives_split_horizontally:
    ∀p s sf. derives G (p ++ s) sf ⇔
             ∃sf1 sf2. sf = sf1 ++ sf2 ∧ derives G p sf1 ∧ derives G s sf2
Proof
  rpt gen_tac >> REVERSE eq_tac >- metis_tac [derives_paste_horizontally] >>
  `∃sf0. p ++ s = sf0` by simp[] >> simp[] >>
  pop_assum
    (fn th => disch_then
                (fn th2 => mp_tac th >> map_every qid_spec_tac [`s`, `p`] >>
                           mp_tac th2)) >>
  map_every qid_spec_tac [`sf`, `sf0`] >>
  ho_match_mp_tac RTC_INDUCT >> simp[] >> conj_tac
  >- metis_tac[RTC_REFL] >>
  map_every qx_gen_tac [`sf0`, `sf'`, `sf`] >> simp[derive_def] >>
  disch_then (CONJUNCTS_THEN2
               (qxchl [`pfx`, `N`, `r`, `sfx`] strip_assume_tac)
               strip_assume_tac) >> rw[] >>
  qpat_x_assum `X = Y` mp_tac >> simp[listTheory.APPEND_EQ_APPEND_MID] >>
  disch_then (DISJ_CASES_THEN (qxchl [`l`] strip_assume_tac)) >> rw[] >|[
    first_x_assum (qspecl_then [`pfx ++ r ++ l`, `s`] mp_tac),
    first_x_assum (qspecl_then [`p`, `l ++ r ++ sfx`] mp_tac)
  ] >> simp[] >> disch_then (qxchl [`sf1`, `sf2`] strip_assume_tac) >> rw[] >>
  map_every qexists_tac [`sf1`, `sf2`] >> simp[] >> match_mp_tac RTC_R_I >>
  metis_tac[derive_def]
QED

