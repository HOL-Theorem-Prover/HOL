open HolKernel Parse boolLib bossLib

open boolSimps lcsymtacs

open listTheory pred_setTheory finite_mapTheory

val FLAT_APPEND = rich_listTheory.FLAT_APPEND
val rveq = rpt BasicProvers.VAR_EQ_TAC
fun asm_match q = Q.MATCH_ASSUM_RENAME_TAC q

val _ = new_theory "grammar"

val _ = ParseExtras.tight_equality()

val _ = type_abbrev("inf", ``:'a + num``)
val _ = Datatype `symbol = TOK 'a | NT ('b inf)`;

val isTOK_def = Define`(isTOK (TOK tok) = T) ∧ (isTOK (NT n) = F)`
val _ = export_rewrites ["isTOK_def"]

val destTOK_def = Define`
  (destTOK (TOK tk) = SOME tk) ∧
  (destTOK _ = NONE)
`;
val _ = export_rewrites ["destTOK_def"]

val _ = Datatype`
  grammar = <|
   start : 'b inf;
   rules : 'b inf |-> ('a,'b)symbol list set
|> `;

val _ = Datatype`
  parsetree = Lf (('a,'b) symbol)
            | Nd ('b inf) (parsetree list)
`;

val ptree_size_def = tDefine "ptree_size" `
  (ptree_size (Lf tok) = 1) ∧
  (ptree_size (Nd nt children) = 1 + SUM (MAP ptree_size children))
` (WF_REL_TAC `measure (parsetree_size (K 1) (K 1))` THEN
   Induct_on `children` THEN
   SRW_TAC [][definition "parsetree_size_def"] THEN1 DECIDE_TAC THEN
   RES_TAC THEN POP_ASSUM (Q.SPEC_THEN `nt` MP_TAC) THEN
   DECIDE_TAC)

val ptree_size_def = save_thm(
  "ptree_size_def",
  CONV_RULE (DEPTH_CONV ETA_CONV) ptree_size_def)
val _ = export_rewrites ["ptree_size_def"]

val ptree_head_def = Define`
  (ptree_head (Lf tok) = tok) ∧
  (ptree_head (Nd nt children) = NT nt)
`;
val _ = export_rewrites ["ptree_head_def"]

val noneval = Lib.with_flag (computeLib.auto_import_definitions,false)
fun tzDefine nm q tac = noneval (tDefine nm q) tac
val valid_ptree_def = tzDefine "valid_ptree" `
  (valid_ptree G (Lf _) ⇔ T) ∧
  (valid_ptree G (Nd nt children) ⇔
    nt ∈ FDOM G.rules ∧ MAP ptree_head children ∈ G.rules ' nt ∧
    ∀pt. pt ∈ set children ⇒ valid_ptree G pt)`
  (WF_REL_TAC `measure (ptree_size o SND)` THEN
   Induct_on `children` THEN SRW_TAC [][] THEN1 DECIDE_TAC THEN
   RES_TAC THEN FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [])
val _ = export_rewrites ["valid_ptree_def"]

val ptree_fringe_def = tDefine "ptree_fringe" `
  (ptree_fringe (Lf t) = [t]) ∧
  (ptree_fringe (Nd _ children) = FLAT (MAP ptree_fringe children))
` (WF_REL_TAC `measure ptree_size` THEN Induct_on `children` THEN
   SRW_TAC [][ptree_size_def] THEN1 DECIDE_TAC THEN
   FULL_SIMP_TAC (srw_ss() ++ ETA_ss) [ptree_size_def] THEN
   RES_TAC THEN DECIDE_TAC)

val ptree_fringe_def = save_thm(
  "ptree_fringe_def",
  CONV_RULE (DEPTH_CONV ETA_CONV) ptree_fringe_def)
val _ = export_rewrites ["ptree_fringe_def"]

val complete_ptree_def = Define`
  complete_ptree G pt ⇔
    valid_ptree G pt ∧ ptree_head pt = NT G.start ∧
    ∀t. t ∈ set (ptree_fringe pt) ⇒ isTOK t`

val language_def = Define`
  language G =
   { ts | ∃pt. complete_ptree G pt ∧ ptree_fringe pt = MAP TOK ts }`

val derive_def = Define`
  derive G sf1 sf2 ⇔
    ∃p sym rhs s. sf1 = p ++ [NT sym] ++ s ∧ sf2 = p ++ rhs ++ s ∧
                  sym ∈ FDOM G.rules ∧ rhs ∈ G.rules ' sym
`;

val RTC1 = relationTheory.RTC_RULES |> Q.SPEC `R` |> CONJUNCT2
                                    |> Q.GEN `R`
val qxch = Q.X_CHOOSE_THEN
fun qxchl [] ttac = ttac
  | qxchl (q::qs) ttac = qxch q (qxchl qs ttac)

val derive_common_prefix = store_thm(
  "derive_common_prefix",
  ``derive G sf1 sf2 ⇒ derive G (p ++ sf1) (p ++ sf2)``,
  rw[derive_def] >> metis_tac [APPEND_ASSOC]);
val derive_common_suffix = store_thm(
  "derive_common_suffix",
  ``derive G sf1 sf2 ⇒ derive G (sf1 ++ s) (sf2 ++ s)``,
  rw[derive_def] >> metis_tac [APPEND_ASSOC]);

val _ = overload_on ("derives", ``λG. RTC (derive G)``)
val derive_paste_horizontally = store_thm(
  "derive_paste_horizontally",
  ``derive G sf11 sf12 ∧ derive G sf21 sf22 ⇒
    derives G (sf11 ++ sf21) (sf12 ++ sf22)``,
  metis_tac [derive_common_prefix, derive_common_suffix,
             relationTheory.RTC_RULES])

val derive_1NT = store_thm(
  "derive_1NT",
  ``derive G [NT s] l ⇔ s ∈ FDOM G.rules ∧ l ∈ G.rules ' s``,
  rw[derive_def, APPEND_EQ_CONS]);
val _ = export_rewrites ["derive_1NT"]

val derives_common_prefix = store_thm(
  "derives_common_prefix",
  ``∀sf1 sf2 p. derives G sf1 sf2 ⇒ derives G (p ++ sf1) (p ++ sf2)``,
  simp[GSYM PULL_FORALL] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >> rw[] >>
  metis_tac [relationTheory.RTC_RULES, derive_common_prefix]);
val derives_common_suffix = store_thm(
  "derives_common_suffix",
  ``∀sf1 sf2 s. derives G sf1 sf2 ⇒ derives G (sf1 ++ s) (sf2 ++ s)``,
  simp[GSYM PULL_FORALL] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >> rw[] >>
  metis_tac [relationTheory.RTC_RULES, derive_common_suffix]);

val derives_paste_horizontally = store_thm(
  "derives_paste_horizontally",
  ``derives G sf11 sf12 ∧ derives G sf21 sf22 ⇒
    derives G (sf11 ++ sf21) (sf12 ++ sf22)``,
  metis_tac [relationTheory.RTC_CASES_RTC_TWICE,
             derives_common_suffix, derives_common_prefix])

val ptree_ind = save_thm(
  "ptree_ind",
  TypeBase.induction_of ``:('a,'b)parsetree``
     |> Q.SPECL [`P`, `λl. ∀pt. MEM pt l ⇒ P pt`]
     |> SIMP_RULE (srw_ss() ++ CONJ_ss) []
     |> SIMP_RULE (srw_ss()) [DISJ_IMP_THM, FORALL_AND_THM]
     |> Q.GEN `P`);

val valid_ptree_derive = store_thm(
  "valid_ptree_derive",
  ``∀pt. valid_ptree G pt ⇒ derives G [ptree_head pt] (ptree_fringe pt)``,
  ho_match_mp_tac ptree_ind >> rw[] >> fs[] >>
  match_mp_tac RTC1 >> qexists_tac `MAP ptree_head l` >> rw[] >>
  qpat_assum `SS ∈ G.rules ' s` (K ALL_TAC) >> Induct_on `l` >> rw[] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  metis_tac [derives_paste_horizontally, APPEND]);

val FLAT_EQ_APPEND = store_thm(
  "FLAT_EQ_APPEND",
  ``FLAT l = x ++ y ⇔
    (∃p s. l = p ++ s ∧ x = FLAT p ∧ y = FLAT s) ∨
    (∃p s ip is.
       l = p ++ [ip ++ is] ++ s ∧ ip ≠ [] ∧ is ≠ [] ∧
       x = FLAT p ++ ip ∧
       y = is ++ FLAT s)``,
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
  disj2_tac >> map_every qexists_tac [`h::p`, `s`] >> simp[])

val FLAT_EQ_NIL = store_thm(
  "FLAT_EQ_NIL",
  ``FLAT l = [] ⇔ ∀e. MEM e l ⇒ e = []``,
  Induct_on `l` >> simp[DISJ_IMP_THM, FORALL_AND_THM]);

val FLAT_EQ_SING = store_thm(
  "FLAT_EQ_SING",
  ``FLAT l = [x] ⇔
    ∃p s. l = p ++ [[x]] ++ s ∧ FLAT p = [] ∧ FLAT s = []``,
  Induct_on `l` >> simp[] >> simp[APPEND_EQ_CONS] >>
  simp_tac (srw_ss() ++ DNF_ss) [] >> metis_tac[]);

val fringe_element = store_thm(
  "fringe_element",
  ``∀pt p x s.
      ptree_fringe pt = p ++ [x] ++ s ⇒
      (pt = Lf x ∧ p = [] ∧ s = []) ∨
      ∃nt ip is ts1 xpt ts2.
        pt = Nd nt (ts1 ++ [xpt] ++ ts2) ∧
        p = FLAT (MAP ptree_fringe ts1) ++ ip ∧
        s = is ++ FLAT (MAP ptree_fringe ts2) ∧
        ptree_fringe xpt = ip ++ [x] ++ is``,
  gen_tac >>
  `(∃tok. pt = Lf tok) ∨ (∃sym ptl. pt = Nd sym ptl)`
    by (Cases_on `pt` >> simp[]) >- simp[APPEND_EQ_CONS] >>
  simp[] >> pop_assum (K ALL_TAC) >> rpt gen_tac >>
  simp[Once FLAT_EQ_APPEND] >>
  disch_then
    (DISJ_CASES_THEN2 (qxchl [`fsp`, `fss`] strip_assume_tac) mp_tac) >| [
    qpat_assum `p ++ [x] = FLAT fsp` mp_tac >>
    simp[Once FLAT_EQ_APPEND] >>
    disch_then
    (DISJ_CASES_THEN2 (qxchl [`fsp1`, `fsp2`] strip_assume_tac) mp_tac) >| [
      qpat_assum `[x] = FLAT fsp2` mp_tac >>
      simp[FLAT_EQ_SING] >>
      disch_then (qxchl [`nilps`, `nilss`] strip_assume_tac) >>
      rw[] >> qpat_assum `MAP ptree_fringe ptl = XX` mp_tac >>
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
       by (qpat_assum `p ++ [x] = XX` mp_tac >>
           simp[APPEND_EQ_APPEND, APPEND_EQ_CONS, DISJ_IMP_THM] >>
           metis_tac[]) >>
    qpat_assum `MAP ptree_fringe XX = YY` mp_tac >>
    simp[MAP_EQ_APPEND] >>
    disch_then (fn th =>
      `∃pt1 pt2 ptx. ptl = pt1 ++ [ptx] ++ pt2 ∧
                     f1 = MAP ptree_fringe pt1 ∧
                     f2 = MAP ptree_fringe pt2 ∧
                     fp ++ [x] ++ fs = ptree_fringe ptx`
      by metis_tac [th,APPEND_ASSOC]) >>
    map_every qexists_tac [`fp`, `fs`, `pt1`, `ptx`, `pt2`] >>
    simp[] >> rw[] >> fs[]
  ]);

val derive_fringe = store_thm(
  "derive_fringe",
  ``∀pt sf.
      derive G (ptree_fringe pt) sf ∧ valid_ptree G pt ⇒
      ∃pt'.
         ptree_head pt' = ptree_head pt ∧ valid_ptree G pt' ∧
         ptree_fringe pt' = sf``,
  ho_match_mp_tac ptree_ind >> rw[]
  >- (fs[derive_def, APPEND_EQ_CONS] >>
      qexists_tac `Nd sym (MAP Lf sf)` >> rw[MEM_MAP]
      >- rw[MAP_MAP_o, combinTheory.o_DEF]
      >- rw[] >>
      rw[MAP_MAP_o, combinTheory.o_DEF] >>
      pop_assum (K ALL_TAC) >> Induct_on `sf` >> rw[]) >>
  qpat_assum `derive G XX YY` mp_tac >>
  simp[derive_def] >>
  disch_then (qxchl [`pfx`, `nt`, `rhs`, `sfx`] strip_assume_tac) >>
  qspecl_then [`Nd s l`, `pfx`, `NT nt`, `sfx`] mp_tac fringe_element >>
  simp[] >>
  disch_then (qxchl [`ip`, `is`, `ts1`, `xpt`, `ts2`] strip_assume_tac) >>
  rw[] >>
  fs[FLAT_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
  `derive G (ip ++ [NT nt] ++ is) (ip ++ rhs ++ is)`
     by metis_tac [derive_def] >>
  pop_assum
    (fn th => first_x_assum
                (fn impth => mp_tac (MATCH_MP impth th))) >>
  disch_then (qxch `pt'` strip_assume_tac) >>
  qexists_tac `Nd s (ts1 ++ [pt'] ++ ts2)` >>
  simp[FLAT_APPEND, DISJ_IMP_THM, FORALL_AND_THM]);

val ptrees_derive_extensible = store_thm(
  "ptrees_derive_extensible",
  ``∀pt sf.
      valid_ptree G pt ∧ derives G (ptree_fringe pt) sf ⇒
      ∃pt'.
         valid_ptree G pt' ∧ ptree_head pt' = ptree_head pt ∧
         ptree_fringe pt' = sf``,
  qsuff_tac
    `∀sf1 sf2.
       derives G sf1 sf2 ⇒
       ∀pt.
          valid_ptree G pt ∧ ptree_fringe pt = sf1 ⇒
          ∃pt'.
             valid_ptree G pt' ∧ ptree_head pt' = ptree_head pt ∧
             ptree_fringe pt' = sf2`
    >- metis_tac[] >>
  ho_match_mp_tac relationTheory.RTC_STRONG_INDUCT >> rw[] >>
  metis_tac [derive_fringe])

val singleton_derives_ptree = store_thm(
  "singleton_derives_ptree",
  ``derives G [h] sf ⇒
    ∃pt. valid_ptree G pt ∧ ptree_head pt = h ∧ ptree_fringe pt = sf``,
  strip_tac >> qspec_then `Lf h` mp_tac ptrees_derive_extensible >> simp[]);

val derives_language = store_thm(
  "derives_language",
  ``language G = { ts | derives G [NT G.start] (MAP TOK ts) }``,
  rw[language_def, EXTENSION, complete_ptree_def] >> eq_tac
  >- metis_tac[valid_ptree_derive] >>
  strip_tac >>
  qspecl_then [`Lf (NT G.start)`, `MAP TOK x`] mp_tac
    ptrees_derive_extensible >> simp[] >>
  disch_then (qxch `pt` strip_assume_tac) >> qexists_tac `pt` >>
  simp[] >> asm_simp_tac (srw_ss() ++ DNF_ss) [MEM_MAP]);

val derives_leading_nonNT_E = store_thm(
  "derives_leading_nonNT_E",
  ``N ∉ FDOM G.rules ∧ derives G (NT N :: rest) Y ⇒
    ∃rest'. Y = NT N :: rest' ∧ derives G rest rest'``,
  `∀X Y. derives G X Y ⇒
         ∀N rest. N ∉ FDOM G.rules ∧ X = NT N :: rest ⇒
                  ∃rest'. Y = NT N :: rest' ∧ derives G rest rest'`
    suffices_by metis_tac[] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >> simp[] >> rw[] >>
  fs[derive_def, Once APPEND_EQ_CONS] >>
  fs[APPEND_EQ_CONS] >> rw[] >> fs[] >>
  match_mp_tac RTC1 >> metis_tac [derive_def]);

val derives_leading_nonNT = store_thm(
  "derives_leading_nonNT",
  ``N ∉ FDOM G.rules ⇒
    (derives G (NT N :: rest) Y ⇔
     ∃rest'. Y = NT N :: rest' ∧ derives G rest rest')``,
  strip_tac >> eq_tac >- metis_tac [derives_leading_nonNT_E] >>
  rw[] >>
  metis_tac [APPEND, derives_paste_horizontally,
             relationTheory.RTC_REFL]);

val RTC_R_I = relationTheory.RTC_RULES |> SPEC_ALL |> CONJUNCT2 |> GEN_ALL
val derives_split_horizontally = store_thm(
  "derives_split_horizontally",
  ``∀p s sf. derives G (p ++ s) sf ⇔
             ∃sf1 sf2. sf = sf1 ++ sf2 ∧ derives G p sf1 ∧ derives G s sf2``,
  rpt gen_tac >> REVERSE eq_tac >- metis_tac [derives_paste_horizontally] >>
  `∃sf0. p ++ s = sf0` by simp[] >> simp[] >>
  pop_assum
    (fn th => disch_then
                (fn th2 => mp_tac th >> map_every qid_spec_tac [`s`, `p`] >>
                           mp_tac th2)) >>
  map_every qid_spec_tac [`sf`, `sf0`] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >> simp[] >> conj_tac
  >- metis_tac[relationTheory.RTC_REFL] >>
  map_every qx_gen_tac [`sf0`, `sf'`, `sf`] >> simp[derive_def] >>
  disch_then (CONJUNCTS_THEN2
               (qxchl [`pfx`, `N`, `r`, `sfx`] strip_assume_tac)
               strip_assume_tac) >> rw[] >>
  qpat_assum `X = Y` mp_tac >> simp[listTheory.APPEND_EQ_APPEND_MID] >>
  disch_then (DISJ_CASES_THEN (qxchl [`l`] strip_assume_tac)) >> rw[] >|[
    first_x_assum (qspecl_then [`pfx ++ r ++ l`, `s`] mp_tac),
    first_x_assum (qspecl_then [`p`, `l ++ r ++ sfx`] mp_tac)
  ] >> simp[] >> disch_then (qxchl [`sf1`, `sf2`] strip_assume_tac) >> rw[] >>
  map_every qexists_tac [`sf1`, `sf2`] >> simp[] >> match_mp_tac RTC_R_I >>
  metis_tac[derive_def]);

val _ = export_theory()
