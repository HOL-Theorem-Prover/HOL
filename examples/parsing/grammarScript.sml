open HolKernel Parse boolLib bossLib

open boolSimps lcsymtacs

open listTheory pred_setTheory finite_mapTheory

val _ = new_theory "grammar"

val _ = ParseExtras.tight_equality()

val _ = type_abbrev("inf", ``:'a + num``)
val _ = Hol_datatype `
  symbol = TOK of 'a | NT of 'b inf
`;

val isTOK_def = Define`(isTOK (TOK tok) = T) ∧ (isTOK (NT n) = F)`
val _ = export_rewrites ["isTOK_def"]

val _ = Hol_datatype`
  grammar = <|
   start : 'b inf;
   rules : 'b inf |-> ('a,'b)symbol list set
|> `;

val _ = Hol_datatype`
  parsetree = Lf of ('a,'b) symbol
            | Nd of 'b inf => parsetree list
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

val MAP_EQ_SING = store_thm(
  "MAP_EQ_SING",
  ``MAP f l = [x] ⇔ ∃x0. l = [x0] ∧ x = f x0``,
  Induct_on `l` >> simp[] >> metis_tac[]);

val MAP_EQ_APPEND = store_thm(
  "MAP_EQ_APPEND",
  ``MAP f l = x ++ y ⇔
    ∃x0 y0. l = x0 ++ y0 ∧ x = MAP f x0 ∧ y = MAP f y0``,
  reverse eq_tac >- (rw[]>>rw[]) >>
  map_every qid_spec_tac [`y`,`x`, `l`] >> Induct >> simp[] >>
  map_every qx_gen_tac [`h`, `x`, `y`] >> Cases_on `x` >> simp[] >>
  strip_tac >> Q.REFINE_EXISTS_TAC `hh::tt` >> simp[]);

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
      simp[MAP_EQ_APPEND, MAP_EQ_SING] >>
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
      simp_tac (srw_ss()) [MAP_EQ_APPEND, MAP_EQ_SING] >>
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
    simp[MAP_EQ_APPEND, MAP_EQ_SING] >>
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
  fs[rich_listTheory.FLAT_APPEND, DISJ_IMP_THM, FORALL_AND_THM] >>
  `derive G (ip ++ [NT nt] ++ is) (ip ++ rhs ++ is)`
     by metis_tac [derive_def] >>
  pop_assum
    (fn th => first_x_assum
                (fn impth => mp_tac (MATCH_MP impth th))) >>
  disch_then (qxch `pt'` strip_assume_tac) >>
  qexists_tac `Nd s (ts1 ++ [pt'] ++ ts2)` >>
  simp[rich_listTheory.FLAT_APPEND, DISJ_IMP_THM, FORALL_AND_THM]);

val lemma = prove(
  ``∀pt ts.
      valid_ptree G pt ∧ ptree_head pt = NT G.start ∧
      derives G (ptree_fringe pt) (MAP TOK ts) ⇒
      ∃pt'.
         valid_ptree G pt' ∧ ptree_head pt' = NT G.start ∧
         ptree_fringe pt' = MAP TOK ts``,
  qsuff_tac
    `∀sf1 sf2.
       derives G sf1 sf2 ⇒
       ∀pt ts.
          (sf2 = MAP TOK ts) ∧ valid_ptree G pt ∧
          ptree_head pt = NT G.start ∧ ptree_fringe pt = sf1 ⇒
          ∃pt'.
             valid_ptree G pt' ∧ ptree_head pt' = NT G.start ∧
             ptree_fringe pt' = MAP TOK ts`
    >- metis_tac[] >>
  ho_match_mp_tac relationTheory.RTC_STRONG_INDUCT >> rw[] >>
  metis_tac [derive_fringe])

val derives_language = store_thm(
  "derives_language",
  ``language G = { ts | derives G [NT G.start] (MAP TOK ts) }``,
  rw[language_def, EXTENSION, complete_ptree_def] >> eq_tac
  >- metis_tac[valid_ptree_derive] >>
  strip_tac >>
  qspecl_then [`Lf (NT G.start)`, `x`] mp_tac lemma >> simp[] >>
  disch_then (qxch `pt` strip_assume_tac) >> qexists_tac `pt` >>
  simp[] >> asm_simp_tac (srw_ss() ++ DNF_ss) [MEM_MAP]);

val _ = export_theory()
