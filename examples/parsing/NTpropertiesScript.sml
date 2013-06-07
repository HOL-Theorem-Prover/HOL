open HolKernel Parse boolLib bossLib

open grammarTheory
open lcsymtacs
open pred_setTheory

val _ = new_theory "NTproperties"

fun dsimp thl = asm_simp_tac (srw_ss() ++ boolSimps.DNF_ss) thl
fun asimp thl = asm_simp_tac (srw_ss() ++ ARITH_ss) thl
fun qxchl [] ttac = ttac
  | qxchl (q::qs) ttac = Q.X_CHOOSE_THEN q (qxchl qs ttac)

val APPEND_EQ_SING' = CONV_RULE (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))
                                listTheory.APPEND_EQ_SING

val RTC_R_I = relationTheory.RTC_RULES |> SPEC_ALL |> CONJUNCT2 |> GEN_ALL

(* ----------------------------------------------------------------------
    A sentential form is nullable if it can derive the empty string.

    This work draws on Aditi Barthwal's formalisation.  Using parse trees
    rather than derivations simplifies some of the resulting proofs.
   ---------------------------------------------------------------------- *)

val nullable_def = Define`
  nullable G sf = derives G sf []
`
val _ = overload_on ("nullableNT", ``λG n. nullable G [NT n]``)

val derives_TOK = store_thm(
  "derives_TOK",
  ``∀G p s t sf.
      derives G (p ++ [TOK t] ++ s) sf ⇒
      ∃ps ss. sf = ps ++ [TOK t] ++ ss ∧ derives G p ps ∧ derives G s ss``,
  gen_tac >>
  `∀sf0 sf. derives G sf0 sf ⇒
            ∀p s t. sf0 = p ++ [TOK t] ++ s ⇒
                    ∃ps ss. sf = ps ++ [TOK t] ++ ss ∧ derives G p ps ∧
                            derives G s ss` suffices_by metis_tac[] >>
  HO_MATCH_MP_TAC relationTheory.RTC_INDUCT >> dsimp[] >> conj_tac
  >- metis_tac [relationTheory.RTC_REFL] >>
  map_every qx_gen_tac [`sf0`, `sf`, `p`, `s`, `t`] >>
  simp[derive_def, Once listTheory.APPEND_EQ_APPEND_MID] >>
  disch_then (CONJUNCTS_THEN2 (qxchl [`p0`, `N`, `r`, `s0`] mp_tac)
                              strip_assume_tac) >>
  disch_then (CONJUNCTS_THEN2 (DISJ_CASES_THEN (qxchl [`l`] strip_assume_tac))
                              strip_assume_tac) >>
  rw[] >| [
    qpat_assum `x = y` mp_tac >> simp[Once listTheory.APPEND_EQ_APPEND_MID] >>
    simp[APPEND_EQ_SING'] >> disch_then (qxchl [`l'`] strip_assume_tac) >>
    rw[] >> first_x_assum (qspecl_then [`p`, `l' ++ r ++ s0`, `t`] mp_tac),
    first_x_assum (qspecl_then [`p0 ++ r ++ l`, `s`, `t`] mp_tac)
  ] >>
  simp[] >> disch_then (qxchl [`ps`, `ss`] strip_assume_tac) >>
  map_every qexists_tac [`ps`, `ss`] >> simp[] >>
  match_mp_tac RTC_R_I >> simp[derive_def] >> metis_tac[])

val nullable_CONS_TOK = store_thm(
  "nullable_CONS_TOK",
  ``nullable G (TOK t :: rest) = F``,
  simp[nullable_def] >> strip_tac >>
  qspecl_then [`G`, `[]`, `rest`, `t`, `[]`] mp_tac derives_TOK >> simp[])
val _ = export_rewrites ["nullable_CONS_TOK"]

val nullable_NIL = store_thm(
  "nullable_NIL",
  ``nullable G [] = T``,
  simp[nullable_def])
val _ = export_rewrites ["nullable_NIL"]

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

val nullable_CONS_NT = store_thm(
  "nullable_CONS_NT",
  ``nullable G (NT n :: rest) <=>
      nullable G rest ∧ n ∈ FDOM G.rules ∧
      ∃r. r ∈ G.rules ' n ∧ nullable G r``,
  simp[nullable_def] >> REVERSE eq_tac
  >- (strip_tac >> match_mp_tac RTC_R_I >> simp[derive_def] >>
      qexists_tac `r ++ rest` >> REVERSE conj_tac
      >- metis_tac[derives_paste_horizontally, listTheory.APPEND] >>
      qexists_tac `[]` >> simp[]) >>
  `NT n :: rest = [NT n] ++ rest` by simp[] >> pop_assum SUBST1_TAC >>
  simp[derives_split_horizontally] >> strip_tac >>
  Q.UNDISCH_THEN `derives G [NT n] []`
     (mp_tac o SIMP_RULE (srw_ss()) [Once relationTheory.RTC_CASES1]) >>
  metis_tac[]);



val paireq = prove(
  ``(x,y) = z ⇔ x = FST z ∧ y = SND z``, Cases_on `z` >> simp[])

val GSPEC_INTER = prove(
  ``GSPEC f ∩ Q =
    GSPEC (S ($, o FST o f) (S ($/\ o SND o f) (Q o FST o f)))``,
  simp[GSPECIFICATION, EXTENSION, SPECIFICATION] >> qx_gen_tac `e` >>
  simp[paireq] >> metis_tac[])

val _ = SIMP_CONV (srw_ss())[GSPEC_INTER, combinTheory.o_ABS_R, combinTheory.S_ABS_R, combinTheory.S_ABS_L, pairTheory.o_UNCURRY_R, pairTheory.S_UNCURRY_R] ``{ n + m | n > 10 ∧ m < 3 } ∩ Q``

(* nullableML is an "executable" version of nullable that examines the grammar
   to determine nullability. I put the "executable" in quotes because of the
   scary looking set comprehension below.  This will work fine if the
   sets of rules for non-terminals are always finite. *)
val nullableML_def = tDefine "nullableML" `
  nullableML seen [] = T ∧
  nullableML seen (TOK t :: _) = F ∧
  nullableML seen (NT n :: rest) =
      if n ∈ FDOM G.rules ∧ n ∉ seen then
        if G.rules ' n ∩ { r | nullableML (n INSERT seen) r } = ∅ then F
        else nullableML seen rest
      else F
`
  (WF_REL_TAC `measure (λs. CARD (FDOM G.rules DIFF s)) LEX measure LENGTH` >>
   rpt strip_tac >> simp[] >> DISJ1_TAC >> simp[CARD_DIFF_EQN] >>
   simp[Once INTER_COMM] >> simp[INSERT_INTER] >>
   simp[FINITE_INTER] >> simp[Once INTER_COMM] >>
   simp[arithmeticTheory.SUB_LEFT_LESS] >>
   match_mp_tac arithmeticTheory.LESS_LESS_EQ_TRANS >>
   qexists_tac `CARD (n INSERT FDOM G.rules ∩ seen)` >>
   conj_tac >- simp[] >>
   `FINITE (FDOM G.rules)` by simp[] >>
   pop_assum (MATCH_MP_TAC o MATCH_MP CARD_SUBSET) >>
   simp[SUBSET_DEF])

val nullableML_nullable = store_thm(
  "nullableML_nullable",
  ``∀sn sf. nullableML G sn sf ⇒ nullable G sf``,
  HO_MATCH_MP_TAC (theorem "nullableML_ind") >>
  simp[nullableML_def, nullable_CONS_NT] >>
  map_every qx_gen_tac [`sn`, `N`, `sf`] >> rpt strip_tac >>
  qpat_assum `SS ≠ ∅` mp_tac >> simp[EXTENSION] >> metis_tac[]);


val ptree_NTs_def = tDefine "ptree_NTs" `
  (ptree_NTs (Lf l) = case l of NT N => {N} | _ => ∅) ∧
  (ptree_NTs (Nd n subs) = n INSERT BIGUNION (IMAGE ptree_NTs (set subs)))
`
  (WF_REL_TAC `measure ptree_size` >> Induct_on `subs` >> simp[] >> fs[] >>
   rpt strip_tac >> res_tac >> asimp[])

val ptree_rptfree_def = tDefine "ptree_rptfree" `
  ptree_rptfree (Lf _) = T ∧
  ptree_rptfree (Nd N subs) =
    ∀s. MEM s subs ⇒ ptree_rptfree s ∧ N ∉ ptree_NTs s
`
  (WF_REL_TAC `measure ptree_size` >> Induct_on `subs` >> simp[] >> fs[] >>
   rpt strip_tac >> res_tac >> asimp[])

val nullableML_by_singletons = store_thm(
  "nullableML_by_singletons",
  ``nullableML G sn sf ⇔ ∀a. MEM a sf ⇒ nullableML G sn [a]``,
  Induct_on `sf` >> dsimp[nullableML_def] >> qx_gen_tac `h` >>
  Cases_on `h` >> simp[nullableML_def, CONJ_ASSOC]);

val nullable_by_singletons = store_thm(
  "nullable_by_singletons",
  ``nullable G sf ⇔ ∀a. MEM a sf ⇒ nullable G [a]``,
  Induct_on `sf` >> simp[] >> qx_gen_tac `h` >> Cases_on `h` >>
  dsimp[nullable_CONS_NT] >> metis_tac[])

val ptree_nullableML = store_thm(
  "ptree_nullableML",
  ``∀pt sn. DISJOINT (ptree_NTs pt) sn ∧ ptree_fringe pt = [] ∧
            valid_ptree G pt ∧ ptree_rptfree pt ⇒
            nullableML G sn [ptree_head pt]``,
  HO_MATCH_MP_TAC grammarTheory.ptree_ind >>
  simp[nullableML_def, ptree_NTs_def, ptree_rptfree_def] >>
  qx_gen_tac `subs` >> strip_tac >> dsimp[] >>
  dsimp[FLAT_EQ_NIL, listTheory.MEM_MAP] >> map_every qx_gen_tac [`N`, `sn`] >>
  strip_tac >> simp[EXTENSION] >> qexists_tac `MAP ptree_head subs` >> simp[] >>
  simp[Once nullableML_by_singletons] >> dsimp[listTheory.MEM_MAP] >>
  `∀p. MEM p subs ⇒ DISJOINT (ptree_NTs p) (N INSERT sn)`
    suffices_by simp[] >>
  simp[Once DISJOINT_SYM, DISJOINT_INSERT] >> simp[Once DISJOINT_SYM]);

val rptfree_subtree = store_thm(
  "rptfree_subtree",
  ``∀pt. ptree_rptfree pt ∧ N ∈ ptree_NTs pt ∧ ptree_fringe pt = [] ∧
         valid_ptree G pt ⇒
         ∃pt'. ptree_rptfree pt' ∧ ptree_head pt' = NT N ∧
               ptree_fringe pt' = [] ∧ valid_ptree G pt'``,
  HO_MATCH_MP_TAC grammarTheory.ptree_ind >>
  simp[ptree_rptfree_def, ptree_NTs_def] >> qx_gen_tac `subs` >> strip_tac >>
  dsimp[listTheory.MEM_MAP, FLAT_EQ_NIL] >> conj_tac
  >- (strip_tac >> qexists_tac `Nd N subs` >>
      dsimp[ptree_rptfree_def, FLAT_EQ_NIL, listTheory.MEM_MAP]) >>
  map_every qx_gen_tac [`N'`, `pt`] >> strip_tac >> metis_tac[]);

val rptfree_nullable_ptrees_possible = store_thm(
  "rptfree_nullable_ptrees_possible",
  ``∀pt. valid_ptree G pt ∧ ptree_fringe pt = [] ⇒
         ∃pt'. valid_ptree G pt' ∧ ptree_head pt' = ptree_head pt ∧
               ptree_fringe pt' = [] ∧ ptree_rptfree pt'``,
  HO_MATCH_MP_TAC grammarTheory.ptree_ind >>
  dsimp[FLAT_EQ_NIL, listTheory.MEM_MAP] >>
  map_every qx_gen_tac [`subs`, `N`] >> rpt strip_tac >>
  `∃subs'. MAP ptree_head subs' = MAP ptree_head subs ∧
           ∀p. MEM p subs' ⇒
                 valid_ptree G p ∧ ptree_fringe p = [] ∧
                 ptree_rptfree p`
    by (qpat_assum `MAP ptree_head subs ∈ G.rules ' N` (K ALL_TAC) >>
        Induct_on `subs` >- (rpt strip_tac >> qexists_tac `[]` >> simp[]) >>
        dsimp[] >> qx_gen_tac `h` >> rpt strip_tac >> fs[] >>
        qexists_tac `pt'::subs'` >> dsimp[]) >>
  Cases_on `∃pt. MEM pt subs' ∧ N ∈ ptree_NTs pt`
  >- (fs[] >> metis_tac[rptfree_subtree]) >>
  fs[] >> qexists_tac `Nd N subs'` >>
  dsimp[ptree_rptfree_def, FLAT_EQ_NIL, listTheory.MEM_MAP] >> metis_tac[])

val nullable_nullableML = store_thm(
  "nullable_nullableML",
  ``∀sf. nullable G sf ⇒ nullableML G ∅ sf``,
  simp[Once nullable_by_singletons, Once nullableML_by_singletons] >>
  ntac 2 strip_tac >> qx_gen_tac `a` >> strip_tac >>
  `nullable G [a]` by res_tac >>
  `derives G [a] []` by fs[nullable_def] >>
  qspecl_then [`Lf a`, `[]`] mp_tac ptrees_derive_extensible >> simp[] >>
  disch_then (qxchl [`pt`] strip_assume_tac) >>
  `∃pt'. ptree_rptfree pt' ∧ ptree_head pt' = ptree_head pt ∧
         ptree_fringe pt' = [] ∧ valid_ptree G pt'`
    by metis_tac [rptfree_nullable_ptrees_possible] >>
  qspecl_then [`pt'`, `∅`] mp_tac ptree_nullableML >> simp[]);

val nullableML_EQN = store_thm(
  "nullableML_EQN",
  ``nullable G sf ⇔ nullableML G ∅ sf``,
  metis_tac[nullable_nullableML, nullableML_nullable])


val _ = export_theory()
