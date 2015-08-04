open HolKernel Parse boolLib bossLib

open listTheory
open grammarTheory
open lcsymtacs
open pred_setTheory

val rveq = rpt BasicProvers.VAR_EQ_TAC
fun asm_match q = Q.MATCH_ASSUM_RENAME_TAC q

val MAP_EQ_CONS = prove(
  ``(MAP f l = h::t) ⇔ ∃e es. l = e::es ∧ f e = h ∧ MAP f es = t``,
  Cases_on `l` >> simp[])

fun Store_thm(n,t,tac) = store_thm(n,t,tac) before export_rewrites [n]

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
  "nullable_CONS_TOK[simp]",
  ``nullable G (TOK t :: rest) = F``,
  simp[nullable_def] >> strip_tac >>
  qspecl_then [`G`, `[]`, `rest`, `t`, `[]`] mp_tac derives_TOK >> simp[])

val nullable_NIL = store_thm(
  "nullable_NIL[simp]",
  ``nullable G [] = T``,
  simp[nullable_def])

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
  simp[Once nullableML_by_singletons] >> dsimp[listTheory.MEM_MAP]);

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
  metis_tac[]);

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

(* ----------------------------------------------------------------------
    Calculating first sets
   ---------------------------------------------------------------------- *)

val firstSet_def = Define`
  firstSet G sf = { t | ∃rest. derives G sf (TOK t :: rest) }
`;

val firstSet_nonempty_fringe = store_thm(
  "firstSet_nonempty_fringe",
  ``∀pt t rest. ptree_fringe pt = TOK t :: rest ∧ valid_ptree G pt ⇒
                t ∈ firstSet G [ptree_head pt]``,
  simp[firstSet_def] >> metis_tac [grammarTheory.valid_ptree_derive]);

val IN_firstSet = store_thm(
  "IN_firstSet",
  ``t ∈ firstSet G [sym] ⇒
    ∃pt rest. ptree_head pt = sym ∧ valid_ptree G pt ∧
              ptree_fringe pt = TOK t :: rest``,
  simp[firstSet_def] >>
  metis_tac [grammarTheory.ptrees_derive_extensible
               |> Q.SPECL [`Lf sym`, `TOK t :: rest`]
               |> SIMP_RULE (srw_ss()) []]);

val derives_preserves_leading_toks = store_thm(
  "derives_preserves_leading_toks",
  ``∀G syms rest x.
        derives G (MAP TOK syms ++ rest) x ⇔
        ∃rest'. derives G rest rest' ∧ x = MAP TOK syms ++ rest'``,
  rpt gen_tac >> eq_tac
  >- (`∀x y. derives G x y ⇒
             ∀syms rest.
               (x = MAP TOK syms ++ rest) ⇒
               ∃rest'. derives G rest rest' ∧ y = MAP TOK syms ++ rest'`
        suffices_by metis_tac[] >>
      ho_match_mp_tac relationTheory.RTC_INDUCT >> rw[] >>
      fs[grammarTheory.derive_def] >> rveq >>
      qpat_assum `MAP TOK syms ++ rest = Y` mp_tac >>
      dsimp[listTheory.APPEND_EQ_APPEND, MAP_EQ_APPEND, MAP_EQ_CONS,
            listTheory.APPEND_EQ_SING] >> rw[] >>
      first_x_assum (qspec_then `syms` mp_tac) >>
      simp_tac bool_ss [listTheory.APPEND_11, GSYM APPEND_ASSOC] >>
      rw[] >>
      metis_tac [grammarTheory.derive_def, relationTheory.RTC_CASES1,
                 listTheory.APPEND]) >>
  rw[] >> match_mp_tac grammarTheory.derives_paste_horizontally >>
  simp[]);

val firstSet_NIL = Store_thm(
  "firstSet_NIL",
  ``firstSet G [] = {}``,
  simp[firstSet_def] >> simp[Once relationTheory.RTC_CASES1] >>
  simp[grammarTheory.derive_def]);

val firstSet_TOK = store_thm(
  "firstSet_TOK[simp]",
  ``firstSet G (TOK t::rest) = {t}``,
  simp[firstSet_def, EXTENSION, EQ_IMP_THM] >> rw[]
  >- (qspecl_then [`G`, `[t]`, `rest`] mp_tac derives_preserves_leading_toks >>
      simp[] >> strip_tac >> fs[]) >>
  metis_tac[relationTheory.RTC_REFL]);

val firstSet_NT = store_thm(
  "firstSet_NT",
  ``firstSet G (NT N :: rest) =
      if N ∈ FDOM G.rules then
        BIGUNION (IMAGE (firstSet G) (G.rules ' N)) ∪
        (if nullable G [NT N] then firstSet G rest
         else {})
      else {}``,
  reverse (Cases_on `N ∈ FDOM G.rules`)
  >- simp[firstSet_def, derives_leading_nonNT] >>
  simp[Once EXTENSION] >> qx_gen_tac `t` >> reverse eq_tac
  >- (dsimp[] >> rw[] >> fs[firstSet_def]
      >- (asm_match `rhs ∈ G.rules ' N` >>
          asm_match `derives G rhs (TOK t :: rest0)` >>
          qexists_tac`rest0 ++ rest` >>
          match_mp_tac RTC_R_I >>
          qexists_tac `rhs ++ rest` >> simp[grammarTheory.derive_def] >>
          metis_tac [listTheory.APPEND, APPEND_ASSOC,
                     grammarTheory.derives_paste_horizontally,
                     relationTheory.RTC_REFL]) >>
      fs[nullable_def] >>
      metis_tac [listTheory.APPEND,
                 grammarTheory.derives_paste_horizontally]) >>
  dsimp[firstSet_def] >> qx_gen_tac `rest'` >> strip_tac >>
  `∃Z1 Z2. derives G [NT N] Z1 ∧ derives G rest Z2 ∧
           (TOK t :: rest' = Z1 ++ Z2)`
    by metis_tac [derives_split_horizontally, listTheory.APPEND] >>
  Cases_on `Z1`
  >- (`nullableNT G N` by fs[nullable_def] >> fs[] >> metis_tac[]) >>
  fs[] >> rveq >>
  qpat_assum `derives G [NT N] X`
    (mp_tac o ONCE_REWRITE_RULE [relationTheory.RTC_CASES1]) >>
  simp[] >> metis_tac[]);

val firstSetML_def = tDefine "firstSetML" `
  firstSetML seen [] = {} ∧
  firstSetML seen (TOK t :: _) = {t} ∧
  firstSetML seen (NT n :: rest) =
    if n ∈ FDOM G.rules then
      (if n ∉ seen then
        BIGUNION (IMAGE (firstSetML (n INSERT seen))
                        (G.rules ' n))
       else {}) ∪
      (if nullable G [NT n] then firstSetML seen rest
       else {})
    else {}
`
  (WF_REL_TAC `measure (λs. CARD (FDOM G.rules DIFF s)) LEX measure LENGTH` >>
   simp[] >> rw[] >> DISJ1_TAC >> simp[CARD_DIFF_EQN] >>
   simp[Once INTER_COMM] >> simp[INSERT_INTER] >>
   simp[FINITE_INTER] >> simp[Once INTER_COMM] >>
   simp[arithmeticTheory.SUB_LEFT_LESS] >>
   match_mp_tac arithmeticTheory.LESS_LESS_EQ_TRANS >>
   qexists_tac `CARD (n INSERT FDOM G.rules ∩ seen)` >>
   conj_tac >- simp[] >>
   `FINITE (FDOM G.rules)` by simp[] >>
   pop_assum (MATCH_MP_TAC o MATCH_MP CARD_SUBSET) >>
   simp[SUBSET_DEF])

val firstSetML_firstSet = store_thm(
  "firstSetML_firstSet",
  ``∀seen sf. firstSetML G seen sf ⊆ firstSet G sf``,
  ho_match_mp_tac (theorem "firstSetML_ind") >> simp[firstSetML_def] >>
  map_every qx_gen_tac [`seen`, `N`, `sf`] >> strip_tac >>
  reverse (Cases_on `N ∈ FDOM G.rules`) >> fs[] >>
  reverse conj_tac
  >- (rw[] >> fs[] >> simp[firstSet_NT] >> fs[SUBSET_DEF]) >>
  Cases_on `N ∈ seen` >> simp[] >>
  dsimp[SUBSET_DEF] >> simp[firstSet_NT] >> rpt strip_tac >>
  DISJ1_TAC >> dsimp[] >> fs[SUBSET_DEF] >> metis_tac[]);

val nts_derive_def = Define`
  (nts_derive G [] tok ⇔ F) ∧
  (nts_derive G [N] tok ⇔
    N ∈ FDOM G.rules ∧
    ∃p s. p ++ [TOK tok] ++ s ∈ G.rules ' N ∧
          nullable G p) ∧
  (nts_derive G (N1::N2::NS) tok ⇔
    N1 ∈ FDOM G.rules ∧
    ∃p s. p ++ [NT N2] ++ s ∈ G.rules ' N1 ∧
          nullable G p ∧
          nts_derive G (N2::NS) tok)
`;
val _ = export_rewrites ["nts_derive_def"]

val nts_derive_APPEND_E = store_thm(
  "nts_derive_APPEND_E",
  ``nts_derive G (n1 ++ n2) t ∧ n2 ≠ [] ⇒ nts_derive G n2 t``,
  Induct_on `n1` >> simp[] >> reverse (Cases_on `n1`)
  >- (rpt strip_tac >> fs[]) >>
  fs[] >> Cases_on `n2` >> simp[] >> metis_tac[]);

val firstSetML_nullable_prefix = store_thm(
  "firstSetML_nullable_prefix",
  ``x ∈ firstSetML G sn sf ∧ nullable G p ⇒
    x ∈ firstSetML G sn (p ++ sf)``,
  Induct_on `p` >> simp[] >> Cases >>
  simp[firstSetML_def, nullable_CONS_NT]);

val firstSetML_CONS_I = store_thm(
  "firstSetML_CONS_I",
  ``tk ∈ firstSetML G sn [h] ⇒ tk ∈ firstSetML G sn (h::t)``,
  Cases_on `h` >> simp[firstSetML_def] >> rw[]);

val firstSet_CONS_I = store_thm(
  "firstSet_CONS_I",
  ``tk ∈ firstSet G [h] ⇒ tk ∈ firstSet G (h::t)``,
  Cases_on `h` >> simp[firstSet_NT] >> rw[]);

val distinct_nts_derive_firstSetML = store_thm(
  "distinct_nts_derive_firstSetML",
  ``∀sn. nts_derive G ns tok ∧ ALL_DISTINCT ns ∧
         set ns ∩ sn = ∅ ⇒
         tok ∈ firstSetML G sn [NT (HD ns)]``,
  Induct_on `ns` >> simp[] >>
  Cases_on `ns`
  >- (simp[firstSetML_def] >> map_every qx_gen_tac [`N`, `seen`] >>
      simp[Once EXTENSION] >> dsimp[] >>
      map_every qx_gen_tac [`p`, `s`] >> strip_tac >>
      qexists_tac `p ++ [TOK tok] ++ s` >> simp[] >>
      REWRITE_TAC [GSYM APPEND_ASSOC] >>
      match_mp_tac firstSetML_nullable_prefix >>
      simp[firstSetML_def]) >>
  simp[EXTENSION] >> rpt strip_tac >>
  asm_match `p ++ [NT N'] ++ s ∈ G.rules ' N` >>
  simp[firstSetML_def] >> `N ∉ sn` by metis_tac[] >>
  dsimp[] >> qexists_tac `p ++ [NT N'] ++ s` >> simp[] >>
  REWRITE_TAC [GSYM APPEND_ASSOC] >>
  match_mp_tac firstSetML_nullable_prefix >> simp[] >>
  match_mp_tac firstSetML_CONS_I >> fs[] >>
  first_x_assum match_mp_tac >> simp[EXTENSION] >>
  metis_tac[]);

val heads_give_first = prove(
  ``FLAT (MAP ptree_fringe subs) = tk :: rest ⇒
    ∃p sym s r0.
      p ++ [sym] ++ s = subs ∧ ptree_fringe sym = tk :: r0 ∧
      FLAT (MAP ptree_fringe p) = []``,
  Induct_on `subs` >> simp[] >> simp[APPEND_EQ_CONS] >> rpt strip_tac >>
  dsimp[] >>fs[] >> map_every qexists_tac [`sym`, `s`, `r0`, `p`] >> simp[]);

val nullable_alltrees = store_thm(
  "nullable_alltrees",
  ``nullable G sf ⇔
    ∀sym. MEM sym sf ⇒
          ∃pt. valid_ptree G pt ∧ ptree_head pt = sym ∧ ptree_fringe pt = []``,
  simp[Once nullable_by_singletons] >> eq_tac >> rpt strip_tac >> res_tac
  >- (pop_assum mp_tac >> simp_tac (srw_ss())[nullable_def] >>
      simp[singleton_derives_ptree]) >>
  simp[nullable_def] >> rw[] >> metis_tac [valid_ptree_derive]);

val MEM_last_strip = prove(
  ``∀l. MEM e l ⇒ ∃p s. l = p ++ [e] ++ s ∧ ¬MEM e s``,
  ho_match_mp_tac rich_listTheory.SNOC_INDUCT >> dsimp[] >> conj_tac
  >- (qx_gen_tac `l` >> strip_tac >> map_every qexists_tac [`l`, `[]`] >>
      simp[]) >>
  map_every qx_gen_tac [`l`, `x`] >> rpt strip_tac >> fs[] >>
  Cases_on `x = e`
  >- (map_every qexists_tac [`p ++ [e] ++ s`, `[]`] >> simp[]) >>
  map_every qexists_tac [`p`, `s ++ [x]`] >> simp[]);

val firstSet_nts_derive = store_thm(
  "firstSet_nts_derive",
  ``tk ∈ firstSet G [NT N] ⇒
    ∃Ns. ALL_DISTINCT Ns ∧ nts_derive G Ns tk ∧ HD Ns = N``,
  strip_tac >> pop_assum (strip_assume_tac o MATCH_MP IN_firstSet) >>
  rpt (pop_assum mp_tac) >> map_every qid_spec_tac [`N`, `rest`, `pt`] >>
  ho_match_mp_tac ptree_ind >> simp[] >> rpt strip_tac >>
  imp_res_tac heads_give_first >> rveq >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  `nullable G (MAP ptree_head p)`
    by (dsimp[nullable_alltrees, MEM_MAP] >>
        full_simp_tac (srw_ss() ++ boolSimps.DNF_ss) [MEM_MAP, FLAT_EQ_NIL] >>
        metis_tac[]) >>
  Cases_on `ptree_head sym`
  >- (qexists_tac `[s]` >> simp[] >> Cases_on `sym` >> fs[] >> metis_tac[]) >>
  fs[] >> asm_match `nts_derive G Ns tk` >>
  Cases_on `MEM s Ns`
  >- (pop_assum (qxchl [`Ns0`, `Ns1`] strip_assume_tac o
                 MATCH_MP MEM_last_strip) >>
      `nts_derive G (s::Ns1) tk`
        by (match_mp_tac (GEN_ALL nts_derive_APPEND_E) >> simp[] >>
            fs[] >> qexists_tac `Ns0` >>
            RULE_ASSUM_TAC (REWRITE_RULE[GSYM APPEND_ASSOC, APPEND]) >>
            simp[]) >>
      qexists_tac `s::Ns1` >> simp[] >> fs[ALL_DISTINCT_APPEND]) >>
  qexists_tac `s::Ns` >> simp[] >> Cases_on `Ns` >> fs[] >> metis_tac[]);

val firstSet_singleton = store_thm(
  "firstSet_singleton",
  ``tk ∈ firstSet G sf ⇔
    ∃p e s. sf = p ++ [e] ++ s ∧ nullable G p ∧ tk ∈ firstSet G [e]``,
  Induct_on `sf` >> simp[] >> Cases_on `h` >> simp[] >> eq_tac >> strip_tac
  >- (map_every qexists_tac [`[]`, `TOK tk`, `sf`] >> simp[])
  >- (fs[APPEND_EQ_CONS] >> rw[] >> fs[])
  >- (fs[firstSet_NT] >> pop_assum mp_tac >> rw[]
      >- (asm_match `rhs ∈ G.rules ' N` >>
          map_every qexists_tac [`[]`, `NT N`, `sf`] >> simp[] >>
          dsimp[firstSet_NT] >> metis_tac[])
      >- (asm_match `nullableNT G N` >> asm_match `tk ∈ firstSet G [e]` >>
          asm_match `nullable G p` >>
          map_every qexists_tac [`NT N::p`, `e`] >> simp[] >>
          simp[Once nullable_by_singletons, DISJ_IMP_THM, FORALL_AND_THM] >>
          metis_tac[nullable_by_singletons]) >>
      asm_match `tk ∈ firstSet G rhs` >> asm_match `rhs ∈ G.rules ' N` >>
      map_every qexists_tac [`[]`, `NT N`, `sf`] >> simp[] >>
      simp[firstSet_NT] >> metis_tac[]) >>
  Cases_on `p` >> fs[] >> rw[] >- simp[firstSet_CONS_I] >>
  fs[Once nullable_by_singletons, DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[firstSet_NT] >> fs[nullable_CONS_NT] >> metis_tac[]);

val firstSet_firstSetML = store_thm(
  "firstSet_firstSetML",
  ``tk ∈ firstSet G sf ⇒ tk ∈ firstSetML G {} sf``,
  simp[Once firstSet_singleton] >> rw[] >> REWRITE_TAC [GSYM APPEND_ASSOC] >>
  match_mp_tac firstSetML_nullable_prefix >> simp[] >>
  match_mp_tac firstSetML_CONS_I >>
  asm_match `tk ∈ firstSet G [sym]` >>
  Cases_on `sym` >> fs[] >- simp[firstSetML_def] >>
  imp_res_tac firstSet_nts_derive >> rw[] >>
  match_mp_tac distinct_nts_derive_firstSetML >> simp[]);

val firstSetML_eqn = store_thm(
  "firstSetML_eqn",
  ``firstSet G sf = firstSetML G {} sf``,
  simp[EXTENSION, EQ_IMP_THM, firstSet_firstSetML] >>
  metis_tac [SUBSET_DEF, firstSetML_firstSet]);

val _ = export_theory()
