Theory NTproperties
Ancestors
  list grammar pred_set

val rveq = rpt BasicProvers.VAR_EQ_TAC
fun asm_match q = Q.MATCH_ASSUM_RENAME_TAC q

val MAP_EQ_CONS = prove(
  ``(MAP f l = h::t) ⇔ ∃e es. l = e::es ∧ f e = h ∧ MAP f es = t``,
  Cases_on `l` >> simp[])

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

Definition nullable_def:
  nullable G sf = derives G sf []
End
Overload nullableNT = “λG n. nullable G [NT n]”

Theorem derives_TOK:
  ∀G p s t sf.
      derives G (p ++ [TOK t] ++ s) sf ⇒
      ∃ps ss. sf = ps ++ [TOK t] ++ ss ∧ derives G p ps ∧ derives G s ss
Proof
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
    qpat_x_assum `x = y` mp_tac >> simp[Once listTheory.APPEND_EQ_APPEND_MID] >>
    simp[APPEND_EQ_SING'] >> disch_then (qxchl [`l'`] strip_assume_tac) >>
    rw[] >> first_x_assum (qspecl_then [`p`, `l' ++ r ++ s0`, `t`] mp_tac),
    first_x_assum (qspecl_then [`p0 ++ r ++ l`, `s`, `t`] mp_tac)
  ] >>
  simp[] >> disch_then (qxchl [`ps`, `ss`] strip_assume_tac) >>
  map_every qexists_tac [`ps`, `ss`] >> simp[] >>
  match_mp_tac RTC_R_I >> simp[derive_def] >> metis_tac[]
QED

Theorem nullable_CONS_TOK[simp]:
  nullable G (TOK t :: rest) = F
Proof
  simp[nullable_def] >> strip_tac >>
  qspecl_then [`G`, `[]`, `rest`, `t`, `[]`] mp_tac derives_TOK >> simp[]
QED

Theorem nullable_NIL[simp]:
  nullable G [] = T
Proof simp[nullable_def]
QED

Theorem nullable_CONS_NT:
  nullable G (NT n :: rest) <=>
      nullable G rest ∧ n ∈ FDOM G.rules ∧
      ∃r. r ∈ G.rules ' n ∧ nullable G r
Proof
  simp[nullable_def] >> REVERSE eq_tac
  >- (strip_tac >> match_mp_tac RTC_R_I >> simp[derive_def] >>
      qexists_tac `r ++ rest` >> REVERSE conj_tac
      >- metis_tac[derives_paste_horizontally, listTheory.APPEND] >>
      qexists_tac `[]` >> simp[]) >>
  `NT n :: rest = [NT n] ++ rest` by simp[] >> pop_assum SUBST1_TAC >>
  simp[derives_split_horizontally] >> strip_tac >>
  Q.UNDISCH_THEN `derives G [NT n] []`
     (mp_tac o SIMP_RULE (srw_ss()) [Once relationTheory.RTC_CASES1]) >>
  metis_tac[]
QED

Theorem paireq[local]: (x,y) = z ⇔ x = FST z ∧ y = SND z
Proof Cases_on `z` >> simp[]
QED

Theorem GSPEC_INTER[local]:
  GSPEC f ∩ Q =
  GSPEC (S ($, o FST o f) (S ($/\ o SND o f) (Q o FST o f)))
Proof
  simp[GSPECIFICATION, EXTENSION, SPECIFICATION] >> qx_gen_tac `e` >>
  simp[paireq] >> metis_tac[]
QED

val example = SCONV [GSPEC_INTER, combinTheory.o_ABS_R, combinTheory.S_ABS_R,
                     combinTheory.S_ABS_L, pairTheory.o_UNCURRY_R,
                     pairTheory.S_UNCURRY_R] ``{ n + m | n > 10 ∧ m < 3 } ∩ Q``

(* nullableML is an "executable" version of nullable that examines the grammar
   to determine nullability. I put the "executable" in quotes because of the
   scary looking set comprehension below.  This will work fine if the
   sets of rules for non-terminals are always finite. *)
Definition nullableML_def[schematic]:
  nullableML seen [] = T ∧
  nullableML seen (TOK t :: _) = F ∧
  nullableML seen (NT n :: rest) =
      if n ∈ FDOM G.rules ∧ n ∉ seen then
        if G.rules ' n ∩ { r | nullableML (n INSERT seen) r } = ∅ then F
        else nullableML seen rest
      else F
Termination
  WF_REL_TAC `measure (λs. CARD (FDOM G.rules DIFF s)) LEX measure LENGTH` >>
  rpt strip_tac >> simp[] >> DISJ1_TAC >> simp[CARD_DIFF_EQN] >>
  simp[Once INTER_COMM] >> simp[INSERT_INTER] >>
  simp[FINITE_INTER] >> simp[Once INTER_COMM] >>
  simp[arithmeticTheory.SUB_LEFT_LESS] >>
  match_mp_tac arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists_tac `CARD (n INSERT FDOM G.rules ∩ seen)` >>
  conj_tac >- simp[] >>
  `FINITE (FDOM G.rules)` by simp[] >>
  pop_assum (MATCH_MP_TAC o MATCH_MP CARD_SUBSET) >>
  simp[SUBSET_DEF]
End

Theorem nullableML_nullable:
  ∀sn sf. nullableML G sn sf ⇒ nullable G sf
Proof
  HO_MATCH_MP_TAC (theorem "nullableML_ind") >>
  simp[nullableML_def, nullable_CONS_NT] >>
  map_every qx_gen_tac [`sn`, `N`, `sf`] >> rpt strip_tac >>
  qpat_x_assum `SS ≠ ∅` mp_tac >> simp[EXTENSION] >> metis_tac[]
QED

Definition ptree_NTs_def:
  (ptree_NTs (Lf (l,_)) = case l of NT N => {N} | _ => ∅) ∧
  (ptree_NTs (Nd (n,_) subs) = n INSERT BIGUNION (IMAGE ptree_NTs (set subs)))
End

Definition ptree_rptfree_def:
  ptree_rptfree (Lf _) = T ∧
  ptree_rptfree (Nd (N,_) subs) =
    ∀s. MEM s subs ⇒ ptree_rptfree s ∧ N ∉ ptree_NTs s
End

Theorem nullableML_by_singletons:
  nullableML G sn sf ⇔ ∀a. MEM a sf ⇒ nullableML G sn [a]
Proof
  Induct_on `sf` >> dsimp[nullableML_def] >> qx_gen_tac `h` >>
  Cases_on `h` >> simp[nullableML_def, CONJ_ASSOC]
QED

Theorem nullable_by_singletons:
  nullable G sf ⇔ ∀a. MEM a sf ⇒ nullable G [a]
Proof
  Induct_on `sf` >> simp[] >> qx_gen_tac `h` >> Cases_on `h` >>
  dsimp[nullable_CONS_NT] >> metis_tac[]
QED

Theorem ptree_nullableML:
  ∀pt sn. DISJOINT (ptree_NTs pt) sn ∧ ptree_fringe pt = [] ∧
          valid_ptree G pt ∧ ptree_rptfree pt ⇒
          nullableML G sn [ptree_head pt]
Proof
  HO_MATCH_MP_TAC grammarTheory.ptree_ind >>
  strip_tac >- (rw[] >> Cases_on`pt` >> fs[]) >>
  qx_gen_tac `subs` >> strip_tac >> dsimp[] >>
  dsimp[FLAT_EQ_NIL, listTheory.MEM_MAP] >>
  map_every qx_gen_tac [`N`, `sn`] >> Cases_on `N` >>
  simp[nullableML_def, ptree_NTs_def, ptree_rptfree_def] >>
  strip_tac >> simp[EXTENSION] >>
  qexists_tac `MAP ptree_head subs` >> simp[] >>
  simp[Once nullableML_by_singletons] >> dsimp[listTheory.MEM_MAP] >>
  rw[] >> res_tac >> rw[]
QED

Theorem rptfree_subtree:
  ∀pt : (α,β,γ) parsetree.
      ptree_rptfree pt ∧ N ∈ ptree_NTs pt ∧ ptree_fringe pt = [] ∧
      valid_ptree G pt ⇒
      ∃pt' : (α,β,γ) parsetree.
        ptree_rptfree pt' ∧ ptree_head pt' = NT N ∧
        ptree_fringe pt' = [] ∧ valid_ptree G pt'
Proof
  HO_MATCH_MP_TAC grammarTheory.ptree_ind >>
  strip_tac >- (rw[] >> Cases_on`pt` >> fs[]) >>
  simp[ptree_rptfree_def, ptree_NTs_def] >> qx_gen_tac `subs` >> strip_tac >>
  dsimp[listTheory.MEM_MAP, FLAT_EQ_NIL] >>
  NTAC 2 strip_tac >>
  Cases_on `pt` >>
  fs[ptree_rptfree_def, FLAT_EQ_NIL, listTheory.MEM_MAP,ptree_NTs_def]
  >-(qexists_tac `Nd (N, ARB) subs` >>
     fs[ptree_rptfree_def, FLAT_EQ_NIL, listTheory.MEM_MAP] >> dsimp[]) >>
  metis_tac[]
QED

Theorem rptfree_nullable_ptrees_possible:
  ∀pt : (α,β,γ) parsetree.
      valid_ptree G pt ∧ ptree_fringe pt = [] ⇒
      ∃pt' : (α,β,γ) parsetree.
        valid_ptree G pt' ∧ ptree_head pt' = ptree_head pt ∧
        ptree_fringe pt' = [] ∧ ptree_rptfree pt'
Proof
  HO_MATCH_MP_TAC grammarTheory.ptree_ind >>
  strip_tac >- (rw[] >> Cases_on`pt` >> fs[]) >>
  dsimp[FLAT_EQ_NIL, listTheory.MEM_MAP] >>
  map_every qx_gen_tac [`subs`, `N`] >> rpt strip_tac >>
  Cases_on `N` >> fs[] >>
  `∃subs' : (α,β,γ) parsetree list.
      MAP ptree_head subs' = MAP ptree_head subs ∧
      ∀p. MEM p subs' ⇒
            valid_ptree G p ∧ ptree_fringe p = [] ∧
            ptree_rptfree p`
    by (qpat_x_assum `MAP ptree_head subs ∈ G.rules ' q` (K ALL_TAC) >>
        Induct_on `subs` >- (rpt strip_tac >> qexists_tac `[]` >> simp[]) >>
        dsimp[] >> qx_gen_tac `h` >> rpt strip_tac >> fs[] >>
        qexists_tac `pt'::subs'` >> dsimp[] >> metis_tac[]) >>
  Cases_on `∃pt. MEM pt subs' ∧ q ∈ ptree_NTs pt`
  >- (fs[] >> metis_tac[rptfree_subtree]) >>
  fs[] >> qexists_tac `Nd (q,r) subs'` >>
  dsimp[ptree_rptfree_def, FLAT_EQ_NIL, listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem nullable_nullableML:
  ∀sf. nullable G sf ⇒ nullableML G ∅ sf
Proof
  simp[Once nullable_by_singletons, Once nullableML_by_singletons] >>
  ntac 2 strip_tac >> qx_gen_tac `a` >> strip_tac >>
  ‘nullable G [a]’ by res_tac >>
  ‘derives G [a] []’ by fs[nullable_def] >>
  qspecl_then [`Lf (a, ARB)`, `[]`] mp_tac ptrees_derive_extensible >> simp[] >>
  disch_then (qxchl [`pt`] strip_assume_tac) >>
  ‘∃pt' : (α,β)lfptree.
         ptree_rptfree pt' ∧ ptree_head pt' = ptree_head pt ∧
         ptree_fringe pt' = [] ∧ valid_ptree G pt'’
    by metis_tac [rptfree_nullable_ptrees_possible] >>
  qspec_then ‘pt'’ assume_tac ptree_nullableML >>
  pop_assum (qspecl_then [`∅`] mp_tac) >> simp[]
QED

Theorem nullableML_EQN:
  nullable G sf ⇔ nullableML G ∅ sf
Proof
  metis_tac[nullable_nullableML, nullableML_nullable]
QED

(* ----------------------------------------------------------------------
    Calculating first sets
   ---------------------------------------------------------------------- *)

Definition firstSet_def:
  firstSet G sf = { t | ∃rest. derives G sf (TOK t :: rest) }
End

Theorem firstSet_nonempty_fringe:
  ∀pt t rest. ptree_fringe pt = TOK t :: rest ∧ valid_ptree G pt ⇒
              t ∈ firstSet G [ptree_head pt]
Proof simp[firstSet_def] >> metis_tac [grammarTheory.valid_ptree_derive]
QED

Theorem IN_firstSet:
  t ∈ firstSet G [sym] ⇒
  ∃pt:(α,β)lfptree rest.
     ptree_head pt = sym ∧ valid_ptree G pt ∧
     ptree_fringe pt = TOK t :: rest
Proof
  simp[firstSet_def] >>
  metis_tac [grammarTheory.ptrees_derive_extensible
               |> Q.SPECL [`Lf (sym,())`, `TOK t :: rest`]
               |> SIMP_RULE (srw_ss()) []]
QED

Theorem derives_preserves_leading_toks:
  ∀G syms rest x.
      derives G (MAP TOK syms ++ rest) x ⇔
      ∃rest'. derives G rest rest' ∧ x = MAP TOK syms ++ rest'
Proof
  rpt gen_tac >> eq_tac
  >- (`∀x y. derives G x y ⇒
             ∀syms rest.
               (x = MAP TOK syms ++ rest) ⇒
               ∃rest'. derives G rest rest' ∧ y = MAP TOK syms ++ rest'`
        suffices_by metis_tac[] >>
      ho_match_mp_tac relationTheory.RTC_INDUCT >> rw[] >>
      fs[grammarTheory.derive_def] >> rveq >>
      qpat_x_assum `MAP TOK syms ++ rest = Y` mp_tac >>
      dsimp[listTheory.APPEND_EQ_APPEND, MAP_EQ_APPEND, MAP_EQ_CONS,
            listTheory.APPEND_EQ_SING] >> rw[] >>
      first_x_assum (qspec_then `syms` mp_tac) >>
      simp_tac bool_ss [listTheory.APPEND_11, GSYM APPEND_ASSOC] >>
      rw[] >>
      metis_tac [grammarTheory.derive_def, relationTheory.RTC_CASES1,
                 listTheory.APPEND]) >>
  rw[] >> match_mp_tac grammarTheory.derives_paste_horizontally >>
  simp[]
QED

Theorem firstSet_NIL[simp]:    firstSet G [] = {}
Proof
  simp[firstSet_def] >> simp[Once relationTheory.RTC_CASES1] >>
  simp[grammarTheory.derive_def]
QED

Theorem firstSet_TOK[simp]:
  firstSet G (TOK t::rest) = {t}
Proof
  simp[firstSet_def, EXTENSION, EQ_IMP_THM] >> rw[]
  >- (qspecl_then [`G`, `[t]`, `rest`] mp_tac derives_preserves_leading_toks >>
      simp[] >> strip_tac >> fs[]) >>
  metis_tac[relationTheory.RTC_REFL]
QED

Theorem firstSet_NT:
  firstSet G (NT N :: rest) =
      if N ∈ FDOM G.rules then
        BIGUNION (IMAGE (firstSet G) (G.rules ' N)) ∪
        (if nullable G [NT N] then firstSet G rest
         else {})
      else {}
Proof
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
  qpat_x_assum `derives G [NT N] X`
    (mp_tac o ONCE_REWRITE_RULE [relationTheory.RTC_CASES1]) >>
  simp[] >> metis_tac[]
QED

Definition firstSetML_def[schematic]:
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
Termination
  WF_REL_TAC `measure (λs. CARD (FDOM G.rules DIFF s)) LEX measure LENGTH` >>
  simp[] >> rw[] >> DISJ1_TAC >> simp[CARD_DIFF_EQN] >>
  simp[Once INTER_COMM] >> simp[INSERT_INTER] >>
  simp[FINITE_INTER] >> simp[Once INTER_COMM] >>
  simp[arithmeticTheory.SUB_LEFT_LESS] >>
  match_mp_tac arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists_tac `CARD (n INSERT FDOM G.rules ∩ seen)` >>
  conj_tac >- simp[] >>
  `FINITE (FDOM G.rules)` by simp[] >>
  pop_assum (MATCH_MP_TAC o MATCH_MP CARD_SUBSET) >>
  simp[SUBSET_DEF]
End

Theorem firstSetML_firstSet:
  ∀seen sf. firstSetML G seen sf ⊆ firstSet G sf
Proof
  ho_match_mp_tac firstSetML_ind >> simp[firstSetML_def] >>
  map_every qx_gen_tac [`seen`, `N`, `sf`] >> strip_tac >>
  reverse (Cases_on `N ∈ FDOM G.rules`) >> fs[] >>
  reverse conj_tac
  >- (rw[] >> fs[] >> simp[firstSet_NT] >> fs[SUBSET_DEF]) >>
  Cases_on `N ∈ seen` >> simp[] >>
  dsimp[SUBSET_DEF] >> simp[firstSet_NT] >> rpt strip_tac >>
  DISJ1_TAC >> dsimp[] >> fs[SUBSET_DEF] >> metis_tac[]
QED

(* there is a "path" of non-terminals were N₁ -> N₂ if N₂ appears in a rhs for
   N₁, and in the last one, there is a rhs where the given tok can appear
   first
*)
Definition nts_derive_def[simp]:
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
End

Theorem nts_derive_APPEND_E:
  nts_derive G (n1 ++ n2) t ∧ n2 ≠ [] ⇒ nts_derive G n2 t
Proof
  Induct_on `n1` >> simp[] >> reverse (Cases_on `n1`)
  >- (rpt strip_tac >> fs[]) >>
  fs[] >> Cases_on `n2` >> simp[] >> metis_tac[]
QED

Theorem firstSetML_nullable_prefix:
  x ∈ firstSetML G sn sf ∧ nullable G p ⇒
    x ∈ firstSetML G sn (p ++ sf)
Proof
  Induct_on `p` >> simp[] >> Cases >>
  simp[firstSetML_def, nullable_CONS_NT]
QED

Theorem firstSetML_CONS_I:
  tk ∈ firstSetML G sn [h] ⇒ tk ∈ firstSetML G sn (h::t)
Proof Cases_on `h` >> simp[firstSetML_def] >> rw[]
QED

Theorem firstSet_CONS_I:
  tk ∈ firstSet G [h] ⇒ tk ∈ firstSet G (h::t)
Proof Cases_on `h` >> simp[firstSet_NT] >> rw[]
QED

Theorem distinct_nts_derive_firstSetML:
  ∀sn. nts_derive G ns tok ∧ ALL_DISTINCT ns ∧ set ns ∩ sn = ∅ ⇒
       tok ∈ firstSetML G sn [NT (HD ns)]
Proof
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
  metis_tac[]
QED

Theorem heads_give_first[local]:
  FLAT (MAP ptree_fringe subs) = tk :: rest ⇒
    ∃p sym s r0.
      p ++ [sym] ++ s = subs ∧ ptree_fringe sym = tk :: r0 ∧
      FLAT (MAP ptree_fringe p) = []
Proof
  Induct_on `subs` >> simp[] >> simp[APPEND_EQ_CONS] >> rpt strip_tac >>
  dsimp[] >>fs[] >> map_every qexists_tac [`sym`, `s`, `r0`, `p`] >> simp[]
QED

Theorem nullable_alltrees:
  nullable G sf ⇔
    ∀sym. MEM sym sf ⇒
          ∃pt:(α,β)lfptree.
            valid_ptree G pt ∧ ptree_head pt = sym ∧ ptree_fringe pt = []
Proof
  simp[Once nullable_by_singletons] >> eq_tac >> rpt strip_tac >> res_tac
  >- (pop_assum mp_tac >> simp_tac (srw_ss())[nullable_def] >>
      simp[singleton_derives_ptree]) >>
  simp[nullable_def] >> rw[] >> metis_tac [valid_ptree_derive]
QED

Theorem MEM_last_strip[local]:
  ∀l. MEM e l ⇒ ∃p s. l = p ++ [e] ++ s ∧ ¬MEM e s
Proof metis_tac[MEM_SPLIT_APPEND_last]
QED

Theorem firstSet_nts_derive:
  tk ∈ firstSet G [NT N] ⇒
    ∃Ns. ALL_DISTINCT Ns ∧ nts_derive G Ns tk ∧ HD Ns = N
Proof
  strip_tac >> pop_assum (strip_assume_tac o MATCH_MP IN_firstSet) >>
  rpt (pop_assum mp_tac) >> map_every qid_spec_tac [`N`, `rest`, `pt`] >>
  ho_match_mp_tac ptree_ind >> simp[] >> rpt strip_tac
  >- (rw[] >> Cases_on`pt` >> fs[]) >>
  Cases_on `pt` >> fs[] >>
  imp_res_tac heads_give_first >> rveq >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  `nullable G (MAP ptree_head p)`
    by (dsimp[nullable_alltrees, MEM_MAP] >>
        full_simp_tac (srw_ss() ++ boolSimps.DNF_ss) [MEM_MAP, FLAT_EQ_NIL] >>
        metis_tac[]) >>
  Cases_on `sym` >> Cases_on `p'` >> fs[]
  >- (qexists_tac `[N]` >> simp[] >> metis_tac[]) >>
  Cases_on `MEM N Ns`
  >- (
    pop_assum (qxchl [`Ns0`, `Ns1`] strip_assume_tac o
                 MATCH_MP MEM_last_strip) >>
      `nts_derive G (N::Ns1) tk`
        by (match_mp_tac (GEN_ALL nts_derive_APPEND_E) >> simp[] >>
            fs[] >> qexists_tac `Ns0` >>
            RULE_ASSUM_TAC (REWRITE_RULE[GSYM APPEND_ASSOC, APPEND]) >>
            simp[]) >>
      qexists_tac `N::Ns1` >> simp[] >> fs[ALL_DISTINCT_APPEND]
      ) >>
  qexists_tac `N::Ns` >> simp[] >> Cases_on `Ns` >> fs[] >> metis_tac[]
QED

Theorem firstSet_singleton:
  tk ∈ firstSet G sf ⇔
    ∃p e s. sf = p ++ [e] ++ s ∧ nullable G p ∧ tk ∈ firstSet G [e]
Proof
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
  simp[firstSet_NT] >> fs[nullable_CONS_NT] >> metis_tac[]
QED

Theorem firstSet_firstSetML:
  tk ∈ firstSet G sf ⇒ tk ∈ firstSetML G {} sf
Proof
  simp[Once firstSet_singleton] >> rw[] >> REWRITE_TAC [GSYM APPEND_ASSOC] >>
  match_mp_tac firstSetML_nullable_prefix >> simp[] >>
  match_mp_tac firstSetML_CONS_I >>
  asm_match `tk ∈ firstSet G [sym]` >>
  Cases_on `sym` >> fs[] >- simp[firstSetML_def] >>
  imp_res_tac firstSet_nts_derive >> rw[] >>
  match_mp_tac distinct_nts_derive_firstSetML >> simp[]
QED

Theorem firstSetML_eqn:
  firstSet G sf = firstSetML G {} sf
Proof
  simp[EXTENSION, EQ_IMP_THM, firstSet_firstSetML] >>
  metis_tac [SUBSET_DEF, firstSetML_firstSet]
QED

(* ----------------------------------------------------------------------
    follow sets
   ---------------------------------------------------------------------- *)

(*
Definition followSet_def:
  followSet (g:(α,β) grammar) (sym:(α,β) symbol) =
    { ts | ∃s pfx sfx.
             MEM s (MAP ruleRhs (rules g)) ∧
             RTC (derives g) s (pfx++[sym]++[TS ts]++sfx) }
End

Definition augment_def:
  augment k v fm =
    case FLOOKUP fm k of
      NONE => fm |+ (k,v)
    | SOME v0 => fm |+ (k, v0 ∪ v)
End

Definition subfmset_map_def:
  subfmset_map fm1 fm2 ⇔
     ∀k. k ∈ FDOM fm1 ⇒ k ∈ FDOM fm2 ∧ fm1 ' k ⊆ fm2 ' k
End

Theorem subfmset_map_REFL[simp]:
  subfmset_map fm fm
Proof
  simp[subfmset_map_def]
QED

Theorem subfmset_map_TRANS:
  subfmset_map fm1 fm2 ∧ subfmset_map fm2 fm3 ⇒ subfmset_map fm1 fm3
Proof
  simp[subfmset_map_def] >> metis_tac[SUBSET_TRANS]
QED

Theorem subfmset_map_update[simp]:
  subfmset_map fm (fm |+ (k,v)) ⇔ k ∈ FDOM fm ⇒ fm ' k ⊆ v
Proof
  simp[subfmset_map_def, FAPPLY_FUPDATE_THM] >> metis_tac[SUBSET_REFL]
QED

Theorem subfmset_map_augment[simp]:
  subfmset_map fm (augment k v fm)
Proof
  rw[subfmset_map_def, augment_def, FLOOKUP_DEF, FAPPLY_FUPDATE_THM] >>
  rw[] >> fs[]
QED

Definition safelookup_def:
  safelookup fm k =
    case FLOOKUP fm k of NONE => ∅ | SOME v => v
End

Definition follow_sf_def[simp]:
  follow_sf g N [] A = A ∧
  follow_sf g N (TS _ :: rest) A = follow_sf g N rest A ∧
  follow_sf g N (NTS n :: rest) A =
    follow_sf g N rest
              (augment n (firstSetList g rest ∪
                          if nullable g rest then safelookup A N else ∅)
                       A)
End

Definition nonTerminals'_def:
  nonTerminals' g = { n | NTS n ∈ nonTerminals g }
End

Theorem IN_nonTerminals[simp]:
  NTS n ∈ nonTerminals g ⇔ n ∈ nonTerminals' g
Proof
  simp[nonTerminals'_def]
QED

Theorem FINITE_nonTerminals'[simp]:
  FINITE (nonTerminals' (g:(α,β)grammar))
Proof
  qabbrev_tac ‘s:(α,β)symbol set = IMAGE NTS (nonTerminals' g)’ >>
  ‘s ⊆ nonTerminals g’ by simp[SUBSET_DEF, PULL_EXISTS, Abbr‘s’] >>
  ‘FINITE s’ by metis_tac[finite_nts, SUBSET_FINITE] >>
  fs[INJECTIVE_IMAGE_FINITE, Abbr‘s’]
QED

(* smash together all sets in the range of the finite map *)
Definition range_max_def:
  range_max A = BIGUNION { s | ∃nt. FLOOKUP A nt = SOME s}
End
Theorem range_max_FEMPTY[simp]:
  range_max FEMPTY = ∅
Proof
  simp[EXTENSION, range_max_def]
QED

Definition max_map_def:
  max_map A g =
    FUN_FMAP (K (terminals g ∪ range_max A)) (nonTerminals' g)
End

Theorem FDOM_max_map[simp]:
  FDOM (max_map A g) = nonTerminals' g
Proof
  simp[max_map_def]
QED

Definition fmset_union_def:
  fmset_union fm1 fm2 =
    FUN_FMAP (λk. safelookup fm1 k ∪ safelookup fm2 k) (FDOM fm1 ∪ FDOM fm2)
End

Theorem FDOM_fmset_union[simp]:
  FDOM (fmset_union fm1 fm2) = FDOM fm1 ∪ FDOM fm2
Proof
  simp[FUN_FMAP_DEF, fmset_union_def]
QED

Theorem subfmset_map_union[simp]:
  subfmset_map A (fmset_union A B)
Proof
  simp[subfmset_map_def, fmset_union_def, FUN_FMAP_DEF, safelookup_def,
       FLOOKUP_DEF]
QED


Theorem follow_sf_SUBDOM:
  ∀A. subfmset_map A (follow_sf g N sf A)
Proof
  Induct_on ‘sf’ >> simp[] >> Cases >> simp[] >>
  metis_tac[subfmset_map_augment, subfmset_map_TRANS]
QED

Theorem TS_IN_rule_nonterminals[simp]:
  TS t ∈ rule_nonterminals r ⇔ F
Proof
  Cases_on ‘r’ >> simp[rule_nonterminals_def] Induct_on ‘r’ >>

Theorem TS_IN_nonTerminals[simp]:
  TS t ∈ nonTerminals g ⇔ F
Proof
  Cases_on ‘g’ >> simp[nonTerminals_def] >> qx_gen_tac ‘s’ >>
  Cases_on ‘TS t ∈ s’ >> simp[] >> qx_gen_tac ‘rle’ >>
  rename [‘MEM rle rs’] >> Cases_on ‘MEM rle rs’ >> simp[] >> strip_tac >>
  rw[]


Theorem firstSetList_SUBSET_terminals:
  (∀t. MEM t sf ⇒ t ∈ allSyms g) ⇒
  firstSetList g sf ⊆ terminals g
Proof
  simp[firstSetList_def, SUBSET_DEF, PULL_EXISTS] >> Induct_on ‘RTC’ >> rw[]
  >- (fs[DISJ_IMP_THM, FORALL_AND_THM, allSyms_def]

Theorem follow_sf_max:
  ∀A B. (∀t. MEM t sf ⇒ t ∈ allSyms g) ∧
        subfmset_map B (fmset_union A (max_map A g)) ⇒
        subfmset_map (follow_sf g N sf B) (fmset_union A (max_map A g))
Proof
  Induct_on ‘sf’ >> simp[] >> Cases >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt strip_tac >> fs[] >> first_x_assum irule >>
  pop_assum mp_tac >> rename [‘NTS n ∈ allSyms g’] >>
  simp[augment_def, subfmset_map_def, safelookup_def, FLOOKUP_DEF] >>
  strip_tac >> qx_gen_tac ‘k’ >>
  Cases_on ‘n ∈ FDOM B’ >> simp[] >> Cases_on ‘n = k’ >> simp[] >> rw[]
      Cases_on ‘FLOOKUP Acc n’ >> simp[] >> rw[] >> fs[allSyms_def]
      >- (fs[FLOOKUP_DEF, safelookup_def, fmset_union_def] >>
          Cases_on ‘N ∈ FDOM Acc’ >> simp[FUN_FMAP_DEF] >>
          simp[max_map_def, FUN_FMAP_DEF, range_max_def, SUBSET_DEF,
               FLOOKUP_DEF, PULL_EXISTS] >> metis_tac[])
      >- (fs[FLOOKUP_DEF] >> simp[FAPPLY_FUPDATE_THM] >> rw[] >> fs[] >>
          simp[SUBSET_DEF, fmset_union_def, FUN_FMAP_DEF, safelookup_def,
               FLOOKUP_DEF])

 simp[safelookup_def, fmset_union_def]

Definition follow_rule_def:
  follow_rule g (rule N sf) A = follow_sf g N sf A
End

Definition follow_rules_def:
  follow_rules g (r::rs) A = follow_rules g rs (follow_rule g r A)
End

Definition followG_def:
  followG g A0 =
    let A = follow_rules g (rules g) A0
    in
       if A ⊑ A0 then A else followG g A
Termination


  (followG g sn N = followrs g sn N (LENGTH (rules g) - 1)) ∧
   (followrs g sn N 0 =
    followr g sn N 0 (LENGTH (ruleRhs (EL 0 (rules g))))) ∧
   (followrs g sn N i =
      followr g sn N i (LENGTH (ruleRhs (EL i (rules g)))) ∪
      followrs g sn N (i - 1)) ∧
   (followr g sn N i 0 = {}) ∧
   (followr g sn N i rhsLen =
    case (TAKE rhsLen (ruleRhs (EL i (rules g)))) of
      | TS t::rest => followr g sn N i (rhsLen - 1)
      | NTS P :: rest =>
        (if N = P then
           firstSetList g rest ∪
           (if nullableML g [] rest then
              if  N ∈ sn then {}
               else followG g (N::sn) (ruleLhs (EL i (rules g)))
            else {})
       else {}) ∪ followr g sn N i (rhsLen - 1))
End


val easy_def = Define`
  (easy (INL _) = 0) ∧
  (easy (INR (INL (_, _, _, i))) = i) ∧
  (easy (INR (INR (_, _, _, _, i))) = i)
`;

val cg_def = Define`
  (cg (INL _) = 2) ∧
  (cg (INR (INL _)) = 1) ∧
  (cg (INR (INR _)) = 0)
`;


val validSeen = Define
`validSeen (g:(α, β) grammar) (sn:α list) =
{ (NTS e):(α, β) symbol | MEM e sn ∧ NTS e ∈ nonTerminals g }`;

val tricky_def = Define`
  tricky (g,sn) = CARD (nonTerminals g) - CARD (validSeen g sn)
  `;

val gsn_def = Define`
  (gsn (INL (g,sn,_)) = (g,sn)) ∧
  (gsn (INR (INL (g,sn,_))) = (g,sn)) ∧
  (gsn (INR (INR (g,sn,_))) = (g,sn))`



val takeMem = store_thm
("takeMem",
``∀l l' n.(TAKE n l = l') ⇒ (∀e. e ∈ l' ⇒ e ∈ l)``,

Induct_on `l` THEN SRW_TAC [][] THEN1
METIS_TAC [MEM] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
Cases_on `n` THEN FULL_SIMP_TAC (srw_ss()) [TAKE_def] THEN
METIS_TAC [MEM]);

val followSetMem = store_thm
("followSetMem",
``∀u v.RTC (derives g) u v ⇒ (u=[NTS N]) ⇒
(v=(pfx++[NTS N']++[TS ts]++sfx)) ⇒
((TS ts) IN followSet g (NTS N'))``,

HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [] [RTC_RULES] THEN1
 FULL_SIMP_TAC (srw_ss()) [lreseq] THEN
 FULL_SIMP_TAC (srw_ss()) [derives_def, lreseq, followSet] THEN
 Q.EXISTS_TAC `u'` THEN
 SRW_TAC [] []
 THENL[
       FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ruleRhs_def] THEN
       METIS_TAC [],

       METIS_TAC []]);

val (followG,followG_ind) =
tprove (followG_defn,
cheat);

val followSetEq = store_thm ("followSetEq",
``!g sym. s ∈ followG g [] nt <=> s IN followSet g (NTS nt)``,
cheat)

val _ = export_theory ();

(*
tgoal followML_defn

``∀i l. (EL i l = x) ⇒ x ∈ l``



``NTS P ∈ ruleRhs (EL i (rules g)) ⇒ NTS P ∈ nonTerminals g``,

SRW_TAC [][] THEN
Cases_on `EL i (rules g)` THEN
FULL_SIMP_TAC (srw_ss()) [ruleRhs_def] THEN
METIS_TAC [slemma1_4, rgr_r9eq, ]

val (followML_def, followML_ind) = tprove(
  followML_defn,
  WF_REL_TAC `inv_image (measure tricky LEX $< LEX measure easy)
                        (λx. (gsn x, cg x, x))` THEN
  SRW_TAC [][gsn_def, cg_def, easy_def, tricky_def] THEN

`NTS P ∈ ruleRhs (EL i (rules g))` by METIS_TAC [MEM, takeMem] THEN
`NTS P ∈ nonTerminals g` by cheat THENL[
SRW_TAC [][validSeen] THEN
`{e | ((e = P) ∨ e ∈ sn) ∧ NTS e ∈ nonTerminals g} =
{P} ∪ {e | e ∈ sn ∧ NTS e ∈ nonTerminals g}` by (SRW_TAC [][EXTENSION] THEN
                                                 METIS_TAC []) THEN
`{P} ∩ {e | e ∈ sn ∧ NTS e ∈ nonTerminals g} = {}`
by (SRW_TAC [][EXTENSION] THEN METIS_TAC []) THEN
`FINITE {e | e ∈ sn ∧ NTS e ∈ nonTerminals g}` by cheat THEN
`CARD {e | ((e = P) ∨ e ∈ sn) ∧ NTS e ∈ nonTerminals g} + 0 =
CARD {P} + CARD {e | e ∈ sn ∧ NTS e ∈ nonTerminals g}` by
                          METIS_TAC [CARD_UNION,FINITE_SING,
                                     FINITE_LIST_TO_SET,CARD_EMPTY] THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
ONCE_ASM_REWRITE_TAC [] THEN
DECIDE_TAC,

Q_TAC SUFF_TAC `CARD (validSeen g sn) < CARD (nonTerminals g)` THEN1
DECIDE_TAC THEN
`FINITE (nonTerminals g)` by cheat THEN
Q_TAC SUFF_TAC `validSeen g sn ⊂ nonTerminals g` THEN1 METIS_TAC [CARD_PSUBSET]

`FINITE (validSeen g sn)`
``




val followRuleEq1 = store_thm ("followRuleEq1",
``∀g sn sym r.
     s ∈ (followRuleML g sn sym r) ⇒
     (∀rl rh.(r = rule rl rh) ⇒ ∃rh'. (MEM (rule rl rh') (rules g)) ∧
                                     ∃pfx.(rh' = pfx ++ rh))
        ⇒
       s ∈ (followSet g sym)``,

HO_MATCH_MP_TAC followRuleML_ind THEN
SRW_TAC [] [] THEN1
FULL_SIMP_TAC (srw_ss()) [followRuleML] THEN
SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [followRuleML] THEN
Cases_on `~MEM sym sn ∧ sym IN allSyms g` THEN
FULL_SIMP_TAC (srw_ss()) [] THEN
 FULL_SIMP_TAC (srw_ss()) [] THEN

 Cases_on `NTS l ∈ nonTerminalsML g` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
 Cases_on `h=sym` THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][]
 THENL[

  FULL_SIMP_TAC (srw_ss()) [firstSetML_def] THEN
  `s IN (firstSetList g t)`
      by METIS_TAC [firstSet1Eq1, firstSetML_def] THEN
  FULL_SIMP_TAC (srw_ss()) [firstSetList_def, followSet] THEN
  SRW_TAC [][] THEN
  `MEM (pfx++h::t) (MAP (ruleRhs) (rules g))` by (SRW_TAC [] [] THEN
  FULL_SIMP_TAC (srw_ss()) [rgr_r9eq, ruleRhs_def] THEN
  METIS_TAC []) THEN
  Q.EXISTS_TAC `(pfx++h::t)` THEN SRW_TAC [] [] THEN
  `RTC (derives g) (pfx++h::t) (pfx++[h]++[TS fst]++rst)`
      by METIS_TAC [APPEND, APPEND_ASSOC, rtc_derives_same_append_right,
                    rtc_derives_same_append_left] THEN
  METIS_TAC [APPEND, APPEND_ASSOC],

  METIS_TAC [APPEND, APPEND_ASSOC],

  Cases_on `nullableML g [] t` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
  SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`a`] MP_TAC) THEN SRW_TAC [][] THEN
  Cases_on `a` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
  `s ∈ followSet g (NTS l)` by METIS_TAC [APPEND_NIL, APPEND,MEM] THEN
  FULL_SIMP_TAC (srw_ss()) [followSet] THEN
  SRW_TAC [][] THEN
  Q.EXISTS_TAC `s'` THEN SRW_TAC [][] THEN
  `derives g (pfx'++[NTS l]++ [TS ts]++sfx)
 (pfx'++pfx ++ h::t++[TS ts]++sfx)` by
  METIS_TAC [derives_same_append_left, derives_same_append_right,APPEND_ASSOC,
  res1, APPEND] THEN
  `(derives g)^* t []` by METIS_TAC [nullableML, nullableEq, nullable_def] THEN
  `(derives g)^* (pfx' ++ pfx ++ h::t ++ [TS ts] ++ sfx)
 (pfx' ++ pfx ++ [h] ++ [TS ts] ++ sfx)`
  by  METIS_TAC [APPEND, APPEND_ASSOC, rtc_derives_same_append_left,
  rtc_derives_same_append_right,APPEND_NIL] THEN
  METIS_TAC [RTC_RULES, RTC_RTC, APPEND_ASSOC],

  METIS_TAC [APPEND, APPEND_ASSOC]
  ]);



val followSetEq1 = store_thm ("followSetEq1",
``!g sym.s IN (followSetML g sym) ==> s IN (followSet g sym)``,
FULL_SIMP_TAC (srw_ss()) [followSetML] THEN SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
SRW_TAC [][] THEN
Cases_on `y` THEN
METIS_TAC [followRuleEq1, APPEND, APPEND_NIL]);




val ntderive'_def = Define`
  (ntderive' g tok [] = F) ∧
  (ntderive' g tok [N] =
     ∃pfx sfx rhs.
        MEM (rule N rhs) (rules g) ∧
        (rhs = pfx ++ [tok] ++ sfx) ∧
        nullable g pfx) ∧
  (ntderive' g tok (N1 :: N2 :: Ns) =
     ∃pfx sfx rhs.
        MEM (rule N1 rhs) (rules g) ∧
        (rhs = pfx ++ [NTS N2] ++ sfx) ∧
        nullable g pfx ∧
        ntderive' g tok (N2 :: Ns))
`;

val _ = export_rewrites ["ntderive'_def"];

val ntderive'_APPEND = store_thm(
  "ntderive'_APPEND",
  ``∀l1 l2. ntderive' g tok (l1 ++ l2) ∧ ¬(l2 = []) ⇒
            ntderive' g tok l2``,
  Induct THEN1 SRW_TAC [][] THEN
  Cases_on `l1` THEN SRW_TAC [][] THENL [
    Cases_on `l2` THEN FULL_SIMP_TAC (srw_ss()) [],
    METIS_TAC [APPEND]
  ]);

val ntderive'_list_exists = prove(
  ``∀sf1 sf2.
       (derives g)^* sf1 sf2 ⇒
       ∀tok rest. (sf2 = tok :: rest) ∧
                  (∀pfx sfx. nullable g pfx ⇒
                             ¬(sf1 = pfx ++ [tok] ++ sfx))
                 ⇒
                  ∃nlist pfx sfx.
                     (sf1 = pfx ++ [NTS (HD nlist)] ++ sfx) ∧
                     nullable g pfx ∧
                     ntderive' g tok nlist ∧
                     ALL_DISTINCT nlist``,
  HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN1
    (POP_ASSUM (Q.SPEC_THEN `[]` MP_TAC) THEN
                SRW_TAC [][] THEN
                FULL_SIMP_TAC (srw_ss()) [nullable_def]) THEN
  `∃N rhs pfx sfx.
      MEM (rule N rhs) (rules g) ∧
      (sf1 = pfx ++ [NTS N] ++ sfx) ∧
      (sf1' = pfx ++ rhs ++ sfx)`
     by METIS_TAC [derives_def] THEN
  SRW_TAC [][] THEN
  Cases_on `∀p s. nullable g p ⇒
                  ¬(pfx ++ rhs ++ sfx = p ++ [tok] ++ s)`
  THENL [
    FULL_SIMP_TAC (srw_ss()) [] THEN
    REPEAT (Q.PAT_ASSUM `∀x. P x` (K ALL_TAC)) THEN
    RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [split_killer]) THEN
    FULL_SIMP_TAC (srw_ss()) [] THENL [
      SRW_TAC [][] THEN METIS_TAC [APPEND_ASSOC],
      SRW_TAC [][] THEN
      Cases_on `MEM N nlist` THENL [
        `∃n0 nsfx. (nlist = n0 ++ [N] ++ nsfx) ∧
                   ¬ MEM N nsfx`
           by METIS_TAC [isolate_last] THEN
        SRW_TAC [][] THEN
        MAP_EVERY Q.EXISTS_TAC
                  [`N :: nsfx`, `pfx`, `sfx`] THEN
        SRW_TAC [][] THENL [
          FULL_SIMP_TAC (srw_ss()) [nullable_APPEND],
          METIS_TAC [ntderive'_APPEND, APPEND_ASSOC, APPEND,
                     NOT_CONS_NIL],
          METIS_TAC [ALL_DISTINCT_APPEND]
        ],

        MAP_EVERY Q.EXISTS_TAC
                  [`N :: nlist`, `pfx`, `sfx`] THEN
        SRW_TAC [][] THENL [
          FULL_SIMP_TAC (srw_ss()) [nullable_APPEND],
          Cases_on `nlist` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
          METIS_TAC [nullable_APPEND]
        ]
      ],

      SRW_TAC [][] THEN
      MAP_EVERY Q.EXISTS_TAC
                [`nlist`, `pfx ++ [NTS N] ++ y1`, `sfx'`] THEN
      SRW_TAC [][] THEN
      METIS_TAC [nullable_APPEND, nullable_def, res1,
                 RTC_RULES]
    ],

    FULL_SIMP_TAC (srw_ss()) [] THEN
    POP_ASSUM (MP_TAC o SIMP_RULE (srw_ss()) [split_killer]) THEN
    STRIP_TAC THEN SRW_TAC [][] THENL [
      METIS_TAC [APPEND_ASSOC],
      MAP_EVERY Q.EXISTS_TAC [`[N]`, `pfx`, `sfx`] THEN
      SRW_TAC [][] THEN METIS_TAC [nullable_APPEND],
      `nullable g [NTS N]`
         by METIS_TAC [nullable_APPEND, RTC_RULES, res1,
                       nullable_def] THEN
      FULL_SIMP_TAC (srw_ss()) [nullable_APPEND] THEN
      FIRST_X_ASSUM (Q.SPECL_THEN [`pfx ++ [NTS N] ++ y1`, `s`]
                                  MP_TAC) THEN
      SRW_TAC [][nullable_APPEND]
    ]
  ]);

val lemma' =  SIMP_RULE (srw_ss() ++ boolSimps.DNF_ss) []
                       ntderive'_list_exists
*)


(*
``s ∈ followSet g sym ⇒ s ∈ followSetML g sym``,

SRW_TAC [][followSet] THEN
FULL_SIMP_TAC (srw_ss()) [MEM_MAP] THEN
Cases_on `y` THEN FULL_SIMP_TAC  (srw_ss()) [] THEN
SRW_TAC [][]

``TS ts ∈ followRuleML g [] sym (rule s l)``

``∀x y. (derives g)^* x y ⇒
∀pfx sfx m. (x = pfx++m++sfx) ⇒ MEM m (MAP ruleRhs (rules g)) ⇒
∀p s sym ts. (y = pfx ++ p ++ [sym] ++ [TS ts] ++ s ++ sfx) ⇒
TS ts ∈ followSetML g sym``


HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN SRW_TAC [][] THEN1
`m = p ++ [sym]++[TS ts]++s`by METIS_TAC [APPEND_11, APPEND_ASSOC] THEN
SRW_TAC [][] THEN
cheat


FULL_SIMP_TAC (srw_ss()) [derives_def] THEN
SRW_TAC [][] THEN
`MEM rhs (MAP ruleRhs (rules g))` by cheat THEN
FIRST_X_ASSUM (Q.SPECL_THEN [`s1`,`s2`,`rhs`] MP_TAC) THEN SRW_TAC [][] THEN


``∀pfx m sfx dl y.
derives g ⊢ dl ◁ (pfx ++ m ++ sfx) → y ⇒
∀p s sym ts.(y = pfx ++ p ++ [sym] ++ [TS ts] ++ s ++ sfx)  ⇒
(∀e. MEM e dl ⇒ ∃m'.(e= pfx ++ m' ++ sfx)) ⇒
(∀e1 e2. ∃pd sd. (dl = pd ++ [e1;e2] ++ sd) ⇒ LENGTH e2 ≥ LENGTH e1)
⇒
TS ts ∈ followSetML g sym``

Induct_on `dl` THEN SRW_TAC [][] THEN1
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN

Cases_on `dl` THEN FULL_SIMP_TAC (srw_ss()) [] THEN1

SRW_TAC [][] THEN
FULL_SIMP_TAC (srw_ss()) [listderiv_def] THEN
SRW_TAC [][] THEN
cheat



IMP_RES_TAC


``∀g sn sf. ts ∈ firstSet1 g sn sf ⇒ ts ∈ followSet ``
*)

val mlDir = ref ("./theoryML/");



(*
val _ =
 let open EmitML
 in emitML (!mlDir)
   ("followSet",
    OPEN ["list", "option", "regexp", "listLemmas", "grammarDef", "whileLemmas", "set","num", "parseTree", "firstSet"]
    :: MLSIG "type num = numML.num"
    :: MLSIG "type symbol = regexpML.symbol"
    :: MLSIG "type 'a set = 'a setML.set"
    :: MLSIG "type rule = grammarDefML.rule"
    :: MLSIG "type grammar = grammarDefML.grammar"
    :: MLSIG "type ptree = parseTreeML.ptree"
    :: DATATYPE `item = item of string => symbol list # symbol list`
    :: DEFN firstSet1
    :: DEFN followRuleML
    :: DEFN followSetML
    :: [])
 end;
*)

*)

