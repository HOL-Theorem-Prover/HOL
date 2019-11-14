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
Definition nullableML_def:
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
Termination
  WF_REL_TAC `measure ptree_size` >> Induct_on `subs` >> simp[] >> fs[] >>
  rpt strip_tac >> res_tac >> asimp[]
End

Definition ptree_rptfree_def:
  ptree_rptfree (Lf _) = T ∧
  ptree_rptfree (Nd (N,_) subs) =
    ∀s. MEM s subs ⇒ ptree_rptfree s ∧ N ∉ ptree_NTs s
Termination
  WF_REL_TAC `measure ptree_size` >> Induct_on `subs` >> simp[] >> fs[] >>
  rpt strip_tac >> res_tac >> asimp[]
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

Definition firstSetML_def:
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

(* there is a "path" of non-terminals were N₁ -> N₂ if N₂ appears in a rhs for N₁,
   and in the last one, there is a rhs where the given tok can appear first *)
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

Triviality heads_give_first:
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

Triviality MEM_last_strip:
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


val _ = export_theory()
