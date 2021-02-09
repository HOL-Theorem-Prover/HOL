open HolKernel Parse boolLib bossLib

open listTheory rich_listTheory
open grammarTheory
open pred_setTheory
open finite_mapTheory

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
      ∃r. fIN r (G.rules ' n) ∧ nullable G r
Proof
  simp[nullable_def] >> REVERSE eq_tac
  >- (strip_tac >> match_mp_tac RTC_R_I >> simp[derive_def] >>
      qexists_tac `r ++ rest` >> REVERSE conj_tac
      >- metis_tac[derives_paste_horizontally, listTheory.APPEND] >>
      qexists_tac `[]` >> simp[]) >>
  ‘NT n :: rest = [NT n] ++ rest’ by simp[] >> pop_assum SUBST1_TAC >>
  simp[derives_split_horizontally] >> strip_tac >>
  Q.UNDISCH_THEN ‘derives G [NT n] []’
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

val _ = SIMP_CONV (srw_ss())[
  GSPEC_INTER, combinTheory.o_ABS_R, combinTheory.S_ABS_R, combinTheory.S_ABS_L,
  pairTheory.o_UNCURRY_R, pairTheory.S_UNCURRY_R
] ``{ n + m | n > 10 ∧ m < 3 } ∩ Q``

(* nullableML is an "executable" version of nullable that examines the grammar
   to determine nullability. I put the "executable" in quotes because of the
   scary looking set comprehension below.  This will work fine if the
   sets of rules for non-terminals are always finite. *)
Definition nullableML_def:
  nullableML seen [] = T ∧
  nullableML seen (TOK t :: _) = F ∧
  nullableML seen (NT n :: rest) =
      if n ∈ FDOM G.rules ∧ n ∉ seen then
        if fFILTER (λr. nullableML (n INSERT seen) r) (G.rules ' n) = fEMPTY
        then F
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
  qpat_x_assum `SS ≠ fEMPTY` mp_tac >>
  simp[finite_setTheory.EXTENSION] >> metis_tac[]
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
  strip_tac >> simp[finite_setTheory.EXTENSION] >>
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
    by (qpat_x_assum `fIN (MAP ptree_head subs) (G.rules ' q)` (K ALL_TAC) >>
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
        BIGUNION (IMAGE (firstSet G) (toSet (G.rules ' N))) ∪
        (if nullable G [NT N] then firstSet G rest
         else {})
      else {}
Proof
  reverse (Cases_on `N ∈ FDOM G.rules`)
  >- simp[firstSet_def, derives_leading_nonNT] >>
  simp[Once EXTENSION] >> qx_gen_tac `t` >> reverse eq_tac
  >- (dsimp[] >> rw[] >> fs[firstSet_def]
      >- (asm_match `rhs ∈ toSet (G.rules ' N)` >>
          asm_match `derives G rhs (TOK t :: rest0)` >>
          qexists_tac`rest0 ++ rest` >>
          match_mp_tac RTC_R_I >>
          qexists_tac `rhs ++ rest` >> simp[grammarTheory.derive_def] >>
          metis_tac [listTheory.APPEND, APPEND_ASSOC,
                     grammarTheory.derives_paste_horizontally,
                     relationTheory.RTC_REFL, finite_setTheory.fIN_IN]) >>
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
  simp[] >> metis_tac[finite_setTheory.fIN_IN]
QED

Definition firstSetML_def:
  firstSetML seen [] = {} ∧
  firstSetML seen (TOK t :: _) = {t} ∧
  firstSetML seen (NT n :: rest) =
    if n ∈ FDOM G.rules then
      (if n ∉ seen then
        BIGUNION (IMAGE (firstSetML (n INSERT seen))
                        (toSet (G.rules ' n)))
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
    ∃p s. fIN (p ++ [TOK tok] ++ s) (G.rules ' N) ∧ nullable G p) ∧
  (nts_derive G (N1::N2::NS) tok ⇔
    N1 ∈ FDOM G.rules ∧
    ∃p s. fIN (p ++ [NT N2] ++ s) (G.rules ' N1) ∧ nullable G p ∧
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
      qexists_tac `p ++ [TOK tok] ++ s` >>
      simp[GSYM finite_setTheory.fIN_IN] >>
      REWRITE_TAC [GSYM APPEND_ASSOC] >>
      match_mp_tac firstSetML_nullable_prefix >>
      simp[firstSetML_def]) >>
  simp[EXTENSION] >> rpt strip_tac >>
  asm_match `fIN (p ++ [NT N'] ++ s) (G.rules ' N)` >>
  simp[firstSetML_def] >> `N ∉ sn` by metis_tac[] >>
  dsimp[] >> qexists_tac `p ++ [NT N'] ++ s` >>
  simp[GSYM finite_setTheory.fIN_IN] >>
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
      >- (asm_match `rhs ∈ toSet (G.rules ' N)` >>
          map_every qexists_tac [`[]`, `NT N`, `sf`] >> simp[] >>
          dsimp[firstSet_NT] >> metis_tac[])
      >- (asm_match `nullableNT G N` >> asm_match `tk ∈ firstSet G [e]` >>
          asm_match `nullable G p` >>
          map_every qexists_tac [`NT N::p`, `e`] >> simp[] >>
          simp[Once nullable_by_singletons, DISJ_IMP_THM, FORALL_AND_THM] >>
          metis_tac[nullable_by_singletons]) >>
      asm_match `tk ∈ firstSet G rhs` >>
      asm_match `rhs ∈ toSet (G.rules ' N)` >>
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

Theorem RHSes_in_allSyms:
  N ∈ FDOM g.rules ∧ rhs ∈ᶠ g.rules ' N ∧ MEM s rhs ⇒
  s ∈ allSyms g
Proof
  strip_tac >> Cases_on ‘s’ >>
  simp[allSyms_def,  terminals_def, nonTerminals_def] >> metis_tac[]
QED

Theorem firstSet_SUBSET_terminals:
  (∀t. MEM t sf ⇒ t ∈ allSyms g) ⇒ firstSet g sf ⊆ terminals g
Proof
  simp[firstSet_def, SUBSET_DEF, PULL_EXISTS] >> Induct_on ‘RTC’ >> rw[]
  >- fs[DISJ_IMP_THM, FORALL_AND_THM, allSyms_def] >>
  first_x_assum irule >> fs[derive_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  metis_tac[RHSes_in_allSyms]
QED

Theorem firstSet_SUBSET:
  firstSet g sf ⊆ terminals g ∪ { t | MEM (TOK t) sf }
Proof
  simp[firstSet_def, SUBSET_DEF, PULL_EXISTS] >> Induct_on ‘RTC’ >> rw[] >>
  simp[] >>
  fs[derive_def, DISJ_IMP_THM, FORALL_AND_THM] >> rfs[] >>
  drule_all RHSes_in_allSyms >> simp[allSyms_def]
QED

Theorem FINITE_firstSet[simp]:
  FINITE (firstSet g sf)
Proof
  irule SUBSET_FINITE_I >> qexists_tac ‘terminals g ∪ { t | MEM (TOK t) sf }’ >>
  simp[firstSet_SUBSET] >>
  ‘{ t | MEM (TOK t) sf } =
   BIGUNION (IMAGE (λs. case s of TOK t => {t} | NT _ => ∅) (set sf))’
    by (simp[Once EXTENSION, PULL_EXISTS] >> rw[EQ_IMP_THM]
        >- (rename [‘MEM (TOK x) sf’] >> qexists_tac ‘TOK x’ >> simp[]) >>
        rename [‘symbol_CASE sym’] >> Cases_on ‘sym’ >> fs[]) >>
  simp[PULL_EXISTS] >> Cases >> simp[]
QED

(* ----------------------------------------------------------------------
    follow sets
   ---------------------------------------------------------------------- *)

Definition followSet_def:
  followSet (G:(α,β) grammar) (sym:(α,β) symbol) =
    { tk | ∃n sf pfx sfx.
             sf ∈ᶠ G.rules ' n ∧ n ∈ FDOM G.rules ∧
             derives G sf (pfx++[sym]++[TOK tk]++sfx) }
End

Inductive follow:
  (∀p N s M a.
     p ++ [NT N] ++ s ∈ᶠ G.rules ' M ∧ M ∈ FDOM G.rules ∧ a ∈ firstSet G s
    ⇒
     follow G N a) ∧
  (∀p N s M a.
     p ++ [NT N] ++ s ∈ᶠ G.rules ' M ∧ M ∈ FDOM G.rules ∧ nullable G s ∧
     follow G M a
    ⇒
     follow G N a)
End

Theorem follow_followSet:
  ∀N x. follow G N x ⇒ x ∈ followSet G (NT N)
Proof
  Induct_on ‘follow’ >> simp[followSet_def, PULL_EXISTS] >> rw[]
  >- (fs[firstSet_def] >> goal_assum drule >>
      rename [‘p ++ [NT N] ++ s’, ‘derives _ s (TOK a :: rest)’] >>
      qexistsl_tac [‘p’,‘rest’] >>
      ‘derives G (p ++ [NT N]) (p ++ [NT N])’ by simp[] >>
      dxrule_all derives_paste_horizontally >>
      ASM_REWRITE_TAC[GSYM APPEND_ASSOC, APPEND]) >>
  rename [‘derives _ sf (p0 ++ [NT N1] ++ [TOK a] ++ s0)’,
          ‘sf ∈ᶠ G.rules ' N0’, ‘p1 ++ [NT N2] ++ s1 ∈ᶠ G.rules ' N1’] >>
  qexistsl_tac [‘N0’, ‘sf’, ‘p0 ++ p1’, ‘s0’] >> simp[] >>
  ONCE_REWRITE_TAC [relationTheory.RTC_CASES_RTC_TWICE] >>
  goal_assum drule >> irule derives_common_suffix >>
  irule derives_common_suffix >> REWRITE_TAC [GSYM APPEND_ASSOC] >>
  irule derives_common_prefix >>
  irule (relationTheory.RTC_RULES |> SPEC_ALL |> CONJUNCT2) >>
  simp[derive_def] >> goal_assum drule >>
  REWRITE_TAC [GSYM APPEND_ASSOC] >> irule derives_common_prefix >>
  metis_tac[APPEND_NIL, nullable_def, derives_common_prefix]
QED

Theorem derives_starting_NIL[simp]:
  ∀x. derives G [] x ⇔ x = []
Proof
  simp[EQ_IMP_THM] >> Induct_on ‘RTC’ >> rw[derive_def] >> fs[]
QED

Theorem derive_hits_NT_right:
  derive G sf0 (p ++ [NT N]) ⇒ ∃p0 N0. sf0 = p0 ++ [NT N0]
Proof
  dsimp[derive_def, APPEND_EQ_APPEND, APPEND_EQ_CONS]
QED

Theorem derives_hits_NT_right:
  derives G sf0 (p ++ [NT N]) ⇒ ∃p0 N0. sf0 = p0 ++ [NT N0]
Proof
  Induct_on ‘RTC’ >> rw[] >> metis_tac[derive_hits_NT_right]
QED

Theorem follow1 = follow_rules |> SPEC_ALL |> CONJUNCT1
Theorem follow2 = follow_rules |> SPEC_ALL |> CONJUNCT2

val IRULE = goal_assum o resolve_then Any mp_tac

Theorem derive_2syms_cases:
  derive G sf0 (p ++ [sym1; sym2] ++ s) ⇔
  (∃N0 rhs p1 p2.
     N0 ∈ FDOM G.rules ∧ rhs ∈ᶠ G.rules ' N0 ∧
     sf0 = p1 ++ [NT N0] ++ p2 ++ [sym1;sym2] ++ s ∧
     p = p1 ++ rhs ++ p2) ∨
  (∃N0 rhs s1 s2.
     N0 ∈ FDOM G.rules ∧ rhs ∈ᶠ G.rules ' N0 ∧
     sf0 = p ++ [sym1;sym2] ++ s1 ++ [NT N0] ++ s2 ∧
     s = s1 ++ rhs ++ s2) ∨
  (∃N0 rhs p1.
     N0 ∈ FDOM G.rules ∧ rhs ++ [sym1] ∈ᶠ G.rules ' N0 ∧
     sf0 = p1 ++ [NT N0;sym2] ++ s ∧ p = p1 ++ rhs) ∨
  (∃N0 rhs s1.
     N0 ∈ FDOM G.rules ∧ sym2 :: rhs ∈ᶠ G.rules ' N0 ∧
     sf0 = p ++ [sym1;NT N0] ++ s1 ∧ s = rhs ++ s1) ∨
  (∃N0 p0 p1 s0 s1.
     N0 ∈ FDOM G.rules ∧ p1 ++ [sym1; sym2] ++ s1 ∈ᶠ G.rules ' N0 ∧
     sf0 = p0 ++ [NT N0] ++ s0 ∧ p = p0 ++ p1 ∧ s = s1 ++ s0) ∨
  (∃N0.
     N0 ∈ FDOM G.rules ∧ [] ∈ᶠ G.rules ' N0 ∧
     sf0 = p ++ [sym1; NT N0; sym2] ++ s)

Proof
  dsimp[derive_def, APPEND_EQ_APPEND, APPEND_EQ_CONS] >> eq_tac >> rw[] >>
  csimp[] >>
  simp[APPEND_EQ_APPEND, APPEND_EQ_CONS] >> dsimp[]
QED

Theorem valid_ptree_derives_ptree_fringe:
  ∀G pt. valid_ptree G pt ⇒ derives G [ptree_head pt] (ptree_fringe pt)
Proof
  ho_match_mp_tac valid_ptree_ind >> simp[pairTheory.FORALL_PROD] >> rw[] >>
  irule (relationTheory.RTC_RULES |> SPEC_ALL |> CONJUNCT2) >>
  qexists_tac ‘MAP ptree_head children’ >> conj_tac
  >- simp[derive_def] >>
  qpat_x_assum ‘MAP _ _ ∈ᶠ _’ (K ALL_TAC) >> fs[] >>
  Induct_on ‘children’ >> simp[DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
  fs[] >> dxrule_all derives_paste_horizontally >> simp[]
QED

Theorem derives_ptree_E:
  ∀sf0 sf. derives G sf0 sf ⇒
           ∃ptl. (∀pt. MEM pt ptl ⇒ valid_ptree G pt) ∧
                 MAP ptree_head ptl = sf0 ∧ FLAT (MAP ptree_fringe ptl) = sf
Proof
  Induct_on ‘RTC’ >> simp[] >> conj_tac
  >- (qx_gen_tac ‘sf0’ >> qexists_tac‘MAP (λsym. Lf (sym, ARB)) sf0’ >>
      simp[MAP_MAP_o, MEM_MAP, combinTheory.o_ABS_R, PULL_EXISTS] >>
      simp[LIST_EQ_REWRITE, LENGTH_FLAT, MAP_MAP_o,
           combinTheory.o_ABS_R] >> csimp[] >>
      conj_tac >- (Induct_on ‘sf0’ >> simp[]) >>
      Induct_on ‘sf0’ >>
      simp[arithmeticTheory.LT_SUC, DISJ_IMP_THM, PULL_EXISTS]) >>
  simp[derive_def, PULL_EXISTS]>> rw[] >>
  fs[MAP_EQ_APPEND, PULL_EXISTS] >> rw[] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  rename [‘FLAT (MAP _ pxts) ++ FLAT (MAP _ midts) ++ FLAT (MAP _ sxts)’,
         ‘MAP ptree_head midts ∈ᶠ _’ ] >>
  qabbrev_tac ‘midpt = Nd (sym,ARB) midts’ >>
  ‘valid_ptree G midpt’ by simp[Abbr‘midpt’] >>
  first_assum IRULE >> simp[Abbr‘midpt’]>> metis_tac[]
QED

Theorem derives_ptree_IFF:
  ∀sf0 sf. derives G sf0 sf ⇔
           ∃ptl. (∀pt. MEM pt ptl ⇒ valid_ptree G pt) ∧
                 MAP ptree_head ptl = sf0 ∧ FLAT (MAP ptree_fringe ptl) = sf
Proof
  simp[EQ_IMP_THM, FORALL_AND_THM] >> conj_tac >- metis_tac[derives_ptree_E] >>
  simp[PULL_EXISTS] >> Induct >> simp[DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
  fs[] >>
  ‘derives G [ptree_head h] (ptree_fringe h)’
    by metis_tac[valid_ptree_derives_ptree_fringe] >>
  dxrule_all derives_paste_horizontally >> simp[]
QED


Theorem followSet_alt:
  followSet G sym = { tk |
                      ∃pt px sx. valid_ptree G pt ∧
                                 ptree_fringe pt = px ++ [sym; TOK tk] ++ sx }
Proof
  simp[followSet_def, EXTENSION, EQ_IMP_THM, PULL_EXISTS, FORALL_AND_THM] >>
  rw[]
  >- (drule_then (qx_choose_then ‘ptl’ strip_assume_tac) derives_ptree_E >>
      qexists_tac ‘Nd (n,ARB) ptl’ >> simp[] >> metis_tac[]) >>
  drule valid_ptree_derives_ptree_fringe >> simp[] >>
  simp[SimpL “$==>”, Once relationTheory.RTC_CASES1] >> simp[APPEND_EQ_CONS] >>
  simp[derive_def, PULL_EXISTS] >> simp[APPEND_EQ_CONS, PULL_EXISTS] >>
  simp[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC", Excl "LIST_EQ_SIMP_CONV"] >>
  metis_tac[]
QED

Theorem FLAT_EQ_CONS:
  ∀l h t.
    FLAT l = h::t ⇔ ∃px e sx ep. l = px ++ [e] ++ sx ∧
                                 FLAT px = [] ∧ e = h::ep ∧
                                 t = ep ++ FLAT sx
Proof
  Induct >> simp[APPEND_EQ_CONS] >> dsimp[] >> rpt gen_tac >>
  rename [‘h = []’, ‘h = eh :: _’] >> Cases_on ‘h’ >> simp[] >> metis_tac[]
QED

Theorem FLAT_EQ_SNOC:
  ∀l h p.
    FLAT l = p ++ [h] ⇔ ∃px e sx ep. l = px ++ [e] ++ sx ∧
                                     FLAT sx = [] ∧ e = ep ++ [h] ∧
                                     p = FLAT px ++ ep
Proof
  Induct using SNOC_INDUCT >>
  simp[APPEND_EQ_CONS, SNOC_APPEND, APPEND_EQ_APPEND] >> dsimp[] >>
  rpt gen_tac >> rename [‘l0 = [e]’, ‘l0 = []’] >>
  Cases_on ‘l0’ using SNOC_CASES >> simp[]
  >- (eq_tac >> rw[] >> metis_tac[APPEND_NIL, FLAT]) >>
  eq_tac >> rw[] >> simp[]
QED

Theorem ptree_cases:
  ∀pt. (∃s l. pt = Lf (s,l)) ∨ (∃s l ts. pt = Nd (s,l) ts)
Proof
  Cases >> simp[] >> metis_tac[pairTheory.pair_CASES]
QED

Theorem rightNTs_follow2:
  ∀G pt pfx N0 N a.
    valid_ptree G pt ∧ ptree_fringe pt = pfx ++ [NT N] ∧ ptree_head pt = NT N0 ∧
    follow G N0 a ⇒ follow G N a
Proof
  ho_match_mp_tac valid_ptree_ind >> simp[pairTheory.FORALL_PROD] >> rw[] >>
  fs[FLAT_EQ_SNOC] >> rw[] >> fs[MAP_EQ_APPEND] >> rw[] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  rename [‘syms ++ [NT N] = ptree_fringe midpt’] >>
  qpat_x_assum ‘_ ++ _ = ptree_fringe midpt’ (assume_tac o SYM) >> fs[] >>
  ‘∃Nsym. ptree_head midpt = NT Nsym’
    by (Cases_on ‘midpt’ using ptree_cases >> fs[]) >>
  fs[] >> ‘follow G Nsym a’ suffices_by simp[] >>
  irule follow2 >> first_assum IRULE >> simp[] >> first_assum IRULE >>
  simp[nullable_def] >> simp[derives_ptree_IFF] >> metis_tac[]
QED

Theorem ptrees_derive_2syms:
  ∀pts px sym1 sym2 sx.
    FLAT (MAP ptree_fringe pts) = px ++ [sym1; sym2] ++ sx ⇒
    (∃pt px0 px1 sx0 sx1.
       MEM pt pts ∧ ptree_fringe pt = px0 ++ [sym1; sym2] ++ sx0 ∧
       px = px1 ++ px0 ∧ sx = sx0 ++ sx1) ∨
    (∃tpx tsx pt1 pt2 tmids px0 px1 sx0 sx1.
       pts = tpx ++ [pt1] ++ tmids ++ [pt2] ++ tsx ∧
       ptree_fringe pt1 = px0 ++ [sym1] ∧ ptree_fringe pt2 = sym2 :: sx0 ∧
       FLAT (MAP ptree_fringe tmids) = [] ∧
       px = px1 ++ px0 ∧ sx = sx0 ++ sx1 ∧ FLAT (MAP ptree_fringe tpx) = px1 ∧
       FLAT (MAP ptree_fringe tsx) = sx1)
Proof
  Induct_on ‘pts’ >> simp[] >> rpt gen_tac >>
  simp[APPEND_EQ_APPEND, APPEND_EQ_CONS, PULL_EXISTS] >> dsimp[] >> rw[]
  >- metis_tac[APPEND, APPEND_NIL]
  >- (first_x_assum drule >> strip_tac >> rw[] >> metis_tac[APPEND_ASSOC])
  >- (first_x_assum $ qspec_then ‘[]’ mp_tac >> simp[] >> rw[] >>
      metis_tac[APPEND, APPEND_NIL])
  >- (disj2_tac >> pop_assum mp_tac >>
      simp[FLAT_EQ_CONS, MAP_EQ_APPEND, PULL_EXISTS] >> metis_tac[]) >>
  metis_tac[APPEND, APPEND_NIL]
QED

(* needs "right" induction principle for RTC *)
Theorem followSet_follow0:
  ∀G pt a N px sx.
     valid_ptree G pt ∧ ptree_fringe pt = px ++ [NT N; TOK a] ++ sx ⇒
     follow G N a
Proof
  ho_match_mp_tac valid_ptree_ind >>
  simp[pairTheory.FORALL_PROD, APPEND_EQ_CONS] >> rw[] >>
  drule ptrees_derive_2syms >> strip_tac >- metis_tac[] >>
  rw[] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >> irule rightNTs_follow2 >>
  first_assum IRULE >> simp[] >>
  ‘∃N0. ptree_head pt1 = NT N0’ by (Cases_on ‘pt1’ using ptree_cases >> fs[]) >>
  fs[] >> irule follow1 >> first_assum IRULE >>
  rename [‘MAP ptree_head tpx ++ [NT N0] ++ MAP ptree_head tmids ++
           [ptree_head pt2] ++ MAP ptree_head tsx ∈ᶠ _’] >>
  qexists_tac ‘MAP ptree_head tmids ++ [ptree_head pt2] ++ MAP ptree_head tsx’>>
  simp[] >> first_assum IRULE >> simp[firstSet_def] >>
  simp[derives_ptree_IFF] >> CONV_TAC SWAP_EXISTS_CONV >>
  qexists_tac ‘tmids ++ [pt2] ++ tsx’ >> simp[] >> metis_tac[]
QED


Theorem followSet_follow:
  ∀a N. a ∈ followSet G (NT N) ⇒ follow G N a
Proof
  simp[followSet_alt, PULL_EXISTS] >> metis_tac[followSet_follow0]
QED

Definition augment_def:
  augment k v fm =
  if v = ∅ᶠ then fm
  else
    case FLOOKUP fm k of
      NONE => fm |+ (k,v)
    | SOME v0 => fm |+ (k, v0 ∪ᶠ v)
End
Theorem fUNION_COMM[local] = finite_setTheory.fUNION_COMM
Theorem fUNION_ASSOC[local] = finite_setTheory.fUNION_ASSOC

Theorem augment_collapse[simp]:
  augment k v1 (augment k v2 fm) = augment k (v1 ∪ᶠ v2) fm
Proof
  rw[augment_def, FLOOKUP_DEF] >> fs[] >>
  metis_tac[fUNION_COMM, fUNION_ASSOC]
QED

Theorem augment_update:
  augment k1 v1 (fm |+ (k2, v2)) =
  if k1 = k2 then fm |+ (k1, v1 ∪ᶠ v2)
  else augment k1 v1 fm |+ (k2,v2)
Proof
  simp[augment_def, FLOOKUP_UPDATE] >>
  Cases_on ‘k1 = k2’ >> simp[AC fUNION_ASSOC fUNION_COMM] >> rw[] >>
  Cases_on ‘FLOOKUP fm k1’ >>
  simp[AC fUNION_ASSOC fUNION_COMM, FUPDATE_COMMUTES]
QED

Theorem augment_commutes:
  ∀fm. augment k1 v1 (augment k2 v2 fm) = augment k2 v2 (augment k1 v1 fm)
Proof
  Cases_on ‘k1 = k2’ >> simp[AC fUNION_ASSOC fUNION_COMM] >>
  Induct >> conj_tac
  >- (csimp[augment_def, FLOOKUP_DEF, FUPDATE_COMMUTES] >> rw[] >> fs[] >>
      simp[FUPDATE_COMMUTES]) >>
  simp[augment_update] >> rw[] >> rw[augment_update] >> metis_tac[]
QED

Definition safelookup_def:
  safelookup fm k =
    case FLOOKUP fm k of NONE => ∅ᶠ | SOME v => v
End

Definition subfmset_map_def:
  subfmset_map fm1 fm2 ⇔
     ∀k. k ∈ FDOM fm1 ⇒ fm1 ' k ⊆ᶠ safelookup fm2 k
End

Theorem subfmset_map_REFL[simp]:
  subfmset_map fm fm
Proof
  simp[subfmset_map_def, finite_setTheory.fSUBSET_def, safelookup_def,
       FLOOKUP_DEF]
QED

Theorem fSUBSET_EMPTY[simp]:
  fSUBSET fEMPTY fs /\ (fSUBSET fs fEMPTY <=> fs = fEMPTY)
Proof
  simp[finite_setTheory.fSUBSET_def, finite_setTheory.EXTENSION]
QED

Theorem fSUBSET_TRANS:
  fSUBSET fs1 fs2 /\ fSUBSET fs2 fs3 ==> fSUBSET fs1 fs3
Proof
  simp[finite_setTheory.fSUBSET_def] >> metis_tac[]
QED

Theorem subfmset_map_TRANS:
  subfmset_map fm1 fm2 ∧ subfmset_map fm2 fm3 ⇒ subfmset_map fm1 fm3
Proof
  simp[subfmset_map_def, safelookup_def, FLOOKUP_DEF] >>
  rw[] >> rpt (first_x_assum (qspec_then ‘k’ mp_tac)) >> rw[] >> fs[] >>
  metis_tac[fSUBSET_TRANS]
QED

Theorem subfmset_map_update[simp]:
  subfmset_map fm (fm |+ (k,v)) ⇔ k ∈ FDOM fm ⇒ fm ' k ⊆ᶠ v
Proof
  simp[subfmset_map_def, FAPPLY_FUPDATE_THM, safelookup_def, FLOOKUP_DEF] >>
  metis_tac[finite_setTheory.fSUBSET_def]
QED

Theorem subfmset_map_augment[simp]:
  subfmset_map fm (augment k v fm)
Proof
  rw[subfmset_map_def, augment_def, FLOOKUP_DEF, FAPPLY_FUPDATE_THM,
     safelookup_def] >>
  rw[] >> fs[finite_setTheory.fSUBSET_def]
QED

(* processing a rule
     N -> sf
   symbol by symbol, augmenting the finite-map of information in A

   This does the "easy" analysis, finding tokens that are directly
   after non-terminals on rule RHSs.

   The "hard" analysis is recognising that the follow-set of an NT inside
   a RHS needs to include the follow set of the rule's LHS if what comes after
   the NT in the rule is nullable.
*)
Definition follow_p1_def[simp]:
  follow_p1 g [] A = A ∧
  follow_p1 g (TOK _ :: rest) A = follow_p1 g rest A ∧
  follow_p1 g (NT n :: rest) A =
    follow_p1 g rest
              (augment n (fromSet (firstSet g rest)) A)
End

Theorem follow_p1_augment:
  ∀sf N fs A. follow_p1 g sf (augment N fs A) = augment N fs (follow_p1 g sf A)
Proof
  Induct >> simp[] >> Cases >> simp[augment_commutes]
QED

Theorem follow_p1_commutes:
  ∀sf1 sf2 A. follow_p1 g sf1 (follow_p1 g sf2 A) =
              follow_p1 g sf2 (follow_p1 g sf1 A)
Proof
  Induct >> simp[] >> Cases >> simp[]
  >- first_assum ACCEPT_TAC >>
  simp[follow_p1_augment] >> metis_tac[]
QED

Definition follow_approx_def:
  follow_approx g A ⇔ ∀N fs. FLOOKUP A N = SOME fs ⇒ ∀s. s ∈ᶠ fs ⇒ follow g N s
End

Theorem follow_approx_FEMPTY[simp]:
  follow_approx g FEMPTY
Proof
  simp[follow_approx_def]
QED

Theorem follow_approx_augment[simp]:
  follow_approx g (augment N fs A) ⇔
  follow_approx g A ∧ ∀s. s ∈ᶠ fs ⇒ follow g N s
Proof
  simp[augment_def, follow_approx_def, FLOOKUP_DEF] >> rw[] >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, FAPPLY_FUPDATE_THM] >>
  asm_simp_tac (srw_ss() ++ boolSimps.COND_elim_ss) [] >> metis_tac[]
QED

Theorem follow_p1_approxes:
  ∀A. follow_approx g A ∧ N ∈ FDOM g.rules ∧ sf ∈ᶠ g.rules ' N ∧
      IS_SUFFIX sf sf0 ⇒
      follow_approx g (follow_p1 g sf0 A)
Proof
  Induct_on ‘sf0’ >> simp[] >> Cases >> simp[] >> rw[]
  >- metis_tac[IS_SUFFIX_CONS2_E] >>
  first_x_assum irule >> simp[] >> conj_tac
  >- metis_tac[IS_SUFFIX_CONS2_E] >>
  simp[finite_setTheory.IN_fromSet] >>
  fs[IS_SUFFIX_APPEND] >> metis_tac[follow_rules]
QED

Theorem ITSET_follow_p1_approxes:
  ∀s0 A. follow_approx g A ∧
         (∀e. e ∈ᶠ s0 ⇒ ∃N s. N ∈ FDOM g.rules ∧ g.rules ' N = s ∧ e ∈ᶠ s) ⇒
         follow_approx g (fITSET (follow_p1 g) s0 A)
Proof
  Induct >> simp[DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
  simp[finite_setTheory.fITSET_INSERT, follow_p1_commutes] >>
  irule follow_p1_approxes >> conj_tac
  >- metis_tac[IS_SUFFIX_REFL] >>
  first_x_assum irule >> simp[]
QED

Definition follow_phase1_def:
  follow_phase1 g = ITFMAP (K (fITSET (follow_p1 g))) g.rules
End

Theorem fITSET_commutes1:
  (∀e1 e2 A. f e1 (f e2 A) = f e2 (f e1 A)) ⇒
  ∀s e A. fITSET f s (f e A) = f e (fITSET f s A)
Proof
  strip_tac >> Induct >> simp[finite_setTheory.fITSET_INSERT]
QED

Theorem fITSET_commutes:
  (∀e1 e2 A. f e1 (f e2 A) = f e2 (f e1 A)) ⇒
  ∀s1 s2 A. fITSET f s1 (fITSET f s2 A) = fITSET f s2 (fITSET f s1 A)
Proof
  strip_tac >> Induct >>
  simp[finite_setTheory.fITSET_INSERT, fITSET_commutes1] >> metis_tac[]
QED

Theorem K_fITfollowp1_commutes:
  ∀(k1:'a) (k2:'a) v1 v2 A.
    K (fITSET (follow_p1 g)) k1 v1 (K (fITSET (follow_p1 g)) k2 v2 A) =
    K (fITSET (follow_p1 g)) k2 v2 (K (fITSET (follow_p1 g)) k1 v1 A)
Proof
  simp[] >> irule fITSET_commutes >> simp[follow_p1_commutes]
QED


Theorem follow_phase1_approxes:
  ∀A. follow_approx g A ⇒ follow_approx g (follow_phase1 g A)
Proof
  simp[follow_phase1_def] >>
  ‘∀rm A. follow_approx g A ∧ rm ⊑ g.rules ⇒
          follow_approx g (ITFMAP (K (fITSET (follow_p1 g))) rm A)’
    suffices_by metis_tac[SUBMAP_REFL] >>
  Induct>> rw[] >> fs[SUBMAP_FUPDATE] >> rfs[DOMSUB_NOT_IN_DOM] >>
  ‘rm ⊑ g.rules’
    by (pop_assum mp_tac >> csimp[SUBMAP_DEF, DOMSUB_FAPPLY_THM]) >>
  simp[MATCH_MP (ITFMAP_thm |> CONJUNCT2) K_fITfollowp1_commutes] >>
  irule ITSET_follow_p1_approxes >> simp[DOMSUB_NOT_IN_DOM] >> metis_tac[]
QED

Definition follow_rules1_def:
  follow_rules1 g rfm = ITFMAP (K (fITSET (follow_p1 g))) rfm
End

Theorem follow_rules1_thm0:
  follow_rules1 g FEMPTY A = A ∧
  follow_rules1 g (fm |+ (nt, rs)) A =
  follow_rules1 g (fm \\ nt) (fITSET (follow_p1 g) rs A)
Proof
  simp[follow_rules1_def] >>
  REWRITE_TAC[MATCH_MP ITFMAP_tail K_fITfollowp1_commutes] >>
  simp[]
QED

Theorem follow_rules1_thm:
  follow_rules1 g FEMPTY A = A ∧
  follow_rules1 g (fm |+ (nt, ∅ᶠ)) A = follow_rules1 g (fm \\ nt) A ∧
  follow_rules1 g (fm |+ (nt, fINSERT r rs)) A =
    follow_rules1 g (fm |+ (nt, fDELETE r rs)) (follow_p1 g r A)
Proof
  simp[follow_rules1_thm0, finite_setTheory.fITSET_INSERT_tail,
       follow_p1_commutes]
QED

Theorem follow_phase1_thm:
  follow_phase1 g A = follow_rules1 g g.rules A
Proof
  simp[follow_phase1_def, follow_rules1_def]
QED

Definition follow_p2_sf_def:
  follow_p2_sf g M [] A = A ∧
  follow_p2_sf g M (TOK _ :: rest) A = follow_p2_sf g M rest A ∧
  follow_p2_sf g M (NT N :: rest) A =
  if nullable g rest then follow_p2_sf g M rest (augment N (safelookup A M) A)
  else follow_p2_sf g M rest A
End

Theorem follow_p2_sf_approxes:
  ∀A. follow_approx g A ∧ M ∈ FDOM g.rules ∧ sf0 ∈ᶠ g.rules ' M ∧
      IS_SUFFIX sf0 sf ⇒
      follow_approx g (follow_p2_sf g M sf A)
Proof
  Induct_on ‘sf’ >> simp[follow_p2_sf_def] >> rw[] >> Cases_on ‘h’ >>
  simp[follow_p2_sf_def]
  >- metis_tac[IS_SUFFIX_CONS2_E] >>
  reverse (rw[]) >- metis_tac[IS_SUFFIX_CONS2_E] >>
  first_x_assum irule >> simp[] >> conj_tac >- metis_tac[IS_SUFFIX_CONS2_E] >>
  fs[follow_approx_def, safelookup_def] >> Cases_on ‘FLOOKUP A M’ >> simp[] >>
  fs[IS_SUFFIX_APPEND] >> metis_tac[follow_rules]
QED

Theorem safelookup_augment_thm:
  safelookup (augment k1 v A) k2 =
  if k1 = k2 then safelookup A k1 ∪ᶠ v else safelookup A k2
Proof
  rw[safelookup_def, augment_def]
  >- (Cases_on ‘FLOOKUP A k1’ >> simp[FLOOKUP_UPDATE]) >>
  Cases_on ‘FLOOKUP A k1’ >> simp[FLOOKUP_UPDATE]
QED

Theorem follow_p2_sf_alt:
  follow_p2_sf g M (NT N :: rest) A =
  if N = M ∨ ¬nullable g rest then follow_p2_sf g M rest A
  else follow_p2_sf g M rest (augment N (safelookup A M) A)
Proof
  rw[follow_p2_sf_def] >> fs[] >> AP_TERM_TAC >>
  rw[augment_def, safelookup_def] >> Cases_on ‘FLOOKUP A M’ >> fs[] >>
  fs[FLOOKUP_DEF, fmap_EXT, DISJ_IMP_THM, FAPPLY_FUPDATE_THM, ABSORPTION_RWT] >>
  rw[]
QED

Theorem safelookup_follow_p2_sf[simp]:
  ∀A sf. safelookup (follow_p2_sf g M sf A) M = safelookup A M
Proof
  Induct_on ‘sf’ >> simp[follow_p2_sf_def] >> Cases >>
  rw[follow_p2_sf_def, safelookup_augment_thm]
QED

Theorem augment_follow_p2_sf:
  ∀A M N.
    M ≠ N ⇒
    augment N v (follow_p2_sf g M sf A) = follow_p2_sf g M sf (augment N v A)
Proof
  Induct_on ‘sf’ >> simp[follow_p2_sf_def] >> Cases
  >- simp[follow_p2_sf_def] >>
  rw[safelookup_augment_thm, follow_p2_sf_alt] >> fs[] >>
  metis_tac[augment_commutes]
QED

Theorem follow_p2_sf_commutes:
  ∀A. follow_p2_sf g M sf1 (follow_p2_sf g M sf2 A) =
      follow_p2_sf g M sf2 (follow_p2_sf g M sf1 A)
Proof
  Induct_on ‘sf1’ >> simp[follow_p2_sf_def] >> Cases
  >- (simp[follow_p2_sf_def] >> metis_tac[]) >>
  rw[follow_p2_sf_alt] >- metis_tac[] >- metis_tac[] >> fs[] >>
  metis_tac[augment_follow_p2_sf]
QED




(*


(* smash together all sets in the range of the finite map *)
Definition range_max_def:
  range_max A = fBIGUNION (ffRANGE A)
End
Theorem range_max_FEMPTY[simp]:
  range_max FEMPTY = ∅ᶠ
Proof
  simp[range_max_def]
QED

Definition max_map_def:
  max_map A g =
    FUN_FMAP (K (fromSet (terminals g) ∪ᶠ range_max A)) (nonTerminals g)
End

Theorem FDOM_max_map[simp]:
  FDOM (max_map A g) = nonTerminals g
Proof
  simp[max_map_def]
QED

Definition fmset_union_def:
  fmset_union fm1 fm2 =
    FUN_FMAP (λk. safelookup fm1 k ∪ᶠ safelookup fm2 k) (FDOM fm1 ∪ FDOM fm2)
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
       FLOOKUP_DEF, finite_setTheory.fSUBSET_def]
QED

Theorem follow_sf_SUBDOM:
  ∀A. subfmset_map A (follow_sf g N sf A)
Proof
  Induct_on ‘sf’ >> simp[] >> Cases >> simp[] >>
  metis_tac[subfmset_map_augment, subfmset_map_TRANS]
QED

Theorem subfmset_map_augment':
   subfmset_map (augment k v fm1) fm2 ⇔
   subfmset_map fm1 fm2 ∧ v ⊆ᶠ safelookup fm2 k
Proof
  simp[subfmset_map_def, safelookup_def, augment_def] >>
  Cases_on ‘FLOOKUP fm1 k’ >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, FAPPLY_FUPDATE_THM] >>
  asm_simp_tac (srw_ss() ++ boolSimps.COND_elim_ss)[]
  >- (‘∀k'. k' ∈ FDOM fm1 ⇒ k' ≠ k’ by (rpt strip_tac >> fs[FLOOKUP_DEF]) >>
      simp[] >> Cases_on ‘FLOOKUP fm2 k’ >> simp[] >> metis_tac[]) >>
  Cases_on ‘FLOOKUP fm2 k’ >> csimp[] >> eq_tac >> rw[]
  >- (first_x_assum drule >> rw[] >> fs[FLOOKUP_DEF])
  >- (first_x_assum (qspec_then ‘k’ mp_tac) >> fs[FLOOKUP_DEF])
  >- (first_x_assum drule >> rw[] >> rfs[] >> fs[FLOOKUP_DEF] >>
      metis_tac[finite_setTheory.IN_UNION, finite_setTheory.fSUBSET_def])
  >- metis_tac[finite_setTheory.IN_UNION, finite_setTheory.fSUBSET_def]
  >- (first_x_assum (qspec_then ‘k’ mp_tac) >> fs[FLOOKUP_DEF] >>
      metis_tac[finite_setTheory.IN_UNION, finite_setTheory.fSUBSET_def]) >>
  first_x_assum (qspec_then ‘k’ mp_tac) >> fs[FLOOKUP_DEF] >>
  metis_tac[finite_setTheory.IN_UNION, finite_setTheory.fSUBSET_def]
QED

Theorem toSet_fromSet[simp]:
  FINITE s ⇒ toSet (fromSet s) = s
Proof
  simp[finite_setTheory.fromSet_def, SET_TO_LIST_INV]
QED

Theorem toSet_fUNION[simp]:
  toSet (A ∪ᶠ B) = toSet A ∪ toSet B
Proof
  simp[EXTENSION, GSYM finite_setTheory.fIN_IN]
QED

Theorem toSet_fBIGUNION[simp]:
  toSet (fBIGUNION fs) = BIGUNION (toSet (fIMAGE toSet fs))
Proof
  simp[Once EXTENSION, GSYM finite_setTheory.fIN_IN,
       finite_setTheory.IN_BIGUNION, PULL_EXISTS]>>
  metis_tac[]
QED

Theorem toSet_fIMAGE[simp]:
  toSet (fIMAGE f s) = IMAGE f (toSet s)
Proof
  simp[EXTENSION, GSYM finite_setTheory.fIN_IN] >> metis_tac[]
QED

Theorem follow_sf_max:
  ∀A B. (∀t. MEM t sf ⇒ t ∈ allSyms g) ∧ N ∈ nonTerminals g ∧
        subfmset_map B (fmset_union A (max_map A g)) ⇒
        subfmset_map (follow_sf g N sf B) (fmset_union A (max_map A g))
Proof
  Induct_on ‘sf’ >> simp[] >> Cases >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt strip_tac >> fs[] >> first_x_assum irule >>
  simp[subfmset_map_augment', finite_setTheory.fSUBSET_def] >>
  rw[]
  >- (drule firstSet_SUBSET_terminals >>
      simp[safelookup_def, fmset_union_def, FLOOKUP_DEF] >>
      rename [‘NT s ∈ allSyms g’] >>
      ‘s ∈ nonTerminals g’ by fs[allSyms_def] >> simp[FUN_FMAP_DEF] >>
      simp[max_map_def, FUN_FMAP_DEF] >>
      fs[finite_setTheory.IN_fromSet] >>
      metis_tac[SUBSET_DEF])
  >- (fs[allSyms_def, subfmset_map_def, safelookup_def, FLOOKUP_DEF] >>
      ‘N ∈ FDOM B’ by (CCONTR_TAC >> fs[]) >> fs[] >>
      first_x_assum drule >> simp[finite_setTheory.fSUBSET_def] >>
      disch_then drule >>
      simp[fmset_union_def, FLOOKUP_DEF, FUN_FMAP_DEF, safelookup_def,
           max_map_def, range_max_def, finite_setTheory.IN_BIGUNION,
           finite_setTheory.ffRANGE_def, finite_setTheory.fIN_IN,
           PULL_EXISTS] >> strip_tac >> simp[]
      >- (Cases_on ‘N ∈ FDOM A’ >> fs[] >>
          simp[FRANGE_DEF, PULL_EXISTS] >> metis_tac[]) >>
      metis_tac[]) >>
  drule firstSet_SUBSET_terminals >>
  fs[allSyms_def, SUBSET_DEF, finite_setTheory.fIN_IN] >>
  simp[fmset_union_def, FLOOKUP_DEF, FUN_FMAP_DEF, safelookup_def,
       max_map_def, range_max_def, finite_setTheory.IN_BIGUNION,
       finite_setTheory.ffRANGE_def, finite_setTheory.fIN_IN,
       PULL_EXISTS]
QED
(*
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
*)
val _ = export_theory()
