open HolKernel Parse boolLib bossLib;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;

open chap2_1Theory;
open chap2_2Theory;
open chap2_4revisedTheory;
open chap2_5Theory;
open chap2_6Theory;
open prop2_29Theory;
open ultraproductTheory;
open lemma2_73Theory;
open equiv_on_partitionTheory;
open prim_recTheory;
open listTheory;
open finite_mapTheory;
open combinTheory;
open ultrafilterTheory;

open folLangTheory;
open folModelsTheory;
open folCanonTheory;

val _ = new_theory "chap2_7";


val sim_def = Define`
  sim Z M M' <=>
  !w w'. w IN M.frame.world /\ w' IN M'.frame.world /\ Z w w' ==>
  (!p. w IN M.valt p ==> w' IN M'.valt p) /\
  (!v. v IN M.frame.world /\ M.frame.rel w v ==> ?v'. v' IN M'.frame.world /\ Z v v' /\ M'.frame.rel w' v')`;

val preserved_under_sim_def = Define`
  preserved_under_sim (μ:'a itself) (ν:'b itself) phi <=>
  (!M M' Z w w'. w:'a IN M.frame.world /\ w':'b IN M'.frame.world /\ sim Z M M' /\ Z w w' ==> (satis M w phi ==> satis M' w' phi))`;



val (PE_rules, PE_ind, PE_cases) = Hol_reln`
  (PE FALSE) /\
  (PE TRUE) /\
  (!p. PE (VAR p)) /\
  (!f1 f2. (PE f1 /\ PE f2) ==> PE (AND f1 f2)) /\
  (!f1 f2. (PE f1 /\ PE f2) ==> PE (DISJ f1 f2)) /\
  (!f. PE f ==> PE (DIAM f))`;


val thm_2_78_half1_lemma = store_thm(
  "thm_2_78_half1_lemma",
  ``!phi. PE phi ==> (!μ ν. preserved_under_sim μ ν phi)``,
   Induct_on `PE phi` >> rw[preserved_under_sim_def] (* 6 *)
   >- fs[satis_def]
   >- fs[satis_def,TRUE_def]
   >- (fs[satis_def] >> metis_tac[sim_def])
   >- (fs[satis_AND] >> metis_tac[])
   >- (fs[satis_def] >> metis_tac[])
   >- (fs[satis_def] >> imp_res_tac sim_def >> metis_tac[]));

val thm_2_78_half1 = store_thm(
  "thm_2_78_half1",
  ``!phi phi0. (PE phi0 /\ equiv0 (:β) phi phi0 /\ equiv0 (:γ) phi phi0) ==> preserved_under_sim (:β) (:γ) phi``,
  rw[] >> `preserved_under_sim (:β) (:γ) phi0` by metis_tac[thm_2_78_half1_lemma] >>
  fs[preserved_under_sim_def] >> rw[] >> fs[equiv0_def] >> `satis M w phi0` by metis_tac[] >> metis_tac[]);


Theorem FINITE_SUBSET_IMAGE_lemma :
!s f ss. FINITE ss /\ ss ⊆ IMAGE f s ==>
         ?s0. FINITE s0 /\ s0 ⊆ s /\ ss = IMAGE f s0
Proof
rw[] >> qabbrev_tac `A = IMAGE CHOICE {{a | f a = e /\ a IN s}| e IN ss}` >>
qexists_tac `A` >>
`!e. e IN ss ==> {a | f a = e /\ a IN s} <> {}`
   by (rw[] >> fs[IMAGE_DEF,SUBSET_DEF,GSYM MEMBER_NOT_EMPTY] >> metis_tac[]) >>
`A ⊆ s`
  by (rw[Abbr`A`,SUBSET_DEF] >>
      `CHOICE {a | f a = e ∧ a ∈ s} ∈ {a | f a = e ∧ a ∈ s}` suffices_by fs[] >>
      metis_tac[CHOICE_DEF]) >>
rw[IMAGE_DEF,EQ_IMP_THM,EXTENSION] (* 2 *)
>- (rw[Abbr`A`] >> irule IMAGE_FINITE >>
   `?ff. {{a | f a = e ∧ a ∈ s} | e ∈ ss} = IMAGE ff ss`
     suffices_by metis_tac[IMAGE_FINITE] >>
   qexists_tac `\e. {a | f a = e ∧ a ∈ s}` >> rw[IMAGE_DEF,Once EXTENSION])
>- (qexists_tac `CHOICE {a | f a = x ∧ a ∈ s}` >> rw[Abbr`A`] (* 2 *)
   >- (`(CHOICE {a | f a = x ∧ a ∈ s}) IN {a | f a = x ∧ a ∈ s}` suffices_by fs[] >>
       metis_tac[CHOICE_DEF])
   >- (fs[PULL_EXISTS] >> qexists_tac `x` >> rw[]))
>- (fs[Abbr`A`] >> `f (CHOICE {a | f a = e ∧ a ∈ s}) = e` suffices_by metis_tac[] >>
    `(CHOICE {a | f a = e ∧ a ∈ s}) IN {a | f a = e ∧ a ∈ s}` suffices_by fs[] >>
    metis_tac[CHOICE_DEF])
QED


Theorem prop_2_47_i':
 !M w:'b phi σ x. (IMAGE σ univ(:num)) SUBSET M.Dom
                       ==> (satis (folm2mm M) (σ x) phi <=> feval M σ (ST x phi))
Proof
Induct_on `phi` (* 3 *) >> rw[satis_def,feval_def]
>- (rw[folm2mm_def] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
>- (rw[folm2mm_def] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
>- (rw[EQ_IMP_THM] (* 3 *)
   >- (qexists_tac `v` >> rw[] (* 3 *)
       >- fs[folm2mm_def]
       >- fs[folm2mm_def,APPLY_UPDATE_THM]
       >- (`IMAGE σ⦇x + 1 ↦ v⦈ 𝕌(:num) ⊆ M.Dom`
            by (irule IMAGE_UPDATE >> fs[folm2mm_def]) >>
           first_x_assum drule >> rw[] >>
           first_x_assum (qspec_then `x + 1` assume_tac) >>
           fs[APPLY_UPDATE_THM]))
   >- (fs[IMAGE_DEF,SUBSET_DEF,folm2mm_def] >> metis_tac[])
   >- (qexists_tac `a` >> fs[APPLY_UPDATE_THM] >> rw[] (* 3 *)
      >- (fs[folm2mm_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
      >- rw[folm2mm_def]
      >- (`IMAGE σ⦇x + 1 ↦ a⦈ 𝕌(:num) ⊆ M.Dom`
            by (irule IMAGE_UPDATE >> fs[folm2mm_def]) >>
         first_x_assum drule >> rw[] >> first_x_assum (qspec_then `x + 1` assume_tac) >>
         fs[APPLY_UPDATE_THM])))
QED
(*
Theorem compactness_thm_L1tau:
INFINITE (univ (:α)) ==>
!A.
  ((!f. f IN A ==> L1tau f) /\
   (!ss. (FINITE ss /\ ss ⊆ A) ==>
     ?M:α folModels$model σ:num -> α. valuation M σ /\
                   (!ff. ff IN ss ==> feval M σ ff))) ==>
 (?M:α folModels$model σ:num -> α. valuation M σ /\
                   (!f. f IN A ==> feval M σ f))
Proof
rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
Cases_on `FINITE A` (* 2 *)
>- (first_x_assum drule >> rw[SUBSET_DEF] >> metis_tac[]) >>
`?ss. FINITE ss ∧ ss ⊆ A /\
      (!M σ. valuation M σ ==> ?ff. ff ∈ ss /\ ¬feval M σ ff)`
suffices_by metis_tac[] >>
`?f. f IN A` by metis_tac[INFINITE_INHAB] >>
`entails (:α) (A DELETE f) (fNOT f)`
  by
   (rw[entails_def] >> SPOSE_NOT_THEN ASSUME_TAC >>
    `!f. f IN A ==> feval M v f` suffices_by metis_tac[] >>
    rw[] >> Cases_on `f = f'` (* 2 *)
    >- fs[] >> fs[DELETE_DEF,hold_def]) >>
`?A0. FINITE A0 /\ A0 ⊆ (A DELETE f) /\ entails (:α) A0 (fNOT f)`
  by metis_tac[finite_entailment] >>
qexists_tac `f INSERT A0` >> rw[] (* 2 *)
>- fs[SUBSET_DEF] >>
fs[entails_def] >> first_x_assum drule >> strip_tac >>
Cases_on `feval M σ f`
>- (`?ff. ff IN A0 /\ ¬feval M σ ff` suffices_by metis_tac[] >>
   SPOSE_NOT_THEN ASSUME_TAC >>
   `¬feval M σ f` suffices_by metis_tac[] >>
   `interpretation (language (fNOT f INSERT A0)) M ∧ M.Dom ≠ ∅ ∧
    hold M σ A0` suffices_by metis_tac[] >> rw[] (* 3 *)
   >- (simp[interpretation_def,language_def] >>
      `functions (fNOT f INSERT A0) = {}`
        suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
      rw[functions_def] >>
      `{form_functions f' | f' = fNOT f ∨ f' ∈ A0} = {∅}`
       suffices_by metis_tac[] >>
      rw[Once EXTENSION] >>
      `(!f. f IN A0 ==> form_functions f = {}) /\ form_functions (fNOT f) = {}`
       suffices_by metis_tac[] >> rw[] (* 2 *)
      >- fs[SUBSET_DEF,L1tau_def] >>
      fs[form_functions_def,fNOT_def,L1tau_def])
   >- (rw[GSYM MEMBER_NOT_EMPTY] >> metis_tac[valuation_def])
   >- rw[hold_def])
>- metis_tac[]
QED

Theorem compactness_corollary_L1tau:
INFINITE (univ (:α)) ==>
!A a. L1tau a ==>
  ((!f. f IN A ==> L1tau f) /\
   (!M:α folModels$model σ:num -> α. valuation M σ ==>
    (!f. f IN A ==> feval M σ f) ==> feval M σ a)) ==>
  (?ss. FINITE ss /\ ss ⊆ A /\
        (!M:α folModels$model σ:num -> α. valuation M σ ==>
          (!f. f IN ss ==> feval M σ f) ==> feval M σ a))
Proof
rw[] >> drule compactness_thm_L1tau >> rw[] >>
SPOSE_NOT_THEN ASSUME_TAC >>
last_x_assum (qspec_then `A ∪ {fNOT a}` assume_tac) >>
`?M σ. valuation M σ /\ (∀f. f ∈ A ⇒ feval M σ f) /\ ¬feval M σ a`
  suffices_by metis_tac[] >>
`∃M σ. valuation M σ ∧ ∀f. f ∈ A ∪ {fNOT a} ⇒ feval M σ f`
  suffices_by
   (rw[fNOT_def,feval_def] >> map_every qexists_tac [`M`,`σ`] >>
    `feval M σ (a -> fFALSE)` by metis_tac[] >>
    `¬feval M σ a` by fs[feval_def] >> metis_tac[]) >>
first_x_assum irule >> rw[] (* 3 *)
>- metis_tac[]
>- fs[L1tau_def,fNOT_def,form_functions_def,form_predicates]
>- (`ss DELETE (fNOT a) ⊆ A` by (fs[DELETE_DEF,SUBSET_DEF] >> metis_tac[]) >>
   `FINITE (ss DELETE (fNOT a))` by fs[] >>
   first_x_assum drule_all >> rw[] >> map_every qexists_tac [`M`,`σ`] >> rw[] >>
   Cases_on `ff = fNOT a` (* 2 *)
   >> rw[])
QED

*)

Theorem modal_compactness_thm:
INFINITE (univ (:α)) ==>
!s:chap1$form -> bool.
  (!ss. FINITE ss /\ ss ⊆ s ==>
      ?M w:α. w IN M.frame.world /\ (!f. f IN ss ==> satis M w f)) ==>
  ?M w:α. w IN M.frame.world /\ (!f. f IN s ==> satis M w f)
Proof
rw[] >>
qabbrev_tac `A = {ST x f | f IN s}` >>
`!ss. (FINITE ss /\ ss ⊆ A) ==>
     ?M:α folModels$model σ. valuation M σ /\
                   (!ff. ff IN ss ==> feval M σ ff)`
  by (rw[] >>
      drule (FINITE_SUBSET_IMAGE_lemma |> INST_TYPE [alpha |-> ``:chap1$form``])>>
      strip_tac >>
      first_x_assum (qspecl_then [`s`, `ST x`] assume_tac) >>
      `A = IMAGE (ST x) s`
        by rw[Abbr`A`,IMAGE_DEF,Once EXTENSION] >>
      fs[] >> first_x_assum drule >> strip_tac >> first_x_assum drule >>
      strip_tac >> first_x_assum drule >> strip_tac >>
      map_every qexists_tac [`mm2folm M`,`\a.w`] >> rw[] (* 2 *)
      >- rw[valuation_def,mm2folm_def]
      >- (first_x_assum drule >> strip_tac >>
         `IMAGE (λa. w) 𝕌(:num) ⊆ M.frame.world` by fs[IMAGE_DEF,SUBSET_DEF] >>
         drule prop_2_47_i >> strip_tac >> fs[fsatis_def] >> metis_tac[])) >>
`?M:α folModels$model σ. valuation M σ ∧ ∀f. f ∈ A ⇒ feval M σ f`
  by (irule compactness_thm_L1tau >> rw[] >> fs[Abbr`A`] >>
      metis_tac[ST_L1tau]) >>


(*
`!s. ffinsat (:α) s ⇒ satisfiable (:α) s`
       by metis_tac[COMPACTNESS_satisfiable] >>
      fs[ffinsat_def,satisfiable_def,satisfies_def] >>
      first_x_assum (qspec_then `A` assume_tac) >>
      `∃M:α model.
            M.Dom ≠ ∅ ∧ interpretation (language A) M ∧
            ∀v p. valuation M v ∧ p ∈ A ⇒ feval M v p`
        suffices_by
         (strip_tac >> qexists_tac `M` >> rw[] >>
          fs[GSYM MEMBER_NOT_EMPTY] >>
          qexists_tac `\n.x'` >> rw[]  (* 2 *)
          >- rw[valuation_def] >>
          `valuation M (λn:num. x')` by rw[valuation_def] >>
          first_x_assum irule >> rw[] >> fs[]) >>
      first_x_assum irule >> rw[] >>
      first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >>
      qexists_tac `M` >> rw[] (* 3 *)
      >- (fs[valuation_def] >> metis_tac[MEMBER_NOT_EMPTY])
      >- (rw[interpretation_def,language_def] >>
         `functions t = {}` suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
         fs[SUBSET_DEF,Abbr`A`] >> rw[functions_def] >>
         Cases_on `t = {}` (* 2 *)
         >- fs[] >>
         `{form_functions f | f ∈ t} = {∅}` suffices_by metis_tac[] >>
         rw[Once EXTENSION] >>
         fs[GSYM MEMBER_NOT_EMPTY] >>
         `!f. f IN t ==> form_functions f = {}` suffices_by metis_tac[] >>
         rw[] >> metis_tac[ST_form_functions_EMPTY])
      >- metis_tac[])

 cheat(*compactness cheated*)>>*)
map_every qexists_tac [`folm2mm M`,`σ x`] >> rw[] (* 2 *)
>- fs[folm2mm_def,valuation_def]
>- (first_x_assum (qspec_then `ST x f` assume_tac) >>
   `(ST x f) IN A` by (fs[Abbr`A`] >> metis_tac[]) >>
   first_x_assum drule >> strip_tac >>
   `IMAGE σ 𝕌(:num) ⊆ M.Dom` suffices_by metis_tac[prop_2_47_i'] >>
   fs[valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
QED

Theorem modal_compactness_corollary:
INFINITE (univ (:α)) ==>
!s a.
  (!M w:α. w IN M.frame.world ==>
      (!f:chap1$form. f IN s ==> satis M w f) ==> satis M w a) ==>
   ?ss. FINITE ss /\ ss ⊆ s /\
        (!M w:α. w IN M.frame.world ==>
           (!f. f IN ss ==> satis M w f) ==> satis M w a)
Proof
rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
`!ss. FINITE ss /\ ss ⊆ s ∪ {¬a} ==>
     ?M w:α. w IN M.frame.world /\ (!f. f IN ss ==> satis M w f)`
  by
   (rw[] >>
    Cases_on `(NOT a) IN ss` (* 2 *)
    >- (`ss = ¬a INSERT (ss DELETE ¬a)` by metis_tac[INSERT_DELETE] >>
        `FINITE (ss DELETE ¬a)` by fs[] >>
        `ss DELETE ¬a ⊆ s` by (fs[SUBSET_DEF,DELETE_DEF] >> metis_tac[]) >>
        first_x_assum drule_all >> rw[] >>
        map_every qexists_tac [`M`,`w`] >> rw[] >>
        Cases_on `f = ¬a` (* 2 *)
        >- fs[satis_def] >>
        metis_tac[]) >>
    `ss ⊆ s` by (fs[SUBSET_DEF,UNION_DEF] >> metis_tac[]) >>
    metis_tac[]
   ) >>
drule_all modal_compactness_thm >> strip_tac >>
`satis M w ¬a` by fs[] >>
`!f. f IN s ==> satis M w f` by fs[UNION_DEF] >>
metis_tac[satis_def]
QED



Theorem PE_BIGCONJ:
!ss. FINITE ss ==>
     (!f. f IN ss ==> PE f) ==>
      ?ff. PE ff /\
           !M w. w IN M.frame.world ==>
                  (satis M w ff <=> (!f. f IN ss ==> satis M w f))
Proof
Induct_on `FINITE` >> rw[]
>- (qexists_tac `TRUE` >> rw[satis_def,TRUE_def,PE_rules]) >>
`∀f. f ∈ ss ⇒ PE f` by metis_tac[] >>
first_x_assum drule >> strip_tac >>
qexists_tac `AND e ff` >> rw[] (* 2 *)
>- metis_tac[PE_rules] >>
rw[satis_AND] >> metis_tac[]
QED


Theorem PE_BIGDISJ:
!ss. FINITE ss ==>
     (!f. f IN ss ==> PE f) ==>
      ?ff. PE ff /\
           !M w. w IN M.frame.world ==>
                  (satis M w ff <=> (?f. f IN ss /\ satis M w f))
Proof
Induct_on `FINITE` >> rw[]
>- (qexists_tac `FALSE` >> rw[satis_def,PE_rules]) >>
`!f. f IN ss ==> PE f` by metis_tac[] >>
first_x_assum drule >> strip_tac >>
qexists_tac `DISJ e ff` >> rw[] (* 2 *)
>- metis_tac[PE_rules] >>
rw[satis_def] >> metis_tac[]
QED

Theorem PE_BIGCONJ_DIST_TYPE:
!ss. FINITE ss ==>
     (!f. f IN ss ==> PE f) ==>
      ?ff. PE ff /\
           (!M w:β. w IN M.frame.world ==>
                  (satis M w ff <=> (!f. f IN ss ==> satis M w f))) /\
           (!M w:γ. w IN M.frame.world ==>
                  (satis M w ff <=> (!f. f IN ss ==> satis M w f)))
Proof
Induct_on `FINITE` >> rw[]
>- (qexists_tac `TRUE` >> rw[satis_def,PE_rules,TRUE_def]) >>
`!f. f IN ss ==> PE f` by metis_tac[] >>
first_x_assum drule >> strip_tac >>
qexists_tac `AND e ff` >> rw[] (* 2 *)
>- metis_tac[PE_rules] >>
rw[satis_AND] >> metis_tac[]
QED



Theorem exercise_2_7_1:
!M M' w:β w':γ.
   (M_sat M /\ M_sat M' /\ w IN M.frame.world /\ w' IN M'.frame.world)
     ==>
     (!phi. PE phi ==>
             (satis M w phi ==> satis M' w' phi)) ==>
     ?Z. sim Z M M' /\ Z w w'
Proof
rw[] >>
qexists_tac `\w1 w2. (!phi. PE phi ==> satis M w1 phi ==> satis M' w2 phi)` >>
rw[sim_def] (* 2 *)
>- (`satis M w1 (VAR p) ==> satis M' w2 (VAR p)` by metis_tac[PE_rules] >>
    fs[satis_def]) >>
qabbrev_tac `d = {phi | PE phi /\ satis M w1' phi}` >> fs[M_sat_def] >>
`satisfiable_in d {v | v ∈ M'.frame.world ∧ M'.frame.rel w2 v} M'`
  suffices_by
   (rw[satisfiable_in_def] >> qexists_tac `x` >> rw[] >> fs[Abbr`d`]) >>
first_x_assum irule >> rw[fin_satisfiable_in_def,satisfiable_in_def,SUBSET_DEF] >>
drule PE_BIGCONJ_DIST_TYPE >> strip_tac >>
`∀f. f ∈ S' ⇒ PE f` by fs[Abbr`d`] >> first_x_assum drule >> strip_tac >>
`∃x. (x ∈ M'.frame.world ∧ M'.frame.rel w2 x) ∧
     satis M' x ff` suffices_by metis_tac[] >>
`satis M' w2 (DIAM ff)`
  suffices_by metis_tac[satis_def] >>
first_x_assum irule >>
`PE (DIAM ff)` by metis_tac[PE_rules] >>
rw[satis_def] >>
`?v. M.frame.rel w1 v ∧ v ∈ M.frame.world ∧
     (∀f. f ∈ S' ⇒ satis M v f)`
  suffices_by metis_tac[] >>
qexists_tac `w1'` >> rw[] >>
fs[Abbr`d`]
QED


Theorem thm_2_78_half2:
INFINITE (univ (:β)) ==>
 !phi:chap1$form. 
   preserved_under_sim (:(β -> bool) -> bool) (:(β -> bool) -> bool) phi ==>
     (?phi0. equiv0 (:β) phi phi0 /\ PE phi0)
Proof
rw[] >>
qabbrev_tac `PEC = {psi | PE psi /\
                          (!M w:β. w IN M.frame.world ==>
                               satis M w phi ==> satis M w psi)}` >>
`!M w:β. w IN M.frame.world ==>
      (!f. f IN PEC ==> satis M w f) ==> satis M w phi`
  suffices_by
   (rw[] >>
    drule_all (modal_compactness_corollary |> INST_TYPE [alpha |-> ``:'b``]) >>
    rw[] >> drule (PE_BIGCONJ |> INST_TYPE [alpha |-> ``:'b``])>> rw[] >>
    `!f. f IN ss ==> PE f` by fs[SUBSET_DEF,Abbr`PEC`] >>
    first_x_assum drule_all >> rw[] >> qexists_tac `ff` >>
    rw[EQ_equiv0_def,EQ_IMP_THM] >> fs[Abbr`PEC`,SUBSET_DEF]
   ) >>
rw[] >>
qabbrev_tac `Γ = {NOT psi | PE psi /\ satis M w (NOT psi)}` >>
`!ss. FINITE ss /\ ss ⊆ (Γ ∪ {phi}) ==>
    ?N v:β. v IN N.frame.world /\
           (!f. f IN ss ==> satis N v f)`
  by
   (SPOSE_NOT_THEN ASSUME_TAC >> fs[] >>
    `∀N v:β. v ∈ N.frame.world ⇒
           (satis N v phi ==> ?f. f IN (ss DELETE phi) /\ ¬satis N v f)`
      by (fs[DELETE_DEF] >> metis_tac[]) >>
    `ss DELETE phi ⊆ Γ` by (fs[SUBSET_DEF,DELETE_DEF] >> metis_tac[]) >>
    qabbrev_tac `ss0 =
                 IMAGE (\f. case f of
                            NOT phi => phi
                           | _  => ARB)
                       (ss DELETE phi)` >>
    `FINITE (ss DELETE phi)` by fs[] >>
    `FINITE ss0` by metis_tac[IMAGE_FINITE,Abbr`ss0`] >>
    `!f. f IN ss0 ==> PE f`
      by
       (rw[] >> fs[Abbr`ss0`,IMAGE_DEF] >>
        fs[SUBSET_DEF,Abbr`Γ`] >> first_x_assum drule_all >> rw[] >> fs[]) >>
    drule (PE_BIGDISJ|> INST_TYPE [alpha |-> ``:'b``]) >> strip_tac >>
    (*`ss0 <> {}` by metis_tac[IMAGE_EQ_EMPTY] >> strip_tac >>*)
    first_x_assum drule_all >> strip_tac >>
    `ff IN PEC`
      by
       (rw[Abbr`PEC`] >> last_x_assum drule_all >> strip_tac >>
        rw[Abbr`ss0`,IMAGE_DEF,PULL_EXISTS] >> qexists_tac `f` >>
        rw[] (* 2 *)
        >- metis_tac[] >>
        fs[Abbr`Γ`,SUBSET_DEF] >>
        `f <> phi` by metis_tac[] >>
        `∃psi. f = ¬psi ∧ PE psi ∧ satis M w (¬psi)` by metis_tac[] >>
        fs[] >> metis_tac[satis_def]) >>
    `satis M w ff` by metis_tac[] >>
    `?f. f IN ss0 /\ satis M w f` by metis_tac[] >>
    `satis M w (NOT f)` suffices_by metis_tac[satis_def] >>
    fs[Abbr`ss0`,SUBSET_DEF,Abbr`Γ`] >>
    `∃psi. f' = ¬psi ∧ PE psi ∧ satis M w (¬psi)` by metis_tac[] >> fs[]
   ) >>
drule_all modal_compactness_thm >> rw[] >>
rename [`∀f. f ∈ Γ ∨ f = phi ⇒ satis N v f`] >>
`!psi. PE psi ==> (satis N v psi ==> satis M w psi)`
  by
   (SPOSE_NOT_THEN ASSUME_TAC >> fs[] >>
    `satis M w (¬psi)` by metis_tac[satis_def] >>
    `(¬psi) IN Γ` by fs[Abbr`Γ`] >>
    metis_tac[satis_def]) >>
`!psi. PE psi ==>
         satis (UE N) (principle_UF v N.frame.world) psi ==>
         satis (UE M) (principle_UF w M.frame.world) psi`
  by metis_tac[prop_2_59_ii,modal_eq_tau] >>
`M_sat (UE M) /\ M_sat (UE N)` by metis_tac[prop_2_61] >>
drule (exercise_2_7_1|> INST_TYPE [gamma |-> ``:β``]) >> rw[] >>
first_x_assum
  (qspecl_then [`UE M`,
                `principle_UF v N.frame.world`,
                `principle_UF w M.frame.world`] assume_tac) >>
`principle_UF w M.frame.world ∈ (UE M).frame.world ∧
 principle_UF v N.frame.world ∈ (UE N).frame.world`
  by
   (simp[UE_def] >> metis_tac[principle_UF_UF,MEMBER_NOT_EMPTY]) >>
first_x_assum drule_all >> rw[] >>
fs[preserved_under_sim_def] >>
last_x_assum drule >> rw[] >>
first_x_assum
  (qspecl_then [`UE M`,`Z`,`principle_UF w M.frame.world`] assume_tac) >>
rfs[] >>
`satis N v phi` by metis_tac[] >>
metis_tac[prop_2_59_ii,modal_eq_tau]
QED

Theorem prop_2_47_i0':
satis (folm2mm M) w phi ⇔ fsatis M (\n. w) (ST x phi)
Proof
rw[EQ_IMP_THM] (* 2 *)
>- (`IMAGE (\n.w) 𝕌(:num) ⊆ M.Dom`
     by
      (`(folm2mm M).frame.world = M.Dom` by fs[folm2mm_def] >>
       rw[IMAGE_DEF,SUBSET_DEF] >> metis_tac[satis_in_world]) >>
    drule prop_2_47_i' >> rw[fsatis_def]
    >- fs[valuation_def,IMAGE_DEF,SUBSET_DEF] >>
    metis_tac[])
>- (`IMAGE (\n.w) 𝕌(:num) ⊆ M.Dom`
      by fs[IMAGE_DEF,SUBSET_DEF,fsatis_def,valuation_def] >>
    drule prop_2_47_i' >> rw[] >> fs[fsatis_def] >> metis_tac[])
QED


val _ = export_theory();
