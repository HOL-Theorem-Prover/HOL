open HolKernel Parse boolLib bossLib;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;

open chap2_1Theory;
open chap2_2Theory;
open chap2_4Theory;
open chap2_5Theory;
open equiv_on_partitionTheory;
open prim_recTheory;
open listTheory;
open rich_listTheory;
open finite_mapTheory;
open combinTheory;
open folModelsTheory;
open folLangTheory;
open folCanonTheory;
open ultrafilterTheory;
open ultraproductTheory;
open lemma2_73Theory;
open pairTheory;


val _ = new_theory "chap2_6";
val _ = temp_delsimps ["satis_def"]

val L1tau_def = Define`
L1tau phi <=> form_functions phi = {} /\
              form_predicates phi ⊆ (0,2) INSERT {(p,1)| p IN (univ (:num))}`

Theorem ST_L1tau:
!phi x. L1tau (ST x phi)
Proof
Induct_on `phi` (* 5 *) >>
fs[L1tau_def,fDISJ_def,fNOT_def,fAND_def]
QED

val folm2mm_def = Define`
folm2mm FM = <| frame := <| world := FM.Dom ;
                              rel := \w1 w2. (FM.Pred 0 [w1;w2] /\
                                              w1 IN FM.Dom /\ w2 IN FM.Dom) |>;
                 valt := \v w. (FM.Pred v [w] /\ w IN FM.Dom) |>`;


Theorem MAP_LIST_EQ :
  !l f g. (!m. MEM m l ==> f m = g m) ==> MAP f l = MAP g l
Proof
  rw[] >> irule LIST_EQ >> rw[EL_MAP] >> metis_tac[EL_MEM]
QED


Theorem LIST_UNION_EMPTY:
  !l. (LIST_UNION l = {}) <=> (!s. MEM s l ==> s = {})
Proof
  rw[EQ_IMP_THM]
  >- (SPOSE_NOT_THEN ASSUME_TAC >>
  `?x. x IN s` by metis_tac[MEMBER_NOT_EMPTY] >>
  `x IN (LIST_UNION l)` by metis_tac[IN_LIST_UNION] >>
  metis_tac[MEMBER_NOT_EMPTY])
  >- (`¬(?s. s IN (LIST_UNION l))` suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
     `!s. MEM s l ==> (!x. x NOTIN s)` by metis_tac[MEMBER_NOT_EMPTY] >>
     SPOSE_NOT_THEN ASSUME_TAC >> metis_tac[IN_LIST_UNION])
QED

Theorem FC_EMPTY_termval:
  !M1 M2. (M1.Dom = M2.Dom /\
           M1.Pred = M2.Pred /\
           (!n l. l <> [] ==> M1.Fun n l = M2.Fun n l))
            ==> !t σ. FCT t = {} ==>
            termval M1 σ t = termval M2 σ t
Proof
  strip_tac >> strip_tac >> strip_tac >> completeInduct_on `term_size t` >> rw[] >>
  Cases_on `t` >> fs[FCT_def,termval_def] >> Cases_on `l = []` >> fs[] >>
  `(MAP (termval M1 σ) l) = (MAP (termval M2 σ) l)` suffices_by metis_tac[] >>
  irule MAP_LIST_EQ >> rw[] >> Cases_on `m` >> rw[termval_def] >>
  `term_size (Fn n' l') < 1 + (n + term1_size l)` by fs[term_size_lemma] >>
  first_x_assum (qspec_then `term_size (Fn n' l')` assume_tac) >>
  `1 + (n + term1_size l) = n + (term1_size l + 1)` by fs[] >>
  fs[] >> first_x_assum drule >> rw[] >>
  first_x_assum (qspec_then `Fn n' l'` assume_tac) >> fs[term_size_def] >>
  Cases_on `l' = []`
  >- (fs[] >> `MEM (FCT (Fn n' [])) (MAP (λa. FCT a) l)` by (fs[MEM_MAP] >>
     qexists_tac `Fn n' []` >> fs[FCT_def]) >>
     `(FCT (Fn n' [])) = {}` by metis_tac[LIST_UNION_EMPTY] >> fs[FCT_def])
  >- (first_x_assum irule >> rw[] >>
     `MEM (FCT (Fn n' l')) (MAP (λa. FCT a) l)` by (fs[MEM_MAP] >>
     qexists_tac `Fn n' l'` >> fs[FCT_def]) >>
     `(FCT (Fn n' l')) = {}` by metis_tac[LIST_UNION_EMPTY] >>
     fs[FCT_def] >> Cases_on `l' = []` >> fs[])
QED


Theorem FC_EMPTY_feval:
   !M1 M2. (M1.Dom = M2.Dom /\
            M1.Pred = M2.Pred /\
            (!n l. l <> [] ==> M1.Fun n l = M2.Fun n l))
            ==> !phi σ. FC phi = {} ==>
            feval M1 σ phi = feval M2 σ phi
Proof
  strip_tac >> strip_tac >> strip_tac >>
  Induct_on `phi` >> rw[fsatis_def,feval_def,valuation_def] >>
  `(MAP (termval M1 σ) l) = (MAP (termval M2 σ) l)` suffices_by metis_tac[] >>
  irule MAP_LIST_EQ >> rw[] >> irule FC_EMPTY_termval >> rw[] >>
  `MEM (FCT m) (MAP FCT l)` suffices_by metis_tac[LIST_UNION_EMPTY] >>
  fs[MEM_MAP] >> metis_tac[]
QED


Theorem FC_EMPTY_fsatis:
   !M1 M2. (M1.Dom = M2.Dom /\
            M1.Pred = M2.Pred /\
            (!n l. l <> [] ==> M1.Fun n l = M2.Fun n l))
            ==> !phi σ. FC phi = {} ==>
            fsatis M1 σ phi = fsatis M2 σ phi
Proof
  rw[fsatis_def,feval_def,valuation_def] >> metis_tac[FC_EMPTY_feval]
QED



val ST_form_functions_EMPTY = store_thm(
  "ST_form_functions_EMPTY",
  ``!f x. form_functions (ST x f) = {}``,
  Induct_on `f` >>
 rw[ST_def,form_functions_def,fNOT_def,fAND_def,fDISJ_def,Exists_def]);


val ST_FV_singleton = store_thm(
  "ST_FV_singleton",
  ``!f x. (FV (ST x f)) SUBSET {x}``,
  Induct_on `f` >> rw[ST_def,FV_def,fNOT_def,fAND_def,fDISJ_def] >>
  fs[SUBSET_DEF] >> metis_tac[]);

Theorem term_functions_EMPTY_termval:
!t. term_functions t = {} ==>
               !M1 M2 σ. M1.Dom = M2.Dom /\
                         M1.Pred = M2.Pred ==>
               (termval M1 σ t = termval M2 σ t)
Proof
rw[] >> Cases_on `t` >> fs[term_functions_def]
QED


Theorem form_functions_EMPTY_feval:
!phi. form_functions phi = {} ==>
               !M1 M2 σ. M1.Dom = M2.Dom /\
                         M1.Pred = M2.Pred ==>
               (feval M1 σ phi <=> feval M2 σ phi)
Proof
Induct_on `phi` >> rw[feval_def] (* 3 *)
>- (`(MAP (termval M1 σ) l) = (MAP (termval M2 σ) l)` suffices_by metis_tac[] >>
   irule MAP_CONG >> rw[] >>
   `term_functions x = {}`
     suffices_by metis_tac[term_functions_EMPTY_termval] >>
   SPOSE_NOT_THEN ASSUME_TAC >> fs[GSYM MEMBER_NOT_EMPTY] >>
   `x' IN (LIST_UNION (MAP term_functions l))`
    suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
   rw[IN_LIST_UNION] >> rw[MEM_MAP,PULL_EXISTS] >> metis_tac[])
>- metis_tac[]
>- metis_tac[]
QED



Theorem thm_2_65:
  !M. countably_saturated (mm2folm M) ==> M_sat M
Proof
  rw[countably_saturated_def,n_saturated_def,M_sat_def] >>
  qabbrev_tac ‘Σ' = {fR (Fn 0 []) (fV x)} UNION (IMAGE (ST x) Σ)’ >>
  qabbrev_tac ‘MA = <| Dom := (mm2folm M).Dom;
                       Fun := (λn args. if n = 0 ∧ args = [] then w
                                        else CHOICE (mm2folm M).Dom);
                       Pred := (mm2folm M).Pred |>’ >>
  ‘consistent MA Σ'’
    by (rw[consistent_def] >> fs[fin_satisfiable_in_def] >>
        Cases_on ‘(fR (Fn 0 []) (fV x)) IN G0’ (* 2 *)
        >- (‘G0 = (fR (Fn 0 []) (fV x)) INSERT (G0 DELETE (fR (Fn 0 []) (fV x)))’
              by fs[INSERT_DELETE] >>
            ‘!f. f IN G0 ==> f = fR (Fn 0 []) (fV x) \/ f IN (IMAGE (ST x) Σ)’
              by (rpt strip_tac >>
                  ‘f <> fR (Fn 0 []) (fV x) ==> f ∈ IMAGE (ST x) Σ’
                    suffices_by metis_tac[] >>
                  strip_tac >>
                  ‘f IN Σ'’ by fs[SUBSET_DEF] >> fs[Abbr‘Σ'’] (* 2 *)
                  >- fs[] >- metis_tac[]) >>
            fs[satisfiable_in_def] >>
            qabbrev_tac ‘G0' = G0 DELETE fR (Fn 0 []) (fV x)’ >>
            qabbrev_tac
            ‘ps =
             {CHOICE {x' | x' IN Σ /\ f = ST x x'} | f IN G0'}’ >>
            ‘!f. (f IN G0 /\ f <> fR (Fn 0 []) (fV x))
                 ==> {x' | x' IN Σ /\ f = ST x x'} <> {}’
              by (rw[] >> rfs[Abbr‘Σ'’,IMAGE_DEF] >> rw[GSYM MEMBER_NOT_EMPTY] >>
                  metis_tac[]) >>
            ‘ps SUBSET Σ’
              by
              (rw[SUBSET_DEF,Abbr‘ps’] >>
               ‘CHOICE {x' | x' ∈ Σ ∧ f = ST x x'} IN
                                             {x' | x' ∈ Σ ∧ f = ST x x'}’
                 suffices_by fs[] >>
               ‘{x' | x' ∈ Σ ∧ f = ST x x'} <> {}’
                 suffices_by metis_tac[CHOICE_DEF] >>
               fs[Abbr‘G0'’] >> metis_tac[]) >>
            ‘FINITE ps’
              by (‘FINITE {{x' | x' ∈ Σ ∧ f = ST x x'} | f ∈ G0'} /\
                   ps = IMAGE CHOICE {{x' | x' ∈ Σ ∧ f = ST x x'} | f ∈ G0'}’
                    suffices_by metis_tac[IMAGE_FINITE] >>
                  rw[Once EXTENSION,EQ_IMP_THM,IMAGE_DEF,Abbr‘ps’] (* 3 *)
                  >- (‘{{x' | x' ∈ Σ ∧ f = ST x x'} | f ∈ G0'} =
                       IMAGE (\f. {x' | x' ∈ Σ ∧ f = ST x x'}) G0' /\
                       FINITE G0'’ suffices_by metis_tac[IMAGE_FINITE] >>
                      rw[IMAGE_DEF,Once EXTENSION,Abbr‘G0'’] >>
                      qabbrev_tac ‘a = fR (Fn 0 []) (fV x)’ >>
                      fs[INSERT_DELETE]
                     )
                  >> metis_tac[]
                 ) >>
            ‘∃x. (x ∈ M.frame.world ∧ M.frame.rel w x) ∧
                 ∀form. form ∈ ps ⇒ satis M x form’ by metis_tac[] >>
            qexists_tac ‘\n. x'’ >> rw[fsatis_def] (* 5 *)
            >- (rw[Abbr‘MA’] >> rw[IMAGE_DEF,SUBSET_DEF,mm2folm_def])
            >- fs[IMAGE_DEF,SUBSET_DEF,Abbr‘MA’,valuation_def,mm2folm_def]
            >- (fs[] >> rw[feval_def,termval_def,Abbr‘MA’,
                           valuation_def,mm2folm_def])
            >- (‘IMAGE (λn. x') 𝕌(:num) ⊆ MA.Dom’
                  by (rw[Abbr‘MA’] >> rw[IMAGE_DEF,SUBSET_DEF,mm2folm_def]) >>
                rw[valuation_def] >> fs[IMAGE_DEF,SUBSET_DEF])
            >- (‘∃t. phi = ST x t ∧ t ∈ ps’
                  by
                  (fs[Abbr‘G0'’] (*2*)
                   >- metis_tac[]
                   >- (‘phi IN Σ'’ by fs[SUBSET_DEF] >>
                       fs[Abbr‘ps’,Abbr‘Σ'’] (* 2 *)
                       >- fs[] >>
                       fs[PULL_EXISTS] >>
                       qexists_tac ‘ST x x''’ >>
                       rw[] >>
                       ‘CHOICE {x' | x' ∈ Σ ∧ ST x x'' = ST x x'} IN
                           {x' | x' ∈ Σ ∧ ST x x'' = ST x x'}’
                         suffices_by fs[] >>
                       ‘{x' | x' ∈ Σ ∧ ST x x'' = ST x x'} <> {}’
                         suffices_by metis_tac[CHOICE_DEF] >>
                       rw[GSYM MEMBER_NOT_EMPTY] >> metis_tac[])
                  ) >>
                ‘satis M x' t’ by metis_tac[] >>
                ‘(λn. x') x = x'’ by fs[] >>
                ‘IMAGE (λn. x') 𝕌(:num) ⊆ M.frame.world’
                  by fs[Abbr‘MA’,mm2folm_def,IMAGE_DEF,SUBSET_DEF] >>
                imp_res_tac prop_2_47_i >>
                ‘satis M ((λn. x') x) t’ by metis_tac[] >>
                ‘fsatis (mm2folm M) (λn. x') (ST x t)’ by fs[] >>
                ‘feval (mm2folm M) (λn. x') phi <=>
                 feval MA (λn. x') phi’
                  suffices_by metis_tac[fsatis_def] >>
                ‘!phi. form_functions (ST x phi) = {}’
                  by metis_tac[ST_form_functions_EMPTY] >>
                ‘!phi. form_functions phi = {} ==>
                       !M1 M2 σ. M1.Dom = M2.Dom /\
                                 M1.Pred = M2.Pred ==>
                                 (feval M1 σ phi <=> feval M2 σ phi)’
                  by metis_tac[form_functions_EMPTY_feval] >>
                ‘(mm2folm M).Dom = MA.Dom’ by fs[mm2folm_def,Abbr‘MA’] >>
                ‘(mm2folm M).Pred = MA.Pred’ by fs[mm2folm_def,Abbr‘MA’] >>
                metis_tac[]))
        >- (‘!f. f IN G0 ==> f IN (IMAGE (ST x) Σ)’
              by (rpt strip_tac >>
                  ‘f IN Σ'’ by fs[SUBSET_DEF] >> fs[Abbr‘Σ'’] (* 2 *)
                  >- fs[] >- metis_tac[]) >>
            fs[satisfiable_in_def] >>
            qabbrev_tac
            ‘ps =
             {CHOICE {x' | x' IN Σ /\ f = ST x x'} |
             f IN G0}’ >>
            ‘!f. f IN G0
                 ==> {x' | x' IN Σ /\ f = ST x x'} <> {}’
              by
              (rw[] >> rfs[Abbr‘Σ'’,IMAGE_DEF] >> rw[GSYM MEMBER_NOT_EMPTY] >>
               metis_tac[]) >>
            ‘ps SUBSET Σ’
              by
              (rw[SUBSET_DEF,Abbr‘ps’] >>
               ‘CHOICE {x' | x' ∈ Σ ∧ f = ST x x'} IN
                  {x' | x' ∈ Σ ∧ f = ST x x'}’
                 suffices_by fs[] >>
               ‘{x' | x' ∈ Σ ∧ f = ST x x'} <> {}’
                 suffices_by metis_tac[CHOICE_DEF] >>
               metis_tac[]) >>
            ‘FINITE ps’
              by (‘FINITE {{x' | x' ∈ Σ ∧ f = ST x x'} | f ∈ G0} /\
                   ps = IMAGE CHOICE {{x' | x' ∈ Σ ∧ f = ST x x'} | f ∈ G0}’
                    suffices_by metis_tac[IMAGE_FINITE] >>
                  rw[Once EXTENSION,EQ_IMP_THM,IMAGE_DEF,Abbr‘ps’] (* 3 *)
                  >- (‘{{x' | x' ∈ Σ ∧ f = ST x x'} | f ∈ G0} =
                       IMAGE (\f. {x' | x' ∈ Σ ∧ f = ST x x'}) G0 /\
                       FINITE G0’ suffices_by metis_tac[IMAGE_FINITE] >>
                      rw[IMAGE_DEF,Once EXTENSION])
                  >> metis_tac[]
                 ) >>
            ‘∃x. (x ∈ M.frame.world ∧ M.frame.rel w x) ∧
                 ∀form. form ∈ ps ⇒ satis M x form’ by metis_tac[] >>
            qexists_tac ‘\n. x'’ >> rw[fsatis_def] (* 3 *)
            >- (rw[Abbr‘MA’] >> rw[IMAGE_DEF,SUBSET_DEF,mm2folm_def])
            >- fs[IMAGE_DEF,SUBSET_DEF,Abbr‘MA’,valuation_def,mm2folm_def]
            >- (‘∃t. phi = ST x t ∧ t ∈ ps’
                  by
                  (‘phi IN Σ'’ by fs[SUBSET_DEF] >>
                   fs[Abbr‘ps’,Abbr‘Σ'’] (* 2 *)
                   >- fs[] >>
                   fs[PULL_EXISTS] >>
                   qexists_tac ‘ST x x''’ >>
                   rw[] >>
                   ‘CHOICE {x' | x' ∈ Σ ∧ ST x x'' = ST x x'} IN
                      {x' | x' ∈ Σ ∧ ST x x'' = ST x x'}’ suffices_by fs[] >>
                   ‘{x' | x' ∈ Σ ∧ ST x x'' = ST x x'} <> {}’
                     suffices_by metis_tac[CHOICE_DEF] >>
                   rw[GSYM MEMBER_NOT_EMPTY] >> metis_tac[]) >>
                ‘satis M x' t’ by metis_tac[] >>
                ‘(λn. x') x = x'’ by fs[] >>
                ‘IMAGE (λn. x') 𝕌(:num) ⊆ M.frame.world’
                  by fs[Abbr‘MA’,mm2folm_def,IMAGE_DEF,SUBSET_DEF] >>
                imp_res_tac prop_2_47_i >>
                ‘satis M ((λn. x') x) t’ by metis_tac[] >>
                ‘fsatis (mm2folm M) (λn. x') (ST x t)’ by fs[] >>
                ‘feval (mm2folm M) (λn. x') phi <=>
                 feval MA (λn. x') phi’
                  suffices_by metis_tac[fsatis_def] >>
                ‘!phi. form_functions (ST x phi) = {}’
                  by metis_tac[ST_form_functions_EMPTY] >>
                ‘!phi. form_functions phi = {} ==>
                       !M1 M2 σ. M1.Dom = M2.Dom /\
                                 M1.Pred = M2.Pred ==>
                                 (feval M1 σ phi <=> feval M2 σ phi)’
                  by metis_tac[form_functions_EMPTY_feval] >>
                ‘(mm2folm M).Dom = MA.Dom’ by fs[mm2folm_def,Abbr‘MA’] >>
                ‘(mm2folm M).Pred = MA.Pred’ by fs[mm2folm_def,Abbr‘MA’] >>
                metis_tac[]))) >>
  ‘FINITE {w}’ by fs[] >>
  ‘CARD {w} <= 1’ by fs[] >>
  ‘{w} SUBSET (mm2folm M).Dom’ by fs[SUBSET_DEF,mm2folm_def] >>
  ‘MA = expand (mm2folm M) {w} (\n.w)’
    by rw[expand_def,folModelsTheory.model_component_equality,mm2folm_def,
          Abbr‘MA’,FUN_EQ_THM]  >>
(*
`expansion (mm2folm M) {w} MA (\n.w)`
  by (rw[expansion_def] (* 4 *)
      >- fs[mm2folm_def,Abbr`MA`]
      >- fs[BIJ_DEF,INJ_DEF,SURJ_DEF,Abbr`MA`]
      >- (fs[BIJ_DEF,INJ_DEF,SURJ_DEF,Abbr`MA`] >> simp[FUN_EQ_THM] >> rw[] >>
          fs[])
      >- fs[mm2folm_def,Abbr`MA`]) >>*)
  ‘ftype x Σ'’
    by (rw[ftype_def,SUBSET_DEF] >> fs[Abbr‘Σ'’] (* 2 *)
        >- (‘FV (fR (Fn 0 []) (fV x)) = {x}’
              by rw[FV_def,FVT_def] >>
            ‘x'' IN {x}’ by metis_tac[] >> fs[])
        >- (‘FV (ST x x''') SUBSET {x}’ by metis_tac[ST_FV_singleton] >>
            ‘x'' IN {x}’ by metis_tac[SUBSET_DEF] >> fs[])) >>
  ‘frealizes MA x Σ'’
    by (rw[] >> first_x_assum irule >> rw[] (* 3 *)
        (*map_every qexists_tac [`{w}`,`\n.w`,`1`] >> rw[]*) (* 4 *)
        >- (Cases_on ‘phi = fR (Fn 0 []) (fV x)’ (* 2 *)
            >- fs[form_functions_def,FST] >>
            fs[Abbr‘Σ'’] >>
            metis_tac[ST_form_functions_EMPTY,MEMBER_NOT_EMPTY,SUBSET_DEF])
        >- rw[SUBSET_DEF,mm2folm_def,IMAGE_DEF]
        >- rw[BIJ_DEF,INJ_DEF,SURJ_DEF]
       ) >>
  fs[frealizes_def] >>
  rw[satisfiable_in_def] (* 2 *)
  >- rw[SUBSET_DEF]
  >- (qexists_tac ‘w'’ >> rw[] (* 3 *)
      >- fs[expand_def,mm2folm_def]
      >- (‘(fR (Fn 0 []) (fV x)) IN Σ'’ by fs[Abbr‘Σ'’] >>
          ‘IMAGE (\n. w') univ(:num) ⊆ (expand (mm2folm M) {w} (λn. w)).Dom’
            by fs[SUBSET_DEF,IMAGE_DEF,expand_def,mm2folm_def] >>
          ‘fsatis (expand (mm2folm M) {w} (λn. w)) ((x =+ w') (λn. w'))
                  (fR (Fn 0 []) (fV x))’
            by metis_tac[] >>
          fs[fsatis_def,feval_def,APPLY_UPDATE_THM,termval_def,expand_def,
             mm2folm_def])
      >- (‘IMAGE (\n. w') univ(:num) ⊆ (expand (mm2folm M) {w} (λn. w)).Dom’
            by fs[SUBSET_DEF,IMAGE_DEF,expand_def,mm2folm_def] >>
          ‘(ST x form) IN Σ'’ by fs[Abbr‘Σ'’] >>
          ‘fsatis (expand (mm2folm M) {w} (λn. w)) ((x =+ w') (λn. w'))
                  (ST x form)’ by metis_tac[] >>
          ‘(IMAGE ((x =+ w') (λn. w')) univ(:num)) SUBSET M.frame.world’
            by (rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on ‘x'' = x’ (* 2 *) >> rw[] >>
                fs[APPLY_UPDATE_THM,expand_def,mm2folm_def]) >>
          ‘fsatis (mm2folm M) ((x =+ w') (λn. w')) (ST x form)’
            by (rw[fsatis_def] (* 2 *)
                >- (rw[mm2folm_def,valuation_def] >>
                    fs[SUBSET_DEF,IMAGE_DEF] >>
                    metis_tac[]) >>
                ‘feval (expand (mm2folm M) {w} (λn. w)) (λn. w')⦇x ↦ w'⦈
                       (ST x form) <=>
                 feval (mm2folm M) (λn. w')⦇x ↦ w'⦈ (ST x form)’
                  suffices_by metis_tac[fsatis_def] >>
                irule holds_functions >> rw[] (* 3 *)
                >- (qpat_x_assum ‘_ = expand _ {w} _’ (assume_tac o SYM) >>
                    simp[])
                >- (‘form_functions (ST x form) = {}’
                      suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
                    metis_tac[L1tau_def,ST_L1tau])
                >- (qpat_x_assum ‘_ = expand _ {w} _’ (assume_tac o SYM) >>
                    simp[])) >>
          ‘(x =+ w') (λn. w') x = w'’ by fs[APPLY_UPDATE_THM] >>
          metis_tac[prop_2_47_i]))
QED

val thm_2_65_corollary = store_thm(
  "thm_2_65_corollary",
  ``∀M M' w:'b w':'c.
       countably_saturated (mm2folm M) /\ countably_saturated (mm2folm M') ∧ w ∈ M.frame.world ∧ w' ∈ M'.frame.world ⇒
       modal_eq M M' w w' ⇒
       bisim_world M M' w w'``,
   rw[] >> `M_sat M /\ M_sat M'` by metis_tac[thm_2_65] >> metis_tac[prop_2_54_DIST_TYPE]);




Theorem thm_2_74_half1:
  !M N w v. w IN M.frame.world /\ v IN N.frame.world ==>
         !U I MS NS. ultrafilter U I /\
                     (!i. i IN I ==> MS i = M) /\
                     (!i. i IN I ==> NS i = N) ==>
               bisim_world (ultraproduct_model U I MS) (ultraproduct_model U I NS)
                           {fw | Uequiv U I (models2worlds MS) (λi. w) fw}
                           {fv | Uequiv U I (models2worlds NS) (λi. v) fv}
                   ==> (!phi. satis M w phi <=> satis N v phi)
Proof
  rw[] >> drule prop_2_71 >> rw[] >> last_x_assum (qspec_then `U` assume_tac) >>
  first_x_assum (qspecl_then [`phi`,`v`] assume_tac) >> first_x_assum drule >> rw[] >>
  `∀phi w.
             satis (ultraproduct_model U I' MS)
               {fw | Uequiv U I' (models2worlds MS) (λi. w) fw} phi ⇔
             satis M w phi` by metis_tac[prop_2_71] >>
  first_x_assum (qspecl_then [`phi`,`w`] assume_tac) >> drule thm_2_20_lemma >>
  metis_tac[]
QED


Theorem thm_2_74_half2:
  !(M: α modalBasics$model) N w v. (w IN M.frame.world /\ v IN N.frame.world /\
            (!phi. satis M w phi <=> satis N v phi)) ==>
             ?U (I:num -> bool). ultrafilter U I /\
               bisim_world (ultraproduct_model U I (\i. M)) (ultraproduct_model U I (\i. N))
                           {fw | Uequiv U I (models2worlds (\i. M)) (λi. w) fw}
                           {fv | Uequiv U I (models2worlds (\i. N)) (λi. v) fv}
Proof
rw[] >>
`∃U. ultrafilter U 𝕌(:num) ∧ ∀s. FINITE s ⇒ s ∉ U`
  by metis_tac[exercise_2_5_4_b] >>
`!n. {n} NOTIN U` by fs[] >>
drule example_2_72 >> rw[] >>
map_every qexists_tac [`U`,`univ(:num)`] >> rw[] >>
irule thm_2_65_corollary >> rw[] (* 5 *)
>- (irule lemma_2_73 >> rw[] >> metis_tac[MEMBER_NOT_EMPTY])
>- (irule lemma_2_73 >> rw[] >> metis_tac[MEMBER_NOT_EMPTY])
>- (`!i. i IN 𝕌(:num) ==> (\i. M) i = M` by fs[] >>
    `{fw | Uequiv U 𝕌(:num) (models2worlds (λi. M)) (λi. w) fw} ∈
     (ultraproduct_model U 𝕌(:num) (λi. M)).frame.world <=> w IN M.frame.world`
      suffices_by metis_tac[] >> irule ultraproduct_world_constant >> rw[])
>- (`!i. i IN 𝕌(:num) ==> (\i. N) i = N` by fs[] >>
    `{fv | Uequiv U 𝕌(:num) (models2worlds (λi. N)) (λi. v) fv} ∈
     (ultraproduct_model U 𝕌(:num) (λi. N)).frame.world <=> v IN N.frame.world`
      suffices_by metis_tac[] >> irule ultraproduct_world_constant >> rw[])
>- (rw[modal_eq_tau] >>
    `!i. i IN 𝕌(:num) ==> (\i. M) i = M` by fs[] >>
    drule prop_2_71 >> rw[] >>
    `!i. i IN 𝕌(:num) ==> (\i. N) i = N` by fs[] >>
    drule prop_2_71 >> rw[])
QED

(*detour lemma 2.74 2.62*)


Theorem ST_CONJ:
ST x (AND f1 f2) = fAND (ST x f1) (ST x f2)
Proof
rw[ST_def,fAND_def,AND_def]
QED


Theorem ST_BIGCONJ:
!s.
   FINITE s ==>
    !x.
      (!f. f IN s ==> ?phi. f = ST x phi) ==>
       ?cf. (!M σ. IMAGE σ (univ(:num)) ⊆ M.Dom ==>
                  (feval M σ cf <=>
                   (!f. f IN s ==> feval M σ f))) /\
           ?psi. cf = ST x psi
Proof
Induct_on `FINITE` >> rw[] (* 2 *)
>- (qexists_tac `True` >> rw[True_def,fNOT_def,feval_def] >>
    qexists_tac `NOT FALSE` >> rw[ST_def,fNOT_def]) >>
`(∀f. f ∈ s ⇒ ∃phi. f = ST x phi)` by metis_tac[] >>
first_x_assum drule >> rw[] >>
`∃phi. e = ST x phi` by metis_tac[] >>
qexists_tac `fAND (ST x phi) (ST x psi)` >> rw[EQ_IMP_THM] (* 3 *)
>- rw[]
>- metis_tac[] >>
metis_tac[ST_CONJ]
QED

Theorem ST_fNOT:
ST x (NOT f) = fNOT (ST x f)
Proof
rw[ST_def,fNOT_def,Not_def]
QED


Theorem termval_IN_ultraproduct_Dom':
∀U I MS.
    ultrafilter U I ⇒
     (∀n0 l0 i. i IN I ==> (MS i).Fun n0 l0 ∈ (MS i).Dom) ==>
         ∀σ.
             IMAGE σ 𝕌(:num) ⊆ ultraproduct U I (folmodels2Doms MS) ⇒
             ∀a.
                 termval (ultraproduct_folmodel U I MS) σ a ∈
                 ultraproduct U I (folmodels2Doms MS)
Proof
rw[] >>
`ultraproduct U I' (folmodels2Doms MS) =
 (ultraproduct_folmodel U I' MS).Dom`
 by fs[ultraproduct_folmodel_def] >>
rw[] >> irule termval_IN_Dom >> rw[] (* 2 *)
>- metis_tac[ultraproduct_folmodel_well_formed] >>
fs[ultraproduct_folmodel_def]
QED

Theorem folmodels2Doms_models2worlds_folm2mm:
!MS. (folmodels2Doms MS) = (models2worlds (λi. folm2mm (MS i)))
Proof
rw[folmodels2Doms_def,models2worlds_def,folm2mm_def,FUN_EQ_THM]
QED


Theorem ultraproduct_comm_termval':
  !t U I MS. ultrafilter U I ==> term_functions t = {} ==>
      !σ. (termval (ultraproduct_folmodel U I MS) σ t =
           termval (mm2folm (ultraproduct_model U I (λi. folm2mm (MS i)))) σ t)
Proof
 Cases_on `t` >> rw[termval_def]
QED


Theorem ultraproduct_comm_feval':
!phi U I MS.
  ultrafilter U I ==>
  form_functions phi = {} ==>
  (!i n. i IN I ==> (MS i).Pred n [] = F) ==>
  (!i a b n. i IN I ==> (MS i).Pred n [a; b] ==> n = 0) ==>
  (!i a b c d n. i IN I ==> (MS i).Pred n (a:: b :: c :: d) = F) ==>
  (∀n0 l0 i. i IN I ==> (MS i).Fun n0 l0 ∈ (MS i).Dom) ==>
  !σ.
     IMAGE σ (univ(:num)) ⊆ ultraproduct U I (folmodels2Doms MS) ==>
     (feval (ultraproduct_folmodel U I MS) σ phi <=>
      feval (mm2folm (ultraproduct_model U I (λi. folm2mm (MS i)))) σ phi)
Proof
Induct_on `phi` (* 4 *)
>- fs[feval_def]
>- (rw[feval_def] >>
    `MAP (termval (ultraproduct_folmodel U I' MS) σ) l =
     MAP (termval
           (mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))) σ) l`
     by
      (irule MAP_CONG >> rw[] >> irule ultraproduct_comm_termval' >> rw[] >>
       SPOSE_NOT_THEN ASSUME_TAC >> fs[GSYM MEMBER_NOT_EMPTY] >>
       `x' IN LIST_UNION (MAP term_functions l)`
         suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
       simp[IN_LIST_UNION] >> qexists_tac `term_functions x` >>
       rw[MEM_MAP] >> metis_tac[]) >>
    rw[] >>
    qabbrev_tac
      `mapl =
        MAP (termval
             (mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))) σ) l` >>
    Cases_on `mapl = []` (* 2 *)
    >- (fs[] >>
        rw[mm2folm_def,ultraproduct_folmodel_def,
           folm2mm_def,ultraproduct_model_def] >>
        `{i | i ∈ I' ∧ (MS i).Pred n []} = {}`
          suffices_by metis_tac[EMPTY_NOTIN_ultrafilter] >>
        rw[Once EXTENSION] >> metis_tac[])
    >- (`(?a. l = [a]) \/
         (?a b. l = [a;b]) \/
         (?a b c d. l = a :: b :: c :: d)`
          by
           (Cases_on `l` >> fs[Abbr‘mapl’] >>
            Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[]) (* 3 *)
        >- (rw[] >>
            qabbrev_tac
             `sl = termval (ultraproduct_folmodel U I' MS) σ a` >>
            rw[mm2folm_def,
               ultraproduct_folmodel_def,ultraproduct_model_def] >>
            `sl ∈ ultraproduct U I' (models2worlds (λi. folm2mm (MS i)))`
             by
              (rw[Abbr`sl`] >> drule termval_IN_ultraproduct_Dom' >>
               rw[] >>
               metis_tac[folmodels2Doms_models2worlds_folm2mm]) >>
            (*remove the conj first*)
           `sl <> {}` by metis_tac[ultraproduct_eqclass_non_empty] >>
           `CHOICE sl IN sl` by metis_tac[CHOICE_DEF] >>
           `{i | i ∈ I' ∧ (MS i).Pred n [CHOICE sl i]} =
            {i | i ∈ I' ∧ CHOICE sl i ∈ (folm2mm (MS i)).valt n}`
             by (rw[EXTENSION,EQ_IMP_THM,folm2mm_def] >>
                 drule ultraproduct_val_IN_A >> rw[] >>
                 first_x_assum
                   (qspecl_then [`models2worlds (λi. folm2mm (MS i))`,
                                 `sl`,`CHOICE sl`,`x`] assume_tac) >>
                 `(models2worlds (λi. folm2mm (MS i))) x = (MS x).Dom`
                   by rw[models2worlds_def,folm2mm_def] >>
                 fs[]) >>
           rw[EQ_IMP_THM] >- metis_tac[] >>
           `{i | i IN I' /\ f i = (CHOICE sl) i} IN U`
             by
              (irule ultraproduct_same_eqclass >> rw[] >>
               map_every qexists_tac
                [`models2worlds (λi. folm2mm (MS i))`,`sl`] >>
               rw[]) >>
           `({i | i ∈ I' ∧ f i ∈ (folm2mm (MS i)).valt n} ∩
             {i | i ∈ I' ∧ f i = CHOICE sl i}) IN U`
             by metis_tac[ultrafilter_INTER] >>
           irule ultrafilter_SUBSET' >> rw[PULL_EXISTS] (* 2 *)
           >- (qexists_tac
                 `{i | i ∈ I' ∧ f i ∈ (folm2mm (MS i)).valt n} ∩
                  {i | i ∈ I' ∧ f i = CHOICE sl i}` >>
               rw[SUBSET_DEF] >> metis_tac[]) >>
           qexists_tac `I'` >> rw[SUBSET_DEF]
           ) (*1 out of 3*)
        >- (rw[] >>
            qabbrev_tac
             `sl1 = termval (ultraproduct_folmodel U I' MS) σ a` >>
            qabbrev_tac
             `sl2 = termval (ultraproduct_folmodel U I' MS) σ b` >>
            rw[mm2folm_def,ultraproduct_folmodel_def,ultraproduct_model_def] >>
            `{i | i ∈ I' ∧ (MS i).Pred n [CHOICE sl1 i; CHOICE sl2 i]} ∈ U ==>
             n = 0`
              by
               (rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
                `{i | i ∈ I' ∧ (MS i).Pred n [CHOICE sl1 i; CHOICE sl2 i]} = {}`
                  by
                   (rw[EXTENSION] >> metis_tac[]) >>
                metis_tac[EMPTY_NOTIN_ultrafilter]) >>
            `sl1 ∈ ultraproduct U I' (models2worlds (λi. folm2mm (MS i))) ∧
             sl2 ∈ ultraproduct U I' (models2worlds (λi. folm2mm (MS i)))`
              by
               (`!t. (termval (ultraproduct_folmodel U I' MS) σ t) IN
                 ultraproduct U I' (models2worlds (λi. folm2mm (MS i)))`
                  suffices_by metis_tac[] >>
                drule termval_IN_ultraproduct_Dom' >>
                rw[] >>
                metis_tac[folmodels2Doms_models2worlds_folm2mm]) >>
            `sl1 <> {}` by metis_tac[ultraproduct_eqclass_non_empty] >>
            `sl2 <> {}` by metis_tac[ultraproduct_eqclass_non_empty] >>
            `CHOICE sl1 IN sl1 /\ CHOICE sl2 IN sl2` by metis_tac[CHOICE_DEF]>>
            rw[EQ_IMP_THM,EXTENSION] (* 2 *)
            >- (map_every qexists_tac [`CHOICE sl1`,`CHOICE sl2`] >>
                rw[] >>
                `n = 0` by metis_tac[] >>
                `!i. i IN I' ==> CHOICE sl1 i ∈ (MS i).Dom /\
                 CHOICE sl2 i ∈ (MS i).Dom`
                  by
                   (drule ultraproduct_val_IN_A >>
                    `!x. models2worlds (λi. folm2mm (MS i)) x = (MS x).Dom`
                      by rw[models2worlds_def,folm2mm_def] >>
                    metis_tac[CHOICE_DEF,ultraproduct_eqclass_non_empty]) >>
                rw[folm2mm_def] >>
                `{i | i ∈ I' ∧ (MS i).Pred 0 [CHOICE sl1 i; CHOICE sl2 i]} =
                 {i | i ∈ I' ∧ (MS i).Pred 0 [CHOICE sl1 i; CHOICE sl2 i] ∧
                   CHOICE sl1 i ∈ (MS i).Dom ∧ CHOICE sl2 i ∈ (MS i).Dom}`
                  by rw[EXTENSION,EQ_IMP_THM] >>
                metis_tac[]) >>
            qmatch_abbrev_tac `ss IN U` >>
            irule ultrafilter_INTER_INTER_SUBSET >>
            `ss ⊆ I'` by fs[Abbr`ss`,SUBSET_DEF,INTER_DEF] >> rw[] (* 2 *)
            >- (map_every qexists_tac
                 [`{i | i IN I' /\ f i = (CHOICE sl1) i}`,
                  `{i | i IN I' /\ g i = (CHOICE sl2) i}`,
                  `{i | i ∈ I' ∧ (folm2mm (MS i)).frame.rel (f i) (g i)}`] >>
                rw[SUBSET_DEF,folm2mm_def] (* 3 *)
                >- (irule ultraproduct_same_eqclass >> rw[] >>
                    map_every qexists_tac
                    [`models2worlds (λi. folm2mm (MS i))`,`sl1`] >>
                    rw[])
                >- (irule ultraproduct_same_eqclass >> rw[] >>
                    map_every qexists_tac
                    [`models2worlds (λi. folm2mm (MS i))`,`sl2`] >>
                    rw[]) >>
                fs[Abbr`ss`] >> metis_tac[]) >>
            qexists_tac `I'` >> rw[SUBSET_DEF])
        >- (`(mm2folm
              (ultraproduct_model U I' (λi. folm2mm (MS i)))).Pred n mapl = F`
              by rw[mm2folm_def] >>
            `(ultraproduct_folmodel U I' MS).Pred n mapl = F`
              by
              (`{i | i ∈ I' ∧ (MS i).Pred n (MAP (λfc. CHOICE fc i) mapl)} NOTIN
                  U`
                 suffices_by fs[ultraproduct_folmodel_def] >>
               `{i | i ∈ I' ∧ (MS i).Pred n (MAP (λfc. CHOICE fc i) mapl)} = {}`
                 suffices_by metis_tac[EMPTY_NOTIN_ultrafilter] >>
               rw[Once EXTENSION] >> metis_tac[]) >>
            metis_tac[])
    )
   )
>- (rw[] >> metis_tac[])
>- (rw[feval_def,EQ_IMP_THM] (* 2 *)
    >- (first_x_assum drule >> rw[] >>
        `IMAGE σ⦇n ↦ a⦈ 𝕌(:num) ⊆ ultraproduct U I' (folmodels2Doms MS)`
          by (irule IMAGE_UPDATE >>
              `(mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))).Dom =
               ultraproduct U I' (folmodels2Doms MS)`
               by
                (rw[mm2folm_def,ultraproduct_model_def] >>
                 `(models2worlds (λi. folm2mm (MS i))) = (folmodels2Doms MS)`
                   suffices_by metis_tac[] >>
                 rw[FUN_EQ_THM,models2worlds_def,
                    folm2mm_def,folmodels2Doms_def]) >>
              metis_tac[]) >>
        first_x_assum drule >> rw[] >>
        `(ultraproduct_folmodel U I' MS).Dom =
         (mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))).Dom`
          suffices_by metis_tac[] >>
        rw[ultraproduct_folmodel_def,mm2folm_def,ultraproduct_model_def] >>
        metis_tac[folmodels2Doms_models2worlds_folm2mm])
    >- (first_x_assum drule >> rw[] >>
        `IMAGE σ⦇n ↦ a⦈ 𝕌(:num) ⊆ ultraproduct U I' (folmodels2Doms MS)`
          by (irule IMAGE_UPDATE >> rw[] >> fs[ultraproduct_folmodel_def]) >>
        `(ultraproduct_folmodel U I' MS).Dom =
         (mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))).Dom`
          suffices_by metis_tac[] >>
        rw[ultraproduct_folmodel_def,mm2folm_def,ultraproduct_model_def] >>
        metis_tac[folmodels2Doms_models2worlds_folm2mm])
    )
QED



Theorem detour_embedding_lemma:
!M σ a I U x MS.
   (FV a ⊆ {x} /\ form_functions a = ∅ /\
    ultrafilter U I /\
    (∀ff ll. M.Fun ff ll ∈ M.Dom) /\
    (∀n. M.Pred n [] ⇔ F) /\
    (∀a b n. M.Pred n [a; b] ⇒ n = 0) /\
    (∀a b c d n. (M.Pred n (a::b::c::d) ⇔ F)) /\
    IMAGE σ (univ(:num)) ⊆ M.Dom) ==>
    (feval M σ a <=>
     feval (mm2folm (ultraproduct_model U I (λi. folm2mm M)))
       (λx. {fw | Uequiv U I (models2worlds (λi. folm2mm M)) (λi. σ x) fw}) a)
Proof
rw[] >>
drule (corollary_A_21 |> INST_TYPE [alpha |-> ``:'b``,beta |-> ``:'a``]) >>
rw[] >>
first_x_assum
  (qspecl_then [`\i.M`,`M`,`σ`,`a`] assume_tac) >>
fs[] >>
`(∀i ff ll. i ∈ I' ⇒ M.Fun ff ll ∈ M.Dom)` by metis_tac[] >>
first_x_assum drule_all >> rw[] >>
drule
  (ultraproduct_comm_feval'|> INST_TYPE [alpha |-> ``:'b``,beta |-> ``:'a``])>>
rw[] >>
first_x_assum
  (qspecl_then
    [`a`,`\i.M`,
     `(λx. {g | Uequiv U I' (folmodels2Doms (λi. M)) g (λi. σ x)})`]
   assume_tac) >>
rfs[] >>
`IMAGE (λx. {g | Uequiv U I' (folmodels2Doms (λi. M)) g (λi. σ x)})
          𝕌(:num) ⊆ ultraproduct U I' (folmodels2Doms (λi. M))`
  by
   (rw[SUBSET_DEF,ultraproduct_def,partition_def] >>
    qexists_tac `\i. σ x''` >>
    rw[] (* 2 *)
    >- (rw[Cart_prod_def,folmodels2Doms_def] >>
        fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
    >- (rw[EXTENSION,Uequiv_def,EQ_IMP_THM] (* 2 same *) >>
        `{i | i ∈ I' ∧ x' i = σ x''} =
         {i | i ∈ I' ∧ σ x'' = x' i}`
          by (rw[EXTENSION,EQ_IMP_THM] >> metis_tac[]) >>
        metis_tac[])
   ) >>
fs[] >>
`(models2worlds (λi. folm2mm M)) = (folmodels2Doms (λi. M))`
  by
   rw[FUN_EQ_THM,models2worlds_def,folmodels2Doms_def,folm2mm_def] >>
rw[] >>
`(λx. {g | Uequiv U I' (folmodels2Doms (λi. M)) g (λi. σ x)}) =
 (λx'. {fw | Uequiv U I' (folmodels2Doms (λi. M)) (λi. σ x') fw})`
  by
   (rw[FUN_EQ_THM,EQ_IMP_THM] (* 2 same *) >>
    qexists_tac `x''` >> rw[] >> metis_tac[Uequiv_SYM]) >>
rw[] >>
`(∀i a b n. i ∈ I' ⇒ M.Pred n [a; b] ⇒ n = 0)`
  by metis_tac[] >>
first_x_assum drule >> rw[]
QED

Theorem mm2folm_folm2mm_termval:
!t.
  term_functions t = {} ==>
   !σ.
      IMAGE σ univ(:num) ⊆ M.Dom ==>
       termval (mm2folm (folm2mm M)) σ t = termval M σ t
Proof
 rw[] >> Cases_on `t` >> fs[term_functions_def] >> rw[termval_def,mm2folm_def,folm2mm_def]
QED

Theorem mm2folm_folm2mm_feval:
∀f. form_functions f = ∅ ⇒
  ∀σ. IMAGE σ 𝕌(:num) ⊆ M.Dom ⇒
      (∀n. M.Pred n [] ⇔ F) ==>
      (∀a b n. M.Pred n [a; b] ⇒ n = 0) ==>
      (∀a b c d n. (M.Pred n (a::b::c::d) ⇔ F)) ==>
           (feval (mm2folm (folm2mm M)) σ f ⇔ feval M σ f)
Proof
Induct_on `f` (* 4 *)
>- rw[feval_def]
>- (rw[feval_def] >>
    qabbrev_tac `tv = (termval (mm2folm (folm2mm M)) σ)` >>
    rw[mm2folm_def,folm2mm_def] >> Cases_on `l` (*2 *)
    >- fs[] >>
    Cases_on `t` (*2 *)
    >- (fs[] >> Cases_on `h` >> fs[term_functions_def] >>
        rw[Abbr`tv`,mm2folm_folm2mm_termval] >>
        fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
    fs[] >>
    Cases_on `t'` (* 2 *)
    >- (fs[] >> rw[EQ_IMP_THM] (* 7 *)
        >- (fs[Abbr`tv`,mm2folm_folm2mm_termval] >>
            metis_tac[mm2folm_folm2mm_termval])
        >- metis_tac[]
        >- (fs[Abbr`tv`,mm2folm_folm2mm_termval] >>
            metis_tac[mm2folm_folm2mm_termval])
        >- (Cases_on `h` >>
            fs[term_functions_def,Abbr`tv`,IMAGE_DEF,SUBSET_DEF] >>
            metis_tac[])
        >- (Cases_on `h'` >>
            fs[term_functions_def,Abbr`tv`,IMAGE_DEF,SUBSET_DEF] >>
            metis_tac[])
        >- (Cases_on `h` >>
            fs[term_functions_def,Abbr`tv`,IMAGE_DEF,SUBSET_DEF] >>
            metis_tac[])
        >- (Cases_on `h'` >>
            fs[term_functions_def,Abbr`tv`,IMAGE_DEF,SUBSET_DEF] >>
            metis_tac[])) >>
    fs[])
>- (rw[feval_def] >> metis_tac[]) >>
rw[feval_def,EQ_IMP_THM]
>- (`(mm2folm (folm2mm M)).Dom = M.Dom` by fs[mm2folm_def,folm2mm_def] >>
    first_x_assum drule >> rw[] >>
    `IMAGE σ(|n |-> a|) 𝕌(:num) ⊆ M.Dom`
      by (irule IMAGE_UPDATE >> rw[]) >>
    metis_tac[]) >>
`(mm2folm (folm2mm M)).Dom = M.Dom` by fs[mm2folm_def,folm2mm_def] >>
`IMAGE σ(|n |-> a|) 𝕌(:num) ⊆ M.Dom`
  by (irule IMAGE_UPDATE >> fs[]) >>
metis_tac[]
QED

Theorem ultraproduct_mm2folm_folm2mm_comm_feval:
!M σ a I U.
   (FV a ⊆ {x} /\ form_functions a = ∅ /\
    ultrafilter U I /\
    (∀n. ¬M.Pred n []) /\
    (∀a b n. M.Pred n [a; b] ⇒ n = 0) /\
    (∀a b c d n. ¬M.Pred n (a::b::c::d)) /\
    (∀ff ll. M.Fun ff ll ∈ M.Dom) /\
    IMAGE σ (univ(:num)) ⊆ M.Dom) ==>
    (feval M σ a <=>
     feval (mm2folm (ultraproduct_model U I (λi. folm2mm M)))
       (λx. {fw | Uequiv U I (models2worlds (λi. folm2mm M)) (λi. σ x) fw}) a)
Proof
rw[] >>
drule
 (ultraproduct_comm_feval'|> INST_TYPE [alpha |-> ``:'b``,beta |-> ``:'a``])>>
rw[] >>
drule (corollary_A_21 |> INST_TYPE [alpha |-> ``:'b``,beta |-> ``:'a``]) >> rw[] >>
(*apply A_21*)
first_x_assum (qspecl_then [`\i.M`,`M`,`σ`,`a`] assume_tac) >> fs[] >>
last_x_assum
(qspecl_then
  [`a`,`\i.M`,
   `(λx. {g | Uequiv U I' (folmodels2Doms (λi. M)) g (λi. σ x)}) `]
 assume_tac) >>
`IMAGE (λx. {g | Uequiv U I' (folmodels2Doms (λi. M)) g (λi. σ x)})
          𝕌(:num) ⊆ ultraproduct U I' (folmodels2Doms (λi. M))`
  by
   (rw[IMAGE_DEF,SUBSET_DEF,ultraproduct_def,partition_def,Cart_prod_def] >>
    qexists_tac `\i. σ x''` >>
    rw[Uequiv_def,EXTENSION,EQ_IMP_THM,folmodels2Doms_def,Cart_prod_def] >>
    fs[] (* 7 *)
    >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
    >- metis_tac[]
    >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
    >- (`{i | i ∈ I' ∧ x' i = σ x''} = {i | i ∈ I' ∧ σ x'' = x' i}`
         by rw[EXTENSION,EQ_IMP_THM] >> metis_tac[])
    >- metis_tac[]
    >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
    >- (`{i | i ∈ I' ∧ x' i = σ x''} = {i | i ∈ I' ∧ σ x'' = x' i}`
         by rw[EXTENSION,EQ_IMP_THM] >> metis_tac[])
    ) >>
`form_functions a = ∅ ∧ (∀i n. i ∈ I' ⇒ ¬M.Pred n []) ∧
        (∀i a b n. i ∈ I' ⇒ M.Pred n [a; b] ⇒ n = 0) ∧
        (∀i a b c d n. i ∈ I' ⇒ ¬M.Pred n (a::b::c::d)) ∧
        (∀n0 l0 i. i ∈ I' ⇒ M.Fun n0 l0 ∈ M.Dom) ∧
        IMAGE (λx. {g | Uequiv U I' (folmodels2Doms (λi. M)) g (λi. σ x)})
          𝕌(:num) ⊆ ultraproduct U I' (folmodels2Doms (λi. M))`
  by metis_tac[] >>
first_x_assum drule >> rw[] >>
first_x_assum drule >> rw[] >>
irule holds_valuation >> rw[] >>
`x' = x` by fs[SUBSET_DEF] >> fs[] >>
`(folmodels2Doms (λi. M)) = (models2worlds (λi. folm2mm M))`
  by rw[folmodels2Doms_def,models2worlds_def,folm2mm_def,FUN_EQ_THM] >>
rw[EXTENSION,EQ_IMP_THM] >> metis_tac[Uequiv_SYM]
QED



Theorem mm2folm_folm2mm_Pred0:
!M wl.
    (LENGTH wl = 2 /\
        (!w. MEM w wl ==> w IN M.Dom)) ==>
      (mm2folm (folm2mm M)).Pred 0 wl = M.Pred 0 wl
Proof
rw[FUN_EQ_THM,mm2folm_def,folm2mm_def] >>
`?w1 w2. wl = [w1;w2]`
  by (Cases_on `wl` >> fs[LENGTH] >> Cases_on `t` >> fs[LENGTH]) >>
fs[]
QED

Theorem mm2folm_folm2mm_Predn:
!M w n. w IN M.Dom ==>
  (mm2folm (folm2mm M)).Pred n [w] = M.Pred n [w]
Proof
rw[FUN_EQ_THM,mm2folm_def,folm2mm_def]
QED

Theorem mm2folm_folm2mm_term_functions:
!M v a. term_functions a = {} ==>
      termval (mm2folm (folm2mm M)) v a = termval M v a
Proof
rw[term_functions_def,termval_def,mm2folm_def,folm2mm_def] >>
Cases_on `a` >> fs[term_functions_def]
QED

Theorem valuation_termval_functions:
!M t v. (term_functions t = {} /\ valuation M v) ==>
      (termval M v t) IN M.Dom
Proof
rw[] >> Cases_on `t` >> fs[valuation_def,termval_def]
QED

Theorem L1tau_fIMP:
!f1 f2. L1tau (f1 -> f2) <=> (L1tau f1 /\ L1tau f2)
Proof
rw[L1tau_def] >> rw[EQ_IMP_THM]
QED

Theorem L1tau_FALL:
!f n. L1tau (FALL n f) <=> L1tau f
Proof
rw[L1tau_def] >> rw[EQ_IMP_THM]
QED

Theorem L1tau_mm2folm_folm2mm_comm_feval:
∀f. L1tau f ==>
    !M v. valuation M v ==>
          (feval (mm2folm (folm2mm M)) v f ⇔ feval M v f)
Proof
Induct_on `f` (* 4 *)
>- rw[feval_def]
>- (rw[feval_def] >> fs[L1tau_def] (* 2 *)
    >- (`?a b. l = [a;b]`
        by (Cases_on `l` >> fs[LENGTH] >> Cases_on `t` >> fs[]) >>
       fs[] >> rw[mm2folm_folm2mm_term_functions] >>
       `(termval M v a) IN M.Dom /\ (termval M v b) IN M.Dom`
         by metis_tac[valuation_termval_functions] >>
       irule mm2folm_folm2mm_Pred0 >> fs[] >> metis_tac[])
    >- (`?a. l = [a]` by (Cases_on `l` >> fs[LENGTH]) >>
       fs[] >> rw[mm2folm_folm2mm_term_functions] >>
       irule mm2folm_folm2mm_Predn >>
       metis_tac[valuation_termval_functions])
   )
>- fs[feval_def,L1tau_fIMP]
>- (rw[feval_def,L1tau_FALL] >> first_x_assum drule >> rw[] >>
   `(mm2folm (folm2mm M)).Dom = M.Dom` by fs[mm2folm_def,folm2mm_def] >>
   fs[])
QED


Theorem L1tau_ultraproduct_mm2folm_folm2mm_comm_feval:
∀M σ a I U.
            L1tau a ∧ FV a ⊆ {x} ∧ ultrafilter U I ∧ valuation M σ ⇒
            (feval M σ a ⇔
             feval (mm2folm (ultraproduct_model U I (λi. folm2mm M)))
               (λx.
                    {fw |
                     Uequiv U I (models2worlds (λi. folm2mm M)) (λi. σ x) fw})
               a)
Proof
rw[] >>
`feval M σ a <=> feval (mm2folm (folm2mm M)) σ a`
     by metis_tac[L1tau_mm2folm_folm2mm_comm_feval] >>
qabbrev_tac `N = (mm2folm (folm2mm M))` >>
`feval N σ a <=>
 feval (mm2folm (ultraproduct_model U I' (λi. folm2mm N)))
          (λx.
               {fw | Uequiv U I' (models2worlds (λi. folm2mm N)) (λi. σ x) fw})
          a`
   by
    (irule ultraproduct_mm2folm_folm2mm_comm_feval >> rw[] (* 7 *)
     >- fs[Abbr`N`,mm2folm_def,folm2mm_def]
     >- fs[Abbr`N`,mm2folm_def,folm2mm_def]
     >- (fs[Abbr`N`,mm2folm_def,folm2mm_def,valuation_def] >>
         `M.Dom <> {}` suffices_by metis_tac[CHOICE_DEF] >>
         metis_tac[MEMBER_NOT_EMPTY])
     >- fs[Abbr`N`,mm2folm_def,folm2mm_def]
     >- fs[L1tau_def]
     >- (fs[valuation_def,IMAGE_DEF,SUBSET_DEF,Abbr`N`,mm2folm_def,folm2mm_def]
         >> metis_tac[])
     >- metis_tac[]) >>
`feval (mm2folm (ultraproduct_model U I' (λi. folm2mm N)))
          (λx.
               {fw | Uequiv U I' (models2worlds (λi. folm2mm N)) (λi. σ x) fw})
          a <=>
 feval (mm2folm (ultraproduct_model U I' (λi. folm2mm M)))
          (λx.
               {fw | Uequiv U I' (models2worlds (λi. folm2mm M)) (λi. σ x) fw})
          a` suffices_by metis_tac[] >>
rw[Abbr`N`] >>
qabbrev_tac `MS = \i. (mm2folm (folm2mm M))` >>
`feval
        (ultraproduct_folmodel U I' MS)
           (λx.
               {fw |
                Uequiv U I'
                  (models2worlds (λi. folm2mm (mm2folm (folm2mm M))))
                  (λi. σ x) fw}) a <=>
 feval
          (mm2folm
             (ultraproduct_model U I' (λi. folm2mm (MS i))))
          (λx.
               {fw |
                Uequiv U I'
                  (models2worlds (λi. folm2mm (mm2folm (folm2mm M))))
                  (λi. σ x) fw}) a`
  by
    (irule ultraproduct_comm_feval' >> rw[] (* 6 *)
     >- fs[Abbr`MS`,mm2folm_def,folm2mm_def]
     >- fs[Abbr`MS`,mm2folm_def,folm2mm_def]
     >- fs[Abbr`MS`,mm2folm_def,folm2mm_def]
     >- (fs[Abbr`MS`,mm2folm_def,folm2mm_def] >>
        `M.Dom <> {}` suffices_by metis_tac[CHOICE_DEF] >>
        fs[valuation_def] >> metis_tac[MEMBER_NOT_EMPTY])
     >- fs[L1tau_def]
     >- (rw[IMAGE_DEF,SUBSET_DEF,ultraproduct_def,folmodels2Doms_def,
            partition_def,Cart_prod_def] >>
         qexists_tac `(λi. σ x'')` >> rw[] (* 2 *)
         >- fs[Abbr`MS`,mm2folm_def,folm2mm_def,valuation_def]
         >- (`(models2worlds (λi. folm2mm (mm2folm (folm2mm M)))) =
              (λi. (MS i).Dom)`
              by
               (rw[models2worlds_def,Abbr`MS`,folm2mm_def,mm2folm_def]) >>
             fs[] >>
             rw[EQ_IMP_THM,EXTENSION,Uequiv_def] >>
             fs[Cart_prod_def]))) >>
qabbrev_tac `MS' = \i. (folm2mm M)` >>
`feval (mm2folm (ultraproduct_model U I' MS'))
          (λx.
               {fw |
                Uequiv U I'
                  (models2worlds (λi. folm2mm (mm2folm (folm2mm M))))
                  (λi. σ x) fw}) a <=>
   feval (ultraproduct_folmodel U I' (λi. mm2folm (MS' i)))
          (λx.
               {fw |
                Uequiv U I'
                  (models2worlds (λi. folm2mm (mm2folm (folm2mm M))))
                  (λi. σ x) fw}) a`
    by
     (irule ultraproduct_comm_feval >>
      `(models2worlds (λi. folm2mm (mm2folm (folm2mm M)))) =
              (λi. (MS i).Dom)`
        by (rw[models2worlds_def,Abbr`MS`,folm2mm_def,mm2folm_def]) >>
      fs[] >>
      rw[EQ_IMP_THM,EXTENSION,Uequiv_def] >>
      fs[Cart_prod_def] (* 2 *)
      >- fs[L1tau_def,MEMBER_NOT_EMPTY] >>
      rw[IMAGE_DEF,SUBSET_DEF,ultraproduct_def,Cart_prod_def,partition_def] >>
      qexists_tac `\i. σ x''` >> rw[] (* 2 *)
      >- fs[models2worlds_def,valuation_def,Abbr`MS'`,folm2mm_def] >>
      rw[EXTENSION,EQ_IMP_THM] (* 6 *)
      >- fs[models2worlds_def,Abbr`MS'`,folm2mm_def,Abbr`MS`,mm2folm_def]
      >- (rw[Uequiv_def] (* 3 *)
         >- (fs[Abbr`MS'`,folm2mm_def,
             models2worlds_def,valuation_def,GSYM MEMBER_NOT_EMPTY] >>
             metis_tac[])
         >>(rw[Cart_prod_def,models2worlds_def,Abbr`MS'`,folm2mm_def] >>
             fs[Abbr`MS`,folm2mm_def,mm2folm_def] >> metis_tac[]))
      >- (`(MS i).Dom = M.Dom` by fs[Abbr`MS`,folm2mm_def,mm2folm_def] >>
          `models2worlds MS' i = M.Dom`
           by fs[Abbr`MS'`,folm2mm_def,models2worlds_def] >>
          metis_tac[])
      >- (`(MS i).Dom = M.Dom` by fs[Abbr`MS`,folm2mm_def,mm2folm_def] >>
          fs[valuation_def])
      >- (`(MS i).Dom = M.Dom` by fs[Abbr`MS`,folm2mm_def,mm2folm_def] >>
          `models2worlds MS' i = M.Dom`
           by fs[Abbr`MS'`,folm2mm_def,models2worlds_def] >>
          metis_tac[])
      >- fs[Uequiv_def]) >>
fs[Abbr`MS`,Abbr`MS'`] >>
`feval M σ a <=> feval (mm2folm (ultraproduct_model U I' (λi. folm2mm M)))
          (λx.
               {fw |
                Uequiv U I'
                  (models2worlds (λi. folm2mm (mm2folm (folm2mm M))))
                  (λi. σ x) fw}) a` by metis_tac[] >>
`(models2worlds (λi. folm2mm (mm2folm (folm2mm M)))) =
 (models2worlds (λi. folm2mm M))`
   suffices_by (rw[] >> fs[]) >>
fs[models2worlds_def,folm2mm_def,mm2folm_def]
QED

val invar4bisim_def = Define`
  invar4bisim x (t1: μ itself) (t2: ν itself) phi <=>
     (FV phi ⊆ {x} /\ L1tau phi /\
     !(M:μ modalBasics$model) (N:ν modalBasics$model) v w.
        bisim_world M N (w:μ) (v:ν) ==>
           (!(σm: num -> μ) (σn: num -> ν).
             (valuation (mm2folm M) σm /\ valuation (mm2folm N) σn) ==>
                    (fsatis (mm2folm M) σm(|x |-> w|) phi <=>
                    fsatis (mm2folm N) σn(|x |-> v|) phi )))`

Theorem invar4bisim_def':
 ∀x phi.
            invar4bisim x (:α) (:β) phi ⇔
            FV phi ⊆ {x} ∧ L1tau phi ∧
            ∀M N v:β w:α.
                bisim_world M N w v ⇒
                    (fsatis (mm2folm M) (\n.w) phi ⇔
                     fsatis (mm2folm N) (\n.v) phi)
Proof
rw[invar4bisim_def,Once EQ_IMP_THM] (* 2 *)
>- (`valuation (mm2folm M) (λn:num. w) ∧ valuation (mm2folm N) (λn:num. v)`
      by fs[valuation_def,bisim_world_def,mm2folm_def] >>
    `(fsatis (mm2folm M) (λn. w)⦇x ↦ w⦈ phi ⇔
                 fsatis (mm2folm N) (λn. v)⦇x ↦ v⦈ phi)` by metis_tac[] >>
    `(λn. w)⦇x ↦ w⦈ = (λn. w) /\ (λn. v)⦇x ↦ v⦈ = (λn. v)` by simp[] >>
    ntac 2 (pop_assum SUBST_ALL_TAC) >> simp[]) >>
first_x_assum drule >> rw[] >>
`fsatis (mm2folm M) (λn. w) phi = fsatis (mm2folm M) σm⦇x ↦ w⦈ phi /\
 fsatis (mm2folm N) (λn. v) phi = fsatis (mm2folm N) σn⦇x ↦ v⦈ phi`
   suffices_by metis_tac[] >>
strip_tac
>- (`feval (mm2folm M) (λn. w) phi = feval (mm2folm M) σm⦇x ↦ w⦈ phi`
        by
         (irule holds_valuation >> fs[SUBSET_DEF] >>
          rw[combinTheory.APPLY_UPDATE_THM]) >>
       `valuation (mm2folm M) (λn:num. w) /\
        valuation (mm2folm M) σm⦇x ↦ w⦈`
        by fs[valuation_def,mm2folm_def,bisim_world_def] >>
        fs[fsatis_def]) >>
`feval (mm2folm N) (λn. v) phi = feval (mm2folm N) σn⦇x ↦ v⦈ phi`
        by
         (irule holds_valuation >> fs[SUBSET_DEF] >>
          rw[combinTheory.APPLY_UPDATE_THM]) >>
       `valuation (mm2folm N) (λn:num. v) /\
        valuation (mm2folm N) σn⦇x ↦ v⦈`
        by fs[valuation_def,mm2folm_def,bisim_world_def] >>
        fs[fsatis_def]
QED

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

Theorem thm_2_68_half1:
!a x. INFINITE univ (:α) ==>
      (invar4bisim x
       (t1: ((num -> α) -> bool) itself)
       (t2: ((num -> α) -> bool) itself) a ==>
       ?phi.
          !M (v:num -> α). valuation M v ==>
                           (feval M v a <=> feval M v (ST x phi)))
Proof
rw[] >>
qabbrev_tac
  `MOC = {ST x phi | phi |
           (!M:α folModels$model v.
               valuation M v ==>
                feval M v a ==> feval M v (ST x phi))}` >>
`!M:α folModels$model v. valuation M v ==>
               (!ff. ff IN MOC ==> feval M v ff) ==> feval M v a`
  suffices_by
   (strip_tac >> drule compactness_corollary_L1tau >> rw[] >>
    first_x_assum (qspecl_then [`MOC`,`a`] assume_tac) >>
    `L1tau a ∧ (∀f. f ∈ MOC ⇒ L1tau f)`
      by
       (fs[invar4bisim_def,Abbr`MOC`] >> rw[] >> metis_tac[ST_L1tau]) >>
    first_x_assum drule_all >> rw[] >>
    drule ST_BIGCONJ >> rw[] >>
    first_x_assum (qspec_then `x` assume_tac) >>
    `(∀f. f ∈ ss ⇒ ∃phi. f = ST x phi)`
      by
       (fs[Abbr`MOC`,SUBSET_DEF] >> metis_tac[]) >>
    first_x_assum drule >>
    rw[] >> qexists_tac `psi` >> rw[EQ_IMP_THM] (* 2 *)
    >- (`IMAGE v 𝕌(:num) ⊆ M.Dom`
          by (fs[IMAGE_DEF,SUBSET_DEF,valuation_def] >> metis_tac[]) >>
        `∀f. f ∈ ss ⇒ feval M v f` suffices_by metis_tac[] >>
        fs[Abbr`MOC`,SUBSET_DEF] >> metis_tac[]
       )
    >- (`IMAGE v 𝕌(:num) ⊆ M.Dom`
          by (fs[IMAGE_DEF,SUBSET_DEF,valuation_def] >> metis_tac[]) >>
        `∀f. f ∈ ss ⇒ feval M v f` by metis_tac[] >>
        metis_tac[])
 ) >>
rw[] >>
qabbrev_tac `Tx = {ST x phi |phi| feval M v (ST x phi)}` >>
`?N σn. valuation N σn /\ (!f. (f IN Tx \/ f = a) ==> feval N σn f)`
   by
   (SPOSE_NOT_THEN ASSUME_TAC >>
    (*`entails (:α) Tx (fNOT a)`
      by (rw[entails_def,hold_def] >> metis_tac[]) >>*)
    `!M v. valuation M v ==>
            (∀f. f ∈ Tx ⇒ feval M v f) ⇒ feval M v (fNOT a)`
      by
       (rw[fNOT_def,feval_def] >> metis_tac[]) >>
    (* drule (folCanonTheory.finite_entailment |> GEN_ALL) >>
    strip_tac >> first_x_assum (qspecl_then [`fNOT a`,`Tx`] assume_tac) >>
    fs[] >> *)
    drule compactness_corollary_L1tau >> strip_tac >>
    first_x_assum (qspecl_then [`Tx`,`fNOT a`] assume_tac) >>
    `L1tau (fNOT a) ∧ (∀f. f ∈ Tx ⇒ L1tau f)`
      by
       (rw[] (* 2 *)
        >- fs[invar4bisim_def,L1tau_def,fNOT_def,
              form_functions_def,form_predicates]
        >- (fs[Abbr`Tx`] >> metis_tac[ST_L1tau])) >>
    first_x_assum drule_all >> strip_tac >>
    drule ST_BIGCONJ >> strip_tac >>
    first_x_assum (qspec_then `x` assume_tac) >>
    `(∀f. f ∈ ss ⇒ ∃phi. f = ST x phi)`
      by
       (rw[] >> fs[Abbr`Tx`,SUBSET_DEF] >> metis_tac[]) >>
    first_x_assum drule >> strip_tac >> rw[] >>
    `!M v. valuation M v ==> (feval M v a ==> ¬(feval M v (ST x psi)))`
      by
       (rw[] >>
        `IMAGE v' 𝕌(:num) ⊆ M'.Dom`
          by
           (fs[valuation_def,IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
        SPOSE_NOT_THEN ASSUME_TAC >>
        `feval M' v' (fNOT a)` by metis_tac[] >>
        fs[feval_def,fNOT_def]) >>
    `(ST x (¬psi)) IN MOC`
      by
       (rw[Abbr`MOC`] >> qexists_tac `¬psi` >> rw[ST_fNOT]) >>
    `feval M v (fNOT (ST x psi))` by fs[] >>
    fs[feval_def] >>
    `IMAGE v 𝕌(:num) ⊆ M.Dom`
      by (fs[IMAGE_DEF,SUBSET_DEF,valuation_def] >> metis_tac[]) >>
    `?f. f ∈ ss /\ ¬feval M v f` by metis_tac[] >>
    fs[Abbr`Tx`,SUBSET_DEF] >> metis_tac[]
   ) >>
(*existence of N*)
`feval N σn a` by fs[] >>
qabbrev_tac `w0 = v x` >>
qabbrev_tac `v0 = σn x` >>
`!phi. satis (folm2mm M) w0 phi <=> satis (folm2mm N) v0 phi`
  by
   (`IMAGE v 𝕌(:num) ⊆ (folm2mm M).frame.world /\
     IMAGE σn 𝕌(:num) ⊆ (folm2mm N).frame.world`
      by (fs[valuation_def,IMAGE_DEF,SUBSET_DEF,folm2mm_def] >> metis_tac[]) >>
    rw[EQ_IMP_THM] (* 2 *)
    >- (`ST x phi IN Tx`
          by
           (`fsatis (mm2folm (folm2mm M)) v (ST x phi)`
              by metis_tac[Abbr`w`,prop_2_47_i] >>
            rw[Abbr`Tx`] >>
            `feval M v (ST x phi)` suffices_by metis_tac[] >>
            `form_functions (ST x phi) = {}`
              by metis_tac[ST_form_functions_EMPTY] >>
            fs[fsatis_def] >>
            `feval (mm2folm (folm2mm M)) v (ST x phi) <=>
             feval M v (ST x phi)` suffices_by metis_tac[] >>
            irule L1tau_mm2folm_folm2mm_comm_feval >> rw[] >>
            metis_tac[ST_L1tau]
           ) >>
        `feval N σn (ST x phi)` by metis_tac[] >>
        `feval (mm2folm (folm2mm N)) σn (ST x phi)`
          by
           (`feval (mm2folm (folm2mm N)) σn (ST x phi) <=>
             feval N σn (ST x phi)`
              by
               (irule L1tau_mm2folm_folm2mm_comm_feval >>
                metis_tac[ST_L1tau]) >>
            metis_tac[]) >>
        rw[Abbr`v0`] >>
        `fsatis (mm2folm (folm2mm N)) σn (ST x phi)`
           suffices_by metis_tac[prop_2_47_i] >>
        rw[fsatis_def,valuation_def] >> fs[mm2folm_def,IMAGE_DEF,SUBSET_DEF] >>
        metis_tac[])
    >- (SPOSE_NOT_THEN ASSUME_TAC >>
        `ST x (NOT phi) IN Tx`
          by
           (`satis (folm2mm M) w0 (NOT phi)`
              by
               (rw[satis_def,Abbr`w0`] >>
                fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
            `fsatis (mm2folm (folm2mm M)) v (ST x (NOT phi))`
              by
               (`fsatis (mm2folm (folm2mm M)) v (ST x (¬phi))`
                  suffices_by metis_tac[ST_fNOT] >>
                `satis (folm2mm M) (v x) (¬phi) <=>
                 fsatis (mm2folm (folm2mm M)) v (ST x (¬phi))`
                  suffices_by metis_tac[Abbr`w0`] >>
                irule prop_2_47_i >> rw[]
               ) >>
            rw[Abbr`Tx`] >>
            qexists_tac `NOT phi` >> rw[ST_fNOT] >>
            `form_functions (ST x phi) = {}`
              by metis_tac[ST_form_functions_EMPTY] >>
            fs[fsatis_def] >>
            `feval (mm2folm (folm2mm M)) v (ST x phi) <=>
             feval M v (ST x phi)` suffices_by metis_tac[] >>
            irule L1tau_mm2folm_folm2mm_comm_feval >>
            metis_tac[ST_L1tau]
           ) >>
        `feval N σn (ST x (NOT phi))` by metis_tac[] >>
        `feval (mm2folm (folm2mm N)) σn (ST x (NOT phi)) <=>
         feval N σn (ST x (¬phi))`
          by
           (irule L1tau_mm2folm_folm2mm_comm_feval >> metis_tac[ST_L1tau]) >>
        `feval (mm2folm (folm2mm N)) σn (ST x (NOT phi))`
          by metis_tac[] >>
        fs[Abbr`v0`] >>
        `¬fsatis (mm2folm (folm2mm N)) σn (ST x phi)`
           suffices_by metis_tac[prop_2_47_i] >>
        rw[fsatis_def,valuation_def] >> fs[mm2folm_def,IMAGE_DEF,SUBSET_DEF] >>
        metis_tac[])
   ) >>
(*apply 2.74*)
`v0 IN (folm2mm N).frame.world /\ w0 IN (folm2mm M).frame.world`
  by (fs[folm2mm_def,valuation_def,Abbr`w0`,Abbr`v0`] >> metis_tac[]) >>
drule (thm_2_74_half2 |> INST_TYPE [beta |-> ``:'a``]) >>
strip_tac >>
first_x_assum (qspecl_then [`folm2mm N`,`v0`] assume_tac) >>
first_x_assum drule >> rw[] >>
fs[invar4bisim_def] >>
qabbrev_tac `Mst = (ultraproduct_model U I' (λi. folm2mm M))` >>
qabbrev_tac `Nst = (ultraproduct_model U I' (λi. folm2mm N))` >>
qabbrev_tac
  `wst = {fw | Uequiv U I' (models2worlds (λi. folm2mm M)) (λi. w0) fw}` >>
qabbrev_tac
  `vst = {fv | Uequiv U I' (models2worlds (λi. folm2mm N)) (λi. v0) fv}` >>
first_x_assum (qspecl_then [`Mst`,`Nst`,`vst`,`wst`] assume_tac) >> rfs[] >>
drule (corollary_A_21 |> INST_TYPE [alpha |-> ``:num``,beta |-> ``:'a``]) >>
rw[] >>
`(feval M v a <=> fsatis (mm2folm Mst) (\x. wst) a) /\
 fsatis (mm2folm Nst) (\x. vst) a`
  suffices_by
   (rw[] >>
    first_x_assum
      (qspecl_then [`(λx. wst)`,`(λx. vst)`] assume_tac) >>
    `(λx. wst)⦇x ↦ wst⦈ = (λx. wst) ∧ (λx. vst)⦇x ↦ vst⦈ = (λx. vst)`
      by simp[] >> ntac 2 (pop_assum SUBST_ALL_TAC) >>
    rw[] >> fs[] >>
    `(fsatis (mm2folm Mst) (λx. wst) a ⇔ fsatis (mm2folm Nst) (λx. vst) a)`
      suffices_by metis_tac[] >>
    first_x_assum irule >> fs[valuation_def,mm2folm_def,bisim_world_def]
   ) >>
`(feval M v a ⇔ fsatis (mm2folm Mst) (λx. wst) a) /\
 (feval N σn a <=> fsatis (mm2folm Nst) (λx. vst) a)`
suffices_by metis_tac[] >>
`!M σ a (I:num -> bool) U.
  L1tau a /\ FV a ⊆ {x} /\ ultrafilter U I /\ valuation M σ ==>
  (feval M σ a <=>
     feval (mm2folm (ultraproduct_model U I (λi. folm2mm M)))
       (λx. {fw | Uequiv U I (models2worlds (λi. folm2mm M)) (λi. σ x) fw}) a)`
  suffices_by
   (rpt strip_tac (* 2 *)
    >- (first_x_assum (qspecl_then [`M`,`v`,`a`,`I'`,`U`] assume_tac) >>
        first_x_assum drule_all >> strip_tac >>
        fs[Abbr`Mst`,Abbr`wst`,Abbr`w0`] >> rw[] >>
        fs[fsatis_def] >>
        `valuation (mm2folm (ultraproduct_model U I' (λi. folm2mm M)))
          (λx':num.
            {fw | Uequiv U I' (models2worlds (λi. folm2mm M)) (λi. v x) fw})`
          by
           (rw[valuation_def,mm2folm_def,ultraproduct_model_def] >>
            rw[ultraproduct_def,models2worlds_def,folm2mm_def,partition_def] >>
            qexists_tac `\i. v x` >> rw[Cart_prod_def,EXTENSION,EQ_IMP_THM] (*2*)           >- fs[folm2mm_def,valuation_def] >>
            fs[Uequiv_def,Cart_prod_def]
            ) >>
        fs[] >>
        irule holds_valuation >> rw[] >>
        `x' = x` by fs[SUBSET_DEF] >>
        rw[])
    >- (first_x_assum (qspecl_then [`N`,`σn`,`a`,`I'`,`U`] assume_tac) >>
        first_x_assum drule_all >> strip_tac >>
        fs[Abbr`Nst`,Abbr`vst`,Abbr`v0`] >> rw[] >>
        fs[fsatis_def] >>
        `valuation (mm2folm (ultraproduct_model U I' (λi. folm2mm N)))
          (λx':num.
            {fw | Uequiv U I' (models2worlds (λi. folm2mm N)) (λi. σn x) fw})`
          by
           (rw[valuation_def,mm2folm_def,ultraproduct_model_def] >>
            rw[ultraproduct_def,models2worlds_def,folm2mm_def,partition_def] >>
            qexists_tac `\i. σn x` >> rw[Cart_prod_def,EXTENSION,EQ_IMP_THM] (*2*)           >- fs[folm2mm_def] >>
            fs[Uequiv_def,Cart_prod_def]
            ) >>
        fs[] >>
        irule holds_valuation >> rw[] >>
        `x' = x` by fs[SUBSET_DEF] >>
        rw[])
   ) >>
metis_tac[L1tau_ultraproduct_mm2folm_folm2mm_comm_feval]
QED



Theorem holds_functions_predicates:
   M2.Dom = M1.Dom ∧
  (∀P zs. (P,LENGTH zs) ∈ form_predicates p ⇒ (M2.Pred P zs ⇔ M1.Pred P zs)) /\
  (∀f zs. (f,LENGTH zs) ∈ form_functions p ⇒ M2.Fun f zs = M1.Fun f zs) ⇒
      (∀v. feval M2 v p ⇔ feval M1 v p)
Proof
rw[] >>
qabbrev_tac `M1' = <| Dom := M1.Dom ;
                      Fun := M2.Fun ;
                      Pred := M1.Pred |>` >>
`M2.Dom = M1'.Dom`
  by
   (fs[Abbr`M1'`]) >>
drule holds_predicates >> rw[] >>
`(feval M2 v p ⇔ feval M1' v p)`
  by
   (first_x_assum irule >> rw[] (*  2*)
    >- fs[Abbr`M1'`,FUN_EQ_THM]
    >- fs[Abbr`M1'`]) >>
rw[] >>
`M1'.Dom = M1.Dom` by fs[Abbr`M1'`] >>
drule holds_functions >> rw[] >>
first_x_assum irule >> rw[] (* 2 *)
>- fs[Abbr`M1'`]
>- fs[Abbr`M1'`,FUN_EQ_THM]
QED

Theorem thm_2_68_half2':
!phi x. invar4bisim x (:α) (:α) (ST x phi)
Proof
rw[invar4bisim_def] (* 3 *)
>- metis_tac[ST_FV_singleton]
>- metis_tac[ST_L1tau]
>- metis_tac[thm_2_68_half2]
QED




Theorem ultraproduct_comm_feval2:
!phi U I MS.
  ultrafilter U I ==>
  L1tau phi ==>
  (∀n0 l0 i. i IN I ==> (MS i).Fun n0 l0 ∈ (MS i).Dom) ==>
  !σ.
     IMAGE σ (univ(:num)) ⊆ ultraproduct U I (folmodels2Doms MS) ==>
     (feval (ultraproduct_folmodel U I MS) σ phi <=>
      feval (mm2folm (ultraproduct_model U I (λi. folm2mm (MS i)))) σ phi)
Proof
Induct_on `phi` (* 4 *)
>- fs[feval_def]
>- (rw[feval_def] >>
    `MAP (termval (ultraproduct_folmodel U I' MS) σ) l =
     MAP (termval
           (mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))) σ) l`
     by
      (irule listTheory.MAP_CONG >> rw[] >> irule ultraproduct_comm_termval' >> rw[] >> fs[L1tau_def] >>
       SPOSE_NOT_THEN ASSUME_TAC >> fs[GSYM MEMBER_NOT_EMPTY] >>
       `x' IN LIST_UNION (MAP term_functions l)`
         suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
       simp[IN_LIST_UNION] >> qexists_tac `term_functions x` >>
       rw[MEM_MAP] >> metis_tac[]) >>
    rw[] >>
    qabbrev_tac
      `mapl =
        MAP (termval
             (mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))) σ) l` >>
    Cases_on `mapl = []` (* 2 *)
    >- (`form_predicates (Pred n l) ⊆ (0,2) INSERT {(p,1) | p ∈ 𝕌(:num)}`
         by metis_tac[L1tau_def] >>
       `l = []` by
         (SPOSE_NOT_THEN ASSUME_TAC >> fs[Abbr`mapl`]) >>
       fs[])
    >- (`(?a. l = [a]) \/
         (?a b. l = [a;b]) \/
         (?a b c d. l = a :: b :: c :: d)`
          by
           (Cases_on `l` >> fs[Abbr‘mapl’] >>
            Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[]) (* 3 *)
        >- (rw[] >>
            qabbrev_tac
             `sl = termval (ultraproduct_folmodel U I' MS) σ a` >>
            rw[mm2folm_def,
               ultraproduct_folmodel_def,ultraproduct_model_def] >>
            `sl ∈ ultraproduct U I' (models2worlds (λi. folm2mm (MS i)))`
             by
              (rw[Abbr`sl`] >> drule termval_IN_ultraproduct_Dom' >>
               rw[] >>
               metis_tac[folmodels2Doms_models2worlds_folm2mm]) >>
            (*remove the conj first*)
           `sl <> {}` by metis_tac[ultraproduct_eqclass_non_empty] >>
           `CHOICE sl IN sl` by metis_tac[CHOICE_DEF] >>
           `{i | i ∈ I' ∧ (MS i).Pred n [CHOICE sl i]} =
            {i | i ∈ I' ∧ CHOICE sl i ∈ (folm2mm (MS i)).valt n}`
             by (rw[EXTENSION,EQ_IMP_THM,folm2mm_def] >>
                 drule ultraproduct_val_IN_A >> rw[] >>
                 first_x_assum
                   (qspecl_then [`models2worlds (λi. folm2mm (MS i))`,
                                 `sl`,`CHOICE sl`,`x`] assume_tac) >>
                 `(models2worlds (λi. folm2mm (MS i))) x = (MS x).Dom`
                   by rw[models2worlds_def,folm2mm_def] >>
                 fs[]) >>
           rw[EQ_IMP_THM] >- metis_tac[] >>
           `{i | i IN I' /\ f i = (CHOICE sl) i} IN U`
             by
              (irule ultraproduct_same_eqclass >> rw[] >>
               map_every qexists_tac
                [`models2worlds (λi. folm2mm (MS i))`,`sl`] >>
               rw[]) >>
           `({i | i ∈ I' ∧ f i ∈ (folm2mm (MS i)).valt n} ∩
             {i | i ∈ I' ∧ f i = CHOICE sl i}) IN U`
             by metis_tac[ultrafilter_INTER] >>
           irule ultrafilter_SUBSET' >> rw[PULL_EXISTS] (* 2 *)
           >- (qexists_tac
                 `{i | i ∈ I' ∧ f i ∈ (folm2mm (MS i)).valt n} ∩
                  {i | i ∈ I' ∧ f i = CHOICE sl i}` >>
               rw[SUBSET_DEF] >> metis_tac[]) >>
           qexists_tac `I'` >> rw[SUBSET_DEF]
           ) (*1 out of 3*)
      >- (rw[] >>
            qabbrev_tac
             `sl1 = termval (ultraproduct_folmodel U I' MS) σ a` >>
            qabbrev_tac
             `sl2 = termval (ultraproduct_folmodel U I' MS) σ b` >>
            rw[mm2folm_def,ultraproduct_folmodel_def,ultraproduct_model_def] >>
            `{i | i ∈ I' ∧ (MS i).Pred n [CHOICE sl1 i; CHOICE sl2 i]} ∈ U ==>
             n = 0`
              by
               (rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
                `{i | i ∈ I' ∧ (MS i).Pred n [CHOICE sl1 i; CHOICE sl2 i]} = {}`
                  by
                   (fs[] >>
                    `form_predicates (Pred n [a; b]) ⊆
                     (0,2) INSERT {(p,1) | p ∈ 𝕌(:num)}` by metis_tac[L1tau_def] >> fs[]
                ) >>
                metis_tac[EMPTY_NOTIN_ultrafilter]) >>
            `sl1 ∈ ultraproduct U I' (models2worlds (λi. folm2mm (MS i))) ∧
             sl2 ∈ ultraproduct U I' (models2worlds (λi. folm2mm (MS i)))`
              by
               (`!t. (termval (ultraproduct_folmodel U I' MS) σ t) IN
                 ultraproduct U I' (models2worlds (λi. folm2mm (MS i)))`
                  suffices_by metis_tac[] >>
                drule termval_IN_ultraproduct_Dom' >>
                rw[] >>
                metis_tac[folmodels2Doms_models2worlds_folm2mm]) >>
            `sl1 <> {}` by metis_tac[ultraproduct_eqclass_non_empty] >>
            `sl2 <> {}` by metis_tac[ultraproduct_eqclass_non_empty] >>
            `CHOICE sl1 IN sl1 /\ CHOICE sl2 IN sl2` by metis_tac[CHOICE_DEF]>>
            rw[EQ_IMP_THM,EXTENSION] (* 2 *)
            >- (map_every qexists_tac [`CHOICE sl1`,`CHOICE sl2`] >>
                rw[] >>
                `n = 0` by metis_tac[] >>
                `!i. i IN I' ==> CHOICE sl1 i ∈ (MS i).Dom /\
                 CHOICE sl2 i ∈ (MS i).Dom`
                  by
                   (drule ultraproduct_val_IN_A >>
                    `!x. models2worlds (λi. folm2mm (MS i)) x = (MS x).Dom`
                      by rw[models2worlds_def,folm2mm_def] >>
                    metis_tac[CHOICE_DEF,ultraproduct_eqclass_non_empty]) >>
                rw[folm2mm_def] >>
                `{i | i ∈ I' ∧ (MS i).Pred 0 [CHOICE sl1 i; CHOICE sl2 i]} =
                 {i | i ∈ I' ∧ (MS i).Pred 0 [CHOICE sl1 i; CHOICE sl2 i] ∧
                   CHOICE sl1 i ∈ (MS i).Dom ∧ CHOICE sl2 i ∈ (MS i).Dom}`
                  by rw[EXTENSION,EQ_IMP_THM] >>
                metis_tac[]) >>
            qmatch_abbrev_tac `ss IN U` >>
            irule ultrafilter_INTER_INTER_SUBSET >>
            `ss ⊆ I'` by fs[Abbr`ss`,SUBSET_DEF,INTER_DEF] >> rw[] (* 2 *)
            >- (map_every qexists_tac
                 [`{i | i IN I' /\ f i = (CHOICE sl1) i}`,
                  `{i | i IN I' /\ g i = (CHOICE sl2) i}`,
                  `{i | i ∈ I' ∧ (folm2mm (MS i)).frame.rel (f i) (g i)}`] >>
                rw[SUBSET_DEF,folm2mm_def] (* 3 *)
                >- (irule ultraproduct_same_eqclass >> rw[] >>
                    map_every qexists_tac
                    [`models2worlds (λi. folm2mm (MS i))`,`sl1`] >>
                    rw[])
                >- (irule ultraproduct_same_eqclass >> rw[] >>
                    map_every qexists_tac
                    [`models2worlds (λi. folm2mm (MS i))`,`sl2`] >>
                    rw[]) >>
                fs[Abbr`ss`] >> metis_tac[]) >>
            qexists_tac `I'` >> rw[SUBSET_DEF])
        >- (fs[] >>
            `form_predicates (Pred n (a::b::c::d)) ⊆
             (0,2) INSERT {(p,1) | p ∈ 𝕌(:num)}` by metis_tac[L1tau_def] >>
             fs[])
    )
   )
>- (rw[] >>
    `L1tau phi /\ L1tau phi'` suffices_by metis_tac[] >>
    metis_tac[L1tau_fIMP])
>- (rw[feval_def,EQ_IMP_THM] (* 2 *)
    >- (`L1tau phi` by metis_tac[L1tau_FALL] >>
        first_x_assum drule >> rw[] >>
        `IMAGE σ⦇n ↦ a⦈ 𝕌(:num) ⊆ ultraproduct U I' (folmodels2Doms MS)`
          by (irule IMAGE_UPDATE >>
              `(mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))).Dom =
               ultraproduct U I' (folmodels2Doms MS)`
               by
                (rw[mm2folm_def,ultraproduct_model_def] >>
                 `(models2worlds (λi. folm2mm (MS i))) = (folmodels2Doms MS)`
                   suffices_by metis_tac[] >>
                 rw[FUN_EQ_THM,models2worlds_def,
                    folm2mm_def,folmodels2Doms_def]) >>
              metis_tac[]) >>
        first_x_assum drule >> rw[] >>
        `(ultraproduct_folmodel U I' MS).Dom =
         (mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))).Dom`
          suffices_by metis_tac[] >>
        rw[ultraproduct_folmodel_def,mm2folm_def,ultraproduct_model_def] >>
        metis_tac[folmodels2Doms_models2worlds_folm2mm])
    >- (`L1tau phi` by metis_tac[L1tau_FALL] >>
        first_x_assum drule >> rw[] >>
        `IMAGE σ⦇n ↦ a⦈ 𝕌(:num) ⊆ ultraproduct U I' (folmodels2Doms MS)`
          by (irule IMAGE_UPDATE >> rw[] >> fs[ultraproduct_folmodel_def]) >>
        `(ultraproduct_folmodel U I' MS).Dom =
         (mm2folm (ultraproduct_model U I' (λi. folm2mm (MS i)))).Dom`
          suffices_by metis_tac[] >>
        rw[ultraproduct_folmodel_def,mm2folm_def,ultraproduct_model_def] >>
        metis_tac[folmodels2Doms_models2worlds_folm2mm])
    )
QED


Theorem holds_functions_predicates':
   (M2.Dom = M1.Dom ∧ valuation M1 v  /\ valuation M2 v) ==>
  (∀P zs. (P,LENGTH zs) ∈ form_predicates p ⇒ (M2.Pred P zs ⇔ M1.Pred P zs)) /\
  (∀f zs. (f,LENGTH zs) ∈ form_functions p ⇒ M2.Fun f zs = M1.Fun f zs) ⇒
      (∀v. feval M2 v p ⇔ feval M1 v p)
Proof
metis_tac[holds_functions_predicates]
QED



Theorem example_2_64_iii:
  ¬countably_saturated <|Dom:= univ(:num); Fun:= \f l. (CHOICE univ(:num)) ;
                         Pred := \n v. ?x. v = [x] /\ n < x|>
Proof
  rw[countably_saturated_def,expand_def,consistent_def,ftype_def,frealizes_def,
     n_saturated_def] >>
  qabbrev_tac ‘M = <|Dom:= univ(:num); Fun:= \f l. (CHOICE univ(:num)) ;
                     Pred := \n v. ?x. v = [x] /\ n < x|>’ >>
  map_every qexists_tac [‘0’,‘{}’,‘{fP n (fV a) | n | T}’,‘a’,‘\v.0’] >>
  rw[] (* 4 *)
  >- fs[Abbr‘M’]
  >- (fs[FV_def,FVT_def,SUBSET_DEF] >> rw[] >> fs[FV_def])
  >- (rw[] >>
      qabbrev_tac ‘ n = MAX_SET {n | (fP n (fV a)) IN G0}’ >>
      qexists_tac ‘\v. n + 1’ >> rw[] (* 1 *) >>
      fs[SUBSET_DEF] >> first_x_assum drule >> rw[] >> rw[fsatis_def] (* 2 *)
      >- rw[valuation_def,Abbr‘M’]
      >- (rw[Abbr‘M’] >> fs[Abbr‘n’] >>
          ‘n' <= MAX_SET {n | fP n (fV a) ∈ G0}’ suffices_by fs[] >>
          irule in_max_set >>
          rw[] >>
          ‘?f. INJ f {n | fP n (fV a) ∈ G0} G0’ suffices_by
            metis_tac[FINITE_INJ] >>
         qexists_tac ‘\n. fP n (fV a)’ >> rw[INJ_DEF])) >>
  map_every qexists_tac [‘\v.0’,‘fP (w + 1) (fV a)’] >> rw[fsatis_def] >>
  ‘¬M.Pred (w + 1) [w]’ suffices_by metis_tac[] >>
  rw[Abbr‘M’,combinTheory.APPLY_UPDATE_THM]
QED

Theorem feq_thm_2_68_half2:
  ∀phi a x. (FV a ⊆ {x} ∧ L1tau a /\ feq (:α) a (ST x phi)) ==>
            invar4bisim x (:α) (:α) a
Proof
  rw[] >> `invar4bisim x (:α) (:α) (ST x phi)` by metis_tac[thm_2_68_half2'] >>
  fs[feq_def,invar4bisim_def,fsatis_def] >> metis_tac[]
QED


Theorem thm_2_68_half1':
  ∀a x.
    (INFINITE 𝕌(:α) /\
     invar4bisim x (:(num -> α) -> bool) (:(num -> α) -> bool) a) ⇒
    ∃(phi:modalBasics$form). feq (:α) a (ST x phi)

Proof
  rw[] >> drule thm_2_68_half1 >>  rw[feq_def] >> metis_tac[]
QED

val _ = export_theory();
