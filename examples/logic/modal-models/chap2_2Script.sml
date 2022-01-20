open HolKernel Parse boolLib bossLib;
open chap1Theory;
open chap2_1Theory;
open numpairTheory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;
open pairTheory;


val _ = new_theory "chap2_2";


(* bisimulation *)

Definition bisim_def:
  bisim Z M M' <=>
   !w w'. w IN M.frame.world /\ w' IN M'.frame.world /\ Z w w' ==>
            (!a. (satis M w (VAR a)) <=> satis M' w' (VAR a)) /\
            (!v. v IN M.frame.world /\ M.frame.rel w v ==>
                 ?v'. v' IN M'.frame.world /\ Z v v' /\ M'.frame.rel w' v') /\
            (!v'. v' IN M'.frame.world /\ M'.frame.rel w' v' ==>
                  ?v. v IN M.frame.world /\ Z v v' /\ M.frame.rel w v)
End



Definition bisim_world_def:
  bisim_world M M' w w' <=>
   ?Z. bisim Z M M' /\ w IN M.frame.world /\ w' IN M'.frame.world /\ Z w w'
End



val bisim_model_def = Define`
bisim_model M M' <=> ?Z. bisim Z M M'`;



val prop_2_19_i = store_thm(
"prop_2_19_i",
``!M M' f. iso f M M' ==> bisim_model M M'``,
rw[bisim_model_def,bisim_def] >>
qexists_tac `λn1 n2. (n2 = f n1)` >>
rpt strip_tac
>- (`w' = f w` by metis_tac[] >> rw[] >> fs[satis_def,iso_def,strong_hom_def])
>- (qexists_tac `f v` >> `w' = f w` by metis_tac[] >> rw[]
    >- fs[iso_def,strong_hom_def]
    >- metis_tac[iso_def,strong_hom_def])
>- (fs[iso_def] >>
    `∃x. x ∈ M.frame.world /\ f x = v'` by metis_tac[BIJ_DEF,SURJ_DEF] >>
    qexists_tac `x` >> rw[] >> metis_tac[strong_hom_def])
);



val prop_2_19_ii = store_thm(
"prop_2_19_ii",
``!i w f dom. i IN dom /\ w IN (f i).frame.world ==>
              bisim_world (f i) (DU (f,dom)) w (i,w)``,
rpt strip_tac >> rw[bisim_world_def] >> qexists_tac `λa b. (b = (i, a))` >> rw[]
>- (fs[bisim_def] >> rw[]
    >- fs[satis_def,DU_def,FST,SND,IN_DEF]
    >- fs[DU_def,FST,SND,IN_DEF]
    >- fs[DU_def,FST,SND,IN_DEF]
    >- (qexists_tac `SND b'` >> rw[] >> fs[DU_def,FST,SND,IN_DEF]))
>- fs[DU_def,FST,SND,IN_DEF]);



Theorem prop_2_19_iii:
  ∀M M'. GENSUBMODEL M M' ==> (!w. w IN M.frame.world ==> bisim_world M M' w w)
Proof
rw[bisim_world_def,bisim_def] >>
qexists_tac `λn1 n2. n1 = n2` >>
rpt strip_tac
   >- (`w'' = w'` by metis_tac[] >> rw[] >>
       fs[GENSUBMODEL_def,SUBMODEL_def,satis_def,IN_DEF])
   >- (`w'' = w'` by metis_tac[] >> rw[]
       >- fs[GENSUBMODEL_def,SUBMODEL_def,SUBSET_DEF]
       >- metis_tac[GENSUBMODEL_def,SUBMODEL_def])
   >- (`w'' = w'` by metis_tac[] >> rw[]
       >- metis_tac[GENSUBMODEL_def,SUBMODEL_def]
       >- metis_tac[GENSUBMODEL_def,SUBMODEL_def])
   >- metis_tac[GENSUBMODEL_def,SUBMODEL_def,SUBSET_DEF]
   >- metis_tac[]
QED



Theorem prop_2_19_iv:
  !M M' f. bounded_mor_image f M M' ==>
           (!w. w IN M.frame.world ==> bisim_world M M' w (f w))
Proof
rw[bisim_world_def,bisim_def] >>
qexists_tac `λn1 n2. (n2 = f n1)` >>
rpt strip_tac
>- (`w'' = f w'` by metis_tac[] >> rw[] >>
    fs[bounded_mor_image_def,bounded_mor_def])
>- (`w'' = f w'` by metis_tac[] >> qexists_tac `f v` >> rw[] >>
    metis_tac[bounded_mor_image_def,bounded_mor_def])
>- metis_tac[bounded_mor_image_def,bounded_mor_def]
>- metis_tac[bounded_mor_image_def,bounded_mor_def]
>- metis_tac[]
QED



Theorem thm_2_20_lemma:
  !M M' w w' form.
    bisim_world M M' w w' ==> (satis M w form <=> satis M' w' form)
Proof
Induct_on `form`
>- (rpt strip_tac
  >> metis_tac[bisim_def,bisim_world_def])
>- (rpt strip_tac
  >> metis_tac[satis_def])
>- (rpt strip_tac
  >> metis_tac[satis_def])
>- (rpt strip_tac
  >> `satis M w form ⇔ satis M' w' form` by metis_tac[]
  >> `w IN M.frame.world` by metis_tac[bisim_world_def]
  >> `w' IN M'.frame.world` by metis_tac[bisim_world_def]
  >> metis_tac[satis_def])
>- (rpt strip_tac >> rw[satis_def] >> eq_tac
    >- (rpt strip_tac
        >- metis_tac[bisim_world_def]
        >- (`∃Z. bisim Z M M' ∧ w ∈ M.frame.world ∧ w' ∈ M'.frame.world ∧
                 Z w w'` by metis_tac[bisim_world_def] >>
            `∃v'. v' ∈ M'.frame.world ∧ Z v v' ∧ M'.frame.rel w' v'`
              by metis_tac[bisim_def,IN_DEF] >>
            `bisim_world M M' v v'` by metis_tac[bisim_world_def] >>
            qexists_tac `v'` >> metis_tac[IN_DEF]))
    >- (rpt strip_tac
        >- metis_tac[bisim_world_def]
        >- (`∃Z. bisim Z M M' ∧ w ∈ M.frame.world ∧ w' ∈ M'.frame.world ∧
                 Z w w'` by metis_tac[bisim_world_def] >>
            ‘M'.frame.rel w' v’ by metis_tac[IN_DEF] >>
            ‘?a. a IN M.frame.world /\ Z a v /\ M.frame.rel w a’
                by metis_tac[bisim_def] >>
            ‘bisim_world M M' a v’ by metis_tac[bisim_world_def] >>
            qexists_tac `a` >> metis_tac[IN_DEF])))
QED



val thm_2_20 = store_thm(
"thm_2_20",
``!M M' w w'. bisim_world M M' w w' ==> modal_eq M M' w w'``,
fs[modal_eq_def,tau_theory_def]
>> rpt strip_tac
>> `!form. satis M w form <=> satis M' w' form`
      suffices_by fs[SET_EQ_SUBSET,SUBSET_DEF] >> metis_tac[thm_2_20_lemma]);



(* Hennessy-Milner Theorem *)



val BIGCONJ_EXISTS = store_thm(
"BIGCONJ_EXISTS",
``!s: form set. FINITE s ==> !w M. w IN M.frame.world ==>
                (?ff. satis M w ff <=> (!f. f IN s ==> satis M w f))``,
Induct_on `FINITE s`
>> rpt strip_tac
>- (qexists_tac `TRUE` >> eq_tac
    >- (rpt strip_tac >> metis_tac[NOT_IN_EMPTY,TRUE_def,satis_def])
    >- metis_tac[TRUE_def,satis_def])
>- (`?BIGCONJ. satis M w BIGCONJ <=> (!f. f IN s ==> satis M w f)`
       by metis_tac[] >>
    qexists_tac `AND BIGCONJ e` >> eq_tac
    >- (rpt strip_tac >> `f = e \/ f IN s` by metis_tac[IN_INSERT]
        >- (rw[] >> `satis M w e` by metis_tac[satis_def,AND_def])
        >- (`satis M w BIGCONJ` by metis_tac[satis_def,AND_def] >>
            ‘∀f. f ∈ s ⇒ satis M w f’ by metis_tac[] >> metis_tac []))
    >- (rpt strip_tac >>
        ‘!f. (f = e \/ f IN s) ==> satis M w f’ by metis_tac[IN_INSERT] >>
        ‘!f. f IN s ==> satis M w f’ by metis_tac[] >>
        ‘satis M w BIGCONJ’  by metis_tac[] >>
        ‘satis M w e’  by metis_tac[] >> rw[satis_def,AND_def]))
);



Definition image_finite_def:
  image_finite M <=>
    !x. x IN M.frame.world ==> FINITE {y| y IN M.frame.world /\ M.frame.rel x y}
End



Theorem box_vac_true:
  ∀form w M.
    w ∈ M.frame.world ∧ ¬(?w'. w' IN M.frame.world /\ M.frame.rel w w') ==>
    satis M w (BOX form)
Proof rw[satis_def,BOX_def] >> metis_tac[IN_DEF]
QED



val diam_exist_true = store_thm(
"diam_exist_true",
``!M w. w IN M.frame.world /\ (?w'. w' IN M.frame.world /\ M.frame.rel w w') ==>
        satis M w (DIAM TRUE)``,
rw[satis_def,TRUE_def,IN_DEF] >> qexists_tac `w'` >> metis_tac[]);



val satis_in_world = store_thm(
"satis_in_world",
``!M w f. satis M w f ==> w IN M.frame.world``,
Induct_on `f` >> metis_tac[satis_def]);



val satis_AND = store_thm(
"satis_AND",
``!M w f1 f2. satis M w (AND f1 f2) <=> (satis M w f1 /\ satis M w f2)``,
rpt strip_tac >> eq_tac
>- (rpt strip_tac >> fs[satis_def,AND_def] >> metis_tac[])
>- (rpt strip_tac >> fs[satis_def,AND_def] >> metis_tac[satis_in_world]));



Theorem FINITE_BIGCONJ:
  !s. FINITE s ==> s <> {} ==>
      (v ∈ M.frame.world ∧
       (!v'. v' IN s ==> ?phi. satis M v phi /\ ¬satis M' v' phi)) ==>
      (?psi. satis M v psi /\ (!v'. v' IN s ==> ¬satis M' v' psi))
Proof
Induct_on `FINITE s` >> rpt strip_tac >- metis_tac[] >>
`e IN (e INSERT s)` by fs[INSERT_DEF] >>
‘∃phi. satis M v phi ∧ ¬satis M' e phi’ by metis_tac[] >>
‘∀v'. (v' = e \/ v' IN s) ⇒ ∃phi. satis M v phi ∧ ¬satis M' v' phi’
  by fs[INSERT_DEF] >>
‘∀v'. v' ∈ s ⇒ ∃phi. satis M v phi ∧ ¬satis M' v' phi’ by metis_tac[] >>
Cases_on `s <> {}`
>- (`∃psi. satis M v psi ∧ ∀v'. v' ∈ s ⇒ ¬satis M' v' psi` by metis_tac[] >>
    qexists_tac `AND psi phi` >> strip_tac
    >- metis_tac[satis_AND]
    >- (strip_tac >> strip_tac >> `v' = e \/ v' IN s` by fs[INSERT_DEF]
        >- rw[satis_AND]
        >- metis_tac[satis_AND]))
>- (‘s = {}’ by metis_tac[] >>
    qexists_tac `phi` >> strip_tac >- metis_tac[]
    >- (strip_tac >> strip_tac >> `v' = e \/ v' IN s` by fs[INSERT_DEF]
        >- metis_tac[] >- metis_tac[NOT_IN_EMPTY]))
QED

val thm_2_24_lemma = store_thm(
"thm_2_24_lemma",
``!M model M' model w w'.
    image_finite M /\ image_finite M' /\ w IN M.frame.world /\
    w' IN M'.frame.world ==>
    (!form. satis M w form <=> satis M' w' form) ==> bisim_world M M' w w'``,
rpt strip_tac
>> rw[bisim_world_def]
>> qexists_tac `λn1 n2. (!form. satis M n1 form <=> satis M' n2 form)`
>> rpt strip_tac
>-(
  rw[bisim_def]
  >- (rpt strip_tac >> simp[]
   >> SPOSE_NOT_THEN ASSUME_TAC
   >> `FINITE {u'| u' IN M'.frame.world /\ M'.frame.rel n2 u'}`
         by metis_tac[image_finite_def]
   >> `?u. u IN M'.frame.world /\ M'.frame.rel n2 u` by (
   `¬(!u. u IN M'.frame.world ==> ¬M'.frame.rel n2 u)` suffices_by metis_tac[]
   >> rpt strip_tac
   >> `satis M' n2 (BOX FALSE)` by metis_tac[box_vac_true]
   >> `satis M n1 (BOX FALSE)` by metis_tac[]
   >> `satis M n1 (NOT (DIAM TRUE))` by metis_tac[BOX_def,TRUE_def,satis_def]
   >> `¬(satis M n1 (DIAM TRUE))` by metis_tac[satis_def]
   >> `satis M n1 (DIAM TRUE)` by metis_tac[diam_exist_true]
   )
   >> `u IN {u' | u' ∈ M'.frame.world ∧ M'.frame.rel n2 u'}` by simp[]
   >> `{u' | u' ∈ M'.frame.world ∧ M'.frame.rel n2 u'} <> {}`
        by metis_tac[MEMBER_NOT_EMPTY]
   >> `∀n2'.
          n2' ∈ M'.frame.world ⇒ M'.frame.rel n2 n2' ==>
          ¬(∀form. satis M n1' form ⇔ satis M' n2' form)` by metis_tac[]
   >>  `∀n2'.
          n2' ∈ M'.frame.world /\ M'.frame.rel n2 n2' ==>
          ¬(∀form. satis M n1' form ⇔ satis M' n2' form)` by metis_tac[]
   >> `∀n2'.
          n2' ∈ M'.frame.world /\ M'.frame.rel n2 n2' ==>
          ¬(∀form. ¬(¬(satis M n1' form ⇔ satis M' n2' form)))` by metis_tac[]
   >> `∀n2'.
          n2' ∈ M'.frame.world /\ M'.frame.rel n2 n2' ==>
          (?form. ¬(satis M n1' form ⇔ satis M' n2' form))` by metis_tac[]
   >> `∀n2'.
          n2' ∈ M'.frame.world /\ M'.frame.rel n2 n2' ==>
          (?form. satis M n1' form /\ ¬satis M' n2' form)`
        by metis_tac[satis_def]
   >> `∀n2'. n2' IN {u' | u' ∈ M'.frame.world ∧ M'.frame.rel n2 u'} ==>
       ∃form. satis M n1' form ∧ ¬satis M' n2' form` by simp[]
   >> `?psi. satis M n1' psi /\
             (!n2'. n2' IN {u' | u' ∈ M'.frame.world ∧ M'.frame.rel n2 u'} ==>
             ¬satis M' n2' psi)` by metis_tac[FINITE_BIGCONJ]
   >> `satis M n1 (DIAM psi)`
         by (`n1 ∈ M.frame.world ∧
              ∃v. v ∈ M.frame.rel n1 ∧ v ∈ M.frame.world ∧ satis M v psi`
                suffices_by metis_tac[satis_def] >> metis_tac[IN_DEF])
   >> `satis M' n2 (DIAM psi)` by metis_tac[]
   >> `?n2'. n2' IN M'.frame.world /\ M'.frame.rel n2 n2' /\ satis M' n2' psi`
         by metis_tac[satis_def,IN_DEF]
   >> `∀n2'. n2' ∈ M'.frame.world ∧ M'.frame.rel n2 n2' ⇒ ¬satis M' n2' psi`
         by simp[]
   >> metis_tac[])
  >- (rpt strip_tac >> simp[]
   >> SPOSE_NOT_THEN ASSUME_TAC
   >> `FINITE {u'| u' IN M.frame.world /\ M.frame.rel n1 u'}`
         by metis_tac[image_finite_def]
   >> `?u. u IN M.frame.world /\ M.frame.rel n1 u` by (
   `¬(!u. u IN M.frame.world ==> ¬M.frame.rel n1 u)` suffices_by metis_tac[]
   >> rpt strip_tac
   >> `satis M n1 (BOX FALSE)` by metis_tac[box_vac_true]
   >> `satis M' n2 (BOX FALSE)` by metis_tac[]
   >> `satis M' n2 (NOT (DIAM TRUE))` by metis_tac[BOX_def,TRUE_def,satis_def]
   >> `¬(satis M' n2 (DIAM TRUE))` by metis_tac[satis_def]
   >> `satis M' n2 (DIAM TRUE)` by metis_tac[diam_exist_true]
   )
   >> `u IN {u' | u' ∈ M.frame.world ∧ M.frame.rel n1 u'}` by simp[]
   >> `{u' | u' ∈ M.frame.world ∧ M.frame.rel n1 u'} <> {}`
        by metis_tac[MEMBER_NOT_EMPTY]
   >> `∀n1'.
          n1' ∈ M.frame.world ⇒ M.frame.rel n1 n1' ==>
          ¬(∀form. satis M' n2' form ⇔ satis M n1' form)` by metis_tac[]
   >> `∀n1'.
          n1' ∈ M.frame.world /\ M.frame.rel n1 n1' ==>
          ¬(∀form. satis M' n2' form ⇔ satis M n1' form)` by metis_tac[]
   >> `∀n1'.
          n1' ∈ M.frame.world /\ M.frame.rel n1 n1' ==>
          ¬(∀form. ¬(¬(satis M' n2' form ⇔ satis M n1' form)))` by metis_tac[]
   >> `∀n1'.
          n1' ∈ M.frame.world /\ M.frame.rel n1 n1' ==>
          (?form. ¬(satis M' n2' form ⇔ satis M n1' form))` by metis_tac[]
   >> `∀n1'.
          n1' ∈ M.frame.world /\ M.frame.rel n1 n1' ==>
          (?form. satis M' n2' form /\ ¬satis M n1' form)`
        by metis_tac[satis_def]
   >> `∀n1'. n1' IN {u' | u' ∈ M.frame.world ∧ M.frame.rel n1 u'} ==>
       ∃form. satis M' n2' form ∧ ¬satis M n1' form` by simp[]
   >> `?psi. satis M' n2' psi /\
             !n1'. n1' ∈ {u' | u' ∈ M.frame.world ∧ M.frame.rel n1 u'} ==>
                   ¬satis M n1' psi` by metis_tac[FINITE_BIGCONJ]
   >> `satis M' n2 (DIAM psi)`
         by (`n2 ∈ M'.frame.world ∧
              ∃v. v ∈ M'.frame.rel n2 ∧ v ∈ M'.frame.world ∧ satis M' v psi`
                suffices_by metis_tac[satis_def] >> metis_tac[IN_DEF])
   >> `satis M n1 (DIAM psi)` by metis_tac[]
   >> `?n1'. n1' IN M.frame.world /\ M.frame.rel n1 n1' /\ satis M n1' psi`
         by metis_tac[satis_def,IN_DEF]
   >> `∀n1'. n1' ∈ M.frame.world ∧ M.frame.rel n1 n1' ⇒ ¬satis M n1' psi`
         by simp[]
   >> metis_tac[])
)
>- simp[]
);



val thm_2_24_lemma2 = store_thm(
"thm_2_24_lemma2",
``!M M' w w'.
    modal_eq M M' w w' <=> (!form. satis M w form <=> satis M' w' form)``,
fs[modal_eq_def,tau_theory_def] >> simp[pred_setTheory.EXTENSION]);



Theorem thm_2_24_half:
!M M' w:'a w':'a.
  image_finite M ∧ image_finite M' ∧ w ∈ M.frame.world ∧ w' ∈ M'.frame.world ==>
  (modal_eq M M' w w'==> bisim_world M M' w w')
Proof
rpt strip_tac
>> `!form. satis M w form <=> satis M' w' form` by metis_tac[thm_2_24_lemma2]
>> metis_tac[thm_2_24_lemma]
QED



Theorem thm_2_24:
  !M M' w:'a w':'a.
    image_finite M /\ image_finite M' /\ w IN M.frame.world /\
    w' IN M'.frame.world ==> (modal_eq M M' w w'<=> bisim_world M M' w w')
Proof
rpt strip_tac >> eq_tac
>- (strip_tac >> metis_tac[thm_2_24_half])
>- (strip_tac >> metis_tac[thm_2_20])
QED

val _ = export_theory();
