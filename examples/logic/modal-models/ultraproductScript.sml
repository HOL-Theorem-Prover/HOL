open HolKernel Parse boolLib bossLib;
open ultrafilterTheory;
open HolKernel Parse boolLib bossLib;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;
open pairTheory;
open listTheory;
open rich_listTheory;
open combinTheory;
open folLangTheory;
open folModelsTheory;
open chap2_4revisedTheory;
open equiv_on_partitionTheory;
val _ = new_theory "ultraproduct";

val Cart_prod_def = Define`
  Cart_prod I A = {f | !i. i IN I ==> f i IN A i}`;

val Uequiv_def = Define`
  Uequiv U I A f g <=> ultrafilter U I /\
                     (!i. i IN I ==> A i <> {}) /\
                     f IN Cart_prod I A /\ g IN Cart_prod I A /\
                     {i | i IN I /\ f i = g i} IN U`;

Theorem prop_A_16:
  !U I A. ultrafilter U I ==> (Uequiv U I A) equiv_on Cart_prod I A
Proof
  rw[Uequiv_def,Cart_prod_def,equiv_on_def] (* 4 *)
  >- metis_tac[MEMBER_NOT_EMPTY]
  >- metis_tac[ultrafilter_def,proper_filter_def,filter_def]
  >- simp[EQ_SYM_EQ, Excl "NORMEQ_CONV"]
  >- (‘{i | i ∈ I' ∧ x i = y i} ∩ {i | i ∈ I' ∧ y i = z i} IN U’
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     ‘{i | i ∈ I' ∧ x i = y i} ∩ {i | i ∈ I' ∧ y i = z i} ⊆
      {i | i ∈ I' ∧ x i = z i}’ by rw[SUBSET_DEF,INTER_DEF,EXTENSION] >>
     ‘{i | i ∈ I' ∧ x i = z i} ⊆ I'’ by rw[SUBSET_DEF] >>
     metis_tac[ultrafilter_def,proper_filter_def,filter_def])
QED

Definition ultraproduct_def:
  ultraproduct U I A = partition (Uequiv U I A) (Cart_prod I A)
End

Theorem ultraproduct_same_eqclass:
  !U I A. ultrafilter U I ==>
      !fc. fc IN (ultraproduct U I A) ==>
         !x y. x IN fc /\ y IN fc ==>
              {i | i IN I /\ x i = y i} IN U
Proof
  rw[] >> fs[ultraproduct_def,partition_def] >> rfs[] >> drule prop_A_16 >> rw[] >>
  fs[equiv_on_def] >> `Uequiv U I' A x y` by metis_tac[] >> fs[Uequiv_def]
QED


Theorem ultraproduct_go_to_same_eq_class:
  !U I A. ultrafilter U I ==>
     !x y. (!i. i IN I ==> (x i) IN (A i)) /\
           (!i. i IN I ==> (y i) IN (A i)) /\
           ({i | i IN I /\ x i = y i} IN U) ==>
       !fc. fc IN (ultraproduct U I A) ==> (y IN fc <=> x IN fc)
Proof
  rw[] >> drule prop_A_16 >> rw[] >> fs[ultraproduct_def,partition_def,equiv_on_def] >>
  `y ∈ Cart_prod I' A /\ x ∈ Cart_prod I' A` by rw[Cart_prod_def] >>
  `Uequiv U I' A x y` by (rw[Uequiv_def] >> rw[GSYM MEMBER_NOT_EMPTY] >>
                         qexists_tac `x i` >> metis_tac[]) >>
  metis_tac[]
QED


Theorem ultraproduct_eqclass_non_empty:
  !U I A. ultrafilter U I ==>
      !fc. fc IN (ultraproduct U I A) ==> fc <> {}
Proof
  rw[ultraproduct_def] >> drule prop_A_16 >> rw[] >> metis_tac[EMPTY_NOT_IN_partition]
QED
Theorem eqc_CHOICE:
!U I. ultrafilter U I ==>
   !A fc. fc IN (ultraproduct U I A) ==>
          fc = {g | Uequiv U I A g (CHOICE fc)}
Proof
rw[EXTENSION,Uequiv_def,EQ_IMP_THM] (* 5 *)
>- (fs[ultraproduct_def,partition_def,Cart_prod_def] >>
    metis_tac[MEMBER_NOT_EMPTY])
>- (fs[ultraproduct_def,partition_def,Cart_prod_def] >> rfs[])
>- (`fc <> {}` by metis_tac[ultraproduct_eqclass_non_empty] >>
    `CHOICE fc IN fc` by metis_tac[CHOICE_DEF] >>
    fs[ultraproduct_def,partition_def,Cart_prod_def] >>
    rfs[])
>- (irule ultraproduct_same_eqclass >> rw[] >>
    map_every qexists_tac [`A`,`fc`] >> rw[] >>
    `fc <> {}` by metis_tac[ultraproduct_eqclass_non_empty] >>
    metis_tac[CHOICE_DEF])
>- (`CHOICE fc IN fc /\ (CHOICE fc IN fc <=> x IN fc)` suffices_by metis_tac[] >>
    `fc <> {}` by metis_tac[ultraproduct_eqclass_non_empty] >>
    `CHOICE fc IN fc` by metis_tac[CHOICE_DEF] >>
    strip_tac >- rw[] >>
    irule ultraproduct_go_to_same_eq_class >>
    map_every qexists_tac [`A`,`I'`,`U`] >> rw[] (* 2 same*) >>
    fs[Cart_prod_def])
QED



val models2worlds_def = Define`
  models2worlds MS = \i. (MS i).frame.world`;

val ultraproduct_model_def = Define`
  ultraproduct_model U I MS = <| frame := <| world := ultraproduct U I (models2worlds MS);
                                               rel := \fu gu. (?f g. f IN fu /\ g IN gu /\
                                                              {i | i IN I /\ (MS i).frame.rel (f i) (g i)} IN U) |>;
                                  valt := \p fu. (?f. f IN fu /\ {i | i IN I /\ (f i) IN (MS i).valt p} IN U) |>`;


val ultraproduct_world_NOT_EMPTY = store_thm(
  "ultraproduct_world_NOT_EMPTY",
  ``!U J MS v. ultrafilter U J ==> v IN (ultraproduct_model U J MS).frame.world ==> v <> {}``,
  rw[ultraproduct_def,ultraproduct_model_def, models2worlds_def] >> metis_tac[prop_A_16,EMPTY_NOT_IN_partition]);

val ultraproduct_world = store_thm(
  "ultraproduct_world",
  ``!U J MS.
    ultrafilter U J ==>
       (!v.
           v ∈ (ultraproduct_model U J MS).frame.world <=>
               (!i. i IN J ==> (MS i).frame.world <> {}) /\
               (∃x.
                   (∀i. i ∈ J ⇒ x i ∈ (MS i).frame.world) /\
                   v = {y | (∀i. i ∈ J ⇒ y i ∈ (MS i).frame.world) /\ {i | i ∈ J ∧ x i = y i} ∈ U}))``,
  rw[ultraproduct_def,ultraproduct_model_def, models2worlds_def,partition_def,Uequiv_def,Cart_prod_def] >> rw[EQ_IMP_THM] (* 3 *)
  >- metis_tac[MEMBER_NOT_EMPTY]
  >> qexists_tac `x` >> rw[EXTENSION,EQ_IMP_THM] >> metis_tac[]);


val ultraproduct_rel = save_thm(
  "ultraproduct_rel",
  ``(ultraproduct_model U J MS).frame.rel w v``
    |> SIMP_CONV (srw_ss()) [ultraproduct_def,ultraproduct_model_def, models2worlds_def,partition_def,Uequiv_def,Cart_prod_def])

val ultraproduct_valt = save_thm(
  "ultraproduct_valt",
  ``v IN (ultraproduct_model U J MS).valt p``
    |> SIMP_CONV (srw_ss()) [ultraproduct_def,ultraproduct_model_def, models2worlds_def,partition_def,Uequiv_def,Cart_prod_def])



val ultraproduct_world_constant = store_thm(
  "ultraproduct_world_constant",
  ``!U J MS w.
  ultrafilter U J ⇒
  (∀i. i ∈ J ⇒ MS i = M) ⇒
  ({fw | Uequiv U J (models2worlds MS) (λi. w) fw} ∈ (ultraproduct_model U J MS).frame.world
  <=> w ∈ M.frame.world)``,
  rw[EQ_IMP_THM]
  >- (`?i. i IN J`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def,MEMBER_NOT_EMPTY] >>
     `{fw | Uequiv U J (models2worlds MS) (λi. w) fw} <> {}`
       by metis_tac[ultraproduct_world_NOT_EMPTY] >> fs[ultraproduct_world] >>
     fs[Uequiv_def,models2worlds_def,Cart_prod_def] >>
     `?a. a IN {fw |
       ultrafilter U J ∧ (∀i. i ∈ J ⇒ (MS i).frame.world ≠ ∅) ∧
       (∀i. i ∈ J ⇒ w ∈ (MS i).frame.world) ∧
       (∀i. i ∈ J ⇒ fw i ∈ (MS i).frame.world) ∧
       {i | i ∈ J ∧ w = fw i} ∈ U}` by metis_tac[MEMBER_NOT_EMPTY] >> fs[] >> metis_tac[])
  >- (rw[ultraproduct_world] (* 2 *)
     >- metis_tac[MEMBER_NOT_EMPTY]
     >- (qexists_tac `\i.w` >> rw[Uequiv_def,models2worlds_def,Cart_prod_def] >>
        simp[EXTENSION] >> metis_tac[])));



val ultrapower_valt_well_defined = store_thm(
  "ultrapower_valt_well_defined",
  ``!U J Ms. ultrafilter U J ==> !f g. Uequiv U J (models2worlds Ms) f g ==>
             ({i | i IN J /\ (f i) IN (Ms i).valt p} IN U <=>
             {i | i IN J /\ (g i) IN (Ms i).valt p} IN U)``,
  rw[Uequiv_def,models2worlds_def,Cart_prod_def] >> eq_tac >> rw[]
  >- (`{i | i IN J /\ f i = g i} ∩ {i | i IN J /\ f i IN (Ms i).valt p} IN U`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ g i IN (Ms i).valt p} ⊆ J` by fs[SUBSET_DEF] >>
     `({i | i IN J /\ f i = g i} ∩ {i | i IN J /\ f i IN (Ms i).valt p}) ⊆
     {i | i IN J /\ g i IN (Ms i).valt p}` suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     rw[INTER_DEF,SUBSET_DEF] >> metis_tac[])
  >- (`{i | i IN J /\ f i = g i} ∩ {i | i IN J /\ g i IN (Ms i).valt p} IN U`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ f i IN (Ms i).valt p} ⊆ J` by fs[SUBSET_DEF] >>
     `({i | i IN J /\ f i = g i} ∩ {i | i IN J /\ g i IN (Ms i).valt p}) ⊆
     {i | i IN J /\ f i IN (Ms i).valt p}` suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     rw[INTER_DEF,SUBSET_DEF] >> metis_tac[]));


Theorem Los_modal_thm:
  ∀U J Ms phi fc.
            (ultrafilter U J /\
                fc ∈ (ultraproduct_model U J Ms).frame.world) ⇒
                (satis (ultraproduct_model U J Ms) fc phi ⇔
                 ∃f. f ∈ fc ∧ {i | i ∈ J ∧ satis (Ms i) (f i) phi} ∈ U)
Proof
`!U J Ms. ultrafilter U J ==>
             !phi fc. fc IN (ultraproduct_model U J Ms).frame.world ==>
                      (satis (ultraproduct_model U J Ms) fc phi <=>
                      ?f. f IN fc /\ {i | i IN J /\ satis (Ms i) (f i) phi} IN U)` suffices_by metis_tac[] >>
  strip_tac >> strip_tac >> strip_tac  >> strip_tac >> Induct_on `phi` >> rw[] (* 5 *)
(*-----------------------------block 1 `` VAR case``------------------------------------- *)
>-
(fs[satis_def,ultraproduct_world,ultraproduct_valt] >> eq_tac >> rw[] (* 2 *)
>- (qexists_tac `f` >> rw[] >> fs[] >>
        `{i | i IN J /\ f i IN (Ms i).frame.world /\ f i IN (Ms i).valt n} =
        {i | i IN J /\ f i IN (Ms i).valt n}` suffices_by metis_tac[] >>
        simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >>
        `(!i. i IN J ==> (Ms i).frame.world <> {}) /\
         ?x.
            (!i. i IN J ==> x i IN (Ms i).frame.world) /\
            fc =
            {y |
             (!i. i IN J ==> y i IN (Ms i).frame.world) /\
             {i | i IN J /\ x i = y i} IN U}` by metis_tac[ultraproduct_world] >>
        `f IN {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x' i = y i} IN U}`
          by metis_tac[] >> fs[])
>- (`(!i. i IN J ==> (Ms i).frame.world <> {}) /\
   ?x. (!i. i IN J ==> x i IN (Ms i).frame.world) /\
       fc = {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x i = y i} IN U}`
     by metis_tac[ultraproduct_world] >>
   fs[] >> qexists_tac `f` >> rw[] >>
   `{i | i IN J /\ f i IN (Ms i).frame.world /\ f i IN (Ms i).valt n} = {i | i IN J /\ f i IN (Ms i).valt n}`
     by rw[EXTENSION,EQ_IMP_THM] >>
   metis_tac[]))
(*-----------------------------block 2 `` \/ case``------------------------------------- *)
>-
(rw[satis_def,EQ_IMP_THM,ultraproduct_world] (* 3 *)
>- (qexists_tac `f` >> rw[] >>
        `{i | i IN J /\ (satis (Ms i) (f i) phi \/ satis (Ms i) (f i) phi')} ⊆ J` by fs[SUBSET_DEF] >>
        `{i | i IN J /\ satis (Ms i) (f i) phi} ⊆ {i | i IN J /\ (satis (Ms i) (f i) phi \/ satis (Ms i) (f i) phi')}` suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >> fs[SUBSET_DEF])
>- (qexists_tac `f` >> rw[] >>
        `{i | i IN J /\ (satis (Ms i) (f i) phi \/ satis (Ms i) (f i) phi')} ⊆ J` by fs[SUBSET_DEF] >>
        `{i | i IN J /\ satis (Ms i) (f i) phi'} ⊆ {i | i IN J /\ (satis (Ms i) (f i) phi \/ satis (Ms i) (f i) phi')}` suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >> fs[SUBSET_DEF])
>- (`{i | i IN J /\ (satis (Ms i) (f i) phi \/ satis (Ms i) (f i) phi')} =
        {i | i IN J /\ satis (Ms i) (f i) phi} ∪ {i | i IN J /\ satis (Ms i) (f i) phi'}`
          by (rw[EXTENSION,EQ_IMP_THM] >> metis_tac[]) >>
        `{i | i IN J /\ satis (Ms i) (f i) phi} ⊆ J /\
         {i | i IN J /\ satis (Ms i) (f i) phi'} ⊆ J` by fs[SUBSET_DEF] >>
        `{i | i IN J /\ satis (Ms i) (f i) phi} IN U \/
        {i | i IN J /\ satis (Ms i) (f i) phi'} IN U` by metis_tac[ultrafilter_UNION]
        >> metis_tac[]))
(*-----------------------------block 3 `` FALSE case``------------------------------------- *)
>-
(`((satis (ultraproduct_model U J Ms) fc FALSE) = F) /\
((?f. f IN fc /\ {i | i IN J /\ satis (Ms i) (f i) FALSE} IN U) = F)` suffices_by metis_tac[] >> rw[] (* 2 *)
>- rw[satis_def]
>- (`{i | i IN J /\ satis (Ms i) (f i) FALSE} NOTIN U` suffices_by metis_tac[] >>
   `{i | i IN J /\ satis (Ms i) (f i) FALSE} = {}`
     by rw[EXTENSION,EQ_IMP_THM,satis_def] >>
   metis_tac[EMPTY_NOTIN_ultrafilter]))
(*-----------------------------block 4 `` ¬ case``------------------------------------- *)
>-
(rw[satis_def,EQ_IMP_THM,ultraproduct_world] (* 2 *)
>- (`(!i. i IN J ==> (Ms i).frame.world <> {}) /\
    ?x. (!i. i IN J ==> x i IN (Ms i).frame.world) /\
        fc = {y |
             (!i. i IN J ==> y i IN (Ms i).frame.world) /\
             {i | i IN J /\ x i = y i} IN U}` by metis_tac[ultraproduct_world] >>
   qexists_tac `x` >> rw[] (* 2 *)
   >- metis_tac[ultrafilter_def,proper_filter_def,filter_def]
   >- (`x IN {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x i = y i} IN U}`
        by (rw[] >> metis_tac[ultrafilter_def,proper_filter_def,filter_def]) >>
      `{i | i IN J /\ satis (Ms i) (x i) phi} NOTIN U` by metis_tac[] >>
      `{i | i IN J /\ satis (Ms i) (x i) phi} IN (POW J)` by fs[SUBSET_DEF,POW_DEF] >>
      `J DIFF {i | i IN J /\ satis (Ms i) (x i) phi} IN U` by metis_tac[ultrafilter_def] >>
      fs[DIFF_DEF] >>
      `{i | i IN J /\ x i IN (Ms i).frame.world /\ ~satis (Ms i) (x i) phi} =
      {x' | x' IN J /\ (x' NOTIN J \/ ~satis (Ms x') (x x') phi)}`
        by rw[EXTENSION,EQ_IMP_THM] >>
      metis_tac[]))
>- (`!f'. f' IN fc ==> {i | i IN J /\ satis (Ms i) (f' i) phi} NOTIN U` suffices_by metis_tac[] >> rw[] >>
   `(!i. i IN J ==> (Ms i).frame.world <> {}) /\
    ?x. (!i. i IN J ==> x i IN (Ms i).frame.world) /\
        fc = {y |
             (!i. i IN J ==> y i IN (Ms i).frame.world) /\
             {i | i IN J /\ x i = y i} IN U}` by metis_tac[ultraproduct_world] >>
   fs[] >>
   `{i | i IN J /\ satis (Ms i) (f' i) phi} IN (POW J)` by fs[SUBSET_DEF,POW_DEF] >>
   `J DIFF {i | i IN J /\ satis (Ms i) (f' i) phi} IN U` suffices_by metis_tac[ultrafilter_def] >>
   rw[DIFF_DEF] >>
   `{x | x IN J /\ (x NOTIN J \/ ~satis (Ms x) (f' x) phi)} =
   {x | x IN J /\ ~satis (Ms x) (f' x) phi}` by rw[EXTENSION,EQ_IMP_THM] >> fs[] >>
   `{i | i IN J /\ f i IN (Ms i).frame.world /\ ~satis (Ms i) (f i) phi} ∩
   {i | i IN J /\ x i = f i} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
   `({i | i IN J /\ f i IN (Ms i).frame.world /\ ~satis (Ms i) (f i) phi} ∩
   {i | i IN J /\ x i = f i}) ∩  {i | i IN J /\ x i = f' i} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
   `({i | i IN J /\ f i IN (Ms i).frame.world /\ ~satis (Ms i) (f i) phi} ∩
   {i | i IN J /\ x i = f i}) ∩  {i | i IN J /\ x i = f' i} ⊆
   {x | x IN J /\ ~satis (Ms x) (f' x) phi}` by (rw[SUBSET_DEF] >> metis_tac[]) >>
   `{x | x IN J /\ ~satis (Ms x) (f' x) phi} ⊆ J` by rw[SUBSET_DEF] >>
   metis_tac[ultrafilter_def,proper_filter_def,filter_def]))
(*-----------------------------block 4 ``DIAM case``------------------------------------- *)
>-
(rw[satis_def,EQ_IMP_THM,ultraproduct_world] (* 2 *)
(*-------------------------------half 1---------------------------------------------------*)
>- (`(!i. i IN J ==> (Ms i).frame.world <> {}) /\
   ?x. (!i. i IN J ==> x i IN (Ms i).frame.world) /\
   fc = {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x i = y i} IN U}` by metis_tac[ultraproduct_world] >> qexists_tac `x'` >> rw[] >> fs[] (* 2 *)
  >- metis_tac[ultrafilter_def,proper_filter_def,filter_def]
  >- (`?f g.
      f IN {y |
         (!i. i IN J ==> y i IN (Ms i).frame.world) /\
         {i | i IN J /\ x' i = y i} IN U} /\ g IN {y |
         (!i. i IN J ==> y i IN (Ms i).frame.world) /\
         {i | i IN J /\ x i = y i} IN U} /\
      {i | i IN J /\ (Ms i).frame.rel (f i) (g i)} IN U` by metis_tac[ultraproduct_rel] >> fs[] >>
     `{i | i IN J /\ x' i = f i} ∩ {i | i IN J /\ (Ms i).frame.rel (f i) (g i)} IN U`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ x' i = f i} INTER {i | i IN J /\ (Ms i).frame.rel (f i) (g i)} ⊆ {i | i IN J /\ (Ms i).frame.rel (x' i) (g i)} `
       by rw[SUBSET_DEF] >>
     `{i | i IN J /\ (Ms i).frame.rel (x' i) (g i)} ⊆ J` by fs[SUBSET_DEF] >>
     `{i | i IN J /\ (Ms i).frame.rel (x' i) (g i)} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ satis (Ms i) (g i) phi} IN U`
       by (`?r. r IN {y |
          (!i. i IN J ==> y i IN (Ms i).frame.world) /\
          {i | i IN J /\ x i = y i} IN U} /\ {i | i IN J /\ satis (Ms i) (r i) phi} IN U` by metis_tac[satis_in_world] >> fs[] >> `{i | i IN J /\ satis (Ms i) (r i) phi} ∩ {i | i IN J /\ x i = r i} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
          `{i | i IN J /\ satis (Ms i) (r i) phi} INTER {i | i IN J /\ x i = r i} ⊆ {i | i IN J /\ satis (Ms i) (x i) phi}` by fs[SUBSET_DEF] >>
          `{i | i IN J /\ satis (Ms i) (x i) phi} ⊆ J` by fs[SUBSET_DEF] >>
          `{i | i IN J /\ satis (Ms i) (x i) phi} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
          `{i | i IN J /\ g i = x i} = {i | i IN J /\ x i = g i}` by rw[EXTENSION,EQ_IMP_THM] >>
          `{i | i IN J /\ satis (Ms i) (x i) phi} INTER {i | i IN J /\ g i = x i} IN U` by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
          `{i | i IN J /\ satis (Ms i) (x i) phi} INTER {i | i IN J /\ g i = x i} ⊆ {i | i IN J /\ satis (Ms i) (g i) phi}` by fs[SUBSET_DEF] >>
          `{i | i IN J /\ satis (Ms i) (g i) phi} ⊆ J` by fs[SUBSET_DEF] >>
          metis_tac[ultrafilter_def,proper_filter_def,filter_def]) >>
     `{i | i IN J /\ (Ms i).frame.rel (x' i) (g i)} ∩ {i | i IN J /\ satis (Ms i) (g i) phi} IN U`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ (Ms i).frame.rel (x' i) (g i) /\ satis (Ms i) (g i) phi} =
     {i | i IN J /\ (Ms i).frame.rel (x' i) (g i)} ∩ {i | i IN J /\ satis (Ms i) (g i) phi}`
       by rw[EXTENSION,EQ_IMP_THM] >>
     `{i | i IN J /\ (Ms i).frame.rel (x' i) (g i) /\ satis (Ms i) (g i) phi} ⊆
     {i | i IN J /\ x' i IN (Ms i).frame.world /\
     ?v. (Ms i).frame.rel (x' i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}`
       by (rw[SUBSET_DEF] >> qexists_tac `g x''` >> rw[]) >>
     `{i | i IN J /\ x' i IN (Ms i).frame.world /\
      ?v. (Ms i).frame.rel (x' i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} ⊆ J` by fs[SUBSET_DEF] >>
      metis_tac[ultrafilter_def,proper_filter_def,filter_def]))
(*-------------------------------half 2---------------------------------------------------*)
>- (`{i | i IN J /\ f i IN (Ms i).frame.world /\
      ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} <> {}`
        by metis_tac[EMPTY_NOTIN_ultrafilter] >> fs[GSYM MEMBER_NOT_EMPTY] >>
     simp[PULL_EXISTS] >> rw[ultraproduct_rel] >>
     `?x g. (f IN fc /\
     ((!i. i IN J ==> g i IN (Ms i).frame.world) /\
     {i | i IN J /\ x i = g i} IN U) /\
     {i | i IN J /\ (Ms i).frame.rel (f i) (g i)} IN U) /\
     (!i. i IN J ==> (Ms i).frame.world <> {}) /\
     (!i. i IN J ==> x i IN (Ms i).frame.world) /\
     satis (ultraproduct_model U J Ms)
     {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x i = y i} IN U} phi`
     suffices_by (rw[] >> qexists_tac `x'` >> rw[] (* 2 *)
                 >- (map_every qexists_tac [`f`,`g`] >> rw[])
                 >- metis_tac[MEMBER_NOT_EMPTY]) >>
     map_every qexists_tac
     [`\i. if (?v.
          (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\
          satis (Ms i) v phi) then CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
          else CHOICE (Ms i).frame.world`,
     `\i. if (?v.
          (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\
          satis (Ms i) v phi) then CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
          else CHOICE (Ms i).frame.world`]>> rw[] (* 8 *)
     >- (`{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} <> {}`
          by (`v' IN {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}` by fs[] >>
             metis_tac[MEMBER_NOT_EMPTY]) >>
        `CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} IN
        {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}` by metis_tac[CHOICE_DEF] >>
        fs[])
     >- (`!i. i IN J ==> (Ms i).frame.world <> {}` by metis_tac[ultraproduct_world] >>
        `(Ms i).frame.world <> {}` by metis_tac[] >> metis_tac[CHOICE_DEF])
     >- metis_tac[ultrafilter_def,proper_filter_def,filter_def]
     >- (`{i | i IN J /\ f i IN (Ms i).frame.world /\
         ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} ⊆
        {i | i IN J /\ (Ms i).frame.rel (f i)
        (if
           (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
        then
            CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
        else CHOICE (Ms i).frame.world)}`
          by (rw[SUBSET_DEF] >>
             `{v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi} <> {}`
               by (`v' IN {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi}`
                     by fs[] >>
                  metis_tac[MEMBER_NOT_EMPTY]) >>
             `CHOICE {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi} IN
             {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi}`
               by metis_tac[CHOICE_DEF] >> fs[]) >>
        `{i | i IN J /\ (Ms i).frame.rel (f i)
        (if
           (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
        then
            CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
        else CHOICE (Ms i).frame.world)} ⊆ J` by fs[SUBSET_DEF] >>
        metis_tac[ultrafilter_def,proper_filter_def,filter_def])
     >- metis_tac[ultraproduct_world]
     >- (`{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} <> {}`
          by (`v' IN {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}` by fs[] >>
             metis_tac[MEMBER_NOT_EMPTY]) >>
        `CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} IN
        {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}` by metis_tac[CHOICE_DEF] >>
        fs[])
     >- (`!i. i IN J ==> (Ms i).frame.world <> {}` by metis_tac[ultraproduct_world] >>
        `(Ms i).frame.world <> {}` by metis_tac[] >> metis_tac[CHOICE_DEF])
     >- (`{i | i IN J /\
        satis (Ms i)
        (if
           (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
        then
            CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
        else CHOICE (Ms i).frame.world) phi} IN U`
          by (`{i | i IN J /\ f i IN (Ms i).frame.world /\
             ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} ⊆
             {i | i IN J /\ satis (Ms i)
             (if
             (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
             then
             CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
             else CHOICE (Ms i).frame.world) phi}`
               by (rw[SUBSET_DEF] >>
                  `{v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi} <> {}`
                    by (`v' IN {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi}`
                          by fs[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
                  `CHOICE {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi} IN
                  {v | (Ms x').frame.rel (f x') v /\ v IN (Ms x').frame.world /\ satis (Ms x') v phi}`
                    by metis_tac[CHOICE_DEF] >> fs[]) >>
             `{i | i IN J /\ satis (Ms i)
             (if
             (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
             then
             CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
             else CHOICE (Ms i).frame.world) phi} ⊆ J` by fs[SUBSET_DEF] >>
             metis_tac[ultrafilter_def,proper_filter_def,filter_def]) >>
        `{y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\
              {i | i IN J /\
                  (if
                  ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi
                  then
                  CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
                  else CHOICE (Ms i).frame.world) = y i} IN U} IN (ultraproduct_model U J Ms).frame.world`
          by
          (`!i. i IN J ==> (Ms i).frame.world <> {}` by metis_tac[ultraproduct_world] >>
          `?x.
            (!i. i IN J ==> x i IN (Ms i).frame.world) /\
          {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\
              {i | i IN J /\
                  (if
                  ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi
                  then
                  CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
                  else CHOICE (Ms i).frame.world) = y i} IN U} =
          {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\ {i | i IN J /\ x i = y i} IN U}`
          suffices_by metis_tac[ultraproduct_world] >>
          qexists_tac
          `\i. (if
             (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
             then
             CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
             else CHOICE (Ms i).frame.world)` >> rw[] (* 2 *)
          >- (`{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} <> {}`
               by (`v' IN {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}`
                     by fs[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
             `CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} IN
             {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}`
               by metis_tac[CHOICE_DEF] >> fs[])
          >- metis_tac[CHOICE_DEF]) >>
        `(\i. (if
             (?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi)
             then
             CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
             else CHOICE (Ms i).frame.world)) IN
        {y | (!i. i IN J ==> y i IN (Ms i).frame.world) /\
              {i | i IN J /\
                  (if
                  ?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi
                  then
                  CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}
                  else CHOICE (Ms i).frame.world) = y i} IN U}`
          by (rw[] (* 2 *)
             >- (Cases_on `?v. (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi` (* 2 *)
                >- (rw[] >>
                   `{v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} <> {}`
                     by (`v' IN {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}`
                           by fs[] >> metis_tac[MEMBER_NOT_EMPTY]) >>
                   `CHOICE {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi} IN
                   {v | (Ms i).frame.rel (f i) v /\ v IN (Ms i).frame.world /\ satis (Ms i) v phi}`
                     by metis_tac[CHOICE_DEF] >> fs[])
                >- (rw[] >> metis_tac[CHOICE_DEF,ultraproduct_world]))
             >- metis_tac[ultrafilter_def,proper_filter_def,filter_def]) >> metis_tac[])))
QED



val prop_2_71 = store_thm(
  "prop_2_71",
  ``!U J Ms. (!i. i IN J ==> (Ms i) = M) /\ ultrafilter U J ==>
         !phi w. satis (ultraproduct_model U J Ms) {fw | Uequiv U J (models2worlds Ms) (\i.w) fw} phi <=> satis M w phi``,
  rw[EQ_IMP_THM] (* 2 *)
  >- (`!phi fc.
              fc IN (ultraproduct_model U J Ms).frame.world ==>
              (satis (ultraproduct_model U J Ms) fc phi <=>
               ?f.
                  f IN fc /\
                  {i | i IN J /\ satis (Ms i) (f i) phi} IN U)` by metis_tac[Los_modal_thm] >>
     `{fw | Uequiv U J (models2worlds Ms) (\i. w) fw} IN (ultraproduct_model U J Ms).frame.world`
       by metis_tac[satis_in_world] >>
     `?f. f IN {fw | Uequiv U J (models2worlds Ms) (\i. w) fw} /\ {i | i IN J /\ satis (Ms i) (f i) phi} IN U`
       by metis_tac[] >>
     fs[Uequiv_def,models2worlds_def,Cart_prod_def] >>
     `{i | i IN J /\ w = f i} ∩ {i | i IN J /\ satis (Ms i) (f i) phi} IN U`
       by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
     `{i | i IN J /\ w = f i} ∩ {i | i IN J /\ satis (Ms i) (f i) phi} <> {}`
       by metis_tac[EMPTY_NOTIN_ultrafilter] >>
     fs[GSYM MEMBER_NOT_EMPTY] >> metis_tac[])
  >- (` !phi fc.
              fc IN (ultraproduct_model U J Ms).frame.world ==>
              (satis (ultraproduct_model U J Ms) fc phi <=>
               ?f.
                  f IN fc /\
                  {i | i IN J /\ satis (Ms i) (f i) phi} IN U)` by metis_tac[Los_modal_thm] >>
     `{fw | Uequiv U J (models2worlds Ms) (\i. w) fw} IN (ultraproduct_model U J Ms).frame.world`
       by (`w IN M.frame.world` by metis_tac[satis_in_world] >>
          metis_tac[ultraproduct_world_constant]) >>
     `?f. f IN {fw | Uequiv U J (models2worlds Ms) (\i. w) fw} /\ {i | i IN J /\ satis (Ms i) (f i) phi} IN U`
       suffices_by metis_tac[] >>
     qexists_tac `\i.w` >> rw[] (* 2 *)
     >- (fs[Uequiv_def,models2worlds_def,Cart_prod_def] >>
        `w IN M.frame.world` by metis_tac[satis_in_world] >>
        metis_tac[ultrafilter_def,proper_filter_def,filter_def,MEMBER_NOT_EMPTY])
     >- (`{i | i IN J /\ satis (Ms i) w phi} = J`
          suffices_by metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
        rw[EXTENSION,EQ_IMP_THM])));





val folmodels2Doms_def = Define`
  folmodels2Doms FMS = \i. (FMS i).Dom`


 (*
val _ = overload_on ("fP", “λp t. Pred p [t]”);
val _ = overload_on ("fR", “λw1 w2. Pred 0 [w1; w2]”); *)
(*
val ultraproduct_folmodel_def = Define`
   ultraproduct_folmodel U I FMS =
    <| Dom := ultraproduct U I (folmodels2Doms FMS) ;
       Fun := \n fs fc. (\i. ((FMS i).Fun n (MAP ((\f. f i) o CHOICE) fs)) IN U);
       Pred := \p zs. ({i IN I | (FMS i).Pred p (MAP ((\f. f i) zs) o CHOICE) zs} IN U) |>`;
*)



val ultraproduct_folmodel_def = Define`
   ultraproduct_folmodel U I FMS =
    <| Dom := ultraproduct U I (folmodels2Doms FMS) ;
       Fun := \n fs. {y | (!i. i IN I ==> (y i) IN (FMS i).Dom) /\
                          {i | i IN I /\
                               (y i) = (FMS i).Fun n (MAP (\fc. (CHOICE fc) i)fs)} IN U
                     };
       Pred := \p zs. {i | i IN I /\ (FMS i).Pred p (MAP (\fc. (CHOICE fc) i) zs)} IN U |>`;

val wffm_def = Define`
wffm M <=> (∀n0 l0. M.Fun n0 l0 ∈ M.Dom)`

Theorem thm_A_19_i_V_l3:
  !U I A m eqc. ultrafilter U I ==>  (m IN eqc /\ eqc IN (ultraproduct U I A)) ==>
      !i. i IN I ==> (m i) IN (A i)
Proof
  rw[ultraproduct_def,partition_def] >> fs[] >> fs[Cart_prod_def]
QED

Theorem thm_A_19_i_V_l2:
  !U I A m eqc. ultrafilter U I ==>  (m IN eqc /\ eqc IN (ultraproduct U I A)) ==> m ∈ Cart_prod I A
Proof
  rw[Cart_prod_def] >> metis_tac[thm_A_19_i_V_l3]
QED


Theorem thm_A_19_i_V_l1:
  !U I A m eqc. ultrafilter U I ==>  (m IN eqc /\ eqc IN (ultraproduct U I A)) ==> Uequiv U I A m m
Proof
  rw[] >> drule prop_A_16 >> rw[] >> first_x_assum (qspec_then `A` assume_tac) >>
  `m IN (Cart_prod I' A)` suffices_by fs[equiv_on_def] >> metis_tac[thm_A_19_i_V_l2]
QED

Theorem thm_A_19_i_V_l4:
  !U I A. ultrafilter U I ==> !eqc. eqc IN (ultraproduct U I A) ==> (CHOICE eqc) IN eqc
Proof
  rw[] >> drule ultraproduct_eqclass_non_empty >> rw[] >> metis_tac[CHOICE_DEF]
QED


Theorem Uequiv_SYM:
  !U I A x y. ultrafilter U I ==> (Uequiv U I A x y <=> Uequiv U I A y x)
Proof
  rw[] >> drule prop_A_16 >> fs[equiv_on_def] >> fs[Uequiv_def] >> metis_tac[]
QED


Theorem thm_A_19_i_V_l5:
  !U I A. ultrafilter U I ==> !eqc. eqc IN (ultraproduct U I A) ==>
          {f | Uequiv U I A f (CHOICE eqc)} ∈ ultraproduct U I A
Proof
  rw[] >> rw[ultraproduct_def,partition_def] >> qexists_tac `CHOICE eqc` >> rw[] (* 2 *)
  >- (irule thm_A_19_i_V_l2 >> map_every qexists_tac [`U`,`eqc`] >> rw[] >> irule thm_A_19_i_V_l4 >>
     metis_tac[])
  >- (`{f | Uequiv U I' A f (CHOICE eqc)} =  {f | Uequiv U I' A (CHOICE eqc) f}` by
        (rw[EXTENSION] >> metis_tac[Uequiv_SYM]) >>
     rw[EXTENSION] >> rw[Uequiv_def] >> eq_tac >> rw[] (* 2 *) >>
     `{i | i ∈ I' ∧ x i = CHOICE eqc i} = {i | i ∈ I' ∧ CHOICE eqc i = x i}`
           by (rw[EXTENSION] >> metis_tac[]) >> metis_tac[])
QED

Theorem thm_A_19_i_Fn_l1:
  !σ U I A. IMAGE σ 𝕌(:num) ⊆ ultraproduct U I A ==> (!i. i IN I ==> A i <> {})
Proof
  rw[] >> fs[ultraproduct_def,partition_def,Cart_prod_def] >> strip_tac >>
  `{t |
         ∃x.
             (∀i. i ∈ I' ⇒ x i ∈ A i) ∧
             t = {y | (∀i. i ∈ I' ⇒ y i ∈ A i) ∧ Uequiv U I' A x y}} = {}`
    by (SPOSE_NOT_THEN ASSUME_TAC >> fs[GSYM MEMBER_NOT_EMPTY] >> metis_tac[MEMBER_NOT_EMPTY]) >>
  fs[IMAGE_EQ_EMPTY]
QED

Theorem termval_IN_Dom:
  !FM. (!n l. (FM.Fun n l) IN FM.Dom) ==>
       !σ. IMAGE σ (univ(:num)) ⊆ FM.Dom ==>
           !t. (termval FM σ t) IN FM.Dom
Proof
  rw[] >> Cases_on `t` >> fs[] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]
QED
(*
val _ = temp_overload_on ("fm2D", ``folmodels2Doms``);
val _ = temp_overload_on ("upfm", ``ultraproduct_folmodel``);
*)
Theorem thm_A_19_i:
  !t U I. ultrafilter U I ==>
          !σ FMS. IMAGE σ (univ(:num)) ⊆ ultraproduct U I (folmodels2Doms FMS) ==>
             (!i ff ll. i IN I ==> (FMS i).Fun ff ll IN (FMS i).Dom) ==>
          termval (ultraproduct_folmodel U I FMS) σ t =
          {f | Uequiv U I (folmodels2Doms FMS) f
               (\i. termval (FMS i) (\n. CHOICE (σ n) i) t)}
Proof
completeInduct_on `term_size t` >> rw[] >> Cases_on `t` (* 2 *)
>- (rw[termval_def] >> irule equiv_on_same_partition >>
    map_every qexists_tac [`Uequiv U I' (folmodels2Doms FMS)`,
                           `Cart_prod I' (folmodels2Doms FMS)`, `CHOICE (σ n)`,
                           `CHOICE (σ n)`] >>
    rw[] (* 6 *)
    >- (* uequiv is equiv rel so refl *)
       (irule thm_A_19_i_V_l1 >> rw[] >>
        qexists_tac `σ n` >> rw[] (* 2 *)
        >- (irule thm_A_19_i_V_l4 >>
            map_every qexists_tac [`(folmodels2Doms FMS)`,`I'`,`U`] >> rw[] >>
            fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
        >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]))

    >- (* each world is non empty *)
       (irule thm_A_19_i_V_l4 >>
          map_every qexists_tac [`(folmodels2Doms FMS)`,`I'`,`U`] >> rw[] >>
          fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
    >- (* uequiv is equiv *)
       (`Uequiv U I' (folmodels2Doms FMS) (CHOICE (σ n)) (CHOICE (σ n))`
          by (irule thm_A_19_i_V_l1 >> rw[] >>
              qexists_tac `σ n` >> rw[] (* 2 *)
              >- (irule thm_A_19_i_V_l4 >>
                 map_every qexists_tac [`(folmodels2Doms FMS)`,`I'`,`U`] >> rw[] >>
                 fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
              >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])) >>
       `(λi. CHOICE (σ n) i) = CHOICE (σ n)` suffices_by metis_tac[] >> simp[FUN_EQ_THM])
    >- (* definition of ultraprod *)
       (`partition (Uequiv U I' (folmodels2Doms FMS))
            (Cart_prod I' (folmodels2Doms FMS)) =
         ultraproduct U I' (folmodels2Doms FMS)`
           by rw[ultraproduct_def] >> rw[] >> fs[IMAGE_DEF,SUBSET_DEF] >>
        metis_tac[])
    >- (* definition of partition *)
       (`partition (Uequiv U I' (folmodels2Doms FMS))
          (Cart_prod I' (folmodels2Doms FMS)) =
         ultraproduct U I' (folmodels2Doms FMS)`
           by rw[ultraproduct_def] >> rw[] >>
       `(λi. CHOICE (σ n) i) = CHOICE (σ n)` by (rw[FUN_EQ_THM] >> fs[]) >>
       fs[] >>
       irule thm_A_19_i_V_l5 >> rw[] >> fs[IMAGE_DEF,SUBSET_DEF] >>
       metis_tac[])
    >- (* proved thm *) metis_tac[prop_A_16])
>- (Cases_on `l = []`
    >- (fs[] >> rw[termval_def,ultraproduct_folmodel_def] >>
        rw[EXTENSION,EQ_IMP_THM](* 3 *)
        >- (rw[Uequiv_def] (* 3 *)
            >- (rw[folmodels2Doms_def] >> metis_tac[MEMBER_NOT_EMPTY])
            >- (rw[Cart_prod_def] >> fs[folmodels2Doms_def])
            >- rw[Cart_prod_def,folmodels2Doms_def])
        >- fs[Uequiv_def,Cart_prod_def,folmodels2Doms_def]
        >- fs[Uequiv_def]) >>
    rw[termval_def,ultraproduct_folmodel_def] >>
    qabbrev_tac `
      UPM  =  <|Dom := ultraproduct U I' (folmodels2Doms FMS);
                Fun := (λn fs.
                           {y |
                             (∀i. i ∈ I' ⇒ y i ∈ (FMS i).Dom) ∧
                             {i |
                                  i ∈ I' ∧
                                  y i =
                                  (FMS i).Fun n (MAP (λfc. CHOICE fc i) fs)} ∈
                                 U});
                Pred :=(λp zs. {i |
                                 i ∈ I' ∧
                                 (FMS i).Pred p (MAP (λfc. CHOICE fc i) zs)} ∈
                                U)|>` >> rw[MAP_MAP_o,o_DEF] >>
    irule equiv_on_same_partition >>
    map_every qexists_tac [
      `Uequiv U I' (folmodels2Doms FMS)`,
      `Cart_prod I' (folmodels2Doms FMS)`,
      `\i. (FMS i).Fun n (MAP (λa. CHOICE (termval UPM σ a) i) l)`,
      `λi. (FMS i).Fun n
              (MAP (λa. termval (FMS i) (λn. CHOICE (σ n) i) a) l)`] >> rw[] >>
    `UPM = (ultraproduct_folmodel U I' FMS)`
       by fs[Abbr`UPM`,ultraproduct_folmodel_def] (* 6 *)
    >- (`(λi. (FMS i).Fun n (MAP (λa. CHOICE (termval UPM σ a) i) l)) =
         (λi. (FMS i).Fun n
              (MAP (λa. CHOICE
                         {f |
                          Uequiv U I' (folmodels2Doms FMS) f
                            (λi. termval (FMS i)
                                         (λn. CHOICE (σ n) i) a)} i) l))`
            by (rw[FUN_EQ_THM] >> AP_TERM_TAC >> irule MAP_CONG >> simp[] >>
                qx_gen_tac ‘m’ >> rw[] >>
                `(termval (ultraproduct_folmodel U I' FMS) σ m) =
                 {f | Uequiv U I' (folmodels2Doms FMS) f
                     (λi. termval (FMS i) (λn. CHOICE (σ n) i) m)}`
                  suffices_by metis_tac[] >>
                rw[] >> first_x_assum irule >> rw[] >> drule term_size_lemma >>
                strip_tac >>
                first_x_assum (qspec_then `n` assume_tac) >> fs[] >>
                metis_tac[]) >> rw[] >>
        rw[Uequiv_def] (* 4 *)
        >- (`!i. i IN I' ==> folmodels2Doms FMS i ≠ ∅` suffices_by metis_tac[]>>
            drule thm_A_19_i_Fn_l1 >> rw[])
        >- rw[Cart_prod_def,folmodels2Doms_def]
        >- rw[Cart_prod_def,folmodels2Doms_def] >>
        `{i | i IN I' /\
              (FMS i).Fun n (MAP (λa. CHOICE
                        {f |
                         Uequiv U I' (folmodels2Doms FMS) f
                           (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i) l) =
               (FMS i).Fun n
                 (MAP (λa. termval (FMS i) (λn. CHOICE (σ n) i) a) l)} IN U`
              suffices_by fs[Uequiv_def] >>
        qmatch_abbrev_tac `BIGSET IN U` >>
        `{i | i IN I' /\
              (MAP
                (λa.
                   CHOICE
                     {f |
                      Uequiv U I' (folmodels2Doms FMS) f
                        (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i) l) =
         (MAP (λa. termval (FMS i) (λn. CHOICE (σ n) i) a) l)
         } ⊆ BIGSET` by rw[SUBSET_DEF,Abbr`BIGSET`] >>
        `{i |
           i ∈ I' ∧
           MAP
             (λa.
                  CHOICE                  {f |
                     Uequiv U I' (folmodels2Doms FMS) f
                       (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i) l =
           MAP (λa. termval (FMS i) (λn. CHOICE (σ n) i) a) l} IN U`
         suffices_by
          (qmatch_abbrev_tac `BS IN U ==> BIGSET IN U` >>
           fs[ultrafilter_def,proper_filter_def,filter_def] >>
           `BIGSET ⊆ I' /\ BS ⊆ I'` suffices_by metis_tac[] >>
           fs[Abbr`BIGSET`,Abbr`BS`,SUBSET_DEF]) >>
        (* the above reduce the goal into proving another set is in U *)
        `{i |
           i ∈ I' ∧
           (!a. MEM a l ==>
              CHOICE
                    {f |
                     Uequiv U I' (folmodels2Doms FMS) f
                       (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i =
                   termval (FMS i) (λn. CHOICE (σ n) i) a)} ⊆
         {i |
            i ∈ I' ∧
            MAP
              (λa.
                   CHOICE
                     {f |
                      Uequiv U I' (folmodels2Doms FMS) f
                        (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i) l =
            MAP (λa. termval (FMS i) (λn. CHOICE (σ n) i) a) l}`
          by
            (rw[SUBSET_DEF] >> irule MAP_CONG >> fs[] >>
             qmatch_abbrev_tac `BS IN U` >>
             `{i |
                i ∈ I' ∧
                ∀a.
                    MEM a l ⇒
                    CHOICE
                      {f |
                       Uequiv U I' (folmodels2Doms FMS) f
                         (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i =
                    termval (FMS i) (λn. CHOICE (σ n) i) a} IN U`
               suffices_by
                  (qmatch_abbrev_tac `BS' IN U ==> BS IN U` >>
                   fs[ultrafilter_def,proper_filter_def,filter_def] >>
                   `BS ⊆ I' /\ BS' ⊆ I'` suffices_by metis_tac[] >>
                   fs[Abbr`BS`,Abbr`BS'`,SUBSET_DEF])) >>
        qmatch_abbrev_tac `SS IN U` >>
        `BIGINTER (
          {{i | i IN I' /\
                CHOICE
                 {f |
                   Uequiv U I' (folmodels2Doms FMS) f
                     (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i =
                termval (FMS i) (λn. CHOICE (σ n) i) a} | MEM a l}) IN U`
          suffices_by
           (qmatch_abbrev_tac `BS' IN U ==> SS IN U` >>
            `BS' ⊆ SS` suffices_by
                (fs[ultrafilter_def,proper_filter_def,filter_def] >>
                 `SS ⊆ I' /\ BS' ⊆ I'` suffices_by metis_tac[] >>
                 rw[] (* 2 *)
                 >- (rw[SUBSET_DEF,Abbr`SS`] >> fs[])
                 >- (rw[SUBSET_DEF] >> fs[Abbr`BS'`] >>
                     fs[PULL_EXISTS,PULL_FORALL] >>
                     `?mm. MEM mm l` by metis_tac[NOT_NULL_MEM,NULL_EQ] >>
                      metis_tac[])) >>
            (* BS' ⊆ SS suffices tac end *)
            rw[Abbr`BS'`,Abbr`SS`,SUBSET_DEF] (* 2 *)
            >- (fs[PULL_EXISTS,PULL_FORALL] >>
                `?mm. MEM mm l` by metis_tac[NOT_NULL_MEM,NULL_EQ] >>
                metis_tac[]) >>
            irule MAP_CONG >> fs[PULL_EXISTS,PULL_FORALL]) >>
        (* BIGSET suffices end *)
        `!a. MEM a l ==>
             {i | i ∈ I' ∧
                  CHOICE
                   {f |
                     Uequiv U I' (folmodels2Doms FMS) f
                       (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i =
                  termval (FMS i) (λn. CHOICE (σ n) i) a} IN U`
          suffices_by
         (* split into small sets and appeal to finite inter *)
         (rw[] >> irule BIGINTER_FINITE >> rw[] (* 4 *)
          >- fs[ultrafilter_def,proper_filter_def,filter_def]
          >- (qmatch_abbrev_tac `FINITE IS` >>
              `?(s: term set) f. FINITE s /\ IS = IMAGE f s`
                suffices_by metis_tac[IMAGE_FINITE] >>
              map_every qexists_tac [
                `{a| MEM a l}`,
                `\a. {i |
                       i ∈ I' ∧
                       CHOICE
                         {f |
                          Uequiv U I' (folmodels2Doms FMS) f
                            (λi. termval (FMS i)
                                   (λn. CHOICE (σ n) i) a)} i =
                       termval (FMS i) (λn. CHOICE (σ n) i) a}`] >>
              rw[] (* only one subgoal *)>>
              rw[IMAGE_DEF])
          >- (rw[GSYM MEMBER_NOT_EMPTY] >>
              metis_tac[NULL_EQ,NOT_NULL_MEM])
          >- (rw[SUBSET_DEF] >> metis_tac[]))
        (* all mem suffices tac end *)
        >> rw[] >>
        `Uequiv U I' (folmodels2Doms FMS)
          (\i.CHOICE
               {f |
                  Uequiv U I' (folmodels2Doms FMS) f
                    (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)
               } i)
               (\i.termval (FMS i) (λn. CHOICE (σ n) i) a)`
          suffices_by
           (rw[Uequiv_def] >> fs[] >>
            `CHOICE
              {f |
               f ∈ Cart_prod I' (folmodels2Doms FMS) ∧
               {i | i ∈ I' ∧
                    f i = termval (FMS i) (λn. CHOICE (σ n) i) a} ∈ U} IN
               {f |
                 f ∈ Cart_prod I' (folmodels2Doms FMS) ∧
                 {i | i ∈ I' ∧
                      f i = termval (FMS i) (λn. CHOICE (σ n) i) a} ∈ U}`
                 suffices_by rw[] >>
            (* very little suffice tac *)
            `{f |
               f ∈ Cart_prod I' (folmodels2Doms FMS) ∧
               {i | i ∈ I' ∧
                    f i = termval (FMS i) (λn. CHOICE (σ n) i) a} ∈ U} <>
             {}` suffices_by metis_tac[CHOICE_DEF] >>
            rw[GSYM MEMBER_NOT_EMPTY] >>
            qexists_tac `\i. termval (FMS i) (λn. CHOICE (σ n) i) a` >>
            rw[] >>
            fs[ultrafilter_def,proper_filter_def,filter_def]) >>
        (* Uequiv suffices tac end *)
        `(λi.
               CHOICE
                 {f |
                  Uequiv U I' (folmodels2Doms FMS) f
                    (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} i) =
               CHOICE
                 {f |
                  Uequiv U I' (folmodels2Doms FMS) f
                    (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)}`
            by rw[FUN_EQ_THM] >> rw[] >>
        `CHOICE
             {f |
              Uequiv U I' (folmodels2Doms FMS) f
                (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} IN
         {f |
              Uequiv U I' (folmodels2Doms FMS) f
                (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)}`
            suffices_by fs[] >>
        `{f |
           Uequiv U I' (folmodels2Doms FMS) f
             (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} <> {}`
          suffices_by fs[CHOICE_DEF] >>
        rw[GSYM MEMBER_NOT_EMPTY] >>
        qexists_tac `(λi. termval (FMS i) (λn. CHOICE (σ n) i) a)` >>
        rw[] >> drule prop_A_16 >> rw[] >>
        first_x_assum (qspec_then `(folmodels2Doms FMS)` assume_tac) >>
        fs[equiv_on_def] >>
        `(λi. termval (FMS i) (λn. CHOICE (σ n) i) a) IN
            Cart_prod I' (folmodels2Doms FMS)` suffices_by metis_tac[] >>
        fs[Cart_prod_def] >> rw[folmodels2Doms_def] >>
        irule termval_IN_Dom >> rw[] >> fs[IMAGE_DEF,SUBSET_DEF] >> rw[] >>
        `σ n' ∈ ultraproduct U I' (folmodels2Doms FMS)` by metis_tac[] >>
        fs[ultraproduct_def,folmodels2Doms_def,partition_def,Cart_prod_def] >>
        `CHOICE
          {y |
           (∀i. i ∈ I' ⇒ y i ∈ (FMS i).Dom) ∧
           Uequiv U I' (λi. (FMS i).Dom) x y} IN
          {y |
           (∀i. i ∈ I' ⇒ y i ∈ (FMS i).Dom) ∧
           Uequiv U I' (λi. (FMS i).Dom) x y}` by
         (`{y |(∀i. i ∈ I' ⇒ y i ∈ (FMS i).Dom) ∧
           Uequiv U I' (λi. (FMS i).Dom) x y} <> {}` suffices_by metis_tac[CHOICE_DEF] >>
          rw[GSYM MEMBER_NOT_EMPTY] >> qexists_tac `x` >> rw[]) >> fs[])(*))??*)
   (* 5 goals remain *)
   >- (* by definition of ultrafilter *) fs[ultrafilter_def,proper_filter_def,filter_def]
   >- (* Uequiv is equiv_on *) (rw[Uequiv_def] (* 4 *)
      >- (rw[folmodels2Doms_def] >> metis_tac[MEMBER_NOT_EMPTY])
      >- rw[Cart_prod_def,folmodels2Doms_def]
      >- rw[Cart_prod_def,folmodels2Doms_def]
      >- fs[ultrafilter_def,proper_filter_def,filter_def])
   >- (* in card prod by definition, need lemmas *) (rw[partition_def,Cart_prod_def] >>
      qexists_tac `\i. (FMS i).Fun n
                (MAP
                   (λa.
                        CHOICE (termval (ultraproduct_folmodel U I' FMS) σ a)
                          i) l)` >> rw[] (* 2 *)
      >- rw[folmodels2Doms_def]
      >- (rw[EQ_IMP_THM,Once EXTENSION,Uequiv_def] (* 7 *)
         >- rw[folmodels2Doms_def]
         >- (rw[folmodels2Doms_def] >>  metis_tac[MEMBER_NOT_EMPTY])
         >- rw[Cart_prod_def,folmodels2Doms_def]
         >- rw[Cart_prod_def,folmodels2Doms_def]
         >- (`{i | i ∈ I' ∧ x i = (FMS i).Fun n
           (MAP (λa. CHOICE (termval (ultraproduct_folmodel U I' FMS) σ a) i) l)} =
             {i | i ∈ I' ∧ (FMS i).Fun n
           (MAP (λa. CHOICE (termval (ultraproduct_folmodel U I' FMS) σ a) i) l) = x i}`
             suffices_by metis_tac[] >> rw[EXTENSION] >> metis_tac[])
         >- fs[folmodels2Doms_def]
         >- (`{i | i ∈ I' ∧ x i = (FMS i).Fun n
           (MAP (λa. CHOICE (termval (ultraproduct_folmodel U I' FMS) σ a) i) l)} =
             {i | i ∈ I' ∧ (FMS i).Fun n
           (MAP (λa. CHOICE (termval (ultraproduct_folmodel U I' FMS) σ a) i) l) = x i}`
             suffices_by metis_tac[] >> rw[EXTENSION] >> metis_tac[])))
   >- (* same as above *)
      (rw[partition_def,Cart_prod_def] >>
      qexists_tac `λi.
                    (FMS i).Fun n
                      (MAP (λa. termval (FMS i) (λn. CHOICE (σ n) i) a) l)` >> rw[] (* 2 *)
      >- rw[folmodels2Doms_def]
      >- (rw[EQ_IMP_THM,Once EXTENSION,Uequiv_def] (* 3 *)
          >- fs[Cart_prod_def,folmodels2Doms_def]
          >> (`{i | i ∈ I' ∧ x i =
              (FMS i).Fun n (MAP (λa. termval (FMS i) (λn. CHOICE (σ n) i) a) l)} =
              {i | i ∈ I' ∧ (FMS i).Fun n (MAP (λa. termval (FMS i) (λn. CHOICE (σ n) i) a) l) = x i}`
                suffices_by metis_tac[] >> rw[EXTENSION] >> metis_tac[])))
   >- metis_tac[prop_A_16])
QED

Theorem IMAGE_UPDATE:
  !σ a. IMAGE σ A ⊆ B ==> !b. b IN B ==> IMAGE σ(|a |-> b|) A ⊆ B
Proof
  rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x' = a` >> rw[APPLY_UPDATE_THM] >> metis_tac[]
QED


Theorem thm_A_19_ii:
!U I phi σ FMS. (ultrafilter U I /\
                 (valuation (ultraproduct_folmodel U I FMS) σ) /\
                 (!i. i IN I ==> wffm (FMS i))) ==>
                  (feval (ultraproduct_folmodel U I FMS) σ phi <=>
                  {i | i IN I /\ feval (FMS i) (\x. (CHOICE (σ x)) i) phi} IN U)
Proof
  `!U I phi. ultrafilter U I ==>
      !σ FMS. IMAGE σ (univ(:num)) ⊆ ultraproduct U I (folmodels2Doms FMS) ==>
             (!i ff ll. i IN I ==> (FMS i).Fun ff ll IN (FMS i).Dom) ==>
                  (feval (ultraproduct_folmodel U I FMS) σ phi <=>
                 {i | i IN I /\ feval (FMS i) (\x. (CHOICE (σ x)) i) phi} IN U)`
    suffices_by
      (rw[] >> first_x_assum irule >>
 fs[IMAGE_DEF,valuation_def,wffm_def,SUBSET_DEF,ultraproduct_folmodel_def] >>
metis_tac[]) >>
Induct_on `phi` (* 4 *)
>- (rw[feval_def] >> metis_tac[EMPTY_NOTIN_ultrafilter])
>- (rw[] >> Cases_on `l = []`
    >- (fs[] >> rw[ultraproduct_folmodel_def]) (*2nd subgoal 1st case done*)>>
    rw[feval_def,ultraproduct_folmodel_def,feval_def,MAP_MAP_o,o_DEF] >>
    `<|Dom := ultraproduct U I' (folmodels2Doms FMS);
       Fun := (λn fs. {y | (∀i. i ∈ I' ⇒ y i ∈ (FMS i).Dom) ∧
                            {i | i ∈ I' ∧
                              y i =
                                 (FMS i).Fun n (MAP (λfc. CHOICE fc i) fs)
                            } ∈ U
                      });
       Pred := (λp zs. {i | i ∈ I' ∧
                            (FMS i).Pred p (MAP (λfc. CHOICE fc i) zs)
                       } ∈ U)|> = ultraproduct_folmodel U I' FMS`
      by fs[ultraproduct_folmodel_def] >> rw[] >>
    qmatch_abbrev_tac `S1 IN U <=> S2 IN U` >>
    qabbrev_tac
      `I0 = {i | i IN I' /\
                 (MAP
                   (λx. CHOICE
                     (termval (ultraproduct_folmodel U I' FMS) σ x) i) l) =
                 (MAP (termval (FMS i) (λx. CHOICE (σ x) i)) l)}` >>
    `I0 ∩ S1 = I0 ∩ S2`
      by
       (rw[EXTENSION,EQ_IMP_THM,Abbr`S1`,Abbr`S2`,Abbr`I0`] >> metis_tac[]) >>
    `I0 IN U`
      suffices_by
       (rw[EQ_IMP_THM] (* 2 *)
        >- (fs[ultrafilter_def,proper_filter_def,filter_def] >>
            `(I0 ∩ S2) IN U` by metis_tac[] >>
            `(I0 ∩ S2) ⊆ S2` by rw[SUBSET_DEF,INTER_DEF] >>
            `S2 ⊆ I'` by rw[Abbr`S2`,SUBSET_DEF] >> metis_tac[])
        >- (fs[ultrafilter_def,proper_filter_def,filter_def] >>
            `(I0 ∩ S1) IN U` by metis_tac[] >>
            `(I0 ∩ S1) ⊆ S1` by rw[SUBSET_DEF,INTER_DEF] >>
            `S1 ⊆ I'` by rw[Abbr`S1`,SUBSET_DEF] >> metis_tac[])) >>
     (* reduced the goal into I0 in U *)
    `BIGINTER
      {
       {i | i ∈ I' ∧
            CHOICE
              (termval (ultraproduct_folmodel U I' FMS) σ a) i
            = (termval (FMS i) (λx. CHOICE (σ x) i) a)}
       | MEM a l} ⊆ I0`
      by
        (* split I0 inter small sets *)
       (rw[SUBSET_DEF,Abbr`I0`] (* 2 *)
        >- (`?m. MEM m l` by metis_tac[NOT_NULL_MEM,NULL_EQ] >>
            fs[PULL_EXISTS] >> metis_tac[])
        >- (irule MAP_CONG >> rw[] >> fs[PULL_EXISTS])) >>
    `BIGINTER
      {
       {i | i ∈ I' ∧
            CHOICE (termval (ultraproduct_folmodel U I' FMS) σ a) i
            = (termval (FMS i) (λx. CHOICE (σ x) i) a)}
        | MEM a l} IN U`
      suffices_by
       (fs[ultrafilter_def,proper_filter_def,filter_def] >>
        `I0 ⊆ I'` by fs[SUBSET_DEF,Abbr`I0`] >> metis_tac[]) >>
     (* reduced the goal into prove biginter in  U *)
    irule BIGINTER_FINITE >> rw[] (* 4 *)
    >- fs[ultrafilter_def,proper_filter_def,filter_def]
    >- (qmatch_abbrev_tac `FINITE BS` >>
        `?(s:term-> bool) f.
          FINITE s /\ BS = IMAGE f s`
         suffices_by metis_tac[IMAGE_FINITE] >>
        map_every qexists_tac [
          `{a| MEM a l}`,
          `\a.{i | i ∈ I' ∧
                   CHOICE
                     (termval (ultraproduct_folmodel U I' FMS) σ a) i =
                   termval (FMS i) (λx. CHOICE (σ x) i) a}`] >> rw[] >>
        rw[EQ_IMP_THM,Once EXTENSION] (* 2 *)
        >- (fs[Abbr`BS`] >> metis_tac[])
        >- (rw[Abbr`BS`] >> qexists_tac `a` >> metis_tac[]))
    >- (rw[GSYM MEMBER_NOT_EMPTY] >> metis_tac[NOT_NULL_MEM,NULL_EQ])
    >- (rw[SUBSET_DEF] >> drule thm_A_19_i >> rw[] >>
        `CHOICE
           {f |
            Uequiv U I' (folmodels2Doms FMS) f
              (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} IN
           {f |
            Uequiv U I' (folmodels2Doms FMS) f
              (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)}`
          suffices_by
           (rw[] >> metis_tac[Uequiv_def]) >>
        `{f | Uequiv U I' (folmodels2Doms FMS) f
              (λi. termval (FMS i) (λn. CHOICE (σ n) i) a)} <> {}`
          suffices_by metis_tac[CHOICE_DEF] >>
        rw[GSYM MEMBER_NOT_EMPTY] >>
        qexists_tac `(λi. termval (FMS i) (λn. CHOICE (σ n) i) a)` >>
        rw[Uequiv_def] (* 4 *)
        >- (rw[folmodels2Doms_def] >> metis_tac[MEMBER_NOT_EMPTY])
        >- (rw[Cart_prod_def,folmodels2Doms_def] >>
            irule termval_IN_Dom >> rw[] >>
            fs[IMAGE_DEF,SUBSET_DEF] >> rw[] >>
            `(σ n') IN (ultraproduct U I' (folmodels2Doms FMS))`
              by metis_tac[] >>
            fs[ultraproduct_def,folmodels2Doms_def] >>
            `σ n' <> {}` by metis_tac[EMPTY_NOT_IN_partition,prop_A_16] >>
            `CHOICE (σ n') IN (σ n')` by metis_tac[CHOICE_DEF] >>
            fs[partition_def,Cart_prod_def] >> rfs[])
        >- (rw[Cart_prod_def,folmodels2Doms_def] >>
            irule termval_IN_Dom >> rw[] >>
            fs[IMAGE_DEF,SUBSET_DEF] >> rw[] >>
            `(σ n') IN (ultraproduct U I' (folmodels2Doms FMS))`
              by metis_tac[] >>
            fs[ultraproduct_def,folmodels2Doms_def] >>
            `σ n' <> {}` by metis_tac[EMPTY_NOT_IN_partition,prop_A_16] >>
            `CHOICE (σ n') IN (σ n')` by metis_tac[CHOICE_DEF] >>
            fs[partition_def,Cart_prod_def] >> rfs[])
        >- fs[ultrafilter_def,proper_filter_def,filter_def]))
>- (rw[feval_def,EQ_IMP_THM] (* 2 *)
    >- (`{i | i ∈ I' ∧
              (¬(feval (FMS i) (λx. CHOICE (σ x) i) phi) \/
              feval (FMS i) (λx. CHOICE (σ x) i) phi')} ∈ U`
          suffices_by
           (`{i | i ∈ I' ∧
                  (¬(feval (FMS i) (λx. CHOICE (σ x) i) phi) \/
                  feval (FMS i) (λx. CHOICE (σ x) i) phi')} =
             {i | i ∈ I' ∧
                  (feval (FMS i) (λx. CHOICE (σ x) i) phi ⇒
                  feval (FMS i) (λx. CHOICE (σ x) i) phi')}`
              suffices_by metis_tac[] >>
            rw[EXTENSION] >> metis_tac[]) >>
        `{i | i ∈ I' ∧
              (¬feval (FMS i) (λx. CHOICE (σ x) i) phi ∨
              feval (FMS i) (λx. CHOICE (σ x) i) phi')} =
         {i | i ∈ I' ∧
              (¬feval (FMS i) (λx. CHOICE (σ x) i) phi)} ∪
         {i | i ∈ I' ∧
              (feval (FMS i) (λx. CHOICE (σ x) i) phi')}`
          by (rw[EXTENSION] >> metis_tac[]) >> rw[] >>
        Cases_on
          `{i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i) phi} ∈ U` (* 2 *)
        >- (first_x_assum drule >> rw[] >> qmatch_abbrev_tac `UU IN U` >>
            `UU ⊆ I' /\
             {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i) phi'} ⊆ UU`
              suffices_by
               metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
           rw[Abbr`UU`,SUBSET_DEF])
        >- (`{i | i ∈ I' ∧ ¬feval (FMS i) (λx. CHOICE (σ x) i) phi} IN U`
              by metis_tac[ultrafilter_complement] >>
            qmatch_abbrev_tac `UU IN U` >>
            `UU ⊆ I' /\
             {i | i ∈ I' ∧ ¬feval (FMS i) (λx. CHOICE (σ x) i) phi} ⊆ UU`
              suffices_by
               metis_tac[ultrafilter_def,proper_filter_def,filter_def] >>
            rw[Abbr`UU`,SUBSET_DEF]))
    >- (`{i | i ∈ I' ∧
         (feval (FMS i) (λx. CHOICE (σ x) i) phi ⇒
         feval (FMS i) (λx. CHOICE (σ x) i) phi')} =
         {i |  i ∈ I' ∧
         ((¬(feval (FMS i) (λx. CHOICE (σ x) i) phi))\/
         feval (FMS i) (λx. CHOICE (σ x) i) phi')}`
          by (rw[EXTENSION] >> metis_tac[]) >>
        `{i | i ∈ I' ∧
         (¬feval (FMS i) (λx. CHOICE (σ x) i) phi ∨
          feval (FMS i) (λx. CHOICE (σ x) i) phi')} =
         {i | i ∈ I' ∧ ¬feval (FMS i) (λx. CHOICE (σ x) i) phi} ∪
         {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i) phi'}`
          by (rw[EXTENSION] >> metis_tac[]) >>
        fs[] >>
        `{i | i ∈ I' ∧ ¬feval (FMS i) (λx. CHOICE (σ x) i) phi} NOTIN U`
          by metis_tac[ultrafilter_complement] >>
        drule ultrafilter_UNION >> rw[] >>
        first_x_assum
          (qspecl_then
            [`{i | i ∈ I' ∧ ¬feval (FMS i) (λx. CHOICE (σ x) i) phi}`,
             `{i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i) phi'}`]
           assume_tac) >>
        fs[SUBSET_DEF]))
>- (rw[feval_def] >> rw[EQ_IMP_THM]
  >- (SPOSE_NOT_THEN ASSUME_TAC >>
      `{i | i ∈ I' ∧
            ?a. a ∈ (FMS i).Dom /\
            ¬ feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi} IN U`
        by
         (`(I' DIFF {i | i ∈ I' ∧
                         ∀a. a ∈ (FMS i).Dom ⇒
                           feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi}) IN U`
            by (fs[ultrafilter_def,proper_filter_def,filter_def] >>
          `{i | i ∈ I' ∧
                ∀a. a ∈ (FMS i).Dom ⇒
                  feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi} IN (POW I')`
           suffices_by metis_tac[] >> rw[POW_DEF,SUBSET_DEF]) >>
      `I' DIFF {i | i ∈ I' ∧
                    ∀a. a ∈ (FMS i).Dom ⇒
                      feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi} =
       {i | i ∈ I' ∧
            ?a. a ∈ (FMS i).Dom /\
            ¬ feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi}`
        suffices_by metis_tac[] >>
      rw[EXTENSION,EQ_IMP_THM] >> metis_tac[]) >>
     (* ? in U by tactic end *)
      qabbrev_tac
        `f = \i. if
                  (∃a. a ∈ (FMS i).Dom ∧
                       ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi) then
                  (CHOICE {a | a ∈ (FMS i).Dom ∧
                               ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi})
                 else (CHOICE (FMS i).Dom)` >>
      `{i | i IN I' /\
            ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ f i⦈ phi} IN U`
       (* biggest suffices *)
        suffices_by
         (strip_tac >>
          `?a. a ∈ (ultraproduct_folmodel U I' FMS).Dom /\
               ¬feval (ultraproduct_folmodel U I' FMS) σ⦇n ↦ a⦈ phi`
            suffices_by metis_tac[] >>
          qexists_tac
           `{g | Uequiv U I' (folmodels2Doms FMS) g f}` >> rw[] (* 2 *)
          >- (rw[ultraproduct_folmodel_def,ultraproduct_def,partition_def] >>
              qexists_tac `f` >> rw[] (* 2 *)
              >- (rw[Cart_prod_def,folmodels2Doms_def] >>
                  Cases_on
                  `(∃a. a ∈ (FMS i).Dom ∧
                        ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi)` >>
                  fs[Abbr`f`] >> rw[] (* 4 *)
                  >- (`CHOICE
                       {a | a ∈ (FMS i).Dom ∧
                            ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi} IN
                       {a | a ∈ (FMS i).Dom ∧
                            ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi}`
                       suffices_by fs[] >>
                      `{a | a ∈ (FMS i).Dom ∧
                            ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi}
                       <> {}` suffices_by metis_tac[CHOICE_DEF] >>
                      rw[GSYM MEMBER_NOT_EMPTY] >>
                      qexists_tac `a` >> fs[])
                  >- (fs[] >>
                      `(FMS i).Dom <> {}` suffices_by metis_tac[CHOICE_DEF] >>
                      metis_tac[MEMBER_NOT_EMPTY])
                  >- (`CHOICE
                       {a | a ∈ (FMS i).Dom ∧
                            ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi} IN
                       {a | a ∈ (FMS i).Dom ∧
                            ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi}`
                       suffices_by fs[] >>
                      `{a | a ∈ (FMS i).Dom ∧
                            ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi}
                       <> {}` suffices_by metis_tac[CHOICE_DEF] >>
                      rw[GSYM MEMBER_NOT_EMPTY] >>
                      qexists_tac `a` >> fs[])
                  >- (fs[] >>
                      `(FMS i).Dom <> {}` suffices_by metis_tac[CHOICE_DEF] >>
                      metis_tac[MEMBER_NOT_EMPTY]))
              >- (rw[EXTENSION,Uequiv_def,EQ_IMP_THM] (* 2 *) >>
                  `{i | i ∈ I' ∧ x i = f i} = {i | i ∈ I' ∧ f i = x i}`
                   suffices_by metis_tac[] >> rw[EXTENSION,EQ_IMP_THM]))
          >- (first_x_assum drule >> rw[] >>
              first_x_assum (qspecl_then
               [`σ⦇n ↦ {g | Uequiv U I' (folmodels2Doms FMS) g f}⦈`,
                `FMS`] assume_tac) >>
              `{i | i ∈ I' ∧
                    feval (FMS i)
                     (λx. CHOICE
                           (σ⦇n ↦ {g | Uequiv U I' (folmodels2Doms FMS) g f}⦈ x)                            i)
                          phi} NOTIN U /\
               IMAGE σ⦇n ↦ {g | Uequiv U I' (folmodels2Doms FMS) g f}⦈ 𝕌(:num)
                 ⊆ ultraproduct U I' (folmodels2Doms FMS)`
                suffices_by metis_tac[] >> rw[] (* 2 *)
              >- (`{i | i ∈ I' ∧
                        ¬feval (FMS i)
                             (λx. CHOICE
                              (σ⦇n ↦ {g | Uequiv U I' (folmodels2Doms FMS) g f}⦈                               x) i)
                             phi} IN U`
                    suffices_by
                     (rw[] >>
                      `I' DIFF
                        {i | i ∈ I' ∧
                             ¬feval (FMS i)
                                    (λx.
                                     CHOICE
                                      (σ⦇n ↦
                                     {g | Uequiv U I' (folmodels2Doms FMS) g f}⦈                                       x) i)
                                     phi} NOTIN U`
                        by
                         (fs[ultrafilter_def,proper_filter_def,filter_def]>>
                          `{i | i ∈ I' ∧
                                ¬feval (FMS i)
                                     (λx.
                                      CHOICE
                                       (σ⦇n ↦
                                        {g |
                                          Uequiv U I' (folmodels2Doms FMS) g f}⦈                                        x)
                                      i) phi} IN (POW I')`
                            suffices_by metis_tac[] >>
                          rw[POW_DEF,SUBSET_DEF]) >>
                               (* proved the diff in the set *)
                      qmatch_abbrev_tac `BS NOTIN U` >>
                      `I' DIFF
                        {i | i ∈ I' ∧ ¬feval (FMS i)
                             (λx.
                              CHOICE
                              (σ⦇n ↦ {g | Uequiv U I' (folmodels2Doms FMS) g f}⦈                               x)
                                    i) phi} = BS`
                        suffices_by metis_tac[] >>
                      rw[EXTENSION,Abbr`BS`]>>
                      metis_tac[]) >>
                           (* a big suffices end *)
                   `{i | i IN I' /\
                         (λx.
                          CHOICE
                           (σ⦇n ↦ {g | Uequiv U I' (folmodels2Doms FMS) g f}⦈ x)                           i) =
                          (λx. CHOICE (σ x) i)⦇n ↦ f i⦈} ∩
                    {i | i ∈ I' ∧
                         ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ f i⦈ phi} ⊆
                    {i | i ∈ I' ∧
                         ¬feval (FMS i) (λx.
                         CHOICE
                           (σ⦇n ↦ {g | Uequiv U I' (folmodels2Doms FMS) g f}⦈ x)
                         i) phi}` by rw[SUBSET_DEF] >>
                   `{i | i ∈ I' ∧
                         (λx.
                           CHOICE
                           (σ⦇n ↦ {g | Uequiv U I' (folmodels2Doms FMS) g f}⦈ x)                           i) =
                         (λx. CHOICE (σ x) i)⦇n ↦ f i⦈} IN U`
                      suffices_by
                       (qmatch_abbrev_tac `A IN U ==> B IN U` >> rw[] >>
                        `A ∩
                         {i | i ∈ I' ∧
                         ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ f i⦈ phi} IN U`
                          by metis_tac[ultrafilter_INTER] >>
                        `B ⊆ I'` by rw[Abbr`B`,SUBSET_DEF] >>
                        metis_tac[ultrafilter_SUBSET']) >>
                   `{i | i IN I' /\
                         (CHOICE {g | Uequiv U I' (folmodels2Doms FMS) g f}) i =                         f i} ⊆
                    {i | i ∈ I' ∧
                         (λx. CHOICE
                           (σ⦇n ↦ {g | Uequiv U I' (folmodels2Doms FMS) g f}⦈ x)                           i) =
                         (λx. CHOICE (σ x) i)⦇n ↦ f i⦈}`
                     by (rw[SUBSET_DEF] >>
                         rw[APPLY_UPDATE_THM,FUN_EQ_THM] >>
                         Cases_on `n = x'` >> rw[])>>
                   qmatch_abbrev_tac `BIGSET IN U` >>
                   `BIGSET ⊆ I'` by fs[Abbr`BIGSET`,SUBSET_DEF] >>
                   `{i |i ∈ I' ∧
                        CHOICE
                         {g | Uequiv U I' (folmodels2Doms FMS) g f} i = f i}
                        IN U`
                    suffices_by metis_tac[ultrafilter_SUBSET'] >>
                 (* (* checked well defined, enough. Thankfully*) >> cheat >> ch                eat ) do not know hwat are the cheat for...*)
                 (* reduce the goal to the subtle point *)
                   `Uequiv U I' (folmodels2Doms FMS)
                    (CHOICE {g | Uequiv U I' (folmodels2Doms FMS) g f}) f`
                     suffices_by
                    (* a suffice start here *)
                      (rw[Uequiv_def] >>
                       `{i | i ∈ I' ∧
                             CHOICE
                             {g |
                              (∀i. i ∈ I' ⇒ folmodels2Doms FMS i ≠ ∅) ∧
                              g ∈ Cart_prod I' (folmodels2Doms FMS) ∧
                              f ∈ Cart_prod I' (folmodels2Doms FMS) ∧
                              {i | i ∈ I' ∧ g i = f i} ∈ U} i = f i} =
                        {i | i ∈ I' ∧
                             CHOICE
                             {g |
                              g ∈ Cart_prod I' (folmodels2Doms FMS) ∧
                              {i | i ∈ I' ∧ g i = f i} ∈ U} i = f i}`
                        suffices_by metis_tac[] >>
                       rw[EXTENSION,EQ_IMP_THM]) >>
                    (* the above suffices **a suffices ** end here *)
                   `CHOICE {g | Uequiv U I' (folmodels2Doms FMS) g f} IN
                    {g | Uequiv U I' (folmodels2Doms FMS) g f}`
                    suffices_by fs[] >>
                   `{g | Uequiv U I' (folmodels2Doms FMS) g f} <> {}`
                    suffices_by metis_tac[CHOICE_DEF] >>
                   rw[GSYM MEMBER_NOT_EMPTY] >> qexists_tac `f` >>
                   rw[Uequiv_def] (* 4 *)
                   >- (rw[folmodels2Doms_def] >> metis_tac[MEMBER_NOT_EMPTY])
                   >- (rw[Cart_prod_def,folmodels2Doms_def] >>
                      (* case argument to prove f has image in model *)
                       Cases_on `∃a. a ∈ (FMS i).Dom ∧
                         ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi` (* 2 *)
                       >- (rw[Abbr`f`] >>
                           `CHOICE
                             {a |  a ∈ (FMS i).Dom ∧
                             ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi} ∈
                           {a |  a ∈ (FMS i).Dom ∧
                            ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi}`
                            suffices_by fs[] >>
                           irule CHOICE_DEF >>
                           simp[GSYM MEMBER_NOT_EMPTY] >> metis_tac[])
                       >- (rw[Abbr`f`] >>
                           `(FMS i).Dom <> {}`
                            suffices_by metis_tac[CHOICE_DEF] >>
                           rw[GSYM MEMBER_NOT_EMPTY] >> metis_tac[]))
                   >- (rw[Cart_prod_def,folmodels2Doms_def] >>
                      (* case argument to prove f has image in model *)
                       Cases_on `∃a. a ∈ (FMS i).Dom ∧
                         ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi` (* 2 *)
                       >- (rw[Abbr`f`] >>
                           `CHOICE
                             {a |  a ∈ (FMS i).Dom ∧
                             ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi} ∈
                           {a |  a ∈ (FMS i).Dom ∧
                            ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi}`
                            suffices_by fs[] >>
                           irule CHOICE_DEF >>
                           simp[GSYM MEMBER_NOT_EMPTY] >> metis_tac[])
                       >- (rw[Abbr`f`] >>
                           `(FMS i).Dom <> {}`
                            suffices_by metis_tac[CHOICE_DEF] >>
                           rw[GSYM MEMBER_NOT_EMPTY] >> metis_tac[]))
                   >- fs[ultrafilter_def,proper_filter_def,filter_def])
              (* match the second case in the very early suffices,
                  here need image update *)
              >- (irule IMAGE_UPDATE >> rw[] >>
                 rw[ultraproduct_def,partition_def] >>
                 qexists_tac `f` >> rw[](* 2 *)
                 >- (rw[Cart_prod_def,folmodels2Doms_def] >>
                    (* case argument to prove f has image in model *)
                     Cases_on `∃a. a ∈ (FMS i).Dom ∧
                         ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi` (* 2 *)
                     >- (rw[Abbr`f`] >>
                         `CHOICE {a |
                           a ∈ (FMS i).Dom ∧
                            ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi} ∈
                          {a |  a ∈ (FMS i).Dom ∧
                          ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi}`
                           suffices_by fs[] >>
                         irule CHOICE_DEF >> simp[GSYM MEMBER_NOT_EMPTY] >>
                         metis_tac[])
                     >- (rw[Abbr`f`] >>
                         `(FMS i).Dom <> {}` suffices_by metis_tac[CHOICE_DEF]>>                         rw[GSYM MEMBER_NOT_EMPTY] >> metis_tac[]))
                >- (rw[EXTENSION,Uequiv_def,EQ_IMP_THM] (* 2 *) >>
                    `{i | i ∈ I' ∧ x i = f i} = {i | i ∈ I' ∧ f i = x i}`
                      suffices_by metis_tac[] >>
                    rw[EXTENSION] >> metis_tac[])))) >>
                (* biggest suffices end *)
     qmatch_abbrev_tac `BS' IN U` >>
     `{i | i ∈ I' ∧
           ∃a. a ∈ (FMS i).Dom ∧
      ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi} ⊆ BS'`
       suffices_by
        (`BS' ⊆ I'` by fs[SUBSET_DEF,Abbr`BS'`] >>
         metis_tac[ultrafilter_SUBSET']) >>
     rw[SUBSET_DEF] >> rw[Abbr`BS'`] >>
     Cases_on `∃a.
                      a ∈ (FMS i).Dom ∧
                      ¬feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi` (* 2 *) >>
     rw[Abbr`f`] >> fs[] (* 2same tactic applies for both cases *)
     >- (`CHOICE {a |a ∈ (FMS x).Dom ∧ ¬feval (FMS x) (λx'. CHOICE (σ x') x)⦇n ↦ a⦈ phi} IN
              {a |a ∈ (FMS x).Dom ∧ ¬feval (FMS x) (λx'. CHOICE (σ x') x)⦇n ↦ a⦈ phi}`
        suffices_by fs[] >> irule CHOICE_DEF >> rw[GSYM MEMBER_NOT_EMPTY] >> metis_tac[])
     >- metis_tac[]
     >- (`CHOICE {a |a ∈ (FMS x).Dom ∧ ¬feval (FMS x) (λx'. CHOICE (σ x') x)⦇n ↦ a⦈ phi} IN
              {a |a ∈ (FMS x).Dom ∧ ¬feval (FMS x) (λx'. CHOICE (σ x') x)⦇n ↦ a⦈ phi}`
        suffices_by fs[] >> irule CHOICE_DEF >> rw[GSYM MEMBER_NOT_EMPTY] >> metis_tac[])
     >- metis_tac[])
(* last case last direction *)
   >- (first_x_assum drule >> rw[] >> first_x_assum (qspecl_then [`σ(|n |-> a|)`,`FMS`] assume_tac)>>
      `IMAGE σ⦇n ↦ a⦈ 𝕌(:num) ⊆ ultraproduct U I' (folmodels2Doms FMS) /\
      {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ⦇n ↦ a⦈ x) i) phi} ∈ U` suffices_by metis_tac[] >>
      rw[](* 2 *)
      >- (* need a lemma saying updating with a member in the world *)
         (irule IMAGE_UPDATE >> fs[ultraproduct_folmodel_def])
      >- (`{i |  i ∈ I' ∧
         ∀a. a ∈ (FMS i).Dom ⇒ feval (FMS i) (λx. CHOICE (σ x) i)⦇n ↦ a⦈ phi} ⊆
         {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ⦇n ↦ a⦈ x) i) phi}` suffices_by
          (* little suffice *)
          (rw[] >> irule ultrafilter_SUBSET' >> rw[] (* 2 *)
          >- metis_tac[] >- (qexists_tac `I'` >> rw[SUBSET_DEF]))
          (* little suffice end *) >>
        rw[SUBSET_DEF] >>
        `(λx'. CHOICE (σ⦇n ↦ a⦈ x') x) = (λx'. CHOICE (σ x') x)⦇n ↦ (CHOICE a) x⦈`
          by (rw[FUN_EQ_THM] >> Cases_on `x' = n` >> fs[APPLY_UPDATE_THM]) >> rw[] >>
        first_x_assum irule >>
        `a IN (ultraproduct U I' (folmodels2Doms FMS))` by fs[ultraproduct_folmodel_def] >>
        drule ultraproduct_eqclass_non_empty >> rw[] >> `a <> {}` by metis_tac[] >>
        `CHOICE a IN a` by metis_tac[CHOICE_DEF] >>
        fs[ultraproduct_def,folmodels2Doms_def,partition_def,Cart_prod_def] >> rfs[])))
QED


Theorem ultraproduct_rep_independence_lemma:
!U I FMS σ.
  ultrafilter U I ==>
  IMAGE σ (univ(:num)) ⊆ ultraproduct U I (folmodels2Doms FMS) ==>
  !phi rv.
     (!v. v IN (FV phi) ==> (rv v) IN (σ v)) ==>
  ({i | i ∈ I ∧ feval (FMS i) (λx. CHOICE (σ x) i) phi} ∈ U <=>
   {i | i ∈ I ∧ feval (FMS i) (λv. (rv v) i) phi} ∈ U)
Proof
rw[] >> Cases_on `FV phi = {}`
>- (fs[] >>
    qmatch_abbrev_tac `A IN U <=> B IN U` >>
    `A = B` suffices_by metis_tac[] >>
    rw[EXTENSION,Abbr`A`,Abbr`B`] >>
    qmatch_abbrev_tac `R /\ P <=> R /\ Q` >>
    `P <=> Q` suffices_by metis_tac[] >> rw[Abbr`P`,Abbr`Q`] >>
    irule holds_valuation >> fs[]) >>
rw[EQ_IMP_THM] (* 2 *)
>- (qmatch_abbrev_tac `s IN U` >>
    `(BIGINTER
     { {i | i IN I' /\
            CHOICE (σ v) i = rv v i
       }
          | v IN (FV phi)}) IN U`
     suffices_by
      (drule ultrafilter_SUBSET' >> strip_tac >>
       qmatch_abbrev_tac `A IN U ==> s IN U` >>
       first_x_assum (qspecl_then
       [`A ∩ {i | i ∈ I' ∧ feval (FMS i) (λx. CHOICE (σ x) i) phi} `,`s`] assume_tac) >>
       rw[] >> first_x_assum irule >> rw[Abbr`A`,Abbr`s`,SUBSET_DEF] (* 2 *)
       >- (drule ultrafilter_INTER >> rw[]) >>
       fs[PULL_EXISTS] >>
       `feval (FMS x) (λx'. CHOICE (σ x') x) phi =
       feval (FMS x) (λv. rv v x) phi` suffices_by metis_tac[] >>
       irule holds_valuation >> metis_tac[]) >>
     (*suffices by tac end, reduce to proving biginter*)
   irule BIGINTER_FINITE >> rw[] (* 4 *)
   >- metis_tac[ultrafilter_INTER]
   >- (`FINITE (FV phi)` by metis_tac[FV_FINITE] >>
       qmatch_abbrev_tac `FINITE bs` >>
       `?f:num -> 'a -> bool. IMAGE f (FV phi) = bs` suffices_by metis_tac[IMAGE_FINITE] >>
       qexists_tac `\v.{i | i ∈ I' ∧ CHOICE (σ v) i = rv v i}` >>
       rw[EXTENSION,Abbr`bs`,IMAGE_DEF])
   >- (fs[GSYM MEMBER_NOT_EMPTY] >> metis_tac[])
   >- (rw[SUBSET_DEF] >> irule ultraproduct_same_eqclass >> rw[] >>
       map_every qexists_tac [`folmodels2Doms FMS`,`σ v`] >>
       `σ v IN (ultraproduct U I' (folmodels2Doms FMS))`
        by
         (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
       metis_tac[ultraproduct_eqclass_non_empty,CHOICE_DEF]))
>- (qmatch_abbrev_tac `s IN U` >>
    `(BIGINTER
     { {i | i IN I' /\
            CHOICE (σ v) i = rv v i
       }
          | v IN (FV phi)}) IN U`
     suffices_by
      (drule ultrafilter_SUBSET' >> strip_tac >>
       qmatch_abbrev_tac `A IN U ==> s IN U` >>
       first_x_assum (qspecl_then
       [`A ∩  {i | i ∈ I' ∧ feval (FMS i) (λv. rv v i) phi} `,`s`] assume_tac) >>
       rw[] >> first_x_assum irule >> rw[Abbr`A`,Abbr`s`,SUBSET_DEF] (* 2 *)
       >- (drule ultrafilter_INTER >> rw[]) >>
       fs[PULL_EXISTS] >>
       `feval (FMS x) (λx'. CHOICE (σ x') x) phi =
       feval (FMS x) (λv. rv v x) phi` suffices_by metis_tac[] >>
       irule holds_valuation >> metis_tac[]) >>
     (*suffices by tac end, reduce to proving biginter*)
   irule BIGINTER_FINITE >> rw[] (* 4 *)
   >- metis_tac[ultrafilter_INTER]
   >- (`FINITE (FV phi)` by metis_tac[FV_FINITE] >>
       qmatch_abbrev_tac `FINITE bs` >>
       `?f:num -> 'a -> bool. IMAGE f (FV phi) = bs` suffices_by metis_tac[IMAGE_FINITE] >>
       qexists_tac `\v.{i | i ∈ I' ∧ CHOICE (σ v) i = rv v i}` >>
       rw[EXTENSION,Abbr`bs`,IMAGE_DEF])
   >- (fs[GSYM MEMBER_NOT_EMPTY] >> metis_tac[])
   >- (rw[SUBSET_DEF] >> irule ultraproduct_same_eqclass >> rw[] >>
       map_every qexists_tac [`folmodels2Doms FMS`,`σ v`] >>
       `σ v IN (ultraproduct U I' (folmodels2Doms FMS))`
        by
         (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
       metis_tac[ultraproduct_eqclass_non_empty,CHOICE_DEF]))
QED


Theorem corollary_A_21:
 !U I FMS FM.
   ultrafilter U I ==> (!i. i IN I ==> FMS i = FM) ==>
   (∀i ff ll. i ∈ I ⇒ FM.Fun ff ll ∈ FM.Dom) ==>
   !σ.
      IMAGE σ (univ(:num)) ⊆ FM.Dom ==>
     !phi.
           (feval FM σ phi <=>
            feval (ultraproduct_folmodel U I FMS)
            (\x. {g | Uequiv U I (folmodels2Doms FMS) g (\i. σ x)}) phi)
Proof
rw[] >> drule thm_A_19_ii >> rw[] >> drule ultraproduct_rep_independence_lemma >> rw[] >>
`IMAGE
  (λx. {g | Uequiv U I' (folmodels2Doms FMS) g (λi. σ x)})
     𝕌(:num) ⊆ ultraproduct U I' (folmodels2Doms FMS)`
  by
   (rw[IMAGE_DEF,SUBSET_DEF,ultraproduct_def,partition_def] >>
    qexists_tac `\i. σ x'` >> rw[] (* 2 *)
    >- (rw[Cart_prod_def,folmodels2Doms_def] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
    >- (rw[EXTENSION,Uequiv_SYM] >> rw[EQ_IMP_THM,Uequiv_def])) >>
 `valuation (ultraproduct_folmodel U I' FMS)
  (λx. {g | Uequiv U I' (folmodels2Doms FMS) g (λi. σ x)})`
  by (fs[IMAGE_DEF,SUBSET_DEF,valuation_def,ultraproduct_folmodel_def] >> metis_tac[]) >>
 `∀i. i ∈ I' ⇒ wffm (FMS i)` by
   (rw[wffm_def] >> metis_tac[]) >>
first_x_assum drule >> rw[] >>
first_x_assum drule >> rw[] >>
first_x_assum (qspec_then `phi` assume_tac) >>
rw[EQ_IMP_THM] (* 2 *)
>- (first_x_assum (qspecl_then [`phi`,`\v i. σ v`] assume_tac) >>
    `(∀v.
             v ∈ FV phi ⇒
             Uequiv U I' (folmodels2Doms FMS) ((λv i. σ v) v) (λi. σ v))`
     by
      (rw[Uequiv_def] (* 4 *)
       >- (fs[folmodels2Doms_def,GSYM MEMBER_NOT_EMPTY] >> metis_tac[])
       >- (rw[Cart_prod_def,folmodels2Doms_def] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
       >- (rw[Cart_prod_def,folmodels2Doms_def] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
       >- fs[ultrafilter_def,proper_filter_def,filter_def]) >>
    `{i | i ∈ I' ∧ feval (FMS i) (λv. (λv i. σ v) v i) phi} ∈ U`
      suffices_by metis_tac[] >>
    `{i | i ∈ I' ∧ feval (FMS i) (λv. (λv i. σ v) v i) phi} = I'`
      by
       (rw[EXTENSION,EQ_IMP_THM] >>
        `(\v. σ v) = σ` by fs[FUN_EQ_THM] >> rw[]) >>
    rw[] >> fs[ultrafilter_def,proper_filter_def,filter_def])
>- (first_x_assum (qspecl_then [`phi`,`\v i. σ v`] assume_tac) >>
    `(∀v.
             v ∈ FV phi ⇒
             Uequiv U I' (folmodels2Doms FMS) ((λv i. σ v) v) (λi. σ v))`
     by
      (rw[Uequiv_def] (* 4 *)
       >- (fs[folmodels2Doms_def,GSYM MEMBER_NOT_EMPTY] >> metis_tac[])
       >- (rw[Cart_prod_def,folmodels2Doms_def] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
       >- (rw[Cart_prod_def,folmodels2Doms_def] >> fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
       >- fs[ultrafilter_def,proper_filter_def,filter_def]) >>
    first_x_assum drule >> strip_tac >>
    `{i | i ∈ I' ∧ feval (FMS i) (λv. (λv i. σ v) v i) phi} <> {}`
     by metis_tac[EMPTY_NOTIN_ultrafilter] >>
    fs[GSYM MEMBER_NOT_EMPTY] >>
    `(\v. σ v) = σ` by fs[FUN_EQ_THM] >> metis_tac[])
QED

Theorem rep_give_wf_valuation:
!U I FMS.
  ultrafilter U I ==>
   !rv. (!v i. i IN I ==> (rv v i) IN (FMS i).Dom) ==>
     IMAGE (λv. {g | Uequiv U I (folmodels2Doms FMS) g (rv v)}) 𝕌(:num) ⊆
        (ultraproduct U I (folmodels2Doms FMS))
Proof
 rw[IMAGE_DEF,SUBSET_DEF,ultraproduct_def,folmodels2Doms_def,partition_def] >>
 qexists_tac `rv v` >> rw[] (* 2 *)
 >- rw[Cart_prod_def]
 >- (rw[EXTENSION,Uequiv_def,EQ_IMP_THM] >>
     `{i | i ∈ I' ∧ x i = rv v i} = {i | i ∈ I' ∧ rv v i = x i}`
      suffices_by metis_tac[] >>
     rw[EXTENSION] >> metis_tac[])
QED


Theorem Uequiv_REFL:
!U I A f.
  ultrafilter U I ==>
   (!i. i IN I ==> (f i) IN (A i)) ==>
    Uequiv U I A f f
Proof
rw[Uequiv_def,Cart_prod_def] (* 2 *)
>- metis_tac[MEMBER_NOT_EMPTY]
>- fs[ultrafilter_def,proper_filter_def,filter_def]
QED

Theorem ultraproduct_suffices_rep:
!U I FMS rv.
  ultrafilter U I ==>
  (∀i ff ll. i ∈ I ⇒ (FMS i).Fun ff ll ∈ (FMS i).Dom) ==>
  !rv. (!v i. i IN I ==> (rv v i) IN (FMS i).Dom) ==>
   !phi.
     {i | i IN I /\ feval (FMS i) (\v. rv v i) phi} IN U ==>
     feval (ultraproduct_folmodel U I FMS)
           (\v. {g | Uequiv U I (folmodels2Doms FMS) g (rv v)}) phi
Proof
rw[] >> drule thm_A_19_ii >> rw[] >> drule ultraproduct_rep_independence_lemma >> rw[] >>
first_x_assum
 (qspecl_then
  [`phi`,
   `(λv. {g | Uequiv U I' (folmodels2Doms FMS) g (rv v)})`,
   `FMS`] assume_tac) >>
`IMAGE (λv. {g | Uequiv U I' (folmodels2Doms FMS) g (rv v)}) 𝕌(:num) ⊆
        ultraproduct U I' (folmodels2Doms FMS)`
 by metis_tac[rep_give_wf_valuation] >>
`valuation (ultraproduct_folmodel U I' FMS)
  (λv. {g | Uequiv U I' (folmodels2Doms FMS) g (rv v)})`
  by (fs[IMAGE_DEF,SUBSET_DEF,valuation_def,ultraproduct_folmodel_def] >> metis_tac[]) >>
 `∀i. i ∈ I' ⇒ wffm (FMS i)` by
   (rw[wffm_def] >> metis_tac[]) >>
first_x_assum drule >> rw[] >>
first_x_assum drule >> rw[] >>
first_x_assum (qspecl_then [`phi`,`rv`] assume_tac) >>
`(∀v. v ∈ FV phi ⇒ Uequiv U I' (folmodels2Doms FMS) (rv v) (rv v))`
 by
  (rw[] >> irule Uequiv_REFL >> rw[folmodels2Doms_def]) >>
metis_tac[]
QED


val _ = export_theory();
