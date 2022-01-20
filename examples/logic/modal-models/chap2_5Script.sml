open HolKernel Parse boolLib bossLib;
open chap1Theory;
open pred_setTheory;
open relationTheory;
open arithmeticTheory;
open set_relationTheory;
open pairTheory;

open chap2_1Theory;
open chap2_2Theory;

open ultrafilterTheory;

val _ = new_theory "chap2_5";



val BIGCONJ_EXISTS_DIST_TYPE = store_thm(
  "BIGCONJ_EXISTS_DIST_TYPE",
  ``∀s.
     FINITE s ⇒
     ?ff.
     (∀w:'b M.
        w ∈ M.frame.world ⇒ (satis M w ff ⇔ ∀f. f ∈ s ⇒ satis M w f)) /\
     (∀w:'c M.
        w ∈ M.frame.world ⇒ (satis M w ff ⇔ ∀f. f ∈ s ⇒ satis M w f))``,
  Induct_on `FINITE` >> rw[]
  >- (qexists_tac `TRUE` >> rw[TRUE_def,satis_def])
  >- (qexists_tac `AND e ff` >> rw[satis_def,AND_def] >> eq_tac >> rw[]
     >- rw[]
     >> metis_tac[]));



(* ultrafilter extensions *)

val HM_class_def = Define`
HM_class K = (!M M' w w'. (M IN K /\ M' IN K /\ w IN M.frame.world /\ w' IN M'.frame.world) ==>
(modal_eq M M' w w' ==> bisim_world M M' w w'))`;

val satisfiable_in_def = Define`
satisfiable_in Σ X M <=> X SUBSET M.frame.world /\
                         (?x. x IN X /\ (!form. form IN Σ ==> satis M x form))`;

val fin_satisfiable_in_def = Define`
fin_satisfiable_in Σ X M <=> (!S. S SUBSET Σ /\ FINITE S ==> satisfiable_in S X M)`;

val M_sat_def = Define`
M_sat M ⇔
            ∀w Σ.
                (w ∈ M.frame.world /\
                fin_satisfiable_in Σ
                  {v | v ∈ M.frame.world ∧ M.frame.rel w v} M) ⇒
                satisfiable_in Σ {v | v ∈ M.frame.world ∧ M.frame.rel w v} M`;



val BIGCONJ_EXISTS_2 = store_thm(
"BIGCONJ_EXISTS_2",
``∀s.
     FINITE s ⇒
     ?ff.
     ∀w M.
        w ∈ M.frame.world ⇒ (satis M w ff ⇔ ∀f. f ∈ s ⇒ satis M w f)``,
Induct_on `FINITE s` >> rpt strip_tac
>- (qexists_tac `TRUE` >> rw[] >> metis_tac[satis_def,TRUE_def])
>- (qexists_tac `AND ff e` >> rw[] >> eq_tac
   >- (rpt strip_tac >- metis_tac[satis_AND]
                     >- (`satis M w ff` by metis_tac[satis_AND] >> metis_tac[]))
   >- (rw[] >> `e = e ==> satis M w e` by metis_tac[] >> `e = e` by metis_tac[] >>
      `satis M w e` by metis_tac[] >>
      `!f. f IN s ==> satis M w f` by metis_tac[] >>
      `satis M w ff` by metis_tac[] >>
      metis_tac[satis_AND])));


val prop_2_54 = store_thm(
"prop_2_54",
``HM_class {M | M_sat M}``,
rw[HM_class_def,bisim_world_def,bisim_def] >>
qexists_tac `λn1 n2. (!form. satis M n1 form <=> satis M' n2 form)` >> rw[]
>- (fs[M_sat_def] >>
   `fin_satisfiable_in {form | satis M v form} {v | v ∈ M'.frame.world ∧ M'.frame.rel w''' v} M'` by
   (rw[fin_satisfiable_in_def,satisfiable_in_def]
    >- rw[SUBSET_DEF]
    >- (`∃ff.
        ∀w M.
           w ∈ M.frame.world ⇒ (satis M w ff ⇔ ∀f. f ∈ S' ⇒ satis M w f)` by metis_tac[BIGCONJ_EXISTS_2] >>
       `!f. f IN S' ==> satis M v f` by fs[SUBSET_DEF] >>
       `satis M v ff` by metis_tac[] >>
       `satis M w'' (DIAM ff)`  by metis_tac[satis_def] >>
       `satis M' w''' (DIAM ff)` by metis_tac[] >>
       `?v'. v' IN M'.frame.world /\ M'.frame.rel w''' v' /\ satis M' v' ff` by metis_tac[satis_def] >>
       qexists_tac `v'` >> rw[] >>
       `∀f. f ∈ S' ⇒ satis M' v' f` by metis_tac[] >> metis_tac[])) >>
   `satisfiable_in {form | satis M v form} {v | v ∈ M'.frame.world ∧ M'.frame.rel w''' v} M'` by metis_tac[] >> fs[satisfiable_in_def] >> qexists_tac `x` >> rw[] >>
   SPOSE_NOT_THEN ASSUME_TAC >>
   `¬((satis M v form ==> satis M' x form) /\ (satis M' x form ==> satis M v form))` by metis_tac[] >>
   `¬(satis M v form ==> satis M' x form) \/ ¬(satis M' x form ==> satis M v form)` by metis_tac[]
     >- (`satis M v form /\ ¬(satis M' x form)` by metis_tac[] >> metis_tac[])
     >- (`satis M' x form /\ ¬(satis M v form)` by metis_tac[] >>
        `satis M v (NOT form)` by metis_tac[satis_def] >>
        `¬(satis M' x (NOT form))` by metis_tac[satis_def] >>
        metis_tac[]))
>- (fs[M_sat_def] >>
   `fin_satisfiable_in {form | satis M' v' form} {v | v ∈ M.frame.world ∧ M.frame.rel w'' v} M` by
   (rw[fin_satisfiable_in_def,satisfiable_in_def]
    >- rw[SUBSET_DEF]
    >- (`∃ff.
        ∀w M.
           w ∈ M.frame.world ⇒ (satis M w ff ⇔ ∀f. f ∈ S' ⇒ satis M w f)` by metis_tac[BIGCONJ_EXISTS_2] >>
       `!f. f IN S' ==> satis M' v' f` by fs[SUBSET_DEF] >>
       `satis M' v' ff` by metis_tac[] >>
       `satis M' w''' (DIAM ff)`  by metis_tac[satis_def] >>
       `satis M w'' (DIAM ff)` by metis_tac[] >>
       `?v. v IN M.frame.world /\ M.frame.rel w'' v /\ satis M v ff` by metis_tac[satis_def] >>
       qexists_tac `v` >> rw[] >>
       `∀f. f ∈ S' ⇒ satis M v f` by metis_tac[] >> metis_tac[])) >>
   `satisfiable_in {form | satis M' v' form} {v | v ∈ M.frame.world ∧ M.frame.rel w'' v} M` by metis_tac[] >> fs[satisfiable_in_def] >> qexists_tac `x` >> rw[] >>
   SPOSE_NOT_THEN ASSUME_TAC >>
   `¬((satis M x form ==> satis M' v' form) /\ (satis M' v' form ==> satis M x form))` by metis_tac[] >>
   `¬(satis M x form ==> satis M' v' form) \/ ¬(satis M' v' form ==> satis M x form)` by metis_tac[]
     >- (`satis M x form /\ ¬(satis M' v' form)` by metis_tac[] >>
        `satis M' v' (NOT form)` by metis_tac[satis_def] >>
        `¬(satis M x (NOT form))` by metis_tac[satis_def] >>
        metis_tac[])
     >- (`satis M' v' form /\ ¬(satis M x form)` by metis_tac[] >>
        metis_tac[]))
>- metis_tac[modal_eq_tau]);



val prop_2_54_DIST_TYPE = store_thm(
"prop_2_54_DIST_TYPE",
``∀M M' w:'b w':'c.
        (M_sat M ∧ M_sat M' ∧ w ∈ M.frame.world ∧ w' ∈ M'.frame.world /\
        modal_eq M M' w w') ⇒
        bisim_world M M' w w'``,
rw[bisim_world_def,bisim_def] >>
qexists_tac `λn1 n2. (!form. satis M n1 form <=> satis M' n2 form)` >> rw[]
>- (fs[M_sat_def] >>
   `fin_satisfiable_in {form | satis M v form} {v | v ∈ M'.frame.world ∧ M'.frame.rel w''' v} M'` by
   (rw[fin_satisfiable_in_def,satisfiable_in_def]
    >- rw[SUBSET_DEF]
    >- (drule BIGCONJ_EXISTS_DIST_TYPE >> rw[] >>
       `!f. f IN S' ==> satis M v f` by fs[SUBSET_DEF] >>
       `satis M v ff` by metis_tac[] >>
       `satis M w'' (DIAM ff)`  by metis_tac[satis_def] >>
       `satis M' w''' (DIAM ff)` by metis_tac[] >>
       `?v'. v' IN M'.frame.world /\ M'.frame.rel w''' v' /\ satis M' v' ff` by metis_tac[satis_def] >>
       qexists_tac `v'` >> rw[] >>
       `∀f. f ∈ S' ⇒ satis M' v' f` by metis_tac[] >> metis_tac[])) >>
   `satisfiable_in {form | satis M v form} {v | v ∈ M'.frame.world ∧ M'.frame.rel w''' v} M'` by metis_tac[] >> fs[satisfiable_in_def] >> qexists_tac `x` >> rw[] >>
   SPOSE_NOT_THEN ASSUME_TAC >>
   `¬((satis M v form ==> satis M' x form) /\ (satis M' x form ==> satis M v form))` by metis_tac[] >>
   `¬(satis M v form ==> satis M' x form) \/ ¬(satis M' x form ==> satis M v form)` by metis_tac[]
     >- (`satis M v form /\ ¬(satis M' x form)` by metis_tac[] >> metis_tac[])
     >- (`satis M' x form /\ ¬(satis M v form)` by metis_tac[] >>
        `satis M v (NOT form)` by metis_tac[satis_def] >>
        `¬(satis M' x (NOT form))` by metis_tac[satis_def] >>
        metis_tac[]))
>- (fs[M_sat_def] >>
   `fin_satisfiable_in {form | satis M' v' form} {v | v ∈ M.frame.world ∧ M.frame.rel w'' v} M` by
   (rw[fin_satisfiable_in_def,satisfiable_in_def]
    >- rw[SUBSET_DEF]
    >- (drule BIGCONJ_EXISTS_DIST_TYPE >> rw[] >>
       `!f. f IN S' ==> satis M' v' f` by fs[SUBSET_DEF] >>
       `satis M' v' ff` by metis_tac[] >>
       `satis M' w''' (DIAM ff)`  by metis_tac[satis_def] >>
       `satis M w'' (DIAM ff)` by metis_tac[] >>
       `?v. v IN M.frame.world /\ M.frame.rel w'' v /\ satis M v ff` by metis_tac[satis_def] >>
       qexists_tac `v` >> rw[] >>
       `∀f. f ∈ S' ⇒ satis M v f` by metis_tac[] >> metis_tac[])) >>
   `satisfiable_in {form | satis M' v' form} {v | v ∈ M.frame.world ∧ M.frame.rel w'' v} M` by metis_tac[] >> fs[satisfiable_in_def] >> qexists_tac `x` >> rw[] >>
   SPOSE_NOT_THEN ASSUME_TAC >>
   `¬((satis M x form ==> satis M' v' form) /\ (satis M' v' form ==> satis M x form))` by metis_tac[] >>
   `¬(satis M x form ==> satis M' v' form) \/ ¬(satis M' v' form ==> satis M x form)` by metis_tac[]
     >- (`satis M x form /\ ¬(satis M' v' form)` by metis_tac[] >>
        `satis M' v' (NOT form)` by metis_tac[satis_def] >>
        `¬(satis M x (NOT form))` by metis_tac[satis_def] >>
        metis_tac[])
     >- (`satis M' v' form /\ ¬(satis M x form)` by metis_tac[] >>
        metis_tac[]))
>- metis_tac[modal_eq_tau]);


Theorem M_sat_bisim_modal_eq:
∀M M' w:'b w':'c.
 (M_sat M ∧ M_sat M' ∧ w ∈ M.frame.world ∧ w' ∈ M'.frame.world) ==>
        (modal_eq M M' w w' <=>
        bisim_world M M' w w')
Proof
rw[EQ_IMP_THM] (* 2 *)
>- metis_tac[prop_2_54_DIST_TYPE]
>- metis_tac[thm_2_20]
QED




val can_see_def = Define`
can_see M X = {w | w IN M.frame.world /\ ?x. x IN X /\ M.frame.rel w x}`;

val only_see_def = Define`
only_see M X = {w | w IN M.frame.world /\ (!x. x IN M.frame.world /\ M.frame.rel w x ==> x IN X)}`;

val valt_can_see = store_thm(
"valt_can_see",
``!M form. {w | w IN M.frame.world /\ satis M w (DIAM form)} = can_see M {v | v IN M.frame.world /\ satis M v form}``,
rw[] >> simp[EXTENSION,can_see_def] >> rw[] >> simp[EQ_IMP_THM] >> rw[]
>> metis_tac[satis_def]);

val valt_only_see = store_thm(
"valt_only_see",
``!M form. {w | w IN M.frame.world /\ satis M w (BOX form)} = only_see M {v | v IN M.frame.world /\ satis M v form}``,
rw[] >> simp[only_see_def,BOX_def,EXTENSION] >> rw[] >> simp[EQ_IMP_THM] >> rw[]
>> metis_tac[satis_def]);

val only_can_dual = store_thm(
"only_can_dual",
``!M X. X SUBSET M.frame.world ==> only_see M X = M.frame.world DIFF (can_see M (M.frame.world DIFF X))``,
simp[only_see_def,can_see_def,DIFF_DEF,EXTENSION] >> rw[] >> eq_tac >> rw[]
>> metis_tac[]);

val can_only_dual = store_thm(
"can_only_dual",
``!M X. X SUBSET M.frame.world ==> can_see M X = M.frame.world DIFF (only_see M (M.frame.world DIFF X))``,
simp[only_see_def,can_see_def,DIFF_DEF,EXTENSION] >> rw[] >> eq_tac >> rw[]
>- (fs[SUBSET_DEF] >> metis_tac[]) >> metis_tac[]);

(* exercise 2.5.5 *)

val UE_rel_def = Define`
UE_rel M u v <=> ultrafilter u M.frame.world /\
                 ultrafilter v M.frame.world /\
                 (!X. X IN v ==> (can_see M X) IN u)`;


val ultrafilter_DIFF = store_thm(
"ultrafilter_DIFF",
``!u W. ultrafilter u W ==> (!x. x SUBSET W ==> (x IN u <=> W DIFF x ∉ u))``,
rw[] >> fs[ultrafilter_def] >> `x IN POW W'` by simp[POW_DEF] >> metis_tac[]);

val ultrafilter_SUBSET = store_thm(
"ultrafilter_SUBSET",
``!u W. ultrafilter u W ==> (!x. x IN u ==> x SUBSET W)``,
rw[] >> fs[ultrafilter_def,proper_filter_def,filter_def,POW_DEF,SUBSET_DEF] >> metis_tac[]);

val exercise_2_5_5 = store_thm(
"exercise_2_5_5",
``!M u v. ultrafilter u M.frame.world /\ ultrafilter v M.frame.world ==>
(UE_rel M u v <=> {Y | (only_see M Y) IN u /\ Y SUBSET M.frame.world} SUBSET v)``,
rw[] >> eq_tac
>- (rw[UE_rel_def] >> rw[Once SUBSET_DEF] >>
`!x. ¬(can_see M x IN u) ==> ¬(x IN v)` by metis_tac[] >>
`!x. x SUBSET M.frame.world ==> (x IN v <=> M.frame.world DIFF x ∉ v)` by metis_tac[ultrafilter_DIFF] >>
`!x. x SUBSET M.frame.world /\ can_see M x ∉ u ==> M.frame.world DIFF x IN v` by metis_tac[] >>
`!x. x SUBSET M.frame.world ==> only_see M x = M.frame.world DIFF (can_see M (M.frame.world DIFF x))` by metis_tac[only_can_dual] >>
`only_see M x = M.frame.world DIFF can_see M (M.frame.world DIFF x)` by metis_tac[] >>
`!x. x SUBSET M.frame.world ==> (x IN u <=> M.frame.world DIFF x ∉ u)` by metis_tac[ultrafilter_DIFF] >>
`can_see M (M.frame.world DIFF x) SUBSET M.frame.world` by simp[can_see_def,SUBSET_DEF] >>
`M.frame.world DIFF can_see M (M.frame.world DIFF x) IN u` by metis_tac[] >>
`can_see M (M.frame.world DIFF x) ∉ u` by metis_tac[] >>
`(M.frame.world DIFF x) ∉ v` by metis_tac[] >>
metis_tac[])
>- (rw[Once SUBSET_DEF] >> rw[UE_rel_def] >>
`X SUBSET M.frame.world` by metis_tac[ultrafilter_SUBSET] >>
`!x. ¬(x IN v) ==> ¬(only_see M x IN u) \/ ¬(x SUBSET M.frame.world)` by metis_tac[] >>
`!x. (¬(x IN v) /\ x SUBSET M.frame.world) ==> ¬(only_see M x IN u)` by metis_tac[] >>
`!x. x SUBSET M.frame.world ==> (x IN v <=> M.frame.world DIFF x ∉ v)` by metis_tac[ultrafilter_DIFF] >>
`¬((M.frame.world DIFF X) IN v)` by metis_tac[] >>
`(M.frame.world DIFF X) SUBSET M.frame.world` by metis_tac[DIFF_SUBSET] >>
`¬(only_see M (M.frame.world DIFF X) IN u)` by metis_tac[] >>
`only_see M (M.frame.world DIFF X) SUBSET M.frame.world` by simp[only_see_def,SUBSET_DEF] >>
`!x. x SUBSET M.frame.world ==> (x IN u <=> M.frame.world DIFF x ∉ u)` by metis_tac[ultrafilter_DIFF] >>
`M.frame.world DIFF (only_see M (M.frame.world DIFF X)) IN u` by metis_tac[] >>
metis_tac[can_only_dual]));

val UE_def = Define`
  UE M = <| frame := <| world := {u | ultrafilter u M.frame.world};
                        rel := UE_rel M |>;
            valt := \p v. (ultrafilter v M.frame.world /\ ((M.valt p) ∩ M.frame.world) IN v) |>`;


val only_see_INTER = store_thm(
  "only_see_INTER",
  ``only_see M (X ∩ Y) = only_see M X ∩ only_see M Y``,
  rw[only_see_def,EXTENSION] >> eq_tac >> rw[]);

val BIGINTER_FINITE = store_thm(
"BIGINTER_FINITE",
``!s'. FINITE s' ==> s' <> {} /\ s' SUBSET s ==> (∀a b. a ∈ s ∧ b ∈ s ⇒ a ∩ b ∈ s) ==> BIGINTER s' IN s``,
Induct_on `FINITE s'` >> rw[] >> Cases_on `s' = {}`
>- fs[]
>- metis_tac[]);


val SUBSET_UNION_DIFF = store_thm(
  "SUBSET_UNION_DIFF",
``s SUBSET a ∪ b /\ s <> {} /\ ¬(s SUBSET b) ==> s DIFF b <> {}``,
rw[SUBSET_DEF,DIFF_DEF,EXTENSION]);



val SUBSET_SING = store_thm(
  "SUBSET_SING",
``s <> {} /\ s <> {a} ==> ¬(s SUBSET {a})``,
rw[SUBSET_DEF] >> SPOSE_NOT_THEN ASSUME_TAC >> fs[EXTENSION] >> metis_tac[]);



val IN_DIFF = store_thm(
  "IN_DIFF",
``a IN s ==> s = (s DIFF {a}) UNION {a}``,
rw[DIFF_DEF,UNION_DEF,EXTENSION] >> metis_tac[]);


val NOTIN_DIFF = store_thm(
  "NOTIN_DIFF",
``a NOTIN s ==> s DIFF {a} = s``,
rw[DIFF_DEF,EXTENSION] >> metis_tac[])

val INTER_ABSORB = store_thm(
  "INTER_ABSORB",
  ``a ∩ b ∩ a = a ∩ b``,
  fs[EXTENSION,INTER_DEF] >> metis_tac[]);

val prop_2_59_i = store_thm(
  "prop_2_59_i",
  ``!phi u M. ultrafilter u M.frame.world ==>
          ({w | w IN M.frame.world /\ satis M w phi} IN u <=> satis (UE M) u phi)``,
  Induct_on `phi` >> rw[]
  >- (rw[satis_def,EQ_IMP_THM]
     >- fs[UE_def]
     >- (fs[UE_def] >>
        `M.valt n ∩ M.frame.world = {w | w ∈ M.frame.world ∧ w ∈ M.frame.world ∧ w ∈ M.valt n}`
            by (rw[EXTENSION] >> metis_tac[]) >> rw[])
     >- (fs[UE_def] >>
        `M.valt n ∩ M.frame.world = {w | w ∈ M.frame.world ∧ w ∈ M.frame.world ∧ w ∈ M.valt n}`
            by (rw[EXTENSION] >> metis_tac[]) >> fs[]))
  >- (rw[satis_def] >>
     `{w | w ∈ M.frame.world ∧ (satis M w phi ∨ satis M w phi')} =
     {w | w ∈ M.frame.world ∧ satis M w phi} ∪ {w | w ∈ M.frame.world ∧ satis M w phi'}` by (simp[EXTENSION] >> metis_tac[]) >>
     `{w | w ∈ M.frame.world ∧ satis M w phi} SUBSET M.frame.world` by fs[SUBSET_DEF] >>
     `{w | w ∈ M.frame.world ∧ satis M w phi'} SUBSET M.frame.world` by fs[SUBSET_DEF] >>
     `{w | w ∈ M.frame.world ∧ (satis M w phi ∨ satis M w phi')} ∈ u ⇔
     ({w | w ∈ M.frame.world ∧ satis M w phi'} IN u) \/
     ({w | w ∈ M.frame.world ∧ satis M w phi} IN u)` by metis_tac[ultrafilter_UNION] >>
     metis_tac[])
  >- (fs[ultrafilter_def,filter_def,proper_filter_def] >>
     `(M.frame.world DIFF M.frame.world) ∉ u` by metis_tac[POW_DEF,SUBSET_DEF] >>
     `M.frame.world DIFF M.frame.world = {}` by fs[DIFF_DEF] >>
     `{w | w ∈ M.frame.world ∧ satis M w ⊥} = {}` by (rw[EXTENSION] >> metis_tac[satis_def]) >> metis_tac[satis_def])
  >- (rw[satis_def] >> first_x_assum drule >> rw[] >> fs[ultrafilter_def,proper_filter_def,filter_def] >>
     `{w | w ∈ M.frame.world ∧ w ∈ M.frame.world ∧ ¬satis M w phi} IN (POW M.frame.world)` by (rw[Once POW_DEF] >> fs[SUBSET_DEF]) >>
     `{w | w ∈ M.frame.world ∧ w ∈ M.frame.world ∧ ¬satis M w phi} =
     M.frame.world DIFF {w | w IN M.frame.world /\ satis M w phi}`
         by (simp[EXTENSION,DIFF_DEF] >> metis_tac[]) >>
     `{w | w ∈ M.frame.world ∧ w ∈ M.frame.world ∧ ¬satis M w phi} ∈ u <=>
      M.frame.world DIFF {w | w ∈ M.frame.world ∧ satis M w phi} IN u` by fs[] >>
     `{w | w ∈ M.frame.world ∧ satis M w phi} IN (POW M.frame.world)` by (rw[Once POW_DEF] >> fs[SUBSET_DEF]) >>
     `M.frame.world DIFF {w | w ∈ M.frame.world ∧ satis M w phi} IN u <=>
     {w | w ∈ M.frame.world ∧ satis M w phi} NOTIN u` by metis_tac[] >>
     `{w | w ∈ M.frame.world ∧ satis M w phi} NOTIN u <=> ¬satis (UE M) u phi` by metis_tac[] >>
     `u IN (UE M).frame.world` by (rw[UE_def] >> fs[ultrafilter_def,proper_filter_def,filter_def] >> metis_tac[]) >>
     metis_tac[satis_def])
  >- (rw[EQ_IMP_THM] (* 2 *)
     >- (rw[satis_def]
        >- fs[UE_def]
        >- (`(UE M).frame.rel = UE_rel M` by fs[UE_def] >> fs[] >>
           `?v. {Y | only_see M Y ∈ u ∧ Y ⊆ M.frame.world} ⊆ v /\
                v ∈ (UE M).frame.world ∧ satis (UE M) v phi`
               suffices_by (rw[] >> qexists_tac `v` >> rw[] >> `ultrafilter v M.frame.world` by fs[UE_def] >>
                           metis_tac[exercise_2_5_5]) >>
           qabbrev_tac `s = {Y | only_see M Y ∈ u ∧ Y ⊆ M.frame.world}` >>
           `!a b. a IN s /\ b IN s ==> a ∩ b IN s`
               by (rw[] >> fs[Abbr`s`] >>
                  `only_see M a ∩ only_see M b IN u` by fs[ultrafilter_def,proper_filter_def,filter_def] >>
                  `only_see M a ∩ only_see M b = only_see M (a INTER b)` by fs[only_see_INTER] >>
                  fs[SUBSET_DEF]) >>
           `!a. a IN s ==> a ∩ {w | w ∈ M.frame.world ∧ satis M w phi} <> {}`
               by (rw[] >> fs[Abbr`s`] >>
                  `{} NOTIN u` by metis_tac[EMPTY_NOTIN_ultrafilter] >>
                  `{w | w ∈ M.frame.world ∧ satis M w (◇ phi)} ∩ only_see M a IN u` by fs[ultrafilter_def,proper_filter_def,filter_def] >>
                  `{w | w ∈ M.frame.world ∧ satis M w (◇ phi)} ∩ only_see M a <> {}` by metis_tac[] >>
                  `?x. x IN {w | w ∈ M.frame.world ∧ satis M w (◇ phi)} ∩ only_see M a` by metis_tac[MEMBER_NOT_EMPTY] >>
                  fs[] >>
                  `?y. y IN M.frame.world /\ satis M y phi /\ M.frame.rel x y` by metis_tac[satis_def] >>
                  `y IN a` by fs[only_see_def] >>
                  `y IN a ∩ {w | w ∈ M.frame.world ∧ satis M w phi}` by fs[] >>
                  metis_tac[MEMBER_NOT_EMPTY]) >>
           `{} NOTIN s`
               by (SPOSE_NOT_THEN ASSUME_TAC >>
                  `{} ∩ {w | w ∈ M.frame.world ∧ satis M w phi} = ∅` by fs[EXTENSION] >> metis_tac[]) >>
           (* proof of FIP *)
           `FIP (s ∪ {{w | w ∈ M.frame.world ∧ satis M w phi}}) M.frame.world`
               by (rw[FIP_def]  (* 3 *)
                  >- (fs[Abbr`s`] >> rw[POW_DEF,SUBSET_DEF])
                  >- rw[POW_DEF,SUBSET_DEF]
                  >- (`!S'. FINITE S' ==> S' ⊆ s ∪ {{w | w ∈ M.frame.world ∧ satis M w phi}} /\ S' ≠ ∅ ==>
                     BIGINTER S' ≠ ∅` suffices_by metis_tac[] >>
                     Induct_on `FINITE S'` >> rw[] (* 2 *)
                     (* base case *)
                     >- (Cases_on `S'' = {}` (* 2 *)
                        >- (fs[] >> SPOSE_NOT_THEN ASSUME_TAC >>
                           `e ∩ {w | w ∈ M.frame.world ∧ satis M w phi} = ∅` by fs[EXTENSION] >> metis_tac[])
                        >- (`BIGINTER S'' ≠ ∅` by metis_tac[] >>
                           `(S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}}) SUBSET s`
                               by (fs[SUBSET_DEF,DIFF_DEF] >> metis_tac[]) >>
                           `FINITE (S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}})` by fs[] >>
                           Cases_on `S'' = {{w | w ∈ M.frame.world ∧ satis M w phi}}` (* 2 *)
                           >- fs[BIGINTER]
                           >- (`¬(S'' SUBSET {{w | w ∈ M.frame.world ∧ satis M w phi}})`
                                  by metis_tac[SUBSET_SING] >>
                              `S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}} <> {}`
                                  by metis_tac[SUBSET_UNION_DIFF] >>
                              Cases_on `{w | w ∈ M.frame.world ∧ satis M w phi} IN S''`
                              >- (`S'' =
                                 (S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}}) UNION
                                 {{w | w ∈ M.frame.world ∧ satis M w phi}}`
                                     by metis_tac[IN_DIFF] >>
                                 `BIGINTER (S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}}) IN s` by
                                 metis_tac[BIGINTER_FINITE] >>
                                 `e INTER (BIGINTER (S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}})) IN s`
                                 by metis_tac[] >>
                                 `BIGINTER ((S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}}) ∪
                                           {{w | w ∈ M.frame.world ∧ satis M w phi}}) =
                                  (BIGINTER (S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}})) ∩
                                           {w | w ∈ M.frame.world ∧ satis M w phi}`
                                     by fs[BIGINTER_UNION] >>
                                 `BIGINTER S'' =
                                 BIGINTER (S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}}) ∩
                                 {w | w ∈ M.frame.world ∧ satis M w phi}` by metis_tac[] >> rw[] >>
                                 simp[INTER_ASSOC])
                              >- (`S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}} = S''`
                                     by metis_tac[NOTIN_DIFF] >>
                                 `BIGINTER (S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}}) IN s` by
                                 metis_tac[BIGINTER_FINITE] >>
                                 `e INTER (BIGINTER (S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}})) IN s`
                                     by metis_tac[] >>
                                 `e INTER (BIGINTER (S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}})) <> {}`
                                     by metis_tac[] >>
                                 metis_tac[]))))
                   (* step case *)
                   >- (Cases_on `{w | w ∈ M.frame.world ∧ satis M w phi} IN S''`
                      >- (`S'' =
                         (S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}}) UNION
                         {{w | w ∈ M.frame.world ∧ satis M w phi}}`
                             by metis_tac[IN_DIFF] >>
                         `BIGINTER (S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}}) IN s` by
                         metis_tac[BIGINTER_FINITE] >>
                         `BIGINTER ((S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}}) ∪
                         {{w | w ∈ M.frame.world ∧ satis M w phi}}) =
                         (BIGINTER (S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}})) ∩
                         {w | w ∈ M.frame.world ∧ satis M w phi}`
                             by fs[BIGINTER_UNION] >>
                         `BIGINTER S'' =
                         BIGINTER (S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}}) ∩
                         {w | w ∈ M.frame.world ∧ satis M w phi}` by metis_tac[] >> rw[] >>
                         simp[INTER_ASSOC] >>
                         metis_tac[INTER_ABSORB])
                       >- (`S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}} = S''`
                              by metis_tac[NOTIN_DIFF] >>
                          `(S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}}) SUBSET s`
                              by (fs[SUBSET_DEF,DIFF_DEF] >> metis_tac[]) >>
                          `FINITE (S'' DIFF {{w | w ∈ M.frame.world ∧ satis M w phi}})` by fs[] >>
                          Cases_on `S'' = {}`
                           >- (fs[] >> SPOSE_NOT_THEN ASSUME_TAC >>
                              `{w | w ∈ M.frame.world ∧ satis M w (◇ phi)} <> {}`
                                  by metis_tac[EMPTY_NOTIN_ultrafilter] >>
                              `?x. x IN {w | w ∈ M.frame.world ∧ satis M w (◇ phi)}`
                                  by metis_tac[MEMBER_NOT_EMPTY] >> fs[] >>
                              `?y. y IN M.frame.world /\ satis M y phi` by metis_tac[satis_def] >>
                              `y IN {w | w ∈ M.frame.world ∧ satis M w phi}` by fs[] >>
                              metis_tac[MEMBER_NOT_EMPTY])
                           >- (`S'' SUBSET s` by metis_tac[] >>
                              `BIGINTER S'' IN s` by metis_tac[BIGINTER_FINITE] >> metis_tac[INTER_COMM]))))) >>
         (* proof of FIP ends *)
         `M.frame.world <> {}` by fs[ultrafilter_def,proper_filter_def,filter_def] >>
         `?u. ultrafilter u M.frame.world /\ (s ∪ {{w | w ∈ M.frame.world ∧ satis M w phi}}) SUBSET u`
             by metis_tac[ultrafilter_theorem_corollary] >>
         qexists_tac `u'` >> rw[]
         >- fs[SUBSET_DEF]
         >- fs[UE_def]
         >- (`{w | w ∈ M.frame.world ∧ satis M w phi} IN u'` by fs[SUBSET_DEF] >> metis_tac[])))
     >- (fs[satis_def] >>
        `UE_rel M u v` by fs[UE_def] >>
        fs[UE_rel_def] >>
        `{w | w ∈ M.frame.world ∧ satis M w phi} ∈ v` by metis_tac[] >>
        `(can_see M {w | w ∈ M.frame.world ∧ satis M w phi}) ∈ u` by metis_tac[] >>
        `can_see M {w | w ∈ M.frame.world ∧ satis M w phi} =
        {w | w ∈ M.frame.world ∧ satis M w (◇ phi)}` by metis_tac[valt_can_see] >>
        fs[satis_def])));

val prop_2_59_ii = store_thm(
  "prop_2_59_ii",
  ``!M w. w IN M.frame.world ==> modal_eq M (UE M) w (principle_UF w M.frame.world)``,
  rw[modal_eq_tau] >>
  `M.frame.world <> {}` by metis_tac[MEMBER_NOT_EMPTY] >>
  `ultrafilter (principle_UF w M.frame.world) M.frame.world` by metis_tac[principle_UF_UF] >>
  drule prop_2_59_i >> rw[] >>
  `{w | w ∈ M.frame.world ∧ satis M w form} ∈ principle_UF w M.frame.world <=> satis M w form`
      suffices_by metis_tac[] >>
  rw[EQ_IMP_THM]
  >- (`{w | w ∈ M.frame.world ∧ satis M w form} ∈
         principle_UF w M.frame.world` by metis_tac[] >> fs[principle_UF_def])
  >- (`{w | w ∈ M.frame.world ∧ satis M w form} ∈
         principle_UF w M.frame.world` suffices_by metis_tac[] >> fs[principle_UF_def,SUBSET_DEF] >> metis_tac[]));

val only_see_whole_world = store_thm(
  "only_see_whole_world",
  ``only_see M M.frame.world = M.frame.world``,
  rw[only_see_def]);


val prop_2_61 = store_thm(
  "prop_2_61",
  ``!M:'b model. M_sat (UE M)``,
  rw[] >> Cases_on `M.frame.world = {}`
>- (rw[M_sat_def] >> fs[UE_def,ultrafilter_def] >> fs[proper_filter_def,filter_def])
>- (rw[M_sat_def,fin_satisfiable_in_def,satisfiable_in_def]
  >- fs[SUBSET_DEF]
  >- (qabbrev_tac
     `d = {{w | w IN M.frame.world /\ !phi. phi IN s ==> satis M w phi}| FINITE s /\ s SUBSET Σ}
     UNION {Y | only_see M Y ∈ w ∧ Y ⊆ M.frame.world}` >>
     `!a b. a IN {{w | w IN M.frame.world /\ !phi. phi IN s ==> satis M w phi}| FINITE s /\ s SUBSET Σ} /\
            b IN {Y | only_see M Y ∈ w ∧ Y ⊆ M.frame.world} ==> a ∩ b <> {}`
         by (rw[] >> first_x_assum drule >> rw[] >>
             drule (BIGCONJ_EXISTS_DIST_TYPE |> INST_TYPE [beta |-> ``:'b``,gamma |-> ``:('b -> bool) -> bool``]) >>
             rw[] >>
             `satis (UE M) x ff` by metis_tac[] >>
             `ultrafilter x M.frame.world` by fs[UE_def] >>
             `{w | w ∈ M.frame.world ∧ satis M w ff} ∈ x` by metis_tac[prop_2_59_i] >>
             `UE_rel M w x` by fs[UE_def] >>
             `ultrafilter w M.frame.world` by fs[UE_def] >>
             `{Y | only_see M Y ∈ w ∧ Y ⊆ M.frame.world} ⊆ x`
                 by metis_tac[exercise_2_5_5,UE_def] >>
             `b IN {Y | only_see M Y ∈ w ∧ Y ⊆ M.frame.world}` by fs[] >>
             `b IN x` by fs[SUBSET_DEF] >>
             `({w | w ∈ M.frame.world ∧ satis M w ff} ∩ b) IN x`
                 by metis_tac[ultrafilter_def,filter_def,proper_filter_def] >>
             `({w | w ∈ M.frame.world ∧ satis M w ff} ∩ b) <> {}`
                 by (SPOSE_NOT_THEN ASSUME_TAC  >> metis_tac[EMPTY_NOTIN_ultrafilter]) >>
             `{w | w ∈ M.frame.world ∧ ∀phi. phi ∈ s ⇒ satis M w phi} =
             {w | w ∈ M.frame.world ∧ satis M w ff}`
                 by (rw[EXTENSION,EQ_IMP_THM] >> metis_tac[]) >> metis_tac[]) >>
      `FIP d M.frame.world`
         by (fs[Abbr`d`] >> irule FIP_closed_under_intersection (* 7 *) >> rpt strip_tac
                         >- (rw[] >> fs[] >> qexists_tac `s ∪ s'` >> rw[] >> rw[EXTENSION,EQ_IMP_THM] >> metis_tac[])
                         >- (rw[] >> fs[] >> metis_tac[])
                         >- (rw[] >> simp[only_see_INTER] (* 2 *)
                             >- (`ultrafilter w M.frame.world` by fs[UE_def] >> fs[] >>
                                 metis_tac[ultrafilter_def,proper_filter_def,filter_def])
                             >- fs[INTER_DEF,SUBSET_DEF])
                         >- (`M.frame.world IN
                            {{w | w ∈ M.frame.world ∧ ∀phi. phi ∈ s ⇒ satis M w phi} | FINITE s ∧ s ⊆ Σ}`
                               suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
                            fs[] >> qexists_tac `{}` >> rw[])
                         >- (`M.frame.world IN {Y | only_see M Y ∈ w ∧ Y ⊆ M.frame.world}`
                               suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
                            fs[] >> simp[only_see_whole_world] >> `ultrafilter w M.frame.world` by fs[UE_def] >>
                            metis_tac[ultrafilter_def,proper_filter_def,filter_def])
                         >- (fs[POW_DEF] >> rw[Once SUBSET_DEF] >> rw[SUBSET_DEF])
                         >- (rw[POW_DEF] >> fs[SUBSET_DEF])) >>
     `∃u. ultrafilter u M.frame.world ∧ d ⊆ u` by metis_tac[ultrafilter_theorem_corollary] >>
     qexists_tac `u` >> rw[] (* 3 *)
     >- fs[UE_def]
     >- (rw[UE_def] >>
        `ultrafilter w M.frame.world` by fs[UE_def] >>
        `{Y | only_see M Y ∈ w ∧ Y ⊆ M.frame.world} ⊆ u` suffices_by metis_tac[exercise_2_5_5] >>
        `{Y | only_see M Y ∈ w ∧ Y ⊆ M.frame.world} SUBSET d` by fs[Abbr`d`] >>
        metis_tac[SUBSET_TRANS])
     >- (`{w | w ∈ M.frame.world ∧ satis M w form} ∈ u` suffices_by metis_tac[prop_2_59_i] >>
        `{w | w ∈ M.frame.world ∧ satis M w form} ∈ d` suffices_by metis_tac[SUBSET_DEF] >>
        `{w | w ∈ M.frame.world ∧ satis M w form} IN
        {{w | w ∈ M.frame.world ∧ ∀phi. phi ∈ s ⇒ satis M w phi} | FINITE s ∧ s ⊆ Σ}` suffices_by fs[Abbr`d`] >>
        fs[] >> qexists_tac `{form}` >> rw[]))));

val modal_eq_SYM = store_thm(
  "modal_eq_SYM",
  ``!M M' w w'. modal_eq M M' w w' <=> modal_eq M' M w' w``,
  metis_tac[modal_eq_def]);

val modal_eq_TRANS = store_thm(
  "modal_eq_TRANS",
  ``!M M' M'' w w' w''. modal_eq M M' w w' /\ modal_eq M' M'' w' w'' ==> modal_eq M M'' w w''``,
  metis_tac[modal_eq_def]);



val thm_2_62 = store_thm(
  "thm_2_62",
  ``!M M' w:'b w':'c. w IN M.frame.world /\ w' IN M'.frame.world
                        ==> (modal_eq M M' w w' <=>
                            bisim_world (UE M) (UE M') (principle_UF w M.frame.world) (principle_UF w' M'.frame.world))``,
  rw[EQ_IMP_THM]
  >- (`∀M M' w:('b -> bool) -> bool w':('c -> bool) -> bool.
     M_sat M ∧ M_sat M' ∧ w ∈ M.frame.world ∧ w' ∈ M'.frame.world ⇒
     modal_eq M M' w w' ⇒
     bisim_world M M' w w'` by metis_tac[prop_2_54_DIST_TYPE] >>
     `M_sat (UE M) /\ M_sat (UE M')` by metis_tac[prop_2_61] >>
     fs[HM_class_def] >>
     `(principle_UF w M.frame.world) IN (UE M).frame.world`
         by (fs[UE_def] >>
            `M.frame.world <> {}`  by metis_tac[MEMBER_NOT_EMPTY] >>
            metis_tac[principle_UF_UF]) >>
     `(principle_UF w' M'.frame.world) IN (UE M').frame.world`
         by (fs[UE_def] >>
            `M'.frame.world <> {}`  by metis_tac[MEMBER_NOT_EMPTY] >>
            metis_tac[principle_UF_UF]) >>
     `modal_eq (UE M) (UE M') (principle_UF w M.frame.world) (principle_UF w' M'.frame.world)`
         suffices_by metis_tac[] >>
     `modal_eq M (UE M) w (principle_UF w M.frame.world) /\
     modal_eq M' (UE M') w' (principle_UF w' M'.frame.world)` by metis_tac[prop_2_59_ii] >>
     metis_tac[modal_eq_SYM,modal_eq_TRANS])
  >- (`modal_eq (UE M) (UE M') (principle_UF w M.frame.world) (principle_UF w' M'.frame.world)`
         by metis_tac[thm_2_20] >>
     `modal_eq M (UE M) w (principle_UF w M.frame.world) /\
     modal_eq M' (UE M') w' (principle_UF w' M'.frame.world)` by metis_tac[prop_2_59_ii] >>
     metis_tac[modal_eq_TRANS,modal_eq_SYM]));


Theorem can_see_UNION:
can_see M (X ∪ Y) = (can_see M X) ∪ (can_see M Y)
Proof
rw[can_see_def,EXTENSION,EQ_IMP_THM] (* 6 *)
>> metis_tac[]
QED

val _ = export_theory();
