open HolKernel Parse boolLib bossLib;
open numpairTheory;
open pred_setTheory;
open relationTheory;
open listTheory;
open arithmeticTheory;
open set_relationTheory;
open pairTheory;

open nlistTheory;

val _ = new_theory "equiv_on_partition";

val partition_eq_EMPTY = store_thm(
  "partition_eq_EMPTY[simp]",
  ``(partition R s = {} <=> s = {}) /\ ({} = partition R s <=> s = {})``,
  conj_tac >> rw[partition_def, Once EXTENSION] >> simp[EXTENSION]);


val equiv_on_same_partition1 = store_thm(
"equiv_on_same_partition1",
``R equiv_on s ==> !t. t IN partition R s ==> !x y. x IN s /\ y IN s /\ R x y ==> (x IN t <=> y IN t)``,
rw[partition_def,equiv_on_def] >> eq_tac >> rw[]
>> metis_tac[]);


val equiv_on_same_partition = store_thm(
"equiv_on_same_partition",
``R equiv_on s ==> !x y. R x y ==> (!t1 t2. t1 IN partition R s /\ t2 IN partition R s /\ x IN t1 /\ y IN t2 ==> t1 = t2)``,
rw[partition_def,equiv_on_def] >> rw[EXTENSION,EQ_IMP_THM] >> fs[]
>> metis_tac[]);

val equiv_partition_unique = store_thm(
"equiv_partition_unique",
``R equiv_on s ==> !x. x IN s /\ p1 IN partition R s /\ x IN p1 ==> (!p2. p2 IN partition R s /\ x IN p2 ==> p2 = p1)``,
rw[partition_def,equiv_on_def] >> rw[EXTENSION,EQ_IMP_THM]
>> fs[] >> metis_tac[]);


val equiv_on_SUBSET_partition = store_thm(
"equiv_on_SUBSET_partition",
``R equiv_on s ==> (!p. p SUBSET (partition R s) ==> p = partition R (BIGUNION p))``,
rw[partition_def,SUBSET_DEF,equiv_on_def] >> rw[Once EXTENSION,EQ_IMP_THM]
>- (`∃x'. x' ∈ s ∧ x = {y | y ∈ s ∧ R x' y}` by metis_tac[] >>
   qexists_tac `x'` >> rw[]
   >- (qexists_tac `{y | y ∈ s ∧ R x' y}` >> rw[])
   >- (rw[EXTENSION,EQ_IMP_THM]
      >- (qexists_tac `{y | y ∈ s ∧ R x' y}` >> rw[])
      >- (`?n. n IN s /\ s' = {k | k IN s /\ R n k}` by metis_tac[] >> fs[])))
>- (`?n. n IN s /\ s' = {k | k IN s /\ R n k}` by metis_tac[] >>
   `{y | (∃s. y ∈ s ∧ s ∈ p) ∧ R x' y} = {k | k ∈ s ∧ R n k}` suffices_by metis_tac[] >>
   fs[] >> rw[EXTENSION,EQ_IMP_THM]
   >- (`?u. u IN s /\ s' = {y | y IN s /\ R u y}` by metis_tac[] >> fs[])
   >- (`x IN s` by (`?u. u IN s /\ s' = {y | y IN s /\ R u y}` by metis_tac[] >> fs[]) >> metis_tac[])
   >- (qexists_tac `{k | k ∈ s ∧ R n k}` >> fs[])
   >- metis_tac[]));

val equiv_on_disjoint_partition = store_thm(
"equiv_on_disjoint_partition",
``R equiv_on s ==> !A B. s = A UNION B /\ (!x. x IN A ==> !y. y IN B ==> ¬R x y) ==> partition R s = (partition R A) UNION (partition R B)``,
rw[partition_def] >> rw[Once EXTENSION,EQ_IMP_THM]
>- (`(∃x. x ∈ A ∧ {y | (y ∈ A ∨ y ∈ B) ∧ R x' y} = {y | y ∈ A ∧ R x y})` suffices_by metis_tac[] >>
   qexists_tac `x'` >> rw[EXTENSION,EQ_IMP_THM] >> metis_tac[])
>- (`∃x. x ∈ B ∧ {y | (y ∈ A ∨ y ∈ B) ∧ R x' y} = {y | y ∈ B ∧ R x y}` suffices_by metis_tac[] >>
   qexists_tac `x'` >> rw[EXTENSION,EQ_IMP_THM] >> fs[equiv_on_def,UNION_DEF] >> metis_tac[])
>- (qexists_tac `x'` >> rw[EXTENSION,EQ_IMP_THM] >> metis_tac[equiv_on_def,UNION_DEF])
>- (qexists_tac `x'` >> rw[EXTENSION,EQ_IMP_THM] >> fs[equiv_on_def,UNION_DEF] >> metis_tac[]));

val equiv_on_INSERT_partition_UNION = store_thm(
"equiv_on_INSERT_partition_UNION",
``R equiv_on s ==>  !e p. e INSERT p = partition R s ==> s = e UNION (BIGUNION p)``,
rw[] >>
`BIGUNION (e INSERT p) = s` by metis_tac[BIGUNION_partition] >>
fs[BIGUNION]);

val equiv_on_partition_NOT_R = store_thm(
"equiv_on_partition_NOT_R",
``R equiv_on s ==> !t1 t2. t1 IN partition R s /\ t2 IN partition R s /\ t1 <> t2 ==> !x. x IN t1 ==> !y. y IN t2 ==> ¬R x y``,
rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
metis_tac[equiv_on_same_partition]);

val equiv_on_INSERT_partition = store_thm(
"equiv_on_INSERT_partition",
``R equiv_on s ==> !e p. e NOTIN p /\ e INSERT p = partition R s ==> !x. x IN e ==> !y. y IN (BIGUNION p) ==> ¬R x y``,
rw[] >>
`!a. a IN p ==>  e <> a` by fs[] >>
`e <> s'` by metis_tac[] >>
`e IN partition R s` by fs[INSERT_SUBSET,SET_EQ_SUBSET] >>
`s' IN partition R s` by fs[INSERT_SUBSET,SET_EQ_SUBSET,SUBSET_DEF] >>
metis_tac[equiv_on_partition_NOT_R]);

val equiv_on_INSERT_partition_UNION = store_thm(
"equiv_on_INSERT_partition_UNION",
``R equiv_on s ==>  !e p. e INSERT p = partition R s ==> s = e UNION (BIGUNION p)``,
rw[] >>
`BIGUNION (e INSERT p) = s` by metis_tac[BIGUNION_partition] >>
fs[BIGUNION]);


val equiv_on_INSERT_partition = store_thm(
"equiv_on_INSERT_partition",
``R equiv_on s ==> !e p. e NOTIN p /\ e INSERT p = partition R s ==> !x. x IN e ==> !y. y IN (BIGUNION p) ==> ¬R x y``,
rw[] >>
`!a. a IN p ==>  e <> a` by fs[] >>
`e <> s'` by metis_tac[] >>
`e IN partition R s` by fs[INSERT_SUBSET,SET_EQ_SUBSET] >>
`s' IN partition R s` by fs[INSERT_SUBSET,SET_EQ_SUBSET,SUBSET_DEF] >>
metis_tac[equiv_on_partition_NOT_R]);


val FINITE_partition_SUBSET = store_thm(
  "FINITE_partition_SUBSET",
  ``!R s. R equiv_on s ==> FINITE (partition R s) ==> !a. a ⊆ s ==> FINITE (partition R a)``,
  rw[partition_def] >>
  `?f. INJ f {t | ∃x. x ∈ a ∧ t = {y | y ∈ a ∧ R x y}} {t | ∃x. x ∈ s ∧ t = {y | y ∈ s ∧ R x y}}` suffices_by metis_tac[FINITE_INJ] >>
  qexists_tac `\p. {y | y IN s /\ ?r. r IN p /\ R r y}` >> rw[INJ_DEF]
  >- (qexists_tac `x` >> rw[]
     >- fs[SUBSET_DEF]
     >- (rw[Once EXTENSION] >> eq_tac >> rw[]
        >- (`x IN s` by metis_tac[SUBSET_DEF] >>
           `r IN s` by metis_tac[SUBSET_DEF] >>
           `∀x y z. x ∈ s ∧ y ∈ s ∧ z ∈ s ∧ R x y ∧ R y z ⇒ R x z` by fs[equiv_on_def] >> metis_tac[])
        >- (qexists_tac `x` >> rw[] >>
           `x IN s` by metis_tac[SUBSET_DEF] >>
           fs[equiv_on_def])))
  >- (rw[Once EXTENSION] >> eq_tac >> rw[]
     >- (`{y | y ∈ s ∧ ∃r. r ∈ {y | y ∈ a ∧ R x y} ∧ R r y} =
         {y | y ∈ s ∧ ∃r. r ∈ {y | y ∈ a ∧ R x' y} ∧ R r y} ==> R x' x''` suffices_by metis_tac[] >>
        simp[Once EXTENSION,EQ_IMP_THM] >> rw[] >>
        `x'' IN s` by fs[SUBSET_DEF] >>
        `R x'' x''` by fs[equiv_on_def] >>
        `∃r. (r ∈ a ∧ R x' r) ∧ R r x''` by metis_tac[] >>
        fs[equiv_on_def] >>
        `r IN s` by fs[SUBSET_DEF] >>
        `x' IN s` by fs[SUBSET_DEF] >>
        metis_tac[])
     >- (`{y | y ∈ s ∧ ∃r. r ∈ {y | y ∈ a ∧ R x y} ∧ R r y} =
         {y | y ∈ s ∧ ∃r. r ∈ {y | y ∈ a ∧ R x' y} ∧ R r y} ==> R x x''` suffices_by metis_tac[] >>
        simp[Once EXTENSION,EQ_IMP_THM] >> rw[] >>
        `x'' IN s` by fs[SUBSET_DEF] >>
        `R x'' x''` by fs[equiv_on_def] >>
        `∃r. (r ∈ a ∧ R x r) ∧ R r x''` by metis_tac[] >>
        fs[equiv_on_def] >>
        `r IN s` by fs[SUBSET_DEF] >>
        `x' IN s` by fs[SUBSET_DEF] >>
        `x IN s` by fs[SUBSET_DEF] >> metis_tac[])));

val CHOICE_BIJ_partition = store_thm(
    "CHOICE_BIJ_partition",
    ``!R s. R equiv_on s ==>
    BIJ CHOICE (partition R s) (IMAGE CHOICE (partition R s))``,
    rw[BIJ_DEF,INJ_DEF,SURJ_DEF] >>
    `x <> {} /\ y <> {}` by metis_tac[EMPTY_NOT_IN_partition] >>
    `CHOICE x IN x /\ CHOICE y IN y` by metis_tac[CHOICE_DEF] >>
    `CHOICE x IN y` by fs[] >>
    irule equiv_partition_unique >> map_every qexists_tac [`R`,`s`,`CHOICE x`] >> rw[] >>
    fs[partition_def] >>
    `{y | y ∈ s ∧ R x'' y} <> {}` by (`x'' IN  {y | y ∈ s ∧ R x'' y}` by fs[equiv_on_def] >> metis_tac[MEMBER_NOT_EMPTY]) >>
    `CHOICE {y | y ∈ s ∧ R x'' y} IN {y | y ∈ s ∧ R x'' y}` by metis_tac[CHOICE_DEF] >> fs[]);


val _ = export_theory();
