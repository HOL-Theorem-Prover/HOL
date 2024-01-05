open HolKernel Parse boolLib bossLib;
open chap1Theory;
open numpairTheory;
open pred_setTheory;
open relationTheory;
open listTheory;
open arithmeticTheory;
open set_relationTheory;
open pairTheory;
open quantHeuristicsTheory;
open rich_listTheory;

val _ = new_theory "chap2_1";

val irule = fn th => irule th >> rpt conj_tac


val DU_def = Define`
  DU (f, dom) = <| frame := <| world := {w | (FST w) IN dom /\ (SND w) IN (f (FST w)).frame.world};
                                 rel := \w1 w2. FST w1 = FST w2 /\
                                                (FST w1) IN dom /\
                                                (f (FST w1)).frame.rel (SND w1) (SND w2) |>;
                                valt := \v w. (f (FST w)).valt v (SND w) |>`;

val prop_2_3 = store_thm(
  "prop_2_3",
  ``!w f. (FST w) IN dom ==> (satis (f (FST w)) (SND w) phi <=> satis (DU (f, dom)) w phi)``,
  Induct_on `phi` >> rw[satis_def,EQ_IMP_THM] (* 10 *)
  >- (fs[DU_def] >> map_every qexists_tac [`FST w`,`SND w`] >> rw[])
  >- fs[DU_def,IN_DEF]
  >- fs[DU_def]
  >- fs[DU_def,IN_DEF]
  >- (fs[DU_def] >> map_every qexists_tac [`FST w`,`SND w`] >> rw[])
  >- fs[DU_def]
  >- (fs[DU_def] >> map_every qexists_tac [`FST w`,`SND w`] >> rw[])
  >- (qexists_tac `(FST w,v)` >> rw[]
     >- fs[DU_def]
     >- fs[DU_def]
     >- (`FST (FST w,v) = FST w` by fs[] >>
        `SND (FST w,v) = v` by fs[] >>
        metis_tac[]))
  >- fs[DU_def]
  >- (qexists_tac `SND v` >> rw[]
     >- fs[DU_def]
     >- fs[DU_def]
     >- (`FST v = FST w` by fs[DU_def] >> metis_tac[])));


val M_union_def = Define`
M_union M1 M2 = DU ((λn. if n = 0 then M1 else M2), {x | x = 0 \/ x = 1})`;




val SUBMODEL_def = Define`
SUBMODEL M1 M2 <=> (M1.frame.world) ⊆ (M2.frame.world) /\
                         (!w1. w1 IN M1.frame.world ==>
                         (!v. M1.valt v w1 <=> M2.valt v w1) /\
                         (!w2. w2 IN M1.frame.world ==> (M1.frame.rel w1 w2 <=> M2.frame.rel w1 w2)))`;



val GENSUBMODEL_def = Define`
GENSUBMODEL M1 M2 <=> SUBMODEL M1 M2 /\
                     (!w1. w1 IN M1.frame.world ==>
                     (!w2. w2 IN M2.frame.world /\ M2.frame.rel w1 w2 ==> w2 IN M1.frame.world))`;



val prop_2_6 = store_thm(
"prop_2_6",
``!w phi M1 M2. GENSUBMODEL M1 M2 /\ w IN M1.frame.world ==> (satis M1 w phi <=> satis M2 w phi)``,
Induct_on `phi` >> rw[satis_def]
>- (eq_tac
   >- (rpt strip_tac
      >- fs[SUBSET_DEF,SUBMODEL_def,GENSUBMODEL_def]
      >- (fs[SUBSET_DEF,SUBMODEL_def,GENSUBMODEL_def]
          >> `∀v. M1.valt v w ⇔ M2.valt v w` by metis_tac[]
          >> metis_tac[IN_DEF]))
   >- (rpt strip_tac
      >> fs[SUBMODEL_def,GENSUBMODEL_def,SUBSET_DEF]
      >> `∀v. M1.valt v w ⇔ M2.valt v w` by metis_tac[]
      >> metis_tac[IN_DEF]))
>- (eq_tac
   >- (rpt strip_tac
      >- (`satis M1 w phi ⇔ satis M2 w phi` by metis_tac[]
         >> metis_tac[])
      >- (`satis M1 w phi' ⇔ satis M2 w phi'` by metis_tac[]
         >> metis_tac[]))
   >- (rpt strip_tac
      >- (`satis M1 w phi ⇔ satis M2 w phi` by metis_tac[]
         >> metis_tac[])
      >- (`satis M1 w phi' ⇔ satis M2 w phi'` by metis_tac[]
         >> metis_tac[])))
>- (eq_tac
   >- (rpt strip_tac
      >> metis_tac[SUBSET_DEF,SUBMODEL_def,GENSUBMODEL_def])
   >- (rpt strip_tac
      >> metis_tac[SUBSET_DEF,SUBMODEL_def,GENSUBMODEL_def]))
>- (eq_tac
   >- (rpt strip_tac
      >- metis_tac[SUBSET_DEF,SUBMODEL_def,GENSUBMODEL_def]
      >- (qexists_tac `v`
         >> rpt strip_tac
         >- metis_tac[SUBMODEL_def,GENSUBMODEL_def,IN_DEF]
         >- metis_tac[SUBMODEL_def,GENSUBMODEL_def,SUBSET_DEF]
         >- metis_tac[]))
   >- (rpt strip_tac
      >> qexists_tac `v`
      >> metis_tac[SUBMODEL_def,GENSUBMODEL_def,IN_DEF]))
);



val hom_def = Define`
hom f M1 M2 <=> (!w. w IN M1.frame.world ==> ((f w) IN M2.frame.world /\ (!p. w IN M1.valt p ==> (f w) IN M2.valt p) /\
                                            (!u. u IN M1.frame.world ==> (M1.frame.rel w u ==> M2.frame.rel (f w) (f u)))))`;



val strong_hom_def = Define`
strong_hom f M1 M2 <=> (!w. w IN M1.frame.world ==> ((f w) IN M2.frame.world /\ (!p. w IN M1.valt p <=> (f w) IN M2.valt p) /\
                                            (!u. u IN M1.frame.world ==> (M1.frame.rel w u <=> M2.frame.rel (f w) (f u)))))`;



val embedding_def = Define`
embedding f M1 M2 <=> (strong_hom f M1 M2 /\ INJ f M1.frame.world M2.frame.world)`;



val iso_def = Define`
iso f M1 M2 <=> (strong_hom f M1 M2 /\ BIJ f M1.frame.world M2.frame.world)`;



val tau_theory_def = Define`
tau_theory M w  = {form | satis M w form}`;



val modal_eq_def = Define`
 modal_eq M M' w w'<=> (tau_theory M w = tau_theory M' w')`;

val modal_eq_tau = store_thm(
"modal_eq_tau",
``!M M' w w'. modal_eq M M' w w' <=> (!form. satis M w form <=> satis M' w' form)``,
rw[EQ_IMP_THM] >> fs[modal_eq_def,tau_theory_def,EXTENSION]
>- metis_tac[]
>- rw[EQ_IMP_THM])

val tau_theory_model_def = Define`
tau_theory_model M = {form | !w. w IN M.frame.world ==> satis M w form}`;



val modal_eq_model_def = Define`
modal_eq_model M M' <=> (tau_theory_model M = tau_theory_model M')`;



val lemma_2_9 = store_thm(
"lemma_2_9",
``!M M' w w' f form. strong_hom f M M' /\ (f w) = w' /\ w IN M.frame.world /\ SURJ f M.frame.world M'.frame.world ==> (satis M w form <=> satis M' w' form) ``,
Induct_on `form` >> rw[satis_def]
>- metis_tac[strong_hom_def]
>- metis_tac[strong_hom_def]
>- metis_tac[strong_hom_def]
>- (eq_tac
   >- (rpt strip_tac
      >- metis_tac[strong_hom_def]
      >- (qexists_tac `f v`
         >> metis_tac[strong_hom_def,IN_DEF]))
   >- (rpt strip_tac
      >> `?x. x IN M.frame.world /\ f x = v` by metis_tac[SURJ_DEF]
      >> qexists_tac `x`
      >> metis_tac[strong_hom_def,IN_DEF])
     ));



val prop_2_9 = store_thm(
"prop_2_9",
``!M M' w w' f form. strong_hom f M M' /\ (f w) = w' /\ w IN M.frame.world /\ SURJ f M.frame.world M'.frame.world ==> modal_eq M M' w w' ``,
rw[modal_eq_def,tau_theory_def]
>> `!form. satis M w form <=> satis M' (f w) form` suffices_by metis_tac[SET_EQ_SUBSET,SUBSET_DEF]
>> metis_tac[lemma_2_9]);



val prop_2_9_ii = store_thm(
"prop_2_9_ii",
``!M M' f. iso f M M' ==> modal_eq_model M M'``,
fs[modal_eq_model_def,iso_def,tau_theory_model_def]
>> rpt strip_tac
>> `!form. (∀w. w ∈ M.frame.world ⇒ satis M w form) <=>  (∀w. w ∈ M'.frame.world ⇒ satis M' w form)` suffices_by fs[SET_EQ_SUBSET,SUBSET_DEF]
>> fs[BIJ_DEF]
>> rpt strip_tac
>> eq_tac
   >- (rpt strip_tac
   >> `?v. v IN M.frame.world /\ f v = w` by metis_tac[SURJ_DEF]
   >> `satis M v form` by metis_tac[]
   >> `satis M' (f v) form` by metis_tac[lemma_2_9]
   >> rw[])
   >- (rpt strip_tac
   >> `(f w) IN M'.frame.world` by metis_tac[strong_hom_def]
   >> `satis M' (f w) form` by metis_tac[]
   >> metis_tac[lemma_2_9])
);



val bounded_mor_def = Define`
 bounded_mor f M M' <=> (!w. w IN M.frame.world ==>
((f w) IN M'.frame.world) /\
(!a. (satis M w (VAR a) <=> satis M' (f w) (VAR a))) /\
(!v. v IN M.frame.world /\ M.frame.rel w v ==> M'.frame.rel (f w) (f v)) /\
(!v'. v' IN M'.frame.world /\ M'.frame.rel (f w) v' ==> ?v. v IN M.frame.world /\ M.frame.rel w v /\ f v = v'))`;



val bounded_mor_image_def = Define`
bounded_mor_image f M M' = (bounded_mor f M M' /\ (SURJ f M.frame.world M'.frame.world))`;

Theorem prop_2_14:
  !M M' w f form.
    bounded_mor f M M' /\ w IN M.frame.world ==> (
    satis M w form <=> satis M' (f w) form)
Proof
Induct_on `form` >> rw[satis_def]
>- (eq_tac
   >- (rpt strip_tac
     >- metis_tac[bounded_mor_def]
     >- (`(!a. (satis M w (VAR a) <=> satis M' (f w) (VAR a)))` by metis_tac[bounded_mor_def]
   >> fs[satis_def]
   >> metis_tac[]))
   >- (rpt strip_tac
   >> fs[bounded_mor_def,satis_def,IN_DEF]))
>- (eq_tac
  >- (rpt strip_tac
    >- (`satis M w form ⇔ satis M' (f w) form` by metis_tac[]
       >> fs[])
    >- (`satis M w form' ⇔ satis M' (f w) form'` by metis_tac[]
       >> fs[]))
  >- (rpt strip_tac
    >- (`satis M w form ⇔ satis M' (f w) form` by metis_tac[]
       >> fs[])
    >- (`satis M w form' ⇔ satis M' (f w) form'` by metis_tac[]
       >> fs[])))
>- fs[bounded_mor_def,IN_DEF,satis_def]
>- (eq_tac
  >- (rpt strip_tac
     >- metis_tac[bounded_mor_def]
     >- (qexists_tac `f v`
       >> (rpt strip_tac
       >- metis_tac[bounded_mor_def,IN_DEF]
       >- metis_tac[bounded_mor_def]
       >- metis_tac[])))
  >- (rpt strip_tac
  >> `?x. x IN M.frame.world /\ M.frame.rel w x /\ f x = v` by metis_tac[bounded_mor_def,IN_DEF]
  >> qexists_tac `x`
  >> rpt strip_tac
    >- metis_tac[IN_DEF]
    >- metis_tac[]
    >- metis_tac[]))
QED



(* tree-like lemma *)

(* no-loop lemma *)
val RESTRICT_def = Define`
RESTRICT R s x y <=> R x y /\ x IN s /\ y IN s`;



val tree_def = Define`
tree S r <=>
  r IN S.world /\ (!t. t IN S.world ==> RTC (RESTRICT S.rel S.world) r t) /\
  (!r0. r0 IN S.world ==> ¬S.rel r0 r) /\
  (∀t. t ∈ S.world ∧ t ≠ r ==> ∃!t0. t0 ∈ S.world ∧ S.rel t0 t)`;



val RTC_PREDECESSOR_LEMMA = store_thm(
"RTC_PREDECESSOR_LEMMA",
``!R x y. RTC R x y ==> x <> y ==> ?p. R p y /\ p <> y``,
gen_tac >>
ho_match_mp_tac relationTheory.RTC_STRONG_INDUCT >>
rw[] >> metis_tac[]);



val TC_PREDECESSOR_LEMMA = store_thm(
"TC_PREDECESSOR_LEMMA",
``!R x y. TC R x y ==> x <> y ==> ?p. R p y /\ p <> y``,
gen_tac >>
ho_match_mp_tac relationTheory.TC_STRONG_INDUCT_LEFT1 >>
rw[] >> metis_tac[]);



val _ = clear_overloads_on "R";
val tree_no_loop = store_thm(
"tree_no_loop",
``!s r. tree s r ==> !t0 t. (TC (RESTRICT s.rel s.world) t0 t) ==> t0 <> t``,
rpt gen_tac >> strip_tac >>
qabbrev_tac `R = RESTRICT s.rel s.world` >>
rpt strip_tac >>
`R^* r t` by
(`?t'. R t0 t' /\ R^+ t' t` by metis_tac[TC_CASES1] >> fs[Abbr`R`,RESTRICT_def] >> metis_tac[tree_def]) >>
`!t1 t2. R^* t1 t2 ==> (t1 = r) ==> ¬R^+ t2 t2` suffices_by metis_tac[] >>
ho_match_mp_tac relationTheory.RTC_STRONG_INDUCT_RIGHT1 >>
rpt strip_tac >-
(rw[] >> metis_tac[TC_CASES2,tree_def,RESTRICT_def]
)
>-
(rw[] >>
rename[`R^* r t0`,`¬R^+ t0 t0`,`R t0 t`] >>
`?t1. R t1 t /\ R^* t t1` by metis_tac[TC_CASES2,TC_RTC,RTC_REFL] >>
Cases_on `t0 = t1` >-
(metis_tac[EXTEND_RTC_TC_EQN])
>- (`t <> r` by metis_tac[tree_def,RESTRICT_def]
>> `t0 IN s.world /\ t1 IN s.world` by metis_tac[RESTRICT_def]
>> `s.rel t0 t /\ s.rel t1 t` by metis_tac[RESTRICT_def]
>> metis_tac[tree_def,RESTRICT_def]
)
)
);




(* tree-like model lemma *)



val rooted_model_def = Define`
rooted_model M x M' <=> x IN M'.frame.world /\
                                 (!a. a IN M.frame.world <=> (a IN M'.frame.world /\ (RTC (RESTRICT M'.frame.rel M'.frame.world)) x a)) /\
                                 (!n1 n2. n1 IN M.frame.world /\ n2 IN M.frame.world ==>
                                   (M.frame.rel n1 n2 <=> (RESTRICT M'.frame.rel M'.frame.world) n1 n2)) /\
                                 (!v n. M.valt v n <=> M'.valt v n)`;



val tree_like_model_def = Define`
tree_like_model M <=> ?x. tree M.frame x`;




val bounded_preimage_rooted_def = Define`
  bounded_preimage_rooted M x =
  <| frame := <| world := {l | HD l = x /\
                               LENGTH l > 0 /\
                               (!m. m < LENGTH l - 1 ==>
                                    RESTRICT M.frame.rel M.frame.world (EL m l) (EL (m + 1) l))};
                 rel := \l1 l2. (LENGTH l1) + 1 = LENGTH l2 /\
                                (RESTRICT M.frame.rel M.frame.world) (LAST l1) (LAST l2) /\
                                (!m. m < LENGTH l1 ==> EL m l1 = EL m l2) |>;
     valt := \v n. M.valt v (LAST n) |>`;




val prop_2_15_subgoal_1 = store_thm(
  "prop_2_15_subgoal_1",
  ``rooted_model M x M' ==> bounded_mor LAST (bounded_preimage_rooted M x) M``,
  rw[bounded_mor_def] (* 4 *)
     >- (fs[bounded_preimage_rooted_def,RESTRICT_def] >>
        `LENGTH w <> 0`
            by (SPOSE_NOT_THEN ASSUME_TAC >>
               `w = []` by fs[LENGTH_NIL_SYM] >> fs[HD]) >>
        `LAST w = EL (PRE (LENGTH w)) w` by fs[LAST_EL] >>
        Cases_on `LENGTH w < 2` (* 2 *)
        >- (`LENGTH w = 1` by fs[] >> fs[rooted_model_def])
        >- (`LENGTH w - 2 < LENGTH w - 1` by fs[] >>
           `EL ((LENGTH w - 2) + 1) w IN M.frame.world` by fs[] >>
           `(LENGTH w - 2) + 1 = PRE (LENGTH w)` by fs[] >> fs[]))
     >- (fs[satis_def,bounded_preimage_rooted_def] >>
        `LAST w IN M.frame.world` suffices_by metis_tac[IN_DEF] >>
        `LENGTH w <> 0`
            by (SPOSE_NOT_THEN ASSUME_TAC >>
               `w = []` by fs[LENGTH_NIL_SYM] >> fs[HD]) >>
        `LAST w = EL (PRE (LENGTH w)) w` by fs[LAST_EL] >>
        Cases_on `LENGTH w < 2` (* 2 *)
        >- (`LENGTH w = 1` by fs[] >> fs[rooted_model_def])
        >- (`LENGTH w - 2 < LENGTH w - 1` by fs[] >>
           fs[RESTRICT_def] >>
           `EL ((LENGTH w - 2) + 1) w IN M.frame.world` by fs[] >>
           `(LENGTH w - 2) + 1 = PRE (LENGTH w)` by fs[] >> fs[]))
     >- fs[bounded_preimage_rooted_def,RESTRICT_def]
     >- (qexists_tac `w ++ [v']` >> rw[] (* 2 *)
        >- (fs[bounded_preimage_rooted_def] >> rw[] (* 2 *)
           >- (Cases_on `w`
              >- fs[LENGTH]
              >- fs[HD])
           >- (fs[RESTRICT_def] >> rw[] (* 3 *)
              >- (`w ++ [v'] = SNOC v' w` by fs[] >>
                 `EL m (w ++ [v']) = EL m w` by rw[EL_SNOC] >>
                 fs[] >>
                 Cases_on `m < LENGTH w - 1` (* 2 *)
                 >- (`m + 1 < LENGTH w` by fs[] >>
                    `w ++ [v'] = SNOC v' w` by fs[] >>
                    `EL (m + 1) (w ++ [v']) = EL (m + 1) w` by rw[EL_SNOC] >>
                    fs[])
                 >- (`m = LENGTH w - 1` by fs[] >>
                    `LENGTH w <> 0` by (SPOSE_NOT_THEN ASSUME_TAC >> fs[]) >>
                    `w <> []` by fs[] >>
                    `LAST w = EL (PRE (LENGTH w)) w` by fs[LAST_EL] >>
                    `PRE (LENGTH w) = LENGTH w - 1` by fs[] >>
                    `LAST (w ++ [v']) = v'` by fs[] >>
                    `w ++ [v'] <> []` by fs[] >>
                    `LAST (w ++ [v']) = EL (PRE (LENGTH (w ++ [v']))) (w ++ [v'])` by metis_tac[LAST_EL] >>
                    `LENGTH (w ++ [v']) = LENGTH w + 1` by fs[] >>
                    `LENGTH w = m + 1` by fs[] >>
                    `LENGTH w + 1 = m + 2` by fs[] >>
                    `PRE (LENGTH (w ++ [v'])) = m + 1` by fs[] >>
                    `PRE (LENGTH w) = m` by fs[] >>
                    `EL m w = LAST w` by fs[] >>
                    `EL (m + 1) (w ++ [v']) = v'` by fs[] >> fs[]))
              >- (Cases_on `m < LENGTH w - 1` (* 2 *)
                 >- (`SNOC v' w = w ++ [v']` by fs[] >>
                    `EL m (w ++ [v']) = EL m w` by metis_tac[EL_SNOC] >> fs[])
                 >- (`SNOC v' w = w ++ [v']` by fs[] >>
                    `EL m (w ++ [v']) = EL m w` by metis_tac[EL_SNOC] >> fs[] >>
                    Cases_on `LENGTH w = 1`
                    >- (`m = 0` by fs[] >>
                       `EL m w = HD w` by fs[] >>
                       fs[rooted_model_def])
                    >- (`m  = LENGTH w - 1` by fs[] >>
                       `LENGTH w > 1` by fs[] >>
                       `LENGTH w - 2 < LENGTH w - 1` by fs[] >>
                       `EL ((LENGTH w - 2) + 1) w IN M.frame.world` by fs[] >>
                       `LENGTH w - 2 + 1 = LENGTH w - 1` by fs[] >> fs[])))
              >- (Cases_on `m < LENGTH w - 2` (* 2 *)
                 >- (`m + 1 < LENGTH (w ++ [v'])` by fs[] >>
                    `w ++ [v'] = SNOC v' w` by fs[] >>
                    `EL (m + 1) (w ++ [v']) = EL (m + 1) w` by rw[EL_SNOC] >>
                    `m < LENGTH w - 1` by fs[] >> fs[])
                 >- (Cases_on `m < LENGTH w - 1` (* 2 *)
                    >- (`m + 1 < LENGTH w` by fs[] >>
                       `w ++ [v'] = SNOC v' w` by fs[] >>
                       `EL (m + 1) (w ⧺ [v']) = EL (m + 1) w` by rw[EL_SNOC] >>
                       fs[])
                    >- (`m = LENGTH w - 1` by fs[] >>
                       `m + 1 = LENGTH w` by fs[] >>
                       `LENGTH w = PRE (LENGTH (w ++ [v']))` by fs[] >>
                       `w ++ [v'] <> []` by fs[] >>
                       `LAST (w ++ [v']) = EL (PRE (LENGTH (w ++ [v']))) (w ++ [v'])` by metis_tac[LAST_EL] >>
                       `LAST (w ++ [v']) = v'` by fs[] >>
                       metis_tac[])))))
        >- (fs[bounded_preimage_rooted_def] >> rw[] (* 2 *)
           >- (`(LAST w) IN M.frame.world` suffices_by metis_tac[RESTRICT_def] >>
              Cases_on `LENGTH w = 1` (* 2 *)
              >- (`?x. w = [x]` by fs[LIST_LENGTH_1] >>
                 `HD w = x` by fs[] >>
                 `LAST w = x` by fs[] >>
                 fs[rooted_model_def])
              >- (fs[RESTRICT_def] >>
                 `LENGTH w > 1` by fs[] >>
                 `LENGTH w - 2 < LENGTH w - 1` by fs[] >>
                 `(EL ((LENGTH w - 2) + 1) w) IN M.frame.world` by metis_tac[] >>
                 `LENGTH w - 2 + 1 = PRE (LENGTH w)` by fs[] >>
                 `w <> []`
                     by (SPOSE_NOT_THEN ASSUME_TAC >> fs[LENGTH]) >>
                 rw[LAST_EL] >> metis_tac[]))
            >- (`w ++ [v'] = SNOC v' w` by fs[] >> metis_tac[EL_SNOC]))));


val LAST_in_world = store_thm(
  "LAST_in_world",
  ``rooted_model M x M' /\ w ∈ (bounded_preimage_rooted M x).frame.world ==> LAST w ∈ M.frame.world``,
   rw[bounded_preimage_rooted_def] >>
   Cases_on `LENGTH w = 1` (* 2 *)
   >- (`?x. w = [x]` by fs[LIST_LENGTH_1] >>
      `HD w = x` by fs[] >>
      `LAST w = x` by fs[] >>
      fs[rooted_model_def])
   >- (fs[RESTRICT_def] >>
      `LENGTH w > 1` by fs[] >>
      `LENGTH w - 2 < LENGTH w - 1` by fs[] >>
      `(EL ((LENGTH w - 2) + 1) w) IN M.frame.world` by metis_tac[] >>
      `LENGTH w - 2 + 1 = PRE (LENGTH w)` by fs[] >>
      `w <> []`
         by (SPOSE_NOT_THEN ASSUME_TAC >> fs[LENGTH]) >>
      rw[LAST_EL] >> metis_tac[]));



val prop_2_15_subgoal_2 = store_thm(
  "prop_2_15_subgoal_2",
  ``rooted_model M x M' ==> SURJ LAST (bounded_preimage_rooted M x).frame.world M.frame.world``,
  rw[SURJ_DEF]
     >- metis_tac[LAST_in_world]
     >- (fs[rooted_model_def] >>
        `x' ∈ M'.frame.world ∧
         (RESTRICT M'.frame.rel M'.frame.world)^* x x'` by metis_tac[] >>
        `!x' a. (RESTRICT M'.frame.rel M'.frame.world)^* x' a ==> a IN M'.frame.world /\ x' = x ==>
        ∃y. y ∈ (bounded_preimage_rooted M x).frame.world ∧ LAST y = a` suffices_by metis_tac[] >>
        ho_match_mp_tac RTC_INDUCT_RIGHT1 >> rw[] (* 2 *)
        >- (qexists_tac `[x]` >> rw[] >>
           rw[bounded_preimage_rooted_def])
        >- (`rooted_model M x M'` by rw[rooted_model_def] >>
           `a IN M'.frame.world` by fs[RESTRICT_def] >>
           `∃y. y ∈ (bounded_preimage_rooted M x).frame.world ∧ LAST y = a` by metis_tac[] >>
           qexists_tac `y ++ [a']` >> rw[] >>
           rw[bounded_preimage_rooted_def] (* 2 *)
           >- (`HD y = x` by fs[bounded_preimage_rooted_def] >>
              `y <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> fs[bounded_preimage_rooted_def]) >>
              `HD y = HD (y ++ [a'])` by (Cases_on `y` >- fs[] >- (fs[HD] >> fs[])) >> fs[])
           >- (`HD y = x ∧ LENGTH y > 0 ∧
               ∀m.
                 m < LENGTH y − 1 ⇒
                 RESTRICT M.frame.rel M.frame.world (EL m y)
                   (EL (m + 1) y)` by fs[bounded_preimage_rooted_def] >>
              Cases_on `m < LENGTH y - 1`
              >- (`y ++ [a'] = SNOC a' y` by fs[] >>
                 `EL m (y ++ [a']) = EL m y` by rw[EL_SNOC] >>
                 `m + 1 < LENGTH y` by fs[] >>
                 `EL (m + 1) (y ++ [a']) = EL (m + 1) y` by rw[EL_SNOC] >>
                 metis_tac[])
              >- (`m = LENGTH y - 1` by fs[] >>
                 `y ++ [a'] = SNOC a' y` by fs[] >>
                 `EL m (y ++ [a']) = EL m y` by rw[EL_SNOC] >>
                 `y <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> fs[bounded_preimage_rooted_def]) >>
                 `LAST y = EL (PRE (LENGTH y)) y` by rw[LAST_EL] >>
                 `PRE (LENGTH y) = m` by fs[] >>
                 `LENGTH (y ++ [a']) = m + 2` by fs[] >>
                 `PRE (LENGTH (y ++ [a'])) = m + 1` by fs[] >>
                 `y ++ [a'] <> []` by fs[] >>
                 `LAST (y ++ [a']) = EL (PRE (LENGTH (y ++ [a']))) (y ++ [a'])` by metis_tac[LAST_EL] >>
                 `LAST (y ++ [a']) = a'` by (Cases_on `y` >> fs[]) >>
                 `EL m (y ++ [a']) = LAST y` by rw[] >>
                 `EL (m + 1) (y ++ [a']) = a'` by metis_tac[] >>
                 `RESTRICT M.frame.rel M.frame.world (LAST y) a'` suffices_by metis_tac[] >>
                 rw[RESTRICT_def] (* 3 *)
                 >- (`(LAST y) IN M.frame.world /\ a' IN M.frame.world` suffices_by metis_tac[] >>
                    `(LAST y) IN M.frame.world`
                        suffices_by (rw[] >>
                        `(EL (LENGTH y − 1) y) = LAST y` by rw[] >>
                        metis_tac[RTC_CASES2]) >>
                    metis_tac[LAST_in_world])
                 >- (`(LAST y) IN M.frame.world` by metis_tac[LAST_in_world] >>
                    `(RESTRICT M'.frame.rel M'.frame.world)^* (HD y) (LAST y)` suffices_by rw[] >>
                    metis_tac[])
                 >- (`(RESTRICT M'.frame.rel M'.frame.world)^* (HD y) (LAST y)`
                        by (`(LAST y) IN M.frame.world` by metis_tac[LAST_in_world] >> metis_tac[]) >>
                    metis_tac[RTC_CASES2]))))));

val FRONT_in_world = store_thm(
  "FRONT_in_world",
  ``rooted_model M x M' /\ t IN (bounded_preimage_rooted M x).frame.world /\ LENGTH t > 1 ==>
    (FRONT t) IN (bounded_preimage_rooted M x).frame.world``,
  rw[bounded_preimage_rooted_def] (* 3 *)
  >- (Cases_on `t` >- fs[] >- (Cases_on `t'` >> fs[]))
  >- (`LENGTH t - 1 > 0` by fs[] >>
     `t <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> fs[]) >>
     `LENGTH t - 1 = PRE (LENGTH t)` by fs[] >>
     `LENGTH (FRONT t) = LENGTH t - 1` by fs[LENGTH_FRONT] >>
     fs[])
  >- (`t <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> fs[]) >>
     `LENGTH (FRONT t) = LENGTH t - 1` by fs[LENGTH_FRONT] >>
     `m < LENGTH t - 1` by fs[] >>
     Cases_on `t` >- fs[]
                  >- (`¬(NULL (h :: t'))` by fs[NULL] >>
                     qabbrev_tac `t = h :: t'` >>
                     `EL m (FRONT t) = EL m t` by fs[EL_FRONT] >>
                     `m + 1 < LENGTH (FRONT t)` by fs[] >>
                     `EL (m + 1) (FRONT t) = EL (m + 1) t` by fs[EL_FRONT] >>
                     metis_tac[])));


val prop_2_15_subgoal_4 = store_thm(
  "prop_2_15_subgoal_4",
  ``rooted_model M x M' /\ t ∈ (bounded_preimage_rooted M x).frame.world ==>
        (RESTRICT (bounded_preimage_rooted M x).frame.rel (bounded_preimage_rooted M x).frame.world)^* [x] t``,
  rw[] >>
  completeInduct_on `LENGTH t` >> rw[] >>
  `t = [] \/ ?x l. t = SNOC x l` by metis_tac[SNOC_CASES] (* 2 *)
  >- fs[bounded_preimage_rooted_def]
  >- (`LENGTH t - 1 < LENGTH t` by fs[] >>
     `LENGTH t - 1 = LENGTH (FRONT t)` by fs[LENGTH_FRONT] >>
     Cases_on `LENGTH t > 1` (* 2 *)
     >- (`(FRONT t) IN (bounded_preimage_rooted M x).frame.world` by metis_tac[FRONT_in_world] >>
        `(RESTRICT (bounded_preimage_rooted M x).frame.rel
               (bounded_preimage_rooted M x).frame.world)^* [x] (FRONT t)` by metis_tac[] >>
        `(RESTRICT (bounded_preimage_rooted M x).frame.rel
               (bounded_preimage_rooted M x).frame.world) (FRONT t) t` suffices_by metis_tac[RTC_CASES2] >>
        `(bounded_preimage_rooted M x).frame.rel (FRONT t) t` suffices_by metis_tac[RESTRICT_def] >>
        rw[bounded_preimage_rooted_def] (* 2 *)
        >- (fs[bounded_preimage_rooted_def] >>
           `LENGTH l - 1 < LENGTH l` by fs[] >>
           `EL (LENGTH l - 1) (SNOC x' l) = LAST l /\
           EL ((LENGTH l - 1) + 1) (SNOC x' l) = x'` suffices_by metis_tac[] >> rw[] (* 2 *)
           >- (`SNOC x' l = l ++ [x']` by fs[] >>
              `EL (LENGTH l − 1) (SNOC x' l) = EL (LENGTH l − 1) l` by rw[EL_APPEND1] >>
              `l <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> fs[]) >>
              `PRE (LENGTH l) = LENGTH l - 1` by fs[] >>
              `EL (LENGTH l - 1) l = LAST l` by rw[LAST_EL] >> fs[])
           >-  (`SNOC x' l = l ++ [x']` by fs[] >>
               `PRE (LENGTH (l ++ [x'])) = LENGTH l` by fs[] >>
               `l ++ [x'] <> []` by fs[] >>
               `EL (LENGTH l) (l ++ [x']) = LAST (l ++ [x'])` by metis_tac[LAST_EL] >>
               `LAST (l ++ [x']) = x'` by fs[] >> metis_tac[]))
        >- (`SNOC x' l = l ++ [x']` by fs[] >> metis_tac[EL_APPEND1]))
     >- (`LENGTH t > 0` by fs[bounded_preimage_rooted_def] >>
        `LENGTH t <= 1` by (SPOSE_NOT_THEN ASSUME_TAC >> fs[]) >>
        `LENGTH t <> 0` by fs[] >>
        `LENGTH t = 1` by (SPOSE_NOT_THEN ASSUME_TAC >> fs[]) >>
        `?a. t = [a]` by fs[LIST_LENGTH_1] >>
        `HD t = x` by fs[bounded_preimage_rooted_def] >>
        `HD [a] = a` by fs[HD] >>
        `x = a` by rw[] >> fs[])));


val prop_2_15_subgoal_5 = store_thm(
  "prop_2_15_subgoal_5",
  ``rooted_model M x M' /\ r0 ∈ (bounded_preimage_rooted M x).frame.world ==>
    ¬(bounded_preimage_rooted M x).frame.rel r0 [x]``,
  rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
  `LENGTH r0 + 1 = LENGTH [x]` by fs[bounded_preimage_rooted_def] >>
  `LENGTH [x] = 1` by fs[] >>
  `LENGTH r0 = 0` by fs[] >>
  `¬(LENGTH r0 > 0)` by fs[] >> fs[bounded_preimage_rooted_def]);

val FRONT_rel = store_thm(
  "FRONT_rel",
  ``rooted_model M x M' /\ t IN (bounded_preimage_rooted M x).frame.world /\ LENGTH t > 1 ==>
    (bounded_preimage_rooted M x).frame.rel (FRONT t) t``,
  rw[] >> `t <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> fs[]) >>
  `?x' l. t = SNOC x' l` by metis_tac[SNOC_CASES] >>
  rw[bounded_preimage_rooted_def] (* 2 *)
  >- (fs[bounded_preimage_rooted_def] >>
     `LENGTH l - 1 < LENGTH l` by fs[] >>
     `EL (LENGTH l - 1) (SNOC x' l) = LAST l /\
     EL ((LENGTH l - 1) + 1) (SNOC x' l) = x'` suffices_by metis_tac[] >> rw[] (* 2 *)
     >- (`SNOC x' l = l ++ [x']` by fs[] >>
        `EL (LENGTH l − 1) (SNOC x' l) = EL (LENGTH l − 1) l` by rw[EL_APPEND1] >>
        `l <> []` by (SPOSE_NOT_THEN ASSUME_TAC >> fs[]) >>
        `PRE (LENGTH l) = LENGTH l - 1` by fs[] >>
        `EL (LENGTH l - 1) l = LAST l` by rw[LAST_EL] >> fs[])
     >-  (`SNOC x' l = l ++ [x']` by fs[] >>
         `PRE (LENGTH (l ++ [x'])) = LENGTH l` by fs[] >>
         `l ++ [x'] <> []` by fs[] >>
         `EL (LENGTH l) (l ++ [x']) = LAST (l ++ [x'])` by metis_tac[LAST_EL] >>
         `LAST (l ++ [x']) = x'` by fs[] >> metis_tac[]))
  >- (`SNOC x' l = l ++ [x']` by fs[] >> metis_tac[EL_APPEND1]));



val prop_2_15_subgoal_6 = store_thm(
  "prop_2_15_subgoal_6",
  ``rooted_model M x M' /\ t ∈ (bounded_preimage_rooted M x).frame.world /\ t ≠ [x] ==>
    ∃!t0. t0 ∈ (bounded_preimage_rooted M x).frame.world ∧ (bounded_preimage_rooted M x).frame.rel t0 t``,
  rw[EXISTS_UNIQUE_THM] (* 2 *)
  >- (qexists_tac `FRONT t` >> rw[] (* 2 *)
     >- (`LENGTH t > 1`
            by (SPOSE_NOT_THEN ASSUME_TAC >> `LENGTH t <= 1` by fs[] >>
               `LENGTH t > 0` by fs[bounded_preimage_rooted_def] >>
               `LENGTH t = 1` by fs[] >>
               `?x. t = [x]` by fs[LIST_LENGTH_1] >>
               `HD t = x` by fs[bounded_preimage_rooted_def] >>
               `HD [x'] = x'` by fs[HD] >>
               `x = x'` by metis_tac[] >> metis_tac[]) >>
        metis_tac[FRONT_in_world])
     >- (`LENGTH t > 1`
            by (SPOSE_NOT_THEN ASSUME_TAC >> `LENGTH t <= 1` by fs[] >>
               `LENGTH t > 0` by fs[bounded_preimage_rooted_def] >>
               `LENGTH t = 1` by fs[] >>
               `?x. t = [x]` by fs[LIST_LENGTH_1] >>
               `HD t = x` by fs[bounded_preimage_rooted_def] >>
               `HD [x'] = x'` by fs[HD] >>
               `x = x'` by metis_tac[] >> metis_tac[]) >>
        metis_tac[FRONT_rel]))
  >- (`t0 = FRONT t /\ t0' = FRONT t` suffices_by metis_tac[] >>
      rw[] (* 2 *)
      >- (irule LIST_EQ (* 2 *)
         >- (rw[] >>
            `LENGTH t0 + 1 = LENGTH t` by fs[bounded_preimage_rooted_def] >>
            `EL x' t0 = EL x' t` by fs[bounded_preimage_rooted_def] >>
            `EL x' (FRONT t) = EL x' t` suffices_by metis_tac[] >>
            irule EL_FRONT (* 2 *)
            >- (Cases_on `t`
               >- fs[bounded_preimage_rooted_def]
               >- fs[NULL])
            >- (`LENGTH t0 = LENGTH (FRONT t)` suffices_by metis_tac[] >>
               `LENGTH (FRONT t) = LENGTH t - 1` suffices_by fs[] >>
               Cases_on `t = []` >- fs[bounded_preimage_rooted_def]
                                 >- rw[LENGTH_FRONT]))
         >- (`LENGTH t0 + 1 = LENGTH t` by fs[bounded_preimage_rooted_def] >>
            `LENGTH (FRONT t) = LENGTH t - 1` suffices_by fs[] >>
            Cases_on `t = []` >- fs[bounded_preimage_rooted_def]
                              >- rw[LENGTH_FRONT]))
      >- (irule LIST_EQ (* 2 *)
         >- (rw[] >>
            `LENGTH t0' + 1 = LENGTH t` by fs[bounded_preimage_rooted_def] >>
            `EL x' t0' = EL x' t` by fs[bounded_preimage_rooted_def] >>
            `EL x' (FRONT t) = EL x' t` suffices_by metis_tac[] >>
            irule EL_FRONT (* 2 *)
            >- (Cases_on `t`
               >- fs[bounded_preimage_rooted_def]
               >- fs[NULL])
            >- (`LENGTH t0' = LENGTH (FRONT t)` suffices_by metis_tac[] >>
               `LENGTH (FRONT t) = LENGTH t - 1` suffices_by fs[] >>
               Cases_on `t = []` >- fs[bounded_preimage_rooted_def]
                                 >- rw[LENGTH_FRONT]))
         >- (`LENGTH t0' + 1 = LENGTH t` by fs[bounded_preimage_rooted_def] >>
            `LENGTH (FRONT t) = LENGTH t - 1` suffices_by fs[] >>
            Cases_on `t = []` >- fs[bounded_preimage_rooted_def]
                              >- rw[LENGTH_FRONT]))));






val prop_2_15_strengthen = store_thm(
  "prop_2_15_strengthen",
  ``!M x:'b M'. rooted_model M x M' ==>
            ?MODEL f s:'b list. bounded_mor_image f MODEL M /\ tree MODEL.frame s /\ f s = x``,
  rpt strip_tac >>
  map_every qexists_tac [`bounded_preimage_rooted M x`,`LAST`,`[x]`] >>
  rw[tree_def,bounded_mor_image_def] (* 6 *)
  >- metis_tac[prop_2_15_subgoal_1]
  >- metis_tac[prop_2_15_subgoal_2]
  >- fs[bounded_preimage_rooted_def]
  >- metis_tac[prop_2_15_subgoal_4]
  >- metis_tac[prop_2_15_subgoal_5]
  >- metis_tac[prop_2_15_subgoal_6]);



val point_GENSUBMODEL_def = Define`
  point_GENSUBMODEL M w =
   <| frame := <| world := {v | v IN M.frame.world /\ (RESTRICT M.frame.rel M.frame.world)^* w v };
rel := λw1 w2. w1 IN M.frame.world /\ w2 IN M.frame.world /\ M.frame.rel w1 w2|>;
          valt := M.valt |>`;

val point_GENSUBMODEL_GENSUBMODEL = store_thm(
  "point_GENSUBMODEL_GENSUBMODEL",
  ``!M w. w IN M.frame.world ==> GENSUBMODEL (point_GENSUBMODEL M w) M``,
  rw[GENSUBMODEL_def,point_GENSUBMODEL_def] (* 2 *)
  >- (rw[SUBMODEL_def] >> fs[SUBSET_DEF])
  >- (simp[Once RTC_CASES2] >>
     `∃u. (RESTRICT M.frame.rel M.frame.world)^* w u ∧ RESTRICT M.frame.rel M.frame.world u w2` suffices_by metis_tac[] >>
     qexists_tac `w1` >> simp[Once RESTRICT_def]));


val point_GENSUBMODEL_rooted = store_thm(
  "point_GENSUBMODEL_rooted",
  ``!M w. w IN M.frame.world ==> rooted_model (point_GENSUBMODEL M w) w M``,
  rw[rooted_model_def] >> eq_tac >> rw[] (* 7 *)
  >- fs[point_GENSUBMODEL_def]
  >- fs[point_GENSUBMODEL_def]
  >- fs[point_GENSUBMODEL_def]
  >- (fs[point_GENSUBMODEL_def] >> metis_tac[RESTRICT_def])
  >- (fs[point_GENSUBMODEL_def] >> metis_tac[RESTRICT_def])
  >- fs[point_GENSUBMODEL_def]
  >- fs[point_GENSUBMODEL_def]);

val point_GENSUBMODEL_satis = store_thm(
  "point_GENSUBMODEL_satis",
  ``!M w f. satis M w f ==> satis (point_GENSUBMODEL M w) w f``,
  rw[] >>
  `w IN M.frame.world` by metis_tac[satis_in_world] >>
  `GENSUBMODEL (point_GENSUBMODEL M w) M` by metis_tac[point_GENSUBMODEL_GENSUBMODEL] >>
  `(RESTRICT M.frame.rel M.frame.world)^* w w` by metis_tac[RTC_CASES2] >>
  `w IN (point_GENSUBMODEL M w).frame.world` by fs[point_GENSUBMODEL_def] >>
  metis_tac[prop_2_6]);




val prop_2_15_corollary = store_thm(
  "prop_2_15_corollary",
  ``!M (w:'b) form. satis M w form ==>
  ?MODEL (s:'b list). tree MODEL.frame s /\ satis MODEL s form``,
  rw[] >>
  `w IN M.frame.world` by metis_tac[satis_in_world] >>
  `satis (point_GENSUBMODEL M w) w form` by metis_tac[point_GENSUBMODEL_satis] >>
  `rooted_model (point_GENSUBMODEL M w) w M` by metis_tac[point_GENSUBMODEL_rooted] >>
  drule prop_2_15_strengthen >> rw[] >>
  qexists_tac `MODEL` >> rw[] >> qexists_tac `s` >> rw[] >>
  fs[bounded_mor_image_def] >>
  `s IN MODEL.frame.world` by metis_tac[tree_def] >> metis_tac[prop_2_14]);






val _ = export_theory();
