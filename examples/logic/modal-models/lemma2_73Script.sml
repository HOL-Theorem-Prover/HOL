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
open prim_recTheory;

open equiv_on_partitionTheory;
open ultraproductTheory;
open ultrafilterTheory;

val _ = new_theory "lemma2_73";


Theorem countable_INFINITE_form_set:
!s: folLang$form -> bool.
   INFINITE s ==>
    ?enum. BIJ enum (univ(:num)) s
Proof
rw[] >>
`countable s`
  suffices_by
   (fs[COUNTABLE_ALT_BIJ] >> fs[] >> metis_tac[]) >>
irule subset_countable >>
qexists_tac `univ (:folLang$form)` >> rw[SUBSET_DEF]
QED


Definition FCT_def[simp]:
  (FCT (V v) = {}) /\
  (FCT (Fn s ts) = if ts = [] then {s} else (LIST_UNION (MAP FCT ts)))
Termination
  WF_REL_TAC `(measure (term_size))` >> rw[term_size_lemma]
End

Definition FC_def[simp]:
  (FC False = {}) /\
  (FC (Pred n ts) = LIST_UNION (MAP FCT ts)) /\
  (FC (IMP f1 f2) = FC f1 ∪ FC f2) /\
  (FC (FALL x f) = FC f)
End


val ftype_def = Define`
  ftype x G <=> G ⊆ {phi | FV phi SUBSET {x}}`;

val frealizes_def = Define`
  frealizes M x G <=> ?w. ftype x G /\ w IN M.Dom /\
                          !σ phi. (IMAGE σ univ(:num)) SUBSET M.Dom /\ phi IN G ==> fsatis M ((x=+w)σ) phi`;

(*
val expansion_def = Define`
expansion M A M' f <=> (M'.Dom = M.Dom) /\
                       (BIJ f (count (CARD A)) A) /\
                       (M'.Fun = \n args. if n < CARD A /\ args = [] then f n
                                           else CHOICE M.Dom) /\
                        M'.Pred = M.Pred`

*)


val expand_def = Define`
expand M A f = <| Dom := M.Dom;
                  Fun := \n args. if n < CARD A /\ args = [] then f n
                                           else CHOICE M.Dom;
                  Pred:= M.Pred |>`


val consistent_def = Define`
  consistent M G <=>
      !G0. FINITE G0 /\ G0 ⊆ G ==> ?σ. IMAGE σ univ(:num) SUBSET M.Dom /\ !phi. phi ∈ G0 ==> fsatis M σ phi `;

val n_saturated_def = Define`
  n_saturated M n ⇔
            ∀A G x f.
                (IMAGE f 𝕌(:num) ⊆ M.Dom /\ FINITE A ∧ CARD A ≤ n ∧ A ⊆ M.Dom ∧
                BIJ f (count (CARD A)) A ∧
                (∀phi.
                     phi ∈ G ⇒ form_functions phi ⊆ {(c, 0) | c < CARD A}) ∧
                 ftype x G ∧
                consistent (expand M A f) G) ⇒
                frealizes (expand M A f) x G`;

val countably_saturated_def = Define`
  countably_saturated M <=> !n. n_saturated M n`;


Theorem IMAGE_UPDATE:
  !σ a. IMAGE σ A ⊆ B ==> !b. b IN B ==> IMAGE σ(|a |-> b|) A ⊆ B
Proof
  rw[IMAGE_DEF,SUBSET_DEF] >> Cases_on `x' = a` >> rw[APPLY_UPDATE_THM] >> metis_tac[]
QED





Theorem ultraproduct_comm_termval:
  !t U I MS. ultrafilter U I ==> term_functions t = {} ==>
      !σ. (termval (mm2folm (ultraproduct_model U I MS)) σ t =
           termval (ultraproduct_folmodel U I (\i. mm2folm (MS i))) σ t)
Proof
 Cases_on `t` >> rw[termval_def]
QED

Theorem ultraproduct_image:
  !U I. ultrafilter U I ==>
       !A eqc. eqc IN (ultraproduct U I A) ==>
               !f. f IN eqc ==> (!i. i IN I ==> (f i) IN (A i))
Proof
  rw[ultraproduct_def,partition_def] >> fs[] >> fs[Cart_prod_def]
QED

Theorem ultraproduct_folmodel_well_formed:
!U I.  ultrafilter U I ==>
  !FMS n l. (!n0 l0 i. i IN I ==> ((FMS i).Fun n0 l0) IN (FMS i).Dom) ==>
         ((ultraproduct_folmodel U I FMS).Fun n l) IN (ultraproduct_folmodel U I FMS).Dom
Proof
  rw[ultraproduct_folmodel_def] >>
  rw[ultraproduct_def,folmodels2Doms_def,partition_def,Cart_prod_def] >>
  qexists_tac `\i. (FMS i).Fun n (MAP (λfc. CHOICE fc i) l)` >> rw[Once EXTENSION] >>
  rw[Uequiv_def,EQ_IMP_THM] (* 5 *)
  >- metis_tac[MEMBER_NOT_EMPTY]
  >- rw[Cart_prod_def]
  >- rw[Cart_prod_def]
  >> (`{i | i ∈ I' ∧ x i = (FMS i).Fun n (MAP (λfc. CHOICE fc i) l)} =
     {i | i ∈ I' ∧ (FMS i).Fun n (MAP (λfc. CHOICE fc i) l) = x i}` suffices_by metis_tac[] >>
     rw[EXTENSION] >> metis_tac[])
QED

Theorem ultraproduct_comm_Dom:
  !U I MS. (ultraproduct_folmodel U I (\i. mm2folm (MS i))).Dom =
           (mm2folm (ultraproduct_model U I MS)).Dom
Proof
 rw[ultraproduct_model_def,ultraproduct_folmodel_def,mm2folm_def,folmodels2Doms_def,models2worlds_def]
QED

Theorem mm2folm_ultraproduct_model_Dom:
!U I MS. (mm2folm (ultraproduct_model U I MS)).Dom = ultraproduct U I (models2worlds MS)
Proof
rw[ultraproduct_model_def,ultraproduct_folmodel_def,mm2folm_def,folmodels2Doms_def,models2worlds_def]
QED

Theorem ultraproduct_folmodel_Dom:
!U I FMS. (ultraproduct_folmodel U I FMS).Dom = ultraproduct U I (folmodels2Doms FMS)
Proof
rw[ultraproduct_folmodel_def]
QED

Theorem mm2folm_well_formed:
  !M n l. M.frame.world <> {} ==> ((mm2folm M).Fun n l) IN (mm2folm M).Dom
Proof
  rw[mm2folm_def] >> metis_tac[CHOICE_DEF]
QED


Theorem termval_IN_ultraproduct_Dom:
!U I MS. ultrafilter U I ==>
 !σ. IMAGE σ 𝕌(:num) ⊆ ultraproduct U I (models2worlds MS) ==>
  !a. (termval (mm2folm (ultraproduct_model U I MS)) σ a) IN
      (ultraproduct U I (models2worlds MS))
Proof
  rw[] >>
  `(ultraproduct U I' (models2worlds MS)) = (mm2folm (ultraproduct_model U I' MS)).Dom`
  by metis_tac[mm2folm_ultraproduct_model_Dom] >>
  rw[] >> irule termval_IN_Dom >> rw[] (* 2 *)
  >- (irule mm2folm_well_formed >> fs[IMAGE_DEF,SUBSET_DEF] >>
     `(ultraproduct_model U I' MS).frame.world =
      (mm2folm (ultraproduct_model U I' MS)).Dom` by fs[mm2folm_def] >> rw[] >>
     simp[GSYM MEMBER_NOT_EMPTY] >> fs[PULL_EXISTS] >> qexists_tac `σ x` >> rw[])
  >- fs[mm2folm_def]
QED

Theorem ultraproduct_val_IN_A:
  !U I. ultrafilter U I ==>
     !A eqc. eqc IN ultraproduct U I A ==>
              !f. f IN eqc ==> (!i. i IN I ==> (f i) IN (A i))
Proof
  rw[] >> fs[ultraproduct_def,partition_def,Cart_prod_def] >> rfs[]
QED

Theorem ultraproduct_comm_feval:
  !phi U I MS. ultrafilter U I (* /\ (!i. i IN I ==> (MS i).frame.world <> {})*)
          ==> form_functions phi = {} ==>
            !σ. IMAGE σ (univ(:num)) ⊆ ultraproduct U I (models2worlds MS) ==>
                (feval (mm2folm (ultraproduct_model U I MS)) σ phi <=>
                 feval (ultraproduct_folmodel U I (\i. mm2folm (MS i))) σ phi)
Proof
  Induct_on `phi` (* 4 *)
  >- rw[feval_def]
  >- (rw[feval_def] >>
      `(MAP (termval (mm2folm (ultraproduct_model U I' MS)) σ) l) =
       (MAP (termval (ultraproduct_folmodel U I' (λi. mm2folm (MS i))) σ) l)`
        by
         (irule MAP_CONG >> rw[] >> irule ultraproduct_comm_termval >> rw[] >>
          SPOSE_NOT_THEN ASSUME_TAC >> fs[GSYM MEMBER_NOT_EMPTY] >>
          `x' IN LIST_UNION (MAP term_functions l)`
           suffices_by metis_tac[MEMBER_NOT_EMPTY] >>
          simp[IN_LIST_UNION] >> qexists_tac `term_functions x` >>
          rw[MEM_MAP] >> metis_tac[]) >>
     rw[] >>
     qabbrev_tac
      `mapl = (MAP (termval (ultraproduct_folmodel U I' (λi. mm2folm (MS i))) σ) l)` >>
     Cases_on `mapl = []`(* 2 *)
     >- (fs[] >> rw[mm2folm_def,ultraproduct_folmodel_def,ultraproduct_model_def] >>
        metis_tac[EMPTY_NOTIN_ultrafilter])
     >- (`(?a. l = [a]) \/ (?a b. l = [a;b]) \/ (?a b c d. l = a :: b :: c :: d)` by
            (Cases_on `l` >> fs[] >> Cases_on `t` >> fs[] >> Cases_on `t'` >> fs[])
        (* 3 *)
        >- (rw[] >>
            qabbrev_tac `sl = termval (mm2folm (ultraproduct_model U I' MS)) σ a` >>
            rw[mm2folm_def,ultraproduct_folmodel_def,ultraproduct_model_def] >>
            rw[EQ_IMP_THM] (* 3 *)
            >- (`{i | i IN I' /\ f i = (CHOICE sl) i} IN U`
                 by
                  (irule ultraproduct_same_eqclass >> rw[] >>
                  map_every qexists_tac [`models2worlds MS`,`sl`] >> rw[] >>
                  `sl <> {}` suffices_by metis_tac[CHOICE_DEF] >>
                  drule ultraproduct_eqclass_non_empty >> rw[] >> metis_tac[]) >>
               `{i | i ∈ I' ∧ f i ∈ (MS i).valt n} ∩ {i | i ∈ I' ∧ f i = CHOICE sl i} ⊆
                {i | i ∈ I' ∧ CHOICE sl i ∈ (MS i).frame.world ∧
                (MS i).valt n (CHOICE sl i)}`
                by
                 (rw[INTER_DEF,SUBSET_DEF] (* 2 *)
                  >- (drule ultraproduct_image >> rw[] >>
                      first_x_assum
                       (qspecl_then [`models2worlds MS`,`sl`,`CHOICE sl`,`x`] assume_tac)>>
                      fs[models2worlds_def] >> first_x_assum irule >> rw[] >>
                      `sl <> {}` suffices_by metis_tac[CHOICE_DEF] >>
                      drule ultraproduct_eqclass_non_empty >> rw[] >> metis_tac[])
                  >- fs[IN_DEF]) >>
                  (* proved subset *)
               irule ultrafilter_SUBSET' >> rw[PULL_EXISTS] (* 2 *)
               >- metis_tac[ultrafilter_INTER]
               >- (qexists_tac `I'` >> rw[SUBSET_DEF]))
            >- (drule ultraproduct_folmodel_well_formed >> rw[Abbr`sl`] >>
                `ultraproduct U I' (models2worlds MS) =
                 (mm2folm (ultraproduct_model U I' MS)).Dom`
                 by metis_tac[mm2folm_ultraproduct_model_Dom] >>
                rw[] >> irule termval_IN_Dom >> rw[](* 2 *)
                >- (`(ultraproduct_model U I' MS).frame.world <> {}`
                     suffices_by metis_tac[mm2folm_well_formed] >>
                    rw[Once ultraproduct_model_def] >>
                    fs[mm2folm_ultraproduct_model_Dom] >>
                    fs[IMAGE_DEF,SUBSET_DEF,GSYM MEMBER_NOT_EMPTY] >>
                    qexists_tac `σ x` >> rw[]>>
                    metis_tac[])
                >- metis_tac[mm2folm_ultraproduct_model_Dom])
            >- (qexists_tac `CHOICE sl` >> rw[] (* 2 *)
                >- (`sl <> {}` suffices_by metis_tac[CHOICE_DEF] >>
                    rw[Abbr`sl`] >> drule ultraproduct_eqclass_non_empty >> rw[] >>
                    metis_tac[termval_IN_ultraproduct_Dom])
                    (*once proved sl in world then true by some lemma (fixed)*)
                >- (irule ultrafilter_SUBSET' >> rw[PULL_EXISTS] (* 2 *)
                    >- (qexists_tac `{i | i ∈ I' ∧ CHOICE sl i ∈ (MS i).frame.world ∧
                        (MS i).valt n (CHOICE sl i)}` >> rw[SUBSET_DEF,IN_DEF])
                    >- (qexists_tac `I'` >> rw[SUBSET_DEF]))))
        (*one out of three subgoals solved here*)
        >- (rw[] >>
            qabbrev_tac `sl1 = termval (mm2folm (ultraproduct_model U I' MS)) σ a` >>
            qabbrev_tac `sl2 = termval (mm2folm (ultraproduct_model U I' MS)) σ b` >>
            rw[mm2folm_def,ultraproduct_folmodel_def,ultraproduct_model_def] >>
            rw[EQ_IMP_THM](*5*)
            >- (`{i | i IN I' /\ f i = (CHOICE sl1) i} IN U`
                 by
                  (irule ultraproduct_same_eqclass >> rw[] >>
                   map_every qexists_tac [`models2worlds MS`,`sl1`] >> rw[] >>
                   `sl1 <> {}` suffices_by metis_tac[CHOICE_DEF] >>
                   drule ultraproduct_eqclass_non_empty >> rw[] >> metis_tac[]) >>
                `{i | i IN I' /\ g i = (CHOICE sl2) i} IN U`
                 by
                  (irule ultraproduct_same_eqclass >> rw[] >>
                   map_every qexists_tac [`models2worlds MS`,`sl2`] >> rw[] >>
                   `sl2 <> {}` suffices_by metis_tac[CHOICE_DEF] >>
                   drule ultraproduct_eqclass_non_empty >> rw[] >> metis_tac[]) >>
                qmatch_abbrev_tac `BS IN U` >>
                `{i | i ∈ I' ∧ (MS i).frame.rel (f i) (g i)} ∩
                 {i | i ∈ I' ∧ f i = CHOICE sl1 i} ∩ {i | i ∈ I' ∧ g i = CHOICE sl2 i} ⊆ BS`                  by
                  (* start a proof subset *)
                  (rw[SUBSET_DEF,INTER_DEF,Abbr`BS`] (* 3 *)
                   >- fs[]
                   >- (`f x IN (MS x).frame.world` suffices_by metis_tac[] >>
                       drule ultraproduct_val_IN_A >> rw[] >>
                       first_x_assum
                        (qspecl_then [`models2worlds MS`,`sl1`, `f`,`x`] assume_tac) >>
                       fs[models2worlds_def] >> metis_tac[])
                   >- (`g x IN (MS x).frame.world` suffices_by metis_tac[] >>
                       drule ultraproduct_val_IN_A >> rw[] >>
                       first_x_assum
                        (qspecl_then [`models2worlds MS`,`sl2`, `g`,`x`] assume_tac) >>
                   fs[models2worlds_def] >> metis_tac[])) >>
                  (*subset proof end*)
                `BS ⊆ I'` by fs[Abbr`BS`,SUBSET_DEF] >>
                drule ultrafilter_INTER_INTER_SUBSET >> rw[] >>
                first_x_assum irule >> metis_tac[])
            >- (SPOSE_NOT_THEN ASSUME_TAC >>
                `{i | i ∈ I' ∧ n = 0 ∧ (MS i).frame.rel (CHOICE sl1 i) (CHOICE sl2 i) ∧
                    CHOICE sl1 i ∈ (MS i).frame.world ∧
                    CHOICE sl2 i ∈ (MS i).frame.world} = {}` by rw[Once EXTENSION] >>
                metis_tac[EMPTY_NOTIN_ultrafilter])
            >- (map_every qexists_tac [`CHOICE sl1`,`CHOICE sl2`] >> rw[] (* 3 *)
                >- (`sl1 <> {}` suffices_by metis_tac[CHOICE_DEF] >>
                    drule ultraproduct_eqclass_non_empty >> rw[] >> rw[Abbr`sl1`] >>
                    `termval (mm2folm (ultraproduct_model U I' MS)) σ a ∈
                    ultraproduct U I' (models2worlds MS)`
                      by metis_tac[termval_IN_ultraproduct_Dom]>>
                    metis_tac[ultraproduct_eqclass_non_empty])
                >- (`sl2 <> {}` suffices_by metis_tac[CHOICE_DEF] >>
                    drule ultraproduct_eqclass_non_empty >> rw[] >> rw[Abbr`sl2`] >>
                    `termval (mm2folm (ultraproduct_model U I' MS)) σ b ∈
                    ultraproduct U I' (models2worlds MS)`
                      by metis_tac[termval_IN_ultraproduct_Dom]>>
                    metis_tac[ultraproduct_eqclass_non_empty])
                >- (irule ultrafilter_SUBSET' >> rw[] (* 2 *)
                    >- (qexists_tac
                          `{i |i ∈ I' ∧ n = 0 ∧(MS i).frame.rel
                            (CHOICE sl1 i) (CHOICE sl2 i) ∧
                            CHOICE sl1 i ∈ (MS i).frame.world ∧
                            CHOICE sl2 i ∈ (MS i).frame.world}`>>
                        rw[SUBSET_DEF])
                    >- (qexists_tac `I'` >> rw[SUBSET_DEF])))
            >- (rw[Abbr`sl1`] >> irule termval_IN_ultraproduct_Dom >> rw[])
            >- (rw[Abbr`sl2`] >> irule termval_IN_ultraproduct_Dom >> rw[]))
        >- (rw[mm2folm_def,ultraproduct_folmodel_def,ultraproduct_model_def] >>
           metis_tac[EMPTY_NOTIN_ultrafilter])))
  >- rw[feval_def]
  >- (rw[feval_def] >> rw[EQ_IMP_THM] (* 2 same *) >>
     first_x_assum (qspecl_then [`U`,`I'`,`MS`] assume_tac) >> rfs[] >>
     first_x_assum (qspec_then `σ(|n |-> a|)` assume_tac) >>
     `(ultraproduct_folmodel U I' (λi. mm2folm (MS i))).Dom =
      (mm2folm (ultraproduct_model U I' MS)).Dom` by
        metis_tac[ultraproduct_comm_Dom,mm2folm_ultraproduct_model_Dom] >>
     `IMAGE σ⦇n ↦ a⦈ 𝕌(:num) ⊆ ultraproduct U I' (models2worlds MS)` suffices_by metis_tac[] >>
     irule IMAGE_UPDATE >> rw[] >>
     metis_tac[ultraproduct_comm_Dom,mm2folm_ultraproduct_model_Dom])
QED




(* theory on shift in order to pass from expansion to mm2folm model and then to ultraprodfol model*)

Definition shift_term_def:
  shift_term n (V m) = V (m+n) /\
  shift_term n (Fn m l) = if l = [] then (V m) else (Fn m (MAP (shift_term n) l))
Termination
WF_REL_TAC `measure (term_size o SND)` >> rw[term_size_lemma]
End

Definition shift_form_def:
  shift_form n False = False /\
  shift_form n (Pred m l) = Pred m (MAP (shift_term n) l) /\
  shift_form n (IMP f1 f2) = IMP (shift_form n f1) (shift_form n f2) /\
  shift_form n (FALL x f) = FALL (x + n) (shift_form n f)
End

Definition shift_valuation_def:
  shift_valuation n σ f = \m. if m < n then (f m) else (σ (m-n))
End
(*
Theorem expansion_shift_termval:
  !M A M' f. expansion (mm2folm M) A M' f ==>
            !t. (∀c. c ∈ FCT t ⇒ c < CARD A) ==>
                !σ. (termval M' σ t =
                    termval (mm2folm M) (shift_valuation (CARD A) σ f) (shift_term (CARD A) t))
Proof
  strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
  completeInduct_on `term_size t` >> Cases_on `t` >> rw[] (* 3 *)
  >- rw[termval_def,shift_valuation_def,shift_term_def]
  >- (rw[termval_def,shift_valuation_def,shift_term_def] >> fs[expansion_def])
  >- (rw[termval_def,shift_valuation_def,shift_term_def] >> fs[expansion_def] >>
      fs[mm2folm_def])
QED
*)

Theorem expansion_shift_termval:
  !M A f. (BIJ f (count (CARD A)) A) ==>
            !t. (∀c. c ∈ FCT t ⇒ c < CARD A) ==>
                !σ. (termval (expand (mm2folm M) A f) σ t =
                    termval (mm2folm M) (shift_valuation (CARD A) σ f) (shift_term (CARD A) t))
Proof
  strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
  completeInduct_on `term_size t` >> Cases_on `t` >> rw[] (* 3 *)
  >- rw[termval_def,shift_valuation_def,shift_term_def]
  >- (rw[termval_def,shift_valuation_def,shift_term_def] >> fs[expand_def])
  >- (rw[termval_def,shift_valuation_def,shift_term_def] >> fs[expand_def] >>
      fs[mm2folm_def])
QED

Theorem expansion_shift_feval:
  !M A f. (BIJ f (count (CARD A)) A)  ==>
            !phi. (∀c. c ∈ FC phi ⇒ c < CARD A) ==>
                 !σ.
                    IMAGE σ (univ(:num)) ⊆ M.frame.world ==>
                    (feval (expand (mm2folm M) A f) σ phi <=>
                    feval (mm2folm M) (shift_valuation (CARD A) σ f) (shift_form (CARD A) phi))
Proof
  strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> Induct_on `phi` (* 4 *)
  >- rw[feval_def,shift_form_def]
  >- (rw[feval_def,shift_form_def,shift_term_def,shift_valuation_def,expand_def] >>
     ` (expand (mm2folm M) A f).Pred n (MAP (termval (expand (mm2folm M) A f) σ) l) ⇔
       (expand (mm2folm M) A f).Pred n
          (MAP
             (termval (mm2folm M)
                (λm. if m < CARD A then f m else σ (m - CARD A)))
             (MAP (shift_term (CARD A)) l))` suffices_by fs[expand_def] >>
     AP_TERM_TAC >> simp[MAP_MAP_o] >> irule MAP_CONG >> rw[] >>
     drule expansion_shift_termval >> rw[] >>
     first_x_assum (qspecl_then [`M`,`x`, `σ`] assume_tac) >> fs[shift_valuation_def] >>
     first_x_assum irule >> rw[] >> first_x_assum irule >> rw[MEM_MAP,PULL_EXISTS] >>
     metis_tac[])
  >- (rw[FC_def] >>
     `(∀c. c ∈ FC phi ==> c < CARD A) /\
      (!c. c ∈ FC phi' ⇒ c < CARD A)` by metis_tac[] >>
     first_x_assum drule >> first_x_assum drule >> rw[] >>
     rw[EQ_IMP_THM,shift_form_def])
  >- (rw[FC_def] >> first_x_assum drule >> rw[feval_def] >> rw[EQ_IMP_THM]
    >- (rw[shift_form_def] >>
     `(shift_valuation (CARD A) σ f)⦇n + CARD A ↦ a⦈ =
      (shift_valuation (CARD A) σ(|n |-> a|) f)` by (* store as little lemma ?*)
         (rw[FUN_EQ_THM,shift_valuation_def] >>
         Cases_on `x < CARD A` (* 2 *)
         >- rw[APPLY_UPDATE_THM]
         >- (Cases_on `x = n + CARD A` >> rw[APPLY_UPDATE_THM])) >>
     rw[] >> first_x_assum (qspec_then `σ(|n |-> a|)` assume_tac) >> rw[] >>
     `IMAGE σ⦇n ↦ a⦈ 𝕌(:num) ⊆ M.frame.world /\ feval (expand (mm2folm M) A f) σ⦇n ↦ a⦈ phi` suffices_by metis_tac[] >>
     rw[] (* 2 *) >- (irule IMAGE_UPDATE >> fs[mm2folm_def]) >- fs[mm2folm_def,expand_def])
    >- (first_x_assum (qspec_then `σ(|n |-> a|)` assume_tac) >>
       `IMAGE σ⦇n ↦ a⦈ 𝕌(:num) ⊆ M.frame.world /\
       feval (mm2folm M) (shift_valuation (CARD A) σ⦇n ↦ a⦈ f)
           (shift_form (CARD A) phi)` suffices_by metis_tac[] >> rw[] (* 2 *)
       >- (irule IMAGE_UPDATE >> fs[mm2folm_def,expand_def] >> rfs[])
       >- (fs[shift_form_def] >> first_x_assum (qspec_then `a` assume_tac) >> rw[] >>
          `a IN (mm2folm M).Dom` by (fs[mm2folm_def,expand_def] >> rfs[]) >> fs[] >>
          `(shift_valuation (CARD A) σ f)⦇n + CARD A ↦ a⦈ =
           (shift_valuation (CARD A) σ(|n |-> a|) f)` by (* store as little lemma ?*)
             (rw[FUN_EQ_THM,shift_valuation_def] >>
             Cases_on `x < CARD A` (* 2 *)
              >- rw[APPLY_UPDATE_THM]
              >- (Cases_on `x = n + CARD A` >> rw[APPLY_UPDATE_THM])) >>
         fs[])))
QED

Theorem shift_term_functions_EMPTY:
  !t. (∀c. c ∈ term_functions t ⇒ FST c ∈ count (CARD A) ∧ SND c = 0) ==>
      term_functions (shift_term (CARD A) t) = {}
Proof
  completeInduct_on `term_size t` >> rw[] >> Cases_on `t` >> fs[shift_term_def] >> Cases_on `l = []`>>
  fs[term_functions_def] >> first_x_assum (qspec_then `(n,LENGTH l)` assume_tac) >> fs[]
QED

Theorem shift_form_functions_EMPTY:
  !phi. (∀c. c ∈ form_functions phi ⇒ FST c ∈ count (CARD A) ∧ SND c = 0) ==>
     form_functions (shift_form (CARD A) phi) = {}
Proof
  Induct_on `phi` (* 4 *)
  >- rw[form_functions_def,shift_form_def]
  >- (rw[form_functions_def,shift_form_def] >> SPOSE_NOT_THEN ASSUME_TAC >>
      fs[GSYM MEMBER_NOT_EMPTY] >> fs[MEM_MAP,PULL_EXISTS] >> Cases_on `y'` (* 2 *)
     >- (fs[shift_term_def] >> metis_tac[MEMBER_NOT_EMPTY])
     >- (rfs[] >> fs[term_functions_def,shift_term_def] >> Cases_on `l' = []` >> fs[] (* 2 same *)>>
        first_x_assum drule >> rw[] >> qexists_tac `(n,LENGTH l')` >> rw[]))
  >- rw[form_functions_def,shift_form_def]
  >- rw[form_functions_def,shift_form_def]
QED



Theorem shift_FVT:
!t x. (FVT t ⊆ s /\
       (∀c. c ∈ term_functions t ⇒ FST c ∈ count (CARD A) ∧ SND c = 0)
      ) ==>
         (FVT (shift_term (CARD A) t)) DIFF (count (CARD A)) ⊆ {x + CARD A| x IN s}
Proof
completeInduct_on `term_size t` >> Cases_on `t` >> rw[FVT_def,shift_term_def] >>
rw[SUBSET_DEF] >> fs[MEM_MAP] >> rw[] >> fs[PULL_FORALL] >>
first_x_assum (qspec_then `a'` assume_tac) >> drule term_size_lemma >>
strip_tac >> first_x_assum (qspec_then `n` assume_tac) >> fs[ADD_CLAUSES] >>
fs[PULL_EXISTS] >>
`FVT (shift_term (CARD A) a') DIFF count (CARD A) ⊆ {x + CARD A| x IN s}`
  suffices_by rw[DIFF_DEF,SUBSET_DEF] >>
first_x_assum irule >> rw[] (* 3 *)
>- (fs[SUBSET_DEF,PULL_EXISTS,PULL_FORALL,MEM_MAP] >> metis_tac[])
>- metis_tac[] >>
metis_tac[]
QED

Theorem shift_FV:
!phi s. (FV phi ⊆ s /\
         (∀c. c ∈ form_functions phi ⇒ FST c ∈ count (CARD A) ∧ SND c = 0)
        ) ==>
        (FV (shift_form (CARD A) phi)) DIFF (count (CARD A)) ⊆ {x + CARD A| x IN s}
Proof
Induct_on `phi` (* 4 *)
>- rw[FV_def,shift_form_def]
>- (rw[FV_def,shift_form_def,SUBSET_DEF,DIFF_DEF,PULL_FORALL,PULL_EXISTS] >>
   fs[MEM_MAP,PULL_EXISTS,PULL_FORALL] >> rw[] >>
   `FVT (shift_term (CARD A) y') DIFF count (CARD A) ⊆ {x + CARD A | x IN s}`
     suffices_by rw[DIFF_DEF,SUBSET_DEF] >>
   irule shift_FVT >> rw[] (* 3 *)
   >- metis_tac[] >- metis_tac[] >> rw[SUBSET_DEF] >> metis_tac[])
>- (rw[FV_def,shift_form_def,DIFF_DEF,SUBSET_DEF] (* 2 *)
    >- (`FV (shift_form (CARD A) phi) DIFF count (CARD A) ⊆ {x + CARD A| x IN s}`
         suffices_by fs[DIFF_DEF,SUBSET_DEF,count_def] >>
        first_x_assum irule >> rw[SUBSET_DEF])
    >- (`FV (shift_form (CARD A) phi') DIFF count (CARD A) ⊆ {x + CARD A| x IN s}`
         suffices_by fs[DIFF_DEF,SUBSET_DEF,count_def] >>
        first_x_assum irule >> rw[SUBSET_DEF]))
>- (rw[shift_form_def,FV_def] >>
    first_x_assum (qspec_then `n INSERT s` assume_tac) >>
    `FV (shift_form (CARD A) phi) DIFF count (CARD A) ⊆
        {x + CARD A | x ∈ n INSERT s}`
     suffices_by
      (fs[DIFF_DEF,DELETE_DEF,SUBSET_DEF,INSERT_DEF] >> rw[] >> metis_tac[]) >>
    first_x_assum irule >> rw[] >> fs[SUBSET_DEF,DELETE_DEF,INSERT_DEF] >>
    metis_tac[])
QED

(*theory for shifting ends*)

Theorem ultraproduct_sat_l1:
!enum s. BIJ enum (univ(:num)) s ==>
     !M σ. (!n. feval M σ (enum n)) ==>
           (!phi. phi IN s ==> feval M σ phi)
Proof
rw[] >> fs[BIJ_DEF,INJ_DEF,SURJ_DEF] >>
first_x_assum drule >> metis_tac[]
QED

(*conj enum*)

val fCONJ_def = Define`
fCONJ enum = PRIM_REC (True) (\conjn n. fAND conjn (enum n))`

Theorem fAND_feval:
!M σ. feval M σ (fAND p q) <=>
      (feval M σ p /\ feval M σ q)
Proof
rw[feval_def,fAND_def,fNOT_def,fDISJ_def]
QED

Theorem fCONJ_imp_enum:
!n enum M σ.
   feval M σ (fCONJ enum n) ==>
    !m. m < n ==> feval M σ (enum m)
Proof
Induct_on `n` (* 2 *)
>- rw[fCONJ_def,PRIM_REC_THM,feval_def] >>
rw[fCONJ_def,feval_def] >> Cases_on `m < n` (* 2 *)
>- (first_x_assum irule >> fs[PRIM_REC_THM,fAND_feval,fCONJ_def]) >>
`m = n` by fs[] >> fs[PRIM_REC_THM]
QED

Theorem fCONJ_imp_fCONJ:
!n enum M σ.
   feval M σ (fCONJ enum (n + 1)) ==>
    feval M σ (fCONJ enum n)
Proof
rw[fCONJ_def,fAND_feval,PRIM_REC_THM,GSYM ADD1]
QED

Theorem fCONJ_imp_fCONJ_LE:
!n enum M σ.
   feval M σ (fCONJ enum n) ==>
    !m. m <= n ==> feval M σ (fCONJ enum m)
Proof
Induct_on `n` (* 2 *)
>- rw[fCONJ_def,feval_def,PRIM_REC_THM,True_def,fNOT_def] >>
rw[] >> Cases_on `m <= n` (* 2 *)
>- (first_x_assum irule >>
   fs[fCONJ_def,feval_def,PRIM_REC_THM,True_def,fNOT_def]) >>
`m = SUC n` by fs[] >> rw[]
QED

Theorem fAND_FV:
!p q. FV (fAND p q) = FV p ∪ FV q
Proof
rw[FV_def,fAND_def,fNOT_def,fDISJ_def,EXTENSION] >> metis_tac[]
QED

Theorem fCONJ_FV:
!enum s.
  (!n. FV (enum n) ⊆ s) ==>
    !k. (FV (fCONJ enum k) ⊆ s)
Proof
strip_tac >> strip_tac >> strip_tac >> Induct_on `k` (* 2 *)
>- rw[fCONJ_def,FV_def,PRIM_REC_THM,SUBSET_DEF,True_def,fNOT_def,fDISJ_def] >>
fs[fCONJ_def,PRIM_REC_THM,fAND_FV]
QED

Theorem enum_imp_fCONJ:
!n enum M σ.
  (!t. t < n ==> feval M σ (enum t)) ==> feval M σ (fCONJ enum n)
Proof
Induct_on `n` >> rw[] (* 2 *)
>- rw[fCONJ_def,feval_def,True_def,PRIM_REC_THM] >>
`!t. t < n ==> feval M σ (enum t)` by rw[] >>
first_x_assum drule >>
rw[fCONJ_def,FV_def,PRIM_REC_THM,SUBSET_DEF,True_def,fNOT_def,fDISJ_def]
QED


Theorem ultraproduct_sat_case2:
!U I FMS x. countably_incomplete U I ==>
  !N. x IN N ==>
   !f. IMAGE f (univ(:num)) ⊆ ultraproduct U I (folmodels2Doms FMS) ==>
   (∀i ff ll. i ∈ I ⇒ (FMS i).Fun ff ll ∈ (FMS i).Dom) ==>
  !s. (!phi. phi IN s ==> form_functions phi = {} /\ (FV phi) DIFF N ⊆ {x}) ==>
       (!ss. FINITE ss /\ ss ⊆ s ==>
          ?σ. (IMAGE σ (univ(:num)) ⊆ (ultraproduct_folmodel U I FMS).Dom) /\
              (!n. n IN N ==> σ n = f n) /\
              (!phi. phi IN ss ==> feval (ultraproduct_folmodel U I FMS) σ phi)) ==>
       (?σ. (IMAGE σ (univ(:num)) ⊆ (ultraproduct_folmodel U I FMS).Dom) /\
            (!n. n IN N ==> σ n = f n)  /\
            (!phi. phi IN s ==> feval (ultraproduct_folmodel U I FMS) σ phi))
Proof
rw[] >>
qexists_tac `f` >> rw[] (* 2 *)
>- rw[ultraproduct_folmodel_def] >>
`FINITE {phi}` by fs[] >>
`{phi} ⊆ s` by fs[SUBSET_DEF] >>
first_x_assum drule >> rw[] >>
`feval (ultraproduct_folmodel U I' FMS) σ phi =
 feval (ultraproduct_folmodel U I' FMS) f phi` suffices_by metis_tac[] >>
irule holds_valuation >>
`!x. x IN FV phi ==> x IN N` suffices_by metis_tac[] >> rw[] >>
last_x_assum drule >> rw[DIFF_DEF,EXTENSION] >> metis_tac[]
QED

Theorem ultraproduct_sat_case1:
!U I FMS x. countably_incomplete U I ==>
  !N. x NOTIN N ==>
   !f. IMAGE f (univ(:num)) ⊆ ultraproduct U I (folmodels2Doms FMS) ==>
   (∀i ff ll. i ∈ I ⇒ (FMS i).Fun ff ll ∈ (FMS i).Dom) ==>
  !s. (!phi. phi IN s ==> form_functions phi = {} /\ (FV phi) DIFF N ⊆ {x}) ==>
       (!ss. FINITE ss /\ ss ⊆ s ==>
          ?σ. (IMAGE σ (univ(:num)) ⊆ (ultraproduct_folmodel U I FMS).Dom) /\
              (!n. n IN N ==> σ n = f n) /\
              (!phi. phi IN ss ==> feval (ultraproduct_folmodel U I FMS) σ phi)) ==>
       (?σ. (IMAGE σ (univ(:num)) ⊆ (ultraproduct_folmodel U I FMS).Dom) /\
            (!n. n IN N ==> σ n = f n)  /\
            (!phi. phi IN s ==> feval (ultraproduct_folmodel U I FMS) σ phi))
Proof
rw[] >> Cases_on `FINITE s` (* 2 *)
>- (first_x_assum irule >> rw[SUBSET_DEF]) >>
drule countably_incomplete_chain >> rw[] >>
fs[countably_incomplete_def] >>
`!phi σ FMS. IMAGE σ (univ(:num)) ⊆ ultraproduct U (In 0) (folmodels2Doms FMS) ==>
             (!i ff ll. i IN (In 0) ==> (FMS i).Fun ff ll IN (FMS i).Dom) ==>
                  (feval (ultraproduct_folmodel U (In 0) FMS) σ phi <=>
                  {i | i IN (In 0) /\ feval (FMS i) (\x. (CHOICE (σ x)) i) phi} IN U)`
  by 
   (drule thm_A_19_ii >> rw[] >> first_x_assum irule >> 
    fs[wffm_def,valuation_def,IMAGE_DEF,SUBSET_DEF,ultraproduct_folmodel_def] >>    metis_tac[]) >>
`?enum. BIJ enum (univ(:num)) s` by metis_tac[countable_INFINITE_form_set] >>
(* cheated! need Godel numbering*)
(*first suffices start, change the goal into feval each formula*)
qabbrev_tac `upfm = (ultraproduct_folmodel U (In 0) FMS)` >>
`?σ. IMAGE σ 𝕌(:num) ⊆ upfm.Dom ∧ (∀n. n ∈ N ⇒ σ n = f n) ∧
     ∀n. feval upfm σ (enum n)`
  suffices_by metis_tac[ultraproduct_sat_l1] >>
(*first suffices end*)
(*conj*)
qabbrev_tac `conj = fCONJ enum` >>
(*second suffices begin, change the goal into feval of conj*)
`∃σ. IMAGE σ 𝕌(:num) ⊆ upfm.Dom ∧ (∀n. n ∈ N ⇒ σ n = f n) ∧
     ∀n. feval upfm σ (enum n)`
  suffices_by rw[] >>
`∃rv.  (∀v i. i ∈ (In 0) ⇒ rv v i ∈ (FMS i).Dom) /\
       (∀n. n ∈ N ⇒ {g | Uequiv U (In 0) (folmodels2Doms FMS) g (rv n)} = f n) ∧
       ∀k:num.
             {i | i ∈ (In 0) ∧ feval (FMS i) (λv. rv v i) (conj k)} ∈ U`
 suffices_by
  (rw[] >> drule ultraproduct_suffices_rep >> rw[] >>
   first_x_assum (qspecl_then [`FMS`,`rv`] assume_tac) >>
   qabbrev_tac `σ0 = (λv. {g | Uequiv U (In 0) (folmodels2Doms FMS) g (rv v)})` >>
   qexists_tac `σ0` >> drule rep_give_wf_valuation >> strip_tac >>
   first_x_assum (qspecl_then [`FMS`,`rv`] assume_tac) >>
   first_x_assum drule >> rw[] (*3*)
   >- rw[Abbr`upfm`,ultraproduct_folmodel_Dom]
   >- rw[Abbr`σ0`,FUN_EQ_THM]
   >- (first_x_assum (qspec_then `conj (n + 1)` assume_tac) >>
       first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >>
       `feval upfm σ0 (conj (n+1))`
         suffices_by
          (`n < n + 1` by fs[] >> metis_tac[fCONJ_imp_enum,Abbr`conj`]) >>
       metis_tac[])) >>
(*second suffices end*)
(*construction of Jn, which forms a decending chain, may need extract out, here choose forall instead of exists for the σ since there is no free var*)
qabbrev_tac
  `Jn = \n. {i | i IN (In 0) /\
                 (!σ.
                    (!k. k IN N ==> σ k = CHOICE (f k) i) ==>
                      feval (FMS i) σ (Exists x (conj n))
                 )}` >>
(*prove property of Jn*)
`!n. Jn (n + 1) ⊆ Jn n`
  by
   (rw[Abbr`Jn`,SUBSET_DEF] >> first_x_assum drule >> rw[] >>
    metis_tac[fCONJ_imp_fCONJ]) >>
`!phi. phi IN s ==> FV phi ⊆ N ∪ {x}`
  by
   (rw[] >> `FV phi DIFF N ⊆ {x}` by metis_tac[] >>
    rw[SUBSET_DEF,UNION_DEF] >> fs[DIFF_DEF,SUBSET_DEF] >> metis_tac[]) >>
`!n. FV (enum n) ⊆ N ∪ {x}`
  by fs[BIJ_DEF,SURJ_DEF] >>
`!n. FV (conj n) ⊆ N ∪ {x}`
  by metis_tac[fCONJ_FV] >>
`!n. (Jn n) IN U`
  by
   (rw[Abbr`Jn`] >>
    `FINITE {enum t | t < n} /\ {enum t | t < n} ⊆ s`
     by
      (rw[] (* 2 *)
       >- (`IMAGE enum (count n) = {enum t | t < n}`
            suffices_by metis_tac[IMAGE_FINITE,FINITE_COUNT] >>
           rw[IMAGE_DEF,EXTENSION])
       >- (fs[SUBSET_DEF,BIJ_DEF,INJ_DEF] >> metis_tac[])) >>
    first_x_assum drule >> first_x_assum drule >> rw[] >>
    first_x_assum (qspec_then `(fEXISTS x (conj n))` assume_tac) >>
    pop_assum (assume_tac o SYM) >>
    `feval upfm f (fEXISTS x (conj n))`
     by
      (rw[feval_def] >> qexists_tac `σ x` >> rw[] (* 2 *)
       >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
       >- (`(feval upfm f⦇x ↦ σ x⦈ (conj n) <=> feval upfm σ (conj n)) /\
            feval upfm σ (conj n)`
             suffices_by metis_tac[] >>
           rw[] (* 2 *)
           >- (irule holds_valuation >> rw[] >>
               `x' IN N \/ x' = x`
                by (fs[SUBSET_DEF,UNION_DEF] >> metis_tac[]) (* 2 same *) >>
               fs[APPLY_UPDATE_THM])
           >- (`(!t. t < n ==> feval upfm σ (enum t))
                 ==> feval upfm σ (conj n)` suffices_by metis_tac[] >>
               metis_tac[enum_imp_fCONJ])
          )
      ) >>
     (* by tactic for feval ends*)
    qmatch_abbrev_tac `BS IN U` >>
    `{i | i ∈ In 0 ∧
          feval (FMS i) (λx. CHOICE (f x) i) (fEXISTS x (conj n))} ⊆ BS`
     suffices_by
      (`BS ⊆ In 0` by fs[Abbr`BS`,SUBSET_DEF] >>
       metis_tac[ultrafilter_SUBSET']) >>
    rw[SUBSET_DEF,Abbr`BS`] >> qexists_tac `a` >> rw[] >>
    `!v. v IN FV (conj n) ==>
      (λx. CHOICE (f x) x')⦇x ↦ a⦈ v = σ'⦇x ↦ a⦈ v`
     suffices_by metis_tac[holds_valuation] >>
    rw[] >>
    `v IN N \/ v = x`
     by (fs[SUBSET_DEF,UNION_DEF] >> metis_tac[]) >> (*2 same*)
    fs[APPLY_UPDATE_THM]
   ) >>
(*by tac for Jn n IN U ends*)
qabbrev_tac
  `Xn = \n. (In n) ∩ (Jn n)` >>
(*begin with the construction of Xn*)
`!n. Xn n IN U`
  by
   (rw[Abbr`Xn`] >> metis_tac[ultrafilter_INTER]) >>
`(!n. Xn (n + 1) ⊆ Xn n) /\ BIGINTER {Xn n | n IN (univ(:num))} = {}`
  by
   (simp[Abbr`Xn`] >>
    `∀n. In (n + 1) ∩ Jn (n + 1) ⊆ In n ∩ Jn n ∧
         BIGINTER {In n ∩ Jn n | n ∈ 𝕌(:num)} = ∅`
     suffices_by rw[] >>
    irule two_chains_INTER >>
    rw[]) >>
(*cheated for the property of chains, not suppose to be hard need to fix FV
where is the cheat ...*)
`∃Ni. ∀i. i ∈ Xn 0 ⇒ i ∈ Xn (Ni i) ∧ ∀a. a > Ni i ⇒ i ∉ Xn a`
  by
   (irule chain_Ni_EXISTS >> metis_tac[]) >>
`Jn 0 = In 0`
  by
   (rw[EXTENSION,EQ_IMP_THM,Abbr`Jn`,Abbr`conj`,
       True_def,fNOT_def,fCONJ_def,feval_def,PRIM_REC_THM] >>
    metis_tac[]) >>
`Xn 0 = In 0`
  by rw[Abbr`Xn`] >>
(*the above get the function n(i) in the paper*)
qabbrev_tac
`σr =(\v i. if (v IN N)
        then (CHOICE (f v) i)
       else
       (CHOICE
               {a | a IN (FMS i).Dom /\
                    feval (FMS i)
                          (\n. if n IN N then ((CHOICE (f n)) i)
                               else a)
                    (conj (Ni i))}))` >>
qexists_tac `σr` >>
`!i. i IN In 0 ==> {a | a ∈ (FMS i).Dom ∧
          feval (FMS i) (λn. if n ∈ N then CHOICE (f n) i else a)
          (conj (Ni i))} <> {}`
  by
   (rw[GSYM MEMBER_NOT_EMPTY] >>
    `∀σ. (∀k. k ∈ N ⇒ σ k = CHOICE (f k) i) ⇒
          feval (FMS i) σ (fEXISTS x (conj (Ni i)))`
     by
      (`i IN (Xn (Ni i))` by metis_tac[] >>
       `i IN (Jn (Ni i))` by fs[Abbr`Xn`] >>
       fs[Abbr`Jn`]) >>
    fs[] >>
    first_x_assum (qspec_then `\n. CHOICE (f n) i` assume_tac) >>
    (*specialize with the "canonical" function*)
    fs[] >> qexists_tac `a` >> rw[] >>
    `feval (FMS i) (λn. CHOICE (f n) i)⦇x ↦ a⦈ (conj (Ni i)) <=>
     feval (FMS i) (λn. if n ∈ N then CHOICE (f n) i else a) (conj (Ni i))`
      suffices_by metis_tac[] >>
    irule holds_valuation >> strip_tac >>
    rw[] (* 2 *)
    >- (fs[APPLY_UPDATE_THM] >>
       `x <> x'` by metis_tac[] >> rw[])
    >- (`x' = x`
         by (fs[SUBSET_DEF] >> metis_tac[]) >>
        rw[APPLY_UPDATE_THM])
    ) >>
`∀v i. i ∈ In 0 ⇒ σr v i ∈ (FMS i).Dom`
  by
   (`!v. CHOICE (f v) IN (f v)`
     by
      (`!v. (f v) <> {}` suffices_by metis_tac[CHOICE_DEF] >> rw[] >>
       fs[IMAGE_DEF,SUBSET_DEF] >>
       metis_tac[ultraproduct_eqclass_non_empty]) >>
    `!g v. g IN (f v) ==> (!i. i IN In 0 ==> (g i) IN (FMS i).Dom)`
     by
      (rw[] >>
       `f v IN (ultraproduct U (In 0) (folmodels2Doms FMS))`
         by (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
       `f v IN (partition (Uequiv U (In 0) (folmodels2Doms FMS))
               (Cart_prod (In 0) (folmodels2Doms FMS)))`
         by fs[ultraproduct_def] >>
       fs[partition_def,Cart_prod_def,folmodels2Doms_def] >>
       `g IN {y | (∀i. i ∈ In 0 ⇒ y i ∈ (FMS i).Dom) ∧
                   Uequiv U (In 0) (λi. (FMS i).Dom) x' y}` by metis_tac[] >>
       fs[]) >>
    rw[Abbr`σr`] (* 2 *)
    >- metis_tac[] >>
    qmatch_abbrev_tac `CHOICE bs IN (FMS i).Dom` >>
    `bs <> {}` by fs[Abbr`bs`] >>
    `!a. a IN bs ==> a IN (FMS i).Dom` by fs[Abbr`bs`] >>
    metis_tac[CHOICE_DEF]) >>
(*one of 3 subgoals solved, just do not want to strip it*)
`∀n. n ∈ N ⇒
      {g | Uequiv U (In 0) (folmodels2Doms FMS) g (σr n)} = f n`
  by
   (rw[Abbr`σr`] >> `(λi. CHOICE (f n) i) = CHOICE (f n)` by fs[FUN_EQ_THM] >>
    rw[] >> drule eqc_CHOICE >> strip_tac >>
    first_x_assum (qspecl_then [`(folmodels2Doms FMS)`,`f n`] assume_tac) >>
    `f n ∈ ultraproduct U (In 0) (folmodels2Doms FMS)`
      suffices_by metis_tac[] >>
    fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]) >>
rw[] >>
(*last most subtle subgoal*)
qmatch_abbrev_tac `bs IN U` >>
`(Xn k) ⊆ bs`
  suffices_by
   (`bs ⊆ In 0` by fs[Abbr`bs`,SUBSET_DEF] >> rw[] >>
    irule ultrafilter_SUBSET' >> rw[] (* 2 same *)
    >> metis_tac[]) >>
`!i. i IN (Xn k) ==> feval (FMS i) (λv. σr v i) (conj k)`
  suffices_by rw[Abbr`bs`,Abbr`Xn`,Abbr`Jn`,SUBSET_DEF] >>
rpt strip_tac >>
`k <= Ni i`
  by
   (SPOSE_NOT_THEN ASSUME_TAC >>
    `k > Ni i` by fs[] >>
    `i IN Xn 0` suffices_by metis_tac[] >>
    `0 <= k` by fs[] >>
    `Xn k ⊆ Xn 0` by metis_tac[chain_TRANS] >>
    metis_tac[SUBSET_DEF]) >>
(*need trans feval lemma of conj cheated!*)
`feval (FMS i) (λv. σr v i) (conj (Ni i))`
  suffices_by metis_tac[fCONJ_imp_fCONJ_LE] >>
rw[Abbr`σr`] >>
`CHOICE
   {a | a ∈ (FMS i).Dom ∧
        feval (FMS i) (λn. if n ∈ N then CHOICE (f n) i else a)
                      (conj (Ni i))} IN
   {a | a ∈ (FMS i).Dom ∧
        feval (FMS i) (λn. if n ∈ N then CHOICE (f n) i else a)
                      (conj (Ni i))}` suffices_by rw[] >>
`0 <= k` by fs[] >>
`Xn k ⊆ Xn 0` by metis_tac[chain_TRANS] >>
`i IN Xn 0` by metis_tac[SUBSET_DEF] >>
metis_tac[CHOICE_DEF]
QED

Theorem ultraproduct_sat:
!U I FMS x. countably_incomplete U I ==>
   !f. IMAGE f (univ(:num)) ⊆ ultraproduct U I (folmodels2Doms FMS) ==>
   (∀i ff ll. i ∈ I ⇒ (FMS i).Fun ff ll ∈ (FMS i).Dom) ==>
  !s. (!phi. phi IN s ==> form_functions phi = {} /\ (FV phi) DIFF N ⊆ {x}) ==>
       (!ss. FINITE ss /\ ss ⊆ s ==>
          ?σ. (IMAGE σ (univ(:num)) ⊆ (ultraproduct_folmodel U I FMS).Dom) /\
              (!n. n IN N ==> σ n = f n) /\
              (!phi. phi IN ss ==> feval (ultraproduct_folmodel U I FMS) σ phi)) ==>
       (?σ. (IMAGE σ (univ(:num)) ⊆ (ultraproduct_folmodel U I FMS).Dom) /\
            (!n. n IN N ==> σ n = f n)  /\
            (!phi. phi IN s ==> feval (ultraproduct_folmodel U I FMS) σ phi))
Proof
rw[] >> Cases_on `x IN N`
>- (irule ultraproduct_sat_case2 >> rw[] >> metis_tac[]) >>
irule ultraproduct_sat_case1 >> rw[] >> metis_tac[]
QED



Theorem ultraproduct_sat':
!U I MS x N f. countably_incomplete U I ==>
     (!i. i IN I ==> (MS i).frame.world <> {}) ==>
     (IMAGE f 𝕌(:num) ⊆ ultraproduct U I (models2worlds MS)) ==>
  !s. (!phi. phi IN s ==> form_functions phi = {} /\ (FV phi) DIFF N ⊆ {x}) ==>
       (!ss. FINITE ss /\ ss ⊆ s ==>
          ?σ. (IMAGE σ (univ(:num)) ⊆ (mm2folm (ultraproduct_model U I MS)).Dom) /\
              (!n. n IN N ==> σ n = f n) /\
              (!phi. phi IN ss ==> feval (mm2folm (ultraproduct_model U I MS)) σ phi)) ==>
      (?σ. (IMAGE σ (univ(:num)) ⊆ (mm2folm (ultraproduct_model U I MS)).Dom) /\
           (!n. n IN N ==> σ n = f n)  /\
           (!phi. phi IN s ==> feval (mm2folm (ultraproduct_model U I MS)) σ phi))
Proof
rw[] >> FREEZE_THEN drule ultraproduct_sat >> rw[] >>
fs[countably_incomplete_def] >>
drule ultraproduct_comm_feval >> rw[] >>
`∃σ. IMAGE σ 𝕌(:num) ⊆ (mm2folm (ultraproduct_model U I' MS)).Dom ∧
     (∀n. n ∈ N ⇒ σ n = f n) ∧
     ∀phi.
        phi ∈ s ⇒ feval (ultraproduct_folmodel U I' (λi. mm2folm (MS i))) σ phi`
  suffices_by
   (rw[] >> qexists_tac `σ` >> rw[] >>
    `(mm2folm (ultraproduct_model U I' MS)).Dom =
     ultraproduct U I' (models2worlds MS)`
     by rw[mm2folm_def,ultraproduct_model_def] >>
    first_x_assum drule >> metis_tac[]) >>
first_x_assum (qspecl_then [`λi. mm2folm (MS i)`,`x`,`f`,`s`] assume_tac) >>
`(ultraproduct_folmodel U I' (λi. mm2folm (MS i))).Dom =
(mm2folm (ultraproduct_model U I' MS)).Dom`
 by metis_tac[ultraproduct_comm_Dom] >> fs[] >>
first_x_assum irule >> rw[] (* 3 *)
>- metis_tac[mm2folm_well_formed]
>- (first_x_assum drule >> rw[] >> qexists_tac `σ` >> rw[] >>
    `phi IN s` by fs[SUBSET_DEF] >>
    `form_functions phi = ∅` by metis_tac[] >>
    first_x_assum drule >>
    `ultraproduct U I' (models2worlds MS) =
     (mm2folm (ultraproduct_model U I' MS)).Dom`
     by rw[ultraproduct_model_def,mm2folm_def] >> metis_tac[]) >>
`models2worlds MS = folmodels2Doms (λi. mm2folm (MS i))`
  suffices_by metis_tac[] >>
rw[FUN_EQ_THM,models2worlds_def,folmodels2Doms_def,mm2folm_def]
QED



Theorem FCT_term_functions:
!t. FCT t ⊆ {FST c | c IN (term_functions t)}
Proof
completeInduct_on `term_size t` >> Cases_on `t` >> rw[FCT_def,term_functions_def]>>
rw[SUBSET_DEF] >> fs[MEM_MAP,PULL_FORALL] >>
first_x_assum (qspec_then `a` assume_tac) >> drule term_size_lemma >>
strip_tac >> `term_size a < n + (term1_size l + 1)` by fs[ADD_CLAUSES] >> fs[] >>
rw[] >> fs[SUBSET_DEF] >> first_x_assum drule >> rw[PULL_EXISTS] >>
qexists_tac `c` >> rw[] >> metis_tac[]
QED

Theorem FC_form_functions:
!phi. FC phi ⊆ {FST c | c IN (form_functions phi)}
Proof
Induct_on `phi` >> rw[FC_def,form_functions_def] (* 3 *)
>- (rw[SUBSET_DEF,MEM_MAP,PULL_EXISTS] >>
    `FCT y ⊆ {FST c | c IN (term_functions y)}` by metis_tac[FCT_term_functions]>>
    fs[SUBSET_DEF] >> metis_tac[]) >>
fs[SUBSET_DEF] >> metis_tac[]
QED


Theorem ultraproduct_sat'':
!U I MS x. countably_incomplete U I ==>
       (∀i. i ∈ I ⇒ (MS i).frame.world ≠ ∅) ⇒
   !A f. BIJ f (count (CARD A)) A ==>
           IMAGE f 𝕌(:num) ⊆ ultraproduct U I (models2worlds MS) ==>
  !s. (!phi. phi IN s ==>  (∀c. c ∈ form_functions phi ⇒ FST c ∈ count (CARD A) ∧ SND c = 0)
           /\ FV phi ⊆ {x}) ==>
       (!ss. FINITE ss /\ ss ⊆ s ==>
          ?σ. (IMAGE σ (univ(:num)) ⊆ (mm2folm (ultraproduct_model U I MS)).Dom) /\
              (!phi. phi IN ss ==> feval (expand (mm2folm (ultraproduct_model U I MS)) A f) σ phi)) ==>
      (?σ. (IMAGE σ (univ(:num)) ⊆ (mm2folm (ultraproduct_model U I MS)).Dom) /\
           (!phi. phi IN s ==> feval (expand (mm2folm (ultraproduct_model U I MS)) A f) σ phi))
Proof
rw[] >> drule ultraproduct_sat' >> rw[] >>
drule expansion_shift_feval >> rw[] >>
qabbrev_tac `sfs = {shift_form (CARD A) phi | phi IN s}` >>
`!phi. phi IN sfs ==> form_functions phi = ∅ ∧ (FV phi) DIFF (count (CARD A)) ⊆ {x + CARD A}`
  by (* cheat *)
   (rw[] (* 2 *)
    >- (fs[Abbr`sfs`] >> irule shift_form_functions_EMPTY >>
        rw[count_def] >> (*2 same*) metis_tac[])
    >- (fs[Abbr`sfs`] >> `FV phi' ⊆ {x}` by metis_tac[] >>
        FREEZE_THEN drule
          (shift_FV |> INST_TYPE [alpha |-> ``:('a -> 'b) -> bool``]) >>
        rw[] >> `{x' + CARD A | x' = x} = {x + CARD A}` by fs[EXTENSION] >>
        fs[] >> first_x_assum irule >> metis_tac[])) >>
first_x_assum
   (qspecl_then
   [`MS`,`x + CARD A`,`count (CARD A)`,`f`,`sfs`] assume_tac) >>
`∃σ.
   IMAGE σ 𝕌(:num) ⊆ (mm2folm (ultraproduct_model U I' MS)).Dom ∧
   (∀n. n ∈ count (CARD A) ⇒ σ n = f n) ∧
   ∀phi.
       phi ∈ sfs ⇒
          feval (mm2folm (ultraproduct_model U I' MS)) σ phi`
  suffices_by
   (rw[] >>
    (* suffices within suffices*)
    `∃σ.
       IMAGE σ 𝕌(:num) ⊆ (mm2folm (ultraproduct_model U I' MS)).Dom ∧
       ∀phi. phi ∈ s ⇒
             feval (mm2folm (ultraproduct_model U I' MS))
               (shift_valuation (CARD A) σ f) (shift_form (CARD A) phi)`
      suffices_by
       (rw[] >> qexists_tac `σ'` >> rw[] >>
        first_x_assum (qspec_then `phi` assume_tac) >> rfs[] >>
        first_x_assum (qspecl_then [`(ultraproduct_model U I' MS)`,`phi`,`σ'`] assume_tac) >>
        `feval (expand (mm2folm (ultraproduct_model U I' MS)) A f) σ' phi ⇔
         feval (mm2folm (ultraproduct_model U I' MS))
           (shift_valuation (CARD A) σ' f) (shift_form (CARD A) phi)`
          suffices_by metis_tac[] >>
        first_x_assum irule >> rw[] (* 2 *)
        >- (`!phi. FC phi ⊆ {FST c | c IN (form_functions phi)}`
             suffices_by (rw[SUBSET_DEF] >> metis_tac[]) >>
            metis_tac[FC_form_functions])
        >- fs[mm2folm_def]) >>
    (*suffices within suffices end*)
    qexists_tac `\n. σ ((CARD A) + n)` >> rw[] (* 2 *)
    >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
    >- (first_x_assum (qspec_then `(shift_form (CARD A) phi)` assume_tac) >>
        `shift_form (CARD A) phi ∈ sfs`
         by (rw[Abbr`sfs`] >> metis_tac[]) >>
        first_x_assum drule >> rw[] >>
        `(shift_valuation (CARD A) (λn. σ (n + CARD A)) f) = σ`
          suffices_by metis_tac[] >>
        rw[FUN_EQ_THM,shift_valuation_def] >> Cases_on `x' < CARD A` >> rw[])) >>
   (* big suffices tac end *)
first_x_assum irule >> fs[] >> rw[] >>
`?s0. s0 ⊆ s /\ FINITE s0 /\ ss = IMAGE (shift_form (CARD A)) s0`
 by
  (fs[SUBSET_DEF,Abbr`sfs`] >>
   qexists_tac
     `{CHOICE {phi | phi IN s /\ x = shift_form (CARD A) phi} | x IN ss}` >>
   rw[] (* 3 *)
   >- (`CHOICE {phi | phi ∈ s ∧ x'' = shift_form (CARD A) phi} ∈
        {phi | phi ∈ s ∧ x'' = shift_form (CARD A) phi}`
         suffices_by fs[] >>
       `{phi | phi ∈ s ∧ x'' = shift_form (CARD A) phi} <> {}`
         suffices_by metis_tac[CHOICE_DEF] >>
       rw[GSYM MEMBER_NOT_EMPTY] >> metis_tac[])
   >- (`{CHOICE {phi | phi ∈ s ∧ x = shift_form (CARD A) phi} | x ∈ ss} =
        IMAGE CHOICE
        {{phi | phi ∈ s ∧ x = shift_form (CARD A) phi} | x ∈ ss} /\
        FINITE {{phi | phi ∈ s ∧ x = shift_form (CARD A) phi} | x ∈ ss}`
        suffices_by metis_tac[IMAGE_FINITE] >> rw[] (* 2 *)
       >- rw[IMAGE_DEF,Once EXTENSION,EQ_IMP_THM,PULL_EXISTS,PULL_FORALL]
       >- (`{{phi | phi ∈ s ∧ x = shift_form (CARD A) phi} | x ∈ ss} =
            IMAGE (\x. {phi | phi ∈ s ∧ x = shift_form (CARD A) phi}) ss`
            suffices_by metis_tac[IMAGE_FINITE] >>
           rw[IMAGE_DEF,Once EXTENSION,EQ_IMP_THM,PULL_EXISTS,PULL_FORALL]))
   >- (rw[IMAGE_DEF,Once EXTENSION,EQ_IMP_THM,PULL_EXISTS,PULL_FORALL] (* 2 *)
      >- (qexists_tac `x'` >> rw[] >>
          `CHOICE {phi | phi ∈ s ∧ x' = shift_form (CARD A) phi} ∈
           {phi | phi ∈ s ∧ x' = shift_form (CARD A) phi}`
            suffices_by fs[] >>
          `{phi | phi ∈ s ∧ x' = shift_form (CARD A) phi} <> {}`
            suffices_by metis_tac[CHOICE_DEF] >>
          rw[GSYM MEMBER_NOT_EMPTY] >> metis_tac[])
      >- (`CHOICE {phi | phi ∈ s ∧ x'' = shift_form (CARD A) phi} ∈
           {phi | phi ∈ s ∧ x'' = shift_form (CARD A) phi}`
            suffices_by (fs[] >> metis_tac[]) >>
          `{phi | phi ∈ s ∧ x'' = shift_form (CARD A) phi} <> {}`
            suffices_by metis_tac[CHOICE_DEF] >>
          rw[GSYM MEMBER_NOT_EMPTY] >> metis_tac[]))) >>
first_x_assum (qspec_then `s0` assume_tac) >> rfs[] >>
qexists_tac `shift_valuation (CARD A) σ f` >> rw[] (* 3 *)
>- (fs[SUBSET_DEF,IMAGE_DEF,shift_valuation_def,
   mm2folm_def,ultraproduct_model_def] >> metis_tac[])
>- rw[shift_valuation_def]
>- (`(∀c. c ∈ FC x' ⇒ c < CARD A) ∧
     IMAGE σ 𝕌(:num) ⊆ (ultraproduct_model U I' MS).frame.world`
     suffices_by metis_tac[] >>
    `(ultraproduct_model U I' MS).frame.world =
     (mm2folm (ultraproduct_model U I' MS)).Dom` by fs[mm2folm_def] >>
    rw[] >>
    `FC x' ⊆ {FST c | c ∈ form_functions x'}`
      by metis_tac[FC_form_functions] >>
    fs[SUBSET_DEF] >> metis_tac[])
QED


Theorem lemma_2_73:
  !U I MS.
        ((!i. i IN I ==> (MS i).frame.world <> {}) /\
         countably_incomplete U I) ==>
             countably_saturated (mm2folm (ultraproduct_model U I MS))
Proof
rw[countably_saturated_def,n_saturated_def,
consistent_def,ftype_def,frealizes_def] >>
drule ultraproduct_sat'' (*cheated key theorem*)>> rw[] >>
first_x_assum drule >> rw[] >>
`∃σ. IMAGE σ 𝕌(:num) ⊆ (mm2folm (ultraproduct_model U I' MS)).Dom ∧
     ∀phi. phi ∈ G ⇒ feval (expand (mm2folm (ultraproduct_model U I' MS)) A f) σ phi`
 suffices_by
  (rw[] >> qexists_tac `σ x` >> rw[] (* 2 *)
   >- (`(mm2folm (ultraproduct_model U I' MS)).Dom = (expand (mm2folm (ultraproduct_model U I' MS)) A f).Dom`
        by fs[expand_def] >>
       fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
   >- (rw[fsatis_def] (* 2 *)
      >- (rw[valuation_def] >> Cases_on `n' = x` >> rw[APPLY_UPDATE_THM] (* 2 *)
          >- (`(mm2folm (ultraproduct_model U I' MS)).Dom = (expand (mm2folm (ultraproduct_model U I' MS)) A f).Dom`
               by fs[expand_def] >>
              fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[])
          >- (fs[IMAGE_DEF,SUBSET_DEF] >> metis_tac[]))
      >- (`feval (expand (mm2folm (ultraproduct_model U I' MS)) A f) σ phi <=>
           feval (expand (mm2folm (ultraproduct_model U I' MS)) A f) σ'⦇x ↦ σ x⦈ phi` suffices_by metis_tac[] >>
          irule holds_valuation >>
          `FV phi ⊆ {x}` by (fs[SUBSET_DEF] >> metis_tac[]) >>
          fs[SUBSET_DEF,APPLY_UPDATE_THM]))) >>
  (*suffices tactic end*)
first_x_assum irule >>
`(mm2folm (ultraproduct_model U I' MS)).Dom = (expand (mm2folm (ultraproduct_model U I' MS)) A f).Dom`
  by fs[expand_def] >> rw[] >>
fs[fsatis_def] (* 3 *)
>- (qexists_tac `x` >> rw[] (* 3 *)
    >- (fs[SUBSET_DEF] >>
       `∃k. c = (k,0) ∧ k < CARD A` by metis_tac[] >> fs[])
    >- (fs[SUBSET_DEF] >>
       `∃k. c = (k,0) ∧ k < CARD A` by metis_tac[] >> fs[])
    >- (fs[SUBSET_DEF] >> metis_tac[]))
>- metis_tac[]
>- fs[IMAGE_DEF,SUBSET_DEF,expand_def,mm2folm_def,ultraproduct_model_def]
QED

val _ = export_theory();
