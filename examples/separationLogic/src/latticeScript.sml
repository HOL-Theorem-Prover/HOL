open HolKernel Parse boolLib bossLib;

(*
quietdec := true;
loadPath := 
            (Globals.HOLDIR ^ "/examples/separationLogic/src") :: 
            !loadPath;

map load ["relationTheory", "pred_setTheory", "operatorTheory"];
show_assums := true;
*)

open relationTheory pred_setTheory operatorTheory optionTheory;

(*
quietdec := false;
*)

val _ = new_theory "lattice";

val OPTION_SELECT_def = Define 
   `OPTION_SELECT P = if ~(?x. P x) then NONE else SOME @x. P x`

val OPTION_SELECT_THM = store_thm ("OPTION_SELECT_THM",
   ``(!P. ((OPTION_SELECT P = NONE) = (!x. ~(P x)))) /\
     (!P. (IS_SOME (OPTION_SELECT P) = (?x. P x))) /\
     (!P s. ((OPTION_SELECT P = SOME s) = 
         (?x. P x) /\ (s = @x. P x)))``,

SIMP_TAC std_ss [OPTION_SELECT_def, COND_RAND, COND_RATOR] THEN
METIS_TAC[]);


val OPTION_SELECT_IMP = store_thm ("OPTION_SELECT_IMP",
``(!P x. ((OPTION_SELECT P = (SOME x)) ==> (P x)))``,

SIMP_TAC std_ss [OPTION_SELECT_def, COND_RAND, COND_RATOR] THEN
REPEAT STRIP_TAC THEN
SELECT_ELIM_TAC THEN
METIS_TAC[]);

val rest_reflexive_def = Define `
   rest_reflexive M R = !x. x IN M ==> R x x`

val rest_antisymmetric_def = Define `
   rest_antisymmetric M R = !x y. (x IN M /\ y IN M /\ R x y /\ R y x) ==> (x = y)`

val rest_transitive_def = Define `
   rest_transitive M R = !x y z. (x IN M /\ y IN M /\ z IN M /\ R x y /\ R y z) ==> (R x z)`

val rest_WeakOrder_def = Define `
   rest_WeakOrder M R = rest_reflexive M R /\ rest_antisymmetric M R /\ rest_transitive M R`


val rest_WeakOrder_THM = store_thm ("rest_WeakOrder_THM",

``(!M R. 
   (rest_antisymmetric M (inv R) = rest_antisymmetric M R) /\
   (rest_reflexive M (inv R) = rest_reflexive M R) /\
   (rest_transitive M (inv R) = rest_transitive M R) /\
   (rest_WeakOrder M (inv R) = rest_WeakOrder M R) /\

   (rest_reflexive UNIV R = reflexive R) /\
   (rest_antisymmetric UNIV R = antisymmetric R) /\
   (rest_transitive UNIV R = transitive R) /\
   (rest_WeakOrder UNIV R = WeakOrder R) /\

   (WeakOrder R ==> rest_WeakOrder M R)) /\

   (!R M1 M2. M1 SUBSET M2 ==> (
      (rest_reflexive M2 R ==> rest_reflexive M1 R) /\
      (rest_antisymmetric M2 R ==> rest_antisymmetric M1 R) /\
      (rest_transitive M2 R ==> rest_transitive M1 R) /\
      (rest_WeakOrder M2 R ==> rest_WeakOrder M1 R)))``,


REWRITE_TAC [rest_reflexive_def, SUBSET_DEF, IN_UNIV, reflexive_def,
   rest_antisymmetric_def, IMP_CONJ_THM, FORALL_AND_THM, 
   antisymmetric_def, rest_transitive_def, transitive_def, rest_WeakOrder_def,
   WeakOrder, inv_DEF] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN METIS_TAC[]);




val IS_UPPER_BOUND_def = Define `
   IS_UPPER_BOUND f D M b = ((b IN D) /\ !m. m IN M ==> f m b)`;

val IS_SUPREMUM_def = Define `
   IS_SUPREMUM f D M s = 
   (IS_UPPER_BOUND f D M s) /\
   (!b. IS_UPPER_BOUND f D M b ==> (f s b))`;

val BIGSUP_def = Define `
   (BIGSUP f D M) = OPTION_SELECT (\s. IS_SUPREMUM f D M s)`

val SUP_def = Define `
   SUP f D a b = BIGSUP f D {a; b}`

val IS_LOWER_BOUND_def = Define `
   IS_LOWER_BOUND f D M b = ((b IN D) /\ !m. m IN M ==> f b m)`;

val IS_INFIMUM_def = Define `
   IS_INFIMUM f D M s = 
   (IS_LOWER_BOUND f D M s) /\
   (!b. IS_LOWER_BOUND f D M b ==> (f b s))`;


val BIGINF_def = Define `
   (BIGINF f D M) = OPTION_SELECT (\s. IS_INFIMUM f D M s)`

val INF_def = Define `
   INF f D a b = BIGINF f D {a; b}`


val INF_SUP_inv_THM___1 = prove (
   ``IS_UPPER_BOUND (inv f) = IS_LOWER_BOUND f``,
   SIMP_TAC std_ss [IS_LOWER_BOUND_def, IS_UPPER_BOUND_def, FUN_EQ_THM, inv_DEF])

val INF_SUP_inv_THM___2 = prove (
   ``IS_SUPREMUM (inv f) = IS_INFIMUM f``,
   SIMP_TAC std_ss [FUN_EQ_THM, IS_SUPREMUM_def, IS_INFIMUM_def, INF_SUP_inv_THM___1, inv_DEF]);

val INF_SUP_inv_THM___3 = prove (
   ``BIGSUP (inv f) = BIGINF f``,
   SIMP_TAC std_ss [FUN_EQ_THM, BIGSUP_def, BIGINF_def, INF_SUP_inv_THM___2, inv_DEF]);

val INF_SUP_inv_THM___4 = prove (
   ``SUP (inv f) = INF f``,
   SIMP_TAC std_ss [FUN_EQ_THM, SUP_def, INF_def, INF_SUP_inv_THM___3]);


val INF_SUP_inv_THM = store_thm ("INF_SUP_inv_THM",

``(IS_UPPER_BOUND (inv f) = IS_LOWER_BOUND f) /\
  (IS_LOWER_BOUND (inv f) = IS_UPPER_BOUND f) /\
  (IS_SUPREMUM (inv f) = IS_INFIMUM f) /\
  (IS_INFIMUM (inv f) = IS_SUPREMUM f) /\
  (BIGSUP (inv f) = BIGINF f) /\
  (BIGINF (inv f) = BIGSUP f) /\
  (SUP (inv f) = INF f) /\
  (INF (inv f) = SUP f)``,

PROVE_TAC [inv_inv, INF_SUP_inv_THM___1, INF_SUP_inv_THM___2, INF_SUP_inv_THM___3, INF_SUP_inv_THM___4]);



   
val IS_SUPREMUM_UNIQUE_THM = store_thm ("IS_SUPREMUM_UNIQUE_THM",
``!D f a b M. (rest_antisymmetric D f /\ IS_SUPREMUM f D M a /\ IS_SUPREMUM f D M b) ==> (a = b)``,
SIMP_TAC std_ss [IS_SUPREMUM_def, rest_antisymmetric_def, IS_UPPER_BOUND_def]);

val IS_INFIMUM_UNIQUE_THM = store_thm ("IS_INFIMUM_UNIQUE_THM",
``!D f a b M. (rest_antisymmetric D f /\ IS_INFIMUM f D M a /\ IS_INFIMUM f D M b) ==> (a = b)``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC (Q.SPECL [`D`, `inv f`, `a`, `b`, `M`] IS_SUPREMUM_UNIQUE_THM) THEN
ASM_SIMP_TAC std_ss [rest_WeakOrder_THM, INF_SUP_inv_THM])


val BIGSUP_THM = store_thm ("BIGSUP_THM",
   ``(!D f s M. (rest_antisymmetric D f /\ IS_SUPREMUM f D M s) ==> (BIGSUP f D M = (SOME s)))``,

SIMP_TAC std_ss [BIGSUP_def, OPTION_SELECT_def] THEN
REPEAT STRIP_TAC THEN1 PROVE_TAC[] THEN
SELECT_ELIM_TAC THEN
METIS_TAC[IS_SUPREMUM_UNIQUE_THM]);


val BIGINF_THM = store_thm ("BIGINF_THM",
   ``!D f s M. (rest_antisymmetric D f /\ IS_INFIMUM f D M s) ==> (BIGINF f D M = (SOME s))``,

PROVE_TAC [BIGSUP_THM, INF_SUP_inv_THM, rest_WeakOrder_THM]);



val INF_REWRITE = save_thm ("INF_REWRITE",
   SIMP_RULE std_ss [BIGINF_def, IS_INFIMUM_def, 
      IS_LOWER_BOUND_def, IN_INSERT, NOT_IN_EMPTY,
      DISJ_IMP_THM, FORALL_AND_THM] INF_def);

val SUP_REWRITE = save_thm ("SUP_REWRITE",
   SIMP_RULE std_ss [BIGSUP_def, IS_SUPREMUM_def, 
      IS_UPPER_BOUND_def, IN_INSERT, NOT_IN_EMPTY,
      DISJ_IMP_THM, FORALL_AND_THM] SUP_def);



val IS_LATTICE_def = Define `
   IS_LATTICE f D = rest_WeakOrder D f /\
                    (!x y. (x IN D /\ y IN D) ==> (IS_SOME (INF f D x y) /\ IS_SOME (SUP f D x y)))`


val IS_COMPLETE_LATTICE_def = Define `
   IS_COMPLETE_LATTICE f D = rest_WeakOrder D f /\
                    (!M. (~(M = EMPTY) /\ (M SUBSET D)) ==> (IS_SOME (BIGINF f D M) /\ IS_SOME (BIGSUP f D M)))`


val COMPLETE_LATTICE___IS_LATTICE = store_thm ("COMPLETE_LATTICE___IS_LATTICE",

   ``!D f. (IS_COMPLETE_LATTICE f D ==> IS_LATTICE f D)``,

   SIMP_TAC std_ss [IS_COMPLETE_LATTICE_def, IS_LATTICE_def, INF_def, SUP_def] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   Q.PAT_ASSUM `!M. P M` (MP_TAC o Q.SPEC `{x;y}`) THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT, NOT_IN_EMPTY, DISJ_IMP_THM, FORALL_AND_THM,
      NOT_EMPTY_INSERT]);




val BIGUNION_IS_SUPREMUM = store_thm ("BIGUNION_IS_SUPREMUM",
``!s D M. 
BIGUNION M IN D ==>
(IS_SUPREMUM $SUBSET D M s = ((s = BIGUNION M)))``,

SIMP_TAC std_ss [IS_SUPREMUM_def, IS_UPPER_BOUND_def, EXTENSION, IN_BIGUNION, SUBSET_DEF] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
   ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THENL [
      STRIP_TAC THEN
      Q.PAT_ASSUM `!y. P y ==> Q y` MP_TAC THEN
      SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
      Q.EXISTS_TAC `BIGUNION M` THEN
      ASM_SIMP_TAC std_ss [IN_BIGUNION, GSYM RIGHT_FORALL_IMP_THM,
         GSYM RIGHT_EXISTS_IMP_THM, AND_IMP_INTRO] THEN
      METIS_TAC[],

      METIS_TAC[]
   ],

   REPEAT STRIP_TAC THENL [
      `s = BIGUNION M` by ALL_TAC THEN1 (
         FULL_SIMP_TAC std_ss [EXTENSION, IN_BIGUNION] THEN
         METIS_TAC[]
      ) THEN
      ASM_REWRITE_TAC[],

      METIS_TAC[],
      METIS_TAC[]
   ]
]);





val BIGINTER_IS_INFIMUM = store_thm ("BIGINTER_IS_INFIMUM",
``!s M D. (BIGINTER M IN D) ==>
(IS_INFIMUM $SUBSET D M s = (s = BIGINTER M))``,


SIMP_TAC std_ss [IS_INFIMUM_def, IS_LOWER_BOUND_def] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
   SIMP_TAC std_ss [EXTENSION, IN_BIGINTER] THEN
   REPEAT GEN_TAC THEN EQ_TAC THENL [
      METIS_TAC[SUBSET_DEF],

      STRIP_TAC THEN
      Cases_on `M = EMPTY` THEN1 (
         FULL_SIMP_TAC std_ss [NOT_IN_EMPTY, BIGINTER_EMPTY] THEN
         `UNIV SUBSET s` by METIS_TAC[] THEN
         FULL_SIMP_TAC std_ss [UNIV_SUBSET, IN_UNIV]
      ) THEN
      `?P. P IN M` by METIS_TAC[MEMBER_NOT_EMPTY] THEN
      `x IN P` by METIS_TAC[] THEN

      Q.PAT_ASSUM `!y. (b IN D) /\ (!m. X m y) ==> Q y` MP_TAC THEN
      SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
      Q.EXISTS_TAC `BIGINTER M` THEN
      ASM_SIMP_TAC std_ss [IN_BIGINTER, GSYM RIGHT_FORALL_IMP_THM,
         GSYM RIGHT_EXISTS_IMP_THM, AND_IMP_INTRO, SUBSET_DEF]
   ],

   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGINTER]
]);




val IS_COMPLETE_LATTICE___POWERSET_SUBSET = store_thm ("IS_COMPLETE_LATTICE___POWERSET_SUBSET",
``!D. IS_COMPLETE_LATTICE $SUBSET (POW D)``,


REWRITE_TAC [IS_COMPLETE_LATTICE_def, SUBSET_UNIV, BIGINF_def,
   BIGSUP_def, OPTION_SELECT_THM, IN_UNIV, rest_WeakOrder_def,
   rest_reflexive_def, rest_antisymmetric_def, rest_transitive_def,
   SUBSET_REFL] THEN
REPEAT STRIP_TAC THENL [
   ASM_SIMP_TAC std_ss [SUBSET_ANTISYM],
   METIS_TAC [SUBSET_TRANS],

   `BIGINTER M IN POW D` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF,
         IN_BIGINTER, GSYM MEMBER_NOT_EMPTY] THEN      
      METIS_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [BIGINTER_IS_INFIMUM, IN_POW, SUBSET_DEF,
      IN_BIGINTER, GSYM MEMBER_NOT_EMPTY],

   `BIGUNION M IN POW D` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [IN_POW, SUBSET_DEF,
         IN_BIGUNION, GSYM MEMBER_NOT_EMPTY] THEN      
      METIS_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [BIGUNION_IS_SUPREMUM, IN_POW, SUBSET_DEF,
      IN_BIGUNION, GSYM MEMBER_NOT_EMPTY]
]);


val IS_COMPLETE_LATTICE___ALTERNATIVE_DEF_1 = prove (
``IS_COMPLETE_LATTICE f EMPTY``,

SIMP_TAC std_ss [IS_COMPLETE_LATTICE_def, SUBSET_EMPTY,
rest_WeakOrder_def, rest_reflexive_def, NOT_IN_EMPTY,
rest_antisymmetric_def, rest_transitive_def]);


val IS_COMPLETE_LATTICE___ALTERNATIVE_DEF_2 = prove (
``(IS_COMPLETE_LATTICE f D /\ ~(D = EMPTY)) ==>

(IS_SOME (BIGINF f D EMPTY) /\
IS_SOME (BIGSUP f D EMPTY))``,


SIMP_TAC std_ss [IS_COMPLETE_LATTICE_def, BIGINF_def,
   OPTION_SELECT_THM, BIGSUP_def] THEN
STRIP_TAC THEN
Q.PAT_ASSUM `!M. P M` (MP_TAC o Q.SPEC `D`) THEN
ASM_SIMP_TAC std_ss [SUBSET_REFL, IS_INFIMUM_def,
   IS_SUPREMUM_def, IS_LOWER_BOUND_def,
   IS_UPPER_BOUND_def, NOT_IN_EMPTY] THEN
METIS_TAC[]);
   

val IS_COMPLETE_LATTICE___ALTERNATIVE_DEF = 
store_thm ("IS_COMPLETE_LATTICE___ALTERNATIVE_DEF",
``IS_COMPLETE_LATTICE f D = (
   (D = EMPTY) \/
   (rest_WeakOrder D f /\
    !M. M SUBSET D ==> (IS_SOME (BIGINF f D M) /\
                        IS_SOME (BIGSUP f D M))))``,

Cases_on `D = EMPTY` THEN1 (
   ASM_REWRITE_TAC[IS_COMPLETE_LATTICE___ALTERNATIVE_DEF_1]
) THEN
ASM_SIMP_TAC std_ss [IS_COMPLETE_LATTICE_def] THEN
Tactical.REVERSE (EQ_TAC) THEN1 (
   SIMP_TAC std_ss []
) THEN
STRIP_TAC THEN
ASM_REWRITE_TAC[] THEN
GEN_TAC THEN STRIP_TAC THEN
Cases_on `M = {}` THENL [
   METIS_TAC[IS_COMPLETE_LATTICE___ALTERNATIVE_DEF_2, IS_COMPLETE_LATTICE_def],
   METIS_TAC[]
]);


val IS_NON_EMPTY_COMPLETE_LATTICE_def = Define `
   IS_NON_EMPTY_COMPLETE_LATTICE f D = 
      IS_COMPLETE_LATTICE f D /\ (~(D= EMPTY))`

val IS_NON_EMPTY_COMPLETE_LATTICE_THM = store_thm ("IS_NON_EMPTY_COMPLETE_LATTICE_THM",
``   IS_NON_EMPTY_COMPLETE_LATTICE f D =

   (~(D = EMPTY) /\
   rest_WeakOrder D f /\
    !M. M SUBSET D ==> (IS_SOME (BIGINF f D M) /\
                        IS_SOME (BIGSUP f D M)))``,

   SIMP_TAC std_ss [IS_COMPLETE_LATTICE___ALTERNATIVE_DEF,
      IS_NON_EMPTY_COMPLETE_LATTICE_def] THEN
   METIS_TAC[]);


val inv_LATTICE =
   store_thm ("inv_LATTICE", ``
   (IS_LATTICE (inv f) D = IS_LATTICE f D) /\
   (IS_COMPLETE_LATTICE (inv f) D = IS_COMPLETE_LATTICE f D) /\
   (IS_NON_EMPTY_COMPLETE_LATTICE (inv f) D = IS_NON_EMPTY_COMPLETE_LATTICE f D)``,

SIMP_TAC std_ss [IS_LATTICE_def, rest_WeakOrder_THM,
   IS_COMPLETE_LATTICE_def, INF_SUP_inv_THM,
   IS_NON_EMPTY_COMPLETE_LATTICE_def] THEN
PROVE_TAC[]);



val IS_SOME_EXISTS = prove (``
   IS_SOME p = ?x. p = SOME x``, 
Cases_on `p` THEN SIMP_TAC std_ss []);

val BIGSUP_BIGINF_IN_D = store_thm ("BIGSUP_BIGINF_IN_D",
   ``(!f D a s. ((BIGSUP f D a = SOME s) ==> s IN D)) /\
     (!f D a s. ((BIGINF f D a = SOME s) ==> s IN D))``,

SIMP_TAC std_ss [BIGSUP_def, BIGINF_def] THEN
REPEAT STRIP_TAC THENL [
   IMP_RES_TAC OPTION_SELECT_IMP THEN
   FULL_SIMP_TAC std_ss [IS_SUPREMUM_def, IS_UPPER_BOUND_def],

   IMP_RES_TAC OPTION_SELECT_IMP THEN
   FULL_SIMP_TAC std_ss [IS_INFIMUM_def, IS_LOWER_BOUND_def]
]);


val NON_EMPTY_COMPLETE_LATTICE___BIGSUP_THM = store_thm ("NON_EMPTY_COMPLETE_LATTICE___BIGSUP_THM",
   ``!f D M. (IS_NON_EMPTY_COMPLETE_LATTICE f D /\
            (M SUBSET D)) ==>

    (?s. (BIGSUP f D M = SOME s) /\ (s IN D) /\
        (IS_SUPREMUM f D M s) /\
        (!s'. IS_SUPREMUM f D M s' ==> (s' = s)))``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [IS_NON_EMPTY_COMPLETE_LATTICE_THM] THEN  
`?s. (BIGSUP f D M = SOME s)` by METIS_TAC[IS_SOME_EXISTS] THEN
ASM_SIMP_TAC std_ss [] THEN
MATCH_MP_TAC (prove (``(A /\ (A ==> (B /\ C))) ==> (C /\ A /\ B)``, METIS_TAC[])) THEN
REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [BIGSUP_def] THEN
   IMP_RES_TAC OPTION_SELECT_IMP THEN
   FULL_SIMP_TAC std_ss [],

   FULL_SIMP_TAC std_ss [rest_WeakOrder_def] THEN
   METIS_TAC[IS_SUPREMUM_UNIQUE_THM],

   METIS_TAC[BIGSUP_BIGINF_IN_D]
]);


val NON_EMPTY_COMPLETE_LATTICE___BIGINF_THM = store_thm ("NON_EMPTY_COMPLETE_LATTICE___BIGINF_THM",
   ``!f D M. (IS_NON_EMPTY_COMPLETE_LATTICE f D /\
            (M SUBSET D)) ==>

    (?s. (BIGINF f D M = SOME s) /\ (s IN D) /\
        (IS_INFIMUM f D M s) /\
        (!s'. IS_INFIMUM f D M s' ==> (s' = s)))``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`inv f`, `D`, `M`] NON_EMPTY_COMPLETE_LATTICE___BIGSUP_THM) THEN
ASM_SIMP_TAC std_ss [inv_LATTICE, INF_SUP_inv_THM]);









val IS_COMPLETE_LATTICE_LEMMA_1 = store_thm ("IS_COMPLETE_LATTICE_LEMMA_1",
``!f D A B.

(IS_NON_EMPTY_COMPLETE_LATTICE f D /\ 
(A SUBSET D) /\ (B SUBSET D)) ==>

((BIGSUP f D A = BIGSUP f D B) =
 ((IS_UPPER_BOUND f D A (THE (BIGSUP f D B))) /\ 
  (IS_UPPER_BOUND f D B (THE (BIGSUP f D A)))))``,

REPEAT STRIP_TAC THEN
`?sa sb. (BIGSUP f D A = SOME sa) /\
         (BIGSUP f D B = SOME sb) /\
         IS_SUPREMUM f D A sa /\
         IS_SUPREMUM f D B sb /\
         sa IN D /\ sb IN D` by ALL_TAC THEN1 (
   METIS_TAC[NON_EMPTY_COMPLETE_LATTICE___BIGSUP_THM]
) THEN
FULL_SIMP_TAC std_ss [IS_SUPREMUM_def] THEN
EQ_TAC THENL [
   STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [], 

   STRIP_TAC THEN 
   `f sa sb /\ f sb sa` by METIS_TAC[] THEN
   FULL_SIMP_TAC std_ss [IS_NON_EMPTY_COMPLETE_LATTICE_THM,
      rest_WeakOrder_def, rest_antisymmetric_def]
]);


val IS_COMPLETE_LATTICE_LEMMA_2 = store_thm ("IS_COMPLETE_LATTICE_LEMMA_2",
``!f D A B.

(IS_NON_EMPTY_COMPLETE_LATTICE f D /\ 
(A SUBSET D) /\ (B SUBSET D)) ==>

((BIGINF f D A = BIGINF f D B) =
 ((IS_LOWER_BOUND f D A (THE (BIGINF f D B))) /\ 
  (IS_LOWER_BOUND f D B (THE (BIGINF f D A)))))``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`inv f`, `D`, `A`, `B`] IS_COMPLETE_LATTICE_LEMMA_1) THEN
ASM_SIMP_TAC std_ss [rest_WeakOrder_THM, INF_SUP_inv_THM, inv_LATTICE]);



val IS_COMPLETE_LATTICE_LEMMA_3 = store_thm ("IS_COMPLETE_LATTICE_LEMMA_3",
``!f D A.

(IS_NON_EMPTY_COMPLETE_LATTICE f D /\ 
(BIGUNION A SUBSET D)) ==>

(BIGSUP f D (BIGUNION A) =
BIGSUP f D (IMAGE (\a. THE (BIGSUP f D a)) A))``,

REPEAT STRIP_TAC THEN
`!a. a IN A ==> a SUBSET D` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION,
      GSYM LEFT_FORALL_IMP_THM] THEN
   METIS_TAC[]
) THEN
`(IMAGE (\a. THE (BIGSUP f D a)) A) SUBSET D` by ALL_TAC THEN1 (
   SIMP_TAC std_ss [SUBSET_DEF, IN_IMAGE] THEN
   REPEAT STRIP_TAC THEN
   `?s. (BIGSUP f D a = SOME s)` by ALL_TAC THEN1 (
      METIS_TAC[IS_NON_EMPTY_COMPLETE_LATTICE_THM, IS_SOME_EXISTS]
   ) THEN
   FULL_SIMP_TAC std_ss [] THEN
   METIS_TAC[BIGSUP_BIGINF_IN_D]
) THEN
ASM_SIMP_TAC std_ss [IS_COMPLETE_LATTICE_LEMMA_1] THEN


`(?s1. (BIGSUP f D (BIGUNION A) = SOME s1) /\
       (IS_SUPREMUM f D (BIGUNION A) s1) /\
       (s1 IN D)) /\
 ?s2. (BIGSUP f D (IMAGE (\a. THE (BIGSUP f D a)) A) = SOME s2) /\
      (IS_SUPREMUM f D (IMAGE (\a. THE (BIGSUP f D a)) A) s2) /\
      (s2 IN D)` by 
   METIS_TAC[NON_EMPTY_COMPLETE_LATTICE___BIGSUP_THM] THEN
FULL_SIMP_TAC std_ss [] THEN

FULL_SIMP_TAC std_ss [IS_UPPER_BOUND_def, IN_BIGUNION, GSYM LEFT_FORALL_IMP_THM, IN_IMAGE, IS_SUPREMUM_def] THEN
REPEAT STRIP_TAC THENL [
   `f (THE (BIGSUP f D s)) s2 /\
    (s SUBSET D)` by METIS_TAC[] THEN
   `?s3. (BIGSUP f D s = SOME s3) /\
         (s3 IN D) /\
         (IS_SUPREMUM f D s s3)` by 
      METIS_TAC[NON_EMPTY_COMPLETE_LATTICE___BIGSUP_THM] THEN
   `f s3 s2` by METIS_TAC[option_CLAUSES] THEN
   `f m s3` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [IS_SUPREMUM_def, IS_UPPER_BOUND_def]
   ) THEN 
   `m IN D` by METIS_TAC[SUBSET_DEF] THEN
   FULL_SIMP_TAC std_ss [IS_NON_EMPTY_COMPLETE_LATTICE_def,
      rest_WeakOrder_def, rest_transitive_def,
      IS_COMPLETE_LATTICE_def] THEN
   METIS_TAC[],


   `?s3. (BIGSUP f D a = SOME s3) /\
         (s3 IN D) /\
         (IS_SUPREMUM f D a s3)` by 
      METIS_TAC[NON_EMPTY_COMPLETE_LATTICE___BIGSUP_THM] THEN
   FULL_SIMP_TAC std_ss [] THEN
   `f s3 s2` by METIS_TAC[option_CLAUSES] THEN
   `f s2 s1` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `!b. P b` MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN

      `?s4. (BIGSUP f D a' = SOME s4) /\
            (s4 IN D) /\
            (IS_SUPREMUM f D a' s4)` by 
         METIS_TAC[NON_EMPTY_COMPLETE_LATTICE___BIGSUP_THM] THEN
      FULL_SIMP_TAC std_ss [IS_SUPREMUM_def] THEN
      Q.PAT_ASSUM `!b. P b` MATCH_MP_TAC THEN
      ASM_SIMP_TAC std_ss [IS_UPPER_BOUND_def] THEN
      METIS_TAC[]
   ) THEN

   FULL_SIMP_TAC std_ss [IS_NON_EMPTY_COMPLETE_LATTICE_def,
      rest_WeakOrder_def, rest_transitive_def,
      IS_COMPLETE_LATTICE_def] THEN
   METIS_TAC[]
]);
   
         
val IS_COMPLETE_LATTICE_LEMMA_4 = store_thm ("IS_COMPLETE_LATTICE_LEMMA_4",
``!f D A.

(IS_NON_EMPTY_COMPLETE_LATTICE f D /\ 
(BIGUNION A SUBSET D)) ==>

(BIGINF f D (BIGUNION A) =
BIGINF f D (IMAGE (\a. THE (BIGINF f D a)) A))``,


REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`inv f`, `D`, `A`] IS_COMPLETE_LATTICE_LEMMA_3) THEN
ASM_SIMP_TAC std_ss [rest_WeakOrder_THM, INF_SUP_inv_THM, inv_LATTICE]);




val IS_COMPLETE_LATTICE_LEMMA_5 = store_thm ("IS_COMPLETE_LATTICE_LEMMA_5",
``!f D A B.

(IS_NON_EMPTY_COMPLETE_LATTICE f D /\ 
A SUBSET B /\ (B SUBSET D)) ==>

f (THE (BIGSUP f D A)) (THE (BIGSUP f D B))``,

REPEAT STRIP_TAC THEN
`A SUBSET D` by METIS_TAC[SUBSET_TRANS] THEN
`?sa sb.
   (BIGSUP f D A = SOME sa) /\
   (BIGSUP f D B = SOME sb) /\
   (sa IN D) /\ (sb IN D) /\
   (IS_SUPREMUM f D A sa) /\
   (IS_SUPREMUM f D B sb)` by 
   METIS_TAC[NON_EMPTY_COMPLETE_LATTICE___BIGSUP_THM] THEN

FULL_SIMP_TAC std_ss [IS_SUPREMUM_def] THEN
Tactical.REVERSE (`IS_UPPER_BOUND f D A sb` by ALL_TAC) THEN1 (
   METIS_TAC[]
) THEN
FULL_SIMP_TAC std_ss [IS_UPPER_BOUND_def, SUBSET_DEF]);



val IS_COMPLETE_LATTICE_LEMMA_6 = store_thm ("IS_COMPLETE_LATTICE_LEMMA_6",
``!f D A B.

(IS_NON_EMPTY_COMPLETE_LATTICE f D /\ 
A SUBSET B /\ (B SUBSET D)) ==>

f (THE (BIGINF f D B)) (THE (BIGINF f D A))``,


REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`inv f`, `D`, `A`, `B`] IS_COMPLETE_LATTICE_LEMMA_5) THEN
ASM_SIMP_TAC std_ss [rest_WeakOrder_THM, INF_SUP_inv_THM, inv_LATTICE, inv_DEF]);


val SUPREMUM_INCREASE_SET = store_thm ("SUPREMUM_INCREASE_SET",
``!f D M1 M2 s1 s2.

((transitive f /\
IS_SUPREMUM f D M1 s1 /\
IS_SUPREMUM f D M2 s2 /\
(!e1. e1 IN M1 ==> ?e2. e2 IN M2 /\ f e1 e2)) ==>

(f s1 s2))``,

SIMP_TAC std_ss [IS_SUPREMUM_def, IS_UPPER_BOUND_def] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!b. (b IN D /\ Q b) ==> f s1 b` MATCH_MP_TAC THEN
ASM_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN
`?e2. e2 IN M2 /\ f m e2` by METIS_TAC[] THEN
`f e2 s2` by METIS_TAC[] THEN
METIS_TAC[transitive_def]);


val INFIMUM_DECREASE_SET = store_thm ("INFIMUM_DECREASE_SET",
``!f D M1 M2 s1 s2.

((transitive f /\
IS_INFIMUM f D M1 s1 /\
IS_INFIMUM f D M2 s2 /\
(!e1. e1 IN M1 ==> ?e2. e2 IN M2 /\ f e2 e1)) ==>

(f s2 s1))``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`inv f`, `D`, `M1`, `M2`, `s1`, `s2`] SUPREMUM_INCREASE_SET) THEN
ASM_SIMP_TAC std_ss [rest_WeakOrder_THM, INF_SUP_inv_THM, inv_LATTICE, transitive_inv, inv_DEF]);


val INFIMUM_INCREASE_SET = store_thm ("INFIMUM_INCREASE_SET",
``!f D M1 M2 s1 s2.

((transitive f /\
IS_INFIMUM f D M1 s1 /\
IS_INFIMUM f D M2 s2 /\
(!e2. e2 IN M2 ==> ?e1. e1 IN M1 /\ f e1 e2)) ==>

(f s1 s2))``,

SIMP_TAC std_ss [IS_INFIMUM_def, IS_LOWER_BOUND_def] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!b. (b IN D /\ Q b) ==> f b s2` MATCH_MP_TAC THEN
ASM_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN
`?e1. e1 IN M1 /\ f e1 m` by METIS_TAC[] THEN
`f s1 e1` by METIS_TAC[] THEN
METIS_TAC[transitive_def]);






val SUPREMUM_DECREASE_SET = store_thm ("SUPREMUM_DECREASE_SET",
``!f D M1 M2 s1 s2.

((transitive f /\
IS_SUPREMUM f D M1 s1 /\
IS_SUPREMUM f D M2 s2 /\
(!e2. e2 IN M2 ==> ?e1. e1 IN M1 /\ f e2 e1)) ==>

(f s2 s1))``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`inv f`, `D`, `M1`, `M2`, `s1`, `s2`] INFIMUM_INCREASE_SET) THEN
ASM_SIMP_TAC std_ss [rest_WeakOrder_THM, INF_SUP_inv_THM, inv_LATTICE, transitive_inv, inv_DEF]);


val THE_SUP_def = Define `THE_SUP f D x y = THE (SUP f D x y)`
val THE_INF_def = Define `THE_INF f D x y = THE (INF f D x y)`





val BIGINF_UNIV_IMP = store_thm ("BIGINF_UNIV_IMP",
``!s D M f.
(rest_antisymmetric D f /\ (BIGINF f UNIV M = SOME s) /\ (s IN D)) ==>
(BIGINF f D M = SOME s)``,

SIMP_TAC std_ss [BIGINF_def, OPTION_SELECT_THM] THEN
REPEAT STRIP_TAC THENL [
	Q.PAT_ASSUM `X IN D` MP_TAC THEN
	SELECT_ELIM_TAC THEN
	CONJ_TAC THENL [
		Q.EXISTS_TAC `s` THEN 
		ASM_REWRITE_TAC[],

		REPEAT STRIP_TAC THEN
		Q.EXISTS_TAC `x` THEN
		FULL_SIMP_TAC std_ss [IS_INFIMUM_def, IS_LOWER_BOUND_def, IN_UNIV]
	],


	Q.PAT_ASSUM `X IN D` MP_TAC THEN
	SELECT_ELIM_TAC THEN
	CONJ_TAC THENL [
		Q.EXISTS_TAC `s` THEN 
		ASM_REWRITE_TAC[],

		REPEAT STRIP_TAC THEN
		SELECT_ELIM_TAC THEN
		CONJ_TAC THENL [
			Q.EXISTS_TAC `x` THEN
			FULL_SIMP_TAC std_ss [IS_INFIMUM_def, IS_LOWER_BOUND_def, IN_UNIV],

			REPEAT STRIP_TAC THEN
			FULL_SIMP_TAC std_ss [IS_INFIMUM_def, IS_LOWER_BOUND_def, IN_UNIV, rest_antisymmetric_def]
		]
	]
])


val BIGSUP_UNIV_IMP = store_thm ("BIGSUP_UNIV_IMP",
``!s D M f.
(rest_antisymmetric D f /\ (BIGSUP f UNIV M = SOME s) /\ (s IN D)) ==>
(BIGSUP f D M = SOME s)``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`s`, `D`, `M`, `inv f`] BIGINF_UNIV_IMP) THEN
ASM_SIMP_TAC std_ss [rest_WeakOrder_THM, INF_SUP_inv_THM, inv_LATTICE, transitive_inv, inv_DEF]);

val _ = export_theory();
