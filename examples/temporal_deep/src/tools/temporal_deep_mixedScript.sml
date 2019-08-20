open HolKernel Parse boolLib bossLib;

(*
quietdec := true;

map load
 ["pred_setTheory", "pairTheory", "arithmeticTheory", "tuerk_tacticsLib",
  "containerTheory", "listTheory", "rich_listTheory", "set_lemmataTheory", "bitTheory"];
*)


open pred_setTheory pairTheory arithmeticTheory tuerk_tacticsLib
    containerTheory listTheory rich_listTheory set_lemmataTheory
    bitTheory;
open Sanity;

val _ = hide "S";
val _ = hide "I";

(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)



val _ = new_theory "temporal_deep_mixed";
val _ = ParseExtras.temp_loose_equality()


(******************************************************************************)
(* IS_ELEMENT_ITERATOR                                                        *)
(* This described a function that can create a number of new elements         *)
(******************************************************************************)

val IS_ELEMENT_ITERATOR_def =
Define
    `IS_ELEMENT_ITERATOR f n S =
      (!i j. (i < n /\ j < n) ==> ((f i = f j) = (i = j))) /\
      (!i. (i < n) ==> ~(f i IN S))`

val IS_ELEMENT_ITERATOR_0 =
 store_thm
  ("IS_ELEMENT_ITERATOR_0",

  ``!f S. IS_ELEMENT_ITERATOR f 0 S``,
  SIMP_TAC arith_ss [IS_ELEMENT_ITERATOR_def]);


val IS_ELEMENT_ITERATOR_SUBSET =
 store_thm
  ("IS_ELEMENT_ITERATOR_SUBSET",

  ``!f n S1 S2. (S2 SUBSET S1 /\ IS_ELEMENT_ITERATOR f n S1) ==> IS_ELEMENT_ITERATOR f n S2``,

  SIMP_TAC arith_ss [IS_ELEMENT_ITERATOR_def, SUBSET_DEF] THEN PROVE_TAC[]);


val IS_ELEMENT_ITERATOR_GE =
 store_thm
  ("IS_ELEMENT_ITERATOR_GE",

  ``!f n1 n2 S. (n2 <= n1 /\ IS_ELEMENT_ITERATOR f n1 S) ==> IS_ELEMENT_ITERATOR f n2 S``,

  SIMP_TAC arith_ss [IS_ELEMENT_ITERATOR_def]);


val IS_ELEMENT_ITERATOR___IMPLIES___INJ =
 store_thm
  ("IS_ELEMENT_ITERATOR___IMPLIES___INJ",

    ``!f n S.
        IS_ELEMENT_ITERATOR f n S ==>
        INJ f (count n) UNIV``,

    SIMP_TAC std_ss [IS_ELEMENT_ITERATOR_def, INJ_DEF,
                     IN_COUNT, IN_UNIV]);

val IS_ELEMENT_ITERATOR___INVERSE =
 store_thm
  ("IS_ELEMENT_ITERATOR___INVERSE",

    ``!f n S.
        IS_ELEMENT_ITERATOR f n S ==>
        (?g. !m. (m < n) ==> (g (f m) = m))``,

    METIS_TAC[INJ_INVERSE, IN_COUNT, IS_ELEMENT_ITERATOR___IMPLIES___INJ]);


val IS_ELEMENT_ITERATOR_EXISTS___DIFF =
 store_thm
  ("IS_ELEMENT_ITERATOR_EXISTS___DIFF",

  ``!n S.
      INFINITE (UNIV DIFF S) ==>
      ?f. IS_ELEMENT_ITERATOR f n S``,

  REPEAT STRIP_TAC THEN
  Induct_on `n` THENL [
    SIMP_TAC arith_ss [IS_ELEMENT_ITERATOR_def],

    FULL_SIMP_TAC arith_ss [IS_ELEMENT_ITERATOR_def] THEN
    `?e. e IN (UNIV DIFF S) /\ ~(e IN (IMAGE f (count n)))` by PROVE_TAC[IN_INFINITE_NOT_FINITE, FINITE_COUNT, IMAGE_FINITE] THEN
    `?f'. f' = (\i:num. if (i < n) then (f i) else e)` by METIS_TAC[] THEN
    EXISTS_TAC ``f':num->'a`` THEN
    ASM_SIMP_TAC arith_ss [] THEN
    REPEAT STRIP_TAC THENL [
      Cases_on `i < n` THEN
      Cases_on `j < n` THEN
      REPEAT STRIP_TAC THENL [
        ASM_SIMP_TAC std_ss [],

        `~(i = j)` by DECIDE_TAC THEN
        ASM_SIMP_TAC std_ss [] THEN
        `f i IN IMAGE f (count n)` by (
          ASM_REWRITE_TAC[IN_UNION, IN_IMAGE, IN_COUNT] THEN
          PROVE_TAC[]) THEN
        PROVE_TAC[],


        `~(i = j)` by DECIDE_TAC THEN
        ASM_SIMP_TAC std_ss [] THEN
        `f j IN IMAGE f (count n)` by (
          ASM_REWRITE_TAC[IN_UNION, IN_IMAGE, IN_COUNT] THEN
          PROVE_TAC[]) THEN
        PROVE_TAC[],


        ASM_REWRITE_TAC[] THEN DECIDE_TAC
      ],


      Cases_on `i < n` THENL [
        FULL_SIMP_TAC std_ss [IN_DIFF] THEN PROVE_TAC[],
        FULL_SIMP_TAC std_ss [IN_DIFF] THEN PROVE_TAC[IN_UNION]
      ]
    ]
  ]);


val IS_ELEMENT_ITERATOR_EXISTS =
 store_thm
  ("IS_ELEMENT_ITERATOR_EXISTS",

  ``!n S.
      (FINITE (S:'a set) /\ INFINITE (UNIV:'a set)) ==>
      ?f. IS_ELEMENT_ITERATOR f n S``,

    PROVE_TAC[FINITE_DIFF_down, IS_ELEMENT_ITERATOR_EXISTS___DIFF]);


(************************************************************************)
(* Variable renamings, i.e. injective functions with some properties    *)
(************************************************************************)

val FINITE_INJ_EXISTS_aux = prove (
   ``INFINITE (UNIV:'b set) ==> !S1:'a set. FINITE S1 ==>
            !S2:'b set. FINITE S2 ==>
            ?f:'a->'b. (INJ f S1 UNIV /\ (DISJOINT (IMAGE f S1) S2))``,

      DISCH_TAC THEN
      SET_INDUCT_TAC THENL [
        SIMP_TAC std_ss [INJ_EMPTY, IMAGE_EMPTY, DISJOINT_EMPTY],

        REPEAT STRIP_TAC THEN
        RES_TAC THEN
        `?x. ~(x IN ((IMAGE f s) UNION S2))` by PROVE_TAC[IMAGE_FINITE, NOT_IN_FINITE, FINITE_UNION] THEN
        Q_TAC EXISTS_TAC `\z. (if z = e then x else (f z))` THEN
        UNDISCH_NO_TAC 2 THEN
        SIMP_ALL_TAC std_ss [INJ_DEF, IN_INSERT, IN_UNIV, IN_IMAGE, IN_UNION, DISJOINT_DISJ_THM] THEN
        METIS_TAC[]
      ]);


val FINITE_INJ_EXISTS = save_thm ("FINITE_INJ_EXISTS",
SIMP_RULE std_ss [GSYM RIGHT_FORALL_IMP_THM,
    AND_IMP_INTRO] FINITE_INJ_EXISTS_aux);



val DISJOINT_VARRENAMING_EXISTS =
 store_thm
  ("DISJOINT_VARRENAMING_EXISTS",
   ``!(S1:'a set) (S2:'a set) (S3:'a set). (FINITE S1 /\ FINITE S2 /\ FINITE S3 /\ (DISJOINT S1 S3) /\ INFINITE (UNIV:'a set)) ==>
   (?f. INJ f UNIV UNIV /\ (DISJOINT (IMAGE f S1) S2) /\ (!x. (x IN S3) ==> (f x = x)))``,

   REPEAT STRIP_TAC THEN
   UNDISCH_TAC ``DISJOINT S1 S3`` THEN
   UNDISCH_TAC ``FINITE S1`` THEN
   SPEC_TAC (``S1:'a set``,``S1:'a set``) THEN
   SET_INDUCT_TAC THENL [
      REPEAT STRIP_TAC THEN
      EXISTS_TAC ``\x. x`` THEN
      SIMP_TAC std_ss [INJ_ID, IMAGE_EMPTY, DISJOINT_EMPTY],


      REPEAT STRIP_TAC THEN
      FULL_SIMP_TAC std_ss [DISJOINT_INSERT, IMAGE_INSERT] THEN
      `?x. ~(x IN (IMAGE f (s :'a set))) /\ ~(x IN (S2:'a set)) /\ ~(x IN (S3:'a set))` by (
         `FINITE ((IMAGE f s) UNION S2 UNION S3)` by METIS_TAC[IMAGE_FINITE, FINITE_UNION] THEN
         PROVE_TAC[NOT_IN_FINITE, IN_UNION]
      ) THEN
      EXISTS_TAC ``\z:'a. (if z = e then x:'a else (if (f z) = x then (f e) else (f z)))`` THEN
      REPEAT STRIP_TAC THENL [
        REWRITE_ALL_TAC [INJ_DEF, IN_UNIV] THEN METIS_TAC[],

        FULL_SIMP_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL, IN_IMAGE] THEN
        PROVE_TAC[],

        FULL_SIMP_TAC std_ss [],

        `~(x' = e) /\ ~(f x' = x)` by PROVE_TAC[] THEN
        ASM_SIMP_TAC std_ss []
      ]
   ]);


val POW_VARRENAMING_EXISTS =
 store_thm
  ("POW_VARRENAMING_EXISTS",
   ``!(S1:'a set) (S2:'a set). (FINITE S1 /\ FINITE S2 /\ INFINITE (UNIV:'a set)) ==>
      (?f. INJ f (POW S1) UNIV /\ (DISJOINT (IMAGE f (POW S1)) S2))``,

   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC FINITE_INJ_EXISTS THEN
   ASM_REWRITE_TAC[FINITE_POW_IFF]);





(******************************************************************************)
(* LIST_BIGUNION                                                              *)
(******************************************************************************)

val LIST_BIGUNION_def =
 Define
   `(LIST_BIGUNION [] = EMPTY) /\
    (LIST_BIGUNION (h::l) = (h UNION (LIST_BIGUNION l)))`;


val LIST_BIGUNION_APPEND =
 store_thm
  ("LIST_BIGUNION_APPEND",
    ``!l1 l2. LIST_BIGUNION (l1 ++ l2) = (LIST_BIGUNION l1 UNION LIST_BIGUNION l2)``,

      Induct_on `l1` THENL [
        SIMP_TAC list_ss [LIST_BIGUNION_def, UNION_EMPTY],
        ASM_SIMP_TAC list_ss [LIST_BIGUNION_def, UNION_ASSOC]
      ]);


val IN_LIST_BIGUNION =
 store_thm
  ("IN_LIST_BIGUNION",

   ``!x l. (x IN LIST_BIGUNION l) = ?el. MEM el l /\ x IN el``,

    Induct_on `l` THENL [
      SIMP_TAC list_ss [LIST_BIGUNION_def, NOT_IN_EMPTY],
      SIMP_TAC list_ss [LIST_BIGUNION_def, IN_UNION] THEN PROVE_TAC[]
    ]);

(* Perhaps use this everywhere and get rid of LIST_BIGUNION *)
val LIST_BIGUNION_ALT_DEF = store_thm ("LIST_BIGUNION_ALT_DEF",
  ``!l. LIST_BIGUNION l = BIGUNION (set l)``,

SIMP_TAC std_ss [EXTENSION, IN_LIST_BIGUNION, IN_BIGUNION] >>
METIS_TAC[]);



(******************************************************************************)
(* Auxiliary arithmetic stuff                                                 *)
(******************************************************************************)

val SUC_MOD_CASES =
 store_thm ("SUC_MOD_CASES",

  ``!n m. 0 < n ==>
  ((((SUC m) MOD n) = 0) \/ (((SUC m) MOD n) = (SUC (m MOD n))))``,

  REPEAT STRIP_TAC THEN
  Cases_on `n = 1` THENL [
    ASM_REWRITE_TAC[MOD_1],

    `(SUC m) MOD n = ((SUC (m MOD n)) MOD n)` by (
      `1 < n` by DECIDE_TAC THEN
      `1 = 1 MOD n` by PROVE_TAC[LESS_MOD] THEN
      ASM_SIMP_TAC std_ss [SUC_ONE_ADD] THEN
      ONCE_ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC std_ss [MOD_PLUS]
    ) THEN
    ASM_REWRITE_TAC[] THEN
    Cases_on `SUC (m MOD n) < n` THENL [
      ASM_SIMP_TAC std_ss [LESS_MOD],

      `m MOD n < n` by PROVE_TAC[DIVISION] THEN
      `SUC (m MOD n) = n` by DECIDE_TAC THEN
      ASM_SIMP_TAC std_ss [DIVMOD_ID]
    ]
  ]);



(*****************************)
(* COND_IMP_EQ               *)
(*****************************)

val COND_IMP_EQ_def =
  Define `COND_IMP_EQ c A B = if c then A=B else A ==> B`

val COND_IMP_EQ___REWRITE =
  store_thm ("COND_IMP_EQ___REWRITE",
    ``!c A B. COND_IMP_EQ c A B =
             ((A ==> B) /\ (c ==> (A = B)))``,
      SIMP_TAC std_ss [COND_IMP_EQ_def] THEN
      METIS_TAC[]);


(****************************************************************************************)
(* INTERVAL_SET and INTERVAL_LIST                                                       *)
(*                                                                                      *)
(* Similar to count and COUNT_LIST, but have a starting point that might differ from 0  *)
(****************************************************************************************)

val INTERVAL_SET_def =
  Define `
    INTERVAL_SET (n1:num) (n2:num) = IMAGE (\x. n1 + x) (count ((SUC n2)-n1))`


val INTERVAL_LIST_def =
  Define `
    INTERVAL_LIST (n1:num) (n2:num) =
      MAP (\x. n1 + x) (COUNT_LIST ((SUC n2) - n1))`


val INTERVAL_SET_0 = store_thm ("INTERVAL_SET_0",
  ``!n. INTERVAL_SET 0 n = count (SUC n)``,
SIMP_TAC std_ss [INTERVAL_SET_def, EXTENSION, IN_IMAGE]);

val INTERVAL_LIST_0 = store_thm ("INTERVAL_LIST_0",
  ``!n. INTERVAL_LIST 0 n = COUNT_LIST (SUC n)``,
SIMP_TAC list_ss [INTERVAL_LIST_def, LIST_EQ_REWRITE, EL_MAP]);


val LIST_TO_SET___INTERVAL_LIST =
  store_thm ("LIST_TO_SET___INTERVAL_LIST",
    ``!m0 m1. ((set (INTERVAL_LIST m0 m1)) = INTERVAL_SET m0 m1)``,

SIMP_TAC std_ss [INTERVAL_LIST_def, INTERVAL_SET_def,
  LIST_TO_SET_MAP, COUNT_LIST_COUNT]);


val FINITE_INTERVAL_SET =
  store_thm ("FINITE_INTERVAL_SET",
    ``!n1 n2. FINITE (INTERVAL_SET n1 n2)``,
    SIMP_TAC std_ss [INTERVAL_SET_def, FINITE_COUNT,
      IMAGE_FINITE]);


val MEM_INTERVAL_LIST =
  store_thm ("MEM_INTERVAL_LIST",
    ``!n m0 m1. ((MEM n (INTERVAL_LIST m0 m1)) = (m0 <= n /\ n <= m1))``,

    SIMP_TAC std_ss [INTERVAL_LIST_def, MEM_MAP, MEM_COUNT_LIST] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      DECIDE_TAC,
      DECIDE_TAC,
      Q.EXISTS_TAC `n - m0` >> DECIDE_TAC
    ]
  );


val IN_INTERVAL_SET =
  store_thm ("IN_INTERVAL_SET",
    ``!n n1 n2. (n IN INTERVAL_SET n1 n2) = (n1 <= n /\ n <= n2)``,
    SIMP_TAC std_ss [GSYM LIST_TO_SET___INTERVAL_LIST, MEM_INTERVAL_LIST]);


val INTERVAL_SET_SING =
  store_thm ("INTERVAL_SET_SING",
    ``!n. (INTERVAL_SET n n) = {n}``,
    SIMP_TAC std_ss [EXTENSION, IN_SING, IN_INTERVAL_SET] THEN
    DECIDE_TAC);


val INTERVAL_LIST_THM =
  store_thm ("INTERVAL_LIST_THM",
    ``!n1 n2. ((n1 <= n2) ==> (INTERVAL_LIST n1 n2 = (n1::INTERVAL_LIST (SUC n1) n2))) /\
              ((n2 < n1) ==> (INTERVAL_LIST n1 n2 = []))``,

      SIMP_TAC std_ss [INTERVAL_LIST_def] THEN
      REPEAT STRIP_TAC THENL [
        `(SUC n2 - n1 = SUC (n2 - n1)) /\ (n1 <= n2)` by DECIDE_TAC THEN
        Q.ABBREV_TAC `a = n2 - n1` THEN
        FULL_SIMP_TAC list_ss [COUNT_LIST_def, MAP_MAP_o, combinTheory.o_DEF] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        SIMP_TAC arith_ss [FUN_EQ_THM],

        `(SUC n2 - n1 = 0) /\ (n2 - n1 = 0) /\ ~(n1 <= n2)` by DECIDE_TAC THEN
        ASM_SIMP_TAC list_ss [COUNT_LIST_def]
      ]);



(************************)
(* SET_BINARY_ENCODING  *)
(************************)

(* Encode sets of numbers as numbers. Each number in the original set of numbers
   sets the corresponding bit of the resulting number. *)

val SET_BINARY_ENCODING_def =
  Define `SET_BINARY_ENCODING =
          SIGMA (\n:num. (2:num)**n)`;


val SET_BINARY_ENCODING_THM =
  store_thm ("SET_BINARY_ENCODING_THM",
``(SET_BINARY_ENCODING EMPTY = 0) /\
  (!e s. (FINITE s /\ ~(e IN s)) ==>
         (SET_BINARY_ENCODING (e INSERT s) = (2 ** e) + (SET_BINARY_ENCODING s)))``,

SIMP_TAC std_ss [SET_BINARY_ENCODING_def, SUM_IMAGE_THM] THEN
PROVE_TAC[DELETE_NON_ELEMENT]);

val SET_BINARY_ENCODING_SING =
  store_thm ("SET_BINARY_ENCODING_SING",
``!e. SET_BINARY_ENCODING {e} = 2 ** e``,

SIMP_TAC std_ss [SET_BINARY_ENCODING_def, SUM_IMAGE_SING]);


val SET_BINARY_ENCODING___UNION =
  store_thm ("SET_BINARY_ENCODING___UNION",

``!S1 S2. DISJOINT S1 S2 /\ FINITE S1 /\ FINITE S2 ==>
(SET_BINARY_ENCODING (S1 UNION S2) =
(SET_BINARY_ENCODING S1 + SET_BINARY_ENCODING S2))``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [SET_BINARY_ENCODING_def, SUM_IMAGE_UNION] THEN
`S1 INTER S2 = EMPTY` by (
  SIMP_ALL_TAC std_ss [DISJOINT_DISJ_THM, IN_INTER, EXTENSION, NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[]
) THEN
ASM_SIMP_TAC std_ss [SUM_IMAGE_THM]);



val SET_BINARY_ENCODING___SUBSET =
  store_thm ("SET_BINARY_ENCODING___SUBSET", ``
!S1 S2. S1 SUBSET S2 /\ FINITE S2 ==>
(SET_BINARY_ENCODING S1 <=
(SET_BINARY_ENCODING S2))``,

REPEAT STRIP_TAC THEN
Q.ABBREV_TAC `S3 = S2 DIFF S1` THEN
`S2 = S3 UNION S1` by (
  SIMP_ALL_TAC std_ss [EXTENSION, IN_UNION, IN_DIFF, SUBSET_DEF] THEN
  PROVE_TAC[]
) THEN
ASM_SIMP_TAC std_ss [] THEN

`SET_BINARY_ENCODING (S3 UNION S1) =
 SET_BINARY_ENCODING S3 + SET_BINARY_ENCODING S1` by (

  MATCH_MP_TAC SET_BINARY_ENCODING___UNION THEN
  Q.UNABBREV_TAC `S3` THEN
  METIS_TAC[DISJOINT_DIFF, FINITE_DIFF, SUBSET_FINITE]
) THEN
ASM_SIMP_TAC std_ss []);



val SET_BINARY_ENCODING___COUNT =
  store_thm ("SET_BINARY_ENCODING___COUNT",
    ``!n. SET_BINARY_ENCODING (count n) = PRE (2**n)``,

    Induct_on `n` THENL [
      SIMP_TAC arith_ss [COUNT_ZERO, SET_BINARY_ENCODING_THM],

      SIMP_TAC std_ss [COUNT_SUC, SET_BINARY_ENCODING_THM,
        FINITE_INSERT, FINITE_COUNT, IN_COUNT] THEN
      ASM_SIMP_TAC arith_ss [EXP]
    ]
  );


val SET_BINARY_ENCODING___REDUCE =
  store_thm ("SET_BINARY_ENCODING___REDUCE",
  ``!n S. FINITE S ==> DISJOINT S (count n) ==>
          ((SET_BINARY_ENCODING S) = (SET_BINARY_ENCODING (IMAGE (\x:num. x - n) S)) * (2 ** n))``,

GEN_TAC THEN
SET_INDUCT_TAC THENL [
  SIMP_TAC std_ss [SET_BINARY_ENCODING_THM, IMAGE_EMPTY],

  REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC arith_ss [DISJOINT_INSERT, IN_COUNT] THEN
  `~((e - n) IN (IMAGE (\x. x - n) s))` by (
    SIMP_TAC std_ss [IN_IMAGE] THEN
    GEN_TAC THEN
    Cases_on `x IN s` THEN ASM_REWRITE_TAC[] THEN
    FULL_SIMP_TAC std_ss [DISJOINT_DISJ_THM, IN_INSERT, IN_COUNT] THEN
    `~(x < n) /\ (e <> x)` by PROVE_TAC[] THEN
    DECIDE_TAC
  ) THEN
  FULL_SIMP_TAC std_ss [SET_BINARY_ENCODING_THM, IMAGE_INSERT, FINITE_INSERT, IMAGE_FINITE] THEN
  ASM_SIMP_TAC arith_ss [RIGHT_ADD_DISTRIB, GSYM EXP_ADD]
]);


val SET_BINARY_ENCODING___BITS =
  store_thm ("SET_BINARY_ENCODING___BITS",
  ``!n S. FINITE S ==> (BIT n (SET_BINARY_ENCODING S) = (n IN S))``,

  REPEAT STRIP_TAC THEN
  Q.ABBREV_TAC `S1 = S INTER count n` THEN
  Q.ABBREV_TAC `S2 = S DIFF count (SUC n)` THEN
  Q.ABBREV_TAC `Sn = S INTER {n}` THEN
  `FINITE S1 /\ FINITE Sn /\ FINITE S2` by PROVE_TAC[INTER_FINITE,
    FINITE_SING, FINITE_DIFF] THEN
  Q.SUBGOAL_THEN `S = S1 UNION Sn UNION S2` SUBST1_TAC THEN1 (
    UNABBREV_ALL_TAC THEN
    ASM_SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF,
      IN_COUNT, IN_SING] THEN
    REPEAT STRIP_TAC THEN
    Cases_on `x IN S` THEN ASM_REWRITE_TAC[] THEN
    DECIDE_TAC
  ) THEN

  Q.SUBGOAL_THEN `SET_BINARY_ENCODING (S1 UNION Sn UNION S2) =
                  SET_BINARY_ENCODING S1 + SET_BINARY_ENCODING Sn + SET_BINARY_ENCODING S2`
    SUBST1_TAC THEN1 (
    `DISJOINT S1 Sn /\ DISJOINT (S1 UNION Sn) S2` by (
      UNABBREV_ALL_TAC THEN
      ASM_SIMP_TAC std_ss [DISJOINT_DISJ_THM, IN_INTER, IN_SING,
        IN_COUNT, IN_UNION, IN_DIFF] THEN
      REPEAT STRIP_TAC THEN
      Cases_on `x IN S` THEN ASM_REWRITE_TAC[] THEN
      DECIDE_TAC
    ) THEN

    ASM_SIMP_TAC std_ss [FINITE_UNION, SET_BINARY_ENCODING___UNION]
  ) THEN

  Q.SUBGOAL_THEN `n IN S1 UNION Sn UNION S2 = n IN Sn` SUBST1_TAC THEN1 (
    UNABBREV_ALL_TAC THEN
    ASM_SIMP_TAC arith_ss [IN_UNION, IN_INTER, IN_DIFF, IN_COUNT]
  ) THEN

  `SET_BINARY_ENCODING S1 < 2**n` by (
    MP_TAC (Q.SPECL [`S1`, `count n`] SET_BINARY_ENCODING___SUBSET) THEN
    `S1 SUBSET count n` by METIS_TAC[INTER_SUBSET] THEN
    FULL_SIMP_TAC std_ss [SET_BINARY_ENCODING___COUNT, FINITE_COUNT] THEN
    `~(((2:num) ** n) = 0)` by SIMP_TAC arith_ss [EXP_EQ_0] THEN
    DECIDE_TAC
  ) THEN

  `?a. SET_BINARY_ENCODING S2 = a * 2** (SUC n)` by (
    MP_TAC (Q.SPECL [`SUC n`, `S2`] SET_BINARY_ENCODING___REDUCE) THEN
    `DISJOINT S2 (count (SUC n))` by PROVE_TAC[DISJOINT_DIFF] THEN
    PROVE_TAC[]
  ) THEN

  Q.ABBREV_TAC `nc = (if n IN Sn then 1 else 0)` THEN

  `SET_BINARY_ENCODING Sn = nc * 2**n` by (
    UNABBREV_ALL_TAC THEN
    Cases_on `n IN S` THENL [
      `S INTER {n} = {n}` by (
        ASM_SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_SING] THEN
        METIS_TAC[]
      ) THEN
      ASM_SIMP_TAC std_ss [SET_BINARY_ENCODING_SING, IN_SING],

      `S INTER {n} = EMPTY` by (
        ASM_SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_SING, NOT_IN_EMPTY]
      ) THEN
      ASM_SIMP_TAC std_ss [SET_BINARY_ENCODING_THM, NOT_IN_EMPTY]
    ]
  ) THEN


  MP_TAC (Q.SPECL [`n`, `n`, `nc + 2*a`, `SET_BINARY_ENCODING S1`] BITS_SUM) THEN
  ASM_SIMP_TAC arith_ss [RIGHT_ADD_DISTRIB] THEN
  `2 * (a * 2 ** n) = a * 2 ** SUC n` by (
    SIMP_TAC arith_ss [EXP]
  ) THEN
  ASM_SIMP_TAC std_ss [BIT_def, BITS_SUM2] THEN
  DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN

  REWRITE_TAC[GSYM BIT_def] THEN
  Q.UNABBREV_TAC `nc` THEN
  Cases_on `n IN Sn` THENL [
    ASM_SIMP_TAC std_ss [BIT_B],
    ASM_SIMP_TAC std_ss [BIT_ZERO]
  ]
);





val SET_BINARY_ENCODING___INJ =
  store_thm ("SET_BINARY_ENCODING___INJ",
  ``!S. FINITE S ==> INJ SET_BINARY_ENCODING (POW S) UNIV``,

  SIMP_TAC std_ss [INJ_DEF, IN_UNIV, IN_POW, EXTENSION] THEN
  PROVE_TAC[SET_BINARY_ENCODING___BITS, SUBSET_FINITE]);




val SET_BINARY_ENCODING_SHIFT_def =
  Define `
    SET_BINARY_ENCODING_SHIFT n1 n2 S =
      (SET_BINARY_ENCODING (IMAGE (\n. n - n1) S) + n2)`;


val SET_BINARY_ENCODING_SHIFT___INJ =
  store_thm ("SET_BINARY_ENCODING_SHIFT___INJ",
  ``!S n1 n2. (FINITE S /\ (!n. n IN S ==> n >= n1)) ==> INJ (SET_BINARY_ENCODING_SHIFT n1 n2) (POW S) UNIV``,


  SIMP_TAC std_ss [SET_BINARY_ENCODING_SHIFT_def, INJ_DEF, IN_UNIV] THEN
  REPEAT STRIP_TAC THEN
  Q.ABBREV_TAC `f = (\n:num. n - n1)` THEN
  FULL_SIMP_TAC std_ss [] THEN
  `(IMAGE f x) IN POW (IMAGE f S) /\
               (IMAGE f y) IN POW (IMAGE f S)` by (
    FULL_SIMP_TAC std_ss [IN_POW, IMAGE_SUBSET]
  ) THEN
  `FINITE (IMAGE f S)` by ASM_SIMP_TAC std_ss [IMAGE_FINITE] THEN
  `(IMAGE f x = IMAGE f y) <=> (x = y)` suffices_by METIS_TAC[SET_BINARY_ENCODING___INJ, INJ_DEF] THEN

  MATCH_MP_TAC INJECTIVE_IMAGE_EQ THEN
  REPEAT STRIP_TAC THEN
  `x' >= n1 /\ y' >= n1` by (
    SIMP_ALL_TAC std_ss [IN_POW, IN_UNION, SUBSET_DEF] THEN
    PROVE_TAC[]
  ) THEN
  Q.UNABBREV_TAC `f` THEN
  FULL_SIMP_TAC arith_ss []);




val SET_BINARY_ENCODING___IMAGE_THM =
  store_thm ("SET_BINARY_ENCODING___IMAGE_THM",

  ``!n. IMAGE SET_BINARY_ENCODING (POW (INTERVAL_SET 0 n)) =
        INTERVAL_SET 0 (PRE (2**(SUC n)))``,

    Induct_on `n` THENL [
      SIMP_TAC std_ss [INTERVAL_SET_0, EXTENSION, IN_IMAGE, IN_POW, IN_COUNT] THEN
      `!s. s SUBSET count 1 <=> (s = {}) \/ (s = {0})` by (
         SIMP_TAC arith_ss [EXTENSION, SUBSET_DEF, IN_SING, NOT_IN_EMPTY, IN_COUNT] THEN
         `!n. n < 1 <=> (n = 0)` by DECIDE_TAC THEN
         METIS_TAC[]
      ) THEN
      ASM_SIMP_TAC std_ss [LEFT_AND_OVER_OR, EXISTS_OR_THM, SET_BINARY_ENCODING_THM,
        SET_BINARY_ENCODING_SING] THEN
      DECIDE_TAC,



      Q.SUBGOAL_THEN `(POW (INTERVAL_SET 0 (SUC n))) =
                   ((POW (INTERVAL_SET 0 n)) UNION
                    (IMAGE (\S. (SUC n) INSERT S) (POW (INTERVAL_SET 0 n))))`
        SUBST1_TAC THEN1 (
        SIMP_TAC std_ss [INTERVAL_SET_0, Q.SPEC `SUC n` COUNT_SUC,
          POW_EQNS, LET_THM] THEN
        SIMP_TAC std_ss [EXTENSION, IN_IMAGE, IN_UNION] THEN
        METIS_TAC[]
      ) THEN
      ASM_SIMP_TAC std_ss [IMAGE_UNION] THEN


      Q.SUBGOAL_THEN `IMAGE SET_BINARY_ENCODING
      (IMAGE (\S. SUC n INSERT S) (POW (INTERVAL_SET 0 n))) =
       IMAGE (\x. 2**(SUC n) + x) (IMAGE SET_BINARY_ENCODING
        (POW (INTERVAL_SET 0 n)))` SUBST1_TAC THEN1 (

        SIMP_TAC std_ss [IMAGE_IMAGE, combinTheory.o_DEF] THEN
        MATCH_MP_TAC IMAGE_CONG THEN
        SIMP_TAC std_ss [INTERVAL_SET_0, IN_POW] THEN
        REPEAT STRIP_TAC THEN
        `~(SUC n IN x)` by (
          CCONTR_TAC THEN
          FULL_SIMP_TAC arith_ss [SUBSET_DEF, IN_COUNT] THEN
          `SUC n < SUC n` by METIS_TAC[] THEN
          DECIDE_TAC
        ) THEN
        `FINITE x` by METIS_TAC[SUBSET_FINITE, FINITE_COUNT] THEN
        ASM_SIMP_TAC std_ss [SET_BINARY_ENCODING_THM]
      ) THEN

      ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN
      SIMP_TAC std_ss [IN_UNION, IN_IMAGE, IN_INTERVAL_SET, EXP] THEN
      EQ_TAC THEN REPEAT STRIP_TAC THENL [
        ASM_SIMP_TAC arith_ss [],
        ASM_SIMP_TAC arith_ss [],

        RIGHT_DISJ_TAC THEN
        Q_TAC EXISTS_TAC `x - (2 * 2**n)` THEN
        FULL_SIMP_TAC arith_ss []
      ]
    ]);





val SET_BINARY_ENCODING_SHIFT___IMAGE_THM =
  store_thm ("SET_BINARY_ENCODING_SHIFT___IMAGE_THM",
  ``!n1 n2 n3. n1 <= n2 ==>
              (IMAGE (SET_BINARY_ENCODING_SHIFT n1 n3) (POW (INTERVAL_SET n1 n2)) =
               INTERVAL_SET n3 (n3 + (PRE (2**(SUC (n2 - n1))))))``,

    REPEAT STRIP_TAC THEN

    Q.SUBGOAL_THEN `INTERVAL_SET n3 (n3 + PRE (2 ** SUC (n2 - n1))) =
                 IMAGE (\x:num. x + n3) (INTERVAL_SET 0 (PRE (2 ** SUC (n2 - n1))))` SUBST1_TAC THEN1 (

      SIMP_TAC arith_ss [INTERVAL_SET_def, IMAGE_ID] THEN
      Q.ABBREV_TAC `n4 = PRE (2 ** SUC (n2 - n1))` THEN
      `SUC (n3 + n4) - n3 = SUC n4` suffices_by METIS_TAC[] THEN
      DECIDE_TAC
    ) THEN

    REWRITE_TAC [GSYM SET_BINARY_ENCODING___IMAGE_THM] THEN

    ONCE_REWRITE_TAC[EXTENSION] THEN
    SIMP_TAC std_ss [IN_IMAGE, SET_BINARY_ENCODING_SHIFT_def,
      GSYM RIGHT_EXISTS_AND_THM, IN_POW] THEN
    GEN_TAC THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Q.EXISTS_TAC `(IMAGE (\n. n - n1) x')` THEN
      FULL_SIMP_TAC arith_ss [PULL_EXISTS, SUBSET_DEF, IN_INTERVAL_SET, IN_IMAGE],


      Q_TAC EXISTS_TAC `(IMAGE (\n. n + n1) x'')` THEN
      ASM_SIMP_TAC arith_ss [GSYM IMAGE_COMPOSE, combinTheory.o_DEF,
        IMAGE_ID] THEN
      FULL_SIMP_TAC arith_ss [SUBSET_DEF, IN_INTERVAL_SET, IN_IMAGE, PULL_EXISTS] THEN
      GEN_TAC THEN STRIP_TAC THEN
      RES_TAC THEN
      DECIDE_TAC
    ]);





val SET_BINARY_ENCODING_SHIFT___INSERT =
  store_thm ("SET_BINARY_ENCODING_SHIFT___INSERT",
``!i k l S. FINITE S /\ (i <= l) /\ ~(l IN S) /\ (!x. x IN S ==> i <= x) ==>
(SET_BINARY_ENCODING_SHIFT i k (l INSERT S) =
 SET_BINARY_ENCODING_SHIFT i (2**(l-i)+k) S)``,

SIMP_TAC arith_ss [SET_BINARY_ENCODING_SHIFT_def,
  SET_BINARY_ENCODING_def, SUM_IMAGE_THM, IMAGE_INSERT,
  IMAGE_FINITE] THEN
REPEAT STRIP_TAC THEN
AP_TERM_TAC THEN
SIMP_TAC std_ss [EXTENSION, IN_IMAGE, IN_DELETE] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
  PROVE_TAC[],
  PROVE_TAC[],

  RES_TAC THEN
  `n = l` by DECIDE_TAC THEN
  PROVE_TAC[]
]);

val _ = export_theory();
