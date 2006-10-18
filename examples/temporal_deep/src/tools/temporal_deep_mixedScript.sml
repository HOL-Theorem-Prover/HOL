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


val ITERATE_def =
Define
    `(ITERATE f e0 0 = e0) /\
      (ITERATE f e0 (SUC n) = f (ITERATE f e0 n))`


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


val IS_ELEMENT_ITERATOR___IMPLIES___INJ =
 store_thm
  ("IS_ELEMENT_ITERATOR___IMPLIES___INJ",

    ``!f n S.
        IS_ELEMENT_ITERATOR f n S ==>
        INJ f (count n) UNIV``,
    
    SIMP_TAC std_ss [IS_ELEMENT_ITERATOR_def, INJ_DEF,
                     IN_COUNT, IN_UNIV]);




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

    PROVE_TAC[FINITE_DIFF_down, IS_ELEMENT_ITERATOR_EXISTS___DIFF,
              INFINITE_DEF]);


val POWER_SET_def=
 Define
   `(POWER_SET (s:'a set) = {x | x SUBSET s})`;


val IN_POWER_SET_SUBSET_EQUIV=
 store_thm
  ("IN_POWER_SET_SUBSET_EQUIV",
   ``!s S. (s IN (POWER_SET S)) = (s SUBSET S)``,

   SIMP_TAC std_ss [POWER_SET_def, GSPECIFICATION]);



val POWER_SET_IND_THM=
 store_thm
  ("POWER_SET_IND_THM",
   ``(POWER_SET {} = {{}}) /\
    !s S. ((POWER_SET (s INSERT S) = ((POWER_SET S) UNION (IMAGE (\x. s INSERT x) (POWER_SET S)))))``,

   REWRITE_TAC[POWER_SET_def] THEN
   REPEAT STRIP_TAC THENL [
      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, SUBSET_EMPTY, IN_SING, NOT_IN_EMPTY] THEN
      SIMP_TAC std_ss [GSYM EXTENSION],


      SIMP_TAC std_ss [EXTENSION, GSPECIFICATION, IN_UNION, IN_IMAGE] THEN
      SIMP_TAC std_ss [GSYM EXTENSION] THEN
      REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
        RIGHT_DISJ_TAC THEN
        EXISTS_TAC ``x INTER S:'b set`` THEN
        REWRITE_TAC [INTER_SUBSET] THEN
        FULL_SIMP_TAC std_ss [INSERT_DEF, SUBSET_DEF, IN_INTER, GSPECIFICATION, EXTENSION] THEN
        PROVE_TAC[],

        FULL_SIMP_TAC std_ss [INSERT_DEF, SUBSET_DEF, GSPECIFICATION, EXTENSION],

        FULL_SIMP_TAC std_ss [INSERT_DEF, SUBSET_DEF, GSPECIFICATION, EXTENSION] THEN
        METIS_TAC[]
      ]
   ]);



val POWER_SET_FINITE=
 store_thm
  ("POWER_SET_FINITE",

   ``!s. FINITE (POWER_SET s) = FINITE s``,

   REPEAT STRIP_TAC THEN EQ_TAC THENL [
      Cases_on `s = {}` THENL [
         ASM_REWRITE_TAC[FINITE_EMPTY],


         ONCE_REWRITE_TAC [prove(``(a ==> b) = (~b ==> ~a)``, PROVE_TAC[])] THEN
         ASM_SIMP_TAC std_ss [POWER_SET_def, GSYM INFINITE_DEF] THEN
         REPEAT STRIP_TAC THEN     
             
         `?t. t = {x | x SUBSET s}` by METIS_TAC[] THEN
         `?t'. t' = {{x} | x IN s}` by METIS_TAC[] THEN
         SUBGOAL_TAC `t' SUBSET t` THEN1 (
           ASM_SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION] THEN
           PROVE_TAC[IN_SING]
         ) THEN
         `?f. f = (\x:'a. {x})` by METIS_TAC[] THEN
         SUBGOAL_TAC `(!x y. (f x = f y) = (x = y))` THEN1 (
           ASM_SIMP_TAC std_ss [EXTENSION, IN_SING] THEN 
           PROVE_TAC[]
         ) THEN
         SUBGOAL_TAC `t' = IMAGE f s` THEN1 (
           ASM_SIMP_TAC std_ss [EXTENSION, IN_IMAGE, GSPECIFICATION]
         ) THEN
         `INFINITE t'` by METIS_TAC[INJECTIVE_IMAGE_FINITE, INFINITE_DEF] THEN
         METIS_TAC[INFINITE_SUBSET]
      ],


      SPEC_TAC (``s:'a set``,``s:'a set``) THEN
      SET_INDUCT_TAC THENL [
         SIMP_TAC std_ss [POWER_SET_def, SUBSET_EMPTY, FINITE_SING, GSPEC_EQ],

         ASM_SIMP_TAC std_ss [POWER_SET_IND_THM, FINITE_UNION, IMAGE_FINITE]
      ]
   ])


val IMAGE_DIFF =
 store_thm
  ("IMAGE_DIFF",

   ``!f S1 S2. (INJ f (S1 UNION S2) UNIV) ==> ((IMAGE f (S1 DIFF S2)) = ((IMAGE f S1) DIFF (IMAGE f S2)))``,

   SIMP_TAC std_ss [INJ_DEF,
                  IN_UNION,
                  IN_UNIV,
                  IMAGE_DEF,
                  DIFF_DEF,
                  EXTENSION,
                  GSPECIFICATION] THEN
   METIS_TAC[]);


val IMAGE_ID_SUBSET =
 store_thm
  ("IMAGE_ID_SUBSET",

   ``!f S. (!x. (x IN S) ==> (f x = x)) ==> (IMAGE f S = S)``,

   REPEAT STRIP_TAC THEN
   SIMP_TAC std_ss [IMAGE_DEF, EXTENSION, GSPECIFICATION] THEN
   METIS_TAC[]);



val LIST_EQ_ELEM_THM =
 store_thm
  ("LIST_EQ_ELEM_THM",
   ``!l1 l2. (l1 = l2) = ((LENGTH l1 = LENGTH l2) /\ (!n. (n < LENGTH l1) ==> (EL n l1 = EL n l2)))``,

   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      ASM_REWRITE_TAC[],
      ASM_REWRITE_TAC[],

      UNDISCH_ALL_TAC THEN
      SPEC_TAC (``l1:'a list``, ``l1:'a list``) THEN
      SPEC_TAC (``l2:'a list``, ``l2:'a list``) THEN
      Induct_on `l1` THEN Induct_on `l2` THEN SIMP_TAC list_ss [] THEN
      REPEAT STRIP_TAC THENL [
         `0 < SUC (LENGTH l2)` by DECIDE_TAC THEN
         `EL 0 (h'::l1) = EL 0 (h::l2)` by PROVE_TAC[] THEN
         FULL_SIMP_TAC list_ss [],

         REMAINS_TAC `!n. n < LENGTH l1 ==> (EL n l1 = EL n l2)` THEN1 (
            PROVE_TAC[]
         ) THEN
         REPEAT STRIP_TAC THEN
         `SUC n < SUC (LENGTH l2)` by DECIDE_TAC THEN
         `EL (SUC n) (h'::l1) = EL (SUC n) (h::l2)` by PROVE_TAC[] THEN
         FULL_SIMP_TAC list_ss []
      ]
   ]);




val SOME_EL_IS_EL =
 store_thm
    ("SOME_EL_IS_EL",
    ``!P l. (SOME_EL P l) = (?e. IS_EL e l /\ P e)``,

    Induct_on `l` THENL [
        SIMP_TAC list_ss [],

        SIMP_TAC list_ss [] THEN
        PROVE_TAC[]
    ]);


val SOME_EL___IMPL =
 store_thm 
    ("SOME_EL___IMPL",
    ``!P Q l. ((SOME_EL P l) /\ (!e. P e ==> Q e)) ==> (SOME_EL Q l)``,

    Induct_on `l` THENL [
        REWRITE_TAC[EXISTS_DEF, listTheory.EXISTS_DEF],
    
        REWRITE_TAC[EXISTS_DEF, listTheory.EXISTS_DEF] THEN
        PROVE_TAC[]
    ]);
    

val MAP_EQ_APPEND =
 store_thm
  ("MAP_EQ_APPEND",

   ``!l f l1 l2. (MAP f l = APPEND l1 l2) = 
            (?l1' l2'. (l = APPEND l1' l2') /\ (l1 = MAP f l1') /\ (l2 = MAP f l2'))``,


Induct_on `l1` THENL [
  SIMP_TAC list_ss [] THEN 
  PROVE_TAC[],

  REPEAT STRIP_TAC THEN
  Cases_on `l` THENL [
    SIMP_TAC list_ss [],

    ASM_SIMP_TAC list_ss [] THEN
    EQ_TAC THEN STRIP_TAC THENL [
      Q_TAC EXISTS_TAC `h'::l1'` THEN
      Q_TAC EXISTS_TAC `l2'` THEN
      ASM_SIMP_TAC list_ss [],

      Cases_on `l1'` THEN
      FULL_SIMP_TAC list_ss [] THEN
      Q_TAC EXISTS_TAC `t'` THEN
      Q_TAC EXISTS_TAC `l2'` THEN
      ASM_SIMP_TAC list_ss []
    ]
  ]
])

val MAP_SING_LIST =
 store_thm
  ("MAP_SING_LIST",

   ``!e l f. ([e] = MAP f l) =
             (?e'. (l = [e']) /\ (e = f e'))``,

    Cases_on `l` THENL [
      SIMP_TAC list_ss [],
      
      SIMP_TAC list_ss [] THEN
      PROVE_TAC[]
    ]);


val FINITE_INJ_EXISTS =
 store_thm
  ("FINITE_INJ_EXISTS",
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
      SUBGOAL_TAC `?x. ~(x IN (IMAGE f (s :'a set))) /\ ~(x IN (S2:'a set)) /\ ~(x IN (S3:'a set))` THEN1(
         `FINITE ((IMAGE f s) UNION S2 UNION S3)` by METIS_TAC[IMAGE_FINITE, FINITE_UNION] THEN
         PROVE_TAC[NOT_IN_FINITE, IN_UNION]
      ) THEN
      EXISTS_TAC ``\z:'a. (if z = e then x:'a else (if (f z) = x then (f e) else (f z)))`` THEN
      REPEAT STRIP_TAC THENL [
        REWRITE_ALL_TAC [INJ_DEF, IN_UNIV] THEN METIS_TAC[],

        FULL_SIMP_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL, IN_IMAGE] THEN
        PROVE_TAC[],

        UNDISCH_HD_TAC THEN ASM_SIMP_TAC std_ss [],

        `~(x' = e) /\ ~(f x' = x)` by PROVE_TAC[] THEN
        ASM_SIMP_TAC std_ss []
      ]
   ]);




val POWER_SET_VARRENAMING_EXISTS =
 store_thm
  ("POWER_SET_VARRENAMING_EXISTS",
   ``!(S1:'a set) (S2:'a set). (FINITE S1 /\ FINITE S2 /\ INFINITE (UNIV:'a set)) ==>
   (?f. INJ f (POWER_SET S1) UNIV /\ (DISJOINT (IMAGE f (POWER_SET S1)) S2))``,

   REPEAT STRIP_TAC THEN
   `FINITE (POWER_SET S1)` by PROVE_TAC[POWER_SET_FINITE] THEN
   UNDISCH_TAC ``FINITE (POWER_SET S1)`` THEN
   `?S3. POWER_SET S1 = S3` by PROVE_TAC[] THEN
   ASM_REWRITE_TAC[] THEN
   SPEC_TAC (``S3:'a set set``,``S3:'a set set``) THEN
   SET_INDUCT_TAC THENL [
      SIMP_TAC std_ss [INJ_DEF, NOT_IN_EMPTY, IMAGE_EMPTY, DISJOINT_EMPTY],

      CLEAN_ASSUMPTIONS_TAC THEN
      `FINITE ((IMAGE f s) UNION S2)` by PROVE_TAC[FINITE_UNION, IMAGE_FINITE] THEN
      `?x. ~(x IN (IMAGE f s)) /\ ~(x IN S2)` by PROVE_TAC[NOT_IN_FINITE, IN_UNION] THEN
      EXISTS_TAC ``\z:'a set. (if z = e then x:'a else (f z))`` THEN
      REPEAT STRIP_TAC THENL [
        FULL_SIMP_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, INJ_DEF, IN_INSERT, IN_UNIV, SUBSET_DEF, IN_COMPL, IN_IMAGE] THEN 
        METIS_TAC[],

        FULL_SIMP_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, IN_INSERT, SUBSET_DEF, IN_COMPL, IMAGE_INSERT, IN_IMAGE] THEN 
        METIS_TAC[]
      ]
   ]);



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


val PAIR_BETA_THM =
 store_thm
  ("PAIR_BETA_THM",

  ``!P X. ((\(x1,x2). P x1 x2) X) = (P (FST X) (SND X))``,

    Cases_on `X` THEN
    SIMP_TAC std_ss []);

val PAIR_BETA_THM_3 =
 store_thm
  ("PAIR_BETA_THM_3",

  ``!P X. ((\(x1,x2,x3). P x1 x2 x3) X) = (P (FST X) (FST (SND X)) (SND (SND X)))``,

    Cases_on `X` THEN Cases_on `r` THEN
    SIMP_TAC std_ss []);


val PAIR_BETA_THM_4 =
 store_thm
  ("PAIR_BETA_THM_4",

  ``!P X. ((\(x1,x2,x3,x4). P x1 x2 x3 x4) X) = (P (FST X) (FST (SND X)) (FST (SND (SND X))) (SND (SND (SND X))))``,

    Cases_on `X` THEN Cases_on `r` THEN
    SIMP_TAC std_ss []);


val SUC_MOD_CASES =
 store_thm ("SUC_MOD_CASES",

  ``!n m. 0 < n ==>
  ((((SUC m) MOD n) = 0) \/ (((SUC m) MOD n) = (SUC (m MOD n))))``,
  
  REPEAT STRIP_TAC THEN
  Cases_on `n = 1` THENL [
    ASM_REWRITE_TAC[MOD_1],
  
    SUBGOAL_TAC `(SUC m) MOD n = ((SUC (m MOD n)) MOD n)` THEN1 (
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

val IN_BETA_THM =
 store_thm
  ("IN_BETA_THM",
  ``!f x. x IN (\x. f x) = f x``, 
  SIMP_TAC std_ss [IN_DEF]
  )


val PRED_SET_FORALL_def =
  Define `PRED_SET_FORALL P set = !s. s IN set ==> P s`;


val PRED_SET_FORALL_EMPTY =
  store_thm ("PRED_SET_FORALL_EMPTY",
    ``!P. PRED_SET_FORALL P EMPTY``,
      REWRITE_TAC[PRED_SET_FORALL_def, NOT_IN_EMPTY]);


val PRED_SET_FORALL_INSERT =
  store_thm ("PRED_SET_FORALL_INSERT",
    ``!P s set. PRED_SET_FORALL P (s INSERT set) = (P s /\ PRED_SET_FORALL P set)``,

    SIMP_TAC std_ss [PRED_SET_FORALL_def, IN_INSERT] THEN
    PROVE_TAC[]);


val COND_IMP_EQ_def =    
  Define `COND_IMP_EQ c A B = if c then A=B else A ==> B` 

val COND_IMP_EQ___REWRITE =    
  store_thm ("COND_IMP_EQ___REWRITE", 
    ``!c A B. COND_IMP_EQ c A B =
             ((A ==> B) /\ (c ==> (A = B)))``,
      SIMP_TAC std_ss [COND_IMP_EQ_def] THEN
      METIS_TAC[]);


val POS_START_def =
  Define `
    (POS_START n [] h = 0) /\
    (POS_START n (h'::l) h = (if (h = h') then (SUC n) else (POS_START (SUC n) l h)))`


val POS_START_NOT_FOUND =
  store_thm ("POS_START_NOT_FOUND",
    ``!n l h. ((POS_START n l h = 0) = ~(MEM h l))``,

    Induct_on `l` THENL [
      SIMP_TAC list_ss [POS_START_def],

      ASM_SIMP_TAC list_ss [POS_START_def] THEN
      REPEAT GEN_TAC THEN
      Cases_on `h' = h` THENL [
        ASM_SIMP_TAC arith_ss [],
        ASM_REWRITE_TAC[]
      ]
    ]);

val POS_START_FOUND =
  store_thm ("POS_START_FOUND",
    ``!n l h. (MEM h l ==> (POS_START n l h > n) /\ (EL ((PRE (POS_START n l h)) - n) l = h))``,

    Induct_on `l` THENL [
      SIMP_TAC list_ss [],

      ASM_SIMP_TAC list_ss [POS_START_def] THEN
      REPEAT GEN_TAC THEN
      Cases_on `h' = h` THENL [
        ASM_SIMP_TAC list_ss [],

        ASM_SIMP_TAC list_ss [] THEN
        STRIP_TAC THEN
        Q_SPECL_NO_ASSUM 2 [`SUC n`, `h'`] THEN
        UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL [
          ASM_SIMP_TAC arith_ss [],
          Cases_on `(POS_START (SUC n) l h')` THEN (
            SIMP_ALL_TAC arith_ss []
          ) THEN
          Cases_on `n'` THEN SIMP_ALL_TAC arith_ss [] THEN
          `SUC n'' - n = SUC (n'' - n)` by DECIDE_TAC THEN
          ASM_SIMP_TAC list_ss []
        ]
      ]
    ]);


val POS_START_RANGE =
  store_thm ("POS_START_RANGE",
    ``!n l h. (POS_START n l h > n) \/ (POS_START n l h = 0)``,
    PROVE_TAC[POS_START_FOUND, POS_START_NOT_FOUND]);


val COND_EXPAND_IMP =
  store_thm (
    "COND_EXPAND_IMP",
    ``!b t1 t2. (if b then t1 else t2) = ((b ==> t1) /\ (~b ==> t2))``,
    PROVE_TAC[]);



val INTERVAL_SET_def =
  Define `
    INTERVAL_SET (n1:num) (n2:num) = {x:num | n1 <= x /\ x <= n2}`
    
val COUNT_LIST_def =
  Define `
    (COUNT_LIST 0 x = []) /\
    (COUNT_LIST (SUC n) x = (n + x)::(COUNT_LIST n x))`


val INTERVAL_LIST_def =
  Define `
    INTERVAL_LIST (n1:num) (n2:num) =
      REVERSE (COUNT_LIST ((SUC n2) - n1) n1)`


val IN_INTERVAL_SET =
  store_thm ("IN_INTERVAL_SET", 
    ``!n n1 n2. (n IN INTERVAL_SET n1 n2) = (n1 <= n /\ n <= n2)``,
    SIMP_TAC std_ss [INTERVAL_SET_def, GSPECIFICATION]);


val INTERVAL_SET_SING =
  store_thm ("INTERVAL_SET_SING", 
    ``!n. (INTERVAL_SET n n) = {n}``,
    SIMP_TAC std_ss [INTERVAL_SET_def, GSPECIFICATION, EXTENSION, IN_SING] THEN
    DECIDE_TAC);


val MEM_COUNT_LIST =
  store_thm ("MEM_COUNT_LIST", 
    ``!n m x. (MEM n (COUNT_LIST m x)) = (x <= n /\ n < m+x)``,
    
    Induct_on `m` THENL [
      SIMP_TAC list_ss [COUNT_LIST_def],    
      ASM_SIMP_TAC list_ss [COUNT_LIST_def]
    ]);


val MEM_INTERVAL_LIST =
  store_thm ("MEM_INTERVAL_LIST", 
    ``!n m0 m1. ((MEM n (INTERVAL_LIST m0 m1)) = (m0 <= n /\ n <= m1))``,
    
    SIMP_TAC std_ss [INTERVAL_LIST_def, MEM_MAP, MEM_COUNT_LIST,
      MEM_REVERSE] THEN
    ASM_SIMP_TAC arith_ss [])

val COUNT_LIST_THM =
  store_thm ("COUNT_LIST_THM", 
    ``!n x. COUNT_LIST n x =
              if (n > 0) then (((PRE n)+x)::COUNT_LIST (PRE n) x) else []``,

  Cases_on `n` THEN
  SIMP_TAC std_ss [COUNT_LIST_def]);


val INTERVAL_LIST_THM =
  store_thm ("INTERVAL_LIST_THM", 
    ``!n1 n2. ((n1 <= n2) ==> (INTERVAL_LIST n1 n2 = (n1::INTERVAL_LIST (SUC n1) n2))) /\
              ((n2 < n1) ==> (INTERVAL_LIST n1 n2 = []))``,

      SIMP_TAC std_ss [INTERVAL_LIST_def] THEN
      REPEAT GEN_TAC THEN
      REPEAT STRIP_TAC THENL [
        `(SUC n2 - n1 = SUC (n2 - n1)) /\ (n1 <= n2)` by DECIDE_TAC THEN
        `?a. n2 - n1 = a` by METIS_TAC[] THEN
        FULL_SIMP_TAC std_ss [] THEN
        REPEAT WEAKEN_HD_TAC THEN
        Induct_on `a` THENL [
          SIMP_TAC list_ss [COUNT_LIST_def],
          FULL_SIMP_TAC list_ss [COUNT_LIST_def, REVERSE_APPEND]
        ],

        `(SUC n2 - n1 = 0) /\ (n2 - n1 = 0) /\ ~(n1 <= n2)` by DECIDE_TAC THEN
        ASM_REWRITE_TAC[COUNT_LIST_def, REVERSE]
      ]);
        

val MEM_INTERVAL_LIST =
  store_thm ("MEM_INTERVAL_LIST", 
    ``!n m0 m1. ((MEM n (INTERVAL_LIST m0 m1)) = (m0 <= n /\ n <= m1))``,
    
    SIMP_TAC list_ss [INTERVAL_LIST_def, MEM_MAP, MEM_COUNT_LIST])


val LIST_TO_SET___INTERVAL_LIST =
  store_thm ("LIST_TO_SET___INTERVAL_LIST", 
    ``!m0 m1. ((LIST_TO_SET (INTERVAL_LIST m0 m1)) = INTERVAL_SET m0 m1)``,
    
    REWRITE_TAC[EXTENSION, IN_LIST_TO_SET, MEM_INTERVAL_LIST,
      IN_INTERVAL_SET]);


val INTERVAL_SET___TO___COUNT =
  store_thm ("INTERVAL_SET___TO___COUNT", 
    ``(!n1 n2. (INTERVAL_SET n1 n2) = 
              IMAGE (\n. n + n1) (count ((SUC n2)-n1))) /\
      (!n. (INTERVAL_SET 0 n) = 
            (count (SUC n)))``,

    SIMP_TAC arith_ss [IN_COUNT, IN_INTERVAL_SET, EXTENSION,
      IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Q_TAC EXISTS_TAC `x - n1` THEN
      ASM_SIMP_TAC arith_ss [],

      DECIDE_TAC,
      DECIDE_TAC
    ]);


val FINITE_INTERVAL_SET =
  store_thm ("FINITE_INTERVAL_SET", 
    ``!n1 n2. FINITE (INTERVAL_SET n1 n2)``,
    SIMP_TAC std_ss [INTERVAL_SET___TO___COUNT, FINITE_COUNT,
      IMAGE_FINITE]);



val SET_BINARY_ENCODING_def =
  Define `SET_BINARY_ENCODING =
          SIGMA (\n:num. (2:num)**n)`;


val SET_BINARY_ENCODING___UNION =
  store_thm ("SET_BINARY_ENCODING___UNION",

``!S1 S2. DISJOINT S1 S2 /\ FINITE S1 /\ FINITE S2 ==>
(SET_BINARY_ENCODING (S1 UNION S2) =
(SET_BINARY_ENCODING S1 + SET_BINARY_ENCODING S2))``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [SET_BINARY_ENCODING_def, SUM_IMAGE_UNION] THEN
SUBGOAL_TAC `S1 INTER S2 = EMPTY` THEN1 (
  SIMP_ALL_TAC std_ss [DISJOINT_DISJ_THM, IN_INTER, EXTENSION, NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[]
) THEN
ASM_SIMP_TAC std_ss [SUM_IMAGE_THM]);



val SET_BINARY_ENCODING___SUBSET =
  store_thm ("SET_BINARY_ENCODING___SUBSET",

``
!S1 S2. S1 SUBSET S2 /\ FINITE S2 ==>
(SET_BINARY_ENCODING S1 <=
(SET_BINARY_ENCODING S2))``,

REPEAT STRIP_TAC THEN
`?S3. S3 = S2 DIFF S1` by METIS_TAC[] THEN
SUBGOAL_TAC `S2 = S3 UNION S1` THEN1 (
  SIMP_ALL_TAC std_ss [EXTENSION, IN_UNION, IN_DIFF, SUBSET_DEF] THEN
  PROVE_TAC[]
) THEN
ONCE_ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

ASSUME_TAC SET_BINARY_ENCODING___UNION THEN
Q_SPECL_NO_ASSUM 0 [`S3`, `S1`] THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 (
  REPEAT STRIP_TAC THENL [
    SIMP_ALL_TAC std_ss [DISJOINT_DISJ_THM, EXTENSION, IN_DIFF, IN_UNION, SUBSET_DEF] THEN
    PROVE_TAC[],
    
    PROVE_TAC[FINITE_DIFF],
    PROVE_TAC[SUBSET_FINITE]
  ] 
) THEN
ONCE_ASM_REWRITE_TAC[] THEN

SIMP_TAC std_ss []);
  



val SET_BINARY_ENCODING___COUNT =
  store_thm ("SET_BINARY_ENCODING___COUNT",
    ``(SET_BINARY_ENCODING (count 0) = 0) /\
      (!n:num. (n > 0) ==> (SET_BINARY_ENCODING (count n) =
          PRE (2**n)))``,

  LEFT_CONJ_TAC THENL [
    SIMP_TAC std_ss [COUNT_ZERO, SET_BINARY_ENCODING_def,
      SUM_IMAGE_THM],

    Induct_on `n` THENL [
      SIMP_TAC std_ss [],

      SIMP_TAC std_ss [COUNT_SUC, SET_BINARY_ENCODING_def,
        SUM_IMAGE_THM, FINITE_INSERT, FINITE_COUNT] THEN
      SUBGOAL_TAC `(count n DELETE n) = count n` THEN1 (
        SIMP_TAC arith_ss [EXTENSION, IN_DELETE, IN_COUNT]
      ) THEN
      ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN
      
      SIMP_ALL_TAC std_ss [SET_BINARY_ENCODING_def] THEN
      Cases_on `n` THEN FULL_SIMP_TAC std_ss [] THEN
      SIMP_TAC arith_ss [EXP]
    ]
  ]);

  

val SET_BINARY_ENCODING___REDUCE =
  store_thm ("SET_BINARY_ENCODING___REDUCE",
  ``!S. FINITE S ==> !n. DISJOINT S (count (SUC n)) ==> 
          ((SET_BINARY_ENCODING S) = (SET_BINARY_ENCODING (IMAGE (\x:num. x - SUC n) S)) * (2 ** (SUC n)))``,

SET_INDUCT_TAC THENL [
  SIMP_TAC std_ss [SET_BINARY_ENCODING_def, SUM_IMAGE_THM, IMAGE_EMPTY],

  FULL_SIMP_TAC std_ss [SET_BINARY_ENCODING_def, SUM_IMAGE_THM, IMAGE_INSERT, FINITE_INSERT, IMAGE_FINITE] THEN
  REPEAT STRIP_TAC THEN
  Q_SPEC_NO_ASSUM 2 `n` THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 (
    SIMP_ALL_TAC std_ss [DISJOINT_DISJ_THM, IN_INSERT] THEN
    PROVE_TAC[]
  ) THEN
  `(s DELETE e) = s` by PROVE_TAC[DELETE_NON_ELEMENT] THEN
  SUBGOAL_TAC `(IMAGE (\x. x - SUC n) s DELETE (e - SUC n)) =
               (IMAGE (\x. x - SUC n) s)` THEN1 (
    SIMP_TAC std_ss [EXTENSION, IN_IMAGE, IN_DELETE] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      PROVE_TAC[],
      PROVE_TAC[],
  
      SIMP_ALL_TAC std_ss [DISJOINT_DISJ_THM, IN_INSERT, IN_COUNT] THEN
      `~(e < SUC n) /\ ~(x' < SUC n)` by PROVE_TAC[] THEN
      `x' = e` by DECIDE_TAC THEN
      PROVE_TAC[]
    ]
  ) THEN
  ASM_SIMP_TAC std_ss [RIGHT_ADD_DISTRIB, GSYM EXP_ADD] THEN
  SUBGOAL_TAC `~(e < SUC n)` THEN1 (
    SIMP_ALL_TAC std_ss [DISJOINT_DISJ_THM, IN_INSERT, IN_COUNT] THEN
    METIS_TAC[]
  ) THEN
  `e - SUC n + SUC n = e` by DECIDE_TAC THEN
  ASM_REWRITE_TAC[]
]);


val SET_BINARY_ENCODING___BITS =
  store_thm ("SET_BINARY_ENCODING___BITS",
  ``!n S. FINITE S ==> (BIT n (SET_BINARY_ENCODING S) = (n IN S))``,

  REPEAT STRIP_TAC THEN
  `?S1. S1 = S INTER count n` by METIS_TAC[] THEN
  `?S2. S2 = S DIFF count (SUC n)` by METIS_TAC[] THEN 
  `?Sn. Sn = S INTER {n}` by METIS_TAC[] THEN 
  `FINITE S1 /\ FINITE Sn /\ FINITE S2` by PROVE_TAC[INTER_FINITE,
    FINITE_SING, FINITE_DIFF] THEN
  SUBGOAL_TAC `S = S1 UNION Sn UNION S2` THEN1 (
    ASM_SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF,
      IN_COUNT, IN_SING] THEN
    REPEAT STRIP_TAC THEN
    Cases_on `x IN S` THEN ASM_REWRITE_TAC[] THEN
    DECIDE_TAC
  ) THEN
  ONCE_ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

  SUBGOAL_TAC `SET_BINARY_ENCODING (S1 UNION Sn UNION S2) =
             SET_BINARY_ENCODING S1 + SET_BINARY_ENCODING Sn + SET_BINARY_ENCODING S2` THEN1 (
    SUBGOAL_TAC `DISJOINT S1 Sn /\ DISJOINT (S1 UNION Sn) S2` THEN1 (
      ASM_SIMP_TAC std_ss [DISJOINT_DISJ_THM, IN_INTER, IN_SING,
        IN_COUNT, IN_UNION, IN_DIFF] THEN
      REPEAT STRIP_TAC THEN
      Cases_on `x IN S` THEN ASM_REWRITE_TAC[] THEN
      DECIDE_TAC
    ) THEN
    NTAC 3 (GSYM_NO_TAC 7) THEN

    ASM_SIMP_TAC std_ss [FINITE_UNION, SET_BINARY_ENCODING___UNION] THEN
    GSYM_NO_TAC 0 (*Def Sn*) THEN
    ASM_SIMP_TAC std_ss [SET_BINARY_ENCODING_def]
  ) THEN
  
  SUBGOAL_TAC `n IN S1 UNION Sn UNION S2 =
               n IN Sn` THEN1 (
    ASM_SIMP_TAC arith_ss [IN_UNION, IN_INTER, IN_DIFF, IN_COUNT]
  ) THEN

  SUBGOAL_TAC `SET_BINARY_ENCODING S1 < 2**n` THEN1 (        
    ASSUME_TAC SET_BINARY_ENCODING___SUBSET THEN
    Q_SPECL_NO_ASSUM 0 [`S1`, `count n`] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 PROVE_TAC[FINITE_COUNT, INTER_SUBSET] THEN
    Cases_on `n` THENL [
      FULL_SIMP_TAC std_ss [SET_BINARY_ENCODING___COUNT],

      SIMP_ALL_TAC std_ss [SET_BINARY_ENCODING___COUNT] THEN
      `~(((2:num) ** (SUC n')) = 0)` by SIMP_TAC arith_ss [EXP_EQ_0] THEN
      DECIDE_TAC
    ]
  ) THEN

  SUBGOAL_TAC `?a. SET_BINARY_ENCODING S2 = a* 2**(SUC n)` THEN1 (        
    ASSUME_TAC SET_BINARY_ENCODING___REDUCE THEN
    Q_SPEC_NO_ASSUM 0 `S2` THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 ASM_REWRITE_TAC[] THEN
    Q_SPEC_NO_ASSUM 0 `n` THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 (
      ASM_REWRITE_TAC[DISJOINT_DISJ_THM, IN_DIFF] THEN
      PROVE_TAC[]
    ) THEN
    PROVE_TAC[]
  ) THEN

  `?nc:num. (if n IN S then 1 else 0) = nc` by METIS_TAC[] THEN
  
  SUBGOAL_TAC `SET_BINARY_ENCODING Sn = nc* 2**n` THEN1 (        
    ASM_SIMP_TAC std_ss [] THEN
    Cases_on `n IN S` THENL [
      SUBGOAL_TAC `S INTER {n} = {n}` THEN1 (
        ASM_SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_SING] THEN
        GEN_TAC THEN
        BOOL_EQ_STRIP_TAC
      ) THEN
      `nc = 1` by FULL_SIMP_TAC std_ss [] THEN
      ASM_SIMP_TAC std_ss [SET_BINARY_ENCODING_def,
        SUM_IMAGE_SING],

      SUBGOAL_TAC `S INTER {n} = EMPTY` THEN1 (
        ASM_SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_SING, NOT_IN_EMPTY] 
      ) THEN
      `nc = 0` by FULL_SIMP_TAC std_ss [] THEN
      ASM_SIMP_TAC std_ss [SET_BINARY_ENCODING_def,
        SUM_IMAGE_THM]
    ]
  ) THEN
  
  NTAC 2 (WEAKEN_NO_TAC 10) (*Def S1, S2*) THEN
  ASM_SIMP_TAC std_ss [IN_INTER, IN_SING, BIT_def] THEN


  ASSUME_TAC BITS_SUM THEN
  Q_SPECL_NO_ASSUM 0 [`n`, `n`, `nc + 2*a`, `SET_BINARY_ENCODING S1`] THEN
  UNDISCH_HD_TAC THEN
  ASM_SIMP_TAC arith_ss [RIGHT_ADD_DISTRIB] THEN
  SUBGOAL_TAC `2 * (a * 2 ** n) = a * 2 ** SUC n` THEN1 (
    SIMP_TAC arith_ss [EXP]
  ) THEN
  ASM_SIMP_TAC std_ss [] THEN
  DISCH_TAC THEN WEAKEN_HD_TAC THEN


  ASM_SIMP_TAC std_ss [BITS_SUM2] THEN

  REWRITE_TAC[GSYM BIT_def] THEN
  Cases_on `n IN S` THENL [
    `nc = 1` by PROVE_TAC[] THEN
    ASM_SIMP_TAC std_ss [BIT_B],

    `nc = 0` by PROVE_TAC[] THEN
    ASM_SIMP_TAC std_ss [BIT_ZERO]
  ]
);





val SET_BINARY_ENCODING___INJ =
  store_thm ("SET_BINARY_ENCODING___INJ",
  ``!S. FINITE S ==> INJ SET_BINARY_ENCODING (POWER_SET S) UNIV``,

  SIMP_TAC std_ss [INJ_DEF, IN_UNIV, IN_POWER_SET_SUBSET_EQUIV, EXTENSION] THEN
  PROVE_TAC[SET_BINARY_ENCODING___BITS, SUBSET_FINITE]);




val SET_BINARY_ENCODING_SHIFT_def =
  Define `
    SET_BINARY_ENCODING_SHIFT n1 n2 S =
      (SET_BINARY_ENCODING (IMAGE (\n. n - n1) S) + n2)`;


val SET_BINARY_ENCODING_SHIFT___INJ =
  store_thm ("SET_BINARY_ENCODING_SHIFT___INJ",
  ``!S n1 n2. (FINITE S /\ (!n. n IN S ==> n >= n1)) ==> INJ (SET_BINARY_ENCODING_SHIFT n1 n2) (POWER_SET S) UNIV``,

  
  SIMP_TAC std_ss [SET_BINARY_ENCODING_SHIFT_def, INJ_DEF, IN_UNIV] THEN
  REPEAT STRIP_TAC THEN
  `?f. (\n:num. n - n1) = f` by PROVE_TAC[] THEN
  FULL_SIMP_TAC std_ss [] THEN
  SUBGOAL_TAC `(IMAGE f x) IN POWER_SET (IMAGE f S) /\
               (IMAGE f y) IN POWER_SET (IMAGE f S)`  THEN1 (
    FULL_SIMP_TAC std_ss [IN_POWER_SET_SUBSET_EQUIV, IMAGE_SUBSET]
  ) THEN
  `FINITE (IMAGE f S)` by ASM_SIMP_TAC std_ss [IMAGE_FINITE] THEN
  `IMAGE f x = IMAGE f y` by METIS_TAC[SET_BINARY_ENCODING___INJ, INJ_DEF] THEN
  UNDISCH_HD_TAC THEN IMP_TO_EQ_TAC THEN
  MATCH_MP_TAC INJECTIVE_IMAGE_EQ THEN

  REPEAT STRIP_TAC THEN
  SUBGOAL_TAC `x' >= n1 /\ y' >= n1` THEN1 (
    SIMP_ALL_TAC std_ss [IN_POWER_SET_SUBSET_EQUIV, IN_UNION, SUBSET_DEF] THEN
    PROVE_TAC[]
  ) THEN
  UNDISCH_NO_TAC 2 THEN GSYM_NO_TAC 7 THEN
  ASM_SIMP_TAC arith_ss []);




val SET_BINARY_ENCODING___IMAGE_THM =
  store_thm ("SET_BINARY_ENCODING___IMAGE_THM",

  ``!n. IMAGE SET_BINARY_ENCODING (POWER_SET (
    INTERVAL_SET 0 n)) =
        INTERVAL_SET 0 (PRE (2**(SUC n)))``,

    Induct_on `n` THENL [
      SIMP_TAC std_ss [EXTENSION, IN_INTERVAL_SET, IN_IMAGE, IN_POWER_SET_SUBSET_EQUIV, SUBSET_DEF, SET_BINARY_ENCODING_def] THEN
      Cases_on `x` THENL [
        SIMP_TAC std_ss [] THEN
        EXISTS_TAC ``EMPTY:num set`` THEN
        SIMP_TAC std_ss [SUM_IMAGE_THM, NOT_IN_EMPTY],

        Cases_on `SUC n <= 1` THENL [
          `n = 0` by DECIDE_TAC THEN
          ASM_SIMP_TAC std_ss [] THEN
          EXISTS_TAC ``{0:num}`` THEN
          SIMP_TAC std_ss [IN_SING, SUM_IMAGE_SING],


          ASM_SIMP_TAC std_ss [] THEN
          GEN_TAC THEN 
          LEFT_DISJ_TAC THEN
          Cases_on `x' = EMPTY` THENL [
            ASM_SIMP_TAC arith_ss [SUM_IMAGE_THM],

            FULL_SIMP_TAC std_ss [] THEN
            `?e. e IN x'` by PROVE_TAC[MEMBER_NOT_EMPTY] THEN
            SUBGOAL_TAC `x' = {0}` THEN1 (
              FULL_SIMP_TAC std_ss [EXTENSION, IN_SING, NOT_IN_EMPTY] THEN
              METIS_TAC[]
            ) THEN
            ASM_SIMP_TAC arith_ss [IN_SING, SUM_IMAGE_SING]
          ]
        ]
      ],

      
      SUBGOAL_TAC `(POWER_SET (INTERVAL_SET 0 (SUC n))) =
                   ((POWER_SET (INTERVAL_SET 0 n)) UNION
                    (IMAGE (\S. (SUC n) INSERT S) (POWER_SET (INTERVAL_SET 0 n))))` THEN1 (
        SIMP_TAC arith_ss [EXTENSION, IN_UNION, IN_POWER_SET_SUBSET_EQUIV,
          SUBSET_DEF, IN_INTERVAL_SET, IN_IMAGE] THEN
        REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
          Cases_on `SUC n IN x` THENL [
            DISJ2_TAC THEN
            Q_TAC EXISTS_TAC `x DELETE SUC n` THEN
            ASM_SIMP_TAC arith_ss [INSERT_DELETE] THEN
            ASM_SIMP_TAC arith_ss [IN_DELETE] THEN
            REPEAT STRIP_TAC THEN
            `x' <= SUC n` by PROVE_TAC[] THEN
            DECIDE_TAC,

            DISJ1_TAC THEN
            REPEAT STRIP_TAC THEN
            `x' <= SUC n /\ ~(x' = SUC n)` by PROVE_TAC[] THEN
            DECIDE_TAC
          ],

          `x' <= n` by PROVE_TAC[] THEN
          DECIDE_TAC,

          `(x' = SUC n) \/ (x' IN S')` by PROVE_TAC[IN_INSERT] THENL [
            ASM_SIMP_TAC std_ss [],

            `x' <= n` by PROVE_TAC[] THEN
            DECIDE_TAC
          ]
        ]
      ) THEN
      ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

      ASM_SIMP_TAC std_ss [IMAGE_UNION] THEN

      SUBGOAL_TAC `IMAGE SET_BINARY_ENCODING
      (IMAGE (\S. SUC n INSERT S) (POWER_SET (INTERVAL_SET 0 n))) =
       IMAGE (\x. 2**(SUC n) + x) (IMAGE SET_BINARY_ENCODING
        (POWER_SET (INTERVAL_SET 0 n)))` THEN1 (
        ONCE_REWRITE_TAC [EXTENSION] THEN
        SIMP_TAC std_ss [IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
        GEN_TAC THEN
        EXISTS_EQ_STRIP_TAC THEN
        BOOL_EQ_STRIP_TAC THEN
        MATCH_MP_TAC (prove (``(A = B) ==> ((x = A) = (x = B))``, PROVE_TAC[])) THEN

        `FINITE S'` by PROVE_TAC[IN_POWER_SET_SUBSET_EQUIV,
          SUBSET_FINITE, FINITE_INTERVAL_SET] THEN
        ASM_SIMP_TAC std_ss [SET_BINARY_ENCODING_def, SUM_IMAGE_THM] THEN
        REMAINS_TAC `~(SUC n IN S')` THEN1 PROVE_TAC[DELETE_NON_ELEMENT] THEN
        SIMP_ALL_TAC std_ss [IN_POWER_SET_SUBSET_EQUIV, SUBSET_DEF, IN_INTERVAL_SET] THEN
        `~(SUC n <= n)` by DECIDE_TAC THEN
        METIS_TAC[]
      ) THEN
      ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

      
      ONCE_REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN
      SIMP_TAC std_ss [IN_UNION, IN_IMAGE, IN_INTERVAL_SET, EXP] THEN
      EQ_TAC THEN REPEAT STRIP_TAC THENL [
        ASM_SIMP_TAC arith_ss [],
        ASM_SIMP_TAC arith_ss [],

        RIGHT_DISJ_TAC THEN
        Q_TAC EXISTS_TAC `x - (2 * 2**n)` THEN
        FULL_SIMP_TAC arith_ss []
      ]
    ])
      
      



val SET_BINARY_ENCODING_SHIFT___IMAGE_THM =
  store_thm ("SET_BINARY_ENCODING_SHIFT___IMAGE_THM",
  ``!n1 n2 n3. n1 <= n2 ==> (IMAGE (SET_BINARY_ENCODING_SHIFT n1 n3) (POWER_SET (
    INTERVAL_SET n1 n2)) =
        INTERVAL_SET n3 (n3 + (PRE (2**(SUC (n2 - n1))))))``,

    REPEAT STRIP_TAC THEN

    SUBGOAL_TAC `INTERVAL_SET n3 (n3 + PRE (2 ** SUC (n2 - n1))) =
                 IMAGE (\x:num. x + n3) (INTERVAL_SET 0 (PRE (2 ** SUC (n2 - n1))))` THEN1 (
      ONCE_REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN
      SIMP_TAC std_ss [IN_INTERVAL_SET, IN_IMAGE] THEN
      EQ_TAC THEN REPEAT STRIP_TAC THENL [
        Q_TAC EXISTS_TAC `x-n3` THEN
        ASM_SIMP_TAC std_ss [] THEN
        WEAKEN_HD_TAC THEN
        DECIDE_TAC,

        WEAKEN_HD_TAC THEN
        DECIDE_TAC,

        ASM_SIMP_TAC arith_ss []
      ]
    ) THEN
    ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

    ASSUME_TAC (GSYM SET_BINARY_ENCODING___IMAGE_THM) THEN
    Q_SPEC_NO_ASSUM 0 `n2 - n1` THEN
    ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

    
    ONCE_REWRITE_TAC[EXTENSION] THEN
    SIMP_TAC std_ss [IN_IMAGE, SET_BINARY_ENCODING_SHIFT_def,
      GSYM RIGHT_EXISTS_AND_THM, IN_POWER_SET_SUBSET_EQUIV] THEN
    GEN_TAC THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Q_TAC EXISTS_TAC `(IMAGE (\n. n - n1) x')` THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_ALL_TAC std_ss [SUBSET_DEF, IN_INTERVAL_SET, IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN
      RES_TAC THEN
      DECIDE_TAC,


      Q_TAC EXISTS_TAC `(IMAGE (\n. n + n1) x'')` THEN
      ASM_SIMP_TAC arith_ss [GSYM IMAGE_COMPOSE, combinTheory.o_DEF,
        IMAGE_ID] THEN
      SIMP_ALL_TAC std_ss [SUBSET_DEF, IN_INTERVAL_SET, IN_IMAGE] THEN
      GEN_TAC THEN STRIP_TAC THEN
      RES_TAC THEN
      DECIDE_TAC
    ]);


val POWER_SET_SUBSET =
  store_thm ("POWER_SET_SUBSET",
    ``!s t. (POWER_SET s SUBSET POWER_SET t) = s SUBSET t``,

   SIMP_TAC std_ss [SUBSET_DEF, IN_POWER_SET_SUBSET_EQUIV] THEN
   PROVE_TAC[]);




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

