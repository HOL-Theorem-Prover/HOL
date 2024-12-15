open HolKernel Parse boolLib bossLib;

(*
quietdec := true;
loadPath :=
            (concat [Globals.HOLDIR, "/examples/decidable_separationLogic/src"]) ::
            !loadPath;

map load ["finite_mapTheory", "relationTheory", "congLib", "sortingTheory",
   "rich_listTheory"];
show_assums := true;
*)

open finite_mapTheory relationTheory pred_setTheory congLib sortingTheory
   listTheory rich_listTheory;

(*
load "decidable_separationLogicTheory";
open decidable_separationLogicTheory;

quietdec := false;
*)

val _ = new_theory "decidable_separationLogic";
val _ = ParseExtras.temp_loose_equality()
val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj"]
val list_ss = list_ss -* ["lift_disj_eq", "lift_imp_disj"]
val ONE = arithmeticTheory.ONE
val TWO = arithmeticTheory.TWO

(*general stuff*)

fun MP_FREE_VAR_TAC var =
   POP_ASSUM_LIST (fn thmL =>
      EVERY (rev
      (map (fn thm => if var IN FVs (concl thm) then MP_TAC thm else ASSUME_TAC thm) thmL)));

local
   val thm = prove (“(!x. (P x = Q x)) ==> ((?x. P x) = (?x. Q x))”, METIS_TAC[]);
in
   val STRIP_EQ_EXISTS_TAC =
      HO_MATCH_MP_TAC thm THEN
      GEN_TAC
end


local
   val thm = prove (“(!x. (P x = Q x)) ==> ((!x. P x) = (!x. Q x))”, METIS_TAC[]);
in
   val STRIP_EQ_FORALL_TAC =
      HO_MATCH_MP_TAC thm THEN
      GEN_TAC
end


local
   fun find_in_lists_helper l1 [] l r = r |
       find_in_lists_helper [] (e::l2) l r =
         find_in_lists_helper l l2 l r |
       find_in_lists_helper (e1::l1) (e2::l2) l r =
         if (aconv e1 e2) then
            find_in_lists_helper l1 (e2::l2) l (e1::r) else
         find_in_lists_helper l1 (e2::l2) l r;

   fun find_in_lists l1 l2 = find_in_lists_helper l1 l2 l1 [];


   fun strip_conj_disj t =
      if is_conj t then
         strip_conj t
      else
         strip_disj t;

   fun RHS_LHS_CONV c =
      (TRY_CONV (RHS_CONV c)) THENC
      (TRY_CONV (LHS_CONV c));

in
   fun STRIP_EQ_BOOL_TAC (asm, g') =
      let
         val g'' = (rhs (concl (
            (RHS_LHS_CONV (REWR_CONV IMP_DISJ_THM) g')))) handle _ => g';
         val (l, r) = dest_eq g'';

         val lL = strip_conj_disj l;
         val rL = strip_conj_disj r;

         val commonL = find_in_lists lL rL;
         val commonL = map (fn t => fst (strip_neg t)) commonL;

         val tac = EVERY (map (fn t => (ASM_CASES_TAC t THEN ASM_REWRITE_TAC[])) commonL)
      in
         tac (asm, g')
      end
end;



val PAIR_BETA_THM = store_thm ("PAIR_BETA_THM",
“!f. (\x. f x (FST x) (SND x)) = (λ(x1,x2). f (x1,x2) x1 x2)”,

   SIMP_TAC std_ss [FUN_EQ_THM] THEN
   Cases_on ‘x’ THEN
   SIMP_TAC std_ss []
);

val EL_DISJOINT_FILTER = store_thm ("EL_DISJOINT_FILTER",

   “!n1 n2 P l. (~(n1 = n2) /\ (n1 < LENGTH l) /\ (n2 < LENGTH l) /\
                   (EL n1 l = EL n2 l) /\ (P (EL n2 l))) ==>
                 ?n1' n2'. ~(n1' = n2') /\
                           (n1' < LENGTH (FILTER P l)) /\
                           (n2' < LENGTH (FILTER P l)) /\
                           (EL n1' (FILTER P l) = EL n2 l) /\
                           (EL n2' (FILTER P l) = EL n2 l)”,

   HO_MATCH_MP_TAC (prove (“((!n1 n2. P n1 n2 = P n2 n1) /\ (!n1 n2. (n1 <= n2) ==> P n1 n2)) ==>
                             (!n1 n2. P n1 n2)”,
                    METIS_TAC[arithmeticTheory.LESS_EQ_CASES])) THEN
   CONJ_TAC THEN1 METIS_TAC[] THEN
   REPEAT STRIP_TAC THEN

   ‘l = (FIRSTN (SUC n1) l) ++ (LASTN (LENGTH l - (SUC n1)) l)’ by (
      MATCH_MP_TAC (GSYM APPEND_FIRSTN_LASTN) THEN
      ASM_SIMP_TAC arith_ss []
   ) THEN
   Q.ABBREV_TAC ‘l1 = (FIRSTN (SUC n1) l)’ THEN
   Q.ABBREV_TAC ‘l2 = (LASTN (LENGTH l - (SUC n1)) l)’ THEN
   ‘(n1 < LENGTH l1) /\ (LENGTH l1 <= n2)’ by (
      UNABBREV_ALL_TAC THEN
      ASM_SIMP_TAC list_ss [LENGTH_FIRSTN]
   ) THEN
   FULL_SIMP_TAC list_ss [EL_APPEND2, EL_APPEND1] THEN
   ‘n2 - LENGTH l1 < LENGTH l2’ by DECIDE_TAC THEN
   ‘MEM (EL n1 l1) (FILTER P l1)’ by METIS_TAC[MEM_FILTER, MEM_EL] THEN
   ‘MEM (EL n1 l1) (FILTER P l2)’ by METIS_TAC[MEM_FILTER, MEM_EL] THEN
   FULL_SIMP_TAC list_ss [MEM_EL, FILTER_APPEND] THEN
   Q.EXISTS_TAC ‘n’ THEN
   Q.EXISTS_TAC ‘LENGTH (FILTER P l1) + n'’ THEN
   ASM_SIMP_TAC list_ss [EL_APPEND1, EL_APPEND2] THEN
   METIS_TAC[]
);




val FORALL_LESS_SUC = store_thm ("FORALL_LESS_SUC",
   “!P m. ((!n. n < SUC m ==> P n) =
            (P 0 /\ (!n. n < m ==> P (SUC n))))”,

   REPEAT GEN_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THENL [
      ASM_SIMP_TAC arith_ss [],
      ASM_SIMP_TAC arith_ss [],

      Cases_on ‘n’ THENL [
         ASM_REWRITE_TAC[],
         ASM_SIMP_TAC arith_ss []
      ]
   ]);



val IN_FDOM_FOLDR_UNION = store_thm ("IN_FDOM_FOLDR_UNION",
“!x hL. x IN FDOM (FOLDR FUNION FEMPTY hL) =
        ?h. MEM h hL /\ x IN FDOM h”,

Induct_on ‘hL’ THENL [
   SIMP_TAC list_ss [FDOM_FEMPTY, NOT_IN_EMPTY],

   FULL_SIMP_TAC list_ss [FDOM_FUNION, IN_UNION, DISJ_IMP_THM] THEN
   METIS_TAC[]
]);

val REPLACE_ELEMENT_def = Define ‘
   (REPLACE_ELEMENT e n [] = []) /\
   (REPLACE_ELEMENT e 0 (x::l) = e::l) /\
   (REPLACE_ELEMENT e (SUC n) (x::l) = x::REPLACE_ELEMENT e n l)’


val REPLACE_ELEMENT_SEM = store_thm ("REPLACE_ELEMENT_SEM",
   “!e n l.
         (LENGTH (REPLACE_ELEMENT e n l) = LENGTH l) /\
         (!p. p < LENGTH l ==>
            (EL p (REPLACE_ELEMENT e n l) =
             if (p = n) then e else EL p l))”,

   Induct_on ‘n’ THENL [
      Cases_on ‘l’ THEN (
         SIMP_TAC list_ss [REPLACE_ELEMENT_def]
      ) THEN
      Cases_on ‘p’ THEN (
         SIMP_TAC list_ss []
      ),


      Cases_on ‘l’ THEN (
         ASM_SIMP_TAC list_ss [REPLACE_ELEMENT_def]
      ) THEN
      Cases_on ‘p’ THEN (
         ASM_SIMP_TAC list_ss []
      )
   ]);




Theorem MEM_LAST_FRONT[local]:
  !e l h.
    MEM e l /\ ~(e = LAST (h::l)) ==>
    MEM e (FRONT (h::l))
Proof
  Induct_on ‘l’ THENL [
    SIMP_TAC list_ss [],

    ASM_SIMP_TAC list_ss [] THEN
    Cases_on ‘l’ THEN (
      FULL_SIMP_TAC list_ss [] THEN
      METIS_TAC[]
      )
  ]
QED


val EL_ALL_DISTINCT_EQ = store_thm ("EL_ALL_DISTINCT_EQ",
   “!l. ALL_DISTINCT l =
         (!n1 n2. n1 < LENGTH l /\ n2 < LENGTH l ==>
         ((EL n1 l = EL n2 l) = (n1 = n2)))”,

   Induct_on ‘l’ THENL [
      SIMP_TAC list_ss [],

      ASM_SIMP_TAC list_ss [ALL_DISTINCT] THEN
      GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
         Cases_on ‘n1’ THEN Cases_on ‘n2’ THENL [
            SIMP_TAC list_ss [],

            SIMP_TAC list_ss [] THEN
            METIS_TAC[MEM_EL],

            SIMP_TAC list_ss [] THEN
            METIS_TAC[MEM_EL],

            SIMP_TAC list_ss [] THEN
            METIS_TAC[]
         ],


         STRIP_TAC THENL [
            SIMP_TAC std_ss [MEM_EL] THEN
            GEN_TAC THEN
            POP_ASSUM (fn thm => ASSUME_TAC (Q.SPECL [‘0’, ‘SUC n’] thm)) THEN
            FULL_SIMP_TAC list_ss [] THEN
            METIS_TAC[],

            REPEAT GEN_TAC THEN
            POP_ASSUM (fn thm => ASSUME_TAC (Q.SPECL [‘SUC n1’, ‘SUC n2’] thm)) THEN
            FULL_SIMP_TAC list_ss [] THEN
            METIS_TAC[]
         ]
      ]
   ]);



val EL_ALL_DISTINCT = store_thm ("EL_ALL_DISTINCT",
   “!l n1 n2. ALL_DISTINCT l /\ n1 < LENGTH l /\ n2 < LENGTH l ==>
         ((EL n1 l = EL n2 l) = (n1 = n2))”,

   METIS_TAC[EL_ALL_DISTINCT_EQ]);


val FILTER_ALL_DISTINCT = store_thm ("FILTER_ALL_DISTINCT",
   “!P l. ALL_DISTINCT l ==> ALL_DISTINCT (FILTER P l)”,

   Induct_on ‘l’ THENL [
      SIMP_TAC list_ss [],

      SIMP_TAC list_ss [] THEN
      REPEAT STRIP_TAC THEN
      Cases_on ‘P h’ THENL [
         ASM_SIMP_TAC list_ss [MEM_FILTER],
         ASM_SIMP_TAC list_ss []
      ]
   ])


val PERM_ALL_DISTINCT = store_thm ("PERM_ALL_DISTINCT",
“ !l1 l2. (ALL_DISTINCT l1 /\ ALL_DISTINCT l2 /\
            (!x. MEM x l1 = MEM x l2)) ==>
           PERM l1 l2”,

Induct_on ‘l1’ THENL [
   Cases_on ‘l2’ THEN SIMP_TAC list_ss [FORALL_AND_THM, PERM_REFL],

   SIMP_TAC list_ss [] THEN
   REPEAT STRIP_TAC THEN

   ‘?l2'. l2' = FILTER (\x. x = h) l2 ++ (FILTER ($~ o (\x. x = h)) l2)’ by METIS_TAC[] THEN
   ‘PERM l2 l2'’ by METIS_TAC[PERM_SPLIT] THEN
   ‘PERM (h::l1) l2'’ suffices_by (STRIP_TAC THEN
      METIS_TAC[PERM_TRANS, PERM_SYM]
   ) THEN
   ‘FILTER (\x. x = h) l2 = [h]’ by (
      Q.PAT_X_ASSUM ‘ALL_DISTINCT l2’ MP_TAC THEN
      ‘MEM h l2’ by METIS_TAC[] THEN
      POP_ASSUM MP_TAC THEN
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      Induct_on ‘l2’ THENL [
         SIMP_TAC list_ss [],

         SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
         REPEAT STRIP_TAC THENL [
            Q.PAT_X_ASSUM ‘MEM h l2 ==> X’ (K ALL_TAC) THEN
            Induct_on ‘l2’ THENL [
               SIMP_TAC list_ss [],
               ASM_SIMP_TAC list_ss []
            ],


            FULL_SIMP_TAC std_ss [] THEN
            METIS_TAC[]
         ]
      ]
   ) THEN
   ASM_SIMP_TAC list_ss [PERM_CONS_IFF] THEN

   Q.PAT_X_ASSUM ‘!l2. P l2 ==> PERM l1 l2’ MATCH_MP_TAC THEN
   ASM_SIMP_TAC list_ss [MEM_FILTER] THEN
   CONJ_TAC THENL [
      MATCH_MP_TAC FILTER_ALL_DISTINCT THEN
      ASM_REWRITE_TAC[],

      METIS_TAC[]
   ]
]);

val EL_HD_LAST = store_thm ("EL_HD_LAST",
   “!l. 0 < LENGTH l ==>
          ((HD l = EL 0 l) /\
          (LAST l = EL (PRE (LENGTH l)) l))”,

   SIMP_TAC list_ss [] THEN
   Induct_on ‘l’ THENL [
      SIMP_TAC list_ss [],

      SIMP_TAC list_ss [] THEN
      Cases_on ‘l’ THENL [
         SIMP_TAC list_ss [],
         FULL_SIMP_TAC list_ss []
      ]
   ]);

val MEM_FRONT = store_thm ("MEM_FRONT",
   “!l y. MEM y (FRONT (e::l)) ==> MEM y (e::l)”,

Induct_on ‘l’ THENL [
   SIMP_TAC list_ss [],

   Cases_on ‘l’ THEN
   FULL_SIMP_TAC list_ss [DISJ_IMP_THM] THEN
   METIS_TAC[]
]);


val LAST_APPEND = store_thm ("LAST_APPEND",
   “LAST (l1 ++ (e::l2)) = LAST (e::l2)”,
   Induct_on ‘l1’ THENL [
      SIMP_TAC list_ss [],
      ASM_SIMP_TAC list_ss [LAST_DEF]
   ])

val MEM_LAST = store_thm ("MEM_LAST",
   “!e l. MEM (LAST (e::l)) (e::l)”,
     Induct_on ‘l’ THENL [
         ASM_SIMP_TAC list_ss [],

         SIMP_TAC std_ss [Once MEM, LAST_CONS] THEN
         ASM_SIMP_TAC std_ss []
      ])


val ALL_DISTINCT_APPEND = store_thm ("ALL_DISTINCT_APPEND",
   “!l1 l2. ALL_DISTINCT (l1++l2) =
             (ALL_DISTINCT l1 /\ ALL_DISTINCT l2 /\
             (!e. MEM e l1 ==> ~(MEM e l2)))”,

   Induct_on ‘l1’ THENL [
      SIMP_TAC list_ss [],

      ASM_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
      PROVE_TAC[]
   ])

val ALL_DISTINCT_SNOC = store_thm ("ALL_DISTINCT_SNOC",
   “!x l. ALL_DISTINCT (SNOC x l) =
             ~(MEM x l) /\ (ALL_DISTINCT l)”,

   SIMP_TAC list_ss [SNOC_APPEND, ALL_DISTINCT_APPEND] THEN
   METIS_TAC[])


val FUNION_EQ_FEMPTY = store_thm ("FUNION_EQ_FEMPTY",
“!h1 h2. (FUNION h1 h2 = FEMPTY) = ((h1 = FEMPTY) /\ (h2 = FEMPTY))”,

   SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FDOM_FEMPTY, FUNION_DEF,
      NOT_IN_EMPTY, IN_UNION, DISJ_IMP_THM, FORALL_AND_THM] THEN
   METIS_TAC[]);



val SUBMAP___FUNION_EQ = store_thm ("SUBMAP___FUNION_EQ",
“(!f1 f2 f3. DISJOINT (FDOM f1) (FDOM f2) ==> (((f1 SUBMAP (FUNION f2 f3)) = (f1 SUBMAP f3)))) /\
  (!f1 f2 f3. DISJOINT (FDOM f1) (FDOM f3 DIFF (FDOM f2)) ==> (((f1 SUBMAP (FUNION f2 f3)) = (f1 SUBMAP f2))))”,

  SIMP_TAC std_ss [SUBMAP_DEF, FUNION_DEF, IN_UNION, DISJOINT_DEF, EXTENSION,
   NOT_IN_EMPTY, IN_INTER, IN_DIFF] THEN
  METIS_TAC[])


val SUBMAP___FUNION = store_thm ("SUBMAP___FUNION",
“!f1 f2 f3. (f1 SUBMAP f2) \/ ((DISJOINT (FDOM f1) (FDOM f2) /\ (f1 SUBMAP f3))) ==> (f1 SUBMAP (FUNION f2 f3))”,

SIMP_TAC std_ss [SUBMAP_DEF, FUNION_DEF, IN_UNION, DISJOINT_DEF, EXTENSION,
   NOT_IN_EMPTY, IN_INTER] THEN
METIS_TAC[]);

val SUBMAP___FUNION___ID = store_thm ("SUBMAP___FUNION___ID",
“(!f1 f2. (f1 SUBMAP (FUNION f1 f2))) /\
(!f1 f2. (DISJOINT (FDOM f1) (FDOM f2)) ==> (f2 SUBMAP (FUNION f1 f2)))”,

METIS_TAC[SUBMAP_REFL, SUBMAP___FUNION, DISJOINT_SYM]);

val FEMPTY_SUBMAP = store_thm ("FEMPTY_SUBMAP",
   “!h. h SUBMAP FEMPTY = (h = FEMPTY)”,

   SIMP_TAC std_ss [SUBMAP_DEF, FDOM_FEMPTY, NOT_IN_EMPTY, GSYM fmap_EQ_THM,
      EXTENSION] THEN
   METIS_TAC[]);


val FUNION_EQ = store_thm ("FUNION_EQ",
“!f1 f2 f3. (DISJOINT (FDOM f1) (FDOM f2) /\
              DISJOINT (FDOM f1) (FDOM f3)) ==>
             (((FUNION f1 f2) = (FUNION f1 f3)) = (f2 = f3))”,

  SIMP_TAC std_ss [GSYM SUBMAP_ANTISYM, SUBMAP_DEF, FUNION_DEF, IN_UNION, DISJOINT_DEF, EXTENSION,
   NOT_IN_EMPTY, IN_INTER, IN_DIFF] THEN
  METIS_TAC[])

val FUNION_EQ___IMPL = store_thm ("FUNION_EQ___IMPL",
“!f1 f2 f3. (DISJOINT (FDOM f1) (FDOM f2) /\
              DISJOINT (FDOM f1) (FDOM f3) /\ (f2 = f3)) ==>
             ((FUNION f1 f2) = (FUNION f1 f3))”,

  METIS_TAC[FUNION_EQ]);


val DOMSUB_FUNION = store_thm ("DOMSUB_FUNION",
“(FUNION f g) \\ k = FUNION (f \\ k) (g \\ k)”,

SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_DOMSUB, FUNION_DEF, EXTENSION,
   IN_UNION, IN_DELETE] THEN
REPEAT STRIP_TAC THENL [
   METIS_TAC[],
   ASM_SIMP_TAC std_ss [DOMSUB_FAPPLY_NEQ, FUNION_DEF],
   ASM_SIMP_TAC std_ss [DOMSUB_FAPPLY_NEQ, FUNION_DEF]
]);


val FUNION___COMM = store_thm ("FUNION___COMM",
“!f g. (DISJOINT (FDOM f) (FDOM g)) ==> ((FUNION f g) = (FUNION g f))”,

   SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, IN_UNION, DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
   METIS_TAC[])

val FUNION___ASSOC = store_thm ("FUNION___ASSOC",
“!f g h. ((FUNION f (FUNION g h)) = (FUNION (FUNION f g) h))”,

   SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, IN_UNION, EXTENSION] THEN
   METIS_TAC[])

val FRONT___APPEND = store_thm ("FRONT___APPEND",

   “FRONT (l1 ++ e::l2) = l1++FRONT(e::l2)”,

     Induct_on ‘l1’ THEN ASM_SIMP_TAC list_ss [FRONT_DEF])


val FRONT___LENGTH = store_thm ("FRONT___LENGTH",
   “!l. ~(l = []) ==> (LENGTH (FRONT l) = PRE (LENGTH l))”,
   Induct_on ‘l’ THENL [
      SIMP_TAC std_ss [],

      ASM_SIMP_TAC list_ss [FRONT_DEF, COND_RATOR, COND_RAND] THEN
      Cases_on ‘l’ THEN SIMP_TAC list_ss []
   ])


val EL_FRONT = store_thm ("EL_FRONT",
   “!l n. ((n < LENGTH (FRONT l)) /\ (~(l = []))) ==>
           (EL n (FRONT l) = EL n l)”,

   Induct_on ‘l’ THENL [
      SIMP_TAC list_ss [],

      Cases_on ‘l’ THEN
      FULL_SIMP_TAC list_ss [FRONT___LENGTH] THEN
      REPEAT STRIP_TAC THEN
      Cases_on ‘n’ THENL [
         SIMP_TAC list_ss [],
         FULL_SIMP_TAC list_ss []
      ]
   ])


val BUTFIRSTN___CONCAT_EL = store_thm ("BUTFIRSTN___CONCAT_EL",
   “!n. (n < LENGTH l) ==>
         ((BUTFIRSTN n l) = (EL n l) :: (BUTFIRSTN (SUC n) l))”,

   Induct_on ‘l’ THENL [
      FULL_SIMP_TAC list_ss [],

      FULL_SIMP_TAC list_ss [BUTFIRSTN] THEN
      REPEAT STRIP_TAC THEN
      Cases_on ‘n’ THENL [
         SIMP_TAC list_ss [BUTFIRSTN],
         FULL_SIMP_TAC list_ss [BUTFIRSTN]
      ]
   ])


val ALL_DISJOINT_def = Define ‘
   (ALL_DISJOINT [] = T) /\
   (ALL_DISJOINT (e1::l) = (EVERY (\e2. DISJOINT e1 e2) l) /\ ALL_DISJOINT l)’



val EL_ALL_DISJOINT_EQ = store_thm ("EL_ALL_DISJOINT_EQ",
   “!l. ALL_DISJOINT l =
         (!n1 n2. n1 < LENGTH l /\ n2 < LENGTH l ==>
         (DISJOINT (EL n1 l) (EL n2 l) = (~(n1 = n2) \/ (EL n1 l = EMPTY))))”,

   Induct_on ‘l’ THENL [
      SIMP_TAC list_ss [ALL_DISJOINT_def],

      ASM_SIMP_TAC list_ss [ALL_DISJOINT_def, EVERY_MEM] THEN
      GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
         Cases_on ‘n1’ THEN Cases_on ‘n2’ THENL [
            SIMP_TAC list_ss [DISJOINT_DEF, EXTENSION, IN_INTER],

            SIMP_TAC list_ss [] THEN
            METIS_TAC[MEM_EL],

            SIMP_TAC list_ss [] THEN
            METIS_TAC[MEM_EL, DISJOINT_SYM],

            SIMP_TAC list_ss [] THEN
            METIS_TAC[]
         ],


         STRIP_TAC THENL [
            SIMP_TAC std_ss [MEM_EL, GSYM LEFT_FORALL_IMP_THM] THEN
            GEN_TAC THEN
            POP_ASSUM (fn thm => ASSUME_TAC (Q.SPECL [‘0’, ‘SUC n’] thm)) THEN
            FULL_SIMP_TAC list_ss [] THEN
            METIS_TAC[],

            REPEAT GEN_TAC THEN
            POP_ASSUM (fn thm => ASSUME_TAC (Q.SPECL [‘SUC n1’, ‘SUC n2’] thm)) THEN
            FULL_SIMP_TAC list_ss []
         ]
      ]
   ]);

val MAP_EQ_f = store_thm ("MAP_EQ_f",

   “!f1 f2 l. (MAP f1 l = MAP f2 l) = (!e. MEM e l ==> (f1 e = f2 e))”,

   Induct_on ‘l’ THENL [
      SIMP_TAC list_ss [],

      ASM_SIMP_TAC list_ss [] THEN
      METIS_TAC[]
   ])



val DRESTRICT_FUNION = store_thm ("DRESTRICT_FUNION",
   “!h s1 s2. FUNION (DRESTRICT h s1) (DRESTRICT h s2) =
               DRESTRICT h (s1 UNION s2)”,

    SIMP_TAC std_ss [DRESTRICT_DEF, GSYM fmap_EQ_THM, EXTENSION,
      FUNION_DEF, IN_INTER, IN_UNION, DISJ_IMP_THM,
      LEFT_AND_OVER_OR]);



val DRESTRICT_EQ_FUNION = store_thm ("DRESTRICT_EQ_FUNION",
   “!h h1 h2. (DISJOINT (FDOM h1) (FDOM h2)) /\ (FUNION h1 h2 = h) ==> (h2 = DRESTRICT h (COMPL (FDOM h1)))”,

    SIMP_TAC std_ss [DRESTRICT_DEF, GSYM fmap_EQ_THM, EXTENSION,
      FUNION_DEF, IN_INTER, IN_UNION, IN_COMPL, DISJOINT_DEF,
      NOT_IN_EMPTY] THEN
    METIS_TAC[]);



val ALL_DISJOINT___PERM = store_thm ("ALL_DISJOINT___PERM",
   “!l1 l2. PERM l1 l2 ==> (ALL_DISJOINT l1 = ALL_DISJOINT l2)”,

   ‘!l1 l2. PERM l1 l2 ==> ((PERM l1 l2) /\ (ALL_DISJOINT l1 = ALL_DISJOINT l2))’ suffices_by (STRIP_TAC THEN
      METIS_TAC[]
   ) THEN
   HO_MATCH_MP_TAC PERM_IND THEN
   SIMP_TAC list_ss [ALL_DISJOINT_def, EVERY_MEM] THEN
   REPEAT STRIP_TAC THENL [
      REWRITE_TAC[PERM_REFL],
      ASM_REWRITE_TAC[PERM_CONS_IFF],
      METIS_TAC[PERM_MEM_EQ],
      ASM_REWRITE_TAC[PERM_SWAP_AT_FRONT],
      METIS_TAC[DISJOINT_SYM, PERM_MEM_EQ],
      PROVE_TAC [PERM_TRANS, PERM_SYM]
   ])



val ALL_DISTINCT___PERM = store_thm ("ALL_DISTINCT___PERM",
   “!l1 l2. PERM l1 l2 ==> (ALL_DISTINCT l1 = ALL_DISTINCT l2)”,

   ‘!l1 l2. PERM l1 l2 ==> ((PERM l1 l2) /\ (ALL_DISTINCT l1 = ALL_DISTINCT l2))’ suffices_by (STRIP_TAC THEN
      METIS_TAC[]
   ) THEN
   HO_MATCH_MP_TAC PERM_IND THEN
   SIMP_TAC list_ss [] THEN
   REPEAT STRIP_TAC THENL [
      REWRITE_TAC[PERM_REFL],
      ASM_REWRITE_TAC[PERM_CONS_IFF],
      METIS_TAC[PERM_MEM_EQ],
      ASM_REWRITE_TAC[PERM_SWAP_AT_FRONT],
      METIS_TAC[DISJOINT_SYM, PERM_MEM_EQ],
      PROVE_TAC [PERM_TRANS, PERM_SYM]
   ]);


(*----------------------------------------------------------------------------------*)






val _ = Hol_datatype ‘ds_value =
     dsv_nil
   | dsv_const of 'value’

val ds_value_11 = DB.fetch "-" "ds_value_11";
val ds_value_distinct = DB.fetch "-" "ds_value_distinct";

val _ = type_abbrev("heap", Type ‘:'a |-> 'b |-> 'a ds_value’)

val IS_DSV_NIL_def = Define ‘
   (IS_DSV_NIL dsv_nil = T) /\
   (IS_DSV_NIL _ = F)’;

val IS_DSV_NIL_THM = store_thm ("IS_DSV_NIL_THM",
   “!x. IS_DSV_NIL x = (x = dsv_nil)”,

   Cases_on ‘x’ THENL [
      SIMP_TAC std_ss [IS_DSV_NIL_def],
      SIMP_TAC std_ss [IS_DSV_NIL_def, ds_value_distinct]
   ])


val NOT_IS_DSV_NIL_THM = store_thm ("NOT_IS_DSV_NIL_THM",
   “!x. ~(IS_DSV_NIL x) = ?c. (x = dsv_const c)”,

   Cases_on ‘x’ THENL [
      SIMP_TAC std_ss [IS_DSV_NIL_def, ds_value_distinct],
      SIMP_TAC std_ss [IS_DSV_NIL_def, ds_value_11]
   ])


val GET_DSV_VALUE_def = Define ‘
   (GET_DSV_VALUE (dsv_const v) = v)’;

val GET_DSV_VALUE_11 = store_thm ("GET_DSV_VALUE_11",
   “!v1 v2. (~(IS_DSV_NIL v1) /\ ~(IS_DSV_NIL v2)) ==>
     ((GET_DSV_VALUE v1 = GET_DSV_VALUE v2) = (v1 = v2))”,

   Cases_on ‘v1’ THEN Cases_on ‘v2’ THEN
   REWRITE_TAC[GET_DSV_VALUE_def, IS_DSV_NIL_def, ds_value_11])


val dsv_const_GET_DSV_VALUE = store_thm ("dsv_const_GET_DSV_VALUE",
   “!v. ~(IS_DSV_NIL v) ==> (dsv_const (GET_DSV_VALUE v) = v)”,

   Cases_on ‘v’ THEN
   SIMP_TAC std_ss [IS_DSV_NIL_def, GET_DSV_VALUE_def]);

val _ = Hol_datatype ‘ds_expression =
     dse_const of 'value ds_value
   | dse_var of 'vars’;


val dse_nil_def = Define ‘dse_nil = dse_const dsv_nil’

val _ = Hol_datatype ‘ds_pure_formula =
     pf_true
   | pf_equal of ('vars, 'value) ds_expression => ('vars, 'value) ds_expression
   | pf_unequal of ('vars, 'value) ds_expression => ('vars, 'value) ds_expression
   | pf_and of ds_pure_formula => ds_pure_formula’;

val _ = Hol_datatype ‘ds_spatial_formula =
     sf_emp
   | sf_points_to of ('vars, 'value) ds_expression => ('field # ('vars, 'value) ds_expression) list
   | sf_tree of 'field list => ('vars, 'value) ds_expression => ('vars, 'value) ds_expression
   | sf_star of ds_spatial_formula => ds_spatial_formula’;


val ds_expression_11 = DB.fetch "-" "ds_expression_11";
val ds_expression_distinct = DB.fetch "-" "ds_expression_distinct";
val ds_spatial_formula_11 = DB.fetch "-" "ds_spatial_formula_11";
val ds_spatial_formula_distinct = DB.fetch "-" "ds_spatial_formula_distinct";


val nchotomy_thm = prove (“!x.
      (x = sf_emp) \/ (?d l. x = sf_points_to d l) \/
      (?l d d0. x = sf_tree l d d0) \/ ?d d0. x = sf_star d d0”,
                        REWRITE_TAC [TypeBase.nchotomy_of “:('a,'b,'c) ds_spatial_formula”]);

val _ = TypeBase.write [TypeBasePure.put_nchotomy nchotomy_thm (valOf (TypeBase.fetch “:('a,'b,'c) ds_spatial_formula”))];



val SF_IS_SIMPLE_def = Define ‘
   (SF_IS_SIMPLE sf_emp = F) /\
   (SF_IS_SIMPLE (sf_star sf1 sf2) = F) /\
   (SF_IS_SIMPLE X = T)’

val DS_EXPRESSION_EVAL_def = Define
   ‘(DS_EXPRESSION_EVAL s (dse_var v) = (s v)) /\
    (DS_EXPRESSION_EVAL s (dse_const c) = c)’


val DS_EXPRESSION_EQUAL_def = Define
‘DS_EXPRESSION_EQUAL s e1 e2 <=>
          (DS_EXPRESSION_EVAL s e1 = DS_EXPRESSION_EVAL s e2)’;

val DS_EXPRESSION_EVAL_VALUE_def = Define
   ‘DS_EXPRESSION_EVAL_VALUE s e = GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)’;

val PF_SEM_def = Define
   ‘(PF_SEM s pf_true = T) /\
    (PF_SEM s (pf_equal e1 e2) = (DS_EXPRESSION_EQUAL s e1 e2)) /\
    (PF_SEM s (pf_unequal e1 e2) = ~(DS_EXPRESSION_EQUAL s e1 e2)) /\
    (PF_SEM s (pf_and pf1 pf2) = ((PF_SEM s pf1) /\ (PF_SEM s pf2)))’;


val HEAP_READ_ENTRY_def = Define
   ‘HEAP_READ_ENTRY s (h:('a, 'b) heap) e f =
      if (IS_DSV_NIL (DS_EXPRESSION_EVAL s e)) then NONE else
      if (~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) IN (FDOM h))) then NONE else
      if (~(f IN (FDOM (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)))))) then NONE else
      SOME ((h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e))) ' f)’;


val HEAP_READ_ENTRY_THM = store_thm ("HEAP_READ_ENTRY_THM",
“ (!x.
   (HEAP_READ_ENTRY s h e f = (SOME x)) =

   (~IS_DSV_NIL (DS_EXPRESSION_EVAL s e) /\
    GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) IN (FDOM h) /\
    f IN (FDOM (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)))) /\
    (x = ((h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e))) ' f)))) /\

   ((HEAP_READ_ENTRY s h e f = NONE) =

   (IS_DSV_NIL (DS_EXPRESSION_EVAL s e) \/
    ~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) IN (FDOM h)) \/
    ~(f IN (FDOM (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e))))))) /\

   (IS_SOME (HEAP_READ_ENTRY s h e f) =

   (~IS_DSV_NIL (DS_EXPRESSION_EVAL s e) /\
    (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) IN (FDOM h)) /\
    (f IN (FDOM (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)))))))
”,

   SIMP_TAC std_ss [HEAP_READ_ENTRY_def] THEN
   METIS_TAC[optionTheory.option_CLAUSES]);


val DS_POINTS_TO_def = Define ‘
   DS_POINTS_TO s h e1 a =
      ~(IS_DSV_NIL (DS_EXPRESSION_EVAL s e1)) /\
       (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1) IN FDOM h) /\
        EVERY (\(f, e).
            ((f IN FDOM (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1)))) /\
            ((DS_EXPRESSION_EVAL s e) = (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1))) ' f))) a’;


val DS_POINTS_TO___DOMSUB = store_thm ("DS_POINTS_TO___DOMSUB",
   “!s h e1 a k.
      DS_POINTS_TO s (h\\k) e1 a ==>
      DS_POINTS_TO s h e1 a”,

   SIMP_TAC std_ss [DS_POINTS_TO_def, FDOM_DOMSUB, IN_DELETE,
      DOMSUB_FAPPLY_THM] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_X_ASSUM ‘EVERY P l’ MP_TAC THEN
   ASM_SIMP_TAC std_ss [])


val DS_POINTS_TO___SUBMAP = store_thm ("DS_POINTS_TO___SUBMAP",
   “!s h h' e1 a.
      (h' SUBMAP h /\ DS_POINTS_TO s h' e1 a) ==>
      DS_POINTS_TO s h e1 a”,

   SIMP_TAC std_ss [DS_POINTS_TO_def, SUBMAP_DEF] THEN
   METIS_TAC[])


val DS_POINTS_TO___SUBLIST = store_thm ("DS_POINTS_TO___SUBLIST",
   “!s h e a a'.
      ((!x. MEM x a' ==> MEM x a) /\ DS_POINTS_TO s h e a) ==>
      DS_POINTS_TO s h e a'”,

   SIMP_TAC std_ss [DS_POINTS_TO_def, EVERY_MEM] THEN
   METIS_TAC[]);


val DS_POINTS_TO___SPLIT =
   store_thm ("DS_POINTS_TO___SPLIT",

“!s h e f aL.
   (~(aL = [])) ==>
   (DS_POINTS_TO s h e aL =
   EVERY I (MAP (\a. DS_POINTS_TO s h e [a]) aL))”,

Induct_on ‘aL’ THENL [
   SIMP_TAC std_ss [],

   SIMP_TAC list_ss [] THEN
   Cases_on ‘aL’ THENL [
      SIMP_TAC list_ss [],

      FULL_SIMP_TAC list_ss [] THEN
      POP_ASSUM (fn thm => ASSUME_TAC (GSYM thm)) THEN
      ASM_SIMP_TAC std_ss [] THEN

      SIMP_TAC list_ss [DS_POINTS_TO_def] THEN
      METIS_TAC[]
   ]
]);




val DS_POINTS_TO___HEAP_READ_ENTRY_THM =
   store_thm ("DS_POINTS_TO___HEAP_READ_ENTRY_THM",

“!s h e f c.
   (HEAP_READ_ENTRY s h e f = SOME c) =
   DS_POINTS_TO s h e [f, dse_const c]”,

SIMP_TAC list_ss [HEAP_READ_ENTRY_THM, DS_POINTS_TO_def, DS_EXPRESSION_EVAL_def]);





val SF_SEM___sf_tree_len_def = Define ‘
  (SF_SEM___sf_tree_len s h fL 0 e1 e2 = ((h = FEMPTY) /\ (PF_SEM s (pf_equal e2 e1)))) /\
  (SF_SEM___sf_tree_len s h fL (SUC n) e1 e2 = (
      (SF_SEM___sf_tree_len s h fL 0 e1 e2) \/

      (PF_SEM s (pf_unequal e2 e1)) /\
      (?cL hL.
            ~IS_DSV_NIL (DS_EXPRESSION_EVAL s e2) /\
            GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2) IN FDOM h /\
            (MAP (HEAP_READ_ENTRY s h e2) fL = cL) /\
            (EVERY IS_SOME cL) /\
            (LENGTH hL = LENGTH cL) /\
            ALL_DISJOINT (MAP FDOM hL) /\
            (FOLDR FUNION FEMPTY hL = h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2)) /\
            EVERY (\(c , h'). SF_SEM___sf_tree_len s h' fL n e1 (dse_const (THE c))) (ZIP (cL, hL)))
   ))’;



val SF_SEM___sf_tree_def = Define ‘
  SF_SEM___sf_tree s h fL e1 e2 =
   ?n.  SF_SEM___sf_tree_len s h fL n e1 e2’


val WEAK_SF_SEM___sf_tree_len_def = Define ‘
  (WEAK_SF_SEM___sf_tree_len s h fL fL' 0 e1 e2 = ((h = FEMPTY) /\ (PF_SEM s (pf_equal e2 e1)))) /\
  (WEAK_SF_SEM___sf_tree_len s h fL fL' (SUC n) e1 e2 = (
      (SF_SEM___sf_tree_len s h fL 0 e1 e2) \/

      (PF_SEM s (pf_unequal e2 e1)) /\
      (?cL hL.
            ~IS_DSV_NIL (DS_EXPRESSION_EVAL s e2) /\
            GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2) IN FDOM h /\
            (MAP (HEAP_READ_ENTRY s h e2) fL = cL) /\
            (EVERY IS_SOME cL) /\
            (LENGTH hL = LENGTH cL) /\
            ALL_DISJOINT (MAP FDOM hL) /\
            (FOLDR FUNION FEMPTY hL = h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2)) /\
            EVERY (\(c , h'). SF_SEM___sf_tree_len s h' fL' n e1 (dse_const (THE c))) (ZIP (cL, hL)))
   ))’;


val WEAK_SF_SEM___sf_tree_len_THM = store_thm ("WEAK_SF_SEM___sf_tree_len_THM",
   “WEAK_SF_SEM___sf_tree_len s h fL fL n e1 e2 =
     SF_SEM___sf_tree_len s h fL n e1 e2”,

   Cases_on ‘n’ THEN (
      SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, WEAK_SF_SEM___sf_tree_len_def]
   ));




val BALANCED_SF_SEM___sf_tree_len_def = Define ‘
  (BALANCED_SF_SEM___sf_tree_len s h fL 0 e1 e2 = ((h = FEMPTY) /\ (PF_SEM s (pf_equal e2 e1)))) /\
  (BALANCED_SF_SEM___sf_tree_len s h fL (SUC n) e1 e2 = (
      (PF_SEM s (pf_unequal e2 e1)) /\
      (?cL hL.
            ~IS_DSV_NIL (DS_EXPRESSION_EVAL s e2) /\
            GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2) IN FDOM h /\
            (MAP (HEAP_READ_ENTRY s h e2) fL = cL) /\
            (EVERY IS_SOME cL) /\
            (LENGTH hL = LENGTH cL) /\
            ALL_DISJOINT (MAP FDOM hL) /\
            (FOLDR FUNION FEMPTY hL = h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2)) /\
            EVERY (\(c , h'). BALANCED_SF_SEM___sf_tree_len s h' fL n e1 (dse_const (THE c))) (ZIP (cL, hL)))
   ))’;


val BALANCED_SF_SEM___sf_tree_len_THM = store_thm ("BALANCED_SF_SEM___sf_tree_len_THM",
   “!s h fL n e1 e2.
     BALANCED_SF_SEM___sf_tree_len s h fL n e1 e2 ==>
     SF_SEM___sf_tree_len s h fL n e1 e2”,

   Induct_on ‘n’ THENL [
      SIMP_TAC std_ss [BALANCED_SF_SEM___sf_tree_len_def, SF_SEM___sf_tree_len_def],

      SIMP_TAC std_ss [BALANCED_SF_SEM___sf_tree_len_def, SF_SEM___sf_tree_len_def] THEN
      REPEAT STRIP_TAC THEN
      DISJ2_TAC THEN
      Q.EXISTS_TAC ‘hL’ THEN
      ASM_REWRITE_TAC[] THEN
      FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
      REPEAT STRIP_TAC THEN
      RES_TAC THEN
      Cases_on ‘e’ THEN
      FULL_SIMP_TAC std_ss []
   ])



val SF_SEM___sf_tree_len_THM = store_thm ("SF_SEM___sf_tree_len_THM",
   “!s h fL e1 e2 n1 n2.
         (n1 <= n2 /\
          SF_SEM___sf_tree_len s h fL n1 e1 e2) ==>
         SF_SEM___sf_tree_len s h fL n2 e1 e2”,

   Induct_on ‘n2’ THENL [
      SIMP_TAC std_ss [],

      Cases_on ‘n1’ THENL [
         SIMP_TAC list_ss [SF_SEM___sf_tree_len_def],

         SIMP_TAC std_ss [SF_SEM___sf_tree_len_def] THEN
         REPEAT STRIP_TAC THENL [
            ASM_SIMP_TAC std_ss [],

            FULL_SIMP_TAC std_ss [PF_SEM_def] THEN
            Q.EXISTS_TAC ‘hL’ THEN
            ASM_SIMP_TAC std_ss [] THEN
            Q.ABBREV_TAC ‘L = (ZIP (MAP (HEAP_READ_ENTRY s h e2) fL,hL))’ THEN
            POP_ASSUM (fn thm => ALL_TAC) THEN
            Induct_on ‘L’ THENL [
               SIMP_TAC list_ss [],

               GEN_TAC THEN
               Cases_on ‘h'’ THEN
               ASM_SIMP_TAC list_ss [] THEN
               METIS_TAC[]
            ]
         ]
      ]
   ]);



(*
val SF_SEM___sf_tree_len_SUBTREE_SUBLIST_THM = prove (
   ``!s h f fL fL' e1 e2 n.
         ((SF_SEM___sf_tree_len s h fL n e1 e2) /\ (!f. MEM f fL' ==> MEM f fL) /\
          ALL_DISTINCT fL') ==>
         ?h'. h' SUBMAP h /\ SF_SEM___sf_tree_len s h' fL' n e1 e2``,


   Induct_on `n` THENL [
      SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, SUBMAP_REFL],

      SIMP_TAC std_ss [Once SF_SEM___sf_tree_len___EXTENDED_DEF] THEN
      SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
      REPEAT STRIP_TAC THENL [
         ASM_SIMP_TAC std_ss [SUBMAP_REFL],

         FULL_SIMP_TAC list_ss [PF_SEM_def, GSYM RIGHT_EXISTS_AND_THM,
            EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
         `?hL'. MAP (\f. (@h'. ?n'. (n' < LENGTH fL) /\ (EL n' fL = f) /\
                  (h' SUBMAP (EL n' hL)) /\ (
                  SF_SEM___sf_tree_len s h' fL' n e1 (dse_const (THE (HEAP_READ_ENTRY s h e2 f)))))) fL = hL'`
            by METIS_TAC[] THEN
         Q.EXISTS_TAC `FUNION (DRESTRICT h {DS_EXPRESSION_EVAL_VALUE s e2})
                       (FOLDR FUNION FEMPTY hL')` THEN
         Q.EXISTS_TAC `hL'` THEN
         Cases_on `DS_EXPRESSION_EVAL s e2` THEN FULL_SIMP_TAC std_ss [IS_DSV_NIL_def] THEN
         FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM, GET_DSV_VALUE_def, HEAP_READ_ENTRY_def, FDOM_FUNION, IN_UNION,
            IS_DSV_NIL_def, DRESTRICT_DEF, IN_INTER, DS_EXPRESSION_EVAL_VALUE_def, IN_SING,
            FUNION_DEF, DOMSUB_FUNION]

         REPEAT STRIP_TAC THENL [
            SIMP_TAC std_ss [SUBMAP_DEF, FUNION_DEF, DRESTRICT_DEF,
               IN_INTER, IN_INSERT, IN_UNION, NOT_IN_EMPTY] THEN
            GEN_TAC THEN
            Cases_on `x = v` THEN1 (
               FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def]
            ) THEN
            ASM_REWRITE_TAC[] THEN
            `!e. MEM e hL' ==> e SUBMAP h` by (
               Q.PAT_X_ASSUM `X = hL'` (ASSUME_TAC o GSYM) THEN
               ASM_SIMP_TAC std_ss [MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
               REPEAT STRIP_TAC THEN
               SELECT_ELIM_TAC THEN
               REPEAT STRIP_TAC THENL [
                  `?n. (EL n fL = f) /\ n < LENGTH fL` by METIS_TAC[MEM_EL] THEN



            ASM_SIMP_TAC std_ss [] THEN
            Induct_on `fL`
            `MEM h'

         Cases_on `hL` THEN FULL_SIMP_TAC list_ss [] THEN

         Q_TAC MP_FREE_VAR_TAC `fL` THEN
         Q_TAC MP_FREE_VAR_TAC `h` THEN
         Q.SPEC_TAC (`fL`, `fL`) THEN
         Q.SPEC_TAC (`h`, `h`) THEN
         REWRITE_TAC[GSYM CONJ_ASSOC, AND_IMP_INTRO] THEN

         Induct_on `t` THENL [
            SIMP_TAC list_ss [ALL_DISJOINT_def] THEN
            REPEAT STRIP_TAC THEN
            Cases_on `fL` THEN FULL_SIMP_TAC list_ss [] THEN

            Q.EXISTS_TAC `DRESTRICT h {GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2)}` THEN
            Q.EXISTS_TAC `[]` THEN

            ASM_SIMP_TAC list_ss [ALL_DISJOINT_def, SUBMAP_DEF, DRESTRICT_DEF,
               IN_INTER, IN_SING, GSYM fmap_EQ_THM, EXTENSION, FDOM_FEMPTY, NOT_IN_EMPTY,
               FDOM_DOMSUB, IN_DELETE],


            SIMP_TAC list_ss [ALL_DISJOINT_def] THEN
            REPEAT STRIP_TAC THEN

            FULL_SIMP_TAC std_ss [ALL_DISJOINT_def, FDOM_FUNION, IN_UNION] THEN
            `DISJOINT (FDOM h) (FDOM (FOLDR FUNION FEMPTY t)) /\
             DISJOINT (FDOM h') (FDOM (FOLDR FUNION FEMPTY t))` by (
               REPEAT (Q.PAT_X_ASSUM `EVERY X (MAP FDOM t)` MP_TAC) THEN
               REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
               Induct_on `t` THENL [
                  SIMP_TAC list_ss [FDOM_FEMPTY, DISJOINT_EMPTY],
                  FULL_SIMP_TAC list_ss [FDOM_FUNION, DISJOINT_UNION_BOTH, DISJOINT_SYM]
               ]
            ) THEN

            Cases_on `fL` THEN FULL_SIMP_TAC list_ss [] THEN

            Q.PAT_X_ASSUM `!h fL. P h fL` MP_TAC THEN
            SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
            Q.EXISTS_TAC `DRESTRICT h'' (FDOM h'' DIFF FDOM h)` THEN
            Q.EXISTS_TAC `t'` THEN
            MATCH_MP_TAC (prove (``(a /\ (b ==> c)) ==> ((a ==> b) ==> c)``, METIS_TAC[])) THEN

            `~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2) IN FDOM h) /\
             ~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2) IN FDOM h') /\
             ~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2) IN FDOM (FOLDR FUNION FEMPTY t))` by (
               Q.PAT_X_ASSUM `FUNION h' X = Y` MP_TAC THEN
               REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
               SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FUNION_DEF, IN_UNION,
                  FDOM_DOMSUB, IN_DELETE] THEN
               METIS_TAC[]
            ) THEN

            `(HEAP_READ_ENTRY s (DRESTRICT h'' (FDOM h'' DIFF FDOM h)) e2) =
               (HEAP_READ_ENTRY s h'' e2)` by (
               ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_def, FUN_EQ_THM, DRESTRICT_DEF,
                  IN_INTER, IN_DIFF]
            ) THEN

            CONJ_TAC THEN1 (
               ASM_REWRITE_TAC[] THEN
               Q.PAT_X_ASSUM `FUNION h' X = Y` MP_TAC THEN
                  FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
                     GSYM fmap_EQ_THM, FUNION_DEF, DRESTRICT_DEF, IN_UNION,
                     DOMSUB_FAPPLY_THM, FDOM_DOMSUB, IN_DELETE, IN_DIFF] THEN
               METIS_TAC[]
            ) THEN

            STRIP_TAC THEN
            `?i. i SUBMAP h /\ (SF_SEM___sf_tree_len s i fL' n e1
                 (dse_const (THE (HEAP_READ_ENTRY s h'' e2 h'''))))` by METIS_TAC[WEAK_SF_SEM___sf_tree_len_THM] THEN

            Q.EXISTS_TAC `FUNION h'''' i` THEN
            Q.EXISTS_TAC `i::hL'` THEN

            ASM_SIMP_TAC list_ss [ALL_DISJOINT_def, FDOM_FUNION, IN_UNION] THEN
            `(HEAP_READ_ENTRY s (FUNION h'''' i) e2) =
               (HEAP_READ_ENTRY s h'''' e2)` by (
               ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_def, FUN_EQ_THM, FUNION_DEF,
                  IN_INTER, IN_UNION]
            ) THEN
            `(HEAP_READ_ENTRY s h'''' e2) =
               (HEAP_READ_ENTRY s h'' e2)` by (
               Q.PAT_X_ASSUM `h'''' SUBMAP X` MP_TAC THEN
               ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_def, FUN_EQ_THM, FUNION_DEF,
                  IN_INTER, IN_UNION, SUBMAP_DEF, DRESTRICT_DEF]
            ) THEN
            ASM_SIMP_TAC list_ss [] THEN

            REPEAT STRIP_TAC THENL [
               Q.PAT_X_ASSUM `h'''' SUBMAP X` MP_TAC THEN
               Q.PAT_X_ASSUM `i SUBMAP X` MP_TAC THEN
               Q.PAT_X_ASSUM `FUNION X Y = h'' \\ Z` MP_TAC THEN
               ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, SUBMAP_DEF,
                  EXTENSION, DRESTRICT_DEF, FDOM_DOMSUB, DOMSUB_FAPPLY_THM,
                  IN_UNION, IN_DELETE, IN_DIFF, IN_INTER] THEN
               FULL_SIMP_TAC std_ss [EXTENSION, DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY] THEN
               METIS_TAC[],



               `DISJOINT (FDOM h) (FDOM (FOLDR FUNION FEMPTY hL'))` by (
                  Q.PAT_X_ASSUM `h'''' SUBMAP X` MP_TAC THEN

                  ASM_SIMP_TAC std_ss [SUBMAP_DEF, DRESTRICT_DEF, EXTENSION, DISJOINT_DEF,
                     NOT_IN_EMPTY, IN_INTER, IN_DIFF, FDOM_DOMSUB, IN_DELETE] THEN
                  METIS_TAC[]
               ) THEN
               POP_ASSUM MP_TAC THEN

               Q.PAT_X_ASSUM `i SUBMAP h` MP_TAC THEN
               REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN

               Induct_on `hL'` THENL [
                  SIMP_TAC list_ss [],

                  FULL_SIMP_TAC list_ss [DISJOINT_UNION_BOTH, FUNION_DEF, DISJOINT_SYM] THEN
                  SIMP_TAC std_ss [SUBMAP_DEF, DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
                  METIS_TAC[]
               ],


               `(i \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2)) = i` by (
                  FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, SUBMAP_DEF, FDOM_DOMSUB,
                     IN_DELETE, DOMSUB_FAPPLY_THM] THEN
                  METIS_TAC[]
               ) THEN
               ASM_SIMP_TAC std_ss [DOMSUB_FUNION] THEN
               MATCH_MP_TAC FUNION___COMM THEN

               Q.PAT_X_ASSUM `i SUBMAP h` MP_TAC THEN
               Q.PAT_X_ASSUM `h'''' SUBMAP X` MP_TAC THEN
               ASM_SIMP_TAC std_ss [SUBMAP_DEF, DRESTRICT_DEF, EXTENSION, DISJOINT_DEF,
                  NOT_IN_EMPTY, IN_INTER, IN_DIFF, FDOM_DOMSUB, IN_DELETE] THEN
               METIS_TAC[],

               METIS_TAC[]
            ]
         ]
      ]
   ]);

*)


val WEAK_SF_SEM___sf_tree_len_SUBTREE_THM = prove (
   “!s h f fL fL' e1 e2 n.
         (WEAK_SF_SEM___sf_tree_len s h (f::fL) (f::fL') n e1 e2) ==>
         ?h'. h' SUBMAP h /\ WEAK_SF_SEM___sf_tree_len s h' fL fL' n e1 e2”,


   Induct_on ‘n’ THENL [
      SIMP_TAC std_ss [WEAK_SF_SEM___sf_tree_len_def] THEN
      METIS_TAC[SUBMAP_REFL],

      SIMP_TAC std_ss [WEAK_SF_SEM___sf_tree_len_def, SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
      REPEAT STRIP_TAC THENL [
         ASM_SIMP_TAC std_ss [SUBMAP_REFL],

         FULL_SIMP_TAC list_ss [PF_SEM_def, GSYM RIGHT_EXISTS_AND_THM] THEN
         Cases_on ‘hL’ THEN FULL_SIMP_TAC list_ss [] THEN

         Q_TAC MP_FREE_VAR_TAC ‘fL’ THEN
         Q_TAC MP_FREE_VAR_TAC ‘h’ THEN
         Q.SPEC_TAC (‘fL’, ‘fL’) THEN
         Q.SPEC_TAC (‘h’, ‘h’) THEN
         REWRITE_TAC[GSYM CONJ_ASSOC, AND_IMP_INTRO] THEN

         Induct_on ‘t’ THENL [
            SIMP_TAC list_ss [ALL_DISJOINT_def] THEN
            REPEAT STRIP_TAC THEN

            Q.EXISTS_TAC ‘DRESTRICT h {GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2)}’ THEN

            ASM_SIMP_TAC list_ss [ALL_DISJOINT_def, SUBMAP_DEF, DRESTRICT_DEF,
               IN_INTER, IN_SING, GSYM fmap_EQ_THM, EXTENSION, FDOM_FEMPTY, NOT_IN_EMPTY,
               FDOM_DOMSUB, IN_DELETE],


            SIMP_TAC list_ss [ALL_DISJOINT_def] THEN
            REPEAT STRIP_TAC THEN

            FULL_SIMP_TAC std_ss [ALL_DISJOINT_def, FDOM_FUNION, IN_UNION] THEN
            ‘DISJOINT (FDOM h) (FDOM (FOLDR FUNION FEMPTY t)) /\
             DISJOINT (FDOM h') (FDOM (FOLDR FUNION FEMPTY t))’ by (
               REPEAT (Q.PAT_X_ASSUM ‘EVERY X (MAP FDOM t)’ MP_TAC) THEN
               REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
               Induct_on ‘t’ THENL [
                  SIMP_TAC list_ss [FDOM_FEMPTY, DISJOINT_EMPTY],
                  FULL_SIMP_TAC list_ss [FDOM_FUNION, DISJOINT_UNION_BOTH, DISJOINT_SYM]
               ]
            ) THEN

            Cases_on ‘fL’ THEN FULL_SIMP_TAC list_ss [] THEN

            Q.PAT_X_ASSUM ‘!h fL. P h fL’ MP_TAC THEN
            SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
            Q.EXISTS_TAC ‘DRESTRICT h'' (FDOM h'' DIFF FDOM h)’ THEN
            Q.EXISTS_TAC ‘t'’ THEN
            MATCH_MP_TAC (prove (“(a /\ (b ==> c)) ==> ((a ==> b) ==> c)”, METIS_TAC[])) THEN

            ‘~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2) IN FDOM h) /\
             ~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2) IN FDOM h') /\
             ~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2) IN FDOM (FOLDR FUNION FEMPTY t))’ by (
               Q.PAT_X_ASSUM ‘FUNION h' X = Y’ MP_TAC THEN
               REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
               SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FUNION_DEF, IN_UNION,
                  FDOM_DOMSUB, IN_DELETE] THEN
               METIS_TAC[]
            ) THEN

            ‘(HEAP_READ_ENTRY s (DRESTRICT h'' (FDOM h'' DIFF FDOM h)) e2) =
               (HEAP_READ_ENTRY s h'' e2)’ by (
               ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_def, FUN_EQ_THM, DRESTRICT_DEF,
                  IN_INTER, IN_DIFF]
            ) THEN

            CONJ_TAC THEN1 (
               ASM_REWRITE_TAC[] THEN
               Q.PAT_X_ASSUM ‘FUNION h' X = Y’ MP_TAC THEN
                  FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
                     GSYM fmap_EQ_THM, FUNION_DEF, DRESTRICT_DEF, IN_UNION,
                     DOMSUB_FAPPLY_THM, FDOM_DOMSUB, IN_DELETE, IN_DIFF] THEN
               METIS_TAC[]
            ) THEN

            STRIP_TAC THEN
            ‘?i. i SUBMAP h /\ (SF_SEM___sf_tree_len s i fL' n e1
                 (dse_const (THE (HEAP_READ_ENTRY s h'' e2 h'''))))’ by METIS_TAC[WEAK_SF_SEM___sf_tree_len_THM] THEN

            Q.EXISTS_TAC ‘FUNION h'''' i’ THEN
            Q.EXISTS_TAC ‘i::hL'’ THEN

            ASM_SIMP_TAC list_ss [ALL_DISJOINT_def, FDOM_FUNION, IN_UNION] THEN
            ‘(HEAP_READ_ENTRY s (FUNION h'''' i) e2) =
               (HEAP_READ_ENTRY s h'''' e2)’ by (
               ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_def, FUN_EQ_THM, FUNION_DEF,
                  IN_INTER, IN_UNION]
            ) THEN
            ‘(HEAP_READ_ENTRY s h'''' e2) =
               (HEAP_READ_ENTRY s h'' e2)’ by (
               Q.PAT_X_ASSUM ‘h'''' SUBMAP X’ MP_TAC THEN
               ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_def, FUN_EQ_THM, FUNION_DEF,
                  IN_INTER, IN_UNION, SUBMAP_DEF, DRESTRICT_DEF]
            ) THEN
            ASM_SIMP_TAC list_ss [] THEN

            REPEAT STRIP_TAC THENL [
               Q.PAT_X_ASSUM ‘h'''' SUBMAP X’ MP_TAC THEN
               Q.PAT_X_ASSUM ‘i SUBMAP X’ MP_TAC THEN
               Q.PAT_X_ASSUM ‘FUNION X Y = h'' \\ Z’ MP_TAC THEN
               ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, SUBMAP_DEF,
                  EXTENSION, DRESTRICT_DEF, FDOM_DOMSUB, DOMSUB_FAPPLY_THM,
                  IN_UNION, IN_DELETE, IN_DIFF, IN_INTER] THEN
               FULL_SIMP_TAC std_ss [EXTENSION, DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY] THEN
               METIS_TAC[],



               ‘DISJOINT (FDOM h) (FDOM (FOLDR FUNION FEMPTY hL'))’ by (
                  Q.PAT_X_ASSUM ‘h'''' SUBMAP X’ MP_TAC THEN

                  ASM_SIMP_TAC std_ss [SUBMAP_DEF, DRESTRICT_DEF, EXTENSION, DISJOINT_DEF,
                     NOT_IN_EMPTY, IN_INTER, IN_DIFF, FDOM_DOMSUB, IN_DELETE] THEN
                  METIS_TAC[]
               ) THEN
               POP_ASSUM MP_TAC THEN

               Q.PAT_X_ASSUM ‘i SUBMAP h’ MP_TAC THEN
               REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN

               Induct_on ‘hL'’ THENL [
                  SIMP_TAC list_ss [],

                  FULL_SIMP_TAC list_ss [DISJOINT_UNION_BOTH, FUNION_DEF, DISJOINT_SYM] THEN
                  SIMP_TAC std_ss [SUBMAP_DEF, DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
                  METIS_TAC[]
               ],


               ‘(i \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2)) = i’ by (
                  FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, SUBMAP_DEF, FDOM_DOMSUB,
                     IN_DELETE, DOMSUB_FAPPLY_THM] THEN
                  METIS_TAC[]
               ) THEN
               ASM_SIMP_TAC std_ss [DOMSUB_FUNION] THEN
               MATCH_MP_TAC FUNION___COMM THEN

               Q.PAT_X_ASSUM ‘i SUBMAP h’ MP_TAC THEN
               Q.PAT_X_ASSUM ‘h'''' SUBMAP X’ MP_TAC THEN
               ASM_SIMP_TAC std_ss [SUBMAP_DEF, DRESTRICT_DEF, EXTENSION, DISJOINT_DEF,
                  NOT_IN_EMPTY, IN_INTER, IN_DIFF, FDOM_DOMSUB, IN_DELETE] THEN
               METIS_TAC[],

               METIS_TAC[]
            ]
         ]
      ]
   ]);




val SF_SEM___sf_tree_len___EXTENDED_DEF = store_thm ("SF_SEM___sf_tree_len___EXTENDED_DEF",
“(SF_SEM___sf_tree_len s h fL 0 e1 e2 = ((h = FEMPTY) /\ (PF_SEM s (pf_equal e2 e1)))) /\
  (SF_SEM___sf_tree_len s h fL (SUC n) e1 e2 = (
      (SF_SEM___sf_tree_len s h fL 0 e1 e2) \/

      (PF_SEM s (pf_unequal e2 e1)) /\
      (?hL.
            ~IS_DSV_NIL (DS_EXPRESSION_EVAL s e2) /\
            GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2) IN FDOM h /\
            (!f. MEM f fL ==> IS_SOME (HEAP_READ_ENTRY s h e2 f)) /\
            (LENGTH hL = LENGTH fL) /\
            ALL_DISJOINT (MAP FDOM hL) /\
            (FOLDR FUNION FEMPTY hL = h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2)) /\
            (!h'. MEM h' hL ==> h' SUBMAP h) /\
            (!n'. n' < LENGTH hL ==> (SF_SEM___sf_tree_len s (EL n' hL) fL n e1
                (dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2)) ' (EL n' fL))))) /\
            (!x. x IN FDOM h /\ ~(dsv_const x = DS_EXPRESSION_EVAL s e2) ==>
                 ?h'. MEM h' hL /\ x IN FDOM h')
      )
   ))”,



SIMP_TAC list_ss [SF_SEM___sf_tree_len_def, PF_SEM_def,
EVERY_MEM, GSYM LEFT_FORALL_IMP_THM, MEM_MAP] THEN
Cases_on ‘DS_EXPRESSION_EQUAL s e2 e1’ THEN ASM_REWRITE_TAC[] THEN
STRIP_EQ_EXISTS_TAC THEN
STRIP_EQ_BOOL_TAC THEN
FULL_SIMP_TAC list_ss [MEM_ZIP, GSYM LEFT_FORALL_IMP_THM, EL_MAP,
   HEAP_READ_ENTRY_THM] THEN
MATCH_MP_TAC (prove (“(a /\ b /\ (c' = c)) ==> (c' = (a /\ c /\ b))”, METIS_TAC[])) THEN
REPEAT CONJ_TAC THENL [
   REPEAT STRIP_TAC THEN
   ‘h' SUBMAP FOLDR FUNION FEMPTY hL’ suffices_by (STRIP_TAC THEN
      POP_ASSUM MP_TAC THEN
      ASM_SIMP_TAC std_ss [SUBMAP_DEF, DOMSUB_FAPPLY_THM, FDOM_DOMSUB, IN_DELETE]
   ) THEN
   Q.PAT_X_ASSUM ‘MEM h' hL’ MP_TAC THEN
   Q.PAT_X_ASSUM ‘ALL_DISJOINT X’ MP_TAC THEN
   REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
   Induct_on ‘hL’ THENL [
      SIMP_TAC list_ss [],

      SIMP_TAC list_ss [ALL_DISJOINT_def, EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
      METIS_TAC[SUBMAP___FUNION, DISJOINT_SYM, SUBMAP___FUNION___ID]
   ],


   REPEAT STRIP_TAC THENL [
      ‘x IN FDOM (FOLDR FUNION FEMPTY hL)’ by (
         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE] THEN
         Cases_on ‘DS_EXPRESSION_EVAL s e2’  THEN (
            FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, IS_DSV_NIL_def, ds_value_11]
         )
      ) THEN
      POP_ASSUM MP_TAC THEN
      REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
      Induct_on ‘hL’ THENL [
         SIMP_TAC list_ss [FDOM_FEMPTY, NOT_IN_EMPTY],

         SIMP_TAC list_ss [FDOM_FUNION, IN_UNION] THEN
         METIS_TAC[]
      ]
   ],


   STRIP_EQ_FORALL_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   FULL_SIMP_TAC list_ss [HEAP_READ_ENTRY_def, MEM_EL, GSYM LEFT_FORALL_IMP_THM]
]);





val BALANCED_SF_SEM___sf_tree_len___EXTENDED_DEF = store_thm ("BALANCED_SF_SEM___sf_tree_len___EXTENDED_DEF",
“(BALANCED_SF_SEM___sf_tree_len s h fL 0 e1 e2 = ((h = FEMPTY) /\ (PF_SEM s (pf_equal e2 e1)))) /\
  (BALANCED_SF_SEM___sf_tree_len s h fL (SUC n) e1 e2 = (
      (PF_SEM s (pf_unequal e2 e1)) /\
      (?hL.
            ~IS_DSV_NIL (DS_EXPRESSION_EVAL s e2) /\
            GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2) IN FDOM h /\
            (!f. MEM f fL ==> IS_SOME (HEAP_READ_ENTRY s h e2 f)) /\
            (LENGTH hL = LENGTH fL) /\
            ALL_DISJOINT (MAP FDOM hL) /\
            (FOLDR FUNION FEMPTY hL = h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2)) /\
            (!h'. MEM h' hL ==> h' SUBMAP h) /\
            (!n'. n' < LENGTH hL ==> (BALANCED_SF_SEM___sf_tree_len s (EL n' hL) fL n e1
                (dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2)) ' (EL n' fL))))) /\
            (!x. x IN FDOM h /\ ~(dsv_const x = DS_EXPRESSION_EVAL s e2) ==>
                 ?h'. MEM h' hL /\ x IN FDOM h')
      )
   ))”,


SIMP_TAC list_ss [BALANCED_SF_SEM___sf_tree_len_def, PF_SEM_def,
EVERY_MEM, GSYM LEFT_FORALL_IMP_THM, MEM_MAP] THEN
STRIP_EQ_BOOL_TAC THEN
STRIP_EQ_EXISTS_TAC THEN
STRIP_EQ_BOOL_TAC THEN
FULL_SIMP_TAC list_ss [MEM_ZIP, GSYM LEFT_FORALL_IMP_THM, EL_MAP,
   HEAP_READ_ENTRY_THM] THEN
MATCH_MP_TAC (prove (“(a /\ b /\ (c' = c)) ==> (c' = (a /\ c /\ b))”, METIS_TAC[])) THEN
REPEAT CONJ_TAC THENL [
   REPEAT STRIP_TAC THEN
   ‘h' SUBMAP FOLDR FUNION FEMPTY hL’ suffices_by (STRIP_TAC THEN
      POP_ASSUM MP_TAC THEN
      ASM_SIMP_TAC std_ss [SUBMAP_DEF, DOMSUB_FAPPLY_THM, FDOM_DOMSUB, IN_DELETE]
   ) THEN
   Q.PAT_X_ASSUM ‘MEM h' hL’ MP_TAC THEN
   Q.PAT_X_ASSUM ‘ALL_DISJOINT X’ MP_TAC THEN
   REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
   Induct_on ‘hL’ THENL [
      SIMP_TAC list_ss [],

      SIMP_TAC list_ss [ALL_DISJOINT_def, EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
      METIS_TAC[SUBMAP___FUNION, DISJOINT_SYM, SUBMAP___FUNION___ID]
   ],


   REPEAT STRIP_TAC THENL [
      ‘x IN FDOM (FOLDR FUNION FEMPTY hL)’ by (
         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE] THEN
         Cases_on ‘DS_EXPRESSION_EVAL s e2’  THEN (
            FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, IS_DSV_NIL_def, ds_value_11]
         )
      ) THEN
      POP_ASSUM MP_TAC THEN
      REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
      Induct_on ‘hL’ THENL [
         SIMP_TAC list_ss [FDOM_FEMPTY, NOT_IN_EMPTY],

         SIMP_TAC list_ss [FDOM_FUNION, IN_UNION] THEN
         METIS_TAC[]
      ]
   ],


   STRIP_EQ_FORALL_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   FULL_SIMP_TAC list_ss [HEAP_READ_ENTRY_def, MEM_EL, GSYM LEFT_FORALL_IMP_THM]
]);




val SF_SEM___sf_tree_len_SUBTREE_THM = store_thm ("SF_SEM___sf_tree_len_SUBTREE_THM",
   “!s h f fL e1 e2 n.
         (SF_SEM___sf_tree_len s h (f::fL) n e1 e2) ==>
         ?h'. h' SUBMAP h /\ SF_SEM___sf_tree_len s h' fL n e1 e2”,

   METIS_TAC[WEAK_SF_SEM___sf_tree_len_SUBTREE_THM, WEAK_SF_SEM___sf_tree_len_THM])



Theorem SF_SEM___sf_tree_len_PERM_THM:
  !fL fL' n.
    PERM fL fL' ==>
    !s h es e.
      SF_SEM___sf_tree_len s h fL  n es e = SF_SEM___sf_tree_len s h fL' n es e
Proof

   SIMP_TAC std_ss [EQ_IMP_THM, FORALL_AND_THM, IMP_CONJ_THM] THEN
   reverse conj_asm1_tac THEN1 METIS_TAC[PERM_SYM] THEN

   Induct_on ‘n’ THEN1 (
      REWRITE_TAC [SF_SEM___sf_tree_len_def]
   ) THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   ‘!s h es e.
              SF_SEM___sf_tree_len s h fL' n es e =
              SF_SEM___sf_tree_len s h fL n es e’ by METIS_TAC[PERM_SYM] THEN
   ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
   ‘!x. MEM x fL' = MEM x fL’ by METIS_TAC[PERM_MEM_EQ] THEN
   Cases_on ‘DS_EXPRESSION_EQUAL s e es’ THEN ASM_REWRITE_TAC[] THEN

   STRIP_TAC THEN
   FULL_SIMP_TAC list_ss [] THEN
   ‘?hL'. PERM hL hL' /\
          (!x. MEM x (ZIP (fL', hL')) = MEM x (ZIP (fL, hL)))’ suffices_by
     (STRIP_TAC THEN
      Q.EXISTS_TAC ‘hL'’ THEN
      FULL_SIMP_TAC list_ss [] THEN
      REPEAT STRIP_TAC THENL [
         FULL_SIMP_TAC std_ss [EVERY_MEM, MEM_MAP],
         METIS_TAC[PERM_LENGTH],
         METIS_TAC[PERM_MAP, ALL_DISJOINT___PERM],

         ‘!hL hL':('c, 'a) heap list.
            PERM hL hL' ==>
            ALL_DISJOINT (MAP FDOM hL) /\ ALL_DISJOINT (MAP FDOM hL) ==>
            PERM hL hL' /\ (FOLDR FUNION FEMPTY hL = FOLDR FUNION FEMPTY hL')’
           suffices_by (STRIP_TAC THEN
                        METIS_TAC[PERM_MAP, ALL_DISJOINT___PERM]
                       ) THEN
         REPEAT (POP_ASSUM (K ALL_TAC)) THEN

         HO_MATCH_MP_TAC PERM_IND THEN
         SIMP_TAC list_ss [PERM_REFL, PERM_CONS_IFF, PERM_SWAP_AT_FRONT,
                           ALL_DISJOINT_def, EVERY_MEM, MEM_MAP,
                           GSYM LEFT_FORALL_IMP_THM, DISJOINT_DEF, EXTENSION,
                           NOT_IN_EMPTY, IN_INTER] THEN
         REPEAT STRIP_TAC THENL [
             ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FUNION_DEF,
                                  IN_UNION, DISJ_IMP_THM] THEN
             METIS_TAC[],

             ‘ALL_DISJOINT (MAP FDOM hL')’
               by METIS_TAC[PERM_MAP, ALL_DISJOINT___PERM] THEN
             FULL_SIMP_TAC std_ss [] THEN
             PROVE_TAC[PERM_TRANS],

             ‘ALL_DISJOINT (MAP FDOM hL')’
               by METIS_TAC[PERM_MAP, ALL_DISJOINT___PERM] THEN
             FULL_SIMP_TAC std_ss []
           ],


         FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
         REPEAT STRIP_TAC THEN
         Q.PAT_X_ASSUM ‘!e. MEM e Z ==> P e’ MATCH_MP_TAC THEN
         Q.PAT_X_ASSUM ‘MEM e' Z’ MP_TAC THEN
         Q.PAT_X_ASSUM ‘!e'. P e'’ MP_TAC THEN
         ‘(LENGTH fL' = LENGTH fL) /\ (LENGTH hL' = LENGTH hL)’
           by METIS_TAC[PERM_LENGTH] THEN
         ASM_SIMP_TAC list_ss [MEM_ZIP] THEN
         REPEAT STRIP_TAC THEN
         ‘?n. (n < LENGTH fL) /\ ((EL n' fL', EL n' hL') = (EL n fL, EL n hL))’
           by METIS_TAC[] THEN
         Q.EXISTS_TAC ‘n''’ THEN
         FULL_SIMP_TAC std_ss [EL_MAP]
       ]
     ) THEN


   ‘!fL:('a list) fL'.
      PERM fL fL' ==> (PERM fL fL' /\
      !hL:('c, 'a) heap list.
        (LENGTH hL = LENGTH fL) ==>
        ?hL'. PERM hL hL' /\ !x. MEM x (ZIP (fL',hL')) = MEM x (ZIP (fL,hL)))’
     suffices_by (STRIP_TAC THEN
                  METIS_TAC[]
                 ) THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN

   HO_MATCH_MP_TAC PERM_IND THEN
   SIMP_TAC list_ss [PERM_REFL, PERM_SWAP_AT_FRONT, PERM_CONS_IFF,
      LENGTH_NIL, PERM_NIL] THEN
   REPEAT STRIP_TAC THENL [
      REPEAT STRIP_TAC THEN
      ‘?h hL''. hL = h::hL''’ by (
         Cases_on ‘hL’ THEN FULL_SIMP_TAC list_ss []
      ) THEN
      Q.PAT_X_ASSUM ‘!e. P e’ (fn thm => MP_TAC (Q.SPEC ‘hL''’ thm)) THEN
      FULL_SIMP_TAC list_ss [] THEN
      REPEAT STRIP_TAC THEN
      Q.EXISTS_TAC ‘h::hL'’ THEN
      ASM_SIMP_TAC list_ss [PERM_CONS_IFF],


      REPEAT STRIP_TAC THEN
      ‘?h1 h2 hL''. hL = h1::h2::hL''’ by (
         Cases_on ‘hL’ THEN FULL_SIMP_TAC list_ss [] THEN
         Cases_on ‘t’ THEN FULL_SIMP_TAC list_ss []
      ) THEN
      Q.PAT_X_ASSUM ‘!e. P e’ (fn thm => MP_TAC (Q.SPEC ‘hL''’ thm)) THEN
      FULL_SIMP_TAC list_ss [] THEN
      REPEAT STRIP_TAC THEN
      Q.EXISTS_TAC ‘h2::h1::hL'’ THEN
      ASM_SIMP_TAC list_ss [PERM_SWAP_AT_FRONT] THEN
      PROVE_TAC[],


      METIS_TAC[PERM_TRANS],
      METIS_TAC[PERM_LENGTH,PERM_REFL,PERM_TRANS]
   ]
QED





val SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM = store_thm ("SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM",
 “!s h fL es es' e e' n.
      DS_EXPRESSION_EQUAL s es es' /\
      DS_EXPRESSION_EQUAL s e e' ==>
      (SF_SEM___sf_tree_len s h fL n es e =
       SF_SEM___sf_tree_len s h fL n es' e')”,

Induct_on ‘n’ THENL [
   SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def],

   FULL_SIMP_TAC list_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def] THEN
   REPEAT STRIP_TAC THEN
   Cases_on ‘(DS_EXPRESSION_EVAL s e' = DS_EXPRESSION_EVAL s es')’ THEN ASM_REWRITE_TAC[] THEN
   ‘HEAP_READ_ENTRY s h e = HEAP_READ_ENTRY s h e'’ by (
      ASM_SIMP_TAC std_ss [FUN_EQ_THM, HEAP_READ_ENTRY_def]
   ) THEN
   STRIP_EQ_EXISTS_TAC THEN
   ASM_SIMP_TAC std_ss [EVERY_MEM] THEN
   STRIP_EQ_BOOL_TAC THEN
   STRIP_EQ_FORALL_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   pairLib.GEN_BETA_TAC THEN
   Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]
]);


val SF_SEM_def = Define
   ‘(SF_SEM s (h:('b, 'c) heap) sf_emp = (h = FEMPTY)) /\
    (SF_SEM s h (sf_points_to e a) =
      ((FDOM h = {DS_EXPRESSION_EVAL_VALUE s e}) /\
      DS_POINTS_TO s h e a)) /\
    (SF_SEM s h (sf_star sf1 sf2) =
      ?h1 h2. (h = FUNION h1 h2) /\ (DISJOINT (FDOM h1) (FDOM h2)) /\
              (SF_SEM s h1 sf1 /\ SF_SEM s h2 sf2)) /\
    (SF_SEM s h (sf_tree fL es e) = SF_SEM___sf_tree s h fL es e)’;



val DS_SEM_def = Define
   ‘DS_SEM s h (pf, sf) =
         PF_SEM s pf /\ SF_SEM s h sf’

val PF_ENTAILS_def = Define
   ‘PF_ENTAILS pf1 pf2 =
      !s. PF_SEM s pf1 ==> PF_SEM s pf2’

val PF_EQUIV_def = Define
   ‘PF_EQUIV pf1 pf2 =
      !s. PF_SEM s pf1 = PF_SEM s pf2’

val SF_ENTAILS_def = Define
   ‘SF_ENTAILS sf1 sf2 =
      !s h. (SF_SEM s h sf1 ==> SF_SEM s h sf2)’

val SF_EQUIV_def = Define
   ‘SF_EQUIV sf1 sf2 =
      !s h. (SF_SEM s h sf1 = SF_SEM s h sf2)’

val DS_ENTAILS_def = Define
   ‘DS_ENTAILS f1 f2 =
      !s h. (DS_SEM s h f1 ==> DS_SEM s h f2)’

val DS_EQUIV_def = Define
   ‘DS_EQUIV f1 f2 =
      !s h. (DS_SEM s h f1 = DS_SEM s h f2)’

val DS_EQUIV___ENTAILS = store_thm ("DS_EQUIV___ENTAILS",
“!f1 f2. DS_EQUIV f1 f2 = (DS_ENTAILS f1 f2 /\ DS_ENTAILS f2 f1)”,

SIMP_TAC std_ss [DS_ENTAILS_def, DS_EQUIV_def] THEN
PROVE_TAC[]);



val SF_STAR_CONG = store_thm ("SF_STAR_CONG",
   “(SF_EQUIV sf1 sf1' /\
      SF_EQUIV sf2 sf2') ==>
     (SF_EQUIV (sf_star sf1 sf2) (sf_star sf1' sf2'))”,

   SIMP_TAC std_ss [SF_EQUIV_def, SF_SEM_def])


(*access just a part of SF_SEM_def, technical theorem used for rewriting*)
val SF_SEM___STAR_THM = save_thm ("SF_SEM___STAR_THM",
   SIMP_CONV std_ss [SF_SEM_def] “SF_SEM s h (sf_star sf1 sf2)”);

val SF_SEM___STAR_EMP = store_thm ("SF_SEM___STAR_EMP",
   “(SF_EQUIV (sf_star sf sf_emp) sf) /\
     (SF_EQUIV (sf_star sf_emp sf) sf)”,

   SIMP_TAC std_ss [SF_SEM_def, SF_EQUIV_def, FDOM_FEMPTY, pred_setTheory.DISJOINT_EMPTY,
      FUNION_FEMPTY_2, FUNION_FEMPTY_1])

val SF_SEM_EMP_EXTEND = store_thm ("SF_SEM_EMP_EXTEND",
   “!s h sf. SF_SEM s h sf = SF_SEM s h (sf_star sf sf_emp)”,

   SIMP_TAC std_ss [SF_SEM_def, SF_EQUIV_def, FDOM_FEMPTY, pred_setTheory.DISJOINT_EMPTY,
      FUNION_FEMPTY_2, FUNION_FEMPTY_1])

val SF_SEM___STAR_ASSOC = store_thm ("SF_SEM___STAR_ASSOC",
   “!s h. SF_SEM s h (sf_star (sf_star sf1 sf2) sf3) =
           SF_SEM s h (sf_star sf1 (sf_star sf2 sf3))”,

   SIMP_TAC std_ss [SF_SEM_def, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_EXISTS_AND_THM] THEN
   REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Q.EXISTS_TAC ‘h1'’ THEN
      Q.EXISTS_TAC ‘h2'’ THEN
      Q.EXISTS_TAC ‘h2’ THEN
      FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, FDOM_FUNION,
         IN_UNION, NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THENL [
         SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, IN_UNION, FUNION_DEF] THEN
         METIS_TAC[],

         METIS_TAC[],
         METIS_TAC[]
      ],

      Q.EXISTS_TAC ‘h2'’ THEN
      Q.EXISTS_TAC ‘h1’ THEN
      Q.EXISTS_TAC ‘h1'’ THEN
      FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, FDOM_FUNION,
         IN_UNION, NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THENL [
         SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, IN_UNION, FUNION_DEF] THEN
         METIS_TAC[],

         METIS_TAC[],
         METIS_TAC[]
      ]
   ])


val SF_SEM___STAR_COMM = store_thm ("SF_SEM___STAR_COMM",
   “!s h. SF_SEM s h (sf_star sf1 sf2) =
           SF_SEM s h (sf_star sf2 sf1)”,

   SIMP_TAC std_ss [SF_SEM_def] THEN
   REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Q.EXISTS_TAC ‘h2’ THEN
      Q.EXISTS_TAC ‘h1’ THEN
      FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, FDOM_FUNION,
         IN_UNION, NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THENL [
         SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, IN_UNION, FUNION_DEF] THEN
         METIS_TAC[],

         METIS_TAC[]
      ],

      Q.EXISTS_TAC ‘h2’ THEN
      Q.EXISTS_TAC ‘h1’ THEN
      FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, FDOM_FUNION,
         IN_UNION, NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THENL [
         SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, IN_UNION, FUNION_DEF] THEN
         METIS_TAC[],

         METIS_TAC[]
      ]
   ]);


val SF_SEM___STAR_ASSOC_COMM1 = store_thm ("SF_SEM___STAR_ASSOC_COMM1",
“!s h sf1 sf2 sf3.
        SF_SEM s h (sf_star sf1 (sf_star sf2 sf3)) =
        SF_SEM s h (sf_star sf2 (sf_star sf1 sf3))”,



REWRITE_TAC [Once SF_SEM___STAR_COMM] THEN
REWRITE_TAC [SF_SEM___STAR_ASSOC] THEN
REWRITE_TAC [Once SF_SEM___STAR_THM] THEN
REWRITE_TAC [Once SF_SEM___STAR_COMM] THEN
REWRITE_TAC [SF_SEM___STAR_THM]);



val SF_SEM___sf_tree_THM1 = prove (
  “!s h fL es e.

   SF_SEM s h (sf_tree fL es e) = (
      if (DS_EXPRESSION_EQUAL s e es) then
         (h = FEMPTY)
      else
        (?cL hL n.
               ~IS_DSV_NIL (DS_EXPRESSION_EVAL s e) /\
               GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) IN FDOM h /\
               (MAP (HEAP_READ_ENTRY s h e) fL = cL) /\
               (EVERY IS_SOME cL) /\
               (LENGTH hL = LENGTH cL) /\
               ALL_DISJOINT (MAP FDOM hL) /\
               (FOLDR FUNION FEMPTY hL = h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)) /\
               EVERY (\(c , h'). SF_SEM___sf_tree_len s h' fL n es (dse_const (THE c))) (ZIP (cL, hL)))
      )”,

   SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def] THEN
   SIMP_TAC std_ss [Once EQ_IMP_THM, FORALL_AND_THM,
      GSYM LEFT_FORALL_IMP_THM] THEN
   CONJ_TAC THENL [
      Cases_on ‘n’ THENL [
         SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def],

         SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
         REPEAT STRIP_TAC THENL [
            ASM_SIMP_TAC std_ss [],

            ASM_SIMP_TAC std_ss [] THEN
            METIS_TAC[]
         ]
      ],

      REPEAT GEN_TAC THEN STRIP_TAC THEN
      Cases_on ‘DS_EXPRESSION_EQUAL s e es’ THENL [
         Q.EXISTS_TAC ‘0’ THEN
         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def],

         FULL_SIMP_TAC std_ss [] THEN
         Q.EXISTS_TAC ‘SUC n’ THEN
         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
         METIS_TAC[]
      ]
   ]);





val SF_SEM___sf_tree_THM2 = prove (
  “!fL fL' cL s h.

(?hL n.
   ~IS_DSV_NIL (DS_EXPRESSION_EVAL s e) /\
   GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) IN FDOM h /\
   (MAP (HEAP_READ_ENTRY s h e) fL = cL) /\
   (EVERY IS_SOME cL) /\
   (LENGTH hL = LENGTH cL) /\
   ALL_DISJOINT (MAP FDOM hL) /\
   (FOLDR FUNION FEMPTY hL = h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)) /\
   EVERY (\(c , h'). SF_SEM___sf_tree_len s h' fL' n es (dse_const (THE c))) (ZIP (cL, hL))) =

((LENGTH cL = LENGTH fL) /\
 (EVERY IS_SOME cL) /\
 (SF_SEM s h (sf_star
 (sf_points_to e (MAP (\(f, c). (f, dse_const (THE c))) (ZIP (fL, cL))))
 (FOLDR (\c sf. sf_star (sf_tree fL' es (dse_const (THE c))) sf) sf_emp cL))))”,


Induct_on ‘fL’ THENL [
   REPEAT GEN_TAC THEN
   SIMP_TAC list_ss [LENGTH_NIL] THEN
   Cases_on ‘cL’ THEN ASM_SIMP_TAC list_ss [] THEN
   SIMP_TAC list_ss [LENGTH_NIL, SF_SEM_def, FUNION_FEMPTY_2,
      ALL_DISJOINT_def, FDOM_FEMPTY, DISJOINT_EMPTY, DS_POINTS_TO_def] THEN
   Cases_on ‘~IS_DSV_NIL (DS_EXPRESSION_EVAL s e)’ THEN ASM_SIMP_TAC std_ss [] THEN
   Cases_on ‘GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) IN FDOM h’ THEN ASM_SIMP_TAC std_ss [] THEN

   SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FEMPTY, NOT_IN_EMPTY, FDOM_DOMSUB,
      EXTENSION, IN_DELETE, IN_SING, DS_EXPRESSION_EVAL_VALUE_def] THEN
   METIS_TAC[],


   Cases_on ‘cL’ THEN1 (
      ASM_SIMP_TAC list_ss []
   ) THEN

   REPEAT GEN_TAC THEN
   SIMP_TAC list_ss [SF_SEM___STAR_ASSOC_COMM1] THEN
   SIMP_TAC std_ss [Once SF_SEM___STAR_THM] THEN
   SIMP_TAC std_ss [GSYM RIGHT_EXISTS_AND_THM] THEN

   POP_ASSUM (fn thm => MP_TAC (Q.ISPECL
      [‘fL':'a list’, ‘t:'b ds_value option list’, ‘s:'c -> 'b ds_value’] thm)) THEN
   HO_MATCH_MP_TAC (prove (“(?X. (!h1 h2. b' h1 h2 = (b h2 /\ X h1 h2)) /\ (a' = ?h1 h2. (a h2 /\ X h1 h2))) ==>
                          ((!h. (a h = b h)) ==> (a' = ?h1 h2. b' h1 h2))”, METIS_TAC[])) THEN
   Q.EXISTS_TAC ‘\h1 h2. IS_SOME h /\  SF_SEM s h1 (sf_tree fL' es (dse_const (THE h))) /\
      (h'' = FUNION h1 h2) /\ DISJOINT (FDOM h1) (FDOM h2) /\
      DS_POINTS_TO s h2 e [h', dse_const (THE h)]’ THEN
   CONJ_TAC THEN1 (
      SIMP_TAC std_ss [] THEN
      REPEAT GEN_TAC THEN
      EQ_TAC THEN STRIP_TAC THENL [
         FULL_SIMP_TAC list_ss [SF_SEM_def, DS_POINTS_TO_def,
            FDOM_FUNION, IN_UNION, IN_SING, DS_EXPRESSION_EVAL_VALUE_def,
            FUNION_DEF] THEN
         METIS_TAC[],

         FULL_SIMP_TAC list_ss [SF_SEM_def, DS_POINTS_TO_def,
            FDOM_FUNION, IN_UNION, IN_SING, DS_EXPRESSION_EVAL_VALUE_def,
            FUNION_DEF] THEN
         Q.EXISTS_TAC ‘h1'’ THEN
         Q.EXISTS_TAC ‘h2’ THEN
         ASM_SIMP_TAC std_ss [] THEN
         Q.PAT_X_ASSUM ‘h' IN FDOM X’ MP_TAC THEN
         ASM_SIMP_TAC std_ss [FUNION_DEF]
      ]
   ) THEN

   SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM] THEN
   Cases_on ‘IS_DSV_NIL (DS_EXPRESSION_EVAL s e)’ THEN ASM_SIMP_TAC std_ss [] THEN
   Cases_on ‘IS_SOME h’ THEN ASM_SIMP_TAC std_ss [] THEN
   Cases_on ‘EVERY IS_SOME t’ THEN ASM_SIMP_TAC std_ss [] THEN


   EQ_TAC THEN
   STRIP_TAC THENL [
      Cases_on ‘hL’ THEN
      FULL_SIMP_TAC list_ss [ALL_DISJOINT_def] THEN
      Q.EXISTS_TAC ‘h'''’ THEN
      Q.EXISTS_TAC ‘DRESTRICT h'' (FDOM h'' DIFF FDOM h''')’ THEN
      Q.EXISTS_TAC ‘t'’ THEN
      Q.EXISTS_TAC ‘n’ THEN

      FULL_SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def,
         DRESTRICT_DEF, IN_INTER, IN_DIFF] THEN
      SIMP_TAC std_ss [GSYM CONJ_ASSOC] THEN
      MATCH_MP_TAC (prove (“(a /\ (e1 = e2)) /\
                            (a /\ (e2 = e1) ==> b /\ c /\ d /\ f) ==>
                            (a /\ b /\ c /\ d /\ (e1 = e2) /\ f)”,
                           METIS_TAC[])) THEN
      REPEAT CONJ_TAC THENL [
         STRIP_TAC THEN
         ‘GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) IN
          FDOM (FUNION h''' (FOLDR FUNION FEMPTY t'))’ by (
            ASM_SIMP_TAC std_ss [FUNION_DEF, IN_UNION]
         ) THEN
         POP_ASSUM MP_TAC THEN
         ASM_SIMP_TAC std_ss [] THEN
         SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE],


         Q.PAT_X_ASSUM ‘FUNION h''' X = Y’ MP_TAC THEN
         ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, IN_UNION, EXTENSION,
            FDOM_DOMSUB, IN_DELETE, DRESTRICT_DEF, IN_INTER, IN_DIFF] THEN
         REPEAT STRIP_TAC THENL [
            Cases_on ‘x IN FDOM h''’ THEN ASM_SIMP_TAC std_ss [] THEN
            METIS_TAC[],

            Cases_on ‘x IN FDOM h'''’ THEN ASM_SIMP_TAC std_ss [] THEN
            Q.PAT_X_ASSUM ‘!x. P x’ (fn thm => MP_TAC (Q.ISPEC ‘x:'b’ thm)) THEN
            ASM_SIMP_TAC std_ss [FDOM_DOMSUB, DOMSUB_FAPPLY_THM] THEN
            METIS_TAC[],

            Cases_on ‘x IN FDOM h'''’ THEN ASM_SIMP_TAC std_ss [] THEN
            Q.PAT_X_ASSUM ‘!x. P x’ (fn thm => MP_TAC (Q.ISPEC ‘x:'b’ thm)) THEN
            ASM_SIMP_TAC std_ss [FDOM_DOMSUB, DOMSUB_FAPPLY_THM] THEN
            METIS_TAC[]
         ],


         REPEAT STRIP_TAC THENL [
            Q.PAT_X_ASSUM ‘X = t’ (fn thm => ASM_REWRITE_TAC [GSYM thm]) THEN
            Induct_on ‘fL’ THENL [
               SIMP_TAC list_ss [],
               ASM_SIMP_TAC list_ss [HEAP_READ_ENTRY_def, DRESTRICT_DEF,
                                     IN_INTER, IN_DIFF]
            ],


            Q.PAT_X_ASSUM ‘FUNION h''' (FOLDR FUNION FEMPTY t') = Y’ MP_TAC THEN
            Q.PAT_X_ASSUM ‘FUNION h''' X = Y’ (fn thm =>
               ASM_REWRITE_TAC [Once (GSYM thm)] THEN
               ASSUME_TAC thm
            ) THEN
            ‘h''' \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) = h'''’ by (
               ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FDOM_DOMSUB,
                                    IN_DELETE, DOMSUB_FAPPLY_THM] THEN
               METIS_TAC[]
            ) THEN
            ASM_SIMP_TAC std_ss [DOMSUB_FUNION] THEN
            MATCH_MP_TAC (prove (“(a = b) ==> (a ==> b)”, METIS_TAC[])) THEN
            MATCH_MP_TAC FUNION_EQ THEN

            SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY,
               DRESTRICT_DEF, FDOM_DOMSUB, IN_UNION, IN_DELETE, IN_DIFF] THEN
            REPEAT STRIP_TAC THENL [
               Q.PAT_X_ASSUM ‘EVERY X (FMAP FDOM t')’ MP_TAC THEN
               REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
               Induct_on ‘t'’ THENL [
                  SIMP_TAC list_ss [FDOM_FEMPTY, NOT_IN_EMPTY],

                  FULL_SIMP_TAC list_ss [FUNION_DEF, IN_UNION, DISJOINT_DEF,
                     EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
                  METIS_TAC[]
               ],

               METIS_TAC[]
            ],


            METIS_TAC[],


            SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY,
               IN_DIFF] THEN
            METIS_TAC[],


            Cases_on ‘h’ THEN (
               FULL_SIMP_TAC list_ss [optionTheory.IS_SOME_DEF]
            ) THEN
            FULL_SIMP_TAC list_ss [HEAP_READ_ENTRY_THM, DS_POINTS_TO_def,
               DRESTRICT_DEF, IN_INTER, IN_DIFF, DS_EXPRESSION_EVAL_def]
         ]
      ],



      FULL_SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def] THEN
      Q.EXISTS_TAC ‘h1::hL’ THEN
      Q.EXISTS_TAC ‘MAX n n'’ THEN
      ASM_SIMP_TAC list_ss [ALL_DISJOINT_def, FUNION_DEF, IN_UNION] THEN
      ‘~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) IN FDOM h1)’ by (
         FULL_SIMP_TAC std_ss [DISJOINT_DEF, NOT_IN_EMPTY, EXTENSION, IN_INTER] THEN
         METIS_TAC[]
      ) THEN
      REPEAT STRIP_TAC THENL [
         Cases_on ‘h’ THEN
         FULL_SIMP_TAC std_ss [optionTheory.IS_SOME_DEF] THEN
         FULL_SIMP_TAC list_ss [HEAP_READ_ENTRY_THM, FUNION_DEF,
            IN_UNION, DS_POINTS_TO_def, DS_EXPRESSION_EVAL_def],


         Q.PAT_X_ASSUM ‘X = t’ (fn thm => ASM_REWRITE_TAC [GSYM thm]) THEN
         Induct_on ‘fL’ THENL [
            SIMP_TAC list_ss [],

            ASM_SIMP_TAC list_ss [HEAP_READ_ENTRY_def, DRESTRICT_DEF, IN_INTER, IN_DIFF,
               FUNION_DEF, IN_UNION]
         ],



         ‘DISJOINT (FDOM h1) (FDOM (FOLDR FUNION FEMPTY hL))’ by (
            ASM_SIMP_TAC std_ss [] THEN
            FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY,
               IN_INTER, FDOM_DOMSUB, IN_DELETE] THEN
            METIS_TAC[]
         ) THEN
         Q.PAT_X_ASSUM ‘DISJOINT X Y’ MP_TAC THEN
         REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
         Induct_on ‘hL’ THENL [
            SIMP_TAC list_ss [],

            REPEAT STRIP_TAC THEN
            FULL_SIMP_TAC list_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY,
               IN_INTER, FUNION_DEF, IN_UNION] THEN
            METIS_TAC[]
         ],



         SIMP_TAC std_ss [DOMSUB_FUNION] THEN
         ‘h1 \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) = h1’ suffices_by (STRIP_TAC THEN
            ASM_REWRITE_TAC[]
         ) THEN
         SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_DOMSUB, EXTENSION, IN_DELETE,
            DOMSUB_FAPPLY_THM] THEN
         METIS_TAC[],


         ‘n' <= MAX n n'’ by SIMP_TAC arith_ss [] THEN
         METIS_TAC[SF_SEM___sf_tree_len_THM],


         ‘n <= MAX n n'’ by SIMP_TAC arith_ss [] THEN
         Q.ABBREV_TAC ‘L = (ZIP (t,hL))’ THEN
         POP_ASSUM (fn thm => ALL_TAC) THEN
         Induct_on ‘L’ THENL [
            SIMP_TAC list_ss [],

            SIMP_TAC list_ss [] THEN
            GEN_TAC THEN
            Cases_on ‘h''''’ THEN
            ASM_SIMP_TAC std_ss [] THEN
            METIS_TAC[SF_SEM___sf_tree_len_THM]
         ]
      ]
   ]
]);




val SF_SEM___sf_tree_EXISTS_THM = store_thm ("SF_SEM___sf_tree_EXISTS_THM",
  “!s h fL es e.
   SF_SEM s h (sf_tree fL es e) = (
      if (DS_EXPRESSION_EQUAL s e es) then
         (h = FEMPTY)
      else
         (?cL. (LENGTH cL = LENGTH fL) /\
               (SF_SEM s h (sf_star
                 (sf_points_to e (MAP (\(f, c). (f, dse_const c)) (ZIP (fL, cL))))
                 (FOLDR (\c sf. sf_star (sf_tree fL es (dse_const c)) sf) sf_emp cL)))))”,


   REWRITE_TAC [SF_SEM___sf_tree_THM1, SF_SEM___sf_tree_THM2] THEN
   REPEAT GEN_TAC THEN
   Cases_on ‘DS_EXPRESSION_EQUAL s e es’ THEN ASM_REWRITE_TAC[] THEN

   EQ_TAC THENL [
      STRIP_TAC THEN
      Q.EXISTS_TAC ‘MAP THE cL’ THEN
      FULL_SIMP_TAC list_ss [] THEN
      ‘((MAP (\(f,c). (f,(dse_const c):('b, 'a) ds_expression)) (ZIP (fL,MAP THE cL))) =
        (MAP (\(f,c). (f,dse_const (THE c))) (ZIP (fL,cL)))) /\

       (!fL:'c list.
        ((FOLDR (\c sf. sf_star (sf_tree fL es (dse_const c)) sf) sf_emp
            (MAP THE cL)) =
        (FOLDR (\c sf. sf_star (sf_tree fL es (dse_const (THE c))) sf)
            sf_emp cL)))’ suffices_by METIS_TAC[] THEN


      Q.PAT_X_ASSUM ‘LENGTH cL = LENGTH fL’ MP_TAC THEN
      REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
      Q.SPEC_TAC (‘fL’, ‘fL’) THEN
      Induct_on ‘cL’ THENL [
         Cases_on ‘fL’ THEN
         SIMP_TAC list_ss [],

         Cases_on ‘fL’ THEN
         ASM_SIMP_TAC list_ss [ds_spatial_formula_11] THEN
         METIS_TAC[]
      ],



      STRIP_TAC THEN
      Q.EXISTS_TAC ‘MAP SOME cL’ THEN
      FULL_SIMP_TAC list_ss [] THEN
      CONJ_TAC THEN1 (
         REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
         Induct_on ‘cL’ THENL [
            SIMP_TAC list_ss [],
            ASM_SIMP_TAC list_ss []
         ]
      ) THEN
      ‘((MAP (\(f,c). (f,(dse_const (THE c)):('b, 'a) ds_expression)) (ZIP (fL,MAP SOME cL))) =
        (MAP (\(f,c). (f,dse_const c)) (ZIP (fL,cL)))) /\

       (!fL:'c list.
        ((FOLDR (\c sf. sf_star (sf_tree fL es (dse_const (THE c))) sf) sf_emp
            (MAP SOME cL)) =
        (FOLDR (\c sf. sf_star (sf_tree fL es (dse_const c)) sf)
            sf_emp cL)))’ suffices_by METIS_TAC[] THEN


      Q.PAT_X_ASSUM ‘LENGTH cL = LENGTH fL’ MP_TAC THEN
      REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
      Q.SPEC_TAC (‘fL’, ‘fL’) THEN
      Induct_on ‘cL’ THENL [
         Cases_on ‘fL’ THEN
         SIMP_TAC list_ss [],

         Cases_on ‘fL’ THEN
         ASM_SIMP_TAC list_ss [ds_spatial_formula_11] THEN
         METIS_TAC[]
      ]
   ]);






val SF_SEM___sf_tree_THM = store_thm ("SF_SEM___sf_tree_THM",
  “!s h fL es e.
   SF_SEM s h (sf_tree fL es e) = (
      if (DS_EXPRESSION_EQUAL s e es) then
         (h = FEMPTY)
      else
         (let cL = MAP (\f. h ' (DS_EXPRESSION_EVAL_VALUE s e) ' f) fL in
               (SF_SEM s h (sf_star
                 (sf_points_to e (MAP (\(f, c). (f, dse_const c)) (ZIP (fL, cL))))
                 (FOLDR (\c sf. sf_star (sf_tree fL es (dse_const c)) sf) sf_emp cL)))))”,


   REWRITE_TAC [SF_SEM___sf_tree_EXISTS_THM] THEN
   REPEAT GEN_TAC THEN
   Cases_on ‘DS_EXPRESSION_EQUAL s e es’ THEN ASM_REWRITE_TAC[] THEN

   Tactical.REVERSE EQ_TAC THEN1 (
      METIS_TAC[LENGTH_MAP]
   ) THEN
   REPEAT STRIP_TAC THEN
   ‘?cL. cL =  MAP (\f. h ' (DS_EXPRESSION_EVAL_VALUE s e) ' f) fL’ by METIS_TAC[] THEN
   FULL_SIMP_TAC std_ss [LET_THM, SF_SEM_def] THEN
   Q.EXISTS_TAC ‘h1’ THEN
   Q.EXISTS_TAC ‘h2’ THEN
   ASM_SIMP_TAC std_ss [] THEN
   ‘cL' = cL’ suffices_by (STRIP_TAC THEN
      METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC std_ss [FUNION_DEF, IN_SING] THEN

   Q.PAT_X_ASSUM ‘LENGTH X = LENGTH Y’ MP_TAC THEN
   Q.PAT_X_ASSUM ‘FDOM h1 = X’ MP_TAC THEN
   Q.PAT_X_ASSUM ‘DS_POINTS_TO s h1 X Y’ MP_TAC THEN
   REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
   Q.SPEC_TAC (‘fL’, ‘fL’) THEN
   Q.SPEC_TAC (‘cL’, ‘cL’) THEN
   REWRITE_TAC [AND_IMP_INTRO, GSYM CONJ_ASSOC] THEN

   Induct_on ‘cL’ THENL [
      Cases_on ‘fL’ THEN SIMP_TAC list_ss [],

      Cases_on ‘fL’ THEN SIMP_TAC list_ss [] THEN
      REPEAT STRIP_TAC THENL [
         FULL_SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EVAL_def,
            DS_EXPRESSION_EVAL_VALUE_def],

         Q.PAT_X_ASSUM ‘!fL. P fL’ MATCH_MP_TAC THEN
         FULL_SIMP_TAC list_ss [DS_POINTS_TO_def]
      ]
   ])






val sf_ls_def = Define ‘
   sf_ls f e1 e2 = sf_tree [f] e2 e1’;

val sf_list_def = Define ‘
   sf_list f e = sf_ls f e dse_nil’;



val SF_SEM___sf_ls_EXISTS_THM = store_thm ("SF_SEM___sf_ls_EXISTS_THM",
  “!s h f e1 e2.
   SF_SEM s h (sf_ls f e1 e2) = (
      if (DS_EXPRESSION_EQUAL s e1 e2) then
         (h = FEMPTY)
      else
         (?c. (SF_SEM s h (sf_star
                 (sf_points_to e1 [f, dse_const c])
                 (sf_ls f (dse_const c) e2))))
   )”,

SIMP_TAC std_ss [sf_ls_def, SF_SEM___sf_tree_EXISTS_THM] THEN
REPEAT GEN_TAC THEN
Cases_on ‘DS_EXPRESSION_EQUAL s e1 e2’ THEN ASM_REWRITE_TAC[] THEN
EQ_TAC THENL [
   STRIP_TAC THEN
   Cases_on ‘cL’ THEN FULL_SIMP_TAC list_ss [] THEN
   Cases_on ‘t’ THEN FULL_SIMP_TAC list_ss [] THEN
   Q.EXISTS_TAC ‘h'’ THEN
   FULL_SIMP_TAC std_ss [SF_SEM_def, FUNION_FEMPTY_2] THEN
   METIS_TAC[],

   STRIP_TAC THEN
   Q.EXISTS_TAC ‘[c]’ THEN
   FULL_SIMP_TAC list_ss [SF_SEM_def, FUNION_FEMPTY_2,
      FDOM_FEMPTY, DISJOINT_EMPTY] THEN
   METIS_TAC[]
])




val SF_SEM___sf_ls_THM = store_thm ("SF_SEM___sf_ls_THM",
  “!s h f e1 e2.
   SF_SEM s h (sf_ls f e1 e2) = (
      if (DS_EXPRESSION_EQUAL s e1 e2) then
         (h = FEMPTY)
      else
         (let c = h ' (DS_EXPRESSION_EVAL_VALUE s e1) ' f in
          (SF_SEM s h (sf_star
                 (sf_points_to e1 [f, dse_const c])
                 (sf_ls f (dse_const c) e2))))
   )”,

SIMP_TAC list_ss [sf_ls_def, SF_SEM___sf_tree_THM, LET_THM] THEN
SIMP_TAC std_ss [SF_SEM_def, FDOM_FEMPTY, DISJOINT_EMPTY, FUNION_FEMPTY_2])


val SF_SEM___sf_ls_len_def = Define ‘
  (SF_SEM___sf_ls_len s h f 0 e1 e2 = ((h = FEMPTY) /\ (PF_SEM s (pf_equal e1 e2)))) /\
  (SF_SEM___sf_ls_len s h f (SUC n) e1 e2 = (
      (PF_SEM s (pf_unequal e1 e2)) /\
       ~IS_DSV_NIL (DS_EXPRESSION_EVAL s e1) /\
       (let e1_eval =  GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1) in (
          (e1_eval IN (FDOM h)) /\
          (f IN FDOM (h ' e1_eval)) /\
          (SF_SEM___sf_ls_len s (h \\ (e1_eval)) f n (dse_const (h ' e1_eval ' f)) e2)))))’



val SF_SEM___sf_ls_def = Define ‘
  (SF_SEM___sf_ls s h f e1 e2 = ?n. SF_SEM___sf_ls_len s h f n e1 e2)’


val SF_SEM___sf_ls_SEM = store_thm ("SF_SEM___sf_ls_SEM",
   “!s h f e1 e2. SF_SEM s h (sf_ls f e1 e2) =
         SF_SEM___sf_ls s h f e1 e2”,

SIMP_TAC std_ss [sf_ls_def, SF_SEM_def, SF_SEM___sf_tree_def, SF_SEM___sf_ls_def,
EQ_IMP_THM, FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
CONJ_TAC THENL [
   Induct_on ‘n’ THENL [
      REPEAT STRIP_TAC THEN
      Q.EXISTS_TAC ‘0’ THEN
      FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, SF_SEM___sf_ls_len_def],

      SIMP_TAC list_ss [SF_SEM___sf_tree_len_def] THEN
      REPEAT STRIP_TAC THENL [
         Q.EXISTS_TAC ‘0’ THEN
         ASM_SIMP_TAC std_ss [SF_SEM___sf_ls_len_def],


         Cases_on ‘hL’ THEN FULL_SIMP_TAC list_ss [] THEN
         Cases_on ‘t’ THEN FULL_SIMP_TAC list_ss [] THEN
         RES_TAC THEN

         Q.EXISTS_TAC ‘SUC n'’ THEN
         FULL_SIMP_TAC std_ss [SF_SEM___sf_ls_len_def, LET_THM, FUNION_FEMPTY_2] THEN
         Cases_on ‘HEAP_READ_ENTRY s h e1 f’ THEN FULL_SIMP_TAC std_ss [] THEN
         FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM] THEN
         METIS_TAC[]
      ]
   ],



   Induct_on ‘n’ THENL [
      REPEAT STRIP_TAC THEN
      Q.EXISTS_TAC ‘0’ THEN
      FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, SF_SEM___sf_ls_len_def],

      SIMP_TAC list_ss [SF_SEM___sf_ls_len_def, LET_THM] THEN
      REPEAT STRIP_TAC THEN
      RES_TAC THEN
      Q.EXISTS_TAC ‘SUC n'’ THEN

      FULL_SIMP_TAC list_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, HEAP_READ_ENTRY_def] THEN
      Q.EXISTS_TAC ‘[h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1)]’ THEN
      ASM_SIMP_TAC list_ss [ALL_DISJOINT_def, FUNION_FEMPTY_2]
   ]
]);


val BALANCED_SF_SEM___sf_ls_len = store_thm ("BALANCED_SF_SEM___sf_ls_len",
   “!s h f n e1 e2.
      BALANCED_SF_SEM___sf_tree_len s h [f] n e2 e1 =
      SF_SEM___sf_ls_len s h f n e1 e2
   ”,

   Induct_on ‘n’ THENL [
      SIMP_TAC std_ss [SF_SEM___sf_ls_len_def, BALANCED_SF_SEM___sf_tree_len_def],

      SIMP_TAC list_ss [SF_SEM___sf_ls_len_def, BALANCED_SF_SEM___sf_tree_len_def, LET_THM] THEN
      REPEAT STRIP_TAC THEN EQ_TAC THENL [
         STRIP_TAC THEN
         Cases_on ‘hL’ THEN FULL_SIMP_TAC list_ss [] THEN
         Cases_on ‘t’ THEN FULL_SIMP_TAC list_ss [] THEN
         FULL_SIMP_TAC std_ss [FUNION_FEMPTY_2, HEAP_READ_ENTRY_THM] THEN
         Q.PAT_X_ASSUM ‘BALANCED_SF_SEM___sf_tree_len s h' [f] n e2 X’ MP_TAC THEN
         ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_def],

         STRIP_TAC THEN
         ASM_SIMP_TAC std_ss [] THEN
         Q.EXISTS_TAC ‘[h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1)]’ THEN
         ASM_SIMP_TAC list_ss [HEAP_READ_ENTRY_def, ALL_DISJOINT_def,
            FUNION_FEMPTY_2] THEN
         METIS_TAC[]
      ]
   ]);






val sf_bin_tree_def = Define ‘
   sf_bin_tree (f1, f2) e = sf_tree [f1;f2] dse_nil e’;



val SF_SEM___sf_bin_tree_EXISTS_THM = store_thm ("SF_SEM___sf_bin_tree_EXISTS_THM",
  “!s h f1 f2 e.
   SF_SEM s h (sf_bin_tree (f1,f2) e) = (
      if (DS_EXPRESSION_EQUAL s e dse_nil) then
         (h = FEMPTY)
      else
         (?c1 c2.
            (SF_SEM s h (sf_star
                 (sf_points_to e [(f1, dse_const c1);(f2, dse_const c2)])
                 (sf_star (sf_bin_tree (f1,f2) (dse_const c1))
                          (sf_bin_tree (f1,f2) (dse_const c2)))))
         )
   )”,


SIMP_TAC list_ss [sf_bin_tree_def, SF_SEM___sf_tree_EXISTS_THM] THEN

REPEAT GEN_TAC THEN
Cases_on ‘DS_EXPRESSION_EQUAL s e dse_nil’ THEN ASM_REWRITE_TAC[] THEN
EQ_TAC THENL [
   STRIP_TAC THEN
   Cases_on ‘cL’ THEN FULL_SIMP_TAC list_ss [] THEN
   Cases_on ‘t’ THEN FULL_SIMP_TAC list_ss [] THEN
   Cases_on ‘t'’ THEN FULL_SIMP_TAC list_ss [] THEN
   Q.EXISTS_TAC ‘h'’ THEN
   Q.EXISTS_TAC ‘h''’ THEN
   FULL_SIMP_TAC std_ss [SF_SEM_def, FUNION_FEMPTY_2] THEN
   Q.EXISTS_TAC ‘h1’ THEN
   Q.EXISTS_TAC ‘h2’ THEN
   ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[],


   STRIP_TAC THEN
   Q.EXISTS_TAC ‘[c1;c2]’ THEN
   FULL_SIMP_TAC list_ss [SF_SEM_def, FUNION_FEMPTY_2,
      FDOM_FEMPTY, DISJOINT_EMPTY] THEN
   METIS_TAC[]
]);


val SF_SEM___sf_bin_tree_THM = store_thm ("SF_SEM___sf_bin_tree_THM",
  “!s h f1 f2 e.
   SF_SEM s h (sf_bin_tree (f1,f2) e) = (
      if (DS_EXPRESSION_EQUAL s e dse_nil) then
         (h = FEMPTY)
      else
         (let c1 = h ' (DS_EXPRESSION_EVAL_VALUE s e) ' f1 in
          let c2 = h ' (DS_EXPRESSION_EVAL_VALUE s e) ' f2 in
            (SF_SEM s h (sf_star
                 (sf_points_to e [(f1, dse_const c1);(f2, dse_const c2)])
                 (sf_star (sf_bin_tree (f1,f2) (dse_const c1))
                          (sf_bin_tree (f1,f2) (dse_const c2)))))
         )
   )”,


SIMP_TAC list_ss [sf_bin_tree_def, SF_SEM___sf_tree_THM, LET_THM] THEN
SIMP_TAC std_ss [SF_SEM_def, FDOM_FEMPTY, DISJOINT_EMPTY, FUNION_FEMPTY_2])








val SF_SEM___sf_points_to_THM = store_thm ("SF_SEM___sf_points_to_THM",
“
   (SF_SEM s h (sf_star (sf_points_to e a) sf)) =

    DS_POINTS_TO s h e a /\
    (SF_SEM s (h \\ (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e))) sf)”,

   SIMP_TAC std_ss [SF_SEM_def, LET_THM, DS_POINTS_TO_def] THEN
   Q.ABBREV_TAC ‘e_eval = GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)’ THEN
   EQ_TAC THENL [
      STRIP_TAC THEN
      ASM_SIMP_TAC std_ss [FUNION_DEF, IN_UNION, IN_SING, DOMSUB_FUNION, DS_EXPRESSION_EVAL_VALUE_def] THEN
      ‘h1 \\ e_eval = FEMPTY’ by (
         ASM_SIMP_TAC std_ss [GSYM FDOM_EQ_EMPTY, FDOM_DOMSUB, EXTENSION, IN_DELETE,
            IN_SING, NOT_IN_EMPTY, DS_EXPRESSION_EVAL_VALUE_def]
      ) THEN
      ‘h2 \\ e_eval = h2’ by (
         FULL_SIMP_TAC std_ss [DISJOINT_DEF, GSYM fmap_EQ_THM, FDOM_DOMSUB, EXTENSION, IN_DELETE,
            DOMSUB_FAPPLY_NEQ, NOT_IN_EMPTY, IN_INTER, IN_SING,
            DS_EXPRESSION_EVAL_VALUE_def] THEN
         METIS_TAC[]
      ) THEN
      ASM_SIMP_TAC std_ss [FUNION_FEMPTY_1],


      STRIP_TAC THEN
      Q.EXISTS_TAC ‘FEMPTY |+ (e_eval, h ' e_eval)’ THEN
      Q.EXISTS_TAC ‘h \\ e_eval’ THEN

      ASM_SIMP_TAC std_ss [] THEN
      REPEAT STRIP_TAC THENL [
         SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF,
            FDOM_FUPDATE, IN_SING, FDOM_FEMPTY, FAPPLY_FUPDATE,
            COND_RATOR, COND_RAND, FDOM_DOMSUB] THEN
         REPEAT STRIP_TAC THENL [
            SIMP_TAC std_ss [EXTENSION, IN_SING, IN_UNION, IN_DELETE] THEN
            METIS_TAC[],

            METIS_TAC[DOMSUB_FAPPLY_NEQ],
            METIS_TAC[DOMSUB_FAPPLY_NEQ]
         ],

         SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_SING, IN_INTER, IN_DELETE,
            FDOM_FUPDATE, FDOM_FEMPTY, FDOM_DOMSUB],

         ASM_SIMP_TAC std_ss [FDOM_DOMSUB, FDOM_FUPDATE, FDOM_FEMPTY, DS_EXPRESSION_EVAL_VALUE_def],

         SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT],

         ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE]
      ]
   ]);


(*
val SF_SEM_LIST_LEN___LIST_SEM = store_thm ("SF_SEM_LIST_LEN___LIST_SEM",
``!s h n e1 e2.
SF_SEM_LIST_LEN s h n e1 e2 = ?l. (
   (LENGTH l = (SUC n)) /\
   (HD l = (DS_EXPRESSION_EVAL s e1)) /\ (LAST l = (DS_EXPRESSION_EVAL s e2)) /\
   (!m. (m < n) ==> (DS_POINTS_TO s h (dse_const (EL m l)) (dse_const (EL (SUC m) l)))) /\
   EVERY (\x. ~IS_DSV_NIL x) (BUTLAST l) /\ ALL_DISTINCT l /\
   (FDOM (h:'b stack) = (LIST_TO_SET (MAP GET_DSV_VALUE (BUTLAST l))))
)``,


Induct_on `n` THENL [
   SIMP_TAC std_ss [SF_SEM_LIST_LEN_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
      Q.EXISTS_TAC `[DS_EXPRESSION_EVAL s e1]` THEN
      ASM_SIMP_TAC list_ss [FDOM_FEMPTY, listTheory.IN_LIST_TO_SET, EXTENSION, NOT_IN_EMPTY],

      Cases_on `l` THEN FULL_SIMP_TAC list_ss [LENGTH_NIL] THEN
      Q.PAT_X_ASSUM `t = []` ASSUME_TAC THEN
      FULL_SIMP_TAC list_ss [] THEN
      `FDOM h = EMPTY` by (
         ASM_SIMP_TAC list_ss [EXTENSION, IN_LIST_TO_SET, NOT_IN_EMPTY]
      ) THEN
      ASM_SIMP_TAC list_ss [GSYM fmap_EQ_THM, NOT_IN_EMPTY, FDOM_FEMPTY]
   ],


   FULL_SIMP_TAC std_ss [SF_SEM_LIST_LEN_def, LET_THM] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
      Q.EXISTS_TAC `(DS_EXPRESSION_EVAL s e1)::l` THEN
      ASM_SIMP_TAC list_ss [] THEN
      Cases_on `l` THEN FULL_SIMP_TAC list_ss [] THEN
      Q.PAT_X_ASSUM `h' = X` (fn thm => ASSUME_TAC (GSYM thm)) THEN
      FULL_SIMP_TAC list_ss [EXTENSION, FDOM_DOMSUB, IN_DELETE, IN_LIST_TO_SET,
         MEM] THEN
      REPEAT CONJ_TAC THENL [
         REPEAT STRIP_TAC THEN
         Cases_on `m` THENL [
            FULL_SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EVAL_def],

            FULL_SIMP_TAC list_ss [] THEN
            `DS_POINTS_TO s (h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1))
              (dse_const (EL n' (h'::t))) (dse_const (EL n' t))` by METIS_TAC[] THEN
            METIS_TAC [DS_POINTS_TO___DOMSUB]
         ],


         Cases_on `t` THENL [
            FULL_SIMP_TAC list_ss [PF_SEM_def, DS_EXPRESSION_EQUAL_def],

            FULL_SIMP_TAC list_ss [] THEN
            Cases_on `h'` THEN1 FULL_SIMP_TAC std_ss [IS_DSV_NIL_def] THEN
            METIS_TAC [GET_DSV_VALUE_def]
         ],

         CCONTR_TAC THEN
         `MEM (DS_EXPRESSION_EVAL s e1) (FRONT (h'::t))` by (
            MATCH_MP_TAC MEM_LAST_FRONT THEN
            FULL_SIMP_TAC std_ss [PF_SEM_def, DS_EXPRESSION_EQUAL_def]
         ) THEN
         FULL_SIMP_TAC list_ss [MEM_MAP] THEN
         METIS_TAC[],

         METIS_TAC[]
      ],


      `~(HD l = LAST l)` by (
         `0 < LENGTH l` by ASM_SIMP_TAC arith_ss[] THEN
         POP_ASSUM MP_TAC THEN
         SIMP_TAC std_ss [EL_HD_LAST] THEN
         ASM_SIMP_TAC arith_ss [EL_ALL_DISTINCT]
      ) THEN
      REPEAT STRIP_TAC THENL [
         POP_ASSUM MP_TAC THEN
         ASM_SIMP_TAC std_ss [PF_SEM_def, DS_EXPRESSION_EQUAL_def],

         Cases_on `l` THEN FULL_SIMP_TAC list_ss [] THEN
         Cases_on `t` THEN FULL_SIMP_TAC list_ss [] THEN
         METIS_TAC[],

         Cases_on `l` THEN FULL_SIMP_TAC list_ss [] THEN
         Cases_on `t` THEN FULL_SIMP_TAC list_ss [] THEN
         FULL_SIMP_TAC list_ss [EXTENSION] THEN
         METIS_TAC[],

         Q.EXISTS_TAC `TL l` THEN
         Cases_on `l` THEN FULL_SIMP_TAC list_ss [] THEN
         Cases_on `t` THEN FULL_SIMP_TAC list_ss [] THEN
         REPEAT STRIP_TAC THENL [
            `0 < SUC n` by DECIDE_TAC THEN
            `DS_POINTS_TO s h (dse_const (EL 0 (h'::h''::t')))
              (dse_const (EL 0 (h''::t')))` by METIS_TAC[] THEN
            POP_ASSUM MP_TAC THEN
            SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EVAL_def] THEN
            ASM_SIMP_TAC std_ss [],


            `SUC m < SUC n` by DECIDE_TAC THEN
            `DS_POINTS_TO s h (dse_const (EL (SUC m) (h'::h''::t')))
              (dse_const (EL (SUC m) (h''::t')))` by METIS_TAC[] THEN
            POP_ASSUM MP_TAC THEN
            SIMP_TAC list_ss [DS_POINTS_TO_def, FDOM_DOMSUB, IN_DELETE,
               DS_EXPRESSION_EVAL_def, DOMSUB_FAPPLY_THM, COND_RATOR, COND_RAND] THEN
            STRIP_TAC THEN
            MATCH_MP_TAC (prove (``(~(a1 = a2)) ==> (~(a2 = a1) /\ ((a1 = a2) ==> b))``, METIS_TAC[])) THEN
            Q.PAT_X_ASSUM `h' = X` ASSUME_TAC THEN
            FULL_SIMP_TAC std_ss [GET_DSV_VALUE_11] THEN
            Cases_on `m` THENL [
               SIMP_TAC list_ss [] THEN METIS_TAC[],

               SIMP_TAC list_ss [] THEN
               `n' < LENGTH t'` by DECIDE_TAC THEN
               METIS_TAC[MEM_EL]
            ],

            ASM_SIMP_TAC list_ss [EXTENSION, IN_LIST_TO_SET, FDOM_DOMSUB, IN_DELETE] THEN
            REPEAT STRIP_TAC THEN
            sg `~(MEM (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1)) (MAP GET_DSV_VALUE (FRONT (h''::t'))))` THENL [
               ALL_TAC,
               METIS_TAC[]
            ] THEN
            SIMP_TAC std_ss [MEM_MAP] THEN
            GEN_TAC THEN
            Cases_on `MEM y (FRONT (h''::t'))` THEN ASM_REWRITE_TAC[] THEN
            Q.PAT_X_ASSUM `h' = X` ASSUME_TAC THEN
            FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
            `~IS_DSV_NIL y` by METIS_TAC[] THEN
            ASM_SIMP_TAC std_ss [GET_DSV_VALUE_11] THEN

            `MEM y (h''::t')` by METIS_TAC[MEM_FRONT] THEN
            FULL_SIMP_TAC list_ss [] THEN
            METIS_TAC[]
         ]
      ]
   ]
]);






val DS_POINTER_LIST_def = Define `
   (DS_POINTER_LIST s h 0 e = [(DS_EXPRESSION_EVAL s e)]) /\
   (DS_POINTER_LIST s h (SUC n) e =
      (DS_EXPRESSION_EVAL s e)::(DS_POINTER_LIST s h n (dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e))))))`;


val DS_POINTER_LIST___LENGTH = store_thm ("DS_POINTER_LIST___LENGTH",
   ``!s h n e. LENGTH (DS_POINTER_LIST s h n e) = (SUC n)``,
   Induct_on `n` THENL [
      SIMP_TAC list_ss [DS_POINTER_LIST_def],
      ASM_SIMP_TAC list_ss [DS_POINTER_LIST_def]
   ]);

val DS_POINTER_LIST___HD = store_thm ("DS_POINTER_LIST___HD",
   ``!s h n e. HD (DS_POINTER_LIST s h n e) = DS_EXPRESSION_EVAL s e``,
   Cases_on `n` THEN
   SIMP_TAC list_ss [DS_POINTER_LIST_def])


val DS_POINTER_LIST___FRONT = store_thm ("DS_POINTER_LIST___FRONT",
   ``(!s h e. FRONT (DS_POINTER_LIST s h 0 e) = []) /\
     (!s h n e. FRONT (DS_POINTER_LIST s h (SUC n) e) = (DS_POINTER_LIST s h n e))``,
   CONJ_TAC THENL [
      SIMP_TAC list_ss [DS_POINTER_LIST_def],

      Induct_on `n` THENL [
         SIMP_TAC list_ss [DS_POINTER_LIST_def],

         ASM_SIMP_TAC list_ss [Once DS_POINTER_LIST_def,
            DS_EXPRESSION_EVAL_def, FRONT_DEF] THEN
         SIMP_TAC list_ss [DS_POINTER_LIST_def]
      ]
   ]);

val DS_POINTER_LIST___NOT_EQ_NIL = store_thm ("DS_POINTER_LIST___NOT_EQ_NIL",
   ``!s h n e. ~(DS_POINTER_LIST s h n e = [])``,

Cases_on `n` THEN (
   SIMP_TAC list_ss [DS_POINTER_LIST_def]
));



val DS_POINTER_LIST___STACK_DOMSUB = store_thm ("DS_POINTER_LIST___STACK_DOMSUB",
``!s h n e v. let l = DS_POINTER_LIST s (h \\ GET_DSV_VALUE v) n e in
(EVERY (\x. ~IS_DSV_NIL x) (FRONT l) /\
 ~IS_DSV_NIL v /\
 ~(MEM v (FRONT l))) ==>
(l = DS_POINTER_LIST s h n e)``,


SIMP_TAC list_ss [LET_THM] THEN
Induct_on `n` THENL [
   SIMP_TAC list_ss [DS_POINTER_LIST_def],

   ASM_SIMP_TAC list_ss [DS_POINTER_LIST_def, FRONT_DEF,
      DS_POINTER_LIST___NOT_EQ_NIL,
      DOMSUB_FAPPLY_THM] THEN
   REPEAT STRIP_TAC THEN
   REPEAT (Q.PAT_X_ASSUM `~(IS_DSV_NIL X)` MP_TAC) THEN
   Q.PAT_X_ASSUM `~(v = X)` ASSUME_TAC THEN
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [GET_DSV_VALUE_11]
]);





val SF_SEM_LIST_LEN___LIST_SEM2 = store_thm ("SF_SEM_LIST_LEN___LIST_SEM2",
``!s h n e1 e2.
SF_SEM_LIST_LEN s h n e1 e2 = (
   let l = DS_POINTER_LIST s h n e1 in
   ((LAST l = (DS_EXPRESSION_EVAL s e2)) /\
   EVERY (\x. ~IS_DSV_NIL x) (BUTLAST l) /\ ALL_DISTINCT l /\
   (((FDOM (h:'b stack))) = (LIST_TO_SET (MAP GET_DSV_VALUE (BUTLAST l)))))
)``,


SIMP_TAC list_ss [SF_SEM_LIST_LEN___LIST_SEM, LET_THM] THEN
REPEAT STRIP_TAC THEN
EQ_TAC THEN STRIP_TAC THENL [
   sg `DS_POINTER_LIST s h n e1 = l` THENL [
      ALL_TAC,
      ASM_SIMP_TAC std_ss []
   ] THEN
   REPEAT (POP_ASSUM MP_TAC) THEN
   Q.SPEC_TAC (`n`, `n`) THEN
   Q.SPEC_TAC (`e1`, `e1`) THEN
   Q.SPEC_TAC (`h`, `h`) THEN
   Q.SPEC_TAC (`l`, `l`) THEN
   Induct_on `n` THENL [
      SIMP_TAC list_ss [] THEN
      Cases_on `l` THENL [
         FULL_SIMP_TAC list_ss [],
         FULL_SIMP_TAC list_ss [DS_POINTER_LIST_def, LENGTH_NIL]
      ],

      Cases_on `l` THEN SIMP_TAC list_ss [] THEN
      Cases_on `t` THEN SIMP_TAC list_ss [] THEN
      REPEAT GEN_TAC THEN
      POP_ASSUM (fn thm => ASSUME_TAC (Q.SPECL [`h'::t'`,
         `h''\\ (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1))`,
         `dse_const h'`] thm)) THEN
      FULL_SIMP_TAC list_ss [AND_IMP_INTRO] THEN
      POP_ASSUM MP_TAC THEN
      MATCH_MP_TAC (prove (``((a' ==> a) /\ ((a' /\ b) ==> b')) ==> ((a ==> b) ==> (a' ==> b'))``, PROVE_TAC[])) THEN
      REPEAT CONJ_TAC THENL [
         STRIP_TAC THEN
         ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def] THEN
         REPEAT STRIP_TAC THENL [
            `SUC m < SUC n` by DECIDE_TAC THEN
            `DS_POINTS_TO s h''
              (dse_const (EL (SUC m) (DS_EXPRESSION_EVAL s e1::h'::t')))
              (dse_const (EL (SUC m) (h'::t')))` by METIS_TAC[] THEN
            POP_ASSUM MP_TAC THEN
            SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EVAL_def,
               FDOM_DOMSUB, IN_DELETE, DOMSUB_FAPPLY_THM] THEN
            STRIP_TAC THEN
            SIMP_TAC std_ss [COND_RATOR, COND_RAND] THEN
            MATCH_MP_TAC (prove (``~(a1 = a2) ==> (~(a1 = a2) /\ ((a2 = a1) ==> b))``, METIS_TAC[])) THEN
            ASM_SIMP_TAC std_ss [GET_DSV_VALUE_11] THEN
            Cases_on `m` THENL [
               SIMP_TAC list_ss [] THEN METIS_TAC[],

               `n' < n` by DECIDE_TAC THEN
               SIMP_TAC list_ss [] THEN METIS_TAC[MEM_EL]
            ],

            ASM_SIMP_TAC list_ss [FDOM_DOMSUB, EXTENSION, IN_LIST_TO_SET, IN_DELETE] THEN
            sg `~MEM (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1)) (MAP GET_DSV_VALUE (FRONT (h'::t')))` THENL [
               ALL_TAC,
               METIS_TAC[]
            ] THEN
            FULL_SIMP_TAC list_ss [MEM_MAP, EVERY_MEM] THEN
            GEN_TAC THEN
            Cases_on `MEM y (FRONT (h'::t'))` THEN ASM_REWRITE_TAC[] THEN
            `MEM y (h'::t') /\ (~IS_DSV_NIL y)` by METIS_TAC[MEM_FRONT] THEN
            FULL_SIMP_TAC list_ss [GET_DSV_VALUE_11] THEN
            METIS_TAC[]
         ],


         STRIP_TAC THEN
         SIMP_TAC list_ss [DS_POINTER_LIST_def] THEN
         POP_ASSUM (fn thm => ASSUME_TAC (GSYM thm)) THEN
         `((h'' ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1)))) = h'` by (
            `0 < SUC n` by DECIDE_TAC THEN
            `DS_POINTS_TO s h''
              (dse_const (EL 0 (DS_EXPRESSION_EVAL s e1::h'::t')))
              (dse_const (EL 0 (h'::t')))` by METIS_TAC[] THEN
            FULL_SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EVAL_def]
         ) THEN
         ASM_SIMP_TAC list_ss [] THEN
         MATCH_MP_TAC (GSYM (SIMP_RULE std_ss [LET_THM] DS_POINTER_LIST___STACK_DOMSUB)) THEN

         Q.PAT_X_ASSUM `h'::t' = X` (fn thm => ASSUME_TAC (GSYM thm)) THEN
         ASM_SIMP_TAC std_ss [] THEN
         METIS_TAC[MEM_FRONT, MEM]
      ]
   ],


   Q.EXISTS_TAC `DS_POINTER_LIST s h n e1` THEN
   ASM_SIMP_TAC std_ss [DS_POINTER_LIST___LENGTH, DS_POINTER_LIST___HD] THEN
   Q.PAT_X_ASSUM `LAST X = Y` (fn thm => ALL_TAC) THEN
   FULL_SIMP_TAC std_ss [SET_EQ_SUBSET] THEN
   Q.PAT_X_ASSUM `FDOM h SUBSET X` (fn thm => (ALL_TAC)) THEN
   REPEAT (POP_ASSUM MP_TAC) THEN
   Q.SPEC_TAC (`e1`, `e1`) THEN
   Induct_on `n` THENL [
      SIMP_TAC std_ss [],

      SIMP_TAC list_ss [DS_POINTER_LIST_def, FRONT_DEF, DS_POINTER_LIST___NOT_EQ_NIL] THEN
      REPEAT STRIP_TAC THEN
      Cases_on `m` THENL [
         ASM_SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EVAL_def, DS_POINTER_LIST___HD] THEN
         FULL_SIMP_TAC list_ss [SUBSET_DEF, IN_LIST_TO_SET],

         Q.ABBREV_TAC `e1':('b, 'a) ds_expression = (dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1))))` THEN
         Q.PAT_X_ASSUM `!e1. P e1` (fn thm => MP_TAC (Q.SPEC `e1'` thm)) THEN
         ASM_SIMP_TAC list_ss [] THEN
         MATCH_MP_TAC (prove (``(a /\ (b ==> c)) ==> ((a ==> b) ==> c)``, PROVE_TAC[])) THEN
         REPEAT STRIP_TAC THENL [
            FULL_SIMP_TAC list_ss [SUBSET_DEF],
            FULL_SIMP_TAC std_ss []
         ]
      ]
   ]
]);





val SF_SEM_EVAL___SF_LIST_0 = store_thm ("SF_SEM_EVAL___SF_LIST_0", ``
   (SF_SEM s h (sf_star (sf_ls_len 0 e1 e2) sf)) =
   (PF_SEM s (pf_equal e1 e2) /\ (SF_SEM s h sf))``,

   SIMP_TAC std_ss [SF_SEM_def, SF_SEM_LIST_LEN_def, FDOM_FEMPTY,
      pred_setTheory.DISJOINT_EMPTY, FUNION_FEMPTY_1]);



val SF_SEM_EVAL___SF_LIST_SUC = store_thm ("SF_SEM_EVAL___SF_LIST_SUC", ``
   (SF_SEM s h (sf_star (sf_ls_len (SUC n) e1 e2) sf)) =
   (~(IS_DSV_NIL (DS_EXPRESSION_EVAL s e1)) /\
    let e1_eval = GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1) in
    (e1_eval IN FDOM h) /\
    (PF_SEM s (pf_unequal e1 e2)) /\
   (SF_SEM s (h \\ e1_eval) (sf_star (sf_ls_len n (dse_const (h '
      e1_eval)) e2) sf)))``,

SIMP_TAC std_ss [SF_SEM_def, SF_SEM_LIST_LEN_def, LET_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, DS_EXPRESSION_EVAL_def] THEN
Q.ABBREV_TAC `e1_eval = GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1)` THEN
Cases_on `~(IS_DSV_NIL (DS_EXPRESSION_EVAL s e1))` THEN ASM_REWRITE_TAC[] THEN
Cases_on `PF_SEM s (pf_unequal e1 e2)` THEN ASM_REWRITE_TAC[] THEN
EQ_TAC THEN REPEAT STRIP_TAC THENL [
   Q.EXISTS_TAC `h1 \\ e1_eval` THEN
   Q.EXISTS_TAC `h2` THEN
   REPEAT STRIP_TAC THENL [
      FULL_SIMP_TAC std_ss [FUNION_DEF, GSYM fmap_EQ_THM,
         FDOM_DOMSUB, IN_UNION, IN_DELETE, EXTENSION, DISJOINT_DEF,
         IN_INTER, NOT_IN_EMPTY, DOMSUB_FAPPLY_NEQ] THEN
      PROVE_TAC[],

      FULL_SIMP_TAC std_ss [FUNION_DEF, GSYM fmap_EQ_THM,
         FDOM_DOMSUB, IN_UNION, IN_DELETE, EXTENSION, DISJOINT_DEF,
         IN_INTER, NOT_IN_EMPTY, DOMSUB_FAPPLY_NEQ] THEN
      PROVE_TAC[],

      FULL_SIMP_TAC std_ss [DISJOINT_DEF,
         IN_INTER, NOT_IN_EMPTY, FDOM_DOMSUB, IN_DELETE, EXTENSION] THEN
      METIS_TAC[],

      ASM_SIMP_TAC std_ss [FUNION_DEF],
      ASM_REWRITE_TAC[]
   ],


   Q.EXISTS_TAC `h1 |+ (e1_eval, h ' e1_eval)` THEN
   Q.EXISTS_TAC `h2` THEN
   REPEAT STRIP_TAC THENL [
      FULL_SIMP_TAC std_ss [FUNION_DEF, GSYM fmap_EQ_THM,
         FDOM_DOMSUB, IN_UNION, IN_DELETE, EXTENSION, DISJOINT_DEF,
         IN_INTER, NOT_IN_EMPTY, DOMSUB_FAPPLY_NEQ, FDOM_FUPDATE,
         IN_INSERT] THEN
      REPEAT STRIP_TAC THENL [
         METIS_TAC[],

         Cases_on `x = e1_eval` THEN (
            ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM]
         ) THEN
         METIS_TAC[]
      ],

      FULL_SIMP_TAC std_ss [DISJOINT_DEF,
         IN_INTER, NOT_IN_EMPTY, FDOM_DOMSUB, IN_DELETE, EXTENSION, FDOM_FUPDATE, IN_INSERT,
         GSYM fmap_EQ_THM, FUNION_DEF, IN_UNION] THEN
      METIS_TAC[],

      SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT],

      SIMP_TAC std_ss [DOMSUB_FUPDATE] THEN
      `h1 \\ e1_eval = h1` by (
         FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_DOMSUB, EXTENSION, IN_DELETE,
            DOMSUB_FAPPLY_NEQ, FUNION_DEF, IN_UNION] THEN
         METIS_TAC[]
      ) THEN
      FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_def, FAPPLY_FUPDATE] THEN
      METIS_TAC[],

      ASM_REWRITE_TAC[]
   ]
]);



val SF_SEM_EVAL___SF_LIST_SUC2 = store_thm ("SF_SEM_EVAL___SF_LIST_SUC2", ``
   !s h.
    SF_SEM s h (sf_star (sf_ls_len (SUC n) e1 e2) sf) =
    (let e = (dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1)))) in
     (PF_SEM s (pf_unequal e1 e2) /\
      SF_SEM s h (sf_star (sf_points_to e1 e) (sf_star (sf_ls_len n e e2) sf))))``,

SIMP_TAC std_ss [SF_EQUIV_def, SF_SEM_EVAL___SF_LIST_SUC, SF_SEM_EVAL___SF_POINTS_TO, LET_THM,
   DS_EXPRESSION_EVAL_def, DS_POINTS_TO_def] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN (
   ASM_SIMP_TAC std_ss []
));



val SF_SEM_EVAL___SF_LIST1 = prove (``
   (SF_SEM s h (sf_star (sf_ls e1 e2) sf)) =
   ?n. (SF_SEM s h (sf_star (sf_ls_len n e1 e2) sf))``,

   SIMP_TAC std_ss [SF_SEM_def] THEN METIS_TAC[])


val SF_SEM_EVAL___SF_LIST = store_thm ("SF_SEM_EVAL___SF_LIST", ``
   (SF_SEM s h (sf_star (sf_ls e1 e2) sf)) =
   (if (PF_SEM s (pf_equal e1 e2)) then
      (SF_SEM s h sf)
    else (
    (~(IS_DSV_NIL (DS_EXPRESSION_EVAL s e1))) /\
    (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1) IN FDOM h) /\
     (SF_SEM s (h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1)) (sf_star (sf_ls (dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1)))) e2) sf))))``,


   SIMP_TAC std_ss [SF_SEM_EVAL___SF_LIST1] THEN
   Cases_on `PF_SEM s (pf_equal e1 e2)` THENL [
      ASM_SIMP_TAC std_ss [] THEN
      EQ_TAC THEN REPEAT STRIP_TAC THENL [
         Cases_on `n` THENL [
            FULL_SIMP_TAC std_ss [SF_SEM_EVAL___SF_LIST_0],
            FULL_SIMP_TAC std_ss [SF_SEM_EVAL___SF_LIST_SUC, PF_SEM_def, LET_THM]
         ],

         Q.EXISTS_TAC `0` THEN
         ASM_SIMP_TAC std_ss [SF_SEM_EVAL___SF_LIST_0]
      ],

      ASM_SIMP_TAC std_ss [] THEN
      EQ_TAC THEN STRIP_TAC THENL [
         Cases_on `n` THENL [
            FULL_SIMP_TAC std_ss [SF_SEM_EVAL___SF_LIST_0],
            FULL_SIMP_TAC std_ss [SF_SEM_EVAL___SF_LIST_SUC, LET_THM] THEN
            METIS_TAC[]
         ],

         Q.EXISTS_TAC `SUC n` THEN
         FULL_SIMP_TAC std_ss [SF_SEM_EVAL___SF_LIST_SUC, PF_SEM_def, LET_THM]
      ]
   ])


val SF_SEM_EVAL1 = prove (
   ``(SF_SEM s h sf_emp = (h = FEMPTY)) /\
     (SF_SEM s h sf_true = T) /\
     (SF_SEM s h (sf_ls e1 e2) = SF_SEM s h (sf_star (sf_ls e1 e2) sf_emp)) /\
     (SF_SEM s h (sf_ls_len n e1 e2) = SF_SEM s h (sf_star (sf_ls_len n e1 e2) sf_emp)) /\
     (SF_SEM s h (sf_points_to e1 e2) = SF_SEM s h (sf_star (sf_points_to e1 e2) sf_emp)) /\

     (SF_SEM s h (sf_star sf_emp sf) = SF_SEM s h sf) /\
     (SF_SEM s h (sf_star (sf_star sf1 sf2) sf3) = SF_SEM s h (sf_star sf1 (sf_star sf2 sf3)))``,

SIMP_TAC std_ss [REWRITE_RULE [SF_EQUIV_def] SF_SEM___STAR_EMP, REWRITE_RULE [SF_EQUIV_def] SF_SEM___STAR_ASSOC] THEN
SIMP_TAC std_ss [SF_SEM_def]);



val SF_SEM_EVAL = save_thm ("SF_SEM_EVAL",
   SIMP_RULE std_ss [FORALL_AND_THM, LET_THM] (GEN_ALL
      (LIST_CONJ [SF_SEM_EVAL1,
                 SF_SEM_EVAL___SF_POINTS_TO,
                 SF_SEM_EVAL___SF_LIST_0,
                 SF_SEM_EVAL___SF_LIST_SUC,
                 SF_SEM_EVAL___SF_LIST])));


*)





val LIST_PF_SEM_def = Define ‘
   LIST_PF_SEM s pfL = PF_SEM s (FOLDR pf_and pf_true pfL)’

val LIST_SF_SEM_def = Define ‘
   LIST_SF_SEM s h sfL =
      SF_SEM s h (FOLDR sf_star sf_emp sfL)’;

val LIST_DS_SEM_def = Define ‘
   LIST_DS_SEM s h (pfL, sfL) = LIST_PF_SEM s pfL /\ LIST_SF_SEM s h sfL’;


val LIST_SEM_INTRO_THM = store_thm ("LIST_SEM_INTRO_THM",
   “(PF_SEM s pf = LIST_PF_SEM s [pf]) /\
     (SF_SEM s h sf = LIST_SF_SEM s h [sf]) /\
     (DS_SEM s h (pf,sf) = LIST_DS_SEM s h ([pf], [sf]))”,

   SIMP_TAC list_ss [PF_SEM_def, LIST_PF_SEM_def,
      LIST_SF_SEM_def, SIMP_RULE std_ss [SF_EQUIV_def] SF_SEM___STAR_EMP,
      DS_SEM_def, LIST_DS_SEM_def]);





val LIST_PF_SEM_THM = store_thm ("LIST_PF_SEM_THM",
   “(LIST_PF_SEM s [] = T) /\
     (LIST_PF_SEM s (pf::l) = (PF_SEM s pf /\ LIST_PF_SEM s l)) /\
     (LIST_PF_SEM s (APPEND l1 l2) = (LIST_PF_SEM s l1 /\ LIST_PF_SEM s l2))”,

   REPEAT STRIP_TAC THENL [
      SIMP_TAC list_ss [LIST_PF_SEM_def, PF_SEM_def],
      SIMP_TAC list_ss [LIST_PF_SEM_def, PF_SEM_def],

      Induct_on ‘l1’ THENL [
         SIMP_TAC list_ss [LIST_PF_SEM_def, PF_SEM_def],
         FULL_SIMP_TAC list_ss [LIST_PF_SEM_def, PF_SEM_def] THEN METIS_TAC[]
      ]
   ]);


val MEM_LIST_PF_SEM = store_thm ("MEM_LIST_PF_SEM",
   “!s pfL. LIST_PF_SEM s pfL = (!pf. MEM pf pfL ==> PF_SEM s pf)”,

   Induct_on ‘pfL’ THENL [
      SIMP_TAC list_ss [LIST_PF_SEM_THM],
      ASM_SIMP_TAC list_ss [LIST_PF_SEM_THM, DISJ_IMP_THM, FORALL_AND_THM]
   ])


val MEM_UNEQ_PF_LIST_def = Define ‘
   MEM_UNEQ_PF_LIST e1 e2 pfL =
   MEM (pf_unequal e1 e2) pfL \/ MEM (pf_unequal e2 e1) pfL’

val MEM_UNEQ_PF_LIST_SEM = store_thm ("MEM_UNEQ_PF_LIST_SEM",
“ !e1 e2 pfL s.
   (MEM_UNEQ_PF_LIST e1 e2 pfL /\
   LIST_PF_SEM s pfL) ==>
   ~(DS_EXPRESSION_EQUAL s e1 e2)”,

   SIMP_TAC std_ss [MEM_LIST_PF_SEM, MEM_UNEQ_PF_LIST_def] THEN
   REPEAT STRIP_TAC THEN (
      RES_TAC THEN
      FULL_SIMP_TAC std_ss [PF_SEM_def, DS_EXPRESSION_EQUAL_def]
   ));


val LIST_PF_SEM_PERM = store_thm ("LIST_PF_SEM_PERM",
“!l1 l2. PERM l1 l2 ==>
          !s. (LIST_PF_SEM s l1 = LIST_PF_SEM s l2)”,

HO_MATCH_MP_TAC PERM_IND THEN
SIMP_TAC list_ss [LIST_PF_SEM_THM] THEN
PROVE_TAC[]);





val DS_FLAT_PF_def = Define
   ‘(DS_FLAT_PF pf_true = []) /\
    (DS_FLAT_PF (pf_and pf1 pf2) = APPEND (DS_FLAT_PF pf1) (DS_FLAT_PF pf2)) /\
    (DS_FLAT_PF x = [x])’


val LIST_PF_SEM_FLAT_INTRO = store_thm ("LIST_PF_SEM_FLAT_INTRO",
   “!s. PF_SEM s pf = LIST_PF_SEM s (DS_FLAT_PF pf)”,

   Induct_on ‘pf’ THENL [
      SIMP_TAC std_ss [DS_FLAT_PF_def, LIST_PF_SEM_THM, PF_SEM_def],
      SIMP_TAC std_ss [DS_FLAT_PF_def, LIST_PF_SEM_THM],
      SIMP_TAC std_ss [DS_FLAT_PF_def, LIST_PF_SEM_THM],
      ASM_SIMP_TAC std_ss [DS_FLAT_PF_def, LIST_PF_SEM_THM, PF_SEM_def]
   ]);

val DS_FLAT_PF_THM = store_thm ("DS_FLAT_PF_THM",
   “!s pfL. LIST_PF_SEM s pfL = LIST_PF_SEM s (FLAT (MAP DS_FLAT_PF pfL))”,

Induct_on ‘pfL’ THEN1 SIMP_TAC list_ss [] THEN
ASM_SIMP_TAC list_ss [LIST_PF_SEM_THM, LIST_PF_SEM_FLAT_INTRO]);


val LIST_SF_SEM_THM = store_thm ("LIST_SF_SEM_THM",
   “(!s h. (LIST_SF_SEM s h [] = (h = FEMPTY))) /\
     (!s h sf. (LIST_SF_SEM s h [sf] = (SF_SEM s h sf))) /\
     (!s h sf l. (LIST_SF_SEM s h (sf::l) = (?h1 h2.
         (h = FUNION h1 h2) /\ DISJOINT (FDOM h1) (FDOM h2) /\
         (SF_SEM s h1 sf /\ LIST_SF_SEM s h2 l)))) /\

     (!s h l1 l2. (LIST_SF_SEM s h (APPEND l1 l2) = (?h1 h2.
         (h = FUNION h1 h2) /\ DISJOINT (FDOM h1) (FDOM h2) /\
         (LIST_SF_SEM s h1 l1 /\ LIST_SF_SEM s h2 l2))))”,

   REPEAT CONJ_TAC THENL [
      SIMP_TAC list_ss [LIST_SF_SEM_def, SF_SEM_def],

      SIMP_TAC list_ss [LIST_SF_SEM_def, SF_SEM_def, FUNION_FEMPTY_2,
         FDOM_FEMPTY, DISJOINT_EMPTY],

      SIMP_TAC list_ss [LIST_SF_SEM_def, SF_SEM_def],

      Induct_on ‘l1’ THENL [
         SIMP_TAC list_ss [LIST_SF_SEM_def, SF_SEM_def, FUNION_FEMPTY_1,
            FDOM_FEMPTY, DISJOINT_EMPTY],

         FULL_SIMP_TAC list_ss [LIST_SF_SEM_def, SF_SEM_def,
            GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
         REPEAT GEN_TAC THEN
         HO_MATCH_MP_TAC (prove (“(!h1 h1' h2'.
                                    (P h1 h1' h2' = Q h2' h1 h1'))
                                     ==>
                                ((?h1 h1' h2'. P h1 h1' h2') =
                                 (?h2 h1' h2'. Q h2 h1' h2'))”, METIS_TAC[])) THEN

         REPEAT STRIP_TAC THEN
         Cases_on ‘SF_SEM s h2' (FOLDR sf_star sf_emp l1)’ THEN ASM_REWRITE_TAC[] THEN
         Cases_on ‘SF_SEM s h2 (FOLDR sf_star sf_emp l2)’ THEN ASM_REWRITE_TAC[] THEN
         Cases_on ‘SF_SEM s h1' h’ THEN ASM_REWRITE_TAC[] THEN
         SIMP_TAC std_ss [FDOM_FUNION, DISJOINT_UNION_BOTH] THEN
         Cases_on ‘DISJOINT (FDOM h2') (FDOM h2)’ THEN ASM_REWRITE_TAC[] THEN
         Cases_on ‘DISJOINT (FDOM h1') (FDOM h2')’ THEN (
            ASM_SIMP_TAC std_ss [DISJOINT_SYM]
         ) THEN
         Cases_on ‘DISJOINT (FDOM h1') (FDOM h2)’ THEN ASM_REWRITE_TAC[] THEN

         MATCH_MP_TAC (prove (“(b1 = b2) ==> ((a = b1) = (a = b2))”, METIS_TAC[])) THEN

         FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
         ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, EXTENSION, IN_UNION,
            DISJ_IMP_THM] THEN
         METIS_TAC[]
      ]
   ]);


val LIST_SF_SEM_PERM = store_thm ("LIST_SF_SEM_PERM",
“!l1 l2. PERM l1 l2 ==>
          !s h. (LIST_SF_SEM s h l1 = LIST_SF_SEM s h l2)”,

HO_MATCH_MP_TAC PERM_IND THEN
SIMP_TAC list_ss [LIST_SF_SEM_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC (prove (“(!h1 h1' h2'.
                           (P h1 h1' h2' = Q h1' h1 h2'))
                              ==>
                        ((?h1 h1' h2'. P h1 h1' h2') =
                        (?h2 h1' h2'. Q h2 h1' h2'))”, METIS_TAC[])) THEN
REPEAT GEN_TAC THEN
Cases_on ‘SF_SEM s h1 y’ THEN ASM_REWRITE_TAC[] THEN
Cases_on ‘SF_SEM s h1' x’ THEN ASM_REWRITE_TAC[] THEN
Cases_on ‘LIST_SF_SEM s h2' l2’ THEN ASM_REWRITE_TAC[] THEN
SIMP_TAC std_ss [FDOM_FUNION, DISJOINT_UNION_BOTH, DISJOINT_SYM] THEN
Cases_on ‘DISJOINT (FDOM h1') (FDOM h2')’ THEN ASM_REWRITE_TAC[] THEN
Cases_on ‘DISJOINT (FDOM h1) (FDOM h2')’ THEN ASM_REWRITE_TAC[] THEN
Cases_on ‘DISJOINT (FDOM h1) (FDOM h1')’ THEN ASM_REWRITE_TAC[] THEN
MATCH_MP_TAC (prove (“(b1 = b2) ==> ((a = b1) = (a = b2))”, METIS_TAC[])) THEN

FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, EXTENSION, IN_UNION,
   DISJ_IMP_THM] THEN
METIS_TAC[])




val DS_FLAT_SF_def = Define
   ‘(DS_FLAT_SF sf_emp = []) /\
    (DS_FLAT_SF (sf_star sf1 sf2) = APPEND (DS_FLAT_SF sf1) (DS_FLAT_SF sf2)) /\
    (DS_FLAT_SF x = [x])’


val LIST_SF_SEM_FLAT_INTRO = store_thm ("LIST_SF_SEM_FLAT_INTRO",
   “!s h sf. SF_SEM s h sf = LIST_SF_SEM s h (DS_FLAT_SF sf)”,

   Induct_on ‘sf’ THENL [
      SIMP_TAC std_ss [DS_FLAT_SF_def, LIST_SF_SEM_THM, SF_SEM_def],
      SIMP_TAC std_ss [DS_FLAT_SF_def, LIST_SF_SEM_THM],
      SIMP_TAC std_ss [DS_FLAT_SF_def, LIST_SF_SEM_THM],
      ASM_SIMP_TAC std_ss [DS_FLAT_SF_def, LIST_SF_SEM_THM, SF_SEM_def]
   ]);



val DS_FLAT_SF_THM = store_thm ("DS_FLAT_SF_THM",
   “!s h sfL. LIST_SF_SEM s h sfL = LIST_SF_SEM s h (FLAT (MAP DS_FLAT_SF sfL))”,

Induct_on ‘sfL’ THEN1 SIMP_TAC list_ss [] THEN
ASM_SIMP_TAC list_ss [LIST_SF_SEM_THM, LIST_SF_SEM_FLAT_INTRO]);



val LIST_DS_SEM_FLAT_INTRO = store_thm ("LIST_DS_SEM_FLAT_INTRO",
   “(!s h sf pf. DS_SEM s h (pf, sf) = LIST_DS_SEM s h ((DS_FLAT_PF pf), DS_FLAT_SF sf)) /\
     (!s sf. PF_SEM s pf = LIST_DS_SEM s FEMPTY (DS_FLAT_PF pf, [])) /\
     (!s h sf. SF_SEM s h sf = LIST_DS_SEM s h ([], DS_FLAT_SF sf))”,

   SIMP_TAC std_ss [DS_SEM_def, LIST_PF_SEM_FLAT_INTRO, LIST_SF_SEM_FLAT_INTRO,
      LIST_DS_SEM_def, LIST_PF_SEM_THM, LIST_SF_SEM_THM]);


val LIST_DS_SEM_THM = store_thm ("LIST_DS_SEM_THM", “
(!s h pfL. (LIST_DS_SEM s h (pfL, []) = LIST_PF_SEM s pfL /\ (h = FEMPTY))) /\
(!s h sfL. (LIST_DS_SEM s h ([], sfL) = LIST_SF_SEM s h sfL)) /\
(!s h pfL sfL e. (LIST_DS_SEM s h (pfL, e::sfL) =
   ?h1 h2. (h = FUNION h1 h2) /\ (DISJOINT (FDOM h1) (FDOM h2)) /\
           LIST_DS_SEM s h2 (pfL, sfL) /\ SF_SEM s h1 e)) /\
(!s h pfL sfL e. (LIST_DS_SEM s h (e::pfL, sfL) =
   LIST_DS_SEM s h (pfL,sfL) /\ PF_SEM s e)) /\

(!s h pfL sfL1 sfL2 e. (LIST_DS_SEM s h (pfL, sfL1++sfL2) =
   ?h1 h2. (h = FUNION h1 h2) /\ (DISJOINT (FDOM h1) (FDOM h2)) /\
           LIST_DS_SEM s h1 (pfL, sfL1) /\ LIST_DS_SEM s h2 (pfL, sfL2)))”,

SIMP_TAC std_ss [LIST_DS_SEM_def, LIST_SF_SEM_THM, LIST_PF_SEM_THM] THEN
METIS_TAC[]);






Theorem LIST_DS_SEM_EVAL1[local]:
  (!s h. LIST_DS_SEM s h ([], []) = (h = FEMPTY)) /\
  (!s h. LIST_DS_SEM s h (pfL, []) = (LIST_PF_SEM s pfL /\ (h = FEMPTY))) /\
  (!s h sfL pfL pf1 pf2.
     LIST_DS_SEM s h ((pf_and pf1 pf2)::sfL, pfL) =
     LIST_DS_SEM s h (pf1 :: pf2 :: sfL, pfL)) /\

  (!s h sfL pfL e1 e2.
     LIST_DS_SEM s h ((pf_equal e1 e2)::sfL, pfL) =
     (DS_EXPRESSION_EQUAL s e1 e2 /\ LIST_DS_SEM s h (sfL, pfL))) /\

  (!s h sfL pfL e1 e2.
     LIST_DS_SEM s h ((pf_unequal e1 e2)::sfL, pfL) =
     (~DS_EXPRESSION_EQUAL s e1 e2 /\ LIST_DS_SEM s h (sfL, pfL)))
Proof
  SIMP_TAC std_ss [LIST_DS_SEM_def, LIST_PF_SEM_THM, LIST_SF_SEM_THM,
                   PF_SEM_def, SF_SEM_def] THEN
  METIS_TAC[]
QED



Theorem LIST_DS_SEM_EVAL2[local]:
  (!s h sfL pfL.
     LIST_DS_SEM s h (sfL, sf_emp::pfL) = LIST_DS_SEM s h (sfL, pfL)) /\

  (!s h sfL pfL sf1 sf2.
     LIST_DS_SEM s h (sfL, (sf_star sf1 sf2)::pfL) =
     LIST_DS_SEM s h (sfL, sf1 :: sf2 :: pfL))
Proof
  SIMP_TAC std_ss [LIST_DS_SEM_def, LIST_PF_SEM_THM, LIST_SF_SEM_THM,
                   PF_SEM_def, SF_SEM_def, FUNION_FEMPTY_1, FDOM_FEMPTY,
                   DISJOINT_EMPTY] THEN
  REPEAT STRIP_TAC THENL [
    SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Q.EXISTS_TAC ‘h1'’ THEN
      Q.EXISTS_TAC ‘h2'’ THEN
      Q.EXISTS_TAC ‘h2’ THEN
      FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY,
                            FUNION_DEF, IN_UNION, GSYM fmap_EQ_THM] THEN
      METIS_TAC[],

      Q.EXISTS_TAC ‘h2'’ THEN
      Q.EXISTS_TAC ‘h1’ THEN
      Q.EXISTS_TAC ‘h1'’ THEN
      FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY,
                            FUNION_DEF, IN_UNION, GSYM fmap_EQ_THM] THEN
      METIS_TAC[]
    ]
  ]
QED


Theorem LIST_DS_SEM_EVAL3[local]:
  !s h fL sfL pfL es e.
    LIST_DS_SEM s h (pfL, (sf_tree fL es e)::sfL) =
    if (DS_EXPRESSION_EQUAL s e es) then
      LIST_DS_SEM s h (pfL, sfL)
    else
      let cL = MAP (\f. h ' (DS_EXPRESSION_EVAL_VALUE s e) ' f) fL
      in
        LIST_DS_SEM s h
                    (pfL,
                     sf_points_to e
                       (MAP (λ(f,c). (f,dse_const c)) (ZIP (fL,cL)))::
                       APPEND (MAP (\c. sf_tree fL es (dse_const c)) cL) sfL)
Proof
  SIMP_TAC std_ss [Once LIST_DS_SEM_THM] THEN
  SIMP_TAC std_ss [SF_SEM___sf_tree_THM] THEN
  REPEAT GEN_TAC THEN
  Cases_on ‘DS_EXPRESSION_EQUAL s e es’ THEN ASM_REWRITE_TAC[] THEN1 (
  SIMP_TAC std_ss [FUNION_FEMPTY_1, FDOM_FEMPTY, DISJOINT_EMPTY]
  ) THEN
  SIMP_TAC std_ss [GSYM APPEND] THEN
  ONCE_REWRITE_TAC [LIST_DS_SEM_THM] THEN
  SIMP_TAC std_ss [LET_THM] THEN
  HO_MATCH_MP_TAC
  (prove (“(!h1 h2. P h1 h2 = Q h1 h2) ==>
           ((?h1 h2. P h1 h2) = (?h1 h2. Q h1 h2))”,
          METIS_TAC[])) THEN
  REPEAT GEN_TAC THEN
  Cases_on ‘(h = FUNION h1 h2) /\ DISJOINT (FDOM h1) (FDOM h2) /\
            LIST_DS_SEM s h2 (pfL,sfL)’ THEN FULL_SIMP_TAC std_ss [] THEN
  FULL_SIMP_TAC list_ss [LIST_DS_SEM_def, LIST_SF_SEM_def] THEN

  Cases_on ‘h = FUNION h1 h2’ THEN FULL_SIMP_TAC bool_ss [] THEN
  SIMP_TAC list_ss [SF_SEM___sf_points_to_THM, DS_POINTS_TO_def] THEN
  Cases_on ‘~IS_DSV_NIL (DS_EXPRESSION_EVAL s e) /\
            GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) IN FDOM h1’ THEN (
  FULL_SIMP_TAC std_ss []
  ) THEN
  ASM_SIMP_TAC std_ss [FUNION_DEF, DS_EXPRESSION_EVAL_VALUE_def, FOLDR_MAP]
QED



val LIST_DS_SEM_EVAL3a = prove (“
(!s h fL sfL pfL es e.
   DS_EXPRESSION_EQUAL s e es ==>
      (LIST_DS_SEM s h (pfL, (sf_tree fL es e)::sfL) =
       LIST_DS_SEM s h (pfL, sfL))) /\

(!s h fL sfL pfL es e.
   ~DS_EXPRESSION_EQUAL s e es ==>
      (LIST_DS_SEM s h (pfL, (sf_tree fL es e)::sfL) =

      let cL = MAP (\f. h ' (DS_EXPRESSION_EVAL_VALUE s e) ' f) fL in
      LIST_DS_SEM s h (pfL,
         (sf_points_to e (MAP (\(f,c). (f,dse_const c)) (ZIP (fL,cL))))::
         (APPEND (MAP (\c. sf_tree fL es (dse_const c)) cL) sfL))))”,

SIMP_TAC std_ss [LIST_DS_SEM_EVAL3]);






val LIST_DS_SEM_EVAL3b = prove (“
(!s h f sfL pfL e1 e2.
   DS_EXPRESSION_EQUAL s e1 e2 ==>
      (LIST_DS_SEM s h (pfL, (sf_ls f e1 e2)::sfL) =
       LIST_DS_SEM s h (pfL, sfL))) /\

(!s h f sfL pfL e.
      (LIST_DS_SEM s h (pfL, (sf_ls f e e)::sfL) =
       LIST_DS_SEM s h (pfL, sfL))) /\

(!s h f1 f2 sfL pfL e.
   DS_EXPRESSION_EQUAL s e dse_nil ==>
      (LIST_DS_SEM s h (pfL, (sf_bin_tree (f1,f2) e)::sfL) =
       LIST_DS_SEM s h (pfL, sfL))) /\

(!s h f1 f2 sfL pfL.
      (LIST_DS_SEM s h (pfL, (sf_bin_tree (f1,f2) dse_nil)::sfL) =
       LIST_DS_SEM s h (pfL, sfL))) /\


(!s h f sfL pfL e1 e2.
   ~DS_EXPRESSION_EQUAL s e1 e2 ==>
      (LIST_DS_SEM s h (pfL, (sf_ls f e1 e2)::sfL) =

      let c = h ' (DS_EXPRESSION_EVAL_VALUE s e1) ' f in
      LIST_DS_SEM s h (pfL,
         (sf_points_to e1 [f, dse_const c])::
         (sf_ls f (dse_const c) e2)::sfL))) /\

(!s h f1 f2 sfL pfL e1 e2.
   ~DS_EXPRESSION_EQUAL s e dse_nil ==>
      (LIST_DS_SEM s h (pfL, (sf_bin_tree (f1,f2) e)::sfL) =

      let c1 = h ' (DS_EXPRESSION_EVAL_VALUE s e) ' f1 in
      let c2 = h ' (DS_EXPRESSION_EVAL_VALUE s e) ' f2 in
      LIST_DS_SEM s h (pfL,
         (sf_points_to e [(f1, dse_const c1);(f2, dse_const c2)])::
         (sf_bin_tree (f1,f2) (dse_const c1))::
         (sf_bin_tree (f1,f2) (dse_const c2))::sfL)
      )
)
”,

SIMP_TAC list_ss [sf_ls_def, sf_bin_tree_def, LIST_DS_SEM_EVAL3a,
   DS_EXPRESSION_EQUAL_def, LET_THM]);



val LIST_DS_SEM_EVAL4 = prove (“
!s h sfL pfL e a. LIST_DS_SEM s h (sfL, (sf_points_to e a)::pfL) =
      DS_POINTS_TO s h e a /\
      LIST_DS_SEM s (h \\ (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e))) (sfL, pfL)”,


SIMP_TAC list_ss [LIST_DS_SEM_def, LIST_SF_SEM_def,
   SF_SEM___sf_points_to_THM] THEN
METIS_TAC[]);




val LIST_DS_SEM_EVAL = save_thm ("LIST_DS_SEM_EVAL",
   LIST_CONJ [LIST_DS_SEM_EVAL1,
              LIST_DS_SEM_EVAL2,
              LIST_DS_SEM_EVAL3a,
              LIST_DS_SEM_EVAL3b,
              LIST_DS_SEM_EVAL4]);





val LIST_DS_SEM_PERM = store_thm ("LIST_DS_SEM_PERM",
“!pfL1 pfL2 sfL1 sfL2. (PERM pfL1 pfL2 /\ PERM sfL1 sfL2) ==>
          !s h. (LIST_DS_SEM s h (pfL1, sfL1) = LIST_DS_SEM s h (pfL2, sfL2))”,

   SIMP_TAC std_ss [LIST_DS_SEM_def] THEN
   PROVE_TAC[LIST_PF_SEM_PERM, LIST_SF_SEM_PERM])



val DS_POINTER_DANGLES_def = Define ‘
   DS_POINTER_DANGLES s h e =
   !a. ~(DS_POINTS_TO s h e a)’

val SF_SEM___EXTEND_def = Define ‘
   SF_SEM___EXTEND s h sf1 sf2 =
      (!h'. (DISJOINT (FDOM h) (FDOM h') /\
            SF_SEM s h' sf1) ==>
           SF_SEM s (FUNION h h') sf2)’


val NOT_DS_POINTER_DANGLES = store_thm ("NOT_DS_POINTER_DANGLES",
   “!s h e. ~(DS_POINTER_DANGLES s h e) =
      (~IS_DSV_NIL (DS_EXPRESSION_EVAL s e) /\
      GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) IN FDOM h)”,

   SIMP_TAC std_ss [DS_POINTER_DANGLES_def, DS_POINTS_TO_def] THEN
   REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
   Q.EXISTS_TAC ‘[]’ THEN
   SIMP_TAC list_ss []);


val DS_POINTER_DANGLES = store_thm ("DS_POINTER_DANGLES",
   “!s h e. (DS_POINTER_DANGLES s h e) =
      (IS_DSV_NIL (DS_EXPRESSION_EVAL s e) \/
      ~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) IN FDOM h))”,

   METIS_TAC[NOT_DS_POINTER_DANGLES]);



val DS_VAR_SUBST_def = Define ‘
   (DS_VAR_SUBST v e (dse_const c) = dse_const c) /\
   (DS_VAR_SUBST v e (dse_var v') = if (v = v') then e else (dse_var v'))’

val DS_VAR_SUBST_NIL = store_thm ("DS_VAR_SUBST_NIL",
   “!v e. DS_VAR_SUBST v e dse_nil = dse_nil”,
   SIMP_TAC std_ss [dse_nil_def, DS_VAR_SUBST_def])


val DS_VAR_SUBST_SEM = store_thm ("DS_VAR_SUBST_SEM",
“!s d. DS_EXPRESSION_EVAL s (DS_VAR_SUBST v e d) =
    (DS_EXPRESSION_EVAL
         (\x. (if x = v then DS_EXPRESSION_EVAL s e else s x)) d)”,

  Cases_on ‘d’ THENL [
      SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, DS_VAR_SUBST_def],
      SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, DS_VAR_SUBST_def, COND_RATOR, COND_RAND]
   ])


val PF_SUBST_def = Define ‘
   (PF_SUBST v e pf_true = pf_true) /\
   (PF_SUBST v e (pf_equal e1 e2) = pf_equal (DS_VAR_SUBST v e e1) (DS_VAR_SUBST v e e2)) /\
   (PF_SUBST v e (pf_unequal e1 e2) = pf_unequal (DS_VAR_SUBST v e e1) (DS_VAR_SUBST v e e2)) /\
   (PF_SUBST v e (pf_and pf1 pf2) =
      pf_and (PF_SUBST v e pf1) (PF_SUBST v e pf2))’


val PF_SUBST_SEM = store_thm ("PF_SUBST_SEM",
   “!s pf v e.
            PF_SEM s (PF_SUBST v e pf) =
            PF_SEM (\x. if x = v then DS_EXPRESSION_EVAL s e else s x) pf”,

   Induct_on ‘pf’ THENL [
      SIMP_TAC std_ss [PF_SEM_def, PF_SUBST_def],

      SIMP_TAC std_ss [PF_SEM_def, PF_SUBST_def, DS_EXPRESSION_EQUAL_def,
         DS_VAR_SUBST_SEM],

      SIMP_TAC std_ss [PF_SEM_def, PF_SUBST_def, DS_EXPRESSION_EQUAL_def,
         DS_VAR_SUBST_SEM],

      ASM_SIMP_TAC std_ss [PF_SUBST_def, PF_SEM_def]
   ]);

val LIST_PF_SUBST_SEM = store_thm ("LIST_PF_SUBST_SEM",
   “!s pfL v e.
            LIST_PF_SEM s (MAP (PF_SUBST v e) pfL) =
            LIST_PF_SEM (\x. if x = v then DS_EXPRESSION_EVAL s e else s x) pfL”,

   SIMP_TAC std_ss [LIST_PF_SEM_def, FOLDR_MAP] THEN
   Induct_on ‘pfL’ THENL [
      SIMP_TAC list_ss [PF_SEM_def],
      ASM_SIMP_TAC list_ss [PF_SEM_def, PF_SUBST_SEM]
   ]);


val SF_SUBST_def = Define ‘
   (SF_SUBST v e sf_emp = sf_emp) /\
   (SF_SUBST v e (sf_points_to e1 a) = sf_points_to (DS_VAR_SUBST v e e1) (MAP (\x. (FST x, DS_VAR_SUBST v e (SND x))) a)) /\
   (SF_SUBST v e (sf_tree fL e1 e2) = sf_tree fL (DS_VAR_SUBST v e e1) (DS_VAR_SUBST v e e2)) /\
   (SF_SUBST v e (sf_star sf1 sf2) = sf_star (SF_SUBST v e sf1) (SF_SUBST v e sf2))’


val SF_SUBST_THM = store_thm ("SF_SUBST_THM",
 “(SF_SUBST v e sf_emp = sf_emp) /\
   (SF_SUBST v e (sf_points_to e1 a) = sf_points_to (DS_VAR_SUBST v e e1) (MAP (\x. (FST x, DS_VAR_SUBST v e (SND x))) a)) /\
   (SF_SUBST v e (sf_tree fL e1 e2) = sf_tree fL (DS_VAR_SUBST v e e1) (DS_VAR_SUBST v e e2)) /\
   (SF_SUBST v e (sf_bin_tree (f1,f2) e1) = sf_bin_tree (f1,f2) (DS_VAR_SUBST v e e1)) /\
   (SF_SUBST v e (sf_ls f e1 e2) = sf_ls f (DS_VAR_SUBST v e e1) (DS_VAR_SUBST v e e2))”,

SIMP_TAC std_ss [SF_SUBST_def, sf_bin_tree_def, dse_nil_def, DS_VAR_SUBST_def,
   sf_ls_def])



val SF_SUBST_SEM = store_thm ("SF_SUBST_SEM",
   “!s h sf v e.
            SF_SEM s h (SF_SUBST v e sf) =
            SF_SEM (\x. if x = v then DS_EXPRESSION_EVAL s e else s x) h sf”,

   Induct_on ‘sf’ THENL [
      SIMP_TAC std_ss [SF_SUBST_def, SF_SEM_def],

      SIMP_TAC std_ss [SF_SUBST_def, SF_SEM_def] THEN
      REPEAT GEN_TAC THEN
      BINOP_TAC THENL [
         Cases_on ‘d’ THENL [
            SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def,
               DS_EXPRESSION_EVAL_def, DS_VAR_SUBST_def],

            SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def,
               DS_EXPRESSION_EVAL_def, DS_VAR_SUBST_def] THEN
            Cases_on ‘v' = v’ THEN (
               ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def]
            )
         ],


         SIMP_TAC std_ss [DS_POINTS_TO_def] THEN
         BINOP_TAC THENL [
            Cases_on ‘d’ THENL [
               SIMP_TAC std_ss [DS_VAR_SUBST_def, DS_EXPRESSION_EVAL_def],

               SIMP_TAC std_ss [DS_VAR_SUBST_def, DS_EXPRESSION_EVAL_def] THEN
               Cases_on ‘v' = v’ THEN (
                  ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def]
               )
            ],

            BINOP_TAC THENL [
               Cases_on ‘d’ THENL [
                  SIMP_TAC std_ss [DS_VAR_SUBST_def, DS_EXPRESSION_EVAL_def],

                  SIMP_TAC std_ss [DS_VAR_SUBST_def, DS_EXPRESSION_EVAL_def] THEN
                  Cases_on ‘v' = v’ THEN (
                     ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def]
                  )
               ],

               Induct_on ‘l’ THENL [
                  SIMP_TAC list_ss [],

                  ASM_SIMP_TAC list_ss [] THEN
                  GEN_TAC THEN
                  Tactical.REVERSE BINOP_TAC THEN1 (
                     METIS_TAC[]
                  ) THEN

                  Cases_on ‘h'’ THEN
                  SIMP_TAC std_ss [] THEN
                  BINOP_TAC THENL [
                     Cases_on ‘d’ THENL [
                        SIMP_TAC std_ss [DS_VAR_SUBST_def, DS_EXPRESSION_EVAL_def],

                        SIMP_TAC std_ss [DS_VAR_SUBST_def, DS_EXPRESSION_EVAL_def] THEN
                        Cases_on ‘v' = v’ THEN (
                           ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def]
                        )
                     ],

                     Cases_on ‘d’ THENL [
                        SIMP_TAC std_ss [DS_VAR_SUBST_def, DS_EXPRESSION_EVAL_def] THEN
                        Cases_on ‘r’ THENL [
                           SIMP_TAC std_ss [DS_VAR_SUBST_def, DS_EXPRESSION_EVAL_def],

                           SIMP_TAC std_ss [DS_VAR_SUBST_def, DS_EXPRESSION_EVAL_def] THEN
                           Cases_on ‘v' = v’ THEN (
                              ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def]
                           )
                        ],


                        SIMP_TAC std_ss [DS_VAR_SUBST_def, DS_EXPRESSION_EVAL_def] THEN
                        Cases_on ‘r’ THENL [
                           SIMP_TAC std_ss [DS_VAR_SUBST_def, DS_EXPRESSION_EVAL_def] THEN
                           Cases_on ‘v' = v’ THEN (
                              ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def]
                           ),

                           SIMP_TAC std_ss [DS_VAR_SUBST_def, DS_EXPRESSION_EVAL_def] THEN
                           Cases_on ‘v' = v’ THEN Cases_on ‘v'' = v’ THEN (
                              ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def]
                           )
                        ]
                     ]
                  ]
               ]
            ]
         ]
      ],




      SIMP_TAC std_ss [SF_SUBST_def, SF_SEM_def, DS_VAR_SUBST_SEM,
         SF_SEM___sf_tree_def] THEN
      REPEAT GEN_TAC THEN
      HO_MATCH_MP_TAC (prove (“(!x. (P x = Q x)) ==> ((?x. P x) = (?y. Q y))”, METIS_TAC[])) THEN
      GEN_TAC THEN
      Q.SPEC_TAC (‘h’, ‘h’) THEN
      Q.SPEC_TAC (‘l’, ‘l’) THEN
      Q.SPEC_TAC (‘d0’, ‘d0’) THEN
      Induct_on ‘n’ THENL [
         SIMP_TAC std_ss [SF_SEM___sf_tree_len_def,
            GSYM PF_SUBST_def, PF_SUBST_SEM],

         SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, GSYM PF_SUBST_def, PF_SUBST_SEM] THEN
         REPEAT STRIP_TAC THEN
         HO_MATCH_MP_TAC (prove(“(!hL. c1 hL = c2 hL) ==>
               ((a \/ b /\ (?hL. c1 hL)) = (a \/ b /\ (?hL. c2 hL)))”, METIS_TAC[])) THEN
         GEN_TAC THEN

         ‘!l h d0. MAP (HEAP_READ_ENTRY s h (DS_VAR_SUBST v e d0)) l =
         (MAP (HEAP_READ_ENTRY
            (\x. (if x = v then DS_EXPRESSION_EVAL s e else s x)) h d0) l)’ by (
            Induct_on ‘l’ THENL [
               SIMP_TAC list_ss [],

               ASM_SIMP_TAC list_ss [] THEN
               GEN_TAC THEN
               SIMP_TAC std_ss [HEAP_READ_ENTRY_def] THEN
               Cases_on ‘d0’ THENL [
                  SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, DS_VAR_SUBST_def],

                  SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, DS_VAR_SUBST_def] THEN
                  Cases_on ‘v = v'’ THEN (
                     ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, DS_VAR_SUBST_def]
                  )
               ]
            ]
         ) THEN

         MATCH_MP_TAC (prove(“((a1 /\ b1 /\ f1 = a2 /\ b2 /\ f2) /\ (c1 = c2) /\
                                (d1 = d2) /\ (e1 = e2) /\ (g1 = g2)) ==>
               ((a1 /\ b1 /\ c1 /\ d1 /\ e1 /\ f1 /\ g1) =
                (a2 /\ b2 /\ c2 /\ d2 /\ e2 /\ f2 /\ g2))”, SIMP_TAC std_ss [] THEN METIS_TAC[])) THEN
         REPEAT CONJ_TAC THENL [
            Cases_on ‘d0’ THENL [
               SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, DS_VAR_SUBST_def],

               SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, DS_VAR_SUBST_def] THEN
               Cases_on ‘v = v'’ THEN (
                  ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, DS_VAR_SUBST_def]
               )
            ],


            ASM_SIMP_TAC std_ss [],
            SIMP_TAC list_ss [],
            REWRITE_TAC[],


            ASM_SIMP_TAC list_ss [] THEN
            Q.ABBREV_TAC ‘L = (ZIP
               (MAP
                  (HEAP_READ_ENTRY
                     (\x. (if x = v then DS_EXPRESSION_EVAL s e else s x)) h d0)
                  l,hL))’ THEN
            POP_ASSUM (fn thm => ALL_TAC) THEN
            Induct_on ‘L’ THENL [
               SIMP_TAC list_ss [],

               GEN_TAC THEN
               ASM_SIMP_TAC list_ss [] THEN
               Tactical.REVERSE BINOP_TAC THEN1 (
                  REWRITE_TAC[]
               ) THEN
               Cases_on ‘h’ THEN
               SIMP_TAC std_ss [] THEN
               METIS_TAC[DS_VAR_SUBST_def]
            ]
         ]
      ],


      ASM_SIMP_TAC std_ss [SF_SEM_def, SF_SUBST_def]
   ]);




val LIST_SF_SUBST_SEM = store_thm ("LIST_SF_SUBST_SEM",
   “!s h sfL v e.
            LIST_SF_SEM s h (MAP (SF_SUBST v e) sfL) =
            LIST_SF_SEM (\x. if x = v then DS_EXPRESSION_EVAL s e else s x) h sfL”,

   SIMP_TAC std_ss [LIST_SF_SEM_def, FOLDR_MAP] THEN
   Induct_on ‘sfL’ THENL [
      SIMP_TAC list_ss [SF_SEM_def],
      ASM_SIMP_TAC list_ss [SF_SEM_def, SF_SUBST_SEM]
   ])




val SF_IS_PRECISE_def = Define ‘
   SF_IS_PRECISE sf =
         (!s h h1 h2. (h1 SUBMAP h /\ h2 SUBMAP h /\
                       SF_SEM s h1 sf /\ SF_SEM s h2 sf) ==> (h1 = h2))’

val SF_IS_PRECISE___sf_emp = store_thm ("SF_IS_PRECISE___sf_emp",
   “SF_IS_PRECISE sf_emp”,
   SIMP_TAC std_ss [SF_IS_PRECISE_def, SF_SEM_def])

val SF_IS_PRECISE___sf_points_to = store_thm ("SF_IS_PRECISE___sf_points_to",
   “!e a. SF_IS_PRECISE (sf_points_to e a)”,
   SIMP_TAC std_ss [SF_IS_PRECISE_def, SF_SEM_def, DS_POINTS_TO_def,
      GSYM fmap_EQ_THM, IN_SING, DS_EXPRESSION_EVAL_VALUE_def, SUBMAP_DEF])



val SF_IS_PRECISE___sf_star = store_thm ("SF_IS_PRECISE___sf_star",
   “!sf1 sf2. (SF_IS_PRECISE sf1 /\ SF_IS_PRECISE sf2) ==>
                SF_IS_PRECISE (sf_star sf1 sf2)”,
   SIMP_TAC std_ss [SF_IS_PRECISE_def, SF_SEM_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC std_ss [] THEN
   ‘h1' SUBMAP h’ by METIS_TAC[SUBMAP___FUNION___ID, SUBMAP_TRANS, DISJOINT_SYM] THEN
   ‘h2' SUBMAP h’ by METIS_TAC[SUBMAP___FUNION___ID, SUBMAP_TRANS, DISJOINT_SYM] THEN
   ‘h1'' SUBMAP h’ by METIS_TAC[SUBMAP___FUNION___ID, SUBMAP_TRANS, DISJOINT_SYM] THEN
   ‘h2'' SUBMAP h’ by METIS_TAC[SUBMAP___FUNION___ID, SUBMAP_TRANS, DISJOINT_SYM] THEN
   METIS_TAC[]
);




val SF_IS_PRECISE___sf_tree = store_thm ("SF_IS_PRECISE___sf_tree",
   “!fL e1 e2. SF_IS_PRECISE (sf_tree fL e1 e2)”,

   SIMP_TAC std_ss [SF_IS_PRECISE_def, SF_SEM_def,
      SF_SEM___sf_tree_def] THEN
   REPEAT STRIP_TAC THEN
   ‘?m. SF_SEM___sf_tree_len s h1 fL m e1 e2 /\
        SF_SEM___sf_tree_len s h2 fL m e1 e2’ by (
      Q.EXISTS_TAC ‘MAX n n'’ THEN
      ‘(n <= MAX n n') /\ (n' <= MAX n n')’ by SIMP_TAC arith_ss [] THEN
      METIS_TAC[SF_SEM___sf_tree_len_THM]
   ) THEN
   NTAC 2 (POP_ASSUM MP_TAC) THEN
   REPEAT (Q.PAT_X_ASSUM ‘hx SUBMAP h’ MP_TAC) THEN
   REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
   Q.SPEC_TAC (‘e2’, ‘e2’) THEN
   Q.SPEC_TAC (‘h’, ‘h’) THEN
   Q.SPEC_TAC (‘h1’, ‘h1’) THEN
   Q.SPEC_TAC (‘h2’, ‘h2’) THEN
   Q.SPEC_TAC (‘fL’, ‘fL’) THEN
   Induct_on ‘m’ THENL [
      SIMP_TAC std_ss [SF_SEM___sf_tree_len_def],

      REPEAT GEN_TAC THEN
      NTAC 2 STRIP_TAC THEN
      ‘!fL'.
       WEAK_SF_SEM___sf_tree_len s h1 fL fL' (SUC m) e1 e2 ==>
       WEAK_SF_SEM___sf_tree_len s h2 fL fL' (SUC m) e1 e2 ==>
         (h1 = h2)’ suffices_by (STRIP_TAC THEN
         METIS_TAC[WEAK_SF_SEM___sf_tree_len_THM]
      ) THEN

      SIMP_TAC std_ss [WEAK_SF_SEM___sf_tree_len_def, PF_SEM_def,
         SF_SEM___sf_tree_len_def] THEN
      REPEAT STRIP_TAC THEN1 (
         ASM_REWRITE_TAC[]
      ) THEN

      ‘hL = hL'’ suffices_by (STRIP_TAC THEN
         Q.PAT_X_ASSUM ‘FOLDR FUNION FEMPTY X = Y’ MP_TAC THEN
         FULL_SIMP_TAC std_ss [SUBMAP_DEF] THEN
         ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_DOMSUB, EXTENSION, IN_DELETE,
            DOMSUB_FAPPLY_THM] THEN
         METIS_TAC[]
      ) THEN

      FULL_SIMP_TAC list_ss [] THEN
      ‘?L. MAP (HEAP_READ_ENTRY s h1 e2) fL = L’ by METIS_TAC[] THEN
      ‘MAP (HEAP_READ_ENTRY s h2 e2) fL = MAP (HEAP_READ_ENTRY s h1 e2) fL’ by (
         Q.PAT_X_ASSUM ‘h1 SUBMAP h’ MP_TAC THEN
         Q.PAT_X_ASSUM ‘h2 SUBMAP h’ MP_TAC THEN
         Q.PAT_X_ASSUM ‘X IN FDOM h1’ MP_TAC THEN
         Q.PAT_X_ASSUM ‘X IN FDOM h2’ MP_TAC THEN
         REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN

         REPEAT STRIP_TAC THEN
         Induct_on ‘fL’ THENL [
            SIMP_TAC list_ss [],

            ASM_SIMP_TAC list_ss [] THEN
            FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_def, SUBMAP_DEF]
         ]
      ) THEN
      FULL_SIMP_TAC std_ss [] THEN
      ‘LENGTH L = LENGTH fL’ by METIS_TAC[LENGTH_MAP] THEN
      REPEAT (Q.PAT_X_ASSUM ‘MAP (HEAP_READ_ENTRY s H e2) fL = X’ (fn thm => ALL_TAC)) THEN

      REPEAT (POP_ASSUM MP_TAC) THEN
      REWRITE_TAC [AND_IMP_INTRO, GSYM CONJ_ASSOC] THEN

      Q.SPEC_TAC (‘fL’, ‘fL’) THEN
      Q.SPEC_TAC (‘hL'’, ‘hL'’) THEN
      Q.SPEC_TAC (‘L’, ‘L’) THEN
      Q.SPEC_TAC (‘h1’, ‘h1’) THEN
      Q.SPEC_TAC (‘h2’, ‘h2’) THEN

      Induct_on ‘hL’ THENL [
         SIMP_TAC list_ss [ALL_DISJOINT_def] THEN
         Cases_on ‘fL’ THEN FULL_SIMP_TAC list_ss [] THEN
         Cases_on ‘hL'’ THEN FULL_SIMP_TAC list_ss [],


         REPEAT STRIP_TAC THEN
         Cases_on ‘fL’ THEN FULL_SIMP_TAC list_ss [] THEN
         Cases_on ‘hL'’ THEN FULL_SIMP_TAC list_ss [] THEN
         Cases_on ‘L’ THEN FULL_SIMP_TAC list_ss [] THEN
         STRIP_TAC THENL [
            Q.PAT_X_ASSUM ‘!fL h2 h1 h e2. X fL h2 h1 h e2 ==> (h1 = h2)’ MATCH_MP_TAC THEN
            Q.EXISTS_TAC ‘fL'’ THEN
            Q.EXISTS_TAC ‘h’ THEN
            Q.EXISTS_TAC ‘dse_const (THE h''')’ THEN
            ASM_SIMP_TAC std_ss [] THEN
            ‘(h' SUBMAP h1) /\ h'' SUBMAP h2’ suffices_by (STRIP_TAC THEN
               METIS_TAC[SUBMAP_TRANS]
            ) THEN
            REPEAT (Q.PAT_X_ASSUM ‘FUNION X Y = Z’ MP_TAC) THEN

            SIMP_TAC std_ss [GSYM fmap_EQ_THM, SUBMAP_DEF,
               FDOM_DOMSUB, FUNION_DEF, EXTENSION, IN_UNION, IN_DELETE,
               DOMSUB_FAPPLY_THM] THEN
            METIS_TAC[],


            Q.PAT_X_ASSUM ‘!h2' h1' L hL'' fL. X h2' h1' L hL'' fL ==> (hL = hL'')’ MATCH_MP_TAC THEN
            Q.EXISTS_TAC ‘DRESTRICT h2 (FDOM h2 DIFF FDOM h'')’ THEN
            Q.EXISTS_TAC ‘DRESTRICT h1 (FDOM h1 DIFF FDOM h')’ THEN
            Q.EXISTS_TAC ‘t''’ THEN
            Q.EXISTS_TAC ‘t’ THEN
            FULL_SIMP_TAC std_ss [ALL_DISJOINT_def] THEN
            ASM_REWRITE_TAC[] THEN
            REPEAT STRIP_TAC THENL [
               FULL_SIMP_TAC std_ss [SUBMAP_DEF, DRESTRICT_DEF, IN_INTER, IN_DIFF],
               FULL_SIMP_TAC std_ss [SUBMAP_DEF, DRESTRICT_DEF, IN_INTER, IN_DIFF],

               ASM_SIMP_TAC std_ss [DRESTRICT_DEF, IN_INTER, IN_DIFF] THEN
               CCONTR_TAC THEN
               ‘GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2) IN FDOM (FUNION h' (FOLDR FUNION FEMPTY hL))’ by
                  FULL_SIMP_TAC std_ss [FUNION_DEF, IN_UNION] THEN
               POP_ASSUM MP_TAC THEN
               ASM_SIMP_TAC std_ss [] THEN
               ASM_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE],


               ‘DISJOINT (FDOM (FOLDR FUNION FEMPTY hL)) (FDOM h')’ by (
                  Q.PAT_X_ASSUM ‘EVERY X (MAP FDOM hL)’ MP_TAC THEN
                  REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
                  Induct_on ‘hL’ THENL [
                     SIMP_TAC list_ss [FDOM_FEMPTY, DISJOINT_EMPTY],
                     ASM_SIMP_TAC list_ss [FDOM_FEMPTY, DISJOINT_EMPTY,
                        FDOM_FUNION, DISJOINT_UNION_BOTH, DISJOINT_SYM]
                  ]
               ) THEN
               POP_ASSUM MP_TAC THEN
               Q.PAT_X_ASSUM ‘FUNION h' X = Y’ MP_TAC THEN
               SIMP_TAC std_ss [GSYM fmap_EQ_THM, DRESTRICT_DEF, FDOM_DOMSUB,
                  FAPPLY_FUPDATE_THM, DOMSUB_FAPPLY_THM, EXTENSION, IN_DELETE,
                  FUNION_DEF, IN_UNION, IN_INTER, IN_DIFF, DISJOINT_DEF,
                  NOT_IN_EMPTY] THEN
               METIS_TAC[],


               ASM_SIMP_TAC std_ss [DRESTRICT_DEF, IN_INTER, IN_DIFF] THEN
               CCONTR_TAC THEN
               ‘GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2) IN FDOM (FUNION h'' (FOLDR FUNION FEMPTY t'))’ by
                  FULL_SIMP_TAC std_ss [FUNION_DEF, IN_UNION] THEN
               POP_ASSUM MP_TAC THEN
               ASM_SIMP_TAC std_ss [] THEN
               ASM_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE],


               ‘DISJOINT (FDOM (FOLDR FUNION FEMPTY t')) (FDOM h'')’ by (
                  Q.PAT_X_ASSUM ‘EVERY X (MAP FDOM t')’ MP_TAC THEN
                  REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
                  Induct_on ‘t'’ THENL [
                     SIMP_TAC list_ss [FDOM_FEMPTY, DISJOINT_EMPTY],
                     ASM_SIMP_TAC list_ss [FDOM_FEMPTY, DISJOINT_EMPTY,
                        FDOM_FUNION, DISJOINT_UNION_BOTH, DISJOINT_SYM]
                  ]
               ) THEN
               POP_ASSUM MP_TAC THEN
               Q.PAT_X_ASSUM ‘FUNION h'' X = Y’ MP_TAC THEN
               SIMP_TAC std_ss [GSYM fmap_EQ_THM, DRESTRICT_DEF, FDOM_DOMSUB,
                  FAPPLY_FUPDATE_THM, DOMSUB_FAPPLY_THM, EXTENSION, IN_DELETE,
                  FUNION_DEF, IN_UNION, IN_INTER, IN_DIFF, DISJOINT_DEF,
                  NOT_IN_EMPTY] THEN
               METIS_TAC[]
            ]
         ]
      ]
   ]);




val SF_IS_PRECISE_THM = store_thm ("SF_IS_PRECISE_THM",
   “!sf. SF_IS_PRECISE sf”,

   Induct_on ‘sf’ THENL [
      REWRITE_TAC [SF_IS_PRECISE___sf_emp],
      REWRITE_TAC [SF_IS_PRECISE___sf_points_to],
      REWRITE_TAC [SF_IS_PRECISE___sf_tree],
      ASM_SIMP_TAC std_ss [SF_IS_PRECISE___sf_star]
   ]);



val SF_IS_SIMPLE___MEM_DS_FLAT_SF = store_thm ("SF_IS_SIMPLE___MEM_DS_FLAT_SF",
   “(!sf e. MEM e (DS_FLAT_SF sf) ==> SF_IS_SIMPLE e) /\
     (!sf. SF_IS_SIMPLE sf ==> (DS_FLAT_SF sf = [sf]))”,

   CONJ_TAC THEN (
      Induct_on ‘sf’ THEN
      SIMP_TAC list_ss [DS_FLAT_SF_def, SF_IS_SIMPLE_def] THEN
      METIS_TAC[]
   ));



val PF_EXPRESSION_SET_def = Define ‘
   (PF_EXPRESSION_SET pf_true = {}) /\
   (PF_EXPRESSION_SET (pf_equal e1 e2) = {e1; e2}) /\
   (PF_EXPRESSION_SET (pf_unequal e1 e2) = {e1; e2}) /\
   (PF_EXPRESSION_SET (pf_and pf1 pf2) =
      PF_EXPRESSION_SET pf1 UNION PF_EXPRESSION_SET pf2)’

val PF_EXPRESSION_SET___FINITE = store_thm ("PF_EXPRESSION_SET___FINITE",
   “!pf. FINITE (PF_EXPRESSION_SET pf)”,

   Induct_on ‘pf’ THEN (
      ASM_SIMP_TAC std_ss [PF_EXPRESSION_SET_def, FINITE_EMPTY, FINITE_INSERT,
         FINITE_UNION]
   ))

val SF_EXPRESSION_SET_def = Define ‘
   (SF_EXPRESSION_SET sf_emp = {}) /\
   (SF_EXPRESSION_SET (sf_points_to e a) = e INSERT LIST_TO_SET (MAP SND a)) /\
   (SF_EXPRESSION_SET (sf_tree fL e1 e2) = {e1; e2}) /\
   (SF_EXPRESSION_SET (sf_star sf1 sf2) =
      SF_EXPRESSION_SET sf1 UNION SF_EXPRESSION_SET sf2)’

val SF_EXPRESSION_SET___FINITE = store_thm ("SF_EXPRESSION_SET___FINITE",
   “!sf. FINITE (SF_EXPRESSION_SET sf)”,

   Induct_on ‘sf’ THEN (
      ASM_SIMP_TAC std_ss [SF_EXPRESSION_SET_def, FINITE_EMPTY, FINITE_INSERT,
         FINITE_UNION, FINITE_LIST_TO_SET]
   ));




val SF_EXPRESSION_SET___MEM_DS_FLAT_SF = store_thm ("SF_EXPRESSION_SET___MEM_DS_FLAT_SF",
   “(!sf e. MEM e (DS_FLAT_SF sf) ==>
         SF_EXPRESSION_SET e SUBSET SF_EXPRESSION_SET sf)”,

   Induct_on ‘sf’ THEN
   SIMP_TAC list_ss [DS_FLAT_SF_def, SF_EXPRESSION_SET_def, SUBSET_EMPTY, SUBSET_REFL] THEN
   METIS_TAC[SUBSET_UNION, SUBSET_TRANS]
);






val SIMPLE_SUB_FORMULA_TO_FRONT = store_thm ("SIMPLE_SUB_FORMULA_TO_FRONT",
“!sf sf'. MEM sf' (DS_FLAT_SF sf) ==>
         ?sf''. (SF_EQUIV (sf_star sf' sf'') sf /\
                 (SF_EXPRESSION_SET sf = SF_EXPRESSION_SET sf' UNION SF_EXPRESSION_SET sf''))”,

Induct_on ‘sf’ THENL [
   SIMP_TAC list_ss [DS_FLAT_SF_def],

   SIMP_TAC list_ss [DS_FLAT_SF_def] THEN
   REPEAT GEN_TAC THEN
   Q.EXISTS_TAC ‘sf_emp’ THEN
   SIMP_TAC std_ss [SF_SEM___STAR_EMP, SF_EXPRESSION_SET_def, UNION_EMPTY],

   SIMP_TAC list_ss [DS_FLAT_SF_def] THEN
   REPEAT GEN_TAC THEN
   Q.EXISTS_TAC ‘sf_emp’ THEN
   SIMP_TAC std_ss [SF_SEM___STAR_EMP, SF_EXPRESSION_SET_def, UNION_EMPTY],


   FULL_SIMP_TAC list_ss [SF_EQUIV_def, DS_FLAT_SF_def] THEN
   REPEAT STRIP_TAC THENL [
      RES_TAC THEN
      Q.EXISTS_TAC ‘sf_star sf''' sf'’ THEN
      CONJ_TAC THENL [
         METIS_TAC [SF_STAR_CONG, SF_SEM___STAR_ASSOC, SF_EQUIV_def],

         ASM_SIMP_TAC std_ss [SF_EXPRESSION_SET_def, EXTENSION, IN_UNION] THEN
         METIS_TAC[]
      ],

      RES_TAC THEN
      Q.EXISTS_TAC ‘sf_star sf''' sf’ THEN
      CONJ_TAC THENL [
         METIS_TAC [SF_STAR_CONG, SF_SEM___STAR_ASSOC, SF_EQUIV_def, SF_SEM___STAR_COMM],

         ASM_SIMP_TAC std_ss [SF_EXPRESSION_SET_def, EXTENSION, IN_UNION] THEN
         METIS_TAC[]
      ]
   ]
]);





val DS_POINTS_TO___IN_DISTANCE_def = Define ‘
   (DS_POINTS_TO___IN_DISTANCE s h fL e1 e2 0 = (DS_EXPRESSION_EQUAL s e1 e2)) /\
   (DS_POINTS_TO___IN_DISTANCE s h fL e1 e2 (SUC n) =
      ?y f. (DS_POINTS_TO___IN_DISTANCE s h fL e1 y n) /\
            (MEM f fL) /\
            (DS_POINTS_TO s h y [(f, e2)]))’


val DS_POINTS_TO___IN_DISTANCE___RIGHT = save_thm (
   "DS_POINTS_TO___IN_DISTANCE___RIGHT",
   DS_POINTS_TO___IN_DISTANCE_def);

val DS_POINTS_TO___IN_DISTANCE___LEFT = store_thm (
   "DS_POINTS_TO___IN_DISTANCE___LEFT",
“ (!s h fL e1 e2.
   (DS_POINTS_TO___IN_DISTANCE s h fL e1 e2 0 = (DS_EXPRESSION_EQUAL s e1 e2))) /\

   (!s h fL e1 e2 n.
   (DS_POINTS_TO___IN_DISTANCE s h fL e1 e2 (SUC n) =
      ?y f. (DS_POINTS_TO___IN_DISTANCE s h fL y e2 n) /\
            (MEM f fL) /\
            (DS_POINTS_TO s h e1 [(f, y)])))”,

   CONJ_TAC THEN1 (
      SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def]
   ) THEN
   Induct_on ‘n’ THENL [
      REWRITE_TAC [DS_POINTS_TO___IN_DISTANCE_def, DS_POINTS_TO_def] THEN
      SIMP_TAC list_ss [] THEN
      REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
         Q.EXISTS_TAC ‘e2’ THEN
         Q.EXISTS_TAC ‘f’ THEN
         FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def],

         Q.EXISTS_TAC ‘e1’ THEN
         Q.EXISTS_TAC ‘f’ THEN
         FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def]
      ],


      ONCE_REWRITE_TAC [DS_POINTS_TO___IN_DISTANCE_def] THEN
      METIS_TAC[]
   ])





val DS_POINTS_TO___IN_DISTANCE___DS_EXPRESSION_EQUAL =  store_thm ("DS_POINTS_TO___IN_DISTANCE___DS_EXPRESSION_EQUAL",
   “!s h fL e e1 e2. DS_EXPRESSION_EQUAL s e e1 ==> (
      (DS_POINTS_TO___IN_DISTANCE s h fL e1 e2 = DS_POINTS_TO___IN_DISTANCE s h fL e e2) /\
      (DS_POINTS_TO___IN_DISTANCE s h fL e2 e1 = DS_POINTS_TO___IN_DISTANCE s h fL e2 e))”,

   SIMP_TAC std_ss [FUN_EQ_THM, GSYM FORALL_AND_THM, GSYM RIGHT_FORALL_IMP_THM] THEN
   Induct_on ‘x’ THENL [
      SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def, DS_EXPRESSION_EQUAL_def],

      SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def] THEN
      REPEAT STRIP_TAC THENL [
         METIS_TAC[],
         FULL_SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EQUAL_def]
      ]
   ])

val DS_POINTS_TO___IN_DISTANCE___SUBSET = store_thm ("DS_POINTS_TO___IN_DISTANCE___SUBSET",
   “!s h fL1 fL2 e e' n.
     (DS_POINTS_TO___IN_DISTANCE s h fL1 e e' n /\
      (!f. MEM f fL1 ==> MEM f fL2)) ==>
     (DS_POINTS_TO___IN_DISTANCE s h fL2 e e' n)”,

   Induct_on ‘n’ THENL [
      SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def],

      SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def] THEN
      METIS_TAC[]
   ])


val DS_POINTS_TO___IN_DISTANCE___SUM_IMPL1 = store_thm ("DS_POINTS_TO___IN_DISTANCE___SUM_IMPL1",

   “!s h fL e e1 e2 n1 n2.
     (DS_POINTS_TO___IN_DISTANCE s h fL e e1 n1 /\
      DS_POINTS_TO___IN_DISTANCE s h fL e1 e2 n2) ==>
     (DS_POINTS_TO___IN_DISTANCE s h fL e e2 (n1 + n2))”,

   Induct_on ‘n1’ THENL [
      SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def] THEN
      METIS_TAC[DS_POINTS_TO___IN_DISTANCE___DS_EXPRESSION_EQUAL],

      REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC [prove (“(SUC n1) + n2 = n1 + (SUC n2)”, DECIDE_TAC)] THEN
      Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
      REWRITE_TAC[DS_POINTS_TO___IN_DISTANCE___LEFT] THEN
      FULL_SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE___RIGHT] THEN
      METIS_TAC[]
   ]);


val DS_POINTS_TO___IN_DISTANCE___SUM_IMPL2 = store_thm ("DS_POINTS_TO___IN_DISTANCE___SUM_IMPL2",

   “!s h fL e e1 e2 n1 n2.
     (DS_POINTS_TO___IN_DISTANCE s h fL e1 e2 (n1 + n2)) ==>
     ?e. (DS_POINTS_TO___IN_DISTANCE s h fL e1 e n1 /\
          DS_POINTS_TO___IN_DISTANCE s h fL e e2 n2)”,

   Induct_on ‘n1’ THENL [
      SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def] THEN
      METIS_TAC[DS_POINTS_TO___IN_DISTANCE___DS_EXPRESSION_EQUAL, DS_EXPRESSION_EQUAL_def],

      REWRITE_TAC [prove (“(SUC n1) + n2 = n1 + (SUC n2)”, DECIDE_TAC)] THEN
      REPEAT STRIP_TAC THEN
      RES_TAC THEN
      REWRITE_TAC[DS_POINTS_TO___IN_DISTANCE___RIGHT] THEN
      FULL_SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE___LEFT] THEN
      METIS_TAC[]
   ]);


val DS_POINTS_TO___IN_DISTANCE___SUBMAP = store_thm ("DS_POINTS_TO___IN_DISTANCE___SUBMAP",
   “!s fL h h' n e1 e2. (DS_POINTS_TO___IN_DISTANCE s h fL e1 e2 n /\
                          h SUBMAP h') ==>
                         (DS_POINTS_TO___IN_DISTANCE s h' fL e1 e2 n)”,

   Induct_on ‘n’ THENL [
      SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def],

      SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def] THEN
      METIS_TAC[DS_POINTS_TO___SUBMAP]
   ])


val DS_POINTS_TO___RTC_def = Define ‘
   DS_POINTS_TO___RTC s h fL e1 e2 =
   (?n. (DS_POINTS_TO___IN_DISTANCE s h fL e1 e2 n))’


val DS_POINTS_TO___RTC___SUBMAP = store_thm ("DS_POINTS_TO___RTC___SUBMAP",
   “!h h' s fL e1 e2. (DS_POINTS_TO___RTC s h fL e1 e2 /\
                       h SUBMAP h') ==> DS_POINTS_TO___RTC s h' fL e1 e2”,

   SIMP_TAC std_ss [DS_POINTS_TO___RTC_def] THEN
   METIS_TAC[DS_POINTS_TO___IN_DISTANCE___SUBMAP])


val DS_POINTS_TO___RTC___SUBSET = store_thm ("DS_POINTS_TO___RTC___SUBSET",
   “!s h fL1 fL2 e e'.
     (DS_POINTS_TO___RTC s h fL1 e e' /\
      (!f. MEM f fL1 ==> MEM f fL2)) ==>
     (DS_POINTS_TO___RTC s h fL2 e e')”,

   SIMP_TAC std_ss [DS_POINTS_TO___RTC_def] THEN
   METIS_TAC[DS_POINTS_TO___IN_DISTANCE___SUBSET]);


val DS_POINTS_TO___RTC___is_reflexive = store_thm ("DS_POINTS_TO___RTC___is_reflexive",
   “!s h fL. reflexive (DS_POINTS_TO___RTC s h fL)”,

   SIMP_TAC std_ss [reflexive_def, DS_POINTS_TO___RTC_def] THEN
   REPEAT GEN_TAC THEN
   EXISTS_TAC “0:num” THEN
   SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def, DS_EXPRESSION_EQUAL_def]
);


val DS_POINTS_TO___RTC___is_transitive = store_thm ("DS_POINTS_TO___RTC___is_transitive",
   “!s h fL. transitive (DS_POINTS_TO___RTC s h fL)”,

   SIMP_TAC std_ss [transitive_def, DS_POINTS_TO___RTC_def] THEN
   METIS_TAC[DS_POINTS_TO___IN_DISTANCE___SUM_IMPL1]);








val SF_SEM___sf_tree___ROOT_DANGLES = store_thm ("SF_SEM___sf_tree___ROOT_DANGLES",
“!s h fL es e.
SF_SEM s h (sf_tree fL es e) /\ DS_POINTER_DANGLES s h e ==>
((h = FEMPTY) /\ (DS_EXPRESSION_EQUAL s e es))”,

SIMP_TAC std_ss [SF_SEM___sf_tree_def, SF_SEM_def] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Cases_on ‘n’ THENL [
   FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def],

   FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_POINTER_DANGLES] THEN
   FULL_SIMP_TAC std_ss []
])


val SF_SEM___sf_ls___ROOT_DANGLES = store_thm ("SF_SEM___sf_ls___ROOT_DANGLES",
“!s h f e1 e2.
SF_SEM s h (sf_ls f e1 e2) /\ DS_POINTER_DANGLES s h e1 ==>
((h = FEMPTY) /\ (DS_EXPRESSION_EQUAL s e1 e2))”,

METIS_TAC[sf_ls_def, SF_SEM___sf_tree___ROOT_DANGLES]);




val LEMMA_3_1_1 = store_thm ("LEMMA_3_1_1",
“!s h fL es e.
SF_SEM s h (sf_tree fL es e) ==> DS_POINTER_DANGLES s h es”,

SIMP_TAC list_ss [SF_SEM_def, SF_SEM___sf_tree_def,
   GSYM LEFT_FORALL_IMP_THM] THEN
Induct_on ‘n’ THENL [
   SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, DS_POINTER_DANGLES, FDOM_FEMPTY,
      NOT_IN_EMPTY],

   SIMP_TAC std_ss [SF_SEM___sf_tree_len_def] THEN
   REPEAT STRIP_TAC THENL [
      ASM_SIMP_TAC std_ss [DS_POINTER_DANGLES, FDOM_FEMPTY, NOT_IN_EMPTY],

      SIMP_TAC std_ss [DS_POINTER_DANGLES] THEN
      Cases_on ‘IS_DSV_NIL (DS_EXPRESSION_EVAL s es)’ THEN ASM_REWRITE_TAC[] THEN
      ‘!h'. MEM h' hL ==> ~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s es) IN FDOM h')’ suffices_by (STRIP_TAC THEN
         CCONTR_TAC THEN
         ‘GET_DSV_VALUE (DS_EXPRESSION_EVAL s es) IN FDOM (h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e))’ by (
            FULL_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE, GET_DSV_VALUE_11, DS_EXPRESSION_EQUAL_def,
               PF_SEM_def]
         ) THEN
         POP_ASSUM MP_TAC THEN
         Q.PAT_X_ASSUM ‘FOLDR FUNION FEMPTY hL = X’ (fn thm => REWRITE_TAC [GSYM thm]) THEN
         Q.PAT_X_ASSUM ‘!h'. MEM h' hL ==> P h'’ MP_TAC THEN
         REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN

         Induct_on ‘hL’ THENL [
            SIMP_TAC list_ss [FDOM_FEMPTY, NOT_IN_EMPTY],

            ASM_SIMP_TAC list_ss [FDOM_FEMPTY, NOT_IN_EMPTY, DISJ_IMP_THM, FORALL_AND_THM,
               FUNION_DEF, IN_UNION]
         ]
      ) THEN
      REPEAT STRIP_TAC THEN
      FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
      Q.PAT_X_ASSUM ‘!e'. MEM e' (ZIP L) ==> P e'’ MP_TAC THEN
      ASM_SIMP_TAC list_ss [MEM_ZIP, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN

      ‘?n'. (n' < LENGTH fL) /\ (EL n' hL = h')’ by METIS_TAC[LENGTH_MAP, MEM_EL] THEN
      Q.EXISTS_TAC ‘n'’ THEN
      ASM_SIMP_TAC std_ss [] THEN
      REPEAT STRIP_TAC THEN
      RES_TAC THEN
      FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES] THEN
      FULL_SIMP_TAC std_ss []
   ]
]);


val LEMMA_3_1_1___sf_ls = store_thm ("LEMMA_3_1_1___sf_ls",
“!s h f e1 e2.
SF_SEM s h (sf_ls f e1 e2) ==> DS_POINTER_DANGLES s h e2”,

SIMP_TAC std_ss [sf_ls_def] THEN
METIS_TAC[LEMMA_3_1_1]);




val LEMMA_3_1_2 = store_thm ("LEMMA_3_1_2",
“!s h f fL e1 e2 es e.
(SF_SEM s h (sf_tree fL es e) /\ ~(DS_EXPRESSION_EQUAL s es e2) /\
 MEM f fL /\ DS_POINTS_TO s h e1 [(f,e2)]) ==>
(~(DS_POINTER_DANGLES s h e2))”,


SIMP_TAC std_ss [DS_POINTER_DANGLES, SF_SEM_def, SF_SEM___sf_tree_def,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM] THEN

Induct_on ‘n’ THENL [
   SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, DS_POINTS_TO_def, FDOM_FEMPTY,
      NOT_IN_EMPTY],


   SIMP_TAC std_ss [SF_SEM___sf_tree_len_def] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN1 (
      Q.PAT_X_ASSUM ‘DS_POINTS_TO s h e1 X’ MP_TAC THEN
      ASM_REWRITE_TAC [DS_POINTS_TO_def, FDOM_FEMPTY, NOT_IN_EMPTY]
   ) THEN

   Cases_on ‘DS_EXPRESSION_EVAL s e2 = DS_EXPRESSION_EVAL s e’ THEN1 (
      ASM_SIMP_TAC std_ss []
   ) THEN

   Cases_on ‘DS_EXPRESSION_EVAL s e1 = DS_EXPRESSION_EVAL s e’ THEN1 (
      FULL_SIMP_TAC list_ss [DS_POINTS_TO_def, EVERY_MEM, MEM_MAP,
         GSYM LEFT_FORALL_IMP_THM] THEN
      ‘IS_SOME (HEAP_READ_ENTRY s h e f)’ by METIS_TAC[] THEN
      Cases_on ‘HEAP_READ_ENTRY s h e f’ THEN FULL_SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM] THEN
      Q.PAT_X_ASSUM ‘x = X’ (fn thm => ASSUME_TAC (GSYM thm)) THEN
      Q.PAT_X_ASSUM ‘!e'. P e'’ MP_TAC THEN
      ASM_SIMP_TAC list_ss [MEM_ZIP, GSYM LEFT_FORALL_IMP_THM] THEN
      SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
      ‘?n'. (n' < LENGTH fL) /\ (EL n' fL = f)’ by METIS_TAC[MEM_EL] THEN
      Q.EXISTS_TAC ‘n'’ THEN
      ASM_SIMP_TAC std_ss [EL_MAP, HEAP_READ_ENTRY_def] THEN
      Cases_on ‘n’ THENL [
         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def,
            DS_EXPRESSION_EVAL_def],

         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def,
            DS_EXPRESSION_EVAL_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def] THEN
         STRIP_TAC THEN

         ASM_SIMP_TAC std_ss [] THEN
         ‘(GET_DSV_VALUE x) IN FDOM (FOLDR FUNION FEMPTY hL)’ by (
            Q.PAT_X_ASSUM ‘GET_DSV_VALUE x IN FDOM (EL n' hL)’ MP_TAC THEN
            ‘n' < LENGTH hL’ by METIS_TAC[] THEN
            POP_ASSUM MP_TAC THEN
            REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
            Q.SPEC_TAC (‘n'’, ‘n’) THEN
            Induct_on ‘hL’ THENL [
               SIMP_TAC list_ss [],

               SIMP_TAC list_ss [] THEN
               Cases_on ‘n’ THENL [
                  SIMP_TAC list_ss [FUNION_DEF, IN_UNION],
                  ASM_SIMP_TAC list_ss [FUNION_DEF, IN_UNION] THEN
                  METIS_TAC[]
               ]
            ]
         ) THEN
         POP_ASSUM MP_TAC THEN
         ASM_REWRITE_TAC[] THEN
         SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE]
      ]
   ) THEN

   ‘?h'. MEM h' hL /\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1) IN FDOM h'’ by (
      ‘GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1) IN FDOM (h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e))’ by (
         FULL_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE, GET_DSV_VALUE_11, DS_POINTS_TO_def]
      ) THEN
      POP_ASSUM MP_TAC THEN
      Q.PAT_X_ASSUM ‘FOLDR FUNION FEMPTY hL = X’ (fn thm => ASSUME_TAC (GSYM thm)) THEN
      ASM_REWRITE_TAC[] THEN
      Q.ABBREV_TAC ‘x = GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1)’ THEN
      REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN

      Induct_on ‘hL’ THENL [
         SIMP_TAC list_ss [FDOM_FEMPTY, NOT_IN_EMPTY],

         SIMP_TAC list_ss [FUNION_DEF, IN_UNION] THEN
         METIS_TAC[]
      ]
   ) THEN

   ‘~IS_DSV_NIL (DS_EXPRESSION_EVAL s e2) /\
    GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2) IN FDOM h'’ suffices_by (STRIP_TAC THEN
      ASM_SIMP_TAC std_ss [] THEN

      ‘GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2) IN FDOM (FOLDR FUNION FEMPTY hL)’ by (
         POP_ASSUM MP_TAC THEN
         Q.PAT_X_ASSUM ‘MEM h' hL’ MP_TAC THEN
         REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN

         Induct_on ‘hL’ THENL [
            SIMP_TAC list_ss [],

            SIMP_TAC list_ss [FUNION_DEF, IN_UNION] THEN
            METIS_TAC[]
         ]
      ) THEN
      POP_ASSUM MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE]
   ) THEN

   Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
   Q.EXISTS_TAC ‘f’ THEN
   Q.EXISTS_TAC ‘fL’ THEN
   Q.EXISTS_TAC ‘e1’ THEN
   Q.EXISTS_TAC ‘es’ THEN
   ASM_SIMP_TAC std_ss [LEFT_EXISTS_AND_THM] THEN
   STRIP_TAC THENL [
      Q.PAT_X_ASSUM ‘EVERY X Y’ MP_TAC THEN
      ASM_SIMP_TAC list_ss [EVERY_MEM, MEM_ZIP, GSYM LEFT_FORALL_IMP_THM] THEN
      SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
      ‘?n'. (n' < LENGTH fL) /\ (EL n' hL = h')’ by METIS_TAC[MEM_EL, LENGTH_MAP] THEN
      Q.EXISTS_TAC ‘n'’ THEN
      ASM_SIMP_TAC std_ss [] THEN
      METIS_TAC[],


      FULL_SIMP_TAC list_ss [DS_POINTS_TO_def] THEN
      ‘h' ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1)) =
                         h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1))’ suffices_by (STRIP_TAC THEN
         ASM_REWRITE_TAC[]
      ) THEN
      Q.PAT_X_ASSUM ‘FOLDR FUNION FEMPTY hL = X’ (fn thm => ASSUME_TAC (GSYM thm)) THEN

      ‘h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1)) =
       (h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)) ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1))’ by (
         ASM_SIMP_TAC std_ss [DOMSUB_FAPPLY_THM, GET_DSV_VALUE_11]
      ) THEN
      ASM_REWRITE_TAC[] THEN
      Q.ABBREV_TAC ‘x = (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1))’ THEN
      Q.PAT_X_ASSUM ‘ALL_DISJOINT (MAP FDOM hL)’ MP_TAC THEN
      Q.PAT_X_ASSUM ‘x IN FDOM h'’ MP_TAC THEN
      Q.PAT_X_ASSUM ‘MEM h' hL’ MP_TAC THEN
      REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN

      Induct_on ‘hL’ THENL [
         SIMP_TAC list_ss [],

         SIMP_TAC list_ss [ALL_DISJOINT_def, FUNION_DEF] THEN
         REPEAT STRIP_TAC THENL [
            FULL_SIMP_TAC std_ss [] THEN
            METIS_TAC[],

            FULL_SIMP_TAC std_ss [COND_RATOR, COND_RAND] THEN
            FULL_SIMP_TAC std_ss [EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
            ‘DISJOINT (FDOM h) (FDOM h')’ by METIS_TAC[] THEN
            FULL_SIMP_TAC std_ss [DISJOINT_DEF, NOT_IN_EMPTY, IN_INTER, EXTENSION] THEN
            METIS_TAC[]
         ]
      ]
   ]
]);


val LEMMA_3_1_2___list = store_thm ("LEMMA_3_1_2___list",
“!s h f e1 e2 e3 e4.
(SF_SEM s h (sf_ls f e1 e2) /\ ~(DS_EXPRESSION_EQUAL s e2 e4) /\
 DS_POINTS_TO s h e3 [f, e4]) ==>
(~(DS_POINTER_DANGLES s h e4))”,

SIMP_TAC std_ss [sf_ls_def] THEN
METIS_TAC[LEMMA_3_1_2, DS_EXPRESSION_EQUAL_def, MEM])



val LEMMA_3_1_2_a = store_thm ("LEMMA_3_1_2_a",
“!s h f fL v es e f.
(SF_SEM s h (sf_tree fL es e) /\
(v IN FDOM h) /\ MEM f fL) ==>
f IN FDOM (h ' v)”,

SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def,
   GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
Induct_on ‘n’ THENL [
   SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, FDOM_FEMPTY, NOT_IN_EMPTY],

   SIMP_TAC std_ss [SF_SEM___sf_tree_len___EXTENDED_DEF] THEN
   REPEAT STRIP_TAC THEN1 (
      METIS_TAC[FDOM_FEMPTY, NOT_IN_EMPTY]
   ) THEN
   Cases_on ‘DS_EXPRESSION_EVAL s e = (dsv_const v)’ THENL [
      RES_TAC THEN
      FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM] THEN
      Q.PAT_X_ASSUM ‘f IN FDOM X’ MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GET_DSV_VALUE_def],

      ‘?h'. MEM h' hL /\ v IN FDOM h'’ by METIS_TAC[] THEN
      ‘f IN FDOM (h' ' v)’ by METIS_TAC[MEM_EL] THEN
      METIS_TAC[SUBMAP_DEF]
   ]
]);


val LEMMA_25 = store_thm ("LEMMA_25",
   “!s h1 h2 f e1 e2 e3.
         (DISJOINT (FDOM h1) (FDOM h2) /\
             SF_SEM s h1 (sf_ls f e1 e2) /\
             (DS_POINTER_DANGLES s h1 e3) /\
             SF_SEM s h2 (sf_ls f e2 e3)) ==>
         SF_SEM s (FUNION h1 h2) (sf_ls f e1 e3)”,

SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_len_def, sf_ls_def,
   SF_SEM___sf_tree_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM] THEN
Induct_on ‘n’ THENL [
   SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def,
      FUNION_FEMPTY_1] THEN
   METIS_TAC[SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM, DS_EXPRESSION_EQUAL_def],


   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC list_ss [SF_SEM___sf_tree_len_def] THEN1 (
      FULL_SIMP_TAC std_ss [PF_SEM_def, FUNION_FEMPTY_1] THEN
      METIS_TAC[SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM, DS_EXPRESSION_EQUAL_def]
   ) THEN


   ‘?h1'. hL = [h1']’ by (
      Cases_on ‘hL’ THEN FULL_SIMP_TAC list_ss [LENGTH_NIL]
   ) THEN
   FULL_SIMP_TAC list_ss [FUNION_FEMPTY_2, ALL_DISJOINT_def] THEN
   Q.PAT_X_ASSUM ‘IS_SOME (HEAP_READ_ENTRY s h1 e1 f)’ ASSUME_TAC THEN
   FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM, HEAP_READ_ENTRY_def, PF_SEM_def] THEN

   ‘?c. DS_EXPRESSION_EVAL s e1 = dsv_const c’ by (
      FULL_SIMP_TAC std_ss [NOT_IS_DSV_NIL_THM, ds_value_11]
   ) THEN
   FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, ds_value_11] THEN

   ‘?n. SF_SEM___sf_tree_len s (FUNION h1' h2) [f] n e3 (dse_const (h1 ' c ' f))’ by (
      Q.PAT_X_ASSUM ‘! s h1 h2. P s h1 h2’ MATCH_MP_TAC THEN
      Q.EXISTS_TAC ‘e2’ THEN
      Q.EXISTS_TAC ‘n'’ THEN

      ASM_SIMP_TAC std_ss [] THEN
      CONJ_TAC THENL [
         FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
            FDOM_DOMSUB, IN_DELETE] THEN
         METIS_TAC[],

         FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, FDOM_DOMSUB, IN_DELETE]
      ]
   ) THEN

   Q.EXISTS_TAC ‘SUC n''’ THEN
   ASM_SIMP_TAC list_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, GET_DSV_VALUE_def, FDOM_FUNION,
      IN_UNION] THEN
   ‘~(DS_EXPRESSION_EQUAL s e1 e3)’ by (
      FULL_SIMP_TAC std_ss  [DS_EXPRESSION_EQUAL_def, DS_POINTER_DANGLES, IS_DSV_NIL_THM] THEN
      METIS_TAC[GET_DSV_VALUE_def]
   ) THEN
   ASM_SIMP_TAC std_ss [] THEN
   Q.EXISTS_TAC ‘[FUNION h1' h2]’ THEN
   ASM_SIMP_TAC list_ss [ALL_DISJOINT_def, HEAP_READ_ENTRY_THM,
      GET_DSV_VALUE_def, FUNION_DEF, IN_UNION, FUNION_FEMPTY_2, HEAP_READ_ENTRY_def,
      DOMSUB_FUNION] THEN

   ‘h2 \\ c = h2’ by (
      ‘~(c IN FDOM h2)’ by (
         FULL_SIMP_TAC std_ss [EXTENSION, DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY] THEN
         METIS_TAC[]
      ) THEN
      SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FDOM_DOMSUB,
         IN_DELETE, DOMSUB_FAPPLY_NEQ] THEN
      METIS_TAC[]
   ) THEN
   METIS_TAC[]
]);



val LEMMA_26 = store_thm ("LEMMA_26",
   “!s h fL es e. (~(DS_EXPRESSION_EQUAL s e es) /\
                 (SF_SEM s h (sf_tree fL es e))) ==>
                 (!f. MEM f fL ==> ?e'. DS_POINTS_TO s h e' [(f, es)])”,


   SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_FORALL_IMP_THM] THEN
   Induct_on ‘n’ THEN1 (
      SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
      METIS_TAC[]
   ) THEN

   SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
   REPEAT STRIP_TAC THEN
   ‘?h'. MEM (HEAP_READ_ENTRY s h e f, h') (ZIP (MAP (HEAP_READ_ENTRY s h e) fL,hL))’ by (
         FULL_SIMP_TAC list_ss [MEM_ZIP, MEM_EL] THEN
         Q.EXISTS_TAC ‘n'’ THEN
         ASM_SIMP_TAC std_ss [EL_MAP]
   ) THEN
   FULL_SIMP_TAC std_ss [EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
   RES_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN
   Cases_on ‘~DS_EXPRESSION_EQUAL s (dse_const (THE (HEAP_READ_ENTRY s h e f))) es’ THENL [
      ‘?e'. DS_POINTS_TO s h' e' [(f,es)]’ by METIS_TAC[] THEN
      Q.EXISTS_TAC ‘e'’ THEN

      ‘h' SUBMAP h’ by (
         ‘MEM h' hL’ by (
            Q.PAT_X_ASSUM ‘MEM X (ZIP Y)’ MP_TAC THEN
            ASM_SIMP_TAC list_ss [MEM_ZIP] THEN
            METIS_TAC[MEM_EL, LENGTH_MAP]
         ) THEN
         POP_ASSUM MP_TAC THEN
         Q.PAT_X_ASSUM ‘X = h \\ Y’ MP_TAC THEN
         Q.PAT_X_ASSUM ‘ALL_DISJOINT X’ MP_TAC THEN

         REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
         REPEAT STRIP_TAC THEN
         ‘h' SUBMAP h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)’ suffices_by (STRIP_TAC THEN
            FULL_SIMP_TAC std_ss [SUBMAP_DEF, FDOM_DOMSUB, DOMSUB_FAPPLY_THM, IN_DELETE]
         ) THEN
         Q.PAT_X_ASSUM ‘X = h \\ Y’ (fn thm => ASM_REWRITE_TAC [GSYM thm]) THEN

         Induct_on ‘hL’ THENL [
            SIMP_TAC list_ss [],

            FULL_SIMP_TAC list_ss [SUBMAP_DEF, FUNION_DEF, IN_UNION,
               DISJ_IMP_THM, ALL_DISJOINT_def, EVERY_MEM, MEM_MAP,
               GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
            FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
            METIS_TAC[]
         ]
      ) THEN

      FULL_SIMP_TAC list_ss [DS_POINTS_TO_def, SUBMAP_DEF] THEN
      METIS_TAC[],



      Q.EXISTS_TAC ‘e’ THEN
      POP_ASSUM MP_TAC THEN
      FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM] THEN
      ASM_SIMP_TAC list_ss [DS_EXPRESSION_EQUAL_def, HEAP_READ_ENTRY_def,
         DS_EXPRESSION_EVAL_def, DS_POINTS_TO_def]
   ]
);



val LEMMA_26a = store_thm ("LEMMA_26a",
   “!s h fL es e e'. (~(DS_EXPRESSION_EQUAL s e e') /\
                       ~(IS_DSV_NIL (DS_EXPRESSION_EVAL s e')) /\
                       (DS_EXPRESSION_EVAL_VALUE s e' IN FDOM h) /\
                       (SF_SEM s h (sf_tree fL es e))) ==>
                 (?e'' f. MEM f fL /\ DS_POINTS_TO s h e'' [(f, e')])”,


   SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_FORALL_IMP_THM] THEN
   Induct_on ‘n’ THEN1 (
      SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, FDOM_FEMPTY, NOT_IN_EMPTY]
   ) THEN

   SIMP_TAC std_ss [SF_SEM___sf_tree_len___EXTENDED_DEF, PF_SEM_def] THEN
   REPEAT STRIP_TAC THEN1 (
      FULL_SIMP_TAC std_ss [FDOM_FEMPTY, NOT_IN_EMPTY]
   ) THEN


   ‘?h'. MEM h' hL /\ DS_EXPRESSION_EVAL_VALUE s e' IN FDOM h'’ by (
      ‘~(dsv_const (DS_EXPRESSION_EVAL_VALUE s e') = DS_EXPRESSION_EVAL s e)’ suffices_by (STRIP_TAC THEN
         METIS_TAC[]
      ) THEN
      Cases_on ‘DS_EXPRESSION_EVAL s e'’ THEN FULL_SIMP_TAC list_ss [IS_DSV_NIL_def, GET_DSV_VALUE_def,
         DS_EXPRESSION_EVAL_def, DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_VALUE_def]
   ) THEN

   ‘?n. (n < LENGTH hL) /\ (EL n hL = h')’ by METIS_TAC[MEM_EL] THEN
   ‘?f. (EL n' fL = f) /\ (MEM f fL)’ by METIS_TAC[MEM_EL] THEN
   ‘IS_SOME (HEAP_READ_ENTRY s h e f)’ by METIS_TAC[] THEN
   FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM] THEN
   Cases_on ‘DS_EXPRESSION_EVAL s e’ THEN FULL_SIMP_TAC std_ss [IS_DSV_NIL_def, GET_DSV_VALUE_def] THEN
   Cases_on ‘DS_EXPRESSION_EVAL s e' = (h ' v ' f)’ THEN1 (
      Q.EXISTS_TAC ‘e’ THEN
      Q.EXISTS_TAC ‘f’ THEN
      ASM_SIMP_TAC list_ss [DS_POINTS_TO_def, GET_DSV_VALUE_def, IS_DSV_NIL_def]
   ) THEN

   ‘?e'' f. MEM f fL /\ DS_POINTS_TO s h' e'' [(f,e')]’ suffices_by (STRIP_TAC THEN
      METIS_TAC[DS_POINTS_TO___SUBMAP]
   ) THEN
   Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
   Q.EXISTS_TAC ‘es’ THEN
   Q.EXISTS_TAC ‘dse_const (h ' v ' f)’ THEN
   ASM_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def] THEN
   METIS_TAC[]
);


val LEMMA_26b = store_thm ("LEMMA_26b",
   “!s h fL es e e' f. (~(DS_EXPRESSION_EQUAL s es e') /\
                       ~(IS_DSV_NIL (DS_EXPRESSION_EVAL s e')) /\
                       (DS_EXPRESSION_EVAL_VALUE s e' IN FDOM h) /\
                       (SF_SEM s h (sf_tree fL es e)) /\ MEM f fL) ==>
                 ?e''. DS_POINTS_TO s h e' [(f, e'')]”,


   SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_FORALL_IMP_THM, GSYM LEFT_EXISTS_AND_THM] THEN
   Induct_on ‘n’ THEN1 (
      SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, FDOM_FEMPTY, NOT_IN_EMPTY]
   ) THEN

   SIMP_TAC std_ss [SF_SEM___sf_tree_len___EXTENDED_DEF, PF_SEM_def] THEN
   REPEAT STRIP_TAC THEN1 (
      FULL_SIMP_TAC std_ss [FDOM_FEMPTY, NOT_IN_EMPTY]
   ) THEN


   Cases_on ‘DS_EXPRESSION_EVAL s e' = DS_EXPRESSION_EVAL s e’ THEN1 (
      ‘IS_SOME (HEAP_READ_ENTRY s h e f)’ by METIS_TAC[] THEN
      POP_ASSUM MP_TAC THEN
      SIMP_TAC list_ss [DS_POINTS_TO_def, HEAP_READ_ENTRY_THM] THEN
      ASM_SIMP_TAC std_ss [] THEN
      METIS_TAC[DS_EXPRESSION_EVAL_def]
   ) THEN
   ‘?h'. MEM h' hL /\ DS_EXPRESSION_EVAL_VALUE s e' IN FDOM h'’ by (
      ‘~(dsv_const (DS_EXPRESSION_EVAL_VALUE s e') = DS_EXPRESSION_EVAL s e)’ suffices_by (STRIP_TAC THEN
         METIS_TAC[]
      ) THEN
      FULL_SIMP_TAC list_ss [GET_DSV_VALUE_def,
         DS_EXPRESSION_EVAL_def, DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_VALUE_def,
         NOT_IS_DSV_NIL_THM] THEN
      METIS_TAC[]
   ) THEN

   ‘?n. (n < LENGTH hL) /\ (EL n hL = h')’ by METIS_TAC[MEM_EL] THEN
   ‘IS_SOME (HEAP_READ_ENTRY s h e f)’ by METIS_TAC[] THEN
   FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM, DS_EXPRESSION_EVAL_VALUE_def, NOT_IS_DSV_NIL_THM] THEN
   Q.PAT_X_ASSUM ‘DS_EXPRESSION_EVAL s e = Y’ ASSUME_TAC THEN
   FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def] THEN
   ‘?e''. DS_POINTS_TO s h' e' [(f,e'')]’ suffices_by (STRIP_TAC THEN
      METIS_TAC[DS_POINTS_TO___SUBMAP]
   ) THEN
   Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
   Q.EXISTS_TAC ‘fL’ THEN
   Q.EXISTS_TAC ‘es’ THEN
   ASM_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def,
      ds_value_11] THEN
   METIS_TAC[]
);



val LEMMA_26c = store_thm ("LEMMA_26c",
   “!s h fL es e e' e'' f.
      (~(DS_EXPRESSION_EQUAL s es e') /\
       MEM f fL /\
       DS_POINTS_TO s h e'' [(f, e')] /\
       SF_SEM s h (sf_tree fL es e)) ==>

   ~(IS_DSV_NIL (DS_EXPRESSION_EVAL s e')) /\
   (DS_EXPRESSION_EVAL_VALUE s e' IN FDOM h)”,

   SIMP_TAC list_ss [SF_SEM_def, SF_SEM___sf_tree_def, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_FORALL_IMP_THM, DS_POINTS_TO_def] THEN
   Induct_on ‘n’ THEN1 (
      SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, FDOM_FEMPTY, NOT_IN_EMPTY]
   ) THEN

   SIMP_TAC std_ss [SF_SEM___sf_tree_len___EXTENDED_DEF, PF_SEM_def] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN1 (
      FULL_SIMP_TAC std_ss [FDOM_FEMPTY, NOT_IN_EMPTY]
   ) THEN

   ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def] THEN
   Cases_on ‘DS_EXPRESSION_EVAL s e''’ THEN FULL_SIMP_TAC list_ss [IS_DSV_NIL_def] THEN
   FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, DS_EXPRESSION_EVAL_VALUE_def] THEN
   Cases_on ‘DS_EXPRESSION_EVAL s e = DS_EXPRESSION_EVAL s e''’ THEN1 (
      ‘?n h'. (n < LENGTH hL) /\ (EL n fL = f) /\ (EL n hL = h') /\ MEM h' hL’ by METIS_TAC[MEM_EL] THEN
      ‘SF_SEM___sf_tree_len s h' fL n es (dse_const (h ' v ' f))’ by METIS_TAC[GET_DSV_VALUE_def] THEN
      Cases_on ‘n’ THENL [
         FULL_SIMP_TAC list_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def,
            DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def],

         FULL_SIMP_TAC list_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def,
            DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def] THENL [

            METIS_TAC[],

            ‘h' SUBMAP h’ by METIS_TAC[] THEN
            FULL_SIMP_TAC std_ss [SUBMAP_DEF]
         ]
      ]
   ) THEN
   ‘?h'. MEM h' hL /\ v IN FDOM h'’ by METIS_TAC[] THEN
   ‘h' SUBMAP h’ by METIS_TAC[] THEN

   ‘~IS_DSV_NIL (h' ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e'')) ' f) /\ GET_DSV_VALUE (h' ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e'')) ' f) IN FDOM h'’ suffices_by (STRIP_TAC THEN
      ‘h ' v = h' ' v’ by FULL_SIMP_TAC std_ss [SUBMAP_DEF] THEN
      Q.PAT_X_ASSUM ‘X = dsv_const v’ ASSUME_TAC THEN
      FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def] THEN
      METIS_TAC [SUBMAP_DEF]
   ) THEN

   ‘?n f. (n < LENGTH hL) /\ (EL n fL = f) /\ (EL n hL = h') /\ MEM f fL’ by METIS_TAC[MEM_EL] THEN

   Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
   Q.EXISTS_TAC ‘fL’ THEN
   Q.EXISTS_TAC ‘es’ THEN
   Q.EXISTS_TAC ‘dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)) ' f')’ THEN
   Q.EXISTS_TAC ‘dse_const (h' ' v ' f)’ THEN

   FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, IS_DSV_NIL_def, DS_EXPRESSION_EVAL_def,
      DS_EXPRESSION_EQUAL_def] THEN
   REPEAT CONJ_TAC THENL [
      METIS_TAC[SUBMAP_DEF],
      METIS_TAC[SUBMAP_DEF],
      METIS_TAC[]
   ]
);




val LEMMA_26d = store_thm ("LEMMA_26d",
   “!s h fL es e e' m1 m2. (~(DS_EXPRESSION_EQUAL s es e') /\
                       ~(IS_DSV_NIL (DS_EXPRESSION_EVAL s e')) /\
                       (DS_EXPRESSION_EVAL_VALUE s e' IN FDOM h) /\
                       (SF_SEM s h (sf_tree fL es e)) /\
                        (m1 < LENGTH fL) /\ (m2 < LENGTH fL) /\
                        ~(m1 = m2)) ==>
                 ?e1 e2. DS_POINTS_TO s h e' [(EL m1 fL, e1); (EL m2 fL, e2)] /\
                            ((DS_EXPRESSION_EQUAL s e1 es /\
                            DS_EXPRESSION_EQUAL s e2 es) \/
                            ~(DS_EXPRESSION_EQUAL s e1 e2))”,


   SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_FORALL_IMP_THM, GSYM LEFT_EXISTS_AND_THM] THEN
   Induct_on ‘n’ THEN1 (
      SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, FDOM_FEMPTY, NOT_IN_EMPTY]
   ) THEN

   SIMP_TAC std_ss [SF_SEM___sf_tree_len___EXTENDED_DEF, PF_SEM_def] THEN
   REPEAT STRIP_TAC THEN1 (
      FULL_SIMP_TAC std_ss [FDOM_FEMPTY, NOT_IN_EMPTY]
   ) THEN


   Cases_on ‘DS_EXPRESSION_EVAL s e' = DS_EXPRESSION_EVAL s e’ THEN1 (
      ‘IS_SOME (HEAP_READ_ENTRY s h e (EL m1 fL))’ by METIS_TAC[MEM_EL] THEN
      ‘IS_SOME (HEAP_READ_ENTRY s h e (EL m2 fL))’ by METIS_TAC[MEM_EL] THEN
      NTAC 2 (POP_ASSUM MP_TAC) THEN
      ASM_SIMP_TAC list_ss [DS_POINTS_TO_def, HEAP_READ_ENTRY_THM] THEN
      REPEAT STRIP_TAC THEN
      Cases_on ‘DS_EXPRESSION_EVAL s e’ THEN FULL_SIMP_TAC std_ss [IS_DSV_NIL_def, GET_DSV_VALUE_def] THEN
      Q.EXISTS_TAC ‘dse_const (h ' v ' (EL m1 fL))’ THEN
      Q.EXISTS_TAC ‘dse_const (h ' v ' (EL m2 fL))’ THEN
      ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def] THEN
      MATCH_MP_TAC (prove (“(b ==> a) ==> (a \/ ~b)”, METIS_TAC[])) THEN
      SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def] THEN
      STRIP_TAC THEN
      CCONTR_TAC  THEN
      ‘SF_SEM___sf_tree_len s (EL m1 hL) fL n es (dse_const (h ' v ' (EL m1 fL))) /\
       SF_SEM___sf_tree_len s (EL m2 hL) fL n es (dse_const (h ' v ' (EL m2 fL)))’ by METIS_TAC[] THEN
      NTAC 2 (POP_ASSUM MP_TAC) THEN
      Cases_on ‘n’ THENL [
         SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def,
            DS_EXPRESSION_EVAL_def] THEN
         ASM_SIMP_TAC std_ss [],

         SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def,
            DS_EXPRESSION_EVAL_def, AND_IMP_INTRO] THEN
         ASM_SIMP_TAC list_ss [] THEN
         ‘~(GET_DSV_VALUE (h ' v ' (EL m2 fL)) IN FDOM (EL m1 hL)) \/
                            ~(GET_DSV_VALUE (h ' v ' (EL m2 fL)) IN FDOM (EL m2 hL))’ suffices_by (STRIP_TAC THEN
            METIS_TAC[]
         ) THEN
         FULL_SIMP_TAC list_ss [EL_ALL_DISJOINT_EQ, EL_MAP] THEN
         FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
         METIS_TAC[]
      ]
   ) THEN
   ‘?h'. MEM h' hL /\ DS_EXPRESSION_EVAL_VALUE s e' IN FDOM h'’ by (
      ‘~(dsv_const (DS_EXPRESSION_EVAL_VALUE s e') = DS_EXPRESSION_EVAL s e)’ suffices_by (STRIP_TAC THEN
         METIS_TAC[]
      ) THEN
      FULL_SIMP_TAC list_ss [GET_DSV_VALUE_def,
         DS_EXPRESSION_EVAL_def, DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_VALUE_def,
         NOT_IS_DSV_NIL_THM] THEN
      METIS_TAC[]
   ) THEN

   ‘?n. (n < LENGTH hL) /\ (EL n hL = h')’ by METIS_TAC[MEM_EL] THEN
   Tactical.REVERSE (sg ‘?e1 e2.
      DS_POINTS_TO s h' e' [(EL m1 fL,e1); (EL m2 fL,e2)] /\
      (DS_EXPRESSION_EQUAL s e1 es /\ DS_EXPRESSION_EQUAL s e2 es \/
       ~DS_EXPRESSION_EQUAL s e1 e2)’) THENL [
      METIS_TAC[DS_POINTS_TO___SUBMAP],
      METIS_TAC[DS_POINTS_TO___SUBMAP],
      ALL_TAC
   ] THEN
   Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
   METIS_TAC[]
);



val SF_EXPRESSION_SET___FDOM_HEAP = store_thm ("SF_EXPRESSION_SET___FDOM_HEAP",
“ !s h sf x. (SF_SEM s h sf /\ (x IN FDOM h)) ==>
              ((?e. (e IN SF_EXPRESSION_SET sf) /\ (DS_EXPRESSION_EVAL s e = dsv_const x)) \/
               (?x' f. (x' IN FDOM h) /\ (f IN FDOM (h ' x')) /\
                       (h ' x' ' f = dsv_const x)))”,

Induct_on ‘sf’ THENL [
   SIMP_TAC std_ss [SF_SEM_def, FDOM_FEMPTY, NOT_IN_EMPTY],


   SIMP_TAC std_ss [SF_SEM_def, DS_POINTS_TO_def, DS_EXPRESSION_EVAL_VALUE_def, NOT_IS_DSV_NIL_THM,
      SF_EXPRESSION_SET_def, IN_INSERT, NOT_IN_EMPTY] THEN
   REPEAT STRIP_TAC THEN
   DISJ1_TAC THEN
   Q.EXISTS_TAC ‘d’ THEN
   Q.PAT_X_ASSUM ‘x IN FDOM h’ MP_TAC THEN
   ASM_SIMP_TAC std_ss [IN_SING, GET_DSV_VALUE_def],

   REPEAT STRIP_TAC THEN
   Cases_on ‘DS_EXPRESSION_EVAL s d0 = dsv_const x’ THEN1 (
      SIMP_TAC std_ss [SF_EXPRESSION_SET_def, IN_INSERT, NOT_IN_EMPTY] THEN
      METIS_TAC[]
   ) THEN
   DISJ2_TAC THEN
   MP_TAC (Q.SPECL [‘s’, ‘h’, ‘l’, ‘d’, ‘d0’, ‘dse_const (dsv_const x)’] LEMMA_26a) THEN
   ASM_SIMP_TAC list_ss [DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def,
      IS_DSV_NIL_def, DS_EXPRESSION_EVAL_VALUE_def, DS_POINTS_TO_def, NOT_IS_DSV_NIL_THM] THEN
   METIS_TAC[GET_DSV_VALUE_def],


   SIMP_TAC std_ss [SF_SEM_def, GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_EXISTS_AND_THM, FUNION_DEF, SF_EXPRESSION_SET_def, IN_UNION, DISJOINT_DEF,
      EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
   METIS_TAC[]
])



val LEMMA_27 = store_thm ("LEMMA_27",
“!s h f e1 e2 e3.
         (SF_SEM s h (sf_ls f e1 e3) /\
          ~(DS_POINTER_DANGLES s h e2)) ==>
         SF_SEM s h (sf_star (sf_ls f e1 e2) (sf_ls f e2 e3))”,

SIMP_TAC std_ss [SF_SEM_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, sf_ls_def, SF_SEM___sf_tree_def] THEN

Induct_on ‘n’ THENL [
   SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, DS_POINTER_DANGLES,
      FDOM_FEMPTY, NOT_IN_EMPTY],

   REPEAT GEN_TAC THEN
   Cases_on ‘DS_EXPRESSION_EQUAL s e1 e2’ THEN1 (
      REPEAT STRIP_TAC THEN
      Q.EXISTS_TAC ‘FEMPTY’ THEN
      Q.EXISTS_TAC ‘h’ THEN
      Q.EXISTS_TAC ‘0’ THEN
      Q.EXISTS_TAC ‘SUC n’ THEN
      ASM_SIMP_TAC std_ss [FUNION_FEMPTY_1, FDOM_FEMPTY, DISJOINT_EMPTY] THEN
      CONJ_TAC THENL [
         ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def],
         METIS_TAC[SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM, DS_EXPRESSION_EQUAL_def]
      ]
   ) THEN
   SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
   STRIP_TAC THEN1 (
      FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES] THEN
      METIS_TAC[FDOM_FEMPTY, NOT_IN_EMPTY]
   ) THEN
   ‘?h'. hL = [h']’ by (
      Cases_on ‘hL’ THEN FULL_SIMP_TAC list_ss [LENGTH_NIL]
   ) THEN
   FULL_SIMP_TAC list_ss [] THEN
   Q.PAT_X_ASSUM ‘IS_SOME Y’ ASSUME_TAC THEN
   ‘?c. DS_EXPRESSION_EVAL s e1 = dsv_const c’ by (
      FULL_SIMP_TAC std_ss [NOT_IS_DSV_NIL_THM, ds_value_11]
   ) THEN
   FULL_SIMP_TAC list_ss [GET_DSV_VALUE_def, FUNION_FEMPTY_2, IS_DSV_NIL_def, ALL_DISJOINT_def,
      HEAP_READ_ENTRY_THM, HEAP_READ_ENTRY_def] THEN
   ‘~(DS_POINTER_DANGLES s h' e2)’ by (
      FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, DS_EXPRESSION_EQUAL_def, FDOM_DOMSUB, IN_DELETE] THEN
      METIS_TAC[GET_DSV_VALUE_def, NOT_IS_DSV_NIL_THM]
   ) THEN
   Q.PAT_X_ASSUM ‘!s h f e1 e2 e3. P s h f e1 e2 e3’ (fn thm => MP_TAC (
      Q.SPECL [‘s’, ‘h'’, ‘f’, ‘dse_const ((h:('b, 'c) heap) ' c ' f)’, ‘e2’, ‘e3’] thm)) THEN
   ASM_SIMP_TAC std_ss [] THEN
   STRIP_TAC THEN
   Q.EXISTS_TAC ‘FUNION (DRESTRICT h {c}) h1’ THEN
   Q.EXISTS_TAC ‘h2’ THEN
   Q.EXISTS_TAC ‘SUC n'’ THEN
   Q.EXISTS_TAC ‘n''’ THEN
   ASM_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THENL [
      SIMP_TAC std_ss [GSYM FUNION___ASSOC] THEN
      Q.PAT_X_ASSUM ‘h \\ c = Y’ (fn thm => REWRITE_TAC [GSYM thm]) THEN
      SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, DRESTRICT_DEF,
         EXTENSION, IN_INTER, IN_SING, IN_UNION, IN_DELETE, FDOM_DOMSUB,
         DOMSUB_FAPPLY_THM] THEN
      METIS_TAC[],


      ASM_SIMP_TAC std_ss [FUNION_DEF, DISJOINT_UNION_BOTH] THEN
      ‘~(c IN FDOM h2)’ by (
         CCONTR_TAC THEN
         ‘c IN FDOM (h \\ c)’ by FULL_SIMP_TAC std_ss [FUNION_DEF, IN_UNION] THEN
         FULL_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE]
      ) THEN
      FULL_SIMP_TAC std_ss [DISJOINT_DEF, IN_INTER, EXTENSION, NOT_IN_EMPTY,
         DRESTRICT_DEF, IN_SING],


      ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, IS_DSV_NIL_def, GET_DSV_VALUE_def] THEN
      Q.EXISTS_TAC ‘[h1]’ THEN
      ASM_SIMP_TAC list_ss [DRESTRICT_DEF, FUNION_DEF, IN_UNION, IN_INTER, IN_SING, HEAP_READ_ENTRY_def,
         GET_DSV_VALUE_def, IS_DSV_NIL_def, ALL_DISJOINT_def, FUNION_FEMPTY_2] THEN
      ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_DOMSUB, EXTENSION, IN_DELETE,
         FUNION_DEF, DRESTRICT_DEF, IN_UNION, IN_INTER, IN_SING, DOMSUB_FAPPLY_THM] THEN
      ‘~(c IN FDOM h1)’ by (
         CCONTR_TAC THEN
         ‘c IN FDOM (h \\ c)’ by FULL_SIMP_TAC std_ss [FUNION_DEF, IN_UNION] THEN
         FULL_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE]
      ) THEN
      METIS_TAC[]
   ]
]);





val LEMMA_28_1 = store_thm ("LEMMA_28_1",
   “!s h fL es e. SF_SEM s h (sf_tree fL es e) ==>
                   !e f. MEM f fL ==> ~(DS_POINTS_TO s h e [(f, e)])”,

   SIMP_TAC std_ss [SF_SEM_def, GSYM LEFT_FORALL_IMP_THM,
      SF_SEM___sf_tree_def] THEN
   Induct_on ‘n’ THENL [
      FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, DS_POINTS_TO_def,
         FDOM_FEMPTY, NOT_IN_EMPTY],



      SIMP_TAC std_ss [SF_SEM___sf_tree_len_def] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN1 (
         FULL_SIMP_TAC std_ss [DS_POINTS_TO_def, FDOM_FEMPTY, NOT_IN_EMPTY]
      ) THEN

      REPEAT STRIP_TAC THEN
      Cases_on ‘DS_EXPRESSION_EVAL s e' = DS_EXPRESSION_EVAL s e’ THENL [
         ‘?h'. MEM (HEAP_READ_ENTRY s h e f, h') (ZIP (MAP (HEAP_READ_ENTRY s h e) fL,hL))’ by (
               FULL_SIMP_TAC list_ss [MEM_ZIP, MEM_EL] THEN
               Q.EXISTS_TAC ‘n'’ THEN
               ASM_SIMP_TAC std_ss [EL_MAP]
         ) THEN
         FULL_SIMP_TAC std_ss [EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
            HEAP_READ_ENTRY_THM] THEN
         RES_TAC THEN
         FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM] THEN

         ‘DS_EXPRESSION_EQUAL s e (dse_const (THE (HEAP_READ_ENTRY s h e f)))’ by (
            FULL_SIMP_TAC list_ss [DS_EXPRESSION_EQUAL_def, HEAP_READ_ENTRY_def,
               DS_EXPRESSION_EVAL_def, DS_POINTS_TO_def] THEN
            METIS_TAC[]
         ) THEN

         ‘SF_SEM___sf_tree_len s h' fL n es e’ by METIS_TAC[SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM,
            DS_EXPRESSION_EQUAL_def] THEN
         ‘SF_SEM___sf_tree_len s h' fL (SUC n) es e’ by
            METIS_TAC[prove(“n <= SUC n”, DECIDE_TAC), SF_SEM___sf_tree_len_THM] THEN
         ‘SF_SEM___sf_tree_len s h fL (SUC n) es e’ by (
            FULL_SIMP_TAC list_ss [SF_SEM___sf_tree_len_def, EVERY_MEM,
               MEM_MAP, GSYM LEFT_FORALL_IMP_THM, HEAP_READ_ENTRY_THM] THEN
            METIS_TAC[]
         ) THEN

         ‘(h' SUBMAP h) /\ ~(h' = h)’ by (
            ‘MEM h' hL’ by (
               Q.PAT_X_ASSUM ‘MEM X (ZIP Y)’ MP_TAC THEN
               ASM_SIMP_TAC list_ss [MEM_ZIP] THEN
               METIS_TAC[MEM_EL, LENGTH_MAP]
            ) THEN
            POP_ASSUM MP_TAC THEN
            Q.PAT_X_ASSUM ‘X = h \\ Z’ (fn thm=>MP_TAC (GSYM thm)) THEN
            Q.ABBREV_TAC ‘x = GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)’ THEN
            Q.PAT_X_ASSUM ‘ALL_DISJOINT X’ MP_TAC THEN
            Q.PAT_X_ASSUM ‘x IN FDOM h’ MP_TAC THEN
            REPEAT (POP_ASSUM (fn thm=> ALL_TAC)) THEN

            NTAC 4 STRIP_TAC THEN
            ‘h' SUBMAP h \\ x’ by (
               ASM_REWRITE_TAC[] THEN
               Q.PAT_X_ASSUM ‘h \\ x = Y’ (fn thm => ALL_TAC) THEN
               Q.PAT_X_ASSUM ‘x IN FDOM h’ (fn thm => ALL_TAC) THEN
               Induct_on ‘hL’ THEN (
                  FULL_SIMP_TAC list_ss [SUBMAP_DEF, FUNION_DEF, IN_UNION,
                     ALL_DISJOINT_def, EVERY_MEM,
                     GSYM LEFT_FORALL_IMP_THM, MEM_MAP,
                     DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
                  METIS_TAC[]
               )
            ) THEN
            FULL_SIMP_TAC std_ss [SUBMAP_DEF, FDOM_DOMSUB, IN_DELETE,
               DOMSUB_FAPPLY_THM, GSYM fmap_EQ_THM] THEN
            METIS_TAC[]
         ) THEN

         METIS_TAC[SF_IS_PRECISE_def, SUBMAP_REFL, SF_IS_PRECISE_THM, SF_SEM_def,
            SF_SEM___sf_tree_def],




         ‘?h'. MEM h' hL /\ DS_POINTS_TO s h' e' [(f, e')]’ by (
            ‘DS_POINTS_TO s (h \\ (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e))) e' [(f,e')]’ by (

               FULL_SIMP_TAC list_ss [DS_POINTS_TO_def, DOMSUB_FAPPLY_THM, GET_DSV_VALUE_11,
                  FDOM_DOMSUB, IN_DELETE] THEN
               METIS_TAC[]
            ) THEN
            POP_ASSUM MP_TAC THEN
            Q.PAT_X_ASSUM ‘X = h \\ Y’ (fn thm => REWRITE_TAC [GSYM thm]) THEN

            REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
            SIMP_TAC list_ss [DS_POINTS_TO_def] THEN
            Induct_on ‘hL’ THENL [
               SIMP_TAC list_ss [FDOM_FEMPTY, NOT_IN_EMPTY],

               FULL_SIMP_TAC list_ss [FUNION_DEF, IN_UNION] THEN
               GEN_TAC THEN
               Cases_on ‘GET_DSV_VALUE (DS_EXPRESSION_EVAL s e') IN FDOM h’ THENL [
                  ASM_REWRITE_TAC[] THEN METIS_TAC[],

                  ASM_REWRITE_TAC[] THEN
                  STRIP_TAC THEN
                  FULL_SIMP_TAC std_ss [] THEN
                  METIS_TAC[]
               ]
            ]
         ) THEN

         ‘?f'. MEM (HEAP_READ_ENTRY s h e f', h') (ZIP (MAP (HEAP_READ_ENTRY s h e) fL,hL))’ by (
            ASM_SIMP_TAC list_ss [MEM_ZIP] THEN
            FULL_SIMP_TAC std_ss [MEM_EL] THEN
            Q.EXISTS_TAC ‘EL n'' fL’ THEN
            Q.EXISTS_TAC ‘n''’ THEN
            FULL_SIMP_TAC list_ss [EL_MAP]
         ) THEN
         FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
         RES_TAC THEN
         FULL_SIMP_TAC std_ss [] THEN
         METIS_TAC[]
      ]
   ]);






val LEMMA_28_a = store_thm ("LEMMA_28_a",

“!e1 e2 e3 fL h' h'' h.
(h' SUBMAP h /\ h'' SUBMAP h /\ ~(fL = []) /\
~(DS_EXPRESSION_EQUAL s e2 e3) /\
SF_SEM s h' (sf_tree fL e2 e1) /\
SF_SEM s h'' (sf_tree fL e3 e1)) ==>
(~(DS_POINTER_DANGLES s h'' e2) \/
 ~(DS_POINTER_DANGLES s h' e3))”,



SIMP_TAC std_ss [SF_SEM_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, SF_SEM___sf_tree_def] THEN
Induct_on ‘n’ THENL [
   SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_POINTER_DANGLES,
      FDOM_FEMPTY, NOT_IN_EMPTY] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   ‘~(DS_EXPRESSION_EQUAL s e1 e3)’ by METIS_TAC[DS_EXPRESSION_EQUAL_def] THEN
   Cases_on ‘n'’ THENL [
      FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def],

      FULL_SIMP_TAC list_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def] THEN
      METIS_TAC[]
   ],



   REPEAT STRIP_TAC THEN
   ‘?f fL'. fL = f::fL'’ by (
      Cases_on ‘fL’ THEN FULL_SIMP_TAC list_ss []
   ) THEN
   Cases_on ‘n'’ THEN1 (
      FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THENL [
         METIS_TAC[DS_EXPRESSION_EQUAL_def],
         FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, DS_EXPRESSION_EQUAL_def]
      ]
   ) THEN
   FULL_SIMP_TAC list_ss [SF_SEM___sf_tree_len___EXTENDED_DEF, PF_SEM_def] THENL [
      METIS_TAC[DS_EXPRESSION_EQUAL_def],

      FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def, DS_POINTER_DANGLES] THEN
      METIS_TAC[],

      FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def, DS_POINTER_DANGLES] THEN
      METIS_TAC[],


      ‘0 < LENGTH hL’ by ASM_SIMP_TAC list_ss [] THEN
      ‘0 < LENGTH hL'’ by ASM_SIMP_TAC list_ss [] THEN
      Tactical.REVERSE (sg ‘~DS_POINTER_DANGLES s (EL 0 hL') e2 \/ ~DS_POINTER_DANGLES s (EL 0 hL) e3’) THENL [
         ‘EL 0 hL SUBMAP h'’ by METIS_TAC[MEM_EL] THEN
         FULL_SIMP_TAC std_ss [SUBMAP_DEF, DS_POINTER_DANGLES],

         ‘EL 0 hL' SUBMAP h''’ by METIS_TAC[MEM_EL] THEN
         FULL_SIMP_TAC std_ss [SUBMAP_DEF, DS_POINTER_DANGLES],

         ALL_TAC
      ] THEN

      ‘?c. DS_EXPRESSION_EVAL s e1 = dsv_const c’ by FULL_SIMP_TAC std_ss [NOT_IS_DSV_NIL_THM, ds_value_11] THEN
      FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, ds_value_11] THEN

      ‘h' ' c = h'' ' c’ by (
         FULL_SIMP_TAC list_ss [SUBMAP_DEF]
      ) THEN

      Q.PAT_X_ASSUM ‘!e1 e2 e3. P e1 e2 e3’ MATCH_MP_TAC THEN
      Q.EXISTS_TAC ‘dse_const ((h'':('a, 'c) heap) ' c ' f)’ THEN
      Q.EXISTS_TAC ‘fL’ THEN
      Q.EXISTS_TAC ‘h’ THEN
      Q.EXISTS_TAC ‘n''’ THEN
      ASM_SIMP_TAC std_ss [NOT_NIL_CONS] THEN
      METIS_TAC[EL,HD,MEM_EL,SUBMAP_TRANS]
   ]
])


val LEMMA_28_2 = store_thm ("LEMMA_28_2",
   “!s h h' f e1 e2 e3 e4. (SF_SEM s h (sf_ls f e1 e4) /\
                       ~(DS_EXPRESSION_EQUAL s e2 e3) /\ (h' SUBMAP h) /\
                       SF_SEM s h' (sf_ls f e2 e3)) ==>
      (!h''. h'' SUBMAP h ==> ~(SF_SEM s h'' (sf_ls f e3 e2)))”,

   SIMP_TAC std_ss [SF_SEM_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_IMP_THM,
      GSYM RIGHT_FORALL_OR_THM, IMP_DISJ_THM,
      GSYM LEFT_FORALL_OR_THM, sf_ls_def, SF_SEM___sf_tree_def] THEN

   REPEAT STRIP_TAC THEN
   CCONTR_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN
   ‘~(DS_POINTER_DANGLES s h' e2)’ by (
      Cases_on ‘n'’ THENL [
         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def],

         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
         FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES]
      ]
   ) THEN

   ‘~(DS_POINTER_DANGLES s h'' e3)’ by (
      Cases_on ‘n''’ THENL [
         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def],

         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def] THEN
         FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES]
      ]
   ) THEN

   ‘SF_SEM s h (sf_star (sf_ls f e1 e2) (sf_ls f e2 e4))’ by (
      MATCH_MP_TAC LEMMA_27 THEN
      FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, SF_SEM_def, SUBMAP_DEF,
         SF_SEM___sf_tree_def, SF_SEM_def, sf_ls_def] THEN
      METIS_TAC[]
   ) THEN

   ‘DS_POINTER_DANGLES s h e4’ by (
      MATCH_MP_TAC LEMMA_3_1_1 THEN
      SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def] THEN
      METIS_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [SF_SEM_def] THEN


   ‘~(DS_POINTER_DANGLES s h1 e3) \/ ~(DS_POINTER_DANGLES s h2 e3)’ by (
      FULL_SIMP_TAC std_ss [SUBMAP_DEF, DS_POINTER_DANGLES, FUNION_DEF, IN_UNION]
   ) THENL [
      ‘~(DS_POINTER_DANGLES s h2 e3) \/ ~(DS_POINTER_DANGLES s h' e4)’ by (
         MATCH_MP_TAC LEMMA_28_a THEN
         Q.EXISTS_TAC ‘e2’ THEN
         Q.EXISTS_TAC ‘[f]’ THEN
         Q.EXISTS_TAC ‘h’ THEN
         FULL_SIMP_TAC list_ss [SF_SEM_def, SUBMAP___FUNION___ID,
            sf_ls_def, SF_SEM___sf_tree_def] THEN
         REPEAT STRIP_TAC THENL [
            FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, DS_EXPRESSION_EQUAL_def] THEN
            METIS_TAC[SUBMAP_DEF],

            METIS_TAC[],
            METIS_TAC[]
         ]
      ) THENL [
         FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
         METIS_TAC[],

         FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES] THEN
         METIS_TAC[SUBMAP_DEF]
      ],



      ‘SF_SEM s h2 (sf_star (sf_ls f e2 e3) (sf_ls f e3 e4))’ by (
         MATCH_MP_TAC LEMMA_27 THEN
         ASM_REWRITE_TAC[]
      ) THEN
      FULL_SIMP_TAC std_ss [SF_SEM_def] THEN

      ‘~(DS_POINTER_DANGLES s h2' e2) \/ ~(DS_POINTER_DANGLES s h'' e4)’ by (
         MATCH_MP_TAC LEMMA_28_a THEN
         Q.EXISTS_TAC ‘e3’ THEN
         Q.EXISTS_TAC ‘[f]’ THEN
         Q.EXISTS_TAC ‘h’ THEN
         FULL_SIMP_TAC list_ss [SF_SEM_def, SUBMAP___FUNION___ID, SF_SEM___sf_tree_def, sf_ls_def] THEN
         REPEAT STRIP_TAC THENL [
            SIMP_TAC std_ss [SUBMAP_DEF, FUNION_DEF, IN_UNION] THEN
            FULL_SIMP_TAC std_ss [DISJOINT_DEF, IN_INTER, EXTENSION, NOT_IN_EMPTY,
               FUNION_DEF, IN_UNION] THEN
            METIS_TAC[],

            Q.PAT_X_ASSUM ‘DS_POINTER_DANGLES s h e4’ MP_TAC THEN
            FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, DS_EXPRESSION_EQUAL_def,
               FUNION_DEF, IN_UNION, SUBMAP_DEF],

            METIS_TAC[],
            METIS_TAC[]
         ]
      ) THENL [
         ‘~(DS_POINTER_DANGLES s h1' e2)’ by (
            Q.PAT_X_ASSUM ‘SF_SEM s h1' Y’ MP_TAC THEN
            ASM_SIMP_TAC std_ss [SF_SEM___sf_ls_THM, LET_THM] THEN
            SIMP_TAC list_ss [SF_SEM___sf_points_to_THM, DS_POINTS_TO_def,
            DS_POINTER_DANGLES]
         ) THEN

         FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
            DS_POINTER_DANGLES] THEN
         METIS_TAC[],

         Q.PAT_X_ASSUM ‘DS_POINTER_DANGLES s h e4’ MP_TAC THEN
         FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, DS_EXPRESSION_EQUAL_def,
            FUNION_DEF, IN_UNION, SUBMAP_DEF]
      ]
   ]);


val LEMMA_29 = store_thm ("LEMMA_29",

   “!s h h' f e1 e2 e3 e4.
         (SF_SEM s h (sf_ls f e1 e4) /\
         ~(DS_EXPRESSION_EQUAL s e2 e3) /\ (h' SUBMAP h) /\
         SF_SEM s h' (sf_ls f e2 e3)) ==>

         SF_SEM s h (sf_star (sf_ls f e1 e2) (sf_star (sf_ls f e2 e3) (sf_ls f e3 e4)))”,

   REPEAT STRIP_TAC THEN
   ‘SF_SEM s h (sf_star (sf_ls f e1 e2) (sf_ls f e2 e4))’ by (
      MATCH_MP_TAC LEMMA_27 THEN
      ASM_SIMP_TAC std_ss [DS_POINTER_DANGLES] THEN
      FULL_SIMP_TAC std_ss [SF_SEM_def, sf_ls_def, SF_SEM___sf_tree_def] THEN
      Cases_on ‘n'’ THENL [
         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def],

         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
         FULL_SIMP_TAC std_ss [SUBMAP_DEF]
      ]
   ) THEN
   FULL_SIMP_TAC std_ss [SF_SEM_def] THEN
   Q.EXISTS_TAC ‘h1’ THEN
   Q.EXISTS_TAC ‘h2’ THEN
   ASM_SIMP_TAC std_ss [] THEN
   Cases_on ‘DS_EXPRESSION_EQUAL s e3 e4’ THEN1 (
      Q.EXISTS_TAC ‘h2’ THEN
      Q.EXISTS_TAC ‘FEMPTY’ THEN
      ASM_SIMP_TAC std_ss [FUNION_FEMPTY_2, FDOM_FEMPTY, DISJOINT_EMPTY] THEN

      FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_def, SF_SEM_def, sf_ls_def] THEN
      CONJ_TAC THENL [
         METIS_TAC[SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM, DS_EXPRESSION_EQUAL_def],

         Q.EXISTS_TAC ‘0’ THEN
         ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def]
      ]
   ) THEN

   ‘~(DS_POINTER_DANGLES s h e3)’ by (
      ‘?e. DS_POINTS_TO s h' e [(f, e3)]’ by (
         MP_TAC (Q.SPECL [‘s’, ‘h'’, ‘[f]’, ‘e3’, ‘e2’] LEMMA_26) THEN
         FULL_SIMP_TAC list_ss [sf_ls_def]
      ) THEN

      MATCH_MP_TAC LEMMA_3_1_2 THEN
      Q.EXISTS_TAC ‘f’ THEN
      Q.EXISTS_TAC ‘[f]’ THEN
      Q.EXISTS_TAC ‘e’ THEN
      Q.EXISTS_TAC ‘e4’ THEN
      Q.EXISTS_TAC ‘e1’ THEN
      FULL_SIMP_TAC list_ss [DS_EXPRESSION_EQUAL_def, sf_ls_def] THEN
      METIS_TAC[DS_POINTS_TO___SUBMAP]
   ) THEN


   ‘~(DS_POINTER_DANGLES s h1 e3) \/ ~(DS_POINTER_DANGLES s h2 e3)’ by (
      Q.PAT_X_ASSUM ‘~(DS_POINTER_DANGLES s h e3)’ MP_TAC THEN
      ASM_SIMP_TAC std_ss [DS_POINTER_DANGLES, FUNION_DEF, IN_UNION]
   ) THENL [
      ‘SF_SEM s h1 (sf_star (sf_ls f e1 e3) (sf_ls f e3 e2))’ by (
         MATCH_MP_TAC LEMMA_27 THEN
         ASM_SIMP_TAC std_ss [SF_SEM_def] THEN
         METIS_TAC[]
      ) THEN
      MATCH_MP_TAC (prove (“F ==> X”, METIS_TAC[])) THEN
      FULL_SIMP_TAC std_ss [SF_SEM_def] THEN
      MP_TAC (Q.SPECL [‘s’, ‘h’, ‘h'’, ‘f’, ‘e1’, ‘e2’, ‘e3’, ‘e4’] LEMMA_28_2) THEN
      FULL_SIMP_TAC std_ss [SF_SEM_def, DS_EXPRESSION_EQUAL_def] THEN
      Q.EXISTS_TAC ‘h2'’ THEN
      FULL_SIMP_TAC std_ss [SUBMAP_DEF, DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
         FUNION_DEF, IN_UNION] THEN
      METIS_TAC[],


      ‘SF_SEM s h2 (sf_star (sf_ls f e2 e3) (sf_ls f e3 e4))’ by (
         MATCH_MP_TAC LEMMA_27 THEN
         ASM_SIMP_TAC std_ss [SF_SEM_def] THEN
         METIS_TAC[]
      ) THEN
      FULL_SIMP_TAC std_ss [SF_SEM_def] THEN

      Q.EXISTS_TAC ‘h1'’ THEN
      Q.EXISTS_TAC ‘h2'’ THEN

      ASM_SIMP_TAC std_ss []
   ]
);



(*
val LEMMA_30 = store_thm ("LEMMA_30",
``!s h e1 e2 e3 e4.
(SF_SEM s h (sf_ls e1 e4) /\
SF_SEM s h (sf_star (sf_ls e2 e3) sf_true)) =
(?h1 h2.
  (h = FUNION h1 h2) /\ DISJOINT (FDOM h1) (FDOM h2) /\
  (SF_SEM s h1 (sf_ls e2 e3)) /\ (DS_POINTER_DANGLES s h1 e4) /\
  !h3. ((DISJOINT (FDOM h2) (FDOM h3)) /\
       (SF_SEM s h3 (sf_ls e2 e3)) /\ (DS_POINTER_DANGLES s h3 e4)) ==>
       SF_SEM s (FUNION h3 h2) (sf_ls e1 e4))``,

SIMP_TAC std_ss [SF_SEM___STAR_TRUE] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
   Cases_on `DS_EXPRESSION_EQUAL s e2 e3` THENL [
      `!h. SF_SEM s h (sf_ls e2 e3) = (h = FEMPTY)` by
         METIS_TAC[SF_SEM_EMP_EXTEND, PF_SEM_def, SF_SEM_EVAL___SF_LIST, SF_SEM_def] THEN
      FULL_SIMP_TAC std_ss [FDOM_FEMPTY, DISJOINT_EMPTY, FUNION_FEMPTY_1, DS_POINTER_DANGLES,
         NOT_IN_EMPTY],

      Q.EXISTS_TAC `h'` THEN
      `?h''. h'' = DRESTRICT h (FDOM h DIFF FDOM h')` by METIS_TAC[] THEN
      Q.EXISTS_TAC `h''` THEN
      MATCH_MP_TAC (prove (``(((a1 = a2) /\ b /\ c /\ d) /\ ((a2 = a1) /\ b /\ c /\ d ==> e)) ==> ((a1 = a2) /\ b /\ c /\ d /\ e)``, METIS_TAC[])) THEN
      CONJ_TAC THEN1(
         FULL_SIMP_TAC std_ss [SUBMAP_DEF, GSYM fmap_EQ_THM, EXTENSION, FUNION_DEF,
            DRESTRICT_DEF, IN_UNION, IN_INTER, IN_DIFF, DISJOINT_DEF, NOT_IN_EMPTY] THEN
         REPEAT STRIP_TAC THENL [
            METIS_TAC[],
            METIS_TAC[],

            `DS_POINTER_DANGLES s h e4` by (
               MATCH_MP_TAC LEMMA_3_1_1 THEN
               FULL_SIMP_TAC std_ss [SF_SEM_def] THEN
               METIS_TAC[]
            ) THEN
            FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES] THEN
            METIS_TAC[]
         ]
      ) THEN

      REPEAT STRIP_TAC THEN
      `SF_SEM s h'' (sf_star (sf_ls e1 e2) (sf_ls e3 e4))` by (
         `SF_SEM s h (sf_star (sf_ls e1 e2) (sf_star (sf_ls e2 e3) (sf_ls e3 e4)))` by (
            MATCH_MP_TAC LEMMA_29 THEN
            ASM_SIMP_TAC std_ss [SF_SEM___STAR_TRUE] THEN
            METIS_TAC[]
         ) THEN

         FULL_SIMP_TAC std_ss [SF_SEM___STAR_THM] THEN

         `h1' = h'` by (
            `SF_IS_PRECISE (sf_ls e2 e3)` by PROVE_TAC[SF_IS_PRECISE___sf_ls] THEN
            FULL_SIMP_TAC std_ss [SF_IS_PRECISE_def] THEN
            POP_ASSUM MATCH_MP_TAC THEN
            Q.EXISTS_TAC `s` THEN
            Q.EXISTS_TAC `h` THEN
            ASM_SIMP_TAC std_ss [] THEN

            MATCH_MP_TAC SUBMAP___FUNION THEN
            DISJ2_TAC THEN
            REWRITE_TAC [SUBMAP___FUNION___ID] THEN
            FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY,
               DRESTRICT_DEF, IN_DIFF, FDOM_FUNION, IN_UNION] THEN
            METIS_TAC[]
         ) THEN


         Q.EXISTS_TAC `h1` THEN
         Q.EXISTS_TAC `h2'` THEN

         FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
            FUNION_DEF, IN_UNION, GSYM fmap_EQ_THM, DRESTRICT_DEF, IN_DIFF] THEN
         METIS_TAC[]
      ) THEN

      FULL_SIMP_TAC std_ss [SF_SEM___STAR_THM] THEN
      `DS_POINTER_DANGLES s h e4` by (
         MATCH_MP_TAC LEMMA_3_1_1 THEN
         METIS_TAC[]
      ) THEN

      `SF_SEM s (FUNION h1 h3) (sf_ls e1 e3)` by (
         MATCH_MP_TAC LEMMA_25 THEN
         Q.EXISTS_TAC `e2` THEN
         ASM_SIMP_TAC std_ss [] THEN
         REPEAT STRIP_TAC THENL [
            FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY, FDOM_FUNION, IN_UNION] THEN
            METIS_TAC[],

            FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY, FDOM_FUNION, IN_UNION,
               SF_SEM_def] THEN
            SIMP_TAC std_ss [DS_POINTER_DANGLES] THEN
            Cases_on `(GET_DSV_VALUE (DS_EXPRESSION_EVAL s e3) IN FDOM h2)` THEN1 (
               METIS_TAC[]
            ) THEN
            Tactical.REVERSE (Cases_on `n''''`) THEN1 (
               FULL_SIMP_TAC std_ss [SF_SEM_LIST_LEN_def, LET_THM]
            ) THEN
            FULL_SIMP_TAC std_ss [SF_SEM_LIST_LEN_def, PF_SEM_def, DS_POINTER_DANGLES, DS_EXPRESSION_EQUAL_def] THEN

            Q.PAT_X_ASSUM `FUNION h1 FEMPTY = X` (fn thm => ALL_TAC) THEN
            Q.PAT_X_ASSUM `X = h` (fn thm => (ASSUME_TAC (GSYM thm))) THEN
            FULL_SIMP_TAC std_ss [FDOM_FEMPTY, NOT_IN_EMPTY,
               FUNION_FEMPTY_2, DS_POINTER_DANGLES, DS_EXPRESSION_EQUAL_def,
               DRESTRICT_DEF, IN_INTER, IN_DIFF, SUBMAP_DEF, FUNION_DEF, IN_UNION]
         ]
      ) THEN

      `SF_SEM s (FUNION (FUNION h1 h3) h2) (sf_ls e1 e4)` by (
         MATCH_MP_TAC LEMMA_25 THEN
         Q.EXISTS_TAC `e3` THEN
         ASM_SIMP_TAC std_ss [] THEN
         REPEAT STRIP_TAC THENL [
            FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY, FDOM_FUNION, IN_UNION] THEN
            METIS_TAC[],

            FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY, FDOM_FUNION, IN_UNION,
               SF_SEM_def, DS_POINTER_DANGLES] THEN
            Q.PAT_X_ASSUM `X = h` (fn thm => (ASSUME_TAC (GSYM thm))) THEN
            FULL_SIMP_TAC std_ss [IN_UNION, FDOM_FUNION]
         ]
      ) THEN

      `FUNION h3 (FUNION h1 h2) = FUNION (FUNION h1 h3) h2` suffices_by (STRIP_TAC THEN
         ASM_REWRITE_TAC[]
      ) THEN


      Q.PAT_X_ASSUM `h'' = DRESTRICT h X` (fn thm => ALL_TAC) THEN
      FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FUNION_DEF, IN_UNION, DISJOINT_DEF,
         EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
      METIS_TAC[]
   ],




   CONJ_TAC THENL [
      METIS_TAC[DISJOINT_SYM],

      Q.EXISTS_TAC `h1` THEN
      ASM_SIMP_TAC std_ss [SUBMAP___FUNION___ID]
   ]
]);


val LEMMA_3_1_3 = save_thm ("LEMMA_3_1_3", LEMMA_30);
*)




val DS_POINTS_TO___RTC___sf_tree_ROOT_TO_ALL = store_thm ("DS_POINTS_TO___RTC___sf_tree_ROOT_TO_ALL",
“!s h fL es e e'.
SF_SEM s h (sf_tree fL es e) /\
~(DS_POINTER_DANGLES s h e') ==>
(DS_POINTS_TO___RTC s h fL e e')”,


SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def, GSYM LEFT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, DS_POINTER_DANGLES] THEN
Induct_on ‘n’ THEN1 (
   SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, FDOM_FEMPTY, NOT_IN_EMPTY]
) THEN

SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
REPEAT STRIP_TAC THEN1 (
   METIS_TAC[FDOM_FEMPTY, NOT_IN_EMPTY]
) THEN

Cases_on ‘DS_EXPRESSION_EQUAL s e' e’ THEN1 (
   SIMP_TAC std_ss [DS_POINTS_TO___RTC_def] THEN
   Q.EXISTS_TAC ‘0’ THEN
   FULL_SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def, DS_EXPRESSION_EQUAL_def]
) THEN
‘?h'. MEM h' hL /\ (DS_EXPRESSION_EVAL_VALUE s e' IN FDOM h')’ by (
   ‘(DS_EXPRESSION_EVAL_VALUE s e') IN FDOM (FOLDR FUNION FEMPTY hL)’ by (
      FULL_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE, DS_EXPRESSION_EVAL_VALUE_def,
         GET_DSV_VALUE_11, DS_EXPRESSION_EQUAL_def]
   ) THEN
   POP_ASSUM MP_TAC THEN
   REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
   Induct_on ‘hL’ THENL [
      SIMP_TAC list_ss [FDOM_FEMPTY, NOT_IN_EMPTY],

      SIMP_TAC list_ss [FDOM_FEMPTY, NOT_IN_EMPTY, FDOM_FUNION, IN_UNION,
         DISJ_IMP_THM, FORALL_AND_THM] THEN
      METIS_TAC[]
   ]
) THEN

‘?f. MEM (HEAP_READ_ENTRY s h e f, h') (ZIP (MAP (HEAP_READ_ENTRY s h e) fL,hL)) /\
     MEM f fL’ by (
   ASM_SIMP_TAC list_ss [MEM_ZIP, GSYM LEFT_EXISTS_AND_THM] THEN
   FULL_SIMP_TAC std_ss [MEM_EL] THEN
   Q.EXISTS_TAC ‘EL n' fL’ THEN
   Q.EXISTS_TAC ‘n'’ THEN
   FULL_SIMP_TAC list_ss [EL_MAP] THEN
   METIS_TAC[]
) THEN

‘(\(c,h'). SF_SEM___sf_tree_len s h' fL n es (dse_const (THE c))) (HEAP_READ_ENTRY s h e f,h')’
   by METIS_TAC[EVERY_MEM] THEN

MATCH_MP_TAC (REWRITE_RULE [transitive_def] DS_POINTS_TO___RTC___is_transitive) THEN
Q.EXISTS_TAC ‘dse_const (THE (HEAP_READ_ENTRY s h e f))’ THEN
FULL_SIMP_TAC list_ss [EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM, DS_EXPRESSION_EVAL_VALUE_def] THEN
‘IS_SOME (HEAP_READ_ENTRY s h e f)’ by METIS_TAC[] THEN
FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM] THEN
CONJ_TAC THEN1 (
   ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_def, DS_POINTS_TO___RTC_def] THEN
   Q.EXISTS_TAC ‘SUC 0’ THEN
   REWRITE_TAC [DS_POINTS_TO___IN_DISTANCE_def] THEN
   Q.EXISTS_TAC ‘e’ THEN
   Q.EXISTS_TAC ‘f’ THEN
   ASM_SIMP_TAC list_ss [DS_EXPRESSION_EQUAL_def, DS_POINTS_TO_def, DS_EXPRESSION_EVAL_def]
) THEN



MATCH_MP_TAC DS_POINTS_TO___RTC___SUBMAP THEN
Q.EXISTS_TAC ‘h'’ THEN
Tactical.REVERSE (CONJ_TAC) THEN1 (
   ‘h' SUBMAP (FOLDR FUNION FEMPTY hL)’ suffices_by (STRIP_TAC THEN
      POP_ASSUM MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC std_ss [SUBMAP_DEF, FDOM_DOMSUB, IN_DELETE, DOMSUB_FAPPLY_THM]
   ) THEN
   Q.PAT_X_ASSUM ‘MEM h' hL’ MP_TAC THEN
   Q.PAT_X_ASSUM ‘ALL_DISJOINT P’ MP_TAC THEN
   REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
   Induct_on ‘hL’ THENL [
      SIMP_TAC list_ss [],

      SIMP_TAC list_ss [ALL_DISJOINT_def, DISJ_IMP_THM, SUBMAP___FUNION___ID] THEN
      REPEAT STRIP_TAC THEN
      FULL_SIMP_TAC std_ss [EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
      MATCH_MP_TAC SUBMAP___FUNION THEN
      METIS_TAC[DISJOINT_SYM]
   ]
) THEN

Q.PAT_X_ASSUM ‘!s h fL. P s h fL’ MATCH_MP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
METIS_TAC[]
);



val DS_POINTS_TO___RTC___sf_tree_ROOT_TO_LEAF = store_thm ("DS_POINTS_TO___RTC___sf_tree_ROOT_TO_LEAF",
“!s h fL f es e.
MEM f fL /\
SF_SEM s h (sf_tree fL es e) ==>
DS_POINTS_TO___RTC s h [f] e es”,


SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def, GSYM LEFT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
Induct_on ‘n’ THEN1 (
   SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_POINTS_TO___RTC_def] THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC ‘0’ THEN
   ASM_SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def]
) THEN

SIMP_TAC std_ss [SF_SEM___sf_tree_len___EXTENDED_DEF, PF_SEM_def] THEN
REPEAT STRIP_TAC THEN1 (
   SIMP_TAC std_ss [DS_POINTS_TO___RTC_def] THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC ‘0’ THEN
   ASM_SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def]
) THEN

MATCH_MP_TAC (REWRITE_RULE [transitive_def] DS_POINTS_TO___RTC___is_transitive) THEN
‘IS_SOME (HEAP_READ_ENTRY s h e f)’ by METIS_TAC[] THEN
FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM] THEN
Cases_on ‘DS_EXPRESSION_EVAL s e’ THEN FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def,
   IS_DSV_NIL_def] THEN
Q.EXISTS_TAC ‘dse_const (h ' v ' f)’ THEN
CONJ_TAC THEN1 (
   SIMP_TAC std_ss [DS_POINTS_TO___RTC_def] THEN
   EXISTS_TAC “SUC 0” THEN
   REWRITE_TAC [DS_POINTS_TO___IN_DISTANCE_def] THEN
   Q.EXISTS_TAC ‘e’ THEN
   Q.EXISTS_TAC ‘f’ THEN
   ASM_SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EVAL_def, DS_EXPRESSION_EQUAL_def,
      GET_DSV_VALUE_def, IS_DSV_NIL_def]
) THEN

‘?n. (n < LENGTH hL) /\ (EL n fL = f)’ by METIS_TAC[MEM_EL] THEN
MATCH_MP_TAC DS_POINTS_TO___RTC___SUBMAP THEN
Q.EXISTS_TAC ‘EL n' hL’ THEN
CONJ_TAC THENL [
   Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
   METIS_TAC[],

   METIS_TAC[MEM_EL]
])




val SF_SEM___sf_tree_SUBTREE_THM = store_thm ("SF_SEM___sf_tree_SUBTREE_THM",
“!s h fL es e e'.
SF_SEM s h (sf_tree fL es e) /\
~(DS_POINTER_DANGLES s h e') ==>
(?h'. h' SUBMAP h /\ ((DS_EXPRESSION_EVAL_VALUE s e IN FDOM h') ==> DS_EXPRESSION_EQUAL s e e') /\
SF_SEM s h' (sf_tree fL es e'))”,

SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def, GSYM LEFT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, DS_POINTER_DANGLES] THEN
Induct_on ‘n’ THEN1 (
   SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, FDOM_FEMPTY, NOT_IN_EMPTY]
) THEN

REPEAT STRIP_TAC  THEN
Cases_on ‘DS_EXPRESSION_EQUAL s e e'’ THEN1 (
   Q.EXISTS_TAC ‘h’ THEN
   ASM_REWRITE_TAC [SUBMAP_REFL] THEN
   Q.EXISTS_TAC ‘SUC n’ THEN
   METIS_TAC[SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM, DS_EXPRESSION_EQUAL_def]
) THEN

FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len___EXTENDED_DEF, PF_SEM_def] THEN1 (
   METIS_TAC[FDOM_FEMPTY, NOT_IN_EMPTY]
) THEN
‘?c c'. (DS_EXPRESSION_EVAL s e = dsv_const c) /\ (DS_EXPRESSION_EVAL s e' = dsv_const c')’ by (
   FULL_SIMP_TAC std_ss [NOT_IS_DSV_NIL_THM, ds_value_11]
) THEN
FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, ds_value_11, IS_DSV_NIL_def,
   DS_EXPRESSION_EVAL_VALUE_def, DS_EXPRESSION_EQUAL_def] THEN

‘?h'. MEM h' hL /\ (c' IN FDOM h')’ by METIS_TAC[] THEN
‘?n f. (n < LENGTH hL) /\ (EL n hL = h') /\ (EL n fL = f)’ by METIS_TAC[MEM_EL] THEN

Q.PAT_X_ASSUM ‘!s h. P s h’ (fn thm => MP_TAC (Q.SPECL [‘s’, ‘h'’, ‘fL’, ‘es’, ‘dse_const ((h:('b, 'c) heap) ' c ' f)’, ‘e'’] thm)) THEN
ASM_SIMP_TAC std_ss [IS_DSV_NIL_def,
                     DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def] THEN
impl_tac THEN1 METIS_TAC[] THEN


‘~(c IN FDOM h')’ by (
   CCONTR_TAC THEN
   ‘c IN FDOM (FOLDR FUNION FEMPTY hL)’ by (
      POP_ASSUM MP_TAC THEN
      Q.PAT_X_ASSUM ‘MEM h' hL’ MP_TAC THEN
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      Induct_on ‘hL’ THENL [
         SIMP_TAC list_ss [],

         FULL_SIMP_TAC list_ss [FUNION_DEF, DISJ_IMP_THM, IN_UNION]
      ]
   ) THEN
   POP_ASSUM MP_TAC THEN
   ASM_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE]
) THEN

STRIP_TAC THEN
Q.EXISTS_TAC ‘h''’ THEN
REPEAT STRIP_TAC THENL [
   PROVE_TAC[SUBMAP_TRANS],
   METIS_TAC[SUBMAP_DEF],
   METIS_TAC[]
]);




val DS_POINTS_TO___RTC___sf_tree_ALL_TO_LEAF = store_thm ("DS_POINTS_TO___RTC___sf_tree_ALL_TO_LEAF",
“!s h fL f es e e'.
SF_SEM s h (sf_tree fL es e) /\ MEM f fL /\
~(DS_POINTER_DANGLES s h e') ==>
(DS_POINTS_TO___RTC s h [f] e' es)”,


REPEAT STRIP_TAC THEN
Cases_on ‘DS_EXPRESSION_EQUAL s e' es’ THEN1 (
   SIMP_TAC std_ss [DS_POINTS_TO___RTC_def] THEN
   EXISTS_TAC “0” THEN
   ASM_SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def]
) THEN

‘?h'. h' SUBMAP h /\ SF_SEM s h' (sf_tree fL es e')’ by METIS_TAC[SF_SEM___sf_tree_SUBTREE_THM] THEN

MATCH_MP_TAC DS_POINTS_TO___RTC___SUBMAP THEN
Q.EXISTS_TAC ‘h'’ THEN
ASM_REWRITE_TAC[] THEN
METIS_TAC [DS_POINTS_TO___RTC___sf_tree_ROOT_TO_LEAF]);



val DS_POINTS_TO___IN_DISTANCE___SING_UNIQUE = store_thm (
   "DS_POINTS_TO___IN_DISTANCE___SING_UNIQUE",

“!s h1 h2 h f e e1 e2 n.
   ((h1 SUBMAP h) /\ (h2 SUBMAP h) /\
   DS_POINTS_TO___IN_DISTANCE s h1 [f] e e1 n /\
   DS_POINTS_TO___IN_DISTANCE s h2 [f] e e2 n) ==>

   (DS_EXPRESSION_EQUAL s e1 e2)”,

Induct_on ‘n’ THENL [
   SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def, DS_EXPRESSION_EQUAL_def] THEN
   METIS_TAC[],

   SIMP_TAC list_ss [DS_POINTS_TO___IN_DISTANCE_def] THEN
   REPEAT STRIP_TAC THEN
   ‘DS_EXPRESSION_EQUAL s y y'’ by METIS_TAC[] THEN
   FULL_SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EQUAL_def, SUBMAP_DEF]
])






val SF_SEM___sf_tree___DS_POINTS_TO___RTC___SUBMAP = store_thm ("SF_SEM___sf_tree___DS_POINTS_TO___RTC___SUBMAP",
“!s h h' fL es e e'. (SF_SEM s h (sf_tree fL es e) /\ (h SUBMAP h') /\
                   (DS_POINTS_TO___RTC s h' fL e e') /\
                   ~(DS_POINTS_TO___RTC s h' fL es e')) ==>
         ~(DS_POINTER_DANGLES s h e')”,



SIMP_TAC std_ss [SF_SEM_def, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, GSYM LEFT_EXISTS_AND_THM,
   SF_SEM___sf_tree_def] THEN
Induct_on ‘n’ THENL [
   SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def,
      DS_POINTS_TO___RTC_def] THEN
   METIS_TAC[DS_POINTS_TO___IN_DISTANCE___DS_EXPRESSION_EQUAL],


   SIMP_TAC std_ss [SF_SEM___sf_tree_len___EXTENDED_DEF, PF_SEM_def] THEN
   REPEAT GEN_TAC THEN
   Cases_on ‘DS_EXPRESSION_EQUAL s e es’ THEN1 (
      FULL_SIMP_TAC std_ss [DS_POINTS_TO___RTC_def] THEN
      METIS_TAC[DS_POINTS_TO___IN_DISTANCE___DS_EXPRESSION_EQUAL]
   ) THEN
   ASM_SIMP_TAC std_ss [DS_POINTS_TO___RTC_def] THEN
   STRIP_TAC THEN
   Cases_on ‘n'’ THEN1 (
      FULL_SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def,
         DS_POINTER_DANGLES, DS_EXPRESSION_EQUAL_def]
   ) THEN
   FULL_SIMP_TAC list_ss [DS_POINTS_TO___IN_DISTANCE___LEFT, DS_POINTS_TO_def] THEN
   Cases_on ‘DS_EXPRESSION_EVAL s e’ THEN FULL_SIMP_TAC std_ss [IS_DSV_NIL_def, GET_DSV_VALUE_def] THEN
   ‘?n. (n < LENGTH hL) /\ (EL n fL = f)’ by METIS_TAC[MEM_EL] THEN
   ‘(EL n' hL) SUBMAP h’ by METIS_TAC[MEM_EL] THEN
   ‘~(DS_POINTER_DANGLES s (EL n' hL) e')’ suffices_by (STRIP_TAC THEN
      FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, SUBMAP_DEF]
   ) THEN
   Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
   Q.EXISTS_TAC ‘h'’ THEN
   Q.EXISTS_TAC ‘fL’ THEN
   Q.EXISTS_TAC ‘es’ THEN
   Q.EXISTS_TAC ‘y’ THEN
   ASM_SIMP_TAC std_ss [DS_POINTS_TO___RTC_def] THEN
   REPEAT STRIP_TAC THENL [
      ‘DS_EXPRESSION_EQUAL s y (dse_const (h ' v ' f))’ by (
         ASM_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def] THEN
         METIS_TAC[SUBMAP_DEF]
      ) THEN
      METIS_TAC[SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM, DS_EXPRESSION_EQUAL_def],

      METIS_TAC[SUBMAP_TRANS],

      METIS_TAC[]
   ]
]);



val SF_SEM___sf_tree___DS_POINTS_TO___RTC = store_thm ("SF_SEM___sf_tree___DS_POINTS_TO___RTC",
“!s h fL es e e'. (SF_SEM s h (sf_tree fL es e) /\
                   (DS_POINTS_TO___RTC s h fL e e')) ==>
         (DS_EXPRESSION_EQUAL s es e' \/ ~(DS_POINTER_DANGLES s h e'))”,

REPEAT STRIP_TAC THEN
MP_TAC (
   Q.SPECL [‘s’, ‘h’, ‘h’, ‘fL’, ‘es’, ‘e’, ‘e'’] SF_SEM___sf_tree___DS_POINTS_TO___RTC___SUBMAP) THEN
ASM_REWRITE_TAC[SUBMAP_REFL] THEN
MATCH_MP_TAC (prove (“(a ==> c) ==> ((~a ==> b) ==> (c \/ b))”, METIS_TAC[])) THEN
‘DS_POINTER_DANGLES s h es’ by METIS_TAC[LEMMA_3_1_1] THEN
SIMP_TAC std_ss [DS_POINTS_TO___RTC_def, GSYM LEFT_FORALL_IMP_THM] THEN
Cases_on ‘n’ THENL [
   SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def],

   FULL_SIMP_TAC list_ss [DS_POINTS_TO___IN_DISTANCE___LEFT, DS_POINTS_TO_def,
      DS_POINTER_DANGLES]
])




val TREE_NIL_THM = store_thm ("TREE_NIL_THM",
“!s h es e. ~(DS_EXPRESSION_EQUAL s e es) ==>
(SF_SEM s h (sf_tree [] es e) = SF_SEM s h (sf_points_to e []))”,


SIMP_TAC list_ss [SF_EQUIV_def, SF_SEM_def, SF_SEM___sf_tree_def,
   DS_POINTS_TO_def] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
   Cases_on ‘n’ THENL [
      FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def,
         DS_EXPRESSION_EQUAL_def],

      FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def] THEN
      FULL_SIMP_TAC std_ss [PF_SEM_def, DS_EXPRESSION_EQUAL_def] THEN
      FULL_SIMP_TAC list_ss [LENGTH_NIL] THEN
      Q.PAT_X_ASSUM ‘X = h \\ Y’ MP_TAC THEN
      ASM_SIMP_TAC list_ss [] THEN

      ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION,
         FDOM_FEMPTY, NOT_IN_EMPTY, FDOM_DOMSUB, IN_DELETE,
         IN_SING, DS_EXPRESSION_EVAL_VALUE_def] THEN
      METIS_TAC[]
   ],



   Q.EXISTS_TAC ‘SUC 0’ THEN
   ASM_REWRITE_TAC [SF_SEM___sf_tree_len_def] THEN
   FULL_SIMP_TAC list_ss [PF_SEM_def, LENGTH_NIL, ALL_DISJOINT_def,
      DS_EXPRESSION_EQUAL_def] THEN

   ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FEMPTY, FDOM_DOMSUB, NOT_IN_EMPTY,
      EXTENSION, IN_DELETE, IN_SING, DS_EXPRESSION_EVAL_VALUE_def]
]);




val SUBTREE_SUBTREE_SING = store_thm ("SUBTREE_SUBTREE_SING",
“!s h h' fL n es e es' e'.

(SF_SEM___sf_tree_len s h fL (SUC n) es e /\ h' SUBMAP h /\ ~(fL = []) /\
~(DS_EXPRESSION_EQUAL s e' es') /\
SF_SEM___sf_tree s h' fL es' e') ==>

(DS_EXPRESSION_EQUAL s e' e \/
?h'' f. (h'' SUBMAP h) /\ (h' SUBMAP h'') /\
      MEM f fL /\
      SF_SEM___sf_tree_len s h'' fL n es (dse_const (THE (HEAP_READ_ENTRY s h e f))))”,


REPEAT STRIP_TAC THEN
‘DS_POINTER_DANGLES s h es’ by (
   MATCH_MP_TAC LEMMA_3_1_1 THEN
   SIMP_TAC std_ss [SF_SEM___sf_tree_def, SF_SEM_def] THEN
   METIS_TAC[]
) THEN
FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_def, GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_EXISTS_AND_THM,
   SF_SEM___sf_tree_len___EXTENDED_DEF, PF_SEM_def] THEN
REPEAT STRIP_TAC THENL [
   Q.PAT_X_ASSUM ‘SF_SEM___sf_tree_len s h' fL n' es' e'’ MP_TAC THEN
   ‘h' = FEMPTY’ by METIS_TAC[FEMPTY_SUBMAP] THEN
   Cases_on ‘n'’ THENL [
      ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_len___EXTENDED_DEF, PF_SEM_def],

      ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_len___EXTENDED_DEF, PF_SEM_def, FDOM_FEMPTY, NOT_IN_EMPTY]
   ],


   ‘?v. (DS_EXPRESSION_EVAL s e' = dsv_const v) /\
        (v IN FDOM h')’ by (
      Cases_on ‘n'’ THENL [
         Q.PAT_X_ASSUM ‘SF_SEM___sf_tree_len s h' fL n' es' e'’ MP_TAC THEN
         ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_len___EXTENDED_DEF, PF_SEM_def],

         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN1 (
            PROVE_TAC[]
         ) THEN
         FULL_SIMP_TAC std_ss [NOT_IS_DSV_NIL_THM, ds_value_11] THEN
         METIS_TAC[GET_DSV_VALUE_def]
      ]
   ) THEN
   Cases_on ‘DS_EXPRESSION_EVAL s e’ THEN FULL_SIMP_TAC std_ss [IS_DSV_NIL_def, GET_DSV_VALUE_def,
      DS_EXPRESSION_EVAL_def] THEN

   ASM_REWRITE_TAC[DS_EXPRESSION_EQUAL_def, ds_value_11] THEN
   Cases_on ‘v = v'’ THEN ASM_SIMP_TAC std_ss [] THEN
   ‘?h''. MEM h'' hL /\ v IN FDOM h''’ by METIS_TAC[SUBMAP_DEF, ds_value_11] THEN
   ‘?n f. (n < LENGTH hL) /\ (EL n hL = h'') /\ (EL n fL = f)’ by METIS_TAC[MEM_EL] THEN
   Q.EXISTS_TAC ‘h''’ THEN
   Q.EXISTS_TAC ‘f’ THEN
   REPEAT STRIP_TAC THENL [
      PROVE_TAC[],

      ALL_TAC, (*rotate 1*)

      METIS_TAC[MEM_EL],


      ‘IS_SOME (HEAP_READ_ENTRY s h e f)’ by METIS_TAC[MEM_EL] THEN
      POP_ASSUM MP_TAC THEN
      ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM, HEAP_READ_ENTRY_def, IS_DSV_NIL_def,
         GET_DSV_VALUE_def] THEN
      METIS_TAC[]
   ] THEN

   SIMP_TAC std_ss [SUBMAP_DEF] THEN
   GEN_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC (prove (“((a ==> b) /\ a) ==> (a /\ b)”, METIS_TAC[])) THEN
   CONJ_TAC THEN1 (
      STRIP_TAC THEN
      ‘h' SUBMAP h /\ h'' SUBMAP h’ by METIS_TAC[] THEN
      FULL_SIMP_TAC std_ss [SUBMAP_DEF]
   ) THEN
   ‘DS_POINTS_TO___RTC s h' fL e' (dse_const (dsv_const x))’ by (
      MATCH_MP_TAC DS_POINTS_TO___RTC___sf_tree_ROOT_TO_ALL THEN
      ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_def, SF_SEM_def,
         DS_POINTER_DANGLES, GET_DSV_VALUE_def, DS_EXPRESSION_EVAL_def, IS_DSV_NIL_def] THEN
      METIS_TAC[]
   ) THEN
   POP_ASSUM MP_TAC THEN
   SIMP_TAC std_ss [DS_POINTS_TO___RTC_def, GSYM LEFT_FORALL_IMP_THM] THEN
   GEN_TAC THEN
   ‘DS_EXPRESSION_EVAL_VALUE s e' IN FDOM h''’ by (
      ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def, DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def]
   ) THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [AND_IMP_INTRO] THEN
   Q.SPEC_TAC (‘e'’, ‘e’) THEN

   Induct_on ‘n'''’ THENL [
      SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def, DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def,
      DS_EXPRESSION_EVAL_VALUE_def] THEN
      METIS_TAC[GET_DSV_VALUE_def],



      SIMP_TAC list_ss [DS_POINTS_TO___IN_DISTANCE___LEFT, DS_POINTS_TO_def] THEN
      REPEAT STRIP_TAC THEN
      Cases_on ‘DS_EXPRESSION_EVAL s e''’ THEN (
         FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, IS_DSV_NIL_def, GET_DSV_VALUE_def,
         DS_EXPRESSION_EVAL_VALUE_def]
      ) THEN

      Q.PAT_X_ASSUM ‘!e. P e’ MATCH_MP_TAC THEN
      Q.EXISTS_TAC ‘y’ THEN
      FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def] THEN
      Cases_on ‘DS_EXPRESSION_EQUAL s es (dse_const (h' ' v'' ' f'))’ THEN1 (
         Cases_on ‘n'''’ THENL [
            FULL_SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def, DS_EXPRESSION_EQUAL_def,
               DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def] THEN
            Q.PAT_X_ASSUM ‘Y = dsv_const x’ ASSUME_TAC THEN
            FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, IS_DSV_NIL_def, GET_DSV_VALUE_def] THEN
            METIS_TAC[SUBMAP_DEF],

            FULL_SIMP_TAC list_ss [DS_POINTS_TO___IN_DISTANCE___LEFT, DS_POINTS_TO_def,
               DS_EXPRESSION_EQUAL_def, DS_POINTER_DANGLES, DS_EXPRESSION_EVAL_def] THEN
            METIS_TAC[SUBMAP_DEF]
         ]
      ) THEN
      ‘~(DS_POINTER_DANGLES s h'' (dse_const (h' ' v'' ' f')))’ by (
         MATCH_MP_TAC LEMMA_3_1_2 THEN
         Q.EXISTS_TAC ‘f'’ THEN
         Q.EXISTS_TAC ‘fL’ THEN
         Q.EXISTS_TAC ‘dse_const (dsv_const v'')’ THEN
         Q.EXISTS_TAC ‘es’ THEN
         ‘h'' ' v'' = h' ' v''’ by METIS_TAC[SUBMAP_DEF] THEN
         ASM_SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def, IS_DSV_NIL_def,
            SF_SEM___sf_tree_def, SF_SEM_def] THEN
         METIS_TAC[]
      ) THEN
      FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, DS_EXPRESSION_EVAL_def]
   ]
])


val SUBTREE___IS_POSTFIX___OR___LIST = store_thm ("SUBTREE___IS_POSTFIX___OR___LIST",

“!s h h' fL es e es' e'.

(SF_SEM s h (sf_tree fL es e) /\ h' SUBMAP h /\
SF_SEM s h' (sf_tree fL es' e') /\ ~(fL = []) /\
~DS_EXPRESSION_EQUAL s e' es') ==>

(DS_EXPRESSION_EQUAL s es es' \/ ?f. (fL = [f]))”,


SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def, GSYM LEFT_EXISTS_AND_THM,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
Induct_on ‘n’ THENL [
   Cases_on ‘n'’ THENL [
      SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
      METIS_TAC[],

      SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
      METIS_TAC[FEMPTY_SUBMAP, FDOM_FEMPTY, NOT_IN_EMPTY]
   ],

   REPEAT STRIP_TAC THEN
   MP_TAC (Q.SPECL [‘s’, ‘h’, ‘h'’, ‘fL’, ‘n’, ‘es’, ‘e’, ‘es'’, ‘e'’]
      SUBTREE_SUBTREE_SING) THEN
   MATCH_MP_TAC (prove (“(a /\ (b ==> c)) ==> ((a ==> b) ==> c)”, METIS_TAC[])) THEN
   CONJ_TAC THEN1 (
      ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_def] THEN
      METIS_TAC[]
   ) THEN
   Tactical.REVERSE (Cases_on ‘DS_EXPRESSION_EQUAL s e' e’) THEN1 (
      ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      METIS_TAC[]
   ) THEN


   ASM_REWRITE_TAC[] THEN
   Cases_on ‘?f. fL = [f]’ THEN ASM_REWRITE_TAC[] THEN
   ‘?f1 f2 fL'. fL = f1::f2::fL'’ by (
      Cases_on ‘fL’ THEN1 FULL_SIMP_TAC list_ss [] THEN
      Cases_on ‘t’ THEN1 FULL_SIMP_TAC list_ss [] THEN
      SIMP_TAC list_ss []
   ) THEN
   FULL_SIMP_TAC list_ss [] THEN

   ‘DS_POINTS_TO___RTC s h [f1] e es' /\
    DS_POINTS_TO___RTC s h [f2] e es'’ by (
      ‘DS_POINTS_TO___RTC s h' [f1] e' es' /\
      DS_POINTS_TO___RTC s h' [f2] e' es'’ by (
         ‘SF_SEM s h' (sf_tree fL es' e')’ by (
            SIMP_TAC std_ss [SF_SEM___sf_tree_def, SF_SEM_def] THEN
            METIS_TAC[]
         ) THEN
         ‘MEM f1 fL /\ MEM f2 fL’ by ASM_SIMP_TAC list_ss [] THEN
         METIS_TAC[DS_POINTS_TO___RTC___sf_tree_ROOT_TO_LEAF]
      ) THEN
      METIS_TAC[DS_POINTS_TO___RTC___SUBMAP, DS_POINTS_TO___IN_DISTANCE___DS_EXPRESSION_EQUAL,
         DS_POINTS_TO___RTC_def]
   ) THEN
   ‘~(DS_POINTER_DANGLES s h e)’ by (
      Cases_on ‘n'’ THENL [
         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def],

         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, DS_POINTER_DANGLES,
            DS_EXPRESSION_EQUAL_def, PF_SEM_def] THEN
         METIS_TAC[FEMPTY_SUBMAP, NOT_IN_EMPTY, FDOM_FEMPTY]
      ]
   ) THEN
   Cases_on ‘DS_EXPRESSION_EVAL s e’ THEN (
      FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, IS_DSV_NIL_def, GET_DSV_VALUE_def,
         DS_EXPRESSION_EVAL_def]
   ) THEN

   ‘?h1 h2. (DISJOINT (FDOM h1) (FDOM h2)) /\
            (h1 SUBMAP h) /\ (h2 SUBMAP h) /\
            (SF_SEM___sf_tree_len s h1 fL n es (dse_const (h ' v ' f1))) /\
            (SF_SEM___sf_tree_len s h2 fL n es (dse_const (h ' v ' f2)))’ by (
      FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len___EXTENDED_DEF, PF_SEM_def] THEN1 (
         METIS_TAC[FDOM_FEMPTY, NOT_IN_EMPTY]
      ) THEN
      Q.EXISTS_TAC ‘EL 0 hL’ THEN
      Q.EXISTS_TAC ‘EL 1 hL’ THEN
      ‘(0 < LENGTH hL) /\ (1 < LENGTH hL)’ by FULL_SIMP_TAC list_ss [] THEN
      ‘(EL 0 fL = f1) /\ (EL 1 fL = f2)’ by ASM_SIMP_TAC list_ss [] THEN
      REPEAT STRIP_TAC THENL [
         FULL_SIMP_TAC list_ss [EL_ALL_DISJOINT_EQ, EL_MAP],
         METIS_TAC[MEM_EL],
         METIS_TAC[MEM_EL],
         METIS_TAC[GET_DSV_VALUE_def],
         METIS_TAC[GET_DSV_VALUE_def]
      ]
   ) THEN

   ‘DS_POINTS_TO___RTC s h [f1] (dse_const (h ' v ' f1)) es' /\
    DS_POINTS_TO___RTC s h [f2] (dse_const (h ' v ' f2)) es'’ by (
      FULL_SIMP_TAC std_ss [DS_POINTS_TO___RTC_def] THEN
      CONJ_TAC THENL [
         Cases_on ‘n''’ THEN1 (
            FULL_SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def, DS_EXPRESSION_EQUAL_def]
         ) THEN
         FULL_SIMP_TAC list_ss [DS_POINTS_TO___IN_DISTANCE___LEFT, DS_POINTS_TO_def,
            GET_DSV_VALUE_def] THEN
         ‘DS_EXPRESSION_EQUAL s y (dse_const (h ' v ' f1))’ by (
            ASM_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def]
         ) THEN
         METIS_TAC[DS_POINTS_TO___IN_DISTANCE___DS_EXPRESSION_EQUAL],


         Cases_on ‘n'''’ THEN1 (
            FULL_SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def, DS_EXPRESSION_EQUAL_def]
         ) THEN
         FULL_SIMP_TAC list_ss [DS_POINTS_TO___IN_DISTANCE___LEFT, DS_POINTS_TO_def,
            GET_DSV_VALUE_def] THEN
         ‘DS_EXPRESSION_EQUAL s y (dse_const (h ' v ' f2))’ by (
            ASM_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def]
         ) THEN
         METIS_TAC[DS_POINTS_TO___IN_DISTANCE___DS_EXPRESSION_EQUAL]
      ]
   ) THEN

   ‘DS_POINTER_DANGLES s h es’ by (
      MATCH_MP_TAC LEMMA_3_1_1 THEN
      SIMP_TAC std_ss [SF_SEM___sf_tree_def, SF_SEM_def] THEN
      METIS_TAC[]
   ) THEN
   CCONTR_TAC THEN
   ‘~(DS_POINTER_DANGLES s h1 es')’ by (
      MATCH_MP_TAC SF_SEM___sf_tree___DS_POINTS_TO___RTC___SUBMAP THEN
      Q.EXISTS_TAC ‘h’ THEN
      Q.EXISTS_TAC ‘fL’ THEN
      Q.EXISTS_TAC ‘es’ THEN
      Q.EXISTS_TAC ‘(dse_const (h ' v ' f1))’ THEN
      ASM_SIMP_TAC std_ss [] THEN
      REPEAT STRIP_TAC THENL [
         SIMP_TAC std_ss [SF_SEM___sf_tree_def, SF_SEM_def] THEN
         METIS_TAC[],

         MATCH_MP_TAC DS_POINTS_TO___RTC___SUBSET THEN
         Q.EXISTS_TAC ‘[f1]’ THEN
         ASM_SIMP_TAC list_ss [],

         FULL_SIMP_TAC std_ss [DS_POINTS_TO___RTC_def] THEN
         Cases_on ‘n''''''’ THENL [
            FULL_SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def],

            FULL_SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE___LEFT, DS_POINTS_TO_def,
               DS_POINTER_DANGLES] THEN
            FULL_SIMP_TAC std_ss []
         ]
      ]
   ) THEN

   ‘~(DS_POINTER_DANGLES s h2 es')’ by (
      MATCH_MP_TAC SF_SEM___sf_tree___DS_POINTS_TO___RTC___SUBMAP THEN
      Q.EXISTS_TAC ‘h’ THEN
      Q.EXISTS_TAC ‘fL’ THEN
      Q.EXISTS_TAC ‘es’ THEN
      Q.EXISTS_TAC ‘(dse_const (h ' v ' f2))’ THEN
      ASM_SIMP_TAC std_ss [] THEN
      REPEAT STRIP_TAC THENL [
         SIMP_TAC std_ss [SF_SEM___sf_tree_def, SF_SEM_def] THEN
         METIS_TAC[],

         MATCH_MP_TAC DS_POINTS_TO___RTC___SUBSET THEN
         Q.EXISTS_TAC ‘[f2]’ THEN
         ASM_SIMP_TAC list_ss [],

         FULL_SIMP_TAC std_ss [DS_POINTS_TO___RTC_def] THEN
         Cases_on ‘n''''''’ THENL [
            FULL_SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE_def],

            FULL_SIMP_TAC std_ss [DS_POINTS_TO___IN_DISTANCE___LEFT, DS_POINTS_TO_def,
               DS_POINTER_DANGLES] THEN
            FULL_SIMP_TAC std_ss []
         ]
      ]
   ) THEN

   FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, DISJOINT_DEF, EXTENSION,
      NOT_IN_EMPTY, IN_INTER] THEN
   METIS_TAC[]
]);





val SUBTREE_EXCHANGEABLE_THM = store_thm ("SUBTREE_EXCHANGEABLE_THM",

“!s h1 h2 fL es e e1' e2'.

(SF_SEM s (FUNION h1 h2) (sf_tree fL es e) /\
SF_SEM s h1 (sf_tree fL e1' e2') /\
(DISJOINT (FDOM h1) (FDOM h2))) ==>

(!h1'.
SF_SEM s h1' (sf_tree fL e1' e2') /\
DS_POINTER_DANGLES s h1' es /\
(DISJOINT (FDOM h1') (FDOM h2)) ==>
SF_SEM s (FUNION h1' h2) (sf_tree fL es e))”,


REPEAT GEN_TAC THEN
Cases_on ‘DS_EXPRESSION_EQUAL s e es’ THEN1 (
   ‘DS_EXPRESSION_EQUAL s e es’ by FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def] THEN
   ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_THM, FUNION_EQ_FEMPTY, LET_THM] THEN
   Cases_on ‘DS_EXPRESSION_EQUAL s e2' e1'’ THEN ASM_REWRITE_TAC[] THEN1 (
      METIS_TAC[]
   ) THEN
   Cases_on ‘h1 = FEMPTY’ THEN ASM_REWRITE_TAC[] THEN
   SIMP_TAC std_ss [SF_SEM___sf_points_to_THM] THEN
   SIMP_TAC std_ss [DS_POINTS_TO_def, FDOM_FEMPTY, NOT_IN_EMPTY]
) THEN
Cases_on ‘fL = []’ THEN1 (
   ASM_SIMP_TAC std_ss [TREE_NIL_THM, DS_POINTS_TO_def] THEN
   Cases_on ‘~DS_EXPRESSION_EQUAL s e2' e1'’ THENL [
      ASM_SIMP_TAC std_ss [TREE_NIL_THM, DS_POINTS_TO_def] THEN
      SIMP_TAC list_ss [SF_SEM_def, DS_POINTS_TO_def, FUNION_DEF, IN_UNION,
         IN_SING, DS_EXPRESSION_EVAL_VALUE_def] THEN
      Cases_on ‘FDOM h1 = {GET_DSV_VALUE (DS_EXPRESSION_EVAL s e2')}’ THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC std_ss [IN_SING],

      FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_THM] THEN
      Cases_on ‘h1 = FEMPTY’ THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC std_ss []
   ]
) THEN
Cases_on ‘DS_EXPRESSION_EQUAL s e2' e1'’ THEN1 (
   ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_THM, LET_THM] THEN
   METIS_TAC[]
) THEN
REPEAT STRIP_TAC THEN

‘DS_EXPRESSION_EQUAL s es e1' \/ ~DS_EXPRESSION_EQUAL s es e1' /\ ?f. fL = [f]’ by (
   METIS_TAC[SUBTREE___IS_POSTFIX___OR___LIST, SUBMAP___FUNION___ID]
) THENL [
   FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_def, SF_SEM_def] THEN
   Q.PAT_X_ASSUM ‘SF_SEM___sf_tree_len s (FUNION h1 h2) fL n es e’ MP_TAC THEN
   Q_TAC MP_FREE_VAR_TAC ‘h2’ THEN
   Q.PAT_X_ASSUM ‘~(DS_EXPRESSION_EQUAL s e es)’ (K ALL_TAC) THEN

   REWRITE_TAC [AND_IMP_INTRO, GSYM CONJ_ASSOC] THEN
   Q.SPEC_TAC (‘h2’, ‘h2’) THEN
   Q.SPEC_TAC (‘e’, ‘e’) THEN


   Induct_on ‘n’ THENL [
      SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, FUNION_EQ_FEMPTY,
         FDOM_FEMPTY, DISJOINT_EMPTY] THEN
      REPEAT STRIP_TAC THEN
      Cases_on ‘n'’ THENL [
         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def],

         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
         FULL_SIMP_TAC std_ss [FDOM_FEMPTY, NOT_IN_EMPTY]
      ],



      REPEAT STRIP_TAC THEN
      MP_TAC (Q.SPECL [‘s’, ‘FUNION h1 h2’, ‘h1’, ‘fL’, ‘n’, ‘es’, ‘e’, ‘e1'’, ‘e2'’] SUBTREE_SUBTREE_SING) THEN
      MATCH_MP_TAC (prove (“(a /\ (b ==> c)) ==> ((a ==> b) ==> c)”, SIMP_TAC std_ss [])) THEN
      CONJ_TAC THEN1 (
        ASM_SIMP_TAC std_ss [SUBMAP___FUNION___ID, SF_SEM___sf_tree_len_def, SF_SEM___sf_tree_def]  THEN
        METIS_TAC[]
      ) THEN
      STRIP_TAC THEN1 (
         ‘SF_SEM s h1 (sf_tree fL es e) /\
         SF_SEM s h1' (sf_tree fL es e)’ by (
            FULL_SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def]  THEN
            METIS_TAC[SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM, DS_EXPRESSION_EQUAL_def]
         ) THEN
         ‘FUNION h1 h2 = h1’ by (
            ‘SF_IS_PRECISE (sf_tree fL es e)’ by REWRITE_TAC[SF_IS_PRECISE_THM] THEN
            FULL_SIMP_TAC std_ss [SF_IS_PRECISE_def] THEN
            POP_ASSUM MATCH_MP_TAC THEN
            Q.EXISTS_TAC ‘s’ THEN
            Q.EXISTS_TAC ‘FUNION h1 h2’ THEN
            ASM_SIMP_TAC std_ss [SUBMAP___FUNION___ID, SUBMAP_REFL,
               SF_SEM___sf_tree_def, SF_SEM_def] THEN
            METIS_TAC[]
         ) THEN
         ‘h2 = FEMPTY’ by (
            ‘!x. x IN FDOM h2 ==> x IN FDOM h1’ by (
               POP_ASSUM MP_TAC THEN
               SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FUNION_DEF, IN_UNION] THEN
               METIS_TAC[]
            ) THEN
            FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
            ‘!x. ~(x IN FDOM h2)’ by METIS_TAC[] THEN
            ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, NOT_IN_EMPTY, FDOM_FEMPTY]
         ) THEN
         FULL_SIMP_TAC std_ss [FUNION_FEMPTY_2, SF_SEM___sf_tree_def, SF_SEM_def] THEN
         METIS_TAC[]
      ) THEN

      ‘?hx. DRESTRICT h'' (COMPL (FDOM h1)) = hx’ by METIS_TAC[] THEN
      ‘(h'' = FUNION h1 hx) /\ (hx SUBMAP h2)’ by (
         POP_ASSUM (fn thm => REWRITE_TAC[GSYM thm]) THEN
         Q.PAT_X_ASSUM ‘h1 SUBMAP h''’ MP_TAC THEN
         Q.PAT_X_ASSUM ‘h'' SUBMAP FUNION h1 h2’ MP_TAC THEN
         REPEAT (POP_ASSUM (K ALL_TAC)) THEN
         SIMP_TAC std_ss [SUBMAP_DEF, GSYM fmap_EQ_THM,
            EXTENSION, DRESTRICT_DEF, FUNION_DEF, IN_UNION, IN_INTER, IN_COMPL] THEN
         METIS_TAC[]
      ) THEN

      FULL_SIMP_TAC list_ss [SF_SEM___sf_tree_len___EXTENDED_DEF, PF_SEM_def] THEN1 (
         Q.EXISTS_TAC ‘0’ THEN
         FULL_SIMP_TAC std_ss [FUNION_EQ_FEMPTY, SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
         Cases_on ‘n'’ THENL [
            FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def],

            FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
            FULL_SIMP_TAC std_ss [FDOM_FEMPTY, NOT_IN_EMPTY]
         ]
      ) THEN
      ‘?nx. (nx < LENGTH hL) /\ (EL nx fL = f)’ by METIS_TAC[MEM_EL] THEN

      ‘?c. DS_EXPRESSION_EVAL s e = dsv_const c’ by FULL_SIMP_TAC std_ss [NOT_IS_DSV_NIL_THM, ds_value_11] THEN
      FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def, ds_value_11] THEN
      ‘EL nx hL = h''’ by (
         ‘SF_IS_PRECISE (sf_tree fL es (dse_const (FUNION h1 h2 ' c ' f)))’ by REWRITE_TAC[SF_IS_PRECISE_THM] THEN
         FULL_SIMP_TAC std_ss [SF_IS_PRECISE_def] THEN
         POP_ASSUM MATCH_MP_TAC THEN
         Q.EXISTS_TAC ‘s’ THEN
         Q.EXISTS_TAC ‘FUNION h1 h2’ THEN
         ASM_SIMP_TAC list_ss [SF_SEM___sf_tree_def, SF_SEM_def] THEN
         REPEAT STRIP_TAC THENL [
            METIS_TAC[MEM_EL],
            METIS_TAC[],

            Q.PAT_X_ASSUM ‘SF_SEM___sf_tree_len s (FUNION h1 hx) fL n es Y’ MP_TAC THEN
            ‘IS_SOME (HEAP_READ_ENTRY s (FUNION h1 h2) e f)’ by METIS_TAC[] THEN
            FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM, HEAP_READ_ENTRY_def, GET_DSV_VALUE_def] THEN
            METIS_TAC[]
         ]
      ) THEN

      ‘~(c IN FDOM h1)’ by (
         ‘~(c IN FDOM h'')’ suffices_by (STRIP_TAC THEN
            POP_ASSUM MP_TAC THEN
            FULL_SIMP_TAC std_ss [FUNION_DEF, IN_UNION]
         ) THEN
         CCONTR_TAC THEN
         ‘c IN FDOM (FOLDR FUNION FEMPTY hL)’ suffices_by (STRIP_TAC THEN
            POP_ASSUM MP_TAC THEN
            ASM_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE]
         ) THEN
         POP_ASSUM MP_TAC THEN
         ‘MEM h'' hL’ by METIS_TAC[MEM_EL] THEN
         POP_ASSUM MP_TAC THEN
         REPEAT (POP_ASSUM (K ALL_TAC)) THEN

         Induct_on ‘hL’ THENL [
            SIMP_TAC list_ss [],
            FULL_SIMP_TAC list_ss [FUNION_DEF, IN_UNION, DISJ_IMP_THM]
         ]
      ) THEN
      ‘c IN FDOM h2’ by FULL_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION] THEN
      ‘~(c IN FDOM h1')’ by (
         FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
         METIS_TAC[]
      ) THEN
      ‘!n. (n < LENGTH hL) /\ (~(n = nx)) ==>
           (EL n hL) SUBMAP h2 /\
           (DISJOINT (FDOM (EL n hL)) (FDOM (FUNION h1 hx)))’ by (
         GEN_TAC THEN STRIP_TAC THEN

         ‘(EL n''' hL) SUBMAP FUNION h1 h2’ by METIS_TAC[MEM_EL] THEN
         POP_ASSUM MP_TAC THEN

         FULL_SIMP_TAC list_ss [EL_ALL_DISJOINT_EQ, EL_MAP] THEN
         ‘DISJOINT (FDOM (EL n''' hL)) (FDOM (EL nx hL))’ by METIS_TAC[] THEN
         POP_ASSUM MP_TAC THEN
         ASM_REWRITE_TAC[] THEN

         REPEAT (POP_ASSUM (K ALL_TAC)) THEN
         SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
            SUBMAP_DEF, FUNION_DEF, IN_UNION] THEN
         METIS_TAC[]
      ) THEN
      FULL_SIMP_TAC std_ss [FUNION_DEF, ds_value_11, DISJOINT_UNION_BOTH] THEN

      ‘?n. SF_SEM___sf_tree_len s (FUNION h1' hx) fL n es (dse_const (h2 ' c ' f))’ by (
         Q.PAT_X_ASSUM ‘!e h2. P e h2’ MATCH_MP_TAC THEN
         REWRITE_TAC[CONJ_ASSOC] THEN
         CONJ_TAC THENL [
            FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY, SUBMAP_DEF] THEN
            METIS_TAC[],

            METIS_TAC[]
         ]
      ) THEN

      ‘?m. (n''' <= m) /\ (n <= m)’ by (
         Q.EXISTS_TAC ‘MAX n''' n’ THEN
         SIMP_TAC arith_ss []
      ) THEN
      Q.EXISTS_TAC ‘SUC m’ THEN


      ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_len___EXTENDED_DEF, PF_SEM_def, GET_DSV_VALUE_def,
         FUNION_DEF, IN_UNION, ds_value_11] THEN

      Q.EXISTS_TAC ‘REPLACE_ELEMENT (FUNION h1' hx) nx hL’ THEN
      ASM_SIMP_TAC std_ss [REPLACE_ELEMENT_SEM] THEN

      REPEAT STRIP_TAC THENL [
         ‘IS_SOME (HEAP_READ_ENTRY s (FUNION h1 h2) e f')’ by METIS_TAC[] THEN
         POP_ASSUM MP_TAC THEN
         SIMP_TAC std_ss [HEAP_READ_ENTRY_THM, FUNION_DEF, IN_UNION] THEN
         ASM_SIMP_TAC std_ss [IS_DSV_NIL_def, GET_DSV_VALUE_def],


         Q.PAT_X_ASSUM ‘ALL_DISJOINT Y’ MP_TAC THEN
         SIMP_TAC list_ss [EL_ALL_DISJOINT_EQ, REPLACE_ELEMENT_SEM, EL_MAP] THEN
         HO_MATCH_MP_TAC (prove (“(!n1 n2. P n1 n2 ==> ((Q n1 n2) ==> (Q' n1 n2))) ==>
                                 ((!n1 n2. P n1 n2 ==> Q n1 n2) ==>
                                 (!n1 n2. P n1 n2 ==> Q' n1 n2))”, METIS_TAC[])) THEN
         SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
         REPEAT GEN_TAC THEN STRIP_TAC THEN
         Cases_on ‘n1 = nx’ THEN
         Cases_on ‘n2 = nx’ THEN
         ASM_SIMP_TAC list_ss [] THENL [
            ‘EL n2 hL SUBMAP h2’ by METIS_TAC[] THEN
            POP_ASSUM MP_TAC THEN
            Q.PAT_X_ASSUM ‘DISJOINT (FDOM h1') (FDOM h2)’ MP_TAC THEN
            REPEAT (POP_ASSUM (K ALL_TAC)) THEN
            SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
               FDOM_FUNION, IN_UNION, SUBMAP_DEF] THEN
            METIS_TAC[],

            ‘EL n1 hL SUBMAP h2’ by METIS_TAC[] THEN
            POP_ASSUM MP_TAC THEN
            Q.PAT_X_ASSUM ‘DISJOINT (FDOM h1') (FDOM h2)’ MP_TAC THEN
            REPEAT (POP_ASSUM (K ALL_TAC)) THEN
            SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
               FDOM_FUNION, IN_UNION, SUBMAP_DEF] THEN
            METIS_TAC[]
         ],



         Q.PAT_X_ASSUM ‘Y = Z \\ c’ MP_TAC THEN
         ‘((h1 \\ c) = h1) /\
          ((h1' \\ c) = h1')’ by (
            ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_DOMSUB, IN_DELETE,
               DOMSUB_FAPPLY_NEQ, EXTENSION] THEN
            METIS_TAC[]
         ) THEN
         ASM_SIMP_TAC std_ss [DOMSUB_FUNION] THEN
         Q.PAT_X_ASSUM ‘ALL_DISJOINT Y’ MP_TAC THEN
         Q.PAT_X_ASSUM ‘DISJOINT X Y’ MP_TAC THEN
         Q.PAT_X_ASSUM ‘DISJOINT X Y’ MP_TAC THEN
         Q.PAT_X_ASSUM ‘hx SUBMAP h2’ MP_TAC THEN
         ‘EL nx hL = FUNION h1 hx’ by METIS_TAC[] THEN POP_ASSUM MP_TAC THEN
         Q.PAT_X_ASSUM ‘nx < LENGTH hL’ MP_TAC THEN
         Q.PAT_X_ASSUM ‘!n. (n < LENGTH hL) /\ ~(n = nx) ==> P n’ MP_TAC THEN
         REPEAT (POP_ASSUM (K ALL_TAC)) THEN
         ‘?h. (!h1. (FUNION h1 (h2 \\ c)) = (FUNION h1 h)) /\
                   (FDOM h SUBSET FDOM h2)’ by (
            Q.EXISTS_TAC ‘h2 \\ c’ THEN
            SIMP_TAC std_ss [SUBSET_DEF, FDOM_DOMSUB, IN_DELETE]
         ) THEN
         ASM_REWRITE_TAC [] THEN
         POP_ASSUM MP_TAC THEN
         SIMP_TAC std_ss [AND_IMP_INTRO, GSYM CONJ_ASSOC] THEN
         REPEAT (POP_ASSUM (K ALL_TAC)) THEN

         Q.SPEC_TAC (‘h’, ‘h’) THEN
         Q.SPEC_TAC (‘nx’, ‘nx’) THEN

         Induct_on ‘hL’ THENL [
            SIMP_TAC list_ss [],

            SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM, ALL_DISJOINT_def] THEN
            REPEAT STRIP_TAC THEN
            Cases_on ‘nx’ THENL [
               FULL_SIMP_TAC list_ss [REPLACE_ELEMENT_def] THEN
               Q.PAT_X_ASSUM ‘Y = FUNION h1 h'’ MP_TAC THEN

               ASM_SIMP_TAC std_ss [GSYM FUNION___ASSOC] THEN
               ‘FDOM (FUNION hx (FOLDR FUNION FEMPTY hL)) SUBSET (FDOM h2)’ suffices_by (STRIP_TAC THEN
                  ‘DISJOINT (FDOM h1) (FDOM h') /\
                   DISJOINT (FDOM h1) (FDOM (FUNION hx (FOLDR FUNION FEMPTY hL))) /\
                   DISJOINT (FDOM h1') (FDOM h') /\
                   DISJOINT (FDOM h1') (FDOM (FUNION hx (FOLDR FUNION FEMPTY hL)))’ by (
                     FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
                        FDOM_DOMSUB, IN_DELETE, SUBSET_DEF] THEN
                     METIS_TAC[]
                  ) THEN
                  ASM_SIMP_TAC std_ss [FUNION_EQ]
               ) THEN
               ‘!h'. MEM h' hL ==> FDOM h' SUBSET FDOM h2’ suffices_by (STRIP_TAC THEN
                  SIMP_TAC std_ss [FDOM_FUNION, UNION_SUBSET] THEN
                  CONJ_TAC THENL [
                     FULL_SIMP_TAC std_ss [SUBMAP_DEF, SUBSET_DEF],

                     POP_ASSUM MP_TAC THEN
                     REPEAT (POP_ASSUM (K ALL_TAC)) THEN
                     Induct_on ‘hL’ THENL [
                        SIMP_TAC list_ss [FDOM_FEMPTY, EMPTY_SUBSET],

                        FULL_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM, FDOM_FUNION,
                           UNION_SUBSET]
                     ]
                  ]
               ) THEN
               SIMP_TAC std_ss [MEM_EL] THEN
               REPEAT STRIP_TAC THEN
               Q.PAT_X_ASSUM ‘!n. P n’ (fn thm => (MP_TAC (Q.SPEC ‘SUC n’ thm))) THEN
               ASM_SIMP_TAC list_ss [SUBMAP_DEF, SUBSET_DEF],



               FULL_SIMP_TAC list_ss [REPLACE_ELEMENT_def] THEN
               Q.PAT_X_ASSUM ‘!nx h''. P nx h''’ (fn thm =>
                  MP_TAC (Q.SPECL [‘n’, ‘DRESTRICT h' (COMPL (FDOM (h:('b, 'c) heap)))’] thm)) THEN
               ASM_SIMP_TAC std_ss [] THEN
               ‘DISJOINT (FDOM (h:('b, 'c) heap)) (FDOM (FOLDR FUNION FEMPTY (hL:('b, 'c) heap list)))’ by (
                  FULL_SIMP_TAC std_ss [EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
                  Q.PAT_X_ASSUM ‘!y. MEM y hL ==> P y’ MP_TAC THEN
                  REPEAT (POP_ASSUM (K ALL_TAC)) THEN
                  Induct_on ‘hL’ THENL [
                     SIMP_TAC list_ss [FDOM_FEMPTY, DISJOINT_EMPTY],

                     FULL_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM, FDOM_FUNION,
                        DISJOINT_UNION_BOTH, DISJOINT_SYM]
                  ]
               ) THEN

               ‘FOLDR FUNION FEMPTY hL = DRESTRICT (FUNION h1 h') (COMPL (FDOM h))’ by
                  METIS_TAC[DRESTRICT_EQ_FUNION] THEN
               ‘DISJOINT (FDOM h) (FDOM h1) /\
                DISJOINT (FDOM h) (FDOM hx) /\
                h SUBMAP h2’ by (
                  Q.PAT_X_ASSUM ‘!n. P n’ (fn thm => (MP_TAC (Q.SPEC ‘0’ thm))) THEN
                  ASM_SIMP_TAC list_ss [SUBMAP_DEF, SUBSET_DEF, DISJOINT_SYM]
               ) THEN

               ‘DRESTRICT (FUNION h1 h') (COMPL (FDOM h)) =
                FUNION h1 (DRESTRICT h' (COMPL (FDOM h)))’ by (
                  Q.PAT_X_ASSUM ‘DISJOINT (FDOM h) (FDOM h1)’ MP_TAC THEN
                  REPEAT (POP_ASSUM (K ALL_TAC)) THEN
                  SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, DRESTRICT_DEF, DISJOINT_DEF,
                     NOT_IN_EMPTY, IN_INTER, FUNION_DEF, IN_UNION, IN_COMPL,
                     DISJ_IMP_THM] THEN
                  METIS_TAC[]
               ) THEN
               FULL_SIMP_TAC std_ss [DRESTRICT_DEF, SUBSET_DEF, IN_INTER] THEN
               MATCH_MP_TAC (prove (“(a /\ (b ==> c)) ==> ((a ==> b) ==> c)”, METIS_TAC[])) THEN
               CONJ_TAC THEN1 (
                  GEN_TAC THEN STRIP_TAC THEN
                  Q.PAT_X_ASSUM ‘!n. P n’ (fn thm => (MP_TAC (Q.SPEC ‘SUC n'’ thm))) THEN
                  ASM_SIMP_TAC list_ss []
               ) THEN
               SIMP_TAC std_ss [] THEN
               STRIP_TAC THEN
               ‘DISJOINT (FDOM h) (FDOM h1')’ by (
                  Q.PAT_X_ASSUM ‘DISJOINT (FDOM h1') (FDOM h2)’ MP_TAC THEN
                  Q.PAT_X_ASSUM ‘h SUBMAP h2’ MP_TAC THEN
                  REPEAT (POP_ASSUM (K ALL_TAC)) THEN

                  SIMP_TAC std_ss [SUBMAP_DEF, DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
                  METIS_TAC[]
               ) THEN
               ‘(!Y. FUNION h (FUNION h1 Y) = FUNION h1 (FUNION h Y)) /\
                (!Y. FUNION h (FUNION h1' Y) = FUNION h1' (FUNION h Y))’ by METIS_TAC[FUNION___ASSOC,
                  FUNION___COMM] THEN
               Q.PAT_X_ASSUM ‘Y = FUNION h1 h'’ MP_TAC THEN
               ASM_REWRITE_TAC[] THEN

               ‘DISJOINT (FDOM h1) (FDOM (FUNION h (DRESTRICT h' (COMPL (FDOM h))))) /\
                DISJOINT (FDOM h1) (FDOM h') /\
                DISJOINT (FDOM h1') (FDOM (FUNION h (DRESTRICT h' (COMPL (FDOM h))))) /\
                DISJOINT (FDOM h1') (FDOM h')’ by (
                  ASM_SIMP_TAC std_ss [FDOM_FUNION, DISJOINT_UNION_BOTH] THEN
                  Q.PAT_X_ASSUM ‘!x. x IN FDOM h' ==> P x’ MP_TAC THEN
                  Q.PAT_X_ASSUM ‘DISJOINT (FDOM h1) (FDOM h2)’ MP_TAC THEN
                  Q.PAT_X_ASSUM ‘DISJOINT (FDOM h1') (FDOM h2)’ MP_TAC THEN
                  REPEAT (POP_ASSUM (K ALL_TAC)) THEN

                  SIMP_TAC std_ss [SUBMAP_DEF, DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY,
                     DRESTRICT_DEF] THEN
                  METIS_TAC[]
               ) THEN
               ASM_SIMP_TAC std_ss [FUNION_EQ]
            ]
         ],



         POP_ASSUM MP_TAC THEN
         ASM_SIMP_TAC std_ss [MEM_EL, REPLACE_ELEMENT_SEM] THEN
         STRIP_TAC THEN
         ASM_SIMP_TAC std_ss [REPLACE_ELEMENT_SEM] THEN
         Cases_on ‘n'''' = nx’ THENL [
            ASM_SIMP_TAC std_ss [] THEN
            Q.PAT_X_ASSUM ‘DISJOINT (FDOM h1') (FDOM h2)’ MP_TAC THEN
            Q.PAT_X_ASSUM ‘hx SUBMAP h2’ MP_TAC THEN
            REPEAT (POP_ASSUM (K ALL_TAC)) THEN

            SIMP_TAC std_ss [SUBMAP_DEF, DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY,
               DRESTRICT_DEF, FUNION_DEF, IN_UNION, DISJ_IMP_THM],


            ASM_SIMP_TAC std_ss [] THEN
            ‘EL n'''' hL SUBMAP h2’ by METIS_TAC[MEM_EL] THEN
            POP_ASSUM MP_TAC THEN
            Q.PAT_X_ASSUM ‘DISJOINT (FDOM h1') (FDOM h2)’ MP_TAC THEN
            REPEAT (POP_ASSUM (K ALL_TAC)) THEN

            SIMP_TAC std_ss [SUBMAP_DEF, DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY,
               FUNION_DEF, IN_UNION, DISJ_IMP_THM] THEN
            METIS_TAC[]
         ],


         Cases_on ‘n'''' = nx’ THENL [
            ASM_SIMP_TAC std_ss [] THEN
            METIS_TAC[SF_SEM___sf_tree_len_THM],

            ASM_SIMP_TAC std_ss [] THEN
            METIS_TAC[SF_SEM___sf_tree_len_THM]
         ],


         Q.EXISTS_TAC ‘(FUNION h1' hx)’ THEN
         ASM_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION, MEM_EL] THEN
         Q.EXISTS_TAC ‘nx’ THEN
         ASM_SIMP_TAC std_ss [REPLACE_ELEMENT_SEM] THEN
         METIS_TAC[],


         ‘x IN FDOM (FOLDR FUNION FEMPTY hL)’ by (
            ASM_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE, FDOM_FUNION, IN_UNION]
         ) THEN
         ‘?h. MEM h hL /\ x IN FDOM h’ by (
            POP_ASSUM MP_TAC THEN
            REPEAT (POP_ASSUM (K ALL_TAC)) THEN

            Induct_on ‘hL’ THENL [
               SIMP_TAC list_ss [FDOM_FEMPTY, NOT_IN_EMPTY],

               SIMP_TAC list_ss [FDOM_FEMPTY, NOT_IN_EMPTY, FDOM_FUNION, IN_UNION] THEN
               METIS_TAC[]
            ]
         ) THEN
         ‘?n1. (n1 < LENGTH hL) /\ (h = EL n1 hL)’ by METIS_TAC[MEM_EL] THEN
         Cases_on ‘n1 = nx’ THENL [
            Q.EXISTS_TAC ‘(FUNION h1' hx)’ THEN
            Q.PAT_X_ASSUM ‘x IN FDOM h’ MP_TAC THEN
            ‘~(x IN FDOM h1)’ by (
               FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
               METIS_TAC[]
            ) THEN
            ASM_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION, MEM_EL] THEN
            STRIP_TAC THEN
            Q.EXISTS_TAC ‘nx’ THEN
            ASM_SIMP_TAC std_ss [REPLACE_ELEMENT_SEM] THEN
            METIS_TAC[],


            Q.EXISTS_TAC ‘EL n1 hL’ THEN
            CONJ_TAC THENL [
               REWRITE_TAC[MEM_EL] THEN
               Q.EXISTS_TAC ‘n1’ THEN
               ASM_SIMP_TAC std_ss [REPLACE_ELEMENT_SEM] THEN
               METIS_TAC[],

               METIS_TAC[]
            ]
         ]
      ]
   ],



   FULL_SIMP_TAC std_ss [GSYM sf_ls_def] THEN

   MP_TAC (
      Q.SPECL [‘s’, ‘FUNION h1 (h2:('b, 'c) heap)’, ‘h1’, ‘f’, ‘e’, ‘e2'’, ‘e1'’, ‘es’] LEMMA_29) THEN
   ASM_SIMP_TAC std_ss [SUBMAP___FUNION___ID] THEN
   SIMP_TAC std_ss [SF_SEM___STAR_THM, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      FDOM_FUNION, DISJOINT_UNION_BOTH] THEN
   REPEAT STRIP_TAC THEN

   ‘h1''' = h1’ by (
      ‘SF_IS_PRECISE (sf_ls f e2' e1')’ by REWRITE_TAC[SF_IS_PRECISE_THM] THEN
      FULL_SIMP_TAC std_ss [SF_IS_PRECISE_def] THEN
      POP_ASSUM MATCH_MP_TAC THEN
      Q.EXISTS_TAC ‘s’ THEN
      Q.EXISTS_TAC ‘FUNION h1 h2’ THEN
      REWRITE_TAC [SUBMAP___FUNION___ID] THEN
      ASM_SIMP_TAC std_ss [SUBMAP___FUNION_EQ, SUBMAP___FUNION___ID]
   ) THEN
   ‘h2 = FUNION h1'' h2''’ by (
      Q.PAT_X_ASSUM ‘FUNION h1 h2 = Y’  MP_TAC THEN
      ‘FUNION h1'' (FUNION h1''' h2'') =
       FUNION h1''' (FUNION h1'' h2'')’ by METIS_TAC[FUNION___COMM, FUNION___ASSOC] THEN
     ‘ DISJOINT (FDOM h1) (FDOM (FUNION h1'' h2''))’ by (
       FULL_SIMP_TAC std_ss [FDOM_FUNION, DISJOINT_SYM, DISJOINT_UNION_BOTH]
     ) THEN
     METIS_TAC [FUNION_EQ]
   ) THEN
   Q.PAT_X_ASSUM ‘FUNION h1 h2 = Y’ (K ALL_TAC) THEN
   FULL_SIMP_TAC std_ss [FDOM_FUNION, DISJOINT_UNION_BOTH] THEN

   ‘SF_SEM s (FUNION h1'' h1') (sf_ls f e e1')’ by (
      ‘DS_POINTER_DANGLES s h1'' e1'’ by (
         ‘~DS_POINTER_DANGLES s h2'' e1'’ by METIS_TAC[SF_SEM___sf_ls___ROOT_DANGLES,
            DS_EXPRESSION_EQUAL_def] THEN

         FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
         METIS_TAC[]
      ) THEN

      MATCH_MP_TAC LEMMA_25 THEN
      Q.EXISTS_TAC ‘e2'’ THEN
      ASM_SIMP_TAC std_ss []
   ) THEN

   ‘SF_SEM s (FUNION (FUNION h1'' h1') h2'') (sf_ls f e es)’ by (
      MATCH_MP_TAC LEMMA_25 THEN
      Q.EXISTS_TAC ‘e1'’ THEN
      FULL_SIMP_TAC std_ss [DISJOINT_UNION_BOTH, FDOM_FUNION, DISJOINT_SYM] THEN

      ‘DS_POINTER_DANGLES s (FUNION h1 (FUNION h1'' h2'')) es’ by METIS_TAC[LEMMA_3_1_1___sf_ls] THEN
      POP_ASSUM MP_TAC THEN
      Q.PAT_X_ASSUM ‘DS_POINTER_DANGLES s h1' es’ MP_TAC THEN
      SIMP_TAC std_ss [DS_POINTER_DANGLES, FDOM_FUNION, IN_UNION, DISJ_IMP_THM]
   ) THEN
   ‘FUNION h1' (FUNION h1'' h2'') =  FUNION (FUNION h1'' h1') h2''’ by METIS_TAC[FUNION___COMM, FUNION___ASSOC] THEN
   METIS_TAC[]
]);




val BALANCED_SF_SEM___sf_tree_len___MODEL_EXISTS = store_thm ("BALANCED_SF_SEM___sf_tree_len___MODEL_EXISTS",
   “!s fL n es e X. ((FINITE (X:'b set)) /\ INFINITE (UNIV:'b set) /\
         (ALL_DISTINCT fL) /\
         ((n = 0) ==> DS_EXPRESSION_EQUAL s es e) /\
         (~(n = 0) ==> (
            ~DS_EXPRESSION_EQUAL s es e /\
            ~IS_DSV_NIL (DS_EXPRESSION_EVAL s e)))) ==>
      (?h. (BALANCED_SF_SEM___sf_tree_len s h fL n es e) /\
           (!h'. h' IN (FRANGE h) ==> (FDOM h' = LIST_TO_SET fL)) /\
          (DISJOINT (FDOM h DIFF (
               if IS_DSV_NIL(DS_EXPRESSION_EVAL s e) then {} else
                  {DS_EXPRESSION_EVAL_VALUE s e})) X))”,


Cases_on ‘n’ THENL [
   SIMP_TAC std_ss [BALANCED_SF_SEM___sf_tree_len_def, FDOM_FEMPTY, EMPTY_DIFF, DISJOINT_EMPTY,
         DS_EXPRESSION_EQUAL_def, PF_SEM_def, FRANGE_FEMPTY, NOT_IN_EMPTY],

   SIMP_TAC arith_ss [] THEN
   Induct_on ‘n'’ THENL [
      REWRITE_TAC [BALANCED_SF_SEM___sf_tree_len_def] THEN
      SIMP_TAC list_ss [PF_SEM_def, DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def] THEN
      REPEAT STRIP_TAC THEN
      Q.EXISTS_TAC ‘FEMPTY |+ (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e),
         FUN_FMAP (\x. DS_EXPRESSION_EVAL s es) (LIST_TO_SET fL))’ THEN

      ASM_SIMP_TAC std_ss [FDOM_FUPDATE, DISJOINT_DEF, IN_INSERT, EXTENSION, NOT_IN_EMPTY,
         IN_DIFF, IN_INSERT, IN_INTER, FDOM_FEMPTY, DS_EXPRESSION_EVAL_VALUE_def,
         FRANGE_FUPDATE, DRESTRICT_FEMPTY, FRANGE_FEMPTY, NOT_IN_EMPTY,
         FUN_FMAP_DEF, FINITE_LIST_TO_SET] THEN

      Q.EXISTS_TAC ‘MAP (\x. FEMPTY) fL’ THEN
      ASM_SIMP_TAC list_ss [MAP_MAP_o, combinTheory.o_DEF, FDOM_FEMPTY,
         DOMSUB_FUPDATE, DOMSUB_FEMPTY, EVERY_MEM, MEM_ZIP, EL_MAP, GSYM LEFT_FORALL_IMP_THM,
         HEAP_READ_ENTRY_def, FDOM_FUPDATE, IN_SING,
         FAPPLY_FUPDATE_THM, FUN_FMAP_DEF, FINITE_LIST_TO_SET, EL_IS_EL,
         MEM_MAP] THEN

      Induct_on ‘fL’ THENL [
         SIMP_TAC list_ss [ALL_DISJOINT_def],

         ASM_SIMP_TAC list_ss [ALL_DISJOINT_def, FUNION_FEMPTY_1, EVERY_MEM,
            DISJOINT_EMPTY]
      ],




      REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC [BALANCED_SF_SEM___sf_tree_len_def] THEN
      FULL_SIMP_TAC std_ss [PF_SEM_def, DS_EXPRESSION_EQUAL_def] THEN

      ‘?fL'. (ALL_DISTINCT fL') /\
             (!x. MEM x fL ==> MEM x fL') /\
             (LIST_TO_SET fL = LIST_TO_SET fL') /\
             (!s h. BALANCED_SF_SEM___sf_tree_len s h fL =
                    BALANCED_SF_SEM___sf_tree_len s h fL')’ by METIS_TAC[] THEN
      ASM_REWRITE_TAC[] THEN
      NTAC 2 (POP_ASSUM (fn thm => ALL_TAC)) THEN
      Induct_on ‘fL’ THENL [
         SIMP_TAC list_ss [LENGTH_NIL, ALL_DISJOINT_def] THEN
         Q.EXISTS_TAC ‘FEMPTY |+ (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e),
            FUN_FMAP (\x. dsv_nil) (LIST_TO_SET fL'))’ THEN
         ASM_SIMP_TAC list_ss [FDOM_FUPDATE, IN_INSERT, DOMSUB_FUPDATE, DOMSUB_FEMPTY,
            DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_DIFF, FDOM_FEMPTY,
            DS_EXPRESSION_EVAL_VALUE_def, FRANGE_FUPDATE, FRANGE_FEMPTY, DRESTRICT_FEMPTY,
            FUN_FMAP_DEF, FINITE_LIST_TO_SET],




         FULL_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
         REPEAT STRIP_TAC THEN
         FULL_SIMP_TAC list_ss [] THEN

         ‘?c. ~(c IN ((DS_EXPRESSION_EVAL_VALUE s es) INSERT (X UNION (FDOM (h':('b, 'c) heap)))))’ by (
            MATCH_MP_TAC
               (REWRITE_RULE [IN_UNIV] (Q.SPEC ‘UNIV’ IN_INFINITE_NOT_FINITE)) THEN
            ASM_SIMP_TAC std_ss [FINITE_UNION, FDOM_FINITE, FINITE_INSERT]
         ) THEN


         Q.PAT_X_ASSUM ‘!s' fL'. P s' fL'’ (fn thm => (
            MP_TAC (Q.SPECL [‘s’, ‘fL'’, ‘es’, ‘dse_const (dsv_const c)’, ‘X UNION
            (FDOM (h':('b, 'c) heap))’] thm))) THEN
         MATCH_MP_TAC (prove (“(a /\ (b ==> c)) ==> ((a ==> b) ==> c)”, METIS_TAC[])) THEN
         CONJ_TAC THEN1 (
            FULL_SIMP_TAC list_ss [FINITE_UNION, FDOM_FINITE,
               DS_EXPRESSION_EVAL_def, IS_DSV_NIL_def,
               DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
               IN_INSERT, IN_UNION, DS_EXPRESSION_EVAL_VALUE_def] THEN
            Cases_on ‘DS_EXPRESSION_EVAL s es’ THENL [
               SIMP_TAC std_ss [ds_value_distinct],
               FULL_SIMP_TAC std_ss [ds_value_11, GET_DSV_VALUE_def]
            ]
         ) THEN

         SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def, DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def,
            GSYM LEFT_EXISTS_AND_THM] THEN
         STRIP_TAC THEN
         ‘?h''''. h'''' = ((FUNION h' h'') |+
            (DS_EXPRESSION_EVAL_VALUE s e,
             (h' ' (DS_EXPRESSION_EVAL_VALUE s e)) |+ (h, dsv_const c)))’ by METIS_TAC[] THEN

         Q.EXISTS_TAC ‘h''''’ THEN
         Q.EXISTS_TAC ‘h''::hL’ THEN

         ASM_SIMP_TAC list_ss [FDOM_FUPDATE, IN_INSERT, DS_EXPRESSION_EVAL_VALUE_def,
            HEAP_READ_ENTRY_THM, FAPPLY_FUPDATE_THM, ALL_DISJOINT_def] THEN

         REPEAT STRIP_TAC THENL [
            Q.PAT_X_ASSUM ‘EVERY IS_SOME Z’ MP_TAC THEN
            SIMP_TAC std_ss [EVERY_MEM, MEM_MAP,
               GSYM LEFT_FORALL_IMP_THM, HEAP_READ_ENTRY_THM,
               FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE_THM] THEN
            METIS_TAC[],

            ‘DISJOINT (FDOM h'') (FDOM (FOLDR FUNION FEMPTY hL))’ suffices_by (STRIP_TAC THEN
               POP_ASSUM MP_TAC THEN
               REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
               Induct_on ‘hL’ THENL [
                  SIMP_TAC list_ss [],
                  FULL_SIMP_TAC list_ss [FUNION_DEF, DISJOINT_UNION_BOTH, DISJOINT_SYM]
               ]
            ) THEN
            FULL_SIMP_TAC list_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
               FDOM_DOMSUB, IN_DELETE, IN_DIFF, IN_SING, IN_UNION, DS_EXPRESSION_EVAL_VALUE_def,
               IN_INSERT] THEN
            METIS_TAC[],


            ASM_SIMP_TAC std_ss [DOMSUB_FUPDATE, DOMSUB_FUNION] THEN
            ‘h'' \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) = h''’ by (
               FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM, IN_INSERT, IN_UNION,
                  FDOM_DOMSUB, EXTENSION, IN_DELETE, DOMSUB_FAPPLY_THM,
                  DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
                  IN_DIFF] THEN
               METIS_TAC[]
            ) THEN
            ASM_REWRITE_TAC[] THEN

            MATCH_MP_TAC FUNION___COMM THEN
            FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
               FDOM_DOMSUB, IN_DELETE, IN_INSERT, IN_UNION, IN_SING, IN_DIFF] THEN
            METIS_TAC[],


            ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_def, FDOM_FUPDATE, IN_INSERT,
               FAPPLY_FUPDATE_THM],


            ‘(MAP (HEAP_READ_ENTRY s h' e) fL) =
                               (MAP (HEAP_READ_ENTRY s h'''' e) fL)’ suffices_by (STRIP_TAC THEN

               Q.PAT_X_ASSUM ‘h'''' = XXX’ (MP_TAC o GSYM) THEN
               FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def]
            ) THEN
            ASM_SIMP_TAC std_ss [MAP_EQ_f] THEN
            REPEAT STRIP_TAC THEN
            ‘IS_SOME (HEAP_READ_ENTRY s h' e e')’ by (
               FULL_SIMP_TAC std_ss [EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM]
            ) THEN
            FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM] THEN
            ‘~(e' = h)’ by METIS_TAC[] THEN
            ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_def, FDOM_FUPDATE,
               DS_EXPRESSION_EVAL_VALUE_def, IN_INSERT, FAPPLY_FUPDATE_THM],


            Q.PAT_X_ASSUM ‘h''' IN FRANGE Y’ MP_TAC THEN
            ASM_SIMP_TAC list_ss [FRANGE_DEF, GSPECIFICATION] THEN
            HO_MATCH_MP_TAC (prove (“(!x. P x ==> (Q x ==> Y)) ==>
                                      ((?x. (P x /\ Q x)) ==> Y)”, METIS_TAC[])) THEN
            SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT] THEN
            HO_MATCH_MP_TAC (prove (“((!x. (P1 x ==> Q x)) /\
                                      (!x. (~P1 x /\ P2 x) ==> Q x)) ==>
                                      (!x. (P1 x \/ P2 x) ==> Q x)”, METIS_TAC[])) THEN
            SIMP_TAC std_ss [FAPPLY_FUPDATE_THM, FUNION_DEF, IN_UNION] THEN
            SIMP_TAC std_ss [Once EQ_SYM_EQ] THEN
            FULL_SIMP_TAC std_ss [FRANGE_DEF, GSPECIFICATION, GSYM LEFT_FORALL_IMP_THM] THEN

            CONJ_TAC THENL [
               ASM_SIMP_TAC list_ss [FDOM_FUPDATE, EXTENSION, IN_INSERT] THEN
               METIS_TAC[],

               METIS_TAC[]
            ],


            FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, DISJOINT_DEF,
               NOT_IN_EMPTY, IN_INSERT, IN_DIFF, FUNION_DEF, IN_UNION, DS_EXPRESSION_EVAL_VALUE_def] THEN
            METIS_TAC[]
         ]
      ]
   ]
]);



val BALANCED_SF_SEM___sf_tree_len_1___MODEL_SIZE = store_thm ("BALANCED_SF_SEM___sf_tree_len_1___MODEL_SIZE",
   “!s h fL es e. BALANCED_SF_SEM___sf_tree_len s h fL 1 es e ==>
                   (~(IS_DSV_NIL (DS_EXPRESSION_EVAL s e)) /\
                   (FDOM h = {DS_EXPRESSION_EVAL_VALUE s e}))”,

   REWRITE_TAC [ONE, BALANCED_SF_SEM___sf_tree_len_def] THEN
   REPEAT STRIP_TAC THEN
   ‘FOLDR FUNION FEMPTY hL = FEMPTY’ suffices_by (STRIP_TAC THEN
      FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FEMPTY, NOT_IN_EMPTY, EXTENSION,
         FDOM_DOMSUB, SING_DEF, IN_SING, IN_DELETE, DS_EXPRESSION_EVAL_VALUE_def] THEN
      METIS_TAC[]
   ) THEN
   ‘EVERY (\h. h = FEMPTY) hL’ suffices_by (STRIP_TAC THEN
      POP_ASSUM MP_TAC THEN
      REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
      Induct_on ‘hL’ THENL [
         SIMP_TAC list_ss [],
         ASM_SIMP_TAC list_ss [FUNION_FEMPTY_1]
      ]
   ) THEN
   Q.PAT_X_ASSUM ‘EVERY X (ZIP (cL,hL))’ MP_TAC THEN
   ASM_SIMP_TAC std_ss [EVERY_MEM, MEM_ZIP, GSYM LEFT_FORALL_IMP_THM] THEN
   METIS_TAC[MEM_EL]
)




val BALANCED_SF_SEM___sf_tree_len_2___MODEL_EXISTS = store_thm ("BALANCED_SF_SEM___sf_tree_len_2___MODEL_EXISTS",
“!s fL es e X. ((FINITE (X:'b set)) /\ INFINITE (UNIV:'b set) /\
         (ALL_DISTINCT fL) /\ ~(IS_DSV_NIL (DS_EXPRESSION_EVAL s e)) /\
         ~(DS_EXPRESSION_EQUAL s es e)) ==>

(?h2:('b, 'c) heap hl:('b, 'c) heap.
   (BALANCED_SF_SEM___sf_tree_len s (FUNION h2 hl) fL 2 es e) /\
   (FDOM h2 = {DS_EXPRESSION_EVAL_VALUE s e}) /\
   ((FDOM hl = EMPTY) = (fL = [])) /\
   (DISJOINT (FDOM hl) (FDOM h2)) /\
   (DISJOINT (FDOM hl) X) /\
   (!x. x IN FDOM hl ==> (FDOM (hl ' x) = LIST_TO_SET fL)) /\
   (FDOM (h2 ' (DS_EXPRESSION_EVAL_VALUE s e)) = LIST_TO_SET fL) /\

   (!x. ((?f. MEM f fL /\ (HEAP_READ_ENTRY s h2 e f = SOME (dsv_const x))) =
         (x IN FDOM hl))) /\
   (!x f. MEM f fL /\ (x IN FDOM hl) ==> (HEAP_READ_ENTRY s hl (dse_const (dsv_const x)) f =
                  SOME (DS_EXPRESSION_EVAL s es))) /\
   (!f. MEM f fL ==> ?x. x IN FDOM hl /\
                         (h2 ' (DS_EXPRESSION_EVAL_VALUE s e) ' f = dsv_const x)) /\
   (!f1 f2. MEM f1 fL /\ MEM f2 fL ==> (((h2 ' (DS_EXPRESSION_EVAL_VALUE s e) ' f1) =
                                        (h2 ' (DS_EXPRESSION_EVAL_VALUE s e) ' f2)) =
                                        (f1 = f2))))
”,


REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [‘s’, ‘fL’, ‘2’, ‘es’, ‘e’, ‘X’] BALANCED_SF_SEM___sf_tree_len___MODEL_EXISTS) THEN
ASM_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN
‘?h2. h2 = DRESTRICT h {DS_EXPRESSION_EVAL_VALUE s e}’ by METIS_TAC[] THEN
‘?hl. hl = h \\ (DS_EXPRESSION_EVAL_VALUE s e)’ by METIS_TAC[] THEN
Q.EXISTS_TAC ‘h2’ THEN
Q.EXISTS_TAC ‘hl’ THEN
REPEAT STRIP_TAC THENL [
   ‘FUNION h2 hl = h’ suffices_by METIS_TAC[]    THEN
   ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FUNION_DEF,
      DRESTRICT_DEF, IN_INTER, IN_UNION, FDOM_DOMSUB, IN_DELETE, IN_SING,
      DISJ_IMP_THM, DOMSUB_FAPPLY_THM] THEN
   METIS_TAC[],


   Q.PAT_X_ASSUM ‘BALANCED_SF_SEM___sf_tree_len s h fL 2 es e’ MP_TAC THEN
   REWRITE_TAC [TWO, BALANCED_SF_SEM___sf_tree_len_def] THEN
   ASM_SIMP_TAC std_ss [EXTENSION, DRESTRICT_DEF, IN_INTER, IN_SING,
      DS_EXPRESSION_EVAL_VALUE_def] THEN
   METIS_TAC[],


   EQ_TAC THEN STRIP_TAC THENL [
      CCONTR_TAC THEN
      Q.PAT_X_ASSUM ‘BALANCED_SF_SEM___sf_tree_len s h fL 2 es e’ MP_TAC THEN
      REWRITE_TAC [TWO, BALANCED_SF_SEM___sf_tree_len_def] THEN
      FULL_SIMP_TAC list_ss [PF_SEM_def, DS_EXPRESSION_EQUAL_def] THEN
      Cases_on ‘fL’ THEN FULL_SIMP_TAC std_ss [] THEN
      Cases_on ‘hL’ THEN FULL_SIMP_TAC list_ss [] THEN
      REWRITE_TAC [prove (“(a \/ b) = (~a ==> b)”, METIS_TAC[])] THEN
      REPEAT STRIP_TAC THEN
      ‘?x. FDOM h'' = {x}’ by METIS_TAC[BALANCED_SF_SEM___sf_tree_len_1___MODEL_SIZE] THEN
      FULL_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, NOT_IN_EMPTY, FDOM_DOMSUB, IN_DELETE, IN_SING,
         FUNION_DEF, IN_UNION, DS_EXPRESSION_EVAL_VALUE_def] THEN
      METIS_TAC[],


      Q.PAT_X_ASSUM ‘BALANCED_SF_SEM___sf_tree_len s h fL 2 es e’ MP_TAC THEN
      REWRITE_TAC [TWO, BALANCED_SF_SEM___sf_tree_len_def] THEN
      FULL_SIMP_TAC list_ss [PF_SEM_def, DS_EXPRESSION_EQUAL_def,
         LENGTH_NIL, DS_EXPRESSION_EVAL_VALUE_def,
         EXTENSION, GSYM fmap_EQ_THM, FDOM_FEMPTY, NOT_IN_EMPTY]
   ],


   ASM_REWRITE_TAC[] THEN
   SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
      FDOM_DOMSUB, IN_DELETE, DRESTRICT_DEF, IN_SING],


   FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
      FDOM_DOMSUB, IN_DELETE, IN_DIFF, IN_SING],

   Q.PAT_X_ASSUM ‘x IN FDOM hl’ MP_TAC THEN
   FULL_SIMP_TAC std_ss [FRANGE_DEF, GSPECIFICATION, GSYM LEFT_FORALL_IMP_THM,
      FDOM_DOMSUB, IN_DELETE, DOMSUB_FAPPLY_THM],


   FULL_SIMP_TAC std_ss [FRANGE_DEF, GSPECIFICATION, GSYM LEFT_FORALL_IMP_THM,
      FDOM_DOMSUB, IN_DELETE, DOMSUB_FAPPLY_THM, DRESTRICT_DEF, IN_INTER, IN_SING] THEN
   ‘DS_EXPRESSION_EVAL_VALUE s e IN FDOM h’ suffices_by (STRIP_TAC THEN
      ASM_SIMP_TAC std_ss []
   ) THEN
   Q.PAT_X_ASSUM ‘BALANCED_SF_SEM___sf_tree_len s h fL 2 es e’ MP_TAC THEN
   REWRITE_TAC [TWO, BALANCED_SF_SEM___sf_tree_len_def,
      DS_EXPRESSION_EVAL_VALUE_def] THEN
   METIS_TAC[],


   Q.PAT_X_ASSUM ‘BALANCED_SF_SEM___sf_tree_len s h fL 2 es e’ MP_TAC THEN
   REWRITE_TAC [TWO, BALANCED_SF_SEM___sf_tree_len___EXTENDED_DEF] THEN
   ASM_SIMP_TAC list_ss [HEAP_READ_ENTRY_THM, FDOM_DOMSUB, IN_DELETE, DRESTRICT_DEF,
      IN_INTER, IN_SING, DS_EXPRESSION_EVAL_VALUE_def, RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM] THEN
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL [
      STRIP_TAC THEN
      ‘?n h'. n < LENGTH hL /\ (EL n hL = h') /\ (EL n fL = f) /\ (MEM h' hL)’ by METIS_TAC[MEM_EL] THEN
      ‘BALANCED_SF_SEM___sf_tree_len s h' fL 1 es (dse_const (dsv_const x))’ by METIS_TAC[] THEN
      ‘FDOM h' = {DS_EXPRESSION_EVAL_VALUE s (dse_const (dsv_const x))}’ by METIS_TAC[
         BALANCED_SF_SEM___sf_tree_len_1___MODEL_SIZE] THEN
      FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def, DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def] THEN
      CONJ_TAC THEN1 (
         METIS_TAC[IN_SING, SUBMAP_DEF]
      ) THEN
      ‘~((GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)) IN FDOM (FOLDR FUNION FEMPTY hL))’ by (
         ASM_REWRITE_TAC[FDOM_DOMSUB, IN_DELETE, DS_EXPRESSION_EVAL_VALUE_def]
      ) THEN
      ‘x IN FDOM (FOLDR FUNION FEMPTY hL)’ suffices_by METIS_TAC[] THEN

      Q.PAT_X_ASSUM ‘FDOM h' = Y’ MP_TAC THEN
      Q.PAT_X_ASSUM ‘MEM h' hL’ MP_TAC THEN
      REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
      Induct_on ‘hL’ THENL [
         SIMP_TAC list_ss [],
         ASM_SIMP_TAC list_ss [FDOM_FUNION, IN_UNION, DISJ_IMP_THM, IN_SING]
      ],

      Cases_on ‘DS_EXPRESSION_EVAL s e’ THEN FULL_SIMP_TAC std_ss [IS_DSV_NIL_def, GET_DSV_VALUE_def,
         ds_value_11] THEN
      STRIP_TAC THEN
      ‘?h'. MEM h' hL /\ x IN FDOM h'’ by METIS_TAC[] THEN
      ‘?n f. (n < LENGTH hL) /\ (EL n fL = f) /\ MEM f fL /\ (EL n hL = h')’ by METIS_TAC[MEM_EL] THEN
      Q.EXISTS_TAC ‘f’ THEN
      ASM_SIMP_TAC std_ss [] THEN
      ‘BALANCED_SF_SEM___sf_tree_len s h' fL 1 es (dse_const (h ' v ' f))’ by METIS_TAC[] THEN
      ‘~(IS_DSV_NIL (DS_EXPRESSION_EVAL s (dse_const (h ' v ' f)))) /\
       (FDOM h' = {DS_EXPRESSION_EVAL_VALUE s (dse_const (h ' v ' f))})’ by METIS_TAC[
         BALANCED_SF_SEM___sf_tree_len_1___MODEL_SIZE] THEN
      FULL_SIMP_TAC std_ss [IN_SING, DS_EXPRESSION_EVAL_VALUE_def, DS_EXPRESSION_EVAL_def,
         dsv_const_GET_DSV_VALUE]
   ],


   Q.PAT_X_ASSUM ‘BALANCED_SF_SEM___sf_tree_len s h fL 2 es e’ MP_TAC THEN
   REWRITE_TAC [TWO, BALANCED_SF_SEM___sf_tree_len___EXTENDED_DEF] THEN
   ASM_SIMP_TAC list_ss [HEAP_READ_ENTRY_THM, FDOM_DOMSUB, IN_DELETE, DRESTRICT_DEF,
      IN_INTER, IN_SING, DS_EXPRESSION_EVAL_VALUE_def, RIGHT_EXISTS_AND_THM, LEFT_EXISTS_AND_THM,
      DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def, DOMSUB_FAPPLY_THM, IS_DSV_NIL_def] THEN
   STRIP_TAC THEN
   Q.PAT_X_ASSUM ‘x IN FDOM hl’ MP_TAC THEN
   ASM_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE, DS_EXPRESSION_EVAL_VALUE_def] THEN
   Cases_on ‘DS_EXPRESSION_EVAL s e’ THEN FULL_SIMP_TAC std_ss [IS_DSV_NIL_def, GET_DSV_VALUE_def,
      ds_value_11] THEN
   STRIP_TAC THEN
   ‘?h'. MEM h' hL /\ x IN FDOM h'’ by METIS_TAC[] THEN
   ‘?n f. (n < LENGTH hL) /\ (EL n fL = f) /\ MEM f fL /\ (EL n hL = h')’ by METIS_TAC[MEM_EL] THEN
   ‘BALANCED_SF_SEM___sf_tree_len s h' fL 1 es
               (dse_const (h ' v ' f'))’ by METIS_TAC[] THEN
   ‘~(IS_DSV_NIL (DS_EXPRESSION_EVAL s (dse_const (h ' v ' f')))) /\
       (FDOM h' = {DS_EXPRESSION_EVAL_VALUE s (dse_const (h ' v ' f'))})’ by METIS_TAC[
         BALANCED_SF_SEM___sf_tree_len_1___MODEL_SIZE] THEN
   Q.PAT_X_ASSUM ‘BALANCED_SF_SEM___sf_tree_len s h' fL 1 es Y’ MP_TAC THEN
   REWRITE_TAC [ONE, BALANCED_SF_SEM___sf_tree_len___EXTENDED_DEF] THEN
   FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def,
      IN_SING, DS_EXPRESSION_EVAL_VALUE_def, HEAP_READ_ENTRY_THM] THEN
   ‘(h ' v ' f') = dsv_const x’ by (
      Cases_on ‘h ' v ' f'’ THEN
      FULL_SIMP_TAC std_ss [IS_DSV_NIL_def, GET_DSV_VALUE_def]
   ) THEN
   FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def] THEN
   STRIP_TAC THEN
   ‘h ' x = h' ' x’ by (
      METIS_TAC[SUBMAP_DEF, IN_SING]
   ) THEN
   ‘?m. m < LENGTH fL /\ (EL m fL = f)’ by METIS_TAC[MEM_EL] THEN
   METIS_TAC[],


   Q.PAT_X_ASSUM ‘BALANCED_SF_SEM___sf_tree_len s h fL 2 es e’ MP_TAC THEN
   REWRITE_TAC [TWO, BALANCED_SF_SEM___sf_tree_len___EXTENDED_DEF] THEN
   FULL_SIMP_TAC list_ss [PF_SEM_def, DS_EXPRESSION_EQUAL_def] THEN
   STRIP_TAC THEN
   ‘?n. (n < LENGTH hL) /\ (EL n fL = f)’ by METIS_TAC[MEM_EL] THEN
   ‘BALANCED_SF_SEM___sf_tree_len s (EL n hL) fL 1 es
               (dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)) '  f))’ by METIS_TAC[] THEN
   ‘(FDOM (EL n hL) = {DS_EXPRESSION_EVAL_VALUE s (dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)) '  f))}) /\
    ~IS_DSV_NIL (DS_EXPRESSION_EVAL s (dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)) '  f)))’ by METIS_TAC[BALANCED_SF_SEM___sf_tree_len_1___MODEL_SIZE] THEN
   FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, NOT_IS_DSV_NIL_THM] THEN
   Q.PAT_X_ASSUM ‘Y = dsv_const c’ ASSUME_TAC THEN
   FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def, DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def,
      DRESTRICT_DEF, IN_INTER, IN_SING] THEN
   Q.EXISTS_TAC ‘c'’ THEN
   Q.PAT_X_ASSUM ‘Y = h \\ c’ (fn thm => REWRITE_TAC [GSYM thm]) THEN
   ‘?h'. (MEM h' hL) /\ (FDOM h' = {c'})’ by METIS_TAC[MEM_EL] THEN
   NTAC 2 (POP_ASSUM MP_TAC) THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN
   Induct_on ‘hL’ THENL [
      SIMP_TAC list_ss [],
      SIMP_TAC list_ss [FUNION_DEF, IN_UNION, DISJ_IMP_THM, IN_SING] THEN
      METIS_TAC[]
   ],


   Q.PAT_X_ASSUM ‘BALANCED_SF_SEM___sf_tree_len s h fL 2 es e’ MP_TAC THEN
   REWRITE_TAC [TWO, BALANCED_SF_SEM___sf_tree_len___EXTENDED_DEF] THEN
   FULL_SIMP_TAC list_ss [PF_SEM_def, DS_EXPRESSION_EQUAL_def, DRESTRICT_DEF,
      IN_INTER, IN_SING, DS_EXPRESSION_EVAL_VALUE_def] THEN
   STRIP_TAC THEN
   ASM_SIMP_TAC std_ss [] THEN
   Cases_on ‘f1 = f2’ THEN ASM_REWRITE_TAC[] THEN
   ‘?n1. (n1 < LENGTH hL) /\ (EL n1 fL = f1)’ by METIS_TAC[MEM_EL] THEN
   ‘?n2. (n2 < LENGTH hL) /\ (EL n2 fL = f2)’ by METIS_TAC[MEM_EL] THEN
   ‘~(n1 = n2)’ by METIS_TAC[EL_ALL_DISTINCT_EQ] THEN
   ‘(BALANCED_SF_SEM___sf_tree_len s (EL n1 hL) fL 1 es
               (dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)) ' (EL n1 fL)))) /\
    (BALANCED_SF_SEM___sf_tree_len s (EL n2 hL) fL 1 es
               (dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)) ' (EL n2 fL))))’ by METIS_TAC[] THEN
   ‘(FDOM (EL n1 hL) = {DS_EXPRESSION_EVAL_VALUE s (dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)) '  f1))}) /\
    ~IS_DSV_NIL (DS_EXPRESSION_EVAL s (dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)) '  f1)))’ by METIS_TAC[BALANCED_SF_SEM___sf_tree_len_1___MODEL_SIZE] THEN
   ‘(FDOM (EL n2 hL) = {DS_EXPRESSION_EVAL_VALUE s (dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)) '  f2))}) /\
    ~IS_DSV_NIL (DS_EXPRESSION_EVAL s (dse_const (h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e)) '  f2)))’ by METIS_TAC[BALANCED_SF_SEM___sf_tree_len_1___MODEL_SIZE] THEN
   ‘DISJOINT (FDOM (EL n1 hL)) (FDOM (EL n2 hL))’ by (
      FULL_SIMP_TAC list_ss [EL_ALL_DISJOINT_EQ, EL_MAP] THEN
      METIS_TAC[NOT_EMPTY_SING]
   ) THEN
   POP_ASSUM MP_TAC THEN

   FULL_SIMP_TAC std_ss [NOT_IS_DSV_NIL_THM, DS_EXPRESSION_EVAL_def,
      DS_EXPRESSION_EVAL_VALUE_def, GET_DSV_VALUE_def, ds_value_11] THEN
   SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, IN_SING, NOT_IN_EMPTY]
]);






val BALANCED_SF_SEM___sf_tree_len_2___MODEL_EXISTS_WITH_ELEMENT = store_thm ("BALANCED_SF_SEM___sf_tree_len_2___MODEL_EXISTS_WITH_ELEMENT",
“!s fL es e c X. ((FINITE (X:'b set)) /\ INFINITE (UNIV:'b set) /\
         (ALL_DISTINCT fL) /\ ~(IS_DSV_NIL (DS_EXPRESSION_EVAL s e)) /\
         ~(DS_EXPRESSION_EQUAL s es e) /\ ~(fL = []) /\
         ~(DS_EXPRESSION_EQUAL s es (dse_const (dsv_const c))) /\ ~(c IN X)) ==>

(?h:('b, 'c) heap.
   (BALANCED_SF_SEM___sf_tree_len s h fL 2 es e) /\
   (DISJOINT (FDOM h DIFF {DS_EXPRESSION_EVAL_VALUE s e}) X) /\
   (c IN FDOM h))
”,


REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [‘s’, ‘fL’, ‘2’, ‘es’, ‘e’, ‘X’] BALANCED_SF_SEM___sf_tree_len___MODEL_EXISTS) THEN
ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN
GEN_TAC THEN
Cases_on ‘c IN FDOM h’ THEN1 METIS_TAC[] THEN

REWRITE_TAC[TWO] THEN
SIMP_TAC std_ss [Once BALANCED_SF_SEM___sf_tree_len___EXTENDED_DEF] THEN
REWRITE_TAC[TWO, BALANCED_SF_SEM___sf_tree_len_def] THEN
Cases_on ‘DS_EXPRESSION_EVAL s e’ THEN FULL_SIMP_TAC std_ss [IS_DSV_NIL_def] THEN
SIMP_TAC list_ss [DS_EXPRESSION_EVAL_def, PF_SEM_def, GET_DSV_VALUE_def,
   DS_EXPRESSION_EVAL_VALUE_def, ds_value_11] THEN
REPEAT STRIP_TAC THEN
‘?f fL'. fL = f::fL'’ by (
   Cases_on ‘fL’ THEN FULL_SIMP_TAC list_ss []
) THEN
‘?h' hL'. hL = h'::hL'’ by (
   Cases_on ‘hL’ THEN FULL_SIMP_TAC list_ss []
) THEN
FULL_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN

‘?c'. GET_DSV_VALUE (h ' v ' f) = c'’ by METIS_TAC[] THEN
Q.EXISTS_TAC ‘(h \\ c') |+
              (v, h ' v |+ (f, dsv_const c)) |+
              (c, h ' c')’ THEN

REPEAT STRIP_TAC THENL [
   ALL_TAC, (*rotate 1*)

   Q.PAT_X_ASSUM ‘DISJOINT Y X’ MP_TAC THEN
   ASM_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY, IN_DIFF,
      GET_DSV_VALUE_def, IN_SING, FDOM_FUPDATE, IN_INSERT, FDOM_DOMSUB, IN_DELETE] THEN
   METIS_TAC[],


   SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT]
] THEN

Q.EXISTS_TAC ‘(FEMPTY |+ (c, h ' c'))::hL'’ THEN

‘~(v = c)’ by METIS_TAC[] THEN
‘FDOM h' = {c'}’ by (
   ‘0 < SUC (LENGTH hL')’ by DECIDE_TAC THEN
   RES_TAC THEN
   FULL_SIMP_TAC list_ss [] THEN
   METIS_TAC[BALANCED_SF_SEM___sf_tree_len_1___MODEL_SIZE, DS_EXPRESSION_EVAL_VALUE_def,
      DS_EXPRESSION_EVAL_def]
) THEN
‘h' = DRESTRICT h {c'}’ by (
   POP_ASSUM MP_TAC THEN
   Q.PAT_X_ASSUM ‘h' SUBMAP h’ MP_TAC THEN
   SIMP_TAC std_ss [SUBMAP_DEF, EXTENSION, GSYM fmap_EQ_THM, IN_SING, DRESTRICT_DEF,
      IN_INTER] THEN
   METIS_TAC[]
) THEN

‘~(v = c')’ by (
   Q.PAT_X_ASSUM ‘Y = h \\ v’ MP_TAC THEN
   ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_DOMSUB, FDOM_FUNION, EXTENSION,
      IN_DELETE, IN_UNION, DRESTRICT_DEF, IN_INTER, IN_SING] THEN
   METIS_TAC[]
) THEN
‘c' IN FDOM h’ by METIS_TAC[SUBMAP_DEF, IN_SING] THEN
‘~(c = c')’ by METIS_TAC[] THEN

REPEAT STRIP_TAC THENL [
   SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT],

   Q.PAT_X_ASSUM ‘IS_SOME (HEAP_READ_ENTRY s h e f)’ MP_TAC THEN
   ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM, GET_DSV_VALUE_def,
      IS_DSV_NIL_def, FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE_THM],


   SIMP_TAC std_ss [EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   ‘IS_SOME (HEAP_READ_ENTRY s h e y)’ by METIS_TAC[] THEN
   POP_ASSUM MP_TAC THEN
   SIMP_TAC std_ss [HEAP_READ_ENTRY_THM] THEN
   ASM_SIMP_TAC std_ss [GET_DSV_VALUE_def,
      IS_DSV_NIL_def, FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE_THM],


   ASM_SIMP_TAC list_ss [],


   FULL_SIMP_TAC list_ss [ALL_DISJOINT_def, EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
      FDOM_FUPDATE, FDOM_FEMPTY] THEN
   REPEAT STRIP_TAC THEN
   ‘y SUBMAP h’ by METIS_TAC[] THEN
   SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY, IN_SING] THEN
   METIS_TAC[SUBMAP_DEF],



   ‘FOLDR FUNION FEMPTY hL' = DRESTRICT (h \\ v) (COMPL (FDOM h'))’ by (
      MATCH_MP_TAC DRESTRICT_EQ_FUNION THEN
      ASM_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, IN_SING, NOT_IN_EMPTY,
         IN_FDOM_FOLDR_UNION] THEN
      FULL_SIMP_TAC std_ss [ALL_DISJOINT_def, EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
         DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_SING] THEN
      METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC list_ss [] THEN
   SIMP_TAC std_ss [GSYM fmap_EQ_THM, DRESTRICT_DEF, EXTENSION, FUNION_DEF,
      FDOM_FUPDATE, IN_INSERT, FDOM_FEMPTY, NOT_IN_EMPTY, IN_SING, IN_INTER,
      IN_COMPL, IN_UNION, FDOM_DOMSUB, IN_DELETE,
      FAPPLY_FUPDATE_THM, DOMSUB_FAPPLY_THM] THEN
   METIS_TAC[],



   ASM_SIMP_TAC list_ss [EVERY_MEM, DISJ_IMP_THM, FORALL_AND_THM] THEN
   CONJ_TAC THENL [
      ‘0 < SUC (LENGTH hL')’ by DECIDE_TAC THEN
      ‘BALANCED_SF_SEM___sf_tree_len s (EL 0 (h'::hL')) (f::fL') 1 es
            (dse_const (h ' v ' (EL 0 (f::fL'))))’ by METIS_TAC[] THEN
      POP_ASSUM MP_TAC THEN
      REWRITE_TAC[ONE, BALANCED_SF_SEM___sf_tree_len___EXTENDED_DEF] THEN
      ASM_SIMP_TAC list_ss [HEAP_READ_ENTRY_def, GET_DSV_VALUE_def, IS_DSV_NIL_def,
         DS_EXPRESSION_EVAL_def, FAPPLY_FUPDATE_THM, FDOM_FUPDATE, IN_INSERT,
         FDOM_FEMPTY, NOT_IN_EMPTY, PF_SEM_def, DS_EXPRESSION_EQUAL_def,
         DOMSUB_FUPDATE, DOMSUB_FEMPTY] THEN
      Cases_on ‘h ' v ' f’ THEN FULL_SIMP_TAC list_ss [IS_DSV_NIL_def, GET_DSV_VALUE_def] THEN
      ASM_SIMP_TAC std_ss [DRESTRICT_DEF, IN_INTER, IN_SING] THEN
      REPEAT STRIP_TAC THENL [
         FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def],

         Q.EXISTS_TAC ‘hL''’ THEN
         FULL_SIMP_TAC std_ss [] THEN
         REPEAT STRIP_TAC THENL [
            METIS_TAC[],
            METIS_TAC[],

            SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, DRESTRICT_DEF, FDOM_DOMSUB,
               IN_DELETE, FDOM_FEMPTY, IN_INTER, IN_SING, NOT_IN_EMPTY],

            ‘h'' = FEMPTY’ by METIS_TAC[MEM_EL] THEN
            ASM_SIMP_TAC std_ss [SUBMAP_DEF, FDOM_FEMPTY, NOT_IN_EMPTY]
         ]
      ],


      ASM_SIMP_TAC list_ss [MEM_ZIP, GSYM LEFT_FORALL_IMP_THM, EL_MAP, HEAP_READ_ENTRY_def,
         IS_DSV_NIL_def, GET_DSV_VALUE_def, FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE_THM] THEN
      REPEAT STRIP_TAC THEN
      ‘MEM (EL n fL') fL'’ by METIS_TAC[MEM_EL] THEN
      ‘~((EL n fL') = f)’ by METIS_TAC[] THEN
      ‘IS_SOME (HEAP_READ_ENTRY s h e (EL n fL'))’ by METIS_TAC[] THEN
      Q.PAT_X_ASSUM ‘DS_EXPRESSION_EVAL s e = Y’ ASSUME_TAC THEN
      FULL_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM, GET_DSV_VALUE_def] THEN
      ‘SUC n < SUC (LENGTH hL')’ by ASM_SIMP_TAC std_ss [] THEN
      RES_TAC THEN
      FULL_SIMP_TAC list_ss []
   ]
]);





val SF_SEM___sf_tree_len___MODEL_EXISTS = store_thm ("SF_SEM___sf_tree_len___MODEL_EXISTS",
   “!s fL n es e X. ((FINITE (X:'b set)) /\ INFINITE (UNIV:'b set) /\
         (ALL_DISTINCT fL) /\

         ((n = 0) \/ IS_DSV_NIL (DS_EXPRESSION_EVAL s e) ==>
          DS_EXPRESSION_EQUAL s es e)) ==>
      (?h. (SF_SEM___sf_tree_len s h fL n es e) /\
          (DISJOINT (FDOM h DIFF (
               if IS_DSV_NIL(DS_EXPRESSION_EVAL s e) then {} else
                  {DS_EXPRESSION_EVAL_VALUE s e})) X))”,

   REPEAT STRIP_TAC THEN
   MP_TAC (Q.SPECL [‘s’, ‘fL’, ‘n’, ‘es’, ‘e’, ‘X’] BALANCED_SF_SEM___sf_tree_len___MODEL_EXISTS) THEN
   ASM_REWRITE_TAC[] THEN
   Cases_on ‘n’ THENL [
      FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, FDOM_FEMPTY, EMPTY_DIFF, PF_SEM_def,
         DS_EXPRESSION_EQUAL_def, DISJOINT_EMPTY],

      FULL_SIMP_TAC arith_ss [] THEN
      Cases_on ‘DS_EXPRESSION_EQUAL s es e’ THENL [
         STRIP_TAC THEN
         Q.EXISTS_TAC ‘FEMPTY’ THEN
         FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, FDOM_FEMPTY, EMPTY_DIFF, PF_SEM_def,
         DS_EXPRESSION_EQUAL_def, DISJOINT_EMPTY],

         METIS_TAC[BALANCED_SF_SEM___sf_tree_len_THM]
      ]
   ]);







val lemma_31_list = store_thm ("lemma_31_list",
   “!s h sfL hs. ((LIST_SF_SEM s h sfL) /\ (FCARD hs = 1) /\ (hs SUBMAP h)) ==>
                 (?sf' h'.  (MEM sf' sfL) /\
                               (h' SUBMAP h) /\ (DISJOINT (FDOM hs) (FDOM h')) /\
                               (SF_SEM s (FUNION hs h') sf'))”,

   Induct_on ‘sfL’ THENL [
      SIMP_TAC std_ss [LIST_SF_SEM_THM, SUBMAP_DEF, FDOM_FEMPTY, NOT_IN_EMPTY, FCARD_DEF] THEN
      REPEAT STRIP_TAC THEN
      ‘SING (FDOM hs)’ by METIS_TAC[SING_IFF_CARD1, FDOM_FINITE] THEN
      FULL_SIMP_TAC std_ss [SING_DEF] THEN
      METIS_TAC[IN_SING],

      REPEAT STRIP_TAC THEN
      Cases_on ‘ ?h''.
              h'' SUBMAP h' /\ DISJOINT (FDOM hs) (FDOM h'') /\
              SF_SEM s (FUNION hs h'') h’ THEN1 (
         METIS_TAC[MEM]
      ) THEN
      ‘SING (FDOM hs)’ by METIS_TAC[FCARD_DEF, SING_IFF_CARD1, FDOM_FINITE] THEN
      FULL_SIMP_TAC list_ss [LIST_SF_SEM_THM, SING_DEF] THEN
      ‘~(x IN FDOM h1)’ by (
         CCONTR_TAC THEN
         Q.PAT_X_ASSUM ‘!h''. P h''’ MP_TAC THEN
         FULL_SIMP_TAC std_ss [] THEN
         Q.EXISTS_TAC ‘h1 \\ x’ THEN
         FULL_SIMP_TAC std_ss [DISJOINT_DEF, FDOM_DOMSUB, EXTENSION, IN_INTER, NOT_IN_EMPTY,
            IN_SING, IN_DELETE, SUBMAP_DEF, FUNION_DEF, IN_UNION, DOMSUB_FAPPLY_THM] THEN
         ‘FUNION hs (h1 \\ x) = h1’
            suffices_by (STRIP_TAC THEN ASM_REWRITE_TAC []) THEN
         ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, EXTENSION, FDOM_DOMSUB,
            IN_UNION, IN_DELETE, DOMSUB_FAPPLY_THM] THEN
         METIS_TAC[]
      ) THEN
      ‘hs SUBMAP h2’ by (
         Q.PAT_X_ASSUM ‘hs SUBMAP h'’ MP_TAC THEN
         ASM_SIMP_TAC std_ss [SUBMAP_DEF, IN_UNION, IN_SING,
            FUNION_DEF]
      ) THEN
      ‘?sf' h'.
         MEM sf' sfL /\ h' SUBMAP h2 /\ DISJOINT (FDOM hs) (FDOM h') /\
         SF_SEM s (FUNION hs h') sf'’ by METIS_TAC[] THEN
      Q.EXISTS_TAC ‘sf'’ THEN
      Q.EXISTS_TAC ‘h''’ THEN
      ASM_SIMP_TAC std_ss [] THEN
      METIS_TAC[SUBMAP___FUNION___ID, SUBMAP_TRANS, SUBMAP_REFL]
   ]);



val LEMMA_31 = store_thm ("LEMMA_31",
   “!s h sf hs. ((SF_SEM s h sf) /\ (FCARD hs = 1) /\ (hs SUBMAP h)) ==>
                 (?sf' h' sf''.  SF_IS_SIMPLE sf' /\
                               (SF_EXPRESSION_SET sf = SF_EXPRESSION_SET sf' UNION SF_EXPRESSION_SET sf'') /\
                               (SF_EQUIV sf (sf_star sf' sf'')) /\
                               (h' SUBMAP h) /\ (DISJOINT (FDOM hs) (FDOM h')) /\
                               (SF_SEM s (FUNION hs h') sf'))”,

   SIMP_TAC std_ss [LIST_SF_SEM_FLAT_INTRO] THEN
   REPEAT STRIP_TAC THEN
   ‘?sf' h'.
      MEM sf' (DS_FLAT_SF sf) /\ h' SUBMAP h /\ DISJOINT (FDOM hs) (FDOM h') /\
      SF_SEM s (FUNION hs h') sf'’ by METIS_TAC[lemma_31_list] THEN
   Q.EXISTS_TAC ‘sf'’ THEN
   Q.EXISTS_TAC ‘h'’ THEN
   ‘(SF_IS_SIMPLE sf') /\ (DS_FLAT_SF sf' = [sf'])’ by METIS_TAC[SF_IS_SIMPLE___MEM_DS_FLAT_SF] THEN
   ASM_SIMP_TAC std_ss [GSYM LIST_SF_SEM_FLAT_INTRO] THEN
   METIS_TAC[SIMPLE_SUB_FORMULA_TO_FRONT, SF_EQUIV_def]);





Theorem LEMMA_5:
  !(s:'a ->'b ds_value) h fL e2 e3 pf sf pf' sf'.
    INFINITE (UNIV:'b set) /\ ALL_DISTINCT fL /\ fL ≠ [] /\
    (!h. PF_SEM s pf /\
         (?h1 h2. (h = FUNION h1 h2) /\
                  (DISJOINT (FDOM h1) (FDOM h2)) /\
                  (SF_SEM s h2 sf) /\
                  (BALANCED_SF_SEM___sf_tree_len s h1 fL 2 e3 e2)) ==>
         DS_SEM s h (pf', sf')) /\
    PF_SEM s pf /\ SF_SEM s h sf /\ ~DS_EXPRESSION_EQUAL s e2 e3 /\
    ~DS_EXPRESSION_EQUAL s e2 dse_nil /\
    DS_POINTER_DANGLES s h e2 ==>
    PF_SEM s pf' /\ SF_SEM___EXTEND s h (sf_tree fL e3 e2) sf'
Proof

REPEAT GEN_TAC THEN STRIP_TAC THEN
Cases_on ‘DS_EXPRESSION_EVAL s e2’ THEN1 (
   FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, DS_EXPRESSION_EQUAL_def, dse_nil_def]
) THEN

Q.ABBREV_TAC ‘X = (e2 INSERT e3 INSERT (SF_EXPRESSION_SET sf') UNION
   (IMAGE (dse_const o dsv_const) (FDOM (h:('b, 'c) heap))) UNION
   (BIGUNION (IMAGE (\h':('c |-> 'b ds_value). IMAGE dse_const (FRANGE h')) (FRANGE (h:('b, 'c) heap)))))’ THEN

MP_TAC (
   Q.SPECL [‘s’, ‘fL’, ‘e3’, ‘e2’,
      ‘IMAGE (DS_EXPRESSION_EVAL_VALUE s) X’] BALANCED_SF_SEM___sf_tree_len_2___MODEL_EXISTS) THEN


impl_tac THEN1 (
   ‘FINITE X’ by (
      Q.UNABBREV_TAC ‘X’ THEN
      ASM_SIMP_TAC std_ss [FINITE_INSERT, FINITE_UNION, SF_EXPRESSION_SET___FINITE] THEN
      STRIP_TAC THENL [
         MATCH_MP_TAC IMAGE_FINITE THEN
         SIMP_TAC std_ss [FDOM_FINITE],


         MATCH_MP_TAC FINITE_BIGUNION THEN
         SIMP_TAC std_ss [IN_IMAGE, GSYM LEFT_FORALL_IMP_THM] THEN
         METIS_TAC[FINITE_FRANGE, IMAGE_FINITE]
      ]
   ) THEN
   FULL_SIMP_TAC std_ss [IS_DSV_NIL_def, IMAGE_FINITE, DS_EXPRESSION_EQUAL_def]
) THEN
STRIP_TAC THEN
Q.PAT_X_ASSUM ‘Y = dsv_const v’ ASSUME_TAC THEN
FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, IS_DSV_NIL_def, GET_DSV_VALUE_def,
   DS_EXPRESSION_EVAL_VALUE_def] THEN
‘!e. e IN X ==> ~(DS_EXPRESSION_EVAL_VALUE s e IN FDOM hl)’ by (
   FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
      IN_IMAGE] THEN
   METIS_TAC[]
) THEN

‘?hl1 hl2 w.
   (FUNION hl1 hl2 = hl) /\
   (FDOM hl1 = {w}) /\
   (~(w = v)) /\
   (hl1 SUBMAP hl) /\
   (FCARD hl1 = 1)’ by (

   ‘?x. x IN FDOM hl’ by METIS_TAC[MEMBER_NOT_EMPTY] THEN

   Q.EXISTS_TAC ‘FEMPTY |+ (x, hl ' x)’ THEN
   Q.EXISTS_TAC ‘hl \\ x’ THEN
   Q.EXISTS_TAC ‘x’ THEN
   FULL_SIMP_TAC std_ss [SUBMAP_DEF, FDOM_FUPDATE, IN_INSERT, FDOM_FEMPTY, NOT_IN_EMPTY,
      FAPPLY_FUPDATE_THM, FCARD_DEF, CARD_SING, GSYM fmap_EQ_THM,
      EXTENSION, FUNION_DEF, FAPPLY_FUPDATE_THM, IN_SING, IN_UNION,
      DOMSUB_FAPPLY_THM, FDOM_DOMSUB, IN_DELETE, DISJOINT_DEF, IN_INTER] THEN
   METIS_TAC[]
) THEN

‘DS_SEM s (FUNION h2 (FUNION hl h)) (pf', sf')’ by (
   Q.PAT_X_ASSUM ‘!h:('b, 'c) heap. P h’ MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   Q.EXISTS_TAC ‘FUNION h2 hl’ THEN
   Q.EXISTS_TAC ‘h’ THEN

   ASM_REWRITE_TAC[FDOM_FUNION, DISJOINT_UNION_BOTH,  FUNION___ASSOC] THEN
   Q.PAT_X_ASSUM ‘!e. e IN X ==> P e’ MP_TAC THEN
   Q.UNABBREV_TAC ‘X’ THEN

   FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def,
      DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_SING,
      DS_EXPRESSION_EVAL_VALUE_def, IN_IMAGE, IN_INSERT,
      IN_UNION, DISJ_IMP_THM, FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM,
      DS_EXPRESSION_EVAL_def, DS_POINTER_DANGLES, IS_DSV_NIL_def] THEN
   METIS_TAC []
) THEN

‘~(v IN FDOM hl)’ by (
   Q.PAT_X_ASSUM ‘!e. e IN X ==> P e’ MP_TAC THEN
   Q.UNABBREV_TAC ‘X’ THEN
   ASM_SIMP_TAC std_ss [IN_INSERT, DISJ_IMP_THM, FORALL_AND_THM,
      DS_EXPRESSION_EVAL_VALUE_def, GET_DSV_VALUE_def]
) THEN

FULL_SIMP_TAC std_ss [DS_SEM_def] THEN
MP_TAC (Q.SPECL [‘s’, ‘(FUNION h2 (FUNION hl h))’, ‘sf'’, ‘hl1’] LEMMA_31) THEN
impl_tac THEN1 (
   ASM_REWRITE_TAC[] THEN
   FULL_SIMP_TAC std_ss [SUBMAP_DEF, FUNION_DEF, IN_UNION, IN_SING, COND_RATOR,
                         COND_RAND, IN_INSERT, SUBMAP_DEF,
                         DS_EXPRESSION_EVAL_VALUE_def, GET_DSV_VALUE_def] THEN
   METIS_TAC[]
) THEN
ASM_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY, IN_SING] THEN
STRIP_TAC THEN

‘?h'''. h''' = DRESTRICT (FUNION h2 (FUNION hl h)) (COMPL (FDOM (FUNION hl1 h')))’ by METIS_TAC[] THEN
‘SF_SEM s h''' sf'''’ by (
   FULL_SIMP_TAC std_ss [SF_EQUIV_def, SF_SEM_def] THEN
   ‘h1 = (FUNION hl1 h')’ by (
      ‘SF_IS_PRECISE sf''’ by REWRITE_TAC[SF_IS_PRECISE_THM] THEN
      FULL_SIMP_TAC std_ss [SF_IS_PRECISE_def] THEN
      POP_ASSUM MATCH_MP_TAC THEN
      Q.EXISTS_TAC ‘s’ THEN
      Q.EXISTS_TAC ‘FUNION h2 (FUNION hl h)’ THEN
      ASM_SIMP_TAC std_ss [SUBMAP___FUNION___ID] THEN
      Q.PAT_X_ASSUM ‘YYY = FUNION h1 h2'’ (MP_TAC o GSYM) THEN
      Q.PAT_X_ASSUM ‘h' SUBMAP XXX’ MP_TAC THEN
      Q.PAT_X_ASSUM ‘hl1 SUBMAP XXX’ MP_TAC THEN
      SIMP_TAC std_ss [] THEN
      ASM_SIMP_TAC std_ss [SUBMAP_DEF, FUNION_DEF, IN_UNION, FDOM_FUPDATE,
         IN_INSERT, FDOM_FEMPTY, IN_SING, NOT_IN_EMPTY, GET_DSV_VALUE_def,
         FAPPLY_FUPDATE, DISJOINT_DEF, EXTENSION, IN_INTER,
         DISJ_IMP_THM, DS_EXPRESSION_EVAL_VALUE_def] THEN
      METIS_TAC[]
   ) THEN
   ‘h''' = h2'’ suffices_by METIS_TAC[] THEN
   Q.PAT_X_ASSUM ‘DISJOINT (FDOM h1) (FDOM h2')’ MP_TAC THEN
   ASM_REWRITE_TAC[] THEN

   SIMP_TAC std_ss [GSYM fmap_EQ_THM, DRESTRICT_DEF, IN_INTER, IN_DIFF, FUNION_DEF,
      EXTENSION, IN_UNION, FDOM_FUPDATE, IN_INSERT, IN_SING, FDOM_FEMPTY,
      NOT_IN_EMPTY, FAPPLY_FUPDATE, DISJOINT_DEF, DISJ_IMP_THM, IN_COMPL] THEN
   METIS_TAC[]
) THEN

Q.PAT_X_ASSUM ‘SF_SEM s H sf''’ MP_TAC THEN
Cases_on ‘sf''’ THENL [
   FULL_SIMP_TAC std_ss [SF_IS_SIMPLE_def],


   ASM_SIMP_TAC std_ss [SF_SEM_def, FUNION_DEF, EXTENSION, IN_SING, IN_UNION] THEN
   REPEAT STRIP_TAC THEN
   ‘DS_EXPRESSION_EVAL_VALUE s d = w’ by METIS_TAC[] THEN
   FULL_SIMP_TAC std_ss [SF_EXPRESSION_SET_def, SUBSET_DEF, IN_INSERT,
      NOT_IN_EMPTY, DISJ_IMP_THM, FORALL_AND_THM] THEN
   Q.UNABBREV_TAC ‘X’ THEN
   ‘~(DS_EXPRESSION_EQUAL s (dse_const (dsv_const w)) d)’ by METIS_TAC[IN_SING, SUBMAP_DEF,
      IN_INSERT, IN_UNION] THEN
   NTAC 2 (POP_ASSUM MP_TAC) THEN
   FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_VALUE_def,
      DS_EXPRESSION_EVAL_def, DS_POINTS_TO_def] THEN
   Cases_on ‘DS_EXPRESSION_EVAL s d’ THENL [
      FULL_SIMP_TAC std_ss [IS_DSV_NIL_def],
      SIMP_TAC std_ss [GET_DSV_VALUE_def]
   ],




   STRIP_TAC THEN
   ‘w IN FDOM hl’ by (
      Q.PAT_X_ASSUM ‘YYY = hl’ (MP_TAC o GSYM) THEN
      ASM_SIMP_TAC std_ss [FUNION_DEF, IN_UNION, IN_SING]
   ) THEN
   ‘~(DS_EXPRESSION_EQUAL s d0 d)’ by (
      CCONTR_TAC THEN
      Q.PAT_X_ASSUM ‘SF_SEM s YYY (sf_tree l d d0)’ MP_TAC THEN
      FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_THM] THEN
      ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FEMPTY, EXTENSION, FUNION_DEF, IN_UNION, IN_SING,
         NOT_IN_EMPTY, EXISTS_OR_THM]
   ) THEN
   ‘~(IS_DSV_NIL (DS_EXPRESSION_EVAL s d0))’ by (
      Q.PAT_X_ASSUM ‘SF_SEM s H (sf_tree l d d0)’ MP_TAC THEN
      ASM_SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_len_def, SF_SEM___sf_tree_def,
         GSYM LEFT_FORALL_IMP_THM] THEN
      Cases_on ‘n’ THENL [
         ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def],

         ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def] THEN
         METIS_TAC[]
      ]
   ) THEN
   ‘?hl'dom. hl'dom = \x. ?f. (x = GET_DSV_VALUE (h2 ' v ' f)) /\ (MEM f l)’ by METIS_TAC[] THEN
   ‘?hl'. hl' = DRESTRICT hl hl'dom’ by METIS_TAC[] THEN
   ‘v IN FDOM h' /\ (hl' SUBMAP hl) /\ (!x. MEM x l ==> MEM x fL) /\
    (ALL_DISTINCT l) /\
    (hl' = FUNION hl1 (DRESTRICT h' (FDOM hl))) /\
    SF_SEM s (FUNION h2 hl') (sf_tree l e3 e2)’ by (
      ASM_SIMP_TAC std_ss [] THEN

      ‘~(DS_EXPRESSION_EVAL_VALUE s d IN FDOM hl) /\
      ~(DS_EXPRESSION_EVAL_VALUE s d0 IN FDOM hl)’ by (
         ‘d IN X /\ d0 IN X’ by (
            Q.UNABBREV_TAC ‘X’ THEN
            FULL_SIMP_TAC std_ss [SF_EXPRESSION_SET_def, SUBSET_DEF, IN_INSERT, NOT_IN_EMPTY,
               IN_UNION]
         ) THEN
         METIS_TAC[]
      ) THEN

      ‘!e f x. ((x IN FDOM hl) /\ (x IN FDOM (FUNION hl1 h')) /\ MEM f l /\ DS_POINTS_TO s (FUNION hl1 h') e [(f, dse_const (dsv_const x))]) ==> (DS_EXPRESSION_EVAL s e = dsv_const v)’ by (
         ASM_SIMP_TAC list_ss [DS_EXPRESSION_EQUAL_def, DS_POINTS_TO_def,
            DS_EXPRESSION_EVAL_def, NOT_IS_DSV_NIL_THM, IN_SING, IN_UNION] THEN
         REPEAT STRIP_TAC THEN
         Q.PAT_X_ASSUM ‘DS_EXPRESSION_EVAL s e = dsv_const c’ ASSUME_TAC THEN
         FULL_SIMP_TAC std_ss [ds_value_11, GET_DSV_VALUE_def] THEN

         ‘c IN FDOM h2 \/ (~(c IN (FDOM h2)) /\ (c IN FDOM hl)) \/
          (~(c IN (FDOM h2)) /\ ~(c IN FDOM hl) /\ (c IN FDOM h'))’ by (
            Cases_on ‘c IN FDOM h2’ THEN ASM_REWRITE_TAC[] THEN
            Cases_on ‘c IN FDOM hl’ THEN ASM_REWRITE_TAC[] THEN
            FULL_SIMP_TAC std_ss [FUNION_DEF, IN_UNION, SUBMAP_DEF] THEN
            METIS_TAC[IN_SING]
         ) THENL [
            POP_ASSUM MP_TAC THEN
            ASM_SIMP_TAC std_ss [IN_SING],

            ‘(FUNION hl1 h' ' c) = hl ' c’ by (
               FULL_SIMP_TAC std_ss [FUNION_DEF, SUBMAP_DEF, IN_SING] THEN
               Cases_on ‘c = w’ THEN ASM_REWRITE_TAC[] THEN
               ‘c IN FDOM h'’ by METIS_TAC[IN_UNION, IN_SING] THEN
               METIS_TAC[IN_UNION]
            ) THEN
            FULL_SIMP_TAC std_ss [] THEN

            Q.PAT_X_ASSUM ‘f IN FDOM (hl ' c)’ MP_TAC THEN
            ASM_SIMP_TAC std_ss [] THEN
            STRIP_TAC THEN
            ‘HEAP_READ_ENTRY s hl (dse_const (dsv_const c)) f =
              SOME (DS_EXPRESSION_EVAL s e3)’ by METIS_TAC[] THEN
            POP_ASSUM MP_TAC THEN
            SIMP_TAC std_ss [HEAP_READ_ENTRY_THM, DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def,
               IS_DSV_NIL_def] THEN
            ASM_SIMP_TAC std_ss [] THEN
            ‘e3 IN X’ by (
               Q.UNABBREV_TAC ‘X’ THEN
               SIMP_TAC list_ss [IN_INSERT]
            ) THEN
            METIS_TAC[GET_DSV_VALUE_def, DS_EXPRESSION_EVAL_VALUE_def],


            ‘c IN FDOM h’ by (
               FULL_SIMP_TAC std_ss [SUBMAP_DEF, FUNION_DEF] THEN
               METIS_TAC[IN_UNION]
            ) THEN
            ‘(FUNION hl1 h' ' c) = h ' c’ by (
               ‘~(c = w)’ by METIS_TAC[IN_SING, SUBMAP_DEF] THEN
               FULL_SIMP_TAC std_ss [FUNION_DEF, SUBMAP_DEF, IN_SING]
            ) THEN
            FULL_SIMP_TAC std_ss [] THEN
            ‘dse_const (dsv_const x) IN X’ by (
               Q.UNABBREV_TAC ‘X’ THEN
               ASM_SIMP_TAC std_ss [IN_INSERT, IN_UNION,
                  IN_BIGUNION, IN_IMAGE, FRANGE_DEF, GSYM RIGHT_EXISTS_AND_THM,
                  GSYM LEFT_EXISTS_AND_THM, GSPECIFICATION] THEN
               METIS_TAC[]
            ) THEN
            ‘~(DS_EXPRESSION_EVAL_VALUE s (dse_const (dsv_const x)) IN FDOM hl)’ by METIS_TAC[] THEN
            FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def, DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def]
         ]
      ) THEN
      ‘!x. (x IN FDOM hl /\ x IN FDOM (FUNION hl1 h')) ==> (v IN FDOM h' /\ ?f. MEM f l /\ (h2 ' v ' f = dsv_const x))’ by (
         GEN_TAC THEN STRIP_TAC THEN
         MP_TAC (Q.SPECL [‘s’, ‘FUNION hl1 h'’, ‘l’, ‘d’, ‘d0’, ‘dse_const (dsv_const x)’] LEMMA_26a) THEN
         impl_tac THEN1 (
            POP_ASSUM MP_TAC THEN
            ASM_SIMP_TAC list_ss [DS_EXPRESSION_EVAL_VALUE_def, DS_EXPRESSION_EVAL_def,
               GET_DSV_VALUE_def, IS_DSV_NIL_def, DS_POINTS_TO_def, FUNION_DEF, IN_UNION,
               IN_SING, DS_EXPRESSION_EQUAL_def] THEN
            FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def] THEN
            METIS_TAC[GET_DSV_VALUE_def]
         ) THEN
         STRIP_TAC THEN
         ‘DS_EXPRESSION_EVAL s e'' = dsv_const v’ by (
            Q.PAT_X_ASSUM ‘!e f x. P e f x’ MATCH_MP_TAC THEN
            Q.EXISTS_TAC ‘f’ THEN
            Q.EXISTS_TAC ‘x’ THEN
            ASM_REWRITE_TAC[] THEN
            ASM_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION, IN_SING]
         ) THEN
         Q.PAT_X_ASSUM ‘DS_POINTS_TO s H e'' Y’ MP_TAC THEN
         ASM_SIMP_TAC list_ss [DS_POINTS_TO_def, GET_DSV_VALUE_def, IS_DSV_NIL_def, FUNION_DEF,
            IN_UNION, IN_SING, DS_EXPRESSION_EVAL_def] THEN
         STRIP_TAC THEN
         Q.EXISTS_TAC ‘f’ THEN
         ASM_SIMP_TAC std_ss [] THEN
         FULL_SIMP_TAC std_ss [SUBMAP_DEF, FUNION_DEF, GET_DSV_VALUE_def, IN_SING]
      ) THEN
      ‘v IN FDOM h'’ by (
         FULL_SIMP_TAC std_ss [FUNION_DEF, IN_UNION] THEN
         METIS_TAC[IN_SING]
      ) THEN
      ‘(h' ' v = h2 ' v)’ by (
         FULL_SIMP_TAC std_ss [SUBMAP_DEF, FUNION_DEF, GET_DSV_VALUE_def, IN_SING]
      ) THEN
      FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def] THEN

      ‘!x. MEM x l ==> MEM x fL’ by (
         REPEAT STRIP_TAC THEN
         ‘?e. DS_POINTS_TO s (FUNION hl1 h') e2 [(x, e)]’ by (
            MATCH_MP_TAC LEMMA_26b THEN
            Q.EXISTS_TAC ‘l’ THEN
            Q.EXISTS_TAC ‘d’ THEN
            Q.EXISTS_TAC ‘d0’ THEN
            FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def, IS_DSV_NIL_def,
               DS_EXPRESSION_EVAL_VALUE_def, GET_DSV_VALUE_def, FUNION_DEF, IN_UNION,
               IN_SING, ds_value_11] THEN
            ‘DS_POINTER_DANGLES s (FUNION hl1 h') d’ by METIS_TAC[LEMMA_3_1_1] THEN
            POP_ASSUM MP_TAC THEN
            Cases_on ‘DS_EXPRESSION_EVAL s d’ THENL [
               SIMP_TAC std_ss [ds_value_distinct],

               ASM_SIMP_TAC std_ss [ds_value_11, IS_DSV_NIL_def, GET_DSV_VALUE_def, FUNION_DEF, IN_UNION,
                  IN_SING, DS_POINTER_DANGLES] THEN
               METIS_TAC[]
            ]
         ) THEN
         POP_ASSUM MP_TAC THEN
         ASM_SIMP_TAC list_ss [DS_POINTS_TO_def, GET_DSV_VALUE_def, IS_DSV_NIL_def, FUNION_DEF, IN_UNION,
            IN_SING]
      ) THEN
      ‘ALL_DISTINCT l’ by (
         SIMP_TAC std_ss [EL_ALL_DISTINCT_EQ] THEN
         CCONTR_TAC THEN
         FULL_SIMP_TAC std_ss [] THEN
         Cases_on ‘n1 = n2’ THEN1 METIS_TAC[] THEN
         FULL_SIMP_TAC std_ss [] THEN
         MP_TAC (Q.SPECL [‘s’, ‘FUNION hl1 h'’, ‘l’, ‘d’, ‘d0’, ‘e2’, ‘n1’, ‘n2’] LEMMA_26d) THEN
         ASM_SIMP_TAC list_ss [IS_DSV_NIL_def, DS_EXPRESSION_EVAL_VALUE_def,
            GET_DSV_VALUE_def, FUNION_DEF, DS_EXPRESSION_EQUAL_def, IN_UNION,
            DS_POINTS_TO_def, IN_SING] THEN
         CONJ_TAC THENL [
            CCONTR_TAC THEN
            ‘DS_POINTER_DANGLES  s (FUNION hl1 h') d’ by METIS_TAC[LEMMA_3_1_1] THEN
            POP_ASSUM MP_TAC THEN
            POP_ASSUM MP_TAC THEN
            ASM_SIMP_TAC std_ss [DS_POINTER_DANGLES, GET_DSV_VALUE_def,
               IS_DSV_NIL_def, FUNION_DEF, IN_UNION],

            REPEAT GEN_TAC THEN
            ‘MEM (EL n1 l) fL /\ MEM (EL n2 l) fL’ by METIS_TAC[MEM_EL] THEN
            ASM_SIMP_TAC std_ss [MEM_EL] THEN
            MATCH_MP_TAC (prove (“(~a ==> b) ==> (a \/ b)”, METIS_TAC[])) THEN
            SIMP_TAC std_ss [] THEN
            ‘GET_DSV_VALUE (h2 ' v ' (EL n2 l)) IN FDOM hl’ suffices_by (STRIP_TAC THEN
               METIS_TAC[]
            ) THEN
            Q.PAT_X_ASSUM ‘!x. P x = x IN (FDOM hl)’ (fn thm => REWRITE_TAC [GSYM thm]) THEN
            Q.EXISTS_TAC ‘EL n2 l’ THEN
            ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_def, GET_DSV_VALUE_def, IN_SING, IS_DSV_NIL_def] THEN
            ‘?x. (h2 ' v ' (EL n2 l) = dsv_const x)’ by METIS_TAC[] THEN
            ASM_SIMP_TAC std_ss [GET_DSV_VALUE_def]
         ]
      ) THEN

      REPEAT STRIP_TAC THENL [
         SIMP_TAC std_ss [SUBMAP_DEF, DRESTRICT_DEF, IN_INTER],
         METIS_TAC[],
         ASM_REWRITE_TAC[],


         ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, DRESTRICT_DEF,
            IN_SING, GET_DSV_VALUE_def, IN_UNION, IN_INTER, DISJ_IMP_THM, EXTENSION,
            prove (“!x. x IN (\x. P x) = P x”, SIMP_TAC std_ss [IN_DEF]),
            GSYM RIGHT_EXISTS_AND_THM] THEN
         conj_asm1_tac THENL [
            GEN_TAC THEN
            Cases_on ‘~(x IN FDOM hl)’ THEN1 (
               METIS_TAC[FUNION_DEF, IN_UNION, IN_SING]
            ) THEN
            Cases_on ‘x = w’ THEN1 (
               FULL_SIMP_TAC std_ss [FUNION_DEF, IN_UNION] THEN
               METIS_TAC[GET_DSV_VALUE_def, IN_SING]
            ) THEN
            FULL_SIMP_TAC std_ss [] THEN
            EQ_TAC THENL [
               STRIP_TAC THEN
               ‘?c''. c'' IN FDOM hl /\ (h2 ' v ' f = dsv_const c'')’ by METIS_TAC[] THEN
               FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def] THEN
               MP_TAC (
                  Q.SPECL [‘s’, ‘FUNION hl1 h'’, ‘l’, ‘d’, ‘d0’, ‘dse_const ((h2:('b, 'c) heap) ' v ' f)’, ‘e2’, ‘f’] LEMMA_26c) THEN
               ASM_SIMP_TAC list_ss [DS_EXPRESSION_EVAL_VALUE_def, DS_EXPRESSION_EQUAL_def,
                  DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def, IS_DSV_NIL_def, FDOM_FUNION,
                  IN_UNION, IN_SING, DS_POINTS_TO_def, FUNION_DEF] THEN
               METIS_TAC[GET_DSV_VALUE_def],

               STRIP_TAC THEN
               FULL_SIMP_TAC std_ss [FUNION_DEF, IN_UNION] THEN
               ‘?f. MEM f l /\ (h2 ' v ' f = dsv_const x)’ by METIS_TAC[] THEN
               METIS_TAC[GET_DSV_VALUE_def]
            ],


            POP_ASSUM MP_TAC THEN SIMP_TAC std_ss [] THEN
            STRIP_TAC THEN
            GEN_TAC THEN
            Cases_on ‘x = w’ THENL [
               ASM_SIMP_TAC std_ss [] THEN
               ‘hl1 ' w = hl ' w’ by (
                  FULL_SIMP_TAC std_ss [SUBMAP_DEF, IN_SING]
               ) THEN
               ASM_SIMP_TAC std_ss [],

               ASM_SIMP_TAC std_ss [] THEN
               STRIP_TAC THEN
               ‘h' ' x = hl ' x’ by (
                  FULL_SIMP_TAC std_ss [SUBMAP_DEF, FUNION_DEF, IN_SING] THEN
                  METIS_TAC[GET_DSV_VALUE_def]
               ) THEN
               ASM_SIMP_TAC std_ss []
            ]
         ],



         SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def] THEN
         Q.EXISTS_TAC ‘SUC (SUC 0)’ THEN
         REWRITE_TAC [SF_SEM___sf_tree_len_def] THEN
         ASM_SIMP_TAC list_ss [PF_SEM_def, IS_DSV_NIL_def, GET_DSV_VALUE_def, EVERY_MEM,
            MEM_MAP, GSYM LEFT_FORALL_IMP_THM, DS_EXPRESSION_EVAL_def, DS_EXPRESSION_EQUAL_def,
            FDOM_FUNION, IN_UNION, IN_SING] THEN
         ‘!h. HEAP_READ_ENTRY s (FUNION h2 h) e2 =
              HEAP_READ_ENTRY s h2 e2’ by (
            ASM_SIMP_TAC std_ss [FUN_EQ_THM, HEAP_READ_ENTRY_def,
               GET_DSV_VALUE_def, IN_SING, IS_DSV_NIL_def, FUNION_DEF,
               IN_UNION]
         ) THEN
         ASM_SIMP_TAC std_ss [] THEN
         Q.EXISTS_TAC ‘MAP (\f. DRESTRICT hl {GET_DSV_VALUE (THE (HEAP_READ_ENTRY s h2 e2 f))}) l’ THEN
         ASM_SIMP_TAC list_ss [] THEN
         REPEAT CONJ_TAC THENL [
            ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_THM, IS_DSV_NIL_def, GET_DSV_VALUE_def, IN_SING],

            SIMP_TAC list_ss [EL_ALL_DISJOINT_EQ, EL_MAP, DRESTRICT_DEF,
               DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY, IN_SING] THEN
            ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_def, IS_DSV_NIL_def, IN_SING, GET_DSV_VALUE_def] THEN
            REPEAT GEN_TAC THEN STRIP_TAC THEN
            ‘(MEM (EL n1 l) fL) /\ (MEM (EL n2 l) fL)’ by METIS_TAC[MEM_EL] THEN
            ‘?x1. (x1 IN FDOM hl) /\ (h2 ' v ' (EL n1 l) = dsv_const x1)’ by METIS_TAC[] THEN
            ‘?x2. (x2 IN FDOM hl) /\ (h2 ' v ' (EL n2 l) = dsv_const x2)’ by METIS_TAC[] THEN
            ASM_SIMP_TAC std_ss [GET_DSV_VALUE_def] THEN
            Tactical.REVERSE EQ_TAC THEN1 METIS_TAC[ds_value_11] THEN
            STRIP_TAC THEN
            ‘EL n1 l = EL n2 l’ suffices_by (STRIP_TAC THEN
               METIS_TAC[EL_ALL_DISTINCT_EQ]
            ) THEN
            Cases_on ‘n1 = n2’ THEN1 ASM_REWRITE_TAC[] THEN
            MP_TAC (Q.SPECL [‘s’, ‘FUNION hl1 h'’, ‘l’, ‘d’, ‘d0’, ‘e2’, ‘n1’, ‘n2’] LEMMA_26d) THEN
            ASM_SIMP_TAC list_ss [DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_VALUE_def, IS_DSV_NIL_def,
               GET_DSV_VALUE_def, FDOM_FUNION, IN_UNION, IN_SING] THEN
            MATCH_MP_TAC (prove (“(a /\ (b ==> c)) ==> ((a ==> b) ==> c)”, METIS_TAC[])) THEN
            CONJ_TAC THEN1 (
               CCONTR_TAC THEN
               ‘DS_POINTER_DANGLES s (FUNION hl1 h') d’ by METIS_TAC[LEMMA_3_1_1] THEN
               NTAC 2 (POP_ASSUM MP_TAC) THEN
               FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, GET_DSV_VALUE_def, IS_DSV_NIL_def,
                  FUNION_DEF, IN_UNION]
            ) THEN
            ASM_SIMP_TAC list_ss [DS_POINTS_TO_def, GET_DSV_VALUE_def, FUNION_DEF, IN_SING,
               IS_DSV_NIL_def, IN_UNION] THEN
            STRIP_TAC THENL [
               METIS_TAC[GET_DSV_VALUE_def],
               METIS_TAC[]
            ],



            ‘h2 \\ v = FEMPTY’ by (
               ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_DOMSUB, EXTENSION, IN_DELETE, IN_SING,
                  FDOM_FEMPTY, NOT_IN_EMPTY]
            ) THEN
            ‘!Y. (DRESTRICT hl Y) \\ v = DRESTRICT hl Y’ by (
               ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, DRESTRICT_DEF,
                  FDOM_DOMSUB, IN_INTER, IN_DELETE, DOMSUB_FAPPLY_NEQ] THEN
               METIS_TAC[]
            ) THEN
            ASM_SIMP_TAC std_ss [DOMSUB_FUNION, HEAP_READ_ENTRY_def, IS_DSV_NIL_def, GET_DSV_VALUE_def,
               IN_SING, FUNION_FEMPTY_1] THEN

            Q.PAT_X_ASSUM ‘!x. MEM x l ==> MEM x fL’ MP_TAC THEN
            REPEAT (POP_ASSUM (K ALL_TAC)) THEN
            Induct_on ‘l’ THENL [
               SIMP_TAC list_ss [GSYM fmap_EQ_THM, FDOM_FEMPTY, DRESTRICT_DEF,
                  EXTENSION, NOT_IN_EMPTY, IN_INTER, FUNION_FEMPTY_1] THEN
               SIMP_TAC std_ss [IN_DEF],


               SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
               REPEAT STRIP_TAC THEN
               ‘DRESTRICT hl
                  (\x. ?f. (x = GET_DSV_VALUE ((h2:('b, 'c) heap) ' v ' f)) /\ ((f = h) \/ MEM f l)) =
                FUNION (DRESTRICT hl {GET_DSV_VALUE (h2 ' v ' h)})
                       (DRESTRICT hl (\x. ?f. (x = GET_DSV_VALUE (h2 ' v ' f)) /\ MEM f l))’ by (
                  SIMP_TAC std_ss [DRESTRICT_FUNION] THEN
                  AP_TERM_TAC THEN
                  SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_SING] THEN
                  SIMP_TAC std_ss [IN_DEF] THEN
                  METIS_TAC[]
               ) THEN
               ASM_SIMP_TAC std_ss [FUNION_FEMPTY_1]
            ],


            SIMP_TAC list_ss [MEM_ZIP, GSYM LEFT_FORALL_IMP_THM, EL_MAP] THEN
            GEN_TAC THEN STRIP_TAC THEN
            ‘MEM (EL n l) l /\ MEM (EL n l) fL’ by METIS_TAC[MEM_EL] THEN
            ‘?x. x IN (FDOM hl) /\ (h2 ' v ' (EL n l) = dsv_const x)’ by METIS_TAC[] THEN
            ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_def, GET_DSV_VALUE_def, IN_SING,
               IS_DSV_NIL_def, DS_EXPRESSION_EVAL_def,
               DRESTRICT_DEF, IN_INTER] THEN
            ‘~(dsv_const x = DS_EXPRESSION_EVAL s e3)’ by (
               ‘e3 IN X’ by (
                  Q.UNABBREV_TAC ‘X’ THEN
                  SIMP_TAC std_ss [IN_INSERT]
               ) THEN
               METIS_TAC[GET_DSV_VALUE_def]
            ) THEN
            ASM_SIMP_TAC std_ss [] THEN
            Q.EXISTS_TAC ‘MAP (\x. FEMPTY) l’ THEN
            SIMP_TAC list_ss [EL_ALL_DISJOINT_EQ, EL_MAP, FDOM_FEMPTY, DISJOINT_EMPTY,
               MEM_ZIP, GSYM LEFT_FORALL_IMP_THM] THEN
            CONJ_TAC THENL [
               REPEAT (POP_ASSUM (K ALL_TAC)) THEN
               ‘DRESTRICT hl {x} \\ x = FEMPTY’ by (
                  SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FDOM_DOMSUB,
                     IN_DELETE, DRESTRICT_DEF, IN_INTER, IN_SING, FDOM_FEMPTY, NOT_IN_EMPTY]
               ) THEN
               ASM_SIMP_TAC std_ss [] THEN
               Induct_on ‘l’ THENL [
                  SIMP_TAC list_ss [],
                  ASM_SIMP_TAC list_ss [FUNION_FEMPTY_1]
               ],


               REPEAT STRIP_TAC THEN
               ‘MEM (EL n' l) fL’ by METIS_TAC[MEM_EL] THEN
               ‘(HEAP_READ_ENTRY s hl (dse_const (dsv_const x)) (EL n' l) =
                  SOME (DS_EXPRESSION_EVAL s e3))’ by METIS_TAC[] THEN
               POP_ASSUM MP_TAC THEN
               SIMP_TAC std_ss [HEAP_READ_ENTRY_THM] THEN
               ASM_SIMP_TAC std_ss [HEAP_READ_ENTRY_def, DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def,
                  DRESTRICT_DEF, IN_INTER, IN_SING]
            ]
         ]
      ]
   ) THEN


   ‘DISJOINT (FDOM hl) (FDOM h)’ by (
      Q.PAT_X_ASSUM ‘DISJOINT (FDOM hl) (IMAGE f X)’ MP_TAC THEN
      SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
         IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN
      CCONTR_TAC THEN
      FULL_SIMP_TAC std_ss [] THEN
      ‘dse_const (dsv_const x) IN X’ by (
         Q.UNABBREV_TAC ‘X’ THEN
         ASM_SIMP_TAC std_ss [IN_INSERT, IN_UNION, IN_IMAGE] THEN
         METIS_TAC[]
      ) THEN
      ‘~(x = DS_EXPRESSION_EVAL_VALUE s (dse_const (dsv_const x)))’ by METIS_TAC[] THEN
      POP_ASSUM MP_TAC THEN
      ASM_REWRITE_TAC[DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def, DS_EXPRESSION_EVAL_VALUE_def]
   ) THEN

   ‘DISJOINT (FDOM hl) (FDOM h''')’ by (
      SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
      GEN_TAC THEN
      Cases_on ‘x IN FDOM hl’ THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC std_ss [DRESTRICT_DEF, IN_INTER, IN_COMPL, FUNION_DEF,
         IN_UNION, IN_SING] THEN
      CCONTR_TAC THEN FULL_SIMP_TAC std_ss [] THEN
      MP_TAC (Q.SPECL [‘s’, ‘h'''’, ‘sf'''’, ‘x’] SF_EXPRESSION_SET___FDOM_HEAP) THEN
      ASM_SIMP_TAC std_ss [DRESTRICT_DEF, FUNION_DEF, IN_INTER, IN_UNION, IN_SING, IN_COMPL] THEN
      CONJ_TAC THENL [
         STRIP_TAC THEN
         Cases_on ‘e IN SF_EXPRESSION_SET sf'''’ THEN ASM_REWRITE_TAC[] THEN
         ‘e IN X’ by (
            Q.UNABBREV_TAC ‘X’ THEN
            ASM_SIMP_TAC std_ss [IN_UNION, IN_INSERT]
         ) THEN
         ‘~(DS_EXPRESSION_EVAL_VALUE s e IN FDOM hl)’ by METIS_TAC[] THEN
         POP_ASSUM MP_TAC THEN
         SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def] THEN
         METIS_TAC[GET_DSV_VALUE_def],


         REPEAT STRIP_TAC THEN
         Cases_on ‘x' = w’ THEN ASM_REWRITE_TAC[] THEN
         Cases_on ‘x' IN FDOM h'’ THEN ASM_REWRITE_TAC[] THEN
         ‘~(x' = v)’ by METIS_TAC[] THEN ASM_REWRITE_TAC[] THEN
         Cases_on ‘x' IN FDOM hl’ THEN ASM_REWRITE_TAC[] THENL [
            ASM_SIMP_TAC list_ss [] THEN
            Cases_on ‘MEM f fL’ THEN ASM_REWRITE_TAC[] THEN
            ‘HEAP_READ_ENTRY s hl (dse_const (dsv_const x')) f =
               SOME (DS_EXPRESSION_EVAL s e3)’ by METIS_TAC[] THEN
            POP_ASSUM MP_TAC THEN
            SIMP_TAC std_ss [HEAP_READ_ENTRY_THM] THEN
            ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, IS_DSV_NIL_def, GET_DSV_VALUE_def] THEN
            ‘e3 IN X’ by (
               Q.UNABBREV_TAC ‘X’ THEN
               ASM_SIMP_TAC std_ss [IN_UNION, IN_INSERT]
            ) THEN
            METIS_TAC[GET_DSV_VALUE_def, DS_EXPRESSION_EVAL_VALUE_def],


            Cases_on ‘x' IN FDOM h’ THEN ASM_REWRITE_TAC[] THEN
            Cases_on ‘f IN (FDOM (h ' x'))’ THEN ASM_REWRITE_TAC[] THEN
            ‘dse_const (h ' x' ' f) IN X’ by (
               Q.UNABBREV_TAC ‘X’ THEN
               ASM_SIMP_TAC std_ss [IN_UNION, IN_INSERT, IN_BIGUNION, IN_IMAGE, FRANGE_DEF,
                  GSPECIFICATION, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
               METIS_TAC[]
            ) THEN
            CCONTR_TAC  THEN
            ‘~(DS_EXPRESSION_EVAL_VALUE s (dse_const (h ' x' ' f)) IN FDOM hl)’ by METIS_TAC[] THEN
            POP_ASSUM MP_TAC THEN
            SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def, DS_EXPRESSION_EVAL_def] THEN
            FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def]
         ]
      ]
   ) THEN

   ‘h''' SUBMAP h’ by (
      SIMP_TAC std_ss [SUBMAP_DEF] THEN
      GEN_TAC THEN STRIP_TAC THEN
      ‘~(x IN FDOM hl)’ by (
         FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
         PROVE_TAC[]
      ) THEN
      Q.PAT_X_ASSUM ‘x IN FDOM h'''’ MP_TAC THEN
      ASM_SIMP_TAC std_ss [SUBMAP_DEF, DRESTRICT_DEF, IN_INTER,
         IN_DIFF, FUNION_DEF, IN_UNION, IN_SING, IN_COMPL] THEN
      METIS_TAC[]
   ) THEN

   ‘!x. MEM x fL ==> MEM x l’ by (
      REPEAT STRIP_TAC THEN
      CCONTR_TAC THEN
      ‘?y. y IN FDOM hl /\ (h2 ' v ' x = dsv_const y)’ by METIS_TAC[] THEN
      ‘~(y IN (FDOM h'''))’ by (
         FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
         METIS_TAC[]
      ) THEN
      ‘y IN FDOM (FUNION hl1 (DRESTRICT h' (FDOM hl)))’ by (
         POP_ASSUM MP_TAC THEN
         ASM_SIMP_TAC std_ss [FUNION_DEF, IN_UNION, DRESTRICT_DEF, IN_INTER, IN_COMPL]
      ) THEN
      Q.PAT_X_ASSUM ‘~(y IN FDOM h''')’ MP_TAC THEN
      ASM_SIMP_TAC std_ss [DRESTRICT_DEF, IN_INTER, IN_COMPL, FUNION_DEF, IN_UNION,
         IN_SING] THEN
      CCONTR_TAC THEN (
         Q.PAT_X_ASSUM ‘y IN FDOM Y’ MP_TAC THEN
         FULL_SIMP_TAC std_ss [DRESTRICT_DEF, IN_INTER,
            prove (“!x f. x IN (\x. f x) = f x”, SIMP_TAC std_ss [IN_DEF])] THEN
         METIS_TAC[GET_DSV_VALUE_def]
      )
   ) THEN
   ‘PERM l fL’ by METIS_TAC[PERM_ALL_DISTINCT] THEN
   ‘!s h es e. SF_SEM___sf_tree s h l es e =
               SF_SEM___sf_tree s h fL es e’ by (
      SIMP_TAC std_ss [SF_SEM___sf_tree_def] THEN
      METIS_TAC[SF_SEM___sf_tree_len_PERM_THM]
   ) THEN

   ‘(FUNION h2 hl) SUBMAP (FUNION hl1 h')’ by (
      SIMP_TAC std_ss [SUBMAP_DEF, IMP_CONJ_THM, FORALL_AND_THM] THEN
      MATCH_MP_TAC (prove (“(a ==> b) /\ a ==> (a /\ b)”, METIS_TAC[])) THEN
      CONJ_TAC THEN1 (
         REPEAT STRIP_TAC THEN
         ‘x IN FDOM (FUNION hl1 h')’ by PROVE_TAC[] THEN
         Q.PAT_X_ASSUM ‘h' SUBMAP YYY’ MP_TAC THEN
         ASM_SIMP_TAC std_ss [SUBMAP_DEF, FUNION_DEF, IN_SING, IN_UNION] THEN
         STRIP_TAC THEN
         Q.PAT_X_ASSUM ‘x IN FDOM (FUNION h2 hl)’ MP_TAC THEN
         Cases_on ‘x = v’ THEN (
            ASM_SIMP_TAC std_ss [IN_SING, IN_UNION, FUNION_DEF, DISJ_IMP_THM]
         ) THEN
         STRIP_TAC THEN
         Cases_on ‘x = w’ THEN1 METIS_TAC[SUBMAP_DEF, IN_SING] THEN

         Q.PAT_X_ASSUM ‘x IN FDOM (FUNION hl1 h')’ MP_TAC THEN
         SIMP_TAC std_ss [FUNION_DEF, IN_UNION, IN_SING] THEN
         ASM_SIMP_TAC std_ss [IN_SING]
      ) THEN

      ASM_SIMP_TAC std_ss [FUNION_DEF, IN_UNION, IN_SING, DISJ_IMP_THM] THEN
      REPEAT STRIP_TAC THEN
      CCONTR_TAC THEN
      FULL_SIMP_TAC std_ss [] THEN
      ‘~(x IN FDOM h''')’ by (
         FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
         METIS_TAC[]
      ) THEN
      POP_ASSUM MP_TAC THEN
      ASM_SIMP_TAC std_ss [DRESTRICT_DEF, IN_INTER, IN_COMPL, FUNION_DEF, IN_UNION, IN_SING]
   ) THEN

   ‘?h''. h'' = DRESTRICT h (COMPL (FDOM h'''))’ by METIS_TAC[] THEN
   ‘FUNION hl1 h' = FUNION (FUNION h2 hl) h''’ by (
      SIMP_TAC std_ss [GSYM fmap_EQ_THM] THEN
      MATCH_MP_TAC (prove (“(a ==> b) /\ a ==> (a /\ b)”, METIS_TAC[])) THEN
      CONJ_TAC THEN1 (
         Q.PAT_X_ASSUM ‘h' SUBMAP YYY’ MP_TAC THEN
         ASM_SIMP_TAC std_ss [IN_UNION, FUNION_DEF, IN_SING, DRESTRICT_DEF,
            IN_INTER, IN_COMPL, SUBMAP_DEF] THEN
         STRIP_TAC THEN STRIP_TAC THEN GEN_TAC THEN
         Cases_on ‘x = v’ THEN1 (
            ASM_SIMP_TAC std_ss []
         ) THEN
         ASM_SIMP_TAC std_ss [] THEN
         Cases_on ‘x = w’ THEN1 (
            ASM_SIMP_TAC std_ss [] THEN
            METIS_TAC[IN_SING, SUBMAP_DEF]
         ) THEN
         ASM_SIMP_TAC std_ss [] THEN
         Cases_on ‘x IN FDOM hl’ THEN1 (
            ASM_SIMP_TAC std_ss []
         ) THEN
         ASM_SIMP_TAC std_ss [] THEN
         Cases_on ‘x IN FDOM h’ THEN1 (
            ASM_SIMP_TAC std_ss []
         ) THEN
         METIS_TAC[]
      ) THEN



      Q.PAT_X_ASSUM ‘FUNION h2 hl SUBMAP YYY’ MP_TAC THEN
      ASM_SIMP_TAC std_ss [SUBMAP_DEF, FUNION_DEF, IN_UNION, EXTENSION, IN_SING,
         DRESTRICT_DEF, IN_INTER, IN_COMPL, IMP_CONJ_THM, FORALL_AND_THM, DISJ_IMP_THM] THEN
      REPEAT STRIP_TAC THEN
      Cases_on ‘x = v’ THEN1 (
         ASM_SIMP_TAC std_ss []
      ) THEN
      Cases_on ‘x = w’ THEN1 (
         ASM_SIMP_TAC std_ss []
      ) THEN
      ASM_SIMP_TAC std_ss [] THEN
      Cases_on ‘x IN FDOM h'’ THEN1 (
         Q.PAT_X_ASSUM ‘h' SUBMAP YYY’ MP_TAC THEN
         ASM_SIMP_TAC std_ss [SUBMAP_DEF, FUNION_DEF, IN_UNION, IN_SING] THEN
         METIS_TAC[]
      ) THEN
      ‘~(x IN FDOM hl)’ by METIS_TAC[] THEN
      ASM_SIMP_TAC std_ss []
   ) THEN


   FULL_SIMP_TAC std_ss [SF_SEM___EXTEND_def, SF_SEM_def, SF_EQUIV_def] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (Q.SPECL [‘s’, ‘FUNION h2 hl’, ‘h''’, ‘fL’, ‘d’, ‘d0’, ‘e3’, ‘e2’] SUBTREE_EXCHANGEABLE_THM) THEN
   MATCH_MP_TAC (prove (“(a /\ (b ==> c)) ==> ((a ==> b) ==> c)”, METIS_TAC[])) THEN
   CONJ_TAC THEN1 (
      FULL_SIMP_TAC std_ss [SF_SEM_def] THEN
      REPEAT STRIP_TAC THENL [
         SIMP_TAC std_ss [SF_SEM___sf_tree_def] THEN
         METIS_TAC[BALANCED_SF_SEM___sf_tree_len_THM],

         Q.PAT_X_ASSUM ‘DISJOINT (FDOM hl) (FDOM h)’ MP_TAC THEN
         Q.PAT_X_ASSUM ‘~(v IN FDOM h)’ MP_TAC THEN
         ASM_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, FUNION_DEF,
            DRESTRICT_DEF, IN_UNION, IN_SING] THEN
         REPEAT (POP_ASSUM (K ALL_TAC)) THEN
         METIS_TAC[]
      ]
   ) THEN

   SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
   Q.EXISTS_TAC ‘h''''’ THEN
   MATCH_MP_TAC (prove (“(a /\ (b ==> c)) ==> ((a ==> b) ==> c)”, METIS_TAC[])) THEN
   CONJ_TAC THEN1 (
      ‘DS_POINTER_DANGLES s h'''' d’ suffices_by (STRIP_TAC THEN
         ASM_SIMP_TAC std_ss [SF_SEM_def] THEN
         Q.PAT_X_ASSUM ‘DISJOINT (FDOM h) (FDOM h'''')’ MP_TAC THEN
         REPEAT (POP_ASSUM (K ALL_TAC)) THEN
         SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, FUNION_DEF,
               DRESTRICT_DEF, IN_UNION] THEN
         METIS_TAC[]
      ) THEN

      Cases_on ‘DS_EXPRESSION_EQUAL s d e3’ THEN1 (
         ‘DS_POINTER_DANGLES s h'''' e3’ by METIS_TAC[LEMMA_3_1_1, SF_SEM_def] THEN
         FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, DS_EXPRESSION_EQUAL_def]
      ) THEN
      SIMP_TAC std_ss [DS_POINTER_DANGLES] THEN
      Cases_on ‘DS_EXPRESSION_EVAL s d’ THEN ASM_SIMP_TAC std_ss [IS_DSV_NIL_def, GET_DSV_VALUE_def] THEN
      ‘v' IN FDOM h’ suffices_by (STRIP_TAC THEN
         FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
         METIS_TAC[]
      ) THEN

      CCONTR_TAC THEN
      Q.PAT_X_ASSUM ‘!h:('b, 'c) heap. (P h ==> Q h)’ MP_TAC THEN
      SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
         GSYM LEFT_EXISTS_IMP_THM] THEN

      ‘?hx.
         BALANCED_SF_SEM___sf_tree_len s hx fL 2 e3 e2 /\
         (DISJOINT (FDOM hx) (FDOM h)) /\
         (v' IN FDOM hx)’ by (

         MP_TAC (Q.SPECL [‘s’, ‘fL’, ‘e3’, ‘e2’, ‘v'’, ‘FDOM (h:('b, 'c) heap)’]
            BALANCED_SF_SEM___sf_tree_len_2___MODEL_EXISTS_WITH_ELEMENT) THEN
         MATCH_MP_TAC (prove (“(a /\ (b ==> c)) ==> ((a ==> b) ==> c)”, METIS_TAC[])) THEN
         CONJ_TAC THEN1 (
            FULL_SIMP_TAC std_ss [IS_DSV_NIL_def, FDOM_FINITE, DS_EXPRESSION_EQUAL_def,
               DS_EXPRESSION_EVAL_def]
         ) THEN
         STRIP_TAC THEN
         Q.EXISTS_TAC ‘h'''''’ THEN
         Q.PAT_X_ASSUM ‘DISJOINT Y (FDOM h)’ MP_TAC THEN
         ASM_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
            IN_DIFF, IN_SING, DS_EXPRESSION_EVAL_VALUE_def, GET_DSV_VALUE_def] THEN
         METIS_TAC[]
      ) THEN


      Q.EXISTS_TAC ‘hx’ THEN
      Q.EXISTS_TAC ‘h’ THEN
      ASM_SIMP_TAC std_ss [] THEN
      REPEAT STRIP_TAC THEN
      CCONTR_TAC THEN
      FULL_SIMP_TAC std_ss [] THEN

      ‘~(v' IN FDOM h1')’ by (
         ‘DS_POINTER_DANGLES s h1' d’ by METIS_TAC[LEMMA_3_1_1, SF_SEM_def] THEN
         POP_ASSUM MP_TAC THEN
         ASM_SIMP_TAC std_ss [DS_POINTER_DANGLES, GET_DSV_VALUE_def, IS_DSV_NIL_def]
      ) THEN
      ‘v' IN FDOM h2''’ by (
         ‘v' IN FDOM (FUNION hx h)’ by ASM_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION] THEN
         POP_ASSUM MP_TAC THEN
         ASM_SIMP_TAC std_ss [] THEN
         ASM_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION]
      ) THEN
      ‘h2'' = h'''’ by (
         ‘SF_IS_PRECISE sf'''’ by REWRITE_TAC[SF_IS_PRECISE_THM] THEN
         FULL_SIMP_TAC std_ss [SF_IS_PRECISE_def] THEN
         POP_ASSUM MATCH_MP_TAC THEN
         Q.EXISTS_TAC ‘s’ THEN
         Q.EXISTS_TAC ‘FUNION hx h’ THEN
         REPEAT STRIP_TAC THENL [
            ASM_SIMP_TAC std_ss [SUBMAP___FUNION___ID],
            METIS_TAC[SUBMAP___FUNION___ID, SUBMAP_TRANS],
            ASM_SIMP_TAC std_ss [],
            ASM_SIMP_TAC std_ss []
         ]
      ) THEN
      METIS_TAC[SUBMAP_DEF]
   ) THEN

   STRIP_TAC THEN
   Q.EXISTS_TAC ‘FUNION h'''' h''’ THEN
   Q.EXISTS_TAC ‘h'''’ THEN

   Q.PAT_X_ASSUM ‘h''' = YYY’ (K ALL_TAC) THEN
   ‘DISJOINT (FDOM h'') (FDOM h''') /\ (h = (FUNION h'' h'''))’ by (
      Q.PAT_X_ASSUM ‘h''' SUBMAP h’ MP_TAC THEN
      ONCE_ASM_REWRITE_TAC[] THEN
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      SIMP_TAC std_ss [SUBMAP_DEF, DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
         DRESTRICT_DEF, IN_COMPL, GSYM fmap_EQ_THM, FUNION_DEF, IN_UNION] THEN
      METIS_TAC[]
   ) THEN
   REPEAT STRIP_TAC THENL [
      NTAC 2 (POP_ASSUM MP_TAC) THEN
      Q.PAT_X_ASSUM ‘DISJOINT (FDOM h) (FDOM h'''')’ MP_TAC THEN
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
      SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, IN_UNION, EXTENSION] THEN
      METIS_TAC[],

      Q.PAT_X_ASSUM ‘DISJOINT (FDOM h) (FDOM h'''')’ MP_TAC THEN
      Q.PAT_X_ASSUM ‘h = YYY’ (fn thm => (REWRITE_TAC [thm])) THEN
      SIMP_TAC std_ss [FDOM_FUNION, DISJOINT_UNION_BOTH, DISJOINT_SYM] THEN
      ASM_SIMP_TAC std_ss [],

      METIS_TAC[SF_SEM_def],

      ASM_REWRITE_TAC[]
   ],

   FULL_SIMP_TAC std_ss [SF_IS_SIMPLE_def]
]
QED

Definition HEAP_DISTINCT_def:
  HEAP_DISTINCT s h c d =
  (!e. MEM e c ==> ~(IS_DSV_NIL (DS_EXPRESSION_EVAL s e)) /\
                   ~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) IN FDOM h)) /\
  ALL_DISTINCT (MAP (\e. DS_EXPRESSION_EVAL_VALUE s e) c) /\


  (!e1 e2. MEM (e1,e2) d ==>
           DS_EXPRESSION_EQUAL s e1 e2 \/
           (~(IS_DSV_NIL (DS_EXPRESSION_EVAL s e1)) /\
            ~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1) IN FDOM h))) /\

  ALL_DISTINCT (MAP (λ(e1,e2). DS_EXPRESSION_EVAL_VALUE s e1)
                (FILTER (λ(e1,e2). ~(DS_EXPRESSION_EQUAL s e1 e2)) d)) /\

  (!e1 e2 e3. MEM e1 c /\ MEM (e2,e3) d ==>
              (DS_EXPRESSION_EQUAL s e2 e3 \/
               ~(DS_EXPRESSION_EQUAL s e1 e2)))
End




val HEAP_DISTINCT___IND_DEF = store_thm ("HEAP_DISTINCT___IND_DEF",
“ (!s h. HEAP_DISTINCT s h [] [] = T) /\
   (!s h e c. HEAP_DISTINCT s h (e::c) d = (HEAP_DISTINCT s h c d /\
                                         ~(IS_DSV_NIL (DS_EXPRESSION_EVAL s e)) /\
                                         ~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s e) IN FDOM h) /\
                                         (!e'. MEM e' c ==> (~(DS_EXPRESSION_EQUAL s e e'))) /\
                                         (!e1 e2. MEM (e1,e2) d ==> (
                                                            DS_EXPRESSION_EQUAL s e1 e2 \/
                                                            ~(DS_EXPRESSION_EQUAL s e e1))))) /\

   (!s h e1 e2 c. HEAP_DISTINCT s h c ((e1,e2)::d) = (HEAP_DISTINCT s h c d /\
                                         ((DS_EXPRESSION_EQUAL s e1 e2) \/

                                         (
                                         ~(IS_DSV_NIL (DS_EXPRESSION_EVAL s e1)) /\
                                         ~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1) IN FDOM h) /\
                                         (!e1' e2'. MEM (e1', e2') d ==>
                                                           ((DS_EXPRESSION_EQUAL s e1' e2') \/
                                                           (~(DS_EXPRESSION_EQUAL s e1 e1')))) /\

                                         (!e'. MEM e' c ==> (~(DS_EXPRESSION_EQUAL s e1 e')))))))”,


REPEAT CONJ_TAC THENL [
   SIMP_TAC list_ss [HEAP_DISTINCT_def],

   SIMP_TAC list_ss [HEAP_DISTINCT_def, MEM_MAP, DISJ_IMP_THM, FORALL_AND_THM,
      LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, DS_EXPRESSION_EVAL_VALUE_def, DS_EXPRESSION_EQUAL_def] THEN
   REPEAT STRIP_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   METIS_TAC[GET_DSV_VALUE_11],


   SIMP_TAC list_ss [HEAP_DISTINCT_def, MEM_MAP, DISJ_IMP_THM, FORALL_AND_THM,
      LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, DS_EXPRESSION_EVAL_VALUE_def, DS_EXPRESSION_EQUAL_def] THEN
   REPEAT STRIP_TAC THEN
   Cases_on ‘DS_EXPRESSION_EVAL s e1 = DS_EXPRESSION_EVAL s e2’ THENL [
      ASM_SIMP_TAC std_ss [] THEN
      EQ_TAC THEN STRIP_TAC THEN (
          ASM_SIMP_TAC std_ss [] THEN
          ASM_REWRITE_TAC[]
      ),

      ASM_SIMP_TAC list_ss [MEM_MAP, MEM_FILTER] THEN
      pairLib.GEN_BETA_TAC THEN
      EQ_TAC THEN STRIP_TAC THENL [
          ASM_SIMP_TAC std_ss [] THEN
          REPEAT STRIP_TAC THEN
          RES_TAC THENL [
            ASM_SIMP_TAC std_ss [],


            Q.PAT_X_ASSUM ‘!y :('e, 'd) ds_expression # ('e, 'd) ds_expression. P y’
               (fn thm => MP_TAC (Q.SPECL [‘(e1', e2')’] thm)) THEN
            ASM_SIMP_TAC std_ss [DISJ_IMP_THM, GET_DSV_VALUE_11]
          ],


          ASM_SIMP_TAC std_ss [] THEN
          Cases_on ‘y’ THEN
          SIMP_TAC std_ss [] THEN
          METIS_TAC[GET_DSV_VALUE_11]
      ]
   ]
])


val HEAP_DISTINCT___FUNION = store_thm ("HEAP_DISTINCT___FUNION",
“!s h1 h2 e c d.
      HEAP_DISTINCT s (FUNION h1 h2) c d =
      HEAP_DISTINCT s h1 c d /\ HEAP_DISTINCT s h2 c d”,

SIMP_TAC std_ss [HEAP_DISTINCT_def, FDOM_FUNION, IN_UNION, DS_POINTER_DANGLES] THEN
METIS_TAC[]);


val HEAP_DISTINCT___PERM = store_thm ("HEAP_DISTINCT___PERM",
“!s h c1 c2 d1 d2. (PERM c1 c2 /\ PERM d1 d2) ==>
              (HEAP_DISTINCT s h c1 d1 = HEAP_DISTINCT s h c2 d2)”,


SIMP_TAC std_ss [HEAP_DISTINCT_def] THEN
REPEAT STRIP_TAC THEN
‘!x. MEM x c2 = MEM x c1’ by METIS_TAC[PERM_MEM_EQ] THEN
‘!x. MEM x d2 = MEM x d1’ by METIS_TAC[PERM_MEM_EQ] THEN
ASM_SIMP_TAC std_ss [] THEN
STRIP_EQ_BOOL_TAC THEN
BINOP_TAC THENL [
   MATCH_MP_TAC ALL_DISTINCT___PERM THEN
   MATCH_MP_TAC PERM_MAP THEN
   ASM_REWRITE_TAC[],

   MATCH_MP_TAC ALL_DISTINCT___PERM THEN
   MATCH_MP_TAC PERM_MAP THEN
   MATCH_MP_TAC PERM_FILTER THEN
   ASM_REWRITE_TAC[]
])




val HEAP_DISTINCT___dse_nil = store_thm ("HEAP_DISTINCT___dse_nil",
   “!s h c d x. MEM x c /\ (HEAP_DISTINCT s h c d) ==>
                 ~(DS_EXPRESSION_EQUAL s x dse_nil)”,

SIMP_TAC std_ss [HEAP_DISTINCT_def, DS_EXPRESSION_EQUAL_def, dse_nil_def, DS_EXPRESSION_EVAL_def] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN
METIS_TAC[IS_DSV_NIL_def]);




val HEAP_DISTINCT___NOT_ALL_DISTINCT = store_thm ("HEAP_DISTINCT___NOT_ALL_DISTINCT",
   “!s h c d n1 n2. ((n1 < LENGTH c) /\ (n2 < LENGTH c) /\ ~(n1 = n2) /\ (EL n1 c = EL n2 c)) ==>
             ~(HEAP_DISTINCT s h c d)”,

SIMP_TAC list_ss [HEAP_DISTINCT_def, EL_ALL_DISTINCT_EQ] THEN
REPEAT STRIP_TAC THEN
DISJ2_TAC THEN DISJ1_TAC THEN
Q.EXISTS_TAC ‘n1’ THEN
Q.EXISTS_TAC ‘n2’ THEN
ASM_SIMP_TAC std_ss [EL_MAP])



val HEAP_DISTINCT___NOT_ALL_DISTINCT2 = store_thm ("HEAP_DISTINCT___NOT_ALL_DISTINCT2",
   “!s h c d n1 n2. ((n1 < LENGTH d) /\ (n2 < LENGTH d) /\ ~(n1 = n2) /\ (EL n1 d = EL n2 d) /\
             (HEAP_DISTINCT s h c d)) ==> DS_EXPRESSION_EQUAL s (FST (EL n1 d)) (SND (EL n1 d))”,

SIMP_TAC list_ss [HEAP_DISTINCT_def, EL_ALL_DISTINCT_EQ] THEN
REPEAT STRIP_TAC THEN
CCONTR_TAC THEN
MP_TAC (Q.ISPECL [‘n1:num’, ‘n2:num’, ‘(\(e1:('b, 'a) ds_expression,e2). ~DS_EXPRESSION_EQUAL s e1 e2)’, ‘d:(('b, 'a) ds_expression # ('b, 'a) ds_expression) list’] EL_DISJOINT_FILTER) THEN
ASM_SIMP_TAC std_ss [] THEN
pairLib.GEN_BETA_TAC THEN
ASM_REWRITE_TAC[] THEN
CCONTR_TAC THEN
FULL_SIMP_TAC std_ss [EL_MAP] THEN
Q.PAT_X_ASSUM ‘!n1 (n2:num). P n1 n2’ (fn thm => MP_TAC (Q.SPECL [‘n1'’, ‘n2'’] thm)) THEN
pairLib.GEN_BETA_TAC THEN
ASM_REWRITE_TAC[])



val HEAP_DISTINCT___EQUAL = store_thm ("HEAP_DISTINCT___EQUAL",
   “!s h c d e. HEAP_DISTINCT s h c ((e,e)::d) =
                 HEAP_DISTINCT s h c d”,

   SIMP_TAC std_ss [HEAP_DISTINCT___IND_DEF, DS_EXPRESSION_EQUAL_def])


val HEAP_DISTINCT___UNEQUAL = store_thm ("HEAP_DISTINCT___UNEQUAL",
   “!s h c d e1 e2. ~(DS_EXPRESSION_EQUAL s e1 e2) ==>

                 (HEAP_DISTINCT s h c ((e1,e2)::d) =
                  HEAP_DISTINCT s h (e1::c) d)”,

   SIMP_TAC std_ss [HEAP_DISTINCT___IND_DEF] THEN
   METIS_TAC[])



val LIST_DS_ENTAILS_def = Define
   ‘LIST_DS_ENTAILS c l1 l2 =
      !s h. (HEAP_DISTINCT s h (FST c) (SND c) /\ LIST_DS_SEM s h l1) ==> LIST_DS_SEM s h l2’



val LIST_DS_ENTAILS___PERM = store_thm (
"LIST_DS_ENTAILS___PERM",
“!c1 c2 pf sf pf' sf' c12 c22 pf2 sf2 pf2' sf2'.

((PERM c1 c12) /\ (PERM c2 c22) /\ (PERM pf pf2) /\ (PERM sf sf2) /\ (PERM pf' pf2') /\ (PERM sf' sf2')) ==>

(LIST_DS_ENTAILS (c1,c2) (pf, sf) (pf', sf') =
LIST_DS_ENTAILS (c12,c22) (pf2, sf2) (pf2', sf2'))”,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_def] THEN
REPEAT STRIP_TAC THEN
‘(!s h. (LIST_SF_SEM s h sf = LIST_SF_SEM s h sf2)) /\
 (!s h. (LIST_SF_SEM s h sf' = LIST_SF_SEM s h sf2'))’ by (
   ASM_SIMP_TAC std_ss [LIST_SF_SEM_PERM]
) THEN
‘(!s. (LIST_PF_SEM s pf = LIST_PF_SEM s pf2)) /\
 (!s. (LIST_PF_SEM s pf' = LIST_PF_SEM s pf2'))’ by (
   ASM_SIMP_TAC std_ss [LIST_PF_SEM_PERM]
) THEN
‘!s (h:('a, 'c) heap). HEAP_DISTINCT s h c1 c2 = HEAP_DISTINCT s h c12 c22’ by
   ASM_SIMP_TAC std_ss [HEAP_DISTINCT___PERM] THEN
ASM_SIMP_TAC std_ss []);




(*Normalization Rules*)

val INFERENCE_INCONSISTENT = store_thm ("INFERENCE_INCONSISTENT",
“!e c1 c2 pfL sfL pfL' sfL'. LIST_DS_ENTAILS (c1,c2) ((pf_unequal e e)::pfL, sfL) (sfL', pfL')”,
SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_EVAL,
   DS_EXPRESSION_EQUAL_def]);




val INFERENCE_SUBSTITUTION = store_thm ("INFERENCE_SUBSTITUTION",
“!e c1 c2 v pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS (MAP (DS_VAR_SUBST v e) c1, MAP (\x. (DS_VAR_SUBST v e (FST x), DS_VAR_SUBST v e (SND x))) c2) (MAP (PF_SUBST v e) pfL, MAP (SF_SUBST v e) sfL) (MAP (PF_SUBST v e) pfL', MAP (SF_SUBST v e) sfL') =
      LIST_DS_ENTAILS (c1,c2) ((pf_equal (dse_var v) e)::pfL, sfL) (pfL', sfL')”,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_def,
   DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def,
   LIST_PF_SUBST_SEM, LIST_SF_SUBST_SEM, LIST_PF_SEM_THM,
   PF_SEM_def, MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
   DS_POINTER_DANGLES, DS_VAR_SUBST_SEM, DS_EXPRESSION_EVAL_VALUE_def,
   MAP_MAP_o, combinTheory.o_DEF, HEAP_DISTINCT_def,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, FILTER_MAP] THEN
SIMP_TAC std_ss [PAIR_BETA_THM] THEN
SIMP_TAC std_ss [GSYM pairTheory.PFORALL_THM, GSYM pairTheory.PEXISTS_THM] THEN
REPEAT GEN_TAC THEN
EQ_TAC THEN STRIP_TAC THENL [
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   Q.PAT_X_ASSUM ‘!s h. P s h ==> Q1 s h /\ Q2 s h’ (fn thm => (MP_TAC (Q.SPECL [‘s’, ‘h’] thm))) THEN
   ‘(\x. (if x = v then DS_EXPRESSION_EVAL s e else s x)) = s’ by (
      ASM_SIMP_TAC std_ss [FUN_EQ_THM, COND_RATOR, COND_RAND]
   ) THEN
   ASM_SIMP_TAC std_ss [],


   REPEAT GEN_TAC THEN STRIP_TAC THEN
   Q.PAT_X_ASSUM ‘!s h. P s h ==> (LIST_PF_SEM s pfL' /\ Z)’ (fn thm => (MP_TAC (Q.SPECL [‘\x. (if x = v then DS_EXPRESSION_EVAL s e else s x)’, ‘h’] thm))) THEN
   ASM_SIMP_TAC std_ss [] THEN
   Cases_on ‘e’ THENL [
      SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def],
      SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, COND_RATOR, COND_RAND]
   ]
]);



val INFERENCE_REFLEXIVE_L = store_thm ("INFERENCE_REFLEXIVE_L",
“!e c1 c2 pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS (c1,c2) (pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) ((pf_equal e e)::pfL, sfL) (pfL', sfL')”,
SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_THM,
   DS_EXPRESSION_EQUAL_def, PF_SEM_def]);




val INFERENCE_NIL_NOT_LVAL___points_to = store_thm ("INFERENCE_NIL_NOT_LVAL___points_to",
“!e c1 c2 a pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS (c1,c2) ((pf_unequal e dse_nil)::pfL, (sf_points_to e a)::sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_points_to e a)::sfL) (pfL', sfL')”,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_THM,
   DS_EXPRESSION_EQUAL_def, DS_POINTS_TO_def, DS_EXPRESSION_EVAL_def,
   IS_DSV_NIL_THM, dse_nil_def, SF_SEM_def, PF_SEM_def] THEN
METIS_TAC[]);



val INFERENCE_NIL_NOT_LVAL___tree = store_thm ("INFERENCE_NIL_NOT_LVAL___tree",
“!e1 e2 fL c1 c2 pfL sfL pfL' sfL'.
      MEM_UNEQ_PF_LIST e1 e2 pfL ==>

      (LIST_DS_ENTAILS (c1,c2) ((pf_unequal e2 dse_nil)::pfL, (sf_tree fL e1 e2)::sfL) (pfL', sfL') =
       LIST_DS_ENTAILS (c1,c2) (pfL, (sf_tree fL e1 e2)::sfL) (pfL', sfL'))”,


SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_THM,
   DS_EXPRESSION_EQUAL_def, DS_POINTS_TO_def, DS_EXPRESSION_EVAL_def,
   IS_DSV_NIL_THM, dse_nil_def, SF_SEM_def, PF_SEM_def,
   SF_SEM___sf_tree_def] THEN
REPEAT STRIP_TAC THEN
REPEAT STRIP_EQ_FORALL_TAC THEN
STRIP_EQ_BOOL_TAC THEN
SIMP_TAC std_ss [] THEN
STRIP_EQ_BOOL_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
‘~(DS_EXPRESSION_EQUAL s e1 e2)’ by METIS_TAC[MEM_UNEQ_PF_LIST_SEM, LIST_DS_SEM_def] THEN
Cases_on ‘n’ THENL [
   FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def],

   FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_len_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def,
      IS_DSV_NIL_THM]
])



val INFERENCE_NIL_NOT_LVAL___list = store_thm ("INFERENCE_NIL_NOT_LVAL___list",
“!e1 e2 f c1 c2 pfL sfL pfL' sfL'.
      MEM_UNEQ_PF_LIST e2 e1 pfL ==>

      (LIST_DS_ENTAILS (c1,c2) ((pf_unequal e1 dse_nil)::pfL, (sf_ls f e1 e2)::sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_ls f e1 e2)::sfL) (pfL', sfL'))”,

SIMP_TAC std_ss [sf_ls_def] THEN
METIS_TAC[INFERENCE_NIL_NOT_LVAL___tree]);





val INFERENCE_PARTIAL___points_to___points_to = store_thm ("INFERENCE_PARTIAL___points_to___points_to",
“!e1 e2 a1 a2 c1 c2 pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS (c1,c2) ((pf_unequal e1 e2)::pfL, (sf_points_to e1 a1)::(sf_points_to e2 a2)::sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_points_to e1 a1)::(sf_points_to e2 a2)::sfL) (pfL', sfL')”,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_EVAL,
   DS_EXPRESSION_EQUAL_def, DS_POINTS_TO_def, DS_EXPRESSION_EVAL_def,
   IS_DSV_NIL_THM, dse_nil_def, FDOM_DOMSUB, IN_DELETE] THEN
METIS_TAC[GET_DSV_VALUE_11])



val INFERENCE_PARTIAL___points_to___tree = store_thm ("INFERENCE_PARTIAL___points_to___tree",
“!e1 e2 e3 e4 fL c1 c2 pfL sfL pfL' sfL'.
      MEM_UNEQ_PF_LIST e3 e4 pfL ==>
      (
      LIST_DS_ENTAILS (c1,c2) ((pf_unequal e1 e3)::pfL, (sf_points_to e1 e2)::(sf_tree fL e4 e3)::sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_points_to e1 e2)::(sf_tree fL e4 e3)::sfL) (pfL', sfL'))”,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_EVAL, DS_EXPRESSION_EQUAL_def] THEN
REPEAT STRIP_TAC THEN
REPEAT STRIP_EQ_FORALL_TAC THEN
STRIP_EQ_BOOL_TAC THEN
SIMP_TAC std_ss [] THEN
STRIP_EQ_BOOL_TAC THEN
‘~(DS_EXPRESSION_EQUAL s e3 e4)’ by METIS_TAC[MEM_UNEQ_PF_LIST_SEM, LIST_DS_SEM_def] THEN
FULL_SIMP_TAC std_ss [LIST_DS_SEM_EVAL, DS_EXPRESSION_EQUAL_def, LET_THM] THEN
FULL_SIMP_TAC std_ss [DS_POINTS_TO_def, FDOM_DOMSUB, IN_DELETE] THEN
METIS_TAC[])



val INFERENCE_PARTIAL___tree___tree = store_thm ("INFERENCE_PARTIAL___tree___tree",
“!e1 e2 e3 e4 fL fL' c1 c2 pfL sfL pfL' sfL'.
      (MEM_UNEQ_PF_LIST e1 e2 pfL /\ MEM_UNEQ_PF_LIST e3 e4 pfL) ==>

      (LIST_DS_ENTAILS (c1,c2) ((pf_unequal e1 e3)::pfL, (sf_tree fL e2 e1)::(sf_tree fL' e4 e3)::sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_tree fL e2 e1)::(sf_tree fL' e4 e3)::sfL) (pfL', sfL'))”,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_EVAL, DS_EXPRESSION_EQUAL_def] THEN
REPEAT STRIP_TAC THEN
REPEAT STRIP_EQ_FORALL_TAC THEN
STRIP_EQ_BOOL_TAC THEN
SIMP_TAC std_ss [] THEN
STRIP_EQ_BOOL_TAC THEN
‘~(DS_EXPRESSION_EQUAL s e1 e2)’ by METIS_TAC[MEM_UNEQ_PF_LIST_SEM, LIST_DS_SEM_def] THEN
‘~(DS_EXPRESSION_EQUAL s e3 e4)’ by METIS_TAC[MEM_UNEQ_PF_LIST_SEM, LIST_DS_SEM_def] THEN

FULL_SIMP_TAC std_ss [LIST_DS_SEM_EVAL, LET_THM, MAP_MAP_o] THEN
‘!(s :'b -> 'a ds_value) (h:('a,'c) heap) pfL sfL f (fL:'c list).
   LIST_DS_SEM s h (pfL, (MAP f fL) ++ sfL) =
   LIST_DS_SEM s h (pfL, sfL ++ (MAP f fL))’ by (
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC LIST_DS_SEM_PERM THEN
   SIMP_TAC std_ss [PERM_REFL, PERM_APPEND]
) THEN
FULL_SIMP_TAC list_ss [LIST_DS_SEM_EVAL, LET_THM] THEN
FULL_SIMP_TAC std_ss [DS_POINTS_TO_def, FDOM_DOMSUB, IN_DELETE] THEN
METIS_TAC[])



val INFERENCE_PARTIAL___precondition___points_to = store_thm ("INFERENCE_PARTIAL___precondition___points_to",
“!e1 e2 e3 c1 c2 pfL sfL pfL' sfL'.
      MEM e3 c1 ==>

      (LIST_DS_ENTAILS (c1,c2) ((pf_unequal e1 e3)::pfL, (sf_points_to e1 e2)::sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_points_to e1 e2)::sfL) (pfL', sfL'))”,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_EVAL,
   DS_EXPRESSION_EQUAL_def, DS_POINTS_TO_def, DS_EXPRESSION_EVAL_def,
   IS_DSV_NIL_THM, dse_nil_def, FDOM_DOMSUB, IN_DELETE] THEN
REPEAT STRIP_TAC THEN
REPEAT STRIP_EQ_FORALL_TAC THEN
STRIP_EQ_BOOL_TAC THEN
ASM_SIMP_TAC std_ss [] THEN
STRIP_EQ_BOOL_TAC THEN
METIS_TAC[HEAP_DISTINCT_def]
);


val INFERENCE_PARTIAL___precondition___tree = store_thm ("INFERENCE_PARTIAL___precondition___tree",
“!es e e' fL c1 c2 pfL sfL pfL' sfL'.
      (MEM e' c1 /\ MEM_UNEQ_PF_LIST e es pfL) ==>

      (LIST_DS_ENTAILS (c1,c2) ((pf_unequal e e')::pfL, (sf_tree fL es e)::sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_tree fL es e)::sfL) (pfL', sfL'))”,


SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_EVAL, DS_EXPRESSION_EQUAL_def] THEN
REPEAT STRIP_TAC THEN
REPEAT STRIP_EQ_FORALL_TAC THEN
STRIP_EQ_BOOL_TAC THEN
ASM_SIMP_TAC std_ss [] THEN
STRIP_EQ_BOOL_TAC THEN
FULL_SIMP_TAC std_ss [LIST_DS_SEM_THM] THEN
‘~((GET_DSV_VALUE (DS_EXPRESSION_EVAL s e')) IN FDOM h)’ by METIS_TAC[HEAP_DISTINCT_def] THEN
POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN
Q.PAT_X_ASSUM ‘SF_SEM s h1 Y’ MP_TAC THEN
‘~(DS_EXPRESSION_EQUAL s e es)’ by METIS_TAC[MEM_UNEQ_PF_LIST_SEM, LIST_DS_SEM_def] THEN
ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_THM, DS_EXPRESSION_EQUAL_def, LET_THM,
SF_SEM___sf_points_to_THM, DS_POINTS_TO_def, FDOM_FUNION, IN_UNION] THEN
METIS_TAC[])






val INFERENCE_EXCLUDED_MIDDLE = store_thm ("INFERENCE_EXCLUDED_MIDDLE",
“!e1:('b, 'a) ds_expression e2 c1 c2 pfL sfL pfL' sfL'.
      (LIST_DS_ENTAILS (c1,c2) ((pf_unequal e1 e2)::pfL, sfL) (pfL', sfL') /\
       LIST_DS_ENTAILS (c1,c2) ((pf_equal e1 e2)::pfL, sfL) (pfL', sfL'))
      =
      LIST_DS_ENTAILS (c1,c2) (pfL, sfL) (pfL', sfL')”,


SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_THM, PF_SEM_def] THEN
METIS_TAC[]);






val INFERENCE_EMP_TREE_L = store_thm ("INFERENCE_EMP_TREE_L",
“!e fL c1 c2 pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS (c1,c2) (pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_tree fL e e)::sfL) (pfL', sfL')”,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_THM] THEN
ONCE_REWRITE_TAC [SF_SEM___sf_tree_THM] THEN
SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def,
   DISJOINT_EMPTY, FDOM_FEMPTY, FUNION_FEMPTY_1])



val INFERENCE_EMP_BIN_TREE_L = store_thm ("INFERENCE_EMP_BIN_TREE_L",
“!f1 f2 c1 c2 pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS (c1,c2) (pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_bin_tree (f1,f2) dse_nil)::sfL) (pfL', sfL')”,

SIMP_TAC std_ss [sf_bin_tree_def] THEN
METIS_TAC[INFERENCE_EMP_TREE_L])



val INFERENCE_EMP_LIST_L = store_thm ("INFERENCE_EMP_LIST_L",
“!f e c1 c2 pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS (c1,c2) (pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_ls f e e)::sfL) (pfL', sfL')”,

SIMP_TAC std_ss [sf_ls_def] THEN
METIS_TAC[INFERENCE_EMP_TREE_L])







(*Subtraction Rules*)


val INFERENCE_AXIOM = store_thm ("INFERENCE_AXIOM",
“!pfL c1 c2. LIST_DS_ENTAILS (c1,c2) (pfL, []) ([], [])”,
SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_THM, LIST_SF_SEM_THM]);



val INFERENCE_REFLEXIVE_R = store_thm ("INFERENCE_REFLEXIVE_R",
“!e c1 c2 pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS (c1,c2) (pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, sfL) ((pf_equal e e)::pfL', sfL')”,
SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_EVAL,
   DS_EXPRESSION_EQUAL_def]);



val INFERENCE_HYPOTHESIS = store_thm ("INFERENCE_HYPOTHESIS",
“!pf c1 c2 pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS c (pf::pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS c (pf::pfL, sfL) (pf::pfL', sfL')”,
SIMP_TAC std_ss [LIST_DS_ENTAILS_def,
   LIST_DS_SEM_def, LIST_PF_SEM_THM] THEN
METIS_TAC[]);




val INFERENCE_EMP_TREE_R = store_thm ("INFERENCE_EMP_TREE_R",
“!e fL c1 c2 pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS (c1,c2) (pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, sfL) (pfL', (sf_tree fL e e)::sfL')”,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_THM] THEN
ONCE_REWRITE_TAC [SF_SEM___sf_tree_THM] THEN
SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def,
   DISJOINT_EMPTY, FDOM_FEMPTY, FUNION_FEMPTY_1])



val INFERENCE_EMP_BIN_TREE_R = store_thm ("INFERENCE_EMP_BIN_TREE_R",
“!f1 f2 c1 c2 pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS (c1,c2) (pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, sfL) (pfL', (sf_bin_tree (f1,f2) dse_nil)::sfL')”,

SIMP_TAC std_ss [sf_bin_tree_def] THEN
METIS_TAC[INFERENCE_EMP_TREE_R])



val INFERENCE_EMP_LIST_R = store_thm ("INFERENCE_EMP_LIST_R",
“!f e c1 c2 pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS (c1,c2) (pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, sfL) (pfL', (sf_ls f e e)::sfL')”,

SIMP_TAC std_ss [sf_ls_def] THEN
METIS_TAC[INFERENCE_EMP_TREE_R]);





val INFERENCE_STAR_INTRODUCTION___IMPL = store_thm ("INFERENCE_STAR_INTRODUCTION___IMPL",
“!sf c1 c2 pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS (c1,c2) (pfL, sfL) (pfL', sfL') ==>
      LIST_DS_ENTAILS (c1,c2) (pfL, sf::sfL) (pfL', sf::sfL')”,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_def,
   LIST_SF_SEM_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC ‘h1’ THEN
Q.EXISTS_TAC ‘h2’ THEN
ASM_SIMP_TAC std_ss [] THEN
Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
FULL_SIMP_TAC std_ss [HEAP_DISTINCT___FUNION]);




val INFERENCE_STAR_INTRODUCTION___points_to = store_thm ("INFERENCE_STAR_INTRODUCTION___points_to",
“!e a1 a2 c1 c2 pfL sfL pfL' sfL'.
      ((!x. MEM x a2 ==> MEM x a1) /\
       ALL_DISTINCT (MAP FST a1)) ==>
      (
      LIST_DS_ENTAILS (e::c1, c2) (pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_points_to e a1)::sfL) (pfL', (sf_points_to e a2)::sfL'))”,

SIMP_TAC list_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_EVAL, DISJ_IMP_THM, FORALL_AND_THM] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   CONJ_TAC THENL [
      METIS_TAC[DS_POINTS_TO___SUBLIST],

      Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
      ‘?c'. (DS_EXPRESSION_EVAL s e = dsv_const c') /\
           (c' IN FDOM h)’ by (
         FULL_SIMP_TAC std_ss [DS_POINTS_TO_def, NOT_IS_DSV_NIL_THM, ds_value_11] THEN
         METIS_TAC[GET_DSV_VALUE_def]
      ) THEN
      FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, DS_POINTER_DANGLES, FDOM_DOMSUB, IN_DELETE,
         DS_EXPRESSION_EQUAL_def, dse_nil_def, DS_EXPRESSION_EVAL_def, ds_value_distinct,
         MEM_MAP, IS_DSV_NIL_def, HEAP_DISTINCT___IND_DEF, DS_EXPRESSION_EVAL_VALUE_def] THEN
      REPEAT STRIP_TAC THENL [
         FULL_SIMP_TAC std_ss [HEAP_DISTINCT_def, FDOM_DOMSUB, IN_DELETE, DS_POINTER_DANGLES] THEN
         METIS_TAC[],

         FULL_SIMP_TAC std_ss [HEAP_DISTINCT_def, DS_POINTS_TO_def] THEN
         METIS_TAC[],

         Cases_on ‘DS_EXPRESSION_EVAL s e1 = DS_EXPRESSION_EVAL s e2’ THEN ASM_REWRITE_TAC[] THEN
         FULL_SIMP_TAC std_ss [HEAP_DISTINCT_def, DS_POINTS_TO_def, DS_EXPRESSION_EQUAL_def] THEN
         METIS_TAC[]
      ]
   ],


   SIMP_TAC std_ss [HEAP_DISTINCT___IND_DEF] THEN
   REPEAT STRIP_TAC THEN
   ‘?c'. (DS_EXPRESSION_EVAL s e = dsv_const c')’ by (
      FULL_SIMP_TAC std_ss [NOT_IS_DSV_NIL_THM, ds_value_11]
   ) THEN
   FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, DS_EXPRESSION_EVAL_VALUE_def,
      IS_DSV_NIL_def] THEN
   ‘?he. (FDOM he = {c'}) /\ DS_POINTS_TO s he e a1’ by (
      ASM_SIMP_TAC std_ss [DS_POINTS_TO_def, GET_DSV_VALUE_def,
         IS_DSV_NIL_def, EVERY_MEM] THEN
      Q.PAT_X_ASSUM ‘ALL_DISTINCT (MAP FST a1)’ MP_TAC THEN
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      Induct_on ‘a1’ THENL [
         SIMP_TAC list_ss [] THEN
         Q.EXISTS_TAC ‘FEMPTY |+ (c', FEMPTY)’ THEN
         SIMP_TAC std_ss [FDOM_FUPDATE, FDOM_FEMPTY, IN_INSERT],


         FULL_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM, EVERY_MEM, MEM_MAP,
            GSYM LEFT_FORALL_IMP_THM] THEN
         REPEAT STRIP_TAC THEN
         FULL_SIMP_TAC std_ss [] THEN
         pairLib.GEN_BETA_TAC THEN
         Q.EXISTS_TAC ‘FEMPTY |+ (c', (he ' c') |+ (FST h, DS_EXPRESSION_EVAL s (SND h)))’ THEN
         ASM_SIMP_TAC std_ss [FDOM_FUPDATE, FDOM_FEMPTY, IN_SING, FAPPLY_FUPDATE_THM, IN_INSERT] THEN
         GEN_TAC THEN STRIP_TAC THEN
         Cases_on ‘e'’ THEN
         RES_TAC THEN
         FULL_SIMP_TAC std_ss [COND_RATOR, COND_RAND] THEN
         METIS_TAC[pairTheory.FST]
      ]
   ) THEN
   Q.PAT_X_ASSUM ‘!s h. P s h ==> (DS_POINTS_TO s h e a2 /\ Y)’ (fn thm => MP_TAC (Q.SPECL [‘s’, ‘FUNION he h’] thm)) THEN
   ASM_SIMP_TAC std_ss [GET_DSV_VALUE_def, DS_POINTER_DANGLES, FDOM_FUNION, IN_UNION, IN_SING] THEN
   ‘(he \\ c' = FEMPTY) /\ (h \\ c' = h)’ by (
      ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FDOM_DOMSUB, IN_DELETE, IN_SING, FDOM_FEMPTY,
         NOT_IN_EMPTY, DOMSUB_FAPPLY_THM] THEN
      METIS_TAC[]
   ) THEN
   ‘!x. DS_POINTS_TO s (FUNION he h) e x = DS_POINTS_TO s he e x’ by (
      ASM_SIMP_TAC std_ss [DS_POINTS_TO_def, GET_DSV_VALUE_def, FUNION_DEF, IN_UNION, IN_SING]
   ) THEN
   ‘HEAP_DISTINCT s (FUNION he h) c1 c2’ by (
      FULL_SIMP_TAC std_ss [HEAP_DISTINCT___FUNION, HEAP_DISTINCT_def, IN_SING, DS_EXPRESSION_EQUAL_def] THEN
      METIS_TAC[GET_DSV_VALUE_def, NOT_IS_DSV_NIL_THM]
   ) THEN
   ASM_SIMP_TAC std_ss [DOMSUB_FUNION, FUNION_FEMPTY_1]
]);



val INFERENCE_STAR_INTRODUCTION___tree = store_thm ("INFERENCE_STAR_INTRODUCTION___tree",
“!e es fL fL' c1 c2 pfL sfL pfL' sfL'.
      (PERM fL fL') ==>
      (
      LIST_DS_ENTAILS (c1, (e,es)::c2) (pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1, c2) (pfL, (sf_tree fL es e)::sfL) (pfL', (sf_tree fL' es e)::sfL'))”,

SIMP_TAC list_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_THM, DISJ_IMP_THM, FORALL_AND_THM] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   Q.EXISTS_TAC ‘h1’ THEN
   Q.EXISTS_TAC ‘h2’ THEN
   ASM_SIMP_TAC std_ss [] THEN
   CONJ_TAC THENL [
      Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
      ASM_SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC list_ss [HEAP_DISTINCT___IND_DEF, HEAP_DISTINCT___FUNION] THEN
      Cases_on ‘DS_EXPRESSION_EQUAL s e es’ THEN ASM_REWRITE_TAC[] THEN
      FULL_SIMP_TAC list_ss [SF_SEM___sf_tree_THM, LET_THM, SF_SEM___sf_points_to_THM,
         DS_POINTS_TO_def, HEAP_DISTINCT_def, DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER,
         DS_EXPRESSION_EQUAL_def] THEN
      METIS_TAC[],

      FULL_SIMP_TAC std_ss [SF_SEM_def, SF_SEM___sf_tree_def] THEN
      METIS_TAC[SF_SEM___sf_tree_len_PERM_THM]
   ],


   SIMP_TAC std_ss [HEAP_DISTINCT___IND_DEF] THEN
   REPEAT GEN_TAC THEN
   Cases_on ‘DS_EXPRESSION_EQUAL s e es’ THEN ASM_REWRITE_TAC[] THEN1 (
      STRIP_TAC THEN
      Q.PAT_X_ASSUM ‘!s h. P s h’ (fn thm => MP_TAC (Q.SPECL [‘s’, ‘h’] thm)) THEN
      ASM_SIMP_TAC std_ss [SF_SEM___sf_tree_THM, FDOM_FEMPTY, DISJOINT_EMPTY,
         FUNION_FEMPTY_1]
   ) THEN
   STRIP_TAC THEN

   ‘?c'. (DS_EXPRESSION_EVAL s e = dsv_const c')’ by (
      FULL_SIMP_TAC std_ss [NOT_IS_DSV_NIL_THM, ds_value_11]
   ) THEN
   FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, DS_EXPRESSION_EVAL_VALUE_def, IS_DSV_NIL_def] THEN
   ‘?he. (FDOM he = {c'}) /\ SF_SEM s he (sf_tree fL es e)’ by (
      Q.EXISTS_TAC ‘FEMPTY |+ (c', FUN_FMAP (\x. DS_EXPRESSION_EVAL s es) (LIST_TO_SET fL))’ THEN
      SIMP_TAC std_ss [FDOM_FUPDATE, FDOM_FEMPTY,
         SF_SEM_def, SF_SEM___sf_tree_def] THEN
      Q.EXISTS_TAC ‘SUC 0’ THEN
      REWRITE_TAC[SF_SEM___sf_tree_len_def] THEN
      FULL_SIMP_TAC list_ss [PF_SEM_def, GET_DSV_VALUE_def, FDOM_FUPDATE, IN_INSERT, DS_EXPRESSION_EQUAL_def, IS_DSV_NIL_def] THEN
      Q.EXISTS_TAC ‘MAP (\x. FEMPTY) fL’ THEN
      ASM_SIMP_TAC list_ss [DOMSUB_FUPDATE, EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
         HEAP_READ_ENTRY_def, GET_DSV_VALUE_def, FDOM_FUPDATE, IN_INSERT, FAPPLY_FUPDATE_THM,
         FUN_FMAP_DEF, FINITE_LIST_TO_SET, DOMSUB_FEMPTY, MAP_MAP_o, combinTheory.o_DEF,
         FDOM_FEMPTY, EL_ALL_DISJOINT_EQ, EL_MAP, DISJOINT_EMPTY, MEM_ZIP,
         DS_EXPRESSION_EVAL_def, EL_IS_EL, IS_DSV_NIL_def] THEN
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      Induct_on ‘fL’ THENL [
         SIMP_TAC list_ss [],
         ASM_SIMP_TAC list_ss [FUNION_FEMPTY_1]
      ]
   ) THEN

   FULL_SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM,
      MEM_MAP, IS_DSV_NIL_def] THEN
   Q.PAT_X_ASSUM ‘!s h1 h2. P s h1 h2’ (fn thm => MP_TAC (Q.SPECL [‘s’, ‘he’, ‘h’] thm)) THEN

   ‘HEAP_DISTINCT s he c1 c2’ by (
      FULL_SIMP_TAC std_ss [HEAP_DISTINCT_def, IN_SING, DS_EXPRESSION_EQUAL_def] THEN
      METIS_TAC[NOT_IS_DSV_NIL_THM, GET_DSV_VALUE_def]
   ) THEN
   ASM_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION, IN_SING,
      DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, HEAP_DISTINCT___FUNION] THEN
   STRIP_TAC THEN

   ‘h1' = he’ by (
      ‘SF_IS_PRECISE (sf_tree fL es e)’ by REWRITE_TAC[SF_IS_PRECISE_THM] THEN
      FULL_SIMP_TAC std_ss [SF_IS_PRECISE_def] THEN
      POP_ASSUM MATCH_MP_TAC THEN
      Q.EXISTS_TAC ‘s’ THEN
      Q.EXISTS_TAC ‘FUNION he h’ THEN
      REWRITE_TAC[SUBMAP___FUNION___ID] THEN
      ASM_SIMP_TAC std_ss [SUBMAP___FUNION___ID] THEN
      FULL_SIMP_TAC std_ss [SF_SEM___sf_tree_def, SF_SEM_def] THEN
      METIS_TAC[SF_SEM___sf_tree_len_PERM_THM]
   ) THEN
   ‘DISJOINT (FDOM he) (FDOM h) /\
    DISJOINT (FDOM he) (FDOM h2')’ by (
      FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY, IN_SING] THEN
      METIS_TAC[]
   ) THEN
   Q.PAT_X_ASSUM ‘FUNION h2 h = Y’ MP_TAC THEN
   ASM_SIMP_TAC std_ss [FUNION_EQ]
])




val INFERENCE_STAR_INTRODUCTION___list = store_thm ("INFERENCE_STAR_INTRODUCTION___list",
“!e1 e2 f c1 c2 pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS (c1, (e1,e2)::c2) (pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1, c2) (pfL, (sf_ls f e1 e2)::sfL) (pfL', (sf_ls f e1 e2)::sfL')”,

SIMP_TAC std_ss [sf_ls_def] THEN
REPEAT GEN_TAC THEN
MATCH_MP_TAC INFERENCE_STAR_INTRODUCTION___tree THEN
SIMP_TAC std_ss [PERM_REFL])


val INFERENCE_STAR_INTRODUCTION___bin_tree = store_thm ("INFERENCE_STAR_INTRODUCTION___bin_tree",
“!e f1 f2 f1' f2' c1 c2 pfL sfL pfL' sfL'.
      (((f1 = f1') /\  (f2 = f2')) \/ ((f1 = f2') /\  (f2 = f1'))) ==>

     (LIST_DS_ENTAILS (c1, (e,dse_nil)::c2) (pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1, c2) (pfL, (sf_bin_tree (f1,f2) e)::sfL) (pfL', (sf_bin_tree (f1',f2') e)::sfL'))”,

SIMP_TAC std_ss [sf_bin_tree_def] THEN
REPEAT STRIP_TAC THEN (
   MATCH_MP_TAC INFERENCE_STAR_INTRODUCTION___tree THEN
   ASM_SIMP_TAC std_ss [PERM_REFL, PERM_SWAP_AT_FRONT]
));


val LIST_DS_ENTAILS___ELIM_PRECONDITION_1 = store_thm ("LIST_DS_ENTAILS___ELIM_PRECONDITION_1",
“!c11 c12 c2 pfL pfL' sfL sfL'.
      LIST_DS_ENTAILS ((c11++c12), c2) (pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c12,c2) (pfL,(MAP (\e. sf_points_to e []) c11)++sfL) (pfL',(MAP (\e. sf_points_to e []) c11)++ sfL')”,

Induct_on ‘c11’ THENL [
   SIMP_TAC list_ss [],

   SIMP_TAC list_ss [] THEN
   ASM_SIMP_TAC list_ss [GSYM INFERENCE_STAR_INTRODUCTION___points_to] THEN
   POP_ASSUM (ASSUME_TAC o GSYM) THEN
   ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
   REPEAT GEN_TAC THEN
   REPEAT STRIP_EQ_FORALL_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   SIMP_TAC std_ss [] THEN
   STRIP_EQ_BOOL_TAC THEN
   MATCH_MP_TAC HEAP_DISTINCT___PERM THEN
   SIMP_TAC list_ss [PERM_CONS_EQ_APPEND, PERM_REFL] THEN
   Q.EXISTS_TAC ‘c11’ THEN
   Q.EXISTS_TAC ‘c12’ THEN
   SIMP_TAC std_ss [PERM_REFL]
]);


Theorem LIST_DS_ENTAILS___ELIM_PRECONDITION_2:
  !c21 c22 c1 pfL pfL' sfL sfL'.
    LIST_DS_ENTAILS (c1, c21++c22) (pfL, sfL) (pfL', sfL') <=>
    LIST_DS_ENTAILS (c1, c22)
                    (pfL, MAP (λ(e1,e2). sf_tree [] e2 e1) c21 ++ sfL)
                    (pfL', MAP (λ(e1,e2). sf_tree [] e2 e1) c21 ++ sfL')
Proof
  Induct_on ‘c21’ THENL [
    SIMP_TAC list_ss [],

    Cases_on ‘h’ THEN
    SIMP_TAC list_ss [] THEN
    ASM_SIMP_TAC list_ss [GSYM INFERENCE_STAR_INTRODUCTION___tree, PERM_REFL] >>
    POP_ASSUM (ASSUME_TAC o GSYM) THEN
    ASM_SIMP_TAC std_ss [] THEN
    SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
    REPEAT GEN_TAC THEN
    REPEAT STRIP_EQ_FORALL_TAC THEN
    STRIP_EQ_BOOL_TAC THEN
    SIMP_TAC std_ss [] THEN
    STRIP_EQ_BOOL_TAC THEN
    MATCH_MP_TAC HEAP_DISTINCT___PERM THEN
    SIMP_TAC list_ss [PERM_CONS_EQ_APPEND, PERM_REFL] THEN
    Q.EXISTS_TAC ‘c21’ THEN
    Q.EXISTS_TAC ‘c22’ THEN
    SIMP_TAC std_ss [PERM_REFL]
  ]
QED



Theorem LIST_DS_ENTAILS___ELIM_PRECONDITION_COMPLETE:
  !c1 c2. ?sfL2.
            !pfL pfL' sfL sfL'.
              LIST_DS_ENTAILS (c1,c2) (pfL, sfL) (pfL', sfL') =
              LIST_DS_ENTAILS ([],[]) (pfL, sfL++sfL2) (pfL',sfL'++sfL2)
Proof
  REPEAT GEN_TAC THEN
  ASSUME_TAC (Q.SPECL [‘c1’, ‘[]’] LIST_DS_ENTAILS___ELIM_PRECONDITION_1) THEN
  ASSUME_TAC (Q.SPECL [‘c2’, ‘[]’] LIST_DS_ENTAILS___ELIM_PRECONDITION_2) THEN
  FULL_SIMP_TAC list_ss [] THEN
  REPEAT (POP_ASSUM (K ALL_TAC)) THEN

  Q.ABBREV_TAC
   ‘sfL2 = MAP (λ(e1,e2). sf_tree [] e2 e1) c2 ++
           MAP (\e. sf_points_to e []) c1’ THEN
  Q.EXISTS_TAC ‘sfL2’ THEN
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
  SIMP_TAC std_ss [PERM_REFL, PERM_APPEND]
QED

val INFERENCE_NON_EMPTY_TREE = store_thm ("INFERENCE_NON_EMPTY_TREE",
“!e es c1 c2 eL fL a pfL sfL pfL' sfL'.
      ((LENGTH eL = LENGTH fL) /\ ALL_DISTINCT fL /\
      (!n. n < LENGTH eL ==> MEM (EL n fL, EL n eL) a)) ==>

      ((LIST_DS_ENTAILS (c1,c2) ((pf_unequal e es)::pfL, (sf_points_to e a)::sfL) (pfL',
       (sf_points_to e a)::((MAP (\e. sf_tree fL es e) eL)++sfL'))) =
       LIST_DS_ENTAILS (c1,c2) ((pf_unequal e es)::pfL, (sf_points_to e a)::sfL) (pfL', (sf_tree fL es e)::sfL'))”,


SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
SIMP_TAC std_ss [LIST_DS_SEM_EVAL, LET_THM] THEN
REPEAT STRIP_TAC THEN
REPEAT STRIP_EQ_FORALL_TAC THEN
STRIP_EQ_BOOL_TAC THEN
FULL_SIMP_TAC std_ss [MAP_MAP_o, combinTheory.o_DEF] THEN
‘?c. DS_EXPRESSION_EVAL s e = dsv_const c’ by (
   FULL_SIMP_TAC std_ss [DS_POINTS_TO_def, GET_DSV_VALUE_def, NOT_IS_DSV_NIL_THM,
      ds_value_11]
) THEN
FULL_SIMP_TAC list_ss [GET_DSV_VALUE_def, DS_EXPRESSION_EVAL_VALUE_def] THEN
SIMP_TAC std_ss [LIST_DS_SEM_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_EQ_EXISTS_TAC THEN
STRIP_EQ_BOOL_TAC THEN

MATCH_MP_TAC (prove (“(a /\ (b1 = b2)) ==> (b1 = (a /\ b2))”, METIS_TAC[])) THEN

Q_TAC MP_FREE_VAR_TAC ‘fL’ THEN
Q.SPEC_TAC (‘eL’, ‘eL’) THEN
Q.SPEC_TAC (‘h1’, ‘h1’) THEN
REWRITE_TAC[AND_IMP_INTRO, GSYM CONJ_ASSOC] THEN
‘?fL'. sf_tree fL = sf_tree fL'’ by METIS_TAC[] THEN
FULL_SIMP_TAC std_ss [] THEN POP_ASSUM (K ALL_TAC) THEN
Induct_on ‘fL’ THENL [
   FULL_SIMP_TAC list_ss [LENGTH_NIL, DS_POINTS_TO_def, IS_DSV_NIL_def, GET_DSV_VALUE_def],

   Cases_on ‘eL’ THEN SIMP_TAC list_ss [] THEN
   SIMP_TAC list_ss [FORALL_LESS_SUC, LIST_DS_SEM_THM] THEN
   REPEAT STRIP_TAC THENL [
      FULL_SIMP_TAC std_ss [IMP_CONJ_THM, FORALL_AND_THM] THEN
      Q.PAT_X_ASSUM ‘!eL. P1 eL /\ P2 eL ==> P eL’ (MP_TAC o (Q.SPECL [‘t’])) THEN
      ASM_REWRITE_TAC[] THEN
      FULL_SIMP_TAC list_ss [DS_POINTS_TO_def, EVERY_MEM, MEM_MAP, GET_DSV_VALUE_def, GSYM LEFT_FORALL_IMP_THM, IS_DSV_NIL_def, MEM_ZIP, DS_EXPRESSION_EVAL_def] THEN
      RES_TAC THEN
      FULL_SIMP_TAC std_ss [],


      REPEAT STRIP_EQ_EXISTS_TAC THEN
      STRIP_EQ_BOOL_TAC THEN
      BINOP_TAC THENL [
         METIS_TAC[],


         ‘DS_EXPRESSION_EQUAL s h' (dse_const (h ' c ' h''))’ by (
            FULL_SIMP_TAC std_ss [DS_POINTS_TO_def, GET_DSV_VALUE_def, EVERY_MEM,
               DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def] THEN
            RES_TAC THEN
            FULL_SIMP_TAC std_ss []
         ) THEN
         SIMP_TAC std_ss [SF_SEM___sf_tree_def, SF_SEM_def] THEN
         METIS_TAC[SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM, DS_EXPRESSION_EQUAL_def]
      ]
   ]
]);









val INFERENCE_NON_EMPTY_LS = store_thm ("INFERENCE_NON_EMPTY_LS",
“!e1 e2 e3 f a c1 c2 pfL sfL pfL' sfL'.
      (MEM (f, e2) a) ==>

      ((LIST_DS_ENTAILS (c1,c2) ((pf_unequal e1 e3)::pfL, (sf_points_to e1 a)::sfL) (pfL', (sf_points_to e1 a)::(sf_ls f e2 e3)::sfL')) =
       LIST_DS_ENTAILS (c1,c2) ((pf_unequal e1 e3)::pfL, (sf_points_to e1 a)::sfL) (pfL', (sf_ls f e1 e3)::sfL'))”,


SIMP_TAC std_ss [sf_ls_def] THEN
REPEAT STRIP_TAC THEN
MP_TAC (
   Q.SPECL [‘e1’, ‘e3’, ‘c1’, ‘c2’, ‘[e2]’, ‘[f]’, ‘a’, ‘pfL’, ‘sfL’, ‘pfL'’, ‘sfL'’] INFERENCE_NON_EMPTY_TREE
) THEN
ASM_SIMP_TAC list_ss [prove (“n < 1 = (n = 0)”, DECIDE_TAC)]);




val INFERENCE_NON_EMPTY_BIN_TREE = store_thm ("INFERENCE_NON_EMPTY_BIN_TREE",
“!e e1 e2 f1 f2 a c1 c2 pfL sfL pfL' sfL'.
      ((MEM (f1, e1) a) /\ (MEM (f2, e2) a) /\ ~(f1 = f2)) ==>
      ((LIST_DS_ENTAILS (c1,c2) (pfL, (sf_points_to e a)::sfL) (pfL', (sf_points_to e a)::(sf_bin_tree (f1,f2) e1)::(sf_bin_tree (f1,f2) e2)::sfL')) =
       (LIST_DS_ENTAILS (c1,c2) (pfL, (sf_points_to e a)::sfL) (pfL', (sf_bin_tree (f1,f2) e)::sfL')))”,


SIMP_TAC std_ss [sf_bin_tree_def] THEN
REPEAT STRIP_TAC THEN
MP_TAC (
   Q.SPECL [‘e’, ‘dse_nil’, ‘c1’, ‘c2’, ‘[e1;e2]’, ‘[f1;f2]’, ‘a’, ‘pfL’, ‘sfL’, ‘pfL'’, ‘sfL'’] INFERENCE_NON_EMPTY_TREE
) THEN
ASM_SIMP_TAC list_ss [prove (“n < 2 = ((n = 0) \/ (n = 1))”, DECIDE_TAC),
   DISJ_IMP_THM] THEN
SIMP_TAC std_ss [INFERENCE_NIL_NOT_LVAL___points_to]);




Theorem INFERENCE_UNROLL_COLLAPSE_LS___IMPL___EMPTY[local]:
  !e1:('b, 'a) ds_expression e2 f pfL sfL pfL' sfL'.
    INFINITE (UNIV:'b set) /\
    LIST_DS_ENTAILS ([], []) (pf_equal e1 e2 :: pfL, sfL) (pfL', sfL') /\
    (!x. LIST_DS_ENTAILS ([], [])
                         (pf_unequal e1 e2::
                          pf_unequal (dse_const x) e2::pfL,
                          sf_points_to e1 [(f, dse_const x)]::
                          sf_points_to (dse_const x) [(f, e2)]::sfL)
                         (pfL', sfL')) ==>

    LIST_DS_ENTAILS ([], []) (pfL, (sf_ls f e1 e2)::sfL) (pfL', sfL')
Proof
   SIMP_TAC std_ss [LIST_DS_ENTAILS_def, HEAP_DISTINCT___IND_DEF] THEN
   REPEAT STRIP_TAC THEN
   Cases_on ‘DS_EXPRESSION_EQUAL s e1 e2’ THEN1 (
      FULL_SIMP_TAC std_ss [LIST_DS_SEM_EVAL]
   ) THEN

   Q.PAT_X_ASSUM ‘LIST_DS_SEM s h X’ MP_TAC THEN
   SIMP_TAC std_ss [LIST_DS_SEM_def, LIST_SF_SEM_THM] THEN
   SIMP_TAC std_ss [LIST_PF_SEM_def, LIST_SF_SEM_def] THEN
   Q.ABBREV_TAC ‘pf = (FOLDR pf_and pf_true pfL)’ THEN
   Q.ABBREV_TAC ‘pf' = (FOLDR pf_and pf_true pfL')’ THEN
   Q.ABBREV_TAC ‘sf = (FOLDR sf_star sf_emp sfL)’ THEN
   Q.ABBREV_TAC ‘sf' = (FOLDR sf_star sf_emp sfL')’ THEN
   STRIP_TAC THEN
   MP_TAC (Q.SPECL [‘s’, ‘h2’, ‘[f]’, ‘e1’, ‘e2’, ‘pf’, ‘sf’, ‘pf'’, ‘sf'’] LEMMA_5) THEN
   MATCH_MP_TAC (prove (“(a /\ (b ==> c)) ==> ((a ==> b) ==> c)”, METIS_TAC[])) THEN
   CONJ_TAC THEN1 (
      ASM_SIMP_TAC list_ss [ALL_DISTINCT] THEN
      ‘~(DS_POINTER_DANGLES s h1 e1)’ by (
         Q.PAT_X_ASSUM ‘SF_SEM s h1 Y’ MP_TAC THEN
         ASM_SIMP_TAC std_ss [SF_SEM___sf_ls_THM, LET_THM] THEN
         SIMP_TAC std_ss [SF_SEM___sf_points_to_THM, DS_POINTS_TO_def, DS_POINTER_DANGLES]
      ) THEN
      REPEAT CONJ_TAC THENL [
         SIMP_TAC std_ss [BALANCED_SF_SEM___sf_ls_len] THEN
         REWRITE_TAC [prove (“2 = SUC (SUC 0)”, DECIDE_TAC), SF_SEM___sf_ls_len_def] THEN
         SIMP_TAC list_ss [PF_SEM_def, DS_EXPRESSION_EVAL_def, LET_THM, NOT_IS_DSV_NIL_THM, IN_DELETE,
            FDOM_DOMSUB] THEN
         REPEAT STRIP_TAC THEN
         Q.PAT_X_ASSUM ‘~(GET_DSV_VALUE X = GET_DSV_VALUE Y)’ ASSUME_TAC THEN
         Q.PAT_X_ASSUM ‘Y = dsv_const c'’ ASSUME_TAC THEN
         Q.PAT_X_ASSUM ‘Y = dsv_const c’ ASSUME_TAC THEN
         FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def,
            FDOM_DOMSUB, IN_DELETE, DOMSUB_FAPPLY_THM] THEN

         ‘LIST_DS_SEM s h' (pfL', sfL')’ suffices_by (STRIP_TAC THEN
            POP_ASSUM MP_TAC THEN
            ASM_SIMP_TAC std_ss [DS_SEM_def, LIST_DS_SEM_def, LIST_PF_SEM_def, LIST_SF_SEM_def]
         ) THEN
         Q.PAT_X_ASSUM ‘!x s h. P x s h’ MATCH_MP_TAC THEN
         Q.EXISTS_TAC ‘dsv_const c'’ THEN

         ASM_SIMP_TAC list_ss [LIST_DS_SEM_THM, PF_SEM_def, DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def,
            GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
            SF_SEM_def, DS_EXPRESSION_EVAL_VALUE_def, GET_DSV_VALUE_def,
            DS_POINTS_TO_def, IS_DSV_NIL_def] THEN
         Q.EXISTS_TAC ‘DRESTRICT h1' {c}’ THEN
         Q.EXISTS_TAC ‘DRESTRICT h1' {c'}’ THEN
         Q.EXISTS_TAC ‘h2'’ THEN
         FULL_SIMP_TAC std_ss [DRESTRICT_DEF, IN_INTER, IN_SING, EXTENSION, DISJOINT_DEF, NOT_IN_EMPTY,
            FUNION_DEF, IN_UNION] THEN
         REPEAT STRIP_TAC THENL [
            REWRITE_TAC[FUNION___ASSOC] THEN
            AP_THM_TAC THEN AP_TERM_TAC THEN
            Q.PAT_X_ASSUM ‘h1' \\ c \\ c' = FEMPTY’ MP_TAC THEN
            ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FUNION_DEF,
               DRESTRICT_DEF, IN_UNION, IN_INTER, IN_SING, FDOM_DOMSUB, IN_DELETE,
               FDOM_DOMSUB, FDOM_FEMPTY, NOT_IN_EMPTY, DOMSUB_FAPPLY_THM, GET_DSV_VALUE_def] THEN
            METIS_TAC[],

            METIS_TAC[],
            ASM_SIMP_TAC std_ss [LIST_DS_SEM_def, LIST_SF_SEM_def, LIST_PF_SEM_def],
            METIS_TAC[],
            METIS_TAC[]
         ],

         FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, DS_EXPRESSION_EQUAL_def, dse_nil_def,
            DS_EXPRESSION_EVAL_def, IS_DSV_NIL_THM],


         FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
         METIS_TAC[]
      ]
   ) THEN

   ASM_SIMP_TAC std_ss [GSYM sf_ls_def, SF_SEM___EXTEND_def] THEN
   METIS_TAC[DISJOINT_SYM, FUNION___COMM]
QED

val INFERENCE_UNROLL_COLLAPSE_LS = store_thm ("INFERENCE_UNROLL_COLLAPSE_LS",
“!e1:('b, 'a) ds_expression e2 c1 c2 f pfL sfL pfL' sfL'.
      INFINITE (UNIV:'b set) ==>

      ((
      (LIST_DS_ENTAILS (c1,c2) ((pf_equal e1 e2)::pfL, sfL) (pfL', sfL') /\
       (!x. LIST_DS_ENTAILS (c1,c2) ((pf_unequal e1 e2)::(pf_unequal (dse_const x) e2)::pfL,
                              (sf_points_to e1 [(f, dse_const x)])::(sf_points_to (dse_const x) [(f, e2)])::sfL) (pfL', sfL')))) =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_ls f e1 e2)::sfL) (pfL', sfL'))”,


REPEAT STRIP_TAC THEN
EQ_TAC THENL [
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (Q.ISPECL [‘c1:('b, 'a) ds_expression list’, ‘c2:(('b, 'a) ds_expression # ('b, 'a) ds_expression) list’] LIST_DS_ENTAILS___ELIM_PRECONDITION_COMPLETE) THEN
   FULL_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC list_ss [] THEN
   MATCH_MP_TAC INFERENCE_UNROLL_COLLAPSE_LS___IMPL___EMPTY THEN
   ASM_SIMP_TAC std_ss [],


   REPEAT STRIP_TAC THENL [
      FULL_SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
      REPEAT STRIP_TAC THEN
      Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
      FULL_SIMP_TAC list_ss [LIST_DS_SEM_EVAL],

      FULL_SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
      REPEAT STRIP_TAC THEN
      Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
      FULL_SIMP_TAC list_ss [LIST_DS_SEM_EVAL, LET_THM, DS_POINTS_TO_def,
         DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def, FDOM_DOMSUB, IN_DELETE] THEN
      Q.PAT_X_ASSUM ‘~(GET_DSV_VALUE x = GET_DSV_VALUE Y)’ ASSUME_TAC THEN
      ‘?c c'. (x = dsv_const c) /\ (DS_EXPRESSION_EVAL s e1 = dsv_const c')’ by (
         FULL_SIMP_TAC std_ss [NOT_IS_DSV_NIL_THM, ds_value_11]
      ) THEN
      FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def, GET_DSV_VALUE_def, FDOM_DOMSUB,
         IN_DELETE, IS_DSV_NIL_def, LIST_DS_SEM_THM, DOMSUB_FAPPLY_THM, DS_EXPRESSION_EQUAL_def,
         DS_EXPRESSION_EVAL_def] THEN
      Q.PAT_X_ASSUM ‘dsv_const c = Y’ (ASSUME_TAC o GSYM) THEN

      Q.EXISTS_TAC ‘DRESTRICT h {c}’ THEN
      Q.EXISTS_TAC ‘h \\ c' \\ c’ THEN
      FULL_SIMP_TAC std_ss [SF_SEM___sf_ls_THM, DS_EXPRESSION_EQUAL_def,
         DS_EXPRESSION_EVAL_def, DOMSUB_FAPPLY_THM, DS_EXPRESSION_EQUAL_def, LET_THM] THEN
      SIMP_TAC std_ss [SF_SEM___sf_points_to_THM] THEN
      SIMP_TAC std_ss [SF_SEM___sf_ls_THM] THEN
      ASM_SIMP_TAC list_ss [DS_EXPRESSION_EVAL_def, DS_EXPRESSION_EQUAL_def,
         DS_EXPRESSION_EVAL_VALUE_def, DRESTRICT_DEF, IN_INTER, IN_SING, GET_DSV_VALUE_def,
         DS_POINTS_TO_def, IS_DSV_NIL_def] THEN

      ASM_SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, IN_UNION, FUNION_DEF, DRESTRICT_DEF,
         IN_INTER, IN_SING, FDOM_DOMSUB, DOMSUB_FAPPLY_THM, IN_DELETE, FDOM_FEMPTY,
         NOT_IN_EMPTY, DISJOINT_DEF] THEN
      METIS_TAC[]
   ]
]);



val INFERENCE_UNROLL_COLLAPSE_BIN_TREE___IMPL___EMPTY = prove (
“!e:('b, 'a) ds_expression f1 f2 pfL sfL pfL' sfL'.
      (INFINITE (UNIV:'b set) /\ (~(f1 = f2)) /\
      (LIST_DS_ENTAILS ([],[]) ((pf_equal e dse_nil)::pfL, sfL) (pfL', sfL') /\
       (!x1 x2. LIST_DS_ENTAILS ([],[]) ((pf_unequal e dse_nil)::(pf_unequal (dse_const x1) dse_nil)::(pf_unequal (dse_const x2) dse_nil)::pfL,
                              (sf_points_to e [(f1, dse_const x1);(f2, dse_const x2)])::(sf_points_to (dse_const x1) [(f1, dse_nil);(f2, dse_nil)])::(sf_points_to (dse_const x2) [(f1, dse_nil);(f2, dse_nil)])::sfL) (pfL', sfL')))) ==>

      LIST_DS_ENTAILS ([],[]) (pfL, (sf_bin_tree (f1,f2) e)::sfL) (pfL', sfL')”,


   SIMP_TAC std_ss [LIST_DS_ENTAILS_def, HEAP_DISTINCT___IND_DEF] THEN
   REPEAT STRIP_TAC THEN
   Cases_on ‘DS_EXPRESSION_EQUAL s e dse_nil’ THEN1 (
      FULL_SIMP_TAC std_ss [LIST_DS_SEM_EVAL]
   ) THEN

   Q.PAT_X_ASSUM ‘LIST_DS_SEM s h X’ MP_TAC THEN
   SIMP_TAC std_ss [LIST_DS_SEM_def, LIST_SF_SEM_THM] THEN
   SIMP_TAC std_ss [LIST_PF_SEM_def, LIST_SF_SEM_def] THEN
   Q.ABBREV_TAC ‘pf = (FOLDR pf_and pf_true pfL)’ THEN
   Q.ABBREV_TAC ‘pf' = (FOLDR pf_and pf_true pfL')’ THEN
   Q.ABBREV_TAC ‘sf = (FOLDR sf_star sf_emp sfL)’ THEN
   Q.ABBREV_TAC ‘sf' = (FOLDR sf_star sf_emp sfL')’ THEN
   STRIP_TAC THEN
   MP_TAC (Q.SPECL [‘s’, ‘h2’, ‘[f1;f2]’, ‘e’, ‘dse_nil’, ‘pf’, ‘sf’, ‘pf'’, ‘sf'’] LEMMA_5) THEN
   MATCH_MP_TAC (prove (“(a /\ (b ==> c)) ==> ((a ==> b) ==> c)”, METIS_TAC[])) THEN
   CONJ_TAC THEN1 (
      ASM_SIMP_TAC list_ss [ALL_DISTINCT] THEN
      ‘~(DS_POINTER_DANGLES s h1 e)’ by (
         Q.PAT_X_ASSUM ‘SF_SEM s h1 Y’ MP_TAC THEN
         ASM_SIMP_TAC std_ss [SF_SEM___sf_bin_tree_THM, LET_THM] THEN
         SIMP_TAC std_ss [SF_SEM___sf_points_to_THM, DS_POINTS_TO_def, DS_POINTER_DANGLES]
      ) THEN
      REPEAT CONJ_TAC THENL [
         REWRITE_TAC [prove (“2 = SUC (SUC 0)”, DECIDE_TAC), BALANCED_SF_SEM___sf_tree_len___EXTENDED_DEF] THEN
         SIMP_TAC list_ss [PF_SEM_def, DS_EXPRESSION_EVAL_def, LET_THM, NOT_IS_DSV_NIL_THM, IN_DELETE,
            FDOM_DOMSUB, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, DISJ_IMP_THM,
            FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
         REPEAT GEN_TAC THEN
         Tactical.REVERSE (Cases_on ‘?hl1 hl2. hL = [hl1; hl2]’) THEN1 (
            Cases_on ‘hL’ THEN FULL_SIMP_TAC list_ss [] THEN
            Cases_on ‘t’ THEN FULL_SIMP_TAC list_ss [LENGTH_NIL]
         ) THEN
         FULL_SIMP_TAC std_ss [] THEN
         Cases_on ‘DS_EXPRESSION_EVAL s e = dsv_const c’ THEN ASM_REWRITE_TAC[] THEN
         FULL_SIMP_TAC list_ss [prove (“(n < 2 = ((n = 0) \/ (n = 1)))”, DECIDE_TAC),
            DISJ_IMP_THM, FORALL_AND_THM, GET_DSV_VALUE_def, HEAP_READ_ENTRY_THM
         ] THEN
         REPEAT STRIP_TAC THEN
         ‘LIST_DS_SEM s (FUNION h1' h2') (pfL', sfL')’ suffices_by (STRIP_TAC THEN
            POP_ASSUM MP_TAC THEN
            ASM_SIMP_TAC std_ss [DS_SEM_def, LIST_DS_SEM_def, LIST_PF_SEM_def, LIST_SF_SEM_def]
         ) THEN
         Q.PAT_X_ASSUM ‘!x1 x2 s h. P x1 x2 s h’ MATCH_MP_TAC THEN
         Q.EXISTS_TAC ‘dsv_const c'’ THEN
         Q.EXISTS_TAC ‘dsv_const c''’ THEN

         Q.PAT_X_ASSUM ‘Y = dsv_const c'’ ASSUME_TAC THEN
         Q.PAT_X_ASSUM ‘Y = dsv_const c''’ ASSUME_TAC THEN
         FULL_SIMP_TAC list_ss [LIST_DS_SEM_EVAL, PF_SEM_def, DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def,
            dse_nil_def, ds_value_distinct, DS_POINTS_TO_def, GET_DSV_VALUE_def,
            FUNION_DEF, IS_DSV_NIL_def, IN_UNION, FDOM_DOMSUB, IN_DELETE, ALL_DISJOINT_def,
            DS_POINTER_DANGLES] THEN
         ‘(c' IN FDOM h1') /\ (c'' IN FDOM h1')’ by METIS_TAC[SUBMAP_DEF] THEN
         ‘~(c' = c'')’ by (
            FULL_SIMP_TAC std_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
            METIS_TAC[]
         ) THEN
         ‘~(c' = c)’ by (
            ‘c' IN FDOM (FUNION hl1 (FUNION hl2 FEMPTY))’ by ASM_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION] THEN
            POP_ASSUM MP_TAC THEN
            ASM_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE]
         ) THEN
         ‘~(c'' = c)’ by (
            ‘c'' IN FDOM (FUNION hl1 (FUNION hl2 FEMPTY))’ by ASM_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION] THEN
            POP_ASSUM MP_TAC THEN
            ASM_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE]
         ) THEN
         ‘(h1' ' c' = hl1 ' c') /\ (h1' ' c'' = hl2 ' c'')’ by METIS_TAC[SUBMAP_DEF] THEN

         ‘?hl1' hl2'. hL' = [hl1'; hl2']’ by (
            Q.PAT_X_ASSUM ‘LENGTH hL' = 2’ MP_TAC THEN
            REPEAT (POP_ASSUM (K ALL_TAC)) THEN
            Cases_on ‘hL'’ THEN SIMP_TAC list_ss [] THEN
            Cases_on ‘t’ THEN SIMP_TAC list_ss [LENGTH_NIL]
         ) THEN
         ‘?hl1'' hl2''. hL'' = [hl1''; hl2'']’ by (
            Q.PAT_X_ASSUM ‘LENGTH hL'' = 2’ MP_TAC THEN
            REPEAT (POP_ASSUM (K ALL_TAC)) THEN
            Cases_on ‘hL''’ THEN SIMP_TAC list_ss [] THEN
            Cases_on ‘t’ THEN SIMP_TAC list_ss [LENGTH_NIL]
         ) THEN
         FULL_SIMP_TAC list_ss [DOMSUB_FAPPLY_THM, FUNION_DEF, prove (“(n < 2 = ((n = 0) \/ (n = 1)))”, DECIDE_TAC), DISJ_IMP_THM, FORALL_AND_THM] THEN
         REPEAT (Q.PAT_X_ASSUM ‘FUNION FEMPTY Z = Y’ (ASSUME_TAC o GSYM)) THEN
         FULL_SIMP_TAC std_ss [FUNION_FEMPTY_1, GET_DSV_VALUE_def, ds_value_11] THEN
         REPEAT (Q.PAT_X_ASSUM ‘FEMPTY = Y’ (ASSUME_TAC o GSYM)) THEN
         FULL_SIMP_TAC std_ss [ LIST_DS_SEM_def, LIST_SF_SEM_def, LIST_PF_SEM_def,
            FUNION_FEMPTY_2] THEN

         ‘(FUNION h1' h2' \\ c \\ c' \\ c'') = h2'’ suffices_by (STRIP_TAC THEN
            METIS_TAC[]
         ) THEN
         ASM_SIMP_TAC std_ss [DOMSUB_FUNION] THEN
         ‘((h1' \\ c \\ c' \\ c'') = FEMPTY) /\ ((h2' \\ c \\ c' \\ c'') = h2')’ suffices_by (STRIP_TAC THEN
            ASM_SIMP_TAC std_ss [] THEN
            METIS_TAC[FUNION_FEMPTY_1]
         ) THEN
         SIMP_TAC std_ss [GSYM FDOM_F_FEMPTY1] THEN
         SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_DOMSUB, IN_DELETE, EXTENSION, IN_DELETE,
            DOMSUB_FAPPLY_THM] THEN
         FULL_SIMP_TAC std_ss [EXTENSION, DISJOINT_DEF, IN_INTER, NOT_IN_EMPTY, FUNION_FEMPTY_2,
            ds_value_11] THEN
         Tactical.REVERSE CONJ_TAC THEN1 METIS_TAC[] THEN
         GEN_TAC THEN
         Cases_on ‘a IN FDOM h1'’ THEN ASM_SIMP_TAC std_ss [] THEN
         Cases_on ‘a = c’ THEN ASM_SIMP_TAC std_ss [] THEN
         ‘a IN FDOM (FUNION hl1 hl2)’ by (
            ASM_SIMP_TAC std_ss [FDOM_DOMSUB, IN_DELETE]
         ) THEN
         POP_ASSUM MP_TAC THEN

         ‘FDOM hl1 = {c'}’ by (
            Q.PAT_X_ASSUM ‘c' IN (FDOM hl1)’ MP_TAC THEN
            Q.PAT_X_ASSUM ‘hl1 \\ c' = FEMPTY’ MP_TAC THEN
            REPEAT (POP_ASSUM (K ALL_TAC)) THEN
            SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FEMPTY, EXTENSION, NOT_IN_EMPTY,
               FDOM_DOMSUB, IN_DELETE, DOMSUB_FAPPLY_THM, IN_SING] THEN
            METIS_TAC[]
         ) THEN
         ‘FDOM hl2 = {c''}’ by (
            Q.PAT_X_ASSUM ‘c'' IN (FDOM hl2)’ MP_TAC THEN
            Q.PAT_X_ASSUM ‘hl2 \\ c'' = FEMPTY’ MP_TAC THEN
            REPEAT (POP_ASSUM (K ALL_TAC)) THEN
            SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FEMPTY, EXTENSION, NOT_IN_EMPTY,
               FDOM_DOMSUB, IN_DELETE, DOMSUB_FAPPLY_THM, IN_SING] THEN
            METIS_TAC[]
         ) THEN
         Q.PAT_X_ASSUM ‘FUNION hl1 hl2 = Y’ (K ALL_TAC) THEN
         ASM_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION, IN_SING],


         FULL_SIMP_TAC std_ss [DS_POINTER_DANGLES, DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
         METIS_TAC[]
      ]
   ) THEN

   ASM_SIMP_TAC std_ss [GSYM sf_bin_tree_def, SF_SEM___EXTEND_def] THEN
   METIS_TAC[DISJOINT_SYM, FUNION___COMM]
);




val INFERENCE_UNROLL_COLLAPSE_BIN_TREE = store_thm ("INFERENCE_UNROLL_COLLAPSE_BIN_TREE",
“!e:('b, 'a) ds_expression f1 f2 c1 c2 pfL sfL pfL' sfL'.
      (INFINITE (UNIV:'b set) /\ (~(f1 = f2))) ==>


     ((LIST_DS_ENTAILS (c1,c2) ((pf_equal e dse_nil)::pfL, sfL) (pfL', sfL') /\
       (!x1 x2. LIST_DS_ENTAILS (c1,c2) ((pf_unequal e dse_nil)::(pf_unequal (dse_const x1) dse_nil)::(pf_unequal (dse_const x2) dse_nil)::pfL,
                              (sf_points_to e [(f1, dse_const x1);(f2, dse_const x2)])::(sf_points_to (dse_const x1) [(f1, dse_nil);(f2, dse_nil)])::(sf_points_to (dse_const x2) [(f1, dse_nil);(f2, dse_nil)])::sfL) (pfL', sfL'))) =

      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_bin_tree (f1,f2) e)::sfL) (pfL', sfL'))”,


REPEAT STRIP_TAC THEN
EQ_TAC THENL [
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (Q.ISPECL [‘c1:('b, 'a) ds_expression list’, ‘c2:(('b, 'a) ds_expression # ('b, 'a) ds_expression) list’] LIST_DS_ENTAILS___ELIM_PRECONDITION_COMPLETE) THEN
   FULL_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC list_ss [] THEN
   MATCH_MP_TAC INFERENCE_UNROLL_COLLAPSE_BIN_TREE___IMPL___EMPTY THEN
   ASM_SIMP_TAC std_ss [],


   REPEAT STRIP_TAC THENL [
      FULL_SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
      REPEAT STRIP_TAC THEN
      Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
      FULL_SIMP_TAC list_ss [LIST_DS_SEM_EVAL],

      FULL_SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
      REPEAT STRIP_TAC THEN
      Q.PAT_X_ASSUM ‘!s h. P s h’ MATCH_MP_TAC THEN
      FULL_SIMP_TAC list_ss [LIST_DS_SEM_EVAL, LET_THM, DS_POINTS_TO_def,
         DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def, FDOM_DOMSUB, IN_DELETE] THEN
      Q.PAT_X_ASSUM ‘~(GET_DSV_VALUE x = GET_DSV_VALUE Y)’ ASSUME_TAC THEN
      ‘?c c' c''. (DS_EXPRESSION_EVAL s e = dsv_const c) /\
                 (x1 = dsv_const c') /\
                 (x2 = dsv_const c'')’ by (
         FULL_SIMP_TAC std_ss [NOT_IS_DSV_NIL_THM, ds_value_11]
      ) THEN
      FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def, GET_DSV_VALUE_def, FDOM_DOMSUB,
         IN_DELETE, IS_DSV_NIL_def, LIST_DS_SEM_THM, DOMSUB_FAPPLY_THM, DS_EXPRESSION_EQUAL_def,
         DS_EXPRESSION_EVAL_def] THEN
      Q.PAT_X_ASSUM ‘~(c'' = c)’ ASSUME_TAC THEN
      Q.PAT_X_ASSUM ‘~(c' = c)’ ASSUME_TAC THEN
      FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, dse_nil_def] THEN
      Q.PAT_X_ASSUM ‘dsv_nil = Y’ (ASSUME_TAC o GSYM) THEN
      FULL_SIMP_TAC std_ss [] THEN
      Q.PAT_X_ASSUM ‘dsv_nil = Y’ (ASSUME_TAC o GSYM) THEN
      Q.PAT_X_ASSUM ‘dsv_const z = Y’ (ASSUME_TAC o GSYM) THEN
      Q.PAT_X_ASSUM ‘dsv_const z = Y’ (ASSUME_TAC o GSYM) THEN
      FULL_SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, FDOM_FUNION,
         DISJOINT_UNION_BOTH] THEN

      Q.EXISTS_TAC ‘DRESTRICT h {c'}’ THEN
      Q.EXISTS_TAC ‘DRESTRICT h {c''}’ THEN
      Q.EXISTS_TAC ‘h \\ c \\ c' \\ c''’ THEN
      ASM_SIMP_TAC list_ss [DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, FDOM_DOMSUB, IN_DELETE,
         IN_INTER, DRESTRICT_DEF, IN_SING, SF_SEM___sf_bin_tree_THM,
         DS_EXPRESSION_EVAL_VALUE_def, DS_EXPRESSION_EVAL_def, GET_DSV_VALUE_def,
         DS_EXPRESSION_EQUAL_def, dse_nil_def, SF_SEM___sf_points_to_THM, LET_THM,
         DS_POINTS_TO_def, IS_DSV_NIL_def] THEN
      ‘(DRESTRICT h {c'} \\ c' = FEMPTY) /\
       (DRESTRICT h {c''} \\ c'' = FEMPTY)’ by (
         SIMP_TAC std_ss [GSYM fmap_EQ_THM, DRESTRICT_DEF, FDOM_DOMSUB, EXTENSION, IN_DELETE,
            IN_INTER, IN_SING, FDOM_FEMPTY, NOT_IN_EMPTY]
      ) THEN
      ASM_SIMP_TAC std_ss [] THEN
      ASM_SIMP_TAC std_ss [SF_SEM___STAR_THM, FUNION_EQ_FEMPTY, FDOM_FEMPTY, DISJOINT_EMPTY] THEN
      SIMP_TAC std_ss [SF_SEM___sf_bin_tree_THM, DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def, dse_nil_def] THEN
      CONJ_TAC THENL [
         SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_DOMSUB, EXTENSION, IN_DELETE, FUNION_DEF,
            DRESTRICT_DEF, IN_SING, IN_INTER, IN_UNION, DOMSUB_FAPPLY_THM]  THEN
         METIS_TAC[],

         METIS_TAC[]
      ]
   ]
]);





(* own inference *)
val INFERENCE_INCONSISTENT___NIL_POINTS_TO = store_thm ("INFERENCE_INCONSISTENT___NIL_POINTS_TO",
“!a c1 c2 pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_points_to dse_nil a)::sfL) (pfL', sfL')”,

REPEAT GEN_TAC THEN
ONCE_REWRITE_TAC [GSYM INFERENCE_NIL_NOT_LVAL___points_to] THEN
SIMP_TAC std_ss [INFERENCE_INCONSISTENT])


val INFERENCE_INCONSISTENT___precondition_POINTS_TO = store_thm ("INFERENCE_INCONSISTENT___precondition_POINTS_TO",
“!e a c1 c2 pfL sfL pfL' sfL'.
      MEM e c1 ==>
      (LIST_DS_ENTAILS (c1, c2) (pfL, (sf_points_to e a)::sfL) (pfL', sfL'))”,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, HEAP_DISTINCT_def] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN
FULL_SIMP_TAC std_ss [LIST_DS_SEM_EVAL, DS_POINTS_TO_def]);


val INFERENCE_INCONSISTENT___precondition_BIN_TREE = store_thm ("INFERENCE_INCONSISTENT___precondition_BIN_TREE",
“!e f1 f2 c1 c2 pfL sfL pfL' sfL'.
      MEM e c1 ==>
      (LIST_DS_ENTAILS (c1,c2) (pfL, (sf_bin_tree (f1, f2) e)::sfL) (pfL', sfL'))”,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, HEAP_DISTINCT_def] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN
FULL_SIMP_TAC std_ss [LIST_DS_SEM_THM, sf_bin_tree_def, SF_SEM___sf_tree_THM] THEN
Cases_on ‘DS_EXPRESSION_EQUAL s e dse_nil’ THENL [
   FULL_SIMP_TAC std_ss [FUNION_FEMPTY_1, DS_EXPRESSION_EQUAL_def, dse_nil_def,
      DS_EXPRESSION_EVAL_def, IS_DSV_NIL_def],

   FULL_SIMP_TAC list_ss [LET_THM, SF_SEM___sf_points_to_THM, DS_POINTS_TO_def,
      DS_EXPRESSION_EVAL_def] THEN
   Q.PAT_X_ASSUM ‘h = FUNION h1 h2’ ASSUME_TAC THEN
   FULL_SIMP_TAC std_ss [FUNION_DEF, IN_UNION]
])



val INFERENCE___NIL_LIST = store_thm ("INFERENCE___NIL_LIST",
“!c1 c2 e f pfL sfL pfL' sfL'.
      LIST_DS_ENTAILS (c1,c2) ((pf_equal e dse_nil)::pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_ls f dse_nil e)::sfL) (pfL', sfL')”,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_EVAL] THEN
REPEAT GEN_TAC THEN
HO_MATCH_MP_TAC (prove (“(!s h. (P s h = Q s h)) ==> ((!s h. P s h) = (!s h. Q s h))”, METIS_TAC[])) THEN
REPEAT GEN_TAC THEN
Cases_on ‘DS_EXPRESSION_EQUAL s e dse_nil’ THENL [
   ‘DS_EXPRESSION_EQUAL s dse_nil e’ by METIS_TAC[DS_EXPRESSION_EQUAL_def] THEN
   ASM_SIMP_TAC std_ss [LIST_DS_SEM_EVAL],

   ‘~(DS_EXPRESSION_EQUAL s dse_nil e)’ by METIS_TAC[DS_EXPRESSION_EQUAL_def] THEN
   ASM_SIMP_TAC std_ss [LIST_DS_SEM_EVAL, DS_POINTS_TO_def, dse_nil_def,
      DS_EXPRESSION_EVAL_def, IS_DSV_NIL_def, LET_THM]
])



val INFERENCE___precondition_LIST = store_thm ("INFERENCE___precondition_LIST",
“!c1 c2 e' e f pfL sfL pfL' sfL'.
      MEM e' c1 ==>

      (LIST_DS_ENTAILS (c1, c2) ((pf_equal e e')::pfL, sfL) (pfL', sfL') =
      LIST_DS_ENTAILS (c1, c2) (pfL, (sf_ls f e' e)::sfL) (pfL', sfL'))”,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_EVAL] THEN
REPEAT STRIP_TAC THEN
REPEAT STRIP_EQ_FORALL_TAC THEN
STRIP_EQ_BOOL_TAC THEN
SIMP_TAC list_ss [LIST_DS_SEM_THM, SF_SEM___sf_ls_THM] THEN
STRIP_EQ_BOOL_TAC THEN
Cases_on ‘DS_EXPRESSION_EQUAL s e e'’ THEN1 (
   FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def, FUNION_FEMPTY_1, FDOM_FEMPTY, DISJOINT_EMPTY]
) THEN
FULL_SIMP_TAC list_ss [LET_THM, DS_EXPRESSION_EQUAL_def, SF_SEM___sf_points_to_THM, DS_POINTS_TO_def,
   DS_EXPRESSION_EVAL_def, DS_EXPRESSION_EVAL_VALUE_def, HEAP_DISTINCT_def] THEN
RES_TAC THEN
REPEAT GEN_TAC THEN
Cases_on ‘h = FUNION h1 h2’ THEN ASM_REWRITE_TAC[] THEN
FULL_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION]
);


val INFERENCE___precondition_STRENGTHEN = store_thm ("INFERENCE___precondition_STRENGTHEN",
“!c1 c2 e1 e2 pfL sfL pfL' sfL'.
      (LIST_DS_ENTAILS (e1::c1, c2) ((pf_unequal e1 e2)::pfL, sfL) (pfL', sfL') =
       LIST_DS_ENTAILS (c1, ((e1,e2)::c2)) ((pf_unequal e1 e2)::pfL, sfL) (pfL', sfL'))”,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_EVAL] THEN
METIS_TAC[HEAP_DISTINCT___UNEQUAL])





val INFERENCE_UNROLL_COLLAPSE_LS___NON_EMPTY = store_thm ("INFERENCE_UNROLL_COLLAPSE_LS___NON_EMPTY",
“!e1:('b, 'a) ds_expression e2 f c1 c2 pfL sfL pfL' sfL'.
      (INFINITE (UNIV:'b set)) ==>

      ((!x. LIST_DS_ENTAILS (c1,c2) ((pf_unequal e1 e2)::(pf_unequal (dse_const x) e2)::pfL,
                              (sf_points_to e1 [(f, dse_const x)])::(sf_points_to (dse_const x) [(f, e2)])::sfL) (pfL', sfL')) =
      LIST_DS_ENTAILS (c1,c2) ((pf_unequal e1 e2)::pfL, (sf_ls f e1 e2)::sfL) (pfL', sfL'))”,


REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [Once (GSYM INFERENCE_UNROLL_COLLAPSE_LS)] THEN
SIMP_TAC list_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_EVAL] THEN
METIS_TAC[])




val INFERENCE_LIST_APPEND___helper = prove (“
!e1 e2 e3 e1' x f s h pfL' sfL'.
((e1' = DS_EXPRESSION_EVAL_VALUE s e1) /\
~(DS_EXPRESSION_EQUAL s (dse_const x) e2) /\
~(DS_EXPRESSION_EQUAL s (dse_const x) e3) /\
DS_POINTS_TO s h e1 [(f, dse_const x)] /\
DS_POINTS_TO s (h \\ e1') (dse_const x) [(f, e2)]) ==>

(LIST_DS_SEM s (h \\ e1')
(pfL', sf_ls f (dse_const (h ' e1' ' f)) e2::sf_ls f e2 e3::sfL') =
LIST_DS_SEM s (h \\ e1') (pfL',
       sf_ls f (dse_const (h ' e1' ' f)) e3::sfL'))”,


REPEAT STRIP_TAC THEN
‘(h ' (GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1)) ' f) = x’ by (
   FULL_SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EVAL_VALUE_def,
      DS_EXPRESSION_EVAL_def]
) THEN
FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def, LIST_DS_SEM_EVAL, LET_THM,
   DS_EXPRESSION_EVAL_def] THEN
STRIP_EQ_BOOL_TAC THEN
‘DS_EXPRESSION_EQUAL s (dse_const
((h \\ GET_DSV_VALUE (DS_EXPRESSION_EVAL s e1)) '
(GET_DSV_VALUE x) ' f)) e2’ by (
   FULL_SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EVAL_VALUE_def,
      DS_EXPRESSION_EVAL_def, DS_EXPRESSION_EQUAL_def]
) THEN
ASM_SIMP_TAC std_ss [LIST_DS_SEM_EVAL] THEN
SIMP_TAC std_ss [LIST_DS_SEM_THM] THEN
REPEAT STRIP_EQ_EXISTS_TAC THEN
STRIP_EQ_BOOL_TAC THEN
SIMP_TAC list_ss [sf_ls_def, SF_SEM___sf_tree_def, SF_SEM_def] THEN
STRIP_EQ_EXISTS_TAC THEN
MATCH_MP_TAC SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM THEN
FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def])






val INFERENCE_APPEND_LIST___nil = store_thm ("INFERENCE_APPEND_LIST___nil",
“!e1:('b, 'a) ds_expression e2 f c1 c2 pfL sfL pfL' sfL'.
      (INFINITE (UNIV:'b set)) ==>

      ((LIST_DS_ENTAILS (c1,c2) (pfL, (sf_ls f e1 e2)::sfL) (pfL', (sf_ls f e1 e2)::(sf_ls f e2 dse_nil)::sfL')) =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_ls f e1 e2)::sfL) (pfL', (sf_ls f e1 dse_nil)::sfL'))”,


REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [GSYM INFERENCE_UNROLL_COLLAPSE_LS] THEN
BINOP_TAC THENL [
   SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
   REPEAT STRIP_EQ_FORALL_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   FULL_SIMP_TAC std_ss [LIST_DS_SEM_EVAL, PF_SEM_def] THEN
   SIMP_TAC std_ss [LIST_DS_SEM_THM] THEN
   REPEAT STRIP_EQ_EXISTS_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   SIMP_TAC list_ss [sf_ls_def, SF_SEM___sf_tree_def, SF_SEM_def] THEN
   STRIP_EQ_EXISTS_TAC THEN
   MATCH_MP_TAC SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM THEN
   FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def],


   SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
   REPEAT STRIP_EQ_FORALL_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   FULL_SIMP_TAC std_ss [LIST_DS_SEM_EVAL, LET_THM] THEN
   ‘~(DS_EXPRESSION_EQUAL s e1 dse_nil)’ by (
      FULL_SIMP_TAC std_ss [DS_POINTS_TO_def, DS_EXPRESSION_EQUAL_def,
         DS_EXPRESSION_EVAL_def, NOT_IS_DSV_NIL_THM, dse_nil_def, ds_value_distinct]
   ) THEN
   FULL_SIMP_TAC std_ss [LIST_DS_SEM_EVAL, LET_THM] THEN
   ‘(h ' (DS_EXPRESSION_EVAL_VALUE s e1) ' f) = x’ by (
      FULL_SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EVAL_VALUE_def,
         DS_EXPRESSION_EVAL_def]
   ) THEN
   ASM_SIMP_TAC std_ss [] THEN
   POP_ASSUM (ASSUME_TAC o GSYM)    THEN
   ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def] THEN

   MATCH_MP_TAC (SIMP_RULE std_ss [DS_EXPRESSION_EVAL_VALUE_def] INFERENCE_LIST_APPEND___helper) THEN
   Q.EXISTS_TAC ‘x’ THEN
   ASM_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def, NOT_IS_DSV_NIL_THM, DS_POINTS_TO_def,
      dse_nil_def, DS_EXPRESSION_EVAL_def, ds_value_distinct]
])




val INFERENCE_APPEND_LIST___precond = store_thm ("INFERENCE_APPEND_LIST___precond",
“!e1:('b, 'a) ds_expression e2 e3 f c1 c2 pfL sfL pfL' sfL'.
      (INFINITE (UNIV:'b set) /\
       MEM_UNEQ_PF_LIST e1 e3 pfL) ==>

      ((LIST_DS_ENTAILS (e3::c1,c2) (pfL, (sf_ls f e1 e2)::sfL) (pfL', (sf_ls f e1 e2)::(sf_ls f e2 e3)::sfL')) =
      LIST_DS_ENTAILS (e3::c1,c2) (pfL, (sf_ls f e1 e2)::sfL) (pfL', (sf_ls f e1 e3)::sfL'))”,


REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [GSYM INFERENCE_UNROLL_COLLAPSE_LS] THEN
BINOP_TAC THENL [
   SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
   REPEAT STRIP_EQ_FORALL_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   FULL_SIMP_TAC std_ss [LIST_DS_SEM_THM, PF_SEM_def] THEN
   ‘!h1. SF_SEM s h1 (sf_ls f e1 e2) = (h1 = FEMPTY)’ by ASM_SIMP_TAC std_ss [SF_SEM___sf_ls_THM] THEN
   ASM_SIMP_TAC std_ss [FUNION_FEMPTY_1, FDOM_FEMPTY, DISJOINT_EMPTY] THEN
   REPEAT STRIP_EQ_EXISTS_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   SIMP_TAC list_ss [sf_ls_def, SF_SEM___sf_tree_def, SF_SEM_def] THEN
   STRIP_EQ_EXISTS_TAC THEN
   MATCH_MP_TAC SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM THEN
   FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def],


   SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
   REPEAT STRIP_EQ_FORALL_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   FULL_SIMP_TAC std_ss [LIST_DS_SEM_EVAL, LET_THM] THEN
   ‘~(DS_EXPRESSION_EQUAL s e1 e3)’ by METIS_TAC[MEM_UNEQ_PF_LIST_SEM, LIST_DS_SEM_def] THEN
   FULL_SIMP_TAC std_ss [LIST_DS_SEM_EVAL, LET_THM] THEN
   ‘(h ' (DS_EXPRESSION_EVAL_VALUE s e1) ' f) = x’ by (
      FULL_SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EVAL_VALUE_def,
         DS_EXPRESSION_EVAL_def]
   ) THEN
   ASM_SIMP_TAC std_ss [] THEN
   POP_ASSUM (ASSUME_TAC o GSYM) THEN
   ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def] THEN

   MATCH_MP_TAC (SIMP_RULE std_ss [DS_EXPRESSION_EVAL_VALUE_def] INFERENCE_LIST_APPEND___helper) THEN
   Q.EXISTS_TAC ‘x’ THEN
   ASM_SIMP_TAC std_ss [] THEN
   POP_ASSUM (ASSUME_TAC o GSYM) THEN
   FULL_SIMP_TAC list_ss [DS_EXPRESSION_EQUAL_def, DS_POINTS_TO_def,
      dse_nil_def, DS_EXPRESSION_EVAL_def, ds_value_distinct, DS_EXPRESSION_EVAL_VALUE_def, HEAP_DISTINCT___IND_DEF, FDOM_DOMSUB, IN_DELETE] THEN
   METIS_TAC[]
]);




val INFERENCE_APPEND_LIST___points_to = store_thm ("INFERENCE_APPEND_LIST___points_to",
“!e1:('b, 'a) ds_expression e2 e3 a f c1 c2 pfL sfL pfL' sfL'.
      (INFINITE (UNIV:'b set) /\
       MEM_UNEQ_PF_LIST e1 e3 pfL) ==>

      ((LIST_DS_ENTAILS (c1,c2) (pfL, (sf_ls f e1 e2)::(sf_points_to e3 a)::sfL) (pfL', (sf_ls f e1 e2)::(sf_ls f e2 e3)::sfL')) =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_ls f e1 e2)::(sf_points_to e3 a)::sfL) (pfL', (sf_ls f e1 e3)::sfL'))”,


REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [GSYM INFERENCE_UNROLL_COLLAPSE_LS] THEN
BINOP_TAC THENL [
   SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
   REPEAT STRIP_EQ_FORALL_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   FULL_SIMP_TAC std_ss [LIST_DS_SEM_THM, PF_SEM_def] THEN
   ‘!h1. SF_SEM s h1 (sf_ls f e1 e2) = (h1 = FEMPTY)’ by ASM_SIMP_TAC std_ss [SF_SEM___sf_ls_THM] THEN
   ASM_SIMP_TAC std_ss [FUNION_FEMPTY_1, FDOM_FEMPTY, DISJOINT_EMPTY] THEN
   REPEAT STRIP_EQ_EXISTS_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   SIMP_TAC list_ss [sf_ls_def, SF_SEM___sf_tree_def, SF_SEM_def] THEN
   STRIP_EQ_EXISTS_TAC THEN
   MATCH_MP_TAC SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM THEN
   FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def],


   SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
   REPEAT STRIP_EQ_FORALL_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   FULL_SIMP_TAC std_ss [LIST_DS_SEM_EVAL, LET_THM] THEN
   ‘~(DS_EXPRESSION_EQUAL s e1 e3)’ by METIS_TAC[MEM_UNEQ_PF_LIST_SEM, LIST_DS_SEM_def] THEN
   FULL_SIMP_TAC std_ss [LIST_DS_SEM_EVAL, LET_THM] THEN
   ‘(h ' (DS_EXPRESSION_EVAL_VALUE s e1) ' f) = x’ by (
      FULL_SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EVAL_VALUE_def,
         DS_EXPRESSION_EVAL_def]
   ) THEN
   ASM_SIMP_TAC std_ss [] THEN
   POP_ASSUM (ASSUME_TAC o GSYM) THEN
   ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def] THEN

   MATCH_MP_TAC (SIMP_RULE std_ss [DS_EXPRESSION_EVAL_VALUE_def] INFERENCE_LIST_APPEND___helper) THEN
   Q.EXISTS_TAC ‘x’ THEN
   ASM_SIMP_TAC std_ss [] THEN
   POP_ASSUM (ASSUME_TAC o GSYM) THEN
   FULL_SIMP_TAC list_ss [DS_EXPRESSION_EQUAL_def, DS_POINTS_TO_def,
      dse_nil_def, DS_EXPRESSION_EVAL_def, ds_value_distinct, DS_EXPRESSION_EVAL_VALUE_def, HEAP_DISTINCT___IND_DEF, FDOM_DOMSUB, IN_DELETE] THEN
   METIS_TAC[]
])



val INFERENCE_APPEND_LIST___tree = store_thm ("INFERENCE_APPEND_LIST___tree",
“!e1:('b, 'a) ds_expression e2 e3 fL es f c1 c2 pfL sfL pfL' sfL'.
      (INFINITE (UNIV:'b set) /\
       MEM_UNEQ_PF_LIST e1 e3 pfL /\
       MEM_UNEQ_PF_LIST e3 es pfL) ==>

      ((LIST_DS_ENTAILS (c1,c2) (pfL, (sf_ls f e1 e2)::(sf_tree fL es e3)::sfL) (pfL', (sf_ls f e1 e2)::(sf_ls f e2 e3)::sfL')) =
      LIST_DS_ENTAILS (c1,c2) (pfL, (sf_ls f e1 e2)::(sf_tree fL es e3)::sfL) (pfL', (sf_ls f e1 e3)::sfL'))”,


REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [GSYM INFERENCE_UNROLL_COLLAPSE_LS] THEN
BINOP_TAC THENL [
   SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
   REPEAT STRIP_EQ_FORALL_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   FULL_SIMP_TAC std_ss [LIST_DS_SEM_THM, PF_SEM_def] THEN
   ‘!h1. SF_SEM s h1 (sf_ls f e1 e2) = (h1 = FEMPTY)’ by ASM_SIMP_TAC std_ss [SF_SEM___sf_ls_THM] THEN
   ASM_SIMP_TAC std_ss [FUNION_FEMPTY_1, FDOM_FEMPTY, DISJOINT_EMPTY] THEN
   REPEAT STRIP_EQ_EXISTS_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   SIMP_TAC list_ss [sf_ls_def, SF_SEM___sf_tree_def, SF_SEM_def] THEN
   STRIP_EQ_EXISTS_TAC THEN
   MATCH_MP_TAC SF_SEM___sf_tree_len___DS_EXPRESSION_EQUAL_THM THEN
   FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def],


   SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
   REPEAT STRIP_EQ_FORALL_TAC THEN
   STRIP_EQ_BOOL_TAC THEN
   FULL_SIMP_TAC std_ss [LIST_DS_SEM_EVAL, LET_THM] THEN
   ‘~(DS_EXPRESSION_EQUAL s e1 e3)’ by METIS_TAC[MEM_UNEQ_PF_LIST_SEM, LIST_DS_SEM_def] THEN
   ‘~(DS_EXPRESSION_EQUAL s e3 es)’ by METIS_TAC[MEM_UNEQ_PF_LIST_SEM, LIST_DS_SEM_def] THEN
   FULL_SIMP_TAC std_ss [LIST_DS_SEM_EVAL, LET_THM] THEN
   ‘(h ' (DS_EXPRESSION_EVAL_VALUE s e1) ' f) = x’ by (
      FULL_SIMP_TAC list_ss [DS_POINTS_TO_def, DS_EXPRESSION_EVAL_VALUE_def,
         DS_EXPRESSION_EVAL_def]
   ) THEN
   ASM_SIMP_TAC std_ss [] THEN
   POP_ASSUM (ASSUME_TAC o GSYM) THEN
   ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def] THEN

   MATCH_MP_TAC (SIMP_RULE std_ss [DS_EXPRESSION_EVAL_VALUE_def] INFERENCE_LIST_APPEND___helper) THEN
   Q.EXISTS_TAC ‘x’ THEN
   ASM_SIMP_TAC std_ss [] THEN
   POP_ASSUM (ASSUME_TAC o GSYM) THEN
   Q.PAT_X_ASSUM ‘LIST_DS_SEM s H L’ MP_TAC THEN
   FULL_SIMP_TAC list_ss [DS_EXPRESSION_EQUAL_def, DS_POINTS_TO_def,
      dse_nil_def, DS_EXPRESSION_EVAL_def, ds_value_distinct, DS_EXPRESSION_EVAL_VALUE_def, FDOM_DOMSUB, IN_DELETE, LIST_DS_SEM_THM, SF_SEM___sf_tree_THM, LET_THM, SF_SEM___sf_points_to_THM] THEN
   REPEAT STRIP_TAC THEN
   METIS_TAC[]
])

val _ = export_theory();
