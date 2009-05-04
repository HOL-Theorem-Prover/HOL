open HolKernel Parse boolLib bossLib;

(*
quietdec := true;
loadPath := (Globals.HOLDIR ^ "/examples/decidable_separationLogic/src") :: 
            !loadPath;

map load ["finite_mapTheory", "relationTheory", "congLib", "sortingTheory",
   "rich_listTheory", "operatorTheory", "containerTheory", "bagTheory"];
show_assums := true;
*)

open finite_mapTheory relationTheory pred_setTheory congLib sortingTheory listTheory rich_listTheory arithmeticTheory operatorTheory containerTheory bagTheory stringLib;

(*
quietdec := false;
*)

val _ = new_theory "generalHelpers";



(*general stuff*)

fun MP_FREE_VAR_TAC var =
   POP_ASSUM_LIST (fn thmL =>
      EVERY (rev
      (map (fn thm => if (mem var (free_vars (concl thm))) then MP_TAC thm else ASSUME_TAC thm) thmL)));

local
   val thm = prove (``(!x. (P x = Q x)) ==> ((?x. P x) = (?x. Q x))``, METIS_TAC[]);
in
   val STRIP_EQ_EXISTS_TAC = 
      HO_MATCH_MP_TAC thm THEN
      GEN_TAC
end


local
   val thm = prove (``(!x. (P x = Q x)) ==> ((!x. P x) = (!x. Q x))``, METIS_TAC[]);
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
``!f. (\x. f x (FST x) (SND x)) = (\(x1,x2). f (x1,x2) x1 x2)``,

   SIMP_TAC std_ss [FUN_EQ_THM] THEN
   Cases_on `x` THEN
   SIMP_TAC std_ss []
);


val PAIR_FORALL_THM = store_thm ("PAIR_FORALL_THM",
``(!x:('a # 'b). P x) = (!x1 x2. P (x1,x2))``,
SIMP_TAC std_ss [PAIR_BETA_THM, pairTheory.PFORALL_THM]);


val PAIR_EXISTS_THM = store_thm ("PAIR_EXISTS_THM",
``(?x:('a # 'b). P x) = (?x1 x2. P (x1,x2))``,
SIMP_TAC std_ss [PAIR_BETA_THM, pairTheory.PEXISTS_THM]);



val EL_DISJOINT_FILTER = store_thm ("EL_DISJOINT_FILTER",

   ``!n1 n2 P l. (~(n1 = n2) /\ (n1 < LENGTH l) /\ (n2 < LENGTH l) /\ 
                   (EL n1 l = EL n2 l) /\ (P (EL n2 l))) ==>
                 ?n1' n2'. ~(n1' = n2') /\ 
                           (n1' < LENGTH (FILTER P l)) /\
                           (n2' < LENGTH (FILTER P l)) /\
                           (EL n1' (FILTER P l) = EL n2 l) /\
                           (EL n2' (FILTER P l) = EL n2 l)``,

   HO_MATCH_MP_TAC (prove (``((!n1 n2. P n1 n2 = P n2 n1) /\ (!n1 n2. (n1 <= n2) ==> P n1 n2)) ==> 
                             (!n1 n2. P n1 n2)``,
                    METIS_TAC[arithmeticTheory.LESS_EQ_CASES])) THEN
   CONJ_TAC THEN1 METIS_TAC[] THEN
   REPEAT STRIP_TAC THEN

   `l = (FIRSTN (SUC n1) l) ++ (LASTN (LENGTH l - (SUC n1)) l)` by ALL_TAC THEN1 (
      MATCH_MP_TAC (GSYM APPEND_FIRSTN_LASTN) THEN
      ASM_SIMP_TAC arith_ss []
   ) THEN
   Q.ABBREV_TAC `l1 = (FIRSTN (SUC n1) l)` THEN
   Q.ABBREV_TAC `l2 = (LASTN (LENGTH l - (SUC n1)) l)` THEN
   `(n1 < LENGTH l1) /\ (LENGTH l1 <= n2)` by ALL_TAC THEN1 (
      bossLib.UNABBREV_ALL_TAC THEN
      ASM_SIMP_TAC list_ss [LENGTH_FIRSTN]
   ) THEN
   FULL_SIMP_TAC list_ss [EL_APPEND2, EL_APPEND1] THEN
   `n2 - LENGTH l1 < LENGTH l2` by DECIDE_TAC THEN
   `MEM (EL n1 l1) (FILTER P l1)` by METIS_TAC[MEM_FILTER, MEM_EL] THEN
   `MEM (EL n1 l1) (FILTER P l2)` by METIS_TAC[MEM_FILTER, MEM_EL] THEN
   FULL_SIMP_TAC list_ss [MEM_EL, FILTER_APPEND] THEN
   Q.EXISTS_TAC `n` THEN
   Q.EXISTS_TAC `LENGTH (FILTER P l1) + n'` THEN
   ASM_SIMP_TAC list_ss [EL_APPEND1, EL_APPEND2] THEN
   METIS_TAC[]
);


val APPEND_EQ_SELF = store_thm("APPEND_EQ_SELF",

``((l1 ++ l2 = l1) = (l2 = [])) /\
  ((l1 ++ l2 = l2) = (l1 = [])) /\
  ((l1 = l1 ++ l2) = (l2 = [])) /\
  ((l2 = l1 ++ l2) = (l1 = []))``,

METIS_TAC[APPEND_11, APPEND_NIL])


val FORALL_LESS_SUC = store_thm ("FORALL_LESS_SUC",
   ``!P m. ((!n. n < SUC m ==> P n) =
            (P 0 /\ (!n. n < m ==> P (SUC n))))``,

   REPEAT GEN_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THENL [
      ASM_SIMP_TAC arith_ss [],
      ASM_SIMP_TAC arith_ss [],

      Cases_on `n` THENL [
         ASM_REWRITE_TAC[],
         ASM_SIMP_TAC arith_ss []
      ]
   ])



val IN_FDOM_FOLDR_UNION = store_thm ("IN_FDOM_FOLDR_UNION",
``!x hL. x IN FDOM (FOLDR FUNION FEMPTY hL) =
        ?h. MEM h hL /\ x IN FDOM h``,

Induct_on `hL` THENL [
   SIMP_TAC list_ss [FDOM_FEMPTY, NOT_IN_EMPTY],

   FULL_SIMP_TAC list_ss [FDOM_FUNION, IN_UNION, DISJ_IMP_THM] THEN
   METIS_TAC[]
])

val REPLACE_ELEMENT_def = Define `
   (REPLACE_ELEMENT e n [] = []) /\
   (REPLACE_ELEMENT e 0 (x::l) = e::l) /\
   (REPLACE_ELEMENT e (SUC n) (x::l) = x::REPLACE_ELEMENT e n l)`


val REPLACE_ELEMENT_SEM = store_thm ("REPLACE_ELEMENT_SEM",
   ``!e n l.
         (LENGTH (REPLACE_ELEMENT e n l) = LENGTH l) /\
         (!p. p < LENGTH l ==>
            (EL p (REPLACE_ELEMENT e n l) =
             if (p = n) then e else EL p l))``,

   Induct_on `n` THENL [
      Cases_on `l` THEN (
         SIMP_TAC list_ss [REPLACE_ELEMENT_def]
      ) THEN
      Cases_on `p` THEN (
         SIMP_TAC list_ss []
      ),


      Cases_on `l` THEN (
         ASM_SIMP_TAC list_ss [REPLACE_ELEMENT_def]
      ) THEN
      Cases_on `p` THEN (
         ASM_SIMP_TAC list_ss []
      )
   ]);

val FINITE___LIST_TO_SET = save_thm ("FINITE___LIST_TO_SET",
   FINITE_LIST_TO_SET);

val MEM_LAST_FRONT = prove (``
!e l h.
MEM e l /\ ~(e = LAST (h::l)) ==>
MEM e (FRONT (h::l))``,

Induct_on `l` THENL [
   SIMP_TAC list_ss [],

   ASM_SIMP_TAC list_ss [] THEN
   Cases_on `l` THEN (
      FULL_SIMP_TAC list_ss [] THEN
      METIS_TAC[]
   )
]);


val EL_ALL_DISTINCT_EQ = store_thm ("EL_ALL_DISTINCT_EQ",
   ``!l. ALL_DISTINCT l =
         (!n1 n2. n1 < LENGTH l /\ n2 < LENGTH l ==>
         ((EL n1 l = EL n2 l) = (n1 = n2)))``,

   Induct_on `l` THENL [
      SIMP_TAC list_ss [],
      
      ASM_SIMP_TAC list_ss [ALL_DISTINCT] THEN
      GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
         Cases_on `n1` THEN Cases_on `n2` THENL [
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
            POP_ASSUM (fn thm => ASSUME_TAC (Q.SPECL [`0`, `SUC n`] thm)) THEN
            FULL_SIMP_TAC list_ss [] THEN
            METIS_TAC[],

            REPEAT GEN_TAC THEN
            POP_ASSUM (fn thm => ASSUME_TAC (Q.SPECL [`SUC n1`, `SUC n2`] thm)) THEN
            FULL_SIMP_TAC list_ss [] THEN
            METIS_TAC[]
         ]
      ]
   ]);
   


val EL_ALL_DISTINCT = store_thm ("EL_ALL_DISTINCT",
   ``!l n1 n2. ALL_DISTINCT l /\ n1 < LENGTH l /\ n2 < LENGTH l ==>
         ((EL n1 l = EL n2 l) = (n1 = n2))``,

   METIS_TAC[EL_ALL_DISTINCT_EQ]);


val FILTER_ALL_DISTINCT = store_thm ("FILTER_ALL_DISTINCT",
   ``!P l. ALL_DISTINCT l ==> ALL_DISTINCT (FILTER P l)``,

   Induct_on `l` THENL [
      SIMP_TAC list_ss [],

      SIMP_TAC list_ss [] THEN
      REPEAT STRIP_TAC THEN
      Cases_on `P h` THENL [
         ASM_SIMP_TAC list_ss [MEM_FILTER],
         ASM_SIMP_TAC list_ss []
      ]
   ])


val LIST_TO_BAG___APPEND = store_thm ("LIST_TO_BAG___APPEND",
``!l1 l2.
LIST_TO_BAG (l1 ++ l2) =
BAG_UNION (LIST_TO_BAG l1) (LIST_TO_BAG l2)``,

Induct_on `l1` THENL [
	SIMP_TAC list_ss [LIST_TO_BAG_def, BAG_UNION_EMPTY],

	ASM_SIMP_TAC list_ss [LIST_TO_BAG_def, BAG_UNION_INSERT]
]);

val MEM_SPLIT = store_thm ("MEM_SPLIT",
``!h l.
(MEM h l) =
?M N. (l = M ++ h::N)``,

Induct_on `l` THEN (
	ASM_SIMP_TAC list_ss []
) THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
	Q.EXISTS_TAC `[]` THEN
	ASM_SIMP_TAC list_ss [],

	Q.EXISTS_TAC `h::M` THEN
	ASM_SIMP_TAC list_ss [],

	Cases_on `M` THENL [
		FULL_SIMP_TAC list_ss [],

		FULL_SIMP_TAC list_ss [] THEN
		METIS_TAC[]
	]
]);



val IN_LIST_TO_BAG = store_thm ("IN_LIST_TO_BAG",
``!h l. BAG_IN h (LIST_TO_BAG l) = MEM h l``,

Induct_on `l` THENL [
	SIMP_TAC list_ss [LIST_TO_BAG_def, NOT_IN_EMPTY_BAG],
	ASM_SIMP_TAC list_ss [LIST_TO_BAG_def, BAG_IN_BAG_INSERT]
]);


val LIST_TO_BAG_EQ_EMPTY = store_thm ("LIST_TO_BAG_EQ_EMPTY",
``!l. (LIST_TO_BAG l = EMPTY_BAG) = (l = [])``,

Cases_on `l` THEN
SIMP_TAC list_ss [containerTheory.LIST_TO_BAG_def,
		  bagTheory.BAG_INSERT_NOT_EMPTY]);




val BAG_INN_BAG_INSERT_STRONG = store_thm ("BAG_INN_BAG_INSERT_STRONG",
 ``!b n e1 e2.
            BAG_INN e1 n (BAG_INSERT e2 b) =
            BAG_INN e1 (n - 1) b /\ (e1 = e2) \/ BAG_INN e1 n b /\ ~(e1 = e2)``,

SIMP_TAC std_ss [BAG_INN_BAG_INSERT] THEN
Cases_on `n` THEN SIMP_TAC arith_ss [] THENL [
	METIS_TAC[],

	`n' < SUC n'` by DECIDE_TAC THEN
	METIS_TAC[BAG_INN_LESS]
]);



val PERM_LIST_TO_BAG = store_thm ("PERM_LIST_TO_BAG",
`` !l1 l2. (LIST_TO_BAG l1 = LIST_TO_BAG l2) =
           PERM l1 l2``,

Induct_on `l1` THENL [
	Cases_on `l2` THEN 
	SIMP_TAC list_ss [FORALL_AND_THM, PERM_REFL,
	LIST_TO_BAG_def, BAG_INSERT_NOT_EMPTY,
	PERM_NIL],

	SIMP_TAC list_ss [PERM_CONS_EQ_APPEND] THEN
	REPEAT STRIP_TAC THEN Tactical.REVERSE EQ_TAC THEN1 (
		REPEAT STRIP_TAC THEN
		`LIST_TO_BAG l1 = LIST_TO_BAG (M++N)` by PROVE_TAC[] THEN
		ASM_SIMP_TAC std_ss [LIST_TO_BAG_def, LIST_TO_BAG___APPEND,
			BAG_UNION_INSERT]
	) THEN
	REPEAT STRIP_TAC THEN
	`MEM h l2` by ALL_TAC THEN1 (
		ONCE_REWRITE_TAC [GSYM IN_LIST_TO_BAG] THEN
		Q.PAT_ASSUM `X = LIST_TO_BAG l2` (fn thm => REWRITE_TAC[GSYM thm]) THEN
		SIMP_TAC std_ss [LIST_TO_BAG_def, BAG_IN_BAG_INSERT]
	) THEN
	FULL_SIMP_TAC std_ss [MEM_SPLIT] THEN
	Q.EXISTS_TAC `M` THEN
	Q.EXISTS_TAC `N` THEN
	ASM_SIMP_TAC std_ss [] THEN
	Q.PAT_ASSUM `!l2. X l2 = PERM l1 l2` (ASSUME_TAC o GSYM) THEN
	FULL_SIMP_TAC std_ss [BAG_EXTENSION, LIST_TO_BAG___APPEND,
		LIST_TO_BAG_def, BAG_INN_BAG_INSERT_STRONG, BAG_INN_BAG_UNION] THEN
	REPEAT GEN_TAC THEN
	Cases_on `e = h` THENL [
		Q.PAT_ASSUM `!n e. X n e` (MP_TAC o Q.SPECL [`SUC n`, `e`]) THEN
		ASM_SIMP_TAC std_ss [] THEN
		REPEAT STRIP_TAC THEN
		HO_MATCH_MP_TAC (prove ( 
			``(!m1 m2. X m1 (SUC m2) = Y m1 m2) /\ ~(X 0 0) /\ (!m1. X (SUC m1) 0 ==> Y m1 0) ==>
			((?m1 m2. X m1 m2) = (?m1 m2. Y m1 m2))``,
				METIS_TAC[num_CASES])) THEN
		SIMP_TAC arith_ss [ADD_CLAUSES] THEN
		`n < SUC n` by DECIDE_TAC THEN
		PROVE_TAC[BAG_INN_LESS],


		Q.PAT_ASSUM `!n e. X n e` (MP_TAC o Q.SPECL [`n`, `e`]) THEN
		ASM_SIMP_TAC std_ss []
	]
]);

		


val PERM_ALL_DISTINCT = store_thm ("PERM_ALL_DISTINCT",
`` !l1 l2. (ALL_DISTINCT l1 /\ ALL_DISTINCT l2 /\
            (!x. MEM x l1 = MEM x l2)) ==>
           PERM l1 l2``,

Induct_on `l1` THENL [
   Cases_on `l2` THEN SIMP_TAC list_ss [FORALL_AND_THM, PERM_REFL],

   SIMP_TAC list_ss [] THEN
   REPEAT STRIP_TAC THEN

   `?l2'. l2' = FILTER (\x. x = h) l2 ++ (FILTER ($~ o (\x. x = h)) l2)` by METIS_TAC[] THEN
   `PERM l2 l2'` by METIS_TAC[PERM_SPLIT] THEN
   Tactical.REVERSE (`PERM (h::l1) l2'` by ALL_TAC) THEN1 (
      METIS_TAC[PERM_TRANS, PERM_SYM]
   ) THEN
   `FILTER (\x. x = h) l2 = [h]` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `ALL_DISTINCT l2` MP_TAC THEN
      `MEM h l2` by METIS_TAC[] THEN
      POP_ASSUM MP_TAC THEN
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      Induct_on `l2` THENL [
         SIMP_TAC list_ss [],

         SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN 
         REPEAT STRIP_TAC THENL [
            Q.PAT_ASSUM `MEM h l2 ==> X` (K ALL_TAC) THEN
            Induct_on `l2` THENL [
               SIMP_TAC list_ss [],
               ASM_SIMP_TAC list_ss []
            ],


            FULL_SIMP_TAC std_ss [] THEN
            METIS_TAC[]
         ]
      ]
   ) THEN
   ASM_SIMP_TAC list_ss [PERM_CONS_IFF] THEN

   Q.PAT_ASSUM `!l2. P l2 ==> PERM l1 l2` MATCH_MP_TAC THEN
   ASM_SIMP_TAC list_ss [MEM_FILTER] THEN
   CONJ_TAC THENL [
      MATCH_MP_TAC FILTER_ALL_DISTINCT THEN
      ASM_REWRITE_TAC[],

      METIS_TAC[]
   ]
]);

val FOLDL_EQ_FOLDR = store_thm ("FOLDL_EQ_FOLDR",
``!f e l.
(ASSOC f /\ COMM f) ==>
((FOLDL f e l) = (FOLDR f e l))``,

GEN_TAC THEN
SIMP_TAC std_ss [RIGHT_FORALL_IMP_THM] THEN
STRIP_TAC THEN
Induct_on `l` THENL [
	SIMP_TAC std_ss [FOLDR, FOLDL],

	ASM_SIMP_TAC std_ss [FOLDR, FOLDL] THEN
	POP_ASSUM (K ALL_TAC) THEN
	Induct_on `l` THENL [
		SIMP_TAC list_ss [] THEN
		METIS_TAC[COMM_DEF],

		ASM_SIMP_TAC list_ss [] THEN
		METIS_TAC[COMM_DEF, ASSOC_DEF]
	]
]);

val FOLDR_PERM = store_thm ("FOLDR_PERM",
``!f l1 l2 e.
(ASSOC f /\ COMM f) ==>
((PERM l1 l2) ==>
(FOLDR f e l1 = FOLDR f e l2))``,

SIMP_TAC std_ss [RIGHT_FORALL_IMP_THM] THEN
GEN_TAC THEN STRIP_TAC THEN
HO_MATCH_MP_TAC PERM_IND THEN
SIMP_TAC list_ss [] THEN
METIS_TAC[ASSOC_DEF, COMM_DEF]);


val PERM_MAP = store_thm ("PERM_MAP",
``!l1 l2. PERM l1 l2 ==> !f. (PERM (MAP f l1) (MAP f l2))``,

   HO_MATCH_MP_TAC PERM_IND THEN
   SIMP_TAC list_ss [] THEN
   REPEAT STRIP_TAC THENL [
      REWRITE_TAC[PERM_REFL],
      ASM_REWRITE_TAC[PERM_CONS_IFF],
      ASM_REWRITE_TAC[PERM_SWAP_AT_FRONT],
      PROVE_TAC [PERM_TRANS, PERM_SYM]
   ]);


val PERM_APPEND_IFF = store_thm ("PERM_APPEND_IFF",
``(!l:'a list l1 l2. PERM (l++l1) (l++l2) = PERM l1 l2) /\
  (!l:'a list l1 l2. PERM (l1++l) (l2++l) = PERM l1 l2)``,

   MATCH_MP_TAC (prove (``(a /\ (a ==> b)) ==> (a /\ b)``, PROVE_TAC[])) THEN
   CONJ_TAC THENL [
      Induct_on `l` THENL [
         SIMP_TAC list_ss [],
         ASM_SIMP_TAC list_ss [PERM_CONS_IFF]
      ],

      METIS_TAC[PERM_APPEND, PERM_TRANS]
   ]
);

val PERM_FILTER = store_thm ("PERM_FILTER",
``!l1 l2. PERM l1 l2 ==> !P. (PERM (FILTER P l1) (FILTER P l2))``,

   HO_MATCH_MP_TAC PERM_IND THEN
   SIMP_TAC list_ss [] THEN
   REPEAT STRIP_TAC THENL [
      REWRITE_TAC[PERM_REFL],
      Cases_on `P x` THEN ASM_REWRITE_TAC[PERM_CONS_IFF],

      Cases_on `P x` THEN Cases_on `P y` THEN
      ASM_REWRITE_TAC[PERM_SWAP_AT_FRONT, PERM_CONS_IFF],

      PROVE_TAC [PERM_TRANS, PERM_SYM]
   ]);



val EL_HD_LAST = store_thm ("EL_HD_LAST",
   ``!l. 0 < LENGTH l ==>
          ((HD l = EL 0 l) /\
          (LAST l = EL (PRE (LENGTH l)) l))``,

   SIMP_TAC list_ss [] THEN
   Induct_on `l` THENL [
      SIMP_TAC list_ss [],

      SIMP_TAC list_ss [] THEN
      Cases_on `l` THENL [
         SIMP_TAC list_ss [],
         FULL_SIMP_TAC list_ss []
      ]
   ]);

val MEM_FRONT = store_thm ("MEM_FRONT",
   ``!l y. MEM y (FRONT (e::l)) ==> MEM y (e::l)``,

Induct_on `l` THENL [
   SIMP_TAC list_ss [],

   Cases_on `l` THEN
   FULL_SIMP_TAC list_ss [DISJ_IMP_THM] THEN
   METIS_TAC[]
]);


val LAST_APPEND = store_thm ("LAST_APPEND",
   ``LAST (l1 ++ (e::l2)) = LAST (e::l2)``,
   Induct_on `l1` THENL [
      SIMP_TAC list_ss [],
      ASM_SIMP_TAC list_ss [LAST_DEF]
   ])

val MEM_LAST = store_thm ("MEM_LAST",
   ``!e l. MEM (LAST (e::l)) (e::l)``,
     Induct_on `l` THENL [
         ASM_SIMP_TAC list_ss [],

         SIMP_TAC std_ss [Once MEM, LAST_CONS] THEN
         ASM_SIMP_TAC std_ss []
      ])


val ALL_DISTINCT_APPEND = store_thm ("ALL_DISTINCT_APPEND",
   ``!l1 l2. ALL_DISTINCT (l1++l2) =
             (ALL_DISTINCT l1 /\ ALL_DISTINCT l2 /\
             (!e. MEM e l1 ==> ~(MEM e l2)))``,

   Induct_on `l1` THENL [
      SIMP_TAC list_ss [],

      ASM_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
      PROVE_TAC[]
   ])

val ALL_DISTINCT_SNOC = store_thm ("ALL_DISTINCT_SNOC",
   ``!x l. ALL_DISTINCT (SNOC x l) =
             ~(MEM x l) /\ (ALL_DISTINCT l)``,

   SIMP_TAC list_ss [SNOC_APPEND, ALL_DISTINCT_APPEND] THEN
   METIS_TAC[])


val FUNION_EQ_FEMPTY = store_thm ("FUNION_EQ_FEMPTY",
``!h1 h2. (FUNION h1 h2 = FEMPTY) = ((h1 = FEMPTY) /\ (h2 = FEMPTY))``,

   SIMP_TAC std_ss [GSYM fmap_EQ_THM, EXTENSION, FDOM_FEMPTY, FUNION_DEF,
      NOT_IN_EMPTY, IN_UNION, DISJ_IMP_THM, FORALL_AND_THM] THEN
   METIS_TAC[]);



val SUBMAP___FUNION_EQ = store_thm ("SUBMAP___FUNION_EQ",
``(!f1 f2 f3. DISJOINT (FDOM f1) (FDOM f2) ==> (((f1 SUBMAP (FUNION f2 f3)) = (f1 SUBMAP f3)))) /\
  (!f1 f2 f3. DISJOINT (FDOM f1) (FDOM f3 DIFF (FDOM f2)) ==> (((f1 SUBMAP (FUNION f2 f3)) = (f1 SUBMAP f2))))``,

  SIMP_TAC std_ss [SUBMAP_DEF, FUNION_DEF, IN_UNION, DISJOINT_DEF, EXTENSION, 
   NOT_IN_EMPTY, IN_INTER, IN_DIFF] THEN
  METIS_TAC[])


val SUBMAP___FUNION = store_thm ("SUBMAP___FUNION",
``!f1 f2 f3. (f1 SUBMAP f2) \/ ((DISJOINT (FDOM f1) (FDOM f2) /\ (f1 SUBMAP f3))) ==> (f1 SUBMAP (FUNION f2 f3))``,

SIMP_TAC std_ss [SUBMAP_DEF, FUNION_DEF, IN_UNION, DISJOINT_DEF, EXTENSION, 
   NOT_IN_EMPTY, IN_INTER] THEN
METIS_TAC[]);

val SUBMAP___FUNION___ID = store_thm ("SUBMAP___FUNION___ID",
``(!f1 f2. (f1 SUBMAP (FUNION f1 f2))) /\
(!f1 f2. (DISJOINT (FDOM f1) (FDOM f2)) ==> (f2 SUBMAP (FUNION f1 f2)))``,
   
METIS_TAC[SUBMAP_REFL, SUBMAP___FUNION, DISJOINT_SYM]);

val FEMPTY_SUBMAP = store_thm ("FEMPTY_SUBMAP",
   ``!h. h SUBMAP FEMPTY = (h = FEMPTY)``,

   SIMP_TAC std_ss [SUBMAP_DEF, FDOM_FEMPTY, NOT_IN_EMPTY, GSYM fmap_EQ_THM,
      EXTENSION] THEN
   METIS_TAC[]);


val FUNION_EQ = store_thm ("FUNION_EQ",
``!f1 f2 f3. (DISJOINT (FDOM f1) (FDOM f2) /\
              DISJOINT (FDOM f1) (FDOM f3)) ==> 
             (((FUNION f1 f2) = (FUNION f1 f3)) = (f2 = f3))``,

  SIMP_TAC std_ss [GSYM SUBMAP_ANTISYM, SUBMAP_DEF, FUNION_DEF, IN_UNION, DISJOINT_DEF, EXTENSION, 
   NOT_IN_EMPTY, IN_INTER, IN_DIFF] THEN
  METIS_TAC[])

val FUNION_EQ___IMPL = store_thm ("FUNION_EQ___IMPL",
``!f1 f2 f3. (DISJOINT (FDOM f1) (FDOM f2) /\
              DISJOINT (FDOM f1) (FDOM f3) /\ (f2 = f3)) ==> 
             ((FUNION f1 f2) = (FUNION f1 f3))``,

  METIS_TAC[FUNION_EQ]);


val DOMSUB_FUNION = store_thm ("DOMSUB_FUNION",
``(FUNION f g) \\ k = FUNION (f \\ k) (g \\ k)``,

SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_DOMSUB, FUNION_DEF, EXTENSION,
   IN_UNION, IN_DELETE] THEN
REPEAT STRIP_TAC THENL [
   METIS_TAC[],
   ASM_SIMP_TAC std_ss [DOMSUB_FAPPLY_NEQ, FUNION_DEF],
   ASM_SIMP_TAC std_ss [DOMSUB_FAPPLY_NEQ, FUNION_DEF]
]);


val FUNION___COMM = store_thm ("FUNION___COMM",
``!f g. (DISJOINT (FDOM f) (FDOM g)) ==> ((FUNION f g) = (FUNION g f))``,

   SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, IN_UNION, DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER] THEN
   METIS_TAC[])

val FUNION___ASSOC = store_thm ("FUNION___ASSOC",
``!f g h. ((FUNION f (FUNION g h)) = (FUNION (FUNION f g) h))``,

   SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, IN_UNION, EXTENSION] THEN
   METIS_TAC[])

val FRONT___APPEND = store_thm ("FRONT___APPEND",

   ``FRONT (l1 ++ e::l2) = l1++FRONT(e::l2)``,

     Induct_on `l1` THEN ASM_SIMP_TAC list_ss [FRONT_DEF])


val FRONT___LENGTH = store_thm ("FRONT___LENGTH",
   ``!l. ~(l = []) ==> (LENGTH (FRONT l) = PRE (LENGTH l))``,
   Induct_on `l` THENL [
      SIMP_TAC std_ss [],

      ASM_SIMP_TAC list_ss [FRONT_DEF, COND_RATOR, COND_RAND] THEN
      Cases_on `l` THEN SIMP_TAC list_ss []
   ])


val EL_FRONT = store_thm ("EL_FRONT",
   ``!l n. ((n < LENGTH (FRONT l)) /\ (~(l = []))) ==>
           (EL n (FRONT l) = EL n l)``,

   Induct_on `l` THENL [
      SIMP_TAC list_ss [],
   
      Cases_on `l` THEN 
      FULL_SIMP_TAC list_ss [FRONT___LENGTH] THEN
      REPEAT STRIP_TAC THEN
      Cases_on `n` THENL [
         SIMP_TAC list_ss [],
         FULL_SIMP_TAC list_ss []
      ]
   ])
         

val BUTFIRSTN___CONCAT_EL = store_thm ("BUTFIRSTN___CONCAT_EL",
   ``!n. (n < LENGTH l) ==>
         ((BUTFIRSTN n l) = (EL n l) :: (BUTFIRSTN (SUC n) l))``,

   Induct_on `l` THENL [
      FULL_SIMP_TAC list_ss [],

      FULL_SIMP_TAC list_ss [BUTFIRSTN] THEN
      REPEAT STRIP_TAC THEN
      Cases_on `n` THENL [
         SIMP_TAC list_ss [BUTFIRSTN],
         FULL_SIMP_TAC list_ss [BUTFIRSTN]
      ]
   ])


val ALL_DISJOINT_def = Define `
   (ALL_DISJOINT [] = T) /\
   (ALL_DISJOINT (e1::l) = (EVERY (\e2. DISJOINT e1 e2) l) /\ ALL_DISJOINT l)`



val EL_ALL_DISJOINT_EQ = store_thm ("EL_ALL_DISJOINT_EQ",
   ``!l. ALL_DISJOINT l =
         (!n1 n2. n1 < LENGTH l /\ n2 < LENGTH l ==>
         (DISJOINT (EL n1 l) (EL n2 l) = (~(n1 = n2) \/ (EL n1 l = EMPTY))))``,

   Induct_on `l` THENL [
      SIMP_TAC list_ss [ALL_DISJOINT_def],
      
      ASM_SIMP_TAC list_ss [ALL_DISJOINT_def, EVERY_MEM] THEN
      GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
         Cases_on `n1` THEN Cases_on `n2` THENL [
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
            POP_ASSUM (fn thm => ASSUME_TAC (Q.SPECL [`0`, `SUC n`] thm)) THEN
            FULL_SIMP_TAC list_ss [] THEN
            METIS_TAC[],

            REPEAT GEN_TAC THEN
            POP_ASSUM (fn thm => ASSUME_TAC (Q.SPECL [`SUC n1`, `SUC n2`] thm)) THEN
            FULL_SIMP_TAC list_ss []
         ]
      ]
   ]);

val MAP_EQ_f = store_thm ("MAP_EQ_f",

   ``!f1 f2 l. (MAP f1 l = MAP f2 l) = (!e. MEM e l ==> (f1 e = f2 e))``,

   Induct_on `l` THENL [
      SIMP_TAC list_ss [],

      ASM_SIMP_TAC list_ss [] THEN
      METIS_TAC[]
   ])



val DRESTRICT_FUNION = store_thm ("DRESTRICT_FUNION",
   ``!h s1 s2. FUNION (DRESTRICT h s1) (DRESTRICT h s2) =
               DRESTRICT h (s1 UNION s2)``,

    SIMP_TAC std_ss [DRESTRICT_DEF, GSYM fmap_EQ_THM, EXTENSION,
      FUNION_DEF, IN_INTER, IN_UNION, DISJ_IMP_THM,
      LEFT_AND_OVER_OR]);



val DRESTRICT_EQ_FUNION = store_thm ("DRESTRICT_EQ_FUNION",
   ``!h h1 h2. (DISJOINT (FDOM h1) (FDOM h2)) /\ (FUNION h1 h2 = h) ==> (h2 = DRESTRICT h (COMPL (FDOM h1)))``,

    SIMP_TAC std_ss [DRESTRICT_DEF, GSYM fmap_EQ_THM, EXTENSION,
      FUNION_DEF, IN_INTER, IN_UNION, IN_COMPL, DISJOINT_DEF,
      NOT_IN_EMPTY] THEN
    METIS_TAC[]);



val ALL_DISJOINT___PERM = store_thm ("ALL_DISJOINT___PERM",
   ``!l1 l2. PERM l1 l2 ==> (ALL_DISJOINT l1 = ALL_DISJOINT l2)``,

   Tactical.REVERSE (`!l1 l2. PERM l1 l2 ==> ((PERM l1 l2) /\ (ALL_DISJOINT l1 = ALL_DISJOINT l2))` by ALL_TAC) THEN1 (
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
   ``!l1 l2. PERM l1 l2 ==> (ALL_DISTINCT l1 = ALL_DISTINCT l2)``,

   Tactical.REVERSE (`!l1 l2. PERM l1 l2 ==> ((PERM l1 l2) /\ (ALL_DISTINCT l1 = ALL_DISTINCT l2))` by ALL_TAC) THEN1 (
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
   ])


val ALL_DISJOINT___PERM = store_thm ("ALL_DISJOINT___PERM",
   ``!l1 l2. PERM l1 l2 ==> (ALL_DISJOINT l1 = ALL_DISJOINT l2)``,

   Tactical.REVERSE (`!l1 l2. PERM l1 l2 ==> ((PERM l1 l2) /\ (ALL_DISJOINT l1 = ALL_DISJOINT l2))` by ALL_TAC) THEN1 (
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



val LESS_EQ_ADD_EXISTS = store_thm ("LESS_EQ_ADD_EXISTS",
``!m n. n <= m ==> ?p. p + n = m``,
	REPEAT STRIP_TAC THEN
	Cases_on `n = m` THENL [
		Q.EXISTS_TAC `0` THEN
		ASM_SIMP_TAC arith_ss [],
	
		`n < m` by DECIDE_TAC THEN
		PROVE_TAC[LESS_ADD]
	]
);


val ADD_MOD = store_thm ("ADD_MOD",
``!x y n p.  (0 < n:num) ==> (
	      ((x + p) MOD n = (y + p) MOD n) =
	       (x MOD n = y MOD n)
)``,

REPEAT STRIP_TAC THEN
Induct_on `p` THENL [
	ASM_SIMP_TAC arith_ss [],
	FULL_SIMP_TAC arith_ss [ADD_CLAUSES, SUC_MOD]
]);


val MEM_FLAT = store_thm ("MEM_FLAT",
``!m ll. MEM m (FLAT ll) =
         (?l. MEM l ll /\ MEM m l)``,

Induct_on `ll` THENL [
   SIMP_TAC list_ss [],

   ASM_SIMP_TAC list_ss [] THEN
   METIS_TAC[]
])



val LIST_TO_SET_THM = store_thm ("LIST_TO_SET_THM",
``(LIST_TO_SET [] = EMPTY) /\
  (LIST_TO_SET (e::l) = e INSERT (LIST_TO_SET l))``,

SIMP_TAC list_ss [EXTENSION, IN_LIST_TO_SET, IN_INSERT, NOT_IN_EMPTY])


val LIST_TO_SET___APPEND = store_thm ("LIST_TO_SET___APPEND",
``!l1 l2. LIST_TO_SET (APPEND l1 l2) =
          LIST_TO_SET l1 UNION LIST_TO_SET l2``,

Induct_on `l1` THENL [
   SIMP_TAC list_ss [LIST_TO_SET_THM, UNION_EMPTY],

   ASM_SIMP_TAC list_ss [LIST_TO_SET_THM, EXTENSION, IN_UNION, IN_INSERT] THEN
   METIS_TAC[]
])


val MEM_COMPLETE_NUM_LIST___SORTED = prove (``

!l. SORTED (\n m. m <= n) l ==>

((!e. MEM e l ==> (e < LENGTH l) /\ ALL_DISTINCT l) ==>
(!e. MEM e l = (e < LENGTH l)))``,

Induct_on `l` THENL [
   SIMP_TAC list_ss [],

   REPEAT STRIP_TAC THEN
   MP_TAC (ISPECL [``\n:num m:num. m <= n``, ``l:num list``, ``h:num``] SORTED_EQ) THEN
   ASM_SIMP_TAC list_ss [transitive_def] THEN
   STRIP_TAC THEN
   FULL_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
   `!e. MEM e l ==> e < LENGTH l` by ALL_TAC THEN1 (
      REPEAT STRIP_TAC THEN
      RES_TAC THEN
      `~(e = h)` by PROVE_TAC[] THEN
      DECIDE_TAC
   ) THEN
   RES_TAC THEN
   `h = LENGTH l` by ALL_TAC THEN1 (
      CCONTR_TAC THEN
      `h < LENGTH l` by DECIDE_TAC THEN
      METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC arith_ss []
]);



val MEM_COMPLETE_NUM_LIST = store_thm("MEM_COMPLETE_NUM_LIST",
``!l.
(!e. MEM e l ==> (e < LENGTH l) /\ ALL_DISTINCT l) ==>
(!e. MEM e l = (e < LENGTH l))``,


GEN_TAC THEN
`?l'. l' = QSORT (\n m. m <= n) l` by METIS_TAC[] THEN
`PERM l l'` by ASM_REWRITE_TAC[QSORT_PERM] THEN
`SORTED (\n m. m <= n) l'` by ALL_TAC THEN1 (
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC QSORT_SORTED THEN
   SIMP_TAC arith_ss [transitive_def, total_def]
) THEN
METIS_TAC[
PERM_MEM_EQ,
PERM_LENGTH,
ALL_DISTINCT___PERM,
MEM_COMPLETE_NUM_LIST___SORTED]);


val SUBSET_DIFF = store_thm("SUBSET_DIFF",
``!s1 s2 s3.
(s1 SUBSET (s2 DIFF s3)) =
((s1 SUBSET s2) /\ (DISJOINT s1 s3))``,

SIMP_TAC std_ss [SUBSET_DEF, IN_DIFF, DISJOINT_DEF, EXTENSION, IN_INTER, NOT_IN_EMPTY] THEN
METIS_TAC[])

val IN_ABS = store_thm ("IN_ABS",

``!x P. (x IN \x. P x) = P x``,

SIMP_TAC std_ss [IN_DEF]);


val ASSOC_SYM = store_thm ("ASSOC_SYM",
``!f. ASSOC f = !x y z. f (f x y) z =f x (f y z)``,

SIMP_TAC std_ss [ASSOC_DEF] THEN
METIS_TAC[]);

val IS_SOME_EXISTS = store_thm ("IS_SOME_EXISTS",
``IS_SOME x = ?y. x = SOME y``,

Cases_on `x` THEN SIMP_TAC std_ss []);


val NOT_NONE_IS_SOME = store_thm ("NOT_NONE_IS_SOME",
``(~(x = NONE) = (IS_SOME x)) /\
   (~(NONE = x) = (IS_SOME x))``,

Cases_on `x` THEN SIMP_TAC std_ss []);

val NONE_IS_NOT_SOME = store_thm ("NONE_IS_NOT_SOME",
``((x = NONE) = ~(IS_SOME x)) /\
   ((NONE = x) = ~(IS_SOME x))``,

Cases_on `x` THEN SIMP_TAC std_ss []);



val EQ_SOME_THM = store_thm ("EQ_SOME_THM",
``((SOME x = Y) = ((x = THE Y) /\ (IS_SOME Y))) /\
   ((Y = SOME x) = ((x = THE Y) /\ (IS_SOME Y)))``,

Cases_on `Y` THEN SIMP_TAC std_ss [] THEN
METIS_TAC[]);



val LEFT_FORALL_AND_THM = store_thm ("LEFT_FORALL_AND_THM",
	``(!x. (f x /\ g)) = ((!x. f x) /\ g)``, SIMP_TAC std_ss [FORALL_AND_THM])

val RIGHT_FORALL_AND_THM = store_thm ("RIGHT_FORALL_AND_THM",
	``(!x. (f /\ g x)) = (f /\ (!x. g x))``, SIMP_TAC std_ss [FORALL_AND_THM])


val COND_EXPAND_IMP = store_thm ("COND_EXPAND_IMP",
``!b t1 t2. (if b then t1 else t2) = (b ==> t1) /\ (~b ==> t2)``,
Cases_on `b` THEN SIMP_TAC std_ss []);

val COND_EXPAND_OR = store_thm ("COND_EXPAND_OR",
``!b t1 t2. (if b then t1 else t2) = (b /\ t1) \/ (~b /\ t2)``,
Cases_on `b` THEN SIMP_TAC std_ss []);



val FILTER_EQ_APPEND = store_thm ("FILTER_EQ_APPEND",
``!P l l1 l2.
(FILTER P l = l1 ++ l2) =
?l1' l2'. (l = l1' ++ l2') /\ (FILTER P l1' = l1) /\ (FILTER P l2' = l2)``,

Induct_on `l1` THEN1 (
	SIMP_TAC list_ss [] THEN
	REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
		Q.EXISTS_TAC `[]` THEN
		Q.EXISTS_TAC `l` THEN
		ASM_SIMP_TAC list_ss [],

		ASM_SIMP_TAC list_ss [FILTER_APPEND]
	]
) THEN

Induct_on `l` THENL [
	SIMP_TAC list_ss [],

	SIMP_TAC list_ss [] THEN
	REPEAT GEN_TAC THEN
	Cases_on `P h` THENL [
		ASM_SIMP_TAC list_ss [] THEN
		EQ_TAC THENL [
			REPEAT STRIP_TAC THEN
			Q.EXISTS_TAC `h::l1'` THEN
			Q.EXISTS_TAC `l2'` THEN
			ASM_SIMP_TAC list_ss [] THEN
			METIS_TAC[],


			STRIP_TAC THEN
			Cases_on `l1'` THEN FULL_SIMP_TAC list_ss [] THEN
			Q.PAT_ASSUM `X = h'::l1` MP_TAC THEN
			ASM_SIMP_TAC list_ss [] THEN
			METIS_TAC[]
		],

		FULL_SIMP_TAC list_ss [] THEN
		EQ_TAC THEN REPEAT STRIP_TAC THENL [
			Q.EXISTS_TAC `h::l1'` THEN
			Q.EXISTS_TAC `l2'` THEN
			ASM_SIMP_TAC list_ss [],



			Cases_on `l1'` THEN FULL_SIMP_TAC list_ss [] THEN
			Q.PAT_ASSUM `X = h'::l1` MP_TAC THEN
			ASM_SIMP_TAC list_ss [] THEN
			METIS_TAC[]
		]
	]
]);


val FILTER_EQ_NIL = store_thm ("FILTER_EQ_NIL",
``!P l. (FILTER P l = []) = (EVERY (\x. ~(P x)) l)``,

Induct_on `l` THEN (
	ASM_SIMP_TAC list_ss [COND_RATOR, COND_RAND]
));



val FILTER_EQ = store_thm ("FILTER_EQ",
``!P l h l'.
(FILTER P l = h::l') =
(?l1' l2'. (l = l1'++[h]++l2') /\ (FILTER P l1' = []) /\ (FILTER P l2' = l') /\ (P h))``,

Induct_on `l` THEN (
	SIMP_TAC list_ss []
) THEN
REPEAT STRIP_TAC THEN
Cases_on `P h` THENL [
	ASM_SIMP_TAC list_ss [] THEN
	EQ_TAC THENL [
		STRIP_TAC THEN
		Q.EXISTS_TAC `[]` THEN
		Q.EXISTS_TAC `l` THEN
		ASM_SIMP_TAC list_ss [] THEN
		METIS_TAC[],

		STRIP_TAC THEN
		Cases_on `l1'` THENL [
			FULL_SIMP_TAC list_ss [],
			FULL_SIMP_TAC list_ss [COND_RATOR, COND_RAND]
		]
	],


	ASM_SIMP_TAC std_ss [] THEN
	EQ_TAC THENL [
		STRIP_TAC THEN
		Q.EXISTS_TAC `h::l1'` THEN
		Q.EXISTS_TAC `l2'` THEN
		ASM_SIMP_TAC list_ss [],

		STRIP_TAC THEN
		Cases_on `l1'` THEN (
			FULL_SIMP_TAC list_ss []
		) THEN
		Q.EXISTS_TAC `t` THEN
		Q.EXISTS_TAC `l2'` THEN
		ASM_SIMP_TAC std_ss [] THEN
		METIS_TAC[]
	]
]);




val FILTER_EQ_SING = store_thm ("FILTER_EQ_SING",
``!P l h.
(FILTER P l = [h]) =
(?l1' l2'. (l = l1'++[h]++l2') /\ (FILTER P l1' = []) /\ (FILTER P l2' = []) /\ (P h))``,

SIMP_TAC list_ss [FILTER_EQ]);




val EVERY_FILTER = store_thm ("EVERY_FILTER",
``!P1 P2 l.
EVERY P1 (FILTER P2 l) =
EVERY (\x. P2 x ==> P1 x) l``,

Induct_on `l` THENL [
	SIMP_TAC list_ss [],

	SIMP_TAC list_ss [] THEN
	REPEAT STRIP_TAC THEN
	Cases_on `P2 h` THEN (
		ASM_SIMP_TAC list_ss []
	)
]);
		

val MONO_NOT_EQ = store_thm ("MONO_NOT_EQ",
``(~A ==> ~B) = (B ==> A)``, 
METIS_TAC[]);


val MEMBER_NOT_NIL = store_thm ("MEMBER_NOT_NIL",
	``!l. (?e. MEM e l) = ~(l = [])``,

Cases_on `l` THEN
SIMP_TAC list_ss [EXISTS_OR_THM]);



val IMAGE_ABS2 = store_thm ("IMAGE_ABS2",
``IMAGE f P = (\x. ?y. (x = f y) /\ y IN P)``,
SIMP_TAC std_ss [EXTENSION, IN_IMAGE, IN_ABS]);

val IMAGE_ABS = store_thm ("IMAGE_ABS",
``IMAGE f (\x. P x) = (\x. ?y. (x = f y) /\ P y)``,
SIMP_TAC std_ss [IMAGE_ABS2, IN_ABS]);




val LIST_ELEM_COUNT_def = 
save_thm ("LIST_ELEM_COUNT_def",
LIST_ELEM_COUNT_DEF);



val LIST_ELEM_COUNT_THM = store_thm ("LIST_ELEM_COUNT_THM",

	``(!e. LIST_ELEM_COUNT e [] = 0) /\
	   (!e l1 l2. LIST_ELEM_COUNT e (l1++l2) = LIST_ELEM_COUNT e l1 + LIST_ELEM_COUNT e l2) /\
	   (!e h l. (h = e) ==> (LIST_ELEM_COUNT e (h::l) = SUC (LIST_ELEM_COUNT e l))) /\
	   (!e h l. ~(h = e) ==> (LIST_ELEM_COUNT e (h::l) = LIST_ELEM_COUNT e l))``,


SIMP_TAC list_ss [LIST_ELEM_COUNT_def, FILTER_APPEND]);




val LIST_ELEM_COUNT___MEM = store_thm ("LIST_ELEM_COUNT___MEM",

``(LIST_ELEM_COUNT e l > 0) = (MEM e l)``,

	Induct_on `l` THENL [
		SIMP_TAC list_ss [LIST_ELEM_COUNT_THM],

		FULL_SIMP_TAC list_ss [LIST_ELEM_COUNT_def] THEN
		GEN_TAC THEN
		Cases_on `h = e` THEN (
			ASM_SIMP_TAC list_ss []
		)
	]
);


val FILTER_COND_REWRITE = store_thm ("FILTER_COND_REWRITE",
	``(FILTER P [] = []) /\
	   (!h. (P h) ==> ((FILTER P (h::l) = h::FILTER P l))) /\
	   (!h. ~(P h) ==> (FILTER P (h::l) = FILTER P l))``,

SIMP_TAC list_ss []);


val IN_ABS2 = store_thm ("IN_ABS2",
	``(!t. (t IN X = Q t)) = (X = \t. Q t)``,
SIMP_TAC std_ss [EXTENSION, IN_ABS]);


val IN_ABS3 = store_thm ("IN_ABS3",
	``(\t. (t IN X)) = X``,
SIMP_TAC std_ss [EXTENSION, IN_ABS]);


val IN_ABS_SING = store_thm ("IN_ABS_SING",
	``(\t. (t = X)) = {X}``,
SIMP_TAC std_ss [EXTENSION, IN_ABS, IN_SING]);


val IMAGE_BIGUNION = store_thm ("IMAGE_BIGUNION",
	``IMAGE f (BIGUNION M) = 
	    BIGUNION (IMAGE (IMAGE f) M)``,

ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE,
	GSYM LEFT_EXISTS_AND_THM,
	GSYM RIGHT_EXISTS_AND_THM] THEN
METIS_TAC[]);



val COND_NONE_SOME_REWRITES = store_thm ("COND_NONE_SOME_REWRITES",

``(((if C then NONE else (SOME X)) = (SOME Y)) = (~C /\ (X = Y))) /\
   (((if C then (SOME X) else NONE) = (SOME Y)) = (C /\ (X = Y))) /\
   (((if C then NONE else (SOME X)) = NONE) = C) /\
   (((if C then (SOME X) else NONE) = NONE) = ~C) /\
   ((if C1 then NONE else (if C2 then NONE else Z)) =
    (if C1 \/ C2 then NONE else Z)) /\
   ((if C1 then NONE else (if C2 then Z else NONE)) =
    (if C1 \/ ~C2 then NONE else Z)) /\
   ((if C1 then (if C2 then NONE else Z) else NONE) =
    (if ~C1 \/ C2 then NONE else Z)) /\
   ((if C1 then (if C2 then Z else NONE) else NONE) =
    (if C1 /\ C2 then Z else NONE)) /\
    (IS_SOME (if C then NONE else (SOME X)) = ~C) /\
    (IS_SOME (if C then (SOME X) else NONE) = C) /\
    (IS_NONE (if C then NONE else (SOME X)) = C) /\
    (IS_NONE (if C then (SOME X) else NONE) = ~C) /\
   ((if C then SOME X else SOME Y) = 
    SOME (if C then X else Y))
``,

Cases_on `C` THEN Cases_on `C1` THEN Cases_on `C2` THEN 
SIMP_TAC std_ss []);



val COND_NONE_SOME_REWRITES2 = store_thm ("COND_NONE_SOME_REWRITES2",

``(((if C then NONE else X) = (SOME Y)) = (~C /\ (X = SOME Y))) /\
   (((if C then X else NONE) = (SOME Y)) = (C /\ (X = SOME Y))) /\
   (((if C then NONE else X) = NONE) = C \/ (X = NONE)) /\
   (((if C then X else NONE) = NONE) = ~C \/ (X = NONE))``,

Cases_on `C` THEN Cases_on `X` THEN 
SIMP_TAC std_ss []);




val COND_REWRITES = store_thm ("COND_REWRITES",
``
   (FST (if C then X else Y) =
    if C then FST X else FST Y) /\

   (SND (if C then X else Y) =
    if C then SND X else SND Y) /\

   ((IS_SOME (if C then X' else Y')) =
     if C then (IS_SOME X') else (IS_SOME Y')) /\

   ((IS_NONE (if C then X' else Y')) =
     if C then (IS_NONE X') else (IS_NONE Y')) /\

   (((if C then v1 else v2) = v1) =
    (~C ==> (v2 = v1))) /\

   (((if C then v2 else v1) = v1) =
    (C ==> (v2 = v1)))
``,

Cases_on `C` THEN 
SIMP_TAC std_ss []);



val COND_EQ_REWRITE = store_thm ("COND_EQ_REWRITE",
``
   ((if C then X else Y) = (if C then X' else Y')) =
   ((C ==> (X = X')) /\ (~C ==> (Y = Y')))``,

Cases_on `C` THEN 
SIMP_TAC std_ss []);


val PAIR_EQ_REWRITES = store_thm ("PAIR_EQ_REWRITES",

``(((y1, y2) = x) = (y1 = FST x) /\ (y2 = SND x))``,

Cases_on `x` THEN SIMP_TAC std_ss []);



val COND_NONE_SOME_REWRITES_EQ = store_thm ("COND_NONE_SOME_REWRITES_EQ",
``
   (((if C1 then NONE else (SOME X)) =
    (if C2 then (SOME Y) else NONE)) = ((~C1 = C2) /\ (C2 ==> (X = Y)))) /\

   (((if C1 then (SOME X) else NONE) =
    (if C2 then (SOME Y) else NONE)) = ((C1 = C2) /\ (C2 ==> (X = Y)))) /\


   (((if C1 then NONE else (SOME X)) =
    (if C2 then NONE else (SOME Y))) = ((C1 = C2) /\ (~C2 ==> (X = Y)))) /\

   (((if C1 then (SOME X) else NONE) =
    (if C2 then NONE else (SOME Y))) = ((C1 = ~C2) /\ (~C2 ==> (X = Y))))``,

Cases_on `C1` THEN Cases_on `C2` THEN 
SIMP_TAC std_ss []);




val DRESTRICT_FUNION_DRESTRICT_COMPL = store_thm (
"DRESTRICT_FUNION_DRESTRICT_COMPL",
``FUNION (DRESTRICT f s) (DRESTRICT f (COMPL s)) = f ``,

SIMP_TAC std_ss [GSYM fmap_EQ_THM, FUNION_DEF, DRESTRICT_DEF,
   EXTENSION, IN_INTER, IN_UNION, IN_COMPL] THEN
METIS_TAC[]);





val DRESTRICT_IDEMPOT = store_thm ("DRESTRICT_IDEMPOT",
``!s vs. DRESTRICT (DRESTRICT s vs) vs = (DRESTRICT s vs)``,

SIMP_TAC std_ss [DRESTRICT_DRESTRICT, INTER_IDEMPOT]);




val LENGTH_EQ_NUM = store_thm ("LENGTH_EQ_NUM",
``	(!l:'a list. (LENGTH l = 0) = (l = [])) /\
	(!l:'a list n. (LENGTH l = (SUC n)) = (?h l'. (LENGTH l' = n) /\ (l = h::l'))) /\
	(!l:'a list n1 n2. (LENGTH l = n1+n2) = (?l1 l2. (LENGTH l1 = n1) /\ (LENGTH l2 = n2) /\ (l = l1++l2)))``,

MATCH_MP_TAC (prove (``(A /\ B /\ (A /\ B ==> C)) ==> (A /\ B /\ C)``, METIS_TAC[])) THEN
REPEAT CONJ_TAC THENL [
	REWRITE_TAC [LENGTH_NIL],

	Induct_on `n` THEN (
		Cases_on `l` THEN SIMP_TAC list_ss []
	),

	REPEAT DISCH_TAC THEN
	FULL_SIMP_TAC std_ss [] THEN
	Induct_on `n1` THENL [
		ASM_SIMP_TAC list_ss [],

		ASM_SIMP_TAC list_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
			ADD_CLAUSES] THEN
		METIS_TAC[]
	]
]);

val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;

val LENGTH_EQ_NUM_EVAL = save_thm ("LENGTH_EQ_NUM_EVAL",
	SUC_RULE LENGTH_EQ_NUM);



val PSUBSET_SING = store_thm ("PSUBSET_SING",
``!s x. x PSUBSET {s} = (x = EMPTY)``,

SIMP_TAC std_ss [PSUBSET_DEF, SUBSET_DEF, EXTENSION,
		 IN_SING, NOT_IN_EMPTY] THEN
METIS_TAC[]);



val INTER_SUBSET = store_thm ("INTER_SUBSET",

``((A INTER B = A) = (A SUBSET B)) /\
  ((A INTER B = B) = (B SUBSET A))``,

SIMP_TAC std_ss [EXTENSION, IN_INTER, SUBSET_DEF] THEN
METIS_TAC[]);


val INTER_UNION = store_thm ("INTER_UNION",
``((A UNION B) INTER A = A) /\
  ((B UNION A) INTER A = A) /\
  (A INTER (A UNION B) = A) /\
  (A INTER (B UNION A) = A)``,

SIMP_TAC std_ss [INTER_SUBSET, SUBSET_UNION]);



val BAG_ALL_DISTINCT_def = 
save_thm ("BAG_ALL_DISTINCT_def",
bagTheory.BAG_ALL_DISTINCT);


val BAG_ALL_DISTINCT_THM = store_thm ("BAG_ALL_DISTINCT_THM",
``BAG_ALL_DISTINCT EMPTY_BAG /\
  (BAG_ALL_DISTINCT (BAG_INSERT e b) =
   ~(BAG_IN e b) /\ BAG_ALL_DISTINCT b)``,

SIMP_TAC arith_ss [BAG_ALL_DISTINCT_def, bagTheory.EMPTY_BAG,
		 bagTheory.BAG_IN, bagTheory.BAG_INN,
		 bagTheory.BAG_INSERT, COND_RAND, COND_RATOR,
		 COND_EXPAND_IMP, FORALL_AND_THM] THEN
`(b e + 1 <= 1) = (b e = 0)` by DECIDE_TAC THEN
`~(b e >= 1) = (b e = 0)` by DECIDE_TAC THEN
`0:num <= 1` by DECIDE_TAC THEN
METIS_TAC[]);



val FINITE_INTER = store_thm ("FINITE_INTER",
``((FINITE s1) \/ (FINITE s2)) ==>
  FINITE (s1 INTER s2)``,

`((s1 INTER s2) SUBSET s1) /\ ((s1 INTER s2) SUBSET s2)` by ALL_TAC THEN1 (
   SIMP_TAC std_ss [SUBSET_DEF, IN_INTER]
) THEN
METIS_TAC[SUBSET_FINITE]);


val LIST_UNROLL_GIVEN_ELEMENT_NAMES_def = Define `
    LIST_UNROLL_GIVEN_ELEMENT_NAMES l1 (l2:string list) =
    (LENGTH l1 = LENGTH l2)
`;


val LIST_UNROLL_GIVEN_ELEMENT_NAMES_REWRITE = store_thm ("LIST_UNROLL_GIVEN_ELEMENT_NAMES_REWRITE",
``(LIST_UNROLL_GIVEN_ELEMENT_NAMES [] []) /\
  (LIST_UNROLL_GIVEN_ELEMENT_NAMES (x::xs) (y::ys) =
   LIST_UNROLL_GIVEN_ELEMENT_NAMES xs ys) /\
  ~(LIST_UNROLL_GIVEN_ELEMENT_NAMES [] (y::ys)) /\
  ~(LIST_UNROLL_GIVEN_ELEMENT_NAMES (x::xs) [])``,

SIMP_TAC list_ss [LIST_UNROLL_GIVEN_ELEMENT_NAMES_def]);




val LIST_UNROLL_GIVEN_ELEMENT_NAMES___UNROLL = store_thm ("LIST_UNROLL_GIVEN_ELEMENT_NAMES___UNROLL",
``(LIST_UNROLL_GIVEN_ELEMENT_NAMES x [] = (x = [])) /\
  (LIST_UNROLL_GIVEN_ELEMENT_NAMES x (h::L) = 
   ?h' L'. (x = h'::L') /\ (LIST_UNROLL_GIVEN_ELEMENT_NAMES L' L))``,

Cases_on `x` THEN
SIMP_TAC list_ss [LIST_UNROLL_GIVEN_ELEMENT_NAMES_def]);



val LIST_UNROLL_GIVEN_ELEMENT_NAMES___MAP = store_thm("LIST_UNROLL_GIVEN_ELEMENT_NAMES___MAP",
``LIST_UNROLL_GIVEN_ELEMENT_NAMES (MAP f L) L' =
  LIST_UNROLL_GIVEN_ELEMENT_NAMES L L'``,

SIMP_TAC list_ss [LIST_UNROLL_GIVEN_ELEMENT_NAMES_def]);


val SOME_THE_EQ = store_thm ("SOME_THE_EQ",
``(X = SOME (THE X)) = (IS_SOME X)``, Cases_on `X` THEN SIMP_TAC std_ss []);






val LIST_EQ_REWRITE = store_thm ("LIST_EQ_REWRITE",
``!l1 l2.
  (l1 = l2) = 
  ((LENGTH l1 = LENGTH l2) /\
   ((!n. (n < LENGTH l1) ==> (EL n l1 = EL n l2))))``,

Induct_on `l1` THENL [
  Cases_on `l2` THEN SIMP_TAC list_ss [],

  Cases_on `l2` THEN SIMP_TAC list_ss [] THEN
  GEN_TAC THEN
  Cases_on `h = h'` THENL [
     ASM_SIMP_TAC std_ss [] THEN
     EQ_TAC THEN REPEAT STRIP_TAC THENL [
        ASM_REWRITE_TAC[],

	Cases_on `n` THENL [
           ASM_SIMP_TAC list_ss [],
	   FULL_SIMP_TAC list_ss []
        ],

	ASM_REWRITE_TAC[],

	Q.PAT_ASSUM `!n. X n` (MP_TAC o Q.SPEC `SUC n`) THEN
	ASM_SIMP_TAC list_ss []
     ],

     ASM_SIMP_TAC std_ss [] THEN
     DISJ2_TAC THEN
     Q.EXISTS_TAC `0` THEN
     ASM_SIMP_TAC list_ss []
  ]
]);
  

















val BAG_DISJOINT___BAG_IN =
store_thm ("BAG_DISJOINT___BAG_IN",
``!b1 b2.
  BAG_DISJOINT b1 b2 =
  !e. ~(BAG_IN e b1) \/ ~(BAG_IN e b2)``,

SIMP_TAC std_ss [bagTheory.BAG_DISJOINT,
		 DISJOINT_DEF,
		 EXTENSION, NOT_IN_EMPTY,
		 IN_INTER,
		 bagTheory.IN_SET_OF_BAG]);



val BAG_ALL_DISTINCT___BAG_MERGE =
store_thm ("BAG_ALL_DISTINCT___BAG_MERGE",
``
!b1 b2. BAG_ALL_DISTINCT (BAG_MERGE b1 b2) =
        (BAG_ALL_DISTINCT b1 /\
        BAG_ALL_DISTINCT b2)``,

SIMP_TAC std_ss [BAG_ALL_DISTINCT_def,
		 bagTheory.BAG_MERGE,
		 GSYM FORALL_AND_THM] THEN
REPEAT GEN_TAC THEN
HO_MATCH_MP_TAC (prove (``(!e. (X e = Y e)) ==>
			  ((!e. X e) = (!e. Y e))``, 
                        PROVE_TAC[])) THEN
GEN_TAC THEN
DECIDE_TAC);



val BAG_DISJOINT___BAG_INSERT =
store_thm ("BAG_DISJOINT___BAG_INSERT",
``!b1 b2 e1.
  BAG_DISJOINT (BAG_INSERT e1 b1) b2 =
  (~(BAG_IN e1 b2) /\ (BAG_DISJOINT b1 b2))``,


SIMP_TAC std_ss [BAG_DISJOINT___BAG_IN,
		 bagTheory.BAG_IN_BAG_INSERT] THEN
METIS_TAC[]);




val BAG_ALL_DISTINCT___BAG_UNION =
store_thm ("BAG_ALL_DISTINCT___BAG_UNION",
``
!b1 b2. BAG_ALL_DISTINCT (BAG_UNION b1 b2) =
        (BAG_ALL_DISTINCT b1 /\
         BAG_ALL_DISTINCT b2 /\
         BAG_DISJOINT b1 b2)``,

SIMP_TAC std_ss [BAG_ALL_DISTINCT_def,
		 bagTheory.BAG_UNION,
		 bagTheory.BAG_DISJOINT,
		 DISJOINT_DEF, EXTENSION,
		 NOT_IN_EMPTY, IN_INTER,
		 bagTheory.IN_SET_OF_BAG,
		 bagTheory.BAG_IN,
     		 bagTheory.BAG_INN,
		 GSYM FORALL_AND_THM] THEN
REPEAT GEN_TAC THEN
HO_MATCH_MP_TAC (prove (``(!e. (X e = Y e)) ==>
			  ((!e. X e) = (!e. Y e))``, 
                        PROVE_TAC[])) THEN
GEN_TAC THEN
DECIDE_TAC);



val BAG_IN_BAG_MERGE = 
store_thm ("BAG_IN_BAG_MERGE",

``!e b1 b2. (BAG_IN e (BAG_MERGE b1 b2)) =
            (BAG_IN e b1 \/ BAG_IN e b2)``,

SIMP_TAC std_ss [bagTheory.BAG_MERGE,
	     bagTheory.BAG_INN,
	     bagTheory.BAG_IN] THEN
REPEAT GEN_TAC THEN
DECIDE_TAC);

val SET_OF_BAG_MERGE = store_thm ("SET_OF_BAG_MERGE",
``!b1 b2. SET_OF_BAG (BAG_MERGE b1 b2) =
          SET_OF_BAG b1 UNION SET_OF_BAG b2``,

ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [bagTheory.IN_SET_OF_BAG, IN_UNION,
		 BAG_IN_BAG_MERGE]);


val UNION_DELETE = store_thm ("UNION_DELETE",
``(A UNION B) DELETE x =
  ((A DELETE x) UNION (B DELETE x))``,

SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_DELETE] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
ASM_SIMP_TAC std_ss [])




val FINITE_BAG_INDUCT___FINITE = store_thm ("FINITE_BAG_INDUCT___FINITE",
``
 !P. P {| |} /\ (!b. (P b /\ FINITE_BAG b) ==> !e. P (BAG_INSERT e b)) ==>
 !b. FINITE_BAG b ==> P b``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPEC `\b. P b /\ FINITE_BAG b` bagTheory.FINITE_BAG_INDUCT) THEN
ASM_SIMP_TAC std_ss [bagTheory.FINITE_BAG_THM])








val FMAP_MAP_def = Define 
`FMAP_MAP f m = FUN_FMAP (\x. f (m ' x)) (FDOM m)`;


val FMAP_MAP_THM = store_thm ("FMAP_MAP_THM",
``(FDOM (FMAP_MAP f m) = FDOM m) /\
  (!x. x IN FDOM m ==> ((FMAP_MAP f m) ' x = f (m ' x)))``,

SIMP_TAC std_ss [FMAP_MAP_def,
		 FUN_FMAP_DEF, FDOM_FINITE]);


 
val FMAP_MAP_FEMPTY = store_thm ("FMAP_MAP_FEMPTY",
``FMAP_MAP f FEMPTY = FEMPTY``,

SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMAP_MAP_THM,
		 FDOM_FEMPTY, NOT_IN_EMPTY]);


val FMAP_MAP_FUPDATE = store_thm ("FMAP_MAP_FUPDATE",
``FMAP_MAP f (m |+ (x, v)) = 
  (FMAP_MAP f m) |+ (x, f v)``,

SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMAP_MAP_THM,
		 FDOM_FUPDATE, IN_INSERT,
		 FAPPLY_FUPDATE_THM,
		 COND_RAND, COND_RATOR,
		 DISJ_IMP_THM]);



val FEVERY_FMAP_MAP = store_thm ("FEVERY_FMAP_MAP",
``!m P f.
  FEVERY P (FMAP_MAP f m) = 
  FEVERY (\x. P (FST x, (f (SND x)))) m``,

SIMP_TAC std_ss [FEVERY_DEF,
		 FDOM_FEMPTY,
		 NOT_IN_EMPTY,
		 FMAP_MAP_THM]);




val FMAP_MAP___FMAP_MAP = store_thm ("FMAP_MAP___FMAP_MAP",
``!f1 f2 f.
  FMAP_MAP f1 (FMAP_MAP f2 f) = 
  FMAP_MAP (f1 o f2) f``,

SIMP_TAC std_ss [GSYM fmap_EQ_THM,
		 FMAP_MAP_THM]);


val FMAP_MAP2_def = save_thm(
"FMAP_MAP2_def",
FMAP_MAP2_def);



val FMAP_MAP2_THM = store_thm ("FMAP_MAP2_THM",
``(FDOM (FMAP_MAP2 f m) = FDOM m) /\
  (!x. x IN FDOM m ==> ((FMAP_MAP2 f m) ' x = f (x,m ' x)))``,

SIMP_TAC std_ss [FMAP_MAP2_def,
		 FUN_FMAP_DEF, FDOM_FINITE]);


 
val FMAP_MAP2_FEMPTY = store_thm ("FMAP_MAP2_FEMPTY",
``FMAP_MAP2 f FEMPTY = FEMPTY``,

SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMAP_MAP2_THM,
		 FDOM_FEMPTY, NOT_IN_EMPTY]);


val FMAP_MAP2_FUPDATE = store_thm ("FMAP_MAP2_FUPDATE",
``FMAP_MAP2 f (m |+ (x, v)) = 
  (FMAP_MAP2 f m) |+ (x, f (x,v))``,

SIMP_TAC std_ss [GSYM fmap_EQ_THM, FMAP_MAP2_THM,
		 FDOM_FUPDATE, IN_INSERT,
		 FAPPLY_FUPDATE_THM,
		 COND_RAND, COND_RATOR,
		 DISJ_IMP_THM]);




val FEVERY_STRENGTHEN_THM =
store_thm ("FEVERY_STRENGTHEN_THM",
``FEVERY P FEMPTY /\
         ((FEVERY P f /\ P (x,y)) ==>
          FEVERY P (f |+ (x,y)))``,

SIMP_TAC std_ss [FEVERY_DEF, FDOM_FEMPTY,
		 NOT_IN_EMPTY, FAPPLY_FUPDATE_THM,
		 FDOM_FUPDATE, IN_INSERT] THEN
METIS_TAC[]);




val DELETE_SUBSET_INSERT = store_thm ("DELETE_SUBSET_INSERT",
``s DELETE e SUBSET s2 =
  s SUBSET e INSERT s2``,

SIMP_TAC std_ss [SUBSET_DEF, IN_DELETE, IN_INSERT] THEN
METIS_TAC[]);



val INTER_ABS = store_thm ("INTER_ABS",
``$INTER = \a b x. x IN a /\ x IN b``,

ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC std_ss [EXTENSION, IN_INTER] THEN
SIMP_TAC std_ss [IN_DEF]);


val IMAGE_ABS = store_thm ("IMAGE_ABS",
``IMAGE f X = \x. (?e. (x = f e) /\ e IN X)``,

SIMP_TAC std_ss [EXTENSION, IN_IMAGE] THEN
SIMP_TAC std_ss [IN_DEF]);


val BIGINTER_ABS = store_thm ("BIGINTER_ABS",
``BIGINTER P = \x. !s. s IN P ==> x IN s``,

SIMP_TAC std_ss [EXTENSION, IN_BIGINTER] THEN
SIMP_TAC std_ss [IN_DEF]);



val BAG_IN___BAG_DIFF___ALL_DISTINCT = store_thm ("BAG_IN___BAG_DIFF___ALL_DISTINCT",
``
!b1 b2 e.
BAG_ALL_DISTINCT b1 ==>
(BAG_IN e (BAG_DIFF b1 b2) =
BAG_IN e b1 /\ ~BAG_IN e b2)``,

SIMP_TAC arith_ss [BAG_ALL_DISTINCT_def,
		 bagTheory.BAG_IN,
 		 bagTheory.BAG_INN,
  		 bagTheory.BAG_DIFF] THEN
REPEAT STRIP_TAC THEN
`b1 e <= 1` by PROVE_TAC[] THEN
Cases_on `b1 e >= 1` THEN (
   ASM_SIMP_TAC arith_ss []
));



val SET_OF_BAG_EMPTY = store_thm ("SET_OF_BAG_EMPTY",
``SET_OF_BAG EMPTY_BAG = EMPTY``,
REWRITE_TAC[bagTheory.SET_OF_BAG_EQ_EMPTY]);


val BAG_EVERY_def = save_thm("BAG_EVERY_def",
BAG_EVERY);


val BAG_EVERY_THM = store_thm ("BAG_EVERY_THM",
``(BAG_EVERY P EMPTY_BAG) /\
  (BAG_EVERY P (BAG_INSERT e b) = P e /\ BAG_EVERY P b)``,

SIMP_TAC std_ss [BAG_EVERY_def, bagTheory.BAG_IN_BAG_INSERT,
		 DISJ_IMP_THM, FORALL_AND_THM,
		 bagTheory.NOT_IN_EMPTY_BAG]);



val BAG_ALL_DISTINCT___DIFF = store_thm ("BAG_ALL_DISTINCT___DIFF",

``!b1 b2. BAG_ALL_DISTINCT b1 ==>
  BAG_ALL_DISTINCT (BAG_DIFF b1 b2)``,

SIMP_TAC std_ss [BAG_ALL_DISTINCT_def,
		 bagTheory.BAG_DIFF] THEN
REPEAT STRIP_TAC THEN
`b1 e <= 1` by PROVE_TAC[] THEN
DECIDE_TAC);

val IN_THE_COND_REWRITE = store_thm ("IN_THE_COND_REWRITE",
``x IN THE (if c then X else Y) =
	       (c ==> x IN THE X) /\ (~c ==> x IN THE Y)``,
Cases_on `c` THEN SIMP_TAC std_ss []);



val GSYM_LENGTH_NIL = store_thm ("GSYM_LENGTH_NIL", 
``(0 = LENGTH l) = (l = [])``,
Cases_on `l` THEN SIMP_TAC list_ss []);



val FUPDATE_ELIM = store_thm ("FUPDATE_ELIM",
``!k v f.
  ((k IN FDOM f) /\ (f ' k = v)) ==>
  (f |+ (k,v) = f)``,

REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC[GSYM fmap_EQ_THM] THEN
SIMP_TAC std_ss [FDOM_FUPDATE, IN_INSERT, EXTENSION,
		 FAPPLY_FUPDATE_THM] THEN
METIS_TAC[]);






val FEVERY_DRESTRICT_COMPL = store_thm(
"FEVERY_DRESTRICT_COMPL",
``FEVERY P (DRESTRICT (f |+ (k, v)) (COMPL s)) = 
  (FEVERY P (DRESTRICT f (COMPL (k INSERT s))) /\
  (~(k IN s) ==> P (k,v)))``,

SIMP_TAC std_ss [FEVERY_DEF, IN_INTER,
		 FDOM_DRESTRICT,
                 DRESTRICT_DEF, FAPPLY_FUPDATE_THM,
                 FDOM_FUPDATE, IN_INSERT,
		 RIGHT_AND_OVER_OR, IN_COMPL,
                 DISJ_IMP_THM, FORALL_AND_THM] THEN
METIS_TAC[]);




val BAG_OF_FMAP_def = 
save_thm ("BAG_OF_FMAP_def",
BAG_OF_FMAP_def);


val BAG_OF_FMAP_THM = store_thm ("BAG_OF_FMAP_THM",
``(BAG_OF_FMAP f FEMPTY = EMPTY_BAG) /\
  (BAG_OF_FMAP f (b |+ (k, v)) =
  BAG_INSERT (f k v) (BAG_OF_FMAP f (b \\ k)))
``,

SIMP_TAC std_ss [BAG_OF_FMAP_def,
		 FDOM_FEMPTY, NOT_IN_EMPTY, bagTheory.EMPTY_BAG,
		 combinTheory.K_DEF,
		 bagTheory.BAG_INSERT, FDOM_FUPDATE, IN_INSERT,
		 GSYM EMPTY_DEF, CARD_EMPTY] THEN
ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
GEN_TAC THEN SIMP_TAC std_ss [] THEN
Cases_on `x = f k v` THENL [  
   ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [FAPPLY_FUPDATE_THM,
		        FDOM_DOMSUB, IN_DELETE,
			DOMSUB_FAPPLY_THM] THEN
   Q.ABBREV_TAC `ks =  (\k'. (k' IN FDOM b /\ ~(k' = k)) /\ (f k v = f k' (b ' k')))` THEN
   `FINITE ks` by ALL_TAC THEN1 (
      Tactical.REVERSE (`ks = ks INTER FDOM b` by ALL_TAC) THEN1 (
         ONCE_ASM_REWRITE_TAC[] THEN
         MATCH_MP_TAC FINITE_INTER THEN
	 REWRITE_TAC[FDOM_FINITE]
      ) THEN
      Q.UNABBREV_TAC `ks` THEN
      SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_ABS] THEN
      PROVE_TAC[]
   ) THEN
   `(\k'.
         ((k' = k) \/ k' IN FDOM b) /\
         (f k v = f k' ((if k' = k then v else b ' k')))) =
    k INSERT ks` by ALL_TAC THEN1 (
     Q.UNABBREV_TAC `ks` THEN
     SIMP_TAC std_ss [EXTENSION, IN_INSERT, IN_ABS] THEN
     GEN_TAC THEN
     Cases_on `x' = k` THEN ASM_REWRITE_TAC[]
   ) THEN
   ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

   `~(k IN ks)` by ALL_TAC THEN1 (
      Q.UNABBREV_TAC `ks` THEN
      SIMP_TAC std_ss [IN_ABS]
   ) THEN
   ASM_SIMP_TAC arith_ss [CARD_INSERT],



   FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [FAPPLY_FUPDATE_THM,
		        FDOM_DOMSUB, IN_DELETE,
			DOMSUB_FAPPLY_THM] THEN
   AP_TERM_TAC THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN SIMP_TAC std_ss [] THEN
   Cases_on `x' = k` THEN (
      ASM_SIMP_TAC std_ss []
   )
]);


val BAG_IN___BAG_OF_FMAP = store_thm ("BAG_IN___BAG_OF_FMAP",
``BAG_IN x (BAG_OF_FMAP f b) =
  ?k. k IN FDOM b /\ (x = f k (b ' k))``,

SIMP_TAC std_ss [BAG_OF_FMAP_def,
		 bagTheory.BAG_IN,
 		 bagTheory.BAG_INN] THEN
`!X. (X >= (1:num)) = ~(X = 0)` by DECIDE_TAC THEN
ONCE_ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
`FINITE (\k. k IN FDOM b /\ (x = f k (b ' k)))` by ALL_TAC THEN1 (
   `(\k. k IN FDOM b /\ (x = f k (b ' k))) =
    (\k. k IN FDOM b /\ (x = f k (b ' k))) INTER (FDOM b)` by ALL_TAC THEN1 (
      SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_ABS] THEN
      METIS_TAC[]
   ) THEN
   ONCE_ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC FINITE_INTER THEN
   REWRITE_TAC[FDOM_FINITE]
) THEN
ASM_SIMP_TAC std_ss [CARD_EQ_0] THEN

SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_ABS]);




val FINITE___BAG_OF_FMAP = store_thm ("FINITE___BAG_OF_FMAP",
``!f b. FINITE_BAG (BAG_OF_FMAP f b)``,

REWRITE_TAC[GSYM bagTheory.FINITE_SET_OF_BAG,
	    bagTheory.SET_OF_BAG, BAG_IN___BAG_OF_FMAP] THEN
REPEAT GEN_TAC THEN
`(\x. ?k. k IN FDOM b /\ (x = f k (b ' k))) =
 IMAGE (\k. f k (b ' k)) (FDOM b)` by ALL_TAC THEN1 (
   SIMP_TAC std_ss [EXTENSION, IN_IMAGE, IN_ABS] THEN
   PROVE_TAC[]
) THEN
ONCE_ASM_REWRITE_TAC[] THEN 
MATCH_MP_TAC IMAGE_FINITE THEN
REWRITE_TAC[FDOM_FINITE]);



val IN_INSERT_EXPAND = store_thm ("IN_INSERT_EXPAND",
``x IN y INSERT P =
  (x = y) \/ (~(x = y) /\ x IN P)``,

SIMP_TAC std_ss [IN_INSERT] THEN
METIS_TAC[]);


val LIST_NOT_NIL___HD_EXISTS = store_thm ("LIST_NOT_NIL___HD_EXISTS",
``!l. ~(l = []) = ?e l'. l = e::l'``,
GEN_TAC THEN
Cases_on `l` THEN
SIMP_TAC list_ss []);


val APPEND_ASSOC_CONS = store_thm (
"APPEND_ASSOC_CONS",
``!l1 h l2 l3. 
  (l1 ++ (h::l2) ++ l3 =
   l1 ++ h::(l2++l3))``,

   REWRITE_TAC[GSYM rich_listTheory.APPEND_ASSOC, 
	       rich_listTheory.APPEND]);


val _ = export_theory();


