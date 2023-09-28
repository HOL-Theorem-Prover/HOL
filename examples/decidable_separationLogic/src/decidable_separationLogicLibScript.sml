open HolKernel Parse boolLib bossLib;

(*
quietdec := true;
loadPath :=
            (concat [Globals.HOLDIR, "/examples/decidable_separationLogic/src"]) ::
            !loadPath;

map load ["finite_mapTheory", "relationTheory", "congLib", "sortingTheory",
   "rich_listTheory", "decidable_separationLogicTheory", "listLib", "stringTheory", "pred_setLib"];
show_assums := true;
*)

open finite_mapTheory relationTheory pred_setTheory congLib sortingTheory
   listTheory rich_listTheory decidable_separationLogicTheory listLib stringTheory;


(*
quietdec := false;
*)

val _ = new_theory "decidable_separationLogicLib";
val _ = ParseExtras.temp_loose_equality()

val nchotomy_thm = prove (``!x.
      (x = sf_emp) \/ (?d l. x = sf_points_to d l) \/
      (?l d d0. x = sf_tree l d d0) \/ ?d d0. x = sf_star d d0``,
                        REWRITE_TAC [TypeBase.nchotomy_of ``:('a,'b,'c) ds_spatial_formula``]);

val _ = TypeBase.write [TypeBasePure.put_nchotomy nchotomy_thm (valOf (TypeBase.fetch ``:('a,'b,'c) ds_spatial_formula``))];



val INFINITE_UNIV___NUM = store_thm ("INFINITE_UNIV___NUM",
   ``INFINITE (UNIV:num set)``,

SIMP_TAC std_ss [INFINITE_UNIV] THEN
Q.EXISTS_TAC `SUC` THEN
SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `0` THEN
DECIDE_TAC);




val INFINITE_UNIV___STRING = store_thm ("INFINITE_UNIV___STRING",
   ``INFINITE (UNIV:string set)``,

SIMP_TAC std_ss [INFINITE_UNIV] THEN
Q.EXISTS_TAC `STRING c` THEN
SIMP_TAC list_ss [] THEN
Q.EXISTS_TAC `""` THEN
SIMP_TAC list_ss []);




val SAFE_EL_def = Define `
   (SAFE_EL e n [] = e) /\
   (SAFE_EL e 0 (x::l) = x) /\
   (SAFE_EL e (SUC n) (x::l) = SAFE_EL e n l)`


val SAFE_EL_SEM = store_thm ("SAFE_EL_SEM",
   ``!e n l. SAFE_EL e n l =
               if (n < LENGTH l) then EL n l else e``,

   Induct_on `n` THENL [
      Cases_on `l` THEN SIMP_TAC list_ss [SAFE_EL_def],
      Cases_on `l` THEN ASM_SIMP_TAC list_ss [SAFE_EL_def]
   ])


val SAFE_DEL_EL_def = Define `
   (SAFE_DEL_EL n [] = []) /\
   (SAFE_DEL_EL 0 (x::l) = [x]) /\
   (SAFE_DEL_EL (SUC n) (x::l) = SAFE_DEL_EL n l)`

val SAFE_DEL_EL_THM = store_thm ("SAFE_DEL_EL_THM",
 ``(!n. (SAFE_DEL_EL n [] = [])) /\
   (!x l. (SAFE_DEL_EL 0 (x::l) = [x])) /\
   (!n x l. (SAFE_DEL_EL (SUC n) (x::l) = SAFE_DEL_EL n l))``,

REWRITE_TAC [SAFE_DEL_EL_def]);



val SAFE_DEL_EL_SEM = store_thm ("SAFE_DEL_EL_SEM",
 ``(!n (l:'a list). (n < LENGTH l) ==> (SAFE_DEL_EL n l = [EL n l])) /\
   (!n (l:'a list). ~(n < LENGTH l) ==> (SAFE_DEL_EL n l = []))``,

   SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN
   Induct_on `n` THENL [
      Cases_on `l` THEN SIMP_TAC list_ss [SAFE_DEL_EL_THM],
      Cases_on `l` THEN ASM_SIMP_TAC list_ss [SAFE_DEL_EL_THM]
   ])


val DELETE_ELEMENT_def = Define `
   (DELETE_ELEMENT n [] = []) /\
   (DELETE_ELEMENT 0 (x::l) = l) /\
   (DELETE_ELEMENT (SUC n) (x::l) = x::DELETE_ELEMENT n l)`

val DELETE_ELEMENT_THM = store_thm ("DELETE_ELEMENT_THM",
   ``(!n. DELETE_ELEMENT n [] = []) /\
     (!x l. DELETE_ELEMENT 0 (x::l) = l) /\
     (!n x l. (DELETE_ELEMENT (SUC n) (x::l) = x::DELETE_ELEMENT n l))``,

   REWRITE_TAC [DELETE_ELEMENT_def])


val MEM_DELETE_ELEMENT = store_thm ("MEM_DELETE_ELEMENT",
   ``!x n l. ((~(x = EL n l)) /\ MEM x l) ==>
             MEM x (DELETE_ELEMENT n l)``,


   Induct_on `l` THENL [
      SIMP_TAC list_ss [DELETE_ELEMENT_THM],

      Cases_on `n` THEN (
         SIMP_TAC list_ss [DELETE_ELEMENT_THM] THEN
         METIS_TAC[]
      )
   ]);


val LENGTH_DELETE_ELEMENT = store_thm ("LENGTH_DELETE_ELEMENT",
   ``!n l. LENGTH (DELETE_ELEMENT n l) =
           if (n < LENGTH l) then PRE (LENGTH l) else LENGTH l``,

   Induct_on `l` THENL [
      SIMP_TAC list_ss [DELETE_ELEMENT_THM],

      Cases_on `n` THEN (
         ASM_SIMP_TAC list_ss [DELETE_ELEMENT_THM]
      )
   ]);


Theorem EL_DELETE_ELEMENT:
  (!n1 n2 l. n1 < n2 ==> (EL n1 (DELETE_ELEMENT n2 l) = EL n1 l)) /\
  (!n1 n2 l. ~(n1 < n2) /\ n1 < LENGTH l ==>
             (EL n1 (DELETE_ELEMENT n2 l) = EL (SUC n1) l))
Proof
   CONJ_TAC THENL [
      Induct_on `l` THENL [
         SIMP_TAC list_ss [DELETE_ELEMENT_THM],

         Cases_on `n2` THENL [
            SIMP_TAC list_ss [],

            SIMP_TAC list_ss [DELETE_ELEMENT_THM] THEN
            Cases_on `n1` THEN SIMP_TAC list_ss [] THEN
            ASM_SIMP_TAC std_ss []
         ]
      ],

      Induct_on `l` THENL [
         SIMP_TAC list_ss [DELETE_ELEMENT_THM],

         Cases_on `n1` THENL [
            SIMP_TAC list_ss [] THEN
            REPEAT STRIP_TAC THEN
            ASM_SIMP_TAC std_ss [DELETE_ELEMENT_THM],


            SIMP_TAC list_ss [] THEN
            Cases_on `n2` THENL [
               SIMP_TAC list_ss [DELETE_ELEMENT_THM],
               ASM_SIMP_TAC list_ss [DELETE_ELEMENT_THM]
            ]
         ]
      ]
   ]
QED




val DELETE_ELEMENT_DELETE_ELEMENT = store_thm ("DELETE_ELEMENT_DELETE_ELEMENT",
   ``!n1 n2 l. ((n1 <= n2) ==> (DELETE_ELEMENT n2 (DELETE_ELEMENT n1 l) =
                               DELETE_ELEMENT n1 (DELETE_ELEMENT (SUC n2) l)))``,

   Induct_on `l` THENL [
      SIMP_TAC list_ss [DELETE_ELEMENT_THM],

      Cases_on `n1` THEN Cases_on `n2` THEN (
         ASM_SIMP_TAC list_ss [DELETE_ELEMENT_THM]
      )
   ]);


val SWAP_ELEMENTS_def = Define `
   (SWAP_ELEMENTS 0 0 l = l) /\
   (SWAP_ELEMENTS (SUC n) 0 l = l) /\
   (SWAP_ELEMENTS x y [] = []) /\
   (SWAP_ELEMENTS x y [e] = [e]) /\
   (SWAP_ELEMENTS 0 (SUC n) (e1::e2::l) = (SAFE_EL e1 n (e2::l)) :: REPLACE_ELEMENT e1 n (e2::l)) /\
   (SWAP_ELEMENTS (SUC m) (SUC n) (e::l) = e:: (SWAP_ELEMENTS m n l))`

val SWAP_ELEMENTS_THM = store_thm ("SWAP_ELEMENTS_THM",
   ``(!x y (l:'a list). y <= x ==> (SWAP_ELEMENTS x y l = l)) /\
     (!x y. SWAP_ELEMENTS x y [] = ([]:'a list)) /\
     (!x y e:'a. SWAP_ELEMENTS x y [e] = [e]) /\
     (!y e (l:'a list). SWAP_ELEMENTS y y l = l) /\
     (!y e (l:'a list). SWAP_ELEMENTS (SUC y) 0 l = l) /\
     (!y e (l:'a list).
         (SWAP_ELEMENTS 0 (SUC y) (e::l) = (SAFE_EL e y l) :: REPLACE_ELEMENT e y l)) /\
     (!x y e (l:'a list). (SWAP_ELEMENTS (SUC x) (SUC y) (e::l) = e:: (SWAP_ELEMENTS x y l)))
``,
   MATCH_MP_TAC (prove (``(a /\ (a ==> b)) ==> (a /\ b)``, PROVE_TAC[])) THEN
   CONJ_TAC THEN1 (
      Induct_on `x` THENL [
         Cases_on `l` THENL [
            SIMP_TAC std_ss [SWAP_ELEMENTS_def],
            Cases_on `t` THEN SIMP_TAC std_ss [SWAP_ELEMENTS_def]
         ],

         Cases_on `y` THENL [
            Cases_on `l` THENL [
               SIMP_TAC std_ss [SWAP_ELEMENTS_def],
               Cases_on `t` THEN SIMP_TAC std_ss [SWAP_ELEMENTS_def]
            ],

            Cases_on `l` THENL [
               SIMP_TAC std_ss [SWAP_ELEMENTS_def],

               Cases_on `t` THEN
               ASM_SIMP_TAC std_ss [SWAP_ELEMENTS_def]
            ]
         ]
      ]
   ) THEN
   STRIP_TAC THEN
   REPEAT CONJ_TAC THENL [
      Cases_on `x` THEN Cases_on `y` THEN
      SIMP_TAC std_ss [SWAP_ELEMENTS_def],

      Cases_on `x` THEN Cases_on `y` THEN
      SIMP_TAC std_ss [SWAP_ELEMENTS_def],

      ASM_SIMP_TAC arith_ss [],

      ASM_SIMP_TAC arith_ss [],

      Cases_on `l` THENL [
         SIMP_TAC std_ss [SWAP_ELEMENTS_def] THEN
         Cases_on `y` THEN
         SIMP_TAC std_ss [SAFE_EL_def, REPLACE_ELEMENT_def],

         SIMP_TAC std_ss [SWAP_ELEMENTS_def]
      ],

      Cases_on `l` THEN
      Cases_on `x` THEN Cases_on `y` THEN
      SIMP_TAC std_ss [SWAP_ELEMENTS_def]
   ])



val SWAP_ELEMENTS_SEM = store_thm ("SWAP_ELEMENTS_SEM",
   ``!x y l. ((x <= y) /\ y < LENGTH l) ==>
             ((EL x (SWAP_ELEMENTS x y l) = EL y l) /\
              (EL y (SWAP_ELEMENTS x y l) = EL x l) /\
              (!p. (~(p = x) /\ ~(p = y) /\ (p < LENGTH l)) ==>
                  (EL p (SWAP_ELEMENTS x y l) = EL p l)))``,

   Induct_on `x` THENL [
      Induct_on `y` THENL [
         SIMP_TAC list_ss [SWAP_ELEMENTS_THM],

         Cases_on `l` THEN1 SIMP_TAC list_ss [] THEN
         SIMP_TAC list_ss [SWAP_ELEMENTS_THM, SAFE_EL_SEM, REPLACE_ELEMENT_SEM] THEN
         REPEAT STRIP_TAC THEN
         Cases_on `p` THENL [
            FULL_SIMP_TAC std_ss [],

            FULL_SIMP_TAC list_ss [REPLACE_ELEMENT_SEM]
         ]
      ],

      Cases_on `y` THEN1 SIMP_TAC list_ss [] THEN
      Cases_on `l` THEN1 SIMP_TAC list_ss [] THEN

      ASM_SIMP_TAC list_ss [SWAP_ELEMENTS_THM] THEN
      REPEAT STRIP_TAC THEN
      Cases_on `p` THENL [
         SIMP_TAC list_ss [],
         FULL_SIMP_TAC list_ss []
      ]
   ])

val SWAP_ELEMENTS_SEM___MP = save_thm ("SWAP_ELEMENTS_SEM___MP",
(SIMP_RULE std_ss [IMP_CONJ_THM, FORALL_AND_THM,
                  GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] SWAP_ELEMENTS_SEM));


val SWAP_TO_POS_def = Define `
   (SWAP_TO_POS x y [] = []) /\
   (SWAP_TO_POS 0 0 (e::l) = (e::l)) /\
   (SWAP_TO_POS (SUC m) 0 (e::l) = e::l) /\
   (SWAP_TO_POS 0 (SUC n) (e::l) = (SAFE_DEL_EL n l) ++ e::(DELETE_ELEMENT n l))/\
   (SWAP_TO_POS (SUC m) (SUC n) (e::l) = e::SWAP_TO_POS m n l)`

val SWAP_TO_POS_THM = store_thm ("SWAP_TO_POS_THM",
   ``(!x y (l:'a list). y <= x ==> (SWAP_TO_POS x y l = l)) /\
     (!x y. SWAP_TO_POS x y [] = ([]:'a list)) /\
     (!x y e:'a. SWAP_TO_POS x y [e] = [e]) /\
     (!y e (l:'a list). SWAP_TO_POS y y l = l) /\
     (!y e (l:'a list). SWAP_TO_POS (SUC y) 0 l = l) /\
     (!y e (l:'a list).
         (SWAP_TO_POS 0 (SUC y) (e::l) = (SAFE_DEL_EL y l) ++ e::DELETE_ELEMENT y l)) /\
     (!x y e (l:'a list). (SWAP_TO_POS (SUC x) (SUC y) (e::l) = e:: (SWAP_TO_POS x y l)))``,

   MATCH_MP_TAC (prove (``(a /\ (a ==> b)) ==> (a /\ b)``, PROVE_TAC[])) THEN
   CONJ_TAC THEN1 (
      Induct_on `x` THENL [
         Cases_on `l` THEN SIMP_TAC std_ss [SWAP_TO_POS_def],

         Cases_on `y` THENL [
            Cases_on `l` THEN SIMP_TAC std_ss [SWAP_TO_POS_def],
            Cases_on `l` THEN ASM_SIMP_TAC std_ss [SWAP_TO_POS_def]
         ]
      ]
   ) THEN
   STRIP_TAC THEN
   REPEAT CONJ_TAC THENL [
      Cases_on `x` THEN Cases_on `y` THEN
      SIMP_TAC std_ss [SWAP_TO_POS_def],

      Cases_on `x` THEN Cases_on `y` THEN (
         SIMP_TAC list_ss [SWAP_TO_POS_def, DELETE_ELEMENT_THM, SAFE_DEL_EL_THM]
      ) THEN
      Cases_on `n` THEN Cases_on `n'` THEN
      SIMP_TAC std_ss [SWAP_TO_POS_def],

      ASM_SIMP_TAC arith_ss [],

      ASM_SIMP_TAC arith_ss [],

      SIMP_TAC std_ss [SWAP_TO_POS_def],
      SIMP_TAC std_ss [SWAP_TO_POS_def]
   ])








val SUC_RULE = CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV;


val SWAP_ELEMENTS___REWRITE = SUC_RULE (CONJUNCT2 SWAP_ELEMENTS_THM);
val REPLACE_ELEMENT___REWRITE = SUC_RULE (SIMP_RULE std_ss [FORALL_AND_THM] (GEN_ALL REPLACE_ELEMENT_def))
val SAFE_EL___REWRITE = SUC_RULE (SIMP_RULE std_ss [FORALL_AND_THM] (GEN_ALL SAFE_EL_def))
val SWAP_TO_POS___REWRITE = SUC_RULE (CONJUNCT2 SWAP_TO_POS_THM);
val DELETE_ELEMENT___REWRITE =  SUC_RULE (DELETE_ELEMENT_THM);
val SAFE_DEL_EL___REWRITE = SUC_RULE (SAFE_DEL_EL_THM);

val SWAP_REWRITES = save_thm ("SWAP_REWRITES",
   LIST_CONJ [SWAP_ELEMENTS___REWRITE, REPLACE_ELEMENT___REWRITE, SAFE_EL___REWRITE,
              SWAP_TO_POS___REWRITE, DELETE_ELEMENT___REWRITE, SAFE_DEL_EL___REWRITE])



val PERM___SAFE_REPLACE_EL = store_thm ("PERM___SAFE_REPLACE_EL",
``!e n l. PERM ((SAFE_EL e n l) :: REPLACE_ELEMENT e n l) (e::l)``,

Induct_on `n` THENL [
   Cases_on `l` THENL [
      SIMP_TAC std_ss [SAFE_EL_def, REPLACE_ELEMENT_def, PERM_REFL],

      SIMP_TAC std_ss [SAFE_EL_def, REPLACE_ELEMENT_def, PERM_REFL,
         PERM_SWAP_AT_FRONT]
   ],

   Cases_on `l` THENL [
      SIMP_TAC std_ss [SAFE_EL_def, REPLACE_ELEMENT_def, PERM_REFL],

      SIMP_TAC std_ss [SAFE_EL_def, REPLACE_ELEMENT_def] THEN
      GEN_TAC THEN
      `!e1:'a e2 e3 e4 l l'.
         PERM (e1::e2::l) (e3::e4::l') =
         PERM (e2::e1::l) (e4::e3::l')` suffices_by (STRIP_TAC THEN
         METIS_TAC[PERM_MONO]
      ) THEN
      POP_ASSUM (fn thm => ALL_TAC) THEN
      METIS_TAC[PERM_MONO, PERM_TRANS, PERM_SWAP_AT_FRONT, PERM_SYM, PERM_REFL]
   ]
])

val PERM___SWAP_ELEMENTS = store_thm ("PERM___SWAP_ELEMENTS",
``!m n l. PERM (SWAP_ELEMENTS m n l) l``,

Induct_on `m` THENL [
   Cases_on `n` THENL [
      SIMP_TAC std_ss [SWAP_ELEMENTS_THM, PERM_REFL],

      Cases_on `l` THENL [
         SIMP_TAC std_ss [SWAP_ELEMENTS_THM, PERM_REFL],

         Cases_on `t` THENL [
            Cases_on `n'` THEN
            SIMP_TAC std_ss [SWAP_ELEMENTS_THM, PERM_REFL, SAFE_EL_def, REPLACE_ELEMENT_def],

            SIMP_TAC std_ss [SWAP_ELEMENTS_def, PERM___SAFE_REPLACE_EL]
         ]
      ]
   ],

   Cases_on `n` THENL [
      SIMP_TAC std_ss [SWAP_ELEMENTS_THM, PERM_REFL],

      Cases_on `l` THENL [
         SIMP_TAC std_ss [SWAP_ELEMENTS_THM, PERM_REFL],

         SIMP_TAC std_ss [SWAP_ELEMENTS_THM] THEN
         METIS_TAC[PERM_MONO]
      ]
   ]
]);


val SWAP_ELEMENTS___LENGTH = store_thm ("SWAP_ELEMENTS___LENGTH",
``!n m l. (LENGTH (SWAP_ELEMENTS n m l) = LENGTH l)``,
METIS_TAC[PERM_LENGTH, PERM___SWAP_ELEMENTS]);

val SWAP_ELEMENTS___EQ_NIL = store_thm ("SWAP_ELEMENTS___EQ_NIL",
   ``!n m l. (SWAP_ELEMENTS n m l = []) = (l = [])``,
   SIMP_TAC std_ss [GSYM LENGTH_NIL, SWAP_ELEMENTS___LENGTH])


val PERM___SWAP_TO_POS = store_thm ("PERM___SWAP_TO_POS",
``!m n l. PERM (SWAP_TO_POS m n l) l``,

Induct_on `m` THENL [
   Cases_on `n` THENL [
      SIMP_TAC std_ss [SWAP_TO_POS_THM, PERM_REFL],

      Cases_on `l` THENL [
         SIMP_TAC std_ss [SWAP_TO_POS_THM, PERM_REFL],

         SIMP_TAC std_ss [SWAP_TO_POS_THM, PERM_REFL] THEN
         Q.SPEC_TAC (`t`, `l`) THEN
         Q.SPEC_TAC (`h`, `h`) THEN
         Q.SPEC_TAC (`n'`, `n`) THEN
         Induct_on `n` THENL [
            Cases_on `l` THENL [
               SIMP_TAC list_ss [SAFE_DEL_EL_THM, DELETE_ELEMENT_THM, PERM_REFL],

               SIMP_TAC list_ss [SAFE_DEL_EL_THM, DELETE_ELEMENT_THM, PERM_REFL,
                  PERM_SWAP_AT_FRONT]
            ],

            Cases_on `l` THENL [
               SIMP_TAC list_ss [SAFE_DEL_EL_THM, DELETE_ELEMENT_THM, PERM_REFL],

               SIMP_TAC std_ss [SAFE_DEL_EL_THM, DELETE_ELEMENT_THM] THEN
               GEN_TAC THEN
               `PERM (SAFE_DEL_EL n t ++ h'::h::DELETE_ELEMENT n t)
                     (h'::(SAFE_DEL_EL n t ++ h::DELETE_ELEMENT n t))` by (
                  `h'::h::DELETE_ELEMENT n t =
                   [h'] ++ (h::DELETE_ELEMENT n t)` by METIS_TAC [CONS_APPEND] THEN
                  `h'::SAFE_DEL_EL n t = [h']++SAFE_DEL_EL n t` by METIS_TAC [CONS_APPEND] THEN
                  ASM_SIMP_TAC std_ss [APPEND_ASSOC, GSYM APPEND] THEN
                  REPEAT (POP_ASSUM (fn thm => ALL_TAC)) THEN
                  METIS_TAC [PERM_APPEND, APPEND_ASSOC, PERM_CONG, PERM_REFL]
               ) THEN
               METIS_TAC[PERM_MONO, PERM_REFL, PERM_TRANS]
            ]
         ]
      ]
   ],

   Cases_on `n` THENL [
      SIMP_TAC std_ss [SWAP_TO_POS_THM, PERM_REFL],

      Cases_on `l` THENL [
         SIMP_TAC std_ss [SWAP_TO_POS_THM, PERM_REFL],

         SIMP_TAC std_ss [SWAP_TO_POS_THM] THEN
         METIS_TAC[PERM_MONO]
      ]
   ]
]);



val LIST_DS_ENTAILS___PERM_SWAP_ELEMENTS = store_thm (
"LIST_DS_ENTAILS___PERM_SWAP_ELEMENTS",
``!n1 m1 n2 m2 n3 m3 n4 m4 n5 m5 n6 m6 c1 c2 pf sf pf' sf'.

LIST_DS_ENTAILS (c1, c2) (pf, sf) (pf', sf') =
LIST_DS_ENTAILS (SWAP_ELEMENTS n5 m5 c1, SWAP_ELEMENTS n6 m6 c2) ((SWAP_ELEMENTS n1 m1 pf), (SWAP_ELEMENTS n2 m2 sf))
                ((SWAP_ELEMENTS n3 m3 pf'), (SWAP_ELEMENTS n4 m4 sf'))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
METIS_TAC [PERM___SWAP_ELEMENTS, PERM_SYM]);



val LIST_DS_ENTAILS___PERM_SWAP_TO_POS = store_thm (
"LIST_DS_ENTAILS___PERM_SWAP_TO_POS",
``!n1 m1 n2 m2 n3 m3 n4 m4 n5 m5 n6 m6 c1 c2 pf sf pf' sf'.

LIST_DS_ENTAILS (c1,c2) (pf, sf) (pf', sf') =
LIST_DS_ENTAILS (SWAP_TO_POS n5 m5 c1, SWAP_TO_POS n6 m6 c2) ((SWAP_TO_POS n1 m1 pf), (SWAP_TO_POS n2 m2 sf))
                ((SWAP_TO_POS n3 m3 pf'), (SWAP_TO_POS n4 m4 sf'))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
METIS_TAC [PERM___SWAP_TO_POS, PERM_SYM]);



val PF_TURN_EQ_def = Define `
  (PF_TURN_EQ (pf_equal e1 e2) = (pf_equal e2 e1)) /\
  (PF_TURN_EQ (pf_unequal e1 e2) = (pf_unequal e2 e1)) /\
  (PF_TURN_EQ x = x)`


val PF_TURN_EQ___SEM = store_thm ("PF_TURN_EQ___SEM",
   ``!s pf. PF_SEM s (PF_TURN_EQ pf) = PF_SEM s pf``,

   Induct_on `pf` THEN (
      SIMP_TAC std_ss [PF_TURN_EQ_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def] THEN
      METIS_TAC[]
   )
);



val SAFE_MAP_def = Define `
   (SAFE_MAP x f g [] = []) /\
   (SAFE_MAP T [] g l = MAP g l) /\
   (SAFE_MAP F [] g l = l) /\
   (SAFE_MAP x (T::f) g (e::l) = (g e)::(SAFE_MAP x f g l)) /\
   (SAFE_MAP x (F::f) g (e::l) = e::(SAFE_MAP x f g l))`

val SAFE_MAP_THM = store_thm ("SAFE_MAP_THM",
``(SAFE_MAP x f g [] = []) /\
(SAFE_MAP T [] g l = MAP g l) /\
(SAFE_MAP F [] g l = l) /\
(SAFE_MAP x (T::f) g (e::l) = (g e)::(SAFE_MAP x f g l)) /\
(SAFE_MAP x (F::f) g (e::l) = e::(SAFE_MAP x f g l))``,

Cases_on `l` THEN SIMP_TAC list_ss [SAFE_MAP_def])


val LIST_PF_SEM___PF_TURN_EQ = store_thm ("LIST_PF_SEM___PF_TURN_EQ",
   ``!f s pfL. LIST_PF_SEM s (SAFE_MAP F f PF_TURN_EQ pfL) =
            LIST_PF_SEM s pfL``,

   Induct_on `pfL` THENL [
      SIMP_TAC list_ss [SAFE_MAP_THM],

      Cases_on `f` THENL [
         SIMP_TAC std_ss [SAFE_MAP_THM],

         Cases_on `h` THEN (
            ASM_SIMP_TAC list_ss [LIST_PF_SEM_THM, PF_TURN_EQ___SEM, SAFE_MAP_THM]
         )
      ]
   ])


val LIST_DS_ENTAILS___PF_TURN_EQ = store_thm ("LIST_DS_ENTAILS___PF_TURN_EQ",
``!f1 f2 C pf sf pf' sf'.
   LIST_DS_ENTAILS C (pf, sf) (pf', sf') =
   LIST_DS_ENTAILS C (SAFE_MAP F f1 PF_TURN_EQ pf, sf) (SAFE_MAP F f2 PF_TURN_EQ pf', sf')``,

   SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_def, LIST_PF_SEM___PF_TURN_EQ])







val SAFE_BUTFIRSTN_def = Define `
   (SAFE_BUTFIRSTN 0 l = l) /\
   (SAFE_BUTFIRSTN n [] = []) /\
   (SAFE_BUTFIRSTN (SUC n) (e::l) = SAFE_BUTFIRSTN n l)`;



val SAFE_BUTFIRSTN_THM = store_thm ("SAFE_BUTFIRSTN_THM",
   ``(SAFE_BUTFIRSTN 0 l = l) /\
   (SAFE_BUTFIRSTN n [] = []) /\
   (SAFE_BUTFIRSTN (SUC n) (e::l) = SAFE_BUTFIRSTN n l)``,

   Cases_on `n` THEN SIMP_TAC std_ss [SAFE_BUTFIRSTN_def])


val SAFE_BUTFIRSTN___REWRITE = save_thm ("SAFE_BUTFIRSTN___REWRITE",
SUC_RULE (SIMP_RULE std_ss [FORALL_AND_THM] (GEN_ALL SAFE_BUTFIRSTN_THM)));


val POS_FILTER_def = Define `
   (POS_FILTER [] p l = l) /\
   (POS_FILTER f p [] = []) /\
   (POS_FILTER (T::f) p (e::l) = let (l' = POS_FILTER f p l) in if p e then l' else (e::l')) /\
   (POS_FILTER (F::f) p (e::l) = e::(POS_FILTER f p l))`


val POS_FILTER_THM = store_thm ("POS_FILTER_THM",
`` (POS_FILTER [] p l = l) /\
   (POS_FILTER f p [] = []) /\
   (POS_FILTER (T::f) p (e::l) = let (l' = POS_FILTER f p l) in if p e then l' else (e::l')) /\
   (POS_FILTER (F::f) p (e::l) = e::(POS_FILTER f p l))``,

Cases_on `f` THEN REWRITE_TAC [POS_FILTER_def])


val MEM_POS_FILTER = store_thm ("MEM_POS_FILTER",
   ``!x f p l. ((MEM x l) /\ ~(p x)) ==> MEM x (POS_FILTER f p l)``,

   Induct_on `l` THENL [
      SIMP_TAC std_ss [POS_FILTER_THM],

      Cases_on `f` THEN SIMP_TAC list_ss [POS_FILTER_THM] THEN
      Cases_on `h` THEN (
         ASM_SIMP_TAC list_ss [POS_FILTER_THM, LET_THM, RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM,
            COND_RATOR, COND_RAND]
      )
   ])


val MEM_POS_FILTER_2 = store_thm ("MEM_POS_FILTER_2",
   ``!x f p l. MEM x (POS_FILTER f p l) ==> (MEM x l)``,

   Induct_on `l` THENL [
      SIMP_TAC std_ss [POS_FILTER_THM],

      Cases_on `f` THEN SIMP_TAC list_ss [POS_FILTER_THM] THEN
      Cases_on `h` THEN (
         ASM_SIMP_TAC list_ss [POS_FILTER_THM, LET_THM,
            COND_RATOR, COND_RAND] THEN
         METIS_TAC[]
      )
   ])


val SAFE_FILTER_def = Define `
   (SAFE_FILTER T [] l = l) /\
   (SAFE_FILTER F [] l = []) /\
   (SAFE_FILTER x f [] = []) /\
   (SAFE_FILTER x (T::f) (e::l) = e::SAFE_FILTER x f l) /\
   (SAFE_FILTER x (F::f) (e::l) = SAFE_FILTER x f l)`;


val SAFE_FILTER_THM = store_thm ("SAFE_FILTER_THM",
`` (SAFE_FILTER T [] l = l) /\
   (SAFE_FILTER F [] l = []) /\
   (SAFE_FILTER x f [] = []) /\
   (SAFE_FILTER x (T::f) (e::l) = e::SAFE_FILTER x f l) /\
   (SAFE_FILTER x (F::f) (e::l) = SAFE_FILTER x f l)``,

   Cases_on `x` THEN
   SIMP_TAC std_ss [SAFE_FILTER_def] THEN
   Cases_on `f` THEN
   SIMP_TAC std_ss [SAFE_FILTER_def])

val SAFE_FILTER_APPEND = store_thm ("SAFE_FILTER_APPEND",
   ``!x f l1 l2. SAFE_FILTER x f (l1 ++ l2) =
         SAFE_FILTER x f l1 ++ (SAFE_FILTER x (SAFE_BUTFIRSTN (LENGTH l1) f) l2)``,

   Induct_on `l1` THENL [
      SIMP_TAC list_ss [SAFE_BUTFIRSTN_THM, SAFE_FILTER_THM],

      Cases_on `f` THENL [
         Cases_on `x` THENL [
            SIMP_TAC list_ss [SAFE_FILTER_THM, SAFE_BUTFIRSTN_THM],
            SIMP_TAC list_ss [SAFE_FILTER_THM, SAFE_BUTFIRSTN_THM]
         ],

         Cases_on `h` THEN (
            ASM_SIMP_TAC list_ss [SAFE_FILTER_THM, SAFE_BUTFIRSTN_THM]
         )
      ]
   ])

val MEM_SAFE_FILTER = store_thm ("MEM_SAFE_FILTER",
   ``!x f l e. MEM e (SAFE_FILTER x f l) ==> MEM e l``,

   Induct_on `f` THENL [
      Cases_on `x` THEN
      SIMP_TAC list_ss [SAFE_FILTER_THM],

      Cases_on `l` THEN (
         SIMP_TAC list_ss [SAFE_FILTER_THM]
      ) THEN
      Cases_on `h'` THEN (
         SIMP_TAC list_ss [SAFE_FILTER_THM] THEN
         METIS_TAC[]
      )
   ]);



val LIST_PF_SEM___SAFE_FILTER = store_thm ("LIST_PF_SEM___SAFE_FILTER",
``!s x f pfL. LIST_PF_SEM s pfL ==> LIST_PF_SEM s (SAFE_FILTER x f pfL)``,

Induct_on `pfL` THENL [
   SIMP_TAC std_ss [SAFE_FILTER_THM],

   Cases_on `f` THENL [
      Cases_on `x` THEN
      SIMP_TAC std_ss [SAFE_FILTER_THM, LIST_PF_SEM_THM],

      Cases_on `h` THENL [
         ASM_SIMP_TAC std_ss [SAFE_FILTER_THM, LIST_PF_SEM_THM],
         ASM_SIMP_TAC std_ss [SAFE_FILTER_THM, LIST_PF_SEM_THM]
      ]
   ]
]);



val LIST_DS_ENTAILS___CLEAN_PF = store_thm ("LIST_DS_ENTAILS___CLEAN_PF",
``!x f C pf sf pf' sf'.
LIST_DS_ENTAILS C (SAFE_FILTER x f pf, sf) (pf', sf') ==>
LIST_DS_ENTAILS C (pf, sf) (pf', sf')``,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_def] THEN
METIS_TAC[LIST_PF_SEM___SAFE_FILTER])




val SWAP_TO_POS___DELETE_ELEMENT = store_thm ("SWAP_TO_POS___DELETE_ELEMENT",

   ``!n l. n < LENGTH l ==>
           ((SWAP_TO_POS 0 n l) = (EL n l)::(DELETE_ELEMENT n l))``,

   Cases_on `l` THEN Cases_on `n` THEN
   SIMP_TAC list_ss [SWAP_TO_POS_THM, DELETE_ELEMENT_THM, SAFE_DEL_EL_SEM])

val SAFE_DEL_EL___EQ = store_thm ("SAFE_DEL_EL___EQ",
   ``(!n (l:'a list). (SAFE_DEL_EL n l = []) = (~(n < LENGTH l))) /\
     (!n (l:'a list) e. (SAFE_DEL_EL n l = [e]) = ((n < LENGTH l) /\ (EL n l = e))) /\
     (!n (l:'a list) e1 e2 eL. ~(SAFE_DEL_EL n l = e1::e2::eL))``,

SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN
REPEAT GEN_TAC THEN
Cases_on `n < LENGTH l` THEN (
   ASM_SIMP_TAC list_ss [SAFE_DEL_EL_SEM]
))



val INFERENCE_SUBSTITUTION___EVAL1 = store_thm ("INFERENCE_SUBSTITUTION___EVAL1",
``!n e v c1 c2 pfL sfL pfL' sfL'.
         (SAFE_DEL_EL n pfL = [pf_equal (dse_var v) e]) ==>

         (
         LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL') =
         LIST_DS_ENTAILS (MAP (DS_VAR_SUBST v e) c1, MAP (\x. (DS_VAR_SUBST v e (FST x), DS_VAR_SUBST v e (SND x))) c2)
           (MAP (PF_SUBST v e) (DELETE_ELEMENT n pfL),MAP (SF_SUBST v e) sfL)
           (MAP (PF_SUBST v e) pfL',MAP (SF_SUBST v e) sfL'))``,

SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (SWAP_TO_POS 0 n pfL,sfL) (pfL',sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
FULL_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT,
   GSYM INFERENCE_SUBSTITUTION])



val INFERENCE_SUBSTITUTION___EVAL2 = store_thm ("INFERENCE_SUBSTITUTION___EVAL2",
``!n e v c1 c2 pfL sfL pfL' sfL'.
         (SAFE_DEL_EL n pfL = [pf_equal e (dse_var v)]) ==>

         (
         LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL') =
         LIST_DS_ENTAILS (MAP (DS_VAR_SUBST v e) c1, MAP (\x. (DS_VAR_SUBST v e (FST x), DS_VAR_SUBST v e (SND x))) c2)
           (MAP (PF_SUBST v e) (DELETE_ELEMENT n pfL),MAP (SF_SUBST v e) sfL)
           (MAP (PF_SUBST v e) pfL',MAP (SF_SUBST v e) sfL'))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1,c2) (SWAP_TO_POS 0 n pfL,sfL) (pfL',sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
`LIST_DS_ENTAILS (c1,c2) (pf_equal e (dse_var v)::DELETE_ELEMENT n pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1,c2) (pf_equal (dse_var v) e::DELETE_ELEMENT n pfL,sfL) (pfL',sfL')` by (
   SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_EVAL, DS_EXPRESSION_EQUAL_def] THEN
   METIS_TAC[]
) THEN
FULL_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT,
   GSYM INFERENCE_SUBSTITUTION]);





val PF_TRIVIAL_FILTER_PRED_def = Define
   `(PF_TRIVIAL_FILTER_PRED pf_true = T) /\
    (PF_TRIVIAL_FILTER_PRED (pf_unequal e1 e2) = F) /\
    (PF_TRIVIAL_FILTER_PRED (pf_equal e1 e2) = (e1 = e2)) /\
    (PF_TRIVIAL_FILTER_PRED (pf_and pf1 pf2) =
     PF_TRIVIAL_FILTER_PRED pf1 /\ PF_TRIVIAL_FILTER_PRED pf2)`


val PF_TRIVIAL_FILTER_PRED_SEM = store_thm ("PF_TRIVIAL_FILTER_PRED_SEM",

   ``!pf. PF_TRIVIAL_FILTER_PRED pf ==> !s. PF_SEM s pf``,

Induct_on `pf` THENL [
   REWRITE_TAC [PF_SEM_def],
   SIMP_TAC std_ss [PF_SEM_def, PF_TRIVIAL_FILTER_PRED_def, DS_EXPRESSION_EQUAL_def],
   SIMP_TAC std_ss [PF_TRIVIAL_FILTER_PRED_def],
   ASM_SIMP_TAC std_ss [PF_SEM_def, PF_TRIVIAL_FILTER_PRED_def]
]);



val LIST_PF_SEM___TRIVIAL_FILTER_THM = store_thm ("LIST_PF_SEM___TRIVIAL_FILTER_THM",
   ``!s f pfL.
          LIST_PF_SEM s (POS_FILTER f PF_TRIVIAL_FILTER_PRED pfL) =
           LIST_PF_SEM s pfL``,

Induct_on `pfL` THENL [
   REWRITE_TAC [POS_FILTER_THM],

   Cases_on `f` THEN1 REWRITE_TAC [POS_FILTER_THM] THEN
   Cases_on `h` THENL [
      ASM_SIMP_TAC std_ss [POS_FILTER_THM, LET_THM, COND_RATOR, COND_RAND,
         LIST_PF_SEM_THM, PF_TRIVIAL_FILTER_PRED_SEM],

      ASM_SIMP_TAC std_ss [POS_FILTER_THM, LIST_PF_SEM_THM]
   ]
]);






val SF_TRIVIAL_FILTER_PRED_def = Define
   `(SF_TRIVIAL_FILTER_PRED sf_emp = T) /\
    (SF_TRIVIAL_FILTER_PRED (sf_points_to e a) = F) /\
    (SF_TRIVIAL_FILTER_PRED (sf_tree fL es e) = (es = e)) /\
    (SF_TRIVIAL_FILTER_PRED (sf_star sf1 sf2) =
     SF_TRIVIAL_FILTER_PRED sf1 /\ SF_TRIVIAL_FILTER_PRED sf2)`


val SF_TRIVIAL_FILTER_PRED_THM = store_thm ("SF_TRIVIAL_FILTER_PRED_THM",
  ``(SF_TRIVIAL_FILTER_PRED sf_emp = T) /\
    (SF_TRIVIAL_FILTER_PRED (sf_points_to e a) = F) /\
    (SF_TRIVIAL_FILTER_PRED (sf_tree fL es e) = (es = e)) /\
    (SF_TRIVIAL_FILTER_PRED (sf_ls f e1 e2) = (e1 = e2)) /\
    (SF_TRIVIAL_FILTER_PRED (sf_bin_tree (f1,f2) e) = (e = dse_nil)) /\
    (SF_TRIVIAL_FILTER_PRED (sf_star sf1 sf2) =
     SF_TRIVIAL_FILTER_PRED sf1 /\ SF_TRIVIAL_FILTER_PRED sf2)``,

SIMP_TAC std_ss [SF_TRIVIAL_FILTER_PRED_def, sf_ls_def, sf_bin_tree_def] THEN
METIS_TAC[]);




val SF_TRIVIAL_FILTER_PRED_SEM = store_thm ("SF_TRIVIAL_FILTER_PRED_SEM",

   ``!sf. SF_TRIVIAL_FILTER_PRED sf ==> (!s h. SF_SEM s h sf = (h = FEMPTY))``,

Induct_on `sf` THENL [
   REWRITE_TAC [SF_SEM_def],
   SIMP_TAC std_ss [SF_TRIVIAL_FILTER_PRED_def],
   SIMP_TAC std_ss [SF_TRIVIAL_FILTER_PRED_def, SF_SEM___sf_tree_THM, DS_EXPRESSION_EQUAL_def],

   ASM_SIMP_TAC std_ss [SF_SEM_def, SF_TRIVIAL_FILTER_PRED_def, FUNION_FEMPTY_1, FDOM_FEMPTY,
      DISJOINT_EMPTY]
]);





val LIST_SF_SEM___TRIVIAL_FILTER_THM = store_thm ("LIST_SF_SEM___TRIVIAL_FILTER_THM",
   ``!s h f sfL.
          LIST_SF_SEM s h (POS_FILTER f SF_TRIVIAL_FILTER_PRED sfL) =
           LIST_SF_SEM s h sfL``,

Induct_on `sfL` THENL [
   REWRITE_TAC [POS_FILTER_THM],

   Cases_on `f` THEN1 REWRITE_TAC [POS_FILTER_THM] THEN
   Cases_on `h` THENL [
      ASM_SIMP_TAC std_ss [POS_FILTER_THM, LET_THM, COND_RATOR, COND_RAND,
         LIST_SF_SEM_THM, SF_TRIVIAL_FILTER_PRED_SEM, FUNION_FEMPTY_1,
         DISJOINT_EMPTY, FDOM_FEMPTY],

      ASM_SIMP_TAC std_ss [POS_FILTER_THM, LIST_SF_SEM_THM]
   ]
]);


val HEAP_DISTINCT___TRIVIAL_FILTER_THM = store_thm ("HEAP_DISTINCT___TRIVIAL_FILTER_THM",
   ``!s h f c1 c2.
          (HEAP_DISTINCT s h c1 (POS_FILTER f (\x. (FST x = SND x)) c2) =
          HEAP_DISTINCT s h c1 c2)``,


Induct_on `c2` THENL [
   SIMP_TAC list_ss [POS_FILTER_THM],

   REPEAT GEN_TAC THEN
   Cases_on `h` THEN
   Cases_on `f` THEN1 REWRITE_TAC [POS_FILTER_THM] THEN
   Cases_on `(POS_FILTER (h::t) (\x. FST x = SND x) ((q,r)::c2)) =
             ((q,r)::(POS_FILTER t (\x. FST x = SND x) c2))` THEN1 (
      ASM_SIMP_TAC std_ss [HEAP_DISTINCT___IND_DEF] THEN
      EQ_TAC THEN STRIP_TAC THEN
      ASM_SIMP_TAC std_ss [] THENL [
         DISJ2_TAC THEN
         REPEAT STRIP_TAC THEN
         Cases_on `DS_EXPRESSION_EQUAL s e1' e2'` THEN ASM_REWRITE_TAC[] THEN
         `MEM (e1',e2') (POS_FILTER t (\x. FST x = SND x) c2)` by (
            MATCH_MP_TAC MEM_POS_FILTER THEN
            FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def] THEN
            METIS_TAC[]
         ) THEN
         METIS_TAC[],


         DISJ2_TAC THEN
         REPEAT STRIP_TAC THEN
         `MEM (e1',e2') c2` by METIS_TAC[MEM_POS_FILTER_2] THEN
         METIS_TAC[]
      ]
   ) THEN
   Cases_on `h` THENL [
      ASM_SIMP_TAC std_ss [POS_FILTER_THM, LET_THM] THEN
      Cases_on `q = r` THENL [
         ASM_SIMP_TAC std_ss [HEAP_DISTINCT___EQUAL],
         FULL_SIMP_TAC std_ss [POS_FILTER_THM, LET_THM]
      ],

      FULL_SIMP_TAC std_ss [POS_FILTER_THM]
   ]
]);




val INFERENCE_TRIVIAL_FILTER = store_thm ("INFERENCE_TRIVIAL_FILTER",
``!f1 f2 f3 f4 f5  c1 c2 pfL sfL pfL' sfL'.
  LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
  LIST_DS_ENTAILS (c1, (POS_FILTER f1 (\x. (FST x = SND x)) c2)) (POS_FILTER f2 PF_TRIVIAL_FILTER_PRED pfL, POS_FILTER f3 SF_TRIVIAL_FILTER_PRED sfL) (POS_FILTER f4 PF_TRIVIAL_FILTER_PRED pfL',POS_FILTER f5 SF_TRIVIAL_FILTER_PRED sfL')``,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_def, LIST_PF_SEM___TRIVIAL_FILTER_THM,
   LIST_SF_SEM___TRIVIAL_FILTER_THM, HEAP_DISTINCT___TRIVIAL_FILTER_THM]);



val INFERENCE_INCONSISTENT_UNEQUAL___EVAL = store_thm ("INFERENCE_INCONSISTENT_UNEQUAL___EVAL",
 ``!n e c1 c2 pfL sfL pfL' sfL'.
         (SAFE_DEL_EL n pfL = [pf_unequal e e]) ==>
         LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL')``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (SWAP_TO_POS 0 n pfL,sfL) (pfL',sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT, INFERENCE_INCONSISTENT]);




val INFERENCE_INCONSISTENT___NIL_POINTS_TO___EVAL = store_thm ("INFERENCE_INCONSISTENT___NIL_POINTS_TO___EVAL",
 ``!n a c1 c2 pfL sfL pfL' sfL'.
         (SAFE_DEL_EL n sfL = [sf_points_to dse_nil a]) ==>
         LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL')``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n sfL) (pfL',sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT, INFERENCE_INCONSISTENT___NIL_POINTS_TO])



val INFERENCE_INCONSISTENT___precondition_POINTS_TO___EVAL = store_thm ("INFERENCE_INCONSISTENT___precondition_POINTS_TO___EVAL",
 ``!m n e a c1 c2 pfL sfL pfL' sfL'.
         ((SAFE_DEL_EL n sfL = [sf_points_to e a]) /\
         (SAFE_DEL_EL m c1 = [e])) ==>
         LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL')``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n sfL) (pfL',sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN
MATCH_MP_TAC INFERENCE_INCONSISTENT___precondition_POINTS_TO THEN
ASM_SIMP_TAC std_ss [EL_IS_EL]
);


val INFERENCE_INCONSISTENT___precondition_BIN_TREE___EVAL = store_thm ("INFERENCE_INCONSISTENT___precondition_BIN_TREE___EVAL",
 ``!m n e fL c1 c2 pfL sfL pfL' sfL'.
         ((SAFE_DEL_EL n sfL = [sf_bin_tree fL e]) /\
         (SAFE_DEL_EL m c1 = [e])) ==>
         LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL')``,


Cases_on `fL` THEN
SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n sfL) (pfL',sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN
MATCH_MP_TAC INFERENCE_INCONSISTENT___precondition_BIN_TREE THEN
ASM_SIMP_TAC std_ss [EL_IS_EL]);


val INFERENCE_INCONSISTENT___precondition_dse_nil = store_thm ("INFERENCE_INCONSISTENT___precondition_dse_nil",
 ``!n c1 c2 pfL sfL pfL' sfL'.
         (SAFE_DEL_EL n c1 = [dse_nil]) ==>
         LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL')``,

SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`MEM dse_nil c1` by METIS_TAC [EL_IS_EL] THEN
ASM_SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
METIS_TAC[HEAP_DISTINCT___dse_nil, DS_EXPRESSION_EQUAL_def]);



val INFERENCE_INCONSISTENT___precondition_distinct = store_thm ("INFERENCE_INCONSISTENT___precondition_distinct",
 ``!n m e c1 c2 pfL sfL pfL' sfL'.
         ((SAFE_DEL_EL n c1 = [e]) /\ (SAFE_DEL_EL m c1 = [e]) /\ ~(n = m)) ==>
         LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL')``,

SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [LIST_DS_ENTAILS_def] THEN
METIS_TAC[HEAP_DISTINCT___NOT_ALL_DISTINCT]);



val _ = Hol_datatype `hypothesis_rule_cases =
     hyp_keep
   | hyp_c_dse_nil of bool => num
   | hyp_c_unequal of num => num
   | hyp_in_precond of bool => num
   | hyp_in_self of bool => num`


val HYPOTHESIS_RULE_COND_def = Define `
   (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n h hyp_keep = F) /\

   (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n (pf_unequal e1 e2) (hyp_c_dse_nil F m)  =
      ((e1 = dse_nil) /\ (SAFE_DEL_EL m cL = [e2]))) /\
   (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n (pf_unequal e1 e2) (hyp_c_dse_nil T m)  =
      ((e2 = dse_nil) /\ (SAFE_DEL_EL m cL = [e1]))) /\
   (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n pf (hyp_c_dse_nil b m) = F) /\

   (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n (pf_unequal e1 e2) (hyp_c_unequal m1 m2)  =
      (~(m1 = m2) /\ (SAFE_DEL_EL m1 cL = [e1]) /\ (SAFE_DEL_EL m2 cL = [e2]))) /\
   (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n pf (hyp_c_unequal m1 m2) = F) /\


   (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n h (hyp_in_precond F m)  =
      (SAFE_DEL_EL m pfL1 = [h])) /\
   (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n h (hyp_in_precond T m)  =
      (SAFE_DEL_EL m pfL1 = [PF_TURN_EQ h])) /\

   (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n h (hyp_in_self F m)  =
      ((m < n) /\ (SAFE_DEL_EL m pfL2 = [h]))) /\
   (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n h (hyp_in_self T m)  =
      ((m < n) /\ (SAFE_DEL_EL m pfL2 = [PF_TURN_EQ h])))`



val HYPOTHESIS_RULE_COND_THM = store_thm ("HYPOTHESIS_RULE_COND_THM",
`` (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n pf hyp_keep = F) /\

   (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n (pf_unequal e1 e2) (hyp_c_dse_nil F m)  =
      ((e1 = dse_nil) /\ (SAFE_DEL_EL m cL = [e2]))) /\
   (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n (pf_unequal e1 e2) (hyp_c_dse_nil T m)  =
      ((e2 = dse_nil) /\ (SAFE_DEL_EL m cL = [e1]))) /\

   (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n (pf_unequal e1 e2) (hyp_c_unequal m1 m2)  =
      (~(m1 = m2) /\(SAFE_DEL_EL m1 cL = [e1]) /\ (SAFE_DEL_EL m2 cL = [e2]))) /\

   (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n pf (hyp_in_precond b m)  =
      (SAFE_DEL_EL m pfL1 = [if b then PF_TURN_EQ pf else pf])) /\

   (HYPOTHESIS_RULE_COND cL pfL1 pfL2 n pf (hyp_in_self b m)  =
      ((m < n) /\ (SAFE_DEL_EL m pfL2 = [if b then PF_TURN_EQ pf else pf])))``,

Cases_on `pf` THEN Cases_on `b` THEN SIMP_TAC std_ss [HYPOTHESIS_RULE_COND_def]);


val HYPOTHESIS_RULE_COND___SEM = store_thm ("HYPOTHESIS_RULE_COND___SEM",
``!s h n cL pfL1 pfL2 c2 hyp_cond pf.
    (HEAP_DISTINCT s h cL c2 /\
     LIST_PF_SEM s pfL1 /\ LIST_PF_SEM s pfL2 /\ n <= LENGTH pfL2 /\
     HYPOTHESIS_RULE_COND cL pfL1 (pfL2++l) n pf hyp_cond) ==>
    (PF_SEM s pf)``,

Cases_on `hyp_cond` THENL [
   SIMP_TAC std_ss [HYPOTHESIS_RULE_COND_THM],

   Cases_on `pf` THEN (
      SIMP_TAC std_ss [HYPOTHESIS_RULE_COND_def]
   ) THEN
   Cases_on `b` THEN (
      SIMP_TAC std_ss [HYPOTHESIS_RULE_COND_def, SAFE_DEL_EL___EQ, PF_SEM_def] THEN
      METIS_TAC[HEAP_DISTINCT___dse_nil, DS_EXPRESSION_EQUAL_def, MEM_EL]
   ),

   Cases_on `pf` THEN
   SIMP_TAC list_ss [HYPOTHESIS_RULE_COND_def, SAFE_DEL_EL___EQ] THEN
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC list_ss [HEAP_DISTINCT_def, EL_ALL_DISTINCT_EQ, EL_MAP] THEN
   `~(DS_EXPRESSION_EVAL_VALUE s (EL n cL) = DS_EXPRESSION_EVAL_VALUE s (EL n0 cL))` by METIS_TAC[] THEN
   `~IS_DSV_NIL (DS_EXPRESSION_EVAL s (EL n cL)) /\ ~IS_DSV_NIL (DS_EXPRESSION_EVAL s (EL n0 cL))` by METIS_TAC[MEM_EL] THEN
   FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_VALUE_def, NOT_IS_DSV_NIL_THM] THEN
   FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, PF_SEM_def, DS_EXPRESSION_EQUAL_def] THEN
   METIS_TAC[],


   SIMP_TAC list_ss [HYPOTHESIS_RULE_COND_THM, SAFE_DEL_EL___EQ] THEN
   REPEAT STRIP_TAC THEN
   METIS_TAC[MEM_LIST_PF_SEM, MEM_EL, PF_TURN_EQ___SEM],


   SIMP_TAC list_ss [HYPOTHESIS_RULE_COND_THM, SAFE_DEL_EL___EQ] THEN
   REPEAT STRIP_TAC THEN
   `n < LENGTH pfL2` by DECIDE_TAC  THEN
   FULL_SIMP_TAC std_ss [EL_APPEND1] THEN
   METIS_TAC[MEM_LIST_PF_SEM, MEM_EL, PF_TURN_EQ___SEM]
])





val HYPOTHESIS_RULE_MAP_def = Define `
   (HYPOTHESIS_RULE_MAP cL pfL1 pfL2 n f [] = []) /\
   (HYPOTHESIS_RULE_MAP cL pfL1 pfL2 n [] l = l) /\
   (HYPOTHESIS_RULE_MAP cL pfL1 pfL2 n (hyp_case::f) (h::l) =
      if HYPOTHESIS_RULE_COND cL pfL1 pfL2 n h hyp_case then
         HYPOTHESIS_RULE_MAP cL pfL1 pfL2 (SUC n) f l
      else
         h::(HYPOTHESIS_RULE_MAP cL pfL1 pfL2 (SUC n) f l)
   )`


val HYPOTHESIS_RULE_MAP_THM = store_thm ("HYPOTHESIS_RULE_MAP_THM",
`` (HYPOTHESIS_RULE_MAP cL pfL1 pfL2 n f [] = []) /\
   (HYPOTHESIS_RULE_MAP cL pfL1 pfL2 n [] l = l) /\
   (HYPOTHESIS_RULE_MAP cL pfL1 pfL2 n (hyp_case::f) (h::l) =
      if HYPOTHESIS_RULE_COND cL pfL1 pfL2 n h hyp_case then
         HYPOTHESIS_RULE_MAP cL pfL1 pfL2 (SUC n) f l
      else
         h::(HYPOTHESIS_RULE_MAP cL pfL1 pfL2 (SUC n) f l)
   )``,

Cases_on `l` THEN SIMP_TAC list_ss [HYPOTHESIS_RULE_MAP_def]);


val HYPOTHESIS_RULE_MAP___SEM1 = prove (
``!s h n cL c2 pfL1 pfL2 f l.
    (HEAP_DISTINCT s h cL c2 /\ LIST_PF_SEM s pfL1 /\ LIST_PF_SEM s pfL2 /\ n <= LENGTH pfL2) ==>

    (LIST_PF_SEM s (HYPOTHESIS_RULE_MAP cL pfL1 (pfL2++l) n f l) =
    LIST_PF_SEM s l)``,



Induct_on `l` THENL [
   SIMP_TAC list_ss [HYPOTHESIS_RULE_MAP_THM],

   Cases_on `f` THEN SIMP_TAC list_ss [HYPOTHESIS_RULE_MAP_def] THEN
   REPEAT STRIP_TAC THEN
   `PF_SEM s h' ==> (LIST_PF_SEM s (HYPOTHESIS_RULE_MAP cL pfL1 (pfL2 ++ h'::l) (SUC n) t l) =
                     LIST_PF_SEM s l)` by (
      `(pfL2 ++ (h'::l)) = ((pfL2 ++ [h']) ++ l)` by (
         SIMP_TAC std_ss [APPEND_11, GSYM APPEND_ASSOC, APPEND]
      ) THEN
      ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      Q.PAT_X_ASSUM `!s n. P s n` MATCH_MP_TAC THEN
      ASM_SIMP_TAC list_ss [LIST_PF_SEM_THM] THEN
      METIS_TAC[]
   ) THEN



   Cases_on `HYPOTHESIS_RULE_COND cL pfL1 (pfL2 ++ h'::l) n h' h ` THENL [
      ASM_SIMP_TAC std_ss [LIST_PF_SEM_THM] THEN
      `PF_SEM s h'` by METIS_TAC[HYPOTHESIS_RULE_COND___SEM] THEN
      ASM_SIMP_TAC std_ss [],

      ASM_SIMP_TAC std_ss [LIST_PF_SEM_THM] THEN
      Cases_on `PF_SEM s h'` THEN ASM_REWRITE_TAC[] THEN
      METIS_TAC[]
   ]
])


val HYPOTHESIS_RULE_MAP___SEM = store_thm ("HYPOTHESIS_RULE_MAP___SEM",
``!s h c1 c2 pfL1 f l.
    HEAP_DISTINCT s h c1 c2 /\ LIST_PF_SEM s pfL1 ==>

    (LIST_PF_SEM s (HYPOTHESIS_RULE_MAP c1 pfL1 l 0 f l) =
    LIST_PF_SEM s l)``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`s`, `h`, `0`, `c1`, `c2`, `pfL1`, `[]`, `f`, `l`] HYPOTHESIS_RULE_MAP___SEM1) THEN
ASM_SIMP_TAC list_ss [LIST_PF_SEM_THM])







val INFERENCE_HYPOTHESIS___EVAL = store_thm ("INFERENCE_HYPOTHESIS___EVAL",
 ``!f1 f2 c1 c2 pfL sfL pfL' sfL'.
         LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL') =
         LIST_DS_ENTAILS (c1,c2) (HYPOTHESIS_RULE_MAP c1 [] pfL 0 f1 pfL,sfL) (HYPOTHESIS_RULE_MAP c1 pfL pfL' 0 f2 pfL',sfL')``,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, HYPOTHESIS_RULE_MAP___SEM,
   LIST_DS_SEM_def, LIST_PF_SEM_THM] THEN
METIS_TAC[HYPOTHESIS_RULE_MAP___SEM, LIST_PF_SEM_THM])






val INFERENCE_STAR_INTRODUCTION___points_to___EVAL = store_thm ("INFERENCE_STAR_INTRODUCTION___points_to___EVAL",
 ``!e n a1 m a2 c1 c2 pfL sfL pfL' sfL'.
         (
         (SAFE_DEL_EL n sfL = [sf_points_to e a1]) /\
         (SAFE_DEL_EL m sfL' = [sf_points_to e a2]) /\
         (EVERY (\x. MEM x a1) a2) /\ ALL_DISTINCT (MAP FST a1)) ==>

         (LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL') =
         LIST_DS_ENTAILS (e::c1,c2) (pfL,DELETE_ELEMENT n sfL) (pfL',DELETE_ELEMENT m sfL'))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n sfL) (pfL',SWAP_TO_POS 0 m sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN
MATCH_MP_TAC (GSYM INFERENCE_STAR_INTRODUCTION___points_to) THEN
FULL_SIMP_TAC std_ss [EVERY_MEM])



val INFERENCE_STAR_INTRODUCTION___list___EVAL = store_thm ("INFERENCE_STAR_INTRODUCTION___list___EVAL",
 ``!f e1 e2 n m c1 c2 pfL sfL pfL' sfL'.
         (
         (SAFE_DEL_EL n sfL = [sf_ls f e1 e2]) /\
         (SAFE_DEL_EL m sfL' = [sf_ls f e1 e2])) ==>

         (LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL') =
         LIST_DS_ENTAILS (c1,(e1,e2)::c2) (pfL,DELETE_ELEMENT n sfL) (pfL',DELETE_ELEMENT m sfL'))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n sfL) (pfL',SWAP_TO_POS 0 m sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN
ASM_REWRITE_TAC [INFERENCE_STAR_INTRODUCTION___list])





val INFERENCE_STAR_INTRODUCTION___bin_tree___EVAL = store_thm ("INFERENCE_STAR_INTRODUCTION___bin_tree___EVAL",
 ``!e f1 f2 f1' f2' n m c1 c2 pfL sfL pfL' sfL'.
         (((f1' = f1) /\ (f2' = f2) \/ (f2' = f1) /\ (f1' = f2)) /\
         (SAFE_DEL_EL n sfL = [sf_bin_tree (f1,f2) e]) /\
         (SAFE_DEL_EL m sfL' = [sf_bin_tree (f1',f2') e])) ==>

         (LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL') =
         LIST_DS_ENTAILS (c1,(e,dse_nil)::c2) (pfL,DELETE_ELEMENT n sfL) (pfL',DELETE_ELEMENT m sfL'))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN (
   `LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
   LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n sfL) (pfL',SWAP_TO_POS 0 m sfL')` by (
      MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
      SIMP_TAC std_ss [PERM_REFL] THEN
      METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
   ) THEN
   ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN
   MATCH_MP_TAC (GSYM INFERENCE_STAR_INTRODUCTION___bin_tree) THEN
   ASM_REWRITE_TAC[]
))





Theorem INFERENCE_STAR_INTRODUCTION___EVAL1:
 !sfL'' c1 c2 pfL sfL pfL' sfL'.
   LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL') ==>
   LIST_DS_ENTAILS (c1,c2) (pfL,sfL++sfL'') (pfL',sfL'++sfL'')
Proof
  REPEAT STRIP_TAC THEN
  ‘LIST_DS_ENTAILS (c1, c2) (pfL,sfL++sfL'') (pfL',sfL'++sfL'') =
   LIST_DS_ENTAILS (c1, c2) (pfL,sfL''++sfL) (pfL',sfL''++sfL')’
    by (MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
        SIMP_TAC std_ss [PERM_REFL, PERM_APPEND]
       ) THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
  Induct_on ‘sfL''’ THENL [
   ASM_SIMP_TAC list_ss [],
   ASM_SIMP_TAC list_ss [INFERENCE_STAR_INTRODUCTION___IMPL]
  ]
QED

val INFERENCE_STAR_INTRODUCTION___EVAL2 = store_thm ("INFERENCE_STAR_INTRODUCTION___EVAL2",
 ``!x n1 n2 c1 c2 pfL sfL pfL' sfL'.
        ((SAFE_DEL_EL n1 sfL = [x]) /\
         (SAFE_DEL_EL n2 sfL' = [x]) /\
         LIST_DS_ENTAILS (c1,c2) (pfL,DELETE_ELEMENT n1 sfL) (pfL',DELETE_ELEMENT n2 sfL')) ==>
         LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL')``,

REPEAT GEN_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n1 sfL) (pfL',SWAP_TO_POS 0 n2 sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
POP_ASSUM (K ALL_TAC) THEN
STRIP_TAC THEN
POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN
METIS_TAC[INFERENCE_STAR_INTRODUCTION___IMPL]);










val SF_POINTS_TO_LIST_def = Define `
   (SF_POINTS_TO_LIST [] = []) /\
   (SF_POINTS_TO_LIST ((sf_points_to e1 e2)::l) = e1::SF_POINTS_TO_LIST l) /\
   (SF_POINTS_TO_LIST (sf::l) = SF_POINTS_TO_LIST l)`




val EL___SF_POINTS_TO_LIST = store_thm ("EL___SF_POINTS_TO_LIST",
``!l n. (n < LENGTH (SF_POINTS_TO_LIST l)) ==>
     ?n' a. (n' < LENGTH l) /\ (n <= n') /\
            (EL n' l = sf_points_to (EL n (SF_POINTS_TO_LIST l)) a)``,

Induct_on `l` THENL [
   SIMP_TAC list_ss [SF_POINTS_TO_LIST_def],

   GEN_TAC THEN
   Cases_on `SF_POINTS_TO_LIST (h::l) = SF_POINTS_TO_LIST l` THEN1 (
         ASM_SIMP_TAC list_ss [] THEN
         REPEAT STRIP_TAC THEN
         RES_TAC THEN
         Q.EXISTS_TAC `SUC n'` THEN
         Q.EXISTS_TAC `a` THEN
         ASM_SIMP_TAC list_ss []
   ) THEN
   Cases_on `h` THEN FULL_SIMP_TAC list_ss [SF_POINTS_TO_LIST_def] THEN
   REPEAT STRIP_TAC THEN
   Cases_on `n` THENL [
      FULL_SIMP_TAC std_ss [] THEN
      Q.EXISTS_TAC `0` THEN
      SIMP_TAC list_ss [] THEN
      METIS_TAC[],

      FULL_SIMP_TAC list_ss [] THEN
      RES_TAC THEN
      Q.EXISTS_TAC `SUC n''` THEN
      Q.EXISTS_TAC `a` THEN
      ASM_SIMP_TAC list_ss []
   ]
])



val EL2___SF_POINTS_TO_LIST = store_thm ("EL2___SF_POINTS_TO_LIST",

``!l n m. ((m < LENGTH (SF_POINTS_TO_LIST l)) /\ (n < m)) ==>
     ?n' m' e e'. (m' < LENGTH l) /\ (n <= n') /\ (m <= m') /\
                  (n' < m') /\ (EL n' l = sf_points_to (EL n (SF_POINTS_TO_LIST l)) e) /\
                  (EL m' l = sf_points_to (EL m (SF_POINTS_TO_LIST l)) e')``,

Induct_on `l` THENL [
   SIMP_TAC list_ss [SF_POINTS_TO_LIST_def],

   GEN_TAC THEN
   Cases_on `SF_POINTS_TO_LIST (h::l) = SF_POINTS_TO_LIST l` THEN1 (
         ASM_SIMP_TAC list_ss [] THEN
         REPEAT STRIP_TAC THEN
         Q.PAT_X_ASSUM `!n m. P n m` (fn thm => MP_TAC (Q.ISPECL [`n:num`, `m:num`] thm)) THEN
         ASM_SIMP_TAC std_ss [] THEN
         STRIP_TAC THEN
         Q.EXISTS_TAC `SUC n'` THEN
         Q.EXISTS_TAC `SUC m'` THEN
         Q.EXISTS_TAC `e` THEN
         Q.EXISTS_TAC `e'` THEN
         ASM_SIMP_TAC list_ss []
   ) THEN
   Cases_on `h` THEN FULL_SIMP_TAC std_ss [SF_POINTS_TO_LIST_def] THEN
   POP_ASSUM (fn thm => ALL_TAC) THEN
   ASM_SIMP_TAC list_ss [] THEN
   REPEAT STRIP_TAC THEN
   Cases_on `m` THEN1 FULL_SIMP_TAC std_ss [] THEN
   Cases_on `n` THENL [
      FULL_SIMP_TAC std_ss [] THEN
      `?n'' e.
           n'' < LENGTH l /\ n' <= n'' /\
           (EL n'' l = sf_points_to (EL n' (SF_POINTS_TO_LIST l)) e)` by
         METIS_TAC [EL___SF_POINTS_TO_LIST] THEN
      Q.EXISTS_TAC `0` THEN
      Q.EXISTS_TAC `SUC n''` THEN
      ASM_SIMP_TAC list_ss [] THEN
      METIS_TAC[],


      FULL_SIMP_TAC list_ss [] THEN
      Q.PAT_X_ASSUM `!n m. P n m` (fn thm => MP_TAC (Q.ISPECL [`n'':num`, `n':num`] thm)) THEN
      ASM_SIMP_TAC list_ss [] THEN
      STRIP_TAC THEN
      Q.EXISTS_TAC `SUC n'''` THEN
      Q.EXISTS_TAC `SUC m'` THEN
      Q.EXISTS_TAC `e` THEN
      Q.EXISTS_TAC `e'` THEN
      ASM_SIMP_TAC list_ss []
   ]
]);











val _ = Hol_datatype `pointsto_cases =
     pointsto_skip
   | pointsto_pointsto
   | pointsto_tree of bool => num`

val SF_POINTS_TO_LIST_COND_def = Define `
   (SF_POINTS_TO_LIST_COND pfL pointsto_skip h = []) /\
   (SF_POINTS_TO_LIST_COND pfL pointsto_pointsto (sf_points_to e a) = [e]) /\
   (SF_POINTS_TO_LIST_COND pfL pointsto_pointsto (_) = []) /\
   (SF_POINTS_TO_LIST_COND pfL (pointsto_tree turn n) (sf_tree fL es e) =
   if (SAFE_DEL_EL n pfL = [if turn then pf_unequal es e else pf_unequal e es]) then [e] else []) /\
   (SF_POINTS_TO_LIST_COND pfL (pointsto_tree turn n) _ = [])`

val SF_POINTS_TO_LIST_COND_THM = store_thm ("SF_POINTS_TO_LIST_COND_THM",
``(SF_POINTS_TO_LIST_COND pfL pointsto_skip h = []) /\
   (SF_POINTS_TO_LIST_COND pfL pointsto_pointsto (sf_points_to e a) = [e]) /\
   (SF_POINTS_TO_LIST_COND pfL (pointsto_tree T n) (sf_tree fL es e) =
   if (SAFE_DEL_EL n pfL = [pf_unequal es e]) then [e] else []) /\
   (SF_POINTS_TO_LIST_COND pfL (pointsto_tree F n) (sf_tree fL es e) =
   if (SAFE_DEL_EL n pfL = [pf_unequal e es]) then [e] else []) /\
   (SF_POINTS_TO_LIST_COND pfL (pointsto_tree T n) (sf_ls f e1 e2) =
   if (SAFE_DEL_EL n pfL = [pf_unequal e2 e1]) then [e1] else []) /\
   (SF_POINTS_TO_LIST_COND pfL (pointsto_tree F n) (sf_ls f e1 e2) =
   if (SAFE_DEL_EL n pfL = [pf_unequal e1 e2]) then [e1] else []) /\

   (SF_POINTS_TO_LIST_COND pfL (pointsto_tree T n) (sf_bin_tree (f1,f2) e) =
   if (SAFE_DEL_EL n pfL = [pf_unequal dse_nil e]) then [e] else []) /\
   (SF_POINTS_TO_LIST_COND pfL (pointsto_tree F n) (sf_bin_tree (f1,f2) e) =
   if (SAFE_DEL_EL n pfL = [pf_unequal e dse_nil]) then [e] else [])``,

SIMP_TAC std_ss [SF_POINTS_TO_LIST_COND_def, sf_ls_def, sf_bin_tree_def])




val SF_POINTS_TO_LIST_COND_FILTER_def = Define `
   (SF_POINTS_TO_LIST_COND_FILTER pfL f [] = []) /\
   (SF_POINTS_TO_LIST_COND_FILTER pfL [] l = []) /\
   (SF_POINTS_TO_LIST_COND_FILTER pfL (pointsto_case::f) (h::l) =
      (SF_POINTS_TO_LIST_COND pfL pointsto_case h)++
      (SF_POINTS_TO_LIST_COND_FILTER pfL f l))`





val SF_POINTS_TO_LIST_COND___PRED_def = Define `
   SF_POINTS_TO_LIST_COND___PRED pfL e1 e2 =
((?a. (e2 = sf_points_to e1 a)) \/
 ((?es b fL m.
      (m < LENGTH pfL) /\
      (EL m pfL = (if b then (pf_unequal es e1) else (pf_unequal e1 es))) /\
      (e2 = sf_tree fL es e1))))`;



val SF_POINTS_TO_LIST_COND___PRED___WEAKEN = store_thm ("SF_POINTS_TO_LIST_COND___PRED___WEAKEN",
   ``!pfL1 pfL2 e1 e2. ((!x. MEM x pfL1 ==> MEM x pfL2) /\
                       SF_POINTS_TO_LIST_COND___PRED pfL1 e1 e2) ==>
                       SF_POINTS_TO_LIST_COND___PRED (pfL2) e1 e2``,

SIMP_TAC std_ss [SF_POINTS_TO_LIST_COND___PRED_def] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [ds_spatial_formula_11, ds_spatial_formula_distinct] THEN
METIS_TAC[MEM_EL]);



val EL___SF_POINTS_TO_LIST_COND_FILTER = store_thm ("EL___SF_POINTS_TO_LIST_COND_FILTER",
``!l pfL f n. (n < LENGTH (SF_POINTS_TO_LIST_COND_FILTER pfL f l)) ==>
     (?n'. (n' < LENGTH l) /\ (n <= n') /\
           SF_POINTS_TO_LIST_COND___PRED pfL (EL n (SF_POINTS_TO_LIST_COND_FILTER pfL f l)) (EL n' l))``,

Induct_on `l` THENL [
   Cases_on `f` THEN
   SIMP_TAC list_ss [SF_POINTS_TO_LIST_COND_FILTER_def],

   REPEAT GEN_TAC THEN
   Cases_on `f` THEN1 SIMP_TAC list_ss [SF_POINTS_TO_LIST_COND_FILTER_def] THEN

   Cases_on `(SF_POINTS_TO_LIST_COND_FILTER pfL (h'::t) (h::l)) =
             (SF_POINTS_TO_LIST_COND_FILTER pfL t l)` THEN1 (
      ASM_SIMP_TAC list_ss [] THEN
      REPEAT STRIP_TAC THEN
      RES_TAC THEN
      Q.EXISTS_TAC `SUC n'` THEN
      ASM_SIMP_TAC list_ss []
   ) THEN
   `?x. (SF_POINTS_TO_LIST_COND_FILTER pfL (h'::t) (h::l)) =
    x::(SF_POINTS_TO_LIST_COND_FILTER pfL t l)` by (
      Cases_on `h` THEN
      Cases_on `h'` THEN
      FULL_SIMP_TAC list_ss [SF_POINTS_TO_LIST_COND_FILTER_def, SF_POINTS_TO_LIST_COND_def,
         COND_RATOR, COND_RAND]
   ) THEN
   FULL_SIMP_TAC list_ss [] THEN
   STRIP_TAC THEN
   Tactical.REVERSE (Cases_on `n`) THEN1 (
      FULL_SIMP_TAC std_ss [] THEN
      RES_TAC THEN
      Q.EXISTS_TAC `SUC n''` THEN
      ASM_SIMP_TAC list_ss []
   ) THEN
   FULL_SIMP_TAC list_ss [] THEN

   Q.EXISTS_TAC `0` THEN
   SIMP_TAC list_ss [SF_POINTS_TO_LIST_COND___PRED_def] THEN
   Cases_on `h'` THEN Cases_on `h` THEN (
      FULL_SIMP_TAC list_ss [SF_POINTS_TO_LIST_COND_FILTER_def, SF_POINTS_TO_LIST_COND_def,
         ds_spatial_formula_11, ds_spatial_formula_distinct]
   ) THEN
   Cases_on `SAFE_DEL_EL n pfL = [(if b then pf_unequal d d0 else pf_unequal d0 d)]` THEN FULL_SIMP_TAC list_ss [] THEN
   FULL_SIMP_TAC list_ss [SAFE_DEL_EL___EQ] THEN
   METIS_TAC[]
])



val EL2___SF_POINTS_TO_LIST_COND_FILTER = store_thm ("EL2___SF_POINTS_TO_LIST_COND_FILTER",

``!l pfL f n m. ((m < LENGTH (SF_POINTS_TO_LIST_COND_FILTER pfL f l)) /\ (n < m)) ==>
     ?n' m'. (m' < LENGTH l) /\ (n <= n') /\ (m <= m') /\
             (n' < m') /\
             SF_POINTS_TO_LIST_COND___PRED pfL (EL n (SF_POINTS_TO_LIST_COND_FILTER pfL f l)) (EL n' l) /\
             SF_POINTS_TO_LIST_COND___PRED pfL (EL m (SF_POINTS_TO_LIST_COND_FILTER pfL f l)) (EL m' l)``,


Induct_on `l` THENL [
   Cases_on `f` THEN
   SIMP_TAC list_ss [SF_POINTS_TO_LIST_COND_FILTER_def],

   REPEAT GEN_TAC THEN
   Cases_on `f` THEN1 SIMP_TAC list_ss [SF_POINTS_TO_LIST_COND_FILTER_def] THEN
   Cases_on `(SF_POINTS_TO_LIST_COND_FILTER pfL (h'::t) (h::l)) =
             (SF_POINTS_TO_LIST_COND_FILTER pfL t l)` THEN1 (
      ASM_SIMP_TAC list_ss [] THEN
      REPEAT STRIP_TAC THEN
      Q.PAT_X_ASSUM `!pfL f n m. P n m` (fn thm => MP_TAC (Q.SPECL [`pfL`, `t`, `n:num`, `m:num`] thm)) THEN
      ASM_REWRITE_TAC [] THEN
      STRIP_TAC THEN
      Q.EXISTS_TAC `SUC n'` THEN
      Q.EXISTS_TAC `SUC m'` THEN
      ASM_SIMP_TAC list_ss []
   ) THEN
   `?x. (SF_POINTS_TO_LIST_COND_FILTER pfL (h'::t) (h::l)) =
    x::(SF_POINTS_TO_LIST_COND_FILTER pfL t l)` by (
      Cases_on `h` THEN
      Cases_on `h'` THEN
      FULL_SIMP_TAC list_ss [SF_POINTS_TO_LIST_COND_FILTER_def, SF_POINTS_TO_LIST_COND_def,
         COND_RATOR, COND_RAND]
   ) THEN
   FULL_SIMP_TAC list_ss [] THEN
   Cases_on `m` THEN1 FULL_SIMP_TAC std_ss [] THEN
   Cases_on `n` THENL [
      FULL_SIMP_TAC list_ss [] THEN
      STRIP_TAC THEN
      MP_TAC (Q.SPECL [`h::l`, `pfL`, `h'::t`, `SUC n'`] EL___SF_POINTS_TO_LIST_COND_FILTER) THEN
      ASM_SIMP_TAC list_ss [] THEN
      STRIP_TAC THEN
      Q.EXISTS_TAC `0` THEN
      Q.EXISTS_TAC `n''` THEN
      ASM_SIMP_TAC list_ss [] THEN

      Q.PAT_X_ASSUM `Y = x::Z` MP_TAC THEN
      Cases_on `h'` THEN Cases_on `h` THEN (
         SIMP_TAC list_ss [SF_POINTS_TO_LIST_COND___PRED_def, SF_POINTS_TO_LIST_COND_FILTER_def,
            SF_POINTS_TO_LIST_COND_def, ds_spatial_formula_11, ds_spatial_formula_distinct]
      ) THEN
      SIMP_TAC list_ss [COND_RATOR, COND_RAND, SAFE_DEL_EL___EQ] THEN
      METIS_TAC[],


      SIMP_TAC std_ss [] THEN
      STRIP_TAC THEN
      Q.PAT_X_ASSUM `!pfL f n m. P n m` (fn thm => MP_TAC (Q.SPECL [`pfL`, `t`, `n'':num`, `n':num`] thm)) THEN
      ASM_SIMP_TAC list_ss [] THEN
      STRIP_TAC THEN
      Q.EXISTS_TAC `SUC n'''` THEN
      Q.EXISTS_TAC `SUC m'` THEN
      ASM_SIMP_TAC list_ss []
   ]
]);













val INFERENCE_NIL_NOT_LVAL___EVAL_NIL1 = prove (

``!l c1 c2 pfL sfL pfL' sfL'.
         (!x. MEM x l ==> ?y. SF_POINTS_TO_LIST_COND___PRED pfL x y /\  MEM y sfL) ==>

         (LIST_DS_ENTAILS (c1, c2)
           (MAP (\e. pf_unequal e dse_nil) l ++ pfL,sfL)
           (pfL',sfL') =
         LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL'))``,


NTAC 7 GEN_TAC THEN
Induct_on `l` THENL [
   SIMP_TAC list_ss [SAFE_FILTER_THM],

   SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC list_ss [] THEN
   Q.PAT_X_ASSUM `Y = LIST_DS_ENTAILS (c1,c2) (pfL, sfL) (pfL', sfL')`
      (fn thm => (ASSUME_TAC (GSYM thm))) THEN
   FULL_SIMP_TAC std_ss [MEM_EL] THEN
   Q.PAT_X_ASSUM `Y = EL n sfL` (ASSUME_TAC o GSYM) THEN

   `!pfL. LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
         LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n sfL) (pfL',sfL')` by (
      GEN_TAC THEN
      MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
      SIMP_TAC std_ss [PERM_REFL] THEN
      METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
   ) THEN
   FULL_SIMP_TAC std_ss [SF_POINTS_TO_LIST_COND___PRED_def, SWAP_TO_POS___DELETE_ELEMENT] THENL [
      ASM_SIMP_TAC list_ss [INFERENCE_NIL_NOT_LVAL___points_to],


      MATCH_MP_TAC INFERENCE_NIL_NOT_LVAL___tree THEN
      SIMP_TAC list_ss [MEM_UNEQ_PF_LIST_def] THEN
      METIS_TAC[MEM_EL]
   ]
])



val INFERENCE_NIL_NOT_LVAL___EVAL = store_thm ("INFERENCE_NIL_NOT_LVAL___EVAL",
``!f c1 c2 pfL sfL pfL' sfL'.
         LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
         (LIST_DS_ENTAILS (c1, c2)
           ((MAP (\e. pf_unequal e dse_nil) (SF_POINTS_TO_LIST_COND_FILTER pfL f sfL)) ++ pfL,sfL)
           (pfL',sfL'))``,

REPEAT GEN_TAC THEN
MATCH_MP_TAC (GSYM INFERENCE_NIL_NOT_LVAL___EVAL_NIL1) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [MEM_EL] THEN
METIS_TAC[EL___SF_POINTS_TO_LIST_COND_FILTER]);






val DISJOINT_LIST_PRODUCT_def = Define `
   (DISJOINT_LIST_PRODUCT [] = []) /\
   (DISJOINT_LIST_PRODUCT (e::l) =
      (MAP (\x. (e, x)) l)++(DISJOINT_LIST_PRODUCT l))`;

val MEM___DISJOINT_LIST_PRODUCT = store_thm ("MEM___DISJOINT_LIST_PRODUCT",
   ``!e1 e2. (MEM (e1, e2) (DISJOINT_LIST_PRODUCT l) =
      ?n m. (n < m) /\ (m < LENGTH l) /\
            (e1 = EL n l) /\ (e2 = EL m l))``,

Induct_on `l` THENL [
   SIMP_TAC list_ss [DISJOINT_LIST_PRODUCT_def],

   ASM_SIMP_TAC list_ss [DISJOINT_LIST_PRODUCT_def, MEM_MAP] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THENL [
      REPEAT STRIP_TAC THENL [
         FULL_SIMP_TAC std_ss [MEM_EL] THEN
         Q.EXISTS_TAC `0` THEN
         Q.EXISTS_TAC `SUC n` THEN
         ASM_SIMP_TAC list_ss [],

         Q.EXISTS_TAC `SUC n` THEN
         Q.EXISTS_TAC `SUC m` THEN
         ASM_SIMP_TAC list_ss []
      ],

      STRIP_TAC THEN
      Cases_on `m` THEN1 FULL_SIMP_TAC std_ss [] THEN
      Cases_on `n` THENL [
         DISJ1_TAC THEN
         FULL_SIMP_TAC list_ss [MEM_EL] THEN
         METIS_TAC[],

         DISJ2_TAC THEN
         FULL_SIMP_TAC list_ss [] THEN
         METIS_TAC[]
      ]
   ]
])



val LIST_PRODUCT_def = Define `
   (LIST_PRODUCT [] l2 = []) /\
   (LIST_PRODUCT (e::l1) l2 =
      (MAP (\x. (e, x)) l2)++(LIST_PRODUCT l1 l2))`;

val MEM___LIST_PRODUCT = store_thm ("MEM___LIST_PRODUCT",
   ``!l1 l2 e1 e2. (MEM (e1, e2) (LIST_PRODUCT l1 l2) =
      (MEM e1 l1 /\ MEM e2 l2))``,

Induct_on `l1` THENL [
   SIMP_TAC list_ss [LIST_PRODUCT_def],

   ASM_SIMP_TAC list_ss [LIST_PRODUCT_def, MEM_MAP] THEN
   METIS_TAC[]
]);




val PERM___TWO_ELEMENTS_TO_FRONT_1 = store_thm ("PERM___TWO_ELEMENTS_TO_FRONT_1",
``!n1 n2. ((n1 < n2) /\ n2 < LENGTH l) ==>
PERM (EL n1 l::EL n2 l::(DELETE_ELEMENT n1 (DELETE_ELEMENT n2 l))) l``,


REPEAT STRIP_TAC THEN
Cases_on `n2` THEN1 FULL_SIMP_TAC arith_ss [] THEN
`!l'. PERM l' l = PERM l' (SWAP_TO_POS (SUC 0) (SUC n) (SWAP_TO_POS 0 n1 l))` by
   METIS_TAC[PERM_TRANS, PERM_SYM, PERM___SWAP_TO_POS] THEN
ASM_REWRITE_TAC[] THEN
MATCH_MP_TAC (prove (``(l = l') ==> PERM l l'``, SIMP_TAC std_ss [PERM_REFL])) THEN

`LENGTH (SWAP_TO_POS (SUC 0) (SUC n) l) = LENGTH l` by METIS_TAC[PERM___SWAP_TO_POS, PERM_LENGTH] THEN
`n1 < LENGTH l` by DECIDE_TAC THEN
ASM_SIMP_TAC bool_ss [SWAP_TO_POS___DELETE_ELEMENT, SWAP_TO_POS_THM] THEN

`n < LENGTH (DELETE_ELEMENT n1 l)` by ASM_SIMP_TAC list_ss [LENGTH_DELETE_ELEMENT] THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN
`~(n < n1)` by DECIDE_TAC THEN
`n < LENGTH l` by DECIDE_TAC THEN
ASM_SIMP_TAC list_ss [EL_DELETE_ELEMENT] THEN
`n1 <= n` by DECIDE_TAC THEN
ASM_SIMP_TAC std_ss [GSYM DELETE_ELEMENT_DELETE_ELEMENT])



val PERM___TWO_ELEMENTS_TO_FRONT_2 = store_thm ("PERM___TWO_ELEMENTS_TO_FRONT_2",
``!n1 n2. ((n2 < n1) /\ n1 < LENGTH l) ==>
PERM (EL n1 l::EL n2 l::(DELETE_ELEMENT n2 (DELETE_ELEMENT n1 l))) l``,

REPEAT STRIP_TAC THEN
`!l'. PERM l' l =
      PERM l' (EL n2 l::EL n1 l::DELETE_ELEMENT n2 (DELETE_ELEMENT n1 l))` by
   METIS_TAC[PERM_SYM, PERM___TWO_ELEMENTS_TO_FRONT_1, PERM_TRANS, PERM_REFL] THEN
ASM_SIMP_TAC std_ss [PERM_SWAP_AT_FRONT, PERM_REFL]);



val PERM___TWO_ELEMENTS_TO_FRONT_3 = store_thm ("PERM___TWO_ELEMENTS_TO_FRONT_3",
``!n1 n2. (~(n1 = n2) /\ n1 < LENGTH l /\ n2 < LENGTH l) ==>
?l'. (PERM (EL n1 l::EL n2 l::l') l) /\
     (PERM (EL n2 l::l') (DELETE_ELEMENT n1 l))``,

REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC (prove (``((?l. P l) /\ (!l. P l ==> Q l)) ==> (?l. P l /\ Q l)``, METIS_TAC[])) THEN
CONJ_TAC THEN1 (
   `(n1 < n2) \/ (n2 < n1)` by DECIDE_TAC THENL [
      METIS_TAC[PERM___TWO_ELEMENTS_TO_FRONT_1],
      METIS_TAC[PERM___TWO_ELEMENTS_TO_FRONT_2]
   ]
) THEN
REPEAT STRIP_TAC THEN
`PERM (EL n1 l::EL n2 l::l') (SWAP_TO_POS 0 n1 l)` by METIS_TAC[PERM_TRANS, PERM___SWAP_TO_POS, PERM_SYM] THEN
POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT, PERM_CONS_IFF]
);


val INFERENCE_PARTIAL___EVAL1 = prove (

``!l c1 c2 pfL sfL pfL' sfL'.
         (!e1 e2. MEM (e1,e2) l ==>
          (?n1 n2 y1 y2. (n1 < n2) /\
                  SF_POINTS_TO_LIST_COND___PRED pfL e1 y1 /\
                  SF_POINTS_TO_LIST_COND___PRED pfL e2 y2 /\
                  (SAFE_DEL_EL n1 sfL = [y1]) /\
                  (SAFE_DEL_EL n2 sfL = [y2]))) ==>

         (LIST_DS_ENTAILS (c1, c2)
           ((MAP (\(e1,e2). pf_unequal e1 e2) l) ++ pfL,sfL)
           (pfL',sfL') =
         LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL'))``,

REPEAT GEN_TAC THEN
Induct_on `l` THENL [
   SIMP_TAC list_ss [],

   SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
   Cases_on `h` THEN
   SIMP_TAC list_ss [] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_X_ASSUM `Y ==> (X = Z)` MP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC std_ss [Once EQ_SYM_EQ] THEN
   STRIP_TAC THEN
   `?sfL''. PERM (y1::y2::sfL'') sfL` by (
      FULL_SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
      METIS_TAC[PERM___TWO_ELEMENTS_TO_FRONT_1]
   ) THEN
   `!pfL.
      LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
      LIST_DS_ENTAILS (c1, c2) (pfL,y1::y2::sfL'') (pfL',sfL')` by (
      GEN_TAC THEN
      MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
      ASM_SIMP_TAC std_ss [PERM_REFL] THEN
      METIS_TAC[PERM_SYM]
   ) THEN
   ASM_SIMP_TAC std_ss [] THEN

   FULL_SIMP_TAC std_ss [SF_POINTS_TO_LIST_COND___PRED_def] THENL [
      REWRITE_TAC [INFERENCE_PARTIAL___points_to___points_to],

      MATCH_MP_TAC INFERENCE_PARTIAL___points_to___tree THEN
      SIMP_TAC list_ss [MEM_UNEQ_PF_LIST_def] THEN
      METIS_TAC[MEM_EL],


      `!pfL.
         LIST_DS_ENTAILS (c1, c2) (pfL,sf_tree fL es q::sf_points_to r a::sfL'') (pfL',sfL') =
         LIST_DS_ENTAILS (c1, c2) (pfL,sf_points_to r a::sf_tree fL es q::sfL'') (pfL',sfL')` by (
         GEN_TAC THEN
         MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
         SIMP_TAC std_ss [PERM_REFL, PERM_SWAP_AT_FRONT]
      ) THEN
      `!pfL sfL. LIST_DS_ENTAILS (c1,c2) (pf_unequal q r::pfL, sfL) (pfL', sfL') =
                 LIST_DS_ENTAILS (c1,c2) (pf_unequal r q::pfL, sfL) (pfL', sfL')` by (
         SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_EVAL, DS_EXPRESSION_EQUAL_def] THEN
         METIS_TAC[]
      ) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INFERENCE_PARTIAL___points_to___tree THEN
      SIMP_TAC list_ss [MEM_UNEQ_PF_LIST_def] THEN
      METIS_TAC[MEM_EL],


      MATCH_MP_TAC INFERENCE_PARTIAL___tree___tree THEN
      SIMP_TAC list_ss [MEM_UNEQ_PF_LIST_def] THEN
      METIS_TAC[MEM_EL]
   ]
])





val INFERENCE_PARTIAL___EVAL2 = prove (

``!f f2 c1 c2 pfL sfL pfL' sfL'.
         (LIST_DS_ENTAILS (c1, c2)
           ((MAP (\(e1,e2). pf_unequal e1 e2) (SAFE_FILTER F f (DISJOINT_LIST_PRODUCT (SF_POINTS_TO_LIST_COND_FILTER pfL f2 sfL)))) ++ (pfL),sfL)
           (pfL',sfL') =
         LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL'))``,



REPEAT GEN_TAC THEN
MATCH_MP_TAC INFERENCE_PARTIAL___EVAL1 THEN
REPEAT STRIP_TAC THEN
`MEM (e1,e2) (DISJOINT_LIST_PRODUCT (SF_POINTS_TO_LIST_COND_FILTER pfL f2 sfL))` by METIS_TAC[MEM_SAFE_FILTER] THEN
FULL_SIMP_TAC std_ss [MEM___DISJOINT_LIST_PRODUCT, SAFE_DEL_EL___EQ] THEN
MP_TAC (ISPECL [``sfL:('c, 'b, 'a) ds_spatial_formula list``,``pfL:('b, 'a) ds_pure_formula list``, ``f2:pointsto_cases list``, ``n:num``, ``m:num``] EL2___SF_POINTS_TO_LIST_COND_FILTER) THEN
ASM_REWRITE_TAC[] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `n'` THEN
Q.EXISTS_TAC `m'` THEN
ASM_SIMP_TAC arith_ss [])





val INFERENCE_PARTIAL___EVAL3 = prove (

``!l c1 c2 pfL sfL pfL' sfL'.
         (!e1 e2. MEM (e1,e2) l ==>
          (?n1 n2 y1.
                  SF_POINTS_TO_LIST_COND___PRED pfL e1 y1 /\
                  (SAFE_DEL_EL n1 sfL = [y1]) /\
                  (SAFE_DEL_EL n2 c1 = [e2]))) ==>

         (LIST_DS_ENTAILS (c1, c2)
           ((MAP (\(e1,e2). pf_unequal e1 e2) l) ++ pfL,sfL)
           (pfL',sfL') =
         LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL'))``,

REPEAT GEN_TAC THEN
Induct_on `l` THENL [
   SIMP_TAC list_ss [],

   SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
   Cases_on `h` THEN
   SIMP_TAC list_ss [] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_X_ASSUM `Y ==> (X = Z)` MP_TAC THEN
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC std_ss [Once EQ_SYM_EQ] THEN
   STRIP_TAC THEN
   `!pfL.
      LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
      LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n1 sfL) (pfL',sfL')` by (
      GEN_TAC THEN
      MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
      SIMP_TAC std_ss [PERM_REFL] THEN
      METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
   ) THEN
   FULL_SIMP_TAC std_ss [SAFE_DEL_EL___EQ, SWAP_TO_POS___DELETE_ELEMENT] THEN
   `MEM r c1` by METIS_TAC[MEM_EL] THEN

   FULL_SIMP_TAC std_ss [SF_POINTS_TO_LIST_COND___PRED_def] THENL [
      ASM_SIMP_TAC std_ss [INFERENCE_PARTIAL___precondition___points_to],

      MATCH_MP_TAC INFERENCE_PARTIAL___precondition___tree THEN
      ASM_SIMP_TAC list_ss [MEM_UNEQ_PF_LIST_def] THEN
      METIS_TAC[MEM_EL]
   ]
])



val INFERENCE_PARTIAL___EVAL4 = prove (

``!f f2 c1 c2 pfL1 pfL sfL pfL' sfL'.
         (LIST_DS_ENTAILS (c1, c2)
           ((MAP (\(e1,e2). pf_unequal e1 e2) (SAFE_FILTER F f (LIST_PRODUCT (SF_POINTS_TO_LIST_COND_FILTER pfL f2 sfL) c1))) ++ (pfL1++pfL),sfL)
           (pfL',sfL') =
         LIST_DS_ENTAILS (c1, c2) (pfL1++pfL,sfL) (pfL',sfL'))``,



REPEAT GEN_TAC THEN
MATCH_MP_TAC INFERENCE_PARTIAL___EVAL3 THEN
REPEAT STRIP_TAC THEN
`MEM (e1,e2) (LIST_PRODUCT (SF_POINTS_TO_LIST_COND_FILTER pfL f2 sfL) c1)` by METIS_TAC[MEM_SAFE_FILTER] THEN
FULL_SIMP_TAC std_ss [MEM___LIST_PRODUCT, SAFE_DEL_EL___EQ] THEN
FULL_SIMP_TAC std_ss [MEM_EL] THEN
`!x. MEM x pfL ==> MEM x (pfL1 ++ pfL)` by SIMP_TAC list_ss [] THEN
METIS_TAC[EL___SF_POINTS_TO_LIST_COND_FILTER, SF_POINTS_TO_LIST_COND___PRED___WEAKEN])



val INFERENCE_PARTIAL___EVAL = store_thm ("INFERENCE_PARTIAL___EVAL",

``!f f2 c1 c2 pfL sfL pfL' sfL'.
         LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
         (LIST_DS_ENTAILS (c1, c2)
           ((MAP (\(e1,e2). pf_unequal e1 e2) (SAFE_FILTER F f
               ((LIST_PRODUCT (SF_POINTS_TO_LIST_COND_FILTER pfL f2 sfL) c1) ++ (DISJOINT_LIST_PRODUCT (SF_POINTS_TO_LIST_COND_FILTER pfL f2 sfL))))) ++ pfL,sfL)
           (pfL',sfL'))``,

SIMP_TAC list_ss [SAFE_FILTER_APPEND] THEN
REPEAT STRIP_TAC THEN
REWRITE_TAC [GSYM APPEND_ASSOC] THEN
REWRITE_TAC [INFERENCE_PARTIAL___EVAL4] THEN
REWRITE_TAC [INFERENCE_PARTIAL___EVAL2]);







val INFERENCE___precondition_STRENGTHEN_1 = store_thm ("INFERENCE___precondition_STRENGTHEN_1",
``!n1 n2 e1 e2 c1 c2 pfL sfL pfL' sfL'.
         ((SAFE_DEL_EL n1 pfL = [pf_unequal e1 e2]) /\
          (SAFE_DEL_EL n2 c2 = [(e1,e2)])) ==>

         (LIST_DS_ENTAILS (c1, c2) (pfL, sfL) (pfL', sfL') =
          LIST_DS_ENTAILS (e1::c1, DELETE_ELEMENT n2 c2) (pfL, sfL) (pfL', sfL'))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ, LIST_DS_ENTAILS_def] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC (prove (``(!s h. P s h = Q s h) ==> ((!s h. P s h) = (!s h. Q s h))``, METIS_TAC[])) THEN
REPEAT STRIP_TAC THEN
Cases_on `LIST_DS_SEM s h (pfL,sfL)` THEN ASM_REWRITE_TAC[] THEN
Cases_on `LIST_DS_SEM s h (pfL',sfL')` THEN ASM_REWRITE_TAC[] THEN

REPEAT STRIP_TAC THEN
`(HEAP_DISTINCT s h c1 c2) =
 (HEAP_DISTINCT s h c1 (SWAP_TO_POS 0 n2 c2))` by (
   MATCH_MP_TAC HEAP_DISTINCT___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN
MATCH_MP_TAC HEAP_DISTINCT___UNEQUAL THEN
`PF_SEM s (pf_unequal e1 e2)` by METIS_TAC[MEM_LIST_PF_SEM, MEM_EL, LIST_DS_SEM_def] THEN
FULL_SIMP_TAC std_ss [PF_SEM_def])




val INFERENCE___precondition_STRENGTHEN_2 = store_thm ("INFERENCE___precondition_STRENGTHEN_2",
``!n1 n2 e1 e2 c1 c2 pfL sfL pfL' sfL'.
         ((SAFE_DEL_EL n1 pfL = [pf_unequal e2 e1]) /\
          (SAFE_DEL_EL n2 c2 = [(e1,e2)])) ==>

         (LIST_DS_ENTAILS (c1, c2) (pfL, sfL) (pfL', sfL') =
          LIST_DS_ENTAILS (e1::c1, DELETE_ELEMENT n2 c2) (pfL, sfL) (pfL', sfL'))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ, LIST_DS_ENTAILS_def] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC (prove (``(!s h. P s h = Q s h) ==> ((!s h. P s h) = (!s h. Q s h))``, METIS_TAC[])) THEN
REPEAT STRIP_TAC THEN
Cases_on `LIST_DS_SEM s h (pfL,sfL)` THEN ASM_REWRITE_TAC[] THEN
Cases_on `LIST_DS_SEM s h (pfL',sfL')` THEN ASM_REWRITE_TAC[] THEN

REPEAT STRIP_TAC THEN
`(HEAP_DISTINCT s h c1 c2) =
 (HEAP_DISTINCT s h c1 (SWAP_TO_POS 0 n2 c2))` by (
   MATCH_MP_TAC HEAP_DISTINCT___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN
MATCH_MP_TAC HEAP_DISTINCT___UNEQUAL THEN
`PF_SEM s (pf_unequal e2 e1)` by METIS_TAC[MEM_LIST_PF_SEM, MEM_EL, LIST_DS_SEM_def] THEN
FULL_SIMP_TAC std_ss [PF_SEM_def, DS_EXPRESSION_EQUAL_def])




val INFERENCE___precondition_NOT_DISTINCT_EQ___EVAL = store_thm ("INFERENCE___precondition_NOT_DISTINCT_EQ___EVAL",
``!n1 n2 e1 e2 c1 c2 pfL sfL pfL' sfL'.
         ((n1 < n2) /\ (SAFE_DEL_EL n1 c2 = [(e1,e2)]) /\
          (SAFE_DEL_EL n2 c2 = [(e1,e2)])) ==>

         (LIST_DS_ENTAILS (c1, c2) (pfL, sfL) (pfL', sfL') =
          LIST_DS_ENTAILS (c1, DELETE_ELEMENT n1 (DELETE_ELEMENT n2 c2)) (pf_equal e1 e2::pfL, sfL) (pfL', sfL'))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ, LIST_DS_ENTAILS_def, LIST_DS_SEM_THM, PF_SEM_def] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC (prove (``(!s h. P s h = Q s h) ==> ((!s h. P s h) = (!s h. Q s h))``,
METIS_TAC[])) THEN
REPEAT STRIP_TAC THEN
Cases_on `LIST_DS_SEM s h (pfL', sfL')` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `LIST_DS_SEM s h (pfL, sfL)` THEN ASM_REWRITE_TAC[] THEN
Cases_on `~DS_EXPRESSION_EQUAL s e1 e2` THEN1 (
   `~(n1 = n2)` by DECIDE_TAC THEN
   METIS_TAC[pairTheory.FST, pairTheory.SND, HEAP_DISTINCT___NOT_ALL_DISTINCT2]
) THEN
FULL_SIMP_TAC std_ss [] THEN
SIMP_TAC std_ss [HEAP_DISTINCT_def] THEN
`(FILTER (\(e1,e2). ~DS_EXPRESSION_EQUAL s e1 e2)
                  (DELETE_ELEMENT n1 (DELETE_ELEMENT n2 c2))) =
                  (FILTER (\(e1,e2). ~DS_EXPRESSION_EQUAL s e1 e2) c2)` by (
   Q.PAT_X_ASSUM `n1 < n2` MP_TAC THEN
   REPEAT (Q.PAT_X_ASSUM `N < LENGTH c2` MP_TAC) THEN
   REPEAT (Q.PAT_X_ASSUM `X = (e1,e2)` MP_TAC) THEN
   Q.PAT_X_ASSUM `DS_EXPRESSION_EQUAL s e1 e2` MP_TAC THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN
   Q.SPEC_TAC (`n2`, `n2`) THEN
   Q.SPEC_TAC (`n1`, `n1`) THEN
   REWRITE_TAC [AND_IMP_INTRO, GSYM CONJ_ASSOC] THEN

   Induct_on `c2` THENL [
      SIMP_TAC list_ss [],

      SIMP_TAC list_ss [] THEN
      REPEAT STRIP_TAC THEN
      Cases_on `n2` THEN1 FULL_SIMP_TAC list_ss [] THEN
      Cases_on `n1` THENL [
         FULL_SIMP_TAC list_ss [DELETE_ELEMENT_THM] THEN
         Q.PAT_X_ASSUM `n < LENGTH c2` MP_TAC THEN
         Q.PAT_X_ASSUM `X = (e1,e2)` MP_TAC THEN
         Q.PAT_X_ASSUM `DS_EXPRESSION_EQUAL s e1 e2` MP_TAC THEN
         REPEAT (POP_ASSUM (K ALL_TAC)) THEN
         Q.SPEC_TAC (`n`, `n`) THEN
         REWRITE_TAC [AND_IMP_INTRO, GSYM CONJ_ASSOC] THEN
         Induct_on `c2` THENL [
            SIMP_TAC list_ss [],

            SIMP_TAC list_ss [] THEN
            Cases_on `n` THENL [
               SIMP_TAC list_ss [DELETE_ELEMENT_THM],

               SIMP_TAC list_ss [DELETE_ELEMENT_THM] THEN
               METIS_TAC[]
            ]
         ],

         FULL_SIMP_TAC list_ss [DELETE_ELEMENT_THM]
      ]
   ]
) THEN
`!e1 e2. ~(DS_EXPRESSION_EQUAL s e1 e2) ==>
         (MEM (e1,e2) c2 = MEM (e1,e2) (DELETE_ELEMENT n1 (DELETE_ELEMENT n2 c2)))` by (
   REPEAT STRIP_TAC THEN
   `!l. MEM (e1', e2') l =
        MEM (e1', e2') (FILTER (\(e1,e2). ~DS_EXPRESSION_EQUAL s e1 e2) l)` by (
      ASM_SIMP_TAC std_ss [MEM_FILTER]
   ) THEN
   METIS_TAC[]
) THEN
METIS_TAC[]);




val INFERENCE___precondition_precondition_EQ___EVAL = store_thm ("INFERENCE___precondition_precondition_EQ___EVAL",
``!n1 n2 e1 e2 c1 c2 pfL sfL pfL' sfL'.
         ((SAFE_DEL_EL n1 c1 = [e1]) /\
          (SAFE_DEL_EL n2 c2 = [(e1,e2)])) ==>

         (LIST_DS_ENTAILS (c1, c2) (pfL, sfL) (pfL', sfL') =
          LIST_DS_ENTAILS (c1, (DELETE_ELEMENT n2 c2)) (pf_equal e1 e2::pfL, sfL) (pfL', sfL'))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ, LIST_DS_ENTAILS_def, LIST_DS_SEM_THM, PF_SEM_def] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC (prove (``(!s h. P s h = Q s h) ==> ((!s h. P s h) = (!s h. Q s h))``,
METIS_TAC[])) THEN
REPEAT STRIP_TAC THEN
Cases_on `LIST_DS_SEM s h (pfL', sfL')` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `LIST_DS_SEM s h (pfL, sfL)` THEN ASM_REWRITE_TAC[] THEN
MATCH_MP_TAC (prove (``(~a = ~b) ==> (a = b)``, SIMP_TAC list_ss [])) THEN
REWRITE_TAC [] THEN
SIMP_TAC std_ss [] THEN

`(HEAP_DISTINCT s h c1 c2) =
 (HEAP_DISTINCT s h c1 (SWAP_TO_POS 0 n2 c2))` by (
   MATCH_MP_TAC HEAP_DISTINCT___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
`!c2.
 (HEAP_DISTINCT s h c1 c2) =
 (HEAP_DISTINCT s h (SWAP_TO_POS 0 n1 c1) c2)` by (
   GEN_TAC THEN
   MATCH_MP_TAC HEAP_DISTINCT___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN

SIMP_TAC list_ss [HEAP_DISTINCT___IND_DEF, DISJ_IMP_THM, FORALL_AND_THM] THEN
EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
FULL_SIMP_TAC std_ss [DS_EXPRESSION_EQUAL_def])









val INFERENCE___NIL_LIST_EVAL = store_thm ("INFERENCE___NIL_LIST_EVAL",
``!n f e c1 c2 pfL sfL pfL' sfL'.
         (SAFE_DEL_EL n sfL = [sf_ls f dse_nil e]) ==>

         (LIST_DS_ENTAILS (c1, c2) (pfL, sfL) (pfL', sfL') =
          LIST_DS_ENTAILS (c1, c2) ((pf_equal e dse_nil)::pfL, DELETE_ELEMENT n sfL) (pfL', sfL'))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n sfL) (pfL',sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN
ASM_REWRITE_TAC[INFERENCE___NIL_LIST])




val INFERENCE___precondition_LIST_EVAL = store_thm ("INFERENCE___precondition_LIST_EVAL",
``!n1 n2 f e1 e2 c1 c2 pfL sfL pfL' sfL'.
         ((SAFE_DEL_EL n2 sfL = [sf_ls f e1 e2]) /\
          (SAFE_DEL_EL n1 c1 = [e1])) ==>

         (LIST_DS_ENTAILS (c1, c2) (pfL, sfL) (pfL', sfL') =
          LIST_DS_ENTAILS (c1, c2) ((pf_equal e2 e1)::pfL, DELETE_ELEMENT n2 sfL) (pfL', sfL'))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n2 sfL) (pfL',sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN
SIMP_TAC list_ss [LIST_DS_ENTAILS_def] THEN
HO_MATCH_MP_TAC (prove (``(!s h. P s h = Q s h) ==> ((!s h. P s h) = (!s h. Q s h))``, METIS_TAC[])) THEN
REPEAT STRIP_TAC THEN
Cases_on `HEAP_DISTINCT s h c1 c2` THEN ASM_REWRITE_TAC[] THEN
Cases_on `LIST_DS_SEM s h (pfL', sfL')` THEN ASM_REWRITE_TAC[] THEN
SIMP_TAC std_ss [LIST_DS_SEM_THM, PF_SEM_def] THEN
Cases_on `DS_EXPRESSION_EQUAL s e2 (EL n1 c1)` THENL [
   FULL_SIMP_TAC std_ss [SF_SEM___sf_ls_THM, LET_THM, DS_EXPRESSION_EQUAL_def,
      FUNION_FEMPTY_1, FDOM_FEMPTY, DISJOINT_EMPTY],


   FULL_SIMP_TAC std_ss [SF_SEM___sf_ls_THM, LET_THM, DS_EXPRESSION_EQUAL_def] THEN
   SIMP_TAC std_ss [SF_SEM___sf_points_to_THM, DS_POINTS_TO_def] THEN
   REPEAT STRIP_TAC THEN
   `~(GET_DSV_VALUE (DS_EXPRESSION_EVAL s (EL n1 c1)) IN FDOM h)` by (
      FULL_SIMP_TAC std_ss [HEAP_DISTINCT_def] THEN
      METIS_TAC[MEM_EL]
   ) THEN
   Cases_on `h = FUNION h1 h2` THEN ASM_REWRITE_TAC[] THEN
   FULL_SIMP_TAC std_ss [FDOM_FUNION, IN_UNION]
]);





val INFERENCE___NON_EMPTY_LS___EVAL = store_thm ("INFERENCE___NON_EMPTY_LS___EVAL",
``!n1 n2 n3 b e1 e2 e3 f a c1 c2 pfL sfL pfL' sfL'.
         ((SAFE_DEL_EL n1 sfL' = [sf_ls f e1 e3]) /\
          (SAFE_DEL_EL n2 pfL = [if b then pf_unequal e1 e3 else pf_unequal e3 e1]) /\
          (SAFE_DEL_EL n3 sfL = [sf_points_to e1 a]) /\
          (MEM (f,e2) a) /\ ALL_DISTINCT (MAP FST a)) ==>

         (LIST_DS_ENTAILS (c1, c2) (pfL, sfL) (pfL', sfL') =
          LIST_DS_ENTAILS (e1::c1, c2) (pfL, DELETE_ELEMENT n3 sfL) (pfL', (sf_ls f e2 e3)::DELETE_ELEMENT n1 sfL'))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n3 sfL) (pfL',SWAP_TO_POS 0 n1 sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
`!c1 c2 sfL pfL' sfL'.
 LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (SWAP_TO_POS 0 n2 pfL,sfL) (pfL',sfL')` by (
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
`!c1 c2 pfL sfL pfL' sfL'.
 LIST_DS_ENTAILS (c1, c2) ((if b then pf_unequal e1 e3 else pf_unequal e3 e1)::pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (pf_unequal e1 e3::pfL,sfL) (pfL',sfL')` by (
   REPEAT GEN_TAC THEN
   SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_THM, COND_RAND, COND_RATOR,
      PF_SEM_def, DS_EXPRESSION_EQUAL_def] THEN
   METIS_TAC[]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN

MP_TAC (Q.SPECL [`e1`, `e2`, `e3`, `f`, `a`] (GSYM INFERENCE_NON_EMPTY_LS)) THEN
ASM_SIMP_TAC list_ss [] THEN STRIP_TAC THEN POP_ASSUM (K ALL_TAC) THEN
METIS_TAC[INFERENCE_STAR_INTRODUCTION___points_to])






val INFERENCE___NON_EMPTY_BIN_TREE___EVAL = store_thm ("INFERENCE___NON_EMPTY_BIN_TREE___EVAL",
``!n1 n2 e e1 e2 f1 f2 a c1 c2 pfL sfL pfL' sfL'.
         ((SAFE_DEL_EL n1 sfL' = [sf_bin_tree (f1,f2) e]) /\
          (SAFE_DEL_EL n2 sfL = [sf_points_to e a]) /\
          (MEM (f1,e1) a) /\ MEM (f2,e2) a /\ ~(f1 = f2) /\ ALL_DISTINCT (MAP FST a)) ==>

         (LIST_DS_ENTAILS (c1, c2) (pfL, sfL) (pfL', sfL') =
          LIST_DS_ENTAILS (e::c1, c2) (pfL, DELETE_ELEMENT n2 sfL) (pfL', (sf_bin_tree (f1,f2) e1)::(sf_bin_tree (f1,f2) e2)::DELETE_ELEMENT n1 sfL'))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n2 sfL) (pfL',SWAP_TO_POS 0 n1 sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN

MP_TAC (Q.SPECL [`e`, `e1`, `e2`, `f1`, `f2`, `a`] (GSYM INFERENCE_NON_EMPTY_BIN_TREE)) THEN
ASM_SIMP_TAC list_ss [] THEN STRIP_TAC THEN POP_ASSUM (K ALL_TAC) THEN
METIS_TAC[INFERENCE_STAR_INTRODUCTION___points_to])




val INFERENCE_UNROLL_COLLAPSE_LS___EVAL = store_thm ("INFERENCE_UNROLL_COLLAPSE_LS___EVAL",
``!n (e1:('b, 'a) ds_expression) e2 (f:'c) c1 c2 pfL sfL pfL' sfL'.
          ((SAFE_DEL_EL n sfL = [sf_ls f e1 e2]) /\
            INFINITE (UNIV:'b set)) ==>

            (LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL') =
            (LIST_DS_ENTAILS (c1,c2) (pf_equal e1 e2::pfL,DELETE_ELEMENT n sfL) (pfL',sfL') /\
             (!x.
                LIST_DS_ENTAILS (c1,c2)
                  (pf_unequal e1 e2::pf_unequal (dse_const x) e2::pfL,
                   sf_points_to e1 [(f,dse_const x)]::
                       sf_points_to (dse_const x) [(f,e2)]::DELETE_ELEMENT n sfL) (pfL',sfL'))))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n sfL) (pfL',sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN
METIS_TAC [INFERENCE_UNROLL_COLLAPSE_LS]);





val INFERENCE_UNROLL_COLLAPSE_PRECONDITION___EVAL = store_thm ("INFERENCE_UNROLL_COLLAPSE_PRECONDITION___EVAL",
``!e1 e2 c1 c2 pfL sfL pfL' sfL'.
   (LIST_DS_ENTAILS (c1,(e1,e2)::c2) (pfL,sfL) (pfL',sfL')) =
   (LIST_DS_ENTAILS (e1::c1,c2) (pf_unequal e1 e2::pfL,sfL) (pfL',sfL') /\
    LIST_DS_ENTAILS (c1,c2) (pf_equal e1 e2::pfL,sfL) (pfL',sfL'))``,

SIMP_TAC std_ss [LIST_DS_ENTAILS_def, GSYM FORALL_AND_THM, HEAP_DISTINCT___IND_DEF,
   LIST_DS_SEM_THM, PF_SEM_def] THEN
METIS_TAC[]);


val INFERENCE_UNROLL_COLLAPSE_LS___NON_EMPTY___EVAL = store_thm    ("INFERENCE_UNROLL_COLLAPSE_LS___NON_EMPTY___EVAL",
``!n n2 b (e1:('b, 'a) ds_expression) e2 (f:'c) c1 c2 pfL sfL pfL' sfL'.
          ((SAFE_DEL_EL n sfL = [sf_ls f e1 e2]) /\
           (SAFE_DEL_EL n2 pfL = [if b then pf_unequal e2 e1 else pf_unequal e1 e2]) /\
            INFINITE (UNIV:'b set)) ==>

            (LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL') =
             (!x.
                LIST_DS_ENTAILS (c1,c2)
                  (pf_unequal (dse_const x) e2::pfL,
                   sf_points_to e1 [(f,dse_const x)]::
                       sf_points_to (dse_const x) [(f,e2)]::DELETE_ELEMENT n sfL) (pfL',sfL')))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (SWAP_TO_POS 0 n2 pfL,SWAP_TO_POS 0 n sfL) (pfL',sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
`!sfL pfL' sfL' h.
 LIST_DS_ENTAILS (c1, c2) (h::pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (SWAP_TO_POS 0 (SUC n2) (h::pfL),sfL) (pfL',sfL')` by (
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL, PERM_CONS_IFF] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
`!pfL sfL sfL' pfL'.
   LIST_DS_ENTAILS (c1,c2) ((if b then pf_unequal e2 e1 else pf_unequal e1 e2)::pfL,sfL) (pfL',sfL') =
   LIST_DS_ENTAILS (c1,c2) (pf_unequal e1 e2::pfL,sfL) (pfL',sfL')` by (
   REPEAT GEN_TAC THEN
   SIMP_TAC std_ss [LIST_DS_ENTAILS_def, LIST_DS_SEM_THM, COND_RAND, COND_RATOR,
      PF_SEM_def, DS_EXPRESSION_EQUAL_def] THEN
   METIS_TAC[]
) THEN
ASM_SIMP_TAC list_ss [SWAP_TO_POS___DELETE_ELEMENT, DELETE_ELEMENT_THM] THEN
ASM_SIMP_TAC std_ss [GSYM INFERENCE_UNROLL_COLLAPSE_LS___NON_EMPTY]);










val INFERENCE_UNROLL_COLLAPSE_BIN_TREE___EVAL = store_thm ("INFERENCE_UNROLL_COLLAPSE_BIN_TREE___EVAL",
``!n (e:('b, 'a) ds_expression) (f1:'c) f2 c1 c2 pfL sfL pfL' sfL'.
          ((SAFE_DEL_EL n sfL = [sf_bin_tree (f1,f2) e]) /\ ~(f1 = f2) /\
            INFINITE (UNIV:'b set)) ==>

            (LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL') =
            (LIST_DS_ENTAILS (c1,c2) (pf_equal e dse_nil::pfL,DELETE_ELEMENT n sfL) (pfL',sfL') /\
             (!x1 x2.
                LIST_DS_ENTAILS (c1,c2)
                  (pf_unequal e dse_nil::pf_unequal (dse_const x1) dse_nil::pf_unequal (dse_const x2) dse_nil::pfL,
                   sf_points_to e [(f1,dse_const x1);(f2,dse_const x2)]::
                       sf_points_to (dse_const x1) [(f1,dse_nil);(f2,dse_nil)]::sf_points_to (dse_const x2) [(f1,dse_nil);(f2,dse_nil)]::DELETE_ELEMENT n sfL) (pfL',sfL'))))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n sfL) (pfL',sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN
METIS_TAC [INFERENCE_UNROLL_COLLAPSE_BIN_TREE]);





val INFERENCE_APPEND_LIST___nil___EVAL = store_thm ("INFERENCE_APPEND_LIST___nil___EVAL",
``!n1 n2 (e1:('b, 'a) ds_expression) e2 f c1 c2 pfL sfL pfL' sfL'.
          ((SAFE_DEL_EL n1 sfL = [sf_ls f e1 e2]) /\
           (SAFE_DEL_EL n2 sfL' = [sf_ls f e1 dse_nil]) /\
            INFINITE (UNIV:'b set)) ==>

            (LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL') =
            (LIST_DS_ENTAILS (c1,(e1,e2)::c2) (pfL,DELETE_ELEMENT n1 sfL) (pfL',sf_ls f e2 dse_nil::DELETE_ELEMENT n2 sfL')))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n1 sfL) (pfL',SWAP_TO_POS 0 n2 sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT,
   GSYM INFERENCE_APPEND_LIST___nil,
   GSYM INFERENCE_STAR_INTRODUCTION___list]);





val INFERENCE_APPEND_LIST___precond___EVAL = store_thm ("INFERENCE_APPEND_LIST___precond___EVAL",
``!n1 n2 (e1:('b, 'a) ds_expression) e2 f e3 n3 n4 b c1 c2 pfL sfL pfL' sfL'.
          ((SAFE_DEL_EL n1 sfL = [sf_ls f e1 e2]) /\
           (SAFE_DEL_EL n2 sfL' = [sf_ls f e1 e3]) /\
           (SAFE_DEL_EL n4 pfL = [if b then pf_unequal e3 e1 else pf_unequal e1 e3]) /\
           (SAFE_DEL_EL n3 c1 = [e3]) /\
            INFINITE (UNIV:'b set)) ==>

            (LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL') =
            (LIST_DS_ENTAILS (c1,(e1,e2)::c2) (pfL,DELETE_ELEMENT n1 sfL) (pfL',sf_ls f e2 e3::DELETE_ELEMENT n2 sfL')))``,


REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (pfL,SWAP_TO_POS 0 n1 sfL) (pfL',SWAP_TO_POS 0 n2 sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
`!c2 pfL sfL pfL' sfL'.
 LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (SWAP_TO_POS 0 n3 c1, c2) (pfL,sfL) (pfL',sfL')` by (
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
`MEM_UNEQ_PF_LIST e1 e3 pfL` by (
   SIMP_TAC std_ss [MEM_UNEQ_PF_LIST_def] THEN
   METIS_TAC[MEM_EL]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT,
   GSYM INFERENCE_APPEND_LIST___precond,
   GSYM INFERENCE_STAR_INTRODUCTION___list]);




val INFERENCE_APPEND_LIST___points_to___EVAL = store_thm ("INFERENCE_APPEND_LIST___points_to___EVAL",
``!n1 n2 (e1:('b, 'a) ds_expression) e2 f e3 n3 a n4 b c1 c2 pfL sfL pfL' sfL'.
          ((SAFE_DEL_EL n1 sfL = [sf_ls f e1 e2]) /\
           (SAFE_DEL_EL n2 sfL' = [sf_ls f e1 e3]) /\
           (SAFE_DEL_EL n3 sfL = [sf_points_to e3 a]) /\
           (SAFE_DEL_EL n4 pfL = [if b then pf_unequal e3 e1 else pf_unequal e1 e3]) /\
            INFINITE (UNIV:'b set)) ==>

            (LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL') =
            (LIST_DS_ENTAILS (c1,(e1,e2)::c2) (pfL,DELETE_ELEMENT n1 sfL) (pfL',sf_ls f e2 e3::DELETE_ELEMENT n2 sfL')))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`?sfL''. PERM (EL n1 sfL::EL n3 sfL::sfL'') sfL /\
         PERM (EL n3 sfL::sfL'') (DELETE_ELEMENT n1 sfL)` by (
   MATCH_MP_TAC PERM___TWO_ELEMENTS_TO_FRONT_3 THEN
   ASM_SIMP_TAC std_ss [] THEN
   CCONTR_TAC THEN
   FULL_SIMP_TAC std_ss [ds_spatial_formula_distinct, sf_ls_def]
) THEN

`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (pfL,EL n1 sfL::EL n3 sfL::sfL'') (pfL',SWAP_TO_POS 0 n2 sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN

`MEM_UNEQ_PF_LIST e1 e3 pfL` by (
   SIMP_TAC std_ss [MEM_UNEQ_PF_LIST_def] THEN
   METIS_TAC[MEM_EL]
) THEN
ASM_SIMP_TAC std_ss [GSYM INFERENCE_APPEND_LIST___points_to,
   GSYM INFERENCE_STAR_INTRODUCTION___list] THEN

MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
SIMP_TAC std_ss [PERM_REFL] THEN
METIS_TAC[]);





val INFERENCE_APPEND_LIST___tree___EVAL = store_thm ("INFERENCE_APPEND_LIST___tree___EVAL",
``!n1 n2 (e1:('b, 'a) ds_expression) e2 n3 e3 fL es n4 b1 n5 b2 f c1 c2 pfL sfL pfL' sfL'.
          ((SAFE_DEL_EL n1 sfL = [sf_ls f e1 e2]) /\
           (SAFE_DEL_EL n2 sfL' = [sf_ls f e1 e3]) /\
           (SAFE_DEL_EL n3 sfL = [sf_tree fL es e3]) /\
           (~(n3 = n1)) /\
           (SAFE_DEL_EL n4 pfL = [if b1 then pf_unequal e3 e1 else pf_unequal e1 e3]) /\
           (SAFE_DEL_EL n5 pfL = [if b2 then pf_unequal es e3 else pf_unequal e3 es]) /\
            INFINITE (UNIV:'b set)) ==>

            (LIST_DS_ENTAILS (c1,c2) (pfL,sfL) (pfL',sfL') =
            (LIST_DS_ENTAILS (c1,(e1,e2)::c2) (pfL,DELETE_ELEMENT n1 sfL) (pfL',sf_ls f e2 e3::DELETE_ELEMENT n2 sfL')))``,


SIMP_TAC std_ss [SAFE_DEL_EL___EQ] THEN
REPEAT STRIP_TAC THEN
`?sfL''. PERM (EL n1 sfL::EL n3 sfL::sfL'') sfL /\
         PERM (EL n3 sfL::sfL'') (DELETE_ELEMENT n1 sfL)` by (
   MATCH_MP_TAC PERM___TWO_ELEMENTS_TO_FRONT_3 THEN
   ASM_SIMP_TAC std_ss []
) THEN

`LIST_DS_ENTAILS (c1, c2) (pfL,sfL) (pfL',sfL') =
 LIST_DS_ENTAILS (c1, c2) (pfL,EL n1 sfL::EL n3 sfL::sfL'') (pfL',SWAP_TO_POS 0 n2 sfL')` by (
   MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
   SIMP_TAC std_ss [PERM_REFL] THEN
   METIS_TAC[PERM___SWAP_TO_POS, PERM_SYM]
) THEN
ASM_SIMP_TAC std_ss [SWAP_TO_POS___DELETE_ELEMENT] THEN

`MEM_UNEQ_PF_LIST e1 e3 pfL /\ MEM_UNEQ_PF_LIST e3 es pfL` by (
   SIMP_TAC std_ss [MEM_UNEQ_PF_LIST_def] THEN
   METIS_TAC[MEM_EL]
) THEN
ASM_SIMP_TAC std_ss [GSYM INFERENCE_APPEND_LIST___tree,
   GSYM INFERENCE_STAR_INTRODUCTION___list] THEN

MATCH_MP_TAC LIST_DS_ENTAILS___PERM THEN
SIMP_TAC std_ss [PERM_REFL] THEN
METIS_TAC[]);





(*



val FINITE_DISTINCT_STACK_EXISTS_THM = store_thm ("FINITE_DISTINCT_STACK_EXISTS_THM",
   ``(INFINITE (UNIV:'b set)) ==>
         !eL. (FINITE (eL:('b, 'a) ds_expression set)) ==> (
          !X. FINITE X ==>
          ?s. (!e. (e IN eL) ==> (IS_DSV_NIL (DS_EXPRESSION_EVAL s e) = (e = dse_nil))) /\
              (!v. (dse_var v IN eL) ==> ~(GET_DSV_VALUE (s v) IN X)) /\
              (!e1 e2. (e1 IN eL /\ e2 IN eL) ==> (
                  DS_EXPRESSION_EQUAL s e1 e2 = (e1 = e2))))``,


STRIP_TAC THEN
pred_setLib.SET_INDUCT_TAC THENL [
   SIMP_TAC list_ss [NOT_IN_EMPTY],

   Cases_on `e` THENL [
      GEN_TAC THEN
      Q.PAT_X_ASSUM `!X. P X` (fn thm => ASSUME_TAC(Q.SPEC `GET_DSV_VALUE d INSERT X` thm)) THEN
      STRIP_TAC THEN
      FULL_SIMP_TAC std_ss [FINITE_INSERT] THEN
      Q.EXISTS_TAC `s'` THEN
      FULL_SIMP_TAC std_ss [IN_INSERT, FORALL_AND_THM, DISJ_IMP_THM, FORALL_AND_THM,
      LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, dse_nil_def, DS_EXPRESSION_EQUAL_def,
         ds_value_11, DS_EXPRESSION_EVAL_def, ds_expression_11, ds_value_distinct,
         ds_expression_distinct, IN_INSERT, IS_DSV_NIL_THM] THEN
      SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN
      Cases_on `e1` THENL [
         SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, ds_expression_11],

         SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, ds_expression_distinct] THEN
         METIS_TAC[]
      ],


      GEN_TAC THEN
      Q.PAT_X_ASSUM `!X. P X` (fn thm => ASSUME_TAC(Q.SPEC `X` thm)) THEN
      STRIP_TAC THEN
      FULL_SIMP_TAC std_ss [] THEN

      `?c. ~(c IN (X UNION (IMAGE (DS_EXPRESSION_EVAL_VALUE s') s)))` by
         METIS_TAC[NOT_IN_FINITE, IMAGE_FINITE,
         FINITE_UNION] THEN

      Q.EXISTS_TAC `\x. if (x = v) then dsv_const c else s' x` THEN
      ASM_SIMP_TAC std_ss [IN_INSERT, FORALL_AND_THM, DISJ_IMP_THM, FORALL_AND_THM,
         LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR] THEN
      FULL_SIMP_TAC std_ss [IS_DSV_NIL_THM, DS_EXPRESSION_EQUAL_def, DS_EXPRESSION_EVAL_def,
         dse_nil_def, ds_value_distinct, ds_expression_distinct, ds_expression_11,
         GET_DSV_VALUE_def] THEN
      REPEAT STRIP_TAC THENL [
         `((DS_EXPRESSION_EVAL s' e = dsv_nil) = (e = dse_const dsv_nil))` by METIS_TAC[] THEN
         Cases_on `e` THENL [
            SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, ds_expression_11],

            `~(v' = v)` by METIS_TAC[] THEN
            FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def]
         ],


         FULL_SIMP_TAC std_ss [IN_UNION],
         METIS_TAC[],


         Cases_on `e2` THENL [
            SIMP_TAC list_ss [DS_EXPRESSION_EVAL_def, ds_expression_distinct] THEN
            FULL_SIMP_TAC std_ss [IN_UNION, IN_IMAGE, DS_EXPRESSION_EVAL_VALUE_def] THEN
            `~(c = GET_DSV_VALUE (DS_EXPRESSION_EVAL s' (dse_const d)))` by METIS_TAC[] THEN
            FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def] THEN
            Cases_on `d` THENL [
               SIMP_TAC list_ss [ds_value_distinct],
               FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, ds_value_11]
            ],

            `~(v'=v)` by METIS_TAC[] THEN
            ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, ds_expression_11] THEN
            FULL_SIMP_TAC std_ss [IN_UNION, IN_IMAGE, DS_EXPRESSION_EVAL_VALUE_def] THEN
            `~(c = GET_DSV_VALUE (DS_EXPRESSION_EVAL s' (dse_var v')))` by METIS_TAC[] THEN
            FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def] THEN
            Cases_on `s' v'` THENL [
               SIMP_TAC list_ss [ds_value_distinct],
               FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, ds_value_11]
            ]
         ],


         Cases_on `e1` THENL [
            SIMP_TAC list_ss [DS_EXPRESSION_EVAL_def, ds_expression_distinct] THEN
            FULL_SIMP_TAC std_ss [IN_UNION, IN_IMAGE, DS_EXPRESSION_EVAL_VALUE_def] THEN
            `~(c = GET_DSV_VALUE (DS_EXPRESSION_EVAL s' (dse_const d)))` by METIS_TAC[] THEN
            FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def] THEN
            Cases_on `d` THENL [
               SIMP_TAC list_ss [ds_value_distinct],
               FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, ds_value_11]
            ],

            `~(v'=v)` by METIS_TAC[] THEN
            ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def, ds_expression_11] THEN
            FULL_SIMP_TAC std_ss [IN_UNION, IN_IMAGE, DS_EXPRESSION_EVAL_VALUE_def] THEN
            `~(c = GET_DSV_VALUE (DS_EXPRESSION_EVAL s' (dse_var v')))` by METIS_TAC[] THEN
            FULL_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def] THEN
            Cases_on `s' v'` THENL [
               SIMP_TAC list_ss [ds_value_distinct],
               FULL_SIMP_TAC std_ss [GET_DSV_VALUE_def, ds_value_11]
            ]
         ],

         `!e. e IN s ==>
              (DS_EXPRESSION_EVAL (\x. (if x = v then dsv_const c else s' x)) e =
               DS_EXPRESSION_EVAL s' e)` by (
            REPEAT STRIP_TAC THEN
            Cases_on `e` THENL [
               SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def],

               `~(v' = v)` by METIS_TAC[] THEN
               ASM_SIMP_TAC std_ss [DS_EXPRESSION_EVAL_def]
            ]
         ) THEN
         FULL_SIMP_TAC std_ss []
      ]
   ]
]);





val FINITE_DISTINCT_STACK_EXISTS_THM2 = store_thm ("FINITE_DISTINCT_STACK_EXISTS_THM2",
   ``!eL. (FINITE (eL:('b, 'a) ds_expression set) /\ (INFINITE (UNIV:'b set))) ==>
         ?s. (!e. (e IN eL) ==> (IS_DSV_NIL (DS_EXPRESSION_EVAL s e) = (e = dse_nil))) /\
            (!e1 e2. (e1 IN eL /\ e2 IN eL) ==> (
               DS_EXPRESSION_EQUAL s e1 e2 = (e1 = e2)))``,

REPEAT STRIP_TAC THEN
METIS_TAC[FINITE_EMPTY, FINITE_DISTINCT_STACK_EXISTS_THM]);





val PF_IS_WELL_FORMED_UNEQUAL_def = Define `
   (SF_IS_WELL_FORMED_UNEQUAL (pf_unequal e1 e2) = ~(e1 = e2)) /\
   (SF_IS_WELL_FORMED_UNEQUAL _ = F)`;

val SF_IS_WELL_FORMED_POINTSTO_def = Define `
   (SF_IS_WELL_FORMED_POINTSTO (sf_points_to e a) =
      ALL_DISTINCT (MAP FST a)) /\
   (SF_IS_WELL_FORMED_POINTSTO _ = F)`;

val LIST_DS_ENTAILS___IS_SIMPLE_LHS_def = Define
  `LIST_DS_ENTAILS___IS_SIMPLE_LHS c1 pfL sfL =
   (ALL_DISTINCT c1 /\
    EVERY PF_IS_WELL_FORMED_UNEQUAL pfL /\
    EVERY SF_IS_WELL_FORMED_POINTSTO sfL /\
    ALL_DISTINCT (SF_POINTS_TO_LIST sfL) /\
    EVERY (\x. ~(MEM x (SF_POINTS_TO_LIST sfL))) c1)`



DB.find "SF_POINTS_TO_LIST_def"




*)

val _ = export_theory();
