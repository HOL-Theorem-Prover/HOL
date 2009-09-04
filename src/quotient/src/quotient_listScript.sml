open HolKernel Parse boolLib;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;
infixr -->;


(* --------------------------------------------------------------------- *)
(* Lifting the lambda calculus syntax to the abstract level.             *)
(* Version 2.1.                                                          *)
(* Date: February 28, 2005                                               *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "quotient_list";

open prim_recTheory;
open combinTheory;
open listTheory;
open rich_listTheory;
open listLib;
open bossLib;
open res_quanTheory;
open res_quanLib;
open dep_rewrite;
open quotientTheory;


val REWRITE_THM = fn th => REWRITE_TAC[th];
val ONCE_REWRITE_THM = fn th => ONCE_REWRITE_TAC[th];
val REWRITE_ALL_THM = fn th => RULE_ASSUM_TAC (REWRITE_RULE[th])
                               THEN REWRITE_TAC[th];

val POP_TAC = POP_ASSUM (fn th => ALL_TAC);


(* =================================================================== *)
(* To form a ABS / REP function or a equivalence relation REL from     *)
(* the corresponding functions/relations of the constituent subtypes   *)
(* of the main type, use the following table of operators:             *)
(*                                                                     *)
(*      Type Operator     Constructor   Abstraction      Equivalence   *)
(*                                                                     *)
(*  Identity                  I x           I                $=        *)
(*  Product  (ty1 # ty2)     (a,b)    (abs1 ## abs2)     (R1 ### R2)   *)
(*  Sum      (ty1 + ty2)    (INL x)   (abs1 ++ abs2)     (R1 +++ R2)   *)
(*  List      (ty list)    (CONS h t)    (MAP abs)       (LIST_REL R)  *)
(*  Option    (ty option)  (SOME x)  (OPTION_MAP abs)   (OPTION_REL R) *)
(*  Function (ty1 -> ty2)  (\x. f x)  (rep1 --> abs2)  (rep1 =-> abs2) *)
(*  (Strong respect)                                     (R1 ===> R2)  *)
(*                                                                     *)
(* =================================================================== *)




(* for LIST_REP or LIST_ABS, just use MAP! See Theorem MAP. *)

val LIST_MAP_I =
 store_thm
  ("LIST_MAP_I",
   (--`MAP (I:'a -> 'a) = I`--),
   REWRITE_TAC[FUN_EQ_THM]
   THEN Induct
   THEN ASM_REWRITE_TAC[MAP,I_THM]
  );

(* for list equivalence relation, use prefix LIST_REL, defined here: *)

(* Almost MAP2, but this is totally defined: *)
val LIST_REL_def =
    Define
      `(LIST_REL R [] [] = T) /\
       (LIST_REL R ((a:'a)::as) [] = F) /\
       (LIST_REL R [] ((b:'a)::bs) = F) /\
       (LIST_REL R (a::as) (b::bs) = (R a b /\ LIST_REL R as bs))`;

val LIST_REL_ind = fetch "-" "LIST_REL_ind";

val LIST_REL_EQ = store_thm
   ("LIST_REL_EQ",
    (--`(LIST_REL ($= : 'a->'a->bool)) = $=`--),
    CONV_TAC FUN_EQ_CONV
    THEN CONV_TAC (RAND_CONV (ABS_CONV FUN_EQ_CONV))
    THEN Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Induct
    THEN REWRITE_TAC[LIST_REL_def,NOT_CONS_NIL,NOT_NIL_CONS]
    THEN GEN_TAC
    THEN ASM_REWRITE_TAC[CONS_11]
   );

val LIST_REL_REFL = store_thm
   ("LIST_REL_REFL",
    (--`!R. (!x y:'a. R x y = (R x = R y)) ==>
            !x. LIST_REL R x x`--),
    GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THEN REWRITE_TAC[LIST_REL_def]
    THEN GEN_TAC
    THEN ASM_REWRITE_TAC[]
   );

val LIST_EQUIV = store_thm
   ("LIST_EQUIV",
    (--`!R:'a -> 'a -> bool. EQUIV R ==> EQUIV (LIST_REL R)`--),
    GEN_TAC
    THEN REWRITE_TAC[EQUIV_def]
    THEN DISCH_TAC
    THEN Induct THENL [ALL_TAC, GEN_TAC]
    THEN Induct
    THEN REWRITE_TAC[LIST_REL_def]
    THENL
      [ PROVE_TAC[LIST_REL_def],

        PROVE_TAC[LIST_REL_def],

        GEN_TAC
        THEN CONV_TAC (RAND_CONV FUN_EQ_CONV)
        THEN EQ_TAC
        THENL
          [ STRIP_TAC
            THEN Cases
            THEN REWRITE_TAC[LIST_REL_def]
            THEN PROVE_TAC[],

            DISCH_THEN (MP_TAC o GEN ``c:'a`` o GEN ``cs:'a list``
                               o SPEC ``(c:'a)::cs``)
            THEN REWRITE_TAC[LIST_REL_def]
            THEN IMP_RES_TAC LIST_REL_REFL
            THEN PROVE_TAC[]
          ]
      ]
   );

val LIST_REL_REL = store_thm
   ("LIST_REL_REL",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !r s. LIST_REL R r s = LIST_REL R r r /\ LIST_REL R s s /\
                                (MAP abs r = MAP abs s)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Cases
    THEN ONCE_REWRITE_TAC[LIST_REL_def]
    THEN REWRITE_TAC[MAP,NOT_CONS_NIL,NOT_NIL_CONS]
    THEN REWRITE_TAC[CONS_11]
    THEN IMP_RES_THEN
               (fn th => CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV th))))
               QUOTIENT_REL
    THEN POP_ASSUM
               (fn th => CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th))))
    THEN PROVE_TAC[]
   );

val LIST_QUOTIENT = store_thm
   ("LIST_QUOTIENT",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         QUOTIENT (LIST_REL R) (MAP abs) (MAP rep)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT CONJ_TAC
    THENL (* 3 subgoals *)
      [ IMP_RES_TAC QUOTIENT_ABS_REP
        THEN Induct
        THEN ASM_REWRITE_TAC[MAP],

        IMP_RES_TAC QUOTIENT_REP_REFL
        THEN Induct
        THEN ASM_REWRITE_TAC[MAP,LIST_REL_def],

        Induct
        THENL [ ALL_TAC, GEN_TAC ]
        THEN Cases
        THEN ONCE_REWRITE_TAC[LIST_REL_def]
        THEN REWRITE_TAC[MAP,NOT_CONS_NIL,NOT_NIL_CONS]
        THEN REWRITE_TAC[CONS_11]
        THEN IMP_RES_THEN
               (fn th => CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV th))))
               QUOTIENT_REL
        THEN IMP_RES_THEN
               (fn th => CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th))))
               LIST_REL_REL
        THEN PROVE_TAC[]
      ]
   );




(* Here are some definitional and well-formedness theorems
   for some standard polymorphic operators.
*)



(* list theory: CONS, NIL, MAP, LENGTH, APPEND, FLAT, REVERSE, FILTER,
                NULL, SOME_EL, ALL_EL, FOLDL, FOLDR *)

val CONS_PRS = store_thm
   ("CONS_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !t h. CONS h t = (MAP abs) (CONS (rep h) (MAP rep t))`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THEN ASM_REWRITE_TAC[MAP]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val CONS_RSP = store_thm
   ("CONS_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !t1 t2 h1 h2.
          R h1 h2 /\ (LIST_REL R) t1 t2 ==>
          (LIST_REL R) (CONS h1 t1) (CONS h2 t2)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Cases
    THEN Cases
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[LIST_REL_def]
   );


val NIL_PRS = store_thm
   ("NIL_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         ([] = (MAP abs) [])`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[MAP]
   );

val NIL_RSP = store_thm
   ("NIL_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (LIST_REL R) [] []`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[LIST_REL_def]
   );


val MAP_PRS = store_thm
   ("MAP_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !l f. MAP f l = (MAP abs2) (MAP ((abs1 --> rep2) f) (MAP rep1 l))`--),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN Induct
    THEN ASM_REWRITE_TAC[MAP]
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[CONS_11]
    THEN ASM_REWRITE_TAC[FUN_MAP_THM]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val MAP_RSP = store_thm
   ("MAP_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !l1 l2 f1 f2.
          (R1 ===> R2) f1 f2 /\ (LIST_REL R1) l1 l2 ==>
          (LIST_REL R2) (MAP f1 l1) (MAP f2 l2)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Induct
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[MAP,LIST_REL_def]
    THEN STRIP_TAC
    THEN CONJ_TAC
    THENL
      [ IMP_RES_TAC FUN_REL_MP,

        FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );

val LENGTH_PRS = store_thm
   ("LENGTH_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !l. LENGTH l = LENGTH (MAP rep l)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THEN ASM_REWRITE_TAC[LENGTH,MAP]
   );

val LENGTH_RSP = store_thm
   ("LENGTH_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !l1 l2.
          (LIST_REL R) l1 l2 ==>
          (LENGTH l1 = LENGTH l2)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Induct
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[LENGTH,LIST_REL_def]
    THEN STRIP_TAC
    THEN REWRITE_TAC[INV_SUC_EQ]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN FIRST_ASSUM ACCEPT_TAC
   );

val APPEND_PRS = store_thm
   ("APPEND_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !l m. APPEND l m = MAP abs (APPEND (MAP rep l) (MAP rep m))`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Induct
    THEN ASM_REWRITE_TAC[APPEND,MAP]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
    THEN GEN_TAC
    THEN POP_ASSUM MP_TAC
    THEN REWRITE_TAC[APPEND,MAP]
    THEN DISCH_THEN (REWRITE_THM o SYM)
   );

val APPEND_RSP = store_thm
   ("APPEND_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !l1 l2 m1 m2.
          (LIST_REL R) l1 l2 /\ (LIST_REL R) m1 m2 ==>
          (LIST_REL R) (APPEND l1 m1) (APPEND l2 m2)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Induct
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[APPEND,LIST_REL_def]
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN CONJ_TAC
    THEN FIRST_ASSUM ACCEPT_TAC
   );

val FLAT_PRS = store_thm
   ("FLAT_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !l. FLAT l = MAP abs (FLAT (MAP (MAP rep) l))`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THEN ASM_REWRITE_TAC[FLAT,MAP]
    THEN Induct
    THEN REWRITE_TAC[MAP,APPEND]
    THEN ASM_REWRITE_TAC[MAP_APPEND]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val FLAT_RSP = store_thm
   ("FLAT_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !l1 l2.
          LIST_REL (LIST_REL R) l1 l2 ==>
          (LIST_REL R) (FLAT l1) (FLAT l2)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Induct
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[FLAT,LIST_REL_def]
    THEN STRIP_TAC
    THEN DEP_REWRITE_TAC[APPEND_RSP]
    THEN EXISTS_TAC (--`abs:'a -> 'b`--)
    THEN EXISTS_TAC (--`rep:'b -> 'a`--)
    THEN ASM_REWRITE_TAC[]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN FIRST_ASSUM ACCEPT_TAC
   );

val REVERSE_PRS = store_thm
   ("REVERSE_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !l. REVERSE l = MAP abs (REVERSE (MAP rep l))`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THEN ASM_REWRITE_TAC[REVERSE_DEF,MAP]
    THEN GEN_TAC
    THEN ASM_REWRITE_TAC[MAP_APPEND,MAP]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val REVERSE_RSP = store_thm
   ("REVERSE_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !l1 l2.
          LIST_REL R l1 l2 ==>
          (LIST_REL R) (REVERSE l1) (REVERSE l2)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Induct
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[REVERSE_DEF,LIST_REL_def]
    THEN STRIP_TAC
    THEN DEP_REWRITE_TAC[APPEND_RSP]
    THEN EXISTS_TAC (--`abs:'a -> 'b`--)
    THEN EXISTS_TAC (--`rep:'b -> 'a`--)
    THEN ASM_REWRITE_TAC[LIST_REL_def]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN FIRST_ASSUM ACCEPT_TAC
   );

val FILTER_PRS = store_thm
   ("FILTER_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !P l. FILTER P l = (MAP abs) (FILTER ((abs --> I) P) (MAP rep l))
       `--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN GEN_TAC
    THEN Induct
    THEN ASM_REWRITE_TAC[FILTER,MAP]
    THEN GEN_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[FUN_MAP_THM,I_THM]
    THEN COND_CASES_TAC
    THEN ASM_REWRITE_TAC[MAP]
   );

val FILTER_RSP = store_thm
   ("FILTER_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !P1 P2 l1 l2.
          (R ===> $=) P1 P2 /\ (LIST_REL R) l1 l2 ==>
          (LIST_REL R) (FILTER P1 l1) (FILTER P2 l2)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN GEN_TAC THEN GEN_TAC
    THEN Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Induct
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[FILTER,LIST_REL_def]
    THEN REWRITE_TAC[FUN_REL]
    THEN STRIP_TAC
    THEN REPEAT COND_CASES_TAC
    THEN REWRITE_TAC[LIST_REL_def]
    THEN REPEAT CONJ_TAC
    THENL (* 5 subgoals *)
      [ FIRST_ASSUM ACCEPT_TAC,

        FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[FUN_REL],

        RES_TAC
        THEN RES_TAC,

        RES_TAC
        THEN RES_TAC,

        FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[FUN_REL]
      ]
   );

val NULL_PRS = store_thm
   ("NULL_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !l. NULL l = NULL (MAP rep l)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Cases
    THEN REWRITE_TAC[NULL,MAP]
   );

val NULL_RSP = store_thm
   ("NULL_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !l1 l2.
          LIST_REL R l1 l2 ==>
          (NULL l1 = NULL l2)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Induct
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[NULL,LIST_REL_def]
   );

val SOME_EL_PRS = store_thm
   ("SOME_EL_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !l P. SOME_EL P l = SOME_EL ((abs --> I) P) (MAP rep l)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THEN ASM_REWRITE_TAC[SOME_EL,MAP]
    THEN REPEAT GEN_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[FUN_MAP_THM,I_THM]
   );

val SOME_EL_RSP = store_thm
   ("SOME_EL_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !l1 l2 P1 P2.
          (R ===> $=) P1 P2 /\ (LIST_REL R) l1 l2 ==>
          (SOME_EL P1 l1 = SOME_EL P2 l2)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Induct
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[SOME_EL,LIST_REL_def]
    THEN REWRITE_TAC[FUN_REL]
    THEN STRIP_TAC
    THEN MK_COMB_TAC
    THENL
      [ AP_TERM_TAC
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN FIRST_ASSUM ACCEPT_TAC,

        FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[FUN_REL]
      ]
   );

val ALL_EL_PRS = store_thm
   ("ALL_EL_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !l P. ALL_EL P l = ALL_EL ((abs --> I) P) (MAP rep l)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THEN ASM_REWRITE_TAC[ALL_EL,MAP]
    THEN REPEAT GEN_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[FUN_MAP_THM,I_THM]
   );

val ALL_EL_RSP = store_thm
   ("ALL_EL_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !l1 l2 P1 P2.
          (R ===> $=) P1 P2 /\ (LIST_REL R) l1 l2 ==>
          (ALL_EL P1 l1 = ALL_EL P2 l2)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Induct
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[ALL_EL,LIST_REL_def]
    THEN REWRITE_TAC[FUN_REL]
    THEN STRIP_TAC
    THEN MK_COMB_TAC
    THENL
      [ AP_TERM_TAC
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN FIRST_ASSUM ACCEPT_TAC,

        FIRST_ASSUM MATCH_MP_TAC
        THEN ASM_REWRITE_TAC[FUN_REL]
      ]
   );


val FOLDL_PRS = store_thm
   ("FOLDL_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !l f e. FOLDL f e l =
                 abs1 (FOLDL ((abs1 --> abs2 --> rep1) f)
                      (rep1 e)
                      (MAP rep2 l))`--),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN Induct
    THEN ASM_REWRITE_TAC[FOLDL,MAP,FUN_MAP_THM]
   );

val FOLDL_RSP = store_thm
   ("FOLDL_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !l1 l2 f1 f2 e1 e2.
          (R1 ===> R2 ===> R1) f1 f2 /\
             R1 e1 e2 /\ (LIST_REL R2) l1 l2 ==>
          R1 (FOLDL f1 e1 l1) (FOLDL f2 e2 l2)`--),
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Induct
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[FOLDL,LIST_REL_def]
    THEN REWRITE_TAC[FUN_REL]
    THEN STRIP_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN REPEAT CONJ_TAC (* 3 subgoals *)
    THEN TRY (FIRST_ASSUM ACCEPT_TAC)
    THEN DEP_ONCE_ASM_REWRITE_TAC[]
    THEN CONJ_TAC
    THEN FIRST_ASSUM ACCEPT_TAC
   );


val FOLDR_PRS = store_thm
   ("FOLDR_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !l f e. FOLDR f e l =
                 abs2 (FOLDR ((abs1 --> abs2 --> rep2) f)
                      (rep2 e)
                      (MAP rep1 l))`--),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN Induct
    THEN ASM_REWRITE_TAC[FOLDR,MAP,FUN_MAP_THM]
   );

val FOLDR_RSP = store_thm
   ("FOLDR_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !l1 l2 f1 f2 e1 e2.
          (R1 ===> R2 ===> R2) f1 f2 /\
             R2 e1 e2 /\ (LIST_REL R1) l1 l2 ==>
          R2 (FOLDR f1 e1 l1) (FOLDR f2 e2 l2)`--),
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN Induct
    THENL [ ALL_TAC, GEN_TAC ]
    THEN Induct
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[FOLDR,LIST_REL_def]
    THEN REWRITE_TAC[FUN_REL]
    THEN STRIP_TAC
    THEN DEP_ONCE_ASM_REWRITE_TAC[]
    THEN CONJ_TAC
    THEN TRY (FIRST_ASSUM ACCEPT_TAC)
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN REPEAT CONJ_TAC
    THEN FIRST_ASSUM ACCEPT_TAC
   );




val _ = export_theory();

val _ = print_theory_to_file "-" "quotient_list.lst";

val _ = html_theory "quotient_list";

