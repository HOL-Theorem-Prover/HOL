open HolKernel Parse boolLib;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;
infixr -->;


(* --------------------------------------------------------------------- *)
(* Lifting the lambda calculus syntax to the abstract level.             *)
(* Version 2.1.                                                          *)
(* Date: February 28, 2005                                               *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "quotient_option";

open prim_recTheory;
open combinTheory;
open optionTheory;
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




(* for OPTION_ABS or OPTION_REP, use OPTION_MAP abs or OPTION_MAP rep,
 as defined in theory "option". *)

val OPTION_MAP_I = store_thm
   ("OPTION_MAP_I",
    (--`OPTION_MAP I = (I : 'a option -> 'a option)`--),
    CONV_TAC FUN_EQ_CONV
    THEN Cases
    THEN REWRITE_TAC[OPTION_MAP_DEF,I_THM]
   );

(* Here is the definition of OPTION_REL: *)

val OPTION_REL_def =
    Define
      `(OPTION_REL R (NONE)        (NONE)        = T) /\
       (OPTION_REL R (SOME (x:'a)) (NONE)        = F) /\
       (OPTION_REL R (NONE)        (SOME (y:'a)) = F) /\
       (OPTION_REL R (SOME (x:'a)) (SOME (y:'a)) = R x y)`;

val OPTION_REL_EQ = store_thm
   ("OPTION_REL_EQ",
    (--`(OPTION_REL ($= : 'a->'a->bool)) = $=`--),
    CONV_TAC FUN_EQ_CONV
    THEN CONV_TAC (RAND_CONV (ABS_CONV FUN_EQ_CONV))
    THEN Cases
    THEN Cases
    THEN REWRITE_TAC[OPTION_REL_def,option_CLAUSES]
   );

val OPTION_EQUIV = store_thm
   ("OPTION_EQUIV",
    (--`!R:'a -> 'a -> bool. EQUIV R ==> EQUIV (OPTION_REL R)`--),
    GEN_TAC
    THEN REWRITE_TAC[EQUIV_def]
    THEN DISCH_TAC
    THEN Cases
    THEN Cases (* 4 subgoals *)
    THEN ASM_REWRITE_TAC[OPTION_REL_def]
    THEN CONV_TAC (RAND_CONV FUN_EQ_CONV)
    THENL
      [ DISCH_THEN (MP_TAC o SPEC ``NONE :'a option``)
        THEN ASM_REWRITE_TAC[OPTION_REL_def],

        DISCH_THEN (MP_TAC o SPEC ``NONE :'a option``)
        THEN ASM_REWRITE_TAC[OPTION_REL_def],

        EQ_TAC
        THENL
          [ STRIP_TAC
            THEN Cases
            THEN ASM_REWRITE_TAC[OPTION_REL_def],

            DISCH_THEN (MP_TAC o SPEC ``SOME x :'a option``)
            THEN ASM_REWRITE_TAC[OPTION_REL_def]
          ]
      ]
   );

val OPTION_QUOTIENT = store_thm
   ("OPTION_QUOTIENT",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         QUOTIENT (OPTION_REL R) (OPTION_MAP abs) (OPTION_MAP rep)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REWRITE_TAC[QUOTIENT_def]
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN IMP_RES_TAC QUOTIENT_REP_REFL
    THEN REPEAT CONJ_TAC
    THEN REPEAT Cases
    THEN ASM_REWRITE_TAC[OPTION_MAP_DEF,OPTION_REL_def,option_CLAUSES]
    THEN IMP_RES_THEN (fn th => CONV_TAC (LAND_CONV (REWR_CONV th)))
                      QUOTIENT_REL
    THEN REFL_TAC
   );




(* option theory: NONE, SOME, IS_NONE, IS_SOME *)

val NONE_PRS = store_thm
   ("NONE_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (NONE = (OPTION_MAP abs) NONE)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[OPTION_MAP_DEF]
   );

val NONE_RSP = store_thm
   ("NONE_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (OPTION_REL R) NONE NONE`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[OPTION_REL_def]
   );

val SOME_PRS = store_thm
   ("SOME_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (!x. SOME x = (OPTION_MAP abs) (SOME (rep x)))`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[OPTION_MAP_DEF]
   );

val SOME_RSP = store_thm
   ("SOME_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (!x y. R x y ==>
                (OPTION_REL R) (SOME x) (SOME y))`--),
    REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[OPTION_REL_def]
   );

val IS_SOME_PRS = store_thm
   ("IS_SOME_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (!x. IS_SOME x = IS_SOME (OPTION_MAP rep x))`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Cases
    THEN ASM_REWRITE_TAC[IS_SOME_DEF,OPTION_MAP_DEF]
   );

val IS_SOME_RSP = store_thm
   ("IS_SOME_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (!x y. OPTION_REL R x y ==>
                (IS_SOME x = IS_SOME y))`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT Cases
    THEN REWRITE_TAC[OPTION_REL_def,IS_SOME_DEF]
   );

val IS_NONE_PRS = store_thm
   ("IS_NONE_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (!x. IS_NONE x = IS_NONE (OPTION_MAP rep x))`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Cases
    THEN ASM_REWRITE_TAC[IS_NONE_DEF,OPTION_MAP_DEF]
   );

val IS_NONE_RSP = store_thm
   ("IS_NONE_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (!x y. OPTION_REL R x y ==>
                (IS_NONE x = IS_NONE y))`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT Cases
    THEN REWRITE_TAC[OPTION_REL_def,IS_NONE_DEF]
   );


val OPTION_MAP_PRS = store_thm
   ("OPTION_MAP_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a f. OPTION_MAP f a =
               OPTION_MAP abs2
                    (OPTION_MAP ((abs1 --> rep2) f) (OPTION_MAP rep1 a))`--),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN Cases
    THEN GEN_TAC
    THEN REWRITE_TAC[OPTION_MAP_DEF]
    THEN REWRITE_TAC[SOME_11]
    THEN REWRITE_TAC[FUN_MAP_THM]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val OPTION_MAP_RSP = store_thm
   ("OPTION_MAP_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a1 a2 f1 f2.
          (R1 ===> R2) f1 f2 /\ (OPTION_REL R1) a1 a2 ==>
          (OPTION_REL R2) (OPTION_MAP f1 a1) (OPTION_MAP f2 a2)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Cases
    THEN Cases
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[OPTION_MAP_DEF,OPTION_REL_def]
    THEN STRIP_TAC
    THEN IMP_RES_TAC FUN_REL_MP
   );




val _ = export_theory();

val _ = print_theory_to_file "-" "quotient_option.lst";

val _ = html_theory "quotient_option";

