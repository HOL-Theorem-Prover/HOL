open HolKernel Parse boolLib;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;
infixr -->;


(* --------------------------------------------------------------------- *)
(* Lifting the lambda calculus syntax to the abstract level.             *)
(* Version 2.1.                                                          *)
(* Date: February 28, 2005                                               *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "quotient_sum";

open prim_recTheory;
open combinTheory;
open sumTheory;
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



(* for SUM of ABS / REP functions, use infix ++, defined in
   src/sum/sumScript.sml. *)

(* for SUM of equivalence relations, use infix +++, defined here: *)

val _ = Lib.try add_infix("+++", 480, HOLgrammars.LEFT)

val SUM_REL_def = xDefine "SUM_REL"
       `(($+++ R1 R2) (INL (a1:'a)) (INL (a2:'a)) = R1 a1 a2) /\
        (($+++ R1 R2) (INR (b1:'b)) (INR (b2:'b)) = R2 b1 b2) /\
        (($+++ R1 R2) (INL a1) (INR b2) = F) /\
        (($+++ R1 R2) (INR b1) (INL a2) = F)`;

val SUM_REL_EQ = store_thm
   ("SUM_REL_EQ",
    (--`($= +++ $=) = ($= : 'a + 'b -> 'a + 'b -> bool)`--),
    CONV_TAC FUN_EQ_CONV
    THEN Cases
    THEN CONV_TAC FUN_EQ_CONV
    THEN Cases
    THEN REWRITE_TAC[SUM_REL_def,INR_INL_11,sum_distinct,sum_distinct1]
   );

val SUM_EQUIV = store_thm
   ("SUM_EQUIV",
    (--`!(R1:'a -> 'a -> bool) (R2:'b -> 'b -> bool).
            EQUIV R1 ==> EQUIV R2 ==> EQUIV (R1 +++ R2)`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[EQUIV_def]
    THEN REPEAT DISCH_TAC
    THEN Cases
    THEN Cases (* 4 subgoals *)
    THEN ASM_REWRITE_TAC[SUM_REL_def]
    THEN CONV_TAC (RAND_CONV FUN_EQ_CONV)
    THENL
      [ EQ_TAC
        THENL
          [ STRIP_TAC
            THEN Cases
            THEN ASM_REWRITE_TAC[SUM_REL_def],

            DISCH_THEN (MP_TAC o SPEC ``INL x :'a + 'b``)
            THEN ASM_REWRITE_TAC[SUM_REL_def]
          ],

        DISCH_THEN (MP_TAC o SPEC ``INL x' :'a + 'b``)
        THEN ASM_REWRITE_TAC[SUM_REL_def],

        DISCH_THEN (MP_TAC o SPEC ``INR y :'a + 'b``)
        THEN ASM_REWRITE_TAC[SUM_REL_def],

        EQ_TAC
        THENL
          [ STRIP_TAC
            THEN Cases
            THEN ASM_REWRITE_TAC[SUM_REL_def],

            DISCH_THEN (MP_TAC o SPEC ``INR y'' :'a + 'b``)
            THEN ASM_REWRITE_TAC[SUM_REL_def]
          ]
      ]
   );

val SUM_QUOTIENT = store_thm
   ("SUM_QUOTIENT",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         QUOTIENT (R1 +++ R2) (abs1 ++ abs2) (rep1 ++ rep2)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT CONJ_TAC
    THENL
      [ IMP_RES_TAC QUOTIENT_ABS_REP
        THEN Cases
        THEN ASM_REWRITE_TAC[SUM_MAP_def],

        IMP_RES_TAC QUOTIENT_REP_REFL
        THEN Cases
        THEN ASM_REWRITE_TAC[SUM_MAP_def,SUM_REL_def],

        REPEAT Cases
        THEN REWRITE_TAC[SUM_REL_def,SUM_MAP_def]
        THEN REWRITE_TAC[INR_INL_11,sum_distinct,GSYM sum_distinct]
        THEN IMP_RES_THEN
                 (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[th])))
                 QUOTIENT_REL
        THEN REFL_TAC
      ]
   );



(* sum theory: INL, INR, ISL, ISR, ++ *)

val INL_PRS = store_thm
   ("INL_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a. INL a = (abs1 ++ abs2) (INL (rep1 a))`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[SUM_MAP_def]
    THEN PURE_REWRITE_TAC[INR_INL_11]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val INL_RSP = store_thm
   ("INL_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a1 a2.
          R1 a1 a2 ==>
          (R1 +++ R2) (INL a1) (INL a2)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[SUM_REL_def]
   );

val INR_PRS = store_thm
   ("INR_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !b. INR b = (abs1 ++ abs2) (INR (rep2 b))`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[SUM_MAP_def]
    THEN PURE_REWRITE_TAC[INR_INL_11]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val INR_RSP = store_thm
   ("INR_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !b1 b2.
          R2 b1 b2 ==>
          (R1 +++ R2) (INR b1) (INR b2)`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[SUM_REL_def]
   );

val ISL_PRS = store_thm
   ("ISL_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a. ISL a = ISL ((rep1 ++ rep2) a)`--),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN Cases
    THEN PURE_REWRITE_TAC[SUM_MAP_def]
    THEN REWRITE_TAC[ISL]
   );

val ISL_RSP = store_thm
   ("ISL_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a1 a2.
          (R1 +++ R2) a1 a2 ==>
          (ISL a1 = ISL a2)`--),
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN Cases
    THEN Cases
    THEN REWRITE_TAC[SUM_REL_def,ISL]
   );

val ISR_PRS = store_thm
   ("ISR_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a. ISR a = ISR ((rep1 ++ rep2) a)`--),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN Cases
    THEN PURE_REWRITE_TAC[SUM_MAP_def]
    THEN REWRITE_TAC[ISR]
   );

val ISR_RSP = store_thm
   ("ISR_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a1 a2.
          (R1 +++ R2) a1 a2 ==>
          (ISR a1 = ISR a2)`--),
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN Cases
    THEN Cases
    THEN REWRITE_TAC[SUM_REL_def,ISR]
   );

(* OUTL and OUTR are not completely defined, so do not lift. *)

val SUM_MAP_PRS = store_thm
   ("SUM_MAP_PRS",
    (--`!R1 (abs1:'a -> 'e) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'f) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'g) rep3. QUOTIENT R3 abs3 rep3 ==>
        !R4 (abs4:'d -> 'h) rep4. QUOTIENT R4 abs4 rep4 ==>
         !f g. (f ++ g) =
               ((rep1 ++ rep3) --> (abs2 ++ abs4))
                   (((abs1 --> rep2) f) ++ ((abs3 --> rep4) g))`--),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN REPEAT GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN Cases
    THEN PURE_REWRITE_TAC[FUN_MAP_THM,SUM_MAP_def]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val SUM_MAP_RSP = store_thm
   ("SUM_MAP_RSP",
    (--`!R1 (abs1:'a -> 'e) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'f) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'g) rep3. QUOTIENT R3 abs3 rep3 ==>
        !R4 (abs4:'d -> 'h) rep4. QUOTIENT R4 abs4 rep4 ==>
         !f1 f2 g1 g2.
          (R1 ===> R2) f1 f2 /\ (R3 ===> R4) g1 g2 ==>
          ((R1 +++ R3) ===> (R2 +++ R4)) (f1 ++ g1) (f2 ++ g2)`--),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN POP_ASSUM MP_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN STRIP_TAC
    THEN Cases
    THEN Cases
    THEN ASM_REWRITE_TAC[SUM_REL_def,SUM_MAP_def]
   );





val _ = export_theory();

val _ = print_theory_to_file "-" "quotient_sum.lst";

val _ = html_theory "quotient_sum";

