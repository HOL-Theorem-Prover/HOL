open HolKernel Parse boolLib;

(* --------------------------------------------------------------------- *)
(* Lifting the lambda calculus syntax to the abstract level.             *)
(* Version 2.1.                                                          *)
(* Date: February 28, 2005                                               *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "quotient_pair";

open prim_recTheory;
open combinTheory;
open pairTheory;
open pairLib;
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




(* to create PROD (i.e., PAIR) ABS and REP functions, use infix ## *)
(*  See PAIR_MAP_THM, PAIR_MAP. *)

val PAIR_MAP_I = store_thm
   ("PAIR_MAP_I",
    (“(I ## I) = (I : 'a # 'b -> 'a # 'b)”),
    CONV_TAC FUN_EQ_CONV
    THEN Cases
    THEN REWRITE_TAC[PAIR_MAP_THM,I_THM]
   );

Theorem PAIR_REL = pairTheory.PAIR_REL
Theorem PAIR_REL_THM = pairTheory.PAIR_REL_THM
Theorem PAIR_REL_EQ = pairTheory.PAIR_REL_EQ

Theorem PAIR_EQUIV:
  !(R1:'a -> 'a -> bool) (R2:'b -> 'b -> bool).
    EQUIV R1 ==> EQUIV R2 ==> EQUIV (R1 ### R2)
Proof
  REPEAT GEN_TAC >> REWRITE_TAC[EQUIV_def, EQUIV_REFL_SYM_TRANS]
  >> simp[PAIR_REL_REFL] >> rpt strip_tac
  >- (irule $ iffLR PAIR_REL_SYM >> simp[EQ_IMP_THM, FORALL_AND_THM]) >>
  irule PAIR_REL_TRANS >> METIS_TAC[]
QED


val PAIR_QUOTIENT = store_thm
   ("PAIR_QUOTIENT",
    (“!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         QUOTIENT (R1 ### R2) (abs1 ## abs2) (rep1 ## rep2)”),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT CONJ_TAC
    THENL
      [ Cases
        THEN REWRITE_TAC[PAIR_MAP_THM]
        THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP,

        Cases
        THEN REWRITE_TAC[PAIR_MAP_THM,PAIR_REL_THM,PAIR_EQ]
        THEN IMP_RES_THEN REWRITE_THM QUOTIENT_REP_REFL,

        REPEAT Cases
        THEN REWRITE_TAC[PAIR_REL_THM,PAIR_MAP_THM,PAIR_EQ]
        THEN IMP_RES_THEN
                 (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[th])))
                 QUOTIENT_REL
        THEN PROVE_TAC[]
      ]
   );



(* Here are some definitional and well-formedness theorems
   for some standard polymorphic operators.
*)



(* pair theory: FST, SND, COMMA, CURRY, UNCURRY, ## *)

val FST_PRS = store_thm
   ("FST_PRS",
    (“!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !p. FST p = abs1 (FST ((rep1 ## rep2) p))”),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Cases
    THEN PURE_REWRITE_TAC[PAIR_MAP_THM,FST]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val FST_RSP = store_thm
   ("FST_RSP",
    (“!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !p1 p2.
          (R1 ### R2) p1 p2 ==> R1 (FST p1) (FST p2)”),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Cases
    THEN Cases
    THEN REWRITE_TAC[PAIR_REL_THM,FST]
    THEN STRIP_TAC
   );


val SND_PRS = store_thm
   ("SND_PRS",
    (“!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !p. SND p = abs2 (SND ((rep1 ## rep2) p))”),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Cases
    THEN PURE_REWRITE_TAC[PAIR_MAP_THM,SND]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val SND_RSP = store_thm
   ("SND_RSP",
    (“!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !p1 p2.
          (R1 ### R2) p1 p2 ==> R2 (SND p1) (SND p2)”),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN Cases
    THEN Cases
    THEN REWRITE_TAC[PAIR_REL_THM,SND]
    THEN STRIP_TAC
   );


val COMMA_PRS = store_thm
   ("COMMA_PRS",
    (“!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a b. (a,b) = (abs1 ## abs2) (rep1 a, rep2 b)”),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[PAIR_MAP_THM]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val COMMA_RSP = store_thm
   ("COMMA_RSP",
    (“!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !a1 a2 b1 b2.
          R1 a1 b1 /\ R2 a2 b2 ==>
          (R1 ### R2) (a1,a2) (b1,b2)”),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[PAIR_REL_THM]
   );


val CURRY_PRS = store_thm
   ("CURRY_PRS",
    (“!R1 (abs1:'a -> 'd) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'e) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'f) rep3. QUOTIENT R3 abs3 rep3 ==>
         !f a b. CURRY f a b =
                 abs3 (CURRY (((abs1 ## abs2) --> rep3) f)
                             (rep1 a) (rep2 b))”),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[CURRY_DEF]
    THEN PURE_REWRITE_TAC[FUN_MAP_THM]
    THEN PURE_ONCE_REWRITE_TAC[PAIR_MAP_THM]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val CURRY_RSP = store_thm
   ("CURRY_RSP",
    (“!R1 (abs1:'a -> 'd) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'e) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'f) rep3. QUOTIENT R3 abs3 rep3 ==>
         !f1 f2.
          ((R1 ### R2) ===> R3) f1 f2 ==>
          (R1 ===> R2 ===> R3) (CURRY f1) (CURRY f2)”),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[CURRY_DEF]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN PURE_REWRITE_TAC[PAIR_REL_THM]
    THEN CONJ_TAC
    THEN FIRST_ASSUM ACCEPT_TAC
   );


val UNCURRY_PRS = store_thm
   ("UNCURRY_PRS",
    (“!R1 (abs1:'a -> 'd) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'e) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'f) rep3. QUOTIENT R3 abs3 rep3 ==>
         !f p. UNCURRY f p =
               abs3 (UNCURRY ((abs1 --> abs2 --> rep3) f)
                             ((rep1 ## rep2) p))”),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN GEN_TAC
    THEN Cases
    THEN PURE_ONCE_REWRITE_TAC[PAIR_MAP_THM]
    THEN PURE_ONCE_REWRITE_TAC[UNCURRY_DEF]
    THEN PURE_REWRITE_TAC[FUN_MAP_THM]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val UNCURRY_RSP = store_thm
   ("UNCURRY_RSP",
    (“!R1 (abs1:'a -> 'd) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'e) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'f) rep3. QUOTIENT R3 abs3 rep3 ==>
         !f1 f2.
          (R1 ===> R2 ===> R3) f1 f2 ==>
          ((R1 ### R2) ===> R3) (UNCURRY f1) (UNCURRY f2)”),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN POP_ASSUM MP_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN DISCH_TAC
    THEN Cases
    THEN Cases
    THEN REWRITE_TAC[PAIR_REL_THM,UNCURRY_DEF]
    THEN STRIP_TAC
    THEN RES_TAC
   );


val PAIR_MAP_PRS = store_thm
   ("PAIR_MAP_PRS",
    (“!R1 (abs1:'a -> 'e) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'f) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'g) rep3. QUOTIENT R3 abs3 rep3 ==>
        !R4 (abs4:'d -> 'h) rep4. QUOTIENT R4 abs4 rep4 ==>
         !f g. (f ## g) =
               ((rep1 ## rep3) --> (abs2 ## abs4))
                   (((abs1 --> rep2) f) ## ((abs3 --> rep4) g))”),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN REPEAT GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN Cases
    THEN PURE_REWRITE_TAC[FUN_MAP_THM,PAIR_MAP_THM]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
   );

val PAIR_MAP_RSP = store_thm
   ("PAIR_MAP_RSP",
    (“!R1 (abs1:'a -> 'e) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'f) rep2. QUOTIENT R2 abs2 rep2 ==>
        !R3 (abs3:'c -> 'g) rep3. QUOTIENT R3 abs3 rep3 ==>
        !R4 (abs4:'d -> 'h) rep4. QUOTIENT R4 abs4 rep4 ==>
         !f1 f2 g1 g2.
          (R1 ===> R2) f1 f2 /\ (R3 ===> R4) g1 g2 ==>
          ((R1 ### R3) ===> (R2 ### R4)) (f1 ## g1) (f2 ## g2)”),
    REPEAT (REPEAT GEN_TAC THEN DISCH_TAC)
    THEN POP_ASSUM MP_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN STRIP_TAC
    THEN Cases
    THEN Cases
    THEN PURE_REWRITE_TAC[PAIR_REL_THM,PAIR_MAP_THM]
    THEN STRIP_TAC
    THEN CONJ_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN FIRST_ASSUM ACCEPT_TAC
   );




val _ = export_theory();

val _ = print_theory_to_file "-" "quotient_pair.lst";

val _ = html_theory "quotient_pair";
