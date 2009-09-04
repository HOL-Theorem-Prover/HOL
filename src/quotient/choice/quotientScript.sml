open HolKernel Parse boolLib;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;
infixr -->;


(* --------------------------------------------------------------------- *)
(* Definitions and theorems for higher order quotients package.          *)
(* Version that attempts to avoid the use of the Axiom of Choice.        *)
(*                                                                       *)
(* Fails in that from FUN_QUOTIENT can be derived the existance of       *)
(* an operator satisfying the axiom of the Hilbert choice operator.      *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "quotient";

(*
load "dep_rewrite";
*)

open prim_recTheory;
open combinTheory;
open pairTheory;
open pairLib;
open sumTheory;
open listTheory;
open rich_listTheory;
open optionTheory;
open listLib;
open pred_setTheory;
open bossLib;
open res_quanTheory;
open res_quanLib;
open dep_rewrite;


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
(*  Function (ty1 -> ty2)  (\x. f x)  (rep1 --> abs2)    (R1 ===> R2)  *)
(*                                                                     *)
(* =================================================================== *)



val QUOTIENT_def =
    Define
      `QUOTIENT R (abs:'a->'b) =
        (!a. ?r. R r r /\ (abs r = a)) /\
        (!r s. R r s = R r r /\ R s s /\ (abs r = abs s))`;

val QUOTIENT_REP = store_thm
   ("QUOTIENT_REP",
    (--`!R (abs:'a->'b). QUOTIENT R abs ==> (!a. ?r. R r r /\ (abs r = a))`--),
    REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT STRIP_TAC
   );

val QUOTIENT_REL = store_thm
   ("QUOTIENT_REL",
    (--`!R (abs:'a->'b). QUOTIENT R abs ==>
            (!r s. R r s = R r r /\ R s s /\ (abs r = abs s))`--),
    REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT STRIP_TAC
   );

val QUOTIENT_REL_ABS = store_thm
   ("QUOTIENT_REL_ABS",
    (--`!R (abs:'a->'b). QUOTIENT R abs ==>
            (!r s. R r s ==> (abs r = abs s))`--),
    REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT STRIP_TAC
    THEN RES_TAC
   );

val QUOTIENT_REL_ABS_EQ = store_thm
   ("QUOTIENT_REL_ABS_EQ",
    (--`!R (abs:'a->'b). QUOTIENT R abs ==>
            (!r s. R r r ==> R s s ==>
                   (R r s = (abs r = abs s)))`--),
    REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN POP_ASSUM (fn th => REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[th])
    THEN ASM_REWRITE_TAC[]
   );




val IDENTITY_EQUIV = store_thm
   ("IDENTITY_EQUIV",
    (--`!x y:'a. (x = y) = ($= x = $= y)`--),
    REPEAT GEN_TAC
    THEN EQ_TAC
    THEN DISCH_THEN REWRITE_THM
   );

val IDENTITY_QUOTIENT = store_thm
   ("IDENTITY_QUOTIENT",
    (--`QUOTIENT $= (I:'a->'a)`--),
    REWRITE_TAC[QUOTIENT_def]
    THEN REWRITE_TAC[I_THM]
    THEN GEN_TAC
    THEN EXISTS_TAC (--`a:'a`--)
    THEN REFL_TAC
   );



val EQUIV_REFL_SYM_TRANS = store_thm
   ("EQUIV_REFL_SYM_TRANS",
    (--`!R.
         (!x y:'a. R x y = (R x = R y))
         =
         (!x. R x x) /\
         (!x y. R x y ==> R y x) /\
         (!x y z. R x y /\ R y z ==> R x z)`--),
    GEN_TAC
    THEN EQ_TAC
    THEN STRIP_TAC
    THEN REPEAT CONJ_TAC
    THEN REPEAT GEN_TAC
    THENL (* 4 subgoals *)
      [
        PURE_ASM_REWRITE_TAC[]
        THEN REFL_TAC,

        PURE_ASM_REWRITE_TAC[]
        THEN MATCH_ACCEPT_TAC EQ_SYM,

        PURE_ASM_REWRITE_TAC[]
        THEN MATCH_ACCEPT_TAC EQ_TRANS,

        CONV_TAC (RAND_CONV FUN_EQ_CONV)
        THEN EQ_TAC
        THEN DISCH_TAC
        THENL
          [ GEN_TAC
            THEN EQ_TAC
            THEN DISCH_TAC
            THEN RES_TAC
            THEN RES_TAC,

            PURE_ASM_REWRITE_TAC[]
          ]
      ]
   );


val QUOTIENT_SYM = store_thm
   ("QUOTIENT_SYM",
    (--`!R (abs:'a -> 'b). QUOTIENT R abs ==>
         !x y. R x y ==> R y x`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
   );

val QUOTIENT_TRANS = store_thm
   ("QUOTIENT_TRANS",
    (--`!R (abs:'a -> 'b). QUOTIENT R abs ==>
         !x y z. R x y /\ R y z ==> R x z`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
   );




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
    (--`!R. (!x y:'a. R x y = (R x = R y)) ==>
            (!x y. LIST_REL R x y = (LIST_REL R x = LIST_REL R y))`--),
    GEN_TAC
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
    (--`!R (abs:'a -> 'b). QUOTIENT R abs ==>
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
    (--`!R (abs:'a -> 'b). QUOTIENT R abs ==>
         QUOTIENT (LIST_REL R) (MAP abs)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[QUOTIENT_def]
    THEN REPEAT CONJ_TAC
    THENL (* 2 subgoals *)
      [ IMP_RES_TAC QUOTIENT_REP
        THEN Induct
        THEN PROVE_TAC[MAP,LIST_REL_def],

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
    (--`!R. (!x y:'a. R x y = (R x = R y)) ==>
            (!x y. OPTION_REL R x y = (OPTION_REL R x = OPTION_REL R y))`--),
    GEN_TAC
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
    (--`!R (abs:'a -> 'b). QUOTIENT R abs ==>
         QUOTIENT (OPTION_REL R) (OPTION_MAP abs)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REWRITE_TAC[QUOTIENT_def]
    THEN IMP_RES_TAC QUOTIENT_REP
    THEN CONJ_TAC
    THENL
      [ Cases
        THENL
          [ EXISTS_TAC (--`NONE:'a option`--)
            THEN REWRITE_TAC[OPTION_MAP_DEF,OPTION_REL_def,option_CLAUSES],

            POP_ASSUM (STRIP_ASSUME_TAC o SPEC (--`x:'b`--))
            THEN EXISTS_TAC (--`SOME r:'a option`--)
            THEN ASM_REWRITE_TAC[OPTION_MAP_DEF,OPTION_REL_def,option_CLAUSES]
          ],

        REPEAT Cases
        THEN ASM_REWRITE_TAC[OPTION_MAP_DEF,OPTION_REL_def,option_CLAUSES]
        THEN IMP_RES_THEN (fn th => CONV_TAC (LAND_CONV (REWR_CONV th)))
                          QUOTIENT_REL
        THEN REFL_TAC
      ]
   );


(* to create PROD (i.e., PAIR) ABS and REP functions, use infix ## *)
(*  See PAIR_MAP_THM, PAIR_MAP. *)

val PAIR_MAP_I = store_thm
   ("PAIR_MAP_I",
    (--`(I ## I) = (I : 'a # 'b -> 'a # 'b)`--),
    CONV_TAC FUN_EQ_CONV
    THEN Cases
    THEN REWRITE_TAC[PAIR_MAP_THM,I_THM]
   );

(* just like RPROD_DEF, except infix: *)

val PAIR_REL =
    new_infixr_definition
    ("PAIR_REL",
     (--`$### R1 R2 = \(a:'a,b:'b) (c:'c,d:'d). R1 a c /\ R2 b d`--),
     450);

val PAIR_REL_THM = store_thm
   ("PAIR_REL_THM",
    (--`!R1 R2 (a:'a) (b:'b) (c:'c) (d:'d).
         (R1 ### R2) (a,b) (c,d) = R1 a c /\ R2 b d`--),
    REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[PAIR_REL]
    THEN GEN_BETA_TAC
    THEN REFL_TAC
   );

val PAIR_REL_EQ = store_thm
   ("PAIR_REL_EQ",
    (--`($= ### $=) = ($= : 'a # 'b -> 'a # 'b -> bool)`--),
    CONV_TAC FUN_EQ_CONV
    THEN Cases
    THEN CONV_TAC FUN_EQ_CONV
    THEN Cases
    THEN REWRITE_TAC[PAIR_REL_THM,PAIR_EQ]
   );

val PAIR_REL_REFL = store_thm
   ("PAIR_REL_REFL",
    (--`!R1 R2. (!x y:'a. R1 x y = (R1 x = R1 y)) /\
                (!x y:'b. R2 x y = (R2 x = R2 y)) ==>
                !x. (R1 ### R2) x x`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN Cases
    THEN REWRITE_TAC[PAIR_REL_THM]
    THEN ASM_REWRITE_TAC[]
   );

val PAIR_EQUIV = store_thm
   ("PAIR_EQUIV",
    (--`!R1 R2. (!x y:'a. R1 x y = (R1 x = R1 y)) ==>
                (!x y:'b. R2 x y = (R2 x = R2 y)) ==>
                (!x y. (R1 ### R2) x y = ((R1 ### R2) x = (R1 ### R2) y))`--),
    REPEAT GEN_TAC
    THEN REPEAT DISCH_TAC
    THEN Cases
    THEN Cases
    THEN REWRITE_TAC[PAIR_REL_THM]
    THEN CONV_TAC (RAND_CONV FUN_EQ_CONV)
    THEN EQ_TAC
    THENL
      [ STRIP_TAC
        THEN Cases
        THEN REWRITE_TAC[PAIR_REL_THM]
        THEN PROVE_TAC[],

        DISCH_THEN (MP_TAC o GEN ``a:'a`` o GEN ``b:'b``
                               o SPEC ``(a:'a, b:'b)``)
        THEN REWRITE_TAC[PAIR_REL_THM]
        THEN IMP_RES_TAC PAIR_REL_REFL
        THEN PROVE_TAC[]
      ]
   );

val PAIR_QUOTIENT = store_thm
   ("PAIR_QUOTIENT",
    (--`!R1 (abs1:'a -> 'c). QUOTIENT R1 abs1 ==>
        !R2 (abs2:'b -> 'd). QUOTIENT R2 abs2 ==>
         QUOTIENT (R1 ### R2) (abs1 ## abs2)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[QUOTIENT_def]
    THEN CONJ_TAC
    THENL
      [ Cases
        THEN IMP_RES_TAC QUOTIENT_REP
        THEN FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC ``q:'c``)
        THEN FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC ``r:'d``)
        THEN EXISTS_TAC ``(r':'a,r'':'b)``
        THEN ASM_REWRITE_TAC[PAIR_MAP,PAIR_REL_THM,PAIR_EQ],

        REPEAT Cases
        THEN REWRITE_TAC[PAIR_REL_THM,PAIR_MAP_THM,PAIR_EQ]
        THEN IMP_RES_THEN
                 (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[th])))
                 QUOTIENT_REL
        THEN PROVE_TAC[]
      ]
   );



(* for SUM of ABS / REP functions, use infix ++, defined here: *)

val _ = Lib.try add_infix("++", 450, HOLgrammars.RIGHT)

val SUM_MAP_def = xDefine "SUM_MAP"
       `(($++ f g) (INL (a:'a)) = INL ((f a):'c)) /\
        (($++ f g) (INR (b:'b)) = INR ((g b):'d))`;

val SUM_MAP = store_thm
   ("SUM_MAP",
    (--`!f g (z:'a + 'b).
         (f ++ g) z = (if ISL z then INL (f (OUTL z))
                                else INR (g (OUTR z))) :'c + 'd`--),
    GEN_TAC
    THEN GEN_TAC
    THEN Cases
    THEN REWRITE_TAC[SUM_MAP_def,ISL,OUTL,OUTR]
   );

val SUM_MAP_CASE = store_thm
   ("SUM_MAP_CASE",
    (--`!f g (z:'a + 'b).
         (f ++ g) z = sum_case (INL o f) (INR o g) z :'c + 'd`--),
    GEN_TAC
    THEN GEN_TAC
    THEN Cases
    THEN REWRITE_TAC[SUM_MAP_def,sum_case_def,o_THM]
   );

val SUM_MAP_I = store_thm
   ("SUM_MAP_I",
    (--`(I ++ I) = (I : 'a + 'b -> 'a + 'b)`--),
    CONV_TAC FUN_EQ_CONV
    THEN Cases
    THEN REWRITE_TAC[SUM_MAP_def,I_THM]
   );

(* for SUM of equivalence relations, use infix +++, defined here: *)

val _ = Lib.try add_infix("+++", 450, HOLgrammars.RIGHT)

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
    (--`!R1 R2. (!x y:'a. R1 x y = (R1 x = R1 y)) ==>
                (!x y:'b. R2 x y = (R2 x = R2 y)) ==>
                (!x y. (R1 +++ R2) x y = ((R1 +++ R2) x = (R1 +++ R2) y))`--),
    REPEAT GEN_TAC
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
    (--`!R1 (abs1:'a -> 'c). QUOTIENT R1 abs1 ==>
        !R2 (abs2:'b -> 'd). QUOTIENT R2 abs2 ==>
         QUOTIENT (R1 +++ R2) (abs1 ++ abs2)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[QUOTIENT_def]
    THEN CONJ_TAC
    THENL
      [ IMP_RES_TAC QUOTIENT_REP
        THEN Cases
        THENL
          [ FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC ``x:'c``)
            THEN EXISTS_TAC ``INL r : 'a + 'b``,

            FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC ``y:'d``)
            THEN EXISTS_TAC ``INR r : 'a + 'b``
          ]
        THEN ASM_REWRITE_TAC[SUM_REL_def,SUM_MAP_def],

        REPEAT Cases
        THEN REWRITE_TAC[SUM_REL_def,SUM_MAP_def]
        THEN REWRITE_TAC[INR_INL_11,sum_distinct,GSYM sum_distinct]
        THEN IMP_RES_THEN
                 (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[th])))
                 QUOTIENT_REL
        THEN REFL_TAC
      ]
   );



(* FUNCTIONS: *)

val IMAGE_I = store_thm
   ("IMAGE_I",
    (--`(IMAGE (I:'a->'a)) = I`--),
    ONCE_REWRITE_TAC[FUN_EQ_THM]
    THEN REWRITE_TAC[EXTENSION]
    THEN REWRITE_TAC[IN_IMAGE,I_THM]
    THEN REPEAT GEN_TAC
    THEN EQ_TAC
    THEN STRIP_TAC
    THEN TRY (EXISTS_TAC ``x':'a``)
    THEN ASM_REWRITE_TAC[]
   );

val EQ_SING = store_thm
   ("EQ_SING",
    (--`!x. $= (x:'a) = {x}`--),
    REWRITE_TAC[EXTENSION,IN_SING]
    THEN REWRITE_TAC[SPECIFICATION]
    THEN MATCH_ACCEPT_TAC EQ_SYM_EQ
   );

val IMAGE_SING = store_thm
   ("IMAGE_SING",
    (--`!(f:'a->'b) x. IMAGE f {x} = {f x}`--),
    REWRITE_TAC[EXTENSION,IN_IMAGE,IN_SING]
    THEN REPEAT GEN_TAC
    THEN EQ_TAC
    THEN STRIP_TAC
    THEN TRY (EXISTS_TAC ``x:'a``)
    THEN ASM_REWRITE_TAC[]
   );

val SELECT1_EXISTS = TAC_PROOF(([],
    (--`?f. !P. !(x:'a). P x ==> (!y. P y ==> (x = y)) ==> P (f P)`--)),
    EXISTS_TAC ``$@ :('a -> bool) -> 'a``
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SELECT_AX
   );

local
open Rsyntax
in
val SELECT1_DEF =
    new_specification
    {name = "SELECT1_DEF",
     consts = [{const_name = "@!", fixity = Binder}],
     sat_thm = SELECT1_EXISTS}

val _ = Parse.add_binder("@!", 0)
end;

val SELECT1_SING = store_thm
   ("SELECT1_SING",
    (--`!x:'a. $@! {x} = x`--),
    GEN_TAC
    THEN MP_TAC (SPEC ``x:'a`` (ISPEC ``$= (x:'a)`` SELECT1_DEF))
    THEN REWRITE_TAC[GSYM EQ_SING]
    THEN DISCH_THEN (REWRITE_THM o GSYM)
   );

val THE_LEAST_NUM_IS_ZERO = TAC_PROOF(([],
    (--`(@!n. !m. n <= m) = 0`--)),
    MP_TAC (SPEC ``0`` (ISPEC ``\n. !m. n <= m`` SELECT1_DEF))
    THEN BETA_TAC
    THEN CONV_TAC (DEPTH_CONV RIGHT_IMP_FORALL_CONV)
    THEN DISCH_THEN (MP_TAC o SPEC ``0``)
    THEN REWRITE_TAC[arithmeticTheory.LESS_EQ_0, AND_IMP_INTRO]
    THEN DISCH_THEN MATCH_MP_TAC
    THEN REWRITE_TAC[arithmeticTheory.ZERO_LESS_EQ]
    THEN Cases
    THEN REWRITE_TAC[]
    THEN DISCH_THEN (MP_TAC o SPEC ``0``)
    THEN REWRITE_TAC[arithmeticTheory.NOT_SUC_LESS_EQ_0]
   );

(* version using skolemization, which secretly involves @:

val CONTENTS_EXISTS1 = TAC_PROOF(([],
    (--`!P. ?e. !(x:'a). P x ==> (!y. P y ==> (x = y)) ==> P e`--)),
    GEN_TAC
    THEN ASM_CASES_TAC ``?z:'a. P z``
    THENL
      [ POP_ASSUM STRIP_ASSUME_TAC
        THEN EXISTS_TAC ``z:'a``
        THEN ASM_REWRITE_TAC[],

        POP_ASSUM (ASSUME_TAC o CONV_RULE NOT_EXISTS_CONV)
        THEN ASM_REWRITE_TAC[]
      ]
   );

val CONTENTS_EXISTS = CONV_RULE SKOLEM_CONV CONTENTS_EXISTS1;

val CONTENTS_DEF =
    new_specification
    {name = "CONTENTS_DEF",
     consts = [{const_name = "CONTENTS", fixity = Prefix}],
     sat_thm = CONTENTS_EXISTS};

*)

(* for ABS of functions,
   use ((abs1 // R1) --> abs2) *)

val _ = hide "//";

val FUN_REP =
    new_infixr_definition
    ("FUN_REP",
     (--`$// (f:'a->'b) R =
         \a r. R r r /\ (f r = a)`--),
     450);

val FUN_REP_THM = store_thm
   ("FUN_REP_THM",
    (--`!(f:'a -> 'b) R a r.
         (f // R) a r = R r r /\ (f r = a)`--),
    REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[FUN_REP]
    THEN BETA_TAC
    THEN REFL_TAC
   );

val FUN_REP_ELEM = store_thm
   ("FUN_REP_ELEM",
    (--`!(f:'a -> 'b) R r.
         r IN (f // R) (f r) = R r r`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[SPECIFICATION,FUN_REP_THM]
   );

val FUN_REP_IDENTITY = store_thm
   ("FUN_REP_IDENTITY",
    (--`(I:'a->'a // $=) = $=`--),
    REWRITE_TAC[FUN_EQ_THM,FUN_REP_THM,I_THM]
    THEN MATCH_ACCEPT_TAC EQ_SYM_EQ
   );

val _ = hide "-->";

val FUN_MAP =
    new_infixr_definition
    ("FUN_MAP",
     (--`$--> (rep:'c->'a->bool) (abs:'b->'d) =
            \h x. $@! (IMAGE abs (IMAGE h (rep x)))`--),
     450);


val FUN_MAP_THM = store_thm
   ("FUN_MAP_THM",
    (--`!(rep:'c -> 'a -> bool) (abs:'b -> 'd) h x.
         (rep --> abs) h x = $@! (IMAGE abs (IMAGE h (rep x)))`--),
    REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[FUN_MAP]
    THEN BETA_TAC
    THEN REFL_TAC
   );

val FUN_MAP_EQ_I = store_thm
   ("FUN_MAP_EQ_I",
    (--`(($= :'a->'a->bool) --> (I:'b->'b)) = I`--),
    REPEAT (CONV_TAC FUN_EQ_CONV ORELSE GEN_TAC)
    THEN REWRITE_TAC[FUN_MAP_THM]
    THEN REWRITE_TAC[IMAGE_I,I_THM]
    THEN REWRITE_TAC[EQ_SING,IMAGE_SING,SELECT1_SING]
    THEN ONCE_REWRITE_TAC[GSYM SPECIFICATION]
    THEN REWRITE_TAC[IN_SING]
   );



(* The strong version of FUN_REL: *)

val FUN_REL =
    new_infixr_definition
    ("FUN_REL",
     (--`$===> (R1:'a->'a->bool) (R2:'b->'b->bool) f g =
           !x y. R1 x y ==> R2 (f x) (g y)`--),
     450);

(* NOTE: R1 ===> R2 is NOT an equivalence relation, but a partial
         equivalence relation, and it does satisfy a quotient theorem. *)


val FUN_REL_EQ = store_thm
   ("FUN_REL_EQ",
    (--`(($= :'a -> 'a -> bool) ===> ($= :'b -> 'b -> bool)) = $=`--),
    CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[FUN_REL]
    THEN CONV_TAC (RAND_CONV FUN_EQ_CONV)
    THEN PROVE_TAC[]
   );

val IMAGE_o = store_thm
   ("IMAGE_o",
    (--`!(f:'b->'c) g (s:'a -> bool).
           IMAGE f (IMAGE g s) = IMAGE (f o g) s`--),
    REWRITE_TAC[EXTENSION]
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[IN_IMAGE,o_THM]
    THEN PROVE_TAC[]
   );

val SELECT1_IMAGE = store_thm
   ("SELECT1_IMAGE",
    (--`!(f:'a->'b) s x.
           x IN s ==>
           (!x y. x IN s /\ y IN s ==> (f x = f y)) ==>
           ($@! (IMAGE f s) = f x)`--),
    REPEAT STRIP_TAC
    THEN MP_TAC (SPEC ``(f:'a->'b) x``
                  (ISPEC ``IMAGE (f:'a->'b) s`` SELECT1_DEF))
    THEN REWRITE_TAC[REWRITE_RULE[SPECIFICATION] IN_IMAGE]
    THEN SUBGOAL_THEN ``?x'. ((f:'a->'b) x = f x') /\ s x'`` REWRITE_THM
    THENL
      [ EXISTS_TAC ``x:'a``
        THEN REWRITE_TAC[]
        THEN ASM_REWRITE_TAC[GSYM SPECIFICATION],

        ALL_TAC
      ]
    THEN SUBGOAL_THEN ``!y:'b. (?x:'a. (y = f x) /\ s x) ==> (f x = y)``
               REWRITE_THM
    (* 2 subgoals, which are both solved by the following tactic: *)
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN ASM_REWRITE_TAC[SPECIFICATION]
   );


val FUN_REP_MAP = store_thm
   ("FUN_REP_MAP",
    (--`!R1 (abs1:'a -> 'c) R2 (abs2:'b -> 'd) a r.
         QUOTIENT R1 abs1 ==>
         QUOTIENT R2 abs2 ==>
         (((R1 ===> R2) r r /\ (((abs1 // R1) --> abs2) r = a))  =
          (!x. R1 x x ==> (abs2 // R2) (a (abs1 x)) (r x))         )`--),
    REPEAT GEN_TAC
    THEN DISCH_TAC
    THEN DISCH_TAC
    THEN REWRITE_TAC[FUN_EQ_THM]
    THEN REWRITE_TAC[FUN_REL,FUN_REP_THM,FUN_MAP_THM]
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ FIRST_ASSUM MATCH_MP_TAC
        THEN FIRST_ASSUM ACCEPT_TAC,

        EVERY_ASSUM (ONCE_REWRITE_THM o GSYM)
        THEN REWRITE_TAC[IMAGE_o]
        THEN IMP_RES_THEN (ASSUME_TAC o ISPEC ``abs1:'a -> 'c``) FUN_REP_ELEM
        THEN IMP_RES_THEN (fn th => DEP_REWRITE_TAC[th]) SELECT1_IMAGE
        THEN REWRITE_TAC[o_THM]
        THEN REWRITE_TAC[SPECIFICATION,FUN_REP_THM]
        THEN REPEAT STRIP_TAC
        THEN IMP_RES_THEN (fn th => TRY (MATCH_MP_TAC th)) QUOTIENT_REL_ABS
        THEN FIRST_ASSUM MATCH_MP_TAC
        THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
        THEN ASM_REWRITE_TAC[],

        POP_ASSUM MP_TAC
        THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
        THEN REPEAT STRIP_TAC
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        REWRITE_TAC[IMAGE_o]
        THEN IMP_RES_TAC QUOTIENT_REP
        THEN FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC ``x:'c``)
        THEN POP_ASSUM (REWRITE_THM o SYM)
        THEN IMP_RES_THEN (ASSUME_TAC o ISPEC ``abs1:'a -> 'c``) FUN_REP_ELEM
        THEN IMP_RES_THEN (fn th => DEP_REWRITE_TAC[th]) SELECT1_IMAGE
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[o_THM]
        THEN REWRITE_TAC[SPECIFICATION,FUN_REP_THM]
        THEN REPEAT STRIP_TAC
        THEN IMP_RES_THEN (fn th => TRY (MATCH_MP_TAC th)) QUOTIENT_REL_ABS
        THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[]
      ]
   );



val FUN_QUOTIENT = store_thm
   ("FUN_QUOTIENT",
    (--`!R1 (abs1:'a -> 'c). QUOTIENT R1 abs1 ==>
        !R2 (abs2:'b -> 'd). QUOTIENT R2 abs2 ==>
         QUOTIENT (R1 ===> R2) ((abs1 // R1) --> abs2)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[QUOTIENT_def]
    THEN CONJ_TAC
    THENL (* 2 subgoals *)
      [

        GEN_TAC
        THEN IMP_RES_THEN MP_TAC QUOTIENT_REP
(* WARNING!!! The next line uses the AXIOM OF CHOICE!!! *)
        THEN CONV_TAC (ONCE_DEPTH_CONV SKOLEM_CONV)
        THEN REPEAT STRIP_TAC
        THEN EXISTS_TAC ``(r':'d->'b) o a o (abs1:'a->'c)``
        THEN REWRITE_TAC[FUN_EQ_THM]
        THEN ASM_REWRITE_TAC[FUN_REL,FUN_MAP_THM,FUN_REP_THM,o_THM]
        THEN CONJ_TAC
        THENL
          [ IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
            THEN REPEAT GEN_TAC
            THEN STRIP_TAC
            THEN ASM_REWRITE_TAC[],

            GEN_TAC
            THEN REWRITE_TAC[IMAGE_o]
            THEN FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC ``x:'c``)
            THEN IMP_RES_THEN (MP_TAC o ISPEC ``abs1:'a -> 'c``) FUN_REP_ELEM
            THEN ASM_REWRITE_TAC[]
            THEN DISCH_TAC
            THEN IMP_RES_THEN (fn th => DEP_REWRITE_TAC[th]) SELECT1_IMAGE
            THEN ASM_REWRITE_TAC[o_THM]
            THEN REWRITE_TAC[SPECIFICATION,FUN_REP_THM]
            THEN REPEAT STRIP_TAC
            THEN ASM_REWRITE_TAC[]
          ],

        REPEAT GEN_TAC
        THEN CONV_TAC (RAND_CONV (RAND_CONV (RAND_CONV FUN_EQ_CONV)))
        THEN REWRITE_TAC[FUN_REL]
        THEN EQ_TAC
        THEN REPEAT STRIP_TAC
        THENL (* 4 subgoals *)
          [ PROVE_TAC[QUOTIENT_REL],

            PROVE_TAC[QUOTIENT_REL],

            REWRITE_TAC[FUN_MAP_THM]
            THEN AP_TERM_TAC
            THEN REWRITE_TAC[IMAGE_o]
            THEN REWRITE_TAC[EXTENSION,IN_IMAGE]
            THEN REWRITE_TAC[SPECIFICATION,FUN_REP_THM]
            THEN X_GEN_TAC ``y:'d``
            THEN REWRITE_TAC[o_THM]
            THEN EQ_TAC
            THEN STRIP_TAC
            THEN PROVE_TAC[QUOTIENT_REL],

            POP_ASSUM MP_TAC
            THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
            THEN POP_ASSUM MP_TAC
            THEN REWRITE_TAC[FUN_MAP_THM,IMAGE_o]
            THEN STRIP_TAC
            THEN STRIP_TAC
            THEN RES_THEN REWRITE_THM
            THEN FIRST_ASSUM (MP_TAC o SPEC ``(abs1:'a -> 'c) x``)
            THEN IMP_RES_THEN (ASSUME_TAC o ISPEC ``abs1:'a->'c``) FUN_REP_ELEM
            THEN IMP_RES_THEN (fn th => DEP_REWRITE_TAC[th]) SELECT1_IMAGE
            THEN REWRITE_TAC[o_THM,SPECIFICATION,FUN_REP_THM]
            THEN REPEAT STRIP_TAC
            THEN ASM_REWRITE_TAC[]
            THEN IMP_RES_THEN (fn th => TRY (MATCH_MP_TAC th)) QUOTIENT_REL_ABS
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
            THEN ASM_REWRITE_TAC[]
          ]
      ]
   );



val ABSTRACTION_QUOTIENT = store_thm
   ("ABSTRACTION_QUOTIENT",
    (--`!f:'a->'b. ONTO f ==> QUOTIENT (\r s. f r = f s) f`--),
    GEN_TAC
    THEN REWRITE_TAC[ONTO_DEF,QUOTIENT_def]
    THEN BETA_TAC
    THEN REWRITE_TAC[]
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM (STRIP_ASSUME_TAC o SPEC ``a:'b``)
    THEN EXISTS_TAC ``x:'a``
    THEN FIRST_ASSUM (ACCEPT_TAC o SYM)
   );

val PARTIAL_ABSTRACTION_QUOTIENT = store_thm
   ("PARTIAL_ABSTRACTION_QUOTIENT",
    (--`!(f:'a->'b) P.
          (!a. ?r. P r /\ (f r = a)) ==>
          QUOTIENT (\r s. P r /\ P s /\ (f r = f s)) f`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[ONTO_DEF,QUOTIENT_def]
    THEN BETA_TAC
    THEN REWRITE_TAC[]
   );

local
    val ith = INST_TYPE [alpha |-> delta] IDENTITY_QUOTIENT
    val f_  = ``f:'b -> 'd``
    val ath = UNDISCH (ISPEC f_ ABSTRACTION_QUOTIENT)
    val fth = MATCH_MP (MATCH_MP FUN_QUOTIENT ith) ath
    val eth = SPEC ``I:'d->'d`` (MATCH_MP QUOTIENT_REP fth)
    val th1 = BETA_RULE (REWRITE_RULE[FUN_REL,FUN_REP_IDENTITY,FUN_MAP] eth)
    val th2 = REWRITE_RULE [GSYM EQ_SING] (REWRITE_RULE[EQ_SING,IMAGE_SING,SELECT1_SING] th1)
in
    val ONTO_FUN_EXISTS_CHOICE = GEN_ALL (DISCH_ALL th2)
end;

val ONTO_FUNCTION_INVERSE = store_thm
   ("ONTO_FUNCTION_INVERSE",
    (--`!(f :'a -> 'b). ONTO f ==> ?g. f o g = I`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC ONTO_FUN_EXISTS_CHOICE
    THEN POP_ASSUM MP_TAC
    THEN REWRITE_TAC[FUN_EQ_THM,o_THM,I_THM]
    THEN BETA_TAC
    THEN DISCH_TAC
    THEN EXISTS_TAC ``r:'b -> 'a``
    THEN FIRST_ASSUM ACCEPT_TAC
   );

(*
   ONTO_FUNCTION_INVERSE:  |- !f. ONTO f ==> ?g. f o g = I
*)

val ONTO_PARTIAL_FUNCTION = store_thm
   ("ONTO_PARTIAL_FUNCTION",
    (--`!Q. ?(P,a:'a). (P = Q) /\ ((?x. P x) ==> P a)`--),
    GEN_TAC
    THEN ASM_CASES_TAC ``?x:'a. Q x``
    THEN POP_ASSUM STRIP_ASSUME_TAC
    THEN PairRules.PEXISTS_TAC ``(Q:'a->bool, x:'a)``
    THEN ASM_REWRITE_TAC[]
   );

val ONTO_PARTIAL_FUNCTION1 = store_thm
   ("ONTO_PARTIAL_FUNCTION1",
    (--`!Q. ?p. ((?x:'a. FST p x) ==> FST p (SND p)) /\ (FST p = Q)`--),
    GEN_TAC
    THEN PairRules.PSTRIP_ASSUME_TAC (SPEC_ALL ONTO_PARTIAL_FUNCTION)
    THEN PairRules.PEXISTS_TAC ``(P:'a -> bool, a:'a)``
    THEN REWRITE_TAC[FST,SND]
    THEN CONJ_TAC
    THEN FIRST_ASSUM ACCEPT_TAC
   );

local
    val ith = INST_TYPE [alpha |-> (alpha --> bool)] IDENTITY_QUOTIENT
    val f1  = ``FST:(('a -> bool) # 'a) -> ('a -> bool)``
    val Q1  = ``\(P,a). (?x:'a. P x) ==> P a``
    val ath = ISPECL [f1,Q1] PARTIAL_ABSTRACTION_QUOTIENT
    val bth = MP (PairRules.PBETA_RULE ath) ONTO_PARTIAL_FUNCTION1
    val fth = MATCH_MP (MATCH_MP FUN_QUOTIENT ith) bth
    val i1  = ``I:('a -> bool) -> ('a -> bool)``
    val eth = SPEC i1 (MATCH_MP QUOTIENT_REP fth)
    val th1 = PairRules.PBETA_RULE
                  (REWRITE_RULE[FUN_REL,FUN_REP_IDENTITY,FUN_MAP] eth)
    val th2 = REWRITE_RULE [GSYM EQ_SING]
                  (REWRITE_RULE[EQ_SING,IMAGE_SING,SELECT1_SING] th1)
in
    val CHOICE_FUN_PAIR_EXISTS = th2
end;



(*
option_case_def:
  |- (!u f. case u f NONE = u) /\ !u f x. case u f (SOME x) = f x


SPEC ``I:bool->bool``
 (MATCH_MP QUOTIENT_REP_EXISTS
 (MATCH_MP
  (MATCH_MP FUN_QUOTIENT (INST_TYPE [alpha |-> bool] IDENTITY_QUOTIENT))
  (UNDISCH (ISPEC ``P:'a -> bool`` ABSTRACTION_QUOTIENT))))


By QUOTIENT ($= :bool->bool->bool) (I:bool->bool) ($= :bool->bool->bool)
(IDENTITY_QUOTIENT, the identity quotient on booleans), and
by QUOTIENT (\r s:'a. P r = P s) (P:'a -> bool) (\(a:bool) (r:'a). P r = a)
as assumptions to the FUN_QUOTIENT, we have
QUOTIENT ($= ===> (\r s:'a. P r = P s))
         (I --> P)
         (($= >-- (\ (a:bool) (r:'a). P r = a)) $=)
from which by QUOTIENT_REP_EXISTS,
         !g. ?f. (($= >-- (\ (a:bool) (r:'a). P r = a)) $=) g f
*)


val NEW_CHOICE_EXISTS = store_thm
   ("NEW_CHOICE_EXISTS",
    (--`?c. !P (x:'a). P x ==> P (c P)`--),
    STRIP_ASSUME_TAC CHOICE_FUN_PAIR_EXISTS
    THEN EXISTS_TAC ``SND o (r:('a -> bool) -> (('a -> bool) # 'a))``
    THEN POP_ASSUM MP_TAC
    THEN REWRITE_TAC[FUN_EQ_THM,I_THM,o_THM]
    THEN BETA_TAC
    THEN DISCH_THEN (fn th => REWRITE_ALL_THM th THEN ASSUME_TAC th)
    THEN REPEAT STRIP_TAC
    THEN FIRST_ASSUM (MP_TAC o SPECL[ ``P:'a -> bool``, ``P:'a -> bool``])
    THEN REWRITE_TAC[]
    THEN DISCH_THEN MATCH_MP_TAC
    THEN EXISTS_TAC ``x:'a``
    THEN FIRST_ASSUM ACCEPT_TAC
   );

local
open Rsyntax
in
val NEW_CHOICE =
    new_specification { name    = "NEW_CHOICE",
                        consts  = [ { const_name = "@@",
                                      fixity = Binder    } ],
                        sat_thm = NEW_CHOICE_EXISTS           }
end;






val _ = export_theory();

val _ = print_theory_to_file "-" "quotient.lst";

val _ = html_theory "quotient";

fun print_theory_size () =
   (print "The theory ";
    print (current_theory ());
    print " has ";
    print (Int.toString (length (types (current_theory ()))));
    print " types, ";
    print (Int.toString (length (axioms "-")));
    print " axioms, ";
    print (Int.toString (length (definitions "-")));
    print " definitions, and ";
    print (Int.toString (length (theorems "-")));
    print " theorems.";
    print "\n" );

val _ = (*tactics.*)print_theory_size();
