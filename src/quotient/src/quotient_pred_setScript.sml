open HolKernel Parse boolLib;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;
infixr -->;


(* --------------------------------------------------------------------- *)
(* Fundamental definitions and theorems for the quotients package.       *)
(* Version 2.2.                                                          *)
(* Date: April 11, 2005                                                  *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "quotient_pred_set";

open prim_recTheory;
open combinTheory;
open pred_setTheory;
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




(* ============================ *)
(* Main development of SET_REL: *)
(* ============================ *)

(* for set rep or abs, DON'T use (abs --> I) or (rep --> I).  *)
(* No, for set rep or abs, use SET_MAP abs or SET_MAP rep.  *)

val SET_REL_def =
    Define
      `SET_REL (R:'a->'a->bool) = (R ===> ($= :bool->bool->bool))`;

(*
val SET_REL_def =
    Define
      `SET_REL (R:'a->'a->bool) s t = (R ===> ($= :bool->bool->bool)) s t /\
                                      (!x. x IN s \/ x IN t ==> respects R x)`;
*)

val SET_REL = store_thm
   ("SET_REL",
    (--`!(R:'a->'a->bool).
         SET_REL R s t =
           (!x y. R x y ==> ((x IN s) = (y IN t)))`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_REL_def,FUN_REL,SPECIFICATION]
   );

val SET_MAP_def =
    Define
      `SET_MAP (f:'a->'b) = (f --> (I:bool->bool))`;

val SET_MAP_COMPOSE = store_thm
   ("SET_MAP_COMPOSE",
    (--`!(f:'a->'b) s.
         SET_MAP f s = s o f`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_MAP_def,FUN_MAP_THM,I_THM,o_THM,
                     EXTENSION,SPECIFICATION]
   );

val IN_SET_MAP = store_thm
   ("IN_SET_MAP",
    (--`!(f:'a->'b) s x.
         x IN SET_MAP f s = f x IN s`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_MAP_COMPOSE,SPECIFICATION,o_THM]
   );

val SET_MAP_SET_MAP = store_thm
   ("SET_MAP_SET_MAP",
    (--`!(f:'a->'b) (g:'b->'c) s.
         SET_MAP f (SET_MAP g s) = SET_MAP (g o f) s`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_MAP_COMPOSE,o_ASSOC]
   );

val SET_QUOTIENT = store_thm
   ("SET_QUOTIENT",
    (--`!R (abs:'a->'c) rep. QUOTIENT R abs rep ==>
         QUOTIENT (SET_REL R) (SET_MAP rep) (SET_MAP abs)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REWRITE_TAC[SET_REL_def,SET_MAP_def]
    THEN IMP_RES_THEN MATCH_MP_TAC FUN_QUOTIENT
    THEN REWRITE_TAC[IDENTITY_QUOTIENT]
   );


val SET_REL_MP = store_thm
   ("SET_REL_MP",
    (--`!(R:'a -> 'a -> bool) s t x y.
         (SET_REL R) s t ==> R x y ==> (x IN s = y IN t)`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC SET_REL
   );


(* One possible development of SET_REL, based on set rep/abs by IMAGE:
Unfortunately this definition makes it impossible to prove the respectfulness
theorems for such operators as IN.

val SET_REL_def =
    Define
      `SET_REL (R:'a->'a->bool) s t =
                     (!x. x IN s ==> ?y. y IN t /\ R x y) /\
                     (!y. y IN t ==> ?x. x IN s /\ R x y)`;


val SET_EQUIV = store_thm
   ("SET_EQUIV",
    (--`!R :'a->'a->bool.
         (!x y. R x y = (R x = R y)) ==>
         (!x y. SET_REL R x y = (SET_REL R x = SET_REL R y))`--),
    GEN_TAC
    THEN REWRITE_TAC[EQUIV_REFL_SYM_TRANS]
    THEN STRIP_TAC
    THEN REWRITE_TAC[SET_REL_def,EXTENSION,IN_IMAGE]
    THEN REPEAT STRIP_TAC (* 6 subgoals *)
    THENL
      [ EXISTS_TAC ``x':'a``
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC ``y:'a``
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN EXISTS_TAC ``x'':'a``
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN EXISTS_TAC ``y'':'a``
        THEN RES_TAC
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN RES_TAC
        THEN EXISTS_TAC ``y'':'a``
        THEN ASM_REWRITE_TAC[],

        RES_TAC
        THEN RES_TAC
        THEN EXISTS_TAC ``x''':'a``
        THEN ASM_REWRITE_TAC[]
      ]
    THEN PROVE_TAC[] (* could replace the THENL 6 cases above *)
   );


val SET_QUOTIENT = store_thm
   ("SET_QUOTIENT",
    (--`!R (abs:'a->'b) rep.
         (!a. abs (rep a) = a) /\
         (!r r'. R r r' = (abs r = abs r')) ==>
         (!a. IMAGE abs (IMAGE rep a) = a) /\
         (!r r'. SET_REL R r r' = (IMAGE abs r = IMAGE abs r'))`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN CONJ_TAC
    THEN REWRITE_TAC[SET_REL_def,EXTENSION,IN_IMAGE]
    THEN PROVE_TAC[]
   );

*)



(* Here are some definitional and well-formedness theorems
   for some standard polymorphic operators.
*)



(* pred_set theory: IN, EMPTY, UNIV, INTER, UNION, SUBSET, PSUBSET, IMAGE *)

val IN_PRS = store_thm
   ("IN_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !x s. x IN s =
               rep x IN SET_MAP abs s`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[IN_SET_MAP]
   );

val IN_RSP = store_thm
   ("IN_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !x1 x2 s1 s2.
          R x1 x2 /\ (SET_REL R) s1 s2 ==>
          (x1 IN s1 = x2 IN s2)`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC SET_REL_MP
   );


(* GSPEC does not lift directly; because its definition

GSPECIFICATION   |- !f v. v IN GSPEC f = ?x. (v,T) = f x : thm

involves = between v:'b and FST(f x):'b, rather than R2 v (FST(f x)),
it does not respect the equivalence relation on 'b.
But a similar operator exists which we can try to lift to GSPEC.

val GSPEC_PRS = store_thm
   ("GSPEC_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f. GSPEC f =
               SET_MAP rep2 (GSPEC ((abs1 --> (rep2 ## I)) f))`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN REWRITE_TAC[GSPECIFICATION,IN_SET_MAP]
    THEN REWRITE_TAC[FUN_MAP_THM,PAIR_MAP]
    THEN REWRITE_TAC[PAIR_EQ,I_THM]
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
      [ EXISTS_TAC ``rep1 (x':'c) :'a``
        THEN ASM_REWRITE_TAC[]
        THEN POP_ASSUM (REWRITE_THM o SYM),

        EXISTS_TAC ``abs1 (x':'a) :'c``
        THEN CONV_TAC (RAND_CONV (REWR_CONV (GSYM PAIR)))
        THEN REWRITE_TAC[PAIR_EQ]
        THEN POP_ASSUM REWRITE_THM
        THEN POP_ASSUM (MP_TAC o AP_TERM ``abs2:'b->'d``)
        THEN ASM_REWRITE_TAC[]
      ]
   );

val GSPECR_def =
    Define
      `GSPECR R (f:'a -> ('b # bool)) (v:'b) =
                     ?x. (R ### $=) (v,T) (f x)`;


val GSPECIFICATION_R = store_thm
   ("GSPECIFICATION_R",
    (--`!R f v:'b. v IN GSPECR R f = ?x:'a. (R ### $=) (v,T) (f x)`--),
    REWRITE_TAC[GSPECR_def,SPECIFICATION]
   );

val GSPECR_PRS = store_thm
   ("GSPECR_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f. GSPEC f =
               SET_MAP rep2 (GSPECR R2 ((abs1 --> (rep2 ## I)) f))`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN IMP_RES_TAC QUOTIENT_REP_REFL
    THEN REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN REWRITE_TAC[GSPECIFICATION,GSPECIFICATION_R,IN_SET_MAP]
    THEN REWRITE_TAC[FUN_MAP_THM,I_THM,PAIR_MAP]
    THEN REWRITE_TAC[PAIR_REL_THM,PAIR_EQ]
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
      [ EXISTS_TAC ``rep1 (x':'c) :'a``
        THEN ASM_REWRITE_TAC[]
        THEN POP_ASSUM (REWRITE_THM o SYM)
        THEN ASM_REWRITE_TAC[],

        EXISTS_TAC ``abs1 (x':'a) :'c``
        THEN CONV_TAC (RAND_CONV (REWR_CONV (GSYM PAIR)))
        THEN REWRITE_TAC[PAIR_EQ]
        THEN POP_ASSUM REWRITE_THM
        THEN POP_ASSUM MP_TAC
        THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
        THEN ASM_REWRITE_TAC[]
      ]
   );

This proof fails for the new quotient relations; not reflexive!
val GSPECR_RSP = store_thm
   ("GSPECR_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f1 f2.
          (R1 ===> (R2 ### $=)) f1 f2 ==>
          SET_REL R2 (GSPECR R2 f1) (GSPECR R2 f2)`--),
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN REWRITE_TAC[PAIR_REL_THM]
    THEN DISCH_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN X_GEN_TAC ``z:'b``
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN REWRITE_TAC[GSPECIFICATION_R]
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN REWRITE_TAC[PAIR_REL_THM,PAIR_EQ]
    THEN EQ_TAC
    THEN STRIP_TAC
    THEN EXISTS_TAC ``(rep1:'c->'a) ((abs1:'a->'c) x)``
    THEN IMP_RES_TAC QUOTIENT_REP_REFL
    THEN FIRST_ASSUM (ASSUME_TAC o SPEC ``(abs1:'a->'c) x``)
    THEN RES_TAC
    THEN POP_TAC
    THEN POP_TAC
    THEN POP_ASSUM (REWRITE_THM o SYM)
    THEN IMP_RES_TAC QUOTIENT_SYM
    THEN IMP_RES_TAC QUOTIENT_TRANS
   );

Can't prove this, so can't lift GSPEC.

val GSPEC_RSP = store_thm
   ("GSPEC_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1 R2 (abs2:'b -> 'd) rep2.
         (!a. abs1 (rep1 a) = a) /\ (!r r'. R1 r r' = (abs1 r = abs1 r'))
         ==>
         (!a. abs2 (rep2 a) = a) /\ (!r r'. R2 r r' = (abs2 r = abs2 r'))
         ==>
         !f1 f2.
          (R1 ===> (R2 ### $=)) f1 f2 ==>
          SET_REL R2 (GSPEC f1) (GSPEC f2)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL]
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN REWRITE_TAC[PAIR_REL_THM]
    THEN DISCH_TAC
    THEN REWRITE_TAC[SET_REL_EQ]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[GSPECIFICATION]
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN REWRITE_TAC[PAIR_EQ]
    THEN ???
   );

No, the GSPEC / GSPECR experiment has not succeeded.
*)


val EMPTY_PRS = store_thm
   ("EMPTY_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (EMPTY = SET_MAP abs EMPTY)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[EXTENSION]
    THEN REWRITE_TAC[NOT_IN_EMPTY,IN_SET_MAP]
   );

val EMPTY_RSP = store_thm
   ("EMPTY_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         SET_REL R EMPTY EMPTY`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN REWRITE_TAC[NOT_IN_EMPTY]
   );

val UNIV_PRS = store_thm
   ("UNIV_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (UNIV = SET_MAP abs UNIV)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[EXTENSION]
    THEN REWRITE_TAC[IN_SET_MAP,IN_UNIV]
   );

val UNIV_RSP = store_thm
   ("UNIV_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         SET_REL R UNIV UNIV`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN REWRITE_TAC[IN_UNIV]
   );


val UNION_PRS = store_thm
   ("UNION_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t. s UNION t =
               SET_MAP rep (SET_MAP abs s UNION SET_MAP abs t)`--),
    REPEAT STRIP_TAC
    THEN PURE_ONCE_REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN PURE_REWRITE_TAC[IN_SET_MAP,IN_UNION]
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[]
   );

val UNION_RSP = store_thm
   ("UNION_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2 t1 t2.
          SET_REL R s1 s2 /\ SET_REL R t1 t2 ==>
          SET_REL R (s1 UNION t1) (s2 UNION t2)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[SET_REL]
    THEN REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[IN_UNION]
    THEN IMP_RES_TAC (REWRITE_RULE[GSYM AND_IMP_INTRO] SET_REL_MP)
    THEN ASM_REWRITE_TAC[]
   );


val INTER_PRS = store_thm
   ("INTER_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t. s INTER t =
               SET_MAP rep (SET_MAP abs s INTER SET_MAP abs t)`--),
    REPEAT STRIP_TAC
    THEN PURE_ONCE_REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN PURE_REWRITE_TAC[IN_SET_MAP,IN_INTER]
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[]
   );

val INTER_RSP = store_thm
   ("INTER_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2 t1 t2.
          SET_REL R s1 s2 /\ SET_REL R t1 t2 ==>
          SET_REL R (s1 INTER t1) (s2 INTER t2)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[SET_REL]
    THEN REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[IN_INTER]
    THEN IMP_RES_TAC (REWRITE_RULE[GSYM AND_IMP_INTRO] SET_REL_MP)
    THEN ASM_REWRITE_TAC[]
   );

(*
val EQ_EMPTY_PRS = store_thm
   ("EQ_EMPTY_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s.
             (s = {}) = (SET_MAP abs s = {})`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[EXTENSION,NOT_IN_EMPTY]
    THEN REWRITE_TAC[IN_SET_MAP]
    THEN EQ_TAC
    THENL
      [ DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM MATCH_ACCEPT_TAC,

        DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM (MP_TAC o SPEC ``rep (x:'b) :'a``)
        THEN IMP_RES_TAC QUOTIENT_ABS_REP
        THEN ASM_REWRITE_TAC[]
      ]
   );

val EQ_EMPTY_RSP = store_thm
   ("EQ_EMPTY_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2. SET_REL R s1 s2 ==>
             ((s1 = {}) = (s2 = {}))`--),
    REWRITE_TAC[SET_REL]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[EXTENSION,NOT_IN_EMPTY]
    THEN EQ_TAC
    THENL
      [ DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM MATCH_ACCEPT_TAC,

        DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM (MP_TAC o SPEC ``rep (x:'b) :'a``)
        THEN IMP_RES_TAC QUOTIENT_ABS_REP
        THEN ASM_REWRITE_TAC[]
      ]
   );
*)

(* DISJOINT does not lift.

val DISJOINTR_def =
    Define
      `DISJOINTR R (s:'a -> bool) t = SET_REL R (s INTER t) {}`;

NO.
val SET_REL_EXTENSION = store_thm
   ("SET_REL_EXTENSION",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t. SET_REL R s t = (!x :: respects R. x IN s = x IN t)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN CONV_TAC (DEPTH_CONV RES_FORALL_CONV)
    THEN REWRITE_TAC[IN_RESPECTS]
    THEN EQ_TAC
    THENL
      [ DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM MATCH_ACCEPT_TAC,

        DISCH_TAC
        THEN REPEAT GEN_TAC
        THEN POP_ASSUM (MP_TAC o SPEC ``rep (x:'b) :'a``)
        THEN IMP_RES_TAC QUOTIENT_REP_REFL
        THEN ASM_REWRITE_TAC[]
      ]
   );

val DISJOINT_PRS = store_thm
   ("DISJOINT_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t.
             DISJOINT s t = DISJOINTR R (SET_MAP abs s) (SET_MAP abs t)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[DISJOINT_DEF,DISJOINTR_def]
    THEN REWRITE_TAC[EXTENSION,NOT_IN_EMPTY,IN_INTER]
    THEN REWRITE_TAC[SET_REL_EXTENSION,NOT_IN_EMPTY,IN_INTER]
    THEN REWRITE_TAC[IN_SET_MAP]
    THEN EQ_TAC
    THENL
      [ DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM MATCH_ACCEPT_TAC,

        DISCH_TAC
        THEN GEN_TAC
        THEN POP_ASSUM (MP_TAC o SPEC ``rep (x:'b) :'a``)
        THEN IMP_RES_TAC QUOTIENT_ABS_REP
        THEN ASM_REWRITE_TAC[]
      ]
   );

val DISJOINT_RSP = store_thm
   ("DISJOINT_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2 t1 t2.
          SET_REL R s1 s2 /\ SET_REL R t1 t2 ==>
          (DISJOINT s1 t1 = DISJOINT s2 t2)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[DISJOINT_DEF]
    THEN AP_THM_TAC
    THEN AP_TERM_TAC
    THEN MP_TAC (SPEC_ALL INTER_RSP)
    THEN ASM_REWRITE_TAC[]
    THEN 
    THEN 
    THEN 
    THEN IMP_RES_THEN MATCH_MP_TAC INTER_RSP
    THEN 
    THEN REWRITE_TAC[EXTENSION,NOT_IN_EMPTY,IN_INTER]
    THEN REWRITE_TAC[DE_MORGAN_THM]
    THEN EQ_TAC
    THEN DISCH_TAC
    THEN GEN_TAC
    THEN POP_ASSUM (MP_TAC o SPEC ``x:'a``)
    THEN IMP_RES_TAC QUOTIENT_REFL
    THEN POP_ASSUM (ASSUME_TAC o SPEC ``x:'a``)
    THEN IMP_RES_TAC SET_REL_MP
    THEN ASM_REWRITE_TAC[]
   );
*)



val SUBSETR_def =
    Define
      `SUBSETR P s t = !x:'a::P. x IN s ==> x IN t`;

val SUBSET_PRS = store_thm
   ("SUBSET_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t. s SUBSET t =
               SUBSETR (respects R) (SET_MAP abs s) (SET_MAP abs t)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[SUBSET_DEF,SUBSETR_def]
    THEN PURE_REWRITE_TAC[IN_SET_MAP]
    THEN CONV_TAC (RAND_CONV RES_FORALL_CONV)
    THEN PURE_REWRITE_TAC[IN_RESPECTS]
    THEN EQ_TAC
    THEN DISCH_TAC
    THEN GEN_TAC
    THENL
      [ DISCH_TAC
        THEN FIRST_ASSUM MATCH_ACCEPT_TAC,

        POP_ASSUM (MP_TAC o SPEC ``rep (x:'b) :'a``)
        THEN IMP_RES_TAC QUOTIENT_ABS_REP
        THEN IMP_RES_TAC QUOTIENT_REP_REFL
        THEN ASM_REWRITE_TAC[]
      ]
   );

val SUBSETR_RSP = store_thm
   ("SUBSETR_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2 t1 t2.
          SET_REL R s1 s2 /\ SET_REL R t1 t2 ==>
          (SUBSETR (respects R) s1 t1 = SUBSETR (respects R) s2 t2)`--),
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN STRIP_TAC
    THEN PURE_REWRITE_TAC[SUBSETR_def]
    THEN CONV_TAC (DEPTH_CONV RES_FORALL_CONV)
    THEN PURE_REWRITE_TAC[IN_RESPECTS]
    THEN EQ_TAC
    THEN DISCH_TAC
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN DISCH_TAC
    THEN RES_TAC
    THEN RES_TAC
   );


val PSUBSETR_def =
    Define
      `PSUBSETR R (s:'a->bool) t =
       SUBSETR (respects R) s t /\ ~(SET_REL R s t)`;

val PSUBSET_PRS = store_thm
   ("PSUBSET_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t. s PSUBSET t = PSUBSETR R (SET_MAP abs s) (SET_MAP abs t)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[PSUBSET_DEF,PSUBSETR_def]
    THEN PURE_ONCE_REWRITE_TAC[EXTENSION]
    THEN PURE_ONCE_REWRITE_TAC[SET_REL]
    THEN PURE_REWRITE_TAC[IN_SET_MAP]
    THEN IMP_RES_THEN REWRITE_THM SUBSET_PRS
    THEN AP_TERM_TAC
    THEN AP_TERM_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
      [ IMP_RES_TAC QUOTIENT_REL_ABS
        THEN ASM_REWRITE_TAC[],

        IMP_RES_THEN (ASSUME_TAC o SPEC ``x:'b``) QUOTIENT_REP_REFL
        THEN RES_THEN MP_TAC
        THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP
      ]
   );

val PSUBSETR_RSP = store_thm
   ("PSUBSETR_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2 t1 t2.
          SET_REL R s1 s2 /\ SET_REL R t1 t2 ==>
          (PSUBSETR R s1 t1 = PSUBSETR R s2 t2)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[PSUBSETR_def]
    THEN MP_TAC (SPEC_ALL SUBSETR_RSP)
    THEN ASM_REWRITE_TAC[]
    THEN DISCH_THEN (MP_TAC o SPEC_ALL)
    THEN ASM_REWRITE_TAC[]
    THEN DISCH_THEN REWRITE_THM
    THEN AP_TERM_TAC
    THEN AP_TERM_TAC
    THEN IMP_RES_TAC SET_QUOTIENT
    THEN POP_ASSUM (MATCH_MP_TAC o (MATCH_MP EQUALS_RSP))
    THEN ASM_REWRITE_TAC[]
   );


(* IMAGER (rep1,abs2) f s =
   SET_MAP abs2 (IMAGE ((rep1 --> abs2) f) (SET_MAP rep1 s))

   SET_MAP abs2 {(rep1 --> abs2) f x | x IN SET_MAP rep1 s}

   SET_MAP abs2 {(rep1 --> abs2) f x | rep1 x IN s}

   SET_MAP abs2 {abs2 (f (rep1 x)) | rep1 x IN s}

   SET_MAP abs2 {abs2 (f z) | R1 z z /\ z IN s}

   SET_MAP abs2 {abs2 (f z) | R1 z z /\ z IN s}

   {y | ?x. abs2 y = abs2 (f x) /\ R1 x x /\ x IN s}

   {y | ?x. R2 y (f x) /\ R1 x x /\ x IN s}

?  {y | ?x. R2 y (f (rep1 x)) /\ rep1 x IN s}

?  {y | ?x x'. R2 y (f x) /\ R1 x x' /\ x' IN s}

  *)

(*
val IMAGER_def =
    Define
      `IMAGER R1 R2 (f:'a->'b) s =
       {y:'b | ?x :: respects R1. R2 y (f x) /\ x IN s}`;
*)

val IMAGER_def =
    Define
      `IMAGER R1 R2 (f:'a->'b) s =
       {y:'b | ?x :: respects R1. R2 y (f x) /\ x IN s}`;

val IN_IMAGER = store_thm
   ("IN_IMAGER",
    (--`!R1 R2 y (f:'a -> 'b) s.
          y IN IMAGER R1 R2 f s =
                 ?x :: respects R1. R2 y (f x) /\ x IN s`--),
    REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[IMAGER_def]
    THEN CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV)
    THEN REWRITE_TAC[]
   );

val IMAGE_PRS = store_thm
   ("IMAGE_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f s. IMAGE f s =
               SET_MAP rep2 (IMAGER R1 R2 ((abs1-->rep2) f) (SET_MAP abs1 s))
       `--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN PURE_ONCE_REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN PURE_REWRITE_TAC[IN_SET_MAP,IN_IMAGE,IN_IMAGER]
    THEN CONV_TAC (DEPTH_CONV RES_EXISTS_CONV)
    THEN REWRITE_TAC[IN_RESPECTS,FUN_MAP_THM]
    THEN EQ_TAC
    THENL
       [ STRIP_TAC
         THEN EXISTS_TAC (--`(rep1:'c->'a) x'`--)
         THEN IMP_RES_TAC QUOTIENT_REP_REFL
         THEN ASM_REWRITE_TAC[],

         STRIP_TAC
         THEN EXISTS_TAC (--`(abs1:'a->'c) x'`--)
         THEN POP_ASSUM (fn th => REWRITE_TAC[th])
         THEN IMP_RES_TAC QUOTIENT_REL_ABS
         THEN POP_TAC
         THEN POP_ASSUM MP_TAC
         THEN ASM_REWRITE_TAC[]
       ]
   );

val IMAGER_RSP = store_thm
   ("IMAGER_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f1 f2 s1 s2.
          (R1 ===> R2) f1 f2 /\ SET_REL R1 s1 s2 ==>
          SET_REL R2 (IMAGER R1 R2 f1 s1) (IMAGER R1 R2 f2 s2)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN REWRITE_TAC[FUN_REL]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[IN_IMAGER]
    THEN CONV_TAC (DEPTH_CONV RES_EXISTS_CONV)
    THEN REWRITE_TAC[IN_RESPECTS]
    THEN EQ_TAC
    THEN STRIP_TAC
    THEN EXISTS_TAC (--`x':'a`--)
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC QUOTIENT_SYM
    THEN IMP_RES_TAC QUOTIENT_TRANS
   );

(*
val IMAGE_RSP = store_thm
   ("IMAGE_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f1 f2 s1 s2.
          (R1 ===> R2) f1 f2 /\ SET_REL R1 s1 s2 ==>
          SET_REL R2 (IMAGE f1 s1) (IMAGE f2 s2)`--),
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL,SET_REL]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[IN_IMAGE]
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
       [ EXISTS_TAC (--`x':'a`--)
         THEN CONJ_TAC
         THENL
           [ ASM_REWRITE_TAC[]
             THEN FIRST_ASSUM MATCH_MP_TAC
             THEN ASM_REWRITE_TAC[],

             POP_ASSUM MP_TAC
             THEN ASM_REWRITE_TAC[]
           ],

         EXISTS_TAC (--`x':'a`--)
         THEN CONJ_TAC
         THENL
           [ ASM_REWRITE_TAC[]
             THEN ONCE_REWRITE_TAC[EQ_SYM_EQ]
             THEN FIRST_ASSUM MATCH_MP_TAC
             THEN ASM_REWRITE_TAC[],

             POP_ASSUM MP_TAC
             THEN ASM_REWRITE_TAC[]
           ]
       ]
   );
*)





val _ = export_theory();

val _ = print_theory_to_file "-" "quotient_pred_set.lst";

val _ = html_theory "quotient_pred_set";

