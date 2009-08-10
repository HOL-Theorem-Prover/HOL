open HolKernel Parse boolLib;
infix THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL ## |->;
infixr -->;


(* --------------------------------------------------------------------- *)
(* Fundamental definitions and theorems for the quotients package.       *)
(* Version 2.2.                                                          *)
(* Date: July 29, 2005                                                   *)
(* WARNING: EXPERIMENTAL (not guarranteed to be fully operable.)         *)
(* --------------------------------------------------------------------- *)


val _ = new_theory "quotient_pred_set";

open prim_recTheory;
open combinTheory;
open pairTheory;
open pred_setTheory;
open bossLib;
open res_quanTheory;
open res_quanLib;
open dep_rewrite;
open quotientTheory;
open quotient_pairTheory;


val REWRITE_THM = fn th => REWRITE_TAC[th];
val ONCE_REWRITE_THM = fn th => ONCE_REWRITE_TAC[th];
fun ASM_REWRITE_THM th = ASM_REWRITE_TAC[th];
val REWRITE_ALL_THM = fn th => RULE_ASSUM_TAC (REWRITE_RULE[th])
                               THEN REWRITE_TAC[th];
val REWRITE_ALL_TAC = fn ths => RULE_ASSUM_TAC (REWRITE_RULE ths)
                                THEN REWRITE_TAC ths;

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




(* ========================================== *)
(* Main development of predicate set support: *)
(* ========================================== *)

(* for set rep or abs, DON'T use (abs --> I) or (rep --> I).  *)
(* No, for set rep or abs, use SET_MAP abs or SET_MAP rep.  *)



val IN_SET_MAP = store_thm
   ("IN_SET_MAP",
    (--`!(f:'a->'b) s x.
         x IN (f --> I) s = f x IN s`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_MAP_THM,SPECIFICATION,I_THM]
   );

val SET_REL = store_thm
   ("SET_REL",
    (--`!R s t.
         (R ===> $=) s t = !x y:'a. R x y ==> (x IN s = y IN t)`--),
    REPEAT GEN_TAC
    THEN REWRITE_TAC[FUN_REL,SPECIFICATION]
   );

val BOOL_QUOTIENT = INST_TYPE [alpha |-> bool] IDENTITY_QUOTIENT;

val SET_REL_MP = store_thm
   ("SET_REL_MP",
    (--`!R (abs:'a -> 'b) rep.
         QUOTIENT R abs rep ==>
           !s t x y. (R ===> $=) s t /\ R x y ==> (x IN s = y IN t)`--),
    REPEAT GEN_TAC
    THEN DISCH_THEN (ASSUME_TAC o C MATCH_MP BOOL_QUOTIENT o MATCH_MP
              (INST_TYPE[beta |-> bool, delta |-> bool] FUN_REL_MP))
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[SPECIFICATION]
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASM_REWRITE_TAC[]
   );


(* Here are some definitional and well-formedness theorems
   for some standard polymorphic operators.
*)



(* pred_set theory: IN, GSPEC, EMPTY, UNIV, INTER, UNION, SUBSET, PSUBSET,
                    INSERT, DELETE, DIFF, IMAGE *)

val IN_PRS = store_thm
   ("IN_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !x s. x IN s =
               rep x IN (abs --> I) s`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN ASM_REWRITE_TAC[IN_SET_MAP]
   );

val IN_RSP = store_thm
   ("IN_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !x1 x2 s1 s2.
          R x1 x2 /\ (R ===> $=) s1 s2 ==>
          (x1 IN s1 = x2 IN s2)`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC SET_REL_MP
   );


(* GSPEC does not lift directly; because its definition

GSPECIFICATION   |- !f v. v IN GSPEC f = ?x. (v,T) = f x : thm

involves = between v:'b and FST(f x):'b, rather than R1 v (FST(f x)),
which does not respect the equivalence relation on 'b.
The definition also does not guarantee that the chosen x respectes R2.
But a similar operator exists which we can try to lift to GSPEC.  *)


val GSPECR_def = Define
   `GSPECR R1 (R2:'b -> 'b -> bool) f v =
             ?x:'a :: respects R1. (R2 ### $=) (v,T) (f x) `;

val IN_GSPECR = store_thm
   ("IN_GSPECR",
    (--`!R1 R2 f (v:'a).
         v IN GSPECR R1 R2 f =
         ?x:'b :: respects R1. (R2 ### $=) (v,T) (f x : 'a # bool)`--),
    REWRITE_TAC[GSPECR_def,SPECIFICATION]
   );

val GSPEC_PRS = store_thm
   ("GSPEC_PRS",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f. GSPEC f =
               (rep2 --> I) (GSPECR R1 R2 ((abs1 --> (rep2 ## I)) f))`--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN REWRITE_TAC[GSPECIFICATION,IN_SET_MAP,IN_GSPECR]
    THEN REWRITE_TAC[FUN_MAP_THM,PAIR_MAP]
    THEN REWRITE_TAC[PAIR_REL_THM,I_THM]
    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_REL_REP
    THEN CONV_TAC (DEPTH_CONV RES_EXISTS_CONV)
    THEN REWRITE_TAC[IN_RESPECTS]
    THEN EQ_TAC
    THEN STRIP_TAC
    THENL
      [ EXISTS_TAC ``rep1 (x':'c) :'a``
        THEN IMP_RES_THEN REWRITE_THM QUOTIENT_REP_REFL
        THEN ASM_REWRITE_TAC[]
        THEN POP_ASSUM (REWRITE_THM o SYM),

        EXISTS_TAC ``abs1 (x':'a) :'c``
        THEN CONV_TAC (RAND_CONV (REWR_CONV (GSYM PAIR)))
        THEN ASM_REWRITE_TAC[PAIR_EQ]
      ]
   );

val GSPECR_RSP = store_thm
   ("GSPECR_RSP",
    (--`!R1 (abs1:'a -> 'c) rep1. QUOTIENT R1 abs1 rep1 ==>
        !R2 (abs2:'b -> 'd) rep2. QUOTIENT R2 abs2 rep2 ==>
         !f1 f2.
          (R1 ===> (R2 ### $=)) f1 f2 ==>
          (R2 ===> $=) (GSPECR R1 R2 f1) (GSPECR R1 R2 f2)`--),
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN REWRITE_TAC[FUN_REL]
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN REWRITE_TAC[PAIR_REL_THM]
    THEN DISCH_TAC
    THEN X_GEN_TAC ``u:'b``
    THEN X_GEN_TAC ``v:'b``
    THEN DISCH_TAC
    THEN REWRITE_TAC[IN_GSPECR]
    THEN CONV_TAC (DEPTH_CONV RES_EXISTS_CONV)
    THEN REWRITE_TAC[IN_RESPECTS]
    THEN ONCE_REWRITE_TAC[GSYM PAIR]
    THEN REWRITE_TAC[PAIR_REL_THM]
    THEN PROVE_TAC[QUOTIENT_SYM,QUOTIENT_TRANS]
   );


val EMPTY_PRS = store_thm
   ("EMPTY_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (EMPTY = (rep --> I) EMPTY)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[EXTENSION]
    THEN REWRITE_TAC[NOT_IN_EMPTY,IN_SET_MAP]
   );

val EMPTY_RSP = store_thm
   ("EMPTY_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (R ===> $=) EMPTY EMPTY`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN REWRITE_TAC[NOT_IN_EMPTY]
   );

val UNIV_PRS = store_thm
   ("UNIV_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (UNIV = (rep --> I) UNIV)`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[EXTENSION]
    THEN REWRITE_TAC[IN_SET_MAP,IN_UNIV]
   );

val UNIV_RSP = store_thm
   ("UNIV_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         (R ===> $=) UNIV UNIV`--),
    REPEAT STRIP_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN REWRITE_TAC[IN_UNIV]
   );


val UNION_PRS = store_thm
   ("UNION_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t. s UNION t =
               (rep --> I) ((abs --> I) s UNION (abs --> I) t)`--),
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
          (R ===> $=) s1 s2 /\ (R ===> $=) t1 t2 ==>
          (R ===> $=) (s1 UNION t1) (s2 UNION t2)`--),
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
               (rep --> I) ((abs --> I) s INTER (abs --> I) t)`--),
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
          (R ===> $=) s1 s2 /\ (R ===> $=) t1 t2 ==>
          (R ===> $=) (s1 INTER t1) (s2 INTER t2)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[SET_REL]
    THEN REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[IN_INTER]
    THEN IMP_RES_TAC (REWRITE_RULE[GSYM AND_IMP_INTRO] SET_REL_MP)
    THEN ASM_REWRITE_TAC[]
   );



val SUBSETR_def =
    Define
      `SUBSETR R s t = !x:'a::respects R. x IN s ==> x IN t`;

val SUBSET_PRS = store_thm
   ("SUBSET_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t. s SUBSET t =
               SUBSETR R ((abs --> I) s) ((abs --> I) t)`--),
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
          (R ===> $=) s1 s2 /\ (R ===> $=) t1 t2 ==>
          (SUBSETR R s1 t1 = SUBSETR R s2 t2)`--),
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
       SUBSETR R s t /\ ~((R ===> $=) s t)`;

val PSUBSET_PRS = store_thm
   ("PSUBSET_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t. s PSUBSET t = PSUBSETR R ((abs --> I) s) ((abs --> I) t)`--),
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
          (R ===> $=) s1 s2 /\ (R ===> $=) t1 t2 ==>
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
    THEN IMP_RES_THEN (MATCH_MP_TAC o MATCH_MP EQUALS_RSP
                                    o C MATCH_MP BOOL_QUOTIENT)
            (INST_TYPE[beta |-> bool, delta |-> bool] FUN_QUOTIENT)
    THEN ASM_REWRITE_TAC[]
   );



val INSERTR_def =
    Define
      `INSERTR R (x:'a) s = {y:'a | R y x \/ y IN s}`;

val IN_INSERTR = store_thm
   ("IN_INSERTR",
    (--`!R (x:'a) s y.
          y IN INSERTR R x s = R y x \/ y IN s`--),
    REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[INSERTR_def]
    THEN CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV)
    THEN REWRITE_TAC[]
   );

val INSERT_PRS = store_thm
   ("INSERT_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s x. x INSERT s =
               (rep --> I) (INSERTR R (rep x) ((abs --> I) s))
       `--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN IMP_RES_TAC QUOTIENT_REL_REP
    THEN PURE_ONCE_REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN ASM_REWRITE_TAC[IN_SET_MAP,IN_INSERT,IN_INSERTR]
   );

val INSERTR_RSP = store_thm
   ("INSERTR_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !x1 x2 s1 s2.
          R x1 x2 /\ (R ===> $=) s1 s2 ==>
          (R ===> $=) (INSERTR R x1 s1) (INSERTR R x2 s2)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[IN_INSERTR]
    THEN PROVE_TAC[QUOTIENT_SYM,QUOTIENT_TRANS]
   );



val DELETER_def =
    Define
      `DELETER R s (x:'a) = {y:'a | y IN s /\ ~R x y}`;

val IN_DELETER = store_thm
   ("IN_DELETER",
    (--`!R s (x:'a) y.
          y IN DELETER R s x = y IN s /\ ~R x y`--),
    REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[DELETER_def]
    THEN CONV_TAC (DEPTH_CONV pred_setLib.SET_SPEC_CONV)
    THEN REWRITE_TAC[]
   );

val DELETE_PRS = store_thm
   ("DELETE_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s x. s DELETE x =
               (rep --> I) (DELETER R ((abs --> I) s) (rep x))
       `--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN IMP_RES_TAC QUOTIENT_REL_REP
    THEN PURE_ONCE_REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN ASM_REWRITE_TAC[IN_SET_MAP,IN_DELETE,IN_DELETER]
    THEN PROVE_TAC[]
   );

val DELETER_RSP = store_thm
   ("DELETER_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2 x1 x2.
          (R ===> $=) s1 s2 /\ R x1 x2 ==>
          (R ===> $=) (DELETER R s1 x1) (DELETER R s2 x2)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[IN_DELETER]
    THEN PROVE_TAC[QUOTIENT_SYM,QUOTIENT_TRANS]
   );



val DIFF_PRS = store_thm
   ("DIFF_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t. s DIFF t =
               (rep --> I) (((abs --> I) s) DIFF ((abs --> I) t))
       `--),
    REPEAT STRIP_TAC
    THEN IMP_RES_TAC QUOTIENT_ABS_REP
    THEN PURE_ONCE_REWRITE_TAC[EXTENSION]
    THEN GEN_TAC
    THEN ASM_REWRITE_TAC[IN_SET_MAP,IN_DIFF]
   );

val DIFF_RSP = store_thm
   ("DIFF_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2 t1 t2.
          (R ===> $=) s1 s2 /\ (R ===> $=) t1 t2 ==>
          (R ===> $=) (s1 DIFF t1) (s2 DIFF t2)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[IN_DIFF]
    THEN PROVE_TAC[]
   );



val DISJOINTR_def =
    Define
      `DISJOINTR R s t = ~?x:'a::respects R. x IN s /\ x IN t`;


val DISJOINT_PRS = store_thm
   ("DISJOINT_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s t. DISJOINT s t =
               DISJOINTR R ((abs --> I) s) ((abs --> I) t)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[DISJOINT_DEF,DISJOINTR_def]
    THEN PURE_REWRITE_TAC[EXTENSION]
    THEN CONV_TAC (DEPTH_CONV RES_EXISTS_CONV THENC
                   DEPTH_CONV NOT_EXISTS_CONV)
    THEN PURE_REWRITE_TAC[IN_RESPECTS]
    THEN REWRITE_TAC[NOT_IN_EMPTY,IN_INTER,IN_SET_MAP,DE_MORGAN_THM]
    THEN EQ_TAC
    THEN DISCH_TAC
    THEN GEN_TAC
    THENL
      [ ASM_REWRITE_TAC[],

        POP_ASSUM (MP_TAC o SPEC ``rep (x:'b) :'a``)
        THEN IMP_RES_TAC QUOTIENT_ABS_REP
        THEN IMP_RES_TAC QUOTIENT_REP_REFL
        THEN ASM_REWRITE_TAC[]
      ]
   );

val DISJOINTR_RSP = store_thm
   ("DISJOINTR_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2 t1 t2.
          (R ===> $=) s1 s2 /\ (R ===> $=) t1 t2 ==>
          (DISJOINTR R s1 t1 = DISJOINTR R s2 t2)`--),
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[SET_REL]
    THEN STRIP_TAC
    THEN PURE_REWRITE_TAC[DISJOINTR_def]
    THEN CONV_TAC (DEPTH_CONV RES_EXISTS_CONV THENC
                   DEPTH_CONV NOT_EXISTS_CONV)
    THEN REWRITE_TAC[DE_MORGAN_THM,IN_RESPECTS]
    THEN PROVE_TAC[]
   );


val FINITER_def =
    Define
      `FINITER R s = !P :: respects ((R ===> $=) ===> $=).
                         P {} /\
                         (!s::respects(R ===> $=).
                                P s ==> !e:'a::respects R. P (INSERTR R e s))
                         ==> P s`;


val FINITE_PRS = store_thm
   ("FINITE_PRS",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s. FINITE s = FINITER R ((abs --> I) s)`--),
    REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[FINITE_DEF,FINITER_def]
    THEN CONV_TAC (DEPTH_CONV RES_FORALL_CONV)
    THEN PURE_REWRITE_TAC[IN_RESPECTS]
    THEN CONV_TAC (RAND_CONV (RAND_CONV (ABS_CONV (RATOR_CONV
                     (REWRITE_CONV[FUN_REL])))))
    THEN PURE_REWRITE_TAC[SET_REL]
    THEN EQ_TAC
    THEN DISCH_TAC
    THEN GEN_TAC
    THENL
      [ DISCH_TAC
        THEN STRIP_TAC
        THEN FIRST_ASSUM HO_MATCH_MP_TAC
        THEN CONJ_TAC
        THENL
          [ SUBGOAL_THEN ``P (((abs:'a -> 'b) --> (I:bool -> bool)) {})
                           = (P {} : bool)``
                    ASM_REWRITE_THM
            THEN FIRST_ASSUM MATCH_MP_TAC
            THEN REWRITE_TAC[FUN_MAP_THM,I_THM]
            THEN REWRITE_TAC[REWRITE_RULE[SPECIFICATION] NOT_IN_EMPTY],

            REPEAT STRIP_TAC
            THEN SUBGOAL_THEN ``!e. P (((abs:'a -> 'b) --> (I:bool -> bool))
                                      (e INSERT s'))
                            = (P (INSERTR R (rep e) ((abs --> I) s')) : bool)``
                    REWRITE_THM
            THENL
              [ GEN_TAC
                THEN FIRST_ASSUM MATCH_MP_TAC
                THEN REPEAT STRIP_TAC
                THEN REWRITE_TAC[REWRITE_RULE[SPECIFICATION] IN_INSERTR]
                THEN REWRITE_TAC[FUN_MAP_THM,I_THM]
                THEN REWRITE_TAC[REWRITE_RULE[SPECIFICATION] IN_INSERT]
                THEN IMP_RES_TAC QUOTIENT_REL_ABS
                THEN FIRST_ASSUM REWRITE_THM
                THEN AP_THM_TAC
                THEN AP_TERM_TAC
                THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
                THEN IMP_RES_TAC QUOTIENT_REL
                THEN POP_TAC THEN POP_TAC THEN POP_TAC
                THEN POP_ASSUM REWRITE_THM
                THEN IMP_RES_THEN REWRITE_THM QUOTIENT_REP_REFL
                THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP,

                DEP_ONCE_ASM_REWRITE_TAC[]
                THEN REWRITE_TAC[IN_SET_MAP]
                THEN FIRST_ASSUM REWRITE_THM
                THEN IMP_RES_THEN REWRITE_THM QUOTIENT_REP_REFL
                THEN REPEAT STRIP_TAC
                THEN IMP_RES_TAC QUOTIENT_REL_ABS
                THEN FIRST_ASSUM REWRITE_THM
              ]
          ],

        STRIP_TAC
        THEN FIRST_ASSUM (ASSUME_TAC o C MATCH_MP BOOL_QUOTIENT o MATCH_MP
                 (INST_TYPE [alpha |-> etyvar, beta |-> ftyvar] FUN_QUOTIENT))
        THEN SUBGOAL_THEN ``(P s : bool) =
                             P (((rep:'b -> 'a) --> (I:bool -> bool))
                                   (((abs:'a -> 'b) --> I) s))``
                    ONCE_REWRITE_THM
        THENL
          [ IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP,

            FIRST_ASSUM (HO_MATCH_MP_TAC o
                         REWRITE_RULE [AND_IMP_INTRO] o
                         CONV_RULE (DEPTH_CONV RIGHT_IMP_FORALL_CONV))
            THEN REPEAT STRIP_TAC
            THENL (* 3 subgoals *)
              [ POP_ASSUM (ASSUME_TAC o REWRITE_RULE[GSYM FUN_REL])
                THEN IMP_RES_TAC QUOTIENT_REL_ABS
                THEN ASM_REWRITE_TAC[],

                IMP_RES_THEN (ASM_REWRITE_THM o SYM) EMPTY_PRS
                THEN SUBGOAL_THEN ``((rep:'b -> 'a) --> (I:bool -> bool)) {} = {}``
                        ASM_REWRITE_THM
                THEN IMP_RES_THEN (REWRITE_THM o SYM) EMPTY_PRS,

                SUBGOAL_THEN ``((rep:'b -> 'a) --> I) (INSERTR R e s') =
                               ((abs:'a -> 'b) e INSERT ((rep --> I) s'))``
                    REWRITE_THM
                THENL
                  [ REWRITE_TAC[EXTENSION]
                    THEN GEN_TAC
                    THEN REWRITE_TAC[IN_SET_MAP,IN_INSERTR,IN_INSERT]
                    THEN AP_THM_TAC
                    THEN AP_TERM_TAC
                    THEN IMP_RES_THEN ONCE_REWRITE_THM QUOTIENT_REL
                    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_REP_REFL
                    THEN POP_ASSUM REWRITE_THM
                    THEN IMP_RES_THEN REWRITE_THM QUOTIENT_ABS_REP,

                    DEP_ONCE_ASM_REWRITE_TAC[]
                    THEN FIRST_ASSUM ACCEPT_TAC
                  ]
              ]
          ]
      ]
   );

val FINITER_EQ = store_thm
   ("FINITER_EQ",
    (--`!R:'a -> 'a -> bool.
         !s1 s2.
          (R ===> $=) s1 s2 ==>
          (FINITER R s1 = FINITER R s2)`--),
    REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN PURE_REWRITE_TAC[FINITER_def]
    THEN CONV_TAC (DEPTH_CONV RES_FORALL_CONV)
    THEN REWRITE_TAC[IN_RESPECTS]
    THEN EQ_TAC
    THEN DISCH_TAC
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN STRIP_TAC
    THEN RES_TAC
    THEN POP_ASSUM MP_TAC
    THEN SUBGOAL_THEN ``(P s1 : bool) = P (s2 : 'a -> bool)``
                    REWRITE_THM
    THEN POP_TAC THEN POP_TAC
    THEN POP_ASSUM (IMP_RES_TAC o ONCE_REWRITE_RULE[FUN_REL])
   );

val FINITER_RSP = store_thm
   ("FINITER_RSP",
    (--`!R (abs:'a -> 'b) rep. QUOTIENT R abs rep ==>
         !s1 s2.
          (R ===> $=) s1 s2 ==>
          (FINITER R s1 = FINITER R s2)`--),
    REWRITE_TAC[FINITER_EQ]
   );


val FINITER_EMPTY = store_thm
   ("FINITER_EMPTY",
    (--`!R:'a -> 'a -> bool. FINITER R EMPTY`--),
     GEN_TAC THEN
     PURE_ONCE_REWRITE_TAC [FINITER_def] THEN
     RESQ_GEN_TAC THEN
     DISCH_THEN REWRITE_THM
   );

val FINITER_INSERTR = store_thm
   ("FINITER_INSERTR",
    (--`!R (s::respects (R ===> $=)).
            FINITER R s ==>
            !x:'a::respects R. FINITER R (INSERTR R x s)`--),
     GEN_TAC THEN
     PURE_ONCE_REWRITE_TAC [FINITER_def] THEN
     CONV_TAC (DEPTH_CONV RES_FORALL_CONV) THEN
     REWRITE_TAC[IN_RESPECTS] THEN
     REPEAT STRIP_TAC THEN
     UNDISCH_TAC (--`R (x:'a) x :bool`--) THEN
     SPEC_TAC ((--`x:'a`--),(--`x:'a`--)) THEN
     FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO]) THEN
     ASM_REWRITE_TAC[] THEN
     FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE[AND_IMP_INTRO]) THEN
     ASM_REWRITE_TAC[GSYM AND_IMP_INTRO]);

val SIMPLE_FINITER_INDUCT =
    TAC_PROOF
    (([], (--`!R (P::respects ((R ===> $=) ===> $=)).
               P EMPTY /\
               (!s::respects (R ===> $=).
                 P s ==> (!e:'a::respects R. P(INSERTR R e s)))
                ==>
               !s::respects (R ===> $=). FINITER R s ==> P s`--)),
     GEN_TAC THEN
     RESQ_GEN_TAC THEN
     CONV_TAC (DEPTH_CONV RES_FORALL_CONV) THEN
     REWRITE_ALL_TAC[IN_RESPECTS] THEN
     STRIP_TAC THEN
     GEN_TAC THEN DISCH_TAC THEN
     PURE_ONCE_REWRITE_TAC [FINITER_def] THEN
     CONV_TAC (DEPTH_CONV RES_FORALL_CONV) THEN
     REWRITE_ALL_TAC[IN_RESPECTS] THEN
     ONCE_REWRITE_TAC [AND_IMP_INTRO] THEN
     DISCH_THEN MATCH_MP_TAC THEN
     ASM_REWRITE_TAC []);

val lemma =
  let val tac = ASM_CASES_TAC (--`P:bool`--) THEN ASM_REWRITE_TAC[]
      val lem = TAC_PROOF(([],(--`(P ==> P /\ Q) = (P ==> Q)`--)), tac)
      val th1 = DISCH_ALL
                  (RESQ_SPEC (--`\s:'a set. FINITER R s /\ P s`--)
                     (SPEC_ALL SIMPLE_FINITER_INDUCT))
      val th2 = TAC_PROOF(([],(--`P IN respects ((R ===> $=) ===> $=) ==>
                                  (\s:'a set. FINITER R s /\ P s) IN
                                   respects ((R ===> $=) ===> $=)`--)),
                      REWRITE_TAC[IN_RESPECTS]
                      THEN ONCE_REWRITE_TAC[FUN_REL]
                      THEN DISCH_TAC
                      THEN BETA_TAC
                      THEN REPEAT STRIP_TAC
                      THEN IMP_RES_THEN REWRITE_THM FINITER_EQ
                      THEN AP_TERM_TAC
                      THEN FIRST_ASSUM MATCH_MP_TAC
                      THEN FIRST_ASSUM ACCEPT_TAC)
  in DISCH_ALL (REWRITE_RULE [lem,FINITER_EMPTY]
                      (BETA_RULE (MP th1 (UNDISCH_ALL th2))))
  end;

val ABSORPTIONR =
    store_thm
    ("ABSORPTIONR",
     (--`!R (x:'a::respects R). !s::respects(R ===> $=).
            (x IN s) = (R ===> $=) (INSERTR R x s) s`--),
     GEN_TAC THEN
     REWRITE_TAC [SET_REL,IN_INSERTR] THEN
     REPEAT (RESQ_GEN_TAC ORELSE STRIP_TAC ORELSE EQ_TAC) THEN
     REWRITE_ALL_TAC[IN_RESPECTS,SET_REL] THEN
     RES_TAC THEN
     ASM_REWRITE_TAC[]);

val FINITER_INDUCT = store_thm("FINITER_INDUCT",
--`!R (P::respects ((R ===> $=) ===> $=)).
       P {} /\ (!s::respects (R ===> $=). FINITER R s /\ P s ==>
                    (!e:'a::respects R. ~(e IN s) ==> P(INSERTR R e s)))
       ==> !s::respects (R ===> $=). FINITER R s
                          ==> P s`--,
     GEN_TAC THEN
     RESQ_GEN_TAC THEN
     FIRST_ASSUM (MP_TAC o ONCE_REWRITE_RULE[FUN_REL]
                         o REWRITE_RULE[IN_RESPECTS]) THEN
     FIRST_ASSUM (ASSUME_TAC o MP lemma) THEN
     DISCH_TAC THEN
     STRIP_TAC THEN
     FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [] THEN
     FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE[IN_RESPECTS]
                             o CONV_RULE RES_FORALL_CONV) THEN
     RESQ_GEN_TAC THEN
     FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE[IN_RESPECTS]) THEN
     STRIP_TAC THEN
     RESQ_GEN_TAC THEN
     FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE[IN_RESPECTS]) THEN
     CONJ_TAC THENL
     [MP_TAC (ASSUME ``(e:'a) IN respects R``) THEN
      IMP_RES_THEN (MATCH_ACCEPT_TAC o CONV_RULE RES_FORALL_CONV)
               (RESQ_SPEC ``s:'a -> bool`` (SPEC_ALL FINITER_INSERTR)),
      ASM_CASES_TAC (--`(e:'a) IN s`--) THENL
      [IMP_RES_TAC (RESQ_SPEC ``s:'a -> bool``
                    (RESQ_SPEC ``e:'a`` (SPEC_ALL ABSORPTIONR)))
       THEN RES_TAC,
       RES_TAC
       THEN FIRST_ASSUM (IMP_RES_TAC o RESQ_SPEC ``e:'a``)]]);



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
               (rep2 --> I) (IMAGER R1 R2 ((abs1-->rep2) f) ((abs1 --> I) s))
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
          (R1 ===> R2) f1 f2 /\ (R1 ===> $=) s1 s2 ==>
          (R2 ===> $=) (IMAGER R1 R2 f1 s1) (IMAGER R1 R2 f2 s2)`--),
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
          (R1 ===> R2) f1 f2 /\ (R1 ===> $=) s1 s2 ==>
          (R2 ===> $=) (IMAGE f1 s1) (IMAGE f2 s2)`--),
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

