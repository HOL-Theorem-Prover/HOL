(*****************************************************************************)
(* HolBddScript.sml                                                          *)
(* ----------------                                                          *)
(*                                                                           *)
(* Script for proving theorems used by DerivedBddRules.                      *)
(*****************************************************************************)


(*
load "tautLib";
load "bossLib";
load "simpLib";
load "numLib";
load "pairLib";
load "arithmeticTheory";
load "listTheory";
load "pairTheory";
load "Ho_Rewrite";
load "Num_conv";
load "unwindLib";
*)

open HolKernel Parse boolLib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;
infix 8 by;

open tautLib;
open bossLib;
open simpLib;
open numLib;
open pairLib;
open arithmeticTheory;
open listTheory;
open pairTheory;
open Ho_Rewrite;
open Num_conv;
(* open HOLSimps; *)

val _ = new_theory "DerivedBddRules";

fun prove_thm(_:string,tm,tac) = prove(tm,tac);

(*****************************************************************************)
(* ``Next R B state'' is true if state can be reached from                   *)
(* a state satisfying B in one R-step                                        *)
(*****************************************************************************)

val Next_def =
 Define
  `Next R B state = 
    ?state_. B state_ /\  R(state_,state)`;

(*****************************************************************************)
(* ``Prev R Q state'' is the set of states from which Q can be reached       *)
(* in one transition                                                         *)
(*****************************************************************************)

val Prev_def =
 Define
  `Prev R Q state = ?state'. R(state,state') /\ Q state'`;

(*****************************************************************************)
(* Characteristic function of a set with just one state                      *)
(*****************************************************************************)

val Eq_def =
 Define
  `Eq state0 state = (state0 = state)`;

val Prev_Next_Eq =
 prove_thm
  ("Prev_Next_Eq",
   ``!R s s'. Prev R (Eq s') s = Next R (Eq s) s'``,
   PROVE_TAC[Prev_def,Next_def,Eq_def]);

(*****************************************************************************)
(* ``ReachIn n R B state'' is true if state can be reached from              *)
(* a state satisfying B in exactly n R-steps                                 *)
(*****************************************************************************)

val ReachIn_def =
 Define
  `(ReachIn R B 0 = B)
   /\
   (ReachIn R B (SUC n) = Next R (ReachIn R B n))`;

val ReachIn_rec =
 store_thm
  ("ReachIn_rec",
   ``(!R B state. 
       ReachIn R B 0 state = B state)
   /\
   (!R B n state. 
     ReachIn R B (SUC n) state = 
     (?state_. ReachIn R B n state_ /\ R(state_,state)))``,
   PROVE_TAC[ReachIn_def,Next_def]);

val ReachIn_Next =
 prove_thm 
  ("ReachIn_Next",
   ``!n. ReachIn R (Next R B) n = ReachIn R B (SUC n)``,
   Induct   
    THEN RW_TAC std_ss [ReachIn_def,Next_def]);

val ReachIn_expand =
 prove_thm
  ("ReachIn_expand",
   ``!n. ReachIn R (Next R B) n state = 
          (?state_. ReachIn R B n state_ /\ R(state_,state))``,
    PROVE_TAC[ReachIn_def,Next_def,ReachIn_Next]);

val Next_ReachIn =
 prove_thm
  ("Next_ReachIn",
   ``!n. Next R (ReachIn R B n) = ReachIn R B (SUC n)``,
   RW_TAC std_ss [ReachIn_def]);

(*****************************************************************************)
(* ``Reachable R B state'' is true if state can be reached from a            *)
(* state satisfying B in some finite number of R-steps                       *)
(*****************************************************************************)

val Reachable_def =
 Define
  `Reachable R B state = ?n. ReachIn R B n state`;

val Reachable_eqn = 
 prove_thm
  ("Reachable_eqn",
   ``Reachable R B state =
      B state \/ Reachable R (Next R B) state``,
   REWRITE_TAC[Reachable_def,ReachIn_def,Next_def]
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL[DISJ_CASES_TAC(SPEC ``n:num`` num_CASES)
           THENL[PROVE_TAC[ReachIn_def],
                 PROVE_TAC[ReachIn_Next]],
          EXISTS_TAC ``0``
           THEN ASM_REWRITE_TAC[ReachIn_def],
          PROVE_TAC[ReachIn_Next]]);

val ReachBy_def =
 Define
  `ReachBy R B n state = 
    ?m. (m <= n) /\ ReachIn R B m state`;

val ReachIn_IMPLIES_ReachBy =
 prove_thm
  ("ReachIn_IMPLIES_ReachBy",
   ``ReachIn R B n state ==> ReachBy R B n state``,
   PROVE_TAC[ReachBy_def,LESS_EQ_REFL]);

(* Proof of  ReachBy_lemma below is gross -- done in zombie mode *)

val ReachBy_lemma = 
 prove_thm
  ("ReachBy_lemma",
   ``(!R B state.
       ReachBy R B 0 state = B state)
     /\
     (!R B n state.
       ReachBy R B (SUC n) state = 
        ReachBy R B n state 
        \/ 
        Next R (ReachBy R B n) state)``,
   REWRITE_TAC[ReachBy_def,ReachIn_def,LESS_EQ_0]
    THEN CONJ_TAC
    THEN REPEAT GEN_TAC
    THENL
     [PROVE_TAC[ReachIn_def],
      REWRITE_TAC[ReachBy_def]
       THEN EQ_TAC
       THEN REPEAT STRIP_TAC
       THENL
        [ASSUM_LIST(fn[th1,th2]=> 
                     DISJ_CASES_TAC
                      (EQ_MP 
                       (DECIDE ``(m <= SUC n) = (m <= n) \/ (m = SUC n)``)
                       th2))
          THENL
           [PROVE_TAC[],
            DISJ2_TAC
             THEN REWRITE_TAC[Next_def,ReachBy_def]
             THEN ASSUM_LIST
                   (fn[th1,th2,th3] => ASSUME_TAC(REWRITE_RULE[th1]th2))
             THEN IMP_RES_TAC(REWRITE_RULE[ReachIn_Next]ReachIn_expand)
             THEN EXISTS_TAC ``state_:'b``
             THEN ASM_REWRITE_TAC[]
             THEN EXISTS_TAC ``n:num``
             THEN RW_TAC arith_ss []],
         PROVE_TAC[DECIDE``(m<=n)==>(m<=SUC n)``],
         POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[Next_def,ReachBy_def])
          THEN IMP_RES_TAC ReachIn_expand
          THEN EXISTS_TAC ``SUC m``
          THEN ASM_REWRITE_TAC
                [GSYM(ReachIn_Next),DECIDE``(SUC m<=SUC n)=(m<=n)``]]]);

val ReachBy_rec = 
 store_thm
  ("ReachBy_rec",
   ``(!R B state.
       ReachBy R B 0 state = B state)
     /\
     (!R B n state.
       ReachBy R B (SUC n) state = 
        ReachBy R B n state 
        \/ 
        ?state_. ReachBy R B n state_ /\ R (state_,state))``,
   PROVE_TAC[ReachBy_lemma,Next_def]);

val ReachBy_ReachIn = 
 store_thm
  ("ReachBy_ReachIn",
   ``(!R B state.
       ReachBy R B 0 state = B state)
     /\
     (!R B n state.
       ReachBy R B (SUC n) state = 
        ReachBy R B n state \/ ReachIn R B (SUC n) state)``,
   REWRITE_TAC[ReachBy_def,ReachIn_def,LESS_EQ_0]
    THEN CONJ_TAC
    THEN REPEAT GEN_TAC
    THENL
     [PROVE_TAC[ReachIn_def],
      EQ_TAC
       THEN REPEAT STRIP_TAC
       THENL
        [ASSUM_LIST(fn[th1,th2]=> 
                     DISJ_CASES_TAC
                      (EQ_MP 
                       (DECIDE ``(m <= SUC n) = (m <= n) \/ (m = SUC n)``)
                       th2))
          THEN PROVE_TAC[Next_ReachIn],
         PROVE_TAC[DECIDE ``m <= n ==> m <= SUC n``],
         EXISTS_TAC ``SUC n``
          THEN ASM_REWRITE_TAC[LESS_EQ_REFL,GSYM Next_ReachIn]]]);

val Reachable_ReachBy =
 store_thm
  ("Reachable_ReachBy",
   ``Reachable R B state = ?n. ReachBy R B n state``,
   PROVE_TAC[Reachable_def,ReachBy_def,LESS_EQ_REFL]);
   
val ReachBy_mono =
 prove_thm
  ("ReachBy_mono",
   ``!m. ReachBy R B m state 
         ==> 
         !n. ReachBy R B (m+n) state``,
   REWRITE_TAC[ReachBy_def]
    THEN GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THEN ASM_REWRITE_TAC[ADD_CLAUSES]
    THEN POP_ASSUM STRIP_ASSUME_TAC
    THEN ASSUM_LIST
          (fn[th1,th2,th3]
             => ASSUME_TAC(MP(DECIDE``(m' <= m + n)==>(m'<=SUC(m+n))``)th2))
    THEN PROVE_TAC[]);
   
val ReachBy_mono_cor =
 prove_thm
  ("ReachBy_mono_cor",
   ``ReachBy R B n state 
     ==> 
     ReachBy R B (SUC n) state``,
   PROVE_TAC[ReachBy_mono,DECIDE``SUC n = n+1``]);

val ReachBy_LESS =
 prove_thm
  ("ReachBy_LESS",
   ``!n m. m <= n /\ ReachIn R B m state 
           ==> ReachBy R B n state``,
   Induct
    THEN PROVE_TAC [ReachBy_def]);

val Next_ReachIn_ReachBy =
 prove_thm
  ("Next_ReachIn_ReachBy",
   ``!n. Next R (ReachIn R B n) state
         ==>
         Next R (ReachBy R B n) state``,
   PROVE_TAC[LESS_EQ_REFL,ReachBy_LESS,Next_def]);

val fixedpoint_Next = 
 prove_thm
  ("fixedpoint_Next",
   ``(ReachBy R B n = ReachBy R B (SUC n))
     ==>
     (!state'. Next R (ReachBy R B n) state'
               ==>
               ReachBy R B n state')``,
   CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
    THEN REWRITE_TAC[ReachBy_ReachIn,ReachIn_def,Next_def]
    THEN REPEAT STRIP_TAC
    THEN ASSUM_LIST
          (fn[th1,th2,th3]=> 
            STRIP_ASSUME_TAC
             (MATCH_MP (DECIDE``(A = A \/ B) ==> (B ==> A)``)
                       (SPEC ``state':'a`` th3)))
    THEN POP_ASSUM(MAP_EVERY ASSUME_TAC o IMP_CANON)
    THEN IMP_RES_TAC ReachBy_def
    THEN IMP_RES_TAC (DECIDE ``(m<=n)==>(m=n) \/(m<n)``)
    THEN PROVE_TAC
          [REWRITE_RULE[Next_def]((CONV_RULE(DEPTH_CONV FUN_EQ_CONV))ReachIn_def),
           DECIDE``(m<n)==>(SUC m<=n)``,
           ReachBy_LESS]);

val fixedpoint_Next_cor = 
 prove_thm
  ("fixedpoint_Next_cor",
   ``(ReachBy R B n = ReachBy R B (SUC n))
     ==>
     (!state'. Next R (ReachBy R B (SUC n)) state'
               ==>
               ReachBy R B (SUC n) state')``,
   PROVE_TAC[fixedpoint_Next]);

val fixedpoint_SUC = 
 prove_thm
  ("fixedpoint_SUC",
   ``(ReachBy R B n = ReachBy R B (SUC n))
     ==>
     (ReachBy R B (SUC n) = ReachBy R B (SUC(SUC n)))``,
   DISCH_TAC
    THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
    THEN GEN_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
     [IMP_RES_TAC ReachBy_mono_cor,
      POP_ASSUM(ASSUME_TAC o ONCE_REWRITE_RULE[ReachBy_ReachIn])
       THEN POP_ASSUM(ASSUME_TAC o ONCE_REWRITE_RULE[ReachIn_def])
       THEN PROVE_TAC [Next_ReachIn_ReachBy,fixedpoint_Next_cor]]);

val fixedpoint_lemma1 = 
 prove_thm
  ("fixedpoint_lemma1",
   ``(ReachBy R B n = ReachBy R B (SUC n))
     ==>
     !m. ReachBy R B (n+m) = ReachBy R B (SUC(n+m))``,
   DISCH_TAC
    THEN Induct
    THEN ASM_REWRITE_TAC[ADD_CLAUSES]
    THEN IMP_RES_TAC fixedpoint_SUC);

val fixedpoint_lemma2 = 
 prove_thm
  ("fixedpoint_lemma2",
   ``(ReachBy R B n = ReachBy R B (SUC n))
     ==>
     !m. ReachBy R B n = ReachBy R B (n+m)``,
   DISCH_TAC
    THEN Induct
    THEN PROVE_TAC[ADD_CLAUSES,fixedpoint_lemma1]);

val ReachBy_fixedpoint = 
 store_thm
  ("ReachBy_fixedpoint",
   ``!R B n.
      (ReachBy R B n = ReachBy R B (SUC n))
      ==>
      (Reachable R B = ReachBy R B n)``,
   REPEAT STRIP_TAC
    THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
    THEN REWRITE_TAC[Reachable_def]
    THEN GEN_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
     [ASM_CASES_TAC ``n'<=n``
       THENL
        [IMP_RES_TAC ReachBy_def,
         IMP_RES_TAC(DECIDE``~(n' <= n) ==> n < n'``)
          THEN IMP_RES_TAC(ONCE_REWRITE_RULE[ADD_SYM]LESS_ADD)
          THEN IMP_RES_TAC ReachIn_IMPLIES_ReachBy
          THEN PROVE_TAC[fixedpoint_lemma2]],
      PROVE_TAC[ReachBy_def]]);

val _ = export_theory();
