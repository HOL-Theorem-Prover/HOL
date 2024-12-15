(*****************************************************************************)
(* MachineTransitionScript.sml                                               *)
(* ---------------------------                                               *)
(*                                                                           *)
(* Script for proving theorems to support DerivedBddRules                    *)
(*****************************************************************************)
(*                                                                           *)
(* Revision history:                                                         *)
(*                                                                           *)
(*   Wed Nov  7 11:29:35 GMT 2001 -- created file                            *)
(*                                                                           *)
(*****************************************************************************)

open HolKernel Parse boolLib;

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

val _ = new_theory "MachineTransition";
val _ = ParseExtras.temp_loose_equality()

(* These two don't seem to be used ...

val DEPTH_EXISTS_CONV = unwindLib.DEPTH_EXISTS_CONV
and EXPAND_AUTO_CONV  = unwindLib.EXPAND_AUTO_CONV;
*)

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

val EXISTS_IMP_EQ =
 store_thm
  ("EXISTS_IMP_EQ",
   ``((?x. P x) ==> Q) = (!x. P x ==> Q)``,
   PROVE_TAC[]);

val LENGTH_EQ_CONS_EXISTS =
 prove_thm
  ("LENGTH_EQ_CONS_EXISTS",
   ``!P. (?l. (LENGTH l = SUC n) /\ P l)
         =
         (?l. (LENGTH l = n)     /\ ?x. P(CONS x l))``,
   PROVE_TAC[LENGTH_CONS]);

val LENGTH_EQ_NIL_EXISTS =
 prove_thm
  ("LENGTH_EQ_NIL_EXISTS",
   ``!P. (?l. (LENGTH l = 0) /\ P l) = P[]``,
   PROVE_TAC[LENGTH_NIL]);

val EQ_COND =
 store_thm
  ("EQ_COND",
   ``((x = (if b then y else z)) = (if b then (x = y) else (x = z)))
     /\
     (((if b then y else z) = x) = (if b then (y = x) else (z = x)))``,
   ZAP_TAC std_ss []);

val COND_SIMP =
 store_thm
  ("COND_SIMP",
   ``((if b then  F  else  F)  =  F)        /\
     ((if b then  F  else  T)  = ~b)        /\
     ((if b then  T  else  F)  =  b)        /\
     ((if b then  T  else  T)  =  T)        /\
     ((if b then  x  else  x)  =  x)        /\
     ((if b then  b' else ~b') =  (b = b')) /\
     ((if b then ~b' else  b') =  (b = ~b'))``,
   ZAP_TAC std_ss []);

(*****************************************************************************)
(* IsTrace R B Q [s0;s1;...;sn] is true if B s0, Q sn and R(si,s(i+1)).      *)
(* In addition [s0;...;sn] is of minimal length to get from B to Q.          *)
(*****************************************************************************)

val IsTrace_def =
 Define
  `(IsTrace R B Q [] = F)
   /\
   (IsTrace R B Q [s] = B s /\ Q s)
   /\
   (IsTrace R B Q (s0 :: (s1 :: tr)) =
     B s0 /\ R(s0,s1) /\ IsTrace R (Eq s1) Q (s1 :: tr))`;


(*****************************************************************************)
(* ``Stable R state'' is true if all R-successors of state                   *)
(* are equal to state -- i.e. an R-step doesn't change the state             *)
(*****************************************************************************)

val Stable_def =
 Define
  `Stable R state = !state'. R(state,state') ==> (state' = state)`;

val Live_def =
 Define
  `Live R = !state. ?state'. R(state,state')`;

val ReachIn_Stable_SUC =
 prove_thm
  ("ReachIn_Stable_SUC",
   ``ReachIn R B n state /\ Stable R state /\ Live R
     ==>
     ReachIn R B (SUC n) state``,
   PROVE_TAC [ReachIn_def,Stable_def,Next_def,Live_def]);

val ReachIn_Stable =
 prove_thm
  ("ReachIn_Stable",
   ``!m. ReachIn R B m state /\ Stable R state /\ Live R
         ==>
         !n. m <= n ==> ReachIn R B n state``,
   GEN_TAC
    THEN DISCH_TAC
    THEN Induct
    THEN PROVE_TAC[LESS_EQ_0,ReachIn_Stable_SUC,
                   DECIDE``(m<=SUC n) = (m<=n)\/(m=SUC n)``]);

val ReachBy_Stable =
 prove_thm
  ("ReachBy_Stable",
   ``Live R
     ==>
     (ReachBy R B n state /\ Stable R state =
       ReachIn R B n state /\ Stable R state)``,
   PROVE_TAC[ReachBy_def,ReachIn_Stable,LESS_EQ_REFL]);

val Stable_ADD =
 prove_thm
  ("Stable_ADD",
   ``(!state. ReachIn R B m state ==> Stable R state)
     ==>
     !n state.
      ReachIn R B (m+n) state ==> ReachIn R B m state``,
   DISCH_TAC
    THEN Induct
    THENL
     [PROVE_TAC[ADD_CLAUSES],
      REWRITE_TAC[ADD_CLAUSES,ReachIn_def,Next_def]
       THEN REPEAT STRIP_TAC
       THEN RES_TAC
       THEN RES_TAC
       THEN PROVE_TAC[Stable_def]]);

val Reachable_Stable =
 store_thm
  ("Reachable_Stable",
   ``Live R
     /\
     (!state. ReachIn R B n state ==> Stable R state)
     ==>
     (!state.
       Reachable R B state /\ Stable R state = ReachIn R B n state)``,
   RW_TAC std_ss [Reachable_def]
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
     [DISJ_CASES_TAC(SPECL[``n':num``,``n:num``]LESS_OR_EQ_ADD)
       THENL
        [IMP_RES_TAC(DECIDE``(m<n)==>(m<=n)``)
          THEN PROVE_TAC[ReachIn_Stable],
         POP_ASSUM(STRIP_ASSUME_TAC o ONCE_REWRITE_RULE[ADD_SYM])
          THEN ASSUM_LIST
                (fn [th1,th2,th3,th4,th5] => ASSUME_TAC(REWRITE_RULE[th1]th3))
          THEN IMP_RES_TAC Stable_ADD],
      PROVE_TAC[],
      PROVE_TAC[]]);

val TraceReachIn =
 store_thm
  ("TraceReachIn",
   ``!R B tr. B(tr 0) /\ (!n. R(tr n, tr(n+1))) ==> !n. ReachIn R B n (tr n)``,
   REPEAT GEN_TAC
    THEN STRIP_TAC
    THEN Induct
    THEN PROVE_TAC[ReachIn_def,Next_def,ADD1]);

val ModelCheckAlways =
 store_thm
  ("ModelCheckAlways",
   ``!R B P.
      (!s. Reachable R B s ==> P s)
      ==>
      !tr. B(tr 0) /\ (!t. R(tr t, tr(t+1)))  ==> !t. P(tr t)``,
   PROVE_TAC[TraceReachIn,Reachable_def]);

val ModelCheckAlwaysCor1 =
 store_thm
  ("ModelCheckAlwaysCor1",
   ``(!s1 s2. Reachable R B (s1,s2) ==> P s1)
     ==>
     !tr. B (tr 0) /\ (!t. R (tr t,tr (t + 1))) ==> !t. P(FST(tr t))``,
 REWRITE_TAC
  [simpLib.SIMP_RULE
    bossLib.arith_ss
    [pairTheory.FORALL_PROD]
    (ISPECL
      [``R :('a1#'a2) # ('a1#'a2) -> bool``,
       ``B :('a1#'a2) -> bool``,
       ``\p:'a1#'a2. P(FST p):bool``]
      ModelCheckAlways)]);

val ModelCheckAlwaysCor2 =
 store_thm
  ("ModelCheckAlwaysCor2",
   ``!R B P.
      (!s1 s2. Reachable R B (s1,s2) ==> P s1)
      ==>
      !tr1. (?tr2. B(tr1 0,tr2 0) /\ !t. R((tr1 t,tr2 t), (tr1(t+1),tr2(t+1))))  ==> !t. P(tr1 t)``,
   REPEAT STRIP_TAC
    THEN IMP_RES_TAC ModelCheckAlwaysCor1
    THEN POP_ASSUM(ASSUME_TAC o
                   simpLib.SIMP_RULE bossLib.arith_ss [] o
                   ISPEC ``\n:num. (tr1 n:'a, tr2 n:'b)``)
    THEN PROVE_TAC[]);


val FnPair_def = Define `FnPair f g x = (f x, g x)`;

val FnPairAbs =
 store_thm
  ("FnPairAbs",
   ``(!tr:num->'a#'b. FnPair (\n. FST (tr n)) (\n. SND (tr n)) = tr)
     /\
    (!(tr1:num->'a)(tr2:num->'b). (\n. (tr1 n,tr2 n)) = FnPair tr1 tr2)``,
   CONJ_TAC
    THEN REPEAT GEN_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN simpLib.SIMP_TAC bossLib.arith_ss [FnPair_def]);

val FnPairExists =
 store_thm
  ("FnPairExists",
   ``!P. (?tr:num->'a#'b. P tr) = ?tr1 tr2. P(FnPair tr1 tr2)``,
   GEN_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL[EXISTS_TAC ``\n. FST((tr:num->'a#'b) n)``
           THEN EXISTS_TAC ``\n. SND((tr:num->'a#'b) n)``,
          EXISTS_TAC ``\n. ((tr1:num->'a) n, (tr2:num->'b) n)``]
    THEN ASM_REWRITE_TAC[FnPairAbs]);

val FnPairForall =
 store_thm
  ("FnPairForall",
   ``!P. (!tr:num->'a#'b. P tr) = !tr1 tr2. P(FnPair tr1 tr2)``,
   GEN_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL[ALL_TAC,
          ONCE_REWRITE_TAC[GSYM(CONJUNCT1 FnPairAbs)]]
    THEN PROVE_TAC[]);

(*****************************************************************************)
(*     |- !P rep.                                                            *)
(*          TYPE_DEFINITION P rep ==>                                        *)
(*          (?abs. (!a. abs (rep a) = a) /\ (!r. P r = rep (abs r) = r))     *)
(*****************************************************************************)

val ABS_EXISTS_THM = (* Adapted from Hol sources *)
   let val th1 = ASSUME (``?rep:'b->'a. TYPE_DEFINITION P rep``)
       and th2 = BETA_RULE
                  (AP_THM
                    (AP_THM TYPE_DEFINITION ``P:'a->bool``)
                    ``rep :'b -> 'a``)
       val def = EQ_MP (MK_EXISTS(Q.GEN `rep` th2)) th1
       val asm = ASSUME (#Body(Rsyntax.dest_exists(concl def)))
       val (asm1,asm2)  = CONJ_PAIR asm
       val rep_eq =
         let val th1 = DISCH (``a:'b=a'``)
                         (AP_TERM (``rep:'b->'a``) (ASSUME (``a:'b=a'``)))
         in IMP_ANTISYM_RULE (SPECL [(``a:'b``),(``a':'b``)] asm1) th1
         end
       val ABS = (``\r:'a. @a:'b. r = rep a``)
       val absd =  RIGHT_BETA (AP_THM (REFL ABS) (``rep (a:'b):'a``))
       val lem = SYM(SELECT_RULE(EXISTS ((``?a':'b.a=a'``),(``a:'b``))
                                        (REFL (``a:'b``))))
       val TH1 = GEN (``a:'b``)
                     (TRANS(TRANS absd (SELECT_EQ (``a':'b``) rep_eq)) lem)
       val t1 = SELECT_RULE(EQ_MP (SPEC (``r:'a``) asm2)
                                  (ASSUME (``(P:'a->bool) r``)))
       val absd2 =  RIGHT_BETA (AP_THM (REFL ABS) (``r:'a``))
       val imp1 = DISCH (``(P:'a->bool) r``) (SYM (SUBS [SYM absd2] t1))
       val t2 = EXISTS ((``?a:'b. r:'a = rep a``), (``^ABS r``))
                       (SYM(ASSUME (``rep(^ABS (r:'a):'b) = r``)))
       val imp2 = DISCH (``rep(^ABS (r:'a):'b) = r``)
                        (EQ_MP (SYM (SPEC (``r:'a``) asm2)) t2)
       val TH2 = GEN (``r:'a``) (IMP_ANTISYM_RULE imp1 imp2)
       val CTH = CONJ TH1 TH2
       val ath = subst [ABS |-> Term`abs:'a->'b`] (concl CTH)
       val eth1 = EXISTS ((``?abs:'a->'b. ^ath``), ABS) CTH
   in
    save_thm
     ("ABS_EXISTS_THM",
      REWRITE_RULE[GSYM th2](Q.GEN `P` (Q.GEN `rep` (DISCH_ALL eth1))))
   end;

val FORALL_REP =
 store_thm
  ("FORALL_REP",
   ``!abs rep P Q.
      (!a. abs (rep a) = a) /\ (!r. P r = (rep (abs r) = r))
      ==>
      ((!a. Q a) = (!r. P r ==> Q(abs r)))``,
   PROVE_TAC[]);

val EXISTS_REP =
 store_thm
  ("EXISTS_REP",
   ``!abs rep P Q.
      (!a. abs (rep a) = a) /\ (!r. P r = (rep (abs r) = r))
      ==>
      ((?a. Q a) = (?r. P r /\ Q(abs r)))``,
   PROVE_TAC[]);

val ABS_ONE_ONE =
 store_thm
  ("ABS_ONE_ONE",
   ``!abs rep.
      ((!a. abs(rep a) = a) /\ (!r. range r = (rep(abs r) = r)))
      ==>
      !r. range r /\ range r' ==> ((abs r = abs r') = (r = r'))``,
   PROVE_TAC[]);

(*****************************************************************************)
(* Theorems relating paths and transition relations                          *)
(*****************************************************************************)

val Path_def =
 Define
  `Path(R,s)f = (f 0 = s) /\ !n. R(f n, f(n+1))`;

val ReachInPath1 =
 prove_thm
  ("ReachInPath1",
   ``(?f s0. B s0 /\ Path(R,s0)f /\ (s = f n)) ==> ReachIn R B n s``,
   REWRITE_TAC[Path_def]
    THEN REPEAT STRIP_TAC
    THEN PROVE_TAC[TraceReachIn]);

val FinPath_def =
 Define
  `(FinPath(R,s) f 0 = (f 0 = s))
   /\
   (FinPath(R,s) f (SUC n) = FinPath(R,s) f n /\ R(f n, f(n+1)))`;

val FinFunEq =
 store_thm
  ("FinFunEq",
   ``(!m. m <= n+1 ==> (f1 m = f2 m)) = (!m. m <= n ==> (f1 m = f2 m)) /\ (f1(n+1) = f2(n+1))``,
   REWRITE_TAC[ARITH_PROVE ``(m <= n+1) = (m <= n) \/ (m = n+1)``]
    THEN PROVE_TAC[]);

val FinPathThm =
 store_thm
  ("FinPathThm",
   ``!n. FinPath (R,s) f n = (f 0 = s) /\ !m. (m < n) ==> R(f m, f(m+1))``,
   Induct
    THEN RW_TAC arith_ss [FinPath_def,ARITH_PROVE``(m < SUC n) = (m = n) \/ (m < n)``]
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN RW_TAC std_ss []);

val FinPathLemma =
 store_thm
  ("FinPathLemma",
   ``!f1 f2 n.
      (!m. m <= n ==> (f1 m = f2 m)) ==> (FinPath(R,s) f1 n = FinPath(R,s) f2 n)``,
   STRIP_TAC
    THEN STRIP_TAC
    THEN Induct
    THEN RW_TAC std_ss [FinPath_def,LESS_EQ_REFL,ADD1,ARITH_PROVE``n <= n+1``]
    THEN PROVE_TAC[FinFunEq]);

local
val th =
 MP(SPECL
     [``f:num->'a``,``\p. (if p <= n then f p else (s':'a))``,``n:num``]
     FinPathLemma)
   (prove
     (``!m. m <= n ==> (f m = (\p. (if p <= n then f p else s')) m)``,
      RW_TAC std_ss []))
in
val ReachInFinPath1 =
 prove_thm
  ("ReachInFinPath1",
   ``!R B n s. ReachIn R B n s ==> ?f s0. B s0 /\ FinPath(R,s0) f n /\ (s = f n)``,
   STRIP_TAC
    THEN STRIP_TAC
    THEN Induct
    THEN REWRITE_TAC[FinPath_def,ReachIn_def,Next_def,ADD1]
    THEN REPEAT STRIP_TAC
    THENL
     [EXISTS_TAC ``\n:num. s:'a``
       THEN PROVE_TAC[],
      RES_TAC
       THEN EXISTS_TAC ``\p. if p<=n then f p else (s:'a)``
       THEN EXISTS_TAC ``s0:'a``
       THEN RW_TAC std_ss [ARITH_PROVE``~(n+1 <= n) /\ (n <= n)``]
       THEN IMP_RES_TAC th (* PROVE_TAC[th] crashes *)
       THEN ASM_REWRITE_TAC[]])
end;

val ReachInFinPath2 =
 prove_thm
  ("ReachInFinPath2",
   ``!R B n s. (?f s0. B s0 /\ FinPath(R,s0) f n /\ (s = f n)) ==> ReachIn R B n s``,
   GEN_TAC
    THEN GEN_TAC
    THEN Induct
    THEN REWRITE_TAC[FinPath_def,ReachIn_def,Next_def,ADD1]
    THEN PROVE_TAC[]);

val ReachInFinPath =
 store_thm
  ("ReachInFinPath",
   ``!R B n s. ReachIn R B n s = ?f s0. B s0 /\ FinPath(R,s0) f n /\ (s = f n)``,
   PROVE_TAC[ReachInFinPath1,ReachInFinPath2]);

val ReachableFinPath =
 store_thm
  ("ReachableFinPath",
   ``!R B s. Reachable R B s = ?f s0 n. B s0 /\ FinPath(R,s0) f n /\ (s = f n)``,
   PROVE_TAC[ReachInFinPath,Reachable_def]);

(* Another gross proof! *)
val ReachIn_revrec =
 store_thm
  ("ReachIn_revrec",
   ``(!R B state.
       ReachIn R B 0 state = B state)
   /\
   (!R B n state.
     ReachIn R B (SUC n) state =
     (?state1 state2. B state1 /\ R(state1,state2) /\ ReachIn R (Eq state2) n state))``,
   SIMP_TAC std_ss [CONJUNCT1 ReachIn_rec,ReachInFinPath,FinPathThm,Eq_def]
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Q.EXISTS_TAC `f 0`
       THEN Q.EXISTS_TAC `f 1`
       THEN FIRST_ASSUM (Q.SPEC_THEN `0` (ASSUME_TAC o
                                          SIMP_RULE arith_ss []))
       THEN ASM_REWRITE_TAC []
       THEN Q.EXISTS_TAC `\i. f(i+1):'b`
       THEN RW_TAC arith_ss [GSYM ADD1]
       THEN `m + 1 < SUC n` by DECIDE_TAC
       THEN RW_TAC bool_ss [DECIDE``m + 2 = m + 1 + 1``, ADD1],
      Q.EXISTS_TAC `\i. if (i=0) then state1 else f(i-1)`
       THEN RW_TAC std_ss [DECIDE ``(SUC n - 1 = n) /\ (n+1-1 = n)``]
       THEN FIRST_X_ASSUM (Q.SPEC_THEN `m - 1` MP_TAC)
       THEN RW_TAC arith_ss []]);

val Total_def = Define `Total R = !s.?s'. R(s,s')`;

val ChoosePath_def =
 Define
  `(ChoosePath R s 0 = s)
   /\
   (ChoosePath R s (SUC n) = @s'. R(ChoosePath R s n, s'))`;

val TotalPathExists =
 store_thm
  ("TotalPathExists",
   ``Total R ==> !s. Path (R,s) (ChoosePath R s)``,
   REWRITE_TAC[Path_def,ChoosePath_def,GSYM ADD1]
    THEN REPEAT STRIP_TAC
    THEN CONV_TAC SELECT_CONV
    THEN IMP_RES_TAC Total_def
    THEN POP_ASSUM(ACCEPT_TAC o SPEC ``ChoosePath R s n``));

(*****************************************************************************)
(* val FinPathChoosePath =                                                   *)
(*  |- FinPath (R,s) f n =                                                   *)
(*     FinPath (R,s) (\m. (if m <= n then f m else ChoosePath R (f n) m)) n  *)
(*****************************************************************************)

val FinPathChoosePath =
 REWRITE_RULE
  [Q.prove(`!m. m <= n ==>
            (f m = (if m <= n then f m else ChoosePath R (f n) m))`,
         RW_TAC std_ss [])]
  (BETA_RULE(Q.SPECL[`f:num->'a`,
                `\m. if m <= n then (f:num->'a) m else ChoosePath R (f n) m`,
                `n:num`] FinPathLemma));

val FinPathPathExists =
 Q.store_thm
  ("FinPathPathExists",
   `!R B f s n.
      Total R /\ FinPath(R,s) f n
      ==>
      ?g. (!m. m <= n ==> (f m = g m)) /\ Path(R,s)g`,
   REPEAT STRIP_TAC
    THEN `Path (R, f n) (ChoosePath R (f n))` by PROVE_TAC [TotalPathExists]
    THEN Q.EXISTS_TAC `\m. if m <= n then f m else ChoosePath R (f n) (m-n)`
    THEN RW_TAC std_ss [Path_def,ZERO_LESS_EQ]
    THENL
     [PROVE_TAC [FinPathThm],
      IMP_RES_TAC FinPathChoosePath
       THEN BasicProvers.NORM_TAC std_ss []
       THENL
        [`m < n` by DECIDE_TAC THEN PROVE_TAC [FinPathThm],
         `m = n` by DECIDE_TAC THEN RW_TAC arith_ss []
                                THEN PROVE_TAC [Path_def,ADD_CLAUSES],
         PROVE_TAC [DECIDE (Term`x+1 <=y /\ ~(x <= y) ==> F`)],
         `n < m` by DECIDE_TAC
           THEN `m + 1 - n = (m - n) + 1` by DECIDE_TAC
           THEN PROVE_TAC [Path_def, ADD_CLAUSES]]]);

val ReachInPath =
 store_thm
  ("ReachInPath",
   ``!R B n s. Total R
                ==>
               (ReachIn R B n s = ?f s0. B s0 /\ Path(R,s0)f /\ (s = f n))``,
   REWRITE_TAC[ReachInFinPath]
    THEN REPEAT STRIP_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
     [IMP_RES_TAC FinPathPathExists
       THEN EXISTS_TAC ``g':num->'a``
       THEN EXISTS_TAC ``s0:'a``
       THEN PROVE_TAC[LESS_EQ_REFL],
      EXISTS_TAC ``f:num->'a``
       THEN EXISTS_TAC ``s0:'a``
       THEN PROVE_TAC[FinPathThm,Path_def]]);

val ReachablePath =
 store_thm
  ("ReachablePath",
   ``!R B s. Total R
              ==>
             (Reachable R B s = ?f s0. B s0 /\ Path(R,s0)f /\ ?n. (s = f n))``,
   PROVE_TAC[ReachInPath,Reachable_def]);

val Totalise_def =
 Define
  `Totalise R (s,s') = R(s,s') \/ (~(?s''. R(s,s'')) /\ (s = s'))`;

val TotalTotalise =
 store_thm
  ("TotalTotalise",
   ``Total(Totalise R)``,
   PROVE_TAC[Total_def,Totalise_def]);

val TotalImpTotaliseLemma =
 store_thm
  ("TotalImpTotaliseLemma",
   ``Total R ==> !s s'. R (s,s') = Totalise R (s,s')``,
   PROVE_TAC[Total_def,Totalise_def]);

(*****************************************************************************)
(* val TotalImpTotalise = |- Total R ==> (Totalise R = R) : Thm.thm          *)
(*****************************************************************************)

val TotalImpTotalise =
 store_thm
  ("TotalImpTotalise",
   ``Total R ==> (Totalise R = R)``,
   REPEAT STRIP_TAC
    THEN CONV_TAC FUN_EQ_CONV
    THEN REPEAT STRIP_TAC
    THEN Cases_on `p`
    THEN IMP_RES_TAC TotalImpTotaliseLemma
    THEN RW_TAC std_ss []);

val TotaliseReachBy =
 store_thm
  ("TotaliseReachBy",
   ``!n s. ReachBy (Totalise R) B n s = ReachBy R B n s``,
   Induct
    THEN RW_TAC std_ss [ReachBy_rec,Totalise_def,Next_def]
    THEN PROVE_TAC[]);

val ReachableTotalise =
 store_thm
  ("ReachableTotalise",
   ``Reachable (Totalise R) = Reachable R``,
   CONV_TAC (REDEPTH_CONV FUN_EQ_CONV)
    THEN RW_TAC std_ss [Reachable_ReachBy,TotaliseReachBy]
    THEN PROVE_TAC[]);

(*****************************************************************************)
(*  val ReachablePathThm =                                                   *)
(*  |- !R B s.                                                               *)
(*       Reachable R B s =                                                   *)
(*          ?f s0. B s0 /\ Path (Totalise R,s0) f /\ ?n. s = f n             *)
(*****************************************************************************)

val ReachablePathThm =
 save_thm
  ("ReachablePathThm",
   GEN
    ``R :'a # 'a -> bool``
    (REWRITE_RULE[ReachableTotalise,TotalTotalise]
                 (SPEC ``Totalise R`` ReachablePath)));

val Moore_def =
 Define
  `Moore nextfn ((inputs:num->'a),(states:num->'b)) =
    !t. states(t+1) = nextfn(inputs t,states t)`;

val MooreTrans_def =
 Define
  `MooreTrans nextfn (((input:'a),(state:'b)),((input':'a),(state':'b))) =
    (state' = nextfn(input,state))`;

(*****************************************************************************)
(*   val MooreTransEq =                                                      *)
(*     |- MooreTrans nextfn =                                                *)
(*        (\((input,state),input',state'). state' = nextfn (input,state))    *)
(*****************************************************************************)

val MooreTransEq =
 store_thm
  ("MooreTransEq",
   ``MooreTrans nextfn =
      \((input,state),input',state'). state' = nextfn (input,state)``,
   CONV_TAC FUN_EQ_CONV
    THEN REPEAT GEN_TAC
    THEN Cases_on `p`
    THEN Cases_on `q`
    THEN Cases_on `r`
    THEN CONV_TAC(DEPTH_CONV PAIRED_BETA_CONV)
    THEN RW_TAC std_ss [MooreTrans_def]);

val MoorePath =
 store_thm
  ("MoorePath",
   ``Moore nextfn (inputs,states) =
     Path
      (MooreTrans nextfn, (inputs 0,states 0))
      (\t. (inputs t, states t))``,
   RW_TAC std_ss [Path_def,MooreTrans_def,Moore_def]);

val TotalMooreTrans =
 store_thm
  ("TotalMooreTrans",
   ``Total(MooreTrans nextfn)``,
   RW_TAC std_ss [Total_def]
    THEN Cases_on `s`
    THEN Q.EXISTS_TAC `(q',nextfn(q,r))`
    THEN RW_TAC std_ss [MooreTrans_def]);

(* NOTE: duplicated with the next theorem but let's keep the original code:
val ReachableMooreTrans =
 save_thm
  ("ReachableMooreTrans",
   SPECL
    [``\(input:'a,state:'b). (input = inputs 0) /\ (state = states 0)``,
     ``(input:'a, state:'b)``]
    (MATCH_MP ReachablePath TotalMooreTrans));
 *)

(*****************************************************************************)
(*   val ReachableMooreTrans =                                               *)
(*     |- !B s.                                                              *)
(*          Reachable (MooreTrans nextfn) B s =                              *)
(*          ?f s0. B s0 /\ Path (MooreTrans nextfn,s0) f /\ ?n. s = f n      *)
(*****************************************************************************)

val ReachableMooreTrans =
 save_thm
  ("ReachableMooreTrans",
   MATCH_MP ReachablePath TotalMooreTrans);

(* Problem with Q.SPECL? Too many type annotations needed. *)

val MooreReachable1 =
 Q.store_thm
  ("MooreReachable1",
   `(!inputs states.
       B(inputs 0, states 0) /\ Moore nextfn (inputs,states)
       ==> !t. P(inputs t, states t))
     ==>
     (!s. Reachable (MooreTrans nextfn) B s ==> P s)`,
   RW_TAC std_ss [ReachableMooreTrans,MoorePath]
    THEN Q.PAT_X_ASSUM `$! M`
         (MP_TAC o REWRITE_RULE [PAIR] o BETA_RULE o Q.SPECL
           [`\t. if t=0 then FST (s0:'a#'b) else FST(f t:'a#'b)`,
            `\t. if t=0 then SND (s0:'a#'b) else SND(f t:'a#'b)`])
   THEN RW_TAC std_ss [COND_RAND,COND_RATOR]
   THEN `f:num->'a#'b = \t. if t=0 then s0 else f t`
        by (RW_TAC std_ss [FUN_EQ_THM] THEN PROVE_TAC [Path_def])
   THEN Q.PAT_X_ASSUM `Path x y` MP_TAC THEN ONCE_ASM_REWRITE_TAC[]
   THEN BETA_TAC THEN PROVE_TAC []);

val MooreReachable2 =
 store_thm
  ("MooreReachable2",
   ``(!s. Reachable (MooreTrans nextfn) B s ==> P s)
     ==>
     (!inputs states.
        B(inputs 0, states 0) /\ Moore nextfn (inputs,states)
        ==> !t. P(inputs t, states t))``,
   RW_TAC std_ss [ReachableMooreTrans,MoorePath]
    THEN Q.PAT_X_ASSUM `$! M`
         (MP_TAC o BETA_RULE
                 o Q.SPECL [`\t. (inputs t,states t)`, `(inputs 0,states 0)`]
                 o Ho_Rewrite.REWRITE_RULE [GSYM LEFT_FORALL_IMP_THM]
                 o Q.SPEC `(inputs (t:num), states t)`)
    THEN RW_TAC std_ss []
    THEN PROVE_TAC []);

val MooreReachable =
 store_thm
  ("MooreReachable",
   ``!B nextfn P.
      (!inputs states.
         B(inputs 0, states 0) /\ Moore nextfn (inputs,states)
         ==> !t. P(inputs t, states t))
      =
      (!s. Reachable (MooreTrans nextfn) B s ==> P s)``,
   REPEAT GEN_TAC
    THEN EQ_TAC
    THEN REWRITE_TAC[MooreReachable1,MooreReachable2]);


(*****************************************************************************)
(*   val MooreReachableExists =                                              *)
(*     |- (?inputs states.                                                   *)
(*           (B (inputs 0,states 0) /\ Moore nextfn (inputs,states)) /\      *)
(*           ?t. P (inputs t,states t)) =                                    *)
(*        ?s. Reachable (MooreTrans nextfn) B s /\ P s                       *)
(*****************************************************************************)

val MooreReachableExists =
 save_thm
  ("MooreReachableExists",
   (REWRITE_RULE[]                                      o
    CONV_RULE(REDEPTH_CONV NOT_FORALL_CONV)             o
    REWRITE_RULE[TAUT_PROVE ``~(a ==> b) = (a /\ ~b)``] o
    CONV_RULE(REDEPTH_CONV NOT_FORALL_CONV)             o
    ONCE_REWRITE_RULE[TAUT_PROVE ``(a=b) = (~a=~b)``]   o
    BETA_RULE                                           o
    SPECL[``B :'a # 'b -> bool``,
          ``nextfn :'a # 'b -> 'b``,
          ``\p. ~(P :'a # 'b -> bool)p``])
   MooreReachable);

val MooreReachableCor1 =
 store_thm
  ("MooreReachableCor1",
   ``!B nextfn.
      (!inputs states.
         B(inputs 0, states 0) /\
         (!t.  states (t + 1) = nextfn (inputs t,states t))
         ==> !t. P(inputs t, states t))
      =
      (!s. Reachable (\((i,s),(i',s')). s' = nextfn(i,s)) B s ==> P s)``,
   RW_TAC std_ss [GSYM MooreReachable,GSYM Moore_def,GSYM MooreTransEq]);

val _ = export_theory();
