(*****************************************************************************)
(* HolBddScript.sml                                                          *)
(* ----------------                                                          *)
(*                                                                           *)
(* Script for proving miscellaneous theorems.                                *)
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
open DerivedBddRulesTheory;

val _ = new_theory "HolBdd";

val DEPTH_EXISTS_CONV = unwindLib.DEPTH_EXISTS_CONV
and EXPAND_AUTO_CONV  = unwindLib.EXPAND_AUTO_CONV;

fun prove_thm(_:string,tm,tac) = prove(tm,tac);

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
   ``((x = (b => y | z)) = (b => (x = y) | (x = z)))
     /\
     (((b => y | z) = x) = (b => (y = x) | (z = x)))``,
   ZAP_TAC std_ss []);

val COND_SIMP =
 store_thm
  ("COND_SIMP",
   ``((b =>  F  |  F)  =  F)        /\
     ((b =>  F  |  T)  = ~b)        /\
     ((b =>  T  |  F)  =  b)        /\
     ((b =>  T  |  T)  =  T)        /\
     ((b =>  x  |  x)  =  x)        /\
     ((b =>  b' | ~b') =  (b = b')) /\
     ((b => ~b' |  b') =  (b = ~b'))``,
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
       THEN Q.EXISTS_TAC `f(SUC 0)`
       THEN ASSUM_LIST(ASSUME_TAC o SIMP_RULE arith_ss [DECIDE ``1 = SUC 0``] o SPEC ``0`` o hd)
       THEN RW_TAC arith_ss [DECIDE ``0<SUC n /\ (SUC 0 = 1)``,ADD_CLAUSES]
       THEN `R (f 0,f (SUC 0))` 
            by PROVE_TAC[DECIDE ``0<SUC n /\ (SUC 0 = 1)``,ADD_CLAUSES]
       THEN Q.EXISTS_TAC `\i. f(i+1):'b`
       THEN RW_TAC arith_ss [DECIDE``SUC n = n+1``]
       THEN `R (f(SUC m),f(SUC m + 1))` by PROVE_TAC[DECIDE``(m<n)=(SUC m < SUC n)``]
       THEN FULL_SIMP_TAC std_ss [DECIDE``(SUC m = m+1) /\ (SUC m + 1 = m+2)``],
      Q.EXISTS_TAC `\i. if (i=0) then state1 else f(i-1)`
       THEN RW_TAC std_ss [DECIDE ``(SUC n - 1 = n) /\ (n+1-1 = n)``]
       THEN IMP_RES_TAC(DECIDE``~(m+1=0)``)
       THEN IMP_RES_TAC(DECIDE``~(m=0) ==> (m < SUC n) ==> (m-1 < n)``)
       THEN RES_TAC
       THEN IMP_RES_TAC(DECIDE``~(m=0) ==> (m - 1 + 1 = m)``)
       THEN ASSUM_LIST(fn thl => ACCEPT_TAC(REWRITE_RULE[el 1 thl](el 3 thl)))]);

val Total_def = Define `Total R = !s.?s'. R(s,s')`;

val ChoosePath_def = 
 Define 
  `(ChoosePath R s 0 = s) 
   /\ 
   (ChoosePath R s (SUC n) = @s'. R(ChoosePath R s n, s'))`;

val TotalPathExists =
 store_thm
  ("TotalpathExists",
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
  [prove(``!m. m <= n ==>
            (f m = (if m <= n then f m else ChoosePath R (f n) m))``,
         RW_TAC std_ss [])]
  (BETA_RULE(SPECL[``f:num->'a``,
                   ``\m. if m <= n then (f:num->'a) m else ChoosePath R (f n) m``,
                   ``n:num``]FinPathLemma));

(* Next proof got messy when ported to KAnanaskis. Should be cleaned up. *)

val FinPathPathExists =
 store_thm
  ("FinPathPathExists",
   ``!R B f s n. 
      Total R /\ FinPath(R,s) f n 
      ==> 
      ?g. (!m. (m <= n) ==> (f m = g m)) /\ Path(R,s)g``,
   REPEAT STRIP_TAC
    THEN IMP_RES_TAC TotalPathExists
    THEN POP_ASSUM(ASSUME_TAC o SPEC ``(f:num->'a)n``)
    THEN EXISTS_TAC ``\m. if m <= n then f m else ChoosePath R (f n) (m - n)``
    THEN RW_TAC std_ss [Path_def,ARITH_PROVE``0 <= n``]
    THENL
     [IMP_RES_TAC FinPathThm,
      IMP_RES_TAC FinPathChoosePath
       THEN ASM_CASES_TAC ``n' <= n``
       THEN ASM_REWRITE_TAC[]
       THENL
        [ASM_CASES_TAC ``n'+1 <= n``
          THEN ASM_REWRITE_TAC[]
          THENL
           [IMP_RES_TAC(ARITH_PROVE``(n'+1 <= n) ==> (n' < n)``)
             THEN IMP_RES_TAC FinPathThm,
            IMP_RES_TAC(ARITH_PROVE(``(n' <= n) /\ ~(n'+1 <= n) ==> (n' = n)``))
             THEN ASM_REWRITE_TAC[ARITH_PROVE``(n + 1 - n) = 1``]
             THEN IMP_RES_TAC TotalPathExists
             THEN POP_ASSUM(ASSUME_TAC o SPEC ``(f:num->'a)n``)
             THEN IMP_RES_TAC Path_def
             THEN POP_ASSUM(ASSUME_TAC o REWRITE_RULE[ADD_CLAUSES] o SPEC ``0``)
             THEN PROVE_TAC[]],
         IMP_RES_TAC(ARITH_PROVE``~(n' <= n) ==> ~(n'+1 <= n)``)
          THEN ASM_REWRITE_TAC[]
          THEN IMP_RES_TAC(ARITH_PROVE``~(n' <= n) ==> ((n' + 1 - n) = (n' - n) + 1)``)
          THEN ASM_REWRITE_TAC[]
          THEN IMP_RES_TAC Path_def
          THEN POP_ASSUM(ACCEPT_TAC o REWRITE_RULE[ADD_CLAUSES] o SPEC ``n' - n``)],
      IMP_RES_TAC(ARITH_PROVE(``(n' <= n) /\ ~(n'+1 <= n) ==> (n' = n)``))
       THEN ASM_REWRITE_TAC[ARITH_PROVE``(n + 1 - n) = 1``]
       THEN IMP_RES_TAC TotalPathExists
       THEN POP_ASSUM(ASSUME_TAC o SPEC ``(f:num->'a)n``)
       THEN IMP_RES_TAC Path_def
       THEN POP_ASSUM(ASSUME_TAC o REWRITE_RULE[ADD_CLAUSES] o SPEC ``0``)
       THEN PROVE_TAC[],
      IMP_RES_TAC(ARITH_PROVE``~(n' <= n) ==> ~(n'+1 <= n)``),
      IMP_RES_TAC(ARITH_PROVE``~(n' <= n) ==> ((n' + 1 - n) = (n' - n) + 1)``)
        THEN ASM_REWRITE_TAC[]
        THEN IMP_RES_TAC Path_def
        THEN POP_ASSUM(ACCEPT_TAC o REWRITE_RULE[ADD_CLAUSES] o SPEC ``n' - n``)]);

val ReachInPath =
 store_thm
  ("ReachInPath",
   ``!R B n s. Total R ==> (ReachIn R B n s = ?f s0. B s0 /\ Path(R,s0)f /\ (s = f n))``,
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
   ``!R B s. Total R ==> (Reachable R B s = ?f s0. B s0 /\ Path(R,s0)f /\ ?n. (s = f n))``,
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

(*
val TotalImpTotalise =
 save_thm
  ("TotalImpTotalise",
   DISCH_ALL
    (PEXT(PGEN ``((s:'a),(s':'a))`` (GSYM(SPEC_ALL(UNDISCH TotalImpTotaliseLemma))))));
*)

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
    (REWRITE_RULE[ReachableTotalise,TotalTotalise](SPEC ``Totalise R`` ReachablePath)));

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
    

(*
val MooreTransEq =
 save_thm
  ("MooreTransEq",
   CONV_RULE
    (DEPTH_CONV PETA_CONV)
    (PABS
     ``((input:'a,state:'b),input':'a,state':'b)``
     (SPEC_ALL MooreTrans_def)));
*)

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

val ReachableMooreTrans = 
 save_thm
  ("ReachableMooreTrans",
   SPECL
    [``\(input:'a,state:'b). (input = inputs 0) /\ (state = states 0)``,
     ``(input:'a, state:'b)``]
    (MATCH_MP ReachablePath TotalMooreTrans));

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

val PAIR_Lemma1 =
 prove_thm
  ("PAIR_Lemma1",
   ``(\t. ((if t = 0 then FST s0 else FST (f t)),
          (if t = 0 then SND s0 else SND (f t))))
     =
     (\t. if t = 0 then s0 else f t)``,
   CONV_TAC FUN_EQ_CONV
    THEN RW_TAC std_ss []);

val PAIR_Lemma2 =
 prove_thm
  ("PAIR_Lemma21",
   ``((if t = 0 then FST s0 else FST (f t)),
      (if t = 0 then SND s0 else SND (f t)))
     =
     (if t = 0 then s0 else f t)``,
   RW_TAC std_ss []);
 
val COND_Lemma1 =
 prove_thm
  ("COND_Lemma1",
   ``(\t. (if t = 0 then f 0 else f t)) = f``,
   CONV_TAC FUN_EQ_CONV
    THEN RW_TAC std_ss []);

val COND_Lemma2 =
 prove_thm
  ("COND_Lemma2",
   ``(if t = 0 then f 0 else f t) = f t``,
   RW_TAC std_ss []);

val MooreReachable1 =
 store_thm
  ("MooreReachable1",
   ``(!inputs states. 
       B(inputs 0, states 0) /\ Moore nextfn (inputs,states) 
       ==> !t. P(inputs t, states t))
     ==>
     (!s. Reachable (MooreTrans nextfn) B s ==> P s)``,
   REWRITE_TAC[ReachableMooreTrans,MoorePath]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN ASSUM_LIST(fn thl => (ASSUME_TAC                                          o
                               REWRITE_RULE[el 3 thl,PAIR,PAIR_Lemma1,PAIR_Lemma2] o
                               BETA_RULE                                           o
                               SPECL
                                [``\t. if t=0 then FST(s0:'a#'b) else FST((f :num -> 'a # 'b) t)``,
                                 ``\t. if t=0 then SND(s0:'a#'b) else SND((f :num -> 'a # 'b) t)``])
                              (el 4 thl))
    THEN IMP_RES_TAC Path_def
    THEN ASSUM_LIST(fn thl => ASSUME_TAC
                               (REWRITE_RULE
                                 [SYM(el 2 thl),COND_Lemma1,COND_Lemma2]
                                 (el 3 thl)))
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(PURE_REWRITE_RULE[el 3 thl](el 1 thl)))
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(ONCE_REWRITE_RULE[ETA_AX](el 1 thl)))
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);

val IMP_EXISTS_Lemma =
 prove_thm
  ("IMP_EXISTS_Lemma",
   ``((?x y. P x y) ==> Q) = !x y. P x y ==> Q``,
   PROVE_TAC[]);

val MooreReachable2 =
 store_thm
  ("MooreReachable2",
   ``(!s. Reachable (MooreTrans nextfn) B s ==> P s)
     ==>
     (!inputs states. 
        B(inputs 0, states 0) /\ Moore nextfn (inputs,states) 
        ==> !t. P(inputs t, states t))``,
   REWRITE_TAC[ReachableMooreTrans,MoorePath]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN ASSUM_LIST(fn thl => (ASSUME_TAC                                       o
                               REWRITE_RULE
                                [PROVE []``?(n :num). (inputs (t :num),states t) 
                                                       = (inputs n,states n)``] o
                               BETA_RULE                                        o
                               SPECL[``\(t :num). (inputs t,states t)``,
                                     ``((inputs:num->'a)0,(states:num->'b)0)``] o
                               Ho_Rewrite.REWRITE_RULE[IMP_EXISTS_Lemma]        o
                               SPECL
                                [``((inputs:num->'a) t, (states:num->'b) t)``])
                              (el 3 thl))
    THEN RES_TAC);

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
