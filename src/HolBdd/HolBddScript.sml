(* Exports
ReachBy_rec
Next_def
ReachBy_fixedpoint
ReachIn_def
ReachBy_ReachIn
IsTrace_def
Stable_def
Live_def
Reachable_def
Reachable_Stable
ReachIn_rec
Prev_def
Eq_def
Prev_Next_Eq
EXISTS_IMP
EQ_COND
COND_SIMP
*)



(*
(* load "bossLib";     overkill ... can be done with more basic components *)
load "BasicProvers";
load "SingleStep";
load "TotalDefn";
load "arithSimps";
load "Ho_Rewrite";
load "listTheory";
load "numLib";
load "unwindLib";
load "HolBdd";
load "pairLib";
*)

open Globals HolKernel Parse boolLib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

(* open bossLib; *)
open BasicProvers TotalDefn SingleStep;
open arithmeticTheory;
open listTheory;
open pairTheory;
open Ho_Rewrite;
open numLib;
open HolBdd;

val _ = new_theory "HolBdd";

val DEPTH_EXISTS_CONV = unwindLib.DEPTH_EXISTS_CONV
and EXPAND_AUTO_CONV  = unwindLib.EXPAND_AUTO_CONV;

(*
val PGEN = pairTools.PGEN
val PGEN_TAC = pairTools.PGEN_TAC;
*)

(*---------------------------------------------------------------------------
       Instead of loading in all of bossLib.
 ---------------------------------------------------------------------------*)

fun DECIDE q = 
  let val tm = Parse.Term q
  in EQT_ELIM(numLib.ARITH_CONV tm)
     handle HOL_ERR _ => BasicProvers.PROVE [] tm
  end;

val arith_ss = simpLib.++(bool_ss,numSimps.ARITH_ss);

fun prove_thm(_:string,tm,tac) = prove(tm,tac);

val EXISTS_IMP = 
 store_thm
  ("EXISTS_IMP",
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
   PROVE_TAC[]);

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
   PROVE_TAC[]);

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
 store_thm
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
    THEN RW_TAC bool_ss [ReachIn_def,Next_def]);

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
   RW_TAC bool_ss[ReachIn_def]);

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
    THENL[Cases_on `n`
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

(*

REC 0 S B x = B x

REC (SUC n) S B = S (REC n S B) x

ReachBy n R B s =
 REC n B (\f. f s \/ Next R f s) s

*)


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
                       (DECIDE `(m <= SUC n) = (m <= n) \/ (m = SUC n)`)
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
         PROVE_TAC[DECIDE`(m<=n)==>(m<=SUC n)`],
         POP_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[Next_def,ReachBy_def])
          THEN IMP_RES_TAC ReachIn_expand
          THEN EXISTS_TAC ``SUC m``
          THEN ASM_REWRITE_TAC
                [GSYM(ReachIn_Next),LESS_EQ_MONO]]]);

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
                       (DECIDE `(m <= SUC n) = (m <= n) \/ (m = SUC n)`)
                       th2))
          THEN PROVE_TAC[Next_ReachIn],
         PROVE_TAC[DECIDE `m <= n ==> m <= SUC n`],
         EXISTS_TAC ``SUC n``
          THEN ASM_REWRITE_TAC[LESS_EQ_REFL,GSYM Next_ReachIn]]]);

val Reachable_ReachBy =
 prove_thm
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
             => ASSUME_TAC(MP(DECIDE`(m' <= m + n)==>(m'<=SUC(m+n))`)th2))
    THEN PROVE_TAC[]);
   
val ReachBy_mono_cor =
 prove_thm
  ("ReachBy_mono_cor",
   ``ReachBy R B n state 
     ==> 
     ReachBy R B (SUC n) state``,
   PROVE_TAC[ReachBy_mono,DECIDE`SUC n = n+1`]);

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
             (MATCH_MP (DECIDE`(A = A \/ B) ==> (B ==> A)`)
                       (SPEC ``state':'a`` th3)))
    THEN POP_ASSUM(MAP_EVERY ASSUME_TAC o IMP_CANON)
    THEN IMP_RES_TAC ReachBy_def
    THEN IMP_RES_TAC (DECIDE `(m<=n)==>(m=n) \/(m<n)`)
    THEN PROVE_TAC
          [REWRITE_RULE[Next_def]((CONV_RULE(DEPTH_CONV FUN_EQ_CONV))ReachIn_def),
           DECIDE`(m<n)==>(SUC m<=n)`,
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
     [Cases_on `n'<=n`
       THENL
        [IMP_RES_TAC ReachBy_def,
         IMP_RES_TAC(DECIDE`~(n' <= n) ==> n < n'`)
          THEN IMP_RES_TAC(ONCE_REWRITE_RULE[ADD_SYM]LESS_ADD)
          THEN IMP_RES_TAC ReachIn_IMPLIES_ReachBy
          THEN PROVE_TAC[fixedpoint_lemma2]],
      PROVE_TAC[ReachBy_def]]);

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
                   DECIDE`(m<=SUC n) = (m<=n)\/(m=SUC n)`]);

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
   RW_TAC bool_ss[Reachable_def]
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL
     [DISJ_CASES_TAC(SPECL[``n':num``,``n:num``]LESS_OR_EQ_ADD)
       THENL
        [IMP_RES_TAC(DECIDE`(m<n)==>(m<=n)`)
          THEN PROVE_TAC[ReachIn_Stable],
         POP_ASSUM(STRIP_ASSUME_TAC o ONCE_REWRITE_RULE[ADD_SYM])
          THEN ASSUM_LIST
                (fn [th1,th2,th3,th4,th5] => ASSUME_TAC(REWRITE_RULE[th1]th3))
          THEN IMP_RES_TAC Stable_ADD],
      PROVE_TAC[],
      PROVE_TAC[]]);

(* Obsolete -- now EXISTS_IMP
val EXISTS_IMP_lemma = 
 store_thm
 ("EXISTS_IMP_lemma",
   ``((?x. P x) ==> Q) = (!x. P x ==> Q)``,
  PROVE_TAC[]);
*)

(*****************************************************************************)
(*     |- !P rep.                                                            *)
(*          TYPE_DEFINITION P rep ==>                                        *)
(*          (?abs. (!a. abs (rep a) = a) /\ (!r. P r = rep (abs r) = r))     *)
(*****************************************************************************)

val ABS_EXISTS_THM = (* Adapted from Hol sources *)
   let val th1 = ASSUME (--`?rep:'b->'a. TYPE_DEFINITION P rep`--)
       and th2 = MK_EXISTS (SPEC (--`P:'a->bool`--) TYPE_DEFINITION_THM)
       val def = EQ_MP th2 th1
       val asm = ASSUME (snd(dest_exists(concl def)))
       val (asm1,asm2)  = CONJ_PAIR asm
       val rep_eq =
         let val th1 = DISCH (--`a:'b=a'`--)
                         (AP_TERM (--`rep:'b->'a`--) (ASSUME (--`a:'b=a'`--)))
         in IMP_ANTISYM_RULE (SPECL [(--`a:'b`--),(--`a':'b`--)] asm1) th1
         end
       val ABS = (--`\r:'a. @a:'b. r = rep a`--)
       val absd =  RIGHT_BETA (AP_THM (REFL ABS) (--`rep (a:'b):'a`--))
       val lem = SYM(SELECT_RULE(EXISTS ((--`?a':'b.a=a'`--),(--`a:'b`--))
                                        (REFL (--`a:'b`--))))
       val TH1 = GEN (--`a:'b`--)
                     (TRANS(TRANS absd (SELECT_EQ (--`a':'b`--) rep_eq)) lem)
       val t1 = SELECT_RULE(EQ_MP (SPEC (--`r:'a`--) asm2)
                                  (ASSUME (--`(P:'a->bool) r`--)))
       val absd2 =  RIGHT_BETA (AP_THM (REFL ABS) (--`r:'a`--))
       val imp1 = DISCH (--`(P:'a->bool) r`--) (SYM (SUBS [SYM absd2] t1))
       val t2 = EXISTS ((--`?a:'b. r:'a = rep a`--), (--`^ABS r`--))
                       (SYM(ASSUME (--`rep(^ABS (r:'a):'b) = r`--)))
       val imp2 = DISCH (--`rep(^ABS (r:'a):'b) = r`--)
                        (EQ_MP (SYM (SPEC (--`r:'a`--) asm2)) t2)
       val TH2 = GEN (--`r:'a`--) (IMP_ANTISYM_RULE imp1 imp2)
       val CTH = CONJ TH1 TH2
       val ath = subst [ABS |-> Term`abs:'a->'b`] (concl CTH)
       val eth1 = EXISTS ((--`?abs:'a->'b. ^ath`--), ABS) CTH
   in
    save_thm
     ("ABS_EXISTS_THM",
      REWRITE_RULE[GSYM TYPE_DEFINITION](GEN_ALL (DISCH_ALL eth1)))
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

val _ = export_theory();
