%  MICROCODED COMPUTER PROOF : HOL                                      %
%                                                                       %
%  'proof6.ml'                                                          %
%                                                                       %
%  Description                                                          % 
%                                                                       %
%    This theory uses a statement of correctness expressed in terms     %
%  of the 'microcode time scale' to prove a statement of correctness    %
%  expressed in terms of the 'instruction set time scale'.  Further     %
%  detail may be found in "An Example of Temporal Abstraction in        %
%  Higher Order Logic" by Jeff Joyce.                                   %
%                                                                       %
%  Author:  Jeff Joyce                                                  %
%  Date:    August 4, 1985                                              %

new_theory `proof6`;;

new_parent `proof5`;;

let NEXT = definition `next` `NEXT`;;
let COMPUTER = definition `computer` `COMPUTER`;;
let COMPUTER_abs = definition `computer` `COMPUTER_abs`;;

let CORRECTNESS = theorem `proof5` `CORRECTNESS`;;
let infinitely_ready = theorem `proof1` `infinitely_ready`;;

%  LEAST is introduced as an axiom stating that whenever some number    %
%  has a property, there is a least number with that property.  LEAST   %
%  will eventually be proved as a theorem in HOL.                       %

let LEAST = new_axiom
(
 `LEAST`,
 "!P. (?t. P t) ==> (?t. P t /\ !t'. t' < t ==> ~(P t'))"
);;

%  'abs_zero' is a constant defining the zero case predicate in the     %
%  primitive recursive defintion of 'abs'.                              %

let abs_zero = new_definition
(
 `abs_zero`,
 "abs_zero  (sig:num->bool) =
  @t:num. (sig t) /\ (!t':num. (t' < t) ==> (~(sig t')))"
);;

%  'abs_non_zero' is a constant defining the non-zero case predicate    %
%  in the  primitive recursive definition of 'abs'.                     %

let abs_non_zero = new_definition
(
 `abs_non_zero`,
 "abs_non_zero (t'':num) (sig:num->bool) =
  @t:num.
   (sig t) /\
   (t'' < t) /\
   (!t':num. ((t'' < t') /\ (t' < t)) ==> (~(sig t')))"
);;

%  'abs' is a constant defining the predicate which describes the       %
%  relationship between a signal at the microcode level time scale      %
%  and another signal at the instruction set level time scale which     %
%  just samples the microcode level time scale signal when 'sig',       %
%  a boolean signal also at the microcode level time scale, is true.    %
%  'sig' will always be the signal 'ready'.  The definition of 'abs'    %
%  is the basis of the temporal abstraction.                            %

let abs = new_prim_rec_definition
(
 `abs`,
 "(abs 0 sig = abs_zero sig) /\
  (abs (SUC n) sig = abs_non_zero (abs (n:num) sig) sig)"
);;

let COMPUTER_IMP_hypth =
 "COMPUTER_IMP
   (mpc,mar,ir,arg,buf)
   (memory,knob,button,switches,pc,acc,idle,ready)";;

%  lemma1 = |- (n = 0) \/ 0 < n                                         %

let th1 = MP (SPECL ["0";"n:num"] LESS_SUC_IMP) (SPEC "n:num" LESS_0);;
let th2 = PURE_REWRITE_RULE [(CONJUNCT1 NOT_CLAUSES); IMP_DISJ_THM] th1;;
let th3 = DISJ1 (SYM (ASSUME "0 = (n:num)")) "0 < (n:num)";;
let th4 = DISJ2 "(n:num) = 0" (ASSUME "0 < (n:num)");;
let lemma1 = DISJ_CASES th2 th3 th4;;

%  lemma2 = . |- ready(@t. ready t /\ (!t'. t' < t ==> ~ready t'))      %
%                                                                       %
%  where the assumption is !t1. ?t2. t1 < t2 /\ ready t2                %

let th1 = MP (SPEC "ready:num->bool" LEAST) (ASSUME "?t:num. ready t");;
let th2 = ASSUME "(t1 < t) /\ (ready t)";;
let th3 = EXISTS ("?t:num. ready t","t:num") (CONJUNCT2 th2);;
let th4 = MP (DISCH_ALL th1) th3;;
let th5 = CHOOSE ("t:num",(SPEC "t1:num" infinitely_ready)) th4;;
let th6 = CONJUNCT1 (SELECT_RULE th5);;
let th7 = GEN_ALPHA_CONV "t:num" (snd (dest_comb (concl th6)));;
let lemma2 = SUBS [th7] th6;;

%  lemma3 = |- !b1 b2 b3. (b1 ==> ~(b2 /\ b3)) ==> b2 /\ b1 ==> ~b3     %

let th1 = ASSUME "(b1 ==> (~(b2 /\ b3)))";;
let th2 = MP th1 (CONJUNCT2 (ASSUME "b2 /\ b1"));;
let th3 = PURE_REWRITE_RULE [DE_MORGAN_THM] th2;;
let th4 = CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (SPEC "~b2" EQ_CLAUSES)));;
let th5 = snd (EQ_IMP_RULE (PURE_REWRITE_RULE [CONJUNCT1 NOT_CLAUSES] th4));;
let th6 = SUBS [MP th5 (CONJUNCT1 (ASSUME "b2 /\ b1"))] th3;;
let th7 = CONJUNCT1 (CONJUNCT2 (CONJUNCT2 (SPEC "~b3" OR_CLAUSES)));;
let lemma3 = GEN_ALL (DISCH_ALL (DISCH "b2 /\ b1" (SUBS [th7] th6)));;

%  lemma4 = . |- ?m. n = SUC m                                          %
%                                                                       %
%  where the assumption is 0 < n                                        %

let th1 = SPEC "t:num" num_CASES;;
let th2 = SUBS [GEN_ALPHA_CONV "m:num" (snd (dest_disj (concl th1)))] th1;;
let th3 = SUBS [GEN_ALPHA_CONV "n:num" (concl (GEN_ALL th2))] (GEN_ALL th2);;
let th4 = NOT_EQ_SYM (MP (SPECL ["0";"n"] LESS_NOT_EQ) (ASSUME "0 < n"));;
let th5 = SYM (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (SPEC "n = 0" EQ_CLAUSES))));;
let lemma4 = REWRITE_RULE [EQ_MP th5 th4] (SPEC_ALL th3);;

%  lemma5 =                                                             %
%  . |- ?t.                                                             %
%        ready t /\                                                     %
%        (abs m ready) < t /\                                           %
%        (!t'. (abs m ready) < t' /\ t' < t ==> ~ready t')              %
%                                                                       %
%  where the assumption is COMPUTER_IMP_hypth                           %
%                                                                       %
%  Note that lemma5 states an important result, that the abstraction    %
%  'abs' is well-defined.                                               %

let th1 = SPEC "(abs m ready):num" infinitely_ready;;
let th2 = SPEC (mk_abs ("t2:num",(snd (dest_exists (concl th1))))) LEAST;;
let th3 = CONV_RULE (DEPTH_CONV BETA_CONV) th2;;
let th4 = GEN_ALPHA_CONV "t:num" (concl th1);;
let th5 = MP th3 (SUBS [th4] th1);;
let th6 = ASSUME (snd (dest_exists (concl th5)));;
let th7 = SPECL ["t' < t";"(abs m ready) < t'";"(ready t'):bool"] lemma3;;
let th8 = GEN "t'" (MP th7 (SPEC_ALL (CONJUNCT2 th6)));;
let th9 = SPECL ["(abs m ready) < t";"(ready t):bool"] CONJ_SYM;;
let th10 = SUBS [th9] (CONJUNCT1 th6);;
let th11 = LIST_CONJ [(CONJUNCT1 th10);(CONJUNCT2 th10);th8];;
let th12 = EXISTS (mk_exists ("t",(concl th11)),"t") th11;;
let lemma5 = CHOOSE ("t",th5) th12;;

%  lemma6 =                                                             %
%  . |- ready                                                           %
%       (@t.                                                            %
%         ready t /\                                                    %
%         (abs m ready) < t /\                                          %
%         (!t'. (abs m ready) < t' /\ t' < t ==> ~ready t'))            %
%                                                                       %
%  where the assumption is COMPUTER_IMP_hypth                           %

let th1 = CONJUNCT1 (SELECT_RULE lemma5);;
let th2 = GEN_ALPHA_CONV "t:num" (snd (dest_comb (concl th1)));;
let lemma6 = SUBS [th2] th1;;

%  READY_ABS_THM is theorem stating that every point on the instruc-    %
%  tion set level time scale corresponds to a time on the microcode     %
%  level time scale when 'ready' is true.                               %

set_goal ([COMPUTER_IMP_hypth],"ready (abs (n:num) ready)");;

expand (DISJ_CASES_TAC lemma1);;
expand (ASM_REWRITE_TAC []);;
expand (PURE_REWRITE_TAC [(CONJUNCT1 abs);abs_zero]);;

expand (ACCEPT_TAC lemma2);;

expand (CHOOSE_TAC lemma4);;
expand (ASM_REWRITE_TAC []);;
expand (PURE_REWRITE_TAC [(CONJUNCT2 abs);abs_non_zero]);;
expand (ACCEPT_TAC lemma6);;

let READY_ABS_THM = save_top_thm `READY_ABS_THM`;;

%  lemma7 =                                                             %
%  . |- (abs m ready) <                                                 %
%       (@t.                                                            %
%         ready t /\                                                    %
%         (abs m ready) < t /\                                          %
%         (!t'. (abs m ready) < t' /\ t' < t ==> ~ready t'))            %
%                                                                       %
%  where the assumption is COMPUTER_IMP_hypth                           %

let th1 = CONJUNCT1 (CONJUNCT2 (SELECT_RULE lemma5));;
let th2 = GEN_ALPHA_CONV "t:num" (snd (dest_comb (concl th1)));;
let lemma7 = SUBS [th2] th1;;

%  lemma8 =                                                             %
%  . |- !t. (abs m ready) < t /\ t < (abs(SUC m)ready) ==> ~ready t     %
%                                                                       %
%  where the assumption is COMPUTER_IMP_hypth                           %

let th1 = CONJUNCT2 (CONJUNCT2 (SELECT_RULE lemma5));;
let tm =
 snd (dest_comb
  (snd (dest_conj
   (fst (dest_imp (snd (dest_forall (concl th1))))))));;
let th2 = GEN_ALPHA_CONV "t:num" tm;;
let th3 = SUBS [th2] th1;;
let th4 = PURE_REWRITE_RULE [(SYM (CONJUNCT2 abs));(SYM abs_non_zero)] th3;;
let th5 = GEN_ALPHA_CONV "t:num" (concl th4);;
let lemma8 = SUBS [th5] th4;;

%  NEXT_ABS_THM is a theorem stating that two successive points on the  %
%  instruction set level time scale correspond to two points on the     %
%  microcode level time scale which are not necessarily successive but  %
%  for which the relationship described by the constant 'NEXT' holds.   %

set_goal ([COMPUTER_IMP_hypth],"NEXT ((abs n ready),(abs (n + 1) ready)) ready");;

expand (PURE_REWRITE_TAC [NEXT]);;
expand (PURE_REWRITE_TAC [SYM (SPEC "n" ADD1)]);;

expand (CONJ_TAC);;
expand (PURE_REWRITE_TAC [(CONJUNCT2 abs);abs_non_zero]);;
expand (ACCEPT_TAC (SPEC "n" (GEN "m" lemma7)));;

expand (CONJ_TAC);;
expand (ACCEPT_TAC (SPEC "SUC n" (GEN "n" READY_ABS_THM)));;

expand (ACCEPT_TAC (SPEC "n" (GEN "m" lemma8)));;

let NEXT_ABS_THM = save_top_thm `NEXT_ABS_THM`;;

%  Using READY_ABS_THM and NEXT_ABS_THM along with CORRECTNESS, the     %
%  proven statement of correctness at the microcode level time scale,   %
%  prove the statement of correctness at the instruction set level      %
%  time scale.                                                          %
%                                                                       %
%  CORRECTNESS_abs =                                                    %
%  |- COMPUTER_IMP                                                      %
%      (mpc,mar,ir,arg,buf)                                             %
%      (memory,knob,button,switches,pc,acc,idle,ready) =                %
%     (!n. STABLE(abs n ready,abs(n + 1)ready)switches) /\              %
%     (!n. STABLE(abs n ready,abs(n + 1)ready)knob) /\                  %
%     (!n.                                                              %
%       (memory_abs n = memory(abs n ready)) /\                         %
%       (knob_abs n = knob(abs n ready)) /\                             %
%       (button_abs n = button(abs n ready)) /\                         %
%       (switches_abs n = switches(abs n ready)) /\                     %
%       (pc_abs n = pc(abs n ready)) /\                                 %
%       (acc_abs n = acc(abs n ready)) /\                               %
%       (idle_abs n = idle(abs n ready))) ==>                           %
%     COMPUTER_abs                                                      %
%      (memory_abs,                                                     %
%       knob_abs,button_abs,switches_abs,pc_abs,acc_abs,idle_abs)       %

let th1 =
 SPECL
  ["(abs n ready)";"(abs (n + 1) ready)"]
  (GENL ["t1:num";"t2:num"] CORRECTNESS);;

let th2 =
 ASSUME
  "COMPUTER_IMP
    (mpc,mar,ir,arg,buf)
    (memory,knob,button,switches,pc,acc,idle,ready) /\
   (!n. STABLE(abs n ready,abs(n + 1)ready) switches) /\
   (!n. STABLE(abs n ready,abs(n + 1)ready) knob) /\
   (!n:num.
    ((memory_abs (n:num)):mem13_16 = (memory (abs n ready)):mem13_16) /\
    ((knob_abs (n:num)):word2 = (knob (abs n ready)):word2) /\
    ((button_abs (n:num)):bool = (button (abs n ready)):bool) /\
    ((switches_abs (n:num)):word16 = (switches (abs n ready)):word16) /\
    ((pc_abs (n:num)):word13 = (pc (abs n ready)):word13) /\
    ((acc_abs (n:num)):word16 = (acc (abs n ready)):word16) /\
    ((idle_abs (n:num)):bool = (idle (abs n ready)):bool))";;

let th3 =
 LIST_CONJ
 [
  (CONJUNCT1 th2);
  (SPEC "n" (CONJUNCT1 (CONJUNCT2 th2)));
  (SPEC "n" (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 th2))));
  (MP (DISCH_ALL NEXT_ABS_THM) (CONJUNCT1 th2));
  (MP (DISCH_ALL READY_ABS_THM) (CONJUNCT1 th2))
 ];;

let th4 = MP th1 th3;;
let th5 = PURE_REWRITE_RULE [COMPUTER] th4;;

let th6 = CONJUNCT2 (CONJUNCT2 (CONJUNCT2 th2));;
let th8 = SUBS (map SYM (CONJ_LIST 7 (SPEC "n+1" th6))) th5;;
let th9 = SUBS (map SYM (CONJ_LIST 7 (SPEC "n:num" th6))) th8;;

let th10 = GEN "n" th9;;
let th11 = SUBS [GEN_ALPHA_CONV "t" (concl th10)] th10;;
let th12 = DISCH_ALL (EQ_MP (SYM COMPUTER_abs) th11);;

let CORRECTNESS_abs = save_thm (`CORRECTNESS_abs`,th12);;

close_theory ();;
