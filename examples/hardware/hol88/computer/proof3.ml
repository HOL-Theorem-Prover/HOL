%  MICROCODED COMPUTER PROOF : HOL                                      %
%                                                                       %
%  'proof3.ml'                                                          %
%                                                                       %
%  Description                                                          % 
%                                                                       %
%     This theory identifies the term "((t1 + 1) ... + 1)" with t2      %
%  for each of the fifteen possible execution cycles from results in    %
%  'proof1', lemmas about the 'NEXT' relation, and the assumption       %
%  "NEXT (t1,t2) ready".  The theorems about each of the the execution  %
%  cycles derived in 'proof1' can be simplified with this identity.     %
%  The assumptions "STABLE (t1,t2) knob" and "STABLE (t1,t2) switches"  %
%  also allow "knob (t1 + 1)" and "switches ((t1 + 1) + 1)" to be       %
%  replaced by "knob t1" and "switches t1".  These identities result    %
%  in theorems which only have "t1" and "t2" as terms of time.  That    %
%  is, references to times in between 't1' and 't2' are eliminated.     %
%  The resulting theorems are further simplifed to an assertion about   %
%  the memory, program counter, accumulator, and idle status.  Other    %
%  results from 'proof1' (eg. the status of 'ready' and the other       %
%  registers) are not required beyond this step in the proof.           %
%                                                                       %
%  Author:  Jeff Joyce                                                  %
%  Date:    August 4, 1985                                              %

new_theory `proof3`;;

new_parent `next`;;
new_parent `proof2`;;

let NEXT_INC_LEMMA = theorem `next` `NEXT_INC_LEMMA`;;
let NEXT_IDENTITY_LEMMA = theorem `next` `NEXT_IDENTITY_LEMMA`;;
let NEXT_INC_INTERVAL_LEMMA = theorem `next` `NEXT_INC_INTERVAL_LEMMA`;;

let STABLE = definition `values` `STABLE`;;
let VAL_word2_CASES = theorem `values` `VAL_word2_CASES`;;

let COMPUTER_IMP_mpc_0_button_T_knob_0 =
 theorem `proof2` `COMPUTER_IMP_mpc_0_button_T_knob_0`;;
let COMPUTER_IMP_mpc_0_button_T_knob_1 =
 theorem `proof2` `COMPUTER_IMP_mpc_0_button_T_knob_1`;;
let COMPUTER_IMP_mpc_0_button_T_knob_2 =
 theorem `proof2` `COMPUTER_IMP_mpc_0_button_T_knob_2`;;
let COMPUTER_IMP_mpc_0_button_T_knob_3 =
 theorem `proof2` `COMPUTER_IMP_mpc_0_button_T_knob_3`;;
let COMPUTER_IMP_mpc_0_button_F =
 theorem `proof2` `COMPUTER_IMP_mpc_0_button_F`;;
let COMPUTER_IMP_mpc_5_button_T =
 theorem `proof2` `COMPUTER_IMP_mpc_5_button_T`;;
let COMPUTER_IMP_mpc_5_button_F_opcode_0 =
 theorem `proof2` `COMPUTER_IMP_mpc_5_button_F_opcode_0`;;
let COMPUTER_IMP_mpc_5_button_F_opcode_1 =
 theorem `proof2` `COMPUTER_IMP_mpc_5_button_F_opcode_1`;;
let COMPUTER_IMP_mpc_5_button_F_zero_opcode_2 =
 theorem `proof2` `COMPUTER_IMP_mpc_5_button_F_zero_opcode_2`;;
let COMPUTER_IMP_mpc_5_button_F_nonzero_opcode_2 =
 theorem `proof2` `COMPUTER_IMP_mpc_5_button_F_nonzero_opcode_2`;;
let COMPUTER_IMP_mpc_5_button_F_opcode_3 =
 theorem `proof2` `COMPUTER_IMP_mpc_5_button_F_opcode_3`;;
let COMPUTER_IMP_mpc_5_button_F_opcode_4 =
 theorem `proof2` `COMPUTER_IMP_mpc_5_button_F_opcode_4`;;
let COMPUTER_IMP_mpc_5_button_F_opcode_5 =
 theorem `proof2` `COMPUTER_IMP_mpc_5_button_F_opcode_5`;;
let COMPUTER_IMP_mpc_5_button_F_opcode_6 =
 theorem `proof2` `COMPUTER_IMP_mpc_5_button_F_opcode_6`;;d
let COMPUTER_IMP_mpc_5_button_F_opcode_7 =
 theorem `proof2` `COMPUTER_IMP_mpc_5_button_F_opcode_7`;;

letrec tm n = if n = 0 then "t1:num" else "(^(tm (n - 1))) + 1";;

letrec reduce_interval i n ready next =
 if i < 0 then next
 else reduce_interval (i - 1) n (CONJUNCT2 ready)
  (MP
   (SPECL [(tm i);(tm n)] (SPEC "ready:num->bool" NEXT_INC_INTERVAL_LEMMA))
   (LIST_CONJ [(CONJUNCT1 (CONJUNCT2 ready));next]));;

let identify_interval n thm =
 MP
  (SPECL [(tm 0);(tm n);"t2:num"] (SPEC "ready:num->bool" NEXT_IDENTITY_LEMMA))
  (LIST_CONJ
   [
    (reduce_interval (n - 2) n
     (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 thm))))
     (MP
      (SPEC (tm (n - 1))(SPEC "ready:num->bool"  NEXT_INC_LEMMA))
      (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 thm))))))
    );
    (ASSUME "NEXT (t1,t2) ready")
   ]);;

let between_0_1_2 =
 let th1 = (SUBS [SPEC (tm 0) ADD1] (SPEC (tm 0) LESS_SUC_REFL)) in
 let th2 = (SUBS [SPEC (tm 1) ADD1] (SPEC (tm 1) LESS_SUC_REFL)) in
 LIST_CONJ [th1;th2];;

let between_0_1_3 =
 let th1 = (SUBS [SPEC (tm 0) ADD1] (SPEC (tm 0) LESS_SUC_REFL)) in
 let th2 = (SUBS [SPEC (tm 1) ADD1] (SPEC (tm 1) LESS_SUC_REFL)) in
 let th3 = (MP (SPECL [(tm 1);(tm 2)] LESS_SUC) th2) in
 let th4 = (SUBS [SPEC (tm 2) ADD1] th3) in
 LIST_CONJ [th1;th4];;

let between_0_1_4 =
 let th1 = (SUBS [SPEC (tm 0) ADD1] (SPEC (tm 0) LESS_SUC_REFL)) in
 let th2 = (SUBS [SPEC (tm 1) ADD1] (SPEC (tm 1) LESS_SUC_REFL)) in
 let th3 = (MP (SPECL [(tm 1);(tm 2)] LESS_SUC) th2) in
 let th4 = (SUBS [SPEC (tm 2) ADD1] th3) in
 let th5 = (MP (SPECL [(tm 1);(tm 3)] LESS_SUC) th4) in
 let th6 = (SUBS [SPEC (tm 3) ADD1] th5) in
 LIST_CONJ [th1;th6];;

let between_mpc_0_button_T_knob_0 =
 SUBS [identify_interval 3 COMPUTER_IMP_mpc_0_button_T_knob_0] between_0_1_3;;
let between_mpc_0_button_T_knob_1 =
 SUBS [identify_interval 3 COMPUTER_IMP_mpc_0_button_T_knob_1] between_0_1_3;;
let between_mpc_0_button_T_knob_2 =
 SUBS [identify_interval 4 COMPUTER_IMP_mpc_0_button_T_knob_2] between_0_1_4;;
let between_mpc_0_button_T_knob_3 =
 SUBS [identify_interval 2 COMPUTER_IMP_mpc_0_button_T_knob_3] between_0_1_2;;

let th1 =
 DISJ_CASES
  (ASSUME "(VAL2(knob(t1 + 1)) = 2) \/ (VAL2(knob(t1 + 1)) = 3)")
  between_mpc_0_button_T_knob_2 between_mpc_0_button_T_knob_3;;

let th2 =
 DISJ_CASES
  (ASSUME
   "(VAL2(knob(t1 + 1)) = 1) \/
    (VAL2(knob(t1 + 1)) = 2) \/ (VAL2(knob(t1 + 1)) = 3)")
  between_mpc_0_button_T_knob_1 th1;;

let knob_interval =
 DISJ_CASES (SPEC "(knob ((t1:num) + 1)):word2" VAL_word2_CASES)
  between_mpc_0_button_T_knob_0 th2;;

let knob_constant_mpc_0_button_T =
 let th1 = (ASSUME "STABLE (t1,t2) (knob:num->word2)") in
 let th2 = (PURE_REWRITE_RULE [STABLE] th1) in
 let th3 = (SPEC (tm 1) th2) in
 MP th3 knob_interval;;

let between_0_2_3 =
 let th1 = (SUBS [SPEC (tm 0) ADD1] (SPEC (tm 0) LESS_SUC_REFL)) in
 let th2 = (MP (SPECL [(tm 0);(tm 1)] LESS_SUC) th1) in
 let th3 = (SUBS [SPEC (tm 1) ADD1] th2) in
 let th4 = (SUBS [SPEC (tm 2) ADD1] (SPEC (tm 2) LESS_SUC_REFL)) in
 LIST_CONJ [th3;th4];;

let switches_constant_rule identity =
 let th1 = (SUBS [identity] between_0_2_3) in
 let th2 = (ASSUME "STABLE (t1,t2) (switches:num->word16)") in
 let th3 = (PURE_REWRITE_RULE [STABLE] th2) in
 let th4 = (SPEC (tm 2) th3) in
 let th5 = (MP th4 th1) in
 UNDISCH_ALL (SUBS [knob_constant_mpc_0_button_T] (DISCH_ALL th5));;

let switches_constant_mpc_0_button_T_knob_0 =
 switches_constant_rule (identify_interval 3 COMPUTER_IMP_mpc_0_button_T_knob_0);;

let switches_constant_mpc_0_button_T_knob_1 =
 switches_constant_rule (identify_interval 3 COMPUTER_IMP_mpc_0_button_T_knob_1);;

let simplify n constant_signal_lemmas thm =
 UNDISCH_ALL
  (SUBS constant_signal_lemmas
   (DISCH_ALL
    (SUBS [identify_interval n thm]
     (LIST_CONJ
      [
       CONJUNCT1 thm;
       CONJUNCT1 (CONJUNCT2 thm);
       CONJUNCT1 (CONJUNCT2 (CONJUNCT2 thm));
       CONJUNCT1 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 thm)))
      ]))));;

% ===================================================================== %
% Case: mpc = 0, button = T, knob = 0 ================================= %

let constant_signal_lemmas =
 [knob_constant_mpc_0_button_T;switches_constant_mpc_0_button_T_knob_0];;

let SIMP_mpc_0_button_T_knob_0 =
 save_thm
 (
  `SIMP_mpc_0_button_T_knob_0`,
  (simplify 3 constant_signal_lemmas COMPUTER_IMP_mpc_0_button_T_knob_0)
 );;

% ===================================================================== %
% Case: mpc = 0, button = T, knob = 1 ================================= %

let constant_signal_lemmas =
 [knob_constant_mpc_0_button_T;switches_constant_mpc_0_button_T_knob_1];;

let SIMP_mpc_0_button_T_knob_1 =
 save_thm
 (
  `SIMP_mpc_0_button_T_knob_1`,
  (simplify 3 constant_signal_lemmas COMPUTER_IMP_mpc_0_button_T_knob_1)
 );;

% ===================================================================== %
% Case: mpc = 0, button = T, knob = 2 ================================= %

let constant_signal_lemmas = [knob_constant_mpc_0_button_T];;

let SIMP_mpc_0_button_T_knob_2 =
 save_thm
 (
  `SIMP_mpc_0_button_T_knob_2`,
  (simplify 4 constant_signal_lemmas COMPUTER_IMP_mpc_0_button_T_knob_2)
 );;

% ===================================================================== %
% Case: mpc = 0, button = T, knob = 3 ================================= %

let constant_signal_lemmas = [knob_constant_mpc_0_button_T];;

let SIMP_mpc_0_button_T_knob_3 =
 save_thm
 (
  `SIMP_mpc_0_button_T_knob_3`,
  (simplify 2 constant_signal_lemmas COMPUTER_IMP_mpc_0_button_T_knob_3)
 );;

% ===================================================================== %
% Case: mpc = 0, button = F =========================================== %

let SIMP_mpc_0_button_F =
 save_thm
 (
  `SIMP_mpc_0_button_F`,
  (simplify 1 [] COMPUTER_IMP_mpc_0_button_F)
 );;

% ===================================================================== %
% Case: mpc = 5, button = T =========================================== %

let SIMP_mpc_5_button_T =
 save_thm
 (
  `SIMP_mpc_5_button_T`,
  (simplify 1 [] COMPUTER_IMP_mpc_5_button_T)
 );;

% ===================================================================== %
% Case: mpc = 5, button = F, opcode is 0 (HALT) ======================= %

let SIMP_mpc_5_button_F_opcode_0 =
 save_thm
 (
  `SIMP_mpc_5_button_F_opcode_0`,
  (simplify 5 [] COMPUTER_IMP_mpc_5_button_F_opcode_0)
 );;

% ===================================================================== %
% Case: mpc = 5, button = F, opcode is 1 (JMP) ======================== %

let SIMP_mpc_5_button_F_opcode_1 =
 save_thm
 (
  `SIMP_mpc_5_button_F_opcode_1`,
  (simplify 5 [] COMPUTER_IMP_mpc_5_button_F_opcode_1)
 );;

% ===================================================================== %
% Case: mpc = 5, button = F, zero, opcode is 2 (JZR) ================== %

let SIMP_mpc_5_button_F_zero_opcode_2 =
 save_thm
 (
  `SIMP_mpc_5_button_F_zero_opcode_2`,
  (simplify 6 [] COMPUTER_IMP_mpc_5_button_F_zero_opcode_2)
 );;

% ===================================================================== %
% Case: mpc = 5, button = F, nonzero, opcode is 2 (JZR) =============== %

let SIMP_mpc_5_button_F_nonzero_opcode_2 =
 save_thm
 (
  `SIMP_mpc_5_button_F_nonzero_opcode_2`,
  (simplify 7 [] COMPUTER_IMP_mpc_5_button_F_nonzero_opcode_2)
 );;

% ===================================================================== %
% Case: mpc = 5, button = F, opcode is 3 (ADD) ======================== %

let SIMP_mpc_5_button_F_opcode_3 =
 save_thm
 (
  `SIMP_mpc_5_button_F_opcode_3`,
  (simplify 10 [] COMPUTER_IMP_mpc_5_button_F_opcode_3)
 );;

% ===================================================================== %
% Case: mpc = 5, button = F, opcode is 4 (SUB) ======================== %

let SIMP_mpc_5_button_F_opcode_4 =
 save_thm
 (
  `SIMP_mpc_5_button_F_opcode_4`,
  (simplify 10 [] COMPUTER_IMP_mpc_5_button_F_opcode_4)
 );;

% ===================================================================== %
% Case: mpc = 5, button = F, opcode is 5 (LD) ========================= %

let SIMP_mpc_5_button_F_opcode_5 =
 save_thm
 (
  `SIMP_mpc_5_button_F_opcode_5`,
  (simplify 8 [] COMPUTER_IMP_mpc_5_button_F_opcode_5)
 );;

% ===================================================================== %
% Case: mpc = 5, button = F, opcode is 6 (ST) ========================= %

let SIMP_mpc_5_button_F_opcode_6 =
 save_thm
 (
  `SIMP_mpc_5_button_F_opcode_6`,
  (simplify 8 [] COMPUTER_IMP_mpc_5_button_F_opcode_6)
 );;

% ===================================================================== %
% Case: mpc = 5, button = F, opcode is 7 (SKIP) ======================= %

let SIMP_mpc_5_button_F_opcode_7 =
 save_thm
 (
  `SIMP_mpc_5_button_F_opcode_7`,
  (simplify 6 [] COMPUTER_IMP_mpc_5_button_F_opcode_7)
 );;

close_theory ();;
