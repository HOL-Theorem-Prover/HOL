%  MICROCODED COMPUTER PROOF : HOL                                      %
%                                                                       %
%  'proof5.ml'                                                          %
%                                                                       %
%  Description                                                          % 
%                                                                       %
%     This theory results in the proof of correctness by performing     %
%  a case analysis for all possible execution paths.  Theorems for      %
%  each case are available in 'proof4'.  The actual statement of        %
%  correctness is shown below.                                          %
%                                                                       %
%  |- COMPUTER_IMP                                                      %
%      (mpc,mar,ir,arg,buf)                                             %
%      (memory,knob,button,switches,pc,acc,idle,ready) /\               %
%     STABLE (t1,t2) switches /\                                        %
%     STABLE (t1,t2) knob /\                                            %
%     NEXT(t1,t2) ready /\                                              %
%     ready t1                                                          %
%     ==>                                                               %
%     COMPUTER (t1,t2) (m,knob,button,switches,pc,acc,idle)             %
%                                                                       %
%  Author:  Jeff Joyce                                                  %
%  Date:    August 4, 1985                                              %

new_theory `proof5`;;

new_parent `proof4`;;
new_parent `computer`;;

let VAL_word2_CASES = theorem `values` `VAL_word2_CASES`;;
let VAL_word3_CASES = theorem `values` `VAL_word3_CASES`;;

let CASE_idle_button_T_knob_0 =
 theorem `proof4` `CASE_idle_button_T_knob_0`;;
let CASE_idle_button_T_knob_1 =
 theorem `proof4` `CASE_idle_button_T_knob_1`;;
let CASE_idle_button_T_knob_2 =
 theorem `proof4` `CASE_idle_button_T_knob_2`;;
let CASE_idle_button_T_knob_3 =
 theorem `proof4` `CASE_idle_button_T_knob_3`;;
let CASE_idle_button_F =
 theorem `proof4` `CASE_idle_button_F`;;
let CASE_run_button_T =
 theorem `proof4` `CASE_run_button_T`;;
let CASE_run_button_F_opcode_0 =
 theorem `proof4` `CASE_run_button_F_opcode_0`;;
let CASE_run_button_F_opcode_1 =
 theorem `proof4` `CASE_run_button_F_opcode_1`;;
let CASE_run_button_F_zero_opcode_2 =
 theorem `proof4` `CASE_run_button_F_zero_opcode_2`;;
let CASE_run_button_F_nonzero_opcode_2 =
 theorem `proof4` `CASE_run_button_F_nonzero_opcode_2`;;
let CASE_run_button_F_opcode_3 =
 theorem `proof4` `CASE_run_button_F_opcode_3`;;
let CASE_run_button_F_opcode_4 =
 theorem `proof4` `CASE_run_button_F_opcode_4`;;
let CASE_run_button_F_opcode_5 =
 theorem `proof4` `CASE_run_button_F_opcode_5`;;
let CASE_run_button_F_opcode_6 =
 theorem `proof4` `CASE_run_button_F_opcode_6`;;
let CASE_run_button_F_opcode_7 =
 theorem `proof4` `CASE_run_button_F_opcode_7`;;

let EXECUTE = definition `computer` `EXECUTE`;;

let COMPUTER = definition `computer` `COMPUTER`;;

letrec derive_less_than n m =
 if (n + 1) = m
  then
   (SUBS [SYM (num_CONV (int_to_term (n + 1)))]
    (SPEC (int_to_term n) LESS_SUC_REFL))
 else
  (SUBS [SYM (num_CONV (int_to_term m))]
   (MP
    (SPECL [(int_to_term n);(int_to_term (m - 1))] LESS_SUC)
    (derive_less_than n (m - 1))));;

let derive_not_equal n m =
 NOT_EQ_SYM
  (MP
   (SPECL [(int_to_term n);(int_to_term m)] LESS_NOT_EQ)
   (derive_less_than n m));;

letrec derive_all_not_equals i n =
 if (i < 0)
  then []
  else (derive_not_equal i n).(derive_all_not_equals (i - 1) n);;

let not_eqs n = derive_all_not_equals (n - 1) n;;

let button_CASES =
 let lemma = SPEC "(button (t1:num)):bool" EQ_CLAUSES in
 SUBS
  [
   (SYM (CONJUNCT1 (CONJUNCT2 lemma)));
   (SYM (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 lemma))))
  ]
  (SPEC "(button (t1:num)):bool" EXCLUDED_MIDDLE);;

let acc_zero_CASES =
 let lemma = SPEC "((VAL16(acc (t1:num))) = 0):bool" EQ_CLAUSES in
 SUBS
  [
   (SYM (CONJUNCT1 (CONJUNCT2 lemma)));
   (SYM (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 lemma))))
  ]
  (SPEC "((VAL16(acc (t1:num))) = 0):bool" EXCLUDED_MIDDLE);;

set_goal
(
 [],
 "COMPUTER_IMP
    (mpc,mar,ir,arg,buf)
    (memory,knob,button,switches,pc,acc,idle,ready) /\
  STABLE (t1,t2) switches /\
  STABLE (t1,t2) knob /\
  NEXT(t1,t2) ready /\
  ready t1
  ==>
  COMPUTER
   (t1:num,t2:num)
   (memory,knob,button,switches,pc,acc,idle)"
);;

expand (REPEAT STRIP_TAC);;

expand (PURE_REWRITE_TAC [COMPUTER;EXECUTE]);;

expand ((REWRITE_TAC [LET_DEF]) THEN (CONV_TAC (DEPTH_CONV BETA_CONV)));;

expand (ASM_CASES_TAC "(idle t1):bool");;

expand (DISJ_CASES_TAC button_CASES);;

expand (DISJ_CASES_TAC (SPEC "(knob (t1:num)):word2" VAL_word2_CASES));;

expand (ASM_REWRITE_TAC []);;

expandf (ACCEPT_TAC CASE_idle_button_T_knob_0);;

expand
 (DISJ_CASES_TAC
  (ASSUME
   "(VAL2(knob t1) = 1) \/ (VAL2(knob t1) = 2) \/ (VAL2(knob t1) = 3)"));;

expand (ASM_REWRITE_TAC (not_eqs 1));;

expandf (ACCEPT_TAC CASE_idle_button_T_knob_1);;

expand
 (DISJ_CASES_TAC
  (ASSUME
   "(VAL2(knob t1) = 2) \/ (VAL2(knob t1) = 3)"));;

expand (ASM_REWRITE_TAC (not_eqs 2));;

expandf (ACCEPT_TAC CASE_idle_button_T_knob_2);;

expand (ASM_REWRITE_TAC (not_eqs 3));;

expandf (ACCEPT_TAC CASE_idle_button_T_knob_3);;

expand (ASM_REWRITE_TAC []);;

expandf (ACCEPT_TAC CASE_idle_button_F);;

expand (DISJ_CASES_TAC button_CASES);;

expand (ASM_REWRITE_TAC []);;

expandf (ACCEPT_TAC CASE_run_button_T);;

expand (DISJ_CASES_TAC (SPEC "OPCODE(FETCH13(memory t1)(pc t1))" VAL_word3_CASES));;

expand (ASM_REWRITE_TAC []);;

expandf (ACCEPT_TAC CASE_run_button_F_opcode_0);;

expand
 (DISJ_CASES_TAC
  (ASSUME
"(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 1) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 2) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 3) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 4) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 5) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 6) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 7)"));;

expand (ASM_REWRITE_TAC (not_eqs 1));;

expandf (ACCEPT_TAC CASE_run_button_F_opcode_1);;

expand
 (DISJ_CASES_TAC
  (ASSUME
"(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 2) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 3) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 4) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 5) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 6) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 7)"));;

expand (DISJ_CASES_TAC acc_zero_CASES);;

expand (ASM_REWRITE_TAC (not_eqs 2));;

expandf (ACCEPT_TAC CASE_run_button_F_zero_opcode_2);;

expand (ASM_REWRITE_TAC (not_eqs 2));;

expandf (ACCEPT_TAC CASE_run_button_F_nonzero_opcode_2);;

expand
 (DISJ_CASES_TAC
  (ASSUME
"(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 3) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 4) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 5) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 6) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 7)"));;

expand (ASM_REWRITE_TAC (not_eqs 3));;

expandf (ACCEPT_TAC CASE_run_button_F_opcode_3);;

expand
 (DISJ_CASES_TAC
  (ASSUME
"(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 4) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 5) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 6) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 7)"));;

expand (ASM_REWRITE_TAC (not_eqs 4));;

expandf (ACCEPT_TAC CASE_run_button_F_opcode_4);;

expand
 (DISJ_CASES_TAC
  (ASSUME
"(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 5) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 6) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 7)"));;

expand (ASM_REWRITE_TAC (not_eqs 5));;

expandf (ACCEPT_TAC CASE_run_button_F_opcode_5);;

expand
 (DISJ_CASES_TAC
  (ASSUME
"(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 6) \/
(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num)))) = 7)"));;

expand (ASM_REWRITE_TAC (not_eqs 6));;

expandf (ACCEPT_TAC CASE_run_button_F_opcode_6);;

expand (ASM_REWRITE_TAC (not_eqs 7));;

expandf (ACCEPT_TAC CASE_run_button_F_opcode_7);;

save_top_thm `CORRECTNESS`;;

close_theory ();;
