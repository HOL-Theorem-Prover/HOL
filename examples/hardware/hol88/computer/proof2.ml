%  MICROCODED COMPUTER PROOF : HOL                                      %
%                                                                       %
%  'proof2.ml'                                                          %
%                                                                       %
%  Description                                                          % 
%                                                                       %
%     This theory results in a theorem about each of the fifteen        %
%  possible execution cycles.  There are five possible cycles for       %
%  the idling case, four when the button is pressed depending on the    %
%  value of knob, and one possible cycle when the button is not         %
%  pressed.  The remaining ten possible execution cycles are cases      %
%  of when the computer is running.  There is one possible execution    %
%  cycle for each of the eight opcode except for the conditional jump   %
%  for which there are two possible execution cycles depending on       %
%  whether the accumulator is zero or non-zero.  Finally, there is      %
%  is the execution cycle which results when the machine is running     %
%  and the button is pressed.  The idling case is mpc t1 = #00000"      %
%  and the running case is "mpc t1 = #00101".                           %
%     The theorems are derived for each case by simulating the exec-    %
%  ution cycle.  Instead of data, the 'values' are assertions about     %
%  data in terms of the state at the start of the execution cycle.      %
%     This is the major step in the proof.  The rest of the proof is    %
%  mostly 'stitching' together results of this step.                    %
%                                                                       %
%  Author:  Jeff Joyce                                                  %
%  Date:    August 4, 1985                                              %

new_theory `proof2`;;

new_parent `proof1`;;

let CUT_PAD = axiom `values` `CUT_PAD`;;
let CUT_INC_PAD = axiom `values` `CUT_INC_PAD`;;

let arith_lemmas =
 [
  (theorem `arith` `plus_0_2`);
  (theorem `arith` `plus_1_2`);
  (theorem `arith` `plus_2_2`);
  (theorem `arith` `plus_3_2`);
  (theorem `arith` `plus_0_10`);
  (theorem `arith` `plus_1_10`);
  (theorem `arith` `plus_2_10`);
  (theorem `arith` `plus_3_10`);
  (theorem `arith` `plus_4_10`);
  (theorem `arith` `plus_5_10`);
  (theorem `arith` `plus_6_10`);
  (theorem `arith` `plus_7_10`)
 ];;

let microcode =
[
 WORD_RULE (axiom `microcode` `MICROCODE0`);
 WORD_RULE (axiom `microcode` `MICROCODE1`);
 WORD_RULE (axiom `microcode` `MICROCODE2`);
 WORD_RULE (axiom `microcode` `MICROCODE3`);
 WORD_RULE (axiom `microcode` `MICROCODE4`);
 WORD_RULE (axiom `microcode` `MICROCODE5`);
 WORD_RULE (axiom `microcode` `MICROCODE6`);
 WORD_RULE (axiom `microcode` `MICROCODE7`);
 WORD_RULE (axiom `microcode` `MICROCODE8`);
 WORD_RULE (axiom `microcode` `MICROCODE9`);
 WORD_RULE (axiom `microcode` `MICROCODE10`);
 WORD_RULE (axiom `microcode` `MICROCODE11`);
 WORD_RULE (axiom `microcode` `MICROCODE12`);
 WORD_RULE (axiom `microcode` `MICROCODE13`);
 WORD_RULE (axiom `microcode` `MICROCODE14`);
 WORD_RULE (axiom `microcode` `MICROCODE15`);
 WORD_RULE (axiom `microcode` `MICROCODE16`);
 WORD_RULE (axiom `microcode` `MICROCODE17`);
 WORD_RULE (axiom `microcode` `MICROCODE18`);
 WORD_RULE (axiom `microcode` `MICROCODE19`);
 WORD_RULE (axiom `microcode` `MICROCODE20`);
 WORD_RULE (axiom `microcode` `MICROCODE21`);
 WORD_RULE (axiom `microcode` `MICROCODE22`);
 WORD_RULE (axiom `microcode` `MICROCODE23`);
 WORD_RULE (axiom `microcode` `MICROCODE24`);
 WORD_RULE (axiom `microcode` `MICROCODE25`)
];;

let COMPUTER_IMP_EXP_ASM = theorem `computer_imp` `COMPUTER_IMP_EXP_ASM`;;

letrec nth_CONJUNCT n thm =
 if n = 0 then thm else (nth_CONJUNCT (n - 1) (CONJUNCT2 thm));;

let COMPUTER_IMP_buf   = CONJUNCT1 (nth_CONJUNCT 0 COMPUTER_IMP_EXP_ASM);;
let COMPUTER_IMP_m     = CONJUNCT1 (nth_CONJUNCT 1 COMPUTER_IMP_EXP_ASM);;
let COMPUTER_IMP_mar   = CONJUNCT1 (nth_CONJUNCT 2 COMPUTER_IMP_EXP_ASM);;
let COMPUTER_IMP_pc    = CONJUNCT1 (nth_CONJUNCT 3 COMPUTER_IMP_EXP_ASM);;
let COMPUTER_IMP_acc   = CONJUNCT1 (nth_CONJUNCT 4 COMPUTER_IMP_EXP_ASM);;
let COMPUTER_IMP_ir    = CONJUNCT1 (nth_CONJUNCT 5 COMPUTER_IMP_EXP_ASM);;
let COMPUTER_IMP_arg   = CONJUNCT1 (nth_CONJUNCT 6 COMPUTER_IMP_EXP_ASM);;
let COMPUTER_IMP_mpc   = CONJUNCT1 (nth_CONJUNCT 7 COMPUTER_IMP_EXP_ASM);;
let COMPUTER_IMP_ready = CONJUNCT1 (nth_CONJUNCT 8 COMPUTER_IMP_EXP_ASM);;
let COMPUTER_IMP_idle  = CONJUNCT2 (nth_CONJUNCT 8 COMPUTER_IMP_EXP_ASM);;

letrec tm n = if n = 0 then "t1:num" else "(^(tm (n - 1))) + 1";;

let arith_rule thm = WORD_RULE (SUBS arith_lemmas thm);;

let evaluate_rule =
	BITS_RULE thenf
	EL_RULE   thenf
	COND_RULE thenf
	SEG_RULE  thenf
	V_RULE    thenf
	WORD_RULE thenf
	VAL_RULE  thenf
	EQ_RULE   thenf
	COND_RULE thenf
	U_RULE    thenf
	TRI_RULE  thenf
	bool_RULE thenf
	COND_RULE;;

let reduce_rule assumptions thm =
 REWRITE_RULE [CUT_PAD;CUT_INC_PAD]
  (arith_rule
   (SUBS assumptions
    (evaluate_rule
     (SUBS microcode
      (SUBS assumptions thm)))));;

let first_state assumptions =
 (
  (reduce_rule assumptions (SPEC "t1:num" COMPUTER_IMP_buf)),
  (reduce_rule assumptions (SPEC "t1:num" COMPUTER_IMP_m)),
  (reduce_rule assumptions (SPEC "t1:num" COMPUTER_IMP_mar)),
  (reduce_rule assumptions (SPEC "t1:num" COMPUTER_IMP_pc)),
  (reduce_rule assumptions (SPEC "t1:num" COMPUTER_IMP_acc)),
  (reduce_rule assumptions (SPEC "t1:num" COMPUTER_IMP_ir)),
  (reduce_rule assumptions (SPEC "t1:num" COMPUTER_IMP_arg)),
  (reduce_rule assumptions (SPEC "t1:num" COMPUTER_IMP_mpc)),
  (reduce_rule assumptions (SPEC "t1:num" COMPUTER_IMP_ready))
 );;

% The state at time t1 + i is obtained by specifying COMPUTER_IMP_buf,  %
% COMPUTER_IMP_m, ..., COMPUTER_IMP_ready for the term (tm (i - 1)) and %
% 'reducing' these assertions.  Reduction involves substitution with    %
% assertions about the state at time t1 + (i - 1) as well as substi-    %
% tution with the microcode and assumptions for the the particular      %
% case followed by an evaluation.  The evalution uses BITS_RULE,        %
% EL_RULE, WORD_RULE, etc. (see 'evaluate_rule').                       %

letrec iterate_state
 i n assumptions (buf,m,mar,pc,acc,ir,arg,mpc,ready) =
 if i > n
  then (buf,m,mar,pc,acc,ir,arg,mpc,ready)
  else
   let update_rule thm =
    (reduce_rule
     ([buf;m;mar;pc;acc;ir;arg;mpc] @ assumptions)
     (SPEC (tm (i - 1)) thm)
    ) in
    iterate_state
     (i + 1)
     n
     assumptions
     (
      (update_rule COMPUTER_IMP_buf),
      (update_rule COMPUTER_IMP_m),
      (update_rule COMPUTER_IMP_mar),
      (update_rule COMPUTER_IMP_pc),
      (update_rule COMPUTER_IMP_acc),
      (update_rule COMPUTER_IMP_ir),
      (update_rule COMPUTER_IMP_arg),
      (update_rule COMPUTER_IMP_mpc),
      (LIST_CONJ [(update_rule COMPUTER_IMP_ready);ready])
     );;

let simulate ncycles assumptions =
 let (buf,m,mar,pc,acc,ir,arg,mpc,readylist) =
  iterate_state 2 ncycles assumptions (first_state assumptions) in
 let idle = reduce_rule [mpc] (SPEC (tm ncycles) COMPUTER_IMP_idle) in
 let ready = reduce_rule [mpc] (SPEC (tm ncycles) COMPUTER_IMP_ready) in
 LIST_CONJ [m;pc;acc;idle;ready;readylist];;

% ===================================================================== %
% Case: mpc = 0, button = T, knob = 0 ================================= %

let assumptions = 
[
 ASSUME "(mpc (t1:num)) = #00000";
 ASSUME "(button (t1:num)) = T";
 ASSUME "(VAL2 (knob ((t1:num) + 1))) = 0"
];;

let COMPUTER_IMP_mpc_0_button_T_knob_0 =
 save_thm (`COMPUTER_IMP_mpc_0_button_T_knob_0`,(simulate 3 assumptions));;

% ===================================================================== %
% Case: mpc = 0, button = T, knob = 1 ================================= %

let assumptions = 
[
 ASSUME "(mpc (t1:num)) = #00000";
 ASSUME "(button (t1:num)) = T";
 ASSUME "(VAL2 (knob ((t1:num) + 1))) = 1"
];;

let COMPUTER_IMP_mpc_0_button_T_knob_1 =
 save_thm (`COMPUTER_IMP_mpc_0_button_T_knob_1`,(simulate 3 assumptions));;

% ===================================================================== %
% Case: mpc = 0, button = T, knob = 2 ================================= %

let assumptions = 
[
 ASSUME "(mpc (t1:num)) = #00000";
 ASSUME "(button (t1:num)) = T";
 ASSUME "(VAL2 (knob ((t1:num) + 1))) = 2"
];;

let COMPUTER_IMP_mpc_0_button_T_knob_2 =
 save_thm (`COMPUTER_IMP_mpc_0_button_T_knob_2`,(simulate 4 assumptions));;

% ===================================================================== %
% Case: mpc = 0, button = T, knob = 3 ================================= %

let assumptions = 
[
 ASSUME "(mpc (t1:num)) = #00000";
 ASSUME "(button (t1:num)) = T";
 ASSUME "(VAL2 (knob ((t1:num) + 1))) = 3"
];;

let COMPUTER_IMP_mpc_0_button_T_knob_3 =
 save_thm (`COMPUTER_IMP_mpc_0_button_T_knob_3`,(simulate 2 assumptions));;

% ===================================================================== %
% Case: mpc = 0, button = F =========================================== %

let assumptions = 
[
 ASSUME "(mpc (t1:num)) = #00000";
 ASSUME "(button (t1:num)) = F";
];;

let COMPUTER_IMP_mpc_0_button_F =
 save_thm (`COMPUTER_IMP_mpc_0_button_F`,(simulate 1 assumptions));;

% ===================================================================== %
% Case: mpc = 5, button = T =========================================== %

let assumptions = 
[
 ASSUME "(mpc (t1:num)) = #00101";
 ASSUME "(button (t1:num)) = T";
];;

let COMPUTER_IMP_mpc_5_button_T =
 save_thm (`COMPUTER_IMP_mpc_5_button_T`,(simulate 1 assumptions));;

% ===================================================================== %
% Case: mpc = 5, button = F, opcode is 0 (HALT) ======================= %

let assumptions = 
[
 ASSUME "(mpc (t1:num)) = #00101";
 ASSUME "(button (t1:num)) = F";
 ASSUME "(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num))))) = 0"
];;

let COMPUTER_IMP_mpc_5_button_F_opcode_0 =
 save_thm (`COMPUTER_IMP_mpc_5_button_F_opcode_0`,(simulate 5 assumptions));;

% ===================================================================== %
% Case: mpc = 5, button = F, opcode is 1 (JMP) ======================== %

let assumptions = 
[
 ASSUME "(mpc (t1:num)) = #00101";
 ASSUME "(button (t1:num)) = F";
 ASSUME "(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num))))) = 1"
];;

let COMPUTER_IMP_mpc_5_button_F_opcode_1 =
 save_thm (`COMPUTER_IMP_mpc_5_button_F_opcode_1`,(simulate 5 assumptions));;

% ===================================================================== %
% Case: mpc = 5, button = F, zero, opcode is 2 (JZR) ================== %

let assumptions = 
[
 ASSUME "(mpc (t1:num)) = #00101";
 ASSUME "(button (t1:num)) = F";
 ASSUME "((VAL16(acc (t1:num))) = 0) = T";
 ASSUME "(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num))))) = 2"
];;

let COMPUTER_IMP_mpc_5_button_F_zero_opcode_2 =
 save_thm (`COMPUTER_IMP_mpc_5_button_F_zero_opcode_2`,(simulate 6 assumptions));;

% ===================================================================== %
% Case: mpc = 5, button = F, nonzero, opcode is 2 (JZR) =============== %

let assumptions = 
[
 ASSUME "(mpc (t1:num)) = #00101";
 ASSUME "(button (t1:num)) = F";
 ASSUME "((VAL16(acc (t1:num))) = 0) = F";
 ASSUME "(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num))))) = 2"
];;

let COMPUTER_IMP_mpc_5_button_F_nonzero_opcode_2 =
 save_thm (`COMPUTER_IMP_mpc_5_button_F_nonzero_opcode_2`,(simulate 7 assumptions));;

% ===================================================================== %
% Case: mpc = 5, button = F, opcode is 3 (ADD) ======================== %

let assumptions = 
[
 ASSUME "(mpc (t1:num)) = #00101";
 ASSUME "(button (t1:num)) = F";
 ASSUME "(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num))))) = 3"
];;

let COMPUTER_IMP_mpc_5_button_F_opcode_3 =
 save_thm (`COMPUTER_IMP_mpc_5_button_F_opcode_3`,(simulate 10 assumptions));;

% ===================================================================== %
% Case: mpc = 5, button = F, opcode is 4 (SUB) ======================== %

let assumptions = 
[
 ASSUME "(mpc (t1:num)) = #00101";
 ASSUME "(button (t1:num)) = F";
 ASSUME "(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num))))) = 4"
];;

let COMPUTER_IMP_mpc_5_button_F_opcode_4 =
 save_thm (`COMPUTER_IMP_mpc_5_button_F_opcode_4`,(simulate 10 assumptions));;

% ===================================================================== %
% Case: mpc = 5, button = F, opcode is 5 (LD) ========================= %

let assumptions = 
[
 ASSUME "(mpc (t1:num)) = #00101";
 ASSUME "(button (t1:num)) = F";
 ASSUME "(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num))))) = 5"
];;

let COMPUTER_IMP_mpc_5_button_F_opcode_5 =
 save_thm (`COMPUTER_IMP_mpc_5_button_F_opcode_5`,(simulate 8 assumptions));;

% ===================================================================== %
% Case: mpc = 5, button = F, opcode is 6 (ST) ========================= %

let assumptions = 
[
 ASSUME "(mpc (t1:num)) = #00101";
 ASSUME "(button (t1:num)) = F";
 ASSUME "(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num))))) = 6"
];;

let COMPUTER_IMP_mpc_5_button_F_opcode_6 =
 save_thm (`COMPUTER_IMP_mpc_5_button_F_opcode_6`,(simulate 8 assumptions));;

% ===================================================================== %
% Case: mpc = 5, button = F, opcode is 7 (SKIP) ======================= %

let assumptions = 
[
 ASSUME "(mpc (t1:num)) = #00101";
 ASSUME "(button (t1:num)) = F";
 ASSUME "(VAL3(OPCODE(FETCH13(memory (t1:num))(pc (t1:num))))) = 7"
];;

let COMPUTER_IMP_mpc_5_button_F_opcode_7 =
 save_thm (`COMPUTER_IMP_mpc_5_button_F_opcode_7`,(simulate 6 assumptions));;

close_theory ();;
