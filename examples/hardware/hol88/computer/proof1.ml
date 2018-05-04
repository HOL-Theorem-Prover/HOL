%  MICROCODED COMPUTER PROOF : HOL                                      %
%                                                                       %
%  'proof1.ml'                                                          %
%                                                                       %
%  Description                                                          % 
%                                                                       %
%     This theory results in several preliminary lemmas based on        %
%  simple observations about the microcode.                             %
%                                                                       %
%  Author:  Jeff Joyce                                                  %
%  Date:    August 4, 1985                                              %

new_theory `proof1`;;

new_parent `arith`;;
new_parent `microcode`;;
new_parent `computer_imp`;;

let CUT_PAD = axiom `values` `CUT_PAD`;;
let CUT_INC_PAD = axiom `values` `CUT_INC_PAD`;;

let word5_CASES = axiom `values` `word5_CASES`;;
let VAL_word2_CASES = theorem `values` `VAL_word2_CASES`;;
let VAL_word3_CASES = theorem `values` `VAL_word3_CASES`;;

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
 WORD_RULE (axiom `microcode` `MICROCODE25`);
 WORD_RULE (axiom `microcode` `MICROCODE26`);
 WORD_RULE (axiom `microcode` `MICROCODE27`);
 WORD_RULE (axiom `microcode` `MICROCODE28`);
 WORD_RULE (axiom `microcode` `MICROCODE29`);
 WORD_RULE (axiom `microcode` `MICROCODE30`);
 WORD_RULE (axiom `microcode` `MICROCODE31`)
];;

let COMPUTER_IMP_EXP_ASM = theorem `computer_imp` `COMPUTER_IMP_EXP_ASM`;;

letrec nth_CONJUNCT n thm =
 if n = 0 then thm else (nth_CONJUNCT (n - 1) (CONJUNCT2 thm));;

let COMPUTER_IMP_mpc   = CONJUNCT1 (nth_CONJUNCT 7 COMPUTER_IMP_EXP_ASM);;
let COMPUTER_IMP_ready = CONJUNCT1 (nth_CONJUNCT 8 COMPUTER_IMP_EXP_ASM);;
let COMPUTER_IMP_idle  = CONJUNCT2 (nth_CONJUNCT 8 COMPUTER_IMP_EXP_ASM);;

let lemma1 =
 GEN_ALL
  (DISCH_ALL
   (IMP_ANTISYM_RULE (ASSUME "t:bool ==> F") (SPEC_ALL FALSITY)));;

let rule_out_mpc_case_rule tm =
 let th1 = SPEC "t1:num" COMPUTER_IMP_ready in
 let th2 = SUBS [ASSUME "(mpc (t1:num)) = ^tm"] th1 in
 let th3 = SUBS microcode th2 in
 let th4 = EL_RULE (BITS_RULE th3) in
 let th5 = CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (SPEC_ALL EQ_CLAUSES))) in
 let th6 = REWRITE_RULE [th5] th4 in
 let th7 = SPEC "(ready (t1:num)):bool" F_IMP in
 let th8 = MP (MP th7 th6) (ASSUME "(ready (t1:num)):bool") in
 let th9 = DISCH "mpc (t1:num) = ^tm" th8 in
 MP (SPEC "mpc (t1:num) = ^tm" lemma1) th9;;

let ruled_out_mpc_cases =
[
 rule_out_mpc_case_rule "#00001";
 rule_out_mpc_case_rule "#00010";
 rule_out_mpc_case_rule "#00011";
 rule_out_mpc_case_rule "#00100";
 rule_out_mpc_case_rule "#00110";
 rule_out_mpc_case_rule "#00111";
 rule_out_mpc_case_rule "#01000";
 rule_out_mpc_case_rule "#01001";
 rule_out_mpc_case_rule "#01010";
 rule_out_mpc_case_rule "#01011";
 rule_out_mpc_case_rule "#01100";
 rule_out_mpc_case_rule "#01101";
 rule_out_mpc_case_rule "#01110";
 rule_out_mpc_case_rule "#01111";
 rule_out_mpc_case_rule "#10000";
 rule_out_mpc_case_rule "#10001";
 rule_out_mpc_case_rule "#10010";
 rule_out_mpc_case_rule "#10011";
 rule_out_mpc_case_rule "#10100";
 rule_out_mpc_case_rule "#10101";
 rule_out_mpc_case_rule "#10110";
 rule_out_mpc_case_rule "#10111";
 rule_out_mpc_case_rule "#11000";
 rule_out_mpc_case_rule "#11001";
 rule_out_mpc_case_rule "#11010";
 rule_out_mpc_case_rule "#11011";
 rule_out_mpc_case_rule "#11100";
 rule_out_mpc_case_rule "#11101";
 rule_out_mpc_case_rule "#11110";
 rule_out_mpc_case_rule "#11111";
];;

let th1 =
 SUBS
  ruled_out_mpc_cases
  (SPEC "(mpc (t1:num)):word5" word5_CASES);;

let th2 = REWRITE_RULE [] th1;;

let th3 = SPEC "t1:num" COMPUTER_IMP_idle;;
let th4 = SUBS [ASSUME "(mpc (t1:num)) = #00101"] th3;;
let th5 = SUBS microcode th4;;
let th6 = EL_RULE (BITS_RULE th5);;
let th7 = CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (SPEC_ALL EQ_CLAUSES)));;
let th8 = REWRITE_RULE [th7] th6;;
let th9 = SPEC "(idle (t1:num)):bool" F_IMP;;
let th10 = MP (MP th9 th8) (ASSUME "(idle (t1:num)):bool");;
let th11 = DISCH "mpc (t1:num) = #00101" th10;;
let th12 = MP (SPEC "mpc (t1:num) = #00101" lemma1) th11;;
let th13 = REWRITE_RULE [th12] th2;;

%   COMPUTER_IMP                                                        %
%    (mpc,mar,ir,arg,buf)                                               %
%    (memory,knob,button,switches,pc,acc,idle,ready),                   %
%   ready t1,                                                           %
%   idle t1                                                             %
%   |- (mpc t1 = #00000)                                                %

save_thm (`ready_idle_mpc`,th13);;

let th3 = SPEC "t1:num" COMPUTER_IMP_idle;;
let th4 = SUBS [ASSUME "(mpc (t1:num)) = #00000"] th3;;
let th5 = SUBS microcode th4;;
let th6 = EL_RULE (BITS_RULE th5);;
let th7 = CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (SPEC_ALL EQ_CLAUSES)));;
let th8 = REWRITE_RULE [th7] th6;;
let th9 = SPEC "(idle (t1:num)):bool" F_IMP;;
let th10 = MP (MP th9 (ASSUME "~(idle (t1:num)):bool")) th8;;
let th11 = DISCH "mpc (t1:num) = #00000" th10;;
let th12 = MP (SPEC "mpc (t1:num) = #00000" lemma1) th11;;
let th13 = REWRITE_RULE [th12] th2;;

%   COMPUTER_IMP                                                        %
%    (mpc,mar,ir,arg,buf)                                               %
%    (memory,knob,button,switches,pc,acc,idle,ready),                   %
%   ready t1,                                                           %
%   ~idle t1                                                            %
%   |- (mpc t1 = #00101)                                                %

save_thm (`ready_not_idle_mpc`,th13);;

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

letrec nth_disj n tm =
 if n = 0 then tm else nth_disj (n - 1) (snd (dest_disj tm));;

let derive_next_mpc tm =
 let assumption = ASSUME "mpc (t:num) = ^tm" in
 (DISCH (concl assumption)
   (reduce_rule [assumption] (SPEC "t:num" COMPUTER_IMP_mpc)));;

let next_mpc_0 = derive_next_mpc "#00000";;
let next_mpc_1 = derive_next_mpc "#00001";;
let next_mpc_2 = derive_next_mpc "#00010";;
let next_mpc_3 = derive_next_mpc "#00011";;
let next_mpc_4 = derive_next_mpc "#00100";;
let next_mpc_5 = derive_next_mpc "#00101";;
let next_mpc_6 = derive_next_mpc "#00110";;
let next_mpc_7 = derive_next_mpc "#00111";;
let next_mpc_8 = derive_next_mpc "#01000";;
let next_mpc_9 = derive_next_mpc "#01001";;
let next_mpc_10 = derive_next_mpc "#01010";;
let next_mpc_11 = derive_next_mpc "#01011";;
let next_mpc_12 = derive_next_mpc "#01100";;
let next_mpc_13 = derive_next_mpc "#01101";;
let next_mpc_14 = derive_next_mpc "#01110";;
let next_mpc_15 = derive_next_mpc "#01111";;
let next_mpc_16 = derive_next_mpc "#10000";;
let next_mpc_17 = derive_next_mpc "#10001";;
let next_mpc_18 = derive_next_mpc "#10010";;
let next_mpc_19 = derive_next_mpc "#10011";;
let next_mpc_20 = derive_next_mpc "#10100";;
let next_mpc_21 = derive_next_mpc "#10101";;
let next_mpc_22 = derive_next_mpc "#10110";;
let next_mpc_23 = derive_next_mpc "#10111";;
let next_mpc_24 = derive_next_mpc "#11000";;
let next_mpc_25 = derive_next_mpc "#11001";;
let next_mpc_26 = derive_next_mpc "#11010";;
let next_mpc_27 = derive_next_mpc "#11011";;
let next_mpc_28 = derive_next_mpc "#11100";;
let next_mpc_29 = derive_next_mpc "#11101";;
let next_mpc_30 = derive_next_mpc "#11110";;
let next_mpc_31 = derive_next_mpc "#11111";;

let lemma2 = REWRITE_RULE [ADD1] (SPEC "t:num" LESS_SUC_REFL);;

let th1 = ASSUME "mpc ((t:num) + 1) = #00000";;
let th2 = SUBS [th1] (SPEC "(t:num) + 1" COMPUTER_IMP_ready);;
let th3 = (EL_RULE o BITS_RULE) (SUBS microcode th2);;
let th4 = CONJUNCT1 (CONJUNCT2 (SPEC "(ready ((t:num) + 1)):bool" EQ_CLAUSES));;
let lemma3 = DISCH (concl th1) (SUBS [th4] th3);;

let th1 = ASSUME "mpc ((t:num) + 1) = #00101";;
let th2 = SUBS [th1] (SPEC "(t:num) + 1" COMPUTER_IMP_ready);;
let th3 = (EL_RULE o BITS_RULE) (SUBS microcode th2);;
let th4 = CONJUNCT1 (CONJUNCT2 (SPEC "(ready ((t:num) + 1)):bool" EQ_CLAUSES));;
let lemma4 = DISCH (concl th1) (SUBS [th4] th3);;

let base_case lemma thm =
 DISCH
  (fst (dest_imp (concl thm)))
  (EXISTS
   ("?t2:num. ((t:num) < t2) /\ (ready t2)","(t:num) + 1")
   (LIST_CONJ [lemma2;(UNDISCH (IMP_TRANS thm lemma))]));;

let final_mpc_2 = GEN "t:num" (base_case lemma3 next_mpc_2);;
let final_mpc_3 = GEN "t:num" (base_case lemma3 next_mpc_3);;
let final_mpc_7 = GEN "t:num" (base_case lemma3 next_mpc_7);;
let final_mpc_10 = GEN "t:num" (base_case lemma3 next_mpc_10);;
let final_mpc_11 = GEN "t:num" (base_case lemma4 next_mpc_11);;
let final_mpc_18 = GEN "t:num" (base_case lemma4 next_mpc_18);;
let final_mpc_26 = GEN "t:num" (base_case lemma3 next_mpc_26);;
let final_mpc_27 = GEN "t:num" (base_case lemma3 next_mpc_27);;
let final_mpc_28 = GEN "t:num" (base_case lemma3 next_mpc_28);;
let final_mpc_29 = GEN "t:num" (base_case lemma3 next_mpc_29);;
let final_mpc_30 = GEN "t:num" (base_case lemma3 next_mpc_30);;
let final_mpc_31 = GEN "t:num" (base_case lemma3 next_mpc_31);;

let th1 = SPECL ["t:num";"(t:num) + 1";"t2:num"] LESS_TRANS;;
let th2 = ASSUME "((t:num) + 1) < (t2:num)";;
let lemma5 = DISCH_ALL (MP th1 (LIST_CONJ [lemma2;th2]));;

let iterate_case th1 th2 =
 let th1 = IMP_TRANS th2 (SPEC "(t:num) + 1" th1) in
 let th2 = ASSUME "((t:num) + 1) < (t2:num) /\ ready (t2:num)" in
 let th3 = LIST_CONJ [(MP lemma5 (CONJUNCT1 th2));(CONJUNCT2 th2)] in
 let th4 = EXISTS ("?t2:num. t < t2 /\ ready t2","t2") th3 in
 let th5 = CHOOSE ("t2:num",(UNDISCH th1)) th4 in
 DISCH (fst (dest_imp (concl th1))) th5;;

let final_mpc_4 = GEN "t:num" (iterate_case final_mpc_7 next_mpc_4);;
let final_mpc_17 = GEN "t:num" (iterate_case final_mpc_18 next_mpc_17);;

let final_mpc_1_knob_0 =
 iterate_case final_mpc_2
  (WORD_RULE
   (SUBS arith_lemmas
    (SUBS [ASSUME "VAL2(knob (t:num)) = 0"] next_mpc_1)));;

let final_mpc_1_knob_1 =
 iterate_case final_mpc_3
  (WORD_RULE
   (SUBS arith_lemmas
    (SUBS [ASSUME "VAL2(knob (t:num)) = 1"] next_mpc_1)));;

let final_mpc_1_knob_2 =
 iterate_case final_mpc_4
  (WORD_RULE
   (SUBS arith_lemmas
    (SUBS [ASSUME "VAL2(knob (t:num)) = 2"] next_mpc_1)));;

let final_mpc_1_knob_3 =
 base_case lemma4
  (WORD_RULE
   (SUBS arith_lemmas
    (SUBS [ASSUME "VAL2(knob (t:num)) = 3"] next_mpc_1)));;

let lemma6 = SPEC "(knob (t:num)):word2" VAL_word2_CASES;;

let final_mpc_1_knob_2_3 =
 DISJ_CASES (ASSUME (nth_disj 2 (concl lemma6)))
 final_mpc_1_knob_2 final_mpc_1_knob_3;;

let final_mpc_1_knob_1_2_3 =
 DISJ_CASES (ASSUME (nth_disj 1 (concl lemma6)))
 final_mpc_1_knob_1 final_mpc_1_knob_2_3;;

let final_mpc_1 =
 GEN "t:num"
  (DISJ_CASES lemma6
   final_mpc_1_knob_0 final_mpc_1_knob_1_2_3);;

let final_mpc_12_zero =
 iterate_case
  final_mpc_11
  (REWRITE_RULE [ASSUME "(VAL16(acc (t:num)) = 0) = T"] next_mpc_12);;

let final_mpc_12_nonzero =
 iterate_case
  final_mpc_17
  (REWRITE_RULE [ASSUME "(VAL16(acc (t:num)) = 0) = F"] next_mpc_12);;

let final_mpc_12 =
 GEN "t:num"
  (DISJ_CASES
   (SPEC "VAL16(acc (t:num)) = 0" BOOL_CASES_AX)
   final_mpc_12_zero final_mpc_12_nonzero);;

let final_mpc_0_button_T =
 iterate_case final_mpc_1
  (REWRITE_RULE [ASSUME "button (t:num) = T"] next_mpc_0);;

let final_mpc_0_button_F =
 base_case lemma3
  (REWRITE_RULE [ASSUME "button (t:num) = F"] next_mpc_0);;

let final_mpc_0 =
 GEN "t:num"
  (DISJ_CASES (SPEC "(button (t:num)):bool" BOOL_CASES_AX)
  final_mpc_0_button_T final_mpc_0_button_F);;

let final_mpc_21 = GEN "t:num" (iterate_case final_mpc_17 next_mpc_21);;
let final_mpc_24 = GEN "t:num" (iterate_case final_mpc_17 next_mpc_24);;
let final_mpc_25 = GEN "t:num" (iterate_case final_mpc_17 next_mpc_25);;
let final_mpc_15 = GEN "t:num" (iterate_case final_mpc_24 next_mpc_15);;
let final_mpc_16 = GEN "t:num" (iterate_case final_mpc_25 next_mpc_16);;
let final_mpc_20 = GEN "t:num" (iterate_case final_mpc_21 next_mpc_20);;
let final_mpc_23 = GEN "t:num" (iterate_case final_mpc_21 next_mpc_23);;
let final_mpc_19 = GEN "t:num" (iterate_case final_mpc_20 next_mpc_19);;
let final_mpc_22 = GEN "t:num" (iterate_case final_mpc_23 next_mpc_22);;
let final_mpc_13 = GEN "t:num" (iterate_case final_mpc_19 next_mpc_13);;
let final_mpc_14 = GEN "t:num" (iterate_case final_mpc_22 next_mpc_14);;

let final_mpc_9_opcode_0 =
 iterate_case
  final_mpc_10
  (WORD_RULE
   (SUBS arith_lemmas
    (SUBS [ASSUME "VAL3(OPCODE(ir t)) = 0"] next_mpc_9)));;

let final_mpc_9_opcode_1 =
 iterate_case
  final_mpc_11
  (WORD_RULE
   (SUBS arith_lemmas
    (SUBS [ASSUME "VAL3(OPCODE(ir t)) = 1"] next_mpc_9)));;

let final_mpc_9_opcode_2 =
 iterate_case
  final_mpc_12
  (WORD_RULE
   (SUBS arith_lemmas
    (SUBS [ASSUME "VAL3(OPCODE(ir t)) = 2"] next_mpc_9)));;

let final_mpc_9_opcode_3 =
 iterate_case
  final_mpc_13
  (WORD_RULE
   (SUBS arith_lemmas
    (SUBS [ASSUME "VAL3(OPCODE(ir t)) = 3"] next_mpc_9)));;

let final_mpc_9_opcode_4 =
 iterate_case
  final_mpc_14
  (WORD_RULE
   (SUBS arith_lemmas
    (SUBS [ASSUME "VAL3(OPCODE(ir t)) = 4"] next_mpc_9)));;

let final_mpc_9_opcode_5 =
 iterate_case
  final_mpc_15
  (WORD_RULE
   (SUBS arith_lemmas
    (SUBS [ASSUME "VAL3(OPCODE(ir t)) = 5"] next_mpc_9)));;

let final_mpc_9_opcode_6 =
 iterate_case
  final_mpc_16
  (WORD_RULE
   (SUBS arith_lemmas
    (SUBS [ASSUME "VAL3(OPCODE(ir t)) = 6"] next_mpc_9)));;

let final_mpc_9_opcode_7 =
 iterate_case
  final_mpc_17
  (WORD_RULE
   (SUBS arith_lemmas
    (SUBS [ASSUME "VAL3(OPCODE(ir t)) = 7"] next_mpc_9)));;

let lemma7 = SPEC "OPCODE(ir t)" VAL_word3_CASES;;

let final_mpc_9_opcode_6_7 =
 DISJ_CASES (ASSUME (nth_disj 6 (concl lemma7)))
 final_mpc_9_opcode_6 final_mpc_9_opcode_7;;

let final_mpc_9_opcode_5_6_7 =
 DISJ_CASES (ASSUME (nth_disj 5 (concl lemma7)))
 final_mpc_9_opcode_5 final_mpc_9_opcode_6_7;;

let final_mpc_9_opcode_4_5_6_7 =
 DISJ_CASES (ASSUME (nth_disj 4 (concl lemma7)))
 final_mpc_9_opcode_4 final_mpc_9_opcode_5_6_7;;

let final_mpc_9_opcode_3_4_5_6_7 =
 DISJ_CASES (ASSUME (nth_disj 3 (concl lemma7)))
 final_mpc_9_opcode_3 final_mpc_9_opcode_4_5_6_7;;

let final_mpc_9_opcode_2_3_4_5_6_7 =
 DISJ_CASES (ASSUME (nth_disj 2 (concl lemma7)))
 final_mpc_9_opcode_2 final_mpc_9_opcode_3_4_5_6_7;;

let final_mpc_9_opcode_1_2_3_4_5_6_7 =
 DISJ_CASES (ASSUME (nth_disj 1 (concl lemma7)))
 final_mpc_9_opcode_1 final_mpc_9_opcode_2_3_4_5_6_7;;

let final_mpc_9 =
 GEN "t:num"
  (DISJ_CASES lemma7
   final_mpc_9_opcode_0 final_mpc_9_opcode_1_2_3_4_5_6_7);;

let final_mpc_8 = GEN "t:num" (iterate_case final_mpc_9 next_mpc_8);;
let final_mpc_6 = GEN "t:num" (iterate_case final_mpc_8 next_mpc_6);;

let final_mpc_5_button_T =
 base_case lemma3
  (REWRITE_RULE [ASSUME "button (t:num) = T"] next_mpc_5);;

let final_mpc_5_button_F =
 iterate_case final_mpc_6
  (REWRITE_RULE [ASSUME "button (t:num) = F"] next_mpc_5);;

let final_mpc_5 =
 GEN "t:num"
  (DISJ_CASES (SPEC "(button (t:num)):bool" BOOL_CASES_AX)
  final_mpc_5_button_T final_mpc_5_button_F);;

let lemma8 = SPEC "(mpc t):word5" word5_CASES;;

letrec nth_item n l = if n = 1 then (hd l) else (nth_item (n - 1) (tl l));;

letrec iterate_DISJ_CASES n lemma thm th_list =
 if n = 1 then (DISJ_CASES lemma (nth_item 1 th_list) thm)
 else
  (iterate_DISJ_CASES
   (n - 1)
   lemma
   (DISJ_CASES (ASSUME (nth_disj (n-1) (concl lemma)))
    (nth_item n th_list) thm)
   th_list);;

let CHAIN_DISJ_CASES lemma th_list =
 let n = length th_list in
 iterate_DISJ_CASES (n - 1) lemma (nth_item n th_list) th_list;;

let th_list =
 map
  (\th.(UNDISCH (SPEC "t:num" th)))
  [
    final_mpc_0;
    final_mpc_1;
    final_mpc_2;
    final_mpc_3;
    final_mpc_4;
    final_mpc_5;
    final_mpc_6;
    final_mpc_7;
    final_mpc_8;
    final_mpc_9;
    final_mpc_10;
    final_mpc_11;
    final_mpc_12;
    final_mpc_13;
    final_mpc_14;
    final_mpc_15;
    final_mpc_16;
    final_mpc_17;
    final_mpc_18;
    final_mpc_19;
    final_mpc_20;
    final_mpc_21;
    final_mpc_22;
    final_mpc_23;
    final_mpc_24;
    final_mpc_25;
    final_mpc_26;
    final_mpc_27;
    final_mpc_28;
    final_mpc_29;
    final_mpc_30;
    final_mpc_31
 ];;

let th1 = CHAIN_DISJ_CASES lemma8 th_list;;
let th2 = GEN "t1:num" (SPEC "t1:num" (GEN "t:num" th1));;

%  COMPUTER_IMP                                                         %
%   (mpc,mar,ir,arg,buf)                                                %
%   (memory,knob,button,switches,pc,acc,idle,ready)                     %
%  |- (!t1. ?t2. t1 < t2 /\ ready t2)                                   %

save_thm (`infinitely_ready`,(UNDISCH_ALL (DISCH_ALL th2)));;

close_theory ();;
