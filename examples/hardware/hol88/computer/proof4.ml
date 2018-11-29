%  MICROCODED COMPUTER PROOF : HOL                                      %
%                                                                       %
%  'proof4.ml'                                                          %
%                                                                       %
%  Description                                                          % 
%                                                                       %
%     This theory puts the results from 'proof3' into the final form    %
%  for the case analysis.  The theorems from 'proof3' are conjunctions  %
%  consisting of four conjuncts which state equivalences.  These are    %
%  are changed into theorems about the equivalence of four-tuples in    %
%  accordance with the target level specification.  Furthermore, the    %
%  assumption that "mpc t1 = #00000" is traded in for the assumptions   %
%  "ready t1" and "idle t1" using a lemma from 'proof1'.  Similarly,    %
%  "mpc t1 = #00101" is replaced by the assumptions "ready t1" and      %
%  "~idle t1".                                                          %
%                                                                       %
%  Author:  Jeff Joyce                                                  %
%  Date:    August 4, 1985                                              %

new_theory `proof4`;;

new_parent `proof3`;;

let ready_idle_mpc = theorem `proof1` `ready_idle_mpc`;;
let ready_not_idle_mpc = theorem `proof1` `ready_not_idle_mpc`;;

let SIMP_mpc_0_button_T_knob_0 =
 theorem `proof3` `SIMP_mpc_0_button_T_knob_0`;;
let SIMP_mpc_0_button_T_knob_1 =
 theorem `proof3` `SIMP_mpc_0_button_T_knob_1`;;
let SIMP_mpc_0_button_T_knob_2 =
 theorem `proof3` `SIMP_mpc_0_button_T_knob_2`;;
let SIMP_mpc_0_button_T_knob_3 =
 theorem `proof3` `SIMP_mpc_0_button_T_knob_3`;;
let SIMP_mpc_0_button_F =
 theorem `proof3` `SIMP_mpc_0_button_F`;;
let SIMP_mpc_5_button_T =
 theorem `proof3` `SIMP_mpc_5_button_T`;;
let SIMP_mpc_5_button_F_opcode_0 =
 theorem `proof3` `SIMP_mpc_5_button_F_opcode_0`;;
let SIMP_mpc_5_button_F_opcode_1 =
 theorem `proof3` `SIMP_mpc_5_button_F_opcode_1`;;
let SIMP_mpc_5_button_F_zero_opcode_2 =
 theorem `proof3` `SIMP_mpc_5_button_F_zero_opcode_2`;;
let SIMP_mpc_5_button_F_nonzero_opcode_2 =
 theorem `proof3` `SIMP_mpc_5_button_F_nonzero_opcode_2`;;
let SIMP_mpc_5_button_F_opcode_3 =
 theorem `proof3` `SIMP_mpc_5_button_F_opcode_3`;;
let SIMP_mpc_5_button_F_opcode_4 =
 theorem `proof3` `SIMP_mpc_5_button_F_opcode_4`;;
let SIMP_mpc_5_button_F_opcode_5 =
 theorem `proof3` `SIMP_mpc_5_button_F_opcode_5`;;
let SIMP_mpc_5_button_F_opcode_6 =
 theorem `proof3` `SIMP_mpc_5_button_F_opcode_6`;;d
let SIMP_mpc_5_button_F_opcode_7 =
 theorem `proof3` `SIMP_mpc_5_button_F_opcode_7`;;

let idle_T_lemma =
 SYM
  (CONJUNCT1 (CONJUNCT2 (SPEC "(idle (t2:num)):bool" EQ_CLAUSES)));;

let idle_F_lemma =
 SYM
  (CONJUNCT2
   (CONJUNCT2 (CONJUNCT2 (SPEC "(idle (t2:num)):bool" EQ_CLAUSES))));;

%     tuples_lemma =                                                    %
%     |- !a1 a2 b1 b2 c1 c2 d1 d2.                                      %
%     (a1 = a2) /\ (b1 = b2) /\ (c1 = c2) /\ (d1 = d2) ==>              %
%     (a1,b1,c1,d1 = a2,b2,c2,d2)                                       %

let tuples_lemma =
  (GEN_ALL
   (DISCH_ALL
    (SUBS_OCCS
     (map
      (\th.([2],th))
      (CONJUNCTS
       (ASSUME
        "(((a1:mem13_16) = (a2:mem13_16)) /\
          ((b1:word13) = (b2:word13)) /\
          ((c1:word16) = (c2:word16)) /\
          ((d1:bool) = (d2:bool)))")))
     (REFL "a1:mem13_16,b1:word13,c1:word16,d1:bool"))));;

let four_tuple thm =
 let th1 = (SUBS [idle_T_lemma;idle_F_lemma] thm) in
 let (m_lhs,m_rhs) =
  (dest_eq (fst (dest_conj (snd (dest_thm th1))))) in
 let (pc_lhs,pc_rhs) =
  (dest_eq (fst (dest_conj (snd (dest_conj (snd (dest_thm th1))))))) in
 let (acc_lhs,acc_rhs) =
  (dest_eq (fst (dest_conj
   (snd (dest_conj (snd (dest_conj (snd (dest_thm th1))))))))) in
 let (idle_lhs,idle_rhs) =
  (dest_eq (snd (dest_conj
   (snd (dest_conj (snd (dest_conj (snd (dest_thm th1))))))))) in
 let th2 =
  SPECL [m_lhs;m_rhs;pc_lhs;pc_rhs;acc_lhs;acc_rhs;idle_lhs;idle_rhs]
   tuples_lemma in
 (MP th2 th1);;

let introduce_idle_asm b thm =
 if b
  then (MP (DISCH "(mpc (t1:num)) = #00000" thm) ready_idle_mpc)
  else (MP (DISCH "(mpc (t1:num)) = #00101" thm) ready_not_idle_mpc);;

% ===================================================================== %
% Case: idle, button = T, knob is 0 =================================== %

let CASE_idle_button_T_knob_0 =
 save_thm
 (
  `CASE_idle_button_T_knob_0`,
  (introduce_idle_asm true (four_tuple SIMP_mpc_0_button_T_knob_0))
 );;

% ===================================================================== %
% Case: idle, button = T, knob is 1 =================================== %

let CASE_idle_button_T_knob_1 =
 save_thm
 (
  `CASE_idle_button_T_knob_1`,
  (introduce_idle_asm true (four_tuple SIMP_mpc_0_button_T_knob_1))
 );;

% ===================================================================== %
% Case: idle, button = T, knob is 2 =================================== %

let CASE_idle_button_T_knob_2 =
 save_thm
 (
  `CASE_idle_button_T_knob_2`,
  (introduce_idle_asm true (four_tuple SIMP_mpc_0_button_T_knob_2))
 );;

% ===================================================================== %
% Case: idle, button = T, knob is 3 =================================== %

let CASE_idle_button_T_knob_3 =
 save_thm
 (
  `CASE_idle_button_T_knob_3`,
  (introduce_idle_asm true (four_tuple SIMP_mpc_0_button_T_knob_3))
 );;

% ===================================================================== %
% Case: idle, button = F ============================================== %

let CASE_idle_button_F =
 save_thm
 (
  `CASE_idle_button_F`,
  (introduce_idle_asm true (four_tuple SIMP_mpc_0_button_F))
 );;

% ===================================================================== %
% Case: run, button = T =============================================== %

let CASE_run_button_T =
 save_thm
 (
  `CASE_run_button_T`,
  (introduce_idle_asm false (four_tuple SIMP_mpc_5_button_T))
 );;

% ===================================================================== %
% Case: run, button = F, opcode is 0 (HALT) =========================== %

let CASE_run_button_F_opcode_0 =
 save_thm
 (
  `CASE_run_button_F_opcode_0`,
  (introduce_idle_asm false (four_tuple SIMP_mpc_5_button_F_opcode_0))
 );;

% ===================================================================== %
% Case: run, button = F, opcode is 1 (JMP) ============================ %

let CASE_run_button_F_opcode_1 =
 save_thm
 (
  `CASE_run_button_F_opcode_1`,
  (introduce_idle_asm false (four_tuple SIMP_mpc_5_button_F_opcode_1))
 );;

% ===================================================================== %
% Case: run, button = F, zero, opcode is 2 (JZR) ====================== %

let CASE_run_button_F_zero_opcode_2 =
 save_thm
 (
  `CASE_run_button_F_zero_opcode_2`,
  (introduce_idle_asm false (four_tuple SIMP_mpc_5_button_F_zero_opcode_2))
 );;

% ===================================================================== %
% Case: run, button = F, nonzero, opcode is 2 (JZR) =================== %

let CASE_run_button_F_nonzero_opcode_2 =
 save_thm
 (
  `CASE_run_button_F_nonzero_opcode_2`,
  (introduce_idle_asm false (four_tuple SIMP_mpc_5_button_F_nonzero_opcode_2))
 );;

% ===================================================================== %
% Case: run, button = F, opcode is 3 (ADD) ============================ %

let CASE_run_button_F_opcode_3 =
 save_thm
 (
  `CASE_run_button_F_opcode_3`,
  (introduce_idle_asm false (four_tuple SIMP_mpc_5_button_F_opcode_3))
 );;

% ===================================================================== %
% Case: run, button = F, opcode is 4 (SUB) ============================ %

let CASE_run_button_F_opcode_4 =
 save_thm
 (
  `CASE_run_button_F_opcode_4`,
  (introduce_idle_asm false (four_tuple SIMP_mpc_5_button_F_opcode_4))
 );;

% ===================================================================== %
% Case: run, button = F, opcode is 5 (LD) ============================= %

let CASE_run_button_F_opcode_5 =
 save_thm
 (
  `CASE_run_button_F_opcode_5`,
  (introduce_idle_asm false (four_tuple SIMP_mpc_5_button_F_opcode_5))
 );;

% ===================================================================== %
% Case: run, button = F, opcode is 6 (ST) ============================= %

let CASE_run_button_F_opcode_6 =
 save_thm
 (
  `CASE_run_button_F_opcode_6`,
  (introduce_idle_asm false (four_tuple SIMP_mpc_5_button_F_opcode_6))
 );;

% ===================================================================== %
% Case: run, button = F, opcode is 7 (SKIP) =========================== %

let CASE_run_button_F_opcode_7 =
 save_thm
 (
  `CASE_run_button_F_opcode_7`,
  (introduce_idle_asm false (four_tuple SIMP_mpc_5_button_F_opcode_7))
 );;

close_theory ();;
