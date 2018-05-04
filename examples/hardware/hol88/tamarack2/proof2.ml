% ===================================================================== %
% 14 June 1989 - modified for HOL88					%
%									%
% The following bits are needed to make this proof run in HOL88.	%

set_flag (`sticky`,true);;
let definition x y = SPEC_ALL (definition x y);;

% ===================================================================== %
% Jeff Joyce, University of Cambridge, 1 November 1988			%
%									%
% Derive results of executing microinstructions sequences implementing	%
% machine instructions.							%

new_theory `proof2`;;

new_parent `proof1`;;

let Bits = definition `tamarack` `Bits`;;
let Inst = definition `tamarack` `Inst`;;
let Opc = definition `tamarack` `Opc`;;
let Addr = definition `tamarack` `Addr`;;
let NextState = definition `tamarack` `NextState`;;
let Behaviour = definition `tamarack` `Behaviour`;;

let MPC_0_THM = theorem `proof1` `MPC_0_THM`;;
let MPC_1_THM = theorem `proof1` `MPC_1_THM`;;
let MPC_2_THM = theorem `proof1` `MPC_2_THM`;;
let MPC_3_THM = theorem `proof1` `MPC_3_THM`;;
let MPC_4_THM = theorem `proof1` `MPC_4_THM`;;
let MPC_5_THM = theorem `proof1` `MPC_5_THM`;;
let MPC_6_THM = theorem `proof1` `MPC_6_THM`;;
let MPC_7_THM = theorem `proof1` `MPC_7_THM`;;
let MPC_8_THM = theorem `proof1` `MPC_8_THM`;;
let MPC_9_THM = theorem `proof1` `MPC_9_THM`;;
let MPC_10_THM = theorem `proof1` `MPC_10_THM`;;
let MPC_11_THM = theorem `proof1` `MPC_11_THM`;;
let MPC_12_THM = theorem `proof1` `MPC_12_THM`;;
let MPC_13_THM = theorem `proof1` `MPC_13_THM`;;
let MPC_14_THM = theorem `proof1` `MPC_14_THM`;;

let Div_THM = theorem `div` `Div_THM`;;

let PAIR_EQ_THM = theorem `proof1` `PAIR_EQ_THM`;;

let LET_TAC = PURE_ONCE_REWRITE_TAC [LET_DEF] THEN BETA_TAC;;
let LET_RULE = BETA_RULE o (PURE_ONCE_REWRITE_RULE [LET_DEF]);;

let FILTER_IMP_RES_THEN f ttac =
	HOL_IMP_RES_THEN
	  (\thm. if f (concl thm) then (ttac thm) else ALL_TAC);;
let FILTER_IMP_RES_TAC f = FILTER_IMP_RES_THEN f ASSUME_TAC;;

let (MATCH_GOAL_TAC:thm_tactic) impthm (asl,tm) = (
	let match = ((PART_MATCH (snd o dest_imp)) impthm) tm
	in
	([asl,fst (dest_imp (concl match))],\[th]. MP match th)) ?
	failwith `MATCH_GOAL_TAC`;;

let sum_CONV tm =
	if not (rator (rator tm)) = "$+" then failwith `sum_CONV` else
	let [n;m] = map term_to_int [rand (rator tm);rand tm] in
	TAC_PROOF (([],"^tm = ^(int_to_term (n+m))"),
	  CONV_TAC (REDEPTH_CONV num_CONV) THEN
	  REWRITE_TAC [ADD_CLAUSES]);;

let not_eq_CONV tm =
	if not (is_eq tm) then failwith `not_eq_CONV` else
	let [n;m] = map term_to_int [rand (rator tm);rand tm] in
	if m = n then failwith `not_eq_CONV` else
	TAC_PROOF (([],"^tm = F"),
	  CONV_TAC (REDEPTH_CONV num_CONV) THEN
	  REWRITE_TAC [INV_SUC_EQ;NOT_SUC]);;

let nextstate = LET_RULE NextState;;

let Div_2_EXP_0_THM = TAC_PROOF (
	([],"!n. n Div (2 EXP 0) = n"),
	MP_TAC (MATCH_MP Div_THM (REWRITE_RULE [ADD1] (SPEC "0" LESS_0))) THEN
	REWRITE_TAC [EXP;ADD_CLAUSES;MULT_CLAUSES]);;

let EXEC_MPC_TAC mpc_thm tm tac =
	FILTER_IMP_RES_THEN is_eq MP_TAC mpc_thm THEN
	SUBST1_TAC
	  (SYM (REWRITE_RULE [ADD1;ADD_ASSOC] (DEPTH_CONV num_CONV tm))) THEN
	tac THEN
	DISCH_THEN (STRIP_ASSUME_TAC o (PURE_REWRITE_RULE [PAIR_EQ_THM]));;

let EXEC_INST_FETCH_TAC =
	PURE_REWRITE_TAC [Opc;Inst] THEN
	REPEAT (FIRST [GEN_TAC;DISCH_THEN STRIP_ASSUME_TAC]) THEN
	EXEC_MPC_TAC MPC_0_THM "t+1" ALL_TAC THEN
	EXEC_MPC_TAC MPC_1_THM "t+2" ALL_TAC THEN
	EXEC_MPC_TAC MPC_2_THM "t+3"
	  (FILTER_ASM_REWRITE_TAC is_eq [Bits;Div_2_EXP_0_THM] THEN
	   CONV_TAC (DEPTH_CONV sum_CONV));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 0) /\
	    (Opc n (Inst n (mem t,pc t)) = 0) /\
	    (acc t = 0)
	    ==>
	    (mpc (t+5) = 0) /\
	    ((mem (t+5),pc (t+5),acc (t+5)) =
	      NextState n (mem t,pc t,acc t))");;

expandf EXEC_INST_FETCH_TAC;;
expandf (EXEC_MPC_TAC MPC_3_THM "t+4" (ASM_REWRITE_TAC []));;
expandf (EXEC_MPC_TAC MPC_4_THM "t+5" ALL_TAC);;
expandf (ASM_REWRITE_TAC [nextstate;Inst;Opc;Addr;Bits;Div_2_EXP_0_THM]);;

let JZR_T_INST_THM = save_thm (`JZR_T_INST_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 0) /\
	    (Opc n (Inst n (mem t,pc t)) = 0) /\
	    ~(acc t = 0)
	    ==>
	    (mpc (t+6) = 0) /\
	    ((mem (t+6),pc (t+6),acc (t+6)) =
	      NextState n (mem t,pc t,acc t))");;

expandf EXEC_INST_FETCH_TAC;;
expandf (EXEC_MPC_TAC MPC_3_THM "t+4" (ASM_REWRITE_TAC []));;
expandf (EXEC_MPC_TAC MPC_10_THM "t+5" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_11_THM "t+6" ALL_TAC);;
expandf (ASM_REWRITE_TAC [nextstate;Inst;Opc;Addr;Bits;Div_2_EXP_0_THM]);;

let JZR_F_INST_THM = save_thm (`JZR_F_INST_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 0) /\
	    (Opc n (Inst n (mem t,pc t)) = 1)
	    ==>
	    (mpc (t+4) = 0) /\
	    ((mem (t+4),pc (t+4),acc (t+4)) =
	      NextState n (mem t,pc t,acc t))");;

expandf EXEC_INST_FETCH_TAC;;
expandf (EXEC_MPC_TAC MPC_4_THM "t+4" ALL_TAC);;
expandf (ASM_REWRITE_TAC [nextstate;Inst;Opc;Addr;Bits;Div_2_EXP_0_THM]);;
expandf (CONV_TAC (DEPTH_CONV not_eq_CONV));;
expandf (REWRITE_TAC []);;

let JMP_INST_THM = save_thm (`JMP_INST_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 0) /\
	    (Opc n (Inst n (mem t,pc t)) = 2)
	    ==>
	    (mpc (t+8) = 0) /\
	    ((mem (t+8),pc (t+8),acc (t+8)) =
	      NextState n (mem t,pc t,acc t))");;

expandf EXEC_INST_FETCH_TAC;;
expandf (EXEC_MPC_TAC MPC_5_THM "t+4" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_12_THM "t+5" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_14_THM "t+6" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_10_THM "t+7" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_11_THM "t+8" ALL_TAC);;
expandf (ASM_REWRITE_TAC [nextstate;Inst;Opc;Addr;Bits;Div_2_EXP_0_THM]);;
expandf (CONV_TAC (DEPTH_CONV not_eq_CONV));;
expandf (REWRITE_TAC []);;

let ADD_INST_THM = save_thm (`ADD_INST_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 0) /\
	    (Opc n (Inst n (mem t,pc t)) = 3)
	    ==>
	    (mpc (t+8) = 0) /\
	    ((mem (t+8),pc (t+8),acc (t+8)) =
	      NextState n (mem t,pc t,acc t))");;

expandf EXEC_INST_FETCH_TAC;;
expandf (EXEC_MPC_TAC MPC_6_THM "t+4" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_13_THM "t+5" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_14_THM "t+6" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_10_THM "t+7" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_11_THM "t+8" ALL_TAC);;
expandf (ASM_REWRITE_TAC [nextstate;Inst;Opc;Addr;Bits;Div_2_EXP_0_THM]);;
expandf (CONV_TAC (DEPTH_CONV not_eq_CONV));;
expandf (REWRITE_TAC []);;

let SUB_INST_THM = save_thm (`SUB_INST_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 0) /\
	    (Opc n (Inst n (mem t,pc t)) = 4)
	    ==>
	    (mpc (t+6) = 0) /\
	    ((mem (t+6),pc (t+6),acc (t+6)) =
	      NextState n (mem t,pc t,acc t))");;

expandf EXEC_INST_FETCH_TAC;;
expandf (EXEC_MPC_TAC MPC_7_THM "t+4" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_10_THM "t+5" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_11_THM "t+6" ALL_TAC);;
expandf (ASM_REWRITE_TAC [nextstate;Inst;Opc;Addr;Bits;Div_2_EXP_0_THM]);;
expandf (CONV_TAC (DEPTH_CONV not_eq_CONV));;
expandf (REWRITE_TAC []);;

let LD_INST_THM = save_thm (`LD_INST_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 0) /\
	    (Opc n (Inst n (mem t,pc t)) = 5)
	    ==>
	    (mpc (t+6) = 0) /\
	    ((mem (t+6),pc (t+6),acc (t+6)) =
	      NextState n (mem t,pc t,acc t))");;

expandf EXEC_INST_FETCH_TAC;;
expandf (EXEC_MPC_TAC MPC_8_THM "t+4" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_10_THM "t+5" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_11_THM "t+6" ALL_TAC);;
expandf (ASM_REWRITE_TAC [nextstate;Inst;Opc;Addr;Bits;Div_2_EXP_0_THM]);;
expandf (CONV_TAC (DEPTH_CONV not_eq_CONV));;
expandf (REWRITE_TAC []);;

let ST_INST_THM = save_thm (`ST_INST_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 0) /\
	    (Opc n (Inst n (mem t,pc t)) = 6)
	    ==>
	    (mpc (t+6) = 0) /\
	    ((mem (t+6),pc (t+6),acc (t+6)) =
	      NextState n (mem t,pc t,acc t))");;

expandf EXEC_INST_FETCH_TAC;;
expandf (EXEC_MPC_TAC MPC_9_THM "t+4" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_10_THM "t+5" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_11_THM "t+6" ALL_TAC);;
expandf (ASM_REWRITE_TAC [nextstate;Inst;Opc;Addr;Bits;Div_2_EXP_0_THM]);;
expandf (CONV_TAC (DEPTH_CONV not_eq_CONV));;
expandf (REWRITE_TAC []);;

let NOP1_INST_THM = save_thm (`NOP1_INST_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 0) /\
	    (Opc n (Inst n (mem t,pc t)) = 7)
	    ==>
	    (mpc (t+5) = 0) /\
	    ((mem (t+5),pc (t+5),acc (t+5)) =
	      NextState n (mem t,pc t,acc t))");;

expandf EXEC_INST_FETCH_TAC;;
expandf (EXEC_MPC_TAC MPC_10_THM "t+4" ALL_TAC);;
expandf (EXEC_MPC_TAC MPC_11_THM "t+5" ALL_TAC);;
expandf (ASM_REWRITE_TAC [nextstate;Inst;Opc;Addr;Bits;Div_2_EXP_0_THM]);;
expandf (CONV_TAC (DEPTH_CONV not_eq_CONV));;
expandf (REWRITE_TAC []);;

let NOP2_INST_THM = save_thm (`NOP2_INST_THM`,top_proof (rep_goals goals));;

close_theory ();;
