% ===================================================================== %
% 14 June 1989 - modified for HOL88					%
%									%
% The following bits are needed to make this proof run in HOL88.	%

set_flag (`sticky`,true);;
let definition x y = SPEC_ALL (definition x y);;
let new_definition = SPEC_ALL o new_definition ;;

let new_prim_rec_definition  =
	LIST_CONJ o (map SPEC_ALL) o CONJUNCTS o new_prim_rec_definition;;

% ===================================================================== %
% Jeff Joyce, University of Cambridge, 1 November 1988			%
%									%
% Combine results for each machine instructions to prove top-level	%
% correctness theorem.							%

new_theory `proof3`;;

new_parent `proof2`;;

% `o' already define in HOL88
let o_DEF = new_infix_definition (
	`o_DEF`,
	"$o (f:***->**) (g:*->***) = \x. f (g x)");;
%

let MicroCycles = new_definition (
	`MicroCycles`,
	"MicroCycles n (mem,pc,acc) =
	  let opc = Opc n (Inst n (mem,pc)) in
	  ((opc = 0) => ((acc = 0) => 5 | 6) |
	   (opc = 1) => 4 |
	   (opc = 2) => 8 |
	   (opc = 3) => 8 |
	   (opc = 4) => 6 |
	   (opc = 5) => 6 |
	   (opc = 6) => 6 |
	                5)");;

let REV_TimeOfCycle = new_prim_rec_definition (
	`REV_TimeOfCycle`,
	"(REV_TimeOfCycle 0 n mem pc acc = 0) /\
	 (REV_TimeOfCycle (SUC t) n mem pc acc =
	  let prev = (REV_TimeOfCycle t n mem pc acc) in
	  (prev + (MicroCycles n (mem prev,pc prev,acc prev))))");;

let TimeOfCycle = new_definition (
	`TimeOfCycle`,
	"TimeOfCycle n (mem,pc,acc) t = REV_TimeOfCycle t n mem pc acc");;

let JZR_T_INST_THM = theorem `proof2` `JZR_T_INST_THM`;;
let JZR_F_INST_THM = theorem `proof2` `JZR_F_INST_THM`;;
let JMP_INST_THM = theorem `proof2` `JMP_INST_THM`;;
let ADD_INST_THM = theorem `proof2` `ADD_INST_THM`;;
let SUB_INST_THM = theorem `proof2` `SUB_INST_THM`;;
let LD_INST_THM = theorem `proof2` `LD_INST_THM`;;
let ST_INST_THM = theorem `proof2` `ST_INST_THM`;;
let NOP1_INST_THM = theorem `proof2` `NOP1_INST_THM`;;
let NOP2_INST_THM = theorem `proof2` `NOP2_INST_THM`;;

let Opc = definition `tamarack` `Opc`;;
let Inst = definition `tamarack` `Inst`;;
let Behaviour = definition `tamarack` `Behaviour`;;

let th1 = mk_thm ([],"!n. 0 < (2 EXP n)");;
let MOD_LESS_THM = theorem `mod` `MOD_LESS_THM`;;

let LET_TAC = PURE_ONCE_REWRITE_TAC [LET_DEF] THEN BETA_TAC;;
let LET_RULE = BETA_RULE o (PURE_ONCE_REWRITE_RULE [LET_DEF]);;

let not_eq_CONV tm =
	if not (is_eq tm) then failwith `not_eq_CONV` else
	let [n;m] = map term_to_int [rand (rator tm);rand tm] in
	if m = n then failwith `not_eq_CONV` else
	TAC_PROOF (([],"^tm = F"),
	  CONV_TAC (REDEPTH_CONV num_CONV) THEN
	  REWRITE_TAC [INV_SUC_EQ;NOT_SUC]);;

let Opc_Cases_THM = TAC_PROOF ((
	[],
	"!n inst.
	  (Opc n inst = 0) \/
	  (Opc n inst = 1) \/
	  (Opc n inst = 2) \/
	  (Opc n inst = 3) \/
	  (Opc n inst = 4) \/
	  (Opc n inst = 5) \/
	  (Opc n inst = 6) \/
	  (Opc n inst = 7)"),
	REPEAT GEN_TAC THEN
	PURE_ONCE_REWRITE_TAC [Opc] THEN
	SPEC_TAC ("inst Div (2 EXP n)","m:num") THEN
	GEN_TAC THEN
	MP_TAC (SPEC "m:num" (MATCH_MP MOD_LESS_THM (SPEC "3" th1))) THEN
	SPEC_TAC ("m MOD (2 EXP 3)","p:num") THEN
	GEN_TAC THEN
	DISCH_THEN (MP_TAC o (CONV_RULE (REDEPTH_CONV num_CONV))) THEN
	PURE_REWRITE_TAC [num_CONV "1";EXP;MULT_CLAUSES;ADD_CLAUSES] THEN
	PURE_REWRITE_TAC [LESS_THM;NOT_LESS_0] THEN
	CONV_TAC (REDEPTH_CONV num_CONV) THEN
	STRIP_TAC THEN
	ASM_REWRITE_TAC []);;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 0)
	    ==>
	    let m = MicroCycles n (mem t,pc t,acc t) in
	    ((mpc (t+m) = 0) /\
	     ((mem (t+m),pc (t+m),acc (t+m)) =
	      NextState n (mem t,pc t,acc t)))");;

expandf (REPEAT STRIP_TAC THEN
	PURE_REWRITE_TAC [MicroCycles] THEN
	LET_TAC);;
expandf ((REPEAT_TCL DISJ_CASES_THEN) ASSUME_TAC
	  (SPECL ["n";"Inst n (mem t,pc t)"] Opc_Cases_THM) THEN
	ASM_REWRITE_TAC [] THEN
	CONV_TAC (DEPTH_CONV not_eq_CONV) THEN
	REWRITE_TAC [] THENL [
	  DISJ_CASES_TAC (SPEC "acc t = 0" EXCLUDED_MIDDLE) THEN
	  IMP_RES_THEN IMP_RES_TAC JZR_T_INST_THM THEN
	  IMP_RES_THEN IMP_RES_TAC JZR_F_INST_THM THEN
	  ASM_REWRITE_TAC [];
	  CONJ_TAC THEN IMP_RES_THEN IMP_RES_TAC JMP_INST_THM;
	  CONJ_TAC THEN IMP_RES_THEN IMP_RES_TAC ADD_INST_THM;
	  CONJ_TAC THEN IMP_RES_THEN IMP_RES_TAC SUB_INST_THM;
	  CONJ_TAC THEN IMP_RES_THEN IMP_RES_TAC LD_INST_THM;
	  CONJ_TAC THEN IMP_RES_THEN IMP_RES_TAC ST_INST_THM;
	  CONJ_TAC THEN IMP_RES_THEN IMP_RES_TAC NOP1_INST_THM;
	  CONJ_TAC THEN IMP_RES_THEN IMP_RES_TAC NOP2_INST_THM]);;

let EVERY_INST_THM = top_proof (rep_goals goals);;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf) /\
	  (mpc 0 = 0)
	  ==>
	  !t. mpc (TimeOfCycle n (mem,pc,acc) t) = 0");;

expandf (REPEAT GEN_TAC THEN
	STRIP_TAC THEN
	PURE_ONCE_REWRITE_TAC [TimeOfCycle] THEN
	INDUCT_TAC THENL [
	  ASM_REWRITE_TAC [REV_TimeOfCycle];
	  PURE_REWRITE_TAC [LET_RULE REV_TimeOfCycle] THEN
	  IMP_RES_TAC (LET_RULE EVERY_INST_THM)]);;

let ALWAYS_MPC_0_THM = top_proof (rep_goals goals);;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf) /\
	  (mpc 0 = 0)
	  ==>
	  let f = TimeOfCycle n (mem,pc,acc) in
	  Behaviour n (mem o f,pc o f,acc o f)");;

expandf (PURE_REWRITE_TAC [Behaviour;o_DEF] THEN
	LET_TAC THEN
	REPEAT STRIP_TAC);;
expandf (PURE_REWRITE_TAC [num_CONV "1";ADD_CLAUSES] THEN
	PURE_REWRITE_TAC [TimeOfCycle;LET_RULE REV_TimeOfCycle] THEN
	PURE_ONCE_REWRITE_TAC [SYM TimeOfCycle]);;
expandf (IMP_RES_THEN (ASSUME_TAC o (SPEC "t:num")) ALWAYS_MPC_0_THM);;
expandf (IMP_RES_TAC (LET_RULE EVERY_INST_THM));;

let CORRECTNESS_THM = save_thm (`CORRECTNESS_THM`,top_proof (rep_goals goals));;

close_theory ();;
