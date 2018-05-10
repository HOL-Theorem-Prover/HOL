% ===================================================================== %
% 14 June 1989 - modified for HOL88					%
%									%
% The following bits are needed to make this proof run in HOL88.	%

set_flag (`sticky`,true);;
load_library `string`;;
let definition x y = SPEC_ALL (definition x y);;

% ===================================================================== %
% Jeff Joyce, University of Cambridge, 1 November 1988			%
%									%
% Derive results of executing individual microinstructions.		%

new_theory `proof1`;;

new_parent `tamarack`;;

let ADDn = definition `tamarack` `ADDn`;;
let Bits = definition `tamarack` `Bits`;;
let PWR = definition `tamarack` `PWR`;;
let GND = definition `tamarack` `GND`;;
let AND = definition `tamarack` `AND`;;
let OR = definition `tamarack` `OR`;;
let MUX = definition `tamarack` `MUX`;;
let BITS = definition `tamarack` `BITS`;;
let TNZ = definition `tamarack` `TNZ`;;
let HWC = definition `tamarack` `HWC`;;
let ADDER = definition `tamarack` `ADDER`;;
let ALU = definition `tamarack` `ALU`;;
let DEL = definition `tamarack` `DEL`;;
let REG = definition `tamarack` `REG`;;
let MEM = definition `tamarack` `MEM`;;
let CheckCntls = definition `tamarack` `CheckCntls`;;
let DataPath = definition `tamarack` `DataPath`;;
let Cntls = definition `tamarack` `Cntls`;;
let NextMpc = definition `tamarack` `NextMpc`;;
let Microcode = definition `tamarack` `Microcode`;;
let ROM = definition `tamarack` `ROM`;;
let Decoder = definition `tamarack` `Decoder`;;
let MpcUnit = definition `tamarack` `MpcUnit`;;
let CntlUnit = definition `tamarack` `CntlUnit`;;
let Tamarack = definition `tamarack` `Tamarack`;;

let LESS_MOD_THM = theorem `mod` `LESS_MOD_THM`;;
let LESS_LESS_MONO = theorem `arith` `LESS_LESS_MONO`;;
let MOD_LESS_THM = theorem `mod` `MOD_LESS_THM`;;

let FILTER_IMP_RES_THEN f ttac =
	HOL_IMP_RES_THEN
	  (\thm. if f (concl thm) then (ttac thm) else ALL_TAC);;
let FILTER_IMP_RES_TAC f = FILTER_IMP_RES_THEN f ASSUME_TAC;;

let (MATCH_GOAL_TAC:thm_tactic) impthm (asl,tm) = (
	let match = ((PART_MATCH (snd o dest_imp)) impthm) tm
	in
	([asl,fst (dest_imp (concl match))],\[th]. MP match th)) ?
	failwith `MATCH_GOAL_TAC`;;

let PAIR_EQ_THM = prove_thm (
	`PAIR_EQ_THM`,
	"!a:*. !b:**. !c:*. !d:**. ((a,b) = (c,d)) = ((a = c) /\ (b = d))",
	REPEAT STRIP_TAC THEN
	EQ_TAC THENL
	[DISCH_THEN
	  (\thm.
	    REWRITE_TAC [
	      PURE_REWRITE_RULE [FST;SND]
	        (CONJ
	          (AP_TERM "FST:(* # **)->*" thm)
	          (AP_TERM "SND:(* # **)->**" thm))]);
	 DISCH_TAC THEN
	 ASM_REWRITE_TAC []]);;

let not_eq_CONV tm =
	if not (is_eq tm) then failwith `not_eq_CONV` else
	let [n;m] = map term_to_int [rand (rator tm);rand tm] in
	if m = n then failwith `not_eq_CONV` else
	TAC_PROOF (([],"^tm = F"),
	  CONV_TAC (REDEPTH_CONV num_CONV) THEN
	  REWRITE_TAC [INV_SUC_EQ;NOT_SUC]);;

% The two steps could take quite a long time ! %

let thlist1 = map
	(\n.
	  (REWRITE_RULE []
	    (CONV_RULE (ONCE_DEPTH_CONV not_eq_CONV)
	      (REWRITE_RULE []
	        (SPEC (int_to_term n) (GEN "n:num" Microcode))))))
	[0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15];;

let Microcode_THMS = map
	((REWRITE_RULE []) o
	 (CONV_RULE (ONCE_DEPTH_CONV string_EQ_CONV)) o
	 (PURE_ONCE_REWRITE_RULE [Cntls;NextMpc]))
	thlist1;;

let EXP_2_4 =
	PURE_REWRITE_RULE [MULT_CLAUSES;ADD_CLAUSES]
	  (PURE_REWRITE_RULE [num_CONV "1";EXP]
	    ((REDEPTH_CONV num_CONV) "2 EXP 4"));;

% The following tactics correspond to the sequence of steps which take	%
% place when a microinstruction is executed:  tac1 - produce microcode	%
% ROM output; tac2 - generate next mpc state; tac3 - generate next data	%
% path state.  The last step, tac4, is used to simplify the mpc state.	%

let tac1 =
	PURE_REWRITE_TAC [Tamarack;CntlUnit;ROM] THEN
	REPEAT STRIP_TAC THEN
	IMP_RES_THEN (MP_TAC o (SPEC "t")) (fst (EQ_IMP_RULE Decoder)) THEN
	PURE_ASM_REWRITE_TAC [] THEN
	SUBST_TAC Microcode_THMS THEN
	DISCH_THEN (STRIP_ASSUME_TAC o (PURE_REWRITE_RULE [PAIR_EQ_THM]));;

let tac2 =
	IMP_RES_THEN MP_TAC (fst (EQ_IMP_RULE MpcUnit)) THEN
	PURE_ONCE_REWRITE_TAC [AND;OR;MUX;HWC;ADDER;DEL] THEN
	DISCH_THEN ((REPEAT_TCL CHOOSE_THEN) (\thm. REWRITE_TAC [thm])) THEN
	ASM_REWRITE_TAC [];;

let tac3 =
	IMP_RES_THEN MP_TAC (fst (EQ_IMP_RULE DataPath)) THEN
	PURE_ONCE_REWRITE_TAC [CheckCntls;MEM;REG;BITS;TNZ;ALU;PWR;GND] THEN
	DISCH_THEN ((REPEAT_TCL CHOOSE_THEN) MP_TAC) THEN
	DISCH_THEN (MP_TAC o LIST_CONJ o (map (SPEC "t")) o CONJUNCTS) THEN
	ASM_REWRITE_TAC [PAIR_EQ_THM] THEN
	DISCH_THEN
	  (\thm. MP_TAC (REWRITE_RULE [CONJUNCT1 thm] (CONJUNCT2 thm))) THEN
	STRIP_TAC THEN
	ASM_REWRITE_TAC [];;

let tac4 =
	REWRITE_TAC [ADDn] THEN
	SUBST1_TAC EXP_2_4 THEN
	CONV_TAC (REDEPTH_CONV num_CONV) THEN
	PURE_REWRITE_TAC [ADD_CLAUSES] THEN
	MATCH_GOAL_TAC LESS_MOD_THM THEN
	REWRITE_TAC [LESS_MONO_EQ;LESS_0];;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 0) ==>
	    ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1)) =
	     (1,mem t,pc t,pc t,acc t))");;

expandf (tac1 THEN tac2 THEN tac3);;
expandf tac4;;

let MPC_0_THM = save_thm (`MPC_0_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 1) ==>
	    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),ir (t+1)) =
	     (2,mem t,pc t,acc t,mem t (Bits (0,n) (mar t))))");;

expandf (tac1 THEN tac2 THEN tac3);;
expandf tac4;;

let MPC_1_THM = save_thm (`MPC_1_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 2) ==>
	    ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1),ir (t+1)) =
	     ((Bits (n,3) (ir t)) + 3,mem t,ir t,pc t,acc t,ir t))");;

expandf (tac1 THEN tac2 THEN tac3);;

let th1 = mk_thm ([],"!n. 0 < (2 EXP n)");;

let th2 = TAC_PROOF (([],"3 < (2 EXP 3)"),
	CONV_TAC (REDEPTH_CONV num_CONV) THEN
	PURE_REWRITE_TAC [num_CONV "1";EXP] THEN
	PURE_REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES] THEN
	REWRITE_TAC [LESS_MONO_EQ;LESS_0]);;

expandf (PURE_REWRITE_TAC [ADDn;Bits] THEN
	MATCH_GOAL_TAC LESS_MOD_THM THEN
	SUBST1_TAC (DEPTH_CONV num_CONV "2 EXP 4") THEN
	PURE_REWRITE_TAC [EXP;MULT_CLAUSES;ADD_CLAUSES] THEN
	SUBST1_TAC (SYM (num_CONV "2")) THEN
	ASSUME_TAC
	  (SPEC "((ir t) Div (2 EXP n))"
	    (MATCH_MP MOD_LESS_THM (SPEC "3" th1))) THEN
	ASSUME_TAC th2 THEN
	PURE_ONCE_REWRITE_TAC [ADD_SYM] THEN
	IMP_RES_TAC LESS_LESS_MONO);;

let MPC_2_THM = save_thm (`MPC_2_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 3) ==>
	    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),ir (t+1)) =
	     ((((acc t) = 0) => 4 | 10),mem t,pc t,acc t,ir t))");;

expandf (tac1 THEN tac2 THEN tac3);;
expandf (BOOL_CASES_TAC "(acc:bus) t = 0" THEN
	tac4);;

let MPC_3_THM = save_thm (`MPC_3_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 4) ==>
	    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
	     (0,mem t,ir t,acc t))");;

expandf (tac1 THEN tac2 THEN tac3);;
expandf tac4;;

let MPC_4_THM = save_thm (`MPC_4_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 5) ==>
	    ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1),arg (t+1)) =
	     (12,mem t,mar t,pc t,acc t,acc t))");;

expandf (tac1 THEN tac2 THEN tac3);;
expandf tac4;;

let MPC_5_THM = save_thm (`MPC_5_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 6) ==>
	    ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1),arg (t+1)) =
	     (13,mem t,mar t,pc t,acc t,acc t))");;

expandf (tac1 THEN tac2 THEN tac3);;
expandf tac4;;

let MPC_6_THM = save_thm (`MPC_6_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 7) ==>
	    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
	     (10,mem t,pc t,mem t (Bits (0,n) (mar t))))");;

expandf (tac1 THEN tac2 THEN tac3);;
expandf tac4;;

let MPC_7_THM = save_thm (`MPC_7_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 8) ==>
	    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
	     (10,Update (mem t,Bits (0,n) (mar t),acc t),pc t,acc t))");;

expandf (tac1 THEN tac2 THEN tac3);;
expandf tac4;;

let MPC_8_THM = save_thm (`MPC_8_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 9) ==>
	    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
	     (10,mem t,pc t,acc t))");;

expandf (tac1 THEN tac2 THEN tac3);;
expandf tac4;;

let MPC_9_THM = save_thm (`MPC_9_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 10) ==>
	    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),buf (t+1)) =
	     (11,mem t,pc t,acc t,INCn (n+3) (pc t)))");;

expandf (tac1 THEN tac2 THEN tac3);;
expandf tac4;;

let MPC_10_THM = save_thm (`MPC_10_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 11) ==>
	    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
	     (0,mem t,buf t,acc t))");;

expandf (tac1 THEN tac2 THEN tac3);;
expandf tac4;;

let MPC_11_THM = save_thm (`MPC_11_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 12) ==>
	    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),buf (t+1)) =
	     (14,mem t,pc t,acc t,
	      ADDn (n+3) (arg t,mem t (Bits (0,n) (mar t)))))");;

expandf (tac1 THEN tac2 THEN tac3);;
expandf tac4;;

let MPC_12_THM = save_thm (`MPC_12_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 13) ==>
	    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),buf (t+1)) =
	     (14,mem t,pc t,acc t,
	      SUBn (n+3) (arg t,mem t (Bits (0,n) (mar t)))))");;

expandf (tac1 THEN tac2 THEN tac3);;
expandf tac4;;

let MPC_13_THM = save_thm (`MPC_13_THM`,top_proof (rep_goals goals));;

set_goal ([],
	"!n mpc mem mar pc acc ir arg buf.
	  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
	  ==>
	  !t.
	    (mpc t = 14) ==>
	    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
	     (10,mem t,pc t,buf t))");;

expandf (tac1 THEN tac2 THEN tac3);;
expandf tac4;;

let MPC_14_THM = save_thm (`MPC_14_THM`,top_proof (rep_goals goals));;

close_theory ();;
