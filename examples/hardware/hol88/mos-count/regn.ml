% PROOF		: Transistor Implementation of a Counter		%
% FILE		: regn.ml						%
%									%
% DESCRIPTION	: Defines a dynamic register and uses it to construct	%
%		  a n-bit dynamic register.  Note that only N-type	%
%		  pass transistors are used instead of complementary	%
%		  logic.						%
%									%
%		  The register model is taken from Inder Dhingra's	%
%		  paper, "Formal Validation of an Integrated Circuit	%
%		  Design Style", Hardware Verification Workshop,	%
%		  University of Calgary, January 1987.			%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 31 March 1987						%

new_theory `regn`;;

loadt `misc`;;
loadt `types`;;

new_parent `clock`;;
new_parent `dataabs`;;

% =====================================================================	%
% Propagation of a signal through the register:				%
%									%
%             phiA                       phiB				%
%	      _|_                        _|_				%
%	i ___|   |___w1_____w2_____w3___|   |___w4_____w5_____ o	%
%	                 |      |                   |      |		%
%	                Cap1   Cap2                Cap3   Cap4		%
%									%
%  t	i(t)         i(t)						%
%  t+1	             Zz     i(t)					%
%  t+2	             Zz     Zz     i(t)         i(t)			%
%  t+3                                          Zz     i(t)		%
%  t+4                                          Zz     Zz      i(t)	%
% ===================================================================== %

let REG_IMP = new_definition (
	`REG_IMP`,
	"REG_IMP (phi1:^wire,phi2:^wire,i:^wire,o:^wire) =
	  ?w1 w2 w3 w4 w5.
	    Ntran (phi1,i,w1) /\
	    Cap (w1,w2) /\
	    Cap (w2,w3) /\
	    Ntran (phi2,w3,w4) /\
	    Cap (w4,w5) /\
	    Cap (w5,o)");;

let REGn_IMP = new_definition (
	`REGn_IMP`,
	"REGn_IMP n (phi1:^wire,phi2:^wire,i:^bus,o:^bus) =
	  !m. m <= n ==> REG_IMP (phi1,phi2,DEST_BUS i m,DEST_BUS o m)");;

let when = definition `tempabs` `when`;;
let Cap = definition `mos` `Cap`;;
let Ntran = definition `mos` `Ntran`;;
let Clock = definition `clock` `Clock`;;
let DEST_BUS = definition `dataabs` `DEST_BUS`;;

let val_not_eq_ax = axiom `mos` `val_not_eq_ax`;;

let ClockSignals = theorem `clock` `ClockSignals`;;
let TimeOf_isHi_TRUE = theorem `clock` `TimeOf_isHi_TRUE`;;
let TimeOf_isHi_plus4 = theorem `clock` `TimeOf_isHi_plus4`;;

let isBus_THM = theorem `dataabs` `isBus_THM`;;
let Clock_Cycle = theorem `clock` `Clock_Cycle`;;

let t0 = "t:num";;
let t1 = "SUC t";;
let t2 = "SUC(SUC t)";;
let t3 = "SUC(SUC(SUC t))";;
let t4 = "SUC(SUC(SUC(SUC t)))";;

let w1thm = PURE_REWRITE_RULE [Ntran] (ASSUME "Ntran(phiA,i,w1)");;
let w2thm = PURE_REWRITE_RULE [Cap] (ASSUME "Cap(w1,w2)");;
let w3thm = PURE_REWRITE_RULE [Cap] (ASSUME "Cap(w2,w3)");;
let w4thm = PURE_REWRITE_RULE [Ntran] (ASSUME "Ntran(phiB,w3,w4)");;
let w5thm = PURE_REWRITE_RULE [Cap] (ASSUME "Cap(w4,w5)");;
let othm = PURE_REWRITE_RULE [Cap] (ASSUME "Cap(w5,o)");;

% The following 12 theorems establish that the output signal at time	%
% "t+4" is the value of the input signal at time "t" following the	%
% causal relationships shown in the above diagram.  Assumptions about	%
% phiA and phiB are introduced as required.				%

let w1t0 = REWRITE_RULE [ASSUME "phiA ^t0 = Hi"] (SPEC t0 w1thm);;
let w1t1 =
	REWRITE_RULE
	  [ASSUME "phiA ^t1 = Lo";val_not_eq_ax] (SPEC t1 w1thm);;
let w1t2 =
	REWRITE_RULE
	  [ASSUME "phiA ^t2 = Lo";val_not_eq_ax] (SPEC t2 w1thm);;
let w2t1 = REWRITE_RULE [SUC_SUB1;w1t1;w1t0] (SPEC t1 w2thm);;
let w2t2 = REWRITE_RULE [SUC_SUB1;w1t2;w1t1] (SPEC t2 w2thm);;
let w3t2 = REWRITE_RULE [SUC_SUB1;w2t2;w2t1] (SPEC t2 w3thm);;
let w3t2 = REWRITE_RULE [SUC_SUB1;w2t2;w2t1] (SPEC t2 w3thm);;
let w4t2 = REWRITE_RULE [ASSUME "phiB ^t2 = Hi";w3t2] (SPEC t2 w4thm);;
let w4t3 =
	REWRITE_RULE
	  [ASSUME "phiB ^t3 = Lo";val_not_eq_ax] (SPEC t3 w4thm);;
let w4t4 =
	REWRITE_RULE
	  [ASSUME "phiB ^t4 = Lo";val_not_eq_ax] (SPEC t4 w4thm);;
let w5t3 = REWRITE_RULE [SUC_SUB1;w4t3;w4t2] (SPEC t3 w5thm);;
let w5t4 = REWRITE_RULE [SUC_SUB1;w4t4;w4t3] (SPEC t4 w5thm);;
let ot4 = REWRITE_RULE [SUC_SUB1;w5t4;w5t3] (SPEC t4 othm);;

% ot4 = ............ |- o(SUC(SUC(SUC(SUC t)))) = i t %

let REG_CORRECT = prove_thm (
	`REG_CORRECT`,
	"!phi1 phi1bar phi2 phi2bar i o.
	  Clock (phi1,phi1bar,phi2,phi2bar) /\
	  REG_IMP (phi1,phi2,i,o)
	  ==>
	  !t. ((o when (isHi phi1)) (t+1) = (i when (isHi phi1)) t)",
	PURE_REWRITE_TAC [REG_IMP;when] THEN
	BETA_TAC THEN
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC Clock_Cycle THEN
	IMP_RES_TAC TimeOf_isHi_plus4 THEN
	ASM_REWRITE_TAC [] THEN
	HOL_IMP_RES_THEN (ASSUME_TAC o (SPEC "t")) TimeOf_isHi_TRUE THEN
	SUC_FORM_TAC THEN
	IMP_RES_TAC (SUC_FORM_RULE ClockSignals) THEN
	IMP_RES_TAC (GEN "t" (DISCH_ALL ot4)));;

let REGn_CORRECT = prove_thm (
	`REGn_CORRECT`,
	"!n phi1 phi1bar phi2 phi2bar i o.
	  Clock (phi1,phi1bar,phi2,phi2bar) /\
	  REGn_IMP n (phi1,phi2,i,o) /\
	  isBus n i /\
	  isBus n o
	  ==>
	  !t. ((o when (isHi phi1)) (t+1) = (i when (isHi phi1)) t)",
	PURE_REWRITE_TAC [REGn_IMP;when] THEN
	BETA_TAC THEN
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC isBus_THM THEN
	ASM_REWRITE_TAC [] THEN
	REPEAT STRIP_TAC THEN
	RES_TAC THEN
	HOL_IMP_RES_THEN
	  (ASSUME_TAC o BETA_RULE o (PURE_REWRITE_RULE [DEST_BUS;when]))
	  REG_CORRECT THEN
	ASM_REWRITE_TAC []);;

close_theory ();;
