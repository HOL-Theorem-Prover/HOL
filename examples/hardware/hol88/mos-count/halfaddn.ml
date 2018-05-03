% PROOF		: Transistor Implementation of a Counter		%
% FILE		: halfaddn.ml						%
%									%
% DESCRIPTION	: Defines a CMOS half-adder circuit and uses this	%
%		  to construct a n-bit half-adder.			%
%									%
%		  The specification of the half-adder is based on the	%
%		  specification and proof of a full-adder reported in	%
%		  Cambridge University Computer Laboratory Technical	%
%		  Reports #77 (M.Gordon) and #91 (A.Camilleri,M.Gordon,	%
%		  and T.Melham).					%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 31 March 1987						%

new_theory `halfaddn`;;

loadt `misc`;;
loadt `types`;;

new_parent `gates`;;

let HALFADD_IMP = new_definition (
	`HALFADD_IMP`,
	"HALFADD_IMP (a:^wire,cin:^wire,sum:^wire,cout:^wire) =
	  AND_IMP (a,cin,cout) /\ XOR_IMP (a,cin,sum)");;

let HALFADDn_IMP = new_prim_rec_definition (
	`HALFADDn_IMP`,
	"(HALFADDn_IMP 0 (a:^bus) (cin:^wire) (sum:^bus) (cout:^wire) =
	  HALFADD_IMP (DEST_BUS a 0,cin,DEST_BUS sum 0,cout)) /\
	 (HALFADDn_IMP (SUC n) a cin sum cout =
	  ?c.
	    HALFADDn_IMP n a cin sum c /\
	    HALFADD_IMP (DEST_BUS a (SUC n),c,DEST_BUS sum (SUC n),cout))");;

let Defn = theorem `dataabs` `Defn`;;
let WordAbs = definition `dataabs` `WordAbs`;;
let BoolVal = definition `dataabs` `BoolVal`;;
let WordVal = theorem `dataabs` `WordVal`;;
let DEST_BUS = definition `dataabs` `DEST_BUS`;;
let and = definition `gates` `and`;;
let xor = definition `gates` `xor`;;

let val_not_eq_ax = axiom `mos` `val_not_eq_ax`;;

let AND_CORRECT = theorem `gates` `AND_CORRECT`;;
let XOR_CORRECT = theorem `gates` `XOR_CORRECT`;;

let HALFADD_CORRECT = prove_thm (
	`HALFADD_CORRECT`,
	"!i cin sum cout.
	  HALFADD_IMP (i,cin,sum,cout)
	  ==>
	  !t.
	    Def (i t) /\ Def (cin t) ==>
	      Def (sum t) /\ Def (cout t) /\
	      ((2 * (BoolVal (BoolAbs (cout t)))) +
	        (BoolVal (BoolAbs (sum t))) =
	          (BoolVal (BoolAbs (i t))) + (BoolVal (BoolAbs (cin t))))",
	PURE_REWRITE_TAC [HALFADD_IMP] THEN
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC AND_CORRECT THEN
	IMP_RES_TAC XOR_CORRECT THEN
	RES_TAC THEN
	ASM_REWRITE_TAC [and;xor;BoolVal] THEN
	BOOL_CASES_TAC "BoolAbs (i t)" THEN
	BOOL_CASES_TAC "BoolAbs (cin t)" THEN
	REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES;num_CONV "2";num_CONV "1"]);;

let th1 = ASSUME
	"(2 * (BoolVal(BoolAbs(cout t)))) +
	  (BoolVal(BoolAbs(sum t(SUC n)))) =
	    (BoolVal(BoolAbs(i t(SUC n)))) + (BoolVal(BoolAbs(c t)))";;

let th2 = AP_TERM "$* (2 EXP (SUC n))" th1;;
let th3 = PURE_REWRITE_RULE [MULT_ASSOC;LEFT_ADD_DISTRIB] th2;;
let th4 = SUBS [SPECL ["2 EXP (SUC n)";"2"] MULT_SYM] th3;;
let th5 = PURE_REWRITE_RULE [SYM (CONJUNCT2 EXP)] th4;;
let th6 = BETA_RULE (AP_TERM "\tm. tm + (WordVal n (WordAbs (sum t)))" th5);;
let th7 = PURE_REWRITE_RULE [GEN_ALL (SYM (SPEC_ALL ADD_ASSOC))] th6;;

let th8 =
	BETA_RULE
	  ((DEPTH_CONV (REWRITE_CONV WordAbs)) "WordAbs v n");;

let HALFADDn_CORRECT = prove_thm (
	`HALFADDn_CORRECT`,
	"!n i cin sum cout.
	  HALFADDn_IMP n i cin sum cout
	  ==>
	  !t.
	    Defn n (i t) /\ Def (cin t) ==>
	      Defn n (sum t) /\ Def (cout t) /\
	      (((2 EXP (SUC n)) * (BoolVal (BoolAbs (cout t)))) +
	        (WordVal n (WordAbs (sum t))) =
	          (WordVal n (WordAbs (i t))) + (BoolVal (BoolAbs (cin t))))",
	INDUCT_TAC THENL
	[PURE_REWRITE_TAC [HALFADDn_IMP;Defn;WordAbs;WordVal] THEN
	 BETA_TAC THEN
	 PURE_REWRITE_TAC [EXP;MULT_CLAUSES] THEN
	 REPEAT STRIP_TAC THEN
	 HOL_IMP_RES_THEN
	  (IMP_RES_TAC o BETA_RULE o (PURE_REWRITE_RULE [DEST_BUS]))
	  HALFADD_CORRECT THEN
	 RES_TAC;
	 PURE_REWRITE_TAC [HALFADDn_IMP;Defn] THEN
	 REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
	 GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
	 RES_TAC THEN
	 RES_TAC THEN
	 HOL_IMP_RES_THEN
	  (IMP_RES_TAC o BETA_RULE o (PURE_REWRITE_RULE [DEST_BUS]))
	  HALFADD_CORRECT THEN
	 REPEAT STRIP_TAC THENL
	 [FIRST_ASSUM ACCEPT_TAC;
	  FIRST_ASSUM ACCEPT_TAC;
	  FIRST_ASSUM ACCEPT_TAC;
	  PURE_REWRITE_TAC
	    [WordVal;th8;GEN_ALL (SYM (SPEC_ALL ADD_ASSOC))] THEN
	  SUBST1_TAC th7 THEN
	  ASM_REWRITE_TAC []]]);;

close_theory ();;
