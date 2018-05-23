% PROOF		: Transistor Implementation of a Counter		%
% FILE		: incn.ml						%
%									%
% DESCRIPTION	: Connect carry-in line of n-bit halfadder to Vdd to	%
%		  make a n-bit increment circuit and derives its	%
%		  behaviour in terms of addition modulo (2 EXP n).	%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 1 April 1987						%

new_theory `incn`;;

loadt `misc`;;
loadt `types`;;

new_parent `mod`;;
new_parent `halfaddn`;;

let INCn_IMP = new_definition (
	`INCn_IMP`,
	"INCn_IMP n (i:^bus,o:^bus) =
	  ?cin cout. HALFADDn_IMP n i cin o cout /\ Vdd cin");;

let Vdd = definition `mos` `Vdd`;;
let Def = definition `dataabs` `Def`;;
let BoolVal = definition `dataabs` `BoolVal`;;
let WordVal = theorem `dataabs` `WordVal`;;

let MOD_THM = theorem `mod` `MOD_THM`;;
let BoolAbs_THM = theorem `dataabs` `BoolAbs_THM`;;
let HALFADDn_CORRECT = theorem `halfaddn` `HALFADDn_CORRECT`;;

let lemma1 = TAC_PROOF (
	([],"!w. Vdd w ==> !t. Def (w t) /\ (BoolVal (BoolAbs (w t)) = 1)"),
	PURE_REWRITE_TAC [Vdd] THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC [Def;BoolVal;BoolAbs_THM]);;

let lemma2 =
	GEN_ALL
	  (PURE_REWRITE_RULE [MULT_CLAUSES;ADD_CLAUSES]
	    (SPECL ["m";"n";"0"] MOD_THM));;
let lemma3 =
	GEN_ALL
	  (PURE_REWRITE_RULE [MULT_CLAUSES] (SPECL ["m";"n";"1"] MOD_THM));;

let th1 = TAC_PROOF (
	([],"1 < 2"),
	SUC_FORM_TAC THEN REWRITE_TAC [LESS_SUC_REFL]);;

let th2 = TAC_PROOF (
	([],"0 < 2"),
	SUC_FORM_TAC THEN REWRITE_TAC [LESS_0]);;

let th3 = (DEPTH_CONV (REWRITE_CONV (num_CONV "2"))) "2 * a";;

let th4 =
	GEN_ALL
	  (SUBS [SPECL ["m";"p"] ADD_SYM;SPECL ["n";"p"] ADD_SYM]
	    (SPEC_ALL LESS_MONO_ADD_EQ));;

let th5 = TAC_PROOF (
	([],"!m n p. m < n ==> m < n + p"),
	GEN_TAC THEN GEN_TAC THEN
	INDUCT_TAC THEN
	REWRITE_TAC [ADD_CLAUSES] THEN
	DISCH_TAC THEN
	RES_TAC THEN
	IMP_RES_TAC LESS_SUC);;

let th6 = TAC_PROOF (
	([],"!n w. WordVal n (w:^word) < 2 EXP (SUC n)"),
	REPEAT GEN_TAC THEN
	SPEC_TAC ("n","n") THEN
	PURE_REWRITE_TAC [EXP] THEN
	INDUCT_TAC THENL
	[PURE_REWRITE_TAC [WordVal;EXP;MULT_CLAUSES] THEN
	 BOOL_CASES_TAC "(w:^word) 0" THEN
	 REWRITE_TAC [BoolVal;th1;th2];
	 PURE_REWRITE_TAC [WordVal;MULT_CLAUSES;th3] THEN
	 BOOL_CASES_TAC "(w:^word) (SUC n)" THENL
	 [ASM_REWRITE_TAC [EXP;BoolVal;MULT_CLAUSES;th4];
	  REWRITE_TAC [EXP;BoolVal;MULT_CLAUSES;ADD_CLAUSES] THEN
	  IMP_RES_TAC
	    (SPECL ["WordVal n w";"2 * (2 EXP n)";"2 * (2 EXP n)"] th5)]]);;

let th7 = ASSUME
	"((2 EXP (SUC n)) * (BoolVal(BoolAbs(cout t)))) +
	  (WordVal n(WordAbs(o t))) =
	    (WordVal n(WordAbs(i t))) + (BoolVal(BoolAbs(cin t)))";;

let th8 = SUBS [ASSUME "BoolVal(BoolAbs (cin t)) = 1"] th7;;

let th9 = MATCH_MP lemma2 (SPECL ["n";"(WordAbs (o t)):^word"] th6);;
let th10 = MATCH_MP lemma3 (SPECL ["n";"(WordAbs (o t)):^word"] th6);;

let INCn_CORRECT = prove_thm (
	`INCn_CORRECT`,
	"!n i o.
	  INCn_IMP n (i:^bus,o:^bus)
	  ==>
	  !t.
	    Defn n (i t) ==>
	      Defn n (o t) /\
	      (WordVal n (WordAbs (o t)) =
	        (((WordVal n (WordAbs (i t))) + 1) MOD (2 EXP (SUC n))))",
	PURE_REWRITE_TAC [INCn_IMP] THEN
	REPEAT STRIP_TAC THEN
	HOL_IMP_RES_THEN (STRIP_ASSUME_TAC o (SPEC "t")) lemma1 THEN
	IMP_RES_TAC HALFADDn_CORRECT THEN
	RES_TAC THEN
	SUBST1_TAC (SYM th8) THEN
	BOOL_CASES_TAC "BoolAbs (cout t)" THEN
	REWRITE_TAC [BoolVal;MULT_CLAUSES;ADD_CLAUSES] THENL
	[ACCEPT_TAC th10; ACCEPT_TAC th9]);;

close_theory ();;
