% PROOF		: Transistor Implementation of a Counter		%
% FILE		: muxn.ml						%
%									%
% DESCRIPTION	: Defines a CMOS Mux and uses this to construct a	%
%		  n-bit Mux.  Only the control line is abstracted	%
%		  to a boolean signal.					%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 31 March 1987						%

new_theory `muxn`;;

loadt `misc`;;
loadt `types`;;

new_parent `gates`;;

let mux = new_definition (`mux`,"mux (cntl,i1:*,i2:*) = cntl => i1 | i2");;

let CMUX_IMP = new_definition (
	`CMUX_IMP`,
	"CMUX_IMP (cntl:^wire,cntlbar:^wire,i1:^wire,i2:^wire,o:^wire) =
	  ?w1 w2 w3 w4 w5 w6.
	    Ptran (cntlbar,i1,w1) /\
	    Ntran (cntl,i1,w2) /\
	    Join (w1,w2,w3) /\
	    Join (w3,w4,o) /\
	    Join (w5,w6,w4) /\
	    Ptran (cntl,i2,w5) /\
	    Ntran (cntlbar,i2,w6)");;

let CMUXn_IMP = new_definition (
	`CMUXn_IMP`,
	"CMUXn_IMP n (cntl:^wire,cntlbar:^wire,i1:^bus,i2:^bus,o:^bus) =
	  !m. m <= n ==>
	    CMUX_IMP
	      (cntl,cntlbar,DEST_BUS i1 m,DEST_BUS i2 m,DEST_BUS o m)");;

let MUXn_IMP = new_definition (
	`MUXn_IMP`,
	"MUXn_IMP n (cntl:^wire,i1:^bus,i2:^bus,o:^bus) =
	  ?cntlbar.
	    INV_IMP (cntl,cntlbar) /\ CMUXn_IMP n (cntl,cntlbar,i1,i2,o)");;

let U = definition `mos` `U`;;
let Vdd = definition `mos` `Vdd`;;
let Gnd = definition `mos` `Gnd`;;
let Ptran = definition `mos` `Ptran`;;
let Ntran = definition `mos` `Ntran`;;
let Join = definition `mos` `Join`;;
let Not = definition `mos` `Not`;;
let Def = definition `dataabs` `Def`;;
let DEST_BUS = definition `dataabs` `DEST_BUS`;;
let INV_IMP = definition `gates` `INV_IMP`;;

let val_not_eq_ax = axiom `mos` `val_not_eq_ax`;;

let Def_DISJ_CASES = theorem `dataabs` `Def_DISJ_CASES`;;
let BoolAbs_THM = theorem `dataabs` `BoolAbs_THM`;;
let isBus_THM = theorem `dataabs` `isBus_THM`;;

let lemma1 = TAC_PROOF ((
	  [],
	  "(!t1:*. !t2:*. (((t1 = t2) => t1 | t1) = t1)) /\
	   (!t1:*. !t2:*. (((t1 = t2) => t2 | t2) = t2)) /\
	   (!t1:*. !t2:*. (((t1 = t2) => t1 | t2) = t2)) /\
	   (!t1:*. !t2:*. (((t1 = t2) => t2 | t1) = t1))"),
	let thm = SYM (CONJUNCT2(CONJUNCT2(CONJUNCT2 (SPEC_ALL EQ_CLAUSES))))
	in
	REPEAT STRIP_TAC THEN
	DISJ_CASES_TAC (SPEC "t1 = t2" EXCLUDED_MIDDLE) THEN
	IMP_RES_TAC thm THEN
	ASM_REWRITE_TAC []);;

let CMUX_CORRECT = prove_thm (
	`CMUX_CORRECT`,
	"!cntl cntlbar i1 i2 o.
	  CMUX_IMP (cntl,cntlbar,i1,i2,o)
	  ==>
	  !t.
	    Def (cntl t) /\ (cntlbar t = Not (cntl t))
	    ==>
	    (o t = mux (BoolAbs (cntl t),i1 t,i2 t))",
	PURE_REWRITE_TAC [EXPANDF [Ptran;Ntran;Join] CMUX_IMP] THEN
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC Def_DISJ_CASES THEN
	ASM_REWRITE_TAC [Not;mux;U;val_not_eq_ax;BoolAbs_THM;lemma1]);;

let CMUXn_CORRECT = prove_thm (
	`CMUXn_CORRECT`,
	"!n cntl cntlbar i1 i2 o.
	  CMUXn_IMP n (cntl,cntlbar,i1,i2,o) /\
	  isBus n i1 /\
	  isBus n i2 /\
	  isBus n o
	  ==>
	  !t.
	    Def (cntl t) /\ (cntlbar t = Not (cntl t))
	    ==>
	    (o t = mux (BoolAbs (cntl t),i1 t,i2 t))",
	PURE_REWRITE_TAC [CMUXn_IMP;mux] THEN
	REPEAT STRIP_TAC THEN
	COND_CASES_TAC THEN
	IMP_RES_TAC isBus_THM THEN
	ASM_REWRITE_TAC [] THEN
	REPEAT STRIP_TAC THEN
	RES_TAC THEN
	HOL_IMP_RES_THEN
	  (ASSUME_TAC o BETA_RULE o PURE_REWRITE_RULE [DEST_BUS])
	  CMUX_CORRECT THEN
	RES_TAC THEN
	ASM_REWRITE_TAC [mux]);;

let th1 = TAC_PROOF (
	([],"!i o. INV_IMP (i,o) ==> !t. Def (i t) ==> (o t = Not (i t))"),
	PURE_REWRITE_TAC [EXPANDF [Vdd;Gnd;Ptran;Ntran;Join] INV_IMP] THEN
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC Def_DISJ_CASES THEN
	ASM_REWRITE_TAC [Not;U;val_not_eq_ax]);;

let MUXn_CORRECT = prove_thm (
	`MUXn_CORRECT`,
	"!n cntl i1 i2 o.
	  MUXn_IMP n (cntl,i1,i2,o) /\
	  isBus n i1 /\
	  isBus n i2 /\
	  isBus n o
	  ==>
	  !t. Def (cntl t) ==> (o t = mux (BoolAbs (cntl t),i1 t,i2 t))",
	PURE_REWRITE_TAC [MUXn_IMP] THEN
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC th1 THEN
	IMP_RES_TAC CMUXn_CORRECT THEN
	RES_TAC);;

close_theory ();;
