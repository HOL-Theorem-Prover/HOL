% PROOF		: Transistor Implementation of a Counter		%
% FILE		: gates.ml						%
%									%
% DESCRIPTION	: Defines CMOS implementations of basic gates used	%
%		  in the increment unit circuit and derives boolean	%
%		  behaviours.						%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 31 March 1987						%

new_theory `gates`;;

loadt `misc`;;
loadt `types`;;

new_parent `dataabs`;;

let inv = new_definition (`inv`,"inv i = ~i");;
let nand = new_definition (`nand`,"nand (i1,i2) = ~(i1 /\ i2)");;
let and = new_definition (`and`,"and (i1,i2) = (i1 /\ i2)");;
let xor = new_definition (`xor`,"xor (i1,i2) = (i1 /\ ~i2) \/ (~i1 /\ i2)");;

let INV_IMP = new_definition (
	`INV_IMP`,
	"INV_IMP (i:^wire,o:^wire) =
	  ?w1 w2 w3 w4.
	    Vdd (w1) /\
	    Ptran (i,w1,w2) /\
	    Join (w2,w3,o) /\
	    Ntran (i,w4,w3) /\
	    Gnd (w4)");;

let NAND_IMP = new_definition (
	`NAND_IMP`,
	"NAND_IMP (i1:^wire,i2:^wire,o:^wire) =
	  ?w1 w2 w3 w4 w5 w6 w7.
	    Vdd (w1) /\
	    Ptran (i1,w1,w2) /\
	    Ptran (i2,w1,w3) /\
	    Join (w2,w3,w4) /\
	    Join (w4,w5,o) /\
	    Ntran (i1,w6,w5) /\
	    Ntran (i2,w7,w6) /\
	    Gnd (w7)");;

let AND_IMP = new_definition (
	`AND_IMP`,
	"AND_IMP (i1:^wire,i2:^wire,o:^wire) =
	  ?w. NAND_IMP (i1,i2,w) /\ INV_IMP (w,o)");;

let XOR_IMP = new_definition (
	`XOR_IMP`,
	"XOR_IMP (i1:^wire,i2:^wire,o:^wire) =
	  ?w1 w2 w3.
	    NAND_IMP (i1,i2,w1) /\
	    NAND_IMP (i1,w1,w2) /\
	    NAND_IMP (i2,w1,w3) /\
	    NAND_IMP (w2,w3,o)");;

let val_not_eq_ax = axiom `mos` `val_not_eq_ax`;;

let U = definition `mos` `U`;;
let Not = definition `mos` `Not`;;
let Vdd = definition `mos` `Vdd`;;
let Gnd = definition `mos` `Gnd`;;
let Ptran = definition `mos` `Ptran`;;
let Ntran = definition `mos` `Ntran`;;
let Join = definition `mos` `Join`;;
let Def = definition `dataabs` `Def`;;
let BoolAbs_THM = theorem `dataabs` `BoolAbs_THM`;;
let Def_DISJ_CASES = theorem `dataabs` `Def_DISJ_CASES`;;

let INV_CORRECT = prove_thm (
	`INV_CORRECT`,
	"!i o.
	  INV_IMP (i,o)
	  ==>
	  !t.
	    Def (i t) ==>
	      Def (o t) /\ (BoolAbs (o t) = inv (BoolAbs (i t)))",
	let th1 = EXPANDF [Vdd;Gnd;Ptran;Ntran;Join] INV_IMP
	in
	PURE_REWRITE_TAC [th1] THEN
	REPEAT STRIP_TAC THEN
	PURE_REWRITE_TAC [Def] THEN
	IMP_RES_TAC Def_DISJ_CASES THEN
	ASM_REWRITE_TAC [val_not_eq_ax;U;BoolAbs_THM;inv]);;

let NAND_CORRECT = prove_thm (
	`NAND_CORRECT`,
	"!i1 i2 o.
	  NAND_IMP (i1,i2,o)
	  ==>
	  !t.
	    Def (i1 t) /\ Def (i2 t) ==>
	      Def (o t) /\
	        (BoolAbs (o t) = nand (BoolAbs (i1 t),BoolAbs (i2 t)))",
	let th1 = EXPANDF [Vdd;Gnd;Ptran;Ntran;Join] NAND_IMP
	in
	PURE_REWRITE_TAC [th1] THEN
	REPEAT STRIP_TAC THEN
	PURE_REWRITE_TAC [Def] THEN
	IMP_RES_TAC Def_DISJ_CASES THEN
	ASM_REWRITE_TAC [val_not_eq_ax;U;BoolAbs_THM;nand]);;

let AND_CORRECT = prove_thm (
	`AND_CORRECT`,
	"!i1 i2 o.
	  AND_IMP (i1,i2,o)
	  ==>
	  !t.
	    Def (i1 t) /\ Def (i2 t) ==>
	      Def (o t) /\
	        (BoolAbs (o t) = and (BoolAbs (i1 t),BoolAbs (i2 t)))",
	PURE_REWRITE_TAC [AND_IMP] THEN
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC NAND_CORRECT THEN
	RES_TAC THEN
	IMP_RES_TAC INV_CORRECT THEN
	RES_TAC THEN
	ASM_REWRITE_TAC [nand;inv;and]);;

let XOR_CORRECT = prove_thm (
	`XOR_CORRECT`,
	"!i1 i2 o.
	  XOR_IMP (i1,i2,o)
	  ==>
	  !t.
	    Def (i1 t) /\ Def (i2 t) ==>
	      Def (o t) /\
	        (BoolAbs (o t) = xor (BoolAbs (i1 t),BoolAbs (i2 t)))",
	PURE_REWRITE_TAC [XOR_IMP] THEN
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC NAND_CORRECT THEN
	RES_TAC THEN
	ASM_REWRITE_TAC [] THEN
	BOOL_CASES_TAC "BoolAbs (i1 t)" THEN
	BOOL_CASES_TAC "BoolAbs (i2 t)" THEN
	REWRITE_TAC [nand;xor]);;

close_theory ();;
