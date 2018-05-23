% PROOF		: Transistor Implementation of a Counter		%
% FILE		: clock.ml						%
%									%
% DESCRIPTION	: Defines predicates for a very simple version of	%
%		  two phase non-overlapping clocking and derives	%
%		  theorems about the clock behaviour.  The theory	%
%		  also uses the temporal abstraction theory to derive	%
%		  two major theorems for temporal abstraction on any	%
%		  of the four phases of the clock.			%
%									%
%		  These definitions of a two phase non-overlapping 	%
%		  clock are taken from I. Dhingra's paper, "Formal	%
%		  Validation of an Integrated Circuit Design Style",	%
%		  Hardware Verification Workshop, University of		%
%		  Calgary, January 1987.				%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 31 March 1987						%

new_theory `clock`;;

loadt `misc`;;
loadt `types`;;

new_parent `da`;;
new_parent `mos`;;
new_parent `tempabs`;;

let Shift = new_definition (
	`Shift`,
	"Shift (phi1:^wire) (phi2:^wire) = !t. phi2 (t+2) = phi1 t");;

let Invert = new_definition (
	`Invert`,
	"Invert (phi:^wire) (phibar:^wire) = !t. phibar t = Not (phi t)");;

let Cycle1 = new_definition (
	`Cycle1`,
	"Cycle1 (phi:^wire) (t:^time) =
	  (phi t = Hi) /\ (phi (t+1) = Lo) /\
	    (phi (t+2) = Lo) /\ (phi (t+3) = Lo)");;

let Cycle = new_definition (
	`Cycle`,
	"Cycle (phi:^wire) =
	  ((!t. phi (t+4) = phi t) /\
	    (Cycle1 phi 0 \/
	      Cycle1 phi 1 \/ Cycle1 phi 2 \/ Cycle1 phi 3))");;

let Clock = new_definition (
	`Clock`,
	"Clock (phi1:^wire,phi1bar:^wire,phi2:^wire,phi2bar:^wire) =
	  Cycle phi1 /\ Shift phi1 phi2 /\
	    Invert phi1 phi1bar /\ Invert phi2 phi2bar");;

let isHi = new_definition (`isHi`,"isHi phi t = (phi t = Hi)");;

let Not = definition `mos` `Not`;;
let Inf = definition `tempabs` `Inf`;;
let val_not_eq_ax = axiom `mos` `val_not_eq_ax`;;

let DA = theorem `da` `DA`;;
let Next_ADD1 = theorem `tempabs` `Next_ADD1`;;
let Next_INCREASE = theorem `tempabs` `Next_INCREASE`;;
let Next_IDENTITY = theorem `tempabs` `Next_IDENTITY`;;
let TimeOf_TRUE = theorem `tempabs` `TimeOf_TRUE`;;
let TimeOf_Next = theorem `tempabs` `TimeOf_Next`;;

let DISJ_ASSOC = TAC_PROOF (
	([],"!t1 t2 t3. t1 \/ t2 \/ t3 = (t1 \/ t2) \/ t3"),
	REPEAT GEN_TAC THEN
	BOOL_CASES_TAC "t1" THEN REWRITE_TAC [] ORELSE
	BOOL_CASES_TAC "t2" THEN REWRITE_TAC [] ORELSE
	BOOL_CASES_TAC "t3" THEN REWRITE_TAC []);;

% lemma1 = [Cycle phi] |- !t. phi(SUC(SUC(SUC(SUC t)))) = phi t %
let lemma1 = SUC_FORM_RULE (CONJUNCT1 (UNDISCH (fst (EQ_IMP_RULE Cycle))));;

let lemma2 =
	PURE_REWRITE_RULE [lemma1]
	  (SUC_FORM_RULE
	    (PURE_REWRITE_RULE [Cycle1]
	      (CONJUNCT2 (UNDISCH (fst (EQ_IMP_RULE Cycle))))));;

let lemma3 = TAC_PROOF (
	([],"!phi. Cycle phi ==> !t. (Cycle1 phi (t+4) = Cycle1 phi t)"),
	REPEAT STRIP_TAC THEN
	PURE_REWRITE_TAC [Cycle1] THEN
	PURE_REWRITE_TAC [SYM (SPECL ["t";"4";"m"] ADD_ASSOC)] THEN
	PURE_REWRITE_TAC [SPECL ["4";"m"] ADD_SYM] THEN
	PURE_REWRITE_TAC [ADD_ASSOC] THEN
	REWRITE_TAC [CONJUNCT1 (UNDISCH (fst (EQ_IMP_RULE Cycle)))]);;

let th1 = TAC_PROOF (
	([],"0 < 4"),
	SUC_FORM_TAC THEN
	ASSUME_TAC (SPEC "0" LESS_0) THEN
	REPEAT (FIRST [FIRST_ASSUM ACCEPT_TAC;IMP_RES_TAC LESS_SUC]));;

let th2 = TAC_PROOF (
	([],"!m. m < 4 ==> ((m = 0) \/ (m = 1) \/ (m = 2) \/ (m = 3))"),
	let thm =
	  GEN_ALL (SYM
	    (SUBS [SPECL ["m = n";"m < n"] DISJ_SYM] (SPEC_ALL LESS_THM)))
	in
	REPEAT STRIP_TAC THEN
	PURE_REWRITE_TAC [DISJ_ASSOC] THEN
	PURE_REWRITE_TAC
	  [GEN_ALL (REWRITE_RULE [NOT_LESS_0] (SPECL ["m";"0"] thm))] THEN
	PURE_REWRITE_TAC [thm;SYM (num_CONV "1")] THEN
	PURE_REWRITE_TAC [thm;SYM (num_CONV "2")] THEN
	PURE_REWRITE_TAC [thm;SYM (num_CONV "3")] THEN
	ASM_REWRITE_TAC [SYM (num_CONV "4")]);;

% th3 = |- !m n p. (m + n) + p = (m + p) + n %
let th3 =
	GEN_ALL
	  ((SUBS [SPECL ["n";"p"] ADD_SYM] (SYM (SPEC_ALL ADD_ASSOC)))
	    TRANS (SPECL ["m";"p";"n"] ADD_ASSOC));;

let Cycle1_ALWAYS = prove_thm (
	`Cycle1_ALWAYS`,
	"!phi.
	  Cycle phi
	  ==>
	  !t.
	    Cycle1 phi t \/
	    Cycle1 phi (t+1) \/
	    Cycle1 phi (t+2) \/
	    Cycle1 phi (t+3)",
	GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
	STRIP_ASSUME_TAC
	  (MP (SPECL ["t";"4"] DA)
	    (NOT_EQ_SYM (MATCH_MP LESS_NOT_EQ th1))) THEN
	SUBST1_TAC (ASSUME "t = (q * 4) + r") THEN
	SPEC_TAC ("q:num","q':num") THEN
	INDUCT_TAC THENL
	[PURE_REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES] THEN
	 PURE_REWRITE_TAC [Cycle1] THEN
	 SUC_FORM_TAC THEN
	 IMP_RES_TAC th2 THENL
	 (map (\tm. SUBST1_TAC (ASSUME "r = ^tm")) ["0";"1";"2";"3"]) THEN
	 SUC_FORM_TAC THEN
	 PURE_REWRITE_TAC [lemma1] THEN
	 IMP_RES_TAC (DISCH_ALL lemma2) THEN
	 ASM_REWRITE_TAC [];				% 16 cases %
	 PURE_REWRITE_TAC [MULT_CLAUSES] THEN
	 PURE_REWRITE_TAC [SPECL ["m";"4";"n"] th3] THEN
	 IMP_RES_THEN (\thm. ASM_REWRITE_TAC [thm]) lemma3]);;

let th1 =
	REWRITE_RULE
	  [lemma1;ASSUME "phi t = Hi";val_not_eq_ax]
	  (SUC_FORM_RULE
	    (PURE_REWRITE_RULE [Cycle1]
	      (SPEC_ALL (UNDISCH_ALL (SPEC_ALL Cycle1_ALWAYS)))));;

let isHi_Cycle1_ALWAYS = prove_thm (
	`isHi_Cycle1_ALWAYS`,
	"!phi t. (Cycle phi /\ isHi phi t) ==> Cycle1 phi t",
	PURE_REWRITE_TAC [isHi;Cycle1] THEN
	REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
	SUC_FORM_TAC THEN
	ASM_REWRITE_TAC [th1]);;

let num_CONVs = map num_CONV ["1";"2";"3";"4"];;
let th1 = SUC_FORM_RULE (PURE_REWRITE_RULE [Cycle1] Cycle1_ALWAYS);;

let Cycle_Inf = prove_thm (
	`Cycle_Inf`,
	"!phi. Cycle phi ==> Inf (isHi phi)",
	PURE_REWRITE_TAC [Inf;isHi;GREATER] THEN
	REPEAT STRIP_TAC THEN
	ASSUME_TAC (SPEC "t" LESS_SUC_REFL) THEN
	IMP_RES_TAC LESS_SUC THEN
	IMP_RES_TAC LESS_SUC THEN
	IMP_RES_TAC LESS_SUC THEN
	IMP_RES_TAC (hd (IMP_CANON th1)) THENL
	(map EXISTS_TAC ["t+4";"t+1";"t+2";"t+3"]) THEN
	ASM_REWRITE_TAC (num_CONVs @ [ADD_CLAUSES;lemma1]));;

let TimeOf_isHi_TRUE = prove_thm (
	`TimeOf_isHi_TRUE`,
	"!phi. Cycle phi ==> !n. (isHi phi) (TimeOf (isHi phi) n)",
	GEN_TAC THEN DISCH_TAC THEN
	IMP_RES_TAC Cycle_Inf THEN IMP_RES_TAC TimeOf_TRUE);;

let TimeOf_isHi_Next = prove_thm (
	`TimeOf_isHi_Next`,
	"!phi.
	  Cycle phi ==>
	  !n. Next (TimeOf (isHi phi) n,TimeOf (isHi phi) (n+1)) (isHi phi)",
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC Cycle_Inf THEN IMP_RES_TAC TimeOf_Next);;

% th1 = .. |- phi(SUC(SUC(SUC(SUC t)))) = Hi %
let th1 = SUBS [SYM (SPEC "t" lemma1)] (ASSUME "phi t = Hi");;
let th2 = TAC_PROOF (
	([],"!phi t. (phi t = Lo) ==> ~(phi t = Hi)"),
	REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [val_not_eq_ax]);;
let th3 =
	SUC_FORM_RULE
	  (PURE_REWRITE_RULE [isHi] (SPEC "isHi phi" Next_ADD1));;
let th4 =
	SUC_FORM_RULE
	  (PURE_REWRITE_RULE [isHi] (SPEC "isHi phi" Next_INCREASE));;

let isHi_Next_plus4 = prove_thm (
	`isHi_Next_plus4`,
	"!phi t. (Cycle phi /\ isHi phi t) ==> Next (t,t+4) (isHi phi)",
	REPEAT STRIP_TAC THEN
	SUC_FORM_TAC THEN
	IMP_RES_TAC
	  (SUC_FORM_RULE (PURE_REWRITE_RULE [Cycle1] isHi_Cycle1_ALWAYS)) THEN
	ASSUME_TAC th1 THEN
	IMP_RES_TAC th2 THEN
	IMP_RES_TAC th3 THEN
	IMP_RES_TAC th4 THEN
	IMP_RES_TAC th4 THEN
	IMP_RES_TAC th4);;

let TimeOf_isHi_Next_plus4 = prove_thm (
	`TimeOf_isHi_Next_plus4`,
	"!phi.
	  Cycle phi ==>
	  !n. Next (TimeOf (isHi phi) n,(TimeOf (isHi phi) n)+4) (isHi phi)",
	REPEAT STRIP_TAC THEN
	ASSUME_TAC
	  (SPEC "n" (MATCH_MP TimeOf_isHi_TRUE (ASSUME "Cycle phi"))) THEN
	IMP_RES_TAC isHi_Next_plus4);;

let TimeOf_isHi_plus4 = prove_thm (
	`TimeOf_isHi_plus4`,
	"!phi.
	  Cycle phi ==>
	    !n. (TimeOf (isHi phi) (n+1) = (TimeOf (isHi phi) n)+4)",
	REPEAT STRIP_TAC THEN
	ASSUME_TAC
	  (SPEC "n" (MATCH_MP TimeOf_isHi_Next (ASSUME "Cycle phi"))) THEN
	ASSUME_TAC
	  (SPEC "n"
	    (MATCH_MP TimeOf_isHi_Next_plus4 (ASSUME "Cycle phi"))) THEN
	IMP_RES_TAC Next_IDENTITY);;

let th1 =
	SUC_FORM_RULE
	  (PURE_REWRITE_RULE [Cycle1] (ASSUME "Cycle1 phi1 t"));;
let th2 =
	SUC_FORM_RULE
	  (SUBS (CONJUNCTS th1)
	    (SPEC "t"
	      (CONJUNCT1
	        (PURE_REWRITE_RULE [Cycle] (ASSUME "Cycle phi1")))));;
let th3 = PURE_REWRITE_RULE [Invert] (ASSUME "Invert phi1 phi1bar");;
let th4 = PURE_REWRITE_RULE [Invert] (ASSUME "Invert phi2 phi2bar");;
let th5 =
	SUC_FORM_RULE
	  (PURE_REWRITE_RULE [Shift] (ASSUME "Shift phi1 phi2"));;

let ClockSignals = prove_thm (
	`ClockSignals`,
	"!phi1 phi1bar phi2 phi2bar t.
	  (Clock (phi1,phi1bar,phi2,phi2bar) /\ (isHi phi1 t))
	  ==>
	  (phi1    t     = Hi) /\ (phi1    (t+1) = Lo) /\
	  (phi1    (t+2) = Lo) /\ (phi1    (t+3) = Lo) /\
	  (phi1    (t+4) = Hi) /\
	  (phi1bar (t+1) = Hi) /\ (phi1bar (t+2) = Hi) /\
	  (phi1bar (t+3) = Hi) /\ (phi1bar (t+4) = Lo) /\
	  (phi2    (t+2) = Hi) /\ (phi2    (t+3) = Lo) /\
	  (phi2    (t+4) = Lo) /\
	  (phi2bar (t+3) = Hi) /\ (phi2bar (t+4) = Hi)",
	PURE_REWRITE_TAC [Clock] THEN
	REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
	IMP_RES_TAC isHi_Cycle1_ALWAYS THEN
	SUC_FORM_TAC THEN
	REWRITE_TAC [th1;th2;th3;th4;th5;Not;val_not_eq_ax]);;
%
|- !phi1 phi1bar phi2 phi2bar.
    Clock(phi1,phi1bar,phi2,phi2bar) ==> Cycle phi1
%
let Clock_Cycle = save_thm (
	`Clock_Cycle`,
	GEN_ALL (DISCH_ALL (CONJUNCT1 (UNDISCH (fst (EQ_IMP_RULE Clock))))));;

close_theory ();;
