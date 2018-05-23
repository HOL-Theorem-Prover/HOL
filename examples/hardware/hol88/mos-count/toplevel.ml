% PROOF		: Transistor Implementation of a Counter		%
% FILE		: toplevel.ml						%
%									%
% DESCRIPTION	: Top-level implementation using the counter and	%
%		  some I/0 devices.					%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 1 April 1987						%

new_theory `toplevel`;;

loadt `misc`;;
loadt `types`;;

new_parent `count`;;

let BUTTON = new_definition (
	`BUTTON`,
	"BUTTON (g:^wire,i:^boolsig,o:^wire) =
	  (!t. Def ((o when (isHi g)) t)) /\
	  (!t. (i t = BoolAbs ((o when (isHi g)) t)))");;

let SWITCHES = new_definition (
	`SWITCHES`,
	"SWITCHES n (g:^wire,i:^numsig,o:^bus) =
	  (!t. Defn n ((o when (isHi g)) t)) /\
	  (!t. (i t = WordVal n (WordAbs ((o when (isHi g)) t))))");;

let DISPLAY = new_definition (
	`DISPLAY`,
	"DISPLAY n (g:^wire,i:^bus,o:^numsig) =
	  !t.
	    Defn n ((i when (isHi g)) t) ==>
	    (o t = WordVal n (WordAbs ((i when (isHi g)) t)))");;

let DEVICE_IMP = new_definition (
	`DEVICE_IMP`,
	"DEVICE_IMP n (button:^boolsig,switches:^numsig,display:^numsig) =
	  ?phiA w1 b1 b2.
	    BUTTON (phiA,button,w1) /\
	    SWITCHES n (phiA,switches,b1) /\
	    DISPLAY n (phiA,b2,display) /\
	    COUNT_IMP n (phiA,w1,b1,b2) /\
	    isBus n b1 /\
	    isBus n b2");;

let Def_DISJ_CASES = theorem `dataabs` `Def_DISJ_CASES`;;
let BoolAbs_THM = theorem `dataabs` `BoolAbs_THM`;;
let COUNT_CORRECT = theorem `count` `COUNT_CORRECT2`;;

let LESS_OR_EQ_ADD = TAC_PROOF(
	([],"!m n. m <= n = (?p. p + m = n)"),
	REPEAT GEN_TAC THEN
	EQ_TAC THENL
	[PURE_REWRITE_TAC [LESS_OR_EQ] THEN
	 REPEAT STRIP_TAC THENL
	 [IMP_RES_TAC LESS_ADD;
	  EXISTS_TAC "0" THEN ASM_REWRITE_TAC [ADD_CLAUSES]];
	 REPEAT STRIP_TAC THEN
	 FIRST_ASSUM (SUBST1_TAC o SYM) THEN
	 SUBST1_TAC (SPECL ["p";"m"] ADD_SYM) THEN
	 REWRITE_TAC [LESS_EQ_ADD]]);;

let ASSUM_LIST_SPEC_TAC tm =
	ASSUM_LIST (MAP_EVERY
	    (\thm.
	      if not (is_forall (concl thm)) then ALL_TAC
	      else let var = fst (dest_forall (concl thm)) in
	      if not (type_of tm = type_of var) then ALL_TAC
	      else ASSUME_TAC (SPEC tm thm) ?
	      failwith `ASSUM_LIST_SPEC_TAC`));;

let lemma1 = TAC_PROOF ((
	[],
	"!w t.
	  Def (w t) ==> (b t = BoolAbs (w t)) ==> (b t = T) ==> (w t = Hi)"),
	REPEAT GEN_TAC THEN
	DISCH_THEN (STRIP_THM_THEN SUBST1_TAC o(MATCH_MP Def_DISJ_CASES)) THEN
	DISCH_THEN SUBST1_TAC THEN REWRITE_TAC [BoolAbs_THM]);;

let lemma2 =
	GEN_ALL
	  (SUBS [SPECL ["m";"n"] ADD_SYM] (SPECL ["m";"n"] LESS_EQ_ADD));;

let th1 = CONJUNCT1 (CONJUNCT2 (CONJUNCT2 ADD_CLAUSES));;
let th2 = (DEPTH_CONV (REWRITE_CONV th1)) "((SUC n') + sysinit)";;
let th3 = SYM (TRANS th2 ((REWRITE_CONV ADD1) (rhs (concl th2))));;
let th4 = ASSUME
	"display((n' + sysinit) + 1) =
	  WordVal n(WordAbs((b2 when (isHi phiA))((n' + sysinit) + 1)))";;
let th5 = SUBS [th3] th4;;

let TOPLEVEL_CORRECT = prove_thm (
	`TOPLEVEL_CORRECT`,
	"!n.
	  let max = 2 EXP (n + 1) in
	    !button switches display sysinit.
	      DEVICE_IMP n (button,switches,display) /\
	      (button sysinit = T)
	      ==>
	      !t. sysinit <= t ==>
	        (display (t + 1) =
	          button t => switches t | (((display t) + 1) MOD max))",
	GEN_TAC THEN
	SUBST1_TAC (SYM (SPEC "n" ADD1)) THEN
	PURE_REWRITE_TAC [LET_DEF;DEVICE_IMP;BUTTON;SWITCHES;DISPLAY] THEN
	BETA_TAC THEN
	REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
	PURE_REWRITE_TAC [LESS_OR_EQ_ADD] THEN
	DISCH_THEN (STRIP_THM_THEN (SUBST1_TAC o SYM)) THEN
	ASSUM_LIST_SPEC_TAC "sysinit" THEN
	IMP_RES_TAC lemma1 THEN
	DISJ_CASES_THENL
	  [SUBST1_TAC;STRIP_THM_THEN SUBST1_TAC] (SPEC "p" num_CASES) THENL
	[PURE_REWRITE_TAC [ADD_CLAUSES] THEN
	 ASSUME_TAC (SPEC "sysinit" LESS_EQ_REFL) THEN
	 IMP_RES_TAC COUNT_CORRECT THEN
	 RES_TAC THEN
	 ASM_REWRITE_TAC [BoolAbs_THM];
	 ASSUME_TAC (SPECL ["sysinit";"n'"] lemma2) THEN
	 ASSUME_TAC (SPECL ["sysinit";"SUC n'"] lemma2) THEN
	 IMP_RES_TAC COUNT_CORRECT THEN
	 RES_TAC THEN
	 ASM_REWRITE_TAC [] THEN
	 SUBST1_TAC th5 THEN
	 ASM_REWRITE_TAC []]);;

close_theory ();;
