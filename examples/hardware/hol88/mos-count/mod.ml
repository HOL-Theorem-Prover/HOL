% PROOF		: Modulus Function for Natural Numbers			%
% FILE		: mod.ml						%
%									%
% DESCRIPTION	: Defines MOD function for natural numbers and proves	%
%		  the following theorem:				%
%									%
%		  !m n k. n < m ==> (n = ((k * m) + n) MOD m)		%
%									%
%		  This theorem uses the division algorithm theorem for	%
%		  natural numbers proven by T.Melham.			%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 31 March 1987						%

new_theory `mod`;;

loadt `misc`;;

new_parent `da`;;

let MOD = new_infix_definition (
	`MOD`,
	"$MOD n m = @r. ?q. (n = (q * m) + r) /\ (r < m)");;

let DA = theorem `da` `DA`;;

let lemma1 = TAC_PROOF ((
	[],
	"!m n. 0 < m ==> ?q. (n = (q * m) + (n MOD m)) /\ (n MOD m) < m"),
	REPEAT STRIP_TAC THEN
	HOL_IMP_RES_THEN (ASSUME_TAC o NOT_EQ_SYM) LESS_NOT_EQ THEN
	REWRITE_TAC [MOD;SELECT_RULE (UNDISCH_ALL (SPECL ["n";"m"] DA))]);;

let lemma2 =
	GEN_ALL
	  (SUBS [SPECL ["m";"p"] ADD_SYM;SPECL ["n";"p"] ADD_SYM]
	    (SPEC_ALL EQ_MONO_ADD_EQ));;

let lemma3 = TAC_PROOF (
	([],"!m n. (?p. p + n = m) = (n <= m)"),
	REPEAT STRIP_TAC THEN EQ_TAC THENL
	[DISCH_THEN (STRIP_THM_THEN (SUBST1_TAC o SYM)) THEN
	 SUBST1_TAC (SPECL ["p";"n"] ADD_SYM) THEN
	 REWRITE_TAC [LESS_EQ_ADD];
	 DISCH_THEN (DISJ_CASES_TAC o (PURE_REWRITE_RULE [LESS_OR_EQ])) THENL
	 [IMP_RES_TAC LESS_ADD;
	  EXISTS_TAC "0" THEN ASM_REWRITE_TAC [ADD_CLAUSES]]]);;

let th1 =
	SPECL ["n";"((p' * m) + p) + m"]
	  (INST_TYPE [":num",":*"] EQ_SYM_EQ);;
let th2 =
	CONV_RULE EXISTS_IMP_FORALL_CONV
	  (fst (EQ_IMP_RULE (SPECL ["n";"m"] lemma3)));;

let lemma4 = TAC_PROOF ((
	[],
	"!m n p q s.
	  n < m /\ p < m /\ q < s ==> ~((q * m) + n = (s * m) + p)"),
	REPEAT GEN_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
	STRIP_THM_THEN SUBST1_TAC (MATCH_MP LESS_ADD_1 (ASSUME "q < s")) THEN
	PURE_REWRITE_TAC [ADD1;RIGHT_ADD_DISTRIB] THEN
	PURE_REWRITE_TAC [lemma2;GEN_ALL (SYM (SPEC_ALL ADD_ASSOC))] THEN
	PURE_REWRITE_TAC [MULT_CLAUSES] THEN
	SUBST1_TAC (SPECL ["m";"p"] ADD_SYM) THEN
	PURE_REWRITE_TAC [ADD_ASSOC] THEN
	SUBST1_TAC th1 THEN
	STRIP_TAC THEN
	IMP_RES_TAC th2 THEN
	IMP_RES_TAC (GEN_ALL (snd (EQ_IMP_RULE (SPEC_ALL NOT_LESS)))));;

let th1 =
	PURE_REWRITE_RULE [lemma2;ASSUME "q = k"]
	  (ASSUME "(k * m) + n = (q * m) + (((k * m) + n) MOD m)");;

let lemma5 = TAC_PROOF (
	([],"!m n. m < n ==> 0 < n"),
	REPEAT STRIP_TAC THEN
	DISJ_CASES_TAC (SPEC "n" LESS_0_CASES) THENL
	[ASSUME_TAC (SUBS [SYM (ASSUME "0 = n")] (ASSUME "m < n")) THEN
	 IMP_RES_TAC NOT_LESS_0;
	 FIRST_ASSUM ACCEPT_TAC]);;

let MOD_THM = prove_thm (
	`MOD_THM`,
	"!m n k. n < m ==> (n = ((k * m) + n) MOD m)",
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC lemma5 THEN
	HOL_IMP_RES_THEN
	  STRIP_ASSUME_TAC (SPECL ["m";"(k * m) + n"] lemma1) THEN
	DISJ_CASES_TAC (SPECL ["k";"q"] LESS_CASES) THENL
	[IMP_RES_TAC lemma4;
	 DISJ_CASES_TAC
	   (PURE_REWRITE_RULE [LESS_OR_EQ] (ASSUME "q <= k")) THENL
	 [ASSUME_TAC
	    (SYM
	      (ASSUME "(k * m) + n = (q * m) + (((k * m) + n) MOD m)")) THEN
	  IMP_RES_TAC lemma4;
	  ACCEPT_TAC th1]]);;

close_theory ();;
