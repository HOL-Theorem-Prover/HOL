% ===================================================================== %
% 14 June 1989 - modified for HOL88					%
%									%
% The following bits are needed to make this proof run in HOL88.	%

set_flag (`sticky`,true);;

% =====================================================================	%
% PROOF		: More Theorems of Arithmetic				%
% FILE		: arith.ml						%
%									%
% DESCRIPTION	: Proves some general theorems of arithmetic which	%
%		  are not currently built into the system.		%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 16 July 1987						%
% =====================================================================	%

new_theory `arith`;;

let LESS_LESS_0 = prove_thm (
	`LESS_LESS_0`,
	"!m n. m < n ==> 0 < n",
	REPEAT STRIP_TAC THEN
	DISJ_CASES_TAC (SPEC "n" LESS_0_CASES) THENL
	[ASSUME_TAC (SUBS [SYM (ASSUME "0 = n")] (ASSUME "m < n")) THEN
	 IMP_RES_TAC NOT_LESS_0;
	 FIRST_ASSUM ACCEPT_TAC]);;

let LESS_EQ_LESS_TRANS = prove_thm (
	`LESS_EQ_LESS_TRANS`,
	"!m n p. m <= n /\ n < p ==> m < p",
	PURE_REWRITE_TAC [LESS_OR_EQ] THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC [] THEN
	IMP_RES_TAC LESS_TRANS);;

let LESS_ADD_LESS = prove_thm (
	`LESS_ADD_LESS`,
	"!m n. m < n ==> !p. m < p + n",
	REPEAT GEN_TAC THEN
	DISCH_TAC THEN
	INDUCT_TAC THEN
	ASM_REWRITE_TAC [ADD_CLAUSES] THEN
	IMP_RES_TAC LESS_SUC);;

let ADD_LESS_OR_EQ = prove_thm (
	`ADD_LESS_OR_EQ`,
	"!m n. (?p. p + n = m) = (n <= m)",
	REPEAT STRIP_TAC THEN EQ_TAC THENL
	[DISCH_THEN (STRIP_THM_THEN (SUBST1_TAC o SYM)) THEN
	 SUBST1_TAC (SPECL ["p";"n"] ADD_SYM) THEN
	 REWRITE_TAC [LESS_EQ_ADD];
	 DISCH_THEN (DISJ_CASES_TAC o (PURE_REWRITE_RULE [LESS_OR_EQ])) THENL
	 [IMP_RES_TAC LESS_ADD;
	  EXISTS_TAC "0" THEN ASM_REWRITE_TAC [ADD_CLAUSES]]]);;

let LESS_ADD_SUC = prove_thm (
	`LESS_ADD_SUC`,
	"!m n. n < m ==> ?p. p + (SUC n) = m",
	INDUCT_TAC THENL
	[REWRITE_TAC [NOT_LESS_0];
	 PURE_REWRITE_TAC [LESS_THM] THEN
	 REPEAT STRIP_TAC THENL
	 [EXISTS_TAC "0" THEN
	  ASM_REWRITE_TAC [ADD_CLAUSES];
	  RES_THEN (X_CHOOSE_THEN "p" (ASSUME_TAC o SYM)) THEN
	  EXISTS_TAC "SUC p" THEN
	  ASM_REWRITE_TAC [ADD_CLAUSES]]]);;

let GREATER_0_num_CASES = prove_thm (
	`GREATER_0_num_CASES`,
	"!m. 0 < m ==> ?n. m = SUC n",
	GEN_TAC THEN
	DISJ_CASES_TAC (SPEC "m" num_CASES) THEN
	ASM_REWRITE_TAC [NOT_LESS_0]);;

let SUB_ID = prove_thm (
	`SUB_ID`,
	"!m. m - m = 0",
	GEN_TAC THEN
	ASSUME_TAC (SPEC "m" LESS_EQ_REFL) THEN
	IMP_RES_TAC (snd (EQ_IMP_RULE (SPECL ["m";"m"] SUB_EQ_0))));;

let ADD_SUB = prove_thm (
	`ADD_SUB`,
	"!m n. ((m+n)-n) = m",
	let th1 =
	  GEN_ALL (DISCH_ALL (GEN "m" (SYM
	    (SUBS [SPECL ["m";"p - n"] (INST_TYPE [":num",":*"] EQ_SYM_EQ)]
	      (UNDISCH (SPEC_ALL ADD_EQ_SUB)))))) in
	let th2 =
	  SUBS [SPECL ["n";"p"] ADD_SYM] (SPECL ["n";"p"] LESS_EQ_ADD) in
	GEN_TAC THEN
	INDUCT_TAC THENL
	[REWRITE_TAC [ADD_CLAUSES;SUB_ID;SUB_0];
	 REPEAT STRIP_TAC THEN REWRITE_TAC [GEN_ALL (MATCH_MP th1 th2)]]);;

let th1 = TAC_PROOF (
	([],"!m n. m < SUC n ==> m <= n"),
	PURE_REWRITE_TAC [LESS_THM] THEN
	REPEAT STRIP_TAC THEN
	ASM_REWRITE_TAC [LESS_OR_EQ]);;

let th2 = TAC_PROOF (
	([],"!m n. m <= n ==> ~(n < m)"),
	REWRITE_TAC [NOT_LESS]);;

let ADD_SUB_ASSOC = prove_thm (
	`ADD_SUB_ASSOC`,
	"!m n. m <= n ==> !p. ((p+n)-m) = (p+(n-m))",
	GEN_TAC THEN
	INDUCT_TAC THEN
	REWRITE_TAC [LESS_OR_EQ;NOT_LESS_0] THEN
	REPEAT STRIP_TAC THENL
	[ASM_REWRITE_TAC [ADD_CLAUSES;SUB_0];
	 IMP_RES_TAC th1 THEN
	 RES_TAC THEN
	 IMP_RES_TAC th2 THEN
	 ASM_REWRITE_TAC [SUB] THEN
	 PURE_REWRITE_TAC [ADD_CLAUSES] THEN
	 ASM_REWRITE_TAC
	   [SYM (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 ADD_CLAUSES)))];
	ASM_REWRITE_TAC [SUB_ID] THEN
	REWRITE_TAC [ADD_CLAUSES;ADD_SUB]]);;

let LESS_MULT_LESS = prove_thm (
	`LESS_MULT_LESS`,
	"!m. 0 < m ==> !n p. n < p ==> n < m * p",
	GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
	INDUCT_TAC THEN
	REWRITE_TAC [NOT_LESS_0;LESS_THM] THEN
	DISCH_THEN
	  (DISJ_CASES_THENL [SUBST1_TAC;ANTE_RES_THEN ASSUME_TAC]) THENL
	[HOL_IMP_RES_THEN (CHOOSE_THEN SUBST1_TAC) GREATER_0_num_CASES THEN
	 REWRITE_TAC [MULT_CLAUSES;CONJUNCT2 ADD] THEN
	 REWRITE_TAC [MATCH_MP LESS_ADD_LESS (SPEC "p" LESS_SUC_REFL)];
	 REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES] THEN
	 REWRITE_TAC [MATCH_MP LESS_ADD_LESS (ASSUME "n < (m * p)")]]);;

let LESS_ADD_MONO = prove_thm (
	`LESS_ADD_MONO`,
	"!m n. m < n ==> !p. m < n + p",
	REPEAT GEN_TAC THEN STRIP_TAC THEN
	INDUCT_TAC THEN
	ASM_REWRITE_TAC [ADD_CLAUSES] THEN
	IMP_RES_TAC LESS_SUC);;

% adapted from M.Gordon's proof of LESS_EQ_LESS_EQ_MONO %
let LESS_LESS_MONO = prove_thm (
	`LESS_LESS_MONO`,
	"!m n p q. (m < p) /\ (n < q) ==> ((m + n) < (p + q))",
	let th1 = SPECL ["m";"p";"n"] LESS_MONO_ADD_EQ in
	let th2 = SPECL ["n";"q";"p"] LESS_MONO_ADD_EQ in
	let sublist = [SPECL ["n";"p"] ADD_SYM;SPECL ["q";"p"] ADD_SYM] in
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC (snd (EQ_IMP_RULE th1)) THEN
	IMP_RES_TAC (SUBS sublist (snd (EQ_IMP_RULE th2))) THEN
	IMP_RES_TAC (SPECL ["m+n";"p+n";"p+q"] LESS_TRANS) THEN
	ASM_REWRITE_TAC []);;

let LESS_EQ_MONO_MULT = save_thm (`LESS_EQ_MONO_MULT`,LESS_MONO_MULT);;

let LESS_MONO_MULT = prove_thm (
	`LESS_MONO_MULT`,
	"!n m. m < n ==> !p. 0 < p ==> (p * m) < (p * n)",
	REPEAT STRIP_TAC THEN
	IMP_RES_THEN (X_CHOOSE_THEN "q" SUBST1_TAC) GREATER_0_num_CASES THEN
	PURE_REWRITE_TAC [MULT_CLAUSES] THEN
	SPEC_TAC ("q","q") THEN
	INDUCT_TAC THEN
	ASM_REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES] THEN
	IMP_RES_TAC
	  (SPECL ["(q * m) + m";"m";"(q * n) + n";"n"] LESS_LESS_MONO));;

let th1 = TAC_PROOF (
	([],"!m n. m < n ==> ~(n < m)"),
	let thm = GEN_ALL (SYM (CONJUNCT1 (SPEC_ALL DE_MORGAN_THM))) in
	REWRITE_TAC [IMP_DISJ_THM;thm;LESS_ANTISYM]);;

let LESS_MONO_MULT_EQ = prove_thm (
	`LESS_MONO_MULT_EQ`,
	"!m. 0 < m ==> !n p. ((n * m) < (p * m)) = (n < p)",
	REPEAT STRIP_TAC THEN
	SUBST1_TAC (SPECL ["n";"m"] MULT_SYM) THEN
	SUBST1_TAC (SPECL ["p";"m"] MULT_SYM) THEN
	MP_TAC (REWRITE_RULE [LESS_OR_EQ] (SPECL ["n";"p"] LESS_CASES)) THEN
	STRIP_TAC THEN
	IMP_RES_TAC LESS_MONO_MULT THEN
	IMP_RES_TAC th1 THEN
	ASM_REWRITE_TAC [LESS_REFL]);;

let UNIQUE_QUOTIENT_THM = prove_thm (
	`UNIQUE_QUOTIENT_THM`,
	"!m n p. (m < n) /\ (p < n) ==>
	  !q s. (((q * n) + m) = ((s * n) + p)) ==> (q = s)",
	REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
	MP_TAC (REWRITE_RULE [LESS_OR_EQ] (SPECL ["q";"s"] LESS_CASES)) THEN
	STRIP_TAC THENL
	[X_CHOOSE_THEN "r:num"
	   (SUBST1_TAC o SYM) (MATCH_MP LESS_ADD_SUC (ASSUME "q < s")) THEN
	 PURE_REWRITE_TAC [RIGHT_ADD_DISTRIB;MULT_CLAUSES] THEN
	 SUBST1_TAC (SPECL ["r * n";"(q * n) + n"] ADD_SYM) THEN
	 PURE_REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL ADD_ASSOC))] THEN
	 SUBST1_TAC (SPECL ["q * n";"m"] ADD_SYM) THEN
	 SUBST1_TAC (SPECL ["q * n";"n + ((r * n) + p)"] ADD_SYM) THEN
	 PURE_REWRITE_TAC [EQ_MONO_ADD_EQ] THEN
	 HOL_IMP_RES_THEN
	   (\thm. REWRITE_TAC [MATCH_MP LESS_NOT_EQ (SPEC "(r * n) + p" thm)])
	   LESS_ADD_MONO;
	 X_CHOOSE_THEN "r:num"
	   (SUBST1_TAC o SYM) (MATCH_MP LESS_ADD_SUC (ASSUME "s < q")) THEN
	 PURE_REWRITE_TAC [RIGHT_ADD_DISTRIB;MULT_CLAUSES] THEN
	 SUBST1_TAC (SPECL ["r * n";"(s * n) + n"] ADD_SYM) THEN
	 PURE_REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL ADD_ASSOC))] THEN
	 SUBST1_TAC (SPECL ["s * n";"p"] ADD_SYM) THEN
	 SUBST1_TAC (SPECL ["s * n";"n + ((r * n) + m)"] ADD_SYM) THEN
	 PURE_REWRITE_TAC [EQ_MONO_ADD_EQ] THEN
	 HOL_IMP_RES_THEN
	   (\thm.
	      REWRITE_TAC
	      [NOT_EQ_SYM (MATCH_MP LESS_NOT_EQ (SPEC "(r * n) + m" thm))])
	   LESS_ADD_MONO;
	 ASM_REWRITE_TAC []]);;

let UNIQUE_REMAINDER_THM = prove_thm (
	`UNIQUE_REMAINDER_THM`,
	"!m n p. (m < n) /\ (p < n) ==>
	  !q s. (((q * n) + m) = ((s * n) + p)) ==> (m = p)",
	REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
	DISCH_THEN (\thm. ASSUME_TAC thm THEN MP_TAC thm) THEN
	IMP_RES_THEN (\thm. REWRITE_TAC [thm]) UNIQUE_QUOTIENT_THM THEN
	REWRITE_TAC [SPEC "s * n" ADD_SYM;EQ_MONO_ADD_EQ]);;

let GREATER_0_EXP = prove_thm (
	`GREATER_0_EXP`,
	"!m. 0 < m ==> !n. 0 < m EXP n",
	GEN_TAC THEN DISCH_TAC THEN
	INDUCT_TAC THEN
	REWRITE_TAC [EXP;num_CONV "1";LESS_0] THEN
	IMP_RES_TAC LESS_MULT_LESS);;

let EXP_ADD_MULT = prove_thm (
	`EXP_ADD_MULT`,
	"!m n p. m EXP (n + p) = ((m EXP n) * (m EXP p))",
	GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THEN
	REWRITE_TAC [ADD_CLAUSES;EXP;MULT_CLAUSES;EXP] THEN
	PURE_REWRITE_TAC [SYM (SPEC_ALL MULT_ASSOC)] THEN
	FIRST_ASSUM (ACCEPT_TAC o (AP_TERM "$* m") o SPEC_ALL));;

close_theory ();;
