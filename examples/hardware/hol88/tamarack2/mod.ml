% ===================================================================== %
% 14 June 1989 - modified for HOL88					%
%									%
% The following bits are needed to make this proof run in HOL88.	%

set_flag (`sticky`,true);;
let MOD =
	SPEC_ALL
	  (PURE_REWRITE_RULE [
	    SPECL ["m+n";"p:num"] (INST_TYPE [":num",":*"] EQ_SYM_EQ)] MOD);;

% =====================================================================	%
% PROOF		: Modulus Function for Natural Numbers			%
% FILE		: mod.ml						%
%									%
% DESCRIPTION	: Defines MOD function for natural numbers and proves	%
%		  some useful theorems about this function, including	%
%		  the following theorem:				%
%									%
%		  !m n. n < m ==> !k. (((k * m) + n) MOD m) = n		%
%									%
%		  These theorems depend on the division algorithm	%
%		  theorem for natural numbers proven by T.Melham.	%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 16 July 1987						%
% =====================================================================	%

new_theory `mod`;;

new_parent `da`;;
new_parent `arith`;;

% =====================================================================	%
% 89-June-14: MOD already defined in HOL88 				%
% let MOD = new_infix_definition (					%
%	`MOD`,								%
%	"$MOD n m = @r. ?q. (n = (q * m) + r) /\ (r < m)");;		%

let DA = theorem `da` `DA`;;

let ADD_SUB = theorem `arith` `ADD_SUB`;;
let LESS_LESS_0 = theorem `arith` `LESS_LESS_0`;;
let ADD_SUB_ASSOC = theorem `arith` `ADD_SUB_ASSOC`;;
let ADD_LESS_OR_EQ = theorem `arith` `ADD_LESS_OR_EQ`;;
let UNIQUE_REMAINDER_THM = theorem `arith` `UNIQUE_REMAINDER_THM`;;

let EXISTS_MOD = prove_thm (
	`EXISTS_MOD`,
	"!m. 0 < m ==> !n. ?q. (n = (q * m) + (n MOD m)) /\ (n MOD m) < m",
	REPEAT STRIP_TAC THEN
	HOL_IMP_RES_THEN (ASSUME_TAC o NOT_EQ_SYM) LESS_NOT_EQ THEN
	REWRITE_TAC [MOD;SELECT_RULE (UNDISCH_ALL (SPECL ["n";"m"] DA))]);;

let MOD_THM = prove_thm (
	`MOD_THM`,
	"!m n. n < m ==> !k. ((((k * m) + n) MOD m) = n)",
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC LESS_LESS_0 THEN
	HOL_IMP_RES_THEN
	  (STRIP_ASSUME_TAC o (SPEC "(k * m) + n")) EXISTS_MOD THEN
	IMP_RES_THEN
	  (\thm. (ACCEPT_TAC (SYM thm)) ? ALL_TAC) UNIQUE_REMAINDER_THM);;

let MOD_ONE_THM = prove_thm (
	`MOD_ONE_THM`,
	"!m. m MOD 1 = 0",
	GEN_TAC THEN
	SUBST1_TAC (SYM (CONJUNCT1 (CONJUNCT2
	  (CONJUNCT2 (CONJUNCT2 (SPEC_ALL MULT_CLAUSES)))))) THEN
	SUBST1_TAC (SYM (CONJUNCT1
	  (CONJUNCT2 (SPEC "m * 1" (GEN "m" ADD_CLAUSES))))) THEN
	REWRITE_TAC
	  [REWRITE_RULE [LESS_0]
	    (SUBS_OCCS [[1],num_CONV "1"] (SPECL ["1";"0"] MOD_THM))]);;

let LESS_MOD_THM = prove_thm (
	`LESS_MOD_THM`,
	"!m n. n < m ==> ((n MOD m) = n)",
	REPEAT STRIP_TAC THEN
	HOL_IMP_RES_THEN
	  (ACCEPT_TAC o
	    (REWRITE_RULE [MULT_CLAUSES;ADD_CLAUSES]) o (SPEC "0")) MOD_THM);;

let MOD_LESS_THM = prove_thm (
	`MOD_LESS_THM`,
	"!m. 0 < m ==> !n. (n MOD m) < m",
	REPEAT STRIP_TAC THEN
	HOL_IMP_RES_THEN (STRIP_ASSUME_TAC o (SPEC "n")) EXISTS_MOD);;

let MOD_LESS_EQ = prove_thm (
	`MOD_LESS_EQ`,
	"!m. 0 < m ==> !n. (n MOD m) <= n",
	REPEAT STRIP_TAC THEN
	IMP_RES_THEN
	  ((X_CHOOSE_THEN "q"
	    (\thm. SUBST_OCCS_TAC [[2],CONJUNCT1 thm])) o (SPEC "n"))
	  EXISTS_MOD THEN
	SUBST1_TAC (SPECL ["q * m";"n MOD m"] ADD_SYM) THEN
	REWRITE_TAC [LESS_EQ_ADD]);;

let MULT_MOD_0 = prove_thm (
	`MULT_MOD_0`,
	"!m. 0 < m ==> !n. ((n * m) MOD m) = 0",
	REPEAT STRIP_TAC THEN
	SUBST1_TAC
	  (SYM
	    (SPEC "n * m" (GEN "m" (CONJUNCT1 (CONJUNCT2 ADD_CLAUSES))))) THEN
	IMP_RES_THEN (\thm. REWRITE_TAC [thm]) MOD_THM);;

let MOD_MOD_THM = prove_thm (
	`MOD_MOD_THM`,
	"!m. 0 < m ==> !n. ((n MOD m) MOD m) = (n MOD m)",
	REPEAT STRIP_TAC THEN
	HOL_IMP_RES_THEN (ASSUME_TAC o (SPEC "n")) MOD_LESS_THM THEN
	HOL_IMP_RES_THEN (ASSUME_TAC o (SPEC "0")) MOD_THM THEN
	FIRST_ASSUM
	  (ACCEPT_TAC o (REWRITE_RULE [MULT_CLAUSES;ADD_CLAUSES])));;

let MOD_CONGRUENCE_THM = prove_thm (
	`MOD_CONGRUENCE_THM`,
	"!m. 0 < m ==> !n k. ((k * m) + n) MOD m = n MOD m",
	REPEAT STRIP_TAC THEN
	HOL_IMP_RES_THEN
	  ((X_CHOOSE_THEN "q:num"
	    (\thm. SUBST_OCCS_TAC [[1],CONJUNCT1 thm])) o (SPEC "n"))
	  EXISTS_MOD THEN
	REWRITE_TAC
	  [ADD_ASSOC;GEN_ALL (SYM (SPEC_ALL RIGHT_ADD_DISTRIB))] THEN
	HOL_IMP_RES_THEN
	  (\thm.
	    REWRITE_TAC [MATCH_MP MOD_THM (SPEC "n" thm)]) MOD_LESS_THM);;

let MOD_ADD_THM = prove_thm (
	`MOD_ADD_THM`,
	"!m. 0 < m ==>
	  !n p. (((n MOD m) + (p MOD m)) MOD m) = ((n + p) MOD m)",
	REPEAT STRIP_TAC THEN
	HOL_IMP_RES_THEN
	  ((X_CHOOSE_THEN "qn:num"
	    (\thm. SUBST_OCCS_TAC [[2],CONJUNCT1 thm])) o (SPEC "n"))
	  EXISTS_MOD THEN
	HOL_IMP_RES_THEN
	  ((X_CHOOSE_THEN "qp:num"
	    (\thm. SUBST_OCCS_TAC [[2],CONJUNCT1 thm])) o (SPEC "p"))
	  EXISTS_MOD THEN
	PURE_REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL ADD_ASSOC))] THEN
	IMP_RES_THEN (\thm. PURE_REWRITE_TAC [thm]) MOD_CONGRUENCE_THM THEN
	PURE_REWRITE_TAC [ADD_ASSOC] THEN
	SUBST1_TAC (SPECL ["n MOD m";"qp * m"] ADD_SYM) THEN
	PURE_REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL ADD_ASSOC))] THEN
	IMP_RES_THEN (\thm. REWRITE_TAC [thm]) MOD_CONGRUENCE_THM);;

let MOD_SUB_THM = prove_thm (
	`MOD_SUB_THM`,
	"!m n p. (0 < m /\ p <= n MOD m) ==>
	  ((((n MOD m) - p) MOD m) = ((n - p) MOD m))",
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC LESS_LESS_0 THEN
	HOL_IMP_RES_THEN
	  ((X_CHOOSE_THEN "qn:num"
	    (\thm. SUBST_OCCS_TAC [[2],CONJUNCT1 thm])) o (SPEC "n"))
	  EXISTS_MOD THEN
	HOL_IMP_RES_THEN (\thm. PURE_REWRITE_TAC [thm]) ADD_SUB_ASSOC THEN
	IMP_RES_THEN (\thm. REWRITE_TAC [thm]) MOD_CONGRUENCE_THM);;

% =====================================================================	%
% MOD_SUB_THM is a special case of a more general theorem relating	%
% subtraction and modulus but its proof depends on several unproven	%
% subtraction theorems (which aren't too hard but I don't have time	%
% to prove them now).  Here is the general theorem and a tactic for	%
% proving it but the required subtraction theorems are just assumed.	%
% ===================================================================== %

let SUB_lemma1 = ASSUME "!m n p. (m-(n+p)) = ((m-n)-p)";;
let SUB_lemma2 = ASSUME "!m n. m <= n ==> !p. ((n+p)-m) = ((n-m)+p)";;
let SUB_lemma3 = ASSUME "!m n p. ((m*n)-(p*n)) = ((m-p)*n)";;

TAC_PROOF ((
	(hyp (LIST_CONJ [SUB_lemma1;SUB_lemma2;SUB_lemma3])),
	"!m. 0 < m ==>
	  !n p.
	    ((p MOD m) <= (n MOD m)) /\
	      ((p - (p MOD m)) <= (n - (n MOD m))) ==>
	    ((((n MOD m) - (p MOD m)) MOD m) = ((n - p) MOD m))"),
	GEN_TAC THEN
	STRIP_TAC THEN
	REPEAT GEN_TAC THEN
	HOL_IMP_RES_THEN
	  ((X_CHOOSE_THEN "qn:num"
	    (\thm. SUBST_OCCS_TAC [[2;5],CONJUNCT1 thm])) o (SPEC "n"))
	  EXISTS_MOD THEN
	HOL_IMP_RES_THEN
	  ((X_CHOOSE_THEN "qp:num"
	    (\thm. SUBST_OCCS_TAC [[2;5],CONJUNCT1 thm])) o (SPEC "p"))
	  EXISTS_MOD THEN
	PURE_REWRITE_TAC [ADD_SUB] THEN
	STRIP_TAC THEN
	PURE_REWRITE_TAC [SUB_lemma1] THEN
	HOL_IMP_RES_THEN (\thm. PURE_REWRITE_TAC [thm]) SUB_lemma2 THEN
	PURE_REWRITE_TAC [SUB_lemma3] THEN
	HOL_IMP_RES_THEN (\thm. PURE_REWRITE_TAC [thm]) ADD_SUB_ASSOC THEN
	IMP_RES_THEN (\thm. REWRITE_TAC [thm]) MOD_CONGRUENCE_THM);;

close_theory ();;
