% ===================================================================== %
% 14 June 1989 - modified for HOL88					%
%									%
% The following bits are needed to make this proof run in HOL88.	%

set_flag (`sticky`,true);;

% =====================================================================	%
% PROOF		: Division for Natural Numbers				%
% FILE		: div.ml						%
%									%
% DESCRIPTION	: Defines division for natural numbers and proves	%
%		  some useful theorems about this function including	%
%		  the following theorem:				%
%									%
%		  !m n. n < m ==> !k. (((k * m) + n) Div m) = k		%
%									%
%		  These theorems depend on the division algorithm	%
%		  theorem for natural numbers proven by T.Melham.	%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 16 July 1987						%
% =====================================================================	%

new_theory `div`;;

new_parent `da`;;
new_parent `arith`;;

let DA = theorem `da` `DA`;;

let LESS_LESS_0 = theorem `arith` `LESS_LESS_0`;;
let LESS_ADD_SUC = theorem `arith` `LESS_ADD_SUC`;;
let LESS_MONO_MULT_EQ = theorem `arith` `LESS_MONO_MULT_EQ`;;
let UNIQUE_QUOTIENT_THM = theorem `arith` `UNIQUE_QUOTIENT_THM`;;

let Div = new_infix_definition (
	`Div`,
	"$Div n m = @q. ?r. (n = (q * m) + r) /\ (r < m)");;

let EXISTS_DIV = prove_thm (
	`EXISTS_DIV`,
	"!m. 0 < m ==> !n. ?r. (n = ((n Div m) * m) + r) /\ (r < m)",
	let th1 = UNDISCH (SPEC_ALL DA) in
	let th2 = ASSUME (snd (dest_exists (concl th1))) in
	let th3 = ASSUME (snd (dest_exists (concl th2))) in
	let th4 = EXISTS (mk_exists ("r",concl th3),"r") th3 in
	let th5 = EXISTS (mk_exists ("q",concl th4),"q") th4 in
	let th6 = CHOOSE ("r",th1) (CHOOSE ("q",th2) th5) in
	let th7 = GEN_ALL (DISCH_ALL th6) in
	REPEAT STRIP_TAC THEN
	HOL_IMP_RES_THEN (ASSUME_TAC o NOT_EQ_SYM) LESS_NOT_EQ THEN
	REWRITE_TAC [Div;SELECT_RULE (UNDISCH_ALL (SPECL ["m";"n"] th7))]);;

let Div_THM = prove_thm (
	`Div_THM`,
	"!m n. n < m ==> !k. (((k * m) + n) Div m) = k",
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC LESS_LESS_0 THEN
	HOL_IMP_RES_THEN
	  (STRIP_ASSUME_TAC o (SPEC "(k * m) + n")) EXISTS_DIV THEN
	IMP_RES_THEN
	  (\thm. (ACCEPT_TAC (SYM thm)) ? ALL_TAC) UNIQUE_QUOTIENT_THM);;

let Div_MULT_LESS_EQ = prove_thm (
	`Div_MULT_LESS_EQ`,
	"!m. 0 < m ==> !n. ((n Div m) * m) <= n",
	REPEAT STRIP_TAC THEN
	HOL_IMP_RES_THEN
	  ((CHOOSE_THEN (\thm. (SUBST_OCCS_TAC [[2],CONJUNCT1 thm]))) o
	    (SPEC "n")) EXISTS_DIV THEN
	REWRITE_TAC [LESS_EQ_ADD]);;

let LESS_MULT_Div_LESS = prove_thm (
	`LESS_MULT_Div_LESS`,
	"!m. 0 < m ==> !n p. (n < (p * m)) ==> ((n Div m) < p)",
	REPEAT STRIP_TAC THEN
	HOL_IMP_RES_THEN
	  (DISJ_CASES_TAC o (REWRITE_RULE [LESS_OR_EQ]) o (SPEC "n"))
	  Div_MULT_LESS_EQ THENL
	[HOL_IMP_RES_THEN ASSUME_TAC LESS_TRANS THEN
	 IMP_RES_THEN
	   (\thm. FIRST_ASSUM (ACCEPT_TAC o (PURE_REWRITE_RULE [thm])))
	   LESS_MONO_MULT_EQ;
	 ASSUME_TAC
	   (SUBS
	     [SYM (ASSUME "(n Div m) * m = n")] (ASSUME "n < (p * m)")) THEN
	 IMP_RES_THEN
	   (\thm. FIRST_ASSUM (ACCEPT_TAC o (PURE_REWRITE_RULE [thm])))
	   LESS_MONO_MULT_EQ]);;

let LESS_Div_LESS_EQ = prove_thm (
	`LESS_Div_LESS_EQ`,
	"!m. 0 < m ==> !n p. (n < p) ==> ((n Div m) <= (p Div m))",
	PURE_REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL NOT_LESS))] THEN
	REPEAT STRIP_TAC THEN
	MP_TAC (ASSUME "n < p") THEN
	HOL_IMP_RES_THEN
	  ((X_CHOOSE_THEN "qn:num"
	    (\thm.
	      SUBST1_TAC (CONJUNCT1 thm) THEN ASSUME_TAC (CONJUNCT2 thm))) o
	    (SPEC "n")) EXISTS_DIV THEN
	HOL_IMP_RES_THEN
	  ((X_CHOOSE_THEN "qp:num"
	    (\thm.
	      SUBST1_TAC (CONJUNCT1 thm) THEN ASSUME_TAC (CONJUNCT2 thm))) o
	    (SPEC "p")) EXISTS_DIV THEN
	X_CHOOSE_THEN "q" (SUBST1_TAC o SYM)
	  (MATCH_MP LESS_ADD_SUC (ASSUME "(p Div m) < (n Div m)")) THEN
	PURE_REWRITE_TAC [ADD_CLAUSES;MULT_CLAUSES;RIGHT_ADD_DISTRIB] THEN
	PURE_REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL ADD_ASSOC))] THEN
	SUBST1_TAC (SPECL ["q * m";"((p Div m) * m) + (m + qn)"] ADD_SYM) THEN
	PURE_REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL ADD_ASSOC))] THEN
	PURE_REWRITE_TAC
	  [REWRITE_RULE [] (GEN_ALL (AP_TERM "$~" (SPEC_ALL NOT_LESS)))] THEN
	ASSUME_TAC
	  (MATCH_MP LESS_EQ_TRANS
	    (LIST_CONJ
	      [MATCH_MP LESS_IMP_LESS_OR_EQ (ASSUME "qp < m");
	       SPECL ["m";"qn + (q * m)"] LESS_EQ_ADD])) THEN
	ASSUME_TAC (SPEC "(p Div m) * m" LESS_EQ_REFL) THEN
	IMP_RES_TAC LESS_EQ_LESS_EQ_MONO THEN
	ASM_REWRITE_TAC []);;

close_theory ();;
