% =====================================================================	%
% Jeff Joyce, 14 June 1989						%
%									%
% Division Algorithm Theorem.						%
% First show that a "r" and "q" exists and then use WOP.		%
% (see D. Burton, Elementary Number Theory, Allyn and Bacon, 1976)	%

new_theory `da`;;

new_parent `wop`;;

let WOP = theorem `wop` `WOP`;;

let th1 = TAC_PROOF (
	([],"!a b. ?r q. a = (q * b) + r"),
	REPEAT STRIP_TAC THEN
	EXISTS_TAC "a:num" THEN
	EXISTS_TAC "0" THEN
	REWRITE_TAC [ADD_CLAUSES;MULT_CLAUSES]);;

let th2 =
	CONV_RULE EXISTS_IMP_FORALL_CONV
	  (BETA_RULE (SPEC "\r. ?q. a = (q*b) + r" WOP));;

let th3 = TAC_PROOF (
	([],"!m n. n <= m ==> ?p. m = n + p"),
	PURE_ONCE_REWRITE_TAC [LESS_OR_EQ;EQ_SYM_EQ] THEN
	REPEAT STRIP_TAC THENL [
	  IMP_RES_TAC (PURE_ONCE_REWRITE_RULE [ADD_SYM] LESS_ADD);
	  EXISTS_TAC "0" THEN ASM_REWRITE_TAC [ADD_CLAUSES]]);;

let th4 = TAC_PROOF (
	([],"!m n p. ((n = m + p) /\ 0 < m) ==> p < n"),
	REPEAT STRIP_TAC THEN
	DISJ_CASES_THENL [ACCEPT_TAC;MP_TAC]
	  (SPECL ["p:num";"n:num"] LESS_CASES) THEN
	ASSUM_LIST (SUBST_TAC o (filter (is_eq o concl))) THEN
	REWRITE_TAC
	  [REWRITE_RULE [ADD] (SPECL ["m:num";"0"] LESS_EQ_MONO_ADD_EQ)] THEN
	DISCH_TAC THEN
	IMP_RES_TAC LESS_EQ_ANTISYM);;

let th5 = TAC_PROOF (
	([],"!n. (~(n = 0)) = 0 < n"),
	GEN_TAC THEN
	DISJ_CASES_THENL [SUBST1_TAC;CHOOSE_THEN SUBST1_TAC]
	  (SPEC "n:num" num_CASES) THEN
	REWRITE_TAC [NOT_LESS_0;NOT_SUC;LESS_0]);;

let DA = prove_thm (
	`DA`,
	"!k n. ~(n = 0) ==> ?r q. (k = (q * n) + r) /\ r < n",
	PURE_ONCE_REWRITE_TAC [th5] THEN
	REPEAT STRIP_TAC THEN
	CHOOSE_THEN (MP_TAC o (MATCH_MP th2))
	  (SPECL ["k:num";"n:num"] th1) THEN
	CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN
	DISCH_THEN (X_CHOOSE_THEN "r:num" STRIP_ASSUME_TAC) THEN
	EXISTS_TAC "r:num" THEN
	EXISTS_TAC "q:num" THEN
	CONJ_TAC THEN
	FIRST [FIRST_ASSUM ACCEPT_TAC;ALL_TAC] THEN
	DISJ_CASES_THENL [ACCEPT_TAC;MP_TAC]
	  (SPECL ["r:num";"n:num"] LESS_CASES) THEN
	DISCH_THEN ((X_CHOOSE_TAC "p:num") o (MATCH_MP th3)) THEN
	IMP_RES_THEN IMP_RES_TAC th4 THEN
	MP_TAC (ASSUME "k = (q * n) + r") THEN
	SUBST1_TAC (ASSUME "r = n + p") THEN
	PURE_REWRITE_TAC [ADD_ASSOC;SYM (SPEC_ALL (CONJUNCT2 MULT))] THEN
	DISCH_TAC THEN
	RES_TAC);;

close_theory ();;
