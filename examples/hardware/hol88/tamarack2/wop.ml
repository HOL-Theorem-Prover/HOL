% =====================================================================	%
% Jeff Joyce, 28 April 1989						%
%									%
% Well Ordering Principle for the natural numbers.			%
% =====================================================================	%

new_theory `wop`;;

let (MATCH_GOAL_TAC:thm_tactic) impthm (asl,tm) = (
	let match = ((HOL_PART_MATCH (snd o dest_imp)) impthm) tm
	in
	([asl,fst (dest_imp (concl match))],\[th]. MP match th)) ?
	failwith `MATCH_GOAL_TAC`;;

let COURSE_OF_VALUES_LEMMA = prove_thm (
	`COURSE_OF_VALUES_LEMMA`,
	"!P. (!n. (!m. m < n ==> P m)) ==> !n. P n",
	REPEAT STRIP_TAC THEN
	FIRST_ASSUM (MP_TAC o (SPECL ["SUC n";"n:num"])) THEN
	REWRITE_TAC [LESS_SUC_REFL]);;

let WOP = prove_thm (
	`WOP`,
	"!P. (?n. P n) ==> (?n. P n /\ (!m. m < n ==> ~P m))",
	GEN_TAC THEN
	CONV_TAC EXISTS_IMP_FORALL_CONV THEN
	MATCH_GOAL_TAC
	  (BETA_RULE (SPEC "\n. P n ==> (?n. P n /\ (!m. m < n ==> ~P m))"
	    COURSE_OF_VALUES_LEMMA)) THEN
	INDUCT_TAC THEN
	REWRITE_TAC [NOT_LESS_0;LESS_THM] THEN
	GEN_TAC THEN
	DISCH_THEN (DISJ_CASES_THENL [SUBST1_TAC;ASSUME_TAC]) THEN
	REPEAT STRIP_TAC THEN
	RES_TAC THEN
	DISJ_CASES_THENL [ASSUME_TAC;MP_TAC]
	  (CONV_RULE (ONCE_DEPTH_CONV NOT_FORALL_CONV)
	    (SPEC "!m. m < n ==> ~(P m)" EXCLUDED_MIDDLE)) THENL [
	  EXISTS_TAC "n:num" THEN
	  ASM_REWRITE_TAC [];
          DISCH_THEN (STRIP_ASSUME_TAC o
	    (REWRITE_RULE [IMP_DISJ_THM;DE_MORGAN_THM])) THEN
	  RES_TAC]);;

close_theory ();;
