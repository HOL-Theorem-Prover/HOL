% PROOF		: Well Ordering Property				%
% FILE		: wop.ml						%
% DESCRIPTION   : Prove the well ordering property:			%
%									%
%		  |- !P. (?n. P n) ==> 					%
%		         (?n. P n /\ (!m. m < n ==> ~P m))		%
%									%
%		 I.e. considering P to be a set, that is the set of 	%
%		 integers, x , such that P(x), then every non-empty	%
%		 P has a smallest element. 				%
%									%
% READS FILES	: <none>						%
% WRITES FILES  : wop.th						%
%									%
% AUTHOR	: T. Melham						%
% DATE		: 85.04.06						%
% REVISED	: 86.05.10						%

% Create new theory "wop.th".						%
new_theory `wop`;;

% Matching modus ponens for boolean equalities.  			%
let MATCH_EQ_MP thm = 
    let vars = fst (strip_forall (concl thm)) in
        MATCH_MP (GENL vars (fst (EQ_IMP_RULE (SPEC_ALL thm))));;

% We first prove that, if there does NOT exist a smallest n such that	%
% P(n) is true, then for all n P is false of all numbers smaller than n.%
% The main step is an induction on n.					%
let lemma = 
    TAC_PROOF(([], "(~?n. P(n) /\ (!m. m<n ==> ~P(m))) ==>
		    (!n m. m<n ==> ~P(m))"),
	      CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN
	      DISCH_THEN (ASSUME_TAC o hd o RES_CANON) THEN
	      INDUCT_TAC THENL
	      [REWRITE_TAC [NOT_LESS_0];
	       GEN_TAC THEN
	       DISCH_THEN 
	        ((DISJ_CASES_THEN2 SUBST1_TAC (ANTE_RES_THEN ACCEPT_TAC)) o
		 (MATCH_EQ_MP LESS_THM)) THEN
	       DISCH_THEN (ANTE_RES_THEN IMP_RES_TAC)]);;

% We now prove the Contrapositive of the well ordering property. By the	%
% lemma, we know that there is no n such that P is true of it.		%
let wop_contrapos = 
    TAC_PROOF(([], "(~?n. P(n) /\ (!m. m<n ==> ~P(m))) ==> ~?n.P(n)"),
	      DISCH_TAC THEN
	      EVERY_ASSUM (ASSUME_TAC o hd o RES_CANON o 
	    	           CONV_RULE (DEPTH_CONV NOT_EXISTS_CONV)) THEN
	      CONV_TAC NOT_EXISTS_CONV THEN
	      X_GEN_TAC "n:num" THEN
	      HOL_IMP_RES_THEN (ASSUME_TAC o (SPEC "n")) lemma THEN
	      DISCH_THEN (ANTE_RES_THEN IMP_RES_TAC));;

% To get the well ordering property, we take the contrapositive of the	%
% theorem "wop_contrapos" and simplify double negations --- "~~P".	%
let WOP =
    save_thm(`WOP`, 
	     GEN_ALL(REWRITE_RULE [NOT_CLAUSES] (CONTRAPOS wop_contrapos)));;

% Close the theory "wop.th".						%
close_theory();;

quit();;
