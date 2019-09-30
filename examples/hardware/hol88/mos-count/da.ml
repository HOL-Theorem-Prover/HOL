% PROOF		: Division Algorithm for natural numbers.		%
% FILE		: da.ml							%
% DESCRIPTION   : Proof of the Division Algorithm for natural numbers.	%
%									%
%		      |- !k n. (n>0) ==> ?q r. k=qn+r /\ 0<=r<n		%
%									%
%		  The proof follows MacLane & Birkhoff, p29.		%
%		 							%
% READS FILES	: wop.th						%
% WRITES FILES  : da.th							%
%									%
% AUTHOR	: T.F. Melham						%
% DATE		: 86.02.01						%
% REVISED	: 86.05.11						%
%									% 
% REFERENCES	: MacLane, S. & Birkhoff, G.				%
%	      	  "Algebra"						%
%		  2nd Edition, MacMillan, New York, 1979.		%

% Create the new theory "da.th"						%
new_theory `da`;;

% Parent theory is "wop.th" --- the well ordering property.		%
new_parent `wop`;;

% Fetch the theorem stating the well ordering property.			%
let WOP = theorem `wop` `WOP`;;

% We first show that ?r q. k=qn+r.  This is easy, with r=k and q=0.	%
let exists_lemma = 
    TAC_PROOF(([], "?r q. (k=(q*n)+r)"),
	      MAP_EVERY EXISTS_TAC ["k";"0"] THEN
	      REWRITE_TAC [MULT_CLAUSES;ADD_CLAUSES]);;

% We now show, using the well ordering property, that there is a	%
% SMALLEST n' such that ?q. k=qn+n'.  This is the correct remainder.	%
%									%
% The theorem is: |- ?n'. (?q. k = q*n+n') /\	 			%
%			  (!y. y<n' ==> (!q. ~(k=q*n+y)))		%
let smallest_lemma = 
    CONV_RULE (DEPTH_CONV NOT_EXISTS_CONV)
	      (MATCH_MP (CONV_RULE (DEPTH_CONV BETA_CONV) 
				   (SPEC "\r.?q.k=(q*n)+r" WOP))
	      	  	exists_lemma);;

% We will need the lemma  |- !m n. n <= m ==> (?p. m = n + p)		%
let leq_add_lemma =
    TAC_PROOF(([],"!m n. (n<=m) ==> ?p.m=n+p"),
	      REWRITE_TAC [LESS_OR_EQ] THEN
	      REPEAT STRIP_TAC THENL
	      [FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP LESS_ADD_1) THEN
	       EXISTS_TAC "p+1" THEN
	       FIRST_ASSUM ACCEPT_TAC;
	       EXISTS_TAC "0" THEN
	       ASM_REWRITE_TAC [ADD_CLAUSES]]);;

% We will need the lemma:  |- k=qn+n+p ==> k=(q+1)*n+p			%
let k_expr_lemma = 
    TAC_PROOF(([], "(k=(q*n)+n+p) ==> (k=((q+1)*n)+p)"),
	      REWRITE_TAC [RIGHT_ADD_DISTRIB;MULT_CLAUSES;ADD_ASSOC]);;

% We will need the lemma: [~n=0] |- p < (n + p)				%
let less_add = UNDISCH(SUBS [SPECL ["p";"n"] ADD_SYM]
		            (SPECL ["p:num";"n:num"] LESS_ADD_NONZERO));;

% Now prove the theorem stating the Division Algorithm Theorem.		%
let da = 
    prove_thm(`DA`,
              "!k n. ~(n=0) ==> ?r q. (k=(q*n)+r) /\ r<n",
	      REPEAT STRIP_TAC THEN
	      STRIP_ASSUME_TAC smallest_lemma THEN
	      MAP_EVERY EXISTS_TAC ["n':num";"q"] THEN
	      ASM_REWRITE_TAC [] THEN
	      DISJ_CASES_THEN CHECK_ASSUME_TAC
			      (SPECL ["n':num";"n"] LESS_CASES) THEN
	      IMP_RES_THEN (STRIP_THM_THEN SUBST_ALL_TAC) leq_add_lemma THEN
	      IMP_RES_TAC k_expr_lemma THEN
	      ANTE_RES_THEN IMP_RES_TAC less_add);;

% Close the theory "da.th".						%
close_theory();;

quit();;
