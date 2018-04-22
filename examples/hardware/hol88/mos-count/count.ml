% PROOF		: Transistor Implementation of a Counter		%
% FILE		: count.ml						%
%									%
% DESCRIPTION	: Top-level implementation of the counter with three	%
%		  different correctness statements.			%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 1 April 1987						%

new_theory `count`;;

loadt `misc`;;
loadt `types`;;

new_parent `regn`;;
new_parent `muxn`;;
new_parent `incn`;;

let COUNT_IMP = new_definition (
	`COUNT_IMP`,
	"COUNT_IMP n (phiA:^wire,reset:^wire,in:^bus,out:^bus) =
	  ?phiAbar phiB phiBbar b1 b2.
	    Clock (phiA,phiAbar,phiB,phiBbar) /\
	    REGn_IMP n (phiA,phiB,b1,out) /\
	    MUXn_IMP n (reset,in,b2,b1) /\
	    INCn_IMP n (out,b2) /\
	    isBus n b1 /\
	    isBus n b2");;

let when = definition `tempabs` `when`;;
let mux = definition `muxn` `mux`;;

let BoolAbs_THM = theorem `dataabs` `BoolAbs_THM`;;
let REGn_CORRECT = theorem `regn` `REGn_CORRECT`;;
let MUXn_CORRECT = theorem `muxn` `MUXn_CORRECT`;;
let INCn_CORRECT = theorem `incn` `INCn_CORRECT`;;

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


% =========================================== %
% Basic Behaviour disregarding initialization %

let COUNT_CORRECT1 = prove_thm (
	`COUNT_CORRECT1`,
	"!n clk reset inp out.
	  COUNT_IMP n (clk,reset,inp,out) /\
	  isBus n inp /\
	  isBus n out
	  ==>
	  !t.
	    Def ((reset when (isHi clk)) t) /\
	      Defn n ((inp when (isHi clk)) t) /\
	        (((reset when (isHi clk)) t = Hi) \/
	          (Defn n ((out when (isHi clk)) t)))
	    ==>
	    Defn n ((out when (isHi clk)) (t+1)) /\
	      (WordVal n (WordAbs ((out when (isHi clk)) (t+1))) =
	        (BoolAbs ((reset when (isHi clk)) t) =>
	          (WordVal n (WordAbs ((inp when (isHi clk)) t))) |
	          (((WordVal n (WordAbs ((out when (isHi clk)) t))) + 1)
	            MOD (2 EXP (SUC n)))))",
	let REGn_thm = (BETA_RULE (PURE_REWRITE_RULE [when] REGn_CORRECT))
	in
	PURE_REWRITE_TAC [COUNT_IMP;when] THEN
	BETA_TAC THEN
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC REGn_thm THEN
	IMP_RES_TAC MUXn_CORRECT THEN
	IMP_RES_TAC INCn_CORRECT THEN
	ASM_REWRITE_TAC [mux] THENL
	[ASM_REWRITE_TAC [BoolAbs_THM];
	 ASM_REWRITE_TAC [BoolAbs_THM];
	 COND_CASES_TAC THEN ASM_REWRITE_TAC [BoolAbs_THM];
	 COND_CASES_TAC THEN ASM_REWRITE_TAC [BoolAbs_THM]]);;

% ================================================== %
% Behaviour plus proper initialization at some point %

let th1 = CONJUNCT1 (CONJUNCT2 (CONJUNCT2 ADD_CLAUSES));;
let th2 = (DEPTH_CONV (REWRITE_CONV th1)) "((SUC p) + sysinit)";;
let th3 = SYM (TRANS th2 ((REWRITE_CONV ADD1) (rhs (concl th2))));;

let COUNT_CORRECT2 = prove_thm (
	`COUNT_CORRECT2`,
	"!n clk reset inp out.
	  COUNT_IMP n (clk,reset,inp,out) /\
	  isBus n inp /\
	  isBus n out /\
	  (!t. Def ((reset when (isHi clk)) t)) /\
	  (!t. Defn n ((inp when (isHi clk)) t))
	  ==>
	  !sysinit.
	    ((reset when (isHi clk)) sysinit = Hi)
	    ==>
	    !t. sysinit <= t ==>
	      Defn n ((out when (isHi clk)) (t+1)) /\
	        (WordVal n (WordAbs ((out when (isHi clk)) (t+1))) =
	          (BoolAbs ((reset when (isHi clk)) t) =>
	            (WordVal n (WordAbs ((inp when (isHi clk)) t))) |
	            (((WordVal n (WordAbs ((out when (isHi clk)) t))) + 1)
	              MOD (2 EXP (SUC n)))))",
	PURE_REWRITE_TAC [LESS_OR_EQ_ADD] THEN
	REPEAT GEN_TAC THEN STRIP_TAC THEN
	GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
	DISCH_THEN (STRIP_THM_THEN (SUBST1_TAC o SYM)) THEN
	SPEC_TAC ("p","p") THEN
	INDUCT_TAC THENL
	[PURE_REWRITE_TAC [ADD_CLAUSES] THEN
	 ASSUM_LIST (MAP_EVERY
	   (\thm. if (is_forall (concl thm))
	     then (ASSUME_TAC (SPEC "sysinit" thm)) else ALL_TAC)) THEN
	 IMP_RES_TAC COUNT_CORRECT1 THEN
	 RES_TAC THEN
	 ASM_REWRITE_TAC [];
	 ASSUM_LIST (MAP_EVERY
	   (\thm. if (is_forall (concl thm))
	     then (ASSUME_TAC (SPEC "(SUC p) + sysinit" thm))
	     else ALL_TAC)) THEN
	 ASSUM_LIST (MAP_EVERY
	   (\thm. if (is_conj (concl thm))
	     then (ASSUME_TAC (SUBS [th3] (CONJUNCT1 thm)))
	     else ALL_TAC)) THEN
	 IMP_RES_TAC COUNT_CORRECT1 THEN
	 RES_TAC THEN
	 ASM_REWRITE_TAC []]);;

% ========================================================== %
% Similar to COUNT_CORRECT2 but weaker assumptions on inputs %

let COUNT_CORRECT3 = prove_thm (
	`COUNT_CORRECT3`,
	"!n clk reset inp out.
	  COUNT_IMP n (clk,reset,inp,out) /\
	  isBus n inp /\
	  isBus n out
	  ==>
	  !sysinit.
	    (!t. sysinit <= t ==> Def ((reset when (isHi clk)) t)) /\
	    (!t. sysinit <= t ==> Defn n ((inp when (isHi clk)) t)) /\
	    ((reset when (isHi clk)) sysinit = Hi)
	    ==>
	    !t. sysinit <= t ==>
	      Defn n ((out when (isHi clk)) (t+1)) /\
	        (WordVal n (WordAbs ((out when (isHi clk)) (t+1))) =
	          (BoolAbs ((reset when (isHi clk)) t) =>
	            (WordVal n (WordAbs ((inp when (isHi clk)) t))) |
	            (((WordVal n (WordAbs ((out when (isHi clk)) t))) + 1)
	              MOD (2 EXP (SUC n)))))",
	REPEAT GEN_TAC THEN STRIP_TAC THEN
	GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
	PURE_REWRITE_TAC [LESS_OR_EQ_ADD] THEN
	DISCH_THEN (STRIP_THM_THEN (SUBST1_TAC o SYM)) THEN
	SPEC_TAC ("p","p") THEN
	INDUCT_TAC THENL
	[PURE_REWRITE_TAC [ADD_CLAUSES] THEN
	 ASSUME_TAC (SPEC "sysinit" LESS_EQ_REFL) THEN
	 RES_TAC THEN
	 IMP_RES_TAC COUNT_CORRECT1 THEN
	 RES_TAC THEN
	 ASM_REWRITE_TAC [];
	 ASSUME_TAC
	   (SUBS [SPECL ["sysinit";"SUC p"] ADD_SYM]
	    (SPECL ["sysinit";"SUC p"] LESS_EQ_ADD)) THEN
	 RES_TAC THEN
	 ASSUM_LIST (MAP_EVERY
	   (\thm. if (is_conj (concl thm))
	     then (ASSUME_TAC (SUBS [th3] (CONJUNCT1 thm)))
	     else ALL_TAC)) THEN
	 IMP_RES_TAC COUNT_CORRECT1 THEN
	 RES_TAC THEN
	 ASM_REWRITE_TAC []]);;

close_theory ();;
