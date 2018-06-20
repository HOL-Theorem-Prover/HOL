% PROOF		: Transistor Implementation of a Counter		%
% FILE		: tempabs.ml						%
%									%
% DESCRIPTION	: Defines the predicates `Next`, `Inf`, `IsTimeOf`	%
%		  and `TimeOf` and derives several major theorems	%
%		  which provide a basis for temporal abstraction.	%
%									%
%		  These predicates and theorems are taken from		%
%		  T.Melham's paper, "Abstraction Mechanisms for		%
%		  Hardware Verification", Hardware Verification		%
%		  Workshop, University of Calgary, January 1987.	%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 31 March 1987						%

new_theory `tempabs`;;

new_parent `wop`;;

let Next = new_definition (
	`Next`, 
	"Next (t1,t2) g =
	  (t1 < t2) /\ (g t2)  /\ (!t. (t1 < t) /\ (t < t2) ==> ~g t)");;

let Inf = new_definition (
	`Inf`,
	"Inf g = !t.?t'. t'>t /\ (g t')");;

let IsTimeOf = new_prim_rec_definition (
	`IsTimeOf`,
	"(IsTimeOf 0 g t = g (t) /\ !t'. t' < t ==> ~g (t')) /\
	 (IsTimeOf (SUC n) g t =
	  g (t) /\
	  ?t'.
	    t' < t /\
	    IsTimeOf n g t' /\
	    (!t''. ((t' < t'') /\ (t'' < t)) ==> ~g (t'')))");;

let TimeOf = new_definition (
	`TimeOf`,
	"TimeOf g n = @t. IsTimeOf n g t");;

let when = new_infix_definition (
	`when`,
	"when (s1:num->*) (s2:num->bool) = (\n. s1 (TimeOf s2 n))");;

let WOP = theorem `wop` `WOP`;;

let BETA_RULE = CONV_RULE (DEPTH_CONV BETA_CONV);;

let Next_ADD1 = prove_thm (
	`Next_ADD1`,
	"!s t. (s (t + 1) ==> Next (t,t + 1) s)",
	PURE_REWRITE_TAC [Next;SYM (SPEC "t" ADD1)] THEN
	REPEAT STRIP_TAC THENL
	[REWRITE_TAC [LESS_SUC_REFL];
	 FIRST_ASSUM ACCEPT_TAC;
	 IMP_RES_TAC LESS_NOT_EQ THEN
	 ASSUME_TAC (NOT_EQ_SYM (ASSUME "~(t = t')")) THEN
	 IMP_RES_TAC LESS_SUC_IMP THEN
	 IMP_RES_TAC LESS_ANTISYM]);;

let Next_INCREASE = prove_thm (
	`Next_INCREASE`,
	"!s t1 t2.
	  (~(s (t1 + 1)) /\ Next (t1 + 1,t2) s) ==> Next (t1,t2) s",
	PURE_REWRITE_TAC [Next;SYM (SPEC "t" ADD1)] THEN
	REPEAT STRIP_TAC THENL
	[IMP_RES_TAC SUC_LESS;
	 FIRST_ASSUM ACCEPT_TAC;
	 IMP_RES_TAC LESS_SUC_EQ THEN
	 DISJ_CASES_TAC
	   (PURE_REWRITE_RULE [LESS_OR_EQ] (ASSUME "(SUC t1) <= t")) THENL
	 [RES_TAC;
	  ASSUME_TAC (SUBS [ASSUME "SUC t1 = t"] (ASSUME "~s(SUC t1)")) THEN
	  RES_TAC]]);;

let Next_IDENTITY = prove_thm (
	`Next_IDENTITY`,
	"!s t1 t2 t3.
	  (Next (t1,t2) s /\ Next (t1,t3) s) ==> (t2 = t3)",
	PURE_REWRITE_TAC [Next] THEN
	REPEAT STRIP_TAC THEN
	DISJ_CASES_TAC (SPEC "t2 = t3" EXCLUDED_MIDDLE) THENL
	[FIRST_ASSUM ACCEPT_TAC;
	 DISJ_CASES_TAC (SPEC "t2 < t3" EXCLUDED_MIDDLE) THENL
	 [RES_TAC;IMP_RES_TAC LESS_CASES_IMP THEN RES_TAC]]);;

% lemma1 = . |- ?n. g n /\ (!m. m < n ==> ~g m) %
let th1 = SPEC "t" (PURE_REWRITE_RULE [Inf] (ASSUME "Inf g"));;
let th2 = ASSUME (snd (dest_exists (concl th1)));;
let th3 = CONJUNCT2 th2;;
let th4 = EXISTS (mk_exists ("t'",concl th3),"t'") th3;;
let th5 = CHOOSE ("t'",th1) th4;;
let lemma1 = MATCH_MP WOP th5;;

let lemma2 = TAC_PROOF (
	([],"(a ==> ~(b /\ c)) = ((b /\ a) ==> ~c)"),
	REWRITE_TAC [DE_MORGAN_THM;SYM (SPEC_ALL IMP_DISJ_THM)] THEN
	EQ_TAC THEN (REPEAT STRIP_TAC) THEN RES_TAC);;

%
lemma3 = 
.. |- ?t'.
       g t' /\
       (?t. t < t' /\ IsTimeOf n g t /\ (!m. t < m /\ m < t' ==> ~g m))
%
let th1 = ASSUME "?t. IsTimeOf n g t";;
let th2 = ASSUME (snd (dest_exists (concl th1)));;
let th3 = SPEC "t" (PURE_REWRITE_RULE [Inf] (ASSUME "Inf g"));;
let th4 = ASSUME (snd (dest_exists (concl th3)));;
let th5 = BETA_CONV (mk_comb (mk_abs ("t'",concl th4),"t'"));;
let th6 = EQ_MP (SYM th5) th4;;
let th7 = EXISTS (mk_exists ("t'",concl th6),"t'") th6;;
let th8 = CHOOSE ("t'",th3) th7;;
let th9 = BETA_RULE (MATCH_MP WOP th8);;
let th10 = EQ_MP (GEN_ALPHA_CONV "t'" (concl th9)) th9;;
let th11 = PURE_REWRITE_RULE [GREATER;lemma2] th10;;
let th12 = ASSUME (snd (dest_exists (concl th11)));;
let th13 = CONJUNCT1 (CONJUNCT1 th12);;
let th14 = CONJUNCT2 (CONJUNCT1 th12);;
let th15 = CONJUNCT2 th12;;
let th16 = LIST_CONJ [th13;th2;th15];;
let th17 = EXISTS (mk_exists ("t",concl th16),"t") th16;;
let th18 = LIST_CONJ [th14;th17];;
let th19 = EXISTS (mk_exists ("t'",concl th18),"t'") th18;;
let th20 = CHOOSE ("t'",th11) th19;;
let lemma3 = CHOOSE ("t",th1) th20;;

let IsTimeOf_EXISTS = prove_thm (
	`IsTimeOf_EXISTS`,
	"!g. Inf g ==> !n. ?t. IsTimeOf n g t",
	GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
	[REWRITE_TAC [IsTimeOf;lemma1];REWRITE_TAC [IsTimeOf;lemma3]]);;

let TimeOf_DEFINED = prove_thm (
	`TimeOf_DEFINED`,
	"!g. Inf g ==> !n. IsTimeOf n g (TimeOf g n)",
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC IsTimeOf_EXISTS THEN
	ACCEPT_TAC
	  (PURE_REWRITE_RULE [SYM TimeOf]
	    (SELECT_RULE (SPEC "n" (ASSUME "!n. ?t. IsTimeOf n g t")))));;

let TimeOf_TRUE = prove_thm (
	`TimeOf_TRUE`,
	"!g. Inf g ==> !n. g (TimeOf g n)",
	REPEAT STRIP_TAC THEN
	IMP_RES_TAC TimeOf_DEFINED THEN
	DISJ_CASES_TAC (SPEC "n" num_CASES) THENL
	[SUBST1_TAC (ASSUME "n = 0") THEN
	 STRIP_ASSUME_TAC
	   (PURE_REWRITE_RULE [IsTimeOf]
	     (SPEC "0" (ASSUME "!n. IsTimeOf n g (TimeOf g n)")));
	 FIRST_ASSUM
	   (\thm.
	     if is_exists (concl thm)
	       then (CHOOSE_THEN SUBST1_TAC thm) else NO_TAC) THEN
	 STRIP_ASSUME_TAC
	   (PURE_REWRITE_RULE [IsTimeOf]
	     (SPEC "SUC n'" (ASSUME "!n. IsTimeOf n g (TimeOf g n)")))]);;

let tm = "!t''. t' < t'' /\ t'' < t1 ==> ~g t''";;

let IsTimeOf_IDENTITY = prove_thm (
	`IsTimeOf_IDENTITY`,
	"!g n t1 t2. IsTimeOf n g t1 /\ IsTimeOf n g t2 ==> (t1 = t2)",
	GEN_TAC THEN
	INDUCT_TAC THENL
	[PURE_REWRITE_TAC [IsTimeOf] THEN
	 REPEAT STRIP_TAC THEN
	 DISJ_CASES_TAC (SPECL ["t1";"t2"] LESS_CASES) THENL
	 [RES_TAC;
	  DISJ_CASES_TAC
	    (PURE_REWRITE_RULE [LESS_OR_EQ] (ASSUME "t2 <= t1")) THENL
	  [RES_TAC;ACCEPT_TAC (SYM (ASSUME "t2 = t1"))]];
	 PURE_REWRITE_TAC [IsTimeOf] THEN
	 REPEAT STRIP_TAC THEN
	 RES_TAC THEN
	 ASSUME_TAC
	  (SUBS [ASSUME "t'' = t'"]
	    (ASSUME "!t'''. t'' < t''' /\ t''' < t2 ==> ~g t'''")) THEN
	 ASSUME_TAC
	   (SUBS [ASSUME "t' = t''"]
	     (EQ_MP (GEN_ALPHA_CONV "t''':num" tm) (ASSUME tm))) THEN
	 DISJ_CASES_TAC (SPECL ["t1";"t2"] LESS_CASES) THENL
	 [RES_TAC;
	  DISJ_CASES_TAC
	    (PURE_REWRITE_RULE [LESS_OR_EQ] (ASSUME "t2 <= t1")) THENL
	  [RES_TAC;
	   ASSUME_TAC (SYM (ASSUME "t2 = t1")) THEN
	   RES_TAC THEN
	   ACCEPT_TAC (SYM (ASSUME "t2 = t1"))]]]);;

%
TimeOf_INCREASING = 
|- !g. Inf g ==> (!n. (TimeOf g n) < (TimeOf g(n + 1)))
%
let th1 =
	PURE_REWRITE_RULE [IsTimeOf]
	  (SPEC "SUC n" (UNDISCH (SPEC "g" TimeOf_DEFINED)));;
let th2 = CONJUNCT2 th1;;
let th3 = ASSUME (snd (dest_exists (concl th2)));;
let th4 = CONJUNCT1 th3;;
let th5 = CONJUNCT1 (CONJUNCT2 th3);;
let th6 = SPEC "n" (UNDISCH (SPEC "g" TimeOf_DEFINED));;
let th7 = MATCH_MP IsTimeOf_IDENTITY (LIST_CONJ [th5;th6]);;
let th8 = SUBS [th7] th4;;
let th9 = CHOOSE ("t'",th2) th8;;
let th10 = GEN "g" (DISCH_ALL (GEN "n" th9));;
let th11 = PURE_REWRITE_RULE [ADD1] th10;;
let TimeOf_INCREASING = save_thm (`TimeOf_INCREASING`,th11);;

%
TimeOf_INTERVAL = 
|- !g.
    Inf g ==> (!n t. (TimeOf g n) < t /\ t < (TimeOf g(n + 1)) ==> ~g t)
%
let th1 =
	PURE_REWRITE_RULE [IsTimeOf]
	  (SPEC "SUC n" (UNDISCH (SPEC "g" TimeOf_DEFINED)));;
let th2 = CONJUNCT2 th1;;
let th3 = ASSUME (snd (dest_exists (concl th2)));;
let th4 = CONJUNCT2 (CONJUNCT2 th3);;
let th5 = CONJUNCT1 (CONJUNCT2 th3);;
let th6 = SPEC "n" (UNDISCH (SPEC "g" TimeOf_DEFINED));;
let th7 = MATCH_MP IsTimeOf_IDENTITY (LIST_CONJ [th5;th6]);;
let th8 = SUBS [th7] th4;;
let th9 = EQ_MP (GEN_ALPHA_CONV "t" (concl th8)) th8;;
let th10 = CHOOSE ("t'",th2) th9;;
let th11 = GEN "g" (DISCH_ALL (GEN "n" th10));;
let th12 = PURE_REWRITE_RULE [ADD1] th11;;
let TimeOf_INTERVAL = save_thm (`TimeOf_Interval`,th12);;

let TimeOf_Next = prove_thm (
	`TimeOf_Next`,
	"!g. Inf g ==> Next (TimeOf g n,TimeOf g (n+1)) g",
	PURE_REWRITE_TAC [Next] THEN
	REPEAT STRIP_TAC THEN
	IMP_RES_THEN (\thm. REWRITE_TAC [thm]) TimeOf_INCREASING THEN
	IMP_RES_THEN (\thm. REWRITE_TAC [thm]) TimeOf_TRUE THEN
	IMP_RES_THEN (\thm. REWRITE_TAC [thm]) TimeOf_INTERVAL);;

close_theory ();;
