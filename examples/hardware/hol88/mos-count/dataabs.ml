% PROOF		: Transistor Implementation of a Counter		%
% FILE		: dataabs.ml						%
%									%
% DESCRIPTION	: Defines data abstractions from the four-valued	%
%		  logic to boolean logic for single bits and for	%
%		  arbitrary sized words and from words to numbers.	%
%									%
%		  Hilbert's choice operator "@" is used to simulate	%
%		  the partial mapping of values in the four-valued	%
%		  logic to booleans.  The predicates Def and Defn	%
%		  determine when the abstraction is valid.  Alternate	%
%		  ways of abstracting to boolean logic would include	%
%		  the use of relations or else mapping instead to a	%
%		  three-valued logic consisting of T,F and bottom.	%
%									%
%		  The Def predicate is taken from Inder Dhingra's	%
%		  paper, "Formal Validation of an Integrated Circuit	%
%		  Design Style", Hardware Verification Workshop,	%
%		  University of Calgary, January 1987.			%
%									%
% AUTHOR	: J.Joyce						%
% DATE		: 31 March 1987						%

new_theory `dataabs`;;

loadt `misc`;;
loadt `types`;;

new_parent `mos`;;

let Def = new_definition (
	`Def`,
	"Def (v:^val) = (v = Lo) \/ (v = Hi)");;

let Defn = new_prim_rec_definition (
	`Defn`,
	"(Defn 0 (v:^vec) = Def (v 0)) /\
	 (Defn (SUC n) (v:^vec) = Def (v (SUC n)) /\ Defn n v)");;

let BoolAbs = new_definition (
	`BoolAbs`,
	"BoolAbs (v:^val) =
	  @b. ((v = Lo) /\ (b = F)) \/ ((v = Hi) /\ (b = T))");;

let WordAbs = new_definition (
	`WordAbs`,
	"WordAbs (v:^vec) = \p. BoolAbs (v p)");;

let BoolVal = new_definition (
	`BoolVal`,
	"BoolVal (b:bool) = (b => 1 | 0)");;

let WordVal = new_prim_rec_definition (
	`WordVal`,
	"(WordVal 0 (w:^word) = BoolVal (w 0)) /\
	 (WordVal (SUC n) (w:^word) =
	  ((2 EXP (SUC n)) * (BoolVal (w (SUC n)))) + (WordVal n w))");;

let isBus = new_definition (
	`isBus`,
	"isBus n (b:^bus) = !m. n < m ==> !t. b t m = Er");;

let DEST_BUS = new_definition (
	`DEST_BUS`,
	"DEST_BUS (b:^bus) = \p. \t. b t p");;

let After = new_definition (`After`,"After t c = !t'. t <= t' ==> c t'");;

let val_not_eq_ax = axiom `mos` `val_not_eq_ax`;;

let CHOOSE_TRUE = SELECT_RULE (EXISTS ("?b.b","T") TRUTH);;

let NOT_CHOOSE_FALSE =
	SELECT_RULE
	  (EXISTS ("?b.~b","F")
	    (SUBS [SYM (CONJUNCT2 (CONJUNCT2 NOT_CLAUSES))] TRUTH));;

let Def_DISJ_CASES = save_thm (
	`Def_DISJ_CASES`,
	GEN_ALL (fst (EQ_IMP_RULE Def)));;

let BoolAbs_THM = prove_thm (
	`BoolAbs_THM`,
	"(BoolAbs Hi = T) /\ (BoolAbs Lo = F)",
	REWRITE_TAC [BoolAbs;val_not_eq_ax;CHOOSE_TRUE;NOT_CHOOSE_FALSE]);;

let isBus_THM = prove_thm (
	`isBus_THM`,
	"!n b1 b2.
	  isBus n b1 /\
	  isBus n b2
	  ==>
	  !t1 t2. (b1 t1 = b2 t2) = (!m. m <= n ==> (b1 t1 m = b2 t2 m))",
	let thm = INST_TYPE [":^posn",":*";":^val",":**"] EQ_EXT
	in
	PURE_REWRITE_TAC [isBus] THEN
	BETA_TAC THEN
	REPEAT STRIP_TAC THEN
	EQ_TAC THENL
	[STRIP_TAC THEN ASM_REWRITE_TAC [];
	 REPEAT STRIP_TAC THEN
	 (\g. IMP_TAC (SPECL [lhs (snd g);rhs (snd g)] thm) g) THEN
	 GEN_TAC THEN
	 DISJ_CASES_TAC (SPECL ["n:num";"x:num"] LESS_CASES) THEN
	 RES_TAC THEN
	 ASM_REWRITE_TAC []]);;

close_theory ();;
