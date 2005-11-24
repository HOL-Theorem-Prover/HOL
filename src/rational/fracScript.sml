(***************************************************************************
 *
 *  Theory of fractions.
 *
 *  Jens Brandt, November 2005
 *
 ***************************************************************************)

open HolKernel boolLib Parse bossLib;

(* interactive mode
app load [
	"pairTheory", "jbUtils", "schneiderUtils",
	"arithmeticTheory", "integerTheory", "intLib", "integerRingLib", "intSyntax",
	"intExtensionTheory", "intExtensionLib", "fracUtils"];
*)

open
	pairTheory jbUtils schneiderUtils
	arithmeticTheory integerTheory intLib integerRingLib intSyntax
	intExtensionTheory intExtensionLib fracUtils;

val _ = new_theory "frac";

(*--------------------------------------------------------------------------*
 * type definition
 *--------------------------------------------------------------------------*)

val frac_tyax = new_type_definition( "frac",
	Q.prove(`?x. (\f:int#int. 0i<SND(f)) x`,
		EXISTS_TAC ``(1i,1i)`` THEN
		BETA_TAC THEN
		REWRITE_TAC[SND] THEN
		RW_TAC int_ss []) );

val frac_bij = save_thm("frac_bij", define_new_type_bijections{
		name="frac_tybij",
		ABS="abs_frac",
		REP="rep_frac",
		tyax=frac_tyax } );

(*--------------------------------------------------------------------------*
 * operations
 *--------------------------------------------------------------------------*)

(* numerator, denominator, sign of a fraction *)
val frac_nmr_def = Define `frac_nmr f = FST(rep_frac f)`;
val frac_dnm_def = Define `frac_dnm f = SND(rep_frac f)`;
val frac_sgn_def = Define `frac_sgn f1 = SGN (frac_nmr f1)`;

(* additive, multiplicative inverse of a fraction *)
val frac_ainv_def = Define `frac_ainv f1 = abs_frac(~frac_nmr f1, frac_dnm f1)`;
val frac_minv_def = Define `frac_minv f1 = abs_frac(frac_sgn f1 * frac_dnm f1, ABS(frac_nmr f1) )`;

(* neutral elements *)
val frac_0_def = Define `frac_0 = abs_frac(0i,1i)`;
val frac_1_def = Define `frac_1 = abs_frac(1i,1i)`;

(* less (absolute value) *)
val les_abs_def = Define`les_abs f1 f2 = frac_nmr f1 * frac_dnm f2 < frac_nmr f2 * frac_dnm f1`;

(* basic arithmetics *)
val frac_add_def = Define `frac_add f1 f2 = abs_frac(frac_nmr f1 * frac_dnm f2 + frac_nmr f2 * frac_dnm f1, frac_dnm f1*frac_dnm f2)`;
val frac_sub_def = Define `frac_sub f1 f2 = frac_add f1 (frac_ainv f2)`;
val frac_mul_def = Define `frac_mul f1 f2 = abs_frac(frac_nmr f1 * frac_nmr f2, frac_dnm f1*frac_dnm f2)`;
val frac_div_def = Define `frac_div f1 f2 = frac_mul f1 (frac_minv f2)`;

(*  frac_save terms are always defined (encode the definition of a fraction in the syntax) *)
val frac_save_def = Define `frac_save (nmr:int) (dnm:num) = abs_frac(nmr,&dnm + 1)`;

(*--------------------------------------------------------------------------
 *  FRAC: thm
 *  |- !f. abs_frac (frac_nmr f,frac_dnm f) = f
 *--------------------------------------------------------------------------*)

val FRAC = store_thm("FRAC", ``!f. abs_frac (frac_nmr f,frac_dnm f) = f``,
	STRIP_TAC THEN
	REWRITE_TAC[frac_nmr_def,frac_dnm_def]
	THEN RW_TAC int_ss [CONJUNCT1 frac_bij]);

(*==========================================================================
 *  equivalence of fractions
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  FRAC_EQ: thm
 *  |- !a1 b1 a2 b2. 0<b1 ==> 0<b2 ==>
 *     ((abs_frac(a1,b1)=abs_frac(a2,b2)) = (a1=a2) /\ (b1=b2) )
 *--------------------------------------------------------------------------*)

val FRAC_EQ =
	let
		val subst2a = #1 (EQ_IMP_RULE (REWRITE_RULE [SND] (BETA_RULE (SPEC ``(a1:int,b1:int)`` (CONJUNCT2 frac_bij)))));
		val subst2b = #1 (EQ_IMP_RULE (REWRITE_RULE [SND] (BETA_RULE (SPEC ``(a2:int,b2:int)`` (CONJUNCT2 frac_bij)))));
	in
		store_thm("FRAC_EQ", ``!a1 b1 a2 b2. 0i < b1 ==> 0i < b2 ==> ((abs_frac(a1,b1)=abs_frac(a2,b2)) = (a1=a2) /\ (b1=b2) )``,
			REPEAT GEN_TAC THEN
			STRIP_TAC THEN
			STRIP_TAC THEN
			EQ_TAC THENL
			[
				STRIP_TAC THEN
				REWRITE_TAC[ prove(``((a1:int = a2:int) /\ (b1:int = b2:int)) = ((a1,b1)=(a2,b2))``,RW_TAC int_ss []) ] THEN
				SUBST_TAC[GSYM (UNDISCH_ALL subst2a), GSYM (UNDISCH_ALL subst2b)] THEN
				PROVE_TAC[frac_bij]
			,
				PROVE_TAC[]
			] )
	end;

(*--------------------------------------------------------------------------
 *  FRAC_EQ_ALT : thm
 *  |- !f1 f2. (f1=f2) = (frac_nmr f1 = frac_nmr f2) /\ (frac_dnm f1 = frac_dnm f2)
 *--------------------------------------------------------------------------*)

val FRAC_EQ_ALT = store_thm("FRAC_EQ_ALT", ``!f1 f2. (f1=f2) = (frac_nmr f1 = frac_nmr f2) /\ (frac_dnm f1 = frac_dnm f2)``,
	REPEAT GEN_TAC THEN
	EQ_TAC THEN
	STRIP_TAC THENL
	[
		ALL_TAC
	,
		ONCE_REWRITE_TAC[GSYM FRAC]
	] THEN
	ASM_REWRITE_TAC[] );

(*--------------------------------------------------------------------------
 *  FRAC_NOT_EQ : thm
 *  |- !a1 b1 a2 b2. 0 < b1 ==> 0 < b2 ==>
 *	(~(abs_frac(a1,b1) = abs_frac(a2,b2)) = ~(a1=a2) \/ ~(b1=b2))
 *--------------------------------------------------------------------------*)

val FRAC_NOT_EQ = store_thm("FRAC_NOT_EQ", ``!a1 b1 a2 b2. 0i<b1 ==> 0i<b2 ==> (~(abs_frac(a1,b1) = abs_frac(a2,b2)) = ~(a1=a2) \/ ~(b1=b2))``,
	REPEAT STRIP_TAC THEN
	RW_TAC int_ss [] THEN
	PROVE_TAC[FRAC_EQ] );

(*--------------------------------------------------------------------------
 *  FRAC_NOT_EQ_IMP : thm
 *  |- !a1 b1 a2 b2. 0 < b1 ==> 0 < b2 ==>
 *     ~((a1,b1) = (a2,b2)) ==> ~(abs_frac (a1,b1) = abs_frac (a2,b2))
 *--------------------------------------------------------------------------*)

val FRAC_NOT_EQ_IMP =
	let
		val lemma01a = fst(EQ_IMP_RULE (ONCE_REWRITE_RULE[EQ_SYM_EQ] (SPEC ``(a1:int,b1:int)`` (ONCE_REWRITE_RULE [EQ_SYM_EQ] (CONJUNCT2 frac_bij)))));
		val lemma01b = fst(EQ_IMP_RULE (ONCE_REWRITE_RULE[EQ_SYM_EQ] (SPEC ``(a2:int,b2:int)`` (ONCE_REWRITE_RULE [EQ_SYM_EQ] (CONJUNCT2 frac_bij)))));
		val lemma02a = UNDISCH_ALL (GSYM (REWRITE_RULE[SND] (BETA_RULE (SPEC_ALL lemma01a))));
		val lemma02b = UNDISCH_ALL (GSYM (REWRITE_RULE[SND] (BETA_RULE (SPEC_ALL lemma01b))));
	in
		store_thm("FRAC_NOT_EQ", ``!a1 b1 a2 b2. 0i < b1 ==> 0i < b2 ==> ~((a1,b1) = (a2,b2)) ==> ~(abs_frac (a1,b1) = abs_frac (a2,b2))``,
			REPEAT GEN_TAC THEN
			STRIP_TAC THEN STRIP_TAC THEN
			REWRITE_TAC[CONTRAPOS_CONV ``~((a1,b1) = (a2,b2)) ==> ~(abs_frac (a1,b1) = abs_frac (a2,b2))``] THEN
			ONCE_REWRITE_TAC[lemma02a,lemma02b] THEN
			REWRITE_TAC[CONJUNCT1 frac_bij] THEN
			RW_TAC int_ss [] )
	end;

(*--------------------------------------------------------------------------
 *  FRAC_EQ_TAC : tactic
 *
 *     A ?- abs_frac(a1,b1) = abs_frac(a2,b2)
 *   =========================================  FRAC_EQ_TAC
 *     A ?- a1=a2 | A ?- b1=b2
 *--------------------------------------------------------------------------*)

val FRAC_EQ_TAC:tactic = fn (asm_list,goal) =>
let
	val (lhs,rhs) = dest_eq goal;
	val (lhc, lha) = dest_comb lhs;
	val (rhc, rha ) = dest_comb rhs;
	val (a1,b1) = dest_pair lha;
	val (a2,b2) = dest_pair rha;
in
	let
		val subgoal1 = mk_eq(a1,a2);
		val subgoal2 = mk_eq(b1,b2);
	in
		(
			[(asm_list,subgoal1), (asm_list,subgoal2)],
			fn thms => MP
				(SPEC b2 (SPEC a2 (SPEC b1 (SPEC a1 (
				prove(``!a1 b1 a2 b2. (a1=a2) /\ (b1=b2) ==> (abs_frac(a1,b1)=abs_frac(a2,b2))``, RW_TAC int_ss [])
				)))))
				(LIST_CONJ thms)
		)
	end
end
handle HOL_ERR _ => raise ERR "FRAC_EQ_TAC" "";


(*==========================================================================
 *  some useful things about positive and non-zero
 *  numbers in the context of fractions
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  FRAC_DNMPOS : thm
 *  |- !f. 0 < frac_dnm f
 *--------------------------------------------------------------------------*)

val FRAC_DNMPOS = store_thm("FRAC_DNMPOS",``!f. 0 < frac_dnm f``,
	REWRITE_TAC[frac_dnm_def] THEN
	RW_TAC int_ss [REWRITE_RULE [CONJUNCT1 frac_bij] (SPEC ``rep_frac(f)`` (BETA_RULE (ONCE_REWRITE_RULE [EQ_SYM_EQ] (CONJUNCT2 frac_bij)))) ]);

(*--------------------------------------------------------------------------
 *  frac_pos_conv : term list -> conv
 *--------------------------------------------------------------------------*)

fun frac_pos_conv (asm_list:term list) (t1:term) =
	if (in_list asm_list ``0i < ^t1``) then
		ASSUME ``0i < ^t1``
	else
		if (is_comb t1) then
			let
				val (rator, rand) = dest_comb t1;
			in
				if (is_mult t1) then
					let
						val (fac1, fac2) = intSyntax.dest_mult t1;
						val fac1_thm = frac_pos_conv asm_list fac1;
						val fac2_thm = frac_pos_conv asm_list fac2;
					in
						LIST_MP [fac1_thm,fac2_thm] (SPECL[fac1,fac2] INT_MUL_POS_SIGN)
					end
				else if (rator=``frac_dnm``) then
					SPEC rand FRAC_DNMPOS
				else if (rator=``ABS``) andalso (in_list asm_list ``~(^rand = 0)``) then
					UNDISCH (SPEC rand INT_ABS_NOT0POS)
				else if (is_int_literal t1) then
					EQT_ELIM (ARITH_CONV ``0 < ^t1``)
				else
					ASSUME ``0i < ^t1``
			end
		else
			ASSUME ``0i < ^t1``;

(*--------------------------------------------------------------------------
 *  frac_not0_conv : term list -> conv
 *--------------------------------------------------------------------------*)

fun frac_not0_conv (asm_list:term list) (t1:term) =
	if (in_list asm_list ``~(^t1 = 0i)``) then
		ASSUME ``~(^t1 = 0i)``
	else
		if (is_comb t1) then
			let
				val (rator, rand) = dest_comb t1;
			in
				if (is_mult t1) then
					let
						val (fac1, fac2) = intSyntax.dest_mult t1;
						val fac1_thm = frac_not0_conv asm_list fac1;
						val fac2_thm = frac_not0_conv asm_list fac2;
					in
						LIST_MP [fac1_thm,fac2_thm] (SPECL[fac1,fac2] INT_NOT0_MUL)
					end
				else if (rator=``frac_dnm``) then
					MP (SPEC t1 INT_GT0_IMP_NOT0) (SPEC rand FRAC_DNMPOS)
				else if (rator=``SGN``) andalso (in_list asm_list ``~(^rand = 0)``) then
					UNDISCH (SPEC rand INT_NOT0_SGNNOT0)
				else if (is_int_literal t1) then
					EQT_ELIM (ARITH_CONV ``~(^t1 = 0i)``)
				else
					ASSUME ``~(^t1 = 0i)``
			end
		else
			ASSUME ``~(^t1 = 0i)``;

(*--------------------------------------------------------------------------
 *  FRAC_POS_TAC : term -> tactic
 *--------------------------------------------------------------------------*)

fun FRAC_POS_TAC term1 (asm_list, goal) =
	(ASSUME_TAC (frac_pos_conv asm_list term1)) (asm_list, goal);

(*--------------------------------------------------------------------------
 *  FRAC_NOT0_TAC : term -> tactic
 *--------------------------------------------------------------------------*)

fun FRAC_NOT0_TAC term1 (asm_list, goal) =
	(ASSUME_TAC (frac_not0_conv asm_list term1)) (asm_list, goal);

(*==========================================================================
 *  numerator and denominator extraction
 *==========================================================================*)

val FRAC_REP_ABS_SUBST =
let
  val lemma01 = prove( ``(\f. 0<SND f) (a1:int,b1:int) = (0<b1)``, BETA_TAC THEN REWRITE_TAC[SND]);
  val lemma02 = fst(EQ_IMP_RULE (ONCE_REWRITE_RULE[EQ_SYM_EQ] (SPEC ``(a:int,b:int)`` (ONCE_REWRITE_RULE [EQ_SYM_EQ] (CONJUNCT2 frac_bij)))))
in
  UNDISCH(ONCE_REWRITE_RULE [lemma01] lemma02)
end;

(*--------------------------------------------------------------------------
 *  NMR: thm
 *  |- !a b. 0 < b ==> (frac_nmr (abs_frac (a,b)) = a)
 *--------------------------------------------------------------------------*)

val NMR = store_thm("NMR", ``!a b. 0 < b ==> (frac_nmr (abs_frac (a,b)) = a)``,
	REPEAT STRIP_TAC THEN
	REWRITE_TAC[frac_nmr_def] THEN
	REWRITE_TAC[FRAC_REP_ABS_SUBST] );

(*--------------------------------------------------------------------------
 *  DNM: thm
 *  |- !a b. 0 < b ==> (frac_dnm (abs_frac (a,b)) = b)
 *--------------------------------------------------------------------------*)

val DNM = store_thm("DNM", ``!a b. 0 < b ==> (frac_dnm (abs_frac (a,b)) = b)``,
	REPEAT STRIP_TAC THEN
	REWRITE_TAC[frac_dnm_def] THEN
	REWRITE_TAC[FRAC_REP_ABS_SUBST] );

(*--------------------------------------------------------------------------
 *  FRAC_NMR_CONV: conv
 *
 *    frac_nmr (abs_frac (a1,b1))
 *   -----------------------------------------
 *    0 < b1 |- (frac_nmr (abs_frac (a1,b1)) = a1)
 *--------------------------------------------------------------------------*)

val FRAC_NMR_CONV:conv = fn term =>
let
	val (nmr,f) = dest_comb term;
	val (abs,args) = dest_comb f;
	val (a,b) = dest_pair args;
in
	UNDISCH_ALL(SPEC b (SPEC a NMR))
end
handle HOL_ERR _ => raise ERR "FRAC_NMR_CONV" "";


(*--------------------------------------------------------------------------
 *  FRAC_DNM_CONV: conv
 *
 *    frac_dnm (abs_frac (a1,b1))
 *   -----------------------------------------
 *    0 < b1 |- (frac_dnm (abs_frac (a1,b1)) = a1)
 *--------------------------------------------------------------------------*)

val FRAC_DNM_CONV:conv = fn term =>
let
	val (nmr,f) = dest_comb term;
	val (abs,args) = dest_comb f;
	val (a,b) = dest_pair args;
in
	UNDISCH_ALL(SPEC b (SPEC a DNM))
end
handle HOL_ERR _ => raise ERR "FRAC_DNM_CONV" "";

(*--------------------------------------------------------------------------
 *  frac_nmr_tac : term*term -> tactic
 *--------------------------------------------------------------------------*)

    fun frac_nmr_tac (asm_list:term list) (nmr,dnm) =
	let
		val asm_thm = frac_pos_conv asm_list dnm;
		val sub_thm = DISCH_ALL (FRAC_NMR_CONV ``nmr( abs_frac (^nmr, ^dnm) )``);
	in
		TRY (
			SUBST1_TAC (MP sub_thm asm_thm)
		)
	end;

(*--------------------------------------------------------------------------
 *  frac_dnm_tac : term*term -> tactic
 *--------------------------------------------------------------------------*)

fun frac_dnm_tac (asm_list:term list) (nmr,dnm) =
	let
		val asm_thm = frac_pos_conv asm_list dnm;
		val sub_thm = DISCH_ALL (FRAC_DNM_CONV ``dnm( abs_frac (^nmr, ^dnm) )``);
	in
		TRY (
			SUBST1_TAC (MP sub_thm asm_thm)
		)
	end;

(*--------------------------------------------------------------------------
 *  FRAC_NMRDNM_TAC : tactic
 *
 *  simplify resp. nmr(abs_frac(a1,b1)) to a1 and frac_dnm(abs_frac(a1,b1)) to b1
 *--------------------------------------------------------------------------*)

fun FRAC_NMRDNM_TAC (asm_list, goal) =
let
  val term_list = extract_frac_fun [``frac_nmr``,``frac_dnm``] goal
  val nmr_term_list  = map (fn (rator,nmr,dnm) => (nmr,dnm))
                           (filter (fn (a1,_,_) => a1=``frac_nmr``) term_list)
  val dnm_term_list  = map (fn (rator,nmr,dnm) => (nmr,dnm))
                           (filter (fn (a1,_,_) => a1=``frac_dnm``) term_list)
in
	(
		MAP_EVERY (frac_nmr_tac asm_list) nmr_term_list THEN
		MAP_EVERY (frac_dnm_tac asm_list) dnm_term_list THEN
		SIMP_TAC int_ss [INT_MUL_LID, INT_MUL_RID, INT_MUL_LZERO, INT_MUL_RZERO]
	) (asm_list,goal)
end
handle HOL_ERR _ => raise ERR "FRAC_NMRDNM_TAC" "";

(*==========================================================================
 *  calculation
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  FRAC_AINV_CALCULATE : thm
 *  |- !a1 b1. 0 < b1 ==>
 *	frac_ainv (abs_frac(a1,b1)) = abs_frac(~a1,b1)
 *--------------------------------------------------------------------------*)

val FRAC_AINV_CALCULATE = store_thm("FRAC_AINV_CALCULATE", ``!a1 b1. 0i<b1 ==> (frac_ainv (abs_frac(a1,b1)) = abs_frac(~a1,b1))``,
	REPEAT STRIP_TAC THEN
	REWRITE_TAC[frac_ainv_def] THEN
	SUBST_TAC[FRAC_NMR_CONV ``frac_nmr (abs_frac (a1,b1))``,FRAC_DNM_CONV ``frac_dnm (abs_frac (a1,b1))``] THEN
	RW_TAC int_ss [] );

(*--------------------------------------------------------------------------
 *  FRAC_MINV_CALCULATE : thm
 *  |- !a1 b1. (0i < b1) ==> ~(a1 = 0i) ==>
 *	frac_minv (abs_frac(a1,b1)) = if 0 < a1 then abs_frac(b1,a1) else abs_frac(~b1, ~a1) )
 *--------------------------------------------------------------------------*)

val FRAC_MINV_CALCULATE = store_thm("FRAC_MINV_CALCULATE", ``!a1 b1. (0i < b1) ==> ~(a1 = 0i) ==> (frac_minv (abs_frac(a1,b1)) = abs_frac(SGN(a1)*b1,ABS(a1)) )``,
	REPEAT STRIP_TAC THEN
	REWRITE_TAC[frac_minv_def, frac_sgn_def] THEN
	SUBST_TAC[FRAC_NMR_CONV ``frac_nmr (abs_frac (a1,b1))``,FRAC_DNM_CONV ``frac_dnm (abs_frac (a1,b1))``] THEN
	PROVE_TAC[] );

(*--------------------------------------------------------------------------
 *  FRAC_SGN_CALCULATE : thm
 *  |- !a1 b1. (0 < b1) ==>
 *	(frac_sgn (abs_frac(a1,b1)) = SGN a1)
 *--------------------------------------------------------------------------*)

val FRAC_SGN_CALCULATE = store_thm("FRAC_SGN_CALCULATE", ``!a1 b1. (0i < b1) ==> (frac_sgn (abs_frac(a1,b1)) = SGN a1)``,
	REPEAT STRIP_TAC THEN
	REWRITE_TAC[frac_sgn_def] THEN
	SUBST_TAC[FRAC_NMR_CONV ``frac_nmr (abs_frac (a1,b1))``,FRAC_DNM_CONV ``frac_dnm (abs_frac (a1,b1))``] THEN
	RW_TAC int_ss []);

(*--------------------------------------------------------------------------
 *  FRAC_ADD_CALCULATE : thm
 *  |- !a1 b1 a2 b2. 0 < b1 ==> 0 < b2 ==>
 *	frac_add (abs_frac(a1,b1)) (abs_frac(a2,b2)) = abs_frac( a1*b2+a2*b1 , b1*b2 )
 *--------------------------------------------------------------------------*)

val FRAC_ADD_CALCULATE = store_thm("FRAC_ADD_CALCULATE", ``!a1 b1 a2 b2. 0<b1 ==> 0<b2 ==> (frac_add (abs_frac(a1,b1)) (abs_frac(a2,b2)) = abs_frac( a1*b2+a2*b1 , b1*b2 ))``,
	REPEAT STRIP_TAC THEN
	REWRITE_TAC[frac_add_def] THEN
	SUBST_TAC[
		FRAC_NMR_CONV ``frac_nmr (abs_frac (a1,b1))``,FRAC_DNM_CONV ``frac_dnm (abs_frac (a1,b1))``,
		FRAC_NMR_CONV ``frac_nmr (abs_frac (a2,b2))``,FRAC_DNM_CONV ``frac_dnm (abs_frac (a2,b2))``] THEN
	RW_TAC int_ss [] );

(*--------------------------------------------------------------------------
 *  FRAC_SUB_CALCULATE : thm
 *  |- !a1 b1 a2 b2. 0 < b1 ==> 0 < b2 ==>
 *	frac_sub (abs_frac(a1,b1)) (abs_frac(a2,b2)) = abs_frac( a1*b2-a2*b1 , b1*b2 )
 *--------------------------------------------------------------------------*)

val FRAC_SUB_CALCULATE = store_thm("FRAC_SUB_CALCULATE", ``!a1 b1 a2 b2. 0<b1 ==> 0<b2 ==> (frac_sub (abs_frac(a1,b1)) (abs_frac(a2,b2)) = abs_frac( a1*b2-a2*b1 , b1*b2 ))``,
	REPEAT STRIP_TAC THEN
	REWRITE_TAC[frac_sub_def,frac_add_def,frac_ainv_def] THEN
	SUBST_TAC[
		FRAC_NMR_CONV ``frac_nmr (abs_frac (a1,b1))``,FRAC_DNM_CONV ``frac_dnm (abs_frac (a1,b1))``,
		FRAC_NMR_CONV ``frac_nmr (abs_frac (a2,b2))``,FRAC_DNM_CONV ``frac_dnm (abs_frac (a2,b2))``] THEN
	SUBST_TAC[FRAC_NMR_CONV ``frac_nmr (abs_frac (~a2,b2))``,FRAC_DNM_CONV ``frac_dnm (abs_frac (~a2,b2))``] THEN
	RW_TAC int_ss [INT_SUB_CALCULATE, INT_MUL_CALCULATE] );

(*--------------------------------------------------------------------------
 *  FRAC_MULT_CALCULATE : thm
 *  |- !a1 b1 a2 b2. 0 < b1 ==> 0 < b2 ==>
 *	frac_mul (abs_frac(a1,b1)) (abs_frac(a2,b2)) = abs_frac( a1*a2 , b1*b2 )
 *--------------------------------------------------------------------------*)

val FRAC_MULT_CALCULATE = store_thm("FRAC_MULT_CALCULATE", ``!a1 b1 a2 b2. 0<b1 ==> 0<b2 ==> (frac_mul (abs_frac(a1,b1)) (abs_frac(a2,b2)) = abs_frac( a1*a2 , b1*b2 ))``,
	REPEAT STRIP_TAC THEN
	REWRITE_TAC[frac_mul_def] THEN
	SUBST_TAC[
		FRAC_NMR_CONV ``frac_nmr (abs_frac (a1,b1))``,FRAC_DNM_CONV ``frac_dnm (abs_frac (a1,b1))``,
		FRAC_NMR_CONV ``frac_nmr (abs_frac (a2,b2))``,FRAC_DNM_CONV ``frac_dnm (abs_frac (a2,b2))``] THEN
	RW_TAC int_ss [] );

(*--------------------------------------------------------------------------
 *  FRAC_DIV_CALCULATE : thm
 *  |- !a1 b1 a2 b2. 0 < b1 ==> 0 < b2 ==> ~(a2 = 0) ==>
 *	frac_div (abs_frac(a1,b1)) (abs_frac(a2,b2)) = abs_frac( a1*SGN(a2)*b2 , b1*ABS(a2) )
 *--------------------------------------------------------------------------*)

val FRAC_DIV_CALCULATE = store_thm("FRAC_DIV_CALCULATE", ``!a1 b1 a2 b2. 0i<b1 ==> 0i<b2 ==> ~(a2=0i) ==> (frac_div (abs_frac(a1,b1)) (abs_frac(a2,b2)) = abs_frac( a1*SGN(a2)*b2 , b1*ABS(a2) ) )``,
	REPEAT STRIP_TAC THEN
	REWRITE_TAC[frac_div_def,frac_mul_def,frac_minv_def, frac_sgn_def] THEN
	SUBST_TAC[
		FRAC_NMR_CONV ``frac_nmr (abs_frac (a1,b1))``,FRAC_DNM_CONV ``frac_dnm (abs_frac (a1,b1))``,
		FRAC_NMR_CONV ``frac_nmr (abs_frac (a2,b2))``,FRAC_DNM_CONV ``frac_dnm (abs_frac (a2,b2))``] THEN
	ASSUME_TAC (UNDISCH_ALL (SPEC ``a2:int`` INT_ABS_NOT0POS)) THEN
	SUBST_TAC[FRAC_NMR_CONV ``frac_nmr (abs_frac (SGN a2 * b2,ABS a2))``,FRAC_DNM_CONV ``frac_dnm (abs_frac (SGN a2 * b2,ABS a2))``] THEN
	RW_TAC (int_ss ++ (simpLib.ac_ss [(INT_MUL_ASSOC, INT_MUL_COMM)])) [] );

(*==========================================================================
 *  basic theorems (associativity, commutativity, identity elements, ...)
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  FRAC_ADD_ASSOC: thm
 *  |- !a b c. frac_add a (frac_add b c) = frac_add (frac_add a b) c
 *
 *  FRAC_MULT_ASSOC: thm
 *  |- !a b c. frac_mul a (frac_mul b c) = frac_mul (frac_mul a b) c
 *--------------------------------------------------------------------------*)

val FRAC_ADD_ASSOC = store_thm("FRAC_ADD_ASSOC", ``!a b c. frac_add a (frac_add b c) = frac_add (frac_add a b) c``,
	REPEAT STRIP_TAC THEN REWRITE_TAC[frac_add_def]
	THEN FRAC_POS_TAC ``frac_dnm a * frac_dnm b``
	THEN FRAC_POS_TAC ``frac_dnm b * frac_dnm c``
	THEN RW_TAC int_ss [NMR,DNM]
	THEN FRAC_EQ_TAC THEN INT_RING_TAC );

val FRAC_MUL_ASSOC = store_thm("FRAC_MUL_ASSOC", ``!a b c. frac_mul a (frac_mul b c) = frac_mul (frac_mul a b) c``,
	REPEAT STRIP_TAC THEN REWRITE_TAC[frac_mul_def]
	THEN FRAC_POS_TAC ``frac_dnm a * frac_dnm b``
	THEN FRAC_POS_TAC ``frac_dnm b * frac_dnm c``
	THEN RW_TAC int_ss [NMR,DNM]
	THEN FRAC_EQ_TAC THEN INT_RING_TAC);

(*--------------------------------------------------------------------------
 *  FRAC_ADD_COMM: thm
 *  |- !a b c. frac_add a b = frac_add b a
 *
 *  FRAC_MUL_COMM: thm
 *  |- !a b c. frac_mul a b = frac_mul b a
 *--------------------------------------------------------------------------*)

val FRAC_ADD_COMM = store_thm("FRAC_ADD_COMM",``!a b. frac_add a b = frac_add b a``,
	REPEAT STRIP_TAC THEN
	REWRITE_TAC[frac_add_def]
	THEN FRAC_EQ_TAC
	THEN INT_RING_TAC );

val FRAC_MUL_COMM = store_thm("FRAC_MUL_COMM",``!a b. frac_mul a b = frac_mul b a``,
	REPEAT STRIP_TAC THEN
	REWRITE_TAC[frac_mul_def]
	THEN FRAC_EQ_TAC THEN
	INT_RING_TAC );

(*--------------------------------------------------------------------------
 *  FRAC_ADD_RID: thm
 *  |- !a. frac_add a frac_0 = a
 *
 *  FRAC_MUL_RID: thm
 *  |- !a. frac_mul a frac_1 = a
 *--------------------------------------------------------------------------*)

val FRAC_ADD_RID = store_thm("FRAC_ADD_RID",``!a. frac_add a frac_0 = a``,
	STRIP_TAC THEN
	REWRITE_TAC[frac_add_def, frac_0_def] THEN
	RW_TAC int_ss [NMR,DNM] THEN
	RW_TAC int_ss [FRAC] );

val FRAC_MUL_RID = store_thm("FRAC_MUL_RID",``!a. frac_mul a frac_1 = a``,
	STRIP_TAC THEN
	REWRITE_TAC[frac_mul_def, frac_1_def] THEN
	RW_TAC int_ss [NMR,DNM] THEN
	RW_TAC int_ss [FRAC] );

(*--------------------------------------------------------------------------
 *  FRAC_1_0: thm
 *  |- ~ (frac_1=frac_0)
 *--------------------------------------------------------------------------*)

val FRAC_1_0 = store_thm("FRAC_1_0", ``~ (frac_1=frac_0)``,
	REWRITE_TAC[frac_0_def, frac_1_def] THEN
	FRAC_POS_TAC ``1i`` THEN
	MATCH_MP_TAC (UNDISCH (UNDISCH (SPEC ``1i`` (SPEC ``0i`` (SPEC ``1i`` (SPEC ``1i`` FRAC_NOT_EQ_IMP)))))) THEN
	RW_TAC int_ss [] );

(*==========================================================================
 *  calculation rules of basic arithmetics
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  FRAC_AINV_0: thm
 *  |- frac_ainv frac_0 = frac_0
 *
 *  FRAC_AINV_AINV: thm
 *  |- !f1. frac_ainv (frac_ainv f1) = f1
 *
 *  FRAC_AINV_ADD: thm
 *  |- ! f1 f2. frac_ainv (frac_add f1 f2) = frac_add (frac_ainv f1) (frac_ainv f2)
 *
 *  FRAC_AINV_SUB: thm
 *  |- !a b. frac_sub a b = frac_ainv (frac_sub b a)
 *
 *  FRAC_AINV_LMUL: thm
 *  |- !f1 f2. frac_ainv (frac_mul f1 f2) = frac_mul f1 (frac_ainv f2)
 *
 *  FRAC_AINV_LMUL: thm
 *  |- !f1 f2. frac_ainv (frac_mul f1 f2) = frac_mul (frac_ainv f1) f2
 *--------------------------------------------------------------------------*)

val FRAC_AINV_0 = store_thm("FRAC_AINV_0", ``frac_ainv frac_0 = frac_0``,
	REWRITE_TAC[frac_0_def,frac_ainv_def] THEN
	FRAC_POS_TAC ``1i`` THEN
	RW_TAC int_ss [NMR,DNM] THEN
	RW_TAC int_ss [INT_NEG_0] );

val FRAC_AINV_AINV = store_thm("FRAC_AINV_AINV", ``!f1. frac_ainv (frac_ainv f1) = f1``,
	GEN_TAC THEN
	REWRITE_TAC[frac_ainv_def] THEN
	FRAC_POS_TAC ``frac_dnm f1`` THEN
	RW_TAC int_ss [NMR, DNM, INT_NEGNEG, FRAC] );

val FRAC_AINV_ADD = store_thm( "FRAC_AINV_ADD", ``! f1 f2. frac_ainv (frac_add f1 f2) = frac_add (frac_ainv f1) (frac_ainv f2)``,
	REPEAT GEN_TAC THEN
	REWRITE_TAC[frac_add_def, frac_ainv_def] THEN
	FRAC_POS_TAC ``frac_dnm f1`` THEN
	FRAC_POS_TAC ``frac_dnm f2`` THEN
	FRAC_POS_TAC ``frac_dnm f1 * frac_dnm f2`` THEN
	RW_TAC int_ss [NMR,DNM] THEN
	FRAC_EQ_TAC THENL
	[INT_RING_TAC,RW_TAC int_ss []] );

val FRAC_AINV_SUB = store_thm("FRAC_AINV_SUB", ``!f1 f2. frac_ainv (frac_sub f2 f1) = frac_sub f1 f2``,
	REPEAT GEN_TAC THEN
	REWRITE_TAC[frac_ainv_def, frac_add_def, frac_sub_def] THEN
	FRAC_POS_TAC ``frac_dnm f1`` THEN
	FRAC_POS_TAC ``frac_dnm f2`` THEN
	FRAC_POS_TAC ``frac_dnm f2 * frac_dnm f1`` THEN
	RW_TAC int_ss [NMR,DNM] THEN
	FRAC_EQ_TAC THEN
	INT_RING_TAC );

val FRAC_AINV_RMUL = store_thm("FRAC_AINV_RMUL", ``!f1 f2. frac_ainv (frac_mul f1 f2) = frac_mul f1 (frac_ainv f2)``,
	REPEAT GEN_TAC THEN
	REWRITE_TAC[frac_mul_def, frac_ainv_def] THEN
	FRAC_POS_TAC ``frac_dnm f2`` THEN
	FRAC_POS_TAC ``frac_dnm f1 * frac_dnm f2`` THEN
	RW_TAC int_ss [NMR,DNM] THEN
	FRAC_EQ_TAC THENL
	[
		integerRingLib.INT_RING_TAC
	,
		PROVE_TAC[]
	] );

val FRAC_AINV_LMUL = store_thm("FRAC_AINV_LMUL", ``!f1 f2. frac_ainv (frac_mul f1 f2) = frac_mul (frac_ainv f1) f2``,
	PROVE_TAC[FRAC_MUL_COMM, FRAC_AINV_RMUL] );

(*--------------------------------------------------------------------------
 *  FRAC_SUB_ADD: thm
 *  |- !a b c. frac_sub a (frac_add b c) = frac_sub (frac_sub a b) c
 *
 *  FRAC_SUB_SUB: thm
 *  |- !a b c. frac_sub a (frac_sub b c) = frac_add (frac_sub a b) c
 *--------------------------------------------------------------------------*)

val FRAC_SUB_ADD = store_thm("FRAC_SUB_ADD", ``!a b c. frac_sub a (frac_add b c) = frac_sub (frac_sub a b) c``,
	REPEAT STRIP_TAC THEN REWRITE_TAC[frac_add_def,frac_sub_def,frac_ainv_def] THEN
	FRAC_POS_TAC ``frac_dnm a * frac_dnm b`` THEN
	FRAC_POS_TAC ``frac_dnm b * frac_dnm c`` THEN
	FRAC_POS_TAC ``frac_dnm b`` THEN
	FRAC_POS_TAC ``frac_dnm c`` THEN
	RW_TAC int_ss [NMR,DNM] THEN
	FRAC_EQ_TAC THEN
	INT_RING_TAC );

val FRAC_SUB_SUB = store_thm("FRAC_SUB_SUB", ``!a b c. frac_sub a (frac_sub b c) = frac_add (frac_sub a b) c``,
	REPEAT STRIP_TAC THEN REWRITE_TAC[frac_add_def,frac_sub_def,frac_ainv_def] THEN
	FRAC_POS_TAC ``frac_dnm a * frac_dnm b`` THEN
	FRAC_POS_TAC ``frac_dnm b * frac_dnm c`` THEN
	FRAC_POS_TAC ``frac_dnm b`` THEN
	FRAC_POS_TAC ``frac_dnm c`` THEN
	RW_TAC int_ss [NMR,DNM]	THEN
	FRAC_EQ_TAC THEN
	INT_RING_TAC );

(*==========================================================================
 *  signum, absolute value
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  FRAC_SGN_TOTAL: thm
 *  |- !f. (frac_sgn f1 = ~1) \/ (frac_sgn f1 = 0) \/ (frac_sgn f1 = 1)
 *--------------------------------------------------------------------------*)

val FRAC_SGN_TOTAL = store_thm("FRAC_SGN_TOTAL", ``!f1. (frac_sgn f1 = ~1) \/ (frac_sgn f1 = 0) \/ (frac_sgn f1 = 1)``,
	REPEAT GEN_TAC THEN
	REWRITE_TAC[frac_sgn_def, SGN_def] THEN
	ASM_CASES_TAC ``frac_nmr f1 = 0`` THENL
	[
		PROVE_TAC[]
	,
		ASM_CASES_TAC ``frac_nmr f1 < 0`` THEN
		PROVE_TAC[]
	] );

(*--------------------------------------------------------------------------
 *  FRAC_SGN_POS: thm
 *  |- !f1. (frac_sgn f1 = 1) = 0 < nmr f1
 *--------------------------------------------------------------------------*)

val FRAC_SGN_POS = store_thm("FRAC_SGN_POS", ``!f1. (frac_sgn f1 = 1) = 0 < frac_nmr f1``,
	GEN_TAC THEN
	REWRITE_TAC[frac_sgn_def, SGN_def] THEN
	RW_TAC int_ss [] THENL
	[
		PROVE_TAC[INT_LT_GT]
	,
		PROVE_TAC[INT_LT_TOTAL]
	] );

(*--------------------------------------------------------------------------
 *  FRAC_SGN_NOT_NEG: thm
 *  |- !f1. ~(frac_sgn f1 = ~1) = (0 = frac_nmr f1) \/ (0 < frac_nmr f1)
 *--------------------------------------------------------------------------*)

val FRAC_SGN_NOT_NEG = store_thm("FRAC_SGN_NOT_NEG", ``!f1. ~(frac_sgn f1 = ~1) = (0 = frac_nmr f1) \/ (0 < frac_nmr f1)``,
	GEN_TAC THEN
	REWRITE_TAC[frac_sgn_def, SGN_def] THEN
	RW_TAC int_ss [] THENL
	[
		PROVE_TAC[INT_LT_GT]
	,
		PROVE_TAC[INT_LT_TOTAL]
	] );

(*--------------------------------------------------------------------------
 *  FRAC_SGN_NEG: thm
 *  |- ! f. ~frac_sgn (frac_ainv f) = frac_sgn f
 *--------------------------------------------------------------------------*)

val FRAC_SGN_NEG = store_thm("FRAC_SGN_NEG", ``! f. ~frac_sgn (frac_ainv f) = frac_sgn f``,
	GEN_TAC THEN
	ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
	REWRITE_TAC[frac_ainv_def] THEN
	ONCE_REWRITE_TAC[GSYM FRAC] THEN
	FRAC_POS_TAC ``frac_dnm f`` THEN
	RW_TAC int_ss [NMR,DNM] THEN
	REWRITE_TAC[frac_sgn_def, SGN_def] THEN
	SUBST_TAC[UNDISCH_ALL (SPEC ``frac_dnm f`` (SPEC ``frac_nmr f`` NMR))] THEN
	COND_CASES_TAC THENL
	[
		ASM_REWRITE_TAC[] THEN
		SUBST_TAC[UNDISCH_ALL (SPEC ``frac_dnm f`` (SPEC ``~0`` NMR))] THEN
		PROVE_TAC[INT_NEG_0]
	,
		SUBST_TAC[UNDISCH_ALL (SPEC ``frac_dnm f`` (SPEC ``~frac_nmr f`` NMR))] THEN
		REWRITE_TAC[INT_NEG_EQ,INT_NEG_LT0,INT_NEG_0] THEN
		COND_CASES_TAC THENL
		[
		ASSUME_TAC (UNDISCH (SPEC ``0i`` (SPEC  ``frac_nmr f`` INT_LT_GT))) THEN
		PROVE_TAC[]
		,
		ASSUME_TAC (SPEC ``frac_nmr f`` INT_NOTGT_IMP_EQLT) THEN
		UNDISCH_TAC ``~(frac_nmr f < 0) = (0 = frac_nmr f) \/ 0 < frac_nmr f`` THEN
		RW_TAC int_ss []
		]
	] );

(*--------------------------------------------------------------------------
 *  FRAC_SGN_IMP_EQGT: thm
 *  |- !f1 f2. frac_sub f1 f2 = frac_ainv (frac_sub f2 f1)
 *--------------------------------------------------------------------------*)

val FRAC_SGN_IMP_EQGT = store_thm("FRAC_SGN_IMP_EQGT",``!f1. ~(frac_sgn f1 = ~1) = (frac_sgn f1 = 0i) \/ (frac_sgn f1 = 1i)``,
	GEN_TAC THEN
	ASSUME_TAC (SPEC_ALL FRAC_SGN_TOTAL) THEN
	REPEAT (RW_TAC int_ss []) );

(*--------------------------------------------------------------------------
 *  FRAC_SGN_MUL: thm
 *  |- !f1 f2. frac_sgn (frac_mul f1 f2) = frac_sgn f1 * frac_sgn f2
 *--------------------------------------------------------------------------*)

val FRAC_SGN_MUL = store_thm("FRAC_SGN_MUL", ``!f1 f2. frac_sgn (frac_mul f1 f2) = frac_sgn f1 * frac_sgn f2``,
	REPEAT GEN_TAC THEN
	REWRITE_TAC[frac_mul_def, frac_sgn_def, SGN_def] THEN
	FRAC_POS_TAC ``frac_dnm f1 * frac_dnm f2`` THEN
	REWRITE_TAC[UNDISCH_ALL (SPEC ``frac_dnm f1 * frac_dnm f2`` (SPEC ``frac_nmr f1 * frac_nmr f2`` NMR))] THEN
	ASM_CASES_TAC ``frac_nmr f1=0i`` THEN
	ASM_CASES_TAC ``frac_nmr f1 < 0i`` THEN
	ASM_CASES_TAC ``frac_nmr f2=0i`` THEN
	ASM_CASES_TAC ``frac_nmr f2 < 0i`` THEN
	RW_TAC int_ss [INT_MUL_LZERO, INT_MUL_RZERO] THEN
	PROVE_TAC[INT_NO_ZERODIV,INT_MUL_SIGN_CASES,INT_LT_GT,INT_LT_TOTAL] );


(*--------------------------------------------------------------------------
 *  FRAC_ABS_SGN : thm
 *  |- !f1. ~(frac_nmr f1 = 0i) ==> (ABS (frac_sgn f1) = 1)
 *--------------------------------------------------------------------------*)

val FRAC_ABS_SGN = store_thm("FRAC_ABS_SGN", ``!f1. ~(frac_nmr f1 = 0i) ==> (ABS (frac_sgn f1) = 1i)``,
	GEN_TAC THEN
	REWRITE_TAC[frac_sgn_def, SGN_def] THEN
	RW_TAC int_ss [] THEN
	RW_TAC int_ss [INT_ABS] );

(*--------------------------------------------------------------------------
 *  FRAC_SGN_MUL : thm
 *  |- !f1 f2. frac_sgn (frac_mul f1 f2) = frac_sgn f1 * frac_sgn f2
 * TODO: was FRAC_SGN_MUL2
 *--------------------------------------------------------------------------*)

val FRAC_SGN_MUL = store_thm("FRAC_SGN_MUL2", ``!f1 f2. frac_sgn (frac_mul f1 f2) = frac_sgn f1 * frac_sgn f2``,
	REPEAT GEN_TAC THEN
	REWRITE_TAC[frac_sgn_def, frac_mul_def] THEN
	FRAC_NMRDNM_TAC THEN
	PROVE_TAC[INT_SGN_MUL2] );

(*--------------------------------------------------------------------------
 *  FRAC_SGN_MUL : thm
 *  |- !f1 f2 i1 i2. (frac_sgn f1 = i1) ==> (frac_sgn f2 = i2) ==>
 *	(frac_sgn (frac_mul f1 f2) = i1 * i2)
 * deleted
 *--------------------------------------------------------------------------*)

(*val FRAC_SGN_MUL = store_thm("FRAC_SGN_MUL", ``!f1 f2 i1 i2. (frac_sgn f1 = i1) ==> (frac_sgn f2 = i2) ==> (frac_sgn (frac_mul f1 f2) = i1 * i2)``,
	REPEAT GEN_TAC THEN
	REWRITE_TAC[frac_sgn_def] THEN
	FRAC_CALC_TAC THEN
	FRAC_NMRDNM_TAC THEN
	PROVE_TAC[INT_SGN_MUL] );*)

(*--------------------------------------------------------------------------
 *  FRAC_SGN_CASES : thm
 *  |- !f1 P.
 *	((frac_sgn f1 = ~1) ==> P) /\
 *	((frac_sgn f1 = 0i) ==> P) /\
 *	((frac_sgn f1 = 1i) ==> P) ==> P
 *--------------------------------------------------------------------------*)

val FRAC_SGN_CASES = store_thm("FRAC_SGN_CASES", ``!f1 P. ((frac_sgn f1 = ~1) ==> P) /\ ((frac_sgn f1 = 0i) ==> P) /\ ((frac_sgn f1 = 1i) ==> P) ==> P``,
	REPEAT GEN_TAC THEN
	ASM_CASES_TAC ``frac_sgn f1 = ~1`` THEN
	ASM_CASES_TAC ``frac_sgn f1 = 0i`` THEN
	ASM_CASES_TAC ``frac_sgn f1 = 1i`` THEN
	UNDISCH_ALL_TAC THEN
	PROVE_TAC[FRAC_SGN_TOTAL] );

(*--------------------------------------------------------------------------
 *  FRAC_SGN_AINV : thm
 *  |- !f1. ~frac_sgn (frac_ainv f1) = frac_sgn f1
 *--------------------------------------------------------------------------*)

val FRAC_SGN_AINV = store_thm("FRAC_SGN_AINV", ``!f1. ~frac_sgn (frac_ainv f1) = frac_sgn f1``,
	GEN_TAC THEN
	REWRITE_TAC[frac_sgn_def, frac_ainv_def] THEN
	FRAC_NMRDNM_TAC THEN
	REWRITE_TAC[SGN_def] THEN
	REWRITE_TAC[INT_NEG_EQ, INT_NEG_0] THEN
	SUBGOAL_THEN ``(~frac_nmr f1 < 0) = (0 < frac_nmr f1)`` SUBST1_TAC THENL
	[
		EQ_TAC THEN
		STRIP_TAC THEN
		ONCE_REWRITE_TAC[GSYM INT_LT_NEG] THEN
		PROVE_TAC[INT_NEG_0, INT_NEGNEG]
	,
		RW_TAC int_ss [] THEN
		PROVE_TAC[INT_LT_ANTISYM, INT_LT_TOTAL]
	] );



(*==========================================================================
 *  one-to-one and onto theorems
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  FRAC_AINV_ONE_ONE : thm
 *  |- ONE_ONE frac_ainv
 *--------------------------------------------------------------------------*)

val FRAC_AINV_ONEONE = store_thm("FRAC_AINV_ONEONE", ``ONE_ONE frac_ainv``,
	REWRITE_TAC[ONE_ONE_DEF] THEN
	BETA_TAC THEN
	REPEAT GEN_TAC THEN
	REWRITE_TAC[frac_ainv_def] THEN
	FRAC_POS_TAC ``frac_dnm x1`` THEN
	FRAC_POS_TAC ``frac_dnm x2`` THEN
	REWRITE_TAC[UNDISCH_ALL (SPECL[``~frac_nmr x1``,``frac_dnm x1``,``~frac_nmr x2``,``frac_dnm x2``] FRAC_EQ)] THEN
	REWRITE_TAC[INT_EQ_NEG] THEN
	SUBST_TAC[SPEC ``x1:frac`` (GSYM FRAC), SPEC ``x2:frac`` (GSYM FRAC)] THEN
	RW_TAC bool_ss [NMR,DNM] );

(*--------------------------------------------------------------------------
 *  FRAC_AINV_ONTO : thm
 *  |- ONTO frac_ainv
 *--------------------------------------------------------------------------*)

val FRAC_AINV_ONTO = store_thm("FRAC_AINV_ONTO", ``ONTO frac_ainv``,
	REWRITE_TAC[ONTO_DEF] THEN
	BETA_TAC THEN
	GEN_TAC THEN
	EXISTS_TAC ``frac_ainv y`` THEN
	PROVE_TAC[FRAC_AINV_AINV] );



(*==========================================================================
 *  encode whether a fraction is defined or not in the syntax
 *==========================================================================*)


(*==========================================================================
 *  compute the numerator and denominator of a fraction
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  FRAC_NMR_SAVE: thm
 *  |- !a1 b1. frac_nmr( frac_save a1 b1 ) = a1
 *
 *  FRAC_DNM_SAVE: thm
 *  |- !a1 b1. frac_dnm( frac_save a1 b1 ) = &b1 + 1i
 *--------------------------------------------------------------------------*)

val FRAC_NMR_SAVE = store_thm("FRAC_NMR_SAVE", ``!a1 b1. frac_nmr( frac_save a1 b1 ) = a1``,
	REPEAT GEN_TAC THEN
	REWRITE_TAC[frac_save_def] THEN
	ASSUME_TAC (ARITH_PROVE ``0i < &b1 + 1``) THEN
	PROVE_TAC[NMR] );

val FRAC_DNM_SAVE = store_thm("FRAC_DNM_SAVE", ``!a1 b1. frac_dnm( frac_save a1 b1 ) = &b1 + 1i``,
	REPEAT GEN_TAC THEN
	REWRITE_TAC[frac_save_def] THEN
	ASSUME_TAC (ARITH_PROVE ``0i < &b1 + 1``) THEN
	PROVE_TAC[DNM] );

(*--------------------------------------------------------------------------
 *  FRAC_0_SAVE: thm
 *  |- frac_0 = frac_save 0 0
 *
 *  FRAC_1_SAVE: thm
 *  |- frac_1 = frac_save 1 0
 *--------------------------------------------------------------------------*)

val FRAC_0_SAVE = store_thm("FRAC_0_SAVE", ``frac_0 = frac_save 0 0``,
	REPEAT GEN_TAC THEN
	REWRITE_TAC[frac_0_def, frac_save_def] THEN
	ASSUME_TAC (ARITH_PROVE ``0i < &b1 + 1``) THEN
	FRAC_EQ_TAC THEN
	ARITH_TAC );

val FRAC_1_SAVE = store_thm("FRAC_1_SAVE", ``frac_1 = frac_save 1 0``,
	REPEAT GEN_TAC THEN
	REWRITE_TAC[frac_1_def, frac_save_def] THEN
	ASSUME_TAC (ARITH_PROVE ``0i < &b1 + 1``) THEN
	FRAC_EQ_TAC THEN
	ARITH_TAC );

(*--------------------------------------------------------------------------
 *  FRAC_AINV_SAVE: thm
 *  |- !a1 b1. frac_ainv (frac_save a1 b1) = frac_save (~a1) b1
 *
 *  RAT_MINV_SAVE: thm
 *  |- !a1 b1. ~(abs_rat (frac_save a1 b1) = rat_0) ==>
 *		(rat_minv (abs_rat (frac_save a1 b1)) =
 *		 abs_rat( frac_save (SGN a1 * (& b1 + 1)) (Num (ABS a1 - 1))) )
 *--------------------------------------------------------------------------*)

val FRAC_AINV_SAVE = store_thm("FRAC_AINV_SAVE", ``!a1 b1. frac_ainv (frac_save a1 b1) = frac_save (~a1) b1``,
	REPEAT GEN_TAC THEN
	REWRITE_TAC[frac_ainv_def, frac_save_def] THEN
	ASSUME_TAC (ARITH_PROVE ``0i < &b1 + 1``) THEN
	FRAC_NMRDNM_TAC THEN
	FRAC_EQ_TAC );


val FRAC_MINV_SAVE = store_thm("FRAC_MINV_SAVE",``!a1 b1. ~(a1=0) ==> (frac_minv (frac_save a1 b1) = frac_save (SGN a1 * (&b1 + 1)) (Num (ABS a1 - 1)))``,
	REPEAT STRIP_TAC THEN
	REWRITE_TAC[frac_minv_def, frac_sgn_def, frac_save_def] THEN
	ASSUME_TAC (ARITH_PROVE ``0i < &b1 + 1``) THEN
	ASSUME_TAC (ARITH_PROVE ``0i < & (Num (ABS a1 - 1)) + 1``) THEN
	FRAC_NMRDNM_TAC THEN
	FRAC_EQ_TAC THEN
	RW_TAC int_ss [SGN_def, GSYM INT_EQ_SUB_RADD] THEN
	ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
	REWRITE_TAC[INT_OF_NUM] THEN
	ARITH_TAC );


(*--------------------------------------------------------------------------
 *  FRAC_ADD_SAVE: thm
 *  |- !a1 b1 a2 b2.
 *	frac_add (frac_save a1 b1) (frac_save a2 b2) =
 *	frac_save (a1 * &b2 + a2 * &b1 + a1 + a2) (b1 * b2 + b1 + b2)
 *
 *  FRAC_MUL_SAVE: thm
 *  |- !a1 b1 a2 b2.
 *	frac_mul (frac_save a1 b1) (frac_save a2 b2) =
 *	frac_save (a1 * a2) (b1 * b2 + b1 + b2)
 *--------------------------------------------------------------------------*)

val FRAC_ADD_SAVE = store_thm(
  "FRAC_ADD_SAVE",
  ``!a1 b1 a2 b2.
         frac_add (frac_save a1 b1) (frac_save a2 b2) =
         frac_save (a1 * &b2 + a2 * &b1 + a1 + a2) (b1 * b2 + b1 + b2)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[frac_add_def, frac_save_def] THEN
  ASSUME_TAC (ARITH_PROVE ``0i < &b1 + 1``) THEN
  ASSUME_TAC (ARITH_PROVE ``0i < &b2 + 1``) THEN
  FRAC_NMRDNM_TAC THEN
  FRAC_EQ_TAC THEN
  SIMP_TAC (srw_ss()) [INT_LDISTRIB, INT_RDISTRIB, GSYM INT_ADD,
                       AC INT_ADD_COMM INT_ADD_ASSOC]);

val FRAC_MUL_SAVE = store_thm(
  "FRAC_MUL_SAVE",
  ``!a1 b1 a2 b2. frac_mul (frac_save a1 b1) (frac_save a2 b2) =
                  frac_save (a1 * a2) (b1 * b2 + b1 + b2)``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[frac_mul_def, frac_save_def] THEN
  ASSUME_TAC (ARITH_PROVE ``0i < &b1 + 1``) THEN
  ASSUME_TAC (ARITH_PROVE ``0i < &b2 + 1``) THEN
  FRAC_NMRDNM_TAC THEN
  FRAC_EQ_TAC THEN
  REWRITE_TAC[INT_ADD_CALCULATE, INT_MUL_CALCULATE, INT_EQ_CALCULATE] THEN
  RW_TAC arith_ss [arithmeticTheory.LEFT_ADD_DISTRIB,
                   arithmeticTheory.RIGHT_ADD_DISTRIB] THEN
  ARITH_TAC);

(*==========================================================================
 * end of theory
 *==========================================================================*)

val _ = export_theory();

