structure ratLib :> ratLib =
struct

open HolKernel boolLib Parse bossLib;

(* interactive mode
app load ["simpLib", "pairLib", "intExtensionTheory",
	"jbUtils", "schneiderUtils", "intLib",
	"fracTheory", "fracLib", "fracUtils",
	"ratTheory", "ratUtils", "integerRingLib"];
*)

open
	simpLib pairLib integerTheory intLib intExtensionTheory
	jbUtils schneiderUtils
	fracTheory fracLib fracUtils
	ratTheory ratUtils integerRingLib ratSyntax;

(*--------------------------------------------------------------------------
 *  imported from fracLib
 *--------------------------------------------------------------------------*)

val FRAC_EQ_TAC = fracLib.FRAC_EQ_TAC;
val FRAC_POS_TAC = fracLib.FRAC_POS_TAC;

(*==========================================================================
 * equivalence of rational numbers
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  RAT_EQ_CONV : conv
 *
 *    abs_rat f1 = abs_rat f2
 *   ----------------------------------------------------
 *    |- (abs_rat f1 = abs_rat f2)
 *	= (nmr f1 * dnm f2 = nmr f2 * dnm f1) : thm
 *--------------------------------------------------------------------------*)

val RAT_EQ_CONV:conv = fn term1 =>
let
	val eqn = dest_neg term1;
	val (lhs,rhs) = dest_eq eqn;
	val (lhc, f1) = dest_comb lhs;
	val (rhc, f2) = dest_comb rhs;
in
	UNDISCH_ALL (SPECL[f1,f2] RAT_EQ)
end
handle HOL_ERR _ => raise ERR "RAT_EQ_CONV" "";


(*--------------------------------------------------------------------------
 *  RAT_EQ_TAC : tactic
 *
 *     A ?- abs_rat f1 = abs_rat f2
 *   =========================================  RAT_EQ_TAC
 *     A ?- nmr f1 * dnm f2 = nmr f2 * dnm f1
 *--------------------------------------------------------------------------*)

fun RAT_EQ_TAC (asm_list,goal) =
	(SUBST_TAC[RAT_EQ_CONV goal]) (asm_list,goal)
handle HOL_ERR _ => raise ERR "RAT_EQ_TAC" "";


(*==========================================================================
 * associativity, commutativity
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  RAT_ADDAC_TAC : tactic
 *  RAT_MULAC_TAC : tactic
 *--------------------------------------------------------------------------*)

val RAT_ADDAC_CONV = AC_CONV (RAT_MUL_ASSOC, RAT_MUL_COMM);
val RAT_MULAC_CONV = AC_CONV (RAT_MUL_ASSOC, RAT_MUL_COMM);

fun RAT_ADDAC_TAC t1 = SUBST1_TAC (EQT_ELIM (AC_CONV (RAT_ADD_ASSOC, RAT_ADD_COMM) t1));
fun RAT_MULAC_TAC t1 = SUBST1_TAC (EQT_ELIM (AC_CONV (RAT_MUL_ASSOC, RAT_MUL_COMM) t1));

(*==========================================================================
   manipulation of terms/equations
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  RAT_ADDSUB_TAC : tactic
 *--------------------------------------------------------------------------*)

fun RAT_ADDSUB_TAC t1 t2 = SUBST1_TAC (SUBS [SPEC t2 (GSYM RAT_ADD_RINV)] (SPEC t1 (GSYM RAT_ADD_RID)));

(*--------------------------------------------------------------------------
 *  RAT_EQ_LMUL_TAC : tactic
 *--------------------------------------------------------------------------*)

fun RAT_EQ_LMUL_TAC term1 (asm_list,goal) =
let
	val (eq_lhs,eq_rhs) = dest_eq goal;
in
	SUBST_TAC[GSYM (UNDISCH_ALL (SPECL [eq_lhs,eq_rhs,term1] RAT_EQ_LMUL))]
end
	(asm_list,goal)
handle HOL_ERR _ => raise ERR "RAT_EQ_RMUL_TAC" "";

(*--------------------------------------------------------------------------
 *  RAT_EQ_RMUL_TAC : tactic
 *--------------------------------------------------------------------------*)

fun RAT_EQ_RMUL_TAC term1 (asm_list,goal) =
let
	val (eq_lhs,eq_rhs) = dest_eq goal;
in
	SUBST_TAC[GSYM (UNDISCH_ALL (SPECL [eq_lhs,eq_rhs,term1] RAT_EQ_RMUL))]
end
	(asm_list,goal)
handle HOL_ERR _ => raise ERR "RAT_EQ_RMUL_TAC" "";

(*==========================================================================
   calculation
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  RAT_CALCULATE_rewrites : thm list
 *--------------------------------------------------------------------------*)

val RAT_CALCULATE_rewrites =
	[RAT_ADD_CALCULATE, RAT_SUB_CALCULATE, RAT_MUL_CALCULATE, RAT_DIV_CALCULATE, RAT_AINV_CALCULATE, RAT_MINV_CALCULATE, rat_0_def, rat_1_def];

(*--------------------------------------------------------------------------
 *  rat_calculate_table : (term * thm) list
 *--------------------------------------------------------------------------*)

val rat_calculate_table = [
	( ``rat_0``,	rat_0_def ),
	( ``rat_1``,	rat_1_def ),
	( ``rat_ainv``,	RAT_AINV_CALCULATE ),
	( ``rat_minv``,	RAT_MINV_CALCULATE ),
	( ``rat_add``,	RAT_ADD_CALCULATE ),
	( ``rat_sub``,	RAT_SUB_CALCULATE ),
	( ``rat_mul``,	RAT_MUL_CALCULATE ),
	( ``rat_div``,	RAT_DIV_CALCULATE )
];

(*--------------------------------------------------------------------------
 *  RAT_CALC_CONV : conv
 *
 *    r1
 *   ---------------------
 *    |- r1 = abs_rat(f1)
 *--------------------------------------------------------------------------*)


fun RAT_CALC_CONV (t1:term) =
let
	val thm = REFL t1;
	val (top_rator, top_rands) = strip_comb t1;
	val calc_table_entry = List.find (fn x => fst(x)= top_rator) rat_calculate_table;
in
	(* do nothing if term is already in the form abs_rat(...) *)
	if top_rator=``abs_rat`` then
		thm
	(* if it is a numeral, simply rewrite it *)
	else if (top_rator=``rat_of_num``) then
		SUBST [``x:rat`` |-> SPEC (rand t1) (RAT_OF_NUM_CALCULATE)] ``^t1 = x:rat`` thm
	(* if there is an entry in the calculation table, calculate it *)
	else if (isSome calc_table_entry) then
		let
			val arg_thms = map RAT_CALC_CONV top_rands;
			val arg_fracs = map (fn x => rand(rhs(concl x))) arg_thms;
			val arg_vars = map (fn x => genvar ``:rat``) arg_thms;

			val subst_list = map (fn x => fst(x) |-> snd(x)) (ListPair.zip (arg_vars,arg_thms));
			(* subst_term: t1 = top_rator arg_vars[1] ... arg_vars[n] *)
			val subst_term =  mk_eq (t1 , list_mk_comb (top_rator,arg_vars))

			val thm1 = SUBST subst_list subst_term thm;
			val (thm1_lhs, thm1_rhs) = dest_eq(concl thm1);
			val thm1_lhs_var = genvar ``:rat``;

			val calc_thm = snd (valOf( calc_table_entry ));
		in
			SUBST [thm1_lhs_var |-> UNDISCH_ALL (SPECL arg_fracs calc_thm)] ``^thm1_lhs = ^thm1_lhs_var`` thm1
		end
	(* otherwise: applying r = abs_rat(rep_rat r)) always works *)
	else
		SUBST [``x:rat`` |-> SPEC t1 (GSYM RAT)] ``^t1 = x:rat`` thm
end;

(* ---------- test cases ---------- *
	RAT_CALC_CONV ``abs_rat(f1)``;
	RAT_CALC_CONV ``r1:rat``;
	RAT_CALC_CONV ``rat_ainv ( abs_rat(f1) )``
	RAT_CALC_CONV ``rat_add (abs_rat(f1)) (abs_rat(f2))``;
	RAT_CALC_CONV ``rat_add r1 ( rat_sub (abs_rat(abs_frac(4i,5i))) r2)``;
	RAT_CALC_CONV ``rat_mul r1 ( rat_div (abs_rat(abs_frac(4i,5i))) r2)``;
	RAT_CALC_CONV ``rat_add rat_0 rat_1``;
 * ---------- test cases ---------- *)


(*--------------------------------------------------------------------------
 *  RAT_CALCTERM_TAC : term -> tactic
 *
 *  calculates the value of t1:rat
 *--------------------------------------------------------------------------*)

fun RAT_CALCTERM_TAC (t1:term) (asm_list,goal) =
	let
		val calc_thm = RAT_CALC_CONV t1;
		val (calc_asms, calc_concl) = dest_thm calc_thm;
	in
		(
			MAP_EVERY ASSUME_TAC (map (fn x => TAC_PROOF ((asm_list,x), RW_TAC intLib.int_ss [FRAC_DNMPOS,INT_MUL_POS_SIGN,INT_NOTPOS0_NEG,INT_NOT0_MUL,INT_GT0_IMP_NOT0,INT_ABS_NOT0POS])) calc_asms) THEN
			SUBST_TAC[calc_thm]
		) (asm_list,goal)
	end
handle HOL_ERR _ => raise ERR "RAT_CALCTERM_TAC" "";


(*--------------------------------------------------------------------------
 *  RAT_STRICT_CALC_TAC : tactic
 *
 *  calculates the value of all subterms (of type ``:rat``)
 *--------------------------------------------------------------------------*)

fun RAT_STRICT_CALC_TAC (asm_list,goal) =
	let
		val rat_terms = extract_rat goal;
		val calc_thms = map RAT_CALC_CONV rat_terms;
		val calc_asms = list_xmerge (map (fn x => fst (dest_thm x)) calc_thms);
	in
		(
			MAP_EVERY ASSUME_TAC (map (fn x => TAC_PROOF ((asm_list,x), RW_TAC intLib.int_ss [FRAC_DNMPOS,INT_MUL_POS_SIGN,INT_NOTPOS0_NEG,INT_NOT0_MUL,INT_GT0_IMP_NOT0,INT_ABS_NOT0POS])) calc_asms) THEN
			SUBST_TAC calc_thms
		) (asm_list,goal)
	end
handle HOL_ERR _ => raise ERR "RAT_STRICT_CALC_TAC" "";

(*--------------------------------------------------------------------------
 *  RAT_CALC_TAC : tactic
 *
 *  calculates the value of all subterms (of type ``:rat``)
 *  assumptions that were needed for the simplification are added to the goal
 *--------------------------------------------------------------------------*)

fun RAT_CALC_TAC (asm_list,goal) =
	let
			(* extract terms of type ``:rat`` *)
		val rat_terms = extract_rat goal;
			(* build conversions *)
		val calc_thms = map RAT_CALC_CONV rat_terms;
			(* split list into assumptions and conclusions *)
		val (calc_asmlists, calc_concl) = ListPair.unzip (map (fn x => dest_thm x) calc_thms);
			(* merge assumptions lists *)
		val calc_asms = list_xmerge calc_asmlists;
			(* function to prove an assumption, TODO: fracLib benutzen *)
		val gen_thm = (fn x => TAC_PROOF ((asm_list,x), RW_TAC intLib.int_ss [] ));
			(* try to prove assumptions *)
		val prove_list = List.map (total gen_thm) calc_asms;
			(* combine assumptions and their proofs *)
		val list1 = ListPair.zip (calc_asms,prove_list);
			(* partition assumptions into proved assumptions and assumptions to be proved *)
		val list2 = partition (fn x => isSome (snd x)) list1;
		val asms_toprove = map fst (snd list2);
		val asms_proved = map (fn x => valOf (snd x)) (fst list2);
			(* generate new subgoal goal *)
		val subst_goal = snd (dest_eq (snd (dest_thm (ONCE_REWRITE_CONV calc_thms goal))));
		val subgoal = (list_mk_conj (asms_toprove @ [subst_goal]) );
		val mp_thm = TAC_PROOF
			(
				(asm_list, mk_imp (subgoal,goal))
			,
				STRIP_TAC THEN
				MAP_EVERY ASSUME_TAC asms_proved THEN
				ONCE_REWRITE_TAC calc_thms THEN
				PROVE_TAC []
			);
	in
			( [(asm_list,subgoal)], fn (thms:thm list) => MP mp_thm (hd thms) )
	end
handle HOL_ERR _ => raise ERR "RAT_CALC_TAC" "";

(*--------------------------------------------------------------------------
 *  RAT_CALCEQ_TAC : tactic
 *--------------------------------------------------------------------------*)

val RAT_CALCEQ_TAC =
	RAT_CALC_TAC THEN
	FRAC_CALC_TAC THEN
	REWRITE_TAC[RAT_EQ] THEN
	FRAC_NMRDNM_TAC THEN
	INT_RING_TAC;


(*==========================================================================
 * transformation of rational numbers into "defined rational numbers"
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  RAT_SAVE_TAC : term -> tactic
 *--------------------------------------------------------------------------*)

fun RAT_SAVE_TAC t1 (asm_list, goal) =
	let val subst_thm = SPEC t1 RAT_SAVE in
		(ASSUME_TAC subst_thm THEN LEFT_EXISTS_TAC THEN LEFT_EXISTS_TAC THEN FILTER_ASM_REWRITE_TAC (fn t => not (mem t asm_list)) [] THEN POP_NO_TAC 0) (asm_list, goal)
	end;

(*--------------------------------------------------------------------------
 *  RAT_SAVE_ALLVARS_TAC : tactic
 *--------------------------------------------------------------------------*)

fun RAT_SAVE_ALLVARS_TAC (asm_list, goal) =
	MAP_EVERY RAT_SAVE_TAC (extract_rat_vars goal) (asm_list, goal);


(*==========================================================================
 * elimination of rat_minv_terms
 *==========================================================================*)

(*--------------------------------------------------------------------------
 * rat_eq_rmul_list_conv: term list -> term -> thm
 *--------------------------------------------------------------------------*)

fun rat_eq_rmul_list_conv (factor_list:term list) (equation:term) =
let
	val (lhs,rhs) = dest_eq equation;
	val product = list_rat_mul factor_list;
in
	REWRITE_RULE[RAT_MUL_ASSOC, RAT_RDISTRIB] (GSYM (UNDISCH( SPECL[lhs,rhs,product] RAT_EQ_RMUL) ))
end;

(*--------------------------------------------------------------------------
 * rat_eliminate_minv_conv: term -> thm
 *--------------------------------------------------------------------------*)

fun rat_eliminate_minv_conv (t1:term) =
let
	(* update the appropiate counter : each element of the list counts the number of occurences of a given term and its multiplicative inverse *)
	fun insert_into_factor_list (term1:term) (i1:int,i2:int) (h::t) =
		if( fst h = term1 ) then
			(fst h, (fst (snd h)+i1, snd (snd h)+i2) )::t
		else
			h::(insert_into_factor_list term1 (i1,i2) t)
	| insert_into_factor_list term1 (i1:int,i2:int) [] = [(term1,(i1,i2))]
	(* count all factors *)
	fun count_factors l0 (h::t) =
		if (is_rat_minv h) then
			count_factors (insert_into_factor_list (dest_rat_minv h) (0,1) l0) t
		else
			count_factors (insert_into_factor_list h (1,0) l0) t
	| count_factors l0 [] = l0;
	(* generate the part of a product (product of the same terms and multiplicative inverses resp.) *)
	fun gen_product_part (term1, (i1,i2)) =
		if (i1>0) andalso (i2>0) then
			``rat_minv ^term1 * ^term1``::gen_product_part(term1,(i1-1,i2-1))
		else if (i1=0) andalso (i2>0) then
			``rat_minv ^term1``::gen_product_part (term1,(i1,i2-1))
		else if (i1>0) andalso (i2=0) then
			``^term1``::gen_product_part (term1,(i1-1,i2))
		else
			[];
	(* generate the whole product *)
	fun reorder_product (h::t) = gen_product_part h::reorder_product t
	| reorder_product [] = [];

	(* extract all fractors of the product given by term t1 *)
	val factors = strip_rat_mul t1;
	(* filter out all multiplicative inverses *)
	val minv_factors = filter is_rat_minv factors;
	(* generate the new product in which factors and their corresponding multiplicative inverses have been cancelled *)
	val desired_product = list_rat_mul (map list_rat_mul (reorder_product (count_factors [] factors)));
in
	(* this is basically proven by the specialised versions of RAT_MUL_LINV *)
	((fn tx => EQT_ELIM (RAT_MULAC_CONV ``^tx = ^desired_product``)) THENC (REWRITE_CONV (RAT_MUL_LID::RAT_MUL_RID::(map (fn fx=> UNDISCH (SPEC fx RAT_MUL_LINV)) (map dest_rat_minv minv_factors))))) t1
end;


(*--------------------------------------------------------------------------
 * rat_eliminate_minv_eq_conv: term -> thm
 *--------------------------------------------------------------------------*)

fun rat_eliminate_minv_eq_conv (t1:term) =
let
	val (lhs,rhs) = dest_eq t1;
	(* extract all summands *)
	val summands = (strip_rat_add lhs) @ (strip_rat_add rhs);
	(* generate elimination theorems for all of them *)
	val reorder_thms = map rat_eliminate_minv_conv summands;
in
	(* apply all theorems - TODO: only rewrite on the right side!  *)
	ONCE_REWRITE_CONV reorder_thms (t1:term)
end;


(*--------------------------------------------------------------------------
 * RAT_ELIMINATE_MINV_EQ_CONV: term -> thm
 *--------------------------------------------------------------------------*)

fun RAT_ELIMINATE_MINV_EQ_CONV (t1:term) =
let
	(* generate elimination theorem *)
	val thm1 = (rat_eq_rmul_list_conv (map dest_rat_minv (extract_rat_minv t1)) THENC rat_eliminate_minv_eq_conv) t1;
in
	(* simplify assumption list *)
	UNDISCH_ALL (IMP_AND_RULE (REWRITE_RULE[RAT_NO_ZERODIV_NEG] (DISCH_ALL thm1 )))
end;

(*--------------------------------------------------------------------------
 * RAT_ELIMINATE_MINV_CONV: term -> thm
 *--------------------------------------------------------------------------*)

fun RAT_ELIMINATE_MINV_CONV (t1:term) =
	ONCE_REWRITE_CONV (map RAT_ELIMINATE_MINV_EQ_CONV (extract_rat_equations t1)) t1;

(*--------------------------------------------------------------------------
 * RAT_ELIMINATE_MINV_TAC: tactic -> thm
 *--------------------------------------------------------------------------*)

val RAT_ELIMINATE_MINV_TAC = CONV_TAC RAT_ELIMINATE_MINV_CONV;



(*==========================================================================
 * calculation of rational expressions
 *==========================================================================*)

(*--------------------------------------------------------------------------
 * rewrite rules to calculate rational expressions
 *--------------------------------------------------------------------------*)

(* rewrites to calculate operations on integers - (TODO) remove dependencies: numRingTheory and integerRingTheory *)
local open numeralTheory numRingTheory integerRingTheory in
	val num_rewrites = [numeral_distrib, numeral_eq, numeral_suc, numeral_iisuc, numeral_add, numeral_mult, iDUB_removal, ISPEC(``ALT_ZERO``) REFL_CLAUSE, ISPEC(``0:num``) REFL_CLAUSE ];
	val int_rewrites = [int_calculate, INT_0, INT_1, numeral_lt, numeral_lte, numeral_sub, iSUB_THM, AND_CLAUSES, SGN_def] @ num_rewrites
end;
(* rewrites to calculate operations on fractions *)
val frac_rewrites = [FRAC_0_SAVE, FRAC_1_SAVE, FRAC_AINV_SAVE, FRAC_ADD_SAVE, FRAC_MUL_SAVE];
(* rewrites to calculate operations on rational numbers *)
val rat_basic_rewrites = [rat_0, rat_1, rat_0_def, rat_1_def, RAT_AINV_CALCULATE, RAT_ADD_CALCULATE, RAT_MUL_CALCULATE] @ frac_rewrites;
(* rewrites to additionally decide equalities and inequalities on rational numbers *)
val rat_rewrites = [RAT_EQ_CALCULATE, RAT_LES_CALCULATE, rat_gre_def, rat_leq_def, rat_geq_def, FRAC_NMR_SAVE, FRAC_DNM_SAVE] @ rat_basic_rewrites;
(* rewrites to decide equalities on rationals in numeral form *)
val rat_num_rewrites = [RAT_ADD_NUM_CALCULATE, RAT_MUL_NUM_CALCULATE, RAT_EQ_NUM_CALCULATE, RAT_AINV_AINV, RAT_AINV_0] @ num_rewrites;

(*--------------------------------------------------------------------------
 * RAT_PRECALC_CONV
 * RAT_POSTCALC_CONV
 *--------------------------------------------------------------------------*)

val RAT_PRECALC_CONV =
	SIMP_CONV int_ss [rat_cons_def, RAT_SAVE_NUM, SGN_def] THENC REWRITE_CONV[RAT_SUB_ADDAINV, RAT_DIV_MULMINV] THENC FRAC_SAVE_CONV;

val RAT_POSTCALC_CONV =
	REWRITE_CONV[GSYM RAT_SUB_ADDAINV, GSYM RAT_DIV_MULMINV] THENC SIMP_CONV int_ss [RAT_SAVE_TO_CONS, RAT_CONS_TO_NUM];

(*--------------------------------------------------------------------------
 * RAT_BASIC_ARITH_CONV
 *--------------------------------------------------------------------------*)

val RAT_BASIC_ARITH_CONV =
	RAT_PRECALC_CONV THENC REWRITE_CONV ([GSYM INT_ADD, GSYM INT_MUL] @ rat_rewrites) THENC ARITH_CONV;

(*--------------------------------------------------------------------------
 * RAT_BASIC_ARITH_TAC
 *--------------------------------------------------------------------------*)

val RAT_BASIC_ARITH_TAC =
	CONV_TAC RAT_BASIC_ARITH_CONV;

(*==========================================================================
 * end of structure
 *==========================================================================*)
end;
