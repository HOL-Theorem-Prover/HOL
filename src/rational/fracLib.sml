structure fracLib :> fracLib =
struct

open HolKernel boolLib Parse bossLib;

(* interactive mode
app load ["pairTheory", "pairLib", "integerTheory","intLib","intSyntax",
	"ringLib", "integerRingTheory","integerRingLib",
	"intExtensionTheory", "intExtensionLib", "jbUtils",
	"fracTheory","fracUtils", "fracSyntax"];
*)

open
	arithmeticTheory
	pairTheory pairLib integerTheory intLib intSyntax
	ringLib integerRingTheory integerRingLib
	intExtensionTheory intExtensionLib
	jbUtils	fracTheory fracUtils fracSyntax;

(*==========================================================================
 *  equivalence of fractions
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  FRAC_EQ_CONV : conv
 *
 *    (abs_frac (a1,b1) = abs_frac (a2,b2)
 *   ----------------------------------------------------
 *    0<b1, 0<b2 |- (abs_frac (a1,b1) = abs_frac (a1,b1))
 *	= (a1 = a2) /\ (b1 = b2) : thm
 *--------------------------------------------------------------------------*)

val FRAC_EQ_CONV:conv = fn term1 =>
let
	val eqn = dest_neg term1;
	val (lhs,rhs) = dest_eq eqn;
	val (lhc, lha) = dest_comb lhs;
	val (rhc, rha ) = dest_comb rhs;
	val (a1,b1) = dest_pair lha;
	val (a2,b2) = dest_pair rha;
in
	UNDISCH_ALL (SPECL[a1,b1,a2,b2] FRAC_EQ)
end
handle HOL_ERR _ => raise ERR "FRAC_EQ_CONV" "";

(*--------------------------------------------------------------------------
 *  FRAC_NOTEQ_CONV : conv
 *
 *    ~((abs_frac (a1,b1) = abs_frac (a2,b2))
 *   ----------------------------------------------------
 *    0<b1, 0<b2 |- ~(abs_frac (a1,b1) = abs_frac (a2,b2))
 *	= ~(a1 = a2) \/ ~(b1 = b2)
 *--------------------------------------------------------------------------*)

val FRAC_NOTEQ_CONV:conv = fn term1 =>
let
	val eqn = dest_neg term1;
	val (lhs,rhs) = dest_eq eqn;
	val (lhc, lha) = dest_comb lhs;
	val (rhc, rha ) = dest_comb rhs;
	val (a1,b1) = dest_pair lha;
	val (a2,b2) = dest_pair rha;
in
	UNDISCH_ALL (SPECL[a1,b1,a2,b2] FRAC_NOT_EQ)
end
handle HOL_ERR _ => raise ERR "FRAC_NOTEQ_CONV" "";

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
 *  some useful conversion and tactics about
 *  positive and non-zero numbers in the context of fractions
 *==========================================================================*)

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
						val (fac1, fac2) = dest_mult t1;
						val fac1_thm = frac_pos_conv asm_list fac1;
						val fac2_thm = frac_pos_conv asm_list fac2;
					in
						LIST_MP [fac1_thm,fac2_thm] (SPECL[fac1,fac2] INT_MUL_POS_SIGN)
					end
				else if (rator=frac_dnm_tm) then
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
						val (fac1, fac2) = dest_mult t1;
						val fac1_thm = frac_not0_conv asm_list fac1;
						val fac2_thm = frac_not0_conv asm_list fac2;
					in
						LIST_MP [fac1_thm,fac2_thm] (SPECL[fac1,fac2] INT_NOT0_MUL)
					end
				else if (rator=frac_dnm_tm) then
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
 *  FRAC_POS_CONV : conv
 *--------------------------------------------------------------------------*)

val FRAC_POS_CONV = frac_pos_conv [];

(*--------------------------------------------------------------------------
 *  FRAC_NOT0_CONV : conv
 *--------------------------------------------------------------------------*)

val FRAC_NOT0_CONV = frac_not0_conv [];

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
		val sub_thm = DISCH_ALL (FRAC_NMR_CONV ``frac_nmr( abs_frac (^nmr, ^dnm) )``);
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
		val sub_thm = DISCH_ALL (FRAC_DNM_CONV ``frac_dnm( abs_frac (^nmr, ^dnm) )``);
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
	val term_list = extract_frac_fun [frac_nmr_tm,frac_dnm_tm] goal;
	val nmr_term_list  = map (fn x => let val (rator,nmr,dnm) = x in (nmr,dnm) end) (filter (fn x => let val (a1,a2,a3) = x in a1=frac_nmr_tm end) term_list);
	val dnm_term_list  = map (fn x => let val (rator,nmr,dnm) = x in (nmr,dnm) end) (filter (fn x => let val (a1,a2,a3) = x in a1=frac_dnm_tm end) term_list);
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
 *  subst_thm : term -> thm
 *--------------------------------------------------------------------------*)

fun subst_thm (top_rator:term) =
	if top_rator=frac_add_tm then
		FRAC_ADD_CALCULATE
	else if top_rator=frac_sub_tm then
		FRAC_SUB_CALCULATE
	else if top_rator=frac_mul_tm then
		FRAC_MULT_CALCULATE
	else if top_rator=frac_div_tm then
		FRAC_DIV_CALCULATE
	else if top_rator=frac_ainv_tm then
		FRAC_AINV_CALCULATE
	else if top_rator=frac_minv_tm then
		FRAC_MINV_CALCULATE
	else
		REFL ``x:frac``;

(*--------------------------------------------------------------------------
 *  FRAC_CALC_CONV : term -> conv
 *
 *    t1
 *   -------------------------
 *    |- t1 = abs_frac(a1,b1)
 *--------------------------------------------------------------------------*)
fun FRAC_CALC_CONV (t1:term) =
let
	val (top_rator, top_rands) = dest_frac t1;
	val thm = REFL t1;
in
	if top_rator=``abs_frac`` then
		thm
	else
		if top_rator=t1 orelse top_rator=``rep_rat`` then
			if is_var top_rator  orelse top_rator=``rep_rat`` then
				SUBST [``x:frac`` |-> SPEC t1 (GSYM FRAC)] ``^t1 = x:frac`` thm
			else
				if t1=``frac_0`` then
					frac_0_def
				else
					frac_1_def
		else
			if tl top_rands = [] then
				let
					val fst_arg = FRAC_CALC_CONV (hd top_rands);
					val (fst_nmr,fst_dnm) = dest_pair (snd(dest_comb (snd(dest_eq (snd(dest_thm fst_arg)) )) ));
					val fst_var = genvar ``:frac``;
				in
					let
						val thm1 = SUBST [fst_var |-> fst_arg] ``^t1 = ^top_rator ^fst_var`` thm;
						val (lhs, rhs) = dest_eq( snd (dest_thm thm1) );
						val lhs_var = genvar ``:frac``;
					in
						SUBST [lhs_var |-> UNDISCH_ALL (SPECL[fst_nmr, fst_dnm] (subst_thm top_rator))] ``^lhs = ^lhs_var`` thm1
					end
				end
			else
				let
					val fst_arg = FRAC_CALC_CONV (hd top_rands);
					val snd_arg = FRAC_CALC_CONV (hd (tl top_rands));
					val (fst_nmr,fst_dnm) = dest_pair (snd(dest_comb (snd(dest_eq (snd(dest_thm fst_arg)) )) ));
					val (snd_nmr,snd_dnm) = dest_pair (snd(dest_comb (snd(dest_eq (snd(dest_thm snd_arg)) )) ));
					val fst_var = genvar ``:frac``;
					val snd_var = genvar ``:frac``;
				in
					let
						val thm1 = SUBST [fst_var |-> fst_arg, snd_var |-> snd_arg] ``^t1 = ^top_rator ^fst_var ^snd_var`` thm;
						val (lhs, rhs) = dest_eq( snd (dest_thm thm1) );
						val lhs_var = genvar ``:frac``;
					in
						SUBST [lhs_var |-> UNDISCH_ALL (SPECL[fst_nmr, fst_dnm, snd_nmr, snd_dnm] (subst_thm top_rator))] ``^lhs = ^lhs_var`` thm1
					end
				end
end;

(* ---------- test cases ---------- *
	FRAC_CALC_CONV ``frac_add (abs_frac(3i,4i)) (abs_frac(4i,5i))``;
	FRAC_CALC_CONV ``frac_add f1 f2``;
	FRAC_CALC_CONV ``frac_add f1 ( frac_sub (abs_frac(4i,5i)) f2)``;
	FRAC_CALC_CONV ``frac_add f1 ( frac_div (abs_frac(4i,5i)) f2)``;
	FRAC_CALC_CONV ``frac_add (frac_ainv f1) ( frac_mul f2 (frac_minv f3))``;
	FRAC_CALC_CONV ``frac_add (frac_ainv frac_1) frac_0``;
	FRAC_CALC_CONV ``frac_sub (rep_rat r1) frac_0``;
	FRAC_CALC_CONV ``frac_sub (frac_add (rep_rat r1) (rep_rat r2)) frac_0``;
 * ---------- test cases ---------- *)


(*--------------------------------------------------------------------------
 *  FRAC_STRICT_CALC_TAC : tactic
 *--------------------------------------------------------------------------*)

fun FRAC_STRICT_CALC_TAC (asm_list,goal) =
	let
		val frac_terms = extract_frac goal;
		val calc_thms = map FRAC_CALC_CONV frac_terms;
	in
		(
			SUBST_TAC calc_thms
		) (asm_list,goal)
	end
handle HOL_ERR _ => raise ERR "FRAC_STRICT_CALCULATE_TAC" "";



(*--------------------------------------------------------------------------
 *  frac_calc_tac : term list -> tactic
 *--------------------------------------------------------------------------*)

fun frac_calc_tac (frac_terms:term list) (asm_list:term list,goal:term) =
	let
		(* generate calculation theorems for these terms *)
		val calc_thms = map FRAC_CALC_CONV frac_terms;
		(* extract hypotheses and conclusions *)
		val (calc_thms_hyps,calc_thms_concls) = unzip (map dest_thm calc_thms); (* was calc_asms2 *)
		(* extract left-hand sides and right-hand sides of calculation theorem conclusions *)
		val calc_thms_conls_sides = map dest_eq calc_thms_concls;
		(* merge lists of hypotheses *)
		val calc_hyps = list_xmerge (map (fn x => fst (dest_thm x)) calc_thms);
		(* divide lists of hypotheses into parts ``0 < x`` and ``~(x = 0)`` *)
		val (calc_hyps_gt0, calc_hyps_not0) = partition is_less calc_hyps;

		(* generate theorems for gt0 and not0 hypotheses *)
		val asm_gt0_thms  = map (fn x => frac_pos_conv  asm_list (snd (dest_less x)) ) calc_hyps_gt0;
		val asm_not0_thms = map (fn x => frac_not0_conv asm_list (fst (dest_eq (dest_neg x))) ) calc_hyps_not0;
		val precond_thms = asm_gt0_thms @ asm_not0_thms;

		(* partition them *)
		fun proved (x:thm) = hyp x = [] orelse List.all (in_list asm_list) (hyp x);
		val (asms_proved,asms_toprove) = partition proved (asm_gt0_thms @ asm_not0_thms);

		(* hypothesis, TODO: eventuell gleich triviale entfernen *)
		val asms_hyp = list_xmerge (map (fn x => fst (dest_thm x)) asms_toprove);

		(* generate subgoal:  prove the proposition in which the fractions are subsituted by their calculated values *)
		val subs_sg  = (asm_list, subst (map (fn (lhs,rhs) => (lhs |-> rhs)) calc_thms_conls_sides) goal);
		(* generate subgoals: prove the hypothesis of the hypothesis of the calculation theorems *)
		val hyps_sgs = map (fn x => (asm_list,x)) asms_hyp;

		(* TODO: statt oben hier noch ein paar Theoreme ergänzen, die dann mit thms konkateniert werden *)

		(*val thms = map mk_thm ([subs_sg] @ hyps_sgs);*)

	in
		([subs_sg] @ hyps_sgs , fn (thms:thm list) =>
			let
				(* first theorem: the "main subgoal" *)
				val subs_thm = hd thms;
				(* all other theorems: hyptothesis subgoals *)
				val asm_thms = tl thms;

				(* erster Schritt: baue Voraussetzungen für die calc_thms zusammen *)


				(* extract proof from asm_thms list (TODO: other list) *)
				fun proof_from_asm_thms (t1:term) =
					let
						val corres_asm_thm = List.find (fn x => concl x = t1) asm_thms;
						val corres_pro_thm = List.find (fn x => concl x = t1) asms_proved;
					in
						if (isSome corres_pro_thm) then
							valOf corres_pro_thm
						else if (isSome corres_asm_thm) then
							valOf corres_asm_thm
						else
							ASSUME ``T``
					end;



				fun get_step1_proofs (thm1:thm) = map proof_from_asm_thms (hyp thm1);
				fun mapped_precond_thm (thm1:thm) = LIST_MP (List.rev (get_step1_proofs thm1)) (DISCH_ALL thm1);

				val step1_proofs = map mapped_precond_thm precond_thms;


				fun proof_from_step1 (t1:term) =
					let
						val corres_asm_thm = List.find (fn x => concl x = t1) step1_proofs;
						(*val corres_pro_thm = List.find (fn x => concl x = t1) asms_proved;*)
					in
						(*if (isSome corres_pro_thm) then
							valOf corres_pro_thm
						else*) if (isSome corres_asm_thm) then
							valOf corres_asm_thm
						else
							ASSUME ``T``
					end;


				fun get_step2_proofs (thm1:thm) = map proof_from_step1 (hyp thm1);
				fun step2_thm (thm1:thm) = LIST_MP (List.rev (get_step2_proofs thm1)) (DISCH_ALL thm1);

				val step2_proofs = map step2_thm calc_thms;
			in
				(* PROBLEM: calc_thms bringen viele Hypothesen rein -> eliminieren *)
				SUBS (map GSYM step2_proofs) subs_thm
			end
		)
	end
handle HOL_ERR _ => raise ERR "FRAC_CALC_TAC" "";


(*--------------------------------------------------------------------------
 *  FRAC_CALCTERM_TAC : term -> tactic
 *--------------------------------------------------------------------------*)

fun FRAC_CALCTERM_TAC (t1:term) (asm_list:term list,goal:term) =
	(frac_calc_tac [t1]) (asm_list:term list,goal:term);

(*--------------------------------------------------------------------------
 *  FRAC_CALC_TAC : tactic
 *--------------------------------------------------------------------------*)

fun FRAC_CALC_TAC (asm_list, goal) =
	(frac_calc_tac (extract_frac goal)) (asm_list, goal);

(*--------------------------------------------------------------------------
 *  FRAC_STRICT_CALCEQ_TAC : tactic
 *--------------------------------------------------------------------------*)

val FRAC_STRICT_CALCEQ_TAC =
	FRAC_STRICT_CALC_TAC THEN
	REWRITE_TAC[FRAC_EQ_ALT] THEN
	FRAC_NMRDNM_TAC THEN
	INT_CALCEQ_TAC;

(*--------------------------------------------------------------------------
 *  FRAC_CALCEQ_TAC : tactic
 *--------------------------------------------------------------------------*)

val FRAC_CALCEQ_TAC =
	FRAC_CALC_TAC THEN
	REWRITE_TAC[FRAC_EQ_ALT] THEN
	FRAC_NMRDNM_TAC THEN
	INT_CALCEQ_TAC;

(*==========================================================================
 * transformation of fractions into "valid fractions"
 *==========================================================================*)

(*--------------------------------------------------------------------------
 *  frac_saveterm_conv : conv
 *--------------------------------------------------------------------------*)

fun frac_saveterm_conv t1 =
	let
		val (comb, args) = dest_comb t1;
		val (a1,b1) = dest_pair args;
		val a2 = a1;
		val b2x = ``Num (^b1 - 1i)``;
		val b2 = ``& ^b2x + 1i``;
		val to_show = ``abs_frac (^a1, ^b1) = frac_save ^a1 (Num (^b1 - 1i))``;
		val dnm_thm1 = ARITH_PROVE ``0i < ^b1``;
		val dnm_thm2 = ARITH_PROVE ``0i < ^b2``;
		val frac_thm = SPECL[a1,b1,a1,b2] FRAC_EQ
	in
		REWRITE_RULE [SIMP_CONV int_ss [] b2x] (EQT_ELIM (REWRITE_CONV [frac_save_def,LIST_MP [dnm_thm1,dnm_thm2] frac_thm,SIMP_CONV int_ss [] ``^b1 = ^b2``] to_show))
	end;

(*--------------------------------------------------------------------------
 *  FRAC_SAVE_CONV : conv
 *--------------------------------------------------------------------------*)

fun FRAC_SAVE_CONV t1 =
	REWRITE_CONV (map (TRY_CONV frac_saveterm_conv) (extract_abs_frac t1)) t1;

(*--------------------------------------------------------------------------
 *  FRAC_SAVE_TAC : tactic
 *--------------------------------------------------------------------------*)

val FRAC_SAVE_TAC = CONV_TAC FRAC_SAVE_CONV;

(*==========================================================================
 * end of structure
 *==========================================================================*)
end;
