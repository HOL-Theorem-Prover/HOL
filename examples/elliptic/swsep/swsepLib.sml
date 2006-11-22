(* 
structure arm_translateLib :> arm_translateLib =
struct

	loadPath := 
            (concat Globals.HOLDIR "/examples/dev/sw") :: 
            (concat Globals.HOLDIR "/examples/elliptic/arm") :: 
            (concat Globals.HOLDIR "/examples/elliptic/sep") :: 
            !loadPath;

	use (concat Globals.HOLDIR "/examples/dev/sw/compiler");
	quietdec := true;

	map load ["swsepTheory", "arm_progTheory", "set_sepLib", "arm_instTheory", "pred_setSyntax"];

	quietdec := false;
*)

open HolKernel boolLib bossLib Parse;
open Portable Assem wordsTheory ANF pairTheory pairLib listTheory arithmeticTheory whileTheory  wordsLib PairedLambda mechReasoning IRSyntax;
open swsepTheory arm_progTheory progTheory pred_setTheory set_sepLib set_sepTheory arm_instTheory 

fun extract_ir (_, _, _, _, _, spec, _, wf, _) = 
	let
		val ir = rand (concl wf);
		val (st_var, _) = dest_forall (concl spec);
		val new_var = prim_variant [st_var] st_var;

		val replace = ``^new_var = run_ir ^ir ^st_var``;
		val replace_thm = ASSUME replace
		val thm = GEN_ALL (DISCH replace (REWRITE_RULE [GSYM replace_thm] (SPEC_ALL spec)))
	in
		(thm, wf, ir)
	end;

fun translate_ir ir =
	let
		val t1 = ``CTL_STRUCTURE2INSTRUCTION_LIST ^ir``
		val t2 = ``CONTAINS_MEMORY_DOPER ^ir``
		val t3 = ``IS_WELL_FORMED_CTL_STRUCTURE ^ir``
		val thm1 = EVAL t1
		val thm2 = EVAL t2
		val thm3 = EVAL t3
	in
		(rhs (concl thm1), thm1, thm2, thm3)
	end;

fun spec_ir comp =
	let
		val (spec, wf, ir) = extract_ir comp;
		val (vars, body) = strip_forall (concl spec);

		fun replace var_old var_new =
			subst [``mread ^var_old (RR R0)`` |-> ``^var_new (MREG2REG R0)``,
					 ``mread ^var_old (RR R1)`` |-> ``^var_new (MREG2REG R1)``,
					 ``mread ^var_old (RR R2)`` |-> ``^var_new (MREG2REG R2)``,
					 ``mread ^var_old (RR R3)`` |-> ``^var_new (MREG2REG R3)``,
					 ``mread ^var_old (RR R4)`` |-> ``^var_new (MREG2REG R4)``,
					 ``mread ^var_old (RR R5)`` |-> ``^var_new (MREG2REG R5)``,
					 ``mread ^var_old (RR R6)`` |-> ``^var_new (MREG2REG R6)``,
					 ``mread ^var_old (RR R7)`` |-> ``^var_new (MREG2REG R7)``,
					 ``mread ^var_old (RR R8)`` |-> ``^var_new (MREG2REG R8)``,
					 ``mread ^var_old (RR R9)`` |-> ``^var_new (MREG2REG R9)``,
					 ``mread ^var_old (RR R10)`` |-> ``^var_new (MREG2REG R10)``,
					 ``mread ^var_old (RR R11)`` |-> ``^var_new (MREG2REG R11)``,
					 ``mread ^var_old (RR R12)`` |-> ``^var_new (MREG2REG R12)``,
					 ``mread ^var_old (RR R13)`` |-> ``^var_new (MREG2REG R13)``,
					 ``mread ^var_old (RR R14)`` |-> ``^var_new (MREG2REG R14)``];

		val new_var1 = prim_variant (free_vars body) (mk_var ("r", ``:word4 -> word32``))
		val new_var2 = prim_variant (new_var1::free_vars body) (mk_var ("r", ``:word4 -> word32``))

		val spec_term = rand (body);
		val spec_term = replace (el 1 vars) new_var2 spec_term;
		val spec_term = replace (el 2 vars) new_var1 spec_term;
		val spec_term = mk_abs (new_var2, spec_term);
		val spec_term = mk_abs (new_var1, spec_term);



		val (_, ir_thm, mem_thm, wf_thm2) = translate_ir ir;
		val thm = SIMP_RULE std_ss [dimindex_24] TRANSLATION_SPEC_thm;
		val thm = SPECL [ir, spec_term] thm 
		val thm = SIMP_RULE list_ss [wf, ir_thm, mem_thm, wf_thm2, state2reg_fun2mread, 
			arm_mem_state2reg_fun2REG_READ, spec, ILTheory.from_reg_index_def] thm
	in
		thm
	end;



	fun FILTER_CONV conv t =
		let
			val thm = ONCE_REWRITE_CONV [FILTER] t;
			val thm = BETA_RULE thm
			val r = rhs (concl thm)				
			val e = if (is_cond r) then
							let
								val thm2 = ((RATOR_CONV (RATOR_CONV conv)) THENC REWRITE_CONV []) r;
								val thm = CONV_RULE (RHS_CONV (REWRITE_CONV [thm2])) thm
							in
								CONV_RULE (RHS_CONV (DEPTH_CONV (FILTER_CONV conv))) thm
							end
						else
							thm
		in 
			e
		end;

fun post_process_sep thm =
	let
		val thm = (SIMP_RULE std_ss [GSYM SEP_HIDE_THM, STAR_ASSOC]) thm
		val thm = (CONV_RULE (DEPTH_CONV ETA_CONV)) thm

		val (_, body) = strip_forall (concl thm);
		val (arm_prog, args) = strip_comb body;
		val pre = hd args;
		val opr = rator (rator pre);
		val used_values = free_vars (el 4 args);
		val pre_parts = liteLib.binops opr pre

		fun remove_unused t =
			if	mem (rand t) used_values then t else
				liteLib.mk_icomb (``$~:('a -> 'b -> bool) -> 'b -> bool``, rator t)

		val new_preparts = map remove_unused pre_parts	

		val new_pre = mk_comb (arm_prog, foldr (fn (t1, t2) => liteLib.list_mk_icomb opr [t1, t2]) (``emp:(ARMel -> bool) -> bool``) new_preparts)
		val new_pre = rhs (concl (SIMP_CONV std_ss [emp_STAR, STAR_ASSOC] new_pre))
		val new_pre_thm = SIMP_CONV (std_ss++SEP_EXISTS_ss) [SEP_HIDE_THM] new_pre;

		val new_term = liteLib.list_mk_icomb new_pre (tl args)
		val new_term = gen_all new_term;
		
		val thm = prove (new_term, 					
			SIMP_TAC std_ss [GSYM SEP_HIDE_THM, new_pre_thm] THEN
			ONCE_REWRITE_TAC[prove(``ARM_PROG p = ARM_PROG (emp * p)``, REWRITE_TAC[emp_STAR])] THEN
			SIMP_TAC std_ss [GSYM ARM_PROG_HIDE_PRE] THEN
			SIMP_TAC std_ss [emp_STAR, thm]);
	in
		thm
	end;


fun spec_sep (comp:(string * hol_type * (IRSyntax.exp * 'a * IRSyntax.exp) * thm list * thm * thm * thm * thm * thm)) = 
	let
		val (spec, wf, ir) = extract_ir comp;
		val input_regs = listSyntax.mk_list (map IRSyntax.convert_reg (IRSyntax.pair2list (#1 (#3 comp))), Type `:MREG`);

		val unchanged_thm = CONJUNCT1 (REWRITE_RULE [ILTheory.UNCHANGED_STACK_def] (#9 comp))
		
		val uregs_all = rand (rator (concl unchanged_thm));
		val uregs_term = ``FILTER (\r. ~MEM r ^input_regs) ^uregs_all``
		val uregs_thm = (FILTER_CONV (SIMP_CONV std_ss [MEM, ILTheory.MREG_distinct]))
				uregs_term
		val uregs = rhs (concl uregs_thm)

		val uregs_input = rhs (concl ((FILTER_CONV (SIMP_CONV std_ss [MEM, ILTheory.MREG_distinct]))
				``FILTER (\r. MEM r ^uregs_all) ^input_regs``))
		val r_unchanged_thm = REWRITE_RULE [uregs_thm] 
									 (prove (``UNCHANGED ^uregs_term ^ir``,
										MP_TAC unchanged_thm THEN
										REWRITE_TAC [ILTheory.UNCHANGED_def, MEM_FILTER] THEN
										PROVE_TAC[]));

		val (vars, body) = strip_forall (concl spec);
		val body_rel = rand body
		val body_rel = 
			(rhs (concl (SIMP_CONV std_ss [PAIR_FST_SND_EQ] body_rel)))
			handle _ => body_rel

		val vals = ``vals:word4->word32``;
		fun replace var_old =
			subst [``mread ^var_old (RR R0)`` |-> ``^vals (MREG2REG R0)``,
					 ``mread ^var_old (RR R1)`` |-> ``^vals (MREG2REG R1)``,
					 ``mread ^var_old (RR R2)`` |-> ``^vals (MREG2REG R2)``,
					 ``mread ^var_old (RR R3)`` |-> ``^vals (MREG2REG R3)``,
					 ``mread ^var_old (RR R4)`` |-> ``^vals (MREG2REG R4)``,
					 ``mread ^var_old (RR R5)`` |-> ``^vals (MREG2REG R5)``,
					 ``mread ^var_old (RR R6)`` |-> ``^vals (MREG2REG R6)``,
					 ``mread ^var_old (RR R7)`` |-> ``^vals (MREG2REG R7)``,
					 ``mread ^var_old (RR R8)`` |-> ``^vals (MREG2REG R8)``,
					 ``mread ^var_old (RR R9)`` |-> ``^vals (MREG2REG R9)``,
					 ``mread ^var_old (RR R10)`` |-> ``^vals (MREG2REG R10)``,
					 ``mread ^var_old (RR R11)`` |-> ``^vals (MREG2REG R11)``,
					 ``mread ^var_old (RR R12)`` |-> ``^vals (MREG2REG R12)``,
					 ``mread ^var_old (RR R13)`` |-> ``^vals (MREG2REG R13)``,
					 ``mread ^var_old (RR R14)`` |-> ``^vals (MREG2REG R14)``];

		val body_rel = replace (el 2 vars) body_rel
		val body_list = strip_conj body_rel;
		val x = mk_var ("x", Type `:word4`);
		fun extract_oregs_f [] = (uregs_input, mk_comb(vals,x)) |
			 extract_oregs_f (t::l) = 
				let
					val (oregs, f) = extract_oregs_f l;
					val (ls, rs) = dest_eq t;
					val oreg = rand (rand ls);

					val oregs = listSyntax.mk_cons(oreg, oregs);
					val f = mk_cond (mk_eq (x, ``MREG2REG ^oreg``), rs, f)
				in
					(oregs, f)
				end;
		val (oregs, f) = extract_oregs_f body_list

		val f = rhs (concl (REWRITE_CONV [MREG2REG_def, ILTheory.index_of_reg_def] f));
		val f = mk_abs (vals, (mk_abs (x, f)))

		val oregs_words_thm = REWRITE_CONV [MAP, MREG2REG_def, ILTheory.index_of_reg_def] (``MAP MREG2REG ^oregs``);
		val oregs_words = rhs (concl oregs_words_thm);
		val uregs_words_thm = REWRITE_CONV [MAP, MREG2REG_def, ILTheory.index_of_reg_def] (``MAP MREG2REG ^uregs``);
		val uregs_words = rhs (concl uregs_words_thm);

		val oregs_uregs_distinct = (SIMP_CONV list_ss [DISJ_IMP_THM, ILTheory.MREG_distinct] ``(!x. MEM x ^oregs ==> ~MEM x ^uregs)``)


		val regs_list = ``[(0w:word4,rv0:word32); (1w,rv1); (2w,rv2); (3w,rv3); (4w,rv4); (5w,rv5);
           (6w,rv6); (7w,rv7); (8w,rv8); (9w,rv9); (10w,rv10); (11w,rv11);
           (12w,rv12); (13w,rv13); (14w,rv14)]``;

		val f_thm = GEN_ALL (SIMP_CONV std_ss [LIST_TO_FUN_def, preARMTheory.word4_distinct] ``^f (LIST_TO_FUN 0w ^regs_list)``)


		val input_regs_list_thm = GEN_ALL (
			FILTER_CONV (REWRITE_CONV [MEM, preARMTheory.word4_distinct]) 		
				``FILTER (\x. ~MEM (FST x) ^uregs_words) ^regs_list``)
		val input_regs_list = rhs (concl (SPEC_ALL input_regs_list_thm))

		val fe_var = mk_var ("fe", Type `:word4 -> word32`);
		val output_regs_list_term = ``(FILTER (\x. MEM (FST x) ^oregs_words)
            (MAP (\(r,v). (r, ^fe_var r)) ^regs_list))``
		val output_regs_thm1 = 
			((SIMP_CONV std_ss [MAP]) THENC (FILTER_CONV (REWRITE_CONV [MEM, preARMTheory.word4_distinct]))) output_regs_list_term
		val output_regs_thm2 = 
			SPEC ``^f (LIST_TO_FUN 0w ^regs_list)`` (
				GEN fe_var output_regs_thm1
			)
		val output_regs_thm = SIMP_RULE std_ss [f_thm, preARMTheory.word4_distinct] output_regs_thm2

		
		val unknown_changed_regs_list_thm = GEN_ALL (
			((SIMP_CONV std_ss [MAP]) THENC (FILTER_CONV (REWRITE_CONV [MEM, preARMTheory.word4_distinct]))) 
			``FILTER (\x. ~MEM x ^oregs_words) (MAP FST ^input_regs_list)``)

		val f_depend_term = ``!f1 f2.
            (!q. MEM q ^input_regs_list ==> (f1 (FST q) = f2 (FST q))) ==>
            !r. MEM r ^oregs_words ==> (^f f1 r = ^f f2 r)``
		val f_depend_thm = GEN_ALL (SIMP_RULE std_ss [] (
			SIMP_CONV list_ss [DISJ_IMP_THM, FORALL_AND_THM, preARMTheory.word4_distinct] f_depend_term))

		val f_spec_term = ``!st r.
            MEM r ^oregs_words ==>
            (state2reg_fun (run_ir ^ir st) r = ^f (state2reg_fun st) r)``

		val f_spec_thm = prove (f_spec_term, (*set_goal ([], f_spec_term)*)
			SIMP_TAC list_ss [DISJ_IMP_THM, state2reg_fun2mread2, preARMTheory.word4_distinct] THEN
			WORDS_TAC THEN
			MP_TAC unchanged_thm THEN
			SIMP_TAC std_ss [ILTheory.from_reg_index_def, ILTheory.UNCHANGED_def,
				GSYM rulesTheory.mread_def] THEN
			REWRITE_TAC[MEM] THEN
			METIS_TAC[spec, FST, SND, PAIR_EQ])



		val (_, ir_thm, mem_thm, wf_thm2) = translate_ir ir;
		val thm = TRANSLATION_SPEC_SEP_thm;
		val thm2 = SPECL [ir, uregs, oregs, f] thm 
		val thm3 = REWRITE_RULE [wf, ir_thm, mem_thm, wf_thm2, spec, r_unchanged_thm,
			uregs_words_thm, oregs_words_thm, oregs_uregs_distinct] thm2
		val thm4 = SIMP_RULE std_ss [input_regs_list_thm, f_thm, output_regs_thm,
			unknown_changed_regs_list_thm, f_spec_thm] thm3
		val thm5 = REWRITE_RULE [f_depend_thm] thm4
		val thm6 = SIMP_RULE std_ss [LENGTH, dimindex_24, reg_spec_def, FOLDR,
			ereg_spec_def, emp_STAR] thm5		
		val thm7 = post_process_sep thm6
	in
		thm7
	end
