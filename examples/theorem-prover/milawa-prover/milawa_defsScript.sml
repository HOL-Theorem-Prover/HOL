open HolKernel boolLib bossLib Parse; val _ = new_theory "milawa_defs";

open lisp_extractLib lisp_extractTheory;

open stringTheory finite_mapTheory pred_setTheory listTheory sumTheory;
open optionTheory arithmeticTheory relationTheory;

open lisp_sexpTheory lisp_semanticsTheory lisp_parseTheory;

open milawa_initTheory;
val _ = max_print_depth := 20;

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* we extract functions defined by milawa-init *)

val _ = install_assum_eq core_assum_def;


(* extract functions *)

val not_def = pure_extract "NOT" NONE

val isTrue_not = prove(
  ``!x. isTrue (not x) = ~(isTrue x)``,
  SIMP_TAC std_ss [fetch "-" "not_def"] \\ REPEAT STRIP_TAC
  \\ Cases_on `isTrue x` \\ ASM_SIMP_TAC std_ss [] \\ EVAL_TAC);

(*
  fetch "-" "R_ev_rank"
*)

(* we define a tactic that can solve simple termination goals *)

val LSIZE_CAR_CDR = prove(
  ``isDot x ==> LSIZE (CAR x) < LSIZE x /\ LSIZE (CDR x) < LSIZE x``,
  REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [isDot_thm,CAR_def,CDR_def,LSIZE_def]
  \\ DECIDE_TAC);

val LSIZE_CAR_IMP = prove(
  ``LSIZE x < LSIZE y ==> LSIZE (CAR x) < LSIZE y``,
  Cases_on `x` \\ SIMP_TAC std_ss [LSIZE_def,CAR_def] \\ DECIDE_TAC);

val LSIZE_CDR_IMP = prove(
  ``LSIZE x < LSIZE y ==> LSIZE (CDR x) < LSIZE y``,
  Cases_on `x` \\ SIMP_TAC std_ss [LSIZE_def,CDR_def] \\ DECIDE_TAC);

fun LSIZE_TAC f =
  WF_REL_TAC f
  \\ REWRITE_TAC [isTrue_not,isTrue_CLAUSES,FIRST_def,SECOND_def,THIRD_def,
       FOURTH_def,FIFTH_def] \\ REPEAT STRIP_TAC \\ IMP_RES_TAC LSIZE_CAR_CDR
  \\ NTAC 10 ((MATCH_MP_TAC LSIZE_CAR_IMP ORELSE MATCH_MP_TAC LSIZE_CDR_IMP)
              \\ ASM_SIMP_TAC std_ss []) \\ NO_TAC

val term_tac =
  SOME (FIRST [LSIZE_TAC `measure (LSIZE)`,
               LSIZE_TAC `measure (LSIZE o FST)`,
               LSIZE_TAC `measure (LSIZE o SND)`,
               LSIZE_TAC `measure (LSIZE o FST o SND)`,
               LSIZE_TAC `measure (LSIZE o SND o SND)`])

val rank_def = pure_extract "RANK" term_tac;
val ord__def = pure_extract "ORD<" term_tac;
val ordp_def = pure_extract "ORDP" term_tac;
val nfix_def = pure_extract "NFIX" term_tac;
val less_eq_def = pure_extract "<=" term_tac;
val zp_def = pure_extract "ZP" term_tac;
val true_listp_def = pure_extract "TRUE-LISTP" term_tac;
val list_fix_def = pure_extract "LIST-FIX" term_tac;
val len_def = pure_extract "LEN" term_tac;
val memberp_def = pure_extract "MEMBERP" term_tac;
val subsetp_def = pure_extract "SUBSETP" term_tac;
val uniquep_def = pure_extract "UNIQUEP" term_tac;
val app_def = pure_extract "APP" term_tac;
val rev_def = pure_extract "REV" term_tac;
val tuplep_def = pure_extract "TUPLEP" term_tac;
val pair_lists_def = pure_extract "PAIR-LISTS" term_tac;
val lookup_def = pure_extract "LOOKUP" term_tac;
val logic_variablep_def = pure_extract "LOGIC.VARIABLEP" term_tac;
val logic_variable_listp_def = pure_extract "LOGIC.VARIABLE-LISTP" term_tac;
val logic_constantp_def = pure_extract "LOGIC.CONSTANTP" term_tac;
val logic_constant_listp_def = pure_extract "LOGIC.CONSTANT-LISTP" term_tac;
val logic_function_namep_def = pure_extract "LOGIC.FUNCTION-NAMEP" term_tac;
val logic_flag_term_vars_def = pure_extract "LOGIC.FLAG-TERM-VARS" term_tac;
val logic_term_vars_def = pure_extract "LOGIC.TERM-VARS" term_tac;

val CAR_CAR_EQ_LAMBDA = prove(
  ``!x. (CAR (CAR x) = Sym "LAMBDA") ==> isDot x``,
  Cases \\ SIMP_TAC (srw_ss()) [isDot_def,CAR_def,CDR_def]);

val logic_flag_termp_def = pure_extract "LOGIC.FLAG-TERMP" (SOME
 (WF_REL_TAC `measure (\(f,x). 2 * LSIZE x + if f = Sym "TERM" then 1 else 0)`
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [isTrue_not,isTrue_CLAUSES,FIRST_def,SECOND_def,THIRD_def,
       FOURTH_def,FIFTH_def] \\ IMP_RES_TAC CAR_CAR_EQ_LAMBDA
  \\ IMP_RES_TAC LSIZE_CAR_CDR
  \\ TRY (NTAC 10 ((MATCH_MP_TAC LSIZE_CAR_IMP ORELSE MATCH_MP_TAC LSIZE_CDR_IMP)
              \\ ASM_SIMP_TAC std_ss [])) \\ REPEAT DECIDE_TAC
  \\ Cases_on `x` \\ SIMP_TAC std_ss [LSIZE_def,CDR_def] \\ DECIDE_TAC))

val logic_termp_def = pure_extract "LOGIC.TERMP" term_tac;
val logic_unquote_def = pure_extract "LOGIC.UNQUOTE" term_tac;
val logic_unquote_list_def = pure_extract "LOGIC.UNQUOTE-LIST" term_tac;
val logic_functionp_def = pure_extract "LOGIC.FUNCTIONP" term_tac;
val logic_function_name_def = pure_extract "LOGIC.FUNCTION-NAME" term_tac;
val logic_function_args_def = pure_extract "LOGIC.FUNCTION-ARGS" term_tac;
val logic_function_def = pure_extract "LOGIC.FUNCTION" term_tac;
val logic_lambdap_def = pure_extract "LOGIC.LAMBDAP" term_tac;
val logic_lambda_formals_def = pure_extract "LOGIC.LAMBDA-FORMALS" term_tac;
val logic_lambda_body_def = pure_extract "LOGIC.LAMBDA-BODY" term_tac;
val logic_lambda_actuals_def = pure_extract "LOGIC.LAMBDA-ACTUALS" term_tac;
val logic_lambda_def = pure_extract "LOGIC.LAMBDA" term_tac;

val logic_lambdap_IMP_isDot = prove(
  ``!x. isTrue (logic_lambdap x) ==> isDot x``,
  Cases \\ EVAL_TAC);

val logic_functionp_IMP_isDot = prove(
  ``!x. isTrue (logic_functionp x) ==> isDot x``,
  Cases \\ SIMP_TAC std_ss [isDot_def] THEN1 EVAL_TAC
  \\ SIMP_TAC std_ss [logic_functionp_def,logic_function_namep_def,CAR_def] \\ EVAL_TAC);

val logic_flag_term_atblp_def = pure_extract "LOGIC.FLAG-TERM-ATBLP" (SOME
 (WF_REL_TAC `measure (\(f,x,y). 2 * LSIZE x + if f = Sym "TERM" then 1 else 0)`
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [isTrue_not,isTrue_CLAUSES,FIRST_def,SECOND_def,THIRD_def,
       FOURTH_def,FIFTH_def,logic_function_args_def,logic_lambda_actuals_def,
       logic_lambda_body_def] \\ IMP_RES_TAC logic_lambdap_IMP_isDot
  \\ IMP_RES_TAC logic_functionp_IMP_isDot
  \\ IMP_RES_TAC LSIZE_CAR_CDR
  \\ REPEAT ((MATCH_MP_TAC LSIZE_CAR_IMP ORELSE MATCH_MP_TAC LSIZE_CDR_IMP)
             \\ ASM_SIMP_TAC std_ss [])
  \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss [LSIZE_def,CDR_def,CAR_def,isDot_def] \\ DECIDE_TAC))

val logic_term_atblp_def = pure_extract "LOGIC.TERM-ATBLP" term_tac;

val isTrue_tuplep = prove(
  ``!x. (isTrue (tuplep (Val 3) x) = ?x1 x2 x3. x = list2sexp [x1;x2;x3]) /\
        (isTrue (tuplep (Val 2) x) = ?x1 x2. x = list2sexp [x1;x2])``,
  SIMP_TAC std_ss [EVAL ``tuplep (Val 2) x``,EVAL ``tuplep (Val 3) x``]
  \\ SRW_TAC [] [] \\ Cases_on `isDot x` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `isDot (CDR x)` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `isDot (CDR (CDR x))` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ Cases_on `CDR (CDR (CDR x)) = Sym "NIL"` \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SIMP_TAC std_ss [list2sexp_def,isTrue_CLAUSES]
  \\ CCONTR_TAC \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [isDot_def,CDR_def]
  \\ Cases_on `S0` \\ FULL_SIMP_TAC (srw_ss()) [isDot_def,CDR_def]
  \\ Cases_on `S0'` \\ FULL_SIMP_TAC (srw_ss()) [isDot_def,CDR_def,isTrue_CLAUSES]);

val logic_formulap_def = pure_extract "LOGIC.FORMULAP" (SOME
 (WF_REL_TAC `measure LSIZE`
  \\ REWRITE_TAC [isTrue_not,isTrue_CLAUSES,FIRST_def,SECOND_def,THIRD_def,
       FOURTH_def,FIFTH_def,isTrue_tuplep,list2sexp_def] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC std_ss [CAR_def,CDR_def,LSIZE_def] \\ DECIDE_TAC))

val logic_formula_listp_def = pure_extract "LOGIC.FORMULA-LISTP" term_tac;
val logic_fmtype_def = pure_extract "LOGIC.FMTYPE" term_tac;
val logic__lhs_def = pure_extract "LOGIC.=LHS" term_tac;
val logic__rhs_def = pure_extract "LOGIC.=RHS" term_tac;
val logic__arg_def = pure_extract "LOGIC.~ARG" term_tac;
val logic_vlhs_def = pure_extract "LOGIC.VLHS" term_tac;
val logic_vrhs_def = pure_extract "LOGIC.VRHS" term_tac;
val logic_pequal_def = pure_extract "LOGIC.PEQUAL" term_tac;
val logic_pnot_def = pure_extract "LOGIC.PNOT" term_tac;
val logic_por_def = pure_extract "LOGIC.POR" term_tac;
val logic_formula_atblp_def = pure_extract "LOGIC.FORMULA-ATBLP" (SOME
 (WF_REL_TAC `measure (LSIZE o FST)`
  \\ FULL_SIMP_TAC std_ss [isTrue_not,isTrue_CLAUSES,FIRST_def,SECOND_def,THIRD_def,
       FOURTH_def,FIFTH_def,isTrue_tuplep,list2sexp_def,logic_vlhs_def,
       logic_vrhs_def,logic__arg_def,logic_fmtype_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def,CDR_def]
  \\ Cases_on `S0` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def,CDR_def,LSIZE_def]
  \\ REPEAT (Cases_on `S0':SExp` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def,CDR_def,LSIZE_def])
  \\ DECIDE_TAC));

val logic_disjoin_formulas_def = pure_extract "LOGIC.DISJOIN-FORMULAS" term_tac;

val logic_formulap_IMP_isDot = prove(
  ``!x. isTrue (logic_formulap x) ==> isDot x``,
  Cases \\ SIMP_TAC std_ss [isDot_def] \\ EVAL_TAC);

val logic_flag_appealp_def = pure_extract "LOGIC.FLAG-APPEALP" (SOME
 (WF_REL_TAC `measure (LSIZE o SND)`
  \\ FULL_SIMP_TAC std_ss [isTrue_not,isTrue_CLAUSES,FIRST_def,SECOND_def,THIRD_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC logic_formulap_IMP_isDot
  \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def,CDR_def]
  \\ REPEAT (Cases_on `S0` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def,CDR_def,LSIZE_def])
  \\ REPEAT (Cases_on `S0'` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def,CDR_def,LSIZE_def])
  \\ FULL_SIMP_TAC std_ss [isDot_def] \\ DECIDE_TAC));

val logic_appealp_def = pure_extract "LOGIC.APPEALP" term_tac;
val logic_appeal_listp_def = pure_extract "LOGIC.APPEAL-LISTP" term_tac;
val logic_method_def = pure_extract "LOGIC.METHOD" term_tac;
val logic_conclusion_def = pure_extract "LOGIC.CONCLUSION" term_tac;
val logic_subproofs_def = pure_extract "LOGIC.SUBPROOFS" term_tac;
val logic_extras_def = pure_extract "LOGIC.EXTRAS" term_tac;
val logic_strip_conclusions_def = pure_extract "LOGIC.STRIP-CONCLUSIONS" term_tac;
val logic_axiom_okp_def = pure_extract "LOGIC.AXIOM-OKP" term_tac;
val logic_theorem_okp_def = pure_extract "LOGIC.THEOREM-OKP" term_tac;
val logic_associativity_okp_def = pure_extract "LOGIC.ASSOCIATIVITY-OKP" term_tac;
val logic_contraction_okp_def = pure_extract "LOGIC.CONTRACTION-OKP" term_tac;
val logic_cut_okp_def = pure_extract "LOGIC.CUT-OKP" term_tac;
val logic_expansion_okp_def = pure_extract "LOGIC.EXPANSION-OKP" term_tac;
val logic_propositional_schema_okp_def = pure_extract "LOGIC.PROPOSITIONAL-SCHEMA-OKP" term_tac;
val logic_check_functional_axiom_def = pure_extract "LOGIC.CHECK-FUNCTIONAL-AXIOM" (SOME
 (WF_REL_TAC `measure (LSIZE o FST)`
  \\ FULL_SIMP_TAC std_ss [isTrue_not,isTrue_CLAUSES,FIRST_def,SECOND_def,THIRD_def,
       FOURTH_def,FIFTH_def,isTrue_tuplep,list2sexp_def,logic_vlhs_def,
       logic_vrhs_def,logic__arg_def,logic_fmtype_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `x` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def,CDR_def]
  \\ Cases_on `S0` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def,CDR_def,LSIZE_def]
  \\ REPEAT (Cases_on `S0':SExp` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def,CDR_def,LSIZE_def])
  \\ DECIDE_TAC));

val logic_functional_equality_okp_def = pure_extract "LOGIC.FUNCTIONAL-EQUALITY-OKP" term_tac;
val logic_sigmap_def = pure_extract "LOGIC.SIGMAP" term_tac;
val logic_sigma_listp_def = pure_extract "LOGIC.SIGMA-LISTP" term_tac;
val logic_sigma_list_listp_def = pure_extract "LOGIC.SIGMA-LIST-LISTP" term_tac;

val logic_flag_substitute_def = pure_extract "LOGIC.FLAG-SUBSTITUTE" (SOME
 (WF_REL_TAC `measure (\(f,x,y). 2 * LSIZE x + if f = Sym "TERM" then 1 else 0)`
  \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [isTrue_not,isTrue_CLAUSES,FIRST_def,SECOND_def,THIRD_def,
       FOURTH_def,FIFTH_def,logic_function_args_def,logic_lambda_actuals_def,
       logic_lambda_body_def] \\ IMP_RES_TAC logic_lambdap_IMP_isDot
  \\ IMP_RES_TAC logic_functionp_IMP_isDot
  \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss [LSIZE_def,CDR_def,CAR_def,isDot_def] \\ DECIDE_TAC))

val logic_substitute_def = pure_extract "LOGIC.SUBSTITUTE" term_tac;
val logic_substitute_list_def = pure_extract "LOGIC.SUBSTITUTE-LIST" term_tac;

val logic_substitute_formula_def = pure_extract "LOGIC.SUBSTITUTE-FORMULA" (SOME
 (WF_REL_TAC `measure (LSIZE o FST)`
  \\ SIMP_TAC std_ss [logic_vlhs_def,logic__arg_def,logic_vrhs_def,FIRST_def,
       SECOND_def,THIRD_def,logic_fmtype_def,isTrue_CLAUSES]
  \\ REPEAT STRIP_TAC \\ Cases_on `formula`
  \\ FULL_SIMP_TAC (srw_ss()) [CAR_def,CDR_def]
  \\ Cases_on `S0` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def,CDR_def,LSIZE_def]
  \\ REPEAT (Cases_on `S0':SExp` \\ FULL_SIMP_TAC (srw_ss()) [CAR_def,CDR_def,LSIZE_def])
  \\ DECIDE_TAC));

val logic_instantiation_okp_def = pure_extract "LOGIC.INSTANTIATION-OKP" term_tac;
val logic_beta_reduction_okp_def = pure_extract "LOGIC.BETA-REDUCTION-OKP" term_tac;
val logic_initial_arity_table_def = pure_extract "LOGIC.INITIAL-ARITY-TABLE" term_tac;
val logic_base_evaluablep_def = pure_extract "LOGIC.BASE-EVALUABLEP" term_tac;
val logic_base_evaluator_def = pure_extract "LOGIC.BASE-EVALUATOR" term_tac;
val logic_base_eval_okp_def = pure_extract "LOGIC.BASE-EVAL-OKP" term_tac;
val logic_make_basis_step_def = pure_extract "LOGIC.MAKE-BASIS-STEP" term_tac;
val logic_substitute_each_sigma_into_formula_def = pure_extract "LOGIC.SUBSTITUTE-EACH-SIGMA-INTO-FORMULA" term_tac;
val logic_make_induction_step_def = pure_extract "LOGIC.MAKE-INDUCTION-STEP" term_tac;
val logic_make_induction_steps_def = pure_extract "LOGIC.MAKE-INDUCTION-STEPS" term_tac;
val logic_make_ordinal_step_def = pure_extract "LOGIC.MAKE-ORDINAL-STEP" term_tac;
val logic_make_measure_step_def = pure_extract "LOGIC.MAKE-MEASURE-STEP" term_tac;
val logic_make_measure_steps_def = pure_extract "LOGIC.MAKE-MEASURE-STEPS" term_tac;
val logic_make_all_measure_steps_def = pure_extract "LOGIC.MAKE-ALL-MEASURE-STEPS" term_tac;
val logic_induction_okp_def = pure_extract "LOGIC.INDUCTION-OKP" term_tac;
val logic_appeal_step_okp_def = pure_extract "LOGIC.APPEAL-STEP-OKP" term_tac;

val logic_appeal_step_okp_IMP_isDot = prove(
  ``!x. isTrue (logic_appeal_step_okp x y z q) ==> isDot x``,
  Cases \\ SIMP_TAC std_ss [isDot_def] \\ EVAL_TAC);

val logic_flag_proofp_def = pure_extract "LOGIC.FLAG-PROOFP" (SOME
 (WF_REL_TAC `measure (\(f,x,y). LSIZE x)` \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [isTrue_not,isTrue_CLAUSES,FIRST_def,SECOND_def,THIRD_def,
       FOURTH_def,FIFTH_def,logic_function_args_def,logic_lambda_actuals_def,
       logic_lambda_body_def,logic_subproofs_def] \\ IMP_RES_TAC logic_lambdap_IMP_isDot
  \\ IMP_RES_TAC logic_appeal_step_okp_IMP_isDot
  \\ Cases_on `x` \\ FULL_SIMP_TAC std_ss [LSIZE_def,CDR_def,CAR_def,isDot_def]
  \\ REPEAT (Cases_on `S0` \\ FULL_SIMP_TAC std_ss [CAR_def,CDR_def])
  \\ REPEAT (Cases_on `S0'` \\ FULL_SIMP_TAC std_ss [CAR_def,CDR_def])
  \\ FULL_SIMP_TAC std_ss [LSIZE_def,isDot_def] \\ DECIDE_TAC));

val logic_proofp_def = pure_extract "LOGIC.PROOFP" term_tac;
val logic_provable_witness_def = pure_extract "LOGIC.PROVABLE-WITNESS" term_tac;
val logic_provablep_def = pure_extract "LOGIC.PROVABLEP" term_tac;
val remove_all_def = pure_extract "REMOVE-ALL" term_tac;
val remove_duplicates_def = pure_extract "REMOVE-DUPLICATES" term_tac;
val difference_def = pure_extract "DIFFERENCE" term_tac;
val strip_firsts_def = pure_extract "STRIP-FIRSTS" term_tac;
val strip_seconds_def = pure_extract "STRIP-SECONDS" term_tac;
val tuple_listp_def = pure_extract "TUPLE-LISTP" term_tac;
val sort_symbols_insert_def = pure_extract "SORT-SYMBOLS-INSERT" term_tac;
val sort_symbols_def = pure_extract "SORT-SYMBOLS" term_tac;
val logic_translate_and_term_def = pure_extract "LOGIC.TRANSLATE-AND-TERM" term_tac;
val logic_translate_let_term_def = pure_extract "LOGIC.TRANSLATE-LET-TERM" term_tac;
val logic_translate_or_term_def = pure_extract "LOGIC.TRANSLATE-OR-TERM" term_tac;
val logic_translate_list_term_def = pure_extract "LOGIC.TRANSLATE-LIST-TERM" term_tac;
val logic_translate_cond_term_def = pure_extract "LOGIC.TRANSLATE-COND-TERM" term_tac;
val logic_translate_let__term_def = pure_extract "LOGIC.TRANSLATE-LET*-TERM" term_tac;

val IMP_isDot = prove(
  ``!x. ~(isVal x) /\ ~(isSym x) ==> isDot x``,
  Cases \\ EVAL_TAC);

val LSIZE_strip_seconds = prove(
  ``!x. LSIZE (strip_seconds x) <= LSIZE x``,
  REVERSE Induct
  THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ ONCE_REWRITE_TAC [strip_seconds_def]
  \\ SIMP_TAC std_ss [isTrue_CLAUSES,isDot_def,CAR_def,LISP_CONS_def,LSIZE_def,CDR_def]
  \\ `LSIZE (SECOND x) <= LSIZE x` suffices_by DECIDE_TAC
  \\ Cases_on `x` \\ EVAL_TAC
  \\ Cases_on `S0` \\ EVAL_TAC \\ DECIDE_TAC);

val LSIZE_strip_firsts = prove(
  ``!x. LSIZE (strip_firsts x) <= LSIZE x``,
  REVERSE Induct
  THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  THEN1 (EVAL_TAC \\ SIMP_TAC std_ss [])
  \\ ONCE_REWRITE_TAC [strip_firsts_def]
  \\ SIMP_TAC std_ss [isTrue_CLAUSES,isDot_def,CAR_def,LISP_CONS_def,LSIZE_def,CDR_def]
  \\ `LSIZE (FIRST x) <= LSIZE x` suffices_by DECIDE_TAC
  \\ Cases_on `x` \\ EVAL_TAC \\ DECIDE_TAC);

val logic_flag_translate_def = pure_extract "LOGIC.FLAG-TRANSLATE" (SOME
 (WF_REL_TAC `measure (\(f,x). LSIZE x)` \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [isTrue_not,isTrue_CLAUSES,FIRST_def,SECOND_def,THIRD_def,
       FOURTH_def,FIFTH_def,logic_function_args_def,logic_lambda_actuals_def,
       logic_lambda_body_def,logic_subproofs_def]
  \\ IMP_RES_TAC IMP_isDot
  \\ REPEAT (MATCH_MP_TAC
       (MATCH_MP (RW [GSYM AND_IMP_INTRO] LESS_EQ_LESS_TRANS) (SPEC_ALL LSIZE_strip_firsts)))
  \\ REPEAT (MATCH_MP_TAC
       (MATCH_MP (RW [GSYM AND_IMP_INTRO] LESS_EQ_LESS_TRANS) (SPEC_ALL LSIZE_strip_seconds)))
  \\ IMP_RES_TAC LSIZE_CAR_CDR
  \\ REPEAT ((MATCH_MP_TAC LSIZE_CAR_IMP ORELSE MATCH_MP_TAC LSIZE_CDR_IMP)
             \\ ASM_SIMP_TAC std_ss [])));

val logic_translate_def = pure_extract "LOGIC.TRANSLATE" term_tac;
val cons_onto_ranges_def = pure_extract "CONS-ONTO-RANGES" term_tac;
val logic_substitute_callmap_def = pure_extract "LOGIC.SUBSTITUTE-CALLMAP" term_tac;

val logic_flag_callmap_def = pure_extract "LOGIC.FLAG-CALLMAP" (SOME
 (WF_REL_TAC `measure (\(f,x,y). LSIZE y)` \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [isTrue_not,isTrue_CLAUSES,FIRST_def,SECOND_def,THIRD_def,
       FOURTH_def,FIFTH_def,logic_function_args_def,logic_lambda_actuals_def,
       logic_lambda_body_def,logic_subproofs_def]
  \\ IMP_RES_TAC logic_functionp_IMP_isDot
  \\ IMP_RES_TAC logic_lambdap_IMP_isDot
  \\ IMP_RES_TAC LSIZE_CAR_CDR
  \\ REPEAT ((MATCH_MP_TAC LSIZE_CAR_IMP ORELSE MATCH_MP_TAC LSIZE_CDR_IMP)
             \\ ASM_SIMP_TAC std_ss [])));

val logic_callmap_def = pure_extract "LOGIC.CALLMAP" term_tac;

val isTrue_zp = prove(
  ``!x. isTrue (zp x) = (getVal x = 0)``,
  Cases \\ EVAL_TAC \\ SRW_TAC [] []);

val repeat_def = pure_extract "REPEAT" (SOME
 (WF_REL_TAC `measure (getVal o SND)` \\ FULL_SIMP_TAC std_ss [isTrue_zp]
  \\ Cases \\ SIMP_TAC std_ss [getVal_def,LISP_SUB_def] \\ DECIDE_TAC));

val logic_pequal_list_def = pure_extract "LOGIC.PEQUAL-LIST" term_tac;
val logic_progress_obligation_def = pure_extract "LOGIC.PROGRESS-OBLIGATION" term_tac;
val logic_progress_obligations_def = pure_extract "LOGIC.PROGRESS-OBLIGATIONS" term_tac;
val logic_termination_obligations_def = pure_extract "LOGIC.TERMINATION-OBLIGATIONS" term_tac;
val core_initial_atbl_def = pure_extract "CORE.INITIAL-ATBL" term_tac;
val core_initial_axioms_def = pure_extract "CORE.INITIAL-AXIOMS" term_tac;
val core_state_def = pure_extract "CORE.STATE" term_tac;
val core_axioms_def = pure_extract "CORE.AXIOMS" term_tac;
val core_thms_def = pure_extract "CORE.THMS" term_tac;
val core_atbl_def = pure_extract "CORE.ATBL" term_tac;
val core_checker_def = pure_extract "CORE.CHECKER" term_tac;
val core_ftbl_def = pure_extract "CORE.FTBL" term_tac;
val lookup_safe_def = pure_extract "LOOKUP-SAFE" term_tac;
val define_safe_def = impure_extract "DEFINE-SAFE" term_tac;
val define_safe_list_def = impure_extract "DEFINE-SAFE-LIST" term_tac;
val core_check_proof_def = impure_extract "CORE.CHECK-PROOF" term_tac;
val core_check_proof_list_def = impure_extract "CORE.CHECK-PROOF-LIST" term_tac;
val logic_soundness_claim_def = pure_extract "LOGIC.SOUNDNESS-CLAIM" term_tac;
val core_admit_switch_def = impure_extract "CORE.ADMIT-SWITCH" term_tac;
val core_admit_theorem_def = impure_extract "CORE.ADMIT-THEOREM" term_tac;
val core_admit_defun_def = impure_extract "CORE.ADMIT-DEFUN" term_tac;
val core_admit_witness_def = impure_extract "CORE.ADMIT-WITNESS" term_tac;
val core_eval_function_def = impure_extract "CORE.EVAL-FUNCTION" term_tac;
val core_admit_eval_def = impure_extract "CORE.ADMIT-EVAL" term_tac;
val core_admit_print_def = impure_extract "CORE.ADMIT-PRINT" term_tac;
val core_accept_command_def = impure_extract "CORE.ACCEPT-COMMAND" term_tac;
val core_accept_commands_def = impure_extract_cut "CORE.ACCEPT-COMMANDS" term_tac;

(* the top-level function, milawa-main, is extracted using a weaker assumption *)

val _ = install_assum_eq init_assum_def;
val _ = atbl_install "MILAWA-INIT" R_ev_milawa_init;

val milawa_main_def = impure_extract "MILAWA-MAIN" term_tac;

val _ = export_theory();
