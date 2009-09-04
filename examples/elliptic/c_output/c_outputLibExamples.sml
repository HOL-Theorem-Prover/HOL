(*
quietdec := true;
loadPath :=
            (concat Globals.HOLDIR "/examples/dev/sw") ::
            (concat Globals.HOLDIR "/examples/elliptic/arm") ::
            (concat Globals.HOLDIR "/examples/elliptic/spec") ::
            (concat Globals.HOLDIR "/examples/elliptic/sep") ::
            (concat Globals.HOLDIR "/examples/elliptic/swsep") ::
            (concat Globals.HOLDIR "/examples/elliptic/c_output") ::
            !loadPath;

map load ["elliptic_exampleTheory", "c_outputLib"];
show_assums := true;
*)

open HolKernel Parse boolLib bossLib;
open ellipticTheory;
open elliptic_exampleTheory;
open wordsTheory;
open wordsLib;
open c_outputLib;

(*
quietdec := false;
*)



val defs = [ex1_field_neg_alt, ex1_field_add_alt, ex1_field_sub_alt,
	ex1_field_mult_aux_alt, ex1_field_mult_alt, ex1_field_exp_aux_alt,
	ex1_field_exp_alt, ex1_field_inv_alt, ex1_field_div_alt,
	ex1_curve_neg_alt, ex1_curve_double_alt, ex1_curve_add_alt,
	ex1_curve_mult_aux_alt, ex1_curve_mult_alt];
val rewrites = [];


fun precompile_tests conv (f, tests)  =
	let
		fun eval_test a =
			(a, rhs (concl (conv (mk_comb (f, a)))))
	in
		(f, map (fn x => (print_term (mk_comb (f, x)); print "\n"; eval_test x)) tests)
	end

val testArgs_1 = generate_word_pair_list 1 1000 5;
val testArgs_2 = generate_word_pair_list 2 1000 3;
val tests_1 = (map (fn f => (f, testArgs_1)) [``ex1_field_neg``]);
val tests_2 = (map (fn f => (f, testArgs_2)) [``ex1_field_add``,
														  ``ex1_field_sub``]);
val tests = tests_1 @ tests_2;
val testsL = map (precompile_tests EVAL) tests

val _ = translate_to_c (concat Globals.HOLDIR "/examples/elliptic/c_output/") "defs" defs rewrites ``ex1_field_neg`` testsL

