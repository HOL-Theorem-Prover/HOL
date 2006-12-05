structure c_outputLib :> c_outputLib =
struct

(*
quietdec := true;
loadPath := 
            (concat Globals.HOLDIR "/examples/dev/sw") :: 
            (concat Globals.HOLDIR "/examples/elliptic/arm") :: 
            (concat Globals.HOLDIR "/examples/elliptic/spec") :: 
            (concat Globals.HOLDIR "/examples/elliptic/sep") :: 
            (concat Globals.HOLDIR "/examples/elliptic/swsep") :: 
            !loadPath;

show_assums := true;
map load ["wordsLib"];
*)

open HolKernel Parse boolSyntax Drule Rewrite wordsTheory wordsLib;

(*
quietdec := false;
*)


val word_type = Type `:word32`

fun get_word_type_arity t n =
	let
		val (fname, l) = dest_type t;
	in
		if (fname = "prod") then (
			if (el 1 l = word_type) then
				get_word_type_arity (el 2 l) (n+1)
			else
				(~1)
		) else (
			if (t = word_type) then (n+1) else (~1)
		)
	end


fun get_word_fun_arity t =
	let
		val (fname, l) = dest_type t
	in
		if (fname = "fun") then
			let
				val a1 = get_word_type_arity (el 1 l) 0;
				val a2 = get_word_type_arity (el 2 l) 0;
			in
				(a1, a2)
			end
		else
			(0, get_word_type_arity t 0)
	end

fun add_consts t set =
	if (numSyntax.is_numeral t) then set 
	else if (is_const t) then
		(if (
				(same_const let_tm t) orelse
				(same_const conditional t)
			 )then
			set
		else 
			(HOLset.add (set, t)))
	else if (is_abs t) then
		add_consts (#2 (dest_abs t)) set 
	else if (pairSyntax.is_pair t) then
		let
			val (t1, t2) = pairSyntax.dest_pair t
			val set = add_consts t1 set;
			val set = add_consts t2 set;		
		in
			set
		end
	else if (is_comb t) then
		let
			val (t1, t2) = dest_comb t;
			val set = add_consts t1 set;
			val set = add_consts t2 set;
		in
			set
		end
	else set;

val known_consts_list = [
	Term `($+):word32->word32->word32`,
	Term `($-):word32->word32->word32`,
	Term `($*):word32->word32->word32`,
	Term `($>>>):word32->num->word32`,
	Term `($&&):word32->word32->word32`,
	Term `($!!):word32->word32->word32`,
	Term `($??):word32->word32->word32`,
	Term `($=):word32->word32->bool`,
	Term `($<):word32->word32->bool`,
	Term `n2w:num->word32`
];

val known_consts_set = HOLset.addList (Term.empty_tmset, known_consts_list)


fun get_unknown_consts tL =
	let
		val c_set = foldl (fn (t, s) => add_consts t s) Term.empty_tmset tL;
	in
		HOLset.difference (c_set,known_consts_set)
	end;


fun indent_block l =
	map (fn s => ("   "^s)) l

exception SYNTAX_EXCEPTION;
fun syntax_error c m =
	if c then 
		let
			val _ = print ("!! "^m^"\n");			
		in
			raise SYNTAX_EXCEPTION
		end
	else
		()

val max_used_word_type = ref 1;
fun get_word_type n =
	let
		val _ = if (n > !max_used_word_type) then 
				  (max_used_word_type := n) else ()
	in
		if (n = 1) then "word32" else
		("word32_"^Int.toString n)
	end

fun c_get_word_type n =
	if (n = 1) then ["typedef unsigned int "^(get_word_type n)^";"] else
	let
		val name = get_word_type n;
		val word_type_1 = get_word_type 1;
		val decl = "typedef struct "^name^"_tag {"
		val acc_list = List.tabulate (n, fn n => (word_type_1^" e"^(Int.toString (n+1))^";"))
		val end_line = "} "^name^";"
	in
		[decl]@(indent_block acc_list)@[end_line]
	end


val temp_var_count = ref 0;
fun get_new_temp_var () =
	let
		val _ = (temp_var_count := !temp_var_count + 1);
	in
		"temp_"^Int.toString (!temp_var_count)
	end;



fun translate_fun f argL =
	if (same_const f wordsSyntax.word_add_tm) then
		([], "("^(hd (el 1 argL))^" + "^(hd (el 2 argL))^")")
	else if (same_const f wordsSyntax.word_sub_tm) then
		([], "("^(hd (el 1 argL))^" - "^(hd (el 2 argL))^")")
	else if (same_const f wordsSyntax.word_and_tm) then
		([], "("^(hd (el 1 argL))^" & "^(hd (el 2 argL))^")")
	else if (same_const f wordsSyntax.word_or_tm) then
		([], "("^(hd (el 1 argL))^" | "^(hd (el 2 argL))^")")
	else if (same_const f wordsSyntax.word_xor_tm) then
		([], "("^(hd (el 1 argL))^" ^ "^(hd (el 2 argL))^")")
	else if (same_const f wordsSyntax.word_lsr_tm) then
		([], "("^(hd (el 1 argL))^" >> "^(hd (el 2 argL))^")")
	else 
	let
		val argL' = if argL = [] then [] else el 1 argL;
		val (f_name, f_type) = dest_const f;
		val (arg_n, res_n) = get_word_fun_arity (f_type);
		val _ = syntax_error (not (arg_n = length argL') orelse
								    (res_n <= 0)
					) ("Unknown function '"^f_name^"'!")
		val args_string = String.concat (commafy argL');
	in
		([], f_name^"("^args_string^")")
	end


(*
	val (exp, n) = (body, 1);
*)

fun translate_exp exp n =
	let
		fun translate_bool_exp exp =
			if (exp = T) then ([], "1") 
			else if (exp = F) then ([], "0")				
			else if (is_neg exp) then
				let
					val exp' = dest_neg exp;
					val (inst, exp_s) = translate_bool_exp exp';				
				in
					(inst, "(!"^exp_s^")")
				end
			else if (is_conj exp) then
				let
					val (exp1, exp2) = dest_conj exp;
					val (inst1, exp_s1) = translate_bool_exp exp1;			val (inst2, exp_s2) = translate_bool_exp exp2;			
				in
					(inst1@inst2, "("^exp_s1^" && "^exp_s2^")")
				end
			else if (is_disj exp) then			
				let
					val (exp1, exp2) = dest_disj exp;
					val (inst1, exp_s1) = translate_bool_exp exp1;			val (inst2, exp_s2) = translate_bool_exp exp2;			
				in
					(inst1@inst2, "("^exp_s1^" || "^exp_s2^")")
				end
			else if (is_comb exp) then
				let
					val (f, args) = strip_comb exp;
					val _ = syntax_error ((not (length args = 2)) orelse
												((not (all (fn arg => (type_of arg = word_type)) args))))
								("Unknown boolean function '"^(term_to_string exp)^"'!");
					val operator = 
						if (same_const f boolSyntax.equality) then
							"=="
						else if (f = ``($<):word32->word32->bool``) then
							"<"
						else
							(syntax_error true ("Unknown boolean function '"^(term_to_string exp)^"'!"); "");

					val (inst1, arg1) = translate_exp (el 1 args) 1;
					val (inst2, arg2) = translate_exp (el 2 args) 1;
				in
					(inst1@inst2, "("^(hd arg1)^" "^operator^" "^(hd arg2)^")")
				end
			else (syntax_error true "Unknown boolean expression!"; ([], ""));

		fun translate_exp_bool exp n =
			if (type_of exp = bool) then
				let
					val (instL, s) = translate_bool_exp exp
				in
					(instL, [s])
				end
			else
				translate_exp exp n

		fun translate_args arg = 
			if (numLib.is_numeral arg) then
				([], [term_to_string arg])
			else
				let
					val (args_n, res_n) = 
						get_word_fun_arity (type_of arg);					
					val _ = syntax_error ((not (args_n = 0)) orelse
												(res_n  <= 0))
							("Invalid argument '" ^ (term_to_string arg) ^"' in term '"^(term_to_string exp)^"'!");
				in
					translate_exp arg res_n
				end

	in
		if ((wordsSyntax.is_n2w exp) orelse
			 (numLib.is_numeral exp)) then
			([], [Int.toString(numSyntax.int_of_term (rand exp))])
		else if (is_var exp) then
			let
				val var_name = #1 (dest_var exp);
				val expL = if (n = 1) then [var_name] else
							(List.tabulate (n, fn n => var_name^".e"^(Int.toString (n+1))))
			in
				([], expL)
			end
		else if (is_cond exp) then
			let
				val (cond_exp, true_exp, false_exp) = dest_cond exp;
				val temp_var = get_new_temp_var ();
				val a = get_word_type_arity (type_of exp) 0;
				val _ = syntax_error (not ((n = 1) orelse (n = a)))
								"Wrong arrity of condition!";
				val temp_type = get_word_type a;
				val decl = temp_type^" "^temp_var^";";

				val (cond_inst, cond_exp') = translate_bool_exp cond_exp;
				val (true_inst, true_exp') = translate_exp true_exp 1;
				val (false_inst, false_exp') = translate_exp false_exp 1;

				val if_1 = "if ("^cond_exp'^") {"
				val if_1e = temp_var ^ " = "^(hd true_exp')^";"
				val if_2 = "} else {"
				val if_2e = temp_var ^ " = "^(hd false_exp')^";"
				val if_3 = "}";

				val expL = if (n=1) then [temp_var] else
							(List.tabulate (n, fn n => temp_var^".e"^(Int.toString (n+1))))
			in
				(cond_inst@[decl]@([if_1]@(indent_block (true_inst@[if_1e]))@[if_2]@
				 (indent_block (false_inst@[if_2e]))@[if_3]),
				 expL)
			end
		else if (pairLib.is_pair exp) then
			let
				val expL = pairLib.strip_pair exp;
				val expL' = map translate_args expL 
				val (args_insts, args_exp) = unzip expL';
				val args_insts = List.concat args_insts;
				val args_exp = List.concat args_exp;
				val _ = syntax_error (not (length (args_exp) = n))
								"Invalid arity!";
			in
				(args_insts, args_exp)
			end
		else if (is_let exp) then
			let
				val (body, rhs) = dest_let exp;
				val (lhs, body) = pairLib.dest_pabs body;
				val lhsL = pairLib.strip_pair lhs;
				val lhsL' = map (fn t => #1 (dest_var t)) lhsL;
				val (pre, rhsL) = translate_exp_bool rhs (length lhsL);
				val assignments = map (fn (s1, s2) => (s1^" = "^s2^";")) (zip lhsL' rhsL);
				val (x, exp_s) = translate_exp body n;
			in
				(pre@assignments@x, exp_s)
			end
		else if ((is_comb exp) orelse (is_const exp)) then
			let 
				val (f, args) = strip_comb exp;
				val args_exp = map translate_args args;				
				val (args_insts, args_exp) = unzip args_exp;
				val args_insts = List.concat args_insts;
				val (fun_insts, fun_exp) = translate_fun f args_exp;
				val (extra_insts, expL) = if (n = 1) then ([], [fun_exp]) else
					let
						val temp_var = get_new_temp_var ();
						val a = get_word_type_arity (type_of exp) 0;
						val temp_type = get_word_type a;
						val decl = temp_type^" "^temp_var^";";
						val assignment = temp_var ^ " = "^fun_exp^";"
						val expL = (List.tabulate (n, fn n => temp_var^".e"^(Int.toString (n+1))))
					in
						([decl,assignment], expL)
					end
			in
				(args_insts@fun_insts@extra_insts, expL)
			end
		else 
			let
				val _ = syntax_error true ("Unknown expression '"^(term_to_string exp)^"'!")
			in
				([], ["ERROR"])
			end
	end;

fun print_insts l =
let
	val _ = print "\n\n";
	val _ = map (fn s => print (s^"\n")) l
	val _ = print "\n\n";
in
	()
end



fun std_bvars stem tm = 
 let 
	open Lib
   fun num2name i = stem^Lib.int_to_string i
	val nameStrm = Lib.mk_istream (fn x => x+1) 0 num2name
	fun next_name () = state(next nameStrm)
	fun trav M = 
		if is_comb M then 
			let val (M1,M2) = dest_comb M
					val M1' = trav M1
					val M2' = trav M2 
			in mk_comb(M1',M2')
			end else 
		if is_abs M then 
			let val (v,N) = dest_abs(rename_bvar (next_name()) M)
			in mk_abs(v,trav N)
			end
		else M
 in 
   trav tm
 end; 

fun STD_BVARS_CONV stem tm = 
 let val tm' = std_bvars stem tm
 in Thm.ALPHA tm tm'
 end;

fun is_valid_c_indentifier s = 
	all (fn c => not (c = #"'")) (String.explode s)

fun dest_fun_def def = 
	let
		val def_term = concl (SPEC_ALL def);		
		val (fun_const, args) = strip_comb (lhs def_term);
		val body = rhs def_term;
		val (fun_name, fun_type) = dest_const fun_const
		val (arg_n, return_n) = get_word_fun_arity fun_type;
		val _ = syntax_error ((return_n <= 0) orelse (arg_n < 0) orelse
								    (length args > 1)) 
					("The function '"^fun_name^"' is not a function on 32-bit words!");
		val args_fv = FVL args Term.empty_varset
		val body_fv = FVL [body] Term.empty_varset
		val _ = syntax_error (not (HOLset.isSubset (args_fv, body_fv)))
					 ("There are free variables in the definition of '"^
						fun_name^"'!")
		val body_av = HOLset.addList (Term.empty_varset, Term.all_vars body);
		val body_bv = HOLset.difference (body_av, body_fv);
		val body_bv_list = HOLset.listItems body_bv;
		
		val args_list = if (args=[]) then [] else (pairLib.strip_pair (hd args));
	in
		(def_term, args_list, body_bv_list, body, fun_name, arg_n, return_n)
	end;


fun normalise_fun_def def force =
	let
		val (def_term, args_list, body_bv_list, body, fun_name, arg_n, return_n) = dest_fun_def def;

		val valid_bv = all (fn v => is_valid_c_indentifier (#1 (dest_var v))) body_bv_list;
		val def = SPEC_ALL def;
		val def' = if (force orelse not valid_bv) then
							Conv.CONV_RULE (Conv.RHS_CONV (STD_BVARS_CONV "v")) def
					  else def

		val valid_args = all (fn v => is_valid_c_indentifier (#1 (dest_var v))) args_list;

		val def'' = if (force orelse not valid_args) then
							let
								val ren = enumerate 1 args_list;
								val ren' = map (fn (n, t) => 
									({redex=t, residue = mk_var ("a"^(Int.toString n), word_type)})) ren;								
							in
								Thm.INST ren' def'
							end
					   else def'
	in
		def''
	end
	

fun translate_fun_to_c def =
	let
		val _ = temp_var_count := 0;
		val def = normalise_fun_def def false;
		val (def_term, args_list, body_bv_list, body, fun_name, arg_n, return_n) = dest_fun_def def;
		val def_string = "/* "^(term_to_string def_term)^ " */";

		val word_type_string = get_word_type 1;
		val args_string_list = map (fn arg => 
				word_type_string^ " "^(#1 (dest_var arg))) args_list;
		val args_string = String.concat (commafy args_string_list);
		val fun_sig = get_word_type (return_n) ^ " "^fun_name^ " ("^args_string^")";
		val var_decl = map (fn v =>
			let
				val (var_name, var_type) = dest_var v;
				val var_type_string = if (var_type = bool) then "bool" else
					let
						val arity = get_word_type_arity var_type 0
						val _ = syntax_error (arity <= 0) ("Variable '"^var_name^"' is not of type bool or a word type!");
					in
						get_word_type arity
					end
			in
				(var_type_string ^ " " ^ var_name ^ ";")
			end) body_bv_list
		val (body_inst, body_exp) = translate_exp body 1
		val return_inst = "return "^(hd body_exp)^";";
		val instL = [def_string,fun_sig^" {"]@(indent_block (var_decl @  body_inst @ [return_inst]))@["}"]
	in
		(fun_sig^";", instL)
	end


fun create_tests testL =
	let
 		val _ = temp_var_count := 0;

		fun create_f_test (f, tests) =
		let
			val (f_name, f_type) = dest_const f;
			val (args_n, res_n) = get_word_fun_arity f_type;
			val res_var = get_new_temp_var ();
			
			val decl_ret = (get_word_type res_n)^" "^res_var^";";
			fun create_single_test (arg, res) =
				let
					val args = pairLib.strip_pair arg;
					val args_string = map (fn t =>
							Arbnum.toString (numLib.dest_numeral (rand t))) args;
					val args_s = String.concat (commafy args_string)
					val fun_call = res_var^" = "^f_name^"("^args_s^");"

					val ress = pairLib.strip_pair res;
					val ress_string = map (fn t =>
							Arbnum.toString (numLib.dest_numeral (rand t))) ress;

					val conditionL = if (res_n = 1) then
							["("^res_var^" == "^(hd ress_string)^")"]
						 else
							(List.tabulate (res_n, (fn n =>
								"("^res_var^".e"^(Int.toString (n+1))^
								" == "^(el (n+1) ress_string) ^")")))
					val condition = foldl (fn (s1, s2) => s1 ^ " & "^s2) "1" conditionL;

					val error_message = "Test of '"^f_name^"("^args_s^")' failed!\\n";
					val error_inst = "if (! ("^condition^")) printf(\""^(String.toCString error_message)^"\");"
				in
					[fun_call,error_inst]
				end
			
			val test_insts = map create_single_test tests
		in	
			decl_ret::(List.concat test_insts)@[""]
		end;

		val all_tests = List.concat (map create_f_test testL)		
	in
		["void auto_tests() {"]@(indent_block all_tests)@["}"]
	end


fun create_main main_fun =
let
	val (f_name, f_type) = dest_const main_fun;
	val (args_n, res_n) = get_word_fun_arity f_type;
	val decl_ret = (get_word_type res_n)^" res;";
	val word_type_string = get_word_type 1;
	val args_list = List.tabulate (args_n, fn n =>
		("a"^(Int.toString (n+1))))
	val decl_args = map (fn s =>
		(word_type_string^" "^s^";")) args_list;
	val f_string = f_name^"("^(String.concat (commafy args_list))^")";
	val print_fun = "printf(\""^f_string^"\\n\");"

	val read_args = map (fn s =>
		("printf(\""^s^": \"); if (scanf(\"%ud\", &"^s^") == 0) exit(0);")) args_list
	val execution = "res = "^f_string^";"
	
	val res_words = if (res_n) = 1 then ["res"] else
							(List.tabulate (res_n, (fn n =>
								"res.e"^(Int.toString (n+1)))));
	val print_results = map (fn s=>"printf(\"- %ud\\n\", "^s^");") res_words;
	val print_space = "printf(\"\\n\\n\");"
	
	val body = [print_fun]@read_args@[execution,print_space]@print_results@[print_space]

	val run_auto_tests = ["auto_tests();", "", ""];
	val body' = run_auto_tests@decl_args@[decl_ret]@["","while (1) {"]@
					(indent_block body)@["}"]			
in
	["main () {"]@(indent_block body')@["}"]
end;		





fun translate_to_c dirname filename defs rewrites main_fun tests =
	let
		val defs' = (map (SPEC_ALL o (REWRITE_RULE rewrites)) defs)
		fun extract_fun_const def = (#1 (strip_comb (lhs (concl (SPEC_ALL def)))))
		val defined_funs = map extract_fun_const defs';
		val defs'' = zip (map dest_const defined_funs) defs';
		val defs'' = Listsort.sort (fn (((s1, _), _), ((s2, _),_)) => String.compare (s1, s2)) defs'';

		(*check for undefined functions*)
		val defined_funs_set = HOLset.addList (Term.empty_tmset, defined_funs);
		val _ = if (not (HOLset.member (defined_funs_set, main_fun))) then
					 (print "The main function is not in the list of definitions!\n";fail()) else ();

		val unknown_consts = get_unknown_consts (map concl defs');
		val unknown_consts = HOLset.difference (unknown_consts, defined_funs_set);
		val unknown_consts_list = HOLset.listItems unknown_consts;
		val _ = if (unknown_consts_list = []) then () else
				  let
					  val _ = print "The following constants are unkown to the C-export function. Please add additional definitions or rewrites:\n";
					  val _ = map (fn t => (print " - ";print_term t;print "\n")) unknown_consts_list
				  in
					 fail()
				  end 

		val _ = max_used_word_type := 1;		
	 	val (fun_decl, fun_defs) = unzip (map (fn (_, def) => translate_fun_to_c def) defs'');

(*		val def = #2 (el 3 defs'');
		translate_fun_to_c def;
*)

		val fun_defs = List.concat (map (fn l => l@["","",""]) fun_defs);

		val word_type_defs = List.tabulate ((!max_used_word_type), fn n => c_get_word_type (n+1))
		val word_type_defs = List.concat (map (fn l => l@[""]) word_type_defs);
		
		val auto_test = create_tests tests;
		val main_fun_def = create_main main_fun;
		val spaces = ["",""];


		(*write header file*)
		val file_name_header = filename^".h";
		val file_name_header_guard = filename^"_H";
		
	   val file_st = TextIO.openOut(dirname^file_name_header);
		val _ = map (fn s => TextIO.output(file_st, s^"\n")) 
			(["#ifndef "^file_name_header_guard, "#define "^file_name_header_guard, ""]@word_type_defs@spaces@fun_decl@["","#endif"]);
   	val _ = TextIO.output(file_st, "\n\n");
      val _ = TextIO.flushOut file_st;
	   val _ = TextIO.closeOut file_st;

		(*write fun_defs*)
		val inits = ["#include <stdio.h>",
						 "#include \""^file_name_header^"\""];
		val file_name_c = filename^".c";
	   val file_st = TextIO.openOut(dirname^file_name_c);
		val _ = map (fn s => TextIO.output(file_st, s^"\n"))
					(inits@spaces@fun_defs);
   	val _ = TextIO.output(file_st, "\n\n");
      val _ = TextIO.flushOut file_st;
	   val _ = TextIO.closeOut file_st;


		(*write test*)
		val file_name_test = filename^"-test.c";
	   val file_st = TextIO.openOut(dirname^file_name_test);
		val _ = map (fn s => TextIO.output(file_st, s^"\n"))
					(inits@spaces@auto_test@spaces@main_fun_def);
   	val _ = TextIO.output(file_st, "\n\n");
      val _ = TextIO.flushOut file_st;
	   val _ = TextIO.closeOut file_st;
	in
		()
	end

val r = Random.newgen ();

fun generate_word max =
	let
		val n = if (max = 0) then
						let
							val l = Random.rangelist (0, 65536)  (2, r);
							val n1 = Arbnum.fromInt (el 1 l);
							val n2 = Arbnum.* (Arbnum.fromInt (el 2 l), Arbnum.fromInt 65536);
							val n = Arbnum.+ (n1, n2);
						in
							n
						end
					else
						Arbnum.fromInt (Random.range (0, max) r)
	in
		mk_comb (Term `n2w:num->word32`, numSyntax.mk_numeral n)
	end;

fun generate_word_pair n max =
	let
		val wL = List.tabulate (n, fn n => generate_word max);		
	in
		pairSyntax.list_mk_pair wL
	end;

fun generate_word_pair_list n max m =
	List.tabulate (m, fn x => generate_word_pair n max);		

end;
