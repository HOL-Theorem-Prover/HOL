(*****************************************************************************)
(* File: encodeLib.sml                                                       *)
(* Author: James Reynolds                                                    *)
(*                                                                           *)
(* Provides the functions to encode HOL into ACL2                            *)
(*****************************************************************************)

(* Changelog: *)

(*	26/07/2006:	Version 2: Polytypism added, massive restructuring *)
(*	27/07/2006:	Improved the type-checking to complete nchotomys (~A ==> (A \/ B = B))
			Judgements with remaining hypothesis are no longer allowed *)
(*	31/07/2006:	Added 'convert_theorem' to convert theorems in a similar manner to convert_definition
			Added an IMP_CONV to convert A ==> B but prefix hypothesis with A
			Added sexp_type_imp_term to the type checker, for terms of the form:
				|= booleanp (implies (consp a) (car a)) etc... *)
(*	02/08/2006:	Added a simple decision checker, helps with converting '0 < b ==> P (a DIV b)' etc...
			Now uses caar etc... to simplify terms *)
(*	08/08/2006:	Modified 'attempt_decision' to work with terms such as 'P ==> ~(2 = 0)` *)
(*	09/08/2006:	Added a FULL_BETA_CONV to the pre-processing stage, simplifies: (\(a,b).f a b) x = f (FST x) (SND x)
			Modified 'RECURSE_CONV' so it now instantiates free encoders (eg. pair f nat (f a b))
			Modified 'is_encoded_term' to match free encoders
			Modified theorem matching in ACL2_DEPTH_CONV to do the same *)
(*	10/08/2006:	Added a 'convert_definition_restricted' which allows predicates to be placed on arguments such as `~(n = 0)'
			Fixed get_recogniser so it works properly with lists and pairs
			Changed get_recogniser so it now outputs a correctness theorem for 
the recogniser *)
(* 	11/08/2006:	Added a 'convert_definition_full' which allows addition of variant theorems to assist termination in ACL2, eg `!a. 0 < a ==> a DIV 2 < a'
			Modified convert_theorem so |= implies a b is output, instead of (|= a) ==> (|= b) *)
(*	12/08/2006:	Recursion theorems and restriction terms now have the forms: `!v0...vn. P v0...vn` and `\v0....vn. P v0...vn` *)
(*	14/08/2006:	Bug-fixes to allow type checking of |= natp (add a (unary_minus (nat 1))), formed by modified NAT_CASE thm in translateTheory *)
(*	15/08/2006:	Bug-fix: definitions were being created with hypothesis left in due to not cleaning the hypothesis set after removing recursion theorems
			Bug-fix: recursion theorems with > 1 hypothesis couldn't be removed from the theorem
			Bug-fix: creation of the judgement theorem failed if it couldn't remove a recursive theorem
			Bug-fix: improved the removal of restrictions and recursion theorems from the correctness theorem *)
(* 	07/09/2006:	Changed convert_theorem to use |- x = |= bool x instead, code is now much cleaner.
			Changed encode_all to remove type variables
			Changed encode_decode_function to also encode HO arguments
			stage3 is now modified to ensure the variable naming is consistent with stage4
			Type constraints for functions now work for HO arguments
			Encoder matching in IF_CONV, prevents some mismatch bugs
			Modified DISCH_HYPS so it actually works! *)
(*	08/09/2006:	Modified make_acl2_definition & make_judgement so that HO functions that 
			preserve arguments may now be converted (eg. FILTER) *)
(*	19/09/2006:	Variables renamed to avoid restricted keywords *)
(*	25/09/2006:	let terms and lambda terms are now handled natively, see DIVMOD / findq examples
			Bugs in curry_single_function & convert_theorem fixed
			String and character conversions implemented
			Improved 'attempt_decision' *)
(*	11/11/2006:	Completely rewritten nchotomy checking, now uses local resolution in DNF
			Can now process functions with incomplete specification
			The convert_definition interface has been simplified and allows extra theorems for resolution
			Added some simple caching to the typing procedures *)
(*	07/02/2006:	Modified to work with natp from def axioms *)

(* Interactive stuff... *)
(*
app load ["translateTheory","listLib","intLib","translateLib"];
*)

open HolKernel boolLib bossLib Q Parse combinTheory computeLib
     Conv Thm Tactical BasicProvers Tactic Drule Definition translateTheory translateLib 
     listTheory numLib listLib pairLib pairTheory sexpTheory hol_defaxiomsTheory sumTheory Lib arithmeticTheory;

(*****************************************************************************)
(* Error handling and tracing                                                *)
(*****************************************************************************)

val type_encode_trace = ref 0;
val func_encode_trace = ref 0;

fun tprint_trace level m = if level <= !type_encode_trace then print m else ()
fun fprint_trace level m = if level <= !func_encode_trace then print m else ()

val _ = register_trace ("EncodeLib.TypeEncoding",type_encode_trace,4);
val _ = register_trace ("EncodeLib.FunctionEncoding",func_encode_trace,4);

fun raise_error stage function error = 
	let val func = if stage > 0 then "Stage " ^ int_to_string stage ^ ": " ^ function else function
	in
		raise (mk_HOL_ERR "encodeLib" func error)
	end;

fun wrap_exn stage function exn = 
let 	val func = if stage > 0 then "Stage " ^ int_to_string stage ^ ": " ^ function else function
in	
	raise (mk_HOL_ERR "encodeLib" func (exn_to_string exn))
end;


(*****************************************************************************)
(* Theorems required in the conversion process                               *)
(*****************************************************************************)

val DOUBLE_OR = GEN_ALL (last (CONJUNCTS (SPEC_ALL OR_CLAUSES)));

val TRUE_IMP = GEN_ALL (CONJUNCT1 (SPEC_ALL IMP_CLAUSES));

val FALSE_IMP = GEN_ALL (last (CONJUNCTS (SPEC_ALL IMP_CLAUSES)));

val [NOT_NOT,NOT_TRUE,NOT_FALSE] = CONJUNCTS NOT_CLAUSES;

val (NOT_AND_IMP,NOT_IMP_IMP) = EQ_IMP_RULE (SPEC_ALL NOT_IMP);

val AND_TRUE = el 2 (CONJUNCTS (SPEC_ALL AND_CLAUSES));

val IMP_DISTRIB = 
	DISCH ``A ==> B ==> C`` (DISCH ``A ==> B`` (DISCH ``A:bool``
		(PROVE_HYP (UNDISCH (ASSUME ``A ==> B``)) (UNDISCH_ALL (ASSUME ``A ==> B ==> C``)))));

val IF_THMS = CONJ (el 5 (CONJUNCTS TRUTH_REWRITES)) (el 4 (CONJUNCTS TRUTH_REWRITES))

val IF_THMS_IMP = prove(``((|= P) ==> (a = ite P a b)) /\ ((~|= P) ==> (b = ite P a b))``,RW_TAC std_ss [ite_def,TRUTH_REWRITES]);

val BOOL_TRUE = last (CONJUNCTS TRUTH_REWRITES);

val CDR_THM = prove(``(?b. x = cons a b) ==> (x = cons a (cdr x))``,Cases_on `x` THEN REWRITE_TAC [cdr_def,sexp_distinct,sexp_11] THEN STRIP_TAC);

val EQUAL_TRUE = prove(``(a = b) ==> (|= a) ==> (|= b)``,RW_TAC std_ss [TRUTH_REWRITES]);

val ACL2_OR = prove(``(|= ite a t b) = (|= a) \/ (|= b)``,Cases_on `|= a` THEN Cases_on `|= b` THEN RW_TAC std_ss [ite_def,TRUTH_REWRITES]);

val ACL2_AND = prove(``(|= ite a b nil) = (|= a) /\ (|= b)``,Cases_on `|= a` THEN Cases_on `|= b` THEN RW_TAC std_ss [ite_def,TRUTH_REWRITES]);

val PAIRP_THM = prove(``!x. pairp l r x = ite (consp x) (ite (l (car x)) (r (cdr x)) nil) nil``,
				Cases THEN RW_TAC std_ss [ite_def,car_def,cdr_def,pairp_def,consp_def,TRUTH_REWRITES])

val EQUAL_EQ = prove(``(|= equal x y) = (x = y)``,RW_TAC std_ss [equal_def,TRUTH_REWRITES]);

val gsym_car_cdr_thms = filter (C mem [``car``,``cdr``] o repeat rator o rhs o snd o strip_forall o concl) 
				(filter (is_eq o snd o strip_forall o concl) (CONJUNCTS ACL2_SIMPS));

val car_cdr_thms = map GSYM gsym_car_cdr_thms

val OR_IMP_CONVERT = DECIDE ``(A \/ B) ==> ((~A ==> B) /\ (~B ==> A))``

val CORRECT_CONVERT = prove(``(~X ==> ((if Y then a else b) = c)) ==> ((~X ==> ~Y) ==> (~X ==> (b = c)))``,
	REPEAT STRIP_TAC THEN RES_TAC THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC []);

(*****************************************************************************)
(* Composition tools, like MK_COMB/mk_comb but allows instantiation          *)
(*****************************************************************************)

(* Returns a new string, a single character greater than the input *)
fun addc [] = [#"a"]
  | addc (x::xs) = if x >= #"z" then #"1" :: addc xs else (if x >= #"9" andalso x < #"a" then #"a" :: xs else Char.succ x :: xs);

fun next_var s = (implode o rev o addc o rev o explode) s;

fun new_var L = repeat (fn x => if mem x L then next_var x else raise Empty) "a";

(* Replace a variable with a nicer one *)
fun fix_thm_var var thm = 
let	val vars = map (fst o dest_var) (HOLset.listItems(HOLset.addList(hyp_frees thm,thm_frees thm)))
in
	INST [var |-> mk_var(new_var vars,type_of var)] thm
end;

(* Replace a type variable with a nicer one *)
fun fix_thm_type tv thm =
let	val vars = map ((fn x => String.extract (x,1,NONE)) o dest_vartype) (HOLset.listItems(HOLset.addList(hyp_tyvars thm,(type_vars_in_term o concl) thm)))
in
	INST_TYPE [tv |-> mk_vartype ("'" ^ (new_var vars))] thm
end;

(* Replace a type variable with a nicer one *)
fun fix_term_type tv term =
	inst [tv |-> mk_vartype ("'" ^ (new_var (map ((fn x => String.extract (x,1,NONE)) o dest_vartype) (type_vars_in_term term))))] term;


fun IMK_COMB (thm1,thm2) = 
let 	val vartype = gen_tyvar()
	val t1 = (type_of o lhs o concl) thm1
	val t2 = (type_of o lhs o concl) thm2
	val (t1',t2') = if can dom_rng t1 then ((fst o dom_rng) t1,t2) else (t1,t2 --> vartype)
	fun match_type_occurs t1 t2 = 
		let val match = match_type t1 t2 in
			if exists (fn {redex,residue} => type_var_in redex residue) match then raise (mk_HOL_ERR "encodeLib" "IMK_COMB" "Types fail occurs check") else match
		end
in
	fix_thm_type vartype (MK_COMB (INST_TYPE (match_type_occurs t1' t2') thm1,thm2) handle e => MK_COMB (thm1,INST_TYPE (match_type_occurs t2' t1') thm2))
end;

fun IAP_TERM term thm = IMK_COMB (REFL term,thm);
fun IAP_THM thm term = IMK_COMB (thm,REFL term);

(* imk_comb: same as mk_comb except tries to instantiate the left or right type domain to match *)
fun imk_comb (term1,term2) = 
let 	val vartype = gen_tyvar()
	val t1 = type_of term1
	val t2 = type_of term2
	val (t1',t2') = if can dom_rng t1 then ((fst o dom_rng) t1,t2) else (t1,t2 --> vartype)
in
	fix_term_type vartype (mk_comb (inst (match_type t1' t2') term1,term2) handle e => mk_comb(term1,inst (match_type t2' t1') term2))
end;

(* ILIST_MK_COMB: term * thm list -> thm  : Takes a constructor and a list of equality theorems to create a constructed equality term *)
fun ILIST_MK_COMB (term,thms) = 
	foldl (fn (a,b) => IMK_COMB (b,a)) (REFL term) thms;

(*****************************************************************************)
(* Thm manipulation tools                                                    *)
(*****************************************************************************)

(* Attempt remove the antecedent by decision *)
fun DECIDE_ANTE thm = 
	MATCH_MP thm (DECIDE ((fst o dest_imp o concl) thm));

(* Performs CHOOSE for a list of variables *)
local
fun get_exists x = 
	let 	val (v,b) = Psyntax.dest_exists x
		val (l,r) = get_exists b
	in	(v::l,x::r) end handle e => ([],[])
in
fun CHOOSE_L (vars,cthm) thm = 
let	val (xvars,bodies) = get_exists (concl cthm);
in
	PROVE_HYP cthm (foldr (uncurry CHOOSE) thm (map2 (C pair o ASSUME o subst (map2 (curry op|->) xvars vars)) bodies vars))
end
end;

(* A version of UNDISCH_ALL that converts any conjunctions to separate hypothesis *)
fun CUNDISCH_ALL thm = 
	(CUNDISCH_ALL (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) thm) handle e => CUNDISCH_ALL (UNDISCH thm)) handle e => thm;

(* Like DISCH_ALL but conjuncts the hypothesis together *)
fun DISCH_AND_CONJ thm = 
	foldl (fn (h,thm) => CONV_RULE (REWR_CONV AND_IMP_INTRO) (DISCH h thm)) (DISCH (hd (hyp thm)) thm) (tl (hyp thm)) handle Empty => thm;

(* Apply a CONV to all of the hypothesis *)
fun CONV_HYP c thm =
let 	fun UNDISCHi thm = CONV_RULE (REWR_CONV TRUE_IMP) thm handle _ => UNDISCH thm
	fun conv (thm,[]) = thm
      	  | conv (thm,h::hs) = conv (UNDISCHi (CONV_RULE (LAND_CONV c) (DISCH h thm)),hs)
in
     conv (thm, hyp thm)
end;

(* Fold a function f : term -> thm -> thm over the hypothesis set *)
fun FOLD_HYP f thm = foldl (uncurry f) thm (hyp thm);

(* Like strip_imp but don't do ~a --> a ==> F *)
fun rstrip_imp term = 
	if is_neg term then ([],term) else 
		let val (a,(b,c)) = (I ## rstrip_imp) (dest_imp term) in (a::b,c) end handle e => ([],term);

fun rdest_imp term = if is_neg term then raise (mk_HOL_ERR "encodeLib" "rdest_imp" "not an \"==>\"") else dest_imp term;

fun ris_imp term = is_imp term andalso not (is_neg term);

(* Like UNDISCH_ALL but don't do |- ~a --> [a] |- F *)
fun RUNDISCH_ALL thm = 
	if (ris_imp o concl) thm then (RUNDISCH_ALL o UNDISCH) thm
	else thm;

(* Splits a hypothesis [R ==> A /\ B,...] to [R ==> A, R ==> B, ...] *)
fun split_hyp h thm = 
let	val (imps,c) = rstrip_imp h
in
	PROVE_HYP (foldr (uncurry DISCH) (LIST_CONJ (map (RUNDISCH_ALL o ASSUME o curry list_mk_imp imps) (strip_conj c))) imps) thm
end;

(* Strips an ite of the form: ite p0 a0 (ite p1 a1 (ite .... *)
fun strip_ite term = 
let 	val (p,a,b) = dest_acl2_cond term
	val (bs,last) = strip_ite b 
in	((p,a)::bs,last) end handle e => ([],term);

(* A variable to store ``:sexp`` *)
val sexp_type = ``:sexp``;

(*****************************************************************************)
(* Encoding/Decoding tools:                                                  *)
(*                                                                           *)
(* reachable : (''a -> ''a list) -> ''a -> ''a list                          *)
(*     - Given a function to list next nodes and a start node returns all    *)
(*       nodes reachable from the start node                                 *)
(* return_cycles : (''a -> ''a list) -> ''a -> ''a list list                 *)
(*     - Given a function to list next nodes and a start node returns a      *)
(*       list of cycles and nodes not contained in cycles                    *)
(* base_type : hol_type -> hol_type                                          *)
(*     - Returns a type with no type variables instantiated                  *)
(* required_functions : hol_type -> hol_type list                            *)
(*     - Returns a list of types which would need to be encoded/decoded for  *)
(*       this type to be encoded or decoded                                  *)
(* get_conjuncts : hol_type -> thm list                                      *)
(*     - Returns a list of case thms from the case definition                *)
(* get_type_chain : hol_type -> hol_type list * hol_type list hol_type list  *)
(*     - Returns a list of types mutually recursive with the type, and a     *)
(*       list of sub-types                                                   *)
(*                                                                           *)
(*****************************************************************************)

(* Returns sets of variables, with those included in cycles together *)
local
	fun group opr L var = 
	let	val new = set_diff (map (pair var) (opr var)) L
	in	if new = [] then L else (foldl (fn (var,L) => group opr L var) (new @ L) (map snd new)) end
 	fun mergeif (x,y) L = if snd x = fst y then (if mem (fst x,snd y) L then L else (fst x,snd y)::L) else L;
	fun allpairs _ [] = []
          | allpairs [] _ = []
          | allpairs (x::xs) (y::ys) = mergeif (x,y) (union (allpairs xs (y::ys)) (allpairs (x::xs) ys))
	fun addnew pair pairs = 
	 	U ((pair::pairs)::(map2 allpairs [[pair],(filter (fn x => snd x = fst pair) pairs),(filter (fn x => snd x = fst pair) pairs)]
						[(filter (fn x => fst x = snd pair) pairs),[pair],(filter (fn x => fst x = snd pair) pairs)]));
	fun trans_close group = foldl (uncurry addnew) [] group
	fun mutual_vars reachable (v1,group) = 
		(v1,filter (fn v2 => (exists (fn pair => pair = (v1,v2)) group) andalso (exists (fn pair => pair = (v2,v1)) group)) (set_diff reachable [v1]))
	fun proper_subset x y = all (C mem y) x andalso (not (x = y));
	fun remove_subsets l1 l2 = filter (not o C (op_mem proper_subset) l2) l1;
in
	fun reachable opr start = mk_set (start::(map snd (group opr [] start)))
	fun return_cycles opr start =
	let 	val reach = reachable opr start
	in
		(fn x => remove_subsets x x) (op_mk_set set_eq (map (op:: o mutual_vars reach) (zip reach (map (trans_close o group opr []) reach))))
	end
end;

(* Return the base type for an instantiated type *)
fun base_type t = 
	(last o fst o strip_fun o type_of o TypeBase.case_const_of) t handle e => t;

(* Given a type, return a list of types which would have to be encoded/decoded for this to be encoded/decoded *)
fun required_functions t = 
let	val inst_types = map2 (curry op|->) (snd (dest_type (base_type t))) (snd (dest_type t))
in
	map (type_subst inst_types) (flatten ((map (fst o strip_fun) o fst o strip_fun o type_of o TypeBase.case_const_of) t))
end  handle _ => [];

fun get_type_chain t = 
let	val all_types = first (fn x => mem (base_type t) x) (return_cycles required_functions (base_type t))
	val (types,extra_types) = (map base_type ## map base_type) (partition (fn t => mem t ((reachable required_functions o base_type) t)) all_types);

	val all_types_concrete = first (fn x => mem t x) (return_cycles required_functions t)
	
	fun mapping [] ys = []
          | mapping (x::xs) ys =
	let	val (poss,nposs) = partition (can (match_type x)) ys
		val selects = map (fn (a,b) => (hd b, a @ (tl b) @ nposs)) (foldl (fn ((x,y),l) => split_after x poss::l) [] (enumerate 0 poss))
	in	tryfind (fn (ti,to) => (x,ti)::mapping xs to) selects end;


	fun fix_type L = map snd (mapping L all_types_concrete)	

in
	(fix_type types,fix_type extra_types,mk_set (filter (not o is_vartype)
				(filter (fn x => null (intersect (reachable required_functions x) all_types_concrete))
					(flatten (map (reachable required_functions) all_types_concrete)))))
end;

(* Return a list of conjunctions from a case definition *)
fun get_conjuncts x = map SPEC_ALL (CONJUNCTS (TypeBase.case_def_of x));


(*****************************************************************************)
(* Stage 1: Replace function clauses with case statements                    *)
(*                                                                           *)
(*         |- (!m. m ** 0 = 1) /\ !m n. m ** SUC n = m * m ** n              *)
(*    ---> |- m ** n = case n of 0 -> 1 || SUC n -> m * m ** n               *)
(*                                                                           *)
(*****************************************************************************)

fun assume_and_rewrite nchotomy_thm thms = 
let	val disjuncts = (strip_disj o concl o SPEC_ALL) nchotomy_thm
	val case_term = repeat (fn x => mk_comb(x,variant (free_vars x) (mk_var("x",(fst o dom_rng o type_of) x)))) 
		((TypeBase.case_const_of o type_of o rhs o snd o strip_exists o hd) disjuncts)
	fun REWRITE rthm thm = CONV_RULE (DEPTH_CONV (fn term => 
		if can (match_term case_term) term then RAND_CONV (REWR_CONV rthm) term else NO_CONV term) THENC RAND_CONV (DEPTH_CONV (REWR_CONV rthm))) thm
	fun rewrite_thm thm rewrite = 
		snd (foldl (fn (v,(term,thm)) => (list_mk_exists ([v],term),CHOOSE (v,ASSUME (list_mk_exists ([v],term))) thm))
		((snd o strip_exists) rewrite,
		REWRITE	((SYM o ASSUME o snd o strip_exists) rewrite)
			(UNDISCH (DISCH rewrite 
			(INST_TY_TERM (match_term ((last o snd o strip_comb o snd o strip_abs o lhs o concl) thm) 
				((rhs o snd o strip_exists) rewrite)) thm)))) ((rev o fst o strip_exists) rewrite))
in
	map (fn x => tryfind (rewrite_thm x) disjuncts) thms
end;

(* Combine two substitutions *)
fun combine_subs (x:{redex : term, residue : term} list list,y:{redex : hol_type, residue : hol_type} list list) = 
	((op_mk_set (curry (op= o (#redex ## #redex))) o flatten) x,(op_mk_set (curry (op= o (#redex ## #redex))) o flatten) y)

(* join all the cases of a function together *)
fun join_cases nchotomy_thm = DISJ_CASESL (SPEC_ALL nchotomy_thm) o assume_and_rewrite nchotomy_thm;

(* Return various parameterisation theorems for case statements *)
fun make_case_thms t = 
let 	val typevar = gen_tyvar()
	val gfun = mk_var("g",typevar)
	val xvar = genvar typevar
	
	val nchotomy_thm = TypeBase.nchotomy_of t
	val conjuncts = map SPEC_ALL (CONJUNCTS (TypeBase.case_def_of t))
	val eta_terms = map2 	(fn x => fn y => let val var_list = (snd o strip_comb) x in (foldl (fn (a,b) => mk_comb (b,a)) (foldr mk_abs y var_list) var_list) end)
				(map (rhs o concl) conjuncts)

	val conjuncts1 = map (BETA_RULE o INST_TY_TERM (combine_subs (unzip ((fn x => map2 match_term x (eta_terms x)) (map (rhs o concl) conjuncts))))) conjuncts
	val conjuncts2 = map (IAP_TERM gfun) conjuncts1
	val conjuncts3 = map (fn x => IAP_THM x xvar) conjuncts1
	val conjuncts4 = map (MK_ABS o GEN xvar o INST (map (fn x => x |-> inst (match_type alpha (type_of x)) (mk_comb(mk_var("f",typevar --> alpha),xvar))) 
					(map (repeat rator o rhs o concl) conjuncts1))) conjuncts1;

	val subs1 = (combine_subs o unzip o map (fn x => match_term (rhs x) ((rand o lhs) x)) o map concl) conjuncts1
	val subs2 = (combine_subs o unzip o map2 match_term (map (rhs o concl) conjuncts1)) (eta_terms (map (rhs o concl) conjuncts2))
	val subs3 = (combine_subs o unzip o map2 match_term (map (rhs o concl) conjuncts1)) (eta_terms (map (rhs o concl) conjuncts3))
	val subs4 = (combine_subs o unzip o map2 (fn x => fn y => match_term (fst x) (list_mk_abs(snd x,(rhs o concl) y))) 
				(map (strip_comb o rhs o concl) conjuncts1)) conjuncts4

	val join = GSYM o join_cases nchotomy_thm
	fun rename_bvar thm = 
		CONV_RULE (BINOP_CONV (ONCE_DEPTH_CONV (
			fn term => if (is_genvar o fst o dest_abs) term then RENAME_VARS_CONV [new_var (map (fst o dest_var) (free_vars term))] term else NO_CONV term))) thm

in
	(((join o CONJUNCTS o INST_TY_TERM subs1 o LIST_CONJ) conjuncts1,
	 (fix_thm_type typevar o join o map GSYM o map2 TRANS conjuncts2) (map (GSYM o BETA_RULE o INST_TY_TERM subs2) conjuncts1)),
	((fix_thm_type typevar o fix_thm_var xvar o join o map GSYM o map2 TRANS conjuncts3) (map (GSYM o BETA_RULE o INST_TY_TERM subs3) conjuncts1),
	 (rename_bvar o fix_thm_type typevar o join o map GSYM o map2 TRANS conjuncts4) (map (BETA_RULE o GSYM o INST_TY_TERM subs4) conjuncts1)))
end;

val case_thms = ref [] : ((thm * thm) * (thm * thm)) list ref;

local
fun safe_INST_TYPE subs thm = 
let	val type_vars = type_vars_in_term (concl thm)
	val set1 = set_diff type_vars (map #redex subs)
	val set2 = set_diff (map #redex subs) (map #residue subs)
	val (replace_set,subs') = partition (fn {redex,residue} => mem residue set1) subs
	val (s1,s2) = foldl (fn (({redex,residue},v),(s1,s2)) => let val x = gen_tyvar() in ((redex |-> x) :: s1,(x |-> residue) :: (residue |-> v) :: s2) end) 
			(subs',[]) (zip replace_set (List.take (set2,length replace_set)))
in
	INST_TYPE s2 (INST_TYPE s1 thm)
end
fun instantiate t thm =
		safe_INST_TYPE (match_type ((type_of o last o snd o strip_comb o rhs o concl) thm) t) thm
fun inst4 t = ((instantiate t ## instantiate t) ## instantiate t ## instantiate t)
in
fun get_case_thms t = 
	tryfind (inst4 t) (!case_thms) handle _ => 
	(case_thms := make_case_thms t :: !case_thms ; (inst4 t) (hd (!case_thms)))
end;
 
val get_case_refl = fst o fst o get_case_thms;
val get_case_lid = snd o fst o get_case_thms;
val get_case_rid = fst o snd o get_case_thms;
val get_case_abs = snd o snd o get_case_thms;

fun transpose [] = [] 
  | transpose L = (map hd L) :: transpose (map tl L) handle e => [];

(* argument_list - Returns sets of each curried argument from all function clauses, along with the function itself *)
fun argument_list thm = ((hd ## transpose) o unzip o map (strip_comb o fst o dest_eq o snd o strip_forall) o strip_conj o concl) thm;

(* Take the first variable in the constructor we find, if we don't find one, just use variants of a *)
fun make_var_list [] L = []
  | make_var_list (args::clauses) L =
	let val x = (tryfind (fst o dest_var) (all_varsl args) handle _ => new_var L) in x :: make_var_list clauses (x :: L) end;


(* Given a list of argument clauses and a term makes a case statement theorem *)
(* - Will partition the arguments to ensure that the list is partitioned so   *)
(*   the resulting tree formed is balanced                                    *)
(*                                                                            *)
(* strip_thm_case [[A,B,A,B,A,B],[X,X,Y,Y,Z,Z]] ``m a b`` -->                 *)
(*     case b of X -> m (strip_thm_case [[A,B],[X]]) X                        *)
(*            || Y -> m (strip_thm_case [[A,B],[Y]]) Y                        *)
(*            || Z -> m (strip_thm_case [[A,B],[Z]]) Z                        *)    
(*                                                                            *)

val var_setify = op_mk_set (fn a => fn b => can (match_term a) b andalso can (match_term b) a)

local
	fun metric (x,y) = 
		if (length x > 1 orelse (is_var y andalso not (is_var (hd x)))) then length x else 0
	fun min_len (item,c) [] = item
          | min_len (NONE,c) (x::xs) = if metric x > 0 then min_len (SOME x,metric x) xs else min_len (NONE,c) xs
	  | min_len (item,c) (x::xs) = if metric x > 0 andalso metric x < c then min_len (SOME x,metric x) xs else
						min_len (item,c) xs
	fun combine_case_list l [] = raise Empty
	  | combine_case_list l [x] = (x,[])
	  | combine_case_list l (x::y::xys) = 
		combine_case_list l
			(RIGHT_CONV_RULE (TRY_CONV (FIRST_CONV (map HO_REWR_CONV l))) (MK_COMB(x,y))::xys) handle e =>
		let 	val (y',xys') = combine_case_list l (y::xys)
		in	if can (dom_rng o type_of o lhs o concl) x then combine_case_list l (x::y'::xys') else (x,y'::xys')
		end handle e => (x,y::xys);
	fun fix_list (list,term) = 
		if all (same_const (repeat rator term) o repeat rator) list then 
			(var_setify (map (repeat rator) list),repeat rator term)::
				(flatten (map fix_list (zip (transpose (map (snd o strip_comb) list)) (snd (strip_comb term)))))
		else [(var_setify list,term)]
	fun fix_list_vars A [] = []
          | fix_list_vars A ((constructors,var)::rest) = 
		if is_var var 	then (constructors,variant A var)::fix_list_vars ((variant A var)::A) rest
				else (constructors,var)::fix_list_vars A rest
in	
fun split_thm_case list =
let	val (nvars,vars) = partition (exists is_comb o fst) list
in
	case (mapfilter valOf [min_len (NONE,0) nvars,min_len (NONE,0) vars])
	of (x::xs) => 
		let	val rewrite = PART_MATCH lhs ((get_case_refl o type_of o hd o fst) x) (snd x)
			val lid = (get_case_lid o type_of o snd) x;
			val rid = (get_case_rid o type_of o snd) x;
			val thm = fst (combine_case_list [rid,lid] (map (fn (_,y) => if y = snd x then rewrite else REFL y) list));
			val (pre_list,post_list) = (I ## tl) (split_after (index (curry op= x) list) list)
			val next_lists = 
				map (fn c => pre_list @ (fix_list 
					(filter (fn x => same_const (repeat rator x) (repeat rator c)) (fst x),c)) @ 
						post_list)
				((map snd o (fn (a,b,c) => c) o TypeBase.dest_case o rhs o concl) rewrite);
			val full = map (fix_list_vars []) (filter (exists (not o null o fst)) next_lists)
		in
			RIGHT_CONV_RULE (ONCE_REWRITE_CONV (map split_thm_case full)) thm
		end
	| [] => (fst o combine_case_list [] o map (REFL o snd)) list
end
end;

(* Check if a term is constructor for a type *)
fun is_constructor x = 
let	val t = snd (strip_fun (type_of x))
	val constructors = 
		map (fn x => inst (match_type ((snd o strip_fun o type_of) x) t) x) (TypeBase.constructors_of t) handle e => []
in
	mem x constructors
end;

(* Convert a theorem to case form *)
fun convert_tc function =
let	val arg_list = argument_list function
	val var_list = make_var_list (snd arg_list) []
	val vars = map2 (curry mk_var) var_list ((fst o strip_fun o type_of o fst) arg_list)
	val term = list_mk_comb(fst arg_list,vars);
	val list = zip ([fst arg_list]::(map var_setify (snd arg_list))) (op:: (strip_comb term));
	val bad_terms = flatten (flatten (map (map 
				(find_terms (fn x => not (is_comb x) andalso not (is_constructor x orelse is_var x))) o fst) (tl list)))
	val _ = if null bad_terms then () else
			raise_error 1 "convert_tc" 
				("Non-constructor '" ^ (term_to_string (hd bad_terms)) ^ "' found in function definition")
in
	RIGHT_CONV_RULE (ONCE_REWRITE_CONV (CONJUNCTS (SPEC_ALL function))) (split_thm_case list)
end;

(* Return unwritten cases from the conclusion *)
fun incomplete rights term terms = 
	if TypeBase.is_case term andalso not (exists (can (C match_term term)) rights) then
		let	val (_,_,cases) = TypeBase.dest_case term;
		in	foldr (uncurry (incomplete rights)) terms (map snd cases) end
	else
		if exists (can (C match_term term)) rights then terms else term::terms
	

(*****************************************************************************)
(* Stage 2: Curry all arguments with only one case:                          *)
(*                                                                           *)
(* |- (add_pair (0,b) = b) /\ (add_pair (SUC n,b) = add_pair (n,SUC b))      *)
(* |- add_pair b = case b of (0,b) -> b || (SUC n,b) -> add_pair (n,SUC b)   *)
(* |- add_pair b = pair_case                                                 *) 
(*      (\a b. case a of 0 -> b || SUC n -> add_pair (n,SUC b)) b            *)
(* |- add_pair (a,b) = case a of 0 -> b || SUC n -> add_pair (n,SUC b)       *)
(* |- (\a b. add_pair (a,b)) a b =                                           *)
(*      case a of 0 -> b || SUC n -> add_pair (n,SUC b)                      *)
(*                                                                           *)
(*****************************************************************************)

(* Like INST_TY_TERM but for terms *)
fun	inst_subst (x,y) = subst x o inst y

(* Replace the argument relating to the top case statement with a constructed one *) 
fun construct_argument thm = 
let	val 	argument = (last o snd o strip_comb o rhs o concl) thm
	val 	case_def = (TypeBase.case_def_of o type_of) argument
in
	RIGHT_CONV_RULE (REWR_CONV case_def THENC PairRules.LIST_PBETA_CONV) 
		(INST [argument |-> inst_subst (combine_subs (unzip (map2 match_term 
			((snd o strip_comb o rhs o concl o SPEC_ALL) case_def) 
				((fst o strip_abs o hd o snd o strip_comb o rhs o concl) thm))))
			((last o snd o strip_comb o lhs o concl o SPEC_ALL) case_def)] thm)
end;

(* Find the case on the variable given and pull it to top level *)
fun pull_case thm var =
let 	val get_var = last o snd o strip_comb
	val case_abs = (get_case_abs (type_of var),get_var o snd o dest_abs)
	val case_rid = (get_case_rid (type_of var),get_var o rator)
	val case_lid = (get_case_lid (type_of var),get_var o rand)
in
	RIGHT_CONV_RULE (REDEPTH_CONV (FIRST_CONV (map (fn (thm,varf) => fn term => 
		let val res = HO_PART_MATCH lhs thm term in if (varf term = var) then res else NO_CONV term end) [case_abs,case_rid,case_lid]))) thm
end;

(* First tests to see if the case statement refers to the variable we think it does... *)
fun construct_arg_test var thm = 
	if (last o snd o strip_comb o rhs o concl) thm = var then construct_argument thm else thm;

(* Abstract over all of a functions arguments then apply them *)
fun curry_thm thm = 
let val curried_thm = (fn x => DEPTH_CONV BETA_CONV x handle UNCHANGED => REFL x)
			((fn vars => foldl (fn (a,b) => mk_comb (b,a)) 
				(foldr mk_abs ((lhs o concl) thm) vars) vars) ((free_vars_lr o lhs o concl) thm))
in
	TRANS curried_thm thm
end;

(* 'Curry' all the arguments we can *)
fun curry_single_function thm =
let	fun is_recursive thm = 
	let	val (rfuns,c) = (strip_exists o snd o strip_forall o concl) thm
		val clauses = map (snd o strip_forall) (strip_conj c)
		fun recursive_rfun rfun = 
		let	val cycles = return_cycles (fn rfun => flatten (map (find_terms (C mem rfuns) o rhs) (filter (curry op= rfun o repeat rator) clauses))) rfun
		in	length cycles > 1 orelse exists (fn c => repeat rator (lhs c) = rfun andalso can (find_term (curry op= rfun)) (rhs c)) clauses
		end
	in	
		exists recursive_rfun rfuns
	end	
	fun is_single_case t = (not o is_recursive o TypeBase.axiom_of) t andalso 
					(length o strip_disj o concl o SPEC_ALL o TypeBase.nchotomy_of) t = 1 
				handle _ => false
	fun curry_arguments thm = 
	let	val arguments = filter (is_single_case o type_of) ((map hd o snd) (argument_list thm))
	in	if null arguments then REFL (hd arguments) else 
			curry_thm (CONV_RULE (FORK_CONV (DEPTH_CONV BETA_CONV,ALL_CONV)) (foldl (fn (arg,thm) => construct_arg_test arg (pull_case thm arg)) thm arguments))
	end;
in
	repeat curry_arguments thm
end;

(*****************************************************************************)
(* Type encoding: Create encode, decode & predicate functions                *)
(*                                                                           *)
(*                                                                           *)
(*****************************************************************************)

(* Return an encoder for the type given *)
local
	val pair_proof = REWRITE_RULE [FST,SND] (ISPECL [``f:'a -> sexp``,``g:'b -> sexp``,``(p,q):'a # 'b``] pair_def)
in
val encoders = ref [
	(``:'a # 'b``,(``pair:('a -> sexp) -> ('b -> sexp) -> 'a # 'b -> sexp``,SOME pair_proof)),
	(``:'a list``,(``list:('a -> sexp) -> 'a list -> sexp``,SOME list_def)),
	(``:num``,(``nat``,SOME nat_def)),
	(``:int``,(``int``,SOME int_def)),
	(``:bool``,(``bool``,SOME bool_def)),
	(``:rat``,(``rat``,SOME (translateTheory.rat_def))),
	(``:char``,(``chr``,NONE)),
	(``:string``,(``str``,NONE))]
end;

fun get_encoder t = 
	if is_vartype t then mk_var("encode_" ^ dest_vartype t,t --> sexp_type) else
	(fn me => fn se => foldl (uncurry (C (curry mk_comb))) (inst (flatten (map2 match_type ((butlast o fst o strip_fun o type_of) me) (map type_of se))) me) se)
	(	case (assoc1 (base_type t) (!encoders))
		of SOME (_,(term,def)) => term
                |  NONE                => raise_error 3 "encode" ("Unrecognised type: " ^ (type_to_string t)))
	(map get_encoder (snd (dest_type t)));

fun has_encoder_definition t = 
	not (is_vartype t) andalso exists (fn x => fst x = base_type t andalso ((Option.isSome o snd o snd) x)) (!encoders);

fun get_encoder_definition_base t = 
	if is_vartype t then raise_error 3 "encode" "Type variables have no associated encoder definition" else
	case (assoc1 (base_type t) (!encoders))
	of SOME (_,(_,SOME def)) => def
	|  SOME (_,(_,NONE))     => raise_error 3 "encode" ("Type " ^ fst (dest_type t) ^ " has no associated encoder definition")
	|  NONE                  => raise_error 3 "encode" ("Unrecognised type: " ^ (type_to_string t));

fun get_encoder_definition t = 
	PART_MATCH (rator o lhs o snd o strip_forall o hd o strip_conj) ((LIST_CONJ o map SPEC_ALL o CONJUNCTS) (get_encoder_definition_base t)) (get_encoder t);

fun add_encoder (s,t) = encoders := (base_type s,t)::(!encoders);
fun remove_encoder s = encoders := snd (pluck (fn x => fst x = base_type s) (!encoders));
fun add_encoder_def encoders def =
let	val conjuncts = CONJUNCTS def
	fun get_encoder t = 
	let	val def = LIST_CONJ (filter (curry op= (t --> sexp_type) o type_of o rator o lhs o snd o strip_forall o concl) conjuncts)
	in	((repeat rator o lhs o snd o strip_forall o hd o strip_conj o concl) def,SOME def) end;
in	
	(app (fn t => (add_encoder (base_type t,get_encoder t))) encoders ; def)
end;

(* Return a decoder for the type given *)

local
	val nat_proof = prove(``(!n. sexp_to_nat (num n) = if |= natp (num n) then Num (sexp_to_int (num n)) else 0) /\ 
				(!a. sexp_to_nat (chr a) = 0) /\ (!a. sexp_to_nat (str a) = 0) /\ (!a b. sexp_to_nat (sym a b) = 0) /\ (!a b. sexp_to_nat (cons a b) = 0)``,
			RW_TAC std_ss [sexp_to_nat_def,natp_def,integerp_def,TRUTH_REWRITES,ANDL_REWRITE])
	val bool_proof = prove(``(!n. sexp_to_bool (num n) = T) /\ (!a. sexp_to_bool (chr a) = T) /\ (!a. sexp_to_bool (str a) = T) /\ (!a b. sexp_to_bool (cons a b) = T) /\
				(!a b. sexp_to_bool (sym a b) = ~(a = "COMMON-LISP") \/ ~(b = "NIL"))``,
			RW_TAC std_ss [sexp_to_bool_def,ACL2_TRUE_def,equal_def,ite_def,EVAL ``nil = t``] THEN
			POP_ASSUM MP_TAC THEN RW_TAC std_ss [nil_def,t_def] THEN FULL_SIMP_TAC std_ss [DE_MORGAN_THM])
in
val decoders = ref [
	(``:'a # 'b``,(``sexp_to_pair:(sexp -> 'a) -> (sexp -> 'b) -> sexp -> 'a # 'b``,SOME sexp_to_pair_def)),
	(``:'a list``,(``sexp_to_list:(sexp -> 'a) -> sexp -> 'a list``,SOME sexp_to_list_def)),
	(``:num``,(``sexp_to_nat``,SOME nat_proof)),
	(``:int``,(``sexp_to_int``,SOME sexp_to_int_def)),
	(``:bool``,(``sexp_to_bool``,SOME bool_proof)),
	(``:rat``,(``sexp_to_rat``,SOME sexp_to_rat_def)),
	(``:char``,(``sexp_to_char``,SOME sexp_to_char_def)),
	(``:string``,(``sexp_to_string``,SOME sexp_to_string_def))]
end;

fun get_decoder t = 
	if is_vartype t then mk_var("decode_" ^ dest_vartype t,sexp_type --> t) else
	(fn me => fn se => foldl (uncurry (C (curry mk_comb))) (inst (flatten (map2 match_type ((butlast o fst o strip_fun o type_of) me) (map type_of se))) me) se)
	(	case (assoc1 (base_type t) (!decoders))
		of SOME (_,(term,def)) => term
                |  NONE                => raise_error 3 "decode" ("Unrecognised type: " ^ (type_to_string t)))
	(map get_decoder (snd (dest_type t)));

fun has_decoder_definition t = 
	not (is_vartype t) andalso exists (fn x => fst x = base_type t andalso ((Option.isSome o snd o snd) x)) (!decoders);

fun get_decoder_definition_base t = 
	if is_vartype t then raise_error 3 "encode" "Type variables have no associated decoder definition" else
	case (assoc1 (base_type t) (!decoders))
	of SOME (_,(_,SOME def)) => def
	|  SOME (_,(_,NONE))     => raise_error 3 "decode" ("Type " ^ (type_to_string t) ^ " has no associated decoder definition")
	|  NONE                  => raise_error 3 "decode" ("Unrecognised type: " ^ (type_to_string t));

fun get_decoder_definition t = 
	PART_MATCH (rator o lhs o snd o strip_forall o hd o strip_conj) ((LIST_CONJ o map SPEC_ALL o CONJUNCTS) (get_decoder_definition_base t)) (get_decoder t);

fun add_decoder (s,t) = decoders := (base_type s,t)::(!decoders);
fun remove_decoder s = decoders := snd (pluck (fn x => fst x = base_type s) (!decoders));
fun add_decoder_def decoders def =
let	val conjuncts = CONJUNCTS def
	fun get_decoder t = 
	let	val def = LIST_CONJ (filter (curry op= (sexp_type --> t) o type_of o rator o lhs o snd o strip_forall o concl) conjuncts)
	in	((repeat rator o lhs o snd o strip_forall o hd o strip_conj o concl) def,SOME def) end;
in	
	(app (fn t => (add_decoder (base_type t,get_decoder t))) decoders ; def)
end;



(* Return a detector for the type given *)

local 
	val nat_proof = prove(``(!a. natp (num a) = ite (integerp (num a)) (ite (not (less (num a) (nat 0))) t nil) nil) /\
				(!a. natp (chr a) = nil) /\ (!a. natp (str a) = nil) /\ (!a b. natp (sym a b) = nil) /\ (!a b. natp (cons a b) = nil)``,
			RW_TAC std_ss [natp_def,integerp_def,ite_def,ANDL_REWRITE,TRUTH_REWRITES,andl_def,not_def] THEN
			FULL_SIMP_TAC std_ss [])			
	val bool_proof = prove(``(!a. booleanp (num a) = nil) /\ (!a. booleanp (chr a) = nil) /\ (!a. booleanp (str a) = nil) /\ (!a b. booleanp (cons a b) = nil) /\
				(!a b. booleanp (sym a b) = ite (equal (sym a b) t) t (equal (sym a b) nil))``,
			RW_TAC std_ss [booleanp_def,equal_def,ite_def,nil_def,t_def])
in
val detectors = ref [
	(``:'a # 'b``,(``pairp:(sexp -> sexp) -> (sexp -> sexp) -> sexp -> sexp``,SOME pairp_def)),
	(``:'a list``,(``listp:(sexp -> sexp) -> sexp -> sexp``,SOME listp_def)),
	(``:num``,(``natp``,SOME nat_proof)),
	(``:int``,(``integerp``,SOME integerp_def)),
	(``:bool``,(``booleanp``,SOME bool_proof)),
	(``:rat``,(``rationalp``,SOME rationalp_def)),
	(``:char``,(``characterp``,SOME characterp_def)),
	(``:string``,(``stringp``,SOME stringp_def))]
end;

fun get_detector t = 
	if is_vartype t then mk_var((dest_vartype t) ^ "termp",``:sexp -> sexp``) else
	foldl (fn (x,l) => imk_comb(l,x)) (
		case (assoc1 (base_type t) (!detectors))
		of SOME (_,(term,def)) => term
                |  NONE                => raise_error 3 "detect" ("Unrecognised type: " ^ (type_to_string t)))
	(map get_detector (snd (dest_type t)));

fun has_detector_definition t = 
	not (is_vartype t) andalso exists (fn x => fst x = base_type t andalso ((Option.isSome o snd o snd) x)) (!detectors);

fun get_detector_definition_base t = 
	if is_vartype t then raise_error 3 "encode" "Type variables have no associated detector definition" else
	case (assoc1 (base_type t) (!detectors))
	of SOME (_,(_,SOME def)) => def
	|  SOME (_,(_,NONE))     => raise_error 3 "detect" ("Type " ^ fst (dest_type t) ^ " has no associated detector definition")
	|  NONE                  => raise_error 3 "detect" ("Unrecognised type: " ^ (type_to_string t));

fun get_detector_definition t = 
	PART_MATCH (rator o lhs o snd o strip_forall o hd o strip_conj) ((LIST_CONJ o map SPEC_ALL o CONJUNCTS) (get_detector_definition_base t)) (get_detector t);

fun add_detector (s,t) = detectors := (base_type s,t)::(!detectors);
fun remove_detector s = detectors := snd (pluck (fn x => fst x = base_type s) (!detectors));

fun add_detector_def detectors def =
let	val conjuncts = CONJUNCTS def
	fun get_detector t = 
	let	val def = LIST_CONJ (filter (curry op= ((fst (dest_type t)) ^ "p") o fst o dest_const o repeat rator o lhs o snd o strip_forall o concl) conjuncts)
	in	((repeat rator o lhs o snd o strip_forall o hd o strip_conj o concl) def,SOME def) end
in
	(app (fn t => (add_detector (base_type t,get_detector t))) detectors ; def)
end;


(* Generation of the encoding functions *)

fun encode_function_name t = if is_vartype t then "encode_" ^ dest_vartype t else "encode_" ^ (fst (dest_type t));
fun decode_function_name t = if is_vartype t then "decode_" ^ dest_vartype t else "decode_" ^ (fst (dest_type t));
fun detect_function_name t = if is_vartype t then (dest_vartype t) ^ "termp" else (fst (dest_type t)) ^ "p";

fun make_encode_variable t = 
	mk_var(encode_function_name t,if is_vartype t then (t --> sexp_type) else
				(foldr (fn (x,t) => (x --> sexp_type) --> t) (t --> sexp_type) (snd (dest_type t))));

fun make_decode_variable t = 
	mk_var(decode_function_name t,if is_vartype t then (sexp_type --> t) else
				(foldr (fn (x,t) => (sexp_type --> x) --> t) (sexp_type --> t) (snd (dest_type t))));

fun make_detect_variable t = 
	mk_var(detect_function_name t,if is_vartype t then ``:sexp -> sexp`` else
				(foldr (fn (x,t) => (``:sexp -> sexp``) --> t) (``:sexp -> sexp``) (snd (dest_type t))));


fun make_variable_comb f t = 
	foldl (fn (x,l) => mk_comb(l,f x)) (f t) (snd (dest_type t));

val make_encode_variable_comb = make_variable_comb make_encode_variable;
val make_decode_variable_comb = make_variable_comb make_decode_variable;
val make_detect_variable_comb = make_variable_comb make_detect_variable;


(* Encoding a function *)

(* 1) Create encodings for all the cases *)

fun create_labels x = rev (snd (foldl (fn (x,(c,l)) => (Arbnum.plus1 c,mk_comb(``nat``,mk_numeral c)::l)) (Arbnum.zero,[]) x));

fun return_encode_for_case conjunct  =
let	val args = (rev o snd o strip_comb o rhs o concl) conjunct
	fun pair_encode x l =
		mk_comb(mk_comb(``cons``,mk_comb(get_encoder (type_of x),x)),l)
in
	foldl (fn (arg,term) => pair_encode arg term) (mk_comb(get_encoder (type_of (hd args)),hd args)) (tl args)
end;

fun add_label (SOME function) label = 
	mk_comb(mk_comb(``cons: sexp -> sexp -> sexp``,label),function)
  | add_label NONE label = mk_comb(mk_comb(``cons: sexp -> sexp -> sexp``,label),``nil``);

fun encode_cases conjuncts = 
let	val functions = map (fn x => SOME (return_encode_for_case x) handle Empty => NONE) conjuncts
in
	(fn x => if not (exists isSome functions) then map (rand o rator) x else x)
		(if length conjuncts > 1 orelse functions = [NONE] then map2 add_label functions (create_labels functions) else map Option.valOf functions)
end;


(* 2) Create a definition *)

fun make_encode_definition results conjuncts ttype = 
	new_definition((encode_function_name ttype),
	mk_eq(mk_comb(make_encode_variable_comb ttype,mk_var("t",ttype)),
		mk_comb(foldl (fn (x,l) => imk_comb(l,x)) (TypeBase.case_const_of ttype) (map2 (curry list_mk_abs) (map (snd o strip_comb o rhs o concl) conjuncts) results),
			mk_var("t",ttype))));


fun prove_match match = 
	prove(match,
		DISCH_TAC THEN
		REPEAT (POP_ASSUM (fn thm => X_CHOOSE_TAC ((hd o fst o strip_exists o concl) thm) thm handle e => NO_TAC)) THEN
		POP_ASSUM STRIP_ASSUME_TAC THEN
		DISCH_TAC THEN
		(fn (assums,goal) =>
			let	val vars = (fst o strip_forall) (hd assums)
				val args = fst (strip_exists goal)
			in
				(POP_ASSUM (ASSUME_TAC o SPEC_ALL) THEN
				POP_ASSUM (fn thm => 
					SUBGOAL_THEN ((snd o dest_imp o concl o SPEC_ALL) thm) STRIP_ASSUME_TAC THEN1 
					(MATCH_MP_TAC thm THEN REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC)) THEN
				POP_ASSUM SUBST_ALL_TAC THEN
				MAP_EVERY EXISTS_TAC (List.drop(vars,length vars - length args))) end (assums,goal)) THEN
		REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC)
	handle e => raise_error 3 "prove_match" ("Couldn't prove implication theorem: " ^ (term_to_string match) ^ "\nexception: " ^ (exn_to_string e));


fun prove_function_eq_encoder proof proof_encoders = 
let	fun make_n_forall_rw n tlist res_string = 
	let	val list = map genvar tlist
		val (listl,listr) = split_after n list
		val res = list_mk_comb(mk_var(res_string,foldr (fn (x,t) => x --> t) ``:bool`` tlist),list)
	in
		(list_mk_forall(list,res),list_mk_forall ((hd listr)::(listl @ (tl listr)),res))
	end; 
	fun find_mapping [] [] = []
        |   find_mapping _  [] = raise Empty
        |   find_mapping [] _  = raise Empty
	|   find_mapping (gt::gtypes) itypes =
	let	val (poss,nposs) = partition (fn it => exists (can (match_type it)) gt) itypes
		val selects = map (fn (a,b) => (hd b, a @ (tl b) @ nposs)) (foldl (fn ((x,y),l) => split_after x poss::l) [] (enumerate 0 poss))
	in
		tryfind (fn (tin,tout) => (tin,gt)::find_mapping gtypes tout) selects
	end;

	fun var_enumerate x = foldr (fn (x,t) => (x,"a" ^ (int_to_string (length t)))::t) [] x;
	
	fun fix_const_induction n ind = 
	let	val t = (type_of o fst) (SPEC_VAR ind);
		val s = mk_var("s",(fst o dom_rng) t)
	in
		CONV_RULE (RAND_CONV (DEPTH_CONV FORALL_AND_CONV)) (BETA_RULE (SPEC(mk_abs(s,list_mk_conj(map (C (curry mk_comb) s o genvar) (for 1 n (K t))))) ind))
	end;

	fun FIND_INDUCTION_TAC (assums,goal) =
	let 	val gtypes = (map (map type_of o fst o strip_forall) o strip_conj) goal;
		fun induction_types induction = ((map (type_of o hd o fst o strip_forall) o strip_conj o snd o dest_imp o snd o strip_forall o concl) induction);
		val (mapping,induction) = 
			tryfind (fn it => ((find_mapping gtypes o induction_types) it,it)) (mapfilter (GEN_ALL o TypeBase.induction_of) (flatten gtypes))
			handle _ => 	(I ## fix_const_induction (length gtypes))
					(hd (mapfilter (fn x => (map (fn g => (x,g)) gtypes,(GEN_ALL o TypeBase.induction_of) x)) 
					(filter (fn x => all (mem x) gtypes) (mk_set (flatten gtypes)))));



		val itypes = var_enumerate (induction_types induction)
		val (ctypes,_,_) = repeat (fn (c,m,i) => ((index (can (match_type (fst (hd m)))) (snd (hd m)),assoc (fst (hd m)) i)::c,
						tl m,snd (pluck (curry op= (fst (hd m)) o fst) i))) ([],rev mapping,itypes);

		val rws = map2 (fn ct => fn gt => (snd ct,make_n_forall_rw (fst ct) gt (snd ct))) ctypes gtypes;				
		val rewrite = prove(mk_eq(list_mk_conj (map (fst o C assoc rws o snd) ctypes),list_mk_conj (map (snd o C assoc rws o snd) itypes)),
				EQ_TAC THEN REPEAT STRIP_TAC THEN RULE_ASSUM_TAC SPEC_ALL THEN FIRST_ASSUM ACCEPT_TAC)
	in
		(CONV_TAC (HO_REWR_CONV rewrite) THEN
		BETA_TAC THEN HO_MATCH_MP_TAC induction THEN
		REPEAT STRIP_TAC) (assums,goal)
	end handle e => (raise_error 3 "prove_function_eq_encoder" 
		("FIND_INDUCTION_TAC failed trying to prove:\n [" ^ 
			(foldl (fn (x,s) => (term_to_string x) ^ "," ^ s) ((term_to_string(last assums)) ^ "] |-\n " ^ 
				(term_to_string goal) ^ "\n with exception: " ^ (exn_to_string e)) (butlast assums))))
in	prove(proof,
		REPEAT GEN_TAC THEN DISCH_TAC THEN
		REWRITE_TAC [FUN_EQ_THM] THEN
		FIND_INDUCTION_TAC THEN
		ASM_REWRITE_TAC proof_encoders)
	handle e => (raise_error 3 "prove_function_eq_encoder" ("Proof of:\n " ^ (term_to_string proof) ^ "\nfailed due to: " ^ (exn_to_string e)))
end;

fun calculate_substitution term_conj term_thm_list = 
let	val thms = flatten (map (map (snd o strip_forall) o strip_conj o concl o snd) term_thm_list);
	val terms = flatten (map (map (snd o strip_forall)) term_conj);

	(* Set the types correctly *)
	val subs1 = (fn opr => map2 (fn x => fn y => inst (match_type (opr x) (opr y)) x) thms terms) (type_of o rator o lhs);

	fun replace_mutually_recursive [] term = term
          | replace_mutually_recursive (t::ts) term = 
		inst_subst (match_term ((rator o lhs) term) (find_term (can (match_term ((rator o lhs) term))) t)) term
		handle _ => replace_mutually_recursive ts term;

	(* Make the theorems mutually recursive as well *)
	val subs2 = map (replace_mutually_recursive subs1) subs1;

	(* Match each term function with left of each thm *)
	val subs3 = map (subst (flatten ((fn opr => map2 (fn x => fn y => [opr x |-> opr y]) subs2 terms) (rator o lhs)))) subs2;

	(* Form a substitution by matching terms from subs3 to the original terms *)
	val subs4 = 
		combine_subs (unzip (map (fn s3 => tryfind (match_term s3) terms) subs3));
in
	(* Substitute back in, then make the substitution list *)
	(fn (a,b,c) => a)
	(foldl (fn ((term,thms),(subs,term_list1,term_list2)) => 
		((term |-> list_mk_abs((snd o strip_comb o rator o lhs o hd) term_list1,(rator o lhs o hd) term_list2))::subs,
		List.drop(term_list1,length (CONJUNCTS thms)),List.drop(term_list2,length (CONJUNCTS thms))))
	([],terms,map (inst_subst subs4) subs2)
	term_thm_list)
end handle e => raise_error 3 "calculate_substitution" 
		("Unable to calculate a substitution to match terms:\n" ^
			foldl (fn (t,s) => (term_to_string t) ^ ",\n" ^ s) ((term_to_string (last (flatten term_conj))) ^ "\nwith theorems: " ^
			foldl (fn (t,s) => (thm_to_string t) ^ ",\n" ^ s) (((thm_to_string o snd o last) term_thm_list) ^ "\ndue to exception: " ^ (exn_to_string e))
				(map snd (butlast term_thm_list)))
				(butlast (flatten term_conj)));


fun make_function_eq_proof definition_conjs substitution =
let	val get_arg = rand o lhs o snd o strip_forall
	val get_fun = repeat rator o lhs o snd o strip_forall
	val functions = map #redex substitution
	val arg_types = map (fn f => (type_of o get_arg) (first (fn d => get_fun d = f) definition_conjs)) functions
	val constructors = map TypeBase.constructors_of arg_types
	val def_constructors = map2 (fn f => fn a => map (fn c => total (first (fn d => get_fun d = f andalso same_const c (repeat rator (get_arg d)))) definition_conjs) 
		(TypeBase.constructors_of a)) functions arg_types
	fun make_eq {redex,residue} def_list = 
		if all isSome def_list then 
			mk_eq(redex,residue)
		else	
			list_mk_conj(mapfilter (fn SOME d => 
				list_mk_forall((snd o strip_comb) (get_arg d),
					mk_eq(mk_comb(list_mk_comb(redex,(fst o strip_abs) residue),get_arg d),mk_comb((snd o strip_abs) residue,get_arg d)))
						|  NONE => raise Empty) def_list)
in
	mk_imp(list_mk_conj definition_conjs,list_mk_conj (map2 make_eq substitution def_constructors))
end;

			

fun remove_extra_function (term_thm_list,recursive_proof) =
let	val (binders,body) = (C set_diff (map fst term_thm_list) ## I) (strip_exists (concl recursive_proof))
	val term_conj = map (fn (term,_) => filter (fn c => (repeat rator o lhs o snd o strip_forall) c = term) (strip_conj body)) term_thm_list;
	val subs = calculate_substitution term_conj term_thm_list
	val conj_in = filter (fn c => not (mem ((repeat rator o lhs o snd o strip_forall) c) (map fst term_thm_list))) (strip_conj body);
	val goal = list_mk_exists(binders,subst subs (list_mk_conj conj_in));
	val proof = list_mk_forall((map fst term_thm_list) @ binders,make_function_eq_proof (flatten term_conj) subs)
in
	BETA_RULE (MP (MP (prove_match(mk_imp(concl recursive_proof,mk_imp(proof,goal)))) recursive_proof) (prove_function_eq_encoder proof (map snd term_thm_list)))
end handle e => (raise_error 3 "remove_extra_function" 
	("Failed to remove functions: " ^ 	(foldl (fn (t,s) => (term_to_string t) ^ "," ^ s) 
						(((term_to_string o fst o last) term_thm_list) ^ "\ndue to exception: " ^ (exn_to_string e))
						(map fst (butlast term_thm_list)))));

fun remove_extra_functions recursive_proof replace_list = 
let	val fvars = map fst replace_list
	val conjs = (map (snd o strip_forall) o strip_conj o snd o strip_exists o concl) recursive_proof
	val to_remove = (op_mk_set set_eq o flatten) 
			(map (return_cycles (fn x => mk_set (filter (C mem fvars) (free_varsl (map rhs (filter (fn c => free_in x (lhs c)) conjs)))))) fvars)
in
	foldl (remove_extra_function) recursive_proof (map (map (Option.valOf o C assoc1 replace_list)) to_remove)
end;

(* For a given function in a list of conjunctions, find and order all conjuncts which match the function and type constructors *)
fun order_conjuncts conjuncts function = 
let 	val constructors = (TypeBase.constructors_of o last o fst o strip_fun o type_of) function
	val ordered = map (fn c => filter (fn conj => 	(repeat rator o lhs o snd o strip_forall) conj = function 
					andalso (repeat rator o rand o lhs o snd o strip_forall) conj = c) conjuncts)
				constructors;
in	
	if all (fn [x] => true | [] => true | _ => false) ordered then (map (total hd) ordered)
	else raise_error 3 "prove_rec_fn_mutual_exists"
		("Constructor \"" ^ (term_to_string (el (index (fn x::y::ys => true | _ => false) ordered) constructors)) ^ 
			"\" occurs more than once in function " ^ (term_to_string function))
end;

(****************************************************************************)
(* Checks to see if a term is of the correct form:                          *)
(*	Term is a conjunction of equalities                                 *)
(*      All clause arguments have the same type                             *)
(*      Functions of the same name have the same type                       *)
(*      Exactly enough clauses are present                                  *)
(*      Recursive calls are only made for recursive constructors            *)
(*      Variables do not occur twice in the lhs of any clause               *)
(*	A recursive function call is called with an expression not a var    *)
(****************************************************************************)

fun check_mutual_function term =
let	val raise_err = raise_error 3 "prove_rec_fn_mutual_exists"

	fun concat [] = "" | concat [x] = x | concat (x::xs) = x ^ "," ^ (concat xs);
	val _ = if not ((is_conj o snd o strip_forall) term andalso (all (is_eq o snd o strip_forall) o strip_conj o snd o strip_forall) term) then
			raise_err "Term is not a conjunction of equalities" else ()
	val conjs = (map (snd o strip_forall) o strip_conj o snd o strip_forall) term
	
	val args = map (rand o lhs) conjs
	
	val _ = if not (length (mk_set (map type_of args)) = 1) then 
		raise_err ("Clause arguments are of different types: [" ^ (concat (map type_to_string (mk_set (map type_of args)))) ^ "]") else ();

	val fs = mk_set (map (repeat rator o lhs) conjs)
	
	val _ = if not (all is_var fs) then 
			raise_err ("The following function names are not variables: [" ^ (concat (map term_to_string (filter (not o is_var) fs))) ^ "]") else ();
		
	val names = map dest_var fs;

	val _ = if not (length names = length (mk_set (map fst names))) then 
		raise_err ("Two functions with the same name: [" ^ (concat (map (fn (x,y) => x ^ (type_to_string y)) names)) ^ "]") else ();

	val funcs = map (fn name => filter (curry op= name o dest_var o repeat rator o lhs) conjs) names
	val argsf = map (map (repeat rator o rand o lhs)) funcs
	
	val arg_type = type_of (hd args);
	val constructors = TypeBase.constructors_of arg_type;

	val _ = if exists (not o set_eq constructors) argsf then raise_err 
			("Function " ^ ((fst o dest_var o repeat rator o lhs o hd o fst) (first (not o set_eq constructors o snd) (zip funcs argsf))) ^ 
			" has the wrong number of constructors, should have: [" ^ 
			(concat (map term_to_string constructors)) ^ "] but instead has [" ^ 
			(concat (map term_to_string (first (not o set_eq constructors) argsf))) ^ "]") else ();

	val var_wrong = total (first (fn conj => not (null (set_diff (set_diff (free_vars (rhs conj)) (free_vars (lhs conj))) fs)))) conjs;

	val _ = case var_wrong
		of SOME x => raise_err ("Free variables in clause not in definition in clause: " ^ term_to_string x)
		|  NONE => ();

	val var_wrong2 = total (first (fn conj => not (length (free_vars (lhs conj)) = length(free_varsl (op:: (strip_comb (lhs conj))))))) conjs;
	
	val _ = case var_wrong2
		of SOME x => raise_err ("Variable occurs more than once in lhs of clause: " ^ term_to_string x)
		|  NONE => ();

	val _ = case (total (first (not o is_var o last o snd o strip_comb)) 
			(flatten (map (find_terms (fn x => (C mem fs o repeat rator) x andalso can rand x andalso (type_of o rand) x = arg_type) o rand) conjs)))
		of SOME x => raise_err ("Recursive function called on non-variable: " ^ term_to_string x)
		|  NONE => ();

	val rec_wrong = 
		total (first (fn conj => can (find_term (C mem fs)) (rhs conj) andalso not (mem arg_type ((map type_of o snd o strip_comb o rand o lhs) conj)))) conjs;

in
	case rec_wrong
	of	SOME x => raise_err ("Function clause: " ^ (term_to_string x) ^ " makes a recursive call, but doesn't use a recursive constructor")
	|	NONE   => ()
end;

(* Function to create a mutually recursive definition *)
(* Terms must be of the form: (f x0 C0 = A0) /\ (f y0 C1 B0) /\ ... (g x1 C0 = A1) /\ (g y1 C1 = B1) ... *)
(* Its only expected to work with :sexp, so anything else is likely to break it. *)
fun prove_rec_fn_mutual_exists term = 
let	val _ = check_mutual_function term

	fun reverse_map tmap = map (map (map (fn {redex,residue} => residue |-> redex))) tmap
	fun opt_subst x NONE = NONE | opt_subst x (SOME y) = SOME (subst x y);
	
	val conjuncts = (map (snd o strip_forall) o strip_conj) term
	val functions = mk_set (map (repeat rator o lhs) conjuncts)
	val bodies = transpose (map (order_conjuncts conjuncts) functions)

	val constructors = map (map (Option.map (free_vars_lr o rand o lhs))) bodies;
	val constructors_map = 
		transpose ((map (map (fn SOME x => x | NONE => [])))
		(map (map2 (fn y => Option.map (map2 (C (curry op|->)) y)) (map (map (genvar o type_of) o valOf o first isSome) constructors)) (transpose constructors)));

	val args = map (map (fn SOME x => (butlast o snd o strip_comb o lhs) x | NONE => [])) bodies;

	(* Forms a map of argument function calls, if f x = ... g x ... and g y = ... then (x,y) is in the map *)
	(* then finds any calls for which there is only one link in the map x -> y and replaces x by y *)
	fun modify_map args_map =
	let 	val conjs = mapfilter valOf (flatten ((map2 (map2 opt_subst) args_map) bodies))
		fun next_args conjs arg = 
		let	val terms = flatten (map (find_terms (fn term => exists (curry op= (repeat rator term)) functions 
						andalso mem arg ((snd o strip_comb) term)) o rhs) conjs)
		in
			map fst (flatten (mapfilter (fn t => filter (fn x => snd x = arg) (zip (snd (first (fn (f,_) => f = repeat rator t) 
				(map (strip_comb o lhs) conjs))) ((snd o strip_comb) t))) terms))
		end
		fun find_subs [] links = []
		  | find_subs (v::vs)  links = 
		let	val (v_calls,links') = (snd o hd ## I) (partition (fn (a,c) => a = v) links)
			val (callers,others) = partition (fn (a,c) => mem v c) links'
		in
			if length callers = 1  	then (v |-> fst (hd callers))::find_subs vs ((fst (hd callers),snd (hd callers) @ v_calls)::others)
						else find_subs vs links
		end;

		fun replace_all_args (conjs,args_map) = 
		let	val args_new = (mk_set o map #residue  o flatten o flatten) args_map
			val subs = find_subs args_new (map (fn arg => (pair arg o filter (not o curry op= arg) o next_args conjs) arg) args_new)
		in
			if null subs then raise Empty else
			(map (subst subs) conjs,map (map (map (fn {redex,residue} => redex |-> subst subs residue))) args_map)
		end	
	in
		snd (repeat replace_all_args (conjs,args_map))
	end;

	val args_map = 
		modify_map (map(map2 (fn g => fn a => map2 (curry op|->) a (List.take(g,length a)))
			(map (map (genvar o type_of)) (map (fn l => if exists (not o null) l then first (not o null) l else []) (transpose args)))) args);
	
	val args_new = (mk_set o map #residue  o flatten o flatten) args_map;

	val bodies' =   (map2 (map2 opt_subst) constructors_map) ((map2 (map2 opt_subst) args_map) bodies);
			
	val arg_type = 
		case (mk_set (mapfilter valOf (flatten (map (map (Option.map (type_of o rand o lhs))) bodies'))))
		of []      => raise_error 3 "prove_rec_fn_mutual_exists" "Couldn't find argument type, incorrect form"
		|  [x]     => x 
                |  (x::xs) => raise_error 3 "prove_rec_fn_mutual_exists" "Functions mutually recursive on different argument types";
	
	val result_type = sumSyntax.list_mk_sum(map (type_of o rhs o valOf o first isSome) (transpose bodies'))
	val vector_type = sumSyntax.list_mk_sum(map (K ``:one``) functions)
	val function = 
		list_mk_comb(genvar (foldr op--> (vector_type --> arg_type --> result_type) (map type_of args_new)),args_new);
	val vector_var = genvar vector_type;
	
	fun mk_select 0 term outt = if type_of term = outt then term else sumSyntax.mk_inl(term,snd (sumSyntax.dest_sum outt))
	  | mk_select n term outt = 
		let	val (a,b) = sumSyntax.dest_sum outt in sumSyntax.mk_inr(mk_select (n - 1) term b,a) end;
		
	fun inputn term n = mk_select n term result_type;
	fun vector n = mk_select n ``():one`` vector_type;
	
	fun outputn term 0 = (sumSyntax.mk_outl term handle e => term)
	  | outputn term n = outputn (sumSyntax.mk_outr term) (n - 1);

	(* Forms a substitution from a function to the generic function *)
	(* Eg: f x |-> (\cons.OUTL (F (INL ()) cons x y z)) *)
	fun map_function conj =
	let	val (func,args) = (strip_comb o rator o lhs) conj
		val const = mk_var("cons",(type_of o rand o lhs ) conj)
		val res_type = (type_of o rhs) conj
		val n = index (curry op= func) functions
	in
		func |-> list_mk_abs(args,mk_abs(const,outputn (mk_comb(mk_comb(function,vector n),const)) n))
	end;

	(* Converts a clause to use the generic function *)
	fun wrap_function subs conj =
	let	val n = index (curry op= ((repeat rator o lhs) conj)) functions
	in
		mk_eq(mk_comb(mk_comb(function,vector n),(rand o lhs) conj),inputn (subst subs (rhs conj)) n)
	end;

	fun input_to_is term var =
	let	val (a,b) = dest_comb term
	in	if same_const a sumSyntax.inl_tm then sumSyntax.mk_isl var	
		else mk_conj(sumSyntax.mk_isr var,input_to_is b (sumSyntax.mk_outr var))
	end handle _ => sumSyntax.mk_isr var
	

	(* Combines a list of function clauses into an if statement *)
	fun combine_clause_list list = 
	let	val (function,args_list) = (strip_comb o rator o rator o lhs o hd) list
		val constructor = (rand o lhs o hd) list
	in
		mk_eq(mk_comb(mk_comb(list_mk_comb(function,args_list),vector_var),constructor),
			foldr (fn (conj,term) => mk_cond(input_to_is ((rand o rator o lhs) conj) vector_var,rhs conj,term)) (rhs (last list)) (butlast list))
	end;
	
	val constructor_consts = TypeBase.constructors_of arg_type
	
	fun fill_clause_list list =
	let	val constructor = (rand o lhs o valOf o first isSome) list
		val list' = map (fn (n,_) => mk_eq(mk_comb(mk_comb(function,vector n),constructor),inputn (mk_arb (el (n+1) (sumSyntax.strip_sum result_type))) n))
					(enumerate 0 list)
	in
		map2  (fn SOME x => (fn y => x) | NONE => (fn y => y)) list list'
	end;
	
	val rec_function = prove_rec_fn_exists (TypeBase.axiom_of arg_type) 
		(list_mk_conj (map (combine_clause_list o fill_clause_list)
				((map (map (Option.map (wrap_function (map (map_function o valOf o first isSome) (transpose bodies')))))) bodies')));

	(*
	(subst [vector_var |-> mk_var("v",type_of vector_var),repeat rator function |-> mk_var("F",type_of (repeat rator function))] o 
		subst (flatten (flatten (reverse_map args_map))) o subst (flatten (flatten (reverse_map constructors_map))) o rhs o concl o DEPTH_CONV BETA_CONV) 
				((list_mk_conj (map (combine_clause_list o fill_clause_list)
				((map (map (Option.map (wrap_function (map (map_function o valOf o first isSome) (transpose bodies')))))) bodies'))));
	*)

	val _ = if not (null (hyp rec_function)) then raise_error 3 "prove_rec_fn_mutual_exists" "Recursive function returned has an hypothesis!" else ();

	fun wrap_thm n thm = 
	let	val rewr_thm = (fn x => DEPTH_CONV (REWR_CONV (GSYM combinTheory.o_THM)) x handle UNCHANGED => REFL x) (outputn (mk_var("a",result_type)) n)
	in
		REWRITE_RULE [OUTL,OUTR] (ONCE_REWRITE_RULE [GSYM rewr_thm] (AP_TERM ((rator o rhs o concl) rewr_thm) thm))
	end handle e => thm;
			
	val constructors_map_inverse = (transpose o reverse_map) constructors_map;
	
	val conjuncts1 = (	(map2 (map2 (fn c => GENL (map #residue c) o INST c)) constructors_map_inverse)
				(map (fn x => map (wrap_thm x o PURE_REWRITE_RULE [COND_CLAUSES,AND_CLAUSES,ISL,ISR,OUTR,OUTL] o SPEC (vector x) o GEN vector_var o SPEC_ALL) 
				(CONJUNCTS (ASSUME ((snd o strip_exists o concl) rec_function)))) (map fst (enumerate 0 (sumSyntax.strip_sum result_type)))));

	fun get_args_list term = 
	let val (f,x) = strip_comb term in if length x = 1 then get_args_list (hd x) else x end;

	val match_terms = 	(map (fn x => subst ((fn y => map2 (curry op|->) y (foldr (fn (x,l) => variant l (mk_var("x",x))::l) [] (map type_of y))) 
					(get_args_list x)) x))
				(map (lhs o snd o strip_forall o concl o hd) conjuncts1);


	(* Converts a term that matches one of match_terms to a lambda abstraction *)
	fun FUNCTION_CONV test_term = 
	let	val term' = first (can (C match_term test_term)) match_terms
		val const = filter (fn x => not (type_of x = vector_type)) (get_args_list test_term)
		val consv = filter (fn x => not (type_of x = vector_type)) (get_args_list term')
	in
		GSYM (DEPTH_CONV BETA_CONV (list_mk_comb(list_mk_abs(consv,subst (map2 (curry op|->) const consv) test_term),const)))
	end;

	val args_map_inverse = (transpose o reverse_map) args_map;
	
	val conjuncts2 = LIST_CONJ (map2 (fn x => (LIST_CONJ o map2 (fn x => GEN_ALL o GENL (map #residue x) o INST x o CONV_RULE (DEPTH_CONV (FUNCTION_CONV))) x))
				args_map_inverse conjuncts1);

	val new_functions = map (repeat rator o lhs o snd o strip_forall o concl o CONV_RULE (DEPTH_CONV (FUNCTION_CONV)) o hd) conjuncts1;

	fun exists_it functions thm cthm = 
	let 	fun setify [] = [] | setify (x::xs) = x::setify (filter (not o curry op= x) xs);
		fun rrator term = if is_comb term andalso (not o is_arb o rand) term then rrator (rator term) else term
		val new_functions = setify ((map (rrator o lhs o snd o strip_forall) o strip_conj o concl) thm)
		val functions' = map2 (fn x => fn y => mk_var((fst o dest_var) x,type_of y)) functions new_functions
		val new_term = mk_pexists(list_mk_pair functions',subst (map2 (curry op|->) new_functions functions') (concl thm))
	in
		CHOOSE_L ((fst o strip_exists o concl) cthm,cthm)
			(foldr (fn ((newf,fvar),thm) => EXISTS (Psyntax.mk_exists(fvar,subst [newf |-> fvar] (concl thm)),newf) thm)
				thm (zip new_functions functions'))
	end;

	val thm1 = BETA_RULE (exists_it functions conjuncts2 rec_function);

	fun remove_genvar_gen thm = 
		(fn (x,y) => GENL ((filter (not o is_genvar) o rev) x) y) (repeat (fn (l,thm) => (C (curry op::) l ## I) (SPEC_VAR thm)) ([],thm));
	
	fun make_param_term fc = 
	let 	val (binders,f) = (I ## rator o lhs) (strip_forall fc)
	in	list_mk_forall([],mk_eq(f,subst (map (fn x => x |-> mk_arb(type_of x)) (filter is_genvar (free_vars f))) (f))) end;

	val functions_conj = map (fn f => make_param_term (first (fn x => (fst o dest_var o repeat rator o lhs o snd o strip_forall) x = (fst o dest_var) f)
				(map fst (filter (isSome o snd) (zip ((strip_conj o snd o strip_exists o concl) thm1) (flatten (transpose bodies'))))))) functions;



	fun DISJ_ALL_CASES_TAC thm stack = 
		DISJ_CASES_THENL [fn th => (TRY (DISJ_ALL_CASES_TAC th) THEN STRIP_ASSUME_TAC th),STRIP_ASSUME_TAC] thm stack;

	fun matches_goal goal =
		exists (fn fc => (repeat rator o lhs) goal = (repeat rator o lhs) fc) functions_conj;

	val equiv_proof = UNDISCH (prove(mk_imp((snd o strip_exists o concl) thm1,list_mk_conj functions_conj),	
		STRIP_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN
		CONV_TAC (TOP_DEPTH_CONV (LEFT_AND_FORALL_CONV ORELSEC RIGHT_AND_FORALL_CONV)) THEN
		(fn (assums,goal) => 
			let 	val v = (list_mk_plus (map (curry mk_comb ``sexp_size``) ((fst o strip_forall) goal)))
			in
				REPEAT GEN_TAC THEN 
				MAP_EVERY (fn x => SPEC_TAC (x,x)) 
					(flatten ((map (snd o strip_comb o rator o lhs) o strip_conj o snd o strip_forall) goal)) THEN
				CONV_TAC (REDEPTH_CONV FORALL_AND_CONV) THEN
				STRIP_ASSUME_TAC (EXISTS (Psyntax.mk_exists(``v:num``,mk_eq(``v:num``,v)),v) (REFL v)) THEN
				POP_ASSUM MP_TAC THEN 
				MAP_EVERY (fn x => SPEC_TAC (x,x)) (rev ((fst o strip_forall) goal)) THEN
				SPEC_TAC (``v:num``,``v:num``) THEN
				HO_MATCH_MP_TAC arithmeticTheory.COMPLETE_INDUCTION THEN
				REPEAT STRIP_TAC 
			end (assums,goal)) THEN
		FIRST_ASSUM SUBST_ALL_TAC THEN
		(fn (assums,goal) => (DISJ_ALL_CASES_TAC (SPEC ((rand o lhs) goal) ((TypeBase.nchotomy_of  o type_of o rand o lhs) goal))) (assums,goal)) THEN
		POP_ASSUM SUBST_ALL_TAC THEN
		ASM_REWRITE_TAC [] THEN
		REPEAT (REFL_TAC ORELSE (fn (assums,goal) => (if not (matches_goal goal) then MK_COMB_TAC else NO_TAC) (assums,goal))) THEN
		(fn (assums,goal) => 
		PAT_ASSUM ``!v:num.P`` (fn thm => 
		let	val (break,nobreak) = (pluck is_comb o map rand o strip_plus o snd o dest_less o fst o dest_imp o snd o strip_forall o concl) thm;
			val new_sum = list_mk_plus (map (curry mk_comb ``sexp_size``) (List.take((snd o strip_comb) break @ nobreak,length nobreak + 1)));
		in	
			(STRIP_ASSUME_TAC o DECIDE_ANTE o REWRITE_RULE [snd (TypeBase.size_of sexp_type)] o 
			SPEC new_sum)
		end thm) (assums,goal)) THEN
		(fn (assums,goal) => 
		let	val (vars,body) = (strip_forall o hd) assums
			val match = (rand o lhs o snd o strip_forall) (first (curry op= ((repeat rator o lhs) goal) o repeat rator o lhs o snd o strip_forall) 
				((strip_conj o snd o dest_imp) body));
			val terms = (map rand o strip_plus o fst o dest_eq o hd o fst o strip_imp o snd o strip_forall o hd) assums
			fun same x = (repeat rator o lhs o snd o strip_forall o concl) x = (repeat rator o lhs) goal;
		in
			(fn x => (CONV_TAC (RAND_CONV (REWR_CONV x) THENC LAND_CONV (REWR_CONV x)) THEN REFL_TAC)) 
				(first same 
					(CONJUNCTS (REDUCE_RULE (CONV_RULE (LAND_CONV (AC_CONV (ADD_ASSOC,ADD_COMM))) 
						(SPECL (map (C assoc (zip (op:: (pluck (curry op= match) vars)) (op:: (pluck (curry op= ((rand o lhs) goal)) terms)))) vars) 
						(ASSUME (hd assums))))))) (assums,goal)
		end)));

	val functions_conj_correct = mk_set (map (rator o lhs o valOf) (flatten bodies));

	fun FARB_CONV term =
	let 	val f = repeat rator term
		val function_conj = first (curry op= (fst (dest_var f)) o fst o dest_var o repeat rator) functions_conj_correct;
		val args = (snd o strip_comb) term;
		val args_correct = (snd o strip_comb) function_conj;
		val vars = foldr (fn (x,t) => if is_arb x then x :: t else variant (filter is_var t) (mk_var("x",type_of x)) :: t) [] args
		val vars_correct = map (C assoc (filter (not o is_arb o snd) (zip args vars))) args_correct;
	in
		if 	not (length args_correct = length (filter (not o is_arb) args)) orelse 
			not (op_mem (curry (op= o ((fst o dest_var) ## (fst o dest_var)))) f functions) then NO_CONV term else
		GSYM (DEPTH_CONV BETA_CONV (list_mk_comb(list_mk_abs(vars_correct,list_mk_comb(f,vars)),args_correct)))
	end;

in
	exists_it functions (CONV_RULE (DEPTH_CONV FARB_CONV) (ONCE_REWRITE_RULE (CONJUNCTS equiv_proof) 
		(LIST_CONJ  (map fst (filter (isSome o snd) 
			(zip (map remove_genvar_gen (CONJUNCTS (ASSUME ((snd o strip_exists o concl) thm1)))) (flatten (transpose bodies')))))))) thm1

end;

(* val function = (list_mk_conj functions);
   val types = main_encoders;
   val (has_definition,get_definition,get_term) =  (has_encoder_definition,get_encoder_definition_base,get_encoder);
 
   val (has_definition,get_definition,get_term) = (has_decoder_definition,get_decoder_definition_revert,get_decoder);
 
   val (has_definition,get_definition,get_term) = (has_detector_definition,get_detector_definition_revert,get_detector);
 *)

(* Converts a function from case form to clause form *)
fun case_to_clause thm =
	(if (TypeBase.is_case o rhs o concl o SPEC_ALL) thm then
		let	val var = (rand o lhs o concl o SPEC_ALL) thm
		in
			LIST_CONJ 
				(map (fn x => (BETA_RULE o REWRITE_RULE [TypeBase.case_def_of (type_of var)] o SPEC ((rhs o snd o strip_exists) x) o GEN var o SPEC_ALL) thm) 
					((strip_disj o concl o ISPEC var o TypeBase.nchotomy_of o type_of) var))
		end
	else thm) handle e => thm;		

(* Makes a recursive definition by adding extra functions necessary to prove recursion, then removing them afterwards *)
fun make_recursive_definition function (has_definition,get_definition,get_term) (types,extra_types,sub_types) = 
let	val _ = tprint_trace 1 "Defining recursive function: \n"
	val _ = tprint_trace 3 ((term_to_string function) ^ "\n");

	val extra_functions_base = map (case_to_clause o get_definition) extra_types;
	val extra_functions = map2 (PART_MATCH (rator o lhs o hd o strip_conj)) 
				(map (LIST_CONJ o map SPEC_ALL o CONJUNCTS) extra_functions_base) (map get_term extra_types);

	val _ = tprint_trace 1 ("Additional type functions required for recursion proof: [" ^
			(foldr (fn (x,s) => ((type_to_string x) ^ "," ^ s)) (type_to_string (last extra_types) ^ "]\n") (butlast extra_types)
			handle _ => "]\n"));

	val full_function = list_mk_conj (flatten (map strip_conj (function::(map concl extra_functions))))
	
	fun make_functions_variable (fvars,vars,full_function) [] = (vars,full_function)
	|   make_functions_variable (fvars,vars,full_function) (function::functions_list) =
	let	val left = (rator o lhs o hd o strip_conj) (function)
		val args = set_diff (free_vars left) fvars
		val var = variant vars (mk_var("x",foldr (fn (x,t) => (type_of x) --> t) (type_of left) args))
		val subs = subst [left |-> list_mk_comb(var,args)]
	in
		make_functions_variable (var::fvars,var::vars,subs full_function) (map subs functions_list)
	end

	val function_vars = mk_set (map (repeat rator o lhs o snd o strip_forall) (strip_conj function))
	val (vars,full_function') = make_functions_variable (map (repeat rator) function_vars,free_vars full_function,full_function) (map concl extra_functions);
	val recursive_proof = 
		if (fst o dom_rng o type_of o rator o lhs o hd o strip_conj) full_function' = sexp_type then
			prove_rec_fn_mutual_exists full_function' else
			prove_rec_fn_exists (TypeBase.axiom_of (hd types)) full_function'
	val replace_list = zip (rev (List.take(vars,length extra_functions_base))) extra_functions_base

in
	remove_extra_functions recursive_proof replace_list
end;

	

(* Note: As the naming is consistent, we don't need to find the terms... eg. making the case & finding the definition both use the same names *)
fun make_encode_recursive_definition encodings (main_encoders,extra_types,sub_types) = 
let	val function_vars = map make_encode_variable_comb main_encoders	
	val lhs_list = map2 (fn fv => map (curry mk_comb fv)) function_vars (map ((map (last o snd o strip_comb o lhs o concl) o get_conjuncts)) main_encoders)
	val functions = flatten (map2 (map2 (curry mk_eq)) lhs_list encodings);
	val names = map encode_function_name main_encoders
in
	new_specification((hd names) ^ "_def",names,
		make_recursive_definition (list_mk_conj functions) (has_encoder_definition,get_encoder_definition_base,get_encoder) (main_encoders,extra_types,sub_types))
end;
	

fun encode_of x = 
let 	val (main_encoders,extra_types,sub_types) = get_type_chain (base_type x)
	val new_encoders = map make_encode_variable main_encoders
	val _ = app add_encoder (map (fn (var,t) => (t,(var,NONE))) (zip new_encoders main_encoders))
	val encodings = map (encode_cases o get_conjuncts) main_encoders
	val encoder_def = 
		(if length new_encoders = 1 andalso not (exists (free_in (hd new_encoders)) (hd encodings)) then
			make_encode_definition (hd encodings) (get_conjuncts x) (base_type x)
		else
			make_encode_recursive_definition encodings (main_encoders,extra_types,sub_types)) handle e => 
		(app remove_encoder main_encoders ; raise e)
in
	(app remove_encoder main_encoders ; add_encoder_def main_encoders encoder_def)
end;


(* Decoding a function *)



(* Create a decode function for a case construct *)
fun return_decode_for_case conjunct  =
let	val args = (snd o strip_comb o rhs o concl) conjunct
	val constructor = (last o snd o strip_comb o lhs o concl) conjunct
	fun split_terms [] = []
	  | split_terms [x] = [x]
          | split_terms (x::xs) = mk_comb(``car``,x)::split_terms (map (curry mk_comb ``cdr``) xs);
in
	(subst 	(map2 (curry op|->) args (map2 (curry mk_comb) (map (get_decoder o type_of) args) (split_terms (map (fn x => mk_var("x",sexp_type)) args))))
		constructor)
end;

fun add_decode_labels var cases labels = 
	map2 (fn c => fn l => imk_comb(mk_comb(``COND:bool -> 'a -> 'a -> 'a``,mk_eq(var,l)),c)) (map (subst [``x:sexp`` |-> ``cdr x:sexp``]) cases) labels;

fun decode_cases conjuncts = 
let	val cases = map return_decode_for_case conjuncts
	val labels = create_labels cases
in
	if length labels = 1 then cases else 
		(if exists (free_in (mk_var("x",sexp_type))) cases then add_decode_labels ``car x`` cases labels else add_decode_labels ``x:sexp`` cases labels)
end;


(* Finds the value to be cased using 'find_var' in the thm, instantiates this to the same as the value in the nchotomy thm then performs the casing *)
(* -- should work on both conjunction form (where 'find_var' locates the case value) or simple function form *)
fun split_thm find_var nchotomy thm = 
let	val nchots = (strip_disj o concl) nchotomy
	val var = (lhs o snd o strip_exists o hd) nchots
in
	if is_conj (concl thm) orelse (length nchots = 1 andalso can (match_term ((rhs o snd o strip_exists o hd) nchots)) ((find_var o concl o SPEC_ALL) thm))
	then 	map ((fn x => UNDISCH (DISCH (mk_eq(var,(find_var o concl) x)) x)) o SPEC_ALL) (CONJUNCTS thm)
	else  	let	val thm' = INST_TY_TERM (match_term ((find_var o concl) thm) var) thm
		in	map (fn t => (PURE_ONCE_REWRITE_RULE [ASSUME t] o UNDISCH o DISCH t) thm')
				(map ((fn n => subst (map (fn x => x |-> variant ((free_vars o concl) thm') x) (free_vars (rhs n))) n) o snd o strip_exists) nchots)
		end
end;


(* Given a list of theorems split by split_thm, choose_thms will convert: [t = C a b] |- P to [?a b. t = C a b] |- P *)
fun choose_thms nchotomy thms = 
let 	val hyps = map2 (fn nchot => fn thm => first (can (match_term ((snd o strip_exists) nchot))) (hyp thm)) ((strip_disj o concl) nchotomy) thms
	val vars = map2 (fn h => total (fn nchot => map (inst_subst (match_term ((snd o strip_exists) nchot) h)) ((fst o strip_exists) nchot)))
			hyps ((strip_disj o concl) nchotomy);
in
	map2 (fn (SOME v,x) => (fn y => CHOOSE_L (v,x) y) | (NONE,_) => (fn y => y))
		(zip vars (map ASSUME ((strip_disj o concl) nchotomy)))
		thms
end;

fun join_thms nchotomy thms =  DISJ_CASESL nchotomy (choose_thms nchotomy thms);

(* Removes the first equality in the hypothesis by instantiating the lhs to the rhs *)
fun remove_hyp_eq thm = let val h = first is_eq (hyp thm) in PROVE_HYP ((REFL o rhs) h) (INST [lhs h |-> rhs h] thm) end handle e => thm

(* Converts a function operating on a single :sexp variable to work on clauses instead *)
local
	val simp_prove = CONV_RULE bool_EQ_CONV o REWRITE_CONV [car_def,cdr_def,nil_def,sexp_to_list_def]
	val nat_prove = fn x => prove(x,RW_TAC std_ss [nat_def,int_def,cpx_def,sexpTheory.rat_def,nil_def])
	val eq_prove = fn x => prove(x,RW_TAC std_ss [equal_def,nil_def,t_def,prove(``bool a = if a then t else nil``,RW_TAC std_ss [bool_def])]);
	val substs = [	car_def,cdr_def,nat_prove ``(cons a b = nat c) = F``,
			nat_prove ``(sym a b = nat x) = F``,nat_prove ``(str s = nat x) = F``,nat_prove ``(chr c = nat x) = F``,
			LIST_CONJ (map (remove_hyp_eq o RIGHT_CONV_RULE (REWRITE_CONV [nil_def,sexp_11,sexp_distinct,equal_def] THENC REWRITE_CONV [GSYM nil_def])) 
					(split_thm (rand o lhs) (SPEC_ALL (TypeBase.nchotomy_of sexp_type)) (REFL ``equal nil x``))),
			LIST_CONJ (map (remove_hyp_eq o RIGHT_CONV_RULE (REWRITE_CONV [nil_def,sexp_11,sexp_distinct,equal_def] THENC REWRITE_CONV [GSYM nil_def])) 
					(split_thm (rand o rator o lhs) (SPEC_ALL (TypeBase.nchotomy_of sexp_type)) (REFL ``equal x nil``))),
			COND_CLAUSES,IF_THMS,prove(``(ite x a a = a)``,RW_TAC std_ss [nil_def,t_def,ite_def])] @ (CONJUNCTS pairp_def)
in
fun convert_sexp_to_clause nil_rewrites function_vars function = 
let 	val terms = map concl (split_thm (rand o lhs) (SPEC_ALL (TypeBase.nchotomy_of sexp_type)) (ASSUME function))
	val rewrs = map ((fn x => (REWRITE_CONV (nil_def::(substs @ nil_rewrites)) THENC REWRITE_CONV [GSYM nil_def]) x handle _ => REFL x) o rhs) terms
in
	(map (GENL function_vars o DISCH_ALL) rewrs,map2 (fn x => rhs o concl o ONCE_REWRITE_CONV [x]) rewrs terms)
	
end
end;

fun strip_cond term = 
	let 	val (p,a,b) = dest_cond term
		val (bs,last) = strip_cond b 
	in	((p,a)::bs,last) end handle e => ([],term)

fun dest_acl2_and term = 
	let	val (a,b,c) = dest_acl2_cond term
	in	if not (same_const c ``nil``) then raise Empty else (a,b) end;

local 
fun strip_acl2_or' term = 
	let	val (a,tt,b) = dest_acl2_cond term
		val (aos,nilt) = strip_acl2_or' a
	in
		if not (same_const tt ``t``) then ([dest_acl2_and term],``nil``) else ((dest_acl2_and b)::aos,nilt)
	end 	handle e =>  ([dest_acl2_and term],``nil``)
in
fun strip_acl2_or term = (rev ## I) (strip_acl2_or' term) handle e => ([],term)
end;


fun remove_car_cdr sub_functions get_definition function_vars L =
let	val split_name = ref "strip"
	
	val _ = tprint_trace 1 "Splitting functions: ";

	val nil_rewrites = map (map SPEC_ALL o CONJUNCTS) sub_functions;

	fun next_split vars sterm = 
	let	val x = list_mk_comb(mk_var(!split_name,list_mk_fun(map type_of vars,sexp_type --> (type_of sterm))),vars)
	in	(split_name := prime (!split_name) ; x) end;
	
	val findterm = (fn x => (can (match_term ``car x``) x orelse can (match_term ``cdr x``) x) andalso (is_var o repeat rand) x)
	val count_terms = length o find_terms (fn x => same_const ``car`` x orelse same_const ``cdr`` x);

	fun make_rewrites nil_rewrites L = flatten ((map (fn (x,y) => 
		(ASSUME (list_mk_forall(free_varsl (snd (strip_comb (lhs x))),x)))) L)::nil_rewrites);

	fun pairit (x::xs) [] = (x::xs)
                  | pairit (x::xs) (y::ys) = (mk_fst ## fst o dest_pair) x :: (pairit (map (mk_snd ## snd o dest_pair) (x::xs)) ys)
		  | pairit _ _ = [];

	(* Create split functions, recursive calls may only share a split function if their split term size is the same *)
	fun create_new (sterm,L)  = 
	let	val terms = mk_set (find_terms findterm sterm)
		val fcalls = 
			filter (not o null o find_terms (C mem function_vars))
				(sort (fn a => fn b => (count_terms (rand a) > count_terms (rand b))) 
					(find_terms (fn x => not (mem x terms) andalso can rand x andalso mem (rand x) terms) sterm))
	in		
		if null fcalls then raise Empty else create_new_separate L fcalls
	end
	and create_new_separate L fcalls = 
	let	val partitioned = mk_set (map (fn m => mk_set (filter (curry op= (count_terms m) o count_terms) fcalls)) fcalls)
		val new_funs = map (fn fc => mk_eq(mk_comb(next_split (set_diff (free_vars fc) ((repeat rand fc)::function_vars)) fc,repeat rand fc),fc)) 
					(map list_mk_pair partitioned)
		val converted = map (fn nf => convert_sexp_to_clause (make_rewrites nil_rewrites L) function_vars nf) new_funs
		val _ = tprint_trace 1 (foldl op^ "" (for 1 (length fcalls) (K ".")));
		val subs = map (map (uncurry (C (curry op|->)))) (map2 (fn nf => (fn [] => [dest_eq nf] | (x::xs) => pairit [dest_eq nf] xs)) new_funs partitioned);
	in
		foldl (fn ((_,x),L) => create_new ((rhs o first (same_const ``cons`` o repeat rator o rand o lhs)) x,L) handle e => L)
			(map (subst (flatten subs) ## I) ((flatten (map (uncurry (C zip)) converted)) @  L)) converted
	end

	fun create_new_all L = 
		create_new_all (tryfind (fn (x,y) => (create_new (x,L))) L) handle e => L

	val res = create_new_all L
in
	(tprint_trace 1 "\n" ; res)
end;

fun remove_pairp sub_functions get_definition function_vars L =
let	fun rewrite x = (rhs o concl o PURE_REWRITE_CONV [PAIRP_THM]) x handle e => x
in
	(remove_car_cdr sub_functions (PURE_REWRITE_RULE [PAIRP_THM] o get_definition) function_vars (map (rewrite ## PURE_REWRITE_RULE [PAIRP_THM]) L))
end;

(* val rewrites =  (map2 (curry op::) rewrs functions_rewrs) *)

(* Like mapfilter except retains a list of those that fail *)
fun mappartition f [] = ([],[])
  | mappartition f (x::xs) = 
let	val (l,r) = mappartition f xs in (f x::l,r) handle e => (l,x::r) end;


(* Combines split functions back together and throws them away *)
fun remove_splits function_vars [] thm = thm
  | remove_splits function_vars L thm = 
let	val _ = tprint_trace 1 "Removing additional functions: 0%"
	val conjuncts_unspec = CONJUNCTS (SPEC_ALL (ASSUME ((snd o strip_exists o concl) thm)));

	
	val matched_list = 
		snd (repeat (fn (x,l) => (List.drop(x,5),List.take(x,5)::l)) 
			(map (fn c => (SPEC_ALL c,snd (first (fn (x,y) => curry (op= o (lhs ## lhs)) x ((concl o SPEC_ALL) c)) L))) conjuncts_unspec,[]));

	fun fix_hyps rewrite = 
	let	fun fix_single x = 
		let	val (a,b) = strip_forall x
		in	GENL a (tryfind (C (PART_MATCH lhs) (lhs b)) conjuncts_unspec) end
	in
		
		if (is_imp o concl) rewrite then 
			foldl (uncurry PROVE_HYP) (UNDISCH_ALL rewrite) (map fix_single ((fst o strip_imp o concl) rewrite))
		else rewrite
	end;

	val match5 = map (fn (c,r) => CONV_RULE (RAND_CONV (GSYM o fix_hyps o PART_MATCH (rhs o snd o strip_imp) r)) c);

 	fun fix_theorems total _ [] = []
	  | fix_theorems total n to_do =
	let	val (joined,to_do) =
			mappartition (	GEN_ALL o join_thms (SPEC_ALL (TypeBase.nchotomy_of sexp_type)) o 
					map (fn x => PURE_REWRITE_RULE (mapfilter (SYM o ASSUME) (hyp x)) x) o 
					split_thm (rand o lhs) (SPEC_ALL (TypeBase.nchotomy_of sexp_type)) o LIST_CONJ o match5) to_do
		val _ = if null joined then (tprint_trace 1 "\n" ; raise_error 3 "remove_splits" "Couldn't remove split theorems") else ()
		val _ = tprint_trace 1 ("-" ^ int_to_string (((n + length joined) * 100) div total) ^ "%")
		val rewrite = PURE_REWRITE_RULE (FST::SND::filter (not o C mem function_vars o repeat rator o lhs o snd o strip_forall o concl) joined)
	in	
		joined @ fix_theorems total (n + length joined) (map (map (rewrite ## rewrite)) to_do)
	end;
	
	val result = 
		CHOOSE_L ((fst o strip_exists o concl) thm,thm)
			((fn thm => foldr (fn (v,thm) => EXISTS (Psyntax.mk_exists(v,concl thm),v) thm) thm function_vars)
				(LIST_CONJ (filter (C mem function_vars o repeat rator o lhs o snd o strip_forall o concl) 
					(fix_theorems (length matched_list) 0 matched_list))));
in
	(tprint_trace 1 "\n" ; result)
end;

fun revert_definition needs_split strip_top thm = 
let	val function_consts = (map (repeat rator o lhs o snd o strip_forall) o strip_conj o concl) thm
	val function_vars = map (mk_var o dest_const) function_consts;

	fun convert_to_clause thms = 
		map (LIST_CONJ o map (fn (x,y) => ONCE_REWRITE_RULE [x] y) o map (SPECL function_vars ## ONCE_REWRITE_CONV thms o lhs) o 
				uncurry zip o convert_sexp_to_clause [] function_vars o snd o strip_forall o concl) thms;
	
	val unsplit = convert_to_clause (CONJUNCTS thm);

	val conds = map (strip_top o rhs o first (same_const ``cons`` o repeat rator o rand o lhs o snd o strip_forall) o strip_conj o concl) unsplit

	fun combine f term =
	let 	val function = mk_comb(mk_comb(inst [alpha |-> (fst o dom_rng o type_of) f,beta |-> (snd o dom_rng o type_of) f,gamma |-> sexp_type]
					``$o:('a -> 'b) -> ('c -> 'a) -> 'c -> 'b``,f),term)
	in
		if is_var term then mk_abs(term,function) else function
	end;

	fun make_split thm_list term_list_list = 
	let 	val new_funcs = (map (REWRITE_CONV (combinTheory.o_THM::thm_list) o C (curry mk_comb) ``x:sexp``)
				(flatten (map2 (fn f => fn vl => map (fn v => combine f (mk_comb(``cons``,v))) vl)
				(map (rator o lhs o snd o strip_forall o hd o strip_conj o concl) thm_list) term_list_list)))
		val clauses = convert_to_clause new_funcs
		val thm_list' = map (REWRITE_RULE (map (GEN_ALL o GSYM) new_funcs)) thm_list
	in
		thm_list' @ clauses @ ((fn ([],[]) => [] | (x,y) => make_split x (map (fn x => [x]) y))
			(unzip (filter (needs_split o snd) 
			(zip clauses (map (rhs o first (same_const ``cons`` o repeat rator o rand o lhs o snd o strip_forall) o strip_conj o concl) clauses)))))
	end;

in
	LIST_CONJ (flatten (map CONJUNCTS (make_split unsplit (map (map fst o filter (needs_split o snd)) conds))))
end

fun get_decoder_definition_revert t = 
let	val thm = get_decoder_definition_base t
	val consts = (map (repeat rator o lhs o snd o strip_forall) o strip_conj o concl) thm
in
	if not (mk_set consts = consts) then thm 
	else	
		revert_definition 
			(fn x => length (find_terms (fn y => (can (match_term ``car x``) y orelse can (match_term ``cdr x``) y) andalso (is_var o rand) y) x) = 2)
			(map (rhs ## I) o fst o strip_cond) thm
end;

fun get_detector_definition_revert t = 
let	val thm = REWRITE_RULE [GSYM PAIRP_THM] (get_detector_definition_base t)
	val consts = (map (repeat rator o lhs o snd o strip_forall) o strip_conj o concl) thm
in
	if not (mk_set consts = consts) then thm 
	else	
		revert_definition	
			(fn x => length (find_terms (fn y => can (match_term ``pairp x y z``) y andalso (is_var o rand) y) x) = 2)
			(map (rand o rator ## I) o fst o strip_acl2_or) thm
end;

(* Change the order of exists quantifiers in a theorem to have the named ones at the front *)
fun order_exists_rule names thm = 
let	val (vars,body) = (strip_exists o concl) thm;
	fun nindex x p = index x p handle e => length p + 1
	val nvars = sort (fn a => fn b => nindex (curry op= ((fst o dest_var) a)) names < nindex (curry op= ((fst o dest_var) b)) names) vars;
in
	CHOOSE_L (vars,thm) (foldr (fn (x,thm) => EXISTS (Psyntax.mk_exists(x,concl thm),x) thm) (ASSUME body) nvars)
end;


(* Given a set of rewritten definitions, rewrites again to ensure that recursive calls using nil are replaced *)
fun calculate_nils function_vars get_definition types list = 
let	val nils1 = map (tryfind (fn x => inst_subst (match_term ((rand o lhs) x) ((rhs o concl) nil_def)) x) o snd) list;
	val nils2 = map (UNDISCH o fst o EQ_IMP_RULE o REWRITE_CONV [GSYM nil_def]) nils1;
	
	val sub_functions = mapfilter get_definition 
		(filter (not o is_vartype) (filter (not o C mem types) (flatten (map (map base_type o reachable required_functions) types))));

	val nils3 = 
		mapfilter (REWRITE_RULE [GSYM nil_def] o tryfind (fn x => INST_TY_TERM (match_term ((rand o lhs o concl) x) ((rhs o concl) nil_def)) x)) 
			(map (map SPEC_ALL o CONJUNCTS) sub_functions);

	fun fix_sublist (thms,terms) =
		unzip (map2 (fn thm => fn term => 
			let val thm' = GENL function_vars (DISCH_ALL (RIGHT_CONV_RULE (REWRITE_CONV (nils2 @ nils3)) (UNDISCH_ALL (SPEC_ALL thm))))
			in	(thm',mk_eq(lhs term,(rhs o snd o strip_imp o snd o strip_forall o concl) thm')) end) thms terms);

	val done = map fix_sublist list
in
	if not (map snd done = map snd list) then calculate_nils function_vars get_definition types done else done
end;


fun make_recursive_decode_definition functions (main_decoders,extra_types,sub_types) =
let	val function_vars = map make_decode_variable main_decoders
	val sub_functions = mapfilter get_decoder_definition_revert (extra_types @ sub_types);
	val (rewrs,functions_split_base) = 
		unzip (calculate_nils function_vars get_decoder_definition_revert main_decoders (map (convert_sexp_to_clause sub_functions function_vars) functions));
	val L = remove_car_cdr sub_functions get_decoder_definition_revert function_vars (flatten (map2 zip functions_split_base rewrs))
	val function = list_mk_conj (map fst L)
	val names = map decode_function_name main_decoders;
	val thm = order_exists_rule names
				(make_recursive_definition function (has_decoder_definition,get_decoder_definition_revert,get_decoder) (main_decoders,extra_types,sub_types))
in
	new_specification((hd names) ^ "_def",names,remove_splits function_vars L thm)
end;

fun decode_of x = 
let 	val (main_decoders,extra_types,sub_types) = get_type_chain (base_type x)
	val new_decoders = map make_decode_variable main_decoders
	val _ = app add_decoder (map (fn (var,t) => (base_type t,(var,NONE))) (zip new_decoders main_decoders))
	val decodings = map (decode_cases o get_conjuncts) main_decoders
	
	fun combine_decodings []  t  = raise Empty
          | combine_decodings [x] t  = mk_eq(mk_comb(make_decode_variable_comb t,``x:sexp``),x)
	  | combine_decodings l   t = mk_eq(mk_comb(make_decode_variable_comb t,``x:sexp``),foldr mk_comb (mk_arb t) l)
	
	val functions = map2 combine_decodings decodings (map base_type main_decoders)

	val decoder_def = 
		(if length new_decoders = 1 andalso not (exists (free_in (hd new_decoders)) (hd decodings)) then
			new_definition(decode_function_name (base_type x),hd functions)
		else
			make_recursive_decode_definition functions (main_decoders,extra_types,sub_types) handle e => 
		(app remove_decoder main_decoders ; raise e))
in
	(app remove_decoder main_decoders ; add_decoder_def main_decoders decoder_def)
end;



(* Create a detection function for a case construct *)
fun return_detect_for_case conjunct = 
let	val args = (rev o snd o strip_comb o rhs o concl) conjunct
	fun make_pair_detector a l =
		mk_comb(mk_comb(``pairp``,a),l)
in
	(fn l => foldl (uncurry make_pair_detector) (hd l) (tl l)) (map (get_detector o type_of) args)
end;

fun add_detect_label NONE label = 
	mk_comb(mk_comb(``pairp``,mk_comb(``equal``,label)),``equal nil``)
|   add_detect_label (SOME function) label = 
	mk_comb(mk_comb(``pairp``,mk_comb(``equal``,label)),function);

fun detect_cases conjuncts =
let	val cases = map (fn x => SOME (return_detect_for_case x) handle Empty => NONE) conjuncts
	val labels = create_labels cases
in
	if exists isSome cases then 
		(if length labels = 1 then map valOf cases else map2 add_detect_label cases labels)
	else
		map (curry mk_comb ``equal:sexp -> sexp -> sexp``) labels
end;


fun make_recursive_detect_definition functions (main_detectors,extra_types,sub_types) =
let	val function_vars = map make_detect_variable main_detectors
	val sub_functions = mapfilter get_detector_definition_revert (extra_types @ sub_types);
	val (rewrs,functions_split_base) = 
		unzip (calculate_nils function_vars get_detector_definition_revert main_detectors (map (convert_sexp_to_clause sub_functions function_vars) functions))
	val L = remove_pairp sub_functions get_detector_definition_revert function_vars (flatten (map2 zip functions_split_base rewrs))
	val function = list_mk_conj (map fst L);
	val names = map detect_function_name main_detectors;
	val thm = order_exists_rule names
				(make_recursive_definition function (has_detector_definition,get_detector_definition_revert,get_detector) 
						(main_detectors,extra_types,sub_types))
in
	new_specification((hd names) ^ "_def",names,remove_splits function_vars L thm)
end;

fun detect_of x = 
let 	val (main_detectors,extra_types,sub_types) = get_type_chain (base_type x)
	val new_detectors = map make_detect_variable main_detectors
	val _ = app add_detector (map (fn (var,t) => (base_type t,(var,NONE))) (zip new_detectors main_detectors))
	val decodings = map (detect_cases o get_conjuncts) main_detectors
	fun make_acl2_or a b =
		mk_comb(mk_comb(mk_comb(``ite``,a),``t``),b);
	fun combine_detect_definition decodings t = 
		mk_eq(mk_comb(make_detect_variable_comb t,``x:sexp``),
			(fn l => foldl (uncurry (C make_acl2_or)) (hd l) (tl l)) (map (C (curry mk_comb) ``x:sexp``) decodings));
	val functions = map2 combine_detect_definition decodings main_detectors

	val detector_def = 
		(if length new_detectors = 1 andalso not (exists (free_in (hd new_detectors)) (hd decodings)) then
			new_definition(detect_function_name (hd main_detectors),hd functions)
		else
			make_recursive_detect_definition functions (main_detectors,extra_types,sub_types)) handle e => 
		(app remove_detector main_detectors ; raise e)
in
	(app remove_detector main_detectors ; add_detector_def main_detectors detector_def)
end;



type encode_decode_proof = {det_enc_thm : thm, dec_enc_thm : thm, enc_dec_thm : thm, case_thm : thm option,  
				judgement_thm : thm option, judgement_thm_paired : thm option, nchotomy_thm : thm option};

val proofs = ref [];

fun clear_proofs () = 
	proofs := 
	[(``:'a list``,{det_enc_thm = LISTP_LIST, case_thm = SOME LIST_CASE, enc_dec_thm = SEXP_TO_LIST_OF_LIST, dec_enc_thm = LIST_OF_SEXP_TO_LIST,
		judgement_thm = SOME (CONJUNCT1 LIST_JUDGEMENT), judgement_thm_paired = SOME (CONJUNCT2 LIST_JUDGEMENT), 
		nchotomy_thm = SOME (last (CONJUNCTS LIST_NCHOTOMY))}),
	(``:'a # 'b``,{det_enc_thm = PAIRP_PAIR, case_thm = SOME PAIR_CASE, enc_dec_thm = SEXP_TO_PAIR_OF_PAIR, dec_enc_thm = PAIR_OF_SEXP_TO_PAIR,
		judgement_thm = SOME PAIR_JUDGEMENT,judgement_thm_paired = NONE,nchotomy_thm = SOME PAIR_NCHOTOMY}),
	(``:num``, {det_enc_thm = NATP_NAT, case_thm = SOME NAT_CASE,  enc_dec_thm = SEXP_TO_NAT_OF_NAT,   dec_enc_thm = NAT_OF_SEXP_TO_NAT, 
		judgement_thm = NONE,judgement_thm_paired = NONE,nchotomy_thm = NONE}),
	(``:int``, {det_enc_thm = INTEGERP_INT, case_thm = NONE, enc_dec_thm = SEXP_TO_INT_OF_INT, dec_enc_thm = INT_OF_SEXP_TO_INT,
		judgement_thm = NONE, judgement_thm_paired = NONE,nchotomy_thm = NONE}),
	(``:rat``, {det_enc_thm = RATIONALP_RAT,case_thm = NONE, enc_dec_thm = SEXP_TO_RAT_OF_RAT, dec_enc_thm = RAT_OF_SEXP_TO_RAT,
		judgement_thm = NONE, judgement_thm_paired = NONE,nchotomy_thm = NONE}),
	(``:bool``,{det_enc_thm = BOOLEANP_BOOL,case_thm = SOME BOOL_CASE, enc_dec_thm = SEXP_TO_BOOL_OF_BOOL, dec_enc_thm = BOOL_OF_SEXP_TO_BOOL,
		judgement_thm = NONE, judgement_thm_paired = NONE,nchotomy_thm = NONE}),
	(``:char``,{det_enc_thm = CHARACTERP_CHAR,case_thm = NONE, enc_dec_thm = SEXP_TO_CHAR_OF_CHAR, dec_enc_thm = CHAR_OF_SEXP_TO_CHAR,
		judgement_thm = NONE, judgement_thm_paired = NONE,nchotomy_thm = NONE}),
	(``:string``,{det_enc_thm = STRINGP_STRING,case_thm = SOME STRING_CASE, enc_dec_thm = SEXP_TO_STRING_OF_STRING, dec_enc_thm = STRING_OF_SEXP_TO_STRING,
		judgement_thm = SOME STRING_JUDGEMENT, judgement_thm_paired = SOME STRING_JUDGEMENT, nchotomy_thm = NONE})];

val _ = clear_proofs();

fun get_proofs_base t = 
	case (assoc1 (base_type t) (!proofs))
	of NONE => raise_error 3 "proofs" ("Encode/Decode proofs not in database for type: " ^ (type_to_string t))
	|  SOME (_,proofs) => proofs
	handle e => raise_error 3 "proofs" "Type variables do not have associated proofs";

local
	fun enc_dec_concl (enc,dec,det) t = mk_eq(mk_comb(dec,(mk_comb(enc,mk_var("x",t)))),mk_var("x",t))
	fun dec_enc_concl (enc,dec,det) t = mk_imp(mk_acl2_true (mk_comb(det,``x:sexp``)),mk_eq(mk_comb(enc,mk_comb(dec,``x:sexp``)),``x:sexp``))
	fun det_enc_concl (enc,dec,det) t = mk_acl2_true(mk_comb(det,mk_comb(enc,mk_var("x",t))))
	fun get_proofs_var t = 
	let	val (enc_dec,dec_enc,det_enc) = (fn x => (enc_dec_concl x t,dec_enc_concl x t,det_enc_concl x t)) (get_encoder t,get_decoder t,get_detector t)
	in
	{	enc_dec_thm = DISCH_ALL (ASSUME (mk_forall(mk_var("x",t),enc_dec))), 
		dec_enc_thm = DISCH_ALL (ASSUME (mk_forall(``x:sexp``,dec_enc))), 
		det_enc_thm = DISCH_ALL (ASSUME (mk_forall(mk_var("x",t),det_enc))),
		judgement_thm = NONE,judgement_thm_paired = NONE,nchotomy_thm = NONE,case_thm = NONE}
	end
	fun prove_hyps select thms_list thm = 
		DISCH_AND_CONJ (foldl (uncurry (PROVE_HYP o UNDISCH_ALL o select)) (UNDISCH_ALL (REWRITE_RULE [GSYM AND_IMP_INTRO] thm)) thms_list)
	fun fix_case_thm thms_list t thm = 
	let	val encoder = get_encoder t
		val thm' = UNDISCH_ALL (REWRITE_RULE [GSYM AND_IMP_INTRO] thm)
		val thm'' = INST_TY_TERM (match_term
			(rator (find_term (fn term => rand term = (fst o dest_forall o concl) thm' andalso type_of term = sexp_type handle e => false) (concl thm')))
			encoder) thm'
		val (des,eds) = partition (is_acl2_true o snd o strip_forall o snd o strip_imp) (hyp thm'')
	in
		(prove_hyps #det_enc_thm thms_list
		(prove_hyps #enc_dec_thm thms_list 	
			(INST 	(map (fn de => (rator o dest_acl2_true o snd o dest_forall) de |-> (get_detector o type_of o fst o dest_forall) de) des)
			(INST (map (fn ed => (rator o lhs o snd o dest_forall) ed |-> (get_decoder o type_of o fst o dest_forall) ed) eds) thm''))))
	end handle e => thm
	fun SPART_MATCH thm term = DISCH_ALL (Q.GEN `x` (INST_TY_TERM (match_term ((snd o strip_forall o snd o strip_imp o concl) thm) term) ((SPEC_ALL o UNDISCH_ALL) thm)))
	fun get_proofs_concrete t = 
	let	val thms_list = map (fn x => if is_vartype x then get_proofs_var x else get_proofs_concrete x) (snd (dest_type t))
		val thms = get_proofs_base t
		val (enc_dec,dec_enc,det_enc) = (fn x => (enc_dec_concl x t,dec_enc_concl x t,det_enc_concl x t)) (get_encoder t,get_decoder t,get_detector t)
	in
	{	enc_dec_thm = prove_hyps #enc_dec_thm thms_list (SPART_MATCH (#enc_dec_thm thms) enc_dec),
		dec_enc_thm = prove_hyps #dec_enc_thm thms_list (SPART_MATCH (#dec_enc_thm thms) dec_enc),
		det_enc_thm = prove_hyps #det_enc_thm thms_list (SPART_MATCH (#det_enc_thm thms) det_enc),
		judgement_thm = #judgement_thm thms,judgement_thm_paired = #judgement_thm_paired thms, nchotomy_thm = #nchotomy_thm thms,
		case_thm = Option.map (fix_case_thm thms_list t) (#case_thm thms)}
	end
in
	fun get_proofs t = get_proofs_concrete t
end;

fun type_cache_metric a = 
let	val (a0,a1) = (first is_acl2_true o strip_conj o hd ## I) ((strip_imp o concl) a)
	val value = real o term_size o rand o dest_acl2_true
in	(value a1) / (value a0) end;

val typing_cache = 
	ref (PAIRP_CONS::LISTP_CONS::sort (curry (op> o (type_cache_metric ## type_cache_metric))) 
		(map DISCH_ALL 
			(flatten (flatten (mapfilter (map (CONJUNCTS o UNDISCH_ALL) o 
				CONJUNCTS o UNDISCH o SPEC_ALL o valOf o #judgement_thm o snd) 
						(!proofs))))))

local
	fun new_cons thm = 
	let	val l = free_vars (concl thm)
		val x1 = variant l ``x:sexp``
	in	mk_acl2_cons (x1,variant (x1::l) ``x:sexp``)
	end;
	
	fun inst_equal p thm = if (is_var o rand) p then 	INST [rand p |-> (rand o rator) p] thm else 
								INST [(rand o rator) p |-> rand p] thm
	
	fun remove_or_split thm =
	let	val preds = (map (fn x => ((fn (a,b,c) => a) o dest_acl2_cond o dest_acl2_true) x handle e =>
					  dest_acl2_true x) o strip_disj o rhs o concl) thm
	in
		op_mk_set (curry (op= o (concl ## concl))) (map (fn p => 
			if (same_const ``consp`` o rator) p then
				RIGHT_CONV_RULE (EVERY_DISJ_CONV (REWRITE_CONV [CONJUNCT1 consp_def,IF_THMS,car_def,cdr_def])) (INST [rand (hd preds) |-> new_cons thm] thm)
			else if (same_const ``equal`` o repeat rator) p then
				REDUCE_RULE (RIGHT_CONV_RULE (EVERY_DISJ_CONV (
						(RAND_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV (REWR_CONV equal_def)))) ORELSEC (RAND_CONV (REWR_CONV equal_def))) THENC
						REWRITE_CONV [LABEL_CONG] THENC REDUCE_CONV THENC 
						REWRITE_CONV [IF_THMS,el 8 (CONJUNCTS TRUTH_REWRITES),el 9 (CONJUNCTS TRUTH_REWRITES)]))
					(inst_equal p thm))
			else raise Empty) (mk_set preds))
	end;
	fun remove_all_splits thms = 
		 flatten ((uncurry (C (curry op::))) ((map remove_all_splits ## I) (mappartition remove_or_split thms)));
		
in
	fun prove_rewrite_cons detect = 
	let	val thms = map (REWRITE_RULE [ACL2_AND]) (remove_all_splits
				[REWRITE_RULE [ACL2_OR,PAIRP_THM] (AP_TERM acl2_true_tm (SPEC_ALL detect))])
	in	map (fn thm => if (is_eq o concl) thm then snd (EQ_IMP_RULE thm) else thm) thms
	end
end;


local
fun insert x [] = [x]
  | insert x (y::xs) = 
	if type_cache_metric x > type_cache_metric y then x::y::xs else y::(insert x xs)
in
fun type_cache_insert x L = 
	if (term_size o rand o dest_acl2_true o first is_acl2_true o fst o strip_imp o concl) x = (term_size o rand o dest_acl2_true o snd o strip_imp o concl) x then L 
	else insert x L
end;


fun add_proof r = 
let	val t = (base_type o type_of o rand o rand o lhs o snd o strip_forall o snd o strip_imp o concl o #enc_dec_thm) r
in	(
	proofs := (t,r) :: (!proofs) ;
	(* typing_cache := (foldl (op::) ((prove_rewrite_cons o get_detector_definition) t) (!typing_cache)) ;*)
	typing_cache := (case (#judgement_thm r)
			of NONE => (!typing_cache)
			|  SOME j => foldl (uncurry type_cache_insert) (!typing_cache)
					(map DISCH_ALL (flatten ((map (CONJUNCTS o UNDISCH_ALL) o 
						CONJUNCTS o UNDISCH o SPEC_ALL) j)))))
end;

fun make_implications (encodes,decodes,detects) = 
let	fun args_list x = map (filter is_var o snd o strip_comb o rator o lhs o snd o strip_forall o hd o strip_conj o concl) x
	fun mk_var_enc enc = mk_var("x",(fst o dom_rng o type_of) enc)
	fun make_implication (enc,(dec,det)) = 
		(mk_forall(mk_var_enc enc,mk_eq(mk_comb(dec,mk_comb(enc,mk_var_enc enc)),mk_var_enc enc)),(
		mk_forall(``x:sexp``,mk_imp(mk_acl2_true(mk_comb(det,``x:sexp``)),mk_eq(mk_comb(enc,mk_comb(dec,``x:sexp``)),``x:sexp``))),
		mk_forall(mk_var_enc enc,mk_neg(mk_eq(mk_comb(det,mk_comb(enc,mk_var_enc enc)),``nil``)))))
in
	map (map make_implication) (map2 zip (args_list encodes) (map2 zip (args_list decodes) (args_list detects)))
end;

val SPECIAL_THMS = ref [{
	nchot_eq = NAT_NCHOT_EQ,nchot = NAT_NCHOTOMY, destructor = NAT_DESTRUCT,
	constructors = CONJUNCTS NAT_CONSTRUCTORS}];

(* NCHOTOMY_TO_EQUAL_CONV: |- (?b. x = cons (nat 0) b) = (|= equal (car x) (nat 0)) *)
(* EQUAL_TO_NCHOTOMY_CONV: |- (|= equal (car x) (nat 0)) = (?b. x = cons (nat 0) b) *)

local
	val rewrite_equal1 = prove(``!x a b. ~(a = nil) \/ ~(b = nil) ==> ((|= equal x (cons a b)) = (|= equal (car x) a) /\ (|= equal (cdr x) b))``,
			Cases THEN RW_TAC std_ss [equal_def,TRUTH_REWRITES,car_def,cdr_def])
	val rewrite_equal2 = prove(``!x. (|= equal x (cons a b)) = (|= consp x) /\ (|= equal (car x) a) /\ (|= equal (cdr x) b)``,
			Cases THEN RW_TAC std_ss [equal_def,TRUTH_REWRITES,consp_def,car_def,cdr_def]);
	val rewrite_to_equal = prove(``!x y. (x = y) = |= equal x y``,REPEAT GEN_TAC THEN EQ_TAC THEN RW_TAC std_ss [equal_def,TRUTH_REWRITES]);
	val nz_proofs = [prove(``!x. ~(nat x = nil)``,RW_TAC std_ss [nat_def,int_def,cpx_def,sexpTheory.rat_def,nil_def])];
	val equal_proof = prove(``(?b. |= equal x b) /\ ?b. |= equal b x``,RW_TAC std_ss [equal_def,TRUTH_REWRITES]);
	val and_proof = prove(``(|= a) /\ (|= b) = |= andl [a; b]``,RW_TAC std_ss [andl_def,TRUTH_REWRITES,ite_def]);

	val consp_proof = prove(``!x. (|= consp x) = (?a b. x = cons a b)``,Cases THEN RW_TAC std_ss [consp_def,TRUTH_REWRITES]);
	val rewrite_car = prove(``!x y. ~(y = nil) ==> ((|= equal (car x) y) = ?b. x = cons y b)``,Cases THEN RW_TAC std_ss [TRUTH_REWRITES,car_def,equal_def]);
	val rewrite_cdr = prove(``!x y. ~(y = nil) ==> ((|= equal (cdr x) y) = ?a. x = cons a y)``,Cases THEN RW_TAC std_ss [TRUTH_REWRITES,cdr_def,equal_def]);

	val join_proof1 = prove(``(x = cons a b) /\ (x = cons c d) = (a = c) /\ (b = d) /\ (x = cons a b)``,
		EQ_TAC THEN REPEAT STRIP_TAC THEN FIRST_ASSUM SUBST_ALL_TAC THEN FULL_SIMP_TAC std_ss [sexpTheory.sexp_11]);
	val join_proof2 = prove(``(x = cons a b) /\ (car x = cons c d) = (a = cons c d) /\ (x = cons (cons c d) b)``,
		EQ_TAC THEN REPEAT STRIP_TAC THEN ASSUM_LIST (MAP_EVERY SUBST_ALL_TAC o filter (curry op= ``x:sexp`` o lhs o concl)) THEN
		FULL_SIMP_TAC std_ss [car_def,cdr_def,sexpTheory.sexp_11]);
	val join_proof3 = prove(``(x = cons a b) /\ (cdr x = cons c d) = (b = cons c d) /\ (x = cons a (cons c d))``,
		EQ_TAC THEN REPEAT STRIP_TAC THEN ASSUM_LIST (MAP_EVERY SUBST_ALL_TAC o filter (curry op= ``x:sexp`` o lhs o concl)) THEN
		FULL_SIMP_TAC std_ss [car_def,cdr_def,sexpTheory.sexp_11]);
fun NCHOTOMY_TO_EQUAL_CONV_basic term = 
let	val nz_thms = mapfilter (fn x => tryfind (C (PART_MATCH (lhs o dest_neg)) x) nz_proofs)
				(set_diff ((strip_cons o rhs o snd o strip_exists) term) ((fst o strip_exists) term))
	val rewrites = (map (MATCH_MP rewrite_equal1 o C DISJ1 ``~(b = nil)``) nz_thms) @ (map (MATCH_MP rewrite_equal1 o DISJ2 ``~(a = nil)``) nz_thms);
in
	(STRIP_QUANT_CONV (REWR_CONV rewrite_to_equal) THENC REWRITE_CONV rewrites THENC REWRITE_CONV [rewrite_equal2] THENC
	 TOP_DEPTH_CONV EXISTS_AND_CONV THENC SIMP_CONV std_ss [equal_proof,and_proof]) term
end
fun EQUAL_TO_NCHOTOMY_CONV_basic term =
let	val thm = (RAND_CONV (REWR_CONV not_def THENC REWR_CONV ite_def) THENC 
			REWRITE_CONV (CONJUNCTS TRUTH_REWRITES)) term handle _ => REFL term	
	val nz_thms = mapfilter (fn x => tryfind (C (PART_MATCH (lhs o dest_neg)) (rand x)) nz_proofs) 
		(find_terms (can (match_term ``equal a b``)) (concl thm));
	val rewrites = (map (MATCH_MP rewrite_car) nz_thms) @ (map (MATCH_MP rewrite_cdr) nz_thms)
in
	TRANS thm ((REWRITE_CONV rewrites THENC 
		REWRITE_CONV [GSYM and_proof,consp_proof,GSYM rewrite_to_equal] THENC 
		REDEPTH_CONV (LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV ORELSEC AND_EXISTS_CONV) 
		THENC SIMP_CONV std_ss [LABEL_CONG,join_proof1,join_proof2,join_proof3]) ((rand o concl) thm))
end
in
fun NCHOTOMY_TO_EQUAL_CONV term = 
	tryfind (C REWR_CONV term o #nchot_eq) (!SPECIAL_THMS) handle _ => NCHOTOMY_TO_EQUAL_CONV_basic term
fun EQUAL_TO_NCHOTOMY_CONV term = 
	tryfind (C REWR_CONV term o GSYM o #nchot_eq) (!SPECIAL_THMS) handle _ => EQUAL_TO_NCHOTOMY_CONV_basic term
end;

(****************************************************************************)
(* Matches two terms identical up to exists bound variables                 *)
(****************************************************************************)

fun exists_it [] thm = thm
  | exists_it ((v1,v2)::vars) thm = 
let	val v1' = variant (map snd vars) v1
	val thm' = exists_it vars (INST [v1 |-> v1'] thm)
in
	EXISTS (Psyntax.mk_exists(v2,subst [v1' |-> v2] (concl thm')),v1') thm'
		
end;

fun imp_exists_terms term1 term2 = 
let	val (vars1,t1) = strip_exists term1
	val (vars2,t2) = strip_exists term2
	val vars_map = 
		map (fn v2 => first (curry op= v2 o snd) 
			(map2 pair vars1 (map (inst_subst (match_term t1 t2)) vars1))) vars2
in	
	DISCH term1 (CHOOSE_L (vars1,ASSUME term1)
		((fn thm => INST_TY_TERM (match_term (hd (hyp thm)) t1) thm) (exists_it vars_map (ASSUME t1))))
end

fun EXISTS_EQUIV term1 term2 = 
	IMP_ANTISYM_RULE (imp_exists_terms term1 term2) (imp_exists_terms term2 term1)

(****************************************************************************)
(* Takes a detector and returns an nchotomy thm for the labels it detects:  *) 
(*       ~(detector x = nil) ==> (?b. x = cons (nat 0) b) \/                *)
(*                               (?b. x = cons (nat 1) b) ...               *)
(* ... the full version also contains the falsehood of other constructors:  *)
(*      (?b. x = cons (nat 0) b) /\ ~(?b. x = cons (nat 1) b) \/ ...        *)
(****************************************************************************)

fun make_detect_nchotomy detect = 
let	val nchot = REWRITE_RULE [GSYM DISJ_ASSOC] 
			(UNDISCH (fst (EQ_IMP_RULE (REWRITE_CONV [detect,ACL2_OR] (mk_acl2_true((lhs o snd o strip_forall o concl) detect))))))
	val thms = 	map (UNDISCH o PART_MATCH (fst o dest_imp) LABEL_CONS) ((strip_disj o concl) nchot) handle e =>
			map (MATCH_MP LABEL o ASSUME) ((strip_disj o concl) nchot);
in
	DISCH_ALL (DISJ_CASES_UNIONL nchot thms)
end;

fun make_detect_nchotomy_full dnchotomy = 
let	val thm = UNDISCH dnchotomy
	val disjs = (strip_disj o concl) thm
	val thms = map (ASSUME o snd o strip_exists) disjs
	fun prove_false term = 
		CONV_RULE (REWR_CONV FALSE_IMP) (DISCH_ALL (SIMP_RULE arith_ss [nil_def,LABEL_CONG,sexp_11] (ASSUME term)))
	fun fill_thm th = 
	let	val h = first is_eq (hyp th)
		val subs = [(op|-> o dest_eq) h]
	in	
		(fn x => CONJ 	x
			(REWRITE_RULE [(GSYM o ASSUME) h] (LIST_CONJ (mapfilter (prove_false o subst subs) disjs))) handle e => x)
		(foldl (fn (v,thm) => EXISTS (Psyntax.mk_exists(v,concl thm),v) thm) th (free_vars_lr (rhs h)))
	end;
in
	DISCH_ALL (DISJ_CASES_UNIONL thm (choose_thms thm (map fill_thm thms)))
end;

(****************************************************************************)
(* make_proofs:                                                             *)
(*      Given encode, decode and detect functions for all types in a        *)
(*	mutually recursive set of types, attempts to prove the following    *)
(*	theorems:                                                           *)
(*	      |- !x. decode (encode x) = x                                  *)
(*            |- !x. (|= detect x) ==> (encode (decode x))                  *)
(*            |- !x. |= detect (encode x)                                   *)
(*            |- !x. (|= detect x) ==> (x = C0) ==> (|= detect (cdr x))     *)
(*            |- !x. encode' (case a of C0 -> A x || ...) =                 *)
(*                      ite (equal (nat 0) (car x))                         *)
(*                           (encode' (A (cdr (encode x)))) ...             *)
(*                                                                          *)
(****************************************************************************)

fun make_proofs (encode,decode,detect) = 
let	val induction_uninst = (GEN_ALL o TypeBase.induction_of o type_of o rand o lhs o snd o strip_forall o hd o strip_conj o concl o SPEC_ALL) encode

	val types = filter (C mem ((map (type_of o rand o lhs o snd o strip_forall) o strip_conj o concl o SPEC_ALL) encode)) 
				((map (base_type o fst o dom_rng o type_of) o fst o strip_forall o concl) induction_uninst);

	val induction = foldl (uncurry INST_TYPE) induction_uninst
				(map (fn t => tryfind (match_type t) ((map (fst o dom_rng o type_of) o fst o strip_forall o concl) induction_uninst)) types)


	val type_from_encode = fst o dom_rng o type_of o rator o lhs o concl o SPEC_ALL o hd o CONJUNCTS
	
	val extra_types = mk_set (filter (not o C mem types) 
		(flatten (map (filter (fn x => exists (C mem types) (reachable required_functions x)) o (reachable required_functions)) types)));
	
	val encodes = 	(map LIST_CONJ (map (fn t => filter (curry op= t o type_from_encode) ((CONJUNCTS o SPEC_ALL) encode)) types)) @ 
			(map get_encoder_definition extra_types);

	val (decodes,detects) = unzip ((map (fn t => first (curry op= t o snd o dom_rng o type_of o rator o lhs o concl o SPEC_ALL o fst) 
			(zip ((CONJUNCTS o SPEC_ALL) decode) ((map (REWRITE_RULE [GSYM PAIRP_THM]) o CONJUNCTS o SPEC_ALL) detect))) types) @ 
			(zip (map get_decoder_definition extra_types) (map (REWRITE_RULE [GSYM PAIRP_THM] o get_detector_definition) extra_types)));

	val (enc_decs,(dec_encs,det_encs)) = ((I ## unzip) o unzip o map ((I ## unzip) o unzip)) (make_implications (encodes,decodes,detects));
	
	val nchotomys = (map (fn t => (ISPEC (mk_var("t",t)) o GEN_ALL o TypeBase.nchotomy_of) t) types) @ 
			(map (fn t => ((fn x => ISPEC (mk_var((fst o dest_var o hd o fst o strip_forall o concl) x,t)) x) o GEN_ALL o TypeBase.nchotomy_of) t) extra_types);
	
	(* Takes an encoder and finds its label cases: (t = C0) ==> (car (encode t) = nat 0) ... *)
	fun make_encode_cases t nchotomy encode = 
		LIST_CONJ (map (DISCH_ALL o (fn x => REWRITE_RULE (map (GSYM o ASSUME) (hyp x)) x) o REWRITE_RULE [car_def] o 
				(fn x => if (same_const ``cons`` o repeat rator o rhs o concl) x then AP_TERM ``car`` x else x) o 
				BETA_RULE o RIGHT_CONV_RULE (REWRITE_CONV [TypeBase.case_def_of t])) 
						(split_thm (rand o lhs) (hd nchotomys) (SPEC_ALL (hd encodes))))
	
	(* Convert a detect theorem to work in a clause-ish fashion *)
	fun streamline_detect detect = 
	let	val thm = REWRITE_RULE [GSYM DISJ_ASSOC,ACL2_AND,ACL2_OR,pairp_def] (AP_TERM acl2_true_tm 
			(if (free_in ``pairp`` (concl (SPEC_ALL detect))) then 
				SPEC ``cons a b`` (GEN ((rand o lhs o concl o SPEC_ALL) detect) (SPEC_ALL detect)) else SPEC_ALL detect));
		val terms = map (hd o strip_conj) ((strip_disj o rhs o concl) thm);
		fun inst_thm thm term = 
			case (strip_comb (dest_acl2_true term))
				of (eq_term,[pr,pl]) => (INST [pl |-> pr] thm handle e => INST [pr |-> pl] thm)
				| _ => raise Empty
	in
		(map (CONV_RULE (ONCE_DEPTH_CONV REDUCE_CONV) o REWRITE_RULE [TRUTH_REWRITES,equal_def,LABEL_CONG,pairp_def] o inst_thm thm) terms)
	end handle e => (map (AP_TERM acl2_true_tm) (CONJUNCTS (SPEC_ALL detect)));

	fun split [] = ([],[],[],[],[])
          | split ({case_thm,dec_enc_thm,det_enc_thm,enc_dec_thm,judgement_thm,judgement_thm_paired,nchotomy_thm}::xs) = 
	let val (c,d,p,e,j) = split xs 
	in
		(case_thm :: c,dec_enc_thm :: d,det_enc_thm::p,enc_dec_thm :: e, (nchotomy_thm,(judgement_thm_paired,judgement_thm)) :: j)
	end;

	
	val (case_thms,dec_enc_proofs,det_enc_proofs,enc_dec_proofs,judgements) = 
		split (map get_proofs (mk_set (flatten (map (filter (fn x => not (is_vartype x) andalso not (exists (C mem types) (reachable required_functions x))) o 
			(reachable required_functions)) types))));
	
	val extra_judgements = ((fn (a,b,c,d,e) => e) o split o map (get_proofs_base)) extra_types;
	
	(* Returns two judgement theorems from a detector: a paired judgement where curried constructors which form: C a b -> pairp ap bp are left in
	   and a judgement where these are removed in favour of ~(ap x = nil) /\ ~(bp x = nil) *)
	(* In the case of extra types (where theorems must already exist) the corresponding theorems are simply handed out *)
	local 
	fun make_judgement_thm_unsafe nchotomy (detect,sdetect) = 
	let	val detect_nchotomy = total make_detect_nchotomy detect
		val thms = case detect_nchotomy 
				of SOME dn =>  map (RIGHT_CONV_RULE (REWRITE_CONV sdetect) o AP_TERM acl2_true_tm) 
					(split_thm (rand o lhs) (UNDISCH dn) ((REFL o lhs o concl o SPEC_ALL) detect))
				|  NONE => [AP_TERM acl2_true_tm (SPEC_ALL detect)]
		val consts =  (map (rhs o snd o strip_exists) o (strip_disj o concl o SPEC_ALL)) nchotomy
		fun match_pairn n thm = 
			if n <= 1 then thm else (uncurry CONJ o (I ## match_pairn (n - 1)) o CONJ_PAIR) (MATCH_MP PAIR_JUDGEMENT thm);
		fun pair_and_unpair const thm = 
			(foldl (uncurry DISCH) (UNDISCH thm) (hyp thm),
			foldl (uncurry DISCH) (match_pairn ((length o snd o strip_comb) const) (UNDISCH thm)) (hyp thm))
		val no_matches = [``A ==> T``,``A ==> |= equal X Y``];
		val useful = total (DISCH_ALL o LIST_CONJ o filter (fn x => not (exists (can (C match_term (concl x))) no_matches)))
		fun pair_unpair_all thms = 
			map2 pair_and_unpair consts (case detect_nchotomy
			of SOME dn => choose_thms (UNDISCH dn) (map (fn t => PURE_REWRITE_RULE (mapfilter (SYM o ASSUME) (hyp t)) t) thms) | NONE => thms)
	in
		(detect_nchotomy,((total (DISCH_ALL o LIST_CONJ) ## Option.map GEN_ALL o useful) (unzip (pair_unpair_all 
			(map 	((fn x => PURE_REWRITE_RULE (GSYM EQUAL_EQ::(mapfilter (REWRITE_RULE [cdr_def] o GSYM o AP_TERM ``cdr`` o ASSUME) (hyp x))) x) o
				(fn x => PURE_REWRITE_RULE (mapfilter (GSYM o ASSUME) (hyp x)) x) o fst o EQ_IMP_RULE) thms)))))
	end
	in
		fun make_judgement_thm nchotomy (detect,sdetect) = 
		let 	val (nchot,(jthm_paired,jthm)) = 
				el (index (curry op= ((type_of o rhs o snd o strip_exists o hd o strip_disj o concl) nchotomy)) extra_types + 1) extra_judgements
			val match_term = (rator o lhs o hd o strip_conj o concl) detect
			val match_fun = C (PART_MATCH (rator o dest_acl2_true o hd o fst o strip_imp)) match_term o SPEC_ALL
		in
			(Option.map match_fun nchot, (Option.map match_fun jthm_paired,Option.map (GEN_ALL o match_fun) jthm))
		end     handle e => make_judgement_thm_unsafe nchotomy (detect,sdetect)
	end;


	fun function_term function = (rator o lhs o snd o strip_forall o hd o strip_conj o concl o SPEC_ALL) function;
	val enc_functions = map function_term encodes
	val det_functions = map function_term detects
	val dec_functions = map function_term decodes

	

	fun make_enc_dec enc dec = 
		let val var = mk_var("x",(fst o dom_rng o type_of) enc) in mk_eq(mk_comb(dec,mk_comb(enc,var)),var) end;
	
	(* Need to sort out sexp_to_list & sexp_to_pair style decode definitions *)

	local
		val renc_dec = map2 make_enc_dec enc_functions dec_functions
		val predicates = (map (rator o snd o strip_forall) o strip_conj o snd o strip_imp o snd o strip_forall o concl) induction;
		val predicate_map1 = map (fn x => ((fst o dom_rng o type_of) x,x)) predicates;
		val predicate_map2 = map (fn x => (x,first (can (match_type ((fst o dom_rng o type_of) x)) o type_of o rhs) renc_dec)) predicates;
		fun get_predicates term = if is_imp term then ((map (C assoc predicate_map2 o rator) o strip_conj o fst o dest_imp o snd o strip_forall) term) else []
	in
	fun make_recursive_call thm = 
	let	val predicate = mk_comb((C assoc predicate_map1 o type_of o rand o rand o lhs o concl) thm,(rand o rand o lhs o concl) thm)
		val renc_dec_filtered = (get_predicates o snd o strip_forall)
			(first (can (C match_term predicate) o snd o strip_forall o snd o strip_imp o snd o strip_forall) 
				((strip_conj o fst o dest_imp o concl o SPEC_ALL) induction))
		val recurse = find_terms (fn term => exists (can (C match_term term) o lhs) renc_dec_filtered) ((rhs o concl) thm)
	in
		foldl (fn (r,t) => (PURE_REWRITE_RULE [AND_IMP_INTRO] o DISCH r o CONV_RULE (DEPTH_CONV (REWR_CONV (ASSUME r)))) t) thm
			(map (fn rterm => tryfind (fn red => inst_subst (match_term (lhs red) rterm) red) renc_dec_filtered) recurse)
	end end;
	
	val _ = tprint_trace 1 "Proving decode of encode theorems...\n"

	(* Convert a decode theorem to work in a clause-ish fashion *)
	fun streamline_decode thm = 
	let	val (p,a,b) = (dest_cond o rhs o concl) thm
		fun rewrite term = 
		let	val thm' = CONV_HYP (TRY_CONV reduceLib.BEQ_CONV) 
				(RIGHT_CONV_RULE (RATOR_CONV (RATOR_CONV (RAND_CONV (REWR_CONV (ASSUME term)))) THENC reduceLib.COND_CONV) thm)
		in
			RIGHT_CONV_RULE (REWRITE_CONV [car_def,cdr_def])
				((CONV_HYP (REWRITE_CONV [LABEL_CONG,sexp_11,car_def] THENC REDUCE_CONV)
				(remove_hyp_eq (CONV_HYP (REWRITE_CONV [car_def])
				(if (same_const ``car`` o repeat rator o lhs o lhs) term then INST [(rand o lhs o lhs) term |-> ``cons a b``] thm' else thm')))))
		end;
	in	
		(rewrite (mk_eq(p,``T``)))::streamline_decode(rewrite (mk_eq(p,``F``)))
	end handle e => (if (is_conj o concl) thm then CONJUNCTS thm else if (not o is_cond o rhs o concl) thm then [thm] else raise e)

	val sdecodes = map (streamline_decode o SPEC_ALL) decodes;

	val thms = map2 (fn ((encode,ef),(decode,df)) => fn (nchotomy,enc_dec) => 
		map 	(make_recursive_call o 
			UNDISCH_ALL o 
			SIMP_RULE arith_ss (LABEL_CONG :: car_def :: cdr_def :: enc_dec_proofs) o
			(fn x => foldl (REWRITE_RULE [AND_IMP_INTRO] o uncurry DISCH) x enc_dec) o 
			RIGHT_CONV_RULE (TOP_DEPTH_CONV (BETA_CONV ORELSEC REWRITE_CONV
				(TypeBase.case_def_of (type_from_encode encode) :: nil_def :: ((CONJUNCTS encode) @ decode)))))
		(split_thm (rand o rand o lhs) nchotomy (REFL (fst (dest_eq (make_enc_dec ef df))))))
	(zip (zip encodes enc_functions) (zip sdecodes dec_functions)) (zip nchotomys enc_decs);

	fun last_imp term = if ris_imp term then last_imp (snd (dest_imp term)) else term;
	
	local
		val to_match = (fn x => zip (map (rand o snd o strip_forall o snd o strip_imp o snd o strip_forall) x) x) 
					((strip_conj o fst o dest_imp o concl o SPEC_ALL) induction)
		fun find_term term = (rand o rand o lhs) term handle e => (rand o rand o dest_acl2_true) term
		fun match_thm (t,match) thm = 
		let 	val term = (find_term o last_imp o snd o strip_forall o concl) thm
			val var_subst = fst (match_term t term)
		in
			if (is_imp o snd o strip_forall) match
			then	let	val imp = (fst o dest_imp o concl) thm
					val (vars1,vars2) = (free_vars_lr term,free_vars imp)
					val hs = strip_conj imp
					val ms = (map (subst var_subst o rand) o strip_conj o fst o dest_imp o snd o strip_forall) match
					val conc = (snd o dest_imp o concl) thm
				in	
					GENL (intersect vars1 vars2)
					(foldl (CONV_RULE (DEPTH_CONV (FORALL_AND_CONV ORELSEC FORALL_IMP_CONV)) o uncurry GEN)
						(CONV_RULE (LAND_CONV (REWR_CONV (CONV_RULE bool_EQ_CONV (AC_CONV (CONJ_ASSOC,CONJ_COMM) 
							(mk_eq(imp,list_mk_conj (map (fn m => first (curry op= m o find_term) hs) ms))))))) thm)
					(set_diff vars1 vars2))
				end
				else 	GENL (free_vars_lr term) thm
		end
	in			
	fun induct_theorems thms = 
		HO_MATCH_MP induction (LIST_CONJ (map (fn match => tryfind (match_thm match o remove_hyp_eq) (flatten thms)) to_match))
	end;


	val enc_dec_thms = map DISCH_ALL (filter (C mem types o type_of o hd o fst o strip_forall o concl) (CONJUNCTS (induct_theorems thms)))

	val detects' = zip detects (map streamline_detect detects);

	val (detect_nchotomy,(judgement_thm_paired,judgement_thm)) = 
		((I ## unzip) o unzip) (map2 (fn nchotomy => fn detect => make_judgement_thm nchotomy detect) nchotomys detects')

	val de_proof = (case (mk_set (flatten dec_encs)) of [] => I | (x::xs) => (fn y => mk_imp(list_mk_conj (x::xs),y)))
			(list_mk_conj (map2 (fn p => fn (e,d) => mk_forall(``x:sexp``,mk_imp(mk_acl2_true(mk_comb(p,``x:sexp``)),
				mk_eq(mk_comb(e,mk_comb(d,``x:sexp``)),``x:sexp``)))) det_functions (zip enc_functions dec_functions)));

	fun MATCH_ALL_TAC thm (assums,goal) = 
	let	val thm1 = repeat (SPEC_ALL o UNDISCH) (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] (PART_MATCH (snd o strip_imp o snd o strip_forall o snd o strip_imp) thm goal))
		fun match_assums thm1 [] = [thm1]
		  | match_assums thm1 (h::hs) = 
			flatten (mapfilter (fn m => match_assums (INST_TY_TERM m thm1) hs) (mapfilter (match_term h) assums))
	in
		(MAP_FIRST ACCEPT_TAC (match_assums thm1 (hyp thm1))) (assums,goal)
	end;
		
	val _ = tprint_trace 1 "Proving encode of decode theorems...\n"

	fun PAIR_JUDGEMENT_TAC (assums,goal) = 
	let	val new = filter (not o C mem assums o concl) (flatten (mapfilter (CONJUNCTS o MATCH_MP PAIR_JUDGEMENT o ASSUME) assums))
	in	(if null new then ALL_TAC else MAP_EVERY ASSUME_TAC new THEN PAIR_JUDGEMENT_TAC) (assums,goal) end;
	

	val dec_enc_thms = 
	(map DISCH_ALL o filter (C mem types o type_of o rand o lhs o snd o strip_imp o snd o strip_forall o concl) o CONJUNCTS o UNDISCH_ALL)
	(prove(de_proof,
		(if not (null (flatten dec_encs)) then STRIP_TAC else ALL_TAC) THEN 
		CONV_TAC (TOP_DEPTH_CONV (LEFT_AND_FORALL_CONV ORELSEC RIGHT_AND_FORALL_CONV)) THEN
		(fn (assums,goal) => 
			let val v = (list_mk_plus (map (curry mk_comb ``sexp_size``) ((fst o strip_forall) goal)))
			in
				REPEAT GEN_TAC THEN 
				STRIP_ASSUME_TAC (EXISTS (Psyntax.mk_exists(``v:num``,mk_eq(``v:num``,v)),v) (REFL v)) THEN
				POP_ASSUM MP_TAC THEN 
				MAP_EVERY (fn x => SPEC_TAC (x,x)) (rev ((fst o strip_forall) goal)) THEN
				SPEC_TAC (``v:num``,``v:num``) THEN
				HO_MATCH_MP_TAC arithmeticTheory.COMPLETE_INDUCTION THEN
				REPEAT STRIP_TAC 
			end (assums,goal)) THEN
		FIRST_ASSUM SUBST_ALL_TAC THEN
		MAP_EVERY IMP_RES_TAC (mapfilter valOf judgement_thm_paired) THEN
		MAP_EVERY IMP_RES_TAC (mapfilter valOf detect_nchotomy) THEN 
		FIRST	[	(POP_ASSUM SUBST_ALL_TAC ORELSE (IMP_RES_TAC PAIR_NCHOTOMY THEN POP_ASSUM SUBST_ALL_TAC)) THEN
				GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) bool_rewrites [nil_def,t_def] THEN
				GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) bool_rewrites [nil_def,t_def] THEN
				REPEAT (fn (assums,goal) => (if (C exists [``sym``,``cons``,``nat``] (same_const ((repeat rator o rand o rand o lhs) goal))) then
					CHANGED_TAC (ONCE_REWRITE_TAC (flatten sdecodes)) THEN 
						REWRITE_TAC [sexp_11,car_def,cdr_def,LABEL_CONG] THEN CONV_TAC REDUCE_CONV THEN 
					CHANGED_TAC (ONCE_REWRITE_TAC encodes) THEN REWRITE_TAC (sexp_11::map TypeBase.case_def_of types) else NO_TAC) 
				(assums,goal)),
				ONCE_REWRITE_TAC (flatten sdecodes) THEN REWRITE_TAC [sexp_11,car_def,cdr_def,LABEL_CONG] THEN CONV_TAC REDUCE_CONV THEN 
				ONCE_REWRITE_TAC encodes THEN REWRITE_TAC (sexp_11::map TypeBase.case_def_of types) THEN CONV_TAC REDUCE_CONV] THEN
		FULL_SIMP_TAC arith_ss [GSYM nil_def,GSYM t_def,car_def,cdr_def,LABEL_CONG,sexp_11,EQUAL_EQ] THEN
		TRY (MAP_FIRST MATCH_ALL_TAC dec_enc_proofs) THEN
		PAIR_JUDGEMENT_TAC THEN FULL_SIMP_TAC std_ss [car_def,cdr_def] THEN
		REPEAT CONJ_TAC THEN
		TRY (MAP_FIRST MATCH_ALL_TAC dec_enc_proofs) THEN
		REPEAT (fn (assums,goal) => 
			(if (same_const ``cons`` o repeat rator o lhs) goal then 
			FIRST_ASSUM (fn thm => if (rand o dest_acl2_true o concl) thm = rhs goal then 
				STRIP_ASSUME_TAC (MATCH_MP PAIR_NCHOTOMY thm) THEN POP_ASSUM SUBST_ALL_TAC THEN FULL_SIMP_TAC std_ss [car_def,cdr_def,sexp_11] THEN 
				TRY CONJ_TAC
				else NO_TAC) else NO_TAC) (assums,goal)) THEN
			(fn (assums,goal) => 
		PAT_ASSUM ``!v:num.P`` (fn thm => 
		let	val (break,nobreak) = (partition (is_comb o rand) o strip_plus o snd o dest_less o fst o dest_imp o snd o strip_forall o concl) thm
			val new_sum = (map (curry mk_comb ``sexp_size``) o filter (C free_in goal) o filter is_var o flatten o map (strip_cons o rand)) break 
		in	
			(STRIP_ASSUME_TAC o DECIDE_ANTE o REWRITE_RULE [snd (TypeBase.size_of sexp_type)] o 
			SPEC (list_mk_plus(new_sum @ (List.take(nobreak,length break + length nobreak - length new_sum)))))
		end thm) (assums,goal)) THEN
		(fn (assums,goal) => 
		let	val goals = strip_conj goal
			val matches = (map (snd o dest_imp) o strip_conj o snd o dest_imp o snd o strip_forall o hd) assums
			val vars = (fst o strip_forall o hd) assums
			val matched = mapfilter (fn m => (fn x => (rhs m,rhs x)) (first (fn g => (rator o lhs) g = (rator o lhs) m 
						andalso (rator o rand o lhs) g = (rator o rand o lhs) m) goals)) matches
			val terms = (map rand o strip_plus o fst o dest_eq o hd o fst o strip_imp o snd o strip_forall o hd) assums
		in
			POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [] o CONV_RULE (LAND_CONV (AC_CONV (ADD_ASSOC,ADD_COMM))) o SPECL 
				(map (C assoc (matched @ (zip (set_diff vars (map fst matched)) (set_diff terms (map snd matched))))) vars))
		end (assums,goal)) THEN
		PAIR_JUDGEMENT_TAC THEN
		FULL_SIMP_TAC std_ss [cdr_def,car_def] THEN 
		((FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC) ORELSE MAP_FIRST MATCH_ALL_TAC dec_enc_proofs)))
	

	fun make_det_enc enc det = 
	let 	val var = mk_var("x",(fst o dom_rng o type_of) enc)
	in	mk_acl2_true(mk_comb(det,mk_comb(enc,var))) end;

	local
		val rdet_enc = map2 make_det_enc enc_functions det_functions
		val predicates = (map (rator o snd o strip_forall) o strip_conj o snd o strip_imp o snd o strip_forall o concl) induction;
		val predicate_map1 = map (fn x => ((fst o dom_rng o type_of) x,x)) predicates;
		val predicate_map2 = map (fn x => (x,first (can (match_type ((fst o dom_rng o type_of) x)) o type_of o rand o rand o dest_acl2_true) rdet_enc)) predicates;
		fun get_predicates term = if is_imp term then ((map (C assoc predicate_map2 o rator) o strip_conj o fst o dest_imp o snd o strip_forall) term) else []
	in
	fun make_recursive_call_det_enc thm = 
	let	val predicate = mk_comb((C assoc predicate_map1 o type_of o rand o rand o dest_acl2_true o concl) thm,(rand o rand o dest_acl2_true o concl) thm)
		val rdet_enc_filtered = (get_predicates o snd o strip_forall)
			(first (can (C match_term predicate) o snd o strip_forall o snd o strip_imp o snd o strip_forall) 
				((strip_conj o fst o dest_imp o concl o SPEC_ALL) induction))
		val recurse = find_terms (fn term => exists (can (C match_term term) o dest_acl2_true) rdet_enc_filtered) (list_mk_conj (hyp thm))
	in
		foldl (fn (r,t) => (PURE_REWRITE_RULE [AND_IMP_INTRO] o DISCH r o CONV_RULE (REWRITE_CONV [ASSUME r])) t) thm
			(map (fn rterm => tryfind (fn red => inst_subst (match_term (dest_acl2_true red) rterm) red) rdet_enc_filtered) recurse)
	end end;

	local
		val match_thms = map (DISCH_ALL o SPEC_ALL o UNDISCH_ALL) 
			((DISCH_ALL (ASSUME (mk_conj(mk_var("A",``:bool``),mk_var("B",``:bool``))))) ::PAIRP_CONS :: det_enc_proofs)
	in
	fun match_det_enc_proofs thm = 
		tryfind (fn h => UNDISCH_ALL 
			(REWRITE_RULE [GSYM AND_IMP_INTRO] (DISCH_ALL (PROVE_HYP (UNDISCH_ALL 
				(CONV_RULE REDUCE_CONV (tryfind (C (PART_MATCH last_imp) h) match_thms))) thm)))) 
		(hyp thm)
	end;

	local 
		fun is_recursive h = mem ((rator o dest_acl2_true) h) det_functions
	in
	fun fix_det_enc thm = 
		foldl (fn (h,thm) => 
			if is_acl2_true h andalso (not (is_recursive h)) then 
					PROVE_HYP (SPEC ((rand o rand o dest_acl2_true) h) (ASSUME (mk_forall((rand o rand o dest_acl2_true) h,h)))) 
				thm else thm)
		thm (hyp thm)
	end;

	val _ = tprint_trace 1 "Proving detect of encode theorems...\n"

	

	val det_enc_thms = 
		map DISCH_AND_CONJ (filter (C mem types o type_of o hd o fst o strip_forall o concl) (CONJUNCTS (induct_theorems 
		(map2 (fn (df,de) => fn (e,n) => map (
			make_recursive_call_det_enc o fix_det_enc o CONV_HYP (SIMP_CONV std_ss [TRUTH_REWRITES]) o
			repeat match_det_enc_proofs o
			CONV_HYP (SIMP_CONV std_ss [ite_def,TRUTH_REWRITES,LABEL_CONG,LABEL_EQ] THENC REDUCE_CONV) o
			UNDISCH o snd o EQ_IMP_RULE o 
			RIGHT_CONV_RULE (
				REWRITE_CONV [TypeBase.case_def_of (type_from_encode e),nil_def,t_def] THENC DEPTH_CONV BETA_CONV THENC
				ONCE_REWRITE_CONV (flatten (map snd detects')) THENC
				REWRITE_CONV [GSYM nil_def,GSYM t_def,LABEL_EQ,ite_def,LABEL_CONG,equal_def] THENC REDUCE_CONV) o 
			AP_TERM acl2_true_tm o AP_TERM df o SPEC_ALL) (split_thm (rand o lhs) n e))
		(zip det_functions dec_encs) (zip encodes nchotomys)))));

	val (judgement_stripped,(judgement_paired_stripped,detect_nchotomy_stripped)) = 
		((fn x => (x ## (x ## x))) (fn x => List.take(x,length types))) (judgement_thm,(judgement_thm_paired,detect_nchotomy));

	val _ = tprint_trace 1 "Generating case theorems...\n"

	val type_var = gen_tyvar();

	val case_thms1 = 
		map (fn (t,ed) => AP_TERM (mk_var("encode",type_var --> sexp_type)) (AP_TERM (rator (TypeBase.mk_case(mk_var("X",t),
			(map (fn (a,x) => ((fn z => (z ## z) (x,mk_var("C" ^ (int_to_string a),list_mk_fun((fst o strip_fun o type_of) x,type_var)))) 
			(fn x => list_mk_comb(x,(map (fn (a,b) => mk_var("a" ^ (int_to_string a),b)) o enumerate 0 o fst o strip_fun o type_of) x)))) o 
			enumerate 0 o TypeBase.constructors_of) t))) (GSYM ed)))
		(map (fn x => ((type_of o hd o fst o strip_forall o concl) x,SPEC_ALL x)) (map UNDISCH_ALL enc_dec_thms));

	val dns = 
		map2 (fn x => fn y => INST [(repeat rand o lhs o snd o strip_exists o hd o strip_conj o hd o strip_disj o concl) x |-> (repeat rand o rhs o concl) y] x)
			(map2 (fn x => (fn SOME y => MATCH_MP (make_detect_nchotomy_full y) (SPEC_ALL (UNDISCH_ALL x)) 
					|   NONE => REFL ((rand o dest_acl2_true o concl o SPEC_ALL o UNDISCH_ALL) x))) 
				det_enc_thms detect_nchotomy_stripped)
			case_thms1;

	fun make_if_thms thms = 
	let 	fun get_hs thm = first (not o is_forall o hd o strip_conj) (hyp thm)
		val eqs = map (NCHOTOMY_TO_EQUAL_CONV o fst o strip_neg) (strip_conj (get_hs (hd thms)))
		val neqs = map (AP_TERM negation) eqs
		val left = (lhs o concl o hd) thms;
		val terms_pos = map (CONV_HYP (REWRITE_CONV (map GSYM eqs)) o UNDISCH o PART_MATCH (fst o dest_imp) (CONJUNCT1 IF_THMS_IMP) o rhs o concl) (butlast eqs)
		val terms_neg = map2 (fn a => fn b => INST [``a:sexp`` |-> b] a) 
				(map (CONV_HYP (REWRITE_CONV (map GSYM neqs)) o UNDISCH o PART_MATCH (fst o dest_imp) (CONJUNCT2 IF_THMS_IMP) o rhs o concl) (butlast neqs)) 
				(map (rhs o concl) (butlast thms));
	
		fun LAST_RAND_CONV thm term = if is_comb term andalso (type_of (rand term) = sexp_type) then 
			RAND_CONV (LAST_RAND_CONV thm) term else REWR_CONV thm term;
	
		fun in_thm thm1 thm2 = exists (aconv (hd (hyp thm1))) (hyp thm2);
	in
		map (fn thm => C (foldl (uncurry PROVE_HYP)) 	(CONJUNCTS (ASSUME (get_hs thm))) 
								(INST [``b:sexp`` |-> (rhs o concl o last) thms] (foldl (fn ((tp,tn),thm) => 
			RIGHT_CONV_RULE (LAST_RAND_CONV (if in_thm tp thm then tp else tn)) thm) ((CUNDISCH_ALL o DISCH_ALL) thm) (zip terms_pos terms_neg)))) thms
	end;

	
	fun make_cdr x = MATCH_MP CDR_THM (ASSUME x) handle e => ASSUME x;

	val case_thms = 
		map (fix_thm_type type_var o DISCH_AND_CONJ o CUNDISCH_ALL o REWRITE_RULE car_cdr_thms o DISCH_ALL o (fn x => GEN ((rand o rand o lhs o concl) x) x))
		(map2 DISJ_CASESL dns (map2 (fn a => make_if_thms o map (BETA_RULE o REWRITE_RULE ((TypeBase.case_def_of o type_of o lhs o concl o hd) a::a))) 
			(List.take(sdecodes,length dns))
		(map2 (fn d => fn c => 
			(map (fn a => foldl (uncurry PROVE_HYP) (ONCE_REWRITE_RULE [make_cdr (first (not o is_neg) (strip_conj a))] c) (CONJUNCTS (ASSUME a)))
				o strip_disj o concl) d)
		dns case_thms1)));

	val _ = tprint_trace 1 "Adding proofs to database...\n";
	
	fun zip_all ([],[],[],[],[],[],[]) = []
          | zip_all (x0::x0s,x1::x1s,x2::x2s,x3::x3s,x4::x4s,x5::x5s,x6::x6s) = 
		{case_thm = SOME x0, dec_enc_thm = x1, det_enc_thm = x2,enc_dec_thm = x3,judgement_thm = x4,judgement_thm_paired = x5, nchotomy_thm = x6}::
		zip_all (x0s,x1s,x2s,x3s,x4s,x5s,x6s)
	  | zip_all _ = raise Empty;

in
	app add_proof (zip_all (case_thms,dec_enc_thms,det_enc_thms,enc_dec_thms,judgement_stripped,judgement_paired_stripped,detect_nchotomy_stripped))
end;

fun get_encoding t = 
	(get_encoder t,get_decoder t,get_detector t,get_proofs t);

fun has_encoding t = 
let 	val s = base_type t
in	isSome (assoc1 s (!encoders)) andalso isSome (assoc1 s (!decoders)) andalso isSome (assoc1 s (!detectors)) andalso isSome (assoc1 s (!proofs))
end	handle e => false;

fun encode_type x = 
	if (has_encoding x) then tprint_trace 1 ("Type: " ^ (type_to_string x) ^ " has already been encoded.\n") else
	if (not (can TypeBase.induction_of x)) then tprint_trace 1 ("Type: " ^ (type_to_string x) ^ " is not an inductively defined type.\n") else
	if (x = sexp_type) then raise (mk_HOL_ERR "encodeLib" "encode_type" "Cannot encode sexp")
	else
let	val t = base_type x
	val (types,extra_types,sub_types) = get_type_chain t
	
	val to_encode = filter (not o has_encoding) (filter (not o is_vartype) 
				(mk_set (map base_type (flatten (map (reachable required_functions) ((map base_type extra_types) @ sub_types))))));

	fun concat [] = "" | concat [x] = x | concat (x::xs) = x ^ ", " ^ (concat xs);
	
	val _ = tprint_trace 1 ("Encoding types: [" ^ concat (map type_to_string types) ^ "] with sub-types: [" ^ 
				concat (map type_to_string sub_types) ^ "] where [" ^ concat (map type_to_string extra_types) ^ 
				"] are mutually recursive with the type set\n")

	
	val _ = if not (null to_encode) then
			tprint_trace 1 ("... but must first encode subtypes: [" ^ concat (map type_to_string to_encode) ^"]\n") else ();

	val _ = app encode_type to_encode

	val encode = (tprint_trace 1 "Generating encoding function(s)...\n" ; encode_of t);
	val decode = (tprint_trace 1 "Generating decoding function(s)...\n" ; decode_of t);
	val detect = (tprint_trace 1 "Generating detecting function(s)...\n" ; detect_of t);
in
	(tprint_trace 1 "Proving functions are correct...\n" ; make_proofs (encode,decode,detect) ; tprint_trace 1 "Success!\n")
end;

fun encode_all t = 
let	val (types,extra_types,sub_types) = get_type_chain t
	val types' = filter (not o can dom_rng) (filter (not o is_vartype) types)
in
	if exists (not o has_encoding) types' then (encode_type (hd types') ; encode_all t)
	else app encode_all (filter (not o has_encoding) (filter (not o is_vartype) (mk_set (extra_types @ sub_types))))
end;

fun all_has_encoding t = 
	if can dest_type t then
		has_encoding t andalso all all_has_encoding (snd (dest_type t))
	else
		(is_vartype t) orelse has_encoding t;
	

fun get_encode_term t = (if not (all_has_encoding t) then encode_all t else () ; get_encoder t)
fun get_decode_term t = (if not (all_has_encoding t) then encode_all t else () ; get_decoder t)
fun get_detect_term t = (if not (all_has_encoding t) then encode_all t else () ; get_detector t)

fun get_case_thm t 		= (if not (all_has_encoding t) then encode_all t else () ; #case_thm (get_proofs t));
fun get_encode_decode_thm t 	= (if not (all_has_encoding t) then encode_all t else () ; #enc_dec_thm (get_proofs t));
fun get_decode_encode_thm t 	= (if not (all_has_encoding t) then encode_all t else () ; #dec_enc_thm (get_proofs t));
fun get_detect_encode_thm t 	= (if not (all_has_encoding t) then encode_all t else () ; #det_enc_thm (get_proofs t));
fun get_judgement_thm t 	= (if not (all_has_encoding t) then encode_all t else () ; #judgement_thm (get_proofs t));
fun get_detect_nchotomy t       = (if not (all_has_encoding t) then encode_all t else () ; #nchotomy_thm (get_proofs t));

(*****************************************************************************)
(* Stage 3: Create an encoded / decoded version of the theorem               *)
(*                                                                           *)
(* |- f a = A   ---> |- encode (f (decode a')) = encode (A [decode a' / a])  *)
(*                                                                           *)
(*****************************************************************************)


(* Create a variable of the same name, but with type sexp *)
fun sexp_var var = 
	mk_var(fst (dest_var var),foldl (fn (x,l) => sexp_type --> l) sexp_type ((fst o strip_fun o type_of) var))

(* Make a decoded version of a variable *)
fun make_acl2_var var =
let	val encoded = mk_comb((get_decode_term o snd o strip_fun o type_of) var,
			foldl (fn (x,t) => mk_comb(t,mk_comb(get_encode_term x,variant (free_vars t) (mk_var("x",x))))) 
				(sexp_var var) ((fst o strip_fun o type_of) var))
in	list_mk_abs((map rand o snd o strip_comb o last o snd o strip_comb) encoded,encoded)
end;

(* Final functions *)
fun encode_decode_function thm = 
let	val args = map hd (snd (argument_list thm))
in
	INST (map2 (curry op|->) args (map make_acl2_var args)) (AP_TERM (get_encode_term ((type_of o lhs o concl) thm)) thm)
end;

(*****************************************************************************)
(* Stage 4: Create a possible rewrite and prove it can be used as such       *)
(*                                                                           *)
(* acl2_exp a b = ite P (nat (sexp_to_nat a ** sexp_to_nat b)) (nat 0),      *)
(*	          P |- (nat (sexp_to_nat a ** sexp_to_nat b) = acl2_exp a b) *)
(*                                                                           *)
(*****************************************************************************)

(* CONSTRUCTOR_CONV: encode (C0 x) = C0' x                                   *)
local
fun check_refl_conv term [] = NO_CONV term
  | check_refl_conv term (x::xs) = 
	if can (match_term ((lhs o concl) x)) term then
		if (lhs o concl) x = (rhs o concl) x then ALL_CONV term else REWR_CONV x term
	else check_refl_conv term xs
in
fun CONSTRUCTOR_CONV term = 
	if 	is_comb term andalso (has_encoder_definition o type_of o rand) term andalso
		op_mem same_const ((repeat rator o rand) term) ((TypeBase.constructors_of o type_of o rand) term)
	then 	
		check_refl_conv term
		(first (curry op= (rator term) o rator o lhs o concl o hd) (map #constructors (!SPECIAL_THMS)))
			handle UNCHANGED => raise UNCHANGED | _ =>
		(FIRST_CONV (map REWR_CONV (CONJUNCTS ((get_encoder_definition_base o type_of o rand) term))) THENC
		 REWRITE_CONV (CONJUNCTS ((TypeBase.case_def_of o type_of o rand) term)) THENC DEPTH_CONV BETA_CONV) term
	else NO_CONV term;
end;

(* List of default values for types *)
val default_values = ref [("num",``0n``),("rat",``0:rat``),("int",``0i``),("complex_rational",``num com_0``),("char",``#"a"``),("string",``""``)];

(* Returns a default value for a given type *)
local
exception no_type;
fun default_value_concrete tried t = 
let	val induction = (fn x => INST_TYPE (tryfind (C match_type t) ((map (fst o dom_rng o type_of) o fst o strip_forall o concl) x)) x) (GEN_ALL (TypeBase.induction_of t))
	val constructors = filter (curry op= t o type_of) 
		((map (rand o snd o strip_forall o snd o strip_imp o snd o strip_forall) o strip_conj o fst o dest_imp o snd o strip_forall o concl) induction)
in
	tryfind (fn chosen => subst (map (fn x => x |-> (default_value (t::tried) o type_of) x) (free_vars chosen)) chosen) constructors
end
and default_value tried t = 
	if mem t tried then raise no_type else 
		(if is_vartype t then mk_var("X",t) else assoc (fst (dest_type t)) (!default_values) handle e => default_value_concrete tried t);
in
fun default_value_concrete t = 
let	val value = default_value [] (base_type t) handle no_type => 
			raise_error 4 "add_default_value" ("Couldn't find default value for type: " ^ (type_to_string (base_type t)) ^ "\n")
	val _ = default_values := mk_set (((fst o dest_type) t,value) :: (!default_values))
	val type_subst = match_type (base_type t) t
	val term_subst = map (fn {redex,residue} => mk_var("X",residue) |-> default_value_concrete residue) type_subst
in
	inst_subst (term_subst,type_subst) value
end
fun add_default_value_hol term = mk_comb(term,(default_value_concrete o fst o dom_rng o type_of) term)
fun add_default_value term = 
let	val valued = add_default_value_hol term	
	fun conv term = 
	let 	val thm = CONSTRUCTOR_CONV term handle e => REFL term
	in	if (lhs o concl) thm = (rhs o concl) thm then thm
		else RIGHT_CONV_RULE (TRY_CONV (SUB_CONV conv)) thm
	end
in	
	conv valued
end
end;

(* Define the function, then prove the rewrite *)
fun acl2_define_function name stage3 = 
let	val mp_thm = prove(``(X = ite P a b) ==> ((|= P) ==> (a = X))``,RW_TAC std_ss [ite_def,TRUTH_REWRITES])
	val function_clause = (lhs o concl) stage3;
	val args = (map (repeat rator o last o snd o strip_comb o snd o strip_abs) o 
			snd o strip_comb o rand) function_clause
	val body = 
		mk_acl2_cond(
			list_mk_comb(mk_var("P",list_mk_fun(map type_of args,sexp_type)),args),
			function_clause,
			(rhs o concl) (add_default_value(rator function_clause)))
in
	(UNDISCH o BETA_RULE o MATCH_MP mp_thm o SPEC_ALL o ASSUME)
		(list_mk_forall(args,mk_eq(list_mk_comb(mk_var(name,list_mk_fun(map type_of args,sexp_type)),args),body)))
end;


(* Is the term I'm looking at the definition? - All quantified variables occur as arguments to the lhs *)
fun is_definition term = 
	(uncurry set_eq) ((I ## snd o strip_comb o lhs) (strip_forall term)) handle _ => false;

(* Helper function to locate the P term in the hypothesis *)
fun findP thm =
let	val hs = hyp thm
	val definition = first is_definition hs
	val term = (repeat rator o (fn (a,b,c) => a) o dest_acl2_cond o rhs o snd o strip_forall) definition
in
	first (fn x => (curry op= term o repeat rator o dest_acl2_true) x handle _ => false) hs
end;

(*****************************************************************************)
(* DESTRUCTOR_CONV: converts a decoded sexpression into a HOL term           *)
(* eg: sexp_to_list sexp_to_nat nil = []                                     *)
(*                                                                           *)
(*****************************************************************************)

(* Returns true if term is of the form: ``nat X`` *)
fun is_encoded_term term = 
	(is_comb term andalso can (C assoc (!encoders)) ((base_type o type_of o rand) term) andalso 
	can (match_term (rator term)) ((get_encode_term o type_of o rand) term)) handle _ => false;

(* Returns true if term is of the form: ``sexp_to_nat X`` *)
fun is_decoded_term term = 
	(is_comb term andalso can (C assoc (!decoders)) ((base_type o type_of) term) andalso 
	(get_decode_term o type_of) term = rator term) handle _ => false;

fun get_encoder_chain L t =
	if has_encoder_definition t then
		let	val thm = get_encoder_definition t
			val types = mk_set (map (type_of o rand) (find_terms is_encoded_term (concl thm)))
		in
			foldl (uncurry (C get_encoder_chain)) (thm::L)
				(set_diff types (map (type_of o rand o lhs o snd o strip_forall o hd o 
						strip_conj o snd o strip_forall o concl) (thm::L)))
		end
	else L;

fun PCONV term = 
let	val (a,b,c) = dest_cond term;
in
	RIGHT_CONV_RULE (FIRST_CONV (map REWR_CONV (CONJUNCTS (SPEC_ALL COND_CLAUSES))) THENC TRY_CONV PCONV)
		(IAP_THM (IAP_THM (AP_TERM conditional ((REWRITE_CONV [nil_def,t_def] THENC 
			DEPTH_CONV BETA_CONV THENC 
			REWRITE_CONV [consp_def,GSYM nil_def,GSYM t_def,cdr_def,car_def,LABEL_CONG] THENC
			REDUCE_CONV) a)) b) c)
end;

fun RDEPTH_CONV conv term = (conv ORELSEC (RAND_CONV (RDEPTH_CONV conv) THENC conv)) term

fun CCCONV term = 
	if is_decoded_term (rand term)
		then (	RAND_CONV (RAND_CONV (TRY_CONV (RDEPTH_CONV
				(FIRST_CONV (map REWR_CONV (CONJUNCTS (CONJ car_def cdr_def))))))) THENC
			TRY_CONV (RATOR_CONV CCCONV)) term
		else NO_CONV term;

fun DESTRUCTOR_CONV term = 
	if	is_decoded_term term andalso (has_decoder_definition o type_of) term then
		case ((get_detect_nchotomy o type_of) term)
		of NONE => 
			let 	val t = type_of term
			in
				REWRITE_CONV ((get_encode_decode_thm t)::(map GSYM (get_encoder_chain [] t))) term
			end
		|  SOME d =>
			if 	op_mem same_const ((repeat rator o rand) term) 
					(map (repeat rator o rhs o snd o strip_exists) 
					((strip_disj o snd o strip_imp o concl o SPEC_ALL) d)) 
			then	(RAND_CONV (REWRITE_CONV [nil_def,t_def]) THENC 
				FIRST_CONV (map REWR_CONV (CONJUNCTS ((get_decoder_definition_base o type_of) term))) 
				THENC TRY_CONV PCONV THENC TRY_CONV CCCONV THENC 
				REWRITE_CONV [GSYM nil_def,GSYM t_def]) term
			else NO_CONV term
	else NO_CONV term;

(*****************************************************************************)
(* LET_LAM_CONV / LAM_LET_CONV:                                              *)
(*	Convert terms from let expressions to lambda abstractions and back   *)
(*                                                                           *)
(*****************************************************************************)

fun LET_LAM_CONV term =
	(REWR_CONV LET_THM THENC TRY_CONV (RATOR_CONV LET_LAM_CONV)) term;

fun LAM_LET_CONV term = 
	if is_pabs term then ALL_CONV term else
	(TRY_CONV (RATOR_CONV LAM_LET_CONV) THENC REWR_CONV (GSYM LET_THM)) term;

(*****************************************************************************)
(* SEXP_TYPE_TERM_AS   :                                                     *)
(*      Given a term and a list of theorems attempts to prove statements of  *)
(*	the form |- |= detectp (encodep x).                                  *)
(*                                                                           *)
(* PROVE_TYPE_JUDGEMENT:                                                     *)
(*      Given a term of the form ``A /\ B /\ C ==> |= detectp X`` will       *)
(*      attempt to prove it by assuming the antecedents then using           *)
(*	SEXP_TYPE_TERM_AS.                                                   *)
(*                                                                           *)
(*****************************************************************************)

(* Returns true if something is a type judgement *)
fun is_type_judgement term = 
	mem ((repeat rator o dest_acl2_true o snd o strip_forall)  term) (map (fst o snd) (!detectors)) orelse
	(curry op= ``bool`` o repeat rator o dest_acl2_true o snd o strip_forall) term handle e => false;


fun cacheable term = term_size term < 30

(* SEXP_TYPE_TERM_AS:	Given a term consisting of s-expressions and encode statements   *)
(*			attempts to prove the typing judgement for it.                   *)

local
	fun get_eq_detector term =
	let	val detector = tryfind (C (PART_MATCH lhs) (dest_acl2_true term) o valOf o snd o snd) (!detectors)
	in	if (not o is_acl2_cond o rhs o concl) detector then 
			AP_TERM acl2_true_tm detector else 
			raise (mk_HOL_ERR "encodeLib" "SEXP_TYPE_TERM_AS" "No matching detector")
	end;

	fun insert_term term net = 
		if cacheable term then Net.insert (term,term) (Net.delete(term,can (match_term term)) net) else net

	fun split_case_thms x = 
	let	val cs = map SPEC_ALL (CONJUNCTS (TypeBase.case_def_of (type_of (rand (lhs (concl x))))));
		val ts = map (rand o lhs o concl) cs
	in
		map (REWR_CONV x THENC REWRITE_CONV cs THENC DEPTH_CONV BETA_CONV) 
			(map (curry mk_comb ((rator o lhs o concl) x)) ts)
	end handle e => [x]

	fun get_detector_type term =
	case (strip_comb term) 
	of (d,[]) => fst (first (curry op= d o fst o snd) (!detectors))
	|  (d,xs) => 
		let	val types = map get_detector_type xs
		in
			mk_type(fst (dest_type (get_detector_type d)),types)
		end			

	fun all_eq_detectors thm = repeat (fn l => EQ_MP (get_eq_detector (concl (hd l))) (hd l)::l) [thm]

	fun remove_single h thm = 
		UNDISCH (DISJ_IMP (CONV_RULE (REWR_CONV (CONV_RULE bool_EQ_CONV (AC_CONV (DISJ_ASSOC,DISJ_COMM) 
			(mk_eq(concl thm,list_mk_disj(dest_neg h::(filter (not o curry op= (dest_neg h)) ((strip_disj o concl) thm)))))))) thm));

	(* Try to prove constraints of the form: ~(|= P x) ==> (f x = f y) *)
	fun prove_ho_constraint term = 
	let	val proof = DISCH ((fst o dest_imp) term) 
				(CONV_RULE bool_EQ_CONV ((DEPTH_CONV BETA_CONV THENC REWRITE_CONV (COND_ID::ite_def::(ASSUME ((fst o dest_imp) term))::(CONJUNCTS TRUTH_REWRITES))) 
				((snd o dest_imp) term)))
	in
		if null (hyp proof) then proof else raise Empty
	end;

	fun make_gen term = 
	let	val (term',var) = (dest_comb o dest_acl2_true) term
		val (detect,vars) = strip_comb term'
		val vars' = map (fn v => genvar ``:sexp -> sexp``) vars
	in
		mk_acl2_true (mk_comb(list_mk_comb(detect,vars'),var))
	end

	fun is_gen term = 
		all is_genvar ((snd o strip_comb o rator o dest_acl2_true) term) handle e => true

	(* If a hypothesis is a negation of something in the conclusion, remove it *)
	fun remove_disj thm = 
		remove_disj (remove_single (first (fn x => is_neg x andalso mem (dest_neg x) ((strip_disj o concl) thm)) (hyp thm)) thm) handle e => thm;

	fun or_imp thm =
	let	val (hyps,c) = strip_imp (concl thm)
	in
		foldr (uncurry DISCH) 
			(MATCH_MP OR_IMP_CONVERT (UNDISCH_ALL thm)) hyps
		handle e => thm
	end

	fun nth_imp 0 term = term
	  | nth_imp n term = nth_imp (n - 1) ((snd o rdest_imp) term);
		

	(* if the theorems contain all the negative parts of an nchotomy, and its type can be inferred then add the nchotomy to the set *)
	fun complete_an_nchotomy thms var =
	let	val neg_disjuncts = 
			filter (fn x => (lhs o snd o strip_exists o dest_neg o concl) x = var 
				handle e => false) thms
		val all_terms = map (dest_neg o concl) neg_disjuncts;
		val r = REWRITE_CONV (car_def::cdr_def::gsym_car_cdr_thms)
		val nchotomys = filter (not o is_disj o concl) 
				(mapfilter (remove_disj o UNDISCH_ALL o CONV_HYP r o CONV_RULE r) 
				(map (C (foldl (uncurry DISCH)) 
				(filter is_neg (map concl thms)))
				(filter (fn x => length (op_set_diff aconv ((strip_disj o snd o strip_imp o 
					snd o strip_forall o concl) x) all_terms) = 1)
				(mapfilter ((fn x => INST [(rand o dest_acl2_true o fst o dest_imp o concl) x |-> var] x) 
					o SPEC_ALL o valOf o #nchotomy_thm o snd) (!proofs)))));
		val detectors = mapfilter (rator o dest_acl2_true o concl) thms;
		fun get_hyps thm = set_diff (hyp thm) (flatten (map hyp thms))
	in
		(tryfind (fn thm => 
			foldl (fn (h,thm) => if is_acl2_true h then 
				let 	val thm' = tryfind (DOUBLE_MATCH I I h) thms
				in	PROVE_HYP thm' (INST_TY_TERM (match_term h (concl thm')) thm) end
				else thm) thm (get_hyps thm))
			nchotomys handle e =>
		tryfind (fn thm => 
			foldl (fn (h,thm) => if is_acl2_true h then PROVE_HYP (prove_type_judgement thms h) thm else thm) thm (get_hyps thm))
			(filter ((fn x => exists (can (find_term (curry op= x))) detectors) o rator o dest_acl2_true o first is_acl2_true o hyp) nchotomys) handle e =>
		tryfind (fn thm => 
			foldl (fn (h,thm) => if is_acl2_true h then PROVE_HYP (prove_type_judgement thms h) thm else thm) thm (get_hyps thm))
			(filter (not o (fn x => exists (can (find_term (curry op= x))) detectors) o rator o dest_acl2_true o first is_acl2_true o hyp) nchotomys))
	end
	and resolve_thms thms = 
	let	val r = REWRITE_CONV (car_def::cdr_def::gsym_car_cdr_thms)
		val thms' = map (CONV_HYP r o CONV_RULE r) thms
		val vars = mk_set (mapfilter (lhs o snd o strip_exists o dest_neg o concl) thms')
	in
		(mapfilter (complete_an_nchotomy thms') vars) @ thms'
	end
	and best_match thms hs h =
	let	fun equiv h thms = mapfilter (fn thm => CONV_RULE (REWR_CONV (EXISTS_EQUIV (concl thm) h)) thm) thms
		val matches = (flatten (filter (not o null) 
			(mapfilter (fn thm => (mapfilter (C INST_TY_TERM thm o 
				C match_term ((snd o strip_exists) h)) o
				map (snd o strip_exists) o strip_disj o snd o rstrip_imp o concl o SPEC_ALL) thm) thms)));
		val matches' = 
			flatten (mapfilter (equiv h o (map RUNDISCH_ALL) o CONJUNCTS o or_imp o RUNDISCH_ALL) matches)
		fun PH thm1 thm2 = PROVE_HYP thm1 (INST_TY_TERM (match_term h (concl thm1)) thm2)
	in
		map (fn thm => foldl (fn (h1,thm) => 
			tryfind (fn h2 => PH (CONV_RULE (REWR_CONV (EXISTS_EQUIV (concl h2) h1)) h2) thm) 
				(flatten (map CONJUNCTS (map ASSUME hs))) handle e => thm) thm (hyp thm)) 
			(map (FOLD_HYP split_hyp) matches')
	end
	and find_match (extra,cprove,nprove) thms [] = raise Empty
          | find_match (extra,cprove,nprove) thms ((hs,[],thm)::ns) = thm
          | find_match (extra,cprove,nprove) thms ((hs,h::h_list,thm)::ns) =
	let	val next = filter (fn x => not (mem (concl x) (hyp x)))
					(((if is_type_judgement h then [SEXP_TYPE_TERM_AS' (extra,cprove,nprove) thms h] else []) handle e => [])
					@ (map (CONV_HYP (DEPTH_CONV BETA_CONV)) (best_match thms hs h)))
		fun do_it n thm hs =
		let	val m = match_term h (concl n)
			val hs' = map (inst_subst m) hs
			val _ = if exists (C free_in (concl (INST_TYPE (snd m) thm))) 
					(map #redex (fst m)) then raise Empty else ()
		in
			(hs',(map (inst_subst m) h_list) @ (set_diff (hyp n) hs'),PROVE_HYP n (INST_TY_TERM m thm))
		end
	in	
		find_match (extra,cprove,nprove) thms (ns @ 
			mapfilter (fn n => do_it n thm hs) next)
	end
	and fix_thm (extra,cprove,nprove) thm thms term =
		if null (hyp thm) then thm else
		foldl (uncurry PROVE_HYP)
			(FOLD_HYP split_hyp 
				(repeat (fn thm => tryfind (fn h => find_match (extra,cprove,nprove) thms [(hyp thm,[h],thm)]) (hyp thm))
				(CONV_HYP (DEPTH_CONV BETA_CONV THENC 
						PURE_REWRITE_CONV (car_def::cdr_def::gsym_car_cdr_thms)) 
				(foldl (UNDISCH o uncurry DISCH) thm
					(flatten (map strip_conj (term::extra)))))))
			(CONJUNCTS (REWRITE_RULE (car_def::cdr_def::gsym_car_cdr_thms) (BETA_RULE (ASSUME term))))
	and sexp_type_constructed_term (extra,cprove,nprove) thms term = 
	let	val t = (get_detector_type o rator o dest_acl2_true) term
		val decoder = get_decoder t
		val decoded = DESTRUCTOR_CONV (mk_comb(decoder,rand (dest_acl2_true term)))
		val encoded = TOP_DEPTH_CONV CONSTRUCTOR_CONV (mk_comb(get_encoder t,(rhs o concl) decoded))
		val thm = REWRITE_RULE [encoded] (PART_MATCH (rand o dest_acl2_true) (get_detect_encode_thm t)
				((lhs o concl) encoded))
		val ft = find_terms (fn term => (type_of o rand o rand) term = sexp_type andalso 
						not ((type_of o rand) term = sexp_type) andalso 
						type_of term = sexp_type handle e => false)
		val enc_decs = set_diff ((ft o concl) thm) (ft term)
		val thm' = DISCH_AND_CONJ (PURE_REWRITE_RULE 
			(map UNDISCH_ALL (map2 (PART_MATCH (lhs o snd o strip_imp)) 
			(map (get_decode_encode_thm o type_of o rand) enc_decs) enc_decs)) thm)
		val terms = (strip_conj o fst o dest_imp o concl) thm' handle e => []
	in
		if null terms then PART_MATCH I thm' term else
				PART_MATCH I (MATCH_MP thm' (LIST_CONJ (map (SEXP_TYPE_TERM_AS' (extra,cprove,nprove) thms) terms))) term
	end
	and sexp_type_lambda_term (extra,cprove,nprove) thms term = 
	let	val _ = if (is_abs o repeat rator o rand o dest_acl2_true) term then () else (NO_CONV term ; ())
		val thm1 = DEPTH_CONV BETA_CONV term
	in
		EQ_MP (GSYM thm1) (SEXP_TYPE_TERM_AS' (extra,cprove,nprove) thms ((rhs o concl) thm1))
	end
	and sexp_type_let_term (extra,cprove,nprove) thms term = 
	let	val _ = if (is_let o rand o dest_acl2_true) term then () else (NO_CONV term ; ())
		val thm1 = DEPTH_CONV LET_LAM_CONV term
	in
		EQ_MP (GSYM thm1) (sexp_type_lambda_term (extra,cprove,nprove) thms ((rhs o concl) thm1))
	end
	and sexp_type_encoded_term (extra,cprove,nprove) thms term = 
	let 	val det_encs = (all_eq_detectors o SPEC_ALL o CUNDISCH_ALL o get_detect_encode_thm o type_of o 
					rand o rand o dest_acl2_true) term
	in	tryfind (DOUBLE_MATCH I (rator o dest_acl2_true) term) det_encs 
	end
	and match_term_thm n term thm = 
		PART_MATCH (nth_imp n) thm term handle e =>
		DISCH ((fst o rdest_imp) term) (match_term_thm n ((snd o rdest_imp) term) thm) handle e =>
		PART_MATCH (nth_imp (n+1)) thm term
	and try_prove_term (extra,cprove,nprove) thms term = 
		(tryfind (match_term_thm 0 term) 
			(filter (not o is_acl2_true o snd o rstrip_imp o concl o SPEC_ALL) thms)  handle _ =>
			prove_ho_constraint term) handle e =>
		if is_type_judgement term then SEXP_TYPE_TERM_AS' (extra,cprove,nprove) thms term else raise e
	and sexp_type_match_thm_term (extra,cprove,nprove) thms term = 
	let	val all_thms = mapfilter (DOUBLE_MATCH (snd o rstrip_imp) (rator o dest_acl2_true) term) 
				(thms @ (!typing_cache))
	in	tryfind (fn thm => if (not (ris_imp (concl thm))) then thm else
			(CUNDISCH_ALL o MATCH_MP thm) 
				(LIST_CONJ ((map (uncurry GENL o (I ## try_prove_term (extra,cprove,nprove) thms) o 
					strip_forall) o strip_conj o hd o fst o rstrip_imp o concl) thm))) all_thms
	end
	and sexp_type_eq_detector_term (extra,cprove,nprove) thms term =
	let	val detector = get_eq_detector term
	in	EQ_MP (GSYM detector) (SEXP_TYPE_TERM_AS' (extra,cprove,nprove) thms ((rhs o concl) detector))
	end
	and sexp_type_ite_term (extra,cprove,nprove) thms term = 
	let	val thm = PURE_REWRITE_RULE [ANDL_REWRITE,ACL2_AND,NOT_REWRITE] (PART_MATCH (snd o strip_imp) TYPE_ITE term)
		val ((posa,posb),(nega,negb)) = ((dest_imp ## dest_imp) o dest_conj o fst o dest_imp o concl) thm
		val posa' = flatten (map all_eq_detectors
				(map (CONV_RULE (TRY_CONV EQUAL_TO_NCHOTOMY_CONV THENC TRY_CONV (REWR_CONV BOOL_TRUE))) (CONJUNCTS (ASSUME posa))))
		val nega' = CONV_RULE (TRY_CONV (RAND_CONV EQUAL_TO_NCHOTOMY_CONV)) (ASSUME nega)
		val pthms = resolve_thms (posa' @ thms)
		val nthms = resolve_thms (nega'::thms)
		val ecn_pos = (posa::extra,cprove,ref Net.empty)
		val ecn_neg =  (nega::extra,cprove,ref Net.empty)
		val posd = DISCH posa (fix_thm ecn_pos (SEXP_TYPE_TERM_AS' ecn_pos pthms posb) pthms posa)
		val negd = DISCH nega (fix_thm ecn_neg (SEXP_TYPE_TERM_AS' ecn_neg nthms negb) nthms nega)
	in
		MATCH_MP thm (CONJ posd negd)
	end
	and sexp_type_imp_term (extra,cprove,nprove) thms term = 
	let	val thm = PURE_REWRITE_RULE [ANDL_REWRITE,ACL2_AND] (PART_MATCH (snd o strip_imp) TYPE_IMP term)
		val (hyps,conc) = (dest_imp o fst o dest_imp o concl) thm
		val thms' = flatten (map all_eq_detectors
				(map (CONV_RULE (TRY_CONV EQUAL_TO_NCHOTOMY_CONV THENC TRY_CONV (REWR_CONV BOOL_TRUE))) (CONJUNCTS (ASSUME hyps))))
		val ecn_next = (conc::extra,cprove,ref Net.empty)
		val thms_next = resolve_thms (thms' @ thms)
		val thm' = DISCH hyps (fix_thm ecn_next (SEXP_TYPE_TERM_AS' ecn_next thms_next conc) thms_next conc)
	in
		MATCH_MP thm thm'
	end
	and SEXP_TYPE_TERM_AS' (extra,cprove,nprove) thms term =
	let	val r = REWRITE_CONV (car_def::cdr_def::gsym_car_cdr_thms)
		val rthm = r term handle e => REFL term
		val term' = rhs (concl rthm)
		val thms' = map (CONV_HYP r o CONV_RULE r) thms
		val typed = 
			(first (curry op= term' o concl) (Net.index term' (!cprove))) handle e =>
			if 	exists (fn x => can (C match_term term') x andalso 
				(rand o dest_acl2_true) x = (rand o dest_acl2_true) term')
					(Net.match term' (!nprove)) 
				then raise Empty 
				else
			(fprint_trace 1 "#" ; 
			tryfind (fn (a,x) => (x (extra,cprove,nprove) thms' term') )
				(enumerate 1 [	sexp_type_let_term, sexp_type_lambda_term, 
					sexp_type_ite_term, sexp_type_imp_term, sexp_type_encoded_term,
					sexp_type_match_thm_term, sexp_type_constructed_term, 
					sexp_type_eq_detector_term])) handle e =>
			((if not (is_gen term) 
				then (	SEXP_TYPE_TERM_AS' (extra,cprove,nprove) thms (make_gen term) ; 
					nprove := insert_term term (!nprove))
				else nprove := insert_term term (!nprove)) ; raise e)
		val _ = cprove := Net.insert (term',typed) (!cprove)
	in	
		EQ_MP (GSYM (PART_MATCH rhs rthm (concl typed))) typed
	end
	and prove_type_judgement thms term = 
	let	val _ = if (not o is_acl2_true o snd o strip_imp) term then 
			raise (mk_HOL_ERR "encodeLib" "PROVE_TYPE_JUDGEMENT" "Not a type judgement") else ()
		val (a,b) = strip_imp term
		val rthm = REWRITE_CONV gsym_car_cdr_thms b handle e => REFL b

		val thms' = flatten (map all_eq_detectors ((flatten (map (CONJUNCTS o ASSUME) a)) @ thms))
		val nchotomys = map (remove_disj o UNDISCH_ALL) (map (C (foldl (uncurry DISCH)) (filter is_neg a))
					(mapfilter (fn x => tryfind (C MATCH_MP x o valOf o #nchotomy_thm o snd) (!proofs)) thms'));

		val proof = foldl (uncurry PROVE_HYP) (foldl (uncurry PROVE_HYP) (sexp_type_term_as thms' ((rhs o concl) rthm)) nchotomys) 
				(flatten (map (CONJUNCTS o ASSUME) a))

	in	
		foldr (uncurry DISCH) (EQ_MP (GSYM (PART_MATCH rhs rthm (concl proof))) proof) a
	end
	and sexp_type_term_as thms term = 
	let	val thms' = flatten (map (fn x => repeat (fn l => EQ_MP (get_eq_detector (concl (hd l))) (hd l)::l) [x]) thms);
		val typed = SEXP_TYPE_TERM_AS' ([],ref (Net.empty),ref (Net.empty)) thms' term
	in	
		typed
	end
in
	val SEXP_TYPE_TERM_AS = sexp_type_term_as
	val PROVE_TYPE_JUDGEMENT = prove_type_judgement
end;

(****************************************************************************)
(* Convert a term (|= detect_t x) to a decode then encode theorem           *)
(****************************************************************************)

fun DECENC_FROM_DET t = 
let	val thm1 = tryfind (UNDISCH_ALL o C (PART_MATCH (last o fst o strip_imp)) t o DISCH_ALL o SPEC_ALL o UNDISCH_ALL o #dec_enc_thm o snd) (!proofs)
in	GEN_ALL (DISCH_ALL (repeat (fn t => 
		let 	val h = first is_forall (hyp t)
			val thm = (DECENC_FROM_DET o fst o dest_imp o snd o dest_forall) h
		in
			PROVE_HYP thm (INST_TY_TERM (match_term h (concl thm)) t)
		end) (FOLD_HYP split_hyp thm1)))
end;

(****************************************************************************)
(* Convert decoded a HOL nchotomy term to an ACL2 style one                 *)
(*         eg: (?h tl. sexp_to_list sexp_to_nat x = h::tl) =                *)
(*             (?h tl. x = cons h tl)                                       *)
(****************************************************************************)

local
fun PROVE_EXISTS thm = 
let	val term = fst (dest_imp (concl thm))
	val (vars,body) = strip_exists term
	val sub = map (fn v => first (curry op= v o #redex) (fst (match_term (rhs body) (lhs body)))) vars
	val l = lhs o snd o strip_exists o concl
	val r = rhs o snd o strip_exists o concl
	val v = fst o strip_exists o concl
in
	MATCH_MP thm (foldr (fn ({redex,residue},thm) => EXISTS (list_mk_exists(redex::(v thm),mk_eq(l thm,subst [residue |-> redex] (r thm))),residue) thm) (REFL (lhs body)) sub)
end
fun JUDGE_COMPOUND compound  = 
let	val thms = CONJUNCTS (REWRITE_RULE [car_def,cdr_def] (tryfind PROVE_EXISTS (CONJUNCTS (tryfind (C MATCH_MP compound) (mapfilter (valOf o #judgement_thm o snd) (!proofs))))))
in
	flatten (map (fn x => JUDGE_COMPOUND x handle e => [x]) thms)
end
fun general_info term =
let 	val (vars,term') = strip_exists term
	val t = (type_of o lhs) term'
	val arg_t = mk_acl2_true (mk_comb(get_detect_term t,(rand o lhs o snd o strip_exists) term))
	val thma = AP_TERM (get_encode_term t) (ASSUME term')
	val rewr_left = UNDISCH (PART_MATCH (lhs o snd o dest_imp) 
				(SPEC_ALL (get_decode_encode_thm t)) (lhs (concl thma)))
	val rewr_right = CONSTRUCTOR_CONV (rhs (concl thma))
in
	(t,arg_t,vars,term',thma,rewr_left,rewr_right)
end
fun encode_v v = mk_comb(get_encode_term (type_of v),v)
fun decode_v v = mk_comb(get_decode_term (type_of v),sexp_var v)
fun NCHOT_HOL_IMP_ACL2_basic term =
let	val (t,arg_t,vars,term',thma,rewr_left,rewr_right) = general_info term
in
	DISCH term (CHOOSE_L (vars,ASSUME (list_mk_exists (vars,term')))
		(foldr (fn ((v,sv),thm) => 
			EXISTS (Psyntax.mk_exists(sv,
				subst [encode_v v |-> sv] (concl thm)),encode_v v) thm)
		(CONV_RULE (RAND_CONV (REWR_CONV rewr_right) THENC LAND_CONV (REWR_CONV rewr_left)) thma)
		(zip vars (map sexp_var vars))))
end
and NCHOT_ACL2_IMP_HOL_basic term = 
let	val (t,arg_t,vars,term',thma,rewr_left,rewr_right) = general_info term
	val svars = map sexp_var vars
	val term'' = 
		mk_eq((rand o rand) arg_t,
			subst (map2 (curry op|->) (map encode_v vars) svars) ((rhs o concl) rewr_right))
in
	DISCH (list_mk_exists(svars,term'')) 
	(CHOOSE_L (svars,ASSUME (list_mk_exists(svars,term'')))
	(foldr (fn (v,thm) => 
			EXISTS (Psyntax.mk_exists(v,
				subst [decode_v v |-> v] (concl thm)),decode_v v) thm)
	(RIGHT_CONV_RULE (REWR_CONV (get_encode_decode_thm t)) 
	(AP_TERM (get_decode_term t) (RIGHT_CONV_RULE (REWR_CONV (GSYM rewr_right)) (ONCE_REWRITE_RULE (
		map (fn thm => GSYM (MATCH_MP (DECENC_FROM_DET (concl thm)) thm))
		 ((fn x => map (PROVE_HYP x) (JUDGE_COMPOUND x)) (REWRITE_RULE [ASSUME term''] (ASSUME arg_t))) handle e => [])
	(ASSUME term''))))) vars))
end
and NCHOT_HOL_ACL2_basic term = 
	IMP_ANTISYM_RULE (NCHOT_HOL_IMP_ACL2_basic term) (NCHOT_ACL2_IMP_HOL_basic term)
fun fix_exists_match term thm = 
let	val thm' = 
		tryfind (fn thm => 
			UNDISCH (PART_MATCH (snd o strip_exists o lhs o snd o dest_imp) thm ((snd o strip_exists) term)))
		(map DISCH_ALL (CONJUNCTS (UNDISCH thm)))
	val term' = (lhs o concl) thm'
in
	CONV_RULE (LAND_CONV (REWR_CONV (GSYM (EXISTS_EQUIV term term')))) thm'
end
in
fun NCHOT_HOL_IMP_ACL2 term = 
	fst (EQ_IMP_RULE (tryfind (fix_exists_match term o #nchot) (!SPECIAL_THMS)))
	handle e => NCHOT_HOL_IMP_ACL2_basic term
fun NCHOT_ACL2_IMP_HOL term = 
	snd (EQ_IMP_RULE (tryfind (fix_exists_match term o #nchot) (!SPECIAL_THMS)))
	handle e => NCHOT_ACL2_IMP_HOL_basic term
fun NCHOT_HOL_ACL2 term = 
	tryfind (fix_exists_match term o #nchot) (!SPECIAL_THMS)
	handle e => NCHOT_HOL_ACL2_basic term
end;

(*****************************************************************************)
(* DESTRUCTORS: Convert a term of the form x = cons a b to cdr x = a ...     *)
(*****************************************************************************)

local
fun DESTRUCTORS_basic thm =
let	fun fix (a,thm) = RIGHT_CONV_RULE (REWR_CONV (CONJUNCT1 a)) thm
	val next = CONJUNCTS (tryfind (C MATCH_MP thm o #destructor) (!SPECIAL_THMS))
			handle e => mapfilter fix [(car_def,(AP_TERM ``car`` thm)),(cdr_def,(AP_TERM ``cdr`` thm))]
in
	(next @ flatten (map DESTRUCTORS_basic next))
end
fun fix_destruct thm =
let	val t = (type_of o rand o lhs o concl) thm
in
	CONV_RULE (LAND_CONV (REWR_CONV (get_encode_decode_thm t))) (AP_TERM (get_decode_term t) thm)
end
in
fun DESTRUCTORS thm = 
	filter (is_var o lhs o concl) (mapfilter (fix_destruct o GSYM) (DESTRUCTORS_basic thm))
end;


(*****************************************************************************)
(* Stage 5: Push the encodings in (ACL2_DEPTH_CONV)                          *)
(*                                                                           *)
(* |- nat (a + b) = add (nat a) (nat b) etc...                               *)
(*                                                                           *)
(*****************************************************************************)

type acl2_dc_data = {types : thm list, missing : (term * term) list list, stage4 : thm option, next : conv, pre_next : (term * term) list list -> thm list -> conv};

fun build_data missing types stage4 pre_next = 
	({types = types,missing = missing,stage4 = stage4,next = pre_next missing types,pre_next = pre_next}:acl2_dc_data)

fun get_stage4  ({types,missing,stage4,next,pre_next}:acl2_dc_data) = valOf stage4;
fun get_missing ({types,missing,stage4,next,pre_next}:acl2_dc_data) = missing;
fun get_types   ({types,missing,stage4,next,pre_next}:acl2_dc_data) = types;
fun get_next    ({types,missing,stage4,next,pre_next}:acl2_dc_data) = next;

fun add_types   ({types,missing,stage4,next,pre_next}:acl2_dc_data) types' = 
let	val new_types = types' @ types
in	
	build_data missing new_types stage4 pre_next
end;

fun set_missing ({types,missing,stage4,next,pre_next}:acl2_dc_data) new_missing = 
	build_data new_missing types stage4 pre_next;




fun ANDL_FLATTEN_CONV term =
let	val _ = fprint_trace 4 ("andl flatten: " ^ (term_to_string term) ^ "\n")
	val (l,_) = dest_list (rand term);
in
	if same_const ``andl`` (repeat rator (hd l)) then
		(REWRITE_CONV [andl_append,APPEND] THENC ANDL_FLATTEN_CONV) term
	else
		(if length l <= 1 then REFL term else 
			(TRY_CONV (REWR_CONV (last (CONJUNCTS andl_def))) THENC RATOR_CONV (RAND_CONV ANDL_FLATTEN_CONV) THENC REWRITE_CONV [andl_fold]) term)
end;

(* Strips combs, but doesn't strip UNCURRY (\a b. c) a *)
fun pstrip_comb term = 
	if pairSyntax.is_pabs term then (term,[]) else
	let val (f,tms) = pstrip_comb (rator term) in (f,tms @ [rand term]) end handle e => (term,[]);	

(* Applies conv1 to the function and conv2 to every argument *)
fun FCOMB_CONV (conv1,conv2) term = 
let	val (func,args) = pstrip_comb term
in
	foldl (uncurry (C (curry MK_COMB))) (conv1 func) (map conv2 args)
end;

(* Remove superfluous hypothesis *)
fun clean_hyp_set thm = 
let	val hs = hyp thm
	fun subset x y = set_eq (intersect x y) x
	val simp_remove = mapfilter (fn x => let val (imps,c) = rstrip_imp x in 
		(imps,first (fn h => not (h = x) andalso (snd o rstrip_imp) h = c andalso subset ((fst o rstrip_imp) h) imps) hs) end) hs
in
	foldl (fn ((imps,sr),thm) => PROVE_HYP (foldr (uncurry DISCH) (RUNDISCH_ALL (ASSUME sr)) imps) thm) thm simp_remove
end;

(* Is the term an encoded number? *)
fun is_number term = exists (fn x => is_numeral (#residue (first (fn x => #redex x = ``n:num``) (fst (match_term x term)))) handle _ => false)
		[``nat n``,``rat (& n):sexp``,``int (& n)``,``num (com (rat (& a) (& b)) (rat (& c) (& d)))``]

(* acl2_constant, returns true when the term is a constant of ACL2 *)
fun acl2_constant term = 
	is_encoded_term term andalso (is_number term orelse (is_var o rand) term) orelse 
	(is_const term andalso all (C mem [sexp_type,``:sexp list``]) 
		(uncurry (C (curry op::)) (strip_fun (type_of term)))) orelse
	(mem (repeat rator term) [``sym``,``str``,``chr``]);

(* THENCU - a version of THENC which passes through UNCHANGED, and allows instantiation of free variables in the left hand theorem *)
infix THENCU

fun (conv1 THENCU conv2) t =
let 	val th1 = conv1 t
	val th2 = conv2 ((rhs o concl) th1)
in
	TRANS (PART_MATCH rhs th1 ((lhs o concl) th2)) th2
end;

(* is_sexp_abs - term is of the form: (\a b c. encode (A a b c)) (encode a) ... *)
fun is_sexp_abs tm = 
	is_comb tm andalso 
	(fn (a,b) => a andalso b) 
	(((fn tm => is_pabs tm andalso (is_encoded_term o snd o strip_abs) tm) ## all is_encoded_term) (pstrip_comb tm));

(* SUB_ABS_CONV  *)
fun SUB_ABS_CONV data term = 
let	val (abs_tm,args) = pstrip_comb term
	val (vars,body) = strip_abs abs_tm;
	fun fmap f g x = f (g x)
	val data' = add_types data (map2 (fmap (ASSUME o mk_acl2_true) o curry mk_comb o get_detect_term o type_of o rand) args vars);
	
	val body' = (get_next data') body
	val args' = map (get_next data) args;
in
	CONV_RULE (BINOP_CONV (
		foldl (fn (x,n) => UNBETA_CONV x THENC RATOR_CONV n) ALL_CONV args THENC
		FCOMB_CONV(RENAME_VARS_CONV (map (fst o dest_var) vars),REFL)) THENC
		FORK_CONV(ALL_CONV,FCOMB_CONV(REFL,FIRST_CONV (map REWR_CONV args'))))
	(foldl (uncurry PROVE_HYP) (INST (map2 (curry op|->) vars args) body')
		(map2 (PART_MATCH (rand o dest_acl2_true) o get_detect_encode_thm o type_of o rand) args args))
end

(* is_sexp_let - term is of the form: let a = encode b in encode c *)
fun is_sexp_let tm = 
	is_let tm andalso 
	(fn (a,b) => all (is_encoded_term o snd) a andalso is_encoded_term b) (pairSyntax.dest_anylet tm);

(* SUB_LET_CONV *)
fun SUB_LET_CONV data term = 
	(LET_LAM_CONV THENC SUB_ABS_CONV data THENC LAM_LET_CONV) term;

(* SUB_CONST_CONV - ignore top level acl2 constants and recurse on encoded sub-expressions *)
(*		  - terms should always be of the form: f (encode a) (encode b) ... or (encode a) *)
fun SUB_CONST_CONV data term = 
	if acl2_constant term then REFL term else
	if is_encoded_term term then (get_next data) term else
	if is_sexp_let term then SUB_LET_CONV data term else
	if is_sexp_abs term then SUB_ABS_CONV data term else
	if is_comb term then COMB_CONV (SUB_CONST_CONV data) term else
	if is_abs term then ABS_CONV (SUB_CONST_CONV data) term else
	if is_var term andalso type_of term = sexp_type then REFL term
	else raise UNCHANGED;

(* DISCH_BUT : Discharges a term over the conclusion, and all of the hypothesis except those in the list *)
local
	fun mapindicate f [] L = (false,L)
          | mapindicate f (x::xs) L = 
		let val (l,r) = mapindicate f xs L in (true,f x::r) handle e => (l,x::r) end;

	fun reduce imps = 
		case (partition (ris_imp o concl) imps)
		of ([],imps') => imps'
		|  (reds,imps') => 
			case (mapindicate (fn r => tryfind (MATCH_MP r) imps') reds imps')
			of (true,imps'') => reduce imps''
			|  (false,imps'') => imps'';
	fun QSIMP_CONV term = 
	let	val (conc,imps) = (I ## reduce o op_mk_set (fn a => fn b => concl a = concl b))
				(repeat (fn (x,l) => let val thm = MATCH_MP NOT_AND_IMP x in (CONJUNCT2 thm,CONJUNCT1 thm::l) end) (ASSUME (mk_neg term),[]))
	in
		(CONV_RULE (CONTRAPOS_CONV THENC RAND_CONV (REWR_CONV NOT_NOT)) o DISCH_ALL) (
			MATCH_MP NOT_AND (CONJ (first (curry op= ((dest_neg o concl) conc) o concl) imps) conc) handle e =>
			foldl (fn (a,b) => MATCH_MP NOT_IMP_IMP (CONJ a b)) conc imps)
	end;

	fun IMP_DISTRIB_RULE term (h,thm) = 
	let	val simp_term = mk_imp(term,h)
		val thmn = DISCH simp_term (DISCH term (PROVE_HYP (UNDISCH (ASSUME simp_term)) thm))
		val thmr = QSIMP_CONV simp_term
		val thm' = IMP_TRANS thmr thmn
	in
		UNDISCH (UNDISCH (CONV_RULE (LAND_CONV (REWR_CONV NOT_NOT)) thm')) handle e => 
		UNDISCH (CONV_RULE (LAND_CONV (REWR_CONV NOT_FALSE) THENC REWR_CONV TRUE_IMP) thm')
	end
in
fun DISCH_BUT term thm hs = 
	(fprint_trace 1 ("H[" ^ (int_to_string (length (hyp thm))) ^ "]") ; 
	let 	val thm' = clean_hyp_set (UNDISCH (DISCH term thm))
	in	(fn thm => clean_hyp_set (DISCH term (foldl (IMP_DISTRIB_RULE term) thm (set_diff (hyp thm) hs)))) thm' end)
end;

(* Given a theorem Q = |= P, converts the statement: [Q ==> aP, ~Q ==> bP] |- ite P (encode A) (encode B) = ite P a' b' *)
local
	val iteq_thm = prove(``(Q = |= P) /\ (Q ==> ((f:'a -> sexp) a = X)) /\ (~Q ==> (f b = Y)) ==> (ite P (f a) (f b) = ite P X Y)``,
		Cases_on `Q` THEN RW_TAC std_ss [ite_def,TRUTH_REWRITES])
	val itep_thm = prove(``((|= P) ==> ((f:'a -> sexp) a = X)) /\ (~(|= P) ==> (f b = Y)) ==> (ite P (f a) (f b) = ite P X Y)``,
		Cases_on `|= P` THEN RW_TAC std_ss [ite_def,TRUTH_REWRITES]);
in
	fun ITE_CONV_Q thms datas term =
	let	val ((p,a),b) = ((unzip ## I) o strip_ite) term
		val thms' = map2 (PART_MATCH rhs) thms (map mk_acl2_true p)
		val arg_types = get_types (hd datas)
		fun conv' data term =  
		let	val x = foldl (uncurry PROVE_HYP) ((get_next data) term) arg_types
		in	if null (hyp x) then x else 
				UNDISCH (DISCH_BUT (findP (get_stage4 data)) x 
					(filter is_definition (hyp (get_stage4 data)))) handle e => x
		end	
		val hs = filter is_definition (hyp (get_stage4 (hd datas))) handle e => []
	in
		clean_hyp_set (foldl (fn ((aterm,(data,thm)),bthm) => MATCH_MP iteq_thm 
				(LIST_CONJ [thm,DISCH_BUT ((lhs o concl) thm) (conv' data aterm) hs,DISCH_BUT ((mk_neg o lhs o concl) thm) bthm hs]))
			(conv' (last datas) b) (zip a (zip (butlast datas) thms')))
	end
	fun ITE_CONV_P data term =
	let	val ((p,a),b) = ((unzip ## I) o strip_ite) term
		val arg_types = get_types data
		fun conv' term =  
		let	val x = foldl (uncurry PROVE_HYP) ((get_next data) term) arg_types
		in	if null (hyp x) then x else 
				UNDISCH (DISCH_BUT (findP (get_stage4 data)) x 
					(filter is_definition (hyp (get_stage4 data)))) handle e => x
		end	
		val hs = filter is_definition (hyp (get_stage4 data)) handle e => []
	in
		clean_hyp_set (foldl (fn ((aterm,term),bthm) => MATCH_MP itep_thm 
				(LIST_CONJ [DISCH_BUT term (conv' aterm) hs,DISCH_BUT (mk_neg term) bthm hs]))
			(conv' b) (zip a (map mk_acl2_true p)))
	end
end;
	
	

(* IF_CONV:                                                                  *) 
(*      encodes an if statement, prefixing any generated hypothesis with P   *)
(* [.] |- encode (if P then a else b) = ite P' a' b' .. where                *)
(*       |- bool P = P', |- P ==> (encode a = a'), |- ~P ==> (encode b = b') *)

local
	val match_thm = prove(``(bool X = Y) ==> (X = |= Y)``,Cases_on `X` THEN REPEAT (RW_TAC std_ss [TRUTH_REWRITES,bool_def]))
	val rewrite = prove(``(P = |= Q) ==> ((encode:'a -> sexp) (if P then X else Y) = ite Q (encode X) (encode Y))``,
		Cases_on `P` THEN RW_TAC std_ss [TRUTH_REWRITES,ite_def]);
in
fun IF_CONV data term =
let	val (p,a,b) = dest_cond (rand term)
	val P = MATCH_MP match_thm ((get_next data) (mk_comb(``bool``,p)))
	val _ = fprint_trace 1 ".IF"
in
	RIGHT_CONV_RULE (ITE_CONV_Q [P] [data,data])
		(REWR_CONV (MATCH_MP (INST_TY_TERM (match_term ``encode:'a -> sexp`` (rator term)) rewrite) P) term)
end
end;

(* IMP_CONV:                                                                 *) 
(*      encodes an implies statement, prefixing any generated hypothesis     *)
(* [.] |- bool (A ==> B) = implies A' B'   where |- A ==> (bool B = B')      *) 
local
	val imp_thm = prove(``!A B. (A ==> (bool B = b)) /\ (bool A = a) ==> (bool (A ==> B) = implies a b)``,
		   Cases THEN Cases THEN RW_TAC std_ss [bool_def,implies_def,ite_def,andl_def])
in
fun IMP_CONV data term = 
let	val (a,b) = if is_neg (rand term) then raise (mk_HOL_ERR "boolSyntax" "dest_imp" "not an \"==>\"") else 
			dest_imp (rand term)
	fun conv' term =  
	let	val x = foldl (uncurry PROVE_HYP) ((get_next data) term) (get_types data)
	in	if null (hyp x) then x else 
		UNDISCH (DISCH_BUT (findP (get_stage4 data)) x
					(filter is_definition (hyp (get_stage4 data)))) handle e => x
	end
	val hs = filter is_definition (hyp (get_stage4 data)) handle e => []
	val b' = DISCH_BUT a (conv' (mk_comb(``bool``,b))) hs
	val a' = (get_next data) (mk_comb(``bool``,a))
in
	MATCH_MP imp_thm (CONJ b' a')
end
end;
	
(* Given a type 't' returns |- !A B. (A = B) = (encode A = encode B) *)
fun make_one_one_thm t =
let	val encode_term = get_encode_term t
	val decode_term = get_decode_term t
	val enc_dec_thm = CUNDISCH_ALL (get_encode_decode_thm t)
	val (A,B) = (mk_var("A",t),mk_var("B",t))
	val eq_term = (mk_eq(mk_comb(encode_term,A),mk_comb(encode_term,B)));
in
	GENL [A,B] (IMP_ANTISYM_RULE 
		(DISCH_ALL (AP_TERM encode_term (ASSUME (mk_eq(A,B)))))
		(DISCH eq_term (CONV_RULE (BINOP_CONV (REWR_CONV enc_dec_thm)) (AP_TERM decode_term (ASSUME eq_term)))))
end;

(* EQUAL_CONV: bool (a = b) = equal (encode a) (encode b)              *)
local
	val rewrite = prove(``bool (a = b) = equal a b``,RW_TAC std_ss [bool_def,equal_def,ite_def,nil_def,t_def])
	fun EQUAL_CONV' term = 
	let	val (a,b) = (dest_eq o rand) term
	in
		RIGHT_CONV_RULE (REWR_CONV rewrite) (AP_TERM ``bool`` (SPECL [a,b] (make_one_one_thm (type_of a))))
	end;
in
	fun EQUAL_CONV term = if can (match_term ``bool (a = b:'a)``) term then EQUAL_CONV' term else NO_CONV term
end;



(* Rewrites the current term with the rewrite defined in stage4 *)
(* Terms will be of the form: encode (f (g (decode a)) (h (decode b)) ...)               *)
(* and will be encoded to be: acl2_f (encode (g (decode a))) (encode (h (decode b))) ... *)
(* the arguments will then be encoded                                                    *)
local
fun can_recurse_conv stage4 term =
let	val (enc1,(function1,args1)) = (I ## strip_comb) ((dest_comb o lhs o concl) stage4)
	val (enc2,(function2,args2)) = (I ## strip_comb) (dest_comb term)
in
	(can (match_term enc2) enc1) andalso (can (match_term function1) function2) andalso (map type_of args1 = map type_of args2)
end
fun curry_args [] = []
  | curry_args ((x,y)::xys) = 
	if is_decoded_term y then x::curry_args xys
	else  curry_args (zip ((snd o strip_comb) x) ((snd o strip_comb) y) @ xys)
fun RECURSE_CONV' data term =
let	val stage4 = get_stage4 data
	val args = curry_args (zip ((snd o strip_comb o rand) term) ((snd o strip_comb o rand o lhs o concl) stage4))
	val enc_dec_thms = map (get_encode_decode_thm o type_of) args
	val wrapped = map2 (fn arg => fn thm => 
			RIGHT_CONV_RULE (RAND_CONV (get_next data)) (GSYM (CUNDISCH_ALL (PART_MATCH (lhs o snd o strip_imp) 
					((DISCH_ALL o SPEC_ALL o CUNDISCH_ALL) thm)
				(mk_comb((get_decode_term o type_of) arg,mk_comb((get_encode_term o type_of) arg,arg))))))) args enc_dec_thms
	val wrap = ONCE_DEPTH_CONV (FIRST_CONV (map REWR_CONV wrapped)) 
		(inst_subst (match_term (rator term) ((rator o lhs o concl) stage4)) term)
in
	TRANS wrap (INST_TY_TERM (match_term ((lhs o concl) stage4) ((rhs o concl) wrap)) stage4)
end
in
fun RECURSE_CONV data term = if (can_recurse_conv (get_stage4 data) term handle _ => false) then 
	(fprint_trace 1 ".REC(" ; let val res = RECURSE_CONV' data term in (fprint_trace 1 ")" ; res) end) else NO_CONV term
end;

(* Extra judgements for newly defined functions *)
val function_judgements = ref ([]:thm list);

(* DEC_ENC_CONV: if a term matches encode (decode x) then replace it with x              *)
local
fun STA cache thms1 thms2 term = 
	tryfind (DOUBLE_MATCH I (rator o dest_acl2_true) term) (Net.match term (!cache)) handle e =>
	let 	val r = SEXP_TYPE_TERM_AS (thms1 @ thms2) term
	in
		(cache := Net.insert (term,r) (!cache) ; r)
	end
fun DEC_ENC_CONV' cache data term = 
let	val (enc,(dec,var)) = (I ## dest_comb) (dest_comb term)
	val t = (fst o dom_rng o type_of) enc
	val (encode_term,decode_term,detect_term) = (get_encode_term t,get_decode_term t,get_detect_term t)
in	
	if can (match_term enc) encode_term andalso dec = decode_term then
		(if is_vartype t then 
			(fprint_trace 1 ".DEC_ENC" ; 
				UNDISCH (SPEC var (ASSUME (mk_forall(``a:sexp``,
						mk_imp(mk_acl2_true(mk_comb(detect_term,``a:sexp``)),
				mk_eq(mk_comb(encode_term,mk_comb(decode_term,``a:sexp``)),``a:sexp``)))))))
		else 
			let 	val term' = inst_subst (match_term enc encode_term) term;
				val thm = (fn x => DISCH (first is_acl2_true (hyp x)) x) 
						(CUNDISCH_ALL (PART_MATCH (lhs o snd o strip_imp) 
						((DISCH_ALL o SPEC_ALL o CUNDISCH_ALL) (get_decode_encode_thm t)) term'))
				val _ = fprint_trace 1 ".DEC_ENC("
				val res = 
					tryfind (MP thm) (get_types data) handle e =>
					(MATCH_MP thm o CONV_HYP (DEPTH_CONV 
						(STRIP_QUANT_CONV (TEST_DEC_ENC_CONV cache data)))) 
						(STA cache (get_types data) (!function_judgements) 
							((fst o dest_imp o concl) thm))
			in	
				(fprint_trace 1 ")" ; res)
			end)	handle e => NO_CONV term
	else NO_CONV term
end
and TEST_DEC_ENC_CONV cache data term = 
	if is_encoded_term term andalso (is_comb o rand) term andalso has_encoding (type_of (rand term)) then 
		DEC_ENC_CONV' cache data term else NO_CONV term
in
fun DEC_ENC_CONV cache data term = (TEST_DEC_ENC_CONV cache data THENCU SUB_CONST_CONV data) term
end

(* LAMBDA_CONV:                                                             *)
(* 	encodes a term of the form:                                         *)
(*	``encode((\a0 a1... .b a0 a1...) c0 c1...``                         *)
local
fun SWAP_CONV f list = 
let 	val list' = f (map2 (C SPEC o GSYM o get_encode_decode_thm o type_of) list list)
in	fn term => first (curry op= term o lhs o concl) list'
end;		
fun unpair_list [] = []
  | unpair_list (x::xs) = 
	if (is_pair o lhs o concl) x then
		(PURE_REWRITE_RULE [FST] (IAP_TERM fst_tm x)) ::
		unpair_list ((PURE_REWRITE_RULE [SND] (IAP_TERM snd_tm x))::xs)
	else	x::unpair_list xs
fun LAMBDA_CONV' tm = 
let	val rand_tm = rand tm
	val (abs_tm,args) = pstrip_comb rand_tm
	val (vars,body) = pairSyntax.strip_pabs abs_tm
in
	(RAND_CONV (
		FCOMB_CONV (STRIP_BINDER_CONV NONE (ONCE_DEPTH_CONV (SWAP_CONV unpair_list vars)),
						ONCE_DEPTH_CONV (SWAP_CONV I args)) THENC
		PairRules.LIST_PBETA_CONV THENC 
		DEPTH_CONV (FIRST_CONV (map (fn arg => 
			let val t = type_of arg in 
				REWR_CONV (MATCH_MP (get_decode_encode_thm t) (SPEC arg (get_detect_encode_thm t)))
			end) args))) THENC
	foldl (fn (x,n) => UNBETA_CONV (mk_comb(get_encode_term (type_of x),x)) THENC RATOR_CONV n) ALL_CONV args THENC
	FCOMB_CONV(RENAME_VARS_CONV (map (fn v => String.concat (map (fst o dest_var) (strip_pair v))) vars),REFL)) tm
end
in
fun LAMBDA_CONV tm = 
	if (is_encoded_term tm andalso (is_comb o rand) tm andalso (is_pabs o fst o pstrip_comb o rand) tm) then
		LAMBDA_CONV' tm
	else
		NO_CONV tm
end;

(* LET_CONV:                                                                *)
(* 	encodes a term of the form: ``encode (let a = b in c)``             *)
fun LET_CONV tm =	
	(RAND_CONV LET_LAM_CONV THENC LAMBDA_CONV THENC LAM_LET_CONV) tm

fun convert_missing conv [] = (NONE,[])
  | convert_missing conv clist = 
let	val var = (fst o hd) clist
	val t = type_of var
	val thms = map (fn (a,b) => NCHOT_HOL_ACL2 (list_mk_exists (free_vars b,mk_eq (a,b)))) clist
	val terms = filter (fn x => 
			not (exists (can (C match_term ((snd o strip_exists) x)) o 
				snd o strip_exists o lhs o concl) thms)) 
			((strip_disj o concl) (ISPEC var (TypeBase.nchotomy_of t)));
in
	case terms
	of [x] => (SOME (NCHOT_HOL_ACL2 x),thms)
	|  _   => (NONE,thms)
end

(* CASE_CONV:                                                               *)
(*      encodes a case statement, using the case theorem from the proofs    *)

(* Going to get: 	?b. x = cons (nat 1) b 	==> 	equal (car (encode a)) (nat 1) 
			x = X	 		==>	equal (encode a) X
   and we can get the other things from the nchotomy_thm *)

local	
	fun RITE_CONV [] term = ALL_CONV term
	  | RITE_CONV (x::xs) term = 
		((RATOR_CONV o RATOR_CONV o RAND_CONV) (REWR_CONV x) THENC RAND_CONV (RITE_CONV xs)) term;
	fun SKIP_CONV conv term = 
		if is_comb term andalso mem (rator term) [``car``,``cdr``,``consp``] then 
			AP_TERM (rator term) (SKIP_CONV conv (rand term)) else conv term
	fun CASE_CONV' data term = 
	let	val t = (type_of o rand o rand) term
		val (_,var,cases) = TypeBase.dest_case (rand term);
		val missings = map (fn (c,_) => filter (can (match_term c) o snd o fst) 
				(map (pluck (curry op= var o fst)) (get_missing data)) handle e => []) cases;
		val datas = map (set_missing data o map snd) 
				(filter (fn x => not (length x = 1 andalso (null o snd o hd) x)) missings)
		val conv = get_next data
		val case_thm = CUNDISCH_ALL (HO_PART_MATCH (lhs o snd o strip_imp) 
					((DISCH_ALL o SPEC_ALL o CUNDISCH_ALL o valOf o get_case_thm) t) term)
		val (keep,removes) = 
			convert_missing conv 
				(map (fst o hd) (filter (fn x => length x = 1 andalso (null o snd o hd) x) missings))
		
		val removes_acl2 = 
			map (UNDISCH o fst o EQ_IMP_RULE o 
				AP_TERM ``$~:bool -> bool`` o NCHOTOMY_TO_EQUAL_CONV o rhs o concl) removes;
		val keep_acl2 = Option.map (UNDISCH o fst o EQ_IMP_RULE o NCHOTOMY_TO_EQUAL_CONV o rhs o concl) keep;

		val ((ps_prev,_),_) = ((unzip ## I) o strip_ite o rhs o concl) case_thm;
		val ps_thms = 
			map (fn t => tryfind (GEN_ALL o C MATCH_MP t) (CONJUNCTS (GSYM IF_THMS_IMP)))
			(mapfilter (fn p => tryfind 
				(fn x => INST_TY_TERM ((C match_term p o dest_acl2_true o fst o strip_neg o concl) x) x) 
				(mapfilter valOf (keep_acl2::(map SOME removes_acl2)))) ps_prev);
		
		val case_thm' = REWRITE_RULE ps_thms case_thm
		val ((ps,a),b) = ((unzip ## I) o strip_ite o rhs o concl) case_thm';
		val _ = fprint_trace 1 ".CASE("
		val ite_thms1 = map (RAND_CONV (SKIP_CONV conv) THENC TRY_CONV (RATOR_CONV (RAND_CONV (SKIP_CONV conv)))) ps;
		val ite_thms2 = map (GSYM o EQUAL_TO_NCHOTOMY_CONV o mk_acl2_true o rhs o concl) ite_thms1;
	in
		(RIGHT_CONV_RULE (RITE_CONV ite_thms1 THENC ITE_CONV_Q ite_thms2 datas) case_thm')
		before (fprint_trace 1 ")")
	end
in
	fun CASE_CONV data term = 
		if is_comb term andalso (TypeBase.is_case o rand) term then 
			CASE_CONV' data term
		else 
			NO_CONV term
end;

(* Converts terms of the from bool (if |= P x /\ |= Q y... then ...) , ** but only if P, Q... are valid detectors ** *)
local
	val andl_thm = prove(``(|= P) /\ (|= Q) = |= andl [P; Q]``,RW_TAC std_ss [ANDL_REWRITE]);
	val ite_thm = prove(``((|= P) ==> (bool a = A)) /\ (~(|= P) ==> (bool b = B)) ==> (bool (if |= P then a else b) = ite P A B)``,RW_TAC std_ss [TRUTH_REWRITES,ite_def]);
in
fun CONSTRAINT_CONV data term =
let	val (dec,a,b) = (dest_cond o rand) term
	val conv = get_next data
in
	if all (C mem (map (fst o snd) (!detectors))) ((map (repeat rator o dest_acl2_true) o strip_conj) dec) then
		 let 	val dec_rw = TRY_CONV (REWRITE_CONV [andl_thm] THENC RAND_CONV ANDL_FLATTEN_CONV) dec handle e => REFL dec
			val A = CONV_RULE (LAND_CONV (REWR_CONV dec_rw)) (DISCH dec (foldl (uncurry PROVE_HYP) ((DEPTH_CONV BETA_CONV THENC conv) (mk_comb(rator term,a))) (CONJUNCTS (ASSUME dec))))
			val B = CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV dec_rw))) (DISCH (mk_neg dec) ((DEPTH_CONV BETA_CONV THENC conv) (mk_comb(rator term,b))))
		in
			MATCH_MP ite_thm (CONJ A B)
		end
	else
		NO_CONV term
end
end;

exception bad_term of (term * acl2_dc_data);

(* ACL2_DEPTH_CONV *)
local
	fun tryfind_u f [] = raise UNCHANGED
          | tryfind_u f (x::xs) = (f x) handle UNCHANGED => raise UNCHANGED 
						| bad_term t => raise bad_term t | e => tryfind_u f xs;
	fun print_if s f r = (let val result = f r in (fprint_trace 1 s ; result) end)
	fun ACL2_DEPTH_CONV_basic cache thms data term =
	let 	fun std_conv s conv data = (print_if s conv) THENCU SUB_CONST_CONV data
	in
		tryfind_u (fn x => x term) [
			CONSTRAINT_CONV data,
			std_conv ".LET" LET_CONV data,
			std_conv ".LAM" LAMBDA_CONV data,
			RECURSE_CONV data,
			IF_CONV data,
			CASE_CONV data,
			std_conv ".EQ"  EQUAL_CONV data,
			DEC_ENC_CONV cache data,
			IMP_CONV data,
			(fn term => (tryfind (fn (x,thm) => print_if (".T" ^ (int_to_string x))
					(CUNDISCH_ALL o C (DOUBLE_MATCH (lhs o snd o strip_imp) rator) thm) term) 
						(enumerate 1 thms)))
				 THENCU SUB_CONST_CONV data,
			(print_if ".CONS" (fn x => CONSTRUCTOR_CONV x handle UNCHANGED => REFL x)) 
				THENCU SUB_CONST_CONV data]
		handle UNCHANGED => 
			if acl2_constant term then 
				(fprint_trace 1 ".const" ; REFL term) else raise bad_term (term,data)
	end
in
	fun ACL2_DEPTH_CONV_C cache arg_types thms stage4 missing term = 
	let	val data = build_data missing arg_types stage4 
				(fn missing => fn types => ACL2_DEPTH_CONV_C cache types thms stage4 missing)
	in	
		ACL2_DEPTH_CONV_basic cache thms data term
		handle (bad_term (term,data)) => 
			(raise_error 5 "ACL2_DEPTH_CONV" ("Unencodable term: " ^ term_to_string term))
	end
	fun ACL2_DEPTH_CONV arg_types thms stage4 missing term = 
		ACL2_DEPTH_CONV_C (ref Net.empty) arg_types thms stage4 missing term
end;

(* Final function *)
fun convert_acl2 arg_types stage3 stage4 missing thms = 
let	val clean_it = clean_hyp_set o C (foldl (uncurry PROVE_HYP)) arg_types
in
		(clean_it ((fn thm => if can (first is_definition) (hyp thm) then thm else 
			CUNDISCH_ALL (DISCH (first is_definition (hyp stage4)) (DISCH_BUT (findP stage4) thm [])))
		(RIGHT_CONV_RULE (ACL2_DEPTH_CONV arg_types thms (SOME stage4) missing) stage3)))
	before
		(fprint_trace 1 "\n")
end;

(*****************************************************************************)
(* Stage 6: Remove the |= P term with the theorem list given by:             *)
(*                                                                           *)
(* 1) Convert all case theorems to HOL style (save conversion theorems)      *)
(* 2) Convert non-typing judgements to sexp style                            *)
(* 3) Attempt to prove hyps which are not typing judgements                  *)
(* 4) Make a P-term using non-typing judgements and the typing judgements    *)
(* 5) Prove all of the hypothesis using the theorems from (1)                *)
(*                                                                           *)
(*****************************************************************************)

val rewrite_thms = ref (flatten (map CONJUNCTS [NAT_THMS,INT_THMS,RAT_THMS,COM_THMS,BOOL_THMS,
				LIST_THMS,PAIR_THMS,STRING_THMS]));

(* Given a type judgement and a case term converts the term to a HOL term                     *)
(* eg: CONVERT_TO_HOL ``?a b. x = cons a b`` ``|= listp natp x``                              *)
(*	[|= listp natp x] |- (?a b. x = cons a b) = ?a b. sexp_to_list sexp_to_nat x = a::b   *)
local
	fun exists_and_choose term thm = 
	let	val rlist = map2 (fn x => fn y => (mk_var(fst (dest_var x),type_of y),y)) ((fst o strip_exists) term) ((snd o strip_comb o rhs o concl) thm)
	in
		DISCH term (CHOOSE_L ((fst o strip_exists) term,ASSUME term) 
			(foldr (fn ((v,term),thm) => EXISTS (Psyntax.mk_exists(v,subst [term |-> v] (concl thm)),term) thm) thm rlist))
	end
	fun conv_then_exists conv term t thm = 
		exists_and_choose term (RIGHT_CONV_RULE conv thm) handle e => 
		DISCH term (RIGHT_CONV_RULE (REWR_CONV (get_encode_decode_thm t)) thm)
in
fun CONVERT_TO_HOL term detector =
let	val enc_dec_thm = CHOOSEP (map (#dec_enc_thm o snd) (!proofs)) detector
	val t = (type_of o rand o lhs o snd o strip_imp o concl) enc_dec_thm;
	val thm1 = conv_then_exists DESTRUCTOR_CONV ((fst o strip_neg) term) t (AP_TERM (get_decode_term t) (ASSUME ((snd o strip_exists o fst o strip_neg) term)))
	val term' = (snd o strip_imp o concl) thm1
	val thm2 = REWRITE_RULE [UNDISCH enc_dec_thm] (AP_TERM (get_encode_term t) (ASSUME ((snd o strip_exists o fst o strip_neg) term')))
	val thm = 	IMP_ANTISYM_RULE thm1 (DISCH term' thm2) handle e => 
			IMP_ANTISYM_RULE thm1 (conv_then_exists CONSTRUCTOR_CONV ((fst o strip_neg) term') t thm2)
in
	ONCE_DEPTH_CONV (REWR_CONV thm) term
end
end;

(* Takes a thm [h0..hn] |- a0 ==> a1 ==> .. P and returns [a0 /\ a1 /\ ... ==> h0,...] |- a0 ==> a1 ==> P *)
fun DISCH_HYPS thm = 
let	val hs = hyp thm
	val imps = fst (strip_imp (concl thm))
	fun MUNDISCH_ALL thm = 
		if is_imp (concl thm) andalso not (is_neg (concl thm)) then MUNDISCH_ALL (UNDISCH thm) else thm
in
	if null hs orelse null imps then thm else
	foldr (uncurry DISCH) 
		(PROVE_HYP (MUNDISCH_ALL (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] (DISCH_ALL (ASSUME (list_mk_conj imps)))))
			(MUNDISCH_ALL (foldl (fn (h,thm) => MUNDISCH_ALL (MATCH_MP IMP_DISTRIB (DISCH (list_mk_conj imps) (DISCH h thm))))
				(MUNDISCH_ALL thm) hs))) imps
end;

(* Try to prove the term from the assumptions *)
fun exists_proof assums term = 
let	val assums' = zip (map (strip_neg o concl) assums) assums
	val (sterm,count) = strip_neg term
in
	if exists (curry op= (count mod 2) o C (curry op mod) 2 o snd o fst) 
		(filter (can (match_term ((snd o strip_exists) sterm) o snd o strip_exists o fst o fst)) assums')
	then
		tryfind (fn a => MP (DISCH_ALL (CONV_HYP (REWRITE_CONV [NOT_CLAUSES]) (ASSUME term)))
				(CONV_RULE (REWRITE_CONV [NOT_CLAUSES] THENC 
					ONCE_REWRITE_CONV [EXISTS_EQUIV ((fst o fst) a) sterm]) 
			(snd a))) assums'
	else	raise Empty
end

val element_eq = (fn x => fn y => if is_type_judgement x andalso is_type_judgement y then 
			((rand o dest_acl2_true) x = (rand o dest_acl2_true) y) andalso 
			can (match_term ((rator o dest_acl2_true) x)) ((rator o dest_acl2_true) y) else x = y)

fun element_eq_enc x y = 
	(if (is_encoded_term o rand o dest_acl2_true) x andalso (is_encoded_term o rand o dest_acl2_true) y
		then can (match_term ((rator o dest_acl2_true) x) o rator o dest_acl2_true) y
		else element_eq x y) handle _ => element_eq x y

fun LIST_MK_DISJ [] = raise Empty
  | LIST_MK_DISJ [x] = x
  | LIST_MK_DISJ (x::xs) = PURE_REWRITE_RULE [GSYM DISJ_ASSOC] (MATCH_MP MONO_OR (CONJ x (LIST_MK_DISJ xs)))

local	
fun snd_imp x = if ris_imp (concl x) then snd (dest_imp (concl x)) else (concl x)
in
fun TRUE_DISCH L =
	case (split_after (index (not o ris_imp o concl) L) L)
	of (left,[r]) => foldr (uncurry (DISJ2 o snd_imp)) r left
	|  (left,r::rs) => foldr (uncurry (DISJ2 o snd_imp)) (DISJ1 r (list_mk_disj (map snd_imp rs))) left
	|  _ => raise Empty
end

val DNF_CONV = PURE_REWRITE_CONV [GSYM DISJ_ASSOC,GSYM CONJ_ASSOC,
				LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,DE_MORGAN_THM,IMP_DISJ_THM];
fun CONJ_IMPSa ca a b = 
	if ris_imp (concl b) 
		then MATCH_MP MONO_AND (CONJ a b)
		else DISCH ca (CONJ (UNDISCH a) b)

fun CONJ_IMPSb a b =	
	if ris_imp (concl b)
		then DISCH (fst (dest_imp (concl b))) (CONJ a (UNDISCH b))
		else CONJ a b

fun LIST_CONJ_IMPS [] = raise Empty
  | LIST_CONJ_IMPS [x] = x
  | LIST_CONJ_IMPS (x::xs) = 
	if ris_imp (concl x) 
		then CONJ_IMPSa (fst (dest_imp (concl x))) x (LIST_CONJ_IMPS xs)
		else CONJ_IMPSb x (LIST_CONJ_IMPS xs)

fun CONJ_IMPS a b = LIST_CONJ_IMPS [a,b];


(* Remove a truth value from a clause *)
(* [A,A /\ B \/ C] -> [A,B \/ C] *)
(* [A,A \/ B] -> [A] *)
fun prove1 truths s set = 
let	val test = exists_proof truths
	val thms1 = map (fn d => foldr (fn (c,conj) => 
			(CONJ_IMPSb (test c) conj) handle _ => CONJ_IMPSa c (DISCH_ALL (ASSUME c)) conj)
				(test (last d) handle _ => DISCH_ALL (ASSUME (last d))) (butlast d)) s
in
	if all (null o hyp) thms1 then raise Empty
	else 
		(set,TRUE_DISCH thms1) handle e => 
		(insert (map (strip_conj o fst o dest_imp o concl) thms1) set,UNDISCH (LIST_MK_DISJ thms1))
end;

(* Remove negated truth values from a clause *)
(* [A,~A /\ B \/ C] -> [A,C] *)
(* [A,~A \/ B] -> [A,B] *)
local 
fun lmd [] = raise Empty
  | lmd [(false,term)] = (SOME (DISCH_ALL (ASSUME (list_mk_conj term))),hd term)
  | lmd [(true,term)]  = (NONE,list_mk_conj term)
  | lmd ((false,term)::rest) =
	(case (lmd rest)
	of (SOME thm,c) => (SOME (MATCH_MP MONO_OR (CONJ (DISCH_ALL (ASSUME (list_mk_conj term))) thm)),c)
	|  (NONE,tm)  => (SOME (DISCH_ALL (DISJ1 (ASSUME (list_mk_conj term)) tm)),tm))
  | lmd ((true,term)::rest) = 
	case (lmd rest)
	of (SOME thm,c) => (SOME (DISCH_ALL (DISJ2 (list_mk_conj term) (UNDISCH thm))),c)
        |  (NONE,tm)    => (NONE,mk_disj (list_mk_conj term,tm))
in
fun prove2 truths s set =
let	val clauses = zip (map (can (tryfind (exists_proof truths o mk_neg))) s) s
in	
	if exists fst clauses then
		case (lmd clauses)
		of (NONE,_) => raise_error 6 "make_acl2_definition" "Hypothesis set unprovable!!!!"
  		|  (SOME thm,_) => (insert (map snd (filter (not o fst) clauses)) set,UNDISCH thm)
	else	raise Empty
end
end;

(* Removes duplicate conjunctions *)
(* [A /\ A \/ B] --> [A \/ B] *)
local
fun compress1 hs [] = []
  | compress1 hs (c::cs) = 
let	val t1 = exists_proof (map ASSUME (hs @ cs)) c
in	t1::compress1 ((hyp t1) @ hs) cs
end	handle _ => ASSUME c::compress1 (c::hs) cs
in
fun prove3 (truths:thm list) s set = 
let	val proof = map (compress1 []) s
	val s' = map (map (hd o hyp)) proof
	val _ = if all (op= o (length ## length)) (zip s' s) then raise Empty else ()
	val proof1 = map (PURE_REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC] o DISCH_ALL o LIST_CONJ) proof
in
	(insert s' set,UNDISCH (LIST_MK_DISJ proof1))
end
end;

(* Remove type judgements *)
local
	fun list_conj L = PURE_REWRITE_RULE [GSYM CONJ_ASSOC] (LIST_CONJ_IMPS L)
in
fun prove4 proved noproved truths s set = 
let	val assums = truths @ (!function_judgements) @ (CONJUNCTS JUDGEMENT_THMS);
	val count = ref 0
	val thms = 
		map (map (fn x => 
			if is_type_judgement x then 
				((tryfind (DOUBLE_MATCH I (rator o dest_acl2_true) x) (!proved)) before (count := (!count) + 1)) handle e => 
				(first (element_eq_enc x o concl) (!noproved)) handle e =>
				(proved := (SEXP_TYPE_TERM_AS assums x) :: (!proved) ; count := (!count) + 1 ; hd (!proved)) handle e =>
				(noproved := (ASSUME x) :: (!noproved) ; hd (!noproved))
			else ASSUME x)) s
	val truth_terms = map concl truths
	fun disch_all thm = foldr (uncurry DISCH) thm (set_diff (hyp thm) truth_terms)
in
	if (!count) = 0 then raise Empty
	else
		let 	val thms2 = map (list_conj o map (PURE_REWRITE_RULE [AND_IMP_INTRO] o disch_all)) thms
		in	
			(set,TRUE_DISCH thms2) handle _ =>
			(insert ((map (flatten o map (C set_diff truth_terms o hyp)) thms)) set,UNDISCH (LIST_MK_DISJ thms2))
		end
end
end;

fun mappluck f [] = []
  | mappluck f (x::xs) =
	(f x,xs)::(map (I ## cons x) (mappluck f xs)) handle e => (map (I ## cons x) (mappluck f xs))

fun match_term_exists t1 t2 = 
	match_term ((snd o strip_exists o fst o strip_neg) t1) ((snd o strip_exists o fst o strip_neg) t2) 

local
fun find_match [] s = []
  | find_match (t::ts) s = 
let	val matches = mappluck (tryfind (match_term_exists t)) s
in
	tryfind (fn (m,s') => m::find_match (map (inst_subst m) ts) s') matches
end;
in
fun get_nchot s nchot = 
let	val disjs = (strip_disj o concl) nchot
	val nchot' = foldl (uncurry INST_TY_TERM) nchot (find_match disjs s)
in
	DISJ_CASES_UNIONL nchot' 
		(map (fn d => tryfind (exists_proof [ASSUME d]) (flatten s)) ((strip_disj o concl) nchot'))
end
end

fun DISJ_LIST_CONV [] term = ALL_CONV term
  | DISJ_LIST_CONV [c] term = c term
  | DISJ_LIST_CONV (c::cs) term = 
let	val (a,b) = dest_disj term
in
	let 	val next = DISJ_LIST_CONV cs b
	in	MK_COMB (AP_TERM disjunction (c a),next) handle UNCHANGED => AP_TERM (mk_comb(disjunction,a)) next
	end
	handle UNCHANGED => AP_THM (AP_TERM disjunction (c a)) b
end;

fun ncombs [] = [[]]
  | ncombs (x::xs) = flatten (map (fn y => map (cons y) (ncombs xs)) x)

(* Converts a theorem of the form [t0,t1,...,A] |- B to [t0,t1,...,A' \/ B] |- B *)
fun ADD_HYPOTHESIS truth_terms s thm =
let	val s1 = map strip_conj (strip_disj (first (not o C mem truth_terms) (hyp thm)))
	val s2 = map list_mk_conj (filter (fn cs1 => not (exists (all (C (op_mem (fn a => can (exists_proof [ASSUME a]))) cs1)) s)) s1)
	val s3 = filter (fn cs1 => not (is_type_judgement cs1) orelse 
			not (exists (element_eq cs1) (filter is_type_judgement (map list_mk_conj s)))) s2
	val thm_remove = 
		UNDISCH (
			(uncurry (C (foldr (fn (a,thm) => if mem a s3 then MATCH_MP MONO_OR (CONJ (DISCH_ALL (ASSUME a)) thm) else DISCH_ALL (DISJ2 a (UNDISCH thm))))))
			((I ## DISCH_ALL o (fn a => DISJ1 (ASSUME (hd a)) (list_mk_disj (tl a)) handle e => ASSUME (hd a)))
			(split_after (index (curry op= (last s3)) (map list_mk_conj s1)) (map list_mk_conj s1))))
in
	((map strip_conj s3) @ s,UNDISCH (CONV_RULE (	LAND_CONV (PURE_REWRITE_CONV [GSYM DISJ_ASSOC]) THENC 
				RAND_CONV (REWR_CONV DOUBLE_OR ))
	(MATCH_MP MONO_OR (CONJ (DISCH (list_mk_disj s3) (PROVE_HYP thm_remove thm)) 
		(DISCH_ALL (ASSUME (list_mk_disj (map list_mk_conj s))))))))
end;

fun add_result truth_terms [] s set = raise Empty
  | add_result truth_terms (thms::rest) s set =
let	fun disch_all thm = foldr (uncurry DISCH) thm (set_diff (hyp thm) truth_terms)
	val thm1 = CONV_RULE DNF_CONV (RUNDISCH_ALL (LIST_CONJ_IMPS thms))
	val disjs = (strip_disj o concl) thm1
	val thm2 = CONV_RULE (DISJ_LIST_CONV 
			(map (fn d => tryfind (REWR_CONV o CONV_RULE bool_EQ_CONV o AC_CONV (CONJ_ASSOC,CONJ_COMM) o 
						curry mk_eq d o list_mk_conj) s) disjs)) thm1
	val disjs' = (strip_disj o concl) thm2
	val thm3 =
		(fn thm => CONV_RULE (REWR_CONV (CONV_RULE bool_EQ_CONV 
			(AC_CONV (DISJ_ASSOC,DISJ_COMM) (mk_eq(concl thm,list_mk_disj (map list_mk_conj s)))))) thm)
			(foldr (uncurry DISJ2) thm2 (set_diff (map list_mk_conj s) disjs'))
in
	if null (set_diff (hyp thm3) truth_terms) then (set,thm3) else
	let 	val (s'',jthm) = ADD_HYPOTHESIS truth_terms s thm3
	in
		(I ## C PROVE_HYP jthm) (add_result truth_terms rest s'' set) handle e => (insert s'' set,jthm)
	end	handle e => add_result truth_terms rest s set
end;

(* P ==> A x \/ B x, [A x /\ S0 \/ B x /\ S1] and S0 < S1 ---> [A x /\ S0 \/ P /\ S1 \/ B x /\ S1] *)
fun match_nchot sb [] = []
  | match_nchot sb (d::ds) =
let	val matches = mappluck (fn s => 
			let	val m1 = match_term_exists d s
				val m2 = match_term d s
			in	(m1,exists_proof [ASSUME (inst_subst m1 d)] s) handle e => (m2,exists_proof [ASSUME (inst_subst m2 d)] s) end) sb
in
	tryfind (fn ((m,p),sb') => map (INST_TY_TERM m) (p::match_nchot sb' ds)) matches
end;

fun rmatch nchot thm =
	MP thm (INST_TY_TERM (match_term (concl nchot) (fst (dest_imp (concl thm)))) nchot);

fun MAP_DISJ_CONV [] term = ALL_CONV term
  | MAP_DISJ_CONV [c] term = c term
  | MAP_DISJ_CONV (c::cs) term = 
let	val (a,b) = dest_disj term
in
	MK_COMB (AP_TERM disjunction (c a),MAP_DISJ_CONV cs b) handle UNCHANGED =>
	AP_THM (AP_TERM disjunction (c a)) b handle UNCHANGED =>
	AP_TERM a (MAP_DISJ_CONV cs b)
end;

fun diff xs [] = xs
  | diff xs (y::ys) = diff (snd (pluck (curry op= y) xs)) ys handle _ => diff xs ys;

fun fix_extra [] = []
  | fix_extra (e1::es) = 
let	val (e2,es') = pluck (curry op= ((lhs o concl) e1) o hd o strip_disj o rhs o concl) es
in
	fix_extra ((RIGHT_CONV_RULE (LAND_CONV (REWR_CONV e2)) e1)::es')
end	handle e => e1::fix_extra es;

fun disj_conj_match opr thm1 thm2 =
let	val cconv = CONV_RULE bool_EQ_CONV o AC_CONV(CONJ_ASSOC,CONJ_COMM)
	val dconv = CONV_RULE bool_EQ_CONV o AC_CONV(DISJ_ASSOC,DISJ_COMM)
	val t1 = opr (concl thm1)
	val t2 = opr (concl thm2)	
	val t1cs = strip_disj t1
	val t2cs = strip_disj t2
	val conj_rewrite = map (fn t1c => tryfind (cconv o curry mk_eq t1c) t2cs) t1cs
	val extra = diff t2cs (map (rhs o concl) conj_rewrite)
	val extra' =
		fix_extra (map (fn e => tryfind (fn c => 
			RIGHT_CONV_RULE (RAND_CONV (REWR_CONV (cconv (mk_eq((rhs o concl) c,e)))))
				(GSYM (SPEC ((rhs o concl) c) DOUBLE_OR))) conj_rewrite) extra);
	val conj_rewrite' = 
		map (fn c => first (curry op= ((lhs o concl) c) o lhs o concl) extra' handle e => c) conj_rewrite;
	val thm = (REWRITE_CONV [GSYM DISJ_ASSOC] THENC MAP_DISJ_CONV (map REWR_CONV conj_rewrite')) t1
	val remove = fix_extra 
			(map (GSYM o C SPEC DOUBLE_OR) (diff (strip_disj (rhs (concl thm))) t2cs))
	val remove' = map (fn t2c => first (curry op= t2c o lhs o concl) remove handle e => REFL t2c) t2cs
	val thm' = TRANS thm (dconv (mk_eq((rhs o concl) thm,list_mk_disj (map (rhs o concl) remove'))))
in
	RIGHT_CONV_RULE (MAP_DISJ_CONV (map (REWR_CONV o GSYM) remove')) thm'
end

(* Here we are keeping X,Y and losing Z *)
fun make_subset (left as (d0,s0)::d0s) (right as (d1,s1)::d1s) =
let	val proofs_l = map (map (exists_proof (map ASSUME s0)) o snd) left
	val proofs_r = map (map (exists_proof (map ASSUME (s0 @ s1))) o snd) right
	val list_l = map (total (LIST_CONJ_IMPS o map DISCH_ALL)) proofs_l
	val list_r = map (LIST_CONJ_IMPS o map DISCH_ALL) proofs_r;
	
	val out_terms = set_diff (mk_set (flatten (map (strip_conj o fst o dest_imp o concl) list_r))) s0;

	val thmr = 
		LIST_MK_DISJ 
			((DISCH (list_mk_disj (map (fst o dest_imp o concl) list_r))
			(PURE_REWRITE_RULE [	LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR] 
				(CONJ (ASSUME (list_mk_disj (map fst right))) (UNDISCH (LIST_MK_DISJ list_r))))) ::
			(map2 (fn SOME x => (fn (a,_) => CONJ_IMPS (DISCH a (ASSUME a)) x)
				| NONE   => (fn (a,_) => DISCH a (ASSUME a))) list_l left));

	val thml_1 = (fn x => CONJ_IMPS (DISCH_ALL (ASSUME (list_mk_conj s0))) x handle e => x)
			(DISCH (mk_disj(list_mk_conj out_terms,list_mk_disj (map fst left))) 
				(ASSUME (list_mk_disj (map fst left))))
	val thml_2 = 
		CONV_RULE (PURE_REWRITE_CONV [LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR])
			(DISCH ((fst o dest_imp o concl) thml_1) 
			(DISJ2 (list_mk_disj (map (list_mk_conj o op::) right)) (UNDISCH thml_1)))
	val thml = CONV_RULE (	LAND_CONV (REWR_CONV (disj_conj_match (fst o dest_imp) thml_2 thmr)) THENC
			RAND_CONV (REWR_CONV (disj_conj_match (snd o dest_imp) thml_2 thmr))) thml_2
in
	DISJ_CASES (CONV_HYP (PURE_REWRITE_CONV [GSYM DISJ_ASSOC]) (ASSUME (list_mk_disj ((hyp thml) @ (hyp thmr)))))
		thml thmr
end
  | make_subset _ _ = raise Empty;

local
fun all_lists [] = [[]]
  | all_lists ([]::ys) = []
  | all_lists ((x::xs)::ys) = 
	(map (cons x) (all_lists ys)) @ (all_lists (xs::ys))
fun part_lists p acc [] = p::acc
  | part_lists (c1,c2) acc (x::xs) = part_lists (x::c1,c2) (part_lists (c1,x::c2) acc xs) xs
in
fun find_subset [] = raise Empty
  | find_subset ([]::ys) = raise Empty
  | find_subset ((x::xs)::ys) =
	tryfind (tryfind (uncurry make_subset) o part_lists ([],[]) [] o curry op:: x) (all_lists ys) handle e =>
	find_subset (xs::ys)
end;
	
fun fst_imp term = if is_imp term andalso not (is_neg term) then fst (dest_imp term) else term

fun subset xs ys = all (C mem ys) xs;

fun adjust_thm truths thm s = 
let	val p = hd (hyp thm)
	val thm' = CONV_HYP (PURE_REWRITE_CONV [SPEC p LEFT_AND_OVER_OR,SPEC p RIGHT_AND_OVER_OR])
			(UNDISCH (PURE_REWRITE_RULE [AND_IMP_INTRO] (DISCH_ALL thm)));
	val sterm = list_mk_disj (map list_mk_conj s)
	val split_thm = map strip_conj (strip_disj (concl thm'))
	val thm'' = foldl (uncurry (DISJ2 o list_mk_conj)) thm'
			(filter (not o C (op_mem set_eq) split_thm) s)
in
	ADD_HYPOTHESIS truths s 
			(CONV_HYP DNF_CONV (CONV_RULE (REWR_CONV (disj_conj_match I thm'' (ASSUME sterm))) thm''))
end;

fun term_dnf [] = raise Empty
  | term_dnf [x] = strip_disj (concl x)
  | term_dnf (x::xs) = 
	flatten (map (fn x => map (curry mk_conj x) (term_dnf xs)) (strip_disj (concl x)))

fun add_nchot truth_terms nchot s =
let	val split_nchot = term_dnf nchot
	val disjs = map strip_conj split_nchot
	val sets = 
		flatten (map (fn d => map (pair (list_mk_conj d) o snd) (filter (set_eq d o fst)
			(mapfilter (fn c => partition (C mem (first (C subset c) disjs)) c) s))) disjs)
	val thm1 = 	LIST_MK_DISJ (map (fn d => DISCH_ALL (ASSUME 
			(fst (first (fn (a,b) => (a = d) andalso null b) sets)))) split_nchot) handle e =>
			find_subset (map (fn d => filter (curry op= d o fst) sets) split_nchot)

	val thm2 = foldl (uncurry (DISJ2 o list_mk_conj)) (UNDISCH thm1) s;

	val thm3 = (CONV_RULE (REWR_CONV (disj_conj_match I thm2 (ASSUME (list_mk_disj (map list_mk_conj s))))) thm2)
	
	val nchot' = PURE_REWRITE_RULE [LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,GSYM CONJ_ASSOC,GSYM DISJ_ASSOC] (LIST_CONJ nchot)
	
	val thm4 = DISCH_ALL (foldl (uncurry DISCH) thm3 
			(op_set_diff (curry (uncurry set_eq o (strip_disj ## strip_disj))) (hyp thm3) [concl nchot']))
	val nchot'' =
		INST (map (fn v => v |-> variant (free_varsl (flatten s)) v) 
				(set_diff (free_varsl (hyp nchot')) (free_vars (concl nchot')))) nchot'

	val thm5 = MP (CONV_RULE (LAND_CONV (REWR_CONV (disj_conj_match fst_imp thm4 nchot''))) thm4) nchot''
in
	if is_imp (concl thm5) 
		then (SOME ## I) (
			if null (op_set_diff element_eq (hyp (UNDISCH thm5)) truth_terms)
				then ((map strip_conj o strip_disj o fst o dest_imp o concl) thm5,UNDISCH thm5)
				else (adjust_thm truth_terms thm5 s))			
		else 
		(if null (op_set_diff element_eq (hyp thm5) truth_terms) then (NONE,thm5) 
			else (SOME ## I) (ADD_HYPOTHESIS truth_terms s thm5))
end;

fun add_all_nchots truth_terms s set []= raise Empty
  | add_all_nchots truth_terms s set (nchot::nchots) = 
	(case (add_nchot truth_terms nchot s)
	of (NONE,thm) => (set,thm)
	|  (SOME s',thm) => 
		((I ## C PROVE_HYP thm) (add_all_nchots truth_terms s' set nchots) handle _ => (s'::set,thm)))
	handle _ => add_all_nchots truth_terms s set nchots;

fun fix_nchot_set [] = true
  | fix_nchot_set (x::xs) = 
let	val find = first is_type_judgement o hyp
	val matches = filter (curry op= ((rand o dest_acl2_true o find) x) o rand o dest_acl2_true o find) xs
in
	all (curry op= (find x) o find) matches andalso fix_nchot_set xs
end	handle e => null (hyp x)

fun all_combs c acc [] = if null c then acc else c::acc
  | all_combs c acc (x::xs) = 
	if fix_nchot_set (x::c) then all_combs (x::c) (all_combs c acc xs) xs else all_combs c acc xs;

fun prove9 noproved truths s set =
let	val vars = mk_set (mapfilter (lhs o snd o strip_exists o fst o strip_neg) (flatten s))
	val s_bagged = 
		map (fn v => flatten (map (filter (fn x => (curry op= v o lhs o snd o 
					strip_exists o fst o strip_neg) x handle e => false)) s)) vars
	val nchots = (SPEC_ALL EXCLUDED_MIDDLE) :: 
			mapfilter (UNDISCH o SPEC_ALL o valOf o #nchotomy_thm o snd) (!proofs)
	
	val matched_thms = flatten (map (fn sb => mapfilter (fn nchot => 
		rmatch nchot ((LIST_MK_DISJ o map DISCH_ALL o 
				match_nchot sb o strip_disj o concl) nchot)) nchots) s_bagged);
	
	val matched_thms' = filter (not o exists (C (op_mem element_eq_enc) 
					(map concl (!noproved))) o hyp) matched_thms
	
	val nchots = all_combs [] [] matched_thms'
in
	(add_all_nchots (map concl truths) s set nchots)
end;
 
(* Everything in s matched by something in t *)
fun match_conjunction ts found [] = [([],rev (map (fn (a,b) => exists_proof [ASSUME a] b) found))]
  | match_conjunction ts found (d1::s) = 
let	val matches = mapfilter (fn t => (t,match_term_exists t d1)) ts
in
	flatten (mapfilter (fn (t,m) => 
		(map (cons m ## I) (match_conjunction (map (inst_subst m) ts) 
			(map (inst_subst m ## I) ((t,d1)::found)) s))) matches)
end;

(* Everything in t matched by something in s *)
fun match_disjunction s [] = []
  | match_disjunction s (t::ts) = 
let	val matches = flatten (map (match_conjunction t []) s)
in
	tryfind (fn (mlist,proof_list) => 
		DISCH_ALL (foldl (uncurry PROVE_HYP) (LIST_CONJ proof_list) 
			(CONJUNCTS (ASSUME (foldr (uncurry inst_subst) (list_mk_conj t) mlist))))
		:: match_disjunction s (map (map (C (foldr (uncurry inst_subst)) mlist)) ts)) matches
end;

fun make_disj [] = raise Empty
  | make_disj [(SOME t,_)] = DISCH_ALL (ASSUME t)
  | make_disj ((NONE,t)::ts) = DISCH_ALL (DISJ2 t (UNDISCH (make_disj ts)))
  | make_disj ((SOME t,_)::ts) = 
	MATCH_MP MONO_OR (CONJ (DISCH_ALL (ASSUME t)) (make_disj ts)) handle e =>
	DISCH_ALL (DISJ1 (ASSUME t) (list_mk_disj (map snd ts)))

(* Whole disjunctions match the theorem *)
fun prove5_1 truths s set thm = 
let	val s' = map strip_conj (strip_disj (concl thm))
	val match = match_disjunction s s'
	val term_match = list_mk_disj (map (fst o dest_imp o concl) match)
	val thm_match = MATCH_MP (LIST_MK_DISJ match) (INST_TY_TERM (match_term (concl thm) term_match) thm)
	
	val term_match = UNDISCH (make_disj (map (fn cs => 
		(total (first (curry op= cs)) (mapfilter (snd o dest_imp o concl) match),cs)) (map list_mk_conj s)))

	val term = hd (hyp term_match);
	
	val thm_match_ordered = CONV_RULE (REWR_CONV (CONV_RULE bool_EQ_CONV 
					(AC_CONV (DISJ_ASSOC,DISJ_COMM) (mk_eq(concl thm_match,term))))) thm_match

	val full_match = 
		CONV_RULE (RAND_CONV DNF_CONV) 
			(PURE_REWRITE_RULE [AND_IMP_INTRO] (DISCH_ALL (PROVE_HYP thm_match_ordered term_match)))
	
	val hs = map strip_conj (strip_disj (fst (dest_imp (concl full_match)))) handle e => []
	val (s',j_thm) = if null hs 
		then ([],TRUTH)
		else prove1 truths hs [] handle e => ([hs],ASSUME (list_mk_disj (map list_mk_conj hs)))

	val final_thm = MATCH_MP full_match j_thm handle e => full_match
in
	if null s'	then (set,final_thm)
			else (C cons set ## I) (ADD_HYPOTHESIS (map concl truths) s final_thm)
end;

fun prove5 ethms truths s set =
	tryfind (prove5_1 truths s set) ethms

fun free_proof1 s term = 
let	val (l,r) = split_after (index (curry op= term) s) s
in
	foldr (uncurry (DISJ2 o list_mk_conj))
		(case (tl r)
		of [] => ASSUME (hd (hd r))
		|  xs => DISJ1 (ASSUME (hd (hd r))) (list_mk_disj (map list_mk_conj xs))) l
end

fun free_proof2 s term = 
let	fun disch_but thm = foldl (uncurry DISCH) thm (set_diff (hyp thm) (map mk_neg term));
	val count = ref 0;
	val clauses = map (fn c => 
		(let 	val x = tryfind (exists_proof (map (ASSUME o mk_neg) term)) c
			val _ = count := (!count) + 1
		in	disch_but (foldl (uncurry PROVE_HYP) (LIST_CONJ (map ASSUME c)) 
				(x::CONJUNCTS (ASSUME (list_mk_conj (set_diff c [concl x])))))
		end) handle e => disch_but (ASSUME (list_mk_conj c))) s
in
	if !count = 0 then raise Empty else 
	(NONE,TRUE_DISCH clauses) handle e =>
	(SOME (map (strip_conj o fst o dest_imp o concl) clauses),UNDISCH (LIST_MK_DISJ clauses))
end;

fun free_proof3 s term = 
let	val (s',p2) = free_proof2 s term
in	
	(s',DISJ_CASES (SPEC (list_mk_conj term) EXCLUDED_MIDDLE) (free_proof1 s term) p2)
end;

fun free_proofs s [] = raise Empty
  | free_proofs s (x::xs) = 
let	val (next,thm) = free_proof3 s x
in
	case next 
	of SOME s' => ((I ## C PROVE_HYP thm) (free_proofs s' xs) handle e => (SOME s',thm))
        |  NONE    => (NONE,thm)
end	handle e => free_proofs s xs

(* Remove the negation of any 'free' disjunction from other conjunctions *)
(* [A \/ ~A /\ B] --> [A \/ B] *)
fun prove6 (truths:thm list) s set = 
	case (free_proofs s (filter (curry op= 1 o length) s))
	of (SOME s,thm) => (s::set,thm)
	|  (NONE,thm)   => (set,thm);

(* Encode terms and rewrite using car / cdr *)
fun prove7 (truths:thm list) s set = 
let	val thm = DEPTH_CONV (REWRITE_CONV (car_def::cdr_def::gsym_car_cdr_thms) 
			THENC TRY_CONV CONSTRUCTOR_CONV) (list_mk_disj (map list_mk_conj s));
in
	(insert ((map strip_conj o strip_disj o rhs o concl) thm) set,UNDISCH (snd (EQ_IMP_RULE thm)))
end

(* Rewrite terms with the recursive condition *)
(* [A acl2 /\ B \/ C] - [P acl2 /\ A hol /\ B \/ A acl2 /\ B] *)
fun prove8 NONE truths s set = raise Empty
  | prove8 (SOME stage4) (truths:thm list) s set = 
let	fun disch_but thm = foldl (uncurry DISCH) thm (filter (not o is_definition) (hyp thm))
	fun s4conv term = RUNDISCH_ALL (PART_MATCH (lhs o snd o rstrip_imp) (disch_but (GSYM stage4)) term)
	fun fix thm = 
		CONV_RULE (RAND_CONV (REWR_CONV DOUBLE_OR))
			(MATCH_MP MONO_OR (CONJ 
				(REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC] (disch_but (snd (EQ_IMP_RULE thm))))
				(DISCH_ALL (ASSUME (lhs (concl thm))))))
	val modified = map ((fn x => (fix o DEPTH_CONV s4conv) x handle _ => DISCH_ALL (ASSUME x)) o list_mk_conj) s;
	val s' = map (strip_conj) (flatten (map (strip_disj o fst o dest_imp o concl) modified))
	val extra = map (filter (not o is_type_judgement)) s'
in
	if exists (fn c' => not (exists (fn c => all (C mem c) c') s)) extra then
		(insert s' set,UNDISCH (LIST_MK_DISJ modified))
	else raise Empty
end;

local
exception Debug of string
fun tryfind f [] = raise (mk_HOL_ERR "Lib" "tryfind" "all applications failed")
  | tryfind f (x::xs) = 
		(f x) handle (Debug x) => raise (Debug x) | _ => tryfind f xs;
fun repeat f x = repeat f (f x) handle (Debug y) => raise (Debug y) | _ => x;
fun limit 0 f x = x
  | limit n f x = limit (n - 1) f (f x) handle (Debug y) => raise (Debug y) | _ => x
val split = map strip_conj o strip_disj
fun check2 a thm =
	if null (hyp thm) orelse (list_mk_disj (map list_mk_conj (split (hd (hyp thm)))) = (hd (hyp thm))) then ()
	else raise (Debug ("Prover: " ^ (int_to_string a) ^ " not returning DNF!"))
fun check1 truths s a set thm =
let	val set' = map split (set_diff (hyp thm) (map concl truths))
	fun printlist [] = print "]\n"
	  | printlist [s] = (print_term (list_mk_disj (map list_mk_conj s)) ; print "]\n")
	  | printlist (s::ss) = 
		(print "``" ; print_term (list_mk_disj (map list_mk_conj s)) ; print "``" ; print "," ; printlist ss);
	fun plist x = (print "[" ; printlist x)
in
	if set_eq set set' then thm else 
		(print_term (list_mk_disj (map list_mk_conj s)) ; print "\n\n" ;raise (Debug ("Prover: " ^ (int_to_string a) ^ " munged the set!")))
end
fun tryproofs truths fs L _ (thm,[]) = raise Empty
  | tryproofs truths fs L [] (thm,s::set) = tryproofs truths (s::fs) L L (thm,set)
  | tryproofs truths fs L ((a,f)::funs) (thm,s::set) =
let	val (set',jthm) = f truths s set
	val _ = check2 a jthm
	val _ = fprint_trace 1 ((int_to_string a) ^ "#")
	val match = filter (fn (a,b) => not (null a andalso null b)) 
			(map (uncurry match_term) (zip (map list_mk_conj s) (strip_disj (concl jthm))));
	val matched = foldr (uncurry INST_TY_TERM) thm match
	val (set'',fs') = if null match then (set',fs) else
			(map (map (map (C (foldr (uncurry inst_subst)) match))) set',
			map (map (map (C (foldr (uncurry inst_subst)) match))) fs)
	val _ = if not (mem (concl jthm) (hyp matched)) then raise (Debug ("Prover: " ^ (int_to_string a) ^ " produced a theorem not relating to: " ^ (term_to_string (list_mk_disj (map list_mk_conj s))))) else ()
	val next = check1 truths s a (fs' @ set'') (PROVE_HYP jthm matched)
in
	case set''
	of (s'::set''') => (tryproofs truths fs' L L (next,s'::set''') 
				handle (Debug x) => raise (Debug x) | _ => (next,s'::set'''))
	|  [] => (next,(rev fs') @ set'')
end	handle (Debug x) => raise (Debug x) | _ => tryproofs truths fs L funs (thm,s::set)
in
fun augment_hypothesis stage4 extra_thms thm =
let	val _ = fprint_trace 1 "Resolving hypothesis set: "
	val thm' = CONV_HYP (DNF_CONV THENC REWRITE_CONV (car_def::cdr_def::gsym_car_cdr_thms)) thm
	val thm'' = FOLD_HYP split_hyp thm'
	val truths = map ASSUME (filter (not o is_disj) (hyp thm''))
	val ethms = map (CONV_HYP DNF_CONV o RUNDISCH_ALL o REWRITE_RULE [AND_IMP_INTRO]) extra_thms
	val hs = set_diff (hyp thm'') (map concl truths)
	val proved = ref []
	val noproved = ref []
	val functions = enumerate 1 [	prove1,prove2,prove3,prove4 proved noproved,
					prove5 ethms,prove6,prove7,prove8 stage4,prove9 noproved]
in
	(fst (repeat (tryproofs truths [] functions functions) (thm'',map split hs)))
	before (fprint_trace 1 "\n")
end
end;

(****************************************************************************)
(* replace_constructed: replaces constructed terms with decoded sexps       *)
(****************************************************************************)

fun replace_constructed thm = 
let	val constructed_terms = 
		filter (not o null o free_vars) 
			(op_mk_set free_in (find_terms (is_constructor o repeat rator) (concl thm)))
	val rewrite_terms = 
		map (fn x => (type_of x,mk_eq(mk_comb(get_decode_term (type_of x),genvar sexp_type),x))) constructed_terms
	val destructed = 
		flatten (map (fn (t,x) => 
			DESTRUCTORS (CONV_RULE (FORK_CONV (REWR_CONV
				(MATCH_MP (get_decode_encode_thm t) 
					(ASSUME (mk_acl2_true (mk_comb (get_detect_term t,(rand o lhs) x))))),
				CONSTRUCTOR_CONV))
			(AP_TERM (get_encode_term t) (ASSUME x)))) rewrite_terms)
	val thm' = REWRITE_RULE destructed (REWRITE_RULE (map (GSYM o ASSUME o snd) rewrite_terms) thm)
in
	CONV_HYP (TRY_CONV NCHOT_HOL_ACL2) (foldl (fn (h,thm) => if is_eq h then 
		CHOOSE_L ((free_vars_lr o rhs) h,ASSUME (list_mk_exists((free_vars_lr o rhs) h,h))) thm else thm)
		thm' (hyp thm'))
end

(****************************************************************************)
(* replace_free_hol: replaces free hol variables with decoded sexpressions  *)
(****************************************************************************)

fun replace_free_hol thm = 
	CONV_HYP (TRY_CONV NCHOT_HOL_ACL2) (CONV_RULE (DEPTH_CONV NCHOT_HOL_ACL2)
		(INST (map (fn x => x |-> mk_comb(get_decode_term (type_of x),genvar sexp_type)) (filter (not o curry op= sexp_type o type_of) (free_vars_lr (concl thm)))) thm))
	
fun make_ho_encoder name hol_type =
let	val term = foldl (fn (x,t) => 
		let 	val var = variant (free_vars t) (mk_var("x",sexp_type))
		in      mk_comb(t,mk_comb(get_decode_term x,var))
		end)
			(mk_var(name,hol_type)) 
			(fst (strip_fun hol_type))
	val term' = if null ((snd o strip_comb) term) then term else 
			mk_cond(	list_mk_conj(map (fn x => mk_acl2_true(mk_comb((get_detect_term o type_of) x,rand x))) ((snd o strip_comb) term)),
					term,
					list_mk_comb(repeat rator term,map (rand o add_default_value_hol o get_encode_term o type_of) ((snd o strip_comb) term)))
in
	list_mk_abs((map rand o snd o strip_comb) term,mk_comb((get_encode_term o snd o strip_fun) hol_type,term'))
end;

(* Not the right way to go about things at all .... *)
fun remove_missing_cases NONE types thm = thm
  | remove_missing_cases (SOME ca) types thm = 
let	val terms = (map lhs o strip_conj o concl) ca;
	val vars = free_varsl terms;
	val (neg_terms,pos_terms) = partition (can (match_term ``|= not a``)) terms
	val p_terms = find_terms (fn x => is_acl2_cond x andalso exists (C free_in (((fn (a,b,c) => a) o dest_acl2_cond) x)) vars) (concl thm);
	val nchotomys = mapfilter (fn t => tryfind (CONV_RULE (EVERY_DISJ_CONV NCHOTOMY_TO_EQUAL_CONV) o C MATCH_MP (ASSUME t) o SPEC_ALL o valOf o #nchotomy_thm o snd) (!proofs)) types;

	val neg_terms' = map (UNDISCH o fst o EQ_IMP_RULE o (RAND_CONV (REWR_CONV not_def) THENC REWRITE_CONV [ite_def,TRUTH_REWRITES])) neg_terms
	val pos_terms' = map ASSUME pos_terms
	val all_terms = flatten [filter (not o is_disj o concl) (map (REWRITE_RULE neg_terms') nchotomys),neg_terms',pos_terms']
in
	REWRITE_RULE (filter (not o is_cond o rhs o concl) (map (REWR_CONV ite_def THENC REWRITE_CONV (TRUTH_REWRITES::all_terms)) p_terms)) thm
end

local
val not_rewr = GSYM (REWRITE_CONV [not_def,ite_def,TRUTH_REWRITES] ``|= not a``); 
fun carg L NONE = L
  | carg L (SOME converted_arg) = foldl (fn (c,l) => ((dest_acl2_true o lhs) c :: l)) L ((strip_conj o concl) converted_arg)
fun gPt Pterm terms converted_missing constraint_theorems_converted = 
let 	val ctc_remove = flatten (map (strip_disj o snd o rstrip_imp o concl) constraint_theorems_converted)
	val cmissing = map (rhs o concl) (filter (not o C (op_mem aconv) ctc_remove o lhs o concl) (map snd converted_missing))
	val new_list = 
		case (map (curry mk_comb ``not`` o dest_acl2_true) cmissing)
		of [] => rev terms
		|  L  => rev (mk_comb(``not``,mk_comb(``andl``,mk_list(L,sexp_type)))::terms)
in
	list_mk_abs(snd (strip_comb (dest_acl2_true Pterm)),mk_comb(``andl``,mk_list (new_list,sexp_type)))
end
in
fun generatePterm Pterm types ca converted_missing constraint_theorems_converted = 
	gPt Pterm (carg (map (fn x => dest_acl2_true x handle e => mk_comb(``bool``,x)) types) ca) converted_missing constraint_theorems_converted
end;

fun make_decode_encode_ho_thm term = 
let	val (quants,body) = strip_abs term
	val cases = ((fn (a,b,c) => a) o dest_cond o rand) body
	val terms = (snd o strip_comb o rand o (fn (a,b,c) => b) o dest_cond o rand) body
	val dec_encs = map2 (fn x => UNDISCH o SPEC ((rand o rand) x)) terms (map (get_decode_encode_thm o type_of o rand) terms)
	
	val true_thm = REWRITE_CONV (ASSUME cases::dec_encs) body;

	val fthm1 = CONV_HYP (REWRITE_CONV [DE_MORGAN_THM]) (REWRITE_CONV [ASSUME (mk_neg cases)] body);
	val false_thm = RIGHT_CONV_RULE (REWRITE_CONV [GSYM (MATCH_MP (ASSUME (list_mk_forall(quants,mk_imp(hd (hyp fthm1),
				mk_eq((rand o rand o rhs o concl) true_thm,(rand o rand o rhs o concl) fthm1))))) (ASSUME (hd (hyp fthm1))))]) fthm1;
in
	CONV_RULE (DEPTH_CONV ETA_CONV) (foldr (uncurry ABS) 
		(TRANS 	(DISJ_CASES (SPEC (hd (hyp true_thm)) EXCLUDED_MIDDLE) true_thm false_thm)
			(MATCH_MP ((get_decode_encode_thm o type_of o rand) body) 
				(SPEC_ALL (ASSUME (list_mk_forall(quants,mk_acl2_true (mk_comb((get_detect_term o type_of o rand) body,((rand o rand o rhs o concl) true_thm))))))))) quants)
end handle e => UNDISCH (PART_MATCH (lhs o snd o strip_imp) ((get_decode_encode_thm o type_of o rand) term) term);


fun make_judgement converted_arg recursive extra_thms correct' =
let	val vars = (fst o strip_forall o concl) correct'
	val svars = map make_acl2_var vars
	val thm1 = BETA_RULE (SPECL svars correct')
	val term = (rand o lhs o snd o strip_imp o concl) thm1;
	val thm2 = DISCH_AND_CONJ (ONCE_REWRITE_RULE [UNDISCH_ALL thm1] (SPEC term ((get_detect_encode_thm o type_of) term)));
	val thm3 = GENL (free_varsl svars) (REWRITE_RULE [ANDL_REWRITE,NOT_REWRITE] (DISCH_AND_CONJ ((clean_hyp_set o 
				REWRITE_RULE (mapfilter (GSYM o valOf) [converted_arg]) o
				REWRITE_RULE ((map make_decode_encode_ho_thm o snd o strip_comb o rand o dest_acl2_true o snd o strip_imp o concl) thm2)) thm2)));
	val ho_assumptions = filter (fn x => is_forall x andalso (is_imp o snd o strip_forall) x) 
					((strip_conj o fst o dest_imp o concl) (PART_MATCH (rand o dest_acl2_true o snd o strip_imp) thm3 ((lhs o concl o SPEC_ALL) recursive))) handle e => []
	val detector = (get_detector o type_of o rand o lhs o snd o strip_imp o snd o strip_forall o concl) correct'
	val _ = fprint_trace 1 "Typing function body: "
	val res = (REWRITE_RULE [GSYM recursive] 
		(PROVE_TYPE_JUDGEMENT (thm3::(flatten [extra_thms,map ASSUME ho_assumptions,!function_judgements,CONJUNCTS JUDGEMENT_THMS]))
			(mk_acl2_true (mk_comb (detector, (rhs o snd o strip_forall o concl) recursive)))))
in
	if not (null (set_diff (hyp res) ho_assumptions)) then 
		raise_error 6 "make_judgement" ("Hypothesis remain in judgement theorem: " ^ (thm_to_string (DISCH_AND_CONJ res))) 
	else 
		(fprint_trace 1 "\n" ; GEN_ALL (DISCH_AND_CONJ res))
end;

fun extra_hypothesis_error Pterm_true stage6 = 
	(fprint_trace 1 "Unresolved hypothesis in function: [\n" ; 
	(fn s => (	app (fprint_trace 1) (map (fn x => (term_to_string x) ^ ",\n") (tl s)) ; 
			fprint_trace 1 ((term_to_string (hd s)) ^ "]\n")))
	(filter (not o curry op= Pterm_true) (filter (not o is_definition) (hyp stage6))) ;
	raise_error 6 "make_acl2_definition" "Unresolve hypothesis in function, see trace for details")

local
	val rewrite = prove(``((|= P) ==> (a = b)) /\ (f = ite P a c) ==> (f = ite P b c)``,Cases_on `|= P` THEN RW_TAC std_ss [TRUTH_REWRITES,ite_def])
in
fun make_acl2_definition converted_arg converted_missing theorems stage4 stage5 = 
let	val oldPterm = (mk_acl2_true o rand o rator o rator o rhs o snd o strip_forall) (first is_definition (hyp stage5));
	val oldP = (repeat rator o dest_acl2_true) oldPterm;

	val types = filter (all (curry op= sexp_type) o flatten o 
				map (uncurry (C (curry op::)) o strip_fun o type_of) o free_vars)
			(filter (not o curry op= oldPterm) (filter (is_acl2_true o snd o strip_forall) (hyp stage5)));

	val terms = mk_set (filter (is_eq o snd o strip_exists o fst o strip_neg) (flatten (map (fst o strip_imp) (hyp stage5))));
	
	
	val cargs = CONJUNCTS (valOf converted_arg) handle _ => [];

	fun some_imp_match x y =
		match_term x y handle e => 
		match_term (fst (dest_imp x)) y;

	
	val (constraint_theorems,proof_theorems) = 
		mappartition ((fn x => INST_TY_TERM (tryfind (some_imp_match (concl x) o rhs o concl) cargs) x) o 
			replace_free_hol o replace_constructed o SPEC_ALL) theorems

	val constraint_theorems_converted = 
		map (REWRITE_RULE [ANDL_REWRITE,NOT_REWRITE] o DISCH_AND_CONJ o 
			CONV_RULE (DEPTH_CONV (FIRST_CONV (map (fn x => fn y => 
			GSYM (INST_TY_TERM (match_term ((rhs o concl) x) y) x)) cargs)))) constraint_theorems

	val newPterm = generatePterm oldPterm types converted_arg converted_missing constraint_theorems_converted

	val Pterm_true = (mk_acl2_true (repeat body newPterm));

	val (type_proofs,other_proofs) = partition (C mem types o concl) 
			(CONJUNCTS (REWRITE_RULE [ANDL_REWRITE,NOT_REWRITE,BOOL_TRUE] 
			(ASSUME Pterm_true)))

	val hol_types = (fst o strip_fun o type_of o repeat rator o rand o lhs o concl) stage5;

	val dec_enc_rewrs = mapfilter 
		(fn t => tryfind (C MATCH_MP t) (map (get_decode_encode_thm) hol_types)) type_proofs;
	val enc_dec_rewrs = mapfilter get_encode_decode_thm hol_types

	val extra_thms = (map (REWRITE_RULE [ANDL_REWRITE,NOT_REWRITE,AND_IMP_INTRO,GSYM CONJ_ASSOC] o DISCH_ALL)
				((map (fst o EQ_IMP_RULE o CONV_RULE (DEPTH_CONV NCHOT_HOL_ACL2)) cargs) @ 
				constraint_theorems_converted @ proof_theorems)) @
			 (map (snd o EQ_IMP_RULE o snd) converted_missing);

	val hyp_conv = CONV_HYP (DEPTH_CONV BETA_CONV THENC REWRITE_CONV 
				(ANDL_REWRITE::NOT_REWRITE::TRUTH_REWRITES::(dec_enc_rewrs @ enc_dec_rewrs)))
	
	val stage6 = (	C (foldl (uncurry PROVE_HYP)) type_proofs o
			C (foldl (uncurry PROVE_HYP)) other_proofs o
			augment_hypothesis (SOME (hyp_conv (INST [oldP |-> newPterm] stage4))) extra_thms o
			FOLD_HYP split_hyp o
			CONV_HYP (DEPTH_CONV NCHOT_HOL_ACL2) o
			RUNDISCH_ALL o C (foldl (uncurry DISCH)) (map concl other_proofs) o
			RUNDISCH_ALL o C (foldl (uncurry DISCH)) (map concl type_proofs))
		(hyp_conv (INST [oldP |-> newPterm] stage5));

	val _ = if length (hyp stage6) > 2 then extra_hypothesis_error Pterm_true stage6 else ()

	val definition =  (fn x => new_definition((fst o dest_var o repeat rator o lhs o snd o strip_forall) x,x)) 
				(first is_definition (hyp stage6));

	val recursive = GEN_ALL (MATCH_MP rewrite 
		(CONJ 
		(CONV_RULE (RAND_CONV (FORK_CONV (DEPTH_CONV BETA_CONV,ALL_CONV)))
			(MATCH_MP (DISCH (first is_definition (hyp stage6)) (DISCH Pterm_true stage6)) definition))
		(INST_TY_TERM (match_term 
			(((fn (a,b,c) => b) o dest_acl2_cond o rhs o snd o 
				strip_forall o first is_definition o hyp) stage6) 
			((lhs o concl o BETA_RULE) stage6)) 
				(SPEC_ALL definition))));

	val enc_decs = map get_encode_decode_thm (flatten (map (uncurry (C (curry op::)) o strip_fun) hol_types));
	val enc_dets = map get_detect_encode_thm (flatten (map (uncurry (C (curry op::)) o strip_fun) hol_types));
	val encoders = map2 (fn n => fn t => n |-> make_ho_encoder ((fst o dest_var) n) t)
					((snd o strip_comb o lhs o concl o SPEC_ALL) definition)
					hol_types
	
	val cmissing_rewrite = map (DISCH_ALL o SYM o uncurry TRANS) converted_missing;

	val correct = (SYM o CONV_RULE (DEPTH_CONV ETA_CONV THENC DEPTH_CONV FORALL_NOT_CONV) o SIMP_RULE std_ss 
			(ite_def::NOT_REWRITE::ANDL_REWRITE::TRUTH_REWRITES::(
				cmissing_rewrite @
				enc_dets @ 
				theorems @
				(mapfilter (DISCH_ALL o valOf) [Option.map 
				(REWRITE_RULE (enc_decs @ enc_dets) o DISCH_ALL o INST encoders) converted_arg]))))
		(REWRITE_RULE enc_decs 
		(BETA_RULE (INST encoders (SPEC_ALL definition))))

	val correct' = 
		GEN_ALL (SIMP_RULE std_ss (theorems @ enc_decs)
				(MATCH_MP CORRECT_CONVERT
				(DISCH ((mk_neg o (fn (a,b,c) => a) o dest_cond o lhs o concl) correct) correct))
			handle e => correct)

	val judgement = make_judgement converted_arg recursive extra_thms correct';

in
	(judgement,correct',PURE_REWRITE_RULE [el 2 (CONJUNCTS andl_def)] recursive)
end
end;

local
	fun unpair [] arg = REFL arg
	  | unpair (x::xs) arg = 
		RIGHT_CONV_RULE (RAND_CONV (unpair xs)) (SYM (ISPEC arg pairTheory.PAIR))
in
fun FULL_BETA_CONV term =
	BETA_CONV term handle e => 
	pairLib.PAIRED_BETA_CONV term handle e => 
	let	val ((vars,body),arg) = ((pairSyntax.strip_pair ## I) o pairSyntax.dest_pabs ## I) (dest_comb term)
	in	(RAND_CONV (unpair (tl vars)) THENC pairLib.PAIRED_BETA_CONV THENC REWRITE_CONV [FST,SND]) term
	end
end;
		
fun ilist_mk_comb [] term = term
  | ilist_mk_comb (x::xs) term = ilist_mk_comb xs (beta_conv (mk_comb(inst (match_type (fst (dom_rng (type_of term))) (type_of x)) term,x)))

(* Returns type constraints for arguments *)
fun get_arg_constraints stage3' = 
let	val args = (snd o strip_comb o rand o lhs o concl) stage3'
	val decodes = map (get_detect_term o type_of o repeat body) args;
in
	map2 (fn arg => fn decode => 
		ASSUME(list_mk_forall(	(map sexp_var o fst o strip_abs) arg,
					mk_acl2_true (mk_comb(decode,
						list_mk_comb((repeat rator o rand o snd o strip_abs) arg,
						(map sexp_var o fst o strip_abs) arg)))))) args decodes
end;

(*****************************************************************************)
(* ensure_correct_vars: Ensure variables are acl2 variables                  *)
(*                                                                           *)
(* var'...'    ---> VAR_n                                                    *)
(* reserved    ---> RESERVED_TYPE                                            *)
(* other       ---> VAR_n                                                    *)
(*                                                                           *)
(*****************************************************************************)

local
	val reserved = (map (stringLib.fromHOLstring o hd o strip_pair) o fst o dest_list o rhs o concl) acl2_packageTheory.ACL2_PACKAGE_ALIST_def
	fun count_prim [] = ("",0)
          | count_prim (x::xs) = 
		let val (s,n) = count_prim xs in if x = #"'" then (s,n + 1) else (str x ^ s,n) end;
	fun strip_ s = if size s > 0 andalso String.sub(s,0) = #"_" then strip_ (String.substring(s,1,size s - 1)) else s
	fun new_name v = 
	let	val (s,t) = dest_var v
	in	
		if mem (String.map Char.toUpper s) reserved then new_name(mk_var(String.map Char.toUpper (s ^ "_" ^ (fst (dest_type t))),t))
		else if Char.contains s #"'" then new_name(mk_var(String.map Char.toUpper (((fn (a,b) => a ^ "_" ^ (int_to_string b)) (count_prim (explode s)))),t))
		else if not (exists Char.isAlpha (explode s)) then new_name (mk_var("VAR_" ^ (strip_ s),t))
		else mk_var(String.map Char.toUpper s,t)
	end
	fun acl2_variant vars_list v = 
	let	val (s,t) = dest_var v
		val fields = String.fields (curry op= #"_") s
		val n = case (tryfind Int.fromString (rev fields)) of SOME n => n | NONE => 0
		val s' = if all Char.isDigit (explode (last fields)) then substring(s,0,size s - size (last fields) - 1) else s
	in
		if mem v vars_list then acl2_variant vars_list (mk_var(s' ^ "_" ^ (int_to_string (n + 1)),t)) else v
	end;
	fun CHECK_VAR_CONV term = 
	let	val name = new_name ((fst o dest_abs) term)
		val other_names = free_vars term
	in
		RENAME_VARS_CONV [fst (dest_var (acl2_variant other_names name))] term
	end
	fun CHECK_VARS_CONV term = (TRY_CONV CHECK_VAR_CONV THENC SUB_CONV CHECK_VARS_CONV) term
in
fun ensure_correct_variables thm = SPEC_ALL (CONV_RULE CHECK_VARS_CONV (GEN_ALL thm))
end

fun check_missing_cases L = 
if all null L then L else
let	val c = map hd L
	val t = type_of (fst (hd c)) 
	val constructors = TypeBase.constructors_of t;
in
	if null (set_diff constructors (map (repeat rator o snd) c)) 
		then check_missing_cases (map tl L)
		else map2 (curry op::) c (check_missing_cases (map tl L))
end;

fun gen_missing_list missing stage3 = 
let	val args = (snd o strip_comb o rand o lhs o concl) stage3
in
	mk_set (check_missing_cases (map (zip args o snd o strip_comb) missing))
end;

(*****************************************************************************)
(* Calculates input restrictions caused by missing function clauses          *)
(*                                                                           *)
(* Condition is a disjunction of constructors                                *)
(* Recursive conditions are placed by taking predicates on the path to the   *)
(* missing clauses                                                           *)
(*****************************************************************************)

fun subst_route v a l = 
let	val f = subst (map2 (curry op|->) v a)
in	map (map f ## f) l
end

fun find_routes (function,args) term =
	if TypeBase.is_case term then
		let 	val (_,var,cl) = TypeBase.dest_case term
		in	flatten (map (fn (c,v) => 
				let 	val sub = subst (map (fn a => a |-> variant (free_vars var) a) (free_vars c))
				in
				map (cons (list_mk_exists(map sub (free_vars_lr c),sub (mk_eq(var,c)))) o map sub ## sub) 
					(find_routes (function,args) v)
				end) cl)
		end
	else if is_cond term then
		let 	val (pred,left,right) = dest_cond term
		in	flatten [
				map (cons pred ## I) (find_routes (function,args) left),
				map (cons (mk_neg pred) ## I) (find_routes (function,args) right)]
		end
	else if is_imp term then
		let	val (pred,right) = dest_imp term
		in	map (cons pred ## I) (find_routes (function,args) right)
		end
	else 
		let	val (f,a) = strip_comb term
		in	if (f = function) andalso (length a = length args) 
				then [([],term)] 
				else if null a 
					then []
					else if is_abs f then 
						let 	val (vs,b) = strip_abs f
						in	flatten (subst_route vs a (find_routes (function,args) b) :: 
								map (find_routes (function,args)) a)
						end
						else flatten (map (find_routes (function,args)) (f::a))
		end

val get_constructor = repeat rator o rhs o snd o strip_exists o fst o strip_neg;

fun is_constructed term = 
let	val cs = (TypeBase.constructors_of o type_of o lhs o snd o strip_exists) term
in
	exists (can (C match_term (get_constructor term))) cs
end;
	
fun calculate_missing_conditions [] stage3 = (``T``,[])
  | calculate_missing_conditions missing stage3 = 
let	val terms = flatten (map (map (fn (a,b) => mk_neg (list_mk_exists(free_vars_lr b,mk_eq (a,b))))) missing)
	val thm = REWRITE_RULE [GSYM DISJ_ASSOC] (DISJ_CASES_UNIONL (ASSUME (list_mk_disj terms))
			(map2 (fn x => REWRITE_RULE [ASSUME x])
			terms
			(flatten (map (map ((fn x => (ISPEC x o TypeBase.nchotomy_of o type_of) x) o fst)) missing))))
	val conditions = (strip_disj o concl) thm
	val (function,args) = (strip_comb o rand o lhs o concl) stage3;
	val recursive_routes = 
		(map (filter is_constructed ## I))
		(filter (fn x => not (op_mem (fn x => fn y => all (op= o (repeat rator ## repeat rator)) (zip x y))
				((snd o strip_comb o snd) x) (map (map snd) missing)))
			((find_routes (function,args) o rhs o concl) stage3));
	fun func2pred term = list_mk_comb(mk_var("P",list_mk_fun((fst o strip_fun o type_of o repeat rator) term,``:bool``)),snd (strip_comb term))
	val pred = func2pred ((rand o lhs o concl) stage3);
in
	(mk_imp(pred,list_mk_disj conditions handle e => ``T``),
	map (fn (rr,t) => list_mk_imp(subst (mapfilter (fn x => (lhs o snd o strip_exists) x |-> (rhs o snd o strip_exists) x) rr) pred :: 
					(filter (fn t => not (exists (C free_in t) args)) rr),func2pred t)) recursive_routes)	
end

fun print_missing_info stage1 stage3 clauses (condition,recursives) =
let	fun subs_map x = 
		(fn y => list_mk_forall(tl (free_vars_lr y),y))
			(subst (map2 (curry op|->) 
				((snd o strip_comb o rand o lhs o concl) stage3)
				((snd o strip_comb o lhs o concl) stage1)) x)
	fun concat comma c = 
		foldl (fn (x,s) => (term_to_string x) ^ comma ^ s) ((term_to_string o hd) c) (tl c) 
in
	(fprint_trace 1 "The following clauses are missing from the definition: [" ;
	 fprint_trace 1 (concat "," clauses) ;
	 fprint_trace 1 "]\nRequiring a recursive predicate P that satisfies:\n" ;
	 fprint_trace 1 ("     " ^ term_to_string (subs_map condition) ^ " /\\ \n") ;
	 fprint_trace 1 ("     " ^ concat " /\\ " (map subs_map recursives)) ;
	 fprint_trace 1 "]\n")
end;

fun convert_argument types NONE = NONE
  | convert_argument types (SOME x) = 
let	val _ = fprint_trace 1 "Converting argument constraints: "
in
	(SOME (	(LIST_CONJ o (map (RIGHT_CONV_RULE (FIRST_CONV (mapfilter REWR_CONV (CONJUNCTS TRUTH_REWRITES))) o 
		GSYM o AP_TERM acl2_true_tm o 
		ACL2_DEPTH_CONV types (!rewrite_thms) NONE [] o curry mk_comb ``bool``)) o strip_conj) x))
	before (fprint_trace 1 "\n")
end;

fun convert_definition_full arg_assumption theorems function = 
let	val stage1 = convert_tc function
	val stage3 = encode_decode_function (curry_single_function stage1)
	val stage4 = acl2_define_function 
		("acl2_" ^ ((fst o dest_const o repeat rator o lhs o 
			snd o strip_forall o hd o strip_conj o concl) function)) stage3;
	val stage3' = INST_TY_TERM (match_term ((lhs o concl o BETA_RULE) stage3) ((lhs o concl) stage4)) stage3
	val missing_clauses = incomplete (map (rhs o snd o strip_forall o concl) (CONJUNCTS function))
				((rhs o concl) stage1) []
	val missing = gen_missing_list missing_clauses stage3
	val missing_conditions = calculate_missing_conditions missing stage3

	val _ = if null (snd missing_conditions) then () else 
		print_missing_info stage1 stage3 missing_clauses missing_conditions

	val arg_types = get_arg_constraints stage3'
	
	val stage5 = convert_acl2 arg_types stage3' stage4 missing (!rewrite_thms);

	val arg = Option.map (ilist_mk_comb ((snd o strip_comb o rand o lhs o concl) stage4)) arg_assumption

	val converted_arg = convert_argument arg_types arg;

	val NTEC = (fn x => (x,(NCHOTOMY_TO_EQUAL_CONV ((rhs o concl) x))))
	
	val converted_missing = 
		(map (NTEC o NCHOT_HOL_ACL2) o strip_disj o snd o dest_imp o fst) missing_conditions handle e => []

	val (judgement,correct,recursive) = 
		make_acl2_definition converted_arg converted_missing theorems stage4 stage5;

	val _ = fprint_trace 1 ("Adding judgement theorem: " ^ (thm_to_string judgement) ^ "\n")
	val _ = fprint_trace 2 ("Adding rewrite theorem: " ^ (thm_to_string correct) ^ "\n")
	
	val _ = rewrite_thms := (correct::(!rewrite_thms))
	val _ = function_judgements := (judgement::(!function_judgements))
in	
	(correct,ensure_correct_variables recursive)
end;

fun convert_definition thm = convert_definition_full NONE [] thm;

local
	val flattened_detectors = ref ([]:(hol_type * (thm * thm)) list)
	fun fix x = fix (implode (List.drop(explode x,index (curry op= #":") (explode x) + 1))) handle e => x;
	fun concat [] = "" | concat [x] = fix x | concat (x::xs) = fix x ^ "_" ^ concat xs;
	fun get_detector_definition' t = 
		if is_list_type t then
			ISPEC (get_detector (dest_list_type t)) (GEN ``p:sexp -> sexp`` LISTP_FLAT)
		else if (can dest_prod t) then
			ISPECL (map get_detector [fst (dest_prod t),snd (dest_prod t)]) (GEN ``f:sexp -> sexp`` (GEN ``g:sexp -> sexp`` PAIRP_FLAT))
		else if t = ``:num`` then natp_def
		else get_detector_definition t
	fun make_detector t =
	let	val d = SPEC_ALL ((RIGHT_CONV_RULE (	(if not (is_list_type t) then ONCE_REWRITE_CONV [LISTP_FLAT] else ALL_CONV) THENC 
							(if not (can dest_prod t) then ONCE_REWRITE_CONV [PAIRP_FLAT] else ALL_CONV) THENC 
							REWRITE_CONV [andl_fold] THENC ONCE_DEPTH_CONV ANDL_FLATTEN_CONV) o get_detector_definition') t)
		val name = mk_var(concat (map (fst o dest_const) ((op:: o strip_comb o rator o lhs o concl) d)),``:sexp -> sexp``)
	in
		if length ((op:: o strip_comb o rator o lhs o snd o strip_forall o concl) d) = 1 then ((REFL o lhs o concl) d,d) else
			let 	val x = GSYM (new_definition((fst o dest_var) name,mk_eq(mk_comb(name,(rand o lhs o concl) d),(lhs o concl) d)))
			in
				(x,REWRITE_RULE [x] d) 
			end
	end
in
	fun get_recogniser t = 
	if polymorphic t then raise_error 6 "get_detector" "Can only get a detector definition for base types."
	else assoc t (!flattened_detectors) handle e =>
		let	val d = make_detector t
			val _ = flattened_detectors := (t,d) :: (!flattened_detectors)
		in	d
		end
end;


(* Convert a HO term into a FO definition suitable for ACL2 *)
fun flatten_HO_definition name thm term = 
let	val (function,args) = strip_comb term
	val named_args = (snd o strip_comb o lhs o concl o SPEC_ALL) thm;
	
	val thm1 = BETA_RULE (PART_MATCH lhs thm (list_mk_comb(function,
		map2 (fn a => fn na => if (can dom_rng o type_of) a then a else na) args named_args)))

	val fo_args = (free_vars o rhs o concl) thm1

	val thm2 = GSYM (DEPTH_CONV BETA_CONV
		(list_mk_comb(list_mk_abs(fo_args,(lhs o concl) thm1),fo_args)));

	val thm3 = ONCE_REWRITE_RULE [thm2] thm1;

	val function = (repeat rator o rhs o concl) thm2;
	val fvar = mk_var(name,type_of function);
	
	val ho_types = find_terms is_forall (concl thm3);

	val thm4 = GENL fo_args (REWRITE_RULE (bool_def::(map (uncurry GENL o (I ## PROVE_TYPE_JUDGEMENT (flatten [!function_judgements,CONJUNCTS JUDGEMENT_THMS])) o strip_forall) ho_types)) thm3);

	val definition = new_definition(name ^ "_def",mk_eq(fvar,function));
in
	(GSYM (BETA_RULE (foldr (uncurry (C AP_THM)) definition fo_args)),
		ensure_correct_variables (REWRITE_RULE [GSYM definition] thm4))
end;

local
	val imp_rewrite = prove(``((|= a) ==> (|= b)) ==> (|= implies a b)``,
		RW_TAC arith_ss [andl_def,implies_def,ite_def,TRUTH_REWRITES])
in
fun finish_conversion ethms types thm = 
let	val terms = filter (is_eq o snd o strip_exists o fst o strip_neg) (flatten (map (fst o strip_imp) (hyp thm)));

	val thms = mapfilter (fn term => CONVERT_TO_HOL term (first 
		(curry op= ((lhs o snd o strip_exists o fst o strip_neg) term) o rand o dest_acl2_true) types)) terms;

	val thm' = 
		clean_hyp_set (UNDISCH_ALL (foldr (uncurry DISCH) 
			(CONV_HYP (DEPTH_CONV (FIRST_CONV (map (REWR_CONV o GSYM) thms))) 
				(CONV_HYP (DEPTH_CONV (FIRST_CONV (map REWR_CONV thms))) thm))
			types))
	val _ = fprint_trace 1 "\n"
in
	(fn x => ensure_correct_variables (MATCH_MP imp_rewrite x handle e => x))
	(CONV_RULE (if null (hyp thm') then 
			ALL_CONV else 
			LAND_CONV (REWR_CONV (GSYM AND_TRUE) THENC 
				PURE_REWRITE_CONV [GSYM ANDL_REWRITE,GSYM CONJ_ASSOC]))
		(DISCH_AND_CONJ (augment_hypothesis NONE ethms thm')))
		
end
end;

fun convert_theorem thms thm = 
let	val thm_a = CONV_RULE (REDEPTH_CONV (AND_FORALL_CONV ORELSEC OR_FORALL_CONV ORELSEC RIGHT_IMP_FORALL_CONV)) thm
	val thm_b = SPEC_ALL thm_a
	val vars = free_vars (concl thm_b)
	val arg_types = map (fn x => ASSUME (mk_acl2_true(mk_comb(get_detect_term (type_of x),sexp_var x)))) vars
	val arg_decodes = map (fn x => mk_comb(get_decode_term (type_of x),sexp_var x)) vars	
in
	finish_conversion thms (map concl arg_types) 
		(CONV_RULE (RAND_CONV (ACL2_DEPTH_CONV arg_types (!rewrite_thms) NONE []))
			(CONV_RULE (ONCE_REWRITE_CONV [GSYM SEXP_TO_BOOL_OF_BOOL] THENC REWRITE_CONV [sexp_to_bool_def])
				(INST (map2 (curry op|->) vars arg_decodes) thm_b)))
end;

