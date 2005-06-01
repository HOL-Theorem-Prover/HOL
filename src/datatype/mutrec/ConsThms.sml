(* =====================================================================*)
(* FILE          : cons_thms.sml                                        *)
(* DESCRIPTION   : functor for proving mutually recursive data          *)
(*                 constructors one-to-one, onto and distinct           *)
(*                                                                      *)
(* AUTHOR        : Myra VanInwegen                                      *)
(*                                                                      *)
(* DATE          : 93.12.17                                             *)
(*                                                                      *)
(* =====================================================================*)


structure ConsThms :> ConsThms =
struct

open HolKernel Parse basicHol90Lib;

type thm = Thm.thm;

val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars boolTheory.bool_grammars

fun decompose (tm, args_so_far) =
    if is_comb tm then
	let val {Rator, Rand} = dest_comb tm in
	    decompose (Rator, Rand :: args_so_far)
	end
    else
	(tm, args_so_far)


fun build {New_Ty_Existence_Thm, New_Ty_Induct_Thm,New_Ty_Uniqueness_Thm}
 = let
val rec_thm = New_Ty_Existence_Thm
val induct_thm = New_Ty_Induct_Thm

(* decompose takes as arguments a term that is a constructor applied
   to some args and the list of args stripped off so far; it strips
   off the rest of the args, returning the constructor by itself
   and the complete list of args *)

(* This function divides up a list of applied constructors into a list
   such that each element of the list is the list of apllied constructors
   for one of the types of the mutually recursive types.
   To get this going, send
   in true as first_item, and [] as current_sublist and completed_sublists,
   and any type whatsoever as current_type *)
fun divide_list first_item (item::rest_list) current_type current_sublist
    completed_sublists =
    let val new_type = type_of item
    in
	if first_item orelse (new_type = current_type) then
	    divide_list false rest_list new_type (item::current_sublist)
	    completed_sublists
	else
	    divide_list false rest_list new_type [item]
	    ((rev current_sublist)::completed_sublists)
    end
  | divide_list first_item  [] current_type current_sublist
    completed_sublists =
    (rev ((rev current_sublist)::completed_sublists))


(* This function proves that constructors are distinct, ie, for each TY
   among the mutually recursive types, if CON1 and CON2 are two different
   constructors, we prove that a term of type TY constructed with
   the constructor CON1 cannot be equal to one constructed with the
   CON2 constructor, and so on. What is returned is a list of theormes,
   one for each type among the mutually recursive types.
   BUG: this cannot be used twice, as it defines some functions (named
   dist_aux_ftn_TY for each type TY of the mutually recursive types),
   so an attempt to do it again will result in a attempt to define these
   functions. *)


(* the first thing I want to to is tear apart rec_thm to find out what
   all the constructors and their args are *)

val temp = map strip_forall
    (strip_conj (snd (strip_exists
		      (snd (strip_forall (concl (rec_thm)))))))

val applied_cons_list = map (fn x => rand (lhs (snd x))) temp


val divided_list = divide_list true applied_cons_list Type.bool [] []

    val temp = map (map (fn x => decompose (x, []))) divided_list

val cons_var_list = map split temp


(* Now we need to generate some new variable names for the arguments.
   We will need to generate clauses like
   ~(CONS1 <args for CONS1> = CONS2 <args for CONS2>)
   and the problem is that the args for CONS1, which are variables,
   may have the same name as the args for CONS2, and we need to qualify
   over all of them separately. *)

val all_vars = flatten (flatten (map snd cons_var_list))
(* note all_vars is used below, not as a parameter *)

fun add_differently_named_vars (cons_list, vars_list) =
    let val new_vars_list =
	map (fn y => map (fn x => variant all_vars x) y) vars_list
    in
	(cons_list, vars_list, new_vars_list)
    end

val cons_var_newvar_list = map add_differently_named_vars cons_var_list

fun make_ineq cons1 x_args cons2 y_args =
    let val eq_term = mk_eq {lhs = list_mk_comb (cons1, x_args),
			     rhs = list_mk_comb (cons2, y_args)}
	val not_eq_term = mk_comb {Rator = --`$~`--, Rand = eq_term}
	val temp_result = list_mk_forall (y_args, not_eq_term)
    in
	list_mk_forall (x_args, temp_result)
    end

(* the following function takes the constructor first in the list, (say
   it is CONS1) and combines it, in turn, with the rest of the constructors
   on the list (say they are CONS2 ... CONS7), into items that look like
   !<x_args for CONS1> <y_args for CONS2>.
         ~(CONS1 <x_args for CONS1> = CONS2 <y_args for CONS2>)
                   ...
   !<x_args for CONS1> <y_args for CONS7>.
         ~(CONS1 <x_args for CONS1> = CONS7 <y_args for CONS7>)    *)
fun mk_conjuncts
    cons1 cons1_x_args (cons2::more_cons) (cons2_y_args::more_args) =
    (make_ineq cons1 cons1_x_args cons2 cons2_y_args)::
    mk_conjuncts cons1 cons1_x_args more_cons more_args
  | mk_conjuncts cons1 cons1_x_args [] [] = []
  | mk_conjuncts _ _ _ _ = raise HOL_ERR
    {message = "improper constructor or variable args",
     origin_function = "mk_conjuncts",
     origin_structure = "prove_mutual_constructors_distinct"}

(* this function makes all the conjuncts for one type *)
fun mk_all_conjuncts (con::cons_list,
		      x_args::x_args_list, y_args::y_args_list) =
    if (cons_list = []) then
	([] : term list)
    else
	(mk_conjuncts con x_args cons_list y_args_list)@
	(mk_all_conjuncts (cons_list, x_args_list, y_args_list))
  | mk_all_conjuncts (_, _, _) = raise HOL_ERR
    {message = "improper constructor or variable args",
     origin_function = "mk_all_conjuncts",
     origin_structure = "prove_mutual_constructors_distinct"}

val conjuncts_list = map mk_all_conjuncts cons_var_newvar_list

(* now, the problem is that there may be types that have only one
   constructor, so the list of conjuncts may be empty, so we have
   to filter out these empty lists *)
val filtered_list = filter (fn x => x <> []) conjuncts_list

(* goals is a list, containining one goal for each type;
   each goal says that the the constructors for that type are distinct *)

val goals = map list_mk_conj filtered_list

(* Now I need to define functions (I call then distinctness functions)
   that return a different (natural) number
   when applied to items constructed with each constructor *)

val num_ty = Type`:num`
fun mk_function_variable the_type =
    mk_var {Name = "dist_aux_ftn_"^(#Tyop (dest_type the_type)),
	    Ty = mk_type {Tyop = "fun", Args = [the_type, num_ty]}}
fun mk_def_term ftn_var old_type (app_con::app_con_list) count =
    let val new_type = type_of app_con
	val new_ftn_var =
	    if new_type = old_type then	ftn_var
	    else mk_function_variable new_type
	val new_conjunct =
	    mk_eq {lhs = mk_comb {Rator = new_ftn_var, Rand = app_con},
                   rhs = Term.mk_numeral (Arbnum.fromInt count)}
(*		   rhs = mk_const {Name = Lib.int_to_string count,
				   Ty = num_ty}}
*)
    in
	if app_con_list = [] then
	    new_conjunct
	else
	    mk_conj {conj1 = new_conjunct,
		     conj2 = mk_def_term new_ftn_var new_type app_con_list
		             (count + 1)}
    end
  | mk_def_term _ _ [] _ = raise HOL_ERR
    {message = "empty constructor list",
     origin_function = "mk_all_conjuncts",
     origin_structure = "prove_mutual_constructors_distinct"}

(* the conjuncts of def_term say that there are a bunch of functions (the
   distinctness functions), one for each type, and they all return
   different numbers when applied to terms made from different
   constructors *)

val def_term =
    let val old_type = type_of (hd applied_cons_list)
    in
	mk_def_term (mk_function_variable old_type) old_type
	applied_cons_list 0
    end

val dist_aux_ftns_thm = Recftn.define_mutual_functions
                        {rec_axiom = rec_thm, def = def_term, fixities = NONE,
			 name = ("dist_aux_ftn_"^
				 (#Tyop (dest_type(type_of
                                 (hd applied_cons_list))))^"_DEF")}


(* OK, now the way that we go about proving the theorem is this --
   we need to prove, for example,
         ~(CON1 <args for CON1> = CON2 <args for CON2>)
   using STRIP_TAC, this breaks down to showing
         CON1 <args for CON1> = CON2 <args for CON2> ==> F
   So we assume
         CON1 <args for CON1> = CON2 <args for CON2>
   We apply the appropriate distinctness function, getting
         n1 = n2
   where n1 and n2 are two different natural numbers.
   We apply num_EQ_CONV and get
         F
   and we're done *)

fun solve_goal_tac dist_ftn (asms, gl) =
    let val asm = hd asms
	val thm1 = AP_TERM dist_ftn (ASSUME asm)
	val thm2 = REWRITE_RULE [dist_aux_ftns_thm] thm1
	val thm3 = CONV_RULE reduceLib.NEQ_CONV thm2
    in
	ACCEPT_TAC thm3 (asms, gl)
    end

fun mk_function_const the_type =
    mk_const {Name = "dist_aux_ftn_"^(#Tyop (dest_type the_type)),
	      Ty = mk_type {Tyop = "fun", Args = [the_type, num_ty]}}

fun prove_one_type_distinct gl =
    let val one_conj = if is_conj gl then (#conj1 (dest_conj gl)) else gl
	val the_type = type_of (lhs (rand (snd (strip_forall one_conj))))
	val dist_ftn = mk_function_const the_type
    in
	TAC_PROOF (([], gl),
		   REPEAT STRIP_TAC THEN solve_goal_tac dist_ftn)
    end

val distinctness_theorems = map prove_one_type_distinct goals

(* If there is only one constructor then we return the theorem |- T  *)
val mutual_constructors_distinct =
    (case distinctness_theorems
       of [] => TRUTH
        | _ => LIST_CONJ distinctness_theorems)




(* This function proves that constructors are one-to-one, ie, for each TY
   among the mutually recursive types, if CON is a constructor for that
   type, then the theorem for TY (what is returned is a list of theorems,
   one for each type among the mutually recursive types) includes a clause
   saying that CON arg1 ... argn = CON Arg1 ... Argn
   iff (arg1 = Arg1) /\ ... (argn = Argn).
   BUG: this cannot be used twice, as it defines some functions (the
   argument extraction functions, names CON_arg if the constructor CON
   has one arg, or CON_arg1 ... CON_argn if CON has n args),
   so an attempt to do it again will result in a attempt to define these
   functions. *)



(* the first thing I want to to is tear apart rec_thm to find out what
   all the constructors and their args are *)

val temp = map strip_forall
    (strip_conj (snd (strip_exists
		      (snd (strip_forall (concl (rec_thm)))))))

val applied_cons_list = map (fn x => rand (lhs (snd x))) temp

val divided_list = divide_list true applied_cons_list Type.bool [] []

(* At this stage, I will eliminate from the list the constructors
   that have no arguments, since they won't be needed in the theorem *)
    val temp = map (map (fn x => decompose (x, []))) divided_list

val unsplit_cons_var_list = map (filter (fn x => snd x <> [])) temp


val cons_var_list = map split unsplit_cons_var_list
(* Now we need to generate some new variable names for the arguments.
   We will need to generate clauses like
   ~(CONS1 <args for CONS1> = CONS2 <args for CONS2>)
   and the problem is that the args for CONS1, which are variables,
   may have the same name as the args for CONS2, and we need to qualify
   over all of them separately. *)
val all_vars = flatten (flatten (map snd cons_var_list))
(* note all_vars is used below, not as a parameter *)
fun add_differently_named_vars (cons_list, vars_list) =
    let val new_vars_list =
	map (fn y => map (fn x => variant all_vars x) y) vars_list
    in
	(cons_list, vars_list, new_vars_list)
    end
val cons_var_newvar_list = map add_differently_named_vars cons_var_list

fun mk_var_eq_conj (x_var::x_vars) (y_var::y_vars) =
    if x_vars = [] then
	mk_eq {lhs = x_var, rhs = y_var}
    else
	mk_conj {conj1 = mk_eq {lhs = x_var, rhs = y_var},
		 conj2 = mk_var_eq_conj x_vars y_vars}
  | mk_var_eq_conj _ _ = raise HOL_ERR
    {message = "different number of args",
     origin_function = "mk_var_eq_conj",
     origin_structure = "prove_mutual_constructors_one_one"}

fun mk_1_1_statement con x_vars y_vars =
    let val appl_x = list_mk_comb (con, x_vars)
	val appl_y = list_mk_comb (con, y_vars)
	val left = mk_eq {lhs = appl_x, rhs = appl_y}
	val eq_term = mk_eq {lhs = left,
			     rhs = mk_var_eq_conj x_vars y_vars}
	val forall_term = list_mk_forall (y_vars, eq_term)
    in
	list_mk_forall (x_vars, forall_term)
    end
val T_term = Term`T`

fun mk_goal_for_one_type ([],[],[]) = T_term
  | mk_goal_for_one_type (con::[],x_vars::[],y_vars::[]) =
	mk_1_1_statement con x_vars y_vars
  | mk_goal_for_one_type (con::cons_list, x_vars::x_vars_list,
			  y_vars::y_vars_list) =
    mk_conj {conj1 = mk_1_1_statement con x_vars y_vars,
	     conj2 = mk_goal_for_one_type (cons_list, x_vars_list,
					   y_vars_list)}
  | mk_goal_for_one_type (_, _, _) = raise HOL_ERR
    {message = "different number of conses or args",
     origin_function = "mk_goal_for_one_type",
     origin_structure = "prove_mutual_constructors_one_one"}

val goals = map mk_goal_for_one_type cons_var_newvar_list

(* Now I have to define some functions that, given a constructor CON applied
   to arguments, will return the arguments. There will be N functions
   defined, one for each argument to the constructor, named CON_arg1 thru'
   CON_argN. (But, if the constructor has only one argument, the argument
   extraction function will be called CON_arg.) *)

fun mk_fun_ty ty1 ty2 = mk_type {Tyop = "fun", Args = [ty1, ty2]}

fun mk_ftn_var con suffix type_of_ftn =
    let val name = (#Name (dest_const con))^suffix
    in {ftn_name = name, ftn_var =  mk_var {Name = name, Ty = type_of_ftn}}
    end

fun mk_hilbert the_type =
    let val the_ftn = mk_abs {Bvar = mk_var {Name = "x", Ty = the_type},
			      Body = T_term}
	val hilbert_type = mk_fun_ty (mk_fun_ty the_type Type.bool) the_type
	val hilbert_op = mk_const {Name = "@", Ty = hilbert_type}
    in
	mk_comb {Rator = hilbert_op, Rand = the_ftn}
    end

fun define_single_ftn con arg =
    let val appl_term = mk_comb {Rator = con, Rand = arg}
	val appl_term_type = type_of appl_term
	val arg_type = type_of arg
	val type_of_ftn = mk_fun_ty appl_term_type arg_type
	val {ftn_var, ftn_name} = mk_ftn_var con "_arg" type_of_ftn
	val ftn_appl_term = mk_comb {Rator = ftn_var, Rand = appl_term}
	val def_clause = mk_eq {lhs = ftn_appl_term, rhs = arg}
	val allelse_lhs = mk_comb {Rator = ftn_var,
				   Rand = mk_var {Name = "allelse",
						  Ty = appl_term_type}}
	val allelse_clause = mk_eq {lhs = allelse_lhs,
				    rhs = mk_hilbert arg_type}
	val def_term = mk_conj {conj1 = def_clause, conj2 = allelse_clause}
	val def_name = ftn_name ^ "_DEF"
	val ftn_thm = Recftn.define_mutual_functions
	              {rec_axiom = rec_thm, def = def_term, name = def_name,
		       fixities = NONE}
	val ftn_const = mk_const (dest_var ftn_var)
    in
	[((def_name, ftn_thm), ftn_const)]
    end

fun define_several_functions con args =
    let val appl_term = list_mk_comb (con, args)
	val appl_term_type = type_of appl_term
	fun helper count (arg::more_args) =
	    let val arg_type = type_of arg
		val type_of_ftn = mk_fun_ty appl_term_type arg_type
		val {ftn_var,ftn_name} = mk_ftn_var con
		    ("_arg"^(Lib.int_to_string count)) type_of_ftn
		val ftn_appl_term = mk_comb {Rator = ftn_var,
					     Rand = appl_term}
		val def_clause = mk_eq {lhs = ftn_appl_term, rhs = arg}
		val allelse_lhs =
		    mk_comb {Rator = ftn_var,
			     Rand = mk_var {Name = "allelse",
					    Ty = appl_term_type}}
		val allelse_clause = mk_eq {lhs = allelse_lhs,
					    rhs = mk_hilbert arg_type}
		val def_term = mk_conj {conj1 = def_clause,
					conj2 = allelse_clause}
		val def_name = ftn_name ^"_DEF"
		val ftn_thm = Recftn.define_mutual_functions
		              {rec_axiom = rec_thm, def = def_term,
			       fixities = NONE, name = def_name}
		val ftn_const = mk_const (dest_var ftn_var)
	    in
		((def_name,ftn_thm), ftn_const)::
		(helper (count + 1) more_args)
	    end
	  | helper _ [] = []
    in
	helper 1 args
    end

fun define_extraction_functions (con, args) =
    if length (args) = 1 then
	define_single_ftn con (hd args)
    else
	define_several_functions con args

fun ftn_defs_for_one_type unsplit_cons_vars =
    map define_extraction_functions unsplit_cons_vars

(* The structure of ftn_defs is kind of complicated. It is a list, each
   element containing information for one of the mutually recursive
   types. Each of these element is a list continaing information for
   each constructor for that type. Each element of this is a list, containing
   information on the different extraction functions (there is one for
   each argument) defined for that constructor. Each of these elements is
   a pair consisting of the definition of the function and the name of
   the function defined. *)

val ftn_defs = map ftn_defs_for_one_type unsplit_cons_var_list

(* OK, my argument extraction functions are defined, now I need to go and
   prove the theorem! *)

fun double_eq eq1 eq2 =
    let val {lhs = x1, rhs = x2} = dest_eq (concl eq1)
	val {lhs = y1, rhs = y2} = dest_eq (concl eq2)
	val thm1 = AP_TERM x1 eq2
	val thm2 = AP_THM eq1 y2
    in
	TRANS thm1 thm2
    end

fun solve_goal_tac ftn_info (asms, gl) =
    let val {lhs = appl_cons_eq, rhs = args_eq} = dest_eq gl
	val args_eq_list = strip_conj args_eq
	val thm1 = ASSUME appl_cons_eq
	fun mk_thm (((name,thm),const)::more_info) =
	    let val this_thm =
		REWRITE_RULE [thm] (AP_TERM const thm1)
	    in
		if null more_info then
		    this_thm
		else
		    CONJ this_thm (mk_thm more_info)
	    end
	  | mk_thm [] = raise HOL_ERR
	    {message = "empty ftn_info",
	     origin_function = "solve_goal_tac",
	     origin_structure = "prove_mutual_constructors_one_one"}
	val thm2 = mk_thm ftn_info
	val left_implies_right = DISCH_ALL thm2
	val thm3 = ASSUME args_eq
	val thm_list = CONJUNCTS  thm3
	val (cons, _) = decompose (lhs appl_cons_eq, [])
	val thm4 = REFL cons
	fun do_apply eq_thm (next_eq_thm::more_eq_thms) =
	    do_apply (double_eq eq_thm next_eq_thm) more_eq_thms
	  | do_apply eq_thm [] = eq_thm
	val thm5 = do_apply thm4 thm_list
	val right_implies_left = DISCH_ALL thm5
	val final_thm = IMP_ANTISYM_RULE left_implies_right
	    right_implies_left
    in
	ACCEPT_TAC final_thm (asms, gl)
    end

fun solve_goal_for_one_type ftn_info_for_type goal =
    TAC_PROOF (([], goal),
	       REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
	       (case ftn_info_for_type of [] => [ACCEPT_TAC TRUTH]
		  | _ => map solve_goal_tac ftn_info_for_type))

fun prove_theorms (ftn_info::more_info) (goal::more_goals) =
    (solve_goal_for_one_type ftn_info goal)::
    prove_theorms more_info more_goals
  | prove_theorms [] [] = []
  | prove_theorms _ _ = raise HOL_ERR
    {message = "ftn_info and goals lists have different length",
     origin_function = "prove_theorems",
     origin_structure = "prove_mutual_constructors_one_one"}

val mutual_constructors_one_one = LIST_CONJ (prove_theorms ftn_defs goals)


val argument_extraction_definitions =
foldr (fn (listlist,name_thm_list)=>
        foldr (fn (name_thm_const_list, name_thm_l) =>
	        foldr (fn ((n_t,c),n_t_list) => n_t::n_t_list)
		      name_thm_l
	              name_thm_const_list)
	      name_thm_list
              listlist)
      []
      ftn_defs



(* This function proves that for each value Vof type TY among the
   mutually recursive types, if CON1 ... CONn are its constructors, then
   V must be equal to at least one of the CON1 ... CONn, apllied to some
   appropriate args. *)

val (prop_vars, rest_of_term) = strip_forall (concl induct_thm)
val {ant, conseq} = dest_imp rest_of_term
val conjuncts = strip_conj ant

(* Given a list of conjuncts from the induction theorem, this constructs the
   properties that we want to prove. *)

fun make_props_aux {prop_conjs, props, prev_type, term_var,
		    conjuncts = (conj::more_conjs)} =
    let val (vars, impl) = strip_forall conj
	val prop_appl_cons =
	    if is_imp impl then
		#conseq (dest_imp impl)
	    else
		impl
	val {Rator = prop_var, Rand = appl_cons} = dest_comb prop_appl_cons
	val new_type = type_of appl_cons
	val new_term_var =
	    if (prev_type <> new_type) then
		mk_var {Name = (#Tyop (dest_type new_type))^"_term",
			Ty = new_type}
	    else
		term_var
	val new_conj_in_prop =
	    list_mk_exists (vars, mk_eq {lhs = new_term_var, rhs = appl_cons})
    in
	if (new_type <> prev_type) then
           (* done with this property but continue on *)
	    make_props_aux {prop_conjs = [new_conj_in_prop],
			    props = (mk_abs {Bvar = term_var,
					     Body = list_mk_disj
					            (rev prop_conjs)}
				    :: props),
			    prev_type = new_type, term_var = new_term_var,
			    conjuncts = more_conjs}
	else make_props_aux {prop_conjs = (new_conj_in_prop::prop_conjs),
			     props = props ,
			     prev_type = new_type,
			     term_var = new_term_var,
			     conjuncts = more_conjs}
    end
  | make_props_aux {prop_conjs, props, term_var, conjuncts = [],...} =
    rev (mk_abs {Bvar = term_var, Body = list_mk_disj (rev prop_conjs)}::props)

fun make_props [] = []
  | make_props (conj :: more_conjs) =
    let val (vars, impl) = strip_forall conj
	val prop_appl_cons =
	    if is_imp impl then
		#conseq (dest_imp impl)
	    else
		impl
	val {Rator = prop_var, Rand = appl_cons} = dest_comb prop_appl_cons
	val new_type = type_of appl_cons
	val new_term_var = mk_var {Name = (#Tyop (dest_type new_type))^"_term",
				   Ty = new_type}
	val new_conj_in_prop =
	    list_mk_exists (vars, mk_eq {lhs = new_term_var, rhs = appl_cons})
    in
    make_props_aux {prop_conjs = [new_conj_in_prop],
		    props = [],
		    prev_type = new_type,
		    term_var = new_term_var,
		    conjuncts = more_conjs}
    end

val props = make_props conjuncts;

val spec_induct = BETA_RULE (SPECL props induct_thm)
val goal = #ant (dest_imp (concl spec_induct))

fun exists_list_tac (ex_term::terms) =
    if (terms = []) then
	EXISTS_TAC ex_term
    else
	EXISTS_TAC ex_term THEN exists_list_tac terms
  | exists_list_tac [] = ALL_TAC

fun just_do_it lhs_args (asms, gl) =
    if (lhs_args = []) then
	REWRITE_TAC [] (asms, gl)
    else
	(exists_list_tac lhs_args THEN REWRITE_TAC []) (asms, gl)

fun solve_goal_tac (asms, gl) =
    let val gl_is_disj = is_disj gl
	val term1 =
	    if gl_is_disj then #disj1 (dest_disj gl)
	    else gl
	val (vars, eq_term) = strip_exists term1
	val {lhs = left, rhs = right} = dest_eq eq_term
	val (lhs_cons, lhs_args) = decompose (left, [])
	val (rhs_cons, rhs_args) = decompose (right, [])
        (* the folowing function is nested so that
	   lhs_cons and lhs_args can be free in it *)
	fun helper (asms, gl) =
	    let val gl_is_disj = is_disj gl
		val term1 =
		if gl_is_disj then #disj1 (dest_disj gl)
		else gl
		val (vars, eq_term) = strip_exists term1
		val (rhs_cons, rhs_args) =
		    decompose (rhs eq_term, [])
	    in
		if not gl_is_disj then
		    just_do_it lhs_args (asms, gl)
		else if lhs_cons = rhs_cons then
		    (DISJ1_TAC THEN just_do_it lhs_args) (asms, gl)
		else
		    (DISJ2_TAC THEN helper) (asms, gl)
	    end
    in
	if not gl_is_disj then
	    just_do_it lhs_args (asms, gl)
	else if lhs_cons = rhs_cons then
	    (DISJ1_TAC THEN just_do_it lhs_args) (asms, gl)
	else
	    (DISJ2_TAC THEN helper) (asms, gl)
    end

val goal_thm =
    TAC_PROOF (([], goal),
	       REPEAT STRIP_TAC THEN solve_goal_tac)

val mutual_cases =  MP spec_induct goal_thm

in
   {mutual_constructors_distinct = mutual_constructors_distinct,
    mutual_constructors_one_one = mutual_constructors_one_one,
    mutual_cases                = mutual_cases,
    argument_extraction_definitions = argument_extraction_definitions}
end;

val _ = Parse.temp_set_grammars ambient_grammars

end (* ConsThms *)

