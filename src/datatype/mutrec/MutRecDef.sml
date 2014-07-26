(* =====================================================================*)
(* FILE          : mut_rec_ty.sml                                       *)
(* DESCRIPTION   : functor for defining mutually recursive types.       *)
(*                                                                      *)
(* AUTHOR        : Elsa Gunter and Myra VanInwegen, based on comments   *)
(*                 by Tom Melham                                        *)
(* DATE          : 92.08.08                                             *)
(*                                                                      *)
(* MODIFIED      : 93.12.28 Fixed to handle polymorphism. ELG.          *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1992, 1993 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

structure MutRecDef :> MutRecDef =
struct

open MutRecMask;
nonfix quot ;
nonfix rem;
val quot = Int.quot
val rem = Int.rem;
infix 7 quot rem;

open HolKernel Parse basicHol90Lib TypeInfo;

type thm = Thm.thm

val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars boolTheory.bool_grammars;

fun MUT_REC_ERR {function,message} = HOL_ERR{origin_structure = "MutRecDef",
					     origin_function = function,
					     message = message}

(* Some general functions and values we need *)

val num = Type`:num`
val bool = Type.bool
fun mk_fun{Range,Domain} = mk_type{Tyop="fun",Args=[Domain,Range]}
fun dest_fun ty =
    (case dest_type ty
       of {Tyop = "fun", Args = [Domain,Range]}
	   => {Domain = Domain, Range = Range}
	 | _ => raise MUT_REC_ERR {function = "dest_fun",
				   message = "Not a function type"})
fun mk_prod{Fst,Snd} = mk_type{Tyop="prod",Args=[Fst,Snd]}
fun dest_prod ty =
    (case dest_type ty
       of {Tyop = "prod", Args = [Fst,Snd]}
	   => {Fst = Fst, Snd = Snd}
	 | _ => raise MUT_REC_ERR {function = "dest_prod",
				   message = "Not a product type"})
fun mk_sum{Inl,Inr} = mk_type{Tyop="sum",Args=[Inl,Inr]}
fun dest_sum ty =
    (case dest_type ty
       of {Tyop = "sum",Args = [Inl,Inr]}
	   => {Inl = Inl, Inr = Inr}
	 | _ => raise MUT_REC_ERR{function = "dest_sum",
				  message = "Not a sum type"})


(* mk_const {Name = int_to_string n, Ty = num} *)
fun mk_hol_num n = Term.mk_numeral(Arbnum.fromInt n);

fun find test [] = NONE
  | find test (x::xs) = if test x then SOME x else find test xs


(*
 is_closed determines whether there is a witness for each type in the
 arg_info for a constructor.
*)
fun is_closed {constructor_arg_info = [], ...} = true
  | is_closed {constructor_arg_info = (existing ty) :: rest, witnesses} =
      is_closed {constructor_arg_info = rest, witnesses = witnesses}
  | is_closed {constructor_arg_info = (being_defined tyname) :: rest,
	       witnesses} =
      if exists
	  (fn {type_name, witness = {name,arg_info}} => type_name = tyname)
	  witnesses
      then is_closed {constructor_arg_info = rest, witnesses = witnesses}
      else false


(*
 find_witnesses repeatedly searches through all the types and all their
 constructors to find the information necessary to prove the existence
 theorems for all of the types being defined
*)

(*
 Base Case: We have found witnesses for all the types being constructed
*)
fun find_witnesses {seen_new_witness_this_pass,
		    types_to_be_looked_at = [],
		    no_witness_this_pass = [],
		    witnesses} = witnesses

(*
 Next Pass Case: We are done with a pass through the types.  If any new
 witnesses were found then we need to start a new pass looking at all the
 types that still don't have witnesses.  Otherwise, we need to abort.
*)
  | find_witnesses {seen_new_witness_this_pass,
		    types_to_be_looked_at = [],
		    no_witness_this_pass,
		    witnesses} =
    if seen_new_witness_this_pass
	then find_witnesses
	      {seen_new_witness_this_pass = false,
	       types_to_be_looked_at = no_witness_this_pass,
	       no_witness_this_pass = [],
	       witnesses = witnesses}
    else Raise (MUT_REC_ERR {function = "find_witnesses",
			     message = "Not all the types are non-empty."})

(*
 General Case: We need to try to find a witness for a type being defined.
 We need to ask of each of it's constructors, whether there are witnesses
 for each of its argument types (i.e. is th constructor closed in the current
 world).  If we find such a constructor, it is a witness, and so we put it
 with the type being defined into the witnesses, and set the flag
 seen_new_witness_this_pass to true.  If none of the constructors are closed
 yet, we move that type over to no_witness_this_pass, and contintinue with
 the rest of types_to_be_looked_at, leaving seen_new_witness_this_pass alone.
*)
  | find_witnesses {seen_new_witness_this_pass,
		    types_to_be_looked_at =
		      (ty as {type_name, constructors}) :: types,
		    no_witness_this_pass,
		    witnesses} =
    let
	val witness = find
	                (fn {name,arg_info} =>
			 is_closed {constructor_arg_info = arg_info,
				    witnesses = witnesses})
			constructors
    in
	case witness
	  of NONE =>
	      find_witnesses {seen_new_witness_this_pass =
			        seen_new_witness_this_pass,
			      types_to_be_looked_at = types,
			      no_witness_this_pass =
			        ty :: no_witness_this_pass,
			      witnesses = witnesses}
	    | SOME constr =>
		  find_witnesses {seen_new_witness_this_pass = true,
				  types_to_be_looked_at = types,
				  no_witness_this_pass = no_witness_this_pass,
				  witnesses =
				    {type_name = type_name,witness = constr} ::
				    witnesses}
    end;

fun change_arg (existing ty) = SOME ty
  | change_arg (being_defined _) = NONE
fun change_entry {name,arg_info} = {constructor = "JOINT_"^name,
                                    args = map change_arg arg_info,
                                    fixity = Prefix};

fun type_num_aux name num_types_seen [] =
	raise MUT_REC_ERR{function="type_num",
			  message = "name not in type_names"}
      | type_num_aux name num_types_seen (n::ns) =
	if name = n then num_types_seen
	else type_num_aux name (num_types_seen + 1) ns;


(* Big definition *)
fun define_type mut_rec_ty_spec =
let
(* type_names is the list of names of types being defined *)
val type_names = map (#type_name) mut_rec_ty_spec

(*
 The first thing we need to do is to establish that every type that will
 eventually be defined will be non-empty, and to construct the information
 necessary to construct the witnesses to this, after the representing type
 has been built.
*)


(*
 existence_witnesses is a list of the type names together with a descrition
 of a constructor for that type.  The list is given the order in which the
 existence theorems for the mutually recursive types should be proved.  The
 constructor description given with the type name is tthe information
 sufficient for proving the existence theorem for the type, assuming that
 all the existence theorems for the earlier types have already been proven.
*)
val existence_witnesses =
	  rev (find_witnesses {seen_new_witness_this_pass = false,
			       types_to_be_looked_at = mut_rec_ty_spec,
			       no_witness_this_pass = [],
			       witnesses = []})




(* First we'll define a type that is a combinition of all types being
   defined, and use this as a base for defining other types. The name of
   this combinition type (the joint_name) is the concatenation (separated
   by _) of all the type names being defined, preceded by "joint_ty" *)
val joint_name = rev_itlist
                   (fn tyname => fn  str => str ^ "_" ^ tyname)
		   type_names
		   "joint_ty"

(* To make a specification for this combo type, we take all the constructors
   for the individual types, add "JOINT_" to the front, and replace the
   being_defined args of the constructors with our joint type.
*)
val big_simple_spec =
   itlist (fn {constructors,...} => fn part_result =>
             (itlist (fn elt => fn lst => (change_entry elt)::lst)
                     constructors part_result))
 	  mut_rec_ty_spec
 	  [];

val JointTypeAxiom = Define_type.dtype
                     {save_name = joint_name^"_Axiom",
                      ty_name = joint_name,
                      clauses = big_simple_spec}


val joint_type =
    #Domain (dest_fun (type_of (#Bvar (dest_abs (rand (snd (strip_forall
        (concl JointTypeAxiom))))))))

val type_arg_vars = type_vars joint_type;

(* Our next goal is to define a function (called joint_name^"_select",
   I'll refer to it as the joint select function) that, given an item in
   the joint type, will return a number indicating which type (if any) it
   would be if the constructors used to make it had the JOINT_ removed.
   It will return 1 for the first element in type_names, 2 for the
   second, etc, and 0 if the term would not be a well-formed term at all.
   We make it by defining the functions f0, f1, e0, e1, ... (the functions
   and constants, one for each constructor of the joint type, that compute
   return values for the joint select function; I'll refer to them
   as the return functions) in the JointTypeAxiom. *)


(*
 type_num looks up the number associated with a given type
*)

fun type_num name = type_num_aux name 1 type_names


(*
 In order to be able to use JointTypeAxiom, we are going to need values to
 which to specialize the values making up the case statements (i.e. the
 e0, f1, f2, ...).  Each of these functions corresponds to a constructor.
 It takes as arguments first all of the recursive values (ie the values
 gotten by recursively applying the function being defined) for each each of
 recursive types in the arguments to the constructor, next the constructor
 arguments of non-recursive type, and last the constructor arguments of
 recursive type.
*)

(* get_var_info is used to create the variables (and numbers) we will
   need to create the return functions for our joint select function.
   The recN vars returned are the vars representing the return values of
   the recursive calls to the joint select function, the number terms will
   be the values these recursive calls should return for the item to be a
   legitimate member of a particular type, and the xN vars are the vars
   representing the arguments to the constructor the return function
   is for. We build up the being_defined & existing constructor arg lists
   separately since the return functions take the existing args before
   the ones being defined *)

(*
 Base Case: We are through looking at the constructor arguments.  Return the
 information for making the type checks (equations of the form f xi = ni)
 to guarantee that the term is well-formed, and return the variables to
 be abstracted.
*)
fun get_var_info {arg_info =[],
		  type_case_num,
		  var_num,
		  recvar_eq_num_list,
		  being_defined_args,
		  existing_args} =
      {recvar_eq_num_list = rev recvar_eq_num_list,
       plain_then_rec_var_type_info =
         rev (being_defined_args@existing_args)}

(*
 Case: We are looking at an argument of existing type.  We need to generate
 a variable of the existing type from var_num and add it to the
 existing_args.
*)
  | get_var_info {arg_info = (existing ty)::arg_info,
		  type_case_num,
		  var_num,
		  recvar_eq_num_list,
		  being_defined_args,
		  existing_args} =
       get_var_info {arg_info = arg_info,
		     type_case_num = type_case_num,
		     var_num = var_num + 1,
		     recvar_eq_num_list = recvar_eq_num_list,
		     being_defined_args = being_defined_args,
		     existing_args =
		       (mk_var {Name = "x"^(int_to_string var_num),
				Ty = ty})::existing_args}

(*
 Case: We are looking at an argument of a type being defined.  We need to
 generate a variable of type num and record the information for the equation
 that gives well-formedness.   We also need to generate a variable of the
 joint type from var_num and add it to the being_defined_args.
*)
  | get_var_info {arg_info = (being_defined str)::arg_info,
		  type_case_num,
		  var_num,
		  recvar_eq_num_list,
		  being_defined_args,
		  existing_args} =
    let val recvar = mk_var {Name = "rec"^(int_to_string type_case_num),
			     Ty = num}
	val rec_num_term = mk_hol_num (type_num str)
    in
	get_var_info {arg_info = arg_info,
		      type_case_num = type_case_num + 1,
		      var_num = var_num + 1,
		      recvar_eq_num_list =
		        {lhs = recvar, rhs = rec_num_term}::
			recvar_eq_num_list,
		      being_defined_args =
		        (mk_var {Name = "x"^(int_to_string var_num),
				 Ty = joint_type})::being_defined_args,
		      existing_args = existing_args}
    end


    (* if constructor has no args, the return "function" is just a constant *)
fun make_return_ftn {name, arg_info = []} type_num = mk_hol_num type_num

    (* if the constructor has args, get variables (and numbers) to
       correspond to return values of recursive calls and variables
       to correspond to arguments of the constructor *)
  | make_return_ftn {name, arg_info} type_num =
    let val {recvar_eq_num_list, plain_then_rec_var_type_info} =
	      get_var_info {arg_info = arg_info,
			    type_case_num = 1,
			    var_num = 1,
			    recvar_eq_num_list = [],
			    being_defined_args = [],
			    existing_args = []}
	val body =
	    (* if all the args are existing types, then the body of
	       our return function will be just a constant giving the
	       type; otherwise we need to test that the return values
	       of the recursive calls are what we expect *)
	    if recvar_eq_num_list = nil then
		mk_hol_num type_num
	    else
		mk_cond {cond = list_mk_conj (map mk_eq recvar_eq_num_list),
			 larm = mk_hol_num type_num,
			 rarm = mk_hol_num 0}
    in
	list_mk_abs (map (#lhs) recvar_eq_num_list,
		     list_mk_abs (plain_then_rec_var_type_info, body))
    end

fun make_return_ftns ({type_name, constructors}::spec) n =
     (map (fn c => make_return_ftn c n) constructors)@
     make_return_ftns spec (n + 1)
  | make_return_ftns [] n = []


(* fn_lemma says there exists a unique function satisfying the
   desired properties of our joint selection function *)
val fn_lemma =
    CONV_RULE (DEPTH_CONV BETA_CONV)
              (ISPECL (make_return_ftns mut_rec_ty_spec 1) JointTypeAxiom)

(* we want to make a name, joint_name ^ "_select", for the fn in fn_lemma *)
val joint_select_name = joint_name ^ "_select"

(* define our joint_select function *)
val joint_select_def =
    new_specification {name = joint_name ^ "_select_DEF",
		       consts = [{fixity = Prefix,
				  const_name = joint_select_name}],
		       sat_thm = EXISTENCE fn_lemma}


(* make a constant for our joint select function *)
val joint_select = mk_const {Name = joint_select_name,
			     Ty = mk_fun {Domain = joint_type,
					  Range = num}}

(*
  Next we make the predicates for representing the types to be defined,
  prove the existence theorems for those predicates, define the types,
  and define the REP and ABS functions.
*)
val Joint_x = mk_var {Name = "x", Ty = joint_type}

fun joint_select_x ty_name =
    {Bvar = Joint_x,
     Body = mk_eq {lhs = mk_comb {Rator = joint_select, Rand = Joint_x},
		   rhs = mk_hol_num (type_num ty_name)}}

fun mk_joint_arg_ty_and_arg (existing ty) =
    {ty = ty,
     arg = mk_select{Bvar = mk_var{Name = "x", Ty = ty},
		     Body = mk_const{Name = "T", Ty = bool}}}
  | mk_joint_arg_ty_and_arg (being_defined ty_name) =
    {ty = joint_type,
     arg = mk_select (joint_select_x ty_name)}

fun prove_exists
    {type_name, witness = {arg_info,name}}
    {exist_thms, prop_thms}=
    let
	val {args, ty} =
	    itlist
	    (fn ty_info => fn {args, ty} =>
	     let
		 val next = mk_joint_arg_ty_and_arg ty_info
	     in
		 {args = (#arg next) :: args,
		  ty = mk_fun {Domain = (#ty next), Range = ty}}
	     end)
	    arg_info
	    {args = [], ty = joint_type}
	val witness =
	    list_mk_comb ((mk_const{Name = "JOINT_"^name, Ty = ty}),args)
	val goal = ([],mk_exists (joint_select_x type_name))
	val tac = (EXISTS_TAC witness) THEN
	    (REWRITE_TAC (joint_select_def::prop_thms))
	val ethm = TAC_PROOF(goal,tac)
	    val pthm = SELECT_RULE ethm
    in
	{exist_thms = {type_name = type_name, exists_thm = ethm} ::
	               exist_thms,
	 prop_thms = pthm :: prop_thms}
    end

(*
 Here are the existence theorems
*)

val {exist_thms = existence_thms,...} =
    rev_itlist
    prove_exists
    existence_witnesses
    {exist_thms = [], prop_thms = []}


fun mk_abs_name tyname = tyname ^ "_abs"
fun mk_rep_name tyname = tyname ^ "_rep"
fun mk_bij_name tyname = tyname ^ "_REP_ABS"

fun rev_map_aux f acc [] = acc
  | rev_map_aux f acc (x::xs) = rev_map_aux f ((f x)::acc) xs

fun rev_map f l = rev_map_aux f [] l


(*
 Here is the WONDERFUL computation of the type definitions and the REP
 and ABS functions
*)

val ty_defs =
    rev_map
    (fn {exists_thm, type_name} =>
     let
	 val pred = (rand o concl) exists_thm
	 val sel = mk_exists {Bvar = Joint_x,
			      Body = mk_comb{Rator = pred, Rand = Joint_x}}
	 val inhab_thm =
	       EQ_MP (SYM (DEPTH_CONV BETA_CONV sel)) exists_thm
	 val type_def = new_type_definition{inhab_thm = inhab_thm,
					    name  =  type_name,
					    pred = pred}
	 val new_type =
	     #Domain(dest_fun (type_of (#Bvar(dest_exists (concl type_def)))))
	 val rep_name = mk_rep_name type_name
	 val abs_name = mk_abs_name type_name
	 val rep_abs_thm =
	       define_new_type_bijections {name = mk_bij_name type_name,
					   ABS = abs_name,
					   REP = rep_name,
					   tyax = type_def}
	 val rep = mk_const{Name = rep_name,
			    Ty = mk_fun {Domain = new_type,
					 Range = joint_type}}
	 val abs = mk_const{Name = abs_name,
			    Ty = mk_fun {Domain = joint_type,
					 Range = new_type}}
     in
	 {type_name = type_name,
	  new_type = new_type,
	  rep_abs_thm = rep_abs_thm,
	  rep = rep, abs = abs}
     end)
    existence_thms


(* Now we have to define all the constructors for the individual types.
   We make them from the constructors for the joint type, with some
   *_abs and *_rep functions thrown in for typecasting. All of the functions
   up to define_constructors are essentiall helper functions *)

(* mk_constructor_app makes a constructor and creates variables of the
   right type for it to be applied to, applies it to the variables,
   returns the applied constructor and list of vars that were created. *)
fun mk_constructor_app type_name {name, arg_info} =
    let
	val result_type = mk_type {Tyop=type_name,Args=type_arg_vars}
	val (constructor_type, dom_ty_list) =
	    itlist
	    (fn (existing ty) =>
	            (fn (range_ty, dom_ty_list) =>
		     (mk_fun{Domain = ty, Range = range_ty},
		      ty::dom_ty_list))
	      | (being_defined str) =>
		    (fn (range_ty, dom_ty_list) =>
		     let val ty = mk_type{Tyop = str, Args = type_arg_vars}
		     in
			 (mk_fun{Domain = ty, Range = range_ty},
			  ty::dom_ty_list)
		     end))
	    arg_info
	    (result_type,[])
	val constructor = mk_var {Name = name, Ty = constructor_type}
	fun mk_c_app C_app [] n vars_seen =
	    {Applied_Constructor = C_app, Var_Args = rev vars_seen}
	  | mk_c_app C_app (ty::tys) n vars_seen =
	    let val v = mk_var{Name = ("x"^(int_to_string n)), Ty = ty}
	    in mk_c_app
		(mk_comb {Rator = C_app, Rand = v})
		tys
		(n + 1)
		(v::vars_seen)
	    end
    in
	mk_c_app constructor dom_ty_list 1 []
    end

(* apply_constructor takes a constructor name, the args it's to be applied
   to, and the type the result should be after it's applied, creates a
   constant for the constructor and applies it *)
fun apply_constructor (cons_name, result_type, args) =
    let val constructor_type =
	     foldr (fn (arg, range_ty) => mk_fun{Domain = type_of arg,
						 Range = range_ty})
	           result_type
                   args
	fun apply_args (tm, []) = tm
	  | apply_args (tm, first_arg :: rest_args) =
	       apply_args (mk_comb {Rator = tm, Rand = first_arg},
			   rest_args)
    in
	apply_args (mk_const {Name = cons_name, Ty = constructor_type},
		    args)
    end

(* get_type returns the type of the given type_name *)
fun get_type str =
    (case find (fn entry => str = #type_name entry) ty_defs
       of SOME entry => #new_type entry
	| NONE => raise MUT_REC_ERR{function = "mk_case",
				    message = "Impossible"})

(* get_abs returns the abstraction function associated with type of tyname *)
fun get_abs tyname =
    let fun helper ({type_name, abs, rep, new_type, rep_abs_thm}::names) =
	      if tyname = type_name then abs
	      else helper names
	  | helper (_) = raise MUT_REC_ERR
	        {function = "get_abs", message = "no abs for " ^ tyname}
    in
	helper ty_defs
    end

(* get_rep returns the representation function associated with tyname *)
fun get_rep tyname =
    let fun helper ({type_name, abs, rep, new_type, rep_abs_thm}::names) =
	      if tyname = type_name then rep
	      else helper names
	  | helper (_) = raise MUT_REC_ERR
	        {function = "get_rep", message = "no rep for " ^ tyname}
    in
	helper ty_defs
    end

(* the joint constructor must be applied to the variables returned by
   mk_constructor_app, so the variables that are of types being defined
   must be coerced to be in the joint type *)
fun coerce_arg (arg, existing ty) = arg
  | coerce_arg (arg, being_defined tyname) =
      mk_comb {Rator = get_rep tyname, Rand = arg}

(* define_constructor does the coersions, assembles the definitions, and
   defines one constructor for the type with name tyname *)
fun define_constructor tyname (cons_info as {name, arg_info}) =
    let val {Applied_Constructor = lhs, Var_Args} =
	      mk_constructor_app tyname cons_info
	val args_of_joint_cons = map coerce_arg
	                             (combine (Var_Args, arg_info))
	val applied_joint_cons = apply_constructor
	      ("JOINT_" ^ name, joint_type, args_of_joint_cons)
	val cons_def = mk_eq {lhs = lhs,
			      rhs = mk_comb {Rator = get_abs tyname ,
					     Rand = applied_joint_cons}}
    in
	(new_definition (name ^ "_DEF", cons_def); ())
    end

(* the purpose of define_constructors is to essentially feed info to
   define_constructor *)
fun define_constructors (tyname, cons_info::more_info, type_data) =
    (define_constructor tyname (cons_info);
     define_constructors (tyname, more_info, type_data))
  | define_constructors (tyname, [], {type_name, constructors}::more_data) =
      define_constructors (type_name, constructors, more_data)
  | define_constructors (tyname, [], []) = ()

val _ = define_constructors ("", [], mut_rec_ty_spec)



(*
 Having defined the individual types and the constructors for those types,
 we next need to prove the theorem that allows us to define functions by
 mutual recursion over these types.  The theorem states that given the
 cases for a mutually recursive definition, there exists a unique collection
 of functions satisfying the mutually recursive definition.

 In order to prove such a theorem, we are going to need to use JointTypeAxiom
 again.  In order to be to use JointTypeAxiom, we are going to need values
 to which to specialize the case statements.
*)

(*
 sum_type is the disjoint sum of all the range types of the functions being
 defined by mutual recursion
*)


    val ord_a = 97
    fun name_of_num n =
	if n < 26 then Char.toString(Char.chr(n + ord_a))
	else name_of_num ((n quot 26) - 1)
             ^ Char.toString(Char.chr((n rem 26) + ord_a))

    fun mk_new_tyvar_name {type_num, avoiding_tyvar_names} =
	let val new_tyvar_name = "'" ^ (name_of_num type_num)
	in
	    if Lib.mem new_tyvar_name avoiding_tyvar_names
		then mk_new_tyvar_name {type_num = type_num +1,
				       avoiding_tyvar_names =
				        avoiding_tyvar_names}
	    else {next_type_num = type_num + 1, new_type_name = new_tyvar_name}
	end
    fun get_sum_type {type_names = [], types_made = [], ...} =
	raise MUT_REC_ERR{function = "get_sum_type", message = "No types!?!"}
      | get_sum_type {type_names = [], types_made = inl::rest, type_num} =
	rev_itlist
	(fn Inl => fn Inr => mk_sum{Inl = Inl, Inr = Inr})
	rest
	inl

      | get_sum_type {type_names = (type_name::type_names),
		      types_made,
		      type_num} =
	let

	    val {new_type_name, next_type_num} =
		mk_new_tyvar_name {type_num = type_num,
				  avoiding_tyvar_names =
				   map Type.dest_vartype type_arg_vars}
	    val new_type = mk_vartype new_type_name
	in
	    get_sum_type {type_names = type_names,
			  types_made = new_type :: types_made,
			  type_num = next_type_num}
	end

    val sum_type = get_sum_type {type_names = type_names,
				 types_made = [],
				 type_num = 0}


(*
 Ins_Outs is a table of the range type (type_summand) associated with a
 type name and the list of INR(L)s and OUTR(L)s need to inject that type
 into the sum_type and project it out.
*)

    fun mk_rights [] =
	raise  MUT_REC_ERR
	    {function = "mk_rights", message = "Impossible"}
      | mk_rights [last] = {Ins = [], Outs = []}
      | mk_rights (ty1::(tys as ty2::_)) =
	let
	    val {Ins, Outs} = mk_rights tys
	in
	    {Ins =
	     (mk_const{Name = "INR", Ty = mk_fun{Domain = ty1, Range = ty2}})
	     :: Ins,
	     Outs =
	     (mk_const{Name = "OUTR", Ty = mk_fun{Domain = ty2, Range = ty1}})
	     :: Outs}
	end

    fun get_ins_outs {type_names = [],...} =
	raise  MUT_REC_ERR
	    {function = "get_ins_outs", message = "Impossible - No type names"}
      | get_ins_outs {sum_types = [], ...} =
	raise  MUT_REC_ERR
	    {function = "get_ins_outs", message = "Impossible - No types"}
      | get_ins_outs {type_names = [last], sum_types = [ty]} =
	let val id = mk_const {Name = "I", Ty = mk_fun{Domain=ty, Range=ty}}
	in
	    [{type_name = last, type_summand = ty, Ins = [id], Outs = [id]}]
	end
      | get_ins_outs {type_names = [last], sum_types = tys as ty1 :: _} =
	let
	    val {Ins, Outs} = mk_rights tys
	in
	    [{type_name = last,
	      type_summand = ty1,
	      Ins = Ins,
	      Outs = Outs}]
	end
      | get_ins_outs {type_names = type_name :: type_names,
		      sum_types = tys as ty1 :: _} =
	let
	    val {Ins, Outs} = mk_rights tys
	    val {Inl = type_summand, Inr = top_sum_type} = dest_sum ty1
	    val Inl = mk_const{Name = "INL",
			       Ty = mk_fun{Domain = type_summand, Range = ty1}}
	    val Outl = mk_const{Name = "OUTL",
				Ty = mk_fun{Domain = ty1,
					    Range = type_summand}}
	    val ins_outs = get_ins_outs {type_names = type_names,
					 sum_types = top_sum_type :: tys}
	in
	    {type_name = type_name,
	     type_summand = type_summand,
	     Ins = Inl :: Ins,
	     Outs = Outl :: Outs}
	    :: ins_outs
	end

val Ins_Outs = get_ins_outs{type_names = type_names,sum_types = [sum_type]}


fun new_list_mk_conj [] = mk_const{Name = "T", Ty = bool}
  | new_list_mk_conj l = list_mk_conj l

val JointProp = mk_var{Name = "Prop",
		       Ty = mk_fun{Domain = joint_type, Range = bool}}

fun new_ty_Prop type_name = mk_var{Name = type_name^"_Prop",
				   Ty = mk_fun {Domain = get_type type_name,
						Range = bool}}

fun joint_select_x ty_name =
    mk_eq {lhs = mk_comb {Rator = joint_select, Rand = Joint_x},
	   rhs = mk_hol_num (type_num ty_name)}


(*
 mk_case_aux is used to create the types, variables and arguments we will
 need to create the return functions for our joint mutual recursion function.
 The summand_types are the recursive argument types to the case, the
 exisiting_types are the types of the arguments to the operators of
 previously existing type, and the being_defined_types are the types of the
 arguments to the operators of types that are being defined.  The rec_vars
 returned are the vars representing the return values (of sum_type) of the
 recursive call to the joint function, the plain_vars are the vars
 representing the arguments to the operators of existing type, the new_ty_vars
 are the vars representing arguments to the operators of types being defined,
 and the joint_ty_vars are the vars representing arguments to the operators of
 the joint type.  The  new_ty_const_arg_vars are all the variable arguments
 to the operators of the types being defined and the joint_constructor_arg_vars
 are all the variable arguments to the operators of the joint type.  The
 abs_args are the abstractions from the joint type to the specific new types
 and the proj_args are the projections from the sum_type to the individual
 result types the mutually recursive functions being defined.
 exists_specl is the set of specializations for the conjuncts.
*)

(*
 Base Case: We are through looking at the constructor arguments.  Return the
 case information.
*)


fun mk_case_aux {arg_info = [] : type_info list,
		 constructor_name : string,
		 type_name : string,
		 xy_var_num : int,
		 rec_var_num : int,
		 summand_types : hol_type list,
		 existing_types : hol_type list,
		 being_defined_types : hol_type list,
		 rec_vars : term list,
		 new_ty_vars : term list,
		 joint_ty_vars : term list,
		 proj_args : term list,
		 plain_vars : term list,
		 abs_args : term list,
		 exists_specl : term list,
		 new_ty_const_arg_vars : term list,
		 new_ty_const_arg_types : hol_type list,
		 new_ty_props : term list,
		 joint_constructor_arg_types : hol_type list,
		 joint_constructor_arg_vars : term list,
		 joint_induct_rec_vars :term list} =
    let
	val {type_summand,Ins,...} =
	    case find (fn entry => type_name = #type_name entry) Ins_Outs
	      of SOME entry => entry
	       | NONE => raise MUT_REC_ERR{function = "mk_case",
					   message = "Impossible"}
	fun rev_list_mk_fun {Domain_list, Range}=
	    rev_itlist
	    (fn Domain => fn Range =>
	     (mk_fun {Domain = Domain, Range = Range}))
	    Domain_list
	    Range
	val case_type =
	    rev_list_mk_fun
	    {Domain_list = summand_types,
	     Range = rev_list_mk_fun
	             {Domain_list = existing_types,
		      Range = rev_list_mk_fun
	                      {Domain_list = being_defined_types,
			       Range = type_summand}}}
	val case_var = mk_var{Name = constructor_name^"_case",Ty = case_type}
	val sym_cons_def =
	    GEN_ALL(SYM(SPEC_ALL
	      (definition (constructor_name^"_DEF"))))
	val Body =
	    rev_itlist
	    (fn Rator => fn Rand => mk_comb{Rator = Rator, Rand = Rand})
	    Ins
	    (list_mk_comb
	     (list_mk_comb
	      (list_mk_comb (case_var,rev proj_args),
	       rev plain_vars),
	      rev abs_args))
	fun rev_list_mk_abs {Bvars, Body} =
	    rev_itlist
	    (fn Bvar => fn Body => mk_abs{Bvar = Bvar, Body = Body})
	    Bvars
	    Body
	val exists_case_fn =
	    rev_list_mk_abs
	    {Bvars = rec_vars,
	     Body = rev_list_mk_abs
	            {Bvars = plain_vars,
		     Body = rev_list_mk_abs
		            {Bvars = joint_ty_vars,
			     Body = Body}}}
	val new_ty_const_args = rev new_ty_const_arg_vars
	val applied_constructor =
	    list_mk_comb
	    (mk_const{Name = constructor_name,
		      Ty = rev_list_mk_fun
		      {Domain_list = new_ty_const_arg_types,
		       Range = get_type type_name}},
	     new_ty_const_args)
	val new_ty_induct_case =
	    list_mk_forall(new_ty_const_args,
			   mk_imp{ant = new_list_mk_conj (rev new_ty_props),
				  conseq =
				     mk_comb {Rator = (new_ty_Prop type_name),
					      Rand = applied_constructor}})
	val joint_cons_args = rev joint_constructor_arg_vars
	val applied_joint_constructor =
	    list_mk_comb
	    (mk_const{Name = "JOINT_"^constructor_name,
		      Ty = rev_list_mk_fun
		      {Domain_list = joint_constructor_arg_types,
		       Range = joint_type}},
	     joint_cons_args)
	val joint_induction_case =
	    rev_list_mk_abs
	    {Bvars = joint_induct_rec_vars,
	     Body = rev_list_mk_abs
	            {Bvars = plain_vars,
		     Body = rev_list_mk_abs
		            {Bvars = joint_ty_vars,
			     Body =
			     mk_cond {cond = new_list_mk_conj
				             joint_induct_rec_vars,
				      larm = mk_const{Name="T",Ty = bool},
				      rarm =
				      mk_comb{Rator = JointProp,
					      Rand =
					      applied_joint_constructor}}}}}
	val select_exists_term =
	    list_mk_exists
	    (new_ty_const_args,
	     mk_eq {lhs = mk_comb{Rator = get_abs type_name, Rand = Joint_x},
		    rhs = applied_constructor})
    in
	{type_name = type_name,
	 case_var = case_var,
	 exists_case_fn = exists_case_fn,
	 exists_specl = rev exists_specl,
	 new_ty_const_arg_vars = new_ty_const_args,
	 joint_induction_case = joint_induction_case,
	 select_exists_term = select_exists_term,
	 applied_joint_constructor = applied_joint_constructor,
	 sym_cons_def = sym_cons_def,
	 new_ty_induct_case = new_ty_induct_case}
    end

(*
 Case: We are looking at an argument of existing type.  We need to generate
 a variable of the existing type from var_num and add it to both plain_vars
 and arg_vars.
*)
  | mk_case_aux {arg_info = (existing ty)::arg_info,
		 constructor_name,
		 type_name,
		 xy_var_num,
		 rec_var_num,
		 summand_types,
		 existing_types,
		 being_defined_types,
		 rec_vars,
		 new_ty_vars,
		 joint_ty_vars,
		 proj_args,
		 plain_vars,
		 abs_args,
		 exists_specl,
		 new_ty_const_arg_vars,
		 new_ty_const_arg_types,
		 new_ty_props,
		 joint_constructor_arg_types,
		 joint_constructor_arg_vars,
		 joint_induct_rec_vars} =
    let
	val xN = mk_var {Name = "x"^(int_to_string xy_var_num),
			 Ty = ty}
    in
	mk_case_aux {arg_info = arg_info,
		     type_name = type_name,
		     constructor_name = constructor_name,
		     xy_var_num = xy_var_num + 1,
		     rec_var_num = rec_var_num,
		     summand_types = summand_types,
		     existing_types = ty :: existing_types,
		     being_defined_types = being_defined_types,
		     rec_vars = rec_vars,
		     new_ty_vars = new_ty_vars,
		     joint_ty_vars = joint_ty_vars,
		     proj_args = proj_args,
		     plain_vars = xN :: plain_vars,
		     abs_args = abs_args,
		     exists_specl = xN :: exists_specl,
		     new_ty_const_arg_vars = xN :: new_ty_const_arg_vars,
		     new_ty_const_arg_types =
		       ty :: new_ty_const_arg_types,
		     new_ty_props = new_ty_props,
		     joint_constructor_arg_types =
		       ty :: joint_constructor_arg_types,
		     joint_constructor_arg_vars =
		       xN :: joint_constructor_arg_vars,
		     joint_induct_rec_vars = joint_induct_rec_vars}
    end

(*
 Case: We are looking at an argument of a type being defined.  We need to
 generate a variable recN of type sum_type from rec_var_num and add it to
 rec_vars.  We need to project it onto the appropriate type_summand, add the
 projection onto proj_args and the type_summand onto summand_types.  We need
 to generate a variable xN of the  joint type from var_num and add it to the
 arg_vars.  We need to abstract it from the joint type to the type being
 defined and add it to the abs_args.  We need to add the type being defined
 to being_defined_types.
*)
  | mk_case_aux {arg_info = (being_defined str)::arg_info,
		 type_name,
		 constructor_name,
		 xy_var_num,
		 rec_var_num,
		 summand_types,
		 existing_types,
		 being_defined_types,
		 rec_vars,
		 new_ty_vars,
		 joint_ty_vars,
		 proj_args,
		 plain_vars,
		 abs_args,
		 exists_specl,
		 new_ty_const_arg_vars,
		 new_ty_const_arg_types,
		 new_ty_props,
		 joint_constructor_arg_types,
		 joint_constructor_arg_vars,
		 joint_induct_rec_vars} =
    let
	val M = int_to_string rec_var_num
	val recM = mk_var {Name = "rec"^M, Ty = sum_type}
	val joint_induct_recM = mk_var {Name = "rec"^M, Ty = bool}
	val {type_summand,Outs,...} =
	    case find (fn entry => str = #type_name entry) Ins_Outs
	      of SOME entry => entry
	       | NONE => raise MUT_REC_ERR{function = "mk_case",
					   message = "Impossible"}
	val proj =
	    itlist
	    (fn Rator => fn Rand => mk_comb{Rator = Rator, Rand = Rand})
	    Outs
	    recM
	val {new_type = being_defined_type, abs, rep,...} =
	    case find (fn entry => str = #type_name entry) ty_defs
	      of SOME entry => entry
	       | NONE => raise MUT_REC_ERR{function = "mk_case",
					   message = "Impossible"}
	val N = int_to_string xy_var_num
	val xN = mk_var {Name = "x"^N, Ty = being_defined_type}
	val yN = mk_var {Name = "y"^N, Ty = joint_type}
	val abs_arg = mk_comb{Rator = abs, Rand = yN}
	val rep_arg = mk_comb{Rator = rep, Rand = xN}
	val new_ty_prop = mk_comb {Rator = (new_ty_Prop str), Rand = xN}
    in
	mk_case_aux {arg_info = arg_info,
		     type_name = type_name,
		     constructor_name = constructor_name,
		     xy_var_num = xy_var_num + 1,
		     rec_var_num = rec_var_num + 1,
		     summand_types = type_summand :: summand_types,
		     existing_types = existing_types,
		     being_defined_types =
		       being_defined_type :: being_defined_types,
		     rec_vars = recM :: rec_vars,
		     new_ty_vars = xN :: new_ty_vars,
		     joint_ty_vars = yN :: joint_ty_vars,
		     proj_args = proj :: proj_args,
		     plain_vars = plain_vars,
		     abs_args = abs_arg :: abs_args,
		     exists_specl = rep_arg :: exists_specl,
		     new_ty_const_arg_vars = xN :: new_ty_const_arg_vars,
		     new_ty_const_arg_types =
		       being_defined_type :: new_ty_const_arg_types,
		     new_ty_props = new_ty_prop :: new_ty_props,
		     joint_constructor_arg_types =
		       joint_type :: joint_constructor_arg_types,
		     joint_constructor_arg_vars =
		       yN :: joint_constructor_arg_vars,
		     joint_induct_rec_vars =
		       joint_induct_recM :: joint_induct_rec_vars}
    end

fun mk_case {type_name, constructor_name,arg_info} =
    mk_case_aux {arg_info = arg_info,
		 type_name = type_name,
		 constructor_name = constructor_name,
		 xy_var_num = 1,
		 rec_var_num = 1,
		 summand_types = [],
		 existing_types = [],
		 being_defined_types = [],
		 rec_vars = [],
		 new_ty_vars = [],
		 joint_ty_vars = [],
		 proj_args = [],
		 plain_vars = [],
		 abs_args = [],
		 exists_specl = [],
		 new_ty_const_arg_vars = [],
		 new_ty_const_arg_types = [],
		 new_ty_props = [],
		 joint_constructor_arg_types = [],
		 joint_constructor_arg_vars = [],
		 joint_induct_rec_vars = []}


val spec_cases =
    itlist
    (fn {type_name, constructors} => fn l =>
     (itlist
      (fn {name,arg_info} => fn l =>
       (mk_case {type_name = type_name,
		 constructor_name = name,
		 arg_info = arg_info})::l)
      constructors
      []) @ l)
    mut_rec_ty_spec
    []

val th1 = BETA_RULE
          (rev_itlist
	   (fn {exists_case_fn,...} => (fn thm => ISPEC exists_case_fn thm))
	   spec_cases
	   JointTypeAxiom)

val (Exists, Unique) = CONJ_PAIR (EQ_MP (EXISTS_UNIQUE_CONV (concl th1)) th1)

val P = #Rand (dest_comb(concl th1))
val {Bvar = f,Body} = dest_abs P

val mod_fns =
    map
    (fn type_name =>
     let
	 val {new_type = being_defined_type, rep,...} =
	     case find (fn entry => type_name = #type_name entry) ty_defs
	       of SOME entry => entry
		| NONE => raise MUT_REC_ERR{function = "",
					    message = "Impossible"}
	 val x =  mk_var {Name = "x", Ty = being_defined_type}
	 val {Outs,...} =
	     case find (fn entry => type_name = #type_name entry) Ins_Outs
	       of SOME entry => entry
		| NONE => raise MUT_REC_ERR{function = "",
					   message = "Impossible"}
	 val lambda =
	     mk_abs{Bvar = x,
		    Body =
		    itlist
		    (fn Rator => fn Rand =>
		     mk_comb{Rator = Rator, Rand = Rand})
		    Outs
		    (mk_comb{Rator = f,
			     Rand = (mk_comb{Rator = rep, Rand = x})})}
	 val beta_thm =
	     GEN x (SYM (BETA_CONV (mk_comb{Rator = lambda, Rand = x})))
     in
	 {lambda = lambda, beta_thm = beta_thm}
     end)
    type_names

val rep_abs_thms =
    map
    (fn type_name =>
     (case find (fn entry => type_name = #type_name entry) ty_defs
	  of SOME entry => BETA_RULE (#rep_abs_thm entry)
	       | NONE => raise MUT_REC_ERR{function = "",
					        message = "Impossible"}))
    type_names

val abs_rep_thms = map CONJUNCT1 rep_abs_thms

val elim_cons_thms =
    itlist
    (fn {type_name, constructors} => fn l =>
     let
	 val cons_REP_ABS =
	     CONJUNCT2 (definition (mk_bij_name type_name))
	 val {abs = cons_abs, rep = cons_rep,...} =
	     case find (fn entry => type_name = #type_name entry) ty_defs
	       of SOME entry => entry
		| NONE => raise MUT_REC_ERR{function = "",
					    message = "Impossible"}
     in
	 (itlist
	  (fn {name,arg_info} => fn l =>
	   let
	       val cons_def = definition (name^"_DEF")
	       val sym_cons_def =
		   SYM (AP_TERM cons_rep (SPEC_ALL cons_def))
	       val r = rand(rand(lhs(concl sym_cons_def)))
	       val spec_REP_ABS = BETA_RULE (SPEC r cons_REP_ABS)
	       val select_thm =
		   TAC_PROOF(([],(lhs(concl spec_REP_ABS))),
			     ((PURE_ONCE_REWRITE_TAC [joint_select_def]) THEN
			      REWRITE_TAC rep_abs_thms))
	       val joint_elim_thm = (PURE_ONCE_REWRITE_RULE [sym_cons_def]
				     (EQ_MP spec_REP_ABS select_thm))
	       val cons_elim_thm = (PURE_ONCE_REWRITE_RULE abs_rep_thms
				    (AP_TERM cons_abs joint_elim_thm))

	   in
	       {type_name = type_name,
		joint_elim_thm = SYM joint_elim_thm,
		cons_elim_thm = cons_elim_thm} :: l
	   end)
	 constructors
	 [])
     end @ l)
    mut_rec_ty_spec
    []

(* Do the generalization while you are at it *)
fun map3 f [] [] [] = []
  | map3 f (x1::l1) (x2::l2) (x3::l3) = (f x1 x2 x3)::(map3 f l1 l2 l3)
  | map3 f _ _ _ = raise MUT_REC_ERR{function = "map3",
				     message = "Unbalanced lists (impossible)"}

val OUTL = sumTheory.OUTL
val OUTR = sumTheory.OUTR
val II_THM = prove((--`!x:'a. I (I x) = x`--),
		   REWRITE_TAC[combinTheory.I_THM]);


    fun abs_every tm1 var tm2 frees =
	    if tm1 = tm2 then var
	    else if is_var tm2 then tm2
	    else if is_const tm2 then tm2
	    else if is_comb tm2
		     then mk_comb{Rator = abs_every tm1 var (rator tm2) frees,
				  Rand = abs_every tm1 var (rand tm2) frees}
	    else
		let val {Bvar, Body} = dest_abs tm2
		in if mem Bvar frees then tm2
		   else mk_abs {Bvar = Bvar,
				Body = abs_every tm1 var Body frees}
		end

fun abstract_every tm1 v tm2 =
    let val var = variant (all_vars tm2) v
	val frees = free_vars tm1
	in
	    abs_every tm1 var tm2 frees
    end


fun EX n [] thm = {fns = [], ext_thm = thm}
  | EX n (tm::tms) thm =
    let
	val f = mk_var {Name = "fn"^(int_to_string n), Ty = type_of tm}
	val {fns, ext_thm} = EX (n+1) tms thm
	val pattern = mk_exists{Bvar = f,
				Body = abstract_every tm f (concl ext_thm)}
    in
	{fns = f :: fns, ext_thm = EXISTS (pattern,tm) ext_thm}
    end

val {ext_thm = ext_thm, fns} =
    EX 1 (map #lambda mod_fns)
    (LIST_CONJ
     (map3
      (fn {type_name, joint_elim_thm,...} =>
       let
	   val {Outs,...} =
	       case find (fn entry => type_name = #type_name entry) Ins_Outs
		 of SOME entry => entry
		  | NONE => raise MUT_REC_ERR{function = "",
					      message = "Impossible"}
       in
	   fn {exists_specl, new_ty_const_arg_vars, ...} => fn thm =>
	   GENL new_ty_const_arg_vars
	   (PURE_ONCE_REWRITE_RULE (map (#beta_thm) mod_fns)
	    (PURE_REWRITE_RULE (II_THM::OUTL::OUTR::abs_rep_thms)
	     (itlist AP_TERM Outs
	      (PURE_ONCE_REWRITE_RULE [joint_elim_thm]
	       (SPECL exists_specl thm)))))
       end)
	      elim_cons_thms
	      spec_cases
	      (CONJUNCTS (ASSUME Body))))
val lemma =
    TAC_PROOF
    (([],
      (--`!(P:'a -> bool) (Q:bool). (?x.P x) ==> ((!x.P x ==> Q) ==> Q)`--)),
     ((REPEAT STRIP_TAC) THEN RES_TAC))

val Q = concl ext_thm
val cases = map (#case_var) spec_cases

val New_Ty_Existence_Thm =
    GENL cases
    (MP (MP (BETA_RULE (ISPECL [P, Q] lemma)) Exists)
     (GEN f (DISCH_ALL ext_thm)))


val IfThenElse_Imp =
    prove ((--`!A B. (B = (if A then T else B)) = (A ==> B)`--),
	   ((REPEAT STRIP_TAC )THEN
	    (ASM_CASES_TAC (--`A:bool`--)) THEN
	    (ASM_REWRITE_TAC [])))

val JointInduct =
let
    val th =
	CONJUNCT2
	(CONV_RULE EXISTS_UNIQUE_CONV
	 (BETA_RULE
	  (rev_itlist
	   (fn {joint_induction_case,...} =>
	    (fn thm => ISPEC joint_induction_case thm))
	   spec_cases
	   JointTypeAxiom)))
    val f = #Bvar (dest_forall (concl th))
in
    GEN JointProp
    (REWRITE_RULE [IfThenElse_Imp]
    (BETA_RULE
    (CONV_RULE (ONCE_DEPTH_CONV FUN_EQ_CONV)
      (SPECL
       [JointProp,
	(mk_abs{Bvar = Joint_x, Body = mk_const{Name = "T", Ty =bool}})]
       th))))
end


val lemma =
    prove((--`!b f s:'a. ((if b then f else s) = f) = ((f = s) \/ b)`--),
	  ((REPEAT GEN_TAC) THEN EQ_TAC THEN COND_CASES_TAC THEN
	   (REWRITE_TAC []) THEN STRIP_TAC THEN (ASM_REWRITE_TAC[])))

val rep_abs_eq_simps =
    map
    (fn {type_name,applied_joint_constructor,...} =>
     (REWRITE_RULE rep_abs_thms
      (CONV_RULE (DEPTH_CONV reduceLib.NEQ_CONV)
       (REWRITE_RULE [lemma,joint_select_def]
	(SYM (SPEC applied_joint_constructor
	      (CONJUNCT2 (List.nth
                  ((rep_abs_thms,(type_num type_name) - 1))))))))))
    spec_cases


fun non_diag_map p f [] = []
  | non_diag_map p f (x::xs) =
      if p x then non_diag_map p f xs
      else (f x)::(non_diag_map p f xs)

val not_rep_abs_thms =
    flatten
    (map
     (fn {type_name, applied_joint_constructor, ...} =>
      non_diag_map
      (fn tyn => (tyn = type_name))
      (fn ty_name =>
       prove
       (mk_neg(mk_eq{lhs = mk_comb{Rator = get_rep ty_name,
				   Rand = mk_comb{Rator = get_abs ty_name,
						  Rand =
						  applied_joint_constructor}},
		     rhs = applied_joint_constructor}),
	((PURE_ONCE_REWRITE_TAC
	  (map (SYM o SPEC_ALL o CONJUNCT2) rep_abs_thms)) THEN
	 (PURE_ONCE_REWRITE_TAC [joint_select_def]) THEN
	 (COND_CASES_TAC ORELSE ALL_TAC) THEN (ONCE_REWRITE_TAC[]) THEN
	 (CONV_TAC (DEPTH_CONV reduceLib.NEQ_CONV)) THEN
	 (ONCE_REWRITE_TAC[]))))
      type_names)
     spec_cases)



fun mk_case_prop type_name =
    let
	val abs =  mk_comb{Rator = get_abs type_name, Rand = Joint_x}
	val rep_abs = mk_comb{Rator = get_rep type_name, Rand = abs}
    in
	mk_imp {ant = mk_eq{lhs = rep_abs, rhs = Joint_x},
	      conseq = mk_comb {Rator = new_ty_Prop type_name,
				Rand = abs}}
    end

fun mk_rep_abs_cases_prop [] =  mk_const{Name= "T",Ty=bool}
  | mk_rep_abs_cases_prop (type_name :: nil) =
    mk_case_prop type_name
  | mk_rep_abs_cases_prop (type_name :: type_names) =
      mk_conj{conj1 = mk_case_prop type_name,
	      conj2 = mk_rep_abs_cases_prop type_names}

val new_ty_induct_prop = mk_forall{Bvar = Joint_x,
				   Body = mk_rep_abs_cases_prop type_names}


fun case_thm type_name num =
    let
	val var = mk_var{Name= "x"^(int_to_string num),
			 Ty = get_type type_name}
    in
	GEN var
	(REWRITE_RULE
	 rep_abs_thms
	 (List.nth (CONJUNCTS (SPEC
			 (mk_comb {Rator = get_rep type_name,
				   Rand = var})
			(ASSUME new_ty_induct_prop)),
	       (num - 1))))
    end

fun case_induct_concl num [] = TRUTH
  | case_induct_concl num [type_name] = case_thm type_name num
  | case_induct_concl num (type_name::type_names) =
    CONJ (case_thm type_name num) (case_induct_concl (num + 1) type_names)

val inter_case_induct_thm = (DISCH_ALL (case_induct_concl 1 type_names))



val lemma = prove ((--`!A. (T ==> A) = A`--), (REWRITE_TAC []))

val new_ty_induct_assum =
      UNDISCH (PURE_ONCE_REWRITE_RULE [lemma] (DISCH_ALL
      (ASSUME (new_list_mk_conj (map (#new_ty_induct_case) spec_cases)))))


val inter_case_assum = #ant(dest_imp (concl inter_case_induct_thm))

val pre_case_induct_thm = prove
((mk_imp {ant = concl new_ty_induct_assum, conseq = inter_case_assum}),
 ((REWRITE_TAC (map (#cons_elim_thm) elim_cons_thms)) THEN
  STRIP_TAC THEN
  (elsaUtils.MP_IMP_TAC (BETA_RULE (SPEC (rand new_ty_induct_prop) JointInduct))) THEN
  (ASM_REWRITE_TAC (rep_abs_eq_simps @ not_rep_abs_thms)) THEN
  (REPEAT CONJ_TAC) THEN (REPEAT GEN_TAC) THEN STRIP_TAC THEN
  (fn g as (ams,gl) =>
   let val eqs =
       map (SUBST1_TAC o SYM o ASSUME) (strip_conj (#ant (dest_imp gl)))
       val tac = itlist (fn t1 => fn t2 => t1 THEN t2) eqs ALL_TAC
   in (STRIP_TAC THEN tac) g end) THEN
  (FIRST_ASSUM
   (fn th => elsaUtils.MATCH_MP_IMP_TAC (SPEC (#Bvar(dest_forall(concl th))) th))) THEN
  (REPEAT CONJ_TAC) THEN
  (FIRST_ASSUM elsaUtils.MATCH_MP_IMP_TAC) THEN (FIRST_ASSUM ACCEPT_TAC)))

val New_Ty_Induct_Thm = itlist (fn ty_name => fn th =>
                                  GEN (new_ty_Prop ty_name) th)
                               type_names
                               (IMP_TRANS pre_case_induct_thm
                                          inter_case_induct_thm);


    val (forall_vars,eBody) = strip_forall (concl New_Ty_Existence_Thm)
    val (exists_vars, New_Ty_Existence_Body) = strip_exists eBody
    val bad_vars = exists_vars @ forall_vars

val New_Ty_Existence_Body = New_Ty_Existence_Body

val {new_fns, fns_subst} =
    itlist
    (fn f => (fn {new_fns, fns_subst} =>
     let
	 val new_f = variant bad_vars f
     in
	 {new_fns = new_f :: new_fns,
	  fns_subst = {redex = f, residue = new_f} :: fns_subst}
     end))
    fns
    {new_fns = [], fns_subst = []}


val unique_goal =
    mk_imp{ant = mk_conj{conj1 = New_Ty_Existence_Body,
			 conj2 = (subst fns_subst New_Ty_Existence_Body)},
	   conseq = list_mk_conj (map
				  (fn {redex, residue} =>
				   mk_eq{lhs = redex, rhs = residue})
				  fns_subst)}

val pre_unique_thm = prove(unique_goal,
 (STRIP_TAC THEN (CONV_TAC (ONCE_DEPTH_CONV FUN_EQ_CONV)) THEN
  (fn g as (asm,gl) =>
   let val eq_preds = map rand (strip_conj gl)
       val induct = BETA_RULE (SPECL eq_preds New_Ty_Induct_Thm)
   in elsaUtils.MP_IMP_TAC induct g
   end) THEN
  (REPEAT STRIP_TAC) THEN
  (ASM_REWRITE_TAC [])))

val New_Ty_Uniqueness_Thm = GENL (cases @ fns @ new_fns) pre_unique_thm

in
  {New_Ty_Existence_Thm = New_Ty_Existence_Thm,
   New_Ty_Induct_Thm = New_Ty_Induct_Thm,
   New_Ty_Uniqueness_Thm = New_Ty_Uniqueness_Thm}
end

val _ = Parse.temp_set_grammars ambient_grammars

end (* MutRecDef *)

