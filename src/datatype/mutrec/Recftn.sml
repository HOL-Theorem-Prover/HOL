(* In order to use our recursive theorem on mutually recursive types to
   define functions on these types, we need to be able to extract from a
   description of how the function should behave the values of the
   "return functions": the things that are universally quantified on
   the outside of the recursive theorem, which are functions and
   constants, one for each constructor of the mutually recursive types,
   that compute the return value of the function from the arguments
   of the constructor and the return values of applications of (possibly
   other) mutually recursive functions to the constructor args. We then
   instantiate our recursive function with them, define the functions,
   and prove that the definitions satisfy the desired properties. *)

(*
   In any term that defines a set of mutually recursive functions,
   there must be at most one function defined for each type (there need
   not be a function defined for every type). If a function is being
   defined on a type, the term must provide, in a sepate conjunct, a
   value for each constructor for the type, except as descibed below in
   the text reguarding the examples.

   Both examples define the same functions, a set of functions that
   count the number of variables and constructors used in a pattern. The
   first term gives explictly the values of the function on all
   constructors for each type for which a function is defined, and the
   second one uses the variable "allelse" to give the values for some of
   the constructors.  The "allelse" works like this: Say a function is
   being defined on a type (call it TY, in the second example this is
   atpat) and the case for a constructor is missing (for example,
   SCONatpat). If, following the clauses for the constructors for which
   explicit values are given (in the second example, VARatpat, CONatpat,
   EXCONatpat, RECORD2atpat, and PARatpat), there is a conjunct where the
   constructor applied to appropriate arguments (here, (SCONatpat sc)) is
   replaced by the variable "allelse" with type TY, then the value to the
   right of the = sign is used as the value of the function on terms
   constructed with that constructor. If there is a variable "arg" with
   type TY as one of the subterms of this value (the one to the right of
   the =), this will be replaced by the constructor applied to arguments
   (again, (SCONatpat sc)). There may be at most one "allelse" clause per
   function being defined, but there is no limit to the number of
   "allelse" clauses used in the term (they will be destinguished by the
   type of the variable). As noted above, the "allelse" clause must
   follow the clauses giving values for specific constructors (there need
   not be any of these).

--`(varcon_pat (ATPATpat ap) = varcon_atpat ap) /\
   (varcon_pat (CONpat c ap) = 1 + (varcon_atpat ap)) /\
   (varcon_pat (EXCONpat e a) = 1 + (varcon_atpat a)) /\
   (varcon_atpat WILDCARDatpat = 0) /\
   (varcon_atpat (SCONatpat sc) = 0) /\
   (varcon_atpat (VARatpat v) = 1) /\
   (varcon_atpat (CONatpat c) = 1) /\
   (varcon_atpat (EXCONatpat e) = 1) /\
   (varcon_atpat RECORD1atpat = 0) /\
   (varcon_atpat (RECORD2atpat pr) = varcon_patrow pr) /\
   (varcon_atpat (PARatpat p) = varcon_pat p) /\
   (varcon_patrow DOTDOTDOT = 0) /\
   (varcon_patrow (PATROW1 l p) = varcon_pat p) /\
   (varcon_patrow (PATROW2 l p pr) = (varcon_pat p) + (varcon_patrow pr))`--

--`(varcon_pat (ATPATpat ap) = varcon_atpat ap) /\
   (varcon_pat (CONpat c ap) = 1 + (varcon_atpat ap)) /\
   (varcon_pat (EXCONpat e a) = 1 + (varcon_atpat a)) /\
   (varcon_atpat (VARatpat v) = 1) /\
   (varcon_atpat (CONatpat c) = 1) /\
   (varcon_atpat (EXCONatpat e) = 1) /\
   (varcon_atpat (RECORD2atpat pr) = varcon_patrow pr) /\
   (varcon_atpat (PARatpat p) = varcon_pat p) /\
   (varcon_atpat allelse = 0) /\
   (varcon_patrow DOTDOTDOT = 0) /\
   (varcon_patrow (PATROW1 l p) = varcon_pat p) /\
   (varcon_patrow (PATROW2 l p pr) = (varcon_pat p) + (varcon_patrow pr))`--

*)

structure Recftn :> Recftn =
struct

open HolKernel Parse basicHol90Lib;

type term = Term.term
type fixity = Parse.fixity
type thm = Thm.thm;


val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars boolTheory.bool_grammars


(* define_mutual_functions takes the term def (one such as the one above)
   and warps it into a state where it can be combined with rec_axiom to
   produce definitions for the mutually recursive functions the user
   has given information enough to define. It returns a proof that
   the functions defined really do satisfy the conditions
   imposed by the term *)

fun define_mutual_functions {rec_axiom, name = specification_name,
			     fixities, def} =
let
open Rsyntax   (* use records *)
(*    (* We coerce the type so that rec_axiom and def agree *)
    local
	val rec_type_args =
	    #Args(dest_type(hd(#Args(dest_type(type_of
	    (hd(#1(strip_exists(#2(strip_forall (concl rec_axiom)))))))))))
	val def_type_args =
	    #Args(dest_type(type_of (rand(lhs(hd(strip_conj def))))))
	val ty_subst =
	    Lib.map2
	    (fn redex => fn residue => {redex = redex,residue=residue})
	    rec_type_args
	    def_type_args
    in
	val rec_axiom = if rec_type_args = def_type_args then rec_axiom
			else INST_TYPE ty_subst rec_axiom
    end
*)
    (* first need to deconstruct rec_axiom so we know what to look for *)

    (* term_name and type_name are used for making error messages *)
    fun term_name tm =
	if is_var tm then
	    #Name (dest_var tm)
	else if is_const tm then
	    #Name (dest_const tm)
	else raise HOL_ERR {origin_structure = "define_mutual_functions",
			    origin_function = "term_name",
			    message = "term is not constant or var"}

    fun type_name ty = #Tyop (dest_type ty)

    (* decompose takes as arguments a term that is a constructor applied
       to some args and the list of args stripped off so far; it strips
       off the rest of the args, returning the constructor by itself
       and the complete list of args *)
    fun decompose (tm, args_so_far) =
	if is_comb tm then
	    let val {Rator, Rand} = dest_comb tm in
		decompose (Rator, Rand :: args_so_far)
	    end
	else
	    (tm, args_so_far)

    (* extract_cons gets, for a conjunct in the main body of rec_axiom,
       the constructor associated with it, the arguments of the constructor,
       and the type the constructor will construct *)
    fun extract_cons conj =
	let val (cons_args, body) = strip_forall conj
	    val applied_cons = #Rand (dest_comb (#lhs (dest_eq body)))
	in
	    {result_type = type_of applied_cons,
	     cons = fst (decompose (applied_cons, [])),
	     cons_args = cons_args}
	end

    (* now we want to break up our defining term as a preliminary step
       to defining what's there *)

    (* get_def_info returns a record that looks like this
          {ftn = <fun_being_defined>,
	   ftn_dom = <domain type of function>,
	   constructor = <constructor this case covers>,
	   args = <constructor args>,
	   def = <term defining this case for function>}  *)
    fun get_def_info conj =
	let val {lhs, rhs} = dest_eq conj
	    val {Rator = ftn_term, Rand = applied_cons} = dest_comb lhs
	    val ftn_dom = type_of applied_cons
	    val (con, args) = decompose (applied_cons, [])
	in
	    {ftn = ftn_term, ftn_dom = ftn_dom,
	     constructor = con, args = args, def = rhs}
	end

    val def_data = map get_def_info (strip_conj def)

    local
	val stripped_rec =
	    #2(strip_exists (#2(strip_forall (concl rec_axiom))))
	val gen_cons_data = map extract_cons (strip_conj stripped_rec)

	fun same_cons constructor {cons,cons_args,result_type}=
	    (#Name(dest_const constructor) = #Name(dest_const cons))
	fun find_ty_subst {constructor,args,def,ftn,ftn_dom} =
	    #2(Term.match_term
	       (#cons(Lib.first (same_cons constructor) gen_cons_data))
	       constructor)
	    handle HOL_ERR _ => []

(********* backwards args to match_term ************************************
 *	fun find_ty_subst {constructor,args,def,ftn,ftn_dom} =
 *	    #2(Match.match_term constructor
 *	       (#cons(Lib.first (same_cons constructor) gen_cons_data)))
 *	    handle HOL_ERR _ => []
 **************************************************************************)
	val subst =
	    foldr (fn (data,subs) => ((find_ty_subst data) @ subs)) [] def_data
    in
	val rec_axiom =
	    (case subst of [] => rec_axiom | _ => INST_TYPE subst rec_axiom)
	val cons_data =
	    (case subst of [] => gen_cons_data
	       | _ => map extract_cons
		 (strip_conj(#2(strip_exists
				(#2(strip_forall (concl rec_axiom)))))))
    end

    (* get_type_info just gets a list of the types involved in the
       mutually recursive type definition creating them *)
    fun get_types ({result_type, cons, cons_args}::cons_data,
		   ty_last_seen, tys) =
	if result_type <> ty_last_seen then
	    (* this is the first time we've seen this type *)
	    get_types (cons_data, result_type, result_type::tys)
	else
	    get_types (cons_data, ty_last_seen, tys)
      | get_types ([], _, tys) = rev tys
    (* we pass ==:`num`== as ty_last_seen as it for sure will not be the
       return type of any of the constructors for our mutually
       recursive types *)
    val types = get_types (cons_data, Type`:num`, [])

    (* now we need to looks thru' def_data and figure out exactly
       what is there and what isn't *)

    (* get_def_for_con looks thru' def_data to see if it can find a
       definition for this constructor. If finds exactly one, returns
       SOME <datum>, if finds none, returns NONE, if finds more than
       one, raises an exception *)
    fun get_def_for_con {result_type, cons, cons_args} =
	let fun apply_all ftn (arg::args) =
	        apply_all (mk_comb {Rator = ftn, Rand = arg}) args
	      | apply_all ftn [] = ftn
        (* lookup_con looks for an item with information on cons in def_info,
	   returns NONE if didn't find it, and if some sort of match was
	   found returns a flag indicating whether an exact match was
	   found (ie, we matched against a constructor rather than an
	   "allelse"), and the corresponding item from def_info if it
	   found the constructor, or the information from an "allelse"
	   clause if it found that, as well as the rest of the def_info
	   (for error checking). If the argument exact_match_found is true,
           then we will not match with "allelse" clauses. This is to avoid
	   matching with an "allelse" clause after already matching
	   getting an exact constructor match. *)
	    fun lookup_cons (exact_match_found,
			     (def_datum as {ftn, ftn_dom, constructor,
					    args, def})::more_data) =
	        (* return the info if we've found it *)
	        if constructor = cons then
		    SOME (true, def_datum, more_data)
		(* check if there's an "allelse" clause for this type;
		   if so, the constructor is the one we're looking for
		   and the body is the definition provided by the user
		   with the applied constructor substituted for the
		   variable "arg" in order to allow the uxser to do something
		   with the argument of the function. *)
		else if not exact_match_found andalso (result_type = ftn_dom)
		    andalso (is_var constructor)
		    andalso (#Name (dest_var constructor) = "allelse") then
		    let val arg_var = mk_var {Name = "arg", Ty = ftn_dom}
			val app_cons = apply_all cons cons_args
			val subst_def = subst [{redex = arg_var,
						residue = app_cons}] def
		    in
			SOME (false,
			      {ftn = ftn, ftn_dom = ftn_dom,
			       constructor = cons, args = cons_args,
			       def = subst_def}, more_data)
		    end
		else
		    lookup_cons (exact_match_found, more_data)
	      | lookup_cons (_, []) = NONE
	    val lookup_info = lookup_cons (false, def_data)
	in
	    case lookup_info
	         (* if there was no info, there's no case for this
		    constructor for our type *)
	      of NONE => NONE
	         (* if it was in here, check to make sure it wasn't in there
		    more than once *)
	       | SOME (exact_match_found, def_datum, more_data) =>
		    (case lookup_cons (exact_match_found, more_data)
			  (* that constructor only appeared once *)
		       of NONE => SOME def_datum
			  (* constructor appeared more than once in def *)
			| SOME (_, _, _) => raise HOL_ERR
			      {origin_structure = "define_mutual_functions",
			       origin_function = "get_def_for_con",
			       message = ("constructor " ^ (term_name cons) ^
				" appears more than once in definition")})
	end
    val def_cases = map get_def_for_con cons_data

    (* get_result_typevar destructs function types until it finds that
       the range type is a typevar, and then returns that typevar *)
    fun get_result_typevar ftn_ty =
	if is_vartype ftn_ty then
	    ftn_ty
	else
	    get_result_typevar (hd (tl (#Args (dest_type ftn_ty))))

    (* we want to make sure that if the person is trying to define a
       function for a type, then s/he gives a value for each of the
       constructors for that type, and that only one function is being
       defined. Also, we return a list telling, for each type, which (if any)
       functions is being defined for that type *)
    fun check_error ftn =
	raise HOL_ERR {origin_structure = "define_mutual_functions",
		       origin_function = "check_def",
		       message = ("only some cases provided for function " ^
			(term_name ftn))}
    val one_ty = Type`:one`
    val one_tm = Term`one`

    fun get_ftn_info ({cons, cons_args, result_type}::cons_data,
		      def_datum::def_data,
		      ftn_dom_ty,
		      ftn_being_defined) =
	if result_type <> ftn_dom_ty then
            (* we have a new type to report info and check functions for *)
	    case def_datum
	      of NONE =>
		  (* we set range type to be one because we will create
		     a dummy function returning one. The domain of the
		     function we're defining is the result type of the
		     constructor it's operating on *)
		  {ftn_op = NONE, dom_ty = result_type, rng_ty = one_ty}::
		  get_ftn_info (cons_data, def_data, result_type, NONE)
               | SOME {args, constructor, def, ftn, ftn_dom} =>
		  {ftn_op = SOME ftn, dom_ty = result_type,
		   rng_ty = type_of def}::
		  get_ftn_info (cons_data, def_data, result_type, SOME ftn)
	else
	    (* we need to make sure the functions match *)
	   (case def_datum
	      of NONE =>
		  (case ftn_being_defined
		     of NONE =>
			 get_ftn_info (cons_data, def_data, ftn_dom_ty, NONE)
		      | SOME ftn => check_error ftn)
               | SOME {args, constructor, def, ftn, ftn_dom} =>
		  (case ftn_being_defined
		     of NONE => check_error ftn
		      | SOME other_ftn =>
			 if ftn <> other_ftn then raise HOL_ERR
			     {origin_structure = "define_mutual_functions",
			      origin_function = "get_ftn_info",
			      message = ("two different functions " ^
					 (term_name ftn) ^
			       " and " ^ (term_name other_ftn) ^
			       " defined for type " ^ (type_name result_type))}
			 else
			     get_ftn_info (cons_data, def_data,
					   ftn_dom_ty, ftn_being_defined)))
      | get_ftn_info (_, _, _, _) = []

    (* again, pass ==`:num`== as a type that shouldn't be among the
       recursive types *)
    val ftn_type_data = get_ftn_info (cons_data, def_cases, Type`:num`, NONE)

    (* now we need to construct the return functions from the data given *)

    (* Now I want to get the definitions of the functions and constants
       that compute return values for each constructor, ie, the a-nn in
       the definition of syntax_rec. To do this, we munge the def field
       in each element of term_parts. Using the example above, consider the
       phrase
	   (varcon_pat (CONpat c ap) = 1 + (varcon_atpat ap))
       We want to create nn, the function that will return a value for
       items constructed using CONpat. nn should have type
       'j->id->atpat->'m, where 'j and 'm, the return values of varcon_atpat
       and varcon_pat, resp, are both num. So nn will have the form
	   \r:num. \c:con. \ap:atpat. <body>
       We have to munge (1 + (varcon_atpat ap)) around to be <body>. The main
       thing we have to do is replace recursive calls with the arguments
       provided for that purpose. We know that ap must have
       type atpat (since it's the second arg to constructor CONpat), and
       so the only recursive function that can be applied to it is
       varcon_atpat, the function being defined for that type. So we replace
       (varcon_atpat ap) with r to get the body. Thus nn will be
           \r. \c. \ap. 1 + r
       If no function is defined for a type, I will create a dummy function
       that returns one for all inputs. *)

    (* lookup_ftn will tell me, for each type, if it is one of the recursive
       types we're defining funtions on, and if so, whether the person is
       defining a function on it and what the domain and range types of
       such a function would be. lookup_return is the datatype returned by
       lookup_ftn *)
    datatype lookup_return = not_rec_type |
	rec_ftn_info of {dom_ty:hol_type, ftn_op:term option, rng_ty:hol_type}

    fun lookup_ftn (dom, (datum as {ftn_op, dom_ty, rng_ty})::ftn_type_data) =
	if dom = dom_ty then
	    rec_ftn_info datum
	else
	    lookup_ftn (dom, ftn_type_data)
      | lookup_ftn (_, []) = not_rec_type

    (* get_rec_vars is used when no function is being defined for this type,
       figures out what vars to abstract over to make a constant function,
       returns them is reverse order. all_vars initially contains the args
       (which are variables) of the constructors; the recursive variables
       are added on as they are computed *)
    fun get_rec_vars (all_vars, arg::more_args, rev_rec_vars) =
        let val ftn_info = lookup_ftn (type_of arg, ftn_type_data)
        in
            case ftn_info
              of not_rec_type =>
                  (* can't recurse on this arg, so add no more vars *)
                  get_rec_vars (all_vars, more_args, rev_rec_vars)
               | rec_ftn_info {ftn_op, dom_ty, rng_ty} =>
                     (* we'll have to create a recursive var for it *)
                     let val new_var = variant all_vars
                         (mk_var {Name = "r", Ty = rng_ty})
                     in
                          get_rec_vars (new_var::all_vars, more_args,
                                        new_var::rev_rec_vars)
                     end
        end
      | get_rec_vars (all_vars, [], rev_rec_vars) = rev_rec_vars

    (* sort_cons_args is used to sort the constructor args into
       recursive (one of the types defined in the recursive type def)
       and nonrecursive (an existing type). This is done because the
       return functions have the non-recursive args before the
       recursive args, even if they were interspersed in the definition
       of the constructor. Within those sorts, however, earlier
       constructor args are earlier in the lists. The list returned is
       in reverse order (i.e. rev_rec_args @ rev_nonrec_args) since
       abstract_over_vars takes them in reverse order *)
    fun sort_cons_args (arg::cons_args, rev_rec_args, rev_nonrec_args) =
	let val ftn_info = lookup_ftn (type_of arg, ftn_type_data)
        in
            case ftn_info
              of not_rec_type => sort_cons_args
		  (cons_args, rev_rec_args, arg::rev_nonrec_args)
	       | rec_ftn_info _ => sort_cons_args
		  (cons_args, arg::rev_rec_args, rev_nonrec_args)
	end
      | sort_cons_args ([], rev_rec_args, rev_nonrec_args) =
	rev_rec_args @ rev_nonrec_args

    (* replace_recursion actually does the job of replacing recursive calls
       (like (varcon_atpat ap)) with variables (like r) in definition
       given in order to make body of return function. It returns
       the the modified term (which will be the body of our function) and
       the variables representing the recursions (in reverse order). The arg
       all_vars initially contains the args (which are variables) of the
       constructors; the recursive variables are added on as they
       are computed *)
    fun replace_recursion (tm, all_vars, [], rev_rec_vars) =
	(tm, rev_rec_vars)
      | replace_recursion (tm, all_vars, arg::args, rev_rec_vars) =
	let val ftn_info = lookup_ftn (type_of arg, ftn_type_data)
	in
	    case ftn_info
	      of not_rec_type =>
		  (* this is a base type,  no need to do recursion *)
		  replace_recursion (tm, all_vars, args, rev_rec_vars)
	       | rec_ftn_info {ftn_op = NONE, dom_ty, rng_ty} =>
	          (* this is a recursive type, but there will be no
		     recursive calls on this arg since no recursive function
		     is being defined on it. Still, we need to abstract
		     over it *)
		  let val new_var = variant all_vars
		      (mk_var {Name = "r", Ty = rng_ty})
		  in
		      replace_recursion (tm,  new_var::all_vars,
					 args, new_var::rev_rec_vars)
		  end
	       | rec_ftn_info {ftn_op = SOME ftn, dom_ty, rng_ty} =>
		  (* this is a recursive type and we will have to replace
		     recursive calls on it *)
		  let val term_to_replace = mk_comb {Rator = ftn, Rand = arg}
		      val new_var = variant all_vars
			  (mk_var {Name = "r", Ty = rng_ty})
		      val sub1 = [{redex = term_to_replace, residue = new_var}]
		  in
		      replace_recursion (subst sub1 tm, new_var::all_vars,
					 args, new_var::rev_rec_vars)
		  end
	end

    (* abstract_over_vars takes as arguments the body of the function
       we are creating and the variables we want to abstract over (in
       reverse order), and returns the body abstracted over the vars *)
    fun abstract_over_vars (tm, []) = tm
      | abstract_over_vars (tm, arg::rev_args) =
	   abstract_over_vars (mk_abs {Bvar = arg, Body = tm},
			       rev_args)

    (* create_return_fun munges the RHS of an equation given in the term
       into the function or constant (one of a - nn) needed by syntax_rec *)
    fun create_return_fun (NONE,
			   {cons, cons_args, result_type}) =
	(* no function defined for this type, make the function be
	   \<rec vars> <cons args -- nonrecursive ones first>. one *)
	let val rev_sorted_args = sort_cons_args (cons_args, [], [])
	    val rev_rec_vars = get_rec_vars (cons_args, cons_args, [])
	in
	    abstract_over_vars (abstract_over_vars (one_tm, rev_sorted_args),
				rev_rec_vars)
	end
      | create_return_fun (SOME {ftn, ftn_dom, constructor, args, def},
			   {cons, cons_args, result_type}) =
	let val (body, rev_rec_vars) = replace_recursion (def, args, args, [])
	    val rev_sorted_args = sort_cons_args (args, [], [])
	in
	    abstract_over_vars (abstract_over_vars (body, rev_sorted_args),
				rev_rec_vars)
	end

    (* create list of functions and constants that create return values for
       our mutually recursive functions *)
    val return_functions = map create_return_fun
	                       (combine (def_cases, cons_data))

    (* Now we can define our mutually recursive functions. If we specialize
       rec_axiom to our return functions, we get a theorem that says that
       the functions that we want to exist do exist. Actually the form
       of the theorem is
	   ? fn1 ... fnN. (fn1 satisfies property1) /\ ...
                          (fnN satisfies propertyN)
       where N is the number of mutually recursive types, fI is the
       function defined for type I (using the order in which the types
       are given in rec_axiom), and propertyI is, if a function is
       defined for type I, definition the user gave, otherwise
       propertyI says that the function returns one on all inputs. *)
    val  exists_thm = BETA_RULE (ISPECL return_functions rec_axiom)

    (* We will need to prove a theorem something like
           ? fn1 fn2 ... fnM. <user's definition with fnI in place of
                               functions user wants to define>
       (where M <= N is the number of functions the user actually defined)
       in order to do a new_specification to define the functions.

       Our first step will be to get rid of all the unwanted conjuncts
       (those that refer to types the user isn't defining a function for),
       thus obtaining a theorem like
           ? fn1 fn2 ... fnN. <user's definition with fnI in place of
                               functions user wants to define>
       and later we will get rid of the undesired fnI's that we're
       quantifying over.
       To get this theorem we will prove a lemma (called lemma1 below) saying
            !P Q. ((?fn1 ... fnN. P fn1 ... fnN) /\
                   (!fn1 ... fnN. P fn1 ... fnN ==> Q fn1 ... fnN)) ==>
                  ?fn1 ... fnN. Q fn1 ... fnN
       The idea is that P will be instantiated to
              \fn1 fn2 ... fnN. (fn1 satisfies property1) /\ ...
	                        (fnN satisfies propertyN)
       mentioned above, and Q will be instantiated to
              \fn1 fn2 ... fnN. <user's definition with fnI in place of
                                 functions user wants to define>
       from above. *)

    (* To prove this lemma we will use TAC_PROOF. Our first task is to
       concoct the term that is the conclusion *)
    val (rec_ftn_vars, base_P) = strip_exists (concl exists_thm)
    (* Let's make Ptm, which is what the P variable in our lemma will
       eventually be instantiated to *)
    val Ptm = list_mk_abs (rec_ftn_vars, base_P)
    (* Pvar and Qvar will be the generic properties we'll use in the lemma *)
    val Pvar = mk_var {Name = "P", Ty = type_of Ptm}
    val Qvar = mk_var {Name = "Q", Ty = type_of Ptm}
    (* make applied versions of P and Q *)
    val Papp = list_mk_comb (Pvar, rec_ftn_vars)
    val Qapp = list_mk_comb (Qvar, rec_ftn_vars)
    (* make the antecedant *)
    val conj1 = list_mk_exists (rec_ftn_vars, Papp)
    val conj2 = list_mk_forall (rec_ftn_vars,
				mk_imp {ant = Papp, conseq = Qapp})
    val ant = mk_conj {conj1 = conj1, conj2 = conj2}
    (* make the consequent *)
    val conseq = list_mk_exists (rec_ftn_vars, Qapp)
    (* and now for our goal *)
    val goal = list_mk_forall ([Pvar, Qvar],
			       mk_imp {ant = ant, conseq = conseq})
    (* Make a tactic for instantiating all our existential variables *)
    fun mk_multi_exists_tac [] = ALL_TAC
      | mk_multi_exists_tac [ftn_var] = EXISTS_TAC ftn_var
      | mk_multi_exists_tac (ftn_var::rec_ftn_vars) =
	(EXISTS_TAC ftn_var) THEN (mk_multi_exists_tac rec_ftn_vars)
    val multi_exists_tac = mk_multi_exists_tac rec_ftn_vars
    (* Prove it! *)
    val lemma1 = TAC_PROOF
	(([], goal),
	 (REPEAT GEN_TAC) THEN STRIP_TAC THEN multi_exists_tac THEN
	 (MP_TAC (ASSUME Papp)) THEN (ASM_REWRITE_TAC []))

    (* Specialize lemma1 to Ptm *)
    val specP_lemma1 = BETA_RULE (SPEC Ptm lemma1)

    (* we need to get some info about exists_thm: for each conjunct
       I want the conjunct itself, the constructor and the conjunct
       refers to, and the type of the constructor *)
    fun get_exists_info conjunct =
	let val (_, temp_tm) = strip_forall conjunct
	    val cons_and_args = rand (lhs temp_tm)
	    val return_type = type_of cons_and_args
	    val (constructor, _) = decompose (cons_and_args, [])
	in
	    {cons = constructor, cons_range = return_type, conj = conjunct}
	end
    val exists_data = map get_exists_info
	              (strip_conj (snd (strip_exists (concl exists_thm))))

    (* addlist performs the functions, essentially, of (rev l1)@l2 *)
    fun addlist (item::rev_list, old_list) =
	addlist (rev_list, item::old_list)
      | addlist ([], old_list) = old_list

    (* get_conj_for_cons looks through exists_data to find the conjunct
       associated with the constructor field of an item in def_data,
       returns the conj found as well as exists_data with that conj
       removed *)
    fun get_conj_for_cons ({constructor, ftn, ftn_dom, args, def},
			   exists_data) =
	let fun helper (seen_data,
			(datum as {cons, conj, cons_range})::exists_data) =
	        if constructor = cons then
		    (conj, addlist (seen_data, exists_data))
	        else
		    helper (datum::seen_data, exists_data)
	      | helper (seen_data, []) = raise HOL_ERR
		{origin_structure = "define_mutual_functions",
		 origin_function = "get_conj_for_cons",
		 message = ("illegal constructor " ^ (term_name constructor) ^
		  " in definition")}
	in
	    helper ([], exists_data)
	end
    (* get_conjs_for_allelse returns a list of the conjunts that apply
       to an allelse clause, returns the list of conjs found as well
       as exists_data with those conjs removed *)
    fun get_conjs_for_allelse ({constructor, ftn, ftn_dom, args, def},
			       exists_data) =
	let fun helper (seen_data, conjs,
			(datum as {cons, conj, cons_range})::exists_data) =
	        if ftn_dom = cons_range then
		    helper (seen_data, conj::conjs, exists_data)
		else
		    helper (datum::seen_data, conjs, exists_data)
	      | helper (seen_data, conjs, []) = (rev conjs, rev seen_data)
	in
	    helper ([], [], exists_data)
	end

    (* this function goes through the list, picking out the conjunc(s)
       that go with each conjunct in def. There might be more than one
       conjunct since the conjunct in def might be an "allelse" one.
       As we find the conjuncts the functions get_conjs_for_allelse and
       get_conj_for_cons eliminate them from the version of exists_data
       that they return so that when we come across an "allelse" clause
       we will know which clauses have already been used for the non
       "allelse" conjuncts *)
    fun mk_Qtm_body ((datum as {ftn, ftn_dom, constructor, args, def})
		     ::def_data,
		     exists_data) =
	if is_var constructor then
	    if #Name (dest_var constructor) = "allelse" then
		let val (conjs, exists_data2) =
		    get_conjs_for_allelse (datum, exists_data)
		in
		    conjs@(mk_Qtm_body (def_data, exists_data2))
		end
	    else
		raise HOL_ERR {origin_structure = "define_mutual_functions",
			       origin_function = "mk_Qtm_body",
			       message = ("illegal variable " ^
					  (term_name constructor) ^
					  " in definition")}
	else
	    let val (conj, exists_data2) =
		get_conj_for_cons (datum, exists_data)
	    in
		conj::(mk_Qtm_body (def_data, exists_data2))
	    end
      | mk_Qtm_body ([], exists_data) = []

    (* Make Qtm, the term Q will be instantiated to *)
    val Qtm = list_mk_abs (rec_ftn_vars,
			   list_mk_conj (mk_Qtm_body (def_data, exists_data)))
    val specPQ_lemma1 = BETA_RULE(SPEC Qtm specP_lemma1)

    (* Now want to prove !fn1 ... fnN. P fn1 ... fnN ==> Q fn1 ... fnN *)
    val goal = #conj2 (dest_conj (#ant (dest_imp (concl specPQ_lemma1))))
    (* this goal is pretty easy to prove for the variables fn1 thru'
       fnN, since all the conjuncts in Qtm are present in Ptm, but would take
       a long time to verify for the particular functions that make Ptn true.
       This is why we are using lemma1 in the first place *)
    val lemma2 = TAC_PROOF
	(([],goal),
	 (REPEAT GEN_TAC) THEN STRIP_TAC THEN (REPEAT CONJ_TAC) THEN
	 (FIRST_ASSUM ACCEPT_TAC))

    (* now that we have both ?fn1 ... fnN. Ptm fn1 ... fnN (in exists_thm)
       and !fn1 ... fnN. Ptm fn1 ... fnN ==> Qtm fn1 ... fnN) (in lemma2) we
       now conclude that ?fn1 ... fnN. Qtm fn1 ... fnN (which is existsQ) *)
    val existsQ = MP specPQ_lemma1 (CONJ exists_thm lemma2)

    (* Now we need to eliminate from the f1 ... fN
       the functions the user didn't want to define (we defined them
       as functions returning one). We do this using a rewrite. *)
    val sat_thm = REWRITE_RULE [] existsQ

    (* Now we want to use sat_thm in a new_specification.
       To do this we need the names of the functions we are defining,
       in the order in which the constructors for it are presented in
       rec_axiom. ftn_type_data will give us this info *)
    val new_ftn_names =
	foldr (fn ({ftn_op = NONE, dom_ty, rng_ty}, namelist) =>
	          namelist
	        | ({ftn_op = SOME ftn, dom_ty, rng_ty}, namelist) =>
		  (#Name (dest_var ftn))::namelist)
	      []
	      ftn_type_data

    val consts =
	case fixities
	    of SOME fixes => (map2
			      (fn name => fn fixity => {const_name = name,
							fixity = fixity})
			      new_ftn_names
			      fixes
			      handle (HOL_ERR _) => raise
				  HOL_ERR {origin_structure = "top",
					   origin_function =
					   "define_mutual_functions",
					   message =
					   "term is not constant or var"})
	  | NONE => map (fn name => {const_name = name, fixity = Prefix})
	                new_ftn_names

    (* Now we do our definition. *)
    val final = new_specification
	{name =  specification_name,
	 consts = consts,
	 sat_thm = sat_thm}

    in
	final
    end

val _ = Parse.temp_set_grammars ambient_grammars
end;

(* Tests:

(* The following is an example of a term used to define mutually
   recursive functions operating on the syntax classes. It defines a
   function that counts the number of variables and constructors used
   in a pattern. *)

val def =
--`(varcon_pat (ATPATpat ap) = varcon_atpat ap) /\
   (varcon_pat (CONpat c ap) = 1 + (varcon_atpat ap)) /\
   (varcon_pat (EXCONpat e a) = 1 + (varcon_atpat a)) /\
   (varcon_atpat WILDCARDatpat = 0) /\
   (varcon_atpat (SCONatpat sc) = 0) /\
   (varcon_atpat (VARatpat v) = 1) /\
   (varcon_atpat (CONatpat c) = 1) /\
   (varcon_atpat (EXCONatpat e) = 1) /\
   (varcon_atpat RECORD1atpat = 0) /\
   (varcon_atpat (RECORD2atpat pr) = varcon_patrow pr) /\
   (varcon_atpat (PARatpat p) = varcon_pat p) /\
   (varcon_patrow DOTDOTDOT = 0) /\
   (varcon_patrow (PATROW1 l p) = varcon_pat p) /\
   (varcon_patrow (PATROW2 l p pr) = (varcon_pat p) + (varcon_patrow pr))`--

val def =
--`(varcon_pat (ATPATpat ap) = varcon_atpat ap) /\
   (varcon_pat (CONpat c ap) = 1 + (varcon_atpat ap)) /\
   (varcon_pat (EXCONpat e a) = 1 + (varcon_atpat a)) /\
   (varcon_atpat (VARatpat v) = 1) /\
   (varcon_atpat (CONatpat c) = 1) /\
   (varcon_atpat (EXCONatpat e) = 1) /\
   (varcon_atpat (RECORD2atpat pr) = varcon_patrow pr) /\
   (varcon_atpat (PARatpat p) = varcon_pat p) /\
   (varcon_atpat allelse = 0) /\
   (varcon_patrow DOTDOTDOT = 0) /\
   (varcon_patrow (PATROW1 l p) = varcon_pat p) /\
   (varcon_patrow (PATROW2 l p pr) = (varcon_pat p) + (varcon_patrow pr))`--

val def =
--`(varcon_pat (ATPATpat ap) = varcon_atpat ap) /\
   (varcon_pat (CONpat c ap) = 1 + (varcon_atpat ap)) /\
   (varcon_pat (EXCONpat e a) = 1 + (varcon_atpat a)) /\
   (varcon_atpat (VARatpat v) = 1) /\
   (varcon_atpat (CONatpat c) = 1) /\
   (varcon_atpat (EXCONatpat e) = 1) /\
   (varcon_atpat (RECORD2atpat pr) = varcon_patrow pr) /\
   (varcon_atpat (PARatpat p) = varcon_pat p) /\
   (varcon_atpat allelse = 0) /\
   (varcon_patrow DOTDOTDOT = 0) /\
   (varcon_patrow (PATROW1 l p) = varcon_pat p) /\
   (varcon_patrow (PATROW2 l p pr) = (varcon_pat p) + (varcon_patrow pr))`--

val def =
--`(foo33 (ATEXPexp ae) = T) /\
   (foo33 allelse =
    eval_exp arg ^initial_state ^initial_env ^initial_state
    (PACKvp ^Bind_pack))`--

end tests
 *)
