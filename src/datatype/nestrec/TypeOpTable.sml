(* =====================================================================*)
(* FILE          : entries.sml                                          *)
(* DESCRIPTION   : Functor for making lookup tables keyed on type ops.  *)
(*                                                                      *)
(* AUTHOR        : Healfdene Goguen, University of Edinburgh            *)
(* DATE          : 92.08.01                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1992 by AT&T Bell Laboratories *)
(* Share and Enjoy *)
structure TypeOpTable :> TypeOpTable =
    struct
   	open TypeInfo HolKernel;
   
  type hol_type = Type.hol_type
  type term = Term.term
  type thm = Thm.thm
  type type_info = TypeInfo.type_info

  val ord = Char.ord;
	(*
	 * Process a single type operator
	 * Figure out its arity, name, and information about the
	 *	constructors (including how to get type_info lists
	 *	for them) from the recursor
	 
	 *)

fun make(tyop_prefix, recursor_thms) =
let val tyop_suffix = 
            "_" ^String.substring (tyop_prefix,0,size tyop_prefix - 1)
	fun underscore [] = ""
	  | underscore [s] = s
	  | underscore (s::ss) = s ^ "_" ^ (underscore ss)
	    
	val symbolic_ords = String.explode "#?+*/\\=<>&%@!,:;_|~-"
	fun rename_symbolic s = "ch"^Int.toString(Char.ord s)

	fun mk_symbolic_free_const_name n =
	    if Lib.mem (String.sub(n,0)) symbolic_ords
   	    then underscore (map rename_symbolic (String.explode n))
	    else n

	fun type_to_string ty =
	    (case Type.dest_type ty
		 of {Tyop,Args = []} => Tyop
	       | {Tyop,Args} => underscore (map type_to_string Args) ^
		                "_" ^ Tyop)
		 handle HOL_ERR _ => "tv" ^ dest_vartype ty

	fun type_info_to_string (being_defined t) = t
	  | type_info_to_string (existing ty) = type_to_string ty

	    
	fun get_rator t =
	    let
		val {Rator, ...} = dest_comb t
	    in
		get_rator Rator
	    end
	handle HOL_ERR _ => t

	fun process_type_op (rec_thm : thm) =
	    let
		val {base_t = stripped, ...} =
		    GenFuns.get_forall_term (concl rec_thm)
		val {Rand = prop, ...} = dest_comb stripped
		val {Body, Bvar} = dest_abs prop
		val {dom = op_type, ...} = GenFuns.dom_cod Bvar
		val {Tyop = op_type_name, Args = tyvars} = dest_type op_type
		val op_type_name_ext = op_type_name ^ tyop_suffix
		val arity = case length tyvars of
		    0 => raise HOL_ERR
			{origin_structure = "top",
			 origin_function = "make_type_op",
			 message = "non-parametric type"}
		  | n => n

		fun process_constr t =
		    let
			val {base_t = stripped, ...} = 
			    GenFuns.get_forall_term t
			val {lhs, ...} = dest_eq stripped
			val {Rand = constr_sat, ...} = dest_comb lhs
			val constr = get_rator constr_sat
			val {Name = orig_constr_name, ...} = dest_const constr
			val constr_name =
			    tyop_prefix ^
			    (mk_symbolic_free_const_name orig_constr_name)
			val {arg_types = constr_arg_types, ...} =
			    GenFuns.curry_to_list (type_of constr)
			fun original_constructor (l : hol_type list) =
			    inst (match_type op_type
				  (mk_type {Tyop = op_type_name,
					    Args = l})) constr
			fun make_type_constr
			    (info_list:type_info list) ty_args_str =
			    let
				val table =
				    foldr
				    (fn ((tyvar, tyinfo), table) =>
				     TypeTable.enter
				     {key = tyvar,
				      entry = tyinfo,
				      table = table})
				    (TypeTable.enter
				     {key = op_type,
				      entry = being_defined
				      (ty_args_str ^ "_" ^ op_type_name_ext),
				      table = TypeTable.empty})
				    (zip tyvars info_list)
				fun to_info ty =
				    case TypeTable.lookup
					{key = ty, table = table} of
					TypeTable.NotFound => existing ty
				      | TypeTable.InTable info => info
			    in
				{name = constr_name ^ "_" ^ ty_args_str,
				 arg_info = map to_info constr_arg_types}
			    end
		    in
			{original_constructor = original_constructor,
			 make_type_constr = make_type_constr}
		    end
		fun process_constr_list [] =
		    {original_constructors = fn _ => [],
		     make_type_constrs = fn _ => fn _ => []}
		  | process_constr_list
			({original_constructor,
			  make_type_constr}::constr_list) =
		    let
			val {original_constructors, make_type_constrs} =
			    process_constr_list constr_list
		    in
			{original_constructors =
			    fn l => (original_constructor l)::
					(original_constructors l),
			 make_type_constrs =
			 fn l => fn ty_args_str =>
			 (make_type_constr l ty_args_str)::
			 (make_type_constrs l ty_args_str)}
		    end
		fun process_constrs (conj_constrs : term) =
		    let
			val {original_constructors, make_type_constrs} =
			    process_constr_list
				(GenFuns.conj_map_term
				 process_constr conj_constrs)
		    in
			{original_constructors = original_constructors,
			 make_type = fn l =>
			    let
				val ty_args_str =
				    (underscore (map type_info_to_string l))
			    in
				{type_name =
				 ty_args_str ^ "_" ^ op_type_name_ext,
				 constructors =
				 make_type_constrs l ty_args_str}
			    end}
		    end
		val {original_constructors, make_type} = process_constrs Body
	    in
		{name = op_type_name,
		 arity = arity,
		 rec_thm = rec_thm,
		 original_constructors = original_constructors,
		 make_type = make_type}
	    end

	fun process_thms rec_thm_list =
	    let
		fun enter_type_op (th, table) =
		    let
			val (entry as {name, ...}) = (process_type_op th)
		    in
			StringTable.enter {key = name,
					   entry = entry,
					   table = table}
		    end
		val empty_table =
		    StringTable.empty :
			{name:string,
			 arity:int,
			 rec_thm:thm,
			 original_constructors : hol_type list -> term list,
			 make_type: type_info list ->
			    {type_name : string,
			     constructors : {name : string,
					     arg_info : type_info list} list}
			} StringTable.table
	    in
		foldr enter_type_op empty_table rec_thm_list
	    end

	val tyop_table = process_thms recursor_thms
 in
  (tyop_table, mk_symbolic_free_const_name)
 end

end;
