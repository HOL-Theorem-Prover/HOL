(* =====================================================================*)
(* FILE          : def_type.sig                                         *)
(* DESCRIPTION   : Functor for creating a nested recursive type         *)
(*                 definition.  Uses mutually recursive definitions.    *)
(*                                                                      *)
(* AUTHORS       : Healfdene Goguen, University of Edinburgh, and       *)
(*                 Elsa L. Gunter, AT&T Bell Laboratories               *)
(* DATE          : 94.03.13                                             *)
(*                                                                      *)
(* =====================================================================*)

(* Copyright 1994 by AT&T Bell Laboratories *)
(* Share and Enjoy *)

structure DefType :> DefType =
  struct

    open HolKernel Parse basicHol90Lib;
    val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars
    fun -- q x = Term q
    fun == q x = Type q
        infix THEN |->
        open Recftn;
        open TypeInfo

        fun DEF_TYPE_ERR {function, message} =
            HOL_ERR {message = message,
                     origin_function = function,
                     origin_structure = "def_type"}


        val int_to_string = Int.toString
        (*
         * This type lets us put tags on the new types which we
         * define to represent the expanded type operators in a mutual
         * recursive definition
         *)
        datatype defn = Basic
          | Type_op of {rec_thm : thm,
                        tyop_args : type_info list,
                        tyop_name : string,
                        original_constructors :
                        hol_type list -> term list}

        (*
         * These functions and values, culminating in
         * ty_ops, gather up the types being defined
         * on the left-hand sides of equations and in the
         * constructors, as well as the type operators used.
         *)
        fun collect {constrs:string StringTable.table,
                     ty_ops:(string * int) StringTable.table}
            (DefTypeInfo.being_defined ty) =
            {constrs = StringTable.enter {key = ty,
                                          entry = ty,
                                          table = constrs},
             ty_ops = ty_ops}

          | collect d (DefTypeInfo.existing _) = d
          | collect {constrs, ty_ops} (DefTypeInfo.type_op {Tyop, Args}) =
            let
                val ty_ops = case StringTable.lookup {key = Tyop,
                                                      table = ty_ops} of
                    StringTable.InTable (_, lnth) =>
                        if lnth = length Args then
                            ty_ops
                        else
                            raise DEF_TYPE_ERR
                                {function = "collect",
                                 message  = "operator " ^ Tyop ^
                                 " has different arities"}
                  | StringTable.NotFound =>
                        StringTable.enter {key = Tyop,
                                           entry = (Tyop, length Args),
                                           table = ty_ops}
            in
                collect_args {constrs = constrs, ty_ops = ty_ops} Args
            end
        and collect_args t l = foldr (fn (a, t) => collect t a) t l
        fun collect_constr_defs t l =
            foldr (fn ({name, arg_info}, t') =>
                   collect_args t' arg_info) t l
        fun collect_new_defs [] = {defs = StringTable.empty,
                                   constrs = StringTable.empty,
                                   ty_ops = StringTable.empty}
          | collect_new_defs ({type_name, constructors}::l) =
            let
                val {defs, constrs, ty_ops} = collect_new_defs l
                val defs = case StringTable.lookup
                    {key = type_name, table = defs} of
                    StringTable.InTable _ =>
                        raise DEF_TYPE_ERR
                            {function = "defined_types",
                             message = type_name ^
                             " defined more than once"}
                  | StringTable.NotFound =>
                        StringTable.enter {key = type_name,
                                           entry = type_name,
                                           table = defs}
                val {constrs, ty_ops} =
                    collect_constr_defs
                    {constrs = constrs, ty_ops = ty_ops} constructors
            in
                {defs = defs, constrs = constrs, ty_ops = ty_ops}
            end
        fun match_constrs_with_defs {constr_list, def_table} =
            foldr (fn (s, l) =>
                   case StringTable.lookup {key = s, table = def_table} of
                       StringTable.InTable _ => l
                     | StringTable.NotFound => s::l
                           ) [] constr_list;

fun define_type def_type_spec recursor_thms =
 let
        val {defs, constrs, ty_ops} = collect_new_defs def_type_spec

        (*
         * Check that all types being defined in constructors are
         * being defined on left-hand side
         *)
        val _ = case match_constrs_with_defs
            {constr_list = StringTable.elts constrs,
             def_table = defs} of
            [] => ()
          | l  => raise DEF_TYPE_ERR
                {function = "define_type_list",
                 message = (GenFuns.present_strings l) ^
                 " used in constructors but not defined"}


(*	local
        structure RecursorThms =
            struct
               type thm = Thm.thm
                structure TypeInfo = TypeInfo
                type type_info = TypeInfo.type_info
		val tyop_prefix = (foldr (fn (x,y) => x^"_"^y)
				    "" (StringTable.elts defs))
                val recursor_thms = DefTypeInput.recursor_thms
            end
        in
        structure TypeOps : TypeOpSig =
            MakeTypeOpTable (structure RecursorThms = RecursorThms)
        end
*)
    val tyop_prefix = foldr (fn (x,y) => x^"_"^y) "" (StringTable.elts defs)

     val (TypeOps_tyop_table, TypeOps_mk_symbolic_free_const_name)
       = TypeOpTable.make(tyop_prefix,recursor_thms)

        (*
         * Check that we have recursors for all of
         * the collected type operators and that the arities
         * of the type operators match
         *)
        val _ = foldr (fn ((name, carity), _) =>
                       let
                           val {arity, ...} =
                               case StringTable.lookup
                                   {key = name, table = TypeOps_tyop_table} of
                                   StringTable.InTable x => x
                                 | StringTable.NotFound =>
                                       raise DEF_TYPE_ERR
                                           {function = "check_ty_ops",
                                            message = name ^ " not defined"}
                       in
                           if arity = carity then ()
                           else
                               raise DEF_TYPE_ERR
                                   {function = "check_ty_ops",
                                    message = name ^ " has arity " ^
                                    (int_to_string carity) ^
                                    " as a constructor and arity " ^
                                    (int_to_string arity) ^
                                    " in theorem"}
                       end) () (StringTable.elts ty_ops)

        (*
         * Create the equations for the mutual recursive type
         *)


        fun make_mutual_constructor
            {name:string, arg_info:DefTypeInfo.type_info list} =
            let
                fun process_arg (DefTypeInfo.being_defined X) =
                    {arg = being_defined X, new_types = []}
                  | process_arg (DefTypeInfo.existing T) =
                    {arg = existing T, new_types = []}
                  | process_arg (T as DefTypeInfo.type_op
                                 {Tyop = F, Args = arg_info}) =
                    let
                        val {args, new_types} = process_args arg_info
                        val {make_type, rec_thm, original_constructors, ...} =
                            case StringTable.lookup
                                {key = F, table = TypeOps_tyop_table} of
                                StringTable.InTable x => x
                              | StringTable.NotFound =>
                                    raise DEF_TYPE_ERR
                                        {function = "make_mutual_constructor",
                                         message = "bug: type operator " ^ F ^
                                         " not found"}
                        val ({type_name, constructors}) = make_type args
                    in
                        {arg = being_defined type_name,
                         new_types =
                         {type_name = type_name,
                          def = Type_op {rec_thm = rec_thm,
                                         tyop_args = args,
                                         tyop_name = F,
                                         original_constructors =
                                         original_constructors},
                          constructors = constructors}::new_types}
                    end
                and process_args [] = {args = [], new_types = []}
                  | process_args (c::l) =
                    let
                        val {arg, new_types} = process_arg c
                        val {args = collected_args,
                             new_types = collected_new_types} =
                            process_args l
                    in
                        {args = arg::collected_args,
                         new_types = new_types@collected_new_types}
                    end
                val {args = arg_info, new_types} =
                    process_args arg_info
            in
                {constr_info = {name = name, arg_info = arg_info},
                 new_types = new_types}
            end

        (*
         * Create a table with type specifications, keyed by type name
         *)
        fun make_mutual_types [] = StringTable.empty
          | make_mutual_types
            ({type_name : string,
              def : defn,
              constructors : {name : string,
                              arg_info : DefTypeInfo.type_info list}
              list}::l) =
            let
                fun add_new_type {table:{type_name : string,
                                         def : defn,
                                         constructors :
                                         {name : string,
                                          arg_info : type_info list} list}
                                  StringTable.table,
                                  new_type = new_type as
                                  {type_name,
                                   constructors,
                                   ...}} =
                    (case StringTable.lookup {key = type_name,
					      table = table}
			 of StringTable.NotFound =>
			     StringTable.enter {key = type_name,
						entry = new_type,
						table = table}
		       | StringTable.InTable
			 {constructors = existing_constrs, ...} =>
			     if constructors = existing_constrs then table
			     else
				 raise DEF_TYPE_ERR
				     {function = "add_new_type",
				      message = "type " ^ type_name ^
				      " has differing definitions"})
                fun process_constrs [] = {constr_info = [], new_types = []}
                  | process_constrs (c::l) =
                    let
                        val {constr_info, new_types} =
                            make_mutual_constructor c
                        val {constr_info = collected_constr_info,
                             new_types = collected_new_types} =
                            process_constrs l
                    in
                        {constr_info = constr_info::collected_constr_info,
                         new_types = new_types@collected_new_types}
                    end
                val {constr_info, new_types} = process_constrs constructors
            in
                add_new_type
                {table = foldr (fn (new_type, table) =>
                                add_new_type {table = table,
                                              new_type = new_type})
                 (make_mutual_types l) new_types,
                 new_type = {type_name = type_name, def = def,
                             constructors = constr_info}}
            end

        (*
         * Change original specification to have the definition tag as well
         * For now the list should have one element
         *)
        fun basics [] = []
          | basics ({type_name, constructors}::l) =
            {type_name = type_name,
             constructors = constructors,
             def = Basic}::(basics l)

        val types = make_mutual_types (basics def_type_spec)

        (*
         * Extract the specification of the mutual type as
         * MutRecDefFunc expects it
         *)
        local
            fun internal_names [] = []
              | internal_names (({name, arg_info})::l) =
                {name = "int_" ^ name,
                 arg_info = arg_info}::(internal_names l)
        in
            fun extract_mut_rec_definition [] = []
              | extract_mut_rec_definition ({type_name,
                                             constructors,
                                             def}::l) =
                {type_name = type_name,
                 constructors = internal_names constructors}::
                (extract_mut_rec_definition l)
        end

        (*
         * Extract the specification and call the mutual type
         * definition package
         *)
        val mut_rec_ty_spec =
            extract_mut_rec_definition (StringTable.elts types)

(*
	local
        structure MutRecTyInput =
            struct
                structure TypeInfo = TypeInfo
                type type_info = TypeInfo.type_info

                val mut_rec_ty_spec = mut_rec_ty_spec
            end
        in
        structure MutRecDef =
            MutRecDefFunc (structure utilsLib = utilsLib
                           structure MutRecTyInput = MutRecTyInput)
        end
*)
       val {New_Ty_Induct_Thm = MRD_New_Ty_Induct_Thm,
            New_Ty_Uniqueness_Thm = MRD_New_Ty_Uniqueness_Thm,
            New_Ty_Existence_Thm = MRD_New_Ty_Existence_Thm}
              = MutRecDef.define_type mut_rec_ty_spec

        val newly_defined_types =
            map
            (fn tm => hd (#Args (dest_type (type_of tm))))
            (#1(strip_exists
                (#2(strip_forall(concl MRD_New_Ty_Existence_Thm)))))

        fun get_new_type name =
            Lib.first
            (fn ty => #Tyop (dest_type ty) = name)
            newly_defined_types

        (*
         * Coerce type_info to hol_type
         *)
        fun raise_type_info (existing t) = t
          | raise_type_info (being_defined X) = get_new_type X



        (*
         * Coerce internal constructor specifications into
         * internal constructors
         *)
        local
            fun get_vars {rec_vars, arg_vars, x_vars, arg_info = [], ...} =
                {rec_vars = rec_vars, arg_vars = arg_vars, x_vars = x_vars}
              | get_vars {count, rec_vars, arg_vars, x_vars,
                          arg_info = (existing ty) :: arg_info} =
                let val x = mk_var{Name = "x"^(int_to_string count), Ty = ty}
                in get_vars {count = count + 1,rec_vars = rec_vars,
                             arg_vars = x::arg_vars, x_vars = x :: x_vars,
                             arg_info = arg_info}
                end
              | get_vars {count, rec_vars, arg_vars, x_vars,
                          arg_info = (being_defined n) :: arg_info} =
                let val ty = get_new_type n
                    val x = mk_var{Name = "y"^(int_to_string count), Ty = ty}
                    val r = mk_var{Name = "r"^(int_to_string (count+1)),
                                   Ty = ty}
                in
                    get_vars {count = count + 2, rec_vars = r::rec_vars,
                              arg_vars = r::arg_vars, x_vars = x :: x_vars,
                              arg_info = arg_info}
                end
        in
            val internal_constructors =
                map
                (fn {type_name, constructors} =>
                 {type_name = type_name,
                  int_const_info =
                  foldr
                  (fn ({name, arg_info}, {int_consts, cases}) =>
                   let
                       val int_const =
                           mk_const {Name = name,
                                     Ty = GenFuns.list_to_curry
                                     {arg_types = map raise_type_info arg_info,
                                      cod_type = get_new_type type_name}}
                       val case_arg = (*{rec_vars,arg_vars,x_vars} =*)
                           get_vars {count = 1, rec_vars = [],arg_vars = [],
                                     x_vars = [], arg_info = arg_info}

                   in
                       {int_consts = int_const::int_consts,
                        cases = case_arg :: cases}
                   end)
                  {int_consts = [], cases = []}
                  constructors})
                mut_rec_ty_spec
        end

        fun lookup_int_constructors ty_name =
            #int_consts(#int_const_info
            (Lib.first
             (fn {type_name,...} => (type_name = ty_name))
             internal_constructors))

(*
        (*
         * Tables keyed by hol_type
         *)
        structure TypeEntry =
            struct
                datatype rel = Equal | Less | Grt
                type index = hol_type
                fun get_type t =
                    dest_type t handle HOL_ERR _ =>
                        {Tyop = dest_vartype t, Args = []}
                fun compare t t' =
                    if t = t' then Equal
                    else
                        let
                            val {Tyop = Tyop_t, Args = Args_t} = get_type t
                            val {Tyop = Tyop_t', Args = Args_t'} = get_type t'
                        in
                            if Tyop_t < Tyop_t' then Less
                            else if Tyop_t' < Tyop_t then Grt
                                 else
                                     compare_args Args_t Args_t'
                        end
                and compare_args [] [] = Equal
                  | compare_args [] (_::_) = Less
                  | compare_args (_::_) [] = Grt
                  | compare_args (a::l) (a'::l') =
                    case compare a a' of
                        Equal => compare_args l l'
                      | Less => Less
                      | Grt => Grt
            end
        structure TypeTable = TableFunc (structure Entry = TypeEntry)
*)


        (*
         * Find a type equation which can be solved given that the
         * injections for types in inj_table have already been defined
         *)
        fun find_solvable {tyop_table, inj_table, equations = []} =
            raise DEF_TYPE_ERR {function = "find_solvable",
                                message = "no solution"}
          | find_solvable {tyop_table, inj_table, equations = ty::l} =
            let
                fun arg_solvable type_name (being_defined X) =
                    if X = type_name then true
                    else
                        (let
                             val {def, constructors, type_name} =
                                 case StringTable.lookup
                                     {key = X, table = tyop_table} of
                                     StringTable.NotFound =>
                                         raise DEF_TYPE_ERR
                                             {function = "find_solvable",
                                              message = "internal error:" ^
                                              " type not found"}
                                   | StringTable.InTable x => x
                         in
                             case def of
                                 Basic => true
                               | Type_op _ =>
                                     (case TypeTable.lookup
                                          {key = get_new_type X,
                                           table = inj_table} of
                                          TypeTable.NotFound => false
                                        | TypeTable.InTable _ => true)
                         end)
                  | arg_solvable type_name (existing _) = true
                fun constr_solvable type_name {arg_info, name} =
                    Lib.all (arg_solvable type_name) arg_info
                fun solvable {constructors, type_name, def} =
                    Lib.all (constr_solvable type_name) constructors
            in
                if solvable ty then
                    {solve = ty, new_list = l}
                else
                    let
                        val {solve, new_list} =
                            find_solvable {tyop_table = tyop_table,
                                           inj_table = inj_table,
                                           equations = l}
                    in
                        {solve = solve, new_list = ty::new_list}
                    end
            end

        (*
         * Type for storing isomorphisms between mutual type
         * representations and expanded type operators
         *)
        type map_table = {map : term, map_thm : thm} TypeTable.table



        (* Coerce the varaible form the range of the maps back to
         * the domain of the maps
         *)

        fun coerce_var {var = x, table = maps} =
            let
                val {Ty, Name} = dest_var x
            in
                case TypeTable.lookup {key = Ty, table = maps} of
                    TypeTable.NotFound => {var = x, coerced = x}
                  | TypeTable.InTable {map, map_thm} =>
                        let
                            val {dom, ...} = GenFuns.dom_cod map
                            val x' = mk_var {Name = Name, Ty = dom}
                        in
                            {var = x',
                             coerced = mk_comb {Rator = map,
                                                Rand = x'}}
                        end
            end

        (*
         * Coerce the argument types of a term if the types are
         *      in the map table
         * Returns the saturated term and the variables to abstract
         *)

        fun coerce_arg_vars (maps:map_table) t =
            let
                fun coerce ((t:term), (n:int)) =
                    let
                        val {dom, ...} = GenFuns.dom_cod t
                        val xname = "x" ^ (int_to_string n)
                        val {var, coerced} =
                            coerce_var {var =(mk_var {Ty = dom, Name = xname}),
                                        table = maps}
                        val {vars, coerced_term} =
                            coerce ((mk_comb {Rator = t,
                                             Rand = coerced}), (n + 1))
                    in
                        {vars = var::vars, coerced_term = coerced_term}
                    end
                handle HOL_ERR _ => {vars = [], coerced_term = t}
            in
                coerce (t, 0)
            end

        (*
         * Same as coerce_arg_vars, but does the abstractions
         *)
        fun coerce_args (maps:map_table) t =
            let
                val {vars, coerced_term} = coerce_arg_vars maps t
            in
                GenFuns.abslist vars coerced_term
            end

        (*
         * Returns specification of return value for a map (either
         *      injection or inverse) for one particular constructor
         *)
        fun define_map_case {maps : map_table,
                             new_map : term,
                             case_map : term,
                             case_val_map : term} =
            let
                val {cod = map_type, ...} = GenFuns.dom_cod new_map
                val {vars, coerced_term = rhs} =
                    coerce_arg_vars
                    (TypeTable.enter
                     {key = map_type,
                      entry = {map = new_map,
                               map_thm = REFL (--`1`--)},
                      table = maps}) case_val_map
                fun mk_lhs [] lhs = lhs
                  | mk_lhs (v::l) lhs =
                    mk_lhs l (GenFuns.mk_poly_comb {Rator = lhs, Rand = v})
            in
                mk_eq {lhs = mk_comb {Rator = new_map,
                                      Rand = mk_lhs vars case_map},
                       rhs = rhs}
            end

        (*
         * Define either an injection or an inverse, given a
         *      function which takes a functional specification and
         *      returns the function
         *)
        fun define_map {maps : map_table,
                        map_name : string,
                        map_type : hol_type,
                        rec_def_fun : string -> term -> thm,
                        lhs_vals : term list,
                        rhs_vals : term list} =
            let
                val new_map = mk_var {Name = map_name, Ty = map_type}
                fun mk_and [] [] =
                    raise DEF_TYPE_ERR {function = "define_map",
                                        message =
                                        "internal error: no constructors"}
                  | mk_and (lhs_val::ll) (rhs_val::rl) =
                    let
                        val constr_val =
                            define_map_case
                            {maps = maps,
                             new_map = new_map,
                             case_map = lhs_val,
                             case_val_map = rhs_val}
                    in
                        case (ll, rl) of
                            ([], []) => constr_val
                          | _      => mk_conj {conj1 = constr_val,
                                               conj2 = mk_and ll rl}
                    end
                  | mk_and _ _ =
                    raise DEF_TYPE_ERR {function = "define_injection",
                                        message =
                                     "internal error: mismatched constructors"}
                val map_thm = rec_def_fun map_name (mk_and lhs_vals rhs_vals)
            in
                {map = mk_const {Name = map_name, Ty = map_type},
                 map_thm = map_thm}
            end

        (*
         * If there's a map with codomain t in the table, return its domain
         *)
        fun coerce_type (maps:map_table) (t:hol_type) =
            case TypeTable.lookup {key = t, table = maps} of
                TypeTable.NotFound => t
              | TypeTable.InTable {map, map_thm} =>
                    let
                        val {dom, ...} = GenFuns.dom_cod map
                    in
                        dom
                    end

        fun get_rewrites (maps:map_table) =
            map (fn {map_thm, ...} => map_thm) (TypeTable.elts maps)

        fun get_id_eqn (constr : term) (t : hol_type) =
            let
                fun get_id_eqn_n (constr : term) (n:int) =
                    let
                        val {dom, cod} = GenFuns.dom_cod constr
                        val nstring = int_to_string n
                        val x = mk_var {Name = "x" ^ nstring, Ty = dom}
                    in
                        if dom = t then
                            let
                                val y = mk_var {Name = "y" ^ nstring, Ty = t}
                                val {recvars, vars, constr_sat} =
                                    get_id_eqn_n
                                    (GenFuns.mk_poly_comb {Rator = constr,
							   Rand = y}) (n + 1)
                            in
                                {recvars = y::recvars,
                                 vars = x::vars,
                                 constr_sat = constr_sat}
                            end
                        else
                            let
                                val {recvars, vars, constr_sat} =
                                    get_id_eqn_n
                                    (GenFuns.mk_poly_comb {Rator = constr,
							   Rand = x}) (n + 1)
                            in
                                {recvars = recvars,
                                 vars = x::vars,
                                 constr_sat = constr_sat}
                            end
                    end
                handle HOL_ERR _ =>
                    {recvars = [], vars = [], constr_sat = constr}
                val {recvars, vars, constr_sat} = get_id_eqn_n constr 0
            in
                GenFuns.abslist recvars (GenFuns.abslist vars constr_sat)
            end


        (*
         * Prove that inv o inj = 1
         *)
        fun get_inv_inj_thm {rec_thm,
                             injs,
                             invs,
                             old_ext_constrs,
                             inj,
                             inv,
                             inv_inj_rewrite_eqns,
                             ext_ty} =
            let
                val eu_thm =
                    ISPECL (map (fn c => get_id_eqn c ext_ty) old_ext_constrs)
                    rec_thm
                val uniq_thm = CONJUNCT2 (CONV_RULE EXISTS_UNIQUE_CONV eu_thm)
                val x = mk_var {Name = "x", Ty = ext_ty}
                val id = mk_abs {Bvar = x, Body = x}
                val inv_inj = mk_abs {Bvar = x,
                                      Body = mk_comb
                                      {Rator = inv,
                                       Rand = mk_comb {Rator = inj,
                                                       Rand = x}}}
                val inst_uniq_thm = BETA_RULE (SPECL [inv_inj, id] uniq_thm)
                val inv_inj_eq_thm =
                    REWRITE_RULE ((get_rewrites invs) @
                                  (get_rewrites injs) @
                                  inv_inj_rewrite_eqns) inst_uniq_thm
                val jvx = mk_comb {Rator = inv_inj, Rand = x}
                val f = mk_var {Name = "f", Ty = type_of id}
                val app_thm = SUBST [f |-> inv_inj_eq_thm]
                    (mk_eq {lhs = jvx, rhs = mk_comb {Rator = f, Rand = x}})
                    (REFL jvx)
                val final = GEN x (BETA_RULE app_thm)
            in
                final
            end

        (*
         * Define inj : Type_op (Args) -> Type_op_Args
         * and    inv : Type_op_Args   -> Type_op (Args)
         *)
        fun define_inj_inv {injs,
                            invs,
                            inj_o_invs,
                            type_name,
                            inj_rec_thm,
                            inj_def_fun,
                            inv_def_fun,
                            inv_inj_rewrite_eqns,
                            tyop_args,
                            tyop_name,
                            original_constructors} =
            let
                val args = map ((coerce_type injs) o raise_type_info) tyop_args
                val inj_range = get_new_type type_name
                val inv_range = mk_type {Tyop = tyop_name, Args = args}
                val int_vals = lookup_int_constructors type_name
                val old_vals = original_constructors args
                val inj_name = "int_inj_" ^ type_name
                val inj_ty = mk_type {Tyop = "fun",
                                      Args = [inv_range, inj_range]}
                val inj_map as {map = new_inj, map_thm = new_inj_thm}
                    = define_map {maps = injs,
                                  map_name = inj_name,
                                  map_type = inj_ty,
                                  rec_def_fun = inj_def_fun,
                                  lhs_vals = old_vals,
                                  rhs_vals = int_vals}
                val inv_name = "int_inv_" ^ type_name
                val inv_ty = mk_type {Tyop = "fun",
                                      Args = [inj_range, inv_range]}
                val inv_map as {map = new_inv, map_thm = new_inv_thm} =
                    define_map {maps = invs,
                                map_name = inv_name,
                                map_type = inv_ty,
                                rec_def_fun = inv_def_fun,
                                lhs_vals = int_vals,
                                rhs_vals = old_vals}
                val new_injs = TypeTable.enter {key = inj_range,
                                                entry = inj_map,
                                                table = injs}
                val new_invs = TypeTable.enter {key = inv_range,
                                                entry = inv_map,
                                                table = invs}
                val inv_inj_thm =
                    get_inv_inj_thm {rec_thm = inj_rec_thm,
                                     injs = new_injs,
                                     invs = new_invs,
                                     old_ext_constrs = old_vals,
                                     inj = new_inj,
                                     inv = new_inv,
                                     inv_inj_rewrite_eqns =
                                     inv_inj_rewrite_eqns,
                                     ext_ty = inv_range}
                val new_inj_o_inv =
                    let val x = mk_var {Name = "x", Ty = inj_range}
                    in {Bvar = x,
                        Body = mk_comb
                        {Rator = new_inj,
                         Rand = mk_comb {Rator = new_inv,
                                         Rand = x}}}
                    end
                val new_inj_o_invs =
                    StringTable.enter{key= type_name,
                                      entry = new_inj_o_inv,
                                      table = inj_o_invs}
            in
                {injs = new_injs,
                 invs = new_invs,
                 inv_inj_thm = inv_inj_thm,
                 inj_o_invs = new_inj_o_invs}
            end

        (*
         * Define constructors for one of the originally specified types
         * It needs the injection table to coerce constructors from
         *      internal representations of type operators to type operators
         *)
        fun make_constructors inj_table {type_name, constructors, def} =
            let
                fun do_defines [] = []
                  | do_defines ((constr as {name, arg_info})::constrs) =
                    let
                        val int_const =
                            Lib.first
                            (fn c => #Name(dest_const c) =
                             "int_" ^
                             (TypeOps_mk_symbolic_free_const_name name))
                            (lookup_int_constructors type_name)
                        val {vars, coerced_term} =
                            coerce_arg_vars inj_table int_const
                        val constr_term = GenFuns.abslist vars coerced_term
                        val constr_spec = {Name = name,
                                           Ty = type_of constr_term}
                        val new_defn =
                            new_definition
                            (name, mk_eq {lhs = mk_var constr_spec,
                                          rhs = constr_term})
                        val f = mk_var {Name = "f", Ty = type_of constr_term}
                        val eq = mk_eq {lhs = GenFuns.applist vars f,
                                        rhs = GenFuns.applist vars
                                        (mk_const constr_spec)}
                        val eqn = GENL vars
                                  (BETA_RULE
                                   (SUBST [f |-> new_defn]
                                          eq (REFL (GenFuns.applist
                                                    vars
                                                    (mk_const constr_spec)))))
                    in
                         eqn :: (do_defines constrs)
                    end
            in
                do_defines constructors
            end

        (*
         * Define injections, inverses, reductions, and constructors
         *)
        fun define_all_maps tyop_table l =
            let
                fun def_all_maps jv [] = jv
                  | def_all_maps {injs, invs, inj_o_invs,
                                  inv_inj_rewrite_eqns, constructor_defs} l =
                    let
                        val {solve = solve as {type_name, def, ...},
                             new_list} =
                            find_solvable {tyop_table = tyop_table,
                                           inj_table = injs,
                                           equations = l}
                    in
                        case def of
                            Basic =>
                                def_all_maps
                                {injs = injs,
                                 invs = invs,
                                 inj_o_invs = inj_o_invs,
                                 inv_inj_rewrite_eqns = inv_inj_rewrite_eqns,
                                 constructor_defs =
                                 make_constructors injs solve @
                                 constructor_defs}
                                new_list
                          | Type_op {original_constructors,
                                     rec_thm, tyop_args, tyop_name} =>
                                let
                                    fun prim_def_fun s t =
                                        new_recursive_definition
                                        {fixity = Prefix,
                                         name = s,
                                         rec_axiom = rec_thm,
                                         def = t}
                                    fun mut_def_fun s t =
                                        define_mutual_functions
                                        {name = s,
                                         rec_axiom =
                                         MRD_New_Ty_Existence_Thm,
                                         fixities = NONE,
                                         def = t}
                                    val {injs, invs, inj_o_invs,
                                         inv_inj_thm} =
                                        define_inj_inv
                                        {injs = injs,
                                         invs = invs,
                                         inj_o_invs =
                                         inj_o_invs,
                                         inj_rec_thm = rec_thm,
                                         type_name = type_name,
                                         inj_def_fun = prim_def_fun,
                                         inv_def_fun = mut_def_fun,
                                         inv_inj_rewrite_eqns =
                                         inv_inj_rewrite_eqns,
                                         tyop_args = tyop_args,
                                         tyop_name = tyop_name,
                                         original_constructors =
                                         original_constructors}
                        in
                                    def_all_maps {injs = injs,
                                                  invs = invs,
                                                  inj_o_invs =
                                                  inj_o_invs,
                                                  inv_inj_rewrite_eqns =
                                                  inv_inj_thm::
                                                  inv_inj_rewrite_eqns,
                                                  constructor_defs =
                                                  constructor_defs}
                                    new_list
                                end
                    end
            in
                def_all_maps {injs = TypeTable.empty,
                              invs = TypeTable.empty,
                              inj_o_invs = StringTable.empty,
                              inv_inj_rewrite_eqns = [],
                              constructor_defs = []} l
            end

        val {injs = inj_table, invs = inv_table, inj_o_invs,
             inv_inj_rewrite_eqns, constructor_defs} =
            define_all_maps types (StringTable.elts types)



        fun coerce_term {dom_maps:map_table,
                         cod_maps:map_table,
                         coercee:term}  =
            case TypeTable.lookup {key = type_of coercee, table = cod_maps} of
                TypeTable.NotFound => coercee
              | TypeTable.InTable {map, map_thm} =>
                    let
                        val {dom, ...} = GenFuns.dom_cod map
                    in
                        case TypeTable.lookup {key = dom, table = dom_maps} of
                            TypeTable.NotFound => coercee
                          | TypeTable.InTable {map, map_thm} =>
                                mk_comb {Rator = map, Rand = coercee}
                    end

        (*
         * Since inj : Type_op Args -> Type_op_Args, we rewrite by
         *      the inverse of the theorems about the injection to get
         *      the correct left-hand sides for the theorem
         * For example,
         *      inj [] = int_NIL
         * causes
         *      fn1 int_NIL = int_NIL_case
         * to rewrite to
         *      fn1 (inj []) = int_NIL_case
         * fn1 o inj will be the function for our theorem
         *)

        val inv_rewrites = get_rewrites inv_table
        val inj_rewrites = get_rewrites inj_table

        local
            fun flip_eqn th =
                let
                    val {Body, Bvar} = dest_forall (concl th)
                in
                    GEN Bvar (flip_eqn (SPEC Bvar th))
                end
            handle HOL_ERR _ => SYM th
        in
            val flipped_inj_rewrites =
                map (GenFuns.conj_map flip_eqn) inj_rewrites
        end


        local
            fun mk_prop type_name =
                (case StringTable.lookup {key = type_name,
                                          table = inj_o_invs}
                     of StringTable.NotFound =>
                         mk_abs{Bvar = mk_var{Name = "x",
                                              Ty = get_new_type type_name},
                                Body = (--`T`--)}
                       | StringTable.InTable {Bvar, Body} =>
                             mk_abs {Bvar = Bvar,
                                     Body = mk_eq{lhs = Body, rhs = Bvar}})

            val props = map (mk_prop o (#type_name)) mut_rec_ty_spec

            val thm1 = REWRITE_RULE inj_rewrites
                (REWRITE_RULE inv_rewrites
                 (BETA_RULE (ISPECL props MRD_New_Ty_Induct_Thm)))

            val thm2 = if is_imp (concl thm1)
			   then MP thm1 (prove (#ant(dest_imp(concl thm1)),
						(REPEAT STRIP_TAC) THEN
						(ASM_REWRITE_TAC [])))
		       else thm1
        in
            val sym_inj_inv_rewrite_eqns =
		map (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV))
		    (CONJUNCTS thm2)
        end



       val inj_one_one_lemmas =
           map (MATCH_MP GenFuns.one_one_lemma) inv_inj_rewrite_eqns

        (*
         * Take a theorem with forall-quantification and instantiate
         *      the quantified variables with coerced versions of them
         * Return the newly quantified variables and the
         *      instantiated theorem
         *)

        fun change_type map_table ty =
            let
                val {dom, cod} = GenFuns.dom_cod_ty ty
            in
                mk_type {Tyop = "fun",
                         Args = [coerce_type map_table dom,
                                 change_type map_table cod]}
            end handle HOL_ERR _ => coerce_type map_table ty

        fun coerce_args_term {dom_maps, cod_maps, term} =
            let
                val {vars, coerced_term} = coerce_arg_vars cod_maps term
            in
                GenFuns.abslist vars (coerce_term {dom_maps = dom_maps,
                                           cod_maps = cod_maps,
                                           coercee = coerced_term})
            end

        fun strip_int Name =
            let val len = String.size Name
            in if len >4 andalso String.substring (Name,0,4) = "int_"
                   then String.substring (Name,4,len - 4)
               else Name
            end

        fun change_var t =
            let
                val {Ty, Name} = dest_var t
            in
                mk_var {Name = strip_int Name,
                        Ty = change_type inj_table Ty}
            end


        local
            exception NotForall
        in
            fun spec_change_foralls thm =
                let
                    val {Bvar, ...} = dest_forall (concl thm)
                        handle HOL_ERR _ => raise NotForall
                    val new_forall_var = change_var Bvar
                    val instance = coerce_args_term {dom_maps = inj_table,
                                                     cod_maps = inv_table,
                                                     term = new_forall_var}
                    val {new_forall_vars, instances, new_forall_thm} =
                        spec_change_foralls (SPEC instance thm)
                in
                    {new_forall_vars = new_forall_var :: new_forall_vars,
                     instances = instance :: instances,
                     new_forall_thm = new_forall_thm}
                end
            handle NotForall => {new_forall_vars = [],
                                 instances = [],
                                 new_forall_thm = thm}
        end

        fun change_foralls thm =
            let
                val {new_forall_vars, new_forall_thm,...} =
                    spec_change_foralls thm
                val changed =
                    BETA_RULE
                    (REWRITE_RULE flipped_inj_rewrites new_forall_thm)
            in
                GENL new_forall_vars changed
            end

        (*
         * mk_fun_exists_coercion creates:
         *      - a coercion_fun for GEN_EXISTS_FROM_EXISTS_RULE
         *      - a conversion which changes full applications of
         *              the coercion_fun into abstractions
         * For example, if we have
         *      fn1 (inj x)
         * we really want
         *      (\fn1 x. fn1 (inj x)) fn1 x
         *)

        fun mk_fun_exists_coercion var =
            let
                val {vars, coerced_term} = coerce_arg_vars inj_table var
                val coerced = GenFuns.abslist vars coerced_term
                val coercion_fun = mk_abs {Bvar = var,
                                           Body = coerced}
                val coercion_appfn = GenFuns.applist vars coerced
                val coerce_eqn = DEPTH_CONV BETA_CONV coercion_appfn
                val test = rhs (concl coerce_eqn)
                val {func = test_func, args = test_args} =
		    GenFuns.dest_appln test
                fun coercion_CONV t =
                    let
                        val {func, args} = GenFuns.dest_appln t
                        val match = fst (match_term test t)
                    in
                        if func = test_func then
                            SYM (DEPTH_CONV BETA_CONV
                                 (subst match coercion_appfn))
                        else raise HOL_ERR {message = "no match",
                                            origin_function =
                                            "mk_fun_exists_coercion",
                                            origin_structure = "top"}
                    end
            in
                {coercion_fun = coercion_fun, coercion_CONV = coercion_CONV}
            end

        (*
         * Do the rewriting necessary to change the mutual recursive
         *      existential theorem into the simply type existential thm
         *)
        fun change_fun_exists {exists_term, exists_thm} =
            let
                val (vars, base_t) = strip_exists exists_term
                val coercions = map mk_fun_exists_coercion vars
                val {coercion_funs, coercion_CONVs} =
                    foldr (fn ({coercion_fun, coercion_CONV},
                               {coercion_funs, coercion_CONVs}) =>
                           {coercion_funs = coercion_fun::coercion_funs,
                            coercion_CONVs = coercion_CONV::coercion_CONVs})
                     {coercion_funs = [],coercion_CONVs = []} coercions
                val int_var = mk_var {Name = "int_var",
                                      Ty = type_of base_t}

                val seed = GenFuns.conj_map change_foralls  (ASSUME base_t)
                (*
                 * This should very possibly use ORELSEC instead of
                 * doing each conversion
                 *)
                val forall_imp_thm =
                    GENL vars
                         (DISCH base_t
                          (SUBST [int_var |-> foldr (fn (conv, th) =>
                                                TRANS
                                                th
                                                (ONCE_DEPTH_CONV
                                                 conv
                                                 (rhs (concl th))))
                                                (REFL (concl seed))
                                                coercion_CONVs]
                                  int_var
                                  seed))
            in
                ExistsFuns.GEN_EXISTS_FROM_EXISTS_RULE
                {exists_thm = exists_thm,
                 forall_imp_thm = forall_imp_thm,
                 coercion_funs = coercion_funs}
            end

        (*
         * Take the mutual recursive recursor and massage it into
         * the recursor for our simple type with embedded type operators
         *)

        local
            val {new_forall_vars, instances, new_forall_thm} =
                spec_change_foralls MRD_New_Ty_Existence_Thm
        in
            val New_Ty_Existence_Thm =
                GENL new_forall_vars
                (REWRITE_RULE constructor_defs
                 (REWRITE_RULE inv_inj_rewrite_eqns
                  (change_fun_exists {exists_term = concl new_forall_thm,
                                      exists_thm = new_forall_thm})))
            val ext_case_vars = new_forall_vars
            val case_instances = instances
        end


        fun mk_arg_exists_coercion var =
            (case TypeTable.lookup {key = type_of var,table = inj_table}
                 of TypeTable.NotFound =>
                     let val id = mk_abs{Bvar = var,Body = var}
                     in
                         {coercion_fun = id,
                          coerced_term = mk_comb{Rator = id, Rand = var}}
                     end
               | TypeTable.InTable {map = inj,...} =>
                     (case TypeTable.lookup {key = #dom(GenFuns.dom_cod inj),
                                             table = inv_table}
                          of TypeTable.NotFound =>
                              Raise (DEF_TYPE_ERR
                                     {function = "mk_arg_exists_coercion",
                                      message = "Impossible!"})
                        | TypeTable.InTable {map = inv,...} =>
                              {coercion_fun = inv,
                               coerced_term =
                               mk_comb{Rator=inj,
                                       Rand=mk_comb{Rator=inv,
                                                    Rand=var}}}))


        (*
         * change_arg_exists:
         *  ?int_x1 ... int_xn. P int_x1 ... int_xn  ==>>
         *  ?ext_x1 ... ext_xn. P (inj_1 ext_x1) ... (inj_n ext_xn)
         *)

        fun change_arg_exists exists_thm =
            let
                val (vars, P) = strip_exists (concl exists_thm)
                val {substitution, coercion_funs} =
                    foldr
                    (fn (v, {substitution, coercion_funs}) =>
                     (case mk_arg_exists_coercion v of
                          {coerced_term, coercion_fun} =>
			      {substitution = (v |->
                                 ONCE_REWRITE_CONV sym_inj_inv_rewrite_eqns v)
                                :: substitution,
                               coercion_funs = coercion_fun ::coercion_funs}))
                    {substitution = [], coercion_funs = []}
                    vars

                val forall_imp_thm =
		    GENL vars (DISCH P (SUBST substitution P (ASSUME P)))
            in
                ExistsFuns.GEN_EXISTS_FROM_EXISTS_RULE
                {exists_thm = exists_thm,
                 forall_imp_thm = forall_imp_thm,
                 coercion_funs = coercion_funs}
            end


    (* (!int_x1 ... int_xn. P) ==> Q ==>> (!ext_x1 ... ext_xn. P') ==> Q *)

        fun change_left_forall thm =
            CONV_RULE GenFuns.LIST_EXISTS_IMP_CONV
            (change_arg_exists
             (CONV_RULE GenFuns.LEFT_IMP_LIST_FORALL_CONV thm))


        fun change_hyps_foralls {hyps = [], thm, ...} =
	    (PURE_REWRITE_RULE flipped_inj_rewrites thm)
          | change_hyps_foralls {hyps = (h::hyps), thm} =
            change_hyps_foralls {hyps = hyps,
                                 thm = PURE_ONCE_REWRITE_RULE
				 [GenFuns.UNCURRY_LEMMA]
                                 (change_left_forall (DISCH h thm))}


        local
            val {new_forall_thm, instances, new_forall_vars} =
                spec_change_foralls
                (SPECL case_instances MRD_New_Ty_Uniqueness_Thm)
            val thm1 =
                UNDISCH
                (PURE_ONCE_REWRITE_RULE [GenFuns.CURRY_LEMMA]
                 (BETA_RULE
                  (CONV_RULE (DEPTH_CONV FUN_EQ_CONV) new_forall_thm)))
            val first_hyp = hd (hyp thm1)
            val fun_lemma = SYM (FUN_EQ_CONV (--`f = (g:'a -> 'b)`--))
            val thm2 =
                PURE_REWRITE_RULE [fun_lemma]
                (PURE_REWRITE_RULE inv_inj_rewrite_eqns
                 (GenFuns.conj_map change_foralls (UNDISCH thm1)))
            val thm3 =
                change_hyps_foralls
                (GenFuns.REPEAT_UNDISCH
		 (PURE_REWRITE_RULE [GenFuns.CURRY_LEMMA]
		  (DISCH first_hyp thm2)))
            val snd_hyp = hd (hyp thm3)
            val thm4 =
                DISCH_ALL
                (change_hyps_foralls
                 (GenFuns.REPEAT_UNDISCH
		  (PURE_REWRITE_RULE [GenFuns.CURRY_LEMMA]
		   (DISCH snd_hyp (UNDISCH thm3)))))
            val thm5 =
                PURE_REWRITE_RULE inv_inj_rewrite_eqns
		(PURE_REWRITE_RULE constructor_defs thm4)

        in
            val New_Ty_Uniqueness_Thm =
                GENL ext_case_vars (GENL new_forall_vars thm5)
        end;


	local
	    val thm1 = change_foralls MRD_New_Ty_Induct_Thm
	    val prop_vars = #1(strip_forall (concl thm1))
	    val thm2 = SPECL prop_vars thm1
	    val {hyps, thm = thm3} =
		GenFuns.REPEAT_UNDISCH
		(PURE_REWRITE_RULE [GenFuns.CURRY_LEMMA] thm2)
	    val thm4 =
		PURE_REWRITE_RULE inv_inj_rewrite_eqns
		(GenFuns.conj_map change_foralls thm3)
	    val thm5 = change_hyps_foralls {hyps = hyps, thm = thm4}
	in
	    val New_Ty_Induct_Thm =
		GENL prop_vars
		(PURE_REWRITE_RULE inv_inj_rewrite_eqns
		 (PURE_REWRITE_RULE constructor_defs thm5))
	end


(*        structure ConsThms = ConsThmsFunc(structure numLib = numLib
                                          structure MutRecDef = MutRecDef)
*)
       val {mutual_constructors_distinct,
            mutual_constructors_one_one,
            mutual_cases,
            argument_extraction_definitions}
              = ConsThms.build {New_Ty_Existence_Thm = MRD_New_Ty_Existence_Thm,
                                New_Ty_Induct_Thm = MRD_New_Ty_Induct_Thm,
                                New_Ty_Uniqueness_Thm=MRD_New_Ty_Uniqueness_Thm};

        val Constructors_Distinct_Thm =
              PURE_REWRITE_RULE inj_one_one_lemmas
	      (PURE_REWRITE_RULE inv_inj_rewrite_eqns
	       (PURE_REWRITE_RULE constructor_defs
                (GenFuns.conj_map change_foralls
                 mutual_constructors_distinct)))

        val Constructors_One_One_Thm =
              PURE_REWRITE_RULE inj_one_one_lemmas
	      (PURE_REWRITE_RULE inv_inj_rewrite_eqns
	       (PURE_REWRITE_RULE constructor_defs
                (GenFuns.conj_map change_foralls
		 mutual_constructors_one_one)))

        val Cases_Thm =
	    PURE_REWRITE_RULE inj_one_one_lemmas
	    (PURE_REWRITE_RULE constructor_defs
	     (GenFuns.conj_map (fn th => change_foralls
				(GenFuns.forall_map
				 (GenFuns.disj_map change_arg_exists) th))
	      mutual_cases))

   in
      {New_Ty_Induct_Thm = New_Ty_Induct_Thm,
       New_Ty_Uniqueness_Thm = New_Ty_Uniqueness_Thm,
       New_Ty_Existence_Thm = New_Ty_Existence_Thm,
       Constructors_Distinct_Thm = Constructors_Distinct_Thm,
       Constructors_One_One_Thm = Constructors_One_One_Thm,
       Cases_Thm = Cases_Thm}
   end

end;
