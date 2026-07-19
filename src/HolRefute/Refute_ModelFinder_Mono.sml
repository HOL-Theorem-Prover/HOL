(*
 * Monotonicity inference for the model-finder backend.
 *
 * This file contains the mtype and constraint-solving half of the
 * Isabelle Nitpick monotonicity calculus.  Formula traversal continues in
 * the next implementation stage.
 *)

structure Refute_ModelFinder_Mono :> REFUTE_MODEL_FINDER_MONO = struct
  structure MFH = Refute_ModelFinder_HOL
  structure PS = Refute_PropSat

  datatype sign = Plus | Minus
  datatype annotation = Gen | New | Fls | Tru
  datatype annotation_atom = A of annotation | V of int

  type assign_literal = int * (sign * annotation)

  datatype mtyp =
      MAlpha
    | MFun of mtyp * annotation_atom * mtyp
    | MPair of mtyp * mtyp
    | MType of string * mtyp list
    | MRec of Type.hol_type

  type mdata =
    {context : MFH.mf_context,
     binarize : bool,
     alpha_ty : Type.hol_type,
     max_fresh : int ref,
     data_type_mcache : (Type.hol_type * mtyp) list ref,
     constr_mcache : (Term.term * mtyp) list ref}

  exception UNSOLVABLE of unit
  exception MTYPE of string * mtyp list * Type.hol_type list

  val trace = ref false

  fun trace_msg thunk =
    if !trace then Feedback.HOL_MESG (thunk ()) else ()

  fun fresh counter =
    let val result = !counter + 1
    in counter := result; result end

  fun member equal value = List.exists (fn other => equal (value, other))

  fun insert equal value values =
    if member equal value values then values else value :: values

  fun same_type (left, right) = left = right
  fun same_mtype (left, right) = left = right
  fun same_term (left, right) = Term.aconv left right

  fun lookup equal key pairs =
    case List.find (fn (other, _) => equal (key, other)) pairs of
        SOME (_, value) => SOME value
      | NONE => NONE

  fun update equal (key, value) pairs =
    (key, value) ::
    List.filter (fn (other, _) => not (equal (key, other))) pairs

  fun type_name ty =
    if Type.is_vartype ty then Type.dest_vartype ty
    else
      let val {Thy, Tyop, ...} = Type.dest_thy_type ty
      in Thy ^ "$" ^ Tyop end

  val bool_M = MType ("min$bool", [])

  fun is_MRec (MRec _) = true
    | is_MRec _ = false

  fun flatten_mtype (MPair (left, right)) =
        flatten_mtype left @ flatten_mtype right
    | flatten_mtype (MType (_, arguments)) =
        List.concat (map flatten_mtype arguments)
    | flatten_mtype mtype = [mtype]

  fun initial_mdata context binarize alpha_ty : mdata =
    {context = context,
     binarize = binarize,
     alpha_ty = alpha_ty,
     max_fresh = ref 0,
     data_type_mcache = ref [],
     constr_mcache = ref []}

  fun type_arguments ty =
    if Type.is_vartype ty then []
    else #Args (Type.dest_thy_type ty)

  fun could_exist_alpha_subtype alpha_ty ty =
    same_type (alpha_ty, ty) orelse
    List.exists (could_exist_alpha_subtype alpha_ty) (type_arguments ty)

  fun could_exist_alpha_sub_mtype _ alpha_ty ty =
    if Type.is_vartype alpha_ty then
      could_exist_alpha_subtype alpha_ty ty
    else
      same_type (alpha_ty, ty) orelse MFH.is_data_type ty

  fun exists_alpha_sub_mtype MAlpha = true
    | exists_alpha_sub_mtype (MFun (left, _, right)) =
        exists_alpha_sub_mtype left orelse exists_alpha_sub_mtype right
    | exists_alpha_sub_mtype (MPair (left, right)) =
        exists_alpha_sub_mtype left orelse exists_alpha_sub_mtype right
    | exists_alpha_sub_mtype (MType (_, arguments)) =
        List.exists exists_alpha_sub_mtype arguments
    | exists_alpha_sub_mtype (MRec _) = true

  fun exists_alpha_sub_mtype_fresh MAlpha = true
    | exists_alpha_sub_mtype_fresh (MFun (_, V _, _)) = true
    | exists_alpha_sub_mtype_fresh (MFun (_, _, right)) =
        exists_alpha_sub_mtype_fresh right
    | exists_alpha_sub_mtype_fresh (MPair (left, right)) =
        exists_alpha_sub_mtype_fresh left orelse
        exists_alpha_sub_mtype_fresh right
    | exists_alpha_sub_mtype_fresh (MType (_, arguments)) =
        List.exists exists_alpha_sub_mtype_fresh arguments
    | exists_alpha_sub_mtype_fresh (MRec _) = true

  fun constr_mtype_for_binders ty mtypes =
    List.foldr (fn (mtype, result) =>
      MFun (mtype, A Gen, result)) (MRec ty) mtypes

  fun repair_mtype _ _ MAlpha = MAlpha
    | repair_mtype cache seen (MFun (left, atom, right)) =
        MFun (repair_mtype cache seen left, atom,
          repair_mtype cache seen right)
    | repair_mtype cache seen (MPair (left, right)) =
        MPair (repair_mtype cache seen left,
          repair_mtype cache seen right)
    | repair_mtype cache seen (MType (name, arguments)) =
        MType (name,
          List.concat (map
            (flatten_mtype o repair_mtype cache seen) arguments))
    | repair_mtype cache seen (MRec ty) =
        (case lookup same_type ty cache of
             SOME (MRec _) => MType (type_name ty, [])
           | SOME mtype =>
               if member same_mtype mtype seen then
                 MType (type_name ty, [])
               else
                 repair_mtype cache (mtype :: seen) mtype
           | NONE =>
               raise MTYPE
                 ("Refute_ModelFinder_Mono.repair_mtype", [], [ty]))

  fun repair_data_type_mcache cache =
    List.app (fn (ty, mtype) =>
      cache := update same_type
        (ty, repair_mtype (!cache) [] mtype) (!cache))
      (rev (!cache))

  fun repair_constr_mcache dtype_cache constr_cache =
    List.app (fn (constructor, mtype) =>
      constr_cache := update same_term
        (constructor, repair_mtype dtype_cache [] mtype)
        (!constr_cache)) (!constr_cache)

  fun body_type ty = #2 (boolSyntax.strip_fun ty)

  fun is_fin_fun_supported_type ty =
    MFH.is_boolean_type ty orelse optionSyntax.is_option ty

  fun union_mtypes new old =
    List.foldl (fn (mtype, result) =>
      insert same_mtype mtype result) old new

  fun fresh_mfun_for_fun_type
        (mdata as {max_fresh, ...} : mdata) all_minus domain range =
    let
      val domain_mtype = fresh_mtype_for_type mdata all_minus domain
      val range_mtype = fresh_mtype_for_type mdata all_minus range
      val atom =
        if not all_minus andalso
           exists_alpha_sub_mtype_fresh domain_mtype andalso
           is_fin_fun_supported_type (body_type range) then
          V (fresh max_fresh)
        else
          A Gen
    in
      (domain_mtype, atom, range_mtype)
    end
  and fresh_mtype_for_type
        (mdata as
          {context, alpha_ty, data_type_mcache, constr_mcache, ...} : mdata)
        all_minus ty =
    let
      fun nominal_type current =
        if not (could_exist_alpha_sub_mtype context alpha_ty current) then
          MType (type_name current, [])
        else
          case lookup same_type current (!data_type_mcache) of
              SOME mtype => mtype
            | NONE =>
                let
                  val _ = data_type_mcache :=
                    (current, MRec current) :: !data_type_mcache
                  val constructors = MFH.data_type_constrs context current
                  fun do_constructor constructor
                        (all_mtypes, constructor_mtypes) =
                    let
                      val binder_mtypes = map do_type
                        (MFH.constructor_arg_types constructor)
                      val new_mtypes = List.filter
                        exists_alpha_sub_mtype_fresh binder_mtypes
                    in
                      (union_mtypes new_mtypes all_mtypes,
                       constr_mtype_for_binders current binder_mtypes ::
                         constructor_mtypes)
                    end
                  val (all_mtypes, reversed_constructor_mtypes) =
                    List.foldl (fn (constructor, result) =>
                      do_constructor constructor result) ([], [])
                      constructors
                  val constructor_mtypes =
                    rev reversed_constructor_mtypes
                  val mtype = MType (type_name current, all_mtypes)
                  val _ = data_type_mcache := update same_type
                    (current, mtype) (!data_type_mcache)
                  val _ = ListPair.appEq
                    (fn (constructor, constructor_mtype) =>
                      constr_mcache := update same_term
                        (constructor, constructor_mtype) (!constr_mcache))
                    (constructors, constructor_mtypes)
                in
                  if List.all (not o is_MRec o #2)
                       (!data_type_mcache) then
                    (repair_data_type_mcache data_type_mcache;
                     repair_constr_mcache (!data_type_mcache)
                       constr_mcache;
                     case lookup same_type current
                            (!data_type_mcache) of
                         SOME repaired => repaired
                       | NONE => raise MTYPE
                           ("Refute_ModelFinder_Mono.mtype_of_type",
                            [], [current]))
                  else
                    mtype
                end
      and do_type current =
        if same_type (current, alpha_ty) then
          MAlpha
        else if MFH.is_pair_type current then
          let val (left, right) = pairSyntax.dest_prod current
          in MPair (do_type left, do_type right) end
        else
          case Lib.total Type.dom_rng current of
              SOME (domain, range) =>
                MFun (fresh_mfun_for_fun_type mdata all_minus
                  domain range)
            | NONE =>
                if Type.is_vartype current then
                  MType (Type.dest_vartype current, [])
                else
                  nominal_type current
    in
      do_type ty
    end

  fun mtype_for_constr
        (mdata as {context, alpha_ty, constr_mcache, ...} : mdata)
        constructor =
    let val ty = Term.type_of constructor
    in
      if could_exist_alpha_sub_mtype context alpha_ty ty then
        case lookup same_term constructor (!constr_mcache) of
            SOME mtype => mtype
          | NONE =>
              if same_type (ty, alpha_ty) then
                let
                  val mtype = fresh_mtype_for_type mdata false ty
                  val _ = constr_mcache := update same_term
                    (constructor, mtype) (!constr_mcache)
                in
                  mtype
                end
              else
                let
                  val _ = fresh_mtype_for_type mdata false
                    (MFH.constructor_result_type constructor)
                in
                  case lookup same_term constructor
                         (!constr_mcache) of
                      SOME mtype => mtype
                    | NONE => raise MTYPE
                        ("Refute_ModelFinder_Mono.mtype_for_constr",
                         [], [ty])
                end
      else
        fresh_mtype_for_type mdata false ty
    end

  datatype comp_op = Eq | Neq | Leq
  type comp = annotation_atom * annotation_atom * comp_op * int list
  type assign_clause = assign_literal list
  type constraint_set = comp list * assign_clause list

  val empty_constraints : constraint_set = ([], [])

  fun add_assign_literal (literal as (x, (sign, annotation))) clauses =
    if List.exists
         (fn [(x', (sign', annotation'))] =>
                x = x' andalso
                ((sign = sign' andalso annotation <> annotation') orelse
                 (sign <> sign' andalso annotation = annotation'))
           | _ => false) clauses then
      NONE
    else
      SOME ([literal] :: clauses)

  fun add_assign_disjunct _ NONE = NONE
    | add_assign_disjunct literal (SOME literals) =
        SOME (insert (op =) literal literals)

  fun add_assign_clause_opt NONE clauses = clauses
    | add_assign_clause_opt (SOME clause) clauses =
        insert (op =) clause clauses

  fun annotation_comp Eq left right = left = right
    | annotation_comp Neq left right = left <> right
    | annotation_comp Leq left right =
        left = right orelse right = Gen

  fun sign_for_comp_op Eq = Plus
    | sign_for_comp_op Neq = Minus
    | sign_for_comp_op Leq =
        raise Fail "Refute_ModelFinder_Mono.sign_for_comp_op: Leq"

  fun do_annotation_atom_comp Leq [] left right
        (constraints as (comps, clauses)) =
        (case (left, right) of
             (A left', A right') =>
               if annotation_comp Leq left' right' then
                 SOME constraints
               else
                 NONE
           | _ =>
               SOME
                 (insert (op =) (left, right, Leq, []) comps, clauses))
    | do_annotation_atom_comp comparison [] left right
        (constraints as (comps, clauses)) =
        (case (left, right) of
             (A left', A right') =>
               if annotation_comp comparison left' right' then
                 SOME constraints
               else
                 NONE
           | (V x, A annotation) =>
               Option.map (fn clauses' => (comps, clauses'))
                 (add_assign_literal
                   (x, (sign_for_comp_op comparison, annotation)) clauses)
           | (A _, V _) =>
               do_annotation_atom_comp comparison [] right left constraints
           | (V _, V _) =>
               SOME
                 (insert (op =)
                   (left, right, comparison, []) comps, clauses))
    | do_annotation_atom_comp comparison unless left right
        (comps, clauses) =
        SOME
          (insert (op =)
            (left, right, comparison, unless) comps, clauses)

  fun add_annotation_atom_comp comparison unless left right constraints =
    case do_annotation_atom_comp comparison unless left right constraints of
        SOME result => result
      | NONE => raise UNSOLVABLE ()

  fun do_mtype_comp _ _ _ _ NONE = NONE
    | do_mtype_comp _ _ MAlpha MAlpha constraints = constraints
    | do_mtype_comp Eq unless
        (MFun (left_domain, left_atom, left_range))
        (MFun (right_domain, right_atom, right_range))
        (SOME constraints) =
        do_mtype_comp Eq unless left_range right_range
          (do_mtype_comp Eq unless left_domain right_domain
            (do_annotation_atom_comp Eq unless left_atom right_atom
              constraints))
    | do_mtype_comp Leq unless
        (MFun (left_domain, left_atom, left_range))
        (MFun (right_domain, right_atom, right_range))
        (SOME constraints) =
        let
          val domains =
            if exists_alpha_sub_mtype left_domain then
              let
                val first = do_annotation_atom_comp Leq unless
                  left_atom right_atom constraints
                val second = do_mtype_comp Leq unless
                  right_domain left_domain first
              in
                case right_atom of
                    A Gen => second
                  | A _ => do_mtype_comp Leq unless
                      left_domain right_domain second
                  | V x => do_mtype_comp Leq (x :: unless)
                      left_domain right_domain second
              end
            else
              SOME constraints
        in
          do_mtype_comp Leq unless left_range right_range domains
        end
    | do_mtype_comp comparison unless
        (MPair (left1, left2)) (MPair (right1, right2)) constraints =
        do_mtype_comp comparison unless left2 right2
          (do_mtype_comp comparison unless left1 right1 constraints)
    | do_mtype_comp _ _ (MType _) (MType _) constraints = constraints
    | do_mtype_comp comparison _ left right _ =
        raise MTYPE
          ("Refute_ModelFinder_Mono.do_mtype_comp",
           [left, right], [])

  fun add_mtype_comp comparison left right constraints =
    case do_mtype_comp comparison [] left right (SOME constraints) of
        SOME result => result
      | NONE => raise UNSOLVABLE ()

  val add_mtypes_equal = add_mtype_comp Eq
  val add_is_sub_mtype = add_mtype_comp Leq

  fun do_notin_mtype_fv _ _ _ NONE = NONE
    | do_notin_mtype_fv Minus _ MAlpha constraints = constraints
    | do_notin_mtype_fv Plus [] MAlpha _ = NONE
    | do_notin_mtype_fv Plus [literal] MAlpha (SOME clauses) =
        add_assign_literal literal clauses
    | do_notin_mtype_fv Plus unless MAlpha (SOME clauses) =
        SOME (insert (op =) unless clauses)
    | do_notin_mtype_fv sign unless
        (MFun (domain, A annotation, range)) constraints =
        let
          val domain_constraints =
            case sign of
                Plus =>
                  let
                    val first =
                      if annotation <> Gen then
                        do_notin_mtype_fv Plus unless domain constraints
                      else
                        constraints
                  in
                    do_notin_mtype_fv Minus unless domain first
                  end
              | Minus =>
                  (* The A-atom Minus case in upstream under-constrains G
                     and N.  Paper Def. 6.3 and the V case require Plus
                     domain constraints here; see [m4-mono §11.3]. *)
                  if annotation = Gen orelse annotation = New then
                    do_notin_mtype_fv Plus unless domain constraints
                  else
                    constraints
        in
          do_notin_mtype_fv sign unless range domain_constraints
        end
    | do_notin_mtype_fv Plus unless
        (MFun (domain, V x, range)) constraints =
        let
          val with_gen =
            add_assign_disjunct (x, (Plus, Gen)) (SOME unless)
          val first =
            case with_gen of
                NONE => constraints
              | SOME unless' =>
                  do_notin_mtype_fv Plus unless' domain constraints
          val second = do_notin_mtype_fv Minus unless domain first
        in
          do_notin_mtype_fv Plus unless range second
        end
    | do_notin_mtype_fv Minus unless
        (MFun (domain, V x, range)) constraints =
        let
          val extended = List.foldl
            (fn (annotation, result) =>
              add_assign_disjunct (x, (Plus, annotation)) result)
            (SOME unless) [Fls, Tru]
          val first =
            case extended of
                NONE => constraints
              | SOME unless' =>
                  do_notin_mtype_fv Plus unless' domain constraints
        in
          do_notin_mtype_fv Minus unless range first
        end
    | do_notin_mtype_fv sign unless
        (MPair (left, right)) constraints =
        do_notin_mtype_fv sign unless right
          (do_notin_mtype_fv sign unless left constraints)
    | do_notin_mtype_fv sign unless
        (MType (_, arguments)) constraints =
        List.foldl (fn (mtype, result) =>
          do_notin_mtype_fv sign unless mtype result)
          constraints arguments
    | do_notin_mtype_fv _ _ mtype _ =
        raise MTYPE
          ("Refute_ModelFinder_Mono.do_notin_mtype_fv", [mtype], [])

  fun add_notin_mtype_fv sign unless mtype (comps, clauses) =
    case do_notin_mtype_fv sign unless mtype (SOME clauses) of
        SOME clauses' => (comps, clauses')
      | NONE => raise UNSOLVABLE ()

  val add_mtype_is_concrete = add_notin_mtype_fv Minus
  val add_mtype_is_complete = add_notin_mtype_fv Plus

  val bool_table =
    [(Gen, (false, false)),
     (New, (false, true)),
     (Fls, (true, false)),
     (Tru, (true, true))]

  fun fst_var variable = 2 * variable
  fun snd_var variable = 2 * variable + 1

  fun bools_from_annotation annotation =
    case lookup (op =) annotation bool_table of
        SOME result => result
      | NONE => raise Fail "Refute_ModelFinder_Mono: bad annotation"

  fun annotation_from_bools bits =
    case List.find (fn (_, other) => other = bits) bool_table of
        SOME (annotation, _) => annotation
      | NONE => raise Fail "Refute_ModelFinder_Mono: bad bit pair"

  fun prop_for_bool true = PS.True
    | prop_for_bool false = PS.False

  fun prop_for_bool_var_equality (left, right) =
    PS.SAnd
      (PS.SOr (PS.BoolVar left, PS.SNot (PS.BoolVar right)),
       PS.SOr (PS.SNot (PS.BoolVar left), PS.BoolVar right))

  fun prop_for_assign (variable, annotation) =
    let
      val (first, second) = bools_from_annotation annotation
      fun bit true formula = formula
        | bit false formula = PS.SNot formula
    in
      if variable <= 0 then
        raise Fail "Refute_ModelFinder_Mono: nonpositive variable"
      else
        PS.SAnd
          (bit first (PS.BoolVar (fst_var variable)),
           bit second (PS.BoolVar (snd_var variable)))
    end

  fun prop_for_assign_literal (variable, (Plus, annotation)) =
        prop_for_assign (variable, annotation)
    | prop_for_assign_literal (variable, (Minus, annotation)) =
        PS.SNot (prop_for_assign (variable, annotation))

  fun prop_for_atom_assign (A actual, expected) =
        prop_for_bool (actual = expected)
    | prop_for_atom_assign (V variable, expected) =
        prop_for_assign (variable, expected)

  fun prop_for_atom_equality (left, A annotation) =
        prop_for_atom_assign (left, annotation)
    | prop_for_atom_equality (A annotation, right) =
        prop_for_atom_assign (right, annotation)
    | prop_for_atom_equality (V left, V right) =
        PS.SAnd
          (prop_for_bool_var_equality
             (fst_var left, fst_var right),
           prop_for_bool_var_equality
             (snd_var left, snd_var right))

  fun prop_for_assign_clause clause =
    PS.exists (map prop_for_assign_literal clause)

  fun prop_for_exists_var_assign_literal variables annotation =
    PS.exists (map (fn variable =>
      prop_for_assign (variable, annotation)) variables)

  fun prop_for_comp (left, right, Eq, []) =
        PS.SAnd
          (prop_for_comp (left, right, Leq, []),
           prop_for_comp (right, left, Leq, []))
    | prop_for_comp (left, right, Neq, []) =
        PS.SNot (prop_for_comp (left, right, Eq, []))
    | prop_for_comp (left, right, Leq, []) =
        PS.SOr
          (prop_for_atom_equality (left, right),
           prop_for_atom_assign (right, Gen))
    | prop_for_comp (left, right, comparison, variables) =
        PS.SOr
          (prop_for_exists_var_assign_literal variables Gen,
           prop_for_comp (left, right, comparison, []))

  fun encode (comps, clauses) =
    PS.all (map prop_for_comp comps @ map prop_for_assign_clause clauses)

  fun association_defined key pairs =
    List.exists (fn (other, _) => key = other) pairs

  fun extract_assigns max_var assigns forced =
    let
      fun add variable result =
        if association_defined variable forced then result
        else
          case (assigns (fst_var variable),
                assigns (snd_var variable)) of
              (NONE, NONE) => result
            | (first, second) =>
                (variable,
                 annotation_from_bools
                   (Option.getOpt (first, false),
                    Option.getOpt (second, false))) :: result
      fun loop variable result =
        if variable > max_var then result
        else loop (variable + 1) (add variable result)
    in
      loop 1 forced
    end

  fun solve tac_timeout max_var (constraints as (_, clauses)) =
    let
      val forced = List.mapPartial
        (fn [(variable, (Plus, annotation))] =>
              SOME (variable, annotation)
          | _ => NONE) clauses
      val prop = encode constraints
      fun finish assignments =
        SOME (extract_assigns max_var assignments forced)
    in
      if PS.eval (fn _ => false) prop then
        finish (fn _ => SOME false)
      else if PS.eval (fn _ => true) prop then
        finish (fn _ => SOME true)
      else
        (* Deviation from upstream: with cdclite as the sole in-process
           solver, the 0.02 s probe followed by the same solver is skipped.
           We make one call under the remaining tac_timeout budget. *)
        (case Timeout.apply tac_timeout PS.solve prop of
             PS.SATISFIABLE assignments => finish assignments
           | PS.UNSATISFIABLE => NONE)
        handle Timeout.TIMEOUT _ => NONE
    end

  fun mtype_has_rec MAlpha = false
    | mtype_has_rec (MFun (left, _, right)) =
        mtype_has_rec left orelse mtype_has_rec right
    | mtype_has_rec (MPair (left, right)) =
        mtype_has_rec left orelse mtype_has_rec right
    | mtype_has_rec (MType (_, arguments)) =
        List.exists mtype_has_rec arguments
    | mtype_has_rec (MRec _) = true

  structure Test = struct
    datatype sign = datatype sign
    datatype annotation = datatype annotation
    datatype annotation_atom = datatype annotation_atom
    datatype mtyp = datatype mtyp
    datatype comp_op = datatype comp_op

    type assign_literal = assign_literal
    type comp = comp
    type assign_clause = assign_clause
    type constraint_set = constraint_set
    type mdata = mdata

    exception UNSOLVABLE = UNSOLVABLE

    val empty_constraints = empty_constraints
    val initial_mdata = initial_mdata
    fun mtype_of_type data ty = fresh_mtype_for_type data false ty
    val mtype_of_type_all_minus = fresh_mtype_for_type
    val mtype_for_constr = mtype_for_constr
    fun max_fresh ({max_fresh, ...} : mdata) = !max_fresh
    fun caches_repaired
          ({data_type_mcache, constr_mcache, ...} : mdata) =
      List.all (not o mtype_has_rec o #2) (!data_type_mcache) andalso
      List.all (not o mtype_has_rec o #2) (!constr_mcache)

    val add_annotation_atom_comp = add_annotation_atom_comp
    fun add_assign_clause clause (comps, clauses) =
      (comps, add_assign_clause_opt (SOME clause) clauses)
    val add_mtypes_equal = add_mtypes_equal
    val add_is_sub_mtype = add_is_sub_mtype
    val add_mtype_is_concrete = add_mtype_is_concrete
    val add_mtype_is_complete = add_mtype_is_complete

    val prop_for_assign = prop_for_assign
    val prop_for_comp = prop_for_comp
    val encode = encode
    val solve = solve
  end
end
