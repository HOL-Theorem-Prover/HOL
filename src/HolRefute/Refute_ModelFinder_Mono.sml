(*
 * Monotonicity inference for the model-finder backend.
 *
 * This is the HOL4 port of Isabelle Nitpick's complete M3 monotonicity
 * calculus: mtypes, constraints, frames, term/formula traversal, and SAT
 * solving.
 *)

structure Refute_ModelFinder_Mono :> REFUTE_MODEL_FINDER_MONO = struct
  open Feedback

  structure MFH = Refute_ModelFinder_HOL
  structure MFN = Refute_ModelFinder_Names
  structure MFU = Refute_ModelFinder_Util
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
          {context, binarize, alpha_ty, data_type_mcache,
           constr_mcache, ...} : mdata)
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
                  val constructors =
                    MFH.binarized_and_boxed_data_type_constrs
                      context binarize current
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

  fun negate_sign Plus = Minus
    | negate_sign Minus = Plus

  fun dest_MFun (MFun triple) = triple
    | dest_MFun mtype =
        raise MTYPE ("Refute_ModelFinder_Mono.dest_MFun", [mtype], [])

  fun string_for_annotation Gen = "G"
    | string_for_annotation New = "N"
    | string_for_annotation Fls = "F"
    | string_for_annotation Tru = "T"

  fun string_for_atom (A annotation) = string_for_annotation annotation
    | string_for_atom (V variable) = Int.toString variable

  fun string_for_mtype mtype =
    let
      fun parenthesize true string = "(" ^ string ^ ")"
        | parenthesize false string = string
      fun render precedence candidate =
        case candidate of
            MAlpha => "alpha"
          | MFun (domain, atom, range) =>
              parenthesize (precedence > 1)
                (render 2 domain ^ " =>^" ^ string_for_atom atom ^ " " ^
                 render 1 range)
          | MPair (left, right) =>
              parenthesize (precedence > 2)
                (render 3 left ^ " * " ^ render 2 right)
          | MType (name, []) =>
              if name = "min$bool" then "o" else name
          | MType (name, arguments) =>
              "(" ^ String.concatWith ", " (map (render 0) arguments) ^
              ") " ^ name
          | MRec ty => "[" ^ Parse.type_to_string ty ^ "]"
    in
      render 0 mtype
    end

  val ground_and_sole_base_constrs : string list = []

  fun prodM_factors (MPair (left, right)) =
        prodM_factors left @ prodM_factors right
    | prodM_factors mtype = [mtype]

  fun curried_strip_mtype (MFun (domain, _, range)) =
        let val (domains, result) = curried_strip_mtype range
        in (prodM_factors domain @ domains, result) end
    | curried_strip_mtype mtype = ([], mtype)

  fun sel_mtype_from_constr_mtype name mtype =
    let
      val (arguments, data_mtype) = curried_strip_mtype mtype
      val annotation =
        if List.exists (fn item => item = MFN.original_name name)
             ground_and_sole_base_constrs then Fls
        else Gen
      val range =
        case MFN.sel_no_from_name name of
            ~1 => bool_M
          | index =>
              (List.nth (arguments, index)
               handle Subscript =>
                 raise MTYPE
                   ("Refute_ModelFinder_Mono.selector", [mtype], []))
    in
      MFun (data_mtype, A annotation, range)
    end

  fun mtype_for_sel
        (mdata as {context, binarize, ...} : mdata) selector =
    let
      val (name, selector_ty) = Term.dest_var selector
      val (domain, _) = Type.dom_rng selector_ty
      val constructor =
        MFH.binarized_and_boxed_constr_for_sel context binarize selector
        handle HOL_ERR _ => raise MTYPE
          ("Refute_ModelFinder_Mono.mtype_for_sel", [], [domain])
    in
      sel_mtype_from_constr_mtype name
        (mtype_for_constr mdata constructor)
    end

  fun resolve_atom assignments (V variable) =
        (case List.find (fn (other, _) => other = variable) assignments of
             SOME (_, annotation) => A annotation
           | NONE => V variable)
    | resolve_atom _ atom = atom

  fun resolve_mtype assignments candidate =
    case candidate of
        MAlpha => MAlpha
      | MFun (domain, atom, range) =>
          MFun (resolve_mtype assignments domain,
            resolve_atom assignments atom,
            resolve_mtype assignments range)
      | MPair (left, right) =>
          MPair (resolve_mtype assignments left,
            resolve_mtype assignments right)
      | MType (name, arguments) =>
          MType (name, map (resolve_mtype assignments) arguments)
      | MRec ty => MRec ty

  type mcontext =
    {bounds : (int * Term.term * mtyp) list,
     frame : (int * Term.term * annotation_atom) list,
     frees : (Term.term * mtyp) list,
     consts : (Term.term * mtyp) list,
     next_bound : int}

  val initial_gamma : mcontext =
    {bounds = [], frame = [], frees = [], consts = [], next_bound = 0}

  fun push_bound atom variable mtype
        ({bounds, frame, frees, consts, next_bound} : mcontext) =
    {bounds = (next_bound, variable, mtype) :: bounds,
     frame = frame @ [(next_bound, variable, atom)],
     frees = frees, consts = consts, next_bound = next_bound + 1}

  fun pop_bound
        ({bounds, frame, frees, consts, next_bound} : mcontext) =
    case bounds of
        [] => initial_gamma
      | (identifier, _, _) :: rest =>
          {bounds = rest,
           frame = List.filter (fn (other, _, _) =>
             identifier <> other) frame,
           frees = frees, consts = consts, next_bound = next_bound}

  fun set_frame new_frame
        ({bounds, frees, consts, next_bound, ...} : mcontext) =
    {bounds = bounds, frame = new_frame, frees = frees, consts = consts,
     next_bound = next_bound}

  fun add_comp_frame atom comparison frame constraints =
    List.foldl (fn ((_, _, other), result) =>
      add_annotation_atom_comp comparison [] atom other result)
      constraints frame

  fun add_bound_frame identifier frame constraints =
    let
      val (own, other) = List.partition (fn (candidate, _, _) =>
        identifier = candidate) frame
    in
      add_comp_frame (A Gen) Eq other
        (add_comp_frame (A New) Leq own constraints)
    end

  fun fresh_frame ({max_fresh, ...} : mdata) fls tru frame =
    map (fn (identifier, variable, atom) =>
      (identifier, variable,
       case (atom, fls, tru) of
           (A Fls, SOME annotation, _) => A annotation
         | (A Tru, _, SOME annotation) => A annotation
         | (A Gen, _, _) => A Gen
         | _ => V (fresh max_fresh))) frame

  type quasi_literal = annotation_atom * (comp_op * annotation)
  type quasi_clause = quasi_literal list

  fun conj_clauses result left right : quasi_clause list =
    [[(left, (Neq, Tru)), (right, (Neq, Tru)), (result, (Eq, Tru))],
     [(left, (Neq, Fls)), (result, (Eq, Fls))],
     [(right, (Neq, Fls)), (result, (Eq, Fls))],
     [(left, (Neq, Gen)), (right, (Eq, Fls)), (result, (Eq, Gen))],
     [(left, (Neq, New)), (right, (Eq, Fls)), (result, (Eq, Gen))],
     [(left, (Eq, Fls)), (right, (Neq, Gen)), (result, (Eq, Gen))],
     [(left, (Eq, Fls)), (right, (Neq, New)), (result, (Eq, Gen))]]

  fun disj_clauses result left right : quasi_clause list =
    [[(left, (Neq, Tru)), (result, (Eq, Tru))],
     [(right, (Neq, Tru)), (result, (Eq, Tru))],
     [(left, (Neq, Fls)), (right, (Neq, Fls)), (result, (Eq, Fls))],
     [(left, (Neq, Gen)), (right, (Eq, Tru)), (result, (Eq, Gen))],
     [(left, (Neq, New)), (right, (Eq, Tru)), (result, (Eq, Gen))],
     [(left, (Eq, Tru)), (right, (Neq, Gen)), (result, (Eq, Gen))],
     [(left, (Eq, Tru)), (right, (Neq, New)), (result, (Eq, Gen))]]

  fun imp_clauses result left right : quasi_clause list =
    [[(left, (Neq, Fls)), (result, (Eq, Tru))],
     [(right, (Neq, Tru)), (result, (Eq, Tru))],
     [(left, (Neq, Tru)), (right, (Neq, Fls)), (result, (Eq, Fls))],
     [(left, (Neq, Gen)), (right, (Eq, Tru)), (result, (Eq, Gen))],
     [(left, (Neq, New)), (right, (Eq, Tru)), (result, (Eq, Gen))],
     [(left, (Eq, Fls)), (right, (Neq, Gen)), (result, (Eq, Gen))],
     [(left, (Eq, Fls)), (right, (Neq, New)), (result, (Eq, Gen))]]

  val conj_spec = ("and", conj_clauses)
  val disj_spec = ("or", disj_clauses)
  val imp_spec = ("implies", imp_clauses)

  fun assign_clause_from_quasi_clause literals =
    let
      fun add [] result = result
        | add _ NONE = NONE
        | add ((atom, (comparison, annotation)) :: rest) result =
            (case atom of
                 A actual =>
                   if annotation_comp comparison actual annotation then NONE
                   else add rest result
               | V variable =>
                   add rest
                     (Option.map (fn clause =>
                       insert (op =)
                         (variable,
                          (sign_for_comp_op comparison, annotation)) clause)
                       result))
    in
      add literals (SOME [])
    end

  fun add_connective_var _ make_clauses result left right constraints =
    List.foldl (fn (clause, (comps, clauses)) =>
      (comps,
       add_assign_clause_opt (assign_clause_from_quasi_clause clause)
         clauses)) constraints (make_clauses result left right)

  fun add_connective_frames name make_clauses result_frame left_frame
        right_frame constraints =
    let
      val triples = ListPair.zipEq
        (result_frame, ListPair.zipEq (left_frame, right_frame))
        handle ListPair.UnequalLengths =>
          raise MTYPE
            ("Refute_ModelFinder_Mono.connective_frames", [], [])
    in
      List.foldl
        (fn (((_, _, result), ((_, _, left), (_, _, right))), current) =>
          add_connective_var name make_clauses result left right current)
        constraints triples
    end

  fun kill_unused_in_frame predicate
        (gamma as {frame, ...} : mcontext, constraints) =
    let val (used, unused) = List.partition predicate frame
    in
      (set_frame used gamma,
       add_comp_frame (A Gen) Eq unused constraints)
    end

  fun split_frame is_in_function
        (gamma as {frame, ...} : mcontext, constraints) =
    let
      fun bubble function_frame argument_frame [] current =
            ((rev function_frame, rev argument_frame), (gamma, current))
        | bubble function_frame argument_frame
            ((entry as (_, _, atom)) :: rest) current =
            if is_in_function entry then
              bubble (entry :: function_frame) argument_frame rest
                (add_comp_frame atom Leq argument_frame current)
            else
              bubble function_frame (entry :: argument_frame) rest current
    in
      bubble [] [] frame constraints
    end

  fun add_annotation_atom_comp_alt _ (A Gen) _ _ constraints = constraints
    | add_annotation_atom_comp_alt _ (A _) _ _ _ = raise UNSOLVABLE ()
    | add_annotation_atom_comp_alt comparison (V variable) left right
        constraints =
        add_annotation_atom_comp comparison [variable] left right constraints

  fun add_arg_order1 ((_, _, atom), (_, _, previous)) constraints =
    add_annotation_atom_comp_alt Neq previous (A Gen) atom constraints

  fun add_app1 function_atom
        ((_, _, result_atom), (_, _, argument_atom))
        (comps, clauses) =
    let
      val clause = assign_clause_from_quasi_clause
        [(argument_atom, (Eq, New)), (result_atom, (Eq, Gen))]
      val constraints =
        (comps, add_assign_clause_opt clause clauses)
    in
      add_annotation_atom_comp_alt Leq argument_atom function_atom
        result_atom constraints
    end

  fun add_app _ [] [] constraints = constraints
    | add_app function_atom result_frame argument_frame constraints =
        let
          val _ = if length result_frame = length argument_frame then ()
                  else raise MTYPE
                    ("Refute_ModelFinder_Mono.add_app", [], [])
          val adjacent =
            if null argument_frame then []
            else ListPair.zipEq
              (tl argument_frame,
               List.take (argument_frame, length argument_frame - 1))
          val constraints =
            add_comp_frame (A New) Leq argument_frame constraints
          val constraints = List.foldl
            (fn (pair, current) => add_arg_order1 pair current)
            constraints adjacent
        in
          List.foldl (fn (pair, current) =>
            add_app1 function_atom pair current) constraints
            (ListPair.zipEq (result_frame, argument_frame))
        end

  fun consider_connective mdata (_, make_clauses) do_left do_right
        (gamma as {frame, ...} : mcontext, constraints) =
    let
      val left_frame = fresh_frame mdata (SOME Tru) NONE frame
      val right_frame = fresh_frame mdata (SOME Fls) NONE frame
      val (left_gamma, constraints) =
        do_left (set_frame left_frame gamma, constraints)
      val (right_gamma, constraints) =
        do_right (set_frame right_frame left_gamma, constraints)
      val gamma = set_frame frame right_gamma
    in
      (gamma, add_connective_frames "" make_clauses frame left_frame
        right_frame constraints)
    end

  fun option_none term =
    Term.is_const term andalso
    MFH.is_named_const {Thy = "option", Name = "NONE"} term

  fun fin_fun_body variable domain_ty range_ty body =
    if Term.aconv body boolSyntax.F orelse option_none body then
      SOME body
    else if boolSyntax.is_cond body then
      let
        val (condition, value, rest) = boolSyntax.dest_cond body
        val equality = Lib.total boolSyntax.dest_eq condition
        fun key_of (left, right) =
          if Term.aconv left variable andalso
             not (Term.free_in variable right) then SOME right
          else if Term.aconv right variable andalso
                  not (Term.free_in variable left) then SOME left
          else NONE
      in
        case Option.mapPartial key_of equality of
            NONE => NONE
          | SOME key =>
              (case fin_fun_body variable domain_ty range_ty rest of
                   NONE => NONE
                 | SOME rewritten_rest =>
                     let
                       val is_unknown = Term.mk_thy_const
                         {Thy = "refute", Name = "is_unknown",
                          Ty = Type.-->(domain_ty, Type.bool)}
                       val unknown = Term.mk_thy_const
                         {Thy = "refute", Name = "unknown", Ty = range_ty}
                       val original = boolSyntax.mk_cond
                         (condition, value, rewritten_rest)
                     in
                       SOME (boolSyntax.mk_cond
                         (Term.mk_comb (is_unknown, key), unknown, original))
                     end)
      end
    else
      NONE

  fun consider_term
        (mdata as {context, alpha_ty, max_fresh, ...} : mdata) =
    let
      val mtype_for = fresh_mtype_for_type mdata false

      fun range_after 0 ty = ty
        | range_after count ty =
            range_after (count - 1) (#2 (Type.dom_rng ty))

      fun do_quantifier annotation ty accum =
        let
          val predicate_ty = #1 (Type.dom_rng ty)
          val element_ty = #1 (Type.dom_rng predicate_ty)
          val element_mtype = mtype_for element_ty
          val result_mtype = mtype_for (#2 (Type.dom_rng predicate_ty))
          val variable = fresh max_fresh
          val result = MFun
            (MFun (element_mtype, V variable, result_mtype), A Gen,
             result_mtype)
          val (gamma, constraints) = accum
        in
          (result,
           (gamma, add_mtype_is_complete
             [(variable, (Plus, annotation))] element_mtype constraints))
        end

      fun do_equals ty (gamma, constraints) =
        let
          val element_ty = #1 (Type.dom_rng ty)
          val mtype = mtype_for element_ty
          val variable = fresh max_fresh
          val constraints = add_mtype_is_concrete [] mtype constraints
          val constraints = add_annotation_atom_comp Leq []
            (A Fls) (V variable) constraints
        in
          (MFun (mtype, A Gen,
             MFun (mtype, V variable, bool_M)), (gamma, constraints))
        end

      fun do_robust_operation branch_ty (gamma, constraints) =
        let
          val left = mtype_for branch_ty
          val right = mtype_for branch_ty
          val result = mtype_for branch_ty
          val constraints = add_is_sub_mtype left result constraints
          val constraints = add_is_sub_mtype right result constraints
        in
          (MFun (bool_M, A Gen,
             MFun (left, A Gen, MFun (right, A Gen, result))),
           (gamma, constraints))
        end

      fun do_fragile_operation ty (gamma, constraints) =
        let
          val shared_ty = #1 (Type.dom_rng ty)
          val shared_mtype = mtype_for shared_ty
          fun custom current =
            if same_type (current, shared_ty) then shared_mtype
            else
              case Lib.total Type.dom_rng current of
                  SOME (domain, range) =>
                    MFun (custom domain, A Gen, custom range)
                | NONE => mtype_for current
        in
          (custom ty,
           (gamma, add_mtype_is_concrete [] shared_mtype constraints))
        end

      fun do_pair_constructor ty accum =
        let
          val result_ty = range_after 2 ty
        in
          case mtype_for result_ty of
              pair_mtype as MPair (left, right) =>
                (MFun (left, A Gen,
                   MFun (right, A Gen, pair_mtype)), accum)
            | other => raise MTYPE
                ("Refute_ModelFinder_Mono.pair", [other], [ty])
        end

      fun do_pair_selector index ty accum =
        let val domain_ty = #1 (Type.dom_rng ty)
        in
          case mtype_for domain_ty of
              pair_mtype as MPair (left, right) =>
                (MFun (pair_mtype, A Gen,
                   if index = 0 then left else right), accum)
            | other => raise MTYPE
                ("Refute_ModelFinder_Mono.pair_selector", [other], [ty])
        end

      fun cache_constant term mtype
            ({bounds, frame, frees, consts, next_bound} : mcontext) =
        {bounds = bounds, frame = frame, frees = frees,
         consts = (term, mtype) :: consts, next_bound = next_bound}

      fun cache_free term mtype
            ({bounds, frame, frees, consts, next_bound} : mcontext) =
        {bounds = bounds, frame = frame,
         frees = (term, mtype) :: frees, consts = consts,
         next_bound = next_bound}

      fun lookup_term term pairs = lookup same_term term pairs

      fun lookup_bound term bounds =
        case List.find (fn (_, variable, _) =>
               Term.aconv term variable) bounds of
            SOME (identifier, _, mtype) => SOME (identifier, mtype)
          | NONE => NONE

      fun variable_name term = #1 (Term.dest_var term)

      fun is_reserved term =
        Term.is_var term andalso
        MFN.is_reserved_name (variable_name term)

      fun const_like term
            (accum as (gamma as {frame, consts, ...} : mcontext,
                       constraints)) =
        let
          val ty = Term.type_of term
          val result =
            case lookup_term term consts of
                SOME mtype => (mtype, accum)
              | NONE =>
                  if not (could_exist_alpha_subtype alpha_ty ty) then
                    (mtype_for ty, accum)
                  else if MFH.is_named_const {Thy = "bool", Name = "!"}
                            term then
                    do_quantifier Tru ty accum
                  else if MFH.is_named_const {Thy = "bool", Name = "?"}
                            term then
                    do_quantifier Fls ty accum
                  else if MFH.is_named_const {Thy = "min", Name = "="}
                            term then
                    do_equals ty accum
                  else if MFH.is_named_const {Thy = "min", Name = "@"}
                            term then
                    raise UNSOLVABLE ()
                  else if MFH.is_named_const
                            {Thy = "bool", Name = "COND"} term then
                    do_robust_operation (range_after 3 ty) accum
                  else if MFH.is_named_const {Thy = "pair", Name = ","}
                            term then
                    do_pair_constructor ty accum
                  else if MFH.is_named_const {Thy = "pair", Name = "FST"}
                            term then
                    do_pair_selector 0 ty accum
                  else if MFH.is_named_const {Thy = "pair", Name = "SND"}
                            term then
                    do_pair_selector 1 ty accum
                  else if MFH.is_named_const
                            {Thy = "pred_set", Name = "FINITE"} term then
                    let
                      val predicate_ty = #1 (Type.dom_rng ty)
                      val element_ty = #1 (Type.dom_rng predicate_ty)
                      val element_mtype = mtype_for element_ty
                      val atom = if exists_alpha_sub_mtype element_mtype
                                 then A Fls else A Gen
                    in
                      (MFun (MFun (element_mtype, atom, bool_M),
                         A Gen, bool_M), accum)
                    end
                  else if MFH.is_named_const
                            {Thy = "pred_set", Name = "SUBSET"} term then
                    do_fragile_operation ty accum
                  else if is_reserved term andalso
                          MFN.is_sel (variable_name term) then
                    (mtype_for_sel mdata term, accum)
                  else if MFH.is_constr term then
                    (mtype_for_constr mdata term, accum)
                  else if MFH.is_named_const
                            {Thy = "refute", Name = "safe_The"} term then
                    let
                      val predicate_mtype = mtype_for (#1 (Type.dom_rng ty))
                      val element_mtype = #1 (dest_MFun predicate_mtype)
                    in
                      (MFun (predicate_mtype, A Gen, element_mtype), accum)
                    end
                  else if MFH.is_built_in_const term then
                    (fresh_mtype_for_type mdata true ty, accum)
                  else
                    let val mtype = mtype_for ty
                    in (mtype, (cache_constant term mtype gamma,
                                constraints)) end
          val (mtype, (gamma, constraints)) = result
        in
          (mtype, (gamma,
            add_comp_frame (A Gen) Eq frame constraints))
        end

      fun is_enough_eta_expanded term =
        let val (head, arguments) = HolKernel.strip_comb term
        in
          if Term.is_const head orelse is_reserved head then
            Option.getOpt (MFH.arity_of_built_in_const head, 0) <=
              length arguments
          else true
        end

      fun do_connect spec left right accum =
        (bool_M, consider_connective mdata spec
          (fn current => #2 (do_term left current))
          (fn current => #2 (do_term right current)) accum)

      and do_term term
            (accum as (gamma as {bounds, frame, frees, ...} : mcontext,
                       constraints)) =
        let
          val _ = trace_msg (fn () => "Mono term: " ^
            Parse.term_to_string term)
          val bound_mtype = lookup_bound term bounds
          val symmetric_equality =
            if boolSyntax.is_eq term then
              let val (left, right) = boolSyntax.dest_eq term
              in
                case (bounds, lookup_bound left bounds) of
                    ((top, _, _) :: _, SOME (identifier, _)) =>
                      if top = identifier then
                        SOME (if Term.aconv left right then boolSyntax.T
                              else boolSyntax.mk_eq (right, left))
                      else NONE
                  | _ => NONE
              end
            else NONE
        in
          if Term.aconv term boolSyntax.F then
            (bool_M, (gamma,
              add_comp_frame (A Fls) Leq frame constraints))
          else if Term.aconv term boolSyntax.T then
            (bool_M, (gamma,
              add_comp_frame (A Tru) Leq frame constraints))
          else if option_none term then
            (mtype_for (Term.type_of term),
             (gamma, add_comp_frame (A Fls) Leq frame constraints))
          else
            case symmetric_equality of
                SOME rewritten => do_term rewritten accum
              | NONE =>
                case bound_mtype of
                    SOME (identifier, mtype) =>
                      (mtype, (gamma,
                        add_bound_frame identifier frame constraints))
                  | NONE =>
                  if boolSyntax.is_neg term then
                    do_connect imp_spec (boolSyntax.dest_neg term)
                      boolSyntax.F accum
                  else if boolSyntax.is_conj term then
                    let val (left, right) = boolSyntax.dest_conj term
                    in do_connect conj_spec left right accum end
                  else if boolSyntax.is_disj term then
                    let val (left, right) = boolSyntax.dest_disj term
                    in do_connect disj_spec left right accum end
                  else if boolSyntax.is_imp_only term then
                    let val (left, right) = boolSyntax.dest_imp term
                    in do_connect imp_spec left right accum end
                  else if boolSyntax.is_let term then
                    let val (function, value) = boolSyntax.dest_let term
                    in do_term (MFH.s_betapply (function, value)) accum end
                  else
                    let
                      val (head, arguments) = HolKernel.strip_comb term
                    in
                      if Term.is_const head andalso
                         MFH.is_named_const {Thy = "bool", Name = "IN"}
                           head andalso length arguments = 2 then
                        do_term (Term.mk_comb
                          (List.nth (arguments, 1), hd arguments)) accum
                      else if Term.is_const term orelse is_reserved term then
                        const_like term accum
                      else if Term.is_var term then
                        (case lookup_term term frees of
                             SOME mtype =>
                               (mtype, (gamma,
                                 add_comp_frame (A Gen) Eq frame constraints))
                           | NONE =>
                               let
                                 val mtype = mtype_for (Term.type_of term)
                                 val gamma = cache_free term mtype gamma
                               in
                                 (mtype, (gamma,
                                   add_comp_frame (A Gen) Eq frame
                                     constraints))
                               end)
                      else if Term.is_abs term then
                        let
                          val (variable, body) = Term.dest_abs term
                          val domain_ty = Term.type_of variable
                          val range_ty = Term.type_of body
                        in
                          case fin_fun_body variable domain_ty range_ty body of
                              SOME rewritten =>
                                let
                                  val domain_mtype = mtype_for domain_ty
                                  val annotation = V (fresh max_fresh)
                                  val pushed = push_bound annotation variable
                                    domain_mtype gamma
                                  val (range_mtype, (gamma, constraints)) =
                                    do_term rewritten (pushed, constraints)
                                  val gamma = pop_bound gamma
                                  val constraints = add_annotation_atom_comp
                                    Leq [] (A Fls) annotation constraints
                                in
                                  (MFun (domain_mtype, annotation,
                                     range_mtype), (gamma, constraints))
                                end
                            | NONE =>
                                if boolSyntax.is_eq body then
                                  let
                                    val (left, right) = boolSyntax.dest_eq body
                                    val (head, _) = HolKernel.strip_comb body
                                  in
                                    if Term.aconv left variable andalso
                                       not (Term.free_in variable right) then
                                      do_term (Term.mk_comb (head, right))
                                        accum
                                    else if
                                      Term.aconv right variable andalso
                                      not (Term.free_in variable left)
                                    then
                                      do_term (Term.mk_comb (head, left)) accum
                                    else
                                      general_abs variable body accum
                                  end
                                else
                                  (case Lib.total Term.dest_comb body of
                                       SOME (function, argument) =>
                                         if
                                           Term.aconv argument variable andalso
                                           not (Term.free_in variable function)
                                           andalso
                                           is_enough_eta_expanded function
                                         then
                                           do_term function accum
                                         else general_abs variable body accum
                                     | NONE => general_abs variable body accum)
                        end
                      else if Term.is_comb term then
                        let
                          fun occurs (_, variable, _) =
                            Term.free_in variable term
                          val (gamma, constraints) =
                            kill_unused_in_frame occurs accum
                          val ((function_frame, argument_frame),
                               (gamma, constraints)) =
                            split_frame (fn (_, variable, _) =>
                              Term.free_in variable (#1
                                (Term.dest_comb term)))
                              (gamma, constraints)
                          val fresh_argument_frame = map
                            (fn (identifier, variable, _) =>
                              (identifier, variable, V (fresh max_fresh)))
                              argument_frame
                          val argument_context_frame =
                            map (fn (identifier, variable, _) =>
                              (identifier, variable, A Gen)) function_frame @
                            fresh_argument_frame
                          val (function, argument) = Term.dest_comb term
                          val (function_mtype, (gamma, constraints)) =
                            do_term function
                              (set_frame function_frame gamma, constraints)
                          val (argument_mtype, (gamma, constraints)) =
                            do_term argument
                              (set_frame argument_context_frame gamma,
                               constraints)
                          val (domain_mtype, atom, range_mtype) =
                            dest_MFun function_mtype
                          val constraints = add_is_sub_mtype argument_mtype
                            domain_mtype constraints
                          val constraints = add_app atom argument_frame
                            fresh_argument_frame constraints
                        in
                          (range_mtype,
                           (set_frame frame gamma, constraints))
                        end
                      else
                        raise UNSOLVABLE ()
                    end
        end

      and general_abs variable body
            (gamma as {frame, ...} : mcontext, constraints) =
        let
          val domain_mtype = mtype_for (Term.type_of variable)
          val annotation = V (fresh max_fresh)
          val (range_mtype, (gamma, constraints)) =
            do_term body
              (push_bound annotation variable domain_mtype gamma,
               constraints)
        in
          (MFun (domain_mtype, annotation, range_mtype),
           (pop_bound gamma, constraints))
        end
    in
      do_term
    end

  fun force_gen_funs 0 _ constraints = constraints
    | force_gen_funs count
        (mtype as MFun (domain, _, range)) constraints =
        force_gen_funs (count - 1) range
          (add_mtypes_equal mtype
            (MFun (domain, A Gen, range)) constraints)
    | force_gen_funs _ mtype _ =
        raise MTYPE
          ("Refute_ModelFinder_Mono.force_gen_funs", [mtype], [])

  fun consider_general_equals mdata definitional left right
        (gamma, constraints) =
    let
      val (left_mtype, (gamma, constraints)) =
        consider_term mdata left (gamma, constraints)
      val (right_mtype, (gamma, constraints)) =
        consider_term mdata right (gamma, constraints)
      val constraints = add_mtypes_equal left_mtype right_mtype constraints
    in
      if definitional then
        let
          val (head, arguments) = HolKernel.strip_comb left
          val (head_mtype, (gamma, constraints)) =
            consider_term mdata head (gamma, constraints)
        in
          (gamma, force_gen_funs (length arguments) head_mtype constraints)
        end
      else
        (gamma, constraints)
    end

  fun consider_general_formula
        (mdata as {max_fresh, ...} : mdata) =
    let
      val mtype_for = fresh_mtype_for_type mdata false

      fun do_quantifier sign existential variable body
            (gamma, constraints) =
        let
          val mtype = mtype_for (Term.type_of variable)
          val annotation = V (fresh max_fresh)
          val side_condition =
            (sign = Minus) = existential
          val constraints =
            if side_condition then
              add_mtype_is_complete
                [(case annotation of V x => x | _ => 0,
                  (Plus, if existential then Fls else Tru))]
                mtype constraints
            else constraints
          val (gamma, constraints) =
            do_formula sign body
              (push_bound annotation variable mtype gamma, constraints)
        in
          (pop_bound gamma, constraints)
        end

      and do_connect sign spec flip_left left right accum =
        consider_connective mdata spec
          (do_formula (if flip_left then negate_sign sign else sign) left)
          (do_formula sign right) accum

      and do_formula sign term accum =
        if boolSyntax.is_forall term then
          let val (variable, body) = boolSyntax.dest_forall term
          in do_quantifier sign false variable body accum end
        else if boolSyntax.is_exists term then
          let
            val (variable, body) = boolSyntax.dest_exists term
          in
            if sign = Plus then
              do_quantifier sign true variable body accum
            else
              let
                val predicate = Term.mk_abs (variable, body)
                val empty = Term.mk_abs (variable, boolSyntax.F)
                val rewritten = boolSyntax.mk_neg
                  (boolSyntax.mk_eq (predicate, empty))
              in
                #2 (consider_term mdata rewritten accum)
              end
          end
        else if boolSyntax.is_eq term then
          let val (left, right) = boolSyntax.dest_eq term
          in
            if sign = Plus then #2 (consider_term mdata term accum)
            else consider_general_equals mdata false left right accum
          end
        else if boolSyntax.is_let term then
          let val (function, value) = boolSyntax.dest_let term
          in do_formula sign (MFH.s_betapply (function, value)) accum end
        else if boolSyntax.is_neg term then
          do_connect sign imp_spec true (boolSyntax.dest_neg term)
            boolSyntax.F accum
        else if boolSyntax.is_conj term then
          let val (left, right) = boolSyntax.dest_conj term
          in do_connect sign conj_spec false left right accum end
        else if boolSyntax.is_disj term then
          let val (left, right) = boolSyntax.dest_disj term
          in do_connect sign disj_spec false left right accum end
        else if boolSyntax.is_imp_only term then
          let val (left, right) = boolSyntax.dest_imp term
          in do_connect sign imp_spec true left right accum end
        else
          #2 (consider_term mdata term accum)
    in
      do_formula
    end

  val harmless_consts =
    ["prim_rec$<", "arithmetic$<=", "integer$int_lt",
     "integer$int_le"]
  val bounteous_consts = ["refute$bisim", "bisim"]

  fun term_name term =
    if Term.is_const term then
      let val {Thy, Name, ...} = Term.dest_thy_const term
      in Thy ^ "$" ^ Name end
    else
      #1 (Term.dest_var term)

  fun is_constant_like term =
    Term.is_const term orelse
    (Term.is_var term andalso
     MFN.is_reserved_name (#1 (Term.dest_var term)))

  fun is_harmless_axiom term =
    let
      val constants = HolKernel.find_terms is_constant_like term
      val nonbuiltins = List.filter
        (not o MFH.is_built_in_const) constants
      fun canonical candidate = MFN.original_name (term_name candidate)
    in
      List.all (fn candidate => List.exists (fn harmless =>
        canonical candidate = harmless) harmless_consts) nonbuiltins orelse
      List.exists (fn candidate => List.exists (fn bounteous =>
        term_name candidate = bounteous orelse
        canonical candidate = bounteous) bounteous_consts) constants
    end

  fun consider_nondefinitional_axiom mdata term accum =
    if is_harmless_axiom term then accum
    else consider_general_formula mdata Plus term accum

  fun is_constructor_pattern bound term =
    if List.exists (Term.aconv term) bound orelse
       (Term.is_var term andalso
        MFN.is_reserved_name (#1 (Term.dest_var term))) then
      true
    else
      let val (head, arguments) = HolKernel.strip_comb term
      in
        MFH.is_nonfree_constr head andalso
        List.all (is_constructor_pattern bound) arguments
      end handle HOL_ERR _ => false

  fun is_constructor_pattern_formula term =
    let
      fun lhs variables candidate =
        if boolSyntax.is_forall candidate then
          let val (variable, body) = boolSyntax.dest_forall candidate
          in lhs (variable :: variables) body end
        else if boolSyntax.is_imp_only candidate then
          lhs variables (#2 (boolSyntax.dest_imp candidate))
        else
          SOME (variables, #1 (boolSyntax.dest_eq candidate))
          handle HOL_ERR _ => NONE
    in
      case lhs [] term of
          SOME (variables, left) =>
            List.all (is_constructor_pattern variables)
              (#2 (HolKernel.strip_comb left))
        | NONE => false
    end

  fun consider_definitional_axiom
        (mdata as {max_fresh, ...} : mdata) term accum =
    if not (is_constructor_pattern_formula term) then
      consider_nondefinitional_axiom mdata term accum
    else if is_harmless_axiom term then accum
    else
      let
        val mtype_for = fresh_mtype_for_type mdata false
        fun do_formula candidate (gamma, constraints) =
          if boolSyntax.is_forall candidate then
            let
              val (variable, body) = boolSyntax.dest_forall candidate
              val gamma = push_bound (A Gen) variable
                (mtype_for (Term.type_of variable)) gamma
              val (gamma, constraints) = do_formula body
                (gamma, constraints)
            in
              (pop_bound gamma, constraints)
            end
          else if boolSyntax.is_imp_only candidate then
            let
              val (premise, conclusion) = boolSyntax.dest_imp candidate
              val (_, (gamma, constraints)) =
                consider_term mdata premise (gamma, constraints)
            in
              do_formula conclusion (gamma, constraints)
            end
          else if boolSyntax.is_conj candidate then
            let val (left, right) = boolSyntax.dest_conj candidate
                val current = do_formula left (gamma, constraints)
            in do_formula right current end
          else if boolSyntax.is_eq candidate then
            let val (left, right) = boolSyntax.dest_eq candidate
            in
              consider_general_equals mdata true left right
                (gamma, constraints)
            end
          else
            raise MFU.BAD
              ("Refute_ModelFinder_Mono.consider_definitional_axiom",
               Parse.term_to_string candidate)
      in
        do_formula term accum
      end

  fun print_mcontext assignments
        ({frees, consts, ...} : mcontext) =
    trace_msg (fn () => String.concatWith "\n"
      (map (fn (term, mtype) => Parse.term_to_string term ^ " : " ^
        string_for_mtype (resolve_mtype assignments mtype))
        (rev frees @ rev consts)))

  fun formulas_monotonic context binarize alpha_ty
        (nondefinitions, definitions) =
    let
      val _ = trace_msg (fn () => "Monotonicity analysis for " ^
        Parse.type_to_string alpha_ty)
      val mdata as {max_fresh, ...} =
        initial_mdata context binarize alpha_ty
      val initial = (initial_gamma, empty_constraints)
      val after_nondefinitions =
        case nondefinitions of
            [] => initial
          | first :: rest =>
              List.foldl (fn (term, current) =>
                consider_nondefinitional_axiom mdata term current)
                (consider_general_formula mdata Plus first initial) rest
      val (gamma, constraints) = List.foldl
        (fn (term, current) =>
          consider_definitional_axiom mdata term current)
        after_nondefinitions definitions
    in
      case solve (#tac_timeout context) (!max_fresh) constraints of
          SOME assignments => (print_mcontext assignments gamma; true)
        | NONE => false
    end
    handle UNSOLVABLE () => false
         | MTYPE (location, mtypes, types) =>
             (* Deviation from upstream: an internal mtype mismatch must not
                abort Refute.  The driver catches BAD, reports at trace
                level, and conservatively classifies the type nonmonotonic. *)
             raise MFU.BAD
               (location,
                String.concatWith ", "
                  (map string_for_mtype mtypes @
                   map Parse.type_to_string types))

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
