structure hhMonomorph :> hhMonomorph =
struct

  open HolKernel

  type term = Term.term
  type hol_type = Type.hol_type
  type subst = (hol_type, hol_type) Lib.subst

  val max_thm_instances = 10
  val max_schematic_occurrences = 20
  val max_substitution_nodes = 20000
  val privileged_facts = 10

  datatype fact_info =
      Ground of string * term
    | Ignored
    | Schematic of {
        nickname : string,
        theorem : term,
        tvars : hol_type list,
        schematics : (string * hol_type) list,
        initial_round : int,
        instances : (int * subst * term) list ref
      }

  val sort = Listsort.sort

  fun insert_type ty [] = [ty]
    | insert_type ty (old :: rest) =
        case Type.compare (ty, old) of
            LESS => ty :: old :: rest
          | EQUAL => old :: rest
          | GREATER => old :: insert_type ty rest

  fun lookup name table =
    case List.find (fn (other, _) => other = name) table of
        SOME (_, value) => value
      | NONE => []

  fun has_name name table = List.exists (fn (other, _) => other = name) table

  fun update name value table =
    map (fn (other, old) => if other = name then (other, value)
                            else (other, old)) table

  fun schematic_consts tm =
    let
      fun walk current result =
        if length result > max_schematic_occurrences then result
        else if is_const current then
          let val constant as (_, ty) = dest_const current in
            if Type.polymorphic ty then constant :: result else result
          end
        else if is_comb current then
          walk (rand current) (walk (rator current) result)
        else if is_abs current then
          walk (body current) (walk (bvar current) result)
        else result
    in
      walk tm []
    end

  fun tvar_is_bound tvars ty = mem ty tvars

  fun groundable tvars schematics =
    let
      val schematic_tvars =
        List.foldl (fn ((_, ty), result) =>
          List.foldl (fn (tvar, vars) =>
            if tvar_is_bound vars tvar then vars else tvar :: vars)
            result (Type.type_vars ty)) [] schematics
    in
      List.all (tvar_is_bound schematic_tvars) tvars
    end

  (* The goal's type variables are rigid: they name fixed, unknown types,
     and the printer gives each its own opaque sort.  A premise's type
     variables are schematic.  Renaming those that clash apart lets a
     premise match a goal occurrence such as count_occ : 'a -> ... at the
     goal's own 'a; Type.match_type drops identity bindings, so an
     unrenamed premise could never be instantiated there. *)
  fun rename_apart rigid theorem =
    let
      val clashing = List.filter (fn ty => mem ty rigid)
        (Term.type_vars_in_term theorem)
    in
      if null clashing then theorem
      else Term.inst (map (fn ty =>
        {redex = ty, residue = Type.gen_tyvar ()}) clashing) theorem
    end

  fun classify rigid rank (nickname, original) =
    let
      val theorem = rename_apart rigid original
      val tvars = Term.type_vars_in_term theorem
      val schematics = schematic_consts theorem
      val prioritized = Listsort.sort (fn ((left_name, left_ty),
          (right_name, right_ty)) =>
        case Int.compare (length (Type.type_vars right_ty),
                          length (Type.type_vars left_ty)) of
            EQUAL =>
              (case String.compare (left_name, right_name) of
                   EQUAL => Type.compare (left_ty, right_ty)
                 | order => order)
          | order => order) schematics
    in
      if null tvars then Ground (nickname, theorem)
      else if not (groundable tvars schematics) then Ignored
      else Schematic {
        nickname = nickname,
        theorem = theorem,
        tvars = tvars,
        schematics = prioritized,
        initial_round = if rank < privileged_facts then 1 else 2,
        instances = ref []
      }
    end

  fun schema_names infos =
    let
      fun add (Schematic {schematics, ...}, names) =
            List.foldl (fn ((name, _), result) =>
              if has_name name result then result else (name, []) :: result)
              names schematics
        | add (_, names) = names
    in
      List.rev (List.foldl add [] infos)
    end

  fun add_ground (name, ty) table =
    if has_name name table then
      update name (insert_type ty (lookup name table)) table
    else table

  fun is_ground rigid ty =
    List.all (fn tvar => mem tvar rigid) (Type.type_vars ty)

  fun add_grounds rigid tm table =
    let
      fun walk current result =
        if is_const current then
          let val constant as (_, ty) = dest_const current in
            if not (is_ground rigid ty) then result
            else add_ground constant result
          end
        else if is_comb current then
          walk (rand current) (walk (rator current) result)
        else if is_abs current then walk (body current) result
        else result
    in
      walk tm table
    end

  fun merge_grounds left right =
    map (fn (name, tys) =>
      (name, List.foldl (fn (ty, result) => insert_type ty result)
        tys (lookup name right))) left

  fun type_size ty = Type.type_size ty

  fun subst_pairs subst =
    sort (fn ({redex = left, ...}, {redex = right, ...}) =>
      Type.compare (left, right)) subst

  fun subst_compare (left, right) =
    let
      fun size subst =
        List.foldl (fn ({residue, ...}, total) => type_size residue + total)
          0 subst
      fun compare_pairs ([], []) = EQUAL
        | compare_pairs ([], _) = LESS
        | compare_pairs (_, []) = GREATER
        | compare_pairs ((lvar, lty) :: ls, (rvar, rty) :: rs) =
            (case Type.compare (lvar, rvar) of
                 EQUAL =>
                   (case Type.compare (lty, rty) of
                        EQUAL => compare_pairs (ls, rs)
                      | result => result)
               | result => result)
      val size_order = Int.compare (size left, size right)
    in
      if size_order = EQUAL then
        compare_pairs (map (fn {redex, residue} => (redex, residue))
          (subst_pairs left),
          map (fn {redex, residue} => (redex, residue)) (subst_pairs right))
      else size_order
    end

  fun complete tvars subst =
    List.all (fn tvar =>
      List.exists (fn {redex, ...} => redex = tvar) subst) tvars

  fun match ty ground subst =
    SOME (Type.match_type_in_context ty ground subst)
      handle HOL_ERR _ => NONE

  fun matching_grounds name ty subst known new =
    let
      fun try_one is_new ground =
        case match ty ground subst of
            SOME refined => [(is_new, refined)]
          | NONE => []
    in
      List.concat (map (try_one true) (lookup name new)) @
      List.concat (map (try_one false) (lookup name known))
    end

  fun substitutions tvars schematics known new require_new limit =
    let
      val visited = ref 0
      fun same_subst left right = subst_compare (left, right) = EQUAL
      fun add_best subst result =
        if List.exists (fn old => same_subst subst old) result then result
        else aiLib.first_n limit
          (Listsort.sort subst_compare (subst :: result))
      (* The exhaustive branch still visits the same bounded search tree,
         but only its canonical best [limit] substitutions can reach the
         caller.  Keeping that prefix incrementally avoids constructing and
         sorting a large discarded tail before theorem instantiation. *)
      val best = ref []
      fun matches_new subst (name, ty) =
        List.exists (fn ground =>
          case match ty ground subst of SOME _ => true | NONE => false)
          (lookup name new)
      fun search remaining subst used_new =
        if !visited >= max_substitution_nodes then ()
        else if complete tvars subst then
          if not require_new orelse used_new orelse
             List.exists (matches_new subst) remaining
          then best := add_best subst (!best)
          else ()
        else
          (visited := !visited + 1;
          case remaining of
              [] => ()
            | (name, ty) :: rest =>
            let
              val matched = matching_grounds name ty subst known new
            in
              List.app (fn (is_new, subst') =>
                search rest subst' (used_new orelse is_new)) matched;
              search rest subst used_new
            end)
      fun covers_all ty =
        let val vars = Type.type_vars ty in
          List.all (fn tvar => mem tvar vars) tvars
        end
      fun direct all_schematics (name, ty) initial =
        let
          fun consider is_new ground result =
            case match ty ground [] of
                SOME subst =>
                  if complete tvars subst andalso
                     (not require_new orelse is_new orelse
                      List.exists (matches_new subst) all_schematics)
                  then add_best subst result
                  else result
              | NONE => result
          val from_new = List.foldl (fn (ground, result) =>
            consider true ground result) initial (lookup name new)
        in
          List.foldl (fn (ground, result) => consider false ground result)
            from_new (lookup name known)
        end
    in
      case List.filter (covers_all o #2) schematics of
          [] => (search schematics [] false; !best)
        | covering => List.foldl (fn (schematic, result) =>
            direct schematics schematic result) [] covering
    end

  fun unique_terms candidates old =
    let
      fun seen tm = List.exists (fn (_, _, prior) => aconv tm prior) old
      fun loop [] result = List.rev result
        | loop ((item as (_, _, tm)) :: rest) result =
            if seen tm orelse
               List.exists (fn (_, _, prior) => aconv tm prior) result then
              loop rest result
            else loop rest (item :: result)
    in
      loop candidates []
    end

  fun grounds_from_instances rigid instances table =
    List.foldl (fn ((_, _, theorem), result) =>
      add_grounds rigid theorem result) table instances

  fun process_fact rigid round known new remaining fact next_new =
    case fact of
        Schematic {theorem, tvars, schematics, initial_round,
                   instances, ...} =>
          if round < initial_round orelse !remaining <= 0 orelse
             length schematics > max_schematic_occurrences then next_new
          else
            let
              val (old, fresh, require_new) =
                if round = initial_round then
                  ([], merge_grounds known new, false)
                else (known, new, true)
              val room = Int.min (max_thm_instances - length (!instances),
                !remaining)
              (* Substitutions are already in canonical preference order.
                 Different complete substitutions produce differently typed
                 theorem instances, and at most one per old instance can be
                 filtered below.  Instantiate only the bounded prefix that
                 can therefore contribute to this fact. *)
              val substs = if room <= 0 then [] else
                substitutions tvars schematics old fresh require_new
                  (room + length (!instances))
              val candidates = map (fn subst =>
                (round, subst, Term.inst subst theorem))
                substs
              val candidates = unique_terms candidates (!instances)
              val selected = aiLib.first_n room candidates
              val _ = instances := !instances @ selected
              val _ = remaining := !remaining - length selected
            in
              grounds_from_instances rigid selected next_new
            end
      | _ => next_new

  fun result_of (Ground (nickname, theorem)) = [(nickname, theorem)]
    | result_of Ignored = []
    | result_of (Schematic {nickname, instances, ...}) =
        map (fn (_, _, theorem) => (nickname, theorem)) (!instances)

  fun monomorph {max_iters, max_new_instances} goal premises =
    let
      val rigid = Term.type_vars_in_term goal
      val infos = Portable.mapi (classify rigid) premises
      val names = schema_names infos
      val initial = add_grounds rigid goal
        (List.foldl (fn (Ground (_, theorem), result) =>
                       add_grounds rigid theorem result
                      | (_, result) => result) names infos)
      val remaining = ref (Int.max (0, max_new_instances))

      fun rounds round known new =
        if round > Int.max (0, max_iters) orelse !remaining <= 0 then ()
        else
          let
            val next = List.foldl
              (fn (fact, result) =>
                process_fact rigid round known new remaining fact result)
                names infos
          in
            rounds (round + 1) (merge_grounds known new) next
          end

      val _ = rounds 1 names initial
    in
      List.concat (map result_of infos)
    end

end
