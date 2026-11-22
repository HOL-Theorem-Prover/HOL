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
        covering : (string * hol_type) list,
        initial_round : int,
        instances : (int * subst * term) list ref
      }

  val sort = Listsort.sort

  (* Return NONE if the type was already present. *)
  fun insert_type ty [] = SOME [ty]
    | insert_type ty (types as old :: rest) =
        case Type.compare (ty, old) of
            LESS => SOME (ty :: types)
          | EQUAL => NONE
          | GREATER => Option.map (fn tail => old :: tail) (insert_type ty rest)

  fun lookup name table =
    Option.getOpt (Redblackmap.peek (table, name), [])

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
        List.foldl (fn ((_, vars, _), result) =>
          List.foldl (fn (tvar, seen) =>
            if tvar_is_bound seen tvar then seen else tvar :: seen)
            result vars) [] schematics
    in
      List.all (tvar_is_bound schematic_tvars) tvars
    end

  (* The goal's type variables are rigid: they name fixed, unknown types,
     and the printer gives each its own opaque sort.  A premise's type
     variables are schematic.  Renaming those that clash apart lets a
     premise match a goal occurrence such as count_occ : 'a -> ... at the
     goal's own 'a; Type.match_type drops identity bindings, so an
     unrenamed premise could never be instantiated there. *)
  fun rename_apart names rigid theorem tvars =
    let
      val clashing = List.filter (fn ty => mem ty rigid) tvars
    in
      if null clashing then (theorem, tvars)
      else
        let
          val renamed = Term.inst (map (fn ty =>
            {redex = ty, residue = names ()}) clashing) theorem
        in
          (renamed, Term.type_vars_in_term renamed)
        end
    end

  fun classify names rigid rank (nickname, original) =
    case Term.type_vars_in_term original of
        [] => Ground (nickname, original)
      | original_vars =>
          let
            val (theorem, tvars) = rename_apart names rigid original
              original_vars
            fun describe (constant as (_, ty)) =
              let val vars = Type.type_vars ty in
                (constant, vars, length vars)
              end
            val schematics = map describe (schematic_consts theorem)
            fun compare (((left_name, left_ty), _, left_count),
                         ((right_name, right_ty), _, right_count)) =
              case Int.compare (right_count, left_count) of
                  EQUAL =>
                    (case String.compare (left_name, right_name) of
                         EQUAL => Type.compare (left_ty, right_ty)
                       | order => order)
                | order => order
          in
            if not (groundable tvars schematics) then Ignored
            else
              let
                val ordered = sort compare schematics
                fun cover (constant, vars, _) =
                  if List.all (tvar_is_bound vars) tvars then SOME constant
                  else NONE
                val covering =
                  if length ordered > max_schematic_occurrences then []
                  else List.mapPartial cover ordered
              in
                Schematic {
                  nickname = nickname,
                  theorem = theorem,
                  tvars = tvars,
                  schematics = map #1 ordered,
                  covering = covering,
                  initial_round = if rank < privileged_facts then 1 else 2,
                  instances = ref []
                }
              end
          end

  fun schema_names infos =
    let
      fun add (Schematic {schematics, ...}, names) =
            List.foldl (fn ((name, _), result) =>
              if Redblackmap.inDomain (result, name) then result
              else Redblackmap.insert (result, name, []))
              names schematics
        | add (_, names) = names
    in
      List.foldl add (Redblackmap.mkDict String.compare) infos
    end

  fun insert_ground table name ty types =
    case insert_type ty types of
        SOME updated => Redblackmap.insert (table, name, updated)
      | NONE => table

  fun add_ground (name, ty) table =
    case Redblackmap.peek (table, name) of
        SOME tys => insert_ground table name ty tys
      | NONE => table

  fun is_ground rigid ty =
    List.all (fn tvar => mem tvar rigid) (Type.type_vars ty)

  (* Fold f over the constants of tm whose types are ground for rigid. *)
  fun fold_ground_consts rigid f tm acc =
    let
      fun walk current result =
        if is_const current then
          let val constant as (_, ty) = dest_const current in
            if is_ground rigid ty then f (constant, result) else result
          end
        else if is_comb current then
          walk (rand current) (walk (rator current) result)
        else if is_abs current then walk (body current) result
        else result
    in
      walk tm acc
    end

  fun add_grounds rigid tm table =
    fold_ground_consts rigid (fn (constant, result) =>
      add_ground constant result) tm table

  (* Both inputs are sorted and unique.  Keep the left representative of
     an equal type, as repeated insertion would. *)
  fun merge_types [] right = right
    | merge_types left [] = left
    | merge_types (left as ty :: tys) (right as other :: others) =
        case Type.compare (ty, other) of
            LESS => ty :: merge_types tys right
          | EQUAL => ty :: merge_types tys others
          | GREATER => other :: merge_types left others

  fun merge_grounds left right =
    Redblackmap.map (fn (name, tys) =>
      merge_types tys (lookup name right)) left

  fun subst_size (subst : subst) =
    List.foldl (fn ({residue, ...}, total) => Type.type_size residue + total)
      0 subst

  fun subst_pairs (subst : subst) =
    sort (fn ({redex = left, ...}, {redex = right, ...}) =>
      Type.compare (left, right)) subst

  fun compare_pairs ([] : subst, []) = EQUAL
    | compare_pairs ([], _) = LESS
    | compare_pairs (_, []) = GREATER
    | compare_pairs ({redex = lvar, residue = lty} :: ls,
                     {redex = rvar, residue = rty} :: rs) =
        case Type.compare (lvar, rvar) of
            EQUAL =>
              (case Type.compare (lty, rty) of
                   EQUAL => compare_pairs (ls, rs)
                 | result => result)
          | result => result

  (* Reverse preference order, so the least preferred key is first. *)
  fun compare_keys ((left_size, left_pairs), (right_size, right_pairs)) =
    case Int.compare (right_size, left_size) of
        EQUAL => compare_pairs (right_pairs, left_pairs)
      | order => order

  fun complete tvars subst =
    List.all (fn tvar =>
      List.exists (fn {redex, ...} => redex = tvar) subst) tvars

  fun match ty ground subst =
    SOME (Type.match_type_in_context ty ground subst)
      handle HOL_ERR _ => NONE

  fun substitutions tvars schematics covering known new require_new limit =
    let
      val visited = ref 0
      val best = ref (Redblackmap.mkDict compare_keys)
      fun add_best subst =
        let
          val size = subst_size subst
          val current = !best
          fun keep key pool =
            best := Redblackmap.insert (pool, key, subst)
        in
          if Redblackmap.numItems current < limit then
            let
              val key = (size, subst_pairs subst)
            in
              if Redblackmap.inDomain (current, key) then ()
              else keep key current
            end
          else
            case Redblackmap.firsti current of
                SOME (worst as (worst_size, _), _) =>
                  if size > worst_size then ()
                  else
                    let val key = (size, subst_pairs subst) in
                      if compare_keys (worst, key) = LESS andalso
                         not (Redblackmap.inDomain (current, key)) then
                        keep key (#1 (Redblackmap.remove (current, worst)))
                      else ()
                    end
              | NONE => ()
        end
      fun matches_new subst (name, ty) =
        List.exists (fn ground =>
          case match ty ground subst of SOME _ => true | NONE => false)
          (lookup name new)
      fun search remaining subst used_new =
        if !visited >= max_substitution_nodes then ()
        else if complete tvars subst then
          if not require_new orelse used_new orelse
             List.exists (matches_new subst) remaining
          then add_best subst
          else ()
        else
          (visited := !visited + 1;
          case remaining of
              [] => ()
            | (name, ty) :: rest =>
            let
              fun visit _ [] = ()
                | visit is_new (ground :: grounds) =
                    if !visited >= max_substitution_nodes then ()
                    else
                      (case match ty ground subst of
                           SOME refined =>
                             search rest refined (used_new orelse is_new)
                         | NONE => ();
                       visit is_new grounds)
            in
              visit true (lookup name new);
              visit false (lookup name known);
              search rest subst used_new
            end)
      fun direct (name, ty) =
        let
          fun consider is_new ground =
            case match ty ground [] of
                SOME subst =>
                  if complete tvars subst andalso
                     (not require_new orelse is_new orelse
                      List.exists (matches_new subst) schematics)
                  then add_best subst
                  else ()
              | NONE => ()
        in
          List.app (consider true) (lookup name new);
          List.app (consider false) (lookup name known)
        end
      val _ =
        (* Later rounds require a match from the current round's types.
           A fact whose constants have no such types cannot contribute. *)
        if require_new andalso
           List.all (fn (name, _) => null (lookup name new)) schematics then ()
        else
          case covering of
              [] => search schematics [] false
            | _ => List.app direct covering
    in
      Redblackmap.foldl' op:: [] (!best)
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

  fun process_fact rigid round merged known new remaining fact next_new =
    case fact of
        Schematic {theorem, tvars, schematics, covering, initial_round,
                   instances, ...} =>
          if round < initial_round orelse !remaining <= 0 orelse
             length schematics > max_schematic_occurrences then next_new
          else
            let
              val (old, fresh, require_new) =
                if round = initial_round then
                  (Redblackmap.mkDict String.compare, merged, false)
                else (known, new, true)
              val room = Int.min (max_thm_instances - length (!instances),
                !remaining)
              (* Substitutions are already in canonical preference order.
                 Different complete substitutions produce differently typed
                 theorem instances, and at most one per old instance can be
                 filtered below.  Instantiate only the bounded prefix that
                 can therefore contribute to this fact. *)
              val substs = if room <= 0 then [] else
                substitutions tvars schematics covering old fresh require_new
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

  (* The seed of a run: the rigid type variables and the initial table,
     which holds every schematic name (empty when it has no ground type)
     with the ground types of the goal and of the ground premises. *)
  fun add_premise_grounds rigid infos table =
    List.foldl (fn (Ground (_, theorem), result) =>
                  add_grounds rigid theorem result
                 | (_, result) => result) table infos

  (* A reusable seed: the goal, its rigid type variables and, once a run
     needs it, the ground types of the goal by constant name, sorted, for
     every constant whose type is ground for the rigid variables.  A run
     projects the index onto its own schematic names.  Both are computed
     on demand and at most once, so a pool that is never used (polymorphic
     encodings, no schematic helper) costs nothing. *)
  type 'a susp = {force : unit -> 'a, forced : unit -> bool}

  fun susp f =
    let val cell = ref NONE in
      {force = fn () => case !cell of
           SOME value => value
         | NONE => let val value = f () in cell := SOME value; value end,
       forced = fn () => Option.isSome (!cell)}
    end

  type pool = {fresh : hhNames.supply,
               goal : term susp,
               rigid : hol_type list susp,
               index : (string, hol_type list) Redblackmap.dict susp}

  fun index_add ((name, ty), dict) =
    insert_ground dict name ty (lookup name dict)

  fun index_of rigid goal =
    fold_ground_consts rigid index_add goal
      (Redblackmap.mkDict String.compare)

  fun mk_pool_with names goal =
    let val rigid = susp (fn () => Term.type_vars_in_term goal) in
      {fresh = names, goal = susp (fn () => goal), rigid = rigid,
       index = susp (fn () => index_of (#force rigid ()) goal)}
    end

  fun pool_indexed (pool : pool) = #forced (#index pool) ()

  (* The pool of [list_mk_conj (goal :: extras)], itself computed on
     demand.  The conjunction constructor adds the constant [/\] to the
     index.  A new type variable changes which types are ground, so the
     index is then rebuilt from the whole conjunction. *)
  fun extend_pool (pool : pool) extras =
    if null extras then pool
    else
      let
        val goal = susp (fn () =>
          boolSyntax.list_mk_conj (#force (#goal pool) () :: extras))
        val reuse = susp (fn () =>
          List.all (fn ty => mem ty (#force (#rigid pool) ()))
            (Term.type_vars_in_term (boolSyntax.list_mk_conj extras)))
        val rigid = susp (fn () =>
          if #force reuse () then #force (#rigid pool) ()
          else Term.type_vars_in_term (#force goal ()))
        val index = susp (fn () =>
          if #force reuse () then
            List.foldl (fn (tm, dict) =>
              fold_ground_consts (#force rigid ()) index_add tm dict)
              (index_add (dest_const boolSyntax.conjunction,
                          #force (#index pool) ()))
              extras
          else index_of (#force rigid ()) (#force goal ()))
      in
        {fresh = #fresh pool, goal = goal, rigid = rigid, index = index}
      end

  fun monomorph_pool {max_iters, max_new_instances} (pool : pool) premises =
    let
      val rigid = #force (#rigid pool) ()
      val infos = Portable.mapi (classify (#fresh pool) rigid) premises
      val names = schema_names infos
      val initial =
        if Redblackmap.numItems names = 0 then names
        else
          let val index = #force (#index pool) () in
            add_premise_grounds rigid infos
              (Redblackmap.map (fn (name, _) => lookup name index) names)
          end
      val remaining = ref (Int.max (0, max_new_instances))

      fun rounds round known new =
        if round > Int.max (0, max_iters) orelse !remaining <= 0 then ()
        (* From round 3 on, every fact requires a match from new. *)
        else if round > 2 andalso not (Redblackmap.exists (not o null) new)
        then ()
        else
          let
            (* Known and new are immutable during the round: merge once,
               for the facts entering now and for the next round. *)
            val merged = merge_grounds known new
            val next = List.foldl
              (fn (fact, result) =>
                process_fact rigid round merged known new remaining fact
                  result) names infos
          in
            rounds (round + 1) merged next
          end

      val _ = rounds 1 names initial
    in
      List.concat (map result_of infos)
    end

  val mk_pool = mk_pool_with hhNames.global

  fun monomorph caps goal premises =
    monomorph_pool caps (mk_pool goal) premises

end
