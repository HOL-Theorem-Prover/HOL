structure Refute_Eval :> Refute_Eval = struct
  type term = Term.term

  type mode = Refute_SmartGen.mode
  type program_version = Refute_SmartGen.program_version
  type relation_key = Refute_SmartGen.relation_key

  datatype plan =
      Test of term
    | Gen of term * plan
    | Bind of term * term * plan option * plan
    | Split of term * (term * term list * plan) list
    | Guard of {condition : term, smart : bool, cont : plan}
    | SmartGuard of {predicate : term, version : program_version,
                     cont : plan}
    | Enum of {rel : relation_key, mode : mode, version : program_version,
               ins : term list, outs : term list, cont : plan}
    | Prune

  datatype quant = Forall | Exists

  datatype qc_problem =
      Plans of plan list
    | Pnf of {prefix : (quant * term) list, body : term}

  datatype case_shape =
    CaseShape of
      {depth : int, complete : bool,
       constructors : case_constructor list}
  withtype case_constructor = {id : int, fields : case_shape list}

  datatype case_pattern =
      CaseVariable
    | CaseConstructor of int * case_pattern list

  datatype case_tree =
      CaseLeaf
    | CaseUniversal of
        {shape : case_shape, witness : term, subtree : case_tree}
    | CaseExistential of
        {shape : case_shape,
         branches : (case_pattern * term * case_tree) list}

  type candidate =
    {env : (term * term) list,
     ground_env : (term * term) list option,
     case_tree : case_tree option,
     genuine : bool,
     run_depth : int option}

  datatype verdict = Continue | Found of candidate

  datatype run_result =
      CexFound of candidate
    | Exhausted of {complete : bool}
    | GaveUp of string

  datatype strategy =
      Exhaustive
    | Random of {seed : IntInf.int}
    | Narrowing

  (* Substrate selection checks [accepts] before calling [compile].
     These helpers make that invariant explicit inside ground-only
     compilers, without duplicating applicability guards in each one. *)
  fun ground_strategy Exhaustive {exhaustive, random = _} =
        exhaustive ()
    | ground_strategy (Random {seed}) {exhaustive = _, random} =
        random seed
    | ground_strategy Narrowing _ =
        raise Fail "Refute_Eval.ground_strategy: capability invariant"

  fun with_plans (Plans plans) body = body plans
    | with_plans (Pnf _) _ =
        raise Fail "Refute_Eval.with_plans: capability invariant"

  type run_input =
    { genuine_only : bool,
      card : int,
      size : int,
      draws : int,
      ignored : candidate list }

  type compiled_test =
    { run : run_input -> run_result,
      close : unit -> unit,
      max_chunk : int option,
      last_stats : (string * int) list ref }

  datatype compile_result =
      Compiled of compiled_test
    | Inapplicable of string list

  type substrate =
    { name : string,
      priority : int,
      accepts : qc_problem -> bool,
      preflight :
        (Refute_Core.config -> strategy -> plan list -> term list ->
          string list) option,
      compile : Refute_Core.config -> strategy -> qc_problem ->
        compile_result }

  val rand_modulus : IntInf.int = 18446744073709551616
  val rand_output_divisor : IntInf.int = 4294967296

  fun normalize_seed state = IntInf.mod (state, rand_modulus)

  fun rand_next state =
    normalize_seed
      (6364136223846793005 * state + 1442695040888963407)

  fun rand_out state = IntInf.div (state, rand_output_divisor)

  fun rand_below bound state =
    let
      val next = rand_next state
      val value = IntInf.div (rand_out next * bound, rand_output_divisor)
    in
      (value, next)
    end

  fun checked_rand_below bound state =
    if bound <= 0 orelse bound > rand_output_divisor then
      raise Fail "Refute rand_below bound exceeds 2^32"
    else
      rand_below bound state

  val rand_below_limit = rand_output_divisor

  val session_seed : IntInf.int ref = ref 42
  val session_seed_mutex = Mutex.mutex ()

  (* Reserving an implicit seed advances the session stream exactly once.
     Refute invocations may be reentrant, so the ordinary output mutex is
     not sufficient protection for this mutable stream. *)
  fun take_session_seed () =
    Multithreading.synchronized "Refute random seed" session_seed_mutex
      (fn () =>
        let
          val seed = !session_seed
          val _ = session_seed := rand_next seed
        in
          seed
        end)

  (* Preorder, may contain duplicates; callers dedup as needed. *)
  fun plan_gen_types plan =
    case plan of
        Test _ => []
      | Gen (variable, next) =>
          Term.type_of variable :: plan_gen_types next
      | Bind (_, _, fallback, next) =>
          Option.getOpt (Option.map plan_gen_types fallback, []) @
          plan_gen_types next
      | Split (_, branches) =>
          List.concat (List.map (plan_gen_types o #3) branches)
      | Guard {cont, ...} => plan_gen_types cont
      | SmartGuard {cont, ...} => plan_gen_types cont
      | Enum {cont, ...} => plan_gen_types cont
      | Prune => []

  (* Both plan classifiers below are the same search for [Enum] or
     [SmartGuard] anywhere in the plan, and differ only in whether a
     smart [Guard] counts; [count_smart_guard] is that one bit, so a
     new plan constructor is classified in one place. *)
  fun plan_search count_smart_guard plan =
    let
      fun walk plan =
        case plan of
            Enum _ => true
          | SmartGuard _ => true
          | Gen (_, next) => walk next
          | Bind (_, _, fallback, next) =>
              walk next orelse
              Option.getOpt (Option.map walk fallback, false)
          | Split (_, branches) => List.exists (walk o #3) branches
          | Guard {smart, cont, ...} =>
              (count_smart_guard andalso smart) orelse walk cont
          | Test _ => false
          | Prune => false
    in
      walk plan
    end

  (* Does this plan need enumerator programs for a fuel-bounded
     construct whose terminal exhaustion cannot be certified?  A smart
     [Guard] is excluded: its condition is a closed guard over
     already-bound inputs, decided with the same three-valued
     discipline as an ordinary one, so it needs no enumerator and its
     exhaustion is exact. *)
  val plan_uses_enum = plan_search false

  (* Does this plan contain a smart construct -- [Enum], [SmartGuard]
     or a smart [Guard] -- that the executability gate must account
     for?  All three are compiled by the smart-generator machinery, and
     a syntactically gated goal needs one of them to lift. *)
  val plan_uses_smart = plan_search true

  val same_env = Lib.list_eq boolSyntax.tmp_eq

  fun same_shape
        (CaseShape {depth = depth1, complete = complete1,
                    constructors = constructors1},
         CaseShape {depth = depth2, complete = complete2,
                    constructors = constructors2}) =
    let
      fun same_constructor
            ({id = id1, fields = fields1},
             {id = id2, fields = fields2}) =
        id1 = id2 andalso Lib.list_eq (Lib.curry same_shape) fields1 fields2
    in
      depth1 = depth2 andalso complete1 = complete2 andalso
      Lib.list_eq (Lib.curry same_constructor) constructors1 constructors2
    end

  fun same_pattern (CaseVariable, CaseVariable) = true
    | same_pattern
        (CaseConstructor (id1, arguments1),
         CaseConstructor (id2, arguments2)) =
        id1 = id2 andalso
        Lib.list_eq (Lib.curry same_pattern) arguments1 arguments2
    | same_pattern _ = false

  fun same_tree (CaseLeaf, CaseLeaf) = true
    | same_tree
        (CaseUniversal {shape = shape1, witness = witness1,
                        subtree = subtree1},
         CaseUniversal {shape = shape2, witness = witness2,
                        subtree = subtree2}) =
        same_shape (shape1, shape2) andalso
        Term.aconv witness1 witness2 andalso same_tree (subtree1, subtree2)
    | same_tree
        (CaseExistential {shape = shape1, branches = branches1},
         CaseExistential {shape = shape2, branches = branches2}) =
        let
          fun same_branch
                ((pattern1, term1, subtree1),
                 (pattern2, term2, subtree2)) =
            same_pattern (pattern1, pattern2) andalso
            Term.aconv term1 term2 andalso same_tree (subtree1, subtree2)
        in
          same_shape (shape1, shape2) andalso
          Lib.list_eq (Lib.curry same_branch) branches1 branches2
        end
    | same_tree _ = false

  val same_case_tree = Lib.option_eq (Lib.curry same_tree)

  val same_optional_env = Lib.option_eq same_env

  (* [run_depth] is part of candidate identity on purpose: narrowing carries
     its ignore list forward to the next scheduled depth, and the same
     bindings found deeper are a fresh opportunity, not a repeat — a
     depth-truncated case tree may be complete at depth + 1 and certify
     there.  So an entry stored at depth d deliberately does not suppress
     the same candidate at depth d + 1; within one depth the list still
     does its job.  (Tree-carrying candidates are already discriminated by
     [same_case_tree], since CaseShape records the depth.) *)
  fun same_candidate first second =
    same_env (#env first) (#env second) andalso
    same_optional_env (#ground_env first) (#ground_env second) andalso
    #genuine first = #genuine second andalso
    same_case_tree (#case_tree first) (#case_tree second) andalso
    #run_depth first = #run_depth second

  fun ignored_candidate candidate ignored =
    List.exists (same_candidate candidate) ignored

  fun fully_applied_constructor tm =
    let
      val (constructor, arguments) = boolSyntax.strip_comb tm
      val (domain, _) = boolSyntax.strip_fun (Term.type_of constructor)
    in
      if TypeBase.is_constructor constructor andalso
         length domain = length arguments
      then SOME (constructor, arguments)
      else NONE
    end

  val substrate_registry : substrate list ref = ref []
  val substrate_mutex = Mutex.mutex ()

  fun synchronized_substrates f =
    Multithreading.synchronized "Refute_Eval.substrates" substrate_mutex f

  fun substrate_before (left : substrate) (right : substrate) =
    #priority left < #priority right orelse
    (#priority left = #priority right andalso #name left < #name right)

  fun insert substrate [] = [substrate]
    | insert substrate (other :: rest) =
        if substrate_before substrate other then
          substrate :: other :: rest
        else other :: insert substrate rest

  fun register_substrate substrate =
    synchronized_substrates (fn () =>
      let
        val remaining = List.filter
          (fn registered => #name registered <> #name substrate)
          (!substrate_registry)
      in
        substrate_registry := insert substrate remaining
      end)

  fun get_substrates () =
    synchronized_substrates (fn () => !substrate_registry)
end
