structure Refute_Eval :> Refute_Eval = struct
  type term = Term.term

  type mode = Refute_SmartGen.mode
  type program_version = Refute_SmartGen.program_version

  datatype plan =
      Test of term
    | Gen of term * plan
    | Bind of term * term * plan option * plan
    | Split of term * (term * term list * plan) list
    | Guard of term * plan
    | SmartGuard of {predicate : term, version : program_version,
                     cont : plan}
    | Enum of {rel : term, mode : mode, version : program_version,
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

  (* Preorder, may contain duplicates; callers dedup as needed. *)
  fun plan_gen_types plan =
    case plan of
        Test _ => []
      | Gen (variable, next) =>
          Term.type_of variable :: plan_gen_types next
      | Bind (_, _, fallback, next) =>
          (case fallback of
               NONE => []
             | SOME alternative => plan_gen_types alternative) @
          plan_gen_types next
      | Split (_, branches) =>
          List.concat (List.map (plan_gen_types o #3) branches)
      | Guard (_, next) => plan_gen_types next
      | SmartGuard {cont, ...} => plan_gen_types cont
      | Enum {cont, ...} => plan_gen_types cont
      | Prune => []

  (* Does this plan depend on the smart-generator machinery?  Both the
     substrate compilers and the QC gate ask this question, so a new plan
     constructor is classified in one place. *)
  fun plan_uses_enum plan =
    case plan of
        Enum _ => true
      | SmartGuard _ => true
      | Gen (_, next) => plan_uses_enum next
      | Bind (_, _, fallback, next) =>
          plan_uses_enum next orelse
          Option.getOpt (Option.map plan_uses_enum fallback, false)
      | Split (_, branches) =>
          List.exists (plan_uses_enum o #3) branches
      | Guard (_, next) => plan_uses_enum next
      | Test _ => false
      | Prune => false

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
        id1 = id2 andalso
        Lib.list_eq (fn first => fn second =>
          same_shape (first, second)) fields1 fields2
    in
      depth1 = depth2 andalso complete1 = complete2 andalso
      Lib.list_eq (fn first => fn second =>
        same_constructor (first, second)) constructors1 constructors2
    end

  fun same_pattern (CaseVariable, CaseVariable) = true
    | same_pattern
        (CaseConstructor (id1, arguments1),
         CaseConstructor (id2, arguments2)) =
        id1 = id2 andalso
        Lib.list_eq (fn first => fn second =>
          same_pattern (first, second)) arguments1 arguments2
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
          Lib.list_eq (fn first => fn second =>
            same_branch (first, second)) branches1 branches2
        end
    | same_tree _ = false

  fun same_case_tree NONE NONE = true
    | same_case_tree (SOME first) (SOME second) =
        same_tree (first, second)
    | same_case_tree _ _ = false

  fun same_optional_env NONE NONE = true
    | same_optional_env (SOME first) (SOME second) =
        same_env first second
    | same_optional_env _ _ = false

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

  (* Selftest-only stream hook.  Replacing tests by failure exposes each
     generated environment without changing the generator or its state. *)
  fun dump_plan current =
    case current of
        Test _ => Test boolSyntax.F
      | Gen (variable, next) => Gen (variable, dump_plan next)
      | Bind (variable, tm, fallback, next) =>
          Bind (variable, tm, Option.map dump_plan fallback, dump_plan next)
      | Split (tm, branches) =>
          Split (tm, List.map (fn (constructor, variables, next) =>
            (constructor, variables, dump_plan next)) branches)
      | Guard (tm, next) => Guard (tm, dump_plan next)
      | SmartGuard {predicate, version, cont} =>
          SmartGuard {predicate = predicate, version = version,
                      cont = dump_plan cont}
      | Enum {rel, mode, version, ins, outs, cont} =>
          Enum {rel = rel, mode = mode, version = version,
                ins = ins, outs = outs, cont = dump_plan cont}
      | Prune => Test boolSyntax.F

  fun dump_stream (test : compiled_test) {size, count} =
    let
      fun loop 0 candidates = rev candidates
        | loop remaining candidates =
            (case #run test
              {genuine_only = true, card = 1, size = size,
               draws = 1, ignored = []} of
                 CexFound {env, ...} =>
                   loop (remaining - 1)
                     (rev (List.map #2 env) :: candidates)
               | Exhausted _ =>
                   raise Fail "Refute candidate dump exhausted"
               | GaveUp reason => raise Fail reason)
      val result = Exn.capture (fn () => loop (Int.max (0, count)) []) ()
      val close_result = Exn.capture (#close test) ()
    in
      case close_result of
          Exn.Res _ => Exn.release result
        | Exn.Exn error => raise error
    end

  val substrate_registry : substrate list ref = ref []

  fun substrate_before (left : substrate) (right : substrate) =
    #priority left < #priority right orelse
    (#priority left = #priority right andalso #name left < #name right)

  fun insert substrate [] = [substrate]
    | insert substrate (other :: rest) =
        if substrate_before substrate other then
          substrate :: other :: rest
        else other :: insert substrate rest

  fun register_substrate substrate =
    let
      val remaining = List.filter
        (fn registered => #name registered <> #name substrate)
        (!substrate_registry)
    in
      substrate_registry := insert substrate remaining
    end

  fun get_substrates () = !substrate_registry
end
