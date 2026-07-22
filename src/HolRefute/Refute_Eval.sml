structure Refute_Eval :> Refute_Eval = struct
  type term = Term.term

  datatype plan =
      Test of term
    | Gen of term * plan
    | Bind of term * term * plan option * plan
    | Split of term * (term * term list * plan) list
    | Guard of term * plan
    | Prune

  datatype quant = Forall | Exists

  datatype qc_problem =
      Plans of plan list
    | Pnf of {prefix : (quant * term) list, body : term}

  type candidate = {env : (term * term) list, genuine : bool}

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
      | Prune => []

  val same_env = Lib.list_eq boolSyntax.tmp_eq

  fun ignored_candidate env ignored =
    List.exists (fn candidate => same_env env (#env candidate)) ignored

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
