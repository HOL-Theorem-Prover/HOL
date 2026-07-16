structure Refute_Eval :> Refute_Eval = struct
  type term = Term.term

  datatype plan =
      Test of term
    | Gen of term * plan
    | Bind of term * term * plan option * plan
    | Split of term * (term * term list * plan) list
    | Guard of term * plan
    | Prune

  type candidate = {env : (term * term) list, genuine : bool}

  datatype verdict = Continue | Found of candidate

  datatype run_result =
      CexFound of candidate
    | Exhausted of {complete : bool}
    | GaveUp of string

  datatype strategy =
      Exhaustive
    | Random of {seed : IntInf.int}

  type run_input =
    { genuine_only : bool,
      card : int,
      size : int,
      draws : int,
      ignored : candidate list }

  type compiled_test =
    { run : run_input -> run_result,
      last_stats : (string * int) list ref }

  datatype compile_result =
      Compiled of compiled_test
    | Inapplicable of string list

  type substrate =
    { name : string,
      priority : int,
      compile : Refute_Core.config -> strategy -> plan list ->
        compile_result }

  val rand_modulus : IntInf.int = 18446744073709551616
  val rand_output_divisor : IntInf.int = 4294967296

  fun rand_next state =
    IntInf.mod
      (6364136223846793005 * state + 1442695040888963407,
       rand_modulus)

  fun rand_out state = IntInf.div (state, rand_output_divisor)

  fun rand_below bound state =
    let
      val next = rand_next state
      val value = IntInf.div (rand_out next * bound, rand_output_divisor)
    in
      (value, next)
    end

  val session_seed : IntInf.int ref = ref 42

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
