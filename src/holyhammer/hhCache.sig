signature hhCache =
sig
  type key_parts =
    {prover : string, version : string option, argv : string list,
     problem : string}

  (* lookup and store take the key that key_of computes, so that the
     problem is hashed once per run. *)
  val key_of : key_parts -> string
  val lookup : hhConfig.hh_options -> string -> hhProver.run_result option
  val store : hhConfig.hh_options -> string -> hhProver.run_result -> unit
  val prune : hhConfig.hh_options -> unit
end
