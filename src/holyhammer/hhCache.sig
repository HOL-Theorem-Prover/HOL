signature hhCache =
sig
  type key_parts =
    {prover : string, version : string option, argv : string list,
     problem : string}

  (* Use key_of_digest to share the SHA-1 of an immutable problem file
     across requests with different arguments. *)
  val key_of_digest : string -> key_parts -> string
  val key_of : key_parts -> string
  val lookup : hhConfig.hh_options -> string -> hhProver.run_result option
  val store : hhConfig.hh_options -> string -> hhProver.run_result -> unit
  val prune : hhConfig.hh_options -> unit
end
