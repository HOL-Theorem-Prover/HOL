signature PolyRuntime =
sig
  exception TacticTimeout of real

  (* Execute f(x) with a timeout in seconds.
     Raises TacticTimeout if the computation exceeds the limit.
     On runtimes without thread support, runs f(x) without timeout. *)
  val tactic_timeout : real -> ('a -> 'b) -> 'a -> 'b

  (* Save the current heap state to the given path.
     Does nothing on runtimes without heap save support. *)
  val save_heap : string -> unit

  (* Compile and execute an SML string in the current namespace.
     Used for fragment-stepped proof execution.
     Raises Fail on runtimes without compiler access. *)
  val eval_sml_string : string -> unit
end
