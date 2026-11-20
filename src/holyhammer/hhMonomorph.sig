(* Bounded term-level monomorphization for the new problem generator. *)
signature hhMonomorph =
sig

  type term = Term.term

  (* The goal supplies round-zero ground instances.  The first ten premises
     are privileged (round one); the remaining premises start in round two.
     A schematic premise can produce several terms with the same nickname. *)
  val monomorph :
    {max_iters : int, max_new_instances : int} ->
    term -> (string * term) list -> (string * term) list

end
