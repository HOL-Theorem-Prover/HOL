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

  (* The same, with the goal given as a reusable seed.  [monomorph_pool
     caps (mk_pool goal)] equals [monomorph caps goal].  [extend_pool
     pool goal extras] is the pool of [list_mk_conj (goal :: extras)]
     (the goal is the one [pool] was made from). *)
  type pool
  val mk_pool : term -> pool
  val extend_pool : pool -> term -> term list -> pool
  val monomorph_pool :
    {max_iters : int, max_new_instances : int} ->
    pool -> (string * term) list -> (string * term) list

end
