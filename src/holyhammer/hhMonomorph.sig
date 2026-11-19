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

  (* The goal as a reusable seed, for runs that differ only in their
     premises.  [monomorph_pool caps (mk_pool goal)] equals
     [monomorph caps goal].  Nothing is computed until a run with a
     schematic premise needs the goal's ground types, and then once.
     [extend_pool pool extras] is the pool of
     [list_mk_conj (goal :: extras)], goal being the one [pool] was made
     from.  [pool_indexed] tells whether the ground types were computed. *)
  type pool
  val mk_pool : term -> pool
  (* The same, with the fresh type variables that renaming a premise apart
     from the goal needs taken from the given supply (mk_pool takes them
     from the global counter).  Extended pools and the runs against them
     use the pool's supply. *)
  val mk_pool_with : hhNames.supply -> term -> pool
  val extend_pool : pool -> term list -> pool
  val pool_indexed : pool -> bool
  val monomorph_pool :
    {max_iters : int, max_new_instances : int} ->
    pool -> (string * term) list -> (string * term) list

end
