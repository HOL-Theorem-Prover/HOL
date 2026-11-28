(* Bounded term-level monomorphization of premises for hhProblemGen. *)
signature hhMonomorph =
sig

  type term = Term.term

  (* [monomorph caps goal premises] keeps the ground premises and replaces
     each schematic one by at most ten ground instances, under its
     nickname, or drops it when it has none.  Instances are found in at
     most max_iters rounds, at most max_new_instances in all, at the types
     of constants in the goal, the ground premises and earlier instances;
     the goal's type variables count as ground.  The first ten premises
     are privileged (round one); the remaining premises start in round
     two. *)
  val monomorph :
    {max_iters : int, max_new_instances : int} ->
    term -> (string * term) list -> (string * term) list

  (* The goal as a reusable seed, for runs that differ only in their
     premises.  [monomorph_pool caps (mk_pool goal)] equals
     [monomorph caps goal].  The goal's type variables are computed at the
     first run and its ground types at the first run with a schematic
     premise, each once.  [extend_pool pool extras] is the pool of
     [list_mk_conj (goal :: extras)], goal being the one [pool] was made
     from.  [pool_indexed] tells whether the ground types were computed. *)
  type pool
  val mk_pool : term -> pool
  val extend_pool : pool -> term list -> pool
  val pool_indexed : pool -> bool
  val monomorph_pool :
    {max_iters : int, max_new_instances : int} ->
    pool -> (string * term) list -> (string * term) list

end
