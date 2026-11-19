(* Supplies of the fresh type variables that the problem generator draws
   while it prepares a problem (renaming a premise apart from the goal,
   instantiating combinators, unifying their applications). *)
signature hhNames =
sig

  (* One call, one fresh type variable. *)
  type supply = unit -> Type.hol_type

  (* The process-global counter, Type.gen_tyvar: what every export outside
     the pipelined run uses. *)
  val global : supply

  (* A supply private to its user, which must be a single thread.  It is
     seeded by one draw from the global counter, so that its first name is
     the one the global supply would have given and it then continues with
     the successive numbers, formatted as Type.gen_tyvar formats them.  The
     names it hands out are drawn from nobody else, so the sequence of
     names does not depend on what other threads draw meanwhile.  release
     () must be called once the supply is no longer used: it advances the
     global counter past every number handed out, so that no later global
     draw repeats a name held in a memo or a cache.  Calling it more than
     once, or without any draw, is harmless. *)
  val private_supply : unit -> {supply : supply, release : unit -> unit}

end
