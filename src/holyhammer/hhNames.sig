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

  (* A supply private to its user, which must be a single thread, and
     used only inside scoped.  It is seeded by one draw from the global
     counter, so that its first name is the one the global supply would
     have given, and it then continues with the successive numbers,
     formatted as Type.gen_tyvar formats them (the result is the same type
     variable, so Type.is_gen_tyvar holds).  Its sequence does not depend
     on what other threads draw meanwhile.  The global counter does go on
     meanwhile, so a concurrent global draw can repeat a number that the
     supply hands out, until release: callers must keep the terms that
     carry private names apart from the terms of the global draws (the
     producer's memo and pool never meet a replay's terms).  Every name
     that the user holds from before the seed was drawn globally, below
     every private number.
     scoped f runs f on the calling thread with the kernel's complaint
     about the format of these names switched off.  It pins the thread
     (Context.with_context), which is what makes the switch private to it:
     a flag set without a pin is the live flag that every thread reads.
     release () must be called once the supply is no longer used: it
     advances the global counter past every number handed out, so that no
     later global draw repeats a name held in a memo or a cache.  Calling
     it more than once, or without any draw, is harmless. *)
  val private_supply : unit ->
    {supply : supply, release : unit -> unit,
     scoped : (unit -> unit) -> unit}

end
