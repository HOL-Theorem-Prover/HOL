signature ParList =
sig
  (* The worker count must be positive.  Results retain input order; all
     started workers unwind before return or an input-ordered exception. *)
  val map_with_workers: int -> ('a -> 'b) -> 'a list -> 'b list
  (* The worker count must be positive.  The first published result stops
     the race; interrupted losers unwind before return. *)
  val get_some_with_workers:
    int -> ('a -> 'b option) -> 'a list -> 'b option
  val get_some: ('a -> 'b option) -> 'a list -> 'b option
  val get_first: ('a -> 'b option) -> 'a list -> 'b option
  (* Like [Thread_Attributes.uninterruptible], for a wait that must run to
     completion yet must not swallow the user's Ctrl-C.  A plain mask clears
     the broadcast flag, and Poly/ML drops a broadcast interrupt aimed at a
     thread that is not accepting one instead of retaining it the way it
     retains a directed interrupt.  [observe g y] therefore runs [g y] under
     the caller's own attributes and answers [SOME] with its result, or
     records the interrupt and answers [NONE]; steps after a recorded
     interrupt run masked.  A recorded interrupt is raised once the body has
     returned; an exception raised by the body itself wins over it. *)
  val uninterruptible_wait:
    ((('c -> 'd) -> 'c -> 'd option) -> 'a -> 'b) -> 'a -> 'b
end
