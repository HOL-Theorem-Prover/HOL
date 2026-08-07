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
end
