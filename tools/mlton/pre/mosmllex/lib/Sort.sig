(* Sorting lists *)

signature SORT =
sig

  val sort : ('a * 'a -> bool) * 'a list -> 'a list;
        (* Sort a list in increasing order according to an ordering predicate.
           The predicate should return [true] if its first argument is
           less than or equal to its second argument. Preserves original
           order of elements that compare equal. *)

end (* signature SORT *)
