signature Par_List =
sig
  val map_name: string -> ('a -> 'b) -> 'a list -> 'b list
  val map_independent: ('a -> 'b) -> 'a list -> 'b list
  val map: ('a -> 'b) -> 'a list -> 'b list
  val get_some: ('a -> 'b option) -> 'a list -> 'b option
  val find_some: ('a -> bool) -> 'a list -> 'a option
  val exists: ('a -> bool) -> 'a list -> bool
  val forall: ('a -> bool) -> 'a list -> bool
end;
