signature fspathTrie =
sig

  type t
  val empty : t
  val insertPath : string -> t -> t
  val hasPrefix : t -> string -> string option

end
