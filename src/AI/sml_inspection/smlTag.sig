signature smlTag =
sig

  val sml_fst : ('a * 'b) -> 'a
  val number_stac : string -> string
  val drop_numbering : string list -> string list
  val replace_at : string list * string list -> string list -> string list

end
