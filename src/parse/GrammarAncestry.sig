signature GrammarAncestry =
sig

  val ancestry : {thy:string} -> string list
  val set_ancestry : string list -> unit

end
