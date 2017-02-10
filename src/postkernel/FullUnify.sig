signature FullUnify =
sig

  type tyenv
  val empty_tyenv : tyenv
  val tyunify : (string -> bool) -> tyenv -> (hol_type * hol_type) ->
                tyenv option

end
