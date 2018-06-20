signature FullUnify =
sig

  type tyenv
  val empty_tyenv : tyenv
  val tyunify : (string -> bool) -> tyenv -> (Type.hol_type * Type.hol_type) ->
                tyenv option

end
