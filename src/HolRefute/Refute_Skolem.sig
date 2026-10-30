signature Refute_Skolem = sig
  type dependency =
    {origin : int,
     source_type : Type.hol_type}

  type info =
    {origin : int option,
     generated_name : string,
     source_name : string,
     source_type : Type.hol_type,
     dependencies : dependency list,
     arity : int,
     stage : string}

  val prefix_binders : Term.term -> (string * Type.hol_type) list
  val mark_source_ambiguities :
    Term.term -> (string * Type.hol_type) list ->
    (string * Type.hol_type) list
  val map_types : (Type.hol_type -> Type.hol_type) -> info -> info
end
