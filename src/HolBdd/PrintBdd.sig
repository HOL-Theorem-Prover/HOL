signature PrintBdd = sig
  val dotLabelledTermBdd : string -> string -> PrimitiveBddRules.term_bdd -> unit
  val dotBdd : string -> string -> bdd.bdd -> bdd.bdd
  val dotTermBdd : PrimitiveBddRules.term_bdd -> unit
  val dotTermBddFlag : bool ref
end
