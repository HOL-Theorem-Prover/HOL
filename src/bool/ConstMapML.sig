signature ConstMapML =
sig

  type constmap

  val theConstMap  : unit -> constmap
  val prim_insert  : Term.term * (string * string * Type.hol_type) -> unit
  val insert       : Term.term -> unit
  val apply        : Term.term -> string * string * Type.hol_type

end
