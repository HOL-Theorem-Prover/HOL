signature ConstMapML =
sig

  type constmap

  val theConstMap  : unit -> constmap
  val insert       : Term.term * (string * string) -> unit
  val apply        : Term.term -> string * string

end
