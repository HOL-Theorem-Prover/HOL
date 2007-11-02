signature Varmap = sig
  type varmap = (string, int) Binarymap.dict
  exception unifyVarmapError
  val size : varmap -> int
  val dest : varmap -> (string * int) list
  val extends : varmap -> varmap -> bool
  val insert : string * int -> varmap -> varmap
  val empty : varmap
  val eq : varmap * varmap -> bool
  val peek : varmap -> string -> int option
  val unify : varmap -> varmap -> varmap
  val remove : string -> varmap -> varmap
end
