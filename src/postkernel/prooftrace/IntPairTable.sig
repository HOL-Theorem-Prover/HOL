signature IntPairTable = sig

  type table

  val create : int -> table
  val lookup : table -> int * int -> int option
  val insert : table -> int * int -> int -> unit

end
