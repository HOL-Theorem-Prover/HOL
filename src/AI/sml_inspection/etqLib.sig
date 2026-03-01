signature etqLib =
sig
  val etq : string -> Manager.proof
  val etq_tmo : real -> string -> Manager.proof
end
