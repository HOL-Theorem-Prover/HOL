signature  disassemblerLib =
sig
  val opcode_string : Arbnum.num -> string
  val psr_string    : Arbnum.num -> string
  val is_coproc     : Arbnum.num -> bool
  val pp_arm        : unit -> unit
  val pp_arm6       : unit -> unit
  val npp_arm       : unit -> unit
  val npp_arm6      : unit -> unit
end
