signature  disassemblerLib =
sig
  val opcode_string : Arbnum.num -> string
  val pp_word_psr : unit -> unit
  val pp_word_pipe : unit -> unit
  val pp_word_arm_ex : unit -> unit
  val pp_word_arm : unit -> unit
  val npp_word_psr : unit -> unit
  val npp_word_pipe : unit -> unit
  val npp_word_arm_ex : unit -> unit
  val npp_word_arm : unit -> unit
end
