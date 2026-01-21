signature terminal_primitives =
sig


  val strmIsTTY : TextIO.outstream -> bool
  val TERM_isANSI : unit -> bool

end
