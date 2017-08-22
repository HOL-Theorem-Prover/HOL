signature hhReconstruct =
sig

  include Abbrev
  exception Status of string
  val minimize_flag : bool ref
  val reconstruct   : (string * string) -> term -> unit

end
