signature hhReconstruct =
sig

  include Abbrev
  val minimize_flag : bool ref
  val reconstruct   : thm list -> (string * string) -> term -> unit
  val reconstructl  : thm list -> (string * string) list -> term -> unit

end
