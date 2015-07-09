signature hhReconstruct =
sig

  val minimize_flag : bool ref
  val reconstruct   : (string * string) -> term -> unit
  val reconstructl  : (string * string) list -> term -> unit

end
