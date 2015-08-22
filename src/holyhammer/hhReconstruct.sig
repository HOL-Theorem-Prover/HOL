signature hhReconstruct =
sig

  val minimize_flag : bool ref
  val reconstruct   : thm list -> (string * string) -> term -> unit
  val reconstructl  : thm list -> (string * string) list -> term -> unit

end
