signature hhReconstruct =
sig

  include Abbrev
  exception Status of string
  val minimize_flag : bool ref
  val get_lemmas : (string * string) -> 
    (string * string) list option
  val reconstruct   : (string * string) -> term -> unit

end
