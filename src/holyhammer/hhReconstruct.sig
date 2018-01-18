signature hhReconstruct =
sig

  include Abbrev
  val get_lemmas : (string * string) -> (string * string) list option
  val reconstruct : (string * string) -> goal -> tactic
  val reconstruct_stac : (string * string) -> goal -> string option

end
