signature hhReconstruct =
sig

  include Abbrev

  (* Settings *)
  val reconstruct_flag : bool ref
  val minimization_timeout : real ref
  val reconstruction_timeout : real ref

  (* Read output of ATP *)
  val get_lemmas : (string * string) -> string list option

  (* Reconstruction *)
  val hh_reconstruct : string list -> goal -> (string * tactic)

end
