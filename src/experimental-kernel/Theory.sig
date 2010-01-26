signature Theory =
sig

  include FinalTheory where type hol_type = Type.hol_type
                        and type term = Term.term
                        and type thm = Thm.thm

  val store_definition   : string * thm -> thm
  val incorporate_consts : string -> hol_type Vector.vector ->
                           (string*int) list -> unit

end
