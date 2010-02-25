signature Theory =
sig

  include FinalTheory
  val incorporate_consts : string -> (string*hol_type)list -> unit

end
