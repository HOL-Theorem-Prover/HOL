signature Lift =
sig
  include Abbrev

  val lift_def_syntax   : (string -> term option) * string 
                           -> string list * string list * term list
  val pp_lifter_def     : ppstream -> string -> unit
  val lift_ML_as_string : hol_type -> string -> string

end
