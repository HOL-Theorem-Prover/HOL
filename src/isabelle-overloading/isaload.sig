signature isaload =
sig

  include Abbrev
  val declare_const : string * hol_type -> unit

  val define_const : term -> thm

end

