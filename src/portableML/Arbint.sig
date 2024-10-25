signature Arbint =
sig

  include Arbintcore
  val pp_int     : int -> HOLPP.pretty

end
