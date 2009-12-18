signature Arbint =
sig

  include Arbintcore
  val pp_int     : HOLPP.ppstream -> int -> unit

end
