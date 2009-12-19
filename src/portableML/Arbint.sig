signature Arbint =
sig

  include Arbintcore where type int = Arbintcore.int
  val pp_int     : HOLPP.ppstream -> int -> unit

end
