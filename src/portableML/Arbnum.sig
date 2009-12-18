signature Arbnum =
sig

  include Arbnumcore

  val base_pp_num : StringCvt.radix -> HOLPP.ppstream -> num -> unit
  val pp_num      : HOLPP.ppstream -> num -> unit

end
