signature Arbnum =
sig

  include Arbnumcore where type num = Arbnumcore.num

  val base_pp_num : StringCvt.radix -> num -> HOLPP.pretty
  val pp_num      : num -> HOLPP.pretty

end
