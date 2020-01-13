signature HOLsexp =
sig

  datatype t = datatype HOLsexp_dtype.t

  val Nil : t
  val Quote : t
  val List : t list -> t

  val printer : t HOLPP.pprinter
  val scan : (char, 'a) StringCvt.reader -> (t, 'a) StringCvt.reader
  val fromString : string -> t option

end
