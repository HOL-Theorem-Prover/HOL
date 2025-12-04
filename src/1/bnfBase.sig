signature bnfBase =
sig

  include Abbrev
  type t (* for "pure" manipulations *)
  datatype info = datatype bnfBase_dtype.info

  val pure_lookup : t -> hol_type -> thm info option

end
