signature bnfBase =
sig

  type t (* for "pure" manipulations *)
  datatype info = datatype bnfBase_dtype.info

  val pure_lookup : t -> hol_type -> info option

end
