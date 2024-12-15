signature HOLquotation =
sig

  datatype frag = datatype quotation_dtype.frag
  type 'a quotation = 'a quotation_dtype.quotation

  val norm_quote : 'a quotation -> 'a quotation
  val dest_last_comment : 'a quotation -> 'a quotation * string option

end
