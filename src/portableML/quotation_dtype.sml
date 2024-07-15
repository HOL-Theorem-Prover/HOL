structure quotation_dtype =
struct

  datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a
  type 'a quotation = 'a frag list

end
