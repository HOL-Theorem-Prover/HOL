structure TheoryDatTokens_dtype =
struct

  datatype t = ID of string
             | QString of string
             | Num of Arbnum.num
             | LBr
             | RBr
             | Comma
             | EOF
  exception DatTokenError of string


end
