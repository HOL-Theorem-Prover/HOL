structure DB_dtype =
struct

 datatype class = Thm | Axm | Def
 datatype theory =
          THEORY of string *
                {types       : (string * int) list,
                 consts      : (string * Type.hol_type) list,
                 parents     : string list,
                 axioms      : (string * Thm.thm) list,
                 definitions : (string * Thm.thm) list,
                 theorems    : (string * Thm.thm) list}

 type data = (string * string) * (Thm.thm * class)


end
