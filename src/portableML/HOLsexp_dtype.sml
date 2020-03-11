structure HOLsexp_dtype =
struct

datatype t =
           Symbol of string
         | String of string
         | Integer of int
         | Cons of t * t

end
