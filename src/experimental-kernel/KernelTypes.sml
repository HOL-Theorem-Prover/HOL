structure KernelTypes =
struct

type hol_type = Type_dtype.hol_type
type id = KernelSig.kernelid

type const_info = id * Type_dtype.holty
datatype term = Var of string * hol_type
              | App of term * term
              | Const of const_info
              | Abs of term * term

end
