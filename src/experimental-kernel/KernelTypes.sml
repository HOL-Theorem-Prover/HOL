structure KernelTypes =
struct

datatype hol_type = Tyv of string
                  | Tyapp of KernelSig.kernelid * hol_type list

type const_info = (KernelSig.kernelid * hol_type)
datatype term = Var of string * hol_type
              | App of term * term
              | Const of const_info
              | Abs of term * term

end
