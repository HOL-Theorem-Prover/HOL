structure type_grammar_dtype =
struct

datatype grammar_rule =
         INFIX of {opname : string, parse_string : string} list *
                  HOLgrammars.associativity

datatype type_structure =
         TYOP of {Thy : string, Tyop : string, Args : type_structure list}
       | PARAM of int

datatype delta =
         NEW_TYPE of KernelSig.kernelname
       | NEW_INFIX of {Name : string, ParseName : string,
                       Assoc : HOLgrammars.associativity, Prec : int}
       | TYABBREV of KernelSig.kernelname * Type.hol_type
       | DISABLE_TYPRINT of string
       | RM_KNM_TYABBREV of KernelSig.kernelname
       | RM_TYABBREV of string

end
