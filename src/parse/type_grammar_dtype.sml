structure type_grammar_dtype =
struct

datatype grammar_rule =
         INFIX of {opname : string, parse_string : string} list *
                  HOLgrammars.associativity

datatype type_structure =
         TYOP of {Thy : string, Tyop : string, Args : type_structure list}
       | PARAM of int

datatype delta =
         NEW_TYPE of string
       | NEW_INFIX of {Name : string, ParseName : string,
                       Assoc : HOLgrammars.associativity, Prec : int}

end
