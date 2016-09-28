structure type_grammar_dtype =
struct

datatype grammar_rule =
         INFIX of {opname : string, parse_string : string} list *
                  HOLgrammars.associativity

datatype type_structure =
         TYOP of {Thy : string, Tyop : string, Args : type_structure list}
       | PARAM of int

end
