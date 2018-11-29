signature type_pp =
sig

 val pp_type : type_grammar.grammar -> PPBackEnd.t ->
               Type.hol_type -> term_pp_types.uprinter
 val pp_type_with_depth : type_grammar.grammar -> PPBackEnd.t ->
                          int -> Type.hol_type -> term_pp_types.uprinter

 val pp_num_types   : bool ref
 val pp_array_types : bool ref
end
