signature type_pp =
sig

 val pp_type : type_grammar.grammar -> PPBackEnd.t ->
               Type.hol_type -> term_pp_types.uprinter
 val pp_type_with_depth : type_grammar.grammar -> PPBackEnd.t ->
                          int -> Type.hol_type -> term_pp_types.uprinter

 val type_pp_prefix : unit -> string
 val type_pp_suffix : unit -> string
 val term_pp_prefix : unit -> string
 val term_pp_suffix : unit -> string
 val thm_pp_prefix : unit -> string

end
