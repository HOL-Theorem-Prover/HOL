signature kind_pp =
sig

 val pp_kind : kind_grammar.grammar -> PPBackEnd.t ->
               Portable.ppstream -> Kind.kind -> unit
 val pp_kind_with_depth : kind_grammar.grammar -> PPBackEnd.t ->
                          Portable.ppstream -> int -> Kind.kind -> unit

 val pp_arity_kinds : bool ref
end
