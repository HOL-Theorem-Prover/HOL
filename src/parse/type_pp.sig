signature type_pp =
sig

 val pp_type : type_grammar.grammar -> PPBackEnd.t -> bool ->
               Portable.ppstream -> Type.hol_type -> unit
 val pp_type_with_depth : type_grammar.grammar -> PPBackEnd.t -> bool ->
                          Portable.ppstream -> int -> Type.hol_type -> unit
 val pp_type_cont :
               type_grammar.grammar -> PPBackEnd.t -> bool ->
               Portable.ppstream -> Type.hol_type -> unit
 val pp_type_with_depth_cont :
               type_grammar.grammar -> PPBackEnd.t -> bool ->
               Portable.ppstream -> int -> Type.hol_type -> unit

 val pp_num_types   : bool ref
 val pp_array_types : bool ref

 val ftyvars_seen : Type.hol_type list ref
 val btyvars_seen : Type.hol_type list ref
end
