signature type_pp =
sig

 val pp_type : type_grammar.grammar -> PPBackEnd.t ->
               Portable.ppstream -> Type.hol_type -> unit
 val pp_type_with_depth : type_grammar.grammar -> PPBackEnd.t ->
                          Portable.ppstream -> int -> Type.hol_type -> unit
 val pp_type_cont :
               type_grammar.grammar -> PPBackEnd.t ->
               Portable.ppstream -> Type.hol_type -> unit
 val pp_type_with_depth_cont :
               type_grammar.grammar -> PPBackEnd.t ->
               Portable.ppstream -> int -> Type.hol_type -> unit

 val pp_num_types   : bool ref
 val pp_array_types : bool ref

 val ftyvars_seen : Type.hol_type list ref
 val btyvars_seen : Type.hol_type list ref

 (* Kind antiquotations (required in type parser) *)
 val kd_antiq  : Kind.kind -> Type.hol_type
 val dest_kd_antiq : Type.hol_type -> Kind.kind
 val is_kd_antiq : Type.hol_type -> bool
end
