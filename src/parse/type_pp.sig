val pp_type : parse_type.grammar -> Portable.ppstream -> Type.hol_type -> unit
val pp_type_with_depth :
  parse_type.grammar -> Portable.ppstream -> int -> Type.hol_type -> unit