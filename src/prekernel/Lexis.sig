signature Lexis =
sig
  val alphanumerics         : Word8Array.array
  val hol_symbols           : Word8Array.array
  val sml_symbols           : Word8Array.array
  val alphabet              : Word8Array.array
  val numbers               : Word8Array.array
  val tyvar_ids             : Word8Array.array
  val parens                : Word8Array.array
  val in_class              : Word8Array.array * int -> bool

  val allowed_user_type_var : string -> bool
  val allowed_type_constant : string -> bool
  val allowed_term_constant : string -> bool
  val ok_identifier         : string -> bool
  val ok_symbolic           : string -> bool
  val ok_sml_identifier     : string -> bool
  val is_num_literal        : string -> bool
  val is_string_literal     : string -> bool
  val is_char_literal       : string -> bool

  val nameStrm              : string -> unit -> string
  val tyvar_vary            : string -> string
  val tmvar_vary            : string -> string
  val gen_variant           : (string -> string)
                                -> string list -> string -> string
end;
