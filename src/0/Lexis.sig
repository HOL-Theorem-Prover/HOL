(* ===================================================================== *)
(* FILE          : lexis.sig                                             *)
(* DESCRIPTION   : Signature for functions defining lexical structure    *)
(*                 of hol90 types and terms.                             *)
(*                                                                       *)
(* AUTHOR        : Konrad Slind, University of Calgary                   *)
(* DATE          : August 26, 1991                                       *)
(* Modified      : September 22, 1997, Ken Larsen                        *)
(* ===================================================================== *)


signature Lexis =
sig
  val alphanumerics : Portable_ByteArray.bytearray
  val hol_symbols   : Portable_ByteArray.bytearray
  val sml_symbols   : Portable_ByteArray.bytearray
  val alphabet      : Portable_ByteArray.bytearray
  val numbers       : Portable_ByteArray.bytearray
  val tyvar_ids     : Portable_ByteArray.bytearray
  val parens        : Portable_ByteArray.bytearray

  val in_class      : Portable_ByteArray.bytearray * int -> bool

  val allowed_user_type_var : string -> bool
  val allowed_type_constant : string -> bool
  val allowed_term_constant : string -> bool
  val ok_identifier : string -> bool
  val ok_symbolic : string -> bool
  val ok_sml_identifier : string -> bool
  val is_num_literal : string -> bool
  val is_string_literal : string -> bool
end;
