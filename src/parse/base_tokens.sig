signature base_tokens =
sig

  exception LEX_ERR of string * locn.locn

  type fracinfo = base_tokens_dtype.fracinfo
  datatype base_token = datatype base_tokens_dtype.base_token

  val toString : 'a base_token -> string

  val allow_octal_input : bool ref
  val preferred_output_base : StringCvt.radix ref

  val parse_numeric_literal : string * locn.locn -> Arbnum.num * char option
  val parse_fraction : string * locn.locn -> fracinfo

end
