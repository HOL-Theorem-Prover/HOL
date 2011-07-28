signature base_tokens =
sig

  exception LEX_ERR of string * locn.locn

  datatype 'a base_token =
    BT_Ident of string
  | BT_Numeral of (Arbnum.num * char option)
  | BT_DecimalFraction of {wholepart: Arbnum.num, fracpart: Arbnum.num,
                            places : int}
  | BT_AQ of 'a
  | BT_EOI

  val toString : 'a base_token -> string

  val allow_octal_input : bool ref
  val preferred_output_base : StringCvt.radix ref

  val parse_numeric_literal : string * locn.locn -> Arbnum.num * char option

end

