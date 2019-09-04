structure base_tokens_dtype =
struct

  type fracinfo = {wholepart: Arbnum.num, fracpart: Arbnum.num, places : int}

  datatype 'a base_token =
    BT_Ident of string
  | BT_StrLit of {ldelim: string, contents : string}
  | BT_Numeral of (Arbnum.num * char option)
  | BT_DecimalFraction of fracinfo
  | BT_AQ of 'a
  | BT_EOI

end
