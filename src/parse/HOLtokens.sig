signature HOLtokens =
sig

  type charclass = char -> bool

  val empty : charclass
  val HOLsym : charclass
  val HOLspecials : charclass
  val fromLex : Word8Array.array -> charclass

  val ANDNOT : charclass * charclass -> charclass
  val OR : charclass * charclass -> charclass
  val ITEMS : string -> charclass
  val ITEM : char -> charclass
end
