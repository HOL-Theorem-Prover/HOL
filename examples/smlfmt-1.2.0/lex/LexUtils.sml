(** Copyright (c) 2020-2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure LexUtils =
struct

  val isValidFormatEscapeChar = Char.contains " \t\n\f\r"

  val isValidSingleEscapeChar = Char.contains "abtnvfr\\\""

  fun isValidControlEscapeChar c =
    64 <= Char.ord c andalso Char.ord c <= 95

  val isSymbolic = Char.contains "!%&$#+-/:<=>?@\\~`^|*"

  fun isDecDigit c = Char.isDigit c

  fun isHexDigit c = Char.isHexDigit c

  fun isLetter c = Char.isAlpha c

  fun isAlphaNumPrimeOrUnderscore c =
    Char.isAlphaNum c orelse c = #"_" orelse c = #"'"

  val isOtherPathChar = Char.contains "$()_-./"

  fun isValidUnquotedPathChar c = Char.isAlphaNum c orelse isOtherPathChar c

end
