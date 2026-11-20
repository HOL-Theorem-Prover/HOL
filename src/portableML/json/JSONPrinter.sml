(* json-printer.sml
 *
 * COPYRIGHT (c) 2008 The Fellowship of SML/NJ (http://www.smlnj.org)
 * All rights reserved.
 *
 * A printer for JSON values.
 *)

structure JSONPrinter =
struct

fun hexDigit n =
    if n < 10 then Char.chr (Char.ord #"0" + n)
    else Char.chr (Char.ord #"a" + n - 10)

fun controlEscape c = let
  val n = Char.ord c
in
  String.implode [#"\\", #"u", hexDigit (n div 4096),
                  hexDigit ((n div 256) mod 16),
                  hexDigit ((n div 16) mod 16), hexDigit (n mod 16)]
end

fun escapeString s = let
  fun escape #"\"" = "\\\""
    | escape #"\\" = "\\\\"
    | escape #"\b" = "\\b"
    | escape #"\f" = "\\f"
    | escape #"\n" = "\\n"
    | escape #"\r" = "\\r"
    | escape #"\t" = "\\t"
    | escape c =
        if Char.ord c < 32 orelse Char.ord c = 127
        then controlEscape c
        else str c
in
  "\"" ^ String.translate escape s ^ "\""
end

fun numberString n =
    String.map (fn #"~" => #"-" | c => c) (IntInf.toString n)

fun floatString f =
    if Real.isFinite f then
      String.map (fn #"~" => #"-" | c => c)
        (Real.fmt (StringCvt.GEN (SOME 17)) f)
    else
      raise Fail "cannot print a non-finite JSON number"

val join = String.concatWith

fun indent n = CharVector.tabulate (2 * n, fn _ => #" ")

fun valueString pretty = let
  fun value level (JSON.OBJECT fields) =
      object level fields
    | value level (JSON.ARRAY values) = array level values
    | value _ JSON.NULL = "null"
    | value _ (JSON.BOOL false) = "false"
    | value _ (JSON.BOOL true) = "true"
    | value _ (JSON.INT n) = numberString n
    | value _ (JSON.FLOAT f) = floatString f
    | value _ (JSON.STRING s) = escapeString s
  and object _ [] = "{}"
    | object level fields =
      if pretty then
        let
          fun field (key, v) =
              indent (level + 1) ^ escapeString key ^ ": " ^
              value (level + 1) v
        in
          "{\n" ^ join ",\n" (map field fields) ^ "\n" ^ indent level ^ "}"
        end
      else
        let
          fun field (key, v) = escapeString key ^ ":" ^ value level v
        in
          "{" ^ join "," (map field fields) ^ "}"
        end
  and array _ [] = "[]"
    | array level values =
      if pretty then
        let
          fun element v = indent (level + 1) ^ value (level + 1) v
        in
          "[\n" ^ join ",\n" (map element values) ^ "\n" ^ indent level ^ "]"
        end
      else
        "[" ^ join "," (map (value level) values) ^ "]"
in
  value 0
end

val valueToString = valueString false

fun print (strm, value) = TextIO.output (strm, valueToString value)

fun printFmt (strm, value) = TextIO.output (strm, valueString true value)

end
