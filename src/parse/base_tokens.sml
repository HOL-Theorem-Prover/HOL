structure base_tokens :> base_tokens =
struct

exception LEX_ERR of string * locn.locn
type fracinfo = {wholepart: Arbnum.num, fracpart: Arbnum.num, places : int}

datatype 'a base_token =
         BT_Ident of string
       | BT_Numeral of (Arbnum.num * char option)
       | BT_DecimalFraction of fracinfo
       | BT_AQ of 'a
       | BT_EOI

val allow_octal_input = ref false
val preferred_output_base = ref StringCvt.DEC


fun toString (BT_Ident s) = s
  | toString (BT_Numeral(s, copt)) = Arbnum.toString s ^
                                     (case copt of SOME c => String.str c
                                                 | NONE => "")
  | toString (BT_DecimalFraction{wholepart,fracpart,places}) =
      Arbnum.toString wholepart ^ "." ^
      StringCvt.padLeft #"0" places (Arbnum.toString fracpart)
  | toString (BT_AQ x) = "<AntiQuote>"
  | toString BT_EOI = "<End of Input>"

fun check p exnstring (s,loc) = let
  open Substring
  fun check ss =
      case getc ss of
        NONE => s
      | SOME (c,ss) => if p c then check ss
                       else raise LEX_ERR (exnstring ^ ": " ^ s, loc)
in
  check (full s)
end

val check_binary = check (fn c => c = #"0" orelse c = #"1")
                         "Illegal binary literal"
val check_octal = check (fn c => #"0" <= c andalso c <= #"7")
                        "Illegal octal literal"
val check_hex = check (fn c => (#"0" <= c andalso c <= #"9") orelse
                               (let val c' = Char.toLower c
                                in
                                  #"a" <= c' andalso c' <= #"f"
                                end))
                      "Illegal hex literal"
val check_decimal = check Char.isDigit "Illegal numeral"

fun strip_underscores s =
    String.translate (fn #"_" => "" | c => str c) s

fun parse_numeric_literal (s,locn) = let
  val c = String.sub (s, size s - 1)
  val clower = Char.toLower c
  val chexp = #"a" <= clower andalso clower <= #"f"
  val (s,copt) =
      if Char.isAlpha c andalso not (String.isPrefix "0x" s andalso chexp)
      then (String.substring(s,0,size s - 1), SOME c)
      else (s, NONE)
in
  if String.sub(s, 0) <> #"0" orelse size s = 1 then
    (Arbnum.fromString (check_decimal (strip_underscores s, locn)), copt)
  else let
      val c = String.sub(s, 1)
    in
      case c of
        #"x" => (Arbnum.fromHexString
                     (check_hex (strip_underscores (String.extract(s,2,NONE)),
                                 locn)),
                 copt)
      | #"b" => (Arbnum.fromBinString
                     (check_binary
                          (strip_underscores (String.extract(s,2,NONE)), locn)),
                 copt)
      | _ => if !allow_octal_input then
               (Arbnum.fromOctString (check_octal (strip_underscores s, locn)),
                copt)
             else
               (Arbnum.fromString (check_decimal (strip_underscores s, locn)),
                copt)
    end
end

fun parse_fraction (s, loc) =
    case String.fields (Lib.equal #".") s of
      [] => raise Fail ("parse_fraction: impossible: "^s)
    | [_] => raise LEX_ERR ("Decimal fraction with no fractional part: " ^s,
                            loc)
    | [npart, fpart] => let
        val fpart = strip_underscores fpart
      in
        {wholepart = Arbnum.fromString (strip_underscores npart),
         fracpart = Arbnum.fromString fpart,
         places = String.size fpart}
      end
    | _ => raise LEX_ERR ("Decimal fraction with too many decimal points: "^s,
                          loc)


end; (* struct *)
