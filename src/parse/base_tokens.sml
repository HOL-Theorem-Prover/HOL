structure base_tokens :> base_tokens =
struct

exception LEX_ERR of string * locn.locn

datatype 'a base_token =
         BT_Ident of string
       | BT_Numeral of (Arbnum.num * char option)
       | BT_QIdent of (string * string)
       | BT_AQ of 'a
       | BT_EOI
       | BT_InComment of int

val allow_octal_input = ref false
val preferred_output_base = ref StringCvt.DEC


fun toString (BT_Ident s) = s
  | toString (BT_Numeral(s, copt)) = Arbnum.toString s ^
                                     (case copt of SOME c => String.str c
                                                 | NONE => "")
  | toString (BT_QIdent(s1, s2)) = s1 ^ "$" ^ s2
  | toString (BT_AQ x) = "<AntiQuote>"
  | toString BT_EOI = "<End of Input>"
  | toString (BT_InComment n) = "<In Comment, depth "^Int.toString(n + 1)^">"

fun check_binary (s, loc) = let
  open Substring
  fun check ss =
      case getc ss of
        NONE => s
      | SOME (c, ss) => if c = #"0" orelse c = #"1" then check ss
                        else raise LEX_ERR ("Illegal binary literal", loc)
in
  check (all s)
end

fun check_octal (s, loc) = let
  open Substring
  fun check ss =
      case getc ss of
        NONE => s
      | SOME (c, ss) => if c = #"8" orelse c = #"9" then
                          raise LEX_ERR ("Illegal octal literal", loc)
                        else check ss
in
  check (all s)
end

fun strip_underscores s =
    String.translate (fn #"_" => "" | c => str c) s

fun parse_numeric_literal (s,locn) =
    if String.sub(s, 0) <> #"0" orelse size s = 1 then
      Arbnum.fromString (strip_underscores s)
    else let
        val c = String.sub(s, 1)
      in
        case c of
          #"x" => Arbnum.fromHexString
                    (strip_underscores (String.extract(s,2,NONE)))
        | #"b" => Arbnum.fromBinString
                    (check_binary
                       (strip_underscores (String.extract(s,2,NONE)), locn))
        | _ => if !allow_octal_input then
                 Arbnum.fromOctString (check_octal (strip_underscores s, locn))
               else Arbnum.fromString (strip_underscores s)
      end


end; (* struct *)
