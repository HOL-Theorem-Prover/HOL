(* tokens for Holmakefiles *)
{
  fun fromEscapedString s = let
    fun munge [] = []
      | munge [#"\\"] = raise Fail "no trailing backslashes"
      | munge [c] = [c]
      | munge (#"\\"::c::cs) = c :: munge cs
      | munge (c::cs) = c :: munge cs
  in
    String.implode (munge (String.explode s))
  end
  open Holmake_parse
}

let newline = "\r\n" | `\n` | `\r`
let whitespace = `\r` | `\t` | `\n` | ` `
rule token =
  parse `:` { COLON }
      | `=` { EQUALS }
      | `\t` { TAB }
      | "INCLUDES" { INCLUDES }
      | "PRE_INCLUDES" { PRE_INCLUDES }
      | "OPTIONS"  { OPTIONS }
      | `\\` newline { token lexbuf }
      | newline { NEWLINE }
      | `#`    { comment lexbuf; token lexbuf }
      | ([^ `\\` `\r` `\t` `\n` ` ` `#` `:` `=`] | (`\\` _))+ {
            ID (fromEscapedString (Lexing.getLexeme lexbuf))
        }
      | eof { EOF }
      | ` ` { token lexbuf }
      | _ { raise Fail ("Unexpected character "^Lexing.getLexeme lexbuf) }
and comment =
  parse newline { () }
      | _ { comment lexbuf }

;

(* Local variables: *)
(* mode: sml *)
(* end: *)
