(* tokens for Holmakefiles *)
{
  open Holmake_types
}

let newline = "\r\n" | `\n` | `\r`
let whitespace = `\r` | `\t` | `\n` | ` ` | "\\" newline
let nonlws = ([` ` `\t`]|"\\" newline)* (* no newline whitespace *)
let alpha = [ `A` - `Z`  `a` - `z` ]
let number = [`0` - `9`]
let cmdtext = ([^ `\n` `\r` `\\`] | "\\"  _)* (newline | eof)
let rulebody = `\t` cmdtext
let ident = (alpha | number | `_` ) +
let comment = `#` cmdtext
(* text where comments possible, but not including the comments *)
let composs_text = ([^ `\n` `#` `\\` `\r`] | "\\" _ | "\\#")* `\\`?
(* text that actually includes comments, allowing for later processing to
   remove them *)
let include_com_text =
   ([^ `\n` `\r` `#` `\\`] | "\\" _ )* (comment|newline|eof)
let nonspec_char = ([^ `\n` `\r` `:` `#` `\\`] | `\\` _)

rule token =
  parse
    whitespace + { token lexbuf }
  | comment { token lexbuf }
  | ident nonlws `=` composs_text  {
      DEFN (Lexing.getLexeme lexbuf)
    }
  | [^ `\n` `\r` ] * [^ `\\` ] `=` {
      raise Fail ("Bad LHS for variable definition: "^Lexing.getLexeme lexbuf)
    }
  | `=` {
      raise Fail ("Bad LHS for variable definition: "^Lexing.getLexeme lexbuf)
    }
  | nonspec_char+ `:` include_com_text rulebody*
    {
      RULE (Lexing.getLexeme lexbuf)
    }
  | `:` { raise Fail "Rule with no targets" }
  | nonspec_char+ { raise Fail ("Bogus rule start: "^Lexing.getLexeme lexbuf) }
  | eof { EOF }
  | _ { raise Fail ("Didn't expect to see: "^Lexing.getLexeme lexbuf) }

;

(* Local variables: *)
(* mode: sml *)
(* end: *)
