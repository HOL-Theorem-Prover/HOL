(* The lexical analyzer for lexer definitions. Bootstrapped! *)

{
structure Scanner:SCANNER =
struct
open LexBuffer LexError

open Fnlib Syntax Token Scan_aux
}

{
end
}

{}

rule main = parse
    [` ` `\n` `\r` `\t` ] +
    { main () }
  | "(*"
    { (comment_depth := 1; comment (); main ()) }
  | "*)"
      { raise Lexical_error "unmatched comment bracket" }
  | [`A`-`Z` `a`-`z`] ( [ `A`-`Z` `a`-`z` `0`-`9` `_` `'`] )*
    { case getLexeme () of
        "rule"  => Trule
      | "parse" => Tparse
      | "and"   => Tand
      | "eof"   => Teof
      | "let"   => Tlet
      | s       => Tident s }
  | `"`
    { (reset_string_buffer();
       string ();
       Tstring(get_stored_string())) }
  | "`"
    { char () }
  | `{`
    { let val n1 = getLexemeEnd ()
          val () = brace_depth := 1
          val Taction1 n2 = action ()
      in Taction(Location(LexBuffer.substring(lexbuf,n1,n2-n1))) end }
  | `=`  { Tequal }
  | ";"  { Tend }
  | `|`  { Tor }
  | `_`  { Tunderscore }
  | "eof"  { Teof }
  | `[`  { Tlbracket }
  | `]`  { Trbracket }
  | `*`  { Tstar }
  | `?`  { Tmaybe }
  | `+`  { Tplus }
  | `(`  { Tlparen }
  | `)`  { Trparen }
  | `^`  { Tcaret }
  | `-`  { Tdash }
  | (eof | `\026`)
    { raise Lexical_error "unterminated lexer definition" }
  | _
    { raise Lexical_error
             ("illegal character #" ^ (getLexeme ())) }

and action = parse
    `{`
        { (incr brace_depth; action ()) }
  | `}`
        { (decr brace_depth;
           if !brace_depth = 0 then
             Taction1 (getLexemeStart ())
           else
             action ()) }
  | `"`
    { (reset_string_buffer();
       string ();
       reset_string_buffer();
       action ()) }
  | "(*"
    { (comment_depth := 1; comment (); action ()) }
  | "*)"
      { raise Lexical_error "unmatched comment bracket" }
  | (eof | `\026`)
    { raise Lexical_error "unterminated action" }
  | _
    { action () }

and string = parse
    `"`
    { Tend }
  | `\\` [` ` `\t` `\n` `\r`]+ `\\`
      { string () }
  | `\\` [`\\` `"` `n` `t` `b` `r`]
    { (store_string_char(char_for_backslash(getLexemeChar 1));
       string ()) }
  | `\\` `^` [`@`-`_`]
      { (store_string_char(
           Char.chr(Char.ord(getLexemeChar 2) - 64));
         string ()) }
  | `\\` [`0`-`9`] [`0`-`9`] [`0`-`9`]
    { let val code = char_for_decimal_code lexbuf 1 in
        if Char.ord code >= 256 then
          raise Lexical_error "character code in string > 255"
        else ();
        store_string_char code;
        string ()
      end }
  | `\\`
      { raise Lexical_error "ill-formed escape sequence in string" }
  | (eof | `\026`)
    { raise Lexical_error "unterminated string" }
  | [`\001`-`\031` `\127` `\255`]
      { raise Lexical_error "invalid character in string" }
  | _
    { (store_string_char(getLexemeChar 0);
       string ()) }

and char = parse
    `\\` [`\\` `\`` `n` `t` `b` `r`] "`"
    { Tchar (char_for_backslash (getLexemeChar 1)) }
  | `\\` `^` [`@`-`_`] "`"
      { Tchar (Char.chr(Char.ord(getLexemeChar 2) - 64)) }
  | `\\` [`0`-`9`] [`0`-`9`] [`0`-`9`] "`"
    { let val code = char_for_decimal_code lexbuf 1 in
        if Char.ord code >= 256 then
          raise Lexical_error "character code in string > 255"
        else ();
        Tchar (code)
      end }
  | `\\`
      { raise Lexical_error "ill-formed escape sequence in character constant" }
  | (eof | `\026`)
    { raise Lexical_error "unterminated character constant" }
  | [`\001`-`\031` `\127` `\255`]
      { raise Lexical_error "invalid character in character constant" }
  | _ "`"
    { Tchar (getLexemeChar 0) }
  | _
    { raise Lexical_error "ill-formed character constant" }

and comment = parse
    "(*"
    { (incr comment_depth; comment ()) }
  | "*)"
    { (decr comment_depth;
       if !comment_depth = 0 then Tend else comment ()) }
  | (eof | `\026`)
    { raise Lexical_error "unterminated comment" }
  | _
    { comment () }
;
