{ open base_tokens }

let alpha = [ `A` - `Z` `a` - `z` `_` `'` ]
let numeric = [ `0` - `9` ]

(* symbol is as one would expect less '(' and '*' to enable handling of
   comments *)
let symbol = [ `|` `!` `#` `%` `&` `)` `-` `=` `+` `[` `]` `{`
               `}` `;` `:` `@` `~` `\\` `,` `.` `<` `>` `?` `/` ]
let nonparen = symbol | `*`
let nonstar = symbol | `(`
let ident = alpha (alpha | numeric)*
let anysymb = ident | nonparen * `(` | (nonparen | `(` nonstar) +
let space = [` ` `\n` `\t` `\r`]

rule base_token =
   parse

   ident `$` anysymb  {
     let val l = String.tokens (fn c => c = #"$") (getLexeme lexbuf)
     in BT_QIdent (hd l, hd (tl l)) end }
 | "(*"  { comment lexbuf 0 }
 | numeric+ alpha?  {
     let val s = getLexeme lexbuf
         val c = String.sub (s, size s - 1)
     in
       if Char.isAlpha c then
         BT_Numeral(String.extract(s,0,SOME (size s - 1)), SOME c)
       else
         BT_Numeral(s, NONE)
     end }
 | `$` ? anysymb { BT_Ident (getLexeme lexbuf) }
 | "\""  { BT_Ident (String.implode (List.rev (string lexbuf [#"\""]))) }
 | space { base_token lexbuf }
 | _     { raise LEX_ERR ("Character \""^getLexeme lexbuf^
                          "\" is a lexical error") }
 | eof   { BT_EOI }

and string =
   parse

   "\""    { fn acc => #"\""::acc }
 | "\\n"   { fn acc => string lexbuf (#"\n"::acc) }
 | "\\\""  { fn acc => string lexbuf (#"\""::acc) }
 | "\\\\"  { fn acc => string lexbuf (#"\\"::acc) }
 | "\\r"   { fn acc => string lexbuf (#"\r"::acc) }
 | `\n`    { raise LEX_ERR "newline inside quote-delimited string" }
 | eof     { raise LEX_ERR "eof/antiquote inside quote-delimited string" }
 | _       { fn acc => string lexbuf (Lexing.getLexemeChar lexbuf 0::acc) }

and comment =
   parse

   "*)"    { fn n => if n = 0 then base_token lexbuf
                     else comment lexbuf (n - 1) }
 | eof     { fn n => BT_InComment n }
 | "(*"    { fn n => comment lexbuf (n + 1) }
 | _       { comment lexbuf }

;

(* Local variables: *)
(* mode: sml *)
(* end: *)
