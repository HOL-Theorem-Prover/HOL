{ open base_tokens locn

  type extrastate = (int * int * int) ref
  (* mutable state argument to each rule is st=(nf,r,i), where:
       - nf  is the number of the fragment being parsed
       - r   is the current row number
       - i   is the index of the first char on the current row
  *)

  fun getLoc (st as ref (nf,r,i)) lexbuf = Loc(LocP(nf,r,getLexemeStart lexbuf - i),
                                               LocP(nf,r,getLexemeEnd lexbuf - i - 1))
  fun newstate nf = ref (nf,0,0)
}

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
let space = [` ` `\t` ]
let newline = "\r\n" | `\n` | `\r`  (* DOS, UNIX, Mac respectively *)

rule base_token =
   parse

   ident `$` anysymb  { fn st =>
     let val l = String.tokens (fn c => c = #"$") (getLexeme lexbuf)
     in (BT_QIdent (hd l, hd (tl l)),getLoc st lexbuf) end }
 | "(*"  { fn st => comment lexbuf st 0 }
 | numeric+ alpha?  { fn st =>
     let val s = getLexeme lexbuf
         val c = String.sub (s, size s - 1)
     in
       if Char.isAlpha c then
         (BT_Numeral(String.extract(s,0,SOME (size s - 1)), SOME c),getLoc st lexbuf)
       else
         (BT_Numeral(s, NONE),getLoc st lexbuf)
     end }
 | `$` ? anysymb { fn st => (BT_Ident (getLexeme lexbuf),getLoc st lexbuf) }
 | "\""  { fn st as ref (nf,r,i) =>
     let val s = LocP(nf,r,getLexemeStart lexbuf - i)
         val (str,e) = string lexbuf st [#"\""]
     in
         (BT_Ident (String.implode (List.rev str)),Loc(s,e))
     end }
 | space { base_token lexbuf }
 | newline { fn st as ref (nf,r,i) => (st := (nf,r+1,getLexemeEnd lexbuf);
                                       base_token lexbuf st) }
 | _     { fn st => raise LEX_ERR ("Character \""^getLexeme lexbuf^
                                   "\" is a lexical error",getLoc st lexbuf) }
 | eof   { fn st => (BT_EOI,getLoc st lexbuf) }

and string =
   parse

   "\""    { fn st as ref (nf,r,i) =>
             fn acc => (#"\""::acc,LocP(nf,r,getLexemeEnd lexbuf - i - 1)) }
 | "\\n"   { fn st => fn acc => string lexbuf st (#"\n"::acc) }
 | "\\\""  { fn st => fn acc => string lexbuf st (#"\""::acc) }
 | "\\\\"  { fn st => fn acc => string lexbuf st (#"\\"::acc) }
 | "\\r"   { fn st => fn acc => string lexbuf st (#"\r"::acc) }
 | newline { fn st => raise LEX_ERR ("newline inside quote-delimited string",getLoc st lexbuf) }
 | eof     { fn st => raise LEX_ERR ("eof/antiquote inside quote-delimited string",getLoc st lexbuf) }
 | _       { fn st => fn acc => string lexbuf st (Lexing.getLexemeChar lexbuf 0::acc) }

and comment =
   parse

   "*)"    { fn st => fn n => if n = 0 then base_token lexbuf st
                        else comment lexbuf st (n - 1) }
 | eof     { fn st => fn n => (BT_InComment n,getLoc st lexbuf) }
 | "(*"    { fn st => fn n => comment lexbuf st (n + 1) }
 | newline { fn st as ref (nf,r,i) => fn n => (st := (nf,r+1,getLexemeEnd lexbuf);
                                               comment lexbuf st n) }
 | _       { comment lexbuf }

;

(* Local variables: *)
(* mode: sml *)
(* end: *)
