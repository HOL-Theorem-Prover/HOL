{ open base_tokens locn

  type extrastate = (int * int * int * (int * int) option) ref
  (* mutable state argument to each rule is st=(nf,r,i,rcopt), where:
       - nf  is the number of the fragment being parsed
       - r   is the current row number
       - i   is the index of the first char on the current row
       - rcopt is the absolute line and character of the start of this fragment, if known
  *)

  fun mkLoc (st as ref (_,_,_,rcopt)) s e
    = case rcopt of
          NONE => Loc(s,e)
        | SOME(row,col) => Loc(rel_to_abs row col s, rel_to_abs row col e)

  fun getLoc (st as ref (nf,r,i,rcopt)) lexbuf
    = let val s = LocP(nf,r,getLexemeStart lexbuf - i)
          val e = LocP(nf,r,getLexemeEnd lexbuf - i - 1)
      in
          mkLoc st s e
      end

  fun newstate nf = ref (nf,0,0,NONE)

  (* processes location pragmas of the form (*#loc row col*), using
     them to determine the absolute position of fragments in the input
     stream. *)
  fun dolocpragma parser lexbuf (st as ref (nf,r,i,rcopt))
    = let val s = Substring.all (getLexeme lexbuf)
          val sr = Substring.dropl (not o Char.isDigit) s
          val sc = Substring.dropl (Char.isDigit) sr
      in
          (st := (nf,0,getLexemeEnd lexbuf,
                  SOME (valOf (Int.fromString(Substring.string sr)) - 1,
                        valOf (Int.fromString(Substring.string sc)) - 1));
           parser lexbuf st)
      end

}

let alpha = [ `A` - `Z` `a` - `z` `_` `'` ]
let numeric = [ `0` - `9` ]
let digitseq = (numeric | `_`)* numeric (numeric | `_`)*
let hexdigit = [ `A` - `F` `a` - `f` ] | numeric
let hexdigitseq = (hexdigit | `_`)* hexdigit (hexdigit | `_`)*

(* symbol is as one would expect less '(' and '*' to prevent symbols that
   begin with '(''*' to match as symbols.  This sequence can't appear inside
   symbols because of the hideous hack that is separate_out_comments in
   qbuf.sml *)
let symbol = [ `|` `!` `#` `%` `&` `)` `-` `=` `+` `[` `]` `{`
               `}` `;` `:` `@` `~` `\\` `,` `.` `<` `>` `?` `/` ]
let nonparen = symbol | `*`
let nonstar = symbol | `(`
let ident = alpha (alpha | numeric)*
let anysymb = ident | nonparen * `(` | (nonparen | `(` nonstar) +
let space = [` ` `\t` ]
let newline = "\r\n" | `\n` | `\r`  (* DOS, UNIX, Mac respectively *)
let locpragma = "(*#loc" space+ numeric* space+ numeric* space* "*)"

rule base_token =
   parse

   ident `$` (anysymb|numeric+)  { fn st =>
     let val l = String.tokens (fn c => c = #"$") (getLexeme lexbuf)
     in (BT_QIdent (hd l, hd (tl l)),getLoc st lexbuf) end }
 | locpragma { dolocpragma base_token lexbuf } (* must come before paren-star *)
 | "(*"  { fn st => comment lexbuf st 0 }
 | ("0b" digitseq | numeric (numeric | `_`)* | "0x" hexdigitseq ) alpha?  {
     fn st =>
     let val s = getLexeme lexbuf
         val c = String.sub (s, size s - 1)
         val clower = Char.toLower c
         val chexp = #"a" <= clower andalso clower <= #"f"
         val loc = getLoc st lexbuf
     in
       if Char.isAlpha c andalso not (String.isPrefix "0x" s andalso chexp)
       then let
           val s = substring(s,0,size s - 1)
         in
           (BT_Numeral(parse_numeric_literal(s, loc), SOME c), loc)
         end
       else
         (BT_Numeral(parse_numeric_literal(s, loc), NONE), loc)
     end }
 | `$` ? anysymb { fn st => (BT_Ident (getLexeme lexbuf),getLoc st lexbuf) }
 | "\""  { fn st as ref (nf,r,i,_) =>
     let val s = LocP(nf,r,getLexemeStart lexbuf - i)
         val (str,e) = string lexbuf st [#"\""]
     in
         (BT_Ident (String.implode (List.rev str)),mkLoc st s e)
     end }
 | space { base_token lexbuf }
 | newline { fn st as ref (nf,r,i,rcopt) => (st := (nf,r+1,getLexemeEnd lexbuf,rcopt);
                                             base_token lexbuf st) }
 | _     { fn st => raise LEX_ERR ("Character \""^getLexeme lexbuf^
                                   "\" is a lexical error",getLoc st lexbuf) }
 | eof   { fn st => (BT_EOI,getLoc st lexbuf) }

and string =
   parse

   "\""    { fn st as ref (nf,r,i,_) =>
             fn acc => (#"\""::acc,LocP(nf,r,getLexemeEnd lexbuf - i - 1)) }
 | "\\n"   { fn st => fn acc => string lexbuf st (#"\n"::acc) }
 | "\\\""  { fn st => fn acc => string lexbuf st (#"\""::acc) }
 | "\\\\"  { fn st => fn acc => string lexbuf st (#"\\"::acc) }
 | "\\r"   { fn st => fn acc => string lexbuf st (#"\r"::acc) }
 | locpragma { dolocpragma string lexbuf } (* surprising, but I think necessary *)
 | newline { fn st => raise LEX_ERR ("newline inside quote-delimited string",getLoc st lexbuf) }
 | eof     { fn st => raise LEX_ERR ("eof/antiquote inside quote-delimited string",getLoc st lexbuf) }
 | _       { fn st => fn acc => string lexbuf st (Lexing.getLexemeChar lexbuf 0::acc) }

and comment =
   parse

   "*)"    { fn st => fn n => if n = 0 then base_token lexbuf st
                        else comment lexbuf st (n - 1) }
 | eof     { fn st => fn n => (BT_InComment n,getLoc st lexbuf) }
 | locpragma { dolocpragma comment lexbuf } (* must come before paren-star *)
 | "(*"    { fn st => fn n => comment lexbuf st (n + 1) }
 | newline { fn st as ref (nf,r,i,rcopt) => fn n => (st := (nf,r+1,getLexemeEnd lexbuf,rcopt);
                                                     comment lexbuf st n) }
 | _       { comment lexbuf }

;

(* Local variables: *)
(* mode: sml *)
(* end: *)
