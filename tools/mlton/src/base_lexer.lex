{
  structure base_lexer =
  struct

  open LexBuffer base_tokens locn

  datatype ('a,'b,'c) lextype =
    Base_token of 'a
  | String of 'b
  | Comment of 'c;

  fun magic x = x;

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
           parser () st)
      end


(* MOVE FROM HERE TO THE END OF THE FILE! *)

val base_token = fn lexbuf => fn st =>
  (fn Base_token x => x)
  (base_token lexbuf st (Base_token ()));

val comment = fn lexbuf => fn st => fn n =>
  (fn Comment x => x)
  (comment lexbuf st (Comment n));

end

(* MOVE UP TO HERE TO THE END OF THE FILE! *)

}

let alpha = [ `A` - `Z` `a` - `z` `_` `'` ]
let numeric = [ `0` - `9` ]

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

   ident `$` (anysymb|numeric+)  { fn st => fn Base_token () =>
     let val l = String.tokens (fn c => c = #"$") (getLexeme ())
     in Base_token (BT_QIdent (hd l, hd (tl l)),getLoc st lexbuf)
     end }
 | locpragma { dolocpragma base_token lexbuf } (* must come before paren-star *)
 | "(*"  { fn st => fn Base_token () =>
           (fn Comment x => Base_token x) (comment () st (Comment 0)) }
 | numeric+ alpha?  { fn st => fn Base_token () =>
     let val s = getLexeme ()
         val c = String.sub (s, size s - 1)
     in
       if Char.isAlpha c then
         Base_token (BT_Numeral(String.extract(s,0,SOME (size s - 1)), SOME c),
                     getLoc st lexbuf)
       else
         Base_token (BT_Numeral(s, NONE),getLoc st lexbuf)
     end }
 | `$` ? anysymb { fn st => fn Base_token () =>
                   Base_token (BT_Ident (getLexeme ()),getLoc st lexbuf) }
 | "\""  { fn st as ref (nf,r,i,_) => fn Base_token () =>
     let val s = LocP(nf,r,getLexemeStart () - i)
         val String (str,e) = string () st (String [#"\""])
     in
       Base_token (BT_Ident (String.implode (List.rev str)),mkLoc st s e)
     end }
 | space { base_token () }
 | newline { fn st as ref (nf,r,i,rcopt) => fn Base_token () =>
             (st := (nf,r+1,getLexemeEnd (),rcopt);
              base_token () st (Base_token ())) }
 | _     { fn st => fn Base_token () =>
           raise LEX_ERR ("Character \""^getLexeme ()^
                          "\" is a lexical error", getLoc st lexbuf) }
 | eof   { fn st => fn Base_token () => Base_token (BT_EOI,getLoc st lexbuf) }

and string =
   parse

   "\""    { fn st as ref (nf,r,i,_) => fn String acc =>
             String (#"\"" :: acc, LocP(nf,r,getLexemeEnd () - i - 1)) }
 | "\\n"   { fn st => fn String acc => string () st (String (#"\n" :: acc)) }
 | "\\\""  { fn st => fn String acc => string () st (String (#"\"" :: acc)) }
 | "\\\\"  { fn st => fn String acc => string () st (String (#"\\" :: acc)) }
 | "\\r"   { fn st => fn String acc => string () st (String (#"\r" :: acc)) }
 | locpragma { dolocpragma string lexbuf } (* surprising, but I think necessary *)
 | newline { fn st => raise LEX_ERR ("newline inside quote-delimited string",getLoc st lexbuf) }
 | eof     { fn st => raise LEX_ERR ("eof/antiquote inside quote-delimited string",getLoc st lexbuf) }
 | _       { fn st => fn String acc =>
             string () st (String (getLexemeChar 0 :: acc)) }

and comment =
   parse

   "*)"    { fn st => fn Comment n =>
             if n = 0 then
               (fn Base_token x => Comment x)
               (base_token () st (Base_token ()))
             else comment () st (Comment (n - 1)) }
 | eof     { fn st => fn Comment n =>
             Comment (BT_InComment n, getLoc st lexbuf) }
 | locpragma { dolocpragma comment lexbuf } (* must come before paren-star *)
 | "(*"    { fn st => fn Comment n => comment () st (Comment (n + 1)) }
 | newline { fn st as ref (nf,r,i,rcopt) => fn l =>
             (st := (nf,r+1,getLexemeEnd (),rcopt); comment () st l) }
 | _       { comment () }
;

(* Local variables: *)
(* mode: sml *)
(* end: *)
