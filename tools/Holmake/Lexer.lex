{
open Parser

(* For nesting comments *)

val comment_depth = ref 0;

(* The table of keywords *)
val keyword_table =
    (Polyhash.mkPolyTable(53, Subscript) : (string,token) Polyhash.hash_table);

val () =
    List.app (Polyhash.insert keyword_table)
    [
     ("abstype",    NULL),
     ("and",        NULL),
     ("andalso",    NULL),
     ("as",         NULL),
     ("case",       NULL),
     ("datatype",   NULL),
     ("do",         NULL),
     ("else",       NULL),
     ("eqtype",     NULL),
     ("end",        NULL),
     ("exception",  NULL),
     ("fn",         NULL),
     ("fun",        NULL),
     ("handle",     NULL),
     ("if",         NULL),
     ("in",         NULL),
     ("include",    INCLUDE),
     ("infix",      NULL),
     ("infixr",     NULL),
     ("let",        NULL),
     ("local",      NULL),
     ("nonfix",     NULL),
     ("of",         NULL),
     ("op",         NULL),
     ("open",       OPEN),
     ("orelse",     NULL),
     ("prim_eqtype",  NULL),
     ("prim_EQtype",  NULL),
     ("prim_type",    NULL),
     ("prim_val",     NULL),
     ("raise",      NULL),
     ("rec",        NULL),
     ("then",       NULL),
     ("type",       NULL),
     ("val",        NULL),
     ("while",      NULL),
     ("with",       NULL),
     ("withtype",   NULL),
     ("#",          NULL),
     ("->",         NULL),
     ("|",          NULL),
     (":",          NULL),
     ("=>",         NULL),
     ("=",          NULL),
     ("*",          NULL)
     ];

fun mkKeyword lexbuf =
  let val s = getLexeme lexbuf in
    Polyhash.find keyword_table s
    handle Subscript => ID s
  end
;

val savedLexemeStart = ref 0;
exception LexicalError of string * int * int (* (message, loc1, loc2) *)

fun getQual s =
  let open CharVector
      val len' = size s - 1
      fun parse n =
        if sub(s, n) = #"." then
	    String.extract(s, 0, SOME n)
        else
	    parse (n+1)
  in parse 0 end;

fun mkQualId lexbuf =
  QUAL_ID (getQual(getLexeme lexbuf));

fun lexError msg lexbuf =
  raise LexicalError (msg, getLexemeStart lexbuf, getLexemeEnd lexbuf)


fun incr r = (r := !r + 1);
fun decr r = (r := !r - 1);

}

rule Token = parse
    [^ `\000`-`\255`]
      { lexError "this will be never called!" lexbuf }
  | ""
      {TokenN lexbuf}
and TokenN = parse
    [` ` `\n` `\r` `\t`]  { TokenN lexbuf }
  | "(*"
      { savedLexemeStart := getLexemeStart lexbuf;
        comment_depth := 1; Comment lexbuf; TokenN lexbuf
      }
  | "*)"
      { lexError "unmatched comment bracket" lexbuf }
  | "'" [ `A`-`Z` `a`-`z` `0`-`9` `_` `'`]+
                { NULL }
  | "~"? [`0`-`9`]+ (`.` [`0`-`9`]+)? (`E` `~`? [`0`-`9`]+)?
                { NULL }
  | "\""
      { String lexbuf }
  | "#\""
      { String lexbuf }
  | "_"         { NULL }
  | ","         { NULL }
  | "..."       { NULL }
  | "{"         { NULL }
  | "}"         { NULL }
  | "["         { NULL }
  | "#["        { NULL }
  | "]"         { NULL }
  | "("		{ NULL }
  | ")"		{ NULL }
  | ";"         { NULL }
  | (eof | `\^Z`) { EOF }
  | "``"        { DQuotation lexbuf }
  | `\``        { Quotation lexbuf }
  | ""          { TokenId lexbuf }

and TokenId = parse
    ( [`A`-`Z` `a`-`z`] [ `A`-`Z` `a`-`z` `0`-`9` `_` `'`]*
    | [`!` `%` `&` `$` `#` `+` `-` `/` `:` `<` `=` `>` `?` `@` `\\`
       `~` `^` `|` `*`]+ )
      { mkKeyword lexbuf }
  | ( [`A`-`Z` `a`-`z`] [ `A`-`Z` `a`-`z` `0`-`9` `_` `'`]*
    | [`!` `%` `&` `$` `#` `+` `-` `/` `:` `<` `=` `>` `?` `@` `\\`
       `~` `^` `|` `*`]+ )
    "."
    ( [`A`-`Z` `a`-`z`] [ `A`-`Z` `a`-`z` `0`-`9` `_` `'` `.`]*
    | [`!` `%` `&` `$` `#` `+` `-` `/` `:` `<` `=` `>` `?` `@` `\\`
       `~` `^` `|` `*` `.`]+ )
      { mkQualId lexbuf }
  | _
      { lexError "ill-formed token" lexbuf }

and Comment = parse
    "(*"
      { (incr comment_depth; Comment lexbuf) }
  | "*)"
      { (decr comment_depth;
         if !comment_depth > 0 then Comment lexbuf else NULL) }
  | (eof | `\^Z`)
      { EOF }
  | _
      { Comment lexbuf }

and String = parse
    `"`
      { NULL }
  | `\\` [`\\` `"` `n` `t`]
      { String lexbuf }
  | `\\` [` ` `\t` `\n` `\r`]+ `\\`
      { String lexbuf }
  | `\\` `^` [`@`-`_`]
      { String lexbuf }
  | `\\` [`0`-`9`] [`0`-`9`] [`0`-`9`]
      { String lexbuf }
  | `\\`
      { SkipString lexbuf }
  | (eof | `\^Z`)
      { EOF }
  | [`\^A`-`\^Z` `\127` `\255`]
      { SkipString lexbuf }
  | _
      { String lexbuf }

and SkipString = parse
    `"`
      { NULL }
  | `\\` [`\\` `"` `n` `t`]
      { SkipString lexbuf }
  | `\\` [` ` `\t` `\n` `\r`]+ `\\`
      { SkipString lexbuf }
  | (eof | `\^Z`)
      { EOF }
  | _
      { SkipString lexbuf }

and Quotation = parse
    "`" { NULL }
  | (eof | `\^Z`) { EOF }
  | "^`" { Quotation lexbuf }
  | _ { Quotation lexbuf }
and DQuotation = parse
    "``" { NULL }
  | (eof | `\^Z`) { EOF }
  | "^`" { Quotation lexbuf }
  | _ {DQuotation lexbuf }

;
