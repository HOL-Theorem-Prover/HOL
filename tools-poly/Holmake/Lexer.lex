type pos = int;
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult  = (svalue,pos) token
open Tokens;

fun eof () = EOF(~1,~1);

(* For nesting comments *)

val comment_depth = ref 0;

(* The table of keywords *)

val keyword_table =
  List.foldl (fn ((k,v), d) => Binarymap.insert (d, k, v))
             (Binarymap.mkDict String.compare)
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

fun mkKeyword s pos =
  (Binarymap.find (keyword_table, s))(pos, pos)
  handle Binarymap.NotFound => ID (s, pos, pos)
;

fun getQual s =
  let val len' = String.size s - 1
      fun parse n =
        if String.sub(s, n) = #"." then
	    String.extract(s, 0, SOME n)
        else
	    parse (n+1)
  in parse 0 end;

fun mkQualId s pos = QUAL_ID (getQual s, pos, pos);

exception LexicalError of string * string * int (* (message, loc1, loc2) *)
fun lexError msg text pos =
  raise (LexicalError (msg, text, pos))


fun incr r = (r := !r + 1);
fun decr r = (r := !r - 1);

%%
%header (functor SimpleSMLLexFun(structure Tokens : SimpleSML_TOKENS));
%s Comment String SkipString Quotation DQuotation;
%full
id=[A-Za-z][A-Za-z0-9_']* | [-!%&$#+/:<=>?@~^|*`\\]+;

%%

<INITIAL>[\ \n\013\t] => 
  ( lex () );
<INITIAL>"(*" =>
  ( (comment_depth := 1; YYBEGIN Comment; lex ()) );
<INITIAL>"*)" =>
  ( lexError "unmatched comment bracket" yytext yypos );
<INITIAL>'[A-Za-z0-9_']+ => 
  ( NULL(yypos,yypos) );
<INITIAL>~?[0-9]+(\.[0-9]+)?(E~?[0-9]+)? => 
  ( NULL(yypos,yypos) );
<INITIAL>["] | #["] =>
  ( (YYBEGIN String; lex ()) );
<INITIAL>[_,{}[();] | "]" | "..." | #\[ =>
  ( NULL(yypos,yypos) );
<INITIAL>`` =>
  ( (YYBEGIN DQuotation; lex ()) );
<INITIAL>` =>
  ( (YYBEGIN Quotation; lex ()) );
<INITIAL>{id} =>
  ( mkKeyword yytext yypos );
<INITIAL>({id}\.)+{id} =>
  ( mkQualId yytext yypos );
<INITIAL>[\000-\255] =>
  ( lexError "ill-formed token" yytext yypos );

<Comment> "(*" => 
  ( (incr comment_depth; lex ()) );
<Comment>"*)" =>
  ( (decr comment_depth;
     if !comment_depth > 0 then lex () else (YYBEGIN INITIAL; lex ())) );
<Comment>[\000-\255] => 
  ( lex () );

<String>\" => 
  ( YYBEGIN INITIAL; NULL(yypos,yypos) );
<String>\\["nt\\] => 
  ( lex () );
<String>\\[\ \t\n\013]+\\ => 
  ( lex () );
<String>\\\^[@-_] => 
  ( lex () );
<String>\\[0-9][0-9][0-9]=> 
  ( lex ());
<String>\\ => 
  ( (YYBEGIN SkipString; lex ()) );
<String>[\001-\026\127] => 
  ( (YYBEGIN SkipString; lex ()) );
<String>[\000-\255] => 
  ( lex () );

<SkipString>\" => 
  ( YYBEGIN INITIAL; NULL(yypos,yypos) );
<SkipString>\\["nt\\] => 
  ( lex () );
<SkipString>\\[\ \t\n\013]+\\ => 
  ( lex () );
<SkipString>[\000-\255] => 
  ( lex () );

<Quotation>` => 
  ( YYBEGIN INITIAL; NULL(yypos,yypos) );
<Quotation>\^` => 
  ( lex () );
<Quotation>[\000-\255] => 
  ( lex () );

<DQuotation>`` => 
  ( YYBEGIN INITIAL; NULL(yypos,yypos) );
<DQuotation>\^` => 
  ( YYBEGIN Quotation; lex () );
<DQuotation>[\000-\255] => 
  ( lex () );
