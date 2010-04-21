type pos = (int * int);
type arg = int;
open Tokens;
type lexresult  = (svalue,pos) token

val linestart_pos = ref 0;

fun mkTok f text pos line =
  (f text, ((pos - !linestart_pos) - String.size text, line), 
            (pos - !linestart_pos, line));

fun mkMtTok text pos line = 
  (((pos - !linestart_pos) - String.size text, line), 
    (pos - !linestart_pos, line));

fun I x = x;
fun eof () = EOF ((~1, ~1), (~1, ~1));


exception LexicalError of string * int * int;
fun lexError msg text pos line =
  (raise (LexicalError (text, pos, line)))


(* The table of keywords *)

val keyword_table =
List.foldl (fn ((str, tok), t) => Binarymap.insert (t, str, tok))
(Binarymap.mkDict String.compare)
[
  ("TERM",      TERM),
  ("@TERM",     TERM),

  ("THEOREM",   THEOREM),
  ("@THEOREM",  THEOREM),
  ("THM",      THEOREM),
  ("@THM",      THEOREM),


  ("TYPE",      TYPE),
  ("@TYPE",     TYPE),

  ("FORCE_INDEX", FORCE_INDEX),
  ("FORCE-INDEX", FORCE_INDEX),
  ("LONG_INDEX" , LONG_INDEX),
  ("LONG-INDEX" , LONG_INDEX),
  ("SHORT_INDEX" , SHORT_INDEX),
  ("SHORT-INDEX" , SHORT_INDEX),

  ("OPTIONS",   OPTIONS),
  ("LABEL",     LABEL),
  ("CONTENT",   CONTENT),
  ("COMMENT",   COMMENT)
];


fun toUpperString s =
   String.translate (fn c => Char.toString(Char.toUpper c)) s

fun mkKeyword text pos line =
  (Binarymap.find (keyword_table, toUpperString text)) (mkMtTok text pos line)
  handle Binarymap.NotFound => IDENT (mkTok I text pos line);


%%
%header (functor HolindexLexFun(structure Tokens : Holindex_TOKENS));
%s Comment;
%count

newline=(\010 | \013 | "\013\010");
blank = [\ | \009 | \012];
letter = [A-Z\_a-z];
digit = [0-9];
alphanum = ({digit} | {letter});
extalphanum = ("." | "-" | ":" | "@" | {digit} | {letter});
ident = {extalphanum}*;
hol_quote = "``" [^ `\``]* "``";
quoted_string = "\"" [^ `\"`]* "\"";


%%


<INITIAL>{newline} => ( ((linestart_pos := yypos); continue ()) );
<INITIAL>{blank} => ( continue () );
<INITIAL>"{" =>
  ( LBRACE (mkMtTok yytext yypos (!yylineno)) );
<INITIAL>"}" =>
  ( RBRACE (mkMtTok yytext yypos (!yylineno)) );
<INITIAL>"=" =>
  ( EQUAL (mkMtTok yytext yypos (!yylineno)) );
<INITIAL>"," =>
  ( COMMA (mkMtTok yytext yypos (!yylineno)) );
<INITIAL>{hol_quote} =>
  ( STRING (mkTok (fn s => (substring (s, 2, (String.size s)-4))) yytext yypos (!yylineno)) );
<INITIAL>{hol_quote} =>
  ( STRING (mkTok (fn s => (substring (s, 2, (String.size s)-4))) yytext yypos (!yylineno)) );
<INITIAL>{quoted_string} =>
  ( STRING (mkTok (fn s => (substring (s, 1, (String.size s)-2))) yytext yypos (!yylineno)) );
<INITIAL>{ident} =>
  ( mkKeyword yytext yypos (!yylineno) );
<INITIAL>. =>
  ( lexError "ill-formed token" yytext yypos (!yylineno) );
