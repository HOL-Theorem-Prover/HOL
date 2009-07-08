type pos = (int * int);
type arg = int;
open Tokens;
type lexresult  = (svalue,pos) token
exception Impossible of string;
fun fatalError s = raise(Impossible s);

fun mkTok f text pos line =
  (f text, (pos - String.size text, line), (pos, line));

fun mkMtTok text pos line =
  ((pos - String.size text, line), (pos, line));



(* To translate escape sequences *)

(* No problem that this isn't correct for Macintosh *)
val char_for_backslash = fn
(* *)    #"n" => #"\010"
(* *)  | #"r" => #"\013"
(* *)  | #"a" => #"\007"
(* *)  | #"b" => #"\008"
(* *)  | #"t" => #"\009"
(* *)  | #"v" => #"\011"
(* *)  | #"f" => #"\012"
(* *)  | c => c
;

(* The table of keywords *)

val keyword_table =
List.foldl (fn ((str, tok), t) => Binarymap.insert (t, str, tok))
(Binarymap.mkDict String.compare)
[
  ("abstype",      ABSTYPE),
  ("and",          AND),
  ("andalso",      ANDALSO),
  ("as",           AS),
  ("case",         CASE),
  ("datatype",     DATATYPE),
  ("do",           DO),
  ("else",         ELSE),
  ("eqtype",       EQTYPE),
  ("end",          END),
  ("exception",    EXCEPTION),
  ("fn",           FN),
  ("fun",          FUN),
  ("handle",       HANDLE),
  ("if",           IF),
  ("in",           IN),
  ("include",      INCLUDE),
  ("infix",        INFIX),
  ("infixr",       INFIXR),
  ("let",          LET),
  ("local",        LOCAL),
  ("nonfix",       NONFIX),
  ("of",           OF),
  ("op",           OP),
  ("open",         OPEN),
  ("orelse",       ORELSE),
  ("prim_eqtype",  PRIM_EQTYPE),
  ("prim_EQtype",  PRIM_REFTYPE),
  ("prim_type",    PRIM_TYPE),
  ("prim_val",     PRIM_VAL),
  ("raise",        RAISE),
  ("rec",          REC),
  ("sig",          SIG),
  ("signature",    SIGNATURE),
  ("struct",       STRUCT),
  ("structure",    STRUCTURE),
  ("then",         THEN),
  ("type",         TYPE),
  ("val",          VAL),
  ("while",        WHILE),
  ("where",        WHERE),
  ("with",         WITH),
  ("withtype",     WITHTYPE),
  ("#",            HASH),
  ("->",           ARROW),
  ("|",            BAR),
  (":",            COLON),
  ("=>",           DARROW),
  ("=",            EQUALS),
  ("*",            STAR)
];
(*
local (* Make sure that strings are shared (interned); this saves space
         when writing to disk: *)
    val intern_table = (Hasht.new 123 : (string, string) Hasht.t);
in
    fun share s =
       case Hasht.peek intern_table s of
           NONE    => (Hasht.insert intern_table s s; s)
         | SOME s' => s'
end
*)
fun share s = s;

fun mkKeyword text pos line =
  (Binarymap.find (keyword_table, text)) (mkMtTok text pos line)
  handle Binarymap.NotFound => ID (mkTok share text pos line);

val savedLexemeStart = ref 0;

fun splitQualId s =
  let open CharVector
      val len' = size s - 1
      fun parse n =
        if n = 0 then
          ("", s)
        else if sub(s, n) = #"." then
          ( String.extract(s, 0, SOME n),
            String.extract(s, n + 1, SOME(len' - n)) )
        else
          parse (n-1)
  in parse len' end;

fun mkQualId text pos line =
  let val (qual, id) = splitQualId text in
    if id = "*" then
      QUAL_STAR (mkTok (fn x => { qual=qual, id=id }) text pos line)
    else
      QUAL_ID (mkTok (fn x => { qual=qual, id=id }) text pos line)
  end
;

exception LexicalError of string * string * int (* (message, loc1, loc2) *)
fun lexError msg text pos line =
  raise (LexicalError (msg, text, line))

fun eof commentDepth =
  if not (commentDepth = 0) then
    lexError "Unclosed comment" "" ~1 (!savedLexemeStart)
  else
    EOF ((~1, ~1), (~1, ~1));

fun constTooLarge msg yytext yypos yylineno =
(
  lexError (msg ^ " constant is too large") yytext yypos yylineno
);

fun string_of_string s =
  case String.fromString (String.substring (s, 1, String.size s - 2)) of
    NONE => raise Fail ""
  | SOME s => s;

fun char_of_string s =
  case Char.fromString (String.substring (s, 2, String.size s - 3)) of
    NONE => raise Fail ""
  | SOME s => s;

fun int_of_string s =
  case StringCvt.scanString (Int.scan StringCvt.DEC) s of
    NONE => raise Fail ""
  | SOME i => i;

fun hex_of_string s =
  case StringCvt.scanString (Int.scan StringCvt.HEX) s of
    NONE => raise Fail ""
  | SOME i => i;

fun word_of_string s =
  case StringCvt.scanString (Word.scan StringCvt.DEC) s of
    NONE => raise Fail ""
  | SOME i => i;

fun word_of_hexstring s =
  case StringCvt.scanString (Word.scan StringCvt.HEX) s of
    NONE => raise Fail ""
  | SOME i => i;

fun real_of_string s =
  case Real.fromString s of
    NONE => raise Fail ""
  | SOME r => r;

%%
%header (functor SMLLexFun(structure Tokens : SML_TOKENS));
%s Comment;
%full
%arg (commentDepth);
%count
id=[A-Za-z][A-Za-z0-9_']* | [-!%&$#+/:<=>?@~^|*\\]+;
stringchar=(\\["abtnvfr\\])|(\\[ \t\n\r]+\\)|(\\\^[@-_])|(\\[0-9][0-9][0-9])|[^\\\n\r\127\255\001-\026];

%%
<INITIAL>[\ \t\n]+ =>
  ( continue () );
<INITIAL>"(*" =>
  ( (savedLexemeStart:=(!yylineno); YYBEGIN Comment; lex 1 ()) );
<INITIAL>"*)" =>
  ( lexError "unmatched comment bracket" yytext yypos (!yylineno) );
<INITIAL>'[A-Za-z0-9_']+ =>
  ( TYVAR (mkTok (fn x => x) yytext yypos (!yylineno)) );
<INITIAL>0 =>
  ( ZDIGIT (mkTok (fn x => 0) yytext yypos (!yylineno)) );
<INITIAL>[1-9] =>
  ( NZDIGIT (mkTok int_of_string yytext yypos (!yylineno)) );
<INITIAL>0[0-9]+ =>
  ( ZPOSINT2 (mkTok int_of_string yytext yypos (!yylineno))
     handle Fail _ => constTooLarge "integer" yytext yypos (!yylineno) );
<INITIAL>[1-9][0-9]+ =>
  ( NZPOSINT2 (mkTok int_of_string yytext yypos (!yylineno))
     handle Fail _ => constTooLarge "integer" yytext yypos (!yylineno) );
<INITIAL>~[0-9]+ =>
  ( NEGINT (mkTok int_of_string yytext yypos (!yylineno))
     handle Fail _ => constTooLarge "integer" yytext yypos (!yylineno) );
<INITIAL>~?0x[0-9a-fA-F]+ =>
  ( NEGINT (mkTok hex_of_string yytext yypos (!yylineno))
     handle Fail _ => constTooLarge "integer" yytext yypos (!yylineno) );
<INITIAL>0w[0-9]+ =>
  ( WORD (mkTok word_of_string yytext yypos (!yylineno))
     handle Fail _ => constTooLarge "word" yytext yypos (!yylineno) );
<INITIAL>0wx[0-9a-fA-F]+ =>
  ( WORD (mkTok word_of_hexstring yytext yypos (!yylineno))
     handle Fail _ => constTooLarge "word" yytext yypos (!yylineno) );
<INITIAL>~?[0-9]+(\.[0-9]+)?([eE]~?[0-9]+)? =>
  ( REAL (mkTok real_of_string yytext yypos (!yylineno))
     handle Fail _ => constTooLarge "real" yytext yypos (!yylineno) );
<INITIAL>"{stringchar}*" =>
  ( STRING (mkTok string_of_string yytext yypos (!yylineno)) );
<INITIAL>#"{stringchar}" =>
  ( CHAR (mkTok char_of_string yytext yypos (!yylineno)) );
<INITIAL>_ =>
  ( UNDERBAR (mkMtTok yytext yypos (!yylineno)) );
<INITIAL>, =>
  ( COMMA (mkMtTok yytext yypos (!yylineno)) );
<INITIAL>\.\.\. =>
  ( DOTDOTDOT (mkMtTok yytext yypos (!yylineno)) );
<INITIAL>\{ =>
  ( LBRACE (mkMtTok yytext yypos (!yylineno)) );
<INITIAL>} =>
  ( RBRACE (mkMtTok yytext yypos (!yylineno)) );
<INITIAL>\[ =>
  ( LBRACKET (mkMtTok yytext yypos (!yylineno)) );
<INITIAL>#\[ =>
  ( HASHLBRACKET (mkMtTok yytext yypos (!yylineno)) );
<INITIAL>] =>
  ( RBRACKET (mkMtTok yytext yypos (!yylineno)) );
<INITIAL>\( =>
  ( LPAREN (mkMtTok yytext yypos (!yylineno)) );
<INITIAL>\) =>
  ( RPAREN (mkMtTok yytext yypos (!yylineno)) );
<INITIAL>\; =>
  ( SEMICOLON (mkMtTok yytext yypos (!yylineno)) );
<INITIAL>{id} =>
  ( mkKeyword yytext yypos (!yylineno) );
<INITIAL>({id}\.)+{id} =>
  ( mkQualId yytext yypos (!yylineno) );
<INITIAL>. =>
  ( lexError "ill-formed token" yytext yypos (!yylineno) );

<Comment>"(*" =>
  ( (lex (commentDepth + 1) ()) );
<Comment>"*)" =>
  ( (if commentDepth = 1 then YYBEGIN INITIAL else ()); lex (commentDepth - 1) ());
<Comment>[^*()]+ =>
  ( continue () );
<Comment>. =>
  ( continue () );

