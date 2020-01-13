(* this is an -*- sml-lex -*- file *)
structure Tokens = Tokens
type pos = int

type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b)Tokens.token
type lexresult = (svalue,pos) token

val pos = ref 1
fun eof _ = Tokens.EOF(!pos,!pos)
type arg = string list ref

%%
%header (functor HOLsexpLexFun(structure Tokens : HOLsexp_TOKENS));
%full
%s string comment quotedsymbol;
%arg (stringbuffer : string list ref);
digit=[0-9];
integer={digit}+;
space = [\ \t];
%%
<INITIAL>";" => (YYBEGIN comment; continue());
<INITIAL>"(" => (Tokens.LPAREN(!pos, !pos));
<INITIAL>")" => (Tokens.RPAREN(!pos, !pos));
<INITIAL>{space}+ => (continue());
<INITIAL>"\n" => (continue());
<INITIAL>[-+]?{integer} =>
   (Tokens.NUMBER(valOf (Int.fromString yytext), !pos, !pos));
<INITIAL>"'" => (Tokens.QUOTE(!pos,!pos));
<INITIAL>"." => (Tokens.DOT(!pos,!pos));
<INITIAL>"|" => (YYBEGIN quotedsymbol; stringbuffer := []; continue());
<INITIAL>[-%+*_A-Za-z0-9]+ => (Tokens.SYMBOL(yytext, !pos, !pos));
<INITIAL>"\"" => (YYBEGIN string; stringbuffer := []; continue());
<INITIAL>. => (raise Fail ("Unexpected: "^yytext));

<quotedsymbol>"|" => (YYBEGIN INITIAL;
                      Tokens.SYMBOL(String.concat (List.rev(!stringbuffer)),
                                    !pos, !pos));
<quotedsymbol>"\\|" => (stringbuffer := "|" :: !stringbuffer; continue());
<quotedsymbol>"\\n" => (stringbuffer := "\n" :: !stringbuffer; continue());
<quotedsymbol>[^\\|]+ => (stringbuffer := yytext :: !stringbuffer; continue());
<quotedsymbol>\n => (raise Fail "Newline inside |-quoted-symbol");

<string>"\"" => (YYBEGIN INITIAL;
                 Tokens.STRING(String.concat (List.rev(!stringbuffer)),
                               !pos, !pos));
<string>"\\\"" => (stringbuffer := "\"" :: !stringbuffer; continue());
<string>"\\a" => (stringbuffer := "\a" :: !stringbuffer; continue());
<string>"\\b" => (stringbuffer := "\b" :: !stringbuffer; continue());
<string>"\\f" => (stringbuffer := "\f" :: !stringbuffer; continue());
<string>"\\n" => (stringbuffer := "\n" :: !stringbuffer; continue());
<string>"\\r" => (stringbuffer := "\r" :: !stringbuffer; continue());
<string>"\\t" => (stringbuffer := "\t" :: !stringbuffer; continue());
<string>[^\"\\]+ => (stringbuffer := yytext :: !stringbuffer; continue());
<string>\n => (raise Fail "Newline inside string literal");
<string>"\\"[0-9][0-9][0-9] => (
  let
    val code = valOf (Int.fromString (String.substring(yytext, 1, 3)))
  in
    stringbuffer := str (Char.chr code) :: !stringbuffer; continue()
  end
);
<string>"\\^" [\064-\095] => (
  let
    val code = Char.ord (String.sub(yytext, 2)) - 64
  in
    stringbuffer := str (Char.chr code) :: !stringbuffer ; continue()
  end
);
<string>. => (raise Fail ("Can't cope with character "^yytext^
                          " inside string literal"));

<comment>\n => (YYBEGIN INITIAL; continue());
<comment>. => (continue());
