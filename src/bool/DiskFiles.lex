(* User declarations.  This is a -*- sml -*- file *)
structure Tokens = Tokens
type pos = int

type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b)Tokens.token
type lexresult = (svalue,pos) token

val pos = ref 1
fun eof () = Tokens.EOF(!pos,!pos)

%%
%header (functor DiskFilesLexFun(structure Tokens : DiskFiles_TOKENS));
digit=[0-9];
integer={digit}+;
idstring=\" ([^\"\\] | "\\\"" | "\\\\" | "\\n")* \";
%%
\n => (pos := !pos + 1; continue());
[\ \t]+ => (continue());
"$"   => (Tokens.DOLLAR(!pos,!pos));
"."   => (Tokens.FULLSTOP(!pos,!pos));
"\\"   => (Tokens.BACKSLASH(!pos,!pos));
"("   => (Tokens.LPAREN(!pos,!pos));
")"   => (Tokens.RPAREN(!pos,!pos));
"["   => (Tokens.LBRACKET(!pos,!pos));
"]"   => (Tokens.RBRACKET(!pos,!pos));
"TYV"   => (Tokens.TYV(!pos,!pos));
"TYOP"   => (Tokens.TYOP(!pos,!pos));
"TMV"   => (Tokens.TMV(!pos,!pos));
"TMC"   => (Tokens.TMC(!pos,!pos));
"IDS"   => (Tokens.IDS(!pos,!pos));
"TYPES"   => (Tokens.TYPES(!pos,!pos));
"TERMS"   => (Tokens.TERMS(!pos,!pos));
"THEOREMS"   => (Tokens.THEOREMS(!pos,!pos));
{integer} => (Tokens.NUMBER(Option.valOf (Int.fromString yytext),
                            !pos, !pos));
{idstring} => (let val substr = String.substring(yytext,1,size yytext - 2)
               in
                 Tokens.ID(valOf (String.fromString substr), !pos, !pos)
               end);
