{
 open Lexing;;
 open Hh_parse;;
}

let white = [' ' '\t']
let newline = ['\r' '\n']
let letter = ['a'-'z' 'A'-'Z' '0'-'9' '_']

rule hh2lex = parse
| '%' [^'\n' '\r']*  {hh2lex lexbuf}
| white+             {hh2lex lexbuf}
| newline            {let pos = lexbuf.Lexing.lex_curr_p in
                      lexbuf.Lexing.lex_curr_p <- { pos with
                        Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
                        Lexing.pos_bol = pos.Lexing.pos_cnum;
                      };
                      hh2lex lexbuf} (*...*)
| eof                {TokEof}
| '('                {TokParO}
| ')'                {TokParC}
| '.'                {TokDot}
| ','                {TokComma}
| '!' white* '['     {TokQUni}
| '!' '>' white* '[' {TokQUni}
| '?' white* '['     {TokQExi}
| '^' white* '['     {TokLam}
| ']' white* ':'     {TokSqrC}
| "!="               {TokNEq}
| '~'                {TokTilde}
| "<=>"              {TokEqvt}
| "<~>"              {TokNEqvt}
| "=>"               {TokImpl}
| '='                {TokEq}
| '&'                {TokAnd}
| '|'                {TokOr}
| ':'                {TokColon}
| '>'                {TokFun}
| '@'                {TokAt}
| '\''               {TokWord ("'" ^ lex_squot lexbuf ^ "'")}
| letter+             {TokWord (Lexing.lexeme lexbuf)}
| '$' letter+         {TokWord (Lexing.lexeme lexbuf)}
(*| [^'\n' '\r']+     {TokUnknown (Lexing.lexeme lexbuf)}*)

and lex_squot = parse
| '\''               {""}
| '\\' '\''          {"\\'" ^ lex_squot lexbuf}
| [^ '\'' '\\']+     {let s = Lexing.lexeme lexbuf in s ^ lex_squot lexbuf}

{
}
