{ structure Tok =
struct
datatype token = IDENT of string | INT of string
end
 }

{ }

{ }

let letter = [`a`-`z``A`-`Z`]
let digit  = [`0`-`9`]
let ident  = letter (letter | digit | [`_` `'`])*
let digit  = digit | [`A`-`F`]

rule main = parse
    digit+   { Tok.INT(getLexeme ())}
  | ident    { Tok.IDENT(getLexeme ())}
;
