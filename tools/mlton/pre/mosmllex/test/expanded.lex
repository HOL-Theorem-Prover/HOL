{ }
{ }
{ }
rule main = parse
    [`0`-`9``A`-`F`]+		{ Tok.INT(getLexeme ())}
  | [`a`-`z``A`-`Z`] ([`a`-`z``A`-`Z`] | [`0`-`9`] | [`_` `'`])* 
				{ Tok.IDENT(getLexeme ())}
;
