{ open Database DBparse
}
rule lextoken =
parse [`0` - `9`]+ { NUM (valOf (Int.fromString (Lexing.getLexeme lexbuf))) }
    | "Str"        { STRUCTURE }
    | "Exc"        { EXCEPTION }
    | "Typ"        { TYPE }
    | "Val"        { VAL }
    | "Con"        { CON }
    | "Term"       { TERM }
    | `;`          { SEMI }
    | `"` [^ `"` ]* `"` { let val s = Lexing.getLexeme lexbuf
                          in
                            STRING (String.substring(s,1,size s - 2))
                          end }
    | eof          { EOF }
    | _            { lextoken lexbuf }

;
