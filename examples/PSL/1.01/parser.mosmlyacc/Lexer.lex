

(******************************************************************************
Simple lexer for PSL/Sugar properties
(based on examples/lexyacc in mosml distribution)
 ******************************************************************************)


{
 open Lexing Parser;

 exception LexicalError of string * int * int (* (message, loc1, loc2) *)

 fun lexerError lexbuf s =
     raise LexicalError (s, getLexemeStart lexbuf, getLexemeEnd lexbuf);

 val commentStart = ref 0;  (* Start of outermost comment being scanned *)

 fun commentNotClosed lexbuf =
     raise LexicalError ("Comment not terminated",
                         !commentStart, getLexemeEnd lexbuf);

 val commentDepth = ref 0;  (* Current comment nesting *)

 (* Scan keywords as identifiers and use this function to distinguish them. *)
 (* If the set of keywords is large, use an auxiliary hashtable.            *)

 fun keyword s =
     case s of
         "A"            => A
       | "AF"           => AF
       | "AG"           => AG
       | "AX"           => AX
       | "abort"        => ABORT
       | "always"       => ALWAYS
       | "before"       => BEFORE
       | "E"            => E
       | "EF"           => EF
       | "EG"           => EG
       | "EX"           => EX
       | "forall"       => FORALL
       | "G"            => G
       | "inf"          => INF
       | "never"        => NEVER
       | "next"         => NEXT
       | "U"            => U
       | "X"            => X
       | "abort"        => ABORT
       | "until"        => UNTIL
       | "W"            => W
       | "whilenot"     => WHILENOT
       | "within"       => WITHIN
       | _              => Name s;

 }

rule Token = parse
    "(*"                { commentStart := getLexemeStart lexbuf;
                          commentDepth := 1;
                          SkipComment lexbuf; Token lexbuf }
  | `@`                 { AT }
  | `;`                 { SEMICOLON }
  | "[*"                { LBRKTSTAR }
  | "[="                { LBRKTEQ }
  | "[->"               { LBRKTLEFTARROW }
  | "[*]"               { LBRKTSTARRBRKT }
  | "[+]"               { LBRKTPLUSRBRKT }
  | `,`                 { COMMA }
  | `:`                 { COLON }
  | `|`                 { BAR }
  | "||"                { BARBAR }
  | `&`                 { AMPERSAND }
  | "&&"                { AMPERSANDAMPERSAND }
  | "->"                { LEFTARROW }
  | "<->"               { LEFTRIGHTARROW }
  | "|->"               { BARLEFTARROW }
  | "|=>"               { BAREQLEFTARROW }
  | "|="                { BAREQUAL }
  | `!`                 { EXCLAIM }
  | `*`                 { STAR }
  | `(`                 { LPAR }
  | `)`                 { RPAR }
  | `[`                 { LBRKT }
  | `]`                 { RBRKT }
  | `{`                 { LBRACE }
  | `}`                 { RBRACE }
  | "before!"           { BEFOREX }
  | "before!_"          { BEFOREXU }
  | "before_"           { BEFOREU }
  | "whilenot!_"        { WHILENOTXU }
  | "eventually!"       { EVENTUALLYX }
  | "next!"             { NEXTX }
  | "next_a"            { NEXTA }
  | "next_a!"           { NEXTAX }
  | "next_e"            { NEXTE }
  | "next_e!"           { NEXTEX }
  | "next_event"        { NEXTEVENT }
  | "next_event!"       { NEXTEVENTX }
  | "next_event_a!"     { NEXTEVENTAX }
  | "next_event_e!"     { NEXTEVENTEX }
  | "until!"            { UNTILX }
  | "until!_"           { UNTILXU }
  | "until_"            { UNTILU }
  | "whilenot!"         { WHILENOTX }
  | "whilenot!_"        { WHILENOTXU }
  | "whilenot_"         { WHILENOTU }
  | "within!"           { WITHINX }
  | "within!_"          { WITHINXU }
  | "within_"           { WITHINU }
  | "X!"                { XX }
  | eof                 { EOF }
  | [` ` `\t` `\n` `\r`]{ Token lexbuf }
  | [`0`-`9`]+          { case Int.fromString (getLexeme lexbuf) of
                             NONE   => lexerError lexbuf "internal error"
                           | SOME i => Number i}
  | [`_``a`-`z``A`-`Z`][`_``a`-`z``A`-`Z``0`-`9`]*
                        { keyword (getLexeme lexbuf) }

  | _                   { lexerError lexbuf "Illegal symbol in input" }

and SkipComment = parse
    "*)"                { commentDepth := !commentDepth - 1;
                          if !commentDepth = 0 then ()
                          else SkipComment lexbuf }
   | "(*"               { commentDepth := !commentDepth + 1;
                          SkipComment lexbuf }
   | (eof | `\^Z`)      { commentNotClosed lexbuf }
   | _                  { SkipComment lexbuf }
;
