{
val output_stream = ref TextIO.stdOut
fun ECHO lb = TextIO.output(!output_stream, Lexing.getLexeme lb)
fun print s = TextIO.output(!output_stream, s)
val comdepth = ref 0
val pardepth = ref 0
val antiquote = ref false
fun inc r = (r := !r + 1)
fun dec r = (r := !r - 1)

fun drop_upto c s = let
  (* returns the substring of s that begins at the first occurrence of c *)
  open Substring
  val ss = all s
  val remainder = dropl (fn c' => c <> c') ss
in
  string remainder
end

(* generate location pragmas inside fragments (not antiquoted ones), for the lexer *)
val row = ref 0
val rowstart = ref 0
fun nextline lb = (row := !row + 1; rowstart := getLexemeEnd lb)
fun locpragma lb off
  = " (*#loc "^Int.toString(!row + 1)^" "^
    Int.toString(getLexemeEnd lb - !rowstart - off + 1)^"*)"
    (* NB: the initial space is critical, or else the comment might not be recognised
       when prepended by a paren or symbol char.  --KW
       See cvs log comment at rev 1.2 of src/parse/base_tokens.lex *)

}

let letter = [ `A` - `Z` `a` - `z` ]
let digit = [ `0` - `9` ]
let symbol = [ `!` `%` `&` `$` `+` `/` `:` `<` `=` `>` `?` `@` `~` `|` `-`
               `#` `*` `\\` `^`]
let MLid = letter (letter | digit | `_` | `'`)* | symbol +
let ws = [ ` ` `\t` ]
let newline = "\r\n" | `\n` | `\r`  (* DOS, UNIX, Mac respectively *)

rule INITIAL =
parse `"` { ECHO lexbuf; STRING lexbuf  }
  | "(*" { ECHO lexbuf; inc comdepth; COMMENT lexbuf }
  | "("  { ECHO lexbuf; inc pardepth; INITIAL lexbuf }
  | ")"  { ECHO lexbuf; dec pardepth;
           if !antiquote andalso !pardepth < 1 then () else INITIAL lexbuf }
  | "==" ws * "`" { print ("(Type [QUOTE \""^locpragma lexbuf 0); OLDTYQUOTE lexbuf }
  | "--" ws * "`" { print ("(Term [QUOTE \""^locpragma lexbuf 0); OLDTMQUOTE lexbuf }
  | "``" ws * `:` (letter | ws | [`(` `'` ]) {
      print ("(Type [QUOTE \""^locpragma lexbuf 2);
      print (drop_upto #":" (Lexing.getLexeme lexbuf));
      TYQUOTE lexbuf
    }
  | "``" ws * ":^" { print ("(Type [QUOTE \""^locpragma lexbuf 2^":\", ANTIQUOTE (");
                     ANTIQUOTE lexbuf; TYQUOTE lexbuf }
  | "``" { print ("(Term [QUOTE \""^locpragma lexbuf 0); TMQUOTE lexbuf }
  | "`"  { print ("[QUOTE \""^locpragma lexbuf 0); QUOTE lexbuf }
  | newline { print "\n"; TextIO.flushOut (!output_stream); nextline lexbuf; INITIAL lexbuf }
  | _ { ECHO lexbuf; INITIAL lexbuf }
  | eof { TextIO.flushOut (!output_stream) }

and STRING =
parse "\\\"" { ECHO lexbuf; STRING lexbuf }
    | "\\\\" { ECHO lexbuf; STRING lexbuf }
    | "\""   { ECHO lexbuf; INITIAL lexbuf }
    | newline { print "\n"; TextIO.flushOut (!output_stream); nextline lexbuf; STRING lexbuf }
    | _      { ECHO lexbuf; STRING lexbuf }
    | eof    { () }

and COMMENT =
parse "(*"   { ECHO lexbuf; inc comdepth; COMMENT lexbuf }
    | "*)"   { ECHO lexbuf; dec comdepth;
               if !comdepth < 1 then INITIAL lexbuf
               else COMMENT lexbuf }
    | newline { print "\n"; TextIO.flushOut (!output_stream); nextline lexbuf; COMMENT lexbuf }
    | _      { ECHO lexbuf; COMMENT lexbuf }
    | eof    { () }

and QUOTE =
parse "`"    { print "\"]"; INITIAL lexbuf }
    | `^`    { print "\", ANTIQUOTE ("; ANTIQUOTE lexbuf; QUOTE lexbuf }
    | `\\`   { print "\\\\"; QUOTE lexbuf }
    | `"`   { print "\\\""; QUOTE lexbuf }
    | `\t`   { print "\\t"; QUOTE lexbuf }
    | newline{ nextline lexbuf; print (" \",\nQUOTE \""^locpragma lexbuf 0);
               TextIO.flushOut (!output_stream); QUOTE lexbuf }
    | _      { ECHO lexbuf; QUOTE lexbuf }
    | eof    { () }

and TMQUOTE =
parse "``"   { print "\"])"; INITIAL lexbuf }
    | `^`    { print "\", ANTIQUOTE ("; ANTIQUOTE lexbuf; TMQUOTE lexbuf }
    | `\\`   { print "\\\\"; TMQUOTE lexbuf }
    | `"`   { print "\\\""; TMQUOTE lexbuf }
    | `\t`   { print "\\t"; TMQUOTE lexbuf }
    | newline{ nextline lexbuf; print (" \",\nQUOTE \""^locpragma lexbuf 0);
               TextIO.flushOut(!output_stream); TMQUOTE lexbuf }
    | _      { ECHO lexbuf; TMQUOTE lexbuf }
    | eof    { () }

and TYQUOTE =
parse "``"   { print "\"])"; INITIAL lexbuf }
    | `^`    { print "\", ANTIQUOTE ("; ANTIQUOTE lexbuf; TYQUOTE lexbuf }
    | `\\`   { print "\\\\"; TYQUOTE lexbuf }
    | `"`   { print "\\\""; TYQUOTE lexbuf }
    | `\t`   { print "\\t"; TYQUOTE lexbuf }
    | newline{ nextline lexbuf; print (" \",\nQUOTE \""^locpragma lexbuf 0);
               TextIO.flushOut (!output_stream); TYQUOTE lexbuf }
    | _      { ECHO lexbuf; TYQUOTE lexbuf }
    | eof    { () }

and OLDTMQUOTE =
parse "`" ws * "--"  { print "\"])"; INITIAL lexbuf }
    | `^`    { print "\", ANTIQUOTE ("; ANTIQUOTE lexbuf;
               OLDTMQUOTE lexbuf
             }
    | `\\`   { print "\\\\"; OLDTMQUOTE lexbuf }
    | `"`   { print "\\\""; OLDTMQUOTE lexbuf }
    | `\t`   { print "\\t"; OLDTMQUOTE lexbuf }
    | newline{ nextline lexbuf; print (" \",\nQUOTE \""^locpragma lexbuf 0);
               TextIO.flushOut (!output_stream); OLDTMQUOTE lexbuf }
    | _      { ECHO lexbuf; OLDTMQUOTE lexbuf }
    | eof    { () }

and OLDTYQUOTE =
parse "`" ws * "=="  { print "\"])"; INITIAL lexbuf }
    | `^`    { print "\", ANTIQUOTE ("; ANTIQUOTE lexbuf;
               OLDTYQUOTE lexbuf
             }
    | `\\`   { print "\\\\"; OLDTYQUOTE lexbuf }
    | `"`   { print "\\\""; OLDTYQUOTE lexbuf }
    | `\t`   { print "\\t"; OLDTYQUOTE lexbuf }
    | newline{ nextline lexbuf; print (" \",\nQUOTE \""^locpragma lexbuf 0);
               TextIO.flushOut (!output_stream); OLDTYQUOTE lexbuf }
    | _      { ECHO lexbuf; OLDTYQUOTE lexbuf }
    | eof    { () }

and ANTIQUOTE =
parse MLid { ECHO lexbuf; print ("),QUOTE \""^locpragma lexbuf 0) }
    | `(`  { let val oldanti = !antiquote in
              ECHO lexbuf; pardepth := 1; antiquote := true; INITIAL lexbuf;
              print ("),QUOTE \""^locpragma lexbuf 0); antiquote := oldanti
            end }
    | ws + { ANTIQUOTE lexbuf }
    | newline{ECHO lexbuf; TextIO.flushOut(!output_stream); nextline lexbuf; ANTIQUOTE lexbuf}
    | _    { ECHO lexbuf }
    | eof  { () }

;
