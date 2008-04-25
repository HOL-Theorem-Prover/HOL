{
open Location Parser;

exception Impossible of string;   
exception LexicalError of string * int * int; 
fun fatalError s = raise(Impossible s);    

fun incr r = r := !r + 1;
fun decr r = r := !r - 1;

prim_val sml_hex_of_string : string -> int = 1 "sml_int_of_hex";
prim_val sml_float_of_string : string -> real = 1 "sml_float_of_string";    
prim_val sml_int_of_string : string -> int = 1 "sml_int_of_string"; 

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


(* For Quote/Antiquote --- object language embedding. *)

val quotation = ref false;

datatype lexingMode =
    NORMALlm
  | QUOTElm
  | ANTIQUOTElm
;

val lexingMode = ref NORMALlm;

val parCount = Stack.new() : int Stack.t;

fun resetLexerState() =
(
  lexingMode := NORMALlm;
  Stack.clear parCount
);

(* For nesting comments *)

val comment_depth = ref 0;

(* The table of keywords *)

val keyword_table = (Hasht.new 53 : (string,token) Hasht.t);

val () =
List.app (fn (str,tok) => Hasht.insert keyword_table str tok)
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

local (* Make sure that strings are shared (interned); this saves space 
         when writing to disk: *)
    val intern_table = (Hasht.new 123 : (string, string) Hasht.t);
in 
    fun share s =
       case Hasht.peek intern_table s of
           NONE    => (Hasht.insert intern_table s s; s)
         | SOME s' => s'  
end

fun mkKeyword lexbuf =
  let val s = getLexeme lexbuf in
    Hasht.find keyword_table s
    handle Subscript => ID (share s)
  end
;

val savedLexemeStart = ref 0;

val initial_string_buffer = CharArray.array(256, #"\000");
val string_buff = ref initial_string_buffer;
val string_index = ref 0;

fun reset_string_buffer() =
(
  string_buff := initial_string_buffer;
  string_index := 0;
  ()
);

fun store_string_char c =
  let open CharArray
      val len = length (!string_buff)
  in
    if !string_index >= len then
      let val new_buff = array(len * 2, #"\000") in
        copy
          { src = !string_buff, si = 0, len = NONE, dst = new_buff, di = 0 };
        string_buff := new_buff
      end
    else ();
    update(!string_buff, !string_index, c);
    incr string_index
  end;

fun get_stored_string() =
  let open CharArray
      val s = extract(!string_buff, 0, SOME (!string_index))
  in
    string_buff := initial_string_buffer;
    s
  end;

fun splitQualId s =
  let open CharVector
      val len' = size s - 1
      fun parse n =
        if n = 0 then
          ("", s)
        else if sub(s, n) = #"." then
          ( extract(s, 0, SOME n),
            extract(s, n + 1, SOME(len' - n)) )
        else
          parse (n-1)
  in parse len' end;

fun mkQualId lexbuf =
  let val (qual, id) = splitQualId(getLexeme lexbuf) in
    if id = "*" then
      QUAL_STAR { qual=qual, id=id }
    else
      QUAL_ID   { qual=qual, id=id }
  end
;

fun charCodeOfDecimal lexbuf i =
  100 * (Char.ord(getLexemeChar lexbuf i) - 48) +
   10 * (Char.ord(getLexemeChar lexbuf (i+1)) - 48) +
        (Char.ord(getLexemeChar lexbuf (i+2)) - 48)
;

fun lexError msg lexbuf =
(
  resetLexerState();
  raise LexicalError(msg, getLexemeStart lexbuf, getLexemeEnd lexbuf)
);

fun constTooLarge msg lexbuf =
(
  resetLexerState();
  lexError (msg ^ " constant is too large") lexbuf
);

prim_val sml_word_of_string    : string -> word = 1 "sml_word_of_dec";
prim_val sml_word_of_hexstring : string -> word = 1 "sml_word_of_hex";

fun notTerminated msg lexbuf =
(
  resetLexerState();
  raise LexicalError (msg ^ " not terminated",
                      !savedLexemeStart, getLexemeEnd lexbuf)
);

fun skipString msg skip lexbuf =
  let
    val pos1 = getLexemeStart lexbuf
    val pos2 = getLexemeEnd lexbuf
  in
    skip lexbuf;
    resetLexerState();
    raise (LexicalError(msg, pos1, pos2))
  end
;

fun scanString scan lexbuf =
(
  reset_string_buffer();
  savedLexemeStart := getLexemeStart lexbuf;
  scan lexbuf;
  setLexStartPos lexbuf (!savedLexemeStart - getLexAbsPos lexbuf)
);

}

rule Token = parse
    [^ `\000`-`\255`]
      { lexError "this will be never called!" lexbuf }
  | ""
      { case !lexingMode of
            NORMALlm =>
              TokenN lexbuf
          | QUOTElm =>
              (scanString Quotation lexbuf;
               case !lexingMode of
                   NORMALlm =>
                     QUOTER (get_stored_string())
                 | ANTIQUOTElm =>
                     QUOTEM (get_stored_string())
                 | QUOTElm =>
                     fatalError "Token")
          | ANTIQUOTElm =>
              AntiQuotation lexbuf
      }

and TokenN = parse
    [` ` `\n` `\r` `\t` `\^L`]  { TokenN lexbuf }
  | "(*"
      { savedLexemeStart := getLexemeStart lexbuf;
        comment_depth := 1; Comment lexbuf; TokenN lexbuf
      }
  | "*)"
      { lexError "unmatched comment bracket" lexbuf }
  | "'" [ `A`-`Z` `a`-`z` `0`-`9` `_` `'`]+
                { TYVAR   (getLexeme lexbuf) }
  | "0"         { ZDIGIT 0 }
  | [`1`-`9`]   { NZDIGIT   (sml_int_of_string(getLexeme lexbuf)) }
  | "0" [`0`-`9`]+
                { ZPOSINT2  (sml_int_of_string(getLexeme lexbuf))
                  handle Fail _ => constTooLarge "integer" lexbuf
                }
  | [`1`-`9`] [`0`-`9`]+
                { NZPOSINT2 (sml_int_of_string(getLexeme lexbuf))
                  handle Fail _ => constTooLarge "integer" lexbuf
                }
  | "~" [`0`-`9`]+
                { NEGINT    (sml_int_of_string(getLexeme lexbuf))
                  handle Fail _ => constTooLarge "integer" lexbuf
                }
  | "~"? "0x" [`0`-`9` `a`-`f` `A`-`F`]+
                { NEGINT    (sml_hex_of_string(getLexeme lexbuf))
                  handle Fail _ => constTooLarge "integer" lexbuf
                }
  | "0w" [`0`-`9`]+
                { WORD (sml_word_of_string(getLexeme lexbuf))
                  handle Fail _ => constTooLarge "word" lexbuf
                }
  | "0wx" [`0`-`9` `a`-`f` `A`-`F`]+
                { WORD (sml_word_of_hexstring(getLexeme lexbuf))
                  handle Fail _ => constTooLarge "word" lexbuf
                }
  | "~"? [`0`-`9`]+ (`.` [`0`-`9`]+)? ([`e` `E`] `~`? [`0`-`9`]+)?
                { REAL (sml_float_of_string (getLexeme lexbuf))
                  handle Fail _ => constTooLarge "real" lexbuf
                }
  | "\""
      { scanString String lexbuf;
        STRING (get_stored_string())
      }
  | "#\""
      { scanString String lexbuf;
        let val s = get_stored_string() in
          if size s <> 1 then
            lexError "ill-formed character constant" lexbuf
          else ();
          CHAR (CharVector.sub(s, 0))
        end }
  | "_"         { UNDERBAR }
  | ","         { COMMA }
  | "..."       { DOTDOTDOT }
  | "{"         { LBRACE }
  | "}"         { RBRACE }
  | "["         { LBRACKET }
  | "#["        { HASHLBRACKET }
  | "]"         { RBRACKET }
  | "("
     { if not(Stack.null parCount) then
         Stack.push (Stack.pop parCount + 1) parCount
       else ();
       LPAREN
     }
  | ")"
      { if not(Stack.null parCount) then
          let val count = Stack.pop parCount - 1 in
            if count = 0 then
              (lexingMode := QUOTElm; Token lexbuf)
            else
              (Stack.push count parCount; RPAREN)
          end
        else
          RPAREN
      }
  | ";"         { SEMICOLON }
  | (eof | `\^Z`) { EOF }
  | ""          { if !quotation then TokenIdQ lexbuf else TokenId lexbuf }

and TokenId = parse
    ( [`A`-`Z` `a`-`z`] [ `A`-`Z` `a`-`z` `0`-`9` `_` `'`]*
    | [`!` `%` `&` `$` `#` `+` `-` `/` `:` `<` `=` `>` `?` `@` `\\`
       `~` `\`` `^` `|` `*`]+ )
      { mkKeyword lexbuf }
  | ( [`A`-`Z` `a`-`z`] [ `A`-`Z` `a`-`z` `0`-`9` `_` `'`]*
    | [`!` `%` `&` `$` `#` `+` `-` `/` `:` `<` `=` `>` `?` `@` `\\`
       `~` `\`` `^` `|` `*`]+ )
    ("."
    ( [`A`-`Z` `a`-`z`] [ `A`-`Z` `a`-`z` `0`-`9` `_` `'`]*
    | [`!` `%` `&` `$` `#` `+` `-` `/` `:` `<` `=` `>` `?` `@` `\\`
       `~` `\`` `^` `|` `*`]+ ))+
      { mkQualId lexbuf }
  | _
      { lexError "ill-formed token" lexbuf }

and TokenIdQ = parse
    ( [`A`-`Z` `a`-`z`] [ `A`-`Z` `a`-`z` `0`-`9` `_` `'`]*
    | [`!` `%` `&` `$` `#` `+` `-` `/` `:` `<` `=` `>` `?` `@` `\\`
       `~` `^` `|` `*`]+ )
      { mkKeyword lexbuf }
  | ( [`A`-`Z` `a`-`z`] [ `A`-`Z` `a`-`z` `0`-`9` `_` `'`]*
    | [`!` `%` `&` `$` `#` `+` `-` `/` `:` `<` `=` `>` `?` `@` `\\`
       `~` `^` `|` `*`]+ )
    "."
    ( [`A`-`Z` `a`-`z`] [ `A`-`Z` `a`-`z` `0`-`9` `_` `'`]*
    | [`!` `%` `&` `$` `#` `+` `-` `/` `:` `<` `=` `>` `?` `@` `\\`
       `~` `^` `|` `*`]+ )
      { mkQualId lexbuf }
  | "`"
      { lexingMode := QUOTElm; QUOTEL }
  | _
      { lexError "ill-formed token" lexbuf }

and Comment = parse
    "(*"
      { (incr comment_depth; Comment lexbuf) }
  | "*)"
      { (decr comment_depth;
         if !comment_depth > 0 then Comment lexbuf else ()) }
  | (eof | `\^Z`)
      { notTerminated "comment" lexbuf }
  | _
      { Comment lexbuf }

and String = parse
    `"`
      { () }
  | `\\` [`\\` `"` `a` `b` `t` `n` `v` `f` `r`]
      { store_string_char(char_for_backslash(getLexemeChar lexbuf 1));
        String lexbuf }
  | `\\` [` ` `\t` `\n` `\r`]+ `\\`
      { String lexbuf }
  | `\\` `^` [`@`-`_`]
      { store_string_char(
          Char.chr(Char.ord(getLexemeChar lexbuf 2) - 64));
        String lexbuf }
  | `\\` [`0`-`9`] [`0`-`9`] [`0`-`9`]
      { let val code = charCodeOfDecimal lexbuf 1 in
          if code >= 256 then
            skipString "character code is too large" SkipString lexbuf
          else ();
          store_string_char(Char.chr code);
          String lexbuf
        end }
  | `\\`
      { skipString "ill-formed escape sequence" SkipString lexbuf }
  | (eof | `\^Z`)
      { notTerminated "string" lexbuf }
  | [`\n` `\r`]
      { skipString "newline not permitted in string" SkipString lexbuf }
  | [`\^A`-`\^Z` `\127` `\255`]
      { skipString "invalid character in string" SkipString lexbuf }
  | _
      { (store_string_char(getLexemeChar lexbuf 0);
         String lexbuf) }

and SkipString = parse
    `"`
      { () }
  | `\\` [`\\` `"` `n` `t`]
      { SkipString lexbuf }
  | `\\` [` ` `\t` `\n` `\r`]+ `\\`
      { SkipString lexbuf }
  | (eof | `\^Z`)
      { notTerminated "string" lexbuf }
  | _
      { SkipString lexbuf }

and Quotation = parse
    "`"
      { lexingMode := NORMALlm }
  | `^`
      { lexingMode := ANTIQUOTElm }
  | `\r`
      { Quotation lexbuf }
  | [`\t` `\n`]
      { (store_string_char(getLexemeChar lexbuf 0);
         Quotation lexbuf) }
  | (eof | `\^Z`)
      { lexingMode := NORMALlm;
        notTerminated "quotation" lexbuf
      }
  | [`\^A`-`\^Z` `\127` `\255`]
      { skipString "invalid character in quotation" SkipQuotation lexbuf }
  | _
      { (store_string_char(getLexemeChar lexbuf 0);
         Quotation lexbuf) }

and SkipQuotation = parse
    "`"
      { lexingMode := NORMALlm }
  | (eof | `\^Z`)
      { lexingMode := NORMALlm;
        notTerminated "quotation" lexbuf
      }
  | _
      { SkipQuotation lexbuf }

and AntiQuotation = parse
    ( [`A`-`Z` `a`-`z`] [ `A`-`Z` `a`-`z` `0`-`9` `_` `'`]*
    | [`!` `%` `&` `$` `#` `+` `-` `/` `:` `<` `=` `>` `?` `@` `\\`
       `~` `|` `*`]+ )
      { lexingMode := QUOTElm;
        mkKeyword lexbuf
      }
  | "("
      { Stack.push 1 parCount; lexingMode := NORMALlm;
        TokenN lexbuf
      }
  | "`"
      { lexingMode := NORMALlm;
        lexError "antiquotation is missing" lexbuf
      }
  | (eof | `\^Z`)
      { lexingMode := NORMALlm;
        notTerminated "antiquotation" lexbuf
      }
  | _
      { lexingMode := QUOTElm;
        lexError "ill-formed antiquotation" lexbuf
      }
;
