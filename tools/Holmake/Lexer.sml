local open Obj Lexing in


open Parser

(* For nesting comments *)

val comment_depth = ref 0;

(* The table of keywords *)
val keyword_table = 
    (Polyhash.mkPolyTable(53, Subscript) : (string,token) Polyhash.hash_table);

val () =
    List.app (Polyhash.insert keyword_table)
    [
     ("abstype",    NULL),
     ("and",        NULL),
     ("andalso",    NULL),
     ("as",         NULL),
     ("case",       NULL),
     ("datatype",   NULL),
     ("do",         NULL),
     ("else",       NULL),
     ("eqtype",     NULL),
     ("end",        NULL),
     ("exception",  NULL),
     ("fn",         NULL),
     ("fun",        NULL),
     ("handle",     NULL),
     ("if",         NULL),
     ("in",         NULL),
     ("infix",      NULL),
     ("infixr",     NULL),
     ("let",        NULL),
     ("local",      NULL),
     ("nonfix",     NULL),
     ("of",         NULL),
     ("op",         NULL),
     ("open",       OPEN),
     ("orelse",     NULL),
     ("prim_eqtype",  NULL),
     ("prim_EQtype",  NULL),
     ("prim_type",    NULL),
     ("prim_val",     NULL),
     ("raise",      NULL),
     ("rec",        NULL),
     ("then",       NULL),
     ("type",       NULL),
     ("val",        NULL),
     ("while",      NULL),
     ("with",       NULL),
     ("withtype",   NULL),
     ("#",          NULL),
     ("->",         NULL),
     ("|",          NULL),
     (":",          NULL),
     ("=>",         NULL),
     ("=",          NULL),
     ("*",          NULL)
     ];

fun mkKeyword lexbuf =
  let val s = getLexeme lexbuf in
    Polyhash.find keyword_table s
    handle Subscript => ID s
  end
;

val savedLexemeStart = ref 0;

fun getQual s =
  let open CharVector
      val len' = size s - 1
      fun parse n =
        if n >= len' then
	    ""				(* This can't happen *)
        else if sub(s, n) = #"." then
	    extract(s, 0, SOME n)
        else
	    parse (n+1)
  in parse 0 end;

fun mkQualId lexbuf =
  QUAL_ID (getQual(getLexeme lexbuf));

fun lexError msg lexbuf = NULL;

fun incr r = (r := !r + 1);
fun decr r = (r := !r - 1);


fun action_42 lexbuf = (
TokenN lexbuf)
and action_41 lexbuf = (
 lexError "this will be never called!" lexbuf )
and action_40 lexbuf = (
 TokenId lexbuf )
and action_39 lexbuf = (
 EOF )
and action_38 lexbuf = (
 NULL )
and action_37 lexbuf = (
 NULL )
and action_36 lexbuf = (
 NULL )
and action_35 lexbuf = (
 NULL )
and action_34 lexbuf = (
 NULL )
and action_33 lexbuf = (
 NULL )
and action_32 lexbuf = (
 NULL )
and action_31 lexbuf = (
 NULL )
and action_30 lexbuf = (
 NULL )
and action_29 lexbuf = (
 NULL )
and action_28 lexbuf = (
 NULL )
and action_27 lexbuf = (
 String lexbuf )
and action_26 lexbuf = (
 String lexbuf )
and action_25 lexbuf = (
 NULL )
and action_24 lexbuf = (
 NULL )
and action_23 lexbuf = (
 lexError "unmatched comment bracket" lexbuf )
and action_22 lexbuf = (
 savedLexemeStart := getLexemeStart lexbuf;
        comment_depth := 1; Comment lexbuf; TokenN lexbuf
      )
and action_21 lexbuf = (
 TokenN lexbuf )
and action_20 lexbuf = (
 lexError "ill-formed token" lexbuf )
and action_19 lexbuf = (
 mkQualId lexbuf )
and action_18 lexbuf = (
 mkKeyword lexbuf )
and action_17 lexbuf = (
 Comment lexbuf )
and action_16 lexbuf = (
 EOF )
and action_15 lexbuf = (
 (decr comment_depth;
         if !comment_depth > 0 then Comment lexbuf else NULL) )
and action_14 lexbuf = (
 (incr comment_depth; Comment lexbuf) )
and action_13 lexbuf = (
 String lexbuf )
and action_12 lexbuf = (
 SkipString lexbuf )
and action_11 lexbuf = (
 EOF )
and action_10 lexbuf = (
 SkipString lexbuf )
and action_9 lexbuf = (
 String lexbuf )
and action_8 lexbuf = (
 String lexbuf )
and action_7 lexbuf = (
 String lexbuf )
and action_6 lexbuf = (
 String lexbuf )
and action_5 lexbuf = (
 NULL )
and action_4 lexbuf = (
 SkipString lexbuf )
and action_3 lexbuf = (
 EOF )
and action_2 lexbuf = (
 SkipString lexbuf )
and action_1 lexbuf = (
 SkipString lexbuf )
and action_0 lexbuf = (
 NULL )
and state_0 lexbuf = (
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"\\" => state_69 lexbuf
 |  #"\"" => action_0 lexbuf
 |  #"\^Z" => action_3 lexbuf
 |  #"\^@" => action_3 lexbuf
 |  _ => action_4 lexbuf
 end)
and state_1 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"\^A" andalso currChar <= #"\^Y" then  action_12 lexbuf
 else case currChar of
    #"\127" => action_12 lexbuf
 |  #"\255" => action_12 lexbuf
 |  #"\\" => state_56 lexbuf
 |  #"\"" => action_5 lexbuf
 |  #"\^Z" => action_11 lexbuf
 |  #"\^@" => action_11 lexbuf
 |  _ => action_13 lexbuf
 end)
and state_2 lexbuf = (
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"*" => state_48 lexbuf
 |  #"(" => state_47 lexbuf
 |  #"\^Z" => action_16 lexbuf
 |  #"\^@" => action_16 lexbuf
 |  _ => action_17 lexbuf
 end)
and state_3 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"A" andalso currChar <= #"Z" then  state_38 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_38 lexbuf
 else case currChar of
    #"!" => state_37 lexbuf
 |  #"&" => state_37 lexbuf
 |  #"%" => state_37 lexbuf
 |  #"$" => state_37 lexbuf
 |  #"#" => state_37 lexbuf
 |  #"+" => state_37 lexbuf
 |  #"*" => state_37 lexbuf
 |  #"-" => state_37 lexbuf
 |  #"/" => state_37 lexbuf
 |  #":" => state_37 lexbuf
 |  #"@" => state_37 lexbuf
 |  #"?" => state_37 lexbuf
 |  #">" => state_37 lexbuf
 |  #"=" => state_37 lexbuf
 |  #"<" => state_37 lexbuf
 |  #"\\" => state_37 lexbuf
 |  #"^" => state_37 lexbuf
 |  #"`" => state_37 lexbuf
 |  #"|" => state_37 lexbuf
 |  #"~" => state_37 lexbuf
 |  #"\^@" => backtrack lexbuf
 |  _ => action_20 lexbuf
 end)
and state_4 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_40);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_16 lexbuf
 else case currChar of
    #"\n" => action_21 lexbuf
 |  #"\t" => action_21 lexbuf
 |  #"\r" => action_21 lexbuf
 |  #" " => action_21 lexbuf
 |  #"\^@" => action_39 lexbuf
 |  #"\^Z" => action_39 lexbuf
 |  #"~" => state_23 lexbuf
 |  #"}" => action_32 lexbuf
 |  #"{" => action_31 lexbuf
 |  #"_" => action_28 lexbuf
 |  #"]" => action_35 lexbuf
 |  #"[" => action_33 lexbuf
 |  #";" => action_38 lexbuf
 |  #"." => state_15 lexbuf
 |  #"," => action_29 lexbuf
 |  #"*" => state_13 lexbuf
 |  #")" => action_37 lexbuf
 |  #"(" => state_11 lexbuf
 |  #"'" => state_10 lexbuf
 |  #"#" => state_9 lexbuf
 |  #"\"" => action_26 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_5 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_42);
 let val currChar = getNextChar lexbuf in
 case currChar of
    _ => backtrack lexbuf
 end)
and state_9 lexbuf = (
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"[" => action_34 lexbuf
 |  #"\"" => action_27 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_10 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_33 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_33 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_33 lexbuf
 else case currChar of
    #"'" => state_33 lexbuf
 |  #"_" => state_33 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_11 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_36);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"*" => action_22 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_13 lexbuf = (
 let val currChar = getNextChar lexbuf in
 case currChar of
    #")" => action_23 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_15 lexbuf = (
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"." => state_29 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_16 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_25);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_16 lexbuf
 else case currChar of
    #"E" => state_25 lexbuf
 |  #"." => state_24 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_23 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_16 lexbuf
 else backtrack lexbuf
 end)
and state_24 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_28 lexbuf
 else backtrack lexbuf
 end)
and state_25 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_26 lexbuf
 else case currChar of
    #"~" => state_27 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_26 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_25);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_26 lexbuf
 else backtrack lexbuf
 end)
and state_27 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_26 lexbuf
 else backtrack lexbuf
 end)
and state_28 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_25);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_28 lexbuf
 else case currChar of
    #"E" => state_25 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_29 lexbuf = (
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"." => action_30 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_33 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_24);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_33 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_33 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_33 lexbuf
 else case currChar of
    #"'" => state_33 lexbuf
 |  #"_" => state_33 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_37 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_18);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"!" => state_43 lexbuf
 |  #"&" => state_43 lexbuf
 |  #"%" => state_43 lexbuf
 |  #"$" => state_43 lexbuf
 |  #"#" => state_43 lexbuf
 |  #"+" => state_43 lexbuf
 |  #"*" => state_43 lexbuf
 |  #"-" => state_43 lexbuf
 |  #"/" => state_43 lexbuf
 |  #":" => state_43 lexbuf
 |  #"@" => state_43 lexbuf
 |  #"?" => state_43 lexbuf
 |  #">" => state_43 lexbuf
 |  #"=" => state_43 lexbuf
 |  #"<" => state_43 lexbuf
 |  #"\\" => state_43 lexbuf
 |  #"^" => state_43 lexbuf
 |  #"`" => state_43 lexbuf
 |  #"|" => state_43 lexbuf
 |  #"~" => state_43 lexbuf
 |  #"." => state_40 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_38 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_18);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_39 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_39 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_39 lexbuf
 else case currChar of
    #"'" => state_39 lexbuf
 |  #"_" => state_39 lexbuf
 |  #"." => state_40 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_39 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_18);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_39 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_39 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_39 lexbuf
 else case currChar of
    #"'" => state_39 lexbuf
 |  #"_" => state_39 lexbuf
 |  #"." => state_40 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_40 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"A" andalso currChar <= #"Z" then  state_42 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_42 lexbuf
 else case currChar of
    #"!" => state_41 lexbuf
 |  #"&" => state_41 lexbuf
 |  #"%" => state_41 lexbuf
 |  #"$" => state_41 lexbuf
 |  #"#" => state_41 lexbuf
 |  #"+" => state_41 lexbuf
 |  #"*" => state_41 lexbuf
 |  #"-" => state_41 lexbuf
 |  #"/" => state_41 lexbuf
 |  #":" => state_41 lexbuf
 |  #"@" => state_41 lexbuf
 |  #"?" => state_41 lexbuf
 |  #">" => state_41 lexbuf
 |  #"=" => state_41 lexbuf
 |  #"<" => state_41 lexbuf
 |  #"\\" => state_41 lexbuf
 |  #"^" => state_41 lexbuf
 |  #"`" => state_41 lexbuf
 |  #"|" => state_41 lexbuf
 |  #"~" => state_41 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_41 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_19);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"!" => state_41 lexbuf
 |  #"&" => state_41 lexbuf
 |  #"%" => state_41 lexbuf
 |  #"$" => state_41 lexbuf
 |  #"#" => state_41 lexbuf
 |  #"+" => state_41 lexbuf
 |  #"*" => state_41 lexbuf
 |  #"-" => state_41 lexbuf
 |  #"/" => state_41 lexbuf
 |  #":" => state_41 lexbuf
 |  #"@" => state_41 lexbuf
 |  #"?" => state_41 lexbuf
 |  #">" => state_41 lexbuf
 |  #"=" => state_41 lexbuf
 |  #"<" => state_41 lexbuf
 |  #"\\" => state_41 lexbuf
 |  #"^" => state_41 lexbuf
 |  #"`" => state_41 lexbuf
 |  #"|" => state_41 lexbuf
 |  #"~" => state_41 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_42 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_19);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_42 lexbuf
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_42 lexbuf
 else if currChar >= #"a" andalso currChar <= #"z" then  state_42 lexbuf
 else case currChar of
    #"'" => state_42 lexbuf
 |  #"_" => state_42 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_43 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_18);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"!" => state_43 lexbuf
 |  #"&" => state_43 lexbuf
 |  #"%" => state_43 lexbuf
 |  #"$" => state_43 lexbuf
 |  #"#" => state_43 lexbuf
 |  #"+" => state_43 lexbuf
 |  #"*" => state_43 lexbuf
 |  #"-" => state_43 lexbuf
 |  #"/" => state_43 lexbuf
 |  #":" => state_43 lexbuf
 |  #"@" => state_43 lexbuf
 |  #"?" => state_43 lexbuf
 |  #">" => state_43 lexbuf
 |  #"=" => state_43 lexbuf
 |  #"<" => state_43 lexbuf
 |  #"\\" => state_43 lexbuf
 |  #"^" => state_43 lexbuf
 |  #"`" => state_43 lexbuf
 |  #"|" => state_43 lexbuf
 |  #"~" => state_43 lexbuf
 |  #"." => state_40 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_47 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_17);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"*" => action_14 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_48 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_17);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #")" => action_15 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_56 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_10);
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_59 lexbuf
 else case currChar of
    #"\"" => action_6 lexbuf
 |  #"\\" => action_6 lexbuf
 |  #"n" => action_6 lexbuf
 |  #"t" => action_6 lexbuf
 |  #"\n" => state_57 lexbuf
 |  #"\t" => state_57 lexbuf
 |  #"\r" => state_57 lexbuf
 |  #" " => state_57 lexbuf
 |  #"^" => state_60 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_57 lexbuf = (
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"\n" => state_57 lexbuf
 |  #"\t" => state_57 lexbuf
 |  #"\r" => state_57 lexbuf
 |  #" " => state_57 lexbuf
 |  #"\\" => action_7 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_59 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  state_62 lexbuf
 else backtrack lexbuf
 end)
and state_60 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"@" andalso currChar <= #"_" then  action_8 lexbuf
 else backtrack lexbuf
 end)
and state_62 lexbuf = (
 let val currChar = getNextChar lexbuf in
 if currChar >= #"0" andalso currChar <= #"9" then  action_9 lexbuf
 else backtrack lexbuf
 end)
and state_69 lexbuf = (
 setLexLastPos lexbuf (getLexCurrPos lexbuf);
 setLexLastAction lexbuf (magic action_4);
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"\"" => action_1 lexbuf
 |  #"\\" => action_1 lexbuf
 |  #"n" => action_1 lexbuf
 |  #"t" => action_1 lexbuf
 |  #"\n" => state_70 lexbuf
 |  #"\t" => state_70 lexbuf
 |  #"\r" => state_70 lexbuf
 |  #" " => state_70 lexbuf
 |  _ => backtrack lexbuf
 end)
and state_70 lexbuf = (
 let val currChar = getNextChar lexbuf in
 case currChar of
    #"\n" => state_70 lexbuf
 |  #"\t" => state_70 lexbuf
 |  #"\r" => state_70 lexbuf
 |  #" " => state_70 lexbuf
 |  #"\\" => action_2 lexbuf
 |  _ => backtrack lexbuf
 end)
and Token lexbuf =
  (setLexStartPos lexbuf (getLexCurrPos lexbuf);
   state_5 lexbuf)

and TokenN lexbuf =
  (setLexStartPos lexbuf (getLexCurrPos lexbuf);
   state_4 lexbuf)

and TokenId lexbuf =
  (setLexStartPos lexbuf (getLexCurrPos lexbuf);
   state_3 lexbuf)

and Comment lexbuf =
  (setLexStartPos lexbuf (getLexCurrPos lexbuf);
   state_2 lexbuf)

and String lexbuf =
  (setLexStartPos lexbuf (getLexCurrPos lexbuf);
   state_1 lexbuf)

and SkipString lexbuf =
  (setLexStartPos lexbuf (getLexCurrPos lexbuf);
   state_0 lexbuf)

(* The following checks type consistency of actions *)
val _ = fn _ => [action_42, action_41];
val _ = fn _ => [action_40, action_39, action_38, action_37, action_36, action_35, action_34, action_33, action_32, action_31, action_30, action_29, action_28, action_27, action_26, action_25, action_24, action_23, action_22, action_21];
val _ = fn _ => [action_20, action_19, action_18];
val _ = fn _ => [action_17, action_16, action_15, action_14];
val _ = fn _ => [action_13, action_12, action_11, action_10, action_9, action_8, action_7, action_6, action_5];
val _ = fn _ => [action_4, action_3, action_2, action_1, action_0];

end
