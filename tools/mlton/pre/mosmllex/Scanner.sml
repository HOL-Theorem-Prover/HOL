
structure Scanner:SCANNER =
struct
open LexBuffer LexError

open Fnlib Syntax Token Scan_aux
fun makeLex  lexbuf = 
 let
fun setLastAction f = LexBuffer.setLastAction lexbuf f
fun resetLastPos () = LexBuffer.resetLastPos lexbuf
fun resetStartPos () = LexBuffer.resetStartPos lexbuf
fun getLexeme () = LexBuffer.getLexeme lexbuf
fun getLexemeChar n = LexBuffer.getLexemeChar lexbuf n
fun getLexemeStart () = LexBuffer.getLexemeStart lexbuf
fun getLexemeEnd () = LexBuffer.getLexemeEnd lexbuf
fun getNextChar () = LexBuffer.getNextChar lexbuf
fun backtrack () = LexBuffer.backtrack lexbuf
fun action_50 () = (
 raise Lexical_error
             ("illegal character #" ^ (getLexeme ())) )
and action_49 () = (
 raise Lexical_error "unterminated lexer definition" )
and action_48 () = (
 Tdash )
and action_47 () = (
 Tcaret )
and action_46 () = (
 Trparen )
and action_45 () = (
 Tlparen )
and action_44 () = (
 Tplus )
and action_43 () = (
 Tmaybe )
and action_42 () = (
 Tstar )
and action_41 () = (
 Trbracket )
and action_40 () = (
 Tlbracket )
and action_39 () = (
 Teof )
and action_38 () = (
 Tunderscore )
and action_37 () = (
 Tor )
and action_36 () = (
 Tend )
and action_35 () = (
 Tequal )
and action_34 () = (
 let val n1 = getLexemeEnd ()
          val () = brace_depth := 1
          val Taction1 n2 = action ()
      in Taction(Location(LexBuffer.substring(lexbuf,n1,n2-n1))) end )
and action_33 () = (
 char () )
and action_32 () = (
 (reset_string_buffer();
       string ();
       Tstring(get_stored_string())) )
and action_31 () = (
 case getLexeme () of
        "rule"  => Trule
      | "parse" => Tparse
      | "and"   => Tand
      | "eof"   => Teof
      | "let"   => Tlet
      | s       => Tident s )
and action_30 () = (
 raise Lexical_error "unmatched comment bracket" )
and action_29 () = (
 (comment_depth := 1; comment (); main ()) )
and action_28 () = (
 main () )
and action_27 () = (
 action () )
and action_26 () = (
 raise Lexical_error "unterminated action" )
and action_25 () = (
 raise Lexical_error "unmatched comment bracket" )
and action_24 () = (
 (comment_depth := 1; comment (); action ()) )
and action_23 () = (
 (reset_string_buffer();
       string ();
       reset_string_buffer();
       action ()) )
and action_22 () = (
 (decr brace_depth;
           if !brace_depth = 0 then
             Taction1 (getLexemeStart ())
           else
             action ()) )
and action_21 () = (
 (incr brace_depth; action ()) )
and action_20 () = (
 (store_string_char(getLexemeChar 0);
       string ()) )
and action_19 () = (
 raise Lexical_error "invalid character in string" )
and action_18 () = (
 raise Lexical_error "unterminated string" )
and action_17 () = (
 raise Lexical_error "ill-formed escape sequence in string" )
and action_16 () = (
 let val code = char_for_decimal_code lexbuf 1 in
        if Char.ord code >= 256 then
          raise Lexical_error "character code in string > 255"
        else ();
        store_string_char code;
        string ()
      end )
and action_15 () = (
 (store_string_char(
           Char.chr(Char.ord(getLexemeChar 2) - 64));
         string ()) )
and action_14 () = (
 (store_string_char(char_for_backslash(getLexemeChar 1));
       string ()) )
and action_13 () = (
 string () )
and action_12 () = (
 Tend )
and action_11 () = (
 raise Lexical_error "ill-formed character constant" )
and action_10 () = (
 Tchar (getLexemeChar 0) )
and action_9 () = (
 raise Lexical_error "invalid character in character constant" )
and action_8 () = (
 raise Lexical_error "unterminated character constant" )
and action_7 () = (
 raise Lexical_error "ill-formed escape sequence in character constant" )
and action_6 () = (
 let val code = char_for_decimal_code lexbuf 1 in
        if Char.ord code >= 256 then
          raise Lexical_error "character code in string > 255"
        else ();
        Tchar (code)
      end )
and action_5 () = (
 Tchar (Char.chr(Char.ord(getLexemeChar 2) - 64)) )
and action_4 () = (
 Tchar (char_for_backslash (getLexemeChar 1)) )
and action_3 () = (
 comment () )
and action_2 () = (
 raise Lexical_error "unterminated comment" )
and action_1 () = (
 (decr comment_depth;
       if !comment_depth = 0 then Tend else comment ()) )
and action_0 () = (
 (incr comment_depth; comment ()) )
and state_0 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"*" => state_77 ()
 |  #"(" => state_76 ()
 |  #"\^Z" => action_2 ()
 |  #"\^@" => action_2 ()
 |  _ => action_3 ()
 end)
and state_1 () = (
 let val currChar = getNextChar () in
 if currChar >= #"\^A" andalso currChar <= #"\^Y" then  state_58 ()
 else case currChar of
    #"\^_" => state_58 ()
 |  #"\^^" => state_58 ()
 |  #"\^]" => state_58 ()
 |  #"\^\" => state_58 ()
 |  #"\^[" => state_58 ()
 |  #"\127" => state_58 ()
 |  #"\255" => state_58 ()
 |  #"\\" => state_61 ()
 |  #"\^Z" => state_59 ()
 |  #"\^@" => action_8 ()
 |  _ => state_60 ()
 end)
and state_2 () = (
 let val currChar = getNextChar () in
 if currChar >= #"\^A" andalso currChar <= #"\^Y" then  action_19 ()
 else case currChar of
    #"\^_" => action_19 ()
 |  #"\^^" => action_19 ()
 |  #"\^]" => action_19 ()
 |  #"\^\" => action_19 ()
 |  #"\^[" => action_19 ()
 |  #"\127" => action_19 ()
 |  #"\255" => action_19 ()
 |  #"\\" => state_48 ()
 |  #"\"" => action_12 ()
 |  #"\^Z" => action_18 ()
 |  #"\^@" => action_18 ()
 |  _ => action_20 ()
 end)
and state_3 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"}" => action_22 ()
 |  #"{" => action_21 ()
 |  #"*" => state_38 ()
 |  #"(" => state_37 ()
 |  #"\"" => action_23 ()
 |  #"\^Z" => action_26 ()
 |  #"\^@" => action_26 ()
 |  _ => action_27 ()
 end)
and state_4 () = (
 let val currChar = getNextChar () in
 if currChar >= #"A" andalso currChar <= #"Z" then  state_18 ()
 else if currChar >= #"f" andalso currChar <= #"z" then  state_18 ()
 else case currChar of
    #"d" => state_18 ()
 |  #"c" => state_18 ()
 |  #"b" => state_18 ()
 |  #"a" => state_18 ()
 |  #"\n" => state_7 ()
 |  #"\t" => state_7 ()
 |  #"\r" => state_7 ()
 |  #" " => state_7 ()
 |  #"|" => action_37 ()
 |  #"{" => action_34 ()
 |  #"e" => state_24 ()
 |  #"`" => action_33 ()
 |  #"_" => action_38 ()
 |  #"^" => action_47 ()
 |  #"]" => action_41 ()
 |  #"[" => action_40 ()
 |  #"?" => action_43 ()
 |  #"=" => action_35 ()
 |  #";" => action_36 ()
 |  #"-" => action_48 ()
 |  #"+" => action_44 ()
 |  #"*" => state_12 ()
 |  #")" => action_46 ()
 |  #"(" => state_10 ()
 |  #"\"" => action_32 ()
 |  #"\^Z" => action_49 ()
 |  #"\^@" => action_49 ()
 |  _ => action_50 ()
 end)
and state_7 () = (
 resetLastPos ();
 setLastAction action_28;
 let val currChar = getNextChar () in
 case currChar of
    #"\n" => state_32 ()
 |  #"\t" => state_32 ()
 |  #"\r" => state_32 ()
 |  #" " => state_32 ()
 |  _ => backtrack ()
 end)
and state_10 () = (
 resetLastPos ();
 setLastAction action_45;
 let val currChar = getNextChar () in
 case currChar of
    #"*" => action_29 ()
 |  _ => backtrack ()
 end)
and state_12 () = (
 resetLastPos ();
 setLastAction action_42;
 let val currChar = getNextChar () in
 case currChar of
    #")" => action_30 ()
 |  _ => backtrack ()
 end)
and state_18 () = (
 resetLastPos ();
 setLastAction action_31;
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_27 ()
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_27 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_27 ()
 else case currChar of
    #"'" => state_27 ()
 |  #"_" => state_27 ()
 |  _ => backtrack ()
 end)
and state_24 () = (
 resetLastPos ();
 setLastAction action_31;
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_27 ()
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_27 ()
 else if currChar >= #"a" andalso currChar <= #"n" then  state_27 ()
 else if currChar >= #"p" andalso currChar <= #"z" then  state_27 ()
 else case currChar of
    #"'" => state_27 ()
 |  #"_" => state_27 ()
 |  #"o" => state_28 ()
 |  _ => backtrack ()
 end)
and state_27 () = (
 resetLastPos ();
 setLastAction action_31;
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_27 ()
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_27 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_27 ()
 else case currChar of
    #"'" => state_27 ()
 |  #"_" => state_27 ()
 |  _ => backtrack ()
 end)
and state_28 () = (
 resetLastPos ();
 setLastAction action_31;
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_27 ()
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_27 ()
 else if currChar >= #"g" andalso currChar <= #"z" then  state_27 ()
 else case currChar of
    #"'" => state_27 ()
 |  #"_" => state_27 ()
 |  #"e" => state_27 ()
 |  #"d" => state_27 ()
 |  #"c" => state_27 ()
 |  #"b" => state_27 ()
 |  #"a" => state_27 ()
 |  #"f" => state_29 ()
 |  _ => backtrack ()
 end)
and state_29 () = (
 resetLastPos ();
 setLastAction action_31;
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_27 ()
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_27 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_27 ()
 else case currChar of
    #"'" => state_27 ()
 |  #"_" => state_27 ()
 |  _ => backtrack ()
 end)
and state_32 () = (
 resetLastPos ();
 setLastAction action_28;
 let val currChar = getNextChar () in
 case currChar of
    #"\n" => state_32 ()
 |  #"\t" => state_32 ()
 |  #"\r" => state_32 ()
 |  #" " => state_32 ()
 |  _ => backtrack ()
 end)
and state_37 () = (
 resetLastPos ();
 setLastAction action_27;
 let val currChar = getNextChar () in
 case currChar of
    #"*" => action_24 ()
 |  _ => backtrack ()
 end)
and state_38 () = (
 resetLastPos ();
 setLastAction action_27;
 let val currChar = getNextChar () in
 case currChar of
    #")" => action_25 ()
 |  _ => backtrack ()
 end)
and state_48 () = (
 resetLastPos ();
 setLastAction action_17;
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_51 ()
 else case currChar of
    #"\"" => action_14 ()
 |  #"\\" => action_14 ()
 |  #"b" => action_14 ()
 |  #"n" => action_14 ()
 |  #"r" => action_14 ()
 |  #"t" => action_14 ()
 |  #"\n" => state_49 ()
 |  #"\t" => state_49 ()
 |  #"\r" => state_49 ()
 |  #" " => state_49 ()
 |  #"^" => state_52 ()
 |  _ => backtrack ()
 end)
and state_49 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\n" => state_49 ()
 |  #"\t" => state_49 ()
 |  #"\r" => state_49 ()
 |  #" " => state_49 ()
 |  #"\\" => action_13 ()
 |  _ => backtrack ()
 end)
and state_51 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_54 ()
 else backtrack ()
 end)
and state_52 () = (
 let val currChar = getNextChar () in
 if currChar >= #"@" andalso currChar <= #"_" then  action_15 ()
 else backtrack ()
 end)
and state_54 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  action_16 ()
 else backtrack ()
 end)
and state_58 () = (
 resetLastPos ();
 setLastAction action_9;
 let val currChar = getNextChar () in
 case currChar of
    #"`" => action_10 ()
 |  _ => backtrack ()
 end)
and state_59 () = (
 resetLastPos ();
 setLastAction action_8;
 let val currChar = getNextChar () in
 case currChar of
    #"`" => action_10 ()
 |  _ => backtrack ()
 end)
and state_60 () = (
 resetLastPos ();
 setLastAction action_11;
 let val currChar = getNextChar () in
 case currChar of
    #"`" => action_10 ()
 |  _ => backtrack ()
 end)
and state_61 () = (
 resetLastPos ();
 setLastAction action_7;
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_62 ()
 else case currChar of
    #"\\" => state_63 ()
 |  #"b" => state_63 ()
 |  #"n" => state_63 ()
 |  #"r" => state_63 ()
 |  #"t" => state_63 ()
 |  #"`" => state_65 ()
 |  #"^" => state_64 ()
 |  _ => backtrack ()
 end)
and state_62 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_69 ()
 else backtrack ()
 end)
and state_63 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"`" => action_4 ()
 |  _ => backtrack ()
 end)
and state_64 () = (
 let val currChar = getNextChar () in
 if currChar >= #"@" andalso currChar <= #"_" then  state_67 ()
 else backtrack ()
 end)
and state_65 () = (
 resetLastPos ();
 setLastAction action_10;
 let val currChar = getNextChar () in
 case currChar of
    #"`" => action_4 ()
 |  _ => backtrack ()
 end)
and state_67 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"`" => action_5 ()
 |  _ => backtrack ()
 end)
and state_69 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_70 ()
 else backtrack ()
 end)
and state_70 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"`" => action_6 ()
 |  _ => backtrack ()
 end)
and state_76 () = (
 resetLastPos ();
 setLastAction action_3;
 let val currChar = getNextChar () in
 case currChar of
    #"*" => action_0 ()
 |  _ => backtrack ()
 end)
and state_77 () = (
 resetLastPos ();
 setLastAction action_3;
 let val currChar = getNextChar () in
 case currChar of
    #")" => action_1 ()
 |  _ => backtrack ()
 end)
and main () =
  (resetStartPos ();
   state_4 ())

and action () =
  (resetStartPos ();
   state_3 ())

and string () =
  (resetStartPos ();
   state_2 ())

and char () =
  (resetStartPos ();
   state_1 ())

and comment () =
  (resetStartPos ();
   state_0 ())

(* The following checks type consistency of actions *)
val _ = fn _ => [action_50, action_49, action_48, action_47, action_46, action_45, action_44, action_43, action_42, action_41, action_40, action_39, action_38, action_37, action_36, action_35, action_34, action_33, action_32, action_31, action_30, action_29, action_28];
val _ = fn _ => [action_27, action_26, action_25, action_24, action_23, action_22, action_21];
val _ = fn _ => [action_20, action_19, action_18, action_17, action_16, action_15, action_14, action_13, action_12];
val _ = fn _ => [action_11, action_10, action_9, action_8, action_7, action_6, action_5, action_4];
val _ = fn _ => [action_3, action_2, action_1, action_0];
in main
 end

end
