(* -*-sml-*- *)
  structure base_lexer =
  struct

  open LexBuffer base_tokens locn

  type extrastate = (int * int * int * (int * int) option) ref
  (* mutable state argument to each rule is st=(nf,r,i,rcopt), where:
       - nf  is the number of the fragment being parsed
       - r   is the current row number
       - i   is the index of the first char on the current row
       - rcopt is the absolute line and character of the start of this fragment, if known
  *)

  datatype ('a,'b,'c) lextype =
    Base_token of 'a
  | String of 'b
  | Comment of 'c;

  fun mkLoc (st as ref (_,_,_,rcopt)) s e
    = case rcopt of
          NONE => Loc(s,e)
        | SOME(row,col) => Loc(rel_to_abs row col s, rel_to_abs row col e)

  fun getLoc (st as ref (nf,r,i,rcopt)) lexbuf
    = let val s = LocP(nf,r,getLexemeStart lexbuf - i)
          val e = LocP(nf,r,getLexemeEnd lexbuf - i - 1)
      in
          mkLoc st s e
      end

  fun newstate nf = ref (nf,0,0,NONE)

  (* processes location pragmas of the form (*#loc row col*), using
     them to determine the absolute position of fragments in the input
     stream. *)
  fun dolocpragma parser lexbuf (st as ref (nf,r,i,rcopt))
    = let val s = Substring.all (getLexeme lexbuf)
          val sr = Substring.dropl (not o Char.isDigit) s
          val sc = Substring.dropl (Char.isDigit) sr
      in
          (st := (nf,0,getLexemeEnd lexbuf,
                  SOME (valOf (Int.fromString(Substring.string sr)) - 1,
                        valOf (Int.fromString(Substring.string sc)) - 1));
           parser () st)
      end
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
fun action_25 () = (
 fn st => fn Base_token () => Base_token (BT_EOI,getLoc st lexbuf) )
and action_24 () = (
 fn st => fn Base_token () =>
           raise LEX_ERR ("Character \""^getLexeme ()^
                          "\" is a lexical error", getLoc st lexbuf) )
and action_23 () = (
 fn st as ref (nf,r,i,rcopt) => fn Base_token () =>
             (st := (nf,r+1,getLexemeEnd (),rcopt);
              base_token () st (Base_token ())) )
and action_22 () = (
 base_token () )
and action_21 () = (
 fn st as ref (nf,r,i,_) => fn Base_token () =>
     let val s = LocP(nf,r,getLexemeStart () - i)
         val String (str,e) = string () st (String [#"\""])
     in
       Base_token (BT_Ident (String.implode (List.rev str)),mkLoc st s e)
     end )
and action_20 () = (
 fn st => fn Base_token () =>
                   Base_token (BT_Ident (getLexeme ()),getLoc st lexbuf) )
and action_19 () = (
 fn st => fn Base_token () =>
     let val s = getLexeme ()
         val c = String.sub (s, size s - 1)
     in
       if Char.isAlpha c then
         Base_token (BT_Numeral(String.extract(s,0,SOME (size s - 1)), SOME c),
                     getLoc st lexbuf)
       else
         Base_token (BT_Numeral(s, NONE),getLoc st lexbuf)
     end )
and action_18 () = (
 fn st => fn Base_token () =>
           (fn Comment x => Base_token x) (comment () st (Comment 0)) )
and action_17 () = (
 dolocpragma base_token lexbuf )
and action_16 () = (
 fn st => fn Base_token () =>
     let val l = String.tokens (fn c => c = #"$") (getLexeme ())
     in Base_token (BT_QIdent (hd l, hd (tl l)),getLoc st lexbuf)
     end )
and action_15 () = (
 fn st => fn String acc =>
             string () st (String (getLexemeChar 0 :: acc)) )
and action_14 () = (
 fn st => raise LEX_ERR ("eof/antiquote inside quote-delimited string",getLoc st lexbuf) )
and action_13 () = (
 fn st => raise LEX_ERR ("newline inside quote-delimited string",getLoc st lexbuf) )
and action_12 () = (
 dolocpragma string lexbuf )
and action_11 () = (
 fn st => fn String acc => string () st (String (#"\r" :: acc)) )
and action_10 () = (
 fn st => fn String acc => string () st (String (#"\\" :: acc)) )
and action_9 () = (
 fn st => fn String acc => string () st (String (#"\"" :: acc)) )
and action_8 () = (
 fn st => fn String acc => string () st (String (#"\n" :: acc)) )
and action_7 () = (
 fn st as ref (nf,r,i,_) => fn String acc =>
             String (#"\"" :: acc, LocP(nf,r,getLexemeEnd () - i - 1)) )
and action_6 () = (
 comment () )
and action_5 () = (
 fn st as ref (nf,r,i,rcopt) => fn l =>
             (st := (nf,r+1,getLexemeEnd (),rcopt); comment () st l) )
and action_4 () = (
 fn st => fn Comment n => comment () st (Comment (n + 1)) )
and action_3 () = (
 dolocpragma comment lexbuf )
and action_2 () = (
 fn st => fn Comment n =>
             Comment (BT_InComment n, getLoc st lexbuf) )
and action_1 () = (
 fn st => fn Comment n =>
             if n = 0 then
               (fn Base_token x => Comment x)
               (base_token () st (Base_token ()))
             else comment () st (Comment (n - 1)) )
and action_0 () = (
 fn st => (fn l as Comment _ => comment () st l
                 | l as String _ => string () st l
                 | l as Base_token _ => base_token () st l))
and state_0 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\^@" => backtrack ()
 |  _ => action_0 ()
 end)
and state_1 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"*" => state_85 ()
 |  #"(" => state_84 ()
 |  #"\r" => state_83 ()
 |  #"\n" => action_5 ()
 |  #"\^@" => action_2 ()
 |  _ => action_6 ()
 end)
and state_2 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\\" => state_60 ()
 |  #"(" => state_59 ()
 |  #"\"" => action_7 ()
 |  #"\r" => state_57 ()
 |  #"\n" => action_13 ()
 |  #"\^@" => action_14 ()
 |  _ => action_15 ()
 end)
and state_3 () = (
 let val currChar = getNextChar () in
 if currChar >= #"A" andalso currChar <= #"Z" then  state_12 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_12 ()
 else if currChar >= #")" andalso currChar <= #"/" then  state_9 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_9 ()
 else if currChar >= #"0" andalso currChar <= #"9" then  state_14 ()
 else case currChar of
    #"'" => state_12 ()
 |  #"_" => state_12 ()
 |  #"!" => state_9 ()
 |  #"#" => state_9 ()
 |  #"&" => state_9 ()
 |  #"%" => state_9 ()
 |  #"]" => state_9 ()
 |  #"\\" => state_9 ()
 |  #"[" => state_9 ()
 |  #"~" => state_9 ()
 |  #"}" => state_9 ()
 |  #"|" => state_9 ()
 |  #"{" => state_9 ()
 |  #"\t" => action_22 ()
 |  #" " => action_22 ()
 |  #"(" => state_13 ()
 |  #"$" => state_11 ()
 |  #"\"" => action_21 ()
 |  #"\r" => state_8 ()
 |  #"\n" => action_23 ()
 |  #"\^@" => action_25 ()
 |  _ => action_24 ()
 end)
and state_8 () = (
 resetLastPos ();
 setLastAction action_23;
 let val currChar = getNextChar () in
 case currChar of
    #"\n" => action_23 ()
 |  _ => backtrack ()
 end)
and state_9 () = (
 resetLastPos ();
 setLastAction action_24;
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_49 ()
 else case currChar of
    #"!" => state_49 ()
 |  #"#" => state_49 ()
 |  #"&" => state_49 ()
 |  #"%" => state_49 ()
 |  #")" => state_49 ()
 |  #"/" => state_49 ()
 |  #"." => state_49 ()
 |  #"-" => state_49 ()
 |  #"," => state_49 ()
 |  #"+" => state_49 ()
 |  #"]" => state_49 ()
 |  #"\\" => state_49 ()
 |  #"[" => state_49 ()
 |  #"~" => state_49 ()
 |  #"}" => state_49 ()
 |  #"|" => state_49 ()
 |  #"{" => state_49 ()
 |  #"*" => state_50 ()
 |  #"(" => state_17 ()
 |  _ => backtrack ()
 end)
and state_11 () = (
 resetLastPos ();
 setLastAction action_24;
 let val currChar = getNextChar () in
 if currChar >= #"A" andalso currChar <= #"Z" then  state_47 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_47 ()
 else if currChar >= #")" andalso currChar <= #"/" then  state_46 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_46 ()
 else case currChar of
    #"'" => state_47 ()
 |  #"_" => state_47 ()
 |  #"!" => state_46 ()
 |  #"#" => state_46 ()
 |  #"&" => state_46 ()
 |  #"%" => state_46 ()
 |  #"]" => state_46 ()
 |  #"\\" => state_46 ()
 |  #"[" => state_46 ()
 |  #"~" => state_46 ()
 |  #"}" => state_46 ()
 |  #"|" => state_46 ()
 |  #"{" => state_46 ()
 |  #"(" => state_48 ()
 |  _ => backtrack ()
 end)
and state_12 () = (
 resetLastPos ();
 setLastAction action_24;
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_34 ()
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_34 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_34 ()
 else case currChar of
    #"'" => state_34 ()
 |  #"_" => state_34 ()
 |  #"(" => action_20 ()
 |  #"$" => state_33 ()
 |  _ => backtrack ()
 end)
and state_13 () = (
 resetLastPos ();
 setLastAction action_20;
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_17 ()
 else case currChar of
    #"!" => state_17 ()
 |  #"#" => state_17 ()
 |  #"&" => state_17 ()
 |  #"%" => state_17 ()
 |  #")" => state_17 ()
 |  #"(" => state_17 ()
 |  #"/" => state_17 ()
 |  #"." => state_17 ()
 |  #"-" => state_17 ()
 |  #"," => state_17 ()
 |  #"+" => state_17 ()
 |  #"]" => state_17 ()
 |  #"\\" => state_17 ()
 |  #"[" => state_17 ()
 |  #"~" => state_17 ()
 |  #"}" => state_17 ()
 |  #"|" => state_17 ()
 |  #"{" => state_17 ()
 |  #"*" => state_18 ()
 |  _ => backtrack ()
 end)
and state_14 () = (
 resetLastPos ();
 setLastAction action_19;
 let val currChar = getNextChar () in
 if currChar >= #"A" andalso currChar <= #"Z" then  action_19 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  action_19 ()
 else if currChar >= #"0" andalso currChar <= #"9" then  state_16 ()
 else case currChar of
    #"'" => action_19 ()
 |  #"_" => action_19 ()
 |  _ => backtrack ()
 end)
and state_16 () = (
 resetLastPos ();
 setLastAction action_19;
 let val currChar = getNextChar () in
 if currChar >= #"A" andalso currChar <= #"Z" then  action_19 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  action_19 ()
 else if currChar >= #"0" andalso currChar <= #"9" then  state_16 ()
 else case currChar of
    #"'" => action_19 ()
 |  #"_" => action_19 ()
 |  _ => backtrack ()
 end)
and state_17 () = (
 resetLastPos ();
 setLastAction action_20;
 let val currChar = getNextChar () in
 if currChar >= #"(" andalso currChar <= #"/" then  state_32 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_32 ()
 else case currChar of
    #"!" => state_32 ()
 |  #"#" => state_32 ()
 |  #"&" => state_32 ()
 |  #"%" => state_32 ()
 |  #"]" => state_32 ()
 |  #"\\" => state_32 ()
 |  #"[" => state_32 ()
 |  #"~" => state_32 ()
 |  #"}" => state_32 ()
 |  #"|" => state_32 ()
 |  #"{" => state_32 ()
 |  _ => backtrack ()
 end)
and state_18 () = (
 resetLastPos ();
 setLastAction action_18;
 let val currChar = getNextChar () in
 case currChar of
    #"#" => state_19 ()
 |  _ => backtrack ()
 end)
and state_19 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"l" => state_20 ()
 |  _ => backtrack ()
 end)
and state_20 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"o" => state_21 ()
 |  _ => backtrack ()
 end)
and state_21 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"c" => state_22 ()
 |  _ => backtrack ()
 end)
and state_22 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\t" => state_23 ()
 |  #" " => state_23 ()
 |  _ => backtrack ()
 end)
and state_23 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_25 ()
 else case currChar of
    #"\t" => state_24 ()
 |  #" " => state_24 ()
 |  _ => backtrack ()
 end)
and state_24 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_31 ()
 else case currChar of
    #"\t" => state_24 ()
 |  #" " => state_24 ()
 |  #"*" => state_27 ()
 |  _ => backtrack ()
 end)
and state_25 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_25 ()
 else case currChar of
    #"\t" => state_26 ()
 |  #" " => state_26 ()
 |  _ => backtrack ()
 end)
and state_26 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_28 ()
 else case currChar of
    #"\t" => state_26 ()
 |  #" " => state_26 ()
 |  #"*" => state_27 ()
 |  _ => backtrack ()
 end)
and state_27 () = (
 let val currChar = getNextChar () in
 case currChar of
    #")" => action_17 ()
 |  _ => backtrack ()
 end)
and state_28 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_28 ()
 else case currChar of
    #"\t" => state_29 ()
 |  #" " => state_29 ()
 |  #"*" => state_27 ()
 |  _ => backtrack ()
 end)
and state_29 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\t" => state_29 ()
 |  #" " => state_29 ()
 |  #"*" => state_27 ()
 |  _ => backtrack ()
 end)
and state_31 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_31 ()
 else case currChar of
    #"\t" => state_26 ()
 |  #" " => state_26 ()
 |  #"*" => state_27 ()
 |  _ => backtrack ()
 end)
and state_32 () = (
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_17 ()
 else case currChar of
    #"!" => state_17 ()
 |  #"#" => state_17 ()
 |  #"&" => state_17 ()
 |  #"%" => state_17 ()
 |  #")" => state_17 ()
 |  #"(" => state_17 ()
 |  #"/" => state_17 ()
 |  #"." => state_17 ()
 |  #"-" => state_17 ()
 |  #"," => state_17 ()
 |  #"+" => state_17 ()
 |  #"]" => state_17 ()
 |  #"\\" => state_17 ()
 |  #"[" => state_17 ()
 |  #"~" => state_17 ()
 |  #"}" => state_17 ()
 |  #"|" => state_17 ()
 |  #"{" => state_17 ()
 |  _ => backtrack ()
 end)
and state_33 () = (
 let val currChar = getNextChar () in
 if currChar >= #"A" andalso currChar <= #"Z" then  state_37 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_37 ()
 else if currChar >= #")" andalso currChar <= #"/" then  state_36 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_36 ()
 else case currChar of
    #"'" => state_37 ()
 |  #"_" => state_37 ()
 |  #"!" => state_36 ()
 |  #"#" => state_36 ()
 |  #"&" => state_36 ()
 |  #"%" => state_36 ()
 |  #"]" => state_36 ()
 |  #"\\" => state_36 ()
 |  #"[" => state_36 ()
 |  #"~" => state_36 ()
 |  #"}" => state_36 ()
 |  #"|" => state_36 ()
 |  #"{" => state_36 ()
 |  #"(" => state_38 ()
 |  _ => backtrack ()
 end)
and state_34 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_34 ()
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_34 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_34 ()
 else case currChar of
    #"'" => state_34 ()
 |  #"_" => state_34 ()
 |  #"(" => action_20 ()
 |  #"$" => state_33 ()
 |  _ => backtrack ()
 end)
and state_36 () = (
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_42 ()
 else case currChar of
    #"!" => state_42 ()
 |  #"#" => state_42 ()
 |  #"&" => state_42 ()
 |  #"%" => state_42 ()
 |  #")" => state_42 ()
 |  #"/" => state_42 ()
 |  #"." => state_42 ()
 |  #"-" => state_42 ()
 |  #"," => state_42 ()
 |  #"+" => state_42 ()
 |  #"]" => state_42 ()
 |  #"\\" => state_42 ()
 |  #"[" => state_42 ()
 |  #"~" => state_42 ()
 |  #"}" => state_42 ()
 |  #"|" => state_42 ()
 |  #"{" => state_42 ()
 |  #"*" => state_43 ()
 |  #"(" => state_39 ()
 |  _ => backtrack ()
 end)
and state_37 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_37 ()
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_37 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_37 ()
 else case currChar of
    #"'" => state_37 ()
 |  #"_" => state_37 ()
 |  #"(" => action_16 ()
 |  _ => backtrack ()
 end)
and state_38 () = (
 resetLastPos ();
 setLastAction action_16;
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_39 ()
 else case currChar of
    #"!" => state_39 ()
 |  #"#" => state_39 ()
 |  #"&" => state_39 ()
 |  #"%" => state_39 ()
 |  #")" => state_39 ()
 |  #"(" => state_39 ()
 |  #"/" => state_39 ()
 |  #"." => state_39 ()
 |  #"-" => state_39 ()
 |  #"," => state_39 ()
 |  #"+" => state_39 ()
 |  #"]" => state_39 ()
 |  #"\\" => state_39 ()
 |  #"[" => state_39 ()
 |  #"~" => state_39 ()
 |  #"}" => state_39 ()
 |  #"|" => state_39 ()
 |  #"{" => state_39 ()
 |  _ => backtrack ()
 end)
and state_39 () = (
 resetLastPos ();
 setLastAction action_16;
 let val currChar = getNextChar () in
 if currChar >= #"(" andalso currChar <= #"/" then  state_40 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_40 ()
 else case currChar of
    #"!" => state_40 ()
 |  #"#" => state_40 ()
 |  #"&" => state_40 ()
 |  #"%" => state_40 ()
 |  #"]" => state_40 ()
 |  #"\\" => state_40 ()
 |  #"[" => state_40 ()
 |  #"~" => state_40 ()
 |  #"}" => state_40 ()
 |  #"|" => state_40 ()
 |  #"{" => state_40 ()
 |  _ => backtrack ()
 end)
and state_40 () = (
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_39 ()
 else case currChar of
    #"!" => state_39 ()
 |  #"#" => state_39 ()
 |  #"&" => state_39 ()
 |  #"%" => state_39 ()
 |  #")" => state_39 ()
 |  #"(" => state_39 ()
 |  #"/" => state_39 ()
 |  #"." => state_39 ()
 |  #"-" => state_39 ()
 |  #"," => state_39 ()
 |  #"+" => state_39 ()
 |  #"]" => state_39 ()
 |  #"\\" => state_39 ()
 |  #"[" => state_39 ()
 |  #"~" => state_39 ()
 |  #"}" => state_39 ()
 |  #"|" => state_39 ()
 |  #"{" => state_39 ()
 |  _ => backtrack ()
 end)
and state_42 () = (
 resetLastPos ();
 setLastAction action_16;
 let val currChar = getNextChar () in
 if currChar >= #")" andalso currChar <= #"/" then  state_44 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_44 ()
 else case currChar of
    #"!" => state_44 ()
 |  #"#" => state_44 ()
 |  #"&" => state_44 ()
 |  #"%" => state_44 ()
 |  #"]" => state_44 ()
 |  #"\\" => state_44 ()
 |  #"[" => state_44 ()
 |  #"~" => state_44 ()
 |  #"}" => state_44 ()
 |  #"|" => state_44 ()
 |  #"{" => state_44 ()
 |  #"(" => state_45 ()
 |  _ => backtrack ()
 end)
and state_43 () = (
 let val currChar = getNextChar () in
 if currChar >= #")" andalso currChar <= #"/" then  state_43 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_43 ()
 else case currChar of
    #"!" => state_43 ()
 |  #"#" => state_43 ()
 |  #"&" => state_43 ()
 |  #"%" => state_43 ()
 |  #"]" => state_43 ()
 |  #"\\" => state_43 ()
 |  #"[" => state_43 ()
 |  #"~" => state_43 ()
 |  #"}" => state_43 ()
 |  #"|" => state_43 ()
 |  #"{" => state_43 ()
 |  #"(" => action_16 ()
 |  _ => backtrack ()
 end)
and state_44 () = (
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_42 ()
 else case currChar of
    #"!" => state_42 ()
 |  #"#" => state_42 ()
 |  #"&" => state_42 ()
 |  #"%" => state_42 ()
 |  #")" => state_42 ()
 |  #"/" => state_42 ()
 |  #"." => state_42 ()
 |  #"-" => state_42 ()
 |  #"," => state_42 ()
 |  #"+" => state_42 ()
 |  #"]" => state_42 ()
 |  #"\\" => state_42 ()
 |  #"[" => state_42 ()
 |  #"~" => state_42 ()
 |  #"}" => state_42 ()
 |  #"|" => state_42 ()
 |  #"{" => state_42 ()
 |  #"*" => state_43 ()
 |  #"(" => state_39 ()
 |  _ => backtrack ()
 end)
and state_45 () = (
 resetLastPos ();
 setLastAction action_16;
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_39 ()
 else case currChar of
    #"!" => state_39 ()
 |  #"#" => state_39 ()
 |  #"&" => state_39 ()
 |  #"%" => state_39 ()
 |  #")" => state_39 ()
 |  #"(" => state_39 ()
 |  #"/" => state_39 ()
 |  #"." => state_39 ()
 |  #"-" => state_39 ()
 |  #"," => state_39 ()
 |  #"+" => state_39 ()
 |  #"]" => state_39 ()
 |  #"\\" => state_39 ()
 |  #"[" => state_39 ()
 |  #"~" => state_39 ()
 |  #"}" => state_39 ()
 |  #"|" => state_39 ()
 |  #"{" => state_39 ()
 |  _ => backtrack ()
 end)
and state_46 () = (
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_49 ()
 else case currChar of
    #"!" => state_49 ()
 |  #"#" => state_49 ()
 |  #"&" => state_49 ()
 |  #"%" => state_49 ()
 |  #")" => state_49 ()
 |  #"/" => state_49 ()
 |  #"." => state_49 ()
 |  #"-" => state_49 ()
 |  #"," => state_49 ()
 |  #"+" => state_49 ()
 |  #"]" => state_49 ()
 |  #"\\" => state_49 ()
 |  #"[" => state_49 ()
 |  #"~" => state_49 ()
 |  #"}" => state_49 ()
 |  #"|" => state_49 ()
 |  #"{" => state_49 ()
 |  #"*" => state_50 ()
 |  #"(" => state_17 ()
 |  _ => backtrack ()
 end)
and state_47 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_47 ()
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_47 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_47 ()
 else case currChar of
    #"'" => state_47 ()
 |  #"_" => state_47 ()
 |  #"(" => action_20 ()
 |  _ => backtrack ()
 end)
and state_48 () = (
 resetLastPos ();
 setLastAction action_20;
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_17 ()
 else case currChar of
    #"!" => state_17 ()
 |  #"#" => state_17 ()
 |  #"&" => state_17 ()
 |  #"%" => state_17 ()
 |  #")" => state_17 ()
 |  #"(" => state_17 ()
 |  #"/" => state_17 ()
 |  #"." => state_17 ()
 |  #"-" => state_17 ()
 |  #"," => state_17 ()
 |  #"+" => state_17 ()
 |  #"]" => state_17 ()
 |  #"\\" => state_17 ()
 |  #"[" => state_17 ()
 |  #"~" => state_17 ()
 |  #"}" => state_17 ()
 |  #"|" => state_17 ()
 |  #"{" => state_17 ()
 |  _ => backtrack ()
 end)
and state_49 () = (
 resetLastPos ();
 setLastAction action_20;
 let val currChar = getNextChar () in
 if currChar >= #")" andalso currChar <= #"/" then  state_51 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_51 ()
 else case currChar of
    #"!" => state_51 ()
 |  #"#" => state_51 ()
 |  #"&" => state_51 ()
 |  #"%" => state_51 ()
 |  #"]" => state_51 ()
 |  #"\\" => state_51 ()
 |  #"[" => state_51 ()
 |  #"~" => state_51 ()
 |  #"}" => state_51 ()
 |  #"|" => state_51 ()
 |  #"{" => state_51 ()
 |  #"(" => state_52 ()
 |  _ => backtrack ()
 end)
and state_50 () = (
 let val currChar = getNextChar () in
 if currChar >= #")" andalso currChar <= #"/" then  state_50 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_50 ()
 else case currChar of
    #"!" => state_50 ()
 |  #"#" => state_50 ()
 |  #"&" => state_50 ()
 |  #"%" => state_50 ()
 |  #"]" => state_50 ()
 |  #"\\" => state_50 ()
 |  #"[" => state_50 ()
 |  #"~" => state_50 ()
 |  #"}" => state_50 ()
 |  #"|" => state_50 ()
 |  #"{" => state_50 ()
 |  #"(" => action_20 ()
 |  _ => backtrack ()
 end)
and state_51 () = (
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_49 ()
 else case currChar of
    #"!" => state_49 ()
 |  #"#" => state_49 ()
 |  #"&" => state_49 ()
 |  #"%" => state_49 ()
 |  #")" => state_49 ()
 |  #"/" => state_49 ()
 |  #"." => state_49 ()
 |  #"-" => state_49 ()
 |  #"," => state_49 ()
 |  #"+" => state_49 ()
 |  #"]" => state_49 ()
 |  #"\\" => state_49 ()
 |  #"[" => state_49 ()
 |  #"~" => state_49 ()
 |  #"}" => state_49 ()
 |  #"|" => state_49 ()
 |  #"{" => state_49 ()
 |  #"*" => state_50 ()
 |  #"(" => state_17 ()
 |  _ => backtrack ()
 end)
and state_52 () = (
 resetLastPos ();
 setLastAction action_20;
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_17 ()
 else case currChar of
    #"!" => state_17 ()
 |  #"#" => state_17 ()
 |  #"&" => state_17 ()
 |  #"%" => state_17 ()
 |  #")" => state_17 ()
 |  #"(" => state_17 ()
 |  #"/" => state_17 ()
 |  #"." => state_17 ()
 |  #"-" => state_17 ()
 |  #"," => state_17 ()
 |  #"+" => state_17 ()
 |  #"]" => state_17 ()
 |  #"\\" => state_17 ()
 |  #"[" => state_17 ()
 |  #"~" => state_17 ()
 |  #"}" => state_17 ()
 |  #"|" => state_17 ()
 |  #"{" => state_17 ()
 |  _ => backtrack ()
 end)
and state_57 () = (
 resetLastPos ();
 setLastAction action_13;
 let val currChar = getNextChar () in
 case currChar of
    #"\n" => action_13 ()
 |  _ => backtrack ()
 end)
and state_59 () = (
 resetLastPos ();
 setLastAction action_15;
 let val currChar = getNextChar () in
 case currChar of
    #"*" => state_65 ()
 |  _ => backtrack ()
 end)
and state_60 () = (
 resetLastPos ();
 setLastAction action_15;
 let val currChar = getNextChar () in
 case currChar of
    #"r" => action_11 ()
 |  #"n" => action_8 ()
 |  #"\\" => action_10 ()
 |  #"\"" => action_9 ()
 |  _ => backtrack ()
 end)
and state_65 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"#" => state_66 ()
 |  _ => backtrack ()
 end)
and state_66 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"l" => state_67 ()
 |  _ => backtrack ()
 end)
and state_67 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"o" => state_68 ()
 |  _ => backtrack ()
 end)
and state_68 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"c" => state_69 ()
 |  _ => backtrack ()
 end)
and state_69 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\t" => state_70 ()
 |  #" " => state_70 ()
 |  _ => backtrack ()
 end)
and state_70 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_72 ()
 else case currChar of
    #"\t" => state_71 ()
 |  #" " => state_71 ()
 |  _ => backtrack ()
 end)
and state_71 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_78 ()
 else case currChar of
    #"\t" => state_71 ()
 |  #" " => state_71 ()
 |  #"*" => state_74 ()
 |  _ => backtrack ()
 end)
and state_72 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_72 ()
 else case currChar of
    #"\t" => state_73 ()
 |  #" " => state_73 ()
 |  _ => backtrack ()
 end)
and state_73 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_75 ()
 else case currChar of
    #"\t" => state_73 ()
 |  #" " => state_73 ()
 |  #"*" => state_74 ()
 |  _ => backtrack ()
 end)
and state_74 () = (
 let val currChar = getNextChar () in
 case currChar of
    #")" => action_12 ()
 |  _ => backtrack ()
 end)
and state_75 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_75 ()
 else case currChar of
    #"\t" => state_76 ()
 |  #" " => state_76 ()
 |  #"*" => state_74 ()
 |  _ => backtrack ()
 end)
and state_76 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\t" => state_76 ()
 |  #" " => state_76 ()
 |  #"*" => state_74 ()
 |  _ => backtrack ()
 end)
and state_78 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_78 ()
 else case currChar of
    #"\t" => state_73 ()
 |  #" " => state_73 ()
 |  #"*" => state_74 ()
 |  _ => backtrack ()
 end)
and state_83 () = (
 resetLastPos ();
 setLastAction action_5;
 let val currChar = getNextChar () in
 case currChar of
    #"\n" => action_5 ()
 |  _ => backtrack ()
 end)
and state_84 () = (
 resetLastPos ();
 setLastAction action_6;
 let val currChar = getNextChar () in
 case currChar of
    #"*" => state_87 ()
 |  _ => backtrack ()
 end)
and state_85 () = (
 resetLastPos ();
 setLastAction action_6;
 let val currChar = getNextChar () in
 case currChar of
    #")" => action_1 ()
 |  _ => backtrack ()
 end)
and state_87 () = (
 resetLastPos ();
 setLastAction action_4;
 let val currChar = getNextChar () in
 case currChar of
    #"#" => state_88 ()
 |  _ => backtrack ()
 end)
and state_88 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"l" => state_89 ()
 |  _ => backtrack ()
 end)
and state_89 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"o" => state_90 ()
 |  _ => backtrack ()
 end)
and state_90 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"c" => state_91 ()
 |  _ => backtrack ()
 end)
and state_91 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\t" => state_92 ()
 |  #" " => state_92 ()
 |  _ => backtrack ()
 end)
and state_92 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_94 ()
 else case currChar of
    #"\t" => state_93 ()
 |  #" " => state_93 ()
 |  _ => backtrack ()
 end)
and state_93 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_100 ()
 else case currChar of
    #"\t" => state_93 ()
 |  #" " => state_93 ()
 |  #"*" => state_96 ()
 |  _ => backtrack ()
 end)
and state_94 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_94 ()
 else case currChar of
    #"\t" => state_95 ()
 |  #" " => state_95 ()
 |  _ => backtrack ()
 end)
and state_95 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_97 ()
 else case currChar of
    #"\t" => state_95 ()
 |  #" " => state_95 ()
 |  #"*" => state_96 ()
 |  _ => backtrack ()
 end)
and state_96 () = (
 let val currChar = getNextChar () in
 case currChar of
    #")" => action_3 ()
 |  _ => backtrack ()
 end)
and state_97 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_97 ()
 else case currChar of
    #"\t" => state_98 ()
 |  #" " => state_98 ()
 |  #"*" => state_96 ()
 |  _ => backtrack ()
 end)
and state_98 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\t" => state_98 ()
 |  #" " => state_98 ()
 |  #"*" => state_96 ()
 |  _ => backtrack ()
 end)
and state_100 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_100 ()
 else case currChar of
    #"\t" => state_95 ()
 |  #" " => state_95 ()
 |  #"*" => state_96 ()
 |  _ => backtrack ()
 end)
and base_token () =
  (resetStartPos ();
   state_3 ())

and string () =
  (resetStartPos ();
   state_2 ())

and comment () =
  (resetStartPos ();
   state_1 ())

and main () =
  (resetStartPos ();
   state_0 ())

(* The following checks type consistency of actions *)
val _ = fn _ => [action_25, action_24, action_23, action_22, action_21, action_20, action_19, action_18, action_17, action_16];
val _ = fn _ => [action_15, action_14, action_13, action_12, action_11, action_10, action_9, action_8, action_7];
val _ = fn _ => [action_6, action_5, action_4, action_3, action_2, action_1];
in main
 end

  fun base_token lexbuf st =
    (fn Base_token x => x) (makeLex lexbuf () st (Base_token ()));

  fun comment lexbuf st n =
    (fn Comment x => x) (makeLex lexbuf () st (Comment n));

  end
