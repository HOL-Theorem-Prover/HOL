  structure base_lexer =
  struct

  open LexBuffer base_tokens locn

  datatype ('a,'b,'c) lextype =
    Base_token of 'a
  | String of 'b
  | Comment of 'c;

  fun magic x = x;

  type extrastate = (int * int * int * (int * int) option) ref
  (* mutable state argument to each rule is st=(nf,r,i,rcopt), where:
       - nf  is the number of the fragment being parsed
       - r   is the current row number
       - i   is the index of the first char on the current row
       - rcopt is the absolute line and character of the start of this fragment, if known
  *)

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

fun makeLex lexbuf =
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
fun dummyAction () = LexBuffer.dummyAction lexbuf

fun action_24 () = (
 fn st => fn Base_token () => Base_token (BT_EOI,getLoc st lexbuf) )
and action_23 () = (
 fn st => fn Base_token () =>
           raise LEX_ERR ("Character \""^getLexeme ()^
                          "\" is a lexical error", getLoc st lexbuf) )
and action_22 () = (
 fn st as ref (nf,r,i,rcopt) => fn Base_token () =>
             (st := (nf,r+1,getLexemeEnd (),rcopt);
              base_token () st (Base_token ())) )
and action_21 () = (
 base_token () )
and action_20 () = (
 fn st as ref (nf,r,i,_) => fn Base_token () =>
     let val s = LocP(nf,r,getLexemeStart () - i)
         val String (str,e) = string () st (String [#"\""])
     in
       Base_token (BT_Ident (String.implode (List.rev str)),mkLoc st s e)
     end )
and action_19 () = (
 fn st => fn Base_token () =>
                   Base_token (BT_Ident (getLexeme ()),getLoc st lexbuf) )
and action_18 () = (
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
and action_17 () = (
 fn st => fn Base_token () =>
           (fn Comment x => Base_token x) (comment () st (Comment 0)) )
and action_16 () = (
 dolocpragma base_token lexbuf )
and action_15 () = (
 fn st => fn Base_token () =>
     let val l = String.tokens (fn c => c = #"$") (getLexeme ())
     in Base_token (BT_QIdent (hd l, hd (tl l)),getLoc st lexbuf)
     end )
and action_14 () = (
 fn st => fn String acc =>
             string () st (String (getLexemeChar 0 :: acc)) )
and action_13 () = (
 fn st => raise LEX_ERR ("eof/antiquote inside quote-delimited string",getLoc st lexbuf) )
and action_12 () = (
 fn st => raise LEX_ERR ("newline inside quote-delimited string",getLoc st lexbuf) )
and action_11 () = (
 dolocpragma string lexbuf )
and action_10 () = (
 fn st => fn String acc => string () st (String (#"\r" :: acc)) )
and action_9 () = (
 fn st => fn String acc => string () st (String (#"\\" :: acc)) )
and action_8 () = (
 fn st => fn String acc => string () st (String (#"\"" :: acc)) )
and action_7 () = (
 fn st => fn String acc => string () st (String (#"\n" :: acc)) )
and action_6 () = (
 fn st as ref (nf,r,i,_) => fn String acc =>
             String (#"\"" :: acc, LocP(nf,r,getLexemeEnd () - i - 1)) )
and action_5 () = (
 comment () )
and action_4 () = (
 fn st as ref (nf,r,i,rcopt) => fn l =>
             (st := (nf,r+1,getLexemeEnd (),rcopt); comment () st l) )
and action_3 () = (
 fn st => fn Comment n => comment () st (Comment (n + 1)) )
and action_2 () = (
 dolocpragma comment lexbuf )
and action_1 () = (
 fn st => fn Comment n =>
             Comment (BT_InComment n, getLoc st lexbuf) )
and action_0 () = (
 fn st => fn Comment n =>
             if n = 0 then
               (fn Base_token x => Comment x)
               (base_token () st (Base_token ()))
             else comment () st (Comment (n - 1)) )
and state_0 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"*" => state_77 ()
 |  #"(" => state_76 ()
 |  #"\r" => state_75 ()
 |  #"\n" => action_4 ()
 |  #"\^@" => action_1 ()
 |  _ => action_5 ()
 end)
and state_1 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\\" => state_52 ()
 |  #"(" => state_51 ()
 |  #"\"" => action_6 ()
 |  #"\r" => state_49 ()
 |  #"\n" => action_12 ()
 |  #"\^@" => action_13 ()
 |  _ => action_14 ()
 end)
and state_2 () = (
 let val currChar = getNextChar () in
 if currChar >= #"A" andalso currChar <= #"Z" then  state_11 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_11 ()
 else if currChar >= #")" andalso currChar <= #"/" then  state_8 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_8 ()
 else if currChar >= #"0" andalso currChar <= #"9" then  state_13 ()
 else case currChar of
    #"'" => state_11 ()
 |  #"_" => state_11 ()
 |  #"!" => state_8 ()
 |  #"#" => state_8 ()
 |  #"&" => state_8 ()
 |  #"%" => state_8 ()
 |  #"]" => state_8 ()
 |  #"\\" => state_8 ()
 |  #"[" => state_8 ()
 |  #"~" => state_8 ()
 |  #"}" => state_8 ()
 |  #"|" => state_8 ()
 |  #"{" => state_8 ()
 |  #"\t" => action_21 ()
 |  #" " => action_21 ()
 |  #"(" => state_12 ()
 |  #"$" => state_10 ()
 |  #"\"" => action_20 ()
 |  #"\r" => state_7 ()
 |  #"\n" => action_22 ()
 |  #"\^@" => action_24 ()
 |  _ => action_23 ()
 end)
and state_7 () = (
 resetLastPos ();
 setLastAction (magic action_22);
 let val currChar = getNextChar () in
 case currChar of
    #"\n" => action_22 ()
 |  _ => backtrack ()
 end)
and state_8 () = (
 resetLastPos ();
 setLastAction (magic action_19);
 let val currChar = getNextChar () in
 if currChar >= #")" andalso currChar <= #"/" then  state_41 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_41 ()
 else case currChar of
    #"!" => state_41 ()
 |  #"#" => state_41 ()
 |  #"&" => state_41 ()
 |  #"%" => state_41 ()
 |  #"]" => state_41 ()
 |  #"\\" => state_41 ()
 |  #"[" => state_41 ()
 |  #"~" => state_41 ()
 |  #"}" => state_41 ()
 |  #"|" => state_41 ()
 |  #"{" => state_41 ()
 |  #"(" => state_44 ()
 |  _ => backtrack ()
 end)
and state_10 () = (
 resetLastPos ();
 setLastAction (magic action_23);
 let val currChar = getNextChar () in
 if currChar >= #"A" andalso currChar <= #"Z" then  state_42 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_42 ()
 else if currChar >= #")" andalso currChar <= #"/" then  state_41 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_41 ()
 else case currChar of
    #"'" => state_42 ()
 |  #"_" => state_42 ()
 |  #"!" => state_41 ()
 |  #"#" => state_41 ()
 |  #"&" => state_41 ()
 |  #"%" => state_41 ()
 |  #"]" => state_41 ()
 |  #"\\" => state_41 ()
 |  #"[" => state_41 ()
 |  #"~" => state_41 ()
 |  #"}" => state_41 ()
 |  #"|" => state_41 ()
 |  #"{" => state_41 ()
 |  #"(" => state_43 ()
 |  _ => backtrack ()
 end)
and state_11 () = (
 resetLastPos ();
 setLastAction (magic action_19);
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_33 ()
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_33 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_33 ()
 else case currChar of
    #"'" => state_33 ()
 |  #"_" => state_33 ()
 |  #"$" => state_32 ()
 |  _ => backtrack ()
 end)
and state_12 () = (
 resetLastPos ();
 setLastAction (magic action_19);
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_16 ()
 else case currChar of
    #"!" => state_16 ()
 |  #"#" => state_16 ()
 |  #"&" => state_16 ()
 |  #"%" => state_16 ()
 |  #")" => state_16 ()
 |  #"(" => state_16 ()
 |  #"/" => state_16 ()
 |  #"." => state_16 ()
 |  #"-" => state_16 ()
 |  #"," => state_16 ()
 |  #"+" => state_16 ()
 |  #"]" => state_16 ()
 |  #"\\" => state_16 ()
 |  #"[" => state_16 ()
 |  #"~" => state_16 ()
 |  #"}" => state_16 ()
 |  #"|" => state_16 ()
 |  #"{" => state_16 ()
 |  #"*" => state_17 ()
 |  _ => backtrack ()
 end)
and state_13 () = (
 resetLastPos ();
 setLastAction (magic action_18);
 let val currChar = getNextChar () in
 if currChar >= #"A" andalso currChar <= #"Z" then  action_18 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  action_18 ()
 else if currChar >= #"0" andalso currChar <= #"9" then  state_15 ()
 else case currChar of
    #"'" => action_18 ()
 |  #"_" => action_18 ()
 |  _ => backtrack ()
 end)
and state_15 () = (
 resetLastPos ();
 setLastAction (magic action_18);
 let val currChar = getNextChar () in
 if currChar >= #"A" andalso currChar <= #"Z" then  action_18 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  action_18 ()
 else if currChar >= #"0" andalso currChar <= #"9" then  state_15 ()
 else case currChar of
    #"'" => action_18 ()
 |  #"_" => action_18 ()
 |  _ => backtrack ()
 end)
and state_16 () = (
 resetLastPos ();
 setLastAction (magic action_19);
 let val currChar = getNextChar () in
 if currChar >= #")" andalso currChar <= #"/" then  state_16 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_16 ()
 else case currChar of
    #"!" => state_16 ()
 |  #"#" => state_16 ()
 |  #"&" => state_16 ()
 |  #"%" => state_16 ()
 |  #"]" => state_16 ()
 |  #"\\" => state_16 ()
 |  #"[" => state_16 ()
 |  #"~" => state_16 ()
 |  #"}" => state_16 ()
 |  #"|" => state_16 ()
 |  #"{" => state_16 ()
 |  #"(" => state_31 ()
 |  _ => backtrack ()
 end)
and state_17 () = (
 resetLastPos ();
 setLastAction (magic action_17);
 let val currChar = getNextChar () in
 case currChar of
    #"#" => state_18 ()
 |  _ => backtrack ()
 end)
and state_18 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"l" => state_19 ()
 |  _ => backtrack ()
 end)
and state_19 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"o" => state_20 ()
 |  _ => backtrack ()
 end)
and state_20 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"c" => state_21 ()
 |  _ => backtrack ()
 end)
and state_21 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\t" => state_22 ()
 |  #" " => state_22 ()
 |  _ => backtrack ()
 end)
and state_22 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_24 ()
 else case currChar of
    #"\t" => state_23 ()
 |  #" " => state_23 ()
 |  _ => backtrack ()
 end)
and state_23 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_30 ()
 else case currChar of
    #"\t" => state_23 ()
 |  #" " => state_23 ()
 |  #"*" => state_26 ()
 |  _ => backtrack ()
 end)
and state_24 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_24 ()
 else case currChar of
    #"\t" => state_25 ()
 |  #" " => state_25 ()
 |  _ => backtrack ()
 end)
and state_25 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_27 ()
 else case currChar of
    #"\t" => state_25 ()
 |  #" " => state_25 ()
 |  #"*" => state_26 ()
 |  _ => backtrack ()
 end)
and state_26 () = (
 let val currChar = getNextChar () in
 case currChar of
    #")" => action_16 ()
 |  _ => backtrack ()
 end)
and state_27 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_27 ()
 else case currChar of
    #"\t" => state_28 ()
 |  #" " => state_28 ()
 |  #"*" => state_26 ()
 |  _ => backtrack ()
 end)
and state_28 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\t" => state_28 ()
 |  #" " => state_28 ()
 |  #"*" => state_26 ()
 |  _ => backtrack ()
 end)
and state_30 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_30 ()
 else case currChar of
    #"\t" => state_25 ()
 |  #" " => state_25 ()
 |  #"*" => state_26 ()
 |  _ => backtrack ()
 end)
and state_31 () = (
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_16 ()
 else case currChar of
    #"!" => state_16 ()
 |  #"#" => state_16 ()
 |  #"&" => state_16 ()
 |  #"%" => state_16 ()
 |  #")" => state_16 ()
 |  #"(" => state_16 ()
 |  #"/" => state_16 ()
 |  #"." => state_16 ()
 |  #"-" => state_16 ()
 |  #"," => state_16 ()
 |  #"+" => state_16 ()
 |  #"]" => state_16 ()
 |  #"\\" => state_16 ()
 |  #"[" => state_16 ()
 |  #"~" => state_16 ()
 |  #"}" => state_16 ()
 |  #"|" => state_16 ()
 |  #"{" => state_16 ()
 |  _ => backtrack ()
 end)
and state_32 () = (
 let val currChar = getNextChar () in
 if currChar >= #"A" andalso currChar <= #"Z" then  state_35 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_35 ()
 else if currChar >= #")" andalso currChar <= #"/" then  state_34 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_34 ()
 else if currChar >= #"0" andalso currChar <= #"9" then  state_37 ()
 else case currChar of
    #"'" => state_35 ()
 |  #"_" => state_35 ()
 |  #"!" => state_34 ()
 |  #"#" => state_34 ()
 |  #"&" => state_34 ()
 |  #"%" => state_34 ()
 |  #"]" => state_34 ()
 |  #"\\" => state_34 ()
 |  #"[" => state_34 ()
 |  #"~" => state_34 ()
 |  #"}" => state_34 ()
 |  #"|" => state_34 ()
 |  #"{" => state_34 ()
 |  #"(" => state_36 ()
 |  _ => backtrack ()
 end)
and state_33 () = (
 resetLastPos ();
 setLastAction (magic action_19);
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_33 ()
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_33 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_33 ()
 else case currChar of
    #"'" => state_33 ()
 |  #"_" => state_33 ()
 |  #"$" => state_32 ()
 |  _ => backtrack ()
 end)
and state_34 () = (
 resetLastPos ();
 setLastAction (magic action_15);
 let val currChar = getNextChar () in
 if currChar >= #")" andalso currChar <= #"/" then  state_34 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_34 ()
 else case currChar of
    #"!" => state_34 ()
 |  #"#" => state_34 ()
 |  #"&" => state_34 ()
 |  #"%" => state_34 ()
 |  #"]" => state_34 ()
 |  #"\\" => state_34 ()
 |  #"[" => state_34 ()
 |  #"~" => state_34 ()
 |  #"}" => state_34 ()
 |  #"|" => state_34 ()
 |  #"{" => state_34 ()
 |  #"(" => state_40 ()
 |  _ => backtrack ()
 end)
and state_35 () = (
 resetLastPos ();
 setLastAction (magic action_15);
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_35 ()
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_35 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_35 ()
 else case currChar of
    #"'" => state_35 ()
 |  #"_" => state_35 ()
 |  _ => backtrack ()
 end)
and state_36 () = (
 resetLastPos ();
 setLastAction (magic action_15);
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_38 ()
 else case currChar of
    #"!" => state_38 ()
 |  #"#" => state_38 ()
 |  #"&" => state_38 ()
 |  #"%" => state_38 ()
 |  #")" => state_38 ()
 |  #"(" => state_38 ()
 |  #"/" => state_38 ()
 |  #"." => state_38 ()
 |  #"-" => state_38 ()
 |  #"," => state_38 ()
 |  #"+" => state_38 ()
 |  #"]" => state_38 ()
 |  #"\\" => state_38 ()
 |  #"[" => state_38 ()
 |  #"~" => state_38 ()
 |  #"}" => state_38 ()
 |  #"|" => state_38 ()
 |  #"{" => state_38 ()
 |  _ => backtrack ()
 end)
and state_37 () = (
 resetLastPos ();
 setLastAction (magic action_15);
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_37 ()
 else backtrack ()
 end)
and state_38 () = (
 resetLastPos ();
 setLastAction (magic action_15);
 let val currChar = getNextChar () in
 if currChar >= #")" andalso currChar <= #"/" then  state_38 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_38 ()
 else case currChar of
    #"!" => state_38 ()
 |  #"#" => state_38 ()
 |  #"&" => state_38 ()
 |  #"%" => state_38 ()
 |  #"]" => state_38 ()
 |  #"\\" => state_38 ()
 |  #"[" => state_38 ()
 |  #"~" => state_38 ()
 |  #"}" => state_38 ()
 |  #"|" => state_38 ()
 |  #"{" => state_38 ()
 |  #"(" => state_39 ()
 |  _ => backtrack ()
 end)
and state_39 () = (
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_38 ()
 else case currChar of
    #"!" => state_38 ()
 |  #"#" => state_38 ()
 |  #"&" => state_38 ()
 |  #"%" => state_38 ()
 |  #")" => state_38 ()
 |  #"(" => state_38 ()
 |  #"/" => state_38 ()
 |  #"." => state_38 ()
 |  #"-" => state_38 ()
 |  #"," => state_38 ()
 |  #"+" => state_38 ()
 |  #"]" => state_38 ()
 |  #"\\" => state_38 ()
 |  #"[" => state_38 ()
 |  #"~" => state_38 ()
 |  #"}" => state_38 ()
 |  #"|" => state_38 ()
 |  #"{" => state_38 ()
 |  _ => backtrack ()
 end)
and state_40 () = (
 resetLastPos ();
 setLastAction (magic action_15);
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_38 ()
 else case currChar of
    #"!" => state_38 ()
 |  #"#" => state_38 ()
 |  #"&" => state_38 ()
 |  #"%" => state_38 ()
 |  #")" => state_38 ()
 |  #"(" => state_38 ()
 |  #"/" => state_38 ()
 |  #"." => state_38 ()
 |  #"-" => state_38 ()
 |  #"," => state_38 ()
 |  #"+" => state_38 ()
 |  #"]" => state_38 ()
 |  #"\\" => state_38 ()
 |  #"[" => state_38 ()
 |  #"~" => state_38 ()
 |  #"}" => state_38 ()
 |  #"|" => state_38 ()
 |  #"{" => state_38 ()
 |  _ => backtrack ()
 end)
and state_41 () = (
 resetLastPos ();
 setLastAction (magic action_19);
 let val currChar = getNextChar () in
 if currChar >= #")" andalso currChar <= #"/" then  state_41 ()
 else if currChar >= #":" andalso currChar <= #"@" then  state_41 ()
 else case currChar of
    #"!" => state_41 ()
 |  #"#" => state_41 ()
 |  #"&" => state_41 ()
 |  #"%" => state_41 ()
 |  #"]" => state_41 ()
 |  #"\\" => state_41 ()
 |  #"[" => state_41 ()
 |  #"~" => state_41 ()
 |  #"}" => state_41 ()
 |  #"|" => state_41 ()
 |  #"{" => state_41 ()
 |  #"(" => state_44 ()
 |  _ => backtrack ()
 end)
and state_42 () = (
 resetLastPos ();
 setLastAction (magic action_19);
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_42 ()
 else if currChar >= #"A" andalso currChar <= #"Z" then  state_42 ()
 else if currChar >= #"a" andalso currChar <= #"z" then  state_42 ()
 else case currChar of
    #"'" => state_42 ()
 |  #"_" => state_42 ()
 |  _ => backtrack ()
 end)
and state_43 () = (
 resetLastPos ();
 setLastAction (magic action_19);
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_16 ()
 else case currChar of
    #"!" => state_16 ()
 |  #"#" => state_16 ()
 |  #"&" => state_16 ()
 |  #"%" => state_16 ()
 |  #")" => state_16 ()
 |  #"(" => state_16 ()
 |  #"/" => state_16 ()
 |  #"." => state_16 ()
 |  #"-" => state_16 ()
 |  #"," => state_16 ()
 |  #"+" => state_16 ()
 |  #"]" => state_16 ()
 |  #"\\" => state_16 ()
 |  #"[" => state_16 ()
 |  #"~" => state_16 ()
 |  #"}" => state_16 ()
 |  #"|" => state_16 ()
 |  #"{" => state_16 ()
 |  _ => backtrack ()
 end)
and state_44 () = (
 resetLastPos ();
 setLastAction (magic action_19);
 let val currChar = getNextChar () in
 if currChar >= #":" andalso currChar <= #"@" then  state_16 ()
 else case currChar of
    #"!" => state_16 ()
 |  #"#" => state_16 ()
 |  #"&" => state_16 ()
 |  #"%" => state_16 ()
 |  #")" => state_16 ()
 |  #"(" => state_16 ()
 |  #"/" => state_16 ()
 |  #"." => state_16 ()
 |  #"-" => state_16 ()
 |  #"," => state_16 ()
 |  #"+" => state_16 ()
 |  #"]" => state_16 ()
 |  #"\\" => state_16 ()
 |  #"[" => state_16 ()
 |  #"~" => state_16 ()
 |  #"}" => state_16 ()
 |  #"|" => state_16 ()
 |  #"{" => state_16 ()
 |  _ => backtrack ()
 end)
and state_49 () = (
 resetLastPos ();
 setLastAction (magic action_12);
 let val currChar = getNextChar () in
 case currChar of
    #"\n" => action_12 ()
 |  _ => backtrack ()
 end)
and state_51 () = (
 resetLastPos ();
 setLastAction (magic action_14);
 let val currChar = getNextChar () in
 case currChar of
    #"*" => state_57 ()
 |  _ => backtrack ()
 end)
and state_52 () = (
 resetLastPos ();
 setLastAction (magic action_14);
 let val currChar = getNextChar () in
 case currChar of
    #"r" => action_10 ()
 |  #"n" => action_7 ()
 |  #"\\" => action_9 ()
 |  #"\"" => action_8 ()
 |  _ => backtrack ()
 end)
and state_57 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"#" => state_58 ()
 |  _ => backtrack ()
 end)
and state_58 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"l" => state_59 ()
 |  _ => backtrack ()
 end)
and state_59 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"o" => state_60 ()
 |  _ => backtrack ()
 end)
and state_60 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"c" => state_61 ()
 |  _ => backtrack ()
 end)
and state_61 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\t" => state_62 ()
 |  #" " => state_62 ()
 |  _ => backtrack ()
 end)
and state_62 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_64 ()
 else case currChar of
    #"\t" => state_63 ()
 |  #" " => state_63 ()
 |  _ => backtrack ()
 end)
and state_63 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_70 ()
 else case currChar of
    #"\t" => state_63 ()
 |  #" " => state_63 ()
 |  #"*" => state_66 ()
 |  _ => backtrack ()
 end)
and state_64 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_64 ()
 else case currChar of
    #"\t" => state_65 ()
 |  #" " => state_65 ()
 |  _ => backtrack ()
 end)
and state_65 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_67 ()
 else case currChar of
    #"\t" => state_65 ()
 |  #" " => state_65 ()
 |  #"*" => state_66 ()
 |  _ => backtrack ()
 end)
and state_66 () = (
 let val currChar = getNextChar () in
 case currChar of
    #")" => action_11 ()
 |  _ => backtrack ()
 end)
and state_67 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_67 ()
 else case currChar of
    #"\t" => state_68 ()
 |  #" " => state_68 ()
 |  #"*" => state_66 ()
 |  _ => backtrack ()
 end)
and state_68 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\t" => state_68 ()
 |  #" " => state_68 ()
 |  #"*" => state_66 ()
 |  _ => backtrack ()
 end)
and state_70 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_70 ()
 else case currChar of
    #"\t" => state_65 ()
 |  #" " => state_65 ()
 |  #"*" => state_66 ()
 |  _ => backtrack ()
 end)
and state_75 () = (
 resetLastPos ();
 setLastAction (magic action_4);
 let val currChar = getNextChar () in
 case currChar of
    #"\n" => action_4 ()
 |  _ => backtrack ()
 end)
and state_76 () = (
 resetLastPos ();
 setLastAction (magic action_5);
 let val currChar = getNextChar () in
 case currChar of
    #"*" => state_79 ()
 |  _ => backtrack ()
 end)
and state_77 () = (
 resetLastPos ();
 setLastAction (magic action_5);
 let val currChar = getNextChar () in
 case currChar of
    #")" => action_0 ()
 |  _ => backtrack ()
 end)
and state_79 () = (
 resetLastPos ();
 setLastAction (magic action_3);
 let val currChar = getNextChar () in
 case currChar of
    #"#" => state_80 ()
 |  _ => backtrack ()
 end)
and state_80 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"l" => state_81 ()
 |  _ => backtrack ()
 end)
and state_81 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"o" => state_82 ()
 |  _ => backtrack ()
 end)
and state_82 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"c" => state_83 ()
 |  _ => backtrack ()
 end)
and state_83 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\t" => state_84 ()
 |  #" " => state_84 ()
 |  _ => backtrack ()
 end)
and state_84 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_86 ()
 else case currChar of
    #"\t" => state_85 ()
 |  #" " => state_85 ()
 |  _ => backtrack ()
 end)
and state_85 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_92 ()
 else case currChar of
    #"\t" => state_85 ()
 |  #" " => state_85 ()
 |  #"*" => state_88 ()
 |  _ => backtrack ()
 end)
and state_86 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_86 ()
 else case currChar of
    #"\t" => state_87 ()
 |  #" " => state_87 ()
 |  _ => backtrack ()
 end)
and state_87 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_89 ()
 else case currChar of
    #"\t" => state_87 ()
 |  #" " => state_87 ()
 |  #"*" => state_88 ()
 |  _ => backtrack ()
 end)
and state_88 () = (
 let val currChar = getNextChar () in
 case currChar of
    #")" => action_2 ()
 |  _ => backtrack ()
 end)
and state_89 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_89 ()
 else case currChar of
    #"\t" => state_90 ()
 |  #" " => state_90 ()
 |  #"*" => state_88 ()
 |  _ => backtrack ()
 end)
and state_90 () = (
 let val currChar = getNextChar () in
 case currChar of
    #"\t" => state_90 ()
 |  #" " => state_90 ()
 |  #"*" => state_88 ()
 |  _ => backtrack ()
 end)
and state_92 () = (
 let val currChar = getNextChar () in
 if currChar >= #"0" andalso currChar <= #"9" then  state_92 ()
 else case currChar of
    #"\t" => state_87 ()
 |  #" " => state_87 ()
 |  #"*" => state_88 ()
 |  _ => backtrack ()
 end)
and base_token () =
  (setLastAction (magic dummyAction);
   resetStartPos ();
   state_2 ())

and string () =
  (setLastAction (magic dummyAction);
   resetStartPos ();
   state_1 ())

and comment () =
  (setLastAction (magic dummyAction);
   resetStartPos ();
   state_0 ())

(* The following checks type consistency of actions *)
val _ = fn _ => [action_24, action_23, action_22, action_21, action_20, action_19, action_18, action_17, action_16, action_15]
val _ = fn _ => [action_14, action_13, action_12, action_11, action_10, action_9, action_8, action_7, action_6]
val _ = fn _ => [action_5, action_4, action_3, action_2, action_1, action_0]

in
  {base_token = base_token, comment = comment}
end


(* MOVE FROM HERE TO THE END OF THE FILE! *)

fun base_token lexbuf st =
    (fn Base_token x => x)
    (#base_token (makeLex lexbuf) () st (Base_token ()));

fun comment lexbuf st n =
    (fn Comment x => x)
    (#comment (makeLex lexbuf) () st (Comment n));

end

(* MOVE UP TO HERE TO THE END OF THE FILE! *)

