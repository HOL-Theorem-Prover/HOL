structure Pretype :> Pretype =
struct

open Exception Lib Strm;

fun ERR s1 s2 = 
  Exception.HOL_ERR
   {origin_structure = "Pretype",
    origin_function = s1,
    message = s2};


(*---------------------------------------------------------------------------
     This first bit is general: polymorphism allows any type  of 
     atomic elements.
 ---------------------------------------------------------------------------*)

datatype 'a pretype 
     = tyVar   of 'a
     | tyAntiq of Type.hol_type
     | tyApp   of 'a * 'a pretype list;

(*---------------------------------------------------------------------------
     When we map to a hol_type, we need to map (via name_of) into 
     the names of type operators.
 ---------------------------------------------------------------------------*)
local open Type
in
fun pretype2type name_of =
  let fun pty (tyVar x) = mk_vartype (name_of x)
        | pty (tyAntiq x) = x
        | pty (tyApp(s,l)) = mk_type{Tyop=name_of s, Args = map pty l}
  in pty
  end
end;

(*---------------------------------------------------------------------------
             Parsing pretypes. 

     This following is more specific, since the atomic elements 
     built by the parser are locations.
 ---------------------------------------------------------------------------*)


val alphanumeric = Char.contains
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_'";

val symbolic = Char.contains "#+->,";

(*---------------------------------------------------------------------------*
 * Types for indexes and locations: for finding things in the input.         *
 *---------------------------------------------------------------------------*)
type index = int  (* index in the underlying string. *)
type 'a location = 'a * index;

datatype 'a lexeme = lparen of index
                   | rparen of index
                   | ident  of string location
                   | symbl  of string location
                   | aq     of 'a location
                   | alien  of Char.char location;

fun dest_lexeme (lparen i)    = ("(",i)
  | dest_lexeme (rparen i)    = (")",i)
  | dest_lexeme (ident p)     = p
  | dest_lexeme (symbl p)     = p
  | dest_lexeme (aq (x,i))    = ("<antiquote>", i)
  | dest_lexeme (alien (c,i)) = (Char.toString c, i);

fun print_lexeme lm = 
  let val (s,i) = dest_lexeme lm
  in
    String.concat
       ["lexeme = ", quote s, ", position = ", Int.toString i]
  end;

fun bump n ss = 
  let val (s,i,j) = Substring.base ss
  in Substring.substring(s,i,j+n)
  end;


(*---------------------------------------------------------------------------
    This is called when we know that ssl is alphanumeric, and now we 
    want to get the whole identifier. This function will also build 
    dotted identifiers. A dotted identifier can end in either an 
    alphanumeric or a symbolic.           
  ---------------------------------------------------------------------------*)

fun get_alphanumeric (ssl,s0) =
  let val (ss1,s1) = Strm.splitl alphanumeric s0
      val ssl' = Substring.span (ssl,ss1)
  in case get s1
      of SOME (CH #".", s2) => 
           (case get s2
             of SOME (CH c,_) => 
                  if alphanumeric c then get_alphanumeric (bump 1 ssl', s2)
                  else if symbolic c 
                       then let val (sym,s3) = Strm.splitl symbolic s2
                            in SOME (Substring.span (bump 1 ssl', sym), s3)
                            end
                       else SOME(ssl',s1)
              | _  => SOME(ssl', s1)) (* dotted ident needs final component *)
       | _ => SOME(ssl',s1)
  end;

(*---------------------------------------------------------------------------*
 * The basic type lexer.                                                     *
 *---------------------------------------------------------------------------*)
local open Option
in
fun tylex s =
  case get s
   of NONE => NONE
    | SOME (AQ x, s1) => SOME(aq(x,0), s1)
    | SOME (CH c, s1) => 
       if Char.isSpace c then tylex s1
       else
       let val (s,k,_) = base s1
           val i = k-1   (* Need to move back 1 to get index of c *)
       in
         case c 
          of #")" => SOME (rparen i, s1)
           | #"(" => (case get s1 
                       of SOME (CH #"*",s2) => mapPartial tylex (MLcomment s2)
                        | _ => SOME (lparen i,s1))
           | otherwise =>
              if alphanumeric c
              then let val first = Substring.substring(s,i,1)
                   in case get_alphanumeric (first, s1) 
                       of NONE => NONE
                        | SOME (pref,s2) => 
                            SOME(ident (Substring.string pref, i), s2)
                   end else 
              if symbolic c
              then let val (pref,s2) = Strm.splitl symbolic s1
                       val (_,_,n) = Substring.base pref
                       val ss = Substring.substring(s,i,n+1)
                   in SOME (symbl (Substring.string ss, i), s2)
                   end
              else SOME (alien(c,i), s1)
       end
end;

(*---------------------------------------------------------------------------*
 * Parsing types.                                                            *
 *---------------------------------------------------------------------------*)

fun rank "->" = SOME 1
  | rank "+"  = SOME 2
  | rank "#"  = SOME 3
  | rank  s   = NONE;

fun mk_infix id (h1::h2::t) = tyApp(id, [h2,h1])::t
  | mk_infix _ _ = raise ERR "mk_infix" "wrong number of args";

(*---------------------------------------------------------------------------
    Simple parser for types. 
 ---------------------------------------------------------------------------*)

type ground = string * int;

fun name_of ("->", _) = "fun"
  | name_of ("+", _)  = "sum"
  | name_of ("#", _)  = "prod"
  | name_of (s, _)    = s;


fun ERR1 s = raise (ERR "prs_pretype" s);

val prs_pretype = let
fun ptype (level,(stk,s)) =
case tylex s
 of SOME (aq (x,i), s1) => ptype (level, (tyAntiq x::stk, s1))
  | SOME (lparen i, s1) => 
    (case ptype (0,([],s1))
      of ([ty],s2) => 
          (case tylex s2
           of SOME(rparen i, s3) => 
               (case tylex s3
                 of SOME(ident id,s4) => ptype(level,([tyApp(id,[ty])],s4))
                  | _ => ptype(level, (ty::stk, s3)))
           | SOME(symbl (",",i), s3) => 
               let val (ty1,s4) = ptypel ([ty],s2)
               in ptype (level, (ty1::stk,s4))
               end
           | _ => ERR1 "expected right parenthesis or comma")
       | _ => ERR1 "expected a single type")
  | SOME (ident (id as (p,_)), s1) => 
     (case String.sub(p,0)
       of #"'" => ptype (level, (tyVar id::stk, s1))
        |   _  => ptype (level, ([tyApp(id,stk)], s1)))
  | SOME (symbl (",",_),_) => (stk,s)
  | SOME (symbl (id as (n,_)), s1) => 
     (case rank n  (* tests whether s is a known constant *)
       of SOME r => 
           if r < level then (stk,s) 
           else (case ptype (r, ([],s1))
                  of ([ty], s2) => ptype(level,(mk_infix id (ty::stk), s2))
                   | _ => ERR1 ("too many right-hand args. to "^quote n))
        | NONE => (stk,s))
  | _ => (stk,s)
and
ptypel (stk,s) =
  case tylex s
   of SOME (symbl (",",i), s1) => 
        (case ptype (0,([],s1))
           of ([ty],s2) => ptypel (ty::stk,s2)
            | _ => ERR1 "wrong number of args to compound type")
    | SOME (rparen i, s1) => 
        (case tylex s1
          of SOME (ident id, s2) => (tyApp(id, rev stk), s2)
           | _ =>  ERR1 "expecting a (postfix) type operator")
    | SOME (lm,_) => ERR1 ("unexpected lexeme: "^print_lexeme lm)
    | NONE => ERR1"unexpected end of input when looking for a \")\" or a \",\""
in
  ptype 
end;


fun ERR2 s = raise (ERR "parse" s);

fun parse q =
  case get (strm_of q)
   of SOME (CH #":", s0) => 
        let val (stk,s) = prs_pretype (0, ([],s0))
        in case tylex s 
            of NONE => (case stk 
                         of []  => ERR2 "no input" 
                          | [v] => v
                          |  _  => ERR2 "juxtaposed types")
             | _ => ERR2 (String.concat 
                            ["unparsed input remains: ", quote(string_of s)])
        end
    | _ => ERR2 "first character must be a colon"


end;
