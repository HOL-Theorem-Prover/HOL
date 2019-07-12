(*---------------------------------------------------------------------------*)
(* ML type of regexps                                                        *)
(*---------------------------------------------------------------------------*)

structure Regexp_Type :> Regexp_Type =
struct

open Lib Feedback regexpMisc;

val ERR = mk_HOL_ERR "Regexp_Type";

fun copy x n = List.tabulate (n,K x) handle _ => [];

(*---------------------------------------------------------------------------*)
(* Alphabet                                                                  *)
(*---------------------------------------------------------------------------*)

val alphabet_size = 256;
val alphabetN = List.tabulate (alphabet_size,I)
val alphabet = map Char.chr alphabetN;

(*---------------------------------------------------------------------------*)
(* Charsets                                                                  *)
(*---------------------------------------------------------------------------*)

type w64 = Word64.word;
type charset = w64 * w64 * w64 * w64;

val charset_empty : charset = (0wx0,0wx0,0wx0,0wx0);

fun charset_compl (u1,u2,u3,u4) : charset =
 let open Word64
 in (notb u1, notb u2, notb u3, notb u4)
 end;

val charset_full : charset = charset_compl charset_empty;

fun charset_union (u1,u2,u3,u4) (v1,v2,v3,v4) : charset =
 let open Word64
 in (orb (u1,v1), orb (u2,v2), orb (u3,v3), orb (u4,v4))
 end;

fun charset_inter (u1,u2,u3,u4) (v1,v2,v3,v4) =
 let open Word64
 in (andb (u1,v1), andb (u2,v2), andb (u3,v3), andb (u4,v4))
 end;

fun charset_diff cs1 cs2 = charset_inter cs1 (charset_compl cs2);

val sing_charsets =
 let fun setbit n = Word64.<< (0wx1,Word.fromInt n)
     val sing64 = List.map setbit (upto 0 63)
 in Vector.fromList
     (List.map (fn w => (w,0wx0,0wx0,0wx0):charset) sing64 @
      List.map (fn w => (0wx0,w,0wx0,0wx0):charset) sing64 @
      List.map (fn w => (0wx0,0wx0,w,0wx0):charset) sing64 @
      List.map (fn w => (0wx0,0wx0,0wx0,w):charset) sing64)
 end;

fun charset_mem c ((w1,w2,w3,w4):charset) =
 let val i = Char.ord c
     val (s1,s2,s3,s4) = Vector.sub(sing_charsets,i)
     val result =
        Word64.andb
          (if i < 64  then (w1,s1) else
           if i < 128 then (w2,s2) else
           if i < 192 then (w3,s3) else (w4,s4))
 in
   result <> 0wx0
 end

fun charset_insert c cset =
  charset_union (Vector.sub(sing_charsets,Char.ord c)) cset;

fun charset_elts cs = filter (C charset_mem cs) alphabet;

fun charset_of clist = itlist charset_insert clist charset_empty;

fun charset_sing c = charset_of [c];

fun charset_span b t =
 if 0 <= b andalso b <= 255 andalso
    0 <= t andalso t <= 255
 then
   charset_of (map Char.chr (upto b t))
 else raise ERR "charset_span" "";

fun charset_compare ((u1,u2,u3,u4),(v1,v2,v3,v4)) =
 let open Word64
 in case compare(u1,v1)
     of LESS => LESS
      | GREATER => GREATER
      | EQUAL =>
    case compare (u2,v2)
     of LESS => LESS
      | GREATER => GREATER
      | EQUAL =>
    case compare (u3,v3)
     of LESS => LESS
      | GREATER => GREATER
      | EQUAL => compare (u4,v4)
 end;

val charset_digit = charset_of (String.explode"0123456789");

val charset_alpha = charset_of
  (String.explode "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ");

val charset_alphanum =
  charset_insert #"_"
      (charset_union charset_digit charset_alpha);

val charset_whitespace = charset_of (String.explode" \n\r\t\f");


(*---------------------------------------------------------------------------*)
(* regexp datatype                                                           *)
(*---------------------------------------------------------------------------*)

datatype regexp
   = Chset of charset
   | Cat of regexp * regexp
   | Star of regexp
   | Or of regexp list
   | Neg of regexp;

fun And (r1,r2) = Neg(Or[Neg r1,Neg r2]);
fun Diff (r1,r2) = And(r1,Neg r2);

val WHITESPACE = Chset charset_whitespace
val DIGIT      = Chset charset_digit
val ALPHA      = Chset charset_alpha
val ALPHANUM   = Chset charset_alphanum
val EMPTY      = Chset charset_empty
val SIGMA      = Chset charset_full
val DOT        = SIGMA;
val EPSILON    = Star EMPTY;
val SIGMASTAR  = Star SIGMA;

fun mk_or [] = EMPTY
  | mk_or [x] = x
  | mk_or list = Or list;

fun catlist [] = EPSILON
  | catlist [x] = x
  | catlist (h::t) = Cat (h,catlist t);

fun strip_cat r =
 case r
  of Cat(a,b) => a::strip_cat b
   | otherwise => [r]

val dots = copy DOT;

fun replicate x (n:int) = catlist (copy x n);

fun ranged r i j =
 if j < i then EMPTY
 else Or (map (replicate r) (upto i j));

(*---------------------------------------------------------------------------*)
(* compressed version of ranged. Not used since it is hard for derivative    *)
(* taker to do well with the nesting.                                        *)
(*---------------------------------------------------------------------------*)

fun ranged_alt r i j =
 if j < i then EMPTY
 else Cat (replicate r i,replicate (Or [EPSILON,r]) (j-i))

(*---------------------------------------------------------------------------*)
(* Prettyprinting                                                            *)
(*---------------------------------------------------------------------------*)

fun charset_string cset =
 if cset = charset_full
  then "." else
 if cset = charset_empty
  then "[]" else
 if cset = charset_digit
  then "\\d" else
 if cset = charset_alphanum
  then "\\w" else
 if cset = charset_whitespace
  then "\\s"
 else
 let fun prchar ch =
      if mem ch [#"[", #"]"] then
         "\\" ^ String.str ch
      else
      if Char.isGraph ch then
         String.str ch
      else
      let val i = Char.ord ch
      in String.concat
               ["\\", (if i <= 9 then "00" else
                      if i <= 100 then "0" else ""),
                Int.toString i]
      end
     fun printerval (i,j) =
      if i=j then prchar (Char.chr i)
      else String.concat [prchar (Char.chr i),"-", prchar(Char.chr j)]
     val ords = List.map Char.ord (charset_elts cset)
     val interval_strings = String.concat (map printerval (intervals ords))
 in
   String.concat ["[", interval_strings, "]"]
 end;


(*---------------------------------------------------------------------------*)
(* precedence: Or = 1                                                        *)
(*            Cat = 2                                                        *)
(*            Neg = 3                                                        *)
(*           Star = 4                                                        *)
(*        charset = 5                                                        *)
(*---------------------------------------------------------------------------*)

val pp_regexp =
 let open Portable PP
     fun paren i j s1 s2 ps =
       if i < j then block CONSISTENT 0 ps
       else block INCONSISTENT (size s1) (add_string s1 :: ps @ [add_string s2])
     fun pp i regexp =
      case regexp
       of Chset cs => add_string (charset_string cs)
        | Cat(s,t) =>
            let val rlist = strip_cat regexp
            in
               paren i 2 "(" ")" (
                 pr_list (pp 2) [add_break(0,0)] rlist
               )
            end
        | Or rlist =>
               paren i 1 "(" ")" (
                 pr_list (pp 1) [add_string " |", add_break(1,0)] rlist
               )
        | Neg r =>
               paren i 3 "(" ")" [
                  add_string "~",
                  pp 3 r
                ]
        | Star r =>
               paren i 4 "(" ")" [
                 pp 4 r,
                 add_string "*"
               ]
 in
   pp 0
 end;

val _ = PolyML.addPrettyPrinter (fn d => fn _ => fn r => pp_regexp r);

(*---------------------------------------------------------------------------*)
(* print regexp as string to stdOut                                          *)
(*---------------------------------------------------------------------------*)

val print_regexp = Portable.pprint pp_regexp;
fun println_regexp r = (print_regexp r; print "\n");

(*---------------------------------------------------------------------------*)
(* regexp comparison                                                         *)
(*---------------------------------------------------------------------------*)

fun list_cmp cmp pair =
 case pair
  of ([],[]) => EQUAL
   | ([],_)  => LESS
   | (_,[])  => GREATER
   | (h1::t1,h2::t2) =>
      (case cmp (h1,h2)
        of EQUAL => list_cmp cmp (t1,t2)
         | verdict => verdict);

fun len_cmp l1 l2 =
 if null l1
   then (if null l2 then EQUAL else LESS)
   else (if null l2 then GREATER else len_cmp(tl l1) (tl l2));

fun list_compare cmp l1 l2 =
  case len_cmp l1 l2
   of EQUAL => list_cmp cmp (l1,l2)
    | strict => strict;

fun regexp_compare pair =
 if PolyML.pointerEq pair
 then EQUAL
 else
 case pair
  of (Chset cs1, Chset cs2) => charset_compare(cs1,cs2)
   | (Chset cs, r) => LESS
   | (Cat (r,s), Chset _) => GREATER
   | (Cat(r1,r2),Cat(r3,r4)) =>
         (case regexp_compare (r1,r3)
           of LESS => LESS
            | GREATER => GREATER
            | EQUAL => regexp_compare (r2,r4))
   | (Cat(r,s), _) => LESS
   | (Star r, Chset _) => GREATER
   | (Star r, Cat (s,t)) => GREATER
   | (Star r,Star s) => regexp_compare(r,s)
   | (Star r, _) => LESS
   | (Or rs,Chset _) => GREATER
   | (Or rs,Cat (r,s)) => GREATER
   | (Or rs,Star _) => GREATER
   | (Or rs1,Or rs2) => list_compare regexp_compare (List.rev rs1) (List.rev rs2)
   | (Or rs, _) => LESS
   | (Neg r,Neg s) =>  regexp_compare (r,s)
   | (Neg r,_) => GREATER
;


(*---------------------------------------------------------------------------*)
(* Lexer and parser for Python-style regexp syntax.                          *)
(*---------------------------------------------------------------------------*)

datatype lexeme
   = lparen
   | rparen
   | dot
   | digit
   | alphanum
   | whitespace
   | interval
   | char of Char.char
   | chars of charset
   | preFix of Char.char  (* ~ *)
   | inFix of Char.char   (* &| *)
   | postFix of Char.char (* *+? *)
   | power of IntInf.int
   | range of IntInf.int option * IntInf.int option  (* range + direction *)
   | const of IntInf.int
;

fun lexeme_equal lparen lparen = true
  | lexeme_equal rparen rparen = true
  | lexeme_equal dot dot = true
  | lexeme_equal digit digit = true
  | lexeme_equal alphanum alphanum = true
  | lexeme_equal whitespace whitespace = true
  | lexeme_equal interval interval = true
  | lexeme_equal (const cd1) (const cd2) = (cd1=cd2)
  | lexeme_equal (char c1) (char c2) = (c1=c2)
  | lexeme_equal (chars c1) (chars c2) = (charset_compare(c1,c2) = EQUAL)
  | lexeme_equal (preFix c1) (preFix c2) = (c1=c2)
  | lexeme_equal (inFix c1) (inFix c2) = (c1=c2)
  | lexeme_equal (postFix c1) (postFix c2) = (c1=c2)
  | lexeme_equal (power i1) (power i2) = (i1=i2)
  | lexeme_equal (range io1) (range io2) = (io1=io2)
  | lexeme_equal x y = false

(*---------------------------------------------------------------------------*)
(* Following special characters need to be back-slashed to avoid             *)
(* interpretation.                                                           *)
(*                                                                           *)
(*    val specialChar = Char.contains ".^$*+?{}[]\\|()"                      *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun opt2string (lowOpt,hiOpt) = String.concat
 ["{",
     case (lowOpt,hiOpt)
      of (SOME i,SOME j) => (IntInf.toString i^","^ IntInf.toString j)
       | (SOME i, NONE)  => (IntInf.toString i^",")
       | (NONE, SOME j)  => (","^IntInf.toString j)
       | otherwise => raise ERR "lexeme2string"
                                "opt2string: unexpected format",
  "}"]

fun const2string i =
 String.concat
      ["\\k{", IntInf.toString i, "}"]

fun bstring b = if b then "1" else "0";

fun lexeme2string lparen    = "("
  | lexeme2string rparen    = ")"
  | lexeme2string dot       = "."
  | lexeme2string digit     = "\\d"
  | lexeme2string alphanum  = "\\w"
  | lexeme2string whitespace = "\\s"
  | lexeme2string interval   = "\\i"
  | lexeme2string (char c)   = Char.toString c
  | lexeme2string (chars s)  = "<charset>"
  | lexeme2string (preFix c) = Char.toString c
  | lexeme2string (inFix c)  = Char.toString c
  | lexeme2string (postFix c) = Char.toString c
  | lexeme2string (power n)   = "{"^IntInf.toString n^"}"
  | lexeme2string (range t)   = opt2string t
  | lexeme2string (const c)   = const2string c


(*---------------------------------------------------------------------------*)
(* Lexing support                                                            *)
(*---------------------------------------------------------------------------*)

fun takeWhile P ss =
  let open Substring
      val (ls, ss') = splitl P ss
  in if isEmpty ls
      then NONE
      else SOME (string ls, ss')
  end

fun compose f NONE = NONE
  | compose f (SOME (x,y)) = f x y;

fun try_alt f1 f2 strm =
  case f1 strm
   of NONE => f2 strm
    | other => other

fun chomp ch =
 let open Substring
 in compose (fn l => fn strm =>
      case getc strm
       of SOME(c,strm') => if ch=c then SOME(l,strm') else NONE
        | NONE => NONE)
 end;

fun eat_then ch f strm =
 case Substring.getc strm
  of NONE => NONE
   | SOME(ch1,strm) => if ch=ch1 then f strm else NONE;

fun is_tilde ch = (ch = #"~");

fun getNum ss =
 compose (fn s => fn ss' =>
    case IntInf.fromString s
     of NONE => NONE
      | SOME i => SOME(i,ss'))
  (takeWhile (fn c => Char.isDigit c orelse is_tilde c) ss);

fun mk_right_range x = compose
 (fn i => fn strm => SOME(range(NONE,SOME i),strm)) x;

fun mk_left_range i x = compose
 (fn _ => fn strm => SOME(range(SOME i,NONE),strm)) x;

(*---------------------------------------------------------------------------*)
(* Lexing powers and ranges: we've seen a "{": now get the rest : one of     *)
(*                                                                           *)
(*    "<d>}"                                                                 *)
(*    "<d>,}"                                                                *)
(*    ",<d>}"                                                                *)
(*    "<d>,<d>}"                                                             *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

val comma = #",";

fun get_range strm =
 let open Substring
 in case getc strm
     of NONE => NONE
      | SOME(#",",strm') => mk_right_range(chomp #"}" (getNum strm'))
      | otherwise =>
    case getNum strm
     of NONE => NONE
      | SOME(i,strm') =>
    case getc strm'
     of NONE => NONE
      | SOME(#"}",strm'') => SOME(power i,strm'')
      | SOME(c,strm'') => if c <> comma then NONE else
    case getc strm''
     of NONE => NONE
      | SOME(#"}",strm''') => SOME(range(SOME i,NONE),strm''')
      | otherwise =>
    case getNum strm''
     of NONE => NONE
      | SOME(j,strm''') =>
    case getc strm'''
     of NONE => NONE
      | SOME(#"}",strm1) => SOME(range(SOME i,SOME j),strm1)
      | otherwise => NONE
 end


fun get_const strm =
 let fun get strm =
      case getNum strm
       of NONE =>  NONE
        | SOME(i,strm) =>
             (eat_then #"}" (fn strm => SOME (const(i), strm)))
             strm
 in
  eat_then #"{" get strm
 end

(*---------------------------------------------------------------------------*)
(* Lexing a character set, which has the form                                *)
(*                                                                           *)
(*    [ ... ]  or [^ ... ]                                                   *)
(*                                                                           *)
(* where the latter takes the complement of the following charset.  Ranges   *)
(* of the form c1-c2 are supported, provided they make sense. Backslashing   *)
(* characters is also allowed. Inside a charset, an explicit number denoting *)
(* a char can be written as a backslash followed by three decimal digits,    *)
(* i.e., \ddd.                                                               *)
(*---------------------------------------------------------------------------*)

fun get_charset strm =
 let fun compl(chars cs,strm) = (chars(charset_diff charset_full cs),strm)
       | compl otherwise = raise ERR "get_charset" "compl"
     fun elim_decimal_chars list =
       let in
         case list
          of #"\\"::d1::d2::d3::t =>
            if Char.isDigit d1 andalso Char.isDigit d2 andalso Char.isDigit d3
              then (case Int.fromString (String.implode [d1,d2,d3])
                    of SOME i =>
                        if Int.<(i,256) then chr(i)::elim_decimal_chars t
                        else raise ERR "elim_decimal_chars"
                              "malformed charset element: looking for \\ddd"
                     | NONE => raise ERR "elim_decimal_chars"
                              "number from \\ddd is too big"
                   )
              else List.hd list :: elim_decimal_chars (List.tl list)
          | ch::t => ch :: elim_decimal_chars t
          | [] => []
      end
     fun mk_chars (ch1 :: #"-" :: ch2 :: t) =
         if Char.<=(ch1,ch2)
          then let val clist = map Char.chr (upto (Char.ord ch1) (Char.ord ch2))
               in clist @ mk_chars t
               end
          else raise ERR "lex.get_charset.mk_chars" "bad range"
       | mk_chars (#"\\"::ch::t) = ch::mk_chars t
       | mk_chars (ch::t) = ch::mk_chars t
       | mk_chars [] = []
     fun get_charset_body strm acc =
        case Substring.getc strm
         of SOME(#"]",strm') => (rev acc,strm')
          | SOME(ch,strm') => get_charset_body strm' (ch::acc)
          | NONE => raise ERR "lex.get_charset.get_charset_body"
                     "end of input before getting to end of charset"
     fun mk_cset (clist,strm) =
        (chars (charset_of (mk_chars (elim_decimal_chars clist))),
         strm)
 in case Substring.getc strm
     of NONE => NONE
      | SOME(#"]",strm') => SOME(chars charset_empty, strm')
      | SOME(#"^",strm') => SOME(compl (mk_cset (get_charset_body strm' [])))
      | SOME(ch, strm')  => SOME(mk_cset(get_charset_body strm' [ch]))
 end

fun lex strm =
 let open Substring
 in case getc strm
     of NONE => NONE
      | SOME (#"(",strm') => SOME(lparen,strm')
      | SOME (#")",strm') => SOME(rparen,strm')
      | SOME (#"[",strm') => get_charset strm'
      | SOME (#"{",strm') => get_range strm'
      | SOME (#".",strm') => SOME(dot,strm')
      | SOME (#"~",strm') => SOME(preFix #"~",strm')
      | SOME (#"|",strm') => SOME(inFix #"|",strm')
      | SOME (#"&",strm') => SOME(inFix #"&",strm')
      | SOME (#"*",strm') => SOME(postFix #"*",strm')
      | SOME (#"+",strm') => SOME(postFix #"+",strm')
      | SOME (#"?",strm') => SOME(postFix #"?",strm')
      | SOME (#"\\",strm') =>
        (case getc strm'
          of NONE => NONE
           | SOME(#"d",strm'') => SOME(digit,strm'')
           | SOME(#"w",strm'') => SOME(alphanum,strm'')
           | SOME(#"s",strm'') => SOME(whitespace,strm'')
           | SOME(#"i",strm'') => SOME(interval,strm'')
           | SOME(#"k",strm'') => get_const strm''
           | SOME(ch,strm'')   => SOME(char ch,strm'')
        )
      | SOME (ch,strm') => SOME (char ch,strm')
 end

fun lexemes ss = case lex ss of NONE => [] | SOME(l,ss') => l::lexemes ss'

(*
val ss = Substring.full "[abc\234d]";
val ss = Substring.full "[abc\\234d]";
val ss = Substring.full "[\117-\234\010]";
val [chars cset] = lexemes ss;
*)


(*---------------------------------------------------------------------------*)
(* Now parsing                                                               *)
(*---------------------------------------------------------------------------*)

fun PARSE_ERR s ss =
 let open Substring
     val estring = String.concat
         ["Regexp parser failed!\n   ",s,
          "\n   Remaining input: ", string ss, ".\n"]
 in
   raise ERR "PARSE_ERR" estring
 end;

(*---------------------------------------------------------------------------*)
(* We parse into tree, from which it is easy to generate regexp               *)
(*---------------------------------------------------------------------------*)

datatype tree
   = Ident of Char.char
   | Cset of charset
   | Ap of string * tree list
   | Power of tree * int
   | Range of tree * int option * int option
   | Interval of IntInf.int * IntInf.int
   | Const of IntInf.int;


fun expect lexeme (stk,ss) =
  case lex ss
   of SOME (lexed, ss') =>
       if lexeme_equal lexed lexeme
         then (stk,ss')
         else PARSE_ERR ("Expected "^quote(lexeme2string lexeme)) ss
    | NONE => PARSE_ERR ("Empty input when expecting "
                        ^quote(lexeme2string lexeme)) ss;

fun opr #"*" = "Star"
  | opr #"+" = "Plus"
  | opr #"?" = "Opt"
  | opr #"|" = "Sum"
  | opr #"&" = "And"
  | opr #"~" = "Not"
  | opr ch = raise ERR "opr" ("unknown operator: "^Char.toString ch)

val isInfix = Char.contains"|&";

(*---------------------------------------------------------------------------*)
(* Essential grammar being parsed. Rules given in order of increasing        *)
(* precedence.                                                               *)
(*                                                                           *)
(*  re ::= re "|" re                                                         *)
(*      |  re "&" re                                                         *)
(*      | re <dot> re  ;; <dot> is implicit because concat. is invisible     *)
(*      | ~re                                                                *)
(*      | re<p>        ;; p in {+,*,?} or a power or a range                 *)
(*      | "(" re ")"                                                         *)
(*      | charset                                                            *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

fun parse ss = Disj ([],ss)
and
 Disj (stk,ss) =
  let val (stk',ss') = Conj (stk,ss)
  in case lex ss'
      of SOME (inFix #"|",ss'') =>
          (case Disj(stk',ss'')
           of (e1::e2::t,ss''') => (Ap("Sum",[e2,e1])::t,ss''')
            | otherwise => PARSE_ERR "expected right part of | expression" ss'')
       | other => (stk',ss')
  end
and
 Conj (stk,ss) =
  let val (stk',ss') = Juxt (stk,ss)
  in case lex ss'
      of SOME (inFix #"&",ss'') =>
          (case Conj(stk',ss'')
           of (e1::e2::t,ss''') => (Ap("And",[e2,e1])::t,ss''')
            | otherwise => PARSE_ERR "expected right part of & expression" ss'')
       | other => (stk',ss')
  end
and
 Juxt (stk,ss) =
  let val (stk',ss') = Prefix (stk,ss)
  in case lex ss'
      of SOME(inFix _,_)   => (stk',ss')
       | SOME(rparen,_)    => (stk',ss')
       | SOME(postFix _,_) => (stk',ss')
       | SOME(power _,_)   => (stk',ss')
       | SOME(range _,_)   => (stk',ss')
       | SOME other =>
          (case Juxt(stk',ss')
            of (e1::e2::t,ss'') => (Ap("Juxt",[e2,e1])::t,ss'')
             | otherwise => PARSE_ERR "expected another regexp" ss')
       | NONE => (stk',ss')
  end
and
 Prefix (stk,ss) =
  case lex ss
   of SOME(preFix ch,ss') =>
       (case Prefix(stk,ss')
         of (h::t,ss'') => (Ap(opr ch,[h])::t,ss'')
          | ([],_) => PARSE_ERR "missing argument to ~" ss')
    | otherwise => Postfix(stk,ss)
and
 Postfix (stk,ss) =
  let fun Postfixen (stk,ss) = (* deal with multiple post-fixes *)
       case lex ss
         of SOME(postFix ch,ss') =>
             (case stk
               of h::t => Postfixen(Ap(opr ch,[h])::t,ss')
                | [] => PARSE_ERR "missing argument to postfix operator" ss)
          | SOME(power i,ss') =>
             (case stk
               of h::t => Postfixen(Power(h,IntInf.toInt i)::t,ss')
                | [] => PARSE_ERR "missing regexp for {-} operator" ss)
          | SOME(range(o1,o2),ss') =>
             (case stk
               of Ap("interval",[])::t
                   => (case (o1,o2)
                        of (SOME i, SOME j) => Postfixen(Interval(i,j)::t,ss')
                         | otherwise => PARSE_ERR "incomplete interval" ss)
                | h::t => let val o1' = Option.map IntInf.toInt o1
                              val o2' = Option.map IntInf.toInt o2
                          in Postfixen(Range(h,o1',o2')::t,ss')
                          end
                | [] => PARSE_ERR "missing regexp for {-,-} operator" ss)
          | otherwise => (stk,ss)
  in Postfixen (Atom (stk,ss))
  end
and
 Atom (stk,ss) =
  case lex ss
   of SOME(dot,ss')        => (Ap("dot",[])::stk,ss')
    | SOME(char ch,ss')    => (Ident ch::stk,ss')
    | SOME(chars cset,ss') => (Cset cset::stk,ss')
    | SOME(digit,ss')      => (Ap("digit",[])::stk,ss')
    | SOME(alphanum,ss')   => (Ap("alphanum",[])::stk,ss')
    | SOME(whitespace,ss') => (Ap("whitespace",[])::stk,ss')
    | SOME(interval,ss')   => (Ap("interval",[])::stk,ss')
    | SOME(const copt,ss') => (Const copt::stk,ss')
    | SOME(lparen,ss')     =>
       let in
         case expect rparen (parse ss')
          of ([x],ss'') => (x::stk,ss'')
           | other => PARSE_ERR "unable to complete parse inside parentheses" ss'
       end
    | other => (stk,ss)
;

val tree_parse = parse;

fun substring_to_tree sstring =
 case parse sstring
  of ([t],ss) => if Substring.isEmpty ss then t
                 else PARSE_ERR "remaining input after successful parse" ss
   | ([],ss) => PARSE_ERR "no parse" ss
   | (other,ss) => PARSE_ERR "multiple parses" ss;

val string_to_tree = substring_to_tree o Substring.full;

fun quote_to_tree input =
 case input
  of [QUOTE s] =>
     let open Substring
         val ss = full s
         val (_,ss') = position (String.implode[#"*",#")"]) ss
     in substring_to_tree (slice(ss',2,NONE))
     end
 | otherwise => raise ERR "quote_to_tree"
               "expected a simple quotation of the form ` .... `";

fun tree_to_regexp intervalFn =
 let fun t2r tree =
  case tree
   of Ident ch => Chset (charset_of [ch])
    | Cset cset => Chset cset
    | Power(t,i) => replicate (t2r t) i
    | Range(t,SOME i,SOME j) => ranged (t2r t) i j
    | Range(t,NONE,SOME j) => ranged (t2r t) 0 j
    | Range(t,SOME i,NONE) =>
      let val r = t2r t
      in Cat(replicate r i, Star r)
      end
    | Range (t,NONE,NONE) => Star (t2r t)
    | Interval(i,j) => intervalFn (i,j)
    | Const k => intervalFn (k,k)
    | Ap("dot",[]) => DOT
    | Ap("digit",[]) => DIGIT
    | Ap("alphanum",[]) => ALPHANUM
    | Ap("whitespace",[]) => WHITESPACE
    | Ap("Star",[t]) => Star(t2r t)
    | Ap("Plus",[t]) => let val r = t2r t in Cat(r,Star r) end
    | Ap("Opt",[t]) => Or[EPSILON,t2r t]
    | Ap("Sum",[t1,t2]) => Or[t2r t1,t2r t2]
    | Ap("And",[t1,t2]) => Neg(Or[Neg(t2r t1),Neg(t2r t2)])
    | Ap("Juxt",[t1,t2]) => Cat(t2r t1,t2r t2)
    | Ap("Not",[t]) => Neg(t2r t)
    | Ap("interval",[]) => raise ERR "tree_to_regexp" "missing interval parameters"
    | Ap(other,_) => raise ERR "tree_to_regexp" ("unknown operator: "^other)
 in
   t2r
 end
;

val the_intervalFn : (IntInf.int * IntInf.int -> regexp) ref =
  ref (fn _ => raise ERR "tree_to_regexp" "interval regexp generator not installed")

fun get_intervalFn() = !the_intervalFn
fun set_intervalFn f = (the_intervalFn := f);

fun fromSubstring sstring =
 tree_to_regexp (get_intervalFn()) (substring_to_tree sstring)
 handle e => raise wrap_exn "Regexp_Type" "fromSubstring" e;

fun fromString s = tree_to_regexp (get_intervalFn()) (string_to_tree s)
 handle e => raise wrap_exn "Regexp_Type" "fromString" e;

fun fromQuote q = tree_to_regexp (get_intervalFn()) (quote_to_tree q)
 handle e => raise wrap_exn "Regexp_Type" "fromQuote" e;

end
