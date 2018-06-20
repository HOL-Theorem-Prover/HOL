(*---------------------------------------------------------------------------*)
(* ML type of regexps                                                        *)
(*---------------------------------------------------------------------------*)

structure Regexp_Type :> Regexp_Type =
struct

open Lib Feedback regexpMisc WordOps Interval;

val ERR = mk_HOL_ERR "Regexp_Type";

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
     val (word,sing) =
        if i < 64 then (w1,s1) else
        if i < 128 then (w2,s2) else
        if i < 192 then (w3,s3) else (w4,s4)
 in
   Word64.andb(word,sing) <> 0wx0
 end

fun charset_insert c cset =
  charset_union (Vector.sub(sing_charsets,Char.ord c)) cset;

fun charset_elts cs = filter (C charset_mem cs) alphabet;

fun charset_of clist = itlist charset_insert clist charset_empty;

fun charset_sing c = charset_of [c];

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

(*---------------------------------------------------------------------------*)
(* Character sets represented as (256-bit) bigints.                          *)
(*---------------------------------------------------------------------------*)
(*
type charset = IntInf.int;

val charset_empty = WordOps.allzero;

val powers =
  Vector.fromList (map (curry IntInf.pow 2) (upto 0 (alphabet_size-1)));

fun setbit n w = IntInf.orb(Vector.sub(powers,n),w);

fun charset_insert ch cset = setbit (Char.ord ch) cset;

fun charset_of clist = itlist charset_insert clist charset_empty;

fun charset_sing c = charset_of [c]

val charset_full = charset_of (map Char.chr (upto 0 (alphabet_size-1)))

val charset_mem =
 let open IntInf
 in fn c => fn (cs:charset) =>
    not (andb(cs,Vector.sub(powers, Char.ord c)) = 0)
 end;

fun charset_elts cs = filter (C charset_mem cs) alphabet;

fun charset_union cs1 cs2 = IntInf.orb(cs1,cs2);

fun charset_diff cs1 cs2 = IntInf.andb(cs1,IntInf.notb cs2)

(*---------------------------------------------------------------------------*)
(* charset_compare assumes argument vectors are of equal length              *)
(*---------------------------------------------------------------------------*)

val charset_compare = IntInf.compare;
*)

(*---------------------------------------------------------------------------*)
(* Common charsets                                                           *)
(*---------------------------------------------------------------------------*)

val charset_digit = charset_of (String.explode"0123456789");
val charset_alpha = charset_of
  (String.explode "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ");
val charset_alphanum =
  charset_insert #"_"
      (charset_union charset_digit charset_alpha);
val charset_whitespace = charset_of (String.explode" \n\r\t\f");

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
      if Char.isGraph ch then String.str ch
      else let val i = Char.ord ch
           in String.concat
               ["\\", (if i <= 9 then "00" else
                      if i <= 100 then "0" else ""),
                Int.toString i]
           end
     fun printerval [] = raise ERR "charset_string" "empty interval"
       | printerval [i] = prchar (Char.chr i)
       | printerval (i::t) = String.concat
                               [prchar (Char.chr i),"-",
                                prchar(Char.chr(List.last t))]
     val ords = List.map (IntInf.fromInt o Char.ord) (charset_elts cset)
     val interval_strings =
       String.concat (map (printerval o map IntInf.toInt) (intervals ords))
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

fun strip_cat r =
 case r
  of Cat(a,b) => a::strip_cat b
   | otherwise => [r]

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

datatype direction = LSB | MSB;

datatype packelt
  = Span of IntInf.int * IntInf.int
  | Pad of int;

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
   | range of IntInf.int option * IntInf.int option * direction option  (* range + direction *)
   | const of IntInf.int * direction
   | pack of packelt list
;

fun lexeme_equal lparen lparen = true
  | lexeme_equal rparen rparen = true
  | lexeme_equal dot dot = true
  | lexeme_equal digit digit = true
  | lexeme_equal alphanum alphanum = true
  | lexeme_equal whitespace whitespace = true
  | lexeme_equal interval interval = true
  | lexeme_equal (const cd1) (const cd2) = (cd1=cd2)
  | lexeme_equal (pack p1) (pack p2) = (p1=p2)
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

fun dir2string MSB = "MSB"
  | dir2string LSB = "LSB";

fun string2dir "MSB" = SOME MSB
  | string2dir "LSB" = SOME LSB
  | string2dir other = NONE;

fun opt3string (lowOpt,hiOpt,ordOpt) = String.concat
 ["{",
     case (lowOpt,hiOpt,ordOpt)
      of (SOME i,SOME j,SOME d) => (IntInf.toString i^","^ IntInf.toString j^","^dir2string d)
       | (SOME i,SOME j,NONE) => (IntInf.toString i^","^ IntInf.toString j)
       | (SOME i, NONE,NONE)  => (IntInf.toString i^",")
       | (NONE, SOME j,NONE)  => (","^IntInf.toString j)
       | otherwise => raise ERR "lexeme2string"
                                "opt3string: unexpected format",
  "}"]

fun const2string (i,d) =
 String.concat
      ["\\k{", IntInf.toString i, ",", dir2string d, "}"]

fun bstring b = if b then "1" else "0";

fun pack2string flds =
 let fun field_to_strings pelt =
      case pelt
       of Span(lo,hi) =>
            String.concat["(", IntInf.toString lo, ",", IntInf.toString hi, ")"]
        | Pad i =>
            String.concat["{", Int.toString i, "}"]
 in String.concat
      ("\\p{" :: (Lib.commafy (List.map field_to_strings flds) @ ["}"]))
 end

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
  | lexeme2string (range t)   = opt3string t
  | lexeme2string (const c)   = const2string c
  | lexeme2string (pack list) = pack2string list;


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

fun getDirection ss =
 compose (fn s => fn ss' =>
    case string2dir s
     of NONE => NONE
      | SOME dir => SOME(dir,ss'))
  (takeWhile Char.isAlpha ss);

fun mk_right_range x = compose
 (fn i => fn strm => SOME(range(NONE,SOME i,NONE),strm)) x;

fun mk_left_range i x = compose
 (fn _ => fn strm => SOME(range(SOME i,NONE,NONE),strm)) x;

(*---------------------------------------------------------------------------*)
(* Lexing powers and ranges: we've seen a "{": now get the rest : one of     *)
(*                                                                           *)
(*    "<d>}"                                                                 *)
(*    "<d>,}"                                                                *)
(*    ",<d>}"                                                                *)
(*    "<d>,<d>}"                                                             *)
(*    "<d>,<d>,<dir>}"                                                       *)
(*                                                                           *)
(* where <dir> = LSB | MSB                                                   *)
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
      | SOME(#"}",strm''') => SOME(range(SOME i,NONE,NONE),strm''')
      | otherwise =>
    case getNum strm''
     of NONE => NONE
      | SOME(j,strm''') =>
    case getc strm'''
     of NONE => NONE
      | SOME(#"}",strm1) => SOME(range(SOME i,SOME j,NONE),strm1)
      | SOME(c,strm1) => if c <> comma then NONE else
    case getDirection strm1
     of NONE => NONE
      | SOME(dir,strm2) =>
    case getc strm2
     of SOME(#"}",strm3) => SOME(range(SOME i,SOME j,SOME dir),strm3)
      | otherwise => NONE
 end

(*---------------------------------------------------------------------------*)
(* Lexing a pack spec of the form                                            *)
(*                                                                           *)
(*   \p{elt_1 ... elt_n}                                                     *)
(*                                                                           *)
(* where the \p has already been consumed by the lexer. Each elt_i is either *)
(* of the form                                                               *)
(*                                                                           *)
(*   (lo,hi) (an interval)                                                   *)
(*                                                                           *)
(*   or                                                                      *)
(*                                                                           *)
(*   .{n}  (padding by n bits)                                               *)
(*---------------------------------------------------------------------------*)

fun get_pack strm =
 let open Substring
  fun getPad strm =
    case getc strm
     of NONE => NONE
      | SOME(#".",strm') =>
         (case eat_then #"{" getNum strm'
           of NONE => NONE
            | SOME (n,strm'') =>
           eat_then #"}" (fn s => SOME (Pad (IntInf.toInt n), s)) strm''
         )
      | SOME(_,strm') => NONE
  fun getSpan strm =
      case eat_then #"(" getNum strm
       of NONE =>  NONE
        | SOME(i,strm) =>
      case eat_then #"," getNum strm
       of NONE =>  NONE
        | SOME(j,strm) =>
      eat_then #")" (fn strm => SOME(Span(i,j),strm)) strm
  fun get_block strm = try_alt getPad getSpan strm
  fun get_blocks list strm =
       case get_block strm
        of NONE => eat_then #"}" (fn strm => SOME (pack(rev list), strm)) strm
         | SOME (el,strm) =>
             try_alt
(*              (eat_then #"," (get_blocks (el::list))) *)
              (get_blocks (el::list))
              (eat_then #"}" (fn strm => SOME (pack(rev (el::list)), strm)))
             strm
 in
  eat_then #"{" (get_blocks []) strm
 end

fun get_const strm =
 let fun getDir i strm =
       case getDirection strm
        of NONE => NONE
         | SOME(d,strm) => eat_then #"}" (fn strm => SOME (const(i,d), strm)) strm
     fun get strm =
      case getNum strm
       of NONE =>  NONE
        | SOME(i,strm) =>
           try_alt
              (eat_then #"," (getDir i))
              (eat_then #"}" (fn strm => SOME (const(i,LSB), strm)))
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
           | SOME(#"p",strm'') => get_pack strm''
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
val _ = Vector.appi(fn (i,b) => if b then print (Int.toString i^" ") else ()) cset;
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

datatype tree = Ident of Char.char
              | Cset of charset
              | Ap of string * tree list
              | Power of tree * int
              | Range of tree * int option * int option
              | Interval of IntInf.int * IntInf.int * direction
              | Const of IntInf.int * direction
              | Pack of packelt list;


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
          | SOME(range(o1,o2,od),ss') =>
             (case stk
               of Ap("interval",[])::t
                   => (case (o1,o2,od)
                        of (SOME i, SOME j, SOME d) => Postfixen(Interval(i,j,d)::t,ss')
                         | (SOME i, SOME j, NONE) => Postfixen(Interval(i,j,LSB)::t,ss')
                         | otherwise => PARSE_ERR "incomplete interval" ss)
                | h::t => if od=NONE
                          then let val o1' = Option.map IntInf.toInt o1
                                   val o2' = Option.map IntInf.toInt o2
                               in Postfixen(Range(h,o1',o2')::t,ss')
                               end
                          else PARSE_ERR "did not want LSB/MSB" ss
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
    | SOME(pack list,ss')  => (Pack list::stk,ss')
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


(*---------------------------------------------------------------------------*)
(* Map a parse tree into a regexp                                            *)
(*---------------------------------------------------------------------------*)

val WHITESPACE = Chset charset_whitespace
val DIGIT      = Chset charset_digit
val ALPHA      = Chset charset_alpha
val ALPHANUM   = Chset charset_alphanum
val EMPTY      = Chset charset_empty
val SIGMA      = Chset charset_full
val DOT        = SIGMA;
val EPSILON    = Star EMPTY;
val SIGMASTAR  = Star SIGMA;

fun replicate x (n:int) =
 if n <= 0 then EPSILON else
 if n = 1 then x
  else Cat(x,replicate x (n-1));

fun catlist [] = EPSILON
  | catlist [x] = x
  | catlist (h::t) = Cat (h,catlist t);

fun range r i j =
 if j < i then EMPTY
 else Or (map (replicate r) (upto i j));

(*---------------------------------------------------------------------------*)
(* compressed version ... hard for derivative taker to do well with the      *)
(* nesting.                                                                  *)
(*---------------------------------------------------------------------------*)
(*
fun range r i j =
 if j < i then EMPTY
 else Cat (replicate r i,replicate (Or [EPSILON,r]) (j-i))
*)

fun dots n = if n <= 0 then [] else SIGMA::dots (n-1);

val num2byte = Word8.fromInt;
val byte2num = Word8.toInt;
val byte2char = Char.chr o Word8.toInt;
val char2byte = num2byte o Char.ord;

fun num2chset n =
 if 0 <= n andalso n <= 255
   then Chset(charset_of[Char.chr n])
 else raise ERR "num2chset" "";

val zero_chset = num2chset 0;

val byte2charset = num2chset o byte2num;

(*===========================================================================*)
(* Support for numeric intervals                                             *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* Contiguous char lists.                                                    *)
(*---------------------------------------------------------------------------*)

fun interval_charset b t = Chset(charset_of (map Char.chr (upto b t)))

fun nat_span n = if 0 <= n andalso n <= 255 then interval_charset 0 n else EMPTY;
fun neg_span i = if 0 <= i andalso i <= 255 then interval_charset i 255 else EMPTY;

(*---------------------------------------------------------------------------*)
(* Treats list as being in LSB order, and partitions it into a suffix block  *)
(* of zeros and a prefix block of non-zero numbers. We make a redundant      *)
(* check that the list is non-empty. If it happens that the prefix is empty  *)
(* that means that the input list was all zeroes, so we set the nums to [0]. *)
(*---------------------------------------------------------------------------*)

val lsb_split =
 let fun R [] = ([],[])
       | R (h::t) =
         case R t
          of ([],Z) => if h=0 then ([],0::Z) else ([h],Z)
           | (N,Z) => (h::N,Z)
 in fn list =>
    if null list then raise ERR "lsb_split" ""
    else case R list
          of ([],z::t) => ([z],t)
           | other => other
 end;

fun msb_split list =
 if null list then raise ERR "msb_split" "empty list"
 else
   let fun split [] = ([],[])
         | split (0::t) = (cons 0 ## I) (split t)
         | split list = ([],list)
  in case split list
      of (z::t,[]) => (t,[z])
       | other => other
  end;

(*---------------------------------------------------------------------------*)
(* To match the numbers from 0 to j, represented in n bytes, we first        *)
(* convert j into base 256, least-significant-byte first, so                 *)
(*                                                                           *)
(*   j = [k_1, ..., k_j, 0,...,0]                                            *)
(*                                                                           *)
(* where the trailing zeros are positions needed to bridge between the given *)
(* width n and the number of bytes needed to express the numbers from 0 to j *)
(*                                                                           *)
(* Then the regexp we are after is r1 + r2 where                             *)
(*                                                                           *)
(*   r1 = [0-k_1]...[0-k_(n-1)][k_n]zeros                                    *)
(*                                                                           *)
(* and                                                                       *)
(*                                                                           *)
(*   r2 = ...[0 - (k_n - 1)]zeros      ; n-1 dots (dot means any char)       *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)

val lsb_match_upto =
 let val _ = if alphabet_size <> 256
        then raise ERR "lsb_match_upto" "alphabet_size != 256"
        else ()
     fun list2regexp [] = raise ERR "list2regexp" "null list"
       | list2regexp [x] = nat_span x
       | list2regexp (h::t) =
         let val hpreds = catlist (dots (length t) @ [nat_span (h-1)])
             val hfixed = Cat(list2regexp t,num2chset h)
         in Or[hpreds, hfixed]
         end
 in fn j => fn width =>
    let val rep_256 = map byte2num (bytes_of j width)
    in case lsb_split rep_256
        of ([],_) => raise ERR "lsb_match_upto" "unreachable"
         | (numbers,zeros) =>
            catlist (list2regexp (rev numbers)
            :: List.map (K zero_chset) zeros)
    end
 end;

val lsb_match_downto =
 let val _ = if alphabet_size <> 256
             then raise ERR "lsb_match_downto" "alphabet_size != 256"
             else ()
     fun ilist2regexp [] = raise ERR "ilist2regexp" "null list"
       | ilist2regexp [x] = neg_span x
       | ilist2regexp (h::t) =
         let val hdesc = catlist (dots (length t) @ [neg_span (h+1)])
             val hfixed = Cat(ilist2regexp t,num2chset h)
         in
           Or[hdesc, hfixed]
         end
 in fn i => fn width =>
    let val rep_256 = map byte2num (bytes_of i width)
    in case lsb_split rep_256
        of ([],_) => raise ERR "lsb_match_downto" "unreachable"
         | (numbers,zeros) =>
             catlist (ilist2regexp (rev numbers)
             :: List.map (K zero_chset) zeros)
    end
 end;

val msb_match_upto =
 let val _ = if alphabet_size <> 256
        then raise ERR "msb_match_upto" "alphabet_size != 256"
        else ()
     fun list2regexp [] = raise ERR "msb_match_upto" "list2regexp: null list"
       | list2regexp [x] = nat_span x
       | list2regexp (h::t) =
         let val hpreds = catlist (nat_span (h-1) :: dots (length t))
             val hfixed = Cat(num2chset h,list2regexp t)
         in Or[hpreds, hfixed]
         end
 in fn j => fn width =>
    let val rep_256 = map byte2num (bytes_of j width)
    in case msb_split rep_256
        of ([],_) => raise ERR "msb_match_upto" "unreachable"
         | (zeros,numbers) =>
            catlist (List.map (K zero_chset) zeros @ [list2regexp numbers])
    end
 end;

val msb_match_downto =
 let val _ = if alphabet_size <> 256
             then raise ERR "msb_match_downto" "alphabet_size != 256"
             else ()
     fun ilist2regexp [] = raise ERR "msb_match_downto" "ilist2regexp: null list"
       | ilist2regexp [x] = neg_span x
       | ilist2regexp (h::t) =
         let val hdesc = catlist (neg_span (h+1) :: dots (length t))
             val hfixed = Cat(num2chset h, ilist2regexp t)
         in
           Or[hdesc, hfixed]
         end
 in fn i => fn width =>
    let val rep_256 = map byte2num (bytes_of i width)
    in case msb_split rep_256
        of ([],_) => raise ERR "msb_match_downto" "unreachable"
         | (zeros,numbers) =>
             catlist (List.map (K zero_chset) zeros @ [ilist2regexp numbers])
    end
 end;

val lsb_sing =
 let val _ = if alphabet_size <> 256
             then raise ERR "lsb_sing" "alphabet_size != 256"
             else ()
 in fn i => fn width =>
    let val rep_256 = bytes_of i width
    in catlist (List.map (num2chset o byte2num) rep_256)
    end
 end;

val msb_sing =
 let val _ = if alphabet_size <> 256
             then raise ERR "msb_sing" "alphabet_size != 256"
             else ()
 in fn i => fn width =>
    let val rep_256 = map (num2chset o byte2num) (bytes_of i width)
    in catlist (rev rep_256)
    end
 end;

fun match_downto LSB = lsb_match_downto
  | match_downto MSB = msb_match_downto

fun match_upto LSB = lsb_match_upto
  | match_upto MSB = msb_match_upto;

(*---------------------------------------------------------------------------*)
(* Lang (regexp_interval i j) = {x | i <= to_num x <= j}                     *)
(*---------------------------------------------------------------------------*)

fun regexp_interval lo hi order =
 if lo > hi
     then raise ERR "regexp_interval" "trivial interval"
 else
 if lo < 0 andalso hi < 0 then
  let val width = signed_width_256 lo
  in if hi = ~1 then
         match_downto order lo width
     else
         Diff (match_downto order lo width, match_downto order (hi+1) width)
  end
 else
 if lo < 0 andalso hi >= 0 then
  let val width = Int.max(signed_width_256 lo, signed_width_256 hi)
  in if hi = 0 then
       Or[match_downto order lo width, match_upto order 0 width]
     else
       Or [match_downto order lo width, match_upto order hi width]
  end
 else  (* lo and hi both non-negative *)
  let val width = unsigned_width_256 hi
  in if lo = 0 then
         match_upto order hi width
      else
         Diff (match_upto order hi width, match_upto order (lo-1) width)
  end;

fun sing_interval i order =
 let val width = if i < 0 then signed_width_256 i else unsigned_width_256 i
 in
   case order
    of LSB => lsb_sing i width
     | MSB => msb_sing i width
 end;


(* Interval approach
fun packed_intervals lists width order =
 let val intervals = map (fn list => (hd list, last list)) lists
     fun interval2regexp (lo,hi) =
      if lo > hi
        then raise ERR "interval2regexp" "trivial interval"
      else
      if lo < 0 andalso hi < 0 then
        (if hi = ~1 then
           match_downto order lo width
         else
           Diff (match_downto order lo width,
                 match_downto order (hi+1) width))
      else
      if lo < 0 andalso hi = 0 then
           Or[match_downto order lo width, match_upto order 0 width]
      else
      if lo < 0 andalso hi > 0 then
           Or [match_downto order lo width, match_upto order hi width]
      else  (* lo and hi both non-negative *)
       (if lo = 0 then
          match_upto order hi width
        else
          Diff (match_upto order hi width,
                match_upto order (lo-1) width))
 in
   Or (map interval2regexp intervals)
 end
*)

fun dest_chset (Chset cs) = cs
  | dest_chset other = raise ERR "dest_chset" "";

fun csets_union L =
 let val (L,z) = front_last L
     fun cs_union r cs = charset_union (dest_chset r) cs
 in
   Chset (itlist cs_union L (dest_chset z))
 end

fun bytes2charset bytes =
 let val (L,z) = front_last bytes
     fun add b cs = charset_insert (byte2char b) cs
 in
   Chset (itlist add L (charset_of [byte2char z]))
 end

(*---------------------------------------------------------------------------*)
(* Given a list of lists, all of same length, the hd element of each list is *)
(* the same.                                                                 *)
(*---------------------------------------------------------------------------*)

fun hd_card_eq_one [] = false
  | hd_card_eq_one ([]::t) = false (* Lib.all null t *)
  | hd_card_eq_one ((h::_)::rst) =
     let fun check [] = true
           | check ((g::_)::t) = h=g andalso check t
           | check other = false
     in check rst
     end

(*---------------------------------------------------------------------------*)
(* Given a list of lists, the last element of each list is the same.         *)
(*---------------------------------------------------------------------------*)

fun last_card_eq_one [] = false
  | last_card_eq_one ([]::rst) = false (* Lib.all null rst *)
  | last_card_eq_one (list::rst) =
     let val item = last list
         fun check [] = true
           | check (L::t) = item=last L andalso check t
     in check rst
     end

fun pull_front L =
 if hd_card_eq_one L
   then SOME (hd (hd L), map tl L)
   else NONE

fun pull_last L =
  if last_card_eq_one L
    then SOME (map butlast L, last (hd L))
    else NONE

fun pull_fronts L =
 case pull_front L
  of NONE => ([],L)
   | SOME (a,L') =>
      let val (A,L'') = pull_fronts L'
      in (a::A,L'')
      end
fun pull_lasts L =
 case pull_last L
  of NONE => (L,[])
   | SOME (L',z) =>
      let val (L'',Z) = pull_lasts L'
      in (L'',Z@[z])
      end

fun grabRun f a list acc =
 case list
  of [] => (acc,list)
   | h::t => if f h = a then grabRun f a t (h::acc) else (acc,list);

fun chunk f [] = []
  | chunk f (h::t) =
     let val (run,rst) = grabRun f (f h) (h::t) []
     in run :: chunk f rst
     end;

fun inv_image R f (a,b) = R (f a,f b);

fun sort3 X Y Z = Listsort.sort (inv_image Int.compare fst) [X,Y,Z];

(*---------------------------------------------------------------------------*)
(* Pick smallest regexp resulting from various strategies for building the   *)
(* regexp representing the interval union.                                   *)
(*---------------------------------------------------------------------------*)

fun crunch_interval ibytes =
 let val (L',Z) = pull_lasts ibytes
     val (A,L'') = pull_fronts L'
     fun singleton [_] = true | singleton _ = false
     val core =
       if null L'' then []
       else
       if Lib.all singleton L''
          then [bytes2charset (map hd L'')]
          else [Or (map (fn bytes => catlist(map byte2charset bytes)) L'')]
  in
   catlist (map byte2charset A @ core @ map byte2charset Z)
  end;

fun create_regexps intlist nbytes =
 let val intervalL = intervals intlist
     val _ = stdErr_print("Number of sub-intervals: "
                          ^Int.toString (length intervalL)^"\n")
     fun int_bytes i = bytes_of i nbytes
     val intervalL_bytes = map (map int_bytes) intervalL
     val intervalL_regexp = Or (map crunch_interval intervalL_bytes)

     val bytesL = map int_bytes intlist
     val last_sorted = Listsort.sort (inv_image Word8.compare last) bytesL
     val hd_sorted = Listsort.sort (inv_image Word8.compare hd) bytesL
     val last_chunks = chunk last last_sorted
     val hd_chunks = chunk hd hd_sorted
     val hd_regexp = Or (map crunch_interval hd_chunks)
     val last_regexp = Or (map crunch_interval last_chunks)
 in
  (intervalL_regexp, hd_regexp, last_regexp)
 end;

fun sub_intervals intlist nbytes order =
 let val (r1,r2,r3) = create_regexps intlist nbytes
     val sorted = sort3 (PolyML.objSize r1, r1)
                        (PolyML.objSize r2, r2)
                        (PolyML.objSize r3, r3)
     val nregexp = hd sorted
 in
    stdErr_print ("Size of regexp: "^Int.toString (fst nregexp)^"\n")
  ; snd nregexp
 end

fun bits_width pelt : int =
  case pelt
   of Pad i => i
    | Span (lo,hi) => interval_bit_width (lo,hi)

fun add_padding iwlist =
 let fun add ((Pad _,i)::(Pad _,j)::t)   = add ((Pad (i+j),i+j)::t)
       | add ((Pad _,i)::(Span jk,w)::t) = add ((Span jk,w+i)::t)
       | add ((Span jk,w)::(Pad _,i)::t) = add ((Span jk,w+i)::t)
       | add ((Span jk,w)::t) = (jk,w)::add t
       | add [(Pad _,_)] = raise ERR "add_padding" "padding but no interval?"
       | add [] = []
 in
   add iwlist
 end;

fun interval_width_string (p,w) =
 let open String IntInf
     fun ivl_str (Pad n)     = concat  ["padding: "]
       | ivl_str (Span(i,j)) = concat  ["interval: (",toString i,",",toString j,") ; "]
  in
   String.concat [ivl_str p, "width in bits: ", Int.toString w]
  end;

fun sum [] = 0
  | sum (h::t) = h + sum t;

fun pack_intervals list =
 let val _ = if null list then
             raise ERR "pack_intervals" "empty list input"
	     else ()
     val iwlist = map (fn x => (x,bits_width x)) list
     val _ = stdErr_print ("Packed interval.\n  "^
               String.concat (spread "\n  " (map interval_width_string iwlist))
                ^ "\n")
     val nbits = sum (map snd iwlist)
     val nbytes = let val bnd = nbits div 8
                  in if nbits mod 8 = 0 then bnd
                     else raise ERR "pack_intervals"
                         "subcomponent widths do not sum to a multiple of 8"
                  end
     val _ = stdErr_print ("Number of bytes needed: "^Int.toString nbytes^"\n")
     val piwlist = add_padding iwlist
     val intlist = interval_list_cat [] piwlist
     val _ = stdErr_print ("Cardinality of specified interval: "
                           ^Int.toString (length intlist)^"\n")
 in
   if Lib.all (fn i => zero <= i andalso i <= two_five_five) intlist
      (* fits in a byte *)
   then Chset (charset_of (map (Char.chr o IntInf.toInt) intlist))
   else
     sub_intervals intlist nbytes LSB
 end


fun tree_to_regexp tree =
 case tree
  of Ident ch => Chset (charset_of [ch])
   | Cset cset => Chset cset
   | Power(t,i) => replicate (tree_to_regexp t) i
   | Range(t,SOME i,SOME j) => range (tree_to_regexp t) i j
   | Range(t,NONE,SOME j) => range (tree_to_regexp t) 0 j
   | Range(t,SOME i,NONE) =>
     let val r = tree_to_regexp t
     in Cat(replicate r i, Star r)
     end
   | Range (t,NONE,NONE) => Star (tree_to_regexp t)
   | Interval(i,j,dir) => regexp_interval i j dir
   | Const (k,dir) => sing_interval k dir
   | Pack list => pack_intervals list
   | Ap("dot",[]) => DOT
   | Ap("digit",[]) => DIGIT
   | Ap("alphanum",[]) => ALPHANUM
   | Ap("whitespace",[]) => WHITESPACE
   | Ap("Star",[t]) => Star(tree_to_regexp t)
   | Ap("Plus",[t]) => let val r = tree_to_regexp t in Cat(r,Star r) end
   | Ap("Opt",[t]) => Or[EPSILON,tree_to_regexp t]
   | Ap("Sum",[t1,t2]) => Or[tree_to_regexp t1,tree_to_regexp t2]
   | Ap("And",[t1,t2]) => Neg(Or[Neg(tree_to_regexp t1),Neg(tree_to_regexp t2)])
   | Ap("Juxt",[t1,t2]) => Cat(tree_to_regexp t1,tree_to_regexp t2)
   | Ap("Not",[t]) => Neg(tree_to_regexp t)
   | Ap("interval",[]) => raise ERR "tree_to_regexp" "missing interval parameters"
   | Ap(other,_) => raise ERR "tree_to_regexp" ("unknown operator: "^other)
;

fun fromSubstring sstring =
 tree_to_regexp (substring_to_tree sstring)
 handle e => raise wrap_exn "Regexp_Type" "fromSubstring" e;

fun fromString s = tree_to_regexp (string_to_tree s)
 handle e => raise wrap_exn "Regexp_Type" "fromString" e;

fun fromQuote q = tree_to_regexp (quote_to_tree q)
 handle e => raise wrap_exn "Regexp_Type" "fromQuote" e;

end
