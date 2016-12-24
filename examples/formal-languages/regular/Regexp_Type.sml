(*---------------------------------------------------------------------------*)
(* ML type of regexps                                                        *)
(*---------------------------------------------------------------------------*)

structure Regexp_Type :> Regexp_Type =
struct

open Lib Feedback;

val ERR = mk_HOL_ERR "Regexp_Type";

type charset = IntInf.int;

datatype regexp 
   = Chset of charset
   | Cat of regexp * regexp
   | Star of regexp
   | Or of regexp list
   | Neg of regexp;

fun And (r1,r2) = Neg(Or[Neg r1,Neg r2]);
fun Diff (r1,r2) = And(r1,Neg r2);

(*---------------------------------------------------------------------------*)
(* Alphabet                                                                  *)
(*---------------------------------------------------------------------------*)

val alphabet_size = 256;
val alphabetN = List.tabulate (alphabet_size,I)
val alphabet = map Char.chr alphabetN;

(*---------------------------------------------------------------------------*)
(* Character sets                                                            *)
(*---------------------------------------------------------------------------*)

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

fun charset_union cs1 cs2 = IntInf.orb(cs1,cs2);

fun charset_diff cs1 cs2 = IntInf.andb(cs1,IntInf.notb cs2)

val charset_whitespace = charset_of (String.explode" \n\r\t\f");
val charset_digit      = charset_of (String.explode"0123456789");
val charset_alpha = 
  charset_of (String.explode "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ");
val charset_alphanum = charset_insert #"_" (charset_union charset_digit charset_alpha);

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
 String.concat ["[", String.implode (filter (C charset_mem cset) alphabet), "]"];

 
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

fun pp_regexp ppstrm = 
 let open Portable
     val {add_string, begin_block, end_block, add_break,...} = with_ppstream ppstrm
     fun paren i j x = if i < j then () else add_string x
     fun pp i regexp = 
      case regexp
       of Chset cs => add_string (charset_string cs)
        | Cat(s,t) => 
            let val rlist = strip_cat regexp
            in 
               paren i 2 "("
             ; begin_block INCONSISTENT 2
             ; List.app (pp 2) rlist
             ; end_block ()
             ; paren i 2 ")"
            end
        | Or rlist => 
           let in
               paren i 1 "("
             ; begin_block INCONSISTENT 1
             ; pr_list (pp 1)
                       (fn () => add_string " |")
                       (fn () => add_break(1,0)) rlist
             ; end_block ()
             ; paren i 1 ")"
           end
        | Neg r => 
            let in 
               paren i 3 "("
             ; add_string "~"
             ; begin_block CONSISTENT 1
             ; pp 3 r
             ; end_block ()
             ; paren i 3 ")"
            end 
        | Star r => 
            let in 
               paren i 4 "("
             ; begin_block CONSISTENT 1
             ; pp 4 r
             ; end_block ()
             ; add_string "*"
             ; paren i 4 ")"
            end 
 in
   pp 0 
 end;


(*---------------------------------------------------------------------------*)
(* print regexp as string to stdOut                                          *)
(*---------------------------------------------------------------------------*)

val print_regexp = Portable.pprint pp_regexp;

(*---------------------------------------------------------------------------*)
(* Assumes v1 and v2 are of equal length                                     *)
(*---------------------------------------------------------------------------*)

val charset_compare = IntInf.compare;

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
(* Python-style regexp lexer and parser                                      *)
(*---------------------------------------------------------------------------*)

datatype direction = LSB | MSB;

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
   | pack of (IntInf.int * IntInf.int) list
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
  

fun pack2string flds = 
 let fun field_to_strings (lo,hi) = 
          String.concat["(", IntInf.toString lo, ",", IntInf.toString hi, ")"]
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
(* \p{(lo,hi), ..., (lo,hi)}                                                 *)
(*                                                                           *)
(* where the \p has already been consumed by the lexer.                      *)
(*---------------------------------------------------------------------------*)

fun get_pack strm = 
 let open Substring
  fun get_field strm = 
      case eat_then #"(" getNum strm
       of NONE =>  NONE
        | SOME(i,strm) =>
      case eat_then #"," getNum strm
       of NONE =>  NONE
        | SOME(j,strm) =>
      eat_then #")" (fn strm => SOME((i,j),strm)) strm
  fun get_fields list strm = 
       case get_field strm
        of NONE => eat_then #"}" (fn strm => SOME (pack(rev list), strm)) strm
         | SOME (ij,strm) => 
             try_alt
              (eat_then #"," (get_fields (ij::list)))
              (eat_then #"}" (fn strm => SOME (pack(rev (ij::list)), strm)))
             strm
 in
  eat_then #"{" (get_fields []) strm
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
              | Pack of (IntInf.int * IntInf.int) list;


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

(* compressed version ... hard for derivative taker to do well with the nesting.
fun range r i j = 
 if j < i then EMPTY
 else Cat (replicate r i,replicate (Or [EPSILON,r]) (j-i))
*)
fun range r i j = 
 if j < i then EMPTY 
 else Or (map (replicate r) (upto i j));


(*---------------------------------------------------------------------------*)
(* Numeric intervals                                                         *)
(*---------------------------------------------------------------------------*)

fun unsigned_width_bits (n:IntInf.int) = 
 if n < 0 then raise ERR "unsigned_width_bits" "negative number" else
 if n < 2 then 1
 else 1 + unsigned_width_bits (n div 2);

fun signed_width_bits (n:IntInf.int) = 
  let fun fus bits = 
       let val N = IntInf.pow(2,bits-1)
       in if ~N <= n andalso n <= N-1 then bits else fus (bits+1)
       end
 in fus 0
 end;

fun unsigned_width_256 (n:IntInf.int) = 
 if n < 0 then raise ERR "unsigned_width_256" "negative number" else
 if n < 256 then 1
 else 1 + unsigned_width_256 (n div 256);

fun signed_width_256 (n:IntInf.int) = 
  let fun fus k acc = 
       let val lo = ~(IntInf.pow(2,k-1))
           val hi = IntInf.pow(2,k-1) - 1
       in if lo <= n andalso n <= hi
            then acc
            else fus (k+8) (acc+1)
       end
 in fus 8 1
 end;

fun byte_me i = Word8.fromInt (IntInf.toInt i);
fun inf_byte w = IntInf.fromInt(Word8.toInt w);

val bytes_of = 
 let val eight = Word.fromInt 8
     val mask = 0xFF:IntInf.int
     fun step i w =
      if w=1 then [byte_me i]
      else
        let val a = IntInf.andb(i,mask)
            val j = IntInf.~>>(i,eight)
       in byte_me a::step j (w-1)
       end
  in
   step
 end

fun lsb_signed i   = bytes_of i (signed_width_256 i);
fun lsb_unsigned i = bytes_of i (unsigned_width_256 i);
fun msb_signed i   = rev (lsb_signed i);
fun msb_unsigned i = rev (lsb_unsigned i);

fun lsb_num_of wlist : IntInf.int = 
 let fun value [] = 0
      | value (h::t) = h + 256 * value t
 in value (map inf_byte wlist)
 end;

fun lsb_int_of wlist = 
 let fun value [] = 0
       | value (h::t) = h + 256 * value t
     val (A,a) = Lib.front_last wlist
     val wlist' = map inf_byte A @ [IntInf.fromInt(Word8.toIntX a)]
 in value wlist'
 end;

fun msb_num_of wlist = lsb_num_of (rev wlist);
fun msb_int_of wlist = lsb_int_of (rev wlist);

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
      if lo < 0 andalso hi >= 0 then 
        (if hi = 0 then
           Or[match_downto order lo width, match_upto order 0 width]
         else
           Or [match_downto order lo width, match_upto order hi width])
      else  (* lo and hi both non-negative *)
       (if lo = 0 then 
          match_upto order hi width
        else 
          Diff (match_upto order hi width, 
                match_upto order (lo-1) width))
 in
   Or (map interval2regexp intervals)
 end


val allones = IntInf.notb(IntInf.fromInt 0);

(*---------------------------------------------------------------------------*)
(* Clear top (all but rightmost width) bits in w                             *)
(*---------------------------------------------------------------------------*)

fun clear_top_bits width w = 
 let open IntInf
     val mask = notb(<<(allones,Word.fromInt(width)))
 in andb(w,mask)
 end

fun clear_bot_bits width w = 
 let open IntInf
 in ~>>(w,Word.fromInt width)
 end

fun sign_extend w width = 
 let open IntInf
 in if ~>>(w,Word.fromInt (width - 1)) = 1
  then (* signed *)
     orb(w,IntInf.<<(allones,Word.fromInt width))
  else w
 end

fun icat w shift i = 
 let val shiftw = Word.fromInt shift
     val shifted = IntInf.<<(w,shiftw)
     val x = clear_top_bits shift (IntInf.fromInt i)
 in 
   IntInf.orb(shifted,x)
 end

fun find_width (lo,hi) = 
 if lo > hi 
  then raise ERR "find_width" "malformed interval (lo > hi)"
 else
 if lo < 0 andalso hi < 0 
    then signed_width_bits lo else
 if lo < 0 andalso hi >= 0 
    then Int.max(signed_width_bits lo, signed_width_bits hi)
 else  (* lo and hi both non-negative *)
   unsigned_width_bits hi;

fun sum [] = 0
  | sum (h::t) = h + sum t;

fun add_slop iwlist slop = 
 let fun add [(p,w)] = [(p,w+slop)]
       | add (h::t) = h::add t
       | add [] = raise ERR "add_slop" "expected non-empty list of intervals"
 in 
   add iwlist
 end;

fun intervals list = 
 let val slist = Listsort.sort Int.compare list
     fun follows j i = j = i + 1
     fun chop [] A = rev (map rev A)
       | chop (h::t) [] = chop t [[h]]
       | chop (h::t) ([]::rst) = chop t ([h]::rst)
       | chop (h::t) ((a::L)::rst) = 
          if follows h a
           then chop t ((h::a::L)::rst)
           else chop t ([h]::(a::L)::rst)
 in
   chop slist []
 end;


fun pack_intervals ilist = 
 let val iwlist = map (fn x => (x,find_width x)) ilist
     val nbits = sum (map snd iwlist)
     val nbytes = let val bnd = nbits div 8 
                  in if nbits mod 8 = 0 then bnd else 1 + bnd
                  end
     val slop = nbytes * 8 - nbits
     val iwlist' = add_slop iwlist slop
     fun step A width B = 
      List.concat 
        (List.map (fn a => List.map (icat a width) B) A)
     fun iter W [] = W
       | iter W (((lo,hi),width)::t) = iter (step W width (upto lo hi)) t
 in
   case iwlist'
   of [] => raise ERR "pack_intervals" "supposedly unreachable!"
    | ((lo,hi),_)::t =>
       let val intlist = iter (upto lo hi) t
           val sections = intervals intlist
       in
          packed_intervals sections nbytes LSB
       end
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


(* Testing packed intervals

`\i{~90,90}\i{0,59}\i{0,5999}\p{(~180,180),(0,59)}\i{0,5999}`;

val ilist = [(~180,180),(0,59)];

fun byte_me i = Word8.fromInt (IntInf.toInt i);
fun inf_byte w = IntInf.fromInt(Word8.toInt w);

val bytes_of = 
 let val eight = Word.fromInt 8
     val mask = 0xFF:IntInf.int
     fun step i n =
      if n=1 then [byte_me i]
      else
        let val a = IntInf.andb(i,mask)
            val j = IntInf.~>>(i,eight)
       in byte_me a::step j (n-1)
       end
  in
   step
 end

val allones = IntInf.notb(IntInf.fromInt 0);

(*---------------------------------------------------------------------------*)
(* Clear top (all but rightmost width) bits in w                             *)
(*---------------------------------------------------------------------------*)

fun clear_top_bits width w = 
 let open IntInf
     val mask = notb(<<(allones,Word.fromInt(width)))
 in andb(w,mask)
 end

fun clear_bot_bits width w = 
 let open IntInf
 in ~>>(w,Word.fromInt width)
 end

fun sign_extend w width = 
 let open IntInf
 in if ~>>(w,Word.fromInt (width - 1)) = 1
  then (* signed *)
     orb(w,IntInf.<<(allones,Word.fromInt width))
  else w
 end

fun icat w shift i = 
 let val shiftw = Word.fromInt shift
     val shifted = IntInf.<<(w,shiftw)
     val x = clear_top_bits shift (IntInf.fromInt i)
 in 
   IntInf.orb(shifted,x)
 end

fun allpairs A B = 
  List.concat(map (fn a => map (fn b => (a,b)) B) A);

val match = matcher SML o Regexp_Type.fromQuote;

val tester = #matchfn (match `\p{(~180,180),(0,59)}`);

fun check (a,b) = 
  tester (String.implode (map byte2char (bytes_of (icat a 7 b) 2)))

fun alltests (lo1,hi1) (lo2,hi2) = 
 let val A = upto lo1 hi1
     val B = upto lo2 hi2
     val AxB = allpairs A B
 in 
  List.all check AxB
 end;

alltests  (~180,180) (0,59);

check (181,59);
Lib.all (equal false)
        (map (fn i => check (181,i)) (upto 0 59));

Lib.all (equal false)
        (map (fn i => check (~181,i)) (upto 0 59));


val tester = 
 #matchfn (match `\i{~90,90}\i{0,59}\i{0,5999}\p{(~180,180),(0,59)}\i{0,5999}`)

val tester = 
 #matchfn (match `\i{~90,90}\i{0,59}\i{0,5999}\i{~180,180}\i{0,59}\i{0,5999}`)


fun bin i = IntInf.fmt StringCvt.BIN i;

val input = icat ~180 7 24;
sign_extend(clear_top_bits 7 test) 7;
sign_extend(clear_bot_bits 7 test) 7;

(* swapped *)
val test = icat 24 9 ~180;
sign_extend (clear_top_bits 9 test) 9;
sign_extend (clear_bot_bits 9 test) 9;

val tspan = upto 0 59;
val dspan = upto ~180 180;

fun crunch a bwidth b = bytes_of (icat a bwidth b) 2;

*)
