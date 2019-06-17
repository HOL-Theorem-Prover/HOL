(*===========================================================================*)
(* Regexps for numeric intervals                                             *)
(*===========================================================================*)

structure Regexp_Numerics :> Regexp_Numerics =
struct

open Lib Feedback regexpMisc Regexp_Type;

val ERR = mk_HOL_ERR "Regexp_Numerics";

fun copy x n = List.tabulate (n,K x) handle _ => [];
fun padL list x width = copy x (width - length list) @ list;
fun padR list x width = list @ copy x (width - length list);


(*---------------------------------------------------------------------------*)
(* Least- and Most- significant byte                                         *)
(*---------------------------------------------------------------------------*)

datatype direction = LSB | MSB

fun dir2string MSB = "MSB"
  | dir2string LSB = "LSB";

fun string2dir "MSB" = SOME MSB
  | string2dir "LSB" = SOME LSB
  | string2dir other = NONE;

(*---------------------------------------------------------------------------*)
(* Basic maps between bytes, chars, and ints                                 *)
(*---------------------------------------------------------------------------*)

val byte2char = Char.chr o Word8.toInt;
val char2byte = Word8.fromInt o Char.ord;

fun ii2byte i = Word8.fromInt (IntInf.toInt i);
fun byte2ii w = IntInf.fromInt(Word8.toInt w);

val eight = Word.fromInt 8

(*---------------------------------------------------------------------------*)
(* Maps to and from byte lists                                               *)
(*---------------------------------------------------------------------------*)

fun n2l (n:IntInf.int) =
  if IntInf.<=(n,0) then
    []
  else IntInf.toInt(IntInf.mod(n,256))::n2l (IntInf.div(n,256))

fun l2n [] = 0
  | l2n (h::t) = h + 256 * l2n t;

val n256 = IntInf.fromInt 256;
fun log256 n = IntInf.log2 n div 8;
fun exp256 n = IntInf.pow(n256,n);


(*---------------------------------------------------------------------------*)
(* Minimum bytes needed to express unsigned and signed quantities            *)
(*---------------------------------------------------------------------------*)

fun unsigned_width 0 = 1  (* width in bytes *)
  | unsigned_width i = 
     if 0 < i then 1 + log256 i
     else raise ERR "unsigned_width" "negative input";

fun twos_comp_width i = 
 let val k = unsigned_width (IntInf.abs i)
     val bound = twoE (k*8 - 1)
 in 
    if ~bound <= i andalso i < bound then k else k+1
 end;

fun twos_comp_interval_width (i,j) = 
    Int.max(twos_comp_width i, twos_comp_width j);

(*---------------------------------------------------------------------------*)
(* Map numbers to strings                                                    *)
(*                                                                           *)
(* bytes_of w i lays out i into w bytes                                      *)
(*---------------------------------------------------------------------------*)

fun bytes_of w i =
 let open IntInf
 in if Int.<= (w,1) then 
      [ii2byte i]
    else
      ii2byte (andb(i,0xFF)) :: bytes_of (Int.-(w,1)) (~>>(i,eight))
 end

fun int2string w i =
 String.implode 
    (List.map byte2char (bytes_of w (IntInf.fromInt i)))

fun int2string_msb w i =
 String.implode 
     (rev (List.map byte2char (bytes_of w (IntInf.fromInt i))));


fun value (list :  IntInf.int list) = 
 let open IntInf
 in case list 
     of [] => 0
      | h::t => h + 256 * value t
 end;

val num_of = value o List.map byte2ii;

fun int_of wlist =
 let val (A,a) = Lib.front_last wlist
     val wlist' = List.map byte2ii A @ [IntInf.fromInt(Word8.toIntX a)]
 in value wlist'
 end;

val string2num = num_of o List.map char2byte o String.explode;
val string2int = int_of o List.map char2byte o String.explode;

(*---------------------------------------------------------------------------*)
(* MSB versions                                                              *)
(*---------------------------------------------------------------------------*)

fun num_of_msb wlist = num_of (rev wlist);
fun int_of_msb wlist = int_of (rev wlist);

val string2num_msb = num_of_msb o List.map char2byte o String.explode;
val string2int_msb = int_of_msb o List.map char2byte o String.explode;

(*
fun test r = 
 let val r' = Regexp_Match.normalize
     val tester = #matchfn(regexpLib.matcher SML r')
 in      
     fn i => test (int2string i)
 end;
*)

(*===========================================================================*)
(* Intervals                                                                 *)
(*===========================================================================*)

fun num2regexp n = Chset(charset_span n n);

val zero_regexp = num2regexp 0;

(*---------------------------------------------------------------------------*)
(* Regexp for the interval {n | 0 <= lo <= n <= hi} in binary encoding. The  *)
(* dir argument specifies the order in which bytes of the number are laid    *)
(* out, and the width argument specifies the *minimum* width, in bytes, that *)
(* the number is expected to fill.                                           *)
(*---------------------------------------------------------------------------*)

fun num_interval dir width lo hi =
 let val _ = if lo < 0 orelse hi < lo then 
               raise ERR "num_interval" "malformed interval" 
             else ()
     val _ = if width < unsigned_width hi then 
               raise ERR "num_interval" "given width not large enough" 
             else ()
     val lorep = rev(padR (n2l lo) 0 width)
     val hirep = rev(padR (n2l hi) 0 width)
     fun finalize LoL =
         case dir
          of LSB => rev (map catlist LoL)
           | MSB => rev (map (catlist o rev) LoL)
     fun mk_ivls [] acc = mk_or (finalize acc)
       | mk_ivls ((prefix,[],[])::t) acc = raise ERR "num_interval" "empty lists"
       | mk_ivls ((prefix,[r1],[r2])::t) acc =
                mk_ivls t ((Chset(charset_span r1 r2)::prefix)::acc)
       | mk_ivls ((prefix,q1::r1,q2::r2)::t) acc =
          if q1=q2 then
             mk_ivls ((num2regexp q1::prefix,r1,r2)::t) acc
          else (* have q1 < q2 *)
          if Lib.all (equal 0) r1 andalso Lib.all (equal 255) r2 then
             let val thing = dots (length r1) @ (Chset(charset_span q1 q2) :: prefix)
             in mk_ivls t (thing::acc)
             end
          else
          if q1=0 then  (* fill up to e2 slot *)
             let val w = 1 + length r1
                 val ceil = padR [1] 0 w
                 val preceil = padR [255] 255 (w-1)
                 val thing1 = (num2regexp 0::prefix,r1,preceil)
                 val thing2 = (prefix,ceil,q2::r2)
(*       following needs more thought to be better than current version
         val thing1 = (prefix,q1::r1,padR [q2-1] 255 w)
         val thing2 = (prefix,padR [q2] 0 w,q2::r2)
*)
             in
                mk_ivls (thing1::thing2::t) acc
             end
          else
          let val w = 1 + length r1
          in case (Lib.all (equal 0) r1,Lib.all (equal 255) r2)
              of (true,true)  => raise ERR "mk_ivls" "inaccessible"
               | (true,false) =>
                   let val thing1 = (prefix,q1::r1,padR [q2-1] 255 w)
                       val thing2 = (prefix,padR [q2] 0 w,q2::r2)
                   in mk_ivls (thing1::thing2::t) acc
                   end
               | (false,true) =>
                   let val thing1 = (prefix,q1::r1,padR [q1] 255 w)
                       val thing2 = (prefix,padR [q1+1] 0 w,q2::r2)
                   in mk_ivls (thing1::thing2::t) acc
                   end
               | (false,false) =>
                   let val thing1 = (prefix,q1::r1,padR [q1] 255 w)
                       val thing2 =
                          if (q1 + 1 < q2)
                           then [(prefix,padR [q1+1] 0 w,padR [q2-1] 255 w)]
                           else []
                       val thing3 = (prefix,padR [q2] 0 w,q2::r2)
                   in
                     mk_ivls ([thing1] @ thing2 @ [thing3] @ t) acc
                   end
          end
       | mk_ivls other wise = raise ERR "num_interval" "lists of different length"
 in
   mk_ivls [([]:regexp list,lorep,hirep)] []
 end


(*
fun Ninterval lo hi =
  num_interval MSB (unsigned_width (IntInf.fromInt hi))
       (IntInf.fromInt lo)
       (IntInf.fromInt hi)
Ninterval 38 23567900;
Ninterval 67537 81005;
Ninterval 0 4611686018427387903;  (* Int63.maxInt *)
*)

(*---------------------------------------------------------------------------*)
(* Regexp for binary twos complement representations of integers in the      *)
(* interval lo .. hi.                                                        *)
(*---------------------------------------------------------------------------*)

fun twos_comp_interval dir width lo hi =
 if hi < lo then
     raise ERR "twos_comp_interval" "hi less than lo"
 else
 if width < twos_comp_interval_width (lo,hi) then
   raise ERR "twos_comp_interval" "width is too small"
 else
 if 0 <= lo andalso 0 <= hi then
    num_interval dir width lo hi
 else
 let val top = twoE (width * 8)
 in
   if lo < 0 andalso hi >= 0 then
       (if hi + 1 = top + lo  (* contiguous *) then 
           catlist (dots width)
        else
           Or [num_interval dir width (top + lo) (top-1),
               num_interval dir width 0 hi])
   else
   if lo < 0 andalso hi < 0 then
      num_interval dir width (top+lo) (top+hi)
   else raise ERR "twos_comp_interval" "unexpected values for lo and hi"
 end

(*---------------------------------------------------------------------------*)
(* Regexp for "zigzag" encoded integer in the interval lo .. hi.             *)
(*---------------------------------------------------------------------------*)

fun int_to_zz i = if i >= 0 then 2*i else (2 * IntInf.abs i) - 1;

fun zz_width i = unsigned_width (int_to_zz i);

(*---------------------------------------------------------------------------*)
(* Regexp for numbers >= n                                                   *)
(*---------------------------------------------------------------------------*)

(*
fun num_leq dir width n = num_interval dir width 0 n;

fun num_gtr dir width n = 
  And (Neg (num_interval dir width 0 n),
       catlist(dots (unsigned_width n)));


val r = Regexp_Match.normalize (num_gtr LSB 2 1456);

val basic_evens = filter (fn x => x mod 2 = 0) (upto 0 255);
val be_charset = Regexp_Type.charset_of (map Char.chr basic_evens);
val even_regexp = Cat(Chset be_charset,Star DOT);
val even_regexp_term = regexpSyntax.regexp_to_term even_regexp;

val basic_odds = filter (fn x => x mod 2 = 1) (upto 0 255);
val bo_charset = Regexp_Type.charset_of (map Char.chr basic_odds);
val odd_regexp = Cat(Chset bo_charset,Star DOT);
val odd_regexp_term = regexpSyntax.regexp_to_term odd_regexp;

*)

(*
fun zigzag_interval dir width lo hi =
 if hi < lo then
     raise ERR "zigzag_interval" "hi less than lo"
 else
 if width < Int.max(zz_width lo, zz_width hi) then
   raise ERR "zigzag_interval" "width is too small"
 else
 if 0 <= lo (* all positive *) then
    EVEN && (>= (2*lo)) && (<= (2*hi)) else 
 if hi < 0 (* all negative *) then
    ODD && (>= (2*(abs hi)-1) && (<= (2*(abs lo)-1) 
 else (* lo < 0 and 0 <= hi *)
  let fun singleton n = num_interval dir width n n
      val lomag = IntInf.abs lo
  in if lomag < hi then 
        let val span = num_interval dir width 0 (int_to_zz lomag)
            val points = map int_to_zz (bigUpto (lomag+1) hi)
            val pt_regexps = map singleton points
        in mk_or (span :: pt_regexps)
        end
     else
      if hi < lomag then 
        let val span = num_interval dir width 0 (int_to_zz hi)
            val points = map int_to_zz (bigUpto (hi+1) lomag)
            val pt_regexps = map singleton points
        in mk_or (span :: pt_regexps)
	end
     else (* hi = lomag *)
      num_interval dir width 0 (int_to_zz hi)
  end;

(*---------------------------------------------------------------------------*)
(* Regexp for sign + magnitude representations of integers in the interval   *)
(* lo .. hi. Characters #"-" and #"+" are prepended to the unsigned binary   *)
(* representations. Zero is Cat(#"+",<encoded-zero>). There is no negative   *)
(* zero.                                                                     *)
(*---------------------------------------------------------------------------*)

fun gen_sign_magn_interval lo hi width dir =
 let val plus = Chset(charset_sing #"+")
     val minus = Chset(charset_sing #"-")
 in
  if hi < lo then
     raise ERR "sign_magn_interval" "hi less than lo"
 else
  if 0 <= lo andalso 0 <= hi then
    Cat(plus,num_interval dir width lo hi)
 else
  if lo < 0 andalso hi < 0 then
    Cat(minus,num_interval dir width (IntInf.abs hi) (IntInf.abs lo))
 else
  Or [Cat(minus,num_interval dir width 1 (IntInf.abs lo)),
      Cat(plus,num_interval dir width 0 hi)]
 end

fun magn_bin_width lo hi =
if hi < lo then
     raise ERR "sign_magn_interval_bin_width"
               "hi less than lo"
 else
  Int.max(unsigned_width (IntInf.abs lo),
          unsigned_width (IntInf.abs hi))
;

fun sign_magn_interval lo hi dir =
    gen_sign_magn_interval lo hi (magn_bin_width lo hi) dir;

fun sign_magn_sing_interval i dir = sign_magn_interval i i dir;
*)

end;
