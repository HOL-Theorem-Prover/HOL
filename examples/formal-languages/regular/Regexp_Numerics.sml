(*===========================================================================*)
(* Regexps for numbers and numeric intervals                                 *)
(*===========================================================================*)

structure Regexp_Numerics :> Regexp_Numerics =
struct

open Lib Feedback regexpMisc Regexp_Type Regexp_Match;

val ERR = mk_HOL_ERR "Regexp_Numerics";

type word8 = Word8.word;
type bigint = IntInf.int

fun copy x n = List.tabulate (n,K x) handle _ => [];
fun padL list x width = copy x (width - length list) @ list;
fun padR list x width = list @ copy x (width - length list);


(*---------------------------------------------------------------------------*)
(* Least- and Most- significant byte                                         *)
(*---------------------------------------------------------------------------*)

datatype endian = LSB | MSB

fun compare_endian(LSB,MSB) = LESS
  | compare_endian(MSB,LSB) = GREATER
  | compare_endian other    = EQUAL

fun endian2string MSB = "MSB"
  | endian2string LSB = "LSB";

fun string2endian "MSB" = SOME MSB
  | string2endian "LSB" = SOME LSB
  | string2endian other = NONE;

datatype encoding = Unsigned | Twos_comp | Zigzag | Sign_mag ;

(*---------------------------------------------------------------------------*)
(* ZigZag encoding as an int -> posint map                                   *)
(*---------------------------------------------------------------------------*)

fun zigzag i = if i >= 0 then 2*i else (2 * IntInf.abs i) - 1;

fun undo_zigzag n =
  case IntInf.divMod(n,IntInf.fromInt 2)
   of (k,0) => k
    | (k,_) => ~(k+1);

(*---------------------------------------------------------------------------*)
(* Sign-magnitude encoding as an int -> posint map                           *)
(*---------------------------------------------------------------------------*)

fun sign_mag i = if i >= 0 then 2*i else (2 * IntInf.abs i) + 1;

fun undo_sign_mag n =
 if n = 1 then 0
 else
  case IntInf.divMod(n,IntInf.fromInt 2)
   of (k,0) => k
    | (k,_) => ~k;

(*---------------------------------------------------------------------------*)
(* Minimum bytes needed to express unsigned and signed quantities            *)
(*---------------------------------------------------------------------------*)

fun log256 n = IntInf.log2 n div 8;

fun unsigned_width i =
   if i = 0 then 1 else
   if 0 < i then 1 + log256 i
   else raise ERR "unsigned_width" "negative input";

fun twos_comp_width i =
 let val k = unsigned_width (IntInf.abs i)
     val bound = twoE (k*8 - 1)
 in
    if ~bound <= i andalso i < bound then k else k+1
 end;

fun width_of Unsigned  = unsigned_width
  | width_of Twos_comp = twos_comp_width
  | width_of Zigzag    = unsigned_width o zigzag
  | width_of Sign_mag  = unsigned_width o sign_mag;

fun pair_max f = Int.max o (f##f)

fun interval_width Unsigned  = pair_max unsigned_width
  | interval_width Twos_comp = pair_max twos_comp_width
  | interval_width Zigzag    = pair_max (width_of Zigzag)
  | interval_width Sign_mag  = pair_max (width_of Sign_mag);

(*---------------------------------------------------------------------------*)
(* Twos complement encoding as an int -> posint map.                         *)
(*---------------------------------------------------------------------------*)

fun twos_comp w i =
 let val top = twoE (8*w)
     val bound = IntInf.div(top, IntInf.fromInt 2)
 in if ~bound <= i andalso i < bound then
       (if i >= 0 then i else top + i)
    else raise ERR "twos_comp" "width too small"
 end;

fun undo_twos_comp w n =
 let val top = twoE (8*w)
     val bound = IntInf.div(top, IntInf.fromInt 2)
 in if 0 <= n andalso n < top then
      (if n < bound then n else ~(top - n))
    else raise ERR "undo_twos_comp" "width too small"
 end;

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

val n2l =
 let open IntInf
     fun chunks n =
       if n=0 then []
       else toInt(op mod(n,256)) :: chunks (op div(n,256))
 in
   fn i:IntInf.int =>
        if i < 0 then
           raise ERR "n2l" "negative input"
         else
           chunks i
 end;

fun l2n [] = IntInf.fromInt 0
  | l2n (h::t) = IntInf.fromInt h + 256 * l2n t;

(*---------------------------------------------------------------------------*)
(* bytes_of w i lays out i into w bytes in LSB                               *)
(*                                                                           *)
(* w should be large enough to capture i                                     *)
(*---------------------------------------------------------------------------*)

fun bytes_of w i =
 let open IntInf
 in if Int.<= (w,1) then
      [ii2byte i]
    else
      ii2byte (andb(i,0xFF)) :: bytes_of (Int.-(w,1)) (~>>(i,eight))
 end

(*---------------------------------------------------------------------------*)
(* Maps from numbers to strings                                              *)
(*---------------------------------------------------------------------------*)

fun ii2s LSB w i = String.implode (map byte2char (bytes_of w i))
  | ii2s MSB w i = String.implode (rev (map byte2char (bytes_of w i)))

(*---------------------------------------------------------------------------*)
(* It can be that the specified width is not enough to properly represent i, *)
(* so we take the max                                                        *)
(*---------------------------------------------------------------------------*)

fun iint2string enc d w i =
 let val width = Int.max(w,width_of enc i)
 in ii2s d width
      (case enc
        of Unsigned  => i
         | Twos_comp => twos_comp width i
         | Zigzag    => zigzag i
         | Sign_mag  => sign_mag i)
 end

val int2string = iint2string Twos_comp LSB 1 o IntInf.fromInt;

(*---------------------------------------------------------------------------*)
(* Maps from strings to numbers                                              *)
(*---------------------------------------------------------------------------*)

val unsigned_value_of = l2n o map Word8.toInt;

fun twos_comp_value_of (list : word8 list) =
 let open IntInf
 in case list
     of [] => IntInf.fromInt 0
      | [e] => Word8.toLargeIntX e
      | h::t => byte2ii h + 256 * twos_comp_value_of t
 end;

fun string2iint enc dir =
 let fun vfn Unsigned  = unsigned_value_of
       | vfn Twos_comp = twos_comp_value_of
       | vfn Zigzag    = zigzag o unsigned_value_of
       | vfn Sign_mag  = sign_mag o unsigned_value_of
 in
  case dir
   of LSB => vfn enc o List.map char2byte o String.explode
    | MSB => vfn enc o rev o List.map char2byte o String.explode
 end;

val string2int = IntInf.toInt o string2iint Twos_comp LSB;

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

fun num_interval dir width (lo,hi) =
 let val _ = if lo < 0 orelse hi < lo then
               raise ERR "num_interval" "malformed interval"
             else ()
     val _ = if width < interval_width Unsigned (lo,hi) then
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

fun twos_comp_interval dir width (lo,hi) =
 if hi < lo then
     raise ERR "twos_comp_interval" "hi less than lo"
 else
 if width < interval_width Twos_comp (lo,hi) then
   raise ERR "twos_comp_interval" "width is too small"
 else
 if 0 <= lo andalso 0 <= hi then
    num_interval dir width (lo,hi)
 else
 let val top = twoE (width * 8)
 in
   if lo < 0 andalso hi >= 0 then
       (if hi + 1 = top + lo  (* contiguous *) then
           catlist (dots width)
        else
           Or [num_interval dir width (top + lo,top-1),
               num_interval dir width (0,hi)])
   else
   if lo < 0 andalso hi < 0 then
      num_interval dir width (top+lo,top+hi)
   else raise ERR "twos_comp_interval" "unexpected values for lo and hi"
 end

(*---------------------------------------------------------------------------*)
(* Even and odd numbers                                                      *)
(*---------------------------------------------------------------------------*)

val small_evens = filter (fn x => x mod 2 = 0) (upto 0 255);
val small_odds  = filter (fn x => x mod 2 = 1) (upto 0 255);
val sme_charset = Regexp_Type.charset_of (map Char.chr small_evens);
val smo_charset = Regexp_Type.charset_of (map Char.chr small_odds);

fun EVEN LSB = Cat(Chset sme_charset,Star DOT)
  | EVEN MSB = Cat(Star DOT,Chset sme_charset);

fun ODD LSB = Cat(Chset smo_charset,Star DOT)
  | ODD MSB = Cat(Star DOT, Chset smo_charset);

(*---------------------------------------------------------------------------*)
(* Regexp for "zigzag" encoded integer in the interval [lo,hi]               *)
(*---------------------------------------------------------------------------*)

fun pos_zigzag dir (lo,hi) =
 let val w = interval_width Zigzag (lo,hi)
 in And(EVEN dir, num_interval dir w (2*lo, 2*hi))
 end

fun neg_zigzag dir (lo,hi) =
 let val w = interval_width Zigzag (lo,hi)
 in And(ODD dir, num_interval dir w (2*(abs hi)-1, 2*(abs lo)-1))
 end

fun zigzag_interval dir width (lo,hi) =
 if hi < lo then
     raise ERR "zigzag_interval" "hi less than lo"
 else
 if width < interval_width Zigzag (lo,hi) then
   raise ERR "zigzag_interval" "width is too small"
 else
 if 0 <= lo (* all positive *) then
    pos_zigzag dir (lo, hi) else
 if hi < 0 (* all negative *) then
    neg_zigzag dir (lo,hi)
 else (* lo < 0 and 0 <= hi *)
  let val lomag = IntInf.abs lo
  in if lomag < hi then
        let val span = num_interval dir width (0, zigzag lomag) (* [lo,lomag] *)
            val upper = pos_zigzag dir (lomag+1,hi)
        in mk_or [span, upper]
        end
     else
      if hi < lomag then
        let val span = num_interval dir width (0, zigzag hi) (* [-hi,hi] *)
            val lower = neg_zigzag dir (lo,~(hi+1))
        in mk_or [span,lower]
        end
     else (* hi = lomag *)
      num_interval dir width (0, zigzag hi)
  end;

(*---------------------------------------------------------------------------*)
(* Regexp for sign-magnitude encoded integer in the interval [lo,hi]         *)
(*---------------------------------------------------------------------------*)

fun pos_sign_mag dir (lo,hi) =
 let val w = interval_width Sign_mag (lo,hi)
     val base = And(EVEN dir, num_interval dir w (2*lo, 2*hi))
 in if lo = 0 then
       mk_or[num_interval dir w (1,1), base]
    else base
 end

fun neg_sign_mag dir (lo,hi) =
 let val w = interval_width Sign_mag (lo,hi)
 in And(ODD dir, num_interval dir w (2*(abs hi)+1, 2*(abs lo)+1))
 end

fun sign_mag_interval dir width (lo,hi) =
 if hi < lo then
     raise ERR "sign_mag_interval" "hi less than lo"
 else
 if width < interval_width Sign_mag (lo,hi) then
   raise ERR "sign_mag_interval" "width is too small"
 else
 if 0 <= lo (* all positive *) then
    pos_sign_mag dir (lo, hi) else
 if hi < 0 (* all negative *) then
    neg_sign_mag dir (lo,hi)
 else (* lo < 0 and 0 <= hi *)
  let val lomag = IntInf.abs lo
  in if lomag < hi then
        let val span = num_interval dir width (0, sign_mag lo) (* [lo,lomag] *)
            val upper = pos_sign_mag dir (lomag+1,hi)
        in mk_or [span, upper]
        end
     else
      if hi < lomag then
        let val span = num_interval dir width (0, sign_mag (~hi)) (* [-hi,hi] *)
            val lower = neg_sign_mag dir (lo,~(hi+1))
        in mk_or [span,lower]
        end
     else (* hi = lomag *)
      num_interval dir width (0, sign_mag (~hi))
  end;

fun interval_regexp Unsigned  = num_interval
  | interval_regexp Twos_comp = twos_comp_interval
  | interval_regexp Zigzag    = zigzag_interval
  | interval_regexp Sign_mag  = sign_mag_interval;

fun test_interval enc dir w (lo,hi) =
 let val regexp = Regexp_Match.normalize(interval_regexp enc dir w (lo,hi))
     val dfa = Regexp_Match.matcher regexp
     val matcher = #matchfn dfa
     val states = length (#final dfa)
     val _ = print (Int.toString states^" states\n")
     fun testFn i = matcher (iint2string enc dir w i)
     val ivl = bigUpto lo hi
     val _ = if Lib.all I (map testFn ivl) then
              print "all elements of interval matched" else
             raise ERR "test_interval" "number in interval fails match"
 in
   (regexp,states,testFn)
 end;

(*
val (r,n,testFn) = test_interval Unsigned LSB 2 (12, 1234);
val (r,n,testFn) = test_interval Twos_comp LSB 2 (12, 1234);
val (r,n,testFn) = test_interval Zigzag LSB 2 (12, 1234);
val (r,n,testFn) = test_interval Sign_mag LSB 2 (12, 1234);

val (r,n,testFn) = test_interval Twos_comp LSB 2 (~12, 1234);
val (r,n,testFn) = test_interval Zigzag LSB 2 (~12, 1234);
val (r,n,testFn) = test_interval Sign_mag LSB 2 (~12, 1234);

*)

(*---------------------------------------------------------------------------*)
(* Regexp for numbers >= n of arbitrary size                                 *)
(*---------------------------------------------------------------------------*)

(*
fun LEQ enc dir width n =
 if n < 0 then
    raise ERR "LEQ" "negative input"
 else
    interval_regexp enc dir width (0,n);

fun GTR enc dir width n = And(EVEN dir, Neg (LEQ enc dir width n));

*)

end
