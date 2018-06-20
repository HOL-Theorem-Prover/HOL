structure Interval =
struct

open WordOps;

(*---------------------------------------------------------------------------*)
(* Numeric intervals are introduced with \i{lo,hi}                           *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Given A = [a1, ..., ak] and B = [b1, ..., bn], interval_cat A width B     *)
(* yields                                                                    *)
(*                                                                           *)
(*  [a1.b1, ..., a1.bn, ... , ak.b1, ..., ak.bn]                             *)
(*                                                                           *)
(* where the b1...bn occupy width bits and int_cat i1 width i2 returns a     *)
(* number which is the digits of i1 followed by those of i2.                 *)
(*---------------------------------------------------------------------------*)

fun int_cat w shift i =
 let val shiftw = Word.fromInt shift
     val shifted = IntInf.<<(w,shiftw)
     val x = clear_top_bits shift i
 in
   IntInf.orb(shifted,x)
 end

fun interval_cat A width [] = A
  | interval_cat [] width B = List.map (int_cat zero width) B
  | interval_cat A width B =
      List.concat (List.map (fn a => List.map (int_cat a width) B) A);

fun interval_list_cat W list =
 case list
  of [] => W
   | ((lo,hi),width)::t =>
      interval_list_cat (interval_cat W width (bigUpto lo hi)) t;


(*---------------------------------------------------------------------------*)
(* Numeric intervals                                                         *)
(*---------------------------------------------------------------------------*)

fun intervals list =
 let open IntInf
     val slist = Listsort.sort IntInf.compare list
     val one = IntInf.fromInt 1
     fun follows j i = j = i + one
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

(*---------------------------------------------------------------------------*)
(* Width of an interval (in bytes and bits)                                  *)
(*---------------------------------------------------------------------------*)

fun interval_byte_width (lo,hi) =
 if lo > hi
     then raise ERR "interval_byte_width" "trivial interval"
 else
 if lo < 0 andalso hi < 0 then
    signed_width_256 lo else
 if lo < 0 andalso hi >= 0 then
    Int.max(signed_width_256 lo, signed_width_256 hi)
 else unsigned_width_256 hi;

fun interval_bit_width (lo,hi) =
 if lo > hi
     then raise ERR "interval_bit_width" "trivial interval"
 else
 if lo < 0 andalso hi < 0 then
    signed_width_bits lo else
  if lo < 0 andalso hi >= 0 then
    Int.max(signed_width_bits lo, signed_width_bits hi)
  else  (* lo and hi both non-negative *)
  unsigned_width_bits hi;


end
