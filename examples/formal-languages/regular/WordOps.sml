structure WordOps =
struct

val ERR = Feedback.mk_HOL_ERR "WordOps";

val bigUpto = regexpMisc.bigUpto;

type word = IntInf.int;

val allzero = IntInf.fromInt 0;
val allones = IntInf.notb allzero;

val zero = allzero;
val one = IntInf.fromInt 1;
val two = IntInf.fromInt 2;
val two_five_five = IntInf.fromInt 255;
val two_five_six = IntInf.fromInt 256;

(*---------------------------------------------------------------------------*)
(* Clear top (all but rightmost width) bits in w                             *)
(*---------------------------------------------------------------------------*)

fun clear_top_bits width w =
 let open IntInf
     val mask = notb(<<(allones,Word.fromInt width))
 in andb(w,mask)
 end

fun clear_bot_bits width w = IntInf.~>>(w,Word.fromInt width);

fun sign_extend w width =
 if IntInf.~>>(w,Word.fromInt (width - 1)) = 1
    then (* signed *)
      IntInf.orb(w,IntInf.<<(allones,Word.fromInt width))
 else w

fun bin i = IntInf.fmt StringCvt.BIN i;


fun unsigned_width_bits (n:IntInf.int) =
 if n < zero then raise ERR "unsigned_width_bits" "negative number" else
 if n < two then 1
 else 1 + unsigned_width_bits (IntInf.div (n, two));

fun signed_width_bits (n:IntInf.int) =
  let fun fus bits =
       let val N = IntInf.pow(2,bits-1)
       in if ~N <= n andalso n <= N-1 then bits else fus (bits+1)
       end
 in fus 0
 end;

fun unsigned_width_256 (n:IntInf.int) =
 if n < zero then raise ERR "unsigned_width_256" "negative number" else
 if n < two_five_six then 1
 else 1 + unsigned_width_256 (IntInf.div(n, two_five_six));

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

(*---------------------------------------------------------------------------*)
(* bytes_of i w lays out i into w bytes                                      *)
(*---------------------------------------------------------------------------*)

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
fun msb_signed i   = rev (lsb_signed i);
fun lsb_unsigned i = bytes_of i (unsigned_width_256 i);
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

val byte2char = Char.chr o Word8.toInt;
val char2byte = Word8.fromInt o Char.ord;

val string2num = lsb_num_of o map char2byte o String.explode;
val string2int = lsb_int_of o map char2byte o String.explode;

val msb_string2num = msb_num_of o map char2byte o String.explode;
val msb_string2int = msb_int_of o map char2byte o String.explode;

(*
fun hex2byte c = Option.valOf (Word8.fromString (Char.toString c));
val hexstring2num = lsb_num_of o map hex2byte o String.explode;
val hexstring2int = lsb_int_of o map hex2byte o String.explode;

val msb_hexstring2num = msb_num_of o map hex2byte o String.explode;
val msb_hexstring2int = msb_int_of o map hex2byte o String.explode;
*)

(*---------------------------------------------------------------------------*)
(* Puts int out in LSB                                                       *)
(*---------------------------------------------------------------------------*)

fun int2string w n =
 let val blist = bytes_of (IntInf.fromInt n) w
 in String.implode (map byte2char blist)
 end;

fun int2string_msb w n =
 let val blist = bytes_of (IntInf.fromInt n) w
 in String.implode (map byte2char (rev blist))
 end;

datatype layout = LSB | MSB;

fun stringN LSB s = string2num s
  | stringN MSB s = msb_string2num s

fun stringZ LSB s = string2int s
  | stringZ MSB s = msb_string2int s

fun NZstring LSB w n = int2string w n
  | NZstring MSB w n = int2string_msb w n

end
