open HolKernel Parse boolLib bossLib blastLib;

val _ = set_trace "Unicode" 0

fun trunc w t = let
  val s = Lib.with_flag (Globals.linewidth, 10000) term_to_string t
in
  if size s >= w then String.extract (s, 0, SOME (w - 5)) ^ " ... "
  else StringCvt.padRight #" " w s
end

fun die() = OS.Process.exit OS.Process.failure
fun test c tm = let
  val rt = Timer.startRealTimer ()
  val res = SOME (c tm) handle HOL_ERR _ => NONE
  val elapsed = Timer.checkRealTimer rt
  val res' = SOME (Option.map Drule.EQT_ELIM res)
             handle HOL_ERR _ => NONE
in
  TextIO.print (trunc 65 tm ^ Time.toString elapsed ^
                (case res' of
                   NONE => "FAILED!"
                 | SOME NONE => "FAILED!"
                 | _ => "") ^ "\n");
  case res' of NONE => die() | SOME NONE => die() | _ => ()
end

val raw_blast_true = test blastLib.BIT_BLAST_CONV
val blast_true = test blastLib.BBLAST_CONV

(* start tests *)

val _ = raw_blast_true
  ``(a + b - b : word8) = a``;

val _ = raw_blast_true
  ``(a + b + c : word8) = (c + b + a)``;

val _ = blast_true
  ``(v ?? w = 0w:word8) = (v = w)``;

val _ = blast_true
  ``(1 >< 0) (w2w (x:word30) << 2 + w:word32) : word2 = (1 >< 0) w``;

val _ = blast_true
  ``(1 >< 0) ((w2w (x:word30) << 2) : word32) = 0w :word2``;

val _ = blast_true
  ``(x && 3w = 0w:word32) ==> ((x + 4w * y) && 3w = 0w)``;

val _ = blast_true
  ``(31 >< 2) (w2w (x:word30) << 2 + y:word32) = x + (31 >< 2) y``;

val _ = blast_true
  ``(31 >< 2) (w2w (a:word30) << 2 + 0w:word32) = a``;

val _ = blast_true
  ``(31 >< 2) (w2w (a:word30) << 2 + 1w:word32) = a``;

val _ = blast_true
  ``(31 >< 2) (w2w (a:word30) << 2 + 2w:word32) = a``;

val _ = blast_true
  ``(31 >< 2) (w2w (a:word30) << 2 + 3w:word32) = a``;

val _ = blast_true
  ``(x && 3w = 0w:word32) ==> (w2w ((31 >< 2) x : word30) << 2 = x)``;

val _ = blast_true
  ``w2w (v + w:word30) << 2 = (w2w v << 2 + w2w w << 2) : word32``;

val _ = blast_true
  ``w2w (-w : word30) << 2 = -(w2w w << 2) : word32``;

val _ = blast_true
  ``w2w (v - w:word30) << 2 = (w2w v << 2 - w2w w << 2) : word32``;

val _ = blast_true
  ``w2w (p + 1w:word30) << 2 = w2w p << 2 + 4w:word32``;

val _ = blast_true
  ``(w2w a << 2 = 0w:word32) = (a = 0w:word30)``;

val _ = blast_true
  ``(w2w (a:word30) << 2 && 1w = 0w:word32)``;

val _ = blast_true
  ``(w2w (a:word30) << 2 && 2w = 0w:word32)``;

val _ = blast_true
  ``(w2w (a:word30) << 2 && 3w = 0w:word32)``;

val _ = blast_true
  ``(w2w (a:word30) << 2 = (w2w b << 2):word32) = (a = b)``;

val _ = blast_true
  ``(w2w (a:word30) << 2 + 1w : word32 = w2w b << 2 + 1w) = (a = b)``;

val _ = blast_true
  ``(w2w (a:word30) << 2 + 2w : word32 = w2w b << 2 + 2w) = (a = b)``;

val _ = blast_true
  ``(w2w (a:word30) << 2 + 3w : word32 = w2w b << 2 + 3w) = (a = b)``;

val _ = blast_true
  ``~(w2w (a:word30) << 2 + 1w : word32 = w2w (b:word30) << 2 + 2w)``;

val _ = blast_true
  ``~(w2w (a:word30) << 2 + 1w : word32 = w2w (b:word30) << 2 + 3w)``;

val _ = blast_true
  ``~(w2w (a:word30) << 2 + 2w : word32 = w2w (b:word30) << 2 + 3w)``;

val _ = blast_true
  ``(w2w (x:word30) << 2) + 4w:word32 = w2w (x + 1w) << 2``;

val _ = blast_true
  ``(w2w (x:word30) << 2) + 8w:word32 = w2w (x + 2w) << 2``;

val _ = blast_true
  ``(w2w (x:word30) << 2) + 40w:word32 = w2w (x + 10w) << 2``;

val _ = blast_true
  ``(w2w (x:word30) << 2) - 4w:word32 = w2w (x - 1w) << 2``;

val _ = blast_true
  ``(w2w (x:word30) << 2) - 8w:word32 = w2w (x - 2w) << 2``;

val _ = blast_true
  ``(w2w (x:word30) << 2) - 40w:word32 = w2w (x - 10w) << 2``;

val _ = blast_true
  ``(-x && 3w = 0w:word32) = (x && 3w = 0w)``;

val _ = blast_true
  ``(x && 3w = 0w) ==> (x && 1w = 0w:word32)``;

val _ = blast_true
  ``(x && 3w = 0w) ==> ~(x + 1w && 1w = 0w:word32)``;

val _ = blast_true
  ``(x && 3w = 0w) ==> (x + 1w && 3w = 1w:word32)``;

val _ = blast_true
  ``(x && 3w = 0w) ==> (x + 2w && 3w = 2w:word32)``;

val _ = blast_true
  ``(x && 3w = 0w) ==> (x + 3w && 3w = 3w:word32)``;

val _ = blast_true
  ``(x && 3w = 0w) /\ (y && 3w = 0w) ==> ((x + y) && 3w = 0w:word32)``;

val _ = blast_true
  ``(x && 3w = 0w) /\ (y && 3w = 0w) ==> ((x - y) && 3w = 0w:word32)``;

val _ = blast_true
  ``((a + 4w * x) && 3w = 0w:word32) = (a && 3w = 0w)``;

val _ = blast_true
  ``((4w * x + a) && 3w = 0w:word32) = (a && 3w = 0w)``;

val _ = blast_true
  ``((a + x * 4w) && 3w = 0w:word32) = (a && 3w = 0w)``;

val _ = blast_true
  ``((x * 4w + a) && 3w = 0w:word32) = (a && 3w = 0w)``;

val _ = blast_true
  ``((a + 4w) && 3w = 0w:word32) = (a && 3w = 0w)``;

val _ = blast_true
  ``((4w + a) && 3w = 0w:word32) = (a && 3w = 0w)``;

val _ = blast_true
  ``(a && 3w = 0w:word32) ==> ~((a + 1w) && 3w = 0w)``;

val _ = blast_true
  ``(a && 3w = 0w:word32) ==> ~((a + 2w) && 3w = 0w)``;

val _ = blast_true
  ``(a && 3w = 0w:word32) ==> ~((a + 3w) && 3w = 0w)``;

val _ = blast_true
  ``(x && 3w = 0w:word32) = ~(x ' 0) /\ ~(x ' 1)``;

val _ = blast_true
  ``((x !! y) && 3w = 0w:word32) = (x && 3w = 0w) /\ (y && 3w = 0w)``;

val _ = blast_true
  ``(w2w (x:word30) << 2) :word32 <=+ (w2w (y:word30) << 2) = x <=+ y``;

val _ = blast_true
  ``(w2w (x:word30) << 2) :word32 <+ (w2w (y:word30) << 2) = x <+ y``;

val _ = blast_true
  ``((x:word32) && 3w = 0w) /\ ~(x + 4w = 0w) ==> x <+ x + 4w``;

val _ = blast_true
  ``((x:word32) && 3w = 0w) ==>
    (((x + y) && 3w = 0w) = ((y:word32) && 3w = 0w))``;

val _ = blast_true
  ``((x:word32) && 3w = 0w) ==>
    (((x - y) && 3w = 0w) = ((y:word32) && 3w = 0w))``;

val _ = blast_true
  ``((x:word32) && 3w = 0w) ==>
    (((y - x) && 3w = 0w) = ((y:word32) && 3w = 0w))``;

val _ = blast_true
  ``((x:word32) && 3w = 0w) ==>
    (((y + x) && 3w = 0w) = ((y:word32) && 3w = 0w))``;

val _ = blast_true
  ``((x - 4w:word32) && 3w = 0w) = ((x:word32) && 3w = 0w)``;

val _ = blast_true
  ``((x - 4w * a:word32) && 3w = 0w) = ((x:word32) && 3w = 0w)``;

val _ = blast_true
  ``((66 >< 0) :bool[67] -> bool[128])
    ((((0 >< 0) :bool[unit] -> bool[67])
     ~(((65 >< 65) :bool[66] -> bool[unit]) w)) << 65 +
      (((64 >< 0) :bool[66] -> bool[67]) w) + 0x40000000000000000w) =
      (((0 >< 0) :bool[unit] -> bool[128])
      ~(((65 >< 65) :bool[66] -> bool[unit]) w)) << 65 +
      (((64 >< 0) :bool[66] -> bool[128]) w) + 0x40000000000000000w``;

val _ = blast_true
  ``!w. (sw2sw :bool[32] -> bool[64]) w =
      ((w2w :bool[32] -> bool[64])
        ((w2w :bool[16] -> bool[32])
          (((15 >< 0) :bool[32] -> bool[16]) w))) +
      ((sw2sw :bool[16] -> bool[64])
        ((w2w :bool[32] -> bool[16]) (w >>> 16))) << 16``

val _ = blast_true
  ``!(w: 18 word).
       (sw2sw w): 32 word =
       w2w ((16 >< 0) w: 17 word) + 0xfffe0000w +
       ((0 >< 0) (~(17 >< 17) w:bool [unit]) << 17):32 word``;

val _ = blast_true
  ``!w:word32. ~word_lsb (w << 2)``;

val _ = blast_true
  ``!w:word32. ~word_msb (w >>> 2)``;

val _ = blast_true
  ``!w:word32. word_lsb (w >> 2 #<< 2) = word_msb w``;

val _ = blast_true
  ``!w:word32. w ' 3 ==> (word_bit 4 ((3 --- 1) w))``;

val _ = blast_true
  ``!w:word16. word_reverse (word_reverse w) = w``;

val _ = blast_true
  ``!a b:word8. word_reverse a !! word_reverse b = word_reverse (a !! b)``;

val _ = blast_true
  ``(4 >< 1) (bit_field_insert 4 1 (a:word4) (b:word32) + w2w (-a) << 1) =
    0w:word4``;

val _ = blast_true
  ``!a b:word8.
     ~(a ' 3) /\ ~(b ' 3) ==>
     (((7 >< 4) a + ((7 >< 4) b) : word4) @@ (w2w b + w2w a :word4) = a + b)``;

val _ = blast_true
  ``~a ' 7 ==>
     ((31 >< 24)
      (word_replicate 4 (a:word8) + word_replicate 4 (a:word8) :word32) =
      2w * a)``;

val _ = blast_true
  ``!a:word8. a <+ 4w ==> a <+ 8w``;

val _ = blast_true
  ``!a:word8. a <+ 4w ==> (a + a) <+ 8w``;

val _ = blast_true
  ``!a:word8. a <+ 4w /\ b <+ a /\ c <=+ 5w ==> (b + c) <=+ 7w``;

val _ = blast_true
  ``w ' 3 ==> (reduce_or (w:word8) <> 0w)``;

val _ = blast_true
  ``(reduce_or (w:word8) && reduce_or (v:word8)) =
    ~(reduce_and (~w) !! reduce_and (~v))``;

val _ = blast_true
  ``(0w:word32 = 0xFFFFFFFFw * sw2sw (x :word8)) ==>
    ~(x ' 1 <=> ~(x ' 0))``;

val _ = OS.Process.exit OS.Process.success;
