open HolKernel Parse boolLib bossLib blastLib;

val _ = set_trace "Unicode" 0
val _ = set_trace "print blast counterexamples" 0
val _ = set_trace "bit blast" 0

val prs = StringCvt.padRight #" "
fun trunc w t = let
  val s = Lib.with_flag (Globals.linewidth, 10000) term_to_string t
in
  if size s >= w then String.extract (s, 0, SOME (w - 5)) ^ " ... "
  else prs w s
end

fun die() = ()
fun die() = OS.Process.exit OS.Process.failure

val _ = print "\n";
val _ = print (prs 65 "Parsing :bool[32] list")
val ty1 = listSyntax.mk_list_type (wordsSyntax.mk_int_word_type 32)
val ty2 = Parse.Type`:bool[32] list` handle HOL_ERR _ => alpha
val _ = if Type.compare(ty1,ty2) = EQUAL then print "OK\n"
        else (print "FAILED!\n"; die())

val _ = print (prs 65 "Parsing :('a + 'b)[32]")
val ty1 = fcpSyntax.mk_cart_type
            (sumSyntax.mk_sum(alpha,beta),
             fcpSyntax.mk_int_numeric_type 32);
val ty2 = Parse.Type`:('a + 'b)[32]`
val _ = if Type.compare(ty1,ty2) = EQUAL then print "OK\n"
        else (print "FAILED\n"; die())

val _ = print (prs 65 "Printing :('a + 'b)[32]")
val _ = if type_to_string ty2 = ":('a + 'b)[32]" then print "OK\n"
        else (print "FAILED\n"; die())

fun test (c:conv) tm = let
  val rt = Timer.startRealTimer ()
  val res = Lib.total c tm
  val elapsed = Timer.checkRealTimer rt
in
  TextIO.print (trunc 65 tm ^ Time.toString elapsed ^
                (case res of
                   NONE => "FAILED!"
                 | _ => "") ^ "\n");
  case res of NONE => die() | _ => ()
end

fun test_fail orig (c:conv) tm = let
  val res = (c tm; SOME "should fail!")
              handle HolSatLib.SAT_cex _ => SOME "unexpected counterexample!"
                   | HOL_ERR {origin_function,...} =>
                       if origin_function = orig then
                         NONE
                       else
                         SOME ("unexpected exception from " ^ origin_function)
in
  TextIO.print ("Expecting failure: " ^ trunc 46 tm ^
                (case res of
                   NONE => "OK"
                 | SOME s => s) ^ "\n");
  case res of SOME _ => die() | _ => ()
end

fun test_counter (c:conv) tm = let
  val res = (c tm; SOME "should fail!")
              handle HolSatLib.SAT_cex thm =>
                       if Lib.can Drule.EQF_ELIM thm then
                         NONE
                       else
                         SOME "invalid counterexample"
                   | HOL_ERR {origin_function,...} =>
                         SOME ("unexpected exception from " ^ origin_function)
in
  TextIO.print ("Counterexample: " ^ trunc 49 tm ^
                (case res of
                   NONE => "OK"
                 | SOME s => s) ^ "\n");
  case res of SOME _ => die() | _ => ()
end

(*
fun test_conv (c:conv) tm = let
  val rt = Timer.startRealTimer ()
  val res = QCONV c tm
  val elapsed = Timer.checkRealTimer rt
in
  TextIO.print (Time.toString elapsed ^ "\n");
  TextIO.print (thm_to_string res ^ "\n")
end
*)

fun time_to_minutes e =
let
  val s = Time.toSeconds e
  val minutes = Int.quot (s, 60);
  val seconds = Int.rem (s, 60);
in
  Int.toString minutes ^ "m " ^
  StringCvt.padLeft #"0" 2 (Int.toString seconds) ^ "s"
end;

val raw_blast_true = test (Drule.EQT_ELIM o blastLib.BIT_BLAST_CONV)
val blast_true = test blastLib.BBLAST_PROVE
val eblast_true = test blastLib.EBLAST_PROVE
val blast_fail = test_fail "BBLAST_PROVE" blastLib.BBLAST_PROVE
val blast_counter = test_counter blastLib.BBLAST_PROVE
val srw_true = test (simpLib.SIMP_PROVE (srw_ss()) [])

(* start tests *)
val _ = print "blastLib tests\n"
val tt = Timer.startRealTimer ()

(* Fail (false) *)
val _ = blast_fail ``?x. x <+ 0w : word8``;
val _ = blast_fail ``?x y. !z. (x + y = 0w : word8) /\ P z``;
val _ = blast_fail ``?x: word8. 3w > 4w : word4``;
val _ = blast_fail ``x + x = x :'a word``;

(* Fail, can't solve *)
val _ = blast_fail ``?x. !y. x <=+ y : word8``;
val _ = blast_fail ``!y. ?x. x <=+ y : word8``;
val _ = blast_fail ``?x. x <=+ y : word8``;
val _ = blast_fail ``(!x:word8 y:word8. word_msb x = word_msb y) ==>
                     (x <+ y = x < y : word8)``

(* Counterexamples *)
val _ = blast_counter ``!x. x <+ 0w : word8``;
val _ = blast_counter ``!x. x >=+ 2w : word8``;
val _ = blast_counter ``!y. x <=+ y : word8``;
val _ = blast_counter ``(x = 1w) \/ (x = 2w : word2)``;
val _ = blast_counter ``x = y : word2``
val _ = blast_counter ``x + x = x : word8``;
val _ = blast_counter ``x <+ y = x < y : word8``
val _ = blast_counter ``(8w * a + b && 7w) >> 3 = a && (-1w >> 3) : word8``;

val _ = blast_true ``!x. x >=+ 2w \/ x <+ 2w : word8``;
val _ = blast_true ``?x. x <+ 2w : word8``;
val _ = eblast_true ``?x. !y:word8. (y <> y + 1w) /\ x <+ 2w : word8``;
val _ = blast_true ``?x y. x + y = 12w : word8``;
val _ = blast_true ``?x. x + x = x : word8``;
val _ = blast_true ``?x y. !z. (x + y = 0w : word8) /\ (z \/ ~z)``;
val _ = blast_true ``?x. x <=+ 0w : word8``;
val _ = blast_true ``!w:word8. ~word_lsb (w << 2)``;
val _ = blast_true ``?w:word8. word_lsb w``;
val _ = blast_true ``?x y z. (x + y <+ z + 1w : word8)``;
val _ = blast_true ``?z y x. (x + y <+ z + 1w : word8)``;
val _ = blast_true ``?z x y. (x + y <+ z + 1w : word8)``;
val _ = blast_true ``?x. x``;
val _ = blast_true ``?x y. x \/ y``;
val _ = blast_true ``?y x. x \/ y``;
val _ = blast_true ``!x y. (word_msb x = word_msb y) ==>
                             (x <+ y = x < y : word8)``
val _ = blast_true ``?x y. (word_msb x = word_msb y) ==>
                             (x <+ y = x < y : word8)``
val _ = blast_true ``!x. x <+ 1w ==> (x + x = x : word8)``;
val _ = blast_true ``?x. x <+ 1w ==> (x + x = x : word8)``;
val _ = blast_true ``?x: word8. 3w < 4w : word4``;
val _ = blast_true ``?x y. x + y = y + x : word8``;
val _ = blast_true ``?x:word8 y:word8. T``;
val _ = blast_true ``?x:word8. !y:word8. T``;
val _ = blast_true ``!x:word8. ?y:word8. T``;
val _ = blast_true ``((w2w a - w2w b) : 33 word ' 32) = (a <+ b : word32)``;

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

val _ = blast_true
  ``if (0w :bool[16]) = (x :bool[16]) && (1024w :bool[16]) then
      ~(if (0w :bool[16]) = x && (1024w :bool[16]) then
          $= (((0 :num) >< (0 :num)) (1w :bool[unit]) :bool[unit])
        else
          $= (((0 :num) >< (0 :num)) (0w :bool[unit]) :bool[unit])) (1w
           :bool[unit]) ==>
      ((1w :bool[unit]) = ~(1w :bool[unit]))
    else
      ~(if (0w :bool[16]) = x && (1024w :bool[16]) then
          $= (((0 :num) >< (0 :num)) (1w :bool[unit]) :bool[unit])
        else
          $= (((0 :num) >< (0 :num)) (0w :bool[unit]) :bool[unit])) (1w
           :bool[unit]) ==>
      ((1w :bool[unit]) = ~(0w :bool[unit]))``;

val _ = blast_true
  ``SND (word_rrx (T,v:word32)) = v >>> 1 !! 0x80000000w``;

val _ = srw_true
  ``0x20000000w !! 0w !! w : word32 = w !! 0x20000000w``;

val _ = srw_true
  ``32w && w && 0w = 0w : word32``;

val _ = blast_true
  ``(a:word2) <+ b /\ b <+ c /\ c <+ d ==> (3w * d = 1w)``

val _ = blast_true
  ``(m:word8) <+ 4w /\ n <+ 4w ==> (((w <<~ m) <<~ n) = w <<~ (m + n))``;

val _ = blast_true
  ``(w #<<~ m) #>>~ n = w #<<~ (m - n) : word8``;

val _ = blast_true
  ``w <+ 10w /\ s <+ 3w ==> w <<~ (s + 1w) <+ 73w : word16``;

val _ = blast_true
  ``w >>>~ v <=+ w : word16``

val _ = blast_true
  ``~word_msb w ==> w >>~ v <= w : word16``;

val _ = blast_true
  ``w2w (a * b : word4) = 0xFw && (w2w a * w2w b) : word8``;

val _ = blast_true
  ``(1w <<~ a) * b = b <<~ a : 6 word``;

val _ = blast_true
  ``a <+ 10w /\ b <+ 10w ==> (a * b <=+ 81w : word8)``;

val _ = blast_true
  ``(a + x + c + d - e + 0w = c + -(g - x)) = (-e = -(g + d + a))``;

val _ = blast_true
  ``a << 2 + b = b + a * 4w``;

val _ = blast_true
  ``(-a * (b + c) + b = -a * b) = (-a * c = -b)``;

val _ = blast_true
  ``(a + 4w = b + 2w) = (a + 2w = b)``;

val _ = blast_true
  ``(a + 4w = b - 2w) = (a + 6w = b)``;

val _ = blast_true
  ``(-a = -b) = (a = b)``;

val _ = blast_true
   ``(a + 4w = b) = (b + 4w = a : word3)``;

val _ = blast_true
   ``(x + b * 4w + c * 4w = q + e * 4w - r : word3) =
     (4w * b + 4w * c + 4w * e + x + r = q)``

val elapsed = Timer.checkRealTimer tt;

val _ = print ("\nTotal time: " ^ time_to_minutes elapsed ^ "\n");

val _ = OS.Process.exit OS.Process.success;
