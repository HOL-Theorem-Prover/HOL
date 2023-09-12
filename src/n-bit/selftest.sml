open HolKernel Parse boolLib bossLib;
open blastLib testutils

(*
  fun die s = (print (s ^ "\n"); raise ERR "" "")
*)

val _ = set_trace "Unicode" 0
val _ = set_trace "print blast counterexamples" 0
val _ = set_trace "bit blast" 0

val ERR = mk_HOL_ERR "selftest"

fun parse_n_eval s expected =
    let
      fun checkconv th =
          aconv (rhs (concl th)) expected handle HOL_ERR _ => false
      fun kont (Exn.Res t) =
          (tprint "EVAL result of parse";
           require_msg (check_result checkconv) thm_to_string
                                         EVAL
                                         t)
        | kont _ = raise Fail "Can't happen"
      val _ = tprint ("Parse \"" ^ s ^ "\"")
    in
      require_msgk is_result (K (HOLPP.add_string ""))
                   (fn s => Parse.Term [QUOTE s]) kont s
    end

val _ = parse_n_eval "~2w : word4" “13w : word4”
val _ = parse_n_eval "¬2w : word4" “13w : word4”
val _ = parse_n_eval "(2w : word4) + 11w" “13w : word4”
val _ = parse_n_eval "LOG 2 x" “LOG 2 x”
val _ = parse_n_eval "LOG 2 1023" “9n”

val prs = StringCvt.padRight #" "
fun trunc w t = let
  val s = Lib.with_flag (Globals.linewidth, 10000) term_to_string t
in
  if size s >= w then String.extract (s, 0, SOME (w - 5)) ^ " ... "
  else prs w s
end

val _ = tprint "Parsing :bool[32] list"
val ty1 = listSyntax.mk_list_type (wordsSyntax.mk_int_word_type 32)
val ty2 = Parse.Type`:bool[32] list` handle HOL_ERR _ => alpha
val _ = if Type.compare(ty1,ty2) = EQUAL then OK()
        else die "FAILED!"

val _ = tprint "Parsing :('a + 'b)[32]"
val ty1 = fcpSyntax.mk_cart_type
            (sumSyntax.mk_sum(alpha,beta),
             fcpSyntax.mk_int_numeric_type 32);
val ty2 = Parse.Type`:('a + 'b)[32]`
val _ = if Type.compare(ty1,ty2) = EQUAL then OK()
        else die "FAILED"

val _ = tprint "Printing :('a + 'b)[32]"
val _ = if type_to_string ty2 = ":('a + 'b)[32]" then OK()
        else die "FAILED"

val _ = tprint "Parsing abbreviated word types"
val u8 = fcpSyntax.mk_cart_type(bool, fcpSyntax.mk_int_numeric_type 8)
val _ = type_abbrev_pp("u8", u8)
val _ = if Type.compare(Parse.Type`:u8`, u8) <> EQUAL then die "FAILED!"
        else OK()
val _ = tprint "Printing abbreviated word types"
val _ = if type_to_string u8 = ":u8" then OK() else die "FAILED!"

val _ = tprint "Parsing Datatype with bool-array type"
val _ = require is_result (quietly Datatype) `mytype = mytype_con (bool[3])`;

fun test (c:conv) tm =
    (tprint (trunc 65 tm); testutils.require testutils.is_result c tm)

fun test_fail orig (c:conv) tm =
    let
      open testutils
      fun printarg t = "Expecting failure: " ^ trunc 46 tm
    in
      shouldfail {checkexn = check_HOL_ERRexn (fn (_, f, _) => f = orig),
                  printarg = printarg,
                  printresult = thm_to_string,
                  testfn = c}
                 tm
    end

fun test_counter (c:conv) tm = let
  val res = (c tm; SOME "should fail!")
              handle HolSatLib.SAT_cex thm =>
                       if Lib.can Drule.EQF_ELIM thm then
                         NONE
                       else
                         SOME "bad counterexample"
                   | HOL_ERR {origin_function,...} =>
                         SOME ("unexpected exception from " ^ origin_function)
in
  tprint ("Counterexample: " ^ trunc 49 tm);
  case res of
      NONE => OK()
    | SOME s => die s
end

local
  exception InternalDie of string
  fun idie s = raise InternalDie s
  fun test_conv nm (conv: conv) tm =
    let
      val (t, expected) = boolSyntax.dest_eq tm
    in
      testutils.convtest (nm ^ ": " ^ term_to_string tm, conv, t, expected)
    end
  fun getlocpragma s =
      let
        open Substring
        val ss = full s
        val sr = dropl (not o Char.isDigit) ss
        val sc = dropl Char.isDigit sr
      in
        (valOf (Int.fromString (string sr)), valOf (Int.fromString (string sc)))
      end
  fun mkpragma (r,c) = "(*#loc " ^ Int.toString r ^ " " ^ Int.toString c ^ "*)"
  fun quote_to_term_list q =
   let
     val s = case q of [QUOTE s] => s | _ => raise ERR "quote_to_term_list" ""
     val lines = String.tokens (Lib.equal #"\n") s
     val (r, _) = getlocpragma s
     fun foldthis (s, (r,ts)) =
         if CharVector.all Char.isSpace s then (r+1, ts)
         else (r+1, Parse.Term [QUOTE (mkpragma(r,1) ^ s)] :: ts)
   in
     #2 (List.foldl foldthis (r,[]) lines) |> List.rev
   end
in
  fun qtest_conv nm conv q = List.app (test_conv nm conv) (quote_to_term_list q)
end

val c = SIMP_CONV (srw_ss() ++ wordsLib.WORD_CANCEL_ss) []
val _ = qtest_conv "simp+WORD_CANCEL" c
  ‘(x + y + f z:'a word = a + b + y) <=> (x + f z = a + b)
   (x + -1w * y = e) <=> (e + y = x)
   (a + b + c + d:'a word = x + b + y + d + e) <=> (e + x + y = a + c)
   ((rm:word32) << 2 = 4294967288w) <=> (rm << 2 + 8w = 0w)
   (a + 4w:word32 = b + -2w) <=> (a + 6w = b)
  ’

val _ = let
  val _ = tprint "Word factorial termination with good simp"
  val fact_defn =
      trace ("auto Defn.tgoal", 0) $ trace ("Theory.allow_rebinds", 1) $
      quietly $
          TotalDefn.qDefine "wfact"
             ‘wfact w = if w = 0w then 1 else w2n w * wfact (w - 1w)’
in
  require_msg (check_result (K true)) thm_to_string fact_defn NONE;
  TotalDefn.temp_exclude_termsimp "words.WORD_PRED_THM";
  shouldfail {checkexn = is_struct_HOL_ERR "TotalDefn",
              printarg = K "Word factorial fails after exclusion",
              printresult = thm_to_string,
              testfn = fact_defn} NONE
end;

val blast_true = test blastLib.BBLAST_PROVE
val blast_fail = test_fail "BBLAST_PROVE" blastLib.BBLAST_PROVE
val blast_counter = test_counter blastLib.BBLAST_PROVE
val srw_true = test (simpLib.SIMP_PROVE (srw_ss()) [])

(* start tests *)
val _ = print "\nblastLib tests\n\n"
val tt = Timer.startRealTimer ()

(* Fail (false) *)
val _ = blast_fail ``?x. x <+ 0w : word8``
val _ = blast_fail ``?x y. !z. (x + y = 0w : word8) /\ P z``
val _ = blast_fail ``?x: word8. 3w > 4w : word4``
val _ = blast_fail ``x + x = x :'a word``

(* Fail, can't solve *)
val _ = ParseExtras.temp_loose_equality()
val _ = blast_fail ``?x. !y. x <=+ y : word8``
val _ = blast_fail ``!y. ?x. x <=+ y : word8``
val _ = blast_fail ``?x. x <=+ y : word8``
val _ = blast_fail ``(!x:word8 y:word8. word_msb x = word_msb y) ==>
                     (x <+ y = x < y : word8)``

(* Counterexamples *)
val _ = blast_counter ``!x. x <+ 0w : word8``
val _ = blast_counter ``!x. x >=+ 2w : word8``
val _ = blast_counter ``!y. x <=+ y : word8``
val _ = blast_counter ``(x = 1w) \/ (x = 2w : word2)``
val _ = blast_counter ``x = y : word2``
val _ = blast_counter ``x + x = x : word8``
val _ = blast_counter ``x <+ y = x < y : word8``
val _ = blast_counter ``(8w * a + b && 7w) >> 3 = a && (-1w >> 3) : word8``

val _ = blast_true ``!x. x >=+ 2w \/ x <+ 2w : word8``
val _ = blast_true ``?x. x <+ 2w : word8``
val _ = blast_true ``?x. !y:word8. (y <> y + 1w) /\ x <+ 2w : word8``
val _ = blast_true ``?x y. x + y = 12w : word8``
val _ = blast_true ``?x. x + x = x : word8``
val _ = blast_true ``?x y. !z. (x + y = 0w : word8) /\ (z \/ ~z)``
val _ = blast_true ``?x. x <=+ 0w : word8``
val _ = blast_true ``!w:word8. ~word_lsb (w << 2)``
val _ = blast_true ``?w:word8. word_lsb w``
val _ = blast_true ``?x y z. (x + y <+ z + 1w : word8)``
val _ = blast_true ``?z y x. (x + y <+ z + 1w : word8)``
val _ = blast_true ``?z x y. (x + y <+ z + 1w : word8)``
val _ = blast_true ``?x. x``
val _ = blast_true ``?x y. x \/ y``
val _ = blast_true ``?y x. x \/ y``
val _ = blast_true ``!x y. (word_msb x = word_msb y) ==>
                             (x <+ y = x < y : word8)``
val _ = blast_true ``?x y. (word_msb x = word_msb y) ==>
                             (x <+ y = x < y : word8)``
val _ = blast_true ``!x. x <+ 1w ==> (x + x = x : word8)``
val _ = blast_true ``?x. x <+ 1w ==> (x + x = x : word8)``
val _ = blast_true ``?x: word8. 3w < 4w : word4``
val _ = blast_true ``?x y. x + y = y + x : word8``
val _ = blast_true ``?x:word8 y:word8. T``
val _ = blast_true ``?x:word8. !y:word8. T``
val _ = blast_true ``!x:word8. ?y:word8. T``
val _ = blast_true ``((w2w a - w2w b) : 33 word ' 32) = (a <+ b : word32)``

val _ = blast_true
  ``(v ?? w = 0w:word8) = (v = w)``

val _ = blast_true
  ``(1 >< 0) (w2w (x:word30) << 2 + w:word32) : word2 = (1 >< 0) w``

val _ = blast_true
  ``(1 >< 0) ((w2w (x:word30) << 2) : word32) = 0w :word2``

val _ = blast_true
  ``(x && 3w = 0w:word32) ==> ((x + 4w * y) && 3w = 0w)``

val _ = blast_true
  ``(31 >< 2) (w2w (x:word30) << 2 + y:word32) = x + (31 >< 2) y``

val _ = blast_true
  ``(31 >< 2) (w2w (a:word30) << 2 + 0w:word32) = a``

val _ = blast_true
  ``(31 >< 2) (w2w (a:word30) << 2 + 1w:word32) = a``

val _ = blast_true
  ``(31 >< 2) (w2w (a:word30) << 2 + 2w:word32) = a``

val _ = blast_true
  ``(31 >< 2) (w2w (a:word30) << 2 + 3w:word32) = a``

val _ = blast_true
  ``(x && 3w = 0w:word32) ==> (w2w ((31 >< 2) x : word30) << 2 = x)``

val _ = blast_true
  ``w2w (v + w:word30) << 2 = (w2w v << 2 + w2w w << 2) : word32``

val _ = blast_true
  ``w2w (-w : word30) << 2 = -(w2w w << 2) : word32``

val _ = blast_true
  ``w2w (v - w:word30) << 2 = (w2w v << 2 - w2w w << 2) : word32``

val _ = blast_true
  ``w2w (p + 1w:word30) << 2 = w2w p << 2 + 4w:word32``

val _ = blast_true
  ``(w2w a << 2 = 0w:word32) = (a = 0w:word30)``

val _ = blast_true
  ``(w2w (a:word30) << 2 && 1w = 0w:word32)``

val _ = blast_true
  ``(w2w (a:word30) << 2 && 2w = 0w:word32)``

val _ = blast_true
  ``(w2w (a:word30) << 2 && 3w = 0w:word32)``

val _ = blast_true
  ``(w2w (a:word30) << 2 = (w2w b << 2):word32) = (a = b)``

val _ = blast_true
  ``(w2w (a:word30) << 2 + 1w : word32 = w2w b << 2 + 1w) = (a = b)``

val _ = blast_true
  ``(w2w (a:word30) << 2 + 2w : word32 = w2w b << 2 + 2w) = (a = b)``

val _ = blast_true
  ``(w2w (a:word30) << 2 + 3w : word32 = w2w b << 2 + 3w) = (a = b)``

val _ = blast_true
  ``~(w2w (a:word30) << 2 + 1w : word32 = w2w (b:word30) << 2 + 2w)``

val _ = blast_true
  ``~(w2w (a:word30) << 2 + 1w : word32 = w2w (b:word30) << 2 + 3w)``

val _ = blast_true
  ``~(w2w (a:word30) << 2 + 2w : word32 = w2w (b:word30) << 2 + 3w)``

val _ = blast_true
  ``(w2w (x:word30) << 2) + 4w:word32 = w2w (x + 1w) << 2``

val _ = blast_true
  ``(w2w (x:word30) << 2) + 8w:word32 = w2w (x + 2w) << 2``

val _ = blast_true
  ``(w2w (x:word30) << 2) + 40w:word32 = w2w (x + 10w) << 2``

val _ = blast_true
  ``(w2w (x:word30) << 2) - 4w:word32 = w2w (x - 1w) << 2``

val _ = blast_true
  ``(w2w (x:word30) << 2) - 8w:word32 = w2w (x - 2w) << 2``

val _ = blast_true
  ``(w2w (x:word30) << 2) - 40w:word32 = w2w (x - 10w) << 2``

val _ = blast_true
  ``(-x && 3w = 0w:word32) = (x && 3w = 0w)``

val _ = blast_true
  ``(x && 3w = 0w) ==> (x && 1w = 0w:word32)``

val _ = blast_true
  ``(x && 3w = 0w) ==> ~(x + 1w && 1w = 0w:word32)``

val _ = blast_true
  ``(x && 3w = 0w) ==> (x + 1w && 3w = 1w:word32)``

val _ = blast_true
  ``(x && 3w = 0w) ==> (x + 2w && 3w = 2w:word32)``

val _ = blast_true
  ``(x && 3w = 0w) ==> (x + 3w && 3w = 3w:word32)``

val _ = blast_true
  ``(x && 3w = 0w) /\ (y && 3w = 0w) ==> ((x + y) && 3w = 0w:word32)``

val _ = blast_true
  ``(x && 3w = 0w) /\ (y && 3w = 0w) ==> ((x - y) && 3w = 0w:word32)``

val _ = blast_true
  ``((a + 4w * x) && 3w = 0w:word32) = (a && 3w = 0w)``

val _ = blast_true
  ``((4w * x + a) && 3w = 0w:word32) = (a && 3w = 0w)``

val _ = blast_true
  ``((a + x * 4w) && 3w = 0w:word32) = (a && 3w = 0w)``

val _ = blast_true
  ``((x * 4w + a) && 3w = 0w:word32) = (a && 3w = 0w)``

val _ = blast_true
  ``((a + 4w) && 3w = 0w:word32) = (a && 3w = 0w)``

val _ = blast_true
  ``((4w + a) && 3w = 0w:word32) = (a && 3w = 0w)``

val _ = blast_true
  ``(a && 3w = 0w:word32) ==> ~((a + 1w) && 3w = 0w)``

val _ = blast_true
  ``(a && 3w = 0w:word32) ==> ~((a + 2w) && 3w = 0w)``

val _ = blast_true
  ``(a && 3w = 0w:word32) ==> ~((a + 3w) && 3w = 0w)``

val _ = blast_true
  ``(x && 3w = 0w:word32) = ~(x ' 0) /\ ~(x ' 1)``

val _ = blast_true
  ``((x || y) && 3w = 0w:word32) = (x && 3w = 0w) /\ (y && 3w = 0w)``

val _ = blast_true
  ``(w2w (x:word30) << 2) :word32 <=+ (w2w (y:word30) << 2) = x <=+ y``

val _ = blast_true
  ``(w2w (x:word30) << 2) :word32 <+ (w2w (y:word30) << 2) = x <+ y``

val _ = blast_true
  ``((x:word32) && 3w = 0w) /\ ~(x + 4w = 0w) ==> x <+ x + 4w``

val _ = blast_true
  ``((x:word32) && 3w = 0w) ==>
    (((x + y) && 3w = 0w) = ((y:word32) && 3w = 0w))``

val _ = blast_true
  ``((x:word32) && 3w = 0w) ==>
    (((x - y) && 3w = 0w) = ((y:word32) && 3w = 0w))``

val _ = blast_true
  ``((x:word32) && 3w = 0w) ==>
    (((y - x) && 3w = 0w) = ((y:word32) && 3w = 0w))``

val _ = blast_true
  ``((x:word32) && 3w = 0w) ==>
    (((y + x) && 3w = 0w) = ((y:word32) && 3w = 0w))``

val _ = blast_true
  ``((x - 4w:word32) && 3w = 0w) = ((x:word32) && 3w = 0w)``

val _ = blast_true
  ``((x - 4w * a:word32) && 3w = 0w) = ((x:word32) && 3w = 0w)``

val _ = blast_true
  ``((66 >< 0) :bool[67] -> bool[128])
    ((((0 >< 0) :bool[unit] -> bool[67])
     ~(((65 >< 65) :bool[66] -> bool[unit]) w)) << 65 +
      (((64 >< 0) :bool[66] -> bool[67]) w) + 0x40000000000000000w) =
      (((0 >< 0) :bool[unit] -> bool[128])
      ~(((65 >< 65) :bool[66] -> bool[unit]) w)) << 65 +
      (((64 >< 0) :bool[66] -> bool[128]) w) + 0x40000000000000000w``

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
       ((0 >< 0) (~(17 >< 17) w:bool [unit]) << 17):32 word``

val _ = blast_true
  ``!w:word32. ~word_lsb (w << 2)``

val _ = blast_true
  ``!w:word32. ~word_msb (w >>> 2)``

val _ = blast_true
  ``!w:word32. word_lsb (w >> 2 #<< 2) = word_msb w``

val _ = blast_true
  ``!w:word32. w ' 3 ==> (word_bit 4 ((3 --- 1) w))``

val _ = blast_true
  ``!w:word16. word_reverse (word_reverse w) = w``

val _ = blast_true
  ``!a b:word8. word_reverse a || word_reverse b = word_reverse (a || b)``

val _ = blast_true
  ``(4 >< 1) (bit_field_insert 4 1 (a:word4) (b:word32) + w2w (-a) << 1) =
    0w:word4``

val _ = blast_true
  ``!a b:word8.
     ~(a ' 3) /\ ~(b ' 3) ==>
     (((7 >< 4) a + ((7 >< 4) b) : word4) @@ (w2w b + w2w a :word4) = a + b)``

val _ = blast_true
  ``~a ' 7 ==>
     ((31 >< 24)
      (word_replicate 4 (a:word8) + word_replicate 4 (a:word8) :word32) =
      2w * a)``

val _ = blast_true
  ``!a:word8. a <+ 4w ==> a <+ 8w``

val _ = blast_true
  ``!a:word8. a <+ 4w ==> (a + a) <+ 8w``

val _ = blast_true
  ``!a:word8. a <+ 4w /\ b <+ a /\ c <=+ 5w ==> (b + c) <=+ 7w``

val _ = blast_true
  ``w ' 3 ==> (reduce_or (w:word8) <> 0w)``

val _ = blast_true
  ``(reduce_or (w:word8) && reduce_or (v:word8)) =
    ~(reduce_and (~w) || reduce_and (~v))``

val _ = blast_true
  ``(0w:word32 = 0xFFFFFFFFw * sw2sw (x :word8)) ==>
    ~(x ' 1 <=> ~(x ' 0))``

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
      ((1w :bool[unit]) = ~(0w :bool[unit]))``

val _ = blast_true
  ``SND (word_rrx (T,v:word32)) = v >>> 1 || 0x80000000w``

val _ = blast_true
  ``(a:word2) <+ b /\ b <+ c /\ c <+ d ==> (3w * d = 1w)``

val _ = blast_true
  ``(m:word8) <+ 4w /\ n <+ 4w ==> (((w <<~ m) <<~ n) = w <<~ (m + n))``

val _ = blast_true
  ``(w #<<~ m) #>>~ n = w #<<~ (m - n) : word8``

val _ = blast_true
  ``w <+ 10w /\ s <+ 3w ==> w <<~ (s + 1w) <+ 73w : word16``

val _ = blast_true
  ``w >>>~ v <=+ w : word16``

val _ = blast_true
  ``~word_msb w ==> w >>~ v <= w : word16``

val _ = blast_true
  ``w2w (a * b : word4) = 0xFw && (w2w a * w2w b) : word8``

val _ = blast_true
  ``(1w <<~ a) * b = b <<~ a : 6 word``

val _ = blast_true
  ``a <+ 10w /\ b <+ 10w ==> (a * b <=+ 81w : word8)``

val _ = blast_true
  ``(a + x + c + d - e + 0w = c + -(g - x)) = (-e = -(g + d + a))``

val _ = blast_true
  ``a << 2 + b = b + a * 4w``

val _ = blast_true
  ``(-a * (b + c) + b = -a * b) = (-a * c = -b)``

val _ = blast_true
  ``(a + 4w = b + 2w) = (a + 2w = b)``

val _ = blast_true
  ``(a + 4w = b - 2w) = (a + 6w = b)``

val _ = blast_true
  ``(-a = -b) = (a = b)``

val _ = blast_true
   ``(a + 4w = b) = (b + 4w = a : word3)``

val _ = blast_true
   ``(x + b * 4w + c * 4w = q + e * 4w - r : word3) =
     (4w * b + 4w * c + 4w * e + x + r = q)``

val _ = print "\nsimplifier tests\n\n"

val _ = srw_true
  ``0x20000000w || 0w || w : word32 = w || 0x20000000w``

val _ = srw_true
  ``32w && w && 0w = 0w : word32``

val _ = srw_true
  ``15w && a || (a ?? -1w) = word_T: word4``

val () = qtest_conv "WORD_GROUND_CONV" wordsLib.WORD_GROUND_CONV
 `BIT_SET 2 5 = {2; 4}
  add_with_carry (12w:word8, 11w, T) = (24w,F,F)
  bit_count (0b101101w: word8) = 4
  bit_count_upto 3 (0b101101w: word8) = 2
  concat_word_list [1w; 2w: word8] = 513w: word16
  l2w 10 [1; 2] : word16 = 21w
  reduce_and (0xFw: word4) = 1w
  reduce_nand (0xFw: word4) = 0w
  reduce_nor (0xFw: word4) = 0w
  reduce_or (0xFw: word4) = 1w
  reduce_or (0xFw: word4) = 1w
  reduce_or (0xFw: word4) = 1w
  s2w 16 UNHEX "F0" : word8 = 240w
  saturate_add 12w 4w : word4 = 15w
  saturate_mul 12w 4w : word4 = 15w
  saturate_n2w 18 : word4 = 15w
  saturate_sub 3w 10w : word4 = 0w
  saturate_w2w (18w: word8) : word4 = 15w
  sw2sw (15w: word4) : word8 = 255w
  w2l 2 (0b1011w: word4) = [1; 1; 0; 1]
  w2n (3w: word4) = 3
  w2s 16 HEX (0xF0w: word8) = "F0"
  w2w (15w: word4) : word8 = 15w
  word_1comp (14w: word4) = 1w
  word_2comp (14w: word4) = 2w
  word_H: word8 = 127w
  word_L: word8 = 128w
  word_T: word8 = 255w
  word_abs (255w: word8) = 1w
  word_add 3w 4w : word8 = 7w
  word_and 3w 5w : word8 = 1w
  word_asr_bv 254w 1w : word8 = 255w
  word_asr 254w 1 : word8 = 255w
  word_bit 2 (0b101w: word4) = T
  word_bits 3 2 (0b10101w: word8) = 1w
  word_compare 3w (4w: word4) = 0w
  word_concat (3w: word4) (4w: word4) = 52w: word8
  word_div 8w 2w = 4w : word8
  word_extract 7 4 (0xF0w: word8) = 15w : word4
  word_from_bin_list [1; 0; 1; 1] = 0b1101w: word4
  word_from_bin_string "1011" = 0b1011w: word4
  word_from_dec_list [9; 8] = 89w: word8
  word_from_dec_string "89" = 89w: word8
  word_from_hex_list [10; 11] = 0xBAw: word8
  word_from_hex_string "BA" = 0xBAw: word8
  word_from_oct_list [7] = 7w: word8
  word_from_oct_string "7" = 7w: word8
  word_ge (3w: word4) 2w = T
  word_gt (3w: word4) 2w = T
  word_hi (3w: word4) 2w = T
  word_hs (3w: word4) 2w = T
  word_join (3w: word4) (4w: word4) = 52w: (4 + 4) word
  word_le (3w: word4) 2w = F
  word_lo (3w: word4) 2w = F
  word_ls (3w: word4) 2w = F
  word_lt (3w: word4) 2w = F
  word_len (3w: word4) = 4
  word_log2 (3w: word4) = 1w
  word_lsb (3w: word4) = T
  word_lsl_bv 254w 1w : word8 = 252w
  word_lsl 254w 1 : word8 = 252w
  word_lsr_bv 254w 1w : word8 = 127w
  word_lsr 254w 1 : word8 = 127w
  word_max (3w: word4) 2w = 3w
  word_min (3w: word4) 2w = 2w
  word_mod (3w: word4) 2w = 1w
  word_msb (3w: word4) = F
  word_mul (3w: word4) 2w = 6w
  word_nand (3w: word4) 2w = 13w
  word_nor (3w: word4) 2w = 12w
  word_or (3w: word4) 2w = 3w
  word_quot 8w 2w = 4w : word8
  word_replicate 2 (15w: word4) = 0xFFw: word8
  word_rem (3w: word4) 2w = 1w
  word_reverse (0b1011w: word4) = 0b1101w
  word_rol_bv 254w 1w : word8 = 253w
  word_rol 254w 1 : word8 = 253w
  word_ror_bv 254w 1w : word8 = 127w
  word_ror 254w 1 : word8 = 127w
  word_rrx (T, 254w : word8) = (F, 255w)
  word_sign_extend 4 (0xFw: word16) = 0xFFFFw
  word_signed_bits 7 4 (0xE0w: word16) = 0xFFFEw
  word_slice 7 4 (0xEFw: word16) = 0xE0w
  word_smax (3w: word4) 2w = 3w
  word_smin (3w: word4) 2w = 2w
  word_sub 3w 4w : word8 = 255w
  word_to_bin_list (0b1011w: word4) = [1; 1; 0; 1]
  word_to_bin_string (0b1011w: word4) = "1011"
  word_to_dec_list (1234w: word16) = [4; 3; 2; 1]
  word_to_dec_string (1234w: word16) = "1234"
  word_to_hex_list (0x1234w: word16) = [4; 3; 2; 1]
  word_to_hex_string (0x1234w: word16) = "1234"
  word_to_oct_list (34w: word16) = [2; 4]
  word_to_oct_string (34w: word16) = "42"
  word_xnor 3w 5w : word8 = 249w
  word_xor 3w 5w : word8 = 6w
  `



val elapsed = Timer.checkRealTimer tt

val _ = print ("\nTotal time: " ^ Lib.time_to_string elapsed ^ "\n");



val _ = OS.Process.exit OS.Process.success
