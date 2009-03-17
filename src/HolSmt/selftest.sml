(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Unit tests for HolSmtLib *)

(* Note that you must have Yices 1.0.18 installed for these tests to be carried
   out properly. *)

(*****************************************************************************)
(* utility functions                                                         *)
(*****************************************************************************)

fun die s =
  if !Globals.interactive then
    raise (Fail s)
  else (
    print (s ^ "\n");
    OS.Process.exit OS.Process.failure
  )

(* provable terms *)
fun expect_thm t =
  let val (hyps, concl) = Thm.dest_thm (HolSmtLib.YICES_ORACLE t)
    handle Feedback.HOL_ERR _ =>
      die ("Test failed on term '" ^ Hol_pp.term_to_string t ^
        "': exception HOL_ERR")
  in
    if hyps = [] andalso concl = t then ()
    else
      die ("Test failed on term '" ^ Hol_pp.term_to_string t ^
        "': theorem differs")
  end

(* unprovable terms *)
fun expect_fail t =
  if Lib.can HolSmtLib.YICES_ORACLE t then
    die ("Test failed on term '" ^ Hol_pp.term_to_string t ^
      "': exception expected")
  else ()

(*****************************************************************************)
(* check whether Yices is available; if not, exit                            *)
(*****************************************************************************)

val _ = print "Testing HolSmtLib ...\n"

val _ = HolSmtLib.YICES_ORACLE ``T``
          handle Feedback.HOL_ERR _ =>
            let val s = "Tests for HolSmtLib skipped. Yices not installed?"
            in
              if !Globals.interactive then
                raise (Fail s)
              else (
                print (s ^ "\n");
                OS.Process.exit OS.Process.success
              )
            end

(*****************************************************************************)
(* test cases                                                                *)
(*****************************************************************************)

(* propositional logic *)

val _ = expect_thm ``T``
val _ = expect_fail ``F``
val _ = expect_thm ``p = (p:bool)``
val _ = expect_thm ``p ==> p``
val _ = expect_thm ``p \/ ~ p``
val _ = expect_thm ``p /\ q ==> q /\ p``
val _ = expect_thm ``(p ==> q) /\ (q ==> p) ==> (p = q)``
val _ = expect_fail ``p \/ q ==> p /\ q``
val _ = expect_thm ``if p then (q ==> p) else (p ==> q)``
val _ = expect_thm ``case p of T -> p || F -> ~ p``
val _ = expect_thm ``case p of T -> (q ==> p) || F -> (p ==> q)``

(* numerals *)

(* num *)

val _ = expect_thm ``0n = 0n``
val _ = expect_thm ``1n = 1n``
val _ = expect_fail ``0n = 1n``
val _ = expect_thm ``42n = 42n``

(* int *)

val _ = expect_thm ``0i = 0i``
val _ = expect_thm ``1i = 1i``
val _ = expect_fail ``0i = 1i``
val _ = expect_thm ``42i = 42i``
val _ = expect_thm ``0i = ~0i``
val _ = expect_thm ``~0i = 0i``
val _ = expect_thm ``~0i = ~0i``
val _ = expect_thm ``~42i = ~42i``

(* real *)

val _ = expect_thm ``0r = 0r``
val _ = expect_thm ``1r = 1r``
val _ = expect_fail ``0r = 1r``
val _ = expect_thm ``42r = 42r``
val _ = expect_thm ``0r = ~0r``
val _ = expect_thm ``~0r = 0r``
val _ = expect_thm ``~0r = ~0r``
val _ = expect_thm ``~42r = ~42r``

(* arithmetic operators: SUC, +, -, *, /, DIV, MOD, ABS, MIN, MAX *)

(* num *)

val _ = expect_thm ``SUC 0 = 1``
val _ = expect_thm ``SUC x = x + 1``
val _ = expect_thm ``x < SUC x``
val _ = expect_thm ``(SUC x = SUC y) = (x = y)``
val _ = expect_fail ``SUC (x + y) = (SUC x + SUC y)``

val _ = expect_thm ``(x:num) + 0 = x``
val _ = expect_thm ``0 + (x:num) = x``
val _ = expect_thm ``(x:num) + y = y + x``
val _ = expect_thm ``(x:num) + (y + z) = (x + y) + z``
val _ = expect_thm ``((x:num) + y = 0) = (x = 0) /\ (y = 0)``

val _ = expect_thm ``(x:num) - 0 = x``
val _ = expect_fail ``(x:num) - y = y - x``
val _ = expect_thm ``(x:num) - y - z = x - (y + z)``
val _ = expect_thm ``(x:num) <= y ==> (x - y = 0)``
val _ = expect_thm ``((x:num) - y = 0) \/ (y - x = 0)``

val _ = expect_thm ``(x:num) * 0 = 0``
val _ = expect_thm ``0 * (x:num) = 0``
val _ = expect_thm ``(x:num) * 1 = x``
val _ = expect_thm ``1 * (x:num) = x``
val _ = expect_thm ``(x:num) * 42 = 42 * x``

val _ = expect_thm ``(0:num) DIV 1 = 0``
val _ = expect_thm ``(1:num) DIV 1 = 1``
val _ = expect_thm ``(42:num) DIV 1 = 42``
val _ = expect_thm ``(0:num) DIV 42 = 0``
val _ = expect_thm ``(1:num) DIV 42 = 0``
val _ = expect_thm ``(42:num) DIV 42 = 1``
val _ = expect_thm ``(x:num) DIV 1 = x``
val _ = expect_thm ``(x:num) DIV 42 <= x``
val _ = expect_thm ``((x:num) DIV 42 = x) = (x = 0)``
val _ = expect_fail ``(x:num) DIV 0 = x``
val _ = expect_fail ``(x:num) DIV 0 = 0``
val _ = expect_fail ``(0:num) DIV 0 = 0``
val _ = expect_fail ``(0:num) DIV 0 = 1``
val _ = expect_thm ``(x:num) DIV 0 = x DIV 0``

val _ = expect_thm ``(0:num) MOD 1 = 0``
val _ = expect_thm ``(1:num) MOD 1 = 0``
val _ = expect_thm ``(42:num) MOD 1 = 0``
val _ = expect_thm ``(0:num) MOD 42 = 0``
val _ = expect_thm ``(1:num) MOD 42 = 1``
val _ = expect_thm ``(42:num) MOD 42 = 0``
val _ = expect_thm ``(x:num) MOD 1 = 0``
val _ = expect_thm ``(x:num) MOD 42 < 42``
val _ = expect_thm ``((x:num) MOD 42 = x) = (x < 42)``
val _ = expect_fail ``(x:num) MOD 0 = x``
val _ = expect_fail ``(x:num) MOD 0 = 0``
val _ = expect_fail ``(0:num) MOD 0 = 0``
val _ = expect_fail ``(0:num) MOD 0 = 1``
val _ = expect_thm ``(x:num) MOD 0 = x MOD 0``

(* cf. arithmeticTheory.DIVISION *)
val _ = expect_thm ``((x:num) = x DIV 1 * 1 + x MOD 1) /\ x MOD 1 < 1``
val _ = expect_thm ``((x:num) = x DIV 42 * 42 + x MOD 42) /\ x MOD 42 < 42``

val _ = expect_thm ``MIN (x:num) y <= x``
val _ = expect_thm ``MIN (x:num) y <= y``
val _ = expect_thm ``(z:num) < x /\ z < y ==> z < MIN x y``
val _ = expect_fail ``MIN (x:num) y < x``
val _ = expect_thm ``MIN (x:num) 0 = 0``

val _ = expect_thm ``MAX (x:num) y >= x``
val _ = expect_thm ``MAX (x:num) y >= y``
val _ = expect_thm ``(z:num) > x /\ z > y ==> z > MAX x y``
val _ = expect_fail ``MAX (x:num) y > x``
val _ = expect_thm ``MAX (x:num) 0 = x``

(* int *)

val _ = expect_thm ``(x:int) + 0 = x``
val _ = expect_thm ``0 + (x:int) = x``
val _ = expect_thm ``(x:int) + y = y + x``
val _ = expect_thm ``(x:int) + (y + z) = (x + y) + z``
val _ = expect_fail ``((x:int) + y = 0) = (x = 0) /\ (y = 0)``
val _ = expect_thm ``((x:int) + y = 0) = (x = ~y)``

val _ = expect_thm ``(x:int) - 0 = x``
val _ = expect_fail ``(x:int) - y = y - x``
val _ = expect_thm ``(x:int) - y - z = x - (y + z)``
val _ = expect_fail ``(x:int) <= y ==> (x - y = 0)``
val _ = expect_fail ``((x:int) - y = 0) \/ (y - x = 0)``
val _ = expect_thm ``(x:int) - y = x + ~y``

val _ = expect_thm ``(x:int) * 0 = 0``
val _ = expect_thm ``0 * (x:int) = 0``
val _ = expect_thm ``(x:int) * 1 = x``
val _ = expect_thm ``1 * (x:int) = x``
val _ = expect_thm ``(x:int) * ~1 = ~x``
val _ = expect_thm ``~1 * (x:int) = ~x``
val _ = expect_thm ``(x:int) * 42 = 42 * x``

val _ = expect_thm ``(~42:int) / ~42 = 1``
val _ = expect_thm ``(~1:int) / ~42 = 0``
val _ = expect_thm ``(0:int) / ~42 = 0``
val _ = expect_thm ``(1:int) / ~42 = ~1``
val _ = expect_thm ``(42:int) / ~42 = ~1``
val _ = expect_thm ``(~42:int) / ~1 = 42``
val _ = expect_thm ``(~1:int) / ~1 = 1``
val _ = expect_thm ``(0:int) / ~1 = 0``
val _ = expect_thm ``(1:int) / ~1 = ~1``
val _ = expect_thm ``(42:int) / ~1 = ~42``
val _ = expect_thm ``(~42:int) / 1 = ~42``
val _ = expect_thm ``(~1:int) / 1 = ~1``
val _ = expect_thm ``(0:int) / 1 = 0``
val _ = expect_thm ``(1:int) / 1 = 1``
val _ = expect_thm ``(42:int) / 1 = 42``
val _ = expect_thm ``(~42:int) / 42 = ~1``
val _ = expect_thm ``(~1:int) / 42 = ~1``
val _ = expect_thm ``(0:int) / 42 = 0``
val _ = expect_thm ``(1:int) / 42 = 0``
val _ = expect_thm ``(42:int) / 42 = 1``
val _ = expect_thm ``(x:int) / 1 = x``
val _ = expect_thm ``(x:int) / ~1 = ~x``
val _ = expect_fail ``(x:int) / 42 <= x``
val _ = expect_thm ``(x:int) / 42 <= ABS x``
val _ = expect_fail ``((x:int) / 42 = x) = (x = 0)``
val _ = expect_thm ``((x:int) / 42 = x) = (x = 0) \/ (x = ~1)``
val _ = expect_fail ``(x:int) / 0 = x``
val _ = expect_fail ``(x:int) / 0 = 0``
val _ = expect_fail ``(0:int) / 0 = 0``
val _ = expect_fail ``(0:int) / 0 = 1``
val _ = expect_fail ``(0:int) / 0 = 1 / 0``
val _ = expect_thm ``(x:int) / 0 = x / 0``

(* cf. integerTheory.int_div *)
val _ = expect_thm
  ``(x:int) < 0 ==> (x / 1 = ~(~x / 1) + if ~x % 1 = 0 then 0 else ~1)``
val _ = expect_thm
  ``(x:int) < 0 ==> (x / 42 = ~(~x / 42) + if ~x % 42 = 0 then 0 else ~1)``
val _ = expect_thm
  ``0 <= (x:int) ==> (x / ~42 = ~(x / 42) + if x % 42 = 0 then 0 else ~1)``
val _ = expect_thm
  ``0 <= (x:int) ==> (x / ~1 = ~(x / 1) + if x % 1 = 0 then 0 else ~1)``
val _ = expect_thm ``(x:int) < 0 ==> (x / ~42 = ~x / 42)``
val _ = expect_thm ``(x:int) < 0 ==> (x / ~1 = ~x / 1)``

val _ = expect_thm ``(~42:int) % ~42 = 0``
val _ = expect_thm ``(~1:int) % ~42 = ~1``
val _ = expect_thm ``(0:int) % ~42 = 0``
val _ = expect_thm ``(1:int) % ~42 = ~41``
val _ = expect_thm ``(42:int) % ~42 = 0``
val _ = expect_thm ``(~42:int) % ~1 = 0``
val _ = expect_thm ``(~1:int) % ~1 = 0``
val _ = expect_thm ``(0:int) % ~1 = 0``
val _ = expect_thm ``(1:int) % ~1 = 0``
val _ = expect_thm ``(42:int) % ~1 = 0``
val _ = expect_thm ``(~42:int) % 1 = 0``
val _ = expect_thm ``(~1:int) % 1 = 0``
val _ = expect_thm ``(0:int) % 1 = 0``
val _ = expect_thm ``(1:int) % 1 = 0``
val _ = expect_thm ``(42:int) % 1 = 0``
val _ = expect_thm ``(~42:int) % 42 = 0``
val _ = expect_thm ``(~1:int) % 42 = 41``
val _ = expect_thm ``(0:int) % 42 = 0``
val _ = expect_thm ``(1:int) % 42 = 1``
val _ = expect_thm ``(42:int) % 42 = 0``
val _ = expect_thm ``(x:int) % 1 = 0``
val _ = expect_thm ``(x:int) % ~1 = 0``
val _ = expect_thm ``(x:int) % 42 < 42``
val _ = expect_fail ``((x:int) % 42 = x) = (x < 42)``
val _ = expect_thm ``((x:int) % 42 = x) = (0 <= x) /\ (x < 42)``
val _ = expect_fail ``(x:int) % 0 = x``
val _ = expect_fail ``(x:int) % 0 = 0``
val _ = expect_fail ``(0:int) % 0 = 0``
val _ = expect_fail ``(0:int) % 0 = 1``
val _ = expect_thm ``(x:int) % 0 = x % 0``

(* cf. integerTheory.int_mod *)
val _ = expect_thm ``(x:int) % ~42 = x - x / ~42 * ~42``
val _ = expect_thm ``(x:int) % ~1 = x - x / ~1 * ~1``
val _ = expect_thm ``(x:int) % 1 = x - x / 1 * 1``
val _ = expect_thm ``(x:int) % 42 = x - x / 42 * 42``

val _ = expect_thm ``ABS (x:int) >= 0``
val _ = expect_thm ``(ABS (x:int) = 0) = (x = 0)``
val _ = expect_thm ``(x:int) >= 0 ==> (ABS x = x)``
val _ = expect_thm ``(x:int) <= 0 ==> (ABS x = ~x)``
val _ = expect_thm ``ABS (ABS (x:int)) = ABS x``
val _ = expect_fail ``ABS (x:int) = x``

val _ = expect_thm ``int_min (x:int) y <= x``
val _ = expect_thm ``int_min (x:int) y <= y``
val _ = expect_thm ``(z:int) < x /\ z < y ==> z < int_min x y``
val _ = expect_fail ``int_min (x:int) y < x``
val _ = expect_fail ``int_min (x:int) 0 = 0``
val _ = expect_thm ``(x:int) >= 0 ==> (int_min x 0 = 0)``

val _ = expect_thm ``int_max (x:int) y >= x``
val _ = expect_thm ``int_max (x:int) y >= y``
val _ = expect_thm ``(z:int) > x /\ z > y ==> z > int_max x y``
val _ = expect_fail ``int_max (x:int) y > x``
val _ = expect_thm ``(x:int) >= 0 ==> (int_max x 0 = x)``

(* real *)

val _ = expect_thm ``(x:real) + 0 = x``
val _ = expect_thm ``0 + (x:real) = x``
val _ = expect_thm ``(x:real) + y = y + x``
val _ = expect_thm ``(x:real) + (y + z) = (x + y) + z``
val _ = expect_fail ``((x:real) + y = 0) = (x = 0) /\ (y = 0)``
val _ = expect_thm ``((x:real) + y = 0) = (x = ~y)``

val _ = expect_thm ``(x:real) - 0 = x``
val _ = expect_fail ``(x:real) - y = y - x``
val _ = expect_thm ``(x:real) - y - z = x - (y + z)``
val _ = expect_fail ``(x:real) <= y ==> (x - y = 0)``
val _ = expect_fail ``((x:real) - y = 0) \/ (y - x = 0)``
val _ = expect_thm ``(x:real) - y = x + ~y``

val _ = expect_thm ``(x:real) * 0 = 0``
val _ = expect_thm ``0 * (x:real) = 0``
val _ = expect_thm ``(x:real) * 1 = x``
val _ = expect_thm ``1 * (x:real) = x``
val _ = expect_thm ``(x:real) * 42 = 42 * x``

val _ = expect_thm ``(x:real) / 1 = x``
val _ = expect_thm ``x > 0 ==> (x:real) / 42 < x``
val _ = expect_thm ``x < 0 ==> (x:real) / 42 > x``

val _ = expect_thm ``abs (x:real) >= 0``
val _ = expect_thm ``(abs (x:real) = 0) = (x = 0)``
val _ = expect_thm ``(x:real) >= 0 ==> (abs x = x)``
val _ = expect_thm ``(x:real) <= 0 ==> (abs x = ~x)``
val _ = expect_thm ``abs (abs (x:real)) = abs x``
val _ = expect_fail ``abs (x:real) = x``

val _ = expect_thm ``min (x:real) y <= x``
val _ = expect_thm ``min (x:real) y <= y``
val _ = expect_thm ``(z:real) < x /\ z < y ==> z < min x y``
val _ = expect_fail ``min (x:real) y < x``
val _ = expect_fail ``min (x:real) 0 = 0``
val _ = expect_thm ``(x:real) >= 0 ==> (min x 0 = 0)``

val _ = expect_thm ``max (x:real) y >= x``
val _ = expect_thm ``max (x:real) y >= y``
val _ = expect_thm ``(z:real) > x /\ z > y ==> z > max x y``
val _ = expect_fail ``max (x:real) y > x``
val _ = expect_thm ``(x:real) >= 0 ==> (max x 0 = x)``

(* arithmetic inequalities: <, <=, >, >= *)

(* num *)

val _ = expect_thm ``0n < 1n``
val _ = expect_fail ``1n < 0n``
val _ = expect_fail ``(x:num) < x``
val _ = expect_thm ``(x:num) < y ==> 42 * x < 42 * y``

val _ = expect_thm ``0n <= 1n``
val _ = expect_fail ``1n <= 0n``
val _ = expect_thm ``(x:num) <= x``
val _ = expect_thm ``(x:num) <= y ==> 42 * x <= 42 * y``

val _ = expect_thm ``1n > 0n``
val _ = expect_fail ``0n > 1n``
val _ = expect_fail ``(x:num) > x``
val _ = expect_thm ``(x:num) > y ==> 42 * x > 42 * y``

val _ = expect_thm ``1n >= 0n``
val _ = expect_fail ``0n >= 1n``
val _ = expect_thm ``(x:num) >= x``
val _ = expect_thm ``(x:num) >= y ==> 42 * x >= 42 * y``

val _ = expect_thm ``((x:num) < y) = (y > x)``
val _ = expect_thm ``((x:num) <= y) = (y >= x)``
val _ = expect_thm ``(x:num) < y /\ y <= z ==> x < z``
val _ = expect_thm ``(x:num) <= y /\ y <= z ==> x <= z``
val _ = expect_thm ``(x:num) > y /\ y >= z ==> x > z``
val _ = expect_thm ``(x:num) >= y /\ y >= z ==> x >= z``

val _ = expect_thm ``(x:num) >= 0``
val _ = expect_thm ``0 < (x:num) /\ x <= 1 ==> (x = 1)``

(* int *)

val _ = expect_thm ``0i < 1i``
val _ = expect_fail ``1i < 0i``
val _ = expect_fail ``(x:int) < x``
val _ = expect_thm ``(x:int) < y ==> 42 * x < 42 * y``

val _ = expect_thm ``0i <= 1i``
val _ = expect_fail ``1i <= 0i``
val _ = expect_thm ``(x:int) <= x``
val _ = expect_thm ``(x:int) <= y ==> 42 * x <= 42 * y``

val _ = expect_thm ``1i > 0i``
val _ = expect_fail ``0i > 1i``
val _ = expect_fail ``(x:int) > x``
val _ = expect_thm ``(x:int) > y ==> 42 * x > 42 * y``

val _ = expect_thm ``1i >= 0i``
val _ = expect_fail ``0i >= 1i``
val _ = expect_thm ``(x:int) >= x``
val _ = expect_thm ``(x:int) >= y ==> 42 * x >= 42 * y``

val _ = expect_thm ``((x:int) < y) = (y > x)``
val _ = expect_thm ``((x:int) <= y) = (y >= x)``
val _ = expect_thm ``(x:int) < y /\ y <= z ==> x < z``
val _ = expect_thm ``(x:int) <= y /\ y <= z ==> x <= z``
val _ = expect_thm ``(x:int) > y /\ y >= z ==> x > z``
val _ = expect_thm ``(x:int) >= y /\ y >= z ==> x >= z``

val _ = expect_fail ``(x:int) >= 0``
val _ = expect_thm ``0 < (x:int) /\ x <= 1 ==> (x = 1)``

(* real *)

val _ = expect_thm ``0r < 1r``
val _ = expect_fail ``1r < 0r``
val _ = expect_fail ``(x:real) < x``
val _ = expect_thm ``(x:real) < y ==> 42 * x < 42 * y``

val _ = expect_thm ``0n <= 1n``
val _ = expect_fail ``1n <= 0n``
val _ = expect_thm ``(x:num) <= x``
val _ = expect_thm ``(x:num) <= y ==> 2 * x <= 2 * y``

val _ = expect_thm ``1r > 0r``
val _ = expect_fail ``0r > 1r``
val _ = expect_fail ``(x:real) > x``
val _ = expect_thm ``(x:real) > y ==> 42 * x > 42 * y``

val _ = expect_thm ``1r >= 0r``
val _ = expect_fail ``0r >= 1r``
val _ = expect_thm ``(x:real) >= x``
val _ = expect_thm ``(x:real) >= y ==> 42 * x >= 42 * y``

val _ = expect_thm ``((x:real) < y) = (y > x)``
val _ = expect_thm ``((x:real) <= y) = (y >= x)``
val _ = expect_thm ``(x:real) < y /\ y <= z ==> x < z``
val _ = expect_thm ``(x:real) <= y /\ y <= z ==> x <= z``
val _ = expect_thm ``(x:real) > y /\ y >= z ==> x > z``
val _ = expect_thm ``(x:real) >= y /\ y >= z ==> x >= z``

val _ = expect_fail ``(x:real) >= 0``
val _ = expect_fail ``0 < (x:real) /\ x <= 1 ==> (x = 1)``

(* uninterpreted functions *)

val _ = expect_thm ``(x = y) ==> (f x = f y)``
val _ = expect_thm ``(x = y) ==> (f x y = f y x)``
val _ = expect_thm ``(f (f x) = x) /\ (f (f (f (f (f x)))) = x) ==> (f x = x)``
val _ = expect_fail ``(f x = f y) ==> (x = y)``

(* predicates *)

val _ = expect_thm ``P x ==> P x``
val _ = expect_fail ``P x ==> Q x``
val _ = expect_fail ``P x ==> P y``
val _ = expect_fail ``P x y ==> P x x``
val _ = expect_fail ``P x y ==> P y x``
val _ = expect_fail ``P x y ==> P y y``

(* quantifiers *)

val _ = expect_thm ``!x. x = x``
(* Yices 1.0.18 fails to decide this one
val _ = expect_thm ``?x. x = x``
*)
val _ = expect_thm ``(?y. !x. P x y) ==> (!x. ?y. P x y)``
(* Yices 1.0.18 fails to decide this one
val _ = expect_fail ``(!x. ?y. P x y) ==> (?y. !x. P x y)``
*)
val _ = expect_fail ``(?x. P x) ==> !x. P x``
val _ = expect_thm ``?x. P x ==> !x. P x``

(* lambda abstractions *)

val _ = expect_thm ``(\x. x) = (\y. y)``
val _ = expect_thm ``(\x. \x. x) x x = (\y. \y. y) y x``
val _ = expect_thm ``(\x. x (\x. x)) = (\y. y (\x. x))``
(* Yices 1.0.18 fails to decide this one
val _ = expect_fail ``(\x. x (\x. x)) = (\y. y x)``
*)
val _ = expect_thm ``f x = (\x. f x) x``
val _ = expect_thm ``f x = (\y. f y) x``

(* tuples, FST, SND *)

val _ = expect_fail ``(x, y) = (x, z)``
val _ = expect_fail ``(x, y) = (z, y)``
val _ = expect_fail ``(x, y) = (y, x)``
val _ = expect_thm ``((x, y) = (y, x)) = (x = y)``
val _ = expect_thm ``((x, y, z) = (y, z, x)) = (x = y) /\ (y = z)``
val _ = expect_thm ``((x, y) = (u, v)) = (x = u) /\ (y = v)``

val _ = expect_fail ``y = FST (x, y)``
val _ = expect_thm ``x = FST (x, y)``
val _ = expect_thm ``(FST (x, y, z) = FST (u, v, w)) = (x = u)``
val _ = expect_fail ``(FST (x, y, z) = FST (u, v, w)) = (x = u) /\ (y = w)``

val _ = expect_thm ``y = SND (x, y)``
val _ = expect_fail ``x = SND (x, y)``
val _ = expect_fail ``(SND (x, y, z) = SND (u, v, w)) = (y = v)``
val _ = expect_fail ``(SND (x, y, z) = SND (u, v, w)) = (z = w)``
val _ = expect_thm ``(SND (x, y, z) = SND (u, v, w)) = (y = v) /\ (z = w)``

val _ = expect_thm ``(FST (x, y) = SND (x, y)) = (x = y)``
val _ = expect_thm ``(FST p = SND p) = (p = (SND p, FST p))``
val _ = expect_thm ``((\p. FST p) (x, y)= (\p. SND p) (x, y)) = (x = y)``

(*****************************************************************************)

val _ = print "... done, all tests for HolSmtLib successful.\n"

val _ = OS.Process.exit OS.Process.success
