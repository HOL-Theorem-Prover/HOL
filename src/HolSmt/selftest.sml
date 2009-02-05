
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

val _ = expect_thm ``~42i = ~42i``

(* real *)

val _ = expect_thm ``0r = 0r``

val _ = expect_thm ``1r = 1r``

val _ = expect_fail ``0r = 1r``

val _ = expect_thm ``42r = 42r``

val _ = expect_thm ``0r = ~0r``

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

(* TODO
val _ = expect_thm ``(x:num) DIV 1 = x``

val _ = expect_thm ``(x:num) DIV 42 <= x``

val _ = expect_thm ``((x:num) DIV 42 = x) = (x = 0)``

val _ = expect_fail ``(x:num) DIV 0 = x``

val _ = expect_fail ``(x:num) DIV 0 = 0``

val _ = expect_fail ``(0:num) DIV 0 = 0``

val _ = expect_fail ``(0:num) DIV 0 = 1``

val _ = expect_thm ``(x:num) DIV 0 = x DIV 0``


val _ = expect_thm ``(x:num) MOD 1 = 0``

val _ = expect_thm ``(x:num) MOD 42 < 42``

val _ = expect_thm ``((x:num) MOD 42 = x) = (x < 42)``

val _ = expect_fail ``(x:num) MOD 0 = x``

val _ = expect_fail ``(x:num) MOD 0 = 0``

val _ = expect_fail ``(0:num) MOD 0 = 0``

val _ = expect_fail ``(0:num) MOD 0 = 1``

val _ = expect_thm ``(x:num) MOD 0 = x MOD 0``
*)

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

val _ = expect_thm ``(x:int) * 42 = 42 * x``

(* TODO
val _ = expect_thm ``(x:int) DIV 1 = x``

val _ = expect_thm ``(x:int) DIV 42 <= x``

val _ = expect_thm ``((x:int) DIV 42 = x) = (x = 0)``

val _ = expect_fail ``(x:int) DIV 0 = x``

val _ = expect_fail ``(x:int) DIV 0 = 0``

val _ = expect_fail ``(0:int) DIV 0 = 0``

val _ = expect_fail ``(0:int) DIV 0 = 1``

val _ = expect_thm ``(x:int) DIV 0 = x DIV 0``


val _ = expect_thm ``(x:int) MOD 1 = 0``

val _ = expect_thm ``(x:int) MOD 42 < 42``

val _ = expect_thm ``((x:int) MOD 42 = x) = (x < 42)``

val _ = expect_fail ``(x:int) MOD 0 = x``

val _ = expect_fail ``(x:int) MOD 0 = 0``

val _ = expect_fail ``(0:int) MOD 0 = 0``

val _ = expect_fail ``(0:int) MOD 0 = 1``

val _ = expect_thm ``(x:int) MOD 0 = x MOD 0``
*)

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

(*****************************************************************************)

val _ = print "... done, all tests for HolSmtLib successful.\n"

val _ = OS.Process.exit OS.Process.success
