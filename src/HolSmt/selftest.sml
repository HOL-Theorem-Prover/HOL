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
    print ("\n" ^ s ^ "\n");
    OS.Process.exit OS.Process.failure
  )

(* provable terms *)
fun expect_thm solver t =
  let val (hyps, concl) = Thm.dest_thm ((HolSmtLib.GENERIC_SMT solver) t)
    handle Feedback.HOL_ERR {origin_structure, origin_function, message} =>
      die ("Test of solver '" ^ SolverSpec.get_name solver ^
        "' failed on term '" ^ Hol_pp.term_to_string t ^
        "': exception HOL_ERR (in " ^ origin_structure^ "." ^ origin_function
                                    ^ ", message: " ^ message ^ ")")
  in
    if hyps = [] andalso concl = t then ()
    else
      die ("Test of solver '" ^ SolverSpec.get_name solver ^
        "' failed on term '" ^ Hol_pp.term_to_string t ^
        "': theorem differs")
  end

(* unprovable terms *)
fun expect_fail solver t =
  let val _ = HolSmtLib.GENERIC_SMT solver t
  in
    die ("Test of solver '" ^ SolverSpec.get_name solver ^
      "' failed on term '" ^ Hol_pp.term_to_string t ^
      "': exception expected")
  end handle Feedback.HOL_ERR {origin_structure, origin_function, message} =>
    if origin_structure = "HolSmtLib" andalso
       origin_function = "GENERIC_SMT" andalso
       message = "solver reports negated term to be 'satisfiable'" then
      ()
    else
      die ("Test of solver '" ^ SolverSpec.get_name solver ^
        "' failed on term '" ^ Hol_pp.term_to_string t ^
        "': exception HOL_ERR has unexpected argument values (in " ^
        origin_structure^ "." ^ origin_function ^ ", message: " ^ message ^ ")")

(*****************************************************************************)
(* check whether SMT solvers are installed                                   *)
(*****************************************************************************)

val _ = print "Testing HolSmtLib "

val _ = Feedback.set_trace "HolSmtLib" 0

val yices_installed = Lib.can (HolSmtLib.GENERIC_SMT Yices.YicesOracle) ``T``

val _ = if not yices_installed then
          print "(Yices not installed? Some tests will be skipped.) "
        else ()

val cvc3_installed = Lib.can (HolSmtLib.GENERIC_SMT CVC3.CVC3SMTOracle) ``T``

val _ = if not cvc3_installed then
          print "(CVC3 not installed? Some tests will be skipped.) "
        else ()

(*****************************************************************************)
(* test cases                                                                *)
(*****************************************************************************)

local
  val thm_YO = if yices_installed then
                 (fn t => (expect_thm Yices.YicesOracle t; print "."))
               else Lib.K ()
  val fail_YO = if yices_installed then
                 (fn t => (expect_fail Yices.YicesOracle t; print "."))
               else Lib.K ()

  val thm_YSO = if yices_installed then
                 (fn t => (expect_thm Yices.YicesSMTOracle t; print "."))
               else Lib.K ()
  val fail_YSO = if yices_installed then
                 (fn t => (expect_fail Yices.YicesSMTOracle t; print "."))
               else Lib.K ()

  val thm_CVC = if cvc3_installed then
                 (fn t => (expect_thm CVC3.CVC3SMTOracle t; print "."))
               else Lib.K ()
  val fail_CVC = if cvc3_installed then
                 (fn t => (expect_fail CVC3.CVC3SMTOracle t; print "."))
               else Lib.K ()
in
  val tests = [

    (* propositional logic *)
    (``T``, [thm_YO, thm_YSO, thm_CVC]),
    (``F``, [fail_YO, fail_YSO, fail_CVC]),
    (``p = (p:bool)``, [thm_YO, thm_YSO, thm_CVC]),
    (``p ==> p``, [thm_YO, thm_YSO, thm_CVC]),
    (``p \/ ~ p``, [thm_YO, thm_YSO, thm_CVC]),
    (``p /\ q ==> q /\ p``, [thm_YO, thm_YSO, thm_CVC]),
    (``(p ==> q) /\ (q ==> p) ==> (p = q)``, [thm_YO, thm_YSO, thm_CVC]),
    (``p \/ q ==> p /\ q``, [fail_YO, fail_YSO, fail_CVC]),
    (``if p then (q ==> p) else (p ==> q)``, [thm_YO, thm_YSO, thm_CVC]),
    (``case p of T -> p || F -> ~ p``, [thm_YO, thm_YSO, thm_CVC]),
    (``case p of T -> (q ==> p) || F -> (p ==> q)``,
      [thm_YO, thm_YSO, thm_CVC]),

    (* numerals *)

    (* num *)

    (``0n = 0n``, [thm_YO, thm_YSO, thm_CVC]),
    (``1n = 1n``, [thm_YO, thm_YSO, thm_CVC]),
    (``0n = 1n``, [fail_YO, fail_YSO, fail_CVC]),
    (``42n = 42n``, [thm_YO, thm_YSO, thm_CVC]),

    (* int *)

    (``0i = 0i``, [thm_YO, thm_YSO, thm_CVC]),
    (``1i = 1i``, [thm_YO, thm_YSO, thm_CVC]),
    (``0i = 1i``, [fail_YO, fail_YSO, fail_CVC]),
    (``42i = 42i``, [thm_YO, thm_YSO, thm_CVC]),
    (``0i = ~0i``, [thm_YO, thm_YSO, thm_CVC]),
    (``~0i = 0i``, [thm_YO, thm_YSO, thm_CVC]),
    (``~0i = ~0i``, [thm_YO, thm_YSO, thm_CVC]),
    (``~42i = ~42i``, [thm_YO, thm_YSO, thm_CVC]),

    (* real *)

    (``0r = 0r``, [thm_YO, thm_YSO, thm_CVC]),
    (``1r = 1r``, [thm_YO, thm_YSO, thm_CVC]),
    (``0r = 1r``, [fail_YO, fail_YSO, fail_CVC]),
    (``42r = 42r``, [thm_YO, thm_YSO, thm_CVC]),
    (``0r = ~0r``, [thm_YO]),
    (``~0r = 0r``, [thm_YO]),
    (``~0r = ~0r``, [thm_YO, thm_YSO, thm_CVC]),
    (``~42r = ~42r``, [thm_YO, thm_YSO, thm_CVC]),

    (* arithmetic operators: SUC, +, -, *, /, DIV, MOD, ABS, MIN, MAX *)

    (* num *)

    (``SUC 0 = 1``, [thm_YO]),
    (``SUC x = x + 1``, [thm_YO]),
    (``x < SUC x``, [thm_YO]),
    (``(SUC x = SUC y) = (x = y)``, [thm_YO]),
    (``SUC (x + y) = (SUC x + SUC y)``, [fail_YO, fail_YSO, fail_CVC]),

    (``(x:num) + 0 = x``, [thm_YO]),
    (``0 + (x:num) = x``, [thm_YO]),
    (``(x:num) + y = y + x``, [thm_YO]),
    (``(x:num) + (y + z) = (x + y) + z``, [thm_YO]),
    (``((x:num) + y = 0) = (x = 0) /\ (y = 0)``, [thm_YO]),

    (``(x:num) - 0 = x``, [thm_YO]),
    (``(x:num) - y = y - x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:num) - y - z = x - (y + z)``, [thm_YO]),
    (``(x:num) <= y ==> (x - y = 0)``, [thm_YO]),
    (``((x:num) - y = 0) \/ (y - x = 0)``, [thm_YO]),

    (``(x:num) * 0 = 0``, [thm_YO]),
    (``0 * (x:num) = 0``, [thm_YO]),
    (``(x:num) * 1 = x``, [thm_YO]),
    (``1 * (x:num) = x``, [thm_YO]),
    (``(x:num) * 42 = 42 * x``, [thm_YO]),

    (``(0:num) DIV 1 = 0``, [thm_YO]),
    (``(1:num) DIV 1 = 1``, [thm_YO]),
    (``(42:num) DIV 1 = 42``, [thm_YO]),
    (``(0:num) DIV 42 = 0``, [thm_YO]),
    (``(1:num) DIV 42 = 0``, [thm_YO]),
    (``(42:num) DIV 42 = 1``, [thm_YO]),
    (``(x:num) DIV 1 = x``, [thm_YO]),
    (``(x:num) DIV 42 <= x``, [thm_YO]),
    (``((x:num) DIV 42 = x) = (x = 0)``, [thm_YO]),
    (``(x:num) DIV 0 = x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:num) DIV 0 = 0``, [fail_YO, fail_YSO, fail_CVC]),
    (``(0:num) DIV 0 = 0``, [fail_YO, fail_YSO, fail_CVC]),
    (``(0:num) DIV 0 = 1``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:num) DIV 0 = x DIV 0``, [thm_YO]),

    (``(0:num) MOD 1 = 0``, [thm_YO]),
    (``(1:num) MOD 1 = 0``, [thm_YO]),
    (``(42:num) MOD 1 = 0``, [thm_YO]),
    (``(0:num) MOD 42 = 0``, [thm_YO]),
    (``(1:num) MOD 42 = 1``, [thm_YO]),
    (``(42:num) MOD 42 = 0``, [thm_YO]),
    (``(x:num) MOD 1 = 0``, [thm_YO]),
    (``(x:num) MOD 42 < 42``, [thm_YO]),
    (``((x:num) MOD 42 = x) = (x < 42)``, [thm_YO]),
    (``(x:num) MOD 0 = x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:num) MOD 0 = 0``, [fail_YO, fail_YSO, fail_CVC]),
    (``(0:num) MOD 0 = 0``, [fail_YO, fail_YSO, fail_CVC]),
    (``(0:num) MOD 0 = 1``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:num) MOD 0 = x MOD 0``, [thm_YO, thm_YSO, thm_CVC]),

    (* cf. arithmeticTheory.DIVISION *)
    (``((x:num) = x DIV 1 * 1 + x MOD 1) /\ x MOD 1 < 1``, [thm_YO]),
    (``((x:num) = x DIV 42 * 42 + x MOD 42) /\ x MOD 42 < 42``, [thm_YO]),

    (``MIN (x:num) y <= x``, [thm_YO]),
    (``MIN (x:num) y <= y``, [thm_YO]),
    (``(z:num) < x /\ z < y ==> z < MIN x y``, [thm_YO]),
    (``MIN (x:num) y < x``, [fail_YO, fail_YSO, fail_CVC]),
    (``MIN (x:num) 0 = 0``, [thm_YO]),

    (``MAX (x:num) y >= x``, [thm_YO]),
    (``MAX (x:num) y >= y``, [thm_YO]),
    (``(z:num) > x /\ z > y ==> z > MAX x y``, [thm_YO]),
    (``MAX (x:num) y > x``, [fail_YO, fail_YSO, fail_CVC]),
    (``MAX (x:num) 0 = x``, [thm_YO]),

    (* int *)

    (``(x:int) + 0 = x``, [thm_YO, thm_YSO, thm_CVC]),
    (``0 + (x:int) = x``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x:int) + y = y + x``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x:int) + (y + z) = (x + y) + z``, [thm_YO, thm_YSO, thm_CVC]),
    (``((x:int) + y = 0) = (x = 0) /\ (y = 0)``, [fail_YO, fail_YSO, fail_CVC]),
    (``((x:int) + y = 0) = (x = ~y)``, [thm_YO, thm_YSO, thm_CVC]),

    (``(x:int) - 0 = x``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x:int) - y = y - x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:int) - y - z = x - (y + z)``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x:int) <= y ==> (x - y = 0)``, [fail_YO, fail_YSO, fail_CVC]),
    (``((x:int) - y = 0) \/ (y - x = 0)``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:int) - y = x + ~y``, [thm_YO, thm_YSO, thm_CVC]),

    (``(x:int) * 0 = 0``, [thm_YO, thm_YSO, thm_CVC]),
    (``0 * (x:int) = 0``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x:int) * 1 = x``, [thm_YO, thm_YSO, thm_CVC]),
    (``1 * (x:int) = x``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x:int) * ~1 = ~x``, [thm_YO, thm_YSO, thm_CVC]),
    (``~1 * (x:int) = ~x``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x:int) * 42 = 42 * x``, [thm_YO, thm_YSO, thm_CVC]),

    (``(~42:int) / ~42 = 1``, [thm_YO]),
    (``(~1:int) / ~42 = 0``, [thm_YO]),
    (``(0:int) / ~42 = 0``, [thm_YO]),
    (``(1:int) / ~42 = ~1``, [thm_YO]),
    (``(42:int) / ~42 = ~1``, [thm_YO]),
    (``(~42:int) / ~1 = 42``, [thm_YO]),
    (``(~1:int) / ~1 = 1``, [thm_YO]),
    (``(0:int) / ~1 = 0``, [thm_YO]),
    (``(1:int) / ~1 = ~1``, [thm_YO]),
    (``(42:int) / ~1 = ~42``, [thm_YO]),
    (``(~42:int) / 1 = ~42``, [thm_YO]),
    (``(~1:int) / 1 = ~1``, [thm_YO]),
    (``(0:int) / 1 = 0``, [thm_YO]),
    (``(1:int) / 1 = 1``, [thm_YO]),
    (``(42:int) / 1 = 42``, [thm_YO]),
    (``(~42:int) / 42 = ~1``, [thm_YO]),
    (``(~1:int) / 42 = ~1``, [thm_YO]),
    (``(0:int) / 42 = 0``, [thm_YO]),
    (``(1:int) / 42 = 0``, [thm_YO]),
    (``(42:int) / 42 = 1``, [thm_YO]),
    (``(x:int) / 1 = x``, [thm_YO]),
    (``(x:int) / ~1 = ~x``, [thm_YO]),
    (``(x:int) / 42 <= x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:int) / 42 <= ABS x``, [thm_YO]),
    (``((x:int) / 42 = x) = (x = 0)``, [fail_YO, fail_YSO, fail_CVC]),
    (``((x:int) / 42 = x) = (x = 0) \/ (x = ~1)``, [thm_YO]),
    (``(x:int) / 0 = x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:int) / 0 = 0``, [fail_YO, fail_YSO, fail_CVC]),
    (``(0:int) / 0 = 0``, [fail_YO, fail_YSO, fail_CVC]),
    (``(0:int) / 0 = 1``, [fail_YO, fail_YSO, fail_CVC]),
    (``(0:int) / 0 = 1 / 0``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:int) / 0 = x / 0``, [thm_YO, thm_YSO, thm_CVC]),

    (* cf. integerTheory.int_div *)
    (``(x:int) < 0 ==> (x / 1 = ~(~x / 1) + if ~x % 1 = 0 then 0 else ~1)``,
      [thm_YO]),
    (``(x:int) < 0 ==> (x / 42 = ~(~x / 42) + if ~x % 42 = 0 then 0 else ~1)``,
      [thm_YO]),
    (``0 <= (x:int) ==> (x / ~42 = ~(x / 42) + if x % 42 = 0 then 0 else ~1)``,
      [thm_YO]),
    (``0 <= (x:int) ==> (x / ~1 = ~(x / 1) + if x % 1 = 0 then 0 else ~1)``,
      [thm_YO]),
    (``(x:int) < 0 ==> (x / ~42 = ~x / 42)``, [thm_YO]),
    (``(x:int) < 0 ==> (x / ~1 = ~x / 1)``, [thm_YO]),

    (``(~42:int) % ~42 = 0``, [thm_YO]),
    (``(~1:int) % ~42 = ~1``, [thm_YO]),
    (``(0:int) % ~42 = 0``, [thm_YO]),
    (``(1:int) % ~42 = ~41``, [thm_YO]),
    (``(42:int) % ~42 = 0``, [thm_YO]),
    (``(~42:int) % ~1 = 0``, [thm_YO]),
    (``(~1:int) % ~1 = 0``, [thm_YO]),
    (``(0:int) % ~1 = 0``, [thm_YO]),
    (``(1:int) % ~1 = 0``, [thm_YO]),
    (``(42:int) % ~1 = 0``, [thm_YO]),
    (``(~42:int) % 1 = 0``, [thm_YO]),
    (``(~1:int) % 1 = 0``, [thm_YO]),
    (``(0:int) % 1 = 0``, [thm_YO]),
    (``(1:int) % 1 = 0``, [thm_YO]),
    (``(42:int) % 1 = 0``, [thm_YO]),
    (``(~42:int) % 42 = 0``, [thm_YO]),
    (``(~1:int) % 42 = 41``, [thm_YO]),
    (``(0:int) % 42 = 0``, [thm_YO]),
    (``(1:int) % 42 = 1``, [thm_YO]),
    (``(42:int) % 42 = 0``, [thm_YO]),
    (``(x:int) % 1 = 0``, [thm_YO]),
    (``(x:int) % ~1 = 0``, [thm_YO]),
    (``(x:int) % 42 < 42``, [thm_YO]),
    (``((x:int) % 42 = x) = (x < 42)``, [fail_YO, fail_YSO, fail_CVC]),
    (``((x:int) % 42 = x) = (0 <= x) /\ (x < 42)``, [thm_YO]),
    (``(x:int) % 0 = x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:int) % 0 = 0``, [fail_YO, fail_YSO, fail_CVC]),
    (``(0:int) % 0 = 0``, [fail_YO, fail_YSO, fail_CVC]),
    (``(0:int) % 0 = 1``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:int) % 0 = x % 0``, [thm_YO, thm_YSO, thm_CVC]),

    (* cf. integerTheory.int_mod *)
    (``(x:int) % ~42 = x - x / ~42 * ~42``, [thm_YO]),
    (``(x:int) % ~1 = x - x / ~1 * ~1``, [thm_YO]),
    (``(x:int) % 1 = x - x / 1 * 1``, [thm_YO]),
    (``(x:int) % 42 = x - x / 42 * 42``, [thm_YO]),

    (``ABS (x:int) >= 0``, [thm_YO, thm_YSO, thm_CVC]),
    (``(ABS (x:int) = 0) = (x = 0)``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x:int) >= 0 ==> (ABS x = x)``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x:int) <= 0 ==> (ABS x = ~x)``, [thm_YO, thm_YSO, thm_CVC]),
    (``ABS (ABS (x:int)) = ABS x``, [thm_YO, thm_YSO, thm_CVC]),
    (``ABS (x:int) = x``, [fail_YO]),

    (``int_min (x:int) y <= x``, [thm_YO, thm_YSO, thm_CVC]),
    (``int_min (x:int) y <= y``, [thm_YO, thm_YSO, thm_CVC]),
    (``(z:int) < x /\ z < y ==> z < int_min x y``, [thm_YO, thm_YSO, thm_CVC]),
    (``int_min (x:int) y < x``, [fail_YO]),
    (``int_min (x:int) 0 = 0``, [fail_YO]),
    (``(x:int) >= 0 ==> (int_min x 0 = 0)``, [thm_YO, thm_YSO, thm_CVC]),

    (``int_max (x:int) y >= x``, [thm_YO, thm_YSO, thm_CVC]),
    (``int_max (x:int) y >= y``, [thm_YO, thm_YSO, thm_CVC]),
    (``(z:int) > x /\ z > y ==> z > int_max x y``, [thm_YO, thm_YSO, thm_CVC]),
    (``int_max (x:int) y > x``, [fail_YO]),
    (``(x:int) >= 0 ==> (int_max x 0 = x)``, [thm_YO, thm_YSO, thm_CVC]),

    (* real *)

    (``(x:real) + 0 = x``, [thm_YO]),
    (``0 + (x:real) = x``, [thm_YO]),
    (``(x:real) + y = y + x``, [thm_YO]),
    (``(x:real) + (y + z) = (x + y) + z``, [thm_YO]),
    (``((x:real) + y = 0) = (x = 0) /\ (y = 0)``,
       [fail_YO, fail_YSO, fail_CVC]),
    (``((x:real) + y = 0) = (x = ~y)``, [thm_YO]),

    (``(x:real) - 0 = x``, [thm_YO]),
    (``(x:real) - y = y - x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:real) - y - z = x - (y + z)``, [thm_YO]),
    (``(x:real) <= y ==> (x - y = 0)``, [fail_YO, fail_YSO, fail_CVC]),
    (``((x:real) - y = 0) \/ (y - x = 0)``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:real) - y = x + ~y``, [thm_YO]),

    (``(x:real) * 0 = 0``, [thm_YO]),
    (``0 * (x:real) = 0``, [thm_YO]),
    (``(x:real) * 1 = x``, [thm_YO]),
    (``1 * (x:real) = x``, [thm_YO]),
    (``(x:real) * 42 = 42 * x``, [thm_YO]),

    (``(x:real) / 1 = x``, [thm_YO]),
    (``x > 0 ==> (x:real) / 42 < x``, [thm_YO]),
    (``x < 0 ==> (x:real) / 42 > x``, [thm_YO]),

    (``abs (x:real) >= 0``, [thm_YO]),
    (``(abs (x:real) = 0) = (x = 0)``, [thm_YO]),
    (``(x:real) >= 0 ==> (abs x = x)``, [thm_YO]),
    (``(x:real) <= 0 ==> (abs x = ~x)``, [thm_YO]),
    (``abs (abs (x:real)) = abs x``, [thm_YO]),
    (``abs (x:real) = x``, [fail_YO, fail_YSO, fail_CVC]),

    (``min (x:real) y <= x``, [thm_YO]),
    (``min (x:real) y <= y``, [thm_YO]),
    (``(z:real) < x /\ z < y ==> z < min x y``, [thm_YO]),
    (``min (x:real) y < x``, [fail_YO, fail_YSO, fail_CVC]),
    (``min (x:real) 0 = 0``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:real) >= 0 ==> (min x 0 = 0)``, [thm_YO]),

    (``max (x:real) y >= x``, [thm_YO]),
    (``max (x:real) y >= y``, [thm_YO]),
    (``(z:real) > x /\ z > y ==> z > max x y``, [thm_YO]),
    (``max (x:real) y > x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:real) >= 0 ==> (max x 0 = x)``, [thm_YO]),

    (* arithmetic inequalities: <, <=, >, >= *)

    (* num *)

    (``0n < 1n``, [thm_YO]),
    (``1n < 0n``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:num) < x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:num) < y ==> 42 * x < 42 * y``, [thm_YO]),

    (``0n <= 1n``, [thm_YO]),
    (``1n <= 0n``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:num) <= x``, [thm_YO]),
    (``(x:num) <= y ==> 42 * x <= 42 * y``, [thm_YO]),

    (``1n > 0n``, [thm_YO]),
    (``0n > 1n``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:num) > x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:num) > y ==> 42 * x > 42 * y``, [thm_YO]),

    (``1n >= 0n``, [thm_YO]),
    (``0n >= 1n``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:num) >= x``, [thm_YO]),
    (``(x:num) >= y ==> 42 * x >= 42 * y``, [thm_YO]),

    (``((x:num) < y) = (y > x)``, [thm_YO]),
    (``((x:num) <= y) = (y >= x)``, [thm_YO]),
    (``(x:num) < y /\ y <= z ==> x < z``, [thm_YO]),
    (``(x:num) <= y /\ y <= z ==> x <= z``, [thm_YO]),
    (``(x:num) > y /\ y >= z ==> x > z``, [thm_YO]),
    (``(x:num) >= y /\ y >= z ==> x >= z``, [thm_YO]),

    (``(x:num) >= 0``, [thm_YO]),
    (``0 < (x:num) /\ x <= 1 ==> (x = 1)``, [thm_YO]),

    (* int *)

    (``0i < 1i``, [thm_YO, thm_YSO, thm_CVC]),
    (``1i < 0i``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:int) < x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:int) < y ==> 42 * x < 42 * y``, [thm_YO, thm_YSO, thm_CVC]),

    (``0i <= 1i``, [thm_YO, thm_YSO, thm_CVC]),
    (``1i <= 0i``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:int) <= x``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x:int) <= y ==> 42 * x <= 42 * y``, [thm_YO, thm_YSO, thm_CVC]),

    (``1i > 0i``, [thm_YO, thm_YSO, thm_CVC]),
    (``0i > 1i``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:int) > x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:int) > y ==> 42 * x > 42 * y``, [thm_YO, thm_YSO, thm_CVC]),

    (``1i >= 0i``, [thm_YO, thm_YSO, thm_CVC]),
    (``0i >= 1i``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:int) >= x``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x:int) >= y ==> 42 * x >= 42 * y``, [thm_YO, thm_YSO, thm_CVC]),

    (``((x:int) < y) = (y > x)``, [thm_YO, thm_YSO, thm_CVC]),
    (``((x:int) <= y) = (y >= x)``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x:int) < y /\ y <= z ==> x < z``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x:int) <= y /\ y <= z ==> x <= z``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x:int) > y /\ y >= z ==> x > z``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x:int) >= y /\ y >= z ==> x >= z``, [thm_YO, thm_YSO, thm_CVC]),

    (``(x:int) >= 0``, [fail_YO, fail_YSO, fail_CVC]),
    (``0 < (x:int) /\ x <= 1 ==> (x = 1)``, [thm_YO, thm_YSO, thm_CVC]),

    (* real *)

    (``0r < 1r``, [thm_YO]),
    (``1r < 0r``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:real) < x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:real) < y ==> 42 * x < 42 * y``, [thm_YO]),

    (``0n <= 1n``, [thm_YO]),
    (``1n <= 0n``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:num) <= x``, [thm_YO]),
    (``(x:num) <= y ==> 2 * x <= 2 * y``, [thm_YO]),

    (``1r > 0r``, [thm_YO]),
    (``0r > 1r``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:real) > x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:real) > y ==> 42 * x > 42 * y``, [thm_YO]),

    (``1r >= 0r``, [thm_YO]),
    (``0r >= 1r``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:real) >= x``, [thm_YO]),
    (``(x:real) >= y ==> 42 * x >= 42 * y``, [thm_YO]),

    (``((x:real) < y) = (y > x)``, [thm_YO]),
    (``((x:real) <= y) = (y >= x)``, [thm_YO]),
    (``(x:real) < y /\ y <= z ==> x < z``, [thm_YO]),
    (``(x:real) <= y /\ y <= z ==> x <= z``, [thm_YO]),
    (``(x:real) > y /\ y >= z ==> x > z``, [thm_YO]),
    (``(x:real) >= y /\ y >= z ==> x >= z``, [thm_YO]),

    (``(x:real) >= 0``, [fail_YO, fail_YSO, fail_CVC]),
    (``0 < (x:real) /\ x <= 1 ==> (x = 1)``, [fail_YO, fail_YSO, fail_CVC]),

    (* uninterpreted functions *)

    (``(x = y) ==> (f x = f y)``, [thm_YO, thm_YSO, thm_CVC]),
    (``(x = y) ==> (f x y = f y x)``, [thm_YO, thm_YSO, thm_CVC]),
    (``(f (f x) = x) /\ (f (f (f (f (f x)))) = x) ==> (f x = x)``,
      [thm_YO, thm_YSO, thm_CVC]),
    (``(f x = f y) ==> (x = y)``, [fail_YO, fail_YSO, fail_CVC]),

    (* predicates *)

    (``P x ==> P x``, [thm_YO, thm_YSO, thm_CVC]),
    (``P x ==> Q x``, [fail_YO, fail_YSO, fail_CVC]),
    (``P x ==> P y``, [fail_YO, fail_YSO, fail_CVC]),
    (``P x y ==> P x x``, [fail_YO, fail_YSO, fail_CVC]),
    (``P x y ==> P y x``, [fail_YO, fail_YSO, fail_CVC]),
    (``P x y ==> P y y``, [fail_YO, fail_YSO, fail_CVC]),

    (* quantifiers *)

    (``!x. x = x``, [thm_YO, thm_YSO, thm_CVC]),
    (* Yices 1.0.18 fails to decide this one
    ``?x. x = x``
    *)
    (``(?y. !x. P x y) ==> (!x. ?y. P x y)``, [thm_YO]),
    (* Yices 1.0.18 fails to decide this one
    ``(!x. ?y. P x y) ==> (?y. !x. P x y)``
    *)
    (``(?x. P x) ==> !x. P x``, [fail_YO, fail_YSO, fail_CVC]),
    (``?x. P x ==> !x. P x``, [thm_YO, thm_YSO, thm_CVC]),

    (* lambda abstractions *)

    (``(\x. x) = (\y. y)``, [thm_YO, thm_YSO, thm_CVC]),
    (``(\x. \x. x) x x = (\y. \y. y) y x``, [thm_YO, thm_YSO, thm_CVC]),
    (``(\x. x (\x. x)) = (\y. y (\x. x))``, [thm_YO, thm_YSO, thm_CVC]),
    (* Yices 1.0.18 fails to decide this one
    ``(\x. x (\x. x)) = (\y. y x)``
    *)
    (``f x = (\x. f x) x``, [thm_YO, thm_YSO, thm_CVC]),
    (``f x = (\y. f y) x``, [thm_YO, thm_YSO, thm_CVC]),

    (* tuples, FST, SND *)

    (``(x, y) = (x, z)``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x, y) = (z, y)``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x, y) = (y, x)``, [fail_YO, fail_YSO, fail_CVC]),
    (``((x, y) = (y, x)) = (x = y)``, [thm_YO]),
    (``((x, y, z) = (y, z, x)) = (x = y) /\ (y = z)``, [thm_YO]),
    (``((x, y) = (u, v)) = (x = u) /\ (y = v)``, [thm_YO]),

    (``y = FST (x, y)``, [fail_YO, fail_YSO, fail_CVC]),
    (``x = FST (x, y)``, [thm_YO]),
    (``(FST (x, y, z) = FST (u, v, w)) = (x = u)``, [thm_YO]),
    (``(FST (x, y, z) = FST (u, v, w)) = (x = u) /\ (y = w)``,
      [fail_YO, fail_YSO, fail_CVC]),

    (``y = SND (x, y)``, [thm_YO]),
    (``x = SND (x, y)``, [fail_YO, fail_YSO, fail_CVC]),
    (``(SND (x, y, z) = SND (u, v, w)) = (y = v)``,
       [fail_YO, fail_YSO, fail_CVC]),
    (``(SND (x, y, z) = SND (u, v, w)) = (z = w)``,
       [fail_YO, fail_YSO, fail_CVC]),
    (``(SND (x, y, z) = SND (u, v, w)) = (y = v) /\ (z = w)``, [thm_YO]),

    (``(FST (x, y) = SND (x, y)) = (x = y)``, [thm_YO]),
    (``(FST p = SND p) = (p = (SND p, FST p))``, [thm_YO]),
    (``((\p. FST p) (x, y)= (\p. SND p) (x, y)) = (x = y)``, [thm_YO]),

    (* words (i.e., bit vectors) *)

    (``!x. x:word2 = x``, [thm_YO]),
    (``!x. x:word3 = x``, [thm_YO]),
    (``!x. x:word4 = x``, [thm_YO]),
    (``!x. x:word5 = x``, [thm_YO]),
    (``!x. x:word6 = x``, [thm_YO]),
    (``!x. x:word7 = x``, [thm_YO]),
    (``!x. x:word8 = x``, [thm_YO]),
    (``!x. x:word12 = x``, [thm_YO]),
    (``!x. x:word16 = x``, [thm_YO]),
    (``!x. x:word20 = x``, [thm_YO]),
    (``!x. x:word24 = x``, [thm_YO]),
    (``!x. x:word28 = x``, [thm_YO]),
    (``!x. x:word30 = x``, [thm_YO]),
    (``!x. x:word32 = x``, [thm_YO]),
    (``!x. x:word64 = x``, [thm_YO]),

    (``x:word32 && x = x``, [thm_YO]),
    (``x:word32 && y = y && x``, [thm_YO]),
    (``(x:word32 && y) && z = x && (y && z)``, [thm_YO]),
    (``x:word32 && 0w = 0w``, [thm_YO]),
    (``x:word32 && 0w = x``, [fail_YO, fail_YSO, fail_CVC]),

    (``x:word32 !! x = x``, [thm_YO]),
    (``x:word32 !! y = y !! x``, [thm_YO]),
    (``(x:word32 !! y) !! z = x !! (y !! z)``, [thm_YO]),
    (``x:word32 !! 0w = 0w``, [fail_YO, fail_YSO, fail_CVC]),
    (``x:word32 !! 0w = x``, [thm_YO]),

    (``x:word32 ?? x = 0w``, [thm_YO]),
    (``x:word32 ?? y = y ?? x``, [thm_YO]),
    (``(x:word32 ?? y) ?? z = x ?? (y ?? z)``, [thm_YO]),
    (``x:word32 ?? 0w = 0w``, [fail_YO, fail_YSO, fail_CVC]),
    (``x:word32 ?? 0w = x``, [thm_YO]),

    (``~ ~ x:word32 = x``, [thm_YO]),
    (``~ 0w = 0w:word32``, [fail_YO, fail_YSO, fail_CVC]),

    (``x:word32 << 0 = x``, [thm_YO]),
    (``x:word32 << 31 = 0w``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:word32 << 31 = 0w) \/ (x << 31 = 1w << 31)``, [thm_YO]),

    (* shift index greater than bit width: not allowed by Yices, and not
       handled by the translation yet
    ``x:word32 << 42 = x``
    *)
    (* shift index not a number: not allowed by Yices; we should test for this
       when translating
    ``x:word32 << n = x``
    *)

    (``x:word32 >>> 0 = x``, [thm_YO]),
    (``x:word32 >>> 31 = 0w``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:word32 >>> 31 = 0w) \/ (x >>> 31 = 1w)``, [thm_YO]),

    (``1w:word2 @@ 1w:word2 = 5w:word4``, [thm_YO]),
    (``((x @@ y):word32 = y @@ x) = (x:word16 = y)``, [thm_YO]),

    (``(31 >< 0) x:word32 = x``, [thm_YO]),
    (``(1 >< 0) (0w:word32) = 0w:word2``, [thm_YO]),

    (``(x:word2 = y) = (x ' 0 = y ' 0) /\ (x ' 1 = y ' 1)``, [thm_YO]),

    (``0w:word32 = w2w (0w:word16)``, [thm_YO]),
    (``0w:word32 = w2w (0w:word32)``, [thm_YO]),
    (``0w:word32 = w2w (0w:word64)``, [thm_YO]),
    (``x:word32 = w2w x``, [thm_YO]),

    (``(x:word32) + x = x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:word32) + y = y + x``, [thm_YO]),
    (``((x:word32) + y) + z = x + (y + z)``, [thm_YO]),
    (``(x:word32) + 0w = 0w``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:word32) + 0w = x``, [thm_YO]),

    (``(x:word32) - x = x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:word32) - x = 0w``, [thm_YO]),
    (``(x:word32) - y = y - x``, [fail_YO, fail_YSO, fail_CVC]),
    (``((x:word32) - y) - z = x - (y - z)``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:word32) - 0w = 0w``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:word32) - 0w = x``, [thm_YO]),

    (``(x:word32) * x = x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:word32) * y = y * x``, [thm_YO]),
    (``((x:word32) * y) * z = x * (y * z)``, [thm_YO]),
    (``(x:word32) * 0w = 0w``, [thm_YO]),
    (``(x:word32) * 0w = x``, [fail_YO, fail_YSO, fail_CVC]),
    (``(x:word32) * 1w = x``, [thm_YO]),

    (``- (x:word32) = x``, [fail_YO, fail_YSO, fail_CVC]),
    (``- 0w = 0w:word32``, [thm_YO]),
    (``- - (x:word32) = x``, [thm_YO]),

    (``0w < 1w:word32``, [thm_YO]),
    (``~ 0w < 0w:word32``, [thm_YO]),

    (``0w <= 1w:word32``, [thm_YO]),
    (``x <= y:word32 = x < y \/ (x = y)``, [thm_YO]),
    (``~ 0w <= 0w:word32``, [thm_YO]),

    (``1w > 0w:word32``, [thm_YO]),
    (``0w > ~ 0w:word32``, [thm_YO]),

    (``1w >= 0w:word32``, [thm_YO]),
    (``x >= y:word32 = x > y \/ (x = y)``, [thm_YO]),
    (``0w >= ~ 0w:word32``, [thm_YO]),

    (``0w <+ 1w:word32``, [thm_YO]),
    (``0w <+ ~ 0w:word32``, [thm_YO]),

    (``0w <=+ 1w:word32``, [thm_YO]),
    (``x <=+ y:word32 = x <+ y \/ (x = y)``, [thm_YO]),
    (``0w <=+ ~ 0w:word32``, [thm_YO]),

    (``1w >+ 0w:word32``, [thm_YO]),
    (``~ 0w >+ 0w:word32``, [thm_YO]),

    (``1w >=+ 0w:word32``, [thm_YO]),
    (``x >=+ y:word32 = x >+ y \/ (x = y)``, [thm_YO]),
    (``~ 0w >=+ 0w:word32``, [thm_YO]),

    (* from Magnus Myreen *)
    (``!(a:word32) b.
     (((word_msb (a - b) <=>
        (word_msb a <=/=> word_msb b) /\
        (word_msb a <=/=> word_msb (a - b))) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb b <=/=> word_msb a) /\
        (word_msb a <=/=> word_msb (a - b))) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb a <=/=> word_msb b) /\
        (word_msb (a - b) <=/=> word_msb a)) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb b <=/=> word_msb a) /\
        (word_msb (a - b) <=/=> word_msb a)) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb a <=/=> word_msb (a - b)) /\
        (word_msb a <=/=> word_msb b)) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb a <=/=> word_msb (a - b)) /\
        (word_msb b <=/=> word_msb a)) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb (a - b) <=/=> word_msb a) /\
        (word_msb a <=/=> word_msb b)) <=> b <= a) /\
      ((word_msb (a - b) <=>
        (word_msb (a - b) <=/=> word_msb a) /\
        (word_msb b <=/=> word_msb a)) <=> b <= a) /\
      (((word_msb a <=/=> word_msb b) /\
        (word_msb a <=/=> word_msb (a - b)) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb b <=/=> word_msb a) /\
        (word_msb a <=/=> word_msb (a - b)) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb a <=/=> word_msb b) /\
        (word_msb (a - b) <=/=> word_msb a) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb b <=/=> word_msb a) /\
        (word_msb (a - b) <=/=> word_msb a) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb a <=/=> word_msb (a - b)) /\
        (word_msb a <=/=> word_msb b) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb a <=/=> word_msb (a - b)) /\
        (word_msb b <=/=> word_msb a) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb (a - b) <=/=> word_msb a) /\
        (word_msb a <=/=> word_msb b) <=> word_msb (a - b)) <=>
       b <= a) /\
      (((word_msb (a - b) <=/=> word_msb a) /\
        (word_msb b <=/=> word_msb a) <=> word_msb (a - b)) <=>
       b <= a)) /\ (a >= b <=> b <= a) /\ (a > b <=> b < a) /\
     (~(a <=+ b) <=> b <+ a) /\ (~(a <+ b) <=> b <=+ a) /\
     (a <+ b \/ (a = b) <=> a <=+ b) /\ (~(a < b) <=> b <= a) /\
     (~(a <= b) <=> b < a) /\ (a < b \/ (a = b) <=> a <= b) /\
     ((a = b) \/ a < b <=> a <= b) /\ (a <+ b \/ (a = b) <=> a <=+ b) /\
     ((a = b) \/ a <+ b <=> a <=+ b) /\
     (b <=+ a /\ a <> b <=> b <+ a) /\ (a <> b /\ b <=+ a <=> b <+ a) /\
     (b <= a /\ a <> b <=> b < a) /\ (a <> b /\ b <= a <=> b < a) /\
     (((v:word32) - w = 0w) <=> (v = w)) /\ (w - 0w = w)``, [thm_YO])

  ]  (* tests *)
end

(*****************************************************************************)
(* actually perform tests                                                    *)
(*****************************************************************************)

val _ = map (fn (term, test_funs) =>
               map (fn test_fun => test_fun term) test_funs) tests

(*****************************************************************************)

val _ = print " done, all tests successful.\n"

val _ = OS.Process.exit OS.Process.success
