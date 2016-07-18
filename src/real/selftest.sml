open HolKernel boolLib simpLib Parse realSimps

open testutils

val _ = set_trace "Unicode" 0

val s = SIMP_CONV (bossLib.std_ss ++ REAL_REDUCE_ss) []

fun test (problem, result) = let
  val padr = StringCvt.padRight #" "
  val padl = StringCvt.padLeft #" "
  val p_s = padr 30 (term_to_string problem)
  val r_s = padl 10 (term_to_string result)
  val _ = tprint (p_s ^ " = " ^ r_s)
  val th = QCONV s problem
  val answer = rhs (concl th)
in
  if aconv answer result then OK()
  else die ("FAILED!\n  Got "^term_to_string answer)
end;

val tests = [(``~~3r``, ``3r``),
             (``3r + 4``, ``7r``),
             (``3 - 4r``, ``~1r``),
             (``abs (~20r)``, ``20r``),
             (``abs (1/6)``, ``1/6``),
             (``abs (~3/6)``, ``1/2``),
             (``abs 0``, ``0``),
             (``3r * 3/4``, ``9/4``),
             (``6/~8``, ``~3/4``),
             (``1/3 + 1/2``, ``5/6``),
             (``1/2 = 0``, ``F``),
             (``0 + 3r``, ``3r``),
             (``3r * 0``, ``0r``),
             (``~0r``, ``0r``),
             (``1r - 0``, ``1r``),
             (``1 / 10 + 0r``, ``1r/10``),
             (``0r + 1 / 10``, ``1r/10``),
             (``1/2 * 0r``, ``0r``),
             (``0r * 1/2``, ``0r``)]

val _ = List.app test tests

val _ = Process.exit Process.success
