open HolKernel boolLib simpLib Parse realSimps

val _ = set_trace "Unicode" 0

val s = SIMP_CONV (bossLib.std_ss ++ REAL_REDUCE_ss) []

fun test (problem, result) = let
  val padr = StringCvt.padRight #" "
  val padl = StringCvt.padLeft #" "
  val p_s = padr 30 (term_to_string problem)
  val r_s = padl 10 (term_to_string result)
  val _ = print p_s
  val th = QCONV s problem
  val answer = rhs (concl th)
  val verdict = if aconv answer result then ("OK", true)
                else ("FAILED!", false)
in
  print (" = " ^ r_s);
  print (padl 10 (#1 verdict) ^ "\n");
  #2 verdict
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
             (``1r - 0``, ``1r``)]

val _ = Process.exit (if List.all test tests then Process.success
                      else Process.failure)
