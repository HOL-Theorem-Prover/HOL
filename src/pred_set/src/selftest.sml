open HolKernel boolLib Parse PFset_conv

val s = IMAGE_CONV computeLib.EVAL_CONV NO_CONV

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

val tests = [(``IMAGE (\x. x + 1) {3;4}``, ``{4;5}``),
             (``IMAGE (K 0) {3;4}``, ``{0}``),
             (``IMAGE (\x. x MOD 8) {11;22}``, ``{3;6}``)]

val _ = Process.exit (if List.all test tests then Process.success
                      else Process.failure)
