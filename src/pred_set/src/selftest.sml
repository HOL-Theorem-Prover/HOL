open HolKernel boolLib Parse PFset_conv


val padr = StringCvt.padRight #" "
val padl = StringCvt.padLeft #" "

val s = IMAGE_CONV computeLib.EVAL_CONV NO_CONV

fun test (problem, result) = let
  val p_s = padr 30 (term_to_string problem)
  val r_s = padl 10 (term_to_string result)
  val _ = print p_s
  val th = QCONV s problem
  val answer = rhs (concl th)
  val verdict = if aconv answer result then ("OK", true)
                else ("FAILED!", false)
in
  print (" = " ^ r_s);
  print (padl 19 (#1 verdict) ^ "\n");
  #2 verdict
end;

val tests = [(``IMAGE (\x. x + 1) {3;4}``, ``{4;5}``),
             (``IMAGE (K 0) {3;4}``, ``{0}``),
             (``IMAGE (\x. x MOD 8) {11;22}``, ``{3;6}``)]

fun testpp desired = let
  val t = Parse.Term [QUOTE desired]
  val _ = print (padr 60 ("Testing pretty-printing of "^desired))
  val s = term_to_string t
in
  if s = desired then print "OK\n"
  else (print "FAILED\n"; Process.exit Process.failure)
end

val _ =
    app testpp ["{x | x < 10}",
                "{x | x < 10} y",
                "{x + y | x < y}",
                "{x + y | x > 6}",
                "{x + y | x | x < y}"]

val _ = Process.exit (if List.all test tests then Process.success
                      else Process.failure)
