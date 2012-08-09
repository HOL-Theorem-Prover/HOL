open HolKernel boolLib Parse PFset_conv
open pred_setSimps

val _ = set_trace "Unicode" 0
val padr = StringCvt.padRight #" "
val padl = StringCvt.padLeft #" "

fun test s (problem, result) = let
  val p_s = padr 30 (term_to_string problem)
  val r_s = padl 15 (term_to_string result)
  val _ = print p_s
  val th = QCONV s problem
  val answer = rhs (concl th)
  val verdict = if aconv answer result then ("OK", true)
                else ("FAILED!", false)
in
  print (padr 35 (" = " ^ r_s));
  print (#1 verdict ^ "\n");
  #2 verdict
end;


fun testpp desired = let
  val t = Parse.Term [QUOTE desired]
  val _ = print (padr 65 ("Pretty-printing of "^desired))
  val s = term_to_string t
in
  if s = desired then print "OK\n"
  else (print "FAILED\n"; Process.exit Process.failure)
end

val _ =
    app testpp ["{}",
                "0",
                "{x | x < 10}",
                "{x | x < 10} y",
                "{x + y | x < y}",
                "{x + y | x > 6}",
                "{x + y | x | x < y}",
                "{(case x of T => y | F => y + 1) | y > 3}",
                "{x | x < (case y of T => 3 | F => 2)}"]

val _ = temp_add_rule {
          fixity = Closefix,
          term_name = "lterange",
          block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
          paren_style = OnlyIfNecessary,
          pp_elements = [TOK "{", HardSpace 1, TM, BreakSpace(1,0),
                         TOK "<..", BreakSpace(1,0), TM, HardSpace 1,
                         TOK "}"]}
val _ = temp_overload_on ("lterange", ``\m n. { i | m < i /\ i <= n}``)

val _ = app testpp ["{ 3 <.. 5 }", "{x | x < 6}"]

val imgtests = [(``IMAGE (\x. x + 1) {3;4}``, ``{4;5}``),
                (``IMAGE (K 0) {3;4}``, ``{0}``),
                (``IMAGE (\x. x MOD 8) {11;22}``, ``{3;6}``)]

val gspec_simp_tests =
    [(``{x:num | T}``, ``univ(:num)``),
     (``{x:num | F}``, ``{}:num set``),
     (``{x + y | F}``, ``{}:num set``),
     (``{(x:num,y:bool) | F}``, ``{}:(num#bool) set``),
     (``{x + y | x | F}``, ``{}:num set``)]

val _ = let
  open Systeml OS.Path
in
  print "Testing loads with Unicode trace off\n";
  if OS.Process.isSuccess
         (Systeml.system_ps
              (String.concatWith " "
                   [Systeml.protect
                        (concat(HOLDIR,concat("bin", "hol.bare"))),
                    "<", "testscript.ML"]))
  then print "** OK\n"
  else (print "** FAILED!\n";
        OS.Process.exit OS.Process.failure)
end

val _ =
    Process.exit
        (if
           List.all (test (IMAGE_CONV computeLib.EVAL_CONV NO_CONV)) imgtests
           andalso
           List.all (test GSPEC_SIMP_CONV) gspec_simp_tests
         then Process.success
         else Process.failure)
