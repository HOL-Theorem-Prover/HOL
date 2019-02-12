open HolKernel boolLib Parse PFset_conv
open pred_setSimps

val _ = let
  open testutils
in
  tpp_expected {testf = standard_tpp_message, input = "UNIV 3",
                output = UnicodeChars.universal_set ^ "(:num) 3"}
end

val _ = set_trace "Unicode" 0
val padr = StringCvt.padRight #" "
val padl = StringCvt.padLeft #" "

fun test s (problem, result) = let
  open testutils
  val p_s = padr 30 (term_to_string problem)
  val r_s = padl 15 (term_to_string result)
  val _ = tprint (p_s ^ " = " ^ r_s)
  val th = QCONV s problem
  val answer = rhs (concl th)
in
  if aconv answer result then OK()
  else die "FAILED!";
  true
end;

val tpp_cases = [
      "{}",
      "{1; 2}",
      "{} 2",
      "{1; 2} 3",
      "0",
      "{x | x < 10}",
      "{x | x < 10} y",
      "{x + y | x < y}",
      "{x + y | x > 6}",
      "{x + y | x | x < y}",
      "{(case x of 0 => y | SUC n => y + n) | y > 3}",
      "{x | x < (case y of 0 => 3 | SUC n => 2)}",
      "univ(:'a)",
      "univ(:num)",
      "univ(:num) x",
      "{longfunctionname longarg1 longarg2 longarg3 |\n\
      \ longarg1 * longconstantfactor + longarg2 < longarg3}",
      "{longfunctionname longarg1 longarg2 longarg3 |\n\
      \ longarg2 |\n\
      \ longarg1 * longconstantfactor + longarg2 < longarg3}"
    ]

val _ = app testutils.tpp tpp_cases

val _ = (trace ("Univ pretty-printing", 0) testutils.tpp) "UNIV"

val _ = temp_add_rule {
          fixity = Closefix,
          term_name = "lterange",
          block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
          paren_style = OnlyIfNecessary,
          pp_elements = [TOK "{", HardSpace 1, TM, BreakSpace(1,0),
                         TOK "<..", BreakSpace(1,0), TM, HardSpace 1,
                         TOK "}"]}

val _ = temp_add_user_printer(
  "",``{ i | m < i /\ i <= n}``, term_pp_types.dummyprinter
)
val _ = temp_overload_on ("lterange", ``\m n. { i | m < i /\ i <= n}``)

val _ = app testutils.tpp ["{ 3 <.. 5 }", "{x | x < 6}"]

val imgtests = [(``IMAGE (\x. x + 1) {3;4}``, ``{4;5}``),
                (``IMAGE (K 0) {3;4}``, ``{0}``),
                (``IMAGE (\x. x MOD 8) {11;22}``, ``{3;6}``)]

val gspec_simp_tests =
    [(``{x:num | T}``, ``univ(:num)``),
     (``{x:num | F}``, ``{}:num set``),
     (``{x + y | F}``, ``{}:num set``),
     (``{(x:num,y:bool) | F}``, ``{}:(num#bool) set``),
     (``{x + y | x | F}``, ``{}:num set``)]

val max_set_tests =
    [(``MAX_SET {}``, ``0n``),
     (``MAX_SET {1}``, ``1n``),
     (``MAX_SET {1;2}``, ``2n``),
     (``MAX_SET {2;1}``, ``2n``),
     (``MAX_SET {2;4;3}``, ``4n``)]


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

val feq_def = new_definition("feq_def", ``feq f x y = (f x = f y)``);
val _ = temp_overload_on("equiv_class", ``\R s x. {y | y IN s /\ R x y}``);
val _ = add_user_printer ("",``{y | y IN s /\ R x y}``)
val _ = testutils.tpp "equiv_class (feq f) s x"

val _ = set_grammar_ancestry ["pred_set"]
val _ = print "Setting grammar ancestry to be [\"pred_set\"]\n"
val _ = set_trace "PP.avoid_unicode" 1
val _ = List.app testutils.tpp tpp_cases

val _ =
    Process.exit
        (if
           List.all (test (IMAGE_CONV computeLib.EVAL_CONV NO_CONV)) imgtests
           andalso
           List.all (test GSPEC_SIMP_CONV) gspec_simp_tests
           andalso
           List.all (test MAX_SET_CONV) max_set_tests
         then Process.success
         else Process.failure)
