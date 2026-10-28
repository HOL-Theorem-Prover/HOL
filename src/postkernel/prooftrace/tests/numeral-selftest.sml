open HolKernel;
val () = load "cv_computeLib";
val () = Theory.new_theory "compute_numerals";

fun check (name, numeral) = let
  val input = Parse.Term [QUOTE
    ("cv_add (cv$Num " ^ numeral ^ ") (cv$Num 0)")]
  val expected = Parse.Term [QUOTE ("cv$Num " ^ numeral)]
  val th = cv_computeLib.cv_compute [] input
  val () = if null (Thm.hyp th) andalso
              Term.aconv (Thm.concl th) (boolSyntax.mk_eq(input,expected))
           then () else raise Fail ("wrong compute sequent: " ^ name)
in ignore (Theory.save_thm (name,th)) end;

val () = List.app check
  [("small", "2"),
   ("cached_limit", "255"),
   ("uncached", "256"),
   ("large_odd", "18446744073709551615"),
   ("large_even", "18446744073709551616"),
   ("large_256", "115792089237316195423570985008687907853" ^
     "269984665640564039457584007913129639936")];
val () = Theory.export_theory ();
val () = print "COMPUTE_NUMERALS_PRODUCED\n";

val () = load_pft [];
val () = PFTEmit.emit_expect := true;
val () = List.app (fn (name,ruleset) => (
  PFTEmit.emit_theory
    {trace=".hol/objs/compute_numeralsTheory.tr.gz",
     output="compute_numerals." ^ name ^ ".pft",ruleset=ruleset};
  print ("PASS arbitrary-precision compute numerals convert to " ^ name ^
         "\n"))) [("hol4",PFTEmit.HOL4),("candle",PFTEmit.Candle)];
