val () = load_pft ["PFTReader","PFTReplay"];
val () = use (test_source ^ "oracle-check-results.sml");
val () = if identity_phase <> "replay" then () else let
  val db = PFTReplay.replay PFTReplay.empty_trDB "oracle_hyps.pft.bin"
  val () = check_oracle_results db
in print "PFT_TEST_PHASE_PASS\n"; OS.Process.exit OS.Process.success end;

open HolKernel;
val () = Theory.new_theory "oracle_hyps";

val p = Term.mk_var ("p", Type.bool);
val q = Term.mk_var ("q", Type.bool);
val r = Term.mk_var ("r", Type.bool);
fun oracle sequent = Thm.mk_oracle_thm "PFT_ORACLE_REGRESSION" sequent;
fun save name th = ignore (Theory.save_thm (name, th));

val () = save "hyps" (oracle ([q, r], p));
val x = Term.mk_var("x",Type.bool);
val y = Term.mk_var("y",Type.bool);
val synthetic = Term.mk_var("x pft%0",Type.bool);
val body = boolSyntax.mk_eq(x,synthetic);
val abstraction = Term.rename_bvar "x" (Term.mk_abs(y,body));
val () = save "capture" (oracle ([],boolSyntax.mk_eq(abstraction,abstraction)));
val () = Theory.new_constant("c",Type.alpha --> Type.alpha);
val c = Term.prim_mk_const {Thy="oracle_hyps",Name="c"};
val cb = Term.inst [Type.alpha |-> Type.bool] c;
val cf = Term.inst [Type.alpha |-> (Type.bool --> Type.bool)] c;
val () = save "POLY_BOOL" (Thm.REFL cb);
val () = save "POLY_FUN" (Thm.REFL cf);
val () = Theory.export_theory ();

val () = print "PFT_ORACLE_FIXTURES_PRODUCED\n";

val separate = "oracle_hyps.pft.bin";
val () = PFTEmit.emit_theory
  {trace=".hol/objs/oracle_hypsTheory.tr.gz", output=separate,
   ruleset=PFTEmit.HOL4};
val () = PFTEmit.emit_theory
  {trace=".hol/objs/oracle_hypsTheory.tr.gz",
   output="oracle_hyps.candle.pft.bin",ruleset=PFTEmit.Candle};
val () = print "PFT_ORACLE_SELFTEST_PASSED\n";
