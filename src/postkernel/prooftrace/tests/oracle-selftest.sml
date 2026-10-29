open HolKernel;
val () = Theory.new_theory "oracle_hyps";

val p = Term.mk_var ("p", Type.bool);
val q = Term.mk_var ("q", Type.bool);
val r = Term.mk_var ("r", Type.bool);
fun oracle sequent = Thm.mk_oracle_thm "PFT_ORACLE_REGRESSION" sequent;
fun save name th = ignore (Theory.save_thm (name, th));

val () = save "hyps" (oracle ([q, r], p));
val () = Theory.export_theory ();

val () = Theory.new_theory "deduct_antisym";
val () = save "deduct" (Thm.deductAntisym
  (oracle ([q, r], p)) (oracle ([p], q)));
val () = Theory.export_theory ();
val () = print "PFT_ORACLE_FIXTURES_PRODUCED\n";

val () = load_pft ["PFTReader","PFTReplay"];
val () = use (test_source ^ "oracle-check-results.sml");

val separate = "oracle_hyps.pft.bin";
val () = PFTEmit.emit_theory
  {trace=".hol/objs/oracle_hypsTheory.tr.gz", output=separate,
   ruleset=PFTEmit.HOL4};
val () = check_oracle_results
  (PFTReplay.replay PFTReplay.empty_trDB separate);
val unsupported = "deduct_unsupported.pft.bin";
val rejected = (PFTEmit.emit_theory
  {trace=".hol/objs/deduct_antisymTheory.tr.gz", output=unsupported,
   ruleset=PFTEmit.HOL4}; false)
  handle Fail msg => msg = "PFTEmit: HOL4 deductAntisym replay unsupported";
val () = if rejected then ()
  else raise Fail "HOL4 export accepted unsupported deductAntisym";
val () = List.app OS.FileSys.remove [separate, unsupported];
val () = print "PFT_ORACLE_SELFTEST_PASSED\n";
