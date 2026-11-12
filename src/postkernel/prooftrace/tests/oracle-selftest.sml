val () = load_pft ["PFTReader","PFTReplay"];
val () = use (test_source ^ "oracle-check-results.sml");
val () = if identity_phase <> "replay" then () else let
  val () = PFTEmit.emit_theory
    {trace=Systeml.HOLDIR ^ "/src/bool/.hol/objs/boolTheory.tr.gz",
     output="hol4/bool.pft.bin",ruleset=PFTEmit.HOL4}
  val db = List.foldl (fn (file,db) => PFTReplay.replay db file)
    PFTReplay.empty_trDB ["hol4/bool.pft.bin","oracle_hyps.pft.bin",
                        "oracle_retired_instance.hol4.pft"]
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

fun retired_fixture (name,first_generic) = let
  val () = Theory.new_theory name
  val () = Theory.new_constant("c",Type.alpha --> Type.alpha)
  val c = Term.prim_mk_const {Thy=name,Name="c"}
  val cb = Term.inst [Type.alpha |-> Type.bool] c
  val cf = Term.inst [Type.alpha |-> (Type.bool --> Type.bool)] c
  val (first,second) = if first_generic then (c,cb) else (cb,cf)
  val result = Thm.CONJUNCT2 (Thm.CONJ (Thm.REFL first)
    (Thm.CONJUNCT2 (Thm.CONJ (Thm.REFL second) (Thm.REFL boolSyntax.T))))
  val () = Term.prim_delete_const {Thy=name,Name="c"}
  val () = save "RESULT" result
in Theory.export_theory () end;

val () = retired_fixture ("oracle_retired_poly",false);
val () = retired_fixture ("oracle_retired_instance",true);
val () = List.app (fn (label,ruleset) => let
  val output = "oracle_retired_poly." ^ label ^ ".rejected"
  val rejected =
    (PFTEmit.emit_theory
       {trace=".hol/objs/oracle_retired_polyTheory.tr.gz",
        output=output,ruleset=ruleset}; false)
    handle Fail message =>
      if String.isSubstring "PFTEmit: retired undefined constant " message
         andalso String.isSubstring "oracle_retired_poly$" message
         andalso String.isSubstring
           "its generic declaration type is unavailable" message
      then (print (message ^ "\n"); true) else raise Fail message
  val () = if rejected then OS.FileSys.remove output
           else raise Fail "incompatible retired constant was accepted"
  val () = PFTEmit.emit_theory
    {trace=".hol/objs/oracle_retired_instanceTheory.tr.gz",
     output="oracle_retired_instance." ^ label ^ ".pft",ruleset=ruleset}
in print ("PFT_RETIRED_TYPE_CHECK_PASS " ^ label ^ "\n") end)
  [("hol4",PFTEmit.HOL4),("candle",PFTEmit.Candle)];
val () = print "PFT_ORACLE_SELFTEST_PASSED\n";
