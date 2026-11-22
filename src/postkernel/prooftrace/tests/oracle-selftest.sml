val () = if phase <> "replay" andalso phase <> "merged" then () else
  (check_oracle_results
     (if phase = "merged" then replay ["oracle_merged.hol4.pft"]
      else replay_bool
        ["oracle_hyps.hol4.pft","oracle_retired_instance.hol4.pft"]);
   pass ());

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
val () = save "capture" (oracle ([boolSyntax.mk_eq(abstraction,abstraction)],p));
val () = Theory.new_constant("c",Type.alpha --> Type.alpha);
val c = Term.prim_mk_const {Thy="oracle_hyps",Name="c"};
val cb = Term.inst [Type.alpha |-> Type.bool] c;
val cf = Term.inst [Type.alpha |-> (Type.bool --> Type.bool)] c;
val () = save "POLY_BOOL" (Thm.REFL cb);
val () = save "POLY_FUN" (Thm.REFL cf);
val () = Theory.export_theory ();

val () = print "PFT_ORACLE_FIXTURES_PRODUCED\n";

val () = convert "oracle_hyps" "oracle_hyps";

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
  val () = if rejected then ()
           else raise Fail "incompatible retired constant was accepted"
  val () = if OS.FileSys.access(output,[]) then
             raise Fail "rejected conversion left a partial output"
           else ()
  val () = PFTEmit.emit_theory
    {trace=".hol/objs/oracle_retired_instanceTheory.tr.gz",
     output="oracle_retired_instance." ^ label ^ ".pft",ruleset=ruleset}
in print ("PFT_RETIRED_TYPE_CHECK_PASS " ^ label ^ "\n") end)
  rulesets;
val () = emit (Systeml.HOLDIR ^ "/src/bool/.hol/objs/boolTheory.tr.gz")
  "hol4/bool.pft" PFTEmit.HOL4;
val () = PFTMerge.merge
  {inputs=["hol4/bool.pft","oracle_hyps.hol4.pft",
           "oracle_retired_instance.hol4.pft"],
   targets=[PFTMerge.ThyAll("oracle_hyps",false),
            PFTMerge.ThyAll("oracle_retired_instance",false)],
   output="oracle_merged.hol4.pft",binary=true};
val () = print "PFT_ORACLE_SELFTEST_PASSED\n";
