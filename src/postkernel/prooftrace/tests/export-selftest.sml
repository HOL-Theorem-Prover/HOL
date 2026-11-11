val () = load_pft ["PFTReader","PFTReplay"];
val () = use (test_source ^ "export-check.sml");
val () = if identity_phase <> "replay" then () else let
  val () = PFTEmit.emit_theory
    {trace=Systeml.HOLDIR ^ "/src/bool/.hol/objs/boolTheory.tr.gz",
     output="hol4/bool.pft.bin",ruleset=PFTEmit.HOL4}
  val files = "hol4/bool.pft.bin" :: List.map (fn name => name ^ ".hol4.pft")
    ["vacuous","shadow","overlap","hypotheses","binder"]
  val db = List.foldl (fn (file,db) => PFTReplay.replay db file)
    PFTReplay.empty_trDB files
  val () = check_export_results db
in print "PFT_TEST_PHASE_PASS\n"; OS.Process.exit OS.Process.success end;

open HolKernel;
val case_name = valOf (OS.Process.getEnv "HOL_PFT_EXPORT_CASE");
val theory = "pftExport_" ^ case_name;
val () = Theory.new_theory theory;
val x = Term.mk_var("x", Type.bool);
val y = Term.mk_var("y", Type.bool);

fun save_exact name expected th =
  if null (Thm.hyp th) andalso Term.aconv (Thm.concl th) expected then
    ignore (Theory.save_thm(name,th))
  else raise Fail ("wrong source sequent: " ^ name);

fun save_hyps name expected_hyps expected th =
  if length (Thm.hyp th) = length expected_hyps andalso
     List.all (fn h => List.exists (Term.aconv h) (Thm.hyp th)) expected_hyps
     andalso Term.aconv (Thm.concl th) expected then
    ignore (Theory.save_thm(name,th))
  else raise Fail ("wrong source sequent: " ^ name);

val () = case case_name of
    "vacuous" => let
      val witness = Thm.EXISTS(boolSyntax.mk_exists(x,boolSyntax.T),x)
        boolTheory.TRUTH
      val th = Thm.prim_specification ["unused"] witness
      val unused = Term.mk_thy_const
        {Thy=theory, Name="unused", Ty=Type.bool}
    in
      save_exact "VACUOUS" boolSyntax.T th;
      save_exact "UNUSED_REFL" (boolSyntax.mk_eq(unused,unused))
        (Thm.REFL unused)
    end
  | "shadow" => let
      val inner = Thm.GEN x (Thm.REFL x)
      val body = Thm.CONJ (Thm.REFL x) (Thm.CONJ inner (Thm.REFL y))
      val ey = Thm.EXISTS(boolSyntax.mk_exists(y,Thm.concl body),y) body
      val witness = Thm.EXISTS(boolSyntax.mk_exists(x,Thm.concl ey),x) ey
      val th = Thm.prim_specification ["first","second"] witness
      fun constant name = Term.mk_thy_const
        {Thy=theory, Name=name, Ty=Type.bool}
      val a = constant "first"
      val b = constant "second"
      val expected = boolSyntax.mk_conj(boolSyntax.mk_eq(a,a),
        boolSyntax.mk_conj(Thm.concl inner,boolSyntax.mk_eq(b,b)))
    in save_exact "SHADOW" expected th end
  | "overlap" => let
      val v = Term.mk_var(theory ^ "$first",Type.bool)
      val body = Thm.GEN v (Thm.REFL x)
      val witness = Thm.EXISTS(boolSyntax.mk_exists(x,Thm.concl body),x) body
      val th = Thm.prim_specification ["first"] witness
      val first = Term.mk_thy_const
        {Thy=theory,Name="first",Ty=Type.bool}
      val expected = boolSyntax.mk_forall(v,boolSyntax.mk_eq(first,first))
    in save_exact "OVERLAP" expected th end
  | "hypotheses" => let
      open boolSyntax
      val p = mk_eq(x,x)
      val conj = mk_conj(p,p)
      val refl = Thm.REFL x
      val () = save_hyps "CONJ_LEFT" [p] conj (Thm.CONJ (Thm.ASSUME p) refl)
      val () = save_hyps "CONJ_RIGHT" [p] conj (Thm.CONJ refl (Thm.ASSUME p))
      val ith = Drule.ADD_ASSUM T (Thm.DISCH T refl)
      val () = save_hyps "MP" [T] p (Thm.MP ith boolTheory.TRUTH)
      val branch = mk_imp(p,p)
      val disj = Drule.ADD_ASSUM branch (Thm.DISJ1 (Thm.ASSUME p) p)
      val () = save_hyps "DISJ_CASES" [p,branch] p
        (Thm.DISJ_CASES disj refl refl)
      val pred = Term.mk_abs(y,T)
      val guard = mk_forall(y,mk_imp(Term.mk_comb(pred,y),p))
      val exists = Thm.EXISTS(mk_exists(y,T),T) boolTheory.TRUTH
    in save_hyps "CHOOSE" [guard] p
         (Thm.CHOOSE (y,Drule.ADD_ASSUM guard exists) refl) end
  | "binder" => let
      val let_tm = Term.prim_mk_const {Thy="bool",Name="LET"}
      val result = Term.mk_comb
        (Term.inst [Type.alpha |-> Type.bool, Type.beta |-> Type.bool] let_tm,
         Term.mk_abs(x,boolSyntax.T))
    in save_exact "LET" (boolSyntax.mk_eq(result,result))
         (Thm.GEN_ABS (SOME let_tm) [x] (Thm.REFL boolSyntax.T)) end
  | _ => raise Fail ("unknown export test case: " ^ case_name);
val () = Theory.export_theory ();
val () = print ("EXPORT_FIXTURE_PRODUCED " ^ case_name ^ "\n");

val name = valOf (OS.Process.getEnv "HOL_PFT_EXPORT_CASE");
fun convert (label,ruleset) =
  PFTEmit.emit_theory
    {trace=".hol/objs/pftExport_" ^ name ^ "Theory.tr.gz",
     output=name ^ "." ^ label ^ ".pft",ruleset=ruleset};
val () = List.app (fn target =>
  (convert target; print ("EXPORT_CONVERTED " ^ #1 target ^ "\n")))
  [("hol4",PFTEmit.HOL4),("candle",PFTEmit.Candle)];
