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
  | _ => raise Fail ("unknown export test case: " ^ case_name);
val () = Theory.export_theory ();
val () = print ("EXPORT_FIXTURE_PRODUCED " ^ case_name ^ "\n");
