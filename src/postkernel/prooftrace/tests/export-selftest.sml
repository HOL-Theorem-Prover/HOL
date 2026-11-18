val () = if phase <> "replay" then () else
  (check_export_results (replay_bool (map (fn name => name ^ ".hol4.pft")
     ["vacuous","shadow","overlap","hypotheses","binder"])); pass ());

open HolKernel;
val case_name = phase;
val theory = "pftExport_" ^ case_name;
val () = Theory.new_theory theory;
val x = Term.mk_var("x", Type.bool);
val y = Term.mk_var("y", Type.bool);

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

val () = convert theory case_name;
