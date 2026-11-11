fun mk_abs_eq lhs rhs = let
  val ty = Term.type_of lhs
  val eq = Term.mk_thy_const
    {Thy="min",Name="=",Ty=Type.--> (ty,Type.--> (ty,Type.bool))}
in Term.mk_comb(Term.mk_comb(eq,lhs),rhs) end;

fun mk_abs_fixture () = let
  val x = Term.mk_var("x",Type.bool)
  val x' = Term.mk_var("x'",Type.bool)
  val body = mk_abs_eq x' x
  (* The cosmetic x clashes with the free x; dest_abs opens with x'. *)
  val lam = Term.rename_bvar "x" (Term.mk_abs(x',body))
in (x',lam) end;

val () = load_pft ["PFTReader","PFTReplay"];
val () = if identity_phase = "produce" then let
    val () = Theory.new_theory "pft_mk_abs"
    val (expected_binder,lam) = mk_abs_fixture ()
    val (binder,child,finish) = Thm.Mk_abs (Thm.REFL lam)
    val () = if Term.aconv binder expected_binder then ()
             else raise Fail "unexpected source Mk_abs binder"
    val () = ignore (Theory.save_thm("RESULT",finish child))
  in Theory.export_theory () end
  else let
    val () = PFTEmit.emit_theory
      {trace=".hol/objs/pft_mk_absTheory.tr.gz",
       output="hol4/pft_mk_abs.pft.bin",ruleset=PFTEmit.HOL4}
    val db = PFTReplay.replay PFTReplay.empty_trDB
      "hol4/pft_mk_abs.pft.bin"
    val (_,lam) = mk_abs_fixture ()
    val expected = mk_abs_eq lam lam
    val th = valOf (PFTReplay.lookup db "pft_mk_abs$RESULT")
    val () = if null (Thm.hyp th) andalso
                Term.aconv (Thm.concl th) expected then ()
             else raise Fail "Mk_abs replay sequent mismatch"
  in print "MK_ABS_HOL_EXACT_PASS\n" end;
