fun write file text = let val out = TextIO.openOut file
  in TextIO.output (out,text); TextIO.closeOut out end;
val () =
  if identity_phase = "loader-parent" then
    (load "boolTheory";
     load "boolSyntax")
  else
    (List.app load ["HolKernel", "ThyDataSexp", "TheoryReader"];
     use (source ^ "ThmSrc_tr.sig");
     use (source ^ "ThmSrc_tr.sml");
     load "boolTheory";
     load "boolSyntax");
open HolKernel;
val truth = Term.prim_mk_const {Thy="bool",Name="T"};
val () = if identity_phase = "loader-parent" then let
    val () = new_theory "identity_loader_parent"
    val def = #2 (Thm.gen_prim_specification
      (ASSUME (boolSyntax.mk_eq (mk_var ("item",bool),truth))))
    val _ = save_thm ("item_def",def)
    val () = new_theory "identity_loader_sentinel"
  in write "identity_loader_parent.hash" (Theory.hash "identity_loader_parent")
  end
  else let
    val ins = TextIO.openIn "identity_loader_parent.hash"
    val hash = TextIO.inputAll ins
    val () = TextIO.closeIn ins
    val _ = TheoryReader.load_thydata {thyname="identity_loader_parent",
      path="identity_loader_parentTheory.dat", hash=hash}
    val () = new_theory "identity_trace_loader"
    val _ = save_thm ("RESULT", REFL truth)
    val () = export_theory ()
  in write "identity_trace_loader.expected" "final_const bool$T\n" end;
