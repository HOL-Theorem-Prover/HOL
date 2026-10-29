open HolKernel boolSyntax;

val initial = Context.snapshot ();
val () = Thm.setCT "identity_padding";
val () = List.app (fn i => ignore (Term.prim_new_const
  {Thy="identity_padding",Name=Int.toString i} bool))
  (List.tabulate(31,fn i => i));
val () = Context.restore initial;
val _ = TheoryReader.load_thydata
  {thyname="identity_parent",path="identity_parentTheory.dat",
   hash=SHA1.sha1_file {filename=".hol/objs/identity_parentTheory.dat"}};
val () = Theory.load_complete "identity_parent";
val item = Term.prim_mk_const {Thy="identity_parent",Name="item"};
val ins = TextIO.openIn "identity_parent.epoch";
val parent_epoch = Int.fromString (TextIO.inputAll ins);
val () = TextIO.closeIn ins;
val epoch = KernelSig.epoch_of (#Name (Term.dest_thy_constid item));
val () = if parent_epoch <> SOME epoch then ()
  else raise Fail "parent/child did not use different process-local epochs";
val () = Theory.new_theory "identity_child";
val result = CONJUNCT2 (CONJ (DB.fetch "identity_parent" "ROOT") (REFL item));
val () = ignore (Theory.save_thm ("RESULT",result));
val () = Theory.export_theory ();
val () = print ("IDENTITY_CHILD_ACTUAL_EXPORT_PRODUCED epoch=" ^
                Int.toString epoch ^ "\n");
