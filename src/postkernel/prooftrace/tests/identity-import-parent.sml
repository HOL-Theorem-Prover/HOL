open HolKernel boolSyntax;

val initial = Context.snapshot ();
val () = Thm.setCT "identity_padding";
val () = List.app (fn i => ignore (Term.prim_new_const
  {Thy="identity_padding",Name=Int.toString i} bool))
  (List.tabulate(7,fn i => i));
val () = Context.restore initial;
val () = Theory.new_theory "identity_parent";
val () = Theory.new_constant ("item",bool);
val item = Term.prim_mk_const {Thy="identity_parent",Name="item"};
val () = ignore (Theory.save_thm ("ROOT",REFL item));
val epoch = KernelSig.epoch_of (#Name (Term.dest_thy_constid item));
val out = TextIO.openOut "identity_parent.epoch";
val () = TextIO.output(out,Int.toString epoch ^ "\n");
val () = TextIO.closeOut out;
val () = Theory.export_theory ();
val () = print "IDENTITY_PARENT_ACTUAL_EXPORT_PRODUCED\n";
