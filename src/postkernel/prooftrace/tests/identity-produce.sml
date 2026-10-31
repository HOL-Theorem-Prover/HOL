open HolKernel boolSyntax;

fun identity_require message condition =
  if condition then () else raise Fail message;
fun identity_write file lines =
  let val out = TextIO.openOut file
  in List.app (fn line => TextIO.output(out,line ^ "\n")) lines;
     TextIO.closeOut out
  end;
fun identity_define name rhs =
  #2 (Thm.gen_prim_specification
    (ASSUME (mk_eq(mk_var(name,type_of rhs),rhs))));
fun identity_const name =
  Term.prim_mk_const {Thy=Theory.current_theory (),Name=name};
fun identity_epoch tm =
  KernelSig.epoch_of (#Name (Term.dest_thy_constid tm));
fun identity_keep first second = CONJUNCT2 (CONJ first second);
val identity_initial = Context.snapshot ();
fun identity_start thy =
  (Context.restore identity_initial; Theory.new_theory thy);
fun identity_export th expectations =
  let val thy = Theory.current_theory ()
      val () = identity_require "final theorem must be current"
        (List.all Term.uptodate_term (concl th :: hyp th))
      val () = ignore (Theory.save_thm ("RESULT",th))
      val () = Theory.export_theory ()
  in identity_write (thy ^ ".expected") expectations end;

val () = identity_start "identity_restore";
val old_def = identity_define "item" T;
val old = identity_const "item";
val before_replacement = Context.snapshot ();
val () = Term.prim_delete_const {Thy="identity_restore",Name="item"};
val replacement_def = identity_define "item" F;
val replacement = identity_const "item";
val dependency = CONJ replacement_def (REFL replacement);
val () = Context.restore before_replacement;
val () = identity_export
  (identity_keep dependency (identity_keep old_def (REFL old)))
  ["private_const identity_restore$" ^
   Globals.oldify (identity_epoch replacement) "item",
   "public_const identity_restore$item", "final_const identity_restore$item"];

val () = identity_start "identity_collision";
val old = Term.prim_new_const {Thy="identity_collision",Name="item"} bool;
val dependency = REFL old;
val () = Term.prim_delete_const {Thy="identity_collision",Name="item"};
val collision = Globals.oldify (identity_epoch old) "item";
val _ = Term.prim_new_const {Thy="identity_collision",Name=collision} bool;
val () = identity_export (identity_keep dependency (REFL T))
  ["private_const identity_collision$" ^ collision ^ "'",
   "decl_const identity_collision$" ^ collision, "final_const bool$T"];

val () = identity_start "identity_closure";
val connective = mk_var ("c", bool --> bool --> bool);
val quantified = mk_forall (connective, list_mk_comb (connective,[T,T]));
val projected = CONJUNCT1 (Thm.Specialize conjunction (ASSUME quantified));
val () = identity_export
  (identity_keep (DISCH quantified projected) (REFL T))
  ["final_const bool$T"];

val () = identity_start "identity_reexport";
val item = Term.prim_new_const {Thy="identity_reexport",Name="item"} bool;
val () = identity_export (REFL item)
  ["final_const identity_reexport$item"];
val _ = save_thm ("EXTRA", REFL T);
val () = new_theory "identity_reexport_child";
val () = identity_export (REFL item)
  ["final_const identity_reexport$item"];

val () = print "IDENTITY_ACTUAL_EXPORT_FIXTURES_PRODUCED\n";
