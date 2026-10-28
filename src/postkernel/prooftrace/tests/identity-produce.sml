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

val () = identity_start "identity_delete";
val old_def = identity_define "item" T;
val old = identity_const "item";
val dependency = CONJ old_def (REFL old);
val () = Term.prim_delete_const {Thy="identity_delete",Name="item"};
val () = identity_export (identity_keep dependency (REFL T))
  ["private_const identity_delete$" ^
   Globals.oldify (identity_epoch old) "item",
   "absent_const identity_delete$item", "final_const bool$T"];

val () = identity_start "identity_unused";
val old_def = identity_define "item" T;
val old = identity_const "item";
val dependency = CONJ old_def (REFL old);
val () = Term.prim_delete_const {Thy="identity_unused",Name="item"};
val _ = Term.prim_new_const {Thy="identity_unused",Name="item"} bool;
val () = identity_export (identity_keep dependency (REFL T))
  ["private_const identity_unused$" ^
   Globals.oldify (identity_epoch old) "item",
   "decl_const identity_unused$item", "final_const bool$T"];

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

val () = identity_start "identity_type_restore";
val () = Type.prim_new_type {Thy="identity_type_restore",Tyop="item"} 0;
val old_ty = Type.mk_thy_type
  {Thy="identity_type_restore",Tyop="item",Args=[]};
val before_replacement = Context.snapshot ();
val () = Type.prim_delete_type {Thy="identity_type_restore",Tyop="item"};
val () = Type.prim_new_type {Thy="identity_type_restore",Tyop="item"} 0;
val replacement_ty = Type.mk_thy_type
  {Thy="identity_type_restore",Tyop="item",Args=[]};
val replacement_epoch = KernelSig.epoch_of
  (#Tyop (Type.dest_thy_typeid replacement_ty));
val dependency = REFL (mk_var("discarded",replacement_ty));
val () = Context.restore before_replacement;
val () = identity_export
  (identity_keep dependency (REFL (mk_var("x",old_ty))))
  ["private_type identity_type_restore$" ^
   Globals.oldify replacement_epoch "item",
   "public_type identity_type_restore$item",
   "final_type identity_type_restore$item"];

val () = identity_start "identity_unrecorded";
val foreign = Term.prim_new_const
  {Thy="identity_foreign",Name="item"} bool;
val () = identity_export (identity_keep (REFL foreign) (REFL T))
  ["reject ProofTraceParser: unrecorded imported symbol identity_foreign$item"];

val () = identity_start "identity_retired_import";
val foreign = Term.prim_new_const
  {Thy="identity_retired_foreign",Name="item"} bool;
val dependency = REFL foreign;
val () = Term.prim_delete_const
  {Thy="identity_retired_foreign",Name="item"};
val () = identity_export (identity_keep dependency (REFL T))
  ["reject ProofTraceParser: retired imported symbol " ^
   "identity_retired_foreign$item"];

val () = identity_start "identity_definition_parent";
val retained_definition = identity_define "item" T;
val item = identity_const "item";
val () = ignore (Theory.save_thm ("ROOT",REFL item));
val () = Theory.export_theory ();
val () = Theory.new_theory "identity_foreign_definition";
val () = identity_export retained_definition
  ["reject ProofTraceWalk: foreign definition from " ^
   "identity_definition_parent unsupported"];

val () = print "IDENTITY_ACTUAL_EXPORT_FIXTURES_PRODUCED\n";
