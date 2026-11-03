(* Each phase runs in a fresh process; raw replay starts without boolTheory. *)
val source = valOf (OS.Process.getEnv "HOL_PFT_SOURCE_ROOT") ^
  "/src/postkernel/prooftrace/";
val phase = valOf (OS.Process.getEnv "HOL_PFT_IDENTITY_PHASE");
fun pass () = (print "PFT_TEST_PHASE_PASS\n";
               OS.Process.exit OS.Process.success);
fun require message condition =
  if condition then () else raise Fail message;
fun read file = let val ins = TextIO.openIn file
  in TextIO.inputAll ins before TextIO.closeIn ins end;
fun write file text = let val out = TextIO.openOut file
  in TextIO.output (out,text); TextIO.closeOut out end;
val () =
  (List.app load ["DArray", "PIntMap", "RawTheory_dtype"];
   List.app (fn name =>
     (use (source ^ name ^ ".sig"); use (source ^ name ^ ".sml")))
     ["ProofTraceParser", "ProofTraceWalk", "ProofTraceReplay"]);

(* Replay and check before loading the libraries used to produce the traces. *)
val () = if phase <> "raw" then () else let
  val cases = [("identity_restore", "identity_restore", "item"),
    ("identity_collision", "bool", "T"), ("identity_closure", "bool", "T"),
    ("identity_reexport", "identity_reexport", "item"),
    ("identity_reexport_child", "identity_reexport", "item"),
    ("identity_trace_loader", "bool", "T")]
  val () = ProofTraceReplay.replay
    (Systeml.HOLDIR ^ "/src/bool/.hol/objs/boolTheory.tr.gz")
  fun check (thy, const_thy, name) = let
    val () = ProofTraceReplay.replay (".hol/objs/" ^ thy ^ "Theory.tr.gz")
    val th = valOf (Symtab.lookup
      (#1 (ProofTraceReplay.replayed_thms thy)) "RESULT")
    val tm = Term.prim_mk_const {Thy=const_thy,Name=name}
  in require ("wrong sequent for " ^ thy ^ "$RESULT")
       (null (Thm.hyp th) andalso
        Term.aconv (Thm.concl th) (Thm.concl (Thm.REFL tm)));
     print ("IDENTITY_EXACT " ^ thy ^ "$RESULT\n")
  end
  val () = List.app check cases
  fun declared name = case String.fields (fn c => c = #"$") name of
      [thy,nm] => require ("missing constant " ^ name)
        (List.exists (fn tm => #Thy (Term.dest_thy_const tm) = thy)
          (Term.decls nm))
    | _ => raise Fail name
  val () = List.app declared (String.tokens Char.isSpace (read "identity.names"))
in pass () end;

val () = if phase <> "loader-child" then () else
  (List.app load ["HolKernel", "ThyDataSexp", "TheoryReader"];
   use (source ^ "ThmSrc_tr.sig"); use (source ^ "ThmSrc_tr.sml"));
val () = List.app load ["boolTheory", "boolSyntax"];
open HolKernel boolSyntax;

(* The alternate loader must record imported identities for the next export. *)
val () = if phase = "produce" then () else
  (if phase = "loader-parent" then
     (new_theory "identity_loader_parent";
      save_thm ("item_def", #2 (Thm.gen_prim_specification
        (ASSUME (mk_eq (mk_var ("item",bool),T)))));
      new_theory "identity_loader_sentinel";
      write "identity_loader_parent.hash" (Theory.hash "identity_loader_parent"))
   else
     (TheoryReader.load_thydata {thyname="identity_loader_parent",
        path="identity_loader_parentTheory.dat",
        hash=read "identity_loader_parent.hash"};
      new_theory "identity_trace_loader";
      save_thm ("RESULT", REFL T); export_theory ());
   pass ());

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
fun identity_export th =
  (require "final theorem must be current"
     (List.all Term.uptodate_term (concl th :: hyp th));
   Theory.save_thm ("RESULT",th); Theory.export_theory ());

(* Restoring a signature must not give a replaced constant the public name. *)
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
  (identity_keep dependency (identity_keep old_def (REFL old)));
val restored_private = Globals.oldify (identity_epoch replacement) "item";

(* The private name may already have been declared by the user. *)
val () = identity_start "identity_collision";
val old = Term.prim_new_const {Thy="identity_collision",Name="item"} bool;
val dependency = REFL old;
val () = Term.prim_delete_const {Thy="identity_collision",Name="item"};
val collision = Globals.oldify (identity_epoch old) "item";
val _ = Term.prim_new_const {Thy="identity_collision",Name=collision} bool;
val () = identity_export (identity_keep dependency (REFL T));
val () = write "identity.names"
  ("identity_restore$" ^ restored_private ^ "\n" ^
   "identity_restore$item\nidentity_collision$" ^ collision ^ "\n" ^
   "identity_collision$" ^ collision ^ "'\n");

(* Logical roles can be hidden inside a substitution closure. *)
val () = identity_start "identity_closure";
val connective = mk_var ("c", bool --> bool --> bool);
val quantified = mk_forall (connective, list_mk_comb (connective,[T,T]));
val projected = CONJUNCT1 (Thm.Specialize conjunction (ASSUME quantified));
val () = identity_export
  (identity_keep (DISCH quantified projected) (REFL T));

(* Adding a theorem after export changes the hash recorded by the child. *)
val () = identity_start "identity_reexport";
val item = Term.prim_new_const {Thy="identity_reexport",Name="item"} bool;
val () = identity_export (REFL item);
val _ = save_thm ("EXTRA", REFL T);
val () = new_theory "identity_reexport_child";
val () = identity_export (REFL item);

val () = pass ();
