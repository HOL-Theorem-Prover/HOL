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
val () = load_pft ["PFTReader","PFTReplay","ProofTraceReplay"];

(* Replay and check before loading the libraries used to produce the traces. *)
val () = if phase <> "raw" andalso phase <> "convert" andalso
    phase <> "separate" then () else let
  val cases = [("identity_restore", "identity_restore", "item"),
    ("identity_collision", "bool", "T"), ("identity_closure", "bool", "T"),
    ("identity_negation", "bool", "T"),
    ("identity_reexport", "identity_reexport", "item"),
    ("identity_reexport_child", "identity_reexport", "item"),
    ("identity_trace_loader", "bool", "T")]
  val bootstrap = Systeml.HOLDIR ^
    "/src/bool/.hol/objs/boolTheory.tr.gz"
  val theories = "bool" :: map #1 cases
  fun trace "bool" = bootstrap
    | trace thy = ".hol/objs/" ^ thy ^ "Theory.tr.gz"
  fun output thy = "hol4/" ^ thy ^ ".pft.bin"
  val () = if phase = "raw" then ProofTraceReplay.replay bootstrap else ()
  val () = if phase <> "convert" then () else
    (List.app (fn thy => PFTEmit.emit_theory
       {trace=trace thy,output=output thy,ruleset=PFTEmit.HOL4}) theories;
     PFTEmit.emit_theory {trace=trace "identity_negation",
       output="identity_negation.candle.pft",ruleset=PFTEmit.Candle};
     pass ())
  val db = if phase = "separate" then
      List.foldl (fn (thy,db) => PFTReplay.replay db (output thy))
        PFTReplay.empty_trDB theories
    else PFTReplay.empty_trDB
  fun check (thy, const_thy, name) = let
    val th = if phase = "raw" then
        (ProofTraceReplay.replay (trace thy);
         valOf (Symtab.lookup
           (#1 (ProofTraceReplay.replayed_thms thy)) "RESULT"))
      else valOf (PFTReplay.lookup db (thy ^ "$RESULT"))
    val tm = Term.prim_mk_const {Thy=const_thy,Name=name}
  in require ("wrong sequent for " ^ thy ^ "$RESULT")
       (null (Thm.hyp th) andalso
        Term.aconv (Thm.concl th) (Thm.concl (Thm.REFL tm)));
     print ("IDENTITY_EXACT " ^ thy ^ "$RESULT\n")
  end
  val () = List.app check cases
  val negation = if phase = "raw" then
      valOf (Symtab.lookup
        (#1 (ProofTraceReplay.replayed_thms "identity_negation")) "NEGATION")
    else valOf (PFTReplay.lookup db "identity_negation$NEGATION")
  val n = Term.mk_comb (Term.prim_mk_const {Thy="bool",Name="~"},
    Term.prim_mk_const {Thy="bool",Name="T"})
  val () = require "wrong NOT_INTRO negation sequent"
    (case Thm.hyp negation of
       [h] => Term.aconv h n andalso Term.aconv (Thm.concl negation) n
     | _ => false)
  val () = print "IDENTITY_NEGATION_EXACT\n"
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

(* NOT_INTRO accepts a negation as well as an explicit implication to F. *)
val () = identity_start "identity_negation";
val n = mk_neg T;
val negated = NOT_INTRO (ASSUME n);
val _ = save_thm ("NEGATION",negated);
val () = identity_export
  (identity_keep (DISCH n negated) (REFL T));

(* Adding a theorem after export changes the hash recorded by the child. *)
val () = identity_start "identity_reexport";
val item = Term.prim_new_const {Thy="identity_reexport",Name="item"} bool;
val () = identity_export (REFL item);
val _ = save_thm ("EXTRA", REFL T);
val () = new_theory "identity_reexport_child";
val () = identity_export (REFL item);

val () = pass ();
