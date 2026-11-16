(* PROBE_ARGS, space-separated: the order in which to load the diamond's
   theories (letters from "abcde"), then flags: "nocache", "shadow" (rebind
   a structure the generated theory source uses), "customloader" (replace
   TheoryReader.load_thydata_fn), "limit<n>" (write at most n modules),
   "loadprobe" (load the probe theory exported by an earlier run instead
   of exporting it).  Writes the diamond's theorems to "fingerprint". *)
open HolKernel Parse boolLib bossLib;
val args = String.tokens Char.isSpace (valOf (OS.Process.getEnv "PROBE_ARGS"));
val order = hd args;
fun flag s = List.exists (fn a => a = s) (tl args);
val base = OS.Path.concat (Systeml.HOLDIR, "bin/hol.state");
val enabled =
    not (flag "nocache") andalso
    Meta.configureTheoryModuleCache {directory = "modules", base_state = base};
val save_namespace = PolyML.NameSpace.Structures.contents
  (valOf (#lookupStruct
    (PolyML.NameSpace.Structures.contents
      (valOf (#lookupStruct PolyML.globalNameSpace "PolyML"))) "SaveState"));
(* Meta's own test: modules need both of these, and Poly/ML added
   showHierarchyWithIds months after saveDependentModuleBasic; and only
   the standard and experimental kernels load theories from modules. *)
val supported =
    List.all (Option.isSome o #lookupVal save_namespace)
             ["showHierarchyWithIds", "saveDependentModuleBasic"] andalso
    (Thm.kernelid = "stdknl" orelse Thm.kernelid = "expknl");
val _ = flag "nocache" orelse enabled = supported orelse
        raise Fail "module cache capability mismatch";
val _ = List.app (fn a => if String.isPrefix "limit" a then
                            Meta.theoryModuleWriteLimit :=
                              valOf (Int.fromString (String.extract (a, 5, NONE)))
                          else ())
                 (tl args);
val shadow_calls = ref 0;
val _ = if flag "shadow" then CompilerSpecific.quietbind
  "structure Theory = struct open Theory \
  \fun load_complete s = (shadow_calls := !shadow_calls + 1; \
  \Theory.load_complete s) end"
  else ();
val loader_calls = ref 0;
val _ = if flag "customloader" then
          let val default = !TheoryReader.load_thydata_fn
          in
            TheoryReader.load_thydata_fn :=
              (fn args => (loader_calls := !loader_calls + 1; default args))
          end
        else ();
val events = ref ([] : string list);
val _ = Theory.register_hook
  ("module-test", fn TheoryDelta.TheoryLoaded name => events := name :: !events
                  | _ => ());

val _ = app (fn c => load ("module" ^ str (Char.toUpper c) ^ "Theory"))
            (explode order);

fun thy_of c = "module" ^ str (Char.toUpper c);
val loaded = rev (List.filter (String.isPrefix "module") (!events));
val _ = List.all (fn t => Lib.mem t loaded)
                 (map thy_of (explode "abcde")) andalso
        length loaded = 5 orelse
        raise Fail ("load hooks: " ^ String.concatWith "," loaded);

(* Every theorem is current in this process's kernel, and constants
   built from the kernel's tables are the ones the theorems mention. *)
val _ = List.all (fn t => List.all (Theory.uptodate_thm o #2)
                                   (DB.thms t))
                 (map thy_of (explode "abcde")) orelse
        raise Fail "a loaded theorem is not up to date";
val _ =
  let
    val ty = Type.mk_thy_type {Thy = "moduleA", Tyop = "module_type", Args = []}
    val tm = Term.mk_thy_const
               {Thy = "moduleA", Name = "module_value", Ty = ty}
    val (left, _) = dest_eq (concl moduleATheory.module_value_def)
  in
    Term.compare (left, tm) = EQUAL orelse
    raise Fail "loaded constant differs from the kernel's"
  end;
val _ = Term.compare (concl moduleDTheory.from_b,
                      concl moduleDTheory.from_c) = EQUAL orelse
        raise Fail "diamond parents disagree";
val _ =
  let
    val out = TextIO.openOut "fingerprint"
  in
    app (fn t => app (fn (n, th) =>
                         TextIO.output (out, t ^ "." ^ n ^ " " ^
                                             thm_to_string th ^ "\n"))
                     (Listsort.sort (fn ((a, _), (b, _)) =>
                                        String.compare (a, b))
                                    (DB.thms t)))
        (map thy_of (explode "abcde"));
    TextIO.closeOut out
  end;
val _ = not (flag "shadow") orelse !shadow_calls > 0 orelse
        raise Fail "load ignored the rebound Theory structure";
val _ = not (flag "customloader") orelse !loader_calls = 5 orelse
        raise Fail "load bypassed the custom theory loader";

(* A name gets the canonical stamp once per process: restoring the
   context does not make it available again, and loaded theories stay
   sealed. *)
val _ =
  let
    val ctxt = Context.snapshot ()
    val first = Term.prim_load_const {Thy = "moduleRestore", Name = "c"} bool
    val _ = Context.restore ctxt
    val second = Term.prim_load_const {Thy = "moduleRestore", Name = "c"} bool
    val _ = Context.restore ctxt
    val resealed =
        (ignore (Theory.incorporate_consts "moduleA" [("module_fresh", bool)]);
         true) handle HOL_ERR _ => false
  in
    first andalso not second andalso not resealed orelse
    raise Fail "canonical stamps reissued or sealed theory reopened"
  end;

(* The probe theory, loaded as Meta.load loads a theory, and what its
   theorems are, to compare a module the exporter wrote with one a
   loader wrote. *)
val _ = if flag "loadprobe" then
  let
    val _ = app ((!Meta.moduleSourceLoader) QUse.use)
                ["moduleProbeTheory.sig", "moduleProbeTheory.sml"]
    val thms = DB.thms "moduleProbe"
    val out = TextIO.openOut "probe-fingerprint"
  in
    List.all (Theory.uptodate_thm o #2) thms andalso
    List.all (fn th => Term.compare (concl th,
                                     concl moduleDTheory.from_b) = EQUAL)
             (map (DB.fetch "moduleProbe") ["probe", "probe_c"]) andalso
    length thms = 3 orelse
    raise Fail "loaded probe theory differs";
    app (fn (n, th) =>
            TextIO.output (out, n ^ " " ^ thm_to_string th ^ "\n"))
        (Listsort.sort (fn ((a, _), (b, _)) => String.compare (a, b))
                       thms);
    TextIO.closeOut out
  end
  else ();

val _ = if enabled then
  CompilerSpecific.quietbind
    "val _ = let val out = TextIO.openOut \"module-stats\"; \
    \val {hits,misses,writes} = TheoryModules.statistics() \
    \in TextIO.output(out, Int.toString hits ^ \" \" ^ \
    \Int.toString misses ^ \" \" ^ Int.toString writes); \
    \TextIO.closeOut out end"
  else ();

val _ = if flag "loadprobe" then OS.Process.exit OS.Process.success
        else ();
val _ = Globals.interactive := false;
val _ = new_theory "moduleProbe";
val _ = save_thm ("probe", moduleDTheory.from_b);
val _ = save_thm ("probe_c", moduleDTheory.from_c);
val _ = new_definition ("probe_value_def", ``probe_value = T``);
val _ = export_theory ();
