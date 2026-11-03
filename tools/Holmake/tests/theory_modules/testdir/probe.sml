open HolKernel Parse boolLib bossLib;
val base = OS.Path.concat (Systeml.HOLDIR, "bin/hol.state");
val enabled = Meta.configureTheoryModuleCache
                {directory = OS.Path.concat (OS.FileSys.getDir (), "modules"),
                 base_state = base};
val save_namespace = PolyML.NameSpace.Structures.contents
  (valOf (#lookupStruct
    (PolyML.NameSpace.Structures.contents
      (valOf (#lookupStruct PolyML.globalNameSpace "PolyML"))) "SaveState"));
val supported = Option.isSome
                  (#lookupVal save_namespace "saveDependentModuleBasic");
val _ = enabled = supported orelse raise Fail "module cache capability mismatch";
val shadow_calls = ref 0;
val shadow = OS.Process.getEnv "HOL_MODULE_TEST_SHADOW" = SOME "1";
val _ = if shadow then CompilerSpecific.quietbind
  "structure Option = struct open Option val original = valOf \
  \fun valOf x = (shadow_calls := !shadow_calls + 1; original x) end"
  else ();
val events = ref ([] : string list);
val _ = Theory.register_hook
  ("module-test", fn TheoryDelta.TheoryLoaded name => events := name :: !events
                  | _ => ());
val _ = load "moduleDTheory";
val _ = load "moduleATheory";

val _ =
  let
    val ty = Type.mk_thy_type {Thy = "moduleA", Tyop = "module_type", Args = []}
    val tm = Term.mk_thy_const
               {Thy = "moduleA", Name = "module_value", Ty = ty}
    val th = DB.fetch "moduleA" "module_value_def"
    val (left, _) = dest_eq (concl th)
    val own_events = List.filter (String.isPrefix "module") (rev (!events))
    val _ = Theory.uptodate_thm th andalso aconv left tm orelse
            raise Fail "cached theorem disagrees with current kernel"
    val _ = aconv (concl moduleDTheory.from_b) (concl moduleDTheory.from_c)
            orelse raise Fail "diamond parents disagree"
    val _ = own_events = ["moduleA", "moduleB", "moduleC", "moduleD"] orelse
            raise Fail ("load hooks: " ^ String.concatWith "," own_events)
    val _ = not shadow orelse !shadow_calls > 0 orelse
            raise Fail "cached factory ignored changed ML namespace"
  in
    ()
  end;

val _ = if enabled then
  CompilerSpecific.quietbind
    "val _ = let val out = TextIO.openOut \"module-stats\"; \
    \val {hits,misses,writes} = TheoryModules.statistics() \
    \in TextIO.output(out, Int.toString hits ^ \" \" ^ \
    \Int.toString misses ^ \" \" ^ Int.toString writes); \
    \TextIO.closeOut out end"
  else ();

val _ = Globals.interactive := false;
val _ = new_theory "moduleProbe";
val _ = save_thm ("probe", moduleDTheory.from_b);
val _ = export_theory ();
val _ = if enabled then
  (ignore (Meta.configureTheoryModuleCache
    {directory = OS.Path.concat (OS.FileSys.getDir (), "producer-modules"),
     base_state = base});
   Meta.produceTheoryModule "moduleProbeTheory.sml")
  else ();
