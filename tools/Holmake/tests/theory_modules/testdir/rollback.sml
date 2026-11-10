(* A theory load that fails must not leave the theory in the theory
   graph for a child to link to, and a successful load seals the
   theory.  ROLLBACK_ARGS "modules" loads through the module cache in
   "modules", which an earlier run filled.  Run in a process of its
   own; exits with failure, saying why, if any of this doesn't hold. *)
open HolKernel Parse boolLib bossLib;
fun fail s = (TextIO.output (TextIO.stdErr, "rollback: " ^ s ^ "\n");
              OS.Process.exit OS.Process.failure);
val modules = OS.Process.getEnv "ROLLBACK_ARGS" = SOME "modules";
val _ = not modules orelse
        Meta.configureTheoryModuleCache
          {directory = "modules",
           base_state = OS.Path.concat (Systeml.HOLDIR, "bin/hol.state")}
        orelse fail "no module cache";
val _ = Meta.theoryModuleWriteLimit := 0;
fun read path =
  let val input = HOLFileSys.openIn path
  in HOLFileSys.inputAll input before HOLFileSys.closeIn input end;
fun theory_hash thy =
  let
    val text = read (thy ^ "Theory.sml")
    val (_, rest) = Substring.position "hash = \"" (Substring.full text)
  in
    Substring.string
      (Substring.takel (fn c => c <> #"\"") (Substring.triml 8 rest))
  end;
fun raises f = (ignore (f ()); false) handle _ => true;

(* A constant of the current theory clashes with one of moduleA's, so
   loading moduleA fails after it has started registering. *)
val _ = new_theory "moduleA";
val _ = new_definition ("module_value_def", ``module_value = T``);
val before_load = Context.snapshot ();
val _ = raises (fn () => load "moduleATheory") orelse
        fail "loading moduleA over a clashing constant succeeded";
val after_failure = Context.snapshot ();
val _ = not modules orelse
        (CompilerSpecific.quietbind
           "val _ = #misses (TheoryModules.statistics ()) = 0 orelse \
           \raise Fail \"moduleA's load did not use its module\"";
         true);
val _ = not (Thm.is_sealed "moduleA") orelse
        fail "a failed load sealed the theory";
val parent = ("moduleA", theory_hash "moduleA");
val _ = raises (fn () => Theory.link_parents ("moduleChild", "") [parent])
        orelse fail "a theory whose load failed is in the theory graph";

(* Without the conflict the load succeeds, and seals moduleA.  Not from
   the module: the failed load spent moduleA's canonical stamps, which a
   module needs. *)
val _ = Context.restore before_load;
val _ = delete_const "module_value";
val _ = modules orelse (load "moduleATheory"; Thm.is_sealed "moduleA") orelse
        fail "a loaded theory is unsealed";

(* In the failed load's context, moduleA's child must not load. *)
val _ = Context.restore after_failure;
val _ = raises (fn () => load "moduleBTheory") orelse
        fail "a child loaded on a parent whose load failed";
