(* A module whose parent isn't canonical is refused before anything is
   registered, and the theory loads from its .dat instead.  moduleA
   loads after a failed load spent its canonical stamps, so it isn't
   canonical; moduleB has a module in "modules", which an earlier run
   filled.  Run in a process of its own; exits with failure, saying why,
   if any of this doesn't hold.  Exports an empty refusedScratch theory. *)
open HolKernel Parse boolLib bossLib;
fun fail s = (TextIO.output (TextIO.stdErr, "refused: " ^ s ^ "\n");
              OS.Process.exit OS.Process.failure);
val _ = Meta.configureTheoryModuleCache
          {directory = "modules",
           base_state = OS.Path.concat (Systeml.HOLDIR, "bin/hol.state")}
        orelse fail "no module cache";
val _ = Meta.theoryModuleWriteLimit := 0;
fun raises f = (ignore (f ()); false) handle _ => true;
(* TheoryModules is bound only once modules are configured: compile at
   run time *)
val hit_count = ref 0;
fun hits () =
  (CompilerSpecific.quietbind
     "val _ = hit_count := #hits (TheoryModules.statistics ())";
   !hit_count);

(* The failed load is made in a theory called moduleA, which the context
   is then restored away from: moduleB's parent mustn't share its name
   with the current theory. *)
val _ = new_theory "refusedScratch";
val start = Context.snapshot ();
val _ = new_theory "moduleA";
val _ = new_definition ("module_value_def", ``module_value = T``);
val _ = raises (fn () => load "moduleATheory") orelse
        fail "loading moduleA over a clashing constant succeeded";
val _ = Context.restore start;
val _ = load "moduleATheory";
val _ = not (TheoryReader.is_canonical "moduleA") orelse
        fail "moduleA loaded with canonical stamps";

val hits0 = hits ();
val _ = load "moduleBTheory";
val _ = hits () = hits0 orelse
        fail "moduleB loaded from a module over a non-canonical parent";
val _ = Thm.is_sealed "moduleB" orelse fail "moduleB's load didn't seal it";
val _ = can (DB.fetch "moduleB") "from_a" orelse
        fail "moduleB's theorems aren't bound";
