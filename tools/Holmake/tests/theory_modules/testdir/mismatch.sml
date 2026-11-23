(* Rewrites moduleB's module in "modules", which an earlier run filled, so
   that it stores moduleA's prepared data beside moduleB's own decoded
   data.  A load from it must decode moduleB's data instead of installing
   moduleA's.  Run in a process of its own; exits with failure, saying
   why, if it can't. *)
open HolKernel Parse boolLib bossLib;
fun fail s = (TextIO.output (TextIO.stdErr, "mismatch: " ^ s ^ "\n");
              OS.Process.exit OS.Process.failure);
val base_state = OS.Path.concat (Systeml.HOLDIR, "bin/hol.state");
val _ = Meta.configureTheoryModuleCache
          {directory = "modules", base_state = base_state}
        orelse fail "no module cache";
val base_id = case TheoryModules.base_id_of base_state of
                  SOME id => id
                | NONE => fail "no base state id";
fun found thy =
  let
    val digest = TheoryModules.file_digest (thy ^ "Theory.dat")
    val path = OS.Path.concat
                 ("modules", TheoryModules.module_file base_id (thy, digest))
  in
    case TheoryModules.read_module path (thy ^ "Theory") (thy, digest) of
        SOME m => (path, digest, m)
      | NONE => fail ("no module for " ^ thy)
  end;
val (_, _, module_a) = found "moduleA";
val _ = isSome (#prepared module_a) orelse fail "moduleA has no prepared data";
val (path_b, digest_b, module_b) = found "moduleB";
val roots =
    case TheoryModules.module_roots "moduleBTheory" digest_b (#data module_b)
                                    (TheoryModules.core_bindings ()) of
        SOME roots => roots
      | NONE => fail "no roots for moduleB";
val prepared_a =
    Universal.tagInject TheoryReader.prepared_tag (#prepared module_a);
val roots = List.map (fn r => if Universal.tagIs TheoryReader.prepared_tag r
                              then prepared_a else r)
                     roots;
val _ = TheoryModules.save_module path_b base_id roots;
