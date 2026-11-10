(* A theory load that fails must not leave the theory linked into the
   graph, and a successful load seals the theory.  Run in a process of
   its own; exits with failure, saying why, if either doesn't hold. *)
open HolKernel Parse boolLib bossLib;
fun fail s = (TextIO.output (TextIO.stdErr, "rollback: " ^ s ^ "\n");
              OS.Process.exit OS.Process.failure);
fun read path =
  let val input = HOLFileSys.openIn path
  in HOLFileSys.inputAll input before HOLFileSys.closeIn input end;
fun theory_hash thy =
  let
    val text = read (thy ^ "Theory.sml")
    val (_, rest) = Substring.position "hash = \"" (Substring.full text)
  in
    Substring.string
      (Substring.takel (fn c => c <> #"\"")
                       (Substring.triml 8 rest))
  end;
fun load_dat thy =
  TheoryReader.load_thydata
    {thyname = thy, path = thy ^ "Theory.dat", hash = theory_hash thy};
fun raises f = (ignore (f ()); false) handle _ => true;

(* A clash with a constant of the current theory makes the load of
   moduleA fail after it has started registering. *)
val _ = new_theory "moduleA";
val _ = new_definition ("module_value_def", ``module_value = T``);
val before_load = Context.snapshot ();
val _ = raises (fn () => load_dat "moduleA") orelse
        fail "loading moduleA over a clashing constant succeeded";
val after_failure = Context.snapshot ();
val _ = Context.restore before_load;
val _ = delete_const "module_value";
val _ = load_dat "moduleA";
(* The failed load's context must not have moduleA in the theory graph
   for a child to link to, as moduleB's load would. *)
val _ = Context.restore after_failure;
val parent = ("moduleA", theory_hash "moduleA");
val _ = raises (fn () => Theory.link_parents ("moduleChild", "") [parent])
        orelse fail "a theory whose load failed is in the theory graph";
val _ = Thm.is_sealed "moduleA" orelse fail "a loaded theory is unsealed";
