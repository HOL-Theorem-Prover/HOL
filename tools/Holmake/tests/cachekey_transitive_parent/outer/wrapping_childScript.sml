open HolKernel Parse boolLib
open parentLib

(* On the forced stale hit, validation must discard ALL staged products
   before falling back to this script, not merely report a cache miss. *)
val _ =
    if OS.FileSys.access (".check-cache-publication", []) then
      List.app
        (fn name =>
            if HOLFileSys.access (name, []) then
              raise Fail ("Rejected cache product was exposed: " ^ name)
            else ())
        ["wrapping_childTheory.dat", "wrapping_childTheory.sml",
         "wrapping_childTheory.sig"]
    else ();

(* Name deliberately long enough that the .dat header's sexp printer
   wraps the (theory ...) sublist onto a new line, exercising the
   "(theory\n" case in TheoryDat.read_parents. *)
val _ = new_theory "wrapping_child";
val child_thm = save_thm("child_thm", parent_thm);
val _ = export_theory();
