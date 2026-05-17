open HolKernel Parse boolLib
open childTheory

val _ = new_theory "consume";

(* Coproduct side product -- declared as qux in outer/Holmakefile so
   Holmake's cache won't upload our outputs.  This forces an actual
   script execution on every rebuild, which is when opening
   childTheory above triggers load_thydata, which calls link_parents
   against child's recorded parent hashes -- and a stale child.dat
   fetched from cache fails that check against the current parent. *)
val _ = let val ostrm = TextIO.openOut "qux"
        in TextIO.output (ostrm, "consume side product\n");
           TextIO.closeOut ostrm
        end;

val _ = save_thm("consume_thm", child_thm);
val _ = export_theory();
