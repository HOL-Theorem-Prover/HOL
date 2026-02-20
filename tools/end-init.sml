(* end-init.sml - Moscow ML Bare HOL Finale
   =========================================

   This file is loaded at the end of bare HOL session initialization
   (when hol is invoked with --bare). It simply restores output by
   setting quietdec to false.

   For full HOL sessions, end-init-boss.sml is loaded instead.
   For Poly/ML, the bare/full distinction is handled in prelude.ML/prelude2.ML.
*)

val _ = quietdec := false;
