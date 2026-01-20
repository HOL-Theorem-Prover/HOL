(* prelude2.ML - Poly/ML Full HOL Additional Setup
   ================================================

   This file is loaded after prelude.ML for full HOL sessions (the default,
   without --bare). It:
   - Opens bossLib for convenience
   - Installs additional pretty-printers (simpsets, defns, compsets, etc.)

   For bare HOL sessions, this file is not loaded.

   For Moscow ML, the equivalent is tools/end-init-boss.sml.
*)

(* this is an -*- sml -*- file *)
val () = PolyML.print_depth 0;

open bossLib  (* Any others? *)

(*
This uses quietdec, so it doesn't work in PolyML
val _ = use (HOLDIR ^ "/src/proofman/expandq");
val _ = use (HOLDIR ^ "/src/datatype/Interactive");
*)

local
  fun pp2polypp (ppfn: 'b PP.pprinter) =
      fn depth => fn printArgTypes => fn e: 'b => ppfn e
  fun pp_transform d _ (t : clauses.transform) =
    case t of
      clauses.Conversion c =>
        PolyML.PrettyBlock
          (2, false, [],
           [PolyML.PrettyString "Conversion", PolyML.PrettyBreak (1, 0),
            PolyML.prettyRepresentation (c, d)])
    | clauses.RRules l =>
        PolyML.PrettyBlock
          (2, false, [],
           [PolyML.PrettyString "RRules", PolyML.PrettyBreak (1, 0),
            PolyML.prettyRepresentation (l, d)])
in
  val () =
    ( if !heapname <> SOME Systeml.DEFAULT_STATE then
        let
          val hnm = case !heapname of SOME s => s | NONE => "bare poly"
        in
          TextIO.output
            (TextIO.stdOut, "[In non-standard heap: " ^ hnm ^ "]\n")
        end
      else ()
    ; Feedback.set_trace "metis" 1
    ; Feedback.set_trace "meson" 1
    ; PolyML.addPrettyPrinter (pp2polypp simpLib.pp_ssfrag)
    ; PolyML.addPrettyPrinter (pp2polypp DefnBase.pp_defn)
    ; PolyML.addPrettyPrinter (pp2polypp simpLib.pp_simpset)
    ; PolyML.addPrettyPrinter (pp2polypp computeLib.pp_compset)
    ; PolyML.addPrettyPrinter pp_transform
    ; PolyML.print_depth 100
    )
end
