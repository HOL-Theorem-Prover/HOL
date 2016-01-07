(* this is an -*- sml -*- file *)
val () = PolyML.print_depth 0;

open bossLib  (* Any others? *)

(*
This uses quietdec, so it doesn't work in PolyML
val _ = use (HOLDIR ^ "/src/proofman/expandq");
val _ = use (HOLDIR ^ "/src/datatype/Interactive");
*)

local
  fun pp2polypp (ppfn: PP.ppstream -> 'b -> unit) =
    let
      fun f pps x = Parse.respect_width_ref Globals.linewidth ppfn pps x
                    handle e => Raise e
    in
      fn depth => fn printArgTypes => fn e: 'b =>
        PolyML.PrettyString (PP.pp_to_string (!Globals.linewidth) f e)
    end
in
  val () =
    ( if heapname <> Systeml.DEFAULT_STATE then
        TextIO.output
          (TextIO.stdOut, "[In non-standard heap: " ^ heapname ^ "]\n")
      else ()
    ; Feedback.set_trace "metis" 1
    ; Feedback.set_trace "meson" 1
    ; PolyML.addPrettyPrinter (pp2polypp simpLib.pp_ssfrag)
    ; PolyML.addPrettyPrinter (pp2polypp simpLib.pp_simpset)
    ; PolyML.addPrettyPrinter (pp2polypp computeLib.pp_compset)
    ; PolyML.print_depth 100
    )
end
