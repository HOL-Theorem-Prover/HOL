(* this is an -*- sml -*- file *)
val () = PolyML.print_depth 0;

open bossLib  (* Any others? *)

(*
This uses quietdec, so it doesn't work in PolyML
val _ = use (HOLDIR ^ "/src/proofman/expandq");
val _ = use (HOLDIR ^ "/src/datatype/Interactive");
*)

val () =
  ( if heapname <> "hol.builder" then
      TextIO.output
        (TextIO.stdOut, "[In non-standard heap: " ^ heapname ^ "]\n")
    else ()
  ; set_trace "metis" 1
  ; set_trace "meson" 1
  ; PolyML.print_depth 100
  )
