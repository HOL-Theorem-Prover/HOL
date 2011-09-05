(* this is an -*- sml -*- file *)
val _ = PolyML.print_depth 0;

val _ = if heapname <> "hol.builder" then
          TextIO.output(TextIO.stdOut, "[In non-standard heap: "^heapname^"]\n")
        else ()

local (* install prettyprinters for simpsets and ssfrags *)
fun pp2polypp (f : PP.ppstream -> 'a -> unit)
              (putString : string -> unit,
               beginBlock : int * bool -> unit,
               spaceBlock : int * int -> unit,
               endBlock : unit -> unit)
              (dpth_limit : int)
              recursive_print
              (e : 'a) =
    putString (PP.pp_to_string (!Globals.linewidth) f e);
fun with_pp ppfn pps x =
    Parse.respect_width_ref Globals.linewidth ppfn pps x handle e => Raise e
in
  val _ = PolyML.install_pp (pp2polypp (with_pp simpLib.pp_ssfrag));
  val _ = PolyML.install_pp (pp2polypp (with_pp simpLib.pp_simpset));
  val _ = PolyML.install_pp (pp2polypp (with_pp computeLib.pp_compset));
end;

open bossLib;  (* Any others? *)

(*
This uses quietdec, so it doesn't work in PolyML
val _ = use (HOLDIR^"/src/proofman/expandq");
*)
(* val _ = use (HOLDIR^"/src/datatype/Interactive"); *)

val Hol_datatype =
  Lib.with_flag
    (Feedback.emit_WARNING,false)
    bossLib.Hol_datatype;

val _ = set_trace "metis" 1
val _ = set_trace "meson" 1

val _ = PolyML.print_depth 100;
