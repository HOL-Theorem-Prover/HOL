(* ===================================================================== *)
(* FILE          : Msg.sml                                               *)
(* DESCRIPTION   : Building messages out of HOL values.                  *)
(* ===================================================================== *)

structure Msg :> Msg =
struct

open HOLmessage

type term = Term.term
type hol_type = Type.hol_type
type thm = Thm.thm
type message = HOLmessage.message

(* `Parse.pp_term' reads `Parse.current_backend' when it builds the
   pretty, and the suspension is not run until someone renders the
   message -- so the back end, and the width it is laid out at, are the
   reader's choice rather than the raiser's.  That is the whole trick:
   one message serves a colour terminal, EmitTeX and the LSP without
   any of them agreeing in advance. *)
fun tm t = pp (fn () => Parse.pp_term t)
fun ty t = pp (fn () => Parse.pp_type t)
fun th t = pp (fn () => Parse.pp_thm t)

(* `toString' must agree with `Parse.term_to_string', which pins a raw
   back end and lays out at `Globals.linewidth'.  Installing that here
   rather than in `HOLmessage' keeps the knowledge of back ends in
   `src/parse', where it belongs: the prekernel cannot name one. *)
val () = HOLmessage.plain_renderer :=
  (fn f => Lib.with_flag (Parse.current_backend, PPBackEnd.raw_terminal)
             (fn () => HOLPP.pp_to_string (!Globals.linewidth)
                                          (fn () => f ()) ()) ())

fun segments m =
  PPBackEnd.lsp_segments
    (Lib.with_flag (Parse.current_backend, PPBackEnd.lsp_terminal)
       (HOLPP.pp_to_string (!Globals.linewidth) toPretty) m)

end  (* Msg *)
