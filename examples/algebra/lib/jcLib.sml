structure jcLib :> jcLib =
struct

open HolKernel boolLib Abbrev Tactic Tactical BasicProvers simpLib
open Rewrite bossLib Thm_cont

(* existing strip_tac looks like

    gen_tac ORELSE conj_tac ORELSE disch_then strip_assume_tac

*)

(* disch_then : thm_tactic -> tactic
     =          (thm -> tactic) -> tactic
*)

fun stripDup ths =
    FIRST [gen_tac, conj_tac,
           disch_then (fn th => strip_assume_tac th >>
                                strip_assume_tac (REWRITE_RULE ths th))]

val _ = Feedback.set_trace "Theory.allow_rebinds" 1


end
