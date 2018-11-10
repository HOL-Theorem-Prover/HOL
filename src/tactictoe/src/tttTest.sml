(* =========================================================================
   Evaluation (to move to tttTest)
   ========================================================================= *)
(*
(* Evaluated theorems *)
val ttt_evprove_flag  = ref false
val ttt_evlet_flag    = ref false

val one_in_option = ref NONE
val one_in_counter = ref 0
fun one_in_n () = case !one_in_option of
    NONE => true
  | SOME (offset,freq) =>
    let val b = (!one_in_counter) mod freq = offset in
      (incr one_in_counter; b)
    end

val evaluation_filter = ref (fn s:string => true)

(* Evaluate Eprover instead of TacticToe *)
val eprover_eval_flag = ref false 
val eprover_save_flag = ref false
*)
