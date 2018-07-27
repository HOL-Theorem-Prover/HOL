structure RL_Goal_manager :> RL_Goal_manager = struct

open HolKernel boolLib

(* TODO: move to Lib? *)
fun rotate_list [] = [] | rotate_list (x::xs) = xs @ [x]
fun unrotate_list ls = Lib.uncurry (Lib.C Lib.cons) (Lib.front_last ls)
(*
rotate_list [1,2,3]
unrotate_list [1,2,3]
unrotate_list (rotate_list [1,2,3])
unrotate_list (rotate_list [2])
*)
(* -- *)

(* TODO: move? or take from elsewhere? *)
fun goal_to_string((asl, w):goal) =
  "[" ^ (String.concatWith "," (List.map term_to_string asl)) ^ "] ?- " ^ (term_to_string w)
(* -- *)

datatype goal_term = LEAF of goal
                   | NODE of validation * goal_term list

fun is_LEAF (LEAF _) = true
  | is_LEAF _ = false

fun dest_LEAF (LEAF l) = l
  | dest_LEAF _ = failwith"dest_LEAF: not a LEAF"

datatype goal_state = GOAL of goal_term
                    | ERROR of string
                    | SUCCESS of thm

fun initial_goal_state g = GOAL (LEAF g)

datatype observed_goal_state =
    Observed_goals of goal list
  | Observed_success of thm
  | Observed_error of string

fun observed_goal_state_to_string(Observed_goals gs) =
      "GOAL LIST: " ^ String.concatWith "\n\n" (List.map goal_to_string (List.rev gs))
  | observed_goal_state_to_string(Observed_success thm) =
      "SUCCESS: " ^ thm_to_string thm
  | observed_goal_state_to_string(Observed_error msg) =
      "TACTIC ERROR: " ^ msg

fun get_observed_goal_state (GOAL (LEAF g)) = Observed_goals [g]
  | get_observed_goal_state (GOAL (NODE (_,gs))) =
      if List.all is_LEAF gs then
        Observed_goals (List.map dest_LEAF gs)
      else get_observed_goal_state (GOAL (List.hd gs)) (* should not be empty *)
  | get_observed_goal_state (ERROR msg) = Observed_error msg
  | get_observed_goal_state (SUCCESS thm) = Observed_success thm

fun rotate_goal_term (NODE (v,gs)) =
  if List.null gs then NONE else
  if List.all is_LEAF gs andalso not (List.null (List.tl gs)) then
    SOME (NODE ((fn ls => v (unrotate_list ls)), rotate_list gs))
  else
    (case rotate_goal_term (List.hd gs) of NONE => NONE
        | SOME g1 => SOME (NODE (v, g1::(List.tl gs))))
  | rotate_goal_term _ = NONE

fun rotate_goal_state (GOAL tm) = Option.map GOAL (rotate_goal_term tm)
  | rotate_goal_state _ = NONE

fun apply_tactic_goal_term (tactic:bossLib.tactic) (LEAF g) =
  (let
    val (subgoals,v) = tttTimeout.timeOut 0.1 tactic g
  in
    if List.null subgoals then
      SUCCESS (v [])
    else
      GOAL (NODE (v, List.map LEAF subgoals))
  end
  handle SML90.Interrupt => raise SML90.Interrupt
         | tttTimeout.TacTimeOut => ERROR ("tactic application timeout")
         | e => ERROR (exnMessage e))
|   apply_tactic_goal_term tactic (NODE (v, gs)) =
  if List.null gs then failwith("node with no subgoals")
  else case apply_tactic_goal_term tactic (List.hd gs) of
    ERROR msg => ERROR msg
  | GOAL gtm => GOAL (NODE (v, (gtm::(List.tl gs))))
  | SUCCESS th1 =>
      if List.null (List.tl gs) then
        SUCCESS (v [th1])
      else
        GOAL (NODE ((fn ls => v (th1::ls)), List.tl gs))

fun apply_tactic (t:bossLib.tactic) (GOAL gtm) = apply_tactic_goal_term t gtm
  | apply_tactic _ _ = failwith("apply tactic to non-goal")

end
