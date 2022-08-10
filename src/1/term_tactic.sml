structure term_tactic :> term_tactic =
struct

open HolKernel Feedback Tactical
type tactic = Tactic.tactic
type term_tactic = Term.term -> tactic

fun goal_term ttac (g as (_,w)) = ttac w g
fun subtm_assum_term t ttac (g as (asl,w)) =
    case List.find (free_in t) asl of
        NONE => raise mk_HOL_ERR "term_tactic" "subtm_assum_term"
                      ("No assumption contains " ^
                       Parse.term_to_string t ^ " free")
      | SOME asm => ttac asm g

fun first_assum_term ttac (g as (asl,_)) = MAP_FIRST ttac asl g
fun last_assum_term ttac (g as (asl,_)) = MAP_FIRST ttac (List.rev asl) g
fun first_fv_term ttac (g as (asl,w)) =
    MAP_FIRST ttac (free_varsl (w::asl)) g
fun fv_term ttac (g as (asl,w)) =
    let
      fun recurse l =
          case l of
              [] => raise mk_HOL_ERR "term_tactic" "fv_term"
                          "No free variables in goal"
            | t::ts => case free_vars t of
                           [] => recurse ts
                         | v::_ => ttac v g
    in
      recurse (w::asl)
    end

end (* struct *)
