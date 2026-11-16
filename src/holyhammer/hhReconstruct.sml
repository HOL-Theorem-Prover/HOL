(* ===================================================================== *)
(* FILE          : hhReconstruct.sml                                     *)
(* DESCRIPTION   : Reconstruct a proof from the lemmas given by an ATP   *)
(*                 and optionally minimize them.                         *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure hhReconstruct :> hhReconstruct =
struct

open HolKernel Dep Tag boolLib aiLib smlExecute smlTimeout smlRedirect
  mlThmData

val ERR = mk_HOL_ERR "hhReconstruct"

(* --------------------------------------------------------------------------
   Settings
   -------------------------------------------------------------------------- *)

val reconstruct_flag = ref true
val minimization_timeout = ref 1.0
val reconstruction_timeout = ref 1.0

(*----------------------------------------------------------------------------
   Minimization and pretty-printing
 -----------------------------------------------------------------------------*)

val TC_OFF = HOLFlags.with_bflags [(Parse.show_typecheck_errors, false)]
(* the trace setting, the timeout and the handler all have to span the
   context application, which is when the tactic does its work *)
fun timeout_tactic t tac g =
  let val ctxt = Context.snapshot() in
    SOME (fst (timeout t (TC_OFF (Lib.C tac ctxt)) g))
  end
  handle Interrupt => raise Interrupt | _ => NONE

type settings =
  {minimize : bool, preplay_timeout : real, minimize_timeout : real,
   minimize_deadline : Time.time option}

type reconstruction = {stac : string, tac : tactic, t_replay : real}

(* Compiles stac and runs it on g with the time limit t.  Returns the
   tactic and the replay time when it proves g. *)
fun replay t stac g =
  let
    val tac = tactic_of_sml 1.0 stac
    val (result, time) = add_time (timeout_tactic t tac) g
  in
    case result of
        SOME [] => SOME (tac, time)
      | _ => NONE
  end
  handle Interrupt => raise Interrupt | _ => NONE

fun prettify_stac stac =
  (smlPrettify.smart_space o smlPrettify.elim_infix o
   smlPrettify.elim_struct o smlPrettify.elim_par o
   smlPrettify.elim_dbfetch o smlLexer.partial_sml_lexer) stac

(* As in Sledgehammer's minimiser, an attempt may take at most twice the
   time of the last successful replay, plus some slack; minimize_timeout
   caps it.  A failing attempt, the common case for a needed fact,
   otherwise runs out the whole minimize_timeout. *)
val attempt_factor = 2.0
val attempt_slack = 0.2

fun attempt_timeout minimize_timeout t =
  Real.min (minimize_timeout, attempt_factor * t + attempt_slack)

fun out_of_time NONE = false
  | out_of_time (SOME deadline) = Time.>= (Time.now (), deadline)

(* Drops the lemmas one at a time, keeping a lemma when the replay
   without it fails.  Every intermediate list is verified, so stopping at
   the deadline returns a verified list. *)
fun minimize_lemmas minimize_timeout deadline g lemmas best =
  let
    fun loop kept [] best = (kept, best)
      | loop kept (lemma :: rest) (best as (_, time)) =
          if out_of_time deadline then (kept @ lemma :: rest, best)
          else
            let val candidate = kept @ rest in
              case replay (attempt_timeout minimize_timeout time)
                     (mk_metis_call candidate) g of
                  SOME found => loop kept rest found
                | NONE => loop (kept @ [lemma]) rest best
            end
  in
    loop [] lemmas best
  end

(* A permutative equation, such as commutativity, has sides that are
   instances of each other but not equal.  Metis cannot orient it, and
   one such fact can keep it from replaying a list it proves in
   milliseconds without it: the provers' list for the step case of
   LENGTH (flatten t) = size t replays in 0.2 s without ADD_COMM and not
   in 10 s with it. *)
fun is_permutative_eq tm =
  let val (l, r) = dest_eq (snd (strip_forall tm)) in
    not (aconv l r) andalso can (match_term l) r andalso
    can (match_term r) l
  end
  handle HOL_ERR _ => false

fun is_permutative_lemma lemma =
  case thm_of_name lemma of
      SOME (_, th) =>
        List.exists is_permutative_eq
          (strip_conj (snd (strip_forall (concl th))))
    | NONE => false
  handle Interrupt => raise Interrupt | _ => false

(* The lists Metis is asked to replay, in order: the full list, then,
   if that fails, the list without its permutative equations.  Each try
   costs at most preplay_timeout, so a list that cannot be replayed still
   fails quickly. *)
fun preplay preplay_timeout lemmas g =
  case replay preplay_timeout (mk_metis_call lemmas) g of
      SOME found => SOME (lemmas, found)
    | NONE =>
        let
          val (permutative, others) =
            List.partition is_permutative_lemma lemmas
        in
          if null permutative then NONE
          else
            Option.map (fn found => (others, found))
              (replay preplay_timeout (mk_metis_call others) g)
        end

fun hh_reconstruct_with ({minimize, preplay_timeout, minimize_timeout,
                          minimize_deadline} : settings) lemmas g =
  if not (!reconstruct_flag)
  then (print_endline (mk_metis_call lemmas);
        raise ERR "hh_minimize" "reconstruction off")
  else
    let
      fun result stac (tac, time) : reconstruction =
        {stac = stac, tac = tac, t_replay = time}
    in
      (* Replay before minimising: a list Metis cannot replay fails at
         once instead of being minimised attempt by attempt. *)
      case preplay preplay_timeout lemmas g of
          NONE => raise ERR "hh_reconstruct" "reconstruction failed"
        | SOME (replayed, full) =>
            if not minimize then result (mk_metis_call replayed) full
            else
              let
                val (kept, best) = minimize_lemmas minimize_timeout
                  minimize_deadline g replayed full
                val raw = mk_metis_call kept
                val pretty = prettify_stac raw
              in
                (* The short names are resolved in the current namespace,
                   so the printed form is verified on its own. *)
                case replay preplay_timeout pretty g of
                    SOME found => result pretty found
                  | NONE => result raw best
              end
    end

fun hh_reconstruct lemmas g =
  let
    val {stac, tac, ...} =
      hh_reconstruct_with
        {minimize = true, preplay_timeout = !reconstruction_timeout,
         minimize_timeout = !minimization_timeout,
         minimize_deadline = NONE} lemmas g
  in
    (stac, tac)
  end

end
