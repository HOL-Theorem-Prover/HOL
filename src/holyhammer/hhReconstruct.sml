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
val minimization_timeout = ref hhConfig.default_minimize_timeout
val reconstruction_timeout = ref hhConfig.default_preplay_timeout

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

(* A lemma is renamed to its bare name, so that the call uses the name,
   where the top-level ML value of that name states the same theorem.
   This matters in two cases.  A theorem of the current theory has no
   Theory structure yet, so mk_metis_call fetches it from DB, which
   prints as fetch "thy" "name"; Theorem and Definition bind its name in
   a script.  And a theory may re-export an ancestor's theorem under the
   same name, as rich_list does MAP_REVERSE: the bare name then denotes
   the copy, which the prettifier, comparing pointers, does not
   recognise.  The value's type is looked up before it is compiled, so
   that a name bound to something else prints no error. *)
fun bound_name lemma =
  let
    val (thy, name) = split_string "Theory." lemma
    fun same th stored =
      aconv (concl th) (concl stored) andalso
      HOLset.equal (hypset th, hypset stored)
  in
    case #lookupVal PolyML.globalNameSpace name of
        NONE => lemma
      | SOME value =>
          if not (is_thm_value [(name, value)] name) then lemma
          else
            case thm_of_sml name of
                SOME (_, th) =>
                  if same th (DB.fetch thy name)
                  then namespace_tag ^ "Theory." ^ name
                  else lemma
              | NONE => lemma
  end
  handle Interrupt => raise Interrupt | _ => lemma

(* An attempt may take at most twice the time of the fastest verified
   replay so far in this minimisation, plus some slack; minimize_timeout
   caps it.  A failing attempt, the common case for a needed fact,
   otherwise runs out the whole minimize_timeout.  The fastest replay
   starts as the verified replay the minimisation starts from (the full
   list, or the list without its permutative equations) and improves
   when a shorter list replays faster.  Sledgehammer's minimiser bases
   the limit on the last successful replay, but then a marginal success
   (an attempt that only just fits) raises the limit of every later
   attempt, and the next ones run out a longer limit: the time of a
   minimisation depends on whether one attempt beats its limit by a few
   milliseconds.  With the minimum the limit never rises. *)
val attempt_factor = 2.0
val attempt_slack = 0.2

fun attempt_timeout minimize_timeout t =
  Real.min (minimize_timeout, attempt_factor * t + attempt_slack)

fun out_of_time NONE = false
  | out_of_time (SOME deadline) = Time.>= (Time.now (), deadline)

(* Drops the lemmas one at a time, keeping a lemma when the replay
   without it fails.  try limit candidate is the replay, within limit
   seconds, of the candidate list, and gives its tactic and time when it
   succeeds.  The limit of an attempt is attempt_timeout of the fastest
   replay so far (see above), starting from the time of best, the
   verified result the minimisation starts from.  Every intermediate
   list is verified, so stopping at the deadline returns a verified
   list. *)
fun drop_one_minimize try minimize_timeout deadline lemmas best =
  let
    fun loop kept [] best _ = (kept, best)
      | loop kept (lemma :: rest) best t_min =
          if out_of_time deadline then (kept @ lemma :: rest, best)
          else
            case try (attempt_timeout minimize_timeout t_min)
                     (kept @ rest) of
                SOME (found as (_, t)) =>
                  loop kept rest found (Real.min (t_min, t))
              | NONE => loop (kept @ [lemma]) rest best t_min
  in
    loop [] lemmas best (snd best)
  end

fun minimize_lemmas minimize_timeout deadline g lemmas best =
  drop_one_minimize
    (fn limit => fn candidate => replay limit (mk_metis_call candidate) g)
    minimize_timeout deadline lemmas best

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
                val pretty =
                  psMinimize.unsafe_prettify_stac
                    (mk_metis_call (map bound_name kept))
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
