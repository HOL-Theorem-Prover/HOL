(* ===================================================================== *)
(* FILE          : holyHammer.sml                                        *)
(* DESCRIPTION   : Premise selection and external provers                *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck        *)
(* DATE          : 2015                                                  *)
(* ===================================================================== *)

structure holyHammer :> holyHammer =
struct

open HolKernel boolLib Thread aiLib smlRedirect mlFeature mlThmData
  mlNearestNeighbor

val ERR = mk_HOL_ERR "holyHammer"

datatype prover = datatype hhConfig.prover

fun set_timeout n = hhConfig.hh_set ("timeout", Int.toString n)

fun no_prover caller =
  let
    val message =
      "no prover binary found; run tools/download-provers or put a " ^
      "supported prover binary on PATH"
    val _ = print_endline ("HolyHammer: " ^ message)
  in
    raise ERR caller message
  end

fun available_provers caller provers =
  let
    fun available prover =
      let val config = hhProver.config_of prover in
        case hhProver.find_exec config of
            SOME _ => true
          | NONE =>
              (print_endline ("no binary for " ^ #name config); false)
      end
    val available = filter available provers
  in
    if null available then no_prover caller else available
  end

(* Deliberately a function: state_dir needs HOME and creates directories,
   so binding it at structure-initialisation time would make merely loading
   holyHammer fail wherever HOME is unset or the home is read-only. *)
fun workdir () = hhConfig.state_dir ()

val attrib =
  [Thread.InterruptState Thread.InterruptAsynch,
   Thread.EnableBroadcastInterrupt true]

fun interactive_options provers =
  hhConfig.snapshot_with
    [("max_proofs", "1"),
     ("provers", String.concatWith " " (map hhConfig.prover_name provers))]

type unverified = hhProver.slice * string list

(* A record of the proofs the schedule announced, plus, with the verbose
   option, its own reporting.  Otherwise a call prints only its outcome. *)
fun progress (options : hhConfig.hh_options) found event =
  (case event of
       hhSchedule.ProofFound pair => found := pair :: !found
     | _ => ();
   if #verbose options then hhSchedule.default_progress event else ())

val problem_path = hhSchedule.problem_path

fun output_paths directory prover =
  let
    val prefix = #name (hhProver.config_of prover) ^ "-"
    fun is_output name =
      String.isPrefix prefix name andalso String.isSuffix ".out" name
  in
    map (fn name => OS.Path.concat (directory, name))
      (List.filter is_output (hhConfig.directory_names directory))
  end

fun unverified_line root debug_dir (slice : hhProver.slice, lemmas) =
  let
    val name = #name (hhProver.config_of (#prover slice))
    val heading =
      "  " ^ name ^ ": [" ^ String.concatWith ", " lemmas ^ "]"
  in
    case debug_dir of
        NONE => heading
      | SOME directory =>
          let
            val outputs = output_paths directory (#prover slice)
            val output_text =
              if null outputs then
                OS.Path.concat (directory, name ^ "-*.out")
              else String.concatWith ", " outputs
          in
            heading ^ "\n    problem: " ^ problem_path root slice ^
            "\n    output: " ^ output_text
          end
  end

fun failed caller root options found =
  if null found then
    (print_endline "  ATPs could not find a proof";
     raise ERR caller "ATPs could not find a proof")
  else
    let
      val message =
        "ATPs found proofs, but reconstruction failed for:\n" ^
        String.concatWith "\n"
          (map (unverified_line root (#debug_dir options)) (List.rev found))
    in
      print_endline ("  " ^ message);
      raise ERR caller message
    end

fun run_schedule caller parent options rankings goal =
  hhSchedule.with_problem_dir parent options (fn root =>
    let
      val found = ref ([] : unverified list)
      val result = hhSchedule.run_in root
        {options = options, goal = goal, rankings = rankings,
         progress = SOME (progress options found)}
    in
      case #suggestions result of
          suggestion :: _ => suggestion
        | [] => failed caller root options (!found)
    end)

fun explicit_rankings schedule premises =
  map (fn (filter, _) => (filter, premises))
    (hhSlice.filter_maxima schedule)

fun options_for caller provers =
  interactive_options (available_provers caller provers)

(* The last thing a successful interactive call prints: the verified
   tactic, with what to do with it, after every slice has reported. *)
fun announce instruction (suggestion : hhSchedule.suggestion) =
  print_endline ("\n" ^ instruction ^ "\n  " ^ #stac suggestion)

fun hh_pb directory provers premises goal =
  let
    val options = options_for "hh_pb" provers
    val schedule = hhSlice.mk_schedule options
    val suggestion = run_schedule "hh_pb" directory options
      (explicit_rankings schedule premises) goal
  in
    announce "Replace `hh_pb` with:" suggestion;
    #tac suggestion
  end

fun main_hh_result caller directory thmdata goal =
  let
    val options = options_for caller (#provers (hhConfig.snapshot ()))
    val schedule = hhSlice.mk_schedule options
    val context = hhLearn.create_context thmdata
    fun rank (filter, maximum) =
      (filter, hhLearn.rank context
        {filter = filter, pool = NONE, goal = goal, n = maximum})
    val rankings = map rank (hhSlice.filter_maxima schedule)
  in
    run_schedule caller directory options rankings goal
  end

fun main_hh directory thmdata goal =
  #tac (main_hh_result "main_hh" directory thmdata goal)

fun main_hh_lemmas directory thmdata goal =
  SOME (#lemmas (main_hh_result "main_hh_lemmas" directory thmdata goal))
  handle HOL_ERR _ => NONE

fun has_boolty x = type_of x = bool
fun has_boolty_goal goal = all has_boolty (snd goal :: fst goal)

fun hh_suggestion goal =
  if not (has_boolty_goal goal) then
    raise ERR "hh_goal" "a term is not of type bool"
  else
    let val thmdata = hidef create_thmdata () in
      main_hh_result "main_hh" (workdir ()) thmdata goal
    end

fun hh_goal goal = #tac (hh_suggestion goal)

fun hh_fork goal = Thread.fork (fn () => ignore (hh_goal goal), attrib)

(* hidef has to span the context application, which runs the replay *)
fun hh goal ctxt =
  let
    val suggestion = hh_suggestion goal
    val result = hidef (#tac suggestion goal) ctxt
  in
    announce "Replace `hh` with:" suggestion;
    result
  end

fun holyhammer tm =
  let
    val suggestion = hh_suggestion ([], tm)
    val thm = hidef TAC_PROOF (([], tm), #tac suggestion)
  in
    announce "Prove the statement in a script with:" suggestion;
    thm
  end

end
