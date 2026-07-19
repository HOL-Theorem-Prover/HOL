(*  Title:      HolRefute/Refute_ModelFinder.sml
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Driver for the HOL4 Refute model finder.  The control flow is a port of
Nitpick's pick_them_nits_in_term, specialized to the M3 feature set. *)

signature REFUTE_MODEL_FINDER = sig
  val kodkod_backend : Refute_Core.backend
  val register_backends : unit -> unit
end

structure Refute_ModelFinder :> REFUTE_MODEL_FINDER = struct

open Portable Feedback
infix |>

structure KK = Refute_Forl
structure MFH = Refute_ModelFinder_HOL
structure MFK = Refute_ModelFinder_Kodkod
structure MFM = Refute_ModelFinder_Model
structure MFN = Refute_ModelFinder_Names
structure MFNT = Refute_ModelFinder_Nut
structure MFP = Refute_ModelFinder_Preproc
structure MFS = Refute_ModelFinder_Scope
structure MFU = Refute_ModelFinder_Util

type term = Term.term
type hol_type = Type.hol_type
type rich_problem = MFK.rich_problem

val max_unsound_delay_ms = 200
val max_unsound_delay_percent = 2
val deadline_margin = 1.0

fun elapsed_msec start =
  LargeInt.toInt (Time.toMilliseconds (Time.now () - start))
  handle _ => 0

fun remaining deadline =
  if Time.now () >= deadline then Time.zeroTime
  else deadline - Time.now ()

fun check_deadline deadline =
  if Time.now () >= deadline then raise Timeout.TIMEOUT Time.zeroTime
  else ()

fun unsound_delay deadline =
  Int.max (0, Int.min (max_unsound_delay_ms,
    LargeInt.toInt (Time.toMilliseconds (remaining deadline)) *
      max_unsound_delay_percent div 100))
  handle _ => 0

fun same_type left right = Type.compare (left, right) = EQUAL

fun member_type ty = List.exists (same_type ty)

fun add_type ty types =
  if member_type ty types then types else ty :: types

fun type_arguments ty =
  if Type.is_vartype ty then []
  else #Args (Type.dest_thy_type ty)

fun ground_types context terms =
  let
    fun add ty types =
      if MFH.is_fun_type ty orelse MFH.is_pair_type ty orelse
         pred_setSyntax.is_set_type ty then
        List.foldl (fn (argument, result) => add argument result)
          types (type_arguments ty)
      else if MFH.is_boolean_type ty orelse member_type ty types then
        types
      else
        let
          val types = add_type ty types
          val constructor_types = List.concat
            (map MFH.constructor_arg_types
              (MFH.data_type_constrs context ty))
          val nested =
            if null constructor_types then type_arguments ty
            else constructor_types
        in
          List.foldl (fn (argument, result) => add argument result)
            types nested
        end
    fun add_term term types = add (Term.type_of term) types
    fun add_all_subterms term types =
      List.foldl (fn (subterm, result) => add_term subterm result)
        types (HolKernel.find_terms (fn _ => true) term)
  in
    Listsort.sort Type.compare
      (List.foldl (fn (term, result) => add_all_subterms term result)
        [] terms)
  end

fun aconv_member term = List.exists (Term.aconv term)

fun distinct_terms terms =
  List.foldl (fn (term, result) =>
    if aconv_member term result then result else result @ [term]) [] terms

fun free_variables terms =
  distinct_terms (List.concat (map Term.free_vars_lr terms))

fun inductive_predicate term =
  let
    val table = IndDefLib.rule_induction_map ()
    fun is_inductive constant =
      Option.isSome (KNametab.lookup table (MFH.const_key constant))
      handle HOL_ERR _ => false
  in
    List.find is_inductive (HolKernel.find_terms Term.is_const term)
  end

fun inductive_reason term =
  Option.map (fn constant =>
    "inductive predicate " ^ Parse.term_to_string constant ^
    ": unsupported until M4") (inductive_predicate term)

fun none_true assignments =
  List.all (fn (_, value) => value <> SOME true) assignments

fun authenticity_reasons (mf : Refute_Core.mf_config)
      got_all_mono_user_axioms no_poly_user_axioms =
  if not no_poly_user_axioms then
    ["polymorphic axioms prevent an authenticity guarantee"]
  else
    let
      val options =
        (if got_all_mono_user_axioms then []
         else ["\"user_axioms\" set to \"true\""]) @
        (if none_true (#wf mf) then []
         else ["\"wf\" set to \"smart\" or \"false\""]) @
        (if #total_consts mf = SOME true then
           ["\"total_consts\" set to \"smart\" or \"false\""]
         else [])
    in
      MFM.try_again_reasons options
    end

fun exact_totality all_types (scope : MFS.scope) =
  List.all (MFS.is_exact_type (#data_types scope) true) all_types

fun type_name ty = Parse.type_to_string ty

fun scope_comment (scope : MFS.scope) =
  String.concatWith ", " (map (fn (ty, card) =>
    "card " ^ type_name ty ^ " = " ^ Int.toString card)
    (#card_assigns scope))

fun deep_data_types all_types sel_names =
  let
    fun selector_domain name =
      Option.map #1 (Lib.total Type.dom_rng (MFNT.type_of name))
    fun selected ty = List.exists (fn name =>
      case selector_domain name of
          SOME domain => same_type ty domain
        | NONE => false) sel_names
  in
    List.filter (fn ty => MFH.is_data_type ty andalso
      (same_type ty ``:unit`` orelse selected ty)) all_types
  end

fun actual_solver (mf : Refute_Core.mf_config) =
  if #sat_solver mf = "smart" then
    Refute_ForlSat.smart_sat_solver_name false
  else
    #sat_solver mf

fun solver_arguments deadline solver =
  #2 (Refute_ForlSat.sat_solver_spec (remaining deadline) solver)

fun problem_for_scope deadline (mf : Refute_Core.mf_config)
      all_types solver free_names nonsel_names nondef_us def_us
      unsound scope =
  let
    val effective_total_consts =
      Option.getOpt (#total_consts mf, exact_totality all_types scope)
    val params : MFK.assembly_params =
      {debug = #debug mf,
       peephole_optim = #peephole_optim mf,
       total_consts = effective_total_consts,
       datatype_sym_break = #datatype_sym_break mf,
       kodkod_sym_break = #kodkod_sym_break mf,
       comment = scope_comment scope,
       solver = solver_arguments deadline solver,
       unsound_delay = unsound_delay deadline,
       free_names = free_names,
       nonsel_names = nonsel_names,
       nondef_us = nondef_us,
       def_us = def_us}
  in
    MFK.assemble_problem params unsound scope
  end

fun metadata (_, metadata : MFK.problem_metadata) = metadata
fun raw_problem (problem, _ : MFK.problem_metadata) = problem

fun rich_problems_equivalent (left : rich_problem, right : rich_problem) =
  #unsound (metadata left) = #unsound (metadata right) andalso
  MFS.scopes_equivalent
    (#scope (metadata left), #scope (metadata right)) andalso
  KK.problems_equivalent (raw_problem left, raw_problem right)

fun rich_member problem = List.exists (fn other =>
  rich_problems_equivalent (problem, other))

fun take_at_most count values =
  let
    fun take 0 _ result = rev result
      | take _ [] result = rev result
      | take remaining (value :: rest) result =
          take (remaining - 1) rest (value :: result)
  in
    take (Int.max (0, count)) values []
  end

fun distinct_ints values =
  let
    fun add (value, result) =
      if List.exists (fn old => old = value) result then result
      else value :: result
  in
    Listsort.sort Int.compare (List.foldl add [] values)
  end

fun certainty_is_genuine Refute_Core.Genuine = true
  | certainty_is_genuine _ = false

fun certainty_is_potential (Refute_Core.Potential _) = true
  | certainty_is_potential _ = false

fun replace_stats stats (cex : Refute_Core.counterexample) =
  {backend = #backend cex, substrate = #substrate cex,
   certainty = #certainty cex, bindings = #bindings cex,
   evals = #evals cex, cert = #cert cex, scope = #scope cex,
   model = #model cex, stats = stats}

fun run_instance deadline started (config : Refute_Core.config)
      (instance : Refute_Core.instance) =
  let
    val mf = #mf config
    val original = #original instance
    val negated =
      if #falsify mf then boolSyntax.mk_imp (original, boolSyntax.F)
      else original
    val context = MFH.make_context mf (#evals instance)
    val (nondef_ts, def_ts, got_all_mono_user_axioms,
         no_poly_user_axioms) =
      MFP.preprocess_formulas context [] negated
    val nondef_us = map (MFNT.nut_from_term context MFNT.Eq) nondef_ts
    val def_us = map (MFNT.nut_from_term context MFNT.DefEq) def_ts
    val (free_names, const_names) =
      List.foldl (fn (nut, names) =>
        MFNT.add_free_and_const_names nut names)
        ([], []) (nondef_us @ def_us)
    val (sel_names, nonsel_names) = List.partition
      (MFN.is_sel o MFNT.nickname_of) const_names
    val all_types = ground_types context (nondef_ts @ def_ts)
    val unique_scope = List.all (fn (_, values) => length values = 1)
      (#card mf)
    val (mono_types, nonmono_types) =
      if unique_scope then (all_types, [])
      else MFS.mono_partition (#mono mf) all_types
    val deep_types = deep_data_types all_types sel_names
    val (skipped, scopes) = MFS.all_scopes context (#card mf) (#max mf)
      mono_types nonmono_types deep_types
    val batch_size =
      if #debug mf then 1 else Int.max (1, #batch_size mf)
    val batches = MFU.chunk_list batch_size scopes
    val solver = actual_solver mf
    val real_frees = free_variables [original]
    val executable = not (Option.isSome (#qc_gate instance)) andalso
      #falsify mf
    val genuine_formula = MFM.genuine_means_genuine
      {got_all_mono_user_axioms = got_all_mono_user_axioms,
       no_poly_user_axioms = no_poly_user_axioms,
       wfs = map (fn (_, value) => value = SOME true) (#wf mf),
       total_consts = #total_consts mf}
    val genuine_reasons = authenticity_reasons mf
      got_all_mono_user_axioms no_poly_user_axioms
    val generated_problems = ref ([] : rich_problem list)
    val generated_scopes = ref ([] : MFS.scope list)
    val checked_problems = ref ([] : rich_problem list)
    val counterexamples = ref ([] : Refute_Core.counterexample list)
    val kodkod_calls = ref 0
    val met_potential = ref 0
    val last_donno = ref 0
    val error_reasons = ref ([] : string list)
    val original_max_potential =
      if #genuine_only config then 0
      else Int.min (1, Int.max (0, #max_potential mf))
    val original_max_genuine =
      Int.min (1, Int.max (0, #max_genuine mf))

    fun add_error reason =
      if List.exists (fn old => old = reason) (!error_reasons) then ()
      else error_reasons := !error_reasons @ [reason]

    fun update_checked problems indices =
      List.app (fn index =>
        if index >= 0 andalso index < length problems then
          let val problem = List.nth (problems, index)
          in
            if rich_member problem (!checked_problems) then ()
            else checked_problems := problem :: !checked_problems
          end
        else ()) indices

    fun make_base (problem : rich_problem) : Refute_Core.counterexample =
      {backend = "kodkod", substrate = "kodkod",
       certainty = Refute_Core.Potential [], bindings = [], evals = [],
       cert = NONE,
       scope = SOME (#card_assigns (#scope (metadata problem))),
       model = NONE, stats = []}

    fun reconstruct problem bounds =
      let
        val extension = metadata problem
        val reconstructed = MFM.reconstruct
          {scope = #scope extension,
           atoms = #atoms mf,
           real_frees = real_frees,
           eval_terms = #evals instance,
           free_names = #free_names extension,
           sel_names = #sel_names extension,
           nonsel_names = #nonsel_names extension,
           rel_table = #rel_table extension,
           bounds = bounds}
        val sound = not (#unsound extension)
        val reasons = if sound then genuine_reasons else []
      in
        case MFM.certify
          {executable = executable,
           original = original,
           eval_terms = #evals instance,
           reconstruction = reconstructed,
           cex = make_base problem,
           sound = sound,
           genuine_means_genuine = genuine_formula,
           reasons = reasons} of
            MFM.Drop => NONE
          | MFM.Keep cex =>
              if #genuine_only config andalso
                 certainty_is_potential (#certainty cex)
              then NONE
              else
                (counterexamples := cex :: !counterexamples;
                 if certainty_is_potential (#certainty cex) then
                   met_potential := !met_potential + 1
                 else ();
                 SOME cex)
      end

    fun solve_any_problem state first_time problems =
      let
        val (found_really_genuine, raw_max_potential,
             raw_max_genuine, donno) = state
        val _ = last_donno := donno
        val max_potential = Int.max (0, raw_max_potential)
        val max_genuine = Int.max (0, raw_max_genuine)
        val max_solutions = Int.min (1, max_potential + max_genuine)
      in
        if max_solutions <= 0 then
          (found_really_genuine, 0, 0, donno)
        else if null problems then
          (found_really_genuine, max_potential, max_genuine, donno)
        else
          let
            val _ = check_deadline deadline
            val _ = kodkod_calls := !kodkod_calls + 1
          in
            case KK.solve_any_problem (#debug mf) (#overlord mf) deadline
                (#max_threads mf) max_solutions (map raw_problem problems) of
                KK.Normal ([], unsat_indices, warning) =>
                  (update_checked problems unsat_indices;
                   if warning = "" then () else
                     Refute_Core.Private.say 1
                       ("Kodkod warning: " ^ warning ^ "\n");
                   (found_really_genuine, max_potential,
                    max_genuine, donno))
              | KK.Normal (sat_models, unsat_indices, warning) =>
                  let
                    val _ = if warning = "" then () else
                      Refute_Core.Private.say 1
                        ("Kodkod warning: " ^ warning ^ "\n")
                    val (liberal, conservative) = List.partition
                      (fn (index, _) =>
                        #unsound (metadata (List.nth (problems, index))))
                      sat_models
                  in
                    if null conservative then
                      let
                        val _ = update_checked problems
                          (unsat_indices @ map #1 liberal)
                        val results = List.mapPartial (fn (index, bounds) =>
                          reconstruct (List.nth (problems, index)) bounds)
                          (take_at_most max_potential liberal)
                        val genuine_count = length (List.filter
                          (certainty_is_genuine o #certainty) results)
                        val potential_count = length results - genuine_count
                        val found = found_really_genuine orelse
                          genuine_count > 0
                        val max_genuine = max_genuine - genuine_count
                        val max_potential =
                          max_potential - potential_count
                      in
                        if max_genuine <= 0 then
                          (found, 0, 0, donno)
                        else
                          let
                            (* m3-driver Q4: the upstream potential promotion
                               filter was dead.  Certification is handled
                               directly above, so no vestigial option filter
                               remains here. *)
                            val co_indices = List.mapPartial (fn index =>
                              let val sound_index = index - 1
                              in
                                if sound_index >= 0 andalso
                                   index < length problems andalso
                                   #unsound
                                     (metadata
                                       (List.nth (problems, index))) andalso
                                   MFS.scopes_equivalent
                                     (#scope (metadata (List.nth
                                        (problems, sound_index))),
                                      #scope (metadata (List.nth
                                        (problems, index))))
                                then SOME sound_index else NONE
                              end) unsat_indices
                            val bye = distinct_ints
                              (map #1 sat_models @ unsat_indices @ co_indices)
                            val remaining_problems =
                              MFU.filter_out_indices bye problems
                              |> (fn values =>
                                if max_potential <= 0 then
                                  List.filter
                                    (not o #unsound o metadata) values
                                else values)
                          in
                            solve_any_problem
                              (found, max_potential, max_genuine, donno)
                              false remaining_problems
                          end
                      end
                    else
                      let
                        val results = List.mapPartial (fn (index, bounds) =>
                          reconstruct (List.nth (problems, index)) bounds)
                          (take_at_most max_genuine conservative)
                        val kept = length results
                        val found = found_really_genuine orelse
                          List.exists
                            (certainty_is_genuine o #certainty) results
                        val max_genuine = max_genuine - kept
                      in
                        if max_genuine <= 0 then
                          (found, 0, max_genuine, donno)
                        else
                          let
                            val bye = distinct_ints
                              (map #1 sat_models @ unsat_indices)
                            val remaining_problems =
                              MFU.filter_out_indices bye problems
                              |> List.filter (not o #unsound o metadata)
                          in
                            solve_any_problem
                              (found, 0, max_genuine, donno)
                              false remaining_problems
                          end
                      end
                  end
              | KK.TimedOut unsat_indices =>
                  (update_checked problems unsat_indices;
                   raise Timeout.TIMEOUT Time.zeroTime)
              | KK.Error (message, unsat_indices) =>
                  (update_checked problems unsat_indices;
                   add_error ("Kodkod error: " ^ message);
                   last_donno := donno + 1;
                   (found_really_genuine, max_potential,
                    max_genuine, donno + 1))
          end
      end

    fun add_problem flags scope (problems, donno) =
      let
        fun add unsound (kept, unknown) =
          let
            val _ = check_deadline deadline
          in
            case problem_for_scope deadline mf all_types solver
                free_names nonsel_names nondef_us def_us unsound scope of
                NONE => (kept, unknown + 1)
              | SOME problem =>
                  (case rev kept of
                       previous :: _ =>
                         if KK.problems_equivalent
                              (raw_problem previous, raw_problem problem)
                         then (kept, unknown)
                         else (kept @ [problem], unknown)
                     | [] => ([problem], unknown))
          end
      in
        List.foldl (fn (flag, result) => add flag result)
          (problems, donno) flags
      end

    fun trivially_false_warning () =
      let
        val (unsound, sound) = List.partition
          (#unsound o metadata) (!generated_problems)
      in
        if not (null sound) andalso
           List.all (KK.is_problem_trivially_false o raw_problem) sound then
          Refute_Core.Private.say 1
            ("Refute warning: the " ^
             (if #falsify mf then "conjecture either holds"
              else "formula is unsatisfiable") ^
             " for the given scopes or lies outside the supported " ^
             "fragment" ^
             (if List.exists
                  (not o KK.is_problem_trivially_false o raw_problem)
                  unsound
              then "; only potentially spurious models may be found"
              else "") ^ "\n")
        else ()
      end

    fun run_batch last scope_batch state =
      let
        val (_, max_potential, max_genuine, donno) = state
        val flags =
          (if max_genuine > 0 then [false] else []) @
          (if max_potential > 0 then [true] else [])
        val (problems, donno) = List.foldl (fn (scope, result) =>
          add_problem flags scope result) ([], donno) scope_batch
        val _ = last_donno := donno
        val _ = generated_problems := !generated_problems @ problems
        val _ = generated_scopes := !generated_scopes @ scope_batch
        val _ = if last then trivially_false_warning () else ()
        val (found, max_potential, max_genuine, _) = state
      in
        solve_any_problem
          (found, max_potential, max_genuine, donno) true problems
      end

    fun run_batches [] state = state
      | run_batches (batch :: rest) state =
          let
            val next as (_, _, max_genuine, _) =
              run_batch (null rest) batch state
          in
            if max_genuine > 0 then run_batches rest next else next
          end

    fun problem_count problems scope = length (List.filter (fn problem =>
      MFS.scopes_equivalent (#scope (metadata problem), scope)) problems)

    fun scopes_checked () = length (List.filter (fn scope =>
      let
        val generated = problem_count (!generated_problems) scope
        val checked = problem_count (!checked_problems) scope
      in
        generated > 0 andalso generated = checked
      end) (!generated_scopes))

    fun stats donno =
      [("msec", elapsed_msec started),
       ("card", #card instance),
       ("scopes", length scopes),
       ("scopes_skipped", skipped),
       ("scopes_checked", scopes_checked ()),
       ("problems", length (!generated_problems)),
       ("batches", length batches),
       ("kodkod_calls", !kodkod_calls),
       ("donno", donno),
       ("met_potential", !met_potential)]

    fun finalize donno outcome =
      let val final_stats = stats donno
      in
        case outcome of
            Refute_Core.Counterexample cexs =>
              Refute_Core.Counterexample (map
                (replace_stats final_stats) cexs)
          | other => other
      end

    fun accounting_reason action =
      action ^ " after checking " ^ Int.toString (scopes_checked ()) ^
      " of " ^ Int.toString (length scopes) ^ " scopes"

    fun finish state =
      let
        val (_, max_potential, max_genuine, donno) = state
        val cexs = rev (!counterexamples)
        val outcome =
          if donno > 0 andalso max_genuine > 0 then
            Refute_Core.Unknown
              (accounting_reason "model search was inconclusive" ::
               !error_reasons)
          else if max_genuine = original_max_genuine andalso
                  max_potential = original_max_potential then
            if skipped > 0 then
              Refute_Core.Unknown
                [accounting_reason "scope limit reached"]
            else
              Refute_Core.NoCounterexample
          else if null cexs then
            Refute_Core.Unknown
              (accounting_reason "no usable model was reconstructed" ::
               !error_reasons)
          else
            Refute_Core.Counterexample cexs
      in
        finalize donno outcome
      end

    val initial =
      (false, original_max_potential, original_max_genuine, 0)
  in
    (finish (run_batches batches initial)
     handle Timeout.TIMEOUT _ =>
       let
         val cexs = rev (!counterexamples)
         val outcome =
           if !met_potential > 0 andalso not (null cexs) then
             Refute_Core.Counterexample cexs
           else
             Refute_Core.Unknown [accounting_reason "kodkod timed out"]
       in
         finalize (!last_donno) outcome
       end)
  end

fun decisive (config : Refute_Core.config)
      (Refute_Core.Counterexample cexs) =
    not (null cexs) andalso
    (#abort_potential config orelse
     List.exists (fn cex =>
       case #certainty cex of
           Refute_Core.Genuine => true
         | Refute_Core.QuasiGenuine _ => true
         | Refute_Core.Potential _ => false) cexs)
  | decisive _ _ = false

fun run config instances =
  let
    val started = Time.now ()
    val budget = Real.max (0.0, #timeout config - deadline_margin)
    val deadline = started + Time.fromReal budget
    val ordered = Listsort.sort (fn (left, right) =>
      Int.compare (#card left, #card right)) instances

    fun search [] cexs reasons all_none =
          if not (null cexs) then Refute_Core.Counterexample cexs
          else if all_none then Refute_Core.NoCounterexample
          else Refute_Core.Unknown
            (if null reasons then ["model search was inconclusive"]
             else reasons)
      | search (instance :: rest) cexs reasons all_none =
          if Time.now () >= deadline then
            if null cexs then Refute_Core.Unknown ["kodkod timed out"]
            else Refute_Core.Counterexample cexs
          else
            case inductive_reason (#original instance) of
                SOME reason => search rest cexs (reasons @ [reason]) false
              | NONE =>
                  let val result = run_instance deadline started config instance
                  in
                    case result of
                        Refute_Core.Counterexample more =>
                          let val combined = cexs @ more
                          in
                            if decisive config result then
                              Refute_Core.Counterexample combined
                            else search rest combined reasons false
                          end
                      | Refute_Core.NoCounterexample =>
                          search rest cexs reasons all_none
                      | Refute_Core.Unknown more =>
                          search rest cexs (reasons @ more) false
                  end
  in
    search ordered [] [] (not (null ordered))
  end

val kodkod_backend : Refute_Core.backend =
  {name = "kodkod", weight = 50,
   configured = Refute_Forl.is_configured,
   requires = Refute_Core.AnyGoal,
   run = run}

fun register_backends () = Refute_Core.register_backend kodkod_backend

val _ = register_backends ()

end
