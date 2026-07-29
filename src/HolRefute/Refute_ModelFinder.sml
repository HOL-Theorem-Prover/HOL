(*  Title:      HolRefute/Refute_ModelFinder.sml
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Driver for the HOL4 Refute model finder.  The control flow is a port of
Nitpick's pick_them_nits_in_term. *)

signature REFUTE_MODEL_FINDER = sig
  val prepare_instance_input :
    Refute_Core.instance -> Term.term * Term.term list
  val merge_type_vars_in_terms : Term.term list -> Term.term list
  val merge_type_vars_in_context_input :
    Refute_Core.mf_config -> Term.term -> Term.term list ->
    Refute_Core.mf_config * Term.term * Term.term list
  val scope_limit_hint : string
  val finitizable_data_types :
    Refute_ModelFinder_HOL.mf_context ->
    (Type.hol_type option * bool option) list ->
    (Type.hol_type -> bool) -> Type.hol_type list ->
    Type.hol_type list -> Type.hol_type list
  val authenticity_reasons :
    Refute_Core.mf_config -> bool -> bool -> bool -> string list
  val liberal_budget_after_models :
    {max_potential : int, max_genuine : int, delivered : int,
     kept : int, promoted : bool, incremental : bool} -> int * int
  val kodkod_backend : Refute_Core.backend
  val kodkod_certainty_ceiling : Refute_Core.certainty_ceiling
  val register_backends : unit -> unit
end

structure Refute_ModelFinder :> REFUTE_MODEL_FINDER = struct

open Portable Feedback
infix |>

structure KK = Refute_Forl
structure MFH = Refute_ModelFinder_HOL
structure MFK = Refute_ModelFinder_Kodkod
structure MFM = Refute_ModelFinder_Model
structure MFMono = Refute_ModelFinder_Mono
structure MFN = Refute_ModelFinder_Names
structure MFNT = Refute_ModelFinder_Nut
structure MFP = Refute_ModelFinder_Preproc
structure MFS = Refute_ModelFinder_Scope
structure Util = Refute_ModelFinder_Util

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

fun type_arguments ty =
  if Type.is_vartype ty then []
  else #Args (Type.dest_thy_type ty)

fun ground_types context binarize terms =
  let
    fun add ty types =
      if MFH.is_fun_type ty orelse MFH.is_pair_type ty orelse
         pred_setSyntax.is_set_type ty then
        List.foldl (fn (argument, result) => add argument result)
          types (type_arguments ty)
      else if MFH.is_boolean_type ty orelse Util.member_type ty types then
        types
      else
        let
          val types = Util.add_type ty types
          val constructor_types = List.concat
            (map MFH.constructor_arg_types
              (MFH.binarized_and_boxed_data_type_constrs
                 context binarize ty))
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

fun free_variables terms =
  Util.distinct_terms (List.concat (map Term.free_vars_lr terms))

fun none_true assignments =
  List.all (fn (_, value) => value <> SOME true) assignments

fun authenticity_reasons (mf : Refute_Core.mf_config)
      got_all_mono_user_axioms no_poly_user_axioms codatatypes_ok =
  if not no_poly_user_axioms then
    ["polymorphic axioms prevent an authenticity guarantee"]
  else
    let
      val options =
        (if got_all_mono_user_axioms then []
         else ["\"user_axioms\" set to \"true\""]) @
        (if none_true (#wf mf) then []
         else ["\"wf\" set to \"smart\" or \"false\""]) @
        (if none_true (#finitize mf) then []
         else ["\"finitize\" set to \"smart\" or \"false\""]) @
        (if #total_consts mf = SOME true then
           ["\"total_consts\" set to \"smart\" or \"false\""]
         else []) @
        (if codatatypes_ok then []
         else ["\"bisim_depth\" set to a nonnegative value"])
    in
      MFM.try_again_reasons options
    end

fun exact_totality all_types (scope : MFS.scope) =
  List.all (MFS.is_exact_type (#data_types scope) true) all_types

fun type_name ty = Parse.type_to_string ty

fun scope_comment (scope : MFS.scope) =
  String.concatWith ", " (map (fn (ty, card) =>
    if MFH.is_bisim_iterator_type ty then
      "bisim_depth = " ^ Int.toString (card - 1)
    else
      "card " ^ type_name ty ^ " = " ^ Int.toString card)
    (#card_assigns scope))

fun deep_data_types all_types sel_names =
  let
    fun selector_domain name =
      Option.map #1 (Lib.total Type.dom_rng (MFNT.type_of name))
    fun selected ty = List.exists (fn name =>
      case selector_domain name of
          SOME domain => Util.same_type ty domain
        | NONE => false) sel_names
  in
    List.filter (fn ty =>
      Util.same_type ty ``:unit`` orelse Util.same_type ty MFH.num_type orelse
      MFH.is_bitword_type ty orelse
      Option.isSome (MFH.word_dimension ty) orelse
      (MFH.is_data_type ty andalso selected ty)) all_types
  end

fun finitizable_data_types context finitizes kind_of_monotonic
      all_types deep_types =
  let
    val data_types = List.filter MFH.is_data_type all_types
    val (deep, shallow) = List.partition (fn ty =>
      Util.member_type ty deep_types) data_types
    fun infinite ty = not (MFH.is_finite_type context ty)
    fun forced ty =
      MFS.mono_override finitizes ty = SOME (SOME true)
    fun shallow_finitizable ty =
      case MFS.mono_override finitizes ty of
          SOME (SOME value) => value
        | _ => kind_of_monotonic ty
  in
    List.filter (fn ty => infinite ty andalso forced ty) deep @
    List.filter (fn ty => infinite ty andalso
      shallow_finitizable ty) shallow
  end

fun quote text = "\"" ^ text ^ "\""

fun actual_solver incremental (mf : Refute_Core.mf_config) =
  let
    val requested = #sat_solver mf
    val configured = Refute_ForlSat.configured_sat_solvers incremental
    val solver =
      if requested = "smart" then
        Refute_ForlSat.smart_sat_solver_name incremental
      else if incremental andalso not (Lib.mem requested configured) then
        (Refute_Core.Private.say 1
           ("An incremental SAT solver is required: \"SAT4J\" will be " ^
            "used instead of " ^ quote requested ^ "\n");
         "SAT4J")
      else
        requested
    val _ = if requested <> "smart" then () else
      Refute_Core.Private.say 2
        ("Using SAT solver " ^ quote solver ^ "\nThe following" ^
         (if incremental then " incremental " else " ") ^
         "solvers are configured: " ^
         String.concatWith ", " (map quote configured) ^ "\n")
  in
    solver
  end

fun solver_arguments deadline solver =
  #2 (Refute_ForlSat.sat_solver_spec (remaining deadline) solver)

fun problem_for_scope deadline (mf : Refute_Core.mf_config)
      all_types solver free_names nonsel_names nondef_us def_us need_us
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
       def_us = def_us,
       need_us = need_us}
  in
    MFK.assemble_problem params unsound scope
  end

fun metadata (_, metadata : MFK.problem_metadata) = metadata

fun liberal_budget_after_models
      {max_potential, max_genuine, delivered, kept, promoted,
       incremental} =
  if promoted then (0, max_genuine - 1)
  else
    (max_potential - (if incremental then delivered else kept),
     max_genuine)

fun raw_problem (problem, _ : MFK.problem_metadata) = problem

fun rich_problems_equivalent (left : rich_problem, right : rich_problem) =
  #unsound (metadata left) = #unsound (metadata right) andalso
  MFS.scopes_equivalent
    (#scope (metadata left), #scope (metadata right)) andalso
  KK.problems_equivalent (raw_problem left, raw_problem right)

fun rich_member problem = List.exists (fn other =>
  rich_problems_equivalent (problem, other))

val take_at_most = MFS.take_at_most

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

(* HOL4 has no type classes or sorts, so all goal type variables occupy
   Isabelle's single default-sort equivalence class.  Keeping the
   alphabetically first variable is therefore the sortless specialization
   of Nitpick's [merged_type_var_table_for_terms]. *)
fun merge_type_vars_in_terms terms =
  let
    val tyvars = Listsort.sort (fn (left, right) =>
      String.compare (Type.dest_vartype left, Type.dest_vartype right))
      (Lib.U (map Term.type_vars_in_term terms))
  in
    case tyvars of
        [] => terms
      | canonical :: rest =>
          let
            val theta = map (fn tyvar =>
              {redex = tyvar, residue = canonical}) rest
          in
            map (Term.inst theta) terms
          end
  end

fun merge_type_vars_in_context_input
      (mf : Refute_Core.mf_config) original evals =
  if not (#merge_type_vars mf) then (mf, original, evals)
  else
    let
      val needs = #need mf
      val need_terms = Option.getOpt (needs, [])
      val merged = merge_type_vars_in_terms
        (original :: (evals @ need_terms))
      val merged_tail = tl merged
      val merged_evals = List.take (merged_tail, length evals)
      val merged_need_terms = List.drop (merged_tail, length evals)
      val merged_needs = Option.map (fn _ => merged_need_terms) needs
      val context_mf = Refute_Core.change_mf
        (Refute_Core.MfNeed merged_needs) mf
    in
      (context_mf, hd merged, merged_evals)
    end

fun prepare_instance_input (instance : Refute_Core.instance) =
  let
    val input_original = #original instance
    val (original, renaming, type_renaming) =
      MFN.rename_colliding_goal_vars
        (MFN.reserved_frees input_original) input_original
    val _ = MFN.assert_user_goal original
    val renaming_subst = map (fn (old, fresh) =>
      {redex = old, residue = fresh}) renaming
    fun rename term = term
      |> Term.subst renaming_subst
      |> Term.inst type_renaming
  in
    (original, map rename (#evals instance))
  end

(* A quotient package type also has a kernel typedef theorem, so the raw
   morphism guard discovers both classes.  Prefer the quotient theorem; only
   if that validated harvest misses do we try the typedef bijections shape.
   Iterate because one problem may mention several previously unseen types. *)
fun harvest_guard terms =
  case MFH.first_unregistered_typedef terms of
      NONE => (NONE, false)
    | SOME ty =>
        if MFH.harvest_quotient ty orelse MFH.harvest_typedef ty then
          let val (reason, _) = harvest_guard terms
          in (reason, true) end
        else
          (MFH.unregistered_typedef_reason terms, false)

fun harvest_guard_reason terms = #1 (harvest_guard terms)

exception RESTART_AFTER_HARVEST

val scope_limit_hint =
  "scope limit reached; consider using \"mono\" or \"merge_type_vars\" " ^
  "to prevent this"

fun run_instance deadline started (config : Refute_Core.config)
      incremental solver (initial_max_potential, initial_max_genuine)
      (instance : Refute_Core.instance) =
  let
    val mf = #mf config
    val sound_finitizes = none_true (#finitize mf)
    val (prepared_original, prepared_evals) =
      prepare_instance_input instance
    val (context_mf, original, eval_terms) =
      merge_type_vars_in_context_input mf prepared_original prepared_evals
    val negated =
      if #falsify mf then boolSyntax.mk_imp (original, boolSyntax.F)
      else original
    val context = MFH.make_context context_mf eval_terms
    val fixpoint_refusal = MFH.first_fixpoint_refusal context original
    val _ = if Option.isSome fixpoint_refusal then
        MFH.print_wf_cache context else ()
    val _ = case fixpoint_refusal of
        SOME reason => raise Util.NOT_SUPPORTED reason
      | NONE => ()
    val (nondef_ts, def_ts, need_ts, got_all_mono_user_axioms,
         no_poly_user_axioms, binarize) =
      MFP.preprocess_formulas context [] negated
    (* A typedef morphism can enter through an unfolded wrapper even when it
       was absent from the surface goal.  Scan the complete preprocessed
       problem as well as the early surface-goal guard in [run]. *)
    val _ =
      case harvest_guard (nondef_ts @ def_ts) of
          (SOME reason, _) => raise Util.NOT_SUPPORTED reason
        | (NONE, true) =>
            (* The first preprocessing pass did not know the harvested
               registration and therefore did not insert its axioms or
               morphism rewrites.  Restart with a fresh context before any
               scope or solver work; the positive registry cache makes the
               second pass constant-time at this guard. *)
            raise RESTART_AFTER_HARVEST
        | (NONE, false) => ()
    val _ = MFH.refresh_iterator_arg_types context (nondef_ts @ def_ts)
    val _ = MFH.print_wf_cache context
    val nondef_us = map (MFNT.nut_from_term context MFNT.Eq) nondef_ts
    val def_us = map (MFNT.nut_from_term context MFNT.DefEq) def_ts
    val need_us = map (MFNT.nut_from_term context MFNT.Eq) need_ts
    val (free_names, const_names) =
      List.foldl (fn (nut, names) =>
        MFNT.add_free_and_const_names nut names)
        ([], []) (nondef_us @ def_us @ need_us)
    val (sel_names, nonsel_names) = List.partition
      (MFN.is_sel o MFNT.nickname_of) const_names
    val all_types = ground_types context binarize
      (nondef_ts @ def_ts @ need_ts)
    val unique_scope = List.all (fn (_, values) => length values = 1)
      (#card mf)
    val calculus_mono_cache = ref ([] : (hol_type * bool) list)
    val _ =
      if #binary_ints mf = SOME true andalso not binarize andalso
         List.exists (fn ty => ty = MFH.num_type orelse ty = MFH.int_type)
           all_types then
        Refute_Core.Private.say 2
          ("The option \"binary_ints\" will be ignored because of the " ^
           "presence of rationals, reals, \"Suc\", \"gcd\", or \"lcm\" " ^
           "in the problem.\n")
      else ()

    fun report_mono_failure kind ty detail =
      if !MFMono.trace then
        Feedback.HOL_MESG
          ("Refute monotonicity " ^ kind ^ " for " ^ type_name ty ^
           (if detail = "" then "" else ": " ^ detail))
      else ()

    fun is_type_actually_monotonic ty =
      case List.find (fn (cached_ty, _) => Util.same_type ty cached_ty)
             (!calculus_mono_cache) of
          SOME (_, result) => result
        | NONE =>
            let
              val result =
                (Timeout.apply (#tac_timeout context)
                   (MFMono.formulas_monotonic context binarize ty)
                   (nondef_ts, def_ts)
                 handle Timeout.TIMEOUT _ =>
                          (report_mono_failure "timeout" ty ""; false)
                      | Util.BAD (location, detail) =>
                          (report_mono_failure location ty detail; false))
              val _ = calculus_mono_cache :=
                (ty, result) :: !calculus_mono_cache
            in
              result
            end

    (* Unlike the scope shortcut, kind-of monotonicity deliberately lets a
       user false row block the calculus but does not let a true row force
       it.  Finitization plumbing is this helper's first caller. *)
    fun is_type_kind_of_monotonic ty =
      case MFS.mono_override (#mono mf) ty of
          SOME (SOME false) => false
        | _ => is_type_actually_monotonic ty

    val (mono_types, nonmono_types) =
      if unique_scope then (all_types, [])
      else MFS.mono_partition_with is_type_actually_monotonic
        (#mono mf) all_types
    val forced_mono_types = List.filter (fn ty =>
      MFS.mono_override (#mono mf) ty = SOME (SOME true)) mono_types
    val inferred_mono_types = rev (List.mapPartial
      (fn (ty, true) => SOME ty | _ => NONE) (!calculus_mono_cache))

    fun report_monotonic wording types =
      if null types then ()
      else
        Refute_Core.Private.say 2
          ("The following type" ^ Util.plural_s_for_list types ^ " " ^
           wording ^ ": " ^
           String.concatWith ", " (map type_name types) ^
           ". Refute might be able to skip some scopes.\n")

    val _ = report_monotonic
      (if length forced_mono_types = 1 then "is considered monotonic"
       else "are considered monotonic") forced_mono_types
    val _ = report_monotonic "passed the monotonicity test"
      inferred_mono_types
    val deep_types = deep_data_types all_types sel_names
    val finitizable_types = finitizable_data_types context (#finitize mf)
      is_type_kind_of_monotonic all_types deep_types
    val _ = if null finitizable_types then () else
      Refute_Core.Private.say 2
        ("The following type" ^ Util.plural_s_for_list finitizable_types ^
         " can use a more precise finite encoding: " ^
         String.concatWith ", " (map type_name finitizable_types) ^ "\n")
    val (skipped, scopes) = MFS.all_scopes context binarize
      (#card mf) (#max mf) (#iter mf) (#bits mf) (#bisim_depth mf)
      mono_types nonmono_types
      deep_types finitizable_types
    val batch_size =
      if #debug mf then 1 else Int.max (1, #batch_size mf)
    val batches = Util.chunk_list batch_size scopes
    val real_frees = free_variables [original]
    val executable = not (Option.isSome (#qc_gate instance)) andalso
      #falsify mf andalso
      not (List.exists (fn ty =>
        MFH.is_codatatype ty orelse MFH.is_quot_type ty orelse
        MFH.is_typedef ty) all_types)
    val genuine_formula = MFM.genuine_means_genuine
      {got_all_mono_user_axioms = got_all_mono_user_axioms,
       no_poly_user_axioms = no_poly_user_axioms,
       wfs = map (fn (_, value) => value = SOME true) (#wf mf),
       sound_finitizes = sound_finitizes,
       total_consts = #total_consts mf}
    val generated_problems = ref ([] : rich_problem list)
    val generated_scopes = ref ([] : MFS.scope list)
    val checked_problems = ref ([] : rich_problem list)
    val counterexamples = ref ([] : Refute_Core.counterexample list)
    val kodkod_calls = ref 0
    val met_potential = ref 0
    val last_donno = ref 0
    (* Set when a sound problem was satisfiable but its model did not
       survive reconstruction.  Such a scope is neither refuted nor
       exhausted, so the search may not end in NoCounterexample. *)
    val discarded_sound_model = ref false
    val error_reasons = ref ([] : string list)
    val original_max_potential = Int.max (0, initial_max_potential)
    val original_max_genuine = Int.max (0, initial_max_genuine)
    val latest_state = ref
      (false, original_max_potential, original_max_genuine, 0)

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
        val arguments =
          {scope = #scope extension,
           atoms = #atoms mf,
           special_funs = !(#special_funs context),
           real_frees = real_frees,
           eval_terms = eval_terms,
           free_names = #free_names extension,
           sel_names = #sel_names extension,
           nonsel_names = #nonsel_names extension,
           rel_table = #rel_table extension,
           bounds = bounds}
        val {raw = reconstructed, displayed, postprocessors} =
          MFM.reconstruct_both
          {context = context, formats = #format mf,
           scope = #scope arguments, atoms = #atoms arguments,
           special_funs = #special_funs arguments,
           real_frees = #real_frees arguments,
           eval_terms = #eval_terms arguments,
           free_names = #free_names arguments,
           sel_names = #sel_names arguments,
           nonsel_names = #nonsel_names arguments,
           rel_table = #rel_table arguments,
           bounds = #bounds arguments}
        val sound = not (#unsound extension)
        val scope_has_codatatype =
          List.exists #co (#data_types (#scope extension))
        val weakened = !(#semantic_weakening context)
        val reasons = if sound then
            authenticity_reasons mf got_all_mono_user_axioms
              no_poly_user_axioms (#codatatypes_ok reconstructed) @
            (if weakened then
               ["formula was semantically weakened by whack or ersatz"]
             else [])
          else []
      in
        case MFM.certify
          {executable = executable andalso not scope_has_codatatype,
           original = original,
           eval_terms = eval_terms,
           reconstruction = reconstructed,
           cex = make_base problem,
           sound = sound,
           genuine_means_genuine = genuine_formula andalso not weakened,
           reasons = reasons} of
            MFM.Drop => NONE
          | MFM.Keep semantic_cex =>
              let val cex =
                MFM.display_counterexample postprocessors displayed
                  semantic_cex
              in
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
      end

    fun solve_any_problem state first_time problems =
      let
        val (found_really_genuine, raw_max_potential,
             raw_max_genuine, donno) = state
        val _ = last_donno := donno
        val max_potential = Int.max (0, raw_max_potential)
        val max_genuine = Int.max (0, raw_max_genuine)
        val _ = latest_state :=
          (found_really_genuine, max_potential, max_genuine, donno)
        val max_solutions = max_potential + max_genuine
          |> (fn count => if incremental then count else Int.min (1, count))
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
                  let
                    val all_reported_unsat = List.all
                      (fn index => List.exists (fn reported =>
                        reported = index) unsat_indices)
                      (Portable.upto 0 (length problems - 1))
                  in
                    update_checked problems unsat_indices;
                    if warning = "" then () else
                      Refute_Core.Private.say 1
                        ("Kodkod warning: " ^ warning ^ "\n");
                    if all_reported_unsat then
                      (found_really_genuine, max_potential,
                       max_genuine, donno)
                    else
                      (add_error "Kodkodi returned an incomplete result";
                       (found_really_genuine, max_potential,
                        max_genuine, donno + 1))
                  end
              | KK.Normal (sat_models, unsat_indices, warning) =>
                  let
                    val _ = if warning = "" then () else
                      Refute_Core.Private.say 1
                        ("Kodkod warning: " ^ warning ^ "\n")
                    val (liberal, conservative) = List.partition
                      (fn (index, _) =>
                        #unsound (metadata (List.nth (problems, index))))
                      sat_models
                    val _ = update_checked problems
                      (unsat_indices @ map #1 liberal)
                  in
                    if null conservative then
                      let
                        (* A certification promotion is the phase boundary
                           from [m4-driver section 7 Q6]: do not reconstruct
                           a later liberal model (which could be merely
                           Potential), and consume exactly one genuine slot
                           before dropping the remaining unsound problems. *)
                        fun reconstruct_until_genuine _ [] = (false, 0)
                          | reconstruct_until_genuine 0 _ = (false, 0)
                          | reconstruct_until_genuine remaining
                              ((index, bounds) :: models) =
                              (case reconstruct
                                  (List.nth (problems, index)) bounds of
                                   SOME cex =>
                                     if certainty_is_genuine (#certainty cex)
                                     then (true, 1)
                                     else
                                       let
                                         val (promoted, kept) =
                                           reconstruct_until_genuine
                                             (remaining - 1) models
                                       in
                                         (promoted, kept + 1)
                                       end
                                 | NONE =>
                                     reconstruct_until_genuine
                                       remaining models)
                        (* A solver may over-deliver.  Scan past failed
                           reconstructions, but charge only usable models. *)
                        val (promoted, kept) = reconstruct_until_genuine
                          max_potential liberal
                        val found = found_really_genuine orelse promoted
                        val (max_potential, max_genuine) =
                          liberal_budget_after_models
                            {max_potential = max_potential,
                             max_genuine = max_genuine,
                             delivered = kept,
                             kept = kept, promoted = promoted,
                             incremental = incremental}
                        val _ = latest_state :=
                          (found, max_potential, max_genuine, donno)
                      in
                        if max_genuine <= 0 then
                          (found, 0, 0, donno)
                        else
                          let
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
                              Util.filter_out_indices bye problems
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
                        val attempted = take_at_most max_genuine conservative
                        val results = List.mapPartial (fn (index, bounds) =>
                          reconstruct (List.nth (problems, index)) bounds)
                          attempted
                        val kept = length results
                        val _ = if kept < length attempted then
                                  discarded_sound_model := true
                                else ()
                        val found = found_really_genuine orelse
                          List.exists
                            (certainty_is_genuine o #certainty) results
                        val max_genuine = max_genuine - kept
                        val _ = latest_state :=
                          (found, 0, max_genuine, donno)
                      in
                        (* Upstream harvests sound models for at most two
                           rounds per incremental batch.  Keep the M3 1/1
                           path unchanged, where [first_time] was ignored. *)
                        if max_genuine <= 0 orelse
                           (incremental andalso not first_time) then
                          (found, 0, max_genuine, donno)
                        else
                          let
                            val bye = distinct_ints
                              (map #1 sat_models @ unsat_indices)
                            val remaining_problems =
                              Util.filter_out_indices bye problems
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
                free_names nonsel_names nondef_us def_us need_us
                unsound scope of
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
          (* Keep the M3/upstream inconclusive-result precedence when the
             genuine budget is still open, even if a potential was kept. *)
          if donno > 0 andalso max_genuine > 0 then
            Refute_Core.Unknown
              (accounting_reason "model search was inconclusive" ::
               !error_reasons)
          else if max_genuine = original_max_genuine andalso
                  max_potential = original_max_potential then
            if skipped > 0 then
              Refute_Core.Unknown
                [accounting_reason scope_limit_hint]
            else if !discarded_sound_model then
              Refute_Core.Unknown
                (accounting_reason
                   "every model found was discarded" :: !error_reasons)
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
    fun remaining (_, max_potential, max_genuine, _) =
      (Int.max (0, max_potential), Int.max (0, max_genuine))
  in
    let val final_state = run_batches batches initial
    in
      (finish final_state, remaining final_state)
    end
    handle Timeout.TIMEOUT _ =>
      let
        val cexs = rev (!counterexamples)
        val outcome =
          if not (null cexs) then Refute_Core.Counterexample cexs
          else
            Refute_Core.Unknown [accounting_reason "kodkod timed out"]
      in
        (finalize (!last_donno) outcome, remaining (!latest_state))
      end
  end
  handle RESTART_AFTER_HARVEST =>
    run_instance deadline started config incremental solver
      (initial_max_potential, initial_max_genuine) instance

fun kodkod_certainty_ceiling (config : Refute_Core.config) instances =
  let
    val mf = #mf config
    val certification_reachable =
      #falsify mf andalso
      List.exists Refute_Core.instance_is_executable instances
    (* MFM.genuine_means_genuine also demands the two user-axiom conjuncts,
       and both are functions of the theory ancestry alone, so the ceiling
       can test them here rather than overestimating past them.  An
       overestimate only costs an early stop, but here it costs every one:
       a ceiling of Genuine that the fallback path can never reach leaves
       Refute_Core.decisive permanently false. *)
    val nondefs = MFH.all_nondefs_of ()
    val (poly_nondefs, mono_nondefs) =
      List.partition MFH.is_poly_term nondefs
    val genuine_fallback_reachable =
      List.all (fn (_, value) => value <> SOME true) (#wf mf) andalso
      none_true (#finitize mf) andalso
      #total_consts mf <> SOME true andalso
      (#user_axioms mf = SOME true orelse null mono_nondefs) andalso
      null poly_nondefs
  in
    if certification_reachable orelse genuine_fallback_reachable then
      Refute_Core.Genuine
    else
      Refute_Core.QuasiGenuine
        ["model-finder configuration precludes Genuine results"]
  end

fun run config instances =
  let
    val started = Time.now ()
    val budget = Real.max (0.0, #timeout config - deadline_margin)
    val deadline = started + Time.fromReal budget
    val ordered = Listsort.sort (fn (left, right) =>
      Int.compare (#card left, #card right)) instances
    val mf = #mf config
    val initial_max_potential =
      if #genuine_only config then 0
      else Int.max (0, #max_potential mf)
    val initial_max_genuine = Int.max (0, #max_genuine mf)
    val incremental =
      Int.max (initial_max_potential, initial_max_genuine) >= 2
    val solver = actual_solver incremental mf
    val typedef_reason = harvest_guard_reason
      (List.concat (map (fn (instance : Refute_Core.instance) =>
        #original instance :: #evals instance) ordered))

    fun search [] cexs reasons all_none _ =
          if not (null cexs) then Refute_Core.Counterexample cexs
          else if all_none then Refute_Core.NoCounterexample
          else Refute_Core.Unknown
            (if null reasons then ["model search was inconclusive"]
             else reasons)
      | search (instance :: rest) cexs reasons all_none budget =
          if Time.now () >= deadline then
            if null cexs then Refute_Core.Unknown ["kodkod timed out"]
            else Refute_Core.Counterexample cexs
          else
            let
              val (result, next_budget) =
                run_instance deadline started config incremental solver
                  budget instance
                handle Util.NOT_SUPPORTED reason =>
                  (Refute_Core.Unknown [reason], budget)
              val (_, max_genuine) = next_budget
            in
              case result of
                  Refute_Core.Counterexample more =>
                    let val combined = cexs @ more
                    in
                      if max_genuine <= 0 orelse #abort_potential config then
                        Refute_Core.Counterexample combined
                      else
                        search rest combined reasons false next_budget
                    end
                | Refute_Core.NoCounterexample =>
                    search rest cexs reasons all_none next_budget
                | Refute_Core.Unknown more =>
                    search rest cexs (reasons @ more) false next_budget
            end
  in
    case typedef_reason of
        SOME reason => Refute_Core.Unknown [reason]
      | NONE => search ordered [] [] (not (null ordered))
          (initial_max_potential, initial_max_genuine)
  end

val kodkod_backend : Refute_Core.backend =
  {name = "kodkod", weight = 50,
   configured = Refute_Forl.is_configured,
   requires = Refute_Core.AnyGoal,
   input = Refute_Core.PolyOriginal,
   run = run}

fun register_backends () =
  Refute_Core.register_backend_with_ceiling kodkod_backend
    kodkod_certainty_ceiling

val _ = register_backends ()

end
