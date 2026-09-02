structure Refute_QC_Narrow = struct
  open Refute_Eval
  structure QC = Refute_QC

  (* Narrowing's size coordinate is exactly refinement depth.  Unlike the
     ground generators it must test depth zero, independently of the ordinary
     size-matters optimization. *)
  fun schedule instances size =
    let
      val maximum = Int.max (0, size)
      val entries = List.concat (map (fn instance =>
        List.tabulate (maximum + 1, fn depth => (#card instance, depth)))
        instances)
      fun compare ((card1, depth1), (card2, depth2)) =
        case Int.compare (depth1, depth2) of
            EQUAL => Int.compare (card1, card2)
          | order => order
    in
      Listsort.sort compare entries
    end

  (* Keep free inputs free until selection has inserted any registered
     abstract-generator guards.  [pnf_of] closes them afterwards, preserving
     leading explicit universals in the prefix.  A guarded hit is certified
     against the original formula, so the restriction only narrows search.

     [use_subtype] transport rewrites [#goal], never [#original] (see
     [Refute_QC.transport_instance]): [#original] still quantifies over the
     untransportable abstract type, which narrowing could never search
     either way, so a transported instance must be handed [#goal].  Hand
     it over open, exactly as it is: [#goal] is a rep-typed implication
     whose fresh representation variables are free, and [pnf_of] closes
     free variables itself, so they become the prefix's leading
     universals by the same route every other narrowing input takes.
     Closing them here first instead is what the guard makes tempting and
     it is wrong: measured on [zoo_three_ne_2], [Refute_Core.normalize]
     rewrites the closed [!r. r < 3 ==> r <> 2] to the bounded, ground
     [EVERY (\r. r <> 2) (COUNT_LIST 3)], leaving [pnf_of] an empty
     prefix.  Narrowing then refutes at depth 0 with nothing instantiated
     and an empty [env], and [Refute_QC.record_candidate_with]'s binding
     filter -- which keeps exactly the [env] entries free in [#goal] --
     has nothing to keep, so the hit reports a counterexample naming no
     witness at all.  Every certification call site in [Refute_QC] --
     [Refute_Cert.certify], [Refute_Cert.ground_and_certify], and
     [Refute_Cert_Narrow.certify_case_tree] alike -- is passed
     [original = #original instance] regardless of substrate, so a
     transported hit's replay always closes over the pre-transport
     formula quantifying [x], while its [env] only ever binds the fresh
     [r]: [Refute_Cert.certify]'s direct replay finds [x] unsubstituted
     and gets stuck, and its PNF fallback's [binding_for] finds no [env]
     entry named [x] and raises, so both routes land on [Uncertified].
     That is not a certainty downgrade -- [Refute_Cert.uncertified]
     keeps the payload's [certainty] at whatever testing already
     established (see [Refute_Core]'s "certainty and cert are
     independent axes") -- so reusing [#goal] here, rather than trying
     to route narrowing's own formula into certification, costs nothing:
     certification was never going to see [#goal] either way.  Measured
     on [zoo_three_ne_2] under [Only [Exhaustive]] and [Only [Narrowing]]
     alike: both report [certainty = Genuine], [cert = NONE]. *)
  fun narrowing_goal (instance : Refute_Core.instance) =
    case #transport instance of
        [] => Refute_Core.normalize (#original instance)
      | _ => Refute_Core.normalize (#goal instance)

  (* A narrowing problem is one PNF formula rather than a list of plans.
     Compile each monomorphic/cardinality instance independently and
     multiplex the resulting native tests behind the depth scheduler. *)
  fun compile_instances_window config window instances =
    Refute_Extract.with_narrowing_window window (fn instances =>
    let
      fun compile_one instance =
        case Refute_Narrow.select_for_config config
          (narrowing_goal instance) of
            (Refute_Narrow.PlainRefusal reasons, _) =>
              (NONE, QC.SelectionFailed reasons)
          | (_, problem as Pnf {prefix, ...}) =>
              (SOME prefix, QC.compile_selected config Narrowing problem)
          | _ => raise Fail "narrowing selection did not produce PNF"
      fun selected_tests selected = map #4 selected
      fun preserve_error error selected =
        let
          val cleanup =
            Exn.capture QC.close_tests (selected_tests selected)
        in
          case (error, cleanup) of
              (Interrupt, _) => raise Interrupt
            | (_, Exn.Exn Interrupt) => raise Interrupt
            | _ => Exn.reraise error
        end
      fun loop [] selected =
            let
              val entries = rev selected
              val names = map #3 entries
              val compiled = selected_tests entries
              val last_stats = ref []
              val closed = ref false
              fun run input =
                let
                  val test =
                    case List.find
                      (fn (card, _, _, _) => card = #card input) entries of
                        SOME (_, _, _, found) => found
                      | NONE => raise Subscript
                  (* Cleared before every call, exactly as [Refute_QC.one]
                     clears the compiled test it drives directly: a call
                     that gives up before setting its own stats must read
                     back as "not measured", never the previous call's
                     numbers copied through unchanged. *)
                  val _ = #last_stats test := []
                  val result = #run test
                    {genuine_only = #genuine_only input, card = 1,
                     size = #size input, draws = #draws input,
                     ignored = #ignored input}
                  val _ = last_stats := !(#last_stats test)
                in
                  result
                end
              fun close () =
                if !closed then ()
                else (closed := true; QC.close_tests compiled)
              val name =
                case Lib.mk_set names of
                    [single] => single
                  | _ => "native"
            in
              (QC.Selected (name,
                 {run = run, close = close, max_chunk = NONE,
                  last_stats = last_stats}),
               map (fn (card, prefix, _, _) => (card, prefix)) entries)
            end
        | loop (instance :: rest) selected =
            (case Exn.capture compile_one instance of
                 Exn.Res (SOME prefix, QC.Selected (name, test)) =>
                   loop rest
                     ((#card instance, prefix, name, test) :: selected)
               | Exn.Res (_, QC.SelectionFailed reasons) =>
                   (QC.close_tests (selected_tests selected);
                    (QC.SelectionFailed reasons, []))
               | Exn.Res (NONE, QC.Selected _) =>
                   raise Fail "narrowing selection lost its PNF prefix"
               | Exn.Exn error => preserve_error error selected)
    in
      loop instances []
    end) instances

  fun run_body (config : Refute_Core.config)
      (instances : Refute_Core.instance list) =
    let
      val qc = #qc config
      val counterexamples = ref []
      val replay_potential = ref NONE
      val discarded = ref 0
      val gave_up = ref []
      val failed = ref false
      val frontier = ref (NONE : int option)
      (* Aggregated across every [one] call in this search -- including
         [spend]'s certification retries, not just one per schedule
         entry -- so a narrowing vacuity report reflects the whole run. *)
      val counters = QC.new_counter_totals ()
      val complete_entries = ref ([] : (int * int) list)
      val incomplete_entries = ref ([] : (int * int) list)
      val totally_exhausted_depth = ref (NONE : int option)
      (* Certification retry state outlives each compiled depth window. *)
      val states : (bool * candidate list) ref list =
        map (fn _ => ref (#genuine_only config, [])) instances
      fun target_reached () =
        length (!counterexamples) >=
          Int.max (1, #max_counterexamples config)
      fun instance_for card = List.nth (instances, card - 1)
      fun state_for card = List.nth (states, card - 1)
      fun entry_member entry = List.exists (fn other => other = entry)
        (!complete_entries)
      fun entry_incomplete entry = List.exists (fn other => other = entry)
        (!incomplete_entries)
      fun record_complete entry =
        if entry_member entry orelse entry_incomplete entry then ()
        else complete_entries := entry :: !complete_entries
      fun record_incomplete entry =
        if entry_incomplete entry then ()
        else incomplete_entries := entry :: !incomplete_entries
      fun depth_complete depth =
        not (null instances) andalso
        List.all (fn instance => entry_member (#card instance, depth))
          instances

      fun run_window window entries terminal =
        if Refute_Core.search_expired config orelse target_reached () then ()
        else
          let
            val (selection, prefixes) =
              compile_instances_window config window instances
            fun prefix_for card =
              case List.find (fn (other, _) => other = card) prefixes of
                  SOME (_, prefix) => prefix
                | NONE =>
                    raise Fail "narrowing instance lost its PNF prefix"
          in
            case selection of
                QC.SelectionFailed reasons =>
                  (failed := true; List.app (fn reason =>
                     QC.add_reason reason gave_up) reasons)
              | QC.Selected (substrate, compiled) =>
                  let
                    fun stats_for size card msec =
                      #decorate counters (!(#last_stats compiled)) @
                      (if !discarded = 0 then []
                       else [("discarded", !discarded)]) @
                      [("size", size), ("card", card), ("msec", msec)]
                    fun one (card, size) genuine_only ignored budget =
                      let
                        val start = Time.now ()
                        val result = #run compiled
                          {genuine_only = genuine_only, card = card,
                           size = size, draws = 0, ignored = ignored}
                        val msec = QC.elapsed_msec start
                        val _ = #absorb counters (!(#last_stats compiled))
                      in
                        case result of
                            Exhausted {complete} =>
                              if complete then record_complete (card, size)
                              else ()
                          | GaveUp reason => QC.add_reason reason gave_up
                          | CexFound
                              {env, ground_env, case_tree, genuine, ...} =>
                              let
                                val _ = record_incomplete (card, size)
                                val _ = QC.record_candidate
                                {config = config, strategy = Narrowing,
                                 substrate = substrate,
                                 instance = instance_for card,
                                 stats = stats_for size card msec,
                                 counterexamples = counterexamples,
                                 discarded = discarded,
                                 run_depth = SOME size,
                                 pnf_prefix = SOME (prefix_for card),
                                 retain_replay_potential = fn potential =>
                                   (replay_potential := SOME potential;
                                    Refute_Core.publish_counterexamples
                                      [potential]),
                                 retry = fn go => fn ignored =>
                                   spend (card, size) go ignored budget,
                                 retry_potential = fn go => fn ignored =>
                                   if terminal then
                                     spend (card, size) go ignored budget
                                   else state_for card := (go, ignored)}
                                {env = env, ground_env = ground_env,
                                 case_tree = case_tree, genuine = genuine,
                                 genuine_only = genuine_only,
                                 ignored = ignored}
                                val _ = Refute_Core.publish_counterexamples
                                  (rev (!counterexamples))
                              in
                                ()
                              end
                      end
                    and spend entry genuine_only ignored budget =
                      if !budget <= 0 then
                        QC.add_reason "narrowing retry budget exhausted"
                          gave_up
                      else
                        (budget := !budget - 1;
                         one entry genuine_only ignored budget)
                    fun run_entry (entry as (card, size)) =
                      let
                        val started = Time.now ()
                        val (genuine_only, ignored) = !(state_for card)
                        val budget = ref
                          (QC.bounded_size (#iterations (#qc config)))
                        val _ = one entry genuine_only ignored budget
                        val elapsed = QC.elapsed_msec started
                        val _ = frontier := SOME size
                        val _ = if depth_complete size then
                            totally_exhausted_depth := SOME size
                          else ()
                        val _ = Refute_Core.Private.say 2
                          ("Refute schedule entry (backend: narrowing" ^
                           ", substrate: " ^ substrate ^ ", card " ^
                           Int.toString card ^ ", size " ^
                           Int.toString size ^ "): " ^
                           Int.toString elapsed ^ "ms\n")
                      in
                        ()
                      end
                    fun search [] = ()
                      | search (entry :: rest) =
                          if target_reached () orelse
                             Option.isSome (!totally_exhausted_depth) orelse
                             Refute_Core.search_expired config then ()
                          else (run_entry entry; search rest)
                    val body_result = Exn.capture search entries
                    val close_result = Exn.capture (#close compiled) ()
                  in
                    case body_result of
                        Exn.Exn error => raise error
                      | Exn.Res () => Exn.release close_result
                  end
          end

      val initial = Int.max (0, #size qc)
      val _ =
        case #size_mode qc of
            Refute_Core.FixedBound =>
              run_window {first = 0, last = initial}
                (schedule instances initial) true
          | Refute_Core.IterativeDeepening =>
              let
                fun entries_at depth =
                  map (fn instance => (#card instance, depth)) instances
                fun deepen depth =
                  if !failed orelse target_reached () orelse
                     Option.isSome (!totally_exhausted_depth) orelse
                     Refute_Core.search_expired config then ()
                  else
                    (run_window {first = depth, last = depth}
                       (entries_at depth) false;
                     deepen (depth + 1))
                val _ = run_window {first = 0, last = initial}
                  (schedule instances initial) false
              in
                deepen (initial + 1)
              end
      val frontier_reason =
        case !frontier of
            NONE => []
          | SOME depth =>
              ["searched up to size " ^ Int.toString depth]
      (* Telemetry, not a search-inconclusive reason -- see the matching
         comment in [Refute_QC.strategy_run_body]. *)
      val counter_reason = #reason counters ()
    in
      if not (null (!counterexamples)) then
        Refute_Core.Counterexample (rev (!counterexamples))
      else
        case !replay_potential of
            SOME potential => Refute_Core.Counterexample [potential]
          | NONE =>
              (Option.app (fn text =>
                 Refute_Core.Private.say 2 ("narrowing: " ^ text ^ "\n"))
                 counter_reason;
               if Option.isSome (!totally_exhausted_depth) andalso
                  not (!failed) andalso null (!gave_up) then
                 Refute_Core.NoCounterexample
               else
                 (* A run that never finished a depth has not exhausted
                    anything; saying so would read as a completed search
                    that found nothing. *)
                 Refute_Core.Unknown
                   ((if Option.isSome (!frontier) then
                       "narrowing search exhausted"
                     else "narrowing reached no depth") ::
                    !gave_up @ frontier_reason))
    end

  fun run config instances =
    Refute_Core.with_search_context config (run_body config) instances

  val backend : Refute_Core.backend =
    {name = "narrowing",
     weight = 40,
     configured = fn () => true,
     requires = Refute_Core.AnyGoal,
     input = Refute_Core.MonoInstances,
     run = run}

  fun certainty_ceiling
        (_ : Refute_Core.config) (_ : Refute_Core.instance list) =
    Refute_Core.Genuine

  fun register_backend () =
    Refute_Core.register_backend_with_ceiling backend certainty_ceiling

  val _ = register_backend ()
end
