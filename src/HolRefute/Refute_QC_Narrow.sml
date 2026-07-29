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

  fun narrowing_goal (instance : Refute_Core.instance) =
    Refute_Core.normalize
      (#2 (boolSyntax.strip_forall (#original instance)))

  (* A narrowing problem is one PNF formula rather than a list of plans.
     Compile each monomorphic/cardinality instance independently and
     multiplex the resulting native tests behind the depth scheduler. *)
  fun compile_instances config instances =
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
    end

  fun run (config : Refute_Core.config)
      (instances : Refute_Core.instance list) =
    let
      val (selection, prefixes) = compile_instances config instances
      fun prefix_for card =
        case List.find (fn (other, _) => other = card) prefixes of
            SOME (_, prefix) => prefix
          | NONE => raise Fail "narrowing instance lost its PNF prefix"
    in
      case selection of
          QC.SelectionFailed reasons => Refute_Core.Unknown reasons
        | QC.Selected (substrate, compiled) =>
            let
              fun selected_body () =
                let
                  val entries = schedule instances (#size (#qc config))
                  val counterexamples = ref []
                  val replay_potential = ref NONE
                  val discarded = ref 0
                  val gave_up = ref []
                  (* A plain potential switches this card to the next
                     scheduled depth.  Certification discards alone retry
                     within the depth that produced them. *)
                  val states : (bool * candidate list) ref list =
                    map (fn _ =>
                      ref (#genuine_only config, [])) instances
                  fun instance_for card =
                    List.nth (instances, card - 1)
                  fun state_for card = List.nth (states, card - 1)
                  fun stats_for size card msec =
                    !(#last_stats compiled) @
                    (if !discarded = 0 then []
                     else [("discarded", !discarded)]) @
                    [("size", size), ("card", card), ("msec", msec)]
                  fun one (card, size) genuine_only ignored =
                    let
                      val start = Time.now ()
                      val result = #run compiled
                        {genuine_only = genuine_only, card = card,
                         size = size, draws = 0, ignored = ignored}
                      val msec = QC.elapsed_msec start
                    in
                      case result of
                          Exhausted _ => ()
                        | GaveUp reason =>
                            QC.add_reason reason gave_up
                        | CexFound
                            {env, ground_env, case_tree, genuine, ...} =>
                            QC.record_candidate
                              {config = config, strategy = Narrowing,
                               substrate = substrate,
                               instance = instance_for card,
                               stats = stats_for size card msec,
                               counterexamples = counterexamples,
                               discarded = discarded,
                               run_depth = SOME size,
                               pnf_prefix = SOME (prefix_for card),
                               retain_replay_potential = fn potential =>
                                 replay_potential := SOME potential,
                               retry = fn go => fn ig =>
                                 one (card, size) go ig,
                               retry_potential = fn go => fn ig =>
                                 (* There is no later entry at the final
                                    depth on which saved retry state could
                                    run.  Retry its remaining candidates now. *)
                                 if size >= #depth (#qc config) then
                                   one (card, size) go ig
                                 else
                                   state_for card := (go, ig)
                              {env = env, ground_env = ground_env,
                               case_tree = case_tree, genuine = genuine,
                               genuine_only = genuine_only,
                               ignored = ignored}
                    end
                  fun run_entry (entry as (card, size)) =
                    let
                      val started = Time.now ()
                      val (genuine_only, ignored) = !(state_for card)
                      val _ = one entry genuine_only ignored
                      val elapsed = QC.elapsed_msec started
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
                        if length (!counterexamples) >=
                          Int.max (1, #max_counterexamples config)
                        then ()
                        else (run_entry entry; search rest)
                  val _ = search entries
                in
                  if not (null (!counterexamples)) then
                    Refute_Core.Counterexample (rev (!counterexamples))
                  else
                    case !replay_potential of
                        SOME potential =>
                          Refute_Core.Counterexample [potential]
                      | NONE =>
                          Refute_Core.Unknown
                            ("narrowing search exhausted" :: !gave_up)
                end
              val body_result = Exn.capture selected_body ()
              val close_result = Exn.capture (#close compiled) ()
            in
              case close_result of
                  Exn.Res _ => Exn.release body_result
                | Exn.Exn error => raise error
            end
    end

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
