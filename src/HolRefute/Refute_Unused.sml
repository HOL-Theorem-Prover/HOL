signature REFUTE_UNUSED = sig
  type config = Refute_Core.config
  type thm = Thm.thm

  val check_unused_assms :
    config -> string * thm -> string * int list list option
  val find_unused_assms :
    config -> string -> (string * int list list option) list
  val print_unused_assms : config -> string option -> unit
end

structure Refute_Unused :> REFUTE_UNUSED = struct
  type config = Refute_Core.config
  type thm = Thm.thm

  type checked =
    {result : string * int list list option, skipped : int}

  fun subset (left, right) = List.all (fn x => Lib.mem x right) left

  fun insert_index x indexes =
    if Lib.mem x indexes then indexes
    else Listsort.sort Int.compare (x :: indexes)

  fun insert_set set sets =
    if List.exists (fn old => Lib.set_eq set old) sets then sets
    else sets @ [set]

  fun build indexes sets =
    let
      fun extend (set, result) =
        List.foldl (fn (index, acc) =>
          if Lib.mem index set then acc
          else insert_set (insert_index index set) acc) result indexes
    in
      List.foldl extend [] sets
    end

  fun find_max_subsets [] = []
    | find_max_subsets (sets :: levels) =
        sets :: find_max_subsets
          (map (List.filter (fn set =>
             not (List.exists (fn larger => subset (set, larger)) sets)))
           levels)

  fun drop_indexes indexes terms =
    let
      fun keep (index, term) =
        if Lib.mem index indexes then NONE else SOME term
    in
      List.mapPartial keep (Lib.enumerate 0 terms)
    end

  (* Backend selection is deliberately not changed here.  The public facade
     resolves its configuration option before calling this internal helper;
     an explicit [backends = NONE] therefore still means the full registry. *)
  fun probe_config (config : config) =
    config
    |> Refute_Core.upd_sequential true
    |> Refute_Core.upd_abort_potential true
    |> Refute_Core.upd_quiet true
    |> Refute_Core.upd_expect Refute_Core.NoExpectation

  fun check_detailed config (name, theorem) =
    let
      val (variables, body) = boolSyntax.strip_forall (Thm.concl theorem)
      val (premises, conclusion) = boolSyntax.strip_imp body
      val hypotheses = Thm.hyp theorem
      val skipped = ref 0
      val config' = probe_config config
      (* Only implication premises are candidates for removal, but theorem
         hypotheses remain assumptions of every probe.  Reintroduce the
         stripped binders as well: a hypothesis can mention one of them. *)
      fun conjecture indexes =
        boolSyntax.list_mk_forall (variables,
          boolSyntax.list_mk_imp
            (hypotheses @ drop_indexes indexes premises, conclusion))
      fun droppable indexes =
        case Refute_Core.refute config' (conjecture indexes) of
            Refute_Core.NoCounterexample => true
          | Refute_Core.Counterexample _ => false
          | Refute_Core.Model _ => false
          | Refute_Core.NoModel => false
          | Refute_Core.Unknown _ =>
              (skipped := !skipped + 1; false)
      fun grow singles current levels =
        if null current then [] :: levels
        else
          grow singles
            (List.filter droppable (build singles current))
            (current :: levels)
    in
      if null premises then
        {result = (name, NONE), skipped = 0}
      else
        let
          val indexes = Lib.upto 0 (length premises - 1)
          val singles = List.filter (droppable o (fn index => [index]))
            indexes
          (* [grow] conses each new level, as upstream's [do_while] does.
             Thus maximal sets precede their subsets for the antichain pass. *)
          val levels = grow singles (map (fn index => [index]) singles) []
          val maximals = List.concat (find_max_subsets levels)
        in
          {result = (name, SOME maximals), skipped = !skipped}
        end
    end

  fun check_unused_assms config named_theorem =
    #result (check_detailed config named_theorem)

  fun sort_theorems theorems =
    Listsort.sort (fn ((left, _), (right, _)) =>
      String.compare (left, right)) theorems

  (* Keep theorem probes serial as well as forcing serial backend execution
     inside each probe. *)
  fun detailed_theory config theory =
    map (check_detailed config) (sort_theorems (DB.thms theory))

  fun find_unused_assms config theory =
    map #result (detailed_theory config theory)

  fun indexes_text indexes =
    String.concatWith " and "
      (map (Int.toString o (fn index => index + 1))
        (Listsort.sort Int.compare indexes))

  fun theorem_text (name, sets) =
    name ^ ": unnecessary assumption " ^
    String.concatWith " or " (map indexes_text sets)

  fun print_unused_assms config requested_theory =
    let
      val theory =
        case requested_theory of
            NONE => Theory.current_theory ()
          | SOME name => name
      val checked = detailed_theory config theory
      val results = map #result checked
      val total = length results
      val with_assumptions =
        length (List.filter (Option.isSome o #2) results)
      val superfluous = List.mapPartial (fn (_, NONE) => NONE
        | (_, SOME []) => NONE
        | (name, SOME sets) => SOME (name, sets)) results
      val skipped = List.foldl (fn (item, count) =>
        #skipped item + count) 0 checked
      val lines =
        ["Found " ^ Int.toString (length superfluous) ^
         " theorems with (potentially) superfluous assumptions:", ""] @
        map theorem_text superfluous @
        ["", "Checked " ^ Int.toString with_assumptions ^
         " theorems with assumptions (" ^ Int.toString total ^
         " total) in the theory \"" ^ theory ^ "\"",
         "Skipped " ^ Int.toString skipped ^ " inconclusive probes."]
    in
      Feedback.HOL_MESG (String.concatWith "\n" lines ^ "\n")
    end
end
