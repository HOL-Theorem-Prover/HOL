structure hhLearn :> hhLearn =
struct

open HolKernel aiLib

val ERR = mk_HOL_ERR "hhLearn"

type constants =
  {init_val : real,
   pos_weight : real,
   def_val : real,
   tau : real,
   def_prior_weight : int,
   max_dependencies : int,
   log_base : real,
   unit_weight : real,
   steep_base : real,
   smooth_base : real,
   smooth_exponent : real,
   smooth_rank_factor : real,
   smooth_offset : real,
   scaled_avg_factor : real,
   nb_mesh_weight : real,
   knn_mesh_weight : real,
   chained_weight : real,
   proximity_weight : real,
   learner_weight : real,
   final_mepo_weight : real,
   final_mash_weight : real,
   max_proximity_facts : int,
   over_request_numerator : int,
   over_request_denominator : int,
   max_suggestions_factor : int,
   max_suggestions_extra : int}

(* Isabelle's learner and mesh constants are kept in one value.  Later tuning
   must replace this record as a whole rather than mixing parameter sets. *)
val default_constants : constants =
  {init_val = 30.0,
   pos_weight = 5.0,
   def_val = ~18.0,
   tau = 0.2,
   def_prior_weight = 1000,
   max_dependencies = 20,
   log_base = 2.0,
   unit_weight = 1.0,
   steep_base = 0.62,
   smooth_base = 1.3,
   smooth_exponent = 15.5,
   smooth_rank_factor = 0.2,
   smooth_offset = 15.0,
   scaled_avg_factor = 100000000.0,
   nb_mesh_weight = 0.5,
   knn_mesh_weight = 0.5,
   chained_weight = 0.9,
   proximity_weight = 0.4,
   learner_weight = 0.1,
   final_mepo_weight = 0.5,
   final_mash_weight = 0.5,
   max_proximity_facts = 100,
   over_request_numerator = 51,
   over_request_denominator = 50,
   max_suggestions_factor = 2,
   max_suggestions_extra = 25}

type frequency_table = (int, int) Redblackmap.dict
type weight_table = (int, real) Redblackmap.dict
type idf_table =
  {nfacts : int, dffreq : frequency_table, weights : weight_table}

fun increment key table =
  case Redblackmap.peek (table, key) of
      SOME count => dadd key (count + 1) table
    | NONE => dadd key 1 table

fun create_idf_table facts =
  let
    fun add_fact ((_, features), (nfacts, frequencies)) =
      (nfacts + 1,
       foldl (fn (feature, table) => increment feature table)
         frequencies (mk_fast_set Int.compare features))
    val (nfacts, dffreq) =
      foldl add_fact (0, dempty Int.compare) facts
    val ln_nfacts =
      if nfacts = 0 then 0.0 else Math.ln (Real.fromInt nfacts)
    val weights = dmap (fn (_, frequency) =>
      ln_nfacts - Math.ln (Real.fromInt frequency)) dffreq
  in
    {nfacts = nfacts, dffreq = dffreq, weights = weights}
  end

fun idf_nfacts ({nfacts, ...} : idf_table) = nfacts

fun document_frequency ({dffreq, ...} : idf_table) feature =
  Redblackmap.peek (dffreq, feature)

fun idf_of ({weights, ...} : idf_table) feature =
  Redblackmap.peek (weights, feature)

(* Ranking can expand the fetchable subset, but training needs the original
   proof's completeness and size before any missing dependencies are removed. *)
type dep_info =
  {fetchable : mlThmData.thmid list, intact : bool, count : int}
type dep_table = (mlThmData.thmid, dep_info) Redblackmap.dict

(* The target's (name, theorem) inventory keys its thmdata.  Unchanged
   theorems are usually the very same objects, so the pointer test makes
   the warm comparison linear without rendering any terms. *)
fun same_inventory_entry ((left_name, left_thm), (right_name, right_thm)) =
  left_name = right_name andalso
  (Portable.pointer_eq (left_thm, right_thm) orelse
   goal_compare (dest_thm left_thm, dest_thm right_thm) = EQUAL)

fun same_inventory ((left_target, left_entries),
                    (right_target, right_entries)) =
  left_target = right_target andalso
  ListPair.allEq same_inventory_entry (left_entries, right_entries)

type target_thmdata_cache_key = string * (string * thm) list
val target_thmdata_cache = ref
  (NONE : (target_thmdata_cache_key * mlThmData.thmdata) option)
val target_thmdata_build_count = ref 0

fun target_thmdata_cache_size () =
  if Option.isSome (!target_thmdata_cache) then 1 else 0

fun target_thmdata_cache_builds () = !target_thmdata_build_count

fun clean_target_thmdata_cache () =
  (target_thmdata_cache := NONE; target_thmdata_build_count := 0)

fun create_thmdata_for target =
  let
    val theories = Theory.ancestry target @ [target]
    fun qualify theory (name, theorem) =
      (theory ^ "Theory." ^ name, theorem)
    val database_entries = List.concat (map (fn theory =>
      map (qualify theory) (DB.thms theory)) theories)
    (* Namespace values belong to the interactive ambient context and have
       no theory ownership metadata.  Preserve legacy behavior only when
       that ambient theory is the requested target; an explicit historical
       or evaluation target must be independent of unrelated session state. *)
    val namespace_entries =
      if Theory.current_theory () = target then
        map (qualify mlThmData.namespace_tag)
          (mlThmData.unsafe_namespace_thms ())
      else []
    val entries = database_entries @ namespace_entries
    val key = (target, entries)
    fun add ((name, theorem), (facts, seen)) =
      let val theorem_goal = dest_thm theorem in
        if dmem theorem_goal seen orelse not (uptodate_thm theorem) orelse
           not (null (hyp theorem)) then
          (facts, seen)
        else
          ((name, mlFeature.fea_of_goal_cached true theorem_goal) :: facts,
           dadd theorem_goal () seen)
      end
    fun build () =
      let
        val (facts, _) = foldl add
          ([], dempty goal_compare) entries
      in
        (mlFeature.learn_tfidf facts, facts)
      end
  in
    case !target_thmdata_cache of
        SOME (cached_key, thmdata) =>
          if same_inventory (cached_key, key) then thmdata
          else
            let val replacement = build () in
              target_thmdata_build_count :=
                !target_thmdata_build_count + 1;
              target_thmdata_cache := SOME (key, replacement);
              replacement
            end
      | NONE =>
          let val thmdata = build () in
            target_thmdata_build_count := 1;
            target_thmdata_cache := SOME (key, thmdata);
            thmdata
          end
  end

fun intact_dependencies names : dep_info =
  {fetchable = names, intact = true, count = length names}

fun dep_table_of entries =
  dnew String.compare (map (fn (name, dependencies) =>
    (name, intact_dependencies dependencies)) entries)

fun build_dep_table dependencies facts =
  foldl
    (fn ((thmid, _), table) =>
      if dmem thmid table then table
      else dadd thmid (intact_dependencies (dependencies thmid)) table)
    (dempty String.compare) facts

val raw_dependencies = Dep.depidl_of o Tag.dep_of o Thm.tag

(* Resolve the same entries as mlThmData, building each theory's index
   once. A theory with an unsaved theorem keeps the original scan, which
   raises if it reaches that theorem before finding the dependency. *)
fun dependency_lookup () =
  let
    val indices = ref (dempty String.compare)
    fun build theory =
      SOME (foldl (fn ((name, theorem), table) =>
        let val number = mlThmData.depnumber_of_thm theorem in
          if dmem number table then table else dadd number name table
        end) (dempty Int.compare) (DB.thms theory))
      handle HOL_ERR _ => NONE
    fun index theory =
      case Redblackmap.peek (!indices, theory) of
          SOME result => result
        | NONE =>
            let val result = build theory in
              indices := dadd theory result (!indices);
              result
            end
    fun scan theory number =
      Option.map #1 (List.find (fn (_, theorem) =>
        number = mlThmData.depnumber_of_thm theorem) (DB.thms theory))
    fun thmid_of_depid (theory, number) =
      let
        val found =
          case index theory of
              NONE => scan theory number
            | SOME table => Redblackmap.peek (table, number)
      in
        case found of
            SOME name =>
              (case total (DB.fetch theory) name of
                   SOME theorem =>
                     if uptodate_thm theorem
                     then SOME (theory ^ "Theory." ^ name)
                     else NONE
                 | NONE => NONE)
          | NONE => NONE
      end
  in
    thmid_of_depid
  end

(* Keep only completed lookups, so failures still reach the caller. *)
fun memoize compare compute =
  let
    val table = ref (dempty compare)
  in
    fn key =>
      case Redblackmap.peek (!table, key) of
          SOME result => result
        | NONE =>
            let val result = compute key in
              table := dadd key result (!table);
              result
            end
  end

fun dependency_resolver () =
  List.mapPartial (memoize Dep.depid_compare (dependency_lookup ()))

fun create_dep_table (_, facts) =
  let
    (* Freshness is constant during this build, but checking it repeatedly
       traverses the same shared dependency theorems. *)
    val resolve = dependency_resolver ()
    fun dependency_info thmid =
      case total mlThmData.thm_of_name thmid of
          SOME (SOME (_, theorem)) =>
            let val (theory, _) = split_string "Theory." thmid in
              if theory = mlThmData.namespace_tag then
                SOME (intact_dependencies [])
              else
                let
                  val raw = raw_dependencies theorem
                  val fetchable = resolve raw
                  val count = length raw
                in
                  SOME {fetchable = fetchable,
                        intact = count = length fetchable, count = count}
                end
            end
        | _ => NONE
    fun add ((thmid, _), table) =
      if dmem thmid table then table
      else
        case dependency_info thmid of
            SOME info => dadd thmid info table
          | NONE => table
  in
    foldl add (dempty String.compare) facts
  end

fun dependencies_of (table : dep_table) thmid =
  Option.map #fetchable (Redblackmap.peek (table, thmid))

fun pure_logic_concl conclusion =
  let
    fun nonlogical_constant (_, term) =
      if is_const term then
        let val {Thy, ...} = dest_thy_const term in
          if Thy = "min" orelse Thy = "bool" then NONE else SOME ()
        end
      else NONE
  in
    not (Option.isSome (gen_find_term nonlogical_constant conclusion))
  end

type fact_info =
  {thmid : mlThmData.thmid,
   features : mlFeature.fea,
   def : bool,
   concl : term option}

type score_parts =
  {prior : real,
   positive : real,
   absent : real,
   negative : real,
   total : real}

(* A fact's features in increasing order, each with its frequency and
   its precomputed term of the negative (absent-from-goal) sum. *)
type fact_feature = {feature : int, frequency : int, negative : real}
type nb_model =
  {constants : constants,
   idf : idf_table,
   names : mlThmData.thmid vector,
   indices : (mlThmData.thmid, int) Redblackmap.dict,
   tfreq : int vector,
   sfreq : fact_feature vector vector}

fun add_index ((fact : fact_info), (index, table)) =
  let val thmid = #thmid fact in
    if dmem thmid table then
      raise ERR "train_nb" ("duplicate theorem identifier " ^ thmid)
    else (index + 1, dadd thmid index table)
  end

fun index_facts facts = #2 (foldl add_index (0, dempty String.compare) facts)

fun add_weight amount key table =
  case Redblackmap.peek (table, key) of
      SOME count => dadd key (count + amount) table
    | NONE => dadd key amount table

fun validate_training idf (facts : fact_info list) =
  let
    val _ =
      if idf_nfacts idf = length facts then ()
      else raise ERR "train_nb" "IDF and fact-table sizes differ"
    fun require_feature feature =
      if Option.isSome (idf_of idf feature) then ()
      else raise ERR "train_nb" "fact feature is absent from IDF table"
  in
    List.app (List.app require_feature o #features) facts
  end

fun train_nb_indexed constants idf dependencies facts indices =
  let
    val number = length facts
    val information = Vector.fromList facts
    val names = Vector.map #thmid information
    val pure_logic = Vector.map
      (fn (fact : fact_info) =>
        case #concl fact of
            SOME conclusion => pure_logic_concl conclusion
          | NONE => false)
      information
    val tfreq = Array.array (number, 0)
    val sfreq = Array.tabulate (number, fn _ => dempty Int.compare)

    fun add_use weight target features =
      let
        val frequencies = Array.sub (sfreq, target)
        val frequencies' = foldl
          (fn (feature, table) => add_weight weight feature table)
          frequencies features
      in
        Array.update (tfreq, target,
          Array.sub (tfreq, target) + weight);
        Array.update (sfreq, target, frequencies')
      end

    fun pure_dependency thmid =
      let
        val index = dfind thmid indices
      in
        Vector.sub (pure_logic, index)
      end

    fun usable_dependencies (fact : fact_info) =
      case Redblackmap.peek (dependencies, #thmid fact) of
          NONE => []
        | SOME {fetchable, intact, count} =>
            if #def fact orelse not intact orelse
               count > #max_dependencies constants orelse
               not (List.all (fn thmid => dmem thmid indices)
                 fetchable)
            then []
            else filter (not o pure_dependency)
              (mk_fast_set String.compare fetchable)

    fun learn index =
      if index = number then ()
      else
        let
          val fact = Vector.sub (information, index)
          val features = mk_fast_set Int.compare (#features fact)
          val _ = add_use (#def_prior_weight constants) index features
          val _ = List.app
            (fn dependency =>
              add_use 1 (dfind dependency indices) features)
            (usable_dependencies fact)
        in
          learn (index + 1)
        end
    val _ = learn 0
    fun fact_features index =
      let
        val total_frequency = Real.fromInt (Array.sub (tfreq, index))
        fun entry (feature, frequency) =
          {feature = feature, frequency = frequency,
           negative = valOf (idf_of idf feature) * Math.ln
             (1.0 - Real.fromInt (frequency - 1) / total_frequency)}
      in
        Vector.fromList (map entry (dlist (Array.sub (sfreq, index))))
      end
  in
    {constants = constants, idf = idf, names = names,
     indices = indices, tfreq = Array.vector tfreq,
     sfreq = Vector.tabulate (number, fact_features)}
  end

fun train_nb constants idf dependencies facts =
  (validate_training idf facts;
   train_nb_indexed constants idf dependencies facts (index_facts facts))

fun conclusion_of thmid =
  case total mlThmData.thm_of_name thmid of
      SOME (SOME (_, theorem)) => SOME (Thm.concl theorem)
    | _ => NONE

(* A theorem with hypotheses is no premise: exporters would state its
   conclusion unconditionally (or discharged), and Metis replay cites it
   by name, hypotheses included, so a proof using it never verifies. *)
fun has_hypotheses thmid =
  case total mlThmData.thm_of_name thmid of
      SOME (SOME (_, theorem)) => not (null (hyp theorem))
    | _ => false

fun fact_info statures (thmid, features) : fact_info =
  {thmid = thmid, features = features,
   def = #def (hhStature.stature_of statures thmid),
   concl = conclusion_of thmid}

fun train_nb_from_thmdata constants idf dependencies statures (_, facts) =
  train_nb constants idf dependencies (map (fact_info statures) facts)

fun model_index ({indices, ...} : nb_model) thmid =
  Redblackmap.peek (indices, thmid)

fun nb_tfreq (model as {tfreq, ...} : nb_model) thmid =
  case model_index model thmid of
      SOME index => SOME (Vector.sub (tfreq, index))
    | NONE => NONE

fun nb_sfreq (model as {sfreq, ...} : nb_model) thmid feature =
  case model_index model thmid of
      SOME index =>
        Option.map #frequency
          (Vector.find (fn entry => #feature entry = feature)
             (Vector.sub (sfreq, index)))
    | NONE => NONE

(* The goal's known features in increasing order, with summed weights
   and their IDF. *)
fun known_goal_features ({idf, ...} : nb_model) goal_features =
  let
    fun add ((feature, weight), table) =
      if Option.isSome (idf_of idf feature) then
        case Redblackmap.peek (table, feature) of
            SOME old => dadd feature (old + weight) table
          | NONE => dadd feature weight table
      else table
  in
    map (fn (feature, weight) =>
      (feature, weight, valOf (idf_of idf feature)))
      (dlist (foldl add (dempty Int.compare) goal_features))
  end

(* Both feature lists are increasing, so one merge pass splits them into
   shared, goal-only and fact-only features.  Each sum accumulates in the
   same order as a goal-ordered fold followed by a fact-ordered fold. *)
fun nb_score_parts_prepared (model as
      {constants, tfreq, sfreq, ...} : nb_model)
      prepared_goal_features thmid =
  case model_index model thmid of
      NONE => NONE
    | SOME index =>
        let
          val total_frequency = Real.fromInt (Vector.sub (tfreq, index))
          val fact_features = Vector.sub (sfreq, index)
          val size = Vector.length fact_features
          fun absent_term weight feature_idf =
            weight * feature_idf * #def_val constants
          fun walk goal position (positive, absent, negative) =
            if position = size then
              (positive,
               foldl (fn ((_, weight, feature_idf), sum) =>
                 sum + absent_term weight feature_idf) absent goal,
               negative)
            else
              let val entry = Vector.sub (fact_features, position) in
                case goal of
                    [] => walk goal (position + 1)
                      (positive, absent, negative + #negative entry)
                  | (feature, weight, feature_idf) :: rest =>
                      if feature < #feature entry then
                        walk rest position
                          (positive,
                           absent + absent_term weight feature_idf,
                           negative)
                      else if feature > #feature entry then
                        walk goal (position + 1)
                          (positive, absent, negative + #negative entry)
                      else
                        walk rest (position + 1)
                          (positive + weight * feature_idf *
                             Math.ln (#pos_weight constants *
                               Real.fromInt (#frequency entry) /
                               total_frequency),
                           absent, negative)
              end
          val prior = #init_val constants * Math.ln total_frequency
          val (positive, absent, negative_sum) =
            walk prepared_goal_features 0 (0.0, 0.0, 0.0)
          val negative = #tau constants * negative_sum
          val total = prior + positive + absent + negative
        in
          SOME {prior = prior, positive = positive, absent = absent,
                negative = negative, total = total}
        end

fun nb_score_parts model goal_features thmid =
  nb_score_parts_prepared model
    (known_goal_features model goal_features) thmid

fun nb_scores model {pool, goal_features} =
  let
    (* Normalization is query-wide.  Keeping it outside the candidate loop is
       load-bearing for the large pools used by the live hammer. *)
    val prepared_goal_features = known_goal_features model goal_features
  in
    List.mapPartial
      (fn thmid =>
        case nb_score_parts_prepared model prepared_goal_features thmid of
            SOME parts => SOME (thmid, #total parts)
          | NONE => NONE)
      pool
  end

fun take count items =
  #1 (part_n count items)

fun nb_rank model {pool, goal_features, n} =
  nb_scores model {pool = pool, goal_features = goal_features}
  |> Listsort.sort
       (fn ((_, left), (_, right)) => Real.compare (right, left))
  |> take n
  |> map #1

type scored_facts = (mlThmData.thmid * real) list
type mesh_channel = real * (scored_facts * mlThmData.thmid list)

fun steep_weight rank =
  Math.pow (#steep_base default_constants,
    Math.ln (Real.fromInt (rank + 1)) /
      Math.ln (#log_base default_constants))

fun smooth_weight rank =
  Math.pow (#smooth_base default_constants,
    #smooth_exponent default_constants -
    #smooth_rank_factor default_constants * Real.fromInt rank) +
  #smooth_offset default_constants

fun weight_facts weight facts =
  Portable.mapi (fn index => fn fact => (fact, weight index)) facts

val weight_facts_steeply = weight_facts steep_weight
val weight_facts_smoothly = weight_facts smooth_weight

fun average [] = 0.0
  | average values =
      foldl op+ 0.0 values / Real.fromInt (length values)

fun normalize_scores _ [] = []
  | normalize_scores max_facts scores =
      let
        val mean = average (map #2 (take max_facts scores))
      in
        map (fn (fact, score) => (fact, score / mean)) scores
      end

(* Facts are compared through a key that maps every fact stating the same
   proposition to one representative. *)
fun key_set key facts =
  foldl (fn (fact, set) => Redblackset.add (set, key fact))
    (Redblackset.empty String.compare) facts

fun distinct_by key facts =
  let
    fun add (fact, (seen, result)) =
      let val fact_key = key fact in
        if Redblackset.member (seen, fact_key) then (seen, result)
        else (Redblackset.add (seen, fact_key), fact :: result)
      end
  in
    rev (#2 (foldl add (Redblackset.empty String.compare, []) facts))
  end

val distinct = mk_sameorder_set String.compare

fun name_set names = dset String.compare names

fun member_set set item = dmem item set

fun scaled_average [] = 0
  | scaled_average values =
      Real.ceil (#scaled_avg_factor default_constants *
        foldl op+ 0.0 values) div length values

fun mesh_rank_by unknown_set key max_facts channels =
  if max_facts <= 0 then []
  else
    let
      (* A fact's score in a channel is that of the first entry with
         its key. *)
      fun first_scores scores =
        foldl (fn ((fact, score), table) =>
          let val fact_key = key fact in
            if dmem fact_key table then table
            else dadd fact_key score table
          end) (dempty String.compare) scores
      fun prepare (weight, (selected, unknown)) =
        (weight,
         first_scores (normalize_scores max_facts selected),
         unknown_set unknown)
      val prepared = map prepare channels
      fun add_channel ((_, (selected, _)), (seen, candidates)) =
        foldl (fn ((fact, _), (seen, result)) =>
          let val fact_key = key fact in
            if Redblackset.member (seen, fact_key) then (seen, result)
            else (Redblackset.add (seen, fact_key), fact :: result)
          end) (seen, candidates)
          (take max_facts selected)
      val (_, candidates) =
        foldl add_channel (Redblackset.empty String.compare, [])
          channels
      fun contribution fact_key (weight, scores, unknown) =
        case Redblackmap.peek (scores, fact_key) of
            SOME score => SOME (weight * score)
          | NONE =>
              if Redblackset.member (unknown, fact_key) then NONE
              else SOME 0.0
      fun score index fact =
        (scaled_average
           (List.mapPartial (contribution (key fact)) prepared),
         index, fact)
      fun compare ((left, left_index, _),
                   (right, right_index, _)) =
        case Int.compare (right, left) of
            EQUAL => Int.compare (left_index, right_index)
          | order => order
    in
      Portable.mapi score candidates
      |> Listsort.sort compare
      |> take max_facts
      |> map #3
    end

fun mesh_facts_by _ max_facts [] = []
  | mesh_facts_by key max_facts [(_, (selected, unknown))] =
      distinct_by key
        (map #1 (take max_facts selected) @
         take (max_facts - Int.min (max_facts, length selected)) unknown)
  | mesh_facts_by key max_facts channels =
      mesh_rank_by (key_set key) key max_facts channels

fun mesh_facts max_facts channels =
  mesh_facts_by I max_facts channels

fun subtract_by _ [] items = items
  | subtract_by key removed items =
      let val keys = key_set key removed in
        filter (fn fact => not (Redblackset.member (keys, key fact))) items
      end

fun merge_mash_channels_by key
      {max_facts, suggestions, facts, chained, unknown} =
  let
    val proximate = take (#max_proximity_facts default_constants) facts
    val unknown_keys = key_set key unknown
    fun unknown_in facts =
      filter (fn fact => Redblackset.member (unknown_keys, key fact)) facts
    val unknown_chained = unknown_in chained
    val unknown_proximate = unknown_in proximate
    val empty_keys = Redblackset.empty String.compare
    val used_unknown = unknown_chained @ unknown_proximate
    val channels =
      [(#chained_weight default_constants,
        (map (fn fact => (fact, #unit_weight default_constants))
          unknown_chained, empty_keys)),
       (#proximity_weight default_constants,
        (weight_facts_smoothly unknown_proximate, empty_keys)),
       (#learner_weight default_constants,
        (weight_facts_steeply suggestions, unknown_keys))]
  in
    (mesh_rank_by I key max_facts channels,
     subtract_by key used_unknown unknown)
  end

fun merge_mash_channels parameters =
  merge_mash_channels_by I parameters

fun over_request n =
  n * #over_request_numerator default_constants div
    #over_request_denominator default_constants

fun exclude_and_take excluded n facts =
  take n (filter (not o excluded) facts)

type context =
  {thmdata : mlThmData.thmdata,
   fact_index : (mlThmData.thmid * mlFeature.fea) hhFactIndex.index,
   model : nb_model Susp.susp,
   statures : hhStature.statures,
   mepo : hhMePo.context,
   dependencies : dep_table,
   fact_key : (mlThmData.thmid -> mlThmData.thmid) Susp.susp,
   unknown : mlThmData.thmid list,
   pool_order : mlThmData.thmid list}

type cache_key = string * (mlThmData.thmid * mlFeature.fea) list
datatype cached_context =
    Lightweight of mlThmData.thmdata
  | Prepared of context
val context_cache = ref (NONE : (cache_key * cached_context) option)

fun clean_context_cache () =
  (context_cache := NONE; clean_target_thmdata_cache ())

fun context_key_for current (_, facts) = (current, facts)

fun same_key ((left_current, left_facts),
              (right_current, right_facts)) =
  left_current = right_current andalso left_facts = right_facts

fun cached_context key =
  case !context_cache of
      SOME (cached_key, data) =>
        if same_key (key, cached_key) then SOME data else NONE
    | NONE => NONE

(* Facts whose conclusions are alpha-equivalent state the same
   proposition; each such class is represented by its first fact.  Other
   names, including those without a fetchable theorem, represent
   themselves. *)
fun proposition_key conclusions =
  let
    fun add ((thmid, concl), (keys, representatives)) =
      case concl of
          SOME conclusion =>
            (case Redblackmap.peek (representatives, conclusion) of
                 SOME representative =>
                   if thmid = representative then (keys, representatives)
                   else (dadd thmid representative keys, representatives)
               | NONE => (keys, dadd conclusion thmid representatives))
        | NONE => (keys, representatives)
    val (keys, _) = foldl add
      (dempty String.compare, dempty Term.compare) conclusions
  in
    fn thmid => Option.getOpt (Redblackmap.peek (keys, thmid), thmid)
  end

(* Without a separate training corpus, every candidate belongs to the model. *)
fun make_context_for current (thmdata as (_, facts)) training dependencies =
  let
    val (_, model_facts) = Option.getOpt (training, thmdata)
    val statures = hhStature.create_statures_for current
    (* Resolve the model's facts before deferring its training. *)
    val training_facts = map (fact_info statures) model_facts
    val indices = index_facts training_facts
    val model = Susp.delay (fn () =>
      train_nb_indexed default_constants (create_idf_table model_facts)
        dependencies training_facts indices)
    val conclusions =
      case training of
          NONE => map (fn fact => (#thmid fact, #concl fact)) training_facts
        | SOME _ => map (fn (thmid, _) => (thmid, conclusion_of thmid)) facts
    val fact_key = Susp.delay (fn () => proposition_key conclusions)
    val unknown =
      case training of
          NONE => []
        | SOME _ =>
            let val trained = Susp.force model in
              List.mapPartial (fn (thmid, _) =>
                if Option.isSome (model_index trained thmid) then NONE
                else SOME thmid) facts
            end
  in
    {thmdata = thmdata, fact_index = hhFactIndex.create #1 facts,
     model = model,
     statures = statures,
     mepo = hhMePo.create_context_for current thmdata statures,
     dependencies = dependencies, fact_key = fact_key, unknown = unknown,
     pool_order = map #1 facts}
  end

fun force_context (context : context) =
  (ignore (Susp.force (#model context));
   ignore (Susp.force (#fact_key context));
   context)

fun make_context {thmdata, model_thmdata, dependencies} =
  force_context (make_context_for (Theory.current_theory ()) thmdata
    (SOME model_thmdata) dependencies)

(* Externally built thmdata (mlThmData.create_thmdata, as holyhammer and
   TacticToe pass it) may hold top-level theorems with hypotheses. *)
fun without_hypotheses (weights, facts) =
  (weights, filter (not o has_hypotheses o #1) facts)

fun build_context_for current thmdata =
  make_context_for current thmdata NONE (create_dep_table thmdata)

fun cached_or_build_context prepare current thmdata =
  let
    val key = context_key_for current thmdata
    fun build data =
      let val context = prepare (build_context_for current data) in
        context_cache := SOME (key, Prepared context);
        context
      end
  in
    case cached_context key of
        SOME (Prepared context) => prepare context
      | SOME (Lightweight data) => build data
      | NONE => build (without_hypotheses thmdata)
  end

fun create_context_for current thmdata =
  cached_or_build_context force_context current thmdata

fun create_deferred_context_for current thmdata =
  cached_or_build_context I current thmdata

fun create_context thmdata =
  create_context_for (Theory.current_theory ()) thmdata

fun context_thmids ({pool_order, ...} : context) = pool_order

fun restrict_thmdata ({thmdata = (weights, facts), ...} : context) NONE =
      (weights, facts)
  | restrict_thmdata
      ({thmdata = (weights, _), fact_index, ...} : context)
      (SOME wanted) =
      (weights, hhFactIndex.select fact_index wanted)

fun restrict_unknown ({unknown = [], ...} : context) _ = []
  | restrict_unknown {unknown, ...} NONE = unknown
  | restrict_unknown {unknown, ...} (SOME wanted) =
      filter (member_set wanted) unknown

fun add_thmdep dependencies max_facts predictions =
  let
    fun expand remaining seen result pending predictions =
      if remaining <= 0 then rev result
      else
        case pending of
            name :: rest =>
              if Redblackset.member (seen, name) then
                expand remaining seen result rest predictions
              else
                expand (remaining - 1) (Redblackset.add (seen, name))
                  (name :: result) rest predictions
          | [] =>
              case predictions of
                  [] => rev result
                | prediction :: rest =>
                    expand remaining seen result
                      (prediction :: Option.getOpt
                        (dependencies_of dependencies prediction, []))
                      rest
  in
    expand max_facts (Redblackset.empty String.compare) [] [] predictions
  end

type mash_result =
  {ranking : mlThmData.thmid list,
   unknown : mlThmData.thmid list,
   learner : mlThmData.thmid list,
   max_suggestions : int}

fun suggestion_limit max_facts =
  #max_suggestions_factor default_constants * max_facts +
  #max_suggestions_extra default_constants

fun nb_predict model pool features n =
  nb_rank model {pool = pool, n = n, goal_features =
    map (fn feature => (feature, #unit_weight default_constants)) (features ())}

fun knn_predict thmdata features n =
  mlNearestNeighbor.thmknn thmdata n (features ())

fun mash_leg (context as {dependencies, fact_key, ...} : context)
      wanted names {nb, knn} max_facts =
  if max_facts <= 0 then
    {ranking = [], unknown = [], learner = [], max_suggestions = 0}
  else
    let
      val max_suggestions = suggestion_limit max_facts
      val nb = nb max_suggestions
      val knn = knn max_suggestions
      val learner = mesh_facts max_suggestions
        [(#nb_mesh_weight default_constants,
          (weight_facts_steeply nb, [])),
         (#knn_mesh_weight default_constants,
          (weight_facts_steeply knn, []))]
      val (merged, remaining_unknown) =
        merge_mash_channels_by (Susp.force fact_key)
        {max_facts = max_suggestions, suggestions = learner,
         facts = names, chained = [],
         unknown = restrict_unknown context wanted}
    in
      {ranking = add_thmdep dependencies max_facts merged,
       unknown = remaining_unknown, learner = learner,
       max_suggestions = max_suggestions}
    end

fun restricted_names context NONE _ = context_thmids context
  | restricted_names _ (SOME _) facts = map (fn (thmid, _) => thmid) facts

fun direct_predictions ({model, ...} : context) goal =
  let
    val suspended = Susp.delay (fn () => mlFeature.fea_of_goal true goal)
    fun features () = Susp.force suspended
  in
    {nb = fn names => nb_predict (Susp.force model) names features,
     knn = fn thmdata => knn_predict thmdata features}
  end

fun mash_details context {pool, goal, max_facts} =
  let
    val wanted = Option.map name_set pool
    val restricted as (_, facts) = restrict_thmdata context wanted
    val names = restricted_names context pool facts
    val {nb, knn} = direct_predictions context goal
  in
    mash_leg context wanted names {nb = nb names, knn = knn restricted}
      max_facts
  end

fun knn_expander resolve_dependencies thmid =
  let val (theory, name) = split_string "Theory." thmid in
    thmid ::
      (if theory = mlThmData.namespace_tag then []
       else resolve_dependencies (raw_dependencies (DB.fetch theory name)))
  end

fun expand_knn with_dependencies n predictions =
  take n (distinct (List.concat (map with_dependencies predictions)))

fun rank_knn_with resolve_dependencies thmdata n goal =
  expand_knn (knn_expander resolve_dependencies) n
    (knn_predict thmdata (fn () => mlFeature.fea_of_goal true goal) n)

fun rank_knn thmdata n goal =
  rank_knn_with (dependency_resolver ()) thmdata n goal

fun make_dependency_lookup () =
  let
    val resolve = dependency_resolver ()
    fun intact theorem =
      let
        val deps = raw_dependencies theorem
          handle HOL_ERR _ => raise mk_HOL_ERR "mlThmData" "depidl_of_thm" ""
        val names = resolve deps
      in
        (length deps = length names, names)
      end
  in
    {intact = intact, knn = rank_knn_with resolve}
  end

fun is_induction statures thmid =
  #induction (hhStature.stature_of statures thmid)

fun rank_inputs context pool =
  let
    val wanted = Option.map name_set pool
    val restricted as (_, facts) = restrict_thmdata context wanted
    val names = Susp.delay (fn () => restricted_names context pool facts)
    val mepo = Susp.delay (fn () =>
      case pool of
          NONE => #mepo context
        | SOME _ => hhMePo.restrict_context (#mepo context) (Susp.force names))
  in
    {wanted = wanted, restricted = restricted, names = names, mepo = mepo}
  end

fun rank_with_predictions (context as {statures, fact_key, ...} : context)
      {wanted, names, mepo, restricted = _} {nb, knn} goal shared_depths =
  let
    fun pool_names () = Susp.force names
    fun share calculate =
      case shared_depths of
          _ :: _ :: _ =>
            let val cached = memoize Int.compare calculate in
              fn depth =>
                if List.exists (fn shared => depth = shared) shared_depths
                then cached depth else calculate depth
            end
        | _ => calculate
    val mepo_leg = share
      (fn depth => hhMePo.mepo_rank (Susp.force mepo) goal depth)
    val mash = share (fn depth =>
      mash_leg context wanted (pool_names ()) {nb = nb, knn = knn} depth)
    fun rank_one (filter, n) =
      let
        val generous = over_request n
        fun finish ranking =
          first_test_n (not o is_induction statures) n ranking
      in
        case filter of
            "none" => pool_names ()
          | "knn" =>
              expand_knn (knn_expander (dependency_resolver ())) n (knn n)
          | "mepo" => finish (mepo_leg generous)
          | "mash" => finish (#ranking (mash generous))
          | "mesh" =>
              let
                (* Apply the induction filter and caller's bound before
                   meshing, to preserve normalization and the cutoff. *)
                val mepo_ranking = finish (mepo_leg generous)
                val mash_result = mash generous
                val mash_ranking = finish (#ranking mash_result)
                val unknown = #unknown mash_result
              in
                mesh_facts_by (Susp.force fact_key) n
                  [(#final_mepo_weight default_constants,
                    (weight_facts_steeply mepo_ranking, [])),
                   (#final_mash_weight default_constants,
                    (weight_facts_steeply mash_ranking, unknown))]
              end
          | _ => raise ERR "rank" ("unknown premise filter " ^ filter)
      end
  in
    rank_one
  end

(* Both learners order the entire pool independently of the requested depth.
   Their raw prefixes can be reused before merging and dependency expansion. *)
fun shared_prefix limit predict =
  let val largest = Susp.delay (fn () => predict limit) in
    fn n =>
      if n = limit then Susp.force largest
      else if n < 0 orelse n > limit then predict n
      else take n (Susp.force largest)
  end

(* The prediction inputs are fixed by this goal and pool. Defer each
   learner until a filter asks for it. *)
fun rank_for_filters context {pool, goal} filters =
  let
    val {knn, nb} = direct_predictions context goal
    fun limits ((filter, n), (knn_max, nb_max)) =
      if filter = "knn" then (Int.max (knn_max, n), nb_max)
      else if (filter = "mash" orelse filter = "mesh") andalso n > 0 then
        let val depth = suggestion_limit (over_request n) in
          (Int.max (knn_max, depth), Int.max (nb_max, depth))
        end handle Overflow => (knn_max, nb_max)
      else (knn_max, nb_max)
    val (knn_max, nb_max) = foldl limits (0, 0) filters
    val inputs as {restricted, names, ...} = rank_inputs context pool
    val predictions =
      {knn = shared_prefix knn_max (knn restricted),
       nb = shared_prefix nb_max (fn n => nb (Susp.force names) n)}
    fun component_depth (filter, n) =
      if filter = "mepo" orelse filter = "mash" orelse filter = "mesh" then
        SOME (over_request n) handle Overflow => NONE
      else NONE
    val shared_depths = List.mapPartial component_depth filters
  in
    rank_with_predictions context inputs predictions goal shared_depths
  end

fun rank context {filter, pool, goal, n} =
  let
    val inputs as {restricted, names, ...} = rank_inputs context pool
    val {knn, nb} = direct_predictions context goal
  in
    rank_with_predictions context inputs
      {knn = knn restricted, nb = fn n => nb (Susp.force names) n}
      goal [] (filter, n)
  end

fun rank_filters thmdata goal filters =
  if List.all (fn (filter, _) => filter = "knn" orelse filter = "none")
       filters then
    let
      val key = context_key_for (Theory.current_theory ()) thmdata
      val data as (_, facts) =
        case cached_context key of
            SOME (Prepared {thmdata, ...}) => thmdata
          | SOME (Lightweight data) => data
          | NONE =>
              let val data = without_hypotheses thmdata in
                context_cache := SOME (key, Lightweight data);
                data
              end
      val goal_features = Susp.delay (fn () => mlFeature.fea_of_goal true goal)
      val names = Susp.delay (fn () => map #1 facts)
      fun maximum (("knn", n), largest) = Int.max (n, largest)
        | maximum (_, largest) = largest
      val predict = shared_prefix (foldl maximum 0 filters)
        (knn_predict data (fn () => Susp.force goal_features))
      val fetch = knn_expander (dependency_resolver ())
      val expand =
        case List.filter (fn (filter, _) => filter = "knn") filters of
            _ :: _ :: _ => memoize String.compare fetch
          | _ => fetch
      fun one ("knn", n) = ("knn", expand_knn expand n (predict n))
        | one (filter, _) = (filter, Susp.force names)
    in
      map one filters
    end
  else
    let
      val rank_one =
        rank_for_filters
          (create_deferred_context_for (Theory.current_theory ()) thmdata)
          {pool = NONE, goal = goal} filters
    in
      map (fn (query as (filter, _)) => (filter, rank_one query)) filters
    end

end
