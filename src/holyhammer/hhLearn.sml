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

fun idf_entries ({weights, ...} : idf_table) = dlist weights

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

(* mlThmData.intactdep_of_thm on a theorem's raw dependency list, with
   each theory's depnumber index built once instead of rescanning the
   theory per dependency.  A theory with a theorem lacking a dependency
   number keeps the original scan, which raises exactly where it did. *)
fun intact_dependency_resolver () =
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
              if can (DB.fetch theory) name andalso
                 uptodate_thm (DB.fetch theory name)
              then SOME (theory ^ "Theory." ^ name)
              else NONE
          | NONE => NONE
      end
  in
    fn raw =>
      let val resolved = List.mapPartial thmid_of_depid raw in
        (length raw = length resolved, resolved)
      end
  end

fun create_dep_table (_, facts) =
  let
    val intact_dependencies_of = intact_dependency_resolver ()
    fun dependency_info thmid =
      case total mlThmData.thm_of_name thmid of
          SOME (SOME (_, theorem)) =>
            let val (theory, _) = split_string "Theory." thmid in
              if theory = mlThmData.namespace_tag then
                SOME (intact_dependencies [])
              else
                let
                  val raw = Dep.depidl_of (Tag.dep_of (Thm.tag theorem))
                  val (intact, fetchable) = intact_dependencies_of raw
                in
                  SOME {fetchable = fetchable, intact = intact,
                        count = length raw}
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

fun dependency_entries (table : dep_table) =
  map (fn (name, info) => (name, #fetchable info)) (dlist table)

fun pure_logic_concl conclusion =
  let
    fun pure_constant constant =
      let val {Thy, ...} = dest_thy_const constant in
        Thy = "min" orelse Thy = "bool"
      end
  in
    List.all pure_constant
      (mk_term_set (find_terms is_const conclusion))
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

fun add_weight amount key table =
  case Redblackmap.peek (table, key) of
      SOME count => dadd key (count + amount) table
    | NONE => dadd key amount table

fun train_nb constants idf dependencies facts =
  let
    val number = length facts
    val _ =
      if idf_nfacts idf = number then ()
      else raise ERR "train_nb" "IDF and fact-table sizes differ"
    fun require_feature feature =
      if Option.isSome (idf_of idf feature) then ()
      else raise ERR "train_nb" "fact feature is absent from IDF table"
    val _ = List.app
      (fn (fact : fact_info) => List.app require_feature (#features fact))
      facts
    val information = Vector.fromList facts
    val names = Vector.map #thmid information
    val pure_logic = Vector.map
      (fn (fact : fact_info) =>
        case #concl fact of
            SOME conclusion => pure_logic_concl conclusion
          | NONE => false)
      information
    val (_, indices) =
      foldl add_index (0, dempty String.compare) facts
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

fun train_nb_from_thmdata constants idf dependencies statures (_, facts) =
  let
    fun fact_info (thmid, features) : fact_info =
      {thmid = thmid, features = features,
       def = #def (hhStature.stature_of statures thmid),
       concl = conclusion_of thmid}
  in
    train_nb constants idf dependencies (map fact_info facts)
  end

fun nb_thmids ({names, ...} : nb_model) = Vector.foldr op:: [] names

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

fun nb_knows_feature ({idf, ...} : nb_model) feature =
  Option.isSome (idf_of idf feature)

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

fun mesh_facts_by _ max_facts [] = []
  | mesh_facts_by key max_facts [(_, (selected, unknown))] =
      distinct_by key
        (map #1 (take max_facts selected) @
         take (max_facts - Int.min (max_facts, length selected)) unknown)
  | mesh_facts_by key max_facts channels =
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
             key_set key unknown)
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

fun mesh_facts max_facts channels =
  mesh_facts_by I max_facts channels

fun intersection_in_order_by key right left =
  let val keys = key_set key right in
    filter (fn fact => Redblackset.member (keys, key fact)) left
  end

fun subtract_by key removed items =
  let val keys = key_set key removed in
    filter (fn fact => not (Redblackset.member (keys, key fact))) items
  end

fun merge_mash_channels_by key
      {max_facts, suggestions, facts, chained, unknown} =
  let
    val proximate = take (#max_proximity_facts default_constants) facts
    val unknown_chained = intersection_in_order_by key unknown chained
    val unknown_proximate = intersection_in_order_by key unknown proximate
    val used_unknown = unknown_chained @ unknown_proximate
    val channels =
      [(#chained_weight default_constants,
        (map (fn fact => (fact, #unit_weight default_constants))
          unknown_chained, [])),
       (#proximity_weight default_constants,
        (weight_facts_smoothly unknown_proximate, [])),
       (#learner_weight default_constants,
        (weight_facts_steeply suggestions, unknown))]
  in
    (mesh_facts_by key max_facts channels,
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
   idf : idf_table,
   model : nb_model,
   statures : hhStature.statures,
   mepo : hhMePo.context,
   dependencies : dep_table,
   fact_key : mlThmData.thmid -> mlThmData.thmid,
   pool_order : mlThmData.thmid list}

type cache_key = string * (mlThmData.thmid * mlFeature.fea) list
val context_cache = ref (NONE : (cache_key * context) option)

fun clean_context_cache () =
  (context_cache := NONE; clean_target_thmdata_cache ())

fun context_key_for current (_, facts) = (current, facts)

fun same_key ((left_current, left_facts),
              (right_current, right_facts)) =
  left_current = right_current andalso left_facts = right_facts

(* Facts whose conclusions are alpha-equivalent state the same
   proposition; each such class is represented by its first fact.  Other
   names, including those without a fetchable theorem, represent
   themselves. *)
fun proposition_key facts =
  let
    fun add ((thmid, _), (conclusions, representatives)) =
      case conclusion_of thmid of
          SOME conclusion =>
            (dadd thmid conclusion conclusions,
             if dmem conclusion representatives then representatives
             else dadd conclusion thmid representatives)
        | NONE => (conclusions, representatives)
    val (conclusions, representatives) =
      foldl add (dempty String.compare, dempty Term.compare) facts
  in
    fn thmid =>
      case Redblackmap.peek (conclusions, thmid) of
          SOME conclusion => dfind conclusion representatives
        | NONE => thmid
  end

fun make_context_for current
      {thmdata = thmdata as (_, facts),
       model_thmdata = model_thmdata as (_, model_facts),
       dependencies} =
  let
    val idf = create_idf_table model_facts
    val statures = hhStature.create_statures_for current
    val model = train_nb_from_thmdata default_constants idf dependencies
      statures model_thmdata
    val fact_key = proposition_key facts
  in
    {thmdata = thmdata, idf = idf, model = model,
     statures = statures,
     mepo = hhMePo.create_context_for current thmdata statures,
     dependencies = dependencies, fact_key = fact_key,
     pool_order = map #1 facts}
  end

fun make_context parameters =
  make_context_for (Theory.current_theory ()) parameters

(* Externally built thmdata (mlThmData.create_thmdata, as holyhammer and
   TacticToe pass it) may hold top-level theorems with hypotheses. *)
fun build_context_for current (weights, all_facts) =
  let
    val thmdata = (weights, filter (not o has_hypotheses o #1) all_facts)
  in
    make_context_for current
      {thmdata = thmdata, model_thmdata = thmdata,
       dependencies = create_dep_table thmdata}
  end

fun create_context_for current thmdata =
  let
    val key = context_key_for current thmdata
    fun rebuild () =
      let val context = build_context_for current thmdata in
        context_cache := SOME (key, context);
        context
      end
  in
    case !context_cache of
        SOME (cached_key, context) =>
          if same_key (key, cached_key) then context else rebuild ()
      | NONE => rebuild ()
  end

fun create_context thmdata =
  create_context_for (Theory.current_theory ()) thmdata

fun context_thmids ({pool_order, ...} : context) = pool_order

fun restrict_thmdata ({thmdata = (weights, facts), ...} : context) NONE =
      (weights, facts)
  | restrict_thmdata ({thmdata = (weights, facts), ...} : context)
      (SOME requested) =
      let val wanted = name_set requested in
        (weights, filter (member_set wanted o #1) facts)
      end

fun unknown_facts model facts =
  List.mapPartial
    (fn (thmid, _) =>
      if Option.isSome (model_index model thmid) then NONE else SOME thmid)
    facts

fun add_thmdep dependencies max_facts predictions =
  let
    fun with_dependencies prediction =
      prediction ::
        (case dependencies_of dependencies prediction of
             SOME names => names
           | NONE => [])
  in
    take max_facts
      (distinct (List.concat (map with_dependencies predictions)))
  end

type mash_result =
  {ranking : mlThmData.thmid list,
   unknown : mlThmData.thmid list,
   learner : mlThmData.thmid list,
   max_suggestions : int}

fun mash_leg ({model, dependencies, fact_key, ...} : context)
      restricted goal max_facts =
  if max_facts <= 0 then
    {ranking = [], unknown = [], learner = [], max_suggestions = 0}
  else
    let
      val (weights, facts) = restricted
      val pool = map #1 facts
      val features = mlFeature.fea_of_goal true goal
      val goal_features = map
        (fn feature => (feature, #unit_weight default_constants))
        features
      val max_suggestions =
        #max_suggestions_factor default_constants * max_facts +
        #max_suggestions_extra default_constants
      val nb = nb_rank model
        {pool = pool, goal_features = goal_features, n = max_suggestions}
      val knn = mlNearestNeighbor.thmknn (weights, facts) max_suggestions
        features
      val learner = mesh_facts max_suggestions
        [(#nb_mesh_weight default_constants,
          (weight_facts_steeply nb, [])),
         (#knn_mesh_weight default_constants,
          (weight_facts_steeply knn, []))]
      val (merged, remaining_unknown) = merge_mash_channels_by fact_key
        {max_facts = max_suggestions, suggestions = learner,
         facts = pool, chained = [], unknown = unknown_facts model facts}
    in
      {ranking = add_thmdep dependencies max_facts merged,
       unknown = remaining_unknown, learner = learner,
       max_suggestions = max_suggestions}
    end

fun mash_details context {pool, goal, max_facts} =
  mash_leg context (restrict_thmdata context pool) goal max_facts

fun is_induction statures thmid =
  #induction (hhStature.stature_of statures thmid)

fun rank (context as {statures, mepo, fact_key, ...} : context)
      {filter, pool, goal, n} =
  let
    val restricted as (_, facts) = restrict_thmdata context pool
    val pool_names = map #1 facts
    val generous = over_request n
    fun mepo_leg () =
      hhMePo.mepo_rank
        (case pool of
             NONE => mepo
           | SOME _ => hhMePo.restrict_context mepo pool_names)
        goal generous
    fun mash () = mash_leg context restricted goal generous
    fun finish ranking =
      exclude_and_take (is_induction statures) n ranking
  in
    case filter of
        "none" => pool_names
      | "knn" => mlNearestNeighbor.thmknn_wdep restricted n
          (mlFeature.fea_of_goal true goal)
      | "mepo" => finish (mepo_leg ())
      | "mash" => finish (#ranking (mash ()))
      | "mesh" =>
          let
            (* Each component is a complete standalone leg before MeSh sees
               it: over-request, exclude induction facts, and refill to the
               caller's bound.  Meshing the raw over-requested lists and
               excluding only afterwards changes both normalization and the
               candidate cutoff. *)
            val mepo_ranking = finish (mepo_leg ())
            val mash_result = mash ()
            val mash_ranking = finish (#ranking mash_result)
            val unknown = #unknown mash_result
          in
            mesh_facts_by fact_key n
              [(#final_mepo_weight default_constants,
                (weight_facts_steeply mepo_ranking, [])),
               (#final_mash_weight default_constants,
                (weight_facts_steeply mash_ranking, unknown))]
          end
      | _ => raise ERR "rank" ("unknown premise filter " ^ filter)
  end

end
