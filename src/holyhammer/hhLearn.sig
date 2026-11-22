signature hhLearn =
sig
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

  val default_constants : constants

  type idf_table
  val create_idf_table :
    (mlThmData.thmid * mlFeature.fea) list -> idf_table
  val idf_nfacts : idf_table -> int
  val document_frequency : idf_table -> int -> int option
  val idf_of : idf_table -> int -> real option

  type dep_table
  (* Explicit dependency lists are assumed complete. *)
  val dep_table_of : (mlThmData.thmid * mlThmData.thmid list) list ->
    dep_table
  val build_dep_table :
    (mlThmData.thmid -> mlThmData.thmid list) ->
    (mlThmData.thmid * mlFeature.fea) list -> dep_table
  val create_dep_table : mlThmData.thmdata -> dep_table
  (* Ranking sees fetchable names; the table also retains proof completeness
     and the original dependency count for NB training. *)
  val dependencies_of : dep_table -> mlThmData.thmid ->
    mlThmData.thmid list option

  val pure_logic_concl : Term.term -> bool

  type fact_info =
    {thmid : mlThmData.thmid,
     features : mlFeature.fea,
     def : bool,
     concl : Term.term option}

  type nb_model
  type score_parts =
    {prior : real,
     positive : real,
     absent : real,
     negative : real,
     total : real}

  val train_nb :
    constants -> idf_table -> dep_table -> fact_info list -> nb_model
  val train_nb_from_thmdata :
    constants -> idf_table -> dep_table -> hhStature.statures ->
    mlThmData.thmdata -> nb_model
  val nb_tfreq : nb_model -> mlThmData.thmid -> int option
  val nb_sfreq : nb_model -> mlThmData.thmid -> int -> int option

  (* Goal-feature weights multiply the positive and absent-feature terms.
     Features unknown to the model are discarded before scoring. *)
  val nb_score_parts :
    nb_model -> (int * real) list -> mlThmData.thmid ->
    score_parts option
  val nb_scores :
    nb_model -> {pool : mlThmData.thmid list,
                 goal_features : (int * real) list} ->
    (mlThmData.thmid * real) list
  val nb_rank :
    nb_model -> {pool : mlThmData.thmid list,
                 goal_features : (int * real) list,
                 n : int} -> mlThmData.thmid list

  type scored_facts = (mlThmData.thmid * real) list
  type mesh_channel = real * (scored_facts * mlThmData.thmid list)

  val steep_weight : int -> real
  val smooth_weight : int -> real
  val weight_facts_steeply : mlThmData.thmid list -> scored_facts
  val weight_facts_smoothly : mlThmData.thmid list -> scored_facts

  (* Each channel is (global weight, (ranked facts, unknown facts)).  The
     key maps facts stating the same proposition to one representative;
     mesh_facts uses the identity. *)
  val mesh_facts_by :
    (mlThmData.thmid -> mlThmData.thmid) -> int ->
    mesh_channel list -> mlThmData.thmid list
  val mesh_facts : int -> mesh_channel list -> mlThmData.thmid list
  val merge_mash_channels :
    {max_facts : int, suggestions : mlThmData.thmid list,
     facts : mlThmData.thmid list, chained : mlThmData.thmid list,
     unknown : mlThmData.thmid list} ->
    mlThmData.thmid list * mlThmData.thmid list

  val over_request : int -> int
  val exclude_and_take : (mlThmData.thmid -> bool) -> int ->
    mlThmData.thmid list -> mlThmData.thmid list

  type context
  type mash_result =
    {ranking : mlThmData.thmid list,
     unknown : mlThmData.thmid list,
     learner : mlThmData.thmid list,
     max_suggestions : int}
  val clean_context_cache : unit -> unit
  val target_thmdata_cache_size : unit -> int
  val target_thmdata_cache_builds : unit -> int
  (* The explicit constructor supports a lagging persistent model and is also
     useful for checking partial-model behavior hermetically. *)
  val make_context :
    {thmdata : mlThmData.thmdata,
     model_thmdata : mlThmData.thmdata,
     dependencies : dep_table} -> context
  val create_context_for : string -> mlThmData.thmdata -> context
  val create_thmdata_for : string -> mlThmData.thmdata
  val create_context : mlThmData.thmdata -> context
  val context_thmids : context -> mlThmData.thmid list
  val mash_details : context ->
    {pool : mlThmData.thmid list option, goal : Abbrev.goal,
     max_facts : int} -> mash_result
  val rank_knn : mlThmData.thmdata -> int -> Abbrev.goal ->
    mlThmData.thmid list
  (* The lookup reuses dependency indices for a fixed loaded corpus. *)
  val make_dependency_lookup : unit ->
    {intact : Thm.thm -> bool * mlThmData.thmid list,
     knn : mlThmData.thmdata -> int -> Abbrev.goal -> mlThmData.thmid list}
  val rank : context ->
    {filter : string, pool : mlThmData.thmid list option,
     goal : Abbrev.goal, n : int} -> mlThmData.thmid list
  (* The list gives the expected (filter, depth) queries for one goal and pool.
     It bounds the reusable prediction prefixes. The returned function can
     also answer queries beyond those depths. *)
  val rank_for_filters : context ->
    {pool : mlThmData.thmid list option, goal : Abbrev.goal} ->
    (string * int) list -> (string * int -> mlThmData.thmid list)
  val rank_filters : mlThmData.thmdata -> Abbrev.goal ->
    (string * int) list -> (string * mlThmData.thmid list) list
end
