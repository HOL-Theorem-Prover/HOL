signature rlLib =
sig

  include Abbrev

  type pos = int list

  (* variables *)
  val numtag_var : term
  val numhole_var : term
  val active_var : term
  val pending_var : term
  val extra_operl : (term * int) list

  (* position *)
  val sub_at_pos : term -> pos * term -> term
  val subtm_at_pos : pos -> term -> term
  val recover_cut : term -> pos * term -> term
  val all_posred : term -> (pos * term) list
  val tag_position : term * pos -> term
  val hole_position : term * pos -> term
  val match_subtm : term -> (term * term) -> term

  (* arithmetic *)
  val mk_suc : term -> term
  val mk_sucn : int -> term
  val mk_add : term * term -> term
  val mk_mult : term * term -> term
  val zero : term
  val dest_suc : term -> term
  val dest_add : term -> (term * term)

  (* terms *)
  val human_readable : term -> term
  val fo_terms : term -> term list
  val operl_of_term : term -> (term * int) list
  val negate : term -> term
  val is_subtm : term -> term -> bool

  (* training *)
  val split_traintest :
    real -> (''a * 'b) list -> (''a * 'b) list * (''a * 'b) list
  val train_tnn_eval : int ->
    mlTreeNeuralNetwork.treenn -> (term * real) list * (term * real) list ->
    mlTreeNeuralNetwork.treenn
  val train_tnn_poli : int ->
    mlTreeNeuralNetwork.treenn ->
    (term * real list) list * (term * real list) list ->
    mlTreeNeuralNetwork.treenn

  type knninfo = (int, real) Redblackmap.dict * (term, int list) Redblackmap.dict
  val train_knn : (term * 'a) list -> (knninfo *  (term, 'a) Redblackmap.dict)
  val infer_knn : (knninfo *  (term, 'a) Redblackmap.dict) -> term -> 'a


end
