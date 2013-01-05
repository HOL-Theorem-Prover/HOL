signature quantHeuristicsLibParameters =
sig
  include Abbrev

  (* stateful ones *)
  val stateful_qp        : unit -> quantHeuristicsLibBase.quant_param;
  val pure_stateful_qp   : unit -> quantHeuristicsLibBase.quant_param;
  val TypeBase_qp        : quantHeuristicsLibBase.quant_param;

  val clear_stateful_qp : unit -> unit;
  val stateful_qp___add_combine_arguments :
     quantHeuristicsLibBase.quant_param list -> unit;

  (* ones for specific types *)

  (*pair type*)
  val split_pair___PABS___pred    : term -> term -> term option
  val split_pair___FST_SND___pred : bool -> term -> term -> Abbrev.term option
  val split_pair___ALL___pred     : term -> term -> term option

  val pair_qp           : (term -> term -> term option) list ->
                           quantHeuristicsLibBase.quant_param;
  val pair_default_qp   : quantHeuristicsLibBase.quant_param;

  (*record type*)
  val record_qp         : bool -> (term -> term -> bool) ->
                          quantHeuristicsLibBase.quant_param;
  val record_default_qp : quantHeuristicsLibBase.quant_param;

  (*other types*)
  val num_qp            : quantHeuristicsLibBase.quant_param;
  val option_qp         : quantHeuristicsLibBase.quant_param;
  val list_qp           : quantHeuristicsLibBase.quant_param;
  val list_no_len_qp    : quantHeuristicsLibBase.quant_param; (* do not use LENGTH to unroll lists *)
  val list_len_qp       : quantHeuristicsLibBase.quant_param; (* use LENGTH for number > 1 to unroll lists *)
  val sum_qp            : quantHeuristicsLibBase.quant_param;

  (* filters for type matching *)
  val sum_ty_filter    : term -> term -> bool
  val option_ty_filter : term -> term -> bool
  val pair_ty_filter   : term -> term -> bool
  val num_ty_filter    : term -> term -> bool
  val list_ty_filter   : term -> term -> bool


  (* combination of all except the stateful ones *)
  val std_qp  : quantHeuristicsLibBase.quant_param;

  (* A heuristic that considers just the conclusion of implications. This may lead to wrong guesses, but
     if used carefully, is a handy heuristic. *)
  val implication_concl_qp : quantHeuristicsLibBase.quant_param;

  (* A heuristic that looks at both sides of a conjunction independently
     and just lifts the results. This may lead to wrong guesses, but
     if used carefully, may be a handy heuristic. *)
  val conj_lift_qp : quantHeuristicsLibBase.quant_param;

end
