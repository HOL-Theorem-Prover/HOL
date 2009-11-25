signature quantHeuristicsArgsLib =
sig

  (* stateful ones, copied from quantHeuristicsLib *)
  val stateful_qp        : quantHeuristicsLib.quant_param;
  val pure_stateful_qp   : quantHeuristicsLib.quant_param;
  val TypeBase_qp        : quantHeuristicsLib.quant_param


  (* ones for specific types *)

  (*pair type*)
  val split_pair___PABS___pred    : Abbrev.term -> Abbrev.term -> Abbrev.term option
  val split_pair___FST_SND___pred : bool -> Abbrev.term -> Abbrev.term -> Abbrev.term option
  val split_pair___ALL___pred     : Abbrev.term -> Abbrev.term -> Abbrev.term option

  val pair_qp           : (Abbrev.term -> Abbrev.term -> Abbrev.term option) list ->
                           quantHeuristicsLib.quant_param;
  val pair_default_qp   : quantHeuristicsLib.quant_param;

  (*record type*)
  val record_qp         : bool -> (Abbrev.term -> Abbrev.term -> bool) ->
                          quantHeuristicsLib.quant_param;
  val record_default_qp : quantHeuristicsLib.quant_param;

  (*other types*)
  val num_qp            : quantHeuristicsLib.quant_param;
  val option_qp         : quantHeuristicsLib.quant_param;
  val list_qp           : quantHeuristicsLib.quant_param;


  (* combination of all except the stateful ones *)
  val std_qp  : quantHeuristicsLib.quant_param;

end
