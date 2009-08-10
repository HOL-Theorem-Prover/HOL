signature quantHeuristicsArgsLib =
sig

  (* stateful ones, copied from quantHeuristicsLib *)
  val stateful_qhca        : quantHeuristicsLib.quant_heuristic_combine_argument;
  val pure_stateful_qhca   : quantHeuristicsLib.quant_heuristic_combine_argument;
  val TypeBase_qhca        : quantHeuristicsLib.quant_heuristic_combine_argument


  (* ones for specific types *)
  val pair_qhca    : quantHeuristicsLib.quant_heuristic_combine_argument;
  val num_qhca     : quantHeuristicsLib.quant_heuristic_combine_argument;
  val option_qhca  : quantHeuristicsLib.quant_heuristic_combine_argument;
  val list_qhca    : quantHeuristicsLib.quant_heuristic_combine_argument;


  (* combination of all except the stateful ones *)
  val std_qhca  : quantHeuristicsLib.quant_heuristic_combine_argument;

end
