open HolKernel boolLib tacticToe tttEval;

val _ = tttUnfold.ttt_record_thy "ConseqConv";

val _ = tttUnfold.ttt_record_incremental_opts
  [tttUnfold.Scope (tttUnfold.Theories ["ConseqConv"]),
   tttUnfold.DryRun true];

open metisTools ConseqConvTheory;

val _ = ttt ([],T);
