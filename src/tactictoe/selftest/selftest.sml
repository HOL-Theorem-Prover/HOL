open HolKernel boolLib tacticToe tttEval;

val _ = new_theory "scratch"

val _ = tttUnfold.ttt_record_thy "ConseqConv";

open metisTools ConseqConvTheory;

val _ = ttt ([],T);
