open HolKernel Parse boolLib bossLib;

open kraft_ineqTheory

val _ = new_theory "pfree_enumerable";

val pfree_idx_def = Define‘
  pfree_idx i = prefix_free { bl | ∃y. Phi i (bl2n bl) = SOME y}
’;


val _ = export_theory();
