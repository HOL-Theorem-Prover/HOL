open HolKernel Parse boolLib bossLib;

open kraft_ineqTheory
open recSetsTheory

val _ = new_theory "pfree_enumerable";

val pfree_idx_def = Define‘
  pfree_idx i = prefix_free { bl | ∃y. Phi i (bl2n bl) = SOME y}
’;

(* prefix-free enumerator given index j and argument x
     dovetail over lists of increasing size.
   If a termination is found on a strict prefix of x then loop.
   If termination is found on x, return that.
   If a termination is found on shorter or equal length string, keep going.
   If termination on longer string, loop.
*)

(*
Theorem pfree_re:
  re { i | pfree_idx i}
Proof
  simp[re_def,pfree_idx_def] >>
  qexists_tac ‘
    dBnum (fromTerm (LAM "j" (* machine number *)

*)

val _ = export_theory();
