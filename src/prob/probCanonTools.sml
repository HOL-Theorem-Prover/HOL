(* ------------------------------------------------------------------------- *)
(* A simpset for the canonicalisation procedure.                             *)
(* ------------------------------------------------------------------------- *)

structure probCanonTools :> probCanonTools =
struct

open Drule bossLib rich_listTheory probCanonTheory;

val prob_canon_ss = simpLib.++(list_ss, simpLib.SIMPSET {
  ac = [],
  convs = [],
  dprocs = [],
  filter = NONE,
  rewrs = [alg_canon_def, alg_canon1_def, alg_canon2_def,
	   alg_canon_prefs_def, alg_canon_find_def, alg_canon_merge_def,
	   alg_order_def, IS_PREFIX, FOLDR, ALG_TWIN_NIL, ALG_TWIN_SING,
           ALG_TWIN_CONS, BUTLAST_CONS],
  congs = []});

end;
