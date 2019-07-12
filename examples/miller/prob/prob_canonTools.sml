(* ------------------------------------------------------------------------- *)
(* A simpset for the canonicalisation procedure.                             *)
(* ------------------------------------------------------------------------- *)

structure prob_canonTools :> prob_canonTools =
struct

open Drule bossLib rich_listTheory prob_canonTheory;

fun fnm thy s = (SOME s, DB.fetch thy s)

val prob_canon_ss = simpLib.++(list_ss, simpLib.SSFRAG {
  ac = [],
  convs = [],
  dprocs = [],
  filter = NONE,
  name = NONE,
  rewrs = map (fnm "prob_canon") [
           "prob_canon_def", "prob_canon1_def", "prob_canon2_def",
           "prob_canon_prefs_def", "prob_canon_find_def",
           "prob_canon_merge_def",
           "prob_order_def", "PROB_TWIN_NIL",
           "PROB_TWIN_SING",
           "PROB_TWIN_CONS"
          ] @ [
            (SOME "IS_PREFIX", IS_PREFIX), (SOME "BUTLAST_CONS", BUTLAST_CONS),
            (SOME "FOLDR", FOLDR)
          ],
  congs = []});

end;
