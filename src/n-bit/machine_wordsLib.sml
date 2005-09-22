structure machine_wordsLib :> machine_wordsLib =
struct

(* interactive use:
  load "machine_wordsTheory";
*)

open HolKernel Parse boolLib bossLib;
open computeLib;
open machine_wordsTheory;

(* ------------------------------------------------------------------------- *)

fun machine_words_compset () =
  let val thms = map snd (theorems "machine_words")
      val compset = wordsLib.words_compset()
      val _ = add_thms thms compset
      val _ = add_thms thms computeLib.the_compset
in
  compset
end;

val WORD_CONV = CBV_CONV (machine_words_compset());

end
