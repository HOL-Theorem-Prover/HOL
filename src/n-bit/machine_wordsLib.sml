structure machine_wordsLib :> machine_wordsLib =
struct

(* iinteractive use:
  load "wordsLib";
*)

open HolKernel Parse boolLib bossLib;
open computeLib;
open wordsLib;

(* ------------------------------------------------------------------------- *)

val sizes = [4, 8, 16, 32, 64];

fun word_thms n =
  let val _ = mk_index_type n
      val sn = Int.toString n
      val TYPE = mk_type("cart", [bool, mk_type("i"^sn, [])])
      val _ = type_abbrev("word"^sn, TYPE)
  in
    [theorem ("finite_"^sn), theorem ("dimindex_"^sn)]
  end;

val thms = List.concat (List.map word_thms sizes);

fun machine_words_compset () =
  let val compset = words_compset()
      val _ = add_thms thms compset
      val _ = add_thms thms computeLib.the_compset
in
  compset
end;

val WORD_CONV = CBV_CONV (machine_words_compset());

end
