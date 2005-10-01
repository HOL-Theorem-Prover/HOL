(* interactive use:
  load "fcpLib";
*)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "machine_words";

(* ------------------------------------------------------------------------- *)

val sizes = [2, 3, 4, 5, 6, 7, 8, 12, 16, 20, 24, 28, 32, 64];

fun mk_word_type n =
  let val _ = fcpLib.mk_index_type n
      val sn = Int.toString n
      val TYPE = mk_type("cart", [bool, mk_type("i"^sn, [])])
  in
    type_abbrev("word"^sn, TYPE)
  end;

val _ = List.app mk_word_type sizes;

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
