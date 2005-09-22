(* interactive use:
  load "wordsLib";
*)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "machine_words";

(* ------------------------------------------------------------------------- *)

val sizes = [4, 8, 16, 32, 64];

fun mk_type n =
  let val _ = wordsLib.mk_index_type n
      val sn = Int.toString n
      val TYPE = Type.mk_type("cart", [bool, Type.mk_type("i"^sn, [])])
  in
    type_abbrev("word"^sn, TYPE)
  end;

val _ = List.app mk_type sizes;

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
