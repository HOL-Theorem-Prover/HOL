(*
load "ringLib";
load "numeralTheory";
load "bossLib";
*)
open HolKernel Parse boolLib bossLib
     arithmeticTheory semi_ringTheory;


val _ = new_theory "numRing";

(* num is a semi-ring: *)
val num_semi_ring = store_thm
    ("num_semi_ring",
     --` is_semi_ring (semi_ring 0 1 $+ $* : num semi_ring) `--,
RW_TAC arith_ss [ is_semi_ring_def, semi_ring_accessors,
		  RIGHT_ADD_DISTRIB, MULT_ASSOC ] THEN
MATCH_ACCEPT_TAC MULT_SYM);


val num_ring_thms =
  ringLib.store_ring { Name = "num", Theory = num_semi_ring };


local open numeralTheory in
val num_rewrites = save_thm("num_rewrites", LIST_CONJ
  [ numeral_distrib, numeral_eq, numeral_suc, numeral_iisuc,
    numeral_add, numeral_mult, iDUB_removal,
    ISPEC ``arithmetic$ZERO`` REFL_CLAUSE, ISPEC ``num$0`` REFL_CLAUSE ]);
end;


(* Hack to avoid (semi_ring 0 1 $+ $* ) to be confused with an end
 * of comment.                      ^^^
 *)
val _ = temp_overload_on("mult",--`$* : num->num->num`--);

val _ = export_theory();

