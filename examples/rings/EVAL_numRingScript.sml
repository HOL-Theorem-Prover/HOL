(*
load "ringLib";
load "numeralTheory";
load "bossLib";
*)
Theory EVAL_numRing
Ancestors
  arithmetic EVAL_semiring

(* num is a semi-ring: *)
Theorem num_semi_ring:
       is_semi_ring (semi_ring 0 1 $+ $* : num semi_ring)
Proof
RW_TAC arith_ss [ is_semi_ring_def, semi_ring_accessors,
                  RIGHT_ADD_DISTRIB, MULT_ASSOC ] THEN
MATCH_ACCEPT_TAC MULT_SYM
QED


val num_ring_thms =
  EVAL_ringLib.store_ring { Name = "num", Theory = num_semi_ring };


local open numeralTheory in
val num_rewrites = save_thm("num_rewrites", LIST_CONJ
  [ numeral_distrib, numeral_eq, numeral_suc, numeral_iisuc,
    numeral_add, numeral_mult, iDUB_removal,
    ISPEC ``arithmetic$ZERO`` REFL_CLAUSE, ISPEC ``num$0`` REFL_CLAUSE ]);
end;


