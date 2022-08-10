(* ------------------------------------------------------------------------- *)
(* A conversion to evaluate the Miller-Rabin test.                           *)
(* ------------------------------------------------------------------------- *)

(*
loadPath := "../prob" :: (!loadPath);
app load ["prob_pseudoTheory", "miller_rabin_mlTheory"];
*)

(*
*)
structure miller_rabinTools :> miller_rabinTools =
struct

open HolKernel Parse boolLib bossLib computeLib combinTheory prob_pseudoTheory
     miller_rabin_mlTheory miller_rabinTheory hurdUtils reduceLib;

local
  val compset = num_compset ();
  val _ = add_thms [BIND_ML, FACTOR_TWOS_ML, LOG2_ML, MANY_ML,
                    MILLER_RABIN_1_ML, MILLER_RABIN_ML, MODEXP_ML,
                    PROB_UNIFORM_CUT_ML, PROB_UNIF_ML, UNCURRY_ML,
                    UNIT_ML, WITNESS_ML, WITNESS_TAIL_ML, o_THM,
                    SHD_PROB_PSEUDO, STL_PROB_PSEUDO] compset;
in
  val EVAL = CBV_CONV compset;
end;

fun COMPOSITE_PROVER n =
  TRYR (MATCH_MP MILLER_RABIN_DEDUCE_COMPOSITE)
  (EVAL (Term`miller_rabin ^n 50 (prob_pseudo 103 95 75 0)`));

(*
These tests

Count.apply COMPOSITE_PROVER ``91 : num``;
Count.apply COMPOSITE_PROVER ``123 : num``;
EVAL ``2 EXP (2 EXP 5) + 1``;
Count.apply COMPOSITE_PROVER ``2 EXP (2 EXP 5) + 1``;
EVAL ``2 EXP (2 EXP 6) + 1``;
Count.apply COMPOSITE_PROVER ``2 EXP (2 EXP 6) + 1``;
EVAL ``2 EXP (2 EXP 7) + 1``;
Count.apply COMPOSITE_PROVER ``2 EXP (2 EXP 7) + 1``;
EVAL ``2 EXP (2 EXP 8) + 1``;
Count.apply COMPOSITE_PROVER ``2 EXP (2 EXP 8) + 1``;

produce the following results (on darek):

- runtime: 1.740s,    gctime: 0.150s,     systime: 0.000s.
Axioms asserted: 0.
Definitions made: 0.
Oracle invocations: 0.
Theorems loaded from disk: 0.
HOL primitive inference steps: 41349.
Total: 41349.
> val it = |- ~prime 91 : thm

- - - runtime: 2.010s,    gctime: 0.160s,     systime: 0.000s.
Axioms asserted: 0.
Definitions made: 0.
Oracle invocations: 0.
Theorems loaded from disk: 0.
HOL primitive inference steps: 47767.
Total: 47767.
> val it = |- ~prime 123 : thm

- - > val it = |- 2 EXP 2 EXP 5 + 1 = 4294967297 : thm
- - - runtime: 53.080s,    gctime: 7.170s,     systime: 0.970s.
Axioms asserted: 0.
Definitions made: 0.
Oracle invocations: 0.
Theorems loaded from disk: 0.
HOL primitive inference steps: 1246368.
Total: 1246368.
> val it = |- ~prime (2 EXP 2 EXP 5 + 1) : thm

- - - - > val it = |- 2 EXP 2 EXP 6 + 1 = 18446744073709551617 : thm
- runtime: 370.210s,    gctime: 53.530s,     systime: 0.680s.
Axioms asserted: 0.
Definitions made: 0.
Oracle invocations: 0.
Theorems loaded from disk: 0.
HOL primitive inference steps: 8652867.
Total: 8652867.
> val it = |- ~prime (2 EXP 2 EXP 6 + 1) : thm

- > val it = |- 2 EXP 2 EXP 7 + 1 = 340282366920938463463374607431768211457 : thm
- runtime: 2842.920s,    gctime: 409.620s,     systime: 12.210s.
Axioms asserted: 0.
Definitions made: 0.
Oracle invocations: 0.
Theorems loaded from disk: 0.
HOL primitive inference steps: 65736911.
Total: 65736911.
> val it = |- ~prime (2 EXP 2 EXP 7 + 1) : thm

- - > val it =
    |- 2 EXP 2 EXP 8 + 1 =
       115792089237316195423570985008687907853269984665640564039457584007913129639937
     : thm
- - - runtime: 22095.770s,    gctime: 3170.780s,     systime: 12.570s.
Axioms asserted: 0.
Definitions made: 0.
Oracle invocations: 0.
Theorems loaded from disk: 0.
HOL primitive inference steps: 514934092.
Total: 514934092.
> val it = |- ~prime (2 EXP 2 EXP 8 + 1) : thm

*)

end;
