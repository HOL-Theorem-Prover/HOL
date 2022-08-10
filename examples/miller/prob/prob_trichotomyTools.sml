(* ------------------------------------------------------------------------- *)
(* A conversion to evaluate trichotomy.                                      *)
(* ------------------------------------------------------------------------- *)

structure prob_trichotomyTools :> prob_trichotomyTools =
struct

open HolKernel Parse boolLib reduceLib computeLib pairSyntax combinTheory
     pairTheory sequenceTheory prob_trichotomyTheory state_transformerTheory
     prob_pseudoTheory;

infix 1 THENC
infix 0 ORELSEC;

local
  val compset = num_compset ();
  val _ = add_thms [PROB_TRICHOTOMY_COMPUTE, BIND_DEF, o_THM, sdest_def,
                    UNCURRY_DEF, SHD_PROB_PSEUDO, STL_PROB_PSEUDO,
                    UNIT_DEF] compset;
in
  val PROB_TRICHOTOMY_CONV = CBV_CONV compset;
end;

fun chain f seq 0 = []
  | chain f seq n =
  let
    val th = PROB_TRICHOTOMY_CONV (mk_comb (f, seq))
    val (_, seq) = (dest_pair o snd o dest_eq o concl) th
  in
    th :: chain f seq (n - 1)
  end;

(*
PROB_TRICHOTOMY_CONV ``prob_trichotomy (prob_pseudo 103 95 75 0)``;

Count.apply (chain ``prob_trichotomy`` ``prob_pseudo 103 95 75 0``) 10;

runtime: 2.050s,    gctime: 0.150s,     systime: 0.000s.
Axioms asserted: 0.
Definitions made: 0.
Oracle invocations: 0.
Theorems loaded from disk: 0.
HOL primitive inference steps: 52505.
Total: 52505.
> val it =
    [|- prob_trichotomy (prob_pseudo 103 95 75 0) =
        ((T,F),prob_pseudo 103 95 75 65),

     |- prob_trichotomy (prob_pseudo 103 95 75 65) =
        ((F,T),prob_pseudo 103 95 75 33),

     |- prob_trichotomy (prob_pseudo 103 95 75 33) =
        ((T,F),prob_pseudo 103 95 75 94),

     |- prob_trichotomy (prob_pseudo 103 95 75 94) =
        ((T,F),prob_pseudo 103 95 75 107),

     |- prob_trichotomy (prob_pseudo 103 95 75 107) =
        ((T,T),prob_pseudo 103 95 75 2),

     |- prob_trichotomy (prob_pseudo 103 95 75 2) =
        ((T,T),prob_pseudo 103 95 75 143),

     |- prob_trichotomy (prob_pseudo 103 95 75 143) =
        ((F,T),prob_pseudo 103 95 75 55),

     |- prob_trichotomy (prob_pseudo 103 95 75 55) =
        ((F,T),prob_pseudo 103 95 75 96),

     |- prob_trichotomy (prob_pseudo 103 95 75 96) =
        ((T,F),prob_pseudo 103 95 75 34),

     |- prob_trichotomy (prob_pseudo 103 95 75 34) =
        ((T,T),prob_pseudo 103 95 75 32)] : thm list
*)

end;
