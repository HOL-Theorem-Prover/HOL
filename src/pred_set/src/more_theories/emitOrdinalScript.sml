open HolKernel Parse boolLib bossLib;

open ordinalNotationTheory basis_emitTheory EmitML

val _ = new_theory "emitOrdinal";

(*---------------------------------------------------------------------------*)
(* Generate an ML file for the executable functions of the theory.           *)
(*---------------------------------------------------------------------------*)

Triviality tail_End:
  tail (End n) = FAIL tail ^(mk_var("(End n)",bool)) (End n)
Proof
  REWRITE_TAC [combinTheory.FAIL_THM]
QED

val _ =
 emitML ""    (* Write to current directory, not !Globals.emitMLDir *)
    ("ordinal",
     [MLSIG "type num = numML.num",
      OPEN ["num"],
      DATATYPE `osyntax = End num | Plus osyntax num osyntax`,
      DEFN expt_def,
      DEFN coeff_def,
      DEFN finp_def,
      DEFN (CONJ tail_End tail_def),
      DEFN rank_def,
      DEFN oless_equations,
      DEFN is_ord_equations,
      DEFN ord_less_def,
      DEFN ord_add_def,
      DEFN ord_sub_def,
      DEFN ord_mult_def]);



val _ = export_theory();
