(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Proof reconstruction for Z3: SML type of Z3 proofs *)

structure Z3_Proof =
struct

  (* A single Z3 inference step is represented as a value of type 'proofterm'.
     This datatype has one constructor for each inference rule of Z3.  Premises
     of the inference step are given by integer IDs (rather than proofterms) to
     allow encoding of a proof as a graph (cf. type 'proof' below).  The
     inference step's conclusion is given as a term.  Additionally, there is a
     'THEOREM' constructor, which encapsulates the theorem that is obtained
     from replaying the inference step in HOL. *)

  (* Rules marked with "1" are only used in compressed Z3 proofs
     (PROOF_MODE=1).  Other rules that are commented out are just not used in
     any of the benchmarks/proofs I've tried so far. *)

  datatype proofterm = AND_ELIM of int * Term.term
                  (* | APPLY_DEF of int * Term.term *)
                     | ASSERTED of Term.term
               (* 1: | CNF_STAR of ... *)
                     | COMMUTATIVITY of Term.term
                     | DEF_AXIOM of Term.term
                  (* | DEF_INTRO of Term.term *)
                  (* | DER of Term.term *)
                  (* | DISTRIBUTIVITY of Term.term *)
                     | ELIM_UNUSED of Term.term
                  (* | GOAL of Term.term *)
                     | HYPOTHESIS of Term.term
                     | IFF_FALSE of int * Term.term
                  (* | IFF_TILDE of int * Term.term *)
                     | IFF_TRUE of int * Term.term
                     | LEMMA of int * Term.term
                     | MONOTONICITY of int list * Term.term
                     | MP of int * int * Term.term
                     | MP_TILDE of int * int * Term.term
                     | NNF_NEG of int list * Term.term
                     | NNF_POS of int list * Term.term
               (* 1: | NNF_STAR of int list * Term.term *)
                     | NOT_OR_ELIM of int * Term.term
                     | PULL_QUANT of Term.term
               (* 1: | PULL_QUANT_STAR of Term.term *)
                  (* | PUSH_QUANT of ... *)
                     | QUANT_INST of Term.term
                     | QUANT_INTRO of int * Term.term
                     | REFL of Term.term
                     | REWRITE of Term.term
                     | REWRITE_STAR of int list * Term.term
                     | SK of Term.term
                     | SYMM of int * Term.term
                     | TH_LEMMA of int list * Term.term
                     | TRANS of int * int * Term.term
               (* 1: | TRANS_STAR of int list * Term.term *)
                     | TRUE_AXIOM of Term.term
                     | UNIT_RESOLUTION of int list * Term.term
                     | THEOREM of Thm.thm

  (* The Z3 proof is a directed acyclic graph of inference steps.  A unique
     integer ID is assigned to each inference step.  Note that Z3 assigns no ID
     to the proof's root node, which derives the final theorem "... |- F".  We
     will use ID 0 for the root node. *)

  type proof = (int, proofterm) Redblackmap.dict

end
