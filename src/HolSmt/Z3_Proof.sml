(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Proof reconstruction for Z3: SML type of Z3 proofs *)

structure Z3_Proof =
struct

  (* A single Z3 inference step is represented as a value of type
     'proofterm'.  This datatype has one constructor for each
     inference rule of Z3.  Premises of the inference step are given
     by proofterms.  However, to allow encoding of a proof as a graph
     (rather than a tree), there is an 'ID' constructor that merely
     takes an integer argument (which is an index into the 'proof'
     dictionary, cf. type 'proof' below).  The inference step's
     conclusion is given as a term.  Additionally, there is a
     'THEOREM' constructor that encapsulates the theorem that is
     obtained from replaying the inference step in HOL. *)

  (* At the time of writing (2010-09-08), the Z3 documentation
     unfortunately is outdated with respect to the inference rules
     that the most recent Z3 version (2.11) uses.  I have applied Z3
     to a large number of SMT-LIB benchmarks.  'proofterm' provides a
     constructor for each inference rule that appears (at least once)
     in the generated proofs.  Rules that only appear in compressed Z3
     proofs (PROOF_MODE=1) are NOT supported.

     To add another inference rule, one must 1. add a corresponding
     'proofterm' datatype constructor below; 2. modify
     Z3_ProofParser.sml so that the parser recognizes the new rule's
     concrete syntax; 3. modify Z3_ProofReplay.sml so that
     'check_proof' knows how to validate inferences performed by the
     new rule. *)

  datatype proofterm = AND_ELIM of proofterm * Term.term
                     | ASSERTED of Term.term
                     | COMMUTATIVITY of Term.term
                     | DEF_AXIOM of Term.term
                     | ELIM_UNUSED of Term.term
                     | HYPOTHESIS of Term.term
                     | IFF_TRUE of proofterm * Term.term
                     | LEMMA of proofterm * Term.term
                     | MONOTONICITY of proofterm list * Term.term
                     | MP of proofterm * proofterm * Term.term
                     | NOT_OR_ELIM of proofterm * Term.term
                     | QUANT_INTRO of proofterm * Term.term
                     | REWRITE of Term.term
                     | SYMM of proofterm * Term.term
                     | TH_LEMMA_ARITH of proofterm list * Term.term
                     | TH_LEMMA_ARRAY of proofterm list * Term.term
                     | TH_LEMMA_BASIC of proofterm list * Term.term
                     | TH_LEMMA_BV of proofterm list * Term.term
                     | TRANS of proofterm * proofterm * Term.term
                     | TRUE_AXIOM of Term.term
                     | UNIT_RESOLUTION of proofterm list * Term.term
                     | ID of int
                     | THEOREM of Thm.thm

  (* The Z3 proof is a directed acyclic graph of inference steps.  A
     unique integer ID is assigned to each inference step.  Note that
     Z3 assigns no ID to the proof's root node, which derives the
     final theorem "... |- F".  We will use ID 0 for the root node. *)

  type proof = (int, proofterm) Redblackmap.dict

end
