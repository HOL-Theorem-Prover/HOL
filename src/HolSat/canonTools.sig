(* ========================================================================= *)
(* HOL NORMALIZATION FUNCTIONS.                                              *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

signature canonTools =
sig

  type term = Term.term
  type thm = Thm.thm
  type conv = Abbrev.conv
  type tactic = Abbrev.tactic

  (* Conversion to combinators {S,K,I} *)
  val SKI_CONV : conv

  (* Simplifies away applications of the logical connectives to T or F *)
  val SIMPLIFY_CONV : conv

  (* Negation normal form *)
  val NNF_CONV : conv

  (* Skolemization *)
  val SKOLEMIZE_CONV : conv

  (* A basic tautology prover and simplifier for clauses *)
  val TAUTOLOGY_CONV : conv
  val CONTRACT_CONV : conv

  (* Conjunctive normal form *)
  val tautology_checking : bool ref
  val CNF_CONV : conv

  (* Eliminating Hilbert's epsilon operator (but losing completeness). *)
  val SELECT_TAC : tactic

  (* Eliminating lambdas to make terms "as first-order as possible" *)
  val DELAMB_CONV : conv

  (* ------------------------------------------------------------------ *)
  (* This removes leading existential quantifiers from a theorem.       *)
  (* For example,                                                       *)
  (*   EXISTENTIAL_CONST_RULE   a   |- ?x. P x y z                      *)
  (*      -->   [a = @x. P x y z] |- P a y                              *)
  (*   EXISTENTIAL_CONST_RULE   a y z   |- ?x. P x y                    *)
  (*      -->   [a = \y z. @x. P x y z] |- P (a y z) y                  *)
  (* NEW_CONST_RULE creates a new variable as the argument to           *)
  (* EXISTENTIAL_CONST_RULE, and CLEANUP_CONSTS_RULE tries to eliminate *)
  (* as many of these new equality assumptions as possible.             *)
  (* ------------------------------------------------------------------ *)
  val EXISTENTIAL_CONST_RULE : term -> thm -> thm
  val NEW_CONST_RULE : thm -> thm
  val CLEANUP_CONSTS_RULE : thm -> thm

  (* Definitional negation normal form *)
  val DEF_NNF_CONV : conv

  (* Definitional conjunctive normal form *)
  val DEF_CNF_CONV : conv

end
