(* =====================================================================
 * FILE : $Id$
 *
 * ===================================================================== *)


structure Ho_theorems :> Ho_theorems =
struct

open Ho_boolTheory HolKernel basicHol90Lib
open Ho_rewrite

(* ------------------------------------------------------------------------- *)
(* Universal quantifier and conjunction.                                     *)
(* ------------------------------------------------------------------------- *)

val FORALL_AND_THM       = boolTheory.FORALL_AND_THM;
val AND_FORALL_THM       = GSYM FORALL_AND_THM;
val LEFT_AND_FORALL_THM  = boolTheory.LEFT_AND_FORALL_THM;
val RIGHT_AND_FORALL_THM = boolTheory.RIGHT_AND_FORALL_THM


(* ------------------------------------------------------------------------- *)
(* Existential quantifier and disjunction.                                   *)
(* ------------------------------------------------------------------------- *)

val EXISTS_OR_THM = boolTheory.EXISTS_OR_THM;
val OR_EXISTS_THM = GSYM EXISTS_OR_THM;

val LEFT_OR_EXISTS_THM  = boolTheory.LEFT_OR_EXISTS_THM
val RIGHT_OR_EXISTS_THM = boolTheory.RIGHT_OR_EXISTS_THM

(* ------------------------------------------------------------------------- *)
(* Existential quantifier and conjunction.                                   *)
(* ------------------------------------------------------------------------- *)

val LEFT_EXISTS_AND_THM  = boolTheory.LEFT_EXISTS_AND_THM;
val RIGHT_EXISTS_AND_THM = boolTheory.RIGHT_EXISTS_AND_THM;
val TRIV_EXISTS_AND_THM  = boolTheory.BOTH_EXISTS_AND_THM;

val LEFT_AND_EXISTS_THM  = GSYM LEFT_EXISTS_AND_THM;
val RIGHT_AND_EXISTS_THM = GSYM RIGHT_EXISTS_AND_THM;
val TRIV_AND_EXISTS_THM  = GSYM TRIV_EXISTS_AND_THM

(* ------------------------------------------------------------------------- *)
(* Only trivial instances of universal quantifier and disjunction.           *)
(* ------------------------------------------------------------------------- *)

val TRIV_FORALL_OR_THM = boolTheory.BOTH_FORALL_OR_THM;
val TRIV_OR_FORALL_THM = GSYM TRIV_FORALL_OR_THM;

(* ------------------------------------------------------------------------- *)
(* Implication and quantifiers.                                              *)
(* ------------------------------------------------------------------------- *)

val RIGHT_IMP_FORALL_THM = GSYM boolTheory.RIGHT_FORALL_IMP_THM;
val RIGHT_FORALL_IMP_THM = boolTheory.RIGHT_FORALL_IMP_THM;
val LEFT_IMP_EXISTS_THM  = boolTheory.LEFT_EXISTS_IMP_THM;
val LEFT_FORALL_IMP_THM  = boolTheory.LEFT_FORALL_IMP_THM;
val TRIV_FORALL_IMP_THM  = boolTheory.BOTH_FORALL_IMP_THM;
val TRIV_EXISTS_IMP_THM  = boolTheory.BOTH_EXISTS_IMP_THM;

(* ------------------------------------------------------------------------- *)
(* Infinite de Morgan laws.                                                  *)
(* ------------------------------------------------------------------------- *)

val NOT_EXISTS_THM = boolTheory.NOT_EXISTS_THM
val NOT_FORALL_THM = boolTheory.NOT_FORALL_THM;

val EXISTS_NOT_THM = GSYM NOT_FORALL_THM;
val FORALL_NOT_THM = GSYM NOT_EXISTS_THM;

(* ------------------------------------------------------------------------- *)
(* Universal quantifier and disjunction                                      *)
(* ------------------------------------------------------------------------- *)

val LEFT_FORALL_OR_THM  = boolTheory.LEFT_FORALL_OR_THM;
val RIGHT_FORALL_OR_THM = boolTheory.RIGHT_FORALL_OR_THM;
val LEFT_OR_FORALL_THM  = GSYM LEFT_FORALL_OR_THM;
val RIGHT_OR_FORALL_THM = GSYM RIGHT_FORALL_OR_THM;


(* ------------------------------------------------------------------------- *)
(* Implication and quantifiers.                                              *)
(* ------------------------------------------------------------------------- *)

val LEFT_EXISTS_IMP_THM = boolTheory.LEFT_EXISTS_IMP_THM;
val LEFT_IMP_FORALL_THM = GSYM LEFT_EXISTS_IMP_THM;
val RIGHT_EXISTS_IMP_THM = boolTheory.RIGHT_EXISTS_IMP_THM;
val RIGHT_IMP_EXISTS_THM = GSYM RIGHT_EXISTS_IMP_THM;

(* Nasty side effects that the higher order rewriter seems to depend on *)
val _ = add_implicit_rewrites
  [REFL_CLAUSE,
   EQ_CLAUSES,
   NOT_CLAUSES,
   AND_CLAUSES,
   OR_CLAUSES,
   IMP_CLAUSES,
   FORALL_SIMP,
   EXISTS_SIMP,
   ABS_SIMP];;
val _ = add_implicit_rewrites [SELECT_REFL, SELECT_REFL_2];
val _ = add_implicit_rewrites [COND_CLAUSES];
val _ = add_implicit_rewrites [COND_BOOL_CLAUSES];


end (* struct *)
