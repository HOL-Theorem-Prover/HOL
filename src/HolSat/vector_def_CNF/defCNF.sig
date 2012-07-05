(* ========================================================================= *)
(* DEFINITIONAL CNF IN HOL.                                                  *)
(* Created by Joe Hurd, February 2002.                                       *)
(* ========================================================================= *)

signature defCNF =
sig

include Abbrev

(* ------------------------------------------------------------------------- *)
(* Definitional Negation Normal Form                                         *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (~(p = ~(q = r)) = ~(~(p = q) = r))                                     *)
(*   =                                                                       *)
(*   ((p = (q = r)) = ((p = ~q) = ~r))                                       *)
(* ------------------------------------------------------------------------- *)

val DEF_NNF_CONV : conv

(* ------------------------------------------------------------------------- *)
(* Definitional Conjunctive Normal Form                                      *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (~(p = ~(q = r)) = ~(~(p = q) = r))                                     *)
(*   =                                                                       *)
(*   ?v v1 v2 v3 v4.                                                         *)
(*     (v4 \/ v1 \/ v3) /\ (v4 \/ ~v1 \/ ~v3) /\ (v1 \/ ~v3 \/ ~v4) /\       *)
(*     (v3 \/ ~v1 \/ ~v4) /\ (v3 \/ v2 \/ ~r) /\ (v3 \/ ~v2 \/ r) /\         *)
(*     (v2 \/ r \/ ~v3) /\ (~r \/ ~v2 \/ ~v3) /\ (v2 \/ p \/ ~q) /\          *)
(*     (v2 \/ ~p \/ q) /\ (p \/ q \/ ~v2) /\ (~q \/ ~p \/ ~v2) /\            *)
(*     (v1 \/ p \/ v) /\ (v1 \/ ~p \/ ~v) /\ (p \/ ~v \/ ~v1) /\             *)
(*     (v \/ ~p \/ ~v1) /\ (v \/ q \/ r) /\ (v \/ ~q \/ ~r) /\               *)
(*     (q \/ ~r \/ ~v) /\ (r \/ ~q \/ ~v) /\ v4                              *)
(* ------------------------------------------------------------------------- *)

val PURE_DEF_CNF_CONV    : conv         (* Introduces definitions *)
val CLEANUP_DEF_CNF_CONV : conv         (* Converts defns to CNF *)
val DEF_CNF_CONV         : conv         (* NNF + PURE + CLEANUP *)

(* ------------------------------------------------------------------------- *)
(* Definitional Conjunctive Normal Form using variable vectors               *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (~(p = ~(q = r)) = ~(~(p = q) = r))                                     *)
(*   =                                                                       *)
(*   ?v.                                                                     *)
(*     (v 4 \/ v 1 \/ v 3) /\ (v 4 \/ ~v 1 \/ ~v 3) /\                       *)
(*     (v 1 \/ ~v 3 \/ ~v 4) /\ (v 3 \/ ~v 1 \/ ~v 4) /\                     *)
(*     (~r \/ ~v 2 \/ ~v 3) /\ (v 2 \/ r \/ ~v 3) /\ (v 3 \/ ~v 2 \/ r) /\   *)
(*     (v 3 \/ v 2 \/ ~r) /\ (~q \/ ~p \/ ~v 2) /\ (p \/ q \/ ~v 2) /\       *)
(*     (v 2 \/ ~p \/ q) /\ (v 2 \/ p \/ ~q) /\ (v 0 \/ ~p \/ ~v 1) /\        *)
(*     (p \/ ~v 0 \/ ~v 1) /\ (v 1 \/ ~p \/ ~v 0) /\ (v 1 \/ p \/ v 0) /\    *)
(*     (r \/ ~q \/ ~v 0) /\ (q \/ ~r \/ ~v 0) /\ (v 0 \/ ~q \/ ~r) /\        *)
(*     (v 0 \/ q \/ r) /\ v 4                                                *)
(* ------------------------------------------------------------------------- *)

val PURE_DEF_CNF_VECTOR_CONV : conv
val DEF_CNF_VECTOR_CONV      : conv     (* NNF + PURE + CLEANUP *)

val dcnfgv : (unit -> Term.term) ref
  val ndefs : Term.term ref
end
