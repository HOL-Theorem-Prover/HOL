open BasicProvers Defn HolKernel Parse Conv SatisfySimps Tactic monadsyntax
     boolTheory bossLib arithmeticTheory;

open realTheory arithmeticTheory realLib RealArith;

open LassieLib logicTacticsLib;

val _ = new_theory "caseStudy4NaprochePowerset";

val _ = LassieLib.loadJargon "Logic";

Theorem cantor:
 ∀ f:'a -> ('a -> bool).
  ~ (∀ y:'a -> bool. ∃ x:'a. f x = y)
Proof
  LassieLib.nltac ‘
    assume the contrary. simplify.
    we know '∃ x. f x = λ x . ~ (x IN (f x))'.
    simplify.
    case split for 'x IN f x'.
    simplify with [IN_DEF]. trivial.’
  (* CCONTR_TAC \\ fs[]
  \\ first_x_assum (qspec_then `\ x. ~ (x IN (f x))` assume_tac)
  \\ fs[]
  \\ Cases_on `x IN f x`
  >- (
    pop_assum mp_tac \\ fs[IN_DEF] \\ metis_tac[])
  >- (fs[IN_DEF] \\ metis_tac[]) *)
QED

(*
Let M denote a set.
Let f denote a function.
Let the value of f at x stand for f[x].
Let f is defined on M stand for Dom(f) = M.
Let the domain of f stand for Dom(f). *)

(* Axiom. The value of f at any element of the domain of f is a set. *)
(** This axiom can be encoded by giving f the type :'a -> 'b set option **)

(* Definition.
A subset of M is a set N such that every element of N is an element of M. *)

(* Definition.
The powerset of M is the set of subsets of M. *)

(* Definition.
f surjects onto M iff every element of M is equal to the value of f at some element of the domain of f. *)

(* Proposition.
No function that is defined on M surjects onto the powerset of M.
Proof.
Assume the contrary.
Take a function f that is defined on M and surjects onto the powerset of M.
Define N = { x in M | x is not an element of f[x] }.
Then N is not equal to the value of f at any element of M.
Contradiction. qed. *)

val _ = export_theory();
