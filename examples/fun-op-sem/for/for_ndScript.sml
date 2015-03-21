open HolKernel Parse boolLib bossLib;

val _ = new_theory "for_nd";

(*

This file defines a FOR language that's very similar to the language
used by Arthur Charguéraud in his ESOP'13 paper:

  Pretty-Big-Step Semantics
  http://www.chargueraud.org/research/2012/pretty/

In this non-deterministic (nd) version of Charguéraud's FOR language,
we add basic I/O and non-deterministic evaluation order.

A simpler version of this language can be found in forScript.sml.

*)

open pred_setTheory optionTheory stringTheory llistTheory integerTheory;
open lcsymtacs;

val _ = temp_tight_equality ();
val ect = BasicProvers.EVERY_CASE_TAC;


(* === Syntax === *)

(* Expressions:
   - Evaluation order of Add is unspecified, but one subexpression
     must be completely evaluated before the other.
   - Getchar returns -1 to signal the end of file. *)

val _ = Datatype `
e = Var string
  | Num int
  | Add e e
  | Assign string e
  | Getchar
  | Putchar e`;

(* Statements: *)
val _ = Datatype `
t =
  | Dec string t
  | Exp e
  | Break
  | Seq t t
  | If e t t
  | For e e t`;


(* === Types used in semantics (given in for_nd_semScript.sml) === *)

(* What is observable about program behaviour. A program can terminate
   after doing a finite amount of I/O; it can diverge doing a
   potentially infinite amount of IO (llist is the lazy list type
   constructor of lists that can be either finite or infinite); or it
   can crash. We don't bother with the pre-crash IO because well-typed
   programs won't crash. *)

val _ = Datatype `
  io_tag = Itag int | Otag int`;

val _ = Datatype `
  observation = Terminate (io_tag list) | Diverge (io_tag llist) | Crash`;

val getchar_def = Define `
getchar stream =
  case LTL stream of
     | NONE => (-1, stream)
     | SOME rest =>
         let v = &(ORD (THE (LHD stream))) in
           (v, rest)`;


(* === A simple type system === *)

(* This type system checks for Break statements and variable accesses. *)
val type_e_def = Define `
(type_e s (Var x) ⇔ x ∈ s) ∧
(type_e s (Num num) ⇔ T) ∧
(type_e s (Add e1 e2) ⇔ type_e s e1 ∧ type_e s e2) ∧
(type_e s (Assign x e) ⇔ x ∈ s ∧ type_e s e) ∧
(type_e s Getchar ⇔ T) ∧
(type_e s (Putchar e) ⇔ type_e s e)`;

val type_t_def = Define `
(type_t in_for s (Exp e) ⇔ type_e s e) ∧
(type_t in_for s (Dec x t) ⇔ type_t in_for (x INSERT s) t) ∧
(type_t in_for s Break ⇔ in_for) ∧
(type_t in_for s (Seq t1 t2) ⇔ type_t in_for s t1 ∧ type_t in_for s t2) ∧
(type_t in_for s (If e t1 t2) ⇔ type_e s e ∧ type_t in_for s t1 ∧ type_t in_for s t2) ∧
(type_t in_for s (For e1 e2 t) ⇔ type_e s e1 ∧ type_e s e2 ∧ type_t T s t)`;

val type_weakening_e = Q.store_thm ("type_weakening_e",
`!s e s' s1. type_e s e ∧ s ⊆ s1 ⇒ type_e s1 e`,
 Induct_on `e` >>
 rw [type_e_def, SUBSET_DEF] >>
 ect >>
 fs [] >>
 rw [EXTENSION] >>
 metis_tac [SUBSET_DEF, NOT_SOME_NONE, SOME_11]);

val type_weakening_t = Q.store_thm ("type_weakening_t",
`!in_for s t s' s1. type_t in_for s t ∧ s ⊆ s1 ⇒ type_t in_for s1 t`,
 Induct_on `t` >>
 rw [type_t_def, SUBSET_DEF] >>
 ect >>
 fs [] >>
 rw [EXTENSION] >>
 metis_tac [SUBSET_DEF, NOT_SOME_NONE, SOME_11, type_weakening_e, INSERT_SUBSET]);

val _ = export_theory ();
