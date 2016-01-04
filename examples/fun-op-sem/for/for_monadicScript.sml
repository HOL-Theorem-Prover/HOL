open HolKernel Parse boolLib bossLib lcsymtacs;
open forTheory state_transformerTheory monadsyntax;

val _ = new_theory "for_monadic";
val _ = temp_tight_equality ();

(*
This file casts the semantics for the FOR language from forTheory using a monad
instead of explicit case expressions.
*)

(* the r-state monad *)

val mbind_def = Define`
  mbind f g s =
    case f s of
    | (Rval x,s) => g x s
    | r => r`;
val _ = overload_on("monad_bind",``mbind``);

val mfail_def = Define`
  mfail = return Rfail`;

val mreturn_def = Define`
  mreturn = return o Rval`;

val lookup_store_def = Define`
  lookup_store x s =
    case FLOOKUP s.store x of
    | NONE => mfail s
    | SOME n => mreturn n s`;

val update_state_def = Define`
  update_state f s = ((),f s)`;

(* Expression evaluation *)

val _ = overload_on("mon_sem_e",``combin$C sem_e``);

val mon_sem_e_var = Q.prove(
  `∀x. mon_sem_e (Var x) = lookup_store x`,
  rw[FUN_EQ_THM] >> EVAL_TAC >>
  BasicProvers.EVERY_CASE_TAC);

val mon_sem_e_num = Q.prove(
  `∀num. mon_sem_e (Num num) = mreturn num`,
  EVAL_TAC >> rw[]);

val mon_sem_e_add = Q.prove(
  `∀e1 e2.
   mon_sem_e (Add e1 e2) =
   do
     n1 <- mon_sem_e e1;
     n2 <- mon_sem_e e2;
     mreturn (n1+n2)
   od`,
  rw[FUN_EQ_THM] >>
  EVAL_TAC >>
  BasicProvers.EVERY_CASE_TAC);

val mon_sem_e_assign = Q.prove(
  `∀x e.
   mon_sem_e (Assign x e) =
   do
     n <- mon_sem_e e;
     update_state (store_var x n);
     mreturn n
   od`,
  rw[FUN_EQ_THM] >>
  EVAL_TAC >>
  BasicProvers.EVERY_CASE_TAC);

val monadic_sem_e = save_thm("monadic_sem_e",
  LIST_CONJ[mon_sem_e_var,mon_sem_e_num,mon_sem_e_add,mon_sem_e_assign]);

val _ = export_theory ();
