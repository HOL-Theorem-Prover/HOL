open HolKernel Parse boolLib bossLib;
open forTheory state_transformerTheory

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

val mibind_def = Define`
  mibind f g = mbind f (λx. g)`;

val mfail_def = Define`
  mfail = return Rfail`;

val _ =
    monadsyntax.declare_monad ("for_state", {
      bind = “mbind”, ignorebind = SOME “mibind”,
      unit = “state_transformer$UNIT”,
      guard = NONE, fail = NONE, choice = NONE
    })
val _ = monadsyntax.enable_monad "for_state"

val mbreak_def = Define`
  mbreak = return Rbreak`;

val mtimeout_def = Define`
  mtimeout = return Rtimeout`;

val mreturn_def = Define`
  mreturn = return o Rval`;

val mtry_def = Define`
  mtry m h k s =
  case m s of
  | (Rbreak, s) => h s
  | _ => mibind m k s`;

val lookup_store_def = Define`
  lookup_store x s =
    case FLOOKUP s.store x of
    | NONE => mfail s
    | SOME n => mreturn n s`;

val get_clock_def = Define`
  get_clock s = (s.clock,s)`;

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

(* Statement evaluation *)

val _ = overload_on("mon_sem_t",``combin$C sem_t``);

val mon_sem_t_exp = Q.prove(
  `∀e. mon_sem_t (Exp e) = mon_sem_e e`,
  rw[FUN_EQ_THM] >> EVAL_TAC);

val mon_sem_t_dec = Q.prove(
  `∀x t. mon_sem_t (Dec x t) =
   do update_state (store_var x 0);
     mon_sem_t t
   od`,
  rw[FUN_EQ_THM] >> EVAL_TAC);

val mon_sem_t_break = Q.prove(
  `mon_sem_t Break = mbreak`,
  rw[FUN_EQ_THM] >> EVAL_TAC);

val mon_sem_t_seq = Q.prove(
  `∀t1 t2. mon_sem_t (Seq t1 t2) =
   do mon_sem_t t1; mon_sem_t t2 od`,
  rw[FUN_EQ_THM] >> EVAL_TAC >>
  BasicProvers.EVERY_CASE_TAC);

val mon_sem_t_if = Q.prove(
  `∀e t1 t2. mon_sem_t (If e t1 t2) =
   do
     n1 <- mon_sem_e e;
     mon_sem_t (if n1 = 0 then t2 else t1)
   od`,
  rw[FUN_EQ_THM] >> EVAL_TAC >>
  BasicProvers.EVERY_CASE_TAC);

val dec_clock_then_def = Define`
  dec_clock_then f =
  do
    k <- get_clock;
    if k = 0 then mtimeout
    else do update_state dec_clock; f od
  od`;

val mon_sem_t_for = Q.prove(
  `∀e1 e2 t. mon_sem_t (For e1 e2 t) =
   do
     n1 <- mon_sem_e e1;
     if n1 = 0 then mreturn 0 else
     mtry (mon_sem_t t) (mreturn 0)
     do
       mon_sem_e e2;
       dec_clock_then (mon_sem_t (For e1 e2 t))
     od
   od`,
  rw[FUN_EQ_THM] >>
  rw[Once sem_t_def,dec_clock_then_def,mbind_def,mibind_def,mreturn_def,UNIT_DEF] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs[mtry_def,mibind_def,mbind_def,BIND_DEF,IGNORE_BIND_DEF,get_clock_def,update_state_def,mtimeout_def,UNIT_DEF]);

val monadic_sem_t = save_thm("monadic_sem_t",
  LIST_CONJ[mon_sem_t_exp,mon_sem_t_dec,mon_sem_t_seq,mon_sem_t_seq,mon_sem_t_if,mon_sem_t_for]);

val _ = export_theory ();
