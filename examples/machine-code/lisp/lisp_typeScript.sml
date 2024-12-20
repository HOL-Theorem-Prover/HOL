open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_type";

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory;
open combinTheory finite_mapTheory addressTheory stringTheory;


val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* type *)

val _ = Hol_datatype `SExp = Dot of SExp => SExp | Val of num | Sym of string`;
val SExp_11 = fetch "-" "SExp_11";
val SExp_distinct = fetch "-" "SExp_distinct";


(* definitions *)

val isDot_def = Define `
  (isDot (Dot x y) = T) /\ (isDot (Val n) = F) /\ (isDot (Sym s) = F)`;
val isVal_def = Define `
  (isVal (Dot x y) = F) /\ (isVal (Val n) = T) /\ (isVal (Sym s) = F)`;
val isSym_def = Define `
  (isSym (Dot x y) = F) /\ (isSym (Val n) = F) /\ (isSym (Sym s) = T)`;

val getVal_def = Define `
  (getVal (Dot x y) = 0) /\ (getVal (Val n) = n) /\ (getVal (Sym s) = 0)`;

val CAR_def = Define `
  (CAR (Dot x y) = x) /\
  (CAR (Val w) = Val w) /\
  (CAR (Sym s) = Sym s)`;

val CDR_def = Define `
  (CDR (Dot x y) = y) /\
  (CDR (Val w) = Val w) /\
  (CDR (Sym s) = Sym s)`;

val LISP_ADD_def   = Define `LISP_ADD  (Val m) (Val n) = Val (m + n)`;
val LISP_SUB_def   = Define `LISP_SUB  (Val m) (Val n) = Val (m - n)`;
val LISP_MULT_def  = Define `LISP_MULT (Val m) (Val n) = Val (m * n)`;
val LISP_DIV_def   = Define `LISP_DIV  (Val m) (Val n) = Val (m DIV n)`;
val LISP_MOD_def   = Define `LISP_MOD  (Val m) (Val n) = Val (m MOD n)`;

val LISP_TEST_def  = Define `LISP_TEST x = if x then Sym "t" else Sym "nil"`;

val LISP_EQUAL_def   = Define `LISP_EQUAL x y = LISP_TEST (x = y)`;
val LISP_LESS_def    = Define `LISP_LESS m n  = LISP_TEST (getVal m < getVal n)`;
val LISP_ATOMP_def   = Define `LISP_ATOMP x   = LISP_TEST (~(isDot x))`;
val LISP_CONSP_def   = Define `LISP_CONSP x   = LISP_TEST (isDot x)`;
val LISP_NUMBERP_def = Define `LISP_NUMBERP x = LISP_TEST (isVal x)`;
val LISP_SYMBOLP_def = Define `LISP_SYMBOLP x = LISP_TEST (isSym x)`;

val TASK_CONT_def = Define `TASK_CONT = Sym "t"`;
val TASK_EVAL_def = Define `TASK_EVAL = Sym "nil"`;
val TASK_FUNC_def = Define `TASK_FUNC = Sym "quote"`;

val isQuote_def = Define `
  isQuote x <=> isDot x /\ (CAR x = Sym "quote") /\
                isDot (CDR x) /\ (CDR (CDR x) = Sym "nil")`;

val LSIZE_def = Define `
  (LSIZE (Dot x y) = SUC (LSIZE x + LSIZE y)) /\
  (LSIZE (Val w) = 0) /\
  (LSIZE (Sym s) = 0)`;

val LDEPTH_def = Define `
  (LDEPTH (Dot x y) = SUC (MAX (LDEPTH x) (LDEPTH y))) /\
  (LDEPTH (Val w) = 0) /\
  (LDEPTH (Sym s) = 0)`;

val SUM_LSIZE_def = Define `
  (SUM_LSIZE [] = 0) /\
  (SUM_LSIZE (x::xs) = LSIZE x + SUM_LSIZE xs)`;


(* theorems *)

val SExp_expand = store_thm("SExp_expand",
  ``!x. (?exp1 exp2. x = Dot exp1 exp2) \/ (?n. x = Val n) \/ (?s. x = Sym s)``,
  Cases \\ SRW_TAC [] []);

val isDot_thm = store_thm("isDot_thm",
  ``!z. isDot z = ?a b. z = Dot a b``,
  Cases \\ SIMP_TAC std_ss [SExp_11,SExp_distinct,isDot_def]);

val isVal_thm = store_thm("isVal_thm",
  ``!z. isVal z = ?a. z = Val a``,
  Cases \\ SIMP_TAC std_ss [SExp_11,SExp_distinct,isVal_def]);

val isSym_thm = store_thm("isSym_thm",
  ``!z. isSym z = ?a. z = Sym a``,
  Cases \\ SIMP_TAC std_ss [SExp_11,SExp_distinct,isSym_def]);

val isQuote_thm = store_thm("isQuote_thm",
  ``!x. isQuote x = ?y. x = Dot (Sym "quote") (Dot y (Sym "nil"))``,
  Cases \\ REWRITE_TAC [isQuote_def,isDot_def,CAR_def,CDR_def,SExp_11]
  \\ SIMP_TAC std_ss [SExp_distinct] \\ Cases_on `S0`
  \\ REWRITE_TAC [isQuote_def,isDot_def,CAR_def,CDR_def,SExp_11]
  \\ METIS_TAC [SExp_distinct]);


val _ = export_theory();
