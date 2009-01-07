open HolKernel boolLib bossLib Parse; val _ = new_theory "lisp_type";

open wordsTheory arithmeticTheory wordsLib listTheory pred_setTheory pairTheory; 
open combinTheory finite_mapTheory addressTheory stringTheory;


infix \\ 
val op \\ = op THEN;
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* type *)

val _ = Hol_datatype `SExp = Dot of SExp => SExp | Num of num | Sym of string`;
val SExp_11 = fetch "-" "SExp_11";
val SExp_distinct = fetch "-" "SExp_distinct";


(* definitions *)

val isDot_def = Define `
  (isDot (Dot x y) = T) /\ (isDot (Num n) = F) /\ (isDot (Sym s) = F)`;
val isNum_def = Define `
  (isNum (Dot x y) = F) /\ (isNum (Num n) = T) /\ (isNum (Sym s) = F)`;
val isSym_def = Define `
  (isSym (Dot x y) = F) /\ (isSym (Num n) = F) /\ (isSym (Sym s) = T)`;

val getNum_def = Define `
  (getNum (Dot x y) = 0) /\ (getNum (Num n) = n) /\ (getNum (Sym s) = 0)`;

val CAR_def = Define `
  (CAR (Dot x y) = x) /\
  (CAR (Num w) = Num w) /\ 
  (CAR (Sym s) = Sym s)`;

val CDR_def = Define `
  (CDR (Dot x y) = y) /\
  (CDR (Num w) = Num w) /\ 
  (CDR (Sym s) = Sym s)`;

val LISP_ADD_def   = Define `LISP_ADD  (Num m) (Num n) = Num (m + n)`;
val LISP_SUB_def   = Define `LISP_SUB  (Num m) (Num n) = Num (m - n)`;
val LISP_MULT_def  = Define `LISP_MULT (Num m) (Num n) = Num (m * n)`;
val LISP_DIV_def   = Define `LISP_DIV  (Num m) (Num n) = Num (m DIV n)`;
val LISP_LESS_def  = Define `LISP_LESS (Num m) (Num n) = m < n`;
val LISP_EQUAL_def = Define `LISP_EQUAL x y = if x = y then Sym "t" else Sym "nil"`;

val isQuote_def = Define `
  isQuote x = isDot x /\ (CAR x = Sym "quote") /\ 
              isDot (CDR x) /\ (CDR (CDR x) = Sym "nil")`;

val LSIZE_def = Define `
  (LSIZE (Dot x y) = SUC (LSIZE x + LSIZE y)) /\
  (LSIZE (Num w) = 0) /\ 
  (LSIZE (Sym s) = 0)`;
  
val LDEPTH_def = Define `
  (LDEPTH (Dot x y) = SUC (MAX (LDEPTH x) (LDEPTH y))) /\
  (LDEPTH (Num w) = 0) /\ 
  (LDEPTH (Sym s) = 0)`;

val SUM_LSIZE_def = Define `
  (SUM_LSIZE [] = 0) /\
  (SUM_LSIZE (x::xs) = LSIZE x + SUM_LSIZE xs)`;


(* theorems *)

val isDot_thm = store_thm("isDot_thm",
  ``!z. isDot z = ?a b. z = Dot a b``,
  Cases \\ SIMP_TAC std_ss [SExp_11,SExp_distinct,isDot_def]);

val isNum_thm = store_thm("isNum_thm",
  ``!z. isNum z = ?a. z = Num a``,
  Cases \\ SIMP_TAC std_ss [SExp_11,SExp_distinct,isNum_def]);

val isSym_thm = store_thm("isSym_thm",
  ``!z. isSym z = ?a. z = Sym a``,
  Cases \\ SIMP_TAC std_ss [SExp_11,SExp_distinct,isSym_def]);


val _ = export_theory();
