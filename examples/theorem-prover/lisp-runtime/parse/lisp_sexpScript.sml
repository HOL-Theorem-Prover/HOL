Theory lisp_sexp
Ancestors
  words arithmetic list pred_set pair combin finite_map string
Libs
  wordsLib

val _ = ParseExtras.temp_loose_equality()

infix \\
val op \\ = op THEN;
val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* type *)

Datatype: SExp = Dot of SExp => SExp | Val of num | Sym of string
End
val SExp_11 = fetch "-" "SExp_11";
val SExp_distinct = fetch "-" "SExp_distinct";


(* definitions *)

Definition isDot_def:
  (isDot (Dot x y) = T) /\ (isDot (Val n) = F) /\ (isDot (Sym s) = F)
End
Definition isVal_def:
  (isVal (Dot x y) = F) /\ (isVal (Val n) = T) /\ (isVal (Sym s) = F)
End
Definition isSym_def:
  (isSym (Dot x y) = F) /\ (isSym (Val n) = F) /\ (isSym (Sym s) = T)
End

Definition getVal_def:
  (getVal (Dot x y) = 0) /\ (getVal (Val n) = n) /\ (getVal (Sym s) = 0)
End
Definition getSym_def:
  (getSym (Dot x y) = "NIL") /\ (getSym (Val n) = "NIL") /\ (getSym (Sym s) = s)
End

Definition CAR_def:
  (CAR (Dot x y) = x) /\
  (CAR (Val w) = Sym "NIL") /\
  (CAR (Sym s) = Sym "NIL")
End

Definition CDR_def:
  (CDR (Dot x y) = y) /\
  (CDR (Val w) = Sym "NIL") /\
  (CDR (Sym s) = Sym "NIL")
End

Definition LISP_CONS_def:    LISP_CONS x y = Dot x y
End

Definition LISP_ADD_def:     LISP_ADD  x y = Val (getVal x + getVal y)
End
Definition LISP_SUB_def:     LISP_SUB  x y = Val (getVal x - getVal y)
End
Definition LISP_MULT_def:    LISP_MULT x y = Val (getVal x * getVal y)
End
Definition LISP_DIV_def:     LISP_DIV  x y = Val (getVal x DIV getVal y)
End
Definition LISP_MOD_def:     LISP_MOD  x y = Val (getVal x MOD getVal y)
End

Definition LISP_TEST_def:    LISP_TEST x = if x then Sym "T" else Sym "NIL"
End

Definition LISP_EQUAL_def:     LISP_EQUAL x y = LISP_TEST (x = y)
End
Definition LISP_LESS_def:      LISP_LESS m n  = LISP_TEST (getVal m < getVal n)
End
Definition LISP_ATOMP_def:     LISP_ATOMP x   = LISP_TEST (~(isDot x))
End
Definition LISP_CONSP_def:     LISP_CONSP x   = LISP_TEST (isDot x)
End
Definition LISP_NUMBERP_def:   LISP_NUMBERP x = LISP_TEST (isVal x)
End
Definition LISP_SYMBOLP_def:   LISP_SYMBOLP x = LISP_TEST (isSym x)
End
Definition LISP_SYMBOL_LESS_def:   LISP_SYMBOL_LESS x y = LISP_TEST (getSym x < getSym y)
End

Definition TASK_CONT_def:   TASK_CONT = Sym "T"
End
Definition TASK_EVAL_def:   TASK_EVAL = Sym "NIL"
End
Definition TASK_FUNC_def:   TASK_FUNC = Sym "QUOTE"
End

Definition isQuote_def:
  isQuote x = isDot x /\ (CAR x = Sym "QUOTE") /\
              isDot (CDR x) /\ (CDR (CDR x) = Sym "NIL")
End

Definition LSIZE_def:
  (LSIZE (Dot x y) = SUC (LSIZE x + LSIZE y)) /\
  (LSIZE (Val w) = 0) /\
  (LSIZE (Sym s) = 0)
End

Definition LDEPTH_def:
  (LDEPTH (Dot x y) = SUC (MAX (LDEPTH x) (LDEPTH y))) /\
  (LDEPTH (Val w) = 0) /\
  (LDEPTH (Sym s) = 0)
End

Definition SUM_LSIZE_def:
  (SUM_LSIZE [] = 0) /\
  (SUM_LSIZE (x::xs) = LSIZE x + SUM_LSIZE xs)
End

Definition UPDATE_NTH_def:
  (UPDATE_NTH 0 x [] = []) /\
  (UPDATE_NTH (SUC n) x [] = []) /\
  (UPDATE_NTH 0 x (y::ys) = x::ys) /\
  (UPDATE_NTH (SUC n) x (y::ys) = y::UPDATE_NTH n (x:'a) ys)
End

Datatype:
  lisp_primitive_op =
    opCONS | opEQUAL | opLESS | opSYMBOL_LESS | opADD | opSUB |
    opCONSP | opNATP | opSYMBOLP | opCAR | opCDR
End

Definition isTrue_def:   isTrue s = ~(s = Sym "NIL")
End


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
  ``!x. isQuote x = ?y. x = Dot (Sym "QUOTE") (Dot y (Sym "NIL"))``,
  Cases \\ REWRITE_TAC [isQuote_def,isDot_def,CAR_def,CDR_def,SExp_11]
  \\ SIMP_TAC std_ss [SExp_distinct] \\ Cases_on `S0`
  \\ REWRITE_TAC [isQuote_def,isDot_def,CAR_def,CDR_def,SExp_11]
  \\ METIS_TAC [SExp_distinct]);


