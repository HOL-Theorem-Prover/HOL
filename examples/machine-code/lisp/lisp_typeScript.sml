Theory lisp_type
Ancestors
  words arithmetic list pred_set pair combin finite_map address
  string
Libs
  wordsLib

val RW = REWRITE_RULE;
val RW1 = ONCE_REWRITE_RULE;


(* type *)

Datatype: SExp = Dot SExp SExp | Val num | Sym string
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

Definition CAR_def:
  (CAR (Dot x y) = x) /\
  (CAR (Val w) = Val w) /\
  (CAR (Sym s) = Sym s)
End

Definition CDR_def:
  (CDR (Dot x y) = y) /\
  (CDR (Val w) = Val w) /\
  (CDR (Sym s) = Sym s)
End

Definition LISP_ADD_def:     LISP_ADD  (Val m) (Val n) = Val (m + n)
End
Definition LISP_SUB_def:     LISP_SUB  (Val m) (Val n) = Val (m - n)
End
Definition LISP_MULT_def:    LISP_MULT (Val m) (Val n) = Val (m * n)
End
Definition LISP_DIV_def:     LISP_DIV  (Val m) (Val n) = Val (m DIV n)
End
Definition LISP_MOD_def:     LISP_MOD  (Val m) (Val n) = Val (m MOD n)
End

Definition LISP_TEST_def:    LISP_TEST x = if x then Sym "t" else Sym "nil"
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

Definition TASK_CONT_def:   TASK_CONT = Sym "t"
End
Definition TASK_EVAL_def:   TASK_EVAL = Sym "nil"
End
Definition TASK_FUNC_def:   TASK_FUNC = Sym "quote"
End

Definition isQuote_def:
  isQuote x <=> isDot x /\ (CAR x = Sym "quote") /\
                isDot (CDR x) /\ (CDR (CDR x) = Sym "nil")
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


(* theorems *)

Theorem SExp_expand:
    !x. (?exp1 exp2. x = Dot exp1 exp2) \/ (?n. x = Val n) \/ (?s. x = Sym s)
Proof
  Cases \\ SRW_TAC [] []
QED

Theorem isDot_thm:
    !z. isDot z = ?a b. z = Dot a b
Proof
  Cases \\ SIMP_TAC std_ss [SExp_11,SExp_distinct,isDot_def]
QED

Theorem isVal_thm:
    !z. isVal z = ?a. z = Val a
Proof
  Cases \\ SIMP_TAC std_ss [SExp_11,SExp_distinct,isVal_def]
QED

Theorem isSym_thm:
    !z. isSym z = ?a. z = Sym a
Proof
  Cases \\ SIMP_TAC std_ss [SExp_11,SExp_distinct,isSym_def]
QED

Theorem isQuote_thm:
    !x. isQuote x = ?y. x = Dot (Sym "quote") (Dot y (Sym "nil"))
Proof
  Cases \\ REWRITE_TAC [isQuote_def,isDot_def,CAR_def,CDR_def,SExp_11]
  \\ SIMP_TAC std_ss [SExp_distinct] \\ Cases_on `S0`
  \\ REWRITE_TAC [isQuote_def,isDot_def,CAR_def,CDR_def,SExp_11]
  \\ METIS_TAC [SExp_distinct]
QED
