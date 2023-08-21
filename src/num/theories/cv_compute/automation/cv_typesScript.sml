open HolKernel Parse boolLib bossLib cvTheory;
open integerTheory wordsTheory;

val _ = new_theory "cv_types";

val _ = set_grammar_ancestry ["cv", "one", "option", "list", "sum", "pair", "words"];

Overload c2n[local] = “cv$c2n”
Overload c2b[local] = “cv$c2b”
Overload Num[local] = “cv$Num”
Overload Pair[local] = “cv$Pair”

(* every from/to function must satisfy: *)

Definition from_to_def:
  from_to (f:'a -> cv) (t:cv -> 'a) = !x. t (f x) = x
End

(* unit *)

Definition from_unit_def:
  from_unit (u:unit) = (Num 0):cv
End

Definition to_unit_def:
  to_unit (x:cv) = ()
End

Theorem from_to_unit:
  from_to from_unit to_unit
Proof
  fs [from_to_def]
QED

(* bool *)

Theorem from_to_bool:
  from_to b2c c2b
Proof
  fs [from_to_def] \\ Cases \\ fs [b2c_def]
QED

(* num *)

Theorem from_to_num:
  from_to Num c2n
Proof
  fs [from_to_def]
QED

(* char *)

Definition from_char_def:
  from_char (c:char) = Num (ORD c)
End

Definition to_char_def:
  to_char x = CHR (c2n x)
End

Theorem from_to_char:
  from_to from_char to_char
Proof
  fs [from_to_def] \\ Cases \\ fs [from_char_def,to_char_def]
QED

(* int *)

Definition from_int_def:
  from_int (i:int) =
    if integer$int_lt i (integer$int_of_num 0) then
      Pair (Num (integer$Num i)) (Num 0)
    else Num (integer$Num i)
End

Definition to_int_def:
  to_int (Num n) = integer$int_of_num n /\
  to_int (Pair x y) = integer$int_neg (integer$int_of_num (c2n x))
End

Theorem from_to_int:
  from_to from_int to_int
Proof
  fs [from_to_def] \\ Cases \\ fs [from_int_def,to_int_def]
QED

(* word *)

Definition from_word_def:
  from_word (w:'a words$word) = Num (words$w2n w)
End

Definition to_word_def:
  to_word n = words$n2w (c2n n) :'a words$word
End

Theorem from_to_word:
  from_to from_word to_word
Proof
  fs [from_to_def] \\ Cases \\ fs [from_word_def,to_word_def]
QED

(* option *)

Definition from_option_def:
  from_option f NONE = Num 0 /\
  from_option f (SOME x) =
    case f x of
    | Num n => Num (n+1)
    | other => other
End

Definition to_option_def:
  to_option t (Num n) = (if n = 0 then NONE else SOME (t (Num (n - 1)))) /\
  to_option t other = SOME (t other)
End

Theorem from_to_option:
  from_to f t ==>
  from_to (from_option f) (to_option t)
Proof
  fs [from_to_def] \\ strip_tac
  \\ Cases \\ fs [from_option_def]
  \\ Cases_on ‘f x'’ \\ fs [to_option_def]
  \\ pop_assum $ assume_tac o GSYM \\ fs []
QED

(* pair *)

Definition from_prod_def:
  from_prod f1 f2 (x,y) = Pair (f1 x) (f2 y)
End

Definition to_prod_def:
  to_prod t1 t2 (Pair x y) = (t1 x, t2 y)
End

Theorem from_to_prod:
  from_to f1 t1 /\ from_to f2 t2 ==>
  from_to (from_prod f1 f2) (to_prod t1 t2)
Proof
  fs [from_to_def] \\ strip_tac
  \\ Cases \\ fs [from_prod_def,to_prod_def]
QED

(* sum *)

Definition from_sum_def:
  from_sum f1 f2 (INL x) = Pair (Num 0) (f1 x) /\
  from_sum f1 f2 (INR y) = Pair (Num 1) (f2 y)
End

Definition to_sum_def:
  to_sum t1 t2 (Pair x y) =
    if x = Num 0 then INL (t1 y) else INR (t2 y)
End

Theorem from_to_sum:
  from_to f1 t1 /\ from_to f2 t2 ==>
  from_to (from_sum f1 f2) (to_sum t1 t2)
Proof
  fs [from_to_def] \\ strip_tac
  \\ Cases \\ fs [from_sum_def,to_sum_def]
QED

(* list *)

Definition from_list_def:
  from_list f [] = Num 0 /\
  from_list f (x::xs) = Pair (f x) (from_list f xs)
End

Definition to_list_def:
  to_list f (Num n) = [] /\
  to_list f (Pair x y) = f x :: to_list f y
End

Theorem from_to_list:
  from_to f t ==>
  from_to (from_list f) (to_list t)
Proof
  fs [from_to_def] \\ strip_tac
  \\ Induct \\ fs [from_list_def,to_list_def]
QED

val _ = export_theory();
