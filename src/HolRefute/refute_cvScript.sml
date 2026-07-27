Theory refute_cv
Ancestors
  refute cv_std
Libs
  cv_transLib wordsLib

open cv_transLib

(* The substrate-independent random stream is translated once, here, so
   per-goal cv translations can reuse it without touching refuteTheory. *)
val _ = cv_trans refuteTheory.rand_next_def
val _ = cv_trans refuteTheory.rand_out_def
val _ = cv_trans refuteTheory.rand_below_def

(* cv translation deliberately rejects higher-order parameters.  Enum search
   uses [first_hit] only with the singleton candidate function, so expose and
   translate that first-order specialization here. *)
Definition refute_cv_first_hit_def:
  refute_cv_first_hit [] (n : num) = (n, NONE) /\
  refute_cv_first_hit (x :: xs) n =
    if n = 0 then (n, SOME x)
    else refute_cv_first_hit xs (n - 1)
End

Theorem refute_cv_first_hit_eq:
  refute_cv_first_hit xs n = first_hit (\x. [x]) xs n
Proof
  qid_spec_tac `n` >>
  Induct_on `xs` >> simp [refute_cv_first_hit_def, first_hit_def]
QED

val _ = cv_trans refute_cv_first_hit_def

(* Numeric generators. *)
Definition refute_cv_num_range_def:
  refute_cv_num_range 0 acc = 0 :: acc /\
  refute_cv_num_range (SUC n) acc =
    refute_cv_num_range n (SUC n :: acc)
End

Definition refute_cv_exh_num_def:
  refute_cv_exh_num size = refute_cv_num_range size []
End

Definition refute_cv_rnd_num_def:
  refute_cv_rnd_num size state = rand_below (size + 1) state
End

Definition refute_cv_int_range_def:
  refute_cv_int_range size 0 acc = (-( &size)) :: acc /\
  refute_cv_int_range size (SUC n) acc =
    refute_cv_int_range size n (((&(SUC n) : int) - &size) :: acc)
End

Definition refute_cv_exh_int_def:
  refute_cv_exh_int size = refute_cv_int_range size (2 * size) []
End

Definition refute_cv_rnd_int_def:
  refute_cv_rnd_int size state =
    let (n, state') = rand_below (2 * size + 1) state
    in ((&n : int) - &size, state')
End

val _ = cv_trans refute_cv_num_range_def
val _ = cv_trans refute_cv_exh_num_def
val _ = cv_trans refute_cv_rnd_num_def
val _ = cv_trans refute_cv_int_range_def
val _ = cv_trans refute_cv_exh_int_def
val _ = cv_trans refute_cv_rnd_int_def

(* Complete finite scalar generators.  The MOD in the character functions
   makes CHR's range condition syntactically evident to cv_trans. *)
Definition refute_cv_char_range_def:
  refute_cv_char_range 0 acc = acc /\
  refute_cv_char_range (SUC n) acc =
    refute_cv_char_range n (CHR (n MOD 256) :: acc)
End

Definition refute_cv_exh_char_def:
  refute_cv_exh_char (size : num) = refute_cv_char_range 256 []
End

Definition refute_cv_rnd_char_def:
  refute_cv_rnd_char (size : num) state =
    let (n, state') = rand_below 256 state
    in (CHR (n MOD 256), state')
End

Definition refute_cv_exh_bool_def:
  refute_cv_exh_bool (size : num) = [T; F]
End

Definition refute_cv_rnd_bool_def:
  refute_cv_rnd_bool (size : num) state =
    let (n, state') = rand_below 2 state
    in (if n = 0 then T else F, state')
End

Definition refute_cv_exh_rf1_def:
  refute_cv_exh_rf1 (size : num) = [rf1_1]
End

Definition refute_cv_rnd_rf1_def:
  refute_cv_rnd_rf1 (size : num) state =
    let (n, state') = rand_below 1 state
    in (rf1_1, state')
End

Definition refute_cv_exh_rf2_def:
  refute_cv_exh_rf2 (size : num) = [rf2_1; rf2_2]
End

Definition refute_cv_rnd_rf2_def:
  refute_cv_rnd_rf2 (size : num) state =
    let (n, state') = rand_below 2 state
    in (if n = 0 then rf2_1 else rf2_2, state')
End

Definition refute_cv_exh_rf3_def:
  refute_cv_exh_rf3 (size : num) = [rf3_1; rf3_2; rf3_3]
End

Definition refute_cv_rnd_rf3_def:
  refute_cv_rnd_rf3 (size : num) state =
    let (n, state') = rand_below 3 state
    in
      (if n = 0 then rf3_1
       else if n = 1 then rf3_2
       else rf3_3,
       state')
End

Definition refute_cv_exh_rf4_def:
  refute_cv_exh_rf4 (size : num) = [rf4_1; rf4_2; rf4_3; rf4_4]
End

Definition refute_cv_rnd_rf4_def:
  refute_cv_rnd_rf4 (size : num) state =
    let (n, state') = rand_below 4 state
    in
      (if n = 0 then rf4_1
       else if n = 1 then rf4_2
       else if n = 2 then rf4_3
       else rf4_4,
       state')
End

Definition refute_cv_exh_rf5_def:
  refute_cv_exh_rf5 (size : num) =
    [rf5_1; rf5_2; rf5_3; rf5_4; rf5_5]
End

Definition refute_cv_rnd_rf5_def:
  refute_cv_rnd_rf5 (size : num) state =
    let (n, state') = rand_below 5 state
    in
      (if n = 0 then rf5_1
       else if n = 1 then rf5_2
       else if n = 2 then rf5_3
       else if n = 3 then rf5_4
       else rf5_5,
       state')
End

Definition refute_cv_exh_rf6_def:
  refute_cv_exh_rf6 (size : num) =
    [rf6_1; rf6_2; rf6_3; rf6_4; rf6_5; rf6_6]
End

Definition refute_cv_rnd_rf6_def:
  refute_cv_rnd_rf6 (size : num) state =
    let (n, state') = rand_below 6 state
    in
      (if n = 0 then rf6_1
       else if n = 1 then rf6_2
       else if n = 2 then rf6_3
       else if n = 3 then rf6_4
       else if n = 4 then rf6_5
       else rf6_6,
       state')
End

val _ = cv_trans refute_cv_char_range_def
val _ = cv_trans refute_cv_exh_char_def
val _ = cv_trans refute_cv_rnd_char_def
val _ = cv_trans refute_cv_exh_bool_def
val _ = cv_trans refute_cv_rnd_bool_def
val _ = cv_trans refute_cv_exh_rf1_def
val _ = cv_trans refute_cv_rnd_rf1_def
val _ = cv_trans refute_cv_exh_rf2_def
val _ = cv_trans refute_cv_rnd_rf2_def
val _ = cv_trans refute_cv_exh_rf3_def
val _ = cv_trans refute_cv_rnd_rf3_def
val _ = cv_trans refute_cv_exh_rf4_def
val _ = cv_trans refute_cv_rnd_rf4_def
val _ = cv_trans refute_cv_exh_rf5_def
val _ = cv_trans refute_cv_rnd_rf5_def
val _ = cv_trans refute_cv_exh_rf6_def
val _ = cv_trans refute_cv_rnd_rf6_def

(* Word generators.  word8 is a complete GenEnum at the M1 cap; wider
   words follow M1's size-bounded exhaustive order.  A word64 draw joins
   two high-to-low 32-bit draws because rand_below's bound is 2^32. *)
Definition refute_cv_word8_range_def:
  refute_cv_word8_range 0 acc = (0w : word8) :: acc /\
  refute_cv_word8_range (SUC n) acc =
    refute_cv_word8_range n ((n2w (SUC n) : word8) :: acc)
End

Definition refute_cv_exh_word8_def:
  refute_cv_exh_word8 (size : num) = refute_cv_word8_range 255 []
End

Definition refute_cv_rnd_word8_def:
  refute_cv_rnd_word8 (size : num) state =
    let (n, state') = rand_below 256 state
    in ((n2w n : word8), state')
End

Definition refute_cv_word16_range_def:
  refute_cv_word16_range 0 acc = (0w : word16) :: acc /\
  refute_cv_word16_range (SUC n) acc =
    refute_cv_word16_range n ((n2w (SUC n) : word16) :: acc)
End

Definition refute_cv_exh_word16_def:
  refute_cv_exh_word16 size =
    refute_cv_word16_range (MIN size 65535) []
End

Definition refute_cv_rnd_word16_def:
  refute_cv_rnd_word16 (size : num) state =
    let (n, state') = rand_below 65536 state
    in ((n2w n : word16), state')
End

Definition refute_cv_word32_range_def:
  refute_cv_word32_range 0 acc = (0w : word32) :: acc /\
  refute_cv_word32_range (SUC n) acc =
    refute_cv_word32_range n ((n2w (SUC n) : word32) :: acc)
End

Definition refute_cv_exh_word32_def:
  refute_cv_exh_word32 size =
    refute_cv_word32_range (MIN size 4294967295) []
End

Definition refute_cv_rnd_word32_def:
  refute_cv_rnd_word32 (size : num) state =
    let (n, state') = rand_below 4294967296 state
    in ((n2w n : word32), state')
End

Definition refute_cv_word64_range_def:
  refute_cv_word64_range 0 acc = (0w : word64) :: acc /\
  refute_cv_word64_range (SUC n) acc =
    refute_cv_word64_range n ((n2w (SUC n) : word64) :: acc)
End

Definition refute_cv_exh_word64_def:
  refute_cv_exh_word64 size =
    refute_cv_word64_range (MIN size 18446744073709551615) []
End

Definition refute_cv_rnd_word64_def:
  refute_cv_rnd_word64 (size : num) state =
    let (hi, state1) = rand_below 4294967296 state;
        (lo, state2) = rand_below 4294967296 state1
    in ((n2w (hi * 4294967296 + lo) : word64), state2)
End

val _ = cv_trans refute_cv_word8_range_def
val _ = cv_trans refute_cv_exh_word8_def
val _ = cv_trans refute_cv_rnd_word8_def
val _ = cv_trans refute_cv_word16_range_def
val _ = cv_trans refute_cv_exh_word16_def
val _ = cv_trans refute_cv_rnd_word16_def
val _ = cv_trans refute_cv_word32_range_def
val _ = cv_trans refute_cv_exh_word32_def
val _ = cv_trans refute_cv_rnd_word32_def
val _ = cv_trans refute_cv_word64_range_def
val _ = cv_trans refute_cv_exh_word64_def
val _ = cv_trans refute_cv_rnd_word64_def

(* num list: constructors and arguments follow M1's nested traversal order. *)
Definition refute_cv_prepend_num_def:
  refute_cv_prepend_num x ([] : num list list) = [] /\
  refute_cv_prepend_num x (xs :: xss) =
    (x :: xs) :: refute_cv_prepend_num x xss
End

Definition refute_cv_num_list_heads_def:
  refute_cv_num_list_heads x 0 tails =
    refute_cv_prepend_num x tails /\
  refute_cv_num_list_heads x (SUC n) tails =
    refute_cv_prepend_num x tails ++
      refute_cv_num_list_heads (SUC x) n tails
End

Definition refute_cv_exh_num_list_def:
  refute_cv_exh_num_list 0 = [] /\
  refute_cv_exh_num_list (SUC n) =
    [] :: refute_cv_num_list_heads 0 n (refute_cv_exh_num_list n)
End

Definition refute_cv_rnd_num_list_aux_def:
  (refute_cv_rnd_num_list_aux 0 size state =
     let (choice, state') = rand_below 1 state
     in ([], state')) /\
  (refute_cv_rnd_num_list_aux (SUC budget) size state =
     let (choice, state1) = rand_below (SUC budget + 1) state
     in
       if choice = 0 then ([], state1)
       else
         let (x, state2) = refute_cv_rnd_num size state1;
             (xs, state3) =
               refute_cv_rnd_num_list_aux budget size state2
         in (x :: xs, state3))
End

Definition refute_cv_rnd_num_list_def:
  refute_cv_rnd_num_list size state =
    refute_cv_rnd_num_list_aux size size state
End

val _ = cv_trans refute_cv_prepend_num_def
val _ = cv_trans refute_cv_num_list_heads_def
val _ = cv_trans refute_cv_exh_num_list_def
val _ = cv_trans refute_cv_rnd_num_list_aux_def
val _ = cv_trans refute_cv_rnd_num_list_def

(* The monomorphic product and option instances. *)
Definition refute_cv_num_pair_row_def:
  refute_cv_num_pair_row x 0 = [(x, 0)] /\
  refute_cv_num_pair_row x (SUC y) =
    refute_cv_num_pair_row x y ++ [(x, SUC y)]
End

Definition refute_cv_num_pair_square_def:
  refute_cv_num_pair_square 0 y = refute_cv_num_pair_row 0 y /\
  refute_cv_num_pair_square (SUC x) y =
    refute_cv_num_pair_square x y ++ refute_cv_num_pair_row (SUC x) y
End

Definition refute_cv_exh_num_pair_def:
  refute_cv_exh_num_pair 0 = [] /\
  refute_cv_exh_num_pair (SUC n) = refute_cv_num_pair_square n n
End

Definition refute_cv_rnd_num_pair_def:
  refute_cv_rnd_num_pair size state =
    let (choice, state1) = rand_below 1 state;
        (x, state2) = refute_cv_rnd_num size state1;
        (y, state3) = refute_cv_rnd_num size state2
    in ((x, y), state3)
End

Definition refute_cv_some_nums_def:
  refute_cv_some_nums 0 = [SOME 0] /\
  refute_cv_some_nums (SUC n) =
    refute_cv_some_nums n ++ [SOME (SUC n)]
End

Definition refute_cv_exh_num_option_def:
  refute_cv_exh_num_option 0 = [] /\
  refute_cv_exh_num_option (SUC n) = NONE :: refute_cv_some_nums n
End

Definition refute_cv_rnd_num_option_def:
  refute_cv_rnd_num_option size state =
    let (choice, state1) = rand_below 2 state
    in
      if choice = 0 then (NONE, state1)
      else
        let (x, state2) = refute_cv_rnd_num size state1
        in (SOME x, state2)
End

val _ = cv_trans refute_cv_num_pair_row_def
val _ = cv_trans refute_cv_num_pair_square_def
val _ = cv_trans refute_cv_exh_num_pair_def
val _ = cv_trans refute_cv_rnd_num_pair_def
val _ = cv_trans refute_cv_some_nums_def
val _ = cv_trans refute_cv_exh_num_option_def
val _ = cv_trans refute_cv_rnd_num_option_def

(* string is HOL's char list, so this pair is shared by both table entries. *)
Definition refute_cv_prepend_char_def:
  refute_cv_prepend_char c ([] : string list) = [] /\
  refute_cv_prepend_char c (s :: ss) =
    (c :: s) :: refute_cv_prepend_char c ss
End

Definition refute_cv_string_heads_def:
  refute_cv_string_heads 0 tails =
    refute_cv_prepend_char (CHR 0) tails /\
  refute_cv_string_heads (SUC n) tails =
    refute_cv_string_heads n tails ++
      refute_cv_prepend_char (CHR ((SUC n) MOD 256)) tails
End

Definition refute_cv_exh_string_def:
  refute_cv_exh_string 0 = [] /\
  refute_cv_exh_string (SUC n) =
    "" :: refute_cv_string_heads 255 (refute_cv_exh_string n)
End

Definition refute_cv_rnd_string_aux_def:
  (refute_cv_rnd_string_aux 0 size state =
     let (choice, state') = rand_below 1 state
     in ("", state')) /\
  (refute_cv_rnd_string_aux (SUC budget) size state =
     let (choice, state1) = rand_below (SUC budget + 1) state
     in
       if choice = 0 then ("", state1)
       else
         let (c, state2) = refute_cv_rnd_char size state1;
             (s, state3) = refute_cv_rnd_string_aux budget size state2
         in (c :: s, state3))
End

Definition refute_cv_rnd_string_def:
  refute_cv_rnd_string size state =
    refute_cv_rnd_string_aux size size state
End

val _ = cv_trans refute_cv_prepend_char_def
val _ = cv_trans refute_cv_string_heads_def
val _ = cv_trans refute_cv_exh_string_def
val _ = cv_trans refute_cv_rnd_string_aux_def
val _ = cv_trans refute_cv_rnd_string_def
