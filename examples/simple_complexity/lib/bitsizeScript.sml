(* ------------------------------------------------------------------------- *)
(* Bit Size for Numbers                                                      *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "bitsize";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib;

(* Get dependent theories in lib *)
(* val _ = load "helperFunctionTheory"; (* has helperNum, helperSet *) *)
(* val _ = load "helperListTheory"; *)
open pred_setTheory arithmeticTheory dividesTheory gcdTheory;
open helperNumTheory helperSetTheory helperListTheory helperFunctionTheory; (* for DIV_EQ_0 *)

(* open dependent theories *)
open listTheory rich_listTheory;

(* val _ = load "logPowerTheory"; *)
open logrootTheory logPowerTheory; (* for LOG_1, ulog *)


(* ------------------------------------------------------------------------- *)
(* Bit Size for Numbers Documentation                                        *)
(* ------------------------------------------------------------------------- *)
(* Type and Overload:
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Encoding and Decoding Binary Bits:
   decode_def            |- decode [] = 0 /\ !h t. decode (h::t) = h + TWICE (decode t)
   encode_def            |- encode 0 = [] /\ !n. encode (SUC n) = SUC n MOD 2::encode (HALF (SUC n))
   encode_eqn            |- !n. 0 < n ==> encode n = n MOD 2::encode (HALF n)
   encode_0              |- encode 0 = []
   encode_1              |- encode 1 = [1]
   encode_2              |- encode 2 = [0; 1]
   decode_encode_eq_id   |- !n. decode (encode n) = n
   decode_all_zero       |- !l. EVERY (\x. x = 0) l ==> (decode l = 0)
   decode_genlist_zero   |- !m. decode (GENLIST (K 0) m) = 0
   decode_nil            |- decode [] = 0
   decode_cons           |- !h t. decode (h::t) = h + TWICE (decode t)
   decode_sing           |- !x. decode [x] = x
   decode_snoc           |- !x l. decode (SNOC x l) = decode l + x * 2 ** LENGTH l

   Binary Representation:
   binary_def            |- !n. binary n = if n = 0 then [0] else encode n
   binary_0              |- binary 0 = [0]
   binary_1              |- binary 1 = [1]
   binary_length         |- !n. LENGTH (binary n) = if n = 0 then 1 else 1 + LOG2 n

   Size of Binary Representation:
   size_def              |- !n. size n = if n = 0 then 1 else if n = 1 then 1
                                         else SUC (size (HALF n))
   size_alt              |- !n. size n = if n <= 1 then 1 else 1 + size (HALF n)
#  size_pos              |- !n. 0 < size n
#  size_nonzero          |- !n. size n <> 0
   one_le_size           |- !n. 1 <= size n
#  size_0                |- size 0 = 1
#  size_1                |- size 1 = 1
#  size_2                |- size 2 = 2
   size_by_halves        |- !n. size n = if n = 0 then 1 else halves n
   size_by_LOG2          |- !n. size n = if n = 0 then 1 else 1 + LOG2 n
   size_ulog             |- !n. ulog n <= size n /\ size n <= 1 + ulog n
   size_le_ulog          |- !n. 1 < n ==> size n <= TWICE (ulog n)
   size_max_1_n          |- !n. size (MAX 1 n) = size n
   max_1_size_n          |- !n. size n = MAX 1 (size n)
   size_monotone_lt      |- !m n. m < n ==> size m <= size n
   size_monotone_le      |- !m n. m <= n ==> size m <= size n
   size_eq_1             |- !n. size n = 1 <=> n = 0 \/ n = 1
   size_mult_two_power   |- !n m. size (n * 2 ** m) = size n + if n = 0 then 0 else m
   size_twice            |- !n. size (TWICE n) = size n + if n = 0 then 0 else 1
   size_2_exp            |- !n. size (2 ** n) = 1 + n
   size_half_SUC         |- !n. 1 < n ==> SUC (size (HALF n)) = size n
   size_half             |- !n. 1 < n ==> size (HALF n) = size n - 1
   size_div_2_exp        |- !n k. size (n DIV 2 ** k) = if n < 2 ** k then 1 else size n - k
   size_exp              |- !n. n < 2 ** size n
   size_property         |- !n. 0 < n ==> n < 2 ** size n /\ 2 ** size n <= TWICE n
   size_property_alt     |- !n. n < 2 ** size n /\ 2 ** size n <= TWICE (MAX 1 n)
   size_unique           |- !n m. 2 ** m <= TWICE n /\ n < 2 ** m ==> size n = m
   size_thm              |- !n. 0 < n ==> !m. size n = m <=> 2 ** m <= TWICE n /\ n < 2 ** m
   size_eq_self          |- !n. (size n = n) <=> (n = 1) \/ (n = 2)
   size_le               |- !n. 0 < n ==> size n <= n
   size_lt               |- !n. 2 < n ==> size n < n
   size_le_self          |- !n. 0 < n ==> size n <= n
   size_size_le          |- !n. size (size n) <= size n
   size_by_ulog          |- !n. size n = if n = 0 \/ perfect_power n 2 then 1 + ulog n else ulog n
   size_by_ulog_alt      |- !n. size n = ulog n + if n = 0 \/ perfect_power n 2 then 1 else 0
   size_by_ulog_eqn      |- !n. size n = if n = 0 then 1 else ulog n + if perfect_power n 2 then 1 else 0
   ulog_by_size          |- !n. ulog n = if n = 0 \/ perfect_power n 2 then size n - 1 else size n
   ulog_by_size_alt      |- !n. ulog n = size n - if n = 0 \/ perfect_power n 2 then 1 else 0
   ulog_by_size_eqn      |- !n. ulog n = if n = 0 then 0 else size n - if perfect_power n 2 then 1 else 0
   halves_by_size        |- !n. halves n = if n = 0 then 0 else size n
   size_genlist_half     |- !k. 1 < k ==> GENLIST (\j. k DIV 2 ** j) (size k) =
                                          k::GENLIST (\j. HALF k DIV 2 ** j) (size (HALF k))
   size_genlist_twice    |- !n k. 1 < k ==> GENLIST (\j. n * 2 ** j) (size k) =
                                            n::GENLIST (\j. TWICE n * 2 ** j) (size (HALF k))
   size_genlist_square   |- !n k. 1 < k ==> GENLIST (\j. n ** 2 ** j) (size k) =
                                            n::GENLIST (\j. SQ n ** 2 ** j) (size (HALF k))
   size_genlist_select   |- !n k. 1 < k ==>
      GENLIST (\j. if EVEN (k DIV 2 ** j) then 0 else n * 2 ** j) (size k) =
      (if EVEN k then 0 else n)::
       GENLIST (\j. if EVEN (HALF k DIV 2 ** j) then 0 else TWICE n * 2 ** j) (size (HALF k))
   size_mult_two_power_upper
                      |- !m n. size (n * 2 ** m) <= size n + m
   size_add_upper     |- !m n. size (m + n) <= 1 + size (MAX m n)
   size_mult_upper    |- !m n. size (m * n) <= size m + size n
   size_sq_upper      |- !n. size (SQ n) <= TWICE (size n)
   size_upper         |- !n. size n <= 1 + n
   size_add1          |- !n. size (n + 1) <= 1 + size n
   size_gt_1          |- !n. 1 < n ==> 1 < size n
   size_max           |- !m n. size (MAX m n) = MAX (size m) (size n)
   size_min           |- !m n. size (MIN m n) = MIN (size m) (size n)
   size_exp_upper           |- !m n. size (m ** n) <= MAX 1 (n * size m)
   size_exp_upper_alt       |- !m n. 0 < n ==> size (m ** n) <= n * size m
   size_exp_two_power_upper |- !m n. size (n ** 2 ** size m) <= TWICE (MAX 1 m) * size n
   size_exp_two_power_le    |- !n m j. 0 < n /\ j < size n ==> size (m ** 2 ** j) <= n * size m
   size_exp_base_le         |- !n m b. m <= n ==> size (b ** m) <= size (b ** n)
   size_exp_exp_le          |- !a b n. a <= b ==> size (a ** n) <= size (b ** n)

   Encode to Fixed Binary Bits:
   to_bits_def           |- !n. to_bits n 0 = [] /\ !n m. to_bits n (SUC m) = n MOD 2::to_bits (HALF n) m
   to_bits_n_0           |- !n. to_bits n 0 = []
   to_bits_n_SUC         |- !n m. to_bits n (SUC m) = n MOD 2::to_bits (HALF n) m
   to_bits_snoc          |- !n m. to_bits n (SUC m) = SNOC ((n DIV 2 ** m) MOD 2) (to_bits n m)
   to_bits_0_m           |- !m. to_bits 0 m = GENLIST (K 0) m
   to_bits_n_m           |- !m n. to_bits n m = GENLIST (\j. (n DIV 2 ** j) MOD 2) m
   to_bits_length        |- !m n. LENGTH (to_bits n m) = m
   to_bits_element       |- !k m n. k < m ==> EL k (to_bits n m) = (n DIV 2 ** k) MOD 2
   decode_to_bits_eq_mod |- !m n. decode (to_bits n m) = n MOD 2 ** m

*)

(* Eliminate parenthesis around equality *)
val _ = ParseExtras.tight_equality();

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Encoding and Decoding Binary Bits                                         *)
(* ------------------------------------------------------------------------- *)

(* Decode a binary list *)
val decode_def = Define`
    (decode [] = 0) /\
    (decode (h::t) = h + 2 * decode t)
`;

(*
> EVAL ``decode [0; 1]``;
val it = |- decode [0; 1] = 2: thm
> EVAL ``decode [1; 1]``;
val it = |- decode [1; 1] = 3: thm
> EVAL ``decode [1; 1; 0]``;
val it = |- decode [1; 1; 0] = 3: thm
> EVAL ``decode [1; 1; 0; 1]``;
val it = |- decode [1; 1; 0; 1] = 11: thm
> EVAL ``decode [1; 1; 1; 0]``;
val it = |- decode [1; 1; 1; 0] = 7: thm
> EVAL ``decode [0]``;
val it = |- decode [0] = 0: thm
> EVAL ``decode [1]``;
val it = |- decode [1] = 1: thm
*)

(* Encode a number to a binary list *)
val encode_def = Define`
    (encode 0 = []) /\
    (encode (SUC n) = (SUC n) MOD 2 :: encode (HALF (SUC n)))
`;

(* Theorem: 0 < n ==> (encode n = n MOD 2 :: encode (HALF n)) *)
(* Proof:
   Note 0 < n means n <> 0      by NOT_ZERO_LT_ZERO
   Thus ?k. n = SUC k           by num_CASES
   The result follows           by encode_def
*)
val encode_eqn = store_thm(
  "encode_eqn",
  ``!n. 0 < n ==> (encode n = n MOD 2 :: encode (HALF n))``,
  metis_tac[encode_def, num_CASES, NOT_ZERO_LT_ZERO]);

(*
> EVAL ``encode 2``;
val it = |- encode 2 = [0; 1]: thm
> EVAL ``encode 3``;
val it = |- encode 3 = [1; 1]: thm
> EVAL ``encode 11``;
val it = |- encode 11 = [1; 1; 0; 1]: thm
> EVAL ``decode (encode 11)``;
val it = |- decode (encode 11) = 11: thm
> EVAL ``encode 1``;
val it = |- encode 1 = [1]: thm
> EVAL ``encode 0``;
val it = |- encode 0 = []: thm
*)

(* Extract theorems *)
val encode_0 = save_thm("encode_0", encode_def |> CONJUNCT1);
val encode_1 = save_thm("encode_1", encode_def |> CONJUNCT2 |> SPEC ``0`` |> SIMP_RULE arith_ss[encode_0]);
val encode_2 = save_thm("encode_2", encode_def |> CONJUNCT2 |> SPEC ``1`` |> SIMP_RULE arith_ss[encode_1]);

(*
val encode_0 = |- encode 0 = []: thm
val encode_1 = |- encode 1 = [1]: thm
val encode_2 = |- encode 2 = [0; 1]: thm
*)

(* Theorem: decode (encode n) = n *)
(* Proof:
   By complete induction on n.
   Base: n = 0 ==> decode (encode n) = n
           decode (encode 0)
         = decode []            by encode_def
         = 0                    by decode_def
   Step: !m. m < n ==> (decode (encode m) = m) ==>
         n <> 0 ==> decode (encode n) = n
      Note ?m. n = SUC m        by num_CASES
       and HALF n < n           by HALF_LT, 0 < n
           decode (encode n)
         = decode (n MOD 2::encode (HALF n))       by encode_def
         = n MOD 2 + 2 * decode (encode (HALF n))  by decode_def
         = n MOD 2 + 2 * (HALF n)                  by induction hypothesis
         = (HALF n) * 2 + (n MOD 2)                by arithmetic
         = n                                       by DIVISION
*)
val decode_encode_eq_id = store_thm(
  "decode_encode_eq_id",
  ``!n. decode (encode n) = n``,
  completeInduct_on `n` >>
  Cases_on `n = 0` >-
  rw_tac std_ss[encode_def, decode_def] >>
  `?m. n = SUC m` by metis_tac[num_CASES] >>
  `HALF n < n` by rw[HALF_LT] >>
  `decode (encode n) = decode (n MOD 2::encode (HALF n))` by rw[encode_def] >>
  `_ = n MOD 2 + 2 * decode (encode (HALF n))` by rw[decode_def] >>
  `_ = n MOD 2 + 2 * (HALF n)` by rw[] >>
  `_ = (HALF n) * 2 + (n MOD 2)` by rw[] >>
  `_ = n` by rw[DIVISION] >>
  rw[]);

(* Theorem: EVERY (\x. x = 0) l ==> (decode l = 0) *)
(* Proof:
   By induction on l.
   Base: decode [] = 0, true      by decode_def
   Step: EVERY (\x. x = 0) l ==> (decode l = 0) ==>
         !h. EVERY (\x. x = 0) (h::l) ==> (decode (h::l) = 0)
         EVERY (\x. x = 0) (h::l)
       = (h = 0) /\ EVERY (\x. x = 0) l   by EVERY_DEF
       = (h = 0) /\ (decode l = 0)        by induction hypothesis
       = (h + 2 * decode l = 0)           by arithmetic
       = (decode (h::l) = 0)              by decode_def
*)
val decode_all_zero = store_thm(
  "decode_all_zero",
  ``!l. EVERY (\x. x = 0) l ==> (decode l = 0)``,
  Induct >>
  rw[decode_def] >>
  rw[decode_def]);

(* Theorem: decode (GENLIST (K 0) m) = 0 *)
(* Proof:
   Note EVERY (\x. x = 0) (GENLIST (K 0) m)   by EVERY_GENLIST
    ==> decode (GENLIST (K 0) m) = 0          by decode_all_zero
*)
val decode_genlist_zero = store_thm(
  "decode_genlist_zero",
  ``!m. decode (GENLIST (K 0) m) = 0``,
  rw[decode_all_zero, EVERY_GENLIST]);

(* Extract theorems from definition *)
val decode_nil = save_thm("decode_nil", decode_def |> CONJUNCT1);
(* val decode_nil = |- decode [] = 0: thm *)

val decode_cons = save_thm("decode_cons", decode_def |> CONJUNCT2);
(* val decode_cons = |- !h t. decode (h::t) = h + TWICE (decode t): thm *)

(* Theorem: decode [x] = x *)
(* Proof: by decode_def *)
val decode_sing = store_thm(
  "decode_sing",
  ``!x. decode [x] = x``,
  rw_tac std_ss[decode_def]);

(*
> EVAL ``decode [0;0;1]``;
val it = |- decode [0; 0; 1] = 4: thm
> EVAL ``decode [0;0;1;1]``;
val it = |- decode [0; 0; 1; 1] = 12: thm
*)

(* Theorem: decode (SNOC x l) = decode l + x * 2 ** (LENGTH l) *)
(* Proof:
   By induction on l.
   Base: decode (SNOC x []) = decode [] + x * 2 ** LENGTH []
           decode (SNOC x [])
         = decode [x]            by SNOC_NIL
         = x                     by decode_sing
         = 0 + x * 1             by arithmetic
         = decode [] + x * 1                  by decode_nil
         = decode [] + x * 2 ** 0             by EXP_0
         = decode [] + x * 2 ** (LENGTH [])   by LENGTH_NIL
   Step: decode (SNOC x l) = decode l + x * 2 ** LENGTH l ==>
         !h. decode (SNOC x (h::l)) = decode (h::l) + x * 2 ** LENGTH (h::l)
           decode (SNOC x (h::l))
         = decode (h::SNOC x l)               by SNOC_CONS
         = h + 2 * decode (SNOC x l)          by decode_cons
         = h + 2 * (decode l + x * 2 ** LENGTH l)       by induction hypothesis
         = (h + 2 * decode l) + x * 2 * 2 ** LENGTH l   by arithmetic
         = decode (h::l) + x * 2 ** SUC (LENGTH l)      by decode_cons, EXP
         = decode (h::l) + x * 2 ** LENGTH (h::l)       by LENGTH
*)
val decode_snoc = store_thm(
  "decode_snoc",
  ``!x l. decode (SNOC x l) = decode l + x * 2 ** (LENGTH l)``,
  strip_tac >>
  Induct >-
  rw[decode_def] >>
  rw[decode_def, SNOC_CONS, EXP]);

(* ------------------------------------------------------------------------- *)
(* Binary Representation                                                     *)
(* ------------------------------------------------------------------------- *)

(* Correct binary list of a number *)
val binary_def = Define`
    binary n = if n = 0 then [0] else encode n
`;
(*
> EVAL ``binary 0``;
val it = |- binary 0 = [0]: thm
> EVAL ``binary 1``;
val it = |- binary 1 = [1]: thm
> EVAL ``binary 2``;
val it = |- binary 2 = [0; 1]: thm
> EVAL ``binary 3``;
val it = |- binary 3 = [1; 1]: thm
> EVAL ``binary 4``;
val it = |- binary 4 = [0; 0; 1]: thm
> EVAL ``binary 5``;
val it = |- binary 5 = [1; 0; 1]: thm
*)

val binary_0 = save_thm("binary_0", EVAL ``binary 0``);
(* val binary_0 = |- binary 0 = [0]: thm *)
val binary_1 = save_thm("binary_1", EVAL ``binary 1``);
(* val binary_1 = |- binary 1 = [1]: thm *)

(* Theorem: LENGTH (binary n) = if n = 0 then 1 else 1 + LOG2 n *)
(* Proof:
   If n = 0,
        LENGTH (binary 0)
      = LENGTH [0]         by binary_0
      = 1                  by LENGTH
   If n <> 0,
      By complete induction on n.
      Note 0 < n           by n <> 0
      Thus HALF n < n      by HALF_LT
      Let m = HALF n.

      If m = 0,
         Then n = 1           by HALF_EQ_0
           LENGTH (binary 1)
         = LENGTH [1]         by binary_1
         = 1                  by LENGTH
         = 1 + 0              by ADD_0
         = 1 + LOG2 1         by LOG2_1
      If m <> 0,
           LENGTH (binary n)
           LENGTH (encode n)             by binary_def
         = LENGTH (n MOD 2 :: encode m)  by encode_eqn, 0 < n
         = LENGTH (encode m) + 1         by LENGTH
         = LOG2 m + 1 + 1                by induction hypothesis, m < n
         = 1 + (1 + LOG2 m)              by arithmetic
         = 1 + LOG2 n                    by LOG_DIV
*)
val binary_length = store_thm(
  "binary_length",
  ``!n. LENGTH (binary n) = if n = 0 then 1 else 1 + LOG2 n``,
  rw[binary_def] >>
  completeInduct_on `n` >>
  rpt strip_tac >>
  `HALF n < n` by rw[HALF_LT] >>
  qabbrev_tac `m = HALF n` >>
  Cases_on `m = 0` >| [
    `n = 1` by metis_tac[HALF_EQ_0] >>
    simp[] >>
    rw[encode_1, LOG2_1],
    fs[encode_eqn, LOG_DIV, Abbr`m`]
  ]);

(* ------------------------------------------------------------------------- *)
(* Size of Binary Representation                                             *)
(* ------------------------------------------------------------------------- *)

(* Define number of bits of a number, recursively. *)
val size_def = Define`
    size n = if n = 0 then 1 else if n = 1 then 1 else SUC (size (HALF n))
`;
(* Both 0 and 1 needs no halving to count. *)

(*
> size_def |> SPEC_ALL |> SIMP_RULE (srw_ss()) [ADD1] |> GEN_ALL;
val it = |- !n. size n = if n = 0 then 1 else if n = 1 then 1 else size (HALF n) + 1: thm
*)

(* Theorem: size n = if n <= 1 then 1 else 1 + size (HALF n) *)
(* Proof: by size_def *)
val size_alt = store_thm(
  "size_alt",
  ``!n. size n = if n <= 1 then 1 else 1 + size (HALF n)``,
  rw[Once size_def]);

(* Theorem: 0 < size n *)
(* Proof: by size_def *)
val size_pos = store_thm(
  "size_pos[simp]",
  ``!n. 0 < size n``,
  rw[Once size_def]);

(* Theorem: size n <> 0 *)
(* Proof: by size_pos *)
val size_nonzero = store_thm(
  "size_nonzero[simp]",
  ``!n. size n <> 0``,
  metis_tac[size_pos, NOT_ZERO_LT_ZERO]);

(* Theorem: 1 <= size n *)
(* Proof: by size_pos *)
val one_le_size = store_thm(
  "one_le_size",
  ``!n. 1 <= size n``,
  metis_tac[size_nonzero, NOT_ZERO_GE_ONE]);

(* Extract theorems from definition *)
val size_0 = save_thm("size_0[simp]", size_def |> SPEC ``0`` |> SIMP_RULE arith_ss[]);
(* val size_0 = |- size 0 = 1: thm *)
val size_1 = save_thm("size_1[simp]", size_def |> SPEC ``1`` |> SIMP_RULE arith_ss[]);
(* val size_1 = |- size 1 = 1: thm *)
val size_2 = save_thm("size_2[simp]", size_def |> SPEC ``2`` |> SIMP_RULE arith_ss[size_1]);
(* val size_2 = |- size 2 = 2: thm *)

(* Note:
logPowerTheory.halves_def
|- !n. halves n = if n = 0 then 0 else SUC (halves (HALF n))
*)

(* Theorem: size n = if n = 0 then 1 else halves n *)
(* Proof:
   By complete induction on n.
   Base: size 0 = if 0 = 0 then 1 else halves 0
      Note size 0 = 1            by size_0
      Hence true.
   Step: n <> 0.
      If n = 1,
         LHS = size 1 = 1        by size_1
         RHS = halves 1 = 1      by halves_1
      If n <> 1,
          HALF n <> 0            by HALF_EQ_0, 1 < n
      and HALF n < n             by HALF_LT
         size n
       = SUC (size (HALF n))     by size_def, 1 < n
       = SUC (halves (HALF n))   by induction hypothesis
       = halves n                by halves_def
*)
val size_by_halves = store_thm(
  "size_by_halves",
  ``!n. size n = if n = 0 then 1 else halves n``,
  completeInduct_on `n` >>
  Cases_on `n = 0` >>
  rw[] >>
  Cases_on `HALF n = 0` >| [
    `n = 1` by fs[HALF_EQ_0] >>
    simp[halves_1],
    `HALF n < n` by rw[HALF_LT] >>
    `size n = SUC (size (HALF n))` by rw[Once size_def] >>
    `_ = SUC (halves (HALF n))` by rw[] >>
    `_ = halves n` by metis_tac[halves_def] >>
    decide_tac
  ]);

(* Theorem: size n = if n = 0 then 1 else 1 + LOG2 n *)
(* Proof:
   If n = 0,
      size 0 = 1           by size_1
   If n <> 0,
      size n = halves n    by size_by_halves
             = 1 + LOG2 n  by halves_by_LOG2
*)
val size_by_LOG2 = store_thm(
  "size_by_LOG2",
  ``!n. size n = if n = 0 then 1 else 1 + LOG2 n``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  simp[] >>
  simp[size_by_halves, halves_by_LOG2]);

(* Theorem: ulog n <= size n /\ size n <= 1 + ulog n *)
(* Proof:
   If n = 0,
      Note size 0 = 1             by size_0
       and ulog 0 = 0             by ulog_0
       and 0 <= 1 /\ 1 <= 1 + 0   by arithmetic
   If n <> 0, then 0 < n.
      Note size n = 1 + LOG2 n    by size_by_LOG2
       and LOG2 n <= ulog n /\
           ulog n <= 1 + LOG2 n   by ulog_LOG2, 0 < n
      Thus size n <= 1 + ulog n /\ ulog n <= size n.
*)
val size_ulog = store_thm(
  "size_ulog",
  ``!n. ulog n <= size n /\ size n <= 1 + ulog n``,
  strip_tac >>
  Cases_on `n = 0` >-
  rw[ulog_0] >>
  `size n = 1 + LOG2 n` by rw[size_by_LOG2] >>
  `0 < n` by decide_tac >>
  imp_res_tac ulog_LOG2 >>
  decide_tac);

(* Theorem: 1 < n ==> size n <= 2 * ulog n *)
(* Proof:
   size n <= 1 + ulog n        by size_ulog
          <= ulog n + ulog n   by ulog_ge_1
           = 2 * ulog n        by arithmetic
*)
val size_le_ulog = store_thm(
  "size_le_ulog",
  ``!n. 1 < n ==> size n <= 2 * ulog n``,
  rpt strip_tac >>
  `size n <= 1 + ulog n` by rw[size_ulog] >>
  `1 <= ulog n` by rw[ulog_ge_1] >>
  decide_tac);

(* Theorem: size (MAX 1 n) = size n *)
(* Proof:
   If n = 0,
      LHS = size (MAX 1 0) = size 1 = 1    by size_1
      RHS = size 0 = 1 = LHS               by size_0
   If n <> 0, then 1 <= n
      LHS = size (MAX 1 n) = size n        by MAX_DEF
*)
val size_max_1_n = store_thm(
  "size_max_1_n",
  ``!n. size (MAX 1 n) = size n``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[] >>
  `1 <= n` by decide_tac >>
  metis_tac[MAX_ALT]);

(* Theorem: size n = MAX 1 (size n) *)
(* Proof: by size_pos, MAX_1_POS *)
val max_1_size_n = store_thm(
  "max_1_size_n",
  ``!n. size n = MAX 1 (size n)``,
  rw[MAX_1_POS]);

(* Note: (size n) is almost (ulog n).
   In fact, (size n) = (ulog n) except when n is a power of 2, in which case (size n) = 1 + ulog n.
   This is because, the real-valued (log n) is talking about an exponent:  n = 2 ** (log n).
   The floor of the real-valued (log n) is (LOG2 n).
   The ceiling of the real-valued (log n) is (ulog n).
   When n is a power of 2, there is an exact exponent, so in this case: LOG2 n = log n = ulog n.
   Indeed, when n is a power of 2, ulog n = 1 + LOG2 n.
   For powers of 2, say, n = 8 = 2 ** 3, 3 bits can represent 8 binaries, from 000 to 111, or 0 to 7.
   The number 8 itself in binary is 1000, with 4 bits, 1 bit more than what the exponent indicates.
   The formula is: size n = 1 + LOG2 n, except when n = 0. Since 0 needs only 1 bit, size 0 = 1.

> EVAL ``GENLIST I 10``;
val it = |- GENLIST I 10            = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]: thm
> EVAL ``MAP ulog (GENLIST I 10)``;
val it = |- MAP ulog (GENLIST I 10) = [0; 0; 1; 2; 2; 3; 3; 3; 3; 4]: thm
> EVAL ``MAP size (GENLIST I 10)``;
val it = |- MAP size (GENLIST I 10) = [1; 1; 2; 2; 3; 3; 3; 3; 4; 4]: thm

> EVAL ``GENLIST SUC 10``;
val it = |- GENLIST SUC 10                    = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]: thm
> EVAL ``MAP LOG2 (GENLIST SUC 10)``;
val it = |- MAP (\n. LOG2 n) (GENLIST SUC 10) = [0; 1; 1; 2; 2; 2; 2; 3; 3; 3]: thm
> EVAL ``MAP ulog (GENLIST SUC 10)``;
val it = |- MAP ulog (GENLIST SUC 10)         = [0; 1; 2; 2; 3; 3; 3; 3; 4; 4]: thm
> EVAL ``MAP size (GENLIST SUC 10)``;
val it = |- MAP size (GENLIST SUC 10)         = [1; 2; 2; 3; 3; 3; 3; 4; 4; 4]: thm

*)

(* Theorem: m < n ==> size m <= size n *)
(* Proof:
   By size_by_LOG2, this is to show:
      m <> 0 /\ m < n ==> LOG2 m <= LOG2 n
   or  0 < m /\ m < n ==> LOG2 m <= LOG2 n      by NOT_ZERO_LT_ZERO
   which is true                                by LOG2_LT
*)
val size_monotone_lt = store_thm(
  "size_monotone_lt",
  ``!m n. m < n ==> size m <= size n``,
  rw[size_by_LOG2, LOG2_LT]);

(* Theorem: m <= n ==> size m <= size n *)
(* Proof:
   If m < n, this is true by size_monotone_lt
   If m = n, this is true trivially.
*)
val size_monotone_le = store_thm(
  "size_monotone_le",
  ``!m n. m <= n ==> size m <= size n``,
  rpt strip_tac >>
  `m < n \/ (m = n)` by decide_tac >-
  rw[size_monotone_lt] >>
  rw[]);

(* Theorem: size n = 1 <=> n = 0 \/ n = 1 *)
(* Proof:
   If part: size n = 1 ==> n = 0 \/ n = 1
      By contradiction, assume n <> 0 /\ n <> 1.
      Then         2 <= n             by n <> 0, n <> 1.
        so    size 2 <= size n        by size_monotone_le
        or         2 <= size n        by size_2
      This contradicts size n = 1.
    Only-if part: n = 0 \/ n = 1 ==> size n = 1
      True since size 0 = 1           by size_0
             and size 1 = 1           by size_1
*)
val size_eq_1 = store_thm(
  "size_eq_1",
  ``!n. size n = 1 <=> n = 0 \/ n = 1``,
  (rw[EQ_IMP_THM] >> simp[]) >>
  spose_not_then strip_assume_tac >>
  `2 <= n` by decide_tac >>
  `size 2 <= size n` by rw[size_monotone_le] >>
  `size 2 = 2` by rw[size_2] >>
  decide_tac);

(* Theorem: size (n * 2 ** m) = size n + (if n = 0 then 0 else m) *)
(* Proof:
   If n = 0,
     size (n * 2 ** m)
   = size 0                   by arithmetic
   = size 0 + 0               by ADD_0
   If n <> 0,
     size (n * 2 ** m)
   = if (n * 2 ** m = 0) then 1 else 1 + LOG2 (n * 2 ** m)   by size_by_LOG2
   = 1 + LOG2 (n * 2 ** m)    by EXP_EQ_0, n <> 0
   = 1 + (m + LOG2 n)         by LOG_EXP, 1 < 2, 0 < n
   = (1 + LOG2 n) + m         by arithmetic
   = size n + m               by size_by_LOG2
*)
val size_mult_two_power = store_thm(
  "size_mult_two_power",
  ``!n m. size (n * 2 ** m) = size n + (if n = 0 then 0 else m)``,
  rw[size_by_LOG2] >>
  `LOG2 (n * 2 ** m) = m + LOG2 n` by rw[GSYM LOG_EXP] >>
  rw[]);

(* Theorem: size (2 * n) = size n + if n = 0 then 0 else 1 *)
(* Proof: by size_mult_two_power *)
val size_twice = store_thm(
  "size_twice",
  ``!n. size (2 * n) = size n + if n = 0 then 0 else 1``,
  metis_tac[size_mult_two_power, EXP_1, MULT_RIGHT_1, MULT_COMM]);

(* Theorem: size (2 ** n) = 1 + n *)
(* Proof:
     size (2 ** n)
   = size (1 * 2 ** n)   by MULT_LEFT_1
   = size 1 + n          by size_mult_two_power
   = 1 + n               by size_1
*)
val size_2_exp = store_thm(
  "size_2_exp",
  ``!n. size (2 ** n) = 1 + n``,
  metis_tac[size_mult_two_power, size_1, MULT_LEFT_1, DECIDE``1 <> 0``]);

(* Theorem: 1 < n ==> SUC (size (HALF n)) = size n *)
(* Proof:
   Note 1 < n means n <> 0 /\ n <> 1    by arithmetic
   Thus size n = SUC (size (HALF n))    by size_def
*)
val size_half_SUC = store_thm(
  "size_half_SUC",
  ``!n. 1 < n ==> SUC (size (HALF n)) = size n``,
  rpt strip_tac >>
  `n <> 0 /\ n <> 1` by decide_tac >>
  metis_tac[size_def]);

(* Theorem: 1 < n ==> size (HALF n) = (size n) - 1 *)
(* Proof:
   Note size n = SUC (size (HALF n))   by size_half_SUC
               = 1 + size (HALF n)     by SUC_ONE_ADD
   Thus size (HALF n) = (size n) - 1   by arithmetic
*)
val size_half = store_thm(
  "size_half",
  ``!n. 1 < n ==> size (HALF n) = (size n) - 1``,
  rpt strip_tac >>
  `size n = 1 + size (HALF n)` by rw[GSYM size_half_SUC] >>
  decide_tac);

(* Theorem: size (n DIV (2 ** k)) = if n < 2 ** k then 1 else size n - k *)
(* Proof:
   By induction on k.
   Base: !n. size (n DIV 2 ** 0) = if n < 2 ** 0 then 1 else size n - 0
      LHS = size (n DIV 2 ** 0)
          = size (n DIV 1)                by EXP_0
          = size n                        by DIV_1
      RHS = if n < 1 then 1 else size n   by EXP_0
          = if n = 0 then 1 else size n   by arithmetic
      If n = 0, LHS = size 0 = 1 = RHS    by size_0
      If n <> 0, LHS = RHS.
   Step: !n. size (n DIV 2 ** k) = if n < 2 ** k then 1 else size n - k ==>
         !n. size (n DIV 2 ** SUC k) = if n < 2 ** SUC k then 1 else size n - SUC k
      If n < 2 ** SUC k,
         Then n DIV 2 ** SUC k = 0        by DIV_EQ_0
         LHS = size 0 = 1 = RHS           by size_0
      Otherwise, 2 ** SUC k <= n.
         Thus    2 * 2 ** k <= n          by EXP
           or        2 ** k <= HALF n     by arithmetic
         Also    1 < 2 ** SUC k           by ONE_LT_EXP
           so    1 < n                    by 2 ** SUC k <= n
         size (n DIV 2 ** SUC k)
       = size ((HALF n) DIV 2 ** k))      by HALF_DIV_TWO_POWER
       = if (HALF n) < 2 ** k then 1 else size (HALF n) - k  by induction hypothesis
       = size (HALF n) - k                by above, 2 ** k <= HALF n
       = (size n - 1) - k                 by size_half, 1 < n
       = size n - SUC k                   by ADD1
*)
val size_div_2_exp = store_thm(
  "size_div_2_exp",
  ``!n k. size (n DIV (2 ** k)) = if n < 2 ** k then 1 else size n - k``,
  Induct_on `k` >| [
    rw[] >>
    `n = 0` by decide_tac >>
    simp[],
    rpt strip_tac >>
    (Cases_on `n < 2 ** SUC k` >> simp[]) >| [
      `n DIV 2 ** SUC k = 0` by rw[DIV_EQ_0] >>
      simp[],
      `2 ** SUC k <= n` by decide_tac >>
      `HALF (2 ** SUC k) <= HALF n` by rw[DIV_LE_MONOTONE] >>
      `HALF (2 ** SUC k) = 2 ** k` by rw[EXP_2_HALF] >>
      `~(HALF n < 2 ** k)` by decide_tac >>
      `size (n DIV 2 ** SUC k) = size ((HALF n) DIV 2 ** k)` by rw[GSYM HALF_DIV_TWO_POWER] >>
      `_ = size (HALF n) - k` by rw[] >>
      `1 < 2 ** SUC k` by rw[ONE_LT_EXP] >>
      `1 < n` by decide_tac >>
      `size (HALF n) - k = (size n - 1) - k` by rw[size_half] >>
      decide_tac
    ]
  ]);

(* Theorem: n < 2 ** (size n) *)
(* Proof:
   If n = 0,
      RHS = 2 ** (size 0)
          = 2 ** 1             by size_0
          = 2 > 0              by EXP_1
   If n <> 0, then 0 < n.
      RHS = 2 ** (size n)
          = 2 ** (1 + LOG2 n)  by size_by_LOG2, n <> 0
          = 2 ** SUC (LOG2 n)  by SUC_ONE_ADD
          > n                  by LOG2_PROPERTY
*)
val size_exp = store_thm(
  "size_exp",
  ``!n. n < 2 ** (size n)``,
  rw[size_by_LOG2] >>
  simp[GSYM ADD1] >>
  rw[LOG2_PROPERTY]);

(* Theorem: n < 2 ** size n /\ 2 ** size n <= 2 * (MAX 1 n) *)
(* Proof:
   This is to show:
   (1) n < 2 ** size n, true   by size_exp
   (2) 2 ** size n <= TWICE n
         2 ** size n
       = 2 ** SUC (LOG2 n)     by size_by_LOG2, 0 < n
       = 2 * 2 ** LOG2 n       by EXP
       <= 2 * n                by LOG2_PROPERTY, 0 < n
*)
val size_property = store_thm(
  "size_property",
  ``!n. 0 < n ==> n < 2 ** size n /\ 2 ** size n <= 2 * n``,
  rpt strip_tac >-
  rw[size_exp] >>
  `2 ** size n = 2 ** SUC (LOG2 n)` by rw[size_by_LOG2] >>
  `_ = 2 * 2 ** LOG2 n` by rw[EXP] >>
  `2 * 2 ** LOG2 n <= 2 * n` by rw[LOG2_PROPERTY] >>
  decide_tac);

(* Theorem: n < 2 ** size n /\ 2 ** size n <= 2 * (MAX 1 n) *)
(* Proof:
   This is to show:
   (1) n < 2 ** size n, true         by size_exp
   (2) 2 ** size n <= 2 * (MAX 1 n)
       If n = 0,
          to show: 2 ** size 0 <= 2 * (MAX 1 0)
          LHS = 2 ** size 0
              = 2 ** 1               by size_0
              = 2                    by EXP_1
              = 2 * (MAX 1 0) = RHS  by MAX_DEF
       If n <> 0,
          to show: 2 ** size n <= 2 * (MAX 1 n)
          Note MAX 1 n = n           by MAX_DEF, 1 <= n
          Thus true                  by size_property
*)
val size_property_alt = store_thm(
  "size_property_alt",
  ``!n. n < 2 ** size n /\ 2 ** size n <= 2 * (MAX 1 n)``,
  rpt strip_tac >-
  rw[size_exp] >>
  Cases_on `n = 0` >-
  rw[] >>
  `1 <= n` by decide_tac >>
  `MAX 1 n = n` by rw[MAX_DEF] >>
  rw[size_property]);

(* Theorem: 2 ** m <= 2 * n /\ n < 2 ** m ==> (size n = m) *)
(* Proof:
   Note n <> 0, since 2 * n = 0           by 2 ** m <= 0 /\ 0 < 2 ** m is a contradiction.
   Thus m <> 0  since n < 1 means n = 0   by EXP_0
     so m = SUC k for some k              by num_CASES
        2 ** m = 2 ** SUC k
               = 2 * 2 ** k               by EXP
               <= 2 * n                   by given
        2 ** k <= n /\ n < 2 ** SUC k     by above
    ==> k = LOG2 n                        by LOG2_UNIQUE
   Thus m = 1 + k
          = 1 + LOG2 n
          = size n                        by size_by_LOG2, n <> 0
*)
val size_unique = store_thm(
  "size_unique",
  ``!n m. 2 ** m <= 2 * n /\ n < 2 ** m ==> (size n = m)``,
  rpt strip_tac >>
  `n <> 0` by metis_tac[MULT_0, NOT_LESS] >>
  `m <> 0` by metis_tac[EXP_0, DECIDE``n:num < 1 ==> (n = 0)``] >>
  `?k. m = SUC k` by metis_tac[num_CASES] >>
  `2 ** k <= n` by fs[EXP] >>
  `k = LOG2 n` by metis_tac[LOG2_UNIQUE] >>
  rw[size_by_LOG2]);

(* Theorem: 0 < n ==> !m. (size n = m) <=> (2 ** m <= TWICE n /\ n < 2 ** m) *)
(* Proof:
   If part: 0 < n ==> 2 ** size n <= TWICE n /\ n < 2 ** size n
      This is true by size_property.
   Only-if part: !n m. 2 ** m <= TWICE n /\ n < 2 ** m ==> size n = m
      This is true by size_unique.
*)
val size_thm = store_thm(
  "size_thm",
  ``!n. 0 < n ==> !m. (size n = m) <=> (2 ** m <= TWICE n /\ n < 2 ** m)``,
  metis_tac[size_property, size_unique]);

(* Theorem: size n = n <=> n = 1 \/ n = 2 *)
(* Proof:
   If part: size n = n ==> n = 1 \/ n = 2
      By contradiction, assume n <> 1 /\ n <> 2.
      Note n <> 0 since size 0 = 1     by size_0
        so ?k. n = SUC k               by num_CASES, n <> 0
      Thus 2 ** SUC k <= 2 * SUC k     by size_property
        or 2 * 2 ** k <= 2 * SUC k     by EXP
       ==>     2 ** k <= SUC k         by arithmetic
       But SUC k < 2 ** k              by SUC_X_LT_2_EXP_X, 1 < k
       This is a contradiction.
   Only-if part: size 1 = 1 /\ size 2 = 2
       This is true                    by size_1, size_2
*)
val size_eq_self = store_thm(
  "size_eq_self",
  ``!n. (size n = n) <=> ((n = 1) \/ (n = 2))``,
  rw_tac std_ss[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `n <> 0` by metis_tac[size_0, DECIDE``1 <> 0``] >>
    `2 < n` by decide_tac >>
    `?k. n = SUC k` by metis_tac[num_CASES] >>
    `1 < k /\ 0 < n` by decide_tac >>
    `2 * 2 ** k = 2 ** SUC k` by rw[EXP] >>
    `2 ** SUC k <= 2 * SUC k` by metis_tac[size_property] >>
    `2 ** k <= SUC k` by decide_tac >>
    `SUC k < 2 ** k` by rw[SUC_X_LT_2_EXP_X] >>
    decide_tac,
    rw[],
    rw[]
  ]);

(* Theorem: 0 < n ==> size n <= n *)
(* Proof:
   Note size n = 1 + LOG2 n   by size_by_LOG2, 0 < n
    and     LOG2 n < n        by LOG2_LT_SELF
     so 1 + LOG2 n <= n       by arithmetic
   Thus     size n <= n       by above
*)
val size_le = store_thm(
  "size_le",
  ``!n. 0 < n ==> size n <= n``,
  rpt strip_tac >>
  `size n = 1 + LOG2 n` by rw[size_by_LOG2] >>
  `LOG2 n < n` by rw[LOG2_LT_SELF] >>
  decide_tac);

(* Theorem: 2 < n ==> size n < n *)
(* Proof:
   By contradiction, assume ~(size n < n), or n <= size n.
   Note size n <= n           by size_le
     so size n = n            by EQ_LESS_EQ
    ==> n = 1 or n = 2        by size_eq_self
   This contradicts 2 < n.
*)
val size_lt = store_thm(
  "size_lt",
  ``!n. 2 < n ==> size n < n``,
  spose_not_then strip_assume_tac >>
  `size n <= n` by rw[size_le] >>
  `size n = n` by decide_tac >>
  fs[size_eq_self]);

(* Theorem: 0 < n ==> size n <= n *)
(* Proof:
     size n
   = 1 + LOG2 n       by size_by_LOG2, n <> 0
   < 1 + n            by LOG2_LT_SELF
   Thus size n <= n   by arithmetic
*)
val size_le_self = store_thm(
  "size_le_self",
  ``!n. 0 < n ==> size n <= n``,
  rpt strip_tac >>
  `size n = 1 + LOG2 n` by rw[size_by_LOG2] >>
  `1 + LOG2 n < 1 + n` by rw[LOG2_LT_SELF] >>
  decide_tac);

(* Theorem: size (size n) <= size n *)
(* Proof:
   If n = 0,
      LHS = size (size 0)
          = size 1 = 1        by size_0, size_1
          = size 0 = RHS      by size_0
   If n <> 0,
      Then size n <= n                by size_le_self
      Thus size (size n) <= size n    by size_monotone_le
*)
val size_size_le = store_thm(
  "size_size_le",
  ``!n. size (size n) <= size n``,
  rpt strip_tac >>
  (Cases_on `n = 0` >> simp[]) >>
  `size n <= n` by rw[size_le_self] >>
  rw[size_monotone_le]);

(*
> EVAL ``MAP size [1 .. 10]``;
val it = |- MAP size [1 .. 10] = [1; 2; 2; 3; 3; 3; 3; 4; 4; 4]: thm
> EVAL ``MAP ulog [1 .. 10]``;
val it = |- MAP ulog [1 .. 10] = [0; 1; 2; 2; 3; 3; 3; 3; 4; 4]: thm
diff:                             1  2     4           8
> EVAL ``MAP LOG2 [1 .. 10]``;
val it = |- MAP (\n. LOG2 n) [1 .. 10] = [0; 1; 1; 2; 2; 2; 2; 3; 3; 3]: thm
*)

(* Theorem: size n = if (n = 0 \/ perfect_power n 2) then 1 + ulog n else ulog n *)
(* Proof:
   If n = 0,
      Then size 0 = 1 + 0            by size_0
                  = 1 + ulog 0       by ulog_0
   If perfect_power n 2,
      Then size n
         = size (2 ** k) for some k  by perfect_power_def
         = 1 + k                     by size_2_exp
         = 1 + ulog (2 ** k)         by ulog_2_exp
         = 1 + ulog n                by n = 2 ** k
   Otherwise,
      Note 0 < n                     by n <> 0,
       and !e. n <> 2 ** e           by perfect_power_def
      Thus 2 ** ulog n < TWICE n /\
           n <= 2 ** ulog n          by ulog_property, 0 < n
        or 2 ** ulog n <= TWICE n /\
           n <  2 ** ulog n          by 2 ** ulog n <> n, take e = ulog n.
       ==> size = ulog n             by size_unique
*)
val size_by_ulog = store_thm(
  "size_by_ulog",
  ``!n. size n = if (n = 0 \/ perfect_power n 2) then 1 + ulog n else ulog n``,
  rw_tac std_ss[perfect_power_def] >-
  rw[ulog_0] >-
  rw[size_2_exp, ulog_2_exp] >>
  irule size_unique >>
  `0 < n` by metis_tac[NOT_ZERO_LT_ZERO] >>
  imp_res_tac ulog_property >>
  `n <> 2 ** ulog n` by metis_tac[] >>
  decide_tac);

(* Theorem: size n = ulog n + (if (n = 0) \/ perfect_power n 2 then 1 else 0) *)
(* Proof: by size_by_ulog *)
val size_by_ulog_alt = store_thm(
  "size_by_ulog_alt",
  ``!n. size n = ulog n + (if (n = 0) \/ perfect_power n 2 then 1 else 0)``,
  rw[size_by_ulog]);

(* Theorem: size n = if (n = 0) then 1 else ulog n + (if perfect_power n 2 then 1 else 0) *)
(* Proof: by size_by_ulog *)
val size_by_ulog_eqn = store_thm(
  "size_by_ulog_eqn",
  ``!n. size n = if (n = 0) then 1 else ulog n + (if perfect_power n 2 then 1 else 0)``,
  rpt strip_tac >>
  (Cases_on `n = 0` >> rw[size_by_ulog]));

(* Theorem: ulog n = if (n = 0) \/ perfect_power n 2 then size n - 1 else size n *)
(* Proof: by size_by_ulog *)
val ulog_by_size = store_thm(
  "ulog_by_size",
  ``!n. ulog n = if (n = 0) \/ perfect_power n 2 then size n - 1 else size n``,
  rw[size_by_ulog]);

(* Theorem: ulog n = size n - (if (n = 0) \/ perfect_power n 2 then 1 else 0) *)
(* Proof: by ulog_by_size *)
val ulog_by_size_alt = store_thm(
  "ulog_by_size_alt",
  ``!n. ulog n = size n - (if (n = 0) \/ perfect_power n 2 then 1 else 0)``,
  rw[ulog_by_size]);

(* Theorem: ulog n = if (n = 0) then 0 else size n - (if perfect_power n 2 then 1 else 0) *)
(* Proof: by ulog_by_size *)
val ulog_by_size_eqn = store_thm(
  "ulog_by_size_eqn",
  ``!n. ulog n = if (n = 0) then 0 else size n - (if perfect_power n 2 then 1 else 0)``,
  rpt strip_tac >>
  (Cases_on `n = 0` >> rw[ulog_by_size]));

(* Theorem: halves n = if n = 0 then 0 else size n *)
(* Proof:
   If n = 0,
      halves 0 = 0     by halves_0
   If n <> 0,
        halves n
      = size n         by size_by_halves, n <> 0
*)
val halves_by_size = store_thm(
  "halves_by_size",
  ``!n. halves n = if n = 0 then 0 else size n``,
  rpt strip_tac >>
  rw[halves_0] >>
  rw[size_by_halves]);

(* Theorem: 1 < k ==> GENLIST (\j. k DIV 2 ** j) (size k) =
            k :: GENLIST (\j. (HALF k) DIV 2 ** j) (size (HALF k)) *)
(* Proof:
   Let f = (\j. k DIV 2 ** j), h = HALF k.
   Then f 0 = k DIV 2 ** 0                      by notation
            = k DIV 1 = k                       by EXP_0, DIV_1
    and f o SUC = (\j. k DIV 2 ** (SUC j))      by notation
                = (\j. (HALF k) DIV 2 ** j)     by HALF_DIV_TWO_POWER
                = (\j. h DIV 2 ** j)            by notation
     GENLIST (\j. k DIV 2 ** j) (size k)
   = GENLIST f (size k)                         by notation
   = GENLIST f (SUC (size h))                   by size_half_SUC
   = f 0::GENLIST (f o SUC) (size h)            by GENLIST_CONS
   = k :: GENLIST (\j. h DIV 2 ** j) (size h)   by above, notation
*)
val size_genlist_half = store_thm(
  "size_genlist_half",
  ``!k. 1 < k ==> GENLIST (\j. k DIV 2 ** j) (size k) =
            k :: GENLIST (\j. (HALF k) DIV 2 ** j) (size (HALF k))``,
  rpt strip_tac >>
  qabbrev_tac `f = \j. k DIV 2 ** j` >>
  `f o SUC = \j. (HALF k) DIV 2 ** j` by
  (rw[FUN_EQ_THM, Abbr`f`] >>
  rw[HALF_DIV_TWO_POWER]) >>
  `f 0 = k` by rw[Abbr`f`] >>
  `GENLIST f (size k) = GENLIST f (SUC (size (HALF k)))` by rw[size_half_SUC] >>
  rw[GENLIST_CONS]);

(* Theorem: 1 < k ==> GENLIST (\j. n * 2 ** j) (size k) =
            n :: GENLIST (\j. 2 * n * 2 ** j) (size (HALF k)) *)
(* Proof:
   Let f = (\j. n * 2 ** j), h = HALF k.
   Then f 0 = n * 2 ** 0                      by notation
            = n * 1 = n                       by EXP_0, MULT_RIGHT_1
    and f o SUC = (\j. n * 2 ** (SUC j))      by notation
                = (\j. n * 2 * 2 ** j)        by EXP
                = (\j. 2 * n * 2 ** j)        by MULT_ASSOC
     GENLIST (\j. n * 2 ** j) (size k)
   = GENLIST f (size k)                         by notation
   = GENLIST f (SUC (size h))                   by size_half_SUC
   = f 0::GENLIST (f o SUC) (size h)            by GENLIST_CONS
   = n :: GENLIST (\j. 2 * n * 2 ** j) (size h) by above, notation
*)
val size_genlist_twice = store_thm(
  "size_genlist_twice",
  ``!n k. 1 < k ==> GENLIST (\j. n * 2 ** j) (size k) =
              n :: GENLIST (\j. 2 * n * 2 ** j) (size (HALF k))``,
  rpt strip_tac >>
  qabbrev_tac `f = \j. n * 2 ** j` >>
  `f o SUC = \j. 2 * n * 2 ** j` by
  (rw[FUN_EQ_THM, Abbr`f`] >>
  rw[EXP]) >>
  `f 0 = n` by rw[Abbr`f`] >>
  `GENLIST f (size k) = GENLIST f (SUC (size (HALF k)))` by rw[size_half_SUC] >>
  rw[GENLIST_CONS]);

(* Theorem: 1 < k ==> GENLIST (\j. n ** 2 ** j) (size k) =
                      n :: GENLIST (\j. (n * n) ** 2 ** j) (size (HALF k)) *)
(* Proof:
   Let f = (\j. n ** 2 ** j), h = HALF k.
   Then f 0 = n ** 2 ** 0                     by notation
            = n ** 1 = n                      by EXP_0, EXP_1
    and f o SUC = (\j. n ** 2 ** (SUC j))     by notation
                = (\j. (n ** 2) ** 2 ** j)    by EXP_EXP_SUC
                = (\j. (n * n) ** 2 ** j)     by EXP_2
     GENLIST (\j. n ** 2 ** j) (size k)
   = GENLIST f (size k)                                 by notation
   = GENLIST f (SUC (size h))                           by size_half_SUC
   = f 0::GENLIST (f o SUC) (size h)                    by GENLIST_CONS
   = n :: GENLIST (\j. (n * n) * n ** 2 ** j) (size h)  by above, notation
*)
val size_genlist_square = store_thm(
  "size_genlist_square",
  ``!n:num k. 1 < k ==> GENLIST (\j. n ** 2 ** j) (size k) =
                       n :: GENLIST (\j. (n * n) ** 2 ** j) (size (HALF k))``,
  rpt strip_tac >>
  qabbrev_tac `f = \j. n ** 2 ** j` >>
  `f o SUC = \j. (n * n) ** 2 ** j` by
  (rw[FUN_EQ_THM, Abbr`f`] >>
  rw[EXP_EXP_SUC]) >>
  `f 0 = n` by rw[Abbr`f`] >>
  `GENLIST f (size k) = GENLIST f (SUC (size (HALF k)))` by rw[size_half_SUC] >>
  rw[GENLIST_CONS]);

(* Theorem: 1 < k ==> GENLIST (\j. if EVEN (k DIV 2 ** j) then 0 else n * 2 ** j) (size k) =
            (if EVEN k then 0 else n) ::
            GENLIST (\j. if EVEN ((HALF k) DIV 2 ** j) then 0 else 2 * n * 2 ** j) (size (HALF k)) *)
(* Proof:
   Let f = (\j. if EVEN (k DIV 2 ** j) then 0 else n * 2 ** j), h = HALF k.
   Then f 0 = if EVEN (k DIV 2 ** 0) then 0 else n * 2 ** 0  by notation
            = if EVEN (k DIV 1) then 0 else n * 1            by EXP_0
            = if EVEN k then 0 else n           by DIV_1, MULT_RIGHT_1
    and f o SUC = (\j. if EVEN (k DIV 2 ** (SUC j)) then 0 else n * 2 ** (SUC j)) by notation
                = (\j. if EVEN ((HALF k) DIV 2 ** j) then 0 else n * 2 * 2 ** j)  by HALF_DIV_TWO_POWER, EXP
                = (\j. if EVEN (h DIV 2 ** j) then 0 else 2 * n * 2 ** j)         by MULT_ASSOC
     GENLIST (\j. if EVEN (k DIV 2 ** j) then 0 else n * 2 ** j) (size k)
   = GENLIST f (size k)                         by notation
   = GENLIST f (SUC (size h))                   by size_half_SUC
   = f 0::GENLIST (f o SUC) (size h)            by GENLIST_CONS
   = (if EVEN k then 0 else n) ::
     GENLIST (\j. if EVEN (h DIV 2 ** j) then 0 else 2 * n * 2 ** j) (size h) by above, notation
*)
val size_genlist_select = store_thm(
  "size_genlist_select",
  ``!n k. 1 < k ==> GENLIST (\j. if EVEN (k DIV 2 ** j) then 0 else n * 2 ** j) (size k) =
            (if EVEN k then 0 else n) ::
            GENLIST (\j. if EVEN ((HALF k) DIV 2 ** j) then 0 else 2 * n * 2 ** j) (size (HALF k))``,
  rpt strip_tac >>
  qabbrev_tac `f = \j. if EVEN (k DIV 2 ** j) then 0 else n * 2 ** j` >>
  `f o SUC = \j. if EVEN ((HALF k) DIV 2 ** j) then 0 else 2 * n * 2 ** j` by
  (rw[FUN_EQ_THM, Abbr`f`] >>
  rw[EXP, HALF_DIV_TWO_POWER]) >>
  `f 0 = if EVEN k then 0 else n` by rw[Abbr`f`] >>
  `GENLIST f (size k) = GENLIST f (SUC (size (HALF k)))` by rw[size_half_SUC] >>
  rw[GENLIST_CONS]);

(* Theorem: size (n * 2 ** m) <= size n + m *)
(* Proof: by size_mult_two_power *)
val size_mult_two_power_upper = store_thm(
  "size_mult_two_power_upper",
  ``!m n. size (n * 2 ** m) <= size n + m``,
  rw[size_mult_two_power]);

(* Theorem: size (m + n) <= 1 + size (MAX m n) *)
(* Proof:
   If m < n,
      Then MAX m n = n          by MAX_DEF
       and m + n <= 2 * n       by arithmetic
           size (m + n)
        <= size (2 * n)         by size_monotone_le
        <= 1 + size n           by size_twice
      Thus size (m + n) <= 1 + size n.
   Otherwise n <= m.
      Then MAX m n = m          by MAX_DEF
       and m + n <= 2 * m       by arithmetic
           size (m + n)
        <= size (2 * m)         by size_monotone_le
        <= 1 + size m           by size_twice
      Thus size (m + n) <= 1 + size m.
*)
val size_add_upper = store_thm(
  "size_add_upper",
  ``!m n. size (m + n) <= 1 + size (MAX m n)``,
  rpt strip_tac >>
  Cases_on `m < n` >| [
    `MAX m n = n` by rw[MAX_DEF] >>
    `m + n <= 2 * n` by rw[] >>
    `size (m + n) <= size (2 * n)` by rw[size_monotone_le] >>
    `size (2 * n) <= 1 + size n` by rw[size_twice] >>
    fs[],
    `MAX m n = m` by rw[MAX_DEF] >>
    `m + n <= 2 * m` by rw[] >>
    `size (m + n) <= size (2 * m)` by rw[size_monotone_le] >>
    `size (2 * m) <= 1 + size m` by rw[size_twice] >>
    fs[]
  ]);

(* Theorem: size (m * n) <= size m + size n *)
(* Proof:
   Note n < 2 ** size n            by size_exp
   Thus m * n <= m * 2 ** size n   by arithmetic
        size (m * n)
     <= size (m * 2 ** size n)     by size_monotone_le
     <= size m + size n            by size_mult_two_power_upper
*)
val size_mult_upper = store_thm(
  "size_mult_upper",
  ``!m n. size (m * n) <= size m + size n``,
  rpt strip_tac >>
  `n < 2 ** size n` by rw[size_exp] >>
  `m * n <= m * 2 ** size n` by rw[] >>
  `size (m * n) <= size (m * 2 ** size n)` by rw[size_monotone_le] >>
  `size (m * 2 ** size n) <= size m + size n` by rw[size_mult_two_power_upper] >>
  decide_tac);

(* Theorem: size (SQ n) <= 2 * size n *)
(* Proof:
      size (SQ n)
    = size (n * n)          by EXP_2
   <= (size n) + (size n)   by size_mult_upper
    = 2 * size n            by TIMES2
*)
val size_sq_upper = store_thm(
  "size_sq_upper",
  ``!n. size (SQ n) <= 2 * size n``,
  metis_tac[size_mult_upper, EXP_2, TIMES2]);

(* Theorem: size n <= 1 + n *)
(* Proof:
   Note n < 2 ** n      by X_LT_EXP_X, 1 < 2
        size n
     <= size (2 ** n)   by size_monotone_le
      = 1 + n           by size_2_exp
*)
val size_upper = store_thm(
  "size_upper",
  ``!n. size n <= 1 + n``,
  rpt strip_tac >>
  `n < 2 ** n` by rw[X_LT_EXP_X] >>
  `size n <= size (2 ** n)` by rw[size_monotone_le] >>
  rw[GSYM size_2_exp]);

(* Theorem: size (n + 1) <= 1 + size n *)
(* Proof:
      size (n + 1)
   <= 1 + size (MAX n 1)      by size_add_upper
   <= 1 +  size n             by size_max_1_n, MAX_COMM
*)
val size_add1 = store_thm(
  "size_add1",
  ``!n. size (n + 1) <= 1 + size n``,
  rpt strip_tac >>
  `size (n + 1) <= 1 + size (MAX n 1)` by rw[size_add_upper] >>
  `size (MAX n 1) = size n` by metis_tac[size_max_1_n, MAX_COMM] >>
  decide_tac);

(* Theorem: 1 < n ==> 1 < size n *)
(* Proof:
   Note size n <> 0       by size_nonzero
    and size n <> 1       by size_eq_1, n <> 0, n <> 1
   Thus 1 < size n        by arithmetic
*)
val size_gt_1 = store_thm(
  "size_gt_1",
  ``!n. 1 < n ==> 1 < size n``,
  rpt strip_tac >>
  `size n <> 0` by rw[] >>
  `size n <> 1` by rw[size_eq_1] >>
  decide_tac);

(* Theorem: size (MAX m n) = MAX (size m) (size n) *)
(* Proof: by MAX_SWAP, size_monotone_le *)
val size_max = store_thm(
  "size_max",
  ``!m n. size (MAX m n) = MAX (size m) (size n)``,
  rw[MAX_SWAP, size_monotone_le]);

(* Theorem: size (MIN m n) = MIN (size m) (size n) *)
(* Proof: by MIN_SWAP, size_monotone_le *)
val size_min = store_thm(
  "size_min",
  ``!m n. size (MIN m n) = MIN (size m) (size n)``,
  rw[MIN_SWAP, size_monotone_le]);

(* Theorem: size (m ** n) <= MAX 1 (n * size m) *)
(* Proof:
   By induction on n.
   Base: size (m ** 0) <= MAX 1 (0 * size m)
      LHS = size 1 = 1        by EXP_0, size_1
      RHS = MAX 1 0 = 1       by MULT, MAX_DEF
      Hence true.
   Step: size (m ** n) <= MAX 1 (n * size m) ==>
         size (m ** SUC n) <= MAX 1 (SUC n * size m)
      If n = 0,
         size (m ** SUC 0)
       = size m               by EXP_1
      <= MAX 1 (size m)       by MAX_IS_MAX
      If n <> 0,
      Note 0 < n * size m                      by size_pos, MULT_POS
        so 1 <= n * size m                     by arithmetic
      thus MAX 1 (n * size m) = n * size m     by MAX_1_POS
      also 0 < SUC n * size m                  by SUC_POS, size_pos, MULT_POS
      thus MAX 1 (SUC n * size m) = SUC n * size m
                                               by MAX_1_POS
         size (m ** SUC n)
       = size (m * m ** n)                     by EXP
      <= size m + size (m ** n)                by size_mult_upper
      <= size m + MAX 1 (n * size m)           by induction hypothesis
       = size m + n * size m                   by above
       = SUC n * size m                        by arithmetic
       = MAX 1 (SUC n * size m)                by above
*)
val size_exp_upper = store_thm(
  "size_exp_upper",
  ``!m n. size (m ** n) <= MAX 1 (n * size m)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[EXP_0] >>
  Cases_on `n = 0` >-
  simp[] >>
  `0 < n * size m /\ 0 < SUC n * size m` by rw[MULT_POS] >>
  `size (m ** SUC n) = size (m * m ** n)` by rw[EXP] >>
  `size (m * m ** n) <= size m + size (m ** n)` by rw[size_mult_upper] >>
  `size m + size (m ** n) <= size m + MAX 1 (n * size m)` by rw[] >>
  `size m + MAX 1 (n * size m) = size m + n * size m` by rw[MAX_1_POS] >>
  `_ = SUC n * size m` by rw[MULT] >>
  rw[MAX_1_POS]);

(* This upper bound seems not likely to be lowered:
val it = |- size 100 = 7: thm
val it = |- size (100 ** 2) = 14: thm
val it = |- size (100 ** 3) = 20: thm
val it = |- size (100 ** 4) = 27: thm
val it = |- size (100 ** 5) = 34: thm
*)

(* Theorem: 0 < n ==> size (m ** n) <= n * size m *)
(* Proof:
   Note 0 < size m           by size_pos
     so 0 < n * size m       by MULT_POS, 0 < n
     or 1 <= n * size m      by arithmetic
        size (m ** n)
     <= MAX 1 (n * size m)   by size_exp_upper
      = n * size m           by above, MAX_DEF
*)
val size_exp_upper_alt = store_thm(
  "size_exp_upper_alt",
  ``!m n. 0 < n ==> size (m ** n) <= n * size m``,
  rpt strip_tac >>
  `0 < n * size m` by rw[MULT_POS] >>
  `1 <= n * size m` by decide_tac >>
  `MAX 1 (n * size m) = n * size m` by rw[MAX_DEF] >>
  metis_tac[size_exp_upper]);

(* Theorem: size (n ** 2 ** size m) <= 2 * (MAX 1 m) * size n *)
(* Proof:
      size (n ** 2 ** size m)
   <= MAX 1 (2 ** size m * size n)   by size_exp_upper
    = 2 ** size m * size n           by EXP_POS, size_pos
   <= 2 * (MAX 1 m) * size n         by size_property_alt
*)
val size_exp_two_power_upper = store_thm(
  "size_exp_two_power_upper",
  ``!m n. size (n ** 2 ** size m) <= 2 * (MAX 1 m) * size n``,
  rpt strip_tac >>
  `size (n ** 2 ** size m) <= MAX 1 (2 ** size m * size n)` by rw[size_exp_upper] >>
  `0 < 2 ** size m * size n` by rw[MULT_POS] >>
  `MAX 1 (2 ** size m * size n) = 2 ** size m * size n` by rw[MAX_1_POS] >>
  `2 ** size m * size n <= 2 * (MAX 1 m) * size n` by rw[size_property_alt] >>
  decide_tac);

(* Theorem: 0 < n /\ j < size n ==> size (m ** 2 ** j) <= n * size m *)
(* Proof:
   Note      j <= size n - 1              by j < size n
     so 2 ** j <= 2 ** (size n - 1)       by EXP_BASE_LE_MONO, [1]
    But   2 * 2 ** (size n - 1)
        = 2 ** SUC (size n - 1)           by EXP
        = 2 ** size n                     by size_pos, 0 < size n
       <= 2 * n                           by size_property, 0 < n, [2]
     so   2 ** j <= n                     by arithmetic, [1] [2]
   Thus   size (m ** (2 ** j))
       <= 2 ** j * size m                 by size_exp_upper_alt
       <= n * size m                      by above, 2 ** j <= n.
*)
val size_exp_two_power_le = store_thm(
  "size_exp_two_power_le",
  ``!n m j. 0 < n /\ j < size n ==> size (m ** 2 ** j) <= n * size m``,
  rpt strip_tac >>
  `size (m ** 2 ** j) <= 2 ** j * size m` by rw[size_exp_upper_alt] >>
  `j <= size n - 1` by decide_tac >>
  `2 ** j <= 2 ** (size n - 1)` by rw[EXP_BASE_LE_MONO] >>
  `0 < size n` by rw[] >>
  `SUC (size n - 1) = size n` by decide_tac >>
  `2 * 2 ** (size n - 1) = 2 ** size n` by rw[GSYM EXP] >>
  `2 ** size n <= 2 * n` by rw[size_property] >>
  `2 ** j * size m <= n * size m` by rw[] >>
  decide_tac);

(* Theorem: m <= n ==> size (b ** m) <= size (b ** n) *)
(* Proof:
   If b = 0,
      Then b ** m = 0 or 1, so size (b ** m) = 1     by size_0, size_1
       and b ** n = 0 or 1, so size (b ** n) = 1     by size_0, size_1
       and 1 <= 1.
   If b <> 0,
      Then b ** m <= b ** n                          by EXP_BASE_LEQ_MONO_IMP
        so size (b ** m) <= size (b ** n)            by size_monotone_le
*)
val size_exp_base_le = store_thm(
  "size_exp_base_le",
  ``!n m b. m <= n ==> size (b ** m) <= size (b ** n)``,
  rpt strip_tac >>
  Cases_on `b = 0` >-
  rw[ZERO_EXP] >>
  `0 < b` by decide_tac >>
  `b ** m <= b ** n` by rw[EXP_BASE_LEQ_MONO_IMP] >>
  rw[size_monotone_le]);

(* Theorem: a <= b ==> size (a ** n) <= size (b ** n) *)
(* Proof:
   Note a ** n <= b ** n                 by EXP_EXP_LE_MONO
   Thus size (a ** n) <= size (b ** n)   by size_monotone_le
*)
val size_exp_exp_le = store_thm(
  "size_exp_exp_le",
  ``!a b n. a <= b ==> size (a ** n) <= size (b ** n)``,
  rw[EXP_EXP_LE_MONO, size_monotone_le]);

(* ------------------------------------------------------------------------- *)
(* Encode to Fixed Binary Bits                                               *)
(* ------------------------------------------------------------------------- *)

(* Encode a number to fix-bit binary *)
val to_bits_def = Define`
    (to_bits n 0 = []) /\
    (to_bits n (SUC m) = n MOD 2 :: to_bits (HALF n) m)
`;

(*
> EVAL ``to_bits 5 3``;
val it = |- to_bits 5 3 = [1; 0; 1]: thm
> EVAL ``to_bits 5 4``;
val it = |- to_bits 5 4 = [1; 0; 1; 0]: thm
> EVAL ``to_bits 5 2``;
val it = |- to_bits 5 2 = [1; 0]: thm
> EVAL ``to_bits 5 1``;
val it = |- to_bits 5 1 = [1]: thm
> EVAL ``decode (to_bits 5 4)``;
val it = |- decode (to_bits 5 4) = 5: thm
> EVAL ``decode (to_bits 5 2)``;
val it = |- decode (to_bits 5 2) = 1: thm
*)

(* Extract theorems from definition *)
val to_bits_n_0 = save_thm("to_bits_n_0", to_bits_def |> CONJUNCT1);
(* val to_bits_n_0 = |- !n. to_bits n 0 = []: thm *)

val to_bits_n_SUC = save_thm("to_bits_n_SUC", to_bits_def |> CONJUNCT2);
(* val to_bits_n_SUC = |- !n m. to_bits n (SUC m) = n MOD 2::to_bits (HALF n) m: thm *)

(* Theorem: to_bits n (SUC m) = SNOC ((n DIV (2 ** m)) MOD 2) (to_bits n m) *)
(* Proof:
   By induction on m.
   Base: !n. to_bits n (SUC 0) = SNOC ((n DIV 2 ** 0) MOD 2) (to_bits n 0)
          to_bits n (SUC 0)
        = n MOD 2::to_bits (HALF n) 0   by to_bits_n_SUC
        = [n MOD 2]                     by to_bits_n_0
          SNOC ((n DIV 2 ** 0) MOD 2) (to_bits n 0)
        = SNOC ((n DIV 2 ** 0) MOD 2) []             by to_bits_n_0
        = [(n DIV 1) MOD 2]             by SNOC
        = [n MOD 2]                     by DIV_ONE
   Step: !n. to_bits n (SUC m) = SNOC ((n DIV 2 ** m) MOD 2) (to_bits n m) ==>
         !n. to_bits n (SUC (SUC m)) = SNOC ((n DIV 2 ** SUC m) MOD 2) (to_bits n (SUC m))
          to_bits n (SUC (SUC m))
        = n MOD 2::to_bits (HALF n) (SUC m)                         by to_bits_n_SUC
        = n MOD 2::SNOC (((HALF n) DIV 2 ** m) MOD 2) (to_bits (HALF n) m)    by induction hypothesis
        = SNOC (((HALF n) DIV 2 ** m) MOD 2) (n MOD 2 :: to_bits (HALF n) m)  by SNOC_CONS
        = SNOC (((HALF n) DIV 2 ** m) MOD 2) (to_bits n (SUC m))    by to_bits_n_SUC
        = SNOC ((n DIV 2 ** SUC m) MOD 2) (to_bits n (SUC m))       by HALF_DIV_TWO_POWER
*)
val to_bits_snoc = store_thm(
  "to_bits_snoc",
  ``!n m. to_bits n (SUC m) = SNOC ((n DIV (2 ** m)) MOD 2) (to_bits n m)``,
  Induct_on `m` >-
  rw[to_bits_def] >>
  rpt strip_tac >>
  `to_bits n (SUC (SUC m)) = n MOD 2::to_bits (HALF n) (SUC m)` by rw[to_bits_n_SUC] >>
  `_ = n MOD 2::SNOC (((HALF n) DIV 2 ** m) MOD 2) (to_bits (HALF n) m)` by rw[] >>
  `_ = SNOC (((HALF n) DIV 2 ** m) MOD 2) (n MOD 2 :: to_bits (HALF n) m)` by rw[SNOC_CONS] >>
  `_ = SNOC (((HALF n) DIV 2 ** m) MOD 2) (to_bits n (SUC m))` by rw[GSYM to_bits_n_SUC] >>
  `_ = SNOC ((n DIV 2 ** SUC m) MOD 2) (to_bits n (SUC m))` by rw[HALF_DIV_TWO_POWER] >>
  rw[]);

(* Theorem: to_bits 0 m = GENLIST (K 0) m *)
(* Proof:
   By induction on m.
   Base: to_bits 0 0 = GENLIST (K 0) 0
         to_bits 0 0
       = []                by to_bits_def
       = GENLIST (K 0) 0   by GENLIST_0
   Step: to_bits 0 m = GENLIST (K 0) m ==> to_bits 0 (SUC m) = GENLIST (K 0) (SUC m)
         to_bits 0 (SUC m)
       = 0 MOD 2::to_bits (HALF 0) m    by to_bits_def
       = 0 :: to_bits 0 m               by ZERO_MOD, ZERO_DIV, 0 < 2
       = 0 :: (GENLIST K 0) m           by induction hypothesis
       = GENLIST (K 0) (SUC m)          by GENLIST_K_CONS
*)
val to_bits_0_m = store_thm(
  "to_bits_0_m",
  ``!m. to_bits 0 m = GENLIST (K 0) m``,
  Induct >-
  rw_tac std_ss[to_bits_def, GENLIST_0] >>
  rw_tac std_ss[to_bits_def, GENLIST_K_CONS]);

(*
> EVAL ``to_bits 7 0``;
val it = |- to_bits 7 0 = []: thm
> EVAL ``to_bits 7 1``;
val it = |- to_bits 7 1 = [1]: thm
> EVAL ``to_bits 7 2``;
val it = |- to_bits 7 2 = [1; 1]: thm
> EVAL ``to_bits 7 3``;
val it = |- to_bits 7 3 = [1; 1; 1]: thm
> EVAL ``to_bits 7 4``;
val it = |- to_bits 7 4 = [1; 1; 1; 0]: thm
*)

(* Theorem: to_bits n m = GENLIST (\j. (n DIV 2 ** j) MOD 2) m *)
(* Proof:
   By induction on m.
   Base: !n. to_bits n 0 = GENLIST (\j. (n DIV 2 ** j) MOD 2) 0
       Let f = \j. (n DIV 2 ** j) MOD 2.
         to_bits n 0
       = []                by to_bits_def
       = GENLIST f 0       by GENLIST_0
   Step: !n. to_bits n m = GENLIST (\j. (n DIV 2 ** j) MOD 2) m ==>
         !n. to_bits n (SUC m) = GENLIST (\j. (n DIV 2 ** j) MOD 2) (SUC m)
         Let f = \j. (n DIV 2 ** j) MOD 2.
         and f 0 = (n DIV 2 ** 0) MOD 2
                 = (n DIV 1) MOD 2                 by ONE
                 = n MOD 2                         by DIV_ONE
         to_bits n (SUC m)
       = n MOD 2::to_bits (HALF n) m               by to_bits_def
       = n MOD 2::GENLIST (\j. ((HALF n) DIV 2 ** j) MOD 2) m     by induction hypothesis
       = n MOD 2::GENLIST (\j. (n DIV (2 * 2 ** j)) MOD 2) m      by DIV_DIV_DIV_MULT
       = n MOD 2::GENLIST (\j. (n DIV (2 ** (SUC j))) MOD 2) m    by EXP
       = n MOD 2::GENLIST (f o SUC) m              by GENLIST_CONG, composition
       = f 0:: GENLIST (f o SUC) m                 by above
       = GENLIST f (SUC m)                         by GENLIST_CONS
*)
Theorem to_bits_n_m:
 !m n. to_bits n m = GENLIST (\j. (n DIV 2 ** j) MOD 2) m
Proof
  Induct >-
  rw[to_bits_def] >>
  rpt strip_tac >>
  qabbrev_tac `f = \j. (n DIV 2 ** j) MOD 2` >>
  `f 0 = n MOD 2` by rw[Abbr`f`] >>
  `to_bits n (SUC m) = n MOD 2::to_bits (HALF n) m` by rw[to_bits_def] >>
  `_ = n MOD 2::GENLIST (\j. ((HALF n) DIV 2 ** j) MOD 2) m` by rw[] >>
  `_ = n MOD 2::GENLIST (\j. (n DIV (2 * 2 ** j)) MOD 2) m` by rw[DIV_DIV_DIV_MULT] >>
  `_ = n MOD 2::GENLIST (\j. (n DIV (2 ** (SUC j))) MOD 2) m` by rw[GSYM EXP] >>
  `_ = n MOD 2::GENLIST (f o SUC) m` by rw[GENLIST_CONG, Abbr`f`] >>
  `_ = GENLIST f (SUC m)` by rw[GENLIST_CONS] >>
  rw[]
QED

(* Theorem: LENGTH (to_bits n m) = m *)
(* Proof:
   Let f = \j. (n DIV 2 ** j) MOD 2.
     LENGTH (to_bits n m)
   = LENGTH (GENLIST f m)   by to_bits_n_m
   = m                      by LENGTH_GENLIST
*)
val to_bits_length = store_thm(
  "to_bits_length",
  ``!m n. LENGTH (to_bits n m) = m``,
  rw_tac std_ss[to_bits_n_m, LENGTH_GENLIST]);

(* Theorem: k < m ==> (EL k (to_bits n m) = (n DIV (2 ** k)) MOD 2) *)
(* Proof:
   Let f = \j. (n DIV 2 ** j) MOD 2.
     EL k (to_bits n m)
   = EL k (GENLIST f m)      by to_bits_n_m
   = f k                     by EL_GENLIST, k < m
   = (n DIV 2 ** k) MOD 2    by notation
*)
val to_bits_element = store_thm(
  "to_bits_element",
  ``!k m n. k < m ==> (EL k (to_bits n m) = (n DIV (2 ** k)) MOD 2)``,
  rw_tac std_ss[to_bits_length, to_bits_n_m, EL_GENLIST]);

(* Theorem: decode (to_bits n m) = n MOD (2 ** m) *)
(* Proof:
   By complete induction on n.
   Base: n = 0 ==> decode (to_bits n m) = n MOD 2 ** m
           decode (to_bits 0 m)
         = decode (GENLIST (K 0) m)  by to_bits_0_m
         = 0                         by decode_genlist_zero
         = 0 MOD 2 ** m              by ZERO_MOD
   Step: !m. m < n ==> !m'. decode (to_bits m m') = m MOD 2 ** m' ==>
         n <> 0 ==> decode (to_bits n m) = n MOD 2 ** m
      If m = 0,
         to show: decode (to_bits n 0) = n MOD 2 ** 0
           decode (to_bits n 0)
         = decode []                 by to_bits_def
         = 0                         by decode_def
         = n MOD 1                   by MOD_ONE
         = n MOD (2 ** 0)            by EXP_0

      Otherwise, m <> 0,
      Note ?k. m = SUC k        by num_CASES
      Let h = 2 ** k.
      Note HALF n < n           by HALF_LT, 0 < n
       and 0 < h                by EXP_POS, 0 < 2
           decode (to_bits n m)
         = decode (to_bits n (SUC k))                    by m = SUC k
         = decode (n MOD 2 :: to_bits (HALF n) k)        by to_bits_def
         = n MOD 2 + 2 * (decode (to_bits (HALF n) k))   by decode_def
         = n MOD 2 + 2 * ((HALF n) MOD 2 ** k)           by induction hypothesis, HALF n < n
         = n MOD 2 + 2 * (HALF (n MOD (2 * h)))          by DIV_MOD_MOD_DIV
         = 2 * (HALF (n MOD (2 * h))) + n MOD 2          by ADD_COMM
         = 2 * (HALF (n MOD (2 * h))) + (n MOD (2 * h)) MOD 2  by MOD_MULT_MOD, 0 < h
         = HALF (n MOD (2 * h)) * 2 + (n MOD (2 * h)) MOD 2    by MULT_COMM
         = n MOD (2 * h)                                       by DIVISION
         = n MOD (2 * 2 ** k)                                  by h = 2 ** k
         = n MOD (2 ** m)                                      by EXP
*)
val decode_to_bits_eq_mod = store_thm(
  "decode_to_bits_eq_mod",
  ``!m n. decode (to_bits n m) = n MOD (2 ** m)``,
  completeInduct_on `n` >>
  Cases_on `n = 0` >-
  rw_tac std_ss[decode_genlist_zero, to_bits_0_m] >>
  rpt strip_tac >>
  Cases_on `m` >-
  rw[decode_def, to_bits_def] >>
  qabbrev_tac `m = SUC n'` >>
  qabbrev_tac `h = 2 ** n'` >>
  `HALF n < n` by rw[HALF_LT] >>
  `0 < h` by rw[EXP_POS, Abbr`h`] >>
  `decode (to_bits n m) = decode (n MOD 2 :: to_bits (HALF n) n')` by rw[to_bits_def, Abbr`m`] >>
  `_ = n MOD 2 + TWICE (decode (to_bits (HALF n) n'))` by rw[decode_def] >>
  `_ = n MOD 2 + TWICE ((HALF n) MOD 2 ** n')` by rw[] >>
  `_ = n MOD 2 + TWICE (HALF (n MOD (2 * h)))` by rw[DIV_MOD_MOD_DIV, Abbr`h`] >>
  `_ = TWICE (HALF (n MOD (2 * h))) + n MOD 2` by rw[] >>
  `_ = TWICE (HALF (n MOD (2 * h))) + (n MOD (2 * h)) MOD 2` by rw[MOD_MULT_MOD] >>
  `_ = HALF (n MOD (2 * h)) * 2 + (n MOD (2 * h)) MOD 2` by rw[] >>
  `_ = n MOD (2 * h)` by rw[DIVISION] >>
  `_ = n MOD 2 ** m` by rw[EXP, Abbr`m`] >>
  rw[]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
