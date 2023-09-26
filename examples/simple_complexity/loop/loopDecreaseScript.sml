(* ------------------------------------------------------------------------- *)
(* Loop Recurrence with Decreasing argument                                  *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "loopDecrease";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* Get dependent theories in lib *)
(* val _ = load "loopTheory"; *)
open loopTheory;

(* open dependent theories *)
open arithmeticTheory;
open dividesTheory;
open helperNumTheory helperListTheory helperFunctionTheory; (* for DIV_EQUAL_0 *)
open listTheory rich_listTheory;
open listRangeTheory;


(* ------------------------------------------------------------------------- *)
(* Loop Recurrence with Decreasing argument Documentation                    *)
(* ------------------------------------------------------------------------- *)
(* Type and Overload:
   decreasing       = decrease_by 1
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Decreasing Count:
   hop_def       |- !n b. hop b n = if b = 0 \/ n = 0 then 0 else SUC (hop b (n - b))
   hop_alt       |- !n b. hop b n = if b = 0 \/ n = 0 then 0 else 1 + hop b (n - b)
   hop_0         |- !b n. b = 0 \/ n = 0 ==> hop b n = 0
   hop_suc       |- !b n. 0 < b /\ 0 < n ==> hop b n = SUC (hop b (n - b))
   hop_zero      |- !b n. hop b 0 = 0 /\ hop 0 n = 0
   hop_nonzero   |- !b n. 0 < b /\ 0 < n ==> hop b n = 1 + hop b (n - b)
   hop_pos       |- !b n. 0 < b /\ 0 < n ==> 0 < hop b n
   hop_property  |- !b n. 0 < b /\ 0 < n ==> !j. b * j < n <=> j < hop b n
   hop_exceeds   |- !b n. 0 < b ==> n <= b * hop b n
   hop_eqn       |- !b n. hop b n = if b = 0 then 0 else n DIV b + if n MOD b = 0 then 0 else 1
   hop_DIV       |- !b n. hop b n <= 1 + n DIV b
   hop_1_n       |- !n. hop 1 n = n
   hop_eq_loop_count
                 |- !b x. 0 < b ==> hop b x = loop_count (\x. x = 0) (\x. x - b) x
   hop_eq_loop2_count
                 |- !b f x y. 0 < b ==> hop b y = loop2_count (\x y. y = 0) (\y. y - b) f x y
   decrease_falling        |- !b. FALLING (\x. x - b)
   iterating_dec_eqn       |- !b n x. FUNPOW (\x. x - b) n x = x - n * b
   iterating_dec_hop       |- !b x. 0 < b ==> FUNPOW (\x. x - b) (hop b x) x = 0
   iterating_dec_hop_alt   |- !b x. 0 < b ==> x <= hop b x * b

   Decrease Loop:
   loop_dec_count_eqn      |- !loop body b c. 0 < b /\
                              (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
                               !x. loop x = c + SUM (GENLIST (\j. body (x - j * b)) (hop b x))
   loop_dec_count_exit_sum_le
                           |- !loop body exit b c. 0 < b /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x - b)) ==>
                               !x. loop x <= c + SUM (GENLIST (\j. body (x - j * b)) (hop b x))
   loop_dec_count_cover_exit_le
                           |- !loop body cover exit b c. 0 < b /\
                              (!x. body x <= cover x) /\ MONO cover /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x - b)) ==>
                               !x. loop x <= c + hop b x * cover x
   loop_dec_count_exit_le  |- !loop body exit b c. 0 < b /\ MONO body /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x - b)) ==>
                               !x. loop x <= c + hop b x * body x
   loop_dec_count_cover_le |- !loop body cover b c. 0 < b /\
                              (!x. body x <= cover x) /\ MONO cover /\
                              (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
                               !x. loop x <= c + hop b x * cover x
   loop_dec_count_le       |- !loop body b c. 0 < b /\ MONO body /\
                              (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
                               !x. loop x <= c + hop b x * body x
   loop_dec_count_rcover_exit_le
                           |- !loop body cover exit b c. 0 < b /\
                              (!x. body x <= cover x) /\ RMONO cover /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x - b)) ==>
                               !x. loop x <= c + hop b x * cover 0
   loop_dec_count_rbody_exit_le
                           |- !loop body exit b c. 0 < b /\ RMONO body /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x - b)) ==>
                               !x. loop x <= c + hop b x * body 0
   loop_dec_count_rcover_le|- !loop body cover b c. 0 < b /\
                              (!x. body x <= cover x) /\ RMONO cover /\
                              (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
                               !x. loop x <= c + hop b x * cover 0
   loop_dec_count_rbody_le |- !loop body b c. 0 < b /\ RMONO body /\
                              (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
                               !x. loop x <= c + hop b x * body 0

   Decrease Loop with Transform:
   loop2_dec_count_eqn     |- !loop f body quit b. 0 < b /\
                              (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
                               !x y. loop x y = quit (FUNPOW f (hop b y) x) +
                                     SUM (GENLIST (\j. body (FUNPOW f j x) (y - j * b)) (hop b y))
   loop2_dec_count_sum_le  |- !loop f body quit exit b. 0 < b /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (hop b y) x) +
                                     SUM (GENLIST (\j. body (FUNPOW f j x) (y - j * b)) (hop b y))

   Decreasing Loop with Transform-independent Body:
   loop2_dec_count_mono_cover_exit_le
                   |- !loop f body quit cover exit b g. 0 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y =
                             if y = 0 then quit x
                             else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * g y
   loop2_dec_count_mono_exit_le
                   |- !loop f body quit exit b g. 0 < b /\ body = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y =
                             if y = 0 then quit x
                             else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * g y
   loop2_dec_count_mono_cover_le
                   |- !loop f body quit cover b g. 0 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * g y
   loop2_dec_count_mono_le
                   |- !loop f body quit b g. 0 < b /\ body = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * g y
   loop2_dec_count_rmono_cover_exit_le
                   |- !loop f body quit cover exit b g. 0 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y =
                             if y = 0 then quit x
                             else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * g 0
   loop2_dec_count_rmono_exit_le
                   |- !loop f body quit exit b g. 0 < b /\ body = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y =
                             if y = 0 then quit x
                             else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * g 0
   loop2_dec_count_rmono_cover_le
                   |- !loop f body quit cover b g. 0 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * g 0
   loop2_dec_count_rmono_le
                   |- !loop f body quit b g. 0 < b /\ body = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * g 0

   Decreasing Loop with Numeric Transform:
   loop2_dec_rise_count_cover_exit_le
                           |- !loop f body quit cover exit b. 0 < b /\
                              (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (hop b y) x) +
                                                 hop b y * cover (FUNPOW f (hop b y) x) y
   loop2_dec_rise_count_exit_le
                           |- !loop f body quit exit b. 0 < b /\ MONO2 body /\ RISING f /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (hop b y) x) +
                                                 hop b y * body (FUNPOW f (hop b y) x) y
   loop2_dec_rise_count_cover_le
                           |- !loop f body quit cover b. 0 < b /\
                              (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
                              (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (hop b y) x) +
                                                 hop b y * cover (FUNPOW f (hop b y) x) y
   loop2_dec_rise_count_le |- !loop f body quit b. 0 < b /\ MONO2 body /\ RISING f /\
                              (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (hop b y) x) +
                                                 hop b y * body (FUNPOW f (hop b y) x) y
   loop2_dec_fall_count_cover_exit_le
                           |- !loop f body quit cover exit b. 0 < b /\
                              (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * cover x y
   loop2_dec_fall_count_exit_le
                           |- !loop f body quit exit b. 0 < b /\ MONO2 body /\ FALLING f /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * body x y
   loop2_dec_fall_count_cover_le
                           |- !loop f body quit cover b. 0 < b /\
                              (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
                              (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * cover x y
   loop2_dec_fall_count_le |- !loop f body quit b. 0 < b /\ MONO2 body /\ FALLING f /\
                              (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * body x y

   Decreasing Loop with Transform cover:
   loop2_dec_mono_count_cover_exit_le
                           |- !loop f g body quit cover exit b. 0 < b /\
                              (!x y. body x y <= cover x y) /\ MONO2 cover /\
                              (!x. f x <= g x) /\ MONO g /\ RISING g /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (hop b y) x) +
                                                 hop b y * cover (FUNPOW g (hop b y) x) y
   loop2_dec_mono_count_exit_le
                           |- !loop f g body quit exit b. 0 < b /\ MONO2 body /\
                              (!x. f x <= g x) /\ MONO g /\ RISING g /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (hop b y) x) +
                                                 hop b y * body (FUNPOW g (hop b y) x) y
   loop2_dec_mono_count_cover_le
                           |- !loop f g body quit cover b. 0 < b /\
                              (!x y. body x y <= cover x y) /\ MONO2 cover /\
                              (!x. f x <= g x) /\ MONO g /\ RISING g /\
                              (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (hop b y) x) +
                                                 hop b y * cover (FUNPOW g (hop b y) x) y
   loop2_dec_mono_count_le |- !loop f g body quit b. 0 < b /\ MONO2 body /\
                              (!x. f x <= g x) /\ MONO g /\ RISING g /\
                              (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (hop b y) x) +
                                                 hop b y * body (FUNPOW g (hop b y) x) y

   Original:
   Decreasing List:
   decrease_by_def         |- !n b. decrease_by b n =
                                    if b = 0 \/ n = 0 then [] else n::decrease_by b (n - b)
   decrease_by_nil         |- !b n. b = 0 \/ n = 0 ==> decrease_by b n = []
   decrease_by_cons        |- !b n. 0 < b /\ 0 < n ==> decrease_by b n = n::decrease_by b (n - b)
   decrease_by_0_n         |- !n. decrease_by 0 n = []
   decrease_by_b_0         |- !b. decrease_by b 0 = []
   decrease_by_b_nonzero   |- !b n. 0 < b /\ n <> 0 ==> decrease_by b n = n::decrease_by b (n - b)
   decrease_by_eqn         |- !b n. decrease_by b n = GENLIST (\j. n - j * b) (hop b n)
   decrease_by_member      |- !b n j. 0 < b /\ 0 < n /\ j * b < n ==> MEM (n - j * b) (decrease_by b n)
   decrease_by_head        |- !b n. 0 < b /\ 0 < n ==> MEM n (decrease_by b n)
   decrease_by_length      |- !b n. LENGTH (decrease_by b n) = hop b n
   decrease_by_element     |- !b n j. j < hop b n ==> EL j (decrease_by b n) = n - j * b
   decreasing_length       |- !n. LENGTH (decreasing n) = n
   decreasing_eqn          |- !n. decreasing n = REVERSE [1 .. n]
   decrease_by_eq_loop_arg |- !b x. 0 < b ==> decrease_by b x = loop_arg (\x. x = 0) (\x. x - b) x
   iterating_decrease_eq_loop2_arg
                           |- !b body f x y. 0 < b ==>
                                 MAP2 body (iterating f x (hop b y)) (decrease_by b y) =
                                 MAP (UNCURRY body) (loop2_arg (\x y. y = 0) (\y. y - b) f x y)

   loop_dec_count_by_sum   |- !loop body b c. 0 < b /\
                              (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
                               !x. loop x = c + SUM (MAP body (decrease_by b x))
   loop_dec_count_exit_by_sum
                           |- !loop body b c exit. 0 < b /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x - b)) ==>
                               !x. loop x <= c + SUM (MAP body (decrease_by b x))
   loop_dec_count_cover_exit_upper
                           |- !loop body cover exit b c. 0 < b /\
                              (!x. body x <= cover x) /\ MONO cover /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x - b)) ==>
                               !x. loop x <= c + cover x * hop b x
   loop_dec_count_exit_upper
                           |- !loop body b c exit. 0 < b /\ MONO body /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x - b)) ==>
                               !x. loop x <= c + body x * hop b x
   loop_dec_count_cover_upper
                           |- !loop body b c cover. 0 < b /\
                              (!x. body x <= cover x) /\ MONO cover /\
                              (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
                               !x. loop x <= c + cover x * hop b x
   loop_dec_count_upper    |- !loop body b c. 0 < b /\ MONO body /\
                              (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
                               !x. loop x <= c + body x * hop b x

   loop2_dec_count_by_sum
                   |- !loop f body b c. 0 < b /\
                      (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y - b)) ==>
                       !x y. loop x y = c + SUM (MAP2 body (iterating f x (hop b y)) (decrease_by b y))
   loop2_dec_count_exit_by_sum
                   |- !loop f body b c exit. 0 < b /\
                      (!x y. loop x y =
                             if y = 0 then c
                             else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
                       !x y. loop x y <= c + SUM (MAP2 body (iterating f x (hop b y)) (decrease_by b y))
   loop2_dec_count_cover_exit_upper
                   |- !loop f body cover exit b c. 0 < b /\ (!x y. body x y <= cover x y) /\
                      (!x1 x2 y1 y2. y1 <= y2 ==> cover x1 y1 <= cover x2 y2) /\
                      (!x y. loop x y =
                             if y = 0 then c
                             else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
                       !x y. loop x y <= c + cover x y * hop b y
   loop2_dec_count_exit_upper
                   |- !loop f body exit b c. 0 < b /\
                      (!x1 x2 y1 y2. y1 <= y2 ==> body x1 y1 <= body x2 y2) /\
                      (!x y. loop x y =
                             if y = 0 then c
                             else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
                       !x y. loop x y <= c + body x y * hop b y
   loop2_dec_count_cover_upper
                   |- !loop f body cover b c. 0 < b /\ (!x y. body x y <= cover x y) /\
                      (!x1 x2 y1 y2. y1 <= y2 ==> cover x1 y1 <= cover x2 y2) /\
                      (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y - b)) ==>
                       !x y. loop x y <= c + cover x y * hop b y
   loop2_dec_count_upper
                   |- !loop f body b c. 0 < b /\
                      (!x1 x2 y1 y2. y1 <= y2 ==> body x1 y1 <= body x2 y2) /\
                      (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y - b)) ==>
                       !x y. loop x y <= c + body x y * hop b y
*)

(* ------------------------------------------------------------------------- *)
(* Loop Recurrence with Decreasing argument                                  *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Decreasing Count.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Define a hop function, count of hops to zero. *)
val hop_def = Define`
    hop b n = if (b = 0) \/ (n = 0) then 0 else SUC (hop b (n - b))
`;

(* alternate form *)
val hop_alt = save_thm("hop_alt", hop_def |> REWRITE_RULE [SUC_ONE_ADD]);
(* val hop_alt = |- !n b. hop b n = if b = 0 \/ n = 0 then 0 else 1 + hop b (n - b): thm *)

(* Theorem: ((b = 0) \/ (n = 0) ==> (hop b n = 0) *)
(* Proof: by hop_def *)
val hop_0 = store_thm(
  "hop_0",
  ``!b n. (b = 0) \/ (n = 0) ==> (hop b n = 0)``,
  rw[Once hop_def]);

(* Theorem: 0 < b /\ 0 < n ==> (hop b n = SUC (hop b (n - b))) *)
(* Proof: by hop_def *)
val hop_suc = store_thm(
  "hop_suc",
  ``!b n. 0 < b /\ 0 < n ==> (hop b n = SUC (hop b (n - b)))``,
  rw[Once hop_def]);

(* Theorem: (hop b 0 = 0) /\ (hop 0 n = 0) *)
(* Proof: by hop_def *)
val hop_zero = store_thm(
  "hop_zero",
  ``!b n. (hop b 0 = 0) /\ (hop 0 n = 0)``,
  rw[Once hop_def] >>
  rw[Once hop_def]);

(* Theorem: 0 < b /\ 0 < n ==> (hop b n = 1 + hop b (n - b)) *)
(* Proof: by hop_def *)
val hop_nonzero = store_thm(
  "hop_nonzero",
  ``!b n. 0 < b /\ 0 < n ==> (hop b n = 1 + hop b (n - b))``,
  rw[Once hop_def]);

(* Theorem: 0 < b /\ 0 < n ==> 0 < hop b n *)
(* Proof: by hop_def *)
val hop_pos = store_thm(
  "hop_pos",
  ``!b n. 0 < b /\ 0 < n ==> 0 < hop b n``,
  rw[Once hop_def]);

(* Theorem: 0 < b /\ 0 < n ==> !j. b * j < n <=> j < hop b n *)
(* Proof:
   By induction from hop_def.
   If n - b = 0,
      Then n <= b                  by SUB_EQ_0
       and hop b n = 1 + hop b 0   by hop_def
                   = 1 + 0 = 1     by hop_zero
      If j = 0, LHS = T = RHS      by hop_pos, 0 < b, 0 < n
      If j <> 0, LHS = F = RHS     by b <= b * j when j <> 0
   If n - b <> 0,
      Then 0 < n - b               by arithmetic
        so b * (j - 1) < n - b <=> j - 1 < hop b (n - b)
                                   by induction hypothesis
      If j = 0, LHS = T = RHS      by hop_pos, 0 < b, 0 < n
      If j <> 0,
         b * j - b < n - b <=> j < 1 + hop b (n - b)  by above
      or         b * j < n <=> j < hop b n            by hop_nonzero
*)
val hop_property = store_thm(
  "hop_property",
  ``!b n. 0 < b /\ 0 < n ==> !j. b * j < n <=> j < hop b n``,
  ho_match_mp_tac (theorem "hop_ind") >>
  rw[] >>
  Cases_on `n - b = 0` >| [
    `n <= b` by decide_tac >>
    (Cases_on `j = 0` >> simp[Once hop_def]) >>
    `b <= b * j` by rw[] >>
    rw[Once hop_def],
    `(j - 1) * b < n - b <=> j - 1 < hop b (n - b)` by rw[] >>
    (Cases_on `j = 0` >> simp[Once hop_def])
  ]);

(* Theorem: 0 < b ==> n <= b * hop b n *)
(* Proof:
   If n = 0, this is trivial.
   If n <> 0,
      Note     b * hop b n < n
           <=> hop b n < hop b n     by hop_property, 0 < n
           <=> F
      Thus n <= b * hop b n is true.
*)
val hop_exceeds = store_thm(
  "hop_exceeds",
  ``!b n. 0 < b ==> n <= b * hop b n``,
  rpt strip_tac >>
  (Cases_on `n = 0` >> simp[]) >>
  metis_tac[hop_property, LESS_EQ_REFL, NOT_LESS, NOT_ZERO]);


(*
val foo_def = Define`
    foo b n = if (b = 0) then 0 else (n DIV b + if n MOD b = 0 then 0 else 1)
`;

> EVAL ``MAP (hop 7) [1 .. 20]``; = [1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3]: thm
> EVAL ``MAP (foo 7) [1 .. 20]``; = [1; 1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 3; 3; 3; 3; 3; 3]: thm
*)

(* Theorem: hop b n = if (b = 0) then 0 else (n DIV b + if n MOD b = 0 then 0 else 1) *)
(* Proof:
   By complete induction on n.
   If b = 0, then hop 0 n = 0         by hop_def
   If n = 0,
      LHS = hop b 0 = 0               by hop_def
      RHS = 0 + 0 = 0 = LHS           by ZERO_DIV, ZERO_MOD
   Otherwise, b <> 0 and n <> 0.
   If n < b,
      Then n - b = 0                  by n < b
       LHS = hop b n
           = SUC (hop b (n - b))      by hop_def
           = SUC (hop b 0)            by n - b = 0
           = SUC 0 = 1                by hop_def, ADD1
       Now n MOD b = n <> 0           by LESS_MOD, n < b
       and n DIV b = 0                by LESS_DIV_EQ_ZERO, n < b
       RHS = 0 + 1 = 1 = LHS          by above
   If b <= n,
      Then b = n or b < n.
      If b = n,
       LHS = hop b n
           = SUC (hop b 0)            by hop_def
           = SUC 0 = 1                by hop_def, ADD1
       RHS = 1 + 0 = 1 = LHS          by DIVMOD_ID, 0 < b
      If b < n,
       LHS = hop b n
           = SUC (hop b (n - b))      by hop_def
           = SUC ((n - b) DIV b + if (n - b) MOD b = 0 then 0 else 1)
                                      by induction hypothesis
       But (n - b) DIV b = n DIV b - 1       by SUB_DIV, 0 < b, b <= n
       and (n - m) MOD b = n MOD b           by SUB_MOD, 0 < b, b <= n
       and n DIV b <> 0                      by DIV_EQUAL_0, 0 < b, ~(n < b)
       LHS = 1 + (n DIV b - 1 + if (n MOD b = 0) then 0 else 1)    by ADD1
           = n DIV m + (if (n MOD b = 0) then 0 else 1)            by n DIV b <> 0
           = RHS
*)
val hop_eqn = store_thm(
  "hop_eqn",
  ``!b n. hop b n = if (b = 0) then 0 else (n DIV b + if n MOD b = 0 then 0 else 1)``,
  strip_tac >>
  completeInduct_on `n` >>
  Cases_on `b = 0` >-
  rw[Once hop_def] >>
  fs[] >>
  Cases_on `n = 0` >| [
    `0 DIV b = 0` by rw[ZERO_DIV] >>
    `0 MOD b = 0` by rw[] >>
    rw[Once hop_def],
    Cases_on `n < b` >| [
      `n - b = 0` by decide_tac >>
      `n DIV b = 0` by rw[LESS_DIV_EQ_ZERO] >>
      `n MOD b = n` by rw[] >>
      `0 DIV b = 0` by rw[ZERO_DIV] >>
      rw[Once hop_def],
      `b <= n` by decide_tac >>
      `(n - b) DIV b = n DIV b - 1` by rw[SUB_DIV] >>
      `(n - b) MOD b = n MOD b` by rw[SUB_MOD] >>
      `n DIV b <> 0` by rw[DIV_EQUAL_0] >>
      rw[Once hop_def]
    ]
  ]);

(* Theorem: hop b n <= 1 + n DIV b *)
(* Proof: by hop_eqn *)
val hop_DIV = store_thm(
  "hop_DIV",
  ``!b n. hop b n <= 1 + n DIV b``,
  rw[hop_eqn]);

(* Theorem: hop 1 n = n *)
(* Proof:
     hop 1 n
   = n DIV 1 + if n MOD 1 = 0 then 0 else 1   by hop_eqn
   = n + if 0 = 0 then 0 else 1               by DIV_1, MOD_1
   = n
*)
val hop_1_n = store_thm(
  "hop_1_n",
  ``!n. hop 1 n = n``,
  rw[hop_eqn]);

(* Theorem: 0 < b ==> (hop b x = loop_count (\x. x = 0) (\x. x - b) x) *)
(* Proof:
   By induction from hop_def.
   Let guard = (\x. x = 0),
       modify = (\x. x - b),
       R = measure (\x. x).
   The goal is: hop b x = loop_count guard modify x

   Note WF R                               by WF_measure
    and !x. ~guard x ==> R (modify x) x    by x - b < x, 0 < b
   If guard x,
      Then x = 0                           by guard x
           hop b 0
         = 0                               by hop_0
         = loop_count guard modify 0       by loop_count_0, guard x
   If ~guard x,
      Then x <> 0                          by ~guard x
           hop b x
         = SUC (hop b (x - b))             by hop_suc
         = SUC (loop_count guard modify (x - b))
                                           by induction hypothesis
         = loop_count guard modify x       by loop_count_suc
*)
val hop_eq_loop_count = store_thm(
  "hop_eq_loop_count",
  ``!b x. 0 < b ==> (hop b x = loop_count (\x. x = 0) (\x. x - b) x)``,
  ho_match_mp_tac (theorem "hop_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x - b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`modify`, Abbr`R`] >>
  Cases_on `guard x` >| [
    `x = 0` by metis_tac[] >>
    metis_tac[hop_0, loop_count_0],
    `x <> 0` by metis_tac[] >>
    `hop b x = SUC (hop b (x - b))` by rw[hop_suc] >>
    `_ = SUC (loop_count guard modify (x - b))` by metis_tac[NOT_ZERO] >>
    `_ = loop_count guard modify x` by metis_tac[loop_count_suc] >>
    decide_tac
  ]);

(* Theorem: 0 < b ==> (hop b y = loop2_count (\x y. y = 0) (\y. y - b) f x y) *)
(* Proof:
   By induction from hop_def.
   Let guard = (\x y. y = 0),
       modify = (\y. y - b),
       R = measure (\(x,y). y).
   The goal is: hop b y = loop2_count guard modify f x y

   Note WF R                                         by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)  by y - b < y, 0 < b
   If guard x y,
      Then y = 0                             by guard x y
           hop b 0
         = 0                                 by hop_0
         = loop2_count guard modify f x 0    by loop2_count_0, guard x y
   If ~guard x y,
      Then y <> 0                            by ~guard x y
           hop b y
         = SUC (hop b (y - b))               by hop_suc
         = SUC (loop2_count guard modify f (f x) (y - b))
                                             by induction hypothesis, take (f x).
         = loop2_count guard modify f x y    by loop2_count_suc
*)
val hop_eq_loop2_count = store_thm(
  "hop_eq_loop2_count",
  ``!b f x y. 0 < b ==> (hop b y = loop2_count (\x y. y = 0) (\y. y - b) f x y)``,
  ntac 4 strip_tac >>
  qid_spec_tac `x` >>
  qid_spec_tac `y` >>
  qid_spec_tac `b` >>
  ho_match_mp_tac (theorem "hop_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x y. y = 0` >>
  qabbrev_tac `modify = \y. y - b` >>
  qabbrev_tac `R = measure (\(x,y). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`modify`, Abbr`R`] >>
  Cases_on `guard x y` >| [
    `y = 0` by metis_tac[] >>
    metis_tac[hop_0, loop2_count_0],
    `y <> 0` by metis_tac[] >>
    `hop b y = SUC (hop b (y - b))` by rw[hop_suc] >>
    `_ = SUC (loop2_count guard modify f (f x) (y - b))` by metis_tac[NOT_ZERO] >>
    `_ = loop2_count guard modify f x y` by metis_tac[loop2_count_suc] >>
    decide_tac
  ]);

(* Theorem: FALLING (\x. x - b) *)
(* Proof:
   By FALLING, this is to show: !x. x - b <= x, which is true.
*)
val decrease_falling = store_thm(
  "decrease_falling",
  ``!b. FALLING (\x. x - b)``,
  simp[]);

(* Theorem: FUNPOW (\x. x - b) n x = x - n * b *)
(* Proof:
   Let f = (\x. x - b).
   By induction on n.
   Base: !x. FUNPOW f 0 x = x - 0 * b
         FUNPOW f 0 x
       = x                 by FUNPOW_0
       = x - 0 * b         by arithmetic
   Step: !x. FUNPOW f n x = x - n * b ==>
         !x. FUNPOW f (SUC n) x = x - SUC n * b
         FUNPOW f (SUC n) x
       = f (FUNPOW f n x)   by FUNPOW_SUC
       = f (x - n * b)      by induction hypothesis
       = (x - n * b) - b    by function application
       = x - (SUC n) * b    by arithmetic, ADD1
*)
val iterating_dec_eqn = store_thm(
  "iterating_dec_eqn",
  ``!b n x. FUNPOW (\x. x - b) n x = x - n * b``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[FUNPOW_SUC, ADD1]);

(*
> EVAL ``MAP (\x. x - (hop 2 x) * 2) [1 .. 10]``; = [0; 0; 0; 0; 0; 0; 0; 0; 0; 0]: thm
> EVAL ``MAP (\x. x - (hop 3 x) * 3) [1 .. 10]``; = [0; 0; 0; 0; 0; 0; 0; 0; 0; 0]: thm
*)

(* Theorem: 0 < b ==> (FUNPOW (\x. x - b) (hop b x) x = 0) *)
(* Proof:
   Let guard = (\x. x = 0),
       modify = (\x. x - b),
       R = measure (\x. x).
   Then WF R                                   by WF_measure
    and !x. ~guard x ==> R (modify x) x        by x - b < x, 0 < b
   Note hop b x = loop_count guard modify x    by hop_eq_loop_count
    and guard (FUNPOW modify (loop_count guard modify x) x)   by loop_count_iterating
     or FUNPOW modify (loop_count guard modify x) x = 0       by guard
*)
val iterating_dec_hop = store_thm(
  "iterating_dec_hop",
  ``!b x. 0 < b ==> (FUNPOW (\x. x - b) (hop b x) x = 0)``,
  rw[hop_eq_loop_count] >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x - b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`modify`, Abbr`R`] >>
  metis_tac[loop_count_iterating]);

(* Theorem: 0 < b ==> x <= (hop b x) * b *)
(* Proof:
   Note FUNPOW (\x. x - b) (hop b x) x = 0     by iterating_dec_hop
     or              x - (hop b x) * b = 0     by iterating_dec_eqn
     or              x <= (hop b x) * b        by SUB_EQ_0
*)
val iterating_dec_hop_alt = store_thm(
  "iterating_dec_hop_alt",
  ``!b x. 0 < b ==> x <= (hop b x) * b``,
  metis_tac[iterating_dec_hop, iterating_dec_eqn, SUB_EQ_0]);

(* This is the same as hop_exceeds: |- !b n. 0 < b ==> n <= b * hop b n *)

(* ------------------------------------------------------------------------- *)
(* Decrease Loop                                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\
       (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
        !x. loop x = c + SUM (GENLIST (\j. body (x - j * b)) (hop b x)) *)
(* Proof:
   Let guard = (\x. x = 0),
       modify = (\x. x - b),
       R = measure (\x. x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by x - b < x, 0 < b
   Let quit = K c,
   Then !x. loop x = if guard x then quit x else body x + loop (modify x)
                                          by given
   Let f = (\j. body (FUNPOW modify j x)).
       z = FUNPOW modify (hop b x) x.
   Then f = (\j. body (x - j * b))        by iterating_dec_eqn, FUN_EQ_THM
    and z = x - (hop b x) * b             by iterating_dec_eqn
          = 0                             by iterating_dec_hop_alt
   Thus loop x
      = quit z + SUM (GENLIST f (loop_count guard modify x))  by loop_modify_count_eqn
      = c + SUM (GENLIST f (hop b x))                    by hop_eq_loop_count
      = c + SUM (GENLIST f (hop b x))                    by iterating_dec_hop_alt
*)
val loop_dec_count_eqn = store_thm(
  "loop_dec_count_eqn",
  ``!loop body b c. 0 < b /\
       (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
        !x. loop x = c + SUM (GENLIST (\j. body (x - j * b)) (hop b x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x - b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  qabbrev_tac `quit = \x:num. c` >>
  `!x. loop x = if guard x then quit x else body x + loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_eqn >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  `loop_count guard modify x = hop b x` by rw[hop_eq_loop_count, Abbr`guard`, Abbr`modify`] >>
  qabbrev_tac `f1 = \j. body (FUNPOW modify j x)` >>
  qabbrev_tac `f2 = \j. body (x - j * b)` >>
  `f1 = f2` by rw[FUN_EQ_THM, iterating_dec_eqn, Abbr`modify`, Abbr`f1`, Abbr`f2`] >>
  metis_tac[]);

(* Theorem: 0 < b /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
        !x. loop x <= c + SUM (GENLIST (\j. body (x - j * b)) (hop b x)) *)
(* Proof:
   Let guard = (\x. x = 0),
       modify = (\x. x - b),
       R = measure (\x. x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by x - b < x, 0 < b
   Let quit = K c,
   Then !x. loop x = if guard x then quit x else body x + loop (modify x)
                                          by given
   Let f = (\j. body (FUNPOW modify j x)).
       z = FUNPOW modify (hop b x) x.
   Then f = (\j. body (x - j * b))        by iterating_dec_eqn, FUN_EQ_THM
    and z = x - (hop b x) * b             by iterating_dec_eqn
          = 0                             by iterating_dec_hop_alt
   Thus  loop x
      <= quit z + SUM (GENLIST f (loop_count guard modify x))  by loop_modify_count_exit_le
       = c + SUM (GENLIST f (hop b x))                         by hop_eq_loop_count
*)
val loop_dec_count_exit_sum_le = store_thm(
  "loop_dec_count_exit_sum_le",
  ``!loop body exit b c. 0 < b /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
        !x. loop x <= c + SUM (GENLIST (\j. body (x - j * b)) (hop b x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x - b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  qabbrev_tac `quit = \x:num. c` >>
  `!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  `loop_count guard modify x = hop b x` by rw[hop_eq_loop_count, Abbr`guard`, Abbr`modify`] >>
  `quit (FUNPOW modify (loop_count guard modify x) x) = c` by rw[Abbr`quit`] >>
  qabbrev_tac `f1 = \j. body (FUNPOW modify j x)` >>
  qabbrev_tac `f2 = \j. body (x - j * b)` >>
  `f1 = f2` by rw[FUN_EQ_THM, iterating_dec_eqn, Abbr`modify`, Abbr`f1`, Abbr`f2`] >>
  metis_tac[]);

(* Theorem: 0 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
        !x. loop x <= c + hop b x * cover x *)
(* Proof:
   Let guard = (\x. x = 0),
       modify = (\x. x - b),
       R = measure (\x. x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by x - b < x, 0 < b
    and FALLIG modify                     by decrease_falling
   Let quit = K c,
   Then !x. loop x = if guard x then quit x else body x + loop (modify x)
                                          by given
   Let n = loop_count guard modify x,
       z = FUNPOW modify (hop b x) x.
       loop x
    <= quit z + n * cover x               by loop_fall_count_cover_exit_le, MONO cover
     = c + hop b x * cover x              by hop_eq_loop_count
*)
val loop_dec_count_cover_exit_le = store_thm(
  "loop_dec_count_cover_exit_le",
  ``!loop body cover exit b c. 0 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
        !x. loop x <= c + hop b x * cover x``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x - b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `FALLING modify` by rw[decrease_falling, Abbr`modify`] >>
  qabbrev_tac `quit = \x:num. c` >>
  `!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_fall_count_cover_exit_le >>
  first_x_assum (qspecl_then [`x`, `cover`] strip_assume_tac) >>
  `loop_count guard modify x = hop b x` by rw[hop_eq_loop_count, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Other similar theorems -- directly *)

(* Theorem: 0 < b /\ MONO body /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
        !x. loop x <= c + hop b x * body x *)
(* Proof: by loop_dec_count_cover_exit_le with cover = body. *)
val loop_dec_count_exit_le = store_thm(
  "loop_dec_count_exit_le",
  ``!loop body exit b c. 0 < b /\ MONO body /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
        !x. loop x <= c + hop b x * body x``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_dec_count_cover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem: 0 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
        !x. loop x <= c + hop b x * cover x *)
(* Proof: by loop_dec_count_cover_exit_le with exit = F. *)
val loop_dec_count_cover_le = store_thm(
  "loop_dec_count_cover_le",
  ``!loop body cover b c. 0 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
        !x. loop x <= c + hop b x * cover x``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num. F` >>
  `!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)` by metis_tac[] >>
  imp_res_tac loop_dec_count_cover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem: 0 < b /\ MONO body /\
       (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
        !x. loop x <= c + hop b x * body x *)
(* Proof: by loop_dec_count_cover_le with cover = body. *)
val loop_dec_count_le = store_thm(
  "loop_dec_count_le",
  ``!loop body cover b c. 0 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
        !x. loop x <= c + hop b x * cover x``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num. F` >>
  `!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)` by metis_tac[] >>
  imp_res_tac loop_dec_count_cover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
        !x. loop x <= c + hop b x * cover 0 *)
(* Proof:
   Let guard = (\x. x = 0),
       modify = (\x. x - b),
       R = measure (\x. x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by x - b < x, 0 < b
    and FALLING modify                    by decrease_falling
   Let quit = K c,
   Then !x. loop x = if guard x then quit x else body x + loop (modify x)
                                          by given

   Let n = loop_count guard modify x,
       z = FUNPOW modify n x.
       loop x
    <= quit z + n * cover (FUNPOW modify n x)    by loop_fall_count_rcover_exit_le, RMONO cover
     = c + n * cover (FUNPOW (\x. x - b) n x)    by notation
     = c + n * cover (x - n * b)                 by iterating_dec_eqn
     = c + hop b x * cover (x - hop b x * b)     by hop_eq_loop_count
     = c + hop b x * cover 0                     by hop_exceeds
*)
val loop_dec_count_rcover_exit_le = store_thm(
  "loop_dec_count_rcover_exit_le",
  ``!loop body cover exit b c. 0 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
        !x. loop x <= c + hop b x * cover 0``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x - b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `FALLING modify` by rw[decrease_falling, Abbr`modify`] >>
  qabbrev_tac `quit = \x:num. c` >>
  `!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_fall_count_rcover_exit_le >>
  first_x_assum (qspecl_then [`x`, `cover`] strip_assume_tac) >>
  `loop_count guard modify x = hop b x` by rw[hop_eq_loop_count, Abbr`guard`, Abbr`modify`] >>
  `loop x <= c + hop b x * cover (FUNPOW modify (hop b x) x)` by metis_tac[] >>
  `FUNPOW modify (hop b x) x = 0` by rw[GSYM iterating_dec_hop, Abbr`modify`] >>
  metis_tac[]);

(* Other similar theorems -- directly *)

(* Theorem: 0 < b /\ RMONO body /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
        !x. loop x <= c + hop b x * body 0 *)
(* Proof: by loop_dec_count_rcover_exit_le with cover = body. *)
val loop_dec_count_rbody_exit_le = store_thm(
  "loop_dec_count_rbody_exit_le",
  ``!loop body exit b c. 0 < b /\ RMONO body /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
        !x. loop x <= c + hop b x * body 0``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_dec_count_rcover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem: 0 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
        !x. loop x <= c + hop b x * cover 0 *)
(* Proof: by loop_dec_count_rcover_exit_le with exit = F. *)
val loop_dec_count_rcover_le = store_thm(
  "loop_dec_count_rcover_le",
  ``!loop body cover b c. 0 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
        !x. loop x <= c + hop b x * cover 0``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num. F` >>
  `!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)` by metis_tac[] >>
  imp_res_tac loop_dec_count_rcover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem:  0 < b /\ RMONO body /\
       (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
        !x. loop x <= c + hop b x * body 0*)
(* Proof: by loop_dec_count_rcover_le with cover = body. *)
val loop_dec_count_rbody_le = store_thm(
  "loop_dec_count_rbody_le",
  ``!loop body b c. 0 < b /\ RMONO body /\
       (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
        !x. loop x <= c + hop b x * body 0``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_dec_count_rcover_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Decrease Loop with Transform                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
     !x y. loop x y = quit (FUNPOW f (hop b y) x) +
                      SUM (GENLIST (\j. body (FUNPOW f j x) (y - j * b)) (hop b y)) *)
(* Proof:
   Let guard = (\x y. y = 0),
       modify = (\y. y - b),
       R = measure (\(x,y). y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by y - b < y, 0 < b
   Let quit2 = (\x y. quit x).
    and !x y. loop x y = if guard x y then quit2 x y else body x y + loop (f x) (modify y)
                                                        by given
   Let g = \j. body (FUNPOW f j x) (FUNPOW modify j y),
       n = loop2_count guard modify f x y,
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = hop b y                                by hop_eq_loop2_count
     so q = 0                                      by iterating_dec_hop
    and g = \j. body (FUNPOW f j x) (y - j * b)    by iterating_dec_eqn
        loop x y
      = quit2 p q + SUM (GENLIST g n)              by loop2_modify_count_eqn
      = quit p 0 + SUM (GENLIST g (hop b y))       by hop_eq_loop2_count
      = quit (FUNPOW f (hop b y) x) + SUM (GENLIST (\j. body (FUNPOW f j x) (y - j * b)) (hop b y))
*)
val loop2_dec_count_eqn = store_thm(
  "loop2_dec_count_eqn",
  ``!loop f body quit b. 0 < b /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
     !x y. loop x y = quit (FUNPOW f (hop b y) x) +
                      SUM (GENLIST (\j. body (FUNPOW f j x) (y - j * b)) (hop b y))``,
  rpt strip_tac >>
  imp_res_tac hop_eq_loop2_count >>
  first_x_assum (qspecl_then [`y`, `x`, `f`] strip_assume_tac) >>
  qabbrev_tac `guard = \x y. y = 0` >>
  qabbrev_tac `modify = \y. y - b` >>
  qabbrev_tac `R = measure (\(x,y). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  qabbrev_tac `quit2 = \x y:num. quit x` >>
  `!x y. loop x y = if guard x y then quit2 x y else body x y + loop (f x) (modify y)` by metis_tac[] >>
  imp_res_tac loop2_modify_count_eqn >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = loop2_count guard modify f x y` >>
  `n = hop b y` by rw[hop_eq_loop2_count, Abbr`n`] >>
  qabbrev_tac `u = \j. body (FUNPOW f j x) (FUNPOW modify j y)` >>
  qabbrev_tac `v = \j. body (FUNPOW f j x) (y - j * b)` >>
  `u = v` by rw[FUN_EQ_THM, iterating_dec_eqn, Abbr`modify`, Abbr`u`, Abbr`v`] >>
  metis_tac[]);

(* Theorem: 0 < b /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) +
                       SUM (GENLIST (\j. body (FUNPOW f j x) (y - j * b)) (hop b y)) *)
(* Proof:
   Let guard = (\x y. y = 0),
       modify = (\y. y - b),
       R = measure (\(x,y). y).
   Then WF R                                         by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)  by y - b < y, 0 < b
   Let quit2 = (\x y. quit x).
   Thus !x y. loop x y = if guard x y then quit2 x y else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                     by given
   Let g = \j. body (FUNPOW f j x) (FUNPOW modify j y),
       n = loop2_count guard modify f x y,
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = hop b y                                by hop_eq_loop2_count
     so q = 0                                      by iterating_dec_hop
    and g = \j. body (FUNPOW f j x) (y - j * b)    by iterating_dec_eqn
        loop x y
     <= quit2 p q + SUM (GENLIST g n)              by loop2_modify_count_exit_le
      = quit q + SUM (GENLIST g (hop b y))         by bop_eq_loop2_count
      = quit (FUNPOW f (hop b y) x) + SUM (GENLIST (\j. body (FUNPOW f j x) (y - j * b)) (hop b y))
*)
val loop2_dec_count_sum_le = store_thm(
  "loop2_dec_count_sum_le",
  ``!loop f body quit exit b. 0 < b /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) +
                       SUM (GENLIST (\j. body (FUNPOW f j x) (y - j * b)) (hop b y))``,
  rpt strip_tac >>
  imp_res_tac hop_eq_loop2_count >>
  first_x_assum (qspecl_then [`y`, `x`, `f`] strip_assume_tac) >>
  qabbrev_tac `guard = \x y. y = 0` >>
  qabbrev_tac `modify = \y. y - b` >>
  qabbrev_tac `R = measure (\(x,y). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  qabbrev_tac `quit2 = \x y:num. quit x` >>
  `!x y. loop x y = if guard x y then quit2 x y else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  imp_res_tac loop2_modify_count_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = loop2_count guard modify f x y` >>
  `n = hop b y` by rw[hop_eq_loop2_count, Abbr`n`] >>
  qabbrev_tac `u = \j. body (FUNPOW f j x) (FUNPOW modify j y)` >>
  qabbrev_tac `v = \j. body (FUNPOW f j x) (y - j * b)` >>
  `u = v` by rw[FUN_EQ_THM, iterating_dec_eqn, Abbr`modify`, Abbr`u`, Abbr`v`] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Decreasing Loop with Transform-independent Body                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g y *)
(* Proof:
   Let n = hop b y, z = FUNPOW f n x.
      loop x y
   <= quit z + SUM (GENLIST (\j. body (FUNPOW f j x) (y - j * b)) n)   by loop2_dec_count_sum_le
   <= quit z + SUM (GENLIST (\j. cover (FUNPOW f j x) (y - j * b)) n)  by SUM_LE, body cover
    = quit z + SUM (GENLIST (\j. g (y - j * b)) n)      by expanding cover
   <= quit z + SUM (GENLIST (K (g y)) n)                by SUM_LE, MONO g
    = quit z + g y * n                                  by SUM_GENLIST_K
    = quit z + n * g y                                  by MULT_COMM
*)
val loop2_dec_count_mono_cover_exit_le = store_thm(
  "loop2_dec_count_mono_cover_exit_le",
  ``!loop f body quit cover exit b g. 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g y``,
  rpt strip_tac >>
  imp_res_tac loop2_dec_count_sum_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = hop b y` >>
  `SUM (GENLIST (\j. body (FUNPOW f j x) (y - j * b)) n) <=
    SUM (GENLIST (\j. cover (FUNPOW f j x) (y - j * b)) n)` by fs[SUM_LE] >>
  `SUM (GENLIST (\j. cover (FUNPOW f j x) (y - j * b)) n) <= SUM (GENLIST (K (g y)) n)` by rw[SUM_LE] >>
  `SUM (GENLIST (K (g y)) n) = g y * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Other similar theorems -- directly *)

(* Theorem: 0 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g y *)
(* Proof: by loop2_dec_count_mono_cover_exit_le with cover = body. *)
val loop2_dec_count_mono_exit_le = store_thm(
  "loop2_dec_count_mono_exit_le",
  ``!loop f body quit exit b g. 0 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_dec_count_mono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g y *)
(* Proof: by loop2_dec_count_mono_cover_exit_le with exit = F. *)
val loop2_dec_count_mono_cover_le = store_thm(
  "loop2_dec_count_mono_cover_le",
  ``!loop f body quit cover b g. 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:'a y:num. F` >>
  `!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y - b)` by metis_tac[] >>
  imp_res_tac loop2_dec_count_mono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g y *)
(* Proof: by loop2_dec_count_mono_cover_le with cover = body. *)
val loop2_dec_count_mono_le = store_thm(
  "loop2_dec_count_mono_le",
  ``!loop f body quit b g. 0 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_dec_count_mono_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g 0 *)
(* Proof:
   Let n = hop b y, z = FUNPOW f n x.
      loop x y
   <= quit z + SUM (GENLIST (\j. body (FUNPOW f j x) (y - j * b)) n)   by loop2_dec_count_sum_le
   <= quit z + SUM (GENLIST (\j. cover (FUNPOW f j x) (y - j * b)) n)  by SUM_LE, body cover
    = quit z + SUM (GENLIST (\j. g (y - j * b)) n)      by expanding cover
   <= quit z + SUM (GENLIST (K (g 0)) n)                by SUM_LE, RMONO g
    = quit z + g 0 * n                                  by SUM_GENLIST_K
    = quit z + n * g 0                                  by MULT_COMM
*)
val loop2_dec_count_rmono_cover_exit_le = store_thm(
  "loop2_dec_count_rmono_cover_exit_le",
  ``!loop f body quit cover exit b g. 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g 0``,
  rpt strip_tac >>
  imp_res_tac loop2_dec_count_sum_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = hop b y` >>
  `SUM (GENLIST (\j. body (FUNPOW f j x) (y - j * b)) n) <=
    SUM (GENLIST (\j. cover (FUNPOW f j x) (y - j * b)) n)` by fs[SUM_LE] >>
  `SUM (GENLIST (\j. cover (FUNPOW f j x) (y - j * b)) n) <= SUM (GENLIST (K (g 0)) n)` by rw[SUM_LE] >>
  `SUM (GENLIST (K (g 0)) n) = g 0 * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Other similar theorems -- directly *)

(* Theorem: 0 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g 0 *)
(* Proof: by loop2_dec_count_rmono_cover_exit_le with cover = body. *)
val loop2_dec_count_rmono_exit_le = store_thm(
  "loop2_dec_count_rmono_exit_le",
  ``!loop f body quit exit b g. 0 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g 0``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_dec_count_rmono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g 0 *)
(* Proof: by loop2_dec_count_rmono_cover_exit_le with exit = F. *)
val loop2_dec_count_rmono_cover_le = store_thm(
  "loop2_dec_count_rmono_cover_le",
  ``!loop f body quit cover b g. 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g 0``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:'a y:num. F` >>
  `!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y - b)` by metis_tac[] >>
  imp_res_tac loop2_dec_count_rmono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g 0 *)
(* Proof: by loop2_dec_count_rmono_cover_le with cover = body. *)
val loop2_dec_count_rmono_le = store_thm(
  "loop2_dec_count_rmono_le",
  ``!loop f body quit b g. 0 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
     !x y. loop x y <= quit (FUNPOW f (hop b y) x) + (hop b y) * g 0``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_dec_count_rmono_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Decreasing Loop with Numeric Transform                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * cover (FUNPOW f (hop b y) x) y *)
(* Proof:
   Let guard = (\x y. y = 0),
       modify = (\y. y - b),
       R = measure (\(x,y). y).
   Then WF R                                            by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by y - b < y, 0 < b
   Let quit2 = (\x y. quit x).
   Then !x y. loop x y = if guard x y then quit2 x y else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                        by given
    and FALLING modify                                  by decrease_falling
   Let n = loop2_count guard modify f x y
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = hop b y                                     by hop_eq_loop2_count
     so q = 0                                           by iterating_dec_hop
        loop x y
     <= quit2 p q + n * cover (FUNPOW f n x) y          by loop2_rise_fall_count_cover_exit_le
      = quit (FUNPOW f (hop b y) x) + (hop b y) * cover (FUNPOW f (hop b y) x) y
*)
val loop2_dec_rise_count_cover_exit_le = store_thm(
  "loop2_dec_rise_count_cover_exit_le",
  ``!loop f body quit cover exit b.
          0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * cover (FUNPOW f (hop b y) x) y``,
  rpt strip_tac >>
  assume_tac (hop_eq_loop2_count |> ISPEC ``b:num`` |> ISPEC ``f:num -> num``) >>
  first_x_assum (qspecl_then [`x`, `y`] strip_assume_tac) >>
  qabbrev_tac `guard = \x:num y. y = 0` >>
  qabbrev_tac `modify = \y. y - b` >>
  qabbrev_tac `R = measure (\(x:num,y:num). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  qabbrev_tac `quit2 = \x y:num. quit x` >>
  `!x y. loop x y = if guard x y then quit2 x y else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  `FALLING modify` by rw[decrease_falling, Abbr`modify`] >>
  imp_res_tac loop2_rise_fall_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`, `cover`] strip_assume_tac) >>
  qabbrev_tac `n = loop2_count guard modify f x y` >>
  `n = hop b y` by rw[hop_eq_loop2_count, Abbr`n`] >>
  metis_tac[]);

(* Other similar theorems -- directly *)

(* Theorem: 0 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * body (FUNPOW f (hop b y) x) y *)
(* Proof: by loop2_dec_rise_count_cover_exit_le with cover = body. *)
val loop2_dec_rise_count_exit_le = store_thm(
  "loop2_dec_rise_count_exit_le",
  ``!loop f body quit exit b. 0 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * body (FUNPOW f (hop b y) x) y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_dec_rise_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * cover (FUNPOW f (hop b y) x) y *)
(* Proof: by loop2_dec_rise_count_cover_exit_le with exit = F. *)
val loop2_dec_rise_count_cover_le = store_thm(
  "loop2_dec_rise_count_cover_le",
  ``!loop f body quit cover b.
          0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * cover (FUNPOW f (hop b y) x) y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  `!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y - b)` by metis_tac[] >>
  imp_res_tac loop2_dec_rise_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * body (FUNPOW f (hop b y) x) y *)
(* Proof: by loop2_dec_rise_count_cover_le with cover = body. *)
val loop2_dec_rise_count_le = store_thm(
  "loop2_dec_rise_count_le",
  ``!loop f body quit b. 0 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * body (FUNPOW f (hop b y) x) y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_dec_rise_count_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * cover x y *)
(* Proof:
   Let guard = (\x y. y = 0),
       modify = (\y. y - b),
       R = measure (\(x,y). y).
   Then WF R                                            by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by y - b < y, 0 < b
   Let quit2 = (\x y. quit x).
   Then !x y. loop x y = if guard x y then quit2 x y else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                        by given
    and FALLING modify                                  by decrease_falling
   Let n = loop2_count guard modify f x y,
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = hop b y                                     by hop_eq_loop2_count
     so q = 0                                           by iterating_dec_hop
        loop x y
     <= quit2 p q + n * cover x y                       by loop2_fall_fall_count_cover_exit_le
      = quit (FUNPOW f (hop b y) x) + (hop b y) * cover x y
*)
val loop2_dec_fall_count_cover_exit_le = store_thm(
  "loop2_dec_fall_count_cover_exit_le",
  ``!loop f body quit cover exit b.
          0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * cover x y``,
  rpt strip_tac >>
  assume_tac (hop_eq_loop2_count |> ISPEC ``b:num`` |> ISPEC ``f:num -> num``) >>
  first_x_assum (qspecl_then [`x`, `y`] strip_assume_tac) >>
  qabbrev_tac `guard = \x:num y. y = 0` >>
  qabbrev_tac `modify = \y. y - b` >>
  qabbrev_tac `R = measure (\(x:num,y:num). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  qabbrev_tac `quit2 = \x y:num. quit x` >>
  `!x y. loop x y = if guard x y then quit2 x y else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  `FALLING modify` by rw[decrease_falling, Abbr`modify`] >>
  assume_tac loop2_fall_fall_count_cover_exit_le >>
  first_x_assum (qspecl_then [`loop`, `guard`, `body`, `quit2`, `exit`, `modify`, `f`, `R`] strip_assume_tac) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`x`, `y`, `cover`] strip_assume_tac) >>
  qabbrev_tac `n = loop2_count guard modify f x y` >>
  `n = hop b y` by rw[hop_eq_loop2_count, Abbr`n`] >>
  metis_tac[]);

(* Other similar theorems -- directly *)

(* Theorem: 0 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * body x y *)
(* Proof: by loop2_dec_fall_count_cover_exit_le with cover = body. *)
val loop2_dec_fall_count_exit_le = store_thm(
  "loop2_dec_fall_count_exit_le",
  ``!loop f body quit exit b. 0 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * body x y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_dec_fall_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * cover x y *)
(* Proof: by loop2_dec_fall_count_cover_exit_le with exit = F. *)
val loop2_dec_fall_count_cover_le = store_thm(
  "loop2_dec_fall_count_cover_le",
  ``!loop f body quit cover b.
          0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * cover x y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  `!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y - b)` by metis_tac[] >>
  imp_res_tac loop2_dec_fall_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * body x y *)
(* Proof: by loop2_dec_fall_count_cover_le with cover = body. *)
val loop2_dec_fall_count_le = store_thm(
  "loop2_dec_fall_count_le",
  ``!loop f body quit b. 0 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * body x y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_dec_fall_count_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Decreasing Loop with Transform cover                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * cover (FUNPOW g (hop b y) x) y *)
(* Proof:
   Let n = hop b y,
       f1 = (\j. body (FUNPOW f j x) (y - j * b)),
       f2 = K (cover (FUNPOW g n x) y).

   Claim: SUM (GENLIST f1 n) <= SUM (GENLIST f2 n)
   Proof: By SUM_LE, LENGTH_MAP, EL_MAP,
          this is to show: k < n ==>
            body (FUNPOW f k x) (y - b * k) <= cover (FUNPOW g n x) y
          Note y - b * k <= y                         by arithmetic
           Now FUNPOW f k x <= FUNPOW g k x           by FUNPOW_LE_MONO, MONO g
           and FUNPOW g k x <= FUNPOW g n x           by FUNPOW_LE_RISING, k < n, RISING g
          Thus body (FUNPOW f k x) (y - b * k)
            <= cover (FUNPOW f k x) (y - b * k)       by body and cover property
            <= cover (FUNPOW g n x) y                 by MONO2 cover

   Let p = FUNPOW f n x.
        loop x y
     <= quit p + SUM (GENLIST f1 n)                           by loop2_dec_count_sum_le
     <= quit p + SUM (GENLIST f2 n)                           by claim
      = quit p + SUM (GENLIST (K cover (FUNPOW g n x) y) n)   by notation
      = quit p + n * cover (FUNPOW g n x)                     by SUM_GENLIST_K
      = quit (FUNPOW f (hop b y) x) + (hop b y) * cover (FUNPOW g (hop b y) x) y
*)
val loop2_dec_mono_count_cover_exit_le = store_thm(
  "loop2_dec_mono_count_cover_exit_le",
  ``!loop f g body quit cover exit b.
          0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * cover (FUNPOW g (hop b y) x) y``,
  rpt strip_tac >>
  imp_res_tac loop2_dec_count_sum_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = hop b y` >>
  qabbrev_tac `f1 = \j. body (FUNPOW f j x) (y - j * b)` >>
  qabbrev_tac `f2:num -> num = K (cover (FUNPOW g n x) y)` >>
  `SUM (GENLIST f1 n) <= SUM (GENLIST f2 n)` by
  (irule SUM_LE >>
  rw[Abbr`f1`, Abbr`f2`] >>
  `y - b * k <= y` by decide_tac >>
  `FUNPOW f k x <= FUNPOW g k x` by rw[FUNPOW_LE_MONO] >>
  `FUNPOW g k x <= FUNPOW g n x` by rw[FUNPOW_LE_RISING] >>
  `FUNPOW f k x <= FUNPOW g n x` by decide_tac >>
  `body (FUNPOW f k x) (y - b * k) <= cover (FUNPOW f k x) (y - b * k)` by rw[] >>
  `cover (FUNPOW f k x) (y - b * k) <= cover (FUNPOW g n x) y` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST f2 n) = n * cover (FUNPOW g n x) y` by rw[SUM_GENLIST_K, Abbr`f2`] >>
  decide_tac);

(* Other similar theorems -- directly *)

(* Theorem: 0 < b /\ MONO2 body /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * body (FUNPOW g (hop b y) x) y *)
(* Proof: by loop2_dec_mono_count_cover_exit_le with cover = body. *)
val loop2_dec_mono_count_exit_le = store_thm(
  "loop2_dec_mono_count_exit_le",
  ``!loop f g body quit exit b. 0 < b /\ MONO2 body /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * body (FUNPOW g (hop b y) x) y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_dec_mono_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * cover (FUNPOW g (hop b y) x) y *)
(* Proof: by loop2_dec_mono_count_cover_exit_le with exit = F. *)
val loop2_dec_mono_count_cover_le = store_thm(
  "loop2_dec_mono_count_cover_le",
  ``!loop f g body quit cover b.
          0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * cover (FUNPOW g (hop b y) x) y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  `!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y - b)` by metis_tac[] >>
  imp_res_tac loop2_dec_mono_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\ MONO2 body /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * body (FUNPOW g (hop b y) x) y *)
(* Proof: by loop2_dec_mono_count_cover_le with cover = body. *)
val loop2_dec_mono_count_le = store_thm(
  "loop2_dec_mono_count_le",
  ``!loop f g body quit b. 0 < b /\ MONO2 body /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y - b)) ==>
           !x y. loop x y <= quit (FUNPOW f (hop b y) x) + hop b y * body (FUNPOW g (hop b y) x) y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_dec_mono_count_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Original investigation, some with quit = constant.                        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Decreasing List.                                                          *)
(* ------------------------------------------------------------------------- *)

(* Given a number n, generate a decreasing list of n, down to before 0. *)
val decrease_by_def = Define`
    decrease_by b n =
       if (b = 0) \/ (n = 0) then [] else n::decrease_by b (n - b)
`;
(* Overload decrease_by 1 *)
val _ = overload_on ("decreasing", ``decrease_by 1``);

(*
EVAL ``decreasing 10``; = [10; 9; 8; 7; 6; 5; 4; 3; 2; 1]: thm
*)

(* Theorem: (b = 0) \/ (n = 0) ==> (decrease_by b n = []) *)
(* Proof: by decrease_by_def *)
val decrease_by_nil = store_thm(
  "decrease_by_nil",
  ``!b n. (b = 0) \/ (n = 0) ==> (decrease_by b n = [])``,
  rw[Once decrease_by_def]);

(* Theorem: 0 < b /\ 0 < n ==> (decrease_by b n = n::decrease_by b (n - b)) *)
(* Proof: by decrease_by_def *)
val decrease_by_cons = store_thm(
  "decrease_by_cons",
  ``!b n. 0 < b /\ 0 < n ==> (decrease_by b n = n::decrease_by b (n - b))``,
  rw[Once decrease_by_def]);

(* Theorem: decrease_by 0 n = [] *)
(* Proof: by decrease_by_def *)
val decrease_by_0_n = store_thm(
  "decrease_by_0_n",
  ``!n. decrease_by 0 n = []``,
  rw[Once decrease_by_def]);

(* Theorem: decrease_by b 0 = [] *)
(* Proof: by decrease_by_def *)
val decrease_by_b_0 = store_thm(
  "decrease_by_b_0",
  ``!b. decrease_by b 0 = []``,
  rw[Once decrease_by_def]);

(* Theorem: 0 < b /\ n <> 0 ==> (decrease_by b n = n :: decrease_by b (n - b)) *)
(* Proof: by decrease_by_def *)
val decrease_by_b_nonzero = store_thm(
  "decrease_by_b_nonzero",
  ``!b n. 0 < b /\ n <> 0 ==> (decrease_by b n = n :: decrease_by b (n - b))``,
  rw[Once decrease_by_def]);

(*
EVAL ``decrease_by 3 10``; = [10; 7; 4; 1]: thm
EVAL ``GENLIST (\j. 10 - 3 * j) (hop 3 10)``; = [10; 7; 4; 1]: thm
*)

(* Theorem: decrease_by b n = GENLIST (\j. n - j * b) (hop b n) *)
(* Proof:
   Let f = (\j. n - (b + b * j)), g = (\j. n - b * j).
   Note f = g o SUC                   by FUN_EQ_THM
    and g 0 = n - 0 = n               by arithmetic
   By induction from decrease_by_def.
   If b = 0 \/ n = 0,
        decrease_by b n
      = []                            by decrease_by_nil
      = GENLIST g 0                   by GENLIST_0
      = GENLIST g (hop b n)           by hop_0
   Otherwise, b <> 0 /\ n <> 0.
       b <> 0 /\ n <> 0 /\ decrease_by b (n - b) = GENLIST f (hop b (n - b)) ==>
       decrease_by b n = GENLIST (\j. n - b * j) (hop b n)

         decrease_by b n
       = n :: decrease_by b (n - b)                by decrease_by_cons
       = n :: GENLIST f (hop b (n - b))            by induction hypothesis
       = g 0 :: GENLIST (g o SUC) (hop b (n - b))  by f = g o SUC, n = g 0
       = GENLIST g (SUC (hop b (n - b)))           by GENLIST_CONS
       = GENLIST g (hop b n)                       by hop_suc
*)
val decrease_by_eqn = store_thm(
  "decrease_by_eqn",
  ``!b n. decrease_by b n = GENLIST (\j. n - j * b) (hop b n)``,
  ho_match_mp_tac (theorem "decrease_by_ind") >>
  rw[] >>
  Cases_on `(b = 0) \/ (n = 0)` >-
  metis_tac[hop_0, decrease_by_nil, GENLIST_0] >>
  `b <> 0 /\ n <> 0` by decide_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  rw[Once decrease_by_def] >>
  qabbrev_tac `f = \j. n - (b + b * j)` >>
  qabbrev_tac `g = \j. n - b * j` >>
  `f = g o SUC` by rw[FUN_EQ_THM, ADD1, Abbr`f`, Abbr`g`] >>
  `n :: GENLIST f (hop b (n - b))  = g 0 :: GENLIST (g o SUC) (hop b (n - b))` by rw[Abbr`g`] >>
  `_ = GENLIST g (SUC (hop b (n - b)))` by rw[GENLIST_CONS] >>
  `_ = GENLIST g (hop b n)` by metis_tac[hop_def] >>
  rw[]);

(* Theorem: 0 < b /\ 0 < n /\ j * b < n ==> MEM (n - j * b) (decrease_by b n) *)
(* Proof:
       MEM (n - j * b) (decrease_by b n)
   <=> MEM (n - j * b) (GENLIST (\j. n - j * b) (hop b n))   by decrease_by_eqn
   <=> ?m. m < hop b n /\ n - j * b = n - m * b              by MEM_GENLIST
   <=> take m = j, with j < hop b n                          by hop_property
*)
val decrease_by_member = store_thm(
  "decrease_by_member",
  ``!b n j. 0 < b /\ 0 < n /\ j * b < n ==> MEM (n - j * b) (decrease_by b n)``,
  rw[decrease_by_eqn] >>
  rw[MEM_GENLIST] >>
  metis_tac[hop_property]);

(* Theorem: 0 < b /\ 0 < n ==> MEM n (decrease_by b n) *)
(* Proof: put j = 0 in decrease_by_member *)
(* Derive a theorem: put j = 0 in decrease_by_member *)
val decrease_by_head = save_thm("decrease_by_head",
    decrease_by_member |> SPEC ``b:num`` |> SPEC ``n:num`` |> SPEC ``0``
      |> SIMP_RULE (srw_ss()) [] |> GEN ``n:num`` |> GEN ``b:num``);
(* val decrease_by_head = |- !b n. 0 < b /\ 0 < n ==> MEM n (decrease_by b n): thm *)

(* Theorem: LENGTH (decrease_by b n) = hop b n *)
(* Proof:
   Let f = (\j. n - j * b).
     LENGTH (decrease_by b n)
   = LENGTH (GENLIST f (hop b n))    by decrease_by_eqn
   = hop b n                         by LENGTH_GENLIST
*)
val decrease_by_length = store_thm(
  "decrease_by_length",
  ``!b n. LENGTH (decrease_by b n) = hop b n``,
  rw[decrease_by_eqn, LENGTH_GENLIST]);

(* Theorem: j < hop b n ==> (EL j (decrease_by b n) = n - j * b) *)
(* Proof:
   Let g = (\j. n - j * b).
     EL j (decrease_by b n)
   = EL j (GENLIST g (hop b n))   by decrease_by_eqn
   = g j                          by EL_GENLIST, j < hop b n
   = n - j * b                    by notation
*)
val decrease_by_element = store_thm(
  "decrease_by_element",
  ``!b n j. j < hop b n ==> (EL j (decrease_by b n) = n - j * b)``,
  rw[decrease_by_eqn]);

(* Theorem: LENGTH (decreasing n) = n *)
(* Proof:
     LENGTH (decreasing n)
   = LENGTH (decrease_by 1 n)   by notation
   = hop_1_n                    by decrease_by_length
   = n                          by hop_1_n
*)
val decreasing_length = store_thm(
  "decreasing_length",
  ``!n. LENGTH (decreasing n) = n``,
  rw[decrease_by_length, hop_1_n]);

(* Theorem: decreasing n = REVERSE [1 .. n] *)
(* Proof:
      decreasing n
    = GENLIST (\j. n - j * 1) (hop 1 n)         by decrease_by_eqn
    = GENLIST (\j. n - j) n                     by hop_1_n

      REVERSE [1 .. n]
    = REVERSE (GENLIST (\i. 1 + i) (n + 1 - 1))   by listRangeINC_def
    = REVERSE (GENLIST SUC n)                     by ADD1
    = GENLIST (\m. SUC (PRE n - m)) n             by REVERSE_GENLIST
    = GENLIST (\m. n - m) n                       by m < n in GENLIST

    Thus decreasing n = REVERSE [1 .. n]          by GENLIST_EQ
*)
val decreasing_eqn = store_thm(
  "decreasing_eqn",
  ``!n. decreasing n = REVERSE [1 .. n]``,
  rw[decrease_by_eqn, hop_1_n, listRangeINC_def] >>
  rw[REVERSE_GENLIST] >>
  irule GENLIST_EQ >>
  rw[FUN_EQ_THM]);

(* Theorem: 0 < b ==> (decrease_by b x = loop_arg (\x. x = 0) (\x. x - b) x) *)
(* Proof:
   By induction from decrease_by_def.
   Let guard = (\x. x = 0),
       modify = (\x. x - b),
       R = measure (\x. x).
   The goal is: decrease_by b x = loop_arg guard modify x
   Then WF R                                by WF_measure
    and !x. ~guard x ==> R (modify x) x     by x - b < x, 0 < b

   If guard x,
      Then x = 0                            by guard x
           decrease_by b 0
         = []                               by decrease_by_nil
         = loop_arg guard modify 0          by loop_arg_nil
   If ~guard x,
      Then x <> 0                                by ~guard x
           decrease_by b x
         = x :: decrease_by b (x - b)            by decrease_by_cons
         = x :: loop_arg guard modify (x - b)    by induction hypothesis
         = loop_arg guard modify x               by loop_arg_cons, ~guard x
*)
val decrease_by_eq_loop_arg = store_thm(
  "decrease_by_eq_loop_arg",
  ``!b x. 0 < b ==> (decrease_by b x = loop_arg (\x. x = 0) (\x. x - b) x)``,
  ho_match_mp_tac (theorem "decrease_by_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x - b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`modify`, Abbr`R`] >>
  Cases_on `guard x` >| [
    `x = 0` by metis_tac[] >>
    metis_tac[decrease_by_nil, loop_arg_nil],
    `x <> 0` by metis_tac[] >>
    `decrease_by b x = x :: decrease_by b (x - b)` by rw[decrease_by_cons] >>
    `_ = x :: loop_arg guard modify (x - b)` by metis_tac[NOT_ZERO] >>
    `_ = loop_arg guard modify x` by metis_tac[loop_arg_cons] >>
    rw[]
  ]);

(* Theorem: 0 < b ==> (MAP2 body (iterating f x (hop b y)) (decrease_by b y) =
                       MAP (UNCURRY body) (loop2_arg (\x y. y = 0) (\y. y - b) f x y)) *)
(* Proof:
   By induction from decrease_by_def.
   Let guard = (\x y. y = 0),
       modify = (\y. y - b),
       R = measure (\(x,y). y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by x - b < x, 0 < b

   If guard x y,
      Then y = 0                                by notation
      LHS = MAP2 body (iterating f x (hop b 0)) (decrease_by b 0)
          = MAP2 body (iterating f x 0) []      by hop_0, decrease_by_nil
          = MAP2 body [] []                     by iterating_nil
          = []                                  by MAP2
      RHS = MAP (UNCURRY body) (loop2_arg guard modify f x y)
          = MAP (UNCURRY body) []               by loop2_arg_nil, guard x y
          = [] = LHS                            by MAP

   If ~guard x y,
     Then y <> 0                                by notation
            MAP2 body (iterating f x (hop b y)) (decrease_by b y)
          = MAP2 body (iterating f x (SUC (hop b (y - b)))) (y::decrease_by b (y - b))
                                                by hop_suc, decrease_by_cons
          = MAP2 body (x::iterating f (f x) (hop b (y - b))) (y::decrease_by b (y - b))
                                                by iterating_cons
          = body x y::MAP2 body (iterating f (f x) (hop b (y - b))) (decrease_by b (y - b))
                                                by MAP2
          = body x y::MAP (UNCURRY body) (loop2_arg guard modify f (f x) (y - b))
                                                by induction hypothesis
          = MAP (UNCURRY body) ((x,y):: loop2_arg guard modify f (f x) (y - b))
                                                by MAP, UNCURRY
          = MAP (UNCURRY body) (loop2_arg guard modify f x y)
                                                by loop2_arg_cons
*)
val iterating_decrease_eq_loop2_arg = store_thm(
  "iterating_decrease_eq_loop2_arg",
  ``!b body f x y. 0 < b ==>
    (MAP2 body (iterating f x (hop b y)) (decrease_by b y) =
     MAP (UNCURRY body) (loop2_arg (\x y. y = 0) (\y. y - b) f x y))``,
  ntac 5 strip_tac >>
  qid_spec_tac `x` >>
  qid_spec_tac `y` >>
  qid_spec_tac `b` >>
  ho_match_mp_tac (theorem "decrease_by_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x y. y = 0` >>
  qabbrev_tac `modify = \y. y - b` >>
  qabbrev_tac `R = measure (\(x,y). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  Cases_on `guard x y` >| [
    `y = 0` by metis_tac[] >>
    rw[iterating_nil, hop_0, decrease_by_nil] >>
    metis_tac[loop2_arg_nil],
    `y <> 0` by metis_tac[] >>
    rw[iterating_cons, hop_suc, decrease_by_cons] >>
    `body x y:: MAP2 body (iterating f (f x) (hop b (modify y))) (decrease_by b (modify y)) =
    body x y:: MAP2 body (iterating f (f x) (hop b (y - b))) (decrease_by b (y - b))` by rw[Abbr`modify`] >>
    `_ = body x y::MAP (UNCURRY body) (loop2_arg guard modify f (f x) (y - b))` by metis_tac[NOT_ZERO] >>
    `_ = MAP (UNCURRY body) ((x,y)::loop2_arg guard modify f (f x) (modify y))` by rw[Abbr`modify`] >>
    metis_tac[loop2_arg_cons]
  ]);

(* ------------------------------------------------------------------------- *)
(* Decrease Loop -- original                                                 *)
(* ------------------------------------------------------------------------- *)

(*
loop_modify_count_by_sum |> SPEC_ALL |> INST_TYPE [alpha |-> ``:num``]
                |> Q.INST [`modify` |-> `(\x. x - b)`, `guard` |-> `(\x. x = 0)`, `R` |-> `measure (\x. x)`]
               |>  ADD_ASSUM ``0 < b`` |> DISCH_ALL
               |> SIMP_RULE (srw_ss()) [GSYM decrease_by_eq_loop_arg];
-- the last one will not work, due to loop being recursive.
*)

(* Theorem: 0 < b /\ (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
        !x. loop x = c + SUM (MAP body (decrease_by b x)) *)
(* Proof:
   Let guard = (\x. x = 0),
       modify = (\x. x - b),
       R = measure (\x. x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by x - b < x, 0 < b
   Also !x. loop x = if guard x then c else body x + loop (modify x)
                                          by given
   Thus loop x
      = c + SUM (MAP body (loop_arg guard modify x))  by loop_modify_count_by_sum
      = c + SUM (MAP body (decrease_by b x))          by decrease_by_eq_loop_arg
*)
val loop_dec_count_by_sum = store_thm(
  "loop_dec_count_by_sum",
  ``!loop body b c. 0 < b /\ (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
        !x. loop x = c + SUM (MAP body (decrease_by b x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x - b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x. loop x = if guard x then c else body x + loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_by_sum >>
  `loop_arg guard modify x = decrease_by b x` by rw[decrease_by_eq_loop_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 0 < b /\
          (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
          !x. loop x <= c + SUM (MAP body (decrease_by b x)) *)
(* Proof:
   Let guard = (\x. x = 0),
       modify = (\x. x - b),
       R = measure (\x. x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by x - b < x, 0 < b
   Also !x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)
                                          by given
   Thus loop x
     <= c + SUM (MAP body (loop_arg guard modify x))  by loop_modify_count_exit_by_sum
      = c + SUM (MAP body (decrease_by b x))          by decrease_by_eq_loop_arg
*)
val loop_dec_count_exit_by_sum = store_thm(
  "loop_dec_count_exit_by_sum",
  ``!loop body b c exit. 0 < b /\
          (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
           !x. loop x <= c + SUM (MAP body (decrease_by b x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x - b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_exit_by_sum >>
  `loop_arg guard modify x = decrease_by b x` by rw[decrease_by_eq_loop_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 0 < b /\ (!x. body x <= cover x) /\ MONO cover /\
            (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
             !x. loop x <= c + cover x * hop b x *)
(* Proof:
   Let ls = decrease_by b x.
       loop x
    <= c + SUM (MAP body ls)       by loop_dec_count_guard_by_sum
    <= SUM (MAP (K (cover n)) ls)  by SUM_LE, decrease_by_length, decrease_by_element, MONO cover
     = (cover x) * LENGTH ls       by SUM_MAP_K
     = (cover x) * (hop b x)       by decrease_by_length
*)
val loop_dec_count_cover_exit_upper = store_thm(
  "loop_dec_count_cover_exit_upper",
  ``!loop body cover exit b c. 0 < b /\ (!x. body x <= cover x) /\ MONO cover /\
   (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
     !x. loop x <= c + (cover x) * (hop b x)``,
  rpt strip_tac >>
  qabbrev_tac `ls = decrease_by b x` >>
  `loop x <= c + SUM (MAP body ls)` by metis_tac[loop_dec_count_exit_by_sum] >>
  `SUM (MAP body ls) <= SUM (MAP (K (cover x)) ls)` by
  (irule SUM_LE >>
  rw[decrease_by_length, decrease_by_element, EL_MAP, Abbr`ls`] >>
  `body (x - b * k) <= cover (x - b * k)` by rw[] >>
  `cover (x - b * k) <= cover x` by rw[] >>
  decide_tac) >>
  `SUM (MAP (K (cover x)) ls) = (cover x) * LENGTH ls` by rw[SUM_MAP_K] >>
  `_ = (cover x) * (hop b x)` by rw[decrease_by_length, Abbr`ls`] >>
  decide_tac);

(* Theorem: 0 < b /\ MONO body /\
            (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
             !x. loop x <= c + (body x) * (hop b x) *)
(* Proof: by loop_dec_count_cover_exit_upper with cover = body. *)
val loop_dec_count_exit_upper = store_thm(
  "loop_dec_count_exit_upper",
  ``!loop body b c exit. 0 < b /\ MONO body /\
   (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x - b)) ==>
     !x. loop x <= c + (body x) * (hop b x)``,
  metis_tac[loop_dec_count_cover_exit_upper, LESS_EQ_REFL]);

(* Theorem: 0 < b /\ (!x. body x <= cover x) /\ MONO cover /\
           (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
            !x. loop x <= c + (body x) * (hop b x) *)
(* Proof: by loop_dec_count_cover_exit_upper with exit = F. *)
val loop_dec_count_cover_upper = store_thm(
  "loop_dec_count_cover_upper",
  ``!loop body b c cover. 0 < b /\ (!x. body x <= cover x) /\ MONO cover /\
   (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
     !x. loop x <= c + (cover x) * (hop b x)``,
  rpt strip_tac >>
  qabbrev_tac `exit = (\x:num. F)` >>
  metis_tac[loop_dec_count_cover_exit_upper]);

(* Theorem: 0 < b /\ MONO body /\
            (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
            !x. loop x <= c + (body x) * (hop b x) *)
(* Proof: by loop_dec_count_cover_upper with body = cover. *)
val loop_dec_count_upper = store_thm(
  "loop_dec_count_upper",
  ``!loop body b c. 0 < b /\ MONO body /\
    (!x. loop x = if x = 0 then c else body x + loop (x - b)) ==>
     !x. loop x <= c + (body x) * (hop b x)``,
  metis_tac[loop_dec_count_cover_upper, LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)
(* Decrease Loop with Transform -- original                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\
    (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y - b)) ==>
     !x y. loop x y = c + SUM (MAP2 body (iterating f x (hop b y)) (decrease_by b y)) *)
(* Proof:
   Let guard = (\x y. y = 0),
       modify = (\y. y - b),
       R = measure (\(x,y). y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by x - b < x, 0 < b
    and !x y. loop x y = if guard x y then c else body x y + loop (f x) (modify y)   by given
        loop x y
      = c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))       by loop2_modify_count_by_sum
      = c + SUM (MAP2 body (iterating f x (hop b y)) (decrease_by b y))   by iterating_decrease_eq_loop2_arg
*)
val loop2_dec_count_by_sum = store_thm(
  "loop2_dec_count_by_sum",
  ``!loop f body b c. 0 < b /\
    (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y - b)) ==>
     !x y. loop x y = c + SUM (MAP2 body (iterating f x (hop b y)) (decrease_by b y))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. y = 0` >>
  qabbrev_tac `modify = \y. y - b` >>
  qabbrev_tac `R = measure (\(x,y). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x y. loop x y = if guard x y then c else body x y + loop (f x) (modify y)` by metis_tac[] >>
  `loop x y = c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))` by metis_tac[loop2_modify_count_by_sum] >>
  `MAP (UNCURRY body) (loop2_arg guard modify f x y) =
    MAP2 body (iterating f x (hop b y)) (decrease_by b y)` by rw[iterating_decrease_eq_loop2_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 0 < b /\
    (!x y. loop x y = if y = 0 then c else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
     !x y. loop x y <= c + SUM (MAP2 body (iterating f x (hop b y)) (decrease_by b y)) *)
(* Proof:
   Let guard = (\x y. y = 0),
       modify = (\y. y - b),
       R = measure (\(x,y). y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by x - b < x, 0 < b
    and !x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                      by given
        loop x y
     <= c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))       by loop2_modify_count_exit_by_sum
      = c + SUM (MAP2 body (iterating f x (hop b y)) (decrease_by b y))   by iterating_decrease_eq_loop2_arg
*)
val loop2_dec_count_exit_by_sum = store_thm(
  "loop2_dec_count_exit_by_sum",
  ``!loop f body b c exit. 0 < b /\
    (!x y. loop x y = if y = 0 then c else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
     !x y. loop x y <= c + SUM (MAP2 body (iterating f x (hop b y)) (decrease_by b y))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. y = 0` >>
  qabbrev_tac `modify = \y. y - b` >>
  qabbrev_tac `R = measure (\(x,y). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  assume_tac (loop2_modify_count_exit_by_sum |> ISPEC ``loop:'a -> num -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `exit`, `modify`, `f`, `R`] strip_assume_tac) >>
  `loop x y <= c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))` by metis_tac[] >>
  `MAP (UNCURRY body) (loop2_arg guard modify f x y) =
    MAP2 body (iterating f x (hop b y)) (decrease_by b y)` by rw[iterating_decrease_eq_loop2_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x1 y1 <= cover x2 y2) /\
       (!x y. loop x y = if y = 0 then c else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
        !x y. loop x y <= c + cover x y * hop b y *)
(* Proof:
   Let guard = (\x y. y = 0),
       modify = (\y. y - b),
       R = measure (\(x,y). y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)    by x - b < x, 0 < b
    and !x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> cover x1 y1 <= cover x2 y2    by R
    and !x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                     by given
        loop x y
     <= c + cover x y * loop2_count guard modify f x y       by loop2_modify_count_bcover_exit_upper
      = c + cover x y * hop b y                              by hop_eq_loop2_count
*)
val loop2_dec_count_cover_exit_upper = store_thm(
  "loop2_dec_count_cover_exit_upper",
  ``!loop f body cover exit b c. 0 < b /\
       (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x1 y1 <= cover x2 y2) /\
       (!x y. loop x y = if y = 0 then c else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
        !x y. loop x y <= c + cover x y * hop b y``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. y = 0` >>
  qabbrev_tac `modify = \y. y - b` >>
  qabbrev_tac `R = measure (\(x,y). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> cover x1 y1 <= cover x2 y2` by rw[Abbr`R`] >>
  `!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  assume_tac (loop2_modify_count_bcover_exit_upper |> ISPEC ``loop:'a -> num -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `exit`, `cover`, `modify`, `f`, `R`] strip_assume_tac) >>
  `loop2_count guard modify f x y = hop b y` by rw[hop_eq_loop2_count, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 0 < b /\ (!x1 x2 y1 y2. y1 <= y2 ==> body x1 y1 <= body x2 y2) /\
       (!x y. loop x y = if y = 0 then c else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
        !x y. loop x y <= c + body x y * hop b y *)
(* Proof: by loop2_dec_count_cover_exit_upper, with cover = body. *)
val loop2_dec_count_exit_upper = store_thm(
  "loop2_dec_count_exit_upper",
  ``!loop f body exit b c. 0 < b /\
       (!x1 x2 y1 y2. y1 <= y2 ==> body x1 y1 <= body x2 y2) /\
       (!x y. loop x y = if y = 0 then c else body x y + if exit x y then 0 else loop (f x) (y - b)) ==>
        !x y. loop x y <= c + body x y * hop b y``,
  rpt strip_tac >>
  assume_tac loop2_dec_count_cover_exit_upper >>
  last_x_assum (qspecl_then [`loop`, `f`, `body`, `body`, `exit`, `b`, `c`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x1 y1 <= cover x2 y2) /\
       (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y - b)) ==>
        !x y. loop x y <= c + cover x y * hop b y *)
(* Proof: by loop2_dec_count_cover_exit_upper, with exit = F. *)
val loop2_dec_count_cover_upper = store_thm(
  "loop2_dec_count_cover_upper",
  ``!loop f body cover b c. 0 < b /\ (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x1 y1 <= cover x2 y2) /\
       (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y - b)) ==>
        !x y. loop x y <= c + cover x y * hop b y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:'a y:num. F` >>
  assume_tac loop2_dec_count_cover_exit_upper >>
  last_x_assum (qspecl_then [`loop`, `f`, `body`, `cover`, `exit`, `b`, `c`] strip_assume_tac) >>
  metis_tac[]);

(* Theorem: 0 < b /\ (!x1 x2 y1 y2. y1 <= y2 ==> body x1 y1 <= body x2 y2) /\
    (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y - b)) ==>
     !x y. loop x y <= c + body x y * hop b y *)
(* Proof: loop2_dec_count_cover_upper, with body = cover. *)
val loop2_dec_count_upper = store_thm(
  "loop2_dec_count_upper",
  ``!loop f body b c. 0 < b /\ (!x1 x2 y1 y2. y1 <= y2 ==> body x1 y1 <= body x2 y2) /\
    (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y - b)) ==>
     !x y. loop x y <= c + body x y * hop b y``,
  rpt strip_tac >>
  assume_tac loop2_dec_count_cover_upper >>
  last_x_assum (qspecl_then [`loop`, `f`, `body`, `body`, `b`, `c`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
