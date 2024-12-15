(* ------------------------------------------------------------------------- *)
(* Loop Recurrence with Dividing argument                                    *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "loopDivide";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open arithmeticTheory dividesTheory numberTheory combinatoricsTheory listTheory
     rich_listTheory listRangeTheory logrootTheory;

open loopTheory bitsizeTheory;

val _ = temp_overload_on("SQ", ``\n. n * n``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);
val _ = temp_overload_on ("RISING", ``\f. !x:num. x <= f x``);
val _ = temp_overload_on ("FALLING", ``\f. !x:num. f x <= x``);

(* ------------------------------------------------------------------------- *)
(* Loop Recurrence with Dividing argument Documentation                      *)
(* ------------------------------------------------------------------------- *)
(* Type and Overload:
   halving          = divide_by 2
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Dividing Count:
   pop_def         |- !n b. pop b n = if b <= 1 \/ n = 0 then 0 else SUC (pop b (n DIV b))
   pop_alt         |- !n b. pop b n = if b <= 1 \/ n = 0 then 0 else 1 + pop b (n DIV b)
   pop_0           |- !b n. b <= 1 \/ n = 0 ==> pop b n = 0
   pop_suc         |- !b n. 1 < b /\ 0 < n ==> pop b n = SUC (pop b (n DIV b))
   pop_zero        |- !b n. pop b 0 = 0 /\ pop 0 n = 0 /\ pop 1 n = 0
   pop_nonzero     |- !b n. 1 < b /\ 0 < n ==> pop b n = 1 + pop b (n DIV b)
   pop_pos         |- !b n. 1 < b /\ 0 < n ==> 0 < pop b n
   pop_property    |- !b n. 1 < b /\ 0 < n ==> !j. m ** j <= n <=> j < pop b n
   pop_exceeds     |- !b n. 1 < b ==> n < b ** pop b n
   pop_exceeds_div |- !b n. 1 < b ==> n DIV b ** pop b n = 0
   pop_eqn         |- !b n. pop b n = if b <= 1 \/ n = 0 then 0 else 1 + LOG b n
   pop_LOG         |- !b n. pop b n <= 1 + LOG b n
   pop_2_size      |- !n. pop 2 n = if n = 0 then 0 else size n
   pop_size        |- !b n. pop b n <= size n
   pop_eq_loop_count
                   |- !b x. 1 < b ==> pop b x = loop_count (\x. x = 0) (\x. x DIV b) x
   pop_eq_loop2_count
                   |- !b f x y. 1 < b ==> pop b y = loop2_count (\x y. y = 0) (\y. y DIV b) f x y

   divide_falling          |- !b. 0 < b ==> FALLING (\x. x DIV b)
   iterating_div_eqn       |- !b n x. 0 < b ==> FUNPOW (\x. x DIV b) n x = x DIV b ** n
   iterating_div_pop       |- !b x. 1 < b ==> FUNPOW (\x. x DIV b) (pop b x) x = 0
   iterating_div_pop_alt   |- !b x. 1 < b ==> x < b ** pop b x

   Dividing Loop:
   loop_div_count_eqn      |- !loop body b c. 1 < b /\
                              (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
                               !x. loop x = c + SUM (GENLIST (\j. body (x DIV b ** j)) (pop b x))
   loop_div_count_exit_sum_le
                           |- !loop body exit b c. 1 < b /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x DIV b)) ==>
                               !x. loop x <= c + SUM (GENLIST (\j. body (x DIV b ** j)) (pop b x))
   loop_div_count_cover_exit_le
                           |- !loop body cover exit b c. 1 < b /\
                              (!x. body x <= cover x) /\ MONO cover /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x DIV b)) ==>
                               !x. loop x <= c + pop b x * cover x
   loop_div_count_exit_le  |- !loop body exit b c. 1 < b /\ MONO body /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x DIV b)) ==>
                               !x. loop x <= c + pop b x * body x
   loop_div_count_cover_le |- !loop body cover b c. 1 < b /\
                              (!x. body x <= cover x) /\ MONO cover /\
                              (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
                               !x. loop x <= c + pop b x * cover x
   loop_div_count_le       |- !loop body b c. 1 < b /\ MONO body /\
                              (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
                               !x. loop x <= c + pop b x * body x
   loop_div_count_rcover_exit_le
                           |- !loop body cover exit b c. 1 < b /\
                              (!x. body x <= cover x) /\ RMONO cover /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x DIV b)) ==>
                               !x. loop x <= c + pop b x * cover 0
   loop_div_count_rbody_exit_le
                           |- !loop body exit b c. 1 < b /\ RMONO body /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x DIV b)) ==>
                               !x. loop x <= c + pop b x * body 0
   loop_div_count_rcover_le|- !loop body cover b c. 1 < b /\
                              (!x. body x <= cover x) /\ RMONO cover /\
                              (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
                               !x. loop x <= c + pop b x * cover 0
   loop_div_count_rbody_le |- !loop body b c. 1 < b /\ RMONO body /\
                              (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
                               !x. loop x <= c + pop b x * body 0

   Dividing Loop with Transform:
   loop2_div_count_eqn     |- !loop f body quit b. 1 < b /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + loop (f x) (y DIV b)) ==>
                               !x y. loop x y = quit (FUNPOW f (pop b y) x) +
                                     SUM (GENLIST (\j. body (FUNPOW f j x) (y DIV b ** j)) (pop b y))
   loop2_div_count_sum_le  |- !loop f body quit exit b. 1 < b /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (pop b y) x) +
                                     SUM (GENLIST (\j. body (FUNPOW f j x) (y DIV b ** j)) (pop b y))

   Dividing Loop with Transform-independent Body:
   loop2_div_count_mono_cover_exit_le
                   |- !loop f body quit cover exit b g. 1 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y =
                             if y = 0 then quit x
                             else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * g y
   loop2_div_count_mono_exit_le
                   |- !loop f body quit exit b g. 1 < b /\ body = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y =
                             if y = 0 then quit x
                             else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * g y
   loop2_div_count_mono_cover_le
                   |- !loop f body quit cover b g. 1 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * g y
   loop2_div_count_mono_le
                   |- !loop f body quit b g. 1 < b /\ body = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * g y
   loop2_div_count_rmono_cover_exit_le
                   |- !loop f body quit cover exit b g. 1 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y =
                             if y = 0 then quit x
                             else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * g 0
   loop2_div_count_rmono_exit_le
                   |- !loop f body quit exit b g. 1 < b /\ body = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y =
                             if y = 0 then quit x
                             else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * g 0
   loop2_div_count_rmono_cover_le
                   |- !loop f body quit cover b g. 1 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * g 0
   loop2_div_count_rmono_le
                   |- !loop f body quit b g. 1 < b /\ body = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * g 0

   Dividing Loop with Numeric Transform:
   loop2_div_rise_count_cover_exit_le
                           |- !loop f body quit cover exit b. 1 < b /\
                              (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (pop b y) x) +
                                                 pop b y * cover (FUNPOW f (pop b y) x) y
   loop2_div_rise_count_exit_le
                           |- !loop f body quit exit b. 1 < b /\ MONO2 body /\ RISING f /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (pop b y) x) +
                                                 pop b y * body (FUNPOW f (pop b y) x) y
   loop2_div_rise_count_cover_le
                           |- !loop f body quit cover b. 1 < b /\
                              (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + loop (f x) (y DIV b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (pop b y) x) +
                                                 pop b y * cover (FUNPOW f (pop b y) x) y
   loop2_div_rise_count_le |- !loop f body quit b. 1 < b /\ MONO2 body /\ RISING f /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + loop (f x) (y DIV b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (pop b y) x) +
                                                 pop b y * body (FUNPOW f (pop b y) x) y
   loop2_div_fall_count_cover_exit_le
                           |- !loop f body quit cover exit b. 1 < b /\
                              (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * cover x y
   loop2_div_fall_count_exit_le
                           |- !loop f body quit exit b. 1 < b /\ MONO2 body /\ FALLING f /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * body x y
   loop2_div_fall_count_cover_le
                           |- !loop f body quit cover b. 1 < b /\
                              (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + loop (f x) (y DIV b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * cover x y
   loop2_div_fall_count_le |- !loop f body quit b. 1 < b /\ MONO2 body /\ FALLING f /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + loop (f x) (y DIV b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * body x y

   Dividing Loop with Transform cover:
   loop2_div_mono_count_cover_exit_le
                           |- !loop f g body quit cover exit b. 1 < b /\
                              (!x y. body x y <= cover x y) /\ MONO2 cover /\
                              (!x. f x <= g x) /\ MONO g /\ RISING g /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (pop b y) x) +
                                                 pop b y * cover (FUNPOW g (pop b y) x) y
   loop2_div_mono_count_exit_le
                           |- !loop f g body quit exit b. 1 < b /\ MONO2 body /\
                              (!x. f x <= g x) /\ MONO g /\ RISING g /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (pop b y) x) +
                                                 pop b y * body (FUNPOW g (pop b y) x) y
   loop2_div_mono_count_cover_le
                           |- !loop f g body quit cover b. 1 < b /\
                              (!x y. body x y <= cover x y) /\ MONO2 cover /\
                              (!x. f x <= g x) /\ MONO g /\ RISING g /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + loop (f x) (y DIV b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (pop b y) x) +
                                                 pop b y * cover (FUNPOW g (pop b y) x) y
   loop2_div_mono_count_le |- !loop f g body quit b. 1 < b /\ MONO2 body /\
                              (!x. f x <= g x) /\ MONO g /\ RISING g /\
                              (!x y. loop x y =
                                     if y = 0 then quit x
                                     else body x y + loop (f x) (y DIV b)) ==>
                               !x y. loop x y <= quit (FUNPOW f (pop b y) x) +
                                                 pop b y * body (FUNPOW g (pop b y) x) y

   Original:
   Dividing List:
   divide_by_def           |- !n b. divide_by b n =
                                    if b <= 1 \/ n = 0 then [] else n::divide_by b (n DIV b)
   divide_by_nil           |- !b n. b <= 1 \/ n = 0 ==> divide_by b n = []
   divide_by_cons          |- !b n. 1 < b /\ 0 < n ==> divide_by b n = n::divide_by b (n DIV b)
   divide_by_0_n           |- !n. divide_by 0 n = []
   divide_by_1_n           |- !n. divide_by 1 n = []
   divide_by_b_0           |- !b. divide_by b 0 = []
   divide_by_b_nonzero     |- !b n. 1 < b /\ n <> 0 ==> divide_by b n = n::divide_by b (n DIV b)
   divide_by_eqn           |- !b n. divide_by b n = GENLIST (\j. n DIV b ** j) (pop b n)
   divide_by_member        |- !b n j. 1 < b /\ 0 < n /\ b ** j <= n ==> MEM (n DIV b ** j) (divide_by b n)
   divide_by_head          |- !b n. 1 < b /\ 0 < n ==> MEM n (divide_by b n)
   divide_by_length        |- !b n. LENGTH (divide_by b n) = pop b n
   divide_by_element       |- !b n j. j < pop b n ==> EL j (divide_by b n) = n DIV b ** j
   divide_by_eq_loop_arg   |- !b x. 1 < b ==> divide_by b x = loop_arg (\x. x = 0) (\x. x DIV b) x
   iterating_divide_eq_loop2_arg
                           |- !b body f x y. 1 < b ==>
                                 MAP2 body (iterating f x (pop b y)) (divide_by b y) =
                                 MAP (UNCURRY body) (loop2_arg (\x y. y = 0) (\y. y DIV b) f x y)

   loop_div_count_by_sum   |- !loop body b c. 1 < b /\
                              (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
                               !x. loop x = c + SUM (MAP body (divide_by b x))
   loop_div_count_exit_by_sum
                           |- !loop body b c exit. 1 < b /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x DIV b)) ==>
                               !x. loop x <= c + SUM (MAP body (divide_by b x))
   loop_div_count_cover_exit_upper
                           |- !loop body cover exit b c. 1 < b /\
                              (!x. body x <= cover x) /\ MONO cover /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x DIV b)) ==>
                               !x. loop x <= c + cover x * pop b x
   loop_div_count_exit_upper
                           |- !loop body b c exit. 1 < b /\ MONO body /\
                              (!x. loop x =
                                   if x = 0 then c
                                   else body x + if exit x then 0 else loop (x DIV b)) ==>
                               !x. loop x <= c + body x * pop b x
   loop_div_count_cover_upper
                           |- !loop body b c cover. 1 < b /\
                              (!x. body x <= cover x) /\ MONO cover /\
                              (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
                               !x. loop x <= c + cover x * pop b x
   loop_div_count_upper    |- !loop body b c. 1 < b /\ MONO body /\
                              (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
                               !x. loop x <= c + body x * pop b x

   loop2_div_count_by_sum
                   |- !loop f body b c. 1 < b /\
                      (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y DIV b)) ==>
                       !x y. loop x y = c + SUM (MAP2 body (iterating f x (pop b y)) (divide_by b y))
   loop2_div_count_exit_by_sum
                   |- !loop f body b c exit. 1 < b /\
                      (!x y. loop x y =
                             if y = 0 then c
                             else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
                       !x y. loop x y <= c + SUM (MAP2 body (iterating f x (pop b y)) (divide_by b y))
   loop2_div_count_cover_exit_upper
                   |- !loop f body cover exit b c. 1 < b /\ (!x y. body x y <= cover x y) /\
                      (!x1 x2 y1 y2. y1 <= y2 ==> cover x1 y1 <= cover x2 y2) /\
                      (!x y. loop x y =
                             if y = 0 then c
                             else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
                       !x y. loop x y <= c + cover x y * pop b y
   loop2_div_count_exit_upper
                   |- !loop f body exit b c. 1 < b /\
                      (!x1 x2 y1 y2. y1 <= y2 ==> body x1 y1 <= body x2 y2) /\
                      (!x y. loop x y =
                             if y = 0 then c
                             else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
                       !x y. loop x y <= c + body x y * pop b y
   loop2_div_count_cover_upper
                   |- !loop f body cover b c. 1 < b /\
                      (!x y. body x y <= cover x y) /\
                      (!x1 x2 y1 y2. y1 <= y2 ==> cover x1 y1 <= cover x2 y2) /\
                      (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y DIV b)) ==>
                       !x y. loop x y <= c + cover x y * pop b y
   loop2_div_count_upper
                   |- !loop f body b c. 1 < b /\ (!x1 x2 y1 y2. y1 <= y2 ==> body x1 y1 <= body x2 y2) /\
                      (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y DIV b)) ==>
                       !x y. loop x y <= c + body x y * pop b y
*)

(* ------------------------------------------------------------------------- *)
(* Loop Recurrence with Dividing argument                                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Dividing Count.                                                           *)
(* ------------------------------------------------------------------------- *)

(* Define a pop function, count of pops to zero. *)
val pop_def = Define`
    pop b n = if (b <= 1) \/ (n = 0) then 0 else SUC (pop b (n DIV b))
`;

(* alternate form *)
val pop_alt = save_thm("pop_alt", pop_def |> REWRITE_RULE [SUC_ONE_ADD]);
(* val pop_alt = |- !n b. pop b n = if b <= 1 \/ n = 0 then 0 else 1 + pop b (n DIV b): thm *)

(* Theorem: (b <= 1) \/ (n = 0) ==> (pop b n = 0) *)
(* Proof: by pop_def *)
val pop_0 = store_thm(
  "pop_0",
  ``!b n. (b <= 1) \/ (n = 0) ==> (pop b n = 0)``,
  rw[Once pop_def]);

(* Theorem: 1 < b /\ 0 < n ==> (pop b n = SUC (pop b (n DIV b))) *)
(* Proof: by pop_def *)
val pop_suc = store_thm(
  "pop_suc",
  ``!b n. 1 < b /\ 0 < n ==> (pop b n = SUC (pop b (n DIV b)))``,
  rw[Once pop_def]);

(* Theorem: (pop b 0 = 0) /\ (pop 0 n = 0) /\ (pop 1 n = 0) *)
(* Proof: by pop_def *)
val pop_zero = store_thm(
  "pop_zero",
  ``!b n. (pop b 0 = 0) /\ (pop 0 n = 0) /\ (pop 1 n = 0)``,
  rw[Once pop_def] >>
  rw[Once pop_def] >>
  rw[Once pop_def]);

(* Theorem: 1 < b /\ 0 < n ==> (pop b n = 1 + pop b (n DIV b)) *)
(* Proof: by pop_def *)
val pop_nonzero = store_thm(
  "pop_nonzero",
  ``!b n. 1 < b /\ 0 < n ==> (pop b n = 1 + pop b (n DIV b))``,
  rw[Once pop_def]);

(* Theorem: 1 < b /\ 0 < n ==> 0 < pop b n *)
(* Proof: by pop_def *)
val pop_pos = store_thm(
  "pop_pos",
  ``!b n. 1 < b /\ 0 < n ==> 0 < pop b n``,
  rw[Once pop_def]);

(* Theorem: 1 < b /\ 0 < n ==> !j. b ** j <= n <=> j < pop b n *)
(* Proof:
   By induction from pop_def, to show:
   If n DIV b = 0,
      Then b < n                   by DIV_EQ_0
       and pop b n = 1 + pop b 0   by pop_def
                   = 1 + 0 = 1     by pop_zero
      If j = 0, LHS = T = RHS      by pop_pos, 0 < b, 1 <= n
      If j <> 0, LHS = F = RHS     by X_LE_X_EXP, b <= b ** j when j <> 0
   If n DIV b <> 0,
      Then ~(b < n), or n <= b     by DIV_EQ_0
        so b ** (j - 1) <= n DIV b <=> j - 1 < pop b (n DIV b)
                                   by induction hypothesis
      If j = 0, LHS = T = RHS      by pop_pos, 0 < m, 1 <= n
      If j <> 0,
         Let k = j - 1, then j = SUC k                by j <> 0
         b ** k <= n DIV b <=> k < pop b (n DIV b)    by above, [1]
         Thus if b ** j <= n
            ==>         b ** SUC k <= n          by j = SUC k
            ==>         b * b ** k <= n          by EXP
            ==> (b * b ** k) DIV b <= n DIV b    by DIV_LE_MONOTONE
            ==>             b ** k <= n DIV b    by MULT_TO_DIV
            ==>        k < pop b (n DIV b)       by [1]
            ==>    SUC k < SUC (pop b (n DIV b)) by LESS_MONO_EQ
            ==>        j < pop b n               by pop_def
         Also if j < pop b n
            ==> SUC k < SUC (pop b (n DIV b))    by pop_def
            ==>     k < pop (b (n DIV b))        by LESS_MONO_EQ
            ==>       b ** k <= n DIV b          by [1]
            ==>   b * b ** k <= b * (n DIV b)    by LE_MULT_LCANCEL
            ==>   b ** SUC k <= b * (n DIV b)    by EXP
              and  b * (n DIV b) <= n            by DIV_MULT_LE
               or         b ** j <= n
*)

Theorem pop_property:
  !b n. 1 < b /\ 0 < n ==> !j. b ** j <= n <=> j < pop b n
Proof
  ho_match_mp_tac (theorem "pop_ind") >>
  rw[] >>
  Cases_on `n DIV b = 0` >| [
    `n < b` by rw[GSYM DIV_EQ_0] >>
    rw[Once pop_def] >>
    rw[Once pop_def] >>
    rw[EQ_IMP_THM] >>
    spose_not_then strip_assume_tac >>
    `0 < j` by decide_tac >>
    `b <= b ** j` by rw[X_LE_X_EXP] >>
    decide_tac,

    `~(n < b)` by rw[GSYM DIV_EQ_0] >>
    `b ** (j - 1) <= n DIV b <=> j - 1 < pop b (n DIV b)` by rw[] >>
    (Cases_on `j = 0` >> simp[Once pop_def, EXP_0]) >>
    rw[EQ_IMP_THM] >| [
      qabbrev_tac `k = j - 1` >>
      `j = SUC k` by rw[Abbr`k`] >>
      `(b * b ** k) DIV b <= n DIV b` by rw[DIV_LE_MONOTONE, GSYM EXP] >>
      `(b * b ** k) DIV b = b ** k` by rw[MULT_TO_DIV] >>
      `k < pop b (n DIV b)` by rw[] >>
      decide_tac,

      qabbrev_tac `k = j - 1` >>
      `j = SUC k` by rw[Abbr`k`] >>
      `k < pop b (n DIV b)` by decide_tac >>
      `b ** k <= n DIV b` by rw[] >>
      `b * (b ** k) <= b * (n DIV b)` by rw[] >>
      `b * b ** k = b ** j` by rw[EXP] >>
      `(n DIV b) * b <= n` by rw[DIV_MULT_LE] >>
      decide_tac
    ]
  ]
QED

(* Theorem: 1 < b ==> n < b ** pop b n *)
(* Proof:
   If n = 0, this is true            by EXP_POS, 1 < b.
   If n <> 0,
      Note     b ** (pop b n) <= n
           <=> pop b n < pop b n     by pop_property, 0 < n
           <=> F
      Thus n < b ** pop b n is true
*)
val pop_exceeds = store_thm(
  "pop_exceeds",
  ``!b n. 1 < b ==> n < b ** pop b n``,
  rpt strip_tac >>
  (Cases_on `n = 0` >> simp[]) >>
  metis_tac[pop_property, LESS_EQ_REFL, NOT_LESS, NOT_ZERO]);

(* Theorem: 1 < b ==> (n DIV b ** pop b n = 0) *)
(* Proof:
   Note n < b ** pop b n         by pop_exceeds
   Thus n DIV b ** pop b n = 0   by LESS_DIV_EQ_ZERO
*)
val pop_exceeds_div = store_thm(
  "pop_exceeds_div",
  ``!b n. 1 < b ==> (n DIV b ** pop b n = 0)``,
  rw[pop_exceeds, LESS_DIV_EQ_ZERO]);

(*
val foo_def = Define`
    foo m n = SUC (LOG b n)
`;

> EVAL ``MAP (pop 7) [1 .. 20]``; = [1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2]: thm
> EVAL ``MAP (foo 7) [1 .. 20]``; = [1; 1; 1; 1; 1; 1; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2]: thm
*)

(* Theorem: pop b n = if b <= 1 \/ (n = 0) then 0 else (1 + LOG b n) *)
(* Proof:
   By complete induction on n.
   If b <= 1, then pop b n = 0        by pop_def
   If n = 0, then pop b 0 = 0         by pop_def
   Otherwise, 1 < b and 0 < n.
   If n DIV b = 0,
      Then n < b                      by DIV_EQ_0
       LHS = pop b n
           = SUC (pop b (n DIV b))    by pop_def
           = SUC (pop b 0)            by n DIV b = 0
           = SUC 0 = 1                by pop_def, ADD1
       Now LOG b n = 0                by LOG_EQ_0, n < b
       RHS = 1 + 0 = 1 = LHS          by above
   If n DIV b <> 0,
      Then ~(n < b)                   by DIV_EQ_0
        or b <= n.
      If b = n,
       LHS = pop b b
           = SUC (pop b 1)            by pop_def, DIVMOD_ID
           = SUC (SUC 0) = 2          by pop_def, ADD1
       RHS = 1 + LOG b m = 2 = LHS    by LOG_BASE, 0 < m
      If b < n,
       LHS = pop b n
           = SUC (pop b (n DIV b))        by pop_def
           = SUC (LOG b (n DIV b) + 1)    by induction hypothesis
           = SUC (SUC (LOG b (n DIV b)))  by ADD1
           = SUC (LOG b n)                by ROOT_RWT
           = 1 + LOG b n = RHS            by ADD1
*)
val pop_eqn = store_thm(
  "pop_eqn",
  ``!b n. pop b n = if b <= 1 \/ (n = 0) then 0 else (1 + LOG b n)``,
  strip_tac >>
  completeInduct_on `n` >>
  Cases_on `b <= 1 \/ (n = 0)` >-
  rw[Once pop_def] >>
  fs[] >>
  `1 < b` by decide_tac >>
  rw[Once pop_def] >| [
    `n < b` by rw[GSYM DIV_EQ_0] >>
    rw[LOG_EQ_0],
    simp[GSYM ADD1] >>
    `~(n < b)` by rw[GSYM DIV_EQ_0] >>
    rw[LOG_RWT]
  ]);

(* Theorem: pop b n <= 1 + LOG b n *)
(* Proof: by pop_eqn *)
val pop_LOG = store_thm(
  "pop_LOG",
  ``!b n. pop b n <= 1 + LOG b n``,
  rw[pop_eqn]);

(*
> EVAL ``MAP size [0 .. 10]``;    = [1; 1; 2; 2; 3; 3; 3; 3; 4; 4; 4]: thm
> EVAL ``MAP (pop 2) [0 .. 10]``; = [0; 1; 2; 2; 3; 3; 3; 3; 4; 4; 4]: thm
*)

(* Theorem: pop 2 n = if n = 0 then 0 else size n *)
(* Proof:
   By complete induction on n.
   Base: pop 2 0 = 0, true            by pop_zero
   Step: !m. m < n ==> pop 2 m = if m = 0 then 0 else size m ==>
         n <> 0 ==> pop 2 n = size n
       Note HALF n < n                by HALF_LESS, 0 < n
       If HALF n = 0,
          Then n = 1                  by HALF_EQ_0, n <> 0
              pop 2 1
            = SUC (pop 2 0) = SUC 0   by pop_def
            = 1 = size 1              by size_1
       If HALF n <> 0,
          Then n <> 1, or 1 < n       by HALF_EQ_0, n <> 0
               pop 2 n
             = SUC (pop 2 (HALF n))   by pop_def
             = SUC (size (HALF n))    by induction hypothesis
             = size n                 by size_half_SUC
*)
val pop_2_size = store_thm(
  "pop_2_size",
  ``!n. pop 2 n = if n = 0 then 0 else size n``,
  completeInduct_on `n` >>
  rw[] >-
  rw[pop_zero] >>
  `HALF n < n` by rw[] >>
  rw[Once pop_def] >| [
    `n = 1` by fs[HALF_EQ_0] >>
    rw[],
    `n <> 1` by fs[HALF_EQ_0] >>
    rw[size_half_SUC]
  ]);

(* Theorem: pop b n <= size n *)
(* Proof:
   If n = 0,
      pop b 0 = 0 <= size 0    by pop_zero
   If b <= 1,
      pop b n = 0 <= size n    by pop_zero
   Otherwise, 1 < b and 0 < n.
      pop b n
   <= 1 + LOG b n      by pop_LOG
   <= 1 + LOG2 n       by LOG_LE_REVERSE, 2 <= m.
    = size n           by size_by_LOG2, 0 < n.
*)
val pop_size = store_thm(
  "pop_size",
  ``!b n. pop b n <= size n``,
  rpt strip_tac >>
  Cases_on `b <= 1 \/ (n = 0)` >| [
    fs[pop_zero] >>
    (`(b = 0) \/ (b = 1)` by decide_tac >> rw[pop_zero]),
    `pop b n <= 1 + LOG b n` by rw[pop_LOG] >>
    `1 + LOG b n <= 1 + LOG2 n` by rw[LOG_LE_REVERSE] >>
    `1 + LOG2 n = size n` by rw[size_by_LOG2] >>
    decide_tac
  ]);

(* Theorem: 1 < b ==> (pop b x = loop_count (\x. x = 0) (\x. x DIV b) x) *)
(* Proof:
   By induction from pop_def.
   Let guard = (\x. x = 0),
       modify = (\x. x DIV b),
       R = measure (\x. x).
   The goal is: pop b x = loop_count guard modify x

   Note WF R                               by WF_measure
    and !x. ~guard x ==> R (modify x) x    by x DIV b < x, 1 < b
   If guard x,
      Then x = 0                           by guard x
           pop b 0
         = 0                               by pop_0
         = loop_count guard modify 0       by loop_count_0, guard x
   If ~guard x,
      Then x <> 0                          by ~guard x
           pop b x
         = SUC (pop b (x DIV b))           by pop_suc
         = SUC (loop_count guard modify (x DIV b))
                                           by induction hypothesis
         = loop_count guard modify x       by loop_count_suc
*)
val pop_eq_loop_count = store_thm(
  "pop_eq_loop_count",
  ``!b x. 1 < b ==> (pop b x = loop_count (\x. x = 0) (\x. x DIV b) x)``,
  ho_match_mp_tac (theorem "pop_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x DIV b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`modify`, Abbr`R`] >>
  Cases_on `guard x` >| [
    `x = 0` by metis_tac[] >>
    metis_tac[pop_0, loop_count_0],
    `x <> 0` by metis_tac[] >>
    `pop b x = SUC (pop b (x DIV b))` by rw[pop_suc] >>
    `_ = SUC (loop_count guard modify (x DIV b))` by metis_tac[NOT_LESS] >>
    `_ = loop_count guard modify x` by metis_tac[loop_count_suc] >>
    decide_tac
  ]);

(* Theorem: 1 < b ==> (pop b y = loop2_count (\x y. y = 0) (\y. y DIV b) f x y) *)
(* Proof:
   By induction from pop_def.
   Let guard = (\x y. y = 0),
       modify = (\y. y DIV b),
       R = measure (\(x,y). y).
   The goal is: pop b y = loop2_count guard modify f x y

   Note WF R                                         by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)  by y DIV b < y, 0 < b
   If guard x y,
      Then y = 0                             by guard x y
           pop b 0
         = 0                                 by pop_0
         = loop2_count guard modify f x 0    by loop2_count_0, guard x y
   If ~guard x y,
      Then y <> 0                            by ~guard x y
           pop b y
         = SUC (pop b (y DIV b))             by pop_suc
         = SUC (loop2_count guard modify f (f x) (y DIV b))
                                             by induction hypothesis, take (f x).
         = loop2_count guard modify f x y    by loop2_count_suc
*)
val pop_eq_loop2_count = store_thm(
  "pop_eq_loop2_count",
  ``!b f x y. 1 < b ==> (pop b y = loop2_count (\x y. y = 0) (\y. y DIV b) f x y)``,
  ntac 4 strip_tac >>
  qid_spec_tac `x` >>
  qid_spec_tac `y` >>
  qid_spec_tac `b` >>
  ho_match_mp_tac (theorem "pop_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x y. y = 0` >>
  qabbrev_tac `modify = \y. y DIV b` >>
  qabbrev_tac `R = measure (\(x,y). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`modify`, Abbr`R`] >>
  Cases_on `guard x y` >| [
    `y = 0` by metis_tac[] >>
    metis_tac[pop_0, loop2_count_0],
    `y <> 0` by metis_tac[] >>
    `pop b y = SUC (pop b (y DIV b))` by rw[pop_suc] >>
    `_ = SUC (loop2_count guard modify f (f x) (y DIV b))` by metis_tac[NOT_LESS] >>
    `_ = loop2_count guard modify f x y` by metis_tac[loop2_count_suc] >>
    decide_tac
  ]);

(* Theorem: 0 < b ==> FALLING (\x. x DIV b) *)
(* Proof:
   By FALLING, this is to show:
      !x. x DIV b <= x, which is true    by DIV_LESS_EQ, 0 < b
*)
val divide_falling = store_thm(
  "divide_falling",
  ``!b. 0 < b ==> FALLING (\x. x DIV b)``,
  simp[DIV_LESS_EQ]);

(* Theorem: 0 < b ==> (FUNPOW (\x. x DIV b) n x = x DIV (b ** n)) *)
(* Proof:
   Let f = (\x. x DIV b).
   By induction on n.
   Base: !x. 0 < b ==> FUNPOW f 0 x = x DIV b ** 0
         FUNPOW f 0 x
       = x                  by FUNPOW_0
       = x DIV 1            by DIV_1
       = x DIV (b ** 0)     by EXP_0
   Step: !x. 0 < b ==> FUNPOW f n x = x DIV b ** n ==>
         !x. 0 < b ==> FUNPOW f (SUC n) x = x DIV b ** SUC n
         FUNPOW f (SUC n) x
       = x (FUNPOW f n x)      by FUNPOW_SUC
       = f (x DIV b ** n)      by induction hypothesis
       = (x DIV b ** n) DIV b  by function application
       = x DIV (b * b ** n)    by DIV_DIV_DIV_MULT
       = x DIV b ** SUC n      by EXP
*)
val iterating_div_eqn = store_thm(
  "iterating_div_eqn",
  ``!b n x. 0 < b ==> (FUNPOW (\x. x DIV b) n x = x DIV (b ** n))``,
  strip_tac >>
  Induct >-
  rw[EXP_0] >>
  rw[FUNPOW_SUC, DIV_DIV_DIV_MULT, EXP]);

(* Theorem:  1 < b ==> (FUNPOW (\x. x DIV b) (pop b x) x = 0) *)
(* Proof:
   Let guard = (\x. x = 0),
       modify = (\x. x DIV b),
       R = measure (\x. x).
   Then WF R                                   by WF_measure
    and !x. ~guard x ==> R (modify x) x        by DIV_LESS, x DIV b < x, 1 < b
   Note pop b x = loop_count guard modify x    by pop_eq_loop_count
    and guard (FUNPOW modify (loop_count guard modify x) x)   by loop_count_iterating
     or FUNPOW modify (loop_count guard modify x) x = 0       by guard
*)
val iterating_div_pop = store_thm(
  "iterating_div_pop",
  ``!b x. 1 < b ==> (FUNPOW (\x. x DIV b) (pop b x) x = 0)``,
  rw[pop_eq_loop_count] >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x DIV b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`modify`, Abbr`R`] >>
  metis_tac[loop_count_iterating]);

(* Theorem: 1 < b ==> x < b ** (pop b x) *)
(* Proof:
   Note 0 < b, so 0 < b ** (pop b x)             by EXP_POS
   Note FUNPOW (\x. x DIV b) (pop b x) x = 0     by iterating_div_pop, 1 < b
     or             x DIV b ** (pop b x) = 0     by iterating_div_eqn, 0 < b
     or                   x < b ** (pop b x)     by DIV_EQUAL_0, 0 <  b ** (pop b x)
*)
val iterating_div_pop_alt = store_thm(
  "iterating_div_pop_alt",
  ``!b x. 1 < b ==> x < b ** (pop b x)``,
  rpt strip_tac >>
  `0 < b` by decide_tac >>
  rw[iterating_div_pop, GSYM iterating_div_eqn, GSYM DIV_EQUAL_0]);

(* This is the same as pop_exceeds: |- !b n. 1 < b ==> n < b ** pop b n *)

(* ------------------------------------------------------------------------- *)
(* Dividing Loop                                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem:  1 < b /\
       (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
        !x. loop x = c + SUM (GENLIST (\j. body (x DIV b ** j)) (pop b x)) *)
(* Proof:
   Let guard = (\x. x = 0),
       modify = (\x. x DIV b),
       R = measure (\x. x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by DIV_LESS, x DIV b < x, 1 < b
   Let quit = (\x. c).
   Then !x. loop x = if guard x then quit x else body x + loop (modify x)
                                          by given
   Let f = (\j. body (FUNPOW modify j x)).
       n = loop_count guard modify x,
       z = FUNPOW modify n x.
   Note n = pop b x                       by pop_eq_loop_count
    and f = (\j. body (x DIV b ** j))     by iterating_div_eqn, FUN_EQ_THM
   Thus loop x
      = quit z + SUM (GENLIST f n)        by loop_modify_count_eqn
      = c + SUM (GENLIST (\j. body (x DIV b ** j)) (pop b x))
*)
val loop_div_count_eqn = store_thm(
  "loop_div_count_eqn",
  ``!loop body b c. 1 < b /\
       (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
        !x. loop x = c + SUM (GENLIST (\j. body (x DIV b ** j)) (pop b x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x DIV b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  qabbrev_tac `quit = \x:num. c` >>
  `!x. loop x = if guard x then quit x else body x + loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_eqn >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  `loop_count guard modify x = pop b x` by rw[pop_eq_loop_count, Abbr`guard`, Abbr`modify`] >>
  qabbrev_tac `u = \j. body (FUNPOW modify j x)` >>
  qabbrev_tac `v = \j. body (x DIV b ** j)` >>
  `u = v` by rw[FUN_EQ_THM, iterating_div_eqn, Abbr`modify`, Abbr`u`, Abbr`v`] >>
  metis_tac[]);

(* Theorem: 1 < b /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
        !x. loop x <= c + SUM (GENLIST (\j. body (x DIV b ** j)) (pop b x)) *)
(* Proof:
   Let guard = (\x. x = 0),
       modify = (\x. x DIV b),
       R = measure (\x. x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by DIV_LESS, x DIV b < x, 1 < b
   Let quit = (\x. c).
   Then !x. loop x = if guard x then quit x else body x + loop (modify x)
                                          by given
   Let f = (\j. body (FUNPOW modify j x)).
       n = loop_count guard modify x,
       z = FUNPOW modify n x.
   Note n = pop b x                       by pop_eq_loop_count
    and f = (\j. body (x DIV b ** j))     by iterating_div_eqn, FUN_EQ_THM
   Thus  loop x
      <= quit z + SUM (GENLIST f n)       by loop_modify_count_exit_le
       = c + SUM (GENLIST (\j. body (x DIV b ** j)) (pop b x))
*)
val loop_div_count_exit_sum_le = store_thm(
  "loop_div_count_exit_sum_le",
  ``!loop body exit b c. 1 < b /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
        !x. loop x <= c + SUM (GENLIST (\j. body (x DIV b ** j)) (pop b x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x DIV b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  qabbrev_tac `quit = \x:num. c` >>
  `!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  `loop_count guard modify x = pop b x` by rw[pop_eq_loop_count, Abbr`guard`, Abbr`modify`] >>
  qabbrev_tac `u = \j. body (FUNPOW modify j x)` >>
  qabbrev_tac `v = \j. body (x DIV b ** j)` >>
  `u = v` by rw[FUN_EQ_THM, iterating_div_eqn, Abbr`modify`, Abbr`u`, Abbr`v`] >>
  metis_tac[]);

(* Theorem: 1 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * cover x *)
(* Proof:
   Let guard = (\x. x = 0),
       modify = (\x. x DIV b),
       R = measure (\x. x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by DIV_LESS, x DIV b < x, 1 < b
    and FALLIG modify                     by divide_falling
   Let quit = (\x. c).
   Then !x. loop x = if guard x then quit x else body x + loop (modify x)
                                          by given
   Let n = loop_count guard modify x.
       z = FUNPOW modify n x.
       loop x
    <= quit z + n * cover x               by loop_fall_count_cover_exit_le, MONO cover
     = c + pop b x * cover x              by pop_eq_loop_count
*)
val loop_div_count_cover_exit_le = store_thm(
  "loop_div_count_cover_exit_le",
  ``!loop body cover exit b c. 1 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * cover x``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x DIV b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `FALLING modify` by rw[divide_falling, Abbr`modify`] >>
  qabbrev_tac `quit = \x:num. c` >>
  `!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_fall_count_cover_exit_le >>
  first_x_assum (qspecl_then [`x`, `cover`] strip_assume_tac) >>
  `loop_count guard modify x = pop b x` by rw[pop_eq_loop_count, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Other similar theorems -- directly *)

(* Theorem:  1 < b /\ MONO body /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * body x *)
(* Proof: by loop_div_count_cover_exit_le with cover = body. *)
val loop_div_count_exit_le = store_thm(
  "loop_div_count_exit_le",
  ``!loop body exit b c. 1 < b /\ MONO body /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * body x``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_div_count_cover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem: 1 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * cover x *)
(* Proof: by loop_div_count_cover_exit_le with exit = F. *)
val loop_div_count_cover_le = store_thm(
  "loop_div_count_cover_le",
  ``!loop body cover b c. 1 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * cover x``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num. F` >>
  `!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)` by metis_tac[] >>
  imp_res_tac loop_div_count_cover_exit_le >>
  first_x_assum (qspec_then`x` strip_assume_tac));

(* Theorem: 1 < b /\ MONO body /\
       (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * body x *)
(* Proof: by loop_div_count_cover_le with cover = body. *)
val loop_div_count_le = store_thm(
  "loop_div_count_le",
  ``!loop body b c. 1 < b /\ MONO body /\
       (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * body x``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_div_count_cover_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * cover 0 *)
(* Proof:
   Let guard = (\x. x = 0),
       modify = (\x. x DIV b),
       R = measure (\x. x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by DIV_LESS, x DIV b < x, 1 < b
    and FALLIG modify                     by divide_falling
   Let quit = (\x. c).
   Then !x. loop x = if guard x then quit x else body x + loop (modify x)
                                          by given
   Let n = loop_count guard modify x,
       z = FUNPOW modify n x.
       loop x
    <= quit z + n * cover (FUNPOW modify n x)    by loop_fall_count_rcover_exit_le, RMONO cover
     = c + n * cover (FUNPOW (\x. x DIV b) n x)  by q z = c
     = c + n * cover (x DIV b ** n)              by iterating_div_eqn
     = c + pop b x * cover (x DIV b ** pop b x)  by pop_eq_loop_count
     = c + pop b x * cover 0                     by pop_exceeds_div
*)
val loop_div_count_rcover_exit_le = store_thm(
  "loop_div_count_rcover_exit_le",
  ``!loop body cover exit b c. 1 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * cover 0``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x DIV b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `FALLING modify` by rw[divide_falling, Abbr`modify`] >>
  qabbrev_tac `quit = \x:num. c` >>
  `!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_fall_count_rcover_exit_le >>
  first_x_assum (qspecl_then [`x`, `cover`] strip_assume_tac) >>
  `loop_count guard modify x = pop b x` by rw[pop_eq_loop_count, Abbr`guard`, Abbr`modify`] >>
  qabbrev_tac `n = pop b x` >>
  `FUNPOW modify n x = x DIV b ** n` by rw[iterating_div_eqn, Abbr`modify`] >>
  `_ = 0` by rw[GSYM pop_exceeds_div, Abbr`n`] >>
  metis_tac[]);

(* Other similar theorems -- directly *)

(* Theorem: 1 < b /\ RMONO body /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * body 0 *)
(* Proof: by loop_div_count_rcover_exit_le with cover = body. *)
val loop_div_count_rbody_exit_le = store_thm(
  "loop_div_count_rbody_exit_le",
  ``!loop body exit b c. 1 < b /\ RMONO body /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * body 0``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_div_count_rcover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem: 1 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * cover 0 *)
(* Proof: by loop_div_count_rcover_exit_le with exit = F. *)
val loop_div_count_rcover_le = store_thm(
  "loop_div_count_rcover_le",
  ``!loop body cover b c. 1 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * cover 0``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num. F` >>
  `!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)` by metis_tac[] >>
  imp_res_tac loop_div_count_rcover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem: 1 < b /\ RMONO body /\
       (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * body 0 *)
(* Proof: by loop_div_count_rcover_le with cover = body. *)
val loop_div_count_rbody_le = store_thm(
  "loop_div_count_rbody_le",
  ``!loop body b c. 1 < b /\ RMONO body /\
       (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
        !x. loop x <= c + pop b x * body 0``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_div_count_rcover_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Dividing Loop with Transform                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
     !x y. loop x y = quit (FUNPOW f (pop b y) x) +
                      SUM (GENLIST (\j. body (FUNPOW f j x) (y DIV b ** j)) (pop b y)) *)
(* Proof:
   Let guard = (\x y. y = 0),
       modify = (\y. y DIV b),
       R = measure (\(x,y). y),
   Then WF R                                           by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)    by DIV_LESS, y DIV b < y, 1 < b
   Let quit2 = (\x y. quit x).
    and !x y. loop x y = if guard x y then quit2 x y else body x y + loop (f x) (modify y)   by given
   Let g = \j. body (FUNPOW f j x) (FUNPOW modify j y),
       n = loop2_count guard modify f x y,
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = pop b y                                    by pop_eq_loop2_count
    and g = (\j. body (FUNPOW f j x) (y DIV b ** j))   by iterating_div_eqn
        loop x y
      = quit2 p q + SUM (GENLIST g n)                  by loop2_modify_count_eqn
      = quit p + SUM (GENLIST g (pop b y))             by n = pop b y
      = quit (FUNPOW f (pop b y) x) + SUM (GENLIST (\j. body (FUNPOW f j x) (y DIV b ** j)) (pop b y))
*)
val loop2_div_count_eqn = store_thm(
  "loop2_div_count_eqn",
  ``!loop f body quit b. 1 < b /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
     !x y. loop x y = quit (FUNPOW f (pop b y) x) +
                      SUM (GENLIST (\j. body (FUNPOW f j x) (y DIV b ** j)) (pop b y))``,
  rpt strip_tac >>
  imp_res_tac pop_eq_loop2_count >>
  first_x_assum (qspecl_then [`y`, `x`, `f`] strip_assume_tac) >>
  qabbrev_tac `guard = \x y. y = 0` >>
  qabbrev_tac `modify = \y. y DIV b` >>
  qabbrev_tac `R = measure (\(x,y). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  qabbrev_tac `quit2 = \x y:num. quit x` >>
  `!x y. loop x y = if guard x y then quit2 x y else body x y + loop (f x) (modify y)` by metis_tac[] >>
  imp_res_tac loop2_modify_count_eqn >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `u = \j. body (FUNPOW f j x) (FUNPOW modify j y)` >>
  qabbrev_tac `v = \j. body (FUNPOW f j x) (y DIV b ** j)` >>
  `u = v` by rw[FUN_EQ_THM, iterating_div_eqn, Abbr`modify`, Abbr`u`, Abbr`v`] >>
  metis_tac[]);

(* Theorem: 1 < b /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) +
                       SUM (GENLIST (\j. body (FUNPOW f j x) (y DIV b ** j)) (pop b y)) *)
(* Proof:
   Let guard = (\x y. y = 0),
       modify = (\y. y DIV b),
       R = measure (\(x,y). y),
   Then WF R                                          by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)   by DIV_LESS, y DIV b < y, 1 < b
   Let quit2 = (\x y. quit x).
   Then !x y. loop x y = if guard x y then quit2 x y else body x y + if exit x y then 0 else loop (f x) (modify y)
                             by given
   Let g = \j. body (FUNPOW f j x) (FUNPOW modify j y),
       n = loop2_count guard modify f x y,
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = pop b y                                    by pop_eq_loop2_count
    and g = (\j. body (FUNPOW f j x) (y DIV b ** j))   by iterating_div_eqn
        loop x y
     <= quit2 p q + SUM (GENLIST g n)                  by loop2_modify_count_exit_le
      = quit p + SUM (GENLIST g (pop b y))             by n = pop b y
      = quit (FUNPOW f (pop b y) x) + SUM (GENLIST (\j. body (FUNPOW f j x) (y DIV b ** j)) (pop b y))
*)
val loop2_div_count_sum_le = store_thm(
  "loop2_div_count_sum_le",
  ``!loop f body quit exit b. 1 < b /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) +
                       SUM (GENLIST (\j. body (FUNPOW f j x) (y DIV b ** j)) (pop b y))``,
  rpt strip_tac >>
  imp_res_tac pop_eq_loop2_count >>
  first_x_assum (qspecl_then [`y`, `x`, `f`] strip_assume_tac) >>
  qabbrev_tac `guard = \x y. y = 0` >>
  qabbrev_tac `modify = \y. y DIV b` >>
  qabbrev_tac `R = measure (\(x,y). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  qabbrev_tac `quit2 = \x y:num. quit x` >>
  `!x y. loop x y = if guard x y then quit2 x y else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  imp_res_tac loop2_modify_count_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `u = \j. body (FUNPOW f j x) (FUNPOW modify j y)` >>
  qabbrev_tac `v = \j. body (FUNPOW f j x) (y DIV b ** j)` >>
  `u = v` by rw[FUN_EQ_THM, iterating_div_eqn, Abbr`modify`, Abbr`u`, Abbr`v`] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Dividing Loop with Transform-independent Body                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g y *)
(* Proof:
   Let n = pop b y, z = FUNPOW f n x.
      loop x y
   <= quit z + SUM (GENLIST (\j. body (FUNPOW f j x) (y DIV b ** j)) n)   by loop2_div_count_sum_le
   <= quit z + SUM (GENLIST (\j. cover (FUNPOW f j x) (y DIV b ** j)) n)  by SUM_LE, body cover
    = quit z + SUM (GENLIST (\j. g (y DIV b ** j)) n)   by expanding cover
   <= quit z + SUM (GENLIST (K (g y)) n)                by SUM_LE, MONO g, DIV_LESS_EQ
    = quit z + g y * n                                  by SUM_GENLIST_K
    = quit z + n * g y                                  by MULT_COMM
*)
val loop2_div_count_mono_cover_exit_le = store_thm(
  "loop2_div_count_mono_cover_exit_le",
  ``!loop f body quit cover exit b g. 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g y``,
  rpt strip_tac >>
  imp_res_tac loop2_div_count_sum_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = pop b y` >>
  `SUM (GENLIST (\j. body (FUNPOW f j x) (y DIV b ** j)) n) <=
    SUM (GENLIST (\j. cover (FUNPOW f j x) (y DIV b ** j)) n)` by fs[SUM_LE] >>
  `SUM (GENLIST (\j. cover (FUNPOW f j x) (y DIV b ** j)) n) <= SUM (GENLIST (K (g y)) n)` by rw[SUM_LE, DIV_LESS_EQ] >>
  `SUM (GENLIST (K (g y)) n) = g y * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Other similar theorems -- directly *)

(* Theorem: 1 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g y *)
(* Proof: by loop2_div_count_mono_cover_exit_le with cover = body. *)
val loop2_div_count_mono_exit_le = store_thm(
  "loop2_div_count_mono_exit_le",
  ``!loop f body quit exit b g. 1 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_div_count_mono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g y *)
(* Proof: by loop2_div_count_mono_cover_exit_le with exit = F. *)
val loop2_div_count_mono_cover_le = store_thm(
  "loop2_div_count_mono_cover_le",
  ``!loop f body quit cover b g. 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:'a y:num. F` >>
  `!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y DIV b)` by metis_tac[] >>
  imp_res_tac loop2_div_count_mono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g y *)
(* Proof: by loop2_div_count_mono_cover_le with cover = body. *)
val loop2_div_count_mono_le = store_thm(
  "loop2_div_count_mono_le",
  ``!loop f body quit b g. 1 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_div_count_mono_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g 0 *)
(* Proof:
   Let n = pop b y, z = FUNPOW f n x.
      loop x y
   <= quit z + SUM (GENLIST (\j. body (FUNPOW f j x) (y DIV b ** j)) n)   by loop2_div_count_sum_le
   <= quit z + SUM (GENLIST (\j. cover (FUNPOW f j x) (y DIV b ** j)) n)  by SUM_LE, body cover
    = quit z + SUM (GENLIST (\j. g (y DIV b ** j)) n)   by expanding cover
   <= quit z + SUM (GENLIST (K (g (y DIV b ** n))) n)   by SUM_LE, RMONO g, DIV_LE_MONOTONE_REVERSE
    = quit z + g (y DIV b ** n) * n                     by SUM_GENLIST_K
    = quit z + g 0 * n                                  by pop_exceeds_div
    = quit z + n * g 0                                  by MULT_COMM
*)
val loop2_div_count_rmono_cover_exit_le = store_thm(
  "loop2_div_count_rmono_cover_exit_le",
  ``!loop f body quit cover exit b g. 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g 0``,
  rpt strip_tac >>
  imp_res_tac loop2_div_count_sum_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = pop b y` >>
  `SUM (GENLIST (\j. body (FUNPOW f j x) (y DIV b ** j)) n) <=
    SUM (GENLIST (\j. cover (FUNPOW f j x) (y DIV b ** j)) n)` by fs[SUM_LE] >>
  `SUM (GENLIST (\j. cover (FUNPOW f j x) (y DIV b ** j)) n) <=
    SUM (GENLIST (K (g (y DIV b ** n))) n)` by rw[SUM_LE, DIV_LE_MONOTONE_REVERSE] >>
  `SUM (GENLIST (K (g (y DIV b ** n))) n) = g (y DIV b ** n) * n` by rw[SUM_GENLIST_K] >>
  `_ = g 0 * n` by rw[pop_exceeds_div, Abbr`n`] >>
  decide_tac);

(* Other similar theorems -- directly *)

(* Theorem: 1 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g 0 *)
(* Proof: by loop2_div_count_rmono_cover_exit_le with cover = body. *)
val loop2_div_count_rmono_exit_le = store_thm(
  "loop2_div_count_rmono_exit_le",
  ``!loop f body quit exit b g. 1 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g 0``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_div_count_rmono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g 0 *)
(* Proof: by loop2_div_count_rmono_cover_exit_le with exit = F. *)
val loop2_div_count_rmono_cover_le = store_thm(
  "loop2_div_count_rmono_cover_le",
  ``!loop f body quit cover b g. 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g 0``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:'a y:num. F` >>
  `!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y DIV b)` by metis_tac[] >>
  imp_res_tac loop2_div_count_rmono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g 0 *)
(* Proof: by loop2_div_count_rmono_cover_le with cover = body. *)
val loop2_div_count_rmono_le = store_thm(
  "loop2_div_count_rmono_le",
  ``!loop f body quit b g. 1 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
     !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * g 0``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_div_count_rmono_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Dividing Loop with Numeric Transform                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * cover (FUNPOW f (pop b y) x) y *)
(* Proof:
   Let guard = (\x y. y = 0),
       modify = (\y. y DIV b),
       R = measure (\(x,y). y),
   Then WF R                                           by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)    by DIV_LESS, y DIV b < y, 1 < b
   Let quit2 = (\x y. quit x).
   Then !x y. loop x y = if guard x y then quit2 x y else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                       by given
   Note FALLING modify                                 by divide_falling
   Let n = loop2_count guard modify f x y
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = pop b y                                    by pop_eq_loop2_count
        loop x y
     <= quit2 p q + n * cover (FUNPOW f n x) y         by loop2_rise_fall_count_cover_exit_le
      = quit p + (pop b y) * cover (FUNPOW f (pop b y) x) y
      = quit (FUNPOW f (pop b y) x) + (pop b y) * cover (FUNPOW f (pop b y) x) y
*)
val loop2_div_rise_count_cover_exit_le = store_thm(
  "loop2_div_rise_count_cover_exit_le",
  ``!loop f body quit cover exit b.
          1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * cover (FUNPOW f (pop b y) x) y``,
  rpt strip_tac >>
  assume_tac (pop_eq_loop2_count |> ISPEC ``b:num`` |> ISPEC ``f:num -> num``) >>
  first_x_assum (qspecl_then [`x`, `y`] strip_assume_tac) >>
  qabbrev_tac `guard = \x:num y. y = 0` >>
  qabbrev_tac `modify = \y. y DIV b` >>
  qabbrev_tac `R = measure (\(x:num,y:num). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  qabbrev_tac `quit2 = \x y:num. quit x` >>
  `!x y. loop x y = if guard x y then quit2 x y else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  `FALLING modify` by rw[divide_falling, Abbr`modify`] >>
  imp_res_tac loop2_rise_fall_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`, `cover`] strip_assume_tac) >>
  metis_tac[]);

(* Other similar theorems -- directly *)

(* Theorem: 1 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * body (FUNPOW f (pop b y) x) y *)
(* Proof: by loop2_div_rise_count_cover_exit_le with cover = body. *)
val loop2_div_rise_count_exit_le = store_thm(
  "loop2_div_rise_count_exit_le",
  ``!loop f body quit exit b. 1 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * body (FUNPOW f (pop b y) x) y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_div_rise_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * cover (FUNPOW f (pop b y) x) y *)
(* Proof: by loop2_div_rise_count_cover_exit_le with exit = F. *)
val loop2_div_rise_count_cover_le = store_thm(
  "loop2_div_rise_count_cover_le",
  ``!loop f body quit cover b.
          1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * cover (FUNPOW f (pop b y) x) y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  `!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y DIV b)` by metis_tac[] >>
  imp_res_tac loop2_div_rise_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * body (FUNPOW f (pop b y) x) y *)
(* Proof: by loop2_div_rise_count_cover_le with cover = body. *)
val loop2_div_rise_count_le = store_thm(
  "loop2_div_rise_count_le",
  ``!loop f body quit b. 1 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * body (FUNPOW f (pop b y) x) y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_div_rise_count_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * cover x y *)
(* Proof:
   Let guard = (\x y. y = 0),
       modify = (\y. y DIV b),
       R = measure (\(x,y). y),
   Then WF R                                            by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by DIV_LESS, y DIV b < y, 1 < b
   Let quit2 = (\x y. quit x).
   Then !x y. loop x y = if guard x y then quit2 x y else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                        by given
   Note FALLING modify                                  by divide_falling
   Let n = loop2_count guard modify f x y
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = pop b y                                     by pop_eq_loop2_count
        loop x y
     <= quit2 p q + n * cover x y                       by loop2_fall_fall_count_cover_exit_le
      = quit p + (pop b y) * cover x y                  by n = pop b y
      = quit (FUNPOW f (pop b y) x) + (pop b y) * cover x y
*)
val loop2_div_fall_count_cover_exit_le = store_thm(
  "loop2_div_fall_count_cover_exit_le",
  ``!loop f body quit cover exit b.
          1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * cover x y``,
  rpt strip_tac >>
  assume_tac (pop_eq_loop2_count |> ISPEC ``b:num`` |> ISPEC ``f:num -> num``) >>
  first_x_assum (qspecl_then [`x`, `y`] strip_assume_tac) >>
  qabbrev_tac `guard = \x:num y. y = 0` >>
  qabbrev_tac `modify = \y. y DIV b` >>
  qabbrev_tac `R = measure (\(x:num,y:num). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  qabbrev_tac `quit2 = \x y:num. quit x` >>
  `!x y. loop x y = if guard x y then quit2 x y else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  `FALLING modify` by rw[divide_falling, Abbr`modify`] >>
  assume_tac loop2_fall_fall_count_cover_exit_le >>
  first_x_assum (qspecl_then [`loop`, `guard`, `body`, `quit2`, `exit`, `modify`, `f`, `R`] strip_assume_tac) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`x`, `y`, `cover`] strip_assume_tac) >>
  metis_tac[]);

(* Other similar theorems -- directly *)

(* Theorem: 1 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * body x y *)
(* Proof: by loop2_div_fall_count_cover_exit_le with cover = body. *)
val loop2_div_fall_count_exit_le = store_thm(
  "loop2_div_fall_count_exit_le",
  ``!loop f body quit exit b. 1 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * body x y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_div_fall_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * cover x y *)
(* Proof: by loop2_div_fall_count_cover_exit_le with exit = F. *)
val loop2_div_fall_count_cover_le = store_thm(
  "loop2_div_fall_count_cover_le",
  ``!loop f body quit cover b.
          1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * cover x y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  `!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y DIV b)` by metis_tac[] >>
  imp_res_tac loop2_div_fall_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * body x y *)
(* Proof: by loop2_div_fall_count_cover_le with cover = body. *)
val loop2_div_fall_count_le = store_thm(
  "loop2_div_fall_count_le",
  ``!loop f body quit b. 1 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + (pop b y) * body x y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_div_fall_count_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Dividing Loop with Transform cover                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * cover (FUNPOW g (pop b y) x) y *)
(* Proof:
   Let n = pop b y,
       f1 = (\j. body (FUNPOW f j x) (y DIV b ** j)),
       f2 = K (cover (FUNPOW g n x) y).

   Claim: SUM (GENLIST f1 n) <= SUM (GENLIST f2 n)
   Proof: By SUM_LE, LENGTH_MAP, EL_MAP,
          this is to show: k < n ==>
            body (FUNPOW f k x) (y DIV b ** k) <= cover (FUNPOW g n x) y
          Note 0 < b ** k                             by EXP_POS, 0 < b
           and y DIV b ** k <= y                      by DIV_LESS_EQ, 0 < b ** k
           Now FUNPOW f k x <= FUNPOW g k x           by FUNPOW_LE_MONO, MONO g
           and FUNPOW g k x <= FUNPOW g n x           by FUNPOW_LE_RISING, k < n, RISING g
          Thus body (FUNPOW f k x) (y DIV b ** k)
            <= cover (FUNPOW f k x) (y DIV b ** k)    by body and cover property
            <= cover (FUNPOW g n x) y                 by MONO2 cover

   Let p = FUNPOW f (pop b y) x.
        loop x y
     <= quit p + SUM (GENLIST f1 n)                           by loop2_div_count_sum_le
     <= quit p + SUM (GENLIST f2 n)                           by claim
      = quit p + SUM (GENLIST (K cover (FUNPOW g n x) y) n)   by notation
      = quit p + n * cover (FUNPOW g n x)                     by SUM_GENLIST_K
      = quit p + (pop b y) * cover (FUNPOW g (pop b y) x) y   by notation
*)
val loop2_div_mono_count_cover_exit_le = store_thm(
  "loop2_div_mono_count_cover_exit_le",
  ``!loop f g body quit cover exit b.
          1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * cover (FUNPOW g (pop b y) x) y``,
  rpt strip_tac >>
  imp_res_tac loop2_div_count_sum_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = pop b y` >>
  qabbrev_tac `f1 = \j. body (FUNPOW f j x) (y DIV b ** j)` >>
  qabbrev_tac `f2:num -> num = K (cover (FUNPOW g n x) y)` >>
  `SUM (GENLIST f1 n) <= SUM (GENLIST f2 n)` by
  (irule SUM_LE >>
  rw[Abbr`f1`, Abbr`f2`] >>
  `y DIV b ** k <= y` by rw[DIV_LESS_EQ] >>
  `FUNPOW f k x <= FUNPOW g k x` by rw[FUNPOW_LE_MONO] >>
  `FUNPOW g k x <= FUNPOW g n x` by rw[FUNPOW_LE_RISING] >>
  `FUNPOW f k x <= FUNPOW g n x` by decide_tac >>
  `body (FUNPOW f k x) (y DIV b ** k) <= cover (FUNPOW f k x) (y DIV b ** k)` by rw[] >>
  `cover (FUNPOW f k x) (y DIV b ** k) <= cover (FUNPOW g n x) y` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST f2 n) = n * cover (FUNPOW g n x) y` by rw[SUM_GENLIST_K, Abbr`f2`] >>
  decide_tac);

(* Note:
There is no corresponding theorem for RMONO g and FALLING g,
because there is no FUNPOW_LE_RMONO.
*)

(* Other similar theorems -- directly *)

(* Theorem: 1 < b /\ MONO2 body /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * body (FUNPOW g (pop b y) x) y *)
(* Proof: by loop2_div_mono_count_cover_exit_le with cover = body. *)
val loop2_div_mono_count_exit_le = store_thm(
  "loop2_div_mono_count_exit_le",
  ``!loop f g body quit exit b. 1 < b /\ MONO2 body /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if y = 0 then quit x
                 else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * body (FUNPOW g (pop b y) x) y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_div_mono_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * cover (FUNPOW g (pop b y) x) y *)
(* Proof: by loop2_div_mono_count_cover_exit_le with exit = F. *)
val loop2_div_mono_count_cover_le = store_thm(
  "loop2_div_mono_count_cover_le",
  ``!loop f g body quit cover b.
          1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * cover (FUNPOW g (pop b y) x) y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  `!x y. loop x y = if y = 0 then quit x else body x y + if exit x y then 0 else loop (f x) (y DIV b)` by metis_tac[] >>
  imp_res_tac loop2_div_mono_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\ MONO2 body /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * body (FUNPOW g (pop b y) x) y *)
(* Proof: by loop2_div_mono_count_cover_le with cover = body. *)
val loop2_div_mono_count_le = store_thm(
  "loop2_div_mono_count_le",
  ``!loop f g body quit b. 1 < b /\ MONO2 body /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if y = 0 then quit x else body x y + loop (f x) (y DIV b)) ==>
           !x y. loop x y <= quit (FUNPOW f (pop b y) x) + pop b y * body (FUNPOW g (pop b y) x) y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_div_mono_count_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Original investigation, some with quit = constant.                        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Dividing List.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Given a number n, generate a dividing list of n, down to before 0. *)
val divide_by_def = Define`
    divide_by b n =
       if (b <= 1) \/ (n = 0) then [] else n::divide_by b (n DIV b)
`;
(* Overload divide_by 2 *)
val _ = overload_on ("halving", ``divide_by 2``);

(*
EVAL ``halving 10``; = [10; 5; 2; 1]: thm
*)

(* Theorem: (b = 0) \/ (n = 0) ==> (divide_by b n = []) *)
(* Proof: by divide_by_def *)
val divide_by_nil = store_thm(
  "divide_by_nil",
  ``!b n. (b <= 1) \/ (n = 0) ==> (divide_by b n = [])``,
  rw[Once divide_by_def]);

(* Theorem: 0 < b /\ 0 < n ==> (divide_by b n = n::divide_by b (n DIV b)) *)
(* Proof: by divide_by_def *)
val divide_by_cons = store_thm(
  "divide_by_cons",
  ``!b n. 1 < b /\ 0 < n ==> (divide_by b n = n::divide_by b (n DIV b))``,
  rw[Once divide_by_def]);

(* Theorem: divide_by 0 n = [] *)
(* Proof: by divide_by_def *)
val divide_by_0_n = store_thm(
  "divide_by_0_n",
  ``!n. divide_by 0 n = []``,
  rw[Once divide_by_def]);

(* Theorem: divide_by 1 n = [] *)
(* Proof: by divide_by_def *)
val divide_by_1_n = store_thm(
  "divide_by_1_n",
  ``!n. divide_by 1 n = []``,
  rw[Once divide_by_def]);

(* Theorem: divide_by b 0 = [] *)
(* Proof: by divide_by_def *)
val divide_by_b_0 = store_thm(
  "divide_by_b_0",
  ``!b. divide_by b 0 = []``,
  rw[Once divide_by_def]);

(* Theorem: 1 < b /\ n <> 0 ==> (divide_by b n = n :: divide_by b (n DIV b)) *)
(* Proof: by divide_by_def *)
val divide_by_b_nonzero = store_thm(
  "divide_by_b_nonzero",
  ``!b n. 1 < b /\ n <> 0 ==> (divide_by b n = n :: divide_by b (n DIV b))``,
  rw[Once divide_by_def]);

(*
> EVAL ``divide_by 3 10``; = [10; 3; 1]: thm
> EVAL ``GENLIST (\j. 10 DIV 3 ** j) (pop 3 10)``; = [10; 3; 1]: thm
> EVAL ``divide_by 3 27``; = [27; 9; 3; 1]: thm
> EVAL ``GENLIST (\j. 27 DIV 3 ** j) (pop 3 27)``; = [27; 9; 3; 1]: thm
*)

(* Theorem: divide_by b n = GENLIST (\j. n DIV b ** j) (pop b n) *)
(* Proof:
   Let f = (\j. n DIV b DIV b ** j), g = (\j. n DIV b ** j).
   Note f = g o SUC                    by FUN_EQ_THM, DIV_DIV_DIV_MULT, EXP
    and g 0 = n DIV 1 = n              by DIV_1
   By induction from definition, this is to show:
   (1) b <= 1 ==> [] = GENLIST g (pop b n)
       Note pop b n = 0                by divide_by_def, b <= 1
        and GENLIST g 0 = []           by GENLIST_0
   (2) [] = GENLIST (\j. 0 DIV b ** j) (pop b 0)
       Note pop b 0 = 0                by divide_by_def, n = 0
        and GENLIST g 0 = []           by GENLIST_0
   (3) 1 < b /\ 0 < n,
       divide_by b (n DIV b) = GENLIST f (pop b (n DIV b)) ==>
       divide_by b n = GENLIST g (pop b n)

         divide_by b n
       = n :: divide_by b (n DIV b)                  by divide_by_def
       = n :: GENLIST f (pop b (n DIV b))            by induction hypothesis
       = g 0 :: GENLIST (g o SUC) (pop b (n DIV b))  by above
       = GENLIST g (SUC (pop b (n DIV b)))           by GENLIST_CONS
       = GENLIST g (pop b n)                         by pop_def
*)
val divide_by_eqn = store_thm(
  "divide_by_eqn",
  ``!b n. divide_by b n = GENLIST (\j. n DIV b ** j) (pop b n)``,
  ho_match_mp_tac (theorem "divide_by_ind") >>
  rw[] >>
  rw[Once divide_by_def] >-
  rw[Once pop_def] >-
  rw[Once pop_def] >>
  `~(b <= 1) /\ n <> 0` by decide_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  `1 < b /\ 0 < n` by decide_tac >>
  qabbrev_tac `f = \j. n DIV b DIV b ** j` >>
  qabbrev_tac `g = \j. n DIV b ** j` >>
  `f = g o SUC` by rw[FUN_EQ_THM, ADD1, DIV_DIV_DIV_MULT, EXP, Abbr`f`, Abbr`g`] >>
  `n :: GENLIST f (pop b (n DIV b))  = g 0 :: GENLIST (g o SUC) (pop b (n DIV b))` by rw[EXP_0, Abbr`g`] >>
  `_ = GENLIST g (SUC (pop b (n DIV b)))` by rw[GENLIST_CONS] >>
  `_ = GENLIST g (pop b n)` by metis_tac[pop_def] >>
  rw[]);

(* Theorem: 1 < b /\ 0 < n /\ b ** j <= n ==> MEM (n DIV (b ** j)) (divide_by b n) *)
(* Proof:
       MEM (n DIV b ** j) (divide_by b n)
   <=> MEM (n DIV b ** j) (GENLIST (\j. n DIV b ** j) (pop b n))   by divide_by_eqn
   <=> ?m. m < pop b n /\ n DIV b ** j = n DIV b ** m              by MEM_GENLIST
   <=> take m = j, with j < pop b n                                by pop_property
*)
val divide_by_member = store_thm(
  "divide_by_member",
  ``!b n j. 1 < b /\ 0 < n /\ b ** j <= n ==> MEM (n DIV (b ** j)) (divide_by b n)``,
  rw[divide_by_eqn] >>
  rw[MEM_GENLIST] >>
  metis_tac[pop_property]);

(* Theorem: 1 < b /\ 0 < n ==> MEM n (divide_by b n) *)
(* Proof: by divide_by_member, EXP_0, DIV_1 *)
val divide_by_head = store_thm(
  "divide_by_head",
  ``!b n. 1 < b /\ 0 < n ==> MEM n (divide_by b n)``,
  metis_tac[divide_by_member, EXP_0, DIV_1, DECIDE``0 < n <=> 1 <= n``]);

(* Theorem: LENGTH (divide_by b n) = pop b n *)
(* Proof:
   Let f = (\j. n DIV b ** j).
     LENGTH (divide_by b n)
   = LENGTH (GENLIST f (pop b n))    by divide_by_eqn
   = pop b n                         by LENGTH_GENLIST
*)
val divide_by_length = store_thm(
  "divide_by_length",
  ``!b n. LENGTH (divide_by b n) = pop b n``,
  rw[divide_by_eqn, LENGTH_GENLIST]);

(* Theorem: j < pop b n ==> (EL j (divide_by b n) = n DIV b ** j) *)
(* Proof:
   Let g = (\j. n DIV b ** j).
     EL j (divide_by b n)
   = EL j (GENLIST g (pop b n))   by divide_by_eqn
   = g j                          by EL_GENLIST, j < pop b n
   = n DIV b ** j                 by notation
*)
val divide_by_element = store_thm(
  "divide_by_element",
  ``!b n j. j < pop b n ==> (EL j (divide_by b n) = n DIV b ** j)``,
  rw[divide_by_eqn]);

(* Theorem: 1 < b ==> (divide_by b x = loop_arg (\x. x = 0) (\x. x DIV b) x) *)
(* Proof:
   By induction from divide_by_def.
   Let guard = (\x. x = 0),
       modify = (\x. x DIV b),
       R = measure (\x. x).
   The goal is: divide_by b x = loop_arg guard modify x
   Then WF R                                by WF_measure
    and !x. ~guard x ==> R (modify x) x     by x DIV b < x, 1 < b

   If guard x,
      Then x = 0                            by guard x
           divide_by b 0
         = []                               by divide_by_nil
         = loop_arg guard modify 0          by loop_arg_nil
   If ~guard x,
      Then x <> 0                                by ~guard x
           divide_by b x
         = x :: divide_by b (x DIV b)            by divide_by_cons
         = x :: loop_arg guard modify (x DIV b)  by induction hypothesis
         = loop_arg guard modify x               by loop_arg_cons, ~guard x
*)
val divide_by_eq_loop_arg = store_thm(
  "divide_by_eq_loop_arg",
  ``!b x. 1 < b ==> (divide_by b x = loop_arg (\x. x = 0) (\x. x DIV b) x)``,
  ho_match_mp_tac (theorem "divide_by_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x DIV b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`modify`, Abbr`R`] >>
  Cases_on `guard x` >| [
    `x = 0` by metis_tac[] >>
    metis_tac[divide_by_nil, loop_arg_nil],
    `x <> 0` by metis_tac[] >>
    `divide_by b x = x :: divide_by b (x DIV b)` by rw[divide_by_cons] >>
    `_ = x :: loop_arg guard modify (x DIV b)` by metis_tac[NOT_LESS] >>
    `_ = loop_arg guard modify x` by metis_tac[loop_arg_cons] >>
    rw[]
  ]);

(* Theorem: 1 < b ==> (MAP2 body (iterating f x (pop b y)) (divide_by b y) =
                       MAP (UNCURRY body) (loop2_arg (\x y. y = 0) (\y. y DIV b) f x y)) *)
(* Proof:
   By induction from divide_by_def.
   Let guard = (\x y. y = 0),
       modify = (\y. y DIV b),
       R = measure (\(x,y). y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by DIV_LESS, 1 < b

   If guard x y,
      Then y = 0                                by notation
      LHS = MAP2 body (iterating f x (pop b 0)) (divide_by b 0)
          = MAP2 body (iterating f x 0) []      by pop_0, divide_by_nil
          = MAP2 body [] []                     by iterating_nil
          = []                                  by MAP2
      RHS = MAP (UNCURRY body) (loop2_arg guard modify f x y)
          = MAP (UNCURRY body) []               by loop2_arg_nil, guard x y
          = [] = LHS                            by MAP

   If ~guard x y,
     Then y <> 0                                by notation
            MAP2 body (iterating f x (pop b y)) (divide_by b y)
          = MAP2 body (iterating f x (SUC (pop b (y DIV b)))) (y::divide_by b (y DIV b))
                                                by pop_suc, divide_by_cons
          = MAP2 body (x::iterating f (f x) (pop b (y DIV b))) (y::divide_by b (y DIV b))
                                                by iterating_cons
          = body x y::MAP2 body (iterating f (f x) (pop b (y DIV b))) (divide_by b (y DIV b))
                                                by MAP2
          = body x y::MAP (UNCURRY body) (loop2_arg guard modify f (f x) (y DIV b))
                                                by induction hypothesis
          = MAP (UNCURRY body) ((x,y):: loop2_arg guard modify f (f x) (y DIV b))
                                                by MAP, UNCURRY
          = MAP (UNCURRY body) (loop2_arg guard modify f x y)
                                                by loop2_arg_cons
*)
val iterating_divide_eq_loop2_arg = store_thm(
  "iterating_divide_eq_loop2_arg",
  ``!b body f x y. 1 < b ==>
    (MAP2 body (iterating f x (pop b y)) (divide_by b y) =
     MAP (UNCURRY body) (loop2_arg (\x y. y = 0) (\y. y DIV b) f x y))``,
  ntac 5 strip_tac >>
  qid_spec_tac `x` >>
  qid_spec_tac `y` >>
  qid_spec_tac `b` >>
  ho_match_mp_tac (theorem "divide_by_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x y. y = 0` >>
  qabbrev_tac `modify = \y. y DIV b` >>
  qabbrev_tac `R = measure (\(x,y). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  Cases_on `guard x y` >| [
    `y = 0` by metis_tac[] >>
    rw[iterating_nil, pop_0, divide_by_nil] >>
    metis_tac[loop2_arg_nil],
    `y <> 0` by metis_tac[] >>
    rw[iterating_cons, pop_suc, divide_by_cons] >>
    `body x y:: MAP2 body (iterating f (f x) (pop b (modify y))) (divide_by b (modify y)) =
    body x y:: MAP2 body (iterating f (f x) (pop b (y DIV b))) (divide_by b (y DIV b))` by rw[Abbr`modify`] >>
    `_ = body x y::MAP (UNCURRY body) (loop2_arg guard modify f (f x) (y DIV b))` by metis_tac[NOT_LESS] >>
    `_ = MAP (UNCURRY body) ((x,y)::loop2_arg guard modify f (f x) (modify y))` by rw[Abbr`modify`] >>
    metis_tac[loop2_arg_cons]
  ]);

(* ------------------------------------------------------------------------- *)
(* Dividing Loop -- original                                                 *)
(* ------------------------------------------------------------------------- *)

(*
loop_modify_count_by_sum |> SPEC_ALL |> INST_TYPE [alpha |-> ``:num``]
                |> Q.INST [`modify` |-> `(\x. x DIV b)`, `guard` |-> `(\x. x = 0)`, `R` |-> `measure (\x. x)`]
               |>  ADD_ASSUM ``1 < b`` |> DISCH_ALL
               |> SIMP_RULE (srw_ss()) [GSYM divide_by_eq_loop_arg];
-- the last one will not work, due to loop being recursive.
*)

(* Theorem: 1 < b /\
            (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
             !x. loop x = c + SUM (MAP body (divide_by b x)) *)
(* Proof:
   Let guard = (\x. x = 0),
       modify = (\x. x DIV b),
       R = measure (\x. x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by DIV_LESS, x DIV b < x, 1 < b
   Also !x. loop x = if guard x then c else body x + loop (modify x)
                                          by given
   Thus loop x
      = c + SUM (MAP body (loop_arg guard modify x))  by loop_modify_count_by_sum
      = c + SUM (MAP body (divide_by b x))            by divide_by_eq_loop_arg
*)
val loop_div_count_by_sum = store_thm(
  "loop_div_count_by_sum",
  ``!loop body b c. 1 < b /\
   (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
     !x. loop x = c + SUM (MAP body (divide_by b x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x DIV b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x. loop x = if guard x then c else body x + loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_by_sum >>
  `loop_arg guard modify x = divide_by b x` by rw[divide_by_eq_loop_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 1 < b /\
            (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
             !x. loop x <= c + SUM (MAP body (divide_by b x)) *)
(* Proof:
   Let guard = (\x. x = 0),
       modify = (\x. x DIV b),
       R = measure (\x. x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by DIV_LESS, x DIV b < x, 1 < b
   Also !x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)
                                          by given
   Thus loop x
     <= c + SUM (MAP body (loop_arg guard modify x))  by loop_modify_count_exit_by_sum
      = c + SUM (MAP body (divide_by b x))            by divide_by_eq_loop_arg
*)
val loop_div_count_exit_by_sum = store_thm(
  "loop_div_count_exit_by_sum",
  ``!loop body b c exit. 1 < b /\
   (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
     !x. loop x <= c + SUM (MAP body (divide_by b x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0` >>
  qabbrev_tac `modify = \x. x DIV b` >>
  qabbrev_tac `R = measure (\x. x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_exit_by_sum >>
  `loop_arg guard modify x = divide_by b x` by rw[divide_by_eq_loop_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem:  1 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
        !x. loop x <= c + cover x * pop b x *)
(* Proof:
   Let ls = divide_by b x.
       loop x
    <= c + SUM (MAP body ls)       by loop_div_count_exit_by_sum
    <= SUM (MAP (K (cover n)) ls)  by SUM_LE, divide_by_length, divide_by_element, MONO cover
     = (cover x) * LENGTH ls       by SUM_MAP_K
     = (cover x) * (pop b x)       by divide_by_length
*)
val loop_div_count_cover_exit_upper = store_thm(
  "loop_div_count_cover_exit_upper",
  ``!loop body cover exit b c. 1 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
        !x. loop x <= c + cover x * pop b x``,
  rpt strip_tac >>
  qabbrev_tac `ls = divide_by b x` >>
  `loop x <= c + SUM (MAP body ls)` by metis_tac[loop_div_count_exit_by_sum] >>
  `SUM (MAP body ls) <= SUM (MAP (K (cover x)) ls)` by
  (irule SUM_LE >>
  rw[divide_by_length, divide_by_element, EL_MAP, Abbr`ls`] >>
  `x DIV b ** k <= x` by rw[DIV_LESS_EQ] >>
  `body (x DIV b ** k) <= cover (x DIV b ** k)` by rw[] >>
  `cover (x DIV b ** k) <= cover x` by rw[] >>
  decide_tac) >>
  `SUM (MAP (K (cover x)) ls) = (cover x) * LENGTH ls` by rw[SUM_MAP_K] >>
  `_ = (cover x) * (pop b x)` by rw[divide_by_length, Abbr`ls`] >>
  decide_tac);

(* Theorem: 1 < b /\ MONO body /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
        !x. loop x <= c + body x * pop b x *)
(* Proof: by loop_div_count_cover_exit_upper with cover = body. *)
val loop_div_count_exit_upper = store_thm(
  "loop_div_count_exit_upper",
  ``!loop body b c exit. 1 < b /\ MONO body /\
       (!x. loop x = if x = 0 then c else body x + if exit x then 0 else loop (x DIV b)) ==>
        !x. loop x <= c + body x * pop b x``,
  metis_tac[loop_div_count_cover_exit_upper, LESS_EQ_REFL]);

(* Theorem: 1 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
        !x. loop x <= c + cover x * pop b x *)
(* Proof: by loop_div_count_cover_exit_upper with exit = F. *)
val loop_div_count_cover_upper = store_thm(
  "loop_div_count_cover_upper",
  ``!loop body b c cover. 1 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
        !x. loop x <= c + cover x * pop b x``,
  rpt strip_tac >>
  qabbrev_tac `exit = (\x:num. F)` >>
  metis_tac[loop_div_count_cover_exit_upper]);

(* Theorem: 1 < b /\ MONO body /\
       (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
        !x. loop x <= c + body x * pop b x *)
(* Proof: by loop_div_count_cover_upper with body = cover. *)
val loop_div_count_upper = store_thm(
  "loop_div_count_upper",
  ``!loop body b c. 1 < b /\ MONO body /\
       (!x. loop x = if x = 0 then c else body x + loop (x DIV b)) ==>
        !x. loop x <= c + body x * pop b x``,
  metis_tac[loop_div_count_cover_upper, LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)
(* Dividing Loop with Transform -- original                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\
    (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y DIV b)) ==>
     !x y. loop x y = c + SUM (MAP2 body (iterating f x (pop b y)) (divide_by b y)) *)
(* Proof:
   Let guard = (\x y. y = 0),
       modify = (\y. y DIV b),
       R = measure (\(x,y). y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by x DIV b < x, 1 < b
    and !x y. loop x y = if guard x y then c else body x y + loop (f x) (modify y)   by given
        loop x y
      = c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))     by loop2_modify_count_by_sum
      = c + SUM (MAP2 body (iterating f x (pop b y)) (divide_by b y))   by iterating_divide_eq_loop2_arg
*)
val loop2_div_count_by_sum = store_thm(
  "loop2_div_count_by_sum",
  ``!loop f body b c. 1 < b /\
    (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y DIV b)) ==>
     !x y. loop x y = c + SUM (MAP2 body (iterating f x (pop b y)) (divide_by b y))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. y = 0` >>
  qabbrev_tac `modify = \y. y DIV b` >>
  qabbrev_tac `R = measure (\(x,y). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x y. loop x y = if guard x y then c else body x y + loop (f x) (modify y)` by metis_tac[] >>
  `loop x y = c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))` by metis_tac[loop2_modify_count_by_sum] >>
  `MAP (UNCURRY body) (loop2_arg guard modify f x y) =
    MAP2 body (iterating f x (pop b y)) (divide_by b y)` by rw[iterating_divide_eq_loop2_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 1 < b /\
    (!x y. loop x y = if y = 0 then c else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
     !x y. loop x y <= c + SUM (MAP2 body (iterating f x (pop b y)) (divide_by b y)) *)
(* Proof:
   Let guard = (\x y. y = 0),
       modify = (\y. y DIV b),
       R = measure (\(x,y). y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by x DIV b < x, 1 < b
    and !x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                      by given
        loop x y
     <= c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))     by loop2_modify_count_exit_by_sum
      = c + SUM (MAP2 body (iterating f x (pop b y)) (divide_by b y))   by iterating_divide_eq_loop2_arg
*)
val loop2_div_count_exit_by_sum = store_thm(
  "loop2_div_count_exit_by_sum",
  ``!loop f body b c exit. 1 < b /\
    (!x y. loop x y = if y = 0 then c else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
     !x y. loop x y <= c + SUM (MAP2 body (iterating f x (pop b y)) (divide_by b y))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. y = 0` >>
  qabbrev_tac `modify = \y. y DIV b` >>
  qabbrev_tac `R = measure (\(x,y). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  assume_tac (loop2_modify_count_exit_by_sum |> ISPEC ``loop:'a -> num -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `exit`, `modify`, `f`, `R`] strip_assume_tac) >>
  `loop x y <= c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))` by metis_tac[] >>
  `MAP (UNCURRY body) (loop2_arg guard modify f x y) =
    MAP2 body (iterating f x (pop b y)) (divide_by b y)` by rw[iterating_divide_eq_loop2_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x1 y1 <= cover x2 y2) /\
       (!x y. loop x y = if y = 0 then c else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
        !x y. loop x y <= c + cover x y * pop b y *)
(* Proof:
   Let guard = (\x y. y = 0),
       modify = (\y. y DIV b),
       R = measure (\(x,y). y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)    by x DIV b < x, 1 < b
    and !x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> cover x1 y1 <= cover x2 y2    by R
    and !x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                       by given
        loop x y
     <= c + cover x y * loop2_count guard modify f x y       by loop2_modify_count_bcover_exit_upper
      = c + cover x y * pop b y                              by pop_eq_loop2_count
*)
val loop2_div_count_cover_exit_upper = store_thm(
  "loop2_div_count_cover_exit_upper",
  ``!loop f body cover exit b c. 1 < b /\
       (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x1 y1 <= cover x2 y2) /\
       (!x y. loop x y = if y = 0 then c else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
        !x y. loop x y <= c + cover x y * pop b y``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. y = 0` >>
  qabbrev_tac `modify = \y. y DIV b` >>
  qabbrev_tac `R = measure (\(x,y). y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> cover x1 y1 <= cover x2 y2` by rw[Abbr`R`] >>
  `!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  assume_tac (loop2_modify_count_bcover_exit_upper |> ISPEC ``loop:'a -> num -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `exit`, `cover`, `modify`, `f`, `R`] strip_assume_tac) >>
  `loop2_count guard modify f x y = pop b y` by rw[pop_eq_loop2_count, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 1 < b /\ (!x1 x2 y1 y2. y1 <= y2 ==> body x1 y1 <= body x2 y2) /\
       (!x y. loop x y = if y = 0 then c else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
        !x y. loop x y <= c + body x y * pop b y *)
(* Proof: by loop2_div_count_cover_exit_upper, with cover = body. *)
val loop2_div_count_exit_upper = store_thm(
  "loop2_div_count_exit_upper",
  ``!loop f body exit b c. 1 < b /\
       (!x1 x2 y1 y2. y1 <= y2 ==> body x1 y1 <= body x2 y2) /\
       (!x y. loop x y = if y = 0 then c else body x y + if exit x y then 0 else loop (f x) (y DIV b)) ==>
        !x y. loop x y <= c + body x y * pop b y``,
  rpt strip_tac >>
  assume_tac loop2_div_count_cover_exit_upper >>
  last_x_assum (qspecl_then [`loop`, `f`, `body`, `body`, `exit`, `b`, `c`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x1 y1 <= cover x2 y2) /\
       (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y DIV b)) ==>
        !x y. loop x y <= c + cover x y * pop b y *)
(* Proof: by loop2_div_count_cover_exit_upper, with exit = F. *)
val loop2_div_count_cover_upper = store_thm(
  "loop2_div_count_cover_upper",
  ``!loop f body cover b c. 1 < b /\ (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x1 y1 <= cover x2 y2) /\
       (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y DIV b)) ==>
        !x y. loop x y <= c + cover x y * pop b y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:'a y:num. F` >>
  assume_tac loop2_div_count_cover_exit_upper >>
  last_x_assum (qspecl_then [`loop`, `f`, `body`, `cover`, `exit`, `b`, `c`] strip_assume_tac) >>
  metis_tac[]);

(* Theorem: 1 < b /\ (!x1 x2 y1 y2. y1 <= y2 ==> body x1 y1 <= body x2 y2) /\
    (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y DIV b)) ==>
     !x y. loop x y <= c + body x y * pop b y *)
(* Proof: loop2_div_count_cover_upper, with body = cover. *)
val loop2_div_count_upper = store_thm(
  "loop2_div_count_upper",
  ``!loop f body b c. 1 < b /\ (!x1 x2 y1 y2. y1 <= y2 ==> body x1 y1 <= body x2 y2) /\
    (!x y. loop x y = if y = 0 then c else body x y + loop (f x) (y DIV b)) ==>
     !x y. loop x y <= c + body x y * pop b y``,
  rpt strip_tac >>
  assume_tac loop2_div_count_cover_upper >>
  last_x_assum (qspecl_then [`loop`, `f`, `body`, `body`, `b`, `c`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
