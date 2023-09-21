(* ------------------------------------------------------------------------- *)
(* Loop Recurrence with Multiplying argument to a maximum                    *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "loopMultiply";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* Get dependent theories in lib *)
(* val _ = load "loopTheory"; *)
open loopTheory;

(* open dependent theories *)
open arithmeticTheory dividesTheory;
open helperNumTheory helperListTheory helperFunctionTheory; (* for DIV_EQUAL_0 *)
open listTheory rich_listTheory;
open listRangeTheory;

(* val _ = load "logPowerTheory"; *)
open logrootTheory logPowerTheory; (* for mop_eqn *)


(* ------------------------------------------------------------------------- *)
(* Loop Recurrence with Multiplying argument Documentation                   *)
(* ------------------------------------------------------------------------- *)
(* Type and Overload:
   doubling         = multiply_by 2
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Multiplying Count:
   mop_def             |- !x m b. mop b m x = if b <= 1 \/ x = 0 \/ m <= x then 0 else SUC (mop b m (b * x))
   mop_0               |- !b m x. b <= 1 \/ x = 0 \/ m <= x ==> mop b m x = 0
   mop_suc             |- !b m x. 1 < b /\ 0 < x /\ x < m ==> mop b m x = SUC (mop b m (b * x))
   mop_property        |- !b m x. 1 < b /\ 0 < x ==> !j. x * b ** j < m <=> j < mop b m x
   mop_exceeds         |- !b m x. 1 < b /\ 0 < x ==> m <= x * b ** mop b m x
   mop_eqn             |- !b m x. mop b m x =
                                  if b <= 1 \/ x = 0 \/ m <= x then 0
                                  else LOG b (m DIV x) +
                                       if m = x * b ** LOG b (m DIV x) then 0 else 1
   mop_LOG_DIV         |- !b m x. mop b m x <= 1 + LOG b (m DIV x)
   mop_b_m_1           |- !m b. 1 < b /\ 1 < m ==> mop b m 1 = LOG b m + if m = b ** LOG b m then 0 else 1
   mop_eq_loop_count   |- !b m x. 1 < b ==> mop b m x = loop_count (\x. x = 0 \/ m <= x) (\x. b * x) x
   mop_eq_loop2_count  |- !b f m x y. 1 < b ==>
                                      mop b m y = loop2_count (\x y. y = 0 \/ m <= y) (\y. b * y) f x y
   multiply_rising     |- !b. RISING (\x. b * x)
   iterating_mul_eqn   |- !b n x. FUNPOW (\x. b * x) n x = x * b ** n
   iterating_mul_mop   |- !b m x. 1 < b /\ 0 < x ==> m <= FUNPOW (\x. b * x) (mop b m x) x
   iterating_mul_mop_alt
                       |- !b m x. 1 < b /\ 0 < x ==> m <= x * b ** mop b m x

   Multiplying Loop:
   loop_mul_count_eqn  |- !loop body quit b m. 1 < b /\
                          (!x. loop x = if x = 0 \/ m <= x then quit x else body x + loop (b * x)) ==>
                           !x. loop x = quit (x * b ** mop b m x) +
                                        SUM (GENLIST (\j. body (x * b ** j)) (mop b m x))
   loop_mul_count_exit_sum_le
                       |- !loop body quit exit b m. 1 < b /\
                          (!x. loop x =
                               if x = 0 \/ m <= x then quit x
                               else body x + if exit x then 0 else loop (b * x)) ==>
                           !x. loop x <= quit (x * b ** mop b m x) +
                                         SUM (GENLIST (\j. body (x * b ** j)) (mop b m x))
   loop_mul_count_cover_exit_le
                       |- !loop body quit cover exit b m. 1 < b /\
                          (!x. body x <= cover x) /\ MONO cover /\
                          (!x. loop x =
                               if x = 0 \/ m <= x then quit x
                               else body x + if exit x then 0 else loop (b * x)) ==>
                           !x. loop x <= quit (x * b ** mop b m x) +
                                         mop b m x * cover (x * b ** mop b m x)
   loop_mul_count_cover_exit_le_alt
                       |- !loop body quit cover exit b m. 1 < b /\
                          (!x. body x <= cover x) /\ MONO cover /\
                          (!x. loop x =
                               if x = 0 \/ m <= x then quit x
                               else body x + if exit x then 0 else loop (b * x)) ==>
                           !x. (let n = mop b m x
                                 in loop x <= quit (x * b ** n) + n * cover (x * b ** n))
   loop_mul_count_exit_le
                       |- !loop body quit exit b m. 1 < b /\ MONO body /\
                          (!x. loop x =
                               if x = 0 \/ m <= x then quit x
                               else body x + if exit x then 0 else loop (b * x)) ==>
                           !x. loop x <= quit (x * b ** mop b m x) +
                                         mop b m x * body (x * b ** mop b m x)
   loop_mul_count_cover_le
                       |- !loop body quit cover b m. 1 < b /\
                          (!x. body x <= cover x) /\ MONO cover /\
                          (!x. loop x = if x = 0 \/ m <= x then quit x else body x + loop (b * x)) ==>
                           !x. loop x <= quit (x * b ** mop b m x) +
                                         mop b m x * cover (x * b ** mop b m x)
   loop_mul_count_le   |- !loop body quit b m. 1 < b /\ MONO body /\
                          (!x. loop x = if x = 0 \/ m <= x then quit x else body x + loop (b * x)) ==>
                           !x. loop x <= quit (x * b ** mop b m x) +
                                         mop b m x * body (x * b ** mop b m x)
   loop_mul_count_rcover_exit_le
                       |- !loop body quit cover exit b m. 1 < b /\
                          (!x. body x <= cover x) /\ RMONO cover /\
                          (!x. loop x =
                               if x = 0 \/ m <= x then quit x
                               else body x + if exit x then 0 else loop (b * x)) ==>
                           !x. loop x <= quit (x * b ** mop b m x) + mop b m x * cover x
   loop_mul_count_rbody_exit_le
                       |- !loop body quit exit b m. 1 < b /\ RMONO body /\
                          (!x. loop x =
                               if x = 0 \/ m <= x then quit x
                               else body x + if exit x then 0 else loop (b * x)) ==>
                           !x. loop x <= quit (x * b ** mop b m x) + mop b m x * body x
   loop_mul_count_rcover_le
                       |- !loop body quit cover b m. 1 < b /\
                          (!x. body x <= cover x) /\ RMONO cover /\
                          (!x. loop x = if x = 0 \/ m <= x then quit x else body x + loop (b * x)) ==>
                           !x. loop x <= quit (x * b ** mop b m x) + mop b m x * cover x
   loop_mul_count_rbody_le
                       |- !loop body quit b m. 1 < b /\ RMONO body /\
                          (!x. loop x = if x = 0 \/ m <= x then quit x else body x + loop (b * x)) ==>
                           !x. loop x <= quit (x * b ** mop b m x) + mop b m x * body x

   Multiplying Loop with Transform:
   loop2_mul_count_eqn |- !loop f body quit b m. 1 < b /\
                          (!x y. loop x y =
                                 if y = 0 \/ m <= y then quit x y
                                 else body x y + loop (f x) (b * y)) ==>
                           !x y. loop x y = quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                 SUM (GENLIST (\j. body (FUNPOW f j x) (y * b ** j)) (mop b m y))
   loop2_mul_count_sum_le
                       |- !loop f body quit exit b m. 1 < b /\
                          (!x y. loop x y =
                                 if y = 0 \/ m <= y then quit x y
                                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
                           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                 SUM (GENLIST (\j. body (FUNPOW f j x) (y * b ** j)) (mop b m y))

   Multiplying Loop with Transform-independent Body:
   loop2_mul_count_mono_cover_exit_le
                   |- !loop f body quit cover exit b m g. 1 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y =
                             if y = 0 \/ m <= y then quit x y
                             else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
                       !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                         mop b m y * g (y * b ** mop b m y)
   loop2_mul_count_mono_exit_le
                   |- !loop f body quit exit b m g. 1 < b /\ body = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y =
                             if y = 0 \/ m <= y then quit x y
                             else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
                       !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                         mop b m y * g (y * b ** mop b m y)
   loop2_mul_count_mono_cover_le
                   |- !loop f body quit cover b m g. 1 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y =
                             if y = 0 \/ m <= y then quit x y
                             else body x y + loop (f x) (b * y)) ==>
                       !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                         mop b m y * g (y * b ** mop b m y)
   loop2_mul_count_mono_le
                   |- !loop f body quit b m g. 1 < b /\ body = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y =
                             if y = 0 \/ m <= y then quit x y
                             else body x y + loop (f x) (b * y)) ==>
                       !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                         mop b m y * g (y * b ** mop b m y)
   loop2_mul_count_rmono_cover_exit_le
                   |- !loop f body quit cover exit b m g. 1 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y =
                             if y = 0 \/ m <= y then quit x y
                             else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
                       !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                         mop b m y * g y
   loop2_mul_count_rmono_exit_le
                   |- !loop f body quit exit b m g. 1 < b /\ body = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y =
                             if y = 0 \/ m <= y then quit x y
                             else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
                       !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                         mop b m y * g y
   loop2_mul_count_rmono_cover_le
                   |- !loop f body quit cover b m g. 1 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y =
                             if y = 0 \/ m <= y then quit x y
                             else body x y + loop (f x) (b * y)) ==>
                       !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                         mop b m y * g y
   loop2_mul_count_rmono_le
                   |- !loop f body quit b m g. 1 < b /\ body = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y =
                             if y = 0 \/ m <= y then quit x y
                             else body x y + loop (f x) (b * y)) ==>
                       !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                         mop b m y * g y

   Multiplying Loop with Numeric Transform:
   loop2_mul_rise_count_cover_exit_le
                       |- !loop f body quit cover exit b m. 1 < b /\
                          (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
                          (!x y. loop x y =
                                 if y = 0 \/ m <= y then quit x y
                                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
                           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                 mop b m y * cover (FUNPOW f (mop b m y) x) (y * b ** mop b m y)
   loop2_mul_rise_count_exit_le
                       |- !loop f body quit exit b m. 1 < b /\ MONO2 body /\ RISING f /\
                          (!x y. loop x y =
                                 if y = 0 \/ m <= y then quit x y
                                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
                           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                 mop b m y * body (FUNPOW f (mop b m y) x) (y * b ** mop b m y)
   loop2_mul_rise_count_cover_le
                       |- !loop f body quit cover b m. 1 < b /\
                          (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
                          (!x y. loop x y =
                                 if y = 0 \/ m <= y then quit x y
                                 else body x y + loop (f x) (b * y)) ==>
                           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                 mop b m y * cover (FUNPOW f (mop b m y) x) (y * b ** mop b m y)
   loop2_mul_rise_count_le
                       |- !loop f body quit b m. 1 < b /\ MONO2 body /\ RISING f /\
                          (!x y. loop x y =
                                 if y = 0 \/ m <= y then quit x y
                                 else body x y + loop (f x) (b * y)) ==>
                           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                 mop b m y * body (FUNPOW f (mop b m y) x) (y * b ** mop b m y)

   loop2_mul_fall_count_cover_exit_le
                       |- !loop f body quit cover exit b m. 1 < b /\
                          (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
                          (!x y. loop x y =
                                 if y = 0 \/ m <= y then quit x y
                                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
                           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                             mop b m y * cover x (y * b ** mop b m y)
   loop2_mul_fall_count_exit_le
                       |- !loop f body quit exit b m. 1 < b /\ MONO2 body /\ FALLING f /\
                          (!x y. loop x y =
                                 if y = 0 \/ m <= y then quit x y
                                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
                           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                             mop b m y * body x (y * b ** mop b m y)
   loop2_mul_fall_count_cover_le
                       |- !loop f body quit cover b m. 1 < b /\
                          (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
                          (!x y. loop x y =
                                 if y = 0 \/ m <= y then quit x y
                                 else body x y + loop (f x) (b * y)) ==>
                           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                             mop b m y * cover x (y * b ** mop b m y)
   loop2_mul_fall_count_le
                       |- !loop f body quit b m. 1 < b /\ MONO2 body /\ FALLING f /\
                          (!x y. loop x y =
                                 if y = 0 \/ m <= y then quit x y
                                 else body x y + loop (f x) (b * y)) ==>
                           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                             mop b m y * body x (y * b ** mop b m y)

   Multiplying Loop with Transform cover:
   loop2_mul_mono_count_cover_exit_le
                       |- !loop f g body quit cover exit b m. 1 < b /\
                          (!x y. body x y <= cover x y) /\
                          (!x y. RMONO (cover x) /\ MONO (combin$C cover y)) /\
                          (!x. f x <= g x) /\ MONO g /\ RISING g /\
                          (!x y. loop x y =
                                 if y = 0 \/ m <= y then quit x y
                                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
                           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                             mop b m y * cover (FUNPOW g (mop b m y) x) y
   loop2_mul_mono_count_exit_le
                       |- !loop f g body quit exit b m. 1 < b /\
                          (!x y. RMONO (body x) /\ MONO (combin$C body y)) /\
                          (!x. f x <= g x) /\ MONO g /\ RISING g /\
                          (!x y. loop x y =
                                 if y = 0 \/ m <= y then quit x y
                                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
                           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                             mop b m y * body (FUNPOW g (mop b m y) x) y
   loop2_mul_mono_count_cover_le
                       |- !loop f g body quit cover b m. 1 < b /\
                          (!x y. body x y <= cover x y) /\
                          (!x y. RMONO (cover x) /\ MONO (combin$C cover y)) /\
                          (!x. f x <= g x) /\ MONO g /\ RISING g /\
                          (!x y. loop x y =
                                 if y = 0 \/ m <= y then quit x y
                                 else body x y + loop (f x) (b * y)) ==>
                           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                             mop b m y * cover (FUNPOW g (mop b m y) x) y
   loop2_mul_mono_count_le
                       |- !loop f g body quit b m. 1 < b /\
                          (!x y. RMONO (body x) /\ MONO (combin$C body y)) /\
                          (!x. f x <= g x) /\ MONO g /\ RISING g /\
                          (!x y. loop x y =
                                 if y = 0 \/ m <= y then quit x y
                                 else body x y + loop (f x) (b * y)) ==>
                           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** mop b m y) +
                                             mop b m y * body (FUNPOW g (mop b m y) x) y

   Original:
   Multiplying List:
   multiply_by_def     |- !x m b. multiply_by b m x =
                                  if b <= 1 \/ x = 0 \/ m <= x then []
                                  else x::multiply_by b m (b * x)
   multiply_by_nil     |- !b m x. b <= 1 \/ x = 0 \/ m <= x ==> multiply_by b m x = []
   multiply_by_cons    |- !b m x. 1 < b /\ 0 < x /\ x < m ==> multiply_by b m x = x::multiply_by b m (b * x)
   multiply_by_eqn     |- !b m x. multiply_by b m x = GENLIST (\j. x * b ** j) (mop b m x)
   multiply_by_member  |- !b m x j. 1 < b /\ x * b ** j < m ==> MEM (x * b ** j) (multiply_by b m x)
   multiply_by_element |- !b m x j. j < mop b m x ==> EL j (multiply_by b m x) = x * b ** j
   multiply_by_length  |- !b m x. LENGTH (multiply_by b m x) = mop b m x
   doubling_length     |- !m. 1 < m ==> LENGTH (doubling m 1) = LOG2 m + if m = 2 ** LOG2 m then 0 else 1
   doubling_eqn        |- !m. 1 < m ==> doubling m 1 = GENLIST (\j. 2 ** j) (mop 2 m 1)
   multiply_by_eq_loop_arg
                       |- !b m x. 1 < b ==> multiply_by b m x = loop_arg (\x. x = 0 \/ m <= x) (\x. b * x) x
   iterating_multiply_eq_loop2_arg
                       |- !b m body f x y. 1 < b ==>
                               MAP2 body (iterating f x (mop b m y)) (multiply_by b m y) =
                               MAP (UNCURRY body) (loop2_arg (\x y. y = 0 \/ m <= y) (\y. b * y) f x y)

   loop_mul_count_by_sum
                       |- !loop body b c m. 1 < b /\
                          (!x. loop x = if x = 0 \/ m <= x then c else body x + loop (b * x)) ==>
                           !x. loop x = c + SUM (MAP body (multiply_by b m x))
   loop_mul_count_exit_by_sum
                       |- !loop body exit b c m. 1 < b /\
                          (!x. loop x =
                               if x = 0 \/ m <= x then c
                               else body x + if exit x then 0 else loop (b * x)) ==>
                           !x. loop x <= c + SUM (MAP body (multiply_by b m x))
   loop_mul_count_cover_exit_upper
                       |- !loop body cover exit b m c. 1 < b /\
                          (!x. body x <= cover x) /\ RMONO cover /\
                          (!x. loop x =
                               if x = 0 \/ m <= x then c
                               else body x + if exit x then 0 else loop (b * x)) ==>
                           !x. loop x <= c + cover x * mop b m x
   loop_mul_count_exit_upper
                       |- !loop body exit b m c. 1 < b /\ RMONO body /\
                          (!x. loop x =
                               if x = 0 \/ m <= x then c
                               else body x + if exit x then 0 else loop (b * x)) ==>
                           !x. loop x <= c + body x * mop b m x
   loop_mul_count_cover_upper
                       |- !loop body cover b m c. 1 < b /\
                          (!x. body x <= cover x) /\ RMONO cover /\
                          (!x. loop x = if x = 0 \/ m <= x then c else body x + loop (b * x)) ==>
                           !x. loop x <= c + cover x * mop b m x
   loop_mul_count_upper|- !loop body b m c. 1 < b /\ RMONO body /\
                          (!x. loop x = if x = 0 \/ m <= x then c else body x + loop (b * x)) ==>
                           !x. loop x <= c + body x * mop b m x

   loop2_mul_count_by_sum
                   |- !loop f body b m c. 1 < b /\
                      (!x y. loop x y = if y = 0 \/ m <= y then c else body x y + loop (f x) (b * y)) ==>
                       !x y. loop x y = c + SUM (MAP2 body (iterating f x (mop b m y)) (multiply_by b m y))
   loop2_mul_count_exit_by_sum
                   |- !loop f body b m c exit. 1 < b /\
                      (!x y. loop x y =
                             if y = 0 \/ m <= y then c
                             else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
                       !x y. loop x y <= c + SUM (MAP2 body (iterating f x (mop b m y)) (multiply_by b m y))
   loop2_mul_count_cover_exit_upper
                   |- !loop f body cover exit b m c. 1 < b /\
                      (!x y. body x y <= cover x y) /\
                      (!x1 x2 y1 y2. y1 <= y2 ==> cover x2 y2 <= cover x1 y1) /\
                      (!x y. loop x y =
                             if y = 0 \/ m <= y then c
                             else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
                       !x y. loop x y <= c + cover x y * mop b m y
   loop2_mul_count_exit_upper
                   |- !loop f body exit b m c. 1 < b /\
                      (!x1 x2 y1 y2. y1 <= y2 ==> body x2 y2 <= body x1 y1) /\
                      (!x y. loop x y =
                             if y = 0 \/ m <= y then c
                             else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
                       !x y. loop x y <= c + body x y * mop b m y
   loop2_mul_count_cover_upper
                   |- !loop f body cover b m c. 1 < b /\
                      (!x y. body x y <= cover x y) /\
                      (!x1 x2 y1 y2. y1 <= y2 ==> cover x2 y2 <= cover x1 y1) /\
                      (!x y. loop x y = if y = 0 \/ m <= y then c else body x y + loop (f x) (b * y)) ==>
                       !x y. loop x y <= c + cover x y * mop b m y
   loop2_mul_count_upper
                   |- !loop f body b m c. 1 < b /\
                      (!x1 x2 y1 y2. y1 <= y2 ==> body x2 y2 <= body x1 y1) /\
                      (!x y. loop x y = if y = 0 \/ m <= y then c else body x y + loop (f x) (b * y)) ==>
                       !x y. loop x y <= c + body x y * mop b m y
*)

(* ------------------------------------------------------------------------- *)
(* Helper                                                                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Loop Recurrence with Multiplying argument to a maximum                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Multiplying Count.                                                        *)
(* ------------------------------------------------------------------------- *)
(*
> loop_count_thm |> SPEC_ALL |> INST_TYPE [alpha |-> ``:num``] |> Q.INST [`modify` |-> `\x. b * x`, `guard` |-> `\x. x = 0 \/ m <= x`];
val it = |- WF R /\ (!x. ~(\x. x = 0 \/ m <= x) x ==> R ((\x. b * x) x) x) ==>
      !x. loop_count (\x. x = 0 \/ m <= x) (\x. b * x) x =
          if (\x. x = 0 \/ m <= x) x then 0
          else SUC (loop_count (\x. x = 0 \/ m <= x) (\x. b * x) ((\x. b * x) x)): thm
*)

(* Given a number x, count then number of b * x, up to some maximum m. *)
(* This definition is tied to loop_count, and not computationally effective.
val mop_def = Define`
    mop b m x = loop_count (\x. x = 0 \/ m <= x) (\x. b * x) x
`;
*)
Definition mop_def:
  mop b m x =
  if (b <= 1) \/ (x = 0) \/ (m <= x) then 0 else SUC (mop b m (b * x))
Termination
  WF_REL_TAC `measure (λ(b,m,x). m - x)` >>
  rw[] >> `x < b * x` by rw[] >> decide_tac
End

(* Theorem: b <= 1 \/ x = 0 \/ m <= x ==> (mop b m x = 0) *)
(* Proof: by mop_def *)
val mop_0 = store_thm(
  "mop_0",
  ``!b m x. b <= 1 \/ x = 0 \/ m <= x ==> (mop b m x = 0)``,
  rw[Once mop_def]);

(* Theorem: 1 < b /\ 0 < x /\ x < m ==> (mop b m x = SUC (mop b m (b * x))) *)
(* Proof: by mop_def *)
val mop_suc = store_thm(
  "mop_suc",
  ``!b m x. 1 < b /\ 0 < x /\ x < m ==> (mop b m x = SUC (mop b m (b * x)))``,
  rw[Once mop_def]);

(* Theorem: 1 < b /\ 0 < x ==> !j. x * b ** j < m <=> j < mop b m x *)
(* Proof:
   By induction from mop_def.
   If m <= x,
           mop b m x = 0             by mop_def
      Thus RHS = F.
      But m <= x /\ x <= x * b ** j  by EXP_POS
      ==> m <= x * b ** j,
        or LHS = F.
   Otherwise, ~(m <= x),
      If j = 0,
         LHS is x * 1 < m or x < m   by EXP_0
             which is T              by ~(m <= x)
         RHS is 0 < mop b m x
             which is T              by mop b m x = SUC (...)   by mop_suc
      If j <> 0,
         b * x * b ** (j - 1) < m <=> j - 1 < mop b m (b * x)
                                     by induction hypothesis
         LHS = x * b * b ** (j - 1)
             = x * b ** SUC (j - 1)  by EXP
             = x * b ** j            by SUC (j - 1) = j, j <> 0
         RHS <=> j < 1 + mop b m (b * x)    by j <> 0
              or j < mop b m x              by mop_suc
*)
val mop_property = store_thm(
  "mop_property",
  ``!b m x. 1 < b /\ 0 < x ==> !j. x * b ** j < m <=> j < mop b m x``,
  ho_match_mp_tac (theorem "mop_ind") >>
  rw[] >>
  Cases_on `m <= x` >| [
    (Cases_on `j = 0` >> simp[Once mop_def]) >>
    `b <= b * j` by rw[] >>
    spose_not_then strip_assume_tac >>
    `x <= x * b ** j` by rw[] >>
    decide_tac,
    `0 < b * x` by rw[MULT_POS] >>
    (Cases_on `j = 0` >> simp[mop_suc]) >>
    `b * x * b ** (j - 1) < m <=> j - 1 < mop b m (b * x)` by rw[] >>
    `b * x * b ** (j - 1) = x * (b * b ** (j - 1))` by decide_tac >>
    `_ = x * b ** SUC (j - 1)` by rw[EXP] >>
    `_ = x * b ** j` by rw[] >>
    `j - 1 < mop b m (b * x) <=> j < 1 + mop b m (b * x)` by decide_tac >>
    rw[ADD1]
  ]);

(* Theorem: 1 < b /\ 0 < x ==> m <= x * b ** mop b m x *)
(* Proof:
   Note     x * b ** (mop b m x) < m
        <=> mop b m x < mop b m x     by mop_property
        <=> F
   Thus m <= x * b ** hop b m x is true.
*)
val mop_exceeds = store_thm(
  "mop_exceeds",
  ``!b m x. 1 < b /\ 0 < x ==> m <= x * b ** mop b m x``,
  metis_tac[mop_property, LESS_EQ_REFL, NOT_LESS]);

(* Note:
   m <= x * b ** n ==> n = LOG b (m DIV x), need to figure out the extra 1.

As long as x * b ** n <> m, we need the extra 1.

Indeed,
      b ** LOG b (m DIV x) <= (m DIV x)             by LOG
  x * b ** LOG b (m DIV x) <= x * (m DIV x) <= m    by DIV_MULT_LESS_EQ
If x * (m DIV x) < m, we need the extra 1 to exit from the loop.
If x * (m DIV x) = m, the loop is exited already.

val foo_def = Define`
    foo b m x =
        if (b <= 1) \/ (x = 0) \/ (m <= x) then 0
        else LOG b (m DIV x) + if (m = x * b ** (LOG b (m DIV x))) then 0 else 1
`;

> EVAL ``MAP (mop 2 100) [1 .. 10]``; = [7; 6; 6; 5; 5; 5; 4; 4; 4; 4]: thm
> EVAL ``MAP (foo 2 100) [1 .. 10]``; = [7; 6; 6; 5; 5; 5; 4; 4; 4; 4]: thm

> EVAL ``MAP (mop 2 1024) [1 .. 10]``; = [10; 9; 9; 8; 8; 8; 8; 7; 7; 7]: thm
> EVAL ``MAP (foo 2 1024) [1 .. 10]``; = [10; 9; 9; 8; 8; 8; 8; 7; 7; 7]: thm
*)

(* Theorem: mop b m x =
            if (b <= 1) \/ (x = 0) \/ (m <= x) then 0
            else LOG b (m DIV x) + if (m = x * b ** (LOG b (m DIV x))) then 0 else 1 *)
(* Proof:
   By induction from mop_def.
   If b <= 1, or x = 0, or m <= x,
      Then mop b m x = 0              by mop_def
   Otherwise, 1 < b /\ 0 < x /\ x < m.
   If m <= b * x,
      LHS = mop b m
          = SUC (mop b m (b * x))     by mop_def
          = SUC 0                     by m <= b * x
          = 1                         by ONE
      Now m <= b * x means m = b * x or m < b * x.
      If m = b * x,
         Then b = m DIV x             by MULT_DIV
           so LOG b (m DIV x)
            = LOG b b = 1             by LOG_BASE
          and x * b ** (LOG b (m DIV x))
            = x * b ** 1 = x * b = m  by EXP_1
         Thus RHS = 1 + 0 = 1 = LHS.
      If m < b * x,
         Then m DIV x < b             by DIV_LT_X, m < b * x
          Now m DIV x <> 0            by DIV_EQUAL_0, 0 < x, x < m
          ==> LOG b (m DIV x) = 0     by LOG_RWT, 0 < m DIV x, m DIV x < b
          and x * b ** (LOG b (m DIV x))
            = x * b ** 0 = x <> m     by EXP_0, x < m
         Thus RHS = 0 + 1 = 1 = LHS.
    Otherwise, b * x < m.
       LHS = mop b m
           = SUC (mop b m (b * x))    by mop_def
           = SUC (LOG b (m DIV (b * x)) + if (m = (b * x) * b ** (LOG b (m DIV (b * x)))) then 0 else 1)
                                      by induction hypothesis
       Now b * x < m ==> b * x <= m,
        so b <= m DIV x               by X_LE_DIV, x * b <= m
       ==> LOG b (m DIV x)
         = 1 + LOG b (m DIV x DIV b)    by LOG_DIV, b <= m DIV x
         = 1 + LOG b (m DIV (x * b))    by DIV_DIV_DIV_MULT
         = SUC (LOG b (m DIV (x * b)))  by ADD1

       LHS = LOG b (m DIV x) + if (m = x * (b * b ** LOG b (m DIV (b * x))) then 0 else 1   by above
           = LOG b (m DIV x) + if (m = x * b ** SUC (LOG b (m DIV (b * x)))) then 0 else 1  by EXP
           = LOG b (m DIV x) + if (m = x * b ** (LOG b (m DIV x))) then 0 else 1            by above
           = RHS
*)
val mop_eqn = store_thm(
  "mop_eqn",
  ``!b m x. mop b m x =
            if (b <= 1) \/ (x = 0) \/ (m <= x) then 0
            else LOG b (m DIV x) + if (m = x * b ** (LOG b (m DIV x))) then 0 else 1``,
  ho_match_mp_tac (theorem "mop_ind") >>
  (rw[] >> simp[Once mop_def]) >| [
    `x * b ** LOG b (m DIV x) <= x * b ** 1` by metis_tac[EXP_1, MULT_COMM] >>
    `b ** LOG b (m DIV x) <= b ** 1` by metis_tac[LE_MULT_LCANCEL] >>
    `LOG b (m DIV x) <= 1` by metis_tac[EXP_BASE_LE_MONO, NOT_LESS] >>
    `m <> x` by decide_tac >>
    `LOG b (m DIV x) <> 0` by metis_tac[EXP_0, MULT_RIGHT_1] >>
    decide_tac,
    `(m = b * x) \/ (m < b * x)` by decide_tac >| [
      `m DIV x = b` by rw[MULT_DIV] >>
      `LOG b (m DIV x) = 1` by rw[LOG_BASE] >>
      fs[EXP_1],
      `m DIV x <> 0` by rw[DIV_EQUAL_0] >>
      `m DIV x < b` by rw[DIV_LT_X] >>
      `LOG b (m DIV x) = 0` by rw[LOG_RWT] >>
      rw[]
    ],
    `x * b ** LOG b (m DIV x) = x * (b * b ** LOG b (m DIV (b * x)))` by decide_tac >>
    `b ** LOG b (m DIV x) = b * b ** LOG b (m DIV (b * x))` by metis_tac[EQ_MULT_LCANCEL] >>
    metis_tac[EXP, EXP_BASE_INJECTIVE, NOT_LESS],
    simp[ADD1] >>
    `b <= m DIV x` by rw[X_LE_DIV] >>
    `LOG b (m DIV x) = 1 + LOG b (m DIV x DIV b)` by rw[LOG_DIV] >>
    `_ = SUC (LOG b (m DIV (x * b)))` by rw[DIV_DIV_DIV_MULT, ADD1] >>
    `m = x * (b * b ** LOG b (m DIV (b * x)))` by decide_tac >>
    fs[EXP],
    `b <= m DIV x` by rw[X_LE_DIV] >>
    `LOG b (m DIV x) = 1 + LOG b (m DIV x DIV b)` by rw[LOG_DIV] >>
    `_ = SUC (LOG b (m DIV (x * b)))` by rw[DIV_DIV_DIV_MULT, ADD1] >>
    `m <> x * (b * b ** LOG b (m DIV (b * x)))` by decide_tac >>
    fs[EXP],
    simp[GSYM ADD1] >>
    `b <= m DIV x` by rw[X_LE_DIV] >>
    `LOG b (m DIV x) = 1 + LOG b (m DIV x DIV b)` by rw[LOG_DIV] >>
    `_ = SUC (LOG b (m DIV (x * b)))` by rw[DIV_DIV_DIV_MULT, ADD1] >>
    decide_tac
  ]);

(* Theorem: mop b m x <= 1 + LOG b (m DIV x) *)
(* Proof: by mop_eqn *)
val mop_LOG_DIV = store_thm(
  "mop_LOG_DIV",
  ``!b m x. mop b m x <= 1 + LOG b (m DIV x)``,
  rw[mop_eqn]);

(* Theorem: 1 < b /\ 1 < m ==> (mop b m 1 = LOG b m + if m = b ** LOG b m then 0 else 1) *)
(* Proof:
     mop b m 1
   = LOG b (m DIV 1) + if m = 1 * b ** LOG b (m DIV 1) then 0 else 1   by mop_eqn
   = LOG b m + if m = b ** LOG b m then 0 else 1                       by DIV_1
*)
val mop_b_m_1 = store_thm(
  "mop_b_m_1",
  ``!m b. 1 < b /\ 1 < m ==> (mop b m 1 = LOG b m + if m = b ** LOG b m then 0 else 1)``,
  rw[mop_eqn]);

(* Theorem: 1 < b ==> (mop b m x = loop_count (\x. x = 0 \/ m <= x) (\x. b * x) x) *)
(* Proof:
   By induction from mop_def.
   Let guard = (\x. x = 0 \/ m <= x),
       modify = (\x. b * x),
       R = measure (\x. m - x).
   The goal is: mop b m x = loop_count guard modify x

   Note WF R                               by WF_measure
    and !x. ~guard x ==> R (modify x) x    by m - (b * x) < m - x, 1 < b, x <> 0
   If guard x,
      Then m <= x                          by guard x
           mop b m 0
         = 0                               by mop_0
         = loop_count guard modify 0       by loop_count_0, guard x
   If ~guard x,
      Then ~(m <= x), or x < m             by ~guard x
           hop b m x
         = SUC (hop b m (b * x))           by hop_suc
         = SUC (loop_count guard modify (b * x))
                                           by induction hypothesis
         = loop_count guard modify x       by loop_count_suc
*)
val mop_eq_loop_count = store_thm(
  "mop_eq_loop_count",
  ``!b m x. 1 < b ==> (mop b m x = loop_count (\x. x = 0 \/ m <= x) (\x. b * x) x)``,
  ho_match_mp_tac (theorem "mop_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x. x = 0 \/ m <= x` >>
  qabbrev_tac `modify = \x. b * x` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by
  (rw[Abbr`guard`, Abbr`modify`, Abbr`R`] >>
  `x' < b * x'` by rw[] >>
  decide_tac) >>
  Cases_on `guard x` >-
  metis_tac[mop_0, loop_count_0] >>
  `~(m <= x)` by metis_tac[] >>
  `x < m` by decide_tac >>
  `mop b m x = SUC (mop b m (b * x))` by metis_tac[mop_suc, NOT_LESS, NOT_ZERO] >>
  `_ = SUC (loop_count guard modify (b * x))` by metis_tac[NOT_LESS, NOT_ZERO] >>
  `_ = loop_count guard modify x` by metis_tac[loop_count_suc] >>
  decide_tac);

(* Theorem: 1 < b ==> (mop b m y = loop2_count (\x y. y = 0 \/ m <= y) (\y. b * y) f x y) *)
(* Proof:
   By induction from mop_def.
   Let guard = (\x y. y = 0 \/ m <= y),
       modify = (\y. b * y),
       R = measure (\(x, y). m - y).
   Then WF R                               by WF_measure
    and !x. ~guard x y ==> R (modify x) x  by m - (b * x) < m - x, 1 < b, x <> 0
   If guard x y,
      Then mop b m y
         = 0                               by mop_0, guard x y
         = loop2_count guard modify f x y  by loop2_count_0, guard x y
   If ~guard x y,
      Then mop b m y
         = SUC (mop b m (b * y))                     by mop_suc, ~guard x y
         = SUC (mop b m (modify x))                  by notation
         = SUC (loop2_count guard modify f (f x) (modify y))
                                                     by induction hypothesis, 1 < b
         = loop2_count guard modify f x y            by loop_count_suc, ~guard x y
*)
val mop_eq_loop2_count = store_thm(
  "mop_eq_loop2_count",
  ``!b f m x y. 1 < b ==> (mop b m y = loop2_count (\x y. y = 0 \/ m <= y) (\y. b * y) f x y)``,
  ntac 5 strip_tac >>
  qid_spec_tac `x` >>
  qid_spec_tac `y` >>
  qid_spec_tac `m` >>
  qid_spec_tac `b` >>
  ho_match_mp_tac (theorem "mop_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x y. y = 0 \/ m <= y` >>
  qabbrev_tac `modify = \y. b * y` >>
  qabbrev_tac `R = measure (\(x,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by
  (rw[Abbr`guard`, Abbr`modify`, Abbr`R`] >>
  `y' < b * y'` by rw[] >>
  decide_tac) >>
  Cases_on `guard x y` >-
  metis_tac[mop_0, loop2_count_0] >>
  `mop b m y = SUC (mop b m (b * y))` by metis_tac[mop_suc, NOT_LESS, NOT_ZERO] >>
  `_ = SUC (loop2_count guard modify f (f x) (b * y))` by metis_tac[NOT_LESS] >>
  `_ = loop2_count guard modify f x y` by metis_tac[loop2_count_suc] >>
  decide_tac);

(* Theorem: 0 < b ==> RISING (\x. b * x) *)
(* Proof:
   By RISING, this is to show: !x. x <= b * x, which is true.
*)
val multiply_rising = store_thm(
  "multiply_rising",
  ``!b. 0 < b ==> RISING (\x. b * x)``,
  simp[]);

(* Theorem: FUNPOW (\x. b * x) n x = x * b ** n *)
(* Proof:
   Let f = (\x. b * x).
   By induction on n.
   Base: !x. FUNPOW (\x. b * x) 0 x = x * b ** 0
         FUNPOW f 0 x
       = x                  by FUNPOW_0
       = x * b ** 0         by arithmetic
   Step: !x. FUNPOW (\x. b * x) n x = x * b ** n ==>
         !x. FUNPOW (\x. b * x) (SUC n) x = x * b ** SUC n
         FUNPOW f (SUC n) x
       = f (FUNPOW f n x)   by FUNPOW_SUC
       = f (x * b ** n)     by induction hypothesis
       = b * (x * b ** n)   by function application
       = x * b ** (SUC n)   by EXP
*)
val iterating_mul_eqn = store_thm(
  "iterating_mul_eqn",
  ``!b n x. FUNPOW (\x. b * x) n x = x * b ** n``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[FUNPOW_SUC, EXP]);

(* Theorem: 1 < b /\ 0 < x ==> m <= FUNPOW (\x. b * x) (mop b m x) x *)
(* Proof:
   Let guard = (\x. x = 0 |/ m <= x),
       modify = (\x. b * x),
       R = measure (\x. m - x).
   Then WF R                                   by WF_measure
    and !x. ~guard x ==> R (modify x) x        by m - x * b < m - x, 1 < b
   Let n = loop_count guard modify x.
   Note n = mop b m x                          by mop_eq_loop_count
    and FUNPOW modify n x = x * b ** n         by iterating_mul_eqn
    and guard (FUNPOW modify (loop_count guard modify x) x)   by loop_count_iterating
    Now 0 < x ==> x * b ** n <> 0              by EXP_POS, 1 < b
   Thus m <= FUNPOW modify (loop_count guard modify x) x      by guard
*)
val iterating_mul_mop = store_thm(
  "iterating_mul_mop",
  ``!b m x. 1 < b /\ 0 < x ==> m <= FUNPOW (\x. b * x) (mop b m x) x``,
  rw[mop_eq_loop_count] >>
  qabbrev_tac `guard = \x. x = 0 \/ m <= x` >>
  qabbrev_tac `modify = \x. b * x` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by
  (rw[Abbr`guard`, Abbr`modify`, Abbr`R`] >>
  `x' < b * x'` by rw[] >>
  decide_tac) >>
  qabbrev_tac `n = loop_count guard modify x` >>
  `FUNPOW modify n x = x * b ** n` by rw[iterating_mul_eqn, Abbr`modify`] >>
  `x * b ** n <> 0` by rw[] >>
  metis_tac[loop_count_iterating]);

(* Theorem: 1 < b /\ 0 < x ==> m <= x * b ** (mop b m x) *)
(* Proof:
   Note m <= FUNPOW (\x. b * x) (mop b m x) x    by iterating_mul_mop
     or m <= x * b ** (mop b m x)                by iterating_mul_eqn
*)
val iterating_mul_mop_alt = store_thm(
  "iterating_mul_mop_alt",
  ``!b m x. 1 < b /\ 0 < x ==> m <= x * b ** (mop b m x)``,
  metis_tac[iterating_mul_mop, iterating_mul_eqn]);

(* This is the same as mop_exceeds: |- !b m x. 1 < b /\ 0 < x ==> m <= x * b ** mop b m x *)

(* ------------------------------------------------------------------------- *)
(* Multiplying Loop                                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + loop (b * x)) ==>
        !x. loop x = quit (x * b ** (mop b m x)) +
                     SUM (GENLIST (\j. body (x * b ** j)) (mop b m x)) *)
(* Proof:
   Let guard = (\x. x = 0 \/ m <= x),
       modify = (\x. b * x),
       R = measure (\x. m - x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by m - (b * x) < m - x, 1 < b, x <> 0
   Also !x. loop x = if guard x then quit x else body x + loop (modify x)
                                          by given
   Let f = (\j. body (FUNPOW modify j x)),
       n = loop_count guard modify x,
       z = FUNPOW modify n x.
   Note n = mop b m x                     by mop_eq_loop_count
    and f = (\j. body (x * b ** j))       by iterating_mul_eqn, FUN_EQ_THM
    and z = x * b ** n                    by iterating_mul_eqn
   Thus loop x
      = quit z + SUM (GENLIST f n)  by loop_modify_count_eqn
      = quit (x * b ** (mop b m x)) + SUM (GENLIST (\j. body (x * b ** j)) (mop b m x))
*)
val loop_mul_count_eqn = store_thm(
  "loop_mul_count_eqn",
  ``!loop body quit b m. 1 < b /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + loop (b * x)) ==>
        !x. loop x = quit (x * b ** (mop b m x)) +
                     SUM (GENLIST (\j. body (x * b ** j)) (mop b m x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0 \/ m <= x` >>
  qabbrev_tac `modify = \x. b * x` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `x < x * b` by rw[] >>
  decide_tac) >>
  `!x. loop x = if guard x then quit x else body x + loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_eqn >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `n = loop_count guard modify x` >>
  `n = mop b m x` by rw[mop_eq_loop_count, Abbr`guard`, Abbr`modify`, Abbr`n`] >>
  `FUNPOW modify n x = x * b ** n` by rw[iterating_mul_eqn, Abbr`modify`] >>
  qabbrev_tac `u = \j. body (FUNPOW modify j x)` >>
  qabbrev_tac `v = \j. body (x * b ** j)` >>
  `u = v` by rw[FUN_EQ_THM, iterating_mul_eqn, Abbr`u`, Abbr`v`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 1 < b /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) +
                      SUM (GENLIST (\j. body (x * b ** j)) (mop b m x)) *)
(* Proof:
   Let guard = (\x. x = 0 \/ m <= x),
       modify = (\x. b * x),
       R = measure (\x. m - x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by m - (b * x) < m - x, 1 < b, x <> 0
   Also !x. loop x = if guard x then quit x else body x + loop (modify x)
                                          by given
   Let f = (\j. body (FUNPOW modify j x)),
       n = loop_count guard modify x,
       z = FUNPOW modify n x.
   Note n = mop b m x                     by mop_eq_loop_count
    and f = (\j. body (x * b ** j))       by iterating_mul_eqn, FUN_EQ_THM
    and z = x * b ** n                    by iterating_mul_eqn
   Thus  loop x
      <= quit z + SUM (GENLIST f n)       by loop_modify_count_exit_le
       = quit (x * b ** (mop b m x)) + SUM (GENLIST (\j. body (x * b ** j)) (mop b m x))
*)
val loop_mul_count_exit_sum_le = store_thm(
  "loop_mul_count_exit_sum_le",
  ``!loop body quit exit b m. 1 < b /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) +
                      SUM (GENLIST (\j. body (x * b ** j)) (mop b m x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0 \/ m <= x` >>
  qabbrev_tac `modify = \x. b * x` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `x < x * b` by rw[] >>
  decide_tac) >>
  `!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `n = loop_count guard modify x` >>
  `n = mop b m x` by rw[mop_eq_loop_count, Abbr`guard`, Abbr`modify`, Abbr`n`] >>
  `FUNPOW modify n x = x * b ** n` by rw[iterating_mul_eqn, Abbr`modify`] >>
  qabbrev_tac `u = \j. body (FUNPOW modify j x)` >>
  qabbrev_tac `v = \j. body (x * b ** j)` >>
  `u = v` by rw[FUN_EQ_THM, iterating_mul_eqn, Abbr`u`, Abbr`v`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 1 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * cover (x * b ** (mop b m x)) *)
(* Proof:
   Let guard = (\x. x = 0 \/ m <= x),
       modify = (\x. b * x),
       R = measure (\x. m - x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by m - (b * x) < m - x, 1 < b, x <> 0
    and RISING modify                     by multiply_rising
   Also !x. loop x = if guard x then quit x else body x + loop (modify x)
                                          by given
   Let n = loop_count guard modify x,
       z = FUNPOW modify n x.
   Note n = mop b m x                     by mop_eq_loop_count
    and z = x * b ** n                    by iterating_mul_eqn
       loop x
    <= quit z + n * cover (FUNPOW modify n x))  by loop_rise_count_cover_exit_le, MONO cover
     = quit (x * b ** (mop b m x)) + mop b m x * cover (x * b ** (mop b m x))
*)
val loop_mul_count_cover_exit_le = store_thm(
  "loop_mul_count_cover_exit_le",
  ``!loop body quit cover exit b m.
       1 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * cover (x * b ** (mop b m x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0 \/ m <= x` >>
  qabbrev_tac `modify = \x. b * x` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `x < b * x` by rw[] >>
  decide_tac) >>
  `RISING modify` by rw[multiply_rising, Abbr`modify`] >>
  `!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_rise_count_cover_exit_le >>
  first_x_assum (qspecl_then [`x`, `cover`] strip_assume_tac) >>
  qabbrev_tac `n = loop_count guard modify x` >>
  `n = mop b m x` by rw[mop_eq_loop_count, Abbr`guard`, Abbr`modify`, Abbr`n`] >>
  `FUNPOW modify n x = x * b ** n` by rw[iterating_mul_eqn, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: Equivalent form of loop_mul_count_cover_exit_le *)
(* Proof: by loop_mul_count_cover_exit_le *)
val loop_mul_count_cover_exit_le_alt = store_thm(
  "loop_mul_count_cover_exit_le_alt",
  ``!loop body quit cover exit b m.
       1 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + if exit x then 0 else loop (b * x)) ==>
        !x. let n = mop b m x in
             loop x <= quit (x * b ** n) + n * cover (x * b ** n)``,
  metis_tac[loop_mul_count_cover_exit_le]);

(* Other similar theorems -- directly *)

(* Theorem: 1 < b /\ MONO body /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * body (x * b ** (mop b m x)) *)
(* Proof: by loop_mul_count_cover_exit_le with cover = body. *)
val loop_mul_count_exit_le = store_thm(
  "loop_mul_count_exit_le",
  ``!loop body quit exit b m. 1 < b /\ MONO body /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * body (x * b ** (mop b m x))``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_mul_count_cover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem: 1 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * cover (x * b ** (mop b m x)) *)
(* Proof: by loop_mul_count_cover_exit_le with exit = F. *)
val loop_mul_count_cover_le = store_thm(
  "loop_mul_count_cover_le",
  ``!loop body quit cover b m.
       1 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * cover (x * b ** (mop b m x))``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num. F` >>
  `!x. loop x = if x = 0 \/ m <= x then quit x else body x + if exit x then 0 else loop (b * x)` by metis_tac[] >>
  imp_res_tac loop_mul_count_cover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem: 1 < b /\ MONO body /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * body (x * b ** (mop b m x)) *)
(* Proof: by loop_mul_count_cover_le with cover = body. *)
val loop_mul_count_le = store_thm(
  "loop_mul_count_le",
  ``!loop body quit b m. 1 < b /\ MONO body /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * body (x * b ** (mop b m x))``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_mul_count_cover_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * cover x *)
(* Proof:
   Let guard = (\x. x = 0 \/ m <= x),
       modify = (\x. b * x),
       R = measure (\x. m - x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by m - (b * x) < m - x, 1 < b, x <> 0
    and RISING modify                     by multiply_rising
   Also !x. loop x = if guard x then quit x else body x + loop (modify x)
                                          by given
   Let n = loop_count guard modify x,
       z = FUNPOW modify n x.
   Note n = mop b m x                     by mop_eq_loop_count
    and z = x * b ** n                    by iterating_mul_eqn
       loop x
    <= quit z + n * cover x               by loop_rise_count_rcover_exit_le, RMONO cover
     = quit (x * b ** (mop b m x)) + mop b m x * cover x
*)
val loop_mul_count_rcover_exit_le = store_thm(
  "loop_mul_count_rcover_exit_le",
  ``!loop body quit cover exit b m.
       1 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * cover x``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0 \/ m <= x` >>
  qabbrev_tac `modify = \x. b * x` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `x < b * x` by rw[] >>
  decide_tac) >>
  `RISING modify` by rw[multiply_rising, Abbr`modify`] >>
  `!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_rise_count_rcover_exit_le >>
  first_x_assum (qspecl_then [`x`, `cover`] strip_assume_tac) >>
  qabbrev_tac `n = loop_count guard modify x` >>
  `n = mop b m x` by rw[mop_eq_loop_count, Abbr`guard`, Abbr`modify`, Abbr`n`] >>
  `FUNPOW modify n x = x * b ** n` by rw[iterating_mul_eqn, Abbr`modify`] >>
  metis_tac[]);

(* Other similar theorems -- directly *)

(* Theorem: 1 < b /\ RMONO body /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * body x *)
(* Proof: by loop_mul_count_rcover_exit_le with cover = body. *)
val loop_mul_count_rbody_exit_le = store_thm(
  "loop_mul_count_rbody_exit_le",
  ``!loop body quit exit b m. 1 < b /\ RMONO body /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * body x``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_mul_count_rcover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem: 1 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * cover x *)
(* Proof: by loop_mul_count_rcover_exit_le with exit = F. *)
val loop_mul_count_rcover_le = store_thm(
  "loop_mul_count_rcover_le",
  ``!loop body quit cover b m.
       1 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * cover x``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num. F` >>
  `!x. loop x = if x = 0 \/ m <= x then quit x else body x + if exit x then 0 else loop (b * x)` by metis_tac[] >>
  imp_res_tac loop_mul_count_rcover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem: 1 < b /\ RMONO body /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * body x *)
(* Proof: by loop_mul_count_rcover_le with cover = body. *)
val loop_mul_count_rbody_le = store_thm(
  "loop_mul_count_rbody_le",
  ``!loop body quit b m. 1 < b /\ RMONO body /\
       (!x. loop x = if x = 0 \/ m <= x then quit x else body x + loop (b * x)) ==>
        !x. loop x <= quit (x * b ** (mop b m x)) + mop b m x * body x``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_mul_count_rcover_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Multiplying Loop with Transform                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
     !x y. loop x y = quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                      SUM (GENLIST (\j. body (FUNPOW f j x) (y * b ** j)) (mop b m y)) *)
(* Proof:
   Let guard = (\x y. y = 0 \/ m <= y),
       modify = (\y. b * y),
       R = measure (\(x,y). m - y).
   Then WF R                                         by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)  by m - (b * x) < m - x, 1 < b, x <> 0
    and !x y. loop x y = if guard x y then quit x y else body x y + loop (f x) (modify y)   by given
   Let g = \j. body (FUNPOW f j x) (FUNPOW modify j y),
       n = loop2_count guard modify f x y,
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = mop b m y                                by mop_eq_loop2_count
    and g = (\j. body (FUNPOW f j x) (y * b ** j))   by iterating_mul_eqn, FUN_EQ_THM
    and q = y * b ** n                               by iterating_mul_eqn
        loop x y
      = quit p q + SUM (GENLIST g n)               by loop2_modify_count_eqn
      = quit p q + SUM (GENLIST g (mop b m y))     by n = mop b m y
      = quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
        SUM (GENLIST (\j. body (FUNPOW f j x) (y * b ** j)) (mop b m y))
*)
val loop2_mul_count_eqn = store_thm(
  "loop2_mul_count_eqn",
  ``!loop f body quit b m. 1 < b /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
     !x y. loop x y = quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                      SUM (GENLIST (\j. body (FUNPOW f j x) (y * b ** j)) (mop b m y))``,
  rpt strip_tac >>
  imp_res_tac mop_eq_loop2_count >>
  first_x_assum (qspecl_then [`y`, `x`, `m`, `f`] strip_assume_tac) >>
  qabbrev_tac `guard = \x y. y = 0 \/ m <= y` >>
  qabbrev_tac `modify = \y. b * y` >>
  qabbrev_tac `R = measure (\(x,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `y' < b * y'` by rw[] >>
  decide_tac) >>
  `!x y. loop x y = if guard x y then quit x y else body x y + loop (f x) (modify y)` by metis_tac[] >>
  imp_res_tac loop2_modify_count_eqn >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = loop2_count guard modify f x y` >>
  `FUNPOW modify n y = y * b ** n` by rw[iterating_mul_eqn, Abbr`modify`] >>
  qabbrev_tac `u = \j. body (FUNPOW f j x) (FUNPOW modify j y)` >>
  qabbrev_tac `v = \j. body (FUNPOW f j x) (y * b ** j)` >>
  `u = v` by rw[FUN_EQ_THM, iterating_mul_eqn, Abbr`modify`, Abbr`u`, Abbr`v`] >>
  metis_tac[]);

(* Theorem: 1 < b /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                       SUM (GENLIST (\j. body (FUNPOW f j x) (y * b ** j)) (mop b m y)) *)
(* Proof:
   Let guard = (\x y. y = 0 \/ m <= y),
       modify = (\y. b * y),
       R = measure (\(x,y). m - y).
   Then WF R                                            by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by m - (b * x) < m - x, 1 < b, x <> 0
    and !x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                        by given
   Let g = \j. body (FUNPOW f j x) (FUNPOW modify j y),
       n = loop2_count guard modify f x y,
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = mop b m y                                by mop_eq_loop2_count
    and g = (\j. body (FUNPOW f j x) (y * b ** j))   by iterating_mul_eqn, FUN_EQ_THM
    and q = y * b ** n                               by iterating_mul_eqn
        loop x y
     <= quit p q + SUM (GENLIST g n)               by loop2_modify_count_exit_le
      = quit p q + SUM (GENLIST g (mop b m y))     by n = mop b m y
      = quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
        SUM (GENLIST (\j. body (FUNPOW f j x) (y * b ** j)) (mop b m y))
*)
val loop2_mul_count_sum_le = store_thm(
  "loop2_mul_count_sum_le",
  ``!loop f body quit exit b m. 1 < b /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                       SUM (GENLIST (\j. body (FUNPOW f j x) (y * b ** j)) (mop b m y))``,
  rpt strip_tac >>
  imp_res_tac mop_eq_loop2_count >>
  first_x_assum (qspecl_then [`y`, `x`, `m`, `f`] strip_assume_tac) >>
  qabbrev_tac `guard = \x y. y = 0 \/ m <= y` >>
  qabbrev_tac `modify = \y. b * y` >>
  qabbrev_tac `R = measure (\(x,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `y' < b * y'` by rw[] >>
  decide_tac) >>
  `!x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  imp_res_tac loop2_modify_count_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = loop2_count guard modify f x y` >>
  `FUNPOW modify n y = y * b ** n` by rw[iterating_mul_eqn, Abbr`modify`] >>
  qabbrev_tac `u = \j. body (FUNPOW f j x) (FUNPOW modify j y)` >>
  qabbrev_tac `v = \j. body (FUNPOW f j x) (y * b ** j)` >>
  `u = v` by rw[FUN_EQ_THM, iterating_mul_eqn, Abbr`modify`, Abbr`u`, Abbr`v`] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Multiplying Loop with Transform-independent Body                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                       (mop b m y) * g (y * b ** (mop b m y)) *)
(* Proof:
   Let n = mop b m y, z = FUNPOW f n x.
      loop x y
   <= quit z (y * b ** n) +
      SUM (GENLIST (\j. body (FUNPOW f j x) (y * b ** j)) n)      by loop2_mul_count_sum_le
   <= quit z (y * b ** n) +
      SUM (GENLIST (\j. cover (FUNPOW f j x) (y * b ** j)) n)     by SUM_LE, body cover
    = quit z (y * b ** n) + SUM (GENLIST (\j. g (y * b ** j)) n)  by expanding cover
   <= quit z (y * b ** n) + SUM (GENLIST (K (g (y * b ** n))) n)  by SUM_LE, MONO g
    = quit z (y * b ** n) + g (y * b ** n) * n                    by SUM_GENLIST_K
    = quit z (y * b ** n) + n * g (y * b ** n)                    by MULT_COMM
*)
val loop2_mul_count_mono_cover_exit_le = store_thm(
  "loop2_mul_count_mono_cover_exit_le",
  ``!loop f body quit cover exit b m g. 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                       (mop b m y) * g (y * b ** (mop b m y))``,
  rpt strip_tac >>
  imp_res_tac loop2_mul_count_sum_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = mop b m y` >>
  `SUM (GENLIST (\j. body (FUNPOW f j x) (y * b ** j)) n) <=
    SUM (GENLIST (\j. cover (FUNPOW f j x) (y * b ** j)) n)` by fs[SUM_LE] >>
  `SUM (GENLIST (\j. cover (FUNPOW f j x) (y * b ** j)) n) <= SUM (GENLIST (K (g (y * b ** n))) n)` by rw[SUM_LE] >>
  `SUM (GENLIST (K (g (y * b ** n))) n) = g (y * b ** n) * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Other similar theorems -- directly *)

(* Theorem: 1 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                       (mop b m y) * g (y * b ** (mop b m y)) *)
(* Proof: by loop2_mul_count_mono_cover_exit_le with cover = body. *)
val loop2_mul_count_mono_exit_le = store_thm(
  "loop2_mul_count_mono_exit_le",
  ``!loop f body quit exit b m g. 1 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                       (mop b m y) * g (y * b ** (mop b m y))``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_mul_count_mono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                       (mop b m y) * g (y * b ** (mop b m y)) *)
(* Proof: by loop2_mul_count_mono_cover_exit_le with exit = F. *)
val loop2_mul_count_mono_cover_le = store_thm(
  "loop2_mul_count_mono_cover_le",
  ``!loop f body quit cover b m g. 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                       (mop b m y) * g (y * b ** (mop b m y))``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:'a y:num. F` >>
  `!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (b * y)` by metis_tac[] >>
  imp_res_tac loop2_mul_count_mono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                       (mop b m y) * g (y * b ** (mop b m y)) *)
(* Proof: by loop2_mul_count_mono_cover_le with cover = body. *)
val loop2_mul_count_mono_le = store_thm(
  "loop2_mul_count_mono_le",
  ``!loop f body quit b m g. 1 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                       (mop b m y) * g (y * b ** (mop b m y))``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_mul_count_mono_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) + (mop b m y) * g y *)
(* Proof:
   Let n = mop b m y, z = FUNPOW f n x.
      loop x y
   <= quit z (y * b ** n) +
      SUM (GENLIST (\j. body (FUNPOW f j x) (y * b ** j)) n)      by loop2_mul_count_sum_le
   <= quit z (y * b ** n) +
      SUM (GENLIST (\j. cover (FUNPOW f j x) (y * b ** j)) n)     by SUM_LE, body cover
    = quit z (y * b ** n) + SUM (GENLIST (\j. g (y * b ** j)) n)  by expanding cover
   <= quit z (y * b ** n) + SUM (GENLIST (K (g y)) n)  by SUM_LE, RMONO g
    = quit z (y * b ** n) + g y * n                    by SUM_GENLIST_K
    = quit z (y * b ** n) + n * g y                    by MULT_COMM
*)
val loop2_mul_count_rmono_cover_exit_le = store_thm(
  "loop2_mul_count_rmono_cover_exit_le",
  ``!loop f body quit cover exit b m g. 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) + (mop b m y) * g y``,
  rpt strip_tac >>
  imp_res_tac loop2_mul_count_sum_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = mop b m y` >>
  `SUM (GENLIST (\j. body (FUNPOW f j x) (y * b ** j)) n) <=
    SUM (GENLIST (\j. cover (FUNPOW f j x) (y * b ** j)) n)` by fs[SUM_LE] >>
  `SUM (GENLIST (\j. cover (FUNPOW f j x) (y * b ** j)) n) <= SUM (GENLIST (K (g y)) n)` by rw[SUM_LE] >>
  `SUM (GENLIST (K (g y)) n) = g y * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Other similar theorems -- directly *)

(* Theorem: 1 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) + (mop b m y) * g y *)
(* Proof: by loop2_mul_count_rmono_cover_exit_le with cover = body. *)
val loop2_mul_count_rmono_exit_le = store_thm(
  "loop2_mul_count_rmono_exit_le",
  ``!loop f body quit exit b m g. 1 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) + (mop b m y) * g y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_mul_count_rmono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) + (mop b m y) * g y *)
(* Proof: by loop2_mul_count_rmono_cover_exit_le with exit = F. *)
val loop2_mul_count_rmono_cover_le = store_thm(
  "loop2_mul_count_rmono_cover_le",
  ``!loop f body quit cover b m g. 1 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) + (mop b m y) * g y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:'a y:num. F` >>
  `!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (b * y)` by metis_tac[] >>
  imp_res_tac loop2_mul_count_rmono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) + (mop b m y) * g y *)
(* Proof: by loop2_mul_count_rmono_cover_le with cover = body. *)
val loop2_mul_count_rmono_le = store_thm(
  "loop2_mul_count_rmono_le",
  ``!loop f body quit b m g. 1 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
     !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) + (mop b m y) * g y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_mul_count_rmono_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Multiplying Loop with Numeric Transform                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y =
                 if y = 0 \/ m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * cover (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) *)
(* Proof:
   Let guard = (\x y. y = 0 \/ m <= y),
       modify = (\y. b * y),
       R = measure (\(x,y). m - y).
   Then WF R                                            by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by m - (b * x) < m - x, 1 < b, x <> 0
    and !x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                        by given
    and RISING modify                                   by multiply_rising
   Let g = \j. body (FUNPOW f j x) (FUNPOW modify j y),
       n = loop2_count guard modify f x y,
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = mop b m y                                by mop_eq_loop2_count
    and g = (\j. body (FUNPOW f j x) (y * b ** j))   by iterating_mul_eqn, FUN_EQ_THM
    and q = y * b ** n                               by iterating_mul_eqn
        loop x y
     <= quit p q + n * cover (FUNPOW f n x) (FUNPOW modify n y))  by loop2_rise_rise_count_cover_exit_le
      = quit p q + n * cover (FUNPOW f n x) (y * b ** n)          by iterating_mul_eqn
      = quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
        (mop b m y) * cover (FUNPOW f (mop b m y) x) (y * b ** (mop b m y))
*)
val loop2_mul_rise_count_cover_exit_le = store_thm(
  "loop2_mul_rise_count_cover_exit_le",
  ``!loop f body quit cover exit b m.
          1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y =
                 if y = 0 \/ m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * cover (FUNPOW f (mop b m y) x) (y * b ** (mop b m y))``,
  rpt strip_tac >>
  assume_tac (mop_eq_loop2_count |> ISPEC ``b:num`` |> ISPEC ``f:num -> num``) >>
  first_x_assum (qspecl_then [`m`, `x`, `y`] strip_assume_tac) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qabbrev_tac `guard = \x:num y. y = 0 \/ m <= y` >>
  qabbrev_tac `modify = \y. b * y` >>
  qabbrev_tac `R = measure (\(x:num,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `y' < b * y'` by rw[] >>
  decide_tac) >>
  `!x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  `RISING modify` by rw[multiply_rising, Abbr`modify`] >>
  assume_tac loop2_rise_rise_count_cover_exit_le >>
  first_x_assum (qspecl_then [`loop`, `guard`, `body`, `quit`, `exit`, `modify`, `f`, `R`] strip_assume_tac) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`x`, `y`, `cover`] strip_assume_tac) >>
  qabbrev_tac `n = loop2_count guard modify f x y` >>
  `FUNPOW modify n y = y * b ** n` by rw[iterating_mul_eqn, Abbr`modify`] >>
  metis_tac[]);

(* Other similar theorems -- directly *)

(* Theorem: 1 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y =
                 if y = 0 \/ m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * body (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) *)
(* Proof: by loop2_mul_rise_count_cover_exit_le with cover = body. *)
val loop2_mul_rise_count_exit_le = store_thm(
  "loop2_mul_rise_count_exit_le",
  ``!loop f body quit exit b m. 1 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y =
                 if y = 0 \/ m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * body (FUNPOW f (mop b m y) x) (y * b ** (mop b m y))``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_mul_rise_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * cover (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) *)
(* Proof: by loop2_mul_rise_count_cover_exit_le with exit = F. *)
val loop2_mul_rise_count_cover_le = store_thm(
  "loop2_mul_rise_count_cover_le",
  ``!loop f body quit cover b m.
          1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * cover (FUNPOW f (mop b m y) x) (y * b ** (mop b m y))``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  `!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (b * y)` by metis_tac[] >>
  imp_res_tac loop2_mul_rise_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * body (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) *)
(* Proof: by loop2_mul_rise_count_cover_le with cover = body. *)
val loop2_mul_rise_count_le = store_thm(
  "loop2_mul_rise_count_le",
  ``!loop f body quit b m. 1 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * body (FUNPOW f (mop b m y) x) (y * b ** (mop b m y))``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_mul_rise_count_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y =
                 if y = 0 \/ m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * cover x (y * b ** (mop b m y)) *)
(* Proof:
   Let guard = (\x y. y = 0 \/ m <= y),
       modify = (\y. b * y),
       R = measure (\(x,y). m - y).
   Then WF R                                            by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by m - (b * x) < m - x, 1 < b, x <> 0
    and !x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                        by given
    and RISING modify                                   by multiply_rising
   Let g = \j. body (FUNPOW f j x) (FUNPOW modify j y),
       n = loop2_count guard modify f x y,
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = mop b m y                                by mop_eq_loop2_count
    and g = (\j. body (FUNPOW f j x) (y * b ** j))   by iterating_mul_eqn, FUN_EQ_THM
    and q = y * b ** n                               by iterating_mul_eqn
        loop x y
     <= quit p q + n * cover x (FUNPOW modify n y))  by loop2_fall_rise_count_cover_exit_le
      = quit p q + n * cover x (y * b ** n)          by iterating_mul_eqn
      = quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
        (mop b m y) * cover x (y * b ** (mop b m y))
*)
val loop2_mul_fall_count_cover_exit_le = store_thm(
  "loop2_mul_fall_count_cover_exit_le",
  ``!loop f body quit cover exit b m.
          1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y =
                 if y = 0 \/ m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * cover x (y * b ** (mop b m y))``,
  rpt strip_tac >>
  assume_tac (mop_eq_loop2_count |> ISPEC ``b:num`` |> ISPEC ``f:num -> num``) >>
  first_x_assum (qspecl_then [`m`, `x`, `y`] strip_assume_tac) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qabbrev_tac `guard = \x:num y. y = 0 \/ m <= y` >>
  qabbrev_tac `modify = \y. b * y` >>
  qabbrev_tac `R = measure (\(x:num,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `y' < b * y'` by rw[] >>
  decide_tac) >>
  `!x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  `RISING modify` by rw[multiply_rising, Abbr`modify`] >>
  imp_res_tac loop2_fall_rise_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`, `cover`] strip_assume_tac) >>
  qabbrev_tac `n = loop2_count guard modify f x y` >>
  `FUNPOW modify n y = y * b ** n` by rw[iterating_mul_eqn, Abbr`modify`] >>
  metis_tac[]);

(* Other similar theorems -- directly *)

(* Theorem: 1 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y =
                 if y = 0 \/ m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * body x (y * b ** (mop b m y)) *)
(* Proof: by loop2_mul_fall_count_cover_exit_le with cover = body. *)
val loop2_mul_fall_count_exit_le = store_thm(
  "loop2_mul_fall_count_exit_le",
  ``!loop f body quit exit b m. 1 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y =
                 if y = 0 \/ m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * body x (y * b ** (mop b m y))``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_mul_fall_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * cover x (y * b ** (mop b m y)) *)
(* Proof: by loop2_mul_fall_count_cover_exit_le with exit = F. *)
val loop2_mul_fall_count_cover_le = store_thm(
  "loop2_mul_fall_count_cover_le",
  ``!loop f body quit cover b m.
          1 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * cover x (y * b ** (mop b m y))``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  `!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (b * y)` by metis_tac[] >>
  imp_res_tac loop2_mul_fall_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * body x (y * b ** (mop b m y)) *)
(* Proof: by loop2_mul_fall_count_cover_le with cover = body *)
val loop2_mul_fall_count_le = store_thm(
  "loop2_mul_fall_count_le",
  ``!loop f body quit b m. 1 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             (mop b m y) * body x (y * b ** (mop b m y))``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_mul_fall_count_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Multiplying Loop with Transform cover                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\
          (!x y. RMONO (cover x) /\ MONO (combin$C cover y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if y = 0 \/ m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             mop b m y * cover (FUNPOW g (mop b m y) x) y *)
(* Proof:
   Let n = mop b m y,
       f1 = (\j. body (FUNPOW f j x) (y * b ** j)),
       f2 = K (cover (FUNPOW g n x) y).

   Claim: SUM (GENLIST f1 n) <= SUM (GENLIST f2 n)
   Proof: By SUM_LE, LENGTH_MAP, EL_MAP,
          this is to show: k < n ==>
            body (FUNPOW f k x) (y * b ** k) <= cover (FUNPOW g n x) y
          Note y <= y * b ** k                        by EXP_POS
           Now FUNPOW f k x <= FUNPOW g k x           by FUNPOW_LE_MONO, MONO g
           and FUNPOW g k x <= FUNPOW g n x           by FUNPOW_LE_RISING, k < n, RISING g
          Thus body (FUNPOW f k x) (y * b ** k)
            <= cover (FUNPOW f k x) (y * b ** k)      by body and cover property
            <= cover (FUNPOW f k x) y                 by RMONO (cover x), for fix x.
            <= cover (FUNPOW g n x) y                 by MONO (combin$C cover y), for fix y.

   Let p = FUNPOW f n x, q = y * b ** n.
        loop x y
     <= quit p q + SUM (GENLIST f1 n)                 by loop2_mul_count_sum_le
     <= quit p q + SUM (GENLIST f2 n)                 by claim
      = quit p q + SUM (GENLIST (K cover (FUNPOW g n x) y) n)   by notation
      = quit p q + n * cover (FUNPOW g n x)                     by SUM_GENLIST_K
      = quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
        (mop b m y) * cover (FUNPOW g (mop b m y) x) y
*)
val loop2_mul_mono_count_cover_exit_le = store_thm(
  "loop2_mul_mono_count_cover_exit_le",
  ``!loop f g body quit cover exit b m.
          1 < b /\ (!x y. body x y <= cover x y) /\
          (!x y. RMONO (cover x) /\ MONO (combin$C cover y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if y = 0 \/ m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             mop b m y * cover (FUNPOW g (mop b m y) x) y``,
  rpt strip_tac >>
  imp_res_tac loop2_mul_count_sum_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = mop b m y` >>
  qabbrev_tac `f1 = \j. body (FUNPOW f j x) (y * b ** j)` >>
  qabbrev_tac `f2:num -> num = K (cover (FUNPOW g n x) y)` >>
  `SUM (GENLIST f1 n) <= SUM (GENLIST f2 n)` by
  (irule SUM_LE >>
  rw[Abbr`f1`, Abbr`f2`] >>
  `y <= y * b ** k` by rw[] >>
  `FUNPOW f k x <= FUNPOW g k x` by rw[FUNPOW_LE_MONO] >>
  `FUNPOW g k x <= FUNPOW g n x` by rw[FUNPOW_LE_RISING] >>
  `FUNPOW f k x <= FUNPOW g n x` by decide_tac >>
  `body (FUNPOW f k x) (y * b ** k) <= cover (FUNPOW f k x) (y * b ** k)` by rw[] >>
  `cover (FUNPOW f k x) (y * b ** k) <= cover (FUNPOW f k x) y` by rw[] >>
  `cover (FUNPOW f k x) y <= cover (FUNPOW g n x) y` by metis_tac[combinTheory.C_THM] >>
  decide_tac) >>
  `SUM (GENLIST f2 n) = n * cover (FUNPOW g n x) y` by rw[SUM_GENLIST_K, Abbr`f2`] >>
  decide_tac);

(* Other similar theorems -- directly *)

(* Theorem: 1 < b /\
          (!x y. RMONO (body x) /\ MONO (combin$C body y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if y = 0 \/ m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             mop b m y * body (FUNPOW g (mop b m y) x) y *)
(* Proof: by loop2_mul_mono_count_cover_exit_le with cover = body. *)
val loop2_mul_mono_count_exit_le = store_thm(
  "loop2_mul_mono_count_exit_le",
  ``!loop f g body quit exit b m. 1 < b /\
          (!x y. RMONO (body x) /\ MONO (combin$C body y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if y = 0 \/ m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             mop b m y * body (FUNPOW g (mop b m y) x) y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_mul_mono_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\
          (!x y. RMONO (cover x) /\ MONO (combin$C cover y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             mop b m y * cover (FUNPOW g (mop b m y) x) y *)
(* Proof: by loop2_mul_mono_count_cover_exit_le with exit = F. *)
val loop2_mul_mono_count_cover_le = store_thm(
  "loop2_mul_mono_count_cover_le",
  ``!loop f g body quit cover b m.
          1 < b /\ (!x y. body x y <= cover x y) /\
          (!x y. RMONO (cover x) /\ MONO (combin$C cover y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             mop b m y * cover (FUNPOW g (mop b m y) x) y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  `!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (b * y)` by metis_tac[] >>
  imp_res_tac loop2_mul_mono_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 1 < b /\
          (!x y. RMONO (body x) /\ MONO (combin$C body y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             mop b m y * body (FUNPOW g (mop b m y) x) y *)
(* Proof: by loop2_mul_mono_count_cover_le with cover = body. *)
val loop2_mul_mono_count_le = store_thm(
  "loop2_mul_mono_count_le",
  ``!loop f g body quit b m. 1 < b /\
          (!x y. RMONO (body x) /\ MONO (combin$C body y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if y = 0 \/ m <= y then quit x y else body x y + loop (f x) (b * y)) ==>
           !x y. loop x y <= quit (FUNPOW f (mop b m y) x) (y * b ** (mop b m y)) +
                             mop b m y * body (FUNPOW g (mop b m y) x) y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_mul_mono_count_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Original investigation, some with quit = constant.                        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Multiplying List.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Given a number x, generate a multiplying list of b * x, up to some maximum m. *)
Definition multiply_by_def:
  multiply_by b m x =
  if (b <= 1) \/ (x = 0) \/ (m <= x) then [] else x::multiply_by b m (b * x)
Termination
  WF_REL_TAC `measure (λ(b,m,x). m - x)` >> rw[] >> `x < b * x` by rw[] >>
  decide_tac
End

(* Overload multiply_by 1 *)
val _ = overload_on ("doubling", ``multiply_by 2``);

(*
EVAL ``doubling 10 1``;= [1; 2; 4; 8]: thm
*)

(* Theorem: b <= 1 \/ x = 0 \/ m <= x ==> (multiply_by b m x = []) *)
(* Proof: by multiply_by_def *)
val multiply_by_nil = store_thm(
  "multiply_by_nil",
  ``!b m x. b <= 1 \/ x = 0 \/ m <= x ==> (multiply_by b m x = [])``,
  rw[Once multiply_by_def]);

(* Theorem: 1 < b /\ 0 < x /\ x < m ==> (multiply_by b m x = x :: multiply_by b m (b * x)) *)
(* Proof: by multiply_by_def *)
val multiply_by_cons = store_thm(
  "multiply_by_cons",
  ``!b m x. 1 < b /\ 0 < x /\ x < m ==> (multiply_by b m x = x :: multiply_by b m (b * x))``,
  rw[Once multiply_by_def]);

(*
EVAL ``multiply_by 3 10 1``; = [1; 3; 9]: thm
EVAL ``GENLIST (\j. 1 * 3 ** j) (mop 3 10 1)``; = [1; 3; 9]: thm
*)

(* Theorem: multiply_by b m x = GENLIST (\j. x * b ** j) (mop b m x) *)
(* Proof:
   Let f = (\j. b * (x * b ** j)), g = (\j. x * b ** j).
   Note f = g o SUC                   by FUN_EQ_THM, EXP
    and g 0 = x * 1 = x               by EXP_0
   By induction from multiply_by_def.
   If b <= 1 \/ x = 0 \/ m <= x,
        multiply_by b m n
      = []                            by multiply_by_nil
      = GENLIST g 0                   by GENLIST_0
      = GENLIST (mop b m x)           by mop_0
   Otherwise, 1 < b /\ x <> 0 /\ ~(m <= x).
       ~(b <= 1 \/ x = 0 \/ m <= x) /\ multiply_by b m (b * x) = GENLIST f (mop b m (b * x)) ==>
       multiply_by b m x = GENLIST g (mop b m x)

         multiply_by b m x
       = x::multiply_by b m (b * x)                  by multiply_by_cons
       = x::GENLIST f (mop b m (b * x))              by induction hypothesis
       = g 0 :: GENLIST (g o SUC) (mop b m (b * x))  by f = g o SUC, x = g 0
       = GENLIST g (SUC (mop b m (b * x))            by GENLIST_CONS
       = GENLIST g (mop b m x)                       by mop_suc
*)
val multiply_by_eqn = store_thm(
  "multiply_by_eqn",
  ``!b m x. multiply_by b m x = GENLIST (\j. x * b ** j) (mop b m x)``,
  ho_match_mp_tac (theorem "multiply_by_ind") >>
  rw[] >>
  Cases_on `(b <= 1) \/ (x = 0) \/ (m <= x)` >-
  metis_tac[mop_0, multiply_by_nil, GENLIST_0] >>
  `~(b <= 1) /\ x <> 0 /\ ~(m <= x)` by decide_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  rw[Once multiply_by_def] >>
  qabbrev_tac `f = \j. b * x * b ** j` >>
  qabbrev_tac `g = \j. x * b ** j` >>
  `f = g o SUC` by rw[FUN_EQ_THM, EXP, Abbr`f`, Abbr`g`] >>
  `x::GENLIST f (mop b m (b * x)) = g 0 :: GENLIST (g o SUC) (mop b m (b * x))` by rw[Abbr`g`] >>
  `_ = GENLIST g (SUC (mop b m (b * x)))` by rw[GENLIST_CONS] >>
  `_ = GENLIST g (mop b m x)` by metis_tac[mop_def] >>
  rw[]);;

(* Theorem: 1 < b /\ 0 < x /\ x * b ** j < m ==> MEM (x * b ** j) (multiply_by b m x) *)
(* Proof:
       MEM (x * b ** j) (multiply_by b m x)
   <=> MEM (x * b ** j) (GENLIST (\j. x * b ** j) (mop b m x))   by multiply_by_eqn
   <=> ?k. k < mop b m x /\ x * b ** j = x * b ** k              by MEM_GENLIST
   <=> take k = j, with k < mop b m x                            by mop_property
*)
val multiply_by_member = store_thm(
  "multiply_by_member",
  ``!b m x j. 1 < b /\ 0 < x /\ x * b ** j < m ==> MEM (x * b ** j) (multiply_by b m x)``,
  rw[multiply_by_eqn] >>
  rw[MEM_GENLIST] >>
  metis_tac[mop_property]);

(* Theorem: j < mop b m x ==> (EL j (multiply_by b m x) = x * b ** j) *)
(* Proof:
   Let f = (\j. x * b ** j).
     EL j (multiply_by b m x)
   = EL j (GENLIST f (mop b m x))   by multiply_by_eqn
   = f j                            by EL_GENLIST, j < mop b n
   = x * b ** j                     by notation
*)
val multiply_by_element = store_thm(
  "multiply_by_element",
  ``!b m x j. j < mop b m x ==> (EL j (multiply_by b m x) = x * b ** j)``,
  rw[multiply_by_eqn]);

(* Theorem: LENGTH (multiply_by b m x) = mop b m x *)
(* Proof:
     LENGTH (multiply_by b m x)
   = LENGTH (GENLIST (\j. x * b ** j) (mop b m x))     by multiply_by_eqn
   = mop b m x                                         by LENGTH_GENLIST
*)
val multiply_by_length = store_thm(
  "multiply_by_length",
  ``!b m x. LENGTH (multiply_by b m x) = mop b m x``,
  rw[multiply_by_eqn]);

(* Theorem: 1 < m ==> (LENGTH (doubling m 1) = LOG2 m + if m = 2 ** LOG2 m then 0 else 1) *)
(* Proof:
     LENGTH (doubling m 1)
   = LENGTH (multiply_by 2 m 1)                  by notation
   = mop 2 m 1                                   by multiply_by_length
   = LOG2 m + if m = 2 ** LOG2 m then 0 else 1   by mop_b_m_1
*)
val doubling_length = store_thm(
  "doubling_length",
  ``!m. 1 < m ==> (LENGTH (doubling m 1) = LOG2 m + if m = 2 ** LOG2 m then 0 else 1)``,
  rw[multiply_by_length, mop_b_m_1]);

(* Theorem: 1 < m ==> (doubling m 1 = GENLIST (\j. 2 ** j) (mop 2 m 1)) *)
(* Proof:
      doubling m 1
    = GENLIST (\j. 1 * 2 ** j) (mop 2 m 1)   by multiply_by_eqn
    = GENLIST (\j. 2 ** j) (mop 2 m 1)
*)
val doubling_eqn = store_thm(
  "doubling_eqn",
  ``!m. 1 < m ==> (doubling m 1 = GENLIST (\j. 2 ** j) (mop 2 m 1))``,
  rw[multiply_by_eqn]);

(* Theorem: 1 < b ==> (multiply_by b m x = loop_arg (\x. x = 0 \/ m <= x) (\x. b * x) x) *)
(* Proof:
   By induction from multiply_by_def.
   Let guard = (\x. x = 0 \/ m <= x),
       modify = (\x. b * x),
       R = measure (\x. m - x).
   Then WF R                               by WF_measure
    and !x. ~guard x ==> R (modify x) x    by m - (b * x) < m - x, 1 < b, x <> 0
   If guard x
           multiply_by b m x
         = []                              by multiply_by_nil, m <= x
         = loop_arg guard modify x         by loop_arg_nil, guard x
   If ~guard x
           multiply_by b m x
         = x :: multiply_by b m (b * x)             by multiply_by_cons, ~(m <= x)
         = x :: multiply_by b m (modify x)          by notation
         = x :: loop_arg guard modify (modify x)    by induction hypothesis
         = loop_arg guard modify x                  by loop_arg_cons, ~guard x
*)
val multiply_by_eq_loop_arg = store_thm(
  "multiply_by_eq_loop_arg",
  ``!b m x. 1 < b ==> (multiply_by b m x = loop_arg (\x. x = 0 \/ m <= x) (\x. b * x) x)``,
  ho_match_mp_tac (theorem "multiply_by_ind") >>
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0 \/ m <= x` >>
  qabbrev_tac `modify = \x. b * x` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `x' < b * x'` by rw[] >>
  decide_tac) >>
  Cases_on `guard x` >-
  metis_tac[multiply_by_nil, loop_arg_nil] >>
  qabbrev_tac `t = loop_arg guard modify (modify x)` >>
  `multiply_by b m x = x :: t` by metis_tac[multiply_by_cons, NOT_LESS, NOT_ZERO] >>
  `t = multiply_by b m (modify x)` by metis_tac[NOT_LESS] >>
  `loop_arg guard modify x = x::t` by metis_tac[loop_arg_cons] >>
  metis_tac[]);

(* Theorem: 1 < b ==> (MAP2 body (iterating f x (mop b m y)) (multiply_by b m y) =
                       MAP (UNCURRY body) (loop2_arg ((\x y. y = 0 \/ m <= y)) (\y. b * y) f x y)) *)
(* Proof:
   By induction from multiply_by_def.
   Let guard = (\x y. y = 0 \/ m <= y),
       modify = (\y. b * y),
       R = measure (\(x,y). m - y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by m - (b * x) < m - x, 1 < b, x <> 0

   If guard x y,
      Then y = 0 \/ m <= y                      by notation
      LHS = MAP2 body (iterating f x (mop b m 0)) (multiply_by b m 0)
          = MAP2 body (iterating f x 0) []      by mop_0, multiply_by_nil
          = MAP2 body [] []                     by iterating_nil
          = []                                  by MAP2
      RHS = MAP (UNCURRY body) (loop2_arg guard modify f x y)
          = MAP (UNCURRY body) []               by loop2_arg_nil, guard x y
          = [] = LHS                            by MAP

   If ~guard x y,
     Then y <> 0 /\ ~(m <= y),
       or 0 < y /\ y < m                        by notation
            MAP2 body (iterating f x (mop b m y)) (multiply_by b m y)
          = MAP2 body (iterating f x (SUC (mop b m (b * y)))) (y::multiply_by b m (b * y))
                                                by mop_suc, multiply_by_cons
          = MAP2 body (x::iterating f (f x) (mop b (b * y))) (y::multiply_by b m (b * y))
                                                by iterating_cons
          = body x y::MAP2 body (iterating f (f x) (mop b m (b * y))) (multiply_by b m (b * y))
                                                by MAP2
          = body x y::MAP (UNCURRY body) (loop2_arg guard modify f (f x) (b * y))
                                                by induction hypothesis
          = MAP (UNCURRY body) ((x,y):: loop2_arg guard modify f (f x) (b * y))
                                                by MAP, UNCURRY
          = MAP (UNCURRY body) (loop2_arg guard modify f x y)
                                                by loop2_arg_cons
*)
val iterating_multiply_eq_loop2_arg = store_thm(
  "iterating_multiply_eq_loop2_arg",
  ``!b m body f x y. 1 < b ==>
    (MAP2 body (iterating f x (mop b m y)) (multiply_by b m y) =
     MAP (UNCURRY body) (loop2_arg (\x y. y = 0 \/ m <= y) (\y. b * y) f x y))``,
  ntac 6 strip_tac >>
  qid_spec_tac `x` >>
  qid_spec_tac `y` >>
  qid_spec_tac `m` >>
  qid_spec_tac `b` >>
  ho_match_mp_tac (theorem "multiply_by_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x y. y = 0 \/ m <= y` >>
  qabbrev_tac `modify = \y. b * y` >>
  qabbrev_tac `R = measure (\(x,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `y' < b * y'` by rw[] >>
  decide_tac) >>
  Cases_on `guard x y` >| [
    `y = 0 \/ m <= y` by metis_tac[] >| [
      rw[iterating_nil, mop_0, multiply_by_nil, loop2_arg_nil] >>
      metis_tac[loop2_arg_nil],
      rw[iterating_nil, mop_0, multiply_by_nil, loop2_arg_nil] >>
      metis_tac[loop2_arg_nil]
    ],
    `y <> 0 /\ ~(m <= y)` by metis_tac[] >>
    rw[iterating_cons, mop_suc, multiply_by_cons] >>
    `body x y:: MAP2 body (iterating f (f x) (mop b m (modify y))) (multiply_by b m (modify y)) =
    body x y:: MAP2 body (iterating f (f x) (mop b m (b * y))) (multiply_by b m (b * y))` by rw[Abbr`modify`] >>
    `_ = body x y::MAP (UNCURRY body) (loop2_arg guard modify f (f x) (b * y))` by metis_tac[NOT_LESS] >>
    `_ = MAP (UNCURRY body) ((x,y)::loop2_arg guard modify f (f x) (modify y))` by rw[Abbr`modify`] >>
    metis_tac[loop2_arg_cons]
  ]);

(* ------------------------------------------------------------------------- *)
(* Multiplying Loop -- original                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\
          (!x. loop x = if x = 0 \/ m <= x then c else body x + loop (b * x)) ==>
           !x. loop x = c + SUM (MAP body (multiply_by b m x)) *)
(* Proof:
   Let guard = (\x. x = 0 \/ m <= x),
       modify = (\x. b * x),
       R = measure (\x. m - x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by m - (b * x) < m - x, 1 < b, x <> 0
   Also !x. loop x = if guard x then c else body x + loop (modify x)
                                          by given
   Thus loop x
      = c + SUM (MAP body (loop_arg guard modify x))  by loop_modify_count_by_sum
      = c + SUM (MAP body (multiply_by b m x))        by multiply_by_eq_loop_arg
*)
val loop_mul_count_by_sum = store_thm(
  "loop_mul_count_by_sum",
  ``!loop body b c m. 1 < b /\
       (!x. loop x = if x = 0 \/ m <= x then c else body x + loop (b * x)) ==>
        !x. loop x = c + SUM (MAP body (multiply_by b m x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0 \/ m <= x` >>
  qabbrev_tac `modify = \x. b * x` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `x < b * x` by rw[] >>
  decide_tac) >>
  `!x. loop x = if guard x then c else body x + loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_by_sum >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  `loop_arg guard modify x = multiply_by b m x` by rw[multiply_by_eq_loop_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 1 < b /\
       (!x. loop x = if x = 0 \/ m <= x then c else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= c + SUM (MAP body (multiply_by b m x)) *)
(* Proof:
   Let guard = (\x. x = 0 \/ m <= x),
       modify = (\x. b * x),
       R = measure (\x. m - x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by m - (b * x) < m - x, 1 < b, x <> 0
   Also !x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)
                                          by given
   Thus loop x
     <= c + SUM (MAP body (loop_arg guard modify x))  by loop_modify_count_exit_by_sum
      = c + SUM (MAP body (multiply_by b m x))        by multiply_by_eq_loop_arg
*)
val loop_mul_count_exit_by_sum = store_thm(
  "loop_mul_count_exit_by_sum",
  ``!loop body exit b c m. 1 < b /\
       (!x. loop x = if x = 0 \/ m <= x then c else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= c + SUM (MAP body (multiply_by b m x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0 \/ m <= x` >>
  qabbrev_tac `modify = \x. b * x` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `x < b * x` by rw[] >>
  decide_tac) >>
  `!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_exit_by_sum >>
  `loop_arg guard modify x = multiply_by b m x` by rw[multiply_by_eq_loop_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 1 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 \/ m <= x then c else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= c + cover x * mop b m x *)
(* Proof:
   Let guard = (\x. x = 0 \/ m <= x),
       modify = (\x. b * x),
       R = measure (\x. m - x).
   Then WF R                 by WF_measure
    and !x. ~guard x ==> R (modify x) x       by m - (b * x) < m - x, 1 < b, x <> 0
    and !x y. R x y ==> cover x <= cover y    by R, reverse order of RMONO cover, LESS_IMP_LESS_OR_EQ
    and !x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)
                                                     by given
        loop x
     <= c + cover x * loop_count guard modify x      by loop_modify_count_cover_exit_upper
      = c + cover x * mop b m x                      by mop_eq_loop_count
*)
val loop_mul_count_cover_exit_upper = store_thm(
  "loop_mul_count_cover_exit_upper",
  ``!loop body cover exit b m c. 1 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 \/ m <= x then c else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= c + cover x * mop b m x``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = 0 \/ m <= x` >>
  qabbrev_tac `modify = \x. b * x` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `x < b * x` by rw[] >>
  decide_tac) >>
  `!x y. R x y ==> cover x <= cover y` by rw[Abbr`R`] >>
  `!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  assume_tac (loop_modify_count_cover_exit_upper |> ISPEC ``loop:num -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `cover`, `exit`, `modify`, `R`] strip_assume_tac) >>
  `loop_count guard modify x = mop b m x` by rw[mop_eq_loop_count, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 1 < b /\ RMONO body /\
       (!x. loop x = if x = 0 \/ m <= x then c else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= c + body x * mop b m x *)
(* Proof: by loop_mul_count_cover_exit_upper, with cover = body. *)
val loop_mul_count_exit_upper = store_thm(
  "loop_mul_count_exit_upper",
  ``!loop body exit b m c. 1 < b /\ RMONO body /\
       (!x. loop x = if x = 0 \/ m <= x then c else body x + if exit x then 0 else loop (b * x)) ==>
        !x. loop x <= c + body x * mop b m x``,
  metis_tac[loop_mul_count_cover_exit_upper, LESS_EQ_REFL]);

(* Theorem: 1 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 \/ m <= x then c else body x + loop (b * x)) ==>
        !x. loop x <= c + cover x * mop b m x *)
(* Proof: by loop_mul_count_cover_exit_upper, with exit = F. *)
val loop_mul_count_cover_upper = store_thm(
  "loop_mul_count_cover_upper",
  ``!loop body cover b m c. 1 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if x = 0 \/ m <= x then c else body x + loop (b * x)) ==>
        !x. loop x <= c + cover x * mop b m x``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num. F` >>
  metis_tac[loop_mul_count_cover_exit_upper]);

(* Theorem: 1 < b /\ RMONO body /\
       (!x. loop x = if x = 0 \/ m <= x then c else body x + loop (b * x)) ==>
        !x. loop x <= c + body x * mop b m x *)
(* Proof: loop_mul_count_cover_upper, with body = cover. *)
val loop_mul_count_upper = store_thm(
  "loop_mul_count_upper",
  ``!loop body b m c. 1 < b /\ RMONO body /\
       (!x. loop x = if x = 0 \/ m <= x then c else body x + loop (b * x)) ==>
        !x. loop x <= c + body x * mop b m x``,
  metis_tac[loop_mul_count_cover_upper, LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)
(* Multiplying Loop with Transform -- original                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b /\
    (!x y. loop x y = if y = 0 \/ m <= y then c else body x y + loop (f x) (b * y)) ==>
     !x y. loop x y = c + SUM (MAP2 body (iterating f x (mop b m y)) (multiply_by b m y)) *)
(* Proof:
   Let guard = (\x y. y = 0 \/ m <= y),
       modify = (\y. b * y),
       R = measure (\(x,y). m - y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by m - (b * x) < m - x, 1 < b, x <> 0
    and !x y. loop x y = if guard x y then c else body x y + loop (f x) (modify y)   by given
        loop x y
      = c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))           by loop2_modify_count_by_sum
      = c + SUM (MAP2 body (iterating f x (mop b m y)) (multiply_by b m y))   by iterating_multiply_eq_loop2_arg
*)
val loop2_mul_count_by_sum = store_thm(
  "loop2_mul_count_by_sum",
  ``!loop f body b m c. 1 < b /\
    (!x y. loop x y = if y = 0 \/ m <= y then c else body x y + loop (f x) (b * y)) ==>
     !x y. loop x y = c + SUM (MAP2 body (iterating f x (mop b m y)) (multiply_by b m y))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. y = 0 \/ m <= y` >>
  qabbrev_tac `modify = \y. b * y` >>
  qabbrev_tac `R = measure (\(x,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `y < b * y` by rw[] >>
  decide_tac) >>
  `!x y. loop x y = if guard x y then c else body x y + loop (f x) (modify y)` by metis_tac[] >>
  assume_tac (loop2_modify_count_by_sum |> ISPEC ``loop:'a -> num -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `modify`, `f`, `R`] strip_assume_tac) >>
  `loop x y = c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))` by metis_tac[] >>
  `MAP (UNCURRY body) (loop2_arg guard modify f x y) =
    MAP2 body (iterating f x (mop b m y)) (multiply_by b m y)` by rw[iterating_multiply_eq_loop2_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 1 < b /\
    (!x y. loop x y = if y = 0 \/ m <= y then c else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
     !x y. loop x y <= c + SUM (MAP2 body (iterating f x (mop b m y)) (multiply_by b m y)) *)
(* Proof:
   Let guard = (\x y. y = 0 \/ m <= y),
       modify = (\y. b * y),
       R = measure (\(x,y). m - y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by m - (b * x) < m - x, 1 < b, x <> 0
    and !x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                        by given
        loop x y
     <= c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))          by loop2_modify_count_exit_by_sum
      = c + SUM (MAP2 body (iterating f x (mop b m y)) (multiply_by b m y))  by iterating_multiply_eq_loop2_arg
*)
val loop2_mul_count_exit_by_sum = store_thm(
  "loop2_mul_count_exit_by_sum",
  ``!loop f body b m c exit. 1 < b /\
    (!x y. loop x y = if y = 0 \/ m <= y then c else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
     !x y. loop x y <= c + SUM (MAP2 body (iterating f x (mop b m y)) (multiply_by b m y))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. y = 0 \/ m <= y` >>
  qabbrev_tac `modify = \y. b * y` >>
  qabbrev_tac `R = measure (\(x,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `y < b * y` by rw[] >>
  decide_tac) >>
  `!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  assume_tac (loop2_modify_count_exit_by_sum |> ISPEC ``loop:'a -> num -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `exit`, `modify`, `f`, `R`] strip_assume_tac) >>
  `loop x y <= c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))` by metis_tac[] >>
  `MAP (UNCURRY body) (loop2_arg guard modify f x y) =
    MAP2 body (iterating f x (mop b m y)) (multiply_by b m y)` by rw[iterating_multiply_eq_loop2_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x2 y2 <= cover x1 y1) /\
       (!x y. loop x y = if y = 0 \/ m <= y then c else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
        !x y. loop x y <= c + cover x y * mop b m y *)
(* Proof:
   Let guard = (\x y. y = 0 \/ m <= y),
       modify = (\y. b * y),
       R = measure (\(x,y). m - y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)    by m - (b * x) < m - x, 1 < b, x <> 0
    and !x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> cover x1 y1 <= cover x2 y2    by R, reverse order
    and !x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                     by given
        loop x y
     <= c + cover x y * loop2_count guard modify f x y       by loop2_modify_count_bcover_exit_upper
      = c + cover x y * mop b m y                            by mop_eq_loop2_count
*)
val loop2_mul_count_cover_exit_upper = store_thm(
  "loop2_mul_count_cover_exit_upper",
  ``!loop f body cover exit b m c. 1 < b /\
       (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x2 y2 <= cover x1 y1) /\
       (!x y. loop x y = if y = 0 \/ m <= y then c else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
        !x y. loop x y <= c + cover x y * mop b m y``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. y = 0 \/ m <= y` >>
  qabbrev_tac `modify = \y. b * y` >>
  qabbrev_tac `R = measure (\(x,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by
  (rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `y < b * y` by rw[] >>
  decide_tac) >>
  `!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> cover x1 y1 <= cover x2 y2` by rw[Abbr`R`] >>
  `!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  assume_tac (loop2_modify_count_bcover_exit_upper |> ISPEC ``loop:'a -> num -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `exit`, `cover`, `modify`, `f`, `R`] strip_assume_tac) >>
  `loop2_count guard modify f x y = mop b m y` by rw[mop_eq_loop2_count, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 1 < b /\ (!x1 x2 y1 y2. y1 <= y2 ==> body x2 y2 <= body x1 y1) /\
       (!x y. loop x y = if y = 0 \/ m <= y then c else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
        !x y. loop x y <= c + body x y * mop b m y *)
(* Proof: by loop2_mul_count_cover_exit_upper, with cover = body. *)
val loop2_mul_count_exit_upper = store_thm(
  "loop2_mul_count_exit_upper",
  ``!loop f body exit b m c. 1 < b /\
       (!x1 x2 y1 y2. y1 <= y2 ==> body x2 y2 <= body x1 y1) /\
       (!x y. loop x y = if y = 0 \/ m <= y then c else body x y + if exit x y then 0 else loop (f x) (b * y)) ==>
        !x y. loop x y <= c + body x y * mop b m y``,
  rpt strip_tac >>
  assume_tac loop2_mul_count_cover_exit_upper >>
  last_x_assum (qspecl_then [`loop`, `f`, `body`, `body`, `exit`, `b`, `m`,`c`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* Theorem: 1 < b /\ (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x2 y2 <= cover x1 y1) /\
       (!x y. loop x y = if y = 0 \/ m <= y then c else body x y + loop (f x) (b * y)) ==>
        !x y. loop x y <= c + cover x y * mop b m y *)
(* Proof: by loop2_mul_count_cover_exit_upper, with exit = F. *)
val loop2_mul_count_cover_upper = store_thm(
  "loop2_mul_count_cover_upper",
  ``!loop f body cover b m c. 1 < b /\ (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x2 y2 <= cover x1 y1) /\
       (!x y. loop x y = if y = 0 \/ m <= y then c else body x y + loop (f x) (b * y)) ==>
        !x y. loop x y <= c + cover x y * mop b m y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:'a y:num. F` >>
  assume_tac loop2_mul_count_cover_exit_upper >>
  last_x_assum (qspecl_then [`loop`, `f`, `body`, `cover`, `exit`, `b`, `m`, `c`] strip_assume_tac) >>
  metis_tac[]);

(* Theorem: 1 < b /\ (!x1 x2 y1 y2. y1 <= y2 ==> body x2 y2 <= body x1 y1) /\
    (!x y. loop x y = if y = 0 \/ m <= y then c else body x y + loop (f x) (b * y)) ==>
     !x y. loop x y <= c + body x y * mop b m y *)
(* Proof: loop2_mul_count_cover_upper, with body = cover. *)
val loop2_mul_count_upper = store_thm(
  "loop2_mul_count_upper",
  ``!loop f body b m c. 1 < b /\ (!x1 x2 y1 y2. y1 <= y2 ==> body x2 y2 <= body x1 y1) /\
    (!x y. loop x y = if y = 0 \/ m <= y then c else body x y + loop (f x) (b * y)) ==>
     !x y. loop x y <= c + body x y * mop b m y``,
  rpt strip_tac >>
  assume_tac loop2_mul_count_cover_upper >>
  last_x_assum (qspecl_then [`loop`, `f`, `body`, `body`, `b`, `m`, `c`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
