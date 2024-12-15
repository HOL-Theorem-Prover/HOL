(* ------------------------------------------------------------------------- *)
(* Loop Recurrence with Increasing argument to a maximum                     *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "loopIncrease";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open arithmeticTheory dividesTheory numberTheory combinatoricsTheory listTheory
     rich_listTheory listRangeTheory;

open loopTheory;

val _ = temp_overload_on ("RISING", ``\f. !x:num. x <= f x``);
val _ = temp_overload_on ("FALLING", ``\f. !x:num. f x <= x``);

(* ------------------------------------------------------------------------- *)
(* Loop Recurrence with Increasing argument Documentation                    *)
(* ------------------------------------------------------------------------- *)
(* Type and Overload:
   increasing       = increase_by 1
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Increasing Count:
   bop_def             |- !x m b. bop b m x = if b = 0 \/ m <= x then 0 else SUC (bop b m (x + b))
   bop_0               |- !b m x. b = 0 \/ m <= x ==> bop b m x = 0
   bop_suc             |- !b m x. 0 < b /\ x < m ==> bop b m x = SUC (bop b m (x + b))
   bop_property        |- !b m x. 0 < b ==> !j. x + b * j < m <=> j < bop b m x
   bop_exceeds         |- !b m x. 0 < b ==> m <= x + b * bop b m x
   bop_eqn             |- !b m x. bop b m x =
                                  if b = 0 \/ m <= x then 0
                                  else (m - x) DIV b + if (m - x) MOD b = 0 then 0 else 1
   bop_DIV             |- !b m x. bop b m x <= 1 + (m - x) DIV b
   bop_1_m_c           |- !m c. bop 1 m c = n - c
   bop_eq_loop_count   |- !b m x. 0 < b ==> bop b m x = loop_count (\x. m <= x) (\x. x + b) x
   bop_eq_loop2_count  |- !b f m x y. 0 < b ==>
                                      bop b m y = loop2_count (\x y. m <= y) (\y. y + b) f x y

   increase_rising     |- !b. RISING (\x. x + b)
   iterating_inc_eqn   |- !b n x. FUNPOW (\x. x + b) n x = x + n * b
   iterating_inc_bop   |- !b m x. 0 < b ==> m <= FUNPOW (\x. x + b) (bop b m x) x
   iterating_inc_bop_alt
                       |- !b m x. 0 < b ==> m <= x + bop b m x * b

   Increase Loop:
   loop_inc_count_eqn  |- !loop body quit b m. 0 < b /\
                          (!x. loop x = if m <= x then quit x else body x + loop (x + b)) ==>
                           !x. loop x = quit (x + bop b m x * b) +
                                        SUM (GENLIST (\j. body (x + j * b)) (bop b m x))
   loop_inc_count_exit_sum_le
                       |- !loop body quit exit b m. 0 < b /\
                          (!x. loop x =
                               if m <= x then quit x
                               else body x + if exit x then 0 else loop (x + b)) ==>
                           !x. loop x <= quit (x + bop b m x * b) +
                                         SUM (GENLIST (\j. body (x + j * b)) (bop b m x))
   loop_inc_count_cover_exit_le
                       |- !loop body quit cover exit b m. 0 < b /\
                          (!x. body x <= cover x) /\ MONO cover /\
                          (!x. loop x =
                               if m <= x then quit x
                               else body x + if exit x then 0 else loop (x + b)) ==>
                           !x. loop x <= quit (x + bop b m x * b) +
                                         bop b m x * cover (x + bop b m x * b)
   loop_inc_count_cover_exit_le_alt
                       |- !loop body quit cover exit b m. 0 < b /\
                          (!x. body x <= cover x) /\ MONO cover /\
                          (!x. loop x = if m <= x then quit x else body x + if exit x then 0 else loop (x + b)) ==>
                           !x. (let n = bop b m x
                                 in loop x <= quit (x + n * b) + n * cover (x + n * b))
   loop_inc_count_exit_le
                       |- !loop body quit exit b m. 0 < b /\ MONO body /\
                          (!x. loop x =
                               if m <= x then quit x
                               else body x + if exit x then 0 else loop (x + b)) ==>
                           !x. loop x <= quit (x + bop b m x * b) +
                                         bop b m x * body (x + bop b m x * b)
   loop_inc_count_cover_le
                       |- !loop body quit cover b m. 0 < b /\
                          (!x. body x <= cover x) /\ MONO cover /\
                          (!x. loop x = if m <= x then quit x else body x + loop (x + b)) ==>
                           !x. loop x <= quit (x + bop b m x * b) +
                                         bop b m x * cover (x + bop b m x * b)
   loop_inc_count_le   |- !loop body quit b m. 0 < b /\ MONO body /\
                          (!x. loop x = if m <= x then quit x else body x + loop (x + b)) ==>
                           !x. loop x <= quit (x + bop b m x * b) +
                                         bop b m x * body (x + bop b m x * b)
   loop_inc_count_rcover_exit_le
                       |- !loop body quit cover exit b m. 0 < b /\
                          (!x. body x <= cover x) /\ RMONO cover /\
                          (!x. loop x =
                               if m <= x then quit x
                               else body x + if exit x then 0 else loop (x + b)) ==>
                           !x. loop x <= quit (x + bop b m x * b) + bop b m x * cover x
   loop_inc_count_rbody_exit_le
                       |- !loop body quit exit b m. 0 < b /\ RMONO body /\
                          (!x. loop x =
                               if m <= x then quit x
                               else body x + if exit x then 0 else loop (x + b)) ==>
                           !x. loop x <= quit (x + bop b m x * b) + bop b m x * body x
   loop_inc_count_rcover_le
                       |- !loop body quit cover b m. 0 < b /\
                          (!x. body x <= cover x) /\ RMONO cover /\
                          (!x. loop x = if m <= x then quit x else body x + loop (x + b)) ==>
                           !x. loop x <= quit (x + bop b m x * b) + bop b m x * cover x
   loop_inc_count_rbody_le
                       |- !loop body quit b m. 0 < b /\ RMONO body /\
                          (!x. loop x = if m <= x then quit x else body x + loop (x + b)) ==>
                           !x. loop x <= quit (x + bop b m x * b) + bop b m x * body x

   Increase Loop with Transform:
   loop2_inc_count_eqn |- !loop f body quit b m. 0 < b /\
                          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
                           !x y. loop x y = quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                            SUM (GENLIST (\j. body (FUNPOW f j x) (y + j * b)) (bop b m y))
   loop2_inc_count_sum_le
                       |- !loop f body quit exit b m. 0 < b /\
                          (!x y. loop x y =
                                 if m <= y then quit x y
                                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
                           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                             SUM (GENLIST (\j. body (FUNPOW f j x) (y + j * b)) (bop b m y))

   Increasing Loop with Transform-independent Body:
   loop2_inc_count_mono_cover_exit_le
                   |- !loop f body quit cover exit b m g. 0 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y =
                             if m <= y then quit x y
                             else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                         bop b m y * g (y + bop b m y * b)
   loop2_inc_count_mono_exit_le
                   |- !loop f body quit exit b m g. 0 < b /\ body = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y =
                             if m <= y then quit x y
                             else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                         bop b m y * g (y + bop b m y * b)
   loop2_inc_count_mono_cover_le
                   |- !loop f body quit cover b m g. 0 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                         bop b m y * g (y + bop b m y * b)
   loop2_inc_count_mono_le
                   |- !loop f body quit b m g. 0 < b /\ body = (\x y. g y) /\ MONO g /\
                      (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                         bop b m y * g (y + bop b m y * b)
   loop2_inc_count_rmono_cover_exit_le
                   |- !loop f body quit cover exit b m g. 0 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y =
                             if m <= y then quit x y
                             else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                         bop b m y * g 0
   loop2_inc_count_rmono_exit_le
                   |- !loop f body quit exit b m g. 0 < b /\ body = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y =
                             if m <= y then quit x y
                             else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                         bop b m y * g 0
   loop2_inc_count_rmono_cover_le
                   |- !loop f body quit cover b m g. 0 < b /\
                      (!x y. body x y <= cover x y) /\ cover = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                         bop b m y * g 0
   loop2_inc_count_rmono_le
                   |- !loop f body quit b m g. 0 < b /\ body = (\x y. g y) /\ RMONO g /\
                      (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
                       !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                         bop b m y * g 0

   Increasing Loop with Numeric Transform:
   loop2_inc_rise_count_cover_exit_le
                       |- !loop f body quit cover exit b m. 0 < b /\
                          (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
                          (!x y. loop x y =
                                 if m <= y then quit x y
                                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
                           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                             bop b m y * cover (FUNPOW f (bop b m y) x) (y + bop b m y * b)
   loop2_inc_rise_count_exit_le
                       |- !loop f body quit exit b m. 0 < b /\ MONO2 body /\ RISING f /\
                          (!x y. loop x y =
                                 if m <= y then quit x y
                                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
                           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                             bop b m y * body (FUNPOW f (bop b m y) x) (y + bop b m y * b)
   loop2_inc_rise_count_cover_le
                       |- !loop f body quit cover b m. 0 < b /\
                          (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
                          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
                           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                             bop b m y * cover (FUNPOW f (bop b m y) x) (y + bop b m y * b)
   loop2_inc_rise_count_le
                       |- !loop f body quit b m. 0 < b /\ MONO2 body /\ RISING f /\
                          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
                           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                             bop b m y * body (FUNPOW f (bop b m y) x) (y + bop b m y * b)

   loop2_inc_fall_count_cover_exit_le
                       |- !loop f body quit cover exit b m. 0 < b /\
                          (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
                          (!x y. loop x y =
                                 if m <= y then quit x y
                                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
                           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                             bop b m y * cover x (y + bop b m y * b)
   loop2_inc_fall_count_exit_le
                       |- !loop f body quit exit b m. 0 < b /\ MONO2 body /\ FALLING f /\
                          (!x y. loop x y =
                                 if m <= y then quit x y
                                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
                           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                             bop b m y * body x (y + bop b m y * b)
   loop2_inc_fall_count_cover_le
                       |- !loop f body quit cover b m. 0 < b /\
                          (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
                          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
                           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                             bop b m y * cover x (y + bop b m y * b)
   loop2_inc_fall_count_le
                       |- !loop f body quit b m. 0 < b /\ MONO2 body /\ FALLING f /\
                          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
                           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                             bop b m y * body x (y + bop b m y * b)

   Increasing Loop with Transform cover:
   loop2_inc_mono_count_cover_exit_le
                       |- !loop f g body quit cover exit b m. 0 < b /\
                          (!x y. body x y <= cover x y) /\
                          (!x y. RMONO (cover x) /\ MONO (combin$C cover y)) /\
                          (!x. f x <= g x) /\ MONO g /\ RISING g /\
                          (!x y. loop x y =
                                 if m <= y then quit x y
                                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
                           !x y. loop x y <=  quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                              bop b m y * cover (FUNPOW g (bop b m y) x) y
   loop2_inc_mono_count_exit_le
                        |- !loop f g body quit exit b m. 0 < b /\
                           (!x y. RMONO (body x) /\ MONO (combin$C body y)) /\
                           (!x. f x <= g x) /\ MONO g /\ RISING g /\
                           (!x y. loop x y =
                                  if m <= y then quit x y
                                  else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
                            !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                              bop b m y * body (FUNPOW g (bop b m y) x) y
   loop2_inc_mono_count_cover_le
                       |- !loop f g body quit cover b m. 0 < b /\
                          (!x y. body x y <= cover x y) /\
                          (!x y. RMONO (cover x) /\ MONO (combin$C cover y)) /\
                          (!x. f x <= g x) /\ MONO g /\ RISING g /\
                          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
                           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                             bop b m y * cover (FUNPOW g (bop b m y) x) y
   loop2_inc_mono_count_le
                       |- !loop f g body quit b m. 0 < b /\
                          (!x y. RMONO (body x) /\ MONO (combin$C body y)) /\
                          (!x. f x <= g x) /\ MONO g /\ RISING g /\
                          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
                           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + bop b m y * b) +
                                             bop b m y * body (FUNPOW g (bop b m y) x) y

   Original:
   Increasing List:
   increase_by_def     |- !x m b. increase_by b m x =
                                      if b = 0 \/ m <= x then [] else x::increase_by b m (x + b)
   increase_by_nil     |- !b m x. b = 0 \/ m <= x ==> increase_by b m x = []
   increase_by_cons    |- !b m x. 0 < b /\ x < m ==> increase_by b m x = x::increase_by b m (x + b)
   increase_by_eqn     |- !b m x. increase_by b m x = GENLIST (\j. x + j * b) (bop b m x)
   increase_by_member  |- !b m x j. 0 < b /\ x + j * b < m ==> MEM (x + j * b) (increase_by b m x)
   increase_by_element |- !b m x j. j < bop b m x ==> EL j (increase_by b m x) = x + j * b
   increase_by_length  |- !b m x. LENGTH (increase_by b m x) = bop b m x
   increasing_length   |- !m c. LENGTH (increasing m c) = m - c
   increasing_eqn      |- !m c. increasing m c = [c ..< m]
   increase_by_eq_loop_arg
                       |- !b m x. 0 < b ==> increase_by b m x = loop_arg (\x. m <= x) (\x. x + b) x
   iterating_increase_eq_loop2_arg
                       |- !b m body f x y. 0 < b ==>
                               MAP2 body (iterating f x (bop b m y)) (increase_by b m y) =
                               MAP (UNCURRY body) (loop2_arg (\x y. m <= y) (\y. y + b) f x y)
   loop_inc_count_by_sum
                       |- !loop body b c m. 0 < b /\
                          (!x. loop x = if m <= x then c else body x + loop (x + b)) ==>
                           !x. loop x = c + SUM (MAP body (increase_by b m x))
   loop_inc_count_exit_by_sum
                       |- !loop body exit b c m. 0 < b /\
                          (!x. loop x =
                               if m <= x then c
                               else body x + if exit x then 0 else loop (x + b)) ==>
                           !x. loop x <= c + SUM (MAP body (increase_by b m x))
   loop_inc_count_cover_exit_upper
                       |- !loop body cover exit b m c. 0 < b /\
                          (!x. body x <= cover x) /\ RMONO cover /\
                          (!x. loop x =
                               if m <= x then c
                               else body x + if exit x then 0 else loop (x + b)) ==>
                           !x. loop x <= c + cover x * bop b m x
   loop_inc_count_exit_upper
                       |- !loop body exit b m c. 0 < b /\ RMONO body /\
                          (!x. loop x =
                               if m <= x then c
                               else body x + if exit x then 0 else loop (x + b)) ==>
                           !x. loop x <= c + body x * bop b m x
   loop_inc_count_cover_upper
                       |- !loop body cover b m c. 0 < b /\
                          (!x. body x <= cover x) /\ RMONO cover /\
                          (!x. loop x = if m <= x then c else body x + loop (x + b)) ==>
                           !x. loop x <= c + cover x * bop b m x
   loop_inc_count_upper|- !loop body b m c. 0 < b /\ RMONO body /\
                          (!x. loop x = if m <= x then c else body x + loop (x + b)) ==>
                           !x. loop x <= c + body x * bop b m x

   loop2_inc_count_by_sum
                   |- !loop f body b m c. 0 < b /\
                      (!x y. loop x y = if m <= y then c else body x y + loop (f x) (y + b)) ==>
                       !x y. loop x y = c + SUM (MAP2 body (iterating f x (bop b m y)) (increase_by b m y))
   loop2_inc_count_exit_by_sum
                   |- !loop f body b m c exit. 0 < b /\
                      (!x y. loop x y =
                             if m <= y then c
                             else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
                       !x y. loop x y <= c + SUM (MAP2 body (iterating f x (bop b m y)) (increase_by b m y))
   loop2_inc_count_cover_exit_upper
                   |- !loop f body cover exit b m c. 0 < b /\
                      (!x y. body x y <= cover x y) /\
                      (!x1 x2 y1 y2. y1 <= y2 ==> cover x2 y2 <= cover x1 y1) /\
                      (!x y. loop x y =
                             if m <= y then c
                             else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
                       !x y. loop x y <= c + cover x y * bop b m y
   loop2_inc_count_exit_upper
                   |- !loop f body exit b m c. 0 < b /\
                      (!x1 x2 y1 y2. y1 <= y2 ==> body x2 y2 <= body x1 y1) /\
                      (!x y. loop x y =
                             if m <= y then c
                             else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
                       !x y. loop x y <= c + body x y * bop b m y
   loop2_inc_count_cover_upper
                   |- !loop f body cover b m c. 0 < b /\
                      (!x y. body x y <= cover x y) /\
                      (!x1 x2 y1 y2. y1 <= y2 ==> cover x2 y2 <= cover x1 y1) /\
                      (!x y. loop x y = if m <= y then c else body x y + loop (f x) (y + b)) ==>
                       !x y. loop x y <= c + cover x y * bop b m y
   loop2_inc_count_upper
                   |- !loop f body b m c. 0 < b /\
                      (!x1 x2 y1 y2. y1 <= y2 ==> body x2 y2 <= body x1 y1) /\
                      (!x y. loop x y = if m <= y then c else body x y + loop (f x) (y + b)) ==>
                       !x y. loop x y <= c + body x y * bop b m y

*)

(* ------------------------------------------------------------------------- *)
(* Helper                                                                    *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Loop Recurrence with Increasing argument to a maximum                     *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Increasing Count.                                                         *)
(* ------------------------------------------------------------------------- *)
(*
> loop_count_thm |> SPEC_ALL |> INST_TYPE [alpha |-> ``:num``] |> Q.INST [`modify` |-> `\x. x + b`, `guard` |-> `\x. m <= x`];
val it = |- WF R /\ (!x. ~(\x. m <= x) x ==> R ((\x. x + b) x) x) ==>
      !x. loop_count (\x. m <= x) (\x. x + b) x =
          if (\x. m <= x) x then 0
          else SUC (loop_count (\x. m <= x) (\x. x + b) ((\x. x + b) x)): thm
*)

(* Given a number x, count then number of x + b, up to some maximum m. *)
(* This definition is tied to loop_count, and not computationally effective.
val bop_def = Define`
    bop b m x = loop_count (\x. m <= x) (\x. x + b) x
`;
*)

Definition bop_def:
  bop b m x =
  if (b = 0) \/ (m <= x) then 0 else SUC (bop b m (x + b))
Termination WF_REL_TAC ‘measure (λ(b,m,x). m - x)’
End

(* Theorem: b = 0 \/ m <= x ==> (bop b m x = 0) *)
(* Proof: by bop_def *)
val bop_0 = store_thm(
  "bop_0",
  ``!b m x. b = 0 \/ m <= x ==> (bop b m x = 0)``,
  rw[Once bop_def]);

(* Theorem: 0 < b /\ x < m ==> (bop b m x = SUC (bop b m (x + b))) *)
(* Proof: by bop_def *)
val bop_suc = store_thm(
  "bop_suc",
  ``!b m x. 0 < b /\ x < m ==> (bop b m x = SUC (bop b m (x + b)))``,
  rw[Once bop_def]);

(* Theorem: 0 < b ==> !j. x + b * j < m <=> j < bop b m x *)
(* Proof:
   By induction from bop_def.
   If m <= x + b,
           bop b m x
         = 1 + bop b m (x + b)     by bop_def, x < m
         = 1 + 0 = 1               by bop_0, m <= x + b
      If j = 0, LHS = T = RHS      by bop_pos, x < m, 0 < 1
      If j <> 0, LHS = F = RHS     by b <= b * j when j <> 0
   Otherwise b + x < m,
      Then b + (x + b * (j - 1)) < m <=> j - 1 < bop b m (x + b)
                                   by induction hypothesis
      If j = 0, LHS = T = RHS      by bop_def, b + x < m
      If j <> 0,
          b + x + b * j < m + b <=> j < 1 + bop b m (x + b)  by above
      or          x + b * j < m <=> j < bop b m x            by bop_suc
*)
val bop_property = store_thm(
  "bop_property",
  ``!b m x. 0 < b ==> !j. x + b * j < m <=> j < bop b m x``,
  ho_match_mp_tac (theorem "bop_ind") >>
  rw[] >>
  Cases_on `m <= x + b` >| [
    (Cases_on `j = 0` >> simp[Once bop_def]) >>
    `b <= b * j` by rw[] >>
    rw[Once bop_def],
    `b + (x + b * (j - 1)) < m <=> j - 1 < bop b m (b + x)` by rw[] >>
    (Cases_on `j = 0` >> simp[Once bop_def])
  ]);

(* Theorem: 0 < b ==> m <= x + b * bop b m x *)
(* Proof:
   Note     x + b * (bop b m x) < m
        <=> bop b m x < bop b m x     by bop_property
        <=> F
   Thus m <= x + b * hop b m x is true.
*)
val bop_exceeds = store_thm(
  "bop_exceeds",
  ``!b m x. 0 < b ==> m <= x + b * bop b m x``,
  metis_tac[bop_property, LESS_EQ_REFL, NOT_LESS]);

(*
val foo_def = Define`
    foo b m x = if (b = 0) \/ (m <= x) then 0 else ((m - x) DIV b + if (m - x) MOD b = 0 then 0 else 1)
`;

> EVAL ``MAP (bop 2 10) [1 .. 20]``; = [5; 4; 4; 3; 3; 2; 2; 1; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]: thm
> EVAL ``MAP (foo 2 10) [1 .. 20]``; = [5; 4; 4; 3; 3; 2; 2; 1; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]: thm
*)

(* Theorem: bop b m x = if (b = 0) \/ (m <= x) then 0 else ((m - x) DIV b + if (m - x) MOD b = 0 then 0 else 1) *)
(* Proof:
   By induction from bop_def.
   If b = 0,
      Then bop b m x = 0              by bop_def
   If m <= x,
      LHS = bop b m x = 0             by bop_def
      RHS = 0 + 0 = 0 = LHS           by ZERO_DIV, ZERO_MOD
   Otherwise, b <> 0 and x < m.
        bop b m x
      = SUC (bop b m (x + b))         by bop_def
      = SUC (if m <= x + b then 0 else (m - (x + b)) DIV b + if (m - (x + b)) MOD b = 0 then 0 else 1)))
                                      by induction hypothesis
   If m <= x + b,
      Then m - x <= b, and m - (x + b) = m - x - b.
      If (m - x) MOD b = 0,
         Then b divdes (m - x)        by DIVIDES_MOD_0
           so b <= m - x              by DIVIDES_LE
         Thus b = m - x               by m - x <= b, b <= m - x
           or (m - x) DIV b = 1       by DIVMOD_ID
          and bop b m x = 1           by bop_def
      If (m - x) MOD b <> 0,
         Then m - x <> b              by DIVMOD_ID
           so m - x < b               by m - x <= b, m - x <> b
           or (m - x) DIV b = 0       by LESS_DIV_EQ_ZERO
          and bop b m x = 1           by bop_def

   If ~(m <= x + b),
       LHS = bop b m x
           = SUC (bop b m (x + b))    by bop_def
           = SUC ((m - (x + b)) DIV b + if (m - (x + b)) MOD b = 0 then 0 else 1)
                                      by induction hypothesis
       But (m - (x + b)) DIV b = (m - x) DIV b - 1       by SUB_DIV
       and (m - (x + b)) MOD b = (m - x) MOD b           by SUB_MOD
       and (m - x) DIV b <> 0                            by DIV_EQUAL_0
       LHS = 1 + ((m - x) DIV b - 1  + if ((m - x) MOD b) then 0 else 1)    by ADD1
           = (m - x) DIV b + (if ((m - x) MOD b = 0) then 0 else 1)         by (m - x) DIV b <> 0
           = RHS
*)
val bop_eqn = store_thm(
  "bop_eqn",
  ``!b m x. bop b m x =
           if (b = 0) \/ (m <= x) then 0 else ((m - x) DIV b + if (m - x) MOD b = 0 then 0 else 1)``,
  ho_match_mp_tac (theorem "bop_ind") >>
  (rw[] >> simp[Once bop_def]) >| [
    `m - x <= b` by decide_tac >>
    `b <= m - x` by rw[DIVIDES_MOD_0, DIVIDES_LE] >>
    `m - x = b` by decide_tac >>
    rw[],
    `m - x <= b` by decide_tac >>
    `m - x <> b` by metis_tac[DIVMOD_ID, NOT_ZERO] >>
    `m - x < b` by decide_tac >>
    metis_tac[DIV_EQUAL_0, NOT_ZERO, ADD],
    `(m - x - b) DIV b = (m - x) DIV b - 1` by rw[SUB_DIV] >>
    `~(m - x <= b)` by decide_tac >>
    `(m - x) DIV b <> 0` by rw[DIV_EQUAL_0] >>
    fs[],
    `m - (b + x) = m - x - b` by decide_tac >>
    `b <= m - x` by decide_tac >>
    `(m - x - b) MOD b = (m - x) MOD b` by rw[SUB_MOD] >>
    fs[],
    `m - (b + x) = m - x - b` by decide_tac >>
    `b <= m - x` by decide_tac >>
    `(m - x - b) MOD b = (m - x) MOD b` by rw[SUB_MOD] >>
    fs[],
    `(m - x - b) DIV b = (m - x) DIV b - 1` by rw[SUB_DIV] >>
    `~(m - x <= b)` by decide_tac >>
    `(m - x) DIV b <> 0` by rw[DIV_EQUAL_0] >>
    fs[]
  ]);

(* Theorem: bop b m x <= 1 + (m - x) DIV b *)
(* Proof: by hop_eqn *)
val bop_DIV = store_thm(
  "bop_DIV",
  ``!b m x. bop b m x <= 1 + (m - x) DIV b``,
  rw[bop_eqn]);

(* Theorem: bop 1 m c = m - c *)
(* Proof:
     bop 1 m c
   = (m - c) DIV 1 + if (m - c) MOD 1 = 0 then 0 else 1   by bop_eqn
   = (m - c) + if 0 = 0 then 0 else 1                     by DIV_1, MOD_1
   = m - c
*)
val bop_1_m_c = store_thm(
  "bop_1_m_c",
  ``!m c. bop 1 m c = m - c``,
  rw[bop_eqn]);

(* Theorem: 0 < b ==> (bop b m x = loop_count (\x. m <= x) (\x. x + b) x) *)
(* Proof:
   By induction from bop_def.
   Let guard = (\x. m <= x),
       modify = (\x. x + b),
       R = measure (\x. m - x).
   The goal is: bop b m x = loop_count guard modify x

   Note WF R                               by WF_measure
    and !x. ~guard x ==> R (modify x) x    by m - (x + b) < m - x, 0 < b
   If guard x,
      Then m <= x                          by guard x
           bop b m 0
         = 0                               by bop_0
         = loop_count guard modify 0       by loop_count_0, guard x
   If ~guard x,
      Then ~(m <= x), or x < m             by ~guard x
           hop b m x
         = SUC (hop b m (x + b))           by hop_suc
         = SUC (loop_count guard modify (x + b))
                                           by induction hypothesis
         = loop_count guard modify x       by loop_count_suc
*)
val bop_eq_loop_count = store_thm(
  "bop_eq_loop_count",
  ``!b m x. 0 < b ==> (bop b m x = loop_count (\x. m <= x) (\x. x + b) x)``,
  ho_match_mp_tac (theorem "bop_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x. m <= x` >>
  qabbrev_tac `modify = \x. b + x` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`modify`, Abbr`R`] >>
  Cases_on `guard x` >| [
    `m <= x` by metis_tac[] >>
    metis_tac[bop_0, loop_count_0],
    `~(m <= x)` by metis_tac[] >>
    `x < m` by decide_tac >>
    `bop b m x = SUC (bop b m (b + x))` by metis_tac[bop_suc, ADD_COMM] >>
    `_ = SUC (loop_count guard modify (b + x))` by metis_tac[NOT_ZERO] >>
    `_ = loop_count guard modify x` by metis_tac[loop_count_suc] >>
    decide_tac
  ]);

(* Theorem: 0 < b ==> (bop b m y = loop2_count (\x y. m <= y) (\y. y + b) f x y) *)
(* Proof:
   By induction from bop_def.
   Let guard = (\x y. m <= y),
       modify = (\y. y + b),
       R = measure (\(x, y). m - y).
   Then WF R                               by WF_measure
    and !x. ~guard x y ==> R (modify x) x  by m - (x + b) < m - x, 0 < b
   If guard x y,
      Then m <= y                          by guard x y
           bop b m y
         = 0                               by bop_0, m <= y
         = loop2_count guard modify f x y  by loop2_count_0, guard x y
   If ~guard x y,
      Then ~(m <= y)                       by ~guard x y
           bop b m y
         = SUC (bop b m (y + b))                     by bop_suc
         = SUC (bop b m (modify x))                  by notation
         = SUC (loop2_count guard modify f (f x) (modify y))
                                                     by induction hypothesis, 0 < b
         = loop2_count guard modify f x y            by loop_count_suc, ~guard x y
*)
val bop_eq_loop2_count = store_thm(
  "bop_eq_loop2_count",
  ``!b f m x y. 0 < b ==> (bop b m y = loop2_count (\x y. m <= y) (\y. y + b) f x y)``,
  ntac 5 strip_tac >>
  qid_spec_tac `x` >>
  qid_spec_tac `y` >>
  qid_spec_tac `m` >>
  qid_spec_tac `b` >>
  ho_match_mp_tac (theorem "bop_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x y. m <= y` >>
  qabbrev_tac `modify = \y. b + y` >>
  qabbrev_tac `R = measure (\(x,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`modify`, Abbr`R`] >>
  Cases_on `guard x y` >| [
    `m <= y` by metis_tac[] >>
    metis_tac[bop_0, loop2_count_0],
    `~(m <= y)` by metis_tac[] >>
    `bop b m y = SUC (bop b m (b + y))` by rw[bop_suc] >>
    `_ = SUC (loop2_count guard modify f (f x) (b + y))` by metis_tac[NOT_ZERO] >>
    `_ = loop2_count guard modify f x y` by metis_tac[loop2_count_suc] >>
    decide_tac
  ]);

(* Theorem: RISING (\x. x + b) *)
(* Proof:
   By RISING, this is to show: !x. x <= x + b, which is true.
*)
val increase_rising = store_thm(
  "increase_rising",
  ``!b. RISING (\x. x + b)``,
  simp[]);

(* Theorem: FUNPOW (\x. x + b) n x = x + n * b *)
(* Proof:
   Let f = (\x. x + b).
   By induction on n.
   Base: !x. FUNPOW f 0 x = x + 0 * b
         FUNPOW f 0 x
       = x                 by FUNPOW_0
       = x + 0 * b         by arithmetic
   Step: !x. FUNPOW f n x = x + n * b ==>
         !x. FUNPOW f (SUC n) x = x + SUC n * b
         FUNPOW f (SUC n) x
       = f (FUNPOW f n x)   by FUNPOW_SUC
       = f (x + n * b)      by induction hypothesis
       = (x + n * b) + b    by function application
       = x + (SUC n) * b    by arithmetic, ADD1
*)
val iterating_inc_eqn = store_thm(
  "iterating_inc_eqn",
  ``!b n x. FUNPOW (\x. x + b) n x = x + n * b``,
  strip_tac >>
  Induct >-
  rw[] >>
  rw[FUNPOW_SUC, ADD1]);

(* Theorem: 0 < b ==> (m <= FUNPOW (\x. x + b) (bop b m x) x) *)
(* Proof:
   Let guard = (\x. m <= x),
       modify = (\x. x + b),
       R = measure (\x. m - x).
   Then WF R                                   by WF_measure
    and !x. ~guard x ==> R (modify x) x        by m - (x + b) < m - x, 0 < b
   Note bop b m x = loop_count guard modify x  by bop_eq_loop_count
    and guard (FUNPOW modify (loop_count guard modify x) x)   by loop_count_iterating
     or m <= FUNPOW modify (loop_count guard modify x) x      by guard
*)
val iterating_inc_bop = store_thm(
  "iterating_inc_bop",
  ``!b m x. 0 < b ==> m <= FUNPOW (\x. x + b) (bop b m x) x``,
  rw[bop_eq_loop_count] >>
  qabbrev_tac `guard = \x. m <= x` >>
  qabbrev_tac `modify = \x. b + x` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`modify`, Abbr`R`] >>
  metis_tac[loop_count_iterating]);

(* Theorem: 0 < b ==> m <= x + (bop b m x) * b *)
(* Proof:
   Note m <= FUNPOW (\x. x + b) (bop b m x) x  by iterating_inc_bop
     or            m <= x + (bop b m x) * b    by iterating_dec_eqn
*)
val iterating_inc_bop_alt = store_thm(
  "iterating_inc_bop_alt",
  ``!b m x. 0 < b ==> m <= x + (bop b m x) * b``,
  metis_tac[iterating_inc_bop, iterating_inc_eqn]);

(* This is the same as bop_exceeds: |- !b n. 0 < b ==> m <= x + b * bop b m x *)

(* ------------------------------------------------------------------------- *)
(* Increase Loop                                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\
       (!x. loop x = if m <= x then quit x else body x + loop (x + b)) ==>
        !x. loop x = quit (x + (bop b m x) * b) + SUM (GENLIST (\j. body (x + j * b)) (bop b m x)) *)
(* Proof:
   Let guard = (\x. m <= x),
       modify = (\x. x + b),
       R = measure (\x. m - x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by m - (x + b) < m - x, 0 < b
   Also !x. loop x = if guard x then quit x else body x + loop (modify x)
                                          by given
   Let f = (\j. body (FUNPOW modify j x)).
       z = FUNPOW modify (bop b m x) x.
   Then f = (\j. body (x + j * b))        by iterating_inc_eqn, FUN_EQ_THM
    abd z = x + (bop b m x) * b           by iterating_inc_eqn
   Thus loop x
      = quit z + SUM (GENLIST f (loop_count guard modify x))       by loop_modify_count_eqn
      = quit (x + (bop b m x) * b) + SUM (GENLIST f (bop b m x))   by bop_eq_loop_count
*)
val loop_inc_count_eqn = store_thm(
  "loop_inc_count_eqn",
  ``!loop body quit b m. 0 < b /\
       (!x. loop x = if m <= x then quit x else body x + loop (x + b)) ==>
        !x. loop x = quit (x + (bop b m x) * b) + SUM (GENLIST (\j. body (x + j * b)) (bop b m x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. m <= x` >>
  qabbrev_tac `modify = \x. x + b` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x. loop x = if guard x then quit x else body x + loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_eqn >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  `loop_count guard modify x = bop b m x` by rw[bop_eq_loop_count, Abbr`guard`, Abbr`modify`] >>
  qabbrev_tac `n = bop b m x` >>
  `FUNPOW modify (loop_count guard modify x) x = x + n * b` by rw[iterating_inc_eqn, Abbr`modify`] >>
  qabbrev_tac `f1 = \j. body (FUNPOW modify j x)` >>
  qabbrev_tac `f2 = \j. body (x + j * b)` >>
  `f1 = f2` by rw[FUN_EQ_THM, iterating_inc_eqn, Abbr`modify`, Abbr`f1`, Abbr`f2`] >>
  metis_tac[]);

(* Theorem: 0 < b /\
       (!x. loop x = if m <= x then quit x else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + SUM (GENLIST (\j. body (x + j * b)) (bop b m x)) *)
(* Proof:
   Let guard = (\x. m <= x),
       modify = (\x. x + b),
       R = measure (\x. m - x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by m - (x + b) < m - x, 0 < b
   Also !x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)
                                          by given
   Let f = (\j. body (FUNPOW modify j x)),
       z = FUNPOW modify (bop b m x) x.
   Then f = (\j. body (x + j * b))        by iterating_inc_eqn, FUN_EQ_THM
    abd z = x + (bop b m x) * b           by iterating_inc_eqn
   Thus  loop x
      <= quit z + SUM (GENLIST f (loop_count guard modify x))  by loop_modify_count_exit_le
       = quit z + SUM (GENLIST f (bop b m x))                  by bop_eq_loop_count
*)
val loop_inc_count_exit_sum_le = store_thm(
  "loop_inc_count_exit_sum_le",
  ``!loop body quit exit b m. 0 < b /\
       (!x. loop x = if m <= x then quit x else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + SUM (GENLIST (\j. body (x + j * b)) (bop b m x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. m <= x` >>
  qabbrev_tac `modify = \x. x + b` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  `loop_count guard modify x = bop b m x` by rw[bop_eq_loop_count, Abbr`guard`, Abbr`modify`] >>
  qabbrev_tac `n = bop b m x` >>
  `FUNPOW modify (loop_count guard modify x) x = x + n * b` by rw[iterating_inc_eqn, Abbr`modify`] >>
  qabbrev_tac `f1 = \j. body (FUNPOW modify j x)` >>
  qabbrev_tac `f2 = \j. body (x + j * b)` >>
  `f1 = f2` by rw[FUN_EQ_THM, iterating_inc_eqn, Abbr`modify`, Abbr`f1`, Abbr`f2`] >>
  metis_tac[]);

(* Theorem: 0 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if m <= x then quit x else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + (bop b m x) * cover (x + (bop b m x) * b) *)
(* Proof:
   Let guard = (\x. m <= x),
       modify = (\x. x + b),
       R = measure (\x. m - x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by m - (x + b) < m - x, 0 < b
    and RISING modify                     by increase_rising
   Also !x. loop x = if guard x then quit x else body x + loop (modify x)
                                          by given
   Let n = loop_count guard modify x,
       z = FUNPOW modify n x.
   Then n = bop b m x                     by bop_eq_loop_count
    abd z = x + n * b                     by iterating_inc_eqn
       loop x
    <= q z + n * cover z                  by loop_rise_count_cover_exit_le, MONO cover
     = q (x + n * b) + bop b m x * cover (x + n * b)
*)
val loop_inc_count_cover_exit_le = store_thm(
  "loop_inc_count_cover_exit_le",
  ``!loop body quit cover exit b m. 0 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if m <= x then quit x else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + (bop b m x) * cover (x + (bop b m x) * b)``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. m <= x` >>
  qabbrev_tac `modify = \x. x + b` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `RISING modify` by rw[increase_rising, Abbr`modify`] >>
  `!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_rise_count_cover_exit_le >>
  first_x_assum (qspecl_then [`x`, `cover`] strip_assume_tac) >>
  qabbrev_tac `n = loop_count guard modify x` >>
  `loop x <= quit (FUNPOW modify n x) + n * cover (FUNPOW modify n x)` by metis_tac[] >>
  `n = bop b m x` by rw[bop_eq_loop_count, Abbr`guard`, Abbr`modify`] >>
  `FUNPOW modify n x = x + n * b` by rw[iterating_inc_eqn, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: Equivalent form of loop_inc_count_cover_exit_le *)
(* Proof: by loop_inc_count_cover_exit_le *)
val loop_inc_count_cover_exit_le_alt = store_thm(
  "loop_inc_count_cover_exit_le_alt",
  ``!loop body quit cover exit b m. 0 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if m <= x then quit x else body x + if exit x then 0 else loop (x + b)) ==>
        !x. let n = bop b m x in
            loop x <= quit (x + n * b) + n * cover (x + n * b)``,
  metis_tac[loop_inc_count_cover_exit_le]);

(* Other similar theorems -- directly *)

(* Theorem: 0 < b /\ MONO body /\
       (!x. loop x = if m <= x then quit x else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + (bop b m x) * body (x + (bop b m x) * b) *)
(* Proof: by loop_inc_count_cover_exit_le with cover = body. *)
val loop_inc_count_exit_le = store_thm(
  "loop_inc_count_exit_le",
  ``!loop body quit exit b m. 0 < b /\ MONO body /\
       (!x. loop x = if m <= x then quit x else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + (bop b m x) * body (x + (bop b m x) * b)``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_inc_count_cover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem: 0 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if m <= x then quit x else body x + loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + (bop b m x) * cover (x + (bop b m x) * b) *)
(* Proof: by loop_inc_count_cover_exit_le with exit = F. *)
val loop_inc_count_cover_le = store_thm(
  "loop_inc_count_cover_le",
  ``!loop body quit cover b m. 0 < b /\ (!x. body x <= cover x) /\ MONO cover /\
       (!x. loop x = if m <= x then quit x else body x + loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + (bop b m x) * cover (x + (bop b m x) * b)``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num. F` >>
  `!x. loop x = if m <= x then quit x else body x + if exit x then 0 else loop (x + b)` by metis_tac[] >>
  imp_res_tac loop_inc_count_cover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem: 0 < b /\ MONO body /\
       (!x. loop x = if m <= x then quit x else body x + loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + (bop b m x) * body (x + (bop b m x) * b) *)
(* Proof: by loop_inc_count_cover_le with cover = body. *)
val loop_inc_count_le = store_thm(
  "loop_inc_count_le",
  ``!loop body quit b m. 0 < b /\ MONO body /\
       (!x. loop x = if m <= x then quit x else body x + loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + (bop b m x) * body (x + (bop b m x) * b)``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_inc_count_cover_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if m <= x then quit x else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + bop b m x * cover x *)
(* Proof:
   Let guard = (\x. m <= x),
       modify = (\x. x + b),
       R = measure (\x. m - x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by m - (x + b) < m - x, 0 < b
    and RISING modify                     by increase_rising
   Also !x. loop x = if guard x then quit x else body x + loop (modify x)
                                          by given
   Let n = loop_count guard modify x.
       z = FUNPOW modify n x.
   Then n = bop b m x                     by bop_eq_loop_count
    abd z = x + n * b                     by iterating_inc_eqn
       loop x
    <= q z + n * cover x                  by loop_rise_count_rcover_exit_le, RMONO cover
     = q (x + n * b) + bop b m x * cover x
*)
val loop_inc_count_rcover_exit_le = store_thm(
  "loop_inc_count_rcover_exit_le",
  ``!loop body quit cover exit b m. 0 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if m <= x then quit x else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + bop b m x * cover x``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. m <= x` >>
  qabbrev_tac `modify = \x. x + b` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `RISING modify` by rw[increase_rising, Abbr`modify`] >>
  `!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_rise_count_rcover_exit_le >>
  first_x_assum (qspecl_then [`x`, `cover`] strip_assume_tac) >>
  qabbrev_tac `n = loop_count guard modify x` >>
  `loop x <= quit (FUNPOW modify n x) + n * cover x` by metis_tac[] >>
  `n = bop b m x` by rw[bop_eq_loop_count, Abbr`guard`, Abbr`modify`] >>
  `FUNPOW modify n x = x + n * b` by rw[iterating_inc_eqn, Abbr`modify`] >>
  metis_tac[]);

(* Other similar theorems -- directly *)

(* Theorem: 0 < b /\ RMONO body /\
       (!x. loop x = if m <= x then quit x else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + bop b m x * body x *)
(* Proof: by loop_inc_count_rcover_exit_le with cover = body. *)
val loop_inc_count_rbody_exit_le = store_thm(
  "loop_inc_count_rbody_exit_le",
  ``!loop body quit exit b m. 0 < b /\ RMONO body /\
       (!x. loop x = if m <= x then quit x else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + bop b m x * body x``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_inc_count_rcover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem: 0 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if m <= x then quit x else body x + loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + bop b m x * cover x *)
(* Proof: by loop_inc_count_rcover_exit_le with exit = F. *)
val loop_inc_count_rcover_le = store_thm(
  "loop_inc_count_rcover_le",
  ``!loop body quit cover b m. 0 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if m <= x then quit x else body x + loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + bop b m x * cover x``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num. F` >>
  `!x. loop x = if m <= x then quit x else body x + if exit x then 0 else loop (x + b)` by metis_tac[] >>
  imp_res_tac loop_inc_count_rcover_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem: 0 < b /\ RMONO body /\
       (!x. loop x = if m <= x then quit x else body x + loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + bop b m x * body x *)
(* Proof: by loop_inc_count_rcover_le with cover = body. *)
val loop_inc_count_rbody_le = store_thm(
  "loop_inc_count_rbody_le",
  ``!loop body quit b m. 0 < b /\ RMONO body /\
       (!x. loop x = if m <= x then quit x else body x + loop (x + b)) ==>
        !x. loop x <= quit (x + (bop b m x) * b) + bop b m x * body x``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_inc_count_rcover_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Increase Loop with Transform                                              *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\
    (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
     !x y. loop x y = quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                      SUM (GENLIST (\j. body (FUNPOW f j x) (y + j * b)) (bop b m y)) *)
(* Proof:
   Let guard = (\x y. m <= y),
       modify = (\y. y + b),
       R = measure (\(x,y). m - y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by m - (x + b) < m - x, 0 < b
    and !x y. loop x y = if guard x y then quit x y else body x y + loop (f x) (modify y)   by given
   Let g = \j. body (FUNPOW f j x) (FUNPOW modify j y),
       n = loop2_count guard modify f x y,
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = bop m y                              by bop_eq_loop2_count
    and g = \j. body (FUNPOW f j x) (y + j * b)  by iterating_inc_eqn
    and q = y + n * b                            by iterating_inc_eqn
        loop x y
      = quit p q + SUM (GENLIST g n)             by loop2_modify_count_eqn
      = quit p q + SUM (GENLIST g (bop b m y))   by bop_eq_loop2_count
      = quit (FUNPOW f n x) (y + n * b) + SUM (GENLIST (\j. body (FUNPOW f j x) (y + j * b)) n)
*)
val loop2_inc_count_eqn = store_thm(
  "loop2_inc_count_eqn",
  ``!loop f body quit b m. 0 < b /\
    (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
     !x y. loop x y = quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                      SUM (GENLIST (\j. body (FUNPOW f j x) (y + j * b)) (bop b m y))``,
  rpt strip_tac >>
  imp_res_tac bop_eq_loop2_count >>
  first_x_assum (qspecl_then [`y`, `x`, `m`, `f`] strip_assume_tac) >>
  qabbrev_tac `guard = \x y. m <= y` >>
  qabbrev_tac `modify = \y. y + b` >>
  qabbrev_tac `R = measure (\(x,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x y. loop x y = if guard x y then quit x y else body x y + loop (f x) (modify y)` by metis_tac[] >>
  imp_res_tac loop2_modify_count_eqn >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = loop2_count guard modify f x y` >>
  `FUNPOW modify n y = y + n * b` by rw[iterating_inc_eqn, Abbr`modify`] >>
  qabbrev_tac `u = \j. body (FUNPOW f j x) (FUNPOW modify j y)` >>
  qabbrev_tac `v = \j. body (FUNPOW f j x) (y + j * b)` >>
  `u = v` by rw[FUN_EQ_THM, iterating_inc_eqn, Abbr`modify`, Abbr`u`, Abbr`v`] >>
  metis_tac[]);

(* Theorem: 0 < b /\
    (!x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                       SUM (GENLIST (\j. body (FUNPOW f j x) (y + j * b)) (bop b m y)) *)
(* Proof:
   Let guard = (\x y. m <= y),
       modify = (\y. y + b),
       R = measure (\(x,y). m - y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by m - (x + b) < m - x, 0 < b
    and !x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (f x) (modify y)
                             by given
   Let g = \j. body (FUNPOW f j x) (FUNPOW modify j y),
       n = loop2_count guard modify f x y,
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = bop m y                              by bop_eq_loop2_count
    and g = \j. body (FUNPOW f j x) (y + j * b)  by iterating_inc_eqn
    and q = y + n * b                            by iterating_inc_eqn
        loop x y
     <= quit p q + SUM (GENLIST g n)             by loop2_modify_count_exit_le
      = quit p q + SUM (GENLIST g (bop b m y))   by bop_eq_loop2_count
      = quit (FUNPOW f n x) (y + n * b) + SUM (GENLIST (\j. body (FUNPOW f j x) (y + j * b)) n)
*)
val loop2_inc_count_sum_le = store_thm(
  "loop2_inc_count_sum_le",
  ``!loop f body quit exit b m. 0 < b /\
    (!x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                       SUM (GENLIST (\j. body (FUNPOW f j x) (y + j * b)) (bop b m y))``,
  rpt strip_tac >>
  imp_res_tac bop_eq_loop2_count >>
  first_x_assum (qspecl_then [`y`, `x`, `m`, `f`] strip_assume_tac) >>
  qabbrev_tac `guard = \x y. m <= y` >>
  qabbrev_tac `modify = \y. y + b` >>
  qabbrev_tac `R = measure (\(x,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  imp_res_tac loop2_modify_count_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = loop2_count guard modify f x y` >>
  `FUNPOW modify n y = y + n * b` by rw[iterating_inc_eqn, Abbr`modify`] >>
  qabbrev_tac `u = \j. body (FUNPOW f j x) (FUNPOW modify j y)` >>
  qabbrev_tac `v = \j. body (FUNPOW f j x) (y + j * b)` >>
  `u = v` by rw[FUN_EQ_THM, iterating_inc_eqn, Abbr`modify`, Abbr`u`, Abbr`v`] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Increasing Loop with Transform-independent Body                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                       (bop b m y) * g (y + (bop b m y) * b) *)
(* Proof:
   Let n = bop b m y, z = FUNPOW f n x.
      loop x y
   <= quit z (y + n * b) +
      SUM (GENLIST (\j. body (FUNPOW f j x) (y + j * b)) n)     by loop2_inc_count_sum_le
   <= quit z (y + n * b) +
      SUM (GENLIST (\j. cover (FUNPOW f j x) (y + j * b)) n)    by SUM_LE, body cover
    = quit z (y + n * b) + SUM (GENLIST (\j. g (y + j * b)) n)  by expanding cover
   <= quit z (y + n * b) + SUM (GENLIST (K (g (y + n * b))) n)  by SUM_LE, MONO g
    = quit z (y + n * b) + g (y + n * b) * n                    by SUM_GENLIST_K
    = quit z (y + n * b) + n * g (y + n * b)                    by MULT_COMM
*)
val loop2_inc_count_mono_cover_exit_le = store_thm(
  "loop2_inc_count_mono_cover_exit_le",
  ``!loop f body quit cover exit b m g. 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                       (bop b m y) * g (y + (bop b m y) * b)``,
  rpt strip_tac >>
  imp_res_tac loop2_inc_count_sum_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = bop b m y` >>
  `SUM (GENLIST (\j. body (FUNPOW f j x) (y + j * b)) n) <=
    SUM (GENLIST (\j. cover (FUNPOW f j x) (y + j * b)) n)` by fs[SUM_LE] >>
  `SUM (GENLIST (\j. cover (FUNPOW f j x) (y + j * b)) n) <= SUM (GENLIST (K (g (y + n * b))) n)` by rw[SUM_LE] >>
  `SUM (GENLIST (K (g (y + n * b))) n) = g (y + n * b) * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Other similar theorems -- directly *)

(* Theorem: 0 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                       (bop b m y) * g (y + (bop b m y) * b) *)
(* Proof: by loop2_inc_count_mono_cover_exit_le with cover = body. *)
val loop2_inc_count_mono_exit_le = store_thm(
  "loop2_inc_count_mono_exit_le",
  ``!loop f body quit exit b m g. 0 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                       (bop b m y) * g (y + (bop b m y) * b)``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_inc_count_mono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                       (bop b m y) * g (y + (bop b m y) * b) *)
(* Proof: by loop2_inc_count_mono_cover_exit_le with exit = F. *)
val loop2_inc_count_mono_cover_le = store_thm(
  "loop2_inc_count_mono_cover_le",
  ``!loop f body quit cover b m g. 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                       (bop b m y) * g (y + (bop b m y) * b)``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:'a y:num. F` >>
  `!x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)` by metis_tac[] >>
  imp_res_tac loop2_inc_count_mono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                       (bop b m y) * g (y + (bop b m y) * b) *)
(* Proof: by loop2_inc_count_mono_cover_le with cover = body. *)
val loop2_inc_count_mono_le = store_thm(
  "loop2_inc_count_mono_le",
  ``!loop f body quit b m g. 0 < b /\ (body = \x y. g y) /\ MONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                       (bop b m y) * g (y + (bop b m y) * b)``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_inc_count_mono_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) + (bop b m y) * g 0 *)
(* Proof:
   Let n = bop b m y, z = FUNPOW f n x.
      loop x y
   <= quit z (y + n * b) +
      SUM (GENLIST (\j. body (FUNPOW f j x) (y + j * b)) n)     by loop2_inc_count_sum_le
   <= quit z (y + n * b) +
      SUM (GENLIST (\j. cover (FUNPOW f j x) (y + j * b)) n)    by SUM_LE, body cover
    = quit z (y + n * b) + SUM (GENLIST (\j. g (y + j * b)) n)  by expanding cover
   <= quit z (y + n * b) + SUM (GENLIST (K (g 0)) n)            by SUM_LE, RMONO g
    = quit z (y + n * b) + g 0 * n                              by SUM_GENLIST_K
    = quit z (y + n * b) + n * g 0                              by MULT_COMM
*)
val loop2_inc_count_rmono_cover_exit_le = store_thm(
  "loop2_inc_count_rmono_cover_exit_le",
  ``!loop f body quit cover exit b m g. 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) + (bop b m y) * g 0``,
  rpt strip_tac >>
  imp_res_tac loop2_inc_count_sum_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = bop b m y` >>
  `SUM (GENLIST (\j. body (FUNPOW f j x) (y + j * b)) n) <=
    SUM (GENLIST (\j. cover (FUNPOW f j x) (y + j * b)) n)` by fs[SUM_LE] >>
  `SUM (GENLIST (\j. cover (FUNPOW f j x) (y + j * b)) n) <= SUM (GENLIST (K (g 0)) n)` by rw[SUM_LE] >>
  `SUM (GENLIST (K (g 0)) n) = g 0 * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Other similar theorems -- directly *)

(* Theorem: 0 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) + (bop b m y) * g 0 *)
(* Proof: by loop2_inc_count_rmono_cover_exit_le with cover = body. *)
val loop2_inc_count_rmono_exit_le = store_thm(
  "loop2_inc_count_rmono_exit_le",
  ``!loop f body quit exit b m g. 0 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) + (bop b m y) * g 0``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_inc_count_rmono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) + (bop b m y) * g 0 *)
(* Proof: by loop2_inc_count_rmono_cover_exit_le with cover = body. *)
val loop2_inc_count_rmono_cover_le = store_thm(
  "loop2_inc_count_rmono_cover_le",
  ``!loop f body quit cover b m g. 0 < b /\
    (!x y. body x y <= cover x y) /\ (cover = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) + (bop b m y) * g 0``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:'a y:num. F` >>
  `!x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)` by metis_tac[] >>
  imp_res_tac loop2_inc_count_rmono_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) + (bop b m y) * g 0 *)
(* Proof: by loop2_inc_count_rmono_cover_le with cover = body. *)
val loop2_inc_count_rmono_le = store_thm(
  "loop2_inc_count_rmono_le",
  ``!loop f body quit b m g. 0 < b /\ (body = \x y. g y) /\ RMONO g /\
    (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
     !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) + (bop b m y) * g 0``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_inc_count_rmono_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Increasing Loop with Numeric Transform                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y =
                 if m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * cover (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) *)
(* Proof:
   Let guard = (\x y. m <= y),
       modify = (\y. y + b),
       R = measure (\(x,y). m - y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by m - (x + b) < m - x, 0 < b
    and !x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (f x) (modify y)
                             by given
    and RISING modify        by increase_rising
   Let g = \j. body (FUNPOW f j x) (FUNPOW modify j y),
       n = loop2_count guard modify f x y,
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = bop m y                              by bop_eq_loop2_count
    and g = \j. body (FUNPOW f j x) (y + j * b)  by iterating_inc_eqn
    and q = y + n * b                            by iterating_inc_eqn
        loop x y
     <= quit p q + n * cover (FUNPOW f n x) (FUNPOW modify n y))  by loop2_rise_rise_count_cover_exit_le
      = quit p q + n * cover (FUNPOW f n x) (y + n * b)           by iterating_inc_eqn
      = quit (FUNPOW f n x) (y + n * b) + n * cover (FUNPOW f n x) (y + n * b)
*)
val loop2_inc_rise_count_cover_exit_le = store_thm(
  "loop2_inc_rise_count_cover_exit_le",
  ``!loop f body quit cover exit b m.
          0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y =
                 if m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * cover (FUNPOW f (bop b m y) x) (y + (bop b m y) * b)``,
  rpt strip_tac >>
  assume_tac (bop_eq_loop2_count |> ISPEC ``b:num`` |> ISPEC ``f:num -> num``) >>
  first_x_assum (qspecl_then [`m`, `x`, `y`] strip_assume_tac) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qabbrev_tac `guard = \x:num y. m <= y` >>
  qabbrev_tac `modify = \y. y + b` >>
  qabbrev_tac `R = measure (\(x:num,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  `RISING modify` by rw[increase_rising, Abbr`modify`] >>
  assume_tac loop2_rise_rise_count_cover_exit_le >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`x`, `y`, `cover`] strip_assume_tac) >>
  `!n. FUNPOW modify n y = y + b * n` by rw[iterating_inc_eqn, Abbr`modify`] >>
  qabbrev_tac `foo1 = !x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)` >>
  qabbrev_tac `foo2 = !x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (f x) (modify y)` >>
  fs[]);

(* Other similar theorems -- directly *)

(* Theorem: 0 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y =
                 if m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * body (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) *)
(* Proof: by loop2_inc_rise_count_cover_exit_le with cover = body. *)
val loop2_inc_rise_count_exit_le = store_thm(
  "loop2_inc_rise_count_exit_le",
  ``!loop f body quit exit b m. 0 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y =
                 if m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * body (FUNPOW f (bop b m y) x) (y + (bop b m y) * b)``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_inc_rise_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * cover (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) *)
(* Proof: by loop2_inc_rise_count_cover_exit_le with exit = F. *)
val loop2_inc_rise_count_cover_le = store_thm(
  "loop2_inc_rise_count_cover_le",
  ``!loop f body quit cover b m.
          0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ RISING f /\
          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * cover (FUNPOW f (bop b m y) x) (y + (bop b m y) * b)``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  `!x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)` by metis_tac[] >>
  imp_res_tac loop2_inc_rise_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * body (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) *)
(* Proof: by loop2_inc_rise_count_cover_le with cover = body. *)
val loop2_inc_rise_count_le = store_thm(
  "loop2_inc_rise_count_le",
  ``!loop f body quit b m. 0 < b /\ MONO2 body /\ RISING f /\
          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * body (FUNPOW f (bop b m y) x) (y + (bop b m y) * b)``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_inc_rise_count_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y =
                 if m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * cover x (y + (bop b m y) * b) *)
(* Proof:
   Let guard = (\x y. m <= y),
       modify = (\y. y + b),
       R = measure (\(x,y). m - y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by m - (x + b) < m - x, 0 < b
    and !x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (f x) (modify y)
                             by given
    and RISING modify        by increase_rising
   Let g = \j. body (FUNPOW f j x) (FUNPOW modify j y),
       n = loop2_count guard modify f x y,
       p = FUNPOW f n x,
       q = FUNPOW modify n y.
   Note n = bop m y                              by bop_eq_loop2_count
    and g = \j. body (FUNPOW f j x) (y + j * b)  by iterating_inc_eqn
    and q = y + n * b                            by iterating_inc_eqn
        loop x y
     <= quit p q + n * cover x (FUNPOW modify n y))  by loop2_fall_rise_count_cover_exit_le
      = quit p q + n * cover x (y + n * b)           by iterating_inc_eqn
      = quit (FUNPOW f n x) (y + n * b) + n * cover x (y + n * b)
*)
val loop2_inc_fall_count_cover_exit_le = store_thm(
  "loop2_inc_fall_count_cover_exit_le",
  ``!loop f body quit cover exit b m.
          0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y =
                 if m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * cover x (y + (bop b m y) * b)``,
  rpt strip_tac >>
  assume_tac (bop_eq_loop2_count |> ISPEC ``b:num`` |> ISPEC ``f:num -> num``) >>
  first_x_assum (qspecl_then [`m`, `x`, `y`] strip_assume_tac) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qabbrev_tac `guard = \x:num y. m <= y` >>
  qabbrev_tac `modify = \y. y + b` >>
  qabbrev_tac `R = measure (\(x:num,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  `RISING modify` by rw[increase_rising, Abbr`modify`] >>
  imp_res_tac loop2_fall_rise_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`, `cover`] strip_assume_tac) >>
  `!n. FUNPOW modify n y = y + n * b` by rw[iterating_inc_eqn, Abbr`modify`] >>
  qabbrev_tac `foo1 = !x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)` >>
  qabbrev_tac `foo2 = !x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (f x) (modify y)` >>
  fs[]);

(* Other similar theorems -- directly *)

(* Theorem: 0 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y =
                 if m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * body x (y + (bop b m y) * b) *)
(* Proof: by loop2_inc_fall_count_cover_exit_le with cover = body. *)
val loop2_inc_fall_count_exit_le = store_thm(
  "loop2_inc_fall_count_exit_le",
  ``!loop f body quit exit b m. 0 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y =
                 if m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * body x (y + (bop b m y) * b)``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_inc_fall_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * cover x (y + (bop b m y) * b) *)
(* Proof: by loop2_inc_fall_count_cover_exit_le with exit = F. *)
val loop2_inc_fall_count_cover_le = store_thm(
  "loop2_inc_fall_count_cover_le",
  ``!loop f body quit cover b m.
          0 < b /\ (!x y. body x y <= cover x y) /\ MONO2 cover /\ FALLING f /\
          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * cover x (y + (bop b m y) * b)``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  `!x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)` by metis_tac[] >>
  imp_res_tac loop2_inc_fall_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * body x (y + (bop b m y) * b) *)
(* Proof: by loop2_inc_fall_count_cover_le with cover = body *)
val loop2_inc_fall_count_le = store_thm(
  "loop2_inc_fall_count_le",
  ``!loop f body quit b m. 0 < b /\ MONO2 body /\ FALLING f /\
          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * body x (y + (bop b m y) * b)``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_inc_fall_count_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Increasing Loop with Transform cover                                      *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\
          (!x y. RMONO (cover x) /\ MONO (combin$C cover y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * cover (FUNPOW g (bop b m y) x) y *)
(* Proof:
   Let n = bop b m y,
       f1 = (\j. body (FUNPOW f j x) (y + b * j)),
       f2 = K (cover (FUNPOW g n x) y).

   Claim: SUM (GENLIST f1 n) <= SUM (GENLIST f2 n)
   Proof: By SUM_LE, LENGTH_MAP, EL_MAP,
          this is to show: k < n ==>
            body (FUNPOW f k x) (y + b * k) <= cover (FUNPOW g n x) y
          Note y <= y + b * k                         by arithmetic
           Now FUNPOW f k x <= FUNPOW g k x           by FUNPOW_LE_MONO, MONO g
           and FUNPOW g k x <= FUNPOW g n x           by FUNPOW_LE_RISING, k < n, RISING g
          Thus body (FUNPOW f k x) (y DIV b ** k)
            <= cover (FUNPOW f k x) (y DIV b ** k)    by body and cover property
            <= cover (FUNPOW f k x) y                 by RMONO (cover x), for fix x.
            <= cover (FUNPOW g n x) y                 by MONO (combin$C cover y), for fix y.

   Let p = FUNPOW f n x, q = y + n * b.
        loop x y
     <= quit p q + SUM (GENLIST f1 n)                               by loop2_inc_count_sum_le
     <= quit p q + SUM (GENLIST f2 n)                               by claim
      = quit p q + SUM (GENLIST (K cover (FUNPOW g n x) y) n)       by notation
      = quit p q + n * cover (FUNPOW g n x)                         by SUM_GENLIST_K
      = quit p q + (bop b m y) * cover (FUNPOW g (bop b m y) x) y   by notation
*)
val loop2_inc_mono_count_cover_exit_le = store_thm(
  "loop2_inc_mono_count_cover_exit_le",
  ``!loop f g body quit cover exit b m.
          0 < b /\ (!x y. body x y <= cover x y) /\
          (!x y. RMONO (cover x) /\ MONO (combin$C cover y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * cover (FUNPOW g (bop b m y) x) y``,
  rpt strip_tac >>
  imp_res_tac loop2_inc_count_sum_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = bop b m y` >>
  qabbrev_tac `f1 = \j. body (FUNPOW f j x) (y + j * b)` >>
  qabbrev_tac `f2:num -> num = K (cover (FUNPOW g n x) y)` >>
  `SUM (GENLIST f1 n) <= SUM (GENLIST f2 n)` by
  (irule SUM_LE >>
  rw[Abbr`f1`, Abbr`f2`] >>
  `y <= y + b * k` by rw[] >>
  `FUNPOW f k x <= FUNPOW g k x` by rw[FUNPOW_LE_MONO] >>
  `FUNPOW g k x <= FUNPOW g n x` by rw[FUNPOW_LE_RISING] >>
  `FUNPOW f k x <= FUNPOW g n x` by decide_tac >>
  `body (FUNPOW f k x) (y + b * k) <= cover (FUNPOW f k x) (y + b * k)` by rw[] >>
  `cover (FUNPOW f k x) (y + b * k) <= cover (FUNPOW f k x) y` by rw[] >>
  `cover (FUNPOW f k x) y <= cover (FUNPOW g n x) y` by metis_tac[combinTheory.C_THM] >>
  decide_tac) >>
  `SUM (GENLIST f2 n) = n * cover (FUNPOW g n x) y` by rw[SUM_GENLIST_K, Abbr`f2`] >>
  decide_tac);

(* Other similar theorems -- directly *)

(* Theorem: 0 < b /\
          (!x y. RMONO (body x) /\ MONO (combin$C body y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * body (FUNPOW g (bop b m y) x) y *)
(* Proof: by loop2_inc_mono_count_cover_exit_le with cover = body. *)
val loop2_inc_mono_count_exit_le = store_thm(
  "loop2_inc_mono_count_exit_le",
  ``!loop f g body quit exit b m. 0 < b /\
          (!x y. RMONO (body x) /\ MONO (combin$C body y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y =
                 if m <= y then quit x y
                 else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * body (FUNPOW g (bop b m y) x) y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_inc_mono_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\
          (!x y. RMONO (cover x) /\ MONO (combin$C cover y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * cover (FUNPOW g (bop b m y) x) y *)
(* Proof: by loop2_inc_mono_count_cover_exit_le with exit = F. *)
val loop2_inc_mono_count_cover_le = store_thm(
  "loop2_inc_mono_count_cover_le",
  ``!loop f g body quit cover b m.
          0 < b /\ (!x y. body x y <= cover x y) /\
          (!x y. RMONO (cover x) /\ MONO (combin$C cover y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * cover (FUNPOW g (bop b m y) x) y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  `!x y. loop x y = if m <= y then quit x y else body x y + if exit x y then 0 else loop (f x) (y + b)` by metis_tac[] >>
  imp_res_tac loop2_inc_mono_count_cover_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: 0 < b /\
          (!x y. RMONO (body x) /\ MONO (combin$C body y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * body (FUNPOW g (bop b m y) x) y *)
(* Proof: by loop2_inc_mono_count_cover_le with cover = body *)
val loop2_inc_mono_count_le = store_thm(
  "loop2_inc_mono_count_le",
  ``!loop f g body quit b m. 0 < b /\
          (!x y. RMONO (body x) /\ MONO (combin$C body y)) /\
          (!x. f x <= g x) /\ MONO g /\ RISING g /\
          (!x y. loop x y = if m <= y then quit x y else body x y + loop (f x) (y + b)) ==>
           !x y. loop x y <= quit (FUNPOW f (bop b m y) x) (y + (bop b m y) * b) +
                             bop b m y * body (FUNPOW g (bop b m y) x) y``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_inc_mono_count_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* Original investigation, some with quit = constant.                        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Increasing List.                                                          *)
(* ------------------------------------------------------------------------- *)

(* Given a number x, generate a increasing list of x + b, up to some maximum m. *)
Definition increase_by_def:
  increase_by b m x =
  if (b = 0) \/ (m <= x) then [] else x::increase_by b m (x + b)
Termination WF_REL_TAC ‘measure (λ(b,m,x). m - x)’
End


(* Overload increase_by 1 *)
val _ = overload_on ("increasing", ``increase_by 1``);

(*
EVAL ``increasing 10 1``; = [1; 2; 3; 4; 5; 6; 7; 8; 9]: thm
*)

(* Theorem: b = 0 \/ m <= x ==> (increase_by b m x = []) *)
(* Proof: by increase_by_def *)
val increase_by_nil = store_thm(
  "increase_by_nil",
  ``!b m x. b = 0 \/ m <= x ==> (increase_by b m x = [])``,
  rw[Once increase_by_def]);

(* Theorem: 0 < b /\ x < m ==> (increase_by b m x = x :: increase_by b m (x + b)) *)
(* Proof: by increase_by_def *)
val increase_by_cons = store_thm(
  "increase_by_cons",
  ``!b m x. 0 < b /\ x < m ==> (increase_by b m x = x :: increase_by b m (x + b))``,
  rw[Once increase_by_def]);

(*
EVAL ``increase_by 3 10 1``; = [1; 4; 7]: thm
EVAL ``GENLIST (\j. 1 + 3 * j) (bop 3 10 1)``; = [1; 4; 7]: thm
*)

(* Theorem: increase_by b m x = GENLIST (\j. x + j * b) (bop b m x) *)
(* Proof:
   Let f = (\j. b + (x + b * j)), g = (\j. x + b * j).
   Note f = g o SUC                   by FUN_EQ_THM
    and g 0 = x + 0 = x               by arithmetic
   By induction from increase_by_def.
   If b = 0 \/ m <= x,
        increase_by b m n
      = []                            by increase_by_nil
      = GENLIST g 0                   by GENLIST_0
      = GENLIST (bop b m x)           by bop_0
   Otherwise, b <> 0 /\ ~(m <= x).
       ~(b = 0 \/ m <= x) /\ increase_by b m (b + x) = GENLIST f (bop b m (b + x)) ==>
       increase_by b m x = GENLIST g (bop b m x)

         increase_by b m x
       = x::increase_by b m (b + x)                  by increase_by_cons
       = x::GENLIST f (bop b m (b + x))              by induction hypothesis
       = g 0 :: GENLIST (g o SUC) (bop b m (b + x))  by f = g o SUC, x = g 0
       = GENLIST g (SUC (bop b m (b + x))            by GENLIST_CONS
       = GENLIST g (hop b m x)                       by bop_suc
*)
val increase_by_eqn = store_thm(
  "increase_by_eqn",
  ``!b m x. increase_by b m x = GENLIST (\j. x + j * b) (bop b m x)``,
  ho_match_mp_tac (theorem "increase_by_ind") >>
  rw[] >>
  Cases_on `(b = 0) \/ (m <= x)` >-
  metis_tac[bop_0, increase_by_nil, GENLIST_0] >>
  `b <> 0 /\ ~(m <= x)` by decide_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  rw[Once increase_by_def] >>
  qabbrev_tac `f = \j. b + (x + b * j)` >>
  qabbrev_tac `g = \j. x + b * j` >>
  `f = g o SUC` by rw[FUN_EQ_THM, ADD1, Abbr`f`, Abbr`g`] >>
  `x::GENLIST f (bop b m (b + x)) = g 0 :: GENLIST (g o SUC) (bop b m (x + b))` by rw[Abbr`g`] >>
  `_ = GENLIST g (SUC (bop b m (x + b)))` by rw[GENLIST_CONS] >>
  `_ = GENLIST g (bop b m x)` by metis_tac[bop_def] >>
  rw[]);

(* Theorem: 0 < b /\ x + j * b < m ==> MEM (x + j * b) (increase_by b m x) *)
(* Proof:
       MEM (x + j * b) (increase_by b m x)
   <=> MEM (x + j * b) (GENLIST (\j. x + j * b) (bop b m x))   by increase_by_eqn
   <=> ?k. k < bop b m x /\ x + j * b = x + k * b              by MEM_GENLIST
   <=> take k = j, with k < bop b m x                          by bop_property
*)
val increase_by_member = store_thm(
  "increase_by_member",
  ``!b m x j. 0 < b /\ x + j * b < m ==> MEM (x + j * b) (increase_by b m x)``,
  rw[increase_by_eqn] >>
  rw[MEM_GENLIST] >>
  metis_tac[bop_property]);

(* Theorem: j < bop b m x ==> (EL j (increase_by b m x) = x + j * b) *)
(* Proof:
   Let f = (\j. x + j * b).
     EL j (increase_by b m x)
   = EL j (GENLIST f (bop b m x))   by increase_by_eqn
   = f j                            by EL_GENLIST, j < bop b n
   = x + j * b                      by notation
*)
val increase_by_element = store_thm(
  "increase_by_element",
  ``!b m x j. j < bop b m x ==> (EL j (increase_by b m x) = x + j * b)``,
  rw[increase_by_eqn]);

(* Theorem: LENGTH (increase_by b m x) = bop b m x *)
(* Proof:
     LENGTH (increase_by b m x)
   = LENGTH (GENLIST (\j. x + j * b) (bop b m x))      by increase_by_eqn
   = bop b m x                                         by LENGTH_GENLIST
*)
val increase_by_length = store_thm(
  "increase_by_length",
  ``!b m x. LENGTH (increase_by b m x) = bop b m x``,
  rw[increase_by_eqn]);

(* Theorem: LENGTH (increasing m c) = m - c *)
(* Proof:
     LENGTH (increasing m c)
   = LENGTH (increase_by 1 m c)   by notation
   = bop 1 m c                    by increase_by_length
   = m - c                        by bop_1_m_c
*)
val increasing_length = store_thm(
  "increasing_length",
  ``!m c. LENGTH (increasing m c) = m - c``,
  rw[increase_by_length, bop_1_m_c]);

(* Theorem: increasing m c = [c ..< m] *)
(* Proof:
      increasing m c
    = GENLIST (\j. c + j * 1) (bop 1 m c)   by increase_by_eqn
    = GENLIST (\j. c + j) (m - c)           by bop_1_m_c
    = [c ..< m]                             by listRangeLHI_def
*)
val increasing_eqn = store_thm(
  "increasing_eqn",
  ``!m c. increasing m c = [c ..< m]``,
  rw[increase_by_eqn, bop_1_m_c, listRangeLHI_def]);

(* Theorem: 0 < b ==> (increase_by b m x = loop_arg (\x. m <= x) (\x. x + b) x) *)
(* Proof:
   By induction from increase_by_def.
   Let guard = (\x. m <= x),
       modify = (\x. x + b),
       R = measure (\x. m - x).
   Then WF R                               by WF_measure
    and !x. ~guard x ==> R (modify x) x    by m - (x + b) < m - x, 0 < b
   If guard x
           increase_by b m x
         = []                              by increase_by_nil, m <= x
         = loop_arg guard modify x         by loop_arg_nil, guard x
   If ~guard x
           increase_by b m x
         = x :: increase_by b m (x + b)             by increase_by_cons, ~(m <= x)
         = x :: increase_by b m (modify x)          by notation
         = x :: loop_arg guard modify (modify x)    by induction hypothesis
         = loop_arg guard modify x                  by loop_arg_cons, ~guard x
*)
val increase_by_eq_loop_arg = store_thm(
  "increase_by_eq_loop_arg",
  ``!b m x. 0 < b ==> (increase_by b m x = loop_arg (\x. m <= x) (\x. x + b) x)``,
  ho_match_mp_tac (theorem "increase_by_ind") >>
  rpt strip_tac >>
  qabbrev_tac `guard = \x. m <= x` >>
  qabbrev_tac `modify = \x. x + b` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by fs[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  Cases_on `guard x` >-
  metis_tac[increase_by_nil, loop_arg_nil] >>
  qabbrev_tac `t = loop_arg guard modify (modify x)` >>
  `increase_by b m x = x :: t` by metis_tac[increase_by_cons, NOT_ZERO, NOT_LESS] >>
  `t = increase_by b m (modify x)` by metis_tac[NOT_ZERO] >>
  `loop_arg guard modify x = x::t` by metis_tac[loop_arg_cons] >>
  metis_tac[]);

(* Theorem: 0 < b ==> (MAP2 body (iterating f x (bop b m y)) (increase_by b m y) =
                       MAP (UNCURRY body) (loop2_arg (\y. m <= y) (\y. y + b) f x y)) *)
(* Proof:
   By induction from increase_by_def.
   Let guard = (\x y. m <= y),
       modify = (\y. y + b),
       R = measure (\(x,y). m - y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by m - (x + b) < m - x, 0 < b

   If guard x y,
      Then m <= y                               by notation
      LHS = MAP2 body (iterating f x (bop b m 0)) (increase_by b m 0)
          = MAP2 body (iterating f x 0) []      by bop_0, increase_by_nil
          = MAP2 body [] []                     by iterating_nil
          = []                                  by MAP2
      RHS = MAP (UNCURRY body) (loop2_arg guard modify f x y)
          = MAP (UNCURRY body) []               by loop2_arg_nil, guard x y
          = [] = LHS                            by MAP

   If ~guard x y,
     Then ~(m <= y), or y < m                   by notation
            MAP2 body (iterating f x (bop b m y)) (increase_by b m y)
          = MAP2 body (iterating f x (SUC (bop b m (y + b)))) (y::increase_by b m (y + b))
                                                by bop_suc, increase_by_cons
          = MAP2 body (x::iterating f (f x) (bop b (y + b))) (y::increase_by b m (y + b))
                                                by iterating_cons
          = body x y::MAP2 body (iterating f (f x) (bop b m (y + b))) (increase_by b m (y + b))
                                                by MAP2
          = body x y::MAP (UNCURRY body) (loop2_arg guard modify f (f x) (y + b))
                                                by induction hypothesis
          = MAP (UNCURRY body) ((x,y):: loop2_arg guard modify f (f x) (y + b))
                                                by MAP, UNCURRY
          = MAP (UNCURRY body) (loop2_arg guard modify f x y)
                                                by loop2_arg_cons
*)
val iterating_increase_eq_loop2_arg = store_thm(
  "iterating_increase_eq_loop2_arg",
  ``!b m body f x y. 0 < b ==>
    (MAP2 body (iterating f x (bop b m y)) (increase_by b m y) =
     MAP (UNCURRY body) (loop2_arg (\x y. m <= y) (\y. y + b) f x y))``,
  ntac 6 strip_tac >>
  qid_spec_tac `x` >>
  qid_spec_tac `y` >>
  qid_spec_tac `m` >>
  qid_spec_tac `b` >>
  ho_match_mp_tac (theorem "increase_by_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x y. m <= y` >>
  qabbrev_tac `modify = \y. b + y` >>
  qabbrev_tac `R = measure (\(x,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  Cases_on `guard x y` >| [
    `m <= y` by metis_tac[] >>
    rw[iterating_nil, bop_0, increase_by_nil] >>
    metis_tac[loop2_arg_nil],
    `~(m <= y)` by metis_tac[] >>
    rw[iterating_cons, bop_suc, increase_by_cons] >>
    `body x y:: MAP2 body (iterating f (f x) (bop b m (modify y))) (increase_by b m (modify y)) =
    body x y:: MAP2 body (iterating f (f x) (bop b m (b + y))) (increase_by b m (b + y))` by rw[Abbr`modify`] >>
    `_ = body x y::MAP (UNCURRY body) (loop2_arg guard modify f (f x) (b + y))` by metis_tac[NOT_ZERO] >>
    `_ = MAP (UNCURRY body) ((x,y)::loop2_arg guard modify f (f x) (modify y))` by rw[Abbr`modify`] >>
    metis_tac[loop2_arg_cons]
  ]);

(* ------------------------------------------------------------------------- *)
(* Increase Loop -- original                                                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\
          (!x. loop x = if m <= x then c else body x + loop (x + b)) ==>
           !x. loop x = c + SUM (MAP body (increase_by b m x)) *)
(* Proof:
   Let guard = (\x. m <= x),
       modify = (\x. x + b),
       R = measure (\x. m - x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by m - (x + b) < m - x, 0 < b
   Also !x. loop x = if guard x then c else body x + loop (modify x)
                                          by given
   Thus loop x
      = c + SUM (MAP body (loop_arg guard modify x))  by loop_modify_count_by_sum
      = c + SUM (MAP body (increase_by b m x))        by increase_by_eq_loop_arg
*)
val loop_inc_count_by_sum = store_thm(
  "loop_inc_count_by_sum",
  ``!loop body b c m. 0 < b /\ (!x. loop x = if m <= x then c else body x + loop (x + b)) ==>
        !x. loop x = c + SUM (MAP body (increase_by b m x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. m <= x` >>
  qabbrev_tac `modify = \x. x + b` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x. loop x = if guard x then c else body x + loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_by_sum >>
  `loop_arg guard modify x = increase_by b m x` by rw[increase_by_eq_loop_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 0 < b /\
       (!x. loop x = if m <= x then c else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= c + SUM (MAP body (increase_by b m x)) *)
(* Proof:
   Let guard = (\x. m <= x),
       modify = (\x. x + b),
       R = measure (\x. m - x),
   Then WF R                              by WF_measure
    and !x. ~guard x ==> R (modify x) x   by m - (x + b) < m - x, 0 < b
   Also !x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)
                                          by given
   Thus loop x
     <= c + SUM (MAP body (loop_arg guard modify x))  by loop_modify_count_exit_by_sum
      = c + SUM (MAP body (increase_by b m x))        by increase_by_eq_loop_arg
*)
val loop_inc_count_exit_by_sum = store_thm(
  "loop_inc_count_exit_by_sum",
  ``!loop body exit b c m. 0 < b /\
       (!x. loop x = if m <= x then c else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= c + SUM (MAP body (increase_by b m x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. m <= x` >>
  qabbrev_tac `modify = \x. x + b` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_exit_by_sum >>
  `loop_arg guard modify x = increase_by b m x` by rw[increase_by_eq_loop_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 0 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if m <= x then c else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= c + cover x * bop b m x *)
(* Proof:
   Let guard = (\x. m <= x),
       modify = (\x. x + b),
       R = measure (\x. m - x).
   Then WF R                 by WF_measure
    and !x. ~guard x ==> R (modify x) x       by m - (x + b) < m - x, 0 < b
    and !x y. R x y ==> cover x <= cover y    by R, reverse order of RMONO cover, LESS_IMP_LESS_OR_EQ
    and !x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)
                                                     by given
        loop x
     <= c + cover x * loop_count guard modify x      by loop_modify_count_cover_exit_upper
      = c + cover x * bop b m x                      by bop_eq_loop_count
*)
val loop_inc_count_cover_exit_upper = store_thm(
  "loop_inc_count_cover_exit_upper",
  ``!loop body cover exit b m c. 0 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if m <= x then c else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= c + cover x * bop b m x``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. m <= x` >>
  qabbrev_tac `modify = \x. x + b` >>
  qabbrev_tac `R = measure (\x. m - x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (modify x) x` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x y. R x y ==> cover x <= cover y` by rw[Abbr`R`] >>
  `!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
  assume_tac (loop_modify_count_cover_exit_upper |> ISPEC ``loop:num -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `cover`, `exit`, `modify`, `R`] strip_assume_tac) >>
  `loop_count guard modify x = bop b m x` by rw[bop_eq_loop_count, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 0 < b /\ RMONO body /\
       (!x. loop x = if m <= x then c else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= c + body x * bop b m x *)
(* Proof: by loop_inc_count_cover_exit_upper, with cover = body. *)
val loop_inc_count_exit_upper = store_thm(
  "loop_inc_count_exit_upper",
  ``!loop body exit b m c. 0 < b /\ RMONO body /\
       (!x. loop x = if m <= x then c else body x + if exit x then 0 else loop (x + b)) ==>
        !x. loop x <= c + body x * bop b m x``,
  metis_tac[loop_inc_count_cover_exit_upper, LESS_EQ_REFL]);

(* Theorem: 0 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if m <= x then c else body x + loop (x + b)) ==>
        !x. loop x <= c + cover x * bop b m x *)
(* Proof: by loop_inc_count_cover_exit_upper, with exit = F. *)
val loop_inc_count_cover_upper = store_thm(
  "loop_inc_count_cover_upper",
  ``!loop body cover b m c. 0 < b /\ (!x. body x <= cover x) /\ RMONO cover /\
       (!x. loop x = if m <= x then c else body x + loop (x + b)) ==>
        !x. loop x <= c + cover x * bop b m x``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num. F` >>
  metis_tac[loop_inc_count_cover_exit_upper]);

(* Theorem: 0 < b /\ RMONO body /\
       (!x. loop x = if m <= x then c else body x + loop (x + b)) ==>
        !x. loop x <= c + body x * bop b m x *)
(* Proof: loop_inc_count_cover_upper, with body = cover. *)
val loop_inc_count_upper = store_thm(
  "loop_inc_count_upper",
  ``!loop body b m c. 0 < b /\ RMONO body /\
       (!x. loop x = if m <= x then c else body x + loop (x + b)) ==>
        !x. loop x <= c + body x * bop b m x``,
  metis_tac[loop_inc_count_cover_upper, LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)
(* Increase Loop with Transform -- original                                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 0 < b /\
    (!x y. loop x y = if m <= y then c else body x y + loop (f x) (y + b)) ==>
     !x y. loop x y = c + SUM (MAP2 body (iterating f x (bop b m y)) (increase_by b m y)) *)
(* Proof:
   Let guard = (\x y. m <= y),
       modify = (\y. y + b),
       R = measure (\(x,y). m - y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by m - (x + b) < m - x, 0 < b
    and !x y. loop x y = if guard x y then c else body x y + loop (f x) (modify y)   by given
        loop x y
      = c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))           by loop2_modify_count_by_sum
      = c + SUM (MAP2 body (iterating f x (bop b m y)) (increase_by b m y))   by iterating_increase_eq_loop2_arg
*)
val loop2_inc_count_by_sum = store_thm(
  "loop2_inc_count_by_sum",
  ``!loop f body b m c. 0 < b /\
    (!x y. loop x y = if m <= y then c else body x y + loop (f x) (y + b)) ==>
     !x y. loop x y = c + SUM (MAP2 body (iterating f x (bop b m y)) (increase_by b m y))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. m <= y` >>
  qabbrev_tac `modify = \y. y + b` >>
  qabbrev_tac `R = measure (\(x,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x y. loop x y = if guard x y then c else body x y + loop (f x) (modify y)` by metis_tac[] >>
  assume_tac (loop2_modify_count_by_sum |> ISPEC ``loop:'a -> num -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `modify`, `f`, `R`] strip_assume_tac) >>
  `loop x y = c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))` by metis_tac[] >>
  `MAP (UNCURRY body) (loop2_arg guard modify f x y) =
    MAP2 body (iterating f x (bop b m y)) (increase_by b m y)` by rw[iterating_increase_eq_loop2_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 0 < b /\
    (!x y. loop x y = if m <= y then c else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
     !x y. loop x y <= c + SUM (MAP2 body (iterating f x (bop b m y)) (increase_by b m y)) *)
(* Proof:
   Let guard = (\x y. m <= y),
       modify = (\y. y + b),
       R = measure (\(x,y). m - y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)     by m - (x + b) < m - x, 0 < b
    and !x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                        by given
        loop x y
     <= c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))          by loop2_modify_count_exit_by_sum
      = c + SUM (MAP2 body (iterating f x (bop b m y)) (increase_by b m y))  by iterating_increase_eq_loop2_arg
*)
val loop2_inc_count_exit_by_sum = store_thm(
  "loop2_inc_count_exit_by_sum",
  ``!loop f body b m c exit. 0 < b /\
    (!x y. loop x y = if m <= y then c else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
     !x y. loop x y <= c + SUM (MAP2 body (iterating f x (bop b m y)) (increase_by b m y))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. m <= y` >>
  qabbrev_tac `modify = \y. y + b` >>
  qabbrev_tac `R = measure (\(x,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  assume_tac (loop2_modify_count_exit_by_sum |> ISPEC ``loop:'a -> num -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `exit`, `modify`, `f`, `R`] strip_assume_tac) >>
  `loop x y <= c + SUM (MAP (UNCURRY body) (loop2_arg guard modify f x y))` by metis_tac[] >>
  `MAP (UNCURRY body) (loop2_arg guard modify f x y) =
    MAP2 body (iterating f x (bop b m y)) (increase_by b m y)` by rw[iterating_increase_eq_loop2_arg, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x2 y2 <= cover x1 y1) /\
       (!x y. loop x y = if m <= y then c else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
        !x y. loop x y <= c + cover x y * bop b m y *)
(* Proof:
   Let guard = (\x y. m <= y),
       modify = (\y. y + b),
       R = measure (\(x,y). m - y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,modify y) (x,y)    by m - (x + b) < m - x, 0 < b
    and !x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> cover x1 y1 <= cover x2 y2    by R, reverse order
    and !x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)
                                                     by given
        loop x y
     <= c + cover x y * loop2_count guard modify f x y       by loop2_modify_count_bcover_exit_upper
      = c + cover x y * bop b m y                            by bop_eq_loop2_count
*)
val loop2_inc_count_cover_exit_upper = store_thm(
  "loop2_inc_count_cover_exit_upper",
  ``!loop f body cover exit b m c. 0 < b /\
       (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x2 y2 <= cover x1 y1) /\
       (!x y. loop x y = if m <= y then c else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
        !x y. loop x y <= c + cover x y * bop b m y``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. m <= y` >>
  qabbrev_tac `modify = \y. y + b` >>
  qabbrev_tac `R = measure (\(x,y). m - y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,modify y) (x,y)` by rw[Abbr`guard`, Abbr`R`, Abbr`modify`] >>
  `!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> cover x1 y1 <= cover x2 y2` by rw[Abbr`R`] >>
  `!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (modify y)` by metis_tac[] >>
  assume_tac (loop2_modify_count_bcover_exit_upper |> ISPEC ``loop:'a -> num -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `exit`, `cover`, `modify`, `f`, `R`] strip_assume_tac) >>
  `loop2_count guard modify f x y = bop b m y` by rw[bop_eq_loop2_count, Abbr`guard`, Abbr`modify`] >>
  metis_tac[]);

(* Theorem: 0 < b /\ (!x1 x2 y1 y2. y1 <= y2 ==> body x2 y2 <= body x1 y1) /\
       (!x y. loop x y = if m <= y then c else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
        !x y. loop x y <= c + body x y * bop b m y *)
(* Proof: by loop2_inc_count_cover_exit_upper, with cover = body. *)
val loop2_inc_count_exit_upper = store_thm(
  "loop2_inc_count_exit_upper",
  ``!loop f body exit b m c. 0 < b /\
       (!x1 x2 y1 y2. y1 <= y2 ==> body x2 y2 <= body x1 y1) /\
       (!x y. loop x y = if m <= y then c else body x y + if exit x y then 0 else loop (f x) (y + b)) ==>
        !x y. loop x y <= c + body x y * bop b m y``,
  rpt strip_tac >>
  assume_tac loop2_inc_count_cover_exit_upper >>
  last_x_assum (qspecl_then [`loop`, `f`, `body`, `body`, `exit`, `b`, `m`,`c`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* Theorem: 0 < b /\ (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x2 y2 <= cover x1 y1) /\
       (!x y. loop x y = if m <= y then c else body x y + loop (f x) (y + b)) ==>
        !x y. loop x y <= c + cover x y * bop b m y *)
(* Proof: by loop2_inc_count_cover_exit_upper, with exit = F. *)
val loop2_inc_count_cover_upper = store_thm(
  "loop2_inc_count_cover_upper",
  ``!loop f body cover b m c. 0 < b /\ (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. y1 <= y2 ==> cover x2 y2 <= cover x1 y1) /\
       (!x y. loop x y = if m <= y then c else body x y + loop (f x) (y + b)) ==>
        !x y. loop x y <= c + cover x y * bop b m y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:'a y:num. F` >>
  assume_tac loop2_inc_count_cover_exit_upper >>
  last_x_assum (qspecl_then [`loop`, `f`, `body`, `cover`, `exit`, `b`, `m`, `c`] strip_assume_tac) >>
  metis_tac[]);

(* Theorem: 0 < b /\ (!x1 x2 y1 y2. y1 <= y2 ==> body x2 y2 <= body x1 y1) /\
    (!x y. loop x y = if m <= y then c else body x y + loop (f x) (y + b)) ==>
     !x y. loop x y <= c + body x y * bop b m y *)
(* Proof: loop2_inc_count_cover_upper, with body = cover. *)
val loop2_inc_count_upper = store_thm(
  "loop2_inc_count_upper",
  ``!loop f body b m c. 0 < b /\ (!x1 x2 y1 y2. y1 <= y2 ==> body x2 y2 <= body x1 y1) /\
    (!x y. loop x y = if m <= y then c else body x y + loop (f x) (y + b)) ==>
     !x y. loop x y <= c + body x y * bop b m y``,
  rpt strip_tac >>
  assume_tac loop2_inc_count_cover_upper >>
  last_x_assum (qspecl_then [`loop`, `f`, `body`, `body`, `b`, `m`, `c`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
