(* ------------------------------------------------------------------------- *)
(* Loop Recurrence Theory                                                    *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "loop";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open arithmeticTheory listTheory rich_listTheory listRangeTheory numberTheory
     combinatoricsTheory;

val _ = temp_overload_on ("RISING", ``\f. !x:num. x <= f x``);
val _ = temp_overload_on ("FALLING", ``\f. !x:num. f x <= x``);

(* ------------------------------------------------------------------------- *)
(* Loop Recurrence Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Type and Overload:
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   Loop Count for recurrence:
   loop_count_def      |- !modify guard R. WF R ==> (!x. ~guard x ==> R (modify x) x) ==>
                          !x. loop_count guard modify x =
                              if guard x then 0 else SUC (loop_count guard modify (modify x))
   loop_count_thm      |- !modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                          !x. loop_count guard modify x =
                              if guard x then 0 else SUC (loop_count guard modify (modify x))
   loop_count_0        |- !modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                          !x. guard x ==> loop_count guard modify x = 0
   loop_count_suc      |- !modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                          !x. ~guard x ==> loop_count guard modify x = SUC (loop_count guard modify (modify x))
   loop_count_iterating|- !modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                          !x. guard (FUNPOW modify (loop_count guard modify x) x)
   loop_count_exists   |- !modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                          !x. ?n. guard (FUNPOW modify n x)
   loop_count_minimal  |- !modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                          !x n. guard (FUNPOW modify n x) /\
                                (!m. m < n ==> ~guard (FUNPOW modify m x)) ==>
                                loop_count guard modify x = n
   loop_count_eqn      |- !modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                          !x. loop_count guard modify x = LEAST n. guard (FUNPOW modify n x)

   General Theory of Recurrence with 1 argument:
   loop_modify_count_eqn
                       |- !loop guard body quit modify R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\
                          (!x. loop x = if guard x then quit x else body x + loop (modify x)) ==>
                           !x. loop x = quit (FUNPOW modify (loop_count guard modify x) x) +
                               SUM (GENLIST (\j. body (FUNPOW modify j x)) (loop_count guard modify x))
   loop_modify_count_eqn_1
                       |- !loop guard body quit modify R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\
                          (!x. loop x = if guard x then quit x else body x + loop (modify x)) ==>
                           !x. (let n = loop_count guard modify x
                                 in loop x = quit (FUNPOW modify n x) +
                                             SUM (GENLIST (\j. body (FUNPOW modify j x)) n))
   loop_modify_count_eqn_2
                       |- !loop guard body quit modify R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\
                          (!x. loop x = if guard x then quit x else body x + loop (modify x)) ==>
                           !x. (let n = loop_count guard modify x
                                 in loop x = quit (FUNPOW modify n x) +
                                             SIGMA (\j. body (FUNPOW modify j x)) (count n))
   loop_modify_count_exit_le
                       |- !loop guard body quit exit modify R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\
                          (!x. loop x =
                               if guard x then quit x
                               else body x + if exit x then 0 else loop (modify x)) ==>
                           !x. loop x <= quit (FUNPOW modify (loop_count guard modify x) x) +
                               SUM (GENLIST (\j. body (FUNPOW modify j x)) (loop_count guard modify x))
   loop_rise_count_cover_exit_le
                       |- !loop guard body quit exit modify R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
                          (!x. loop x =
                               if guard x then quit x
                               else body x + if exit x then 0 else loop (modify x)) ==>
                           !x cover. (let n = loop_count guard modify x
                                       in (!x. body x <= cover x) /\ MONO cover ==>
                               loop x <= quit (FUNPOW modify n x) + n * cover (FUNPOW modify n x))
   loop_rise_count_rcover_exit_le
                       |- !loop guard body quit exit modify R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
                          (!x. loop x =
                               if guard x then quit x
                               else body x + if exit x then 0 else loop (modify x)) ==>
                           !x cover. (let n = loop_count guard modify x
                                       in (!x. body x <= cover x) /\ RMONO cover ==>
                               loop x <= quit (FUNPOW modify n x) + n * cover x)
   loop_fall_count_cover_exit_le
                       |- !loop guard body quit exit modify R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
                          (!x. loop x =
                               if guard x then quit x
                               else body x + if exit x then 0 else loop (modify x)) ==>
                           !x cover. (let n = loop_count guard modify x
                                       in (!x. body x <= cover x) /\ MONO cover ==>
                               loop x <= quit (FUNPOW modify n x) + n * cover x)
   loop_fall_count_rcover_exit_le
                       |- !loop guard body quit exit modify R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
                          (!x. loop x =
                               if guard x then quit x
                               else body x + if exit x then 0 else loop (modify x)) ==>
                           !x cover. (let n = loop_count guard modify x
                                       in (!x. body x <= cover x) /\ RMONO cover ==>
                               loop x <= quit (FUNPOW modify n x) + n * cover (FUNPOW modify n x))

   General Theory of Recurrence with 2 arguments:
   loop2_count_def     |- !guard modify transform x y. loop2_count guard modify transform x y =
                           loop_count (\(x,y). guard x y) (\(x,y). (transform x,modify y)) (x,y)
   loop2_count_thm     |- !transform modify guard R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
                           !x y. loop2_count guard modify transform x y =
                                 if guard x y then 0
                                 else SUC (loop2_count guard modify transform (transform x) (modify y))
   loop2_count_0       |- !transform modify guard R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
                           !x y. guard x y ==> loop2_count guard modify transform x y = 0
   loop2_count_suc     |- !transform modify guard R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
                           !x y. ~guard x y ==> loop2_count guard modify transform x y =
                                 SUC (loop2_count guard modify transform (transform x) (modify y))
   loop2_count_iterating
                       |- !transform modify guard R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
                           !x y. guard (FUNPOW transform (loop2_count guard modify transform x y) x)
                                       (FUNPOW modify (loop2_count guard modify transform x y) y)
   loop2_modify_count_eqn
                       |- !loop guard body quit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                          (!x y. loop x y =
                                 if guard x y then quit x y
                                 else body x y + loop (transform x) (modify y)) ==>
                           !x y. loop x y =
                                 quit (FUNPOW transform (loop2_count guard modify transform x y) x)
                                      (FUNPOW modify (loop2_count guard modify transform x y) y) +
                                 SUM (GENLIST (\j. body (FUNPOW transform j x) (FUNPOW modify j y))
                                              (loop2_count guard modify transform x y))
   loop2_modify_count_exit_le
                       |- !loop guard body quit exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                          (!x y. loop x y =
                                 if guard x y then quit x y
                                 else body x y +
                                      if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y. loop x y <=
                                 quit (FUNPOW transform (loop2_count guard modify transform x y) x)
                                      (FUNPOW modify (loop2_count guard modify transform x y) y) +
                                 SUM (GENLIST (\j. body (FUNPOW transform j x) (FUNPOW modify j y))
                                              (loop2_count guard modify transform x y))

   List for Transform argument:
   iterating_def       |- !y x f. iterating f x y =
                                  if y = 0 then [] else x::iterating f (f x) (y - 1)
   iterating_nil       |- !f x. iterating f x 0 = []
   iterating_cons      |- !f x y. iterating f x (SUC y) = x::iterating f (f x) y
   iterating_alt       |- (!f x. iterating f x 0 = []) /\
                           !f x y. iterating f x (SUC y) = x::iterating f (f x) y
   iterating_eqn       |- !f x y. iterating f x y = MAP (combin$C (FUNPOW f) x) [0 ..< y]
   iterating_length    |- !f x y. LENGTH (iterating f x y) = y
   iterating_member    |- !f x y j. j < y ==> MEM (FUNPOW f j x) (iterating f x y)
   iterating_element   |- !f x y j. j < y ==> EL j (iterating f x y) = FUNPOW f j x

   Numeric Loops with transform and modify:
   loop2_rise_fall_count_cover_exit_le
                       |- !loop guard body quit exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                          RISING transform /\ FALLING modify /\
                          (!x y. loop x y =
                                 if guard x y then quit x y
                                 else body x y +
                                      if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y cover. (let n = loop2_count guard modify transform x y
                                         in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                                loop x y <= quit (FUNPOW transform n x) (FUNPOW modify n y) +
                                            n * cover (FUNPOW transform n x) y)
   loop2_fall_fall_count_cover_exit_le
                       |- !loop guard body quit exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                          FALLING transform /\ FALLING modify /\
                          (!x y. loop x y =
                                 if guard x y then quit x y
                                 else body x y +
                                      if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y cover. (let n = loop2_count guard modify transform x y
                                         in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                                loop x y <= quit (FUNPOW transform n x) (FUNPOW modify n y) +
                                            n * cover x y)
   loop2_fall_rise_count_cover_exit_le
                       |- !loop guard body quit exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                          FALLING transform /\ RISING modify /\
                          (!x y. loop x y =
                                 if guard x y then quit x y
                                 else body x y +
                                      if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y cover. (let n = loop2_count guard modify transform x y
                                         in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                                loop x y <= quit (FUNPOW transform n x) (FUNPOW modify n y) +
                                            n * cover x (FUNPOW modify n y))
   loop2_rise_rise_count_cover_exit_le
                       |- !loop guard body quit exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                          RISING transform /\ RISING modify /\
                          (!x y. loop x y =
                                 if guard x y then quit x y
                                 else body x y +
                                      if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y cover. (let n = loop2_count guard modify transform x y
                                         in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                                loop x y <= quit (FUNPOW transform n x) (FUNPOW modify n y) +
                                            n * cover (FUNPOW transform n x) (FUNPOW modify n y))

   General Theory of Recurrence with 3 arguments:
   loop3_count_def     |- !guard modify transform convert x y z.
                           loop3_count guard modify transform convert x y z =
                           loop_count (\(x,y,z). guard x y z)
                                      (\(x,y,z). (convert x,transform y,modify z)) (x,y,z)
   loop3_count_thm     |- !convert transform modify guard R. WF R /\
                          (!x y z. ~guard x y z ==> R (convert x,transform y,modify z) (x,y,z)) ==>
                           !x y z. loop3_count guard modify transform convert x y z =
                                   if guard x y z then 0
                                   else SUC (loop3_count guard modify transform convert
                                                   (convert x) (transform y) (modify z))
   loop3_count_0       |- !convert transform modify guard R. WF R /\
                          (!x y z. ~guard x y z ==> R (convert x,transform y,modify z) (x,y,z)) ==>
                           !x y z. guard x y z ==>
                                   loop3_count guard modify transform convert x y z = 0
   loop3_count_suc     |- !convert transform modify guard R. WF R /\
                          (!x y z. ~guard x y z ==> R (convert x,transform y,modify z) (x,y,z)) ==>
                           !x y z. ~guard x y z ==>
                                   loop3_count guard modify transform convert x y z =
                                   SUC (loop3_count guard modify transform convert
                                             (convert x) (transform y) (modify z))
   loop3_count_iterating
                       |- !convert transform modify guard R. WF R /\
                          (!x y z. ~guard x y z ==> R (convert x,transform y,modify z) (x,y,z)) ==>
                           !x y z. guard
                              (FUNPOW convert (loop3_count guard modify transform convert x y z) x)
                              (FUNPOW transform (loop3_count guard modify transform convert x y z) y)
                              (FUNPOW modify (loop3_count guard modify transform convert x y z) z)
   loop3_modify_count_eqn
                       |- !loop guard body quit modify transform convert R. WF R /\
                          (!x y z. ~guard x y z ==> R (convert x,transform y,modify z) (x,y,z)) /\
                          (!x y z. loop x y z =
                                   if guard x y z then quit x y z
                                   else body x y z + loop (convert x) (transform y) (modify z)) ==>
                           !x y z. loop x y z =
                                   quit (FUNPOW convert (loop3_count guard modify transform convert x y z) x)
                                        (FUNPOW transform (loop3_count guard modify transform convert x y z) y)
                                        (FUNPOW modify (loop3_count guard modify transform convert x y z) z) +
                                   SUM (GENLIST (\j. body (FUNPOW convert j x)
                                                          (FUNPOW transform j y)
                                                          (FUNPOW modify j z))
                                       (loop3_count guard modify transform convert x y z))
   loop3_modify_count_exit_le
                       |- !loop guard body quit exit modify transform convert R. WF R /\
                          (!x y z. ~guard x y z ==> R (convert x,transform y,modify z) (x,y,z)) /\
                          (!x y z. loop x y z =
                                   if guard x y z then quit x y z
                                   else body x y z + if exit x y z then 0
                                   else loop (convert x) (transform y) (modify z)) ==>
                           !x y z. loop x y z <=
                                   quit (FUNPOW convert (loop3_count guard modify transform convert x y z) x)
                                        (FUNPOW transform (loop3_count guard modify transform convert x y z) y)
                                        (FUNPOW modify (loop3_count guard modify transform convert x y z) z) +
                                   SUM (GENLIST (\j. body (FUNPOW convert j x)
                                                          (FUNPOW transform j y)
                                                          (FUNPOW modify j z))
                                        (loop3_count guard modify transform convert x y z))

   Original:
   loop_arg_def        |- !modify guard R. WF R ==> (!x. ~guard x ==> R (modify x) x) ==>
                          !x. loop_arg guard modify x =
                              if guard x then [] else x::loop_arg guard modify (modify x)
   loop_arg_thm        |- !modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                          !x. loop_arg guard modify x =
                              if guard x then [] else x::loop_arg guard modify (modify x)
   loop_arg_nil        |- !modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                          !x. guard x ==> loop_arg guard modify x = []
   loop_arg_cons       |- !modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                          !x. ~guard x ==> loop_arg guard modify x = x::loop_arg guard modify (modify x)
   loop_arg_length     |- !modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                          !x. LENGTH (loop_arg guard modify x) = loop_count guard modify x
   loop_arg_eqn        |- !modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                          !x. loop_arg guard modify x =
                              GENLIST (\j. FUNPOW modify j x) (loop_count guard modify x)
   loop_arg_element    |- !modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                          !x k. k < loop_count guard modify x ==>
                                EL k (loop_arg guard modify x) = FUNPOW modify k x
   loop_arg_cover_sum  |- !modify guard R cover. WF R /\ (!x. ~guard x ==> R (modify x) x) /\
                          (!x y. R x y ==> cover x <= cover y) ==>
                           !x. SUM (MAP cover (loop_arg guard modify x)) <=
                               SUM (MAP (K (cover x)) (loop_arg guard modify x))
   loop_modify_count_by_sum
                       |- !loop guard body c modify R.
                           WF R /\ (!x. ~guard x ==> R (modify x) x) /\
                           (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
                            !x. loop x = c + SUM (MAP body (loop_arg guard modify x))
   loop_modify_count_exit_by_sum
                       |- !loop guard body c exit modify R.
                           WF R /\ (!x. ~guard x ==> R (modify x) x) /\
                           (!x. loop x =
                                if guard x then c
                                else body x + if exit x then 0 else loop (modify x)) ==>
                            !x. loop x <= c + SUM (MAP body (loop_arg guard modify x))
   loop_modify_count_quitc_eqn
                       |- !loop guard body c modify R.
                           WF R /\ (!x. ~guard x ==> R (modify x) x) /\
                           (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
                            !x. loop x = c + SUM
                                (GENLIST (\j. body (FUNPOW modify j x)) (loop_count guard modify x))
   loop_modify_count_quitc_exit_le
                       |- !loop guard body c exit modify R.
                           WF R /\ (!x. ~guard x ==> R (modify x) x) /\
                           (!x. loop x =
                                if guard x then c
                                else body x + if exit x then 0 else loop (modify x)) ==>
                            !x. loop x <= c + SUM
                                (GENLIST (\j. body (FUNPOW modify j x)) (loop_count guard modify x))

   loop_modify_count_cover_exit_upper
                       |- !loop guard body c cover exit modify R.
                          WF R /\ (!x. ~guard x ==> R (modify x) x) /\
                          (!x. body x <= cover x) /\ (!x y. R x y ==> cover x <= cover y) /\
                          (!x. loop x =
                               if guard x then c
                               else body x + if exit x then 0 else loop (modify x)) ==>
                           !x. loop x <= c + cover x * loop_count guard modify x
   loop_modify_count_exit_upper
                       |- !loop guard body c exit modify R.
                          WF R /\ (!x. ~guard x ==> R (modify x) x) /\
                          (!x y. R x y ==> body x <= body y) /\
                          (!x. loop x =
                               if guard x then c
                               else body x + if exit x then 0 else loop (modify x)) ==>
                           !x. loop x <= c + body x * loop_count guard modify x
   loop_modify_count_cover_upper
                       |- !loop guard body c cover modify R.
                          WF R /\ (!x. ~guard x ==> R (modify x) x) /\
                          (!x. body x <= cover x) /\ (!x y. R x y ==> cover x <= cover y) /\
                          (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
                           !x. loop x <= c + cover x * loop_count guard modify x
   loop_modify_count_upper
                       |- !loop guard body c modify R.
                          WF R /\ (!x. ~guard x ==> R (modify x) x) /\
                          (!x y. R x y ==> body x <= body y) /\
                          (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
                           !x. loop x <= c + body x * loop_count guard modify x

   General Theory of Recurrence with 2 arguments:
   loop2_arg_def       |- !guard modify transform x y. loop2_arg guard modify transform x y =
                           loop_arg (\(x,y). guard x y) (\(x,y). (transform x,modify y)) (x,y)
   loop2_arg_thm       |- !transform modify guard R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
                           !x y. loop2_arg guard modify transform x y =
                                 if guard x y then []
                                 else (x,y):: loop2_arg guard modify transform (transform x) (modify y)
   loop2_arg_nil       |- !transform modify guard R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
                           !x y. guard x y ==> loop2_arg guard modify transform x y = []
   loop2_arg_cons      |- !transform modify guard R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
                           !x y. ~guard x y ==> loop2_arg guard modify transform x y =
                                 (x,y):: loop2_arg guard modify transform (transform x) (modify y)
   loop2_arg_length    |- !transform modify guard R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
                           !x y. LENGTH (loop2_arg guard modify transform x y) =
                                 loop2_count guard modify transform x y
   loop2_arg_eqn       |- !transform modify guard R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
                           !x y. loop2_arg guard modify transform x y =
                                 GENLIST (\j. (FUNPOW transform j x,FUNPOW modify j y))
                                              (loop2_count guard modify transform x y)
   loop2_arg_element   |- !transform modify guard R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
                           !x y k. k < loop2_count guard modify transform x y ==>
                                   EL k (loop2_arg guard modify transform x y) =
                                   (FUNPOW transform k x,FUNPOW modify k y)
   loop2_arg_cover_sum |- !transform modify guard cover R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                          (!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> cover x1 y1 <= cover x2 y2) ==>
                           !x y. SUM (MAP (UNCURRY cover) (loop2_arg guard modify transform x y)) <=
                                 SUM (MAP (K (cover x y)) (loop2_arg guard modify transform x y))
   loop2_modify_count_by_sum
                       |- !loop guard body c modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y + loop (transform x) (modify y)) ==>
                           !x y. loop x y = c +
                                 SUM (MAP (UNCURRY body) (loop2_arg guard modify transform x y))
   loop2_modify_count_exit_by_sum
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y. loop x y <= c +
                                 SUM (MAP (UNCURRY body) (loop2_arg guard modify transform x y))
   loop2_modify_count_quitc_eqn
                       |- !loop guard body c modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y + loop (transform x) (modify y)) ==>
                           !x y. loop x y = c + SUM (GENLIST
                                    (\j. body (FUNPOW transform j x) (FUNPOW modify j y))
                                    (loop2_count guard modify transform x y))
   loop2_modify_count_quitc_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y. loop x y <= c + SUM (GENLIST
                                    (\j. body (FUNPOW transform j x) (FUNPOW modify j y))
                                    (loop2_count guard modify transform x y))
   loop2_modify_count_bcover_exit_upper
                       |- !loop guard body c exit bcover modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                          (!x y. body x y <= bcover x y) /\
                          (!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> bcover x1 y1 <= bcover x2 y2) /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y. loop x y <= c + bcover x y * loop2_count guard modify transform x y
   loop2_modify_count_exit_upper
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                          (!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> body x1 y1 <= body x2 y2) /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y +
                                      if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y. loop x y <= c + body x y * loop2_count guard modify transform x y
   loop2_modify_count_bcover_upper
                       |- !loop guard body c bcover modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                          (!x y. body x y <= bcover x y) /\
                          (!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> bcover x1 y1 <= bcover x2 y2) /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y + loop (transform x) (modify y)) ==>
                           !x y. loop x y <= c + bcover x y * loop2_count guard modify transform x y
   loop2_modify_count_upper
                       |- !loop guard body c modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                          (!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> body x1 y1 <= body x2 y2) /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y + loop (transform x) (modify y)) ==>
                           !x y. loop x y <= c + body x y * loop2_count guard modify transform x y

   Numeric Loops with RISING modify:
   loop_rise_count_cover_quitc_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
                          (!x. loop x =
                               if guard x then c
                               else body x + if exit x then 0 else loop (modify x)) ==>
                           !x cover. (let n = loop_count guard modify x
                                       in (!x. body x <= cover x) /\ MONO cover ==>
                                     loop x <= c + n * cover (FUNPOW modify n x))
   loop_rise_count_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
                          (!x. loop x =
                               if guard x then c
                               else body x + if exit x then 0 else loop (modify x)) ==>
                           !x. (let n = loop_count guard modify x
                                 in MONO body ==> loop x <= c + n * body (FUNPOW modify n x))
   loop_rise_count_cover_le
                       |- !loop guard body c modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
                          (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
                           !x cover. (let n = loop_count guard modify x
                                       in (!x. body x <= cover x) /\ MONO cover ==>
                                     loop x <= c + n * cover (FUNPOW modify n x))
   loop_rise_count_le  |- !loop guard body c modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
                          (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
                           !x. (let n = loop_count guard modify x
                                 in MONO body ==> loop x <= c + n * body (FUNPOW modify n x))
   loop_rise_count_rcover_quitc_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
                          (!x. loop x =
                               if guard x then c
                               else body x + if exit x then 0 else loop (modify x)) ==>
                           !x cover. (let n = loop_count guard modify x
                                       in (!x. body x <= cover x) /\ RMONO cover ==>
                                     loop x <= c + n * cover x)
   loop_rise_count_rbody_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
                          (!x. loop x =
                               if guard x then c
                               else body x + if exit x then 0 else loop (modify x)) ==>
                           !x. (let n = loop_count guard modify x
                                 in RMONO body ==> loop x <= c + n * body x)
   loop_rise_count_rcover_le
                       |- !loop guard body c modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
                          (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
                           !x cover. (let n = loop_count guard modify x
                                       in (!x. body x <= cover x) /\ RMONO cover ==>
                                     loop x <= c + n * cover x)
   loop_rise_count_rbody_le
                       |- !loop guard body c modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
                          (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
                           !x. (let n = loop_count guard modify x
                                 in RMONO body ==> loop x <= c + n * body x)

   Numeric Loops with FALLING modify:
   loop_fall_count_cover_quitc_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
                          (!x. loop x =
                               if guard x then c
                               else body x + if exit x then 0 else loop (modify x)) ==>
                           !x cover. (let n = loop_count guard modify x
                                       in (!x. body x <= cover x) /\ MONO cover ==>
                                     loop x <= c + n * cover x)
   loop_fall_count_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
                          (!x. loop x =
                               if guard x then c
                               else body x + if exit x then 0 else loop (modify x)) ==>
                           !x. (let n = loop_count guard modify x
                                 in MONO body ==> loop x <= c + n * body x)
   loop_fall_count_cover_le
                       |- !loop guard body c modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
                          (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
                           !x cover. (let n = loop_count guard modify x
                                       in (!x. body x <= cover x) /\ MONO cover ==>
                                     loop x <= c + n * cover x)
   loop_fall_count_le  |- !loop guard body c modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
                          (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
                           !x. (let n = loop_count guard modify x
                                 in MONO body ==> loop x <= c + n * body x)
   loop_fall_count_rcover_quitc_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
                          (!x. loop x =
                               if guard x then c
                               else body x + if exit x then 0 else loop (modify x)) ==>
                           !x cover. (let n = loop_count guard modify x
                                       in (!x. body x <= cover x) /\ RMONO cover ==>
                                     loop x <= c + n * cover (FUNPOW modify n x))
   loop_fall_count_rbody_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
                          (!x. loop x =
                               if guard x then c
                               else body x + if exit x then 0 else loop (modify x)) ==>
                           !x. (let n = loop_count guard modify x
                                 in RMONO body ==> loop x <= c + n * body (FUNPOW modify n x))
   loop_fall_count_rcover_le
                       |- !loop guard body c modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
                          (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
                           !x cover. (let n = loop_count guard modify x
                                       in (!x. body x <= cover x) /\ RMONO cover ==>
                                     loop x <= c + n * cover (FUNPOW modify n x))
   loop_fall_count_rbody_le
                       |- !loop guard body c modify transform R. WF R /\
                          (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
                          (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
                           !x. (let n = loop_count guard modify x
                                 in RMONO body ==> loop x <= c + n * body (FUNPOW modify n x))

   Numeric Loops with RISING transform and FALLING modify:
   loop2_rise_fall_count_cover_quitc_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                           RISING transform /\ FALLING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y +
                                      if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y cover. (let n = loop2_count guard modify transform x y
                                         in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                                            loop x y <= c + n * cover (FUNPOW transform n x) y)
   loop2_rise_fall_count_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                           RISING transform /\ FALLING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y +
                                      if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y. (let n = loop2_count guard modify transform x y
                                   in MONO2 body ==> loop x y <= c + n * body (FUNPOW transform n x) y)
   loop2_rise_fall_count_cover_le
                       |- !loop guard body c modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                           RISING transform /\ FALLING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y + loop (transform x) (modify y)) ==>
                           !x y cover. (let n = loop2_count guard modify transform x y
                                         in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                                            loop x y <= c + n * cover (FUNPOW transform n x) y)
   loop2_rise_fall_count_le
                       |- !loop guard body c modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                           RISING transform /\ FALLING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y + loop (transform x) (modify y)) ==>
                           !x y. (let n = loop2_count guard modify transform x y
                                   in MONO2 body ==> loop x y <= c + n * body (FUNPOW transform n x) y)

   Numeric Loops with FALLING transform and FALLING modify:
   loop2_fall_fall_count_cover_quitc_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                           FALLING transform /\ FALLING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y +
                                      if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y cover. (let n = loop2_count guard modify transform x y
                                         in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                                            loop x y <= c + n * cover x y)
   loop2_fall_fall_count_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                           FALLING transform /\ FALLING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y +
                                      if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y. (let n = loop2_count guard modify transform x y in
                                 MONO2 body ==> loop x y <= c + n * body x y)
   loop2_fall_fall_count_cover_le
                       |- !loop guard body c modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                            FALLING transform /\ FALLING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y + loop (transform x) (modify y)) ==>
                           !x y cover. (let n = loop2_count guard modify transform x y
                                         in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                                            loop x y <= c + n * cover x y)
   loop2_fall_fall_count_le
                       |- !loop guard body c modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                            FALLING transform /\ FALLING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y + loop (transform x) (modify y)) ==>
                           !x y. (let n = loop2_count guard modify transform x y
                                   in MONO2 body ==> loop x y <= c + n * body x y)

   Numeric Loops with FALLING transform and RISING modify:
   loop2_fall_rise_count_cover_quitc_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                            FALLING transform /\ RISING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y +
                                      if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y cover. (let n = loop2_count guard modify transform x y
                                         in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                                            loop x y <= c + n * cover x (FUNPOW modify n y))
   loop2_fall_rise_count_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                           FALLING transform /\ RISING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y +
                                      if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y. (let n = loop2_count guard modify transform x y
                                   in MONO2 body ==> loop x y <= c + n * body x (FUNPOW modify n y))
   loop2_fall_rise_count_cover_le
                       |- !loop guard body c modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                           FALLING transform /\ RISING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y + loop (transform x) (modify y)) ==>
                           !x y cover. (let n = loop2_count guard modify transform x y
                                         in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                                            loop x y <= c + n * cover x (FUNPOW modify n y))
   loop2_fall_rise_count_le
                       |- !loop guard body c modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                            FALLING transform /\ RISING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y + loop (transform x) (modify y)) ==>
                           !x y. (let n = loop2_count guard modify transform x y
                                   in MONO2 body ==> loop x y <= c + n * body x (FUNPOW modify n y))

   Numeric Loops with RISING transform and RISING modify:
   loop2_rise_rise_count_cover_quitc_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                            RISING transform /\ RISING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y +
                                      if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y cover. (let n = loop2_count guard modify transform x y
                                         in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                                loop x y <= c + n * cover (FUNPOW transform n x) (FUNPOW modify n y))
   loop2_rise_rise_count_exit_le
                       |- !loop guard body c exit modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                            RISING transform /\ RISING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y +
                                      if exit x y then 0 else loop (transform x) (modify y)) ==>
                           !x y. (let n = loop2_count guard modify transform x y
                                   in MONO2 body ==>
                                 loop x y <= c + n * body (FUNPOW transform n x) (FUNPOW modify n y))
   loop2_rise_rise_count_cover_le
                       |- !loop guard body c modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                            RISING transform /\ RISING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y + loop (transform x) (modify y)) ==>
                           !x y cover. (let n = loop2_count guard modify transform x y
                                         in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                                loop x y <= c + n * cover (FUNPOW transform n x) (FUNPOW modify n y))
   loop2_rise_rise_count_le
                       |- !loop guard body c modify transform R. WF R /\
                          (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
                            RISING transform /\ RISING modify /\
                          (!x y. loop x y =
                                 if guard x y then c
                                 else body x y + loop (transform x) (modify y)) ==>
                           !x y. (let n = loop2_count guard modify transform x y
                                   in MONO2 body ==>
                                 loop x y <= c + n * body (FUNPOW transform n x) (FUNPOW modify n y))
*)

(* ------------------------------------------------------------------------- *)
(* Description                                                               *)
(* ------------------------------------------------------------------------- *)

(*

The basic recurrence pattern for a (loop:'a -> num) is this:

!x. loop x = if guard x then quit x else body x + loop (modify x)

where a well-founded R relates x and (modify x) when (guard x) is false:
WF R /\ (!x. ~guard x ==> R (modify x) x)

The recurrence means:
    loop x = body x + body (modify x) + body (modify (modify x)) + ....
             ... (until guard x is true for last x) ... + quit (last x)
           = quit (last x) + SUM (GENLIST (\j. body (FUNPOW modify j x)) (count-to-last))

To get hold of the count-to-last, define (loop_count x) by a schema:
   loop_count x = if guard x then 0 else SUC (loop_count (modify x))

which is in sync with the loop behaviour.

With these two, we have the fundamental result:

   loop_modify_count_eqn
   |- !loop guard body quit modify R. WF R /\ (!x. ~guard x ==> R (modify x) x) /\
        (!x. loop x = if guard x then quit x else body x + loop (modify x)) ==>
         !x. loop x = quit (FUNPOW modify (loop_count guard modify x) x) +
                      SUM (GENLIST (\j. body (FUNPOW modify j x)) (loop_count guard modify x))

Let n = loop_count guard modify x, this can be expressed as:

    loop x = quit ((modify ** n) x) + SIGMA (0 .. n) (\j. body (modify ** j x))

All other variations, e.g.
with exit: if exit x then 0 else loop (modify x)
with cover: !x. body x <= cover x
with two arguments:
     !x y. loop x y = if guard x y then quit x y else body x y + loop (transform x) (modify y)
with three arguments:
     !x y z. loop x y z = if guard x y z then quit x y z
                          else body x y z + loop (convert x) (transform y) (modify z)

are drived from this basic pattern.

*)

(* ------------------------------------------------------------------------- *)
(* Helper                                                                    *)
(* ------------------------------------------------------------------------- *)

(* Eliminate parenthesis around equality *)
val _ = ParseExtras.tight_equality();

(* ------------------------------------------------------------------------- *)
(* Loop Count for recurrence                                                 *)
(* ------------------------------------------------------------------------- *)

(* Define a loop count corresponding to the length of a loop argument list *)
(* Use a schema to figure out the hypothesis. *)
val loop_count_def = TotalDefn.DefineSchema`
    loop_count (x:'a) =
        if guard x then 0 else SUC (loop_count (modify x))
`;
(*
val loop_count_def =
    [..] |- !x. loop_count guard modify x =
          if guard x then 0 else SUC (loop_count guard modify (modify x)): thm
to see the [..], which is hypothesis,
> hyp loop_count_def;
val it = [``!x. ~guard x ==> R (modify x) x``, ``WF R``]: term list
*)

(* Obtain theorem from loop_count definition *)
val loop_count_thm = save_thm("loop_count_thm",
    loop_count_def |> DISCH_ALL |> SIMP_RULE bool_ss [AND_IMP_INTRO] |> GEN_ALL);
(* val loop_count_thm =
   |- !modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
          !x. loop_count guard modify x =
              if guard x then 0 else SUC (loop_count guard modify (modify x)): thm
*)

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
             !x. guard x ==> (loop_count guard modify x = 0) *)
(* Proof: by loop_count_def *)
val loop_count_0 = store_thm(
  "loop_count_0",
  ``!modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
   !x. guard x ==> (loop_count guard modify x = 0)``,
  rpt strip_tac >>
  rw[Once loop_count_def]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
             !x. ~guard x ==> (loop_count guard modify x = SUC (loop_count guard modify (modify x))) *)
(* Proof: by loop_count_def *)
val loop_count_suc = store_thm(
  "loop_count_suc",
  ``!modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
   !x. ~guard x ==> (loop_count guard modify x = SUC (loop_count guard modify (modify x)))``,
  rpt strip_tac >>
  rw[Once loop_count_def]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                !x. guard (FUNPOW modify (loop_count guard modify x) x) *)
(* Proof:
   If guard x,
          guard (FUNPOW modify (loop_count guard modify x) x)
      <=> guard (FUNPOW modify 0 x)           by loop_count_0
      <=> guard x                             by FUNPOW_0
      <=> T                                   by this case, guard x.
   If ~guard x,
          guard (FUNPOW modify (loop_count guard modify x) x)
      <=> guard (FUNPOW modify (SUC (loop_count guard modify (modify x))) x)    by loop_count_suc
      <=> guard (FUNPOW modify (loop_count guard modify (modify x)) (modify x)) by FUNPOW
      <=> T                                   by induction hypothesis
*)
val loop_count_iterating = store_thm(
  "loop_count_iterating",
  ``!modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                !x. guard (FUNPOW modify (loop_count guard modify x) x)``,
  ntac 4 strip_tac >>
  ho_match_mp_tac (theorem "loop_count_ind") >>
  rw[] >>
  Cases_on `guard x` >-
  metis_tac[loop_count_0, FUNPOW_0] >>
  qabbrev_tac `n = loop_count guard modify (modify x)` >>
  `guard (FUNPOW modify (loop_count guard modify x) x) <=> guard (FUNPOW modify (SUC n) x)` by metis_tac[loop_count_suc] >>
  metis_tac[FUNPOW]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) ==> ?n. guard (FUNPOW modify n x) *)
(* Proof:
   By contradiction, suppose that: !n. ~guard (FUNPOW modify n x).
   Let s = IMAGE (\n. FUNPOW modify n x) univ(:num).
   that is, all the iterations of x by modify.
   Note WF R means
        !B. (?w. B w) ==> ?min. B min /\ !b. R b min ==> ~B b   by WF_DEF
   Let the B be s, we need to show:
   (1) ?w. s w     find a witness
       Since the set s is non-empty -- it is the image of a universal set,
       any element of s is a witness.
   (2) ?min. s min /\ !b. R b min ==> ~s b
       This means: (!n. min <> FUNPOW modify n x) \/ ?b. R b min /\ ?n. b = FUNPOW modify n x
       which is: min = FUNPOW modify n x ==> ?b. R b min /\ ?n. b = FUNPOW modify n x
       or ?k. R (FUNPOW modify k x) R b min, where min = FUNPOW modify n x.
       that is, ?k. R (FUNPOW modify k x) (FUNPOW modify n x)
       Take k = SUC n, then R (FUNPOW modify (SUC n) x) (FUNPOW modify n x)
       since putting y = FUNPOW modify n x,
       we have ~guard y             by our assumption of contradiction
           ==> R (modify y) y       by given !x. ~guard x ==> R (modify x) x
          and modify y = modify (FUNPOW modify n x)
                       = FUNPOW modify (SUC n) x      by FUNPOW_SUC
*)
val loop_count_exists = store_thm(
  "loop_count_exists",
  ``!modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                !x. ?n. guard (FUNPOW modify n x)``,
  spose_not_then strip_assume_tac >>
  qabbrev_tac `s = IMAGE (\n. FUNPOW modify n x) univ(:num)` >>
  fs[relationTheory.WF_DEF] >>
  first_x_assum (qspec_then `s` mp_tac) >>
  impl_tac >-
  rw[Abbr`s`] >>
  rw[Abbr`s`] >>
  rw[DISJ_EQ_IMP] >>
  simp[PULL_EXISTS] >>
  qexists_tac `SUC n` >>
  simp[FUNPOW_SUC]);

(* Theorem:WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
   !x n. guard (FUNPOW modify n x) /\ (!m. m < n ==> ~guard (FUNPOW modify m x)) ==>
         (loop_count guard modify x = n)  *)
(* Proof:
   By induction from loop_count_def.
   If guard x,
      loop_count guard modify x = 0         by loop_count_0
      If n = 0, this is trivially true.
      If n <> 0, then !m. m < n ==> ~guard (FUNPOW modify m x) cannot hold,
         since m = 0 gives
               ~guard (FUNPOW modify 0 x)
             = ~guard x                     by FUNPOW_0
         which contradicts guard x.
   If ~guard x,
        loop_count guard modify x
      = SUC (loop_count guard modify (modify x))  by loop_count_suc
      Now n <> 0,
        since guard (FUNPOW modify 0 x) gives guard x  by FUNPOW_0
        which contradicts ~guard x.
      Let n = SUC k.
      Then guard (FUNPOW modify (SUC k)) /\
           !m. m < SUC k ==> ~guard (FUNPOW modify m x)
      The first one gives
          guard (FUNPOW modify k (modify x))    by !x. ~guard x ==> R (modify x) x
      The implication gives
          !m. m < k ==> ~guard (FUNPOW modify m (modify x))  by putting (SUC m), FUNPOW
      Thus loop_count guard modify (modify x) = k   by induction hypothesis
      or loop_count guard modify x = SUC k = n.
*)
val loop_count_minimal = store_thm(
  "loop_count_minimal",
  ``!modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
   !x n. guard (FUNPOW modify n x) /\ (!m. m < n ==> ~guard (FUNPOW modify m x)) ==>
         (loop_count guard modify x = n)``,
  ntac 4 strip_tac >>
  ho_match_mp_tac (theorem "loop_count_ind") >>
  rw[] >>
  rw[Once loop_count_def] >| [
    (Cases_on `n` >> fs[]) >>
    first_x_assum (qspec_then `0` mp_tac) >>
    simp[],
    fs[] >>
    (Cases_on `n` >> fs[]) >>
    first_x_assum irule >>
    fs[FUNPOW] >>
    rpt strip_tac >>
    first_x_assum (qspec_then `SUC m` mp_tac) >>
    simp[FUNPOW]
  ]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
           !x. loop_count guard modify x = LEAST n. guard (FUNPOW modify n x) *)
(* Proof:
   By LEAST elimination, this is to show:
   (1) ?n. guard (FUNPOW modify n x)), true      by loop_count_exists
   (2) !n. (!m. m < n ==> ~guard (FUNPOW modify m x)) /\ guard (FUNPOW modify n x) ==>
       loop_count guard modify x = n, true       by loop_count_minimal
*)
val loop_count_eqn = store_thm(
  "loop_count_eqn",
  ``!modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
    !x. loop_count guard modify x = LEAST n. guard (FUNPOW modify n x)``,
  rpt strip_tac >>
  numLib.LEAST_ELIM_TAC >>
  rpt strip_tac >-
  metis_tac[loop_count_exists] >>
  metis_tac[loop_count_minimal]);

(* ------------------------------------------------------------------------- *)
(* Direct derivation of general results from loop_count.                     *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* General Theory of Recurrence with 1 argument                              *)
(* ------------------------------------------------------------------------- *)

(* Note: basic solution of the recurrence:

   Given: !x. loop x = if guard x then quit x else body x + loop (modify x)
   Then:  loop x = SUM [body x, body (modify x), body (modify (modify x)), .....] +
                   quit (last modify x)
                       for n terms, where n = loop_count guard modify x
                       and last modify x = x after n modify
   Thus:  loop x = quit (FUNPOW modify n x) + SUM (GENLIST (\j. body (FUNPOW modify j x)) n)
*)


(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\
        (!x. loop x = if guard x then quit x else body x + loop (modify x)) ==>
         !x. loop x = quit (FUNPOW modify (loop_count guard modify x) x) +
                      SUM (GENLIST (\j. body (FUNPOW modify j x)) (loop_count guard modify x)) *)
(* Proof:
   By induction from loop_count_def.
   Let f = (\j. body (FUNPOW modify j x)),
       n = loop_count guard modify x.
   If guard x,
      Then n = 0                 by loop_count_0
      LHS = loop x = quit x      by given loop x, guard x
      RHS = quit (FUNPOW modify 0 x) + SUM (GENLIST f 0)
          = quit x + SUM []      by FUNPOW_0, GENLIST_0
          = quit x + 0 = LHS     by SUM
   If ~guard x,
      Let g = (\j. body (FUNPOW modify j (modify x))),
          m = loop_count guard modify (modify x).
      Note n = SUC m             by loop_count_suc
       and g = f o SUC           by FUN_EQ_THM, FUNPOW
       and f 0 = body x          by notation
        loop x
      = body x + loop (modify x)                                          by given loop x, ~guard x
      = body x + (quit (FUNPOW modify m (modify x)) + SUM (GENLIST g m))  by induction hypothesis
      = quit (FUNPOW modify m (modify x)) + (body x + SUM (GENLIST g m))  by arithmetic
      = quit (FUNPOW modify n x) + (f 0 + SUM (GENLIST (f o SUC) m))      by FUNPOW
      = quit (FUNPOW modify n x) + (SUM (f 0 :: GENLIST (f o SUC) m))     by SUM
      = quit (FUNPOW modify n x) + SUM (GENLIST f n)                      by GENLIST_CONS
*)
val loop_modify_count_eqn = store_thm(
  "loop_modify_count_eqn",
  ``!loop guard body quit modify R.
    WF R /\ (!x. ~guard x ==> R (modify x) x) /\
    (!x. loop x = if guard x then quit x else body x + loop (modify x)) ==>
     !x. loop x = quit (FUNPOW modify (loop_count guard modify x) x) +
                  SUM (GENLIST (\j. body (FUNPOW modify j x)) (loop_count guard modify x))``,
  ntac 7 strip_tac >>
  ho_match_mp_tac (theorem "loop_count_ind") >>
  rpt strip_tac >>
  Cases_on `guard x` >| [
    `loop x = quit x` by metis_tac[] >>
    `loop_count guard modify x = 0` by metis_tac[loop_count_0] >>
    simp[],
    qabbrev_tac `f = \j. body (FUNPOW modify j x)` >>
    qabbrev_tac `n = loop_count guard modify x` >>
    qabbrev_tac `g = \j. body (FUNPOW modify j (modify x))` >>
    qabbrev_tac `m = loop_count guard modify (modify x)` >>
    `n = SUC m` by metis_tac[loop_count_suc] >>
    `g = f o SUC` by rw[FUN_EQ_THM, FUNPOW, Abbr`f`, Abbr`g`] >>
    `f 0 = body x` by rw[Abbr`f`] >>
    `loop x = body x + loop (modify x)` by metis_tac[] >>
    `_ = quit (FUNPOW modify m (modify x)) + (body x + SUM (GENLIST g m))` by rw[] >>
    `_ = quit (FUNPOW modify n x) + (f 0 + SUM (GENLIST (f o SUC) m))` by rw[FUNPOW] >>
    `_ = quit (FUNPOW modify n x) + SUM (GENLIST f n)` by rw[GENLIST_CONS] >>
    decide_tac
  ]);

(* Theorem: Equivalent form of loop_modify_count_eqn *)
(* Proof: by loop_modify_count_eqn *)
val loop_modify_count_eqn_1 = store_thm(
  "loop_modify_count_eqn_1",
  ``!loop guard body quit modify R.
    WF R /\ (!x. ~guard x ==> R (modify x) x) /\
    (!x. loop x = if guard x then quit x else body x + loop (modify x)) ==>
     !x. let n = loop_count guard modify x in
         loop x = quit (FUNPOW modify n x) + SUM (GENLIST (\j. body (FUNPOW modify j x)) n)``,
  metis_tac[loop_modify_count_eqn]);

(* Theorem: Equivalent form of loop_modify_count_eqn *)
(* Proof: by loop_modify_count_eqn *)
val loop_modify_count_eqn_2 = store_thm(
  "loop_modify_count_eqn_2",
  ``!loop guard body quit modify R.
    WF R /\ (!x. ~guard x ==> R (modify x) x) /\
    (!x. loop x = if guard x then quit x else body x + loop (modify x)) ==>
     !x. let n = loop_count guard modify x in
         loop x = quit (FUNPOW modify n x) + SIGMA (\j. body (FUNPOW modify j x)) (count n)``,
  metis_tac[loop_modify_count_eqn_1, SUM_GENLIST]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\
    (!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)) ==>
     !x. loop x <= quit (FUNPOW modify (loop_count guard modify x) x) +
                   SUM (GENLIST (\j. body (FUNPOW modify j x)) (loop_count guard modify x)) *)
(* Proof:
   By induction from loop_count_def.
   Let f = (\j. body (FUNPOW modify j x)),
       n = loop_count guard modify x.
   If guard x,
      Then n = 0                 by loop_count_0
      LHS = loop x = quit x      by given loop x, guard x
      RHS = quit (FUNPOW modify 0 x) + SUM (GENLIST f 0)
          = quit x + SUM []      by FUNPOW_0, GENLIST_0
          = quit x + 0           by SUM
      Thus LHS <= RHS.
   If ~guard x,
      Let g = (\j. body (FUNPOW modify j (modify x))),
          m = loop_count guard modify (modify x).
      Note n = SUC m             by loop_count_suc
       and g = f o SUC           by FUN_EQ_THM, FUNPOW
       and f 0 = body x          by notation
        loop x
      = body x + if exit x then 0 else loop (modify x)                    by given loop x, ~guard x
     <= body x + loop (modify x)                                          by ignoring exit x
     <= body x + (quit (FUNPOW modify m (modify x)) + SUM (GENLIST g m))  by induction hypothesis
      = quit (FUNPOW modify m (modify x)) + (body x + SUM (GENLIST g m))  by arithmetic
      = quit (FUNPOW modify n x) + (f 0 + SUM (GENLIST (f o SUC) m))      by FUNPOW
      = quit (FUNPOW modify n x) + (SUM (f 0 :: GENLIST (f o SUC) m))     by SUM
      = quit (FUNPOW modify n x) + SUM (GENLIST f n)                      by GENLIST_CONS
*)
val loop_modify_count_exit_le = store_thm(
  "loop_modify_count_exit_le",
  ``!loop guard body quit exit modify R.
     WF R /\ (!x. ~guard x ==> R (modify x) x) /\
    (!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)) ==>
     !x. loop x <= quit (FUNPOW modify (loop_count guard modify x) x) +
                   SUM (GENLIST (\j. body (FUNPOW modify j x)) (loop_count guard modify x))``,
  ntac 8 strip_tac >>
  ho_match_mp_tac (theorem "loop_count_ind") >>
  rpt strip_tac >>
  Cases_on `guard x` >| [
    `loop x = quit x` by metis_tac[] >>
    `loop_count guard modify x = 0` by metis_tac[loop_count_0] >>
    simp[],
    qabbrev_tac `f = \j. body (FUNPOW modify j x)` >>
    qabbrev_tac `n = loop_count guard modify x` >>
    qabbrev_tac `g = \j. body (FUNPOW modify j (modify x))` >>
    qabbrev_tac `m = loop_count guard modify (modify x)` >>
    `n = SUC m` by metis_tac[loop_count_suc] >>
    `g = f o SUC` by rw[FUN_EQ_THM, FUNPOW, Abbr`f`, Abbr`g`] >>
    `f 0 = body x` by rw[Abbr`f`] >>
    `loop x = body x + if exit x then 0 else loop (modify x)` by metis_tac[] >>
    `(body x + if exit x then 0 else loop (modify x)) <= body x + loop (modify x)` by decide_tac >>
    `loop x <= body x + loop (modify x)` by metis_tac[] >>
    `loop (modify x) <= quit (FUNPOW modify m (modify x)) + SUM (GENLIST g m)` by rw[] >>
    `loop x <= quit (FUNPOW modify m (modify x)) + (body x + SUM (GENLIST g m))` by decide_tac >>
    `quit (FUNPOW modify m (modify x)) + (body x + SUM (GENLIST g m)) =
    quit (FUNPOW modify n x) + (f 0 + SUM (GENLIST (f o SUC) m))` by rw[FUNPOW] >>
    `_ = quit (FUNPOW modify n x) + SUM (GENLIST f n)` by rw[GENLIST_CONS] >>
    decide_tac
  ]);

(* ------------------------------------------------------------------------- *)
(* Estimation for Numeric Loops                                              *)
(* ------------------------------------------------------------------------- *)

(* Idea:

   From loop_modify_count_eqn, let n = loop_count guard modify x.
     loop x
   = quit (last x) + SUM (GENLIST (\j. body (FUNPOW modify j x)) n)
   = quit (last x) + [body x, body (m x), body (m (m x)), ....]    for n terms
  If FALLING m,
  <= quit (last x) + [body x, body x, body x, .....]    if MONO body,
   = quit (last x) + n * body x
  If RISING m,
  <= quit (last x) + [body (last x), body (last x), ...]  if MONO body,
   = quit (last x) + n * body (last x)
*)

(* ------------------------------------------------------------------------- *)
(* Numeric Loops with RISING modify                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                  in (!x. body x <= cover x) /\ MONO cover ==>
                     loop x <= quit (FUNPOW modify n x) + n * cover (FUNPOW modify n x) *)
(* Proof:
   Let f = (\j. body (FUNPOW modify j x)),
       n = loop_count guard modify x,
       z = FUNPOW modify n x.

   For k < n,
      FUNPOW modify k x <= FUNPOW modify n x  by FUNPOW_LE_RISING, RISING modify
                         = z                  by notation
   Thus,
       loop x
    <= quit z + SUM (GENLIST f n)                by loop_modify_count_quitc_exit_le
    <= quit z + SUM (GENLIST (K (cover z)) n)    by SUM_LE, EL_GENLIST, RISING modify
     = quit z + (cover z) * n                    by SUM_GENLIST_K
     = quit z + n * cover z                      by MULT_COMM
*)
val loop_rise_count_cover_exit_le = store_thm(
  "loop_rise_count_cover_exit_le",
  ``!loop body quit exit guard modify R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                  in (!x. body x <= cover x) /\ MONO cover ==>
                     loop x <= quit (FUNPOW modify n x) + n * cover (FUNPOW modify n x)``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop_modify_count_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `f = \j. body (FUNPOW modify j x)` >>
  qabbrev_tac `n = loop_count guard modify x` >>
  qabbrev_tac `z = FUNPOW modify n x` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover z)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`, Abbr`z`] >>
  `FUNPOW modify k x <= FUNPOW modify n x` by rw[FUNPOW_LE_RISING] >>
  qabbrev_tac `u = FUNPOW modify k x` >>
  qabbrev_tac `v = FUNPOW modify n x` >>
  `body u <= cover u` by rw[] >>
  `cover u <= cover v` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover z)) n) = cover z * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                  in (!x. body x <= cover x) /\ RMONO cover ==>
                     loop x <= quit (FUNPOW modify n x) + n * cover x *)
(* Proof:
   Let f = (\j. body (FUNPOW modify j x)),
       n = loop_count guard modify x,
       z = FUNPOW modify n x.

   For k < n,
      Let u = FUNPOW modify k x.
      FUNPOW modify 0 x <= FUNPOW modify k x  by FUNPOW_LE_RISING, RISING modify
                      x <= u                  by FUNPOW_0
             so cover u <= cover x            by RMONO cover
      body u <= cover u                       by body and cover
   Thus,
       loop x
    <= quit z + SUM (GENLIST f n)                by loop_modify_count_exit_le
    <= quit z + SUM (GENLIST (K (cover x)) n)    by SUM_LE, EL_GENLIST, RISING modify
     = quit z + (cover x) * n                    by SUM_GENLIST_K
     = quit z + n * cover x                      by MULT_COMM
*)
val loop_rise_count_rcover_exit_le = store_thm(
  "loop_rise_count_rcover_exit_le",
  ``!loop body quit exit guard modify R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                  in (!x. body x <= cover x) /\ RMONO cover ==>
                     loop x <= quit (FUNPOW modify n x) + n * cover x``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop_modify_count_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `f = \j. body (FUNPOW modify j x)` >>
  qabbrev_tac `n = loop_count guard modify x` >>
  qabbrev_tac `z = FUNPOW modify n x` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover x)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`] >>
  `FUNPOW modify 0 x <= FUNPOW modify k x` by rw[FUNPOW_LE_RISING] >>
  `FUNPOW modify 0 x = x` by rw[] >>
  qabbrev_tac `u = FUNPOW modify k x` >>
  `body u <= cover u` by rw[] >>
  `cover u <= cover x` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover x)) n) = cover x * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Numeric Loops with FALLING modify                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                  in (!x. body x <= cover x) /\ MONO cover ==>
                     loop x <= quit (FUNPOW modify n x) + n * cover x *)
(* Proof:
   Let f = (\j. body (FUNPOW modify j x)),
       n = loop_count guard modify x,
       z = FUNPOW modify n x.

   For k < n,
      FUNPOW modify k x <= FUNPOW modify 0 x  by FUNPOW_LE_FALLING, FALLING modify
                         = x                  by FUNPOW_0
   Thus,
       loop x
    <= quit z + SUM (GENLIST f n)                by loop_modify_count_exit_le
    <= quit z + SUM (GENLIST (K (cover x)) n)    by SUM_LE, EL_GENLIST, RISING modify
     = quit z + (cover x) * n                    by SUM_GENLIST_K
     = quit z + n * cover x                      by MULT_COMM
*)
val loop_fall_count_cover_exit_le = store_thm(
  "loop_fall_count_cover_exit_le",
  ``!loop guard body quit exit modify R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                  in (!x. body x <= cover x) /\ MONO cover ==>
                     loop x <= quit (FUNPOW modify n x) + n * cover x``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop_modify_count_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `f = \j. body (FUNPOW modify j x)` >>
  qabbrev_tac `n = loop_count guard modify x` >>
  qabbrev_tac `z = FUNPOW modify n x` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover x)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`] >>
  `FUNPOW modify k x <= FUNPOW modify 0 x` by rw[FUNPOW_LE_FALLING] >>
  `FUNPOW modify 0 x = x` by rw[] >>
  qabbrev_tac `u = FUNPOW modify k x` >>
  `body u <= cover u` by rw[] >>
  `cover u <= cover x` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover x)) n) = cover x * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                  in (!x. body x <= cover x) /\ RMONO cover ==>
                     loop x <= quit (FUNPOW modify n x) + n * cover (FUNPOW modify n x) *)
(* Proof:
   Let f = (\j. body (FUNPOW modify j x)),
       n = loop_count guard modify x,
       z = FUNPOW modify n x.

   For k < n,
      Let u = FUNPOW modify k x.
      FUNPOW modify n x <= FUNPOW modify k x  by FUNPOW_LE_FALLING, FALLING modify
                      z <= u                  by notation
             so cover u <= cover z            by RMONO cover
      body u <= cover u                       by cover property
   Thus,
       loop x
    <= quit z + SUM (GENLIST f n)                by loop_modify_count_exit_le
    <= quit z + SUM (GENLIST (K (cover z)) n)    by SUM_LE, EL_GENLIST, RISING modify
     = quit z + (cover z) * n                    by SUM_GENLIST_K
     = quit z + n * cover z                      by MULT_COMM
*)
val loop_fall_count_rcover_exit_le = store_thm(
  "loop_fall_count_rcover_exit_le",
  ``!loop guard body quit exit modify R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                  in (!x. body x <= cover x) /\ RMONO cover ==>
                     loop x <= quit (FUNPOW modify n x) + n * cover (FUNPOW modify n x)``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (modify x)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop_modify_count_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `f = \j. body (FUNPOW modify j x)` >>
  qabbrev_tac `n = loop_count guard modify x` >>
  qabbrev_tac `z = FUNPOW modify n x` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover z)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`, Abbr`z`] >>
  `FUNPOW modify n x <= FUNPOW modify k x` by rw[FUNPOW_LE_FALLING] >>
  qabbrev_tac `u = FUNPOW modify k x` >>
  qabbrev_tac `v = FUNPOW modify n x` >>
  `body u <= cover u` by rw[] >>
  `cover u <= cover v` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover z)) n) = cover z * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* General Theory of Recurrence with 2 arguments                             *)
(* ------------------------------------------------------------------------- *)

(*
> loop_count_def |> DISCH_ALL |> INST_TYPE [alpha |-> ``:'a # 'b``]
  |> SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD]
  |> Q.INST [`guard` |-> `(\(x,y). gd x y)`, `modify` |-> `(\(x,y). (t x, m y))`]
  |> SIMP_RULE (srw_ss()) [];
val it = |- WF R ==> (!p_1 p_2. ~gd p_1 p_2 ==> R (t p_1,m p_2) (p_1,p_2)) ==>
      !p_1 p_2. loop_count (\(x,y). gd x y) (\(x,y). (t x,m y)) (p_1,p_2) =
          if gd p_1 p_2 then 0 else
          SUC (loop_count (\(x,y). gd x y) (\(x,y). (t x,m y)) (t p_1,m p_2)): thm
*)

(* Define loop_count for 2 arguments *)
val loop2_count_def = Define`
    loop2_count guard modify transform x y =
       loop_count (\(x,y). guard x y) (\(x,y). (transform x, modify y)) (x, y)
`;

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
      !x y. loop2_count guard modify transform x y =
              if guard x y then 0
              else SUC (loop2_count guard modify transform (transform x) (modify y)) *)
(* Proof: by loop_count_thm, loop2_count_def *)
val loop2_count_thm = store_thm(
  "loop2_count_thm",
  ``!transform modify guard R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
      !x y. loop2_count guard modify transform x y =
              if guard x y then 0
              else SUC (loop2_count guard modify transform (transform x) (modify y))``,
  rw[loop2_count_def] >>
  imp_res_tac loop_count_thm >>
  rw[Once pairTheory.FORALL_PROD]);

(* Obtain similar theorems. *)
val loop2_count_0 = store_thm(
  "loop2_count_0",
  ``!transform modify guard R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
      !x y. guard x y ==> (loop2_count guard modify transform x y = 0)``,
  rw[loop2_count_def] >>
  imp_res_tac loop_count_0 >>
  rw[Once pairTheory.FORALL_PROD]);

val loop2_count_suc = store_thm(
  "loop2_count_suc",
  ``!transform modify guard R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
      !x y. ~guard x y ==> (loop2_count guard modify transform x y =
            SUC (loop2_count guard modify transform (transform x) (modify y)))``,
  rw[loop2_count_def] >>
  imp_res_tac loop_count_suc >>
  rw[Once pairTheory.FORALL_PROD]);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
      !x y. guard (FUNPOW transform (loop2_count guard modify transform x y) x)
                  (FUNPOW modify (loop2_count guard modify transform x y) y) *)
(* Proof: by loop_count_iterating, loop2_count_def. *)
val loop2_count_iterating = store_thm(
  "loop2_count_iterating",
  ``!transform modify guard R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) ==>
      !x y. guard (FUNPOW transform (loop2_count guard modify transform x y) x)
                  (FUNPOW modify (loop2_count guard modify transform x y) y)``,
  rpt strip_tac >>
  assume_tac (loop_count_iterating
   |> SPEC_ALL |> INST_TYPE [``:'a`` |-> ``:'a # 'b``]
   |> SIMP_RULE bool_ss [pairTheory.FORALL_PROD]
   |> Q.INST [`loop` |-> `(\(x,y). lp x y)`, `guard` |-> `(\(x,y). gd x y)`, `quit` |-> `(\(x,y). qt x y)`,
              `body` |-> `(\(x,y). b x y)`, `modify` |-> `(\(x,y). (t x, m y))`]
   |> SIMP_RULE bool_ss [FUNPOW_PAIR, GSYM loop2_count_def]
   |> Q.INST [`lp` |-> `loop`, `gd` |-> `guard`, `qt` |-> `quit`, `b` |-> `body`, `t` |-> `transform`, `m` |-> `modify`]
   |> PairRules.PBETA_RULE) >>
  metis_tac[]);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
        (!x y. loop x y = if guard x y then quit x y else body x y + loop (transform x) (modify y)) ==>
         !x y. loop x y = quit (FUNPOW transform (loop2_count guard modify transform x y) x)
                               (FUNPOW modify (loop2_count guard modify transform x y) y) +
               SUM (GENLIST (\j. body (FUNPOW transform j x) (FUNPOW modify j y))
                                      (loop2_count guard modify transform x y)) *)
(* Proof: by loop_modify_count_eqn, loop2_count_def *)
val loop2_modify_count_eqn = store_thm(
  "loop2_modify_count_eqn",
  ``!loop guard body quit modify transform R.
        WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
        (!x y. loop x y = if guard x y then quit x y else body x y + loop (transform x) (modify y)) ==>
         !x y. loop x y = quit (FUNPOW transform (loop2_count guard modify transform x y) x)
                               (FUNPOW modify (loop2_count guard modify transform x y) y) +
               SUM (GENLIST (\j. body (FUNPOW transform j x) (FUNPOW modify j y))
                                      (loop2_count guard modify transform x y))``,
  rpt strip_tac >>
  assume_tac (loop_modify_count_eqn
   |> SPEC_ALL |> INST_TYPE [``:'a`` |-> ``:'a # 'b``]
   |> SIMP_RULE bool_ss [pairTheory.FORALL_PROD]
   |> Q.INST [`loop` |-> `(\(x,y). lp x y)`, `guard` |-> `(\(x,y). gd x y)`, `quit` |-> `(\(x,y). qt x y)`,
              `body` |-> `(\(x,y). b x y)`, `modify` |-> `(\(x,y). (t x, m y))`]
   |> SIMP_RULE bool_ss [FUNPOW_PAIR, GSYM loop2_count_def]
   |> Q.INST [`lp` |-> `loop`, `gd` |-> `guard`, `qt` |-> `quit`, `b` |-> `body`, `t` |-> `transform`, `m` |-> `modify`]
   |> PairRules.PBETA_RULE) >>
  metis_tac[]);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
    (!x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
     !x y. loop x y <= quit (FUNPOW transform (loop2_count guard modify transform x y) x)
                               (FUNPOW modify (loop2_count guard modify transform x y) y) +
               SUM (GENLIST (\j. body (FUNPOW transform j x) (FUNPOW modify j y))
                                      (loop2_count guard modify transform x y)) *)
(* Proof: by loop_modify_count_exit_le, loop2_count_def. *)
val loop2_modify_count_exit_le = store_thm(
  "loop2_modify_count_exit_le",
  ``!loop guard body quit exit modify transform R.
    WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
    (!x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
     !x y. loop x y <= quit (FUNPOW transform (loop2_count guard modify transform x y) x)
                               (FUNPOW modify (loop2_count guard modify transform x y) y) +
               SUM (GENLIST (\j. body (FUNPOW transform j x) (FUNPOW modify j y))
                                      (loop2_count guard modify transform x y))``,
  rpt strip_tac >>
  assume_tac (loop_modify_count_exit_le
   |> SPEC_ALL |> INST_TYPE [``:'a`` |-> ``:'a # 'b``]
   |> SIMP_RULE bool_ss [pairTheory.FORALL_PROD]
   |> Q.INST [`loop` |-> `(\(x,y). lp x y)`, `guard` |-> `(\(x,y). gd x y)`,`quit` |-> `(\(x,y). qt x y)`,
              `body` |-> `(\(x,y). b x y)`, `modify` |-> `(\(x,y). (t x, m y))`, `exit` |-> `(\(x,y). et x y)`]
   |> SIMP_RULE bool_ss [FUNPOW_PAIR, GSYM loop2_count_def]
   |> Q.INST [`lp` |-> `loop`, `gd` |-> `guard`, `qt` |-> `quit`, `et` |-> `exit`, `b` |-> `body`, `t` |-> `transform`, `m` |-> `modify`]
   |> PairRules.PBETA_RULE) >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* List for Transform argument                                               *)
(* ------------------------------------------------------------------------- *)

(* Define the iterating list *)
val iterating_def = Define`
    iterating f x y = if y = 0 then [] else x::iterating f (f x) (y - 1)
`;

(*
EVAL ``iterating SQ 2 (pop 2 10)``; = [2; 4; 16; 256]: thm
EVAL ``iterating SQ 3 (pop 2 7)``; = [3; 9; 81]: thm
EVAL ``MAP (\j. FUNPOW SQ j 2) [0 ..< (pop 2 10)]``; = [2; 4; 16; 256]: thm
EVAL ``MAP ((combin$C (FUNPOW SQ)) 2) [0 ..< (pop 2 10)]``;  = [2; 4; 16; 256]:thm
*)

(* Theorem: iterating f x 0 = [] *)
(* Proof: by iterating_def *)
val iterating_nil = store_thm(
  "iterating_nil",
  ``!f x. iterating f x 0 = []``,
  rw[Once iterating_def]);

(* Theorem: iterating f x (SUC y) = x::iterating f (f x) y *)
(* Proof: by iterating_def *)
val iterating_cons = store_thm(
  "iterating_cons",
  ``!f x y. iterating f x (SUC y) = x::iterating f (f x) y``,
  rw[Once iterating_def]);

(* Combine these theorems *)
val iterating_alt = save_thm("iterating_alt", CONJ iterating_nil iterating_cons);
(*
val iterating_alt = |- (!f x. iterating f x 0 = []) /\
                       !f x y. iterating f x (SUC y) = x::iterating f (f x) y: thm
*)

(* Theorem: iterating f x y = MAP (combin$C (FUNPOW f) x) [0 ..< y] *)
(* Proof:
   By induction on y.
   Let g = combin$C (FUNPOW f) x, which is (\j. FUNPOW f j x).
   Base: !x. iterating f x 0 = MAP g [0 ..< 0]
      LHS = iterating f x 0 = []       by iterating_nil
      RHS = MAP g [0 ..< 0]
          = MAP g []                   by listRangeLHI_def
           = []  = LHS                 by MAP
   Step: !x. iterating f x y = MAP (combin$C (FUNPOW f) x) [0 ..< y] ==>
         !x. iterating f x (SUC y) = MAP (combin$C (FUNPOW f) x) [0 ..< SUC y]

        Let h = combin$C (FUNPOW f) (f x), which is (\j. FUNPOW f j (f x)).
       Then h = g o SUC                by FUNPOW
        and g 0 = x                    by FUNPOW_0

         iterating f x (SUC y)
       = x :: iterating f (f x) y      by iterating_cons
       = x :: MAP h [0 ..< y]          by induction hypothesis
       = x :: MAP (g o SUC) [0 ..< y]  by h = g o SUC
       = x :: MAP g [1 ..< SUC y]      by listRangeLHI_MAP_SUC
       = g 0 :: MAP g [1 ..< SUC y]    by x = g 0
       = MAP g (0::[1 ..< SUC y])      by MAP
       = MAP g [0 ..< SUC y]           by listRangeLHI_CONS
*)
val iterating_eqn = store_thm(
  "iterating_eqn",
  ``!f x y. iterating f x y = MAP (combin$C (FUNPOW f) x) [0 ..< y]``,
  strip_tac >>
  Induct_on `y` >-
  rw[Once iterating_def] >>
  rpt strip_tac >>
  qabbrev_tac `g = combin$C (FUNPOW f) x` >>
  qabbrev_tac `h = combin$C (FUNPOW f) (f x)` >>
  `x = g 0` by rw[Abbr`g`] >>
  `h = g o SUC` by rw[FUN_EQ_THM, FUNPOW, Abbr`g`, Abbr`h`] >>
  `iterating f x (SUC y) = x :: iterating f (f x) y` by rw[Once iterating_def] >>
  `_ = x :: MAP h [0 ..< y]` by rw[Abbr`h`] >>
  `_ = x :: MAP (g o SUC) [0 ..< y]` by rw[] >>
  `_ = g 0 :: MAP g [1 ..< SUC y]` by rw[GSYM listRangeLHI_MAP_SUC, ADD1] >>
  `_ = MAP g [0 ..< SUC y]` by rw[listRangeLHI_CONS] >>
  rw[]);

(* Theorem: LENGTH (iterating f x y) = y *)
(* Proof:
     LENGTH (iterating f x y)
   = LENGTH (MAP (combin$C (FUNPOW f) x) [0 ..< y])    by iterating_eqn
   = LENGTH [0 ..< y]                                  by LENGTH_MAP
   = y                                                 by listRangeLHI_LEN
*)
val iterating_length = store_thm(
  "iterating_length",
  ``!f x y. LENGTH (iterating f x y) = y``,
  rw[iterating_eqn, listRangeLHI_LEN]);

(* Theorem: j < y ==> MEM (FUNPOW f j x) (iterating f x y) *)
(* Proof:
       MEM k (iterating f x y)
   <=> MEM k (MAP (combin$C (FUNPOW f) x) [0 ..< y])       by iterating_eqn
   <=> ?t. k = combin$C (FUNPOW f) x t /\ MEM t [0 ..< y]  by MEM_MAP
   <=> ?t. k = FUNPOW f t x /\ 0 <= t /\ t < y             by listRangeLHI_MEM
*)
val iterating_member = store_thm(
  "iterating_member",
  ``!f x y j. j < y ==> MEM (FUNPOW f j x) (iterating f x y)``,
  rw[iterating_eqn, MEM_MAP] >>
  metis_tac[]);

(* Theorem: j < y ==> EL j (iterating f x y) = FUNPOW f j x *)
(* Proof:
   Since j < y = LENGTH (iterating f x y)           by iterating_length
     EL j (iterating f x y)
   = EL j (MAP (combin$C (FUNPOW f) x) [0 ..< y])   by iterating_eqn
   = combin$C (FUNPOW f) x (EL j [0 ..< y])         by EL_MAP
   = combin$C (FUNPOW f) j k                        by listRangeLHI_EL
   = FUNPOW f j x
*)
val iterating_element = store_thm(
  "iterating_element",
  ``!f x y j. j < y ==> EL j (iterating f x y) = FUNPOW f j x``,
  rw[iterating_eqn, iterating_length, EL_MAP, listRangeLHI_EL]);

(* ------------------------------------------------------------------------- *)
(* Numeric Loops with transform and modify                                   *)
(* ------------------------------------------------------------------------- *)

(* Idea:

   From loop2_modify_count_eqn, let n = loop2_count guard modify transform x y.
     loop x y
   = quit (last x) (last y) + SUM (GENLIST (\j. body (FUNPOW transform j x) (FUNPOW modify j y)) n)
   = quit (last x) (last y) + [body x y, body (t x) (m y), body (t (t x)) (m (m y)), ....]    for n terms
  <= quit (last x) (last y) + [body x y, body (t x) y, body (t (t x)) y, .....]    if MONO2 body, FALLING m
  If FALLING t,
  <= quit (last x) (last y) + [body x y, body x y, ....] = c + n * body x y
  If RISING t,
  <= quit (last x) (last y) + [body (last x) y, body (last x) y, ...] = c + n * body (last x) y
  Similar estimates for RISING m
*)

(* ------------------------------------------------------------------------- *)
(* Numeric Loops with RISING transform and FALLING modify                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ FALLING modify /\
      (!x y. loop x y =
             if guard x y then quit x y
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= quit (FUNPOW transform n x) (FUNPOW modify n y) +
                                   n * cover (FUNPOW transform n x) y *)
(* Proof:
   Let f = (\j. body (FUNPOW transform j x) (FUNPOW modify j y)),
       n = loop2_count guard modify transform x y,
       p = FUNPOW transform n x,
       q = FUNPOW modify n y.

   For k < n,
      FUNPOW transform k x <= FUNPOW transform n x   by FUNPOW_LE_RISING, RISING transform
                            = p                      by notation
      FUNPOW modify k y <= FUNPOW modify 0 y         by FUNPOW_LE_FALLING, FALLING modify
                         = y                         by FUNPOW_0
   Thus,
       loop x y
    <= quit p q + SUM (GENLIST f n)                  by loop2_modify_count_exit_le
    <= quit p q + SUM (GENLIST (K (cover p y)) n)    by SUM_LE, EL_GENLIST, FALLING modify, RISING transform
     = quit p q + (cover p y) * n                    by SUM_GENLIST_K
     = quit p q + n * cover p y                      by MULT_COMM
*)
val loop2_rise_fall_count_cover_exit_le = store_thm(
  "loop2_rise_fall_count_cover_exit_le",
  ``!loop guard body quit exit modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ FALLING modify /\
      (!x y. loop x y =
             if guard x y then quit x y
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= quit (FUNPOW transform n x) (FUNPOW modify n y) +
                                   n * cover (FUNPOW transform n x) y``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x y. loop x y =
                      if guard x y then quit x y
                      else body x y + if exit x y then 0 else loop (transform x) (modify y)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop2_modify_count_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `f = \j. body (FUNPOW transform j x) (FUNPOW modify j y)` >>
  qabbrev_tac `n = loop2_count guard modify transform x y` >>
  qabbrev_tac `p = FUNPOW transform n x` >>
  qabbrev_tac `q = FUNPOW modify n y` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover p y)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`, Abbr`p`] >>
  `FUNPOW transform k x <= FUNPOW transform n x` by rw[FUNPOW_LE_RISING] >>
  `FUNPOW modify k y <= FUNPOW modify 0 y` by rw[FUNPOW_LE_FALLING] >>
  `FUNPOW modify 0 y = y` by rw[] >>
  qabbrev_tac `u = FUNPOW transform k x` >>
  qabbrev_tac `v = FUNPOW modify k y` >>
  `body u v <= cover u v` by rw[] >>
  `cover u v <= cover (FUNPOW transform n x) y` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover p y)) n) = cover p y * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Numeric Loops with FALLING transform and FALLING modify                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ FALLING modify /\
      (!x y. loop x y =
             if guard x y then quit x y
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= quit (FUNPOW transform n x) (FUNPOW modify n y) + n * cover x y *)
(* Proof:
   Let f = (\j. body (FUNPOW transform j x) (FUNPOW modify j y)),
       n = loop2_count guard modify transform x y,
       p = FUNPOW transform n x,
       q = FUNPOW modify n y.

   For k < n,
      FUNPOW transform k x <= FUNPOW transform 0 x   by FUNPOW_LE_FALLING, FALLING transform
                            = x                      by FUNPOW_0
      FUNPOW modify k y <= FUNPOW modify 0 y         by FUNPOW_LE_FALLING, FALLING modify
                         = y                         by FUNPOW_0
   Thus,
       loop x y
    <= quit p q + SUM (GENLIST f n)                  by loop2_modify_count_exit_le
    <= quit p q + SUM (GENLIST (K (cover x y)) n)    by SUM_LE, EL_GENLIST, FALLING modify, FALLING transform
     = quit p q + (cover x y) * n                    by SUM_GENLIST_K
     = quit p q + n * cover x y                      by MULT_COMM
*)
val loop2_fall_fall_count_cover_exit_le = store_thm(
  "loop2_fall_fall_count_cover_exit_le",
  ``!loop guard body quit exit modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ FALLING modify /\
      (!x y. loop x y =
             if guard x y then quit x y
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= quit (FUNPOW transform n x) (FUNPOW modify n y) + n * cover x y``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x y. loop x y =
                      if guard x y then quit x y
                      else body x y + if exit x y then 0 else loop (transform x) (modify y)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop2_modify_count_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `f = \j. body (FUNPOW transform j x) (FUNPOW modify j y)` >>
  qabbrev_tac `n = loop2_count guard modify transform x y` >>
  qabbrev_tac `p = FUNPOW transform n x` >>
  qabbrev_tac `q = FUNPOW modify n y` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover x y)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`] >>
  `FUNPOW transform k x <= FUNPOW transform 0 x` by rw[FUNPOW_LE_FALLING] >>
  `FUNPOW modify k y <= FUNPOW modify 0 y` by rw[FUNPOW_LE_FALLING] >>
  `FUNPOW transform 0 x = x` by rw[] >>
  `FUNPOW modify 0 y = y` by rw[] >>
  qabbrev_tac `u = FUNPOW transform k x` >>
  qabbrev_tac `v = FUNPOW modify k y` >>
  `body u v <= cover u v` by rw[] >>
  `cover u v <= cover x y` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover x y)) n) = cover x y * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Numeric Loops with FALLING transform and RISING modify                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ RISING modify /\
      (!x y. loop x y =
             if guard x y then quit x y
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= quit (FUNPOW transform n x) (FUNPOW modify n y) +
                                   n * cover x (FUNPOW modify n y) *)
(* Proof:
   Let f = (\j. body (FUNPOW transform j x) (FUNPOW modify j y)),
       n = loop2_count guard modify transform x y,
       p = FUNPOW transform n x,
       q = FUNPOW modify n y.

   For k < n,
      FUNPOW transform k x <= FUNPOW transform 0 x   by FUNPOW_LE_FALLING, FALLING transform
                            = x                      by FUNPOW_0
      FUNPOW modify k y <= FUNPOW modify n y         by FUNPOW_LE_RISING, RISING modify
                         = q                         by notation
   Thus,
       loop x y
    <= quit p q + SUM (GENLIST f n)                  by loop2_modify_count_exit_le
    <= quit p q + SUM (GENLIST (K (cover x q)) n)    by SUM_LE, EL_GENLIST, RISING modify, FALLING transform
     = quit p q + (cover x q) * n                    by SUM_GENLIST_K
     = quit p q + n * cover x q                      by MULT_COMM
*)
val loop2_fall_rise_count_cover_exit_le = store_thm(
  "loop2_fall_rise_count_cover_exit_le",
  ``!loop guard body quit exit modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ RISING modify /\
      (!x y. loop x y =
             if guard x y then quit x y
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= quit (FUNPOW transform n x) (FUNPOW modify n y) +
                                   n * cover x (FUNPOW modify n y)``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x y. loop x y =
                      if guard x y then quit x y
                      else body x y + if exit x y then 0 else loop (transform x) (modify y)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop2_modify_count_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `f = \j. body (FUNPOW transform j x) (FUNPOW modify j y)` >>
  qabbrev_tac `n = loop2_count guard modify transform x y` >>
  qabbrev_tac `p = FUNPOW transform n x` >>
  qabbrev_tac `q = FUNPOW modify n y` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover x q)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`, Abbr`q`] >>
  `FUNPOW transform k x <= FUNPOW transform 0 x` by rw[FUNPOW_LE_FALLING] >>
  `FUNPOW modify k y <= FUNPOW modify n y` by rw[FUNPOW_LE_RISING] >>
  `FUNPOW transform 0 x = x` by rw[] >>
  qabbrev_tac `u = FUNPOW transform k x` >>
  qabbrev_tac `v = FUNPOW modify k y` >>
  `body u v <= cover u v` by rw[] >>
  `cover u v <= cover x (FUNPOW modify n y)` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover x q)) n) = cover x q * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Numeric Loops with RISING transform and RISING modify                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ RISING modify /\
      (!x y. loop x y =
             if guard x y then quit x y
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= quit (FUNPOW transform n x) (FUNPOW modify n y) +
                                   n * cover (FUNPOW transform n x) (FUNPOW modify n y) *)
(* Proof:
   Let f = (\j. body (FUNPOW transform j x) (FUNPOW modify j y)),
       n = loop2_count guard modify transform x y,
       p = FUNPOW transform n x,
       q = FUNPOW modify n y.

   For k < n,
      FUNPOW transform k x <= FUNPOW transform n x   by FUNPOW_LE_RISING, RISING transform
                            = p                      by notation
      FUNPOW modify k y <= FUNPOW modify n y         by FUNPOW_LE_RISING, RISING modify
                         = q                         by notation
   Thus,
       loop x y
    <= quit p q + SUM (GENLIST f n)                  by loop2_modify_count_exit_le
    <= quit p q + SUM (GENLIST (K (cover p q)) n)    by SUM_LE, EL_GENLIST, RISING modify, RISING transform
     = quit p q + (cover p q) * n                    by SUM_GENLIST_K
     = quit p q + n * cover p q                      by MULT_COMM
*)
val loop2_rise_rise_count_cover_exit_le = store_thm(
  "loop2_rise_rise_count_cover_exit_le",
  ``!loop guard body quit exit modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ RISING modify /\
      (!x y. loop x y =
             if guard x y then quit x y
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= quit (FUNPOW transform n x) (FUNPOW modify n y) +
                                   n * cover (FUNPOW transform n x) (FUNPOW modify n y)``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x y. loop x y =
                      if guard x y then quit x y
                      else body x y + if exit x y then 0 else loop (transform x) (modify y)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop2_modify_count_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `f = \j. body (FUNPOW transform j x) (FUNPOW modify j y)` >>
  qabbrev_tac `n = loop2_count guard modify transform x y` >>
  qabbrev_tac `p = FUNPOW transform n x` >>
  qabbrev_tac `q = FUNPOW modify n y` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover p q)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`, Abbr`p`, Abbr`q`] >>
  `FUNPOW transform k x <= FUNPOW transform n x` by rw[FUNPOW_LE_RISING] >>
  `FUNPOW modify k y <= FUNPOW modify n y` by rw[FUNPOW_LE_RISING] >>
  qabbrev_tac `u = FUNPOW transform k x` >>
  qabbrev_tac `v = FUNPOW modify k y` >>
  `body u v <= cover u v` by rw[] >>
  `cover u v <= cover (FUNPOW transform n x) (FUNPOW modify n y)` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover p q)) n) = cover p q * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* General Theory of Recurrence with 3 arguments                             *)
(* ------------------------------------------------------------------------- *)

(*
> loop_count_def |> DISCH_ALL |> INST_TYPE [alpha |-> ``:'a # 'b # 'c``]
  |> SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD]
  |> Q.INST [`guard` |-> `(\(x,y,z). gd x y z)`, `modify` |-> `(\(x,y,z). (c x, t y, m z))`]
  |> SIMP_RULE (srw_ss()) [];
val it = |- WF R ==> (!p_1 p_1' p_2. ~gd p_1 p_1' p_2 ==> R (c p_1,t p_1',m p_2) (p_1,p_1',p_2)) ==>
      !p_1 p_1' p_2. loop_count (\(x,y,z). gd x y z) (\(x,y,z). (c x,t y,m z)) (p_1,p_1',p_2) =
          if gd p_1 p_1' p_2 then 0
          else SUC (loop_count (\(x,y,z). gd x y z) (\(x,y,z). (c x,t y,m z)) (c p_1,t p_1',m p_2)): thm
*)

(* Define loop_count for 3 arguments *)
val loop3_count_def = Define`
    loop3_count guard modify transform convert x y z =
       loop_count (\(x,y,z). guard x y z) (\(x,y,z). (convert x, transform y, modify z)) (x, y, z)
`;

(* Theorem: WF R /\ (!x y z. ~guard x y z ==> R (convert x, transform y,modify z) (x,y,z)) ==>
      !x y z. loop3_count guard modify transform convert x y z =
              if guard x y z then 0
              else SUC (loop3_count guard modify transform convert (convert x) (transform y) (modify z)) *)
(* Proof: by loop_count_thm, loop3_count_def *)
val loop3_count_thm = store_thm(
  "loop3_count_thm",
  ``!convert transform modify guard R.
      WF R /\ (!x y z. ~guard x y z ==> R (convert x, transform y,modify z) (x,y,z)) ==>
      !x y z. loop3_count guard modify transform convert x y z =
              if guard x y z then 0
              else SUC (loop3_count guard modify transform convert (convert x) (transform y) (modify z))``,
  rw[loop3_count_def] >>
  imp_res_tac loop_count_thm >>
  fs[Once pairTheory.FORALL_PROD]);

(* Obtain similar theorems. *)
val loop3_count_0 = store_thm(
  "loop3_count_0",
  ``!convert transform modify guard R.
      WF R /\ (!x y z. ~guard x y z ==> R (convert x, transform y,modify z) (x,y,z)) ==>
      !x y z. guard x y z ==> (loop3_count guard modify transform convert x y z = 0)``,
  rw[loop3_count_def] >>
  imp_res_tac loop_count_0 >>
  fs[Once pairTheory.FORALL_PROD]);

val loop3_count_suc = store_thm(
  "loop3_count_suc",
  ``!convert transform modify guard R.
      WF R /\ (!x y z. ~guard x y z ==> R (convert x, transform y,modify z) (x,y,z)) ==>
      !x y z. ~guard x y z ==> (loop3_count guard modify transform convert x y z =
            SUC (loop3_count guard modify transform convert (convert x) (transform y) (modify z)))``,
  rw[loop3_count_def] >>
  imp_res_tac loop_count_suc >>
  fs[Once pairTheory.FORALL_PROD]);

(* Theorem: WF R /\ (!x y z. ~guard x y z ==> R (convert x, transform y,modify z) (x,y,z)) ==>
      !x y. guard (FUNPOW convert (loop3_count guard modify transform convert x y z) x)
                  (FUNPOW transform (loop3_count guard modify transform convert x y z) y)
                  (FUNPOW modify (loop3_count guard modify transform convert x y z) z) *)
(* Proof: by loop_count_iterating, loop3_count_def. *)
val loop3_count_iterating = store_thm(
  "loop3_count_iterating",
  ``!convert transform modify guard R.
      WF R /\ (!x y z. ~guard x y z ==> R (convert x, transform y,modify z) (x,y,z)) ==>
      !x y z. guard (FUNPOW convert (loop3_count guard modify transform convert x y z) x)
                    (FUNPOW transform (loop3_count guard modify transform convert x y z) y)
                    (FUNPOW modify (loop3_count guard modify transform convert x y z) z)``,
  rpt strip_tac >>
  assume_tac (loop_count_iterating
   |> SPEC_ALL |> INST_TYPE [``:'a`` |-> ``:'a # 'b # 'c``]
   |> SIMP_RULE bool_ss [pairTheory.FORALL_PROD]
   |> Q.INST [`loop` |-> `(\(x,y,z). lp x y z)`, `guard` |-> `(\(x,y,z). gd x y z)`,
              `quit` |-> `(\(x,y,z). qt x y z)`, `body` |-> `(\(x,y,z). b x y z)`,
              `modify` |-> `(\(x,y,z). (c x, t y, m z))`]
   |> SIMP_RULE bool_ss [FUNPOW_TRIPLE, GSYM loop3_count_def]
   |> Q.INST [`lp` |-> `loop`, `gd` |-> `guard`, `qt` |-> `quit`, `b` |-> `body`,
              `c` |-> `convert`, `t` |-> `transform`, `m` |-> `modify`]
   |> PairRules.PBETA_RULE) >>
  metis_tac[]);

(* Theorem:  WF R /\ (!x y z. ~guard x y z ==> R (convert x, transform y,modify z) (x,y,z)) /\
        (!x y z. loop x y z =
                 if guard x y z then quit x y z
                 else body x y z + loop (convert x) (transform y) (modify z)) ==>
         !x y z. loop x y z = quit (FUNPOW convert (loop3_count guard modify transform convert x y z) x)
                                   (FUNPOW transform (loop3_count guard modify transform convert x y z) y)
                                   (FUNPOW modify (loop3_count guard modify transform convert x y z) z) +
               SUM (GENLIST (\j. body (FUNPOW convert j x) (FUNPOW transform j y) (FUNPOW modify j z))
                                      (loop3_count guard modify transform convert x y z)) *)
(* Proof: by loop_modify_count_eqn, loop3_count_def *)
val loop3_modify_count_eqn = store_thm(
  "loop3_modify_count_eqn",
  ``!loop guard body quit modify transform convert R.
        WF R /\ (!x y z. ~guard x y z ==> R (convert x, transform y,modify z) (x,y,z)) /\
        (!x y z. loop x y z =
                 if guard x y z then quit x y z
                 else body x y z + loop (convert x) (transform y) (modify z)) ==>
         !x y z. loop x y z = quit (FUNPOW convert (loop3_count guard modify transform convert x y z) x)
                                   (FUNPOW transform (loop3_count guard modify transform convert x y z) y)
                                   (FUNPOW modify (loop3_count guard modify transform convert x y z) z) +
               SUM (GENLIST (\j. body (FUNPOW convert j x) (FUNPOW transform j y) (FUNPOW modify j z))
                                      (loop3_count guard modify transform convert x y z))``,
  rpt strip_tac >>
  assume_tac (loop_modify_count_eqn
   |> SPEC_ALL |> INST_TYPE [``:'a`` |-> ``:'a # 'b # 'c``]
   |> SIMP_RULE bool_ss [pairTheory.FORALL_PROD]
   |> Q.INST [`loop` |-> `(\(x,y,z). lp x y z)`, `guard` |-> `(\(x,y,z). gd x y z)`,
              `quit` |-> `(\(x,y,z). qt x y z)`, `body` |-> `(\(x,y,z). b x y z)`,
              `modify` |-> `(\(x,y,z). (c x, t y, m z))`]
   |> SIMP_RULE bool_ss [FUNPOW_TRIPLE, GSYM loop3_count_def]
   |> Q.INST [`lp` |-> `loop`, `gd` |-> `guard`, `qt` |-> `quit`, `b` |-> `body`,
              `c` |-> `convert`, `t` |-> `transform`, `m` |-> `modify`]
   |> PairRules.PBETA_RULE) >>
  metis_tac[]);

(* Theorem: WF R /\ (!x y z. ~guard x y z ==> R (convert x, transform y,modify z) (x,y,z)) /\
    (!x y z. loop x y z =
             if guard x y z then quit x y z
             else body x y z + if exit x y z then 0 else loop (convert x) (transform y) (modify z)) ==>
     !x y z. loop x y z <= quit (FUNPOW convert (loop3_count guard modify transform convert x y z) x)
                                (FUNPOW transform (loop3_count guard modify transform convert x y z) y)
                                (FUNPOW modify (loop3_count guard modify transform convert x y z) z) +
               SUM (GENLIST (\j. body (FUNPOW convert j x) (FUNPOW transform j y) (FUNPOW modify j z))
                                      (loop3_count guard modify transform convert x y z)) *)
(* Proof: by loop_modify_count_exit_le, loop3_count_def. *)
val loop3_modify_count_exit_le = store_thm(
  "loop3_modify_count_exit_le",
  ``!loop guard body quit exit modify transform convert R.
    WF R /\ (!x y z. ~guard x y z ==> R (convert x, transform y,modify z) (x,y,z)) /\
    (!x y z. loop x y z =
             if guard x y z then quit x y z
             else body x y z + if exit x y z then 0 else loop (convert x) (transform y) (modify z)) ==>
     !x y z. loop x y z <= quit (FUNPOW convert (loop3_count guard modify transform convert x y z) x)
                                (FUNPOW transform (loop3_count guard modify transform convert x y z) y)
                                (FUNPOW modify (loop3_count guard modify transform convert x y z) z) +
               SUM (GENLIST (\j. body (FUNPOW convert j x) (FUNPOW transform j y) (FUNPOW modify j z))
                                      (loop3_count guard modify transform convert x y z))``,
  rpt strip_tac >>
  assume_tac (loop_modify_count_exit_le
   |> SPEC_ALL |> INST_TYPE [``:'a`` |-> ``:'a # 'b # 'c``]
   |> SIMP_RULE bool_ss [pairTheory.FORALL_PROD]
   |> Q.INST [`loop` |-> `(\(x,y,z). lp x y z)`, `guard` |-> `(\(x,y,z). gd x y z)`,
              `quit` |-> `(\(x,y,z). qt x y z)`, `body` |-> `(\(x,y,z). b x y z)`,
              `modify` |-> `(\(x,y,z). (c x, t y, m z))`,  `exit` |-> `(\(x,y,z). et x y z)`]
   |> SIMP_RULE bool_ss [FUNPOW_TRIPLE, GSYM loop3_count_def]
   |> Q.INST [`lp` |-> `loop`, `gd` |-> `guard`, `qt` |-> `quit`, `b` |-> `body`,
               `et` |-> `exit`, `c` |-> `convert`, `t` |-> `transform`, `m` |-> `modify`]
   |> PairRules.PBETA_RULE) >>
  qabbrev_tac `foo1 = !x y z. ~guard x y z ==> R (convert x,transform y,modify z) (x,y,z)` >>
  qabbrev_tac `foo2 = !x y z. loop x y z = if guard x y z then quit x y z else body x y z + if exit x y z then 0 else loop (convert x) (transform y) (modify z)` >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* Original investigation, some with quit = constant, name has _quitc_       *)
(* ------------------------------------------------------------------------- *)

(* Define a loop argument list to capture the process of recurrence. *)
(* Use a schema to figure out the hypothesis. *)
val loop_arg_def = TotalDefn.DefineSchema`
    loop_arg (x:'a) =
        if guard x then [] else x :: loop_arg (modify x)
`;
(*
val loop_arg_def =
    [..] |- !x. loop_arg guard modify x =
          if guard x then [] else x::loop_arg guard modify (modify x): thm
to see the [..], which is hypothesis,
> hyp loop_arg_def;
val it = [``!x. ~guard x ==> R (modify x) x``, ``WF R``]: term list

> loop_arg_def |> hyp;
val it = [``!x. ~guard x ==> R (modify x) x``, ``WF R``]: term list

``!(x :'a). ~(guard :'a -> bool) x ==> (R :'a -> 'a -> bool) ((modify :'a -> 'a) x) x``,
``WF (R :'a -> 'a -> bool)``

> loop_arg_def |> DISCH_ALL |> GEN_ALL;
val it = |- !modify guard R. WF R ==> (!x. ~guard x ==> R (modify x) x) ==>
  !x. loop_arg guard modify x = if guard x then [] else x::loop_arg guard modify (modify x): thm
*)

(* Obtain theorem from loop_count definition *)
val loop_arg_thm = save_thm("loop_arg_thm",
    loop_arg_def |> DISCH_ALL |> SIMP_RULE bool_ss [AND_IMP_INTRO] |> GEN_ALL);
(* val loop_arg_thm =
   |- !modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
          !x. loop_arg guard modify x =
              if guard x then [] else x::loop_arg guard modify (modify x): thm
*)

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
             !x. guard x ==> (loop_arg guard modify x = []) *)
(* Proof: by loop_arg_def *)
val loop_arg_nil = store_thm(
  "loop_arg_nil",
  ``!modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
   !x. guard x ==> (loop_arg guard modify x = [])``,
  rpt strip_tac >>
  rw[Once loop_arg_def]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
             !x. ~guard x ==> (loop_arg guard modify x = x :: loop_arg guard modify (modify x)) *)
(* Proof: by loop_arg_def *)
val loop_arg_cons = store_thm(
  "loop_arg_cons",
  ``!modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
   !x. ~guard x ==> (loop_arg guard modify x = x :: loop_arg guard modify (modify x))``,
  rpt strip_tac >>
  rw[Once loop_arg_def]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
             !x. LENGTH (loop_arg guard modify x) = loop_count guard modify x *)
(* Proof:
   By induction from loop_arg_def.
   If guard x,
        LENGTH (loop_arg guard modify x)
      = LENGTH []                    by loop_arg_nil, guard x.
      = 0                            by LENGTH
      = loop_count guard modify x    by loop_count_0
   If ~guard x,
        LENGTH (loop_arg guard modify x)
      = LENGTH (x:: loop_arg guard modify (modify x))     by loop_arg_cons, ~guard x.
      = SUC (LENGTH loop_arg guard modify (modify x))     by LENGTH
      = SUC (loop_count guard modify (modify x))          by induction hypothesis
      = loop_count guard modify x                         by loop_count_suc
*)
val loop_arg_length = store_thm(
  "loop_arg_length",
  ``!modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
                    !x. LENGTH (loop_arg guard modify x) = loop_count guard modify x``,
  ntac 4 strip_tac >>
  ho_match_mp_tac (theorem "loop_arg_ind") >>
  rpt strip_tac >>
  Cases_on `guard x` >-
  metis_tac[loop_arg_nil, loop_count_0, LENGTH] >>
  metis_tac[loop_arg_cons, loop_count_suc, LENGTH]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
            !x. loop_arg guard modify x = GENLIST (\j. FUNPOW modify j x) (loop_count guard modify x) *)
(* Proof:
   By induction from loop_arg_def.
   If guard x,
      LHS = loop_arg guard modify x = []        by loop_arg_nil, guard x
      RHS = GENLIST (\j. FUNPOW modify j x) (loop_count guard modify x)
          = GENLIST (\j. FUNPOW modify j x) 0   by loop_count_0, guard x
          = [] = LHS                            by GENLIST_0
   If ~guard x,
      Let f = \j. FUNPOW modify j x, n = loop_count guard modify (modify x).
      Then f o SUC = \j. FUNPOW modify j (modify x)       by FUN_EQ_THM
       and f 0 = x                                        by notation
         loop_arg guard modify x
       = x::loop_arg guard modify (modify x)              by loop_arg_cons
       = x:: GENLIST (\j. FUNPOW modify j (modify x)) n   by induction hypothesis
       = f 0:: GENLIST (f o SUC) n                        by above
       = GENLIST f (SUC n)                                by GENLIST_CONS
       = GENLIST f (loop_count guard modify x)            by loop_count_suc
*)
val loop_arg_eqn = store_thm(
  "loop_arg_eqn",
  ``!modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
   !x. loop_arg guard modify x = GENLIST (\j. FUNPOW modify j x) (loop_count guard modify x)``,
  ntac 4 strip_tac >>
  ho_match_mp_tac (theorem "loop_arg_ind") >>
  rpt strip_tac >>
  Cases_on `guard x` >-
  metis_tac[loop_arg_nil, loop_count_0, GENLIST_0] >>
  qabbrev_tac `f = \j. FUNPOW modify j x` >>
  qabbrev_tac `n = loop_count guard modify (modify x)` >>
  `f o SUC = \j. FUNPOW modify j (modify x)` by rw[FUNPOW, FUN_EQ_THM, Abbr`f`] >>
  `f 0 = x` by rw[Abbr`f`] >>
  `loop_arg guard modify x = x::loop_arg guard modify (modify x)` by metis_tac[loop_arg_cons] >>
  `_ = f 0:: GENLIST (f o SUC) n` by rw[Abbr`n`] >>
  `SUC n = loop_count guard modify x` by metis_tac[loop_count_suc] >>
  rw[GSYM GENLIST_CONS, Abbr`n`]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
             !x k. k < loop_count guard modify x ==>
               (EL k (loop_arg guard modify x) = FUNPOW modify k x) *)
(* Proof:
   Let f = (\j. FUNPOW modify j x), ls = loop_arg guard modify x.
   Note LENGTH ls
      = loop_count guard modify x     by loop_arg_length
     EL k ls
   = EL k (GENLIST f (LENGTH ls))     by loop_arg_eqn
   = f k                              by EL_GENLIST, k < LENGTH ls
   = FUNPOW modify k x                by notation
*)
val loop_arg_element = store_thm(
  "loop_arg_element",
  ``!modify guard R. WF R /\ (!x. ~guard x ==> R (modify x) x) ==>
     !x k. k < loop_count guard modify x ==> (EL k (loop_arg guard modify x) = FUNPOW modify k x)``,
  rpt strip_tac >>
  imp_res_tac loop_arg_eqn >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `f = \j. FUNPOW modify j x` >>
  qabbrev_tac `ls = loop_arg guard modify x` >>
  `LENGTH ls = loop_count guard modify x` by metis_tac[loop_arg_length] >>
  fs[EL_GENLIST, Abbr`ls`, Abbr`f`]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\
            (!x y. R x y ==> cover x <= cover y) ==>
            !x. SUM (MAP cover (loop_arg guard modify x)) <=
                SUM (MAP (K (cover x)) (loop_arg guard modify x)) *)
(* Proof:
   By induction from loop_arg_def.
   Let ls = loop_arg guard modify x,
   the goal is: SUM (MAP cover ls) <= SUM (MAP (K (cover x)) ls)

   If guard x,
      Then ls = []                      by loop_arg_nil
      LHS = SUM (MAP cover [])
          = SUM []                      by MAP
          = SUM (MAP (K (cover x)) [])  by MAP
          = RHS
   If ~guard x,
      Then ls = x::loop_arg guard modify (modify x)    by loop_arg_cons
       and R (modify x) x                              by given
        so cover (modify x) <= cover x                 by cover property
           SUM (MAP cover ls)
         = SUM (MAP cover (x::loop_arg guard modify (modify x)))        by ls above
         = cover x + SUM (MAP cover (loop_arg guard modify (modify x))) by SUM, MAP
        <= cover x + SUM (MAP (K (cover (modify x))) (loop_arg guard modify (modify x)))   by induction hypothesis
        <= cover x + SUM (MAP (K (cover x)) (loop_arg guard modify (modify x))             by SUM_MAP_K_LE
         = SUM (MAP (K (cover x) x::(loop_arg guard modify (modify x))))   by SUM, MAP
         = SUM (MAP (K (cover x) ls))                                      by ls above
*)
val loop_arg_cover_sum = store_thm(
  "loop_arg_cover_sum",
  ``!modify guard R cover.
         WF R /\ (!x. ~guard x ==> R (modify x) x) /\
         (!x y. R x y ==> cover x <= cover y) ==>
          !x. SUM (MAP cover (loop_arg guard modify x)) <=
              SUM (MAP (K (cover x)) (loop_arg guard modify x))``,
  ntac 5 strip_tac >>
  ho_match_mp_tac (theorem "loop_arg_ind") >>
  rw[] >>
  qabbrev_tac `ls = loop_arg guard modify x` >>
  Cases_on `guard x` >| [
    `ls = []` by metis_tac[loop_arg_nil] >>
    rw[],
    qabbrev_tac `t = loop_arg guard modify (modify x)` >>
    `ls = x::t` by metis_tac[loop_arg_cons] >>
    `cover (modify x) <= cover x` by rw[] >>
    `SUM (MAP cover ls) = cover x + SUM (MAP cover t)` by rw[] >>
    `SUM (MAP cover t) <= SUM (MAP (K (cover (modify x))) t)` by rw[Abbr`t`] >>
    `SUM (MAP (K (cover (modify x))) t) <= SUM (MAP (K (cover x)) t)` by rw[SUM_MAP_K_LE] >>
    `cover x + SUM (MAP (K (cover x)) t) = SUM (MAP (K (cover x)) ls)` by rw[] >>
    decide_tac
  ]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\
            (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
             !x. loop x = c + SUM (MAP body (loop_arg guard modify x)) *)
(* Proof:
   By induction from loop_arg_def.
   If guard x,
      LHS = loop x = c               by loop property, guard x.
      RHS = c + SUM (MAP body (loop_arg guard modify x))
          = c + SUM (MAP body [])    by loop_arg_nil, guard x.
          = c + 0                    by MAP, SUM
          = c = LHS                  by arithmetic
   If ~guard x,
        loop x
      = body x + loop (modify x)        by loop property, ~guard x.
      = body x + (c + SUM (MAP body (loop_arg guard modify (modify x))))
                                        by induction hypothesis
      = c + (body x + SUM (MAP body (loop_arg guard modify (modify x))))
                                        by arithmetic
      = c + SUM (MAP body (x :: (loop_arg guard modify (modify x))))   by MAP, SUM
      = c + SUM (MAP body (loop_arg guard modify x))    by loop_arg_cons, ~guard x
*)
val loop_modify_count_by_sum = store_thm(
  "loop_modify_count_by_sum",
  ``!loop guard body c modify R.
        WF R /\ (!x. ~guard x ==> R (modify x) x) /\
        (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
         !x. loop x = c + SUM (MAP body (loop_arg guard modify x))``,
  ntac 7 strip_tac >>
  ho_match_mp_tac (theorem "loop_arg_ind") >>
  rpt strip_tac >>
  Cases_on `guard x` >| [
    `loop x = c` by metis_tac[] >>
    `loop_arg guard modify x = []` by metis_tac[loop_arg_nil] >>
    metis_tac[SUM, MAP, ADD_0],
    `loop x = body x + loop (modify x)` by metis_tac[] >>
    `_ = c + SUM (MAP body (x :: (loop_arg guard modify (modify x))))` by rw[] >>
    `_ = c + SUM (MAP body (loop_arg guard modify x))` by metis_tac[loop_arg_cons] >>
    decide_tac
  ]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\
            (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
             !x. loop x <= c + SUM (MAP body (loop_arg guard modify x)) *)
(* Proof:
   By induction from loop_arg_def.
   If guard x,
      LHS = loop x = c               by loop property, guard x.
      RHS = c + SUM (MAP body (loop_arg guard modify x))
          = c + SUM (MAP body [])    by loop_arg_nil, guard x.
          = c + 0                    by MAP, SUM
          = c >= LHS                 by LESS_EQ_REFL
   If ~guard x,
         loop x
      <= body x + loop (modify x)       by loop property, ~guard x, cases on exit x.
      <= body x + (c + SUM (MAP body (loop_arg guard modify (modify x))))
                                        by induction hypothesis
      = c + (body x + SUM (MAP body (loop_arg guard modify (modify x))))
                                        by arithmetic
      = c + SUM (MAP body (x :: (loop_arg guard modify (modify x))))   by MAP, SUM
      = c + SUM (MAP body (loop_arg guard modify x))    by loop_arg_cons, ~guard x
*)
val loop_modify_count_exit_by_sum = store_thm(
  "loop_modify_count_exit_by_sum",
  ``!loop guard body c exit modify R.
        WF R /\ (!x. ~guard x ==> R (modify x) x) /\
        (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
         !x. loop x <= c + SUM (MAP body (loop_arg guard modify x))``,
  ntac 8 strip_tac >>
  ho_match_mp_tac (theorem "loop_arg_ind") >>
  rpt strip_tac >>
  Cases_on `guard x` >| [
    `loop x = c` by metis_tac[] >>
    `loop_arg guard modify x = []` by metis_tac[loop_arg_nil] >>
    metis_tac[SUM, MAP, ADD_0, LESS_EQ_REFL],
    `loop x <= body x + loop (modify x)` by
  (Cases_on `exit x` >| [
      `loop x = body x` by metis_tac[ADD_0] >>
      decide_tac,
      `loop x = body x + loop (modify x)` by metis_tac[] >>
      decide_tac
    ]) >>
    `body x + loop (modify x) <=
    body x + (c + SUM (MAP body (loop_arg guard modify (modify x))))` by metis_tac[ADD_MONO_LESS_EQ] >>
    `body x + (c + SUM (MAP body (loop_arg guard modify (modify x)))) =
    c + SUM (MAP body (x :: (loop_arg guard modify (modify x))))` by rw[] >>
    `_ = c + SUM (MAP body (loop_arg guard modify x))` by metis_tac[loop_arg_cons] >>
    decide_tac
  ]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\
            (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
             !x. loop x = c + SUM (GENLIST (\j. body (FUNPOW modify j x)) (loop_count guard modify x)) *)
(* Proof:
   Let f = (\j. FUNPOW modify j x),
       n = loop_count guard modify x.
      loop x
    = c + SUM (MAP body (loop_arg guard modify x))  by loop_modify_count_by_sum
    = c + SUM (MAP body (GENLIST f n))              by loop_arg_eqn
    = c + SUM (GENLIST (body o f) n)                by MAP_GENLIST
    = c + SUM (GENLIST (\j. body (FUNPOW modify j x)) (loop_count guard modify x))
*)
val loop_modify_count_quitc_eqn = store_thm(
  "loop_modify_count_quitc_eqn",
  ``!loop guard body c modify R.
        WF R /\ (!x. ~guard x ==> R (modify x) x) /\
        (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
         !x. loop x = c + SUM (GENLIST (\j. body (FUNPOW modify j x)) (loop_count guard modify x))``,
  rpt strip_tac >>
  imp_res_tac loop_modify_count_by_sum >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  imp_res_tac loop_arg_eqn >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `ls = loop_arg guard modify x` >>
  qabbrev_tac `n = loop_count guard modify x` >>
  qabbrev_tac `f = \j. FUNPOW modify j x` >>
  qabbrev_tac `g = \j. body (FUNPOW modify j x)` >>
  `g = body o f` by rw[FUN_EQ_THM, Abbr`g`, Abbr`f`] >>
  metis_tac[MAP_GENLIST]);

(* Note: this is the solution of the recurrence:

   Given: !x. loop x = if guard x then c else body x + loop (modify x)
   Then:  loop x = c + SUM [body x, body (modify x), body (modify (modify x)), .....]
                       for n terms, where n = loop_count guard modify x
*)

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\
            (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
             !x. loop x <= c + SUM (GENLIST (\j. body (FUNPOW modify j x)) (loop_count guard modify x)) *)
(* Proof:
   Let f = (\j. FUNPOW modify j x),
       n = loop_count guard modify x.
       loop x
    <= c + SUM (MAP body (loop_arg guard modify x))  by loop_modify_count_exit_by_sum
     = c + SUM (MAP body (GENLIST f n))              by loop_arg_eqn
     = c + SUM (GENLIST (body o f) n)                by MAP_GENLIST
     = c + SUM (GENLIST (\j. body (FUNPOW modify j x)) (loop_count guard modify x))
*)
val loop_modify_count_quitc_exit_le = store_thm(
  "loop_modify_count_quitc_exit_le",
  ``!loop guard body c exit modify R.
        WF R /\ (!x. ~guard x ==> R (modify x) x) /\
        (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
         !x. loop x <= c + SUM (GENLIST (\j. body (FUNPOW modify j x)) (loop_count guard modify x))``,
  rpt strip_tac >>
  imp_res_tac loop_modify_count_exit_by_sum >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  imp_res_tac loop_arg_eqn >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `ls = loop_arg guard modify x` >>
  qabbrev_tac `n = loop_count guard modify x` >>
  qabbrev_tac `f = \j. FUNPOW modify j x` >>
  qabbrev_tac `g = \j. body (FUNPOW modify j x)` >>
  `g = body o f` by rw[FUN_EQ_THM, Abbr`g`, Abbr`f`] >>
  metis_tac[MAP_GENLIST]);


(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\
            (!x. body x <= cover x) /\ (!x y. R x y ==> cover x <= cover y) /\
            (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
             !x. loop x <= c + cover x * loop_count guard modify x *)
(* Proof:
   Let ls = loop_arg guard modify x.
       loop x
    <= c + SUM (MAP body ls)                     by loop_modify_count_exit_by_sum
    <= c + SUM (MAP cover ls)                    by SUM_LE, loop_arg_length, EL_MAP, body and cover
    <= c + SUM (MAP (K (cover x)) ls)            by loop_arg_cover_sum, cover property
     = (cover x) * LENGTH ls                     by SUM_MAP_K
     = (cover x) * (loop_count guard modify x)   by loop_arg_length
*)
val loop_modify_count_cover_exit_upper = store_thm(
  "loop_modify_count_cover_exit_upper",
  ``!loop guard body c cover exit modify R.
        WF R /\ (!x. ~guard x ==> R (modify x) x) /\
        (!x. body x <= cover x) /\ (!x y. R x y ==> cover x <= cover y) /\
        (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
         !x. loop x <= c + cover x * loop_count guard modify x``,
  rpt strip_tac >>
  qabbrev_tac `ls = loop_arg guard modify x` >>
  `loop x <= c + SUM (MAP body ls)` by metis_tac[loop_modify_count_exit_by_sum] >>
  `SUM (MAP body ls) <= SUM (MAP cover ls)` by
  (irule SUM_LE >>
  rw[loop_arg_length, EL_MAP]) >>
  `SUM (MAP cover ls) <= SUM (MAP (K (cover x)) ls)` by metis_tac[loop_arg_cover_sum] >>
  `SUM (MAP (K (cover x)) ls) = (cover x) * LENGTH ls` by rw[SUM_MAP_K] >>
  `_ = (cover x) * (loop_count guard modify x)` by metis_tac[loop_arg_length] >>
  decide_tac);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\
            (!x y. R x y ==> body x <= body y) /\
            (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
             !x. loop x <= c + body x * loop_count guard modify x *)
(* Proof: by loop_modify_count_cover_exit_upper with cover = body. *)
val loop_modify_count_exit_upper = store_thm(
  "loop_modify_count_exit_upper",
  ``!loop guard body c exit modify R.
        WF R /\ (!x. ~guard x ==> R (modify x) x) /\
        (!x y. R x y ==> body x <= body y) /\
        (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
         !x. loop x <= c + body x * loop_count guard modify x``,
  rpt strip_tac >>
  assume_tac loop_modify_count_cover_exit_upper >>
  last_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `body`, `exit`, `modify`, `R`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\
            (!x. body x <= cover x) /\ (!x y. R x y ==> cover x <= cover y) /\
            (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
             !x. loop x <= c + cover x * loop_count guard modify x *)
(* Proof: by loop_modify_count_cover_exit_upper with exit = K F. *)
val loop_modify_count_cover_upper = store_thm(
  "loop_modify_count_cover_upper",
  ``!loop guard body c cover modify R.
        WF R /\ (!x. ~guard x ==> R (modify x) x) /\
        (!x. body x <= cover x) /\ (!x y. R x y ==> cover x <= cover y) /\
        (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
         !x. loop x <= c + cover x * loop_count guard modify x``,
  rpt strip_tac >>
  qabbrev_tac `exit = (\x:'a. F)` >>
  assume_tac loop_modify_count_cover_exit_upper >>
  last_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `cover`, `exit`, `modify`, `R`] strip_assume_tac) >>
  metis_tac[]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\
            (!x y. R x y ==> body x <= body y) /\
            (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
             !x. loop x <= c + body x * loop_count guard modify x *)
(* Proof: by loop_modify_count_cover_upper with body = cover. *)
val loop_modify_count_upper = store_thm(
  "loop_modify_count_upper",
  ``!loop guard body c modify R.
        WF R /\ (!x. ~guard x ==> R (modify x) x) /\
        (!x y. R x y ==> body x <= body y) /\
        (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
         !x. loop x <= c + body x * loop_count guard modify x``,
  rpt strip_tac >>
  assume_tac loop_modify_count_cover_upper >>
  last_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `body`, `modify`, `R`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)
(* General Theory of Recurrence with 2 arguments                             *)
(* ------------------------------------------------------------------------- *)

(*
> loop_count_def |> DISCH_ALL |> INST_TYPE [alpha |-> ``:'a # 'b``]
  |> SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD]
  |> Q.INST [`guard` |-> `(\(x,y). gd x y)`, `modify` |-> `(\(x,y). (t x, m y))`]
  |> SIMP_RULE (srw_ss()) [];
val it = |- WF R ==> (!p_1 p_2. ~gd p_1 p_2 ==> R (t p_1,m p_2) (p_1,p_2)) ==>
      !p_1 p_2. loop_count (\(x,y). gd x y) (\(x,y). (t x,m y)) (p_1,p_2) =
          if gd p_1 p_2 then 0 else
          SUC (loop_count (\(x,y). gd x y) (\(x,y). (t x,m y)) (t p_1,m p_2)): thm
> loop_arg_def |> DISCH_ALL |> INST_TYPE [alpha |-> ``:'a # 'b``]
  |> SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD]
  |> Q.INST [`guard` |-> `(\(x,y). gd x y)`, `modify` |-> `(\(x,y). (t x, m y))`]
  |> SIMP_RULE (srw_ss()) [];
val it = |- WF R ==> (!p_1 p_2. ~gd p_1 p_2 ==> R (t p_1,m p_2) (p_1,p_2)) ==>
      !p_1 p_2. loop_arg (\(x,y). gd x y) (\(x,y). (t x,m y)) (p_1,p_2) =
          if gd p_1 p_2 then [] else
            (p_1,p_2):: loop_arg (\(x,y). gd x y) (\(x,y). (t x,m y)) (t p_1,m p_2): thm
*)

(* Define loop_count for 2 arguments *)

(* Define loop_arg for 2 arguments *)
val loop2_arg_def = Define`
    loop2_arg guard modify transform x y =
       loop_arg (\(x,y). guard x y) (\(x,y). (transform x, modify y)) (x, y)
`;

(* Obtain theorem by transform:

val loop2_count_thm = save_thm("loop2_count_thm",
    loop_count_thm |> SPEC_ALL |> INST_TYPE [alpha |-> ``:'a # 'b``]
                 |> SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD]
                 |> Q.INST [`guard` |-> `(\(x,y). gd x y)`, `modify` |-> `(\(x,y). (t x, m y))`]
                 |> SIMP_RULE (srw_ss()) [GSYM loop2_count_def] |> GEN_ALL);

val loop2_count_thm =
   |- !t m gd R. WF R /\ (!p_1 p_2. ~gd p_1 p_2 ==> R (t p_1,m p_2) (p_1,p_2)) ==>
          !p_1 p_2. loop2_count gd m t p_1 p_2 =
              if gd p_1 p_2 then 0 else SUC (loop2_count gd m t (t p_1) (m p_2)): thm

loop_count_0 |> SPEC_ALL |> INST_TYPE [alpha |-> ``:'a # 'b``]
                 |> SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD]
                 |> Q.INST [`guard` |-> `(\(x,y). gd x y)`, `modify` |-> `(\(x,y). (t x, m y))`]
                 |> SIMP_RULE (srw_ss()) [GSYM loop2_count_def] |> GEN_ALL
                 |> CONV_RULE (RENAME_VARS_CONV ["transform", "modify", "guard"]);

loop_count_0 |> SPEC_ALL |> INST_TYPE [alpha |-> ``:'a # 'b``]
             |> SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD]
                 |> Q.INST [`guard` |-> `(\(x,y). gd x y)`, `modify` |-> `(\(x,y). (t x, m y))`]
                 |> SIMP_RULE (srw_ss()) [GSYM loop2_count_def]
                 |> Q.INST [`gd` |-> `guard`, `t` |-> `transform`, `m` |-> `modify`]
                 |> GEN_ALL;
*)


(* Obtain theorems by transform *)
fun loop2_thm_type_a suffix = let
   val th1 = DB.fetch "loop" ("loop_" ^ suffix)
   val th2 = th1 |> SPEC_ALL |> INST_TYPE [alpha |-> ``:'a # 'b``]
                 |> SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD]
                 |> Q.INST [`guard` |-> `(\(x,y). gd x y)`, `modify` |-> `(\(x,y). (t x, m y))`]
                 |> SIMP_RULE (srw_ss()) [GSYM loop2_count_def, GSYM loop2_arg_def] |> GEN_ALL
                 |> CONV_RULE (RENAME_VARS_CONV ["transform", "modify", "guard"])
in
   save_thm("loop2_" ^ suffix, th2 |> DISCH_ALL |> GEN_ALL)
end;


val loop2_arg_thm = loop2_thm_type_a "arg_thm";
(* val loop2_arg_thm = |- !transform modify guard R.
          WF R /\ (!p_1 p_2. ~guard p_1 p_2 ==> R (transform p_1,modify p_2) (p_1,p_2)) ==>
          !p_1 p_2. loop2_arg guard modify transform p_1 p_2 =
              if guard p_1 p_2 then []
              else (p_1,p_2):: loop2_arg guard modify transform (transform p_1) (modify p_2): thm
*)

val loop2_arg_nil = loop2_thm_type_a "arg_nil";
(* val loop2_arg_nil = |- !transform modify guard R.
          WF R /\ (!p_1 p_2. ~guard p_1 p_2 ==> R (transform p_1,modify p_2) (p_1,p_2)) ==>
          !p_1 p_2. guard p_1 p_2 ==> (loop2_arg guard modify transform p_1 p_2 = []): thm
*)

val loop2_arg_cons = loop2_thm_type_a "arg_cons";
(* val loop2_arg_cons = |- !transform modify guard R.
          WF R /\ (!p_1 p_2. ~guard p_1 p_2 ==> R (transform p_1,modify p_2) (p_1,p_2)) ==>
          !p_1 p_2. ~guard p_1 p_2 ==>
              (loop2_arg guard modify transform p_1 p_2 =
               (p_1,p_2)::loop2_arg guard modify transform (transform p_1) (modify p_2)): thm
*)

val loop2_arg_length = loop2_thm_type_a "arg_length";
(* val loop2_arg_length = |- !transform modify guard R.
          WF R /\ (!p_1 p_2. ~guard p_1 p_2 ==> R (transform p_1,modify p_2) (p_1,p_2)) ==>
          !p_1 p_2. LENGTH (loop2_arg guard modify transform p_1 p_2) =
                    loop2_count guard modify transform p_1 p_2: thm
*)

val loop2_arg_eqn = loop2_thm_type_a "arg_eqn";
(* val loop2_arg_eqn = |- !transform modify guard R.
          WF R /\ (!p_1 p_2. ~guard p_1 p_2 ==> R (transform p_1,modify p_2) (p_1,p_2)) ==>
          !p_1 p_2. loop2_arg guard modify transform p_1 p_2 =
              GENLIST (\j. FUNPOW (\(x,y). (transform x,modify y)) j (p_1,p_2))
                      (loop2_count guard modify transform p_1 p_2): thm

*)

val loop2_arg_element = loop2_thm_type_a "arg_element";
(* val loop2_arg_element = |- !transform modify guard R.
          WF R /\ (!p_1 p_2. ~guard p_1 p_2 ==> R (transform p_1,modify p_2) (p_1,p_2)) ==>
          !p_1 p_2 k. k < loop2_count guard modify transform p_1 p_2 ==>
              (EL k (loop2_arg guard modify transform p_1 p_2) =
               FUNPOW (\(x,y). (transform x,modify y)) k (p_1,p_2)): thm
*)

val loop2_arg_cover_sum = loop2_thm_type_a "arg_cover_sum";
(* val loop2_arg_cover_sum = |- !transform modify guard cover R.
          WF R /\ (!p_1 p_2. ~guard p_1 p_2 ==> R (transform p_1,modify p_2) (p_1,p_2)) /\
          (!p_1 p_2 p_1' p_2'. R (p_1,p_2) (p_1',p_2') ==>
               cover (p_1,p_2) <= cover (p_1',p_2')) ==>
          !p_1 p_2.
              SUM (MAP cover (loop2_arg guard modify transform p_1 p_2)) <=
              SUM (MAP (K (cover (p_1,p_2))) (loop2_arg guard modify transform p_1 p_2)): thm
*)

(* Obtain theorems by transform *)
fun loop2_thm_type_b suffix = let
   val th1 = DB.fetch "loop" ("loop_" ^ suffix)
   val th2 = th1 |> SPEC_ALL |> INST_TYPE [alpha |-> ``:'a # 'b``]
                 |> SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD]
                 |> Q.INST [`guard` |-> `(\(x,y). gd x y)`, `modify` |-> `(\(x,y). (t x, m y))`]
                 |> SIMP_RULE (srw_ss()) [GSYM loop2_count_def, GSYM loop2_arg_def] |> GEN_ALL
                 |> CONV_RULE (RENAME_VARS_CONV ["transform", "modify", "guard"])
in
   save_thm("loop2_" ^ suffix, th2 |> DISCH_ALL |> GEN_ALL)
end;
(* Type B is intended for loop and body -- simplification cannot cope with loop. *)

(*
This works:
loop_modify_count_by_sum
   |> SPEC_ALL |> INST_TYPE [``:'a`` |-> ``:'a # 'b``]
   |> SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD]
   |> Q.INST [`loop` |-> `(\(x,y). lp x y)`, `guard` |-> `(\(x,y). gd x y)`,
              `body` |-> `(\(x,y). b x y)`, `modify` |-> `(\(x,y). (t x, m y))`]
   |> PairRules.PBETA_RULE;

But this fails, as SIMP_RULE cannot handle loop:
loop_modify_count_by_sum
   |> SPEC_ALL |> INST_TYPE [``:'a`` |-> ``:'a # 'b``]
   |> SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD]
   |> Q.INST [`loop` |-> `(\(x,y). lp x y)`, `guard` |-> `(\(x,y). gd x y)`,
              `body` |-> `(\(x,y). b x y)`, `modify` |-> `(\(x,y). (t x, m y))`]
   |> SIMP_RULE (srw_ss()) [GSYM loop2_count_def, GSYM loop2_arg_def];
*)

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
        (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
         !x y. loop x y = c + SUM (MAP (UNCURRY body) (loop2_arg guard modify transform x y)) *)
(* Proof: by loop_modify_count_by_sum, loop2_arg_def *)
val loop2_modify_count_by_sum = store_thm(
  "loop2_modify_count_by_sum",
  ``!loop guard body c modify transform R.
        WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
        (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
         !x y. loop x y = c + SUM (MAP (UNCURRY body) (loop2_arg guard modify transform x y))``,
  rpt strip_tac >>
  assume_tac (loop_modify_count_by_sum
   |> SPEC_ALL |> INST_TYPE [``:'a`` |-> ``:'a # 'b``]
   |> SIMP_RULE bool_ss [pairTheory.FORALL_PROD]
   |> Q.INST [`loop` |-> `(\(x,y). lp x y)`, `guard` |-> `(\(x,y). gd x y)`,
              `body` |-> `(\(x,y). b x y)`, `modify` |-> `(\(x,y). (t x, m y))`]
   |> Q.INST [`lp` |-> `loop`, `gd` |-> `guard`, `b` |-> `body`, `t` |-> `transform`, `m` |-> `modify`]
   |> PairRules.PBETA_RULE) >>
  qabbrev_tac `foo1 = !x y. ~guard x y ==> R (transform x,modify y) (x,y)` >>
  qabbrev_tac `foo2 = !x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)` >>
  `UNCURRY body = \(x,y). body x y` by rw[FUN_EQ_THM] >>
  metis_tac[loop2_arg_def]);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
        (!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
         !x y. loop x y <= c + SUM (MAP (UNCURRY body) (loop2_arg guard modify transform x y)) *)
(* Proof: by loop_modify_count_exit_by_sum, loop2_arg_def. *)
val loop2_modify_count_exit_by_sum = store_thm(
  "loop2_modify_count_exit_by_sum",
  ``!loop guard body c exit modify transform R.
    WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
    (!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
     !x y. loop x y <= c + SUM (MAP (UNCURRY body) (loop2_arg guard modify transform x y))``,
  rpt strip_tac >>
  assume_tac (loop_modify_count_exit_by_sum
   |> SPEC_ALL |> INST_TYPE [``:'a`` |-> ``:'a # 'b``]
   |> SIMP_RULE bool_ss [pairTheory.FORALL_PROD]
   |> Q.INST [`loop` |-> `(\(x,y). lp x y)`, `guard` |-> `(\(x,y). gd x y)`,
              `body` |-> `(\(x,y). b x y)`, `modify` |-> `(\(x,y). (t x, m y))`, `exit` |-> `(\(x,y). et x y)`]
   |> Q.INST [`lp` |-> `loop`, `gd` |-> `guard`, `et` |-> `exit`, `b` |-> `body`, `t` |-> `transform`, `m` |-> `modify`]
              |> PairRules.PBETA_RULE) >>
  qabbrev_tac `foo1 = !x y. ~guard x y ==> R (transform x,modify y) (x,y)` >>
  qabbrev_tac `foo2 = !x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (transform x) (modify y)` >>
  `UNCURRY body = \(x,y). body x y` by rw[FUN_EQ_THM] >>
  metis_tac[loop2_arg_def]);

(*
loop_modify_count_quitc_eqn
   |> SPEC_ALL |> INST_TYPE [``:'a`` |-> ``:'a # 'b``]
   |> SIMP_RULE (srw_ss()) [pairTheory.FORALL_PROD]
   |> Q.INST [`loop` |-> `(\(x,y). lp x y)`, `guard` |-> `(\(x,y). gd x y)`,
              `body` |-> `(\(x,y). b x y)`, `modify` |-> `(\(x,y). (t x, m y))`]
   |> PairRules.PBETA_RULE;
val it =
   |- WF R /\ (!p_1 p_2. ~gd p_1 p_2 ==> R (t p_1,m p_2) (p_1,p_2)) /\
      (!p_1 p_2. lp p_1 p_2 =
           if gd p_1 p_2 then c else b p_1 p_2 + lp (t p_1) (m p_2)) ==>
      !p_1 p_2. (if gd p_1 p_2 then c else b p_1 p_2 + lp (t p_1) (m p_2)) =
          c + SUM (GENLIST
               (\j.
                    b (FST (FUNPOW (\(x,y). (t x,m y)) j (p_1,p_2)))
                      (SND (FUNPOW (\(x,y). (t x,m y)) j (p_1,p_2))))
               (loop_count (\(x,y). gd x y) (\(x,y). (t x,m y)) (p_1,p_2))): thm
*)

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
        (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
         !x y. loop x y = c + SUM (GENLIST (\j. body (FUNPOW transform j x) (FUNPOW modify j y))
                                           (loop2_count guard modify transform x y)) *)
(* Proof: by loop_modify_count_quitc_eqn, loop2_count_def *)
val loop2_modify_count_quitc_eqn = store_thm(
  "loop2_modify_count_quitc_eqn",
  ``!loop guard body c modify transform R.
        WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
        (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
         !x y. loop x y = c + SUM (GENLIST (\j. body (FUNPOW transform j x) (FUNPOW modify j y))
                                           (loop2_count guard modify transform x y))``,
  rpt strip_tac >>
  assume_tac (loop_modify_count_quitc_eqn
   |> SPEC_ALL |> INST_TYPE [``:'a`` |-> ``:'a # 'b``]
   |> SIMP_RULE bool_ss [pairTheory.FORALL_PROD]
   |> Q.INST [`loop` |-> `(\(x,y). lp x y)`, `guard` |-> `(\(x,y). gd x y)`,
              `body` |-> `(\(x,y). b x y)`, `modify` |-> `(\(x,y). (t x, m y))`]
   |> SIMP_RULE bool_ss [FUNPOW_PAIR, GSYM loop2_count_def]
   |> Q.INST [`lp` |-> `loop`, `gd` |-> `guard`, `b` |-> `body`, `t` |-> `transform`, `m` |-> `modify`]
   |> PairRules.PBETA_RULE) >>
  qabbrev_tac `foo1 = !x y. ~guard x y ==> R (transform x,modify y) (x,y)` >>
  qabbrev_tac `foo2 = !x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)` >>
  metis_tac[]);


(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
        (!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
         !x y. loop x y <= c + SUM (GENLIST
                                     (\j. body (FUNPOW transform j x) (FUNPOW modify j y))
                                     (loop2_count guard modify transform x y)) *)
(* Proof: by loop_modify_count_quitc_exit_le, loop2_count_def. *)
val loop2_modify_count_quitc_exit_le = store_thm(
  "loop2_modify_count_quitc_exit_le",
  ``!loop guard body c exit modify transform R.
    WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
    (!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
     !x y. loop x y <= c + SUM (GENLIST
                                  (\j. body (FUNPOW transform j x) (FUNPOW modify j y))
                                  (loop2_count guard modify transform x y))``,
  rpt strip_tac >>
  assume_tac (loop_modify_count_quitc_exit_le
   |> SPEC_ALL |> INST_TYPE [``:'a`` |-> ``:'a # 'b``]
   |> SIMP_RULE bool_ss [pairTheory.FORALL_PROD]
   |> Q.INST [`loop` |-> `(\(x,y). lp x y)`, `guard` |-> `(\(x,y). gd x y)`,
              `body` |-> `(\(x,y). b x y)`, `modify` |-> `(\(x,y). (t x, m y))`, `exit` |-> `(\(x,y). et x y)`]
   |> SIMP_RULE bool_ss [FUNPOW_PAIR, GSYM loop2_count_def]
   |> Q.INST [`lp` |-> `loop`, `gd` |-> `guard`, `et` |-> `exit`, `b` |-> `body`, `t` |-> `transform`, `m` |-> `modify`]
   |> PairRules.PBETA_RULE) >>
  qabbrev_tac `foo1 = !x y. ~guard x y ==> R (transform x,modify y) (x,y)` >>
  qabbrev_tac `foo2 = !x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (transform x) (modify y)` >>
  metis_tac[]);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
   (!x y. body x y <= cover x y) /\
   (!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> bcover x1 y1 <= bcover x2 y2) /\
   (!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
    !x y. loop x y <= c + (bcover x y) * loop2_count guard modify transform x y *)
(* Proof: by loop_modify_count_cover_exit_upper, loop2_count_def *)
val loop2_modify_count_bcover_exit_upper = store_thm(
  "loop2_modify_count_bcover_exit_upper",
  ``!loop guard body c exit bcover modify transform R.
   WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
   (!x y. body x y <= bcover x y) /\
   (!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> bcover x1 y1 <= bcover x2 y2) /\
   (!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
    !x y. loop x y <= c + (bcover x y) * loop2_count guard modify transform x y``,
  rpt strip_tac >>
  assume_tac (loop_modify_count_cover_exit_upper
   |> SPEC_ALL |> INST_TYPE [``:'a`` |-> ``:'a # 'b``]
   |> SIMP_RULE bool_ss [pairTheory.FORALL_PROD]
   |> Q.INST [`loop` |-> `(\(x,y). lp x y)`, `guard` |-> `(\(x,y). gd x y)`, `cover` |-> `(\(x,y). cv x y)`,
              `body` |-> `(\(x,y). b x y)`, `modify` |-> `(\(x,y). (t x, m y))`, `exit` |-> `(\(x,y). et x y)`]
   |> Q.INST [`lp` |-> `loop`, `gd` |-> `guard`, `et` |-> `exit`, `b` |-> `body`, `cv` |-> `bcover`, `t` |-> `transform`, `m` |-> `modify`]
              |> PairRules.PBETA_RULE) >>
  qabbrev_tac `foo1 = !x y. ~guard x y ==> R (transform x,modify y) (x,y)` >>
  qabbrev_tac `foo2 = !x y. body x y <= bcover x y` >>
  metis_tac[loop2_count_def]);

(* Note: the most general form should involve tcover, for the transform. *)

(* Since lifting is so complicated, just derive specific cases from this one. *)

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
   (!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> body x1 y1 <= body x2 y2) /\
   (!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
    !x y. loop x y <= c + (body x y) * loop2_count guard modify transform x y *)
(* Proof: by loop2_modify_count_bcover_exit_upper, with bcover = body. *)
val loop2_modify_count_exit_upper = store_thm(
  "loop2_modify_count_exit_upper",
  ``!loop guard body c exit modify transform R.
   WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
   (!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> body x1 y1 <= body x2 y2) /\
   (!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
    !x y. loop x y <= c + (body x y) * loop2_count guard modify transform x y``,
  rpt strip_tac >>
  assume_tac loop2_modify_count_bcover_exit_upper >>
  last_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `exit`, `body`, `modify`, `transform`, `R`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
   (!x y. body x y <= bcover x y) /\
   (!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> bcover x1 y1 <= bcover x2 y2) /\
   (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
    !x y. loop x y <= c + (bcover x y) * loop2_count guard modify transform x y *)
(* Proof: by loop2_modify_count_bcover_exit_upper, with exit = F. *)
val loop2_modify_count_bcover_upper = store_thm(
  "loop2_modify_count_bcover_upper",
  ``!loop guard body c bcover modify transform R.
   WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
   (!x y. body x y <= bcover x y) /\
   (!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> bcover x1 y1 <= bcover x2 y2) /\
   (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
    !x y. loop x y <= c + (bcover x y) * loop2_count guard modify transform x y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x y. F` >>
  assume_tac loop2_modify_count_bcover_exit_upper >>
  last_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `exit`, `bcover`, `modify`, `transform`, `R`] strip_assume_tac) >>
  metis_tac[]);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
   (!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> body x1 y1 <= body x2 y2) /\
   (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
    !x y. loop x y <= c + (bcover x y) * loop2_count guard modify transform x y *)
(* Proof: by loop2_modify_count_bcover_upper, with bcover = body. *)
val loop2_modify_count_upper = store_thm(
  "loop2_modify_count_upper",
  ``!loop guard body c modify transform R.
   WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
   (!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> body x1 y1 <= body x2 y2) /\
   (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
    !x y. loop x y <= c + (body x y) * loop2_count guard modify transform x y``,
  rpt strip_tac >>
  assume_tac loop2_modify_count_bcover_upper >>
  last_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `body`, `modify`, `transform`, `R`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)
(* Estimation for Numeric Loops                                              *)
(* ------------------------------------------------------------------------- *)

(* Idea:

   From loop_modify_count_quitc_eqn, let n = loop_count guard modify x.
     loop x
   = c + SUM (GENLIST (\j. body (FUNPOW modify j x)) n)
   = c + [body x, body (m x), body (m (m x)), ....]    for n terms
  If FALLING m,
  <= c + [body x, body x, body x, .....]    if MONO body,
   = c + n * body x
  If RISING m,
  <= c + [body (last x), body (last x), ...]  if MONO body,
   = c + n * body (last x)
*)

(* ------------------------------------------------------------------------- *)
(* Numeric Loops with RISING modify                                          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                    in (!x. body x <= cover x) /\ MONO cover ==>
                       loop x <= c + n * cover (FUNPOW modify n x) *)
(* Proof:
   Let n = loop_count guard modify x,
       z = FUNPOW modify n x,
       f = (\j. body (FUNPOW modify j x)).

   For k < n,
      FUNPOW modify k x <= FUNPOW modify n x  by FUNPOW_LE_RISING, RISING modify
                         = z                  by notation
   Thus,
       loop x
    <= c + SUM (GENLIST f n)                by loop_modify_count_quitc_exit_le
    <= c + SUM (GENLIST (K (cover z)) n)    by SUM_LE, EL_GENLIST, RISING modify
     = c + (cover z) * n                    by SUM_GENLIST_K
     = c + n * cover z                      by MULT_COMM
*)
val loop_rise_count_cover_quitc_exit_le = store_thm(
  "loop_rise_count_cover_quitc_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                    in (!x. body x <= cover x) /\ MONO cover ==>
                       loop x <= c + n * cover (FUNPOW modify n x)``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop_modify_count_quitc_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `n = loop_count guard modify x` >>
  qabbrev_tac `z = FUNPOW modify n x` >>
  qabbrev_tac `f = \j. body (FUNPOW modify j x)` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover z)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`, Abbr`z`] >>
  `FUNPOW modify k x <= FUNPOW modify n x` by rw[FUNPOW_LE_RISING] >>
  qabbrev_tac `u = FUNPOW modify k x` >>
  qabbrev_tac `v = FUNPOW modify n x` >>
  `body u <= cover u` by rw[] >>
  `cover u <= cover v` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover z)) n) = cover z * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x. let n = loop_count guard modify x
            in MONO body ==> loop x <= c + n * body (FUNPOW modify n x) *)
(* Proof: by loop_rise_count_cover_quitc_exit_le with cover = body. *)
val loop_rise_count_exit_le = store_thm(
  "loop_rise_count_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x. let n = loop_count guard modify x
            in MONO body ==> loop x <= c + n * body (FUNPOW modify n x)``,
  rpt strip_tac >>
  imp_res_tac loop_rise_count_cover_quitc_exit_le >>
  first_x_assum (qspecl_then [`x`, `body`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                    in (!x. body x <= cover x) /\ MONO cover ==>
                       loop x <= c + n * cover (FUNPOW modify n x) *)
(* Proof: by loop_rise_count_cover_quitc_exit_le with exit = F. *)
val loop_rise_count_cover_le = store_thm(
  "loop_rise_count_cover_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                    in (!x. body x <= cover x) /\ MONO cover ==>
                       loop x <= c + n * cover (FUNPOW modify n x)``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num. F` >>
  assume_tac loop_rise_count_cover_quitc_exit_le >>
  first_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `exit`, `modify`, `transform`, `R`] strip_assume_tac) >>
  metis_tac[]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x. let n = loop_count guard modify x
            in MONO body ==> loop x <= c + n * body (FUNPOW modify n x) *)
(* Proof: by loop_rise_count_cover_le with cover = body *)
val loop_rise_count_le = store_thm(
  "loop_rise_count_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x. let n = loop_count guard modify x
            in MONO body ==> loop x <= c + n * body (FUNPOW modify n x)``,
  rpt strip_tac >>
  imp_res_tac loop_rise_count_cover_le >>
  first_x_assum (qspecl_then [`x`, `body`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                    in (!x. body x <= cover x) /\ RMONO cover ==>
                       loop x <= c + n * cover x *)
(* Proof:
   Let n = loop_count guard modify x,
       u = FUNPOW modify k x,
       f = (\j. body (FUNPOW modify j x)).

   For k < n,
      FUNPOW modify 0 x <= FUNPOW modify k x  by FUNPOW_LE_RISING, RISING modify
                      x <= u                  by FUNPOW_0
             so cover u <= cover x            by RMONO cover
      body u <= cover u                       by body and cover
   Thus,
       loop x
    <= c + SUM (GENLIST f n)                by loop_modify_count_quitc_exit_le
    <= c + SUM (GENLIST (K (cover x)) n)    by SUM_LE, EL_GENLIST, RISING modify
     = c + (cover x) * n                    by SUM_GENLIST_K
     = c + n * cover x                      by MULT_COMM
*)
val loop_rise_count_rcover_quitc_exit_le = store_thm(
  "loop_rise_count_rcover_quitc_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                    in (!x. body x <= cover x) /\ RMONO cover ==>
                       loop x <= c + n * cover x``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop_modify_count_quitc_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `f = \j. body (FUNPOW modify j x)` >>
  qabbrev_tac `n = loop_count guard modify x` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover x)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`] >>
  `FUNPOW modify 0 x <= FUNPOW modify k x` by rw[FUNPOW_LE_RISING] >>
  `FUNPOW modify 0 x = x` by rw[] >>
  qabbrev_tac `u = FUNPOW modify k x` >>
  `body u <= cover u` by rw[] >>
  `cover u <= cover x` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover x)) n) = cover x * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x. let n = loop_count guard modify x
                    in RMONO body ==> loop x <= c + n * body x *)
(* Proof: by loop_rise_count_rcover_quitc_exit_le with cover = body. *)
val loop_rise_count_rbody_exit_le = store_thm(
  "loop_rise_count_rbody_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x. let n = loop_count guard modify x
                    in RMONO body ==> loop x <= c + n * body x``,
  rpt strip_tac >>
  imp_res_tac loop_rise_count_rcover_quitc_exit_le >>
  first_x_assum (qspecl_then [`x`, `body`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                    in (!x. body x <= cover x) /\ RMONO cover ==>
                       loop x <= c + n * cover x *)
(* Proof: by loop_rise_count_rcover_quitc_exit_le with exit = F. *)
val loop_rise_count_rcover_le = store_thm(
  "loop_rise_count_rcover_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                  in (!x. body x <= cover x) /\ RMONO cover ==>
                       loop x <= c + n * cover x``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num. F` >>
  assume_tac loop_rise_count_rcover_quitc_exit_le >>
  first_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `exit`, `modify`, `transform`, `R`] strip_assume_tac) >>
  metis_tac[]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x. let n = loop_count guard modify x
            in RMONO body ==> loop x <= c + n * body x *)
(* Proof: by loop_rise_count_rcover_le with cover = body. *)
val loop_rise_count_rbody_le = store_thm(
  "loop_rise_count_rbody_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ RISING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x. let n = loop_count guard modify x
            in RMONO body ==> loop x <= c + n * body x``,
  rpt strip_tac >>
  imp_res_tac loop_rise_count_rcover_le >>
  first_x_assum (qspecl_then [`x`, `body`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)
(* Numeric Loops with FALLING modify                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                    in (!x. body x <= cover x) /\ MONO cover ==>
                       loop x <= c + n * cover x *)
(* Proof:
   Let n = loop_count guard modify x,
       f = (\j. body (FUNPOW modify j x)).

   For k < n,
      FUNPOW modify k x <= FUNPOW modify 0 x  by FUNPOW_LE_FALLING, FALLING modify
                         = x                  by FUNPOW_0
   Thus,
       loop x
    <= c + SUM (GENLIST f n)                by loop_modify_count_quitc_exit_le
    <= c + SUM (GENLIST (K (cover x)) n)    by SUM_LE, EL_GENLIST, RISING modify
     = c + (cover x) * n                    by SUM_GENLIST_K
     = c + n * cover x                      by MULT_COMM
*)
val loop_fall_count_cover_quitc_exit_le = store_thm(
  "loop_fall_count_cover_quitc_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                    in (!x. body x <= cover x) /\ MONO cover ==>
                       loop x <= c + n * cover x``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop_modify_count_quitc_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `n = loop_count guard modify x` >>
  qabbrev_tac `f = \j. body (FUNPOW modify j x)` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover x)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`] >>
  `FUNPOW modify k x <= FUNPOW modify 0 x` by rw[FUNPOW_LE_FALLING] >>
  `FUNPOW modify 0 x = x` by rw[] >>
  qabbrev_tac `u = FUNPOW modify k x` >>
  `body u <= cover u` by rw[] >>
  `cover u <= cover x` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover x)) n) = cover x * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x. let n = loop_count guard modify x
            in MONO body ==> loop x <= c + n * body x *)
(* Proof: by loop_fall_count_cover_quitc_exit_le with cover = body *)
val loop_fall_count_exit_le = store_thm(
  "loop_fall_count_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x. let n = loop_count guard modify x
                    in MONO body ==> loop x <= c + n * body x``,
  rpt strip_tac >>
  imp_res_tac loop_fall_count_cover_quitc_exit_le >>
  first_x_assum (qspecl_then [`x`, `body`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                    in (!x. body x <= cover x) /\ MONO cover ==>
                       loop x <= c + n * cover x *)
(* Proof: by loop_fall_count_cover_quitc_exit_le with exit = F. *)
val loop_fall_count_cover_le = store_thm(
  "loop_fall_count_cover_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                    in (!x. body x <= cover x) /\ MONO cover ==>
                       loop x <= c + n * cover x``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num. F` >>
  assume_tac loop_fall_count_cover_quitc_exit_le >>
  first_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `exit`, `modify`, `transform`, `R`] strip_assume_tac) >>
  metis_tac[]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x. let n = loop_count guard modify x
            in MONO body ==> loop x <= c + n * body x *)
(* Proof: by loop_fall_count_cover_le with cover = body *)
val loop_fall_count_le = store_thm(
  "loop_fall_count_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x. let n = loop_count guard modify x
            in MONO body ==> loop x <= c + n * body x``,
  rpt strip_tac >>
  imp_res_tac loop_fall_count_cover_le >>
  first_x_assum (qspecl_then [`x`, `body`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                    in (!x. body x <= cover x) /\ RMONO cover ==>
                       loop x <= c + n * cover (FUNPOW modify n x) *)
(* Proof:
   Let n = loop_count guard modify x,
       u = FUNPOW modify k x,
       z = FUNPOW modify n x,
       f = (\j. body (FUNPOW modify j x)).

   For k < n,
      FUNPOW modify n x <= FUNPOW modify k x  by FUNPOW_LE_FALLING, FALLING modify
                      z <= u                  by notation
             so cover u <= cover z            by RMONO cover
      body u <= cover u                       by cover property
   Thus,
       loop x
    <= c + SUM (GENLIST f n)                by loop_modify_count_quitc_exit_le
    <= c + SUM (GENLIST (K (cover z)) n)    by SUM_LE, EL_GENLIST, RISING modify
     = c + (cover z) * n                    by SUM_GENLIST_K
     = c + n * cover z                      by MULT_COMM
*)
val loop_fall_count_rcover_quitc_exit_le = store_thm(
  "loop_fall_count_rcover_quitc_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                    in (!x. body x <= cover x) /\ RMONO cover ==>
                       loop x <= c + n * cover (FUNPOW modify n x)``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop_modify_count_quitc_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `f = \j. body (FUNPOW modify j x)` >>
  qabbrev_tac `n = loop_count guard modify x` >>
  qabbrev_tac `z = FUNPOW modify n x` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover z)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`, Abbr`z`] >>
  `FUNPOW modify n x <= FUNPOW modify k x` by rw[FUNPOW_LE_FALLING] >>
  qabbrev_tac `u = FUNPOW modify k x` >>
  qabbrev_tac `v = FUNPOW modify n x` >>
  `body u <= cover u` by rw[] >>
  `cover u <= cover v` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover z)) n) = cover z * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x. let n = loop_count guard modify x
            in RMONO body ==> loop x <= c + n * body (FUNPOW modify n x) *)
(* Proof: by loop_fall_count_rcover_quitc_exit_le with cover = body. *)
val loop_fall_count_rbody_exit_le = store_thm(
  "loop_fall_count_rbody_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + if exit x then 0 else loop (modify x)) ==>
       !x. let n = loop_count guard modify x
            in RMONO body ==> loop x <= c + n * body (FUNPOW modify n x)``,
  rpt strip_tac >>
  imp_res_tac loop_fall_count_rcover_quitc_exit_le >>
  first_x_assum (qspecl_then [`x`, `body`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                  in (!x. body x <= cover x) /\ RMONO cover ==>
                       loop x <= c + n * cover (FUNPOW modify n x) *)
(* Proof: by loop_fall_count_rcover_quitc_exit_le with exit = F. *)
val loop_fall_count_rcover_le = store_thm(
  "loop_fall_count_rcover_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x cover. let n = loop_count guard modify x
                  in (!x. body x <= cover x) /\ RMONO cover ==>
                       loop x <= c + n * cover (FUNPOW modify n x)``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x: num. F` >>
  assume_tac loop_fall_count_rcover_quitc_exit_le >>
  first_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `exit`, `modify`, `transform`, `R`] strip_assume_tac) >>
  metis_tac[]);

(* Theorem: WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x. let n = loop_count guard modify x
                    in RMONO body ==> loop x <= c + n * body (FUNPOW modify n x) *)
(* Proof: by loop_fall_count_rcover_le with cover = body. *)
val loop_fall_count_rbody_le = store_thm(
  "loop_fall_count_rbody_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x. ~guard x ==> R (modify x) x) /\ FALLING modify /\
      (!x. loop x = if guard x then c else body x + loop (modify x)) ==>
       !x. let n = loop_count guard modify x
                    in RMONO body ==> loop x <= c + n * body (FUNPOW modify n x)``,
  rpt strip_tac >>
  imp_res_tac loop_fall_count_rcover_le >>
  first_x_assum (qspecl_then [`x`, `body`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)

(* Idea:

   From loop2_modify_count_quitc_eqn, let n = loop2_count guard modify transform x y.
     loop x y
   = c + SUM (GENLIST (\j. body (FUNPOW transform j x) (FUNPOW modify j y)) n)
   = c + [body x y, body (t x) (m y), body (t (t x)) (m (m y)), ....]    for n terms
  <= c + [body x y, body (t x) y, body (t (t x)) y, .....]    if MONO2 body, FALLING m
  If FALLING t,
  <= c + [body x y, body x y, ....] = c + n * body x y
  If RISING t,
  <= c + [body (last x) y, body (last x) y, ...] = c + n * body (last x) y
  Similar estimates for RISING m
*)

(* ------------------------------------------------------------------------- *)
(* Numeric Loops with RISING transform and FALLING modify                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ FALLING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover (FUNPOW transform n x) y *)
(* Proof:
   Let n = loop2_count guard modify transform x y,
       p = FUNPOW transform n x,
       f = (\j. body (FUNPOW transform j x) (FUNPOW modify j y)).

   For k < n,
      FUNPOW transform k x <= FUNPOW transform n x   by FUNPOW_LE_RISING, RISING transform
                            = p                      by notation
      FUNPOW modify k y <= FUNPOW modify 0 y         by FUNPOW_LE_FALLING, FALLING modify
                         = y                         by FUNPOW_0
   Thus,
       loop x y
    <= c + SUM (GENLIST f n)                  by loop2_modify_count_quitc_exit_le
    <= c + SUM (GENLIST (K (cover p y)) n)    by SUM_LE, EL_GENLIST, FALLING modify, RISING transform
     = c + (cover p y) * n                    by SUM_GENLIST_K
     = c + n * cover p y                      by MULT_COMM
*)
val loop2_rise_fall_count_cover_quitc_exit_le = store_thm(
  "loop2_rise_fall_count_cover_quitc_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ FALLING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover (FUNPOW transform n x) y``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x y. loop x y =
                      if guard x y then c
                      else body x y + if exit x y then 0 else loop (transform x) (modify y)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop2_modify_count_quitc_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = loop2_count guard modify transform x y` >>
  qabbrev_tac `p = FUNPOW transform n x` >>
  qabbrev_tac `f = \j. body (FUNPOW transform j x) (FUNPOW modify j y)` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover p y)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`, Abbr`p`] >>
  `FUNPOW transform k x <= FUNPOW transform n x` by rw[FUNPOW_LE_RISING] >>
  `FUNPOW modify k y <= FUNPOW modify 0 y` by rw[FUNPOW_LE_FALLING] >>
  `FUNPOW modify 0 y = y` by rw[] >>
  qabbrev_tac `u = FUNPOW transform k x` >>
  qabbrev_tac `v = FUNPOW modify k y` >>
  `body u v <= cover u v` by rw[] >>
  `cover u v <= cover (FUNPOW transform n x) y` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover p y)) n) = cover p y * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ FALLING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
              in MONO2 body ==> loop x y <= c + n * body (FUNPOW transform n x) y *)
(* Proof: by loop2_rise_fall_count_cover_quitc_exit_le with cover = body. *)
val loop2_rise_fall_count_exit_le = store_thm(
  "loop2_rise_fall_count_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ FALLING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
              in MONO2 body ==> loop x y <= c + n * body (FUNPOW transform n x) y``,
  rpt strip_tac >>
  imp_res_tac loop2_rise_fall_count_cover_quitc_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`, `body`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ FALLING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover (FUNPOW transform n x) y *)
(* Proof: by loop2_rise_fall_count_cover_quitc_exit_le with exit = F. *)
val loop2_rise_fall_count_cover_le = store_thm(
  "loop2_rise_fall_count_cover_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ FALLING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover (FUNPOW transform n x) y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  assume_tac loop2_rise_fall_count_cover_quitc_exit_le >>
  first_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `exit`, `modify`, `transform`, `R`] strip_assume_tac) >>
  metis_tac[]);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ FALLING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
              in MONO2 body ==> loop x y <= c + n * body (FUNPOW transform n x) y *)
(* Proof: by loop2_rise_fall_count_cover_le with cover = body. *)
val loop2_rise_fall_count_le = store_thm(
  "loop2_rise_fall_count_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ FALLING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
              in MONO2 body ==> loop x y <= c + n * body (FUNPOW transform n x) y``,
  rpt strip_tac >>
  imp_res_tac loop2_rise_fall_count_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`, `body`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)
(* Numeric Loops with FALLING transform and FALLING modify                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ FALLING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover x y *)
(* Proof:
   Let n = loop2_count guard modify transform x y,
       f = (\j. body (FUNPOW transform j x) (FUNPOW modify j y)).

   For k < n,
      FUNPOW transform k x <= FUNPOW transform 0 x   by FUNPOW_LE_FALLING, FALLING transform
                            = x                      by FUNPOW_0
      FUNPOW modify k y <= FUNPOW modify 0 y         by FUNPOW_LE_FALLING, FALLING modify
                         = y                         by FUNPOW_0
   Thus,
       loop x y
    <= c + SUM (GENLIST f n)                  by loop2_modify_count_quitc_exit_le
    <= c + SUM (GENLIST (K (cover x y)) n)    by SUM_LE, EL_GENLIST, FALLING modify, FALLING transform
     = c + (cover x y) * n                    by SUM_GENLIST_K
     = c + n * cover x y                      by MULT_COMM
*)
val loop2_fall_fall_count_cover_quitc_exit_le = store_thm(
  "loop2_fall_fall_count_cover_quitc_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ FALLING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover x y``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x y. loop x y =
                      if guard x y then c
                      else body x y + if exit x y then 0 else loop (transform x) (modify y)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop2_modify_count_quitc_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = loop2_count guard modify transform x y` >>
  qabbrev_tac `f = \j. body (FUNPOW transform j x) (FUNPOW modify j y)` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover x y)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`] >>
  `FUNPOW transform k x <= FUNPOW transform 0 x` by rw[FUNPOW_LE_FALLING] >>
  `FUNPOW modify k y <= FUNPOW modify 0 y` by rw[FUNPOW_LE_FALLING] >>
  `FUNPOW transform 0 x = x` by rw[] >>
  `FUNPOW modify 0 y = y` by rw[] >>
  qabbrev_tac `u = FUNPOW transform k x` >>
  qabbrev_tac `v = FUNPOW modify k y` >>
  `body u v <= cover u v` by rw[] >>
  `cover u v <= cover x y` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover x y)) n) = cover x y * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ FALLING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
                    in MONO2 body ==> loop x y <= c + n * body x y *)
(* Proof: by loop2_fall_fall_count_cover_quitc_exit_le with cover = body. *)
val loop2_fall_fall_count_exit_le = store_thm(
  "loop2_fall_fall_count_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ FALLING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
                    in MONO2 body ==> loop x y <= c + n * body x y``,
  rpt strip_tac >>
  assume_tac loop2_fall_fall_count_cover_quitc_exit_le >>
  first_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `exit`, `modify`, `transform`, `R`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ FALLING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover x y *)
(* Proof: by loop2_fall_fall_count_cover_quitc_exit_le with exit = F. *)
val loop2_fall_fall_count_cover_le = store_thm(
  "loop2_fall_fall_count_cover_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ FALLING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover x y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  assume_tac loop2_fall_fall_count_cover_quitc_exit_le >>
  first_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `exit`, `modify`, `transform`, `R`] strip_assume_tac) >>
  metis_tac[]);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ FALLING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
                    in MONO2 body ==> loop x y <= c + n * body x y *)
(* Proof: by loop2_fall_fall_count_cover_le with cover = body *)
val loop2_fall_fall_count_le = store_thm(
  "loop2_fall_fall_count_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ FALLING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
                    in MONO2 body ==> loop x y <= c + n * body x y``,
  rpt strip_tac >>
  assume_tac loop2_fall_fall_count_cover_le >>
  first_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `modify`, `transform`, `R`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)
(* Numeric Loops with FALLING transform and RISING modify                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ RISING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover x (FUNPOW modify n y) *)
(* Proof:
   Let n = loop2_count guard modify transform x y,
       q = FUNPOW modify n y,
       f = (\j. body (FUNPOW transform j x) (FUNPOW modify j y)).

   For k < n,
      FUNPOW transform k x <= FUNPOW transform 0 x   by FUNPOW_LE_FALLING, FALLING transform
                            = x                      by FUNPOW_0
      FUNPOW modify k y <= FUNPOW modify n y         by FUNPOW_LE_RISING, RISING modify
                         = q                         by notation
   Thus,
       loop x y
    <= c + SUM (GENLIST f n)                  by loop2_modify_count_quitc_exit_le
    <= c + SUM (GENLIST (K (cover x q)) n)    by SUM_LE, EL_GENLIST, RISING modify, FALLING transform
     = c + (cover x q) * n                    by SUM_GENLIST_K
     = c + n * cover x q                      by MULT_COMM
*)
val loop2_fall_rise_count_cover_quitc_exit_le = store_thm(
  "loop2_fall_rise_count_cover_quitc_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ RISING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover x (FUNPOW modify n y)``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x y. loop x y =
                      if guard x y then c
                      else body x y + if exit x y then 0 else loop (transform x) (modify y)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop2_modify_count_quitc_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = loop2_count guard modify transform x y` >>
  qabbrev_tac `q = FUNPOW modify n y` >>
  qabbrev_tac `f = \j. body (FUNPOW transform j x) (FUNPOW modify j y)` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover x q)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`, Abbr`q`] >>
  `FUNPOW transform k x <= FUNPOW transform 0 x` by rw[FUNPOW_LE_FALLING] >>
  `FUNPOW modify k y <= FUNPOW modify n y` by rw[FUNPOW_LE_RISING] >>
  `FUNPOW transform 0 x = x` by rw[] >>
  qabbrev_tac `u = FUNPOW transform k x` >>
  qabbrev_tac `v = FUNPOW modify k y` >>
  `body u v <= cover u v` by rw[] >>
  `cover u v <= cover x (FUNPOW modify n y)` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover x q)) n) = cover x q * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ RISING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
              in MONO2 body ==> loop x y <= c + n * body x (FUNPOW modify n y) *)
(* Proof: by loop2_fall_rise_count_cover_quitc_exit_le with cover = body. *)
val loop2_fall_rise_count_exit_le = store_thm(
  "loop2_fall_rise_count_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ RISING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
              in MONO2 body ==> loop x y <= c + n * body x (FUNPOW modify n y)``,
  rpt strip_tac >>
  imp_res_tac loop2_fall_rise_count_cover_quitc_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`, `body`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ RISING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover x (FUNPOW modify n y) *)
(* Proof: by loop2_fall_rise_count_cover_quitc_exit_le with exit = F. *)
val loop2_fall_rise_count_cover_le = store_thm(
  "loop2_fall_rise_count_cover_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ RISING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover x (FUNPOW modify n y)``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  assume_tac loop2_fall_rise_count_cover_quitc_exit_le >>
  first_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `exit`, `modify`, `transform`, `R`] strip_assume_tac) >>
  metis_tac[]);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ RISING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
                    in MONO2 body ==> loop x y <= c + n * body x (FUNPOW modify n y) *)
(* Proof: by loop2_fall_rise_count_cover_le with cover = body. *)
val loop2_fall_rise_count_le = store_thm(
  "loop2_fall_rise_count_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      FALLING transform /\ RISING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
                    in MONO2 body ==> loop x y <= c + n * body x (FUNPOW modify n y)``,
  rpt strip_tac >>
  imp_res_tac loop2_fall_rise_count_cover_le >>
  first_x_assum (qspecl_then [`y`, `x`, `body`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)
(* Numeric Loops with RISING transform and RISING modify                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ RISING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover (FUNPOW transform n x) (FUNPOW modify n y) *)
(* Proof:
   Let n = loop2_count guard modify transform x y,
       p = FUNPOW transform n x,
       q = FUNPOW modify n y,
       f = (\j. body (FUNPOW transform j x) (FUNPOW modify j y)).

   For k < n,
      FUNPOW transform k x <= FUNPOW transform n x   by FUNPOW_LE_RISING, RISING transform
                            = p                      by notation
      FUNPOW modify k y <= FUNPOW modify n y         by FUNPOW_LE_RISING, RISING modify
                         = q                         by notation
   Thus,
       loop x y
    <= c + SUM (GENLIST f n)                  by loop2_modify_count_quitc_exit_le
    <= c + SUM (GENLIST (K (cover p q)) n)    by SUM_LE, EL_GENLIST, RISING modify, RISING transform
     = c + (cover p q) * n                    by SUM_GENLIST_K
     = c + n * cover p q                      by MULT_COMM
*)
val loop2_rise_rise_count_cover_quitc_exit_le = store_thm(
  "loop2_rise_rise_count_cover_quitc_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ RISING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover (FUNPOW transform n x) (FUNPOW modify n y)``,
  rpt strip_tac >>
  qabbrev_tac `foo = !x y. loop x y =
                      if guard x y then c
                      else body x y + if exit x y then 0 else loop (transform x) (modify y)` >>
  simp[] >>
  unabbrev_all_tac >>
  rpt strip_tac >>
  imp_res_tac loop2_modify_count_quitc_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `n = loop2_count guard modify transform x y` >>
  qabbrev_tac `p = FUNPOW transform n x` >>
  qabbrev_tac `q = FUNPOW modify n y` >>
  qabbrev_tac `f = \j. body (FUNPOW transform j x) (FUNPOW modify j y)` >>
  `SUM (GENLIST f n) <= SUM (GENLIST (K (cover p q)) n)` by
  (irule SUM_LE >>
  rw[] >>
  rw[Abbr`f`, Abbr`p`, Abbr`q`] >>
  `FUNPOW transform k x <= FUNPOW transform n x` by rw[FUNPOW_LE_RISING] >>
  `FUNPOW modify k y <= FUNPOW modify n y` by rw[FUNPOW_LE_RISING] >>
  qabbrev_tac `u = FUNPOW transform k x` >>
  qabbrev_tac `v = FUNPOW modify k y` >>
  `body u v <= cover u v` by rw[] >>
  `cover u v <= cover (FUNPOW transform n x) (FUNPOW modify n y)` by rw[] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover p q)) n) = cover p q * n` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ RISING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
                    in MONO2 body ==>
                       loop x y <= c + n * body (FUNPOW transform n x) (FUNPOW modify n y) *)
(* Proof: by loop2_rise_rise_count_cover_quitc_exit_le with cover = body. *)
val loop2_rise_rise_count_exit_le = store_thm(
  "loop2_rise_rise_count_exit_le",
  ``!loop guard body c exit modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ RISING modify /\
      (!x y. loop x y =
             if guard x y then c
             else body x y + if exit x y then 0 else loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
                    in MONO2 body ==>
                       loop x y <= c + n * body (FUNPOW transform n x) (FUNPOW modify n y)``,
  rpt strip_tac >>
  assume_tac loop2_rise_rise_count_cover_quitc_exit_le >>
  first_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `exit`, `modify`, `transform`, `R`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ RISING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover (FUNPOW transform n x) (FUNPOW modify n y) *)
(* Proof: by loop2_rise_rise_count_cover_quitc_exit_le with exit = F. *)
val loop2_rise_rise_count_cover_le = store_thm(
  "loop2_rise_rise_count_cover_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ RISING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y cover. let n = loop2_count guard modify transform x y
                    in (!x y. body x y <= cover x y) /\ MONO2 cover ==>
                       loop x y <= c + n * cover (FUNPOW transform n x) (FUNPOW modify n y)``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num y:num. F` >>
  assume_tac loop2_rise_rise_count_cover_quitc_exit_le >>
  first_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `exit`, `modify`, `transform`, `R`] strip_assume_tac) >>
  metis_tac[]);

(* Theorem: WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ RISING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
                    in MONO2 body ==>
                       loop x y <= c + n * body (FUNPOW transform n x) (FUNPOW modify n y) *)
(* Proof: by loop2_rise_rise_count_cover_le with cover = body. *)
val loop2_rise_rise_count_le = store_thm(
  "loop2_rise_rise_count_le",
  ``!loop guard body c modify transform R.
      WF R /\ (!x y. ~guard x y ==> R (transform x,modify y) (x,y)) /\
      RISING transform /\ RISING modify /\
      (!x y. loop x y = if guard x y then c else body x y + loop (transform x) (modify y)) ==>
       !x y. let n = loop2_count guard modify transform x y
                    in MONO2 body ==>
                       loop x y <= c + n * body (FUNPOW transform n x) (FUNPOW modify n y)``,
  rpt strip_tac >>
  assume_tac loop2_rise_rise_count_cover_le >>
  first_x_assum (qspecl_then [`loop`, `guard`, `body`, `c`, `modify`, `transform`, `R`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);



(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
