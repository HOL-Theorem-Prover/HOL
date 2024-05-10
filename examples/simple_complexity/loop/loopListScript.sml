(* ------------------------------------------------------------------------- *)
(* Loop Recurrence with List argument                                        *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "loopList";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* Get dependent theories in lib *)
(* val _ = load "loopTheory"; *)
open loopTheory;

(* val _ = load "bitsizeTheory"; *)
open bitsizeTheory;

(* open dependent theories *)
open arithmeticTheory dividesTheory numberTheory combinatoricsTheory listTheory
     rich_listTheory listRangeTheory;

(* Overload sublist by infix operator *)
val _ = temp_overload_on ("<=", ``sublist``);

(* ------------------------------------------------------------------------- *)
(* Loop Recurrence with List argument Documentation                          *)
(* ------------------------------------------------------------------------- *)
(* Type and Overload:
   halving          = divide_by 2
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   List LENGTH as Count:
   list_length_eq_loop_count
                       |- !x. LENGTH x = loop_count (\x. x = []) TL x
   list_length_eq_loop2_count
                       |- !f x y. LENGTH y = loop2_count (\x y. y = []) TL f x y
   list_length_eq_loop2_tail_count
                       |- !x y. loop2_count (\x y. x = [] \/ y = []) TL TL x y =
                                MIN (LENGTH x) (LENGTH y)

   iterating_turn_eq_turn_exp
                       |- !x n. iterating turn x n = MAP (\n. turn_exp x n) [0 ..< n]
   iterating_tail_eqn  |- !n x. n <= LENGTH x ==> FUNPOW TL n x = DROP n x
   iterating_tail_length
                       |- !x. FUNPOW (\x. TL x) (LENGTH x) x = []

   List Reduction Loop:
   loop_list_count_eqn |- !loop body c.
                          (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
                           !x. loop x = c + SUM (GENLIST (\j. body (DROP j x)) (LENGTH x))
   loop_list_count_sum_le
                       |- !loop body exit c.
                          (!x. loop x =
                               if x = [] then c
                               else body x + if exit x then 0 else loop (TL x)) ==>
                           !x. loop x <= c + SUM (GENLIST (\j. body (DROP j x)) (LENGTH x))
   loop_list_count_cover_exit_le
                   |- !loop body c cover exit.
                      (!x. body x <= cover x) /\ (!x y. x <= y ==> cover x <= cover y) /\
                      (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
                       !x. loop x <= c + cover x * LENGTH x
   loop_list_count_exit_le
                   |- !loop body c exit. (!x y. x <= y ==> body x <= body y) /\
                      (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
                       !x. loop x <= c + body x * LENGTH x
   loop_list_count_cover_le
                   |- !loop body c cover.
                      (!x. body x <= cover x) /\ (!x y. x <= y ==> cover x <= cover y) /\
                      (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
                       !x. loop x <= c + cover x * LENGTH x
   loop_list_count_le
                   |- !loop body c. (!x y. x <= y ==> body x <= body y) /\
                      (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
                       !x. loop x <= c + body x * LENGTH x
   loop_list_count_constant_cover_exit_le
                   |- !loop k exit c body.
                      (!x. body x <= k) /\
                      (!x. loop x =
                           if x = [] then c
                           else body x + if exit x then 0 else loop (TL x)) ==>
                       !x. loop x <= c + k * LENGTH x
   loop_list_count_constant_cover_le
                   |- !loop k c body.
                      (!x. body x <= k) /\
                      (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
                       !x. loop x <= c + k * LENGTH x

   List Reduction Loop with Body on Head:
   loop_list_head_count_eqn
                   |- !loop body c f. body = (\x. f (HD x)) /\
                      (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
                       !x. loop x = c + SUM (GENLIST (\j. f (EL j x)) (LENGTH x))
   loop_list_head_count_cover_exit_sum_le
                   |- !loop body c cover exit f.
                      (!x. body x <= cover x) /\ cover = (\x. f (HD x)) /\
                      (!x. loop x =
                           if x = [] then c
                           else body x + if exit x then 0 else loop (TL x)) ==>
                       !x. loop x <= c + SUM (GENLIST (\j. f (EL j x)) (LENGTH x))
   loop_list_head_count_exit_sum_le
                   |- !loop body c exit f. body = (\x. f (HD x)) /\
                      (!x. loop x =
                           if x = [] then c
                           else body x + if exit x then 0 else loop (TL x)) ==>
                       !x. loop x <= c + SUM (GENLIST (\j. f (EL j x)) (LENGTH x))
   loop_list_head_count_cover_sum_le
                   |- !loop body c cover f.
                      (!x. body x <= cover x) /\ cover = (\x. f (HD x)) /\
                      (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
                       !x. loop x <= c + SUM (GENLIST (\j. f (EL j x)) (LENGTH x))

   loop_list_head_bound_count_cover_exit_le
                   |- !loop body c cover exit f.
                      (!x. body x <= cover x) /\ cover = (\x. f (HD x)) /\ MONO f /\
                      (!x. loop x =
                           if x = [] then c
                           else body x + if exit x then 0 else loop (TL x)) ==>
                       !x n. EVERY (\j. j <= n) x ==> loop x <= c + LENGTH x * f n
   loop_list_head_bound_count_exit_le
                   |- !loop body c exit f. body = (\x. f (HD x)) /\ MONO f /\
                      (!x. loop x =
                           if x = [] then c
                           else body x + if exit x then 0 else loop (TL x)) ==>
                       !x n. EVERY (\j. j <= n) x ==> loop x <= c + LENGTH x * f n
   loop_list_head_bound_count_cover_le
                   |- !loop body c cover f.
                      (!x. body x <= cover x) /\ cover = (\x. f (HD x)) /\ MONO f /\
                      (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
                       !x n. EVERY (\j. j <= n) x ==> loop x <= c + LENGTH x * f n
   loop_list_head_bound_count_le
                   |- !loop body c f. body = (\x. f (HD x)) /\ MONO f /\
                      (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
                       !x n. EVERY (\j. j <= n) x ==> loop x <= c + LENGTH x * f n

   loop_list_head_upper_count_cover_exit_le
                   |- !loop body c cover exit f.
                      (!x. body x <= cover x) /\ cover = (\x. f (HD x)) /\ MONO f /\
                      (!x. loop x =
                           if x = [] then c
                           else body x + if exit x then 0 else loop (TL x)) ==>
                       !x n. EVERY (\j. j < n) x ==> loop x <= c + LENGTH x * f n
   loop_list_head_upper_count_exit_le
                   |- !loop body c exit f. body = (\x. f (HD x)) /\ MONO f /\
                      (!x. loop x =
                           if x = [] then c
                           else body x + if exit x then 0 else loop (TL x)) ==>
                       !x n. EVERY (\j. j < n) x ==> loop x <= c + LENGTH x * f n
   loop_list_head_upper_count_cover_le
                   |- !loop body c cover f.
                      (!x. body x <= cover x) /\ cover = (\x. f (HD x)) /\ MONO f /\
                      (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
                       !x n. EVERY (\j. j < n) x ==> loop x <= c + LENGTH x * f n
   loop_list_head_upper_count_le
                   |- !loop body c f. body = (\x. f (HD x)) /\ MONO f /\
                      (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
                       !x n. EVERY (\j. j < n) x ==> loop x <= c + LENGTH x * f n

   List Reduction Loop with Transform:
   loop2_list_count_eqn
                   |- !loop f body c.
                      (!x y. loop x y = if y = [] then c else body x y + loop (f x) (TL y)) ==>
                       !x y. loop x y =
                             c + SUM (GENLIST (\j. body (FUNPOW f j x) (DROP j y)) (LENGTH y))
   loop2_list_count_sum_le
                   |- !loop f body exit c.
                      (!x y. loop x y =
                             if y = [] then c
                             else body x y + if exit x y then 0 else loop (f x) (TL y)) ==>
                       !x y. loop x y <=
                             c + SUM (GENLIST (\j. body (FUNPOW f j x) (DROP j y)) (LENGTH y))

   List Reduction Loop with Tail Transform:
   loop2_list_tail_count_eqn
                   |- !loop body quit.
                      (!x y. loop x y =
                             if x = [] \/ y = [] then quit x y
                             else body x y + loop (TL x) (TL y)) ==>
                       !x y. loop x y = quit (FUNPOW TL (MIN (LENGTH x) (LENGTH y)) x)
                                             (FUNPOW TL (MIN (LENGTH x) (LENGTH y)) y) +
                             SUM (GENLIST (\j. body (DROP j x) (DROP j y)) (MIN (LENGTH x) (LENGTH y)))
   loop2_list_tail_count_sum_le
                   |- !loop body quit exit.
                      (!x y. loop x y =
                             if x = [] \/ y = [] then quit x y
                             else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
                       !x y. loop x y <= quit (FUNPOW TL (MIN (LENGTH x) (LENGTH y)) x)
                                              (FUNPOW TL (MIN (LENGTH x) (LENGTH y)) y) +
                             SUM (GENLIST (\j. body (DROP j x) (DROP j y)) (MIN (LENGTH x) (LENGTH y)))

   List Reduction Loop with Tail Transform and Body on Heads:
   loop2_list_tail_head_count_eqn
                   |- !loop body quit.
                      (!x y. loop x y =
                             if x = [] \/ y = [] then quit x y
                             else body x y + loop (TL x) (TL y)) ==>
                       !x y k f. LENGTH x = k /\ LENGTH y = k /\ body = (\x y. f (HD x) (HD y)) ==>
                                 loop x y = quit [] [] + SUM (GENLIST (\j. f (EL j x) (EL j y)) k)
   loop2_list_tail_head_count_cover_exit_sum_le
                   |- !loop body quit cover exit f.
                      (!x y. body x y <= cover x y) /\ cover = (\x y. f (HD x) (HD y)) /\
                      (!x y. loop x y =
                             if x = [] \/ y = [] then quit x y
                             else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
                       !x y k. LENGTH x = k /\ LENGTH y = k ==>
                               loop x y <= quit [] [] + SUM (GENLIST (\j. f (EL j x) (EL j y)) k)
   loop2_list_tail_head_count_cover_sum_le
                   |- !loop body quit cover f.
                      (!x y. body x y <= cover x y) /\ cover = (\x y. f (HD x) (HD y)) /\
                      (!x y. loop x y =
                             if x = [] \/ y = [] then quit x y
                             else body x y + loop (TL x) (TL y)) ==>
                       !x y k. LENGTH x = k /\ LENGTH y = k ==>
                               loop x y <= quit [] [] + SUM (GENLIST (\j. f (EL j x) (EL j y)) k)
   loop2_list_tail_head_count_exit_sum_le
                   |- !loop body quit exit f. body = (\x y. f (HD x) (HD y)) /\
                      (!x y. loop x y =
                             if x = [] \/ y = [] then quit x y
                             else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
                       !x y k. LENGTH x = k /\ LENGTH y = k ==>
                               loop x y <= quit [] [] + SUM (GENLIST (\j. f (EL j x) (EL j y)) k)

   loop2_list_tail_head_bound_count_cover_exit_le
                   |- !loop body quit cover exit f.
                      (!x y. body x y <= cover x y) /\ cover = (\x y. f (HD x) (HD y)) /\ MONO2 f /\
                      (!x y. loop x y =
                             if x = [] \/ y = [] then quit x y
                             else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
                       !x y k n. LENGTH x = k /\ LENGTH y = k /\
                                 EVERY (\j. j <= n) x /\ EVERY (\j. j <= n) y ==>
                                 loop x y <= quit [] [] + k * f n n
   loop2_list_tail_head_bound_count_exit_le
                   |- !loop body quit exit f. body = (\x y. f (HD x) (HD y)) /\ MONO2 f /\
                      (!x y. loop x y =
                             if x = [] \/ y = [] then quit x y
                             else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
                       !x y k n. LENGTH x = k /\ LENGTH y = k /\
                                 EVERY (\j. j <= n) x /\ EVERY (\j. j <= n) y ==>
                                 loop x y <= quit [] [] + k * f n n
   loop2_list_tail_head_bound_count_cover_le
                   |- !loop body quit cover f.
                      (!x y. body x y <= cover x y) /\ cover = (\x y. f (HD x) (HD y)) /\ MONO2 f /\
                      (!x y. loop x y =
                             if x = [] \/ y = [] then quit x y
                             else body x y + loop (TL x) (TL y)) ==>
                       !x y k n. LENGTH x = k /\ LENGTH y = k /\
                                 EVERY (\j. j <= n) x /\ EVERY (\j. j <= n) y ==>
                                 loop x y <= quit [] [] + k * f n n
   loop2_list_tail_head_bound_count_le
                   |- !loop body quit f. body = (\x y. f (HD x) (HD y)) /\ MONO2 f /\
                      (!x y. loop x y =
                             if x = [] \/ y = [] then quit x y
                             else body x y + loop (TL x) (TL y)) ==>
                       !x y k n. LENGTH x = k /\ LENGTH y = k /\
                                 EVERY (\j. j <= n) x /\ EVERY (\j. j <= n) y ==>
                                 loop x y <= quit [] [] + k * f n n

   loop2_list_tail_head_upper_count_cover_exit_le
                   |- !loop body quit cover exit f.
                      (!x y. body x y <= cover x y) /\ cover = (\x y. f (HD x) (HD y)) /\ MONO2 f /\
                      (!x y. loop x y =
                             if x = [] \/ y = [] then quit x y
                             else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
                       !x y k n. LENGTH x = k /\ LENGTH y = k /\
                                 EVERY (\j. j < n) x /\ EVERY (\j. j < n) y ==>
                                 loop x y <= quit [] [] + k * f n n
   loop2_list_tail_head_upper_count_exit_le
                   |- !loop body quit exit f. body = (\x y. f (HD x) (HD y)) /\ MONO2 f /\
                      (!x y. loop x y =
                             if x = [] \/ y = [] then quit x y
                             else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
                       !x y k n. LENGTH x = k /\ LENGTH y = k /\
                                 EVERY (\j. j < n) x /\ EVERY (\j. j < n) y ==>
                                 loop x y <= quit [] [] + k * f n n
   loop2_list_tail_head_upper_count_cover_le
                   |- !loop body quit cover f.
                      (!x y. body x y <= cover x y) /\ cover = (\x y. f (HD x) (HD y)) /\ MONO2 f /\
                      (!x y. loop x y =
                             if x = [] \/ y = [] then quit x y
                             else body x y + loop (TL x) (TL y)) ==>
                       !x y k n. LENGTH x = k /\ LENGTH y = k /\
                                 EVERY (\j. j < n) x /\ EVERY (\j. j < n) y ==>
                                 loop x y <= quit [] [] + k * f n n
   loop2_list_tail_head_upper_count_le
                   |- !loop body quit f. body = (\x y. f (HD x) (HD y)) /\ MONO2 f /\
                      (!x y. loop x y =
                             if x = [] \/ y = [] then quit x y
                             else body x y + loop (TL x) (TL y)) ==>
                       !x y k n. LENGTH x = k /\ LENGTH y = k /\
                                 EVERY (\j. j < n) x /\ EVERY (\j. j < n) y ==>
                                 loop x y <= quit [] [] + k * f n n

   List Reduction Loop with Turn Transform:
   loop2_list_turn_count_eqn
                   |- !loop body quit.
                      (!x y. loop x y =
                             if y = [] then quit x
                             else body x y + loop (turn x) (TL y)) ==>
                       !x y. loop x y = quit (turn_exp x (LENGTH y)) +
                             SUM (GENLIST (\j. body (turn_exp x j) (DROP j y)) (LENGTH y))
   loop2_list_turn_count_sum_le
                   |- !loop body quit exit.
                      (!x y. loop x y =
                             if y = [] then quit x
                             else body x y + if exit x y then 0 else loop (turn x) (TL y)) ==>
                       !x y. loop x y <= quit (turn_exp x (LENGTH y)) +
                             SUM (GENLIST (\j. body (turn_exp x j) (DROP j y)) (LENGTH y))

   List Reduction Loop with Tail Transform and Body on Head:
   loop2_list_turn_head_count_eqn
                   |- !loop body quit f g. body = (\x y. f (g x) (HD y)) /\
                      (!x y. loop x y = if y = [] then quit x else body x y + loop (turn x) (TL y)) ==>
                       !x y. loop x y = quit (turn_exp x (LENGTH y)) +
                             SUM (GENLIST (\j. f (g (turn_exp x j)) (EL j y)) (LENGTH y))
   loop2_list_turn_head_count_cover_exit_sum_le
                   |- !loop body quit cover exit.
                      (!x y. loop x y =
                             if y = [] then quit x
                             else body x y + if exit x y then 0 else loop (turn x) (TL y)) ==>
                       !x y. (!j. j < LENGTH y ==> body (turn_exp x j) (DROP j y) <= cover j) ==>
                             loop x y <= quit (turn_exp x (LENGTH y)) + SUM (GENLIST cover (LENGTH y))
   loop2_list_turn_head_count_cover_exit_le
                   |- !loop body quit cover exit. MONO cover /\
                      (!x y. loop x y =
                             if y = [] then quit x
                             else body x y + if exit x y then 0 else loop (turn x) (TL y)) ==>
                       !x y. (!j. j < LENGTH y ==> body (turn_exp x j) (DROP j y) <= cover j) ==>
                             loop x y <= quit (turn_exp x (LENGTH y)) + LENGTH y * cover (LENGTH y)
   loop2_list_turn_head_count_cover_le
                   |- !loop body quit cover. MONO cover /\
                      (!x y. loop x y = if y = [] then quit x else body x y + loop (turn x) (TL y)) ==>
                       !x y. (!j. j < LENGTH y ==> body (turn_exp x j) (DROP j y) <= cover j) ==>
                             loop x y <= quit (turn_exp x (LENGTH y)) + LENGTH y * cover (LENGTH y)

   Original:
   Diminishing List:
   diminishing_def     |- !ls. diminishing ls = if ls = [] then [] else ls::diminishing (TL ls)
   diminishing_nil     |- diminishing [] = []
   diminishing_cons    |- !h t. diminishing (h::t) = (h::t)::diminishing t
   diminishing_length  |- !ls. LENGTH (diminishing ls) = LENGTH ls
   diminishing_element |- !ls j. j < LENGTH ls ==> EL j (diminishing ls) = DROP j ls
   diminishing_member  |- !ls j. j < LENGTH ls ==> MEM (DROP j ls) (diminishing ls)
   diminishing_eqn     |- !ls. diminishing ls = MAP (\j. DROP j ls) [0 ..< LENGTH ls]
   diminishing_head_map|- !f x k. LENGTH x = k ==>
                                  MAP (\x. f (HD x)) (diminishing x) = MAP (\j. f (EL j x)) [0 ..< k]
   diminishing_head2_map
                       |- !f x y k. LENGTH x = k /\ LENGTH y = k ==>
                                    MAP2 (\x y. f (HD x) (HD y)) (diminishing x) (diminishing y) =
                                    MAP (\j. f (EL j x) (EL j y)) [0 ..< k]
   diminishing_eq_loop_arg
                       |- !x. diminishing x = loop_arg (\x. x = []) TL x
   iterating_diminishing_eq_loop2_arg
                       |- !body f x y. MAP2 body (iterating f x (LENGTH y)) (diminishing y) =
                                       MAP (UNCURRY body) (loop2_arg (\x y. y = []) TL f x y)
   iterating_diminishing_both_eq_loop2_arg
                       |- !body x y. MAP2 body (diminishing x) (diminishing y) =
                                     MAP (UNCURRY body) (loop2_arg (\x y. x = [] \/ y = []) TL TL x y)
   iterating_tail_eq_diminishing
                       |- !x. iterating TL x (LENGTH x) = diminishing x

   loop_list_count_by_sum
                   |- !loop body c. (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
                      !x. loop x = c + SUM (MAP body (diminishing x))
   loop_list_count_exit_by_sum
                   |- !loop body c exit.
                      (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
                       !x. loop x <= c + SUM (MAP body (diminishing x))

   loop2_list_count_by_sum
                   |- !loop f body c.
                      (!x y. loop x y = if y = [] then c else body x y + loop (f x) (TL y)) ==>
                       !x y. loop x y = c + SUM (MAP2 body (iterating f x (LENGTH y)) (diminishing y))
   loop2_list_count_exit_by_sum
                   |- !loop f body c exit.
                      (!x y. loop x y =
                             if y = [] then c
                             else body x y + if exit x y then 0 else loop (f x) (TL y)) ==>
                       !x y. loop x y <= c + SUM (MAP2 body (iterating f x (LENGTH y)) (diminishing y))
   loop2_list_count_cover_exit_upper
                   |- !loop f body cover exit c.
                      (!x y. body x y <= cover x y) /\
                      (!x1 x2 y1 y2. LENGTH y1 <= LENGTH y2 ==> cover x1 y1 <= cover x2 y2) /\
                      (!x y. loop x y =
                             if y = [] then c
                             else body x y + if exit x y then 0 else loop (f x) (TL y)) ==>
                       !x y. loop x y <= c + cover x y * LENGTH y
   loop2_list_count_exit_upper
                   |- !loop f body exit c.
                      (!x1 x2 y1 y2. LENGTH y1 <= LENGTH y2 ==> body x1 y1 <= body x2 y2) /\
                      (!x y. loop x y =
                             if y = [] then c
                             else body x y + if exit x y then 0 else loop (f x) (TL y)) ==>
                       !x y. loop x y <= c + body x y * LENGTH y
   loop2_list_count_cover_upper
                   |- !loop f body cover c.
                      (!x y. body x y <= cover x y) /\
                      (!x1 x2 y1 y2. LENGTH y1 <= LENGTH y2 ==> cover x1 y1 <= cover x2 y2) /\
                      (!x y. loop x y = if y = [] then c else body x y + loop (f x) (TL y)) ==>
                       !x y. loop x y <= c + cover x y * LENGTH y
   loop2_list_count_upper
                   |- !loop f body c.
                      (!x1 x2 y1 y2. LENGTH y1 <= LENGTH y2 ==> body x1 y1 <= body x2 y2) /\
                      (!x y. loop x y = if y = [] then c else body x y + loop (f x) (TL y)) ==>
                       !x y. loop x y <= c + body x y * LENGTH y

   loop2_list_tail_count_by_sum
                   |- !loop body c.
                      (!x y. loop x y = if x = [] \/ y = [] then c else body x y + loop (TL x) (TL y)) ==>
                       !x y. loop x y = c + SUM (MAP2 body (diminishing x) (diminishing y))
   loop2_list_tail_count_exit_by_sum
                   |- !loop body c exit.
                      (!x y. loop x y =
                             if x = [] \/ y = [] then c
                             else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
                       !x y. loop x y <= c + SUM (MAP2 body (diminishing x) (diminishing y))

   loop2_list_tail_head_count_by_sum
                   |- !loop body c.
                      (!x y. loop x y =
                             if x = [] \/ y = [] then c
                             else body x y + loop (TL x) (TL y)) ==>
                       !x y k f. LENGTH x = k /\ LENGTH y = k /\ body = (\x y. f (HD x) (HD y)) ==>
                                 loop x y = c + SUM (MAP (\j. f (EL j x) (EL j y)) [0 ..< k])
   loop2_list_tail_head_count_cover_exit_by_sum
                   |- !loop body c exit.
                      (!x y. loop x y =
                             if x = [] \/ y = [] then c
                             else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
                       !x y k f cover. LENGTH x = k /\ LENGTH y = k /\
                                       (!x y. body x y <= cover x y) /\
                                       cover = (\x y. f (HD x) (HD y)) ==>
                                       loop x y <= c + SUM (MAP (\j. f (EL j x) (EL j y)) [0 ..< k])
   loop2_list_tail_head_count_exit_by_sum
                   |- !loop body c exit.
                      (!x y. loop x y =
                             if x = [] \/ y = [] then c
                             else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
                       !x y k f. LENGTH x = k /\ LENGTH y = k /\ body = (\x y. f (HD x) (HD y)) ==>
                                 loop x y <= c + SUM (MAP (\j. f (EL j x) (EL j y)) [0 ..< k])
*)

(* ------------------------------------------------------------------------- *)
(* Loop Recurrence with List argument                                        *)
(* ------------------------------------------------------------------------- *)

(* Note:
   listRangeLHI_MAP  |- !f n. MAP f [0 ..< n] = GENLIST f n
   For pretty-printing,
   SUM (GENLIST f n) is better, corresponding to: SIGMA f (count n)
   SUM_GENLIST_THM   |- !f n. SUM (GENLIST f n) = SIGMA f (count n)
*)

(* ------------------------------------------------------------------------- *)
(* List LENGTH as Count.                                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: LENGTH x = loop_count (\x. x = []) TL x *)
(* Proof:
   By induction on list x.
   Let guard = (\x. x = []),
       R = measure (\x. LENGTH x).
   Then WF R                                  by WF_measure
    and !x. ~guard x ==> (R (TL x) x)         by LENGTH_TL_LT
   Base: LENGTH [] = loop_count guard TL []
      Note guard []                           by notation
           LENGTH []
         = 0                                  by LENGTH
         = loop_count guard modify []         by loop_count_0, guard []
   Step: LENGTH x = loop_count guard TL x ==>
         !h. LENGTH (h::x) = loop_count guard TL (h::x)
      Note ~guard (h::x)                      by notation
           LENGTH (h::x)
         = SUC (LENGTH x)                     by LENGTH
         = SUC (loop_count guard TL x)        by induction hypothesis
         = loop_count guard TL (h::x)         by loop_count_suc, ~guard (h::x)
*)
val list_length_eq_loop_count = store_thm(
  "list_length_eq_loop_count",
  ``!x. LENGTH x = loop_count (\x. x = []) TL x``,
  qabbrev_tac `guard = \x. x = []` >>
  qabbrev_tac `R = measure (\x. LENGTH x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> (R (TL x) x)` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  Induct >| [
    `guard []` by rw[Abbr`guard`] >>
    metis_tac[LENGTH, loop_count_0],
    rpt strip_tac >>
    `~guard (h::x)` by rw[Abbr`guard`] >>
    metis_tac[LENGTH, loop_count_suc, TL]
  ]);

(* Theorem: LENGTH y = loop2_count (\x y. y = []) TL f x y *)
(* Proof:
   By induction on list y.
   Let guard = (\x y. y = []),
       R = measure (\(x,y). LENGTH y).
   The goal is: LENGTH y = loop2_count guard TL f x y

   Note WF R                                     by WF_measure
    and !x y. ~guard x y ==> R (f x,TL y) (x,y)  by LENGTH_TL_LT, LENGTH (TL y) < LENGTH y
   If guard x y,
      Then y = []                                by guard x y
           LENGTH []
         = 0                                     by LENGTH
         = loop2_count guard TL f x 0            by loop2_count_0, guard x y
   If ~guard x y,
      Then y <> [], or y = h::t                  by ~guard x y
           LENGTH y
         = SUC (LENGTH t)                        by LENGTH
         = SUC (loop2_count guard TL f (f x) t)  by induction hypothesis, take (f x).
         = loop2_count guard TL f x y            by loop2_count_suc
*)
val list_length_eq_loop2_count = store_thm(
  "list_length_eq_loop2_count",
  ``!f x y. LENGTH y = loop2_count (\x y. y = []) TL f x y``,
  strip_tac >>
  qabbrev_tac `guard = \x y. y = []` >>
  qabbrev_tac `R = measure (\(x,y). LENGTH y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,TL y) (x,y)` by rw[LENGTH_TL_LT, Abbr`guard`,Abbr`R`] >>
  Induct_on `y` >-
  metis_tac[LENGTH, loop2_count_0] >>
  rpt strip_tac >>
  `~guard x (h::y)` by rw[Abbr`guard`] >>
  `LENGTH (h::y) = SUC (LENGTH y)` by rw[] >>
  `_ = SUC (loop2_count guard TL f (f x) y)` by metis_tac[NOT_LESS] >>
  `_ = loop2_count guard TL f x (h::y)` by metis_tac[loop2_count_suc, TL] >>
  decide_tac);

(* Theorem: loop2_count (\x y. x = [] \/ y = []) TL TL x y = MIN (LENGTH x) (LENGTH y) *)
(* Proof:
   By induction on list y.
   Let guard = (\x y. x = [] \/ y = []),
       R = measure (\(x,y). LENGTH y).
   The goal is: loop2_count guard TL TL x y = MIN (LENGTH x) (LENGTH y)

   Note WF R                                     by WF_measure
    and !x y. ~guard x y ==> R (TL x,TL y) (x,y) by LENGTH_TL_LT, LENGTH (TL y) < LENGTH y
   If guard x y,
      Then x = [] \/ y = []                      by guard x y
           loop2_count guard TL TL x 0
         = 0                                     by loop2_count_0, guard x y
         = MIN 0 0                               by MIN_IDEM
         = MIN (LENGTH x) (LENGTH y)             by LENGTH, x = [] or y = {}
   If ~guard x y,
      Then x <> [] /\ y <> [],                   by ~guard x y
      Let x = k::s, y = h::t.
           loop2_count guard TL TL (k::s) (h::t)
         = SUC (loop2_count guard TL TL s t)     by loop2_count_suc
         = SUC (MIN (LENGTH s) (LENGTH t))       by nduction hypothesis
         = MIN (SUC (LENGTH s)) (SUC (LENGTH t)) by MIN_SUC
         = MIN (LENGTH (k::s)) (LENGTH (h::t))   by LENGTH
*)
val list_length_eq_loop2_tail_count = store_thm(
  "list_length_eq_loop2_tail_count",
  ``!x y. loop2_count (\x y. x = [] \/ y = []) TL TL x y = MIN (LENGTH x) (LENGTH y)``,
  qabbrev_tac `guard = \x y. x = [] \/ y = []` >>
  qabbrev_tac `R = measure (\(x:'a list,y). LENGTH y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (TL x,TL y) (x,y)` by rw[LENGTH_TL_LT, Abbr`guard`,Abbr`R`] >>
  Induct_on `y` >| [
    simp[] >>
    metis_tac[loop2_count_0],
    rpt strip_tac >>
    Cases_on `x` >| [
      simp[] >>
      metis_tac[loop2_count_0],
      `~guard (h'::t) (h::y)` by rw[Abbr`guard`] >>
      `loop2_count guard TL TL (h'::t) (h::y) = SUC (loop2_count guard TL TL t y)` by metis_tac[loop2_count_suc, TL] >>
      `_ = SUC (MIN (LENGTH t) (LENGTH y))` by rw[] >>
      `_ = MIN (SUC (LENGTH t)) (SUC (LENGTH y))` by rw[MIN_SUC] >>
      `_ = MIN (LENGTH (h'::t)) (LENGTH (h::y))` by rw[] >>
      decide_tac
    ]
  ]);

(* Theorem: iterating turn x n = MAP (turn_exp x) [0 ..< n] *)
(* Proof:
   By induction on n.
   Base: !x. iterating turn x 0 = MAP (\n. turn_exp x n) [0 ..< 0]
         iterating turn x 0
       = []                            by iterating_nil
       = MAP (turn_exp x) []           by MAP
       = MAP (turn_exp x) [0 ..< 0]    by listRangeLHI_def
   Step: !x. iterating turn x n = MAP (turn_exp x) [0 ..< n] ==>
         !x. iterating turn x (SUC n) = MAP (\n. turn_exp x n) [0 ..< SUC n]
         iterating turn x (SUC n)
       = x::iterating turn (turn x) n                 by iterating_cons
       = x::MAP (turn_exp (turn x)) [0 ..< n]         by induction hypothesis
       = x::MAP (turn_exp o SUC) [0 ..< n]            by FUN_EQ_THM, turn_exp_SUC
       = x::MAP turn_exp [1 ..< n + 1]                by listRangeLHI_MAP_SUC
       = (turn_exp x 0)::MAP turn_exp [1 ..< n + 1]   by turn_exp_0
       = MAP turn_exp (0::[1 ..< n + 1])              by MAP
       = MAP turn_exp [0 ..< SUC n]                   by listRangeLHI_CONS, ADD1
*)
val iterating_turn_eq_turn_exp = store_thm(
  "iterating_turn_eq_turn_exp",
  ``!x n. iterating turn x n = MAP (turn_exp x) [0 ..< n]``,
  Induct_on `n` >-
  rw[iterating_nil] >>
  rw[iterating_cons] >>
  qabbrev_tac `f = \n. turn_exp x n` >>
  qabbrev_tac `g = \n. turn_exp (turn x) n` >>
  `g = f o SUC` by rw[FUN_EQ_THM, turn_exp_SUC, Abbr`f`, Abbr`g`] >>
  `x = f 0` by rw[turn_nil, Abbr`f`] >>
  rw[GSYM listRangeLHI_MAP_SUC, listRangeLHI_CONS, ADD1]);

(* Theorem: n <= LENGTH x ==> (FUNPOW TL n x = DROP n x) *)
(* Proof:
   By induction on n.
   Base: !x. 0 <= LENGTH x ==> FUNPOW TL 0 x = DROP 0 x
         FUNPOW TL 0 x
       = x                  by FUNPOW_0
       = DROP 0 x           by DROP_0
   Step: !x. n <= LENGTH x ==> FUNPOW TL n x = DROP n x ==>
         !x. SUC n <= LENGTH x ==> FUNPOW TL (SUC n) x = DROP (SUC n) x
       Since LENGTH x <> 0,
         x <> []                 by LENGTH_NIL
         Let x = h::t            by x <> []
         Then SUC n <= SUC (LENGTH t)
           or     n <= LENGTH t
         FUNPOW TL (SUC n) x
       = FUNPOW TL (SUC n) (h::t)
       = FUNPOW TL n (TL (h::t))    by FUNPOW
       = FUNPOW TL n t              by TL
       = DROP n t                   by induction hypothesis
       = DROP (SUC n) (h::t)        by DROP
       = DROP (SUC n) x
*)
val iterating_tail_eqn = store_thm(
  "iterating_tail_eqn",
  ``!n x. n <= LENGTH x ==> (FUNPOW TL n x = DROP n x)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  (Cases_on `x` >> fs[]) >>
  rw[FUNPOW, DROP]);

(* Theorem: FUNPOW (\x. TL x) (LENGTH x) x = [] *)
(* Proof:
   Let guard = (\x. x = []),
       modify = (\x. TL x),
       R = measure (\x. LENGTH x).
   Then WF R                                   by WF_measure
    and !x. ~guard x ==> R (modify x) x        by LENGTH_TL_LT
   Note LENGTH x = loop_count guard modify x   by list_length_eq_loop_count
    and guard (FUNPOW modify (loop_count guard modify x) x)   by loop_count_iterating
     or FUNPOW modify (loop_count guard modify x) x = []      by guard
   Or simply,
      FUNPOW (\x. TL x) (LENGTH x) x
    = DROP (LENGTH x) x                by iterating_tail_eqn
    = []                               by DROP_LENGTH_NIL
*)
val iterating_tail_length = store_thm(
  "iterating_tail_length",
  ``!x. FUNPOW (\x. TL x) (LENGTH x) x = []``,
  metis_tac[iterating_tail_eqn, DROP_LENGTH_NIL, LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)
(* List Reduction Loop                                                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
         !x. loop x = c + SUM (GENLIST (\j. body (DROP j x)) (LENGTH x)) *)
(* Proof:
   Let guard = (\x. x = []),
       R = measure (\x. LENGTH x).
   Then WF R                                  by WF_measure
    and !x. ~guard x ==> (R (TL x) x)         by LENGTH_TL_LT
   Let quit = (\x. c)
   Then !x. loop x = if guard x then quit x else body x + loop (TL x)
                                              by given
   Let f = (\j. body (FUNPOW TL j x)),
       n = loop_count guard TL x,
       z = FUNPOW TL n x.
   Note n = LENGTH x                          by list_length_eq_loop_count
    and f = \j. body (DROP j x)               by iterating_tail_eqn, EL_GENLIST, LIST_EQ
   Thus loop x
      = quit z + SUM (GENLIST f n)            by loop_modify_count_eqn
      = c + SUM (GENLIST f (LENGTH x))
      = c + SUM (GENLIST (\j. body (DROP j x)) (LENGTH x))
*)
val loop_list_count_eqn = store_thm(
  "loop_list_count_eqn",
  ``!loop body c. (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
         !x. loop x = c + SUM (GENLIST (\j. body (DROP j x)) (LENGTH x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = []` >>
  qabbrev_tac `R = measure (\x. LENGTH x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (TL x) x` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  qabbrev_tac `quit = \x:'a list. c` >>
  `!x. loop x = if guard x then quit x else body x + loop (TL x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_eqn >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  `loop_count guard TL x = LENGTH x` by rw[list_length_eq_loop_count, Abbr`guard`] >>
  qabbrev_tac `f = \j. body (FUNPOW TL j x)` >>
  qabbrev_tac `g = \j. body (DROP j x)` >>
  `GENLIST f (LENGTH x) = GENLIST g (LENGTH x)` by
  (irule LIST_EQ >>
  rw[iterating_tail_eqn, Abbr`f`, Abbr`g`]) >>
  metis_tac[]);

(* Theorem: (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
         !x. loop x <= c + SUM (GENLIST (\j. body (DROP j x)) (LENGTH x)) *)
(* Proof:
   Let guard = (\x. x = []),
       R = measure (\x. LENGTH x).
   Then WF R                                  by WF_measure
    and !x. ~guard x ==> (R (TL x) x)         by LENGTH_TL_LT
   Let quit = (\x. c)
   Then !x. loop x = if guard x then quit x else body x + loop (TL x)
                                              by given
   Let f = (\j. body (FUNPOW TL j x)),
       n = loop_count guard TL x,
       z = FUNPOW TL n x.
   Note n = LENGTH x                          by list_length_eq_loop_count
    and f = \j. body (DROP j x)               by iterating_tail_eqn, EL_GENLIST, LIST_EQ
   Thus loop x
     <= quit z + SUM (GENLIST f n)            by loop_modify_count_exit_le
      = c + SUM (GENLIST f (LENGTH x))
      = c + SUM (GENLIST (\j. body (DROP j x)) (LENGTH x))
*)
val loop_list_count_sum_le = store_thm(
  "loop_list_count_sum_le",
  ``!loop body exit c.
        (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
         !x. loop x <= c + SUM (GENLIST (\j. body (DROP j x)) (LENGTH x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = []` >>
  qabbrev_tac `R = measure (\x. LENGTH x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> R (TL x) x` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  qabbrev_tac `quit = \x:'a list. c` >>
  `!x. loop x = if guard x then quit x else body x + if exit x then 0 else loop (TL x)` by metis_tac[] >>
  imp_res_tac loop_modify_count_exit_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  `loop_count guard TL x = LENGTH x` by rw[list_length_eq_loop_count, Abbr`guard`] >>
  qabbrev_tac `f = \j. body (FUNPOW TL j x)` >>
  qabbrev_tac `g = \j. body (DROP j x)` >>
  `GENLIST f (LENGTH x) = GENLIST g (LENGTH x)` by
  (irule LIST_EQ >>
  rw[iterating_tail_eqn, Abbr`f`, Abbr`g`]) >>
  metis_tac[]);

(* TL is not a number function, so FALLING TL is type incompatible. *)

(* The following makes uses of sublist, in sublist_drop.
   The condition: x <= y ==> cover x <= cover y   with x sublist y
   is difficult to meet upon application.
   The only instance of application has cover independent of either x or y.
*)

(* Theorem: (!x. body x <= cover x) /\ (!x y. x <= y ==> cover x <= cover y) /\
            (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
             !x. loop x <= c + (cover x) * (LENGTH x) *)
(* Proof:
   Let n = LENGTH x,
       f = (\j. DROP j x),
       ls = GENLIST f k.
       loop x
    <= c + SUM (GENLIST (\j. body (DROP j x)) n)   by loop_list_count_sum_le
     = c + SUM (GENLIST (body o f) n)              by FUN_EQ_THM
     = c + SUM (MAP body ls)                       by MAP_GENLIST
    <= c + SUM (MAP (K (cover x)) ls)              by SUM_LE, EL_MAP, sublist_drop
     = c + (cover x) * LENGTH ls                   by SUM_MAP_K
     = c + (cover x) * n                           by LENGTH_GENLIST
*)
val loop_list_count_cover_exit_le = store_thm(
  "loop_list_count_cover_exit_le",
  ``!loop body c cover exit. (!x. body x <= cover x) /\ (!x y. x <= y ==> cover x <= cover y) /\
   (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
     !x. loop x <= c + (cover x) * (LENGTH x)``,
  rpt strip_tac >>
  imp_res_tac loop_list_count_sum_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `n = LENGTH x` >>
  qabbrev_tac `f = \j. DROP j x` >>
  qabbrev_tac `ls = GENLIST f n` >>
  `LENGTH ls = n` by rw[Abbr`ls`] >>
  `(\j. body (DROP j x)) = body o f` by rw[FUN_EQ_THM, Abbr`f`] >>
  `GENLIST (\j. body (DROP j x)) n = MAP body ls` by rw[MAP_GENLIST, Abbr`ls`] >>
  `SUM (GENLIST (\j. body (DROP j x)) n) = SUM (MAP body ls)` by rw[] >>
  `SUM (MAP body ls) <= SUM (MAP (K (cover x)) ls)` by
  (irule SUM_LE >>
  rw[EL_MAP, Abbr`f`, Abbr`ls`] >>
  `body (DROP k x) <= cover (DROP k x)` by rw[] >>
  `cover (DROP k x) <= cover x` by rw[sublist_drop] >>
  decide_tac) >>
  `SUM (MAP (K (cover x)) ls) = (cover x) * LENGTH ls` by rw[SUM_MAP_K] >>
  `_ = (cover x) * n` by rw[] >>
  decide_tac);

(* Other similar theorems -- directly *)

(* Theorem: (!x y. x <= y ==> body x <= body y) /\
            (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
             !x. loop x <= c + (body x) * (LENGTH x) *)
(* Proof: by loop_list_count_cover_exit_le with cover = body. *)
val loop_list_count_exit_le = store_thm(
  "loop_list_count_exit_le",
  ``!loop body c exit. (!x y. x <= y ==> body x <= body y) /\
   (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
     !x. loop x <= c + (body x) * (LENGTH x)``,
  metis_tac[loop_list_count_cover_exit_le, LESS_EQ_REFL]);

(* Theorem: (!x. body x <= cover x) /\ (!x y. x <= y ==> cover x <= cover y) /\
            (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
             !ls. loop ls <= c + (cover ls) * (LENGTH ls) *)
(* Proof: by loop_list_count_cover_exit_le with guard = K F. *)
val loop_list_count_cover_le = store_thm(
  "loop_list_count_cover_le",
  ``!loop body c cover. (!x. body x <= cover x) /\ (!x y. x <= y ==> cover x <= cover y) /\
   (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
    !x. loop x <= c + (cover x) * (LENGTH x)``,
  rpt strip_tac >>
  qabbrev_tac `guard = (\x:'a list. F)` >>
  metis_tac[loop_list_count_cover_exit_le]);

(* Theorem: (!x y. x <= y ==> body x <= body y) /\
            (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
            !x. loop x <= c + (body x) * (LENGTH x) *)
(* Proof: by loop_list_count_cover_le with cover = body. *)
val loop_list_count_le = store_thm(
  "loop_list_count_le",
  ``!loop body c. (!x y. x <= y ==> body x <= body y) /\
   (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
    !x. loop x <= c + (body x) * (LENGTH x)``,
  metis_tac[loop_list_count_cover_le, LESS_EQ_REFL]);

(* Obtain corollaries when cover is constant *)
val loop_list_count_constant_cover_exit_le = save_thm("loop_list_count_constant_cover_exit_le",
    loop_list_count_cover_exit_le
         |> SPEC_ALL
         |> Q.INST [`cover` |-> `\x. k`]
         |> CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss())[]))
         |> BETA_RULE |> GEN_ALL);
(*
> val loop_list_count_constant_cover_exit_le =
   |- !loop k exit c body.
          (!x. body x <= k) /\
          (!x. loop x =
               if x = [] then c
               else body x + if exit x then 0 else loop (TL x)) ==>
          !x. loop x <= c + k * LENGTH x: thm
*)

val loop_list_count_constant_cover_le = save_thm("loop_list_count_constant_cover_le",
    loop_list_count_cover_le
         |> SPEC_ALL
         |> Q.INST [`cover` |-> `\x. k`]
         |> CONV_RULE (LAND_CONV (SIMP_CONV (srw_ss())[]))
         |> BETA_RULE |> GEN_ALL);
(*
val loop_list_count_constant_cover_le =
   |- !loop k c body.
          (!x. body x <= k) /\
          (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
          !x. loop x <= c + k * LENGTH x: thm
*)

(* ------------------------------------------------------------------------- *)
(* List Reduction Loop with Body on Head                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
        !x k f. (LENGTH x = k) /\ (body = \x. f (HD x)) ==>
               loop x = c + SUM (MAP (\j. f (EL j x)) [0 ..< k]) *)
(* Proof:
   Given body = \x. f (HD x).
   Let k = LENGTH x.
     loop x
   = c + SUM (GENLIST (\j. body (DROP j x)) k)    by loop_list_count_eqn
   = c + SUM (GENLIST (\j. f (HD (DROP j x))) k)  by body = \x. f (HD x)
   = c + SUM (GENLIST (\j. f (EL j x)) k)         by LIST_EQ, HD_DROP
*)
val loop_list_head_count_eqn = store_thm(
  "loop_list_head_count_eqn",
  ``!loop body c f. (body = \x. f (HD x)) /\
       (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
        !x. loop x = c + SUM (GENLIST (\j. f (EL j x)) (LENGTH x))``,
  rpt strip_tac >>
  imp_res_tac loop_list_count_eqn >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  fs[] >>
  qabbrev_tac `k = LENGTH x` >>
  qabbrev_tac `f1 = \j. f (HD (DROP j x))` >>
  qabbrev_tac `f2 = \j. f (EL j x)` >>
  `GENLIST f1 k = GENLIST f2 k` by
  (irule LIST_EQ >>
  rw[HD_DROP, Abbr`f1`, Abbr`f2`]) >>
  metis_tac[]);

(* Theorem: (!x. body x <= cover x) /\ (cover = \x. f (HD x)) /\
    (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
     !x. loop x <= c + SUM (GENLIST (\j. f (EL j x)) (LENGTH x)) *)
(* Proof:
   Given cover = \x. f (HD x).
   Let k = LENGTH x.
      loop x
   <= c + SUM (GENLIST (\j. body (DROP j x)) k)    by loop_list_count_sum_le
   <= c + SUM (GENLIST (\j. cover (DROP j x)) k)   by SUM_LE, cover over body
    = c + SUM (GENLIST (\j. f (HD (DROP j x))) k)  by cover = \x. f (HD x)
    = c + SUM (GENLIST (\j. f (EL j x)) k)         by LIST_EQ, HD_DROP
*)
val loop_list_head_count_cover_exit_sum_le = store_thm(
  "loop_list_head_count_cover_exit_sum_le",
  ``!loop body c cover exit f. (!x. body x <= cover x) /\ (cover = \x. f (HD x)) /\
    (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
     !x. loop x <= c + SUM (GENLIST (\j. f (EL j x)) (LENGTH x))``,
  rpt strip_tac >>
  imp_res_tac loop_list_count_sum_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `k = LENGTH x` >>
  qabbrev_tac `f1 = \j. f (HD (DROP j x))` >>
  qabbrev_tac `f2 = \j. f (EL j x)` >>
  `SUM (GENLIST (\j. body (DROP j x)) k) <= SUM (GENLIST f1 k)` by
  (irule SUM_LE >>
  rw[Abbr`f1`] >>
  metis_tac[]) >>
  `GENLIST f1 k = GENLIST f2 k` by
    (irule LIST_EQ >>
  rw[HD_DROP, Abbr`f1`, Abbr`f2`]) >>
  qabbrev_tac `foo = !x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)` >>
  fs[]);

(* Other similar theorems -- directly *)

(* Theorem: (body = \x. f (HD x)) /\
    (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
     !x. loop x <= c + SUM (GENLIST (\j. f (EL j x)) (LENGTH x)) *)
(* Proof: by loop_list_head_count_cover_exit_sum_le with cover = body. *)
val loop_list_head_count_exit_sum_le = store_thm(
  "loop_list_head_count_exit_sum_le",
  ``!loop body c exit f. (body = \x. f (HD x)) /\
    (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
     !x. loop x <= c + SUM (GENLIST (\j. f (EL j x)) (LENGTH x))``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_list_head_count_cover_exit_sum_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Theorem:  (!x. body x <= cover x) /\ (cover = \x. f (HD x)) /\
    (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
     !x. loop x <= c + SUM (GENLIST (\j. f (EL j x)) (LENGTH x)) *)
(* Proof: by loop_list_head_count_cover_exit_sum_le with exit = F. *)
val loop_list_head_count_cover_sum_le = store_thm(
  "loop_list_head_count_cover_sum_le",
  ``!loop body c cover f. (!x. body x <= cover x) /\ (cover = \x. f (HD x)) /\
    (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
     !x. loop x <= c + SUM (GENLIST (\j. f (EL j x)) (LENGTH x))``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:'a list. F` >>
  `!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)` by metis_tac[] >>
  imp_res_tac loop_list_head_count_cover_exit_sum_le >>
  first_x_assum (qspec_then `x` strip_assume_tac));

(* Note: loop_list_head_count_cover_sum_le with cover = body is:
         loop_list_head_count_eqn, an equation. *)

(* ------------------------------------------------------------------------- *)

(* Theorem: (!x. body x <= cover x) /\ (cover = \x. f (HD x)) /\ MONO f /\
    (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
     !x n. EVERY (\j. j <= n) x ==> loop x <= c + (LENGTH x) * f n *)
(* Proof:
   Given cover = \x. f (HD x), MONO f,
   Let k = LENGTH x.
      loop x
   <= c + SUM (GENLIST (\j. f (EL j x)) k)    by loop_list_head_count_cover_exit_sum_le
   <= c + SUM (GENLIST (\j. f n) k)           by SUM_LE, EVERY_EL
    = c + (f n) * k                           by SUM_GENLIST_K
    = c + k * (f n)                           by MULT_COMM
*)
val loop_list_head_bound_count_cover_exit_le = store_thm(
  "loop_list_head_bound_count_cover_exit_le",
  ``!loop body c cover exit f. (!x. body x <= cover x) /\ (cover = \x. f (HD x)) /\ MONO f /\
    (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
     !x n. EVERY (\j. j <= n) x ==> loop x <= c + (LENGTH x) * f n``,
  rpt strip_tac >>
  imp_res_tac loop_list_head_count_cover_exit_sum_le >>
  first_x_assum (qspec_then `x` strip_assume_tac) >>
  qabbrev_tac `k = LENGTH x` >>
  `SUM (GENLIST (\j. f (EL j x)) k) <= SUM (GENLIST (K (f n)) k)` by
  (irule SUM_LE >>
  rw[] >>
  qabbrev_tac `P = \j. j <= n` >>
  `!j. P j = (j <= n)` by rw[Abbr`P`] >>
  metis_tac[EVERY_EL]) >>
  `SUM (GENLIST (K (f n)) k) <= f n * k` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Other similar theorems -- directly *)

(* Theorem: (body = \x. f (HD x)) /\ MONO f /\
    (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
     !x n. EVERY (\j. j <= n) x ==> loop x <= c + (LENGTH x) * f n *)
(* Proof: by loop_list_head_bound_count_cover_exit_le with cover = body. *)
val loop_list_head_bound_count_exit_le = store_thm(
  "loop_list_head_bound_count_exit_le",
  ``!loop body c exit f. (body = \x. f (HD x)) /\ MONO f /\
    (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
     !x n. EVERY (\j. j <= n) x ==> loop x <= c + (LENGTH x) * f n``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_list_head_bound_count_cover_exit_le);

(* Theorem: (!x. body x <= cover x) /\ (cover = \x. f (HD x)) /\ MONO f /\
    (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
     !x n. EVERY (\j. j <= n) x ==> loop x <= c + (LENGTH x) * f n *)
(* Proof: by loop_list_head_bound_count_cover_exit_le with exit = F. *)
val loop_list_head_bound_count_cover_le = store_thm(
  "loop_list_head_bound_count_cover_le",
  ``!loop body c cover f. (!x. body x <= cover x) /\ (cover = \x. f (HD x)) /\ MONO f /\
    (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
     !x n. EVERY (\j. j <= n) x ==> loop x <= c + (LENGTH x) * f n``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num list. F` >>
  `!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)` by metis_tac[] >>
  imp_res_tac loop_list_head_bound_count_cover_exit_le);

(* Theorem: (body = \x. f (HD x)) /\ MONO f /\
    (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
     !x n. EVERY (\j. j <= n) x ==> loop x <= c + (LENGTH x) * f n *)
(* Proof: by loop_list_head_bound_count_cover_le with cover = body. *)
val loop_list_head_bound_count_le = store_thm(
  "loop_list_head_bound_count_le",
  ``!loop body c f. (body = \x. f (HD x)) /\ MONO f /\
    (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
     !x n. EVERY (\j. j <= n) x ==> loop x <= c + (LENGTH x) * f n``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_list_head_bound_count_cover_le);

(* ------------------------------------------------------------------------- *)

(* Theorem: (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
     !x k n f. (LENGTH x = k) /\ EVERY (\j. j < n) x /\
                   (body = \x. f (HD x)) /\ MONO f ==>
                   loop x <= c + k * f n *)
(* Proof: by loop_list_head_bound_count_cover_exit_le, EVERY_LT_IMP_EVERY_LE. *)
val loop_list_head_upper_count_cover_exit_le = store_thm(
  "loop_list_head_upper_count_cover_exit_le",
  ``!loop body c cover exit f.
          (!x. body x <= cover x) /\ cover = (\x. f (HD x)) /\ MONO f /\
          (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
          !x n. EVERY (\j. j < n) x ==> loop x <= c + LENGTH x * f n``,
  rpt strip_tac >>
  `EVERY (\j. j <= n) x` by rw[EVERY_LT_IMP_EVERY_LE] >>
  imp_res_tac loop_list_head_bound_count_cover_exit_le);

(* Other similar theorems -- directly *)

(* Theorem: body = (\x. f (HD x)) /\ MONO f /\
          (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
          !x n. EVERY (\j. j < n) x ==> loop x <= c + LENGTH x * f n *)
(* Proof: by loop_list_head_upper_count_cover_exit_le with cover = body. *)
val loop_list_head_upper_count_exit_le = store_thm(
  "loop_list_head_upper_count_exit_le",
  ``!loop body c exit f. body = (\x. f (HD x)) /\ MONO f /\
          (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
          !x n. EVERY (\j. j < n) x ==> loop x <= c + LENGTH x * f n``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_list_head_upper_count_cover_exit_le);

(* Theorem: (!x. body x <= cover x) /\ cover = (\x. f (HD x)) /\ MONO f /\
          (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
          !x n. EVERY (\j. j < n) x ==> loop x <= c + LENGTH x * f n *)
(* Proof: by loop_list_head_upper_count_cover_exit_le with exit = F. *)
val loop_list_head_upper_count_cover_le = store_thm(
  "loop_list_head_upper_count_cover_le",
  ``!loop body c cover f.
          (!x. body x <= cover x) /\ cover = (\x. f (HD x)) /\ MONO f /\
          (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
          !x n. EVERY (\j. j < n) x ==> loop x <= c + LENGTH x * f n``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num list. F` >>
  `!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)` by metis_tac[] >>
  imp_res_tac loop_list_head_upper_count_cover_exit_le);

(* Theorem: body = (\x. f (HD x)) /\ MONO f /\
          (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
          !x n. EVERY (\j. j < n) x ==> loop x <= c + LENGTH x * f n *)
(* Proof: by loop_list_head_upper_count_cover_le with cover = body. *)
val loop_list_head_upper_count_le = store_thm(
  "loop_list_head_upper_count_le",
  ``!loop body c f. body = (\x. f (HD x)) /\ MONO f /\
          (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
          !x n. EVERY (\j. j < n) x ==> loop x <= c + LENGTH x * f n``,
  rpt strip_tac >>
  `!x. body x <= body x` by rw[] >>
  imp_res_tac loop_list_head_upper_count_cover_le);

(* ------------------------------------------------------------------------- *)
(* List Reduction Loop with Transform                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (!x y. loop x y = if y = [] then quit x else body x y + loop (f x) (TL y)) ==>
     !x y. loop x y = quit (FUNPOW f (LENGTH y) x) +
                      SUM (GENLIST (\j. body (FUNPOW f j x) (DROP j y)) (LENGTH y)) *)
(* Proof:
   Let guard = (\x y. y = []),
       R = measure (\(x,y). LENGTH y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,TL y) (x,y)    by LENGTH_TL_LT, LENGTH (TL x) < LENGTH x
   Let quit2 = (\x y. quit x).
   Then !x y. loop x y = if guard x y then quit2 x y else body x y + loop (f x) (TL y)
                                                   by given
   Let f = (\j. body (FUNPOW f j x) (FUNPOW TL j y)),
       n = loop2_count guard TL f x y),
       p = FUNPOW f n x,
       q = FUNPOW TL n y.
   Note n = LENGTH y                               by list_length_eq_loop2_count
    and f = (\j. body (FUNPOW f j x) (DROP j y))   by iterating_tail_eqn

        loop x y
      = quit2 p q + SUM (GENLIST f n)              by loop2_modify_count_eqn
      = quit p + SUM (GENLIST f (LENGTH y))        by n = LENGTH y
      = quit (FUNPOW f (LENGTH y) x) +
        SUM (GENLIST (\j. body (FUNPOW f j x) (DROP j y)) (LENGTH y))
*)
val loop2_list_count_eqn = store_thm(
  "loop2_list_count_eqn",
  ``!loop f body quit.
    (!x y. loop x y = if y = [] then quit x else body x y + loop (f x) (TL y)) ==>
     !x y. loop x y = quit (FUNPOW f (LENGTH y) x) +
                      SUM (GENLIST (\j. body (FUNPOW f j x) (DROP j y)) (LENGTH y))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. y = []` >>
  qabbrev_tac `R = measure (\(x,y). LENGTH y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,TL y) (x,y)` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  qabbrev_tac `quit2 = \x y:'b list. quit x` >>
  `!x y. loop x y = if guard x y then quit2 x y else body x y + loop (f x) (TL y)` by metis_tac[] >>
  imp_res_tac loop2_modify_count_eqn >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  `loop2_count guard TL f x y = LENGTH y` by rw[list_length_eq_loop2_count, Abbr`guard`] >>
  qabbrev_tac `u = \j. body (FUNPOW f j x) (FUNPOW TL j y)` >>
  qabbrev_tac `v = \j. body (FUNPOW f j x) (DROP j y)` >>
  `GENLIST u (LENGTH y) = GENLIST v (LENGTH y)` by
  (irule LIST_EQ >>
  rw[iterating_tail_eqn, Abbr`u`, Abbr`v`]) >>
  metis_tac[]);

(* Theorem: (!x y. loop x y = if y = [] then quit x else body x y + if exit x y then 0 else loop (f x) (TL y)) ==>
     !x y. loop x y <= quit (FUNPOW f (LENGTH y) x) +
                       SUM (GENLIST (\j. body (FUNPOW f j x) (DROP j y)) (LENGTH y)) *)
(* Proof:
   Let guard = (\x y. y = []),
       R = measure (\(x,y). LENGTH y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,TL y) (x,y)    by LENGTH_TL_LT, LENGTH (TL x) < LENGTH x
   Let quit2 = (\x y. quit x).
   Then !x y. loop x y = if guard x y then quit2 x y else body x y + if exit x y then 0 else loop (f x) (TL y)
                                                   by given
   Let f = (\j. body (FUNPOW f j x) (FUNPOW TL j y)),
       n = loop2_count guard TL f x y),
       p = FUNPOW f n x,
       q = FUNPOW TL n y.
   Note n = LENGTH y                               by list_length_eq_loop2_count
    and f = (\j. body (FUNPOW f j x) (DROP j y))   by iterating_tail_eqn
        loop x y
      = quit2 p q + SUM (GENLIST f n)              by loop2_modify_count_exit_le
      = quit p + SUM (GENLIST f (LENGTH y))        by n = LENGTH y
      = quit (FUNPOW f (LENGTH y) x) +
        SUM (GENLIST (\j. body (FUNPOW f j x) (DROP j y)) (LENGTH y))
*)
val loop2_list_count_sum_le = store_thm(
  "loop2_list_count_sum_le",
  ``!loop f body quit exit.
    (!x y. loop x y = if y = [] then quit x else body x y + if exit x y then 0 else loop (f x) (TL y)) ==>
     !x y. loop x y <= quit (FUNPOW f (LENGTH y) x) +
                       SUM (GENLIST (\j. body (FUNPOW f j x) (DROP j y)) (LENGTH y))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. y = []` >>
  qabbrev_tac `R = measure (\(x,y). LENGTH y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,TL y) (x,y)` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  qabbrev_tac `quit2 = \x y:'b list. quit x` >>
  `!x y. loop x y = if guard x y then quit2 x y else body x y + if exit x y then 0 else loop (f x) (TL y)` by metis_tac[] >>
  imp_res_tac loop2_modify_count_exit_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  `loop2_count guard TL f x y = LENGTH y` by rw[list_length_eq_loop2_count, Abbr`guard`] >>
  qabbrev_tac `u = \j. body (FUNPOW f j x) (FUNPOW TL j y)` >>
  qabbrev_tac `v = \j. body (FUNPOW f j x) (DROP j y)` >>
  `GENLIST u (LENGTH y) = GENLIST v (LENGTH y)` by
  (irule LIST_EQ >>
  rw[iterating_tail_eqn, Abbr`u`, Abbr`v`]) >>
  metis_tac[]);

(* TL is not a number function, so FALLING TL is type incompatible. *)

(* ------------------------------------------------------------------------- *)
(* List Reduction Loop with Tail Transform                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + loop (TL x) (TL y)) ==>
     !x y. loop x y = quit (FUNPOW TL (MIN (LENGTH x) (LENGTH y)) x)
                           (FUNPOW TL (MIN (LENGTH x) (LENGTH y)) y) +
           SUM (GENLIST (\j. body (DROP j x) (DROP j y)) (MIN (LENGTH x) (LENGTH y))) *)
(* Proof:
   Let guard = (\x y. x = [] \/ y = []),
       R = measure (\(x,y). LENGTH y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (TL x,TL y) (x,y)     by LENGTH_TL_LT, LENGTH (TL x) < LENGTH x
   Let quit (\x y. quit x).
   Then !x y. loop x y = if guard x y then c else body x y + loop (TL x) (TL y)
                                                     by given
   Let n = loop2_count guard TL TL x y.
   Note n = MIN (LENGTH x) (LENGTH y)                by list_length_eq_loop2_tail_count
        loop x y
      = quit (FUNPOW TL n x) (FUNPOW TL n y) +
        SUM (GENLIST (\j. body (FUNPOW TL j x) (FUNPOW TL j y)) n)    by loop2_modify_count_eqn
      = quit (FUNPOW TL n x) +
        SUM (GENLIST (\j. body (DROP j x) (DROP j y)) n)              by iterating_tail_eqn
*)
val loop2_list_tail_count_eqn = store_thm(
  "loop2_list_tail_count_eqn",
  ``!loop body quit.
    (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + loop (TL x) (TL y)) ==>
     !x y. loop x y = quit (FUNPOW TL (MIN (LENGTH x) (LENGTH y)) x)
                           (FUNPOW TL (MIN (LENGTH x) (LENGTH y)) y) +
           SUM (GENLIST (\j. body (DROP j x) (DROP j y)) (MIN (LENGTH x) (LENGTH y)))``,
  rpt strip_tac >>
  qabbrev_tac `n = MIN (LENGTH x) (LENGTH y)` >>
  qabbrev_tac `guard = \x y. x = [] \/ y = []` >>
  qabbrev_tac `R = measure (\(x:'a list,y:'b list). LENGTH y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (TL x,TL y) (x,y)` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  `!x y. loop x y = if guard x y then quit x y else body x y + loop (TL x) (TL y)` by metis_tac[] >>
  imp_res_tac loop2_modify_count_eqn >>
  last_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  `loop2_count guard TL TL x y = n` by rw[GSYM list_length_eq_loop2_tail_count, Abbr`n`] >>
  qabbrev_tac `f1 = \j. body (FUNPOW TL j x) (FUNPOW TL j y)` >>
  qabbrev_tac `f2 = \j. body (DROP j x) (DROP j y)` >>
  `GENLIST f1 n = GENLIST f2 n` by
  (irule LIST_EQ >>
  rw[Abbr`f1`, Abbr`f2`] >>
  qabbrev_tac `n = loop2_count guard TL TL x y` >>
  `n <= LENGTH x /\ n <= LENGTH y` by metis_tac[MIN_IS_MIN] >>
  `x' <= LENGTH x /\ x' <= LENGTH y` by decide_tac >>
  metis_tac[iterating_tail_eqn]) >>
  metis_tac[]);

(* Theorem: (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
     !x y. loop x y <= quit (FUNPOW TL (MIN (LENGTH x) (LENGTH y)) x)
                            (FUNPOW TL (MIN (LENGTH x) (LENGTH y)) y) +
           SUM (GENLIST (\j. body (DROP j x) (DROP j y)) (MIN (LENGTH x) (LENGTH y))) *)
(* Proof:
   Let guard = (\x y. x = [] \/ y = []),
       R = measure (\(x,y). LENGTH y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (TL x,TL y) (x,y)     by LENGTH_TL_LT, LENGTH (TL x) < LENGTH x
   Let quit (\x y. quit x).
   Then !x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (TL x) (TL y)
                                                     by given
   Let n = loop2_count guard TL TL x y.
   Note n = MIN (LENGTH x) (LENGTH y)                by list_length_eq_loop2_tail_count
        loop x y
     <= quit (FUNPOW TL n x) (FUNPOW TL n y) +
        SUM (GENLIST (\j. body (FUNPOW TL j x) (FUNPOW TL j y)) n)    by loop2_modify_count_exit_le
      = quit (FUNPOW TL n x) +
        SUM (GENLIST (\j. body (DROP j x) (DROP j y)) n)              by iterating_tail_eqn
*)
val loop2_list_tail_count_sum_le = store_thm(
  "loop2_list_tail_count_sum_le",
  ``!loop body quit exit.
    (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
     !x y. loop x y <= quit (FUNPOW TL (MIN (LENGTH x) (LENGTH y)) x)
                            (FUNPOW TL (MIN (LENGTH x) (LENGTH y)) y) +
           SUM (GENLIST (\j. body (DROP j x) (DROP j y)) (MIN (LENGTH x) (LENGTH y)))``,
  rpt strip_tac >>
  qabbrev_tac `n = MIN (LENGTH x) (LENGTH y)` >>
  qabbrev_tac `guard = \x y. x = [] \/ y = []` >>
  qabbrev_tac `R = measure (\(x:'a list,y:'b list). LENGTH y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (TL x,TL y) (x,y)` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  `!x y. loop x y = if guard x y then quit x y else body x y + if exit x y then 0 else loop (TL x) (TL y)` by metis_tac[] >>
  imp_res_tac loop2_modify_count_exit_le >>
  last_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  `loop2_count guard TL TL x y = n` by rw[GSYM list_length_eq_loop2_tail_count, Abbr`n`] >>
  qabbrev_tac `f1 = \j. body (FUNPOW TL j x) (FUNPOW TL j y)` >>
  qabbrev_tac `f2 = \j. body (DROP j x) (DROP j y)` >>
  `GENLIST f1 n = GENLIST f2 n` by
  (irule LIST_EQ >>
  rw[Abbr`f1`, Abbr`f2`] >>
  qabbrev_tac `n = loop2_count guard TL TL x y` >>
  `n <= LENGTH x /\ n <= LENGTH y` by metis_tac[MIN_IS_MIN] >>
  `x' <= LENGTH x /\ x' <= LENGTH y` by decide_tac >>
  metis_tac[iterating_tail_eqn]) >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* List Reduction Loop with Tail Transform and Body on Heads                 *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (body = \x y. f (HD x) (HD y)) /\
       (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + loop (TL x) (TL y)) ==>
        !x y k. (LENGTH x = k) /\ (LENGTH y = k) ==>
               loop x y = quit [][] + SUM (GENLIST (\j. f (EL j x) (EL j y)) k) *)
(* Proof:
   Given body = \x y. f (HD x) (HD y), k = LENGTH x = LENGTH y.
   Then MIN (LENGTH x) (LENGTH y) = k                 by MIN_IDEM
     loop x y
   = quit (FUNPOW TL k x) (FUNPOW TL k y) + SUM (GENLIST (\j. body (DROP j x) (DROP j y)) k)
                                                      by loop2_list_tail_count_eqn
   = quit [][] + SUM (GENLIST (\j. f (EL j x) (EL j y)) k)
                                                      by iterating_tail_length, LIST_EQ, HD_DROP
*)
val loop2_list_tail_head_count_eqn = store_thm(
  "loop2_list_tail_head_count_eqn",
  ``!loop body quit f. (body = \x y. f (HD x) (HD y)) /\
       (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + loop (TL x) (TL y)) ==>
        !x y k. (LENGTH x = k) /\ (LENGTH y = k) ==>
               loop x y = quit [][] + SUM (GENLIST (\j. f (EL j x) (EL j y)) k)``,
  rpt strip_tac >>
  imp_res_tac loop2_list_tail_count_eqn >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  fs[MIN_IDEM] >>
  `FUNPOW TL k x = []` by metis_tac[iterating_tail_length] >>
  `FUNPOW TL k y = []` by metis_tac[iterating_tail_length] >>
  qabbrev_tac `f1 = \j. f (HD (DROP j x)) (HD (DROP j y))` >>
  qabbrev_tac `f2 = \j. f (EL j x) (EL j y)` >>
  `GENLIST f1 k = GENLIST f2 k` by
  (irule LIST_EQ >>
  rw[iterating_tail_eqn, Abbr`f1`, Abbr`f2`] >>
  metis_tac[HD_DROP]) >>
  metis_tac[]);

(* Theorem: (!x y. body x y <= cover x y) /\ (cover = \x y. f (HD x) (HD y)) /\
    (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
     !x y k. (LENGTH x = k) /\ (LENGTH y = k) ==>
     loop x y <= quit [][] + SUM (MAP (\j. f (EL j x) (EL j y)) [0 ..< k]) *)
(* Proof:
   Given body = \x y. f (HD x) (HD y), k = LENGTH x = LENGTH y.
   Then MIN (LENGTH x) (LENGTH y) = k                 by MIN_IDEM
      loop x y
   <= quit (FUNPOW TL k x) (FUNPOW TL k y) + SUM (GENLIST (\j. body (DROP j x) (DROP j y)) k)
                                                      by loop2_list_tail_count_sum_le
   <= quit (FUNPOW TL k x) (FUNPOW TL k y) + SUM (GENLIST (\j. cover (DROP j x) (DROP j y)) k)
                                                      by SUM_LE, cover over body
    = quit [][] + SUM (GENLIST (\j. f (EL j x) (EL j y)) k)
                                                      by iterating_tail_length, LIST_EQ, HD_DROP
*)
val loop2_list_tail_head_count_cover_exit_sum_le = store_thm(
  "loop2_list_tail_head_count_cover_exit_sum_le",
  ``!loop body quit cover exit f.
    (!x y. body x y <= cover x y) /\ (cover = \x y. f (HD x) (HD y)) /\
    (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
     !x y k. (LENGTH x = k) /\ (LENGTH y = k) ==>
     loop x y <= quit [][] + SUM (GENLIST (\j. f (EL j x) (EL j y)) k)``,
  rpt strip_tac >>
  imp_res_tac loop2_list_tail_count_sum_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `foo = !x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + if exit x y then 0 else loop (TL x) (TL y)` >>
  rfs[MIN_IDEM] >>
  `FUNPOW TL k x = []` by metis_tac[iterating_tail_length] >>
  `FUNPOW TL k y = []` by metis_tac[iterating_tail_length] >>
  `SUM (GENLIST (\j. body (DROP j x) (DROP j y)) k) <= SUM (GENLIST (\j. cover (DROP j x) (DROP j y)) k)` by
  (irule SUM_LE >>
  fs[]) >>
  qabbrev_tac `f1 = \j. cover (DROP j x) (DROP j y)` >>
  qabbrev_tac `f2 = \j. f (EL j x) (EL j y)` >>
  `GENLIST f1 k = GENLIST f2 k` by
    (irule LIST_EQ >>
  rw[iterating_tail_eqn, Abbr`f1`, Abbr`f2`] >>
  metis_tac[HD_DROP]) >>
  fs[]);

(* Other similar theorems -- directly *)

(* Theorem: (body = \x y. f (HD x) (HD y)) /\
    (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
     !x y k. (LENGTH x = k) /\ (LENGTH y = k) ==>
     loop x y <= quit [][] + SUM (GENLIST (\j. f (EL j x) (EL j y)) k) *)
(* Proof: by loop2_list_tail_head_count_cover_exit_sum_le with cover = body. *)
val loop2_list_tail_head_count_exit_sum_le = store_thm(
  "loop2_list_tail_head_count_exit_sum_le",
  ``!loop body quit exit f. (body = \x y. f (HD x) (HD y)) /\
    (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
     !x y k. (LENGTH x = k) /\ (LENGTH y = k) ==>
     loop x y <= quit [][] + SUM (GENLIST (\j. f (EL j x) (EL j y)) k)``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_list_tail_head_count_cover_exit_sum_le);

(* Theorem: (!x y. body x y <= cover x y) /\ (cover = \x y. f (HD x) (HD y)) /\
    (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + loop (TL x) (TL y)) ==>
     !x y k. (LENGTH x = k) /\ (LENGTH y = k) ==>
     loop x y <= quit [][] + SUM (GENLIST (\j. f (EL j x) (EL j y)) k) *)
(* Proof: by loop2_list_tail_head_count_cover_exit_sum_le with exit = F. *)
val loop2_list_tail_head_count_cover_sum_le = store_thm(
  "loop2_list_tail_head_count_cover_sum_le",
  ``!loop body quit cover f.
    (!x y. body x y <= cover x y) /\ (cover = \x y. f (HD x) (HD y)) /\
    (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + loop (TL x) (TL y)) ==>
     !x y k. (LENGTH x = k) /\ (LENGTH y = k) ==>
     loop x y <= quit [][] + SUM (GENLIST (\j. f (EL j x) (EL j y)) k)``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:'a list y:'b list. F` >>
  `!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + if exit x y then 0 else loop (TL x) (TL y)` by metis_tac[] >>
  imp_res_tac loop2_list_tail_head_count_cover_exit_sum_le);

(* Note: loop2_list_tail_head_count_cover_sum_le with cover = body is:
         loop2_list_tail_head_count_eqn, an equation. *)

(* ------------------------------------------------------------------------- *)

(* Theorem: (!x y. body x y <= cover x y) /\ (cover = \x y. f (HD x) (HD y)) /\ MONO2 f /\
      (!x y. loop x y =
             if x = [] \/ y = [] then quit x y
             else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
      !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
                EVERY (\j. j <= n) x /\ EVERY (\j. j <= n) y ==>
                loop x y <= quit [][] + k * f n n *)
(* Proof:
   Let c = quit [][].
   Given cover = \x y. f (HD x) (HD y), MONO2 f,
      loop x y
   <= c + SUM (GENLIST (\j. f (EL j x) (EL j y)) k)    by loop2_list_tail_head_count_cover_exit_sum_le
   <= c + SUM (GENLIST (\j. f n n) k)                  by SUM_LE, EVERY_EL
    = c + (f n n) * k                                  by SUM_GENLIST_K
    = c + k * f n n                                    by MULT_COMM
*)
val loop2_list_tail_head_bound_count_cover_exit_le = store_thm(
  "loop2_list_tail_head_bound_count_cover_exit_le",
  ``!loop body quit cover exit f.
      (!x y. body x y <= cover x y) /\ (cover = \x y. f (HD x) (HD y)) /\ MONO2 f /\
      (!x y. loop x y =
             if x = [] \/ y = [] then quit x y
             else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
      !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
                EVERY (\j. j <= n) x /\ EVERY (\j. j <= n) y ==>
                loop x y <= quit [][] + k * f n n``,
  rpt strip_tac >>
  assume_tac (loop2_list_tail_head_count_cover_exit_sum_le |> ISPEC ``loop: num list -> num list -> num``) >>
  first_x_assum (qspecl_then [`body`, `quit`,  `cover`, `exit`, `f`] strip_assume_tac) >>
  qabbrev_tac `c = quit [][]` >>
  `loop x y <= c + SUM (GENLIST (\j. f (EL j x) (EL j y)) k)` by metis_tac[] >>
  qabbrev_tac `foo = !x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + if exit x y then 0 else loop (TL x) (TL y)` >>
  `SUM (GENLIST (\j. f (EL j x) (EL j y)) k) <= SUM (GENLIST (K (f n n)) k)` by
  (irule SUM_LE >>
  rw[] >>
  qabbrev_tac `P = \j. j <= n` >>
  `!j. P j = (j <= n)` by rw[Abbr`P`] >>
  metis_tac[EVERY_EL]) >>
  `SUM (GENLIST (K (f n n)) k) = f n n * k` by rw[SUM_GENLIST_K] >>
  decide_tac);

(* Other similar theorems -- directly *)

(* Theorem: (body = \x y. f (HD x) (HD y)) /\ MONO2 f /\
      (!x y. loop x y =
             if x = [] \/ y = [] then quit x y
             else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
      !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
                EVERY (\j. j <= n) x /\ EVERY (\j. j <= n) y ==>
                loop x y <= quit [][] + k * f n n *)
(* Proof: by loop2_list_tail_head_bound_count_cover_exit_le with cover = body. *)
val loop2_list_tail_head_bound_count_exit_le = store_thm(
  "loop2_list_tail_head_bound_count_exit_le",
  ``!loop body quit exit f.
      (body = \x y. f (HD x) (HD y)) /\ MONO2 f /\
      (!x y. loop x y =
             if x = [] \/ y = [] then quit x y
             else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
      !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
                EVERY (\j. j <= n) x /\ EVERY (\j. j <= n) y ==>
                loop x y <= quit [][] + k * f n n``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_list_tail_head_bound_count_cover_exit_le);

(* Theorem: (!x y. body x y <= cover x y) /\ (cover = \x y. f (HD x) (HD y)) /\ MONO2 f /\
      (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + loop (TL x) (TL y)) ==>
      !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
                EVERY (\j. j <= n) x /\ EVERY (\j. j <= n) y ==>
                loop x y <= quit [][] + k * f n n *)
(* Proof: by loop2_list_tail_head_bound_count_cover_exit_le with exit = F. *)
val loop2_list_tail_head_bound_count_cover_le = store_thm(
  "loop2_list_tail_head_bound_count_cover_le",
  ``!loop body quit cover f.
      (!x y. body x y <= cover x y) /\ (cover = \x y. f (HD x) (HD y)) /\ MONO2 f /\
      (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + loop (TL x) (TL y)) ==>
      !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
                EVERY (\j. j <= n) x /\ EVERY (\j. j <= n) y ==>
                loop x y <= quit [][] + k * f n n``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num list y:num list. F` >>
  `!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + if exit x y then 0 else loop (TL x) (TL y)` by metis_tac[] >>
  imp_res_tac loop2_list_tail_head_bound_count_cover_exit_le);

(* Theorem: (body = \x y. f (HD x) (HD y)) /\ MONO2 f /\
      (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + loop (TL x) (TL y)) ==>
      !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
                EVERY (\j. j <= n) x /\ EVERY (\j. j <= n) y ==>
                loop x y <= quit [][] + k * f n n *)
(* Proof: by loop2_list_tail_head_bound_count_cover_le with cover = body. *)
val loop2_list_tail_head_bound_count_le = store_thm(
  "loop2_list_tail_head_bound_count_le",
  ``!loop body quit f.
      (body = \x y. f (HD x) (HD y)) /\ MONO2 f /\
      (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + loop (TL x) (TL y)) ==>
      !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
                    EVERY (\j. j <= n) x /\ EVERY (\j. j <= n) y ==>
                    loop x y <= quit [][] + k * f n n``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_list_tail_head_bound_count_cover_le);

(* ------------------------------------------------------------------------- *)

(* Theorem: (!x y. body x y <= cover x y) /\ (cover = \x y. f (HD x) (HD y)) /\ MONO2 f /\
    (!x y. loop x y =
           if x = [] \/ y = [] then quit x y
           else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
     !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
               EVERY (\j. j < n) x /\ EVERY (\j. j < n) y ==>
               loop x y <= quit [][] + k * f n n *)
(* Proof: by loop2_list_tail_head_bound_count_cover_exit_le, EVERY_LT_IMP_EVERY_LE. *)
val loop2_list_tail_head_upper_count_cover_exit_le = store_thm(
  "loop2_list_tail_head_upper_count_cover_exit_le",
  ``!loop body quit cover exit f.
    (!x y. body x y <= cover x y) /\ (cover = \x y. f (HD x) (HD y)) /\ MONO2 f /\
    (!x y. loop x y =
           if x = [] \/ y = [] then quit x y
           else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
     !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
               EVERY (\j. j < n) x /\ EVERY (\j. j < n) y ==>
               loop x y <= quit [][] + k * f n n``,
  rpt strip_tac >>
  `EVERY (\j. j <= n) x /\ EVERY (\j. j <= n) y` by rw[EVERY_LT_IMP_EVERY_LE] >>
  imp_res_tac loop2_list_tail_head_bound_count_cover_exit_le);

(* Other similar theorems -- directly *)

(* Theorem: (body = \x y. f (HD x) (HD y)) /\ MONO2 f /\
    (!x y. loop x y =
           if x = [] \/ y = [] then quit x y
           else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
     !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
               EVERY (\j. j < n) x /\ EVERY (\j. j < n) y ==>
               loop x y <= quit [][] + k * f n n *)
(* Proof: by loop2_list_tail_head_upper_count_cover_exit_le with cover = body. *)
val loop2_list_tail_head_upper_count_exit_le = store_thm(
  "loop2_list_tail_head_upper_count_exit_le",
  ``!loop body quit exit f.
    (body = \x y. f (HD x) (HD y)) /\ MONO2 f /\
    (!x y. loop x y =
           if x = [] \/ y = [] then quit x y
           else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
     !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
               EVERY (\j. j < n) x /\ EVERY (\j. j < n) y ==>
               loop x y <= quit [][] + k * f n n``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_list_tail_head_upper_count_cover_exit_le);

(* Theorem: (!x y. body x y <= cover x y) /\ (cover = \x y. f (HD x) (HD y)) /\ MONO2 f /\
    (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + loop (TL x) (TL y)) ==>
     !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
               EVERY (\j. j < n) x /\ EVERY (\j. j < n) y ==>
               loop x y <= quit [][] + k * f n n *)
(* Proof: by loop2_list_tail_head_upper_count_cover_exit_le with exit = F. *)
val loop2_list_tail_head_upper_count_cover_le = store_thm(
  "loop2_list_tail_head_upper_count_cover_le",
  ``!loop body quit cover f.
    (!x y. body x y <= cover x y) /\ (cover = \x y. f (HD x) (HD y)) /\ MONO2 f /\
    (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + loop (TL x) (TL y)) ==>
     !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
               EVERY (\j. j < n) x /\ EVERY (\j. j < n) y ==>
               loop x y <= quit [][] + k * f n n``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:num list y:num list. F` >>
  `!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + if exit x y then 0 else loop (TL x) (TL y)` by metis_tac[] >>
  imp_res_tac loop2_list_tail_head_upper_count_cover_exit_le);

(* Theorem: (body = \x y. f (HD x) (HD y)) /\ MONO2 f /\
    (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + loop (TL x) (TL y)) ==>
     !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
               EVERY (\j. j < n) x /\ EVERY (\j. j < n) y ==>
               loop x y <= quit [][] + k * f n n *)
(* Proof: by loop2_list_tail_head_upper_count_cover_le with cover = body. *)
val loop2_list_tail_head_upper_count_le = store_thm(
  "loop2_list_tail_head_upper_count_le",
  ``!loop body quit f.
    (body = \x y. f (HD x) (HD y)) /\ MONO2 f /\
    (!x y. loop x y = if x = [] \/ y = [] then quit x y else body x y + loop (TL x) (TL y)) ==>
     !x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\
               EVERY (\j. j < n) x /\ EVERY (\j. j < n) y ==>
               loop x y <= quit [][] + k * f n n``,
  rpt strip_tac >>
  `!x y. body x y <= body x y` by rw[] >>
  imp_res_tac loop2_list_tail_head_upper_count_cover_le);

(* ------------------------------------------------------------------------- *)
(* List Reduction Loop with Turn Transform                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem:(!x y. loop x y = if y = [] then quit x else body x y + loop (turn x) (TL y)) ==>
     !x y. loop x y = quit (turn_exp x (LENGTH y)) +
                      SUM (GENLIST (\j. body (turn_exp x j) (DROP j y)) (LENGTH y)) *)
(* Proof:
   Let k = LENGTH y,
       z = FUNPOW turn k x
         = turn_exp x k              by notation
      loop x y
    = quit z + SUM (GENLIST (\j. body (FUNPOW turn j x) (DROP j y)) k)
                                              by loop2_list_count_eqn
    = quit (turn_exp x k) + SUM (GENLIST (\j. body (turn_exp x j) (DROP j y)) k)
                                              by notation
*)
val loop2_list_turn_count_eqn = store_thm(
  "loop2_list_turn_count_eqn",
  ``!loop body quit.
    (!x y. loop x y = if y = [] then quit x else body x y + loop (turn x) (TL y)) ==>
     !x y. loop x y = quit (turn_exp x (LENGTH y)) +
                      SUM (GENLIST (\j. body (turn_exp x j) (DROP j y)) (LENGTH y))``,
  rpt strip_tac >>
  imp_res_tac loop2_list_count_eqn >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* Theorem: (!x y. loop x y = if y = [] then quit x else body x y + if exit x y then 0 else loop (turn x) (TL y)) ==>
     !x y. loop x y <= quit (turn_exp x (LENGTH y)) +
                       SUM (GENLIST (\j. body (turn_exp x j) (DROP j y)) (LENGTH y)) *)
(* Proof:
   Let k = LENGTH y,
       z = FUNPOW turn k x
         = turn_exp x k                       by notation
      loop x y
   <= quit z + SUM (GENLIST (\j. body (FUNPOW turn j x) (DROP j y)) k)
                                              by loop2_list_count_sum_le
    = quit (turn_exp x k) + SUM (GENLIST (\j. body (turn_exp x j) (DROP j y)) k)
                                              by notation
*)
val loop2_list_turn_count_sum_le = store_thm(
  "loop2_list_turn_count_sum_le",
  ``!loop body quit exit.
    (!x y. loop x y = if y = [] then quit x else body x y + if exit x y then 0 else loop (turn x) (TL y)) ==>
     !x y. loop x y <= quit (turn_exp x (LENGTH y)) +
                       SUM (GENLIST (\j. body (turn_exp x j) (DROP j y)) (LENGTH y))``,
  rpt strip_tac >>
  imp_res_tac loop2_list_count_sum_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac));

(* ------------------------------------------------------------------------- *)
(* List Reduction Loop with Turn Transform and Body on Head                  *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (body = \x y. f (g x) (HD y)) /\
       (!x y. loop x y = if y = [] then quit x else body x y + loop (turn x) (TL y)) ==>
        !x y. loop x y = quit (turn_exp x (LENGTH y)) +
                         SUM (GENLIST (\j. f (g (turn_exp x j)) (EL j y)) (LENGTH y)) *)
(* Proof:
   Let k = LENGTH y, z = turn_exp x k.
   Given body = \x y. f (g x) (HD y),
     loop x y
   = quit z + SUM (GENLIST (\j. body (turn_exp x j) (DROP j y)) k)
                                                       by loop2_list_turn_count_eqn
   = quit z + SUM (GENLIST (\j. f (g (turn_exp x j)) (HD (DROP j y))) k)
                                                       by substituting body x y
   = quit z + SUM (GENLIST (\j. f (g (turn_exp x j)) (EL j y)) k)
                                                       by HD_DROP
*)
val loop2_list_turn_head_count_eqn = store_thm(
  "loop2_list_turn_head_count_eqn",
  ``!loop body quit f g. (body = \x y. f (g x) (HD y)) /\
       (!x y. loop x y = if y = [] then quit x else body x y + loop (turn x) (TL y)) ==>
        !x y. loop x y = quit (turn_exp x (LENGTH y)) +
                         SUM (GENLIST (\j. f (g (turn_exp x j)) (EL j y)) (LENGTH y))``,
  rpt strip_tac >>
  imp_res_tac loop2_list_turn_count_eqn >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `k = LENGTH y` >>
  rw[] >>
  qabbrev_tac `ls1 = GENLIST (\j. f (g (turn_exp x j)) (HD (DROP j y))) k` >>
  qabbrev_tac `ls2 = GENLIST (\j. f (g (turn_exp x j)) (EL j y)) k` >>
  `ls1 = ls2` by
  (`LENGTH ls1 = LENGTH ls2` by rw[Abbr`ls1`, Abbr`ls2`] >>
  irule LIST_EQ >>
  rw[HD_DROP, Abbr`ls1`, Abbr`ls2`]) >>
  metis_tac[]);

(* Theorem: (!x y. loop x y =
                   if y = [] then quit x
                   else body x y + if exit x y then 0 else loop (turn x) (TL y)) ==>
     !x y. (!j. j < LENGTH y ==> body (turn_exp x j) (DROP j y) <= cover j) ==>
           loop x y <= quit (turn_exp x (LENGTH y)) + SUM (GENLIST cover (LENGTH y)) *)
(* Proof:
   Let k = LENGTH y, z = turn_exp x k.
      loop x y
   <= quit z + SUM (GENLIST (\j. body (turn_exp x j) (DROP j y)) k)
                                                   by loop2_list_turn_count_sum_le
    = quit z + SUM (GENLIST cover k)              by SUM_LE
*)
val loop2_list_turn_head_count_cover_exit_sum_le = store_thm(
  "loop2_list_turn_head_count_cover_exit_sum_le",
  ``!loop body quit cover exit.
    (!x y. loop x y =
           if y = [] then quit x
           else body x y + if exit x y then 0 else loop (turn x) (TL y)) ==>
     !x y. (!j. j < LENGTH y ==> body (turn_exp x j) (DROP j y) <= cover j) ==>
           loop x y <= quit (turn_exp x (LENGTH y)) + SUM (GENLIST cover (LENGTH y))``,
  rpt strip_tac >>
  imp_res_tac loop2_list_turn_count_sum_le >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  qabbrev_tac `k = LENGTH y` >>
  qabbrev_tac `ls1 = GENLIST (\j. body (turn_exp x j) (DROP j y)) k` >>
  qabbrev_tac `ls2 = GENLIST cover k` >>
  `SUM ls1 <= SUM ls2` by rw[SUM_LE, Abbr`ls1`, Abbr`ls2`] >>
  decide_tac);

(* Theorem: MONO cover /\
    (!x y. loop x y =
           if y = [] then quit x
           else body x y + if exit x y then 0 else loop (turn x) (TL y)) ==>
     !x y. (!j. j < LENGTH y ==> body (turn_exp x j) (DROP j y) <= cover j) ==>
           loop x y <= quit (turn_exp x (LENGTH y)) + (LENGTH y) * cover (LENGTH y) *)
(* Proof:
   Let k = LENGTH y, z = turn_exp x k.
      loop x y
   <= quit z + SUM (GENLIST cover k)          by loop2_list_turn_head_count_cover_exit_sum_le
   <= quit z + SUM (GENLIST (K (cover k)) k)  by SUM_LE, MONO cover
    = quit z + (cover k) * k                  by SUM_GENLIST_K
    = quit z + k * cover k                    by MULT_COMM
*)
val loop2_list_turn_head_count_cover_exit_le = store_thm(
  "loop2_list_turn_head_count_cover_exit_le",
  ``!loop body quit cover exit. MONO cover /\
    (!x y. loop x y =
           if y = [] then quit x
           else body x y + if exit x y then 0 else loop (turn x) (TL y)) ==>
     !x y. (!j. j < LENGTH y ==> body (turn_exp x j) (DROP j y) <= cover j) ==>
           loop x y <= quit (turn_exp x (LENGTH y)) + (LENGTH y) * cover (LENGTH y)``,
  rpt strip_tac >>
  imp_res_tac loop2_list_turn_head_count_cover_exit_sum_le >>
  qabbrev_tac `k = LENGTH y` >>
  qabbrev_tac `ls1 = GENLIST cover k` >>
  qabbrev_tac `ls2 = GENLIST (K (cover k)) k` >>
  `SUM ls1 <= SUM ls2` by rw[SUM_LE, Abbr`ls1`, Abbr`ls2`] >>
  `SUM ls2 = cover k * k` by rw[SUM_GENLIST_K, Abbr`ls2`] >>
  decide_tac);

(* Other similar theorems -- directly *)

(* Note: since (body x y) but (cover j), there is no version with cover = body. *)

(* Theorem:  MONO cover /\
    (!x y. loop x y = if y = [] then quit x else body x y + loop (turn x) (TL y)) ==>
     !x y. (!j. j < LENGTH y ==> body (turn_exp x j) (DROP j y) <= cover j) ==>
           loop x y <= quit (turn_exp x (LENGTH y)) + (LENGTH y) * cover (LENGTH y) *)
(* Proof: by loop2_list_turn_head_count_cover_exit_le with exit = F. *)
val loop2_list_turn_head_count_cover_le = store_thm(
  "loop2_list_turn_head_count_cover_le",
  ``!loop body quit cover. MONO cover /\
    (!x y. loop x y = if y = [] then quit x else body x y + loop (turn x) (TL y)) ==>
     !x y. (!j. j < LENGTH y ==> body (turn_exp x j) (DROP j y) <= cover j) ==>
           loop x y <= quit (turn_exp x (LENGTH y)) + (LENGTH y) * cover (LENGTH y)``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x:'a list y:'b list. F` >>
  `!x y. loop x y = if y = [] then quit x else body x y + if exit x y then 0 else loop (turn x) (TL y)` by metis_tac[] >>
  imp_res_tac loop2_list_turn_head_count_cover_exit_le);

(* ------------------------------------------------------------------------- *)
(* Original investigation, some with quit = constant.                        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Diminishing List.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Simple idea:
This loop:
!ls. loop ls = if NULL ls then c else body ls + loop (TL ls)
is equal to this loop:
!ls. loop ls = if LENGTH ls = 0 then c else body x + loop (LENGTH ls - 1)
is equal to this loop:
!x. loop2 x = if x = 0 then c else body2 x + loop2 (x - 1)
Thus this result: !n. loop2 n = c + SUM (MAP body2 (decrease_by 1 n)
becomes:  !ls. loop ls = c + SUM (MAP body (decrease_by 1 (LENGTH ls))

g `!loop body c.
      (!x. loop x = if NULL x then c else body x + loop (TL x) <=>
      !ls. loop ls = c + SUM (MAP body (decrease_by b n))`;
-- but this is difficult to convert.
Have to develop another little theory.
*)

(* Given a list ls, generate a diminishing list of ls, down to before []. *)
Definition diminishing_def:
  diminishing ls =
  if ls = [] then [] else ls::diminishing (TL ls)
Termination
  WF_REL_TAC `measure LENGTH` >> simp[LENGTH_TL_LT]
End

(*
EVAL ``diminishing [4;5;3;2;1]``; = [[4; 5; 3; 2; 1]; [5; 3; 2; 1]; [3; 2; 1]; [2; 1]; [1]]: thm
*)

(* Theorem: diminishing [] = [] *)
(* Proof: by diminishing_def *)
val diminishing_nil = store_thm(
  "diminishing_nil",
  ``diminishing [] = []``,
  rw[Once diminishing_def]);

(* Theorem: ls <> [] ==> (diminishing ls = ls :: diminishing (TL ls))*)
(* Proof: by diminishing_def *)
val diminishing_cons = store_thm(
  "diminishing_cons",
  ``!h t. diminishing (h::t) = (h::t) :: diminishing t``,
  rw[Once diminishing_def]);

(* Theorem: LENGTH (diminishing ls) = LENGTH ls *)
(* Proof:
   By induction on ls.
   Base: LENGTH (diminishing []) = LENGTH [], true    by diminishing_nil
   Step: LENGTH (diminishing ls) = LENGTH ls ==>
         !h. LENGTH (diminishing (h::ls)) = LENGTH (h::ls)
         LENGTH (diminishing (h::ls))
       = LENGTH ((h::ls)::diminishing ls)     by diminishing_cons
       = SUC (LENGTH (diminishing ls))        by LENGTH
       = SUC (LENGTH ls)                      by induction hypothesis
       = LENGTH (h::ls)                       by LENGTH
*)
val diminishing_length = store_thm(
  "diminishing_length",
  ``!ls. LENGTH (diminishing ls) = LENGTH ls``,
  Induct >-
  rw[diminishing_nil] >>
  rw[diminishing_cons]);

(* Theorem: j < LENGTH ls ==> (EL j (diminishing ls) = DROP j ls) *)
(* Proof:
   By induction on ls.
   Base: !j. j < LENGTH [] ==> EL j (diminishing []) = DROP j []
      True since j < 0 = F      by LENGTH
   Step: !j. j < LENGTH ls ==> EL j (diminishing ls) = DROP j ls ==>
        !h. j < LENGTH (h::ls) ==> EL j (diminishing (h::ls)) = DROP j (h::ls)
      Note j < SUC (LENGTH ls)  by LENGTH
      If j = 0,
           EL 0 (diminishing (h::ls))
         = EL 0 ((h::ls)::diminishing ls)     by diminishing_cons
         = h::ls                              by EL
         = DROP 0 (h::ls)                     by DROP_def
      Otherwise, j = SUC k for some k         by num_CASES
         and k < LENGTH ls.
           EL (SUC k) (diminishing (h::ls))
         = EL (SUC k) ((h::ls)::diminishing ls)   by diminishing_cons
         = EL k (diminishing ls)                  by EL
         = DROP k ls                              by induction hypothesis
         = DROP (SUC k) (h::ls)                   by DROP_def
*)
val diminishing_element = store_thm(
  "diminishing_element",
  ``!ls j. j < LENGTH ls ==> (EL j (diminishing ls) = DROP j ls)``,
  Induct >-
  rw[] >>
  rpt strip_tac >>
  Cases_on `j` >-
  rw[diminishing_cons] >>
  `LENGTH (h::ls) = SUC (LENGTH ls)` by rw[] >>
  rw[diminishing_cons]);

(* Theorem: j < LENGTH ls ==> MEM (DROP j ls) (diminishing ls) *)
(* Proof: by MEM_EL, diminishing_length, diminishing_element *)
val diminishing_member = store_thm(
  "diminishing_member",
  ``!ls j. j < LENGTH ls ==> MEM (DROP j ls) (diminishing ls)``,
  metis_tac[diminishing_length, diminishing_element, MEM_EL]);

(* Theorem: diminishing ls = MAP (\j. DROP j ls) [0 ..< (LENGTH ls)] *)
(* Proof:
   Let lx = MAP (\j. DROP j ls) [0 ..< (LENGTH ls)].
   Note LENGTH (diminishing ls) = LENGTH ls       by diminishing_length
    and LENGTH lx = LENGTH ls                     by LENGTH_MAP, listRangeLHI_LEN
   Also if x < LENGTH ls,
        EL x (diminishing ls) = DROP x ls         by diminishing_element
    and EL x lx
      = EL x (MAP (\j. DROP j ls)) [0 ..< (LENGTH ls)]
      = (\j. DROP j ls) (EL x [0 ..< (LENGTH ls)])     by EL_MAP
      = (\j. DROP j ls) (0 + x)                        by listRangeLHI_EL
      = (\j. DROP j ls) x = DROP x ls
   Thus diminishing ls = lx                       by LIST_EQ
*)
val diminishing_eqn = store_thm(
  "diminishing_eqn",
  ``!ls. diminishing ls = MAP (\j. DROP j ls) [0 ..< (LENGTH ls)]``,
  rpt strip_tac >>
  irule LIST_EQ >>
  rw[diminishing_length, diminishing_element, EL_MAP, listRangeLHI_EL]);

(* Theorem: (LENGTH x = k) ==>
            MAP (\x. f (HD x)) (diminishing x) = MAP (\j. f (EL j x)) [0 ..< k] *)
(* Proof:
   Note LENGTH (diminishing x) = LENGTH x = k          by diminishing_length
    and LENGTH [0 ..< k] = k                           by listRangeLHI_LEN
   Let z < k, then
        EL z (MAP (\x. f (HD x)) (diminishing x))
      = (\x. f (HD x)) (EL z (diminishing x))          by EL_MAP
      = (\x. f (HD x)) (DROP z x)                      by diminishing_element
      = f (HD (DROP z x))                              by function application
      = f (EL z x)                                     by HD_DROP
      = (\j. f (EL j x)) z                             by function application
      = (\j. f (EL j x)) (EL z [0 ..< k])              by listRangeLHI_EL
      = EL z (MAP (\j. f (EL j x)) [0 ..< k])          by EL_MAP

   The result follows                                  by LIST_EQ
*)
val diminishing_head_map = store_thm(
  "diminishing_head_map",
  ``!f x k. (LENGTH x = k) ==>
           (MAP (\x. f (HD x)) (diminishing x) = MAP (\j. f (EL j x)) [0 ..< k])``,
  rpt strip_tac >>
  `LENGTH (diminishing x) = k` by rw[diminishing_length] >>
  `LENGTH [0 ..< k] = k` by rw[listRangeLHI_LEN] >>
  irule LIST_EQ >>
  simp[] >>
  rpt strip_tac >>
  fs[EL_MAP, diminishing_element, listRangeLHI_EL, HD_DROP]);

(* Theorem: (LENGTH x = k) /\ (LENGTH y = k) ==>
            (MAP2 (\x y. f (HD x) (HD y)) (diminishing x) (diminishing y) =
             MAP (\j. f (EL j x) (EL j y)) [0 ..< k]) *)
(* Proof:
   Note LENGTH (diminishing x) = LENGTH x = k          by diminishing_length
    and LENGTH (diminishing y) = LENGTH y = k          by diminishing_length
    and LENGTH [0 ..< k] = k                           by listRangeLHI_LEN
   Let z < k, then
        EL z (MAP2 (\x y. f (HD x) (HD y)) (diminishing x) (diminishing y))
      = (\x y. f (HD x) (HD y)) (EL z (diminishing x)) (EL z (diminishing y))
                                                       by EL_MAP2
      = (\x y. f (HD x) (HD y)) (DROP z x) (DROP z y)  by diminishing_element
      = f (HD (DROP z x)) (HD (DROP z y))              by function application
      = f (EL z x) (EL z y)                            by HD_DROP
      = (\j. f (EL j x) (EL j y)) z                    by function application
      = (\j. f (EL j x) (EL j y)) (EL z [0 ..< k])     by listRangeLHI_EL
      = EL z (MAP (\j. f (EL j x) (EL j y)) [0 ..< k]) by EL_MAP

   The result follows                                  by LIST_EQ
*)
val diminishing_head2_map = store_thm(
  "diminishing_head2_map",
  ``!f x y:'a list k. (LENGTH x = k) /\ (LENGTH y = k) ==>
    (MAP2 (\x y. f (HD x) (HD y)) (diminishing x) (diminishing y) =
      MAP (\j. f (EL j x) (EL j y)) [0 ..< k])``,
  rpt strip_tac >>
  `LENGTH (diminishing x) = k` by rw[diminishing_length] >>
  `LENGTH (diminishing y) = k` by rw[Once diminishing_length] >>
  `LENGTH [0 ..< k] = k` by rw[listRangeLHI_LEN] >>
  irule LIST_EQ >>
  simp[] >>
  rpt strip_tac >>
  fs[EL_MAP, EL_MAP2, diminishing_element, listRangeLHI_EL, HD_DROP]);

(* Theorem: diminishing x = loop_arg (\x. x = []) TL x *)
(* Proof:
   By induction from diminishing_def.
   Let guard = (\x. x = []),
       R = measure (\x. LENGTH x).
   Then WF R                                  by WF_measure
    and !x. ~guard x ==> (R (TL x) x)         by LENGTH_TL_LT

   If x = [],
      Then guard []                           by notation
           diminishing []
         = []                                 by diminishing_nil
         = loop_arg guard TL []               by loop_arg_nil, guard []
   If x = h::t,
      Then ~guard (h::t)                      by notation
           diminishing (h::t)
         = (h::t) :: diminishing t            by diminishing_cons
         = (h::t) :: loop_arg guard TL t      by induction hypothesis
         = loop_arg guard TL (h::t)           by loop_arg_cons
*)
val diminishing_eq_loop_arg = store_thm(
  "diminishing_eq_loop_arg",
  ``!x. diminishing x = loop_arg (\x. x = []) TL x``,
  ho_match_mp_tac (theorem "diminishing_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x. x = []` >>
  qabbrev_tac `R = measure (\x. LENGTH x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> (R (TL x) x)` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  Cases_on `x` >| [
    `guard []` by rw[Abbr`guard`] >>
    metis_tac[diminishing_nil, loop_arg_nil],
    `~guard (h::t)` by rw[Abbr`guard`] >>
    metis_tac[diminishing_cons, loop_arg_cons, TL]
  ]);

(* Theorem: MAP2 body (iterating f x (LENGTH y)) (diminishing y) =
            MAP (UNCURRY body) (loop2_arg (\x y. y = []) TL f x y) *)
(* Proof:
   By induction from diminishing_def.
   Let guard = (\x y. y = []),
       R = measure (\(x,y). LENGTH y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,TL y) (x,y) by LENGTH_TL_LT, LENGTH (TL y) < LENGTH y

   If guard x y,
      Then y = []                               by notation
      LHS = MAP2 body (iterating f x (LENGTH [])) (diminishing [])
          = MAP2 body (iterating f x 0) []      by diminishing_nil
          = MAP2 body [] []                     by iterating_nil
          = []                                  by MAP2
      RHS = MAP (UNCURRY body) (loop2_arg guard TL f x [])
          = MAP (UNCURRY body) []               by loop2_arg_nil, guard x y
          = [] = LHS                            by MAP

   If ~guard x y,
     Then y <> []                               by notation
     Let y = h::t.
            MAP2 body (iterating f x (LENGTH y)) (diminishing y)
          = MAP2 body (iterating f x (SUC (LENGTH t))) ((h::t)::diminishing t)
                                                by diminishing_cons
          = MAP2 body (x::iterating f (f x) (LENGTH t)) (y::diminishing t)
                                                by iterating_cons
          = body x y::MAP2 body (iterating f (f x) (LENGTH t)) (diminishing t)
                                                by MAP2
          = body x y::MAP (UNCURRY body) (loop2_arg guard TL f (f x) t)
                                                by induction hypothesis
          = MAP (UNCURRY body) ((x,y):: loop2_arg guard TL f (f x) (TL y))
                                                by MAP, UNCURRY
          = MAP (UNCURRY body) (loop2_arg guard TL f x y)
                                                by loop2_arg_cons
*)
val iterating_diminishing_eq_loop2_arg = store_thm(
  "iterating_diminishing_eq_loop2_arg",
  ``!body f x y. MAP2 body (iterating f x (LENGTH y)) (diminishing y) =
                MAP (UNCURRY body) (loop2_arg (\x y. y = []) TL f x y)``,
  ntac 4 strip_tac >>
  qid_spec_tac `x` >>
  qid_spec_tac `y` >>
  ho_match_mp_tac (theorem "diminishing_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x y. y = []` >>
  qabbrev_tac `R = measure (\(x,y). LENGTH y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,TL y) (x,y)` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  Cases_on `guard x y` >| [
    `y = []` by metis_tac[] >>
    rw[iterating_nil, diminishing_nil] >>
    metis_tac[loop2_arg_nil],
    `y <> []` by metis_tac[] >>
    `?h t. y = h::t` by metis_tac[list_CASES] >>
    rw[iterating_cons, diminishing_cons] >>
    `body x (h::t)::MAP2 body (iterating f (f x) (LENGTH t)) (diminishing t) =
    body x (h::t)::MAP (UNCURRY body) (loop2_arg guard TL f (f x) t)` by metis_tac[] >>
    `_ = MAP (UNCURRY body) ((x,(h::t))::loop2_arg guard TL f (f x) (TL (h::t)))` by rw[] >>
    metis_tac[loop2_arg_cons]
  ]);

(* Theorem: MAP2 body (diminishing x) (diminishing y) =
            MAP (UNCURRY body) (loop2_arg (\x y. x = [] \/ y = []) TL TL x y) *)
(* Proof:
   By induction from diminishing_def.
   Let guard = (\x y. x = [] \/ y = []),
       R = measure (\(x,y). LENGTH y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (TL x,TL y) (x,y)     by LENGTH_TL_LT, LENGTH (TL y) < LENGTH y

   If guard x y,
      Then x = [] or y = []                     by notation
      LHS = MAP2 body (diminishing x) (diminishing y)
          = MAP2 body (diminishing x) []        by diminishing_nil
         or MAP2 body [] (diminishing y)        by diminishing_nil
          = []                                  by MAP2
      RHS = MAP (UNCURRY body) (loop2_arg guard TL TL x [])
          = MAP (UNCURRY body) []               by loop2_arg_nil, guard x y
          = [] = LHS                            by MAP

   If ~guard x y,
     Then x <> [] /\ y <> []                    by notation
     Let x = k::s, y = h::t.
            MAP2 body (diminishing x) (diminishing y)
          = MAP2 body (x::diminishing s) (y::diminishing t)
                                                by diminishing_cons
          = body x y::MAP2 body (diminishing s) (diminishing t)
                                                by MAP2
          = body x y::MAP (UNCURRY body) (loop2_arg guard TL TL s t)
                                                by induction hypothesis
          = MAP (UNCURRY body) ((x,y):: loop2_arg guard TL TL (TL x) (TL y)
                                                by MAP, UNCURRY
          = MAP (UNCURRY body) (loop2_arg guard TL TL x y)
                                                by loop2_arg_cons
*)
val iterating_diminishing_both_eq_loop2_arg = store_thm(
  "iterating_diminishing_both_eq_loop2_arg",
  ``!body x y. MAP2 body (diminishing x) (diminishing y) =
              MAP (UNCURRY body) (loop2_arg (\x y. x = [] \/ y = []) TL TL x y)``,
  ntac 3 strip_tac >>
  qid_spec_tac `x` >>
  qid_spec_tac `y` >>
  ho_match_mp_tac (theorem "diminishing_ind") >>
  rw[] >>
  qabbrev_tac `guard = \x y. x = [] \/ y = []` >>
  qabbrev_tac `R = measure (\(x:'a list,y:'b list). LENGTH y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (TL x,TL y) (x,y)` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  Cases_on `guard x y` >| [
    `x = [] \/ y = []` by metis_tac[] >-
    (rw[diminishing_nil] >> metis_tac[loop2_arg_nil]) >>
    (rw[diminishing_nil] >> metis_tac[loop2_arg_nil]),
    `x <> [] /\ y <> []` by metis_tac[] >>
    `?k s. x = k::s` by metis_tac[list_CASES] >>
    `?h t. y = h::t` by metis_tac[list_CASES] >>
    rw[diminishing_cons] >>
    `body (k::s) (h::t)::MAP2 body (diminishing s) (diminishing t) =
    body (k::s) (h::t)::MAP (UNCURRY body) (loop2_arg guard TL TL s t)` by metis_tac[] >>
    `_ = MAP (UNCURRY body) ((k::s, h::t)::loop2_arg guard TL TL (TL (k::s)) (TL (h::t)))` by rw[] >>
    metis_tac[loop2_arg_cons]
  ]);

(* Theorem: iterating TL x (LENGTH x) = diminishing x *)
(* Proof:
   By induction on x.
   Base: iterating TL [] (LENGTH []) = diminishing []
         iterating TL [] (LENGTH [])
       = iterating TL [] 0           by LENGTH
       = []                          by iterating_nil
       = diminishing []              by diminishing_nil
   Step: iterating TL x (LENGTH x) = diminishing x ==>
         !h. iterating TL (h::x) (LENGTH (h::x)) = diminishing (h::x)
         iterating TL (h::x) (LENGTH (h::x))
       = iterating TL (h::x) (SUC (LENGTH x))   by LENGTH
       = (h::x)::iterating TL x (LENGTH x)      by iterating_cons
       = (h::x)::diminishing x                  by induction hypothesis
       = diminishing (h::x)                     by diminishing_cons
*)
val iterating_tail_eq_diminishing = store_thm(
  "iterating_tail_eq_diminishing",
  ``!x. iterating TL x (LENGTH x) = diminishing x``,
  Induct >-
  rw[iterating_nil, diminishing_nil] >>
  rw[iterating_cons, diminishing_cons]);

(* ------------------------------------------------------------------------- *)
(* List Reduction Loop -- original                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
             !x. loop x = c + SUM (MAP body (diminishing x)) *)
(* Proof:
   Let guard = (\x. x = []),
       R = measure (\x. LENGTH x).
   Then WF R                                  by WF_measure
    and !x. ~guard x ==> (R (TL x) x)         by LENGTH_TL_LT
   Also !x. loop x = if guard x then c else body x + loop (TL x)
                                              by given
   Thus loop x
      = c + SUM (MAP body (loop_arg guard TL x))   by loop_modify_count_by_sum
      = c + SUM (MAP body (diminishing x))         by diminishing_eq_loop_arg
*)
val loop_list_count_by_sum = store_thm(
  "loop_list_count_by_sum",
  ``!loop body c. (!x. loop x = if x = [] then c else body x + loop (TL x)) ==>
         !x. loop x = c + SUM (MAP body (diminishing x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = []` >>
  qabbrev_tac `R = measure (\x. LENGTH x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> (R (TL x) x)` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  `!x. loop x = if guard x then c else body x + loop (TL x)` by metis_tac[] >>
  `loop x = c + SUM (MAP body (loop_arg guard TL x))` by metis_tac[loop_modify_count_by_sum] >>
  `diminishing x = loop_arg guard TL x` by rw[diminishing_eq_loop_arg, Abbr`guard`] >>
  metis_tac[]);

(* Theorem: (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
             !x. loop x <= c + SUM (MAP body (diminishing x)) *)
(* Proof:
   Let guard = (\x. x = []),
       R = measure (\x. LENGTH x).
   Then WF R                                  by WF_measure
    and !x. ~guard x ==> (R (TL x) x)         by LENGTH_TL_LT
   Also !x. loop x = if guard x then c else body x + if exit x then 0 else loop (TL x)
                                              by given
   Thus loop x
     <= c + SUM (MAP body (loop_arg guard TL x))   by loop_modify_count_exit_by_sum
      = c + SUM (MAP body (diminishing x))         by diminishing_eq_loop_arg
*)
val loop_list_count_exit_by_sum = store_thm(
  "loop_list_count_exit_by_sum",
  ``!loop body c exit.
      (!x. loop x = if x = [] then c else body x + if exit x then 0 else loop (TL x)) ==>
       !x. loop x <= c + SUM (MAP body (diminishing x))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x. x = []` >>
  qabbrev_tac `R = measure (\x. LENGTH x)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x. ~guard x ==> (R (TL x) x)` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  `!x. loop x = if guard x then c else body x + if exit x then 0 else loop (TL x)` by metis_tac[] >>
  `loop x <= c + SUM (MAP body (loop_arg guard TL x))` by metis_tac[loop_modify_count_exit_by_sum] >>
  `diminishing x = loop_arg guard TL x` by rw[diminishing_eq_loop_arg, Abbr`guard`] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* List Reduction Loop with Transform -- original                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (!x y. loop x y = if y = [] then c else body x y + loop (f x) (TL y)) ==>
             !x y. loop x y = c + SUM (MAP2 body (iterating f x (LENGTH y)) (diminishing y)) *)
(* Proof:
   Let guard = (\x y. y = []),
       R = measure (\(x,y). LENGTH y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,TL y) (x,y)     by LENGTH_TL_LT, LENGTH (TL x) < LENGTH x
    and !x y. loop x y = if guard x y then c else body x y + loop (f x) (TL y)   by given
        loop x y
      = c + SUM (MAP (UNCURRY body) (loop2_arg guard TL f x y))         by loop2_modify_count_by_sum
      = c + SUM (MAP2 body (iterating f x (LENGTH y)) (diminishing y))  by iterating_diminishing_eq_loop2_arg
*)
val loop2_list_count_by_sum = store_thm(
  "loop2_list_count_by_sum",
  ``!loop f body c.
    (!x y. loop x y = if y = [] then c else body x y + loop (f x) (TL y)) ==>
     !x y. loop x y = c + SUM (MAP2 body (iterating f x (LENGTH y)) (diminishing y))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. y = []` >>
  qabbrev_tac `R = measure (\(x,y). LENGTH y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,TL y) (x,y)` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  `!x y. loop x y = if guard x y then c else body x y + loop (f x) (TL y)` by metis_tac[] >>
  `loop x y = c + SUM (MAP (UNCURRY body) (loop2_arg guard TL f x y))` by metis_tac[loop2_modify_count_by_sum] >>
  `MAP (UNCURRY body) (loop2_arg guard TL f x y) =
    MAP2 body (iterating f x (LENGTH y)) (diminishing y)` by rw[iterating_diminishing_eq_loop2_arg, Abbr`guard`] >>
  metis_tac[]);

(* Theorem: (!x y. loop x y = if y = [] then c else body x y + if exit x y then 0 else loop (f x) (TL y)) ==>
             !x y. loop x y <= c + SUM (MAP2 body (iterating f x (LENGTH y)) (diminishing y)) *)
(* Proof:
   Let guard = (\x y. y = []),
       R = measure (\(x,y). LENGTH y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,TL y) (x,y)     by LENGTH_TL_LT, LENGTH (TL x) < LENGTH x
    and !x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (TL y)
                                                      by given
        loop x y
     <= c + SUM (MAP (UNCURRY body) (loop2_arg guard TL f x y))          by loop2_modify_count_exit_by_sum
      = c + SUM (MAP2 body (iterating f x (LENGTH y)) (diminishing y))   by iterating_diminishing_eq_loop2_arg
*)
val loop2_list_count_exit_by_sum = store_thm(
  "loop2_list_count_exit_by_sum",
  ``!loop f body c exit.
    (!x y. loop x y = if y = [] then c else body x y + if exit x y then 0 else loop (f x) (TL y)) ==>
     !x y. loop x y <= c + SUM (MAP2 body (iterating f x (LENGTH y)) (diminishing y))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. y = []` >>
  qabbrev_tac `R = measure (\(x,y). LENGTH y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,TL y) (x,y)` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  `!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (TL y)` by metis_tac[] >>
  assume_tac (loop2_modify_count_exit_by_sum |> ISPEC ``loop:'a -> 'b list -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `exit`, `TL`, `f`, `R`] strip_assume_tac) >>
  `loop x y <= c + SUM (MAP (UNCURRY body) (loop2_arg guard TL f x y))` by metis_tac[] >>
  `MAP (UNCURRY body) (loop2_arg guard TL f x y) =
    MAP2 body (iterating f x (LENGTH y)) (diminishing y)` by rw[iterating_diminishing_eq_loop2_arg, Abbr`guard`] >>
  metis_tac[]);

(* Theorem: (!x y. body x y <= cover x y) /\
     (!x1 x2 y1 y2. LENGTH y1 <= LENGTH y2 ==> cover x1 y1 <= cover x2 y2) /\
     (!x y. loop x y = if y = [] then c else body x y + if exit x y then 0 else loop (f x) (TL y)) ==>
      !x y. loop x y <= c + cover x y * LENGTH y *)
(* Proof:
   Let guard = (\x y. y = []),
       R = measure (\(x,y). LENGTH y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (f x,TL y) (x,y)     by LENGTH_TL_LT, LENGTH (TL x) < LENGTH x
    and !x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> cover x1 y1 <= cover x2 y2    by R
    and !x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (TL y)
                                                    by given
        loop x y
     <= c + cover x y * loop2_count guard TL f x y  by loop2_modify_count_bcover_exit_upper
      = c + cover x y * LENGTH y                    by list_length_eq_loop2_count
*)
val loop2_list_count_cover_exit_upper = store_thm(
  "loop2_list_count_cover_exit_upper",
  ``!loop f body cover exit c.
       (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. LENGTH y1 <= LENGTH y2 ==> cover x1 y1 <= cover x2 y2) /\
       (!x y. loop x y = if y = [] then c else body x y + if exit x y then 0 else loop (f x) (TL y)) ==>
        !x y. loop x y <= c + cover x y * LENGTH y``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. y = []` >>
  qabbrev_tac `R = measure (\(x,y). LENGTH y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (f x,TL y) (x,y)` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  `!x1 x2 y1 y2. R (x1,y1) (x2,y2) ==> cover x1 y1 <= cover x2 y2` by rw[Abbr`R`] >>
  `!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (f x) (TL y)` by metis_tac[] >>
  assume_tac (loop2_modify_count_bcover_exit_upper |> ISPEC ``loop:'a -> 'b list -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `exit`, `cover`, `TL`, `f`, `R`] strip_assume_tac) >>
  `loop2_count guard TL f x y = LENGTH y` by rw[list_length_eq_loop2_count, Abbr`guard`] >>
  metis_tac[]);

(* Theorem: (!x1 x2 y1 y2. LENGTH y1 <= LENGTH y2 ==> body x1 y1 <= body x2 y2) /\
            (!x y. loop x y = if y = [] then c else body x y + if exit x y then 0 else loop (f x) (TL y)) ==>
             !x y. loop x y <= c + body x y * LENGTH y *)
(* Proof: by loop2_list_count_cover_exit_upper, with cover = body. *)
val loop2_list_count_exit_upper = store_thm(
  "loop2_list_count_exit_upper",
  ``!loop f body exit c.
       (!x1 x2 y1 y2. LENGTH y1 <= LENGTH y2 ==> body x1 y1 <= body x2 y2) /\
       (!x y. loop x y = if y = [] then c else body x y + if exit x y then 0 else loop (f x) (TL y)) ==>
        !x y. loop x y <= c + body x y * LENGTH y``,
  rpt strip_tac >>
  assume_tac loop2_list_count_cover_exit_upper >>
  last_x_assum (qspecl_then [`loop`, `f`, `body`, `body`, `exit`, `c`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* Theorem: (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. LENGTH y1 <= LENGTH y2 ==> cover x1 y1 <= cover x2 y2) /\
       (!x y. loop x y = if y = [] then c else body x y + loop (f x) (TL y)) ==>
        !x y. loop x y <= c + cover x y * LENGTH y *)
(* Proof: by loop2_list_count_cover_exit_upper, with exit = F. *)
val loop2_list_count_cover_upper = store_thm(
  "loop2_list_count_cover_upper",
  ``!loop f body cover c. (!x y. body x y <= cover x y) /\
       (!x1 x2 y1 y2. LENGTH y1 <= LENGTH y2 ==> cover x1 y1 <= cover x2 y2) /\
       (!x y. loop x y = if y = [] then c else body x y + loop (f x) (TL y)) ==>
        !x y. loop x y <= c + cover x y * LENGTH y``,
  rpt strip_tac >>
  qabbrev_tac `exit = \x y:'b list. F` >>
  assume_tac loop2_list_count_cover_exit_upper >>
  last_x_assum (qspecl_then [`loop`, `f`, `body`, `cover`, `exit`, `c`] strip_assume_tac) >>
  metis_tac[]);

(* Theorem: (!x1 x2 y1 y2. LENGTH y1 <= LENGTH y2 ==> body x1 y1 <= body x2 y2) /\
    (!x y. loop x y = if y = [] then c else body x y + loop (f x) (TL y)) ==>
     !x y. loop x y <= c + body x y * LENGTH y *)
(* Proof: loop2_list_count_cover_upper, with cover = body. *)
val loop2_list_count_upper = store_thm(
  "loop2_list_count_upper",
  ``!loop f body c. (!x1 x2 y1 y2. LENGTH y1 <= LENGTH y2 ==> body x1 y1 <= body x2 y2) /\
    (!x y. loop x y = if y = [] then c else body x y + loop (f x) (TL y)) ==>
     !x y. loop x y <= c + body x y * LENGTH y``,
  rpt strip_tac >>
  assume_tac loop2_list_count_cover_upper >>
  last_x_assum (qspecl_then [`loop`, `f`, `body`, `body`, `c`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);

(* ------------------------------------------------------------------------- *)
(* List Reduction Loop with Tail Transform -- original                       *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (!x y. loop x y = if x = [] \/ y = [] then c else body x y + loop (TL x) (TL y)) ==>
             !x y. loop x y = c + SUM (MAP2 body (diminishing x) (diminishing y)) *)
(* Proof:
   Let guard = (\x y. x = [] \/ y = []),
       R = measure (\(x,y). LENGTH y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (TL x,TL y) (x,y)     by LENGTH_TL_LT, LENGTH (TL x) < LENGTH x
    and !x y. loop x y = if guard x y then c else body x y + loop (TL x) (TL y)   by given
        loop x y
      = c + SUM (MAP (UNCURRY body) (loop2_arg guard TL TL x y))   by loop2_modify_count_by_sum
      = c + SUM (MAP2 body (diminishing x) (diminishing y))        by iterating_diminishing_both_eq_loop2_arg
*)
val loop2_list_tail_count_by_sum = store_thm(
  "loop2_list_tail_count_by_sum",
  ``!loop body c.
    (!x y. loop x y = if x = [] \/ y = [] then c else body x y + loop (TL x) (TL y)) ==>
     !x y. loop x y = c + SUM (MAP2 body (diminishing x) (diminishing y))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. x = [] \/ y = []` >>
  qabbrev_tac `R = measure (\(x:'a list,y:'b list). LENGTH y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (TL x,TL y) (x,y)` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  `!x y. loop x y = if guard x y then c else body x y + loop (TL x) (TL y)` by metis_tac[] >>
  assume_tac (loop2_modify_count_by_sum |> ISPEC ``loop:'a list -> 'b list -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `TL`, `TL`, `R`] strip_assume_tac) >>
  `loop x y = c + SUM (MAP (UNCURRY body) (loop2_arg guard TL TL x y))` by metis_tac[] >>
  `MAP (UNCURRY body) (loop2_arg guard TL TL x y) =
    MAP2 body (diminishing x) (diminishing y)` by rw[GSYM iterating_diminishing_both_eq_loop2_arg, Abbr`guard`] >>
  metis_tac[]);

(* Theorem: (!x y. loop x y =
                   if x = [] \/ y = [] then c
                   else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
             !x y. loop x y <= c + SUM (MAP2 body (diminishing x) (diminishing y)) *)
(* Proof:
   Let guard = (\x y. x = [] \/ y = []),
       R = measure (\(x,y). LENGTH y).
   Then WF R                 by WF_measure
    and !x y. ~guard x y ==> R (TL x,TL y) (x,y)     by LENGTH_TL_LT, LENGTH (TL x) < LENGTH x
    and !x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (TL x) (TL y)
                                                     by given
        loop x y
     <= c + SUM (MAP (UNCURRY body) (loop2_arg guard TL TL x y))   by loop2_modify_count_exit_by_sum
      = c + SUM (MAP2 body (diminishing x) (diminishing y))        by iterating_diminishing_both_eq_loop2_arg
*)
val loop2_list_tail_count_exit_by_sum = store_thm(
  "loop2_list_tail_count_exit_by_sum",
  ``!loop body c exit.
    (!x y. loop x y =
           if x = [] \/ y = [] then c
           else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
     !x y. loop x y <= c + SUM (MAP2 body (diminishing x) (diminishing y))``,
  rpt strip_tac >>
  qabbrev_tac `guard = \x y. x = [] \/ y = []` >>
  qabbrev_tac `R = measure (\(x:'a list,y:'b list). LENGTH y)` >>
  `WF R` by rw[Abbr`R`] >>
  `!x y. ~guard x y ==> R (TL x,TL y) (x,y)` by rw[LENGTH_TL_LT, Abbr`guard`, Abbr`R`] >>
  `!x y. loop x y = if guard x y then c else body x y + if exit x y then 0 else loop (TL x) (TL y)` by metis_tac[] >>
  assume_tac (loop2_modify_count_exit_by_sum |> ISPEC ``loop:'a list -> 'b list -> num``) >>
  last_x_assum (qspecl_then [`guard`, `body`, `c`, `exit`, `TL`, `TL`, `R`] strip_assume_tac) >>
  `loop x y <= c + SUM (MAP (UNCURRY body) (loop2_arg guard TL TL x y))` by metis_tac[] >>
  `MAP (UNCURRY body) (loop2_arg guard TL TL x y) =
    MAP2 body (diminishing x) (diminishing y)` by rw[GSYM iterating_diminishing_both_eq_loop2_arg, Abbr`guard`] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)
(* List Reduction Loop with Tail Transform and Body on Heads -- original     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (!x y. loop x y =
                   if x = [] \/ y = [] then c
                   else body x y + loop (TL x) (TL y)) ==>
        !x y k f. (LENGTH x = k) /\ (LENGTH y = k) /\ (body = \x y. f (HD x) (HD y)) ==>
               loop x y = c + SUM (MAP (\j. f (EL j x) (EL j y)) [0 ..< k]) *)
(* Proof:
   Given body = \x y. f (HD x) (HD y),
     loop x y
   = c + SUM (MAP2 body (diminishing x) (diminishing y))    by loop2_list_tail_count_by_sum
   = c + SUM (MAP (\j. f (EL j x) (EL j y)) [0 ..< k])      by diminishing_head2_map
*)
val loop2_list_tail_head_count_by_sum = store_thm(
  "loop2_list_tail_head_count_by_sum",
  ``!loop body c.
       (!x y. loop x y =
              if x = [] \/ y = [] then c
              else body x y + loop (TL x) (TL y)) ==>
        !x y k f. (LENGTH x = k) /\ (LENGTH y = k) /\ (body = \x y. f (HD x) (HD y)) ==>
               loop x y = c + SUM (MAP (\j. f (EL j x) (EL j y)) [0 ..< k])``,
  rpt strip_tac >>
  imp_res_tac loop2_list_tail_count_by_sum >>
  rw[] >>
  metis_tac[diminishing_head2_map]);

(* Theorem: (!x y. loop x y =
                   if y = [] then c
                   else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
     !x y k f cover. (LENGTH x = k) /\ (LENGTH y = k) /\
     (!x y. body x y <= cover x y) /\ (cover = \x y. f (HD x) (HD y)) ==>
     loop x y <= c + SUM (MAP (\j. f (EL j x) (EL j y)) [0 ..< k]) *)
(* Proof:
   Given body = \x y. f (HD x) (HD y),
      loop x y
   <= c + SUM (MAP2 body (diminishing x) (diminishing y))    by loop2_list_tail_count_exit_by_sum
   <= c + SUM (MAP2 cover (diminishing x) (diminishing y))   by SUM_LE, diminishing_element, EL_MAP2, cover property
    = c + SUM (MAP (\j. f (EL j x) (EL j y)) [0 ..< k])      by diminishing_head2_map
*)
val loop2_list_tail_head_count_cover_exit_by_sum = store_thm(
  "loop2_list_tail_head_count_cover_exit_by_sum",
  ``!loop body c exit.
    (!x y. loop x y =
           if x = [] \/ y = [] then c
           else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
     !x y k f cover. (LENGTH x = k) /\ (LENGTH y = k) /\
     (!x y. body x y <= cover x y) /\ (cover = \x y. f (HD x) (HD y)) ==>
     loop x y <= c + SUM (MAP (\j. f (EL j x) (EL j y)) [0 ..< k])``,
  rpt strip_tac >>
  imp_res_tac loop2_list_tail_count_exit_by_sum >>
  first_x_assum (qspecl_then [`y`, `x`] strip_assume_tac) >>
  `SUM (MAP2 body (diminishing x) (diminishing y)) <= SUM (MAP2 cover (diminishing x) (diminishing y))` by
  (irule SUM_LE >>
  fs[diminishing_element, diminishing_length, EL_MAP2]) >>
  `loop x y <= c + SUM (MAP2 cover (diminishing x) (diminishing y))` by decide_tac >>
  `loop x y <= c + SUM (MAP2 (\x y. f (HD x) (HD y)) (diminishing x) (diminishing y))` by rw[] >>
  metis_tac[diminishing_head2_map]);

(* Theorem: (!x y. loop x y =
                   if y = [] then c
                   else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
     !x y k f. (LENGTH x = k) /\ (LENGTH y = k) /\ (body = \x y. f (HD x) (HD y)) ==>
     loop x y <= c + SUM (MAP (\j. f (EL j x) (EL j y)) [0 ..< k]) *)
(* Proof: by loop2_list_tail_head_count_cover_exit_by_sum with body = cover. *)
val loop2_list_tail_head_count_exit_by_sum = store_thm(
  "loop2_list_tail_head_count_exit_by_sum",
  ``!loop body c exit.
    (!x y. loop x y =
           if x = [] \/ y = [] then c
           else body x y + if exit x y then 0 else loop (TL x) (TL y)) ==>
     !x y k f. (LENGTH x = k) /\ (LENGTH y = k) /\ (body = \x y. f (HD x) (HD y)) ==>
     loop x y <= c + SUM (MAP (\j. f (EL j x) (EL j y)) [0 ..< k])``,
  rpt strip_tac >>
  assume_tac loop2_list_tail_head_count_cover_exit_by_sum >>
  first_x_assum (qspecl_then [`loop`, `body`, `c`, `exit`] strip_assume_tac) >>
  metis_tac[LESS_EQ_REFL]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
