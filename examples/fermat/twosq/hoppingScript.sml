(* ------------------------------------------------------------------------- *)
(* Node Hopping Algorithm.                                                   *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "hopping";

(* ------------------------------------------------------------------------- *)


(* open dependent theories *)
(* arithmeticTheory -- load by default *)

(* val _ = load "quarityTheory"; *)
open helperTwosqTheory;
open helperNumTheory;
open helperSetTheory;
open helperFunctionTheory;
open arithmeticTheory pred_setTheory;
open dividesTheory; (* for divides_def, prime_def *)
open logPowerTheory; (* for square_alt *)

open listTheory rich_listTheory;
open helperListTheory;
open listRangeTheory; (* for listRangeLHI_ALL_DISTINCT *)
open indexedListsTheory; (* for findi_EL and EL_findi *)

load "sublistTheory";
open sublistTheory;

open quarityTheory;
open pairTheory;

(* val _ = load "twoSquaresTheory"; *)
open windmillTheory;
open involuteTheory;
open involuteFixTheory;
open iterationTheory; (* for iterate_period_pos *)
open iterateComposeTheory; (* for involute_involute_fix_orbit_fix_odd *)
open iterateComputeTheory; (* for iterate_while_thm *)
open twoSquaresTheory; (* for loop test found *)


(* ------------------------------------------------------------------------- *)
(* Node Hopping Algorithm Documentation                                      *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   The zagier-flip permutation:
   ping_def            |- !x y z. ping (x,y,z) = (x + 2 * y,y,z - y - x)
   pong_def            |- !x y z. pong (x,y,z) = (2 * z - x,z,x + y - z)
   pung_def            |- !x y z. pung (x,y,z) = (x - 2 * z,x + y - z,z)
   ping_alt            |- !x y z. ping (x,y,z) = (x + 2 * y,y,z - (x + y))
   is_ping_def         |- !x y z. is_ping (x,y,z) <=> x < z - y
   is_pong_def         |- !x y z. is_pong (x,y,z) <=> ~(x < z - y) /\ x < 2 * z
   is_pung_def         |- !x y z. is_pung (x,y,z) <=> ~(x < z - y) /\ ~(x < 2 * z)
   triple_cases        |- !t. is_ping t \/ is_pong t \/ is_pung t
   ping_not_pong       |- !t. is_ping t ==> ~is_pong t
   ping_not_pung       |- !t. is_ping t ==> ~is_pung t
   pong_not_ping       |- !t. is_pong t ==> ~is_ping t
   pong_not_pung       |- !t. is_pong t ==> ~is_pung t
   pung_not_ping       |- !t. is_pung t ==> ~is_ping t
   pung_not_pong       |- !t. is_pung t ==> ~is_pong t
   is_ping_alt         |- !x y z. is_ping (x,y,z) <=> SQRT (windmill (x,y,z)) < 2 * z - x
   is_pong_alt         |- !x y z. is_pong (x,y,z) <=> 0 < 2 * z - x /\ 2 * z - x <= SQRT (windmill (x,y,z))
   is_pung_alt         |- !x y z. is_pung (x,y,z) <=> 2 * z - x = 0
   is_ping_x_x_z       |- !x z. 2 * x < z ==> is_ping (x,x,z)
   is_ping_1_1_k       |- !k. 2 < k ==> is_ping (1,1,k)
   not_ping_x_y_y      |- !x y. ~is_ping (x,y,y)
   is_pong_x_y_x       |- !x y. 0 < x ==> is_pong (x,y,x)
   is_ping_by_ping     |- !t. (let (x,y,z) = ping t in is_ping t <=> 0 < z)
   is_pong_by_pong     |- !t. (let (x,y,z) = pong t in 0 < x /\ 0 < z ==> is_pong t)
   is_pung_by_pung     |- !t. (let (x,y,z) = pung t in 0 < x ==> is_pung t)

   Zagier and Flip composition:
   zagier_flip_thm         |- !t. (zagier o flip) t =
                                  if is_ping t then ping t else if is_pong t then pong t else pung t
   zagier_flip_ping        |- !t. is_ping t ==> (zagier o flip) t = ping t
   zagier_flip_pong        |- !t. is_pong t ==> (zagier o flip) t = pong t
   zagier_flip_pung        |- !t. is_pung t ==> (zagier o flip) t = pung t
   zagier_flip_ping_funpow |- !m t. (!j. j < m ==> is_ping (FUNPOW ping j t)) ==>
                                    FUNPOW (zagier o flip) m t = FUNPOW ping m t
   zagier_flip_pung_funpow |- !m t. (!j. j < m ==> is_pung (FUNPOW pung j t)) ==>
                                    FUNPOW (zagier o flip) m t = FUNPOW pung m t

   pung_next_non_ping      |- !x y z. 2 * z <= x ==> ~is_ping (pung (x,y,z))
   pung_next_not_ping      |- !t. is_pung t ==> ~is_ping (pung t)
   ping_before_not_pung    |- !t. is_ping ((zagier o flip) t) ==> ~is_pung t

   mind_of_ping            |- !x y z. mind (ping (x,y,z)) = x + 2 * y
   mind_rise_by_ping       |- !t. mind t <= mind (ping t)
   mind_inc_by_ping        |- !x y z. 0 < x /\ 0 < y ==> mind (x,y,z) < mind (ping (x,y,z))
   mind_of_pung            |- !x y z. 2 * z <= x ==> mind (pung (x,y,z)) = x
   mind_fall_for_pung      |- !x y z. 2 * y <= x ==> mind (pung (x,y,z)) <= mind (x,y,z)
   mind_fall_by_pung       |- !t. is_pung t ==> mind (pung t) <= mind t

   Path on principal orbit of (zagier o flip) iteration:
   path_def                |- (!n. path n 0 = [(1,n DIV 4,1)]) /\
                              !n k. path n (SUC k) = SNOC ((zagier o flip) (LAST (path n k))) (path n k)
   path_0                  |- !n. path n 0 = [(1,n DIV 4,1)]
   path_suc                |- !n k. path n (SUC k) = SNOC ((zagier o flip) (LAST (path n k))) (path n k)
   path_1                  |- !n. path n 1 = [(1,n DIV 4,1); (1,1,n DIV 4)]
   path_not_nil            |- !n k. path n k <> []
   path_length             |- !n k. LENGTH (path n k) = k + 1
   path_head               |- !n k. HD (path n k) = (1,n DIV 4,1)
   path_last               |- !n k. LAST (path n k) = FUNPOW (zagier o flip) k (1,n DIV 4,1)
   path_head_alt           |- !n k. HD (path n k) = EL 0 (path n k)
   path_last_alt           |- !n k. LAST (path n k) = EL k (path n k)
   path_tail_alt           |- !n m. TL (path n (1 + m)) = iterate_trace (1,1,n DIV 4) (zagier o flip) m
   path_tail_all_distinct  |- !n k. tik n /\ ~square n /\
                                    k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) ==>
                                    ALL_DISTINCT (TL (path n k))
   path_eq_sing            |- !n k. path n k = [(1,n DIV 4,1)] <=> k = 0
   path_front_length       |- !n k. LENGTH (FRONT (path n k)) = k
   path_front_head         |- !n k. 0 < k ==> HD (FRONT (path n k)) = (1,n DIV 4,1)
   path_element_eqn        |- !n k j. j <= k ==> EL j (path n k) = FUNPOW (zagier o flip) j (1,n DIV 4,1)
   path_element_suc        |- !n k j. j < k ==> EL (SUC j) (path n k) = (zagier o flip) (EL j (path n k))
   path_element_thm        |- !n k j h. j + h <= k ==> EL (j + h) (path n k) = FUNPOW (zagier o flip) h (EL j (path n k))
   path_element_in_mills   |- !n k j. tik n /\ j <= k ==> EL j (path n k) IN mills n
   path_element_windmill   |- !n k j. tik n /\ j <= k ==> n = windmill (EL j (path n k))
   path_head_is_pong       |- !n k. is_pong (EL 0 (path n k))
   path_element_0          |- !n k. EL 0 (path n k) = (1,n DIV 4,1)
   path_element_1          |- !n k. 0 < k ==> EL 1 (path n k) = (1,1,n DIV 4)
   path_tail_element       |- !n k j. j < k ==> EL j (TL (path n k)) = FUNPOW (zagier o flip) j (1,1,n DIV 4)
   path_head_next_property |- !n k. 0 < k ==> (let t = EL 1 (path n k)
                                                in if n < 4 then is_pung t
                                                   else if n < 12 then is_pong t
                                                   else is_ping t)
   path_last_not_ping      |- !n k. (let ls = path n k
                                      in flip (LAST ls) = LAST ls ==> ~is_ping (LAST ls))
   path_last_not_ping_thm  |- !n p. prime n /\ tik n /\ p = iterate_period (zagier o flip) (1,1,n DIV 4) ==>
                                    ~is_ping (LAST (path n (1 + HALF p)))
   path_element_ping_funpow|- !n k u m. (let ls = path n k
                                          in m + u <= k /\ (!j. j < m ==> is_ping (EL (u + j) ls)) ==>
                                             !j. j <= m ==> EL (u + j) ls = FUNPOW ping j (EL u ls))
   path_element_pung_funpow|- !n k u m. (let ls = path n k
                                          in m + u <= k /\ (!j. j < m ==> is_pung (EL (u + j) ls)) ==>
                                             !j. j <= m ==> EL (u + j) ls = FUNPOW pung j (EL u ls))

   Sections along Path:
   pung_to_ping_has_pong   |- !n k j h. (let ls = path n k
                                          in j < h /\ h <= k /\ is_pung (EL j ls) /\ is_ping (EL h ls) ==>
                                             ?p. j < p /\ p < h /\ is_pong (EL p ls))
   pong_interval_ping_start        |- !n k j h. (let ls = path n k
                                                  in j < h /\ h <= k /\ is_pong (EL j ls) /\ is_pong (EL h ls) /\
                                                     (!p. j < p /\ p < h ==> ~is_pong (EL p ls)) ==>
                                                     !e. j < e /\ e < h /\ is_ping (EL e ls) ==>
                                                     !p. j < p /\ p <= e ==> is_ping (EL p ls))
   pong_interval_ping_start_alt    |- !n k j h. (let ls = path n k
                                                  in j < h /\ h <= k /\ is_pong (EL j ls) /\ is_pong (EL h ls) /\
                                                     EVERY (\p. ~is_pong (EL p ls)) [j + 1 ..< h] ==>
                                                     !e. j < e /\ e < h /\ is_ping (EL e ls) ==>
                                                     EVERY (\p. is_ping (EL p ls)) [j + 1 .. e])
   pong_interval_pung_stop         |- !n k j h. (let ls = path n k
                                                  in j < h /\ h <= k /\ is_pong (EL j ls) /\ is_pong (EL h ls) /\
                                                     (!p. j < p /\ p < h ==> ~is_pong (EL p ls)) ==>
                                                     !e. j < e /\ e < h /\ is_pung (EL e ls) ==>
                                                     !p. e <= p /\ p < h ==> is_pung (EL p ls))
   pong_interval_pung_stop_alt     |- !n k j h. (let ls = path n k
                                                  in j < h /\ h <= k /\ is_pong (EL j ls) /\ is_pong (EL h ls) /\
                                                     EVERY (\p. ~is_pong (EL p ls)) [j + 1 ..< h] ==>
                                                     !e. j < e /\ e < h /\ is_pung (EL e ls) ==>
                                                     EVERY (\p. is_pung (EL p ls)) [e ..< h])
   pong_interval_cut_exists        |- !n k j h. (let ls = path n k
                                                  in j < h /\ h <= k /\ is_pong (EL j ls) /\ is_pong (EL h ls) /\
                                                     (!p. j < p /\ p < h ==> ~is_pong (EL p ls)) ==>
                                                     ?c. j < c /\ c <= h /\ ~is_ping (EL c ls) /\
                                                         (!p. j < p /\ p < c ==> is_ping (EL p ls)) /\
                                                          !p. c <= p /\ p < h ==> is_pung (EL p ls))
   pong_interval_cut_exists_alt    |- !n k j h. (let ls = path n k
                                                  in j < h /\ h <= k /\ is_pong (EL j ls) /\ is_pong (EL h ls) /\
                                                     EVERY (\p. ~is_pong (EL p ls)) [j + 1 ..< h] ==>
                                                     ?c. j < c /\ c <= h /\ ~is_ping (EL c ls) /\
                                                     EVERY (\p. is_ping (EL p ls)) [j + 1 ..< c] /\
                                                     EVERY (\p. is_pung (EL p ls)) [c ..< h])

   pong_seed_pung_before       |- !n k e. (let ls = path n k
                                            in ~is_pung (HD ls) /\ e < k /\ is_pong (EL e ls) ==>
                                               ?j. j <= e /\ (!p. j <= p /\ p < e ==> is_pung (EL p ls)) /\
                                                   ~is_pung (EL (PRE j) ls))
   pong_seed_ping_after        |- !n k e. (let ls = path n k
                                            in ~is_ping (LAST ls) /\ e < k /\ is_pong (EL e ls) ==>
                                               ?h. e <= h /\ h < k /\ (!p. e < p /\ p <= h ==> is_ping (EL p ls)) /\
                                                   ~is_ping (EL (SUC h) ls))
   pong_seed_pung_ping         |- !n k e. (let ls = path n k
                                            in ~is_pung (HD ls) /\ ~is_ping (LAST ls) /\
                                               e < k /\ is_pong (EL e ls) ==>
                                               ?j h. j <= e /\ e <= h /\ h < k /\
                                                     (!p. j <= p /\ p < e ==> is_pung (EL p ls)) /\ ~is_pung (EL (PRE j) ls) /\
                                                     (!p. e < p /\ p <= h ==> is_ping (EL p ls)) /\ ~is_ping (EL (SUC h) ls))
   pung_next_not_flip_fix      |- !x y z. 0 < y /\ is_pung (x,y,z) ==> (let t = pung (x,y,z) in flip t <> t)
   path_last_flip_fix_not_by_pung
                               |- !n k e. (let ls = path n k
                                            in tik n /\ ~square n /\ flip (LAST ls) = LAST ls ==> ~is_pung (EL (k - 1) ls))
   path_last_pong_to_flip_fix  |- !n k j h. (let ls = path n k
                                              in tik n /\ ~square n /\ j < h /\ h <= k /\
                                                 is_pong (EL j ls) /\ flip (EL h ls) = EL h ls /\
                                                 (!p. j < p /\ p < h ==> ~is_pong (EL p ls)) ==>
                                                 !p. j < p /\ p < h ==> is_ping (EL p ls))

   Hopping:
   hop_def             |- !m x y z. hop m (x,y,z) = if x < 2 * m * z
                                                    then (2 * m * z - x,z,y + m * x - m * m * z)
                                                    else (x - 2 * m * z,y + m * x - m * m * z,z)
   hop_alt             |- !m x y z. 0 < z ==>
                                    hop m (x,y,z) =
                                    if x DIV (2 * z) < m
                                    then (2 * m * z - x,z,y + m * x - m * m * z)
                                    else (x - 2 * m * z,y + m * x - m * m * z,z)
   hop_0               |- !t. hop 0 t = t
   hop_1               |- !t. ~is_ping t ==> hop 1 t = (zagier o flip) t
   hop_mind            |- !m x z. 0 < z ==> (x DIV (2 * z) < m <=> 0 < 2 * m * z - x)
   hop_arm             |- !m n x y z. ~square n /\ n = windmill (x,y,z) ==>
                                      (m <= (x + SQRT n) DIV (2 * z) <=> 0 < y + m * x - m * m * z)
   hop_triple_first    |- !n m t. tik n /\ n = windmill t ==> 0 < FST (hop m t)
   hop_windmill        |- !m n x y z. ~square n /\ n = windmill (x,y,z) /\ m <= (x + SQRT n) DIV (2 * z) ==>
                                      n = windmill (hop m (x,y,z))
   hop_range           |- !m n x y z. n = windmill (x,y,z) /\ 0 < 2 * m * z - x /\
                                      0 < y + m * x - m * m * z ==>
                                      x DIV (2 * z) < m /\ m <= (x + SQRT n) DIV (2 * z)
   hop_range_iff       |- !m n x y z. ~square n /\ n = windmill (x,y,z) ==>
                                      (0 < 2 * m * z - x /\ 0 < y + m * x - m * m * z <=>
                                       0 < z /\ x DIV (2 * z) < m /\ m <= (x + SQRT n) DIV (2 * z))

   Matrices of ping, pong, pung and hop:
   ping_funpow         |- !m x y z. FUNPOW ping m (x,y,z) = (x + 2 * m * y,y,z - m * x - m * m * y)
   ping_windmill       |- !t. is_ping t ==> windmill t = windmill (ping t)
   pong_windmill       |- !t. is_pong t ==> windmill t = windmill (pong t)
   pung_windmill       |- !t. is_pung t ==> windmill t = windmill (pung t)
   ping_funpow_windmill|- !m t. (!j. j < m ==> is_ping (FUNPOW ping j t)) ==>
                                windmill t = windmill (FUNPOW ping m t)
   pung_funpow_windmill|- !m t. (!j. j < m ==> is_pung (FUNPOW pung j t)) ==>
                                windmill t = windmill (FUNPOW pung m t)
   pung_funpow         |- !n x y z m. tik n /\ ~square n /\ n = windmill (x,y,z) /\
                                      (!j. j < m ==> is_pung (FUNPOW pung j (x,y,z))) ==>
                                      FUNPOW pung m (x,y,z) = (x - 2 * m * z,y + m * x - m * m * z,z)
   pung_funpow_by_hop  |- !n m t. tik n /\ ~square n /\ n = windmill t /\
                                  (!j. j < m ==> is_pung (FUNPOW pung j t)) ==> FUNPOW pung m t = hop m t
   pung_to_ping_by_hop |- !n t p q. tik n /\ ~square n /\ n = windmill t /\ is_pong (FUNPOW pung q t) /\
                                    (!j. j < q ==> is_pung (FUNPOW pung j t)) ==>
                                    (FUNPOW ping p o pong o FUNPOW pung q) t = hop (p + q + 1) t
   hop_over_pung       |- !m x y z. 0 < z /\ m < x DIV (2 * z) ==> is_pung (hop m (x,y,z))
   hop_beyond_pung     |- !m x y z. 0 < z /\ m = x DIV (2 * z) ==> ~is_pung (hop m (x,y,z))

   Hopping Algorithm:
   step_def            |- !k x y z. step k (x,y,z) = (x + k) DIV (2 * z)
   hopping_def         |- !k t. hopping k t = hop (step k t) t
   two_sq_hop_def      |- !n. two_sq_hop n = WHILE ($~ o found) (hopping (SQRT n)) (1,n DIV 4,1)

   step_0              |- !x y z. step 0 (x,y,z) = x DIV (2 * z)
   step_sqrt           |- !n x y z. step (SQRT n) (x,y,z) = (x + SQRT n) DIV (2 * z)

   Hopping by step 0:
   hop_step_0_over_pung    |- !m x y z. 0 < z /\ m < step 0 (x,y,z) ==> is_pung (hop m (x,y,z))
   hop_step_0_beyond_pung  |- !m x y z. 0 < z /\ m = step 0 (x,y,z) ==> ~is_pung (hop m (x,y,z))
   step_0_eq_0             |- !x y z. 0 < z ==> (step 0 (x,y,z) = 0 <=> ~is_pung (x,y,z))
   step_0_of_ping          |- !x y z. 0 < z /\ is_ping (x,y,z) ==> step 0 (x,y,z) = 0
   step_0_of_pong          |- !x y z. 0 < z /\ is_pong (x,y,z) ==> step 0 (x,y,z) = 0
   step_0_of_pung          |- !x y z. 0 < z /\ is_pung (x,y,z) ==> 0 < step 0 (x,y,z)
   hop_identity_1          |- !m x z. (let xx = x - 2 * m * z in xx - 2 * z = x - 2 * (m + 1) * z)
   hop_identity_2          |- !m x z. (let xx = x - 2 * m * z in 0 < xx ==> 2 * z - xx = 2 * (m + 1) * z - x)
   hop_identity_3          |- !m x y z. (let xx = x - 2 * m * z;
                                             yy = y + m * x - m ** 2 * z
                                          in 0 < xx /\ 0 < yy ==>
                                             xx + yy - z = y + (m + 1) * x - (m + 1) ** 2 * z)
   hop_identity_4          |- !m x y z. (let xx = 2 * m * z - x;
                                             yy = y + m * x - m ** 2 * z
                                          in 0 < xx /\ 0 < yy ==>
                                             yy - z - xx = y + (m + 1) * x - (m + 1) ** 2 * z)
   hop_step_0_before_pong  |- !n m t. tik n /\ ~square n /\ n = windmill t /\ m <= step 0 t ==>
                                      hop m t = FUNPOW pung m t
   hop_step_0_at_pong      |- !n m t. tik n /\ ~square n /\ n = windmill t /\ m = step 0 t ==>
                                      hop (m + 1) t = pong (hop m t)
   hop_step_0_beyond_pong  |- !n m j t. tik n /\ ~square n /\ n = windmill t /\
                                        m = step 0 t /\ m + j < step (SQRT n) t ==>
                                        hop (m + 1 + j) t = FUNPOW ping j (hop (m + 1) t)
   hop_step_0_around_pong  |- !n m j t. tik n /\ ~square n /\ n = windmill t /\
                                        m = step 0 t /\ m + j < step (SQRT n) t ==>
                                        hop (m + 1 + j) t = (FUNPOW ping j o pong o FUNPOW pung m) t
   hop_step_0_before_pong_is_pung
                           |- !n m t. ~square n /\ n = windmill t /\ m < step 0 t ==> is_pung (hop m t)
   hop_step_0_at_pong_is_pong
                           |- !n m t. tik n /\ ~square n /\ n = windmill t /\ m = step 0 t /\ ~is_ping t ==>
                                      is_pong (hop m t)

   Hopping by step (SQRT n):
   step_sqrt_eq_0          |- !x y z. 0 < z ==>
                                      (step (SQRT (windmill (x,y,z))) (x,y,z) = 0 <=> is_ping (x,y,z))
   step_sqrt_of_ping       |- !x y z. 0 < z /\ is_ping (x,y,z) ==>
                                      step (SQRT (windmill (x,y,z))) (x,y,z) = 0
   step_sqrt_of_pong       |- !x y z. 0 < z /\ is_pong (x,y,z) ==>
                                      0 < step (SQRT (windmill (x,y,z))) (x,y,z)
   step_sqrt_of_pung       |- !x y z. 0 < z /\ is_pung (x,y,z) ==>
                                      0 < step (SQRT (windmill (x,y,z))) (x,y,z)
   step_0_le_step_sqrt     |- !x y z. 0 < z ==> step 0 (x,y,z) <= step (SQRT (windmill (x,y,z))) (x,y,z)
   step_0_lt_step_sqrt     |- !n t. ~square n /\ n = windmill t /\ ~is_ping t ==> step 0 t < step (SQRT n) t
   hop_step_0_beyond_pong_is_ping
                           |- !n m j t. tik n /\ ~square n /\ n = windmill t /\ m = step 0 t /\
                                        m + 1 + j < step (SQRT n) t ==> is_ping (hop (m + 1 + j) t)
   hop_step_sqrt_not_ping  |- !n t. tik n /\ ~square n /\ n = windmill t /\ ~is_ping t ==>
                                    ~is_ping (hop (step (SQRT n) t) t)

   Skipping by Triples:
   skip_ping_def           |- !t. skip_ping t = WHILE is_ping ping t
   skip_pung_def           |- !t. skip_pung t = WHILE is_pung pung t
   skip_ping_thm           |- !t k. ~is_ping (FUNPOW ping k t) /\ (!j. j < k ==> is_ping (FUNPOW ping j t)) ==>
                                    skip_ping t = FUNPOW ping k t
   skip_ping_none          |- !t. ~is_ping t ==> skip_ping t = t
   skip_pung_thm           |- !t k. ~is_pung (FUNPOW pung k t) /\ (!j. j < k ==> is_pung (FUNPOW pung j t)) ==>
                                    skip_pung t = FUNPOW pung k t
   skip_pung_none          |- !t. ~is_pung t ==> skip_pung t = t
   hopping_0               |- !n t. tik n /\ ~square n /\ n = windmill t ==>
                                    hopping 0 t = skip_pung t
   hopping_sqrt            |- !n t. tik n /\ ~square n /\ n = windmill t /\ ~is_ping t ==>
                                    hopping (SQRT n) t = skip_ping (pong (hopping 0 t))
   hopping_sqrt_eqn        |- !n t. tik n /\ ~square n /\ n = windmill t /\ ~is_ping t ==>
                                    hopping (SQRT n) t = (skip_ping o pong o skip_pung) t

   Picking Pongs along a Path:
   pong_list_def           |- !ls. pong_list ls = FILTER is_pong ls
   pong_list_nil           |- pong_list [] = []
   pong_list_length        |- !ls. LENGTH (pong_list ls) <= LENGTH ls
   pong_list_element       |- !ls j. (let  ps = pong_list ls
                                       in j < LENGTH ps ==> is_pong (EL j ps) /\ MEM (EL j ps) ls)
   pong_list_all_distinct  |- !ls. ls <> [] /\ ALL_DISTINCT ls ==> ALL_DISTINCT (pong_list (FRONT ls))
   pong_list_path_element  |- !n k j. (let ls = path n k;
                                           ps = pong_list (FRONT ls)
                                        in j < LENGTH ps ==> ?h. h < k /\ EL j ps = EL h ls /\ is_pong (EL h ls))
   pong_list_path_head     |- !n k. 0 < k ==> HD (pong_list (FRONT (path n k))) = (1,n DIV 4,1)
   pong_list_path_head_alt |- !n k. (let ls = path n k
                                      in 0 < k ==> HD (pong_list (FRONT ls)) = HD ls)
   pong_list_path_eq_nil   |- !n k. pong_list (FRONT (path n k)) = [] <=> k = 0

   tik_non_square_property |- !n. tik n /\ ~square n ==> FINITE (mills n) /\ zagier o flip PERMUTES mills n /\
                                  0 < iterate_period (zagier o flip) (1,1,n DIV 4)
   zagier_flip_iterate_period_eq_1
                           |- !k. iterate_period (zagier o flip) (1,1,k) = 1 <=> k = 1
   zagier_flip_iterate_period_ne_2
                           |- !k. iterate_period (zagier o flip) (1,1,k) <> 2
   tik_iterate_period_eq_1 |- !n. tik n ==> (iterate_period (zagier o flip) (1,1,n DIV 4) = 1 <=> n = 5)
   tik_path_head_flip_fix  |- !n k. (let ls = path n k in tik n ==> (flip (HD ls) = HD ls <=> n = 5))
   path_all_distinct       |- !n k. tik n /\ ~square n /\
                                    k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) ==>
                                    (ALL_DISTINCT (path n k) <=> n <> 5)
   path_skip_ping_thm      |- !n k p q. (let ls = path n k
                                          in p <= q /\ q <= k /\ ~is_ping (EL q ls) /\
                                             (!j. p <= j /\ j < q ==> is_ping (EL j ls)) ==>
                                             EL q ls = skip_ping (EL p ls))
   path_skip_pung_thm      |- !n k p q. (let ls = path n k
                                          in p <= q /\ q <= k /\ ~is_pung (EL q ls) /\
                                             (!j. p <= j /\ j < q ==> is_pung (EL j ls)) ==>
                                             EL q ls = skip_pung (EL p ls))
   pong_interval_next_pong |- !n k p q. (let ls = path n k
                                          in p < q /\ q <= k /\ is_pong (EL p ls) /\ is_pong (EL q ls) /\
                                             (!j. p < j /\ j < q ==> ~is_pong (EL j ls)) ==>
                                             EL q ls = (skip_pung o skip_ping o pong) (EL p ls))
   pong_list_pair_in_path  |- !n k j. (let ls = path n k;
                                           ps = pong_list (FRONT ls)
                                        in ALL_DISTINCT ls /\ j + 1 < LENGTH ps ==>
                                           ?p q. p < q /\ q < k /\ EL p ls = EL j ps /\
                                                 EL q ls = EL (j + 1) ps /\ is_pong (EL p ls) /\ is_pong (EL q ls) /\
                                                 !h. p < h /\ h < q ==> ~is_pong (EL h ls))
   pong_list_path_element_suc
                           |- !n k j. (let ls = path n k;
                                           ps = pong_list (FRONT ls)
                                        in ALL_DISTINCT ls /\ j + 1 < LENGTH ps ==>
                                           EL (j + 1) ps = (skip_pung o skip_ping o pong) (EL j ps))
   pong_list_path_element_eqn
                           |- !n k j. (let ls = path n k;
                                           ps = pong_list (FRONT ls)
                                        in ALL_DISTINCT ls /\ j < LENGTH ps ==>
                                           EL j ps = FUNPOW (skip_pung o skip_ping o pong) j (HD ps))

   Hopping nodes:
   beyond_pong_def         |- !t. beyond_pong t = (skip_ping o pong) t
   beyond_pong_eqn         |- !n t. tik n /\ ~square n /\ n = windmill t /\ is_pong t ==> beyond_pong t = hopping (SQRT n) t
   pong_interval_beyond_pong
                           |- !n k p q. (let ls = path n k
                                          in p < q /\ q <= k /\ is_pong (EL p ls) /\ is_pong (EL q ls) /\
                                             (!j. p < j /\ j < q ==> ~is_pong (EL j ls)) ==>
                                             beyond_pong (EL q ls) = (skip_ping o pong o skip_pung) (beyond_pong (EL p ls)))
   hop_nodes_def           |- !ls. hop_nodes ls = MAP beyond_pong (pong_list (FRONT ls))
   hop_nodes_length        |- !ls. LENGTH (hop_nodes ls) = LENGTH (pong_list (FRONT ls))
   hop_nodes_element       |- !ls j. j < LENGTH (hop_nodes ls) ==> EL j (hop_nodes ls) = beyond_pong (EL j (pong_list (FRONT ls)))
   hop_nodes_path_eq_nil   |- !n k. hop_nodes (path n k) = [] <=> k = 0
   hop_nodes_path_head     |- !n k. (let ls = path n k
                                      in tik n /\ ~square n /\ 0 < k ==> HD (hop_nodes ls) = hopping (SQRT n) (HD ls))
   hop_nodes_path_element_less
                           |- !n k j. (let ls = path n k;
                                        ns = hop_nodes ls;
                                         t = EL j ns
                                        in tik n /\ ALL_DISTINCT ls /\ j + 1 < LENGTH ns ==>
                                           n = windmill t /\ ~is_ping t /\ MEM t ls /\ t <> LAST ls)
   hop_nodes_path_element_last
                           |- !n k j. (let ls = path n k;
                                           ns = hop_nodes ls;
                                            t = EL j ns
                                        in tik n /\ ~square n /\ ALL_DISTINCT ls /\ j + 1 = LENGTH ns /\
                                           flip (LAST ls) = LAST ls ==>
                                           n = windmill t /\ ~is_ping t /\ MEM t ls /\ t = LAST ls)
   hop_nodes_path_element_thm
                           |- !n k j. (let ls = path n k;
                                           ns = hop_nodes ls;
                                            t = EL j ns
                                        in tik n /\ ~square n /\ ALL_DISTINCT ls /\ j < LENGTH ns /\
                                           flip (LAST ls) = LAST ls ==>
                                           n = windmill t /\ ~is_ping t /\ MEM t ls /\ (t = LAST ls <=> j + 1 = LENGTH ns))
   hop_nodes_path_element_eqn
                           |- !n k j. (let ls = path n k;
                                           ns = hop_nodes ls
                                        in tik n /\ ~square n /\ ALL_DISTINCT ls /\
                                           flip (LAST ls) = LAST ls /\ j < LENGTH ns ==>
                                           EL j ns = FUNPOW (hopping (SQRT n)) (j + 1) (HD ls))
   hop_nodes_path_last     |- !n k. (let ls = path n k;
                                         ns = hop_nodes ls
                                      in tik n /\ ~square n /\ ALL_DISTINCT ls /\
                                         flip (LAST ls) = LAST ls /\ 0 < k ==>
                                         LAST ns = LAST ls /\
                                         LAST ls = FUNPOW (hopping (SQRT n)) (LENGTH ns) (HD ls))

   Hopping for tik primes:
   tik_prime_property  |- !n. (let s = mills n;
                                   u = (1,1,n DIV 4)
                                in tik n /\ prime n ==>
                                   ~square n /\ FINITE s /\ zagier involute s /\ flip involute s /\
                                   fixes zagier s = {u} /\ ODD (iterate_period (zagier o flip) u))
   tik_prime_iterate_period_odd
                       |- !n. tik n /\ prime n ==> ODD (iterate_period (zagier o flip) (1,1,n DIV 4))
   path_last_at_half_period
                       |- !n k. (let ls = path n k;
                                      u = (1,1,n DIV 4);
                                      p = iterate_period (zagier o flip) u
                                  in k = 1 + HALF p ==> LAST ls = FUNPOW (zagier o flip) (HALF p) u)
   tik_prime_path_last_flip_fix
                       |- !n k. (let ls = path n k
                                  in tik n /\ prime n /\
                                     k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) ==>
                                     flip (LAST ls) = LAST ls)
   tik_prime_path_not_flip_fix
                       |- !n k j. (let ls = path n k
                                    in tik n /\ prime n /\
                                       k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) /\
                                       0 < j /\ j < k ==> flip (EL j ls) <> EL j ls)
   tik_prime_path_flip_fix_iff
                       |- !n k j. (let ls = path n k
                                    in tik n /\ prime n /\
                                       k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) /\
                                       0 < j /\ j <= k ==> (flip (EL j ls) = EL j ls <=> j = k))
   tik_prime_path_flip_fix_iff_alt
                       |- !n k t. (let ls = path n k
                                    in tik n /\ prime n /\ k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) /\
                                       MEM t ls /\ flip (HD ls) <> HD ls ==> (flip t = t <=> t = LAST ls))
   tik_prime_path_hopping_while_thm
                       |- !n k. (let ls = path n k
                                  in tik n /\ prime n /\ k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) ==>
                                     WHILE (\t. flip t <> t) (hopping (SQRT n)) (HD ls) = LAST ls)
   two_sq_hop_thm      |- !n. tik n /\ prime n ==> two_sq_hop n IN fixes flip (mills n)
   two_squares_hop_def |- !n. two_squares_hop n = (let (x,y,z) = two_sq_hop n in (x,y + z))
   two_squares_hop_thm |- !n. tik n /\ prime n ==> (let (u,v) = two_squares_hop n in n = u ** 2 + v ** 2)

   Popping as direct hop:
   pop_def             |- !m x y z. pop m (x,y,z) = (2 * m * z - x,z,y + m * x - m * m * z)
   popping_def         |- !k t. popping k t = pop (step k t) t
   popping_sqrt_eq_hopping_sqrt
                       |- !n t. ~square n /\ n = windmill t /\ ~is_ping t ==>
                                popping (SQRT n) t = hopping (SQRT n) t
   popping_sqrt_eqn    |- !n t. tik n /\ ~square n /\ n = windmill t /\ ~is_ping t ==>
                                popping (SQRT n) t = (skip_ping o pong o skip_pung) t
   beyond_pong_eqn_by_pop
                       |- !n t. tik n /\ ~square n /\ n = windmill t /\ is_pong t ==> beyond_pong t = popping (SQRT n) t
   hop_nodes_path_head_by_pop
                       |- !n k j. (let ls = path n k;
                                       ns = hop_nodes ls
                                    in tik n /\ ~square n /\ 0 < k ==> HD ns = popping (SQRT n) (HD ls))
   hop_nodes_path_element_eqn_by_pop
                       |- !n k j. (let ls = path n k;
                                       ns = hop_nodes ls
                                    in tik n /\ ~square n /\ ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls /\ j < LENGTH ns ==>
                                       EL j ns = FUNPOW (popping (SQRT n)) (j + 1) (HD ls))
   hop_nodes_path_last_by_pop
                       |- !n k. (let ls = path n k;
                                     ns = hop_nodes ls
                                  in tik n /\ ~square n /\ ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls /\ 0 < k ==>
                                     LAST ns = LAST ls /\ LAST ls = FUNPOW (popping (SQRT n)) (LENGTH ns) (HD ls))
   tik_prime_path_popping_while_thm
                       |- !n k. (let ls = path n k
                                  in tik n /\ prime n /\ k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) ==>
                                     WHILE (\t. flip t <> t) (popping (SQRT n)) (HD ls) = LAST ls)
   two_sq_pop_def      |- !n. two_sq_pop n = WHILE ($~ o found) (popping (SQRT n)) (1,n DIV 4,1)
   two_squares_pop_def |- !n. two_squares_pop n = (let (x,y,z) = two_sq_pop n in (x,y + z))
   two_sq_pop_eqn      |- !n. tik n /\ prime n ==> two_sq_pop n = two_sq_hop n
   two_sq_pop_thm      |- !n. tik n /\ prime n ==> two_sq_pop n IN fixes flip (mills n)
   two_squares_pop_thm |- !n. tik n /\ prime n ==> (let (u,v) = two_squares_pop n in n = u ** 2 + v ** 2)

   Direct Popping Nodes:
   node_def            |- (!n. node n 0 = (1,n DIV 4,1)) /\ !n j. node n (SUC j) = popping (SQRT n) (node n j)
   node_0              |- !n. node n 0 = (1,n DIV 4,1)
   node_suc            |- !n j. node n (SUC j) = popping (SQRT n) (node n j)
   node_1              |- !n. node n 1 = popping (SQRT n) (1,n DIV 4,1)
   node_thm            |- !n j. node n j = FUNPOW (popping (SQRT n)) j (1,n DIV 4,1)
   node_path_eqn       |- !n k j. (let ls = path n k;
                                       ns = hop_nodes ls
                                    in tik n /\ ~square n /\ ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls /\
                                       j < LENGTH ns ==> node n (j + 1) = EL j ns)
   node_path_last      |- !n k. (let ls = path n k;
                                     ns = hop_nodes ls
                                  in tik n /\ ~square n /\ ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls /\
                                     0 < k ==> node n (LENGTH ns) = LAST ls)
   node_path_last_iff  |- !n k j. (let ls = path n k;
                                       ns = hop_nodes ls
                                    in tik n /\ ~square n /\ ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls /\ j < LENGTH ns ==>
                                       node n (j + 1) = EL j ns /\ (node n (j + 1) = LAST ls <=> j + 1 = LENGTH ns))

   Hopping along Path (useful theorems):
   path_start_over_ping    |- !n k. (let h = HALF (1 + SQRT n)
                                      in tik n /\ ~square n /\ h <= k ==>
                                         !j. 0 < j /\ j < h ==> is_ping (EL j (path n k)))
   path_start_beyond_ping  |- !n k. (let h = HALF (1 + SQRT n)
                                      in tik n /\ ~square n /\ h <= k ==> ~is_ping (EL h (path n k)))
   path_start_skip_ping    |- !n k. (let ls = path n k;
                                          h = HALF (1 + SQRT n)
                                      in tik n /\ ~square n /\ h <= k ==>
                                         skip_ping (EL 1 ls) = EL (step (SQRT n) (1,n DIV 4,1)) ls)
   hop_step_0_path_element_before_pong
                           |- !n k u m. (let ls = path n k
                                          in tik n /\ ~square n /\ u <= k /\ m <= step 0 (EL u ls) ==>
                                             hop m (EL u ls) = FUNPOW pung m (EL u ls))
   hop_step_0_path_element_at_pong
                           |- !n k u m. (let ls = path n k
                                          in tik n /\ ~square n /\ u <= k /\ m = step 0 (EL u ls) ==>
                                             hop (m + 1) (EL u ls) = pong (hop m (EL u ls)))
   hop_step_0_path_element_beyond_pong
                           |- !n k u m j. (let ls = path n k
                                            in tik n /\ ~square n /\ u <= k /\
                                               m = step 0 (EL u ls) /\ m + j < step (SQRT n) (EL u ls) ==>
                                               hop (m + 1 + j) (EL u ls) = FUNPOW ping j (hop (m + 1) (EL u ls)))
   hop_step_0_path_element_around_pong
                           |- !n k u m j. (let ls = path n k
                                            in tik n /\ ~square n /\ u <= k /\
                                               m = step 0 (EL u ls) /\ m + j < step (SQRT n) (EL u ls) ==>
                                               hop (m + 1 + j) (EL u ls) = (FUNPOW ping j o pong o FUNPOW pung m) (EL u ls))
   hop_step_0_path_element |- !n k u m. (let ls = path n k
                                          in tik n /\ ~square n /\ flip (LAST ls) = LAST ls /\
                                             u < k /\ m <= step 0 (EL u ls) ==>
                                             u + m < k /\ hop m (EL u ls) = EL (u + m) ls)
   hop_step_0_suc          |- !n k u j. (let ls = path n k
                                          in tik n /\ ~square n /\ flip (LAST ls) = LAST ls /\
                                             u < k /\ j < step 0 (EL u ls) ==>
                                             hop (SUC j) (EL u ls) = (zagier o flip) (hop j (EL u ls)))
   hopping_path_step_0     |- !n k u. (let ls = path n k
                                        in tik n /\ ~square n /\ flip (LAST ls) = LAST ls /\
                                           u < k ==> hopping 0 (EL u ls) = skip_pung (EL u ls))
   pong_list_path_element_suc_by_hop
                           |- !n k j. (let ls = path n k;
                                           ps = pong_list (FRONT ls)
                                        in tik n /\ ~square n /\ ALL_DISTINCT ls /\ j + 1 < LENGTH ps ==>
                                           EL (j + 1) ps = (hopping 0 o beyond_pong) (EL j ps))
   pong_list_path_element_eqn_by_hop
                           |- !n k j. (let ls = path n k;
                                           ps = pong_list (FRONT ls)
                                        in tik n /\ ~square n /\ ALL_DISTINCT ls /\ j < LENGTH ps ==>
                                           EL j ps = FUNPOW (hopping 0 o beyond_pong) j (HD ps))
   hop_nodes_path_element_findi_range
                       |- !n k j. (let ls = path n k;
                                       ns = hop_nodes ls;
                                       ps = pong_list (FRONT ls)
                                    in ALL_DISTINCT ls /\ j + 1 < LENGTH ns ==>
                                       findi (EL j ps) ls < findi (EL j ns) ls /\
                                       findi (EL j ns) ls <= findi (EL (j + 1) ps) ls)
   hop_nodes_path_element_findi_thm
                       |- !n k j h. (let ls = path n k;
                                         ns = hop_nodes ls;
                                         ps = pong_list (FRONT ls)
                                      in ALL_DISTINCT ls /\ j + 1 + h < LENGTH ns ==>
                                         findi (EL j ps) ls < findi (EL j ns) ls /\
                                         findi (EL j ns) ls <= findi (EL (j + 1 + h) ps) ls)
   hop_nodes_path_element_findi_last
                       |- !n k. (let ls = path n k;
                                     ns = hop_nodes ls;
                                     ps = pong_list (FRONT ls)
                                  in tik n /\ ~square n /\ ALL_DISTINCT ls /\
                                     flip (LAST ls) = LAST ls /\ 0 < k ==>
                                     findi (LAST ns) ls = k /\ findi (LAST ps) ls < k)
   hop_nodes_path_all_distinct
                       |- !n k. (let ls = path n k
                                  in tik n /\ ~square n /\ ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls ==>
                                     ALL_DISTINCT (hop_nodes ls))

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The zagier-flip permutation.                                              *)
(* ------------------------------------------------------------------------- *)

(* The three cases of Zagier map, or the Zagier-flip map.

zagier_def
|- !x y z. zagier (x,y,z) =
           if x < y - z then (x + 2 * z,z,y - z - x)
           else if x < 2 * y then (2 * y - x,y,x + z - y)
           else (x - 2 * y,x + z - y,y)
these cases are clean by checking (2 * y - x).
Note n = x² + 4yz, so z = (n - x²)/4y. Eliminating z:
           x < y - z
iff        x < y - (n - x²)/4y
iff      4xy < 4y² - n + x²
iff        n < 4y² - 4xy + x² = (2y - x)²
iff       √n < 2y - x

also       x < 2 * y
iff        0 < 2y - x

and the last case: 2y < x, or 2y - x < 0, or 2y - x = 0 in integer arithmetic.

zagier_flip_eqn
|- !x y z. (zagier o flip) (x,y,z) =
           if x < z - y then (x + 2 * y,y,z - y - x)
           else if x < 2 * z then (2 * z - x,z,x + y - z)
           else (x - 2 * z,x + y - z,z)
these cases are clean by checking (2 * z - x).
Note n = x² + 4yz, so y = (n - x²)/4z. Eliminating y:
             x < z - y
iff          x < z - (n - x²)/4z
iff        4xz < 4z² - n + x²
iff          n < 4z² - 4xz + x² = (2z - x)²
iff         √n < 2z - x

also         x < 2 * z
iff          0 < 2z - x

and the last case: 2z < x, or 2z - x < 0, or 2z - x = 0 in integer arithmetic.
*)

(* Define the map for each case of zagier_flip *)
Definition ping_def:
   ping (x,y,z) = (x + 2 * y, y, z - y - x)
End

Definition pong_def:
   pong (x,y,z) = (2 * z - x, z, x + y - z)
End

Definition pung_def:
   pung (x,y,z) = (x - 2 * z, x + y - z, z)
End

(* Theorem: ping (x,y,z) = (x + 2 * y,y,z - (x + y)) *)
(* Proof:
        ping (x,y,z)
      = (x + 2 * y,y,z - y - x)    by ping_def
      = (x + 2 * y,y,z - (x + y))  by SUB_RIGHT_SUB
*)
Theorem ping_alt:
  !x y z. ping (x,y,z) = (x + 2 * y,y,z - (x + y))
Proof
  simp[ping_def]
QED

(* Matrices:
   ping   A = [[1,2,0],[0,1,0],[-1,-1,1]]  A^2 = [[1,4,0],[0,1,0],[-2,-4,1]]  same form A^m = [[1,2m,0],[0,1,0],[-m,-m*m,1]]
   pong   B = [[-1,0,2],[0,0,1],[1,1,-1]]  B^2 = [[3,2,-4],[1,1,-1],[-2,-1,4]]
   pung   C = [[1,0,-2],[1,1,-1],[0,0,1]]  C^2 = [[1,0,-4],[2,1,-4],[0,0,1]]  same form C^m = [[1,0,-2m],[m,1,-m*m],[0,0,1]]
*)

(* Define the ping, pong, pung conditions *)
Definition is_ping_def:
   is_ping (x, y, z) <=> x < z - y
End
Definition is_pong_def:
   is_pong (x, y, z) <=> ~(x < z - y) /\ x < 2 * z
End
Definition is_pung_def:
   is_pung (x, y, z) <=> ~(x < z - y) /\ ~(x < 2 * z)
End

(* Theorem: is_ping t \/ is_pong t \/ is_pung t *)
(* Proof:
   Let (x,y,z) = t                 by FORALL_PROD
   Then true by is_ping_def, is_pong_def, is_pung_def
*)
Theorem triple_cases:
  !t. is_ping t \/ is_pong t \/ is_pung t
Proof
  simp[is_ping_def, is_pong_def, is_pung_def, FORALL_PROD]
QED

(* Theorem: is_ping t ==> ~is_pong t *)
(* Proof: by is_ping_def, is_pong_def. *)
Theorem ping_not_pong:
  !t. is_ping t ==> ~is_pong t
Proof
  rpt strip_tac >>
  `?x y z. t = (x,y,z)` by metis_tac[triple_parts] >>
  fs[is_ping_def, is_pong_def]
QED

(* Theorem: is_ping t ==> ~is_pung t *)
(* Proof: by is_ping_def, is_pung_def. *)
Theorem ping_not_pung:
  !t. is_ping t ==> ~is_pung t
Proof
  rpt strip_tac >>
  `?x y z. t = (x,y,z)` by metis_tac[triple_parts] >>
  fs[is_ping_def, is_pung_def]
QED

(* Theorem: is_pong t ==> ~is_ping t *)
(* Proof: by is_pong_def, is_ping_def. *)
Theorem pong_not_ping:
  !t. is_pong t ==> ~is_ping t
Proof
  rpt strip_tac >>
  `?x y z. t = (x,y,z)` by metis_tac[triple_parts] >>
  fs[is_pong_def, is_ping_def]
QED

(* Theorem: is_pong t ==> ~is_pung t *)
(* Proof: by is_pong_def, is_pung_def. *)
Theorem pong_not_pung:
  !t. is_pong t ==> ~is_pung t
Proof
  rpt strip_tac >>
  `?x y z. t = (x,y,z)` by metis_tac[triple_parts] >>
  fs[is_pong_def, is_pung_def]
QED

(* Theorem: is_pung t ==> ~is_ping t *)
(* Proof: by is_pung_def, is_ping_def. *)
Theorem pung_not_ping:
  !t. is_pung t ==> ~is_ping t
Proof
  rpt strip_tac >>
  `?x y z. t = (x,y,z)` by metis_tac[triple_parts] >>
  fs[is_pung_def, is_ping_def]
QED

(* Theorem: is_pung t ==> ~is_pong t *)
(* Proof: by is_pung_def, is_pong_def. *)
Theorem pung_not_pong:
  !t. is_pung t ==> ~is_pong t
Proof
  rpt strip_tac >>
  `?x y z. t = (x,y,z)` by metis_tac[triple_parts] >>
  fs[is_pung_def, is_pong_def]
QED

(* Theorem: is_ping (x,y,z) <=> SQRT (windmill (x,y,z)) < 2 * z - x *)
(* Proof:
   Let n = windmill (x,y,z).
   Then n = x ** 2 + 4 * y * z                 by windmill_def
    and is_ping (x,y,z) <=> x < z - y          by is_ping_def

   If part: x < z - y ==> SQRT n < 2 * z - x
      By contradiction, suppose 2 * z - x <= SQRT n.
      Note x < 2 * z, 0 < z                    by x < z - y
          2 * z - x <= SQRT n
      ==> (2 * z - x) ** 2 <= (SQRT n) ** 2    by EXP_EXP_LE_MONO_IMP
      ==> (2 * z - x) ** 2 <= n                by SQ_SQRT_LE_alt, LESS_EQ_TRANS
      ==> 4 * z ** 2 + x ** 2 - 4 * z * x <= n                     by binomial_sub, x < 2 * z
      ==> x ** 2 + 4 * z * z - 4 * z * x <= x ** 2 + 4 * y * z     by EXP_2
      ==> 4 * z * (z - x) <= 4 * z * y         by LEFT_SUB_DISTRIB
      ==> z - x <= y                           by LT_MULT_LCANCEL, 0 < z
      ==> z - y <= x                           by inequaltiy
      This contradicts x < z - y.

   Only-if part: SQRT n < 2 * z - x ==> x < z - y
      Note 0 < 2 * z - x                       by SQRT n < 2 * z - x
        so x < 2 * z and 0 < z                 by inequality
           SQRT n < 2 * z - x
       <=> SQRT n < SQRT ((2 * z - x) ** 2)    by SQRT_OF_SQ
       ==> n < (2 * z - x) ** 2                by SQRT_LT_SQRT
       <=> x ** 2 + 4 * y * z < 4 * z ** 2 + x ** 2 - 4 * z * x
                                               by binomial_sub, x < 2 * z
       <=> 4 * y * z  < 4 * z * z - 4 * z * x  by EXP_2
       <=> (4 * z) * y < 4 * z * (z - x)       by LEFT_SUB_DISTRIB
       <=> y < z - x                           by LT_MULT_LCANCEL, 0 < z
       <=> y + x < z                           by inequality
       <=> x < z - y                           by inequality
*)
Theorem is_ping_alt:
  !x y z. is_ping (x,y,z) <=> SQRT (windmill (x,y,z)) < 2 * z - x
Proof
  rpt strip_tac >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  rw[is_ping_def, EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `2 * z - x <= SQRT n` by decide_tac >>
    `0 < z /\ x < 2 * z` by decide_tac >>
    `4 * z * x < 4 * z * z` by simp[] >>
    `(2 * z - x) ** 2 <= (SQRT n) ** 2` by fs[EXP_EXP_LE_MONO_IMP] >>
    `(SQRT n) ** 2 <= n` by simp[SQ_SQRT_LE_alt] >>
    `(2 * z - x) ** 2 = x ** 2 + 4 * z * z - 4 * z * x` by simp[binomial_sub, Once EXP_2] >>
    `_ = x ** 2 + 4 * z * (z - x)` by decide_tac >>
    `n = x ** 2 + 4 * z * y` by simp[windmill_def, Abbr`n`] >>
    `4 * z * (z - x) <= 4 * z * y` by decide_tac >>
    fs[],
    `n = x ** 2 + 4 * z * y` by simp[windmill_def, Abbr`n`] >>
    `n < (2 * z - x) ** 2` by metis_tac[SQRT_OF_SQ, SQRT_LT_SQRT] >>
    `(2 * z - x) ** 2 = x ** 2 + 4 * z * z - 4 * z * x` by fs[binomial_sub, Once EXP_2] >>
    `_ = x ** 2 + 4 * z * (z - x)` by decide_tac >>
    `4 * z * y < 4 * z * (z - x)` by decide_tac >>
    fs[]
  ]
QED

(* Theorem: is_pong (x,y,z) <=> 0 < 2 * z - x /\ 2 * z - x <= SQRT (windmill (x,y,z)) *)
(* Proof:
   Let n = windmill (x,y,z).
   If part: is_pong (x,y,z) <=> 0 < 2 * z - x /\ 2 * z - x <= SQRT n
      Note x < 2 * z               by is_pong_def
        so 0 < 2 * z - x           by inequaltiy
      Also ~is_ping (x,y,z)        by pong_not_ping
        so ~(SQRT n < 2 * z - x)   by is_ping_alt
        or 2 * z - x <= SQRT n     by NOT_LESS

   Only-if part: 0 < 2 * z - x /\ 2 * z - x <= SQRT n ==> is_pong (x,y,z)
      Note 2 * z - x <= SQRT n
       <=> ~(SQRT n < 2 * z - x)   by NOT_LESS
       <=> ~is_ping (x,y,z)        by is_ping_alt
       <=> ~(x < z - y)            by is_ping_def
       and x < 2 * z               by 0 < 2 * z - x
       ==> is_pong (x,y,z)         by is_pong_def
*)
Theorem is_pong_alt:
  !x y z. is_pong (x,y,z) <=> 0 < 2 * z - x /\ 2 * z - x <= SQRT (windmill (x,y,z))
Proof
  rw_tac bool_ss [EQ_IMP_THM] >-
  fs[is_pong_def] >-
  metis_tac[pong_not_ping, is_ping_alt, NOT_LESS] >>
  `~is_ping (x,y,z)` by fs[is_ping_alt] >>
  fs[is_ping_def, is_pong_def]
QED

(* Theorem: is_pung (x,y,z) <=> 2 * z - x = 0 *)
(* Proof:
   Let n = windmill (x,y,z).
   If part: is_pung (x,y,z) ==> 2 * z - x = 0
      Note ~is_ping (x,y,z)        by pung_not_ping
        so ~(SQRT n < 2 * z - x)   by is_ping_alt
       and ~is_pong (x,y,z)        by pung_not_pong
        so ~(0 < 2 * z - x)        by is_pong_alt
        or 2 * z - x = 0           by arithmetic

   Only-if part: 2 * z - x = 0 ==> is_pung (x,y,z)
      Note ~((SQRT n) < 2 * z - x) by 2 * z - x = 0
        so ~is_ping (x,y,z)        by is_ping_alt
      Also ~(0 < 2 * z - x)        by 2 * z - x = 0
        so ~is_pong (x,y,z)        by is_pong_alt
      Thus is_pung (x,y,z)         by triple_cases
*)
Theorem is_pung_alt:
  !x y z. is_pung (x,y,z) <=> 2 * z - x = 0
Proof
  rpt strip_tac >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  rw[EQ_IMP_THM] >| [
    `~(0 < 2 * z - x /\ 2 * z - x <= SQRT n)` by metis_tac[pung_not_pong, is_pong_alt] >>
    `~(SQRT n < 2 * z - x)` by metis_tac[pung_not_ping, is_ping_alt] >>
    decide_tac,
    `~(0 < 2 * z - x) /\ ~((SQRT n) < 2 * z - x)` by decide_tac >>
    metis_tac[is_ping_alt, is_pong_alt, triple_cases]
  ]
QED

(* Theorem: 2 * x < z ==> is_ping (x,x,z) *)
(* Proof:
      is_ping (x,x,z)
   <=> x < z - x               by is_ping_def
   <=> x + x < z               by SUB_LEFT_LESS
   <=> 2 * x < z               by arithmetic
   <=> T                       by given
*)
Theorem is_ping_x_x_z:
  !x z. 2 * x < z ==> is_ping (x,x,z)
Proof
  simp[is_ping_def]
QED

(*
> EVAL ``is_ping (1,1,0)``; <=> F: thm
> EVAL ``is_ping (1,1,1)``; <=> F: thm
> EVAL ``is_ping (1,1,2)``; <=> F: thm
> EVAL ``is_ping (1,1,3)``; <=> T: thm
*)

(* Theorem: 2 < k ==> is_ping (1,1,k) *)
(* Proof: by is_ping_x_x_z. *)
Theorem is_ping_1_1_k:
  !k. 2 < k ==> is_ping (1,1,k)
Proof
  simp[is_ping_x_x_z]
QED

(* Theorem: ~is_ping (x,y,y) *)
(* Proof:
   Note x < y - y is false         by arithmetic
     so ~is_ping (x,y,y)           by is_ping_def
*)
Theorem not_ping_x_y_y:
  !x y. ~is_ping (x,y,y)
Proof
  simp[is_ping_def]
QED

(* Theorem: 0 < x ==> is_pong (x,y,x) *)
(* Proof:
   Note x < x - y is false         by arithmetic, 0 < x
    but x < 2 * x is true          by arithmetic, 0 < x
     so is_pong (x,y,x)            by is_pong_def
*)
Theorem is_pong_x_y_x:
  !x y. 0 < x ==> is_pong (x,y,x)
Proof
  simp[is_pong_def]
QED

(* Idea: A triple (x,y,z) is a ping if, and only if, ping (x,y,z) has third positive. *)

(* Theorem: let (x,y,z) = ping t in is_ping t <=> 0 < z *)
(* Proof:
   Let (xx,yy,zz) = t                          by FORALL_PROD
   Then (x,y,z) = ping t
    ==> x = xx + 2 * yy,
        y = yy,
        z = zz - xx - yy                       by ping_def
        is_ping t
    <=> is_ping (xx,yy,zz)                     by notation
    <=> xx < zz - yy                           by is_ping_def
    <=> 0 < zz - yy - xx                       by SUB_LESS_0
    <=> 0 < zz - (yy + xx)                     by SUB_RIGHT_SUB
    <=> 0 < zz - (xx + yy)                     by ADD_COMM
    <=> 0 < zz - xx - yy                       by SUB_RIGHT_SUB
    <=> 0 < z                                  by notation
*)
Theorem is_ping_by_ping:
  !t. let (x,y,z) = ping t in is_ping t <=> 0 < z
Proof
  simp[ping_def, is_ping_def, FORALL_PROD]
QED

(* Idea: A triple (x,y,z) is a pung if pong (x,y,z) has first and third positive. *)

(* Theorem: let (x,y,z) = ping t in 0 < x /\ 0 < z ==> is_pong t *)
(* Proof:
   Let (xx,yy,zz) = t                          by FORALL_PROD
   Then (x,y,z) = pong t
   Let x = 2 * zz - xx,
       y = zz,
       z = xx + yy - zz                        by pong_def
        0 < x
    <=> 0 < 2 * zz - xx
    <=> xx < 2 * zz                            by SUB_LESS_0, [1]
        0 < zz
    <=> 0 < xx + yy - zz
    <=> zz < xx + yy                           by SUB_EQ_0
    ==> zz - yy < xx                           by SUB_RIGHT_LESS, [2]
   Thus is_pung t                              by is_pung_def, [1][2]
*)
Theorem is_pong_by_pong:
  !t. let (x,y,z) = pong t in 0 < x /\ 0 < z ==> is_pong t
Proof
  simp[pong_def, is_pong_def, FORALL_PROD]
QED

(* Idea: A triple (x,y,z) is a pung if pung (x,y,z) has first positive. *)

(* Theorem: let (x,y,z) = pung t in 0 < x ==> is_pung t *)
(* Proof:
   Let (xx,yy,zz) = t                          by FORALL_PROD
   Then (x,y,z) = pung t
    ==> x = xx - 2 * zz,
        y = xx + yy - zz,
        z = zz                                 by pung_def
        0 < x
    <=> 0 < xx - 2 * zz
    <=> 2 * zz < xx                            by SUB_LESS_0
    ==> 2 * zz - xx = 0                        by SUB_EQ_0
    <=> is_pung t                              by is_pung_alt
*)
Theorem is_pung_by_pung:
  !t. let (x,y,z) = pung t in 0 < x ==> is_pung t
Proof
  simp[pung_def, is_pung_alt, FORALL_PROD]
QED

(* ------------------------------------------------------------------------- *)
(* Zagier and Flip composition                                               *)
(* ------------------------------------------------------------------------- *)

(* Theorem: (zagier o flip) t = if is_ping t then ping t else if is_pong t then pong t else pung t *)
(* Proof: Let t = (x,y,z), by zagier_flip_eqn, ping_def, pong_def, pung_def, is_ping_def, is_pong_def. *)
Theorem zagier_flip_thm:
  !t. (zagier o flip) t = if is_ping t then ping t
                          else if is_pong t then pong t else pung t
Proof
  simp[zagier_flip_eqn, ping_def, pong_def, pung_def, is_ping_def, is_pong_def, FORALL_PROD]
QED

(* Theorem: is_ping t ==> (zagier o flip) t = ping t *)
(* Proof: by zagier_flip_thm. *)
Theorem zagier_flip_ping:
  !t. is_ping t ==> (zagier o flip) t = ping t
Proof
  simp[zagier_flip_thm]
QED

(* Theorem: is_pong t ==> (zagier o flip) t = pong t *)
(* Proof: by zagier_flip_thm, pong_not_ping. *)
Theorem zagier_flip_pong:
  !t. is_pong t ==> (zagier o flip) t = pong t
Proof
  simp[zagier_flip_thm, pong_not_ping]
QED

(* Theorem: is_pung t ==> (zagier o flip) t = pung t *)
(* Proof: by zagier_flip_thm, pung_not_ping, pung_not_pong. *)
Theorem zagier_flip_pung:
  !t. is_pung t ==> (zagier o flip) t = pung t
Proof
  simp[zagier_flip_thm, pung_not_ping, pung_not_pong]
QED

(* Theorem: (!j. j < m ==> is_ping (FUNPOW ping j t)) ==> FUNPOW (zagier o flip) m t = FUNPOW ping m t *)
(* Proof:
   By induction on m.
   Base: (!j. j < 0 ==> is_ping (FUNPOW ping j t)) ==> FUNPOW (zagier o flip) 0 t = FUNPOW ping 0 t
      FUNPOW (zagier o flip) 0 t
    = t                            by FUNPOW_0
    = FUNPOW ping 0 t              by FUNPOW_0

   Step: (!j. j < m ==> is_ping (FUNPOW ping j t)) ==> FUNPOW (zagier o flip) m t = FUNPOW ping m t ==>
         (!j. j < SUC m ==> is_ping (FUNPOW ping j t)) ==> FUNPOW (zagier o flip) (SUC m) t = FUNPOW ping (SUC m) t
      Note !j. j < SUC m ==> is_ping (FUNPOW ping j t)
       <=> !j. (j < m \/ j = m) ==> is_ping (FUNPOW ping j t)      by arithmetic
       <=> is_ping (FUNPOW ping m t) /\
           !j. j < m ==> is_ping (FUNPOW ping j t)                 by DISJ_IMP_THM

           is_ping (FUNPOW ping (SUC m) t)
       <=> is_ping (ping (FUNPOW ping m t))                        by FUNPOW_SUC
       <=> is_ping ((zagier o flip) (FUNPOW ping m t))             by zagier_flip_ping, [1]

        FUNPOW (zagier o flip) (SUC m) t
      = (zagier o flip) (FUNPOW (zagier o flip) m t)               by FUNPOW_SUC
      = (zagier o flip) (FUNPOW ping m t)                          by induction hypothesis
      = ping (FUNPOW ping m t)                                     by zagier_flip_ping, [1]
      = FUNPOW ping (SUC m) t                                      by FUNPOW_SUC
*)
Theorem zagier_flip_ping_funpow:
  !m t. (!j. j < m ==> is_ping (FUNPOW ping j t)) ==> FUNPOW (zagier o flip) m t = FUNPOW ping m t
Proof
  rpt strip_tac >>
  Induct_on `m` >-
  simp[] >>
  strip_tac >>
  `!j. j < SUC m <=> (j < m \/ j = m)` by decide_tac >>
  `is_ping (FUNPOW ping m t) /\ !j. j < m ==> is_ping (FUNPOW ping j t)` by metis_tac[] >>
  fs[FUNPOW_SUC, zagier_flip_ping]
QED

(* Theorem: (!j. j < m ==> is_pung (FUNPOW pung j t)) ==> FUNPOW (zagier o flip) m t = FUNPOW pung m t *)
(* Proof:
   By induction on m.
   Base: (!j. j < 0 ==> is_pung (FUNPOW pung j t)) ==> FUNPOW (zagier o flip) 0 t = FUNPOW pung 0 t
      FUNPOW (zagier o flip) 0 t
    = t                            by FUNPOW_0
    = FUNPOW pung 0 t              by FUNPOW_0

   Step: (!j. j < m ==> is_pung (FUNPOW pung j t)) ==> FUNPOW (zagier o flip) m t = FUNPOW pung m t ==>
         (!j. j < SUC m ==> is_pung (FUNPOW pung j t)) ==> FUNPOW (zagier o flip) (SUC m) t = FUNPOW pung (SUC m) t
      Note !j. j < SUC m ==> is_pung (FUNPOW pung j t)
       <=> !j. (j < m \/ j = m) ==> is_pung (FUNPOW pung j t)        by arithmetic
       <=> is_pung (FUNPOW pung m t) /\
           !j. j < m ==> is_pung (FUNPOW pung j t)                   by DISJ_IMP_THM

           is_pung (FUNPOW pung (SUC m) t)
       <=> is_pung (pung (FUNPOW pung m t))                          by FUNPOW_SUC
       <=> is_pung ((zagier o flip) (FUNPOW pung m t))               by zagier_flip_pung, [1]

        FUNPOW (zagier o flip) (SUC m) t
      = (zagier o flip) (FUNPOW (zagier o flip) m t)                 by FUNPOW_SUC
      = (zagier o flip) (FUNPOW pung m t)                            by induction hypothesis
      = pung (FUNPOW pung m t)                                       by zagier_flip_pung, [1]
      = FUNPOW pung (SUC m) t                                        by FUNPOW_SUC
*)
Theorem zagier_flip_pung_funpow:
  !m t. (!j. j < m ==> is_pung (FUNPOW pung j t)) ==> FUNPOW (zagier o flip) m t = FUNPOW pung m t
Proof
  rpt strip_tac >>
  Induct_on `m` >-
  simp[] >>
  strip_tac >>
  `!j. j < SUC m <=> (j < m \/ j = m)` by decide_tac >>
  `is_pung (FUNPOW pung m t) /\ !j. j < m ==> is_pung (FUNPOW pung j t)` by metis_tac[] >>
  fs[FUNPOW_SUC, zagier_flip_pung]
QED

(* Idea: after a pung, there is no ping. *)

(* Theorem: 2 * z <= x ==> ~is_ping (pung (x,y,z)) *)
(* Proof:
   Note pung (x,y,z)
      = (x - 2 * z,x + y - z,z)                by pung_def
   If this is is_ping,
      x - 2 * z < z - (x + y - z)              by is_ping_def
                = (2 * z - x) - y              by arithmetic
                = 0                            by 2 * z <= x
   This is impossible, a contradiction.
*)
Theorem pung_next_non_ping:
  !x y z. 2 * z <= x ==> ~is_ping (pung (x,y,z))
Proof
  simp[pung_def, is_ping_def]
QED

(* Theorem: is_pung t ==> ~is_ping (pung t) *)
(* Proof: by pung_next_non_ping, is_pung_def gives ~(x < 2 * z) *)
Theorem pung_next_not_ping:
  !t. is_pung t ==> ~is_ping (pung t)
Proof
  metis_tac[pung_next_non_ping, is_pung_def, triple_parts, NOT_LESS]
QED

(* Theorem: is_ping ((zagier o flip) t) ==> ~is_pung t *)
(* Proof:
   By contradiction, suppose is_pung t.
   Then (zagier o flip) t = pung t             by zagier_flip_pung
    but is_ping (pung t) = F                   by pung_next_not_ping
*)
Theorem ping_before_not_pung:
  !t. is_ping ((zagier o flip) t) ==> ~is_pung t
Proof
  spose_not_then strip_assume_tac >>
  fs[zagier_flip_pung, pung_next_not_ping]
QED

(* This means: after a pung, either a pong or a pung, no ping.  *)
(* This means: before a ping, either a ping or a pong, no pung. *)

(* Idea: ping (x,y,z) will generally increase the mind, by first of 5 cases. *)

(* Theorem: mind (ping (x,y,z)) = x + 2 * y *)
(* Proof:
   Let t = (x,y,z).
   Then ping t = (x + 2 * y,y,z - y - x)       by ping_def

   For mind (ping t),
   If x + 2 * y < y - (z - y - x)
   or x + 2 * y < x + 2 * y - z, impossible.
   Otherwise, if x + 2 * y < y, also impossible.
   Otherwise,
        mind (ping t)
      = x + 2 * y                              by mind_def
*)
Theorem mind_of_ping:
  !x y z. mind (ping (x,y,z)) = x + 2 * y
Proof
  simp[ping_def, mind_def]
QED

(* Theorem: mind t <= mind (ping t) *)
(* Proof:
   Let (x,y,z) = t                             by triple_parts
   Then ping t = (x + 2 * y,y,z - y - x)       by ping_def

   Case 1: x < y - z
   Note mind t = x + 2 * z                     by mind_def
        mind (ping t)
      = x + 2 * y                              by mind_of_ping
      > x + 2 * (x + z)                        by x + z < y
      >= x + 2 * z = mind t

   Case 2: ~(x < y - z) /\ x < y
   Note mind t = 2 * y - x                     by mind_def
        mind (ping t)
      = x + 2 * y                              by mind_of_ping
      >= 2 * y
      >= 2 * y - x = mind t

   Case 3: otherwise, ~(x < y - z) /\ ~(x < y)
   Note mind t = x                             by mind_def
        mind (ping t)
      = x + 2 * y                              by mind_of_ping
      >= x = mind t                            by inequality

   Overall, mind t <= mind (ping t).
*)
Theorem mind_rise_by_ping:
  !t. mind t <= mind (ping t)
Proof
  simp[mind_of_ping, mind_def, FORALL_PROD]
QED

(* Theorem: 0 < x /\ 0 < y ==> mind (x,y,z) < mind (ping (x,y,z)) *)
(* Proof:
   Let t = (x,y,z).
   Case 1: x < y - z
   Note mind t = x + 2 * z                     by mind_def
        mind (ping t)
      = x + 2 * y                              by mind_of_ping
      > x + 2 * (x + z)                        by x + z < y
      > x + 2 * z = mind t                     by 0 < x
   Case 2: ~(x < y - z) /\ x < y
   Note mind t = 2 * y - x                     by mind_def
        mind (ping t)
      = x + 2 * y                              by mind_of_ping
      > 2 * y                                  by 0 < x
      > 2 * y - x = mind t                     by 0 < x
   Case 3: otherwise
   Note mind t = x                             by mind_def
        mind (ping t)
      = x + 2 * y                              by mind_of_ping
      > x = mind t                             by 0 < y
*)
Theorem mind_inc_by_ping:
  !x y z. 0 < x /\ 0 < y ==> mind (x,y,z) < mind (ping (x,y,z))
Proof
  simp[mind_def, mind_of_ping]
QED

(* Idea: pung (x,y,z) will generally decrease the mind, by last of 5 cases. *)

(* Theorem: 2 * z <= x ==> mind (pung (x,y,z)) = x*)
(* Proof:
   Let t = (x,y,z).
   Then pung t = (x - 2 * z,x + y - z,z)       by pung_def
   For mind definition,
   If x - 2 * z < (x + y - z) - z
   or x - 2 * z < y + (x - 2 * z)              by 2 * z <= x
   If 0 < y, this is true,
   Thus mind (pung t)
      = (x - 2 * z) + 2 * z                    by mind_def
      = x
   When y = 0, this is false, so check:
   If x - 2 * z < x + 0 - z = z + (x - 2 * z)
   If 0 < z, this is true,
   Thus mind (pung t)
      = 2 * (x + 0 - z) - (x - 2 * z)          by mind_def
      = x                                      by 2 * z <= x
   When z = 0, this is false,
   Thus mind (pung t)
      = x - 2 * 0                              by mind_def
      = x
*)
Theorem mind_of_pung:
  !x y z. 2 * z <= x ==> mind (pung (x,y,z)) = x
Proof
  rw[pung_def] >>
  `0 < y \/ y = 0` by decide_tac >-
  simp[mind_def] >>
  `0 < z \/ z = 0` by decide_tac >-
  simp[mind_def] >>
  simp[mind_def]
QED

(* Theorem: 2 * z <= x ==> mind (pung (x,y,z)) <= mind (x,y,z) *)
(* Proof:
   Let t = (x,y,z).

   Case 1: x < y - z
   Note mind t = x + 2 * z                     by mind_def
        mind (pung t)
      = x                                      by mind_of_pung
      <= x + 2 * z = mind t

   Case 2: ~(x < y - z) /\ x < y
   That is, 2 * x < 2 * y
        ==> x < 2 * y - x                      by inequality [1]
   Note mind t = 2 * y - x                     by mind_def
        mind (pung t)
      = x                                      by mind_of_pung
      < 2 * y - x = mind t                     by [1]

   Case 3: otherwise, ~(x < y - z) /\ ~(x < y)
   Note mind t = x                             by mind_def
        mind (pung t)
      = x = mind t                             by mind_of_pung

   Overall, mind (pung t) <= mind t.
*)
Theorem mind_fall_for_pung:
  !x y z. 2 * z <= x ==> mind (pung (x,y,z)) <= mind (x,y,z)
Proof
  simp[mind_def, mind_of_pung]
QED

(* Theorem: is_pung t ==> mind (pung t) <= mind t *)
(* Proof: by mind_fall_for_pung, is_pung_def. *)
Theorem mind_fall_by_pung:
  !t. is_pung t ==> mind (pung t) <= mind t
Proof
  metis_tac[mind_fall_for_pung, is_pung_def, triple_parts, NOT_LESS]
QED

(* ------------------------------------------------------------------------- *)
(* Path on principal orbit of (zagier o flip) iteration.                     *)
(* ------------------------------------------------------------------------- *)

(* Define the path from flip of zagier-fix to flip-fix. *)
Definition path_def:
   path n 0 = [(1,n DIV 4,1)] /\ (* flip of (1,1,n DIV 4) *)
   path n (SUC k) = SNOC ((zagier o flip) (LAST (path n k))) (path n k)
End

(* Extract theorems *)
Theorem path_0 = path_def |> CONJUNCT1;
(* val path_0 = |- !n. path n 0 = [(1,n DIV 4,1)]: thm *)
Theorem path_suc = path_def |> CONJUNCT2;
(* val path_suc = |- !n k. path n (SUC k) = SNOC ((zagier o flip) (LAST (path n k))) (path n k): thm *)

(*
> EVAL ``path 61 6``;
val it = |- path 61 6 = [(1,15,1); (1,1,15); (3,1,13); (5,1,9); (7,1,3); (1,5,3); (5,3,3)]: thm
> EVAL ``path 89 11``;
val it = |- path 89 11 = [(1,22,1); (1,1,22); (3,1,20); (5,1,16); (7,1,10); (9,1,2); (5,8,2);
                          (1,11,2); (3,2,10); (7,2,5); (3,5,4); (5,4,4)]: thm
*)


(* Theorem: path n 1 = [(1,n DIV 4,1); (1,1,n DIV 4)] *)
(* Proof:
   Let f = zagier o flip,
       t = (1,n DIV 4,1).
   Note path n 0 = [t]             by path_0
     path n 1
   = path n (SUC 0)                by ONE
   = SNOC (f (LAST [t]) [t]        by path_suc
   = SNOC (f t) [t]                by LAST_SING
   = [t; f t]                      by SNOC
   = [t; (1,1,n DIV 4)]            by zagier_flip_x_y_x
*)
Theorem path_1:
  !n. path n 1 = [(1,n DIV 4,1); (1,1,n DIV 4)]
Proof
  rpt strip_tac >>
  qabbrev_tac `f = zagier o flip` >>
  qabbrev_tac `t = (1,n DIV 4,1)` >>
  `path n (SUC 0) = [t; f t]` suffices_by metis_tac[zagier_flip_x_y_x, ONE, DECIDE``0 < 1``] >>
  simp[path_suc, path_0, Abbr`f`, Abbr`t`]
QED

(* Theorem: path n k <> [] *)
(* Proof:
   If k = 0,   path n 0
             = [(1,n DIV 4,1)]     by path_0
             <> []                 by NOT_NIL_CONS
   If k = SUC j, for some j.
               path n (SUC j)
             = SNOC h ls           by path_suc, where
                                   ls = path n j
                                   h = (zagier o flip) (LAST ls)
             <> []                 by NOT_SNOC_NIL
*)
Theorem path_not_nil:
  !n k. path n k <> []
Proof
  metis_tac[num_CASES, path_def, NOT_NIL_CONS, NOT_SNOC_NIL]
QED

(* Theorem: LENGTH (path n k) = k + 1 *)
(* Proof:
   Let f = zagier o flip.
   By induction on k.
   Base: LENGTH (path n 0) = 0 + 1
         LENGTH (path n 0)
       = LENGTH [(1,n DIV 4,1)]                by path_0
       = 1 = 0 + 1                             by LENGTH_SING
   Step: LENGTH (path n k) = k + 1 ==> LENGTH (path n (SUC k)) = SUC k + 1
         LENGTH (path n (SUC k))
       = LENGTH (SNOC (f (LAST ls)) ls)        by path_suc, where ls = path n k
       = SUC (LENGTH ls)                       by LENGTH_SNOC
       = SUC (n + 1)                           by induction hypothesis
       = SUC n + 1                             by arithmetic
*)
Theorem path_length:
  !n k. LENGTH (path n k) = k + 1
Proof
  strip_tac >>
  qabbrev_tac `f = zagier o flip` >>
  Induct >-
  simp[path_0] >>
  simp[path_suc, LENGTH_SNOC]
QED

(* Theorem: HD (path n k) = (1,n DIV 4,1) *)
(* Proof:
   Let f = zagier o flip,
       t = (1,n DIV 4,1).
   By induction on k.
   Base: HD (path n 0) = t
         HD (path n k)
       = HD [t]                                by path_0
       = t                                     by HD
   Step: HD (path n k) = t ==> HD (path n (SUC k)) = t
       Let ls = path n k.
       Note ls <> []                           by path_not_nil
         so ls = HD ls::TL ls                  by LIST_NOT_NIL
         HD (path n (SUC k))
       = HD (SNOC (f (LAST ls)) ls)            by path_suc
       = HD (HD ls::SNOC (f (LAST ls) (TL ls)) by SNOC
       = HD ls                                 by HD
       = t                                     by induction hypothesis
*)
Theorem path_head:
  !n k. HD (path n k) = (1,n DIV 4,1)
Proof
  strip_tac >>
  qabbrev_tac `f = zagier o flip` >>
  qabbrev_tac `t = (1,n DIV 4,1)` >>
  Induct >-
  simp[path_0, Abbr`t`] >>
  qabbrev_tac `ls = path n k` >>
  `ls <> []` by simp[path_not_nil, Abbr`ls`] >>
  `ls = HD ls :: TL ls` by simp[GSYM LIST_NOT_NIL] >>
  metis_tac[path_suc, SNOC, HD]
QED

(* Theorem: LAST (path n k) = FUNPOW (zagier o flip) k (1,n DIV 4,1) *)
(* Proof:
   Let f = zagier o flip,
       t = (1,n DIV 4,1).
   By induction on j.
   Base: LAST (path n 0) = FUNPOW f 0 t
         LAST (path n 0)
       = LAST [t]                              by path_0
       = t                                     by LAST_CONS
   Step: LAST (path n k) = FUNPOW f n t ==> LAST (path n (SUC k)) = FUNPOW f (SUC n) t
       Let ls = path n k.
         LAST (path n (SUC k))
       = LAST (SNOC (f (LAST ls)) ls)          by path_suc
       = f (LAST ls)                           by LAST_SNOC
       = f (FUNPOW f n t)                      by induction hypothesis
       = FUNPOW f (SUC n) t                    by FUNPOW_SUC
*)
Theorem path_last:
  !n k. LAST (path n k) = FUNPOW (zagier o flip) k (1,n DIV 4,1)
Proof
  strip_tac >>
  qabbrev_tac `f = zagier o flip` >>
  qabbrev_tac `t = (1,n DIV 4,1)` >>
  Induct >-
  simp[path_0, LAST_CONS, Abbr`t`] >>
  metis_tac[path_suc, LAST_SNOC, FUNPOW_SUC]
QED

(* Theorem: HD (path n k) = EL 0 (path n k) *)
(* Proof: by EL. *)
Theorem path_head_alt:
  !n k. HD (path n k) = EL 0 (path n k)
Proof
  simp[]
QED

(* Theorem: LAST (path n k) = EL k (path n k) *)
(* Proof:
   Note LENGTH (path n k) = k + 1              by path_length
     so path n k <> []                         by LENGTH_EQ_0
        LAST (path n k)
      = EL (PRE (k + 1)) (path n k)            by LAST_EL
      = EL k (path n k)                        by arithmetic
*)
Theorem path_last_alt:
  !n k. LAST (path n k) = EL k (path n k)
Proof
  rpt strip_tac >>
  `LENGTH (path n k) = k + 1 ` by simp[path_length] >>
  `k + 1 <> 0 /\ PRE (k + 1) = k` by decide_tac >>
  metis_tac[LAST_EL, LENGTH_EQ_0]
QED

(* Idea: the tail of (path n (1 + m)) is an iterate trace up to m. *)

(* Theorem: TL (path n (1 + m)) = iterate_trace (1,1,n DIV 4) (zagier o flip) m *)
(* Proof:
   Let f = zagier o flip,
       u = (1,1,n DIV 4),
       v = (1,n DIV 4,1).
   The goal is to show: TL (path n (1 + m)) = iterate_trace u f m

   By induction on m.
   Base: TL (path n (1 + 0)) = iterate_trace u f 0
         TL (path n (1 + 0))
       = TL (path n 1)
       = TL [(1,n DIV 4,1); u]                 by path_1
       = [u]                                   by TL
       = iterate_trace u f 0                   by iterate_trace_0

   Step: TL (path n (1 + m)) = iterate_trace u f m ==>
         TL (path n (1 + SUC m)) = iterate_trace u f (SUC m)
         TL (path n (1 + SUC m))
       = TL (path n (SUC (1 + m)))             by ADD
       = TL (SNOC (f (LAST (path n (1 + m)))) (path n (1 + m)))     by path_suc
       = SNOC (f (LAST (path n (1 + m)))) (TL (path n (1 + m)))     by TL_SNOC, path n (1 + m) <> []
       = SNOC (f (LAST (path n (1 + m)))) (iterate_trace u f m)     by induction hypothesis
       = SNOC (f (FUNPOW f (1 + m) v)) (iterate_trace u f m)        by path_last
       = SNOC (FUNPOW f (1 + m) (f v)) (iterate_trace u f m)        by FUNPOW_SUC, FUNPOW
       = SNOC (FUNPOW f (SUC m) u) (iterate_trace u f m)            by zagier_flip_x_y_x
       = iterate_trace u f (SUC m)                                  by iterate_trace_suc
*)
Theorem path_tail_alt:
  !n m. TL (path n (1 + m)) = iterate_trace (1,1,n DIV 4) (zagier o flip) m
Proof
  rpt strip_tac >>
  qabbrev_tac `f = zagier o flip` >>
  qabbrev_tac `u = (1,1,n DIV 4)` >>
  Induct_on `m` >-
  simp[path_1, iterate_trace_0] >>
  qabbrev_tac `v = (1,n DIV 4,1)` >>
  `f (LAST (path n (1 + m))) = f (FUNPOW f (1 + m) v)` by metis_tac[path_last] >>
  `_ = FUNPOW f (1 + m) (f v)` by simp[GSYM FUNPOW_SUC, FUNPOW] >>
  `_ = FUNPOW f (1 + m) u` by simp[zagier_flip_x_y_x, Abbr`u`, Abbr`v`, Abbr`f`] >>
  `TL (path n (1 + SUC m)) = TL (SNOC (f (LAST (path n (1 + m)))) (path n (1 + m)))` by fs[path_suc, GSYM ADD1, Abbr`f`] >>
  `_ = SNOC (FUNPOW f (1 + m) u) (TL (path n (1 + m)))` by metis_tac[TL_SNOC, NULL_EQ, path_not_nil] >>
  `_ = SNOC (FUNPOW f (1 + m) u) (iterate_trace u f m)` by fs[] >>
  simp[iterate_trace_suc, ADD1]
QED

(* Idea: the tail of (path n k) has elements all distinct. *)

(* Theorem: tik n /\ ~square n /\ k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) ==>
            ALL_DISTINCT (TL (path n k)) *)
(* Proof:
   Let s = mills n,
       f = zagier o flip,
       u = (1,1,n DIV 4),
       p = iterate_period f u.
   Note FINITE s                               by mills_finite_non_square, ~square n
    and zagier involute s                      by zagier_involute_mills, tik n
    and flip involute s                        by flip_involute_mills
     so f PERMUTES s                           by involute_involute_permutes
   Also u IN s                                 by mills_element_trivial, tik n
   Thus 0 < p                                  by iterate_period_pos
    and HALF p < p                             by HALF_LT, 0 < p

     TL (path n k)
   = TL (path n (1 + HALF p))                  by notation
   = iterate_trace u f (HALF p)                by path_tail_alt

   Thus ALL_DISTINCT (TL (path n k))           by iterate_trace_all_distinct
*)
Theorem path_tail_all_distinct:
  !n k. tik n /\ ~square n /\ k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) ==>
        ALL_DISTINCT (TL (path n k))
Proof
  rpt strip_tac >>
  qabbrev_tac `s = mills n` >>
  qabbrev_tac `f = zagier o flip` >>
  qabbrev_tac `u = (1,1,n DIV 4)` >>
  qabbrev_tac `p = iterate_period f u` >>
  `FINITE s` by simp[mills_finite_non_square, Abbr`s`] >>
  `zagier involute s` by metis_tac[zagier_involute_mills, ONE_NOT_0] >>
  `flip involute s` by metis_tac[flip_involute_mills] >>
  `f PERMUTES s` by fs[involute_involute_permutes, Abbr`f`] >>
  `u IN s` by simp[mills_element_trivial, Abbr`s`, Abbr`u`] >>
  `0 < p` by metis_tac[iterate_period_pos] >>
  `HALF p < p` by simp[HALF_LT] >>
  metis_tac[path_tail_alt, iterate_trace_all_distinct]
QED

(* Theorem: path n k = [(1,n DIV 4,1)] <=> k = 0 *)
(* Proof:
   Note path n k <> []             by path_not_nil
     so ?h t. path n k = h::t      by list_CASES
    and h = (1,n DIV 4,1)          by path_head
    and k + 1 = LENGTH (path n k)  by path_length
              = SUC (LENGTH t)     by LENGTH
    ==> LENGTH t = k               by arithmetic
        path n k = [(1,n DIV 4,1)]
    <=> t = []                     by above
    <=> LENGTH t = 0               by LENGTH_EQ_0
    <=> k = 0                      by above
*)
Theorem path_eq_sing:
  !n k. path n k = [(1,n DIV 4,1)] <=> k = 0
Proof
  rpt strip_tac >>
  qabbrev_tac `ls = path n k` >>
  `?h t. ls = h::t`  by metis_tac[path_not_nil, list_CASES] >>
  `h = (1,n DIV 4,1)` by metis_tac[path_head, HD] >>
  `k + 1 = LENGTH ls` by fs[path_length, Abbr`ls`] >>
  `_ = SUC (LENGTH t)` by simp[] >>
  `LENGTH t = k` by decide_tac >>
  `h::t = [h] <=> t = []` by simp[] >>
  metis_tac[LENGTH_EQ_0]
QED

(* Theorem: LENGTH (FRONT (path n k)) = k *)
(* Proof:
   Let ls = path n k.
   Then ls <> []               by path_not_nil
     so LENGTH (FRONT ls)
      = PRE (LENGTH ls)        by LENGTH_FRONT
      = PRE (k + 1)            by path_length
      = k                      by PRE, ADD1
*)
Theorem path_front_length:
  !n k. LENGTH (FRONT (path n k)) = k
Proof
  simp[path_not_nil, path_length, LENGTH_FRONT]
QED

(* Theorem: 0 < k ==> HD (FRONT (path n k)) = (1,n DIV 4,1) *)
(* Proof:
   Let ls = path n k.
   Note ls <> []                   by path_not_nil
    and LENGTH ls = k + 1          by path_length
     so LENGTH (FRONT ls) = k      by LENGTH_FRONT

      HD (FRONT ls)
    = EL 0 (FRONT ls)              by EL
    = EL 0 ls                      by FRONT_EL, 0 < k
    = HD ls                        by EL
    = (1,1,n DIV 4)                by path_head
*)
Theorem path_front_head:
  !n k. 0 < k ==> HD (FRONT (path n k)) = (1,n DIV 4,1)
Proof
  rpt strip_tac >>
  qabbrev_tac `ls = path n k` >>
  `ls <> []` by simp[path_not_nil, Abbr`ls`] >>
  `LENGTH (FRONT ls) = k` by fs[LENGTH_FRONT, path_length, Abbr`ls`] >>
  metis_tac[FRONT_EL, EL, path_head]
QED

(* Theorem: j <= k ==> EL j (path n k) = FUNPOW (zagier o flip) j (1,1,n DIV 4) *)
(* Proof:
   Let f = zagier o flip,
       t = (1,n DIV 4,1).
   By induction on k.
   Base: !j. j <= 0 ==> EL j (path n 0) = FUNPOW f j t
       That is, j = 0.
         EL 0 (path n 0)
       = HD (path n 0)                         by EL
       = HD [t]                                by path_0
       = t                                     by HD
       = FUNPOW f 0 t                          by FUNPOW_0
   Step: !j. j <= k ==> EL j (path n k) = FUNPOW f j t ==>
         !j. j <= SUC k ==> EL j (path n (SUC k)) = FUNPOW f j t
       If j <= k, then j < k + 1.
          Let ls = path n k.
          Then LENGTH ls = k + 1               by path_length
            EL j (path n (SUC k))
          = EL j (SNOC (f (LAST ls)) ls)       by path_suc
          = EL j ls                            by EL_SNOC, j < LENGTH ls
          = FUNPOW f j t                       by induction hypothesis
       Otherwise, j = SUC k.
          Let ls = path n (SUC k).
          Note LENGTH ls = (SUC k) + 1         by path_length
            so PRE (LENGTH ls) = SUC k         by arithmetic
           and ls <> []                        by path_not_nil
            EL (SUC k) (path n (SUC k))
          = LAST (path n (SUC k))              by LAST_EL
          = FUNPOW f (SUC k) t                 by path_last
*)
Theorem path_element_eqn:
  !n k j. j <= k ==> EL j (path n k) = FUNPOW (zagier o flip) j (1,n DIV 4,1)
Proof
  strip_tac >>
  qabbrev_tac `f = zagier o flip` >>
  qabbrev_tac `t = (1,n DIV 4,1)` >>
  Induct >-
  simp[path_0, Abbr`t`] >>
  rpt strip_tac >>
  Cases_on `j <= k` >| [
    `j < k + 1` by decide_tac >>
    `LENGTH (path n k) = k + 1` by simp[path_length] >>
    simp[path_suc, EL_SNOC],
    `j = SUC k /\ PRE (j + 1) = j` by decide_tac >>
    `LENGTH (path n j) = j + 1` by simp[path_length] >>
    `path n j <> []` by simp[path_not_nil] >>
    metis_tac[LAST_EL, path_last]
  ]
QED
(* This is a major result. *)

(* Theorem: j < k ==> EL (SUC j) (path n k) = (zagier o flip) (EL j (path n k)) *)
(* Proof:
   Let f = zagier o flip,
       t = (1,n DIV 4,t).
   Note SUC j <= k.
     EL (SUC j) (path n k)
   = FUNPOW f (SUC j) t            by path_element_eqn
   = f (FUNPOW f j t)              by FUNPOW_SUC
   = f (EL j (path n k))           by path_element_eqn
*)
Theorem path_element_suc:
  !n k j. j < k ==> EL (SUC j) (path n k) = (zagier o flip) (EL j (path n k))
Proof
  simp[path_element_eqn, FUNPOW_SUC]
QED
(* Note: this is the key relationship between path elements. *)

(* Theorem: j + h <= k ==> EL (j + h) (path n k) = FUNPOW (zagier o flip) h (EL j (path n k)) *)
(* Proof:
   Let ls = path n k,
       t = (1,n DIV 4,1),
       f = zagier o flip.
     EL (j + h) ls
   = FUNPOW f (j + h) t            by path_element_eqn
   = FUNPOW f (h + j) t            by ADD_COMM
   = FUNPOW f h (FUNPOW f j t)     by FUNPOW_ADD
   = FUNPOW f h (EL j ls)          by path_element_eqn
*)
Theorem path_element_thm:
  !n k j h. j + h <= k ==> EL (j + h) (path n k) = FUNPOW (zagier o flip) h (EL j (path n k))
Proof
  rw[path_element_eqn] >>
  simp[FUNPOW_ADD]
QED

(* Theorem: tik n /\ j < k ==> EL j (path n k) IN mills n *)
(* Proof:
   Let ls = path n k.
   By induction on j.
   Base: 0 <= k ==> EL 0 ls IN mills n
         EL 0 ls
       = HD ls                     by EL
       = (1,n DIV 4,1)             by path_head
     and (1,n DIV 4,1) IN mills n  by mills_element_trivial_flip, tik n

   Step: j <= k ==> EL j ls IN mills n ==>
         SUC j <= k ==> EL (SUC j) ls IN mills n
       Note SUC j <= k ==> j < k, making j <= k.
         EL (SUC j) ls
       = (zagier o flip) (EL j ls)             by path_element_suc, j < k
       = flip (zagier (EL j ls))               by composition
     Note (EL j ls) IN mills n                 by inductive hypothesis, j <= k
      ==> zagier (EL j ls) IN mills n          by zagier_closure
      ==> flip (zagier (EL j ls)) IN mills n   by flip_closure
*)
Theorem path_element_in_mills:
  !n k j. tik n /\ j <= k ==> EL j (path n k) IN mills n
Proof
  rpt strip_tac >>
  qabbrev_tac `ls = path n k` >>
  Induct_on `j` >-
  simp[path_head, mills_element_trivial_flip, Abbr`ls`] >>
  rpt strip_tac >>
  `EL (SUC j) ls = (zagier o flip) (EL j ls)` by simp[path_element_suc, Abbr`ls`] >>
  simp[zagier_closure, flip_closure]
QED

(* Theorem: tik n /\ j <= k ==> n = windmill (EL j (path n k)) *)
(* Proof:
   Let ls = path n k,
        t = EL j ls.
   Note t IN (mills n)             by path_element_in_mills, j <= k
     so n = windmill t             by mills_element_alt
*)
Theorem path_element_windmill:
  !n k j. tik n /\ j <= k ==> n = windmill (EL j (path n k))
Proof
  metis_tac[path_element_in_mills, mills_element_alt]
QED

(* Theorem: is_pong (EL 0 (path n k)) *)
(* Proof:
       is_pong (EL 0 (path n k))
   <=> is_pong (HD (path n k))     by EL
   <=> is_pong (1,n DIV 4,1)       by path_head
   <=> T                           by is_pong_def, 1 < 2 * 1
*)
Theorem path_head_is_pong:
  !n k. is_pong (EL 0 (path n k))
Proof
  simp[path_head, is_pong_def]
QED

(* Theorem: EL 0 (path n k) = (1,n DIV 4,1) *)
(* Proof:
     EL 0 (path n k)
   = HD (path n k)             by path_head_alt
   = (1,1,n DIV 4)             by path_head
*)
Theorem path_element_0:
  !n k. EL 0 (path n k) = (1,n DIV 4,1)
Proof
  simp[GSYM path_head_alt, path_head]
QED

(* Theorem: 0 < k ==> EL 1 (path n k) = (1,1,n DIV 4) *)
(* Proof:
   Let t = EL 0 (path n k)
   Then t = (1,n DIV 4,1)      by path_element_0
   Note is_pong t              by path_head_is_pong
     EL 1 (path n k)
   = EL (SUC 0) (path n k)     by ONE
   = (zagier o flip) t         by path_element_suc, 0 < k
   = pong t                    by zagier_flip_pong
   = (1,1,n DIV 4)             by pong_def
*)
Theorem path_element_1:
  !n k. 0 < k ==> EL 1 (path n k) = (1,1,n DIV 4)
Proof
  rpt strip_tac >>
  qabbrev_tac `t = EL 0 (path n k)` >>
  `is_pong t` by simp[path_head_is_pong, Abbr`t`] >>
  `EL 1 (path n k) = EL (SUC 0) (path n k)` by simp[GSYM ONE] >>
  `_ = (zagier o flip) t` by simp[path_element_suc, Abbr`t`] >>
  `_ = pong t` by simp[zagier_flip_pong] >>
  simp[pong_def, path_element_0, Abbr`t`]
QED

(* Theorem: j < k ==> EL j (TL (path n k)) = FUNPOW (zagier o flip) j (1,1,n DIV 4) *)
(* Proof:
   Let zagier o flip = f.
   Note 0 < k /\ 1 + j <= k        by j < k
     EL j (TL (path n k))
   = EL (SUC j) (path n k)         by EL
   = EL (1 + j) (path n k)         by ADD1
   = FUNPOW f j (EL 1 (path n k))  by path_element_thm, 1 + j <= k
   = FUNPOW f j (1,1,n DIV 4)      by path_element_1, 0 < k
*)
Theorem path_tail_element:
  !n k j. j < k ==> EL j (TL (path n k)) = FUNPOW (zagier o flip) j (1,1,n DIV 4)
Proof
  rpt strip_tac >>
  qabbrev_tac `f = zagier o flip` >>
  `EL j (TL (path n k)) = EL (SUC j) (path n k)` by simp[EL] >>
  `_ = EL (1 + j) (path n k)` by simp[ADD1] >>
  `_ = FUNPOW f j (EL 1 (path n k))` by fs[path_element_thm, Abbr`f`] >>
  simp[path_element_1]
QED

(* Theorem: 0 < k ==> let t = EL 1 (path n k) in
            if n < 4 then is_pung t else if n < 12 then is_pong t else is_ping t *)
(* Proof:
   Let t = EL 1 (path n k).
   Then t = (1,1,n DIV 4)          by path_element_1
   Note 3 <= n DIV 4 <=> 3 * 4 <= n   by X_LE_DIV
      or 2 < n DIV 4 <=> 12 <= n
   Also 1 <= n DIV 4 <=> 1 * 4 <= n   by X_LE_DIV
      or 0 < n DIV 4 <=> 4 <= n

   Thus, if n < 4,
       Then n DIV 4 = 0,
       ==> is_pung t               by is_pung_def
   If 4 <= n but n < 8,
       Then n DIV 4 = 1,
       ==> is_pong t               by is_pong_def
   Otherwise, 8 <= n,
       Then 2 < n DIV 4,
       ==> is_ping t               by is_ping_def
*)
Theorem path_head_next_property:
  !n k. 0 < k ==> let t = EL 1 (path n k) in
        if n < 4 then is_pung t else if n < 12 then is_pong t else is_ping t
Proof
  rw_tac std_ss[] >>
  `t = (1,1,n DIV 4)` by simp[path_element_1, Abbr`t`] >>
  `3 <= n DIV 4 <=> 12 <= n` by simp[X_LE_DIV] >>
  `1 <= n DIV 4 <=> 4 <= n` by simp[X_LE_DIV] >>
  (Cases_on `n < 4` >> simp[]) >-
  simp[is_pung_def] >>
  (Cases_on `n < 12` >> simp[]) >-
  simp[is_pong_def] >>
  fs[is_ping_def]
QED

(* Theorem: let ls = path n k in flip (LAST ls) = LAST ls ==> ~is_ping (LAST ls) *)
(* Proof:
   Let t = LAST ls.
   Then t = (x,y,z)                by triple_parts
    and flip t = t ==> y = z       by flip_fix
     so ~is_ping t                 by not_ping_x_y_y
*)
Theorem path_last_not_ping:
  !n k. let ls = path n k in flip (LAST ls) = LAST ls ==> ~is_ping (LAST ls)
Proof
  rw_tac std_ss[] >>
  metis_tac[triple_parts, flip_fix, not_ping_x_y_y]
QED

(* This is the short version. See the long version below. *)

(*
involute_involute_fix_orbit_fix_odd_inv |> ISPEC ``zagier`` |> ISPEC ``flip`` |> ISPEC ``mills n`` |> SPEC ``p:num`` |> ISPEC ``(1,1,n DIV 4)``;
val it = |- FINITE (mills n) /\ zagier involute mills n /\ flip involute mills n /\
      (1,1,n DIV 4) IN fixes zagier (mills n) /\
      p = iterate_period (zagier o flip) (1,1,n DIV 4) /\ ODD p ==>
      FUNPOW (zagier o flip) (1 + HALF p) (1,1,n DIV 4) IN
      fixes flip (mills n): thm

path_last  |- !n k. LAST (path n k) = FUNPOW (zagier o flip) k (1,1,n DIV 4)
path_last |> SPEC ``n:num`` |> SPEC ``1 + HALF p``;
val it = |- LAST (path n (1 + HALF p)) = FUNPOW (zagier o flip) (1 + HALF p) (1,1,n DIV 4): thm
*)

(* Idea: the last element of path is not a ping. *)

(* Theorem: prime n /\ tik n /\ p = iterate_period (zagier o flip) (1,1,n DIV 4) ==>
            ~is_ping (LAST (path n (1 + HALF p))) *)
(* Proof:
   Let u = (1,1,n DIV 4),
       k = 1 + HALF p,
       v = FUNPOW (zagier o flip) k u.
   Note prime n ==> ~square n                  by prime_non_square
     so FINITE (mills n)                       by mills_finite_non_square
    and zagier involute (mills n)              by zagier_involute_mills_prime, prime n
    and flip involute (mills n)                by flip_involute_mills
    and fixes zagier (mills n) = {u}           by zagier_fixes_prime
     so u IN fixes zagier (mills n)            by IN_SING

    Now u IN s                                 by mills_element_trivial, tik n
     so ODD p                                  by involute_involute_fix_sing_period_odd
    ==> v IN fixes flip (mills n)              by involute_involute_fix_orbit_fix_odd

    Claim: v = LAST (path n (1 + k))
    Proof: Let ls = path n (1 + k).
           Then ls <> []                       by path_not_nil
            and LENGTH ls = k + 2              by path_length
                LAST ls
              = EL (PRE (LENGTH ls)) ls        by LAST_EL
              = EL (1 + k) ls                  by above
              = FUNPOW (f o g) k (EL 1 ls)     by path_element_thm
              = FUNPOW (f o g) k u             by path_element_1
              = v

    Thus v = LAST (path n k)                   by path_last
     and ~is_ping v                            by flip_fixes_element, not_ping_x_y_y
*)
Theorem path_last_not_ping_thm:
  !n p. prime n /\ tik n /\ p = iterate_period (zagier o flip) (1,1,n DIV 4) ==>
        ~is_ping (LAST (path n (1 + HALF p)))
Proof
  rpt strip_tac >>
  qabbrev_tac `u = (1,1,n DIV 4)` >>
  qabbrev_tac `k = HALF p` >>
  qabbrev_tac `v = FUNPOW (zagier o flip) k u` >>
  qabbrev_tac `s = mills n` >>
  `~square n` by simp[prime_non_square] >>
  `FINITE s` by fs[mills_finite_non_square, Abbr`s`] >>
  `zagier involute s` by metis_tac[zagier_involute_mills_prime] >>
  `flip involute s` by metis_tac[flip_involute_mills] >>
  `fixes zagier s = {u}` by fs[zagier_fixes_prime, Abbr`s`, Abbr`u`] >>
  `u IN fixes zagier s` by simp[] >>
  `u IN s` by metis_tac[mills_element_trivial] >>
  qabbrev_tac `f = zagier` >>
  qabbrev_tac `g = flip` >>
  drule_then strip_assume_tac involute_involute_fix_sing_period_odd >>
  first_x_assum (qspecl_then [`f`, `g`, `p`, `u`] strip_assume_tac) >>
  `ODD p` by metis_tac[] >>
  drule_then strip_assume_tac involute_involute_fix_orbit_fix_odd >>
  first_x_assum (qspecl_then [`f`, `g`, `p`, `u`] strip_assume_tac) >>
  `v IN fixes g s` by metis_tac[] >>
  `v = LAST (path n (1 + k))` by
  (qabbrev_tac `ls = path n (1 + k)` >>
  `ls <> [] /\ LENGTH ls = k + 2` by simp[path_not_nil, path_length, Abbr`ls`] >>
  `PRE (k + 2) = k + 1` by decide_tac >>
  `LAST ls = EL (1 + k) ls` by simp[LAST_EL] >>
  `_ = FUNPOW (f o g) k (EL 1 ls)` by fs[path_element_thm, Abbr`ls`] >>
  simp[path_element_1, Abbr`ls`, Abbr`u`, Abbr`v`]) >>
  metis_tac[triple_parts, flip_fixes_element, not_ping_x_y_y]
QED

(* Theorem: let ls = path n k in m + u <= k /\
            (!j. j < m ==> is_ping (EL (u + j) ls)) ==>
             !j. j <= m ==> EL (u + j) ls = FUNPOW ping j (EL u ls) *)
(* Proof:
   By induction on j.
   Base: 0 <= m ==> EL (u + 0) ls = FUNPOW ping 0 (EL u ls)
          EL u ls
        = FUNPOW ping 0 (EL u ls)              by FUNPOW_0
   Step: j <= m ==> EL (u + j) ls = FUNPOW ping j (EL u ls) ==>
         SUC j <= m ==> EL (u + SUC j) ls = FUNPOW ping (SUC j) (EL u ls)
      Note SUC j <= m ==> j <= m               by inequality
      Thus is_ping (EL (u + j) ls)             by j < m
         EL (u + SUC j) ls
       = EL (SUC (u + j)) ls                   by ADD_CLAUSES
       = (zagier o flip) (EL (u + j) ls)       by path_element_suc, SUC j <= m
       = ping (EL (u + j) ls)                  by zagier_flip_ping
       = ping (FUNPOW ping j (EL u ls))        by induction hypothesis
       = FUNPOW ping (SUC j) (EL u ls)         by FUNPOW_SUC
*)
Theorem path_element_ping_funpow:
  !n k u m. let ls = path n k in m + u <= k /\
            (!j. j < m ==> is_ping (EL (u + j) ls)) ==>
             !j. j <= m ==> EL (u + j) ls = FUNPOW ping j (EL u ls)
Proof
  rw_tac std_ss[] >>
  Induct_on `j` >-
  simp[] >>
  strip_tac >>
  `j < m` by decide_tac >>
  `is_ping (EL (u + j) ls)` by metis_tac[] >>
  `EL (u + SUC j) ls = EL (SUC (u + j)) ls` by metis_tac[ADD_CLAUSES] >>
  `_ = (zagier o flip) (EL (u + j) ls)` by fs[path_element_suc, Abbr`ls`] >>
  `_ = ping (EL (u + j) ls)` by metis_tac[zagier_flip_ping] >>
  fs[FUNPOW_SUC]
QED

(* Theorem: let ls = path n k in m + u <= k /\
            (!j. j < m ==> is_pung (EL (u + j) ls)) ==>
            !j. j <= m ==> EL (u + j) ls = FUNPOW pung j (EL u ls) *)
(* Proof:
   By induction on j.
   Base: 0 <= m ==> EL (u + 0) ls = FUNPOW pung 0 (EL u ls)
          EL u ls
        = FUNPOW pung 0 (EL u ls)              by FUNPOW_0
   Step: j <= m ==> EL (u + j) ls = FUNPOW pung j (EL u ls) ==>
         SUC j <= m ==> EL (u + SUC j) ls = FUNPOW pung (SUC j) (EL u ls)
      Note SUC j < m ==> j < m                 by inequality
      Thus is_pung (EL (u + j) ls)             by j < m
         EL (u + SUC j) ls
       = EL (SUC (u + j)) ls                   by ADD_CLAUSES
       = (zagier o flip) (EL (u + j) ls)       by path_element_suc, SUC j <= m
       = pung (EL (u + j) ls)                  by zagier_flip_pung
       = pung (FUNPOW pung j (EL u ls))        by induction hypothesis
       = FUNPOW pung (SUC j) (EL u ls)         by FUNPOW_SUC
*)
Theorem path_element_pung_funpow:
  !n k u m. let ls = path n k in m + u <= k /\
            (!j. j < m ==> is_pung (EL (u + j) ls)) ==>
             !j. j <= m ==> EL (u + j) ls = FUNPOW pung j (EL u ls)
Proof
  rw_tac std_ss[] >>
  Induct_on `j` >-
  simp[] >>
  strip_tac >>
  `j < m` by decide_tac >>
  `is_pung (EL (u + j) ls)` by metis_tac[] >>
  `EL (u + SUC j) ls = EL (SUC (u + j)) ls` by metis_tac[ADD_CLAUSES] >>
  `_ = (zagier o flip) (EL (u + j) ls)` by fs[path_element_suc, Abbr`ls`] >>
  `_ = pung (EL (u + j) ls)` by metis_tac[zagier_flip_pung] >>
  fs[FUNPOW_SUC]
QED

(* ------------------------------------------------------------------------- *)
(* Sections along Path.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Idea: between a pung and a ping, there must be a pong. *)

(* Theorem: let ls = path n k in j < h /\ h <= k /\
            is_pung (EL j ls) /\ is_ping (EL h ls) ==>
            ?p. j < p /\ p < h /\ is_pong (EL p ls) *)
(* Proof:
   Let ls = path n k.
   By contradiction, assume !p. j < p /\ p < h ==> ~is_pong (EL p ls).
   thus is_ping (EL p ls) \/ is_pung (EL p ls) by triple_cases
   Note j < h /\ is_pung (EL j ls)             by given
    and is_ping (EL h ls) ==>
        ~is_pung (EL h ls)                     by ping_not_pung
    ==> ?m. j <= m /\ m < h /\
           (!p. j <= p /\ p <= m ==> is_pung (EL p ls)) /\
            ~is_pung (EL (SUC m) ls)           by every_range_span_max
   Note ~is_pong (EL (SUC m) ls)               by every_range_less_ends, j < SUC m < h
    ==> is_ping (EL (SUC m) ls)                by triple_cases, [1]

    Now is_pung (EL m ls)                      by j <= m /\ m <= m
    But m < h <= k,
     so EL (SUC m) ls = pung (EL m ls)         by path_element_suc, zagier_flip_pung, m < k
    ==> ~is_ping (pung (EL m ls))              by pung_next_not_ping
    This is a contradiction                    by [1]
*)
Theorem pung_to_ping_has_pong:
  !n k j h. let ls = path n k in j < h /\ h <= k /\
            is_pung (EL j ls) /\ is_ping (EL h ls) ==>
            ?p. j < p /\ p < h /\ is_pong (EL p ls)
Proof
  rw_tac std_ss[] >>
  spose_not_then strip_assume_tac >>
  `?m. j <= m /\ m < h /\ is_pung (EL m ls) /\ ~is_pung (EL (SUC m) ls)` by
  (`~is_pung (EL h ls)` by simp[ping_not_pung] >>
  assume_tac every_range_span_max >>
  last_x_assum (qspecl_then [`\j. is_pung (EL j ls)`,`j`,`h`] strip_assume_tac) >>
  rfs[] >>
  `is_pung (EL m ls)` by fs[] >>
  metis_tac[]) >>
  `!p. j <= p ==> p <= h ==> ~is_pong (EL p ls)` by
    (`j <= h` by decide_tac >>
  assume_tac every_range_less_ends >>
  last_x_assum (qspecl_then [`\j. ~is_pong (EL j ls)`,`j`,`h`] strip_assume_tac) >>
  rfs[ping_not_pong, pung_not_pong]) >>
  `j <= SUC m /\ SUC m <= h` by decide_tac >>
  `~is_pong (EL (SUC m) ls)` by fs[] >>
  `is_ping (EL (SUC m) ls)` by metis_tac[triple_cases] >>
  `EL (SUC m) ls = pung (EL m ls)` by fs[path_element_suc, zagier_flip_pung, Abbr`ls`] >>
  metis_tac[pung_next_not_ping]
QED

(* Yes! This is the key result for the rest. *)

(* Idea: between two pongs, if there is a ping, then all pings after the starting pong. *)

(* Theorem: let ls = path n k in j < h /\ h <= k /\
            is_pong (EL j ls) /\ is_pong (EL h ls) /\ (!p. j < p /\ p < h ==> ~is_pong (EL p ls)) ==>
            !e. j < e /\ e < h /\ is_ping (EL e ls) ==> !p. j < p /\ p <= e ==> is_ping (EL p ls) *)
(* Proof:
   By contradiction, suppose there is (EL p ls) such that:
      j < p <= e /\ ~is_ping (EL p ls).
   Note !p. j < p < h ==> ~is_pong (EL p ls)   by given, [1]
     so for this p,
        j < p <= e < h ==> j < p < h ==> ~is_pong (EL p ls)
   Thus is_pung (EL p ls)                      by triple_cases
    But is_ping (EL e ls)                      by given
   With p <= e, and p <> e, so p < e           by ping_not_pung
    and e < h <= k, so e <= k
    ==> ?q. p < q /\ q < e /\ is_pong (EL q ls)  by pung_to_ping_has_pong, p < e
    yet j < p < q < e < h,  ~is_pong (EL q ls)   by [1]
   This is a contradiction.
*)
Theorem pong_interval_ping_start:
  !n k j h. let ls = path n k in j < h /\ h <= k /\
            is_pong (EL j ls) /\ is_pong (EL h ls) /\ (!p. j < p /\ p < h ==> ~is_pong (EL p ls)) ==>
            !e. j < e /\ e < h /\ is_ping (EL e ls) ==> !p. j < p /\ p <= e ==> is_ping (EL p ls)
Proof
  rw_tac std_ss[] >>
  spose_not_then strip_assume_tac >>
  `p < h` by decide_tac >>
  `~is_pong (EL p ls)` by fs[] >>
  `is_pung (EL p ls)` by metis_tac[triple_cases] >>
  `p <> e` by metis_tac[ping_not_pung] >>
  `p < e /\ e <= k` by decide_tac >>
  assume_tac pung_to_ping_has_pong >>
  last_x_assum (qspecl_then [`n`, `k`, `p`,`e`] strip_assume_tac) >>
  `?q. p < q /\ q < e /\ is_pong (EL q ls)` by metis_tac[] >>
  rfs[]
QED

(* Theorem: let ls = path n k in j < h /\ h <= k /\
            is_pong (EL j ls) /\ is_pong (EL h ls) /\ EVERY (\p. ~is_pong (EL p ls)) [j+1 ..< h] ==>
            !e. j < e /\ e < h /\ is_ping (EL e ls) ==> EVERY (\p. is_ping (EL p ls)) [j+1 .. e] *)
(* Proof:
   Note EVERY (\p. ~is_pong (EL p ls)) [j+1 ..< h]
    <=> !p. j + 1 <= p /\ p < h ==> ~is_pong (EL p ls)     by listRangeLHI_EVERY
    <=> !p. j< p /\ p < h ==> ~is_pong (EL p ls)
    and EVERY (\p. is_ping (EL p ls)) [j+1 .. e]
    <=> !p. j + 1 <= p /\ p <= e ==> is_ping (EL p ls)     by listRangeINC_EVERY
    <=> !p. j < p /\ p <= e ==> is_ping (EL p ls)
    The result follows from pong_interval_ping_start.
*)
Theorem pong_interval_ping_start_alt:
  !n k j h. let ls = path n k in j < h /\ h <= k /\
            is_pong (EL j ls) /\ is_pong (EL h ls) /\ EVERY (\p. ~is_pong (EL p ls)) [j+1 ..< h] ==>
            !e. j < e /\ e < h /\ is_ping (EL e ls) ==> EVERY (\p. is_ping (EL p ls)) [j+1 .. e]
Proof
  rw_tac std_ss[] >>
  rfs[listRangeLHI_EVERY, listRangeINC_EVERY] >>
  `!p. j + 1 <= p <=> j < p` by decide_tac >>
  assume_tac pong_interval_ping_start >>
  last_x_assum (qspecl_then [`n`, `k`, `j`,`h`] strip_assume_tac) >>
  metis_tac[]
QED

(* Idea: between two pongs, if there is a pung, then all pungs to the ending pong. *)

(* Theorem: let ls = path n k in j < h /\ h <= k /\
            is_pong (EL j ls) /\ is_pong (EL h ls) /\ (!p. j < p /\ p < h ==> ~is_pong (EL p ls)) ==>
            !e. j < e /\ e < h /\ is_pung (EL e ls) ==> !p. e <= p /\ p < h ==> is_pung (EL p ls) *)
(* Proof:
   By contradiction, suppose there is (EL p ls) such that:
      e <= p < h /\ ~is_pung (EL p ls).
   Note !p. j < p < h ==> ~is_pong (EL p ls)   by given, [1]
     so for this p,
        j < e <= p < h ==> j < p < h ==> ~is_pong (EL p ls)
   Thus is_ping (EL p ls)                      by triple_cases
    But is_pung (EL e ls)                      by given
   With e <= p, and e <> p, so e < p           by ping_not_pung
    and p < h <= k, so p <= k
    ==> ?q. e < q /\ q < p /\ is_pong (EL q ls)  by pung_to_ping_has_pong, e < p
    yet j < e <= p < q < h,  ~is_pong (EL q ls)  by [1]
   This is a contradiction.
*)
Theorem pong_interval_pung_stop:
  !n k j h. let ls = path n k in j < h /\ h <= k /\
            is_pong (EL j ls) /\ is_pong (EL h ls) /\ (!p. j < p /\ p < h ==> ~is_pong (EL p ls)) ==>
            !e. j < e /\ e < h /\ is_pung (EL e ls) ==> !p. e <= p /\ p < h ==> is_pung (EL p ls)
Proof
  rw_tac std_ss[] >>
  spose_not_then strip_assume_tac >>
  `j < p` by decide_tac >>
  `~is_pong (EL p ls)` by fs[] >>
  `is_ping (EL p ls)` by metis_tac[triple_cases] >>
  `e <> p` by metis_tac[ping_not_pung] >>
  `e < p /\ p <= k` by decide_tac >>
  assume_tac pung_to_ping_has_pong >>
  last_x_assum (qspecl_then [`n`, `k`, `e`,`p`] strip_assume_tac) >>
  `?q. e < q /\ q < p /\ is_pong (EL q ls)` by metis_tac[] >>
  rfs[]
QED

(* Theorem: let ls = path n k in j < h /\ h <= k /\
            is_pong (EL j ls) /\ is_pong (EL h ls) /\ EVERY (\p. ~is_pong (EL p ls)) [j+1 ..< h] ==>
            !e. j < e /\ e < h /\ is_pung (EL e ls) ==> EVERY (\p. is_pung (EL p ls)) [e ..< h] *)
(* Proof:
   Note EVERY (\p. ~is_pong (EL p ls)) [j+1 ..< h]
    <=> !p. j + 1 <= p /\ p < h ==> ~is_pong (EL p ls)     by listRangeLHI_EVERY
    <=> !p. j< p /\ p < h ==> ~is_pong (EL p ls)
    and EVERY (\p. is_pung (EL p ls)) [e ..< h]
    <=> !p. e <= p /\ p < h ==> is_pung (EL p ls)          by listRangeINC_EVERY
    The result follows from pong_interval_pung_stop.
*)
Theorem pong_interval_pung_stop_alt:
  !n k j h. let ls = path n k in j < h /\ h <= k /\
            is_pong (EL j ls) /\ is_pong (EL h ls) /\ EVERY (\p. ~is_pong (EL p ls)) [j+1 ..< h] ==>
            !e. j < e /\ e < h /\ is_pung (EL e ls) ==> EVERY (\p. is_pung (EL p ls)) [e ..< h]
Proof
  rw_tac std_ss[] >>
  rfs[listRangeLHI_EVERY] >>
  `!p. j + 1 <= p <=> j < p` by decide_tac >>
  assume_tac pong_interval_pung_stop >>
  last_x_assum (qspecl_then [`n`, `k`, `j`,`h`] strip_assume_tac) >>
  metis_tac[]
QED

(* Idea: the cut exists, in that between two pongs, there is a switch-over from ping to pung. *)

(* Theorem: let ls = path n k in j < h /\ h <= k /\
            is_pong (EL j ls) /\ is_pong (EL h ls) /\ (!p. j < p /\ p < h ==> ~is_pong (EL p ls)) ==>
            ?c. j < c /\ c <= h /\ ~is_ping (EL c ls) /\
            (!p. j < p /\ p < c ==> is_ping (EL p ls)) /\ (!p. c <= p /\ p < h ==> is_pung (EL p ls)) *)
(* Proof:
   Note j < h ==> SUC j <= h.
   If SUC j = h,
      pick c = h, that is c = SUC j.
      Then j < p < c = SUC j ==> no such p for is_ping (EL p ls)
       and h = c <= p < h ==> no such p for is_pung (EL p ls)
   Otherwise, SUC j < h.
      Let q = SUC j, then j < q < h.
      Note ~is_pong (EL q ls)                  by given
       so either is_ping or is_pung            by triple_cases

      If is_ping (EL q ls),
         Note ~is_ping (EL h ls)               by pong_not_ping
          ==> ?m. p <= m /\ m < h /\
                  (!j. p <= j /\ j <= m ==> is_ping (EL j ls)) /\
                  ~is_ping (EL (SUC m) ls)     by every_range_span_max
         Pick c = SUC m = m + 1.
         Note !p. SUC j <= p <=> j < p         by arithmetic
           so !p. j < p /\ p < c ==> is_ping (EL p ls)     by above

          Now ~is_ping (EL c ls)               by above
          and c <= h means c = h or c < h.
         If c = h, then trivially
            !p. c <= p /\ p < h ==> is_pung (EL p ls).
            and ~is_ping (EL c ls)             by pong_not_ping
         If c < h,
            Then ~is_pong (EL c ls)            by j < c < h
              so is_pung (EL c ls)             by triple_cases
             ==> !p. c <= p /\ p < h ==> is_pung (EL p ls)
                                               by pong_interval_pung_stop
             and ~is_ping (EL c ls)            by pung_not_ping

      If is_pung (EL q ls),
         Pick c = SUC j.
         Then j < p < c = SUC j ==> no such p for is_ping (EL p ls)
          and !p. j < p <=> SUC j = c <= p     by arithmetic
           so !p. c <= p /\ p < h ==> is_pung (EL p ls)
                                               by pong_interval_pung_stop
          and if c < h, ~is_ping (EL c ls)     by pung_not_ping
           or if c = h, ~is_ping (EL c ls)     by pong_not_ping
*)
Theorem pong_interval_cut_exists:
  !n k j h. let ls = path n k in j < h /\ h <= k /\
            is_pong (EL j ls) /\ is_pong (EL h ls) /\ (!p. j < p /\ p < h ==> ~is_pong (EL p ls)) ==>
            ?c. j < c /\ c <= h /\ ~is_ping (EL c ls) /\
            (!p. j < p /\ p < c ==> is_ping (EL p ls)) /\ (!p. c <= p /\ p < h ==> is_pung (EL p ls))
Proof
  rw_tac std_ss[] >>
  `SUC j = h \/ SUC j < h` by decide_tac >| [
    qexists_tac `h` >>
    simp[pong_not_ping],
    `j < SUC j` by decide_tac >>
    qabbrev_tac `q = SUC j` >>
    `~is_pong (EL q ls)` by fs[] >>
    `is_ping (EL q ls) \/ is_pung (EL q ls)` by metis_tac[triple_cases] >| [
      `~is_ping (EL h ls)` by simp[pong_not_ping] >>
      assume_tac every_range_span_max >>
      last_x_assum (qspecl_then [`\p. is_ping (EL p ls)`, `q`, `h`] strip_assume_tac) >>
      rfs[] >>
      `q < SUC m /\ SUC m <= h` by decide_tac >>
      qabbrev_tac `c = SUC m` >>
      qexists_tac `c` >>
      `!p. q <= p /\ p <= m <=> j < p /\ p < c` by simp[Abbr`q`, Abbr`c`] >>
      rfs[] >>
      `c = h \/ c < h` by decide_tac >-
      simp[] >>
      `~is_pong (EL c ls)` by fs[] >>
      `is_pung (EL c ls)` by metis_tac[triple_cases] >>
      assume_tac pong_interval_pung_stop >>
      last_x_assum (qspecl_then [`n`, `k`, `j`, `h`] strip_assume_tac) >>
      rfs[] >>
      `j < c` by fs[Abbr`q`] >>
      metis_tac[],
      qexists_tac `q` >>
      rfs[pung_not_ping, Abbr`q`] >>
      assume_tac pong_interval_pung_stop >>
      last_x_assum (qspecl_then [`n`, `k`, `j`, `h`] strip_assume_tac) >>
      rfs[] >>
      `j < SUC j` by decide_tac >>
      metis_tac[]
    ]
  ]
QED

(* Theorem: let ls = path n k in j < h /\ h <= k /\
            is_pong (EL j ls) /\ is_pong (EL h ls) /\ EVERY (\p. ~is_pong (EL p ls)) [j+1 ..< h] ==>
            ?c. j < c /\ c <= h /\ ~is_ping (EL c ls) /\
            EVERY (\p. is_ping (EL p ls)) [j+1 ..< c] /\ EVERY (\p. is_pung (EL p ls)) [c ..< h] *)
(* Proof:
       EVERY (\p. ~is_pong (EL p ls)) [j+1 ..< h]
   <=> !p. j + 1 <= p /\ p < h ==> ~is_pong (EL p ls)      by listRangeLHI_EVERY
   <=> !p. j < p /\ p < h ==> ~is_pong (EL p ls)           by arithmetic
   Thus ?c. j < c /\ c <= h /\ ~is_ping (EL c ls) /\
            (!p. j < p /\ p < c ==> is_ping (EL p ls)) /\
            (!p. c <= p /\ p < h ==> is_pung (EL p ls))    by pong_interval_cut_exists
    ==> !p. j + 1 <= p /\ p < c ==> is_ping (EL p ls)      by arithmetic
   Thus EVERY (\p. is_ping (EL p ls)) [j+1 ..< c] /\
        EVERY (\p. is_pung (EL p ls)) [c ..< h]            by listRangeLHI_EVERY
*)
Theorem pong_interval_cut_exists_alt:
  !n k j h. let ls = path n k in j < h /\ h <= k /\
            is_pong (EL j ls) /\ is_pong (EL h ls) /\ EVERY (\p. ~is_pong (EL p ls)) [j+1 ..< h] ==>
            ?c. j < c /\ c <= h /\ ~is_ping (EL c ls) /\
            EVERY (\p. is_ping (EL p ls)) [j+1 ..< c] /\ EVERY (\p. is_pung (EL p ls)) [c ..< h]
Proof
  rw[listRangeLHI_EVERY] >>
  `!p b. j + 1 <= p /\ p < b <=> j < p /\ p < b` by decide_tac >>
  assume_tac pong_interval_cut_exists >>
  last_x_assum (qspecl_then [`n`, `k`, `j`, `h`] strip_assume_tac) >>
  metis_tac[]
QED

(* Yes! A major achievement! *)

(* Example:
ls = path 61 6
is_pong (EL 0 ls) = is_pong (1,1,15) = T
is_ping (EL 1 ls) = is_ping (1,15,1) = T
is_ping (EL 2 ls) = is_ping (3,13,1) = T
is_ping (EL 3 ls) = is_ping (5,9,1) = T
is_pung (EL 4 ls) = is_pung (7,3,1) = T
ls_pong (EL 5 ls) = is_pong (1,3,5) = T
is_pong (EL 6 ls) = is_pong (5,3,3) = T

cut c = 4.
*)

(* Idea: let e be a pong, then there are j and h with j < e a stretch of pungs, and e < h a strech of pings. *)

(* Theorem: let ls = path n k in ~is_pung (HD ls) /\ e < k /\ is_pong (EL e ls) ==>
             ?j. j <= e /\ (!p. j <= p /\ p < e ==> is_pung (EL p ls)) /\ ~is_pung (EL (PRE j) ls) *)
(* Proof:
   If e = 0,
      Pick j = 0, then PRE j = 0 = e           by arithmetic
      Then is_pong (EL e ls)
       ==> ~is_pung (EL (PRE j) ls)            by pong_not_pung
      and the range 0 <= p /\ p < e is empty.

   If 0 < e,
      Let d = e - 1, then d < e.
      Consider the three cases of (EL d ls).

      Case: is_ping (EL d ls)
         Pick j = e, then PRE j = PRE e = d.
         Then ~is_pung (EL d ls)               by ping_not_pung
          and the range e <= p /\ p < e is empty.

      Case: is_pong (EL d ls)
         Pick j = e, then PRE j = PRE e = d.
         Then ~is_pung (EL d ls)               by pong_not_pung
          and the range e <= p /\ p < e is empty.

      Case: is_pung (EL d ls)
         Note HD ls = EL 0 ls                  by EL
          and ~is_pung (EL 0 ls)               by given
          ==> ?m. 0 < m /\ m <= e /\
                  (!j. m <= j /\ j <= e ==> is_pung (EL j ls)) /\
               ~is_pung (EL (PRE m) ls)        by every_range_span_min, 0 < e
         Pick j = m, and j <= e.
*)
Theorem pong_seed_pung_before:
  !n k e. let ls = path n k in ~is_pung (HD ls) /\ e < k /\ is_pong (EL e ls) ==>
          ?j. j <= e /\ (!p. j <= p /\ p < e ==> is_pung (EL p ls)) /\ ~is_pung (EL (PRE j) ls)
Proof
  rw_tac std_ss[] >>
  `e = 0 \/ 0 < e` by decide_tac >| [
    qexists_tac `0` >>
    fs[pong_not_pung],
    `e - 1 < e /\ PRE e = e - 1` by decide_tac >>
    qabbrev_tac `d = e - 1` >>
    `is_ping (EL d ls) \/ is_pong (EL d ls) \/ is_pung (EL d ls)` by metis_tac[triple_cases] >| [
      qexists_tac `e` >>
      fs[ping_not_pung],
      qexists_tac `e` >>
      fs[pong_not_pung],
      `HD ls = EL 0 ls` by simp[] >>
      `d <> 0` by metis_tac[] >>
      `0 < d` by decide_tac >>
      assume_tac every_range_span_min >>
      last_x_assum (qspecl_then [`\p. is_pung (EL p ls)`, `0`, `d`] strip_assume_tac) >>
      rfs[] >>
      qexists_tac `m` >>
      simp[]
    ]
  ]
QED

(* Theorem: let ls = path n k in ~is_ping (LAST ls) /\ e < k /\ is_pong (EL e ls) ==>
            ?h. e <= h /\ h < k /\ (!p. e < p /\ p <= h ==> is_ping (EL p ls)) /\ ~is_ping (EL (SUC h) ls) *)
(* Proof:
   Note LAST ls = EL k ls                      by path_last_alt
   Let d = SUC e, then e < d
   Then e < k ==> SUC e = d <= k               by arithmetic
   Consider the three cases of (EL d ls).

   Case: is_ping (EL d ls)
      Note ~is_ping (EL k ls) ==> d <> k       by given
        so d < k
       ==> ?m. d <= m /\ m < k /\
               (!j. d <= j /\ j <= m ==> is_ping (EL j ls)) /\
               ~is_ping (EL (SUC m) ls)        by every_range_span_max
      Pick h = m, and !j. d <= j <=> e < j.
       and d <= h, or SUC e <= h, or e < h, satisfying e <= h.
       and h = m < k.

   Case: is_pong (EL d ls)
      Pick h = e
        so ~is_ping (EL d ls)                  by pong_not_ping
       and the range e < p <= e is empty.

   Case: is_pung (EL d ls)
      Pick h = e
        so ~is_ping (EL d ls)                  by pung_not_ping
       and the range e < p <= e is empty.
*)
Theorem pong_seed_ping_after:
  !n k e. let ls = path n k in ~is_ping (LAST ls) /\ e < k /\ is_pong (EL e ls) ==>
          ?h. e <= h /\ h < k /\ (!p. e < p /\ p <= h ==> is_ping (EL p ls)) /\ ~is_ping (EL (SUC h) ls)
Proof
  rw_tac std_ss[] >>
  `~is_ping (EL k ls)` by fs[path_last_alt, Abbr`ls`] >>
  `SUC e <= k` by decide_tac >>
  qabbrev_tac `d = SUC e` >>
  `is_ping (EL d ls) \/ is_pong (EL d ls) \/ is_pung (EL d ls)` by metis_tac[triple_cases] >| [
    `d <> k` by metis_tac[] >>
    `d < k` by decide_tac >>
    assume_tac every_range_span_max >>
    last_x_assum (qspecl_then [`\p. is_ping (EL p ls)`, `d`, `k`] strip_assume_tac) >>
    rfs[] >>
    `!j. d <= j <=> e < j` by simp[Abbr`d`] >>
    qexists_tac `m` >>
    simp[Abbr`d`],
    qexists_tac `e` >>
    simp[pong_not_ping],
    qexists_tac `e` >>
    simp[pung_not_ping]
  ]
QED

(* Theorem: let ls = path n k in ~is_pung (HD ls) /\ ~is_ping (LAST ls) /\ e < k /\ is_pong (EL e ls) ==>
            ?j h. j <= e /\ e <= h /\ h < k /\
                  (!p. j <= p /\ p < e ==> is_pung (EL p ls)) /\ ~is_pung (EL (PRE j) ls) /\
                  (!p. e < p /\ p <= h ==> is_ping (EL p ls)) /\ ~is_ping (EL (SUC h) ls) *)
(* Proof: by pong_seed_pung_before, pong_seed_ping_after. *)
Theorem pong_seed_pung_ping:
  !n k e. let ls = path n k in ~is_pung (HD ls) /\ ~is_ping (LAST ls) /\ e < k /\ is_pong (EL e ls) ==>
           ?j h. j <= e /\ e <= h /\ h < k /\
                 (!p. j <= p /\ p < e ==> is_pung (EL p ls)) /\ ~is_pung (EL (PRE j) ls) /\
                 (!p. e < p /\ p <= h ==> is_ping (EL p ls)) /\ ~is_ping (EL (SUC h) ls)
Proof
  metis_tac[pong_seed_pung_before, pong_seed_ping_after]
QED

(* Finally, this justifies the definition of blocks. *)

(*
The path starts with ~is_pung, end at flip fix a ~is_ping.
Path starts with is_pong, so also starts with ~is_ping and ends at ~is_ping.

patterns of blocks:
pong -> ping -> (block)
pung -> pong -> ping -> (block)
pung -> pong -> (block)

where (block) is pong or pung, i.e. ~is_ping.

n = 61 has 2 blocks:
block (path 61 6) 0 = (0,0,4)
      (1,1,15) -> (1,15,1) -> (3,13,1) -> (5,9,1) -> (7,3,1)
      is_pong     is_ping     is_ping     is_ping    is_pung
block (path 61 6) 1 = (4,5,6)
      (7,3,1) -> (1,3,5) -> (5,3,3)
      is_pung    is_pong    is_pong

n = 41 has 3 blocks:
block (path 41 6) 0 = (0,0,3)
      (1,1,10) -> (1,10,1) -> (3,8,1) -> (5,4,1)
      is_pong     is_ping     is_ping    is_pong
block (path 41 6) 1 = (3,3,4)
      (5,4,1) -> (3,2,4)
      is_pong    is_pong
block (path 41 6) 2 = (4,4,6)
      (3,2,4) -> (1,5,2) -> (5,2,2)
      is_pong     is_ping   is_pung

Thus:
* every block starts with pong or pung, a ~is_ping (EL j ls)
* every block ends with pong or pung, again ~is_ping (EL h ls), overlapping the start of next.
* prove that: from ~is_ping (EL j ls), either it is pong or pung. Use skip_pung to locate the next pong.
* prove that: from a pong, use skip_ping to locate the next ~is_ping, as end of block.
*)

(* Theorem: 0 < y /\ is_pung (x,y,z) ==>
            let t = pung (x,y,z) in flip t <> t *)
(* Proof:
   By contradiction, assume flip t = t.
   Note ~(x < z - y) /\ ~(x < 2 * z)           by is_pung_def
     or z - y <= x /\ 2 * z <= x               by NOT_LESS, [1]
    and t = pung (x,y,z)
          = (x - 2 * z,x + y - z,z)            by pung_def
   Then z = x + y - z                          by flip_fix
     or 2 * z = x + y                          by arithmetic
    ==> x + y <= x                             by [1]
   which is impossible when 0 < y.
*)
Theorem pung_next_not_flip_fix:
  !x y z. 0 < y /\ is_pung (x,y,z) ==>
          let t = pung (x,y,z) in flip t <> t
Proof
  rw_tac std_ss[] >>
  spose_not_then strip_assume_tac >>
  fs[is_pung_def, pung_def, Abbr`t`] >>
  fs[flip_fix]
QED

(* Theorem: let ls = path n k in tik n /\ ~square n /\ flip (LAST ls) = LAST ls ==> ~is_pung (EL (k-1) ls) *)
(* Proof:
   Let t = EL (k-1) ls.
   By contradiction, assume is_pung t.

   If k = 0,
      Then t = EL 0 ls             by integer arithmetic
       and is_pong t               by path_head_is_pong
        so ~is_pung t              by pong_not_pung
      leading to contradiction.

   If 0 < k, SUC (k-1) = k         by arithmetic
   Note LAST ls
      = EL k ls                    by path_last_alt
      = (zagier o flip) t          by path_element_suc
      = pung t                     by zagier_flip_pung, is_pung t

   Now t = (x,y,z)                 by triple_parts
   and t IN (mills n)              by path_element_in_mills, tik n
    so 0 < y                       by mills_with_arms, ~square n
   ==> flip t <> t                 by pung_next_not_flip_fix
   This contradicts flip t = t.
*)
Theorem path_last_flip_fix_not_by_pung:
  !n k e. let ls = path n k in tik n /\ ~square n /\
          flip (LAST ls) = LAST ls ==> ~is_pung (EL (k-1) ls)
Proof
  rw_tac std_ss[] >>
  spose_not_then strip_assume_tac >>
  qabbrev_tac `t = EL (k - 1) ls` >>
  `k = 0 \/ 0 < k` by decide_tac >| [
    `k - 1 = 0` by decide_tac >>
    metis_tac[path_head_is_pong, pong_not_pung],
    `SUC (k - 1) = k /\ k - 1 < k` by decide_tac >>
    `LAST ls = pung t` by metis_tac[path_last_alt, path_element_suc, zagier_flip_pung] >>
    `?x y z. t = (x,y,z)` by metis_tac[triple_parts] >>
    `t IN mills n` by simp[path_element_in_mills, Abbr`ls`,Abbr`t`] >>
    `0 < y` by metis_tac[mills_with_arms] >>
    metis_tac[pung_next_not_flip_fix]
  ]
QED

(* Theorem: let ls = path n k in tik n /\ ~square n /\ j < h /\ h <= k /\ is_pong (EL j ls) /\ flip (EL h ls) = EL h ls /\
            (!p. j < p /\ p < h ==> ~is_pong (EL p ls)) ==> !p. j < p /\ p < h ==> is_ping (EL p ls) *)
(* Proof:
   Let ls = path n k.
   To show: !p. j < p /\ p < h ==> is_ping (EL p ls)

   By contradiction, assume ~is_ping (EL p ls).
   Note ~is_pong (EL p ls)                     by given condition
   Thus is_pung (EL p ls)                      by triple_cases

   Note 0 < h                                  by j < h
   Let d = h - 1, then p <= d
   Note ~is_pong (EL d ls)                     by j < p <= d /\ d < h

   Claim: ~is_pung (EL d ls)
   Proof: By contradiction, suppose is_pung (EL d ls).
          Note n = windmill (EL d ls)          by path_element_windmill
          Let (x y z) = EL d ls, then 0 < y    by windmill_with_arms
            EL h ls
          = (zagier o flip) (EL d ls)          by path_element_suc, ADD1
          = pung (EL d ls)                     by zagier_flip_pung
          Thus flip (EL h ls) <> EL h ls       by pung_next_not_flip_fix
          This is a contradiction.

   Thus is_ping (EL d ls)                      by triple_cases
    and p <> d                                 by pung_not_ping
    ==> ?c. p < c /\ c < d /\ is_pong (EL c ls)
                                               by pung_to_ping_has_pong
   This contradicts ~is_pong (EL c ls)         by j < p < c /\ c < d < h
*)
Theorem path_last_pong_to_flip_fix:
  !n k j h. let ls = path n k in tik n /\ ~square n /\ j < h /\ h <= k /\ is_pong (EL j ls) /\ flip (EL h ls) = EL h ls /\
            (!p. j < p /\ p < h ==> ~is_pong (EL p ls)) ==> !p. j < p /\ p < h ==> is_ping (EL p ls)
Proof
  rw_tac std_ss[] >>
  spose_not_then strip_assume_tac >>
  `is_pung (EL p ls)` by metis_tac[triple_cases] >>
  `p <= h - 1 /\ h - 1 < h /\ h = (h - 1) + 1` by decide_tac >>
  qabbrev_tac `d = h - 1` >>
  `~is_pong (EL d ls)` by fs[] >>
  `~is_pung (EL d ls)` by
  (spose_not_then strip_assume_tac >>
  `EL h ls = (zagier o flip) (EL d ls)` by fs[path_element_suc, GSYM ADD1, Abbr`ls`] >>
  `_ = pung (EL d ls)` by simp[zagier_flip_pung] >>
  `n = windmill (EL d ls)` by fs[path_element_windmill, Abbr`ls`] >>
  `?x y z. EL d ls = (x,y,z) /\ 0 < y` by metis_tac[triple_parts, windmill_with_arms] >>
  metis_tac[pung_next_not_flip_fix]) >>
  `is_ping (EL d ls)` by metis_tac[triple_cases] >>
  `p <> d` by metis_tac[pung_not_ping] >>
  assume_tac pung_to_ping_has_pong >>
  last_x_assum (qspecl_then [`n`, `k`, `p`, `d`] strip_assume_tac) >>
  rfs[] >>
  rename1 `c < d` >>
  `j < c /\ c < h` by decide_tac >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* Hopping                                                                   *)
(* ------------------------------------------------------------------------- *)

(* Define the hop map *)
Definition hop_def:
   hop m (x,y,z) = if x < 2 * m * z
                   then (2 * m * z - x, z, y + m * x - m * m * z)
                   else (x - 2 * m * z, y + m * x - m * m * z, z)
End
(* Note: x <> 2 * m * z for a windmill, see windmill_mind_odd. *)
(* The condition x < 2 * m * z matches is_pong when m = 1. *)
(* first Hop Matrix: H = [[-1,0,2*m],[0,0,1],[m,1,-m*m]]
This has a diagonalisation: H = P D P^(-1), where D is diagonal. *)
(* second Hop Matrix: H = [[1,0,-2*m],[m,1,-m*m],[0,0,1]]
This has a Jordan form: H = S J S^(-1), where J is not diagonal. *)

(* Example for n = 61:
> EVAL ``hop 0 (1,15,1)``; = (1,15,1)
> EVAL ``hop 1 (1,15,1)``; = (1,1,15)
> EVAL ``hop 2 (1,15,1)``; = (3,1,13)
> EVAL ``hop 3 (1,15,1)``; = (5,1,9)
> EVAL ``hop 4 (1,15,1)``; = (7,1,3)
> EVAL ``hop 5 (1,15,1)``; = (9,1,0) <-- hop too much!
> EVAL ``hop 0 (7,1,3)``; = (7,1,3)
> EVAL ``hop 1 (7,1,3)``; = (1,5,3)
> EVAL ``hop 2 (7,1,3)``; = (5,3,3)
*)

(*
DIV_LE_X  |- !x y z. 0 < z ==> (y DIV z <= x <=> y < (x + 1) * z)
DIV_LT_X  |- !x y z. 0 < z ==> (y DIV z < x <=> y < x * z)
X_LE_DIV  |- !x y z. 0 < z ==> (x <= y DIV z <=> x * z <= y)
X_LT_DIV  |- !x y z. 0 < z ==> (x < y DIV z <=> (x + 1) * z <= y)
*)

(* Theorem: 0 < z ==>
            hop m (x,y,z) = if x DIV (2 * z) < m
                            then (2 * m * z - x, z, y + m * x - m * m * z)
                            else (x - 2 * m * z, y + m * x - m * m * z, z) *)
(* Proof:
   Note x DIV (2 * z) < m
    <=> x < 2 * m * z              by DIV_LT_X, 0 < z
   The result follows              by hop_def
*)
Theorem hop_alt:
  !m x y z. 0 < z ==>
            hop m (x,y,z) = if x DIV (2 * z) < m
                            then (2 * m * z - x, z, y + m * x - m * m * z)
                            else (x - 2 * m * z, y + m * x - m * m * z, z)
Proof
  rpt strip_tac >>
  `x DIV (2 * z) < m <=> x < 2 * m * z` by simp[DIV_LT_X] >>
  simp[hop_def]
QED

(* Theorem: hop 0 t = t *)
(* Proof: by hop_def, as x < 0 is false. *)
Theorem hop_0:
  !t. hop 0 t = t
Proof
  simp[hop_def, FORALL_PROD]
QED

(* Theorem: ~is_ping t ==> hop 1 t = (zagier o flip) t *)
(* Proof:
   Let (x,y,z) = t,
             f = zagier o flip.
   Note ~is_ping (x,y,z) means ~(x < z - y)    by is_ping_def
    and hop 1 (x,y,z)
      = if x < 2 * z
        then (2 * z - x, z, y + x - z)
        else (x - 2 * z, y + x - z, z)         by hop_def
      = if x < 2 * z
        then pong (x,y,z)                      by pong_def
        else pung (x,y,z)                      by pung_def
   If x < 2 * z, then is_pong (x,y,z)          by is_pong_def, ~(x < z - y)
      so hop 1 (x,y,z) = f (x,y,z)             by zagier_flip_pong
   Otherwise, is_pung (x,y,z)                  by is_pung_def, ~(x < z - y)
      so hop 1 (x,y,z) = f (x,y,z)             by zagier_flip_pung
*)
Theorem hop_1:
  !t. ~is_ping t ==> hop 1 t = (zagier o flip) t
Proof
  simp[is_ping_def, hop_def, zagier_flip_eqn, FORALL_PROD]
QED

(*
max hopping from (x,y,z) = (x + √n)/(2 * z)

For n = 89, start with (1,22,1), SQRT n = 9.
> EVAL ``let (x,y,z) = (1,22,1) in hop ((x + 9) DIV (2 * z)) (x,y,z)``; = (9,1,2)
> EVAL ``let (x,y,z) = (9,1,2) in hop ((x + 9) DIV (2 * z)) (x,y,z)``; = (7,2,5)
> EVAL ``let (x,y,z) = (7,2,5) in hop ((x + 9) DIV (2 * z)) (x,y,z)``; = (3,5,4)
> EVAL ``let (x,y,z) = (3,5,4) in hop ((x + 9) DIV (2 * z)) (x,y,z)``; = (5,4,4)

For n = 137, start with (1,34,1), SQRT n = 11.
> EVAL ``let (x,y,z) = (1,34,1) in hop ((x + 11) DIV (2 * z)) (x,y,z)``; = (11,1,4)
> EVAL ``let (x,y,z) = (11,1,4) in hop ((x + 11) DIV (2 * z)) (x,y,z)``; = (5,4,7)
> EVAL ``let (x,y,z) = (5,4,7) in hop ((x + 11) DIV (2 * z)) (x,y,z)``; = (9,7,2)
> EVAL ``let (x,y,z) = (9,7,2) in hop ((x + 11) DIV (2 * z)) (x,y,z)``; = (11,2,2)
*)


(* Idea: condition for hop m (x,y,z) to have a mind. *)

(* Theorem: 0 < z ==> (x DIV (2 * z) < m <=> 0 < 2 * m * z - x) *)
(* Proof:
       x DIV (2 * z) < m
   <=> x < m * (2 * z)             by DIV_LT_X, 0 < z
   <=> 0 < 2 * m * z - x           by inequality
*)
Theorem hop_mind:
  !m x z. 0 < z ==> (x DIV (2 * z) < m <=> 0 < 2 * m * z - x)
Proof
  rpt strip_tac >>
  `0 < 2 * z` by decide_tac >>
  fs[DIV_LT_X]
QED

(* Idea: condition for hop m (x,y,z) to have arms. *)

(* Theorem: ~square n /\ n = windmill (x,y,z) ==>
            (m <= (x + SQRT n) DIV (2 * z) <=> 0 < y + m * x - m * m * z) *)
(* Proof:
   Note 0 < y /\ 0 < z                         by windmill_with_arms, ~square n
   For the expression (y + m * x - m * m * z),
   with a quadratic dependence on m, surely m cannot be too large.

   If part: m <= (x + SQRT n) DIV (2 * z) ==> 0 < y + m * x - m ** 2 * z
      If x < 2 * m * z,
      Note m <= (x + SQRT n) DIV (2 * z)
       <=> 2 * m * z <= x + SQRT n                 by X_LE_DIV, 0 < z
       <=> 2 * m * z - x <= SQRT n                 by inequality
       ==> (2 * m * z - x) ** 2 <= (SQRT n) ** 2   by EXP_EXP_LE_MONO_IMP
       ==> (2 * m * z - x) ** 2 < n                by SQ_SQRT_LT_alt, ~square n
       ==> (2 * m * z - x) ** 2 < x ** 2 + 4 * y * z                               by windmill_def
       ==> (2 * m * z - x) ** 2 + 4 * m * x * z < x ** 2 + 4 * y * z + 4 * m * x * z
       ==> (2 * m * z) ** 2 + x ** 2 < x ** 2 + 4 * z * y + 4 * m * x * z          by binomial_sub_sum, x < 2 * m * z
       <=>          (2 * m * z) ** 2 < 4 * z * y + 4 * m * x * z                   by inequality
       <=>             m * m * z * z < y * z + m * x * z                           by EXP_2
       <=>           (m * m * z) * z < (y + m * x) * z                             by LEFT_ADD_DISTRIB
       <=>                 m * m * z < y + m * x                                   by LT_MULT_LCANCEL, 0 < z
       <=>                         0 < y + m * x - m * m * z                       by inequality

   Otherwise, 2 * m * z <= x.
       Thus   m * (2 * m * z) <= m * x             by LE_MULT_LCANCEL
       ==>     2 * m ** 2 * z <= m * x             by EXP_2
      2 * m ** 2 * z + y - m ** 2 * z <= m * x + y - m ** 2 * z
      y + m ** 2 * z <= y + m * x - m ** 2 * z
      LHS is > 0.

   Only-if part: 0 < y + m * x - m ** 2 * z ==> m <= (x + SQRT n) DIV (2 * z)
      If x < 2 * m * z
               0 < y + m * x - m ** 2 * z
         <=>   m ** 2 * z < y + m * x                                        by inequality
         <=> 4 * z * (m ** 2 * z) < 4 * z * (y + m * x)                      by LT_MULT_LCANCEL, 0 < z
         <=> 4 * z * m ** 2 + x ** 2 < x ** 2 + 4 * y * z + 4 * m * z * x    by LEFT_ADD_DISTRIB
         <=> 4 * z * m ** 2 + x ** 2 < n + 4 * m * z * x                     by windmill_def
         <=>                    (2 * z * m - x) ** 2 < n                     by binomial_sub_add, x < 2 * m * z
         ==>                     2 * z * m - x <= SQRT n                     by SQRT_LT, SQRT_OF_SQ
         ==>                         2 * z * m <= x + SQRT n                 by inequality
         ==>                                 m <= (x + SQRT n) DIV (2 * z)   by X_LE_DIV, 0 < z

      Otherwise, 2 * m * z <= x
              m <= x DIV (2 * z)               by X_LE_DIV, 0 < z
         ==>  m <= (x + SQRT n) DIV (2 * z)    by DIV_LE_MONOTONE, 0 < z
*)
Theorem hop_arm:
  !m n x y z. ~square n /\ n = windmill (x,y,z) ==>
              (m <= (x + SQRT n) DIV (2 * z) <=> 0 < y + m * x - m * m * z)
Proof
  rpt strip_tac >>
  `0 < y /\ 0 < z` by metis_tac[windmill_with_arms] >>
  qabbrev_tac `X = (n = windmill (x,y,z))` >>
  rw[EQ_IMP_THM] >| [
    `x < 2 * m * z \/ 2 * m * z <= x` by decide_tac >| [
      qabbrev_tac `zz = 2 * m * z` >>
      `(zz - x) ** 2 < n` by
  (`zz <= x + SQRT n` by rfs[X_LE_DIV, Abbr`zz`] >>
      `(zz - x) ** 2 <= (SQRT n) ** 2` by simp[EXP_EXP_LE_MONO_IMP] >>
      `(SQRT n) ** 2 < n` by simp[SQ_SQRT_LT_alt] >>
      decide_tac) >>
      `m ** 2 * z < y + m * x` by
    (`n = x ** 2 + 4 * y * z` by fs[windmill_def] >>
      `2 * zz * x = 4 * m * x * z` by simp[Abbr`zz`] >>
      `zz ** 2 + x ** 2 < 4 * (z * y) + x ** 2 + 4 * m * x * z` by simp[GSYM binomial_sub_sum] >>
      `zz ** 2 = 4 * z * (m * m * z)` by simp[Abbr`zz`, EXP_BASE_MULT] >>
      `4 * z * (m * m * z) < 4 * z * (y + m * x)` by decide_tac >>
      fs[]) >>
      decide_tac,
      `m * (2 * m * z) <= m * x` by simp[] >>
      `m * (2 * m * z) = 2 * m ** 2 * z` by fs[] >>
      decide_tac
    ],
    `x < 2 * m * z \/ 2 * m * z <= x` by decide_tac >| [
      `4 * z * (m * m * z) < 4 * z * (y + m * x)` by fs[] >>
      `4 * z * (m * m * z) = (2 * m * z) ** 2` by simp[EXP_BASE_MULT] >>
      `4 * z * (y + m * x) = 4 * z * y + 4 * m * x * z` by simp[] >>
      `n = x ** 2 + 4 * y * z` by fs[windmill_def] >>
      `(2 * m * z) ** 2 + x ** 2 < n + 4 * m * x * z` by decide_tac >>
      `(2 * m * z) ** 2 + x ** 2 = (2 * m * z - x) ** 2 + 4 * m * x * z` by simp[GSYM binomial_sub_sum] >>
      `(2 * m * z - x) ** 2 < n` by decide_tac >>
      `(2 * m * z - x) <= SQRT n` by metis_tac[SQRT_LT, SQRT_OF_SQ] >>
      `m * (2 * z) <= x + SQRT n` by decide_tac >>
      simp[X_LE_DIV],
      `m <= x DIV (2 * z)` by simp[X_LE_DIV] >>
      `x <= x + SQRT n /\ 0 < 2 * z` by decide_tac >>
      metis_tac[DIV_LE_MONOTONE, LESS_EQ_TRANS]
    ]
  ]
QED

(* Idea: the first of a hop triple is always positive. *)

(* Theorem: tik n /\ n = windmill t ==> 0 < FST (hop m t) *)
(* Proof:
   Let (x,y,z) = t                                                 by FORALL_PROD
   If x < 2 * (m * z),
   Then hop m (x,y,z) = (2 * m * z - x,z,y + m * x - m * m * z)    by hop_def
     so FST (hop m (x,y,z)) = 2 * m * z - x                        by FST
    and 0 < 2 * m * z - x                                          by x < 2 * (m * z)

   If ~(x < 2 * (m * z)),
   Then hop m (x,y,z) = (x - 2 * m * z,y + m * x - m * m * z,z)    by hop_def
     so FST (hop m (x,y,z)) = x - 2 * m * z                        by FST
    but ODD x                                                      by windmill_mind_odd, tik n
     so x <> 2 * (m * z)                                           by EVEN_DOUBLE, EVEN_ODD
    ==> 0 < x - 2 * m * z                                          by arithmetic
*)
Theorem hop_triple_first:
  !n m t. tik n /\ n = windmill t ==> 0 < FST (hop m t)
Proof
  simp[hop_def, FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `windmill (x,y,z)` >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  rw[] >>
  `2 * (m * z) <= x` by decide_tac >>
  `ODD x` by metis_tac[windmill_mind_odd] >>
  `x <> 2 * (m * z)` by metis_tac[EVEN_DOUBLE, EVEN_ODD] >>
  decide_tac
QED

(* Idea: hop goes from windmill to windmill. *)

(* Theorem: ~square n /\ n = windmill (x,y,z) /\ m <= (x + SQRT n) DIV (2 * z) ==>
            n = windmill (hop m (x,y,z)) *)
(* Proof:
   Note 0 < y /\ 0 < z                         by windmill_with_arms, ~square n
    and 0 < y + m * x - m * m * z              by hop_arm, ~square n
    ==> m * m * z < y + m * x                                      by inequality
    ==> 4 * z * (m * m * z) < 4 * z * (y + m * x)                  by 0 < z
    ==> 4 * z * (m * m * z) < 4 * z * y + 4 * z * m * x            by LEFT_ADD_DISTRIB
    ==>   4 * z * m * m * z < 4 * z * y + 4 * m * x * z            by arithmetic, [1]

   If x < 2 * (m * z),
   Then hop m (x,y,z) = (2 * m * z - x,z,y + m * x - m * m * z)    by hop_def
        windmill (hop m (x,y,z))
      = (2 * m * z - x) ** 2 + 4 * z * (y + m * x - m * m * z)     by windmill_def
      = (2 * m * z - x) ** 2 + (4 * z * (y + m * x) - 4 * z * m * m * z)        by LEFT_SUB_DISTRIB
      = (2 * m * z - x) ** 2 + (4 * z * y + 4 * m * z * x - 4 * z * m * m * z)  by LEFT_ADD_DISTRIB
      = (2 * m * z - x) ** 2 + 4 * z * y + 4 * m * z * x - 4 * z * m * m * z    by [1]
      = (2 * m * z - x) ** 2 + 2 * (2 * m * z) * x + 4 * y * z - 4 * z * m * m * z
      = (2 * m * z) ** 2 + x ** 2 + 4 * z * y - 4 * z * m * m * z  by binomial_sub_sum, x < 2 * (m * z)
      = 4 * m ** 2 * z ** 2 + x ** 2 + 4 * z * y - 4 * m ** 2 * z ** 2          by EXP_2, EXP_BASE_MULT
      = x ** 2 + 4 * z * y                                         by arithmetic
      = n                                                          by windmill_def

   If ~(x < 2 * (m * z)),
   Then hop m (x,y,z) = (x - 2 * m * z,y + m * x - m * m * z,z)    by hop_def
        windmill (hop m (x,y,z))
      = (x - 2 * m * z) ** 2 + 4 * (y + m * x - m * m * z) * z     by windmill_def
      = (x - 2 * m * z) ** 2 + (4 * z * (y + m * x) - 4 * z * m * m * z)        by LEFT_SUB_DISTRIB
      = (x - 2 * m * z) ** 2 + (4 * z * y + 4 * m * z * x - 4 * z * m * m * z)  by LEFT_ADD_DISTRIB
      = (x - 2 * m * z) ** 2 + 4 * z * y + 4 * m * z * x - 4 * z * m * m * z    by [1]
      = (x - 2 * m * z) ** 2 + 2 * (2 * m * z) * x + 4 * y * z - 4 * z * m * m * z
      = (2 * m * z) ** 2 + x ** 2 + 4 * z * y - 4 * z * m * m * z  by binomial_sub_sum, 2 * (m * z) <= x
      = 4 * m ** 2 * z ** 2 + x ** 2 + 4 * z * y - 4 * m ** 2 * z ** 2          by EXP_2, EXP_BASE_MULT
      = x ** 2 + 4 * z * y                                         by arithmetic
      = n                                                          by windmill_def
*)
Theorem hop_windmill:
  !m n x y z. ~square n /\ n = windmill (x,y,z) /\ m <= (x + SQRT n) DIV (2 * z) ==>
              n = windmill (hop m (x,y,z))
Proof
  rpt strip_tac >>
  `0 < y /\ 0 < z` by metis_tac[windmill_with_arms] >>
  `0 < y + m * x - m * m * z` by metis_tac[hop_arm] >>
  `4 * (m ** 2 * z ** 2) < 4 * (z * y) + 4 * (m * x * z)` by
  (`m * m * z < y + m * x` by decide_tac >>
  `4 * z * (m ** 2 * z) < 4 * z * (y + m * x)` by fs[] >>
  `4 * z * (m ** 2 * z) = 4 * (m ** 2 * z ** 2)` by simp[] >>
  decide_tac) >>
  rw[hop_def] >| [
    qabbrev_tac `n = windmill (x,y,z)` >>
    qabbrev_tac `zz = 2 * (m * z)` >>
    simp[windmill_def, LEFT_SUB_DISTRIB, LEFT_ADD_DISTRIB] >>
    `4 * (m * x * z) = 2 * zz * x` by simp[Abbr`zz`] >>
    `4 * (m * x * z) + (zz - x) ** 2 = zz ** 2 + x ** 2` by fs[GSYM binomial_sub_sum] >>
    `zz ** 2 = 4 * (m ** 2 * z ** 2)` by simp[EXP_BASE_MULT, Abbr`zz`] >>
    fs[windmill_def, Abbr`n`],
    qabbrev_tac `n = windmill (x,y,z)` >>
    qabbrev_tac `zz = 2 * (m * z)` >>
    simp[windmill_def, LEFT_SUB_DISTRIB, LEFT_ADD_DISTRIB] >>
    `4 * (m * x * z) = 2 * zz * x` by simp[Abbr`zz`] >>
    `4 * (m * x * z) + (x - zz) ** 2 = zz ** 2 + x ** 2` by fs[GSYM binomial_sub_sum] >>
    `zz ** 2 = 4 * (m ** 2 * z ** 2)` by simp[EXP_BASE_MULT, Abbr`zz`] >>
    fs[windmill_def, Abbr`n`]
  ]
QED

(* Idea: windmill defines the range of hopping. *)

(* Theorem: n = windmill (x,y,z) /\
            0 < 2 * m * z - x /\ 0 < y + m * x - m * m * z ==>
            x DIV (2 * z) < m /\ m <= (x + SQRT n) DIV (2 * z) *)
(* Proof:
   Note 0 < 2 * m * z - x
    ==> 0 < z                      by MULT_0, SUB_0
    and x < m * (2 * z)            by inequality
    ==> x DIV (2 * z) < m          by DIV_LT_X, 0 < z

   Also 0 < y + m * x - m * m * z  (without ~square n)
    ==> m * m * z < y + m * x                              by inequality
    ==> 4 * z * (m * m * z) < 4 * z * (y + m * x)          by LT_MULT_LCANCEL, 0 < z
    ==> 4 * z * (m * m * z) < 4 * z * y + 4 * z * m * x    by LEFT_ADD_DISTRIB
    ==>    (2 * m * z) ** 2 < 4 * z * y + 4 * z * m * x    by EXP_BASE_MULT
    ==> x ** 2 + (2 * m * z) ** 2 < x ** 2 + 4 * z * y + 4 * z * m * x   by inequality
    ==> (2 * m * z) ** 2 + x ** 2 < n + 4 * z * m * x      by windmill_def
    ==> (2 * m * z - x) ** 2 + 2 * (2 * m * z) * x < n + 4 * z * m * x   by binomial_sub_sum, x < 2 * m * y
    ==> (2 * m * z - x) ** 2 < n                           by inequality
    ==>       2 * m * z - x <= SQRT n                      by SQRT_LT, SQRT_OF_SQ
    ==>       2 * m * z <= x + SQRT n                      by inequality
    ==>               m <= (x + SQRT n) DIV (2 * z)        by X_LE_DIV, 0 < z
*)
Theorem hop_range:
  !m n x y z. n = windmill (x,y,z) /\
              0 < 2 * m * z - x /\ 0 < y + m * x - m * m * z ==>
              x DIV (2 * z) < m /\ m <= (x + SQRT n) DIV (2 * z)
Proof
  ntac 6 strip_tac >>
  `0 < z` by metis_tac[NOT_ZERO, MULT_0, SUB_0, DECIDE``~(0 < 0)``] >>
  strip_tac >-
  fs[DIV_LT_X] >>
  `m * m * z < y + m * x` by decide_tac >>
  `4 * z * (m * m * z) < 4 * z * (y + m * x)` by fs[] >>
  `4 * z * (m * m * z) = (2 * m * z) ** 2` by simp[EXP_BASE_MULT] >>
  `4 * z * (y + m * x) = 4 * z * y + 4 * m * x * z` by simp[] >>
  `n = x ** 2 + 4 * y * z` by simp[windmill_def] >>
  `(2 * m * z) ** 2 + x ** 2 < n + 4 * m * x * z` by decide_tac >>
  `(2 * m * z) ** 2 + x ** 2 = (2 * m * z - x) ** 2 + 4 * m * x * z` by simp[GSYM binomial_sub_sum] >>
  `(2 * m * z - x) ** 2 < n` by decide_tac >>
  `(2 * m * z - x) <= SQRT n` by metis_tac[SQRT_LT, SQRT_OF_SQ] >>
  `m * (2 * z) <= x + SQRT n` by decide_tac >>
  simp[X_LE_DIV]
QED

(* Idea: the range of hopping is defined by being a windmill. *)

(* Theorem: ~square n /\ n = windmill (x,y,z) ==>
            (0 < 2 * m * z - x /\ 0 < y + m * x - m * m * z <=>
             0 < z /\ x DIV (2 * z) < m /\ m <= (x + SQRT n) DIV (2 * z)) *)
(* Proof:
   If part: 0 < 2 * m * z - x /\ 0 < y + m * x - m * m * z ==>
            0 < z /\ x DIV (2 * z) < m /\ m <= (x + SQRT n) DIV (2 * z)
      Note 0 < 2 * m * z - x ==> 0 < z         by MULT_0, SUB_0
       and x DIV (2 * z) < m                   by hop_range
       and m <= (x + SQRT n) DIV (2 * z)       by hop_range

   Only-if part: 0 < z /\ x DIV (2 * z) < m /\ m <= (x + SQRT n) DIV (2 * z) ==>
                 0 < 2 * m * z - x /\ 0 < y + m * x - m * m * z
      Note x DIV (2 * z) < m
       ==> 0 < 2 * (m * z) - x                 by hop_mind
       and m <= (x + SQRT n) DIV (2 * z)
       ==> 0 < y + m * x - m * m * z           by hop_arm
*)
Theorem hop_range_iff:
  !m n x y z. ~square n /\ n = windmill (x,y,z) ==>
              (0 < 2 * m * z - x /\ 0 < y + m * x - m * m * z <=>
              0 < z /\ x DIV (2 * z) < m /\ m <= (x + SQRT n) DIV (2 * z))
Proof
  ntac 6 strip_tac >>
  rewrite_tac [EQ_IMP_THM] >>
  ntac 2 strip_tac >| [
    `0 < z` by metis_tac[NOT_ZERO, MULT_0, SUB_0, DECIDE``~(0 < 0)``] >>
    metis_tac[hop_range],
    metis_tac[hop_mind, hop_arm]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Matrices of ping, pong, pung and hop.                                     *)
(* ------------------------------------------------------------------------- *)

(*
ping_def |- !x y z. ping (x,y,z) = (x + 2 * y,y,z - y - x)
pong_def |- !x y z. pong (x,y,z) = (2 * z - x,z,x + y - z)
pung_def |- !x y z. pung (x,y,z) = (x - 2 * z,x + y - z,z)

The matrices:
ping  P = [[1,2,0],[0,1,0],[-1,-1,1]]  P^2 = [[1,4,0],[0,1,0],[-2,-4,1]]  same form P^m = [[1,2m,0],[0,1,0],[-m,-m*m,1]]
pong  Q = [[-1,0,2],[0,0,1],[1,1,-1]]  Q^2 = [[3,2,-4],[1,1,-1],[-2,-1,4]]
pung  R = [[1,0,-2],[1,1,-1],[0,0,1]]  R^2 = [[1,0,-4],[2,1,-4],[0,0,1]]  same form R^m = [[1,0,-2m],[m,1,-m*m],[0,0,1]]

Both P and R have Jordan forms (check in WolframAlpha), Q has diagonal form.
*)

(* Theorem: FUNPOW ping m (x,y,z) = (x + 2 * m * y, y, z - m * x - m * m * y) *)
(* Proof:
   By induction on m.
   Base: FUNPOW ping 0 (x,y,z) = (x + 2 * 0 * y,y,z - 0 * x - 0 * 0 * y)
        FUNPOW ping 0 (x,y,z)
      = (x,y,z)                                by FUNPOW_0
      = (x + 0, y, z - 0)                      by ADD_0, SUB_0
      = (x + 2 * 0 * y, y, z - 0 * x - 0 * 0 * y)
   Step: FUNPOW ping m (x,y,z) = (x + 2 * m * y,y,z - m * x - m * m * y) ==>
         FUNPOW ping (SUC m) (x,y,z) = (x + 2 * SUC m * y,y,z - SUC m * x - SUC m * SUC m * y)

        FUNPOW ping (SUC m) (x,y,z)
      = ping (FUNPOW ping m (x,y,z))                     by FUNPOW_SUC
      = ping (x + 2 * m * y,y,z - m * x - m * m * y)     by induction hypothesis
      = (x + 2 * m * y + 2 * y,y,z - m * x - m * m * y - y - (x + 2 * m * y))
                                                         by ping_def
      = (x + 2 * (m + 1) * y), y,                        by LEFT_ADD_DISTRIB
         z - (x * (m + 1) + y * (m + 1) ** 2))           by SUM_SQUARED
      = (x + 2 * SUC m * y, y, z - SUC m * x - SUC m * SUC m * y)
                                                         by ADD1, EXP_2
*)
Theorem ping_funpow:
  !m x y z. FUNPOW ping m (x,y,z) = (x + 2 * m * y, y, z - m * x - m * m * y)
Proof
  rpt strip_tac >>
  Induct_on `m` >-
  simp[] >>
  simp[FUNPOW_SUC, ping_def, ADD1] >>
  `(m + 1) ** 2 = m ** 2 + 2 * m + 1` by simp[SUM_SQUARED] >>
  fs[]
QED

(* Theorem: is_ping t ==> windmill t = windmill (ping t) *)
(* Proof:
     windmill (ping t)
   = windmill ((zagier o flip) t)  by zagier_flip_ping
   = windmill t                    by zagier_flip_windmill
*)
Theorem ping_windmill:
  !t. is_ping t ==> windmill t = windmill (ping t)
Proof
  metis_tac[zagier_flip_ping, zagier_flip_windmill]
QED

(* Theorem: is_pong t ==> windmill t = windmill (pong t) *)
(* Proof:
     windmill (pong t)
   = windmill ((zagier o flip) t)  by zagier_flip_pong
   = windmill t                    by zagier_flip_windmill
*)
Theorem pong_windmill:
  !t. is_pong t ==> windmill t = windmill (pong t)
Proof
  metis_tac[zagier_flip_pong, zagier_flip_windmill]
QED

(* Theorem: is_pung t ==> windmill t = windmill (pung t) *)
(* Proof:
     windmill (pung t)
   = windmill ((zagier o flip) t)  by zagier_flip_pung
   = windmill t                    by zagier_flip_windmill
*)
Theorem pung_windmill:
  !t. is_pung t ==> windmill t = windmill (pung t)
Proof
  metis_tac[zagier_flip_pung, zagier_flip_windmill]
QED

(* Theorem: (!j. j < m ==> is_ping (FUNPOW ping j t)) ==> windmill t = windmill (FUNPOW ping m t) *)
(* Proof:
   By induction on m.
   Base: (!j. j < 0 ==> is_ping (FUNPOW ping j t)) ==>
         windmill t = windmill (FUNPOW ping 0 t)
      Note FUNPOW ping 0 t = t                                 by FUNPOW_0
      Thus trivially true.
   Step: (!j. j < m ==> is_ping (FUNPOW ping j t)) ==> windmill (x,y,z) = windmill (FUNPOW ping m t)
     ==> (!j. j < SUC m ==> is_ping (FUNPOW ping j t)) ==> windmill (x,y,z) = windmill (FUNPOW ping (SUC m) t)
      Note !j. j < SUC m ==> is_ping (FUNPOW ping j t)
       <=> !j. (j < m \/ j = m) ==> is_ping (FUNPOW ping j t)  by arithmetic
       <=> is_ping (FUNPOW ping m (x,y,z)) /\
           !j. j < m ==> is_ping (FUNPOW ping j t)             by DISJ_IMP_THM
        windmill (FUNPOW ping (SUC m) t)
      = windmill (ping (FUNPOW ping m t))                      by FUNPOW_SUC
      = windmill (FUNPOW ping m t)                             by ping_windmill
      = windmill t                                             by induction hypothesis
*)
Theorem ping_funpow_windmill:
  !m t. (!j. j < m ==> is_ping (FUNPOW ping j t)) ==> windmill t = windmill (FUNPOW ping m t)
Proof
  rpt strip_tac >>
  Induct_on `m` >-
  simp[] >>
  strip_tac >>
  `!j. j < SUC m <=> (j < m \/ j = m)` by decide_tac >>
  `is_ping (FUNPOW ping m t) /\ !j. j < m ==> is_ping (FUNPOW ping j t)` by metis_tac[] >>
  fs[FUNPOW_SUC, ping_windmill]
QED

(* Theorem: (!j. j < m ==> is_pung (FUNPOW pung j t)) ==> windmill t = windmill (FUNPOW pung m t) *)
(* Proof:
   By induction on m.
   Base: (!j. j < 0 ==> is_pung (FUNPOW pung j t)) ==>
         windmill (x,y,z) = windmill (FUNPOW pung 0 t)
      Note FUNPOW pung 0 t = t                                 by FUNPOW_0
      Thus trivially true.
   Step: (!j. j < m ==> is_pung (FUNPOW pung j t)) ==>  windmill (x,y,z) = windmill (FUNPOW pung m t)
     ==> (!j. j < SUC m ==> is_pung (FUNPOW pung j t)) ==> windmill (x,y,z) = windmill (FUNPOW pung (SUC m) t)
      Note !j. j < SUC m ==> is_pung (FUNPOW pung j t)
       <=> !j. (j < m \/ j = m) ==> is_pung (FUNPOW pung j t)  by arithmetic
       <=> is_pung (FUNPOW pung m (x,y,z)) /\
           !j. j < m ==> is_pung (FUNPOW pung j t)             by DISJ_IMP_THM
        windmill (FUNPOW pung (SUC m) t)
      = windmill (pung (FUNPOW pung m t))                      by FUNPOW_SUC
      = windmill (FUNPOW pung m t)                             by pung_windmill
      = windmill t                                             by induction hypothesis
*)
Theorem pung_funpow_windmill:
  !m t. (!j. j < m ==> is_pung (FUNPOW pung j t)) ==> windmill t = windmill (FUNPOW pung m t)
Proof
  rpt strip_tac >>
  Induct_on `m` >-
  simp[] >>
  strip_tac >>
  `!j. j < SUC m <=> (j < m \/ j = m)` by decide_tac >>
  `is_pung (FUNPOW pung m t) /\ !j. j < m ==> is_pung (FUNPOW pung j t)` by metis_tac[] >>
  fs[FUNPOW_SUC, pung_windmill]
QED

(* Theorem: tik n /\ ~square n /\ n = windmill (x,y,z) /\
            (!j. j < m ==> is_pung (FUNPOW pung j (x,y,z))) ==>
            FUNPOW pung m (x,y,z) = (x - 2 * m * z, y + m * x - m * m * z, z) *)
(* Proof:
   By induction on m.
   Base: (!j. j < 0 ==> is_pung (FUNPOW pung j (x,y,z))) ==>
         FUNPOW pung 0 (x,y,z) = (x - 2 * 0 * z,y + 0 * x - 0 * 0 * z,z)
        FUNPOW pung 0 (x,y,z)
      = (x,y,z)                                by FUNPOW_0
      = (x - 0, y + 0, z)                      by ADD_0, SUB_0
      = (x - 2 * 0 * z,y + 0 * x - 0 * 0 * z, z)
   Step: (!j. j < m ==> is_pung (FUNPOW pung j (x,y,z))) ==>
         FUNPOW pung m (x,y,z) = (x - 2 * m * z,y + m * x - m * m * z,z) ==>
         (!j. j < SUC m ==> is_pung (FUNPOW pung j (x,y,z))) ==>
         FUNPOW pung (SUC m) (x,y,z) = (x - 2 * SUC m * z,y + SUC m * x - SUC m * SUC m * z,z)
      Note !j. j < SUC m ==> is_pung (FUNPOW pung j (x,y,z))
       <=> !j. (j < m \/ j = m) ==> is_pung (FUNPOW pung j (x,y,z))    by arithmetic
       <=> is_pung (FUNPOW pung m (x,y,z)) /\
           !j. j < m ==> is_pung (FUNPOW pung j (x,y,z))               by DISJ_IMP_THM
      Thus n = windmill (FUNPOW pung m (x,y,z))          by pung_funpow_windmill
      giving the conditions:
           0 < x - 2 * m * z /\
           0 < y + m * x - m ** 2 * z                    by windmill_mind_and_arms, EXP_2

        FUNPOW pung (SUC m) (x,y,z)
      = pung (FUNPOW pung m (x,y,z))                     by FUNPOW_SUC
      = pung (x - 2 * m * z,y + m * x - m * m * z,z)     by induction hypothesis
      = (x - 2 * m * z - 2 * z,x - 2 * m * z + (y + m * x - m * m * z) - z,z)
                                                         by pung_def
      = (x - 2 * (m + 1) * z),                           by LEFT_ADD_DISTRIB, by conditions
         y + (m + 1) * x - (m + 1) ** 2 * z, z)          by SUM_SQUARED
      = (x - 2 * SUC m * z,y + SUC m * x - SUC m * SUC m * z,z)    by ADD1, EXP_2
*)
Theorem pung_funpow:
  !n x y z m. tik n /\ ~square n /\ n = windmill (x,y,z) /\
              (!j. j < m ==> is_pung (FUNPOW pung j (x,y,z))) ==>
              FUNPOW pung m (x,y,z) = (x - 2 * m * z, y + m * x - m * m * z, z)
Proof
  rpt strip_tac >>
  Induct_on `m` >-
  simp[] >>
  strip_tac >>
  `!j. j < SUC m <=> (j < m \/ j = m)` by decide_tac >>
  `is_pung (FUNPOW pung m (x,y,z)) /\ !j. j < m ==> is_pung (FUNPOW pung j (x,y,z))` by metis_tac[] >>
  `n = windmill (FUNPOW pung m (x,y,z))` by simp[GSYM pung_funpow_windmill] >>
  `0 < x - 2 * m * z /\ 0 < y + m * x - m ** 2 * z` by metis_tac[windmill_mind_and_arms, ONE_NOT_0, EXP_2] >>
  simp[FUNPOW_SUC, pung_def, ADD1] >>
  `x - 2 * (m * z) + (y + m * x - m ** 2 * z) - z = (y + m * x - m ** 2 * z) + (x - 2 * (m * z)) - z` by decide_tac >>
  `_ = y + m * x + x - (m ** 2 * z + 2 * m * z + z)` by fs[] >>
  `(m + 1) ** 2 = m ** 2 + 2 * m + 1` by simp[SUM_SQUARED] >>
  rfs[]
QED

(* Idea: the pungs is equivalent to hop. *)

(* Theorem: tik n /\ ~square n /\ n = windmill t /\
             (!j. j < m ==> is_pung (FUNPOW pung j t)) ==> FUNPOW pung m t = hop m t *)
(* Proof:
   Let (x,y,z) = t,
       xx = x - 2 * m * z,
       yy = y + m * x - m * m * z.
   Then FUNPOW pung m (x,y,z)
      = (xx, yy, z)                            by pung_funpow
    and n = windmill (xx,yy,z)                 by pung_funpow_windmill
   Thus 0 < xx                                 by windmill_with_mind, tik n
     or 2 * m * z < x                          by SUB_LESS_0

        hop m (x,y,z)
      = (xx, yy, z)                            by hop_def, 2 * m * z < x
      = FUNPOW pung m (x,y,z)                  by above
*)
Theorem pung_funpow_by_hop:
  !n m t. tik n /\ ~square n /\ n = windmill t /\
          (!j. j < m ==> is_pung (FUNPOW pung j t)) ==> FUNPOW pung m t = hop m t
Proof
  simp[FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `windmill (x,y,z)` >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  `FUNPOW pung m (x,y,z) = (x - 2 * m * z,y + m * x - m * m * z,z)` by fs[pung_funpow] >>
  `n = windmill (FUNPOW pung m (x,y,z))` by metis_tac[pung_funpow_windmill] >>
  `0 < x - 2 * m * z` by metis_tac[windmill_with_mind, ONE_NOT_0] >>
  simp[hop_def]
QED

(* Idea: the pung-to-ping through pong is equivalent to hop. *)

(* Theorem: tik n /\ ~square n /\ n = windmill t /\ is_pong (FUNPOW pung q t) /\
            (!j. j < q ==> is_pung (FUNPOW pung j t)) ==>
            (FUNPOW ping p o pong o FUNPOW pung q) t = hop (p + q + 1) t *)
(* Proof:
   Let (x,y,z) = t,
       a = FUNPOW pung q (x,y,z),
       b = pong a,
       c = FUNPOW ping p b.
   The goal is to show: c = hop (p + (q + 1)) (x,y,z)

   Note a = FUNPOW pung q (x,y,z)
          = (x - 2 * q * z,
             y + q * x - q ** 2 * z, z)        by pung_funpow, EXP_2
    and n = windmill a                         by pung_funpow_windmill
    ==> 0 < x - 2 * q * z /\
        0 < y + q * x - q ** 2 * z             by windmill_mind_and_arms
     or 2 * q * z < x /\
        q ** 2 * z < y + q * x                 by inequality, [1]

   Note b = pong a
          = (2 * z - (x - 2 * q * z), z,
             x - 2 * q * z + (y + q * x - q ** 2 * z) - z,
                                               by pong_def
          = (2 * z + 2 * q * z - x, z,
             (y + q * x - q ** 2 * z) + (x - 2 * q * z) - z)
                                               by SUB_SUB, [1]
          = (2 * (q + 1) * z - x, z,
             y + (q + 1) * x - (q ** 2 + 2 * q + 1) * z)
                                               by RIGHT_ADD_DISTRIB
          = (2 * (q + 1) * z - x, z,
             y + (q + 1) * x - (q + 1) ** 2 * z)
                                               by SUM_SQUARED
    and n = windmill b                         by pong_windmill
    ==> 0 < 2 * (q + 1) * z - x /\
        0 < y + (q + 1) * x - (q + 1) ** 2 * z by windmill_mind_and_arms
     or x < 2 * (q + 1) * z /\
        (q + 1) ** 2 * z < y + (q + 1) * x     by inequality, [2]

     FUNPOW ping p o pong o FUNPOW pung q (x,y,z)
   = FUNPOW ping p (pong (FUNPOW pung q (x,y,z)))      by composition
   = FUNPOW ping p b                                   by above

   If p = 0,
     FUNPOW ping 0 b
   = b                                                 by FUNPOW_0
   = (2 * (q + 1) * z - x, z, y + (q + 1) * x - (q + 1) ** 2 * z)
   = hop (0 + q + 1) (x,y,z)                           by hop_def

   If 0 < p,
   Then p * x  < 2 * p * (q + 1) * z                   by LT_MULT_LCANCEL, [3]

     c
   = FUNPOW ping p b
   = (2 * (q + 1) * z - x + 2 * p * z, z,
      y + (q + 1) * x - (q + 1) ** 2 * z - p * (2 * (q + 1) * z - x) - p ** 2 * z)
                                                       by ping_funpow, EXP_2
   = (2 * (q + 1) * z + 2 * p * z - x, z,
      y + (q + 1) * x + p x - ((q + 1) ** 2 + 2 * p * (q + 1) + p ** 2) * z,
                                                       by arithmetic, [2][3]
   = (2 * (p + q + 1) * z - x, z,
      y + (p + q + 1) * x - ((q + 1) ** 2 + 2 * (q + 1) * p + p ** 2) * z,
                                                       by RIGHT_ADD_DISTRIB
   = (2 * (p + q + 1) * z - x, z,
      y + (p + q + 1) * x - (p + q + 1) ** 2 * z)      by SUM_SQUARED

    Now 0 < 2 * (q + 1) * z - x                by windmill_mind_and_arms
    and 2 * (p + (q + 1)) * z - x = 2 * p * z + (2 * (q + 1) * z - x)
                                               by 0 < 2 * (q + 1) * z - x
   Thus 0 < 2 * (p + (q + 1)) * z - x          by inequality
   Thus c = hop (p + q + 1) (x,y,z)            by hop_def
*)
Theorem pung_to_ping_by_hop:
  !n t p q. tik n /\ ~square n /\ n = windmill t /\ is_pong (FUNPOW pung q t) /\
            (!j. j < q ==> is_pung (FUNPOW pung j t)) ==>
            (FUNPOW ping p o pong o FUNPOW pung q) t = hop (p + q + 1) t
Proof
  simp[FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `windmill (x,y,z)` >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  qabbrev_tac `a = FUNPOW pung q (x,y,z)` >>
  qabbrev_tac `b = pong a` >>
  qabbrev_tac `c = FUNPOW ping p b` >>
  `a = (x - 2 * q * z, y + q * x - q ** 2 * z, z)` by fs[pung_funpow, Abbr`a`] >>
  `n = windmill a` by simp[GSYM pung_funpow_windmill, Abbr`a`] >>
  `b = (2 * (q + 1) * z - x, z, y + (q + 1) * x - (q + 1) ** 2 * z)` by
  (fs[pong_def, Abbr`b`] >>
  `0 < x - 2 * (q * z) /\ 0 < y + q * x - q ** 2 * z` by metis_tac[windmill_mind_and_arms, ONE_NOT_0] >>
  simp[SUM_SQUARED]) >>
  `n = windmill b` by simp[pong_windmill, Abbr`b`] >>
  `c = (2 * (p + (q + 1)) * z - x, z, y + (p + (q + 1)) * x - (p + (q + 1)) ** 2 * z)` by
    (`p = 0 \/ 0 < p` by decide_tac >-
  simp[Abbr`c`] >>
  qabbrev_tac `qq = q + 1` >>
  fs[ping_funpow, Abbr`c`] >>
  `0 < 2 * (qq * z) - x /\ 0 < y + qq * x - qq ** 2 * z` by metis_tac[windmill_mind_and_arms, ONE_NOT_0] >>
  rfs[] >>
  `0 < p * (2 * (qq * z) - x)` by simp[] >>
  `0 < p * 2 * (qq * z) - p * x` by decide_tac >>
  `y + qq * x - (p * (2 * (qq * z) - x) + (p ** 2 * z + qq ** 2 * z)) = y + qq * x - (p ** 2 * z + qq ** 2 * z + p * (2 * (qq * z) - x))` by simp[] >>
  `_ = y + qq * x + p * x - (p ** 2 * z + qq ** 2 * z + 2 * p * qq * z)` by rfs[] >>
  `_ = y + (p + qq) * x - (p ** 2 + qq ** 2 + 2 * p * qq) * z` by rfs[] >>
  rfs[SUM_SQUARED]
  ) >>
  `0 < 2 * (q + 1) * z - x` by metis_tac[windmill_mind_and_arms, ONE_NOT_0] >>
  `0 < 2 * (p + (q + 1)) * z - x` by decide_tac >>
  simp[hop_def]
QED

(* Theorem: 0 < z /\ m < x DIV (2 * z) ==> is_pung (hop m (x,y,z)) *)
(* Proof:
   With m < x DIV (2 * z),
        hop m (x,y,z) = (x - 2 * m * z,y + m * x - m * m * z,z)
                                               by hop_alt
   Note m < x DIV (2 * z)
    <=> 2 * (m + 1) * z <= x                   by X_LT_DIV, 0 < z
    ==> 2 * m * z <= x                         by inequality
    and 2 * (m + 1) * z - x = 0                by arithmetic
   Now 2 * z - (x - 2 * m * z)
     = 2 * (m + 1) * z - x = 0                 by above
   Thus is_pung (hop m (x,y,z))                by is_pung_alt
*)
Theorem hop_over_pung:
  !m x y z. 0 < z /\ m < x DIV (2 * z) ==> is_pung (hop m (x,y,z))
Proof
  rpt strip_tac >>
  `0 < 2 * z` by decide_tac >>
  `2 * (m + 1) * z <= x` by fs[X_LT_DIV] >>
  fs[hop_alt, is_pung_alt]
QED

(* Theorem: 0 < z /\ m = x DIV (2 * z) ==> ~is_pung (hop m (x,y,z) *)
(* Proof:
   With m = x DIV (2 * z),
        hop m (x,y,z) = (x - 2 * m * z,y + m * x - m * m * z,z)
                                               by hop_alt
   Note 2 * m * z
      = (x DIV (2 * z)) * (2 * z) <= x         by DIV_MULT_LE
     so 2 * z - (x - 2 * m * z)
      = 2 * (m + 1) * z - x                    by SUB_SUB, 2 * m * z <= x

    Now x DIV (2 * z) <= m
    ==> x DIV (2 * z) < m + 1
    <=> x < 2 * (m + 1) * z                    by DIV_LT_X, 0 < z
    <=> 0 < 2 * (m + 1) * z - x                by inequality
   Thus 2 * (m + 1) * z - x <> 0               by NOT_ZERO
    ==> ~is_pung (hop m (x,y,z))               by is_pung_alt
*)
Theorem hop_beyond_pung:
  !m x y z. 0 < z /\ m = x DIV (2 * z) ==> ~is_pung (hop m (x,y,z))
Proof
  rpt strip_tac >>
  `~(x DIV (2 * z) < m)` by decide_tac >>
  qabbrev_tac `X = (m = x DIV (2 * z))` >>
  rfs[hop_alt] >>
  fs[] >>
  qunabbrev_tac `X` >>
  `0 < 2 * z` by decide_tac >>
  `m * (2 * z) <= x` by metis_tac[DIV_MULT_LE] >>
  `2 * z - (x - 2 * (m * z)) = 2 * (m + 1) * z - x` by decide_tac >>
  `x DIV (2 * z) < m + 1` by decide_tac >>
  `x < 2 * (m + 1) * z` by rfs[DIV_LT_X] >>
  fs[is_pung_alt]
QED

(* ------------------------------------------------------------------------- *)
(* Hopping Algorithm                                                         *)
(* ------------------------------------------------------------------------- *)

(* To ensure hop with stay as a windmill, the conditions from hop_range are:
   x DIV (2 * z) < m /\ m <= (x + SQRT n) DIV (2 * z)
   which can be taken as (x + k) DIV (2 * z)
   with 0 < k <= SQRT n, seems integer 0 <= k <= SQRT n is good.
*)

(* Define the step function *)
Definition step_def:
   step k (x,y,z) = (x + k) DIV (2 * z)  (* depends on only x, z, not y *)
End
(* the parameter k is taken from the caller, the hopping. *)

(* Define the hopping function *)
Definition hopping_def:
   hopping k t = hop (step k t) t
End
(* the parameter k = SQRT n is taken from the caller, two_sq_hop. *)

(* Define two_squares algorithm with hopping *)
Definition two_sq_hop_def:
   two_sq_hop n =  WHILE ($~ o found) (hopping (SQRT n)) (1,n DIV 4,1)
End
(* Use (1,n DIV 4,1) rather than (1,1,n DIV 4), so path starts with a non-ping. *)

(* The map: mind (x,y,z) gives the mind of a windmill.

mind_def  |- !x y z. mind (x,y,z) = if x < y - z then x + 2 * z else if x < y then 2 * y - x else x

Zagier map preserves the mind;
mind_zagier_eqn |- !x y z. mind (zagier (x,y,z)) = mind (x,y,z)

Generally, flip map changes the mind:
EVAL ``mind (flip (x,y,z))``;
|- mind (flip (x,y,z)) = if x < z - y then x + 2 * y else if x < z then 2 * z - x else x

But  mind (7,1,3) = 7 = mind (7,3,1), so sometimes flip does not change the mind.
Thus, when  mind t = mind (flip t), the triple t is a node, and the pair (t, flip t) share the same mind.
These nodes in (mill n) are close to the hopping points of the improved algorithm.

Part of the reason is due to the map   phi_m = F_1^{m} H = H F_3^{m}, with m = (x + SQRT n) DIV (2 * y) when applied to t = (x,y,z).
hop_def         |- !m x y z. hop m (x,y,z) = (2 * m * y - x,z + m * x - m * m * y,y)
step_def        |- !k x y. step k (x,y) = (x + k) DIV (2 * y)
hopping_def     |- !k x y z. hopping k (x,y,z) = hop (step k (x,y)) (x,y,z)
two_sq_hop_def  |- !n. two_sq_hop n = WHILE ($~ o found) (hopping (SQRT n)) (1,1,n DIV 4)

> EVAL ``two_sq_hop 5``; = (1,1,1): thm
> EVAL ``two_sq_hop 13``; = (3,1,1): thm
> EVAL ``two_sq_hop 17``; = (1,2,2): thm
> EVAL ``two_sq_hop 29``; = (5,1,1): thm
> EVAL ``two_sq_hop 37``; = (1,3,3): thm
> EVAL ``two_sq_hop 41``; = (5,2,2): thm
> EVAL ``two_sq_hop 53``; = (7,1,1): thm
> EVAL ``two_sq_hop 61``; = (5,3,3): thm
> EVAL ``two_sq_hop 73``; = (3,4,4): thm
> EVAL ``two_sq_hop 89``; = (5,4,4): thm
> EVAL ``two_sq_hop 97``; = (9,2,2): thm
> EVAL ``two_sq_hop 1277``; = (11,17,17): thm (reduces from 23 steps to 5 hops)

> EVAL ``two_sq_hop 773``; = (17,11,11): thm
> EVAL ``two_sq_hop 797``; = (11,13,13): thm
> EVAL ``two_sq_hop 977``; = (31,2,2): thm
> EVAL ``two_sq_hop 997``; = (31,3,3): thm
> EVAL ``two_sq_hop 1801``; = (35,12,12): thm   (reduces from 132 steps to 33 hops)
> EVAL ``two_sq_hop 1933``; = (13,21,21): thm

*)

(* Theorem: step 0 (x,y,z) = x DIV (2 * z) *)
(* Proof:
     step 0 (x,y,z)
   = (x + 0) DIV (2 * z)       by step_def
   = x DIV (2 * z)             by ADD_0
*)
Theorem step_0:
  !x y z. step 0 (x,y,z) = x DIV (2 * z)
Proof
  simp[step_def]
QED

(* Theorem: step (SQRT n) (x,y,z) = (x + SQRT n) DIV (2 * z) *)
(* Proof: by step_def. *)
Theorem step_sqrt:
  !n x y z. step (SQRT n) (x,y,z) = (x + SQRT n) DIV (2 * z)
Proof
  simp[step_def]
QED

(*

EVAL ``let n = 61 in (SQRT n, (1,n DIV 4,1))``; = (7,1,15,1)
EVAL ``hopping 7 (1,15,1)``; = (7,1,3)
EVAL ``hopping 7 (7,1,3)``; = (5,3,3)
EVAL ``FUNPOW (hopping 7) 1 (1,15,1)``; = (7,1,3)
EVAL ``FUNPOW (hopping 7) 2 (1,15,1)``; = (5,3,3)
*)

(* ------------------------------------------------------------------------- *)
(* Hopping by step 0.                                                        *)
(* ------------------------------------------------------------------------- *)

(*
Note:
step_0  |- !x y z. step 0 (x,y,z) = x DIV (2 * z)

hopping 0 (x,y,z) = hop (step 0 (x,y,z)) (x,y,z)

This corresponds to the hopping over pungs, reaching pong.
*)

(* Theorem: 0 < z /\ m < step 0 (x,y,z) ==> is_pung (hop m (x,y,z)) *)
(* Proof: by step_0, hop_over_pung. *)
Theorem hop_step_0_over_pung:
  !m x y z. 0 < z /\ m < step 0 (x,y,z) ==> is_pung (hop m (x,y,z))
Proof
  simp[step_0, hop_over_pung]
QED

(* Theorem: 0 < z /\ m = step 0 (x,y,z) ==> ~is_pung (hop m (x,y,z)) *)
(* Proof: by step_0, hop_beyond_pung. *)
Theorem hop_step_0_beyond_pung:
  !m x y z. 0 < z /\ m = step 0 (x,y,z) ==> ~is_pung (hop m (x,y,z))
Proof
  simp[step_0, hop_beyond_pung]
QED

(* Therefore,
If is_ping (x,y,z), step 0 (x,y,z) = 0, as there is no pung to skip.
If is_pong (x,y,z), step 0 (x,y,z) = 0, no pung to skip.
If is_pung (x,y,z), step 0 (x,y,z) <> 0, can be 1, 2, 3, .... at least one to skip.
*)

(* Theorem: 0 < z ==> (step 0 (x,y,z) = 0 <=> ~is_pung (x,y,z)) *)
(* Proof:
       is_pung (x,y,z)
   <=> 2 * z - x = 0           by is_pung_alt
   <=> 2 * z <= x              by SUB_EQ_0
   <=>     1 <= x DIV (2 * z)  by X_LE_DIV
   <=>     0 < x DIV (2 * z)   by LESS_EQ
   <=>     0 < step 0 (x,y,z)  by step_0
   <=>    step 0 (x,y,z) <> 0  by NOT_ZERO
   Thus step 0 (x,y,z) = 0 <=> ~is_pung (x,y,z)    by contrapositive
*)
Theorem step_0_eq_0:
  !x y z. 0 < z ==> (step 0 (x,y,z) = 0 <=> ~is_pung (x,y,z))
Proof
  rpt strip_tac >>
  `0 < 2 * z` by decide_tac >>
  `is_pung (x,y,z) <=> 2 * z <= x` by simp[is_pung_alt] >>
  `_ = (1 <= x DIV (2 * z))` by fs[X_LE_DIV] >>
  `_ = (1 <= step 0 (x,y,z))` by simp[step_0] >>
  `_ = (step 0 (x,y,z) <> 0)` by decide_tac >>
  metis_tac[]
QED

(* Theorem: 0 < z /\ is_ping (x,y,z) ==> step 0 (x,y,z) = 0 *)
(* Proof: by ping_not_pung, step_0_eq_0. *)
Theorem step_0_of_ping:
  !x y z. 0 < z /\ is_ping (x,y,z) ==> step 0 (x,y,z) = 0
Proof
  simp[ping_not_pung, step_0_eq_0]
QED

(* Theorem: 0 < z /\ is_pong (x,y,z) ==> step 0 (x,y,z) = 0 *)
(* Proof: by pong_not_pung, step_0_eq_0. *)
Theorem step_0_of_pong:
  !x y z. 0 < z /\ is_pong (x,y,z) ==> step 0 (x,y,z) = 0
Proof
  simp[pong_not_pung, step_0_eq_0]
QED

(* Theorem: 0 < z /\ is_pung (x,y,z) ==> 0 < step 0 (x,y,z) *)
(* Proof: by step_0_eq_0, NOT_ZERO. *)
Theorem step_0_of_pung:
  !x y z. 0 < z /\ is_pung (x,y,z) ==> 0 < step 0 (x,y,z)
Proof
  metis_tac[step_0_eq_0, NOT_ZERO]
QED

(*
For this range, m <= step 0 (x,y,z) = x DIV (2 * z),
which is ~(x DIV (2 * z) < m),
hop m (x,y,z) = (x - 2 * m * z,y + m * x - m * m * z,z) = (xx,yy,zz)
that is,
xx decreases with m linearly, starting from x.
yy varies with m quadratically, first increases, then decreases, starting from y.
zz is always kept at original z, which is the focus.

Therefore, the discriminant (2 * zz - xx) for subsequent ping/pong/pung
only depends on xx, and increases linearly with m:
2 * zz - xx = 2 * z - (x - 2 * m * z) = 2 * (m + 1) * z - x
Initially, 2 * zz - xx = 2 * z - x is negative for pung,
but eventually this switches to positive, when pung becomes pong at m = step 0 (x,y,z).
*)

(* Theorem: let xx = x - 2 * m * z in xx - 2 * z = x - 2 * (m + 1) * z *)
(* Proof:
   Let xx = x - 2 * m * z.
     xx - 2 * z
   = x - 2 * m * z - 2 * z               by notation
   = x - (2 * m * z + 2 * z)             by SUB_RIGHT_SUB
   = x - 2 * z * (m + 1)                 by LEFT_ADD_DISTRIB
*)
Theorem hop_identity_1:
  !m x z. let xx = x - 2 * m * z in xx - 2 * z = x - 2 * (m + 1) * z
Proof
  simp[]
QED

(* Theorem: let xx = x - 2 * m * z in xx - 2 * z = x - 2 * (m + 1) * z *)
(* Proof:
   Let xx = x - 2 * m * z.
     2 * z - xx
   = 2 * z - (x - 2 * m * z)             by notation
   = 2 * z + 2 * m * z - x               by SUB_SUB, 0 < xx
   = 2 * z * (m + 1) - x                 by LEFT_ADD_DISTRIB
*)
Theorem hop_identity_2:
  !m x z. let xx = x - 2 * m * z in 0 < xx ==> 2 * z - xx = 2 * (m + 1) * z - x
Proof
  simp[]
QED

(* Theorem: let xx = x - 2 * m * z; yy = y + m * x - m ** 2 * z in 0 < xx /\ 0 < yy ==>
            xx + yy - z = y + (m + 1) * x - (m + 1) ** 2 * z *)
(* Proof:
   Let xx = x - 2 * m * z,
       yy = y + m * x - m ** 2 * z.
     xx + yy - z
   = x - 2 * m * z + (y + m * x - m ** 2 * z) - z      by notation
   = (y + m * x - m ** 2 * z) + x - 2 * m * z - z      by SUB_LEFT_ADD, 0 < xx
   = y + (m * x + x) - (m ** 2 * z + 2 * m * z + z)    by SUB_RIGHT_SUB, 0 < yy
   = y + (m + 1) * x - (m ** 2 + 2 * m + 1) * z        by RIGHT_ADD_DISTRIB
   = y + m * x - (m + 1) ** 2 * z                      by SUM_SQUARED
*)
Theorem hop_identity_3:
  !m x y z. let xx = x - 2 * m * z; yy = y + m * x - m ** 2 * z in 0 < xx /\ 0 < yy ==>
            xx + yy - z = y + (m + 1) * x - (m + 1) ** 2 * z
Proof
  rw_tac std_ss[] >>
  `xx + yy - z = y + m * x - m ** 2 * z + x - 2 * (m * z) - z` by simp[Abbr`xx`, Abbr`yy`] >>
  `_ = y + m * x + x - m ** 2 * z - 2 * (m * z) - z` by rfs[Abbr`yy`] >>
  `_ = y + (m + 1) * x - (m ** 2 + 2 * m + 1) * z` by decide_tac >>
  simp[SUM_SQUARED]
QED

(* Theorem: let xx = 2 * m * z - x; yy = y + m * x - m ** 2 * z in 0 < xx /\ 0 < yy ==>
            yy - z - xx = y + (m + 1) * x - (m + 1) ** 2 * z *)
(* Proof:
   Let xx = 2 * m * z - x,
       yy = y + m * x - m ** 2 * z.
     yy - z - xx
   = (y + m * x - m ** 2 * z) - z - (2 * m * z - x)    by notation
   = (y + m * x - m ** 2 * z) + x - 2 * m * z - z      by SUB_LEFT_ADD, 0 < xx
   = y + (m * x + x) - (m ** 2 * z + 2 * m * z + z)    by SUB_RIGHT_SUB, 0 < yy
   = y + (m + 1) * x - (m ** 2 + 2 * m + 1) * z        by RIGHT_ADD_DISTRIB
   = y + m * x - (m + 1) ** 2 * z                      by SUM_SQUARED
*)
Theorem hop_identity_4:
  !m x y z. let xx = 2 * m * z - x; yy = y + m * x - m ** 2 * z in 0 < xx /\ 0 < yy ==>
            yy - z - xx = y + (m + 1) * x - (m + 1) ** 2 * z
Proof
  rw_tac std_ss[] >>
  `yy - z - xx = y + m * x - m ** 2 * z + x - 2 * (m * z) - z` by simp[Abbr`xx`, Abbr`yy`] >>
  `_ = y + m * x + x - m ** 2 * z - 2 * (m * z) - z` by rfs[Abbr`yy`] >>
  `_ = y + (m + 1) * x - (m ** 2 + 2 * m + 1) * z` by decide_tac >>
  simp[SUM_SQUARED]
QED

(* Idea: before hopping to a pong, hopping is just (FUNPOW pung j). *)

(* Theorem: tik n /\ ~square n /\ n = windmill t /\ m <= step 0 t ==> hop m t = FUNPOW pung m t *)
(* Proof:
   Let (x,y,z) = t                             by FORALL_PROD
   Note m <= x DIV (2 * z)                     by step_0

   By complete induction on m.
   This is to show: !j. j < m /\ j <= x DIV (2 * z) ==> hop j (x,y,z) = FUNPOW pung j (x,y,z)
                ==> m <= x DIV (2 * z) ==> hop m (x,y,z) = FUNPOW pung m (x,y,z)

   If m = 0,
        FUNPOW pung 0 (x,y,z)
      = (x,y,z)                                by FUNPOW_0
      = hop 0 (x,y,z)                          by hop_0

   Otherwise, 0 < m.
      Let n = windmill (x,y,z).
      Then 0 < z                               by windmill_with_arms, ~square n
      Let j = m - 1,
          xx = x - 2 * j * z,
          yy = y + j * x - j ** 2 * z.
      Then m = SUC j, j < m <= x DIV (2 * z)   by ADD1

      Note hop j (x,y,z) = (xx,yy,z)           by hop_alt, j < x DIV (2 * z)
       and m <= (x + SQRT n) DIV (2 * z)       by DIV_LE_MONOTONE
       ==> n = windmill (xx,yy,z)              by hop_windmill
        so 0 < xx                              by windmill_with_mind, tik n
       and 0 < yy                              by windmill_with_arms, ~square n

           FUNPOW pung m (x,y,z)
         = pung (FUNPOW pung j (x,y,z))        by FUNPOW_SUC
         = pung (hop j (x,y,z))                by induction hypothesis
         = pung (xx,yy,z)                      by above
         = (xx - 2 * z,xx + yy - z,z)          by pung_def
         = (x - 2 * (j + 1) * z,                         by hop_identity_1
            y + (j + 1) * x - (j + 1) ** 2 * z, z)       by hop_identity_3
         = (x - 2 * m * z, y + m * x - m ** 2 * z, z)    by m = j + 1
         = hop m (x,y,z)                       by hop_alt, m <= x DIV (2 * z)
*)
Theorem hop_step_0_before_pong:
  !n m t. tik n /\ ~square n /\ n = windmill t /\ m <= step 0 t ==> hop m t = FUNPOW pung m t
Proof
  simp[FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `windmill (x,y,z)` >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  fs[step_0] >>
  completeInduct_on `m` >>
  strip_tac >>
  `m = 0 \/ 0 < m` by decide_tac >-
  simp[hop_0] >>
  last_x_assum (qspecl_then [`m-1`] strip_assume_tac) >>
  rfs[] >>
  `SUC (m - 1) = m /\ m - 1 < m /\ m = m - 1 + 1` by decide_tac >>
  qabbrev_tac `j = m - 1` >>
  qabbrev_tac `xx = x - 2 * j * z` >>
  qabbrev_tac `yy = y + j * x - j ** 2 * z` >>
  `0 < z` by metis_tac[windmill_with_arms] >>
  `hop j (x,y,z) = (xx,yy,z)` by fs[hop_alt, Abbr`xx`, Abbr`yy`] >>
  `0 < 2 * z` by decide_tac >>
  `x DIV (2 * z) <= (x + SQRT n) DIV (2 * z)` by simp[DIV_LE_MONOTONE] >>
  `j <= (x + SQRT n) DIV (2 * z)` by decide_tac >>
  `n = windmill (xx,yy,z)` by metis_tac[hop_windmill] >>
  `0 < xx` by metis_tac[windmill_with_mind, ONE_NOT_0] >>
  `0 < yy` by metis_tac[windmill_with_arms] >>
  `FUNPOW pung m (x,y,z) = pung (FUNPOW pung j (x,y,z))` by simp[GSYM FUNPOW_SUC] >>
  `_ = pung (hop j (x,y,z))` by fs[] >>
  `_ = pung (xx,yy,z)` by fs[] >>
  `_ = (xx - 2 * z,xx + yy - z,z)` by simp[pung_def] >>
  `_ = (x - 2 * m * z, y + m * x - m ** 2 * z, z)` by metis_tac[hop_identity_1, hop_identity_3] >>
  fs[hop_alt]
QED

(*
For n = 61,
u = (1,15,1), is_pong u.
step 0 u = 1 DIV (2 * 1) = 0 = m.
hop m u = hop 0 (1,15,1) = (1,15,1)
hop (m + 1) = hop 1 (1,15,1) = (1,1,15)
pong (1,15,1) = (1,1,15)

*)

(* Idea: at pong, the hop definition changes from one form to another.*)

(* Theorem: tik n /\ ~square n /\ n = windmill t /\ m = step 0 t ==> hop (m + 1) t = pong (hop m t) *)
(* Proof:
   Let (x,y,z) = t                             by FORALL_PROD
   Note m = x DIV (2 * z)                      by step_0
   Let n = windmill (x,y,z).
   Then 0 < z                                  by windmill_with_arms, ~square n
    and m <= (x + SQRT n) DIV (2 * z)          by DIV_LE_MONOTONE

   Let xx = x - 2 * m * z,
       yy = y + m * x - m ** 2 * z.
   Then hop m (x,y,z) = (xx,yy,z)              by hop_alt, x DIV (2 * z) = m

   Note n = windmill (xx,yy,z)                 by hop_windmill, m <= step (SQRT n) (x,y,z)
     so 0 < xx                                 by windmill_with_mind, tik n
    and 0 < yy                                 by windmill_with_arms, ~square n

        pong (hop m (x,y,z))
      = pong (xx,yy,z)                         by above
      = (2 * z - xx,z,xx + yy - z)             by pong_def
      = (2 * (m + 1) * z - x, z,               by hop_identity_2, 0 < xx
         y + (m + 1) * x - (m + 1) ** 2 * z)   by hop_identity_3, 0 < yy
      = hop (m + 1) (x,y,z)                    by hop_alt, x DIV (2 * z) < m + 1
*)
Theorem hop_step_0_at_pong:
  !n m t. tik n /\ ~square n /\ n = windmill t /\ m = step 0 t ==> hop (m + 1) t = pong (hop m t)
Proof
  simp[FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `windmill (x,y,z)` >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  qabbrev_tac `m = step 0 (x,y,z)` >>
  `m = x DIV (2 * z)` by simp[step_0, Abbr`m`] >>
  `0 < z` by metis_tac[windmill_with_arms] >>
  `0 < 2 * z` by decide_tac >>
  `m <= (x + SQRT n) DIV (2 * z)` by rfs[DIV_LE_MONOTONE] >>
  qabbrev_tac `xx = x - 2 * m * z` >>
  qabbrev_tac `yy = y + m * x - m ** 2 * z` >>
  `hop m (x,y,z) = (xx,yy,z)` by fs[hop_alt, Abbr`xx`, Abbr`yy`] >>
  `n = windmill (xx,yy,z)` by metis_tac[hop_windmill] >>
  `0 < xx` by metis_tac[windmill_with_mind, ONE_NOT_0] >>
  `0 < yy` by metis_tac[windmill_with_arms] >>
  `pong (hop m (x,y,z)) = pong (xx,yy,z)` by simp[] >>
  `_ = (2 * z - xx,z,xx + yy - z)` by simp[pong_def] >>
  `_ = (2 * (m + 1) * z - x,z,xx + yy - z)` by rfs[hop_identity_2, Abbr`xx`] >>
  `_ = (2 * (m + 1) * z - x,z,y + (m + 1) * x - (m + 1) ** 2 * z)` by metis_tac[hop_identity_3] >>
  `_ = (2 * (m + 1) * z - x,z,y + (m + 1) * x - (m + 1) * (m + 1) * z)` by metis_tac[EXP_2] >>
  fs[hop_alt]
QED

(* Idea: after hopping to a pong, further hopping is just (FUNPOW ping j). *)

(* Theorem: tik n /\ ~square n /\ n = windmill t /\ m = step 0 t /\ m + j < step (SQRT n) t ==>
            hop (m + 1 + j) t = FUNPOW ping j (hop (m + 1) t) *)
(* Proof:
   Let (x,y,z) = t,
       n = windmill (x,y,z),
       k = m + 1.
   Note m = x DIV (2 * z)                      by step_0
    and m + j < (x + SQRT n) DIV (2 * z)       by step_sqrt [1]
    and 0 < z                                  by windmill_with_arms, ~square n
   The goal is to show: hop (k + j) (x,y,z) = FUNPOW ping j (hop k (x,y,z))

   By complete induction on j.
   This is to show: !h. h < j /\ h + m < (x + SQRT n) DIV (2 * z) ==>
                        hop (k + h) (x,y,z) = FUNPOW ping h (hop k (x,y,z))
                 ==> j + m < (x + SQRT n) DIV (2 * z) ==>
                     hop (k + j) (x,y,z) = FUNPOW ping j (hop k (x,y,z))

   If j = 0,
        FUNPOW ping 0 (hop k (x,y,z))
      = hop k (x,y,z)                          by FUNPOW_0
      = hop (k + 0) (x,y,z)                    by ADD_0

   Otherwise, 0 < j.
      Let h = j - 1, then j = SUC h.
       so h < j /\ h + m < (x + SQRT n) DIV (2 * z)

      Let xx = 2 * (m + j) * z - x,
          yy = y + (m + j) * x - (m + j) ** 2 * z.
      Then hop (m + j) (x,y,z) = (xx,z,yy)     by hop_alt, m < m + j
       and m + j <= (x + SQRT n) DIV (2 * z)   by [1]
       ==> n = windmill (xx,z,yy)              by hop_windmill
      Thus 0 < xx                              by windmill_with_mind, tik n
       and 0 < yy                              by windmill_with_arms, ~square n

        FUNPOW ping j (hop k (x,y,z))
      = FUNPOW ping (SUC h) (hop k (x,y,z))    by j = SUC h
      = ping (FUNPOW ping h (hop k (x,y,z)))   by FUNPOW_SUC
      = ping (hop (k + h) (x,y,z))             by induction hypothesis
      = ping (hop (m + j) (x,y,z))             by k + h = m + 1 + j - 1 = m + j
      = ping (xx, z, yy)                       by above
      = (xx + 2 * z,z,yy - z - xx)             by ping_def
      = (2 * z * (m + j) - x + 2 * z, z, yy - z - xx)
      = (2 * z * (m + j + 1) - x, z,           by LEFT_ADD_DISTRIB
         y + (m + j + 1) * x - (m + j + 1) ** 2 * z)
                                               by hop_identity_4, 0 < xx, 0 < yy
      = hop (m + j + 1) (x,y,z)                by hop_alt, m + j + 1 <= (x + SQRT n) DIV (2 * z)
      = hop (k + j) (x,y,z)                    by k = m + 1
*)
Theorem hop_step_0_beyond_pong:
  !n m j t. tik n /\ ~square n /\ n = windmill t /\ m = step 0 t /\ m + j < step (SQRT n) t ==>
            hop (m + 1 + j) t = FUNPOW ping j (hop (m + 1) t)
Proof
  simp[FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `windmill (x,y,z)` >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  qabbrev_tac `m = step 0 (x,y,z)` >>
  fs[step_0, step_sqrt] >>
  completeInduct_on `j` >>
  strip_tac >>
  `j = 0 \/ 0 < j` by decide_tac >-
  simp[] >>
  last_x_assum (qspecl_then [`j-1`] strip_assume_tac) >>
  rfs[] >>
  `SUC (j - 1) = j` by decide_tac >>
  qabbrev_tac `h = j - 1` >>
  qabbrev_tac `k = m + 1` >>
  qabbrev_tac `xx = 2 * (j + m) * z - x` >>
  qabbrev_tac `yy = y + (j + m) * x - (j + m) ** 2 * z` >>
  `0 < z` by metis_tac[windmill_with_arms] >>
  `hop (j + m) (x,y,z) = (xx,z,yy)` by fs[hop_alt, Abbr`m`, Abbr`xx`, Abbr`yy`] >>
  `n = windmill (xx,z,yy)` by metis_tac[hop_windmill, LESS_IMP_LESS_OR_EQ] >>
  `0 < xx` by metis_tac[windmill_with_mind, ONE_NOT_0] >>
  `0 < yy` by metis_tac[windmill_with_arms] >>
  `FUNPOW ping j (hop k (x,y,z)) = ping (FUNPOW ping h (hop k (x,y,z)))` by metis_tac[FUNPOW_SUC] >>
  `_ = ping (xx,z,yy)` by fs[] >>
  `_ = (xx + 2 * z,z,yy - z - xx)` by simp[ping_def] >>
  `_ = (2 * z * (j + m) + 2 * z - x, z, yy - z - xx)` by simp[Abbr`xx`] >>
  `_ = (2 * (j + k) * z - x, z, yy - z - xx)` by simp[Abbr`k`] >>
  `_ = (2 * (j + k) * z - x, z, y + (j + m + 1) * x - (j + m + 1) ** 2 * z)` by metis_tac[hop_identity_4] >>
  fs[hop_alt, Abbr`k`]
QED

(* Theorem: tik n /\ ~square n /\ n = windmill t /\ m = step 0 t /\ m + j < step (SQRT n) t ==>
            hop (m + 1 + j) t = (FUNPOW ping j o pong o FUNPOW pung m) t *)
(* Proof:
     hop (m + 1 + j) t
   = FUNPOW ping j (hop (m + 1) t)             by hop_step_0_beyond_pong
   = FUNPOW ping j (pong (hop m t))            by hop_step_0_at_pong
   = FUNPOW ping j (pong (FUNPOW pung m t))    by hop_step_0_before_pong
   = (FUNPOW ping j o pong o FUNPOW pung m) t  by o_THM
*)
Theorem hop_step_0_around_pong:
  !n m j t. tik n /\ ~square n /\ n = windmill t /\ m = step 0 t /\ m + j < step (SQRT n) t ==>
            hop (m + 1 + j) t = (FUNPOW ping j o pong o FUNPOW pung m) t
Proof
  simp[hop_step_0_beyond_pong, hop_step_0_at_pong, hop_step_0_before_pong]
QED

(* Theorem: ~square n /\ n = windmill t /\ m < step 0 t ==> is_pung (hop m t) *)
(* Proof:
   Let (x,y,z) = t                 by FORALL_PROD
   Note 0 < z                      by windmill_with_arms, ~square n
    and m < x DIV (2 * z)          by step_0
     so is_pung (hop m (x,y,z))    by hop_over_pung
*)
Theorem hop_step_0_before_pong_is_pung:
  !n m t. ~square n /\ n = windmill t /\ m < step 0 t ==> is_pung (hop m t)
Proof
  simp[FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `windmill (x,y,z)` >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  fs[step_0] >>
  `0 < z` by metis_tac[windmill_with_arms] >>
  simp[hop_over_pung]
QED

(* Theorem: tik n /\ ~square n /\ n = windmill t /\ m = step 0 t /\ ~is_ping t ==> is_pong (hop m t) *)
(* Proof:
   Let (x,y,z) = t                 by FORALL_PROD
   Note 0 < z                      by windmill_with_arms, ~square n
    and m = x DIV (2 * z)          by step_0
   Let t = hop m (x,y,z).
   Note ~is_pung t                 by hop_beyond_pung

   If m = 0,
      Then t = hop 0 (x,y,z)
             = (x,y,z)             by hop_0
      Thus ~is_pung (x,y,z)        by above, t = (x,y,z)
       and ~is_ping (x,y,z)        by given
       ==> is_pong (x,y,z)         by triple_cases

   Otherwise, 0 < m.
      Let u = hop (m-1) (x,y,z).
      Then is_pung u               by hop_over_pung
       ==> ~is_ping (pung u)
           hop m (x,y,z)
         = FUNPOW pung m (x,y,z)   by hop_step_0_before_pong
         = pung (FUNPOW pung (m-1) (x,y,z))    by FUNPOW_SUC
         = pung (hop (m - 1) (x,y,z))          by hop_step_0_before_pong
         = pung u

      Thus ~is_ping t              by pung_next_not_ping
      With ~is_pung t              by given
       ==> is_pong t               by triple_cases
*)
Theorem hop_step_0_at_pong_is_pong:
  !n m t. tik n /\ ~square n /\ n = windmill t /\ m = step 0 t /\ ~is_ping t ==> is_pong (hop m t)
Proof
  simp[FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `windmill (x,y,z)` >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  qabbrev_tac `m = step 0 (x,y,z)` >>
  `m = x DIV (2 * z)` by simp[step_0, Abbr`m`] >>
  `0 < z` by metis_tac[windmill_with_arms] >>
  qabbrev_tac `t = hop m (x,y,z)` >>
  `~is_pung t` by fs[hop_beyond_pung, Abbr`t`] >>
  `m = 0 \/ 0 < m` by decide_tac >| [
    `t = (x,y,z)` by simp[hop_0, Abbr`t`] >>
    metis_tac[triple_cases],
    qabbrev_tac `u = hop (m - 1) (x,y,z)` >>
    `t = FUNPOW pung m (x,y,z)` by fs[hop_step_0_before_pong, Abbr`t`] >>
    `u = FUNPOW pung (m-1) (x,y,z)` by fs[hop_step_0_before_pong, Abbr`u`] >>
    `m = SUC (m - 1)` by decide_tac >>
    `t = pung u` by metis_tac[FUNPOW_SUC] >>
    `is_pung u` by fs[hop_over_pung, Abbr`u`] >>
    `~is_ping t` by rfs[pung_next_not_ping] >>
    metis_tac[triple_cases]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Hopping by step (SQRT n).                                                 *)
(* ------------------------------------------------------------------------- *)

(*
Note:
step_sqrt  |- !n x y z. step (SQRT n) (x,y,z) = (x + SQRT n) DIV (2 * z)

hopping (SQRT n) (x,y,z) = hop (step (SQRT n) (x,y,z)) (x,y,z)

This corresponds to the hopping after pong, over pings.

If is_ping (x,y,z), step (SQRT n) (x,y,z) = 0, there is no pungs to skip, no pong to stay, cannot see pings beyond.
If is_pong (x,y,z), step (SQRT n) (x,y,z) <> 0, itself is pong, hope to find some pings to skip.
If is_pung (x,y,z), step (SQRT n) (x,y,z) <> 9, there are pungs to skip, stay at a pong, maybe pings to skip.
*)

(* Theorem: 0 < z ==> (step (SQRT (windmill (x,y,z))) (x,y,z) = 0 <=> is_ping (x,y,z)) *)
(* Proof:
   Let n = windmill (x,y,z).
       is_ping (x,y,z)
   <=> SQRT n < 2 * z - x                      by is_ping_alt
   <=> x + SQRT n < 2 * z                      by SUB_LEFT_LESS
   <=> (x + SQRT n) DIV (2 * z) < 1            by DIV_LT_X
   <=>    step (SQRT n) (x,y,z) < 1            by step_sqrt
   <=>    step (SQRT n) (x,y,z) = 0            by inequality
*)
Theorem step_sqrt_eq_0:
  !x y z. 0 < z ==> (step (SQRT (windmill (x,y,z))) (x,y,z) = 0 <=> is_ping (x,y,z))
Proof
  rpt strip_tac >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  `0 < 2 * z` by decide_tac >>
  `is_ping (x,y,z) <=> x + SQRT n < 2 * z` by simp[is_ping_alt, Abbr`n`] >>
  `_ = ((x + SQRT n) DIV (2 * z) < 1)` by fs[DIV_LT_X] >>
  `_ = (step (SQRT n) (x,y,z) < 1)` by simp[step_sqrt] >>
  `_ = (step (SQRT n) (x,y,z) = 0)` by decide_tac >>
  simp[]
QED

(* Theorem: 0 < z /\ is_ping (x,y,z) ==> step (SQRT (windmill (x,y,z))) (x,y,z) = 0 *)
(* Proof: by step_sqrt_eq_0. *)
Theorem step_sqrt_of_ping:
  !x y z. 0 < z /\ is_ping (x,y,z) ==> step (SQRT (windmill (x,y,z))) (x,y,z) = 0
Proof
  simp[step_sqrt_eq_0]
QED

(* Theorem: 0 < z /\ is_pong (x,y,z) ==> 0 < step (SQRT (windmill (x,y,z))) (x,y,z) *)
(* Proof:
   Let n = windmill (x,y,z).
       is_pong (x,y,z)
   ==> 2 * z - x <= SQRT n                     by is_pong_alt
   <=> 2 * z <= x + SQRT n                     by SUB_RIGHT_LESS_EQ
   <=> 1 <= (x + SQRT n) DIV (2 * z)           by X_LE_DIV
   <=> 1 <= step (SQRT n) (x,y,z)              by step_sqrt
   <=> 0 < step (SQRT n) (x,y,z)               by inequality
   or simply by step_sqrt_eq_0, pong_not_ping.
*)
Theorem step_sqrt_of_pong:
  !x y z. 0 < z /\ is_pong (x,y,z) ==> 0 < step (SQRT (windmill (x,y,z))) (x,y,z)
Proof
  metis_tac[pong_not_ping, step_sqrt_eq_0, NOT_ZERO]
QED

(* Theorem: 0 < z /\ is_pung (x,y,z) ==> 0 < step (SQRT (windmill (x,y,z))) (x,y,z) *)
(* Proof: by pung_not_ping, step_sqrt_eq_0. *)
Theorem step_sqrt_of_pung:
  !x y z. 0 < z /\ is_pung (x,y,z) ==> 0 < step (SQRT (windmill (x,y,z))) (x,y,z)
Proof
  metis_tac[pung_not_ping, step_sqrt_eq_0, NOT_ZERO]
QED

(*
That's why hopping m (x,y,z) always starts with ~is_ping (x,y,z),

                   step 0 (x,y,z)            step (SQRT n) (x,y,z)
is_ping (x,y,z)       = 0                       = 0
is_pong (x,y,z)       = 0                       > 0
is_pung (x,y,z)       > 0                       > 0
*)

(* Idea: for n = windmill (x,y,z), step 0 (x,y,z) <= step (SQRT n) (x,y,z). *)

(* Theorem: 0 < z ==> step 0 (x,y,z) <= step (SQRT (windmill (x,y,z))) (x,y,z) *)
(* Proof:
   Let n = windmill (x,y,z).
   Note x <= x + SQRT n                        by inequality
   Thus step 0 (x,y,z)
      = x DIV (2 * z)                          by step_0
     <= (x + SQRT n) DIV (2 * z)               by DIV_LE_MONOTONE
      = step (SQRT n) (x,y,z)                  by step_sqrt
*)
Theorem step_0_le_step_sqrt:
  !x y z. 0 < z ==> step 0 (x,y,z) <= step (SQRT (windmill (x,y,z))) (x,y,z)
Proof
  rpt strip_tac >>
  `0 < 2 * z` by decide_tac >>
  simp[step_0, step_sqrt, DIV_LE_MONOTONE]
QED

(*
Q: For a pung (x,y,z), looks like x DIV (2 * z) < (x + SQRT n) DIV (2 * z) always, why?

For example, when n = 97, SQRT n = 9. The two will be equal if (2 * z) > SQRT n = 9; e.g. when z = 5.
However, for a windmill, 97 = n = x ** 2 + 2 * 4 * y * z.
The smallest x = 1, so 4 * y * z = 96, or y * z = 16. Max z is only 4, not 5!

Let h = SQRT n.

          x DIV (2 * z) < (x + h) DIV (2 * z)
      <=> (1 + x DIV (2 * z)) * 2 * z <= x + h       by X_LT_DIV
      <=> 2 * z + 2 * z * (x DIV (2 * z)) <= x + h   by RIGHT_ADD_DISTRIB
      <=> 2 * z + x <= x + h + x MOD (2 * z)         by DIVISION
      <=>     2 * z <= h + x MOD (2 * z)

          x DIV (2 * z) < (x + h) DIV (2 * z)
      <=> x < 2 * z * (x + h) DIV (2 * z)            by DIV_LT_X
      <=> x + (x + h) MOD (2 * z) < (x + h)          by DIVISION
      <=>     (x + h) MOD (2 * z) < h
      This is true if    2 * z <= h   since (x + h) MOD (2 * z) < 2 * z   by MOD_LESS
      or  2 * z <= SQRT n             which is what I suspected.

      For windmill, n = x ** 2 + 4 * y * z
      Thus            4 * y * z <= n         in fact < n as x is ODD
      If only         4 * z * z <= n         this is true when y <= z
      Then                2 * z <= SQRT n    by SQRT_LE

      Now is_pung_alt |- !x y z. is_pung (x,y,z) <=> 2 * z - x = 0
      That is, 2 * z <= x                    by SUB_EQ_0
      which is not  2 * z <= SQRT n,
      But x ** 2 <= n, so x <= SQRT n        by windmill_x_upper!

This gives the following proof.
*)

(* Theorem: ~square n /\ n = windmill t /\ ~is_ping t ==> step 0 t < step (SQRT n) t *)
(* Proof:
   Let (x,y,z) = t,
       n = windmill (x,y,z),
       m = step 0 (x,y,z),
       k = step (SQRT n) (x,y,z).
   The goal is to show: m < k.
   Note 0 < z                                       by windmill_with_arms, ~square n

   If is_pong (x,y,z),
      Then m = 0                                    by step_0_of_pong
       but 0 < k                                    by step_sqrt_of_pong
      Hence m < k.

   Otherwise, is_pung (x,y,z)                       by triple_cases
      Then 2 * z - x = 0                            by is_pung_alt
        so 2 * z <= x                               by SUB_EQ_0
      also x <= SQRT n                              by windmill_x_upper
      Thus 2 * z <= SQRT n                          by LESS_EQ_TRANS, [1]

      Let h = SQRT n.
      Note m = x DIV (2 * z)                        by step_0
       and k = (x + h) DIV (2 * z)                  by step_sqrt
       Now (x + h) MOD (2 * z) < (2 * z)            by MOD_LESS
        so (x + h) MOD (2 * z) < h                  by [1]
       <=> ((x + h) DIV (2 * z)) * (2 * z) + (x + h) MOD (2 * z)
         < ((x + h) DIV (2 * z)) * (2 * z) + h      by LESS_MONO_ADD_EQ
       <=> x + h < k * (2 * z) + h                  by DIVISION
       <=>     x < k * (2 * z)                      by LESS_MONO_ADD_EQ
       <=> x DIV (2 * z) < k                        by DIV_LT_X
       <=>             m < k                        by notation
*)
Theorem step_0_lt_step_sqrt:
  !n t. ~square n /\ n = windmill t /\ ~is_ping t ==> step 0 t < step (SQRT n) t
Proof
  simp[FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `windmill (x,y,z)` >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  qabbrev_tac `m = step 0 (x,y,z)` >>
  qabbrev_tac `k = step (SQRT n) (x,y,z)` >>
  `0 < z` by metis_tac[windmill_with_arms] >>
  `is_pong (x,y,z) \/ is_pung (x,y,z)` by metis_tac[triple_cases] >| [
    `m = 0` by fs[step_0_of_pong, Abbr`m`] >>
    `0 < k` by metis_tac[step_sqrt_of_pong] >>
    decide_tac,
    qabbrev_tac `h = SQRT n` >>
    `2 * z <= x` by fs[is_pung_alt] >>
    `x <= h` by metis_tac[windmill_x_upper] >>
    `k = (x + h) DIV (2 * z)` by simp[step_def, Abbr`k`] >>
    `0 < 2 * z` by decide_tac >>
    `x + h = k * (2 * z) + (x + h) MOD (2 * z)` by metis_tac[DIVISION] >>
    `(x + h) MOD (2 * z) < 2 * z` by simp[] >>
    `x < k * (2 * z)` by decide_tac >>
    `x DIV (2 * z) < k` by simp[DIV_LT_X] >>
    fs[step_0, Abbr`m`]
  ]
QED

(*
For this range, x DIV (2 * z) = step 0 (x,y,z) < m <= step (SQRT n) (x,y,z) = (x + SQRT n) DIV (2 * z),
which is DIV (2 * z) < m,
hop m (x,y,z) = (2 * m * z - x,z,y + m * x - m * m * z) = (xx,yy,zz)
that is,
xx increases with m linearly, starting from x - 2 * (step 0 (x,y,z)) * z, the "x" of the pong from ~is_ping.
yy is always kept at original z, which is the focus.
zz varies with m quadratically, first increases, then decreases, starting from "y" of the pong from ~is_ping.

Therefore, the discriminant (2 * zz - xx) for subsequent ping/pong/pung
has two variations:
2 * zz - xx = 2 * (y + m * x - m * m * z) - (2 * m * z - x)
= x + 2 * y + 2 * m * x - 2 * m * m * z - 2 * m * z
= (x + 2 * y) + 2 * m * (x - z) - 2 * m * m * z

This is hard to handle, from the initial ~is_ping (x,y,z).
This is handled by:
hop_alt |- 0 < z ==> hop m (x,y,z) = if x DIV (2 * z) < m then (normal hop) else (invert hop)
This allows to decide which version simply by checking m: if (step 0 (x,y,z) < m) ....

Most likely to proceed by:
(1) show that hopping 0 (x,y,z) will start from ~is_ping (x,y,z) and reaches a pong.
(2) show that hopping (SQRT n) (x,y,z) is equivalent to starting from pong and do skip_ping.
*)

(* Theorem: tik n /\ ~square n /\ n = windmill t /\
            m = step 0 t /\ m + 1 + j < step (SQRT n) t ==> is_ping (hop (m + 1 + j) t)*)
(* Proof:
   Let (x,y,z) = t,
       s = step (SQRT n) (x,y,z),
       tt = hop (m + 1) (x,y,z).
       ping (hop (m + 1 + j) (x,y,z))
     = ping (FUNPOW ping j tt)                 by hop_step_0_beyond_pong, m + j < s
     = FUNPOW ping (SUC j) tt                  by FUNPOW_SUC
     = hop (m + 1 + SUC j) t                   by m + SUC j = m + 1 + j < s

   Let (xx,yy,zz) = hop (m + 1 + SUC j) tt.
   Note s = (x + SQRT n) DIV (2 * z)           by step_sqrt
    ==> n = windmill (xx,yy,zz)                by hop_windmill, ~square n
     so 0 < zz                                 by windmill_with_arms, ~square n

   Thus is_ping hop (m + 1 + j) t              by is_ping_by_ping
*)
Theorem hop_step_0_beyond_pong_is_ping:
  !n m j t. tik n /\ ~square n /\ n = windmill t /\
            m = step 0 t /\ m + 1 + j < step (SQRT n) t ==> is_ping (hop (m + 1 + j) t)
Proof
  simp[FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `windmill (x,y,z)` >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  qabbrev_tac `m = step 0 (x,y,z)` >>
  qabbrev_tac `s = step (SQRT n) (x,y,z)` >>
  qabbrev_tac `t = hop (m + 1) (x,y,z)` >>
  `m + j < s /\ m + SUC j < s /\ m + 1 + SUC j <= s` by decide_tac >>
  `ping (hop (m + 1 + j) (x,y,z)) = ping (FUNPOW ping j t)` by metis_tac[hop_step_0_beyond_pong] >>
  `_ = FUNPOW ping (SUC j) t` by simp[FUNPOW_SUC] >>
  `_ = hop (m + 1 + SUC j) (x,y,z)` by metis_tac[hop_step_0_beyond_pong] >>
  `?xx yy zz. hop (m + 1 + SUC j) (x,y,z) = (xx,yy,zz)` by metis_tac[triple_parts] >>
  `n = windmill (xx,yy,zz)` by metis_tac[hop_windmill, step_sqrt] >>
  `0 < zz` by metis_tac[windmill_with_arms] >>
  qabbrev_tac `u = hop (m + 1 + j) (x,y,z)` >>
  assume_tac is_ping_by_ping >>
  last_x_assum (qspecl_then [`u`] strip_assume_tac) >>
  rfs[]
QED

(* Very good! *)

(* Theorem: tik n /\ ~square n /\ n = windmill t /\ ~is_ping t ==> ~is_ping (hop (step (SQRT n) t) t) *)
(* Proof:
   Let (x,y,z) = t,
       n = windmill (x,y,z),
       m = step 0 (x,y,z),
       k = step (SQRT n) (x,y,z).
   By contradiction, suppose is_ping (hop k (x,y,z)).
   Note is_pong (hop m (x,y,z))                by hop_step_0_at_pong_is_pong [*]
    and m < k                                  by step_0_lt_step_sqrt

   Claim: hop (k + 1) (x,y,z) = ping (hop k (x,y,z))
   Proof: Let j = k - (m + 1).
          Then k = m + 1 + j                                 by arithmetic
          Note is_pong (FUNPOW pung m (x,y,z))               by hop_step_0_before_pong, [*]
           and !j. j < m ==> is_pung (hop j (x,y,z))         by hop_step_0_before_pong_is_pung
            or !j. j < m ==> is_pung (FUNPOW pung j (x,y,z)) by hop_step_0_before_pong
               hop (k + 1) (x,y,z)
             = (FUNPOW ping (SUC j) o pong o FUNPOW pung m) (x,y,z)     by pung_to_ping_by_hop
             = ping ((FUNPOW ping j o pong  o FUNPOW pung m) (x,y,z))   by FUNPOW_SUC
             = ping (hop k (x,y,z))                          by pung_to_ping_by_hop]);


   Note 0 < z                                  by windmill_with_arms
    and m = x DIV (2 * z)                      by step_0
    and k = (x + SQRT n) DIV (2 * z)           by step_sqrt
   Let xx = 2 * (k + 1) * z - x,
       yy = y + (k + 1) * x - (k + 1) * (k + 1) * z.
   Then hop (k + 1) (x,y,z) = (xx,z,yy)        by hop_alt, 0 < z /\ x DIV (2 * z) = m < k + 1
    and n = windmill (hop k (x,y,z))           by hop_windmill k <= (x + SQRT n) DIV (2 * z)
          = windmill (xx,z,yy)                 by ping_windmill, is_ping (hop k (x,y,z))
   Thus ~(0 < yy)                              by hop_arm, k < k + 1
    ==> ~is_ping (hop k (x,y,z))               by is_ping_by_ping, claim.
   This contradicts is_ping (hop k (x,y,z)).
*)
Theorem hop_step_sqrt_not_ping:
  !n t. tik n /\ ~square n /\ n = windmill t /\ ~is_ping t ==> ~is_ping (hop (step (SQRT n) t) t)
Proof
  simp[FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `windmill (x,y,z)` >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  qabbrev_tac `m = step 0 (x,y,z)` >>
  qabbrev_tac `k = step (SQRT n) (x,y,z)` >>
  `is_pong (hop m (x,y,z))` by fs[hop_step_0_at_pong_is_pong] >>
  `m < k` by fs[step_0_lt_step_sqrt, Abbr`m`, Abbr`k`] >>
  `hop (k + 1) (x,y,z) = ping (hop k (x,y,z))` by
  (`is_pong (FUNPOW pung m (x,y,z))` by metis_tac[hop_step_0_before_pong, LESS_EQ_REFL] >>
  `!j. j < m ==> is_pung (FUNPOW pung j (x,y,z))` by metis_tac[hop_step_0_before_pong_is_pung, hop_step_0_before_pong, LESS_IMP_LESS_OR_EQ] >>
  `k = (k - m - 1) + m + 1 /\ k + 1 = SUC (k - m - 1) + m + 1` by decide_tac >>
  qabbrev_tac `j = k - m - 1` >>
  `hop (k + 1) (x,y,z) = (FUNPOW ping (SUC j) o pong o FUNPOW pung m) (x,y,z)` by fs[pung_to_ping_by_hop] >>
  `_ = FUNPOW ping (SUC j) (pong (FUNPOW pung m (x,y,z)))` by fs[] >>
  `_ = ping (FUNPOW ping j (pong (FUNPOW pung m (x,y,z))))` by simp[FUNPOW_SUC] >>
  `_ = ping ((FUNPOW ping j o pong  o FUNPOW pung m) (x,y,z))` by fs[] >>
  metis_tac[pung_to_ping_by_hop]) >>
  `k = (x + SQRT n) DIV (2 * z)` by fs[step_sqrt, Abbr`k`] >>
  `~(k + 1 <= (x + SQRT n) DIV (2 * z)) /\ m < k + 1` by decide_tac >>
  qabbrev_tac `xx = 2 * (k + 1) * z - x` >>
  qabbrev_tac `yy = y + (k + 1) * x - (k + 1) * (k + 1) * z` >>
  `0 < z` by metis_tac[windmill_with_arms] >>
  `hop (k + 1) (x,y,z) = (xx,z,yy)` by metis_tac[hop_alt, step_0] >>
  `n = windmill (hop k (x,y,z))` by metis_tac[hop_windmill, LESS_OR_EQ] >>
  `_ = windmill (xx,z,yy)` by metis_tac[ping_windmill] >>
  `~(0 < yy)` by metis_tac[hop_arm] >>
  assume_tac is_ping_by_ping >>
  last_x_assum (qspecl_then [`hop k (x,y,z)`] strip_assume_tac) >>
  rgs[]
QED

(* Excellent! *)

(* ------------------------------------------------------------------------- *)
(* Skipping by Triples.                                                      *)
(* ------------------------------------------------------------------------- *)

(* Define skips over ping *)
Definition skip_ping_def:
   skip_ping t = WHILE (is_ping) ping t
End

(* Define skips over pung *)
Definition skip_pung_def:
   skip_pung t = WHILE (is_pung) pung t
End

(* Theorem: ~is_ping (FUNPOW ping k t) /\ (!j. j < k ==> is_ping (FUNPOW ping j t)) ==>
            skip_ping t = FUNPOW ping k t *)
(* Proof: by skip_ping_def, iterate_while_thm. *)
Theorem skip_ping_thm:
  !t k. ~is_ping (FUNPOW ping k t) /\ (!j. j < k ==> is_ping (FUNPOW ping j t)) ==>
        skip_ping t = FUNPOW ping k t
Proof
  simp[skip_ping_def, iterate_while_thm]
QED

(* Theorem: ~is_ping t ==> skip_ping t = t *)
(* Proof: put k = 0 in skip_ping_thm. *)
Theorem skip_ping_none:
  !t. ~is_ping t ==> skip_ping t = t
Proof
  metis_tac[skip_ping_thm, FUNPOW_0, DECIDE``~(j < 0)``]
QED

(* Theorem: ~is_pung (FUNPOW pung k t) /\ (!j. j < k ==> is_pung (FUNPOW pung j t)) ==>
            skip_pung t = FUNPOW pung k t *)
(* Proof: by skip_pung_def, iterate_while_thm. *)
Theorem skip_pung_thm:
  !t k. ~is_pung (FUNPOW pung k t) /\ (!j. j < k ==> is_pung (FUNPOW pung j t)) ==>
        skip_pung t = FUNPOW pung k t
Proof
  simp[skip_pung_def, iterate_while_thm]
QED

(* Theorem: ~is_pung t ==> skip_pung t = t *)
(* Proof: put k = 0 in skip_pung_thm. *)
Theorem skip_pung_none:
  !t. ~is_pung t ==> skip_pung t = t
Proof
  metis_tac[skip_pung_thm, FUNPOW_0, DECIDE``~(j < 0)``]
QED

(* Theorem: tik n /\ ~square n /\ n = windmill t ==> hopping 0 t = skip_pung t *)
(* Proof:
   Let (x,y,z) = t,
       m = step 0 (x,y,z).

   If is_ping (x,y,z),
      Note 0 < z                               by windmill_with_arms, ~square n
      Then m = 0                               by step_0_of_ping, 0 < z
       and ~is_pung (x,y,z)                    by ping_not_pung
        hopping 0 (x,y,z)
      = hop (step 0 (x,y,z)) (x,y,z)           by hopping_def
      = hop m (x,y,z)                          by notation
      = (x,y,z)                                by hop_0, m = 0
      = skip_pung (x,y,z)                      by skip_pung_none

   Otherwise, ~is_ping (x,y,z).
   Then is_pong (hop m (x,y,z))                by hop_step_0_at_pong_is_pong
     and hop m (x,y,z) = FUNPOW pung m (x,y,z) by hop_step_0_before_pong
     so ~is_pung (hop m (x,y,z))               by pong_not_pung
   Also !j. j < m ==> is_pung (hop j (x,y,z))  by hop_step_0_before_pong_is_pung

        hopping 0 (x,y,z)
      = hop (step 0 (x,y,z)) (x,y,z)           by hopping_def
      = hop m (x,y,z)                          by notation
      = FUNPOW pung m (x,y,z)                  by above
      = skip_pung (x,y,z)                      by skip_pung_thm
*)
Theorem hopping_0:
  !n t. tik n /\ ~square n /\ n = windmill t ==> hopping 0 t = skip_pung t
Proof
  simp[FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `windmill (x,y,z)` >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  qabbrev_tac `m = step 0 (x,y,z)` >>
  `is_ping (x,y,z) \/ ~is_ping (x,y,z)` by decide_tac >| [
    `0 < z` by metis_tac[windmill_with_arms] >>
    `m = 0` by fs[step_0_of_ping, Abbr`m`] >>
    fs[skip_pung_none, hopping_def, hop_0, ping_not_pung, Abbr`m`],
    `is_pong (hop m (x,y,z))` by fs[hop_step_0_at_pong_is_pong, Abbr`m`] >>
    `hop m (x,y,z) = FUNPOW pung m (x,y,z)` by fs[hop_step_0_before_pong, Abbr`m`] >>
    `!j. j < m ==> is_pung (FUNPOW pung j (x,y,z))` by fs[hop_step_0_before_pong_is_pung, GSYM hop_step_0_before_pong, Abbr`m`] >>
    fs[skip_pung_thm, hopping_def, pong_not_pung, Abbr`m`]
  ]
QED

(* Theorem: tik n /\ ~square n /\ n = windmill t /\ ~is_ping t ==>
            hopping (SQRT n) t = skip_ping (pong (hopping 0 t) *)
(* Proof:
   Let (x,y,z) = t,
       m = step 0 (x,y,z),
       k = step (SQRT n) (x,y,z).

   Note hopping (SQRT n) (x,y,z)
      = hop (step (SQRT n) (x,y,z)) (x,y,z)    by hopping_def
      = hop k (x,y,z)                          by notation [1]
    and hopping 0 (x,y,z)
      = hop (step 0 (x,y,z)) (x,y,z)           by hopping_def
      = hop m (x,y,z)                          by notation [2]
   The goal is to show: hop k (x,y,z) = skip_ping (pong (hop m (x,y,z))).

   Note 0 < z                                  by windmill_with_arms, ~square n
    and m < k                                  by step_0_lt_step_sqrt, ~is_ping (x,y,z)
   Let k = m + 1 + h,
       tt = hop (m + 1) (x,y,z),
        hop k (x,y,z)
      = FUNPOW ping h tt                       by hop_step_0_beyond_pong, m + h < k

   Note !j. j < h ==> is_ping (hop (m + 1 + j) (x,y,z))
                                               by hop_step_0_beyond_pong_is_ping
     or !j. j < h ==> is_ping (FUNPOW ping j tt)
                                               by hop_step_0_beyond_pong
   Note ~is_ping (hop k (x,y,z))               by hop_step_sqrt_not_ping
     or ~is_ping (FUNPOW ping h tt)            by above

        hopping (SQRT n) (x,y,z)
      = hop k (x,y,z)                          by [1]
      = FUNPOW ping h t                        by above
      = skip_ping (FUNPOW ping 0 tt)           by skip_ping_thm
      = skip_ping (hop (m + 1) (x,y,z))        by FUNPOW_0
      = skip_ping (pong (hop m (x,y,z)))       by hop_step_0_at_pong
      = skip_ping (pong (hopping 0 (x,y,z)))   by [2]
*)
Theorem hopping_sqrt:
  !n t. tik n /\ ~square n /\ n = windmill t /\ ~is_ping t ==>
        hopping (SQRT n) t = skip_ping (pong (hopping 0 t))
Proof
  simp[FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `windmill (x,y,z)` >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  rw[hopping_def] >>
  qabbrev_tac `m = step 0 (x,y,z)` >>
  qabbrev_tac `k = step (SQRT n) (x,y,z)` >>
  `0 < z` by metis_tac[windmill_with_arms] >>
  `m < k` by fs[step_0_lt_step_sqrt, Abbr`m`, Abbr`k`, Abbr`n`] >>
  `k = m + 1 + (k - m - 1)` by decide_tac >>
  qabbrev_tac `h = k - m - 1` >>
  qabbrev_tac `t = hop (m + 1) (x,y,z)` >>
  `t = pong (hop m (x,y,z))` by fs[hop_step_0_at_pong, Abbr`m`, Abbr`n`, Abbr`t`] >>
  `m + h < k` by decide_tac >>
  `hop k (x,y,z) = FUNPOW ping h t` by metis_tac[hop_step_0_beyond_pong] >>
  `~is_ping (FUNPOW ping h t)` by metis_tac[hop_step_sqrt_not_ping] >>
  `!j. j < h ==> is_ping (FUNPOW ping j t)` by
  (rpt strip_tac >>
  `m + 1 + j < k` by decide_tac >>
  `is_ping (hop (m + 1 + j) (x,y,z))` by fs[hop_step_0_beyond_pong_is_ping, Abbr`n`, Abbr`m`] >>
  rfs[hop_step_0_beyond_pong, Abbr`n`, Abbr`m`, Abbr`t`]) >>
  `skip_ping t = FUNPOW ping h t` by fs[skip_ping_thm] >>
  rfs[]
QED

(* Theorem: tik n /\ ~square n /\ n = windmill t /\ ~is_ping t ==>
            hopping (SQRT n) t = (skip_ping o pong o skip_pung) t *)
(* Proof:
     hopping (SQRT n) t
   = skip_ping (pong (hopping 0 t))            by hopping_sqrt
   = skip_ping (pong (skip_pung t)             by hopping_0
   = (skip_ping o pong o skip_pung) t          by o_THM
*)
Theorem hopping_sqrt_eqn:
  !n t. tik n /\ ~square n /\ n = windmill t /\ ~is_ping t ==>
        hopping (SQRT n) t = (skip_ping o pong o skip_pung) t
Proof
  simp[hopping_sqrt, hopping_0]
QED

(*
For n = 97, SQRT n = 9, k = n DIV 4 = 24.
> EVAL ``hopping 9 (1,24,1)``; = (9,1,4)
> EVAL ``hopping 9 (9,1,4)``; = (7,4,3)
> EVAL ``hopping 9 (7,4,3)``; = (5,3,6)
> EVAL ``hopping 9 (5,3,6)``; = (7,6,2)
> EVAL ``hopping 9 (7,6,2)``; = (9,2,2)
*)

(* ------------------------------------------------------------------------- *)
(* Picking Pongs along a Path.                                               *)
(* ------------------------------------------------------------------------- *)

(* Extract the pong elements in a list. *)
Definition pong_list_def:
    pong_list ls = FILTER is_pong ls
End

(*
> EVAL ``pong_list (FRONT (path 41 6))``; = [(1,10,1); (5,1,4); (3,4,2)]
> EVAL ``pong_list (FRONT (path 61 6))``; = [(1,15,1); (1,5,3)]
> EVAL ``pong_list (FRONT (path 97 14))``; = [(1,24,1); (1,6,4); (1,8,3); (5,3,6); (3,11,2)]
*)

(* Theorem: LENGTH (pong_list ls) <= LENGTH ls *)
(* Proof:
      pong_list []
    = FILTER is_pong []        by pong_indices_def
    = []]                      by FILTER
*)
Theorem pong_list_nil:
  pong_list [] = []
Proof
  simp[pong_list_def]
QED

(* Theorem: LENGTH (pong_list ls) <= LENGTH ls *)
(* Proof:
      LENGTH (pong_list ls)
    = LENGTH (FILTER is_pong ls)   by pong_indices_def
   <= LENGTH ls                    by LENGTH_FILTER_LEQ
*)
Theorem pong_list_length:
  !ls. LENGTH (pong_list ls) <= LENGTH ls
Proof
  simp[pong_list_def, LENGTH_FILTER_LEQ]
QED

(* Theorem: let ps = pong_list ls in j < LENGTH ps ==> is_pong (EL j ps) /\ MEM (EL j ps) ls *)
(* Proof:
   Let ps = pong_list ls,
        x = EL j ps.
   Then MEM x ps                   by EL_MEM, j < LENGTH ps
    <=> MEM x (FILTER is_pong ls)  by pong_list_def
    <=> is_pong x /\ MEM x ls      by MEM_FILTER
*)
Theorem pong_list_element:
  !ls j. let ps = pong_list ls in j < LENGTH ps ==> is_pong (EL j ps) /\ MEM (EL j ps) ls
Proof
  simp[] >>
  ntac 3 strip_tac >>
  qabbrev_tac `ps = pong_list ls` >>
  `MEM (EL j ps) ps` by fs[EL_MEM] >>
  fs[pong_list_def, MEM_FILTER, Abbr`ps`]
QED

(* Theorem: let ls = path n k; ps = pong_list (FRONT ls) in j < LENGTH ps ==>
            ?h. h < k /\ EL j ps = EL h ls /\ is_pong (EL h ls) *)
(* Proof:
   Let ls = path n k,
       fs = FRONT ls,
       ps = pong_list fs,
       t = EL j ps.
   Then is_pong t /\ MEM t fs                  by pong_list_element
   Note LENGTH fs = k                          by path_front_length
    and ls <> []                               by path_not_nil
   Thus ?h. h < k /\ t = EL h fs               by MEM_EL
     or              t = EL h ls               by FRONT_EL, ls <> []
   Take this h.
*)
(* Theorem: ls <> [] /\ ALL_DISTINCT ls ==> ALL_DISTINCT (pong_list (FRONT ls)) *)
(* Proof:
       ALL_DISTINCT ls
   ==> ALL_DISTINCT (FRONT ls)                     by ALL_DISTINCT_FRONT, ls <> []
   ==> ALL_DISTINCT (FILTER is_pong (FRONT ls))    by FILTER_ALL_DISTINCT
   ==> ALL_DISTINCT (pong_list (FRONT ls))         by pong_list_def
*)
Theorem pong_list_all_distinct:
  !ls. ls <> [] /\ ALL_DISTINCT ls ==> ALL_DISTINCT (pong_list (FRONT ls))
Proof
  rw[pong_list_def] >>
  simp[ALL_DISTINCT_FRONT, FILTER_ALL_DISTINCT]
QED

Theorem pong_list_path_element:
  !n k j. let ls = path n k; ps = pong_list (FRONT ls) in j < LENGTH ps ==>
           ?h. h < k /\ EL j ps = EL h ls /\ is_pong (EL h ls)
Proof
  simp[] >>
  ntac 4 strip_tac >>
  qabbrev_tac `ls = path n k` >>
  qabbrev_tac `fs = FRONT ls` >>
  qabbrev_tac `ps = pong_list fs` >>
  qabbrev_tac `t = EL j ps` >>
  `LENGTH fs = k` by fs[path_front_length, Abbr`fs`, Abbr`ls`] >>
  `is_pong t /\ MEM t fs` by metis_tac[pong_list_element] >>
  metis_tac[path_not_nil, MEM_EL, FRONT_EL]
QED

(* Theorem: 0 < k ==> HD (pong_list (FRONT (path n k))) = (1, n DIV 4, 1) *)
(* Proof:
   Let ls = FRONT (path n k),
        u = (1,n DIV 4,1).
   Then LENGTH ls = k                          by path_front_length
    and HD ls = u                              by path_front_head, 0 < k
    and is_pong u                              by is_pong_x_y_x
   Thus ls = [] ++ u::(TL ls)
        HD (pong_list ls)
      = HD (FILTER is_pong ls)                 by pong_list_def
      = u                                      by FILTER_HD, FILTER
*)
Theorem pong_list_path_head:
  !n k. 0 < k ==> HD (pong_list (FRONT (path n k))) = (1, n DIV 4, 1)
Proof
  rw[pong_list_def] >>
  qabbrev_tac `ls = FRONT (path n k)` >>
  qabbrev_tac `u = (1,n DIV 4,1)` >>
  `LENGTH ls = k` by fs[path_front_length, Abbr`ls`] >>
  `?t. ls = u::t` by metis_tac[path_front_head, LIST_NOT_NIL, LENGTH_EQ_0, NOT_ZERO] >>
  fs[FILTER_HD, is_pong_x_y_x, Abbr`u`]
QED

(* Theorem: let ls = path n k; ps = pong_list (FRONT ls) in 0 < k ==> HD ps = HD ls *)
(* Proof:
     HD ps
   = (1,n DIV 4,1)             by pong_list_path_head, 0 < k
   = HD ls                     by path_head
*)
Theorem pong_list_path_head_alt:
  !n k. let ls = path n k in 0 < k ==> HD (pong_list (FRONT ls)) = HD ls
Proof
  simp[pong_list_path_head, path_head]
QED

(* Theorem: pong_list (FRONT (path n k)) = [] <=> k = 0 *)
(* Proof:
   Let ls = FRONT (path n k),
        u = (1, n DIV 4, 1)
   Then LENGTH ls = k                          by path_front_length

       pong_list ls = []
   <=> FILTER is_pong ls = []                  by pong_list_def
   <=> EVERY ~is_pong ls                       by FILTER_EQ_NIL

   If ls = [],
      Then k = 0                               by LENGTH_EQ_0
       and EVERY ~is_pong [] = T               by EVERY_DEF
   If ls <> [],
      Then 0 < k                               by LENGTH_EQ_0, NOT_ZERO
       and MEM (HD ls) ls                      by HEAD_MEM, ls <> []
        or MEM u ls                            by path_front_head
       and is_pong u                           by is_pong_x_y_x
      Thus EVERY ~is_pong ls = F               by EVERY_MEM
       and k = 0 is F                          by 0 < k
*)
Theorem pong_list_path_eq_nil:
  !n k. pong_list (FRONT (path n k)) = [] <=> k = 0
Proof
  rw[pong_list_def] >>
  qabbrev_tac `ls = FRONT (path n k)` >>
  qabbrev_tac `u = (1,n DIV 4,1)` >>
  `LENGTH ls = k` by fs[path_front_length, Abbr`ls`] >>
  simp[FILTER_EQ_NIL] >>
  Cases_on `ls` >-
  fs[] >>
  qabbrev_tac `ls = h::t` >>
  `ls <> [] /\ 0 < k` by metis_tac[NOT_CONS_NIL, LENGTH_EQ_0, NOT_ZERO] >>
  simp[EVERY_MEM] >>
  qexists_tac `u` >>
  `h = u` by metis_tac[path_front_head, HD] >>
  `is_pong u` by fs[is_pong_x_y_x, Abbr`u`] >>
  metis_tac[HEAD_MEM, HD]
QED

(*
n = 61 is an example of a pong at the end.

> EVAL ``SQRT 61``; = 7
> EVAL ``61 DIV 4``; = 15
> EVAL ``MAP (\t. (t, is_pong t)) (path 61 6)``; = [((1,15,1),T); ((1,1,15),F); ((3,1,13),F); ((5,1,9),F); ((7,1,3),F); ((1,5,3),T); ((5,3,3),T)]
> EVAL ``pong_list (FRONT (path 61 6))``; = [(1,15,1); (1,5,3)]
> EVAL ``FUNPOW (skip_pung o skip_ping o pong) 0 (1,15,1)``; = (1,15,1)
> EVAL ``FUNPOW (skip_pung o skip_ping o pong) 1 (1,15,1)``; = (1,5,3)

> EVAL ``MAP (skip_ping o pong) (pong_list (FRONT (path 61 6)))``; = [(7,1,3); (5,3,3)]
> EVAL ``FUNPOW (hopping 7) 0 (1,15,1)``; = (1,15,1)
> EVAL ``FUNPOW (hopping 7) 1 (1,15,1)``; = (7,1,3)
> EVAL ``FUNPOW (hopping 7) 2 (1,15,1)``; = (5,3,3)

> EVAL ``(skip_pung o skip_ping o pong) (1,15,1)``; = (1,5,3)
*)

(* Theorem: tik n /\ ~square n ==>
            FINITE (mills n) /\ (zagier o flip) PERMUTES (mills n) /\ 0 < iterate_period (zagier o flip) (1,1,n DIV 4) *)
(* Proof:
   Let s = mills n,
       u = (1,1,n DIV 4).
   Then FINITE s                               by mills_finite_non_square, ~square n
    and u IN s                                 by mills_element_trivial, tik n
   Also zagier involute s                      by zagier_involute_mills, tik n /\ ~square n
    and flip involute s                        by flip_involute_mills
   Thus (zagier o flip) PERMUTES s             by involute_involute_permutes
    and 0 < iterate_period (zagier o flip) u   by iterate_period_pos
*)
Theorem tik_non_square_property:
  !n. tik n /\ ~square n ==>
      FINITE (mills n) /\ (zagier o flip) PERMUTES (mills n) /\ 0 < iterate_period (zagier o flip) (1,1,n DIV 4)
Proof
  ntac 2 strip_tac >>
  qabbrev_tac `s = mills n` >>
  qabbrev_tac `u = (1,1,n DIV 4)` >>
  qabbrev_tac `p = iterate_period (zagier o flip) u` >>
  `FINITE s` by fs[mills_finite_non_square, Abbr`s`] >>
  `u IN s` by simp[mills_element_trivial, Abbr`u`, Abbr`s`] >>
  `zagier involute s` by metis_tac[zagier_involute_mills, ONE_NOT_0] >>
  `flip involute s` by metis_tac[flip_involute_mills] >>
  `zagier o flip PERMUTES s` by fs[involute_involute_permutes] >>
  metis_tac[iterate_period_pos]
QED

(* Theorem: iterate_period (zagier o flip) (1,1,k) = 1 <=> k = 1 *)
(* Proof:
   Let u = (1,1,k),
       f = zagier o flip,
       p = iterate_period f u.
   Then p = 1 <=> f u = u                      by iterate_period_eq_1
   If 2 < k,
      f u = (3,1,k - 2) <> u                   by zagier_def, flip_def
   Otherwise k = 0 or 1 or 2.
      If k = 0, f u = (1,2,0) <> u             by zagier_def, flip_def
      If k = 1, f u = (1,1,1) = u              by zagier_def, flip_def
      If k = 2, f u = (3,2,0) <> u             by zagier_def, flip_def

     Hence the period p = 1 iff k = 1.
*)
Theorem zagier_flip_iterate_period_eq_1:
  !k. iterate_period (zagier o flip) (1,1,k) = 1 <=> k = 1
Proof
  rw[iterate_period_eq_1] >>
  Cases_on `2 < k` >-
  fs[zagier_def, flip_def] >>
  (`k = 0 \/ k = 1 \/ k = 2` by decide_tac >> fs[zagier_def, flip_def])
QED

(* Theorem: tik n ==> iterate_period (zagier o flip) (1,1,n DIV 4) <> 2 *)
(* Proof:
   Let u = (1,1,k),
       f = zagier o flip,
       p = iterate_period f u.
   By contradiction, suppose p = 2.
   Then f u <> u /\ f (f u) = u                by iterate_period_eq_2

   If 6 < k,
      f u = (3,1,k-2)                          by zagier_def, flip_def
      f (f u) = (5,1,k-5)                      by zagier_def, flip_def
      This contradicts f (f u) = u             by PAIR_EQ

   Otherwise, if 3 < k,
      f u = (3,1,k-2)                          by zagier_def, flip_def
      f (f u) = (2 * k - 7,k - 2,6 - k)        by zagier_def, flip_def
      This contradicts f (f u) = u             by 1 < k - 2, not 1.

   Otherwise, k = 0 or 1 or 2 or 3.
      If k = 0, f (f u) = (1,3,0) <> u, a contradiction.
      If k = 1, f u = (1,1,1) = u     , a contradiction.
      If k = 2, f (f u) = (3,5,0) <> u, a contradiction.
      If k = 3, f (f u) = (1,3,1) <> u, a contradiction.

     Hence the period p is never 2.
*)
Theorem zagier_flip_iterate_period_ne_2:
  !k. iterate_period (zagier o flip) (1,1,k) <> 2
Proof
  rw[iterate_period_eq_2] >>
  Cases_on `6 < k` >-
  fs[zagier_def, flip_def] >>
  Cases_on `3 < k` >-
  fs[zagier_def, flip_def] >>
  (`k = 0 \/ k = 1 \/ k = 2 \/ k = 3` by decide_tac >> fs[zagier_def, flip_def])
QED

(* Theorem: tik n ==> (iterate_period (zagier o flip) (1,1,n DIV 4) = 1 <=> n = 5) *)
(* Proof:
   Note iterate_period f u = 1 <=> n DIV 4 = 1 by zagier_flip_1_1_z_period
   Then n = (n DIV 4) * 4 + (n MOD 4)          by DIVISION
          = 1 * 4 + 1 = 5                      by tik n
*)
Theorem tik_iterate_period_eq_1:
  !n. tik n ==> (iterate_period (zagier o flip) (1,1,n DIV 4) = 1 <=> n = 5)
Proof
  rpt strip_tac >>
  `n = (n DIV 4) * 4 + 1` by metis_tac[DIVISION, DECIDE``0 < 4``] >>
  simp[zagier_flip_1_1_z_period]
QED

(* Theorem: let ls = path n k in tik n ==> (flip (HD ls) = HD ls <=> n = 5) *)
(* Proof:
   Let ls = path n k.
   Then HD ls = (1,n DIV 4,1)                  by path_head
       flip (HD ls) = HD ls
   <=> n DIV 4 = 1                             by flip_fix
   <=> n = 1 * 4 + n MOD 1                     by DIVISION
   <=> n = 1 * 4 + 1                           by tik n
   <=> n = 5
*)
Theorem tik_path_head_flip_fix:
  !n k. let ls = path n k in tik n ==> (flip (HD ls) = HD ls <=> n = 5)
Proof
  rw_tac std_ss[] >>
  `HD ls = (1, n DIV 4, 1)` by fs[path_head, Abbr`ls`] >>
  `flip (HD ls) = HD ls <=> n DIV 4 = 1` by simp[flip_fix] >>
  `n = (n DIV 4) * 4 + 1` by metis_tac[DIVISION, DECIDE``0 < 4``] >>
  fs[]
QED

(* Idea: the list (path n k) is all distinct unless n = 5. *)

(* Theorem: tik n /\ ~square n /\ k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) ==>
            (ALL_DISTINCT (path n k) <=> n <> 5)` *)
(* Proof:
   Let ls = path n k,
        u = (1,1,n DIV 4),
        v = (1,n DIV 4,1),
        p = iterate_period (zagier o flip) u.

   If part: ALL_DISTINCT ls ==> n <> 5
      By contradiction, suppose n = 5.
      Then p = 1                               by tik_iterate_period_eq_1, tik n
        so k = 1                               by k = 1 + HALF p
      Thus EL 0 ls = v                         by path_element_0
       and EL 1 ls = u                         by path_element_1, 0 < k
       but u = v = (1,1,1)                     by n = 5
       and LENGTH ls = k + 1 = 2               by path_length
      This contradicts ALL_DISTINCT ls         by ALL_DISTINCT_EL_IMP

   Only-if part: n <> 5 ==> ALL_DISTINCT ls
      Note ls <> []                            by path_not_nil
      Thus ?t. ls = v::t                       by path_head, list_CASES
       and LENGTH t = k                        by path_length, LENGTH
       and ALL_DISTINCT t                      by path_tail_all_distinct
      By contradiction, suppose ~ALL_DISTINCT ls.
      Then MEM v t                             by ALL_DISTINCT
       ==> ?h. h < k /\ v = EL h t             by MEM_EL

           FUNPOW (zagier o flip) (SUC h) u
         = (zagier o flip) FUNPOW (zagier o flip) h u      by FUNPOW_SUC
         = (zagier o flip) (EL h t)            by path_tail_element
         = (zagier o flip) v
         = zagier u                            by flip v = u
         = u                                   by zagier_1_1_z, [1]

      Note 0 < p                               by tik_non_square_property
       and p <> 1                              by tik_iterate_period_eq_1, n <> 5
       and p <> 2                              by zagier_flip_iterate_period_ne_2
       and SUC h = h + 1 <= k = 1 + HALF p     by h < k
       but 1 + HALF p < p                      by HALF_ADD1_LT, 2 < p
      Thus SUC h < p, [1] is a contradiction   by iterate_period_minimal, 0 < SUC h
*)
Theorem path_all_distinct:
  !n k. tik n /\ ~square n /\ k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) ==>
        (ALL_DISTINCT (path n k) <=> n <> 5)
Proof
  rpt strip_tac >>
  qabbrev_tac `ls = path n k` >>
  qabbrev_tac `u = (1,1,n DIV 4)` >>
  qabbrev_tac `v = (1,n DIV 4,1)` >>
  qabbrev_tac `p = iterate_period (zagier o flip) u` >>
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    qabbrev_tac `k = 1 + HALF p` >>
    `p = 1` by fs[tik_iterate_period_eq_1, Abbr`p`, Abbr`u`] >>
    `k = 1` by simp[Abbr`k`] >>
    `LENGTH ls = 2` by rfs[path_length, Abbr`ls`] >>
    `EL 0 ls = v` by rfs[path_element_0, Abbr`ls`, Abbr`v`] >>
    `EL 1 ls = u` by rfs[path_element_1, Abbr`ls`, Abbr`u`] >>
    `u = v` by simp[Abbr`u`, Abbr`v`] >>
    `0 < 2 /\ 1 < 2 /\ 0 <> 1` by decide_tac >>
    metis_tac[ALL_DISTINCT_EL_IMP],
    spose_not_then strip_assume_tac >>
    qabbrev_tac `k = 1 + HALF p` >>
    `ls <> []` by fs[path_not_nil, Abbr`ls`] >>
    `?t. ls = v::t` by metis_tac[path_head, list_CASES, HD] >>
    `ALL_DISTINCT t` by metis_tac[path_tail_all_distinct, TL] >>
    `MEM v t` by fs[ALL_DISTINCT] >>
    `SUC (LENGTH t) = k + 1` by metis_tac[path_length, LENGTH] >>
    `LENGTH t = k` by decide_tac >>
    `?h. h < k /\ v = EL h t` by metis_tac[MEM_EL] >>
    `FUNPOW (zagier o flip) (SUC h) u = u` by
  (simp[FUNPOW_SUC] >>
    `zagier (flip (FUNPOW (zagier o flip) h u)) = zagier (flip v)` by metis_tac[path_tail_element, TL] >>
    simp[zagier_def, flip_def, Abbr`v`, Abbr`u`]) >>
    `SUC h < p` by
    (`SUC h <= 1 + HALF p` by fs[Abbr`k`] >>
    `0 < p` by fs[tik_non_square_property, Abbr`p`, Abbr`u`] >>
    `p <> 1` by fs[tik_iterate_period_eq_1, Abbr`p`, Abbr`u`] >>
    `p <> 2` by fs[zagier_flip_iterate_period_ne_2, Abbr`p`, Abbr`u`] >>
    `1 + HALF p < p` by fs[HALF_ADD1_LT] >>
    decide_tac) >>
    `0 < SUC h` by decide_tac >>
    fs[iterate_period_minimal, Abbr`p`]
  ]
QED

(* Theorem: let ls = path n k in p <= q /\ q <= k /\ ~is_ping (EL q ls) /\
            (!j. p <= j /\ j < q ==> is_ping (EL j ls)) ==> EL q ls = skip_ping (EL p ls) *)
(* Proof:
   Let ls = path n k.
   Given !j. p <= j /\ j < q ==> is_ping (EL j ls)
      or !j. j + p < q ==> is_ping (EL (j + p) ls)                 by replacing j with j + p
   Note !j. j <= q - p ==> EL (j + p) ls = FUNPOW ping j (EL p ls) by path_element_ping_funpow
     or !j. j + p <= q ==> EL (j + p) ls = FUNPOW ping j (EL p ls) [1]
   Thus !j. j < q - p ==> is_ping (FUNPOW ping j (EL p ls))        by given
        EL q ls
      = FUNPOW ping (q - p) (EL p ls)                              by q - p + p = q
      = skip_ping (EL p ls)                                        by skip_ping_thm
*)
Theorem path_skip_ping_thm:
  !n k p q. let ls = path n k in p <= q /\ q <= k /\ ~is_ping (EL q ls) /\
            (!j. p <= j /\ j < q ==> is_ping (EL j ls)) ==> EL q ls = skip_ping (EL p ls)
Proof
  rw_tac std_ss[] >>
  assume_tac path_element_ping_funpow >>
  last_x_assum (qspecl_then [`n`, `k`, `p`,`q - p`] strip_assume_tac) >>
  rfs[] >>
  `!j. j < q - p ==> is_ping (FUNPOW ping j (EL p ls))` by
  (rpt strip_tac >>
  `p <= j + p /\ j + p < q /\ j <= q - p` by decide_tac >>
  metis_tac[]) >>
  `EL q ls = FUNPOW ping (q - p) (EL p ls)` by
    (`q - p <= q - p /\ q - p + p = q` by decide_tac >>
  metis_tac[]) >>
  fs[skip_ping_thm]
QED

(* Theorem: let ls = path n k in p <= q /\ q <= k /\ ~is_pung (EL q ls) /\
            (!j. p <= j /\ j < q ==> is_pung (EL j ls)) ==> EL q ls = skip_pung (EL p ls) *)
(* Proof:
   Let ls = path n k.
   Given !j. p <= j /\ j < q ==> is_pung (EL j ls)
      or !j. j + p < q ==> is_pung (EL (j + p) ls)                 by replacing j with j + p
   Note !j. j <= q - p ==> EL (j + p) ls = FUNPOW pung j (EL p ls) by path_element_pung_funpow
     or !j. j + p <= q ==> EL (j + p) ls = FUNPOW pung j (EL p ls) [1]
   Thus !j. j < q - p ==> is_ping (FUNPOW pung j (EL p ls))        by given
        EL q ls
      = FUNPOW pung (q - p) (EL p ls)                              by q - p + p = q
      = skip_pung (EL p ls)                                        by skip_pung_thm
*)
Theorem path_skip_pung_thm:
  !n k p q. let ls = path n k in p <= q /\ q <= k /\ ~is_pung (EL q ls) /\
            (!j. p <= j /\ j < q ==> is_pung (EL j ls)) ==> EL q ls = skip_pung (EL p ls)
Proof
  rw_tac std_ss[] >>
  assume_tac path_element_pung_funpow >>
  last_x_assum (qspecl_then [`n`, `k`, `p`,`q - p`] strip_assume_tac) >>
  rfs[] >>
  `!j. j < q - p ==> is_pung (FUNPOW pung j (EL p ls))` by
  (rpt strip_tac >>
  `p <= j + p /\ j + p < q /\ j <= q - p` by decide_tac >>
  metis_tac[]) >>
  `EL q ls = FUNPOW pung (q - p) (EL p ls)` by
    (`q - p <= q - p /\ q - p + p = q` by decide_tac >>
  metis_tac[]) >>
  fs[skip_pung_thm]
QED

(* Theorem: let ls = path n k in p < q /\ q <= k /\ is_pong (EL p ls) /\ is_pong (EL q ls) /\
            (!j. p < j /\ j < q ==> ~is_pong (EL j ls)) ==> EL q ls = (skip_pung o skip_ping o pong) (EL p ls) *)
(* Proof:
   Let ls = path n k.
   Note ?c. p < c /\ c <= q /\ ~is_ping (EL c ls) /\
            (!j. p < j /\ j < c ==> is_ping (EL j ls)) /\
             !j. c <= j /\ j < q ==> is_pung (EL j ls))        by pong_interval_cut_exists
   Thus EL (p + 1) ls = pong (EL p ls)                         by path_element_suc, zagier_flip_pong
    and EL c ls = skip_ping (EL (p + 1) ls)                    by path_skip_ping_thm
   Also ~is_pung (EL q ls)                                     by pong_not_pung
    and EL q ls = skip_pung (EL c ls)                          by path_skip_pung_thm
   Thus EL q ls = skip_pung (skip_ping (pong (EL p ls)))
                = (skip_pung o skip_ping o pong) (EL p ls)     by o_THM
*)
Theorem pong_interval_next_pong:
  !n k p q. let ls = path n k in p < q /\ q <= k /\ is_pong (EL p ls) /\ is_pong (EL q ls) /\
            (!j. p < j /\ j < q ==> ~is_pong (EL j ls)) ==> EL q ls = (skip_pung o skip_ping o pong) (EL p ls)
Proof
  rw_tac std_ss[] >>
  assume_tac pong_interval_cut_exists >>
  last_x_assum (qspecl_then [`n`, `k`, `p`,`q`] strip_assume_tac) >>
  rfs[] >>
  `EL (p + 1) ls = pong (EL p ls)` by fs[path_element_suc, zagier_flip_pong, GSYM ADD1, Abbr`ls`] >>
  assume_tac path_skip_ping_thm >>
  last_x_assum (qspecl_then [`n`, `k`, `p+1`,`c`] strip_assume_tac) >>
  rfs[] >>
  assume_tac path_skip_pung_thm >>
  last_x_assum (qspecl_then [`n`, `k`, `c`,`q`] strip_assume_tac) >>
  rfs[pong_not_pung]
QED

(* Theorem: let ls = path n k; ps = pong_list (FRONT ls) in ALL_DISTINCT ls /\ j + 1 < LENGTH ps ==>
            ?p q. p < q /\ q < k /\ EL p ls = EL j ps /\ EL q ls = EL (j + 1) ps /\
            is_pong (EL p ls) /\ is_pong (EL q ls) /\ !h. p < h /\ h < q ==> ~is_pong (EL h ls) *)
(* Proof:
   Let ls = path n k,
       fs = FRONT ls,
       ps = pong_list fs,
        t = beyond_pong (EL j ps).
   The goal is to show: n = windmill t /\ ~is_ping t /\ t <> LAST ls

   Note LENGTH fs = k                          by path_front_length
    and ps = FILTER is_pong fs                 by pong_list_def

   Let x = EL j ps,
       y = EL (j + 1) ps.
   Then ?p. p < k /\ x = EL p ls /\ is_pong x  by pong_list_path_element
    and ?q. q < k /\ y = EL q ls /\ is_pong y  by pong_list_path_element
   Pick these p and q.

   Note ls <> []                               by path_not_nil
    and ALL_DISTINCT fs                        by ALL_DISTINCT_FRONT
   also x = EL p fs /\ y = EL q fs             by FRONT_EL
   Thus p < q                                  by FILTER_element_order, findi_EL

   Claim: !h. p < h /\ h < q ==> ~is_pong (EL h ls)
   Proof: By contradiction, suppose is_pong (EL h ls).
          Note ?l1 l2 l3. fs = l1 ++ x::l2 ++ y::l3        by EL_SPLIT_2, p < q
           Now p = LENGTH l1                               by ALL_DISTINCT_EL_APPEND
           and q = LENGTH (l1 ++ x::l2)                    by ALL_DISTINCT_EL_APPEND
          Note h - p <> 0 /\ h - p - 1 < LENGTH l2         by p < h
               EL h ls
             = EL h fs                         by FRONT_EL
             = EL (h - p) (x::l2 ++ y::l3)     by EL_APPEND_EQN
             = EL (h - p) (x::l2)              by EL_APPEND_EQN
             = EL (h - p - 1) l2               by EL_TAIL

          Note j = LENGTH (FILTER is_pong l1)  by FILTER_EL_IFF
          Thus FILTER is_pong l2 = []          by FILTER_EL_NEXT_IFF
           <=> EVERY ~is_pong l2               by FILTER_EQ_NIL
           <=> !n. n < LENGTH l2 ==> ~is_pong (EL n l2)
                                               by EVERY_EL
          Giving ~is_pong (EL h ls), a contradiction.
*)
Theorem pong_list_pair_in_path:
  !n k j. let ls = path n k; ps = pong_list (FRONT ls) in ALL_DISTINCT ls /\ j + 1 < LENGTH ps ==>
          ?p q. p < q /\ q < k /\ EL p ls = EL j ps /\ EL q ls = EL (j + 1) ps /\
          is_pong (EL p ls) /\ is_pong (EL q ls) /\ !h. p < h /\ h < q ==> ~is_pong (EL h ls)
Proof
  simp[] >>
  ntac 4 strip_tac >>
  qabbrev_tac `ls = path n k` >>
  qabbrev_tac `fs = FRONT ls` >>
  qabbrev_tac `ps = pong_list fs` >>
  qabbrev_tac `x = EL j ps` >>
  qabbrev_tac `y = EL (j + 1) ps` >>
  `LENGTH fs = k` by fs[path_front_length, Abbr`ls`, Abbr`fs`] >>
  `ps = FILTER is_pong fs` by fs[pong_list_def, Abbr`ps`, Abbr`fs`] >>
  `j < LENGTH ps /\ j < j + 1` by decide_tac >>
  `?p. p < k /\ x = EL p ls /\ is_pong x` by metis_tac[pong_list_path_element] >>
  `?q. q < k /\ y = EL q ls /\ is_pong y` by metis_tac[pong_list_path_element] >>
  map_every qexists_tac [`p`, `q`] >>
  `ls <> []` by fs[path_not_nil, Abbr`ls`] >>
  `ALL_DISTINCT fs` by fs[ALL_DISTINCT_FRONT, Abbr`fs`] >>
  `x = EL p fs /\ y = EL q fs` by fs[FRONT_EL, Abbr`fs`] >>
  `p < q` by metis_tac[FILTER_element_order, findi_EL] >>
  `!h. p < h /\ h < q ==> ~is_pong (EL h ls)` by
  (rpt strip_tac >>
  `?l1 l2 l3. fs = l1 ++ x::l2 ++ y::l3` by metis_tac[EL_SPLIT_2] >>
  `fs = l1 ++ [x] ++ (l2 ++ y::l3)` by fs[] >>
  `p = LENGTH l1` by metis_tac[ALL_DISTINCT_EL_APPEND] >>
  `fs = (l1 ++ x::l2) ++ [y] ++ l3` by fs[] >>
  `q = LENGTH (l1 ++ x::l2)` by metis_tac[ALL_DISTINCT_EL_APPEND] >>
  `fs = l1 ++ (x::l2 ++ y::l3)` by fs[] >>
  `~(h < p) /\ h - p <> 0` by decide_tac >>
  `EL h ls = EL h fs` by fs[FRONT_EL, Abbr`fs`] >>
  `_ = EL (h - p) (x::l2)` by metis_tac[EL_APPEND_EQN] >>
  `_ = EL (h - p - 1) l2` by fs[EL_TAIL] >>
  `j = LENGTH (FILTER is_pong l1)` by metis_tac[FILTER_EL_IFF, APPEND_ASSOC_CONS] >>
  `FILTER is_pong l2 = []` by metis_tac[FILTER_EL_NEXT_IFF] >>
  `h - p - 1 < LENGTH l2` by fs[] >>
  `!n. n < LENGTH l2 ==> ~is_pong (EL n l2)` by fs[FILTER_EQ_NIL, EVERY_EL] >>
  fs[]) >>
  rfs[]
QED

(* Theorem: let ls = path n k; ps = pong_list (FRONT ls) in ALL_DISTINCT ls /\ j + 1 < LENGTH ps ==>
            EL (j + 1) ps = (skip_pung o skip_ping o pong) (EL j ps) *)
(* Proof:
   Let ls = path n k,
       fs = FRONT ls,
       ps = pong_list fs.
   The goal is to show: EL (j + 1) ps = skip_pung o skip_ping o pong (EL j ps)

   Note ?p q. p < q /\ q < k /\ EL p ls = EL j ps /\ EL q ls = EL (j + 1) ps /\
              is_pong (EL p ls) /\ is_pong (EL q ls) /\
              !h. p < h /\ h < q ==> ~is_pong (EL h ls)
                                                   by pong_list_pair_in_path
   Thus EL (j + 1) ps
      = (skip_pung o skip_ping o pong) (EL j ps)   by pong_interval_next_pong
*)
Theorem pong_list_path_element_suc:
  !n k j. let ls = path n k; ps = pong_list (FRONT ls) in ALL_DISTINCT ls /\ j + 1 < LENGTH ps ==>
          EL (j + 1) ps = (skip_pung o skip_ping o pong) (EL j ps)
Proof
  rw_tac std_ss[] >>
  assume_tac pong_list_pair_in_path >>
  last_x_assum (qspecl_then [`n`, `k`, `j`] strip_assume_tac) >>
  rfs[] >>
  `EL (j + 1) ps = (skip_pung o skip_ping o pong) (EL j ps)` suffices_by simp[] >>
  `q <= k` by decide_tac >>
  metis_tac[pong_interval_next_pong]
QED

(* Well done! *)

(* Theorem: let ls = path n k; ps = pong_list (FRONT ls) in ALL_DISTINCT ls /\ j < LENGTH ps ==>
            EL j ps = FUNPOW (skip_pung o skip_ping o pong) j (HD ps) *)
(* Proof:
   Let ls = path n k,
       ps = pong_list (FRONT ls),
        f = skip_pung o skip_ping o pong.
   The goal is to show: EL j ps = FUNPOW f j (HD ps)

   By induction j.
   Base: 0 < LENGTH ps ==> EL 0 ps = FUNPOW f 0 (HD ps)
         EL 0 ps
       = HD ps                                 by EL
       = FUNPOW f 0 (HD ps)                    by FUNPOW_0
   Step: j < LENGTH ps ==> EL j ps = FUNPOW f j (HD ps)
     ==> SUC j < LENGTH ps ==> EL (SUC j) ps = FUNPOW f (SUC j) (HD ps)
     Note j < LENGTH ps                        by SUC j < LENGTH ps
       EL (SUC j) ps
     = f (EL j ps)                             by pong_list_path_element_suc
     = f (FUNPOW f j (HD ps))                  by induction hypothesis
     = FUNPOW f (SUC j) (HD ps)                by FUNPOW_SUC
*)
Theorem pong_list_path_element_eqn:
  !n k j. let ls = path n k; ps = pong_list (FRONT ls) in ALL_DISTINCT ls /\ j < LENGTH ps ==>
          EL j ps = FUNPOW (skip_pung o skip_ping o pong) j (HD ps)
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `fs = FRONT ls` >>
  qabbrev_tac `u = (1,n DIV 4,1)` >>
  qabbrev_tac `f = skip_pung o skip_ping o pong` >>
  Induct_on `j` >-
  simp[] >>
  rpt strip_tac >>
  `EL (SUC j) ps = f (EL j ps)` by metis_tac[pong_list_path_element_suc, ADD1] >>
  simp[FUNPOW_SUC]
QED

(* Very good! *)

(* ------------------------------------------------------------------------- *)
(* Hopping Nodes                                                             *)
(* ------------------------------------------------------------------------- *)

(* Define the skip_ping of a pong *)
Definition beyond_pong_def:
   beyond_pong t = (skip_ping o pong) t
End

(* Theorem: tik n /\ ~square n /\ n = windmill t /\ is_pong t ==> beyond_pong t = hopping (SQRT n) t *)
(* Proof:
   Note ~is_ping t                             by pong_not_ping
    and ~is_pung t                             by pong_not_pung
     beyond_pong t
   = beyond_pong (skip_pung t)                 by skip_pung_none
   = (skip_ping o pong) (skip_pung t)          by beyond_pong_def
   = hopping (SQRT n) t                        by hopping_sqrt_eqn
*)
Theorem beyond_pong_eqn:
   !n t. tik n /\ ~square n /\ n = windmill t /\ is_pong t ==> beyond_pong t = hopping (SQRT n) t
Proof
  rpt strip_tac >>
  `~is_ping t /\ ~is_pung t` by simp[pong_not_ping, pong_not_pung] >>
  `skip_pung t = t` by fs[skip_pung_none] >>
  simp[beyond_pong_def, hopping_sqrt_eqn]
QED

(* Theorem: let ls = path n k in p < q /\ q <= k /\ is_pong (EL p ls) /\ is_pong (EL q ls) /\
            (!j. p < j /\ j < q ==> ~is_pong (EL j ls)) ==>
            beyond_pong (EL q ls) = (skip_ping o pong o skip_pung) (beyond_pong (EL p ls) *)
(* Proof:
     beyond_pong (EL q ls)
   = (skip_ping o pong) (EL q ls)                                    by beyond_pong_def
   = (skip_ping o pong) ((skip_pung o skip_ping o pong) (EL p ls))   by pong_interval_next_pong
   = (skip_ping o pong o skip_pung) ((skip_ping o pong) (EL p ls))   by o_ASSOC
   = (skip_ping o pong o skip_pung) (beyond_pong (EL p ls))          by beyond_pong_def
*)
Theorem pong_interval_beyond_pong:
  !n k p q. let ls = path n k in p < q /\ q <= k /\ is_pong (EL p ls) /\ is_pong (EL q ls) /\
            (!j. p < j /\ j < q ==> ~is_pong (EL j ls)) ==>
            beyond_pong (EL q ls) = (skip_ping o pong o skip_pung) (beyond_pong (EL p ls))
Proof
  rw_tac std_ss[] >>
  rw[beyond_pong_def] >>
  assume_tac pong_interval_next_pong >>
  last_x_assum (qspecl_then [`n`, `k`, `p`,`q`] strip_assume_tac) >>
  rfs[]
QED

(* Define the hopping nodes. *)
Definition hop_nodes_def:
   hop_nodes ls = MAP beyond_pong (pong_list (FRONT ls))
End

(*
> EVAL ``hop_nodes (path 61 6)``; = [(7,1,3); (5,3,3)]
> EVAL ``hop_nodes (path 41 6)``; = [(5,1,4); (3,4,2); (5,2,2)]
> EVAL ``hop_nodes (path 97 14)``; = [(9,1,4); (7,4,3); (5,3,6); (7,6,2); (9,2,2)]
*)

(* Theorem: LENGTH (hop_nodes ls) = LENGTH (pong_list (FRONT ls)) *)
(* Proof:
   Let f = beyond_pong.
     LENGTH (hop_nodes ls)
   = LENGTH (MAP f (pong_list (FRONT ls)))     by hop_nodes_def
   = LENGTH (pong_list (FRONT ls))             by LENGTH_MAP
*)
Theorem hop_nodes_length:
  !ls. LENGTH (hop_nodes ls) = LENGTH (pong_list (FRONT ls))
Proof
  simp[hop_nodes_def]
QED

(* Theorem: j < LENGTH (hop_nodes ls) ==>
            EL j (hop_nodes ls) = beyond_pong (EL j (pong_list (FRONT ls))) *)
(* Proof:
   Let f = beyond_pong.
     EL j (hop_nodes ls)
   = EL j (MAP f (pong_list (FRONT ls)))       by hop_nodes_def
   = f (EL j (pong_list (FRONT ls)))           by EL_MAP
*)
Theorem hop_nodes_element:
  !ls j. j < LENGTH (hop_nodes ls) ==>
         EL j (hop_nodes ls) = beyond_pong (EL j (pong_list (FRONT ls)))
Proof
  simp[hop_nodes_def, EL_MAP]
QED

(* Theorem: hop_nodes (path n k) = [] <=> k = 0 *)
(* Proof:
   Let ls = path n k,
        f = beyond_pong.
       hop_nodes ls = []
   <=> MAP f (pong_list (FRONT ls)) = []       by hop_nodes_def
   <=> pong_list (FRONT ls) = []               by MAP_EQ_NIL
   <=> k = 0                                   by pong_list_path_eq_nil
*)
Theorem hop_nodes_path_eq_nil:
  !n k. hop_nodes (path n k) = [] <=> k = 0
Proof
  simp[hop_nodes_def, pong_list_path_eq_nil]
QED

(* Theorem: let ls = path n k in tik n /\ ~square n /\ 0 < k ==>
            HD (hop_nodes ls) = hopping (SQRT n) (HD ls) *)
(* Proof:
   Let ls = path n k,
       ps = pong_list (FRONT ls).
   Note is_pong (HD ls)                        by path_head_is_pong, EL
     so ~is_ping (HD ls)                       by pong_not_ping
     or ~is_pung (HD ls)                       by pong_not_pung
   Thus skip_pung (HD ls) = HD ls              by skip_pung_none
    Now HD ls IN (mills n)                     by path_head, mills_element_trivial_flip, tik n
    and n = windmill (HD ls)                   by mills_element_alt
   Also ps <> []                               by pong_list_path_eq_nil, 0 < k

     HD (hop_nodes ls)
   = HD (MAP beyond_pong ps)                   by hop_nodes_def
   = beyond_pong (HD ps)                       by MAP_HD, ps <> []
   = beyond_pong (HD ls)                       by pong_list_path_head_alt, 0 < k
   = (skip_ping o pong) (HD ls)                by beyond_pong_def
   = (skip_ping o pong) (skip_pung (HD ls))    by above
   = (skip_pong o pong o skip_pung) (HD ls)    by o_THM
   = hopping (SQRT n) (HD ls)                  by hopping_sqrt_eqn
*)
Theorem hop_nodes_path_head:
  !n k. let ls = path n k in tik n /\ ~square n /\ 0 < k ==>
        HD (hop_nodes ls) = hopping (SQRT n) (HD ls)
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `ps = pong_list (FRONT ls)` >>
  `is_pong (HD ls)` by metis_tac[path_head_is_pong, EL] >>
  `skip_pung (HD ls) = HD ls` by fs[skip_pung_none, pong_not_pung] >>
  `ps <> []` by fs[pong_list_path_eq_nil, Abbr`ps`, Abbr`ls`] >>
  `HD (hop_nodes ls) = HD (MAP beyond_pong ps)` by simp[hop_nodes_def, Abbr`ps`] >>
  `_ = beyond_pong (HD ps)` by fs[MAP_HD] >>
  `_ = beyond_pong (HD ls)`  by metis_tac[pong_list_path_head_alt] >>
  `_ = (skip_ping o pong) (HD ls) ` by simp[beyond_pong_def] >>
  `_ = (skip_ping o pong) (skip_pung (HD ls))` by fs[] >>
  `HD ls IN (mills n)` by fs[path_head, mills_element_trivial_flip, Abbr`ls`] >>
  `n = windmill (HD ls)` by fs[mills_element_alt, Abbr`ls`] >>
  `~is_ping (HD ls)` by fs[pong_not_ping] >>
  fs[hopping_sqrt_eqn]
QED

(* Idea: Let ps = pong_list (FRONT (path n k)).
   Note is_pong (EL j ps)           by MEM_FILTER
   If (EL j ps) is not the LAST pong,
      there is the next pong, and cut exists, and cut = beyond_pong (EL j ps)
      show the n = windmill cut, and ~is_ping cut.
   If (EL j ps) is the LAST pong,
      then if flip (LAST ls) = LAST ls, ~is_ping (LAST ls) by not_ping_x_y_y
      in between must be all ping:
         in between must be no pong, yes.
         the one before flip fix is not pung  by pung_next_not_flip_fix
         thus it must be a ping.
         suppose after LAST pong and before this ping there is a pung,
         then there is a pong by pung_to_ping_has_pong, a contradiction.
*)

(* Theorem: let ls = path n k; ns = hop_nodes ls; t = EL j ns in tik n /\
            ALL_DISTINCT ls /\ j + 1 < LENGTH ns ==> n = windmill t /\ ~is_ping t /\ MEM t ls /\ t <> LAST ls *)
(* Proof:
   Let ls = path n k,
       ps = pong_list (FRONT ls),
       ns = hop_nodes ls,
        t = EL j ns.
   The goal is to show: n = windmill t /\ ~is_ping t /\ MEM t ls /\ t <> LAST ls.

   Note LENGTH ns = LENGTH ps                  by hop_nodes_length
     so ?p q. p < q /\ q < k /\ EL p ls = EL j ps /\ EL q ls = EL (j + 1) ps /\
              is_pong (EL p ls) /\ is_pong (EL q ls) /\
              !h. p < h /\ h < q ==> ~is_pong (EL h ls)
                                               by pong_list_pair_in_path
   Thus ?c. p < c /\ c <= q /\ ~is_ping (EL c ls) /\
        !p. c <= p /\ p < q ==> is_pung (EL p ls) /\
        !q. p < q /\ q < c ==> is_ping (EL q ls)
                                               by pong_interval_cut_exists
   Claim: t = EL c ls
   Proof: Note EL (p + 1) ls
             = (zagier o flip) (EL p ls)       by path_element_suc, ADD1
             = pong (EL p ls)                  by zagier_flip_pong
          Also EL c ls
             = skip_ping (EL (p + 1) ls)       by path_skip_ping_thm
             = skip_ping (pong (EL p ls))      by above
             = (skip_pong o pong) (EL p ls)    by o_THM
             = beyond_pong (EL p ls)           by beyond_pong_def
             = beyond_pong (EL j ps)           by above
             = EL j ns = t                     by hop_nodes_element

    Note n = windmill (EL c ls)                by path_element_windmill, tik n
     and LENGTH ls = k + 1                     by path_length
    Thus LAST ls = EL k ls                     by path_last_alt
     and MEM t ls                              by EL_MEM, c <= q < k
     and c <> k                                by c <= q, q < k
      so EL c ls <> EL k ls                    by ALL_DISTINCT_EL_IMP
*)
Theorem hop_nodes_path_element_less:
  !n k j. let ls = path n k; ns = hop_nodes ls; t = EL j ns in tik n /\
          ALL_DISTINCT ls /\ j + 1 < LENGTH ns ==> n = windmill t /\ ~is_ping t /\ MEM t ls /\ t <> LAST ls
Proof
  simp[] >>
  ntac 4 strip_tac >>
  qabbrev_tac `ls = path n k` >>
  qabbrev_tac `ps = pong_list (FRONT ls)` >>
  qabbrev_tac `ns = hop_nodes ls` >>
  qabbrev_tac `t = EL j ns` >>
  `LENGTH ns = LENGTH ps` by fs[hop_nodes_length, Abbr`ns`, Abbr`ps`] >>
  assume_tac pong_list_pair_in_path >>
  last_x_assum (qspecl_then [`n`, `k`, `j`] strip_assume_tac) >>
  rfs[] >>
  assume_tac pong_interval_cut_exists >>
  last_x_assum (qspecl_then [`n`, `k`, `p`, `q`] strip_assume_tac) >>
  rfs[] >>
  `t = EL c ls` by
  (simp[hop_nodes_element, beyond_pong_def, Abbr`t`, Abbr`ns`] >>
  `EL (p + 1) ls = (zagier o flip) (EL p ls)` by fs[path_element_suc, GSYM ADD1, Abbr`ls`] >>
  `_ = pong (EL p ls)` by simp[zagier_flip_pong] >>
  assume_tac path_skip_ping_thm >>
  last_x_assum (qspecl_then [`n`, `k`, `p+1`, `c`] strip_assume_tac) >>
  rfs[]) >>
  `n = windmill t` by fs[path_element_windmill, Abbr`ls`] >>
  `LENGTH ls = k + 1 /\ LAST ls = EL k ls` by fs[path_length, path_last_alt, Abbr`ls`] >>
  `MEM t ls` by fs[EL_MEM] >>
  fs[ALL_DISTINCT_EL_IMP]
QED

(* Theorem: let ls = path n k; ns = hop_nodes ls; t = EL j ns in tik n /\ ~square n /\
             ALL_DISTINCT ls /\ j + 1 = LENGTH ns /\ flip (LAST ls) = LAST ls *)
(* Proof:
   Let ls = path n k,
       ps = pong_list (FRONT ls),
       ns = hop_nodes ls,
        t = EL j ns.
   The goal is to show: n = windmill t /\ ~is_ping t /\ MEM t ls /\ t <> LAST ls.

   Note LAST ls = EL k ls                      by path_last_alt
    and n = windmill (EL k ls)                 by path_element_windmill, tik n
    and ~is_ping (LAST ls)                     by path_last_not_ping
   Also ls <> []                               by path_not_nil
     so MEM (LAST ls) ls                       by LAST_MEM

   Note LENGTH ns = LENGTH ps                  by hop_nodes_length
     so ?p. p < k /\ EL j ps = EL p ls /\ is_pong (EL p ls)
                                               by pong_list_path_element, [1]
   Claim: !h. p < h /\ h < k ==> ~is_pong (EL h ls)
   Proof: By contradiction, suppose is_pong (EL h ls).
          Note 0 < LENGTH ps                   by j + 1 = LENGTH ps
            so ps <> []                        by LENGTH_EQ_0
          Thus EL j ps = LAST ps               by LAST_EL
          Note ps = FILTER is_pong fs          by pong_list_def
           and ls <> []                        by path_not_nil
           ==> ALL_DISTINCT fs                 by ALL_DISTINCT_FRONT
          Note LENGTH fs = k                   by path_front_length
           Let x = EL p ls.
          Then x = EL p fs                     by FRONT_EL
           and MEM x fs                        by EL_MEM, p < k
           ==> ?l1 l2. fs = l1 ++ x::l2        by MEM_SPLIT
          Thus FILTER is_pong l2 = []          by FILTER_LAST_IFF

          To show: (EL h ls) in l2,
          Note p = LENGTH l1                   by ALL_DISTINCT_EL_APPEND
           and EL h ls = EL h fs               by FRONT_EL
                       = EL (h - p) (x::l2)    by EL_APPEND_EQN
                       = EL (h - p - 1) l2     by EL_TAIL
          Thus MEM (EL h ls) l2                by EL_MEM
            so ~is_pong (EL h ls)              by FILTER_EQ_NIL, EVERY_MEM
          This contradicts is_pong (EL h ls).

   With claim
   Then !h. p < h /\ h < k ==> is_ping (EL h ls)
                                               by path_last_pong_to_flip_fix, [1]
   Note EL (p + 1) ls
      = (zagier o flip) (EL p ls)              by path_element_suc, ADD1
      = pong (EL p ls)                         by zagier_flip_pong

   Also EL k ls
      = skip_ping (EL (p + 1) ls)              by path_skip_ping_thm, ~is_ping (LAST ls)
      = skip_ping (pong (EL p ls))             by above
      = (skip_pong o pong) (EL p ls)           by o_THM
      = beyond_pong (EL p ls)                  by beyond_pong_def
      = beyond_pong (EL j ps)                  by above
      = EL j ns = t                            by hop_nodes_element
*)
Theorem hop_nodes_path_element_last:
  !n k j. let ls = path n k; ns = hop_nodes ls; t = EL j ns in tik n /\ ~square n /\
          ALL_DISTINCT ls /\ j + 1 = LENGTH ns /\ flip (LAST ls) = LAST ls ==>
          n = windmill t /\ ~is_ping t /\ MEM t ls /\ t = LAST ls
Proof
  simp[] >>
  ntac 4 strip_tac >>
  qabbrev_tac `ls = path n k` >>
  qabbrev_tac `ps = pong_list (FRONT ls)` >>
  qabbrev_tac `ns = hop_nodes ls` >>
  qabbrev_tac `t = EL j ns` >>
  `EL k ls = LAST ls` by fs[path_last_alt, Abbr`ls`] >>
  `n = windmill (EL k ls)` by fs[path_element_windmill, Abbr`ls`] >>
  `~is_ping (LAST ls)` by metis_tac[path_last_not_ping] >>
  `ls <> []` by fs[path_not_nil, Abbr`ls`] >>
  `MEM (LAST ls) ls` by simp[LAST_MEM] >>
  `LENGTH ns = LENGTH ps` by fs[hop_nodes_length, Abbr`ns`, Abbr`ps`] >>
  `j < LENGTH ps` by decide_tac >>
  `?p. p < k /\ EL j ps = EL p ls /\ is_pong (EL p ls)` by metis_tac[pong_list_path_element] >>
  `!h. p < h /\ h < k ==> ~is_pong (EL h ls)` by
  (rpt strip_tac >>
  qabbrev_tac `fs = FRONT ls` >>
  `0 < LENGTH ps /\ j = PRE (LENGTH ps)` by decide_tac >>
  `ps <> [] /\ EL j ps = LAST ps` by metis_tac[LAST_EL, LENGTH_EQ_0, NOT_ZERO] >>
  `ps = FILTER is_pong fs` by simp[pong_list_def, Abbr`ps`, Abbr`fs`] >>
  `ls <> []` by fs[path_not_nil, Abbr`ls`] >>
  `ALL_DISTINCT fs` by fs[ALL_DISTINCT_FRONT, Abbr`fs`] >>
  `LENGTH fs = k` by fs[path_front_length, Abbr`ls`, Abbr`fs`] >>
  `EL p ls = EL p fs` by fs[FRONT_EL, Abbr`fs`] >>
  qabbrev_tac `x = EL p ls` >>
  `MEM x fs` by metis_tac[EL_MEM] >>
  `?l1 l2. fs = l1 ++ x::l2` by simp[GSYM MEM_SPLIT] >>
  `FILTER is_pong l2 = []` by metis_tac[FILTER_LAST_IFF] >>
  `fs = l1 ++ [x] ++ l2` by fs[] >>
  `p = LENGTH l1` by metis_tac[ALL_DISTINCT_EL_APPEND] >>
  `~(h < p) /\ h - p <> 0` by decide_tac >>
  `EL h ls = EL h fs` by fs[FRONT_EL, Abbr`fs`] >>
  `_ = EL (h - p) (x::l2)` by metis_tac[EL_APPEND_EQN] >>
  `_ = EL (h - p - 1) l2` by metis_tac[EL_TAIL] >>
  `MEM (EL h ls) l2` by fs[EL_MEM] >>
  fs[FILTER_EQ_NIL, EVERY_MEM]) >>
  `!h. p < h /\ h < k ==> is_ping (EL h ls)` by metis_tac[path_last_pong_to_flip_fix, LESS_EQ_REFL] >>
  `EL (p + 1) ls = (zagier o flip) (EL p ls)` by fs[path_element_suc, GSYM ADD1, Abbr`ls`] >>
  `_ = pong (EL p ls)` by simp[zagier_flip_pong] >>
  assume_tac path_skip_ping_thm >>
  last_x_assum (qspecl_then [`n`, `k`, `p+1`,`k`] strip_assume_tac) >>
  rfs[] >>
  fs[hop_nodes_element, beyond_pong_def, Abbr`t`, Abbr`ns`]
QED

(* Very good result! *)

(* Theorem: let ls = path n k; ns = hop_nodes ls; t = EL j ns in tik n /\ ~square n /\
            ALL_DISTINCT ls /\ j < LENGTH ns /\ flip (LAST ls) = LAST ls ==>
            n = windmill t /\ ~is_ping t /\ MEM t ls /\ (t = LAST ls <=> j + 1 = LENGTH ns) *)
(* Proof:
   Let ls = path n k,
       ns = hop_nodes fs
        t = EL j ns.
   The goal is to show: n = windmill t /\ ~is_ping t /\ MEM t ls /\ (t = LAST ls <=> j + 1 = LENGTH ns).

   Note j < LENGTH ns <=> j + 1 <= LENGTH ns   by LESS_EQ, ADD1
   If j + 1 < LENGTH ns, this is true          by hop_nodes_path_element_less
   If j + 1 = LENGTH ns, this is true          by hop_nodes_path_element_last
*)
Theorem hop_nodes_path_element_thm:
  !n k j. let ls = path n k; ns = hop_nodes ls; t = EL j ns in tik n /\ ~square n /\
          ALL_DISTINCT ls /\ j < LENGTH ns /\ flip (LAST ls) = LAST ls ==>
          n = windmill t /\ ~is_ping t /\ MEM t ls /\ (t = LAST ls <=> j + 1 = LENGTH ns)
Proof
  simp[] >>
  ntac 4 strip_tac >>
  qabbrev_tac `ls = path n k` >>
  qabbrev_tac `ns = hop_nodes ls` >>
  qabbrev_tac `t = EL j ns` >>
  `j + 1 < LENGTH ns \/ j + 1 = LENGTH ns` by decide_tac >| [
    assume_tac hop_nodes_path_element_less >>
    last_x_assum (qspecl_then [`n`, `k`, `j`] strip_assume_tac) >>
    rfs[],
    assume_tac hop_nodes_path_element_last >>
    last_x_assum (qspecl_then [`n`, `k`, `j`] strip_assume_tac) >>
    rfs[]
  ]
QED

(* Theorem: let ls = path n k; ns = hop_nodes ls in
            tik n /\ ~square n /\ ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls /\ j < LENGTH ns ==>
            EL j ns = FUNPOW (hopping (SQRT n)) (j + 1) (HD ls) *)
(* Proof:
   Let ls = path n k,
       ps = pong_list (FRONT ls),
        f = hopping (SQRT n).
   The goal is to show: EL j ns = FUNPOW f (j + 1) (HD ls)

   Note 0 < LENGTH ps                          by j < LENGTH ns
     so ns <> []                               by LENGTH_EQ_0
     or 0 < k                                  by hop_nodes_path_eq_nil

   By induction on j.
   Base: 0 < LENGTH ns ==> EL 0 ns = FUNPOW f (0 + 1) (HD ls)
         EL 0 ns
       = HD ns                                 by EL
       = f (HD ls)                             by hop_nodes_path_head, 0 < k
       = FUNPOW f 1 (HD ls)                    by FUNPOW_1
   Step: j < LENGTH ns ==> EL j ns = FUNPOW f (j + 1) (HD ls)
     ==> SUC j < LENGTH ns ==> EL (SUC j) ns = FUNPOW f (SUC j + 1) (HD ls)
      Note j < LENGTH ns                       by SUC j < LENGTH ps
       and LENGTH ns = LENGTH ps               by hop_nodes_length
       and n = windmill (EL j ns) /\
           ~is_ping (EL j ns)                  by hop_nodes_path_element_thm, [1]

          EL (SUC j) ns
        = beyond_pong (EL (SUC j) ps)          by hop_nodes_element
        = beyond_pong ((skip_pung o skip_ping o pong) (EL j ps))
                                               by pong_list_path_element_suc, SUC j < LENGTH ps
        = beyond_pong (skip_pung (beyond_pong (EL j ps)))
                                               by beyond_pong_def
        = beyond_pong (skip_pung (EL j ns))    by hop_nodes_element
        = (skip_ping o pong) (skip_pung (EL j ns))
                                               by beyond_pong_def
        = (skip_ping o pong o skip_pung) (EL j ns))
                                               by composition
        = f (EL j ns))                         by hopping_sqrt_eqn, [1]
        = f (FUNPOW f (j + 1) (HD ls))         by induction hypothesis
        = FUNPOW f (SUC j + 1) (HD ls)         by FUNPOW_SUC, ADD
*)
Theorem hop_nodes_path_element_eqn:
  !n k j. let ls = path n k; ns = hop_nodes ls in
          tik n /\ ~square n /\ ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls /\ j < LENGTH ns ==>
          EL j ns = FUNPOW (hopping (SQRT n)) (j + 1) (HD ls)
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `ps = pong_list (FRONT ls)` >>
  qabbrev_tac `f = hopping (SQRT n)` >>
  `0 < LENGTH ns` by decide_tac >>
  `ns <> [] /\ 0 < k` by metis_tac[hop_nodes_path_eq_nil, LENGTH_EQ_0, NOT_ZERO] >>
  Induct_on `j` >| [
    rw[] >>
    metis_tac[hop_nodes_path_head, FUNPOW_1],
    rpt strip_tac >>
    `LENGTH ns = LENGTH ps` by fs[hop_nodes_length, Abbr`ns`, Abbr`ps`] >>
    `j < LENGTH ns` by decide_tac >>
    `n = windmill (EL j ns) /\ ~is_ping (EL j ns)` by metis_tac[hop_nodes_path_element_thm] >>
    `EL (SUC j) ns = beyond_pong (EL (SUC j) ps) ` by fs[hop_nodes_element, Abbr`ns`, Abbr`ps`] >>
    `_ = beyond_pong ((skip_pung o skip_ping o pong) (EL j ps))` by metis_tac[pong_list_path_element_suc, ADD1] >>
    `_ = beyond_pong (skip_pung (EL j ns))` by simp[GSYM beyond_pong_def, GSYM hop_nodes_element, Abbr`ns`, Abbr`ps`] >>
    `_ = (skip_ping o pong) (skip_pung (EL j ns))` by simp[beyond_pong_def] >>
    `_ = (skip_ping o pong o skip_pung) (EL j ns)` by simp[] >>
    `_ = f (EL j ns)` by fs[hopping_sqrt_eqn, Abbr`f`] >>
    `_ = f (FUNPOW f (j + 1) (HD ls))` by fs[] >>
    metis_tac[FUNPOW_SUC, ADD]
  ]
QED

(* Theorem: let ls = path n k; ns = hop_nodes ls in
            tik n /\ ~square n /\ ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls /\ 0 < k ==>
            LAST ns = LAST ls /\ LAST ls = FUNPOW (hopping (SQRT n)) (LENGTH ns) (HD ls) *)
(* Proof:
   Let ls = path n k,
       ns = hop_nodes ls,
        h = LENGTH ns.
   The goal is to show: LAST ns = LAST ls /\ LAST ls = FUNPOW (hopping (SQRT n)) h (HD ls).

   Note ns <> []                               by hop_nodes_path_eq_nil, 0 < k
     so 0 < h                                  by LENGTH_EQ_0, NOT_ZERO
    Let j = h - 1, then j = PRE h.
        LAST ns
      = EL j ns                                by LAST_EL, ns <> []
      = LAST ls                                by hop_nodes_path_element_thm, j + 1 = h
   Also EL j ns
      = FUNPOW (hopping (SQRT n)) h (HD ls)    by hop_nodes_path_element_eqn
*)
Theorem hop_nodes_path_last:
  !n k. let ls = path n k; ns = hop_nodes ls in
        tik n /\ ~square n /\ ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls /\ 0 < k ==>
        LAST ns = LAST ls /\ LAST ls = FUNPOW (hopping (SQRT n)) (LENGTH ns) (HD ls)
Proof
  simp[] >>
  ntac 3 strip_tac >>
  qabbrev_tac `ls = path n k` >>
  qabbrev_tac `ns = hop_nodes ls` >>
  qabbrev_tac `h = LENGTH ns` >>
  `ns <> [] /\ 0 < h` by metis_tac[hop_nodes_path_eq_nil, LENGTH_EQ_0, NOT_ZERO] >>
  `h = h - 1 + 1 /\ h - 1 = PRE h /\ h - 1 < h` by decide_tac >>
  qabbrev_tac `j = h - 1` >>
  `LAST ns = EL j ns` by metis_tac[LAST_EL] >>
  metis_tac[hop_nodes_path_element_thm, hop_nodes_path_element_eqn]
QED

(* A very clean result. *)

(* ------------------------------------------------------------------------- *)
(* Hopping for tik primes.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: let s = mills n; u = (1,1,n DIV 4) in tik n /\ prime n ==>
            ~square n /\ FINITE s /\ zagier involute s /\ flip involute s /\
            fixes zagier s = {u} /\ ODD (iterate_period (zagier o flip) u) *)
(* Proof:
   Let u = (1,1,n DIV 4),
       p = iterate_period (zagier o flip) u,
       s = mills n.
   Note ~square n                  by prime_non_square
     so FINITE s                   by mills_finite_non_square
    and zagier involute s          by zagier_involute_mills_prime
    and flip involute s            by flip_involute_mills
   Also fixes zagier s = {u}       by zagier_fixes_prime, tik n /\ prime n
   Thus ODD p                      by involute_involute_fix_sing_period_odd
*)
Theorem tik_prime_property:
  !n. let s = mills n; u = (1,1,n DIV 4) in tik n /\ prime n ==>
      ~square n /\ FINITE s /\ zagier involute s /\ flip involute s /\
      fixes zagier s = {u} /\ ODD (iterate_period (zagier o flip) u)
Proof
  simp[] >>
  ntac 2 strip_tac >>
  qabbrev_tac `u = (1,1,n DIV 4)` >>
  qabbrev_tac `p = iterate_period (zagier o flip) u` >>
  qabbrev_tac `s = mills n` >>
  `~square n` by simp[prime_non_square] >>
  `FINITE s` by fs[mills_finite_non_square, Abbr`s`] >>
  `zagier involute s` by metis_tac[zagier_involute_mills_prime] >>
  `flip involute s` by metis_tac[flip_involute_mills] >>
  `fixes zagier s = {u}` by fs[zagier_fixes_prime, Abbr`s`, Abbr`u`] >>
  drule_then strip_assume_tac involute_involute_fix_sing_period_odd >>
  last_x_assum (qspecl_then [`zagier`, `flip`, `p`, `u`] strip_assume_tac) >>
  rfs[]
QED

(* Theorem: tik n /\ prime n ==> ODD (iterate_period (zagier o flip) (1,1,n DIV 4)) *)
(* Proof: by tik_prime_property. *)
Theorem tik_prime_iterate_period_odd:
  !n. tik n /\ prime n ==> ODD (iterate_period (zagier o flip) (1,1,n DIV 4))
Proof
  metis_tac[tik_prime_property]
QED

(* Idea: for ls = path n k, LAST ls is iterate (zagier o flip) of zagier-fix to half period. *)

(* Theorem: let ls = path n k; u = (1,1,n DIV 4); p = iterate_period (zagier o flip) u in
            k = 1 + HALF p ==> LAST ls = FUNPOW (zagier o flip) (HALF p) u *)
(* Proof:
   Note ls <> []                   by path_not_nil
    and 0 < k                      by k = 1 + HALF p

     LAST ls
   = EL k ls                       by path_last_alt
   = EL (1 + HALF p) ls            by k = 1 + HALF p
   = EL (SUC (HALF p)) ls          by ADD1
   = EL (HALF p) (TL ls)           by EL
   = FUNPOW (zagier o flip) (HALF p) u
                                   by path_tail_element, HALF p < k
*)
Theorem path_last_at_half_period:
  !n k. let ls = path n k; u = (1,1,n DIV 4); p = iterate_period (zagier o flip) u in
        k = 1 + HALF p ==> LAST ls = FUNPOW (zagier o flip) (HALF p) u
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `k = 1 + HALF p` >>
  `ls <> []` by fs[path_not_nil, Abbr`ls`] >>
  `0 < k /\ HALF p < k` by fs[Abbr`k`] >>
  `LAST ls = EL (SUC (HALF p)) ls` by fs[path_last_alt, ADD1, Abbr`ls`, Abbr`k`] >>
  `_ = EL (HALF p) (TL ls)` by simp[EL] >>
  fs[path_tail_element, Abbr`ls`, Abbr`u`]
QED

(* Idea: for ls = path n k of a tik prime, flip (LAST ls) = (LAST ls) when k = 1 + HALF (iterate period). *)

(* Theorem: let ls = path n k in tik n /\ prime n /\
            k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) ==> flip (LAST ls) = LAST ls *)
(* Proof:
   Let u = (1,1,n DIV 4),
       p = iterate_period (zagier o flip) u,
       k = 1 + HALF p,
       s = mills n,
       t = FUNPOW (zagier o flip) (HALF p) u.
   Note FINITE s /\ zagier involute s /\ flip involute s /\
        fixes zagier s = {u} /\ ODD p          by tik_prime_property

   Thus u IN fixes zagier s                    by IN_SING
    ==> t IN fixes flip s                      by involute_involute_fix_orbit_fix_odd
    But t = LAST ls                            by path_last_at_half_period
     so flip (LAST ls) = LAST ls               by flip_fixes_alt
*)
Theorem tik_prime_path_last_flip_fix:
  !n k. let ls = path n k in tik n /\ prime n /\
        k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) ==> flip (LAST ls) = LAST ls
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `u = (1,1,n DIV 4)` >>
  qabbrev_tac `p = iterate_period (zagier o flip) u` >>
  qabbrev_tac `k = 1 + HALF p` >>
  qabbrev_tac `s = mills n` >>
  qabbrev_tac `t = FUNPOW (zagier o flip) (HALF p) u` >>
  `LAST ls = t` by metis_tac[path_last_at_half_period] >>
  assume_tac tik_prime_property >>
  last_x_assum (qspecl_then [`n`] strip_assume_tac) >>
  rfs[] >>
  `t IN fixes flip s` by fs[involute_involute_fix_orbit_fix_odd, Abbr`t`, Abbr`p`, Abbr`u`] >>
  fs[flip_fixes_alt]
QED

(* Idea: for ls = path n k of a tik prime, flip (EL j ls) <> (EL j ls) when j < k = 1 + HALF (iterate period). *)

(* Theorem: let ls = path n k in tik n /\ prime n /\
            k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) /\
            0 < j /\ j < k ==> flip (EL j ls) <> EL j ls *)
(* Proof:
   Let u = (1,1,n DIV 4),
       p = iterate_period (zagier o flip) u,
       k = 1 + HALF p,
       s = mills n,
       t = FUNPOW (zagier o flip) (HALF p) u.
   Note FINITE s /\ zagier involute s /\ flip involute s /\
        fixes zagier s = {u} /\ ODD p          by tik_prime_property

   By contradiction, suppose flip (EL j ls) = EL j ls.
   Then EL j ls IN fixes flip s                by flip_fixes_alt
   Note 0 < p                                  by ODD_POS
     so HALF p < p                             by HALF_LT
     or k = 1 + HALF p <= p

   Let h = j - 1                               by 0 < j
   Then j = SUC h, and h < j
        EL j ls
      = EL h (TL ls)                           by EL
      = FUNPOW (zagier o flip) h u             by path_tail_element, h < k
    ==> h = HALF p                             by involute_involute_fix_odd_period_fix, h < p
     or j - 1 = HALF p,
     so j = 1 + HALF p = k.
    This contradicts j < k.
*)
Theorem tik_prime_path_not_flip_fix:
  !n k j. let ls = path n k in tik n /\ prime n /\
          k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) /\
          0 < j /\ j < k ==> flip (EL j ls) <> EL j ls
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `u = (1,1,n DIV 4)` >>
  qabbrev_tac `p = iterate_period (zagier o flip) u` >>
  qabbrev_tac `k = 1 + HALF p` >>
  qabbrev_tac `s = mills n` >>
  assume_tac tik_prime_property >>
  last_x_assum (qspecl_then [`n`] strip_assume_tac) >>
  rfs[] >>
  spose_not_then strip_assume_tac >>
  `EL j ls IN s` by fs[path_element_in_mills, Abbr`s`, Abbr`ls`] >>
  `EL j ls IN fixes flip s` by fs[flip_fixes_alt, Abbr`s`] >>
  `j = SUC (j - 1)` by decide_tac >>
  qabbrev_tac `h = j - 1` >>
  `EL j ls = EL h (TL ls)` by metis_tac[EL] >>
  `_ = FUNPOW (zagier o flip) h u` by fs[path_tail_element, Abbr`h`, Abbr`u`, Abbr`ls`] >>
  `FUNPOW (zagier o flip) h u IN fixes flip s` by metis_tac[] >>
  `0 < p` by simp[ODD_POS] >>
  `k <= p` by metis_tac[HALF_LT, LESS_EQ, ADD1] >>
  drule_then strip_assume_tac involute_involute_fix_odd_period_fix >>
  last_x_assum (qspecl_then [`zagier`, `flip`, `p`, `u`, `h`] strip_assume_tac) >>
  rfs[] >>
  `j = 1 + HALF p` by decide_tac >>
  fs[Abbr`k`]
QED

(* Idea: for ls = path n k of a tik prime, flip (EL j ls) = (EL j ls) iff j = k = 1 + HALF (iterate period). *)

(* Theorem: let ls = path n k in tik n /\ prime n /\
          k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) /\
          0 < j /\ j <= k ==> (flip (EL j ls) = EL j ls <=> j = k) *)
(* Proof:
   Let ls = path n k.
   If part: flip (EL j ls) = EL j ls ==> j = k
      By contradiction, assume j <> k.
      Then j < k                               by j <= k
      Thus flip (EL j ls) <> EL j ls           by tik_prime_path_not_flip_fix
      This contradicts flip (EL j ls) = EL j ls.

   Only-if part: j = k ==> flip (EL j ls) = EL j ls
      Note LAST ls = EL k ls                   by path_last_alt
      Thus flip (EL j ls) = EL j ls            by tik_prime_path_last_flip_fix
*)
Theorem tik_prime_path_flip_fix_iff:
  !n k j. let ls = path n k in tik n /\ prime n /\
          k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) /\
          0 < j /\ j <= k ==> (flip (EL j ls) = EL j ls <=> j = k)
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `u = (1,1,n DIV 4)` >>
  qabbrev_tac `p = iterate_period (zagier o flip) u` >>
  qabbrev_tac `k = 1 + HALF p` >>
  rw[EQ_IMP_THM] >| [
    assume_tac tik_prime_path_not_flip_fix >>
    last_x_assum (qspecl_then [`n`, `k`, `j`] strip_assume_tac) >>
    rfs[],
    `LAST ls = EL j ls` by simp[path_last_alt, Abbr`ls`] >>
    assume_tac tik_prime_path_last_flip_fix >>
    last_x_assum (qspecl_then [`n`, `j`] strip_assume_tac) >>
    rfs[]
  ]
QED

(* Theorem: let ls = path n k in tik n /\ prime n /\
          k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) /\
          MEM t ls /\ flip (HD ls) <> HD ls ==> (flip t = t <=> t = LAST ls) *)
(* Proof:
   Let ls = path n k.
   Note LENGTH ls = k + 1                      by path_length
    and ?j. j < k + 1 /\ t = EL j ls           by MEM_EL
    and LAST ls = EL k ls                      by path_last_alt

   If part: flip (EL j ls) = EL j ls ==> EL j ls = EL k ls
      By contradiction, assume EL j ls <> EL k ls
      Then j < k                               by j <> k, j <= k
      Thus flip (EL j ls) <> EL j ls           by tik_prime_path_not_flip_fix
      This contradicts flip (EL j ls) = EL j ls.

   Only-if part: EL j ls = EL k ls ==> flip (EL j ls) = EL j ls
      Note EL k ls = LAST ls                   by above
       and flip (LAST ls) = LAST ls            by tik_prime_path_last_flip_fix
*)
Theorem tik_prime_path_flip_fix_iff_alt:
  !n k t. let ls = path n k in tik n /\ prime n /\
          k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) /\
          MEM t ls /\ flip (HD ls) <> HD ls ==> (flip t = t <=> t = LAST ls)
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `u = (1,1,n DIV 4)` >>
  qabbrev_tac `p = iterate_period (zagier o flip) u` >>
  qabbrev_tac `k = 1 + HALF p` >>
  `LENGTH ls = k + 1` by fs[path_length, Abbr`ls`] >>
  `?j. j < k + 1 /\ t = EL j ls` by metis_tac[MEM_EL] >>
  `LAST ls = EL k ls` by fs[path_last_alt, Abbr`ls`] >>
  rw[EQ_IMP_THM] >| [
    spose_not_then strip_assume_tac >>
    `j <> 0 /\ j <> k` by metis_tac[EL] >>
    assume_tac tik_prime_path_not_flip_fix >>
    last_x_assum (qspecl_then [`n`, `k`, `j`] strip_assume_tac) >>
    rfs[],
    metis_tac[tik_prime_path_last_flip_fix]
  ]
QED

(* Theorem: let ls = path n k in tik n /\ prime n /\
            k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) ==>
            WHILE (\t. flip t <> t) (hopping (SQRT n)) (HD ls) = LAST ls *)
(* Proof:
   Let ls = path n k,
        p = iterate_period (zagier o flip) (1,1,n DIV 4),
        k = 1 + HALF p,
        g = \t. flip t <> t,
        b = hopping (SQRT n).
   The goal is to show: WHILE g b (HD ls) = LAST ls

   If n = 5,
      Then p = 1                               by tik_iterate_period_eq_1
        so k = 1 + HALF 1 = 1                  by arithmetic
       and ls = path 5 1
              = [(1,5 DIV 4,1); (1,1,5 DIV 4)] by path_1
              = [(1,1,1); (1,1,1)]             by arithmetic
      Also flip (1,1,1) = (1,1,1)              by flip_fix
        so ~g (HD ls)                          by applying g
      Thus WHILE g b (HD ls) = HD ls           by iterate_while_none
                             = LAST ls         by HD, LAST_DEF
   If n <> 5,
      Let ns = hop_nodes ls,
           h = LENGTH ns.
      Note ~square n                           by prime_non_square
       and flip (LAST ls) = LAST ls            by tik_prime_path_last_flip_fix
       and flip (HD ls) <> HD ls               by tik_path_head_flip_fix, n <> 5
       and ALL_DISTINCT ls                     by path_all_distinct, n <> 5
      Also 0 < k                               by k = 1 + HALF p
      Thus LAST ns = LAST ls /\ LAST ls = FUNPOW b h (HD ls)
                                               by hop_nodes_path_last, [1]

      The goal becomes: WHILE g b (HD ls) = FUNPOW b h (HD ls)

      By iterate_while_thm, this is to show:
      (1) !j. j < h ==> g (FUNPOW b j (HD ls))
          If j = 0,
             Then FUNPOW b 0 (HD ls) = HD ls   by FUNPOW_0
              and flip (HD ls) <> HD ls        by above
               so g (HD ls)                    by applying g
          Otherwise, 0 < j,
             Let q = EL (j - 1) ns.
             Then q = FUNPOW b j (HD ls)       by hop_nodes_path_element_eqn
              and q <> LAST ls /\ MEM q ls     by hop_nodes_path_element_thm
             Thus flip q <> q                  by tik_prime_path_flip_fix_iff_alt
               or g (FUNPOW b j (HD ls))       by applying g
       (2) ~g (FUNPOW b h (HD ls))
           Note flip (LAST ls) = LAST ls       by tik_prime_path_last_flip_fix
            and LAST ls = FUNPOW b h (HD ls)   by above [1]
           Hence true                          by applying g
*)
Theorem tik_prime_path_hopping_while_thm:
  !n k. let ls = path n k in tik n /\ prime n /\
        k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) ==>
        WHILE (\t. flip t <> t) (hopping (SQRT n)) (HD ls) = LAST ls
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `p = iterate_period (zagier o flip) (1,1,n DIV 4)` >>
  qabbrev_tac `k = 1 + HALF p` >>
  qabbrev_tac `g = \t. flip t <> t` >>
  qabbrev_tac `b = hopping (SQRT n)` >>
  Cases_on `n = 5` >| [
    `p = 1` by fs[tik_iterate_period_eq_1, Abbr`p`] >>
    `k = 1` by fs[Abbr`k`] >>
    `ls = [(1,1,1); (1,1,1)]` by rfs[path_1, Abbr`ls`] >>
    `HD ls = LAST ls` by metis_tac[HD, LAST_DEF] >>
    `~g (1,1,1)` by simp[flip_fix, Abbr`g`] >>
    rfs[iterate_while_none],
    qabbrev_tac `ns = hop_nodes ls` >>
    qabbrev_tac `h = LENGTH ns` >>
    `~square n` by simp[prime_non_square] >>
    `flip (LAST ls) = LAST ls` by metis_tac[tik_prime_path_last_flip_fix] >>
    `flip (HD ls) <> HD ls` by metis_tac[tik_path_head_flip_fix] >>
    `ALL_DISTINCT ls` by fs[path_all_distinct, Abbr`ls`] >>
    `0 < k` by fs[Abbr`k`] >>
    `LAST ns = LAST ls /\ LAST ls = FUNPOW b h (HD ls)` by metis_tac[hop_nodes_path_last] >>
    simp[] >>
    irule iterate_while_thm >>
    rw[Abbr`g`] >| [
      `j = 0 \/ 0 < j` by decide_tac >-
      simp[] >>
      assume_tac hop_nodes_path_element_eqn >>
      last_x_assum (qspecl_then [`n`, `k`, `j-1`] strip_assume_tac) >>
      rfs[] >>
      assume_tac hop_nodes_path_element_thm >>
      last_x_assum (qspecl_then [`n`, `k`, `j-1`] strip_assume_tac) >>
      rfs[] >>
      qabbrev_tac `q = FUNPOW b j (HD ls)` >>
      assume_tac tik_prime_path_flip_fix_iff_alt >>
      last_x_assum (qspecl_then [`n`, `k`, `q`] strip_assume_tac) >>
      rfs[],
      metis_tac[]
    ]
  ]
QED

(* The most desired theorem. *)

(* Theorem: tik n /\ prime n ==> two_sq_hop n IN fixes flip (mills n) *)
(* Proof:
   Let s = mills n,
       f = hopping (SQRT n),
       u = (1,1,n DIV 4),
       v = (1,n DIV 4,1).
   By two_sq_hop_def, this is to show: WHILE ($~ o found) f v IN fixes flip s

   Note (~) o found = (\t. flip t <> t)        by found_def, flip_def, FUN_EQ_THM
   Thus the goal is: WHILE (\t. flip t <> t) f v IN fixes flip s

   Let p = iterate_period (zagier o flip) u,
       k = 1 + HALF p,
       ls = path n k.
   Then HD ls = v                              by path_head
    and WHILE (\t. flip t <> t) f v = LAST ls  by tik_prime_path_hopping_while_thm

    Now LAST ls = EL k ls                      by path_last_alt
     so LAST ls IN s                           by path_element_in_mills
    and flip (LAST ls) = LAST ls               by tik_prime_path_last_flip_fix
    ==> LAST ls IN fixes flip s                by flip_fixes_alt
*)
Theorem two_sq_hop_thm:
  !n. tik n /\ prime n ==> two_sq_hop n IN fixes flip (mills n)
Proof
  rw[two_sq_hop_def] >>
  qabbrev_tac `s = mills n` >>
  qabbrev_tac `f = hopping (SQRT n)` >>
  qabbrev_tac `u = (1,1,n DIV 4)` >>
  qabbrev_tac `v = (1,n DIV 4,1)` >>
  `(~) o found = \t. flip t <> t` by
  (rw[FUN_EQ_THM] >>
  `?x y z. t = (x,y,z)` by rw[triple_parts] >>
  simp[found_def, flip_def]) >>
  simp[] >>
  qabbrev_tac `p = iterate_period (zagier o flip) u` >>
  qabbrev_tac `k = 1 + HALF p` >>
  qabbrev_tac `ls = path n k` >>
  `HD ls = v` by fs[path_head, Abbr`ls`, Abbr`v`] >>
  `LAST ls = EL k ls` by simp[path_last_alt, Abbr`ls`] >>
  `LAST ls IN s` by fs[path_element_in_mills, Abbr`ls`, Abbr`s`] >>
  `WHILE (\t. flip t <> t) f v = LAST ls` by metis_tac[tik_prime_path_hopping_while_thm] >>
  `flip (LAST ls) = LAST ls` by metis_tac[tik_prime_path_last_flip_fix] >>
  rfs[flip_fixes_alt]
QED

(* Finally!! This shows the correctness of the hopping algorithm.  *)

(* Extract the two squares of hopping algorithm. *)
Definition two_squares_hop_def:
    two_squares_hop n = let (x,y,z) = two_sq_hop n in (x, y + z)
End

(*
> EVAL ``two_squares_hop 5``; = (1,2)
> EVAL ``two_squares_hop 13``; = (3,2)
> EVAL ``two_squares_hop 17``; = (1,4)
> EVAL ``two_squares_hop 29``; = (5,2)
> EVAL ``two_squares_hop 97``;  = (9,4)
> EVAL ``MAP two_squares_hop [5; 13; 17; 29; 37; 41; 53; 61; 73; 89; 97]``;
= [(1,2); (3,2); (1,4); (5,2); (1,6); (5,4); (7,2); (5,6); (3,8); (5,8); (9,4)]: thm
*)

(* Theorem: tik n /\ prime n ==> let (u,v) = two_squares_hop n in (n = u ** 2 + v ** 2) *)
(* Proof:
   Let t = two_sq_hop n.
   Then t IN fixes flip (mills n)        by two_sq_hop_thm
    and ?x y z. t = (x,y,z)              by triple_parts
    ==> (x,y,z) IN mills n /\ (y = z)    by flip_fixes_alt, flip_fix
     so n = windmill (x, y, y)           by mills_element
          = x ** 2 + (2 * y) ** 2        by windmill_by_squares
          = x ** 2 + (y + z) ** 2        by y = z
          = u ** 2 + v ** 2              by two_squares_hop_def
*)
Theorem two_squares_hop_thm:
  !n. tik n /\ prime n ==> let (u,v) = two_squares_hop n in (n = u ** 2 + v ** 2)
Proof
  rw[two_squares_hop_def] >>
  qabbrev_tac `t = two_sq_hop n` >>
  `t IN fixes flip (mills n)` by fs[two_sq_hop_thm, Abbr`t`] >>
  `?x y z. t = (x,y,z)` by rw[triple_parts] >>
  `(x,y,z) IN mills n /\ (y = z)` by fs[flip_fixes_alt, flip_fix] >>
  `n = windmill (x, y, y)` by fs[mills_element] >>
  simp[windmill_by_squares]
QED

(* Wonderful! *)

(*
Note: the algorithm works for tik n /\ ~square n:

> EVAL ``two_sq_hop 65``; = (1,4,4)
> EVAL ``two_squares_hop 65``; = (1,8)

These have more than one zagier-fix, each corresponds to a flip-fix.
*)

(* ------------------------------------------------------------------------- *)
(* Popping as direct hop                                                     *)
(* ------------------------------------------------------------------------- *)

(* Define direct hop as pop. *)
Definition pop_def:
   pop m (x,y,z) = (2 * m * z - x,z,y + m * x - m * m * z)
End

(* Define direct hopping. *)
Definition popping_def:
   popping k t = pop (step k t) t
End

(* Idea: the hop in hopping (SQRT n) can be simplifed for non-ping. *)

(* Theorem:  ~square n /\ n = windmill t /\ ~is_ping t ==> popping (SQRT n) t = hopping (SQRT n) t *)
(* Proof:
   Let (x,y,z) = t,
       n = windmill (x,y,z).
       m = (x + SQRT n) DIV (2 * z).
   Note 0 < z                                  by windmill_with_arms
   Thus step 0 (x,y,z) < step (SQRT n) (x,y,z) by step_0_lt_step_sqrt, ~is_ping (x,y,z)
    <=>  x DIV (2 * z) < m                     by step_0, step_sqrt
    <=>  0 < 2 * m * z - x                     by hop_mind, 0 < z, [1]

     hopping (SQRT n) (x,y,z)
   = hop (step (SQRT n) (x,y,z)) (x,y,z)       by hopping_def
   = hop m (x,y,z)                             by step_sqrt
   = (2 * m * z - x,z,y + m * x - m * m * z)   by hop_def, [1]
   = pop m (x,y,z)                             by pop_def
   = popping (SQRT n) (x,y,z)                  by popping_def
*)
Theorem popping_sqrt_eq_hopping_sqrt:
  !n t. ~square n /\ n = windmill t /\ ~is_ping t ==> popping (SQRT n) t = hopping (SQRT n) t
Proof
  simp[FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `windmill (x,y,z)` >>
  qabbrev_tac `n = windmill (x,y,z)` >>
  qabbrev_tac `m = (x + SQRT n) DIV (2 * z)` >>
  `0 < z` by metis_tac[windmill_with_arms] >>
  `m = step (SQRT n) (x,y,z) /\ x DIV (2 * z) < m` by metis_tac[step_0_lt_step_sqrt, step_0, step_sqrt] >>
  `0 < 2 * m * z - x` by rfs[hop_mind] >>
  rfs[hopping_def, hop_def, pop_def, popping_def]
QED

(* Theorem: tik n /\ ~square n /\ n = windmill t /\ ~is_ping t ==>
            popping (SQRT n) t = (skip_ping o pong o skip_pung) t *)
(* Proof:
     (skip_ping o pong o skip_pung) t
   = hopping (SQRT n) t            by hopping_sqrt_eqn
   = popping (SQRT n) t            by popping_sqrt_eq_hopping_sqrt
*)
Theorem popping_sqrt_eqn:
  !n t. tik n /\ ~square n /\ n = windmill t /\ ~is_ping t ==>
        popping (SQRT n) t = (skip_ping o pong o skip_pung) t
Proof
  simp[hopping_sqrt_eqn, popping_sqrt_eq_hopping_sqrt]
QED

(* Theorem: tik n /\ ~square n /\ n = windmill t /\ is_pong t ==> beyond_pong t = popping (SQRT n) t *)
(* Proof:
   Note ~is_ping t                 by pong_not_ping
     beyond_pong t
   = hopping (SQRT n) t            by beyond_pong_eqn
   = popping (SQRT n) t            by popping_sqrt_eq_hopping_sqrt
*)
Theorem beyond_pong_eqn_by_pop:
   !n t. tik n /\ ~square n /\ n = windmill t /\ is_pong t ==> beyond_pong t = popping (SQRT n) t
Proof
  rpt strip_tac >>
  `~is_ping t` by simp[pong_not_ping] >>
  fs[beyond_pong_eqn, popping_sqrt_eq_hopping_sqrt]
QED

(* Theorem: let ls = path n k; ns = hop_nodes ls in tik n /\ ~square n /\ 0 < k ==>
            HD ns = popping (SQRT n) (HD ls) *)
(* Proof:
   Let ls = path n k,
       ns = hop_nodes ls.
   Note is_pong (HD ls)                        by path_head_is_pong, EL
     so ~is_ping (HD ls)                       by pong_not_ping
    Now HD ls IN (mills n)                     by path_head, mills_element_trivial_flip, tik n
    ==> n = windmill (HD ls)                   by mills_element_alt

        HD ns
      = hopping (SQRT n) (HD ls)               by hop_nodes_path_head
      = popping (SQRT n) (HD ls)               by popping_sqrt_eq_hopping_sqrt
*)
Theorem hop_nodes_path_head_by_pop:
  !n k j. let ls = path n k; ns = hop_nodes ls in tik n /\ ~square n /\ 0 < k ==>
          HD ns = popping (SQRT n) (HD ls)
Proof
  rw_tac std_ss[] >>
  `HD ls IN (mills n)` by fs[path_head, mills_element_trivial_flip, Abbr`ls`] >>
  `n = windmill (HD ls)` by fs[mills_element_alt, Abbr`ls`] >>
  `is_pong (HD ls)` by metis_tac[path_head_is_pong, EL] >>
  `~is_ping (HD ls)` by fs[pong_not_ping] >>
  metis_tac[hop_nodes_path_head, popping_sqrt_eq_hopping_sqrt]
QED

(* Theorem: let ls = path n k; ns = hop_nodes ls in
            tik n /\ ~square n /\ ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls /\ j < LENGTH ns ==>
            EL j ns = FUNPOW (popping (SQRT n)) (j + 1) (HD ls) *)
(* Proof:
   Let ls = path n k,
       ps = pong_list (FRONT ls),
        g = popping (SQRT n.
   The goal is to show: EL j ns = FUNPOW g (j + 1) (HD ls)

   Note 0 < LENGTH ns                          by j < LENGTH ns
     so ns <> []                               by LENGTH_EQ_0
     or 0 < k                                  by hop_nodes_path_eq_nil

   By induction on j.
   Base: 0 < LENGTH ns ==> EL 0 ns = FUNPOW g (0 + 1) (HD ls)
         beyond_pong (EL 0 ps)
       = beyond_pong (HD ps)                   by EL
       = g (HD ls)                             by hop_nodes_path_head_by_pop, 0 < k
       = g (HD ps)                             by pong_list_path_head_alt, 0 < k
       = FUNPOW g 1 (HD ps)                    by FUNPOW_1
   Step: j < LENGTH ns ==> EL j ns = FUNPOW g (j + 1) (HD ls)
     ==> SUC j < LENGTH ns ==> EL (SUC j) ns = FUNPOW g (SUC j + 1) (HD ls)
      Note j < LENGTH ns                       by SUC j < LENGTH ns
       and LENGTH ns = LENGTH ps               by hop_nodes_length
       and n = windmill (EL j ns) /\
           ~is_ping (EL j ns)                  by hop_nodes_path_element_thm, [1]

          EL (SUC j) ns
        = beyond_pong (EL (SUC j) ps)          by hop_nodes_element
        = beyond_pong ((skip_pung o skip_ping o pong) (EL j ps))
                                               by pong_list_path_element_suc, SUC j < LENGTH ps
        = beyond_pong (skip_pung (beyond_pong (EL j ps)))
                                               by beyond_pong_def
        = beyond_pong (skip_pung (EL j ns))    by hop_nodes_element
        = (skip_ping o pong) (skip_pung (EL j ns))
                                               by beyond_pong_def
        = (skip_ping o pong o skip_pung) (EL j ns))
                                               by composition
        = g (EL j ns))                         by hopping_sqrt_eqn, [1]
        = g (FUNPOW g (j + 1) (HD ls))         by induction hypothesis
        = FUNPOW g (SUC j + 1) (HD ls)         by FUNPOW_SUC, ADD
*)
Theorem hop_nodes_path_element_eqn_by_pop:
  !n k j. let ls = path n k; ns = hop_nodes ls in
          tik n /\ ~square n /\ ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls /\ j < LENGTH ns ==>
          EL j ns = FUNPOW (popping (SQRT n)) (j + 1) (HD ls)
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `ps = pong_list (FRONT ls)` >>
  qabbrev_tac `g = popping (SQRT n)` >>
  `0 < LENGTH ns` by decide_tac >>
  `ns <> [] /\ 0 < k` by metis_tac[hop_nodes_path_eq_nil, LENGTH_EQ_0, NOT_ZERO] >>
  Induct_on `j` >| [
    rw[] >>
    metis_tac[hop_nodes_path_head_by_pop, pong_list_path_head_alt, FUNPOW_1],
    rpt strip_tac >>
    `LENGTH ns = LENGTH ps` by fs[hop_nodes_length, Abbr`ns`, Abbr`ps`] >>
    `j < LENGTH ns` by decide_tac >>
    `n = windmill (EL j ns) /\ ~is_ping (EL j ns)` by metis_tac[hop_nodes_path_element_thm] >>
    `EL (SUC j) ns = beyond_pong (EL (SUC j) ps) ` by fs[hop_nodes_element, Abbr`ns`, Abbr`ps`] >>
    `_ = beyond_pong ((skip_pung o skip_ping o pong) (EL j ps))` by metis_tac[pong_list_path_element_suc, ADD1] >>
    `_ = beyond_pong (skip_pung (EL j ns))` by simp[GSYM beyond_pong_def, GSYM hop_nodes_element, Abbr`ns`, Abbr`ps`] >>
    `_ = (skip_ping o pong) (skip_pung (EL j ns))` by simp[beyond_pong_def] >>
    `_ = (skip_ping o pong o skip_pung) (EL j ns)` by simp[] >>
    `_ = g (EL j ns)` by fs[popping_sqrt_eqn, Abbr`g`] >>
    `_ = g (FUNPOW g (j + 1) (HD ls))` by fs[] >>
    metis_tac[FUNPOW_SUC, ADD]
  ]
QED

(* Theorem: let ls = path n k; ns = hop_nodes ls in
            tik n /\ ~square n /\ ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls /\ 0 < k ==>
            LAST ns = LAST ls /\ LAST ls = FUNPOW (popping (SQRT n)) (LENGTH ns) (HD ls) *)
(* Proof:
   Let ls = path n k,
       ns = hop_nodes ls,
        h = LENGTH ns.
   The goal is to show: LAST ns = LAST ls /\ LAST ls = FUNPOW (popping (SQRT n)) h (HD ls).

   Note ns <> []                               by hop_nodes_path_eq_nil, 0 < k
     so 0 < h                                  by LENGTH_EQ_0, NOT_ZERO
    Let j = h - 1, then j = PRE h.
        LAST ns
      = EL j ns                                by LAST_EL, ns <> []
      = LAST ls                                by hop_nodes_path_element_thm, j + 1 = h
   Also EL j ns
      = FUNPOW (popping (SQRT n)) h (HD ls)    by hop_nodes_path_element_eqn_by_pop
*)
Theorem hop_nodes_path_last_by_pop:
  !n k. let ls = path n k; ns = hop_nodes ls in
        tik n /\ ~square n /\ ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls /\ 0 < k ==>
        LAST ns = LAST ls /\ LAST ls = FUNPOW (popping (SQRT n)) (LENGTH ns) (HD ls)
Proof
  simp[] >>
  ntac 3 strip_tac >>
  qabbrev_tac `ls = path n k` >>
  qabbrev_tac `ns = hop_nodes ls` >>
  qabbrev_tac `h = LENGTH ns` >>
  `ns <> [] /\ 0 < h` by metis_tac[hop_nodes_path_eq_nil, LENGTH_EQ_0, NOT_ZERO] >>
  `h = h - 1 + 1 /\ h - 1 = PRE h /\ h - 1 < h` by decide_tac >>
  qabbrev_tac `j = h - 1` >>
  `LAST ns = EL j ns` by metis_tac[LAST_EL] >>
  metis_tac[hop_nodes_path_element_thm, hop_nodes_path_element_eqn_by_pop]
QED

(* Theorem: let ls = path n k in tik n /\ prime n /\
            k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) ==>
            WHILE (\t. flip t <> t) (popping (SQRT n)) (HD ls) = LAST ls *)
(* Proof:
   Let ls = path n k,
        p = iterate_period (zagier o flip) (1,1,n DIV 4),
        k = 1 + HALF p,
        g = \t. flip t <> t,
        b = popping (SQRT n).
   The goal is to show: WHILE g b (HD ls) = LAST ls

   If n = 5,
      Then p = 1                               by tik_iterate_period_eq_1
        so k = 1 + HALF 1 = 1                  by arithmetic
       and ls = path 5 1
              = [(1,5 DIV 4,1); (1,1,5 DIV 4)] by path_1
              = [(1,1,1); (1,1,1)]             by arithmetic
      Also flip (1,1,1) = (1,1,1)              by flip_fix
        so ~g (HD ls)                          by applying g
      Thus WHILE g b (HD ls) = HD ls           by iterate_while_none
                             = LAST ls         by HD, LAST_DEF
   If n <> 5,
      Let ns = hop_nodes ls,
           h = LENGTH ns.
      Note ~square n                           by prime_non_square
       and flip (LAST ls) = LAST ls            by tik_prime_path_last_flip_fix
       and flip (HD ls) <> HD ls               by tik_path_head_flip_fix, n <> 5
       and ALL_DISTINCT ls                     by path_all_distinct, n <> 5
      Also 0 < k                               by k = 1 + HALF p
      Thus LAST ns = LAST ls /\ LAST ls = FUNPOW b h (HD ls)
                                               by hop_nodes_path_last_by_pop, [1]

      The goal becomes: WHILE g b (HD ls) = FUNPOW b h (HD ls)

      By iterate_while_thm, this is to show:
      (1) !j. j < h ==> g (FUNPOW b j (HD ls))
          If j = 0,
             Then FUNPOW b 0 (HD ls) = HD ls   by FUNPOW_0
              and flip (HD ls) <> HD ls        by above
               so g (HD ls)                    by applying g
          Otherwise, 0 < j,
             Let q = EL (j - 1) ns.
             Then q = FUNPOW b j (HD ls)       by hop_nodes_path_element_eqn_by_pop
              and q <> LAST ls /\ MEM q ls     by hop_nodes_path_element_thm
             Thus flip q <> q                  by tik_prime_path_flip_fix_iff_alt
               or g (FUNPOW b j (HD ls))       by applying g
       (2) ~g (FUNPOW b h (HD ls))
           Note flip (LAST ls) = LAST ls       by tik_prime_path_last_flip_fix
            and LAST ls = FUNPOW b h (HD ls)   by above. [1]
           Hence true                          by applying g
*)
Theorem tik_prime_path_popping_while_thm:
  !n k. let ls = path n k in tik n /\ prime n /\
        k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)) ==>
        WHILE (\t. flip t <> t) (popping (SQRT n)) (HD ls) = LAST ls
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `p = iterate_period (zagier o flip) (1,1,n DIV 4)` >>
  qabbrev_tac `k = 1 + HALF p` >>
  qabbrev_tac `g = \t. flip t <> t` >>
  qabbrev_tac `b = popping (SQRT n)` >>
  Cases_on `n = 5` >| [
    `p = 1` by fs[tik_iterate_period_eq_1, Abbr`p`] >>
    `k = 1` by fs[Abbr`k`] >>
    `ls = [(1,1,1); (1,1,1)]` by rfs[path_1, Abbr`ls`] >>
    `HD ls = LAST ls` by metis_tac[HD, LAST_DEF] >>
    `~g (1,1,1)` by simp[flip_fix, Abbr`g`] >>
    rfs[iterate_while_none],
    qabbrev_tac `ns = hop_nodes ls` >>
    qabbrev_tac `h = LENGTH ns` >>
    `~square n` by simp[prime_non_square] >>
    `flip (LAST ls) = LAST ls` by metis_tac[tik_prime_path_last_flip_fix] >>
    `flip (HD ls) <> HD ls` by metis_tac[tik_path_head_flip_fix] >>
    `ALL_DISTINCT ls` by fs[path_all_distinct, Abbr`ls`] >>
    `0 < k` by fs[Abbr`k`] >>
    `LAST ns = LAST ls /\ LAST ls = FUNPOW b h (HD ls)` by metis_tac[hop_nodes_path_last_by_pop] >>
    simp[] >>
    irule iterate_while_thm >>
    rw[Abbr`g`] >| [
      `j = 0 \/ 0 < j` by decide_tac >-
      simp[] >>
      assume_tac hop_nodes_path_element_eqn_by_pop >>
      last_x_assum (qspecl_then [`n`, `k`, `j-1`] strip_assume_tac) >>
      rfs[] >>
      assume_tac hop_nodes_path_element_thm >>
      last_x_assum (qspecl_then [`n`, `k`, `j-1`] strip_assume_tac) >>
      rfs[] >>
      qabbrev_tac `q = FUNPOW b j (HD ls)` >>
      assume_tac tik_prime_path_flip_fix_iff_alt >>
      last_x_assum (qspecl_then [`n`, `k`, `q`] strip_assume_tac) >>
      rfs[],
      metis_tac[]
    ]
  ]
QED

(* Define two_squares algorithm with popping *)
Definition two_sq_pop_def:
   two_sq_pop n =  WHILE ($~ o found) (popping (SQRT n)) (1,n DIV 4,1)
End

(* Extract the two squares of hopping algorithm. *)
Definition two_squares_pop_def:
    two_squares_pop n = let (x,y,z) = two_sq_pop n in (x, y + z)
End

(* Theorem: tik n /\ prime n ==> two_sq_pop n = two_sq_hop n *)
(* Proof:
   Let  k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4)),
       ls = path n k,
        u = (1,n DIV 4,1),
        f = $~ o found,
        g = \t. flip t <> t.
   Note HD ls = u                              by path_head
    and f = g                                  by FUN_EQ_THM, found_def, flip_def

        two_sq_pop n
      = WHILE f (popping (SQRT n)) (HD ls)     by two_sq_pop_def
      = WHILE g (popping (SQRT n)) (HD ls)     by f = g
      = LAST ls                                by tik_prime_path_popping_while_thm
      = WHILE g (hopping (SQRT n)) (HD ls)     by tik_prime_path_hopping_while_thm
      = WHILE f (hopping (SQRT n)) (HD ls)     by f = g
      = two_sq_hop n                           by two_sq_hop_def
*)
Theorem two_sq_pop_eqn:
  !n. tik n /\ prime n ==> two_sq_pop n = two_sq_hop n
Proof
  rpt strip_tac >>
  qabbrev_tac `k = 1 + HALF (iterate_period (zagier o flip) (1,1,n DIV 4))` >>
  qabbrev_tac `ls = path n k` >>
  qabbrev_tac `u = (1,n DIV 4,1)` >>
  qabbrev_tac `f = $~ o found` >>
  qabbrev_tac `g = \t. flip t <> t` >>
  `HD ls = u` by fs[path_head, Abbr`ls`, Abbr`u`] >>
  `f = g` by
  (rw[FUN_EQ_THM] >>
  `?a b c. x = (a,b,c)` by metis_tac[triple_parts] >>
  fs[found_def, flip_def, Abbr`f`, Abbr`g`]) >>
  assume_tac tik_prime_path_hopping_while_thm >>
  last_x_assum (qspecl_then [`n`, `k`] strip_assume_tac) >>
  rfs[] >>
  assume_tac tik_prime_path_popping_while_thm >>
  last_x_assum (qspecl_then [`n`, `k`] strip_assume_tac) >>
  rfs[] >>
  rfs[two_sq_hop_def, two_sq_pop_def, Abbr`f`, Abbr`u`]
QED

(* Theorem: tik n /\ prime n ==> two_sq_pop n IN fixes flip (mills n) *)
(* Proof:
   Note two_sq_pop n = two_sq_hop n            by two_sq_pop_eqn
    and two_sq_hop n IN fixes flip (mills n)   by two_sq_hop_thm
*)
Theorem two_sq_pop_thm:
  !n. tik n /\ prime n ==> two_sq_pop n IN fixes flip (mills n)
Proof
  simp[two_sq_pop_eqn, two_sq_hop_thm]
QED

(* Theorem: tik n /\ prime n ==> let (u,v) = two_squares_pop n in n = u ** 2 + v ** 2 *)
(* Proof:
   Let (x,y,z) = two_sq_pop n.
   Then two_squares_pop n = (x, y + z)      by two_squares_pop_def
    and u = x, v = y + z                    by PAIR_EQ

   Note t = two_sq_hop n                    by two_sq_pop_eqn
    and t IN fixes flip (mills n)           by two_sq_hop_thm
   Thus n = windmill (x,y,z) /\ y = z       by flip_fixes_element
     or n = x ** 2 + (2 * y) ** 2           by windmill_by_squares
    <=> n = x ** 2 + (y + z) ** 2           by arithmetic
    <=> n = u ** 2 + v ** 2                 by above
*)
Theorem two_squares_pop_thm:
  !n. tik n /\ prime n ==> let (u,v) = two_squares_pop n in n = u ** 2 + v ** 2
Proof
  rw_tac std_ss[two_squares_pop_def] >>
  `two_sq_hop n = (u,y,z)` by metis_tac[two_sq_pop_eqn] >>
  `(u,y,z) IN fixes flip (mills n)` by metis_tac[two_sq_hop_thm] >>
  fs[flip_fixes_element, windmill_by_squares]
QED

(* A most wonderful theorem. *)

(* ------------------------------------------------------------------------- *)
(* Direct Popping Nodes                                                      *)
(* ------------------------------------------------------------------------- *)

(* Define the direct pop nodes. *)
Definition node_def:
   node n 0 = (1,n DIV 4, 1) /\
   node n (SUC j) = popping (SQRT n) (node n j)
End

(* Extract theorems *)
Theorem node_0 = node_def |> CONJUNCT1;
(* val node_0 = |- !n. node n 0 = (1,n DIV 4,1): thm *)

Theorem node_suc = node_def |> CONJUNCT2;
(* val node_suc = |- !n j. node n (SUC j) = popping (SQRT n) (node n j): thm *)

(* Theorem: node n 1 = popping (SQRT n) (1,n DIV 4,1) *)
(* Proof:
   Let u = (1,n DIV 4,1).
     node n 1
   = popping (SQRT n) (hop_node n 0)       by node_suc, ONE
   = popping (SQRT n) u                    by node_0
*)
Theorem node_1:
  !n. node n 1 = popping (SQRT n) (1,n DIV 4,1)
Proof
  metis_tac[node_def, ONE]
QED

(*
> EVAL ``node 61 0``; = (1,15,1)
> EVAL ``node 61 1``; = (7,1,3)
> EVAL ``node 61 2``; = (5,3,3)
*)

(* Theorem: node n j = FUNPOW (popping (SQRT n)) j (1,n DIV 4,1) *)
(* Proof:
   Let u = (1,n DIV 4,1),
       f = popping (SQRT n).
   The goal is: node n j = FUNPOW f j u

   By induction on j.
   Base: node n 0 = FUNPOW f 0 u
         node n 0
       = u                         by node_0
       = FUNPOW f 0 u              by FUNPOW_0
   Step: node n j = FUNPOW f j u
     ==> node n (SUC j) = FUNPOW f (SUC j) u
         node n (SUC j)
       = f (node n j)              by node_suc
       = f (FUNPOW f j u)          by induction hypothesis
       = FUNPOW f (SUC j) u        by FUNPOW_SUC
*)
Theorem node_thm:
  !n j. node n j = FUNPOW (popping (SQRT n)) j (1,n DIV 4,1)
Proof
  rpt strip_tac >>
  qabbrev_tac `u = (1,n DIV 4,1)` >>
  qabbrev_tac `f = popping (SQRT n)` >>
  Induct_on `j` >-
  simp[node_0, Abbr`u`] >>
  simp[node_suc, FUNPOW_SUC]
QED

(* Theorem: let ls = path n k; ns = hop_nodes ls in tik n /\ ~square n /\ ALL_DISTINCT ls /\
            flip (LAST ls) = LAST ls /\ j < LENGTH ns ==> node n (j + 1) = EL j ns *)
(* Proof:
   Let ls = path n k,
       ns = hop_nodes ls,
        u = (1,n DIV 4,1).
   Then u = HD ls                              by path_head

     node n (j + 1)
   = FUNPOW (popping (SQRT n)) (j + 1) u       by node_thm
   = EL j ns                                   by hop_nodes_path_element_eqn_by_pop, u = HD ls
*)
Theorem node_path_eqn:
  !n k j. let ls = path n k; ns = hop_nodes ls in tik n /\ ~square n /\ ALL_DISTINCT ls /\
          flip (LAST ls) = LAST ls /\ j < LENGTH ns ==> node n (j + 1) = EL j ns
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `u = (1,n DIV 4,1)` >>
  `u = HD ls` by fs[path_head, Abbr`ls`, Abbr`u`] >>
  metis_tac[node_thm, hop_nodes_path_element_eqn_by_pop]
QED

(* Theorem: let ls = path n k; ns = hop_nodes ls in tik n /\ ~square n /\ ALL_DISTINCT ls /\
            flip (LAST ls) = LAST ls /\ 0 < k ==> node n (LENGTH ns) = LAST ls *)
(* Proof:
   Let ls = path n k,
       ns = hop_nodes ls,
        u = (1,n DIV 4,1).
   Then u = HD ls                              by path_head

     node n (LENGTH ns)
   = FUNPOW (popping (SQRT n)) (LENGTH ns) u   by node_thm
   = LAST ls                                   by hop_nodes_path_last_by_pop, u = HD ls
*)
Theorem node_path_last:
  !n k. let ls = path n k; ns = hop_nodes ls in tik n /\ ~square n /\ ALL_DISTINCT ls /\
        flip (LAST ls) = LAST ls /\ 0 < k ==> node n (LENGTH ns) = LAST ls
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `u = (1,n DIV 4,1)` >>
  `u = HD ls` by fs[path_head, Abbr`ls`, Abbr`u`] >>
  metis_tac[node_thm, hop_nodes_path_last_by_pop]
QED

(* Theorem: let ls = path n k; ns = hop_nodes ls in tik n /\ ~square n /\ ALL_DISTINCT ls /\
            flip (LAST ls) = LAST ls /\ j < LENGTH ns ==>
            node n (j + 1) = EL j ns /\ (node n (j + 1) = LAST ls <=> j + 1 = LENGTH ns) *)
(* Proof:
   Let ls = path n k,
       ns = hop_nodes ls,
        h = LENGTH ns.
   Note 0 < h                                  by j < LENGTH ns
     so ns <> []                               by LENGTH_EQ_0
    and 0 < k                                  by hop_nodes_path_eq_nil

   Note node n (j + 1) = EL j ns               by node_path_eqn
    and LAST ns = LAST ls                      by hop_nodes_path_last, 0 < k

    Now j < h means j + 1 <= h.
   If j + 1 < h, then EL j ns <> LAST ls       by hop_nodes_path_element_less
   If j + 1 = h, then EL j ns = LAST ls        by hop_nodes_path_element_last
*)
Theorem node_path_last_iff:
  !n k j. let ls = path n k; ns = hop_nodes ls in tik n /\ ~square n /\ ALL_DISTINCT ls /\
          flip (LAST ls) = LAST ls /\ j < LENGTH ns ==>
          node n (j + 1) = EL j ns /\ (node n (j + 1) = LAST ls <=> j + 1 = LENGTH ns)
Proof
  simp[] >>
  ntac 4 strip_tac >>
  qabbrev_tac `ls = path n k` >>
  qabbrev_tac `ns = hop_nodes ls` >>
  qabbrev_tac `h = LENGTH ns` >>
  `0 < h` by decide_tac >>
  `ns <> [] /\ 0 < k` by metis_tac[hop_nodes_path_eq_nil, LENGTH_EQ_0, NOT_ZERO] >>
  `node n (j + 1) = EL j ns` by metis_tac[node_path_eqn] >>
  `j + 1 < h \/ j + 1 = h` by decide_tac >| [
    assume_tac hop_nodes_path_element_less >>
    last_x_assum (qspecl_then [`n`, `k`, `j`] strip_assume_tac) >>
    rfs[],
    assume_tac hop_nodes_path_element_last >>
    last_x_assum (qspecl_then [`n`, `k`, `j`] strip_assume_tac) >>
    rfs[]
  ]
QED

(* ------------------------------------------------------------------------- *)
(* Hopping along Path (useful theorems)                                      *)
(* ------------------------------------------------------------------------- *)

(*
A quick way to find k of (path n k), without proof:

Definition path_count_def:
   path_count u k = if (flip u = u) then k else path_count ((zagier o flip) u) (k+1)
End
-- need a Termination proof.

Definition path_count_def:
   path_count n = WHILE (\(j,t). flip t <> t) (\(j,t). (SUC j, (zagier o flip) t)) (0,(1,n DIV 4,1))
End

> EVAL ``path_count 61``; = (6,5,3,3)  which means k = 6, (5,3,3) a flip-fix is LAST.
> EVAL ``block_pairs (path 61 6)``; = [(0,4); (5,6)]
> EVAL ``blocks (block_pairs (path 61 6))``; = [(0,0,4); (4,5,6)]
> EVAL ``EL 4 (path 61 6)``; = (7,1,3)
> EVAL ``EL 6 (path 61 6)``; = (5,3,3)

*)

(* Theorem: let h = HALF (1 + SQRT n) in tik n /\ ~square n /\ h <= k ==>
            !j. 0 < j /\ j < h ==> is_ping (EL j (path n k)) *)
(* Proof:
   Let ls = path n k,
        h = HALF (1 + SQRT n).
   By complete induction on j.
   This is to show: !m. m < j ==> 0 < m ==> m < h ==> is_ping (EL m ls) ==>
                    !j. 0 < j /\ j < h ==> is_ping (EL j ls)

   Note the given condition, with j < h, is equivalent to:
        !m. 1 <= m /\ m < j ==> is_ping (EL m ls)      [1]
   Let jj = j - 1,
       q = n DIV 4.
   Then n = 4 * q + 1                          by DIVISION, tik n
    and 0 < k                                  by 0 < j < h <= k

        EL j ls
      = FUNPOW ping jj (EL 1 ls)               by path_element_ping_funpow, [1]
      = FUNPOW ping jj (1,1,q)                 by path_element_1, 0 < k
      = (1 + 2 * jj, 1, q - jj - jj ** 2)      by ping_funpow

        is_ping (EL j ls)
    <=> 1 + 2 * jj + 1 < q - jj - jj ** 2      by is_ping_def
    <=> (jj ** 2 + 2 * jj + 1) + (jj + 1) < q  by arithmetic
    <=>          (jj + 1) ** 2 + (jj + 1) < q  by SUM_SQUARED
    <=>                 j ** 2 + j < q         by jj = j - 1
    <=> 4 * j ** 2 + 4 * j + 1 < 4 * q + 1     by multiplying 4, add 1
    <=>       (2 * j + 1) ** 2 < n             by SUM_SQUARED, n = 4 * q + 1

    Now j < h
    <=> j < (1 + SQRT n) DIV 2                 by notation
    <=> (j + 1) * 2 <= 1 + SQRT n              by X_LT_DIV
    <=>   2 * j + 1 <= SQRT n                  by arithmetic
    <=>  (2 * j + 1) ** 2 <= (SQRT n) ** 2     by EXP_EXP_LE_MONO

    But  (SQRT n) ** 2 < n                     by SQ_SQRT_LT_alt, ~square n
    Thus (2 * j + 1) ** 2 < n                  by inequality
      or is_ping (EL j ls).
*)
Theorem path_start_over_ping:
  !n k. let h = HALF (1 + SQRT n) in tik n /\ ~square n /\ h <= k ==>
        !j. 0 < j /\ j < h ==> is_ping (EL j (path n k))
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `ls = path n k` >>
  completeInduct_on `j` >>
  rpt strip_tac >>
  assume_tac path_element_ping_funpow >>
  last_x_assum (qspecl_then [`n`, `k`, `1`, `j - 1`] strip_assume_tac) >>
  rfs[] >>
  first_x_assum (qspecl_then [`j - 1`] strip_assume_tac) >>
  rfs[] >>
  `is_ping (EL j ls)` suffices_by simp[] >>
  `_ = FUNPOW ping (j - 1) (1,1,n DIV 4)` by fs[path_element_1, Abbr`ls`] >>
  qabbrev_tac `jj = j - 1` >>
  qabbrev_tac `q = n DIV 4` >>
  qabbrev_tac `X = is_ping (EL j ls)` >>
  fs[ping_funpow] >>
  qunabbrev_tac `X` >>
  simp[is_ping_def] >>
  `(jj ** 2 + 2 * jj + 1) + (jj + 1) < q` suffices_by decide_tac >>
  `(2 * j + 1) ** 2 < n` by
  (`(j + 1) * 2 <= 1 + SQRT n` by fs[X_LT_DIV, Abbr`h`] >>
  `2 * j + 1 <= SQRT n` by decide_tac >>
  `(2 * j + 1) ** 2 <= (SQRT n) ** 2` by simp[] >>
  `(SQRT n) ** 2 < n` by simp[SQ_SQRT_LT_alt] >>
  decide_tac) >>
  `(2 * j + 1) ** 2 = 4 * j ** 2 + 4 * j + 1` by simp[SUM_SQUARED, EXP_BASE_MULT] >>
  `n = q * 4 + 1` by metis_tac[DIVISION, DECIDE``0 < 4``] >>
  `_ = 4 * q + 1` by decide_tac >>
  `j ** 2 + j < q` by decide_tac >>
  `j ** 2 + j = (jj + 1) ** 2 + jj + 1` by simp[Abbr`jj`] >>
  fs[SUM_SQUARED]
QED

(* Theorem: let h = HALF (1 + SQRT n) in tik n /\ ~square n /\ h <= k ==>
            ~is_ping (EL h (path n k)) *)
(* Proof:
   Let ls = path n k,
        h = HALF (1 + SQRT n).
   By contradiction, suppose is_ping (EL h ls).
   Note n <> 0                     by square_0
     so SQRT n <> 0                by SQRT_EQ_0
    ==> 0 < h                      by HALF_EQ_0, NOT_ZERO
    Now !j. 0 < j /\ j < h ==> is_ping (EL j ls)
                                   by path_start_over_ping
     or !j. 1 <= j /\ j < h ==> is_ping (EL j ls)      [1]
   Let hh = h - 1,
       q = n DIV 4.
   Then n = 4 * q + 1                          by DIVISION, tik n
    and 0 < k                                  by 0 < h <= k

        EL h ls
      = FUNPOW ping hh (EL 1 ls)               by path_element_ping_funpow, [1]
      = FUNPOW ping hh (1,1,q)                 by path_element_1, 0 < k
      = (1 + 2 * hh, 1, q - hh - hh ** 2)      by ping_funpow

   Thus 1 + 2 * hh < q - hh - hh ** 2 - 1      by is_ping_def, is_ping (EL h ls)
    <=> hh ** 2 + 2 * hh + 1 + (hh + 1) < q    by arithmetic
    <=> (hh + 1) ** 2 + (hh + 1) < q           by SUM_SQUARED
    <=>               h ** 2 + h < q           by hh = h - 1
    ==>   4 * h ** 2 + 4 * h + 1 < 4 * q + 1   by arithmetic
    <=>         (2 * h + 1) ** 2 < 4 * q + 1   by SUM_SQUARED
    <=>         (2 * h + 1) ** 2 < n           by n = 4 * q + 1
    ==>          2 * h + 1 <= SQRT n           by SQRT_LT, SQRT_OF_SQ
    <=>        2 * (h + 1) <= 1 + SQRT n       by arithmetic
    <=>             h < (1 + SQRT n) DIV 2     by X_LT_DIV
    <=>             h < h                      by notation
   which is false, a contradiction.
*)
Theorem path_start_beyond_ping:
  !n k. let h = HALF (1 + SQRT n) in tik n /\ ~square n /\ h <= k ==>
        ~is_ping (EL h (path n k))
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `ls = path n k` >>
  assume_tac path_start_over_ping >>
  last_x_assum (qspecl_then [`n`, `k`] strip_assume_tac) >>
  rfs[] >>
  spose_not_then strip_assume_tac >>
  `0 < n /\ 0 < SQRT n` by metis_tac[square_0, SQRT_EQ_0, NOT_ZERO] >>
  `0 < h` by metis_tac[HALF_EQ_0, ADD_EQ_0, ADD_EQ_1, NOT_ZERO] >>
  assume_tac path_element_ping_funpow >>
  last_x_assum (qspecl_then [`n`, `k`, `1`, `h - 1`] strip_assume_tac) >>
  rfs[] >>
  first_x_assum (qspecl_then [`h - 1`] strip_assume_tac) >>
  rfs[] >>
  `_ = FUNPOW ping (h - 1) (1,1,n DIV 4)` by fs[path_element_1, Abbr`ls`] >>
  qabbrev_tac `hh = h - 1` >>
  qabbrev_tac `q = n DIV 4` >>
  fs[ping_funpow] >>
  fs[is_ping_def] >>
  `hh ** 2 + 2 * hh + 1 + (hh + 1) < q` by decide_tac >>
  `hh ** 2 + 2 * hh + 1 + (hh + 1) = (hh + 1) ** 2 + (hh + 1)` by simp[SUM_SQUARED, EXP_BASE_MULT] >>
  `_ = h ** 2 + h` by simp[Abbr`hh`] >>
  `n = q * 4 + 1` by metis_tac[DIVISION, DECIDE``0 < 4``] >>
  `4 * h ** 2 + 4 * h + 1 < n` by decide_tac >>
  `4 * h ** 2 + 4 * h + 1 = (2 * h + 1) ** 2` by simp[SUM_SQUARED, EXP_BASE_MULT] >>
  `2 * h + 1 <= SQRT n` by metis_tac[SQRT_LT, SQRT_OF_SQ] >>
  `(h + 1) * 2 <= 1 + SQRT n` by decide_tac >>
  `h < HALF (1 + SQRT n)` by simp[X_LT_DIV] >>
  fs[Abbr`h`]
QED

(* A good exercise! *)

(* Theorem: let ls = path n k; h = HALF (1 + SQRT n) in tik n /\ ~square n /\ h <= k ==>
            skip_ping (EL 1 ls) = EL (step (SQRT n) (1,n DIV 4,1)) ls *)
(* Proof:
   Let ls = path n k,
       h = HALF (1 + SQRT n),
       u = (1,n DIV 4,1).
   The goal is to show: skip_ping (EL 1 ls) = EL (step (SQRT n) u) ls.

   Note n <> 0                     by square_0, ~square n
     so 0 < SQRT n                 by SQRT_EQ_0, 0 < n
    and 0 < h                      by HALF_EQ_0, NOT_ZERO
     so 0 < k                      by h <= k
   Also !j. 0 < j /\ j < h ==> is_ping (EL j ls)
                                   by path_start_over_ping
    and ~is_ping (EL h ls)         by path_start_beyond_ping
   Thus skip_ping ls (EL 1 ls)
      = EL h ls                    by path_skip_ping_thm
      = EL (step (SQRT n) u) ls    by step_sqrt
*)
Theorem path_start_skip_ping:
  !n k. let ls = path n k; h = HALF (1 + SQRT n) in tik n /\ ~square n /\ h <= k ==>
        skip_ping (EL 1 ls) = EL (step (SQRT n) (1,n DIV 4,1)) ls
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `u = (1,n DIV 4,1)` >>
  `0 < n /\ 0 < SQRT n` by metis_tac[square_0, SQRT_EQ_0, NOT_ZERO] >>
  `0 < h` by metis_tac[HALF_EQ_0, ADD_EQ_0, ADD_EQ_1, NOT_ZERO] >>
  `~is_ping (EL h ls)` by metis_tac[path_start_beyond_ping] >>
  assume_tac path_start_over_ping >>
  last_x_assum (qspecl_then [`n`, `k`] strip_assume_tac) >>
  rfs[] >>
  assume_tac path_skip_ping_thm >>
  last_x_assum (qspecl_then [`n`, `k`, `1`, `h`] strip_assume_tac) >>
  rfs[] >>
  simp[step_sqrt, Abbr`u`]
QED

(* First good result. *)

(* Theorem: let ls = path n k in tik n /\ ~square n /\ u <= k /\ m <= step 0 (EL u ls) ==>
            hop m (EL u ls) = FUNPOW pung m (EL u ls) *)
(* Proof:
   Let ls = path n k,
       t = EL u ls.
   Note n = windmill t                         by path_element_windmill
   Thus hop m t = FUNPOW pung m t              by hop_step_0_before_pong
*)
Theorem hop_step_0_path_element_before_pong:
  !n k u m. let ls = path n k in tik n /\ ~square n /\ u <= k /\ m <= step 0 (EL u ls) ==>
            hop m (EL u ls) = FUNPOW pung m (EL u ls)
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `t = EL u ls` >>
  `n = windmill t` by fs[path_element_windmill, Abbr`ls`, Abbr`t`] >>
  fs[hop_step_0_before_pong]
QED

(* Theorem: let ls = path n k in tik n /\ ~square n /\ u <= k /\ m = step 0 (EL u ls) ==>
            hop (m + 1) (EL u ls) = pong (hop m (EL u ls)) *)
(* Proof:
   Let ls = path n k,
       t = EL u ls.
   Note n = windmill t                         by path_element_windmill
   Thus hop (m + 1) t = pong (hop m t)         by hop_step_0_at_pong
*)
Theorem hop_step_0_path_element_at_pong:
  !n k u m. let ls = path n k in tik n /\ ~square n /\ u <= k /\ m = step 0 (EL u ls) ==>
            hop (m + 1) (EL u ls) = pong (hop m (EL u ls))
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `t = EL u ls` >>
  `n = windmill t` by fs[path_element_windmill, Abbr`ls`, Abbr`t`] >>
  fs[hop_step_0_at_pong]
QED

(* Theorem: let ls = path n k in tik n /\ ~square n /\ u <= k /\
            m = step 0 (EL u ls) /\ m + j < step (SQRT n) (EL u ls) ==>
            hop (m + 1 + j) (EL u ls) = FUNPOW ping j (hop (m + 1) (EL u ls)) *)
(* Proof:
   Let ls = path n k,
       t = EL u ls.
   Note n = windmill t                         by path_element_windmill
   Thus hop (m + 1 + j) t = FUNPOW ping j (hop (m + 1) t)
                                               by hop_step_0_beyond_pong
*)
Theorem hop_step_0_path_element_beyond_pong:
  !n k u m j. let ls = path n k in tik n /\ ~square n /\ u <= k /\
              m = step 0 (EL u ls) /\ m + j < step (SQRT n) (EL u ls) ==>
              hop (m + 1 + j) (EL u ls) = FUNPOW ping j (hop (m + 1) (EL u ls))
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `t = EL u ls` >>
  `n = windmill t` by fs[path_element_windmill, Abbr`ls`, Abbr`t`] >>
  fs[hop_step_0_beyond_pong]
QED

(* Theorem: let ls = path n k in tik n /\ ~square n /\ u <= k /\
            m = step 0 (EL u ls) /\ m + j < step (SQRT n) (EL u ls) ==>
            hop (m + 1 + j) (EL u ls) = (FUNPOW ping j o pong o FUNPOW pung m) (EL u ls) *)
(* Proof:
   Let ls = path n k,
       t = EL u ls.
   Note n = windmill t                         by path_element_windmill
   Thus hop (m + 1 + j) t = (FUNPOW ping j o pong o FUNPOW pung m) t
                                               by hop_step_0_around_pong
*)
Theorem hop_step_0_path_element_around_pong:
  !n k u m j. let ls = path n k in tik n /\ ~square n /\ u <= k /\
              m = step 0 (EL u ls) /\ m + j < step (SQRT n) (EL u ls) ==>
              hop (m + 1 + j) (EL u ls) = (FUNPOW ping j o pong o FUNPOW pung m) (EL u ls)
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `t = EL u ls` >>
  `n = windmill t` by fs[path_element_windmill, Abbr`ls`, Abbr`t`] >>
  fs[hop_step_0_around_pong]
QED

(* Theorem: let ls = path n k in tik n /\ ~square n /\ flip (LAST ls) = LAST ls /\
            u < k /\ m <= step 0 (EL u ls) ==> u + m < k /\ hop m (EL u ls) = EL (u + m) ls *)
(* Proof:
   Let ls = path n k,
       t = EL u ls.
   The goal is to show: m + u < k /\ hop m t = EL (m + u) ls

   If ~is_pung t,
      Then step 0 t = 0                        by step_0_eq_0
        so m = 0                               by m <= 0
      Thus u + 0 < k                           by u < k
       and hop 0 t = t = EL (u + 0) ls         by hop_0

   If is_pung t,
      By complete induction on m.
      This is to show: !j. j < m /\ u + j <= k /\ j <= step 0 t ==> j + u < k /\ hop j t = EL (u + j) ls
                   ==> m <= step 0 t ==> m + u < k /\ hop m t = EL (u + m) ls
      If m = 0,
         Then u + 0 < k                        by u < k
          and hop 0 t = EL (u + 0) ls          by hop_0
      Otherwise, 0 < m.
         Put j = m - 1.
         Then j < m /\ u + j <= k /\ j <= step 0 t,
          ==> hop j t = EL (u + j) ls          by induction hypothesis
          and is_pung (hop j t)                by hop_step_0_over_pung, j < m

         Claim: m + u < k
         Proof: By contradiction, suppose k <= m + u.
                Then m + u = k                 by m + u - 1 < k, or m + u < k + 1
                  so u + j = u + (m - 1) = k - 1
                 But ~is_pung (EL (k - 1) ls)  by path_last_flip_fix_not_by_pung
                 This contradicts is_pung (hop j t).

         For the remaining goal: hop m t = EL (u + m) ls.
         Note m <= step 0 (x,y,z)
           so m <= x DIV (2 * z)               by step_0
          and j < x DIV (2 * z)                by j < m

          Let xx = x - 2 * j * z,
              yy = y + j * x - j ** 2 * z
          Then hop j t = (xx,yy,z)             by hop_alt, j < x DIV (2 * z)
           and n = windmill (EL (u + j) ls)    by path_element_windmill
                 = hop j t = (xx,yy,z)         by above
            so 0 < xx                          by windmill_with_mind, tik n
           and 0 < yy                          by windmill_with_arms, ~square n

             EL (u + m) ls
           = (zagier o flip) EL (u + j) ls     by path_element_suc
           = pung (hop j t)                    by zagier_flip_pung
           = pung (xx,yy,z)                    by above
           = (xx - 2 * z,xx + yy - z,z)        by pung_def
           = (x - 2 * z * (j + 1),             by hop_identity_1
              y + (j + 1) * x - (j + 1) ** 2 * z, z)  by hop_identity_3, 0 < xx, 0 < yy
           = (x - 2 * m * z,y + m * x - m * m * z,z)  by m = j + 1
           = hop m (x,y,z)                     by hop_alt, m <= x DIV (2 * z)
*)
Theorem hop_step_0_path_element:
  !n k u m. let ls = path n k in tik n /\ ~square n /\ flip (LAST ls) = LAST ls /\
            u < k /\ m <= step 0 (EL u ls) ==> u + m < k /\ hop m (EL u ls) = EL (u + m) ls
Proof
  simp[] >>
  ntac 5 strip_tac >>
  qabbrev_tac `ls = path n k` >>
  qabbrev_tac `t = EL u ls` >>
  `?x y z. t = (x,y,z)` by metis_tac[triple_parts] >>
  `n = windmill (x,y,z)` by metis_tac[path_element_windmill, LESS_IMP_LESS_OR_EQ] >>
  `0 < z` by metis_tac[windmill_with_arms] >>
  `~is_pung t \/ is_pung t` by decide_tac >| [
    `step 0 t = 0` by rfs[step_0_eq_0] >>
    `m = 0` by decide_tac >>
    simp[hop_0],
    completeInduct_on `m` >>
    strip_tac >>
    `m = 0 \/ 0 < m` by decide_tac >-
    simp[hop_0, Abbr`t`] >>
    last_x_assum (qspecl_then [`m-1`] strip_assume_tac) >>
    rfs[] >>
    `m - 1 < m /\ (m - 1) + 1 = m /\ SUC (m + u - 1) = m + u /\ m + u - 1 < k` by decide_tac >>
    `is_pung (EL (m + u - 1) ls)` by metis_tac[hop_step_0_over_pung, LESS_LESS_EQ_TRANS] >>
    `EL (m + u) ls = (zagier o flip) (EL (m + u - 1) ls)` by metis_tac[path_element_suc] >>
    `_ = pung (hop (m - 1) (x,y,z))` by fs[zagier_flip_pung] >>
    strip_tac >| [
      spose_not_then strip_assume_tac >>
      `m + u = k` by decide_tac >>
      metis_tac[path_last_flip_fix_not_by_pung],
      qabbrev_tac `j = m - 1` >>
      `0 < 2 * z` by decide_tac >>
      `m <= x DIV (2 * z)` by fs[step_0] >>
      qabbrev_tac `xx = x - 2 * j * z` >>
      qabbrev_tac `yy = y + j * x - j ** 2 * z` >>
      `hop j (x,y,z) = (xx,yy,z)` by fs[hop_alt, Abbr`xx`, Abbr`yy`] >>
      `n = windmill (EL (m + u - 1) ls)` by fs[path_element_windmill, Abbr`ls`] >>
      `0 < xx` by metis_tac[windmill_with_mind, ONE_NOT_0] >>
      `0 < yy` by metis_tac[windmill_with_arms] >>
      `pung (hop j (x,y,z)) = (xx - 2 * z,xx + yy - z,z)` by rfs[pung_def] >>
      simp[hop_alt] >>
      rpt strip_tac >| [
        `xx - 2 * z = x - 2 * (j + 1) * z` by metis_tac[hop_identity_1] >>
        simp[Abbr`j`],
        `xx + yy - z = y + (j + 1) * x - (j + 1) ** 2 * z` by metis_tac[hop_identity_3] >>
        simp[Abbr`j`]
      ]
    ]
  ]
QED

(* Theorem: let ls = path n k in tik n /\ ~square n /\ flip (LAST ls) = LAST ls /\
            u < k /\ j < step 0 (EL u ls) ==>
            hop (SUC j) (EL u ls) = (zagier o flip) (hop j (EL u ls)) *)
(* Proof:
   Let t = EL u ls.
   Note SUC j <= step 0 t                     by j < step 0 t
   Thus u + j < k /\ hop j t = EL (j + u) ls  by hop_step_0_path_element
   Also u + SUC j < k /\ hop (SUC j) t = EL (u + SUC j) ls
                                              by hop_step_0_path_element
      hop (SUC j) (EL u ls)
    = EL (SUC (u + j)) ls                     by SUC (u + j) = u + SUC j
    = (zagier o flip) (EL (u + j) ls)         by path_element_suc, u + j < k
    = (zagier o flip) hop j t                 by above
*)
Theorem hop_step_0_suc:
  !n k u j. let ls = path n k in tik n /\ ~square n /\ flip (LAST ls) = LAST ls /\
            u < k /\ j < step 0 (EL u ls) ==>
            hop (SUC j) (EL u ls) = (zagier o flip) (hop j (EL u ls))
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `t = EL u ls` >>
  assume_tac hop_step_0_path_element >>
  last_x_assum (qspecl_then [`n`,`k`,`u`,`j`] strip_assume_tac) >>
  rfs[] >>
  assume_tac hop_step_0_path_element >>
  last_x_assum (qspecl_then [`n`,`k`,`u`,`SUC j`] strip_assume_tac) >>
  rfs[] >>
  `u + SUC j = SUC (j + u)` by decide_tac >>
  simp[path_element_suc, Abbr`ls`, Abbr`t`]
QED

(* Theorem: let ls = path n k in tik n /\ ~square n /\ flip (LAST ls) = LAST ls /\ u < k ==>
            hopping 0 (EL u ls) = skip_pung (EL u ls) *)
(* Proof:
   Let ls = path n k,
        t = EL u ls,
   Note ?x y z. t = (x,y,z)                    by triple_parts
    and n = windmill (x,y,z)                   by path_element_windmill, tik n
     so 0 < z                                  by windmill_with_arms, ~square n

   Let m = step 0 t.
   Then !j. j < m ==> is_pung (hop j (x,y,z))  by hop_step_0_over_pung, 0 < z [1]
    and ~is_pung (hop m (x,y,z))               by hop_step_0_beyond_pung, 0 < z [2]

    Now !j. j <= m ==> u + j < k /\ hop j (x,y,z) = EL (u + j) ls)
                                               by hop_step_0_path_element [3]

   Thus ~is_pung (EL (u + m) ls)               by putting j = m, [2]
    and !j. j < m ==> is_pung (EL (u + j) ls)  by keeping j, [1]
     or !i. u + 0 <= i /\ i < u + m ==> is_pung (EL i ls)
                                               by i = u + j
   Thus EL (m + u) ls = skip_pung t            by path_skip_pung_thm

        hopping 0 t
      = hop (step 0 t) t                       by hopping_def
      = hop m (x,y,z)                          by m = step 0 t
      = EL (u + m) ls                          by putting j = m, [3]
      = skip_pung t                            by above
*)
Theorem hopping_path_step_0:
  !n k u. let ls = path n k in tik n /\ ~square n /\ flip (LAST ls) = LAST ls /\ u < k ==>
          hopping 0 (EL u ls) = skip_pung (EL u ls)
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `t = EL u ls` >>
  `?x y z. t = (x,y,z)` by metis_tac[triple_parts] >>
  `n = windmill (x,y,z)` by metis_tac[path_element_windmill, LESS_IMP_LESS_OR_EQ] >>
  `0 < z` by metis_tac[windmill_with_arms] >>
  qabbrev_tac `m = x DIV (2 * z)` >>
  `step 0 (x,y,z) = m` by fs[step_0, Abbr`m`] >>
  `!j. j < m ==> is_pung (hop j (x,y,z))` by simp[hop_over_pung, Abbr`m`] >>
  `~is_pung (hop m (x,y,z))` by simp[hop_beyond_pung, Abbr`m`] >>
  assume_tac hop_step_0_path_element >>
  last_x_assum (qspecl_then [`n`,`k`,`u`] strip_assume_tac) >>
  rfs[] >>
  `~is_pung (EL (u + m) ls) /\ !j. j < m ==> is_pung (EL (u + j) ls)` by fs[] >>
  `!j. u <= j /\ j < u + m ==> is_pung (EL j ls)` by
  (rpt strip_tac >>
  `0 <= j - u /\ j - u < m /\ j = u + (j - u)` by decide_tac >>
  qabbrev_tac `i = j - u` >>
  fs[]) >>
  `m + u < k /\ hop m (x,y,z) = EL (m + u) ls` by fs[] >>
  `m + u <= k` by decide_tac >>
  assume_tac path_skip_pung_thm >>
  last_x_assum (qspecl_then [`n`,`k`,`u`,`u + m`] strip_assume_tac) >>
  rfs[] >>
  `hopping 0 (x,y,z) = hop m (x,y,z)` suffices_by fs[] >>
  simp[hopping_def]
QED

(* Theorem: let ls = path n k; ps = pong_list (FRONT ls) in tik n /\ ~square n /\ ALL_DISTINCT ls /\
            j + 1 < LENGTH ps ==> EL (j + 1) ps = ((hopping 0) o beyond_pong) (EL j ps) *)
(* Proof:
   Let ls = path n k,
       ns = hop_nodes ls,
       ps = pong_list (FRONT ls),
        t = EL j ps.
   Note LENGTH ns = LENGTH ps                  by hop_nodes_length
     so EL j ns = beyond_pong t                by hop_nodes_element
   Then n = windmill (beyond_pong t)           by hop_nodes_path_element_less, tik n

   Note EL (j + 1) ps
      = (skip_pung o skip_ping o pong) t       by pong_list_path_element_suc
      = skip_pung ((skip_ping o pong) t)       by o_THM
      = skip_pung (beyond_pong t)              by beyond_pong_def
      = hopping 0 (beyond_pong t)              by hopping_0, tik n /\ ~square n
      = ((hopping 0) o beyond_pong) t          by o_THM
*)
Theorem pong_list_path_element_suc_by_hop:
  !n k j. let ls = path n k; ps = pong_list (FRONT ls) in tik n /\ ~square n /\ ALL_DISTINCT ls /\
          j + 1 < LENGTH ps ==> EL (j + 1) ps = ((hopping 0) o beyond_pong) (EL j ps)
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `t = EL j ps` >>
  qabbrev_tac `ns = hop_nodes ls` >>
  `LENGTH ns = LENGTH ps` by fs[hop_nodes_length, Abbr`ns`, Abbr`ps`] >>
  `EL j ns = beyond_pong t` by fs[hop_nodes_element, Abbr`ns`, Abbr`t`] >>
  `n = windmill (beyond_pong t)` by metis_tac[hop_nodes_path_element_less] >>
  assume_tac pong_list_path_element_suc >>
  last_x_assum (qspecl_then [`n`, `k`, `j`] strip_assume_tac) >>
  rfs[] >>
  fs[hopping_0, beyond_pong_def]
QED

(* Theorem: let ls = path n k; ps = pong_list (FRONT ls) in tik n /\ ~square n /\ ALL_DISTINCT ls /\
            j < LENGTH ps ==> EL j ps = FUNPOW ((hopping 0) o beyond_pong) j (HD ps) *)
(* Proof:
   Let ls = path n k,
       ps = pong_list (FRONT ls),
        f = (hopping 0) o beyond_pong.
   The goal is to show: EL j ps = FUNPOW f j (HD ps)

   By induction j.
   Base: 0 < LENGTH ps ==> EL 0 ps = FUNPOW f 0 (HD ps)
         EL 0 ps
       = HD ps                                 by EL
       = FUNPOW f 0 (HD ps)                    by FUNPOW_0
   Step: j < LENGTH ps ==> EL j ps = FUNPOW f j (HD ps)
     ==> SUC j < LENGTH ps ==> EL (SUC j) ps = FUNPOW f (SUC j) (HD ps)
     Note j < LENGTH ps                        by SUC j < LENGTH ps
       EL (SUC j) ps
     = f (EL j ps)                             by pong_list_path_element_suc_by_hop
     = f (FUNPOW f j (HD ps))                  by induction hypothesis
     = FUNPOW f (SUC j) (HD ps)                by FUNPOW_SUC
*)
Theorem pong_list_path_element_eqn_by_hop:
  !n k j. let ls = path n k; ps = pong_list (FRONT ls) in tik n /\ ~square n /\ ALL_DISTINCT ls /\
          j < LENGTH ps ==> EL j ps = FUNPOW ((hopping 0) o beyond_pong) j (HD ps)
Proof
  rw_tac std_ss[] >>
  qabbrev_tac `fs = FRONT ls` >>
  qabbrev_tac `u = (1,n DIV 4,1)` >>
  qabbrev_tac `f = (hopping 0) o beyond_pong` >>
  Induct_on `j` >-
  simp[] >>
  rpt strip_tac >>
  `EL (SUC j) ps = f (EL j ps)` by metis_tac[pong_list_path_element_suc_by_hop, ADD1] >>
  simp[FUNPOW_SUC]
QED

(* Theorem: let ls = path n k; ns = hop_nodes ls; ps = pong_list (FRONT ls) in
            ALL_DISTINCT ls /\ j + 1 < LENGTH ns ==>
            findi (EL j ps) ls < findi (EL j ns) ls /\ findi (EL j ns) ls <= findi (EL (j+1) ps) ls *)
(* Proof:
   Let ls = path n k,
       ps = pong_list (FRONT ls),
       ns = hop_nodes ls,
       t1 = EL j ps,
       t2 = EL (j + 1) ps.
   The goal is to show: findi t1 ls < findi (EL j ns) ls /\ findi (EL j ns) ls <= findi t2 ls.

   Note LENGTH ns = LENGTH ps                  by hop_nodes_length
     so ?p q. p < q /\ q < k /\ EL p ls = t1 /\ EL q ls = t2 /\
              is_pong (EL p ls) /\ is_pong (EL q ls) /\
              !h. p < h /\ h < q ==> ~is_pong (EL h ls)
                                               by pong_list_pair_in_path
   Thus ?c. p < c /\ c <= q /\ ~is_ping (EL c ls) /\
        !p. c <= p /\ p < q ==> is_pung (EL p ls) /\
        !q. p < q /\ q < c ==> is_ping (EL q ls)
                                               by pong_interval_cut_exists
   Claim: EL j ns = EL c ls
   Proof: Note EL (p + 1) ls
             = (zagier o flip) (EL p ls)       by path_element_suc, ADD1
             = pong (EL p ls)                  by zagier_flip_pong
          Also EL c ls
             = skip_ping (EL (p + 1) ls)       by path_skip_ping_thm
             = skip_ping (pong (EL p ls))      by above
             = (skip_pong o pong) (EL p ls)    by o_THM
             = beyond_pong (EL p ls)           by beyond_pong_def
             = beyond_pong (EL j ps)           by above
             = EL j ns                         by hop_nodes_element

    Note LENGTH ls = k + 1                     by path_length
      so p = findi t1 ls                       by findi_EL, p < q, q < k
     and q = findi t2 ls                       by findi_EL, q < k
     and c = findi (EL j ns) ls                by findi_EL, c <= q, q < k
    Thus p < c /\ c <= q                       by above
*)
Theorem hop_nodes_path_element_findi_range:
  !n k j. let ls = path n k; ns = hop_nodes ls; ps = pong_list (FRONT ls) in
          ALL_DISTINCT ls /\ j + 1 < LENGTH ns ==>
          findi (EL j ps) ls < findi (EL j ns) ls /\ findi (EL j ns) ls <= findi (EL (j+1) ps) ls
Proof
  simp[] >>
  ntac 4 strip_tac >>
  qabbrev_tac `ls = path n k` >>
  qabbrev_tac `ps = pong_list (FRONT ls)` >>
  qabbrev_tac `ns = hop_nodes ls` >>
  qabbrev_tac `t1 = EL j ps` >>
  qabbrev_tac `t2 = EL (j + 1) ps` >>
  `LENGTH ns = LENGTH ps` by fs[hop_nodes_length, Abbr`ns`, Abbr`ps`] >>
  assume_tac pong_list_pair_in_path >>
  last_x_assum (qspecl_then [`n`, `k`, `j`] strip_assume_tac) >>
  rfs[] >>
  assume_tac pong_interval_cut_exists >>
  last_x_assum (qspecl_then [`n`, `k`, `p`, `q`] strip_assume_tac) >>
  rfs[] >>
  `EL j ns = EL c ls` by
  (simp[hop_nodes_element, beyond_pong_def, Abbr`ns`] >>
  `EL (p + 1) ls = (zagier o flip) (EL p ls)` by fs[path_element_suc, GSYM ADD1, Abbr`ls`] >>
  `_ = pong (EL p ls)` by simp[zagier_flip_pong] >>
  assume_tac path_skip_ping_thm >>
  last_x_assum (qspecl_then [`n`, `k`, `p+1`, `c`] strip_assume_tac) >>
  rfs[]) >>
  `LENGTH ls = k + 1` by fs[path_length, Abbr`ls`] >>
  `p < LENGTH ls /\ q < LENGTH ls /\ c < LENGTH ls` by decide_tac >>
  metis_tac[findi_EL]
QED

(* Theorem: let ls = path n k; ns = hop_nodes ls; ps = pong_list (FRONT ls) in
            ALL_DISTINCT ls /\ j + 1 + h < LENGTH ns ==>
            findi (EL j ps) ls < findi (EL j ns) ls /\ findi (EL j ns) ls <= findi (EL (j+1+h) ps) ls *)
(* Proof:
   Let ls = path n k,
       ps = pong_list (FRONT ls),
       ns = hop_nodes ls.

   By induction on h.
   Base: 0 + (j + 1) < LENGTH ns ==>
         findi (EL j ps) ls < findi (EL j ns) ls /\
         findi (EL j ns) ls <= findi (EL (0 + (j + 1)) ps) ls
         This is true                          by hop_nodes_path_element_findi_range
   Step: h + (j + 1) < LENGTH ns ==> findi (EL j ps) ls < findi (EL j ns) ls /\
                                     findi (EL j ns) ls <= findi (EL (h + (j + 1)) ps) ls
    ==> SUC h + (j + 1) < LENGTH ns ==> findi (EL j ps) ls < findi (EL j ns) ls /\
                                        findi (EL j ns) ls <= findi (EL (SUC h + (j + 1)) ps) ls
        Note h + (j + 1) < LENGTH ns           by SUC h + (j + 1) < LENGTH ns
        Thus findi (EL j ps) ls < findi (EL j ns) ls
                                               by induction hypothesis
        Also findi (EL (h + j + 1) ps) ls < findi (EL (h + j + 1) ns) ls /\
             findi (EL (h + j + 1) ns) ls <= findi (EL (h + (j + 2)) ps) ls
                                               by hop_nodes_path_element_findi_range
             findi (EL j ns) ls
          <= findi (EL (h + (j + 1)) ps) ls    by induction hypothesis
           < findi (EL (h + (j + 2)) ps) ls    by above
           = findi (EL (SUC h + (j + 1)) ps) ls
*)
Theorem hop_nodes_path_element_findi_thm:
  !n k j h. let ls = path n k; ns = hop_nodes ls; ps = pong_list (FRONT ls) in
            ALL_DISTINCT ls /\ j + 1 + h < LENGTH ns ==>
            findi (EL j ps) ls < findi (EL j ns) ls /\ findi (EL j ns) ls <= findi (EL (j+1+h) ps) ls
Proof
  simp[] >>
  ntac 5 strip_tac >>
  qabbrev_tac `ls = path n k` >>
  qabbrev_tac `ps = pong_list (FRONT ls)` >>
  qabbrev_tac `ns = hop_nodes ls` >>
  Induct_on `h` >| [
    strip_tac >>
    assume_tac hop_nodes_path_element_findi_range >>
    last_x_assum (qspecl_then [`n`, `k`, `j`] strip_assume_tac) >>
    rfs[],
    strip_tac >>
    assume_tac hop_nodes_path_element_findi_range >>
    last_x_assum (qspecl_then [`n`, `k`, `h + (j + 1)`] strip_assume_tac) >>
    rfs[] >>
    `h + (j + 1) < LENGTH ns /\ j + (SUC h + 1) = h + (j + 2)` by decide_tac >>
    `findi (EL j ps) ls <= findi (EL (h + (j + 1)) ps) ls` by fs[] >>
    `findi (EL (h + (j + 1)) ps) ls < findi (EL (j + (SUC h + 1)) ps) ls` by metis_tac[LESS_LESS_EQ_TRANS] >>
    decide_tac
  ]
QED

(* Theorem: let ls = path n k; ns = hop_nodes ls; ps = pong_list (FRONT ls) in tik n /\ ~square n /\
            ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls /\ 0 < k ==>
            findi (LAST ns) ls = k /\ findi (LAST ps) ls < k *)
(* Proof:
   Let ls = path n k,
       ps = pong_list (FRONT ls),
       ns = hop_nodes ls.
   Note LENGTH ls = k + 1                      by path_length

   Note LAST ns = LAST ls                      by hop_nodes_path_last
    and LAST ls = EL k ls                      by path_last_alt
     so findi (LAST ns) ls = k                 by findi_EL

   Also ps <> []                               by pong_list_path_eq_nil, 0 < k
     so LAST ps = EL (PRE (LENGTH ps)) ps      by LAST_EL, ps <> []
   Thus ?p. p < k /\ LAST ps = EL p ls         by pong_list_path_element
    and findi (LAST ps) ls = p < k             by findi_EL
*)
Theorem hop_nodes_path_element_findi_last:
  !n k. let ls = path n k; ns = hop_nodes ls; ps = pong_list (FRONT ls) in tik n /\ ~square n /\
        ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls /\ 0 < k ==>
        findi (LAST ns) ls = k /\ findi (LAST ps) ls < k
Proof
  simp[] >>
  ntac 3 strip_tac >>
  qabbrev_tac `ls = path n k` >>
  qabbrev_tac `ps = pong_list (FRONT ls)` >>
  qabbrev_tac `ns = hop_nodes ls` >>
  `LENGTH ls = k + 1` by fs[path_length, Abbr`ls`] >>
  strip_tac >| [
    `LAST ns = LAST ls` by metis_tac[hop_nodes_path_last] >>
    `_ = EL k ls` by fs[path_last_alt, Abbr`ls`] >>
    fs[findi_EL],
    `ps <> []` by fs[pong_list_path_eq_nil, Abbr`ps`, Abbr`ls`] >>
    `0 < LENGTH ps` by metis_tac[LENGTH_EQ_0, NOT_ZERO] >>
    `PRE (LENGTH ps) < LENGTH ps` by decide_tac >>
    `?p. p < k /\ LAST ps = EL p ls` by metis_tac[LAST_EL, pong_list_path_element] >>
    fs[findi_EL]
  ]
QED

(* Theorem: let ls = path n k in tik n /\ ~square n /\
            ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls ==> ALL_DISTINCT (hop_nodes ls) *)
(* Proof:
   Let ls = path n k,
       ps = pong_list (FRONT ls),
       ns = hop_nodes ls,
        f = beyond_pong.
   Note LENGTH ns = LENGTH ps                  by hop_nodes_length
    and ls <> []                               by path_not_nil
   Thus ALL_DISTINCT ps                        by pong_list_all_distinct, ls <> []

   Claim: !x y. MEM x ps /\ MEM y ps /\ f x = f y ==> x = y
   Proof: Let h = LENGTH ps.
          Then ?j1. j1 < h /\ x = EL j1 ps     by MEM_EL
           and ?j2. j2 < h /\ y = EL j2 ps     by MEM_EL
          Also f x = EL j1 ns                  by hop_nodes_element, h = LENGTH ns
           and f y = EL j2 ns                  by hop_nodes_element, h = LENGTH ns
          Note 0 < h                           by j1 < h
          Thus ps <> [] /\ ns <> []            by LENGTH_EQ_0, h = LENGTH ns
            so 0 < k                           by hop_nodes_path_eq_nil

          By contradiction, suppose x <> y.
          That is, j1 ps <> EL j2 ps           by above
            so j1 <> j2                        by ALL_DISTINCT_EL_IMP

          If j1 < j2, i.e,. j1 + 1 <= j2.
             Let d = j2 - j1 - 1,
             Then findi x ls < findi (f x) ls /\ findi (f x) ls <= findi y ls
                                               by hop_nodes_path_element_findi_thm
              and if j2 + 1 < h,
             then findi y ls < findi (f y) ls /\ findi (f y) ls <= findi (EL (j2 + 1) ps) ls
                                               by hop_nodes_path_element_findi_range
              But f x = f y                    by assumption
               so findi y ls < findi (f y) ls = findi (f x) ls <= findi y ls
               or findi y ls < findi y ls, a contradiction
             Thus ~(j2 + 1 < h),
               or h <= j2 + 1 < h + 1          by j2 < h
              ==> h = j2 + 1                   by arithmetic
             Then f x = LAST ls                by hop_nodes_path_element_thm
               or f y = LAST ls                by f x = f y
               so h = j1 + 1                   by hop_nodes_path_element_thm
              ==> j1 = j2                      by h = j1 + 1 = j2 + 1
              which contradicts j1 < j2.
          If j2 < j1, the proof is similar.

       ALL_DISTINCT ls
   ==> ALL_DISTINCT ps                         by pong_list_all_distinct
   ==> ALL_DISTINCT (MAP f ps)                 by ALL_DISTINCT_MAP_INJ, claim
   <=> ALL_DISTINCT (hop_nodes ls)             by hop_nodes_def
*)
Theorem hop_nodes_path_all_distinct:
  !n k. let ls = path n k in tik n /\ ~square n /\
        ALL_DISTINCT ls /\ flip (LAST ls) = LAST ls ==> ALL_DISTINCT (hop_nodes ls)
Proof
  rw_tac std_ss[hop_nodes_def] >>
  qabbrev_tac `ps = pong_list (FRONT ls)` >>
  qabbrev_tac `ns = hop_nodes ls` >>
  `LENGTH ns = LENGTH ps` by fs[hop_nodes_length, Abbr`ns`, Abbr`ps`] >>
  `ls <> []` by fs[path_not_nil, Abbr`ls`] >>
  `ALL_DISTINCT ps` by fs[pong_list_all_distinct, Abbr`ps`] >>
  irule ALL_DISTINCT_MAP_INJ >>
  rw[MEM_EL] >>
  rename1 `EL j1 ps = EL j2 ps` >>
  `EL j1 ns = EL j2 ns` by fs[hop_nodes_element, Abbr`ns`, Abbr`ps`] >>
  `0 < LENGTH ps` by decide_tac >>
  `ps <> [] /\ ns <> []` by metis_tac[LENGTH_EQ_0, NOT_ZERO] >>
  `0 < k` by fs[hop_nodes_path_eq_nil, Abbr`ns`, Abbr`ls`] >>
  spose_not_then strip_assume_tac >>
  `j1 <> j2` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  `j1 < j2 \/ j2 < j1` by decide_tac >| [
    `j2 = j1 + 1 + (j2 - j1 - 1)` by decide_tac >>
    qabbrev_tac `d = j2 - j1 - 1` >>
    assume_tac hop_nodes_path_element_findi_thm >>
    last_x_assum (qspecl_then [`n`, `k`, `j1`, `d`] strip_assume_tac) >>
    rfs[] >>
    assume_tac hop_nodes_path_element_findi_range >>
    last_x_assum (qspecl_then [`n`, `k`, `j2`] strip_assume_tac) >>
    rfs[] >>
    `LENGTH ps = j2 + 1` by decide_tac >>
    `j1 + 1 = LENGTH ns` by metis_tac[hop_nodes_path_element_thm] >>
    decide_tac,
    `j1 = j2 + 1 + (j1 - j2 - 1)` by decide_tac >>
    qabbrev_tac `d = j1 - j2 - 1` >>
    assume_tac hop_nodes_path_element_findi_thm >>
    last_x_assum (qspecl_then [`n`, `k`, `j2`, `d`] strip_assume_tac) >>
    rfs[] >>
    assume_tac hop_nodes_path_element_findi_range >>
    last_x_assum (qspecl_then [`n`, `k`, `j1`] strip_assume_tac) >>
    rfs[] >>
    `LENGTH ps = j1 + 1` by decide_tac >>
    `j2 + 1 = LENGTH ns` by metis_tac[hop_nodes_path_element_thm] >>
    decide_tac
  ]
QED

(* A very good result. *)

(*
Example of a path with two flip-fixes.
For n = 65 = 1² + 8² = 7² + 4²
This one has k = n DIV 4 = 65 DIV 4 = 16.
However, each path (almost) from a zagier-fix leads to only one flip-fix:
> EVAL ``path 65 5``; = [(1,16,1); (1,1,16); (3,1,14); (5,1,10); (7,1,4); (1,4,4)]
> EVAL ``MAP (\j. FUNPOW (zagier o flip) j (1,1,16)) [0 ..< 5]``; = [(1,1,16); (3,1,14); (5,1,10); (7,1,4); (1,4,4)]
> EVAL ``MAP (\j. FUNPOW (zagier o flip) j (5,5,2)) [0 ..< 4]``; = [(5,5,2); (1,8,2); (3,2,7); (7,2,2)]

Do I know that, for tik n /\ ~square n, path starting from (1,n DIV 4,1) leads to only one flip-fix?
Or we can just say: hopping (SQRT n) will lead to the first flip-fix, and later let tik n /\ prime n to resolve the issue.

involute_involute_fix_odd_period_fix
|- !f g s p x. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
               p = iterate_period (f o g) x /\ ODD p ==>
               !j. 0 < j /\ j < p ==> (FUNPOW (f o g) j x IN fixes g s <=> j = HALF p)

involute_involute_fix_orbit_fix_odd
|- !f g s p x. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
               p = iterate_period (f o g) x /\ ODD p ==> FUNPOW (f o g) (HALF p) x IN fixes g s

involute_involute_fix_sing_period_odd
|- !f g s p x. FINITE s /\ f involute s /\ g involute s /\ fixes f s = {x} /\
               p = iterate_period (f o g) x ==> ODD p
zagier_fixes_prime
|- !p. prime p /\ tik p ==> fixes zagier (mills p) = {(1,1,p DIV 4)}

A quick way to find iterate_period of triple x, without proof, by iterate from u to fixed v:

Definition path_period_def:
   path_period u v k = if (u = v) then k else path_period ((zagier o flip) u) v (k+1)
End
-- need a Termination proof.

Definition path_period_def:
   path_period n = let s = (1,1,n DIV 4) in WHILE (\(j,t). t <> s) (\(j,t). (SUC j, (zagier o flip) t)) (1, (zagier o flip) s)
End

> EVAL ``path_period 61``; = (11,1,1,15)  which means p = 11, back to (1,1,5) a zagier-fix at LAST.
> EVAL ``path 61 (1 + HALF 11)``; = [(1,15,1); (1,1,15); (3,1,13); (5,1,9); (7,1,3); (1,5,3); (5,3,3)]
> EVAL ``path 61 (HALF (1 + 11))``; = [(1,15,1); (1,1,15); (3,1,13); (5,1,9); (7,1,3); (1,5,3); (5,3,3)

> EVAL ``path_period 97``; = (27,1,1,24)  which means p = 27, back to (1,1,24) a zagier-fix at LAST.
> EVAL ``path 97 (1 + HALF 27)``; =
         [(1,24,1); (1,1,24); (3,1,22); (5,1,18); (7,1,12); (9,1,4); (1,6,4);
          (7,4,3); (1,8,3); (5,3,6); (7,6,2); (3,11,2); (1,2,12); (5,2,9); (9,2,2)]
> EVAL ``path 97 (HALF (1 + 27))``; =
         [(1,24,1); (1,1,24); (3,1,22); (5,1,18); (7,1,12); (9,1,4); (1,6,4);
          (7,4,3); (1,8,3); (5,3,6); (7,6,2); (3,11,2); (1,2,12); (5,2,9); (9,2,2)]
For ODD period p, (1 + p) is even, and HALF (1 + p) is an exact half.
But ODD_SUC_HALF  |- !n. ODD n ==> HALF (SUC n) = SUC (HALF n)


Definition zf_period_def:
   zf_period s = let u = s in WHILE (\(j,t). t <> u) (\(j,t). (SUC j, (zagier o flip) t)) (1, (zagier o flip) s)
End

Definition zf_pop_def:
   zf_pop n = REVERSE (WHILE (\ls. flip (HD ls) <> HD ls) (\ls. popping (SQRT n) (HD ls)::ls) [(1,n DIV 4,1)])
End

> EVAL ``zf_pop 5``; = [(1,1,1)]
> EVAL ``zf_pop 13``; = [(1,3,1); (3,1,1)]
> EVAL ``zf_pop 17``; = [(1,4,1); (3,1,2); (1,2,2)]
> EVAL ``zf_pop 29``; = [(1,7,1); (5,1,1)]
> EVAL ``zf_pop 37``; = [(1,9,1); (5,1,3); (1,3,3)]
> EVAL ``zf_pop 41``; = [(1,10,1); (5,1,4); (3,4,2); (5,2,2)]
> EVAL ``zf_pop 53``; = [(1,13,1); (7,1,1)]
> EVAL ``zf_pop 61``; = [(1,15,1); (7,1,3); (5,3,3)]
> EVAL ``zf_pop 73``; = [(1,18,1); (7,1,6); (5,6,2); (7,2,3); (5,3,4); (3,4,4)]
> EVAL ``zf_pop 89``; = [(1,22,1); (9,1,2); (7,2,5); (3,5,4); (5,4,4)]
> EVAL ``zf_pop 97``; = [(1,24,1); (9,1,4); (7,4,3); (5,3,6); (7,6,2); (9,2,2)]
> EVAL ``zf_pop 521``; = [(1,130,1); (21,1,20); (19,20,2); (21,2,10); (19,10,4);
                          (21,4,5); (19,5,8); (13,8,11); (9,11,10); (11,10,10)]
> EVAL ``zf_pop 653``; = [(1,163,1); (25,1,7); (17,7,13); (9,13,11); (13,11,11)]
> EVAL ``zf_pop 773``; = [(1,193,1); (27,1,11); (17,11,11)]
> EVAL ``zf_pop 797``; = [(1,199,1); (27,1,17); (7,17,11); (15,11,13); (11,13,13)]
> EVAL ``zf_pop 977``; = [(1,244,1); (31,1,4); (25,4,22); (19,22,7); (23,7,16);  (9,16,14);
                          (19,14,11); (25,11,8); (23,8,14); (5,14,17); (29,17,2); (31,2,2)]
> EVAL ``zf_pop 997``; = [(1,249,1); (31,1,9); (23,9,13); (29,13,3); (31,3,3)]
> EVAL ``zf_pop 1277``; = [(1,319,1); (35,1,13); (17,13,19); (21,19,11); (23,11,17); (11,17,17)]
> EVAL ``zf_pop 1801``; = [(1,450,1); (41,1,30); (19,30,12); (29,12,20); (11,20,21); (31,21,10);
                           (29,10,24); (19,24,15); (41,15,2); (39,2,35); (31,35,6); (41,6,5);
                           (39,5,14); (17,14,27); (37,27,4); (35,4,36); (37,36,3); (41,3,10);
                           (39,10,7); (31,7,30); (29,30,8); (35,8,18); (37,18,6); (35,6,24);
                           (13,24,17); (21,17,20); (19,20,18); (17,18,21); (25,21,14);
                           (31,14,15); (29,15,16); (35,16,9); (37,9,12); (35,12,12)]
> EVAL ``zf_pop 1933``; = [(1,483,1); (43,1,21); (41,21,3); (43,3,7); (41,7,9); (31,9,27);
                           (23,27,13); (29,13,21); (13,21,21)]
*)


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
