(* ------------------------------------------------------------------------- *)
(* Polynomial computations in monadic style.                                 *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "countPoly";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* val _ = load "SatisfySimps"; (* for SatisfySimps.SATISFY_ss *) *)

(* Get dependent theories local *)
(* val _ = load "countModuloTheory"; *)
open countMonadTheory countMacroTheory;
open countModuloTheory;

open bitsizeTheory complexityTheory;
open loopIncreaseTheory loopDecreaseTheory;
open loopDivideTheory loopListTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
open helperNumTheory helperSetTheory helperListTheory;
open helperFunctionTheory;

(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open pred_setTheory listTheory arithmeticTheory;
open dividesTheory gcdTheory;
open rich_listTheory listRangeTheory;

(* (* val _ = load "logPowerTheory"; *) *)
open logrootTheory logPowerTheory;

(* (* val _ = load "monadsyntax"; *) *)
open monadsyntax;
open pairTheory optionTheory;

(* val _ = load "ringInstancesTheory"; *)
open ringInstancesTheory; (* for ZN order *)

(* val _ = load "computeRingTheory"; *)
open computeRingTheory; (* for ZN_poly_cmult_alt *)
open computePolyTheory; (* for unity_mod_monomial *)

open polynomialTheory polyWeakTheory;

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "Count";


(* ------------------------------------------------------------------------- *)
(* Polynomial computations in monadic style Documentation                    *)
(* ------------------------------------------------------------------------- *)
(* Data type:
*)
(* Overloading:
*)
(* Definitions and Theorems (# are exported):

   Helper:

   Making polynomials:
   poly_extendM_def      |- !p k. poly_extendM p k =
                                  do
                                    k0 <- zeroM k;
                                    if k0 then unit p
                                    else do q <- consM 0 p; k' <- decM k; poly_extendM q k' od
                                  od
   poly_zeroM_def        |- !k. poly_zeroM k = poly_extendM [] k
   poly_oneM_def         |- !n k. poly_oneM n k =
                                  do
                                    k0 <- zeroM k;
                                    if k0 then unit []
                                    else
                                      do
                                        j <- decM k;
                                        p <- poly_zeroM n j;
                                        c <- modM 1 n;
                                        consM c p
                                      od
                                  od
#  poly_extendM_value    |- !n p k. valueOf (poly_extendM p k) = unity_mod_zero (ZN n) k ++ p
   poly_extendM_nil      |- !n k. valueOf (poly_extendM [] k) = unity_mod_zero (ZN n) k
#  poly_zeroM_value      |- !n k. valueOf (poly_zeroM n k) = unity_mod_zero (ZN n) k
#  poly_oneM_value       |- !n k. valueOf (poly_oneM n k) = unity_mod_one (ZN n) k
   poly_zeroM_weak       |- !n k. 0 < n ==> Weak (ZN n) (valueOf (poly_zeroM n k))
#  poly_zeroM_length     |- !n k. LENGTH (valueOf (poly_zeroM n k)) = k
   poly_oneM_weak        |- !n k. 0 < n ==> Weak (ZN n) (valueOf (poly_oneM n k))
#  poly_oneM_length      |- !n k. LENGTH (valueOf (poly_oneM n k)) = k
   poly_extendM_steps_thm
               |- !p k. stepsOf (poly_extendM p k) =
                        size k + if k = 0 then 0
                                 else 1 + size k + stepsOf (poly_extendM (0::p) (k - 1))
   poly_extendM_steps_by_dec_loop
               |- !p k. stepsOf (poly_extendM p k) =
                        if k = 0 then 1
                        else 1 + TWICE (size k) + stepsOf (poly_extendM (0::p) (k - 1))
   poly_extendM_steps_eqn
               |- !p k. stepsOf (poly_extendM p k) = 1 + SUM (MAP (\j. 1 + TWICE (size j)) [1 .. k])
   poly_extendM_steps_upper
               |- !p k. stepsOf (poly_extendM p k) <= 1 + k + TWICE k * size k
   poly_extendM_steps_bound
               |- !p k. stepsOf (poly_extendM p k) <= 4 * MAX 1 k * size k
   poly_zeroM_steps_eqn
               |- !n k. stepsOf (poly_zeroM n k) = 1 + SUM (MAP (\j. 1 + TWICE (size j)) [1 .. k])
   poly_zeroM_steps_upper
               |- !n k. stepsOf (poly_zeroM n k) <= 1 + k + TWICE k * size k
   poly_zeroM_steps_bound
               |- !n k. stepsOf (poly_zeroM n k) <= 4 * MAX 1 k * size k
   poly_oneM_steps_eqn
               |- !n k. stepsOf (poly_oneM n k) =
                        if k = 0 then 1
                        else 1 + SUM (MAP (\j. 1 + TWICE (size j)) [1 .. k]) + size n
   poly_oneM_steps_upper
               |- !n k. stepsOf (poly_oneM n k) <= 1 + k + TWICE (size k) + TWICE k * size k + size n
   poly_oneM_steps_bound
               |- !n k. stepsOf (poly_oneM n k) <= 7 * MAX 1 k * size k * size n

   Constant Polynomial:
   poly_constM_def       |- !n k c. poly_constM n k c =
                                    do
                                      k0 <- zeroM k;
                                      if k0 then unit []
                                      else
                                        do
                                          j <- decM k;
                                          p <- poly_zeroM n j;
                                          d <- modM c n;
                                          consM d p
                                        od
                                    od
#  poly_constM_value     |- !n k c. 0 < n ==> valueOf (poly_constM n k c) = unity_mod_const (ZN n) k c
   poly_constM_zero      |- !k c. valueOf (poly_constM 0 k c) = if k = 0 then [] else PAD_RIGHT 0 k [c MOD 0]
   poly_constM_weak      |- !n k c. 0 < n ==> Weak (ZN n) (valueOf (poly_constM n k c))
#  poly_constM_length    |- !n k c. LENGTH (valueOf (poly_constM n k c)) = k
   poly_constM_steps_eqn |- !n k c. stepsOf (poly_constM n k c) =
                                    if k = 0 then 1
                                    else 1 + SUM (MAP (\j. 1 + TWICE (size j)) [1 .. k]) + size c * size n
   poly_constM_steps_upper
                         |- !n k c. stepsOf (poly_constM n k c) <=
                                    1 + k + TWICE (size k) + TWICE k * size k + size c * size n
   poly_constM_steps_bound
                         |- !n k c. stepsOf (poly_constM n k c) <=
                                    7 * MAX 1 k * size k * size c * size n

   Powers of X:
   poly_X_expM_def       |- !n k m. poly_X_expM n k m =
                                    do
                                      k0 <- zeroM k;
                                      if k0 then unit []
                                      else
                                        do
                                          c <- modM 1 n;
                                          k1 <- oneM k;
                                          if k1 then consM c []
                                          else
                                            do
                                              j <- modM m k;
                                              h <- subM k j;
                                              i <- decM h;
                                              p <- poly_zeroM n i;
                                              q <- consM c p;
                                              poly_extendM q j
                                            od
                                        od
                                    od
#  poly_X_expM_value     |- !n k m. 0 < n ==> valueOf (poly_X_expM n k m) = unity_mod_X_exp (ZN n) k m
   poly_X_expM_zero      |- !k m. valueOf (poly_X_expM 0 k m) =
                                  if k = 0 then []
                                  else PAD_RIGHT 0 k (PAD_LEFT 0 (m MOD k + 1) [1 MOD 0])
   poly_X_expM_weak      |- !n k m. 0 < n ==> Weak (ZN n) (valueOf (poly_X_expM n k m))
#  poly_X_expM_length    |- !n k m. LENGTH (valueOf (poly_X_expM n k m)) = k
   poly_X_expM_steps_eqn |- !n k m. stepsOf (poly_X_expM n k m) =
                                    if k = 0 then 1
                                    else size n + TWICE (size k) +
                                         if k = 1 then 1
                                         else (if k = 0 then 0 else size m * size k) + 1 +
                                              size (MAX k (m MOD k)) + size (k - m MOD k) +
                                              stepsOf (poly_zeroM n (k - m MOD k - 1)) +
                                              stepsOf (poly_extendM
                                                 (1 MOD n::unity_mod_zero (ZN n) (k - m MOD k - 1)) (m MOD k))
   poly_X_expM_steps_upper
                         |- !n k m. stepsOf (poly_X_expM n k m) <=
                                    3 + TWICE k + size n + 4 * size k + size m * size k + 4 * k * size k
   poly_X_expM_steps_bound
                         |- !n k m. stepsOf (poly_X_expM n k m) <=
                                    15 * MAX 1 k * size k * size n * size m

   Polynomial operations:
   poly_eqM_def    |- !q p. poly_eqM p q =
                            do
                              p0 <- nullM p;
                              q0 <- nullM q;
                              if p0 then unit q0
                              else if q0 then unit p0
                              else
                                do
                                  h1 <- headM p;
                                  t1 <- tailM p;
                                  h2 <- headM q;
                                  t2 <- tailM q;
                                  e0 <- eqM h1 h2;
                                  if e0 then poly_eqM t1 t2 else unit F
                                od
                            od
#  poly_eqM_value  |- !p q. valueOf (poly_eqM p q) <=> p = q
   poly_eqM_steps_thm
                   |- !p q. stepsOf (poly_eqM p q) =
                            2 + if (p = []) \/ (q = []) then 0
                                else 4 + size (MAX (HD p) (HD q)) +
                                    if HD p <> HD q then 0 else stepsOf (poly_eqM (TL p) (TL q))
   poly_eqM_steps_by_list_loop
                   |- !p q. stepsOf (poly_eqM p q) =
                            if (p = []) \/ (q = []) then 2
                            else 6 + size (MAX (HD p) (HD q)) +
                                 if HD p <> HD q then 0 else stepsOf (poly_eqM (TL p) (TL q))
   poly_eqM_steps_by_sum_le
                   |- !p q k. (LENGTH p = k) /\ (LENGTH q = k) ==>
                              stepsOf (poly_eqM p q) <=
                              2 + SUM (GENLIST (\j. 6 + size (MAX (EL j p) (EL j q))) k)
   poly_eqM_steps_upper
                   |- !p q k n. Weak (ZN n) p /\ Weak (ZN n) q  /\
                                (LENGTH p = k) /\ (LENGTH q = k) ==>
                                stepsOf (poly_eqM p q) <= 2 + 6 * k + k * size n
   poly_eqM_steps_bound
                   |- !p q k n. Weak (ZN n) p /\ Weak (ZN n) q /\
                                (LENGTH p = k) /\ (LENGTH q = k) ==>
                                stepsOf (poly_eqM p q) <= 9 * MAX 1 k * size n


   poly_cmultM_def       |- !p n c. poly_cmultM n c p =
                                    do
                                      p0 <- nullM p;
                                      if p0 then unit []
                                      else
                                        do
                                          h <- headM p;
                                          t <- tailM p;
                                          k <- mmulM n c h;
                                          q <- poly_cmultM n c t;
                                          consM k q
                                        od
                                    od
#  poly_cmultM_value     |- !n c p. valueOf (poly_cmultM n c p) = weak_cmult (ZN n) c p
   poly_cmultM_value_alt |- !n c p. Weak (ZN n) p ==> valueOf (poly_cmultM n c p) = c oz p
   poly_cmultM_element   |- !n c p j. j < LENGTH p ==> EL j (valueOf (poly_cmultM n c p)) = (c * EL j p) MOD n
   poly_cmultM_weak      |- !n c p. 0 < n ==> Weak (ZN n) (valueOf (poly_cmultM n c p))
#  poly_cmultM_length    |- !n c p. LENGTH (valueOf (poly_cmultM n c p)) = LENGTH p
   poly_cmultM_steps_thm |- !n c p. stepsOf (poly_cmultM n c p) =
                                    if (p = []) then 1
                                    else 4 + size c * size (HD p) +
                                         size (c * HD p) * size n +
                                         stepsOf (poly_cmultM n c (TL p))
   poly_cmultM_steps_by_list_loop
                         |- !n c p. stepsOf (poly_cmultM n c p) =
                                    if (p = []) then 1
                                    else 4 + size c * size (HD p) +
                                         size (c * HD p) * size n +
                                         stepsOf (poly_cmultM n c (TL p))
   poly_cmultM_steps_eqn |- !n c p. stepsOf (poly_cmultM n c p) =
                                       1 + SUM (GENLIST
                                                  (\j. 4 + size c * size (EL j p) + size (c * (EL j p)) * size n)
                                                  (LENGTH p))
   poly_cmultM_steps_upper   |- !n c p k. Weak (ZN n) p /\ (LENGTH p = k) ==>
                                          stepsOf (poly_cmultM n c p) <=
                                          1 + 4 * k + TWICE k * size c * size n + k * size n ** 2
   poly_cmultM_steps_bound   |- !n c p k. Weak (ZN n) p /\ (LENGTH p = k) ==>
                                          stepsOf (poly_cmultM n c p) <=
                                          8 * MAX 1 k * size (MAX c n) * size n

   Polynomial weak addition:
   poly_addM_def         |- !q p n. poly_addM n p q =
                                    do
                                      p0 <- nullM p;
                                      q0 <- nullM q;
                                      if p0 then unit q
                                      else if q0 then unit p
                                      else
                                        do
                                          h1 <- headM p;
                                          h2 <- headM q;
                                          t1 <- tailM p;
                                          t2 <- tailM q;
                                          h <- maddM n h1 h2;
                                          r <- poly_addM n t1 t2;
                                          consM h r
                                        od
                                    od
#  poly_addM_value       |- !n p q. valueOf (poly_addM n p q) = weak_add (ZN n) p q
   poly_addM_value_alt   |- !n p q. Weak (ZN n) p /\ Weak (ZN n) q /\ (LENGTH p = LENGTH q) ==>
                                    valueOf (poly_addM n p q) = p +z q
   poly_addM_element     |- !n p q j. j < LENGTH p /\ j < LENGTH q ==>
                                      EL j (valueOf (poly_addM n p q)) = (EL j p + EL j q) MOD n
   poly_addM_weak        |- !n p q. 0 < n /\ (LENGTH p = LENGTH q) ==>
                                    Weak (ZN n) (valueOf (poly_addM n p q))
#  poly_addM_length      |- !n p q. LENGTH (valueOf (poly_addM n p q)) = MAX (LENGTH p) (LENGTH q)
   poly_addM_steps_thm   |- !n p q. stepsOf (poly_addM n p q) =
                                    if (p = []) \/ (q = []) then 2
                                    else 7 + size (MAX (HD p) (HD q)) +
                                         size (HD p + HD q) * size n +
                                         stepsOf (poly_addM n (TL p) (TL q))
   poly_addM_steps_by_list_loop
                         |- !n p q. stepsOf (poly_addM n p q) =
                                    if (p = []) \/ (q = []) then 2
                                    else 7 + size (MAX (HD p) (HD q)) +
                                         size (HD p + HD q) * size n +
                                         stepsOf (poly_addM n (TL p) (TL q))
   poly_addM_steps_eqn   |- !n p q k. (LENGTH p = k) /\ (LENGTH q = k) ==>
                                      stepsOf (poly_addM n p q) =
                                      2 + SUM (GENLIST (\j. 7 + size (MAX (EL j p) (EL j q)) +
                                                            size (EL j p + EL j q) * size n) k
   poly_addM_steps_upper |- !n p q k. Weak (ZN n) p /\ Weak (ZN n) q /\
                                      (LENGTH p = k) /\ (LENGTH q = k) ==>
                                      stepsOf (poly_addM n p q) <=
                                      2 + 7 * k + TWICE k * size n + k * size n ** 2
   poly_addM_steps_bound |- !n p q k. Weak (ZN n) p /\ Weak (ZN n) q /\
                                      (LENGTH p = k) /\ (LENGTH q = k) ==>
                                      stepsOf (poly_addM n p q) <= 12 * MAX 1 k * size n ** 2

   Polynomial multiplication by X:
   poly_lastM_def        |- !p. poly_lastM p =
                                do
                                  p0 <- nullM p;
                                  if p0 then unit (LAST [])
                                  else
                                    do
                                      h <- headM p;
                                      t <- tailM p;
                                      t0 <- nullM t;
                                      if t0 then unit h else poly_lastM t
                                    od
                                od
   poly_frontM_def       |- !p. poly_frontM p =
                                do
                                  p0 <- nullM p;
                                  if p0 then unit (FRONT [])
                                  else
                                    do
                                      h <- headM p;
                                      t <- tailM p;
                                      t0 <- nullM t;
                                      if t0 then unit [] else do q <- poly_frontM t; consM h q od
                                    od
                                od
   poly_turnM_def        |- !p. poly_turnM p =
                                do
                                  p0 <- nullM p;
                                  if p0 then unit []
                                  else do h <- poly_lastM p; t <- poly_frontM p; consM h t od
                                od
   poly_lastM_value      |- !p. valueOf (poly_lastM p) = LAST p
   poly_frontM_value     |- !p. valueOf (poly_frontM p) = FRONT p
   poly_turnM_value      |- !p. valueOf (poly_turnM p) = turn p
   poly_lastM_steps_thm  |- !p. stepsOf (poly_lastM p) =
                                if (p = []) then 1
                                else 4 + if (TL p = []) then 0 else stepsOf (poly_lastM (TL p))
   poly_lastM_steps_by_list_loop
                         |- !p. stepsOf (poly_lastM p) =
                                if (p = []) then 1
                                else 4 + if (TL p = []) then 0 else stepsOf (poly_lastM (TL p))
   poly_lastM_steps_upper|- !p. stepsOf (poly_lastM p) <= 1 + 4 * LENGTH p
   poly_frontM_steps_thm |- !p. stepsOf (poly_frontM p) =
                                if (p = []) then 1
                                else 4 + (if (TL p = []) then 0 else 1) +
                                     if (TL p = []) then 0 else stepsOf (poly_frontM (TL p))
   poly_frontM_steps_by_list_loop
                         |- !p. stepsOf (poly_frontM p) =
                                if (p = []) then 1
                                else 4 + (if (TL p = []) then 0 else 1) +
                                     if (TL p = []) then 0 else stepsOf (poly_frontM (TL p))
   poly_frontM_steps_upper |- !p. stepsOf (poly_frontM p) <= 1 + 5 * LENGTH p
   poly_turnM_steps_thm    |- !p. stepsOf (poly_turnM p) =
                                  if (p = []) then 1
                                  else 2 + stepsOf (poly_lastM p) + stepsOf (poly_frontM p)
   poly_turnM_weak         |- !n p. Weak (ZN n) p ==> Weak (ZN n) (valueOf (poly_turnM p))
   poly_turnM_length       |- !p. LENGTH (valueOf (poly_turnM p)) = LENGTH p
   poly_turnM_steps_upper  |- !p. stepsOf (poly_turnM p) <= 4 + 9 * LENGTH p
   poly_turnM_steps_bound  |- !p k. (LENGTH p = k) ==> stepsOf (poly_turnM p) <= 13 * MAX 1 k

   poly_lastM_steps_eqn  |- !p. stepsOf (poly_lastM p) = if (p = []) then 1 else 4 * LENGTH p
   poly_frontM_steps_eqn |- !p. stepsOf (poly_frontM p) = if (p = []) then 1 else 5 * LENGTH p - 1
   poly_turnM_steps_eqn  |- !p. stepsOf (poly_turnM p) = if (p = []) then 1 else 1 + 9 * LENGTH p

   poly_multM_def        |- !q p n. poly_multM n p q =
                                    do
                                      p0 <- nullM p;
                                      q0 <- nullM q;
                                      if p0 \/ q0 then unit []
                                      else
                                        do
                                          h <- headM q;
                                          t <- tailM q;
                                          p1 <- poly_cmultM n h p;
                                          r <- poly_turnM p;
                                          p2 <- poly_multM n r t;
                                          poly_addM n p1 p2;
                                        od
                                    od
#  poly_multM_value      |- !n p q. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q ==>
                                    valueOf (poly_multM n p q) = unity_mod_mult (ZN n) p q
   poly_multM_value_thm  |- !n p q k. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q /\ q <> [] /\ (LENGTH p = k) ==>
                                      valueOf (poly_multM n p q) = p *z q
   poly_multM_value_alt  |- !n p q k. 0 < n /\ 0 < k /\ Weak (ZN n) p /\ Weak (ZN n) q /\
                                      (LENGTH p = k) /\ (LENGTH q = k) ==>
                                      valueOf (poly_multM n p q) = p *z q
   poly_multM_weak       |- !n p q. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q ==>
                                    Weak (ZN n) (valueOf (poly_multM n p q))
   poly_multM_length     |- !n p q. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q ==>
                                    LENGTH (valueOf (poly_multM n p q)) =
                                    if q = [] then 0 else LENGTH p
   poly_multM_nil        |- !n p. 0 < n /\ Weak (ZN n) p ==> valueOf (poly_multM n p []) = []
   poly_multM_steps_thm  |- !n p q. stepsOf (poly_multM n p q) =
                                    if q = [] then 1
                                    else 3 + stepsOf (poly_turnM p) +
                                         stepsOf (poly_cmultM n (HD q) p) +
                                         stepsOf (poly_addM n
                                                    (weak_cmult (ZN n) (HD q) p)
                                                    (valueOf (poly_multM n (turn p) (TL q)))) +
                                         stepsOf (poly_multM n (turn p) (TL q))
   poly_multM_steps_nil  |- !n p. stepsOf (poly_multM n p []) = 1
   poly_multM_steps_sing_thm
                         |- !n p c. 0 < n /\ Weak (ZN n) p ==>
                                    stepsOf (poly_multM n p [c]) =
                                    6 + stepsOf (poly_turnM p) + stepsOf (poly_cmultM n c p)
   poly_multM_steps_sing_upper
                         |- !n p c k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
                                      stepsOf (poly_multM n p [c]) <=
                                      10 + 9 * k + 8 * MAX 1 k * size (MAX c n) * size n
   poly_multM_steps_sing_bound
                         |- !n p c k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
                                      stepsOf (poly_multM n p [c]) <=
                                      27 * MAX 1 k * size (MAX c n) * size n
   poly_multM_steps_by_list_loop
                         |- !n p q. stepsOf (poly_multM n p q) = if q = [] then 1
                                    else 3 + stepsOf (poly_turnM p) +
                                             stepsOf (poly_cmultM n (HD q) p) +
                                             stepsOf (poly_addM n
                                                        (weak_cmult (ZN n) (HD q) p)
                                                        (valueOf (poly_multM n (turn p) (TL q)))) +
                                             stepsOf (poly_multM n (turn p) (TL q))
   poly_multM_steps_body_upper
                         |- !n. (let body p q = 3 + stepsOf (poly_turnM p) +
                                     stepsOf (poly_cmultM n (HD q) p) +
                                     stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p)
                                                (valueOf (poly_multM n (turn p) (TL q))))
                                  in !p q. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q /\ q <> [] ==>
                                     body p q <= 10 + LENGTH p * (20 + TWICE (size n) + 4 * size n ** 2))
   poly_multM_steps_body_cover
                         |- !n. (let body p q = 3 + stepsOf (poly_turnM p) +
                                     stepsOf (poly_cmultM n (HD q) p) +
                                     stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p)
                                                (valueOf (poly_multM n (turn p) (TL q))))
                                  in !p q k. 0 < n /\ (LENGTH p = k) /\ (LENGTH q = k) /\
                                             Weak (ZN n) p /\ Weak (ZN n) q ==>
                                     !j. j < k ==> body (turn_exp p j) (DROP j q) <=
                                                   10 + k * (20 + TWICE (size n) + 4 * size n ** 2))
   poly_multM_steps_upper|- !n p q k. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q /\
                                      (LENGTH p = k) /\ (LENGTH q = k) ==>
                                      stepsOf (poly_multM n p q) <=
                                      1 + 10 * k + 20 * k ** 2 +
                                          TWICE (k ** 2) * size n + 4 * k ** 2 * size n ** 2
   poly_multM_steps_bound|- !n p q k. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q /\
                                      (LENGTH p = k) /\ (LENGTH q = k) ==>
                                      stepsOf (poly_multM n p q) <= 37 * MAX 1 k ** 2 * size n ** 2
   poly_multM_steps_bound_alt
                         |- !n p q k. 0 < n /\ 0 < k /\ Weak (ZN n) p /\ Weak (ZN n) q /\
                                      (LENGTH p = k) /\ (LENGTH q = k) ==>
                                      stepsOf (poly_multM n p q) <= 37 * k ** 2 * size n ** 2

   poly_sqM_def          |- !n p. poly_sqM n p = poly_multM n p p
#  poly_sqM_value        |- !n p. 0 < n /\ Weak (ZN n) p ==>
                                  valueOf (poly_sqM n p) = unity_mod_sq (ZN n) p
   poly_sqM_value_thm    |- !n p k. 0 < n /\ Weak (ZN n) p /\ p <> [] /\ (LENGTH p = k) ==>
                                    (valueOf (poly_sqM n p) = sqz p)
   poly_sqM_value_alt    |- !n p k. 0 < n /\ 0 < k /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
                                    (valueOf (poly_sqM n p) = sqz p)
   poly_sqM_weak         |- !n p. 0 < n /\ Weak (ZN n) p ==> Weak (ZN n) (valueOf (poly_sqM n p))
   poly_sqM_length       |- !n p. 0 < n /\ Weak (ZN n) p ==>
                                  LENGTH (valueOf (poly_sqM n p)) = LENGTH p
   poly_sqM_iterating_weak
                         |- !n p. 0 < n /\ Weak (ZN n) p ==>
                            !k. Weak (ZN n) (FUNPOW (\p. valueOf (poly_sqM n p)) k p)
   poly_sqM_iterating_length
                         |- !n p. 0 < n /\ Weak (ZN n) p ==>
                            !k. LENGTH (FUNPOW (\p. valueOf (poly_sqM n p)) k p) = LENGTH p
   poly_sqM_steps_thm    |- !n p. 0 < n /\ Weak (ZN n) p ==>
                                  stepsOf (poly_sqM n p) =
                                  if (p = []) then 1
                                  else 3 + stepsOf (poly_turnM p) +
                                       stepsOf (poly_cmultM n (HD p) p) +
                                       stepsOf (poly_addM n (weak_cmult (ZN n) (HD p) p)
                                                  (unity_mod_mult (ZN n) (turn p) (TL p))) +
                                       stepsOf (poly_multM n (turn p) (TL p))
   poly_sqM_steps_upper  |- !n p k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
                                    stepsOf (poly_sqM n p) <=
                                    1 + 10 * k + 20 * k ** 2 +
                                        TWICE (k ** 2) * size n + 4 * k ** 2 * size n ** 2
   poly_sqM_steps_bound  |- !n p k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
                                    stepsOf (poly_sqM n p) <= 37 * MAX 1 k ** 2 * size n ** 2
   poly_sqM_steps_bound_alt
                         |- !n p k. 0 < n /\ 0 < k /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
                                    stepsOf (poly_sqM n p) <= 37 * k ** 2 * size n ** 2

   poly_expM_def         |- !p n j. poly_expM n p j =
                                    do
                                      j0 <- zeroM j;
                                      if j0 then
                                        do t <- consM 1 []; q <- poly_cmultM n 0 p; poly_addM n t q od
                                      else
                                        do
                                          p1 <- poly_sqM n p;
                                          h <- halfM j;
                                          q <- poly_expM n p1 h;
                                          ifM (evenM j) (return q) (poly_multM n p q)
                                        od
                                    od
#  poly_expM_value       |- !n p j. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q ==>
                                    valueOf (poly_expM n p j) = unity_mod_exp (ZN n) p j
   poly_expM_value_thm   |- !n p j k. 1 < n /\ Weak (ZN n) p /\ p <> [] /\ (LENGTH p = k) ==>
                                         (valueOf (poly_expM n p j) = p **z j)
   poly_expM_value_alt   |- !n p j k. 1 < n /\ 0 < k /\ zweak p /\ (LENGTH p = k) ==>
                                         (valueOf (poly_expM n p j) = p **z j)
   poly_expM_weak        |- !n p j. 0 < n /\ Weak (ZN n) p ==> Weak (ZN n) (valueOf (poly_expM n p j))
   poly_expM_length      |- !n p j. 0 < n /\ Weak (ZN n) p ==>
                                    LENGTH (valueOf (poly_expM n p j)) =
                                    if n = 1 then 0 else if j = 0 then 1 else LENGTH p
   poly_expM_0           |- !n p. valueOf (poly_expM n p 0) = if n = 1 then [] else [1]
   poly_expM_trivial     |- !p j. Weak (ZN 1) p ==> valueOf (poly_expM 1 p j) = []
   poly_expM_steps_thm   |- !n p j. stepsOf (poly_expM n p j) =
                                    size j +
                                    if j = 0 then size n + if n = 1 then 0 else 1
                                    else 1 + 4 * size j + stepsOf (poly_sqM n p) +
                                         (if EVEN j then 0 else
                                          stepsOf (poly_multM n p
                                                    (valueOf (poly_expM n
                                                                (valueOf (poly_sqM n p)) (HALF j))))) +
                                         stepsOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))
   poly_expM_steps_by_div_loop
                         |- !n. (let body p j = 1 + 5 * size j + stepsOf (poly_sqM n p) +
                                       if EVEN j then 0
                                       else stepsOf (poly_multM n p
                                                      (valueOf (poly_expM n
                                                                 (valueOf (poly_sqM n p)) (HALF j))))
                                  in !p j. stepsOf (poly_expM n p j) =
                                           if j = 0 then 1 + size n + if n = 1 then 0 else 1
                                           else body p j +
                                                stepsOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j)))
   poly_expM_body_upper  |- !n. (let body p j = 1 + 5 * size j + stepsOf (poly_sqM n p) +
                                       if EVEN j then 0
                                       else stepsOf (poly_multM n p
                                                      (valueOf (poly_expM n
                                                                 (valueOf (poly_sqM n p)) (HALF j))))
                                  in !p j k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
                                             body p j <=
                                             1 + 5 * size j + 74 * MAX 1 k ** 2 * size n ** 2)
   poly_expM_body_bound  |- !n. (let body p j = 1 + 5 * size j + stepsOf (poly_sqM n p) +
                                       if EVEN j then 0
                                       else stepsOf (poly_multM n p
                                                      (valueOf (poly_expM n
                                                                 (valueOf (poly_sqM n p)) (HALF j))))
                                  in !p j k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
                                             body p j <= 80 * size j * MAX 1 k ** 2 * size n ** 2)
   poly_expM_steps_upper |- !p n j k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
                                      stepsOf (poly_expM n p j) <=
                                      2 + size n + 80 * MAX 1 k ** 2 * size j ** 2 * size n ** 2
   poly_expM_steps_bound |- !p n j k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
                                      stepsOf (poly_expM n p j) <=
                                      83 * MAX 1 k ** 2 * size j ** 2 * size n ** 2
   poly_expM_steps_bound_alt
                         |- !p n j k. 1 < n /\ 0 < k /\ zweak p /\ (LENGTH p = k) ==>
                                      stepsOf (poly_expM n p j) <=
                                      83 * k ** 2 * size j ** 2 * size n ** 2

   poly_get_coeffM_def   |- !p j. poly_get_coeffM p j =
                                  do
                                    j0 <- zeroM j;
                                    if j0 then headM p
                                    else do q <- tailM p; i <- decM j; poly_get_coeffM q i od
                                  od
   poly_put_coeffM_def   |- !x p j. poly_put_coeffM x p j =
                                    do
                                      q <- tailM p;
                                      j0 <- zeroM j;
                                      if j0 then consM x q
                                      else
                                        do
                                          h <- headM p;
                                          i <- decM j;
                                          p1 <- poly_put_coeffM x q i;
                                          consM h p1
                                        od
                                    od

*)

(* Eliminate parenthesis around equality *)
val _ = ParseExtras.tight_equality();

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* for EVAL IFm *)
val _ = computeLib.set_skip computeLib.the_compset ``ifM`` (SOME 1);
(* EVAL IFm must be in current script, e.g. EVAL ``expn 1 2 3``; *)

(* ------------------------------------------------------------------------- *)
(* Computations in (ZN n)[X]/(unity k).                                      *)
(* ------------------------------------------------------------------------- *)

(* Note:
All polynomial computations are carried out in (MOD n, unity k).
To simplify computations, the polynomials are not normalised,
so they all have the same length k:
                         <---- k ----->
poly modulus (unity k):  0 0 0 ... 0 0 | 1
polynomial remainders:   . . . ... . .

Thus the little theory of ZN_unity_mod is based on weak polynomials.
*)

(* ------------------------------------------------------------------------- *)
(* Polynomial Computations in monadic style.                                 *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Making polynomials.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Pseudocode:
   Given a polynomial p, extend its length to k by prefix with 0.
   list_extend p k:
      if k = 0, return p               // [] ++ p = p
      q <- 0::p                        // prefix with 0
      return list_extend q (k - 1)     // extend result with (k - 1) 0 prefix
*)

(* Extend poly to length k. *)
Definition poly_extendM_def:
  poly_extendM p k =
      do
        k0 <- zeroM k;
        if k0 then return p
        else do
               q <- consM 0 p;
               j <- decM k;
               poly_extendM q j;
             od
      od
Termination
  WF_REL_TAC `measure (λ(p,k). k)` >> simp[]
End

(*
> EVAL ``poly_extendM [] 7``; = ([0; 0; 0; 0; 0; 0; 0],Count 42): thm
*)

(* Pseudocode:
   Extend |0| to length k.
   list_zero k:
      return list_extend [] k           // starting with [] for list_extend
*)

(* Make |0| of length k *)
val poly_zeroM_def = Define`
    poly_zeroM (n:num) k = poly_extendM [] k
`;

(* Pseudocode:
   Extend |1 (mod n)| to length k.
   list_one n k:
      if k = 0, return []               // [] has length = 0
      t <- list_extend [] (k - 1)       // extend |0| to length (k - 1)
      return (1 (mod n))::t             // put in the constant term
*)

(* Make |1| of length k *)
val poly_oneM_def = Define`
    poly_oneM n k =
      do
        k0 <- zeroM k;
        if k0 then return []
        else do
               j <- decM k;
               p <- poly_zeroM n j;
               c <- modM 1 n; (* gives 1 MOD 0 if n = 0 *)
               consM c p; (* LENGTH is 1 + j = k *)
             od
      od
`;
(* Note:
poly_oneM n k can be defined as (later) poly_constM n k 1,
but then the theorems will have a prefix: 0 < n.
It just happens that poly_constM theorems are still valid at n = 0 when c = 1.
*)

(*
> EVAL ``poly_zeroM 10 7``; = ([0; 0; 0; 0; 0; 0; 0],Count 42): thm
> EVAL ``poly_oneM 10 7``; = ([1; 0; 0; 0; 0; 0; 0], Count 46): thm
> EVAL ``poly_oneM 0 7``; = ([1 MOD 0; 0; 0; 0; 0; 0; 0],Count 42): thm
*)


(* Theorem: valueOf (poly_extendM p k) = (unity_mod_zero (ZN n) k) ++ p *)
(* Proof:
   By induction from poly_extendM_def.
   If k = 0,
        valueOf (poly_extendM p 0)
      = p                            by poly_extendM_def
      = [] ++ p                      by APPEND
   If k <> 0,
      Let f = K 0.
        valueOf (poly_extendM p k)
      = valueOf (poly_extendM (0::p) (k - 1))         by poly_extendM_def
      = unity_mod_zero (ZN n) (k - 1) ++ [0] ++ p     by induction hypothesis
      = PAD_RIGHT 0 (k - 1) [0] ++ [0] ++ p           by unity_mod_zero_def, unity_mod_const_def, ZN_property
      = SNOC 0 (PAD_RIGHT 0 (k - 1 [0])) ++ p         by SNOC_APPEND
      = PAD_RIGHT 0 SUC (k - 1) [0] ++ p              by PAD_RIGHT_SNOC, 1 <= k
      = PAD_RIGHT 0 k [0] ++ p                        by SUC (k - 1) = k, k <> 0
      = unity_mod_zero (ZN n) k ++ p                  by unity_mod_zero_def, unity_mod_const_def, ZN_property
*)
val poly_extendM_value = store_thm(
  "poly_extendM_value[simp]",
  ``!n p k. valueOf (poly_extendM p k) = (unity_mod_zero (ZN n) k) ++ p``,
  strip_tac >>
  ho_match_mp_tac (theorem "poly_extendM_ind") >>
  rw[] >>
  (Cases_on `k = 0` >> rw[unity_mod_zero_def, unity_mod_const_def, ZN_property]) >-
  rw[Once poly_extendM_def] >>
  rw[Once poly_extendM_def, unity_mod_zero_def, unity_mod_const_def, ZN_property] >| [
    `k = 1` by decide_tac >>
    rw[PAD_RIGHT],
    `SUC (k - 1) = k` by decide_tac >>
    `PAD_RIGHT 0 (k - 1) [0] ++ [0] = SNOC 0 (PAD_RIGHT 0 (k - 1) [0])` by rw[] >>
    `_ = PAD_RIGHT 0 (SUC (k - 1)) [0]` by rw[PAD_RIGHT_SNOC] >>
    metis_tac[]
  ]);

(* Theorem: valueOf (poly_extendM [] k) = unity_mod_zero (ZN n) k *)
(* Proof:
     valueOf (poly_extendM [] k)
   = unity_mod_zero (ZN n) k ++ []       by poly_extendM_value
   = unity_mod_zero (ZN n) k             by APPEND_NIL
*)
val poly_extendM_nil = store_thm(
  "poly_extendM_nil",
  ``!n k. valueOf (poly_extendM [] k) = unity_mod_zero (ZN n) k``,
  metis_tac[poly_extendM_value, APPEND_NIL]);

(* Theorem: valueOf (poly_zeroM n k) = unity_mod_zero (ZN n) k *)
(* Proof:
     valueOf (poly_zeroM n k)
   = valueOf (poly_extendM [] k)     by poly_zeroM_def
   = unity_mod_zero (ZN n) k ++ []   by poly_extendM_value
   = unity_mod_zero (ZN n) k         by APPEND_NIL
*)
val poly_zeroM_value = store_thm(
  "poly_zeroM_value[simp]",
  ``!n k. valueOf (poly_zeroM n k) = unity_mod_zero (ZN n) k``,
  metis_tac[poly_zeroM_def, poly_extendM_value, APPEND_NIL]);

(* Theorem: valueOf (poly_oneM n k) = unity_mod_one (ZN n) k *)
(* Proof:
   If k = 0,
         valueOf (poly_oneM n 0)
       = valueOf (return [])         by poly_oneM_def, k = 0
       = []
       = unity_mod_one (ZN n) 0      by unity_mod_one_def, unity_mod_const_def
   If k = 1,
         valueOf (poly_oneM n 1)
       = 1::[]                       by unity_mod_zero_def, unity_mod_const_def, k = 1
       = [1]                         by CONS
       = unity_mod_one (ZN n) 1      by unity_mod_one_def, unity_mod_const_def, k = 1
   If k <> 1,
      Then 0 < k - 1, and SUC (k - 1) = k                 by arithmetic
         valueOf (poly_oneM n k)
       = 1 MOD n::valueOf (poly_zeroM n (k - 1))          by poly_oneM_def, 0 < k
       = 1 MOD n::unity_mod_zero (ZN n) (k - 1)           by poly_zeroM_value

      Let c = (ZN n).sum.exp (ZN n).prod.id 1.
      Then c = 1 MOD n                                    by ZN_num_1
         unity_mod_one (ZN n) k
       = PAD_RIGHT 0 k [c]                   by unity_mod_one_def, unity_mod_const_def, ZN_property
       = PAD_RIGHT 0 (SUC (k - 1)) (c::[])   by k = SUC (k - 1)
       = c::PAD_RIGHT 0 (k - 1) []           by PAD_RIGHT_CONS
       = c::PAD_RIGHT 0 (k - 1) [0]          by PAD_RIGHT_NIL_EQ, 0 < k - 1
       = c::unity_mod_zero (ZN n) (k - 1)    by unity_mod_zero_def, unity_mod_const_def, ZN_property
      Thus LHS = RHS.
*)
val poly_oneM_value = store_thm(
  "poly_oneM_value[simp]",
  ``!n k. valueOf (poly_oneM n k) = unity_mod_one (ZN n) k``,
  rpt strip_tac >>
  Cases_on `k = 0` >-
  rw[poly_oneM_def, unity_mod_one_def, unity_mod_const_def] >>
  rw[poly_oneM_def, unity_mod_one_def, unity_mod_const_def] >>
  qabbrev_tac `c = (ZN n).sum.exp (ZN n).prod.id 1` >>
  `c = 1 MOD n` by rw[ZN_num_1, Abbr`c`] >>
  rw[ZN_property] >>
  Cases_on `k = 1` >-
  rw[unity_mod_zero_def, unity_mod_const_def, PAD_RIGHT] >>
  `0 < k - 1` by decide_tac >>
  `SUC (k - 1) = k` by decide_tac >>
  qabbrev_tac `c = 1 MOD n` >>
  `c::unity_mod_zero (ZN n) (k - 1) = c::PAD_RIGHT 0 (k - 1) [0]` by rw[unity_mod_zero_def, unity_mod_const_def, ZN_property] >>
  `_ = c::PAD_RIGHT 0 (k - 1) []` by rw[PAD_RIGHT_NIL_EQ] >>
  `_ = PAD_RIGHT 0 k [c]` by metis_tac[PAD_RIGHT_CONS] >>
  rw[]);

(* Theorem: 0 < n ==> Weak (ZN n) (valueOf (poly_zeroM n k)) *)
(* Proof:
     Weak (ZN n) (valueOf (poly_zeroM n k))
   = Weak (ZN n) (unity_mod_zero (ZN n) k)      by poly_zeroM_value
   = Weak (ZN n) (unity_mod_const (ZN n) k 0)   by unity_mod_zero_def
   = T                                          by ZN_unity_mod_const_weak, 0 < n
*)
val poly_zeroM_weak = store_thm(
  "poly_zeroM_weak",
  ``!n k. 0 < n ==> Weak (ZN n) (valueOf (poly_zeroM n k))``,
  rw[unity_mod_zero_def, ZN_unity_mod_const_weak]);

(* Theorem: LENGTH (valueOf (poly_zeroM n k)) = k *)
(* Proof:
     LENGTH (valueOf (poly_zeroM n k))
   = LENGTH (unity_mod_zero (ZN n) k)     by poly_zeroM_value
   = k                                    by unity_mod_zero_length
*)
val poly_zeroM_length = store_thm(
  "poly_zeroM_length[simp]",
  ``!n k. LENGTH (valueOf (poly_zeroM n k)) = k``,
  rw[unity_mod_zero_length]);

(* Theorem: 0 < n ==> Weak (ZN n) (valueOf (poly_oneM n k)) *)
(* Proof:
     Weak (ZN n) (valueOf (poly_oneM n k))
   = Weak (ZN n) (unity_mod_one (ZN n) k)       by poly_oneM_value
   = Weak (ZN n) (unity_mod_const (ZN n) k 1)   by unity_mod_one_def
   = T                                          by ZN_unity_mod_const_weak, 0 < n
*)
val poly_oneM_weak = store_thm(
  "poly_oneM_weak",
  ``!n k. 0 < n ==> Weak (ZN n) (valueOf (poly_oneM n k))``,
  rw[unity_mod_one_def, ZN_unity_mod_const_weak]);

(* Theorem: LENGTH (valueOf (poly_oneM n k)) = k *)
(* Proof:
     LENGTH (valueOf (poly_oneM n k))
   = LENGTH (unity_mod_one (ZN n) k)     by poly_oneM_value
   = k                                   by unity_mod_one_length
*)
val poly_oneM_length = store_thm(
  "poly_oneM_length[simp]",
  ``!n k. LENGTH (valueOf (poly_oneM n k)) = k``,
  rw[unity_mod_one_length]);

(* Theorem: stepsOf (poly_extendM p k) =
            size k + if (k = 0) then 0 else 1 + size k + stepsOf (poly_extendM (0::p) (k - 1)) *)
(* Proof:
     stepsOf (poly_extendM p k)
   = stepsOf (zeroM k) + if (k = 0) then 0 else
     stepsOf (consM 0 p) + stepsOf (decM k) +
     stepsOf (poly_extendM (0::p) (k - 1))     by poly_extendM_def
   = size k + if (k = 0) then 0 else 1 + size k + stepsOf (poly_extendM (0::p) (k - 1))
*)
val poly_extendM_steps_thm = store_thm(
  "poly_extendM_steps_thm",
  ``!p k. stepsOf (poly_extendM p k) =
           size k + if (k = 0) then 0 else 1 + size k + stepsOf (poly_extendM (0::p) (k - 1))``,
  ho_match_mp_tac (theorem "poly_extendM_ind") >>
  (rw[] >> rw[Once poly_extendM_def]));

(* Theorem: stepsOf (poly_extendM p k) =
            if k = 0 then 1 else 1 + 2 * size k + stepsOf (poly_extendM (0::p) (k - 1)) *)
(* Proof:
     stepsOf (poly_extendM p k)
   = size k + if (k = 0) then 0
     else 1 + size k + stepsOf (poly_extendM (0::p) (k - 1))    by poly_extendM_steps_thm
   = if k = 0 then size k
     else 1 + 2 * size k + stepsOf (poly_extendM (0::p) (k - 1))
   = if k = 0 then 1 else 1 + 2 * size k + stepsOf (poly_extendM (0::p) (k - 1))
*)
val poly_extendM_steps_by_dec_loop = store_thm(
  "poly_extendM_steps_by_dec_loop",
  ``!p k. stepsOf (poly_extendM p k) =
         if k = 0 then 1 else 1 + 2 * size k + stepsOf (poly_extendM (0::p) (k - 1))``,
  rw[Once poly_extendM_steps_thm]);

(*
This puts poly_extendM_steps in the category: decreasing loop with cons and body.
   param_seekM_steps_by_inc_loop:
        !p k. loop p k = if k = 0 then quit p else body p k + loop (0::p) (k - 1)
suitable for: loop2_dec_count_eqn
*)


(* Theorem: stepsOf (poly_extendM p k) = 1 + SUM (MAP (\j. 1 + 2 * size j) [1 .. k]) *)
(* Proof:
   Let quit = (\p. 1),
       body = (\p k. 1 + 2 * size k),
       f = (\p. 0::p),
       loop = (\p k. stepsOf (poly_extendM p k)).

   Then !p k. loop p k = if k = 0 then quit p else body p k + loop (f p) (k - 1).
   Let n = hop 1 k,
       z = FUNPOW f n k,
       g = (\j. 1 + 2 * size j).
   Note n = hop 1 k = k                                           by hop_1_n
        loop p k
      = quit z +
        SUM (GENLIST (\j. body (FUNPOW f j p) (k - j * 1)) k)     by loop2_dec_count_eqn
      = 1 + SUM (GENLIST (\j. g (k - j)) k)                       by expanding body
      = 1 + SUM (MAP g [1 .. k])                                  by SUM_GENLIST_REVERSE
*)
val poly_extendM_steps_eqn = store_thm(
  "poly_extendM_steps_eqn",
  ``!p k. stepsOf (poly_extendM p k) = 1 + SUM (MAP (\j. 1 + 2 * size j) [1 .. k])``,
  rpt strip_tac >>
  qabbrev_tac `quit = \p:num list. 1` >>
  qabbrev_tac `f = \p. 0::p` >>
  qabbrev_tac `g = \j. 1 + 2 * size j` >>
  qabbrev_tac `body = λ(p:num list) k. g k` >>
  qabbrev_tac `loop = \p k. stepsOf (poly_extendM p k)` >>
  `loop p k = 1 + SUM (MAP g [1 .. k])` suffices_by rw[] >>
  `0 < 1` by decide_tac >>
  `!p k. loop p k = if k = 0 then quit p else body p k + loop (f p) (k - 1)` by metis_tac[poly_extendM_steps_by_dec_loop] >>
  imp_res_tac loop2_dec_count_eqn >>
  first_x_assum (qspecl_then [`k`, `p`] strip_assume_tac) >>
  qabbrev_tac `foo = !p k. loop p k = if k = 0 then quit p else body p k + loop (f p) (k - 1)` >>
  fs[hop_1_n, SUM_GENLIST_REVERSE, Abbr`quit`, Abbr`body`]);

(* This is the first explicit solution of count by sum,
   showing stepsOf (poly_extendM p k) is independent of list p. *)

(* Theorem: stepsOf (poly_extendM p k) <= 1 + k + 2 * k * size k *)
(* Proof:
       stepsOf (poly_extendM p k)
     = 1 + SUM (MAP (\j. 1 + 2 * size j) [1 .. k])    by poly_extendM_steps_eqn
    <= 1 + SUM (GELNLIST (K (1 + 2 * size k)) k)      by SUM_LE, size_monotone_le
     = 1 + (1 + 2 * size k) * k                       by SUM_GENLIST_K
     = 1 + k + 2 * k * size k                         by RIGHT_ADD_DISTRIB
   Or,
   Using the same abbreviations as poly_extendM_steps_eqn,
   with MONO g                                        by size_monotone_le
       loop p k
    <= quit (FUNPOW f (hop 1 k) p) + hop 1 k * g k    by loop2_dec_count_mono_le
     = 1 + k * (1 + 2 * size k)                       by hop_1_n, expanding g
     = 1 + k + 2 * k * size k                         by LEFT_ADD_DISTRIB
*)
val poly_extendM_steps_upper = store_thm(
  "poly_extendM_steps_upper",
  ``!p k. stepsOf (poly_extendM p k) <= 1 + k + 2 * k * size k``,
  rpt strip_tac >>
  qabbrev_tac `f = \j. 1 + 2 * size j` >>
  qabbrev_tac `c = 1 + 2 * size k` >>
  `stepsOf (poly_extendM p k) = 1 + SUM (MAP f [1 .. k])` by rw[poly_extendM_steps_eqn, Abbr`f`] >>
  `SUM (MAP f [1 .. k]) <= SUM (GENLIST (K c) k)` by
  (irule SUM_LE >>
  `LENGTH [1 .. k] = k` by rw[listRangeINC_LEN] >>
  rw[listRangeINC_EL, EL_MAP, EL_GENLIST, Abbr`f`, Abbr`c`] >>
  rw[size_monotone_le]) >>
  `SUM (GENLIST (K c) k) = c * k` by rw[SUM_GENLIST_K] >>
  `c * k = (1 + 2 * size k) * k` by rw[Abbr`c`] >>
  decide_tac);
(* Direct proof is easier, rather than using loop2_dec_count_mono_le. *)

(* Theorem: stepsOf (poly_extendM p k) <= 4 * (MAX 1 k) * size k *)
(* Proof:
      stepsOf (poly_extendM p k)
   <= 1 + k + 2 * k * size k         by poly_extendM_steps_upper
   <= (1 + 1 + 2) * k * size k       by dominant term
    = 4 * k * size k
   Use (MAX 1 k) to cater for k = 0.
*)
val poly_extendM_steps_bound = store_thm(
  "poly_extendM_steps_bound",
  ``!p k. stepsOf (poly_extendM p k) <= 4 * (MAX 1 k) * size k``,
  rpt strip_tac >>
  `stepsOf (poly_extendM p k) <= 1 + k + 2 * k * size k` by rw[poly_extendM_steps_upper] >>
  qabbrev_tac `m = MAX 1 k` >>
  qabbrev_tac `t = m * size k` >>
  `stepsOf (poly_extendM p k) <= 4 * t` suffices_by rw[Abbr`t`] >>
  `1 <= m /\ k <= m` by rw[Abbr`m`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `k <= t` by
  (`m <= t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k * size k <= t` by rw[Abbr`t`] >>
  decide_tac);

(* Theorem: stepsOf (poly_zeroM n k) = 1 + SUM (MAP (\j. 1 + 2 * size j) [1 .. k]) *)
(* Proof:
    stepsOf (poly_zeroM n k)
  = stepsOf (poly_extendM [] k)                  by poly_zeroM_def
  = 1 + SUM (MAP (\j. 1 + 2 * size j) [1 .. k])  by poly_extendM_steps_eqn
*)
val poly_zeroM_steps_eqn = store_thm(
  "poly_zeroM_steps_eqn",
  ``!n k. stepsOf (poly_zeroM n k) = 1 + SUM (MAP (\j. 1 + 2 * size j) [1 .. k])``,
  rw[poly_zeroM_def, poly_extendM_steps_eqn]);

(* Theorem: stepsOf (poly_zeroM n k) <= 1 + k + 2 * k * size k *)
(* Proof:
     stepsOf (poly_zeroM n k)
   = stepsOf (poly_extendM [] k)       by poly_zeroM_def
  <= 1 + k + 2 * k * size k            by poly_extendM_steps_upper
*)
val poly_zeroM_steps_upper = store_thm(
  "poly_zeroM_steps_upper",
  ``!n k. stepsOf (poly_zeroM n k) <= 1 + k + 2 * k * size k``,
  rw_tac std_ss[poly_zeroM_def, poly_extendM_steps_upper]);

(* Theorem: stepsOf (poly_zeroM n k) <= 4 * MAX 1 k * size k *)
(* Proof:
     stepsOf (poly_zeroM n k)
   = stepsOf (poly_extendM [] k)       by poly_zeroM_def
  <= 4 * MAX 1 k * size k              by poly_extendM_steps_bound
*)
val poly_zeroM_steps_bound = store_thm(
  "poly_zeroM_steps_bound",
  ``!n k. stepsOf (poly_zeroM n k) <= 4 * MAX 1 k * size k``,
  rw_tac std_ss[poly_zeroM_def, poly_extendM_steps_bound]);

(* Theorem: stepsOf (poly_oneM n k) =
            if k = 0 then 1
            else 1 + SUM (MAP (\j. 1 + 2 * size j) [1 .. k]) + size n *)
(* Proof:
    stepsOf (poly_oneM n k)
  = stepsOf (zeroM k) + if k = 0 then 0
    else stepsOf (decM k) +
         stepsOf (poly_zeroM n (k - 1)) +
         stepsOf (modM 1 n) +
         stepsOf (consM (1 MOD n) (unity_mod_zero (ZN n) k))  by poly_oneM_def
  = size k + if k = 0 then 0
    else size k + (1 + SUM (MAP (\j. 1 + 2 * size j) [1 .. (k - 1)])) +
         (size 1 * size n) + 1           by poly_zeroM_steps_eqn
  = if k = 0 then 1
    else 1 + (1 + 2 * size k) + SUM (MAP (\j. 1 + 2 * size j) [1 .. k]) + size n
                                                              by size_0, moving last 1 to front
  = if k = 0 then 1
    else 1 + SUM (MAP (\j. 1 + 2 * size j) [1 .. k]) + size n
                                                              by listRangeINC_SUM_MAP
*)
val poly_oneM_steps_eqn = store_thm(
  "poly_oneM_steps_eqn",
  ``!n k. stepsOf (poly_oneM n k) =
         if k = 0 then 1
         else 1 + SUM (MAP (\j. 1 + 2 * size j) [1 .. k]) + size n``,
  rpt strip_tac >>
  (Cases_on `k = 0` >> simp[]) >-
  rw[poly_oneM_def] >>
  simp[poly_oneM_def, poly_zeroM_steps_eqn] >>
  qabbrev_tac `f = \j. 2 * size j + 1` >>
  `SUC (k - 1) = k` by decide_tac >>
  `SUM (MAP f [1 .. k]) = f k + SUM (MAP f [1 .. (k - 1)])` by metis_tac[listRangeINC_SUM_MAP, ADD1] >>
  `f k = 2 * size k + 1` by rw[Abbr`f`] >>
  decide_tac);

(* Theorem: stepsOf (poly_oneM n k) <= 1 + k + 2 * size k + 2 * k * size k + size n *)
(* Proof:
     stepsOf (poly_oneM n k)
   = stepsOf (zeroM k) + if k = 0 then 0
     else stepsOf (decM k) +
          stepsOf (poly_zeroM n (k - 1)) +
          stepsOf (modM 1 n) +
          stepsOf (consM (1 MOD n) (unity_mod_zero (ZN n) k))  by poly_oneM_def
  <= size k + if k = 0 then 0
     else size k + (1 + (k - 1) + 2 * (k - 1) * size (k - 1)) +
                   (size 1 * size n) + 1                       by poly_zeroM_steps_upper
  <= size k + size k + k + 2 * k * size k + size n + 1         by size_1, size_monotone_lt
   = 1 + k + 2 * size k + 2 * k * size k + size n
*)
val poly_oneM_steps_upper = store_thm(
  "poly_oneM_steps_upper",
  ``!n k. stepsOf (poly_oneM n k) <= 1 + k + 2 * size k + 2 * k * size k + size n``,
  rw[poly_oneM_def] >>
  `stepsOf (poly_zeroM n (k - 1)) <= 1 + (k - 1) + 2 * (k - 1) * size (k - 1)` by rw[poly_zeroM_steps_upper] >>
  `1 + (k - 1) = k` by decide_tac >>
  `size (k - 1) <= size k` by rw[size_monotone_lt] >>
  `2 * (k - 1) * size (k - 1) <= 2 * k * size k` by rw[LE_MONO_MULT2] >>
  decide_tac);

(* Theorem: stepsOf (poly_oneM n k) <= 7 * (MAX 1 k) * size k * size n *)
(* Proof:
      stepsOf (poly_oneM n k)
   <= 1 + k + 2 * size k + 2 * k * size k + size n    by poly_oneM_steps_upper
   <= (1 + 1 + 2 + 2 + 1) * k * size k * size n       by dominant term
    = 7 * k * size k * size n
   Use (MAX 1 k) to cater for k = 0.
*)
val poly_oneM_steps_bound = store_thm(
  "poly_oneM_steps_bound",
  ``!n k. stepsOf (poly_oneM n k) <= 7 * (MAX 1 k) * size k * size n``,
  rpt strip_tac >>
  `stepsOf (poly_oneM n k) <= 1 + k + 2 * size k + 2 * k * size k + size n` by rw[poly_oneM_steps_upper] >>
  qabbrev_tac `m = MAX 1 k` >>
  qabbrev_tac `t = m * size k * size n` >>
  `stepsOf (poly_oneM n k) <= 7 * t` suffices_by rw[Abbr`t`] >>
  `1 <= m /\ k <= m` by rw[Abbr`m`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `k <= t` by
  (`0 < size k * size n` by rw[MULT_POS] >>
  `m <= m * (size k * size n)` by rw[] >>
  `m * (size k * size n) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size k <= t` by
    (`0 < m * size n` by rw[MULT_POS] >>
  `size k <= size k * (m * size n)` by rw[] >>
  `size k * (m * size n) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size n <= t` by
      (`0 < m * size k` by rw[MULT_POS] >>
  `size n <= size n * (m * size k)` by rw[] >>
  `size n * (m * size k) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k * size k <= t` by
        (`0 < size n` by rw[] >>
  `k * size k <= m * size k` by rw[] >>
  `m * size k <= m * size k * size n` by rw[] >>
  `m * size k * size n = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Constant Polynomial                                                       *)
(* ------------------------------------------------------------------------- *)

(* Pseudocode:
   Given modulus n and constant c, make |c MOD n| to length k.
   list_const k c:
      if k = 0, return []         // [] has length 0
      t <- list_zero (k - 1)      // extend [] to length (k - 1)
      return (c MOD n)::t         // put in constant term
*)

(* Make c (MOD n, (unity k)) of length k. *)
val poly_constM_def = Define`
    poly_constM n k c =
      do
        (* k = 0 will give length = 0 *)
        k0 <- zeroM k;
        if k0 then return []
        else do
               j <- decM k;
               p <- poly_zeroM n j;
               d <- modM c n;
               consM d p; (* the c MOD n, LENGTH 1 + j = k *)
             od
      od
`;

(*
> EVAL ``poly_constM 10 7 13``; = ([3; 0; 0; 0; 0; 0; 0],Count 58): thm
> EVAL ``poly_constM 10 0 13``; = ([],Count 1): thm
> EVAL ``poly_constM 10 1 13``; = ([3],Count 20): thm
> EVAL ``unity_mod_const (ZN 10) 7 13``; = [3; 0; 0; 0; 0; 0; 0]: thm
> EVAL ``unity_mod_const (ZN 10) 0 13``; = []: thm
> EVAL ``unity_mod_const (ZN 10) 1 13``; = [3]: thm
*)


(* Theorem: 0 < n ==> (valueOf (poly_constM n k c) = unity_mod_const (ZN n) k c) *)
(* Proof:
   If k = 0
        valueOf (poly_constM n 0 c)
      = []                            by poly_constM_def
      = unity_mod_const (ZN n) 0 c    by unity_mod_const_def, k = 0
   If k <> 0,
        valueOf (poly_constM n k c)
      = (c MOD n)::valueOf (poly_zeroM n (k - 1))       by poly_constM_def
      = (c MOD n)::unity_mod_zero (ZN n) (k - 1)        by poly_zeroM_value
      = (c MOD n)::PAD_RIGHT 0 (k - 1) []               by unity_mod_zero_alt, ZN_property
      = PAD_RIGHT 0 k [c MOD n]                         by PAD_RIGHT_CONS
      = PAD_RIGHT (ZN n).sum.id k [(ZN n).sum.exp (ZN n).prod.id c]  by ZN_num_mod
      = unity_mod_const (ZN n) k c                      by unity_mod_const_def, k <> 0
*)
val poly_constM_value = store_thm(
  "poly_constM_value[simp]",
  ``!n k c. 0 < n ==> (valueOf (poly_constM n k c) = unity_mod_const (ZN n) k c)``,
  rw[poly_constM_def] >-
  rw[unity_mod_const_def] >>
  `SUC (k - 1) = k` by decide_tac >>
  `(c MOD n)::unity_mod_zero (ZN n) (k - 1) = (c MOD n)::(PAD_RIGHT 0 (k - 1) [])` by rw[unity_mod_zero_alt, ZN_property] >>
  `_ = PAD_RIGHT 0 k [c MOD n]` by rw[PAD_RIGHT_CONS] >>
  `_ = PAD_RIGHT (ZN n).sum.id k [(ZN n).sum.exp (ZN n).prod.id c]` by rw[ZN_num_mod, ZN_property] >>
  `_ = unity_mod_const (ZN n) k c` by rw[unity_mod_const_def] >>
  rw[]);


(* Theorem: valueOf (poly_constM 0 k c) = if k = 0 then [] else PAD_RIGHT 0 k [c MOD 0] *)
(* Proof:
   If k = 0,
      valueOf (poly_constM 0 k c) = []              by poly_constM_def
   If k <> 0,
      Let x = c MOD 0,
      = c MOD 0 :: valueOf (poly_zeroM n (k - 1))   by poly_constM_def
      = c MOD 0 :: unity_mod_zero (ZN n) (k - 1)    by poly_zeroM_value
      = c MOD 0 :: PAD_RIGHT 0 k []                 by unity_mod_zero_alt, ZN_property
      = PAD_RIGHT k [c MOD 0]                       by PAD_RIGHT_CONS
*)
val poly_constM_zero = store_thm(
  "poly_constM_zero",
  ``!k c. valueOf (poly_constM 0 k c) = if k = 0 then [] else PAD_RIGHT 0 k [c MOD 0]``,
  rw[poly_constM_def, unity_mod_zero_alt, ZN_property] >>
  `SUC (k - 1) = k` by decide_tac >>
  rw[PAD_RIGHT_CONS]);

(* Theorem: 0 < n ==> Weak (ZN n) (valueOf (poly_constM n k c)) *)
(* Proof:
     Weak (ZN n) (valueOf (poly_constM n k c))
   = Weak (ZN n) (unity_mod_const (ZN n) k c)     by poly_constM_value
   = T                                            by ZN_unity_mod_const_weak
*)
val poly_constM_weak = store_thm(
  "poly_constM_weak",
  ``!n k c. 0 < n ==> Weak (ZN n) (valueOf (poly_constM n k c))``,
  rw[ZN_unity_mod_const_weak]);

(* Theorem: LENGTH (valueOf (poly_constM n k c)) = k *)
(* Proof:
   If n = 0,
        LENGTH (valueOf (poly_constM 0 k c))
      = LENGTH (if k = 0 then [] else PAD_RIGHT 0 k [c MOD 0]))
                                             by poly_constM_zero
      = if k = 0 then 0 else LENGTH (PAD_RIGHT 0 k [c MOD 0])
      = if k = 0 then 0 else MAX k 1         by PAD_RIGHT_LENGTH
      = if k = 0 then 0 else k               by k <> 0, MAX_DEF
      = k
   If n <> 0,
     LENGTH (valueOf (poly_constM n k c))
   = LENGTH (unity_mod_const (ZN n) k c))    by poly_constM_value, 0 < n
   = k                                       by unity_mod_const_length
*)
val poly_constM_length = store_thm(
  "poly_constM_length[simp]",
  ``!n k c. LENGTH (valueOf (poly_constM n k c)) = k``,
  rpt strip_tac >>
  Cases_on `n = 0` >-
  rw[poly_constM_zero, PAD_RIGHT_LENGTH, MAX_DEF] >>
  rw[poly_constM_value, unity_mod_const_length]);

(* Theorem: stepsOf (poly_constM n k c) =
            if k = 0 then 1
            else 1 + SUM (MAP (\j. 1 + 2 * size j) [1 .. k]) + size c * size n *)
(* Proof:
     stepsOf (poly_constM n k c)
   = stepsOf (zeroM k) + if k = 0 then 0
     else stepsOf (decM k) +
         stepsOf (poly_zeroM n (k - 1)) +
         stepsOf (modM c n) +
         stepsOf (consM (c MOD n) (unity_mod_zero (ZN n) (k - 1)))
                                          by poly_constM_def
   = size k + if k = 0 then 0
     else size k + (1 + SUM (MAP (\j. 1 + 2 * size j) [1 .. (k - 1)])) +
          (size c * size n) + 1      by poly_zeroM_steps_eqn
   = if k = 0 then 1
     else 1 + SUM (MAP (\j. 1 + 2 * size j) [1 .. k]) + size c * size n
*)
val poly_constM_steps_eqn = store_thm(
  "poly_constM_steps_eqn",
  ``!n k c. stepsOf (poly_constM n k c) =
           if k = 0 then 1
           else 1 + SUM (MAP (\j. 1 + 2 * size j) [1 .. k]) + size c * size n``,
  rpt strip_tac >>
  (Cases_on `k = 0` >> simp[]) >-
  rw[poly_constM_def] >>
  simp[poly_constM_def, poly_zeroM_steps_eqn] >>
  qabbrev_tac `f = \j. 2 * size j + 1` >>
  `SUC (k - 1) = k` by decide_tac >>
  `SUM (MAP f [1 .. k]) = f k + SUM (MAP f [1 .. (k - 1)])` by metis_tac[listRangeINC_SUM_MAP, ADD1] >>
  `f k = 2 * size k + 1` by rw[Abbr`f`] >>
  decide_tac);

(* Theorem: stepsOf (poly_constM n k c) <= 1 + k + 2 * size k + 2 * k * size k + size c * size n *)
(* Proof:
      stepsOf (poly_constM n k c)
    = stepsOf (zeroM k) + if k = 0 then 0
      else stepsOf (decM k) +
          stepsOf (poly_zeroM n (k - 1)) +
          stepsOf (modM c n) +
          stepsOf (consM (c MOD n) (unity_mod_zero (ZN n) (k - 1)))
                                          by poly_constM_def
   <= size k + if k = 0 then 0
      else size k + (1 + (k - 1) + 2 * (k - 1) * size (k - 1)) +
           (size c * size n) + 1          by poly_zeroM_steps_upper
   = size k + size k + k + 2 * k * size k + size c * size n + 1   by size_monotone_lt
   = 1 + k + 2 * size k + 2 * k * size k + size c * size n
*)
val poly_constM_steps_upper = store_thm(
  "poly_constM_steps_upper",
  ``!n k c. stepsOf (poly_constM n k c) <= 1 + k + 2 * size k + 2 * k * size k + size c * size n``,
  rw[poly_constM_def] >>
  `stepsOf (poly_zeroM n (k - 1)) <= 1 + (k - 1) + 2 * (k - 1) * size (k - 1)` by rw[poly_zeroM_steps_upper] >>
  `1 + (k - 1) = k` by decide_tac >>
  `size (k - 1) <= size k` by rw[size_monotone_lt] >>
  `2 * (k - 1) * size (k - 1) <= 2 * k * size k` by rw[LE_MONO_MULT2] >>
  decide_tac);

(* Theorem: stepsOf (poly_constM n k c) <= 7 * (MAX 1 k) * size k * size c * size n *)
(* Proof:
      stepsOf (poly_constM n k c)
   <= 1 + k + 2 * size k + 2 * k * size k + size c * size n    by poly_constM_steps_upper
   <= (1 + 1 + 2 + 2 + 1) * k * size k * size c * size n       by dominant term
    = 7 * k * size k * size c * size n
   Use (MAX 1 k) to cater for k = 0.
*)
val poly_constM_steps_bound = store_thm(
  "poly_constM_steps_bound",
  ``!n k c. stepsOf (poly_constM n k c) <= 7 * (MAX 1 k) * size k * size c * size n``,
  rpt strip_tac >>
  `stepsOf (poly_constM n k c) <= 1 + k + 2 * size k + 2 * k * size k + size c * size n` by rw[poly_constM_steps_upper] >>
  qabbrev_tac `m = MAX 1 k` >>
  qabbrev_tac `t = m * size k * size c * size n` >>
  `stepsOf (poly_constM n k c) <= 7 * t` suffices_by rw[Abbr`t`] >>
  `1 <= m /\ k <= m` by rw[Abbr`m`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `k <= t` by
  (`0 < size k * size c * size n` by rw[MULT_POS] >>
  `m <= m * (size k * size c * size n)` by rw[] >>
  `m * (size k * size c * size n) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size k <= t` by
    (`0 < m * size c * size n` by rw[MULT_POS] >>
  `size k <= size k * (m * size c * size n)` by rw[] >>
  `size k * (m * size c * size n) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k * size k <= t` by
      (`0 < size c * size n` by rw[MULT_POS] >>
  `k * size k <= m * size k` by rw[] >>
  `m * size k <= m * size k * (size c * size n)` by rw[] >>
  `m * size k * (size c * size n) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size c * size n <= t` by
        (`0 < m * size k` by rw[MULT_POS] >>
  `size c * size n <= size c * size n * (m * size k)` by rw[] >>
  `size c * size n * (m * size k) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Powers of X                                                               *)
(* ------------------------------------------------------------------------- *)

(* Make X ** m (MOD n, (unity k)) of length k. *)
(* For X ** 1 = X, this is [0,1,0,...0] if k > 1, [1] if k = 1, [] if k = 0. *)
(* For X ** m, this is [0,0,..1,0,...0] if k > 1, the 1 at (m MOD k),
                        <----------k-->
                        <---(m MOD k)->
               [1] if k = 1, due to (m MOD 1 = 0) by MOD_1,
               [] if k = 0, to keep length = k, always for making polynomials.
*)

(* Pseudocode:
   Given modulus n, compute (X ** m) (mod n, unity k).
   list_Xexp k m:
      if k = 0, return []          // [] has length 0
      if k = 1, return [1 MOD n]   // degenerate case
      j <- m MOD k                 // prefix zeroes in the list
      i <- k - (m MOD k) - 1       // suffix zeroes in the list
      p <- list_extend [] i        // all the suffix zeroes
      q <- (1 MOD n):: p           // put in the X
      return list_extend q j       // extend with preceding zeroes
*)

val poly_X_expM_def = Define`
    poly_X_expM n k m =
       do
          k0 <- zeroM k;
          if k0 then return []
          else do
                 c <- modM 1 n; (* coefficient of X *)
                 k1 <- oneM k;
                 if k1 then consM c []
                 else do
                        j <- modM m k; (* j = m MOD k, the index of X. *)
                        h <- subM k j;
                        i <- decM h; (* number of leading zero = k - m MOD k - 1 *)
                        p <- poly_zeroM n i;
                        q <- consM c p; (* the X *)
                        poly_extendM q j; (* j = number of after zero = m MOD k *)
                      od
               od
       od
`;

(*
> EVAL ``poly_X_expM 10 7 2``; = ([0; 0; 1; 0; 0; 0; 0],Count 53): thm
> EVAL ``poly_X_expM 10 7 0``; = ([1; 0; 0; 0; 0; 0; 0],Count 56): thm
> EVAL ``poly_X_expM 10 0 0``; = ([],Count 1): thm
> EVAL ``poly_X_expM 10 1 0``; = ([1],Count 7): thm
> EVAL ``poly_X_expM 10 7 3``; = ([0; 0; 0; 1; 0; 0; 0],Count 51): thm
> EVAL ``poly_X_expM 10 7 4``; = ([0; 0; 0; 0; 1; 0; 0],Count 55): thm
> EVAL ``poly_X_expM 10 7 5``; = ([0; 0; 0; 0; 0; 1; 0],Count 57): thm
> EVAL ``poly_X_expM 10 7 6``; = ([0; 0; 0; 0; 0; 0; 1],Count 60): thm
> EVAL ``poly_X_expM 10 7 7``; = ([1; 0; 0; 0; 0; 0; 0],Count 62): thm

> EVAL ``unity_mod_special (ZN 10) 7 2 0``; = [0; 0; 1; 0; 0; 0; 0]: thm
> EVAL ``unity_mod_special (ZN 10) 7 0 0``; = [1; 0; 0; 0; 0; 0; 0]: thm
> EVAL ``unity_mod_special (ZN 10) 0 0 0``; = []: thm
> EVAL ``unity_mod_special (ZN 10) 1 0 0``; = [1]: thm
> EVAL ``unity_mod_special (ZN 10) 7 3 0``; = [0; 0; 0; 1; 0; 0; 0]: thm
> EVAL ``unity_mod_special (ZN 10) 7 4 0``; = [0; 0; 0; 0; 1; 0; 0]: thm
> EVAL ``unity_mod_special (ZN 10) 7 5 0``; = [0; 0; 0; 0; 0; 1; 0]: thm
> EVAL ``unity_mod_special (ZN 10) 7 6 0``; = [0; 0; 0; 0; 0; 0; 1]: thm
> EVAL ``unity_mod_special (ZN 10) 7 7 0``; = [1; 0; 0; 0; 0; 0; 0]: thm

> EVAL ``poly_X_expM 0 7 2``; = ([0; 0; 1 MOD 0; 0; 0; 0; 0],Count 49): thm
> EVAL ``unity_mod_special (ZN 0) 7 2 0``; = [0; 0; 1; 0; 0; 0; 0]: thm
*)

(* Theorem: 0 < n ==> (valueOf (poly_X_expM n k m) = unity_mod_X_exp (ZN n) k m) *)
(* Proof:
   If k = 0,
        valueOf (poly_X_expM n 0 m)
      = []                                 by poly_X_expM_def
      = |0|                                by poly_zero
      = unity_mod_X_exp (ZN n) 0 m         by unity_mod_X_exp_0_n
   If k = 1,
        valueOf (poly_X_expM n 1 m)
      = [1 MOD n]                          by poly_X_expM_def
      = [(ZN n).sum.exp (ZN n).prod.id 1]  by ZN_num_1
      = unity_mod_X_exp (ZN n) 1 m         by unity_mod_X_exp_1_n
   Otherwise,
      Let c = 1 MOD n, h = m MOD k,
          ls = c::unity_mod_zero (ZN n) (k - (h + 1)).
        valueOf (poly_X_expM n k m)
      = valueOf (poly_extendM ls h)        by poly_X_expM_def
      If h = 0,
         valueOf (poly_extendM ls 0)
       = unity_mod_zero (ZN n) 0 ++ ls     by poly_extendM_value
       = |0| ++ ls = ls                    by unity_mod_zero_def, unity_mod_const_def, h = 0
       = c::unity_mod_zero (ZN n) (k - 1)  by expanding ls, h = 0
       = c::PAD_RIGHT 0 (k - 1) [0]        by unity_mod_zero_def, unity_mod_const_def, ZN_property
       = c::PAD_RIGHT 0 (k - 1) []         by PAD_RIGHT_NIL_EQ
       = PAD_RIGHT 0 (SUC (k - 1)) [c]     by PAD_RIGHT_CONS
       = PAD_RIGHT 0 k [c]                 by SUC (k - 1) = k, 0 < k
       = unity_mod_special (ZN n) k m 0    by unity_mod_special_def, h = 0
       = unity_mod_X_exp (ZN n) k m        by unity_mod_X_exp_def

      If h <> 0,
         valueOf (poly_extendM ls h)
       = unity_mod_zero (ZN n) h ++ ls     by poly_extendM_value
       = PAD_RIGHT 0 h [0] ++ ls           by unity_mod_zero_def, unity_mod_const_def, ZN_property

         unity_mod_X_exp (ZN n) k m
       = unity_mod_special (ZN n) k m 0    by unity_mod_X_exp_def
       = PAD_RIGHT 0 k (0::PAD_LEFT 0 h [if n = 1 then 0 else 1])
                                           by unity_mod_special_def, ZN_property
       = PAD_RIGHT 0 k (0::PAD_LEFT 0 h [c])  by c = (if n = 1 then 0 else 1), by ONE_MOD, 0 < n.

         Note h < k                        by MOD_LESS, 0 < n
           or h + 1 <= k                   by arithmetic
         If h + 1 = k,
            ls = c::unity_mod_zero (ZN n) 0
               = c::[] = [c]               by unity_mod_zero_def, unity_mod_const_def
            This is to show:
            PAD_RIGHT 0 h [0] ++ [c] = PAD_RIGHT 0 k (0::PAD_LEFT 0 h [c])
              PAD_RIGHT 0 h [0] ++ [c]
            = [0] ++ GENLIST (K 0) (h - 1) ++ [c]   by PAD_RIGHT
            = [0] ++ PAD_LEFT 0 h [c]               by PAD_LEFT
            = 0::PAD_LEFT 0 h [c]                   by CONS_APPEND
            = PAD_RIGHT 0 k (0::PAD_LEFT 0 h [c])   by LENGTH (0::PAD_LEFT 0 h [c]) = k
        If h + 1 < k,
            Let z = k - (h + 1).
            ls = c::unity_mod_zero (ZN n) z
               = c::PAD_RIGHT 0 z [0]               by unity_mod_zero_def, unity_mod_const_def
            This is to show:
            PAD_RIGHT 0 h [0] ++ c::PAD_RIGHT 0 z [0] = PAD_RIGHT 0 k (0::PAD_LEFT 0 h [c])
              PAD_RIGHT 0 h [0] ++ c::PAD_RIGHT 0 z [0]
            = [0] ++ GENLIST (K 0) (h - 1) ++ [c] ++ 0::GENLIST (K 0) (z - 1)  by PAD_RIGHT
            = 0::PAD_LEFT (K 0) h [c] ++ 0::GENLIST (K 0) (z - 1)              by PAD_LEFT
            = 0::PAD_LEFT (K 0) h [c] ++ GENLIST (K 0) z                       by GENLIST_K_CONS
            = PAD_RIGHT 0 (z + (h + 1)) (0::PAD_LEFT 0 h [c])  by PAD_RIGHT, LENGTH (0::PAD_LEFT 0 h [c]) = h + 1
            = PAD_RIGHT 0 k (0::PAD_LEFT 0 h [c])              by k = z + (h + 1)
*)
val poly_X_expM_value = store_thm(
  "poly_X_expM_value[simp]",
  ``!n k m. 0 < n ==> (valueOf (poly_X_expM n k m) = unity_mod_X_exp (ZN n) k m)``,
  rw[poly_X_expM_def] >-
  rw[unity_mod_X_exp_0_n] >>
  (Cases_on `k = 1` >> simp[]) >-
  rw[unity_mod_X_exp_1_n, ZN_num_1] >>
  qabbrev_tac `c = 1 MOD n` >>
  qabbrev_tac `h = m MOD k` >>
  qabbrev_tac `ls = c::unity_mod_zero (ZN n) (k - (h + 1))` >>
  (Cases_on `h = 0` >> simp[]) >| [
    `valueOf (poly_extendM ls 0) = unity_mod_zero (ZN n) 0 ++ ls` by rw[poly_extendM_value] >>
    `_ = ls` by rw[unity_mod_zero_def, unity_mod_const_def] >>
    `unity_mod_X_exp (ZN n) k m = unity_mod_special (ZN n) k m 0` by rw[unity_mod_X_exp_def] >>
    `_ = PAD_RIGHT 0 k [(if n = 1 then 0 else 1) MOD n]` by rw[unity_mod_special_def, ZN_property] >>
    `(if n = 1 then 0 else 1) MOD n = c` by rw[Abbr`c`] >>
    rfs[unity_mod_zero_def, unity_mod_const_def, ZN_property, Abbr`ls`] >>
    `SUC (k - 1) = k` by decide_tac >>
    `1 <= k - 1` by decide_tac >>
    `c::PAD_RIGHT 0 (k - 1) [0] = c::PAD_RIGHT 0 (k - 1) []` by rw[PAD_RIGHT_NIL_EQ] >>
    `_ = PAD_RIGHT 0 k [c]` by rw[PAD_RIGHT_CONS] >>
    rw[],
    `valueOf (poly_extendM ls h) = unity_mod_zero (ZN n) h ++ ls` by rw[poly_extendM_value] >>
    `_ = PAD_RIGHT 0 h [0] ++ ls` by rw[unity_mod_zero_def, unity_mod_const_def, ZN_property] >>
    `unity_mod_X_exp (ZN n) k m = unity_mod_special (ZN n) k m 0` by rw[unity_mod_X_exp_def] >>
    `_ = PAD_RIGHT 0 k (0::PAD_LEFT 0 h [if n = 1 then 0 else 1])` by rw[unity_mod_special_def, ZN_property] >>
    `(if n = 1 then 0 else 1) = c` by rw[Abbr`c`] >>
    rfs[unity_mod_zero_def, unity_mod_const_def, ZN_property, Abbr`ls`] >>
    `h < k` by rw[Abbr`h`] >>
    `h + 1 <= k` by decide_tac >>
    (Cases_on `k <= h + 1` >> simp[]) >| [
      `k = h + 1` by decide_tac >>
      rw[PAD_LEFT, PAD_RIGHT, ADD1],
      rw[PAD_LEFT, PAD_RIGHT] >>
      `SUC (k - (h + 2)) = k - SUC h` by decide_tac >>
      metis_tac[GENLIST_K_CONS]
    ]
  ]);


(* Theorem: valueOf (poly_X_expM 0 k m) =
            if k = 0 then [] else PAD_RIGHT 0 k (PAD_LEFT 0 ((m MOD k) + 1) [1 MOD 0]) *)
(* Proof:
   Let x = 1 MOD n.
   If k = 0,
        valueOf (poly_X_expM 0 0 m)
      = []                                 by poly_X_expM_def
   If k = 1,
      Then m MOD 1 = 0                     by MOD_1
        valueOf (poly_X_expM 0 1 m)
      = [x]                                by poly_X_expM_def
      = PAD_RIGHT 0 1 [x]                  by PAD_RIGHT
      = PAD_RIGHT 0 1 (PAD_LEFT 0 1 [x])   by PAD_LEFT
   Otherwise,
      Let ls = unity_mod_zero (ZN 0) (k - (m MOD k + 1)).
         valueOf (poly_X_expM 0 k m)
       = valueOf (poly_extendM (x::ls) (m MOD k))       by poly_X_expM_def, poly_zeroM_value
       = unity_mod_zero (ZN n) (m MOD k) ++ (x :: ls)   by poly_extendM_value
       = unity_mod_zero (ZN n) (m MOD k) ++ [x] ++ ls   by CONS_APPEND
       = PAD_RIGHT 0 (m MOD k) [] ++ [x] ++ ls          by unity_mod_zero_alt, ZN_property
       = PAD_LEFT 0 (m MOD k + 1) [x] ++ ls             by PAD_LEFT_BY_RIGHT
       = lt ++ unity_mod_zero (ZN 0) (k - (m MOD k + 1)) where lt = PAD_LEFT 0 (m MOD k + 1) [x]
       = lt ++ PAD_RIGHT 0 (k - (m MOD k + 1)) []       by unity_mod_zero_alt, ZN_property
       = PAD_RIGHT 0 k lt                               by PAD_RIGHT_BY_RIGHT, LENGTH lt = (m MOD k) + 1
       = PAD_RIGHT 0 k (PAD_LEFT 0 ((m MOD k) + 1) [1 MOD 0])
*)
Theorem poly_X_expM_zero:
  !k m. valueOf (poly_X_expM 0 k m) =
         if k = 0 then [] else PAD_RIGHT 0 k (PAD_LEFT 0 ((m MOD k) + 1) [1 MOD 0])
Proof
  rpt strip_tac >>
  Cases_on `k <= 1` >| [
    `k = 0 \/ k = 1` by decide_tac >-
    rw[poly_X_expM_def] >>
    rw[poly_X_expM_def, PAD_LEFT, PAD_RIGHT],
    rw[] >>
    qabbrev_tac `x = 1 MOD 0` >>
    qabbrev_tac `ls = unity_mod_zero (ZN 0) (k - (m MOD k + 1))` >>
    qabbrev_tac `lt = PAD_LEFT 0 (m MOD k + 1) [x]` >>
    `LENGTH lt = m MOD k + 1` by rw[PAD_LEFT_LENGTH, MAX_DEF, Abbr`lt`] >>
    `valueOf (poly_X_expM 0 k m) = valueOf (poly_extendM (x::ls) (m MOD k))` by rw[poly_X_expM_def, poly_zeroM_value, Abbr`ls`] >>
    `_ = unity_mod_zero (ZN n) (m MOD k) ++ (x :: ls)` by rw[poly_extendM_value] >>
    `_ = PAD_RIGHT 0 (m MOD k) [] ++ [x] ++ ls` by rw[unity_mod_zero_alt, ZN_property] >>
    `_ = lt ++ ls` by rw[PAD_LEFT_BY_RIGHT, Abbr`lt`] >>
    `_ = lt ++ PAD_RIGHT 0 (k - (m MOD k + 1)) []` by rw[unity_mod_zero_alt, ZN_property, Abbr`ls`] >>
    `_ = PAD_RIGHT 0 k lt`  by metis_tac[PAD_RIGHT_BY_RIGHT] >>
    fs[Abbr`lt`]
  ]
QED

(* Theorem: 0 < n ==> Weak (ZN n) (valueOf (poly_X_expM n k m)) *)
(* Proof:
     Weak (ZN n) (valueOf (poly_X_expM n k m))
   = Weak (ZN n) (unity_mod_X_exp (ZN n) k m)     by poly_X_expM_value
   = Weak (ZN n) (unity_mod_special (ZN n) k m 0) by unity_mod_X_exp_def
   = T                                            by ZN_unity_mod_special_weak
*)
val poly_X_expM_weak = store_thm(
  "poly_X_expM_weak",
  ``!n k m. 0 < n ==> Weak (ZN n) (valueOf (poly_X_expM n k m))``,
  rw[unity_mod_X_exp_def, ZN_unity_mod_special_weak]);

(* Theorem: LENGTH (valueOf (poly_X_expM n k m)) = k *)
(* Proof:
   If n = 0,
        LENGTH (valueOf (poly_X_expM n k m))
      = LENGTH (if k = 0 then [] else PAD_RIGHT 0 k (PAD_LEFT 0 ((m MOD k) + 1) [1 MOD 0]))
                                                         by poly_X_expM_zero
      = if k = 0 then 0 else LENGTH (PAD_RIGHT 0 k ls)  where ls = PAD_LEFT 0 ((m MOD k) + 1) [1 MOD 0]
      = if k = 0 then 0 else MAX k (LENGTH ls)           by PAD_RIGHT_LENGTH
      = if k = 0 then 0 else MAX k (MAX (m MOD k + 1) 1) by PAD_LEFT_LENGTH
      = if k = 0 then 0 else MAX (MAX k (m MOD k)) 1     by MAX_ASSOC
      = if k = 0 then 0 else MAX k 1                     by MOD_LESS, k <> 0
      = if k = 0 then 0 else k                           by MAX_DEF, 1 <= k
      = k
   If n <> 0,
        LENGTH (valueOf (poly_X_expM n k m))
      = LENGTH (unity_mod_X_exp (ZN n) k m)              by poly_X_expM_value, 0 < n
      = k                                                by unity_mod_X_exp_length
*)
val poly_X_expM_length = store_thm(
  "poly_X_expM_length[simp]",
  ``!n k m. LENGTH (valueOf (poly_X_expM n k m)) = k``,
  rpt strip_tac >>
  Cases_on `n = 0` >| [
    rw[poly_X_expM_zero, PAD_RIGHT_LENGTH, PAD_LEFT_LENGTH] >>
    rw[MAX_ASSOC, MAX_DEF] >>
    `m MOD k < k` by rw[MOD_LESS] >>
    decide_tac,
    rw[poly_X_expM_value, unity_mod_X_exp_length]
  ]);

(* Theorem: stepsOf (poly_X_expM n k m) =
      if k = 0 then 1
      else size n + 2 * size k + if k = 1 then 1
      else (if k = 0 then 0 else size m * size k) + 1 + size (MAX k (m MOD k)) + size (k - (m MOD k)) +
            stepsOf (poly_zeroM n (k - (m MOD k) - 1)) +
            stepsOf (poly_extendM ((1 MOD n)::unity_mod_zero (ZN n) (k - (m MOD k) - 1)) (m MOD k)) *)
(* Proof:
     stepsOf (poly_X_expM n k m)
   = stepsOf (zeroM k) + if k = 0 then 0
     else stepsOf (modM 1 n) +
          stepsOf (oneM k) + if k = 1 then 1
      else stepsOf (modM m k) + stepsOf (subM k (m MOD k)) + stepsOf (decM (k - (m MOD k))) +
           stepsOf (poly_zeroM n (k - (m MOD k) - 1)) + stepsOf (consM (1 MOD n) p) +
           stepsOf (poly_extendM q (m MOD k))        by poly_X_expM_def
   = size k + if k = 0 then 0
     else (size 1 * size n) + size k + if k = 1 then 1
     else (if k = 0 then 0 else size m * size k) +
          size (MAX k (m MOD k)) + size (k - (m MOD k)) +
           stepsOf (poly_zeroM n (k - (m MOD k) - 1)) + 1 + stepsOf (poly_extendM q (m MOD k))
   = size k + if k = 0 then 0
     else size n + size k + if k = 1 then 1
     else (if k = 0 then 0 else size m * size k) + 1 +
          size (MAX k (m MOD k)) + size (k - (m MOD k)) +
           stepsOf (poly_zeroM n (k - (m MOD k) - 1)) + stepsOf (poly_extendM q (m MOD k))
   = if k = 0 then 1
     else size n + 2 * size k + if k = 1 then 1
     else (if k = 0 then 0 else size m * size k) + 1 + size (MAX k (m MOD k)) + size (k - (m MOD k)) +
           stepsOf (poly_zeroM n (k - (m MOD k) - 1)) + stepsOf (poly_extendM q (m MOD k))
*)
val poly_X_expM_steps_eqn = store_thm(
  "poly_X_expM_steps_eqn",
  ``!n k m. stepsOf (poly_X_expM n k m) =
           if k = 0 then 1
           else size n + 2 * size k + if k = 1 then 1
           else (if k = 0 then 0 else size m * size k) + 1 + size (MAX k (m MOD k)) + size (k - (m MOD k)) +
                 stepsOf (poly_zeroM n (k - (m MOD k) - 1)) +
                 stepsOf (poly_extendM ((1 MOD n)::unity_mod_zero (ZN n) (k - (m MOD k) - 1)) (m MOD k))``,
  rw[poly_X_expM_def, size_max]);

(* Theorem: stepsOf (poly_X_expM n k m) <=
           3 + 2 * k + size n + 4 * size k + size m * size k + 4 * k * size k *)
(* Proof:
      stepsOf (poly_X_expM n k m)
    = if k = 0 then 1
      else size n + 2 * size k + if k = 1 then 1
      else (if k = 0 then 0 else size m * size k) + 1 + size (MAX k (m MOD k)) + size (k - (m MOD k)) +
            stepsOf (poly_zeroM n (k - (m MOD k) - 1)) +
            stepsOf (poly_extendM ((1 MOD n)::unity_mod_zero (ZN n) (k - (m MOD k) - 1)) (m MOD k))
                                             by poly_X_expM_steps_eqn
   <= size 1 * size n + 2 * size k +
      size m * size k + 1 + size (MAX k (m MOD k)) + size (k - (m MOD k)) +
      (1 + p + 2 * p * size p) +     by poly_zeroM_steps_upper, p = k - (m MOD k) - 1
      (1 + q + 2 * q * size q)       by poly_extendM_steps_upper, q = m MOD k
      Note m MOD k <= k              by MOD_LESS_EQ, 0 < k
      Thus size (MAX k (m MOD k)) = size k    by MAX_DEF
       and size (k - (m MOD k)) <= size k     by size_monotone_le
      Also p < k, so size p <= size k         by size_monotone_lt
       and q <= k, so size q <= size k        by size_monotone_le

      stepsOf (poly_X_expM n k m)
   <= size n + 2 * size k +
      size m * size k + 1 + size k + size k + 2 * (1 + k + 2 * k * size k)
    = 3 + size n + 4 * size k + 2 * k + size m * size k + 4 * k * size k
    = 3 + 2 * k + size n + 4 * size k + size m * size k + 4 * k * size k
*)
val poly_X_expM_steps_upper = store_thm(
  "poly_X_expM_steps_upper",
  ``!n k m. stepsOf (poly_X_expM n k m) <=
           3 + 2 * k + size n + 4 * size k + size m * size k + 4 * k * size k``,
  rpt strip_tac >>
  assume_tac poly_X_expM_steps_eqn >>
  last_x_assum (qspecl_then [`n`, `k`, `m`] strip_assume_tac) >>
  qabbrev_tac `h = m MOD k` >>
  qabbrev_tac `ls = 1 MOD n::unity_mod_zero (ZN n) (k - h - 1)` >>
  qabbrev_tac `j = k - h - 1` >>
  qabbrev_tac `t = size n` >>
  Cases_on `k = 0` >-
  rw[] >>
  Cases_on `k = 1` >-
  rw[] >>
  `h < k` by rw[Abbr`h`] >>
  `size (MAX k h) = size k` by rw[MAX_DEF] >>
  `stepsOf (poly_X_expM n k m) = 1 + t + 3 * (size k) + (size m * size k) +
    size (k - h) + stepsOf (poly_zeroM n j) + stepsOf (poly_extendM ls h)` by fs[] >>
  `size (k - h) <= size k` by rw[size_monotone_le] >>
  `stepsOf (poly_zeroM n j) <= 1 + k + 2 * k * size k` by
  (`stepsOf (poly_zeroM n j) <= 1 + j + 2 * j * size j` by rw[poly_zeroM_steps_upper] >>
  `j < k` by rw[Abbr`j`] >>
  `size j <= size k` by rw[size_monotone_lt] >>
  `j * size j <= k * size k` by rw[LE_MONO_MULT2] >>
  decide_tac) >>
  `stepsOf (poly_extendM ls h) <= 1 + k + 2 * k * size k` by
    (`stepsOf (poly_extendM ls h) <= 1 + h + 2 * h * size h` by rw[poly_extendM_steps_upper] >>
  `size h <= size k` by rw[size_monotone_lt] >>
  `h * size h <= k * size k` by rw[LE_MONO_MULT2] >>
  decide_tac) >>
  decide_tac);

(* Theorem: stepsOf (poly_X_expM n k m) <= 15 * (MAX 1 k) * size k * size n * size m *)
(* Proof:
      stepsOf (poly_X_expM n k m)
   <= 3 + 2 * k + size n + 4 * size k + size m * size k + 4 * k * size k  by poly_X_expM_steps_upper
   <= (3 + 2 + 1 + 4 + 1 + 4) * k * size k * size n * size m              by dominant term
    = 15 * k * size k * size n * size m
   Use (MAX 1 k) to cater for k = 0.
*)
val poly_X_expM_steps_bound = store_thm(
  "poly_X_expM_steps_bound",
  ``!n k m. stepsOf (poly_X_expM n k m) <= 15 * (MAX 1 k) * size k * size n * size m``,
  rpt strip_tac >>
  `stepsOf (poly_X_expM n k m) <= 3 + 2 * k + size n + 4 * size k + size m * size k + 4 * k * size k` by rw[poly_X_expM_steps_upper] >>
  qabbrev_tac `h = MAX 1 k` >>
  qabbrev_tac `t = h * size k * size n * size m` >>
  `stepsOf (poly_X_expM n k m) <= 15 * t` suffices_by rw[Abbr`t`] >>
  `1 <= h /\ k <= h` by rw[Abbr`h`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `k <= t` by
  (`h <= h * (size k * size n * size m)` by rw[MULT_POS] >>
  `h * (size k * size n * size m) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size n <= t` by
    (`size n <= size n * (h * size k * size m)` by rw[MULT_POS] >>
  `size n * (h * size k * size m) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size k <= t` by
      (`size k <= size k * (h * size n * size m)` by rw[MULT_POS] >>
  `size k * (h * size n * size m) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size m * size k <= t` by
        (`size m * size k <= size m * size k * (h * size n)` by rw[MULT_POS] >>
  `size m * size k * (h * size n) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k * size k <= t` by
          (`k * size k <= h * size k` by rw[] >>
  `h * size k <= h * size k * (size m * size n)` by rw[MULT_POS] >>
  `h * size k * (size m * size n) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);


(* ------------------------------------------------------------------------- *)
(* Polynomial operations                                                     *)
(* ------------------------------------------------------------------------- *)

(* Equality of polynomial p q, both of length k *)
(* > EQ_LIST;
val it = |- !h1 h2. h1 = h2 ==> !l1 l2. l1 = l2 ==> h1::l1 = h2::l2: thm
*)

(* Pseudocode:
   Given polynomials p and q, test if (p = q).
   list_eq p q:
      if p = [], return (q = [])        // equal if [] = []
      if q = [], return (p = [])        // equal if [] = []
      return (head p) = (head q) /\     // heads must equal
             list_eq (tail p) (tail q)  // recursive call with tails: tails equal
*)

Definition poly_eqM_def:
  poly_eqM p q =
      do
        p0 <- nullM p;
        q0 <- nullM q;
        if p0 then return q0
        else if q0 then return p0
        else do
               h1 <- headM p;
               t1 <- tailM p;
               h2 <- headM q;
               t2 <- tailM q;
               e0 <- eqM h1 h2;
               if e0 then poly_eqM t1 t2
               else return F
             od
      od
Termination
  WF_REL_TAC `measure (λ(p,q). LENGTH q)` >> simp[LENGTH_TL_LT]
End

(*
EVAL ``poly_eqM [1;1;0;1;0;0;1] [1;1;0;1;0;0;1]``; = (T,Count 51): thm
EVAL ``poly_eqM [1;1;0;1;0;0;1] [1;1;0;0;1;0;1]``; = (F,Count 28): thm
*)


(* Theorem: valueOf (poly_eqM p q) = (p = q) *)
(* Proof:
   By induction from poly_eqM_def.
     valueOf (poly_eqM p q)
   = if (p = []) then (q = [])
     else if (q = []) then (p = [])
     else if (HD p = HD q) then valueOf (poly_eqM (TL p) (TL q)) else F
                                                 by poly_eqM_def
   = if (p = []) then (q = [])
     else if (q = []) then (p = [])
     else (HD p = HD q) /\ (TL p = TL q)         by induction hypothesis
   = (p = q)                                     by LIST_EQ_HEAD_TAIL
*)
Theorem poly_eqM_value[simp]:
  !p q. valueOf (poly_eqM p q) = (p = q)
Proof
  ho_match_mp_tac (theorem "poly_eqM_ind") >>
  rw[] >>
  rw[Once poly_eqM_def] >> rw[LIST_EQ_HEAD_TAIL]
QED

(* Theorem: stepsOf (poly_eqM p q) =
            2 + if ((p = []) \/ (q = [])) then 0
                else 4 + size (MAX (HD p) (HD q)) +
                     if (HD p <> HD q) then 0 else stepsOf (poly_eqM (TL p) (TL q)) *)
(* Proof:
     stepsOf (poly_eqM p q)
   = stepsOf (nullM p) + stepsOf (nullM q) +
     if (p = []) then 0 else if (q = []) then 0
     else stepsOf (headM p) + stepsOf (tailM p) +
          stepsOf (headM q) + stepsOf (tailM q) +
          stepsOf (eqM (HD p) (HD q)) +
          if (HD p = HD q) then stepsOf (poly_eqM (TL p) (TL q)) else 0    by poly_eqM_def
   = 1 + 1 + if ((p = []) \/ (q = [])) then 0
     else 1 + 1 + 1 + 1 + size (MAX (HD p) (HD q)) +
     if (HD p <> HD q) then 0 else stepsOf (poly_eqM (TL p) (TL q))        by size_max
   = 2 + if ((p = []) \/ (q = [])) then 0
     else 4 + size (MAX (HD p) (HD q)) + if (HD p <> HD q) then 0 else stepsOf (poly_eqM (TL p) (TL q))
*)
val poly_eqM_steps_thm = store_thm(
  "poly_eqM_steps_thm",
  ``!p q. stepsOf (poly_eqM p q) =
          2 + if ((p = []) \/ (q = [])) then 0
              else 4 + size (MAX (HD p) (HD q)) +
                   if (HD p <> HD q) then 0 else stepsOf (poly_eqM (TL p) (TL q))``,
  ho_match_mp_tac (theorem "poly_eqM_ind") >>
  (rw[] >> rw[Once poly_eqM_def, size_max]) >-
  rw[Once poly_eqM_def] >>
  rw[Once poly_eqM_def]);

(* Theorem: stepsOf (poly_eqM p q) =
         if ((p = []) \/ (q = [])) then 2
         else 6 + size (MAX (HD p) (HD q)) +
              if (HD p <> HD q) then 0 else stepsOf (poly_eqM (TL p) (TL q)) *)
(* Proof:
     stepsOf (poly_eqM p q)
   = 2 + if ((p = []) \/ (q = [])) then 0
     else 4 + size (MAX (HD p) (HD q)) +
          if (HD p <> HD q) then 0 else stepsOf (poly_eqM (TL p) (TL q))  by poly_eqM_steps_thm
   = if ((p = []) \/ (q = [])) then 2
     else 6 + size (MAX (HD p) (HD q)) +
          if (HD p <> HD q) then 0 else stepsOf (poly_eqM (TL p) (TL q))
*)
val poly_eqM_steps_by_list_loop = store_thm(
  "poly_eqM_steps_by_list_loop",
  ``!p q. stepsOf (poly_eqM p q) =
         if ((p = []) \/ (q = [])) then 2
         else 6 + size (MAX (HD p) (HD q)) +
              if (HD p <> HD q) then 0 else stepsOf (poly_eqM (TL p) (TL q))``,
  rw[Once poly_eqM_steps_thm]);


(*
This puts poly_eqM_steps in the category: list loop with body on head and tail transform with exit.
   mexpM_steps_by_sqmod_div_loop:
        !p q. loop p q = if (p = []) \/ (q = []) then 2 else body p q +
              if exit p q then 0 else loop (TL p) (TL q)
suitable for: loop2_list_tail_head_count_exit_sum_le
and also for: loop2_list_tail_head_upper_count_exit_le
*)

(* Theorem: (LENGTH p = k) /\ (LENGTH q = k) ==>
            stepsOf (poly_eqM p q) <= 2 + SUM (GENLIST (\j. 6 + size (MAX (EL j p) (EL j q))) k) *)
(* Proof:
   Let quit = (\p q. 2),
       f = (\x y. 6 + size (MAX x y)),
       body = (\p q. f (HD p) (HD q)),
       exit = (\p q. HD p <> HD q),
       loop = (\p q. stepsOf (poly_eqM p q)).
   Then !p q. loop p q = if (p = []) \/ (q = []) then quit p q else body p q +
              if exit p q then 0 else loop (TL p) (TL q)   by poly_eqM_steps_by_list_loop
   Given (LENGTH p = k) and LENGTH q = k,
   Thus loop p q
     <= quit [] [] +
        SUM (GENLIST (\j. f (EL j p) (EL j q)) k)          by loop2_list_tail_head_count_exit_sum_le
      = 2 + SUM (GENLIST (\j. f (EL j p) (EL j q)) k)
*)
val poly_eqM_steps_by_sum_le = store_thm(
  "poly_eqM_steps_by_sum_le",
  ``!p q k. (LENGTH p = k) /\ (LENGTH q = k) ==>
           stepsOf (poly_eqM p q) <= 2 + SUM (GENLIST (\j. 6 + size (MAX (EL j p) (EL j q))) k)``,
  rpt strip_tac >>
  qabbrev_tac `quit = \p:num list q:num list. 2` >>
  qabbrev_tac `f = \x y. 6 + size (MAX x y)` >>
  qabbrev_tac `body = \p q. f (HD p) (HD q)` >>
  qabbrev_tac `exit = \p q:num list. HD p <> HD q` >>
  qabbrev_tac `loop = \p q. stepsOf (poly_eqM p q)` >>
  `loop p q <= 2 + SUM (GENLIST (\j. f (EL j p) (EL j q)) k)` suffices_by rw[Abbr`loop`] >>
  `!p q. loop p q = if (p = []) \/ (q = []) then quit p q else body p q + if exit p q then 0 else loop (TL p) (TL q)` by metis_tac[poly_eqM_steps_by_list_loop] >>
  `body = (\p q. f (HD p) (HD q))` by metis_tac[] >>
  imp_res_tac loop2_list_tail_head_count_exit_sum_le >>
  metis_tac[]);

(* Theorem: Weak (ZN n) p /\ Weak (ZN n) q /\ (LENGTH p = k) /\ (LENGTH q = k) ==>
            stepsOf (poly_eqM p q) <= 2 + 6 * k + k * size n *)
(* Proof:
   Let quit = (\p q. 2),
       f = (\x y. 6 + size (MAX x y)),
       body = (\p q. f (HD p) (HD q)),
       exit = (\p q. HD p <> HD q),
       loop = (\p q. stepsOf (poly_eqM p q)).
   Then !p q. loop p q = if (p = []) \/ (q = []) then quit p q else body p q +
              if exit p q then 0 else loop (TL p) (TL q)   by poly_eqM_steps_by_list_loop
   Given (LENGTH p = k) and LENGTH q = k,
     and EVERY (\j. j <= n) p         by ZN_weak
     and EVERY (\j. j <= n) q         by ZN_weak
     and MONO2 f                      by MAX_DEF, size_monotone_le
   Thus loop p q
     <= quit [][] + k * f n n         by loop2_list_tail_head_upper_count_exit_le
      = 2 + k * (6 + size (MAX n n))  by notation
      = 2 + k * (6 + size n)          by MAX_IDEM
      = 2 + 6 * k + k * size n
*)
val poly_eqM_steps_upper = store_thm(
  "poly_eqM_steps_upper",
  ``!p q k n. Weak (ZN n) p /\ Weak (ZN n) q /\ (LENGTH p = k) /\ (LENGTH q = k) ==>
             stepsOf (poly_eqM p q) <= 2 + 6 * k + k * size n``,
  rpt strip_tac >>
  qabbrev_tac `quit = \p:num list q:num list. 2` >>
  qabbrev_tac `f = \x y. 6 + size (MAX x y)` >>
  qabbrev_tac `body = \p q. f (HD p) (HD q)` >>
  qabbrev_tac `exit = \p q:num list. HD p <> HD q` >>
  qabbrev_tac `loop = \p q. stepsOf (poly_eqM p q)` >>
  `loop p q <= 2 + 6 * k + k * size n` suffices_by rw[Abbr`loop`] >>
  `!p q. loop p q = if (p = []) \/ (q = []) then quit p q else body p q + if exit p q then 0 else loop (TL p) (TL q)` by metis_tac[poly_eqM_steps_by_list_loop] >>
  `MONO2 f` by
  (rw[Abbr`f`] >>
  `MAX x1 y1 <= MAX x2 y2` by rw[] >>
  rw[size_monotone_le]) >>
  `body = (\p q. f (HD p) (HD q))` by metis_tac[] >>
  assume_tac (loop2_list_tail_head_upper_count_exit_le |> ISPEC ``loop: num list -> num list -> num``) >>
  first_x_assum (qspecl_then [`body`, `quit`, `exit`, `f`] strip_assume_tac) >>
  qabbrev_tac `foo = !p q. loop p q = if (p = []) \/ (q = []) then quit p q
                else body p q + if exit p q then 0 else loop (TL p) (TL q)` >>
  `!x y k n. (LENGTH x = k) /\ (LENGTH y = k) /\ EVERY (\j. j < n) x /\ EVERY (\j. j < n) y ==>
              loop x y <= quit [] [] + k * f n n` by metis_tac[] >>
  first_x_assum (qspecl_then [`p`, `q`, `k`, `n`] strip_assume_tac) >>
  `loop p q <= 2 + k * f n n` by metis_tac[ZN_weak] >>
  `k * f n n = k * (6 + size n)` by rw[Abbr`f`] >>
  `_ = k * 6 + k * size n` by rw[] >>
  decide_tac);

(* This is the result I like! *)

(* Theorem: Weak (ZN n) p /\ Weak (ZN n) q /\ (LENGTH p = k) /\ (LENGTH q = k) ==>
            stepsOf (poly_eqM p q) <= 9 * (MAX 1 k) * size n *)
(* Proof:
      stepsOf (poly_eqM p q)
   <= 2 + 6 * k + k * size n        by poly_eqM_steps_upper
   <= (2 + 6 + 1) * k * size n      by dominant term
    = 9 * k * size n
   Use (MAX 1 k) to cater for k = 0.
*)
val poly_eqM_steps_bound = store_thm(
  "poly_eqM_steps_bound",
  ``!p q k n. Weak (ZN n) p /\ Weak (ZN n) q /\ (LENGTH p = k) /\ (LENGTH q = k) ==>
             stepsOf (poly_eqM p q) <= 9 * (MAX 1 k) * size n``,
  rpt strip_tac >>
  `stepsOf (poly_eqM p q) <= 2 + 6 * k + k * size n` by rw[poly_eqM_steps_upper] >>
  qabbrev_tac `m = MAX 1 k` >>
  qabbrev_tac `t = m * size n` >>
  `stepsOf (poly_eqM p q) <= 9 * t` suffices_by rw[Abbr`t`] >>
  `1 <= m /\ k <= m` by rw[Abbr`m`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `k <= t` by
  (`m <= m * size n` by rw[MULT_POS] >>
  `m * size n = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k * size n <= t` by
    (`k * size n <= m * size n` by rw[] >>
  `m * size n = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Polynomial multiplication by a scalar                                     *)
(* ------------------------------------------------------------------------- *)

(* Multiply polynomial p of length k by a scalar c in (MOD n, (unity k)) *)
(* > weak_cmult_def;
|- (!r c. c o [] = []) /\ !r c h t. c o (h::t) = c * h::c o t
*)

(* Pseudocode:
   Given modulus n, a scalar c and polynomial p, compute (c o p) (mod n).
   list_cmult c p:
      if p = [], return []         // c o [] = []
      h <- c * (head p) MOD n      // c multiply with head
      t <- list_cmult c (tail p)   // recursive call with tail: c o (tail p)
      return h::t                  // combine to give result
*)

Definition poly_cmultM_def:
    poly_cmultM n c p =
      do
        p0 <- nullM p;
        if p0 then return []
        else do
               h <- headM p;
               t <- tailM p;
               k <- mmulM n c h;
               q <- poly_cmultM n c t;
               consM k q;
             od
      od
Termination WF_REL_TAC `measure (λ(n,c,p). LENGTH p)` >> simp[LENGTH_TL_LT]
End

(*
> EVAL ``poly_cmultM 10 3 [1;4;5;2;1;1;3]``; = ([3; 2; 5; 6; 3; 3; 9],Count 139): thm
> EVAL ``poly_cmultM 0 3 [1;4;5;2;1;1;3]``; =
      ([3 MOD 0; 12 MOD 0; 15 MOD 0; 6 MOD 0; 3 MOD 0; 3 MOD 0; 9 MOD 0], Count 55): thm
> EVAL ``poly_cmultM 0 (3 MOD 0) [1;4;5;2;1;1;3]``; -- run away!
*)

(* Theorem: valueOf (poly_cmultM n c p) = weak_cmult (ZN n) c p *)
(* Proof:
   By induction from poly_cmultM_def.
   If p = [],
        valueOf (poly_cmultM n c p)
      = []                            by poly_cmultM_def
      = weak_cmult (ZN n) c []        by weak_cmult_of_zero
   If p = h::t,
        valueOf (poly_cmultM n c p)
      = (c * h) MOD n :: valueOf (poly_cmultM n c t)    by poly_cmultM_def
      = (c * h) MOD n :: weak_cmult (ZN n) c t          by induction hypothesis
      = weak_cmult (ZN n) c p                           by weak_cmult_cons
*)
val poly_cmultM_value = store_thm(
  "poly_cmultM_value[simp]",
  ``!n c p. valueOf (poly_cmultM n c p) = weak_cmult (ZN n) c p``,
  ho_match_mp_tac (theorem "poly_cmultM_ind") >>
  rw[] >>
  rw[Once poly_cmultM_def] >>
  (Cases_on `p` >> fs[ZN_property]));

(* Theorem: Weak (ZN n) p ==> (valueOf (poly_cmultM n c p) = c oz p) *)
(* Proof: by poly_cmultM_value, ZN_poly_cmult_alt *)
val poly_cmultM_value_alt = store_thm(
  "poly_cmultM_value_alt",
  ``!n c p. Weak (ZN n) p ==> (valueOf (poly_cmultM n c p) = c oz p)``,
  rw[ZN_poly_cmult_alt]);

(*
weak_cmult_element |> ISPEC ``(ZN n)`` |> SIMP_RULE bool_ss [ZN_property];
|- !c p j. j < LENGTH p ==> EL j (weak_cmult (ZN n) c p) = (c * EL j p) MOD n
*)

(* Theorem: j < LENGTH p ==> (EL j (valueOf (poly_cmultM n c p)) = (c * EL j p) MOD n) *)
(* Proof:
     EL j (valueOf (poly_cmultM n c p))
   = EL j (weak_cmult (ZN n) c p)    by poly_cmultM_value
   = (c * EL j p) MD n               by weak_cmult_element
*)
val poly_cmultM_element = store_thm(
  "poly_cmultM_element",
  ``!n c p j. j < LENGTH p ==> (EL j (valueOf (poly_cmultM n c p)) = (c * EL j p) MOD n)``,
  rw[weak_cmult_element, ZN_property]);

(* Note: weak_cmult_weak |- !r. Ring r ==> !p. weak p ==> !c. c IN R ==> weak (c o p)
   requires c IN R. Here we just need c:num, not c < n for c IN (ZN n).carrier.
   Thus the following proof, using weak_cmult_element, is better, special for (ZN n).
*)
(* Theorem: 0 < n ==> Weak (ZN n) (valueOf (poly_cmultM n c p)) *)
(* Proof:
       Weak (ZN n) (valueOf (poly_cmultM n c p))
   <=> Weak (ZN n) (weak_cmult (ZN n) c p)          by poly_cmultM_value
   <=> EVERY (\c. c < n) (weak_cmult (ZN n) c p)    by ZN_weak
   <=> !j. j < LENGTH ls ==> (EL j ls) < n          by EVERY_EL, ls = weak_cmult (ZN n) c p
   <=> !j. j < LENGTH p ==> (c * EL j p) MOD n < n  by weak_cmult_length, weak_cmult_element
   <=> !j. j < LENGTH p ==> T                       by MOD_LESS, 0 < n
   <=> T
*)
val poly_cmultM_weak = store_thm(
  "poly_cmultM_weak",
  ``!n c p. 0 < n ==> Weak (ZN n) (valueOf (poly_cmultM n c p))``,
  rw[ZN_weak] >>
  irule (EVERY_EL |> SPEC_ALL |> #2 o EQ_IMP_RULE) >>
  rw[weak_cmult_element, weak_cmult_length, ZN_property]);

(* Theorem: LENGTH (valueOf (poly_cmultM n c p)) = LENGTH p *)
(* Proof:
     LENGTH (valueOf (poly_cmultM n c p))
   = LENGTH (weak_cmult (ZN n) c p)       by poly_cmultM_value
   = LENGTH p                             by weak_cmult_length
*)
val poly_cmultM_length = store_thm(
  "poly_cmultM_length[simp]",
  ``!n c p. LENGTH (valueOf (poly_cmultM n c p)) = LENGTH p``,
  rw[weak_cmult_length]);

(* Theorem: stepsOf (poly_cmultM n c p) =
            if (p = []) then 1
            else 4 + size c * size (HD p) + size (c * HD p) * size n +
                 stepsOf (poly_cmultM n c (TL p)) *)
(* Proof:
     stepsOf (poly_cmultM n c p)
   = stepsOf (nullM p) + if (p = []) then 0
     else stepsOf (headM p) + stepsOf (tailM p) +
          stepsOf (mmulM n c (HD p)) +
          stepsOf (poly_cmultM n c (TL p)) +
          stepsOf (consM ((c * HD p) MOD n) (valueOf (poly_cmultM n c (TL p))))
                                 by poly_cmultM_def
   = 1  + if (p = []) then 0
     else 1 + 1 + (size c * size (HD p) + size (c * HD p) * size n +
     stepsOf (poly_cmultM n c (TL p)) + 1      by mmulM_steps
   = if (p = []) then 1
     else 4 + size c * size (HD p) + size (c * HD p) * size n +
          stepsOf (poly_cmultM n c (TL p))     by arithmetic
*)
val poly_cmultM_steps_thm = store_thm(
  "poly_cmultM_steps_thm",
  ``!n c p. stepsOf (poly_cmultM n c p) =
           if (p = []) then 1
           else 4 + size c * size (HD p) + size (c * HD p) * size n +
                stepsOf (poly_cmultM n c (TL p))``,
  ho_match_mp_tac (theorem "poly_cmultM_ind") >>
  rpt strip_tac >>
  (Cases_on `p` >> simp[Once poly_cmultM_def]));

(* Theorem alias *)
val poly_cmultM_steps_by_list_loop = save_thm("poly_cmultM_steps_by_list_loop", poly_cmultM_steps_thm);

(*
This puts poly_cmultM_steps in the category: list loop with body on head.
   poly_cmultM_steps_by_list_loop:
        !p. loop p = if (p = []) then c else body p + loop (TL p)
suitable for: loop_list_head_count_eqn
and also for: loop_list_head_upper_count_le
*)

(* Theorem: stepsOf (poly_cmultM n c p) =
            1 + SUM (GENLIST (\j. 4 + size c * size (EL j p) +
                     size (c * (EL j p)) * size n) (LENGTH p)) *)
(* Proof:
   Let f = (\j. 4 + size c * size j + size (c * j) * size n),
       body = (\p. f (HD p)),
       loop = (\p. stepsOf (poly_cmultM n c p))
   Then loop p = if (p = []) then 1 else body p + loop (TL p)    by poly_cmultM_steps_thm
   Thus loop p = 1 + SUM (GENLIST (\j. f (EL j p)) (LENGTH p))   by loop_list_head_count_eqn
*)
val poly_cmultM_steps_eqn = store_thm(
  "poly_cmultM_steps_eqn",
  ``!n c p. stepsOf (poly_cmultM n c p) =
           1 + SUM (GENLIST (\j. 4 + size c * size (EL j p) + size (c * (EL j p)) * size n)
                            (LENGTH p))``,
  rpt strip_tac >>
  qabbrev_tac `f = \j. 4 + size c * size j + size (c * j) * size n` >>
  qabbrev_tac `body = \p. f (HD p)` >>
  qabbrev_tac `loop = \p. stepsOf (poly_cmultM n c p)` >>
  `loop p = 1 + SUM (GENLIST (\j. f (EL j p)) (LENGTH p))` suffices_by rw[] >>
  `!p. loop p = if (p = []) then 1 else body p + loop (TL p)` by metis_tac[poly_cmultM_steps_thm] >>
  `body = (\x. f (HD x))` by metis_tac[] >>
  imp_res_tac loop_list_head_count_eqn >>
  first_x_assum (qspec_then `p` strip_assume_tac));

(* Theorem: Weak (ZN n) p  /\ (LENGTH p = k) ==>
       stepsOf (poly_cmultM n c p) <=
       1 + 4 * k + 2 * k * size c * size n + k * (size n) ** 2 *)
(* Proof:
   Let f = (\j. 4 + size c * size j + size (c * j) * size n),
       body = (\p. f (HD p)),
       loop = (stepsOf o poly_cmultM n c)
   Then loop p = if (p = []) then 1 else body p + loop (TL p)    by poly_cmultM_steps_thm
    Now Weak (ZN n) p <=> EVERY (\j.j < n) p                     by ZN_weak
    and MONO f                         by size_monotone_le
   Thus loop p
     <= 1 + k * f n                    by loop_list_head_upper_count_le
      = 1 + k * (4 + size c * size n + size (c * n) * size n)
     <= 1 + 4 * k + k * size c * size n + k * size (c * n) * size n
     <= 1 + 4 * k + k * size c * size n + k * (size c + size n) * size n    by size_mult_upper
      = 1 + 4 * k + 2 * k * size c * size n + k * size n ** 2
*)
val poly_cmultM_steps_upper = store_thm(
  "poly_cmultM_steps_upper",
  ``!n c p k. Weak (ZN n) p /\ (LENGTH p = k) ==>
       stepsOf (poly_cmultM n c p) <= 1 + 4 * k + 2 * k * size c * size n + k * (size n) ** 2``,
  rpt strip_tac >>
  qabbrev_tac `f = \j. 4 + size c * size j + size (c * j) * size n` >>
  qabbrev_tac `body = \p. f (HD p)` >>
  qabbrev_tac `loop = (stepsOf o poly_cmultM n c)` >>
  `loop p <= 1 + 4 * k + 2 * k * size c * size n + k * (size n) ** 2` suffices_by rw[Abbr`loop`, Abbr`f`] >>
  `!p. loop p = if (p = []) then 1 else body p + loop (TL p)` by metis_tac[poly_cmultM_steps_thm, combinTheory.o_THM] >>
  `MONO f` by
  (rw[size_monotone_le, Abbr`f`] >>
  `c * x <= c * y` by rw[] >>
  `size c * size x <= size c * size y /\ size n * size (c * x) <= size n * size (c * y)` by rw[size_monotone_le] >>
  decide_tac) >>
  `loop p <= 1 + k * f n` by metis_tac[loop_list_head_upper_count_le, ZN_weak] >>
  `k * f n <= 4 * k + TWICE k * size c * size n + k * size n ** 2` by
    (rw[Abbr`f`] >>
  qabbrev_tac `k = LENGTH p` >>
  `size (c * n) <= size c + size n` by rw[size_mult_upper] >>
  `size n * size (c * n) <= size n * (size c + size n)` by rw[] >>
  `size n * (size c + size n) = size n * size c + size n * size n` by decide_tac >>
  `_ = size n * size c + (size n) ** 2` by rw[] >>
  `k * (size c * size n + (size n * size (c * n) + 4)) <=
    k * (size c * size n + (size n * size c + (size n) ** 2 + 4))` by rw[] >>
  decide_tac) >>
  decide_tac);

(* Theorem: Weak (ZN n) p /\ (LENGTH p = k) ==>
            stepsOf (poly_cmultM n c p) <= 8 * (MAX 1 k) * size (MAX c n) * size n *)
(* Proof:
      stepsOf (poly_cmultM n c p)
   <= 1 + 4 * k + 2 * k * size c * size n + k * size n ** 2
                                                      by poly_cmultM_steps_upper
   <= (1 + 4 + 2 + 1) * k * size (MAX c n) * size n   by dominant term
    =  8 * k * size (MAX c n) * size n
   Use (MAX 1 k) to cater for k = 0.
*)
val poly_cmultM_steps_bound = store_thm(
  "poly_cmultM_steps_bound",
  ``!n c p k. Weak (ZN n) p /\ (LENGTH p = k) ==>
       stepsOf (poly_cmultM n c p) <= 8 * (MAX 1 k) * size (MAX c n) * size n``,
  rpt strip_tac >>
  `stepsOf (poly_cmultM n c p) <=
    1 + 4 * k + 2 * k * size c * size n + k * size n ** 2` by rw[poly_cmultM_steps_upper] >>
  qabbrev_tac `m = MAX 1 k` >>
  qabbrev_tac `d = MAX c n` >>
  qabbrev_tac `t = m * size d * size n` >>
  `stepsOf (poly_cmultM n c p) <= 8 * t` suffices_by rw[] >>
  `1 <= m /\ k <= m` by rw[Abbr`m`] >>
  `c <= d /\ n <= d` by rw[Abbr`d`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `k <= t` by
  (`m <= m * (size d * size n)` by rw[MULT_POS] >>
  `m * (size d * size n) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k * size c * size n <= t` by
    (`k * size c * size n <= m * size d * size n` by rw[size_monotone_le, LE_MONO_MULT2] >>
  `m * size d * size n = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k * size n ** 2 <= t` by
      (`k * size n ** 2 = k * size n * size n` by rw[] >>
  `k * size n * size n <= m * size d * size n` by rw[size_monotone_le, LE_MONO_MULT2] >>
  `m * size d * size n = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Polynomial weak addition (by pair-wise add in mod n)                      *)
(* ------------------------------------------------------------------------- *)

(* Add two polynomials p, q of the same length k in (MOD n, (unity k)) *)
(* > weak_add_def;
|- (!r q. [] || q = q) /\ (!v5 v4 r. (v4::v5) || [] = v4::v5) /\
    !r qt qh pt ph. (ph::pt) || (qh::qt) = ph + qh::pt || qt
*)

(* Pseudocode:
   Given modulus n, and polynomials p and q, compute p || q (mod n).
   list_add p q:
      if p = [], return q              // [] || q = q
      if q = [], return p              // p || [] = p
      h <- (head p) + (head q) MOD n   // pair-wise add of heads
      t <- list_add (tail p) (tail q)  // recursive call with tails: (tail p) || (tail q)
      return h::t                      // combine to give result
*)
Definition poly_addM_def:
  poly_addM n p q =
      do
        p0 <- nullM p;
        q0 <- nullM q;
        if p0 then return q
        else if q0 then return p
        else do
               h1 <- headM p;
               h2 <- headM q;
               t1 <- tailM p;
               t2 <- tailM q;
               h <- maddM n h1 h2;
               r <- poly_addM n t1 t2;
               consM h r;
             od
      od
Termination
  WF_REL_TAC `measure (λ(n,p,q). LENGTH q)` >> simp[LENGTH_TL_LT]
End

(*
> EVAL ``poly_addM 10 [1;4;5;6;1;1;3] [1;5;1;6;3;3;2]``; = ([2; 9; 6; 2; 4; 4; 5],Count 155): thm
*)

(* Theorem: valueOf (poly_addM n p q) = weak_add (ZN n) p q *)
(* Proof:
   If p = [],
      valueOf (poly_addM n [] q)
    = q                           by poly_addM_def
    = weak_add (ZN n) [] q        by weak_add_nil
   If q = [],
      valueOf (poly_addM n p [])
    = p                           by poly_addM_def
    = weak_add (ZN n) p []        by weak_add_nil
   Otherwise, p <> [] /\ q <> [].
      Let p = h::t, q = k::s.
      valueOf (poly_addM n (h::t) (k::s))
    = (h + k) MOD n :: valueOf (poly_addM n t s)    by poly_addM_def
    = (h + k) MOD n :: weak_add (ZN n) t s          by induction hypothesis
    = weak_add (ZN n) (h::t) (k::s)                 by weak_add_cons, ZN_property
*)
val poly_addM_value = store_thm(
  "poly_addM_value[simp]",
  ``!n p q. valueOf (poly_addM n p q) = weak_add (ZN n) p q``,
  ho_match_mp_tac (theorem "poly_addM_ind") >>
  rw[] >>
  rw[Once poly_addM_def] >>
  (Cases_on `p` >> Cases_on `q` >> fs[ZN_property]));

(* Theorem: Weak (ZN n) p /\ Weak (ZN n) q /\ (LENGTH p = LENGTH q) ==>
          (valueOf (poly_addM n p q) = p +z q) *)
(* Proof: by poly_addM_value, ZN_poly_add_alt *)
val poly_addM_value_alt = store_thm(
  "poly_addM_value_alt",
  ``!n p q. Weak (ZN n) p /\ Weak (ZN n) q /\ (LENGTH p = LENGTH q) ==>
          (valueOf (poly_addM n p q) = p +z q)``,
  rw[ZN_poly_add_alt]);

(* Theorem: j < LENGTH p /\ j < LENGTH q ==>
            (EL j (valueOf (poly_addM n p q)) = ((EL j p) + (EL j q)) MOD n) *)
(* Proof:
     EL j (valueOf (poly_addM n p q))
   = EL j (weak_add (ZN n) p q)          by poly_addM_value
   = ((EL j p) + (EL j q)) MOD n         by weak_add_element, ZN_property
*)
val poly_addM_element = store_thm(
  "poly_addM_element",
  ``!n p q j. j < LENGTH p /\ j < LENGTH q ==>
             (EL j (valueOf (poly_addM n p q)) = ((EL j p) + (EL j q)) MOD n)``,
  rw[weak_add_element, ZN_property]);

(* Note: weak_add_weak |- !r. Ring r ==> !p q. weak p /\ weak q ==> weak (p || q)
   requires Weak (ZN n) p and Weak (ZN n) q. Here we just need p:num list and q:num list.
   Thus the following proof, using weak_add_element, is better, special for (ZN n).
*)

(* Theorem: 0 < n /\ (LENGTH p = LENGTH q) ==> Weak (ZN n) (valueOf (poly_addM n p q)) *)
(* Proof:
   Note MAX (LENGTH p) (LENGTH q) = LENGTH p     by MAX_DEF, LENGTH p = LENGTH q.
     Weak (ZN n) (valueOf (poly_addM n p q))
   = Weak (ZN n) (weak_add (ZN n) p q)           by poly_addM_value
   = EVERY (\j. j < n) (weak_add (ZN n) p q)     by ZN_weak
   = !j. EL j (weak_add (ZN n) p q) < n          by EVERY_EL
   = !j. (EL j p + EL j q) MOD n < n             by weak_add_element, ZN_property
   = T                                           by MOD_LESS, 0 < n
*)
val poly_addM_weak = store_thm(
  "poly_addM_weak",
  ``!n p q. 0 < n /\ (LENGTH p = LENGTH q) ==> Weak (ZN n) (valueOf (poly_addM n p q))``,
  rw[ZN_weak, EVERY_EL] >>
  fs[weak_add_length, MAX_DEF] >>
  `n' < LENGTH p /\ n' < LENGTH q` by decide_tac >>
  rw[weak_add_element, ZN_property]);

(* Theorem: LENGTH (valueOf (poly_addM n p q)) = MAX (LENGTH p) (LENGTH q) *)
(* Proof:
     LENGTH (valueOf (poly_addM n p q))
   = LENGTH (weak_add (ZN n) p q)            by poly_addM_value
   = MAX (LENGTH p) (LENGTH q)               by weak_add_length
*)
val poly_addM_length = store_thm(
  "poly_addM_length[simp]",
  ``!n p q. LENGTH (valueOf (poly_addM n p q)) = MAX (LENGTH p) (LENGTH q)``,
  rw[weak_add_length]);

(* Theorem: stepsOf (poly_addM n p q) =
            if (p = []) \/ (q = []) then 2
            else 7 + size (MAX (HD p) (HD q)) + size (HD p + HD q) * size n +
                 stepsOf (poly_addM n (TL p) (TL q)) *)
(* Proof:
     stepsOf (poly_addM n p q)
   = stepsOf (nullM p) + stepsOf (nullM q) + if (p = []) then 0 else if q = [] then 0
     else stepsOf (headM p) + stepsOf (headM q) + stepsOf (tailM p) + stepsOf (tailM q) +
          stepsOf (maddM n (HD p) (HD q)) + stepsOf (poly_addM n (TL p) (TL q)) +
          stepsOf (consM ((HD p + HD q) MOD n) r)      by poly_addM_def
   = 1 + 1 + if (p = []) then 0 else if q = [] then 0
     else 1 + 1 + 1 + 1 +
     size (MAX (HD p) (HD q)) + size (HD p + HD q) * size n +
     stepsOf (poly_addM n (TL p) (TL q)) + 1           by size_max
   = if (p = []) \/ (q = []) then 2
     else 7 + size (MAX (HD p) (HD q)) + size (HD p + HD q) * size n +
          stepsOf (poly_addM n (TL p) (TL q))
*)
val poly_addM_steps_thm = store_thm(
  "poly_addM_steps_thm",
  ``!n p q. stepsOf (poly_addM n p q) =
           if (p = []) \/ (q = []) then 2
           else 7 + size (MAX (HD p) (HD q)) + size (HD p + HD q) * size n +
                stepsOf (poly_addM n (TL p) (TL q))``,
  (rw[Once poly_addM_def, size_max] >> fs[]));

(* Theorem alias *)
val poly_addM_steps_by_list_loop = save_thm("poly_addM_steps_by_list_loop", poly_addM_steps_thm);

(*
This puts poly_addM_steps in the category: list loop with body on head and transform on head.
   poly_addM_steps_by_list_loop:
        !p q. loop p q = if (p = []) \/ (q = []) then c else body p q + loop (TL p) (TL q)
suitable for: loop2_list_tail_head_count_eqn
and also for: loop2_list_tail_head_upper_count_le
*)

(* Theorem: (LENGTH p = k) /\ (LENGTH q = k) ==>
            (stepsOf (poly_addM n p q) =
               2 + SUM (GENLIST (\j. 7 + size (MAX (EL j p) (EL j q)) +
                                     size (EL j p + EL j q) * size n) k)) *)
(* Proof:
   Let quit = (\p q. 2),
       f = (\i j. 7 + size (MAX i j) + size (i + j) * size n),
       body = (\p q. f (HD p) (HD q)),
       loop = (\p q. stepsOf (poly_addM n p q)).
   Then loop p q = if (p = []) \/ (q = []) then quit p q else body p q + loop (TL p) (TL q)
                                                              by poly_addM_steps_thm
   Thus loop p q
      = quit [][] + SUM (GENLIST (\j. f (EL j p) (EL j q)) k) by loop2_list_tail_head_count_eqn
      = 2 + SUM (GENLIST (\j. f (EL j p) (EL j q)) k)
*)
val poly_addM_steps_eqn = store_thm(
  "poly_addM_steps_eqn",
  ``!n p q k. (LENGTH p = k) /\ (LENGTH q = k) ==>
      (stepsOf (poly_addM n p q) =
       2 + SUM (GENLIST (\j. 7 + size (MAX (EL j p) (EL j q)) +
                             size (EL j p + EL j q) * size n) k))``,
  rpt strip_tac >>
  qabbrev_tac `quit = \p:num list q:num list. 2` >>
  qabbrev_tac `f = \i j. 7 + size (MAX i j) + size (i + j) * size n` >>
  qabbrev_tac `body = \p q. f (HD p) (HD q)` >>
  qabbrev_tac `loop = \p q. stepsOf (poly_addM n p q)` >>
  qabbrev_tac `g = \j. 7 + size (MAX (EL j p) (EL j q)) + size (EL j p + EL j q) * size n` >>
  `loop p q = 2 + SUM (GENLIST g k)` suffices_by rw[] >>
  `g = \j. f (EL j p) (EL j q)` by rw[Abbr`g`, Abbr`f`] >>
  `SUM (GENLIST g k) = SUM (GENLIST (\j. f (EL j p) (EL j q)) k)` by rw[] >>
  `!p q. loop p q = if (p = []) \/ (q = []) then quit p q else body p q + loop (TL p) (TL q)` by metis_tac[poly_addM_steps_thm] >>
  `body = (\p q. f (HD p) (HD q))` by metis_tac[] >>
  imp_res_tac loop2_list_tail_head_count_eqn >>
  metis_tac[]);

(* Theorem: Weak (ZN n) p /\ Weak (ZN n) q /\ (LENGTH p = k) /\ (LENGTH q = k) ==>
            stepsOf (poly_addM n p q) <= 2 + 7 * k + 2 * k * size n + k * size n ** 2 *)
(* Proof:
   Let quit = (\p q. 2),
       f = (\i j. 7 + size (MAX i j) + size (i + j) * size n),
       body = (\p q. f (HD p) (HD q)),
       loop = (\p q. stepsOf (poly_addM n p q)).
   Then loop p q = if (p = []) \/ (q = []) then quit p q else body p q + loop (TL p) (TL q)
                                                     by poly_addM_steps_thm
    Now MONO2 f                                      by size_monotone_le
   Thus loop p q
     <= quit [][] + k * f n n                        by loop2_list_tail_head_upper_count_le
      = 2 + k * (7 + size (MAX n n) + size (n + n) * size n)  by function application
      = 2 + k * (7 + size n + size (2 * n) * size n)    by MAX_IDEM
      = 2 + k * (7 + size n + (size n + if n = 0 then 0 else 1) * size n)  by size_twice
     <= 2 + k * (7 + size n + (size n + 1) * size n)    by inequality
      = 2 + k * (7 + size n + size n ** 2 + size n)
      = 2 + 7 * k + 2 * k * size n + k * size n ** 2
*)
val poly_addM_steps_upper = store_thm(
  "poly_addM_steps_upper",
  ``!n p q k. Weak (ZN n) p /\ Weak (ZN n) q /\ (LENGTH p = k) /\ (LENGTH q = k) ==>
      stepsOf (poly_addM n p q) <= 2 + 7 * k + 2 * k * size n + k * size n ** 2``,
  rpt strip_tac >>
  qabbrev_tac `quit = \p:num list q:num list. 2` >>
  qabbrev_tac `f = \i j. 7 + size (MAX i j) + size (i + j) * size n` >>
  qabbrev_tac `body = \p q. f (HD p) (HD q)` >>
  qabbrev_tac `loop = \p q. stepsOf (poly_addM n p q)` >>
  `loop p q <= 2 + 7 * k + 2 * k * size n + k * size n ** 2` suffices_by rw[] >>
  `!p q. loop p q = if (p = []) \/ (q = []) then quit p q else body p q + loop (TL p) (TL q)` by metis_tac[poly_addM_steps_thm] >>
  `EVERY (\j. j < n) p /\ EVERY (\j. j < n) q` by rw[GSYM ZN_weak] >>
  `MONO2 f` by
  (rw[size_monotone_le, Abbr`f`] >>
  `MAX x1 y1 <= MAX x2 y2` by rw[] >>
  `x1 + y1 <= x2 + y2` by decide_tac >>
  `size (MAX x1 y1) <= size (MAX x2 y2)` by rw[size_monotone_le] >>
  `size n * size (x1 + y1) <= size n * size (x2 + y2)` by rw[size_monotone_le] >>
  decide_tac) >>
  `body = (\p q. f (HD p) (HD q))` by metis_tac[] >>
  imp_res_tac loop2_list_tail_head_upper_count_le >>
  `loop p q <= 2 + k * f n n` by metis_tac[] >>
  `k * f n n <= 7 * k + 2 * k * size n + k * size n ** 2` by
    (rw[Abbr`f`] >>
  qabbrev_tac `k = LENGTH q` >>
  `k * (size n + (size n * size (2 * n) + 7)) =
    k * size n + k * size n * size (2 * n) + 7 * k` by decide_tac >>
  `size (2 * n) <= 1 + size n` by rw[size_twice] >>
  `k * size n * size (2 * n) <= k * size n * (1 + size n)` by rw[] >>
  `k * size n * (1 + size n) = k * size n + k * size n * size n` by decide_tac >>
  `k * size n * size n = k * size n ** 2` by rw[] >>
  decide_tac) >>
  decide_tac);

(* Theorem: Weak (ZN n) p /\ Weak (ZN n) q /\ (LENGTH p = k) /\ (LENGTH q = k) ==>
            stepsOf (poly_addM n p q) <= 12 * (MAX 1 k) * size n ** 2 *)
(* Proof:
      stepsOf (poly_addM n p q)
   <= 2 + 7 * k + 2 * k * size n + k * size n ** 2    by poly_addM_steps_upper
   <= (2 + 7 + 2 + 1) * k * size n ** 2               by dominant term
    = 12 * k * size n ** 2
   Use (MAX 1 k) to cater for k = 0.
*)
val poly_addM_steps_bound = store_thm(
  "poly_addM_steps_bound",
  ``!n p q k. Weak (ZN n) p /\ Weak (ZN n) q /\ (LENGTH p = k) /\ (LENGTH q = k) ==>
      stepsOf (poly_addM n p q) <= 12 * (MAX 1 k) * size n ** 2``,
  rpt strip_tac >>
  `stepsOf (poly_addM n p q) <= 2 + 7 * k + 2 * k * size n + k * size n ** 2` by rw[poly_addM_steps_upper] >>
  qabbrev_tac `m = MAX 1 k` >>
  qabbrev_tac `t = m * (size n) ** 2` >>
  `stepsOf (poly_addM n p q) <= 12 * t` suffices_by rw[Abbr`t`] >>
  `1 <= m /\ k <= m` by rw[Abbr`m`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `k <= t` by
  (`m <= m * (size n) ** 2` by rw[MULT_POS] >>
  `m * (size n) ** 2 = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k * size n <= t` by
    (`k * size n <= m * size n` by rw[] >>
  `m * size n <= m * size n * size n` by rw[MULT_POS] >>
  `m * size n * size n = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k * size n ** 2 <= t` by
      (`k * size n ** 2 <= m * size n ** 2` by rw[] >>
  `m * size n ** 2 = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Polynomial multiplication by X in (mod n, unity k)                        *)
(* ------------------------------------------------------------------------- *)

(* > LAST_DEF;
val it = |- !h t. LAST (h::t) = if t = [] then h else LAST t: thm
*)

(* Pseudocode:
   Given a polynomial p, compute (LAST p).
   list_last p:
      if p = [], return (LAST [])       // undefined
      h <- head p                       // get head
      t <- tail p                       // examine tail
      if t = [] then return h           // no tail, head is LAST
      return list_last t                // skip head, recursive call for (LAST tail)
*)

Definition poly_lastM_def:
  poly_lastM p =
      do
        p0 <- nullM p;
        if p0 then return (LAST [])
        else do
                h <- headM p;
                t <- tailM p;
                t0 <- nullM t;
                if t0 then return h
                else poly_lastM t;
             od
      od
Termination WF_REL_TAC `measure LENGTH` >> simp[LENGTH_TL_LT]
End

(* > FRONT_DEF;
val it = |- !h t. FRONT (h::t) = if t = [] then [] else h::FRONT t: thm
*)

(* Pseudocode:
   Given a polynomial p, compute (FRONT p).
   list_front p:
      if p = [], return (FRONT []) // undefined
      h <- head p                  // get head
      t <- tail p                  // examine tail
      if t = [] return []          // no tail, FRONT = empty tail
      q <- list_front t            // get (FRONT tail)
      return h::q                  // combine to give result
*)

Definition poly_frontM_def:
  poly_frontM p =
      do
        p0 <- nullM p;
        if p0 then return (FRONT [])
        else do
                h <- headM p;
                t <- tailM p;
                t0 <- nullM t;
                if t0 then return []
                else do
                       q <- poly_frontM t;
                       consM h q
                     od
             od
      od
Termination WF_REL_TAC `measure LENGTH` >> simp[LENGTH_TL_LT]
End

(* Pseudocode:
   Given a polynomial p, compute p * X (mod unity k), where k = LENGTH p.
   list_turn p:
      if p = [], return []     // [] * X = []
      h <- LAST p              // get (LAST p)
      t <- FRONT p             // get (FRONT p)
      return h::t              // combine to give result
*)

(* Multiply a polynomial p by X, in (mod unity k). *)
val poly_turnM_def = Define`
    poly_turnM p =
       do
          p0 <- nullM p;
          if p0 then return []
          else do
                 h <- poly_lastM p;
                 t <- poly_frontM p;
                 consM h t;
               od
       od
`;

(*
EVAL ``poly_lastM [1;2;4;5;3]``; = (3,Count 20): thm
EVAL ``poly_frontM [1;2;4;5;3]``; = ([1; 2; 4; 5],Count 24): thm
EVAL ``poly_turnM [1;2;4;5;3]``; = ([3; 1; 2; 4; 5],Count 46): thm
*)

(* Theorem: valueOf (poly_lastM p) = LAST p *)
(* Proof:
   If p = [],
        valueOf (poly_lastM [])
      = LAST []                        by poly_lastM_def
   If p <> [], let p = h::t.
        valueOf (poly_lastM p)
      = if t = [] then h else valueOf (poly_lastM t)
                                       by poly_lastM_def
      = if t = [] then h else LAST t   by induction hypothesis
      = LAST (h::t)                    by LAST_DEF
*)
val poly_lastM_value = store_thm(
  "poly_lastM_value[simp]",
  ``!p. valueOf (poly_lastM p) = LAST p``,
  ho_match_mp_tac (theorem "poly_lastM_ind") >>
  rw[] >>
  (Cases_on `p` >> rw[Once poly_lastM_def] >> fs[LAST_DEF]));

(* Theorem: valueOf (poly_frontM p) = FRONT p *)
(* Proof:
   If p = [],
        valueOf (poly_frontM [])
      = FRONT []                            by poly_frontM_def
   If p <> [], let p = h::t.
        valueOf (poly_frontM p)
      = if t = [] then [] else h::valueOf (poly_frontM t)
                                            by poly_frontM_def
      = if t = [] then [] else h::FRONT t   by induction hypothesis
      = FRONT (h::t)                        by FRONT_DEF
*)
val poly_frontM_value = store_thm(
  "poly_frontM_value[simp]",
  ``!p. valueOf (poly_frontM p) = FRONT p``,
  ho_match_mp_tac (theorem "poly_frontM_ind") >>
  rw[] >>
  (Cases_on `p` >> rw[Once poly_frontM_def] >> fs[FRONT_DEF]));

(* Theorem: valueOf (poly_turnM p) = turn p *)
(* Proof:
   If p = [],
         valueOf (poly_turnM [])
       = []                        by poly_turnM_def
       = turn []                   by turn_nil
   If p <> [],
         valueOf (poly_turnM p)
       = LAST p :: FRONT p         by poly_turnM_def
       = turn p                    by turn_def
*)
val poly_turnM_value = store_thm(
  "poly_turnM_value[simp]",
  ``!p. valueOf (poly_turnM p) = turn p``,
  rw[poly_turnM_def, turn_def]);

(* Theorem: stepsOf (poly_lastM p) =
            if (p = []) then 1 else 4 + if (TL p = []) then 0 else stepsOf (poly_lastM (TL p)) *)
(* Proof:
     stepsOf (poly_lastM p)
   = stepsOf (nullM p) + if (p = []) then 0
     else stepsOf (headM p) + stepsOf (tailM p) +
          stepsOf (nullM t) + if (TL p = []) then 0
          else stepsOf (poly_lastM (TL p))         by poly_lastM_def
   = 1 + if (p = []) then 0
     else 1 + 1 + 1 + if (TL p = []) then 0 else stepsOf (poly_lastM (TL p))
   = 1 + if (p = []) then 0 else 3 + if (TL p = []) then 0 else stepsOf (poly_lastM (TL p))
   = if (p = []) then 1 else 4 + if (TL p = []) then 0 else stepsOf (poly_lastM (TL p))
*)
val poly_lastM_steps_thm = store_thm(
  "poly_lastM_steps_thm",
  ``!p. stepsOf (poly_lastM p) =
        if (p = []) then 1 else 4 + if (TL p = []) then 0 else stepsOf (poly_lastM (TL p))``,
  ho_match_mp_tac (theorem "poly_lastM_ind") >>
  (rw[] >> rw[Once poly_lastM_def]));

(* Theorem alias *)
val poly_lastM_steps_by_list_loop = save_thm("poly_lastM_steps_by_list_loop", poly_lastM_steps_thm);

(*
This puts poly_lastM_steps in the category: list loop with body and exit.
   poly_lastM_steps_by_list_loop:
        !p. loop p = if (p = []) then c else body p + if exit p then 0 else loop (TL p)
suitable for: loop_list_count_exit_le
*)

(* Theorem: stepsOf (poly_lastM p) <= 1 + 4 * LENGTH p *)
(* Proof:
   Let body = (\p. 4),
       exit = (\p. TL p = []),
       loop = (\p. stepsOf (poly_lastM p)).
   Then !x. loop x = if x = [] then 1 else body x + if exit x then 0 else loop (TL x)
                                                   by poly_lastM_steps_thm
    Now !x y. x <= y ==> body x <= body y          as body is constant
   Thus loop p <= 1 + body p * LENGTH p            by loop_list_count_exit_le
                = 1 + 4 * LENGTH p
*)
val poly_lastM_steps_upper = store_thm(
  "poly_lastM_steps_upper",
  ``!p. stepsOf (poly_lastM p) <= 1 + 4 * LENGTH p``,
  rpt strip_tac >>
  qabbrev_tac `body = \p:'a list. 4` >>
  qabbrev_tac `exit = \p. TL p = []` >>
  qabbrev_tac `loop = \p. stepsOf (poly_lastM p)` >>
  `loop p <= 1 + 4 * LENGTH p` suffices_by rw[] >>
  `!x. loop x = if x = [] then 1 else body x + if exit x then 0 else loop (TL x)` by metis_tac[poly_lastM_steps_thm] >>
  `!x y. x <= y ==> body x <= body y` by rw[Abbr`body`] >>
  imp_res_tac loop_list_count_exit_le >>
  metis_tac[]);

(* Theorem: stepsOf (poly_frontM p) =
            if (p = []) then 1
            else (4 + if (TL p = []) then 0 else 1) +
                 (if (TL p = []) then 0 else stepsOf (poly_frontM (TL p))) *)
(* Proof:
     stepsOf (poly_frontM p)
   = stepsOf (nullM p) + if (p = []) then 0
     else stepsOf (headM p) + stepsOf (tailM p) +
          stepsOf (nullM t) + if (TL p = []) then 0
          else stepsOf (poly_frontM (TL p)) + stepsOf (consM (HD p) (FRONT (TL p)))
                                                  by poly_frontM_def
   = 1 + if (p = []) then 0
     else 1 + 1 + 1 + if (TL p = []) then 0 else stepsOf (poly_frontM (TL p)) + 1
   = 1 + if (p = []) then 0 else 3 + if (TL p = []) then 0 else (1 + stepsOf (poly_frontM (TL p)))
   = if (p = []) then 1 else 4 + if (TL p = []) then 0 else (1 + stepsOf (poly_frontM (TL p)))
   = if (p = []) then 1 else (4 + if (TL p = []) then 0 else 1) + (if (TL p = []) then 0 else stepsOf (poly_frontM (TL p)))
*)
val poly_frontM_steps_thm = store_thm(
  "poly_frontM_steps_thm",
  ``!p. stepsOf (poly_frontM p) =
        if (p = []) then 1
        else (4 + if (TL p = []) then 0 else 1) +
             (if (TL p = []) then 0 else stepsOf (poly_frontM (TL p)))``,
  ho_match_mp_tac (theorem "poly_frontM_ind") >>
  (rw[] >> rw[Once poly_frontM_def]));

(* Theorem alias *)
val poly_frontM_steps_by_list_loop = save_thm("poly_frontM_steps_by_list_loop", poly_frontM_steps_thm);

(*
This puts poly_frontM_steps in the category: list loop with body cover and exit.
   poly_frontM_steps_by_list_loop:
        !p. loop p = if (p = []) then c else body p + if exit p then 0 else loop (TL p)
suitable for: loop_list_count_cover_exit_le
*)

(* Theorem: stepsOf (poly_frontM p) <= 1 + 5 * LENGTH p *)
(* Proof:
   Let body = (\p. 4 + if (TL p = []) then 0 else 1),
       cover = (\p. 5),
       exit = (\p. TL p = []),
       loop = (\p. stepsOf (poly_frontM p)).
   Then !p. loop p = if (p = []) then 1 else body p + if exit p then 0 else loop (TL p)
                                                by poly_frontM_steps_thm
    Now !x. body x <= cover x                   by cases on TL p,
    and !x y. x <= y ==> cover x <= cover y     by cover being a constant
   Thus loop p <= 1 + cover p * LENGTH p        by loop_list_count_cover_exit_le
                = 1 + 5 * LENGTH p
*)
val poly_frontM_steps_upper = store_thm(
  "poly_frontM_steps_upper",
  ``!p. stepsOf (poly_frontM p) <= 1 + 5 * LENGTH p``,
  rpt strip_tac >>
  qabbrev_tac `body = \p. 4 + if (TL p = []) then 0 else 1` >>
  qabbrev_tac `cover = \p:'a list. 5` >>
  qabbrev_tac `exit = \p. TL p = []` >>
  qabbrev_tac `loop = \p. stepsOf (poly_frontM p)` >>
  `loop p <= 1 + 5 * LENGTH p` suffices_by rw[] >>
  `!x. loop x = if x = [] then 1 else body x + if exit x then 0 else loop (TL x)` by metis_tac[poly_frontM_steps_thm] >>
  `!x. body x <= cover x` by rw[Abbr`body`, Abbr`cover`] >>
  `!x y. x <= y ==> cover x <= cover y` by rw[Abbr`cover`] >>
  imp_res_tac loop_list_count_cover_exit_le >>
  metis_tac[]);

(* Michael's proof of the same theorem. *)

(* Theorem: stepsOf (poly_frontM p) <= 1 + 5 * LENGTH p *)
(* Proof:
   Let body = (\p. 4 + if (TL p = []) then 0 else 1),
       exit = (\p. TL p = []),
       loop = (\p. stepsOf (poly_frontM p)).
   Then !p. loop p = if (p = []) then 1 else body p + if exit p then 0 else loop (TL p)
                                                by poly_frontM_steps_thm
    Now !x. body x <= 5                         by cases on TL p,
   Thus loop p <= 1 + 5 * LENGTH p              by loop_list_count_constant_cover_exit_le
*)
val poly_frontM_steps_upper = store_thm(
  "poly_frontM_steps_upper",
  ``!p. stepsOf (poly_frontM p) <= 1 + 5 * LENGTH p``,
  ho_match_mp_tac loop_list_count_constant_cover_exit_le >>
  qexists_tac `\p. TL p = []` >>
  qexists_tac `\p. 4 + if (TL p = []) then 0 else 1` >>
  rw[Once poly_frontM_steps_thm]);

(* Theorem: stepsOf (poly_turnM p) =
            if (p = []) then 1 else 2 + stepsOf (poly_lastM p) + stepsOf(poly_frontM p) *)
(* Proof:
     stepsOf (poly_turnM p)
   = stepsOf (nullM p) + if (p = []) then 0
     else stepsOf (poly_lastM p) + stepsOf(poly_frontM p) + stepsOf (consM h q)   by poly_turnM_def
   = 1 + if (p = []) then 0 else  1 + stepsOf (poly_lastM p) + stepsOf(poly_frontM p)
   = if (p = []) then 1 else 2 + stepsOf (poly_lastM p) + stepsOf(poly_frontM p)
*)
val poly_turnM_steps_thm = store_thm(
  "poly_turnM_steps_thm",
  ``!p. stepsOf (poly_turnM p) =
        if (p = []) then 1 else 2 + stepsOf (poly_lastM p) + stepsOf(poly_frontM p)``,
  rw[poly_turnM_def]);

(* Theorem: stepsOf (poly_turnM p) <= 4 + 9 * LENGTH p *)
(* Proof:
      stepsOf (poly_turnM p)
    = if (p = []) then 1 else 2 + stepsOf (poly_lastM p) + stepsOf(poly_frontM p)
                                                     by poly_turnM_steps_thm
   <= 2 + stepsOf (poly_lastM p) + stepsOf(poly_frontM p)
   <= 2 + (1 + 4 * LENGTH p) + (1 + 5 * LENGTH p)    by poly_lastM_steps_upper, poly_frontM_steps_upper
    = 4 + 9 * LENGTH p
*)
val poly_turnM_steps_upper = store_thm(
  "poly_turnM_steps_upper",
  ``!p. stepsOf (poly_turnM p) <= 4 + 9 * LENGTH p``,
  rpt strip_tac >>
  assume_tac poly_turnM_steps_thm >>
  last_x_assum (qspec_then `p` strip_assume_tac) >>
  (Cases_on `p = []` >> fs[]) >>
  `stepsOf (poly_lastM p) <= 1 + 4 * LENGTH p` by rw[poly_lastM_steps_upper] >>
  `stepsOf (poly_frontM p) <= 1 + 5 * LENGTH p` by rw[poly_frontM_steps_upper] >>
  decide_tac);

(* Theorem: (LENGTH p = k) ==> stepsOf (poly_turnM p) <= 13 * MAX 1 k *)
(* Proof:
      stepsOf (poly_turnM p)
   <= 4 + 9 * k               by poly_turnM_steps_upper
   <= (4 + 9) * (MAX 1 k)     by MAX_DEF
    = 13 * MAX 1 k
*)
val poly_turnM_steps_bound = store_thm(
  "poly_turnM_steps_bound",
  ``!p k. (LENGTH p = k) ==> stepsOf (poly_turnM p) <= 13 * MAX 1 k``,
  rpt strip_tac >>
  `stepsOf (poly_turnM p) <= 4 + 9 * k` by rw[poly_turnM_steps_upper] >>
  qabbrev_tac `m = MAX 1 k` >>
  `1 <= m /\ k <= m` by rw[Abbr`m`] >>
  decide_tac);

(* Theorem: Weak (ZN n) p ==> Weak (ZN n) (valueOf (poly_turnM p)) *)
(* Proof:
     Weak (ZN n) (valueOf (poly_turnM p))
   = Weak (ZN n) (turn p)                by poly_turnM_value
   = T                                   by weak_turn, Weak (ZN n) p
*)
val poly_turnM_weak = store_thm(
  "poly_turnM_weak",
  ``!n p. Weak (ZN n) p ==> Weak (ZN n) (valueOf (poly_turnM p))``,
  rw[weak_turn]);

(* Theorem: LENGTH (valueOf (poly_turnM p)) = LENGTH p *)
(* Proof:
     LENGTH (valueOf (poly_turnM p))
   = LENGTH (turn p)                   by poly_turnM_value
   = LENGTH p                          by turn_length
*)
val poly_turnM_length = store_thm(
  "poly_turnM_length",
  ``!p. LENGTH (valueOf (poly_turnM p)) = LENGTH p``,
  rw[turn_length]);

(* ------------------------------------------------------------------------- *)
(* Exact number of steps                                                     *)
(* ------------------------------------------------------------------------- *)

(*
EVAL ``MAP (\n. stepsOf (poly_lastM [1 .. n])) [0 .. 10]``;
= [1; 4; 8; 12; 16; 20; 24; 28; 32; 36; 40]
EVAL ``MAP (\n. stepsOf (poly_frontM [1 .. n])) [0 .. 10]``;
= [1; 4; 9; 14; 19; 24; 29; 34; 39; 44; 49]
*)

(* Theorem: stepsOf (poly_lastM p) = if (p = []) then 1 else 4 * LENGTH p *)
(* Proof:
   By induction on p.
   Base: stepsOf (poly_lastM []) = if [] = [] then 1 else 4 * LENGTH []
         LHS = stepsOf (poly_lastM []) = 1    by poly_lastM_steps_thm
             = RHS
   Step: stepsOf (poly_lastM p) = if (p = []) then 1 else 4 * LENGTH p ==>
         !h. stepsOf (poly_lastM (h::p)) = if h::(p = []) then 1 else 4 * LENGTH (h::p)
         Note h::(p = []) is false.
           stepsOf (poly_lastM (h::p))
         = 4 + if TL (h::p) = [] then 0 else stepsOf (poly_lastM (TL (h::p)))
                                             by poly_lastM_steps_thm
         = 4 + if (p = []) then 0 else stepsOf (poly_lastM p)
         = 4 + if (p = []) then 0 else 4 * LENGTH p
                                             by induction hypothesis
         = 4 + if (p = []) then 4 * LENGTH p else 4 * LENGTH p
                                             by LENGTH_NIL
         = 4 + 4 * LENGTH p
         = 4 * LENGTH (h::p)                 by LENGTH
*)
val poly_lastM_steps_eqn = store_thm(
  "poly_lastM_steps_eqn",
  ``!p. stepsOf (poly_lastM p) = if (p = []) then 1 else 4 * LENGTH p``,
  (Induct >> rw[Once poly_lastM_steps_thm]));

(* Theorem: stepsOf (poly_frontM p) = if (p = []) then 1 else (5 * LENGTH p - 1) *)
(* Proof:
   By induction on p.
   Base: stepsOf (poly_frontM []) = if [] = [] then 1 else 5 * LENGTH [] - 1
         LHS = stepsOf (poly_frontM []) = 1    by poly_frontM_steps_thm
             = RHS
   Step: stepsOf (poly_frontM p) = if (p = []) then 1 else 5 * LENGTH p - 1 ==>
         !h. stepsOf (poly_frontM (h::p)) = if h::(p = []) then 1 else 5 * LENGTH (h::p) - 1
         Note h::(p = []) is false.
           stepsOf (poly_frontM (h::p))
         = 4 + (if TL (h::p) = [] then 0 else 1) +
                if TL (h::p) = [] then 0 else stepsOf (poly_frontM (TL (h::p)))
                                               by poly_frontM_steps_thm
         = 4 + (if (p = []) then 0 else 1) +
                if (p = []) then 0 else stepsOf (poly_frontM p)
         = 4 + (if (p = []) then 0 else 1) +
                if (p = []) then 0 else (5 * LENGTH p - 1)
                                               by induction hypothesis
         = 4 + (if (p = []) then 5 * LENGTH p else 1) +
                if (p = []) then 5 * LENGTH p else (5 * LENGTH p - 1)
                                               by LENGTH_NIL
         = 4 + if (p = []) then 5 * LENGTH p else 5 * LENGTH p
         = 4 + 5 * LENGTH p
         = 5 * LENGTH (h::p) - 1               by LENGTH
*)
val poly_frontM_steps_eqn = store_thm(
  "poly_frontM_steps_eqn",
  ``!p. stepsOf (poly_frontM p) = if (p = []) then 1 else (5 * LENGTH p - 1)``,
  Induct >-
  rw[Once poly_frontM_steps_thm] >>
  rw[Once poly_frontM_steps_thm] >>
  `LENGTH p <> 0` by rw[LENGTH_NIL] >>
  decide_tac);

(* Theorem: stepsOf (poly_turnM p) = if (p = []) then 1 else (1 + 9 * LENGTH p) *)
(* Proof:
     stepsOf (poly_turnM p)
   = if (p = []) then 1 else 2 + stepsOf (poly_lastM p) + stepsOf (poly_frontM p)
                                                  by poly_turnM_steps_thm
   = if (p = []) then 1 else 2 +
     (if (p = []) then 1 else 4 * LENGTH p) +     by poly_lastM_steps_eqn
     (if (p = []) then 1 else 5 * LENGTH p - 1)   by poly_frontM_steps_eqn
   = if (p = []) then 1 else (2 + 4 * LENGTH p + 5 * LENGTH p - 1)
   = if (p = []) then 1 else (1 + 9 * LENGTH p)
*)
val poly_turnM_steps_eqn = store_thm(
  "poly_turnM_steps_eqn",
  ``!p. stepsOf (poly_turnM p) = if (p = []) then 1 else (1 + 9 * LENGTH p)``,
  rw[poly_turnM_steps_thm, poly_lastM_steps_eqn, poly_frontM_steps_eqn] >>
  `LENGTH p <> 0` by rw[LENGTH_NIL] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)

(* Multiply polynomials p q, both of length k, in (MOD (unity k)) *)
(* > poly_slide_def;
|- (!r p1 p2. poly_slide r p1 p2 [] = p1) /\
    !r p1 p2 h t. poly_slide r p1 p2 (h::t) = poly_slide r (h o p2 || p1) (turn p2) t
> unity_mod_mult_def
|- !r p q. unity_mod_mult r p q = poly_slide r |0| p q
*)

(* Pseudocode:
   Given modulus n, and polynomials p and q, compute p o q (mod n).
   list_mult p q:
      if p = [], return []      // [] o q = []
      if q = [], return []      // p o [] = []
      h <- head q               // get head of q
      t <- tail q               // get tail of q
      p1 <- list_cmult h p             // use head for list_cmult with p
      p2 <- list_mult (list_turn p) t  // use tail for list_mult with (turn p)
      return list_add p1 p2            // add the results, pair-wise
*)

Definition poly_multM_def:
  poly_multM n p q =
      do
        q0 <- nullM q;
        if q0 then return []
        else do
               h <- headM q;
               t <- tailM q;
               p1 <- poly_cmultM n h p;
               r <- poly_turnM p;
               p2 <- poly_multM n r t;
               poly_addM n p1 p2;
             od
      od
Termination WF_REL_TAC `measure (λ(n,p,q). LENGTH q)` >> simp[LENGTH_TL_LT]
End
(* Note: the final poly_addM n p1 p2 can also be poly_addM n p2 p1, as addition is commutative.
   However, the commutative property depends on Ring (ZN n) and weak polynomials.
   To avoid this complication, use of poly_addM n p1 p2 fits unity_mod_mult_cons. *)

(*
> EVAL ``poly_multM 10 [1;1;0;0;0;0;0] [1;1;0;0;0;0;0]``; = ([1; 2; 1; 0; 0; 0; 0],Count 1440): thm
> EVAL ``poly_multM 10 [1;1;0;0;0;0;0] [1;2;1;0;0;0;0]``; = ([1; 3; 3; 1; 0; 0; 0],Count 1471): thm
*)

(*

> EVAL ``poly_slide (ZN 10) [6] [1;2] [4;5]``; = [0; 3]: thm
> EVAL ``weak_add (ZN 10) [6] (poly_slide (ZN 10) [] [1;2] [4;5])``; = [0; 3]: thm
> EVAL ``weak_add (ZN 10) [6] (poly_slide (ZN 10) [7;8] [1;2] [4;5])``; = [7; 1]: thm
> EVAL ``poly_slide (ZN 10) (weak_add (ZN 10) [6] [7;8]) [1;2] [4;5]``; = [7; 1]: thm

Thus: poly_slide r (t1 || t2) p q = t1 || poly_slide r t2 p q

Conceptually this is simple: t1 || t2 is just the accumulator of partial result.
Indeed, poly_slide r |0| p q is supposed to do weak_mult of p and q,
and poly_slide r t p q is just weak_add t to this result, or t || poly_slide r |0| p q.

*)

(*
> unity_mod_mult_cons |> ISPEC ``(ZN n)`` |> SIMP_RULE bool_ss [ZN_property];
val it = |- Ring (ZN n) ==> !p h t. Weak (ZN n) p /\ Weak (ZN n) (h::t) ==>
    unity_mod_mult (ZN n) p (h::t) =
          weak_add (ZN n) (weak_cmult (ZN n) h p) (unity_mod_mult (ZN n) (turn p) t): thm
*)

(* Theorem: 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q ==>
            (valueOf (poly_multM n p q) = unity_mod_mult (ZN n) p q) *)
(* Proof:
   By induction from poly_multM_def.
   If q = [],
        valueOf (poly_multM n p [])
      = []                            by poly_multM_def
      = unity_mod_mult (ZN n) p []    by unity_mod_mult_zero
   Otherwise, p <> [] and q <> [].
      Let q = h::t
        valueOf (poly_multM n p (h::t))
      = (h o p || valueOf (poly_multM n (turn p) t)   by poly_multM_def
      = (h o p || unity_mod_mult (ZN n) (turn p) t)   by induction hypothesis
      = unity_mod_mult (ZN n) p (h::t)                by unity_mod_mult_cons
*)
val poly_multM_value = store_thm(
  "poly_multM_value[simp]",
  ``!n p q. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q ==>
       (valueOf (poly_multM n p q) = unity_mod_mult (ZN n) p q)``,
  ho_match_mp_tac (theorem "poly_multM_ind") >>
  rw[] >>
  rw[Once poly_multM_def] >-
  metis_tac[unity_mod_mult_zero, poly_zero] >>
  (Cases_on `q` >> rw[ZN_property]) >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `Weak (ZN n) t` by metis_tac[weak_cons] >>
  rw[unity_mod_mult_cons, weak_turn]);

(* Theorem: 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q /\ q <> [] /\ (LENGTH p = k) ==>
       (valueOf (poly_multM n p q) = p *z q) *)
(* Proof: by poly_multM_value, ZN_poly_mult_alt *)
val poly_multM_value_thm = store_thm(
  "poly_multM_value_thm",
  ``!n p q k. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q /\ q <> [] /\ (LENGTH p = k) ==>
       (valueOf (poly_multM n p q) = p *z q)``,
  metis_tac[ZN_poly_mult_alt, poly_multM_value]);

(* Above q <> [] is the minimal requirement. Next with 0 < k is symmetric. *)

(* Theorem: 0 < n /\ 0 < k /\ Weak (ZN n) p /\ Weak (ZN n) q /\
            (LENGTH p = k) /\ (LENGTH q = k) ==> (valueOf (poly_multM n p q) = p *z q) *)
(* Proof: by poly_multM_value_thm, LENGTH_NIL *)
val poly_multM_value_alt = store_thm(
  "poly_multM_value_alt",
  ``!n p q k. 0 < n /\ 0 < k /\ Weak (ZN n) p /\ Weak (ZN n) q /\
             (LENGTH p = k) /\ (LENGTH q = k) ==> (valueOf (poly_multM n p q) = p *z q)``,
  metis_tac[poly_multM_value_thm, LENGTH_NIL, NOT_ZERO]);

(* Theorem: 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q ==>
           Weak (ZN n) (valueOf (poly_multM n p q)) *)
(* Proof:
   Note Ring (ZN n)                             by 0 < n
     Weak (ZN n) (valueOf (poly_multM n p q))
   = Weak (ZN n) (unity_mod_mult (ZN n) p q))   by poly_multM_value
   = T                                          by unity_mod_mult_weak, Ring (ZN n)
*)
val poly_multM_weak = store_thm(
  "poly_multM_weak",
  ``!n p q. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q ==>
           Weak (ZN n) (valueOf (poly_multM n p q))``,
  rw[unity_mod_mult_weak, ZN_ring]);

(* Theorem: 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q ==>
            LENGTH (valueOf (poly_multM n p q)) = if q = [] then 0 else LENGTH p *)
(* Proof:
     LENGTH (valueOf (poly_multM n p q))
   = LENGTH (unity_mod_mult (ZN n) p q))   by poly_multM_value
   = if q = [] then 0 else LENGTH p        by unity_mod_mult_length
*)
val poly_multM_length = store_thm(
  "poly_multM_length",
  ``!n p q. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q ==>
            LENGTH (valueOf (poly_multM n p q)) = if q = [] then 0 else LENGTH p``,
  rw[unity_mod_mult_length]);

(* Theorem: 0 < n /\ Weak (ZN n) p ==> (valueOf (poly_multM n p []) = []) *)
(* Proof:
   Note Weak (ZN n) []                             by weak_zero
    and LENGTH (valueOf (poly_multM n p [])) = 0   by poly_multM_length
   Thus valueOf (poly_multM n p []) = []           by LENGTH_NIL
*)
val poly_multM_nil = store_thm(
  "poly_multM_nil",
  ``!n p. 0 < n /\ Weak (ZN n) p ==> (valueOf (poly_multM n p []) = [])``,
  rpt strip_tac >>
  `Weak (ZN n) []` by rw[] >>
  metis_tac[poly_multM_length, LENGTH_NIL]);

(* Theorem: stepsOf (poly_multM n p q) =
            if q = [] then 1
            else 3 + stepsOf (poly_turnM p) +
                 stepsOf (poly_cmultM n (HD q) p) +
                 stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p) (valueOf (poly_multM n (turn p) (TL q)))) +
                 stepsOf (poly_multM n (turn p) (TL q)) *)
(* Proof:
     stepsOf (poly_multM n p q)
   = stepsOf (nullM q) + if (q = []) then 0
     else stepsOf (headM q) + stepsOf (tailM q) +
          stepsOf (poly_turnM p) + stepsOf (poly_multM n (turn p) (TL q)) +
          stepsOf (poly_cmultM n (HD q) p) +
          stepsOf (poly_addM n (HD q o p) (unity_mod_mult (ZN n) (turn p) (TL q)))
                                                   by poly_multM_def
   = 1 + if q = [] then 0
     else 1 + 1 +
          stepsOf (poly_turnM p) + stepsOf (poly_multM n (turn p) (TL q)) +
          stepsOf (poly_cmultM n (HD q) p) +
          stepsOf (poly_addM n (weak_cult (ZN n) (HD q) p) ((turn p) * (TL q)))
   = if q = [] then 1 else 3 +
          stepsOf (poly_turnM p) +
          stepsOf (poly_cmultM n (HD q) p) +
          stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p) (unity_mod_mult (ZN n) (turn p) (TL q))) +
          stepsOf (poly_multM n (turn p) (TL q))
   from Weak (ZN n) (turn p)         by weak_turn
    and Weak (ZN n) (TL q)           by weak_cons
   However, this requires knowing poly_multM_value.
   For an unconditional expression,
   = if q = [] then 1 else 3 +
          stepsOf (poly_turnM p) +
          stepsOf (poly_cmultM n (HD q) p) +
          stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p) (valueOf (poly_multM n (turn p) (TL q)))) +
          stepsOf (poly_multM n (turn p) (TL q))
*)
val poly_multM_steps_thm = store_thm(
  "poly_multM_steps_thm",
  ``!n p q. stepsOf (poly_multM n p q) =
            if q = [] then 1
            else 3 + stepsOf (poly_turnM p) +
                 stepsOf (poly_cmultM n (HD q) p) +
                 stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p) (valueOf (poly_multM n (turn p) (TL q)))) +
                 stepsOf (poly_multM n (turn p) (TL q))``,
  ho_match_mp_tac (theorem "poly_multM_ind") >>
  (rw[] >> rw[Once poly_multM_def, weak_turn]));
(* The unconditional from is more useful. *)

(* Theorem: stepsOf (poly_multM n p []) = 1 *)
(* Proof: by poly_multM_steps_thm *)
val poly_multM_steps_nil = store_thm(
  "poly_multM_steps_nil",
  ``!n p. stepsOf (poly_multM n p []) = 1``,
  rw[Once poly_multM_steps_thm]);

(* Theorem: 0 < n /\ Weak (ZN n) p ==>
           (stepsOf (poly_multM n p [c]) =
              6 + stepsOf (poly_turnM p) + stepsOf (poly_cmultM n c p)) *)
(* Proof:
     stepsOf (poly_multM n p [c])
   = 3 + stepsOf (poly_turnM p) +
         stepsOf (poly_cmultM n c p) +
         stepsOf (poly_addM n (weak_cmult (ZN n) c p) (valueOf (poly_multM n (turn p) []))) +
         stepsOf (poly_multM n (turn p) [])        by poly_multM_steps_thm
   = 3 + stepsOf (poly_turnM p) +
         stepsOf (poly_cmultM n c p) +
         stepsOf (poly_addM n (weak_cmult (ZN n) c p) (unity_mod_mult (ZN n) (turn p) [])) +
         1                                         by poly_multM_steps_thm
   = 3 + stepsOf (poly_turnM p) +
         stepsOf (poly_cmultM n c p) +
         stepsOf (poly_addM n (weak_cmult (ZN n) c p) []) +
         1                                         by unity_mod_mult_length, LENGTH_NIL
   = 3 + stepsOf (poly_turnM p) +
         stepsOf (poly_cmultM n c p) +
         2 + 1                                     by poly_addM_steps_thm
   = 6 + stepsOf (poly_turnM p) + stepsOf (poly_cmultM n c p)
*)
val poly_multM_steps_sing_thm = store_thm(
  "poly_multM_steps_sing_thm",
  ``!n p c. 0 < n /\ Weak (ZN n) p ==>
           (stepsOf (poly_multM n p [c]) =
              6 + stepsOf (poly_turnM p) + stepsOf (poly_cmultM n c p))``,
  rw[Once poly_multM_steps_thm] >>
  rw[Once poly_multM_steps_thm] >>
  qabbrev_tac `q = valueOf (poly_multM n (turn p) [])` >>
  `q = []` by rw[poly_multM_nil, weak_turn, Abbr`q`] >>
  `stepsOf (poly_addM n (weak_cmult (ZN n) c p) q) = 2` by rw[Once poly_addM_steps_thm] >>
  decide_tac);

(* Theorem: 0 < n /\ Weak (ZN n) p ==>
           stepsOf (poly_multM n p [c]) <=
           10 + 9 * k + 8 * MAX 1 k * size (MAX c n) * size n *)
(* Proof:
      stepsOf (poly_multM n p [c])
    = 6 + stepsOf (poly_turnM p) + stepsOf (poly_cmultM n c p)  by poly_multM_steps_sing_thm
   <= 6 + (4 + 9 * k) + (8 * MAX 1 k * size (MAX c n) * size n)   by poly_turnM_steps_upper, poly_cmultM_steps_bound
    = 10 + 9 * k + 8 * MAX 1 k * size (MAX c n) * size n
*)
val poly_multM_steps_sing_upper = store_thm(
  "poly_multM_steps_sing_upper",
  ``!n p c k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
           stepsOf (poly_multM n p [c]) <= 10 + 9 * k + 8 * MAX 1 k * size (MAX c n) * size n``,
  rpt strip_tac >>
  imp_res_tac poly_multM_steps_sing_thm >>
  first_x_assum (qspec_then `c` strip_assume_tac) >>
  `stepsOf (poly_turnM p) <= 4 + 9 * k` by rw[poly_turnM_steps_upper] >>
  `stepsOf (poly_cmultM n c p) <= 8 * MAX 1 k * size (MAX c n) * size n` by rw[poly_cmultM_steps_bound] >>
  decide_tac);

(* Theorem: 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
            stepsOf (poly_multM n p [c]) <= 27 * MAX 1 k * size (MAX c n) * size n *)
(* Proof:
   Let k = LENGTH p.
      stepsOf (poly_multM n p [c])
   <= 10 + 9 * k + 8 * MAX 1 k * size (MAX c n) * size n    by poly_multM_steps_sing_upper
   <= (10 + 9 + 8) * MAX 1 k * size (MAX c n) * size n      by dominant term
    = 27 * MAX 1 k * size (MAX c n) * size n
*)
val poly_multM_steps_sing_bound = store_thm(
  "poly_multM_steps_sing_bound",
  ``!n p c k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
             stepsOf (poly_multM n p [c]) <= 27 * MAX 1 k * size (MAX c n) * size n``,
  rpt strip_tac >>
  imp_res_tac poly_multM_steps_sing_upper >>
  first_x_assum (qspec_then `c` strip_assume_tac) >>
  qabbrev_tac `m = MAX 1 k` >>
  qabbrev_tac `d = MAX c n` >>
  `0 < m * size d * size n` by rw[MULT_POS, Abbr`m`] >>
  `k <= m` by rw[Abbr`m`] >>
  `m <= m * (size d * size n)` by rw[MULT_POS] >>
  decide_tac);


(* Theorem alias *)
val poly_multM_steps_by_list_loop = save_thm("poly_multM_steps_by_list_loop", poly_multM_steps_thm);

(*
This puts poly_multM_steps in the category: list loop with body cover and turn transform.
   poly_multM_steps_by_list_loop:
        !p q. loop p q = if q = [] then quit p else body p q + loop (turn p) (TL q)
suitable for: loop2_list_turn_head_count_cover_le
*)

(* First, work out a cover for the body. *)

(* Theorem: let body p q = 3 + stepsOf (poly_turnM p) +
                      stepsOf (poly_cmultM n (HD q) p) +
                      stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p) (valueOf (poly_multM n (turn p) (TL q))))
        in !p q. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q /\ q <> [] ==>
                 body p q <= 10 + (LENGTH p) * (20 + 2 * size n + 4 * size n ** 2) *)
(* Proof:
   Weak (ZN n) p, k = LENGTH p,
   Let body = (\p q. 3 + stepsOf (poly_turnM p) +
              stepsOf (poly_cmultM n (HD q) p) +
              stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p) (valueOf (poly_multM n (turn p) (TL q)))))
      body p q
    = 3 + stepsOf (poly_turnM p)
        + stepsOf (poly_cmultM n (HD q) p)
        + stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p) (valueOf (poly_multM n (turn p) (TL q)))))
   <= 3 + (4 + 9 * k)                                                    by poly_turnM_steps_upper
        + (1 + 4 * k + 2 * k * size (HD q) * size n + k * size n ** 2)   by poly_cmultM_steps_upper
        + (2 + 7 * k + 2 * k * size n + k * size n ** 2)   by poly_addM_steps_upper
   last one assumes:
        TL q <> [], otherwise only gives 2, which is ok       by poly_addM_steps_thm
        LENGTH (weak_cmult (ZN n) (HD q) p) = k               by weak_cmult_length
        LENGTH (valueOf (poly_multM n (turn p) (TL q))) = k
                unity_mod_mult (ZN n) (turn p) (TL q)         by unity_mod_mult_length, turn_length, TL q <> []
        Weak (ZN n) (weak_cmult (ZN n) (HD q) p)              by weak_cmult_weak, 0 < n, Ring (ZN n), (HD q) IN (ZN n).carrier
        Weak (ZN n) (valueOf (poly_multM n (turn p) (TL q)))  by unity_mod_mult_weak
    = 10 + 20 * k + 2 * k * size n * (1 + size (HD q)) + 2 * k * size n ** 2
   <= 10 + 20 * k + 2 * k * size n * (1 + size n) + 2 * k * size n ** 2    by Weak (ZN n) q, size_monotone_lt
    = 10 + k * (20 + 2 * size n * (1 + size n) + 2 * size n ** 2)
    = 10 + k * (20 + 2 * size n + 4 * size n ** 2)
   For a fixed n, this is a function of k = LENGTH p!
*)
val poly_multM_steps_body_upper = store_thm(
  "poly_multM_steps_body_upper",
  ``!n. let body p q = 3 + stepsOf (poly_turnM p) +
                      stepsOf (poly_cmultM n (HD q) p) +
                      stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p) (valueOf (poly_multM n (turn p) (TL q))))
        in !p q. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q /\ q <> [] ==>
                 body p q <= 10 + (LENGTH p) * (20 + 2 * size n + 4 * size n ** 2)``,
  rw_tac std_ss[] >>
  qabbrev_tac `k = LENGTH p` >>
  `Weak (ZN n) (turn p)` by rw[weak_turn] >>
  `Weak (ZN n) (TL q)` by metis_tac[weak_cons, TL, list_CASES] >>
  `valueOf (poly_multM n (turn p) (TL q)) = unity_mod_mult (ZN n) (turn p) (TL q)` by rw[poly_multM_value] >>
  `body p q = 3 + stepsOf (poly_turnM p)
        + stepsOf (poly_cmultM n (HD q) p)
        + stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p) (unity_mod_mult (ZN n) (turn p) (TL q)))` by metis_tac[] >>
  qabbrev_tac `ct = stepsOf (poly_turnM p)` >>
  qabbrev_tac `cc = stepsOf (poly_cmultM n (HD q) p)` >>
  qabbrev_tac `ca = stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p) (unity_mod_mult (ZN n) (turn p) (TL q)))` >>
  `ct <= 4 + 9 * k` by rw[poly_turnM_steps_upper, Abbr`ct`, Abbr`k`] >>
  `cc <= 1 + 4 * k + 3 * k * size n ** 2` by
  (`cc <= 1 + 4 * k + 2 * k * size (HD q) * size n + k * size n ** 2` by rw[poly_cmultM_steps_upper, Abbr`cc`, Abbr`k`] >>
  `EVERY (\j. j < n) q` by rw[GSYM ZN_weak] >>
  `HD q = EL 0 q` by rw[] >>
  `0 < LENGTH q` by metis_tac[LENGTH_NIL, NOT_ZERO] >>
  qabbrev_tac `P = \j. j < n` >>
  `!j. P j = (j < n)` by rw[Abbr`P`] >>
  `HD q < n` by metis_tac[EVERY_EL] >>
  `size (HD q) <= size n` by rw[size_monotone_lt] >>
  `k * size (HD q) * size n <= k * size n * size n` by rw[] >>
  `k * size n * size n = k * size n ** 2` by rw[] >>
  decide_tac) >>
  `ca <= 2 + 7 * k + 2 * k * size n + k * size n ** 2` by
    (qabbrev_tac `p1 = weak_cmult (ZN n) (HD q) p` >>
  qabbrev_tac `q1 = unity_mod_mult (ZN n) (turn p) (TL q)` >>
  Cases_on `TL q = []` >| [
    `q1 = []` by metis_tac[unity_mod_mult_zero, poly_zero] >>
    `ca = 2` by metis_tac[poly_addM_steps_thm] >>
    decide_tac,
    `LENGTH p1 = k` by metis_tac[weak_cmult_length] >>
    `LENGTH q1 = k` by metis_tac[unity_mod_mult_length, turn_length] >>
    `Ring (ZN n)` by rw[ZN_ring] >>
    `(HD q) IN (ZN n).carrier` by metis_tac[weak_cons, HD, list_CASES] >>
    `Weak (ZN n) p1` by rw[weak_cmult_weak, Abbr`p1`] >>
    `Weak (ZN n) q1` by metis_tac[unity_mod_mult_weak] >>
    metis_tac[poly_addM_steps_upper]
  ]) >>
  decide_tac);

(* Theorem: let body p q = 3 + stepsOf (poly_turnM p) +
                      stepsOf (poly_cmultM n (HD q) p) +
                      stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p) (valueOf (poly_multM n (turn p) (TL q))))
     in !p q k. 0 < n /\ (LENGTH p = k) /\ (LENGTH q = k) /\ Weak (ZN n) p /\ Weak (ZN n) q ==>
        !j. j < k ==> body (turn_exp p j) (DROP j q) <= 10 + k * (20 + 2 * size n + 4 * size n ** 2) *)
(* Proof:
   Let p1 = turn_exp p j,
       q1 = DROP j q.

   To apply poly_multM_steps_body_upper, require:
      0 < n /\ Weak (ZN n) p1 /\ Weak (ZN n) q1 /\ q1 <> [] ==>
      body p1 q1 <= 10 + (LENGTH p1) * (20 + 2 * size n + 4 * size n ** 2)

   Note Weak (ZN n) p1                 by weak_turn_exp
    and Weak (ZN n) q1                 by weak_drop
   Also q1 <> []                       by DROP_EQ_NIL, j < k = LENGTH q
    and LENGTH p1 = k                  by turn_exp_length
   The result follows                  by poly_multM_steps_body_upper
*)
val poly_multM_steps_body_cover = store_thm(
  "poly_multM_steps_body_cover",
  ``!n. let body p q = 3 + stepsOf (poly_turnM p) +
                      stepsOf (poly_cmultM n (HD q) p) +
                      stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p) (valueOf (poly_multM n (turn p) (TL q))))
     in !p q k. 0 < n /\ (LENGTH p = k) /\ (LENGTH q = k) /\ Weak (ZN n) p /\ Weak (ZN n) q ==>
        !j. j < k ==> body (turn_exp p j) (DROP j q) <= 10 + k * (20 + 2 * size n + 4 * size n ** 2)``,
  rw_tac std_ss[] >>
  qabbrev_tac `k = LENGTH p` >>
  qabbrev_tac `p1 = turn_exp p j` >>
  qabbrev_tac `q1 = DROP j q` >>
  `Weak (ZN n) p1` by rw[weak_turn_exp, Abbr`p1`] >>
  `Weak (ZN n) q1` by rw[weak_drop, Abbr`q1`] >>
  `q1 <> []` by rw[DROP_EQ_NIL, Abbr`q1`] >>
  `LENGTH p1 = k` by rw[turn_exp_length, Abbr`p1`] >>
  metis_tac[poly_multM_steps_body_upper]);

(* Theorem: 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q /\ (LENGTH p = k) /\ (LENGTH q = k) ==>
            stepsOf (poly_multM n p q) <=
            1 + 10 * k + 20 * k ** 2 + 2 * k ** 2 * size n + 4 * k ** 2 * size n ** 2 *)
(* Proof:
   Let quit = (\p. 1),
       body = (\p q. 3 + stepsOf (poly_turnM p) + stepsOf (poly_cmultM n (HD q) p) +
              stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p) (valueOf (poly_multM n (turn p) (TL q))))),
       loop = (\p q. stepsOf (poly_multM n p q)).
   Then !p q. loop p q = if (q = []) then quit p else body p q + loop (turn p) (TL q)
                                        by poly_multM_steps_thm
   Let c = 10 + k * (20 + 2 * (size n) + 4 * size n ** 2.
   Then !j. j < k ==> body (turn_exp p j) (DROP j q) <= (K c) j
                                        by poly_multM_steps_body_cover
    and MONO (K c)                      by constant function
        loop p q
     <= quit (turn_exp x k) + k * (K c) k     by loop2_list_turn_head_count_cover_le
      = 1 + k * c                             by applicaiton of (K c), quit
      = 1 + k * (10 + k * (20 + 2 * (size n) + 4 * size n ** 2))
      = 1 + 10 * k + k * k * (20 + 2 * (size n) + 4 * size n ** 2)
      = 1 + 10 * k + 20 * k ** 2 + 2 * k ** 2 * size n + 4 * k ** 2 * size n ** 2
*)
val poly_multM_steps_upper = store_thm(
  "poly_multM_steps_upper",
  ``!n p q k. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q /\ (LENGTH p = k) /\ (LENGTH q = k) ==>
             stepsOf (poly_multM n p q) <=
             1 + 10 * k + 20 * k ** 2 + 2 * k ** 2 * size n + 4 * k ** 2 * size n ** 2``,
  rpt strip_tac >>
  qabbrev_tac `quit = \p:num list. 1` >>
  qabbrev_tac `body = \p q. 3 + stepsOf (poly_turnM p) + stepsOf (poly_cmultM n (HD q) p) +
              stepsOf (poly_addM n (weak_cmult (ZN n) (HD q) p) (valueOf (poly_multM n (turn p) (TL q))))` >>
  qabbrev_tac `loop = \p q. stepsOf (poly_multM n p q)` >>
  `loop p q <= 1 + 10 * k + 20 * k ** 2 + 2 * k ** 2 * size n + 4 * k ** 2 * size n ** 2` suffices_by rw[Abbr`loop`] >>
  `!x y. loop x y = if (y = []) then quit x else body x y + loop (turn x) (TL y)` by metis_tac[poly_multM_steps_thm] >>
  qabbrev_tac `c = 10 + k * (20 + 2 * (size n) + 4 * size n ** 2)` >>
  `!j. j < k ==> body (turn_exp p j) (DROP j q) <= (K c) j` by metis_tac[poly_multM_steps_body_cover, combinTheory.K_THM] >>
  `MONO (K c)` by rw[] >>
  imp_res_tac loop2_list_turn_head_count_cover_le >>
  `loop p q <= 1 + k * (K c) k` by metis_tac[] >>
  `1 + k * (K c) k = 1 + k * c` by rw[] >>
  `k * c = k * (10 + k * 20 + 2 * k * size n + 4 * k * size n ** 2)` by rw[Abbr`c`] >>
  `_ = 10 * k + 20 * (k * k) + 2 * (k * k) * size n + 4 * (k * k) * size n ** 2` by decide_tac >>
  `_ = 10 * k + 20 * (k ** 2) + 2 * (k ** 2) * size n + 4 * (k ** 2) * size n ** 2` by rw[] >>
  decide_tac);

(* Theorem: 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q /\ (LENGTH p = k) /\ (LENGTH q = k) ==>
            stepsOf (poly_multM n p q) <= 37 * (MAX 1 k) ** 2 * size n ** 2 *)
(* Proof:
      stepsOf (poly_multM n p q)
   <= 1 + 10 * k + 20 * k ** 2 + 2 * k ** 2 * size n + 4 * k ** 2 * size n ** 2
                                                       by poly_multM_steps_upper
   <= (1 + 10 + 20 + 2 + 4) * k ** 2 * size n ** 2     by dominant term
    = 37 * k ** 2 * size n ** 2
    Use (MAX 1 k) to cater for k = 0.
*)
val poly_multM_steps_bound = store_thm(
  "poly_multM_steps_bound",
  ``!n p q k. 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q /\ (LENGTH p = k) /\ (LENGTH q = k) ==>
             stepsOf (poly_multM n p q) <= 37 * (MAX 1 k) ** 2 * size n ** 2``,
  rpt strip_tac >>
  `stepsOf (poly_multM n p q) <=
    1 + 10 * k + 20 * k ** 2 + 2 * k ** 2 * size n + 4 * k ** 2 * size n ** 2` by rw[poly_multM_steps_upper] >>
  qabbrev_tac `m = MAX 1 k` >>
  qabbrev_tac `t = m ** 2 * size n ** 2` >>
  `stepsOf (poly_multM n p q) <= 37 * t` suffices_by rw[Abbr`t`] >>
  `1 <= m /\ k <= m` by rw[Abbr`m`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `k <= t` by
  (`m <= m * (m * size n ** 2)` by rw[MULT_POS] >>
  `m * (m * size n ** 2) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k ** 2 <= t` by
    (`k ** 2 <= m ** 2` by rw[] >>
  `m ** 2 <= m ** 2 * size n ** 2` by rw[MULT_POS] >>
  `m ** 2 * size n ** 2 = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k ** 2 * size n <= t` by
      (`k ** 2 * size n <= m ** 2 * size n` by rw[] >>
  `m ** 2 * size n <= m ** 2 * size n * size n` by rw[MULT_POS] >>
  `m ** 2 * size n * size n = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `k ** 2 * size n ** 2 <= t` by
        (`k ** 2 * size n ** 2 <= m ** 2 * size n ** 2` by rw[] >>
  `m ** 2 * size n ** 2 = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* Theorem: 0 < n /\ 0 < k /\ Weak (ZN n) p /\ Weak (ZN n) q /\
            (LENGTH p = k) /\ (LENGTH q = k) ==>
            stepsOf (poly_multM n p q) <= 37 * k ** 2 * size n ** 2 *)
(* Proof: by poly_multM_steps_bound, MAX_1_POS *)
val poly_multM_steps_bound_alt = store_thm(
  "poly_multM_steps_bound_alt",
  ``!n p q k. 0 < n /\ 0 < k /\ Weak (ZN n) p /\ Weak (ZN n) q /\
             (LENGTH p = k) /\ (LENGTH q = k) ==>
             stepsOf (poly_multM n p q) <= 37 * k ** 2 * size n ** 2``,
  metis_tac[poly_multM_steps_bound, MAX_1_POS]);

(* ------------------------------------------------------------------------- *)
(* Squaring of polynomial                                                    *)
(* ------------------------------------------------------------------------- *)

(* Squaring a polynomial p, of length k, in (MOD n, (unity k)). *)
val poly_sqM_def = Define`
    poly_sqM n p = poly_multM n p p
`;

(*
EVAL ``poly_sqM 10 [1;1;0;0;0;0;0]``; = ([1; 2; 1; 0; 0; 0; 0],Count 1448): thm
EVAL ``poly_sqM 10 [1;2;1;0;0;0;0]``; = ([1; 4; 6; 4; 1; 0; 0],Count 1541): thm
EVAL ``poly_sqM 10 [1;4;6;4;1;0;0]``; = ([9; 9; 8; 6; 0; 6; 8],Count 2168): thm
*)

(* Theorem: 0 < n /\ Weak (ZN n) p ==>
            (valueOf (poly_sqM n p) = unity_mod_sq (ZN n) p) *)
(* Proof:
     valueOf (poly_sqM n p)
   = valueOf (poly_multM n p p)    by poly_sqM_def
   = unity_mod_mult (ZN n) p p     by poly_multM_value
   = unity_mod_sq (ZN n) p         by unity_mod_sq_def
*)
val poly_sqM_value = store_thm(
  "poly_sqM_value[simp]",
  ``!n p. 0 < n /\ Weak (ZN n) p ==>
         (valueOf (poly_sqM n p) = unity_mod_sq (ZN n) p)``,
  rw[poly_sqM_def, unity_mod_sq_def]);

(* Theorem: 0 < n /\ Weak (ZN n) p /\ p <> [] /\ (LENGTH p = k) ==>
            (valueOf (poly_sqM n p) = sqz p) *)
(* Proof: by poly_sqM_value, ZN_poly_sq_alt *)
val poly_sqM_value_thm = store_thm(
  "poly_sqM_value_thm",
  ``!n p k. 0 < n /\ Weak (ZN n) p /\ p <> [] /\ (LENGTH p = k) ==>
           (valueOf (poly_sqM n p) = sqz p)``,
  metis_tac[poly_sqM_value, ZN_poly_sq_alt]);

(* Above p <> [] is the minimal requirement. Next with 0 < k is symmetric. *)

(* Theorem: 0 < n /\ 0 < k /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
           (valueOf (poly_sqM n p) = sqz p) *)
(* Proof: by poly_sqM_value_thm, LENGTH_NIL *)
val poly_sqM_value_alt = store_thm(
  "poly_sqM_value_alt",
  ``!n p k. 0 < n /\ 0 < k /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
           (valueOf (poly_sqM n p) = sqz p)``,
  metis_tac[poly_sqM_value_thm, LENGTH_NIL, NOT_ZERO]);

(* Theorem: 0 < n /\ Weak (ZN n) p ==> Weak (ZN n) (valueOf (poly_sqM n p)) *)
(* Proof:
   Note Ring (ZN n)                        by ZN_ring, 0 < n
     Weak (ZN n) (valueOf (poly_sqM n p))
   = Weak (ZN n) (unity_mod_sq (ZN n) p)   by poly_sqM_value
   = T                                     by unity_mod_sq_weak, Ring (ZN n)
*)
val poly_sqM_weak = store_thm(
  "poly_sqM_weak",
  ``!n p. 0 < n /\ Weak (ZN n) p ==> Weak (ZN n) (valueOf (poly_sqM n p))``,
  rw[unity_mod_sq_weak, ZN_ring]);

(* Theorem: 0 < n /\ Weak (ZN n) p ==> LENGTH (valueOf (poly_sqM n p)) = LENGTH p *)
(* Proof:
     LENGTH (valueOf (poly_sqM n p))
   = LENGTH (unity_mod_sq (ZN n) p)   by poly_sqM_value
   = LENGTH p                         by unity_mod_sq_length
*)
val poly_sqM_length = store_thm(
  "poly_sqM_length",
  ``!n p. 0 < n /\ Weak (ZN n) p ==> LENGTH (valueOf (poly_sqM n p)) = LENGTH p``,
  rw[unity_mod_sq_length]);

(* Theorem: 0 < n /\ Weak (ZN n) p ==>
           !k. Weak (ZN n) (FUNPOW (\p. valueOf (poly_sqM n p)) k p) *)
(* Proof:
   By induction on k.
   Let f = (\p. valueOf (poly_sqM n p)).
   Base: Weak (ZN n) (FUNPOW f 0 p)
       = Weak (ZN n) p                     by FUNPOW_0
       = T
   Step: Weak (ZN n) (FUNPOW f (SUC k) p)
       = Weak (ZN n) (f (FUNPOW f k p))    by FUNPOW_SUC
       = T                                 by poly_sqM_weak, induction hypothesis
*)
val poly_sqM_iterating_weak = store_thm(
  "poly_sqM_iterating_weak",
  ``!n p. 0 < n /\ Weak (ZN n) p ==>
        !k. Weak (ZN n) (FUNPOW (\p. valueOf (poly_sqM n p)) k p)``,
  ntac 3 strip_tac >>
  qabbrev_tac `f = \p. valueOf (poly_sqM n p)` >>
  Induct >-
  metis_tac[FUNPOW_0] >>
  metis_tac[FUNPOW_SUC, poly_sqM_weak]);

(* Theorem: 0 < n /\ Weak (ZN n) p ==>
           !k. LENGTH (FUNPOW (\p. valueOf (poly_sqM n p)) k p) = LENGTH p *)
(* Proof:
   By induction on k.
   Let f = (\p. valueOf (poly_sqM n p)).
   Base: LENGTH (FUNPOW f 0 p) = LENGTH p, true   by FUNPOW_0
   Step: LENGTH (FUNPOW f (SUC k) p)
       = LENGTH (f (FUNPOW f k p))    by FUNPOW_SUC
       = LENGTH p                     by poly_sqM_length, induction hypothesis
   since Weak (ZN n) (FUNPOW f k p)   by poly_sqM_iterating_weak
*)
val poly_sqM_iterating_length = store_thm(
  "poly_sqM_iterating_length",
  ``!n p. 0 < n /\ Weak (ZN n) p ==>
        !k. LENGTH (FUNPOW (\p. valueOf (poly_sqM n p)) k p) = LENGTH p``,
  ntac 3 strip_tac >>
  qabbrev_tac `f = \p. valueOf (poly_sqM n p)` >>
  Induct >-
  metis_tac[FUNPOW_0] >>
  `Weak (ZN n) (FUNPOW f k p)` by rw[poly_sqM_iterating_weak, Abbr`f`] >>
  metis_tac[FUNPOW_SUC, poly_sqM_length]);

(* Theorem: 0 < n /\ Weak (ZN n) p ==>
         stepsOf (poly_sqM n p) =
         if (p = []) then 1
         else 3 + stepsOf (poly_turnM p) +
              stepsOf (poly_cmultM n (HD p) p) +
              stepsOf (poly_addM n (weak_cmult (ZN n) (HD p) p)
                                   (unity_mod_mult (ZN n) (turn p) (TL p))) +
              stepsOf (poly_multM n (turn p) (TL p)) *)
(* Proof:
     stepsOf (poly_sqM n p)
   = stepsOf (poly_multM n p p)    by poly_sqM_def
   = if (p = []) then 1
     else 3 + stepsOf (poly_turnM p) + stepsOf (poly_cmultM n (HD p) p) +
              stepsOf (poly_addM n (weak_cmult (ZN n) (HD p) p)
                                   (valueOf (poly_multM n (turn p) (TL p)))) +
              stepsOf (poly_multM n (turn p) (TL p))   by poly_multM_steps_thm
   = if (p = []) then 1
     else 3 + stepsOf (poly_turnM p) + stepsOf (poly_cmultM n (HD p) p) +
              stepsOf (poly_addM n (weak_cmult (ZN n) (HD p) p)
                                   (unity_mod_mult (ZN n) (turn p) (TL p))) +
              stepsOf (poly_multM n (turn p) (TL p))   by poly_multM_value
*)
val poly_sqM_steps_thm = store_thm(
  "poly_sqM_steps_thm",
  ``!n p. 0 < n /\ Weak (ZN n) p ==>
         stepsOf (poly_sqM n p) =
         if (p = []) then 1
         else 3 + stepsOf (poly_turnM p) +
              stepsOf (poly_cmultM n (HD p) p) +
              stepsOf (poly_addM n (weak_cmult (ZN n) (HD p) p)
                                   (unity_mod_mult (ZN n) (turn p) (TL p))) +
              stepsOf (poly_multM n (turn p) (TL p))``,
  rw[poly_sqM_def, Once poly_multM_steps_thm] >>
  rw[poly_multM_value, weak_turn, weak_tail]);

(* Theorem: 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
      stepsOf (poly_sqM n p) <=
      1 + 10 * k + 20 * k ** 2 + 2 * (k ** 2) * size n + 4 * k ** 2 * size n ** 2 *)
(* Proof:
      stepsOf (poly_sqM n p)
    = stepsOf (poly_multM n p p)    by poly_sqM_def
   <= 1 + 10 * k + 20 * k ** 2 + 2 * (k ** 2) * size n + 4 * k ** 2 * size n ** 2
                                    by poly_multM_steps_upper
*)
val poly_sqM_steps_upper = store_thm(
  "poly_sqM_steps_upper",
  ``!n p k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
      stepsOf (poly_sqM n p) <=
      1 + 10 * k + 20 * k ** 2 + 2 * (k ** 2) * size n + 4 * k ** 2 * size n ** 2``,
  metis_tac[poly_sqM_def, poly_multM_steps_upper]);

(* Theorem: 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
            stepsOf (poly_sqM n p) <= 37 * MAX 1 k ** 2 * size n ** 2 *)
(* Proof:
      stepsOf (poly_sqM n p)
    = stepsOf (poly_multM n p p)       by poly_sqM_def
   <= 37 * MAX 1 k ** 2 * size n ** 2  by poly_multM_steps_bound
*)
val poly_sqM_steps_bound = store_thm(
  "poly_sqM_steps_bound",
  ``!n p k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
      stepsOf (poly_sqM n p) <= 37 * MAX 1 k ** 2 * size n ** 2``,
  metis_tac[poly_sqM_def, poly_multM_steps_bound]);

(* Theorem: 0 < n /\ 0 < k /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
            stepsOf (poly_sqM n p) <= 37 * k ** 2 * size n ** 2 *)
(* Proof: by poly_sqM_steps_bound, MAX_1_POS *)
val poly_sqM_steps_bound_alt = store_thm(
  "poly_sqM_steps_bound_alt",
  ``!n p k. 0 < n /\ 0 < k /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
      stepsOf (poly_sqM n p) <= 37 * k ** 2 * size n ** 2``,
  metis_tac[poly_sqM_steps_bound, MAX_1_POS]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Exponential in (mod n, unity k)                                *)
(* ------------------------------------------------------------------------- *)

(* Fast Exponentiation -- recursive form *)

(* Pseudocode:
   Given a polynomial p, and index j, compute (p ** j) (mod n, unity k)
   list_exp p j =
      if j = 0 then return [1]            // p ** 0 = |1|
      q <- list_exp (list_sq p) (HALF j)  // recursive call with (list_sq p) and index (HALF j)
      return if (EVEN j) then q else (list_mult p q) // if OOD j, list_mult result with p
*)

(* Polynomial exponentiation, p ** j (MOD n, unity k). *)
(*
val poly_expM_def = tDefine "poly_expM" `
  poly_expM n p j = (* for p ** j. *)
      do
         j0 <- zeroM j;
         if j0 then do (* trick to keep length k without explicit k *)
                      t <- consM 1 []; (* |1|, but too short *)
                      q <- poly_cmultM n 0 p; (* |0| of same length *)
                      poly_addM n t q (* |1| of same length *)
                    od
         else do
                 p1 <- poly_sqM n p;
                 h <- halfM j;
                 q <- poly_expM n p1 h;
                 ifM (evenM j) (return q) (poly_multM n p q)
              od
      od
`(WF_REL_TAC `measure (λ(n,p,j). j)` >> simp[]);
-- the case j = 0 does not match unity_mod_exp (ZN n) p 0 = |1|
*)
Definition poly_expM_def:
  poly_expM n p j = (* for p ** j. *)
      do
         j0 <- zeroM j;
         if j0 then
              do (* make |1| = if #1 = #0 then [] else [#1] *)
                 n1 <- oneM n;
                 if n1 then return []  (* by 1 MOD 1 = 0 *)
                 else consM 1 [] (* by 1 MOD n = 1, n <> 1 *)
              od
         else do
                 p1 <- poly_sqM n p;
                 h <- halfM j;
                 q <- poly_expM n p1 h;
                 ifM (evenM j) (return q) (poly_multM n p q)
              od
      od
Termination WF_REL_TAC `measure (λ(n,p,j). j)` >> simp[]
End


(*
> EVAL ``poly_expM 10 [1;1;0;0;0;0;0] 0``; = ([1],Count 6): thm
> EVAL ``poly_expM 10 [1;1;0;0;0;0;0] 1``; = ([1; 1; 0; 0; 0; 0; 0],Count 1586): thm
> EVAL ``poly_expM 10 [1;1;0;0;0;0;0] 2``; = ([1; 2; 1; 0; 0; 0; 0],Count 4552): thm
> EVAL ``poly_expM 10 [1;1;0;0;0;0;0] 3``; = ([1; 3; 3; 1; 0; 0; 0],Count 6031): thm
> EVAL ``poly_expM 10 [1;1;0;0;0;0;0] 4``; = ([1; 4; 6; 4; 1; 0; 0],Count 6826): thm
> EVAL ``poly_expM 10 [1;1;0;0;0;0;0] 5``; = ([1; 5; 0; 0; 5; 1; 0],Count 8468): thm
> EVAL ``poly_expM 10 [1;1;0;0;0;0;0] 6``; = ([1; 6; 5; 0; 5; 6; 1],Count 8601): thm
> EVAL ``poly_expM 10 [1;1;0;0;0;0;0] 7``; = ([2; 7; 1; 5; 5; 1; 7],Count 10377): thm
*)

(* Theorem: 0 < n /\ Weak (ZN n) p ==>
            valueOf (poly_expM n p j) = unity_mod_exp (ZN n) p j *)
(* Proof:
   By induction from poly_expM_def.
   Base: valueOf (if n = 1 then unit [] else consM 1 []) = unity_mod_exp (ZN n) p 0
       unity_mod_exp (ZN n) p 0
     = poly_one (ZN n)                               by unity_mod_exp_0
     = if (ZN n).prod.id = (ZN n).sum.id then [] else [(ZN n).prod.id]   by poly_one
     and (ZN n).sum.id = 0                           by ZN_property
     and (ZN n).prod.id = if n = 1 then 0 else 1     by ZN_property
     If n = 1,
        LHS = valueOf (unit []) = [] = RHS
     If n <> 1,
        LHS = valueOf (consM 1 []) = [1] = RHS
   Step: j <> 0 ==> 0 < n /\ Weak (ZN n) (valueOf (poly_sqM n p)) /\ Weak (ZN n) q ==>
         valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j)) =
           unity_mod_exp (ZN n) (valueOf (poly_sqM n p)) (HALF j) ==>
         valueOf (poly_multM n p (valueOf (poly_expM n (unity_mod_sq (ZN n) p) (HALF j)))) =
           unity_mod_exp (ZN n) p j

     If EVEN j,
       valueOf (poly_expM n p j)
     = valueOf (poly_expM n (unity_mod_sq (ZN n) p) (HALF j))  by poly_expM_def
     = unity_mod_exp (ZN n) (unity_mod_sq (ZN n) p) (HALF j)   by induction hypothesis
     = unity_mod_exp (ZN n) p n                                by unity_mod_exp_even

     If ~EVEN j,
       Then ODD j                                              by ODD_EVEN
       valueOf (poly_expM n p j)
     = valueOf (poly_multM n p (valueOf (poly_expM n (unity_mod_sq (ZN n) p) (HALF j))))
                                                               by poly_expM_def
     = valueOf (poly_multM n p (unity_mod_exp (ZN n) (unity_mod_sq (ZN n) p) (HALF j))
                                                               by induction hypothesis
     = unity_mod_mult (ZN n) p (unity_mod_exp (ZN n) (unity_mod_sq (ZN n) p) (HALF j))
                                                               by poly_multM_value
     = unity_mod_exp (ZN n) p n                                by unity_mod_exp_odd
*)
val poly_expM_value = store_thm(
  "poly_expM_value[simp]",
  ``!n p j. 0 < n /\ Weak (ZN n) p ==>
           valueOf (poly_expM n p j) = unity_mod_exp (ZN n) p j``,
  ho_match_mp_tac (theorem "poly_expM_ind") >>
  rw[] >>
  rw[Once poly_expM_def] >-
  (Cases_on `n = 1` >> simp[unity_mod_exp_0, poly_one, ZN_property]) >>
  (Cases_on `EVEN j` >> simp[]) >| [
    `valueOf (poly_expM n (unity_mod_sq (ZN n) p) (HALF j)) =
    valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))` by rw[poly_sqM_value] >>
    `_ = unity_mod_exp (ZN n) (valueOf (poly_sqM n p)) (HALF j)` by rw[poly_sqM_weak] >>
    `_ = unity_mod_exp (ZN n) p j` by rw[unity_mod_exp_even] >>
    rw[],
    `ODD j` by rw[ODD_EVEN] >>
    `valueOf (poly_multM n p (valueOf (poly_expM n (unity_mod_sq (ZN n) p) (HALF j)))) =
    valueOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))` by rw[poly_sqM_value] >>
    `_ = valueOf (poly_multM n p (unity_mod_exp (ZN n) (valueOf (poly_sqM n p)) (HALF j)))` by rw[poly_sqM_weak] >>
    `_ = unity_mod_mult (ZN n) p (unity_mod_exp (ZN n) (valueOf (poly_sqM n p)) (HALF j))` by rw[unity_mod_exp_weak, poly_sqM_weak, ZN_ring] >>
    `_ = unity_mod_exp (ZN n) p j` by rw[unity_mod_exp_odd] >>
    rw[]
  ]);

(* Theorem: 1 < n /\ Weak (ZN n) p /\ p <> [] /\ (LENGTH p = k) ==>
            (valueOf (poly_expM n p j) = p **z j) *)
(* Proof: by poly_expM_value, ZN_poly_exp_alt. *)
val poly_expM_value_thm = store_thm(
  "poly_expM_value_thm",
  ``!n p j k. 1 < n /\ Weak (ZN n) p /\ p <> [] /\ (LENGTH p = k) ==>
             (valueOf (poly_expM n p j) = p **z j)``,
  metis_tac[poly_expM_value, ZN_poly_exp_alt, ONE_LT_POS]);

(* Theorem: 1 < n /\ 0 < k /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
            (valueOf (poly_expM n p j) = p **z j) *)
(* Proof: by poly_expM_value_thm, LENGTH_NIL. *)
val poly_expM_value_alt = store_thm(
  "poly_expM_value_alt",
  ``!n p j k. 1 < n /\ 0 < k /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
             (valueOf (poly_expM n p j) = p **z j)``,
  metis_tac[poly_expM_value_thm, LENGTH_NIL, NOT_ZERO]);

(* Theorem: 0 < n /\ Weak (ZN n) p ==> Weak (ZN n) (valueOf (poly_expM n p j)) *)
(* Proof:
   Note Ring (ZN n)                             by ZN_ring, 0 < n
     Weak (ZN n) (valueOf (poly_expM n p j))
   = Weak (ZN n) (unity_mod_exp (ZN n) p j)     by poly_expM_value
   = T                                          by unity_mod_exp_weak
*)
val poly_expM_weak = store_thm(
  "poly_expM_weak",
  ``!n p j. 0 < n /\ Weak (ZN n) p ==> Weak (ZN n) (valueOf (poly_expM n p j))``,
  metis_tac[poly_expM_value, unity_mod_exp_weak, ZN_ring]);

(* Theorem: 0 < n /\ Weak (ZN n) p /\ Weak (ZN n) q ==>
           LENGTH (valueOf (poly_expM n p j)) =
           if n = 1 then 0 else if j = 0 then 1 else LENGTH p *)
(* Proof:
   Note (ZN n).sum.id = (ZN n).prod.id only when n = 1
                                           by ZN_property
     LENGTH (valueOf (poly_expM n p j))
   = LENGTH (unity_mod_exp (ZN n) p j)     by poly_expM_value
   = if (ZN n).prod.id = (ZN n).sum.id then 0 else if j = 0 then 1 else LENGTH p
                                           by unity_mod_exp_length
   = if n = 1 then 0 else if j = 0 then 1 else LENGTH p
*)
val poly_expM_length = store_thm(
  "poly_expM_length",
  ``!n p j. 0 < n /\ Weak (ZN n) p ==>
           LENGTH (valueOf (poly_expM n p j)) =
           if n = 1 then 0 else if j = 0 then 1 else LENGTH p``,
  rpt strip_tac >>
  `((ZN n).prod.id = (ZN n).sum.id) <=> (n = 1)` by rw[ZN_property] >>
  assume_tac (unity_mod_exp_length |> ISPEC ``(ZN n)``) >>
  first_x_assum (qspecl_then [`p`, `j`] strip_assume_tac) >>
  metis_tac[poly_expM_value, unity_mod_exp_length]);

(* Theorem: valueOf (poly_expM n p 0) = if n = 1 then [] else [1] *)
(* Proof: by poly_expM_def *)
val poly_expM_0 = store_thm(
  "poly_expM_0",
  ``!n p. valueOf (poly_expM n p 0) = if n = 1 then [] else [1]``,
  rw[Once poly_expM_def]);

(* Theorem: Weak (ZN 1) p ==> (valueOf (poly_expM 1 p j) = []) *)
(* Proof:
   Note LENGTH (valueOf (poly_expM 1 p j)) = 0   by poly_expM_length
   Thus valueOf (poly_expM 1 p j) = []           by LENGTH_NIL
*)
val poly_expM_trivial = store_thm(
  "poly_expM_trivial",
  ``!p j. Weak (ZN 1) p ==> (valueOf (poly_expM 1 p j) = [])``,
  metis_tac[poly_expM_length, LENGTH_NIL, DECIDE``0 < 1``]);

(* Theorem: stepsOf (poly_expM n p j) =
             size j +
             if j = 0 then (size n + if n = 1 then 0 else 1)
             else (1 + 4 * size j + stepsOf (poly_sqM n p) +
                     (if EVEN j then 0 else
                     stepsOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))) +
                  stepsOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))) *)
(* Proof:
     stepsOf (poly_expM n p j)
   = stepsOf (zeroM j) +
     if j = 0 then (stepsOf (oneM n) + if n = 1 then 0 else stepsOf (consM 1 []))
     else stepsOf (poly_sqM n p) + stepsOf (halfM j) +
          stepsOf (poly_expM n (unity_mod_sq n p) (HALF j)) + stepsOf (evenM j) +
          if EVEN j then stepsOf (return q) else stepsOf (poly_multM n p q)
              where q = unity_mod_exp n (unity_mod_sq n p) (HALF j)    by poly_expM_def
   = size j + if j = 0 then (size n + if n = 1 then 0 else 1)
     else stepsOf (poly_sqM n p) + 2 * size j +
     stepsOf (poly_expM n (unity_mod_sq n p) (HALF j)) + (1 + 2 * size j) +
     if EVEN j then 0 else stepsOf (poly_multM n p (unity_mod_exp n (unity_mod_sq n p) (HALF j)))
   = size j + if j = 0 then (size n + if n = 1 then 0 else 1)
     else stepsOf (poly_sqM n p) + 2 * size j + (1 + 2 * size j) +
     (if EVEN j then 0 else stepsOf (poly_multM n p (unity_mod_exp n (unity_mod_sq n p) (HALF j)))) +
     stepsOf (poly_expM n (unity_mod_sq n p) (HALF j))
   = size j + if j = 0 then (size n + if n = 1 then 0 else 1)
     else 1 + 4 * size j +stepsOf (poly_sqM n p) +
     (if EVEN j then 0 else stepsOf (poly_multM n p (unity_mod_exp n (unity_mod_sq n p) (HALF j)))) +
     stepsOf (poly_expM n (unity_mod_sq n p) (HALF j))
   use valueOf for unconditional form.
*)
val poly_expM_steps_thm = store_thm(
  "poly_expM_steps_thm",
  ``!n p j. stepsOf (poly_expM n p j) =
             size j +
             if j = 0 then (size n + if n = 1 then 0 else 1)
             else (1 + 4 * size j + stepsOf (poly_sqM n p) +
                     (if EVEN j then 0 else
                     stepsOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))) +
                  stepsOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j)))``,
  rw[Once poly_expM_def]);

(* Theorem: let body p j = 1 + 5 * size j + stepsOf (poly_sqM n p) +
           if EVEN j then 0 else stepsOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))
        in !p j. stepsOf (poly_expM n p j) =
                 if j = 0 then (1 + size n + if n = 1 then 0 else 1)
                 else body p j + stepsOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j)) *)
(* Proof:
     stepsOf (poly_expM n p j)
   = size j + if j = 0 then (size n + if n = 1 then 0 else 1)
     else (1 + 4 * size j + stepsOf (poly_sqM n p) +
          (if EVEN j then 0 else stepsOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))) +
          stepsOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j)))   by poly_expM_steps_thm
   = if j = 0 then (size 0 + size n + if n = 1 then 0 else 1)
     else (size j + 1 + 4 * size j + stepsOf (poly_sqM n p) +
          (if EVEN j then 0 else stepsOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))) +
          stepsOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j)))
   = if j = 0 then (if n = 1 then 2 else 2 + size n)
     else (1 + 5 * size j + stepsOf (poly_sqM n p) +
          (if EVEN j then 0 else stepsOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))) +
          stepsOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j)))
*)
val poly_expM_steps_by_div_loop = store_thm(
  "poly_expM_steps_by_div_loop",
  ``!n. let body p j = 1 + 5 * size j + stepsOf (poly_sqM n p) +
           if EVEN j then 0 else stepsOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))
        in !p j. stepsOf (poly_expM n p j) =
                 if j = 0 then (1 + size n + if n = 1 then 0 else 1)
                 else body p j + stepsOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))``,
  (rw[Once poly_expM_steps_thm] >> Cases_on `j = 0` >> simp[]));

(*
This puts poly_expM_steps in the category: dividing loop with body cover.
   poly_expM_steps_by_div_loop:
        !p j. loop p j = if j = 0 then quit p else body p j + loop (valueOf (poly_sqM n p)) (HALF j)
suitable for: loop2_div_rise_count_cover_le
Actually a conditional cover, so needs to fall back to: loop2_div_count_eqn
*)

(* First, work out a cover for the body. *)

(* Theorem: let body p j = 1 + 5 * size j + stepsOf (poly_sqM n p) +
                if EVEN j then 0 else stepsOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))
             in !p j k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
                        body p j <= 1 + 5 * size j + 74 * (MAX 1 k) ** 2 * size n ** 2 *)
(* Proof:
      body p j
    = 1 + 5 * size j + stepsOf (poly_sqM n p) +
      if EVEN j then 0 else stepsOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))
    = 1 + 5 * size j + stepsOf (poly_sqM n p) +
      if EVEN j then 0 else stepsOf (poly_multM n p q)
                                           where q = valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))
   <= 1 + 5 * size j + stepsOf (poly_sqM n p) + stepsOf (poly_multM n p q)
   Note  stepsOf (poly_sqM n p)
      <= 37 * (MAX 1 k) ** 2 * size n ** 2           by poly_sqM_steps_bound
   For   stepsOf (poly_multM n p q),
   Note Weak (ZN n) q                                by poly_sqM_weak
   If n = 1,
      Then q = []                                    by poly_expM_trivial
       and stepsOf (poly_multM n p []) = 1           by poly_multM_steps_nil
   If HALF j = 0,
      Then q = [1]                                   by poly_expM_0, n <> 1
       and stepsOf (poly_multM n p [1])
        <= 27 * (MAX 1 k) * size (MAX 1 n) * size n  by poly_multM_steps_sing_bound
         = 27 * (MAX 1 k) * size n * size n          by MAX_DEF, 0 < n
         = 27 * (MAX 1 k) * size n ** 2
   Otherwise,
      (LENGTH q = k)                                 by poly_expM_length, poly_sqM_length
      so stepsOf (poly_multM n p q)
      <= 37 * (MAX 1 k) ** 2 * size n ** 2           by poly_multM_steps_bound, LENGTHs match
   Overall,
         body p j
      <= 1 + 5 * size j + 2 * 37 * MAX 1 k ** 2 * size n ** 2
*)
val poly_expM_body_upper = store_thm(
  "poly_expM_body_upper",
  ``!n. let body p j = 1 + 5 * size j + stepsOf (poly_sqM n p) +
           if EVEN j then 0 else stepsOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))
        in !p j k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
                   body p j <= 1 + 5 * size j + 74 * (MAX 1 k) ** 2 * size n ** 2``,
  rw_tac std_ss[] >>
  `body p j = 1 + 5 * size j + stepsOf (poly_sqM n p) +
                 if EVEN j then 0
                 else
                   stepsOf
                     (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))` by fs[Abbr`body`] >>
  qabbrev_tac `q = valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))` >>
  `body p j <=  1 + 5 * size j + stepsOf (poly_sqM n p) + stepsOf (poly_multM n p q)` by rw[] >>
  qabbrev_tac `k = LENGTH p` >>
  `stepsOf (poly_sqM n p) <= 37 * MAX 1 k ** 2 * size n ** 2` by rw[poly_sqM_steps_bound] >>
  `Weak (ZN n) q` by rw[poly_expM_weak, poly_sqM_weak, Abbr`q`] >>
  Cases_on `n = 1` >| [
    `q = []` by metis_tac[poly_expM_trivial, poly_sqM_weak] >>
    `stepsOf (poly_multM n p q) = 1` by metis_tac[poly_multM_steps_nil] >>
    `0 < MAX 1 k ** 2 * size n ** 2` by rw[] >>
    decide_tac,
    Cases_on `HALF j = 0` >| [
      `q = [1]` by metis_tac[poly_expM_0] >>
      `MAX 1 n = n` by rw[MAX_DEF] >>
      `stepsOf (poly_multM n p q) <= 27 * (MAX 1 k) * size n * size n` by metis_tac[poly_multM_steps_sing_bound] >>
      `(MAX 1 k) <= (MAX 1 k) ** 2` by metis_tac[SELF_LE_SQ, EXP_2] >>
      `(MAX 1 k) * size n * size n <= (MAX 1 k) ** 2 * size n ** 2` by rw[] >>
      decide_tac,
      `LENGTH q = k` by metis_tac[poly_expM_length, poly_sqM_weak, poly_sqM_length] >>
      `stepsOf (poly_multM n p q) <= 37 * MAX 1 k ** 2 * size n ** 2` by rw[poly_multM_steps_bound] >>
      decide_tac
    ]
  ]);

(* Theorem: let body p j = 1 + 5 * size j + stepsOf (poly_sqM n p) +
           if EVEN j then 0 else stepsOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))
        in !p j k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
                   body p j <= 80 * size j * (MAX 1 k) ** 2 * size n ** 2 *)
(* Proof:
      body p j
   <= 1 + 5 * size j + 74 * (MAX 1 k) ** 2 * size n ** 2    by poly_expM_body_upper
   <= (1 + 5 + 74) * size j * (MAX 1 k) ** 2 * size n ** 2  by dominant term
    = 80 * size j * (MAX 1 k) ** 2 * size n ** 2
*)
val poly_expM_body_bound = store_thm(
  "poly_expM_body_bound",
  ``!n. let body p j = 1 + 5 * size j + stepsOf (poly_sqM n p) +
           if EVEN j then 0 else stepsOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))
        in !p j k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
                   body p j <= 80 * size j * (MAX 1 k) ** 2 * size n ** 2``,
  rpt strip_tac >>
  assume_tac poly_expM_body_upper >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  qabbrev_tac `body = \p j. 1 + 5 * size j + stepsOf (poly_sqM n p) +
       if EVEN j then 0 else stepsOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))` >>
  `!p j k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==> body p j <= 80 * size j * MAX 1 k ** 2 * size n ** 2` suffices_by fs[] >>
  rpt strip_tac >>
  `body p j <= 1 + 5 * size j + 74 * (MAX 1 k) ** 2 * size n ** 2` by metis_tac[] >>
  qabbrev_tac `m = MAX 1 k` >>
  qabbrev_tac `t = size j * m ** 2 * size n ** 2` >>
  `body p j <= 80 * t` suffices_by rw[Abbr`t`] >>
  `1 <= m` by rw[Abbr`m`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `size j <= t` by
  (`size j <= size j * (m ** 2 * size n ** 2)` by rw[MULT_POS] >>
  `size j * (m ** 2 * size n ** 2) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `m ** 2 * size n ** 2 <= t` by
    (`m ** 2 * size n ** 2 <= m ** 2 * size n ** 2 * size j` by rw[MULT_POS] >>
  `m ** 2 * size n ** 2 * size j = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* Theorem: 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
            stepsOf (poly_expM n p j) <= 2 + size n + 80 * (MAX 1 k) ** 2 * size j ** 2 * size n ** 2 *)
(* Proof:
   Let quit = (\p. 1 + size n + if n = 1 then 0 else 1),
       body = (\p j. 1 + 5 * size j + stepsOf (poly_sqM n p) +
               if EVEN j then 0
               else stepsOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))),
        cover = (\p j. 80 * size j * (MAX 1 (LENGTH p)) ** 2 * size n ** 2),
        f = (\p. valueOf (poly_sqM n p)),
        loop = (\p j. stepsOf (poly_expM n p j)).
   Then !p j. loop p j = if j = 0 then quit p else body p j + loop (f p) (HALF j)
                                        by poly_expM_steps_by_div_loop
    Now !x y. body x y <= cover x y     by poly_expM_body_bound
    and MONO2 cover                     by subgoal
    and RISING f                        by subgoal
   Let m = pop 2 j <= size n            by pop_size
       q = FUNPOW f m p,
       g = (\t. body (FUNPOW f t p) (j DIV 2 ** t)),

   Claim: SUM (GENLIST g m) <= SUM (GENLIST (K (cover p j)) m)
   Proof: Let i < m, want to show:
          EL i (GENLIST g m) <= EL i (GENLIST (K (cover p j)) m)
          Let u = FUNPOW i p, h = j DIV 2 ** i.
          This is to show:   body u h <= cover p j
          Note Weak (ZN n) u          by poly_sqM_iterating_weak
           and LENGTH u = LENGTH p    by poly_sqM_iterating_length
          Note h <= j                 by DIV_LESS_EQ
               body q h
            <= cover q h              by cover over body
             = cover p h              by LENGTH q = LENGTH p, special form of cover
            <= cover p j              by size_monotone_le
          The result follows          by SUM_LE

   Thus loop p j
      = quit q + SUM (GENLIST g m)                  by loop2_div_count_eqn
     <= quit q + SUM (GENLIST (K (cover p j)) m)    by SUM_LE, claim
     <= (2 + size n) + (cover p j) * m              by SUM_GENLIST_K
     <= (2 + size n) + 80 * size j * (MAX 1 k) ** 2 * size n ** 2 * size j
      = 2 + size n + 80 * (MAX 1 k) ** 2 * size j ** 2 * size n ** 2
*)
val poly_expM_steps_upper = store_thm(
  "poly_expM_steps_upper",
  ``!p n j k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
             stepsOf (poly_expM n p j) <= 2 + size n + 80 * (MAX 1 k) ** 2 * size j ** 2 * size n ** 2``,
  rpt strip_tac >>
  assume_tac poly_expM_steps_by_div_loop >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  assume_tac poly_expM_body_bound >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  qabbrev_tac `quit = \p:num list. 1 + size n + if n = 1 then 0 else 1` >>
  qabbrev_tac `body = \p j. 1 + 5 * size j + stepsOf (poly_sqM n p) +
               if EVEN j then 0
               else stepsOf (poly_multM n p (valueOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))))` >>
  qabbrev_tac `cover = \p:num list j. 80 * size j * (MAX 1 (LENGTH p)) ** 2 * size n ** 2` >>
  qabbrev_tac `f = \p. valueOf (poly_sqM n p)` >>
  qabbrev_tac `loop = \p j. stepsOf (poly_expM n p j)` >>
  `loop p j <= 2 + size n + 80 * MAX 1 k ** 2 * size j ** 2 * size n ** 2` suffices_by rw[] >>
  `!p j. loop p j = if j = 0 then quit p else body p j + loop (f p) (HALF j)` by metis_tac[] >>
  `1 < 2` by decide_tac >>
  `!x y. Weak (ZN n) x ==> body x y <= cover x y` by metis_tac[] >>
  imp_res_tac loop2_div_count_eqn >>
  last_x_assum (qspecl_then [`j`, `p`] strip_assume_tac) >>
  qabbrev_tac `foo1 = let body = body in
           !p j. stepsOf (poly_expM n p j) =
               if j = 0 then 1 + size n + if n = 1 then 0 else 1
               else body p j + stepsOf (poly_expM n (valueOf (poly_sqM n p)) (HALF j))` >>
  qabbrev_tac `foo2 = !p j. loop p j = if j = 0 then quit p else body p j + loop (f p) (HALF j)` >>
  `pop 2 j <= size j` by rw[pop_size] >>
  qabbrev_tac `g = \j'. body (FUNPOW f j' p) (j DIV 2 ** j')` >>
  `quit (FUNPOW f (pop 2 j) p) <= 2 + size n` by rw[Abbr`quit`] >>
  `SUM (GENLIST g (pop 2 j)) <= SUM (GENLIST (K (cover p j)) (pop 2 j))` by
  (irule SUM_LE >>
  rw[Abbr`g`] >>
  qabbrev_tac `q = FUNPOW f k' p` >>
  qabbrev_tac `h = j DIV 2 ** k'` >>
  `Weak (ZN n) q` by rw[poly_sqM_iterating_weak, Abbr`q`, Abbr`f`] >>
  `LENGTH q = LENGTH p` by rw[poly_sqM_iterating_length, Abbr`q`, Abbr`f`] >>
  `body q h <= cover q h` by rw[] >>
  `cover q h = cover p h` by rw[Abbr`cover`] >>
  `h <= j` by rw[DIV_LESS_EQ, Abbr`h`] >>
  `cover p h <= cover p j` by rw[size_monotone_le, Abbr`cover`] >>
  decide_tac) >>
  `SUM (GENLIST (K (cover p j)) (pop 2 j)) = (cover p j) * (pop 2 j)` by rw[SUM_GENLIST_K] >>
  `cover p j * pop 2 j <= cover p j * size j` by rw[] >>
  `cover p j * size j = 80 * size j * MAX 1 k ** 2 * size n ** 2 * size j` by fs[Abbr`cover`] >>
  `80 * size j * MAX 1 k ** 2 * size n ** 2 * size j = 80 * MAX 1 k ** 2 * size j ** 2 * size n ** 2` by rw[] >>
  decide_tac);

(* Theorem: 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
            stepsOf (poly_expM n p j) <= 83 * (MAX 1 k) ** 2 * size j ** 2 * size n ** 2 *)
(* Proof:
      stepsOf (poly_expM n p j)
   <= 2 + size n + 80 * (MAX 1 k) ** 2 * size j ** 2 * size n ** 2    by poly_expM_steps_upper
   <= (2 + 1 + 80) * 80 * (MAX 1 k) ** 2 * size j ** 2 * size n ** 2  by dominant term
    = 83 * (MAX 1 k) ** 2 * size j ** 2 * size n ** 2
*)
val poly_expM_steps_bound = store_thm(
  "poly_expM_steps_bound",
  ``!p n j k. 0 < n /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
             stepsOf (poly_expM n p j) <= 83 * (MAX 1 k) ** 2 * size j ** 2 * size n ** 2``,
  rpt strip_tac >>
  assume_tac poly_expM_steps_upper >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  first_x_assum (qspec_then `j` strip_assume_tac) >>
  `0 < MAX 1 k ** 2 * size j ** 2 * size n ** 2` by rw[MULT_POS] >>
  `size n <= size n * (MAX 1 k ** 2 * size j ** 2 * size n)` by rw[MULT_POS] >>
  `size n * (MAX 1 k ** 2 * size j ** 2 * size n) = MAX 1 k ** 2 * size j ** 2 * size n ** 2` by rw[] >>
  decide_tac);

(* The following is just to match conditions in poly_expM_value_alt *)

(* Theorem: 1 < n /\ 0 < k /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
            stepsOf (poly_expM n p j) <= 83 * k ** 2 * size j ** 2 * size n ** 2 *)
(* Proof: by poly_expM_steps_bound, MAX_1_POS *)
val poly_expM_steps_bound_alt = store_thm(
  "poly_expM_steps_bound_alt",
  ``!p n j k. 1 < n /\ 0 < k /\ Weak (ZN n) p /\ (LENGTH p = k) ==>
             stepsOf (poly_expM n p j) <= 83 * k ** 2 * size j ** 2 * size n ** 2``,
  metis_tac[poly_expM_steps_bound, MAX_1_POS, DECIDE``1 < n ==> 0 < n``]);

(* ------------------------------------------------------------------------- *)
(* Polynomial Coefficients                                                   *)
(* ------------------------------------------------------------------------- *)

(* Get coefficient j of polynomial of length k *)
(* > EL;
val it = |- (!l. EL 0 l = HD l) /\ !l n. EL (SUC n) l = EL n (TL l): thm
*)
Definition poly_get_coeffM_def:
  poly_get_coeffM p j = (* always assume p <> |0|, j < k *)
      do
        j0 <- zeroM j;
        if j0 then headM p
        else do
               q <- tailM p;
               i <- decM j;
               poly_get_coeffM q i;
             od
      od
Termination WF_REL_TAC `measure (λ(p,j). j)` >> simp[]
End

(* Put x as coefficient j of polynomial of length k *)
(* > LUPDATE_def
val it = |- (!e n. LUPDATE e n [] = []) /\ (!e x l. LUPDATE e 0 (x::l) = e::l) /\
             !e n x l. LUPDATE e (SUC n) (x::l) = x::LUPDATE e n l: thm
*)
Definition poly_put_coeffM_def:
  poly_put_coeffM x p j = (* always assume p <> |0|, j < k *)
      do
        q <- tailM p;
        j0 <- zeroM j;
        if j0 then consM x q
        else do
               h <- headM p;
               i <- decM j;
               p1 <- poly_put_coeffM x q i;
               consM h p1;
             od
      od
Termination WF_REL_TAC `measure (λ(x,p,j). j)` >> simp[]
End

(*
> EVAL ``poly_get_coeffM [1;2;3;4;5] 2``; = (3,Count 10): thm
> EVAL ``poly_put_coeffM 0 [1;2;3;4;5] 2``; = ([1; 2; 0; 4; 5],Count 15): thm
*)

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
