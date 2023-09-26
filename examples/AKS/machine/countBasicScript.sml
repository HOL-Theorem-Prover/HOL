(* ------------------------------------------------------------------------- *)
(* Basic Computations with Count Monad                                       *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "countBasic";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* val _ = load "SatisfySimps"; (* for SatisfySimps.SATISFY_ss *) *)

(* Get dependent theories local *)
(* val _ = load "countMacroTheory"; *)
open countMonadTheory countMacroTheory;

open bitsizeTheory complexityTheory;
open loopIncreaseTheory loopDecreaseTheory;
open loopDivideTheory;
open loopMultiplyTheory; (* for loop2_mul_rise_steps_le *)

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
open helperNumTheory helperSetTheory helperListTheory;
open pred_setTheory listTheory arithmeticTheory;

(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open dividesTheory gcdTheory;

(* val _ = load "logPowerTheory"; *)
open logrootTheory logPowerTheory;

(* val _ = load "monadsyntax"; *)
open monadsyntax;
open pairTheory optionTheory;
open listRangeTheory;

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "Count";


(* ------------------------------------------------------------------------- *)
(* Basic Computations with Count Monad Documentation                         *)
(* ------------------------------------------------------------------------- *)
(* Data type:
*)
(* Overloading:
*)
(* Definitions and Theorems (# are exported):

   Helper:

   Size in Monadic Style:
   sizeM_def                 |- !n. sizeM n =
                                    do
                                      b0 <- zeroM n;
                                      b1 <- oneM n;
                                      if b0 \/ b1 then 1c
                                      else do x' <- halfM n; y' <- sizeM x'; incM y' od
                                    od
#  sizeM_value               |- !n. valueOf (sizeM n) = size n
   sizeM_steps_thm           |- !n. stepsOf (sizeM n) = TWICE (size n) + if n <= 1 then 0
                                    else TWICE (size n) + size (size n - 1) + stepsOf (sizeM (HALF n))
   sizeM_steps_0             |- stepsOf (sizeM 0) = 2
   sizeM_steps_1             |- stepsOf (sizeM 1) = 2
   sizeM_steps_by_div_loop   |- let body n = if n <= 1 then 2 else 4 * size n + size (size n - 1) ;
                                    exit n = n = 1
                                 in !n. stepsOf (sizeM n) = if n = 0 then 2
                                        else body n + if exit n then 0 else stepsOf (sizeM (HALF n))
   sizeM_steps_upper         |- !n. stepsOf (sizeM n) <= 2 + 5 * size n ** 2
   sizeM_steps_bound         |- !n. stepsOf (sizeM n) <= 7 * size n ** 2
   sizeM_steps_O_poly        |- stepsOf o sizeM IN O_poly 2
   sizeM_steps_big_O         |- stepsOf o sizeM IN big_O (\n. ulog n ** 2)
   sizeM_thm                 |- !n. (valueOf (sizeM n) = size n) /\
                                    stepsOf o sizeM IN big_O (\n. ulog n ** 2)

   Perfect-power in Monadic Style:
   power_ofM_def             |- !n b. power_ofM b n =
                                      do
                                        n0 <- zeroM n;
                                        n1 <- oneM n;
                                        b0 <- zeroM b;
                                        b1 <- oneM b;
                                        if n0 then unit b0
                                        else if n1 then unit T
                                        else if b0 then unit (n0 \/ n1)
                                        else if b1 then unit n1
                                        else
                                          do
                                            m' <- modM n b;
                                            gd <- zeroM m';
                                            if gd then do n' <- divM n b; power_ofM b n' od else unit F
                                          od
                                      od
#  power_ofM_value           |- !b n. valueOf (power_ofM b n) <=> perfect_power n b
   power_ofM_steps_thm       |- !b n. stepsOf (power_ofM b n) =
                                      TWICE (size n) + TWICE (size b) +
                                      if n = 0 \/ n = 1 \/ b = 0 \/ b = 1 then 0
                                      else size n * size b + size (n MOD b) +
                                           if n MOD b <> 0 then 0
                                           else size n * size b + stepsOf (power_ofM b (n DIV b))
   power_ofM_steps_le        |- !b n. TWICE (size n + size b) <= stepsOf (power_ofM b n)
   power_ofM_steps_base      |- !b n. stepsOf (power_ofM b 0) = TWICE (1 + size b) /\
                                      stepsOf (power_ofM b 1) = TWICE (1 + size b) /\
                                      stepsOf (power_ofM 0 n) = TWICE (1 + size n) /\
                                      stepsOf (power_ofM 1 n) = TWICE (1 + size n)
   power_ofM_steps_by_div_loop
                             |- !b. (let body n = TWICE (size n) + TWICE (size b) +
                                           if n <= 1 \/ b <= 1 then 0
                                           else size n * size b + size (n MOD b) +
                                                if n MOD b <> 0 then 0 else size n * size b ;
                                         exit n = n = 1 \/ b = 0 \/ b = 1 \/ n MOD b <> 0
                                      in !n. 1 < b ==>
                                             stepsOf (power_ofM b n) = if n = 0 then 2 + TWICE (size b)
                                             else body n +
                                                  if exit n then 0 else stepsOf (power_ofM b (n DIV b)))
   power_ofM_steps_upper     |- !b n. stepsOf (power_ofM b n) <=
                                      2 + TWICE (size b) + 3 * size b * size n + TWICE (size n ** 2) +
                                          TWICE (size b) * size n ** 2
   power_ofM_steps_bound     |- !b n. stepsOf (power_ofM b n) <= 11 * size b * size n ** 2
   power_ofM_steps_O_poly    |- !b. stepsOf o power_ofM b IN O_poly 2
   power_ofM_steps_big_O     |- !b. stepsOf o power_ofM b IN big_O (\n. ulog n ** 2)
   power_ofM_thm             |- !b n. (valueOf (power_ofM b n) <=> n power_of b) /\
                                      stepsOf o power_ofM b IN big_O (\n. ulog n ** 2)

   power_twoM_def            |- power_twoM = power_ofM 2
#  power_twoM_value          |- !n. valueOf (power_twoM n) <=> perfect_power n 2
   power_twoM_steps_thm      |- !n. stepsOf (power_twoM n) = TWICE (size n) + 4 +
                                      if n = 0 \/ n = 1 then 0
                                      else size n * 2 + size (n MOD 2) + if n MOD 2 <> 0 then 0
                                           else size n * 2 + stepsOf (power_twoM (HALF n))
   power_twoM_steps_0        |- stepsOf (power_twoM 0) = 6
   power_twoM_steps_1        |- stepsOf (power_twoM 1) = 6
   power_twoM_steps_upper    |- !n. stepsOf (power_twoM n) <= 6 + 6 * size n + 6 * size n ** 2
   power_twoM_steps_bound    |- !n. stepsOf (power_twoM n) <= 18 * size n ** 2
   power_twoM_steps_O_poly   |- stepsOf o power_twoM IN O_poly 2
   power_twoM_steps_big_O    |- stepsOf o power_twoM IN big_O (\n. ulog n ** 2)
   power_twoM_thm            |- !n. (valueOf (power_twoM n) <=> n power_of 2) /\
                                    stepsOf o power_twoM IN big_O (\n. ulog n ** 2)

   Ulog in Monad Style:
   ulogM_def           |- !n. ulogM n =
                              do
                                gd <- zeroM n;
                                if gd then 0c
                                else
                                  do x <- sizeM n; b <- power_twoM n; y <- boolM b; subM x y od
                              od
#  ulogM_value         |- !n. valueOf (ulogM n) = ulog n
   ulogM_steps_thm     |- !n. stepsOf (ulogM n) = if n = 0 then 1
                              else 1 + size n + size (size n) + stepsOf (sizeM n) + stepsOf (power_twoM n)
   ulogM_steps_0       |- stepsOf (ulogM 0) = 1
   ulogM_steps_1       |- stepsOf (ulogM 1) = 11
   ulogM_steps_upper   |- !n. stepsOf (ulogM n) <= 9 + 8 * size n + 11 * size n ** 2
   ulogM_steps_bound   |- !n. stepsOf (ulogM n) <= 28 * size n ** 2
   ulogM_steps_O_poly  |- stepsOf o ulogM IN O_poly 2
   ulogM_steps_big_O   |- stepsOf o ulogM IN big_O (\n. ulog n ** 2)
   ulogM_thm           |- !n. (valueOf (ulogM n) = ulog n) /\
                              stepsOf o ulogM IN big_O (\n. ulog n ** 2)

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
(* Size in Monadic Style (by recursion)                                      *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode: compute (size n)
   size n =
      if n = 0 return 1         // size 0 = 1
      if n = 1 return 1         // size 1 = 1
      return 1 + size (HALF n)  // size n = 1 + size (HALF n)
*)

(* Define size monad *)
Definition sizeM_def:
    sizeM n =
      do
        b0 <- zeroM n;
        b1 <- oneM n;
        if b0 \/ b1 then return 1
        else do
               x' <- halfM n;
               y' <- sizeM x';
               incM y';
             od
      od
Termination WF_REL_TAC `$<` >> simp[]
End

(*
EVAL ``MAP sizeM [0 .. 10]``;
EVAL ``MAP size [0 .. 10]``;
*)

(* Theorem: valueOf (sizeM n) = size n *)
(* Proof:
   By complete induction on n.
   If n = 0,
        valueOf (sizeM 0)
      = valueOf (return 1)     by sizeM_def
      = 1 = size 0             by size_0
   If n = 1,
        valueOf (sizeM 1)
      = valueOf (return 1)     by sizeM_def
      = 1 = size 1             by size_1
   If n <> 0, n <> 1,
      Then HALF n < n                     by HALF_LESS, n <> 0
        valueOf (sizeM n)
      = 1 + valueOf (sizeM (HALF n))      by sizeM_def
      = 1 + size (HALF n)                 by induction hypothesis
      = SUC (size (HALF n))               by ADD1
      = size n                            by size_half_SUC
*)
val sizeM_value = store_thm(
  "sizeM_value[simp]",
  ``!n. valueOf (sizeM n) = size n``,
  completeInduct_on `n` >>
  (rw [Once sizeM_def] >> simp[]) >>
  rw[GSYM size_half_SUC, ADD1]);

(* Theorem: stepsOf (sizeM n) = 2 * size n + if n <= 1 then 0 else
                                2 * size n + size (size n - 1) + stepsOf (sizeM (HALF n)) *)
(* Proof:
    stepsOf (sizeM n)
  = stepsOf (zeroM n) + stepsOf (oneM n) +
    if n = 0 \/ n = 1 then 0 else
    stepsOf (halfM n) + stepsOf (sizeM (HALF n)) + stepsOf (incM (valueOf (sizeM (HALF n))))
  = 2 * size n + if n <= 1 then 0 else
    2 * size n + stepsOf (sizeM (HALF n)) + size (size (HALF n))  by sizeM_value
  = 2 * size n + if n <= 1 then 0 else
    2 * size n + size (size n - 1) + stepsOf (sizeM (HALF n))     by size_half
*)
val sizeM_steps_thm = store_thm(
  "sizeM_steps_thm",
  ``!n. stepsOf (sizeM n) = 2 * size n + if n <= 1 then 0 else
                           2 * size n + size (size n - 1) + stepsOf (sizeM (HALF n))``,
  rpt strip_tac >>
  Cases_on `(n = 0) \/ (n = 1)` >-
  simp[Once sizeM_def] >>
  simp[Once sizeM_def, sizeM_value] >>
  rw[size_half]);

(* Theorem: stepsOf (sizeM 0) = 2 *)
(* Proof: by sizeM_steps_thm *)
val sizeM_steps_0 = store_thm(
  "sizeM_steps_0",
  ``stepsOf (sizeM 0) = 2``,
  rw[Once sizeM_steps_thm]);

(* Theorem: stepsOf (sizeM 1) = 2 *)
(* Proof: by sizeM_steps_thm *)
val sizeM_steps_1 = store_thm(
  "sizeM_steps_1",
  ``stepsOf (sizeM 1) = 2``,
  rw[Once sizeM_steps_thm]);


(* Theorem: let body n = if n <= 1 then 2 else 4 * size n + size (size n - 1);
                exit n = (n = 1)
             in !n. stepsOf (sizeM n) = if n = 0 then 2
                    else body n + if exit n then 0 else stepsOf (sizeM (HALF n)) *)
(* Proof:
     stepsOf (sizeM n)
   = 2 * size n + if n <= 1 then 0
     else 2 * size n + size (size n - 1) + stepsOf (sizeM (HALF n))   by sizeM_steps_thm
   = if n <= 1 then 2 * size n
     else 4 * size n  + size (size n - 1) + stepsOf (sizeM (HALF n))
   = if n = 0 \/ n = 1 then 2
     else 4 * size n + size (size n - 1) + stepsOf (sizeM (HALF n))   by size_0, size_1
   = if n = 0 then 2
     else if n = 1 then 2 else 4 * size n + size (size n - 1) +
          if n = 1 then 0 else stepsOf (sizeM (HALF n))
   Modify first n = 1 to n <= 1 for body to be covered.
*)
val sizeM_steps_by_div_loop = store_thm(
  "sizeM_steps_by_div_loop",
  ``let body n = if n <= 1 then 2 else 4 * size n + size (size n - 1);
       exit n = (n = 1)
    in !n. stepsOf (sizeM n) = if n = 0 then 2
           else body n + if exit n then 0 else stepsOf (sizeM (HALF n))``,
  rw[Once sizeM_steps_thm] >>
  (Cases_on `n <= 1` >> simp[]) >>
  fs[LE_ONE]);

(*
This puts sizeM_steps in the category: dividing loop with body cover and exit.
   sizeM_steps_by_div_loop:
        !n. loop n = if n = 0 then 2 else body n + if exit n then 0 else loop (HALF n)
suitable for: loop_div_count_cover_exit_le
*)

(* Theorem: stepsOf (sizeM n) <= 2 + 5 * (size n) ** 2 *)
(* Proof:
   Let loop = (\n. stepsOf (sizeM n)),
       body = (\n. if n <= 1 then 2 else 4 * size n + size (size n - 1)),
       cover = (\n. 5 * size n),
       exit = (\n. n = 1).
   Then loop n = if n = 0 then 2 else body n + if exit n then 0 else loop (HALF n)
                                             by sizeM_steps_by_div_loop
   Claim: !x. body x <= cover x
   Proof: If n <= 1, 2 <= 5 * size n         by size_0, size_1
          Otherwise 1 < n,
          Note size n <= n                   by size_le_self, 0 < n
            so size n < n + 1                by arithmetic
            or size n - 1 < n                by arithmetic
           ==> size (size n - 1) <= size n   by size_monotone_lt
          Thus body n
             = 4 * size n + size (size n - 1)    by notation
            <= 4 * size n + size n
             = 5 * size n

    Now 1 < 2,
    and !x. body x <= cover x                by claim
   Thus loop n
     <= 2 + pop 2 n * cover n                by loop_div_count_cover_exit_le
     <= 2 + size n * cover n                 by pop_size
      = 2 + size n * (5 * size n)            by notation
      = 2 + 5 * size n ** 2                  by EXP_2
*)
val sizeM_steps_upper = store_thm(
  "sizeM_steps_upper",
  ``!n. stepsOf (sizeM n) <= 2 + 5 * (size n) ** 2``,
  rpt strip_tac >>
  assume_tac sizeM_steps_by_div_loop >>
  qabbrev_tac `loop = \n. stepsOf (sizeM n)` >>
  qabbrev_tac `body = \n. if n <= 1 then 2 else 4 * size n + size (size n - 1)` >>
  qabbrev_tac `cover = \n. 5 * size n` >>
  qabbrev_tac `exit = \n. n = 1` >>
  `loop n <= 2 + 5 * size n ** 2` suffices_by rw[Abbr`loop`] >>
  `loop n = if n = 0 then 2 else body n + if exit n then 0 else loop (HALF n)` by metis_tac[] >>
  `1 < 2` by decide_tac >>
  `!x. body x <= cover x` by
  (rw[Abbr`body`, Abbr`cover`] >| [
    `size x = 1` by metis_tac[LE_ONE, size_0, size_1] >>
    decide_tac,
    `1 < x` by decide_tac >>
    `size x <= x` by rw[size_le_self] >>
    `size x - 1 < x` by decide_tac >>
    `size (size x - 1) <= size x` by rw[size_monotone_lt] >>
    decide_tac
  ]) >>
  `MONO cover` by rw[size_monotone_le, Abbr`cover`] >>
  assume_tac loop_div_count_cover_exit_le >>
  first_x_assum (qspecl_then [`loop`, `body`, `cover`, `exit`, `2`, `2`] strip_assume_tac) >>
  `loop n <= 2 + pop 2 n * cover n` by metis_tac[] >>
  `pop 2 n <= size n` by rw[pop_size] >>
  `pop 2 n * cover n <= size n * cover n` by rw[] >>
  `size n * cover n = 5 * size n ** 2` by rw[Abbr`cover`] >>
  decide_tac);

(* Theorem: stepsOf (sizeM n) <= 7 * (size n) ** 2 *)
(* Proof:
      stepsOf (sizeM n)
   <= 2 + 5 * (size n) ** 2          by sizeM_steps_upper
   <= (2 + 5) * (size n ** 2)        by dominant term
    = 7 * size n ** 2                by arithmetic
*)
val sizeM_steps_bound = store_thm(
  "sizeM_steps_bound",
  ``!n. stepsOf (sizeM n) <= 7 * (size n) ** 2``,
  rpt strip_tac >>
  `stepsOf (sizeM n) <= 2 + 5 * (size n) ** 2` by rw[sizeM_steps_upper] >>
  `0 < size n ** 2` by rw[] >>
  decide_tac);

(* Theorem: (stepsOf o sizeM) IN O_poly 2 *)
(* Proof:
   By O_poly_thm, this is to show:
      ?h k. !n. h < n ==> stepsOf (sizeM n) <= k * size n ** 2
   Note stepsOf (sizeM n) <= 7 * (size n) ** 2   by sizeM_steps_bound
   Take any h, k = 7.
*)
val sizeM_steps_O_poly = store_thm(
  "sizeM_steps_O_poly",
  ``(stepsOf o sizeM) IN O_poly 2``,
  rw[O_poly_thm] >>
  metis_tac[sizeM_steps_bound]);

(* Theorem: (stepsOf o sizeM) IN big_O (\n. (ulog n) ** 2) *)
(* Proof:
   Note (stepsOf o sizeM) IN O_poly 2     by sizeM_steps_O_poly
    and O_poly 2
      = big_O (POLY 2 o ulog)             by O_poly_eq_O_poly_ulog
      = (\n. ulog n ** 2)                 by POLY_def, FUN_EQ_THM
   The result follows.
*)
val sizeM_steps_big_O = store_thm(
  "sizeM_steps_big_O",
  ``(stepsOf o sizeM) IN big_O (\n. (ulog n) ** 2)``,
  assume_tac sizeM_steps_O_poly >>
  `O_poly 2 = big_O (POLY 2 o ulog)` by rw[O_poly_eq_O_poly_ulog] >>
  `POLY 2 o ulog = \n. ulog n ** 2` by rw[FUN_EQ_THM, POLY_def] >>
  fs[]);

(* Theorem: (valueOf (sizeM n) = size n) /\
            (stepsOf o sizeM) IN big_O (\n. (ulog n) ** 2) *)
(* Proof: by sizeM_value, sizeM_steps_big_O *)
val sizeM_thm = store_thm(
  "sizeM_thm",
  ``!n. (valueOf (sizeM n) = size n) /\
       (stepsOf o sizeM) IN big_O (\n. (ulog n) ** 2)``,
  metis_tac[sizeM_value, sizeM_steps_big_O]);

(* ------------------------------------------------------------------------- *)
(* Perfect-power in Monadic Style (by recursion)                             *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode: compute (?k. n = b ** k, or: is n a power of k?)
   power_of b n =
      if n = 0, return (b = 0).             // 0 can only be a power of 0.
      if n = 1, return T.                   // 1 can be a power of any base.
      if b = 0, return (n = 0) \/ (n = 1).  // only 0 or 1 is a power of 0.
      if b = 1, return (n = 1).             // only 1 is a power of 1.
      if n MOD b <> 0 return F              // false when not (b divides n)
      return (power_of (n DIV b) b)         // if b divides n,
                                            // check if (n DIV b) is a power of n.
*)

(*
> prefect_power_test |> SPEC ``n:num`` |> SPEC ``b:num``;
val it = |- perfect_power n b <=>
      if n = 0 then b = 0
      else if n = 1 then T
      else if b = 0 then n <= 1
      else if b = 1 then n = 1
      else if n MOD b = 0 then perfect_power (n DIV b) b
      else F: thm
*)

(* Define power_of monad *)
Definition power_ofM_def:
    power_ofM b n =
    do
       n0 <- zeroM n;
       n1 <- oneM n;
       b0 <- zeroM b;
       b1 <- oneM b;
       if n0 then return b0
       else if n1 then return T
       else if b0 then return (n0 \/ n1)
       else if b1 then return n1
       else do
              m' <- modM n b;
              gd <- zeroM m';
              if gd then
                 do
                    n' <- divM n b;
                    power_ofM b n';
                 od
              else return F
            od
    od
Termination WF_REL_TAC `measure SND` >> simp[]
End


(* Theorem: valueOf (power_ofM b n) = perfect_power n b *)
(* Proof:
   By induction based on power_ofM_def,
      matching perfect_power_test.
*)
val power_ofM_value = store_thm(
  "power_ofM_value[simp]",
  ``!b n. valueOf (power_ofM b n) = perfect_power n b``,
  ho_match_mp_tac (theorem "power_ofM_ind") >>
  rw[] >>
  rw[Once power_ofM_def, Once perfect_power_test] >>
  (Cases_on `n MOD b = 0` >> simp[]));

(* Theorem: stepsOf (power_ofM b n) = 2 * size n + 2 * size b +
     if (n = 0 \/ n = 1 \/ b = 0 \/ b = 1) then 0
     else (size n) * (size b) + size (n MOD b) + if (n MOD b <> 0) then 0
          else (size n) * (size b) + stepsOf (power_ofM b (n DIV b)) *)
(* Proof:
     stepsOf (power_ofM b n)
   = stepsOf (zeroM n) + stepsOf (zeroM b) + stepsOf (oneM b) +
     if n = 1 then 0 else if b = 0 then 0 else if b = 1 then 0
     else stepsOf (modM n b) + stepsOf (zeroM (n MOD b)) +
          if n MOD b = 0 then stepsOf (divM n b) + stepsOf (power_ofM b (n MOD b) else 0
                                by power_ofM_def
   = 2 * size n + 2 * size b +
     if (n = 0 \/ n = 1 \/ b = 0 \/ b = 1) then 0
     else (size n) * (size b) + size (n MOD b) +
          if (n MOD b <> 0) then 0
          else (size n) * (size b) + stepsOf (power_ofM b (n DIV b))
*)
val power_ofM_steps_thm = store_thm(
  "power_ofM_steps_thm",
  ``!b n. stepsOf (power_ofM b n) = 2 * size n + 2 * size b +
     if (n = 0 \/ n = 1 \/ b = 0 \/ b = 1) then 0
     else (size n) * (size b) + size (n MOD b) + if (n MOD b <> 0) then 0
          else (size n) * (size b) + stepsOf (power_ofM b (n DIV b))``,
  ho_match_mp_tac (theorem "power_ofM_ind") >>
  rpt strip_tac >>
  Cases_on `n = 0 \/ n = 1 \/ b = 0 \/ b = 1` >>
  rw[Once power_ofM_def]);

(* Theorem: 2 * (size n + size b) <= stepsOf (power_ofM b n) *)
(* Proof: by power_ofM_steps_thm *)
val power_ofM_steps_le = store_thm(
  "power_ofM_steps_le",
  ``!b n. 2 * (size n + size b) <= stepsOf (power_ofM b n)``,
  rw[Once power_ofM_steps_thm]);

(* Theorem: (stepsOf (power_ofM b 0) = 2 * (1 + size b)) /\
            (stepsOf (power_ofM b 1) = 2 * (1 + size b)) /\
            (stepsOf (power_ofM 0 n) = 2 * (1 + size n)) /\
            (stepsOf (power_ofM 1 n) = 2 * (1 + size n)) *)
(* Proof: by power_ofM_steps_thm *)
val power_ofM_steps_base = store_thm(
  "power_ofM_steps_base",
  ``!b n. (stepsOf (power_ofM b 0) = 2 * (1 + size b)) /\
         (stepsOf (power_ofM b 1) = 2 * (1 + size b)) /\
         (stepsOf (power_ofM 0 n) = 2 * (1 + size n)) /\
         (stepsOf (power_ofM 1 n) = 2 * (1 + size n))``,
  (rpt strip_tac >> rw[Once power_ofM_steps_thm]));

(* Theorem: let body n = 2 * size n + 2 * size b + if n <= 1 \/ b <= 1 then 0
                    else size n * size b + size (n MOD b) +
                         if n MOD b <> 0 then 0 else size n * size b;
                exit n = (n = 1 \/ b = 0 \/ b = 1 \/ n MOD b <> 0)
            in !n. 1 < b ==> (stepsOf (power_ofM b n) = if n = 0 then (2 + 2 * size b)
                   else body n + if exit n then 0 else stepsOf (power_ofM b (n DIV b))) *)
(* Proof:
     stepsOf (power_ofM b n)
   = 2 * size n + 2 * size b +
       if n = 0 \/ n = 1 \/ b = 0 \/ b = 1 then 0
       else size n * size b + size (n MOD b) +
            if n MOD b <> 0 then 0
            else size n * size b + (stepsOf o power_ofM b) (n DIV b)  by power_ofM_steps_thm
   = if n = 0 \/ n = 1 \/ b = 0 \/ b = 1
     then 2 * size n + 2 * size b
     else 2 * size n + 2 * size b + size n * size b + size (n MOD b) +
          if n MOD b <> 0 then 0 else size n * size b + (stepsOf o power_ofM b) (n DIV b)
   = if n = 0 then (2 * size 0 + 2 * size b)          for guard
     else if n = 0 \/ n = 1 \/ b = 0 \/ b = 1         for body cover
          then 2 * size n + 2 * size b
          else 2 * size n + 2 * size b + size n * size b + size (n MOD b) +
          if n MOD b <> 0 then 0 else size n * size b +
          if n = 1 \/ b = 0 \/ b = 1 \/ n MOD b <> 0 then 0    for exit
          else stepsOf (power_ofM b (n DIV b))
   = if n = 0 then (2 + 2 * size b)                   by size_0
     else 2 * size n + 2 * size b + if n <= 1 \/ b <= 1 then 0
          else size n * size b + size (n MOD b) + if n MOD b <> 0 then 0 else size n * size b +
          if n = 1 \/ b = 0 \/ b = 1 \/ n MOD b <> 0 then 0
          else stepsOf (power_ofM b (n DIV b))
*)
val power_ofM_steps_by_div_loop = store_thm(
  "power_ofM_steps_by_div_loop",
  ``!b. let body n = 2 * size n + 2 * size b + if n <= 1 \/ b <= 1 then 0
                    else size n * size b + size (n MOD b) +
                         if n MOD b <> 0 then 0 else size n * size b;
           exit n = (n = 1 \/ b = 0 \/ b = 1 \/ n MOD b <> 0)
        in !n. 1 < b ==> (stepsOf (power_ofM b n) = if n = 0 then (2 + 2 * size b)
                        else body n + if exit n then 0 else stepsOf (power_ofM b (n DIV b)))``,
  rw[Once power_ofM_steps_thm] >>
  (Cases_on `n = 0` >> simp[]));

(*
This puts power_ofM_steps in the category: dividing loop with body cover and exit.
   power_ofM_steps_by_div_loop:
        !n. loop n = if n = 0 then c else body n + if exit n then 0 else loop (n DIV b)
suitable for: loop_div_count_cover_exit_le
*)

(* Theorem: 1 < b ==> stepsOf (power_ofM b n) <=
            2 + 2 * size b + 3 * size b * size n + 2 * size n ** 2 + 2 * size b * size n ** 2 *)
(* Proof:
   If b <= 1,
      Then size b = 1                 by size_0, size_1
         stepsOf (power_ofM b n)
       = 2 * (1 + size n)             by power_ofM_steps_base
       = 2 + 2 * size n
       = 2 + 2 * size b * size n      by size b = 1
       Thus the inequality holds.
   If 1 < b,
   Let loop = (\n. stepsOf (power_ofM b n)),
       body = (\n. 2 * size n + 2 * size b + if n <= 1 \/ b <= 1 then 0
                  else size n * size b + size (n MOD b) +
                  if n MOD b <> 0 then 0 else size n * size b),
       cover = (\n. 3 * size b + 2 * size n + 2 * size n * size b),
       exit = (\n. n = 1 \/ b = 0 \/ b = 1 \/ n MOD b <> 0),
       c = 2 + 2 * size b.
   Then loop n = if n = 0 then c else body n + if exit n then 0 else loop (n DIV b)
                                                by power_ofM_steps_by_div_loop
   Claim: !n. body n <= cover n
   Proof: body n = 2 * size n + 2 * size b + if n <= 1 \/ b <= 1 then 0
                   else size n * size b + size (n MOD b) +
                   if n MOD b <> 0 then 0 else size n * size b
                <= 2 * size n + 2 * size b +
                   size n * size b + size (n MOD b) +
                   size n * size b
                <= 2 * size n + 2 * size b +
                   2 * size n * size b + size b   by MOD_LESS, size_monotone_lt
                 = 3 * size b + 2 * size n + 2 * size n * size b
                 = cover n

    Now !x. body x <= cover x            by claim
    and MONO cover                       by size_monotone_le
   Thus loop n
     <= c + pop 2 n * cover n            by loop_div_count_cover_exit_le
     <= c + size n * cover n             by pop_size
      = 2 + 2 * size b + size n * (3 * size b + 2 * size n + 2 * size n * size b)
      = 2 + 2 * size b + 3 * size b * size n + 2 * size n ** 2 + 2 * size b * size n ** 2
*)
val power_ofM_steps_upper = store_thm(
  "power_ofM_steps_upper",
  ``!b n. stepsOf (power_ofM b n) <=
         2 + 2 * size b + 3 * size b * size n + 2 * size n ** 2 + 2 * size b * size n ** 2``,
  rpt strip_tac >>
  Cases_on `b <= 1` >| [
    `size b = 1` by metis_tac[LE_ONE, size_0, size_1] >>
    `stepsOf (power_ofM b n) = 2 * (1 + size n)` by metis_tac[power_ofM_steps_base, LE_ONE] >>
    simp[],
    `1 < b` by decide_tac >>
    assume_tac power_ofM_steps_by_div_loop >>
    last_x_assum (qspec_then `b` strip_assume_tac) >>
    qabbrev_tac `loop = \n. stepsOf (power_ofM b n)` >>
    qabbrev_tac `body = \n. 2 * size n + 2 * size b + if n <= 1 \/ b <= 1 then 0
                       else size n * size b + size (n MOD b) +
                       if n MOD b <> 0 then 0 else size n * size b` >>
    qabbrev_tac `cover = \n. 3 * size b + 2 * size n + 2 * size n * size b` >>
    qabbrev_tac `exit = \n. n = 1 \/ b = 0 \/ b = 1 \/ n MOD b <> 0` >>
    qabbrev_tac `c = 2 + 2 * size b` >>
    qabbrev_tac `t = 3 * size b * size n + 2 * (size n ** 2) + 2 * size b * size n ** 2` >>
    `loop n <= c + t` suffices_by rw[Abbr`loop`, Abbr`t`] >>
    `!n. loop n = if n = 0 then c else body n + if exit n then 0 else loop (n DIV b)` by metis_tac[] >>
    `!x. body x <= cover x` by
  (rw[Abbr`body`, Abbr`cover`] >| [
      `x MOD b < b` by rw[] >>
      `size (x MOD b) <= size b` by rw[size_monotone_lt] >>
      decide_tac,
      `size (x MOD b) = 1` by rw[] >>
      `1 <= size b` by rw[one_le_size] >>
      decide_tac
    ]) >>
    `MONO cover` by
    (rw[Abbr`cover`] >>
    `size x <= size y` by rw[size_monotone_le] >>
    `size b * size x <= size b * size y` by rw[] >>
    decide_tac) >>
    imp_res_tac loop_div_count_cover_exit_le >>
    first_x_assum (qspec_then `n` strip_assume_tac) >>
    `pop b n * cover n <= t` by
      (`pop b n <= size n` by rw[pop_size] >>
    `pop b n * cover n <= size n * cover n` by rw[] >>
    `size n * cover n <= t` by rw[LEFT_ADD_DISTRIB, Abbr`cover`, Abbr`t`] >>
    decide_tac) >>
    decide_tac
  ]);

(* Theorem: stepsOf (power_ofM b n) <= 11 * size b * (size n) ** 2 *)
(* Proof:
      stepsOf (power_ofM b n)
   <= 2 + 2 * size b + 3 * size b * size n + 2 * size n ** 2 + 2 * size b * size n ** 2
                                                    by power_ofM_steps_upper
   <= (2 + 2 + 3 + 2 + 2) * size b * size n ** 2    by dominant term
    = 11 * size b * size n ** 2
*)
val power_ofM_steps_bound = store_thm(
  "power_ofM_steps_bound",
  ``!b n. stepsOf (power_ofM b n) <= 11 * size b * (size n) ** 2``,
  rpt strip_tac >>
  assume_tac power_ofM_steps_upper >>
  last_x_assum (qspecl_then [`b`, `n`] strip_assume_tac) >>
  qabbrev_tac `t = size b * size n ** 2` >>
  `stepsOf (power_ofM b n) <= 11 * t` suffices_by rw[Abbr`t`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `size b <= t` by
  (`size b <= size b * size n ** 2` by rw[MULT_POS] >>
  `size b * size n ** 2 = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size b * size n <= t` by
    (`size b * size n <= size b * size n * size n` by rw[MULT_POS] >>
  `size b * size n * size n = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `size n ** 2 <= t` by
      (`size n ** 2 <= size n ** 2 * size b` by rw[MULT_POS] >>
  `size n ** 2 * size b = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `(size b) * size n ** 2 = t` by rw[Abbr`t`] >>
  decide_tac);

(* Theorem: (stepsOf o power_twoM) IN O_poly 2 *)
(* Proof:
   By O_poly_thm, this is to show:
      ?h k. !n. h < n ==> stepsOf (power_ofM b n) <= k * size n ** 2
   Note stepsOf (power_ofM b n) <= 11 * size b * (size n) ** 2   by power_ofM_steps_bound
   Take any h, and k = 11 * size b.
   The result follows.
*)
val power_ofM_steps_O_poly = store_thm(
  "power_ofM_steps_O_poly",
  ``!b. (stepsOf o power_ofM b) IN O_poly 2``,
  rw[O_poly_thm] >>
  metis_tac[power_ofM_steps_bound]);

(* Theorem: (stepsOf o power_ofM b) IN big_O (\n. (ulog n) ** 2) *)
(* Proof:
   Note (stepsOf o power_ofM b) IN O_poly 2     by power_ofM_steps_O_poly
    and O_poly 2
      = big_O (POLY 2 o ulog)                   by O_poly_eq_O_poly_ulog
      = (\n. ulog n ** 2)                       by POLY_def, FUN_EQ_THM
   The result follows.
*)
val power_ofM_steps_big_O = store_thm(
  "power_ofM_steps_big_O",
  ``!b. (stepsOf o power_ofM b) IN big_O (\n. (ulog n) ** 2)``,
  assume_tac power_ofM_steps_O_poly >>
  `O_poly 2 = big_O (POLY 2 o ulog)` by rw[O_poly_eq_O_poly_ulog] >>
  `POLY 2 o ulog = \n. ulog n ** 2` by rw[FUN_EQ_THM, POLY_def] >>
  fs[]);

(* Theorem: (valueOf (power_ofM b n) <=> n power_of b) /\
            (stepsOf o power_ofM b) IN big_O (\n. size n) *)
(* Proof: by power_ofM_value, power_ofM_steps_big_O *)
val power_ofM_thm = store_thm(
  "power_ofM_thm",
  ``!b n. (valueOf (power_ofM b n) <=> n power_of b) /\
         (stepsOf o power_ofM b) IN big_O (\n. (ulog n) ** 2)``,
  metis_tac[power_ofM_value, power_ofM_steps_big_O]);

(* ------------------------------------------------------------------------- *)

(* Define the power_of_two monad *)
val power_twoM_def = Define `power_twoM = power_ofM 2`;

(*
> EVAL ``power_twoM 63``; = (F,Count 29): thm
> EVAL ``power_twoM 64``; = (T,Count 198): thm
> EVAL ``power_twoM 65``; = (F,Count 33): thm
*)

(* Theorem: valueOf (power_twoM n) = (perfect_power n 2) *)
(* Proof: by power_twoM_def, power_ofM_value *)
val power_twoM_value = store_thm(
  "power_twoM_value[simp]",
  ``!n. valueOf (power_twoM n) = (perfect_power n 2)``,
  rw[power_twoM_def]);

(* Obtain a theorem *)
val power_twoM_steps_thm = save_thm("power_twoM_steps_thm",
    power_ofM_steps_thm |> SPEC ``2`` |> SIMP_RULE (srw_ss()) [GSYM power_twoM_def, size_2]);
(* val power_twoM_steps_thm =
   |- !n. stepsOf (power_twoM n) =
          TWICE (size n) + 4 + if n = 0 \/ n = 1 then 0
          else size n * 2 + size (n MOD 2) +
               if n MOD 2 <> 0 then 0 else size n * 2 + stepsOf (power_ofM 2 (HALF n)): thm
*)

(* Theorem: stepsOf (power_twoM 0) = 6 *)
(* Proof: by power_twoM_steps_thm *)
val power_twoM_steps_0 = store_thm(
  "power_twoM_steps_0",
  ``stepsOf (power_twoM 0) = 6``,
  rw[Once power_twoM_steps_thm]);

(* Theorem: stepsOf (power_twoM 1) = 6 *)
(* Proof: by power_twoM_steps_thm *)
val power_twoM_steps_1 = store_thm(
  "power_twoM_steps_1",
  ``stepsOf (power_twoM 1) = 6``,
  rw[Once power_twoM_steps_thm]);

(* Derive theorems *)
val power_twoM_steps_O_poly = save_thm("power_twoM_steps_O_poly",
   power_ofM_steps_O_poly |> SPEC ``2`` |> SIMP_RULE (srw_ss()) [GSYM power_twoM_def]);
val power_twoM_steps_big_O = save_thm("power_twoM_steps_big_O",
   power_ofM_steps_big_O |> SPEC ``2`` |> SIMP_RULE (srw_ss()) [GSYM power_twoM_def]);
val power_twoM_thm = save_thm("power_twoM_thm",
   power_ofM_thm |> SPEC ``2`` |> SIMP_RULE (bool_ss) [GSYM power_twoM_def]); (* not srw_ss() *)
(*
val power_twoM_steps_upper = |- !n. stepsOf (power_twoM n) <= 6 + 6 * size n + TWICE (size n ** 2) + 4 * size n ** 2: thm
val power_twoM_steps_bound = |- !n. stepsOf (power_twoM n) <= 22 * size n ** 2: thm
val power_twoM_steps_O_poly = |- stepsOf o power_twoM IN O_poly 2: thm
val power_twoM_steps_big_O = |- stepsOf o power_twoM IN big_O (\n. ulog n ** 2): thm
val power_twoM_thm = |- !n. (valueOf (power_twoM n) <=> n power_of 2) /\
                            stepsOf o power_twoM IN big_O (\n. ulog n ** 2)
*)

(* Use theorems rather than transformations to have better constants than above. *)

(* Theorem: stepsOf (power_twoM n) <= 6 + 6 * size n + 6 * size n ** 2 *)
(* Proof: by power_twoM_steps_thm, power_twoM_def *)
val power_twoM_steps_upper = store_thm(
  "power_twoM_steps_upper",
  ``!n. stepsOf (power_twoM n) <= 6 + 6 * size n + 6 * size n ** 2``,
  rw[power_twoM_def] >>
  assume_tac power_ofM_steps_upper >>
  first_x_assum (qspecl_then [`2`, `n`] strip_assume_tac) >>
  fs[size_2]);

(* Note: power_twoM_steps_bound can therefore improve to:
        !n. stepsOf (power_twoM n) <= 18 * size n ** 2
*)

(* Theorem: stepsOf (power_ofM b n) <= 18 * (size n) ** 2 *)
(* Proof:
      stepsOf (power_twoM n)
   <= 6 + 6 * size n + 6 * size n ** 2  by power_twoM_steps_upper
   <= (6 + 6 + 6) * size n ** 2         by dominant term
    = 18 * size b * size n ** 2
*)
val power_twoM_steps_bound = store_thm(
  "power_twoM_steps_bound",
  ``!b n. stepsOf (power_twoM n) <= 18 * (size n) ** 2``,
  rpt strip_tac >>
  assume_tac power_twoM_steps_upper >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  `0 < (size n) ** 2` by rw[] >>
  `size n <= (size n) * (size n)` by rw[] >>
  `(size n) * (size n) = size n ** 2` by rw[] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)
(* Ulog in Monadic Style                                                     *)
(* ------------------------------------------------------------------------- *)
(* Pseudocode: compute (ulog n)
   ulog n =
      if n = 0, return 0              // ulog 0 = 0 is special.
      x <- size n                     // first, get (size n).
      if power_two n, return x - 1.   // if n is a power of 2, ulog n = size n - 1.
      return x.                       // otherwise, ulog n = size n.
*)

(* Define the ulog monad *)
val ulogM_def = Define`
    ulogM n =
      do
         gd <- zeroM n;
         if gd then return 0
         else do
                 x <- sizeM n;
                 b <- power_twoM n;
                 y <- boolM b;
                 subM x y;
              od
      od
`;

(*
> EVAL ``MAP ulogM [0 .. 5]``; =
      [(0,Count 1); (0,Count 11); (1,Count 39); (2,Count 29); (2,Count 77); (3,Count 48)]: thm
> EVAL ``MAP ulog [0 .. 5]``; = [0; 0; 1; 2; 2; 3]: thm
*)

(* Theorem: valueOf (ulogM n) = ulog n *)
(* Proof:
   By ulogM_def, this is to show:
   (1) 0 = ulog 0, true     by ulog_0
   (2) n <> 0 ==> size n - (if perfect_power n 2 then 1 else 0) = ulog n
       If perfect_power n 2,
           to show: size n - 1 = ulog n, true   by ulog_by_size
       Otherwise, show: size n = ulog n, true   by ulog_by_size
*)
val ulogM_value = store_thm(
  "ulogM_value[simp]",
  ``!n. valueOf (ulogM n) = ulog n``,
  rw[ulogM_def] >>
  (Cases_on `perfect_power n 2` >> rw[ulog_by_size]));

(* Theorem: stepsOf (ulogM n) =
            if n = 0 then 1
            else 1 + size n + size (size n) + stepsOf (sizeM n) + stepsOf (power_twoM n) *)
(* Proof:
     stepsOf (ulogM n)
   = stepsOf (zeroM n) + if (n = 0) then 0
     else stepsOf (sizeM n) +
          stepsOf (power_twoM n) +
          stepsOf (boolM (perfect_power n 2)) +
          stepsOf (subM (size n) (if (perfect_power n 2) then 1 else 0))
   = size n + if (n = 0) then 0
     else stepsOf (sizeM n) +
          stepsOf (power_twoM n) +
          1 + MAX (size (size n)) 1          by size_0 = 1, size_1 = 1
   = size n + if (n = 0) then 0
     else stepsOf (sizeM n) + stepsOf (power_twoM n) + 1 + size (size n)    by max_1_size_n
   = if n = 0 then size 0
     else 1 + size n + size (size n) + stepsOf (sizeM n) + stepsOf (power_twoM n)

   with (stepsOf o sizeM) IN O_poly 2        by sizeM_steps_O_poly
    and (stepsOf o power_twoM) IN O_poly 2   by power_twoM_steps_O_poly
*)
val ulogM_steps_thm = store_thm(
  "ulogM_steps_thm",
  ``!n. stepsOf (ulogM n) =
       if n = 0 then 1
       else 1 + size n + size (size n) + stepsOf (sizeM n) + stepsOf (power_twoM n)``,
  rw[ulogM_def] >>
  `MAX (size (size n)) 1 = size (size n)` by metis_tac[max_1_size_n, MAX_COMM] >>
  (Cases_on `perfect_power n 2` >> simp[]));

(* Obtain theorems *)
val ulogM_steps_0 = save_thm("ulogM_steps_0",
    ulogM_steps_thm |> SPEC ``0`` |> SIMP_RULE (srw_ss()) []);
(* val ulogM_steps_0 = |- stepsOf (ulogM 0) = 1: thm *)

val ulogM_steps_1 = save_thm("ulogM_steps_1",
    ulogM_steps_thm |> SPEC ``1`` |> SIMP_RULE (srw_ss()) [sizeM_steps_1, power_twoM_steps_1]);
(* val ulogM_steps_1 = |- stepsOf (ulogM 1) = 11: thm *)

(* Theorem: stepsOf (ulogM n) <= 9 + 8 * size n + 11 * (size n) ** 2 *)
(* Proof:
     stepsOf (ulogM n)
   = if n = 0 then 1 else 1 + size n + size (size n) +
                           stepsOf (sizeM n) + stepsOf (power_twoM n)   by ulogM_steps_thm
  <= 1 + size n + size n + stepsOf (sizeM n) + stepsOf (power_twoM n)   by size_le_self, size_monotone_le
  <= 1 + 2 * size n +
     (2 + 5 * size n ** 2) +              by sizeM_steps_upper
     (6 + 6 * size n + 6 * size n ** 2)   by power_twoM_steps_upper
   = 9 + 8 * size n + 11 * size n ** 2    by arithmetic
*)
val ulogM_steps_upper = store_thm(
  "ulogM_steps_upper",
  ``!n. stepsOf (ulogM n) <= 9 + 8 * size n + 11 * (size n) ** 2``,
  rpt strip_tac >>
  assume_tac ulogM_steps_thm >>
  last_x_assum (qspec_then `n` strip_assume_tac) >>
  qabbrev_tac `s = size n` >>
  `size s <= s` by rw[size_le_self, Abbr`s`] >>
  `stepsOf (ulogM n) <= 1 + 2 * s + stepsOf (sizeM n) + stepsOf (power_twoM n)` by rw[] >>
  `stepsOf (sizeM n) <= 2 + 5 * s ** 2` by rw[sizeM_steps_upper, Abbr`s`] >>
  `stepsOf (power_twoM n) <= 6 + 6 * s + 6 * s ** 2` by rw[power_twoM_steps_upper, Abbr`s`] >>
  decide_tac);

(* Theorem: stepsOf (ulogM n) <= 29 * (size n) ** 2 *)
(* Proof:
      stepsOf (ulogM n)
   <= 9 + 8 * size n + 11 * size n ** 2     by ulogM_steps_upper
   <= (9 + 8 + 11) * size n ** 2            by size_pos, MULT_POS
    = 28 * size n ** 2
*)
val ulogM_steps_bound = store_thm(
  "ulogM_steps_bound",
  ``!n. stepsOf (ulogM n) <= 28 * (size n) ** 2``,
  rpt strip_tac >>
  assume_tac ulogM_steps_upper >>
  last_x_assum (qspec_then `n` strip_assume_tac) >>
  qabbrev_tac `s = size n` >>
  `0 < s * s` by rw[MULT_POS, Abbr`s`] >>
  `s <= s * s` by rw[Abbr`s`] >>
  `s * s = s ** 2` by rw[] >>
  decide_tac);

(* Theorem: (stepsOf o ulogM) IN O_poly 2 *)
(* Proof:
   By O_poly_thm, this is to show:
      ?h k. !n. h < n ==> stepsOf (ulogM n) <= k * size n ** 2
   Note stepsOf (ulogM n) <= 28 * (size n) ** 2        by ulogM_steps_bound
   Take any h, set k = 28, the result follows.
*)
val ulogM_steps_O_poly = store_thm(
  "ulogM_steps_O_poly",
  ``(stepsOf o ulogM) IN O_poly 2``,
  rw[O_poly_thm] >>
  metis_tac[ulogM_steps_bound]);

(* Theorem: (stepsOf o ulogM) IN big_O (\n. (ulog n) ** 2) *)
(* Proof:
   Note (stepsOf o ulogM) IN O_poly 2     by ulogM_steps_O_poly
    and O_poly 2
      = big_O (POLY 2 o ulog)             by O_poly_eq_O_poly_ulog
      = (\n. ulog n ** 2)                 by POLY_def, FUN_EQ_THM
   The result follows.
*)
val ulogM_steps_big_O = store_thm(
  "ulogM_steps_big_O",
  ``(stepsOf o ulogM) IN big_O (\n. (ulog n) ** 2)``,
  assume_tac ulogM_steps_O_poly >>
  `O_poly 2 = big_O (POLY 2 o ulog)` by rw[O_poly_eq_O_poly_ulog] >>
  `POLY 2 o ulog = \n. ulog n ** 2` by rw[FUN_EQ_THM, POLY_def] >>
  fs[]);

(* Theorem: (valueOf (ulogM n) = ulog n) /\
            (stepsOf o ulogM) IN big_O (\n. (ulog n) ** 2) *)
(* Proof: by ulogM_value, ulogM_steps_big_O *)
val ulogM_thm = store_thm(
  "ulogM_thm",
  ``!n. (valueOf (ulogM n) = ulog n) /\
       (stepsOf o ulogM) IN big_O (\n. (ulog n) ** 2)``,
  metis_tac[ulogM_value, ulogM_steps_big_O]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
