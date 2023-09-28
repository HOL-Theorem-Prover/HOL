(* ------------------------------------------------------------------------- *)
(* Modulo Computations with Count Monad                                      *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "countModulo";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* val _ = load "SatisfySimps"; (* for SatisfySimps.SATISFY_ss *) *)

(* Get dependent theories local *)
(* val _ = load "countMacroTheory"; *)
open countMonadTheory countMacroTheory;

open bitsizeTheory complexityTheory;
open loopIncreaseTheory loopDecreaseTheory;
open loopDivideTheory loopMultiplyTheory;

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
open helperNumTheory helperSetTheory helperListTheory;
open helperFunctionTheory;

(* (* val _ = load "dividesTheory"; -- in helperNumTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperNumTheory *) *)
open pred_setTheory listTheory arithmeticTheory;
open dividesTheory gcdTheory;

(* (* val _ = load "logPowerTheory"; *) *)
open logrootTheory logPowerTheory;

(*
(* val _ = load "computeBasicTheory"; *)
open computeBasicTheory; (* for exp_mod_eqn *)
*)

(* (* val _ = load "monadsyntax"; *) *)
open monadsyntax;
open pairTheory optionTheory;
open listRangeTheory;

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "Count";


(* ------------------------------------------------------------------------- *)
(* Modulo Computations with Count Monad Documentation                        *)
(* ------------------------------------------------------------------------- *)
(* Data type:
*)
(* Overloading:
*)
(* Definitions and Theorems (# are exported):

   Helper:

   Modular Arithmetic Operations:
   maddM_def           |- !m x y. maddM m x y = do z <- addM x y; modM z m od
#  maddM_value         |- !m x y. valueOf (maddM m x y) = (x + y) MOD m
#  maddM_steps         |- !m x y. stepsOf (maddM m x y) = size (MAX x y) + size (x + y) * size m
   maddM_steps_upper   |- !m x y. stepsOf (maddM m x y) <= size m + (1 + size m) * size (MAX x y)
   maddM_steps_bound   |- !m x y. stepsOf (maddM m x y) <= 3 * size m * size (MAX x y)

   msubM_def           |- !m x y. msubM m x y = do z <- subM x y; modM z m od
#  msubM_value         |- !m x y. valueOf (msubM m x y) = (x - y) MOD m
#  msubM_steps         |- !m x y. stepsOf (msubM m x y) = size (MAX x y) + size (x - y) * size m
   msubM_steps_upper   |- !m x y. stepsOf (msubM m x y) <= size m * size x + size (MAX x y)
   msubM_steps_bound   |- !m x y. stepsOf (msubM m x y) <= TWICE (size m) * size (MAX x y)

   mmulM_def           |- !m x y. mmulM m x y = do z <- mulM x y; modM z m od
#  mmulM_value         |- !m x y. valueOf (mmulM m x y) = (x * y) MOD m
#  mmulM_steps         |- !m x y. stepsOf (mmulM m x y) = size x * size y + size (x * y) * size m
   mmulM_steps_upper   |- !m x y. stepsOf (mmulM m x y) <= size m * (size x + size y) + size x * size y
   mmulM_steps_bound   |- !m x y. stepsOf (mmulM m x y) <= 3 * size m * size x * size y

   msqM_def            |- !m x. msqM m x = mmulM m x x
#  msqM_value          |- !m x. valueOf (msqM m x) = SQ x MOD m
#  msqM_steps          |- !m x. stepsOf (msqM m x) = SQ (size x) + size (SQ x) * size m
   msqM_steps_upper    |- !m x. stepsOf (msqM m x) <= TWICE (size m * size x) + size x ** 2
   msqM_steps_bound    |- !m x. stepsOf (msqM m x) <= 3 * (size m * size x ** 2)

   Modular Exponentiation:
   mexpM_def           |- !n m b. mexpM m b n =
                                  do
                                    m0 <- zeroM m;
                                    m1 <- oneM m;
                                    gd <- zeroM n;
                                    if m0 \/ m1 then unit (b ** n MOD m)
                                    else if gd then 1c
                                    else
                                      do
                                        b' <- msqM m b;
                                        n' <- halfM n;
                                        r <- mexpM m b' n';
                                        ifM (evenM n) (return r) (mmulM m b r)
                                      od
                                  od
#  mexpM_value         |- !m b n. valueOf (mexpM m b n) = b ** n MOD m
   mexpM_steps_thm     |- !m b n. stepsOf (mexpM m b n) =
                                  if m <= 1 \/ n = 0 then TWICE (size m) + size n
                                  else 1 + 5 * size n + size b ** 2 + TWICE (size m) +
                                       size (SQ b) * size m +
                                       (if EVEN n then 0
                                        else size b * size (SQ b ** HALF n MOD m) +
                                             size (b * SQ b ** HALF n MOD m) * size m) +
                                       stepsOf (mexpM m (SQ b MOD m) (HALF n))
   mexpM_steps_base    |- !m b n. stepsOf (mexpM 0 b n) = 2 + size n /\
                                  stepsOf (mexpM 1 b n) = 2 + size n /\
                                  stepsOf (mexpM m b 0) = 1 + TWICE (size m)
   mexpM_steps_by_sqmod_div_loop
                       |- !m. (let body b n = if m <= 1 then TWICE (size m) + size n
                                       else 1 + 5 * size n + size b ** 2 + TWICE (size m) +
                                            size (SQ b) * size m + if EVEN n then 0
                                            else size b * size (SQ b ** HALF n MOD m) +
                                                 size (b * SQ b ** HALF n MOD m) * size m
                                in !b n. stepsOf (mexpM m b n) = if n = 0 then 1 + TWICE (size m)
                                         else body b n + if m <= 1 then 0
                                              else stepsOf (mexpM m (SQ b MOD m) (HALF n)))
   mexpM_body_upper    |- !m. (let body b n = if m <= 1 then TWICE (size m) + size n
                                       else 1 + 5 * size n + size b ** 2 + TWICE (size m) +
                                            size (SQ b) * size m + if EVEN n then 0
                                            else size b * size (SQ b ** HALF n MOD m) +
                                                 size (b * SQ b ** HALF n MOD m) * size m
                                in !b n. body b n <= 1 + TWICE (size m) + 5 * size n +
                                                     4 * size m * size b + size b ** 2 + size m ** 2)
   mexpM_body_bound    |- !m. (let body b n = if m <= 1 then TWICE (size m) + size n
                                       else 1 + 5 * size n + size b ** 2 + TWICE (size m) +
                                            size (SQ b) * size m + if EVEN n then 0
                                            else size b * size (SQ b ** HALF n MOD m) +
                                                 size (b * SQ b ** HALF n MOD m) * size m
                                in !b n. body b n <= 14 * size n * size b ** 2 * size m ** 2)
   mexpM_steps_upper   |- !m b n. stepsOf (mexpM m b n) <= 1 + TWICE (size m) +
                                    14 * size n ** 2 * size m ** 2 * size (MAX b m) ** 2
   mexpM_steps_bound   |- !m b n. stepsOf (mexpM m b n) <=
                                    17 * size n ** 2 * size m ** 2 * size (MAX b m) ** 2
   mexpM_steps_O_base  |- !m b. stepsOf o mexpM m b IN
                                big_O (POLY 1 o (\n. size n ** 2 * size m ** 2 * size (MAX b m) ** 2))
   mexpM_steps_O_poly  |- !m b. stepsOf o mexpM m b IN O_poly 2
   mexpM_steps_O_swap  |- !m n. stepsOf o combin$C (mexpM m) n IN big_O (POLY 1 o (\b. size (MAX b m) ** 2))
   mexpM_steps_big_O   |- !m b. stepsOf o mexpM m b IN big_O (\n. ulog n ** 2)
   mexpM_thm           |- !m b n. (valueOf (mexpM m b n) = b ** n MOD m) /\
                                  stepsOf o mexpM m b IN big_O (\n. ulog n ** 2)

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
(* Modular Arithmetic Operations                                             *)
(* ------------------------------------------------------------------------- *)

(* Define modular addition: (x + y) MOD m *)
val maddM_def = Define`
    maddM m x y =
       do
          z <- addM x y;
          modM z m;
       od
`;

(* Theorem: valueOf(maddM m x y) = (x + y) MOD m *)
(* Proof: by maddM_def *)
val maddM_value = store_thm(
  "maddM_value[simp]",
  ``!m x y. valueOf(maddM m x y) = (x + y) MOD m``,
  simp[maddM_def]);

(* Theorem: stepsOf(maddM m x y) = size (MAX x y) + size (x + y) * size m *)
(* Proof:
     stepsOf(maddM m x y)
   = stepsOf(addM x y) + stepsOf(modM (x + y) m)     by maddM_def
   = size (MAX x y) + (size (x + y) * size m)        by size_max, modM_steps
*)
val maddM_steps = store_thm(
  "maddM_steps[simp]",
  ``!m x y. stepsOf(maddM m x y) = size (MAX x y) + size (x + y) * size m``,
  simp[maddM_def, size_max]);

(* Theorem: stepsOf(maddM m x y) <= size m + (1 + size m) * size (MAX x y) *)
(* Proof:
      stepsOf(maddM m x y)
    = size (MAX x y) + size (x + y) * size m             by maddM_steps
   <= size (MAX x y) + (1 + size (MAX x y)) * size m     by size_add_upper
    = t + (1 + t) * size m        where t = size (MAX x y)
    = size m + (1 + size m) * t                          by arithmetic
*)
val maddM_steps_upper = store_thm(
  "maddM_steps_upper",
  ``!m x y. stepsOf(maddM m x y) <= size m + (1 + size m) * size (MAX x y)``,
  rpt strip_tac >>
  assume_tac maddM_steps >>
  first_x_assum (qspecl_then [`m`, `x`, `y`] strip_assume_tac) >>
  qabbrev_tac `t = size (MAX x y)` >>
  `size (x + y) <= 1 + t` by rw[size_add_upper, Abbr`t`] >>
  `t + size m * size (x + y) <= t + size m * (1 + t)` by rw[] >>
  `t + size m * (1 + t) = t + size m + t * size m` by rw[] >>
  `t + size m + t * size m = size m + (1 + size m) * t` by rw[] >>
  decide_tac);

(* Theorem: stepsOf(maddM m x y) <= 3 * size m * size (MAX x y) *)
(* Proof:
      stepsOf(maddM m x y)
   <= size m + (1 + size m) * size (MAX x y)    by maddM_steps_upper
    = size m + size (MAX x y) + size m * size (MAX x y)
   <= (1 + 1 + 1) * size m * size (MAX x y)     by dominant term
    = 3 * size m * size (MAX x y)
*)
val maddM_steps_bound = store_thm(
  "maddM_steps_bound",
  ``!m x y. stepsOf(maddM m x y) <= 3 * size m * size (MAX x y)``,
  rpt strip_tac >>
  assume_tac maddM_steps_upper >>
  first_x_assum (qspecl_then [`m`, `x`, `y`] strip_assume_tac) >>
  qabbrev_tac `h = size (MAX x y)` >>
  qabbrev_tac `t = size m * h` >>
  `stepsOf (maddM m x y) <= 3 * t` suffices_by rw[Abbr`t`] >>
  `size m + (1 + size m) * h = size m + h + t` by rw[Abbr`t`] >>
  `size m <= t` by
  (`0 < h` by rw[Abbr`h`] >>
  rw[Abbr`t`]) >>
  `h <= t` by
    (`h <= size m * h` by rw[] >>
  rw[Abbr`h`, Abbr`t`]) >>
  decide_tac);

(* ------------------------------------------------------------------------- *)

(* Define modular subtraction: (x - y) MOD m *)
val msubM_def = Define`
    msubM m x y =
       do
          z <- subM x y;
          modM z m;
       od
`;

(* Theorem: valueOf(msubM m x y) = (x - y) MOD m *)
(* Proof: by msubM_def *)
val msubM_value = store_thm(
  "msubM_value[simp]",
  ``!m x y. valueOf(msubM m x y) = (x - y) MOD m``,
  simp[msubM_def]);

(* Theorem: stepsOf(msubM m x y) = size (MAX x y) + size (x - y) * size m *)
(* Proof:
     stepsOf(msubM m x y)
   = stepsOf(subM x y) + stepsOf(modM (x - y) m) by msubM_def
   = size (MAX x y) + size (x - y) * size m      by size_max, modM_steps
*)
val msubM_steps = store_thm(
  "msubM_steps[simp]",
  ``!m x y. stepsOf(msubM m x y) = size (MAX x y) + size (x - y) * size m``,
  simp[msubM_def, size_max]);

(* Theorem: stepsOf(msubM m x y) <= size m * size x + size (MAX x y) *)
(* Proof:
      stepsOf(msubM m x y)
    = size (MAX x y) + size (x - y) * size m      by msubM_steps
   <= size (MAX x y) + size x * size m            by size_monotone_le
*)
val msubM_steps_upper = store_thm(
  "msubM_steps_upper",
  ``!m x y. stepsOf(msubM m x y) <= size m * size x + size (MAX x y)``,
  rpt strip_tac >>
  assume_tac msubM_steps >>
  last_x_assum (qspecl_then [`m`, `x`, `y`] strip_assume_tac) >>
  qabbrev_tac `t = size (MAX x y)` >>
  rw[size_monotone_le]);

(* Theorem: stepsOf(msubM m x y) <= 2 * size m * size (MAX x y) *)
(* Proof:
      stepsOf(msubM m x y)
   <= size m * size x + size (MAX x y)    by msubM_steps_upper
    = size m * size (MAX x y) + size (MAX x y)
   <= (1 + 1) * size m * size (MAX x y)   by dominant term
    = 2 * size m * size (MAX x y)
*)
val msubM_steps_bound = store_thm(
  "msubM_steps_bound",
  ``!m x y. stepsOf(msubM m x y) <= 2 * size m * size (MAX x y)``,
  rpt strip_tac >>
  assume_tac msubM_steps_upper >>
  first_x_assum (qspecl_then [`m`, `x`, `y`] strip_assume_tac) >>
  qabbrev_tac `h = size (MAX x y)` >>
  qabbrev_tac `t = size m * h` >>
  `stepsOf (msubM m x y) <= 2 * t` suffices_by rw[Abbr`t`] >>
  `size m * size x <= t` by
  (`size x <= h` by rw[size_monotone_le, Abbr`h`] >>
  rw[Abbr`t`]) >>
  `h <= t` by
    (`h <= size m * h` by rw[] >>
  rw[Abbr`h`, Abbr`t`]) >>
  decide_tac);

(* ------------------------------------------------------------------------- *)

(* Define modular multiplication: (x * y) MOD m *)
val mmulM_def = Define`
    mmulM m x y =
       do
          z <- mulM x y;
          modM z m;
       od
`;

(* Theorem: valueOf(mmulM m x y) = (x * y) MOD m *)
(* Proof: by mmulM_def *)
val mmulM_value = store_thm(
  "mmulM_value[simp]",
  ``!m x y. valueOf(mmulM m x y) = (x * y) MOD m``,
  simp[mmulM_def]);

(* Theorem: stepsOf(mmulM m x y) = (size x) * (size y) + size (x * y) * size m *)
(* Proof:
     stepsOf(mmulM m x y)
   = stepsOf(mulM x y) + stepsOf(modM (x * y) m)   by mmulM_def
   = (size x) * (size y) + size (x * y) * size m      by multM_steps, modM_steps
*)
val mmulM_steps = store_thm(
  "mmulM_steps[simp]",
  ``!m x y. stepsOf(mmulM m x y) = (size x) * (size y) + size (x * y) * size m``,
  simp[mmulM_def]);

(* Theorem: stepsOf(mmulM m x y) <= size m * size x + size (MAX x y) *)
(* Proof:
      stepsOf(mmulM m x y)
   <= (size x) (size y) + size (x * y) * size m         by mmulM_steps
   <= (size x) (size y) + (size x + size y) * size m    by size_mult_upper
*)
val mmulM_steps_upper = store_thm(
  "mmulM_steps_upper",
  ``!m x y. stepsOf(mmulM m x y) <= size m * (size x + size y) + (size x) * (size y)``,
  rpt strip_tac >>
  assume_tac mmulM_steps >>
  last_x_assum (qspecl_then [`m`, `x`, `y`] strip_assume_tac) >>
  qabbrev_tac `sx = size x` >>
  qabbrev_tac `sy = size y` >>
  qabbrev_tac `sm = size m` >>
  rw[size_mult_upper, Abbr`sx`, Abbr`sy`]);

(* Theorem: stepsOf(mmulM m x y) <= 3 * size m * size x * size y *)
(* Proof:
      stepsOf(mmulM m x y)
   <= size m * (size x + size y) + size x * size y   by mmulM_steps_upper
    = size m * size x + size m * size y + size x * size y
   <= (1 + 1 + 1) * size m * size x * size y         by dominant term
    = 3 * size m * size x * size y
*)
val mmulM_steps_bound = store_thm(
  "mmulM_steps_bound",
  ``!m x y. stepsOf(mmulM m x y) <= 3 * size m * size x * size y``,
  rpt strip_tac >>
  assume_tac mmulM_steps_upper >>
  last_x_assum (qspecl_then [`m`, `x`, `y`] strip_assume_tac) >>
  qabbrev_tac `t = size m * size x * size y` >>
  `stepsOf (mmulM m x y) <= 3 * t` suffices_by rw[Abbr`t`] >>
  `size m * (size x + size y) + size x * size y = size m * size x + size m * size y + size x * size y` by rw[] >>
  `size m * size x <= t` by rw[Abbr`t`] >>
  `size m * size y <= t` by rw[Abbr`t`] >>
  `size x * size y <= t` by rw[Abbr`t`] >>
  decide_tac);

(* ------------------------------------------------------------------------- *)

(* Define modular square *)
val msqM_def = Define`
    msqM m x = mmulM m x x
`;

(* Obtain theorems *)
val msqM_value = save_thm("msqM_value[simp]",
    mmulM_value |> SPEC ``m:num`` |> SPEC ``x:num`` |> SPEC ``x:num``
                |> REWRITE_RULE [GSYM msqM_def] |> GEN ``x:num`` |> GEN ``m:num``);
(* val msqM_value = |- !m x. valueOf (msqM m x) = SQ x MOD m: thm *)

val msqM_steps = save_thm("msqM_steps[simp]",
    mmulM_steps |> SPEC ``m:num`` |> SPEC ``x:num`` |> SPEC ``x:num``
                |> REWRITE_RULE [GSYM msqM_def] |> GEN ``x:num`` |> GEN ``m:num``);
(* val msqM_steps = |- !m x. stepsOf (msqM m x) = SQ (size x) + size (SQ x) * size m: thm *)

val msqM_steps_upper = save_thm("msqM_steps_upper",
    mmulM_steps_upper |> SPEC ``m:num`` |> SPEC ``x:num`` |> SPEC ``x:num``
                |> SIMP_RULE arith_ss [GSYM msqM_def] |> GEN ``x:num`` |> GEN ``m:num``);
(* val msqM_steps_upper =
   |- !m x. stepsOf (msqM m x) <= TWICE (size m * size x) + size x ** 2: thm
*)

val msqM_steps_bound = save_thm("msqM_steps_bound",
    mmulM_steps_bound |> SPEC ``m:num`` |> SPEC ``x:num`` |> SPEC ``x:num``
                |> SIMP_RULE arith_ss [GSYM msqM_def] |> GEN ``x:num`` |> GEN ``m:num``);
(* val msqM_steps_bound =
   |- !m x. stepsOf (msqM m x) <= 3 * (size m * size x ** 2): thm
*)

(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Modular Exponentiation (Repeated Squares Method)                          *)
(* ------------------------------------------------------------------------- *)
(* Fast Exponentiation -- recursive form.
   (b ** n) MOD m =
      if (n = 0) then return 1 MOD m.
      let result = (b * b) ** (HALF n) MOD m
       in if EVEN n then return result
                    else return (b * result) MOD m
*)

(* Fast Exponentiation -- iterative form *)
(* Pseudocode: compute (b ** n)
   b ** n = r <- 1 MOD m
            loop:
            if (n == 0) return r
            if (ODD n) r <- (r * b) MOD m
            n <- HALF n
            b <- (SQ b) MOD m
            goto loop
*)

(*
val EXP_MOD_EQN = |- !b n m. 1 < m ==>
          b ** n MOD m =
          if n = 0 then 1
          else (let result = SQ b ** HALF n MOD m
                 in if EVEN n then result else (b * result) MOD m): thm
*)

(* Define modular exponentiation: (b ** n) MOD m *)
Definition mexpM_def:
  mexpM m b n =
      do
         m0 <- zeroM m;
         m1 <- oneM m;
         gd <- zeroM n;
         if m0 \/ m1 then return ((b ** n) MOD m)
         else if gd then return 1
         else do
                 b' <- msqM m b;
                 n' <- halfM n;
                 r  <- mexpM m b' n';
                 ifM (evenM n) (return r) (mmulM m b r);
              od
      od
Termination WF_REL_TAC `measure (λ(m,b,n). n)` >> simp[]
End

(*
> EVAL ``MAP (mexpM 7 2) [0 .. 10]``; =
        [(1,Count 7); (2,Count 40); (4,Count 85); (1,Count 103); (2,Count 116); (4,Count 129);
         (1,Count 134); (2,Count 142); (4,Count 171); (1,Count 189); (2,Count 195)]
*)


(* Theorem: valueOf (mexpM m b n) = (b ** n) MOD m *)
(* Proof: by induction from mexpM_def, matching EXP_MOD_EQN. *)
Theorem mexpM_value[simp]:
  !m b n. valueOf (mexpM m b n) = (b ** n) MOD m
Proof
  ho_match_mp_tac (theorem "mexpM_ind") >> rw[] >>
  rw[Once mexpM_def] >>
  `0 < m /\ 1 < m` by decide_tac >>
  assume_tac EXP_MOD_EQN >>
  first_x_assum (qspecl_then [`b`, `n`, `m`] strip_assume_tac) >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  fs[GSYM EXP_2]
QED

(* Theorem: stepsOf (mexpM m b n) = if m <= 1 \/ n = 0 then 2 * size m + size n
            else 1 + 5 * size n + (size b) ** 2 + 2 * size m + size (b * b) * size m +
             (if EVEN n then 0 else (size b * size (((b * b) ** (HALF n)) MOD m) + size (b * ((b * b) ** (HALF n) MOD m)) * size m)) +
             stepsOf (mexpM m ((b * b) MOD m) (HALF n)) *)
(* Proof:
     stepsOf (mexpM m b n)
   = stepsOf (zeroM m) + stepsOf (oneM m) + stepsOf (zeroM n) + if m <= 1 \/ n = 0 then 0
     else stepsOf (msqM m b) +
          stepsOf (halfM n) +
          stepsOf (mexpM m ((b * b) MOD m) (HALF n)) +
          stepsOf (evenM n) +
          if EVEN n then stepsOf (return ((b * b) ** (HALF n) MOD m))
                    else stepsOf (mmulM m b ((b * b) ** (HALF n) MOD m))
   = 2 * size m + size n + if m <= 1 \/ n = 0 then 0
     else (size b) ** 2 + size (b * b) * size m +
          2 * size n +
          stepsOf (mexpM m ((b * b) MOD m) (HALF n)) +
          2 * size n + 1 +
          if EVEN n then 0 else (size b * size (((b * b) ** (HALF n)) MOD m)) + size (b * ((b * b) ** (HALF n) MOD m)) * size m)
  = if m <= 1 \/ n = 0 then 2 * size m + size n
    else 2 * size m + (size b) ** 2 + size (b * b) * size m + 3 * size n + 2 * size n + 1 +
         if EVEN n then 0 else (size b * size (((b * b) ** (HALF n)) MOD m) + size (b * ((b * b) ** (HALF n) MOD m)) * size m) +
          stepsOf (mexpM m ((b * b) MOD m) (HALF n))
  = if m <= 1 \/ n = 0 then 2 * size m + size n
    else 1 + 5 * size n + (size b) ** 2 + 2 * size m + size (b * b) * size m +
         (if EVEN n then 0 else (size b * size (((b * b) ** (HALF n)) MOD m) + size (b * ((b * b) ** (HALF n) MOD m)) * size m)) +
         stepsOf (mexpM m ((b * b) MOD m) (HALF n))
*)
val mexpM_steps_thm = store_thm(
  "mexpM_steps_thm",
  ``!m b n. stepsOf (mexpM m b n) = if m <= 1 \/ n = 0 then 2 * size m + size n
     else 1 + 5 * size n + (size b) ** 2 + 2 * size m + size (b * b) * size m +
          (if EVEN n then 0 else (size b * size (((b * b) ** (HALF n)) MOD m) + size (b * ((b * b) ** (HALF n) MOD m)) * size m)) +
          stepsOf (mexpM m ((b * b) MOD m) (HALF n))``,
  ho_match_mp_tac (theorem "mexpM_ind") >>
  (rw[] >> simp[Once mexpM_def]) >-
  (Cases_on `m = 0 \/ m = 1` >> simp[]) >-
  (Cases_on `m = 0 \/ m = 1` >> simp[]) >>
  (Cases_on `m = 0 \/ m = 1` >> simp[]));

(* Theorem: stepsOf (expM b 0) = 1 *)
(* Proof: by expM_steps_thm *)
val mexpM_steps_base = store_thm(
  "mexpM_steps_base",
  ``!m b n. (stepsOf (mexpM 0 b n) = 2 + size n) /\
           (stepsOf (mexpM 1 b n) = 2 + size n) /\
           (stepsOf (mexpM m b 0) = 1 + 2 * size m)``,
  (rw[Once mexpM_steps_thm] >> rw[Once mexpM_steps_thm]));

(*
mexpM_steps_thm |> SPEC ``m:num`` |> SPEC ``b:num`` |> SPEC ``1`` |> SIMP_RULE (srw_ss()) [EXP_0];
val it = |- stepsOf (mexpM m b 1) = if m <= 1 then TWICE (size m) + 1
      else 6 + size b ** 2 + TWICE (size m) + size (SQ b) * size m +
           (size b * size (1 MOD m) + size (b * 1 MOD m) * size m) + stepsOf (mexpM m (SQ b MOD m) 0): thm
*)

(* Theorem: let body b n = if m <= 1 then 2 * size m + size n else
                  1 + 5 * size n + size b ** 2 + 2 * size m + size (SQ b) * size m +
                  if EVEN n then 0 else
                     size b * size (SQ b ** HALF n MOD m) + size (b * SQ b ** HALF n MOD m) * size m
             in !b n. stepsOf (mexpM m b n) =
                      if n = 0 then 1 + 2 * size m else body b n +
                      if m <= 1 then 0 else stepsOf (mexpM m ((b * b) MOD m) (HALF n)) *)
(* Proof:
     stepsOf (mexpM m b n)
   = if m <= 1 \/ n = 0 then 2 * size m + size n else
     1 + 5 * size n + size b ** 2 + 2 * size m + size (SQ b) * size m +
     (if EVEN n then 0 else
         size b * size (SQ b ** HALF n MOD m) + size (b * SQ b ** HALF n MOD m) * size m) +
     stepsOf (mexpM m (SQ b MOD m) (HALF n))        by mexpM_steps_thm
   = if n = 0 then 2 * size m + size n else
     if m <= 1 then 2 * size m + size n else
     1 + 5 * size n + size b ** 2 + 2 * size m + size (SQ b) * size m +
     (if EVEN n then 0 else
         size b * size (SQ b ** HALF n MOD m) + size (b * SQ b ** HALF n MOD m) * size m) +
     stepsOf (mexpM m (SQ b MOD m) (HALF n))
   = if n = 0 then 1 + 2 * size m else
     (if m <= 1 then 2 * size m + size n else
     1 + 5 * size n + size b ** 2 + 2 * size m + size (SQ b) * size m +
     if EVEN n then 0 else
         size b * size (SQ b ** HALF n MOD m) + size (b * SQ b ** HALF n MOD m) * size m) +
     if m <= 1 then 0 else stepsOf (mexpM m (SQ b MOD m) (HALF n))
*)
val mexpM_steps_by_sqmod_div_loop = store_thm(
  "mexpM_steps_by_sqmod_div_loop",
  ``!m. let body b n = if m <= 1 then 2 * size m + size n else
             1 + 5 * size n + size b ** 2 + 2 * size m + size (SQ b) * size m +
             if EVEN n then 0 else
                size b * size (SQ b ** HALF n MOD m) + size (b * SQ b ** HALF n MOD m) * size m
        in !b n. stepsOf (mexpM m b n) =
                 if n = 0 then 1 + 2 * size m else body b n +
                 if m <= 1 then 0 else stepsOf (mexpM m ((b * b) MOD m) (HALF n))``,
  rw[Once mexpM_steps_thm] >>
  rw[]);

(*
This puts mexpM_steps in the category: halving loop with body cover and exit, RISING sqmod.
   mexpM_steps_by_sqmod_div_loop:
        !b n. loop b n = if n = 0 then quit b else body b n + if exit b n then 0 else loop (SQ b MOD m) (HALF n)
suitable for: loop2_div_mono_count_cover_exit_le
*)

(* First work out a cover for the complicated body. *)

(* Theorem: let body b n = if m <= 1 then 2 * size m + size n else
                  1 + 5 * size n + size b ** 2 + 2 * size m + size (SQ b) * size m +
                  if EVEN n then 0 else
                     size b * size (SQ b ** HALF n MOD m) + size (b * SQ b ** HALF n MOD m) * size m
            in !b n. body b n <=
                     1 + 2 * size m + 5 * size n + 4 * size m * size b + (size b) ** 2 + (size m) ** 2 *)
(* Proof:
      body n
    = if m <= 1 then 2 * size m + size n else
               1 + 5 * size n + size b ** 2 + 2 * size m + size (SQ b) * size m +
               if EVEN n then 0 else
                  size b * size (SQ b ** HALF n MOD m) + size (b * SQ b ** HALF n MOD m) * size m
   <= 1 + 5 * size n + size b ** 2 + 2 * size m + size (b * b) * size m +
      size b * size k + size (b * k) * size m    where k = SQ b ** HALF n MOD m.
   Note k < m                by MOD_LESS, 0 < m
   Note size k <= size m     by size_monotone_lt
   Thus body n
     <= 1 + 5sn + sb ** 2 + 2sm + sm * size (b * b) + sb * sm + sm * size (b * m)
     <= 1 + 5sn + sb ** 2 + 2sm + sm * (sb + sb) + sb * sm + sm * (sb + sm)     by size_mult_upper
      = 1 + 5sn + sb ** 2 + 2sm + 2 * sm * sb + sb * sm + sm * sb + sm * sm
      = 1 + 5sn + sb ** 2 + 2sm + 4 * sm * sb + sm ** 2
      = 1 + 2sm + 5sn + 4 sm sb + sb ** 2 + sm ** 2
*)
val mexpM_body_upper = store_thm(
  "mexpM_body_upper",
  ``!m. let body b n = if m <= 1 then 2 * size m + size n else
               1 + 5 * size n + size b ** 2 + 2 * size m + size (SQ b) * size m +
               if EVEN n then 0 else
                  size b * size (SQ b ** HALF n MOD m) + size (b * SQ b ** HALF n MOD m) * size m
        in !b n. body b n <=
                 1 + 2 * size m + 5 * size n + 4 * size m * size b + (size b) ** 2 + (size m) ** 2``,
  rw[] >>
  (Cases_on `m <= 1` >> rw[]) >| [
    `size (b ** 2) <= 2 * size b` by metis_tac[size_sq_upper, EXP_2] >>
    `size m * size (b ** 2) <= size m * (2 * size b)` by rw[] >>
    decide_tac,
    qabbrev_tac `k = (b ** 2) ** HALF n MOD m` >>
    `k < m` by rw[Abbr`k`] >>
    `size k <= size m` by rw[size_monotone_lt] >>
    `size (b * k) <= size b + size k` by rw[size_mult_upper] >>
    `size m * size (b * k) <= size m * (size b + size k)` by rw[] >>
    `size m * (size b + size k) = size m * size b + size m * size k` by rw[] >>
    `size (b ** 2) <= 2 * size b` by metis_tac[size_sq_upper, EXP_2] >>
    `size m * size (b ** 2) <= size m * (2 * size b)` by rw[] >>
    `size b * size k <= size b * size m` by rw[] >>
    `size m * size k <= size m * size m` by rw[] >>
    `size m * size m = size m ** 2` by rw[] >>
    decide_tac
  ]);

(* Theorem: let body b n = if m <= 1 then 2 * size m + size n else
               1 + 5 * size n + size b ** 2 + 2 * size m + size (SQ b) * size m +
               if EVEN n then 0 else
                  size b * size (SQ b ** HALF n MOD m) + size (b * SQ b ** HALF n MOD m) * size m
            in !b n. body b n <= 14 * (size n) * (size b) ** 2 * (size m) ** 2 *)
(* Proof:
      body b n
   <= 1 + 2 * size m + 5 * size n + 4 * size m * size b + (size b) ** 2 + (size m) ** 2
                                                          by mexpM_body_upper
   <= (1 + 2 + 5 + 4 + 1 + 1) * (size n) * (size b) ** 2 * (size m) ** 2
                                                          by dominant term
    = 14 * (size n) * (size b) ** 2 * (size m) ** 2       by arithmetic
*)
val mexpM_body_bound = store_thm(
  "mexpM_body_bound",
  ``!m. let body b n = if m <= 1 then 2 * size m + size n else
               1 + 5 * size n + size b ** 2 + 2 * size m + size (SQ b) * size m +
               if EVEN n then 0 else
                  size b * size (SQ b ** HALF n MOD m) + size (b * SQ b ** HALF n MOD m) * size m
        in !b n. body b n <= 14 * (size n) * (size b) ** 2 * (size m) ** 2``,
  rpt strip_tac >>
  assume_tac mexpM_body_upper >>
  last_x_assum (qspec_then `m` strip_assume_tac) >>
  qabbrev_tac `body = \b n. if m <= 1 then 2 * size m + size n else
               1 + 5 * size n + size b ** 2 + 2 * size m + size (SQ b) * size m +
               if EVEN n then 0 else
                  size b * size (SQ b ** HALF n MOD m) + size (b * SQ b ** HALF n MOD m) * size m` >>
  `!b n. body b n <= 14 * size n * size b ** 2 * size m ** 2` suffices_by fs[] >>
  rpt strip_tac >>
  `body b n <= 1 + 2 * size m + 5 * size n + 4 * size m * size b + size b ** 2 + size m ** 2` by metis_tac[] >>
  qabbrev_tac `sm = size m` >>
  qabbrev_tac `sb = size b` >>
  qabbrev_tac `sn = size n` >>
  qabbrev_tac `t = sn * sb ** 2 * sm ** 2` >>
  `body b n <= 14 * t` suffices_by rw[Abbr`t`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`, Abbr`sm`, Abbr`sb`, Abbr`sn`] >>
  `1 <= t` by decide_tac >>
  `sm <= t` by
  (`sm <= sm * (sn * sb ** 2 * sm)` by rw[MULT_POS, Abbr`sn`, Abbr`sb`, Abbr`sm`] >>
  `sm * (sn * sb ** 2 * sm) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `sn <= t` by
    (`sn <= sn * (sb ** 2 * sm ** 2)` by rw[MULT_POS, Abbr`sb`, Abbr`sm`] >>
  `sn * (sb ** 2 * sm ** 2) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `sm * sb <= t` by
      (`sm * sb <= sm * sb * (sn * sb * sm)` by rw[MULT_POS,Abbr`sn`, Abbr`sb`, Abbr`sm`] >>
  `sm * sb * (sn * sb * sm) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `sb ** 2 <= t` by
        (`sb ** 2 <= sb ** 2 * (sn * sm ** 2)` by rw[MULT_POS,Abbr`sn`, Abbr`sm`] >>
  `sb ** 2 * (sn * sm ** 2) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  `sm ** 2 <= t` by
          (`sm ** 2 <= sm ** 2 * (sn * sb ** 2)` by rw[MULT_POS,Abbr`sn`, Abbr`sb`] >>
  `sm ** 2 * (sn * sb ** 2) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  decide_tac);

(* Note:

In the following proof of the mexpM_steps upper bound,
it almost works by the simple loop2_div_rise_count_cover_exit_le,
except that f = (\b. (b * b) MOD m) is not exactly RISING f.
This is because the successive FUNPOW values are: x, (x * x) MOD m = y, (y * y) MOD m = z, etc.
While x <= x * x <= (x * x) * (x * x), ....
It is not clear how:  x <= (x * x) MOD m <= ((x * x) * (x * x)) MOD m   can maintain.

The trick to overcome this difficulty is to have a cover for f, using g = (\b. MAX b m).
This works because the terms are:
     x, (x ** 2) MOD m,  (x ** 4) MOD m, ....
Since all the MOD m are bounded by m, every term (including the first) is bounded by MAX x m.
Tracing that the result comes from: loop2_div_steps_sum_le
we can estimate the sum as long as each term is covered in some way.
The modified result is given in: loop2_div_mono_count_cover_exit_le
*)

(* Theorem: stepsOf (mexpM m b n) <=
            1 + 2 * size m + 14 * (size n) ** 2 * (size m) ** 2 * (size (MAX b m)) ** 2 *)
(* Proof:
   Let body = (\b n. if m <= 1 then 2 * size m + size n else
               1 + 5 * size n + size b ** 2 + 2 * size m + size (SQ b) * size m +
               if EVEN n then 0 else
                  size b * size (SQ b ** HALF n MOD m) + size (b * SQ b ** HALF n MOD m) * size m),
       cover = (\b n. 14 * (size n) * (size b) ** 2 * (size m) ** 2),
       exit = (\n. m <= 1),
       f = (\b. (b * b) MOD m),
       g = (\b. MAX b m),
       c = 1 + 2 * size m,
       loop = (\b n. stepsOf (mexpM m b n)),
       quit = (\b. c).
   The goal is: loop b n <= c + 1 + 2 * size m + 14 * (size n) ** 2 * (size m) ** 2 * (size (MAX b m)) ** 2

   If m = 0,
      Then loop b n = 2 + size n          by mexpM_steps_base
       and RHS
         = c + 14 * (size n * 1 * MAX (size b) 1) ** 2
         = 1 + 2 + 14 * (size n * size b) ** 2   by max_1_size_n
         = 3 + 14 * (size n * size b) ** 2 > LHS.

   If n = 0,
      Then loop b n = 1 + 2 * size m      by mexpM_steps_base
                    = c                   by notation
      Hence true.

   If m <> 0 and n <> 0,
      Need 0 < n applies later for exact pop_2_size
       and 0 < m applies later for MOD_LESS

   Note !b n. loop b n = if n = 0 then quit b else body b n + if exit n then 0 else loop (f b) (HALF n)
                                              by mexpM_steps_by_sqmod_div_loop
    and !x y. body x y <= cover x y           by mexpM_body_bound
    and MONO2 cover                           by size_monotone_le, LE_MONO_MULT2
    and !x. f x <= g x                        by MOD_LESS, MAX_DEF, 0 < m
    and MONO g                                by MAX_DEF
    and RISING g                              by MAX_DEF
   Let z = FUNPOW f (pop 2 n) b.

   Thus loop b n
     <= quit z + pop 2 n * cover (FUNPOW g (pop 2 n) b) n  by loop2_div_mono_count_cover_exit_le
      = c + size n * cover (FUNPOW g (size n) b) n         by pop_2_size, 0 < n
      = c + size n * (cover k n)                           where k = FUNPOW g (size n) b
   Note k = FUNPOW g (size n) b
          = FUNPOW (\b. MAX b m) (size n) b           by notation
          = MAX b m                                   by FUNPOW_MAX, 0 < size n
    so size k = size (MAX b m).

        loop b n
     <= c + size n * (cover k n)
      = c + size n * (14 * size n * (size k * size m) ** 2)       by notation for cover
      = (1 + 2 * size m) + 14 * (size k * size n * size m) ** 2   by notation for c
      = 1 + 2 * size m + 14 * (size n) ** 2 * (size m) ** 2 * (size (MAX b m)) ** 2
*)
val mexpM_steps_upper = store_thm(
  "mexpM_steps_upper",
  ``!m b n. stepsOf (mexpM m b n) <=
           1 + 2 * size m + 14 * (size n) ** 2 * (size m) ** 2 * (size (MAX b m)) ** 2``,
  rpt strip_tac >>
  assume_tac mexpM_steps_by_sqmod_div_loop >>
  last_x_assum (qspec_then `m` strip_assume_tac) >>
  assume_tac mexpM_body_bound >>
  first_x_assum (qspec_then `m` strip_assume_tac) >>
  qabbrev_tac `body = \b n. if m <= 1 then 2 * size m + size n
                  else 1 + 5 * size n + size b ** 2 + 2 * size m +
                    size (SQ b) * size m + if EVEN n then 0
                    else size b * size (SQ b ** HALF n MOD m) +
                         size (b * SQ b ** HALF n MOD m) * size m` >>
  qabbrev_tac `cover = \b n. 14 * (size n) * (size b) ** 2 * (size m) ** 2` >>
  qabbrev_tac `exit = \b:num n:num. m <= 1` >>
  qabbrev_tac `c = 1 + 2 * size m` >>
  qabbrev_tac `f = \b. (b * b) MOD m` >>
  qabbrev_tac `g = \b. MAX b m` >>
  qabbrev_tac `loop = \b n. stepsOf (mexpM m b n)` >>
  qabbrev_tac `quit = \b:num. c` >>
  `loop b n <= c + 14 * (size n) ** 2 * (size m) ** 2 * (size (MAX b m)) ** 2` suffices_by rw[Abbr`loop`] >>
  `!b n. loop b n = if n = 0 then quit b else body b n + if exit b n then 0 else loop (f b) (HALF n)` by metis_tac[] >>
  Cases_on `m = 0` >| [
    `loop b n = 2 + size n` by metis_tac[mexpM_steps_base] >>
    simp[Abbr`c`] >>
    `0 < size n * (size (g b)) ** 2` by rw[MULT_POS] >>
    `size n <= size n * (size n * (size (g b)) ** 2)` by rw[] >>
    `size n * (size n * (size (g b)) ** 2) = size n ** 2 * (size (g b)) ** 2` by rw[] >>
    decide_tac,
    Cases_on `n = 0` >| [
      `loop b n = c` by metis_tac[] >>
      decide_tac,
      `!x y. body x y <= cover x y` by metis_tac[] >>
      `MONO2 cover` by rw[size_monotone_le, LE_MONO_MULT2, Abbr`cover`] >>
      `!x. f x <= g x` by
  (rw[Abbr`f`, Abbr`g`] >>
      `x ** 2 MOD m < m` by rw[MOD_LESS] >>
      decide_tac) >>
      `MONO g` by rw[Abbr`g`] >>
      `RISING g` by rw[Abbr`g`] >>
      `1 < 2` by decide_tac >>
      imp_res_tac loop2_div_mono_count_cover_exit_le >>
      first_x_assum (qspecl_then [`n`, `b`] strip_assume_tac) >>
      `pop 2 n * cover (FUNPOW g (pop 2 n) b) n =
       14 * size n ** 2 * size m ** 2 * size (MAX b m) ** 2` by
    (`pop 2 n = size n` by rw[pop_2_size] >>
      rw[Abbr`cover`, Abbr`g`] >>
      `0 < size n` by rw[] >>
      `FUNPOW (\b. MAX b m) (size n) b = MAX b m` by rw[FUNPOW_MAX] >>
      simp[]) >>
      metis_tac[]
    ]
  ]);

(* Theorem: stepsOf (mexpM m b n) <= 17 * size n ** 2 * size m ** 2 * size (MAX b m) ** 2 *)
(* Proof:
      stepsOf (mexpM m b n)
   <= 1 + 2 * size m + 14 * size n ** 2 * size m ** 2 * size (MAX b m) ** 2  by mexpM_steps_upper
   <= (1 + 2 + 14) * size n ** 2 * size m ** 2 * size (MAX b m) ** 2         by dominant term
    = 17 * size n ** 2 * size m ** 2 * size (MAX b m) ** 2                   by arithmetic
*)
val mexpM_steps_bound = store_thm(
  "mexpM_steps_bound",
  ``!m b n. stepsOf (mexpM m b n) <= 17 * size n ** 2 * size m ** 2 * size (MAX b m) ** 2``,
  rpt strip_tac >>
  assume_tac mexpM_steps_upper >>
  last_x_assum (qspecl_then [`m`, `b`, `n`] strip_assume_tac) >>
  qabbrev_tac `t = size n ** 2 * size m ** 2 * size (MAX b m) ** 2` >>
  `stepsOf (mexpM m b n) <= 17 * t` suffices_by rw[Abbr`t`] >>
  `0 < t` by rw[MULT_POS, Abbr`t`] >>
  `1 <= t` by decide_tac >>
  `size m <= t` by
  (`size m <= size m * (size m * size n ** 2 * size (MAX b m) ** 2)` by rw[MULT_POS] >>
  `size m * (size m * size n ** 2 * size (MAX b m) ** 2) = t` by rw[Abbr`t`] >>
  decide_tac) >>
  qunabbrev_tac `t` >>
  decide_tac);

(* Theorem: stepsOf o (mexpM m b) IN
            big_O (POLY 1 o (\n. size n ** 2 * size m ** 2 * size (MAX b m) ** 2)) *)
(* Proof: by big_O_def, POLY_def, mexpM_steps_bound *)
val mexpM_steps_O_base = store_thm(
  "mexpM_steps_O_base",
  ``!m b. stepsOf o (mexpM m b) IN
         big_O (POLY 1 o (\n. size n ** 2 * size m ** 2 * size (MAX b m) ** 2))``,
  rw[big_O_def, POLY_def] >>
  `!n. 17 * size n ** 2 * size m ** 2 * size (MAX b m) ** 2 =
        17 * size m ** 2 * size n ** 2 * size (MAX b m) ** 2` by decide_tac >>
  metis_tac[mexpM_steps_bound]);

(* Theorem: stepsOf o (mexpM m b) IN O_poly 2 *)
(* Proof: by O_poly_thm, mexpM_steps_bound *)
val mexpM_steps_O_poly = store_thm(
  "mexpM_steps_O_poly",
  ``!m b. stepsOf o (mexpM m b) IN O_poly 2``,
  rw[O_poly_thm] >>
  `!n. 17 * size n ** 2 * size m ** 2 * size (MAX b m) ** 2 =
        17 * size m ** 2 * size (MAX b m) ** 2 * size n ** 2` by decide_tac >>
  metis_tac[mexpM_steps_bound]);

(* Theorem: stepsOf o (combin$C (mexpM m) n) IN big_O (POLY 1 o (\b. (size (MAX b m)) ** 2)) *)
(* Proof: by big_O_def, POLY_def, mexpM_steps_bound *)
val mexpM_steps_O_swap = store_thm(
  "mexpM_steps_O_swap",
  ``!m n. stepsOf o (combin$C (mexpM m) n) IN big_O (POLY 1 o (\b. (size (MAX b m)) ** 2))``,
  rw[big_O_def, POLY_def] >>
  metis_tac[mexpM_steps_bound]);

(* Theorem: stepsOf o (mexpM m b) IN big_O (\n. (ulog n) ** 2) *)
(* Proof:
   Note stepsOf o (mexpM m b) IN O_poly 2     by mexpM_steps_O_poly
    and O_poly 2
      = big_O (POLY 2 o ulog)                 by O_poly_eq_O_poly_ulog
      = (\n. ulog n ** 2)                     by POLY_def, FUN_EQ_THM
   The result follows.
*)
val mexpM_steps_big_O = store_thm(
  "mexpM_steps_big_O",
  ``!m b. stepsOf o (mexpM m b) IN big_O (\n. (ulog n) ** 2)``,
  assume_tac mexpM_steps_O_poly >>
  `O_poly 2 = big_O (POLY 2 o ulog)` by rw[O_poly_eq_O_poly_ulog] >>
  `POLY 2 o ulog = \n. ulog n ** 2` by rw[FUN_EQ_THM, POLY_def] >>
  fs[]);

(* Theorem: (valueOf (mexpM m b n) = b ** n MOD m) /\
            (stepsOf o parityM) IN big_O (\n. size n) *)
(* Proof: by mexpM_value, mexpM_steps_big_O *)
val mexpM_thm = store_thm(
  "mexpM_thm",
  ``!m b n. (valueOf (mexpM m b n) = b ** n MOD m) /\
       stepsOf o (mexpM m b) IN big_O (\n. (ulog n) ** 2)``,
  metis_tac[mexpM_value, mexpM_steps_big_O]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
