(* ------------------------------------------------------------------------- *)
(* Macros of Count Monad                                                     *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "countMacro";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory listTheory rich_listTheory arithmeticTheory dividesTheory
     gcdTheory numberTheory combinatoricsTheory pairTheory optionTheory
     listRangeTheory primeTheory;

open bitsizeTheory complexityTheory;

open loopIncreaseTheory loopDecreaseTheory;
open loopDivideTheory loopMultiplyTheory loopListTheory;

open countMonadTheory;

(* val _ = load "monadsyntax"; *)
open monadsyntax;

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "Count";

val _ = temp_overload_on("SQ", ``\n. n * n``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

(* ------------------------------------------------------------------------- *)
(* Macros of Count Monad Documentation                                       *)
(* ------------------------------------------------------------------------- *)
(* Data type:
*)
(* Overloading:
   FUN_POS f  = !x. 0 < f x
   O_poly n   = big_O ((POLY n) o size)
   add_    = app2 addM
   sub_    = app2 subM
   mul_    = app2 mulM
   div_    = app2 divM
   mod_    = app2 modM
   eq_     = app2 eqM
   id_     = app1 idM
   null_   = app1 nullM
   head_   = app1 headM
   tail_   = app1 tailM
   cons_   = app2 consM

   parity_ = app1 parityM
   even_   = app1 evenM
   half_   = app1 halfM
   sq_     = app1 sqM
   inc_    = app1 incM
   dec_    = app1 decM
   twice_  = app1 twiceM
   leq_    = app2 leqM
   lt_     = app2 ltM
   gt1_    = app1 gt1M
*)
(* Definitions and Theorems (# are exported):

   Helper:

   Constructors:
   make_0M_def     |- make_0M = do tick 1; 0c od
   make_FM_def     |- make_FM = do tick 1; unit F od
   make_nilM_def   |- make_nilM = do tick 1; unit [] od

#  make_0M_value   |- valueOf make_0M = 0
#  make_FM_value   |- valueOf make_FM <=> F
#  make_nilM_value |- valueOf make_nilM = []

#  make_0M_steps   |- stepsOf make_0M = 1
#  make_FM_steps   |- stepsOf make_FM = 1
#  make_nilM_steps |- stepsOf make_nilM = 1

   Identity:
   idM_def       |- !x. idM x = do tick 0; unit x od
#  idM_value     |- !x. valueOf (idM x) = x
#  idM_steps     |- !x. stepsOf (idM x) = 0

   Basic Arithmetic:
   addM_def      |- !x y. addM x y = do tick (MAX (size x) (size y)); unit (x + y) od
   subM_def      |- !x y. subM x y = do tick (MAX (size x) (size y)); unit (x - y) od
   mulM_def      |- !x y. mulM x y = do tick (size x * size y); unit (x * y) od
   divM_def      |- !x y. divM x y = do tick (size x * size y); unit (x DIV y) od
   modM_def      |- !x y. modM x y = do tick (size x * size y); unit (x MOD y) od

#  addM_value    |- !x y. valueOf (addM x y) = x + y
#  subM_value    |- !x y. valueOf (subM x y) = x - y
#  mulM_value    |- !x y. valueOf (mulM x y) = x * y
#  divM_value    |- !x y. valueOf (divM x y) = x DIV y
#  modM_value    |- !x y. valueOf (modM x y) = x MOD y

#  addM_steps    |- !x y. stepsOf (addM x y) = MAX (size x) (size y)
#  subM_steps    |- !x y. stepsOf (subM x y) = MAX (size x) (size y)
#  mulM_steps    |- !x y. stepsOf (mulM x y) = size x * size y
#  divM_steps    |- !x y. stepsOf (divM x y) = size x * size y
#  modM_steps    |- !x y. stepsOf (modM x y) = size x * size y

   Basic List:
   nullM_def     |- !ls. nullM ls = do tick 1; unit (ls = []) od
   headM_def     |- !ls. headM ls = do tick 1; unit (HD ls) od
   tailM_def     |- !ls. tailM ls = do tick 1; unit (TL ls) od
   consM_def     |- !x ls. consM x ls = do tick 1; unit (x::ls) od

#  nullM_value   |- !ls. valueOf (nullM ls) <=> ls = []
#  headM_value   |- !ls. valueOf (headM ls) = HD ls
#  tailM_value   |- !ls. valueOf (tailM ls) = TL ls
#  consM_value   |- !x ls. valueOf (consM x ls) = x::ls

#  nullM_steps   |- !ls. stepsOf (nullM ls) = 1
#  headM_steps   |- !ls. stepsOf (headM ls) = 1
#  tailM_steps   |- !ls. stepsOf (tailM ls) = 1
#  consM_steps   |- !x ls. stepsOf (consM x ls) = 1

   Basic Boolean:
   eqM_def       |- !x y. eqM x y = do tick (MAX (size x) (size y)); unit (x = y) od
   notM_def      |- !b. notM b = do tick 1; unit (~b) od
   boolM_def     |- !b. boolM b = do tick 1; unit (if b then 1 else 0) od

#  eqM_value     |- !x y. valueOf (eqM x y) <=> x = y
#  notM_value    |- !b. valueOf (notM b) <=> ~b
#  boolM_value   |- !b. valueOf (boolM b) = if b then 1 else 0
#  eqM_steps     |- !x y. stepsOf (eqM x y) = MAX (size x) (size y)
#  notM_steps    |- !b. stepsOf (notM b) = 1
#  boolM_steps   |- !b. stepsOf (boolM b) = 1

   Macro Monads:
   zeroM_def     |- !n. zeroM n = eqM n 0
#  zeroM_value   |- !n. valueOf (zeroM n) <=> n = 0
#  zeroM_steps   |- !n. stepsOf (zeroM n) = size n
   zeroM_cc      |- (\n. stepsOf (zeroM n)) IN big_O size
   zeroM_poly_cc |- (\n. stepsOf (zeroM n)) IN big_O (POLY 1 o size)
   zeroM_steps_big_O
                 |- stepsOf o zeroM IN big_O (\n. ulog n)
   zeroM_thm     |- !n. (valueOf (zeroM n) <=> n = 0) /\
                        stepsOf o zeroM IN big_O (\n. ulog n)

   oneM_def      | - !n. oneM n = eqM 1 n
#  oneM_value    |- !n. valueOf (oneM n) <=> n = 1
#  oneM_steps    |- !n. stepsOf (oneM n) = size n
   oneM_cc       |- (\n. stepsOf (oneM n)) IN big_O size
   oneM_poly_cc  |- (\n. stepsOf (oneM n)) IN O_poly 1
   oneM_steps_big_O
                 |- stepsOf o oneM IN big_O (\n. ulog n)
   oneM_thm      |- !n. (valueOf (oneM n) <=> n = 1) /\
                         stepsOf o oneM IN big_O (\n. ulog n)

   twiceM_def    |- !n. twiceM n = mulM n 2
   twiceM_cc     |- (\n. stepsOf (twiceM n)) IN big_O size
   twiceM_poly_cc|- (\n. stepsOf (twiceM n)) IN O_poly 1
#  twiceM_value  |- !n. valueOf (twiceM n) = TWICE n
#  twiceM_steps  |- !n. stepsOf (twiceM n) = TWICE (size n)
   twiceM_steps_big_O
                 |- stepsOf o twiceM IN big_O (\n. ulog n)
   twiceM_thm    |- !n. (valueOf (twiceM n) = TWICE n) /\
                        stepsOf o twiceM IN big_O (\n. ulog n)

   halfM_def     |- !n. halfM n = divM n 2
   halfM_cc      |- (\n. stepsOf (halfM n)) IN big_O size
#  halfM_value   |- !n. valueOf (halfM n) = HALF n
#  halfM_steps   |- !n. stepsOf (halfM n) = TWICE (size n)
   halfM_steps_big_O
                 |- stepsOf o halfM IN big_O (\n. ulog n)
   halfM_thm     |- !n. (valueOf (halfM n) = HALF n) /\
                        stepsOf o halfM IN big_O (\n. ulog n)

   parityM_def   |- !n. parityM n = modM n 2
#  parityM_value |- !n. valueOf (parityM n) = n MOD 2
#  parityM_steps |- !n. stepsOf (parityM n) = TWICE (size n)
   parityM_cc    |- (\n. stepsOf (parityM n)) IN big_O size
   parityM_poly_cc  |- (\n. stepsOf (parityM n)) IN big_O (POLY 1 o size)
   parity_cc     |- (\n. n MOD 2) IN big_O (K 1)
   parityM_steps_big_O
                 |- stepsOf o parityM IN big_O (\n. ulog n)
   parityM_thm   |- !n. (valueOf (parityM n) = n MOD 2) /\
                        stepsOf o parityM IN big_O (\n. ulog n)

   evenM_def     |- !n. evenM n = do z <- parityM n; zeroM z od
#  evenM_value   |- !n. valueOf (evenM n) <=> EVEN n
#  evenM_steps   |- !n. stepsOf (evenM n) = TWICE (size n) + 1
   evenM_cc      |- (\n. stepsOf (evenM n)) IN big_O size
   zeroM_parity_cc
                 |- (\n. stepsOf (zeroM (n MOD 2))) IN big_O (K 1)
   evenM_steps_big_O
                 |- stepsOf o evenM IN big_O (\n. ulog n)
   evenM_thm     |- !n. (valueOf (evenM n) <=> EVEN n) /\
                        stepsOf o evenM IN big_O (\n. ulog n)

   sqM_def       |- !n. sqM n = mulM n n
#  sqM_value     |- !n. valueOf (sqM n) = SQ n
#  sqM_steps     |- !n. stepsOf (sqM n) = size n ** 2
   sqM_poly_cc   |- (\n. stepsOf (sqM n)) IN big_O (POLY 2 o size)
   mulM_poly_cc  |- !z. (\(x,y). stepsOf (mulM x y)) z <
                        (POLY 2 o (\(x,y). 1 + MAX (size x) (size y))) z
   sqM_steps_big_O
                 |- stepsOf o sqM IN big_O (\n. ulog n ** 2)
   sqM_thm       |- !n. (valueOf (sqM n) = SQ n) /\
                        stepsOf o sqM IN big_O (\n. ulog n ** 2)

   incM_def      |- !n. incM n = addM n 1
   incM_cc       |- (\n. stepsOf (incM n)) IN O_poly 1
#  incM_value    |- !n. valueOf (incM n) = n + 1
#  incM_steps    |- !n. stepsOf (incM n) = size n
   incM_steps_big_O
                 |- stepsOf o incM IN big_O (\n. ulog n)
   incM_thm      |- !n. (valueOf (incM n) = n + 1) /\
                        stepsOf o incM IN big_O (\n. ulog n)

   decM_def      |- !n. decM n = subM n 1
   decM_cc       |- (\n. stepsOf (decM n)) IN O_poly 1
#  decM_value    |- !n. valueOf (decM n) = n - 1
#  decM_steps    |- !n. stepsOf (decM n) = size n
   decM_steps_big_O
                 |- stepsOf o decM IN big_O (\n. ulog n)
   decM_thm      |- !n. (valueOf (decM n) = n - 1) /\
                        stepsOf o decM IN big_O (\n. ulog n)

   leqM_def      |- !n m. leqM n m = do z <- subM n m; zeroM z od
#  leqM_value    |- !n m. valueOf (leqM n m) <=> n <= m
#  leqM_steps    |- !n m. stepsOf (leqM n m) = MAX (size n) (size m) + size (n - m)
   leqM_steps_alt|- !n m. stepsOf (leqM n m) = size (MAX n m) + size (n - m)
   leqM_steps_le |- !n m. stepsOf (leqM n m) <= TWICE (size (MAX n m))
   leqM_poly_cc  |- !z. (\(n,m). stepsOf (leqM n m)) z ** 2 =
                        (POLY 2 o (\(n,m). size (n - m) + MAX (size n) (size m))) z

   ltM_def       |- !n m. ltM n m = do b <- eqM n m; if b then unit F else leqM n m od
#  ltM_value     |- !n m. valueOf (ltM n m) <=> n < m
#  ltM_steps     |- !n m. stepsOf (ltM n m) =
                          if n = m then size n else TWICE (MAX (size n) (size m)) + size (n - m)
   ltM_poly_cc   |- !z. (\(n,m). stepsOf (ltM n m)) z ** 1 =
                        (POLY 1 o (\(n,m). if n = m then size n
                                           else size (n - m) + TWICE (MAX (size n) (size m)))) z
   gt1M_def      |- !n. gt1M n = ltM 1 n
#  gt1M_value    |- !n. valueOf (gt1M n) <=> 1 < n
#  gt1M_steps    |- !n. stepsOf (gt1M n) = if n = 1 then 1 else 1 + TWICE (size n)

   le1M_def      |- !n. le1M n = do gd <- gt1M n; notM gd od
#  le1M_value    |- !n. valueOf (le1M n) <=> n <= 1
#  le1M_steps    |- !n. stepsOf (le1M n) = if n = 1 then 2 else 2 + TWICE (size n)

   appendM_def   |- !l2 l1. appendM l1 l2 =
                            do
                              gd <- nullM l1;
                              if gd then unit l2
                              else
                                do
                                  h <- headM l1;
                                  t <- tailM l1;
                                  ls <- appendM t l2;
                                  consM h ls
                                od
                            od
#  appendM_value |- !l1 l2. valueOf (appendM l1 l2) = l1 ++ l2:
   snocM_def     |- !x ls. snocM x ls =
                           do
                             gd <- nullM ls;
                             if gd then consM x ls
                             else
                               do h <- headM ls; t <- tailM ls; l <- snocM x t; consM h l od
                           od
#  snocM_value   |- !x ls. valueOf (snocM x ls) = SNOC x ls

*)

(* Eliminate parenthesis around equality *)
val _ = ParseExtras.tight_equality();

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* for EVAL ifM *)
val _ = computeLib.set_skip computeLib.the_compset ``ifM`` (SOME 1);
(* EVAL ifM must be in current script, e.g. EVAL ``expn 1 2 3``; *)

(*
val count_CASES = TypeBase.nchotomy_of ``:counter``;
val cmetis = metis_tac[pair_CASES, count_CASES];
*)

(* ------------------------------------------------------------------------- *)
(* Constructors                                                              *)
(* ------------------------------------------------------------------------- *)

(* Make a zero *)
val make_0M_def = Define`
    make_0M = do tick 1; return 0; od
`;

(* Make a False *)
val make_FM_def = Define`
    make_FM = do tick 1; return F; od
`;

(* Make an empty list *)
val make_nilM_def = Define`
    make_nilM = do tick 1; return []; od
`;

(* Values of constructors *)
val make_0M_value = store_thm("make_0M_value[simp]", ``valueOf (make_0M) = 0``, rw[make_0M_def]);
val make_FM_value = store_thm("make_FM_value[simp]", ``valueOf (make_FM) = F``, rw[make_FM_def]);
val make_nilM_value = store_thm("make_nilM_value[simp]", ``valueOf (make_nilM) = []``, rw[make_nilM_def]);

(* Steps of constructors *)
val make_0M_steps = store_thm("make_0M_steps[simp]", ``stepsOf (make_0M) = 1``, rw[make_0M_def]);
val make_FM_steps = store_thm("make_FM_steps[simp]", ``stepsOf (make_FM) = 1``, rw[make_FM_def]);
val make_nilM_steps = store_thm("make_nilM_steps[simp]", ``stepsOf (make_nilM) = 1``, rw[make_nilM_def]);

(* ------------------------------------------------------------------------- *)
(* Identity                                                                  *)
(* ------------------------------------------------------------------------- *)

(* ID monad *)
val idM_def = Define`
    idM x = do tick 0; return x; od
`;
val _ = overload_on ("id_", ``app1 idM``);

val idM_value = store_thm("idM_value[simp]", ``!x. valueOf (idM x) = x``, rw[idM_def]);
val idM_steps = store_thm("idM_steps[simp]", ``!x. stepsOf (idM x) = 0``, rw[idM_def]);

(* ------------------------------------------------------------------------- *)
(* Basic Arithmetic                                                          *)
(* ------------------------------------------------------------------------- *)

(* ADD monad *)
val addM_def = Define`
    addM x y = do tick (MAX (size x) (size y)); return (x + y); od
`;
val _ = overload_on ("add_", ``app2 addM``);

(*
> EVAL ``addM 3 4``; = (7,Count 3): thm
> EVAL ``add_ 3c 4c``; = (7,Count 3): thm
*)

(* SUB monad *)
val subM_def = Define`
    subM x y = do tick (MAX (size x) (size y)); return (x - y); od
`;
val _ = overload_on ("sub_", ``app2 subM``);

(*
> EVAL ``sub_ 10c 3c``; = (7,Count 4): thm
*)

(* MUL monad *)
val mulM_def = Define`
    mulM x y = do tick (size x * size y); return (x * y); od
`;
val _ = overload_on ("mul_", ``app2 mulM``);

(*
> EVAL ``mul_ 3c 7c``; = (21,Count 6): thm
*)

(* DIV monad *)
val divM_def = Define`
  divM x y = do tick (size x * size y); return (x DIV y); od
`;
val _ = overload_on ("div_", ``app2 divM``);

(* MOD monad *)
val modM_def = Define`
  modM x y = do tick (size x * size y);  return (x MOD y); od
`;
val _ = overload_on ("mod_", ``app2 modM``);

(*
> EVAL ``div_ 17c 3c``; =  (5,Count 10): thm
> EVAL ``mod_ 17c 3c``; =  (2,Count 10): thm
*)

(* Values of basic arithmetic *)
val addM_value = store_thm("addM_value[simp]", ``!x y. valueOf (addM x y) = x + y``, rw[addM_def]);
val subM_value = store_thm("subM_value[simp]", ``!x y. valueOf (subM x y) = x - y``, rw[subM_def]);
val mulM_value = store_thm("mulM_value[simp]", ``!x y. valueOf (mulM x y) = x * y``, rw[mulM_def]);
val divM_value = store_thm("divM_value[simp]", ``!x y. valueOf (divM x y) = x DIV y``, rw[divM_def]);
val modM_value = store_thm("modM_value[simp]", ``!x y. valueOf (modM x y) = x MOD y``, rw[modM_def]);

(* Steps of basic arithmetic *)
val addM_steps = store_thm("addM_steps[simp]", ``!x y. stepsOf (addM x y) = MAX (size x) (size y)``, rw[addM_def]);
val subM_steps = store_thm("subM_steps[simp]", ``!x y. stepsOf (subM x y) = MAX (size x) (size y)``, rw[subM_def]);
val mulM_steps = store_thm("mulM_steps[simp]", ``!x y. stepsOf (mulM x y) = (size x) * (size y)``, rw[mulM_def]);
val divM_steps = store_thm("divM_steps[simp]", ``!x y. stepsOf (divM x y) = (size x) * (size y)``, rw[divM_def]);
val modM_steps = store_thm("modM_steps[simp]", ``!x y. stepsOf (modM x y) = (size x) * (size y)``, rw[modM_def]);

(* ------------------------------------------------------------------------- *)
(* Basic List                                                                *)
(* ------------------------------------------------------------------------- *)

(* Null monad *)
val nullM_def = Define`
    nullM ls = do tick 1; return (ls = []) od
`;
val _ = overload_on ("null_", ``app1 nullM``);

(* Head monad *)
val headM_def = Define`
    headM ls = do tick 1; return (HD ls) od
`;
val _ = overload_on ("head_", ``app1 headM``);

(* Tail monad *)
val tailM_def = Define`
    tailM ls = do tick 1; return (TL ls) od
`;
val _ = overload_on ("tail_", ``app1 tailM``);

(* Cons monad *)
val consM_def = Define`
    consM x ls = do tick 1; return (x::ls) od
`;
val _ = overload_on ("cons_", ``app2 consM``);

(* Values of basic list *)
val nullM_value = store_thm("nullM_value[simp]", ``!ls. valueOf (nullM ls) <=> (ls = []) ``, rw[nullM_def]);
val headM_value = store_thm("headM_value[simp]", ``!ls. valueOf (headM ls) = HD ls``, rw[headM_def]);
val tailM_value = store_thm("tailM_value[simp]", ``!ls. valueOf (tailM ls) = TL ls``, rw[tailM_def]);
val consM_value = store_thm("consM_value[simp]", ``!x ls. valueOf (consM x ls) = x :: ls``, rw[consM_def]);

(* Steps of basic list *)
val nullM_steps = store_thm("nullM_steps[simp]", ``!ls. stepsOf (nullM ls) = 1``, rw[nullM_def]);
val headM_steps = store_thm("headM_steps[simp]", ``!ls. stepsOf (headM ls) = 1``, rw[headM_def]);
val tailM_steps = store_thm("tailM_steps[simp]", ``!ls. stepsOf (tailM ls) = 1``, rw[tailM_def]);
val consM_steps = store_thm("consM_steps[simp]", ``!x ls. stepsOf (consM x ls) = 1``, rw[consM_def]);

(* ------------------------------------------------------------------------- *)
(* Basic Boolean                                                             *)
(* ------------------------------------------------------------------------- *)


(* EQ monad *)
val eqM_def = Define`
    eqM x y = do tick (MAX (size x) (size y)); return (x = y); od
`;
val _ = overload_on ("eq_", ``app2 eqM``);

(*
> EVAL ``eq_ 7c 7c``; = (T,Count 3): thm
> EVAL ``eq_ 7c 3c``; = (F,Count 3): thm
*)


(* Not monad *)
val notM_def = Define`
    notM b = do tick 1; return (~ b) od
`;
val _ = overload_on ("not_", ``app1 notM``);

(* Bool monad *)
val boolM_def = Define`
    boolM b = do tick 1; return (if b then 1 else 0) od
`;
val _ = overload_on ("bool_", ``app1 boolM``);

(* Values of basic boolean *)
val eqM_value = store_thm("eqM_value[simp]", ``!x y. valueOf (eqM x y) = (x = y)``, rw[eqM_def]);
val notM_value = store_thm("notM_value[simp]", ``!b. valueOf (notM b) <=> (~b)``, rw[notM_def]);
val boolM_value = store_thm("boolM_value[simp]", ``!b. valueOf (boolM b) = if b then 1 else 0``, rw[boolM_def]);

(* Steps of basic boolean *)
val eqM_steps = store_thm("eqM_steps[simp]", ``!x y. stepsOf (eqM x y) = MAX (size x) (size y)``, rw[eqM_def]);
val notM_steps = store_thm("notM_steps[simp]", ``!b. stepsOf (notM b) = 1``, rw[notM_def]);
val boolM_steps = store_thm("boolM_steps[simp]", ``!b. stepsOf (boolM b) = 1``, rw[boolM_def]);

(* ------------------------------------------------------------------------- *)
(* Macro Monads                                                              *)
(* ------------------------------------------------------------------------- *)

(* Zero test monad *)
val zeroM_def = Define `zeroM n = eqM n 0`;

(* Theorem: valueOf (zeroM n) <=> (n = 0) *)
(* Proof: by zeroM_def, eqM_value *)
val zeroM_value = store_thm(
  "zeroM_value[simp]",
  ``!n. valueOf (zeroM n) <=> (n = 0)``,
  rw[zeroM_def]);

(* Theorem: stepsOf (zeroM n) = size n *)
(* Proof:
     stepsOf (zeroM n)
   = stepsOf (eqM n 0)      by zeroM_def
   = MAX (size n) (size 0)  by eqM_steps
   = MAX (size n) 1         by size_0
   = size n                 by max_1_size_n, MAX_COMM
*)
val zeroM_steps = store_thm(
  "zeroM_steps[simp]",
  ``!n. stepsOf (zeroM n) = size n``,
  rw[zeroM_def] >>
  metis_tac[max_1_size_n, MAX_COMM]);

(* Theorem: (\n. stepsOf (zeroM n)) IN big_O size *)
(* Proof:
   By big_O_def, zeroM_steps, this is to show:
      ?k c. !n. k < n ==> size n <= c * size n
   or ?k c. !n. k < n ==> size n = 0 \/ 1 <= c
   Take k = 0, c = 1.
*)
val zeroM_cc = store_thm(
  "zeroM_cc",
  ``(\n. stepsOf (zeroM n)) IN big_O size``,
  rw[big_O_def] >>
  qexists_tac `0` >>
  qexists_tac `1` >>
  fs[]);

(* Theorem: (\n. stepsOf (zeroM n)) IN big_O ((POLY 1) o size) *)
(* Proof:
   By big_O_def, POLY_def, zeroM_steps, this is to show:
      ?k c. !n. k < n ==> size <= c * size n
   or ?k c. !n. k < n ==> size n = 0 \/ 1 <= c
   Take k = 0, c = 1.
*)
val zeroM_poly_cc = store_thm(
  "zeroM_poly_cc",
  ``(\n. stepsOf (zeroM n)) IN big_O ((POLY 1) o size)``,
  rw[big_O_def, POLY_def] >>
  qexists_tac `0` >>
  qexists_tac `1` >>
  fs[]);

(* Theorem: (stepsOf o zeroM) IN big_O (\n. ulog n) *)
(* Proof:
   By zeroM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> size n <= c * ulog n
   Put k = 1, c = 2, then size n <= 2 * ulog n      by size_le_ulog
*)
val zeroM_steps_big_O = store_thm(
  "zeroM_steps_big_O",
  ``(stepsOf o zeroM) IN big_O (\n. ulog n)``,
  rw[big_O_def] >>
  metis_tac[size_le_ulog]);

(* Theorem: (valueOf (zeroM n) <=> (n = 0)) /\
            (stepsOf o zeroM) IN big_O (\n. ulog n) *)
(* Proof: by zeroM_value, zeroM_steps_big_O *)
val zeroM_thm = store_thm(
  "zeroM_thm",
  ``!n. (valueOf (zeroM n) <=> (n = 0)) /\
       (stepsOf o zeroM) IN big_O (\n. ulog n)``,
  metis_tac[zeroM_value, zeroM_steps_big_O]);


(* ------------------------------------------------------------------------- *)

(* Define equal-to-one macro *)
val oneM_def = Define`
    oneM n = eqM 1 n
`;

(* Theorem: valueOf (oneM n) = (n = 1) *)
(* Proof: by oneM_def *)
val oneM_value = store_thm(
  "oneM_value[simp]",
  ``!n. valueOf (oneM n) = (n = 1)``,
  rw[oneM_def]);

(* Theorem: stepsOf (oneM n) = size n *)
(* Proof: by oneM_def, size_1, max_1_size_n *)
val oneM_steps = store_thm(
  "oneM_steps[simp]",
  ``!n. stepsOf (oneM n) = size n``,
  rw[oneM_def, max_1_size_n]);

(* Theorem: (\n. stepsOf (oneM n)) IN big_O size *)
(* Proof:
   By big_O_def, oneM_steps, this is to show:
      ?k c. !n. k < n ==> size n <= c * size n
   or ?k c. !n. k < n ==> size n = 0 \/ 1 <= c
   Take k = 0, c = 1.
*)
val oneM_cc = store_thm(
  "oneM_cc",
  ``(\n. stepsOf (oneM n)) IN big_O size``,
  rw[big_O_def] >>
  qexists_tac `0` >>
  qexists_tac `1` >>
  fs[]);

(* Theorem: (\n. stepsOf (oneM n)) IN big_O ((POLY 1) o size) *)
(* Proof:
   By big_O_def, POLY_def, oneM_steps, this is to show:
      ?k c. !n. k < n ==> size <= c * size n
   or ?k c. !n. k < n ==> size n = 0 \/ 1 <= c
   Take k = 0, c = 1.
*)
val oneM_poly_cc = store_thm(
  "oneM_poly_cc",
  ``(\n. stepsOf (oneM n)) IN big_O ((POLY 1) o size)``,
  rw[big_O_def, POLY_def] >>
  qexists_tac `0` >>
  qexists_tac `1` >>
  fs[]);

(* Theorem: (stepsOf o oneM) IN big_O (\n. ulog n) *)
(* Proof:
   By oneM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> size n <= c * ulog n
   Put k = 1, c = 2, then size n <= 2 * ulog n      by size_le_ulog
*)
val oneM_steps_big_O = store_thm(
  "oneM_steps_big_O",
  ``(stepsOf o oneM) IN big_O (\n. ulog n)``,
  rw[big_O_def] >>
  metis_tac[size_le_ulog]);

(* Theorem: (valueOf (oneM n) <=> (n = 1)) /\
            (stepsOf o oneM) IN big_O (\n. ulog n) *)
(* Proof: by oneM_value, oneM_steps_big_O *)
val oneM_thm = store_thm(
  "oneM_thm",
  ``!n. (valueOf (oneM n) <=> (n = 1)) /\
       (stepsOf o oneM) IN big_O (\n. ulog n)``,
  metis_tac[oneM_value, oneM_steps_big_O]);

(* ------------------------------------------------------------------------- *)

(* Twice monad *)
val twiceM_def = Define`
    twiceM n = mulM n 2
`;
val _ = overload_on ("twice_", ``app1 twiceM``);

(*
> EVAL ``twiceM 3``; = (6,Count 4): thm
> EVAL ``twice_ 6c``; = (12,Count 6): thm
*)

(* Theorem: (\n. stepsOf (twiceM n)) IN big_O size *)
(* Proof:
   By twiceM_def, this is to show:
      (\n. size n * size 2) IN big_O size
   By big_O_def, this is to show:
      ?k c. !n. k < n ==> 2 * size n <= c * size n
   Take k = 0, c = 2.
   The result follows.
*)
val twiceM_cc = store_thm(
  "twiceM_cc",
  ``(\n. stepsOf (twiceM n)) IN big_O size``,
  rw[twiceM_def, big_O_def] >>
  qexists_tac `0` >>
  qexists_tac `2` >>
  fs[]);

(* Theorem: (\n. stepsOf (twiceM n)) IN O_poly 1 *)
(* Proof:
   By twiceM_def, this is to show:
      (\n. size n * size 2) IN O_poly 1
   By O_poly_thm, this is to show:
      ?h k. !n. h < n ==> size n * size 2 <= k * size n
   Take h = 0, k = size 2.
   The result follows.
*)
val twiceM_poly_cc = store_thm(
  "twiceM_poly_cc",
  ``(\n. stepsOf (twiceM n)) IN O_poly 1``,
  rw[twiceM_def] >>
  rw[O_poly_thm] >>
  map_every qexists_tac [`0`, `size 2`] >>
  simp[]);

(* Theorem: valueOf (twiceM n) = 2 * n *)
(* Proof:
     valueOf (twiceM n)
   = valueOf (mulM n 2)   by twiceM_def
   = n * 2 = 2 * n        by mulM_value
*)
val twiceM_value = store_thm(
  "twiceM_value[simp]",
  ``!n. valueOf (twiceM n) = 2 * n``,
  rw[twiceM_def]);

(* Theorem: stepsOf (twiceM n) = 2 * (size n) *)
(* Proof:
     stepsOf (twiceM n)
   = stepsOf (mulM n 2)     by twiceM_def
   = (size n) * (size 2)    by mulM_steps
   = (size n) * 2           by size_2
   = 2 * (size n)           by MULT_COMM
*)
val twiceM_steps = store_thm(
  "twiceM_steps[simp]",
  ``!n. stepsOf (twiceM n) = 2 * (size n)``,
  rw[twiceM_def, size_2]);
(* verifies twiceM_cc: (\n. stepsOf (twiceM n)) IN O_poly 1 *)

(* Theorem: (stepsOf o twiceM) IN big_O (\n. ulog n) *)
(* Proof:
   By twiceM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> 2 * size n <= c * ulog n
   Put k = 1, c = 4, then 2 * size n <= 4 * ulog n      by size_le_ulog
*)
val twiceM_steps_big_O = store_thm(
  "twiceM_steps_big_O",
  ``(stepsOf o twiceM) IN big_O (\n. ulog n)``,
  rw[big_O_def] >>
  qexists_tac `1` >>
  qexists_tac `4` >>
  rpt strip_tac >>
  `size n <= 2 * ulog n` by metis_tac[size_le_ulog] >>
  decide_tac);

(* Theorem: (valueOf (twiceM n) = (2 * n)) /\
            (stepsOf o twiceM) IN big_O (\n. ulog n) *)
(* Proof: by twiceM_value, twiceM_steps_big_O *)
val twiceM_thm = store_thm(
  "twiceM_thm",
  ``!n. (valueOf (twiceM n) = (2 * n)) /\
       (stepsOf o twiceM) IN big_O (\n. ulog n)``,
  metis_tac[twiceM_value, twiceM_steps_big_O]);


(* ------------------------------------------------------------------------- *)

(* HALF monad *)
val halfM_def = Define `halfM n = divM n 2`;
val _ = overload_on ("half_", ``app1 halfM``);

(*
> EVAL ``halfM 5``; = (2,Count 6): thm
> EVAL ``half_ 5c``; = (2,Count 6): thm
*)

(* Theorem: (\n. stepsOf (halfM n)) IN big_O size *)
(* Proof:
   By big_O_def, halfM_def, divM_steps, this is to show:
      ?k c. !n. k < n ==> size n * size 2 <= c * size n
   Take k = 0, c = size 2.
*)
val halfM_cc = store_thm(
  "halfM_cc",
  ``(\n. stepsOf (halfM n)) IN big_O size``,
  rw[big_O_def, halfM_def] >>
  qexists_tac `0` >>
  qexists_tac `size 2` >>
  fs[]);

(* Theorem: valueOf (halfM n) = HALF n *)
(* Proof:
     valueOf (halfM n)
   = valueOf (divM n 2)    by halfM_def
   = n DIV 2               by divM_value
   = HALF n                by notation
*)
val halfM_value = store_thm(
  "halfM_value[simp]",
  ``!n. valueOf (halfM n) = HALF n``,
  rw[halfM_def]);

(* Theorem: stepsOf (halfM n) = 2 * size n *)
(* Proof:
     stepsOf (halfM n)
   = stepsOf (divM n 2)    by halfM_def
   = size n * size 2       by divM_steps
   = size n * 2            by size_2
   = 2 * size x
*)
val halfM_steps = store_thm(
  "halfM_steps[simp]",
  ``!n. stepsOf (halfM n) = 2 * size n``,
  rw[halfM_def, size_2]);
(* verifies halfM_cc: (\n. stepsOf (halfM n)) IN big_O size *)

(* Theorem: (stepsOf o halfM) IN big_O (\n. ulog n) *)
(* Proof:
   By halfM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> 2 * size n <= c * ulog n
   Put k = 1, c = 4, then 2 * size n <= 4 * ulog n      by size_le_ulog
*)
val halfM_steps_big_O = store_thm(
  "halfM_steps_big_O",
  ``(stepsOf o halfM) IN big_O (\n. ulog n)``,
  rw[big_O_def] >>
  qexists_tac `1` >>
  qexists_tac `4` >>
  rpt strip_tac >>
  `size n <= 2 * ulog n` by metis_tac[size_le_ulog] >>
  decide_tac);

(* Theorem: (valueOf (halfM n) = HALF n) /\
            (stepsOf o halfM) IN big_O (\n. ulog n) *)
(* Proof: by halfM_value, halfM_steps_big_O *)
val halfM_thm = store_thm(
  "halfM_thm",
  ``!n. (valueOf (halfM n) = HALF n) /\
       (stepsOf o halfM) IN big_O (\n. ulog n)``,
  metis_tac[halfM_value, halfM_steps_big_O]);


(* ------------------------------------------------------------------------- *)

(* Parity monad *)
val parityM_def = Define `parityM n = modM n 2`;

(* Theorem: valueOf (parityM n) = n MOD 2 *)
(* Proof: by parityM_def, modM_value *)
val parityM_value = store_thm(
  "parityM_value[simp]",
  ``!n. valueOf (parityM n) = n MOD 2``,
  rw[parityM_def]);

(* Theorem: stepsOf (parityM n) = 2 * size n *)
(* Proof:
     stepsOf (parityM n)
   = stepsOf (modM n 2)     by parityM_def
   = size n * size 2        by modM_steps
   = size n * 2             by size_2
   = 2 * size n             by arithmetic
*)
val parityM_steps = store_thm(
  "parityM_steps[simp]",
  ``!n. stepsOf (parityM n) = 2 * size n``,
  rw[parityM_def, size_2]);

(* Theorem: stepsOf (parityM n)) IN big_O size *)
(* Proof:
   By big_O_def, parityM_steps, this is to show:
      ?k c. !n. k < n ==> TWICE (size n) <= c * size n
   or ?k c. !n. k < n ==> 2 <= c
   Take k = 0, c = 2.
*)
val parityM_cc = store_thm(
  "parityM_cc",
  ``(\n. stepsOf (parityM n)) IN big_O size``,
  rw[big_O_def] >>
  qexists_tac `0` >>
  qexists_tac `2` >>
  fs[]);

(* Theorem: (\n. stepsOf (parityM n)) IN big_O ((POLY 1) o size) *)
(* Proof:
   By big_O_def, POLY_def, parityM_steps, this is to show:
      ?k c. !n. k < n ==> TWICE (size n) <= c * size n
   or ?k c. !n. k < n ==> 2 <= c
   Take k = 0, c = 2.
*)
val parityM_poly_cc = store_thm(
  "parityM_poly_cc",
  ``(\n. stepsOf (parityM n)) IN big_O ((POLY 1) o size)``,
  rw[big_O_def, POLY_def] >>
  qexists_tac `0` >>
  qexists_tac `2` >>
  fs[]);

(* Theorem: (\n. n MOD 2) IN big_O (K 1) *)
(* Proof:
   By big_O_def, this is to show:
      ?k c. !n. k < n ==> n MOD 2 <= c
   Note n MOD 2 = 0 or 1    by MOD_LESS
   Take k = 0, c = 1.
*)
val parity_cc = store_thm(
  "parity_cc",
  ``(\n. n MOD 2) IN big_O (K 1)``,
  rw[big_O_def] >>
  qexists_tac `0` >>
  qexists_tac `1` >>
  rw[] >>
  `n MOD 2 < 2` by rw[MOD_LESS] >>
  decide_tac);

(* Theorem: (stepsOf o parityM) IN big_O (\n. ulog n) *)
(* Proof:
   By parityM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> 2 * size n <= c * ulog n
   Put k = 1, c = 4, then 2 * size n <= 4 * ulog n      by size_le_ulog
*)
val parityM_steps_big_O = store_thm(
  "parityM_steps_big_O",
  ``(stepsOf o parityM) IN big_O (\n. ulog n)``,
  rw[big_O_def] >>
  qexists_tac `1` >>
  qexists_tac `4` >>
  rpt strip_tac >>
  `size n <= 2 * ulog n` by metis_tac[size_le_ulog] >>
  decide_tac);

(* Theorem: (valueOf (parityM n) = n MOD 2) /\
            (stepsOf o parityM) IN big_O (\n. ulog n) *)
(* Proof: by parityM_value, parityM_steps_big_O *)
val parityM_thm = store_thm(
  "parityM_thm",
  ``!n. (valueOf (parityM n) = n MOD 2) /\
       (stepsOf o parityM) IN big_O (\n. ulog n)``,
  metis_tac[parityM_value, parityM_steps_big_O]);


(* ------------------------------------------------------------------------- *)

(* EVEN monad *)
(* val evenM_def = Define`evenM x = do tick 1; return (EVEN x); od`; *)
(* val evenM_def = Define `evenM x = eq_ (modM x 2) 0c`; *)
(* val evenM_def = Define `evenM x = eq_ (mod_ (unit x) 2c) 0c`; *)
(*
val evenM_def = Define`
    evenM n = do
                 y <- modM n 2;
                 z <- eqM y 0;
              od
`;
*)
val evenM_def = Define`
    evenM n = do
                 z <- parityM n;
                 zeroM z;
              od
`;
val _ = overload_on ("even_", ``app1 evenM``);

(*
> EVAL ``evenM 3``; = (F,Count 5): thm
> EVAL ``even_ 4c``; = (T,Count 7): thm
*)

(* Theorem: valueOf (evenM n) = (EVEN n) *)
(* Proof:
     valueOf (evenM n)
   = valueOf (do z <- parityM n; zeroM z od)   by evenM_def
   = valueOf (zeroM (valueOf (parityM n)))     by valueOf_bind
   = valueOf (zeroM (n MOD 2))                 by parityM_value
   = (n MOD 2 = 0)                             by zeroM_value
   = EVEN n                                    by EVEN_MOD2
*)
val evenM_value = store_thm(
  "evenM_value[simp]",
  ``!n. valueOf (evenM n) = (EVEN n)``,
  rw[evenM_def] >>
  rw[EVEN_MOD2]);

(* Theorem: stepsOf (evenM n) = 2 * size n + 1 *)
(* Proof:
     stepsOf (evenM n)
   = stepsOf (do z <- parityM n; zeroM z od)   by evenM_def
   = stepsOf (parityM n) +
     stepsOf (zeroM (valueOf (parityM n)))     by stepsOf_bind
   = 2 * size n +                              by parityM_steps
     stepsOf (zeroM (n MOD 2))                 by parityM_value
   = 2 * size n + size (n MOD 2)               by zeroM_steps
   = 2 * size n + size (0 or 1)                by MOD_LESS
   = 2 * size n + 1                            by size_0, size_1
*)
val evenM_steps = store_thm(
  "evenM_steps[simp]",
  ``!n. stepsOf (evenM n) = 2 * size n + 1``,
  rw[evenM_def] >>
  `n MOD 2 < 2` by rw[] >>
  metis_tac[size_0, size_1, DECIDE``1 <= 1 /\ (n < 2 <=> (n = 0) \/ (n = 1))``]);
(* consistent with later evenM_cc: (\n. stepsOf (evenM n)) IN big_O size *)

(* Theorem: (\n. stepsOf (evenM n)) IN big_O size *)
(* Proof:
   By evenM_def, this is to show:
      (\n. TWICE (size n) + size (n MOD 2)) IN big_O size
   By big_O_def, this is to show:
      ?k c. !n. k < n ==> TWICE (size n) + size (n MOD 2) <= c * size n
   Take k = 0, c = 3.
   Note n MOD 2 < 2         by MOD_LESS
   Thus size (n MOD 2) = 1  by size_0, size_1
   Apply 1 <= size n        by one_le_size
   The result follows.
*)
val evenM_cc = store_thm(
  "evenM_cc",
  ``(\n. stepsOf (evenM n)) IN big_O size``,
  rw[evenM_def] >>
  rw[big_O_def] >>
  map_every qexists_tac [`0`, `3`] >>
  rpt strip_tac >>
  `n MOD 2 < 2` by rw[] >>
  `size (n MOD 2) = 1` by metis_tac[size_0, size_1, DECIDE``n < 2 ==> (n = 0) \/ (n = 1)``] >>
  `1 <= size n` by rw[one_le_size] >>
  rw[]);
(* But this depends on n MOD 2 = 0 or 1 *)
(* Also: can prove below *)

(* Theorem: (\n. stepsOf (zeroM (n MOD 2))) IN big_O (K 1) *)
(* Proof:
   By big_O_def, zeroM_steps, this is to show:
      ?k c. !n. k < n ==> size (n MOD 2) <= c
   Take k = 0, c = 1.
   Note n MOD 2 < 2       by MOD_LESS
     so n MOD 2 = 0 or n MOD 2 = 1
    But size 0 = 1        by size_0
    and size 1 = 1        by size_1
   Hence true.
*)
val zeroM_parity_cc = store_thm(
  "zeroM_parity_cc",
  ``(\n. stepsOf (zeroM (n MOD 2))) IN big_O (K 1)``,
  rw[big_O_def] >>
  qexists_tac `0` >>
  qexists_tac `1` >>
  rpt strip_tac >>
  `n MOD 2 < 2` by rw[] >>
  metis_tac[size_0, size_1, DECIDE``1 <= 1 /\ (n < 2 <=> (n = 0) \/ (n = 1))``]);

(* This can be very bad! or reasonable? *)

(* Theorem: (stepsOf o evenM) IN big_O (\n. ulog n) *)
(* Proof:
   By evenM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> 2 * size n + 1 <= c * ulog n
   Put k = 1, c = 5,
      then 2 * size n <= 4 * ulog n      by size_le_ulog
      and           1 <= ulog n          by ulog_ge_1
   hence true.
*)
val evenM_steps_big_O = store_thm(
  "evenM_steps_big_O",
  ``(stepsOf o evenM) IN big_O (\n. ulog n)``,
  rw[big_O_def] >>
  qexists_tac `1` >>
  qexists_tac `5` >>
  rpt strip_tac >>
  `size n <= 2 * ulog n` by metis_tac[size_le_ulog] >>
  `1 <= ulog n` by rw[ulog_ge_1] >>
  decide_tac);

(* Theorem: (valueOf (evenM n) <=> EVEN n) /\
            (stepsOf o evenM) IN big_O (\n. ulog n) *)
(* Proof: by evenM_value, evenM_steps_big_O *)
val evenM_thm = store_thm(
  "evenM_thm",
  ``!n. (valueOf (evenM n) <=> EVEN n) /\
       (stepsOf o evenM) IN big_O (\n. ulog n)``,
  metis_tac[evenM_value, evenM_steps_big_O]);


(* ------------------------------------------------------------------------- *)

(* SQ monad *)
val sqM_def = Define `sqM n = mulM n n`;
val _ = overload_on ("sq_", ``app1 sqM``);

(*
> EVAL ``sq_ 7c``; = (49,Count 9): thm
*)

(* Theorem: valueOf (sqM n) = SQ n *)
(* Proof:
     valueOf (sqM n)
   = valueOf (mulM n n)    by sqM_def
   = n * n                 by mulM_value
   = SQ n                  by notation
*)
val sqM_value = store_thm(
  "sqM_value[simp]",
  ``!n. valueOf (sqM n) = SQ n``,
  rw[sqM_def]);

(* Theorem: stepsOf (sqM n) = (size n) ** 2 *)
(* Proof:
     stepsOf (sqM n)
   = stepsOf (mulM n n)    by sqM_def
   = size n * size n       by mulM_steps
   = size n ** 2           by EXP_2
*)
val sqM_steps = store_thm(
  "sqM_steps[simp]",
  ``!n. stepsOf (sqM n) = (size n) ** 2``,
  rw[sqM_def, Once EXP_2]);
(* verifies sqM_poly_cc: (\n. stepsOf (sqM n)) IN big_O (POLY 2 o size) *)

(* Theorem: (\n. stepsOf (sqM n)) IN big_O (POLY 2 o size) *)
(* Proof:
   By big_O_def, POLY_def, sqM_def, mulM_steps, this is to show:
      ?k c. !n. k < n ==> size n * size n <= c * size n * size n
   Take k = 0, c = 1.
*)
val sqM_poly_cc = store_thm(
  "sqM_poly_cc",
  ``(\n. stepsOf (sqM n)) IN big_O (POLY 2 o size)``,
  rw[big_O_def, POLY_def, sqM_def] >>
  qexists_tac `0` >>
  qexists_tac `1` >>
  fs[]);

(* Theorem: (UNCURRY (\x y. stepsOf (mulM x y))) z <
            ((POLY 2) o (UNCURRY (\x y. 1 + MAX (size x) (size y)))) z *)
(* Proof: by mulM_steps, POLY_def, and MAX_DEF *)
val mulM_poly_cc = store_thm(
  "mulM_poly_cc",
  ``!z. (UNCURRY (\x y. stepsOf (mulM x y))) z <
       ((POLY 2) o (UNCURRY (\x y. 1 + MAX (size x) (size y)))) z``,
  rw[] >>
  (Cases_on `z` >> simp[]) >>
  rw[mulM_steps, POLY_def] >>
  qabbrev_tac `z = MAX (size q) (size r) + 1` >>
  `size q < z` by rw[MAX_DEF, Abbr`z`] >>
  `size r < z` by rw[MAX_DEF, Abbr`z`] >>
  `size q * size r < z * z` by rw[LT_MONO_MULT2] >>
  metis_tac[EXP_2]);

(* Theorem: (stepsOf o sqM) IN big_O (\n. (ulog n) ** 2) *)
(* Proof:
   By sqM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> size n ** 2 <= c * ulog n ** 2
   Put k = 1, c = 4,
      then size n <= 2 * ulog n               by size_le_ulog
       so  (size n) ** 2 <= 4 (ulog n) ** 2   by SQ_LE
*)
val sqM_steps_big_O = store_thm(
  "sqM_steps_big_O",
  ``(stepsOf o sqM) IN big_O (\n. (ulog n) ** 2)``,
  rw[big_O_def] >>
  qexists_tac `1` >>
  qexists_tac `4` >>
  rpt strip_tac >>
  `size n <= 2 * ulog n` by metis_tac[size_le_ulog] >>
  `SQ (size n) <= SQ (2 * ulog n)` by rw[SQ_LE] >>
  `SQ (2 * ulog n) = 4 * SQ (ulog n)` by decide_tac >>
  fs[]);

(* Theorem: (valueOf (sqM n) = SQ n) /\
            (stepsOf o sqM) IN big_O (\n. (ulog n) ** 2) *)
(* Proof: by sqM_value, sqM_steps_big_O *)
val sqM_thm = store_thm(
  "sqM_thm",
  ``!n. (valueOf (sqM n) = SQ n) /\
       (stepsOf o sqM) IN big_O (\n. (ulog n) ** 2)``,
  metis_tac[sqM_value, sqM_steps_big_O]);


(* ------------------------------------------------------------------------- *)

(* Increment monad *)
val incM_def = Define`
    incM n = addM n 1
`;
val _ = overload_on ("inc_", ``app1 incM``);

(*
> EVAL ``incM 2``; = (3,Count 2): thm
> EVAL ``inc_ 5c``; = (6,Count 3): thm
*)

(* Theorem: (\n. stepsOf (incM n)) IN O_poly 1 *)
(* Proof:
   By incM_def, this is to show:
      (\n. MAX (size n) (size 1)) IN O_poly 1
   By O_poly_thm, this is to show:
      ?h k. !n. h < n ==> (size n = 0 \/ 0 < k) /\ size 1 <= k * size n
   Take h = 0, k = 1.
   Note 0 < 1               by arithmetic
    and size 1 = 1          by size_1
               <= size n    by one_le_size
   The result follows.
*)
val incM_cc = store_thm(
  "incM_cc",
  ``(\n. stepsOf (incM n)) IN O_poly 1``,
  rw[incM_def] >>
  rw[O_poly_thm] >>
  map_every qexists_tac [`0`, `1`] >>
  simp[one_le_size]);

(* Theorem: valueOf (incM n) = n + 1 *)
(* Proof:
     valueOf (incM n)
   = valueOf (addM n 1)   by incM_def
   = n + 1                by addM_value
*)
val incM_value = store_thm(
  "incM_value[simp]",
  ``!n. valueOf (incM n) = n + 1``,
  rw[incM_def]);

(* Theorem: stepsOf (incM n) = size n *)
(* Proof:
     stepsOf (incM n)
   = stepsOf (addM n 1)     by incM_def
   = MAX (size n) (size 1)  by addM_steps
   = MAX (size n) 1         by size_1
   = size n                 by max_1_size_n, MAX_COMM
*)
val incM_steps = store_thm(
  "incM_steps[simp]",
  ``!n. stepsOf (incM n) = size n``,
  rw[incM_def] >>
  metis_tac[max_1_size_n, MAX_COMM]);
(* verifies incM_cc: (\n. stepsOf (incM n)) IN O_poly 1 *)

(* Theorem: (stepsOf o incM) IN big_O (\n. ulog n) *)
(* Proof:
   By incM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> size n <= c * ulog n
   Put k = 1, c = 2, then size n <= 2 * ulog n  by size_le_ulog
*)
val incM_steps_big_O = store_thm(
  "incM_steps_big_O",
  ``(stepsOf o incM) IN big_O (\n. ulog n)``,
  rw[big_O_def] >>
  metis_tac[size_le_ulog]);

(* Theorem: (valueOf (incM n) = n + 1) /\
            (stepsOf o incM) IN big_O (\n. ulog n) *)
(* Proof: by incM_value, incM_steps_big_O *)
val incM_thm = store_thm(
  "incM_thm",
  ``!n. (valueOf (incM n) = n + 1) /\
       (stepsOf o incM) IN big_O (\n. ulog n)``,
  metis_tac[incM_value, incM_steps_big_O]);


(* ------------------------------------------------------------------------- *)

(* Decrement monad *)
val decM_def = Define`
    decM n = subM n 1
`;
val _ = overload_on ("dec_", ``app1 decM``);

(*
> EVAL ``decM 3``; = (2,Count 2): thm
> EVAL ``dec_ 6c``; = (5,Count 3): thm
*)

(* Theorem: (\n. stepsOf (decM n)) IN O_poly 1 *)
(* Proof:
   By decM_def, this is to show:
      (\n. MAX (size n) (size 1)) IN O_poly 1
   By O_poly_thm, this is to show:
      ?h k. !n. h < n ==> (size n = 0 \/ 0 < k) /\ size 1 <= k * size n
   Take h = 0, k = 1.
   Note 0 < 1               by arithmetic
    and size 1 = 1          by size_1
               <= size n    by one_le_size
   The result follows.
*)
val decM_cc = store_thm(
  "decM_cc",
  ``(\n. stepsOf (decM n)) IN O_poly 1``,
  rw[decM_def] >>
  rw[O_poly_thm] >>
  map_every qexists_tac [`0`, `1`] >>
  simp[one_le_size]);

(* Theorem: valueOf (decM n) = n - 1 *)
(* Proof:
     valueOf (decM n)
   = valueOf (subM n 1)   by decM_def
   = n - 1                by subM_value
*)
val decM_value = store_thm(
  "decM_value[simp]",
  ``!n. valueOf (decM n) = n - 1``,
  rw[decM_def]);

(* Theorem: stepsOf (decM n) = size n *)
(* Proof:
     stepsOf (decM n)
   = stepsOf (subM n 1)     by decM_def
   = MAX (size n) (size 1)  by subM_steps
   = MAX (size n) 1         by size_1
   = size n                 by max_1_size_n, MAX_COMM
*)
val decM_steps = store_thm(
  "decM_steps[simp]",
  ``!n. stepsOf (decM n) = size n``,
  rw[decM_def] >>
  metis_tac[max_1_size_n, MAX_COMM]);
(* verifies decM_cc: (\n. stepsOf (decM n)) IN O_poly 1 *)

(* Theorem: (stepsOf o decM) IN big_O (\n. ulog n) *)
(* Proof:
   By decM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> size n <= c * ulog n
   Put k = 1, c = 2, then size n <= 2 * ulog n  by size_le_ulog
*)
val decM_steps_big_O = store_thm(
  "decM_steps_big_O",
  ``(stepsOf o decM) IN big_O (\n. ulog n)``,
  rw[big_O_def] >>
  metis_tac[size_le_ulog]);

(* Theorem: (valueOf (decM n) = n - 1) /\
            (stepsOf o decM) IN big_O (\n. ulog n) *)
(* Proof: by decM_value, decM_steps_big_O *)
val decM_thm = store_thm(
  "decM_thm",
  ``!n. (valueOf (decM n) = n - 1) /\
       (stepsOf o decM) IN big_O (\n. ulog n)``,
  metis_tac[decM_value, decM_steps_big_O]);


(* ------------------------------------------------------------------------- *)

(* Less-or-equal monad *)
val leqM_def = Define`
    leqM n m = do
                 z <- subM n m;
                 zeroM z
               od
`;
val _ = overload_on ("leq_", ``app2 leqM``);

(*
> EVAL ``leqM 3 4``; = (T,Count 4): thm
> EVAL ``leq_ 6c 6c``; = (T,Count 4): thm
> EVAL ``leqM 7 3``; = (F,Count 6): thm
*)

(* Theorem: valueOf (leqM n m) = (n <= m) *)
(* Proof:
     valueOf (leqM n m)
   = valueOf (do z <- subM n m; zeroM z od)   by leqM_def
   = (n - m = 0)          by subM_value, zeroM_value
   = n <= m               by arithmetic
*)
val leqM_value = store_thm(
  "leqM_value[simp]",
  ``!n m. valueOf (leqM n m) = (n <= m)``,
  rw[leqM_def]);

(* Theorem: stepsOf (leqM n) = 2 * (size n) *)
(* Proof:
     stepsOf (leqM n m)
   = stepsOf (do z <- subM n m; zeroM z od)   by leqM_def
   = MAX (size n) (size m) + (size (n - m))   by subM_steps, subM_value, zeroM_steps
*)
val leqM_steps = store_thm(
  "leqM_steps[simp]",
  ``!n m. stepsOf (leqM n m) = MAX (size n) (size m) + (size (n - m))``,
  rw[leqM_def]);

(* Theorem: stepsOf (leqM n m) = size (MAX n m) + size (n - m) *)
(* Proof: leqM_steps, size_max *)
val leqM_steps_alt = store_thm(
  "leqM_steps_alt",
  ``!n m. stepsOf (leqM n m) = size (MAX n m) + size (n - m)``,
  rw[leqM_steps, size_max]);

(* Theorem: stepsOf (leqM n m) <= 2 * size (MAX n m) *)
(* Proof:
      stepsOf (leqM n m)
    = MAX (size n) (size m) + (size (n - m))    by leqM_steps
    = size (MAX n m) + size (n - m)             by size_max
   <= size (MAX n m) + size n                   by size_monotone_le
   <= size (MAX n m) + size (MAX n m)           by size_monotone_le
    = 2 * size (MAX n m)
*)
val leqM_steps_le = store_thm(
  "leqM_steps_le",
  ``!n m. stepsOf (leqM n m) <= 2 * size (MAX n m)``,
  rpt strip_tac >>
  `stepsOf (leqM n m) = size (MAX n m) + size (n - m)` by rw[leqM_steps, size_max] >>
  `size (n - m) <= size n` by rw[size_monotone_le] >>
  `size n <= size (MAX n m)` by rw[size_monotone_le] >>
  decide_tac);

(* Theorem: (\(n,m). stepsOf (leqM n m)) z ** 2 =
            (POLY 2 o (\(n,m). size (n - m) + MAX (size n) (size m))) z *)
(* Proof: by leqM_def, POLY_def. *)
val leqM_poly_cc = store_thm(
  "leqM_poly_cc",
  ``!z. (\(n,m). stepsOf (leqM n m)) z ** 2 =
       (POLY 2 o (\(n,m). size (n - m) + MAX (size n) (size m))) z``,
  rw[leqM_def] >>
  rw[POLY_def]);
(* This is not proving anything, the exponent 2 comes from POLY 2 *)

(* ------------------------------------------------------------------------- *)

(* Less-than monad *)
val ltM_def = Define`
    ltM n m = do
                 b <- eqM n m;
                 if b then unit F
                 else leqM n m
              od
`;
val _ = overload_on ("lt_", ``app2 ltM``);

(*
> EVAL ``ltM 3 4``; = (T,Count 7): thm
> EVAL ``lt_ 6c 6c``; = (F,Count 3): thm
> EVAL ``ltM 7 3``; = (F,Count 9): thm
*)

(* Theorem: valueOf (ltM n m) = (n < m) *)
(* Proof:
     valueOf (ltM n m)
   = valueOf (do b <- eqM n m; if b then unit F else leqM n m od)   by ltM_def
   = if (n = m) then F else (n <= m)      by eqM_value, subM_value, zeroM_value
   = n < m                                by arithmetic
*)
val ltM_value = store_thm(
  "ltM_value[simp]",
  ``!n m. valueOf (ltM n m) = (n < m)``,
  rw[ltM_def]);

(* Theorem: stepsOf (leqM n) = if (n = m) then size n else 2 * MAX (size n) (size m) + size (n - m) *)
(* Proof:
     stepsOf (ltM n m)
   = stepsOf (do b <- eqM n m; if b then unit F else leqM n m od)   by leqM_def
   = MAX (size n) (size m) + MAX (size n) (size m) + (size (n - m)) by eqM_steps, subM_steps, subM_value, zeroM_steps
   = MAX (size n) (size m) = size n             if n = m
   = 2 * MAX (size n) (size m) + size (n - m)   if n <> m
*)
val ltM_steps = store_thm(
  "ltM_steps[simp]",
  ``!n m. stepsOf (ltM n m) = if (n = m) then size n else 2 * MAX (size n) (size m) + size (n - m)``,
  rw[ltM_def]);

(* Theorem: (\(n,m). stepsOf (ltM n m)) z ** 1 =
            (POLY 1 o (\(n,m). if (n = m) then size n else size (n - m) + 2 * MAX (size n) (size m))) z *)
(* Proof: by ltM_def, POLY_def. *)
val ltM_poly_cc = store_thm(
  "ltM_poly_cc",
  ``!z. (\(n,m). stepsOf (ltM n m)) z ** 1 =
       (POLY 1 o (\(n,m). if (n = m) then size n else size (n - m) + 2 * MAX (size n) (size m))) z``,
  rw[ltM_def] >>
  rw[POLY_def]);
(* This is not proving anything, the exponent 2 comes from POLY 2 *)

(* ------------------------------------------------------------------------- *)

(* Greater than 1 monad *)
val gt1M_def = Define`
    gt1M n = ltM 1 n
`;
val _ = overload_on ("gt1_", ``app1 gt1M``);

(*
> EVAL ``gt1M 3``; = (T,Count 5): thm
> EVAL ``gt1_ 1c``; = (F,Count 1): thm
> EVAL ``gt1M 0``; = (F,Count 3): thm
*)

(* Theorem: valueOf (gt1M n) = (1 < n) *)
(* Proof:
     valueOf (gt1M n)
   = valueOf (ltM 1 n)        by gt1M_def
   = 1 < n                    by ltM_value
*)
val gt1M_value = store_thm(
  "gt1M_value[simp]",
  ``!n. valueOf (gt1M n) = (1 < n)``,
  rw[gt1M_def]);

(* Theorem: stepsOf (gt1M n) = if (n = 1) then 1 else 1 + 2 * size n *)
(* Proof:
     stepsOf (gt1M n)
   = stepsOf (ltM 1 n)   by gt1M_def
   = size n = size 1 = 1                       if n = 1, size_1
   = 2 * MAX (size 1) (size n) + size (1 - n)  if n <> 1
   = 2 * size n + size (1 - n)                 by size_1, max_1_size_n
   = 2 * size n + 1                            by size_0, size_1
*)
val gt1M_steps = store_thm(
  "gt1M_steps[simp]",
  ``!n. stepsOf (gt1M n) = if (n = 1) then 1 else 1 + 2 * size n``,
  rpt strip_tac >>
  `MAX 1 (size n) = size n` by metis_tac[max_1_size_n] >>
  simp[gt1M_def] >>
  Cases_on `n = 1` >-
  metis_tac[] >>
  Cases_on `n = 0` >-
  fs[] >>
  `1 - n = 0` by decide_tac >>
  simp[]);

(* ------------------------------------------------------------------------- *)

(* Define less-equal-1 macro *)
val le1M_def = Define`
    le1M n = do
               gd <- gt1M n;
               notM gd;
             od
`;
val _ = overload_on ("le1_", ``app1 le1M``);

(*
> EVAL ``le1M 3``; = (F,Count 6): thm
> EVAL ``le1_ 1c``; = (T,Count 2): thm
> EVAL ``le1M 0``; = (T,Count 4): thm
*)

(* Theorem: valueOf (le1M n) = (n <= 1) *)
(* Proof:
     valueOf (le1M n)
   = valueOf (notM (1 < n))     by le1M_def
   = ~(1 < n)                   by notM_value
   = n <= 1                     by logic
*)
val le1M_value = store_thm(
  "le1M_value[simp]",
  ``!n. valueOf (le1M n) = (n <= 1)``,
  simp[le1M_def]);


(* Theorem: stepsOf (le1M n) = if n = 1 then 2 else 2 + 2 * size n *)
(* Proof:
     stepsOf (le1M n)
   = stepsOf (gt1M n) + stepsOf (notM (1 < n))     by le1M_def
   = (if n = 1 then 1 else 1 + 2 * (size n)) + 1   by gt1M_steps
   = if n = 1 then 2 else 2 + 2 * size n           by arithmetic
*)
val le1M_steps = store_thm(
  "le1M_steps[simp]",
  ``!n. stepsOf (le1M n) = if n = 1 then 2 else 2 + 2 * size n``,
  simp[le1M_def]);

(* ------------------------------------------------------------------------- *)

(* Define append monad *)
Definition appendM_def:
  appendM l1 l2 =
      do
         gd <- nullM l1;
         if gd then return l2
         else do
                 h <- headM l1;
                 t <- tailM l1;
                 ls <- appendM t l2;
                 consM h ls;
              od
      od
Termination
  WF_REL_TAC `measure (λ(l1, l2). LENGTH l1)` >> simp[LENGTH_TL_LT]
End


(* Theorem: valueOf (appendM l1 l2) = l1 ++ l2 *)
(* Proof: induction on l1, appendM_def, APPEND. *)
val appendM_value = store_thm(
  "appendM_value[simp]",
  ``!l1 l2. valueOf (appendM l1 l2) = l1 ++ l2``,
  ho_match_mp_tac (theorem "appendM_ind") >>
  rw[] >>
  (Cases_on `l1` >> rw[Once appendM_def]));

(* ------------------------------------------------------------------------- *)

(* Define snoc monoad *)
Definition snocM_def:
  snocM x ls =
       do
         gd <- nullM ls;
         if gd then consM x ls
         else do
                 h <- headM ls;
                 t <- tailM ls;
                 l <- snocM x t;
                 consM h l;
              od
       od
Termination
  WF_REL_TAC `measure (λ(x,ls). LENGTH ls)` >> simp[LENGTH_TL_LT]
End

(* Theorem: valueOf (snocM x ls) = SNOC x ls *)
(* Proof: induction on ls, snocM_def, SNOC. *)
val snocM_value = store_thm(
  "snocM_value[simp]",
  ``!x ls. valueOf (snocM x ls) = SNOC x ls``,
  ho_match_mp_tac (theorem "snocM_ind") >>
  rw[] >>
  (Cases_on `ls` >> rw[Once snocM_def]));

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
