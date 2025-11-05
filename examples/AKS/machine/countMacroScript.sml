(* ------------------------------------------------------------------------- *)
(* Macros of Count Monad                                                     *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

Theory countMacro
Ancestors
  pred_set list rich_list arithmetic divides gcd number
  combinatorics pair option listRange prime bitsize complexity
  loopIncrease loopDecrease loopDivide loopMultiply loopList
  countMonad
Libs
  jcLib monadsyntax

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
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
Definition make_0M_def:
    make_0M = do tick 1; return 0; od
End

(* Make a False *)
Definition make_FM_def:
    make_FM = do tick 1; return F; od
End

(* Make an empty list *)
Definition make_nilM_def:
    make_nilM = do tick 1; return []; od
End

(* Values of constructors *)
Theorem make_0M_value[simp]:   valueOf (make_0M) = 0
Proof rw[make_0M_def]
QED
Theorem make_FM_value[simp]:   valueOf (make_FM) = F
Proof rw[make_FM_def]
QED
Theorem make_nilM_value[simp]:   valueOf (make_nilM) = []
Proof rw[make_nilM_def]
QED

(* Steps of constructors *)
Theorem make_0M_steps[simp]:   stepsOf (make_0M) = 1
Proof rw[make_0M_def]
QED
Theorem make_FM_steps[simp]:   stepsOf (make_FM) = 1
Proof rw[make_FM_def]
QED
Theorem make_nilM_steps[simp]:   stepsOf (make_nilM) = 1
Proof rw[make_nilM_def]
QED

(* ------------------------------------------------------------------------- *)
(* Identity                                                                  *)
(* ------------------------------------------------------------------------- *)

(* ID monad *)
Definition idM_def:
    idM x = do tick 0; return x; od
End
val _ = overload_on ("id_", ``app1 idM``);

Theorem idM_value[simp]:   !x. valueOf (idM x) = x
Proof rw[idM_def]
QED
Theorem idM_steps[simp]:   !x. stepsOf (idM x) = 0
Proof rw[idM_def]
QED

(* ------------------------------------------------------------------------- *)
(* Basic Arithmetic                                                          *)
(* ------------------------------------------------------------------------- *)

(* ADD monad *)
Definition addM_def:
    addM x y = do tick (MAX (size x) (size y)); return (x + y); od
End
val _ = overload_on ("add_", ``app2 addM``);

(*
> EVAL ``addM 3 4``; = (7,Count 3): thm
> EVAL ``add_ 3c 4c``; = (7,Count 3): thm
*)

(* SUB monad *)
Definition subM_def:
    subM x y = do tick (MAX (size x) (size y)); return (x - y); od
End
val _ = overload_on ("sub_", ``app2 subM``);

(*
> EVAL ``sub_ 10c 3c``; = (7,Count 4): thm
*)

(* MUL monad *)
Definition mulM_def:
    mulM x y = do tick (size x * size y); return (x * y); od
End
val _ = overload_on ("mul_", ``app2 mulM``);

(*
> EVAL ``mul_ 3c 7c``; = (21,Count 6): thm
*)

(* DIV monad *)
Definition divM_def:
  divM x y = do tick (size x * size y); return (x DIV y); od
End
val _ = overload_on ("div_", ``app2 divM``);

(* MOD monad *)
Definition modM_def:
  modM x y = do tick (size x * size y);  return (x MOD y); od
End
val _ = overload_on ("mod_", ``app2 modM``);

(*
> EVAL ``div_ 17c 3c``; =  (5,Count 10): thm
> EVAL ``mod_ 17c 3c``; =  (2,Count 10): thm
*)

(* Values of basic arithmetic *)
Theorem addM_value[simp]:   !x y. valueOf (addM x y) = x + y
Proof rw[addM_def]
QED
Theorem subM_value[simp]:   !x y. valueOf (subM x y) = x - y
Proof rw[subM_def]
QED
Theorem mulM_value[simp]:   !x y. valueOf (mulM x y) = x * y
Proof rw[mulM_def]
QED
Theorem divM_value[simp]:   !x y. valueOf (divM x y) = x DIV y
Proof rw[divM_def]
QED
Theorem modM_value[simp]:   !x y. valueOf (modM x y) = x MOD y
Proof rw[modM_def]
QED

(* Steps of basic arithmetic *)
Theorem addM_steps[simp]:   !x y. stepsOf (addM x y) = MAX (size x) (size y)
Proof rw[addM_def]
QED
Theorem subM_steps[simp]:   !x y. stepsOf (subM x y) = MAX (size x) (size y)
Proof rw[subM_def]
QED
Theorem mulM_steps[simp]:   !x y. stepsOf (mulM x y) = (size x) * (size y)
Proof rw[mulM_def]
QED
Theorem divM_steps[simp]:   !x y. stepsOf (divM x y) = (size x) * (size y)
Proof rw[divM_def]
QED
Theorem modM_steps[simp]:   !x y. stepsOf (modM x y) = (size x) * (size y)
Proof rw[modM_def]
QED

(* ------------------------------------------------------------------------- *)
(* Basic List                                                                *)
(* ------------------------------------------------------------------------- *)

(* Null monad *)
Definition nullM_def:
    nullM ls = do tick 1; return (ls = []) od
End
val _ = overload_on ("null_", ``app1 nullM``);

(* Head monad *)
Definition headM_def:
    headM ls = do tick 1; return (HD ls) od
End
val _ = overload_on ("head_", ``app1 headM``);

(* Tail monad *)
Definition tailM_def:
    tailM ls = do tick 1; return (TL ls) od
End
val _ = overload_on ("tail_", ``app1 tailM``);

(* Cons monad *)
Definition consM_def:
    consM x ls = do tick 1; return (x::ls) od
End
val _ = overload_on ("cons_", ``app2 consM``);

(* Values of basic list *)
Theorem nullM_value[simp]:   !ls. valueOf (nullM ls) <=> (ls = [])
Proof rw[nullM_def]
QED
Theorem headM_value[simp]:   !ls. valueOf (headM ls) = HD ls
Proof rw[headM_def]
QED
Theorem tailM_value[simp]:   !ls. valueOf (tailM ls) = TL ls
Proof rw[tailM_def]
QED
Theorem consM_value[simp]:   !x ls. valueOf (consM x ls) = x :: ls
Proof rw[consM_def]
QED

(* Steps of basic list *)
Theorem nullM_steps[simp]:   !ls. stepsOf (nullM ls) = 1
Proof rw[nullM_def]
QED
Theorem headM_steps[simp]:   !ls. stepsOf (headM ls) = 1
Proof rw[headM_def]
QED
Theorem tailM_steps[simp]:   !ls. stepsOf (tailM ls) = 1
Proof rw[tailM_def]
QED
Theorem consM_steps[simp]:   !x ls. stepsOf (consM x ls) = 1
Proof rw[consM_def]
QED

(* ------------------------------------------------------------------------- *)
(* Basic Boolean                                                             *)
(* ------------------------------------------------------------------------- *)


(* EQ monad *)
Definition eqM_def:
    eqM x y = do tick (MAX (size x) (size y)); return (x = y); od
End
val _ = overload_on ("eq_", ``app2 eqM``);

(*
> EVAL ``eq_ 7c 7c``; = (T,Count 3): thm
> EVAL ``eq_ 7c 3c``; = (F,Count 3): thm
*)


(* Not monad *)
Definition notM_def:
    notM b = do tick 1; return (~ b) od
End
val _ = overload_on ("not_", ``app1 notM``);

(* Bool monad *)
Definition boolM_def:
    boolM b = do tick 1; return (if b then 1 else 0) od
End
val _ = overload_on ("bool_", ``app1 boolM``);

(* Values of basic boolean *)
Theorem eqM_value[simp]:   !x y. valueOf (eqM x y) = (x = y)
Proof rw[eqM_def]
QED
Theorem notM_value[simp]:   !b. valueOf (notM b) <=> (~b)
Proof rw[notM_def]
QED
Theorem boolM_value[simp]:   !b. valueOf (boolM b) = if b then 1 else 0
Proof rw[boolM_def]
QED

(* Steps of basic boolean *)
Theorem eqM_steps[simp]:   !x y. stepsOf (eqM x y) = MAX (size x) (size y)
Proof rw[eqM_def]
QED
Theorem notM_steps[simp]:   !b. stepsOf (notM b) = 1
Proof rw[notM_def]
QED
Theorem boolM_steps[simp]:   !b. stepsOf (boolM b) = 1
Proof rw[boolM_def]
QED

(* ------------------------------------------------------------------------- *)
(* Macro Monads                                                              *)
(* ------------------------------------------------------------------------- *)

(* Zero test monad *)
Definition zeroM_def:   zeroM n = eqM n 0
End

(* Theorem: valueOf (zeroM n) <=> (n = 0) *)
(* Proof: by zeroM_def, eqM_value *)
Theorem zeroM_value[simp]:
    !n. valueOf (zeroM n) <=> (n = 0)
Proof
  rw[zeroM_def]
QED

(* Theorem: stepsOf (zeroM n) = size n *)
(* Proof:
     stepsOf (zeroM n)
   = stepsOf (eqM n 0)      by zeroM_def
   = MAX (size n) (size 0)  by eqM_steps
   = MAX (size n) 1         by size_0
   = size n                 by max_1_size_n, MAX_COMM
*)
Theorem zeroM_steps[simp]:
    !n. stepsOf (zeroM n) = size n
Proof
  rw[zeroM_def] >>
  metis_tac[max_1_size_n, MAX_COMM]
QED

(* Theorem: (\n. stepsOf (zeroM n)) IN big_O size *)
(* Proof:
   By big_O_def, zeroM_steps, this is to show:
      ?k c. !n. k < n ==> size n <= c * size n
   or ?k c. !n. k < n ==> size n = 0 \/ 1 <= c
   Take k = 0, c = 1.
*)
Theorem zeroM_cc:
    (\n. stepsOf (zeroM n)) IN big_O size
Proof
  rw[big_O_def] >>
  qexists_tac `0` >>
  qexists_tac `1` >>
  fs[]
QED

(* Theorem: (\n. stepsOf (zeroM n)) IN big_O ((POLY 1) o size) *)
(* Proof:
   By big_O_def, POLY_def, zeroM_steps, this is to show:
      ?k c. !n. k < n ==> size <= c * size n
   or ?k c. !n. k < n ==> size n = 0 \/ 1 <= c
   Take k = 0, c = 1.
*)
Theorem zeroM_poly_cc:
    (\n. stepsOf (zeroM n)) IN big_O ((POLY 1) o size)
Proof
  rw[big_O_def, POLY_def] >>
  qexists_tac `0` >>
  qexists_tac `1` >>
  fs[]
QED

(* Theorem: (stepsOf o zeroM) IN big_O (\n. ulog n) *)
(* Proof:
   By zeroM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> size n <= c * ulog n
   Put k = 1, c = 2, then size n <= 2 * ulog n      by size_le_ulog
*)
Theorem zeroM_steps_big_O:
    (stepsOf o zeroM) IN big_O (\n. ulog n)
Proof
  rw[big_O_def] >>
  metis_tac[size_le_ulog]
QED

(* Theorem: (valueOf (zeroM n) <=> (n = 0)) /\
            (stepsOf o zeroM) IN big_O (\n. ulog n) *)
(* Proof: by zeroM_value, zeroM_steps_big_O *)
Theorem zeroM_thm:
    !n. (valueOf (zeroM n) <=> (n = 0)) /\
       (stepsOf o zeroM) IN big_O (\n. ulog n)
Proof
  metis_tac[zeroM_value, zeroM_steps_big_O]
QED


(* ------------------------------------------------------------------------- *)

(* Define equal-to-one macro *)
Definition oneM_def:
    oneM n = eqM 1 n
End

(* Theorem: valueOf (oneM n) = (n = 1) *)
(* Proof: by oneM_def *)
Theorem oneM_value[simp]:
    !n. valueOf (oneM n) = (n = 1)
Proof
  rw[oneM_def]
QED

(* Theorem: stepsOf (oneM n) = size n *)
(* Proof: by oneM_def, size_1, max_1_size_n *)
Theorem oneM_steps[simp]:
    !n. stepsOf (oneM n) = size n
Proof
  rw[oneM_def, max_1_size_n]
QED

(* Theorem: (\n. stepsOf (oneM n)) IN big_O size *)
(* Proof:
   By big_O_def, oneM_steps, this is to show:
      ?k c. !n. k < n ==> size n <= c * size n
   or ?k c. !n. k < n ==> size n = 0 \/ 1 <= c
   Take k = 0, c = 1.
*)
Theorem oneM_cc:
    (\n. stepsOf (oneM n)) IN big_O size
Proof
  rw[big_O_def] >>
  qexists_tac `0` >>
  qexists_tac `1` >>
  fs[]
QED

(* Theorem: (\n. stepsOf (oneM n)) IN big_O ((POLY 1) o size) *)
(* Proof:
   By big_O_def, POLY_def, oneM_steps, this is to show:
      ?k c. !n. k < n ==> size <= c * size n
   or ?k c. !n. k < n ==> size n = 0 \/ 1 <= c
   Take k = 0, c = 1.
*)
Theorem oneM_poly_cc:
    (\n. stepsOf (oneM n)) IN big_O ((POLY 1) o size)
Proof
  rw[big_O_def, POLY_def] >>
  qexists_tac `0` >>
  qexists_tac `1` >>
  fs[]
QED

(* Theorem: (stepsOf o oneM) IN big_O (\n. ulog n) *)
(* Proof:
   By oneM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> size n <= c * ulog n
   Put k = 1, c = 2, then size n <= 2 * ulog n      by size_le_ulog
*)
Theorem oneM_steps_big_O:
    (stepsOf o oneM) IN big_O (\n. ulog n)
Proof
  rw[big_O_def] >>
  metis_tac[size_le_ulog]
QED

(* Theorem: (valueOf (oneM n) <=> (n = 1)) /\
            (stepsOf o oneM) IN big_O (\n. ulog n) *)
(* Proof: by oneM_value, oneM_steps_big_O *)
Theorem oneM_thm:
    !n. (valueOf (oneM n) <=> (n = 1)) /\
       (stepsOf o oneM) IN big_O (\n. ulog n)
Proof
  metis_tac[oneM_value, oneM_steps_big_O]
QED

(* ------------------------------------------------------------------------- *)

(* Twice monad *)
Definition twiceM_def:
    twiceM n = mulM n 2
End
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
Theorem twiceM_cc:
    (\n. stepsOf (twiceM n)) IN big_O size
Proof
  rw[twiceM_def, big_O_def] >>
  qexists_tac `0` >>
  qexists_tac `2` >>
  fs[]
QED

(* Theorem: (\n. stepsOf (twiceM n)) IN O_poly 1 *)
(* Proof:
   By twiceM_def, this is to show:
      (\n. size n * size 2) IN O_poly 1
   By O_poly_thm, this is to show:
      ?h k. !n. h < n ==> size n * size 2 <= k * size n
   Take h = 0, k = size 2.
   The result follows.
*)
Theorem twiceM_poly_cc:
    (\n. stepsOf (twiceM n)) IN O_poly 1
Proof
  rw[twiceM_def] >>
  rw[O_poly_thm] >>
  map_every qexists_tac [`0`, `size 2`] >>
  simp[]
QED

(* Theorem: valueOf (twiceM n) = 2 * n *)
(* Proof:
     valueOf (twiceM n)
   = valueOf (mulM n 2)   by twiceM_def
   = n * 2 = 2 * n        by mulM_value
*)
Theorem twiceM_value[simp]:
    !n. valueOf (twiceM n) = 2 * n
Proof
  rw[twiceM_def]
QED

(* Theorem: stepsOf (twiceM n) = 2 * (size n) *)
(* Proof:
     stepsOf (twiceM n)
   = stepsOf (mulM n 2)     by twiceM_def
   = (size n) * (size 2)    by mulM_steps
   = (size n) * 2           by size_2
   = 2 * (size n)           by MULT_COMM
*)
Theorem twiceM_steps[simp]:
    !n. stepsOf (twiceM n) = 2 * (size n)
Proof
  rw[twiceM_def, size_2]
QED
(* verifies twiceM_cc: (\n. stepsOf (twiceM n)) IN O_poly 1 *)

(* Theorem: (stepsOf o twiceM) IN big_O (\n. ulog n) *)
(* Proof:
   By twiceM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> 2 * size n <= c * ulog n
   Put k = 1, c = 4, then 2 * size n <= 4 * ulog n      by size_le_ulog
*)
Theorem twiceM_steps_big_O:
    (stepsOf o twiceM) IN big_O (\n. ulog n)
Proof
  rw[big_O_def] >>
  qexists_tac `1` >>
  qexists_tac `4` >>
  rpt strip_tac >>
  `size n <= 2 * ulog n` by metis_tac[size_le_ulog] >>
  decide_tac
QED

(* Theorem: (valueOf (twiceM n) = (2 * n)) /\
            (stepsOf o twiceM) IN big_O (\n. ulog n) *)
(* Proof: by twiceM_value, twiceM_steps_big_O *)
Theorem twiceM_thm:
    !n. (valueOf (twiceM n) = (2 * n)) /\
       (stepsOf o twiceM) IN big_O (\n. ulog n)
Proof
  metis_tac[twiceM_value, twiceM_steps_big_O]
QED


(* ------------------------------------------------------------------------- *)

(* HALF monad *)
Definition halfM_def:   halfM n = divM n 2
End
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
Theorem halfM_cc:
    (\n. stepsOf (halfM n)) IN big_O size
Proof
  rw[big_O_def, halfM_def] >>
  qexists_tac `0` >>
  qexists_tac `size 2` >>
  fs[]
QED

(* Theorem: valueOf (halfM n) = HALF n *)
(* Proof:
     valueOf (halfM n)
   = valueOf (divM n 2)    by halfM_def
   = n DIV 2               by divM_value
   = HALF n                by notation
*)
Theorem halfM_value[simp]:
    !n. valueOf (halfM n) = HALF n
Proof
  rw[halfM_def]
QED

(* Theorem: stepsOf (halfM n) = 2 * size n *)
(* Proof:
     stepsOf (halfM n)
   = stepsOf (divM n 2)    by halfM_def
   = size n * size 2       by divM_steps
   = size n * 2            by size_2
   = 2 * size x
*)
Theorem halfM_steps[simp]:
    !n. stepsOf (halfM n) = 2 * size n
Proof
  rw[halfM_def, size_2]
QED
(* verifies halfM_cc: (\n. stepsOf (halfM n)) IN big_O size *)

(* Theorem: (stepsOf o halfM) IN big_O (\n. ulog n) *)
(* Proof:
   By halfM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> 2 * size n <= c * ulog n
   Put k = 1, c = 4, then 2 * size n <= 4 * ulog n      by size_le_ulog
*)
Theorem halfM_steps_big_O:
    (stepsOf o halfM) IN big_O (\n. ulog n)
Proof
  rw[big_O_def] >>
  qexists_tac `1` >>
  qexists_tac `4` >>
  rpt strip_tac >>
  `size n <= 2 * ulog n` by metis_tac[size_le_ulog] >>
  decide_tac
QED

(* Theorem: (valueOf (halfM n) = HALF n) /\
            (stepsOf o halfM) IN big_O (\n. ulog n) *)
(* Proof: by halfM_value, halfM_steps_big_O *)
Theorem halfM_thm:
    !n. (valueOf (halfM n) = HALF n) /\
       (stepsOf o halfM) IN big_O (\n. ulog n)
Proof
  metis_tac[halfM_value, halfM_steps_big_O]
QED


(* ------------------------------------------------------------------------- *)

(* Parity monad *)
Definition parityM_def:   parityM n = modM n 2
End

(* Theorem: valueOf (parityM n) = n MOD 2 *)
(* Proof: by parityM_def, modM_value *)
Theorem parityM_value[simp]:
    !n. valueOf (parityM n) = n MOD 2
Proof
  rw[parityM_def]
QED

(* Theorem: stepsOf (parityM n) = 2 * size n *)
(* Proof:
     stepsOf (parityM n)
   = stepsOf (modM n 2)     by parityM_def
   = size n * size 2        by modM_steps
   = size n * 2             by size_2
   = 2 * size n             by arithmetic
*)
Theorem parityM_steps[simp]:
    !n. stepsOf (parityM n) = 2 * size n
Proof
  rw[parityM_def, size_2]
QED

(* Theorem: stepsOf (parityM n)) IN big_O size *)
(* Proof:
   By big_O_def, parityM_steps, this is to show:
      ?k c. !n. k < n ==> TWICE (size n) <= c * size n
   or ?k c. !n. k < n ==> 2 <= c
   Take k = 0, c = 2.
*)
Theorem parityM_cc:
    (\n. stepsOf (parityM n)) IN big_O size
Proof
  rw[big_O_def] >>
  qexists_tac `0` >>
  qexists_tac `2` >>
  fs[]
QED

(* Theorem: (\n. stepsOf (parityM n)) IN big_O ((POLY 1) o size) *)
(* Proof:
   By big_O_def, POLY_def, parityM_steps, this is to show:
      ?k c. !n. k < n ==> TWICE (size n) <= c * size n
   or ?k c. !n. k < n ==> 2 <= c
   Take k = 0, c = 2.
*)
Theorem parityM_poly_cc:
    (\n. stepsOf (parityM n)) IN big_O ((POLY 1) o size)
Proof
  rw[big_O_def, POLY_def] >>
  qexists_tac `0` >>
  qexists_tac `2` >>
  fs[]
QED

(* Theorem: (\n. n MOD 2) IN big_O (K 1) *)
(* Proof:
   By big_O_def, this is to show:
      ?k c. !n. k < n ==> n MOD 2 <= c
   Note n MOD 2 = 0 or 1    by MOD_LESS
   Take k = 0, c = 1.
*)
Theorem parity_cc:
    (\n. n MOD 2) IN big_O (K 1)
Proof
  rw[big_O_def] >>
  qexists_tac `0` >>
  qexists_tac `1` >>
  rw[] >>
  `n MOD 2 < 2` by rw[MOD_LESS] >>
  decide_tac
QED

(* Theorem: (stepsOf o parityM) IN big_O (\n. ulog n) *)
(* Proof:
   By parityM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> 2 * size n <= c * ulog n
   Put k = 1, c = 4, then 2 * size n <= 4 * ulog n      by size_le_ulog
*)
Theorem parityM_steps_big_O:
    (stepsOf o parityM) IN big_O (\n. ulog n)
Proof
  rw[big_O_def] >>
  qexists_tac `1` >>
  qexists_tac `4` >>
  rpt strip_tac >>
  `size n <= 2 * ulog n` by metis_tac[size_le_ulog] >>
  decide_tac
QED

(* Theorem: (valueOf (parityM n) = n MOD 2) /\
            (stepsOf o parityM) IN big_O (\n. ulog n) *)
(* Proof: by parityM_value, parityM_steps_big_O *)
Theorem parityM_thm:
    !n. (valueOf (parityM n) = n MOD 2) /\
       (stepsOf o parityM) IN big_O (\n. ulog n)
Proof
  metis_tac[parityM_value, parityM_steps_big_O]
QED


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
Definition evenM_def:
    evenM n = do
                 z <- parityM n;
                 zeroM z;
              od
End
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
Theorem evenM_value[simp]:
    !n. valueOf (evenM n) = (EVEN n)
Proof
  rw[evenM_def] >>
  rw[EVEN_MOD2]
QED

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
Theorem evenM_steps[simp]:
    !n. stepsOf (evenM n) = 2 * size n + 1
Proof
  rw[evenM_def] >>
  `n MOD 2 < 2` by rw[] >>
  metis_tac[size_0, size_1, DECIDE``1 <= 1 /\ (n < 2 <=> (n = 0) \/ (n = 1))``]
QED
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
Theorem evenM_cc:
    (\n. stepsOf (evenM n)) IN big_O size
Proof
  rw[evenM_def] >>
  rw[big_O_def] >>
  map_every qexists_tac [`0`, `3`] >>
  rpt strip_tac >>
  `n MOD 2 < 2` by rw[] >>
  `size (n MOD 2) = 1` by metis_tac[size_0, size_1, DECIDE``n < 2 ==> (n = 0) \/ (n = 1)``] >>
  `1 <= size n` by rw[one_le_size] >>
  rw[]
QED
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
Theorem zeroM_parity_cc:
    (\n. stepsOf (zeroM (n MOD 2))) IN big_O (K 1)
Proof
  rw[big_O_def] >>
  qexists_tac `0` >>
  qexists_tac `1` >>
  rpt strip_tac >>
  `n MOD 2 < 2` by rw[] >>
  metis_tac[size_0, size_1, DECIDE``1 <= 1 /\ (n < 2 <=> (n = 0) \/ (n = 1))``]
QED

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
Theorem evenM_steps_big_O:
    (stepsOf o evenM) IN big_O (\n. ulog n)
Proof
  rw[big_O_def] >>
  qexists_tac `1` >>
  qexists_tac `5` >>
  rpt strip_tac >>
  `size n <= 2 * ulog n` by metis_tac[size_le_ulog] >>
  `1 <= ulog n` by rw[ulog_ge_1] >>
  decide_tac
QED

(* Theorem: (valueOf (evenM n) <=> EVEN n) /\
            (stepsOf o evenM) IN big_O (\n. ulog n) *)
(* Proof: by evenM_value, evenM_steps_big_O *)
Theorem evenM_thm:
    !n. (valueOf (evenM n) <=> EVEN n) /\
       (stepsOf o evenM) IN big_O (\n. ulog n)
Proof
  metis_tac[evenM_value, evenM_steps_big_O]
QED


(* ------------------------------------------------------------------------- *)

(* SQ monad *)
Definition sqM_def:   sqM n = mulM n n
End
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
Theorem sqM_value[simp]:
    !n. valueOf (sqM n) = SQ n
Proof
  rw[sqM_def]
QED

(* Theorem: stepsOf (sqM n) = (size n) ** 2 *)
(* Proof:
     stepsOf (sqM n)
   = stepsOf (mulM n n)    by sqM_def
   = size n * size n       by mulM_steps
   = size n ** 2           by EXP_2
*)
Theorem sqM_steps[simp]:
    !n. stepsOf (sqM n) = (size n) ** 2
Proof
  rw[sqM_def, Once EXP_2]
QED
(* verifies sqM_poly_cc: (\n. stepsOf (sqM n)) IN big_O (POLY 2 o size) *)

(* Theorem: (\n. stepsOf (sqM n)) IN big_O (POLY 2 o size) *)
(* Proof:
   By big_O_def, POLY_def, sqM_def, mulM_steps, this is to show:
      ?k c. !n. k < n ==> size n * size n <= c * size n * size n
   Take k = 0, c = 1.
*)
Theorem sqM_poly_cc:
    (\n. stepsOf (sqM n)) IN big_O (POLY 2 o size)
Proof
  rw[big_O_def, POLY_def, sqM_def] >>
  qexists_tac `0` >>
  qexists_tac `1` >>
  fs[]
QED

(* Theorem: (UNCURRY (\x y. stepsOf (mulM x y))) z <
            ((POLY 2) o (UNCURRY (\x y. 1 + MAX (size x) (size y)))) z *)
(* Proof: by mulM_steps, POLY_def, and MAX_DEF *)
Theorem mulM_poly_cc:
    !z. (UNCURRY (\x y. stepsOf (mulM x y))) z <
       ((POLY 2) o (UNCURRY (\x y. 1 + MAX (size x) (size y)))) z
Proof
  rw[] >>
  (Cases_on `z` >> simp[]) >>
  rw[mulM_steps, POLY_def] >>
  qabbrev_tac `z = MAX (size q) (size r) + 1` >>
  `size q < z` by rw[MAX_DEF, Abbr`z`] >>
  `size r < z` by rw[MAX_DEF, Abbr`z`] >>
  `size q * size r < z * z` by rw[LT_MONO_MULT2] >>
  metis_tac[EXP_2]
QED

(* Theorem: (stepsOf o sqM) IN big_O (\n. (ulog n) ** 2) *)
(* Proof:
   By sqM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> size n ** 2 <= c * ulog n ** 2
   Put k = 1, c = 4,
      then size n <= 2 * ulog n               by size_le_ulog
       so  (size n) ** 2 <= 4 (ulog n) ** 2   by SQ_LE
*)
Theorem sqM_steps_big_O:
    (stepsOf o sqM) IN big_O (\n. (ulog n) ** 2)
Proof
  rw[big_O_def] >>
  qexists_tac `1` >>
  qexists_tac `4` >>
  rpt strip_tac >>
  `size n <= 2 * ulog n` by metis_tac[size_le_ulog] >>
  `SQ (size n) <= SQ (2 * ulog n)` by rw[SQ_LE] >>
  `SQ (2 * ulog n) = 4 * SQ (ulog n)` by decide_tac >>
  fs[]
QED

(* Theorem: (valueOf (sqM n) = SQ n) /\
            (stepsOf o sqM) IN big_O (\n. (ulog n) ** 2) *)
(* Proof: by sqM_value, sqM_steps_big_O *)
Theorem sqM_thm:
    !n. (valueOf (sqM n) = SQ n) /\
       (stepsOf o sqM) IN big_O (\n. (ulog n) ** 2)
Proof
  metis_tac[sqM_value, sqM_steps_big_O]
QED


(* ------------------------------------------------------------------------- *)

(* Increment monad *)
Definition incM_def:
    incM n = addM n 1
End
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
Theorem incM_cc:
    (\n. stepsOf (incM n)) IN O_poly 1
Proof
  rw[incM_def] >>
  rw[O_poly_thm] >>
  map_every qexists_tac [`0`, `1`] >>
  simp[one_le_size]
QED

(* Theorem: valueOf (incM n) = n + 1 *)
(* Proof:
     valueOf (incM n)
   = valueOf (addM n 1)   by incM_def
   = n + 1                by addM_value
*)
Theorem incM_value[simp]:
    !n. valueOf (incM n) = n + 1
Proof
  rw[incM_def]
QED

(* Theorem: stepsOf (incM n) = size n *)
(* Proof:
     stepsOf (incM n)
   = stepsOf (addM n 1)     by incM_def
   = MAX (size n) (size 1)  by addM_steps
   = MAX (size n) 1         by size_1
   = size n                 by max_1_size_n, MAX_COMM
*)
Theorem incM_steps[simp]:
    !n. stepsOf (incM n) = size n
Proof
  rw[incM_def] >>
  metis_tac[max_1_size_n, MAX_COMM]
QED
(* verifies incM_cc: (\n. stepsOf (incM n)) IN O_poly 1 *)

(* Theorem: (stepsOf o incM) IN big_O (\n. ulog n) *)
(* Proof:
   By incM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> size n <= c * ulog n
   Put k = 1, c = 2, then size n <= 2 * ulog n  by size_le_ulog
*)
Theorem incM_steps_big_O:
    (stepsOf o incM) IN big_O (\n. ulog n)
Proof
  rw[big_O_def] >>
  metis_tac[size_le_ulog]
QED

(* Theorem: (valueOf (incM n) = n + 1) /\
            (stepsOf o incM) IN big_O (\n. ulog n) *)
(* Proof: by incM_value, incM_steps_big_O *)
Theorem incM_thm:
    !n. (valueOf (incM n) = n + 1) /\
       (stepsOf o incM) IN big_O (\n. ulog n)
Proof
  metis_tac[incM_value, incM_steps_big_O]
QED


(* ------------------------------------------------------------------------- *)

(* Decrement monad *)
Definition decM_def:
    decM n = subM n 1
End
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
Theorem decM_cc:
    (\n. stepsOf (decM n)) IN O_poly 1
Proof
  rw[decM_def] >>
  rw[O_poly_thm] >>
  map_every qexists_tac [`0`, `1`] >>
  simp[one_le_size]
QED

(* Theorem: valueOf (decM n) = n - 1 *)
(* Proof:
     valueOf (decM n)
   = valueOf (subM n 1)   by decM_def
   = n - 1                by subM_value
*)
Theorem decM_value[simp]:
    !n. valueOf (decM n) = n - 1
Proof
  rw[decM_def]
QED

(* Theorem: stepsOf (decM n) = size n *)
(* Proof:
     stepsOf (decM n)
   = stepsOf (subM n 1)     by decM_def
   = MAX (size n) (size 1)  by subM_steps
   = MAX (size n) 1         by size_1
   = size n                 by max_1_size_n, MAX_COMM
*)
Theorem decM_steps[simp]:
    !n. stepsOf (decM n) = size n
Proof
  rw[decM_def] >>
  metis_tac[max_1_size_n, MAX_COMM]
QED
(* verifies decM_cc: (\n. stepsOf (decM n)) IN O_poly 1 *)

(* Theorem: (stepsOf o decM) IN big_O (\n. ulog n) *)
(* Proof:
   By decM_steps and big_O_def, this is to show:
      ?k c. !n. k < n ==> size n <= c * ulog n
   Put k = 1, c = 2, then size n <= 2 * ulog n  by size_le_ulog
*)
Theorem decM_steps_big_O:
    (stepsOf o decM) IN big_O (\n. ulog n)
Proof
  rw[big_O_def] >>
  metis_tac[size_le_ulog]
QED

(* Theorem: (valueOf (decM n) = n - 1) /\
            (stepsOf o decM) IN big_O (\n. ulog n) *)
(* Proof: by decM_value, decM_steps_big_O *)
Theorem decM_thm:
    !n. (valueOf (decM n) = n - 1) /\
       (stepsOf o decM) IN big_O (\n. ulog n)
Proof
  metis_tac[decM_value, decM_steps_big_O]
QED


(* ------------------------------------------------------------------------- *)

(* Less-or-equal monad *)
Definition leqM_def:
    leqM n m = do
                 z <- subM n m;
                 zeroM z
               od
End
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
Theorem leqM_value[simp]:
    !n m. valueOf (leqM n m) = (n <= m)
Proof
  rw[leqM_def]
QED

(* Theorem: stepsOf (leqM n) = 2 * (size n) *)
(* Proof:
     stepsOf (leqM n m)
   = stepsOf (do z <- subM n m; zeroM z od)   by leqM_def
   = MAX (size n) (size m) + (size (n - m))   by subM_steps, subM_value, zeroM_steps
*)
Theorem leqM_steps[simp]:
    !n m. stepsOf (leqM n m) = MAX (size n) (size m) + (size (n - m))
Proof
  rw[leqM_def]
QED

(* Theorem: stepsOf (leqM n m) = size (MAX n m) + size (n - m) *)
(* Proof: leqM_steps, size_max *)
Theorem leqM_steps_alt:
    !n m. stepsOf (leqM n m) = size (MAX n m) + size (n - m)
Proof
  rw[leqM_steps, size_max]
QED

(* Theorem: stepsOf (leqM n m) <= 2 * size (MAX n m) *)
(* Proof:
      stepsOf (leqM n m)
    = MAX (size n) (size m) + (size (n - m))    by leqM_steps
    = size (MAX n m) + size (n - m)             by size_max
   <= size (MAX n m) + size n                   by size_monotone_le
   <= size (MAX n m) + size (MAX n m)           by size_monotone_le
    = 2 * size (MAX n m)
*)
Theorem leqM_steps_le:
    !n m. stepsOf (leqM n m) <= 2 * size (MAX n m)
Proof
  rpt strip_tac >>
  `stepsOf (leqM n m) = size (MAX n m) + size (n - m)` by rw[leqM_steps, size_max] >>
  `size (n - m) <= size n` by rw[size_monotone_le] >>
  `size n <= size (MAX n m)` by rw[size_monotone_le] >>
  decide_tac
QED

(* Theorem: (\(n,m). stepsOf (leqM n m)) z ** 2 =
            (POLY 2 o (\(n,m). size (n - m) + MAX (size n) (size m))) z *)
(* Proof: by leqM_def, POLY_def. *)
Theorem leqM_poly_cc:
    !z. (\(n,m). stepsOf (leqM n m)) z ** 2 =
       (POLY 2 o (\(n,m). size (n - m) + MAX (size n) (size m))) z
Proof
  rw[leqM_def] >>
  rw[POLY_def]
QED
(* This is not proving anything, the exponent 2 comes from POLY 2 *)

(* ------------------------------------------------------------------------- *)

(* Less-than monad *)
Definition ltM_def:
    ltM n m = do
                 b <- eqM n m;
                 if b then unit F
                 else leqM n m
              od
End
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
Theorem ltM_value[simp]:
    !n m. valueOf (ltM n m) = (n < m)
Proof
  rw[ltM_def]
QED

(* Theorem: stepsOf (leqM n) = if (n = m) then size n else 2 * MAX (size n) (size m) + size (n - m) *)
(* Proof:
     stepsOf (ltM n m)
   = stepsOf (do b <- eqM n m; if b then unit F else leqM n m od)   by leqM_def
   = MAX (size n) (size m) + MAX (size n) (size m) + (size (n - m)) by eqM_steps, subM_steps, subM_value, zeroM_steps
   = MAX (size n) (size m) = size n             if n = m
   = 2 * MAX (size n) (size m) + size (n - m)   if n <> m
*)
Theorem ltM_steps[simp]:
    !n m. stepsOf (ltM n m) = if (n = m) then size n else 2 * MAX (size n) (size m) + size (n - m)
Proof
  rw[ltM_def]
QED

(* Theorem: (\(n,m). stepsOf (ltM n m)) z ** 1 =
            (POLY 1 o (\(n,m). if (n = m) then size n else size (n - m) + 2 * MAX (size n) (size m))) z *)
(* Proof: by ltM_def, POLY_def. *)
Theorem ltM_poly_cc:
    !z. (\(n,m). stepsOf (ltM n m)) z ** 1 =
       (POLY 1 o (\(n,m). if (n = m) then size n else size (n - m) + 2 * MAX (size n) (size m))) z
Proof
  rw[ltM_def] >>
  rw[POLY_def]
QED
(* This is not proving anything, the exponent 2 comes from POLY 2 *)

(* ------------------------------------------------------------------------- *)

(* Greater than 1 monad *)
Definition gt1M_def:
    gt1M n = ltM 1 n
End
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
Theorem gt1M_value[simp]:
    !n. valueOf (gt1M n) = (1 < n)
Proof
  rw[gt1M_def]
QED

(* Theorem: stepsOf (gt1M n) = if (n = 1) then 1 else 1 + 2 * size n *)
(* Proof:
     stepsOf (gt1M n)
   = stepsOf (ltM 1 n)   by gt1M_def
   = size n = size 1 = 1                       if n = 1, size_1
   = 2 * MAX (size 1) (size n) + size (1 - n)  if n <> 1
   = 2 * size n + size (1 - n)                 by size_1, max_1_size_n
   = 2 * size n + 1                            by size_0, size_1
*)
Theorem gt1M_steps[simp]:
    !n. stepsOf (gt1M n) = if (n = 1) then 1 else 1 + 2 * size n
Proof
  rpt strip_tac >>
  `MAX 1 (size n) = size n` by metis_tac[max_1_size_n] >>
  simp[gt1M_def] >>
  Cases_on `n = 1` >-
  metis_tac[] >>
  Cases_on `n = 0` >-
  fs[] >>
  `1 - n = 0` by decide_tac >>
  simp[]
QED

(* ------------------------------------------------------------------------- *)

(* Define less-equal-1 macro *)
Definition le1M_def:
    le1M n = do
               gd <- gt1M n;
               notM gd;
             od
End
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
Theorem le1M_value[simp]:
    !n. valueOf (le1M n) = (n <= 1)
Proof
  simp[le1M_def]
QED


(* Theorem: stepsOf (le1M n) = if n = 1 then 2 else 2 + 2 * size n *)
(* Proof:
     stepsOf (le1M n)
   = stepsOf (gt1M n) + stepsOf (notM (1 < n))     by le1M_def
   = (if n = 1 then 1 else 1 + 2 * (size n)) + 1   by gt1M_steps
   = if n = 1 then 2 else 2 + 2 * size n           by arithmetic
*)
Theorem le1M_steps[simp]:
    !n. stepsOf (le1M n) = if n = 1 then 2 else 2 + 2 * size n
Proof
  simp[le1M_def]
QED

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
Theorem appendM_value[simp]:
    !l1 l2. valueOf (appendM l1 l2) = l1 ++ l2
Proof
  ho_match_mp_tac (theorem "appendM_ind") >>
  rw[] >>
  (Cases_on `l1` >> rw[Once appendM_def])
QED

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
Theorem snocM_value:
  !x ls. valueOf (snocM x ls) = SNOC x ls
Proof
  recInduct snocM_ind >>
  rw[] >>
  Cases_on `ls` >> rw[Once snocM_def, GSYM SNOC_APPEND]
QED

(* ------------------------------------------------------------------------- *)
(*===========================================================================*)
