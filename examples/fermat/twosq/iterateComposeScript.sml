(* ------------------------------------------------------------------------- *)
(* Iteration of Involution Composition                                       *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

open arithmeticTheory pred_setTheory dividesTheory gcdsetTheory numberTheory
     combinatoricsTheory;

(* declare new theory at start *)
val _ = new_theory "iterateCompose";

(* ------------------------------------------------------------------------- *)

(* val _ = load "helperTwosqTheory"; *)
open helperTwosqTheory;

(* val _ = load "involuteFixTheory"; *)
open involuteTheory; (* for involute_bij *)
open involuteFixTheory;

(* val _ = load "iterateComputeTheory"; *)
open iterationTheory;
open iterateComputeTheory; (* for iterate_while_thm *)

val _ = temp_overload_on("SQ", ``\n. n * (n :num)``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

(* ------------------------------------------------------------------------- *)
(* Iteration of Involution Composition Documentation                         *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported, ! are in compute):

   Involution Composition Orbits:
   involute_involute_permutes
                   |- !f g s. f involute s /\ g involute s ==> f o g PERMUTES s
   involute_involute_involute
                   |- !f g s. f involute s /\ g involute s /\ f o g = g o f ==>
                              f o g involute s

   Orbit as path:
   involute_compose_inv
                   |- !f g s x. f involute s /\ g involute s /\ x IN s ==>
                                LINV (f o g) s x = (g o f) x
   involute_funpow_inv
                   |- !f g s x n. f involute s /\ g involute s /\ x IN s ==>
                                  FUNPOW (f o g) n (FUNPOW (g o f) n x) = x

   Iteration of Composed Involutions:
   iterate_involute_compose_inv
                   |- !f g s x n. f involute s /\ g involute s /\ x IN s ==>
                                  LINV (FUNPOW (f o g) n) s x = FUNPOW (g o f) n x
   iterate_involute_compose_eqn
                   |- !f g s x n. f involute s /\ g involute s /\ x IN s ==>
                                  FUNPOW (g o f) n x = (g o FUNPOW (f o g) n o g) x
   iterate_involute_compose_shift
                   |- !f g s x n. f involute s /\ g involute s /\ x IN s ==>
                                  f (FUNPOW (g o f) n x) = FUNPOW (f o g) n (f x)

   Iteration Period and Fixes:
   iterate_involute_mod_period
                   |- !f g s x p i j. FINITE s /\ f involute s /\ g involute s /\ x IN s /\
                         p = iterate_period (f o g) x ==>
                        (FUNPOW (f o g) i x = FUNPOW (g o f) j x <=> (i + j) MOD p = 0)
   involute_involute_period_inv
                   |- !f g s x. FINITE s /\ f involute s /\ g involute s /\ x IN s ==>
                        iterate_period (g o f) x = iterate_period (f o g) x
   involute_involute_fixes_both
                   |- !f g s p x. f involute s /\ g involute s /\ x IN fixes f s /\
                         p = iterate_period (f o g) x ==> (p = 1 <=> x IN fixes g s)
   involute_involute_fix_orbit_1
                   |- !f g s x p i j. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                         p = iterate_period (f o g) x ==>
                        (FUNPOW (f o g) i x = f (FUNPOW (f o g) j x) <=> (i + j) MOD p = 0)
   involute_involute_fix_orbit_2
                   |- !f g s x p i j. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                         p = iterate_period (f o g) x ==>
                        (FUNPOW (f o g) i x = g (FUNPOW (f o g) j x) <=> (i + j + 1) MOD p = 0)
   involute_involute_fix_orbit_fix_even
                   |- !f g s p x. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                         p = iterate_period (f o g) x /\ EVEN p ==>
                         FUNPOW (f o g) (HALF p) x IN fixes f s
   involute_involute_fix_orbit_fix_odd
                   |- !f g s p x. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                         p = iterate_period (f o g) x /\ ODD p ==>
                         FUNPOW (f o g) (HALF p) x IN fixes g s
   involute_involute_fix_orbit_fix_even_inv
                   |- !f g s p x.  FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                                   p = iterate_period (g o f) x /\ EVEN p ==>
                                   FUNPOW (g o f) (HALF p) x IN fixes f s
   involute_involute_fix_orbit_fix_odd_inv
                   |- !f g s p x. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                                  p = iterate_period (g o f) x /\ ODD p ==>
                                  FUNPOW (g o f) (1 + HALF p) x IN fixes g s
   involute_involute_fix_orbit_fix_even_distinct
                   |- !f g s p x y. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                         p = iterate_period (f o g) x /\
                        (y = FUNPOW (f o g) (HALF p) x) /\ EVEN p ==> y IN fixes f s /\ y <> x
   involute_involute_fix_orbit_fix_even_distinct_iff
                   |- !f g s p x y. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                         p = iterate_period (f o g) x /\
                        (y = FUNPOW (f o g) (HALF p) x) /\ EVEN p ==>
                         y IN fixes f s /\ (y = x <=> p = 0)
   involute_involute_fix_orbit_fix_odd_distinct
                   |- !f g s p x y. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                         p = iterate_period (f o g) x /\
                        (y = FUNPOW (f o g) (HALF p) x) /\ ODD p ==>
                         y IN fixes g s /\ (1 < p ==> y <> x)
   involute_involute_fix_orbit_fix_odd_distinct_iff
                   |- !f g s p x y. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                         p = iterate_period (f o g) x /\
                        (y = FUNPOW (f o g) (HALF p) x) /\ ODD p ==>
                         y IN fixes g s /\ (y = x <=> p = 1)
   involute_involute_fix_sing_period_odd
                   |- !f g s p x. FINITE s /\ f involute s /\ g involute s /\ fixes f s = {x} /\
                         p = iterate_period (f o g) x ==> ODD p
   involute_involute_fix_iterates_1
                   |- !f g s p x. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                         p = iterate_period (f o g) x ==>
                        !j. j <= p ==> f (FUNPOW (f o g) j x) = FUNPOW (f o g) (p - j) x
   involute_involute_fix_iterates_2
                   |- !f g s p x. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                         p = iterate_period (f o g) x ==>
                        !j. j < p ==> g (FUNPOW (f o g) j x) = FUNPOW (f o g) (p - 1 - j) x
   involute_involute_fix_even_period_fix
                   |- !f g s p x. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                         p = iterate_period (f o g) x /\ EVEN p ==>
                        !j. 0 < j /\ j < p ==> (FUNPOW (f o g) j x IN fixes f s <=> (j = HALF p))
   involute_involute_fix_odd_period_fix
                   |- !f g s p x. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                         p = iterate_period (f o g) x /\ ODD p ==>
                        !j. j < p ==> (FUNPOW (f o g) j x IN fixes g s <=> (j = HALF p))

   Iteration Mate Involution:
   iterate_mate_def      |- !f g x. iterate_mate f g x =
                                   (let h = HALF (iterate_period (f o g) x)
                                     in if f x = x then FUNPOW (f o g) h x
                                        else if g x = x then FUNPOW (g o f) h x
                                        else x)
   iterate_mate_element  |- !f g s x. f involute s /\ g involute s /\ x IN s ==>
                                      iterate_mate f g x IN s
   iterate_mate_reverse  |- !f g s x. FINITE s /\ f involute s /\ g involute s /\ x IN s ==>
                                      iterate_mate g f x = iterate_mate f g x
   iterate_mate_fixes_mate
                         |- !f g s x. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s ==>
                                      iterate_mate f g (iterate_mate f g x) = x
   iterate_mate_mate     |- !f g s x. FINITE s /\ f involute s /\ g involute s /\ x IN s ==>
                                      iterate_mate f g (iterate_mate f g x) = x
   iterate_mate_fixes_mate_fixes
                         |- !f g s x. FINITE s /\ f involute s /\ g involute s /\
                                      x IN fixes f s UNION fixes g s ==>
                                      iterate_mate f g x IN fixes f s UNION fixes g s
   iterate_mate_involute_fixes
                         |- !f g s. FINITE s /\ f involute s /\ g involute s ==>
                                    iterate_mate f g involute fixes f s UNION fixes g s

   Using direct WHILE:
   involute_involute_fix_odd_period_fix_while
                         |- !f g s p x. FINITE s /\ f involute s /\ g involute s /\
                                        x IN fixes f s /\
                                        p = iterate_period (f o g) x /\ ODD p ==>
                                        WHILE (\y. g y <> y) (f o g) x IN fixes g s
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Involution Composition Orbits                                             *)
(* ------------------------------------------------------------------------- *)

(* Theorem: f involute s /\ g involute s ==> (f o g) PERMUTES s *)
(* Proof:
   Note f PERMUTES s /\ g PERMUTES s   by involute_bij
    ==> (f o g) PERMUTES s             by BIJ_COMPOSE
*)
Theorem involute_involute_permutes:
  !f g s. f involute s /\ g involute s ==> (f o g) PERMUTES s
Proof
  metis_tac[involute_bij, BIJ_COMPOSE]
QED

(* Idea: (f o g) involute s iff f and g are inverses. *)

(* Theorem: f involute s /\ g involute s /\ f o g = g o f ==> (f o g) involute s *)
(* Proof:
   Note !x. x IN s ==>
        (f x) IN s /\ (g x) IN s    by involution
   Thus (f o g) x = f (g x) IN s    by o_THM, (g x) IN s
    and (f o g) ((f o g) x)
      = (f o g) ((g o f) x)         by given
      = f (g (g (f x)))             by o_THM
      = f (f x)                     by g involute s, (f x) IN s
      = x                           by f involute s
*)
Theorem involute_involute_involute:
  !f g s. f involute s /\ g involute s /\ f o g = g o f ==> (f o g) involute s
Proof
  ntac 4 strip_tac >>
  `!x. x IN s ==> (f x) IN s /\ (g x) IN s` by rw[] >>
  simp[] >>
  rpt strip_tac >>
  `!x. f (g x) = g (f x)` by fs[FUN_EQ_THM] >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------- *)
(* Orbit as path.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Theorem: f involute s /\ g involute s /\ x IN s ==>
            (LINV (f o g) s) x = (g o f) x *)
(* Proof:
   Note (f o g) PERMUTES s        by involute_involute_permutes
   Let y = LINV (f o g) s x,
       z = (g o f) x.
   Then y IN s                    by BIJ_LINV_ELEMENT
    and z IN s                    by o_THM
    Now (f o g) y = x             by BIJ_LINV_THM
    and (f o g) z
      = (f o g) ((g o f) x)
      = f (g (g (f x)))           by o_THM
      = f (f x)                   by g involute s, f x IN s
      = x                         by f involute s, x IN s
   Thus y = z                     by BIJ_IS_INJ
*)
Theorem involute_compose_inv:
  !f g s x. f involute s /\ g involute s /\ x IN s ==>
              (LINV (f o g) s) x = (g o f) x
Proof
  rpt strip_tac >>
  `(f o g) PERMUTES s` by rw[involute_involute_permutes] >>
  qabbrev_tac `y = LINV (f o g) s x` >>
  qabbrev_tac `z = (g o f) x` >>
  `y IN s` by metis_tac[BIJ_LINV_ELEMENT] >>
  `z IN s` by fs[Abbr`z`] >>
  `(f o g) y = x` by metis_tac[BIJ_LINV_THM] >>
  `(f o g) z = x` by fs[Abbr`z`] >>
  metis_tac[BIJ_IS_INJ]
QED

(* Theorem: f involute s /\ g involute s /\ x IN s ==>
            FUNPOW (f o g) n (FUNPOW (g o f) n x) = x *)
(* Proof:
   By induction on n.
   Base: FUNPOW (f o g) 0 (FUNPOW (g o f) 0 x) = x
           FUNPOW (f o g) 0 (FUNPOW (g o f) 0 x)
         = FUNPOW (f o g) 0 x                    by FUNPOW_0
         = x                                     by FUNPOW_0
   Step: !x. FUNPOW (f o g) n (FUNPOW (g o f) n x) = x ==>
         FUNPOW (f o g) (SUC n) (FUNPOW (g o f) (SUC n) x) = x
         Note (g o f) x IN s                     by BIJ_ELEMENT
           FUNPOW (f o g) (SUC n) (FUNPOW (g o f) (SUC n) x)
         = (f o g) (FUNPOW (f o g) n (FUNPOW (g o f) (SUC n) x))      by FUNPOW_SUC
         = (f o g) (FUNPOW (f o g) n (FUNPOW (g o f) n ((g o f) x)))  by FUNPOW
         = (f o g) ((g o f) x)       by induction hypothesis
         = x                         by f involute s, g involute s
*)
Theorem involute_funpow_inv:
  !f g s x n. f involute s /\ g involute s /\ x IN s ==>
              FUNPOW (f o g) n (FUNPOW (g o f) n x) = x
Proof
  ntac 3 strip_tac >>
  Induct_on `n` >-
  simp[] >>
  rpt strip_tac >>
  `(g o f) x IN s` by rw[BIJ_COMPOSE, BIJ_ELEMENT] >>
  `FUNPOW (f o g) (SUC n) (FUNPOW (g o f) (SUC n) x)
    = (f o g) (FUNPOW (f o g) n (FUNPOW (g o f) (SUC n) x))` by rw[FUNPOW_SUC] >>
  `_ = (f o g) (FUNPOW (f o g) n (FUNPOW (g o f) n ((g o f) x)))` by rw[FUNPOW] >>
  `_ = (f o g) ((g o f) x)` by rw[] >>
  `_ = x` by fs[] >>
  simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Iteration of Composed Involutions.                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: f involute s /\ g involute s /\ x IN s ==>
            FUNPOW (f o g) n (FUNPOW (g o f) n x) = x *)
(* Proof: by involute_funpow_inv *)
(* Theorem not stored as this is just an alias of involute_funpow_inv. *)
val iterate_involute_inv = prove(
  ``!f g s x n. f involute s /\ g involute s /\ x IN s ==>
     FUNPOW (f o g) n (FUNPOW (g o f) n x) = x``,
  rpt strip_tac >>
  irule involute_funpow_inv >>
  metis_tac[]);
(* This is just involute_funpow_inv.
   Funny that simp[involute_funpow_inv], rw, or metis_tac, or prove_tac ...
   will not work!
   Possibly due to difficulty in matching two function compositions.
   Many proofs below have such problems, which can be resolved by:
   . invoke imp_res_tac
   . invoke assume_tac
   . invoke drule_then
*)

(* Theorem: f involute s /\ g involute s /\ x IN s ==>
            (LINV (FUNPOW (f o g) n) s) x = FUNPOW (g o f) n x *)
(* Proof:
   Note (f o g) PERMUTES s        by involute_involute_permutes
    and (g o f) PERMUTES s        by involute_involute_permutes
   Let y = LINV (FUNPOW (f o g) n) s x,
       z = FUNPOW (g o f) n x,
       h = FUNPOW (f o g) n.
   Then h PERMUTES s              by FUNPOW_permutes
     so y IN s                    by BIJ_LINV_ELEMENT
    and z IN s                    by FUNPOW_closure
    Now h y = x                   by BIJ_LINV_THM, h PERMUTES s
    and h z = x                   by involute_funpow_inv
   Thus y = z                     by BIJ_IS_INJ
*)
Theorem iterate_involute_compose_inv:
  !f g s x n. f involute s /\ g involute s /\ x IN s ==>
              (LINV (FUNPOW (f o g) n) s) x = FUNPOW (g o f) n x
Proof
  rpt strip_tac >>
  `(f o g) PERMUTES s /\ (g o f) PERMUTES s` by rw[involute_involute_permutes] >>
  qabbrev_tac `y = LINV (FUNPOW (f o g) n) s x` >>
  qabbrev_tac `z = FUNPOW (g o f) n x` >>
  qabbrev_tac `h = FUNPOW (f o g) n` >>
  `h PERMUTES s` by rw[FUNPOW_permutes, Abbr`h`] >>
  `y IN s` by metis_tac[BIJ_LINV_ELEMENT] >>
  `z IN s` by fs[FUNPOW_closure, Abbr`z`] >>
  `h y = x` by metis_tac[BIJ_LINV_THM] >>
  imp_res_tac involute_funpow_inv >>
  `h z = x` by fs[Abbr`h`, Abbr`z`] >>
  metis_tac[BIJ_IS_INJ]
QED

(* Theorem: f involute s /\ g involute s /\ x IN s ==>
            FUNPOW (g o f) n x = (g o (FUNPOW (f o g) n) o g) x *)
(* Proof:
   By induction on n.
   Base: FUNPOW (g o f) 0 x = g (FUNPOW (f o g) 0 (g x))
         LHS = FUNPOW (g o f) 0 x = x    by FUNPOW_0
         RHS = g (FUNPOW (f o g) 0 (g x))
             = g (g x)                   by FUNPOW_0
             = x                         by g involute s
   Step: FUNPOW (g o f) n x = g (FUNPOW (f o g) n (g x)) ==>
         FUNPOW (g o f) (SUC n) x = g (FUNPOW (f o g) (SUC n) (g x))
           FUNPOW (g o f) (SUC n) x
         = (g o f) (FUNPOW (g o f) n x)          by FUNPOW_SUC
         = (g o f) (g (FUNPOW (f o g) n (g x))   by induction hypothesis
         = g ((f o g) (FUNPOW (f o g) n (g x)))  by o_THM
         = g (FUNPOW (f o g) (SUC n) (g x))      by FUNPOW_SUC
*)
Theorem iterate_involute_compose_eqn:
  !f g s x n. f involute s /\ g involute s /\ x IN s ==>
              FUNPOW (g o f) n x = (g o (FUNPOW (f o g) n) o g) x
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  simp[] >>
  simp[FUNPOW_SUC]
QED

(* Note:
     f o (g o f) o (g o f) o (g o f)
   = (f o g) o (f o g) o (f o g) o f      by associativity

   The following is a formal proof of this situation.
*)

(* Theorem: f involute s /\ g involute s /\ x IN s ==>
            f (FUNPOW (g o f) n x) = FUNPOW (f o g) n (f x) *)
(* Proof:
   By induction on n.
   Base: f (FUNPOW (g o f) 0 x) = FUNPOW (f o g) 0 (f x)
           f (FUNPOW (g o f) 0 x)
         = f x                       by FUNPOW_0
         = FUNPOW (f o g) 0 (f x)    by FUNPOW_0
   Step: f (FUNPOW (g o f) n x) = FUNPOW (f o g) n (f x) ==>
         f (FUNPOW (g o f) (SUC n) x) = FUNPOW (f o g) (SUC n) (f x)
           f (FUNPOW (g o f) (SUC n) x)
         = f ((g o f) (FUNPOW (g o f) n x))     by FUNPOW_SUC
         = f o g (f (FUNPOW (g o f) n x))       by o_THM
         = f o g (FUNPOW (f o g) n (f x))       by induction hypothesis
         = FUNPOW (f o g) (SUC n) (f x)         by FUNPOW_SUC
*)
Theorem iterate_involute_compose_shift:
  !f g s x n. f involute s /\ g involute s /\ x IN s ==>
              f (FUNPOW (g o f) n x) = FUNPOW (f o g) n (f x)
Proof
  rpt strip_tac >>
  Induct_on `n` >-
  simp[] >>
  simp[FUNPOW_SUC]
QED

(* ------------------------------------------------------------------------- *)
(* Iteration Period and Fixes.                                               *)
(* ------------------------------------------------------------------------- *)

(* Idea: iterates (f o g)^i = (g o f)^j iff (i + j) MOD p = 0. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\
            x IN s /\ p = iterate_period (f o g) x ==>
           (FUNPOW (f o g) i x = FUNPOW (g o f) j x <=> (i + j) MOD p = 0) *)
(* Proof:
   Let y = FUNPOW (f o g) i x,
       z = FUNPOW (g o f) j x,
       h = FUNPOW (f o g) j.
   Note f o g PERMUTES s           by involute_involute_permutes
    and g o f PERMUTES s           by involute_involute_permutes
     so y IN s and z IN s          by FUNPOW_closure
   also 0 < p                      by iterate_period_pos, FINITE s
    and h PERMUTES s               by FUNPOW_permutes
   Note h y
      = FUNPOW (f o g) (j + i) x   by FUNPOW_ADD
      = FUNPOW (f o g) (i + j) x   by arithmetic
    and h z = x                    by involute_funpow_inv, x IN s

       y = z
   <=> h y = h z                       by BIJ_DEF, INJ_EQ_11
   <=> FUNPOW (f o g) (i + j) x = x    by above
   <=> (i + j) MOD p = 0               by iterate_period_mod, 0 < p
*)
Theorem iterate_involute_mod_period:
  !f g s x p i j. FINITE s /\ f involute s /\ g involute s /\
                  x IN s /\ p = iterate_period (f o g) x ==>
                 (FUNPOW (f o g) i x = FUNPOW (g o f) j x <=> (i + j) MOD p = 0)
Proof
  rpt strip_tac >>
  qabbrev_tac `y = FUNPOW (f o g) i x` >>
  qabbrev_tac `z = FUNPOW (g o f) j x` >>
  qabbrev_tac `h = FUNPOW (f o g) j` >>
  `f o g PERMUTES s /\ g o f PERMUTES s` by rw[involute_involute_permutes] >>
  `y IN s /\ z IN s` by rw[FUNPOW_closure, Abbr`y`, Abbr`z`] >>
  `0 < p` by metis_tac[iterate_period_pos] >>
  `h PERMUTES s` by rw[FUNPOW_permutes, Abbr`h`] >>
  `h y = FUNPOW (f o g) (j + i) x` by fs[FUNPOW_ADD, Abbr`h`, Abbr`y`] >>
  `_ = FUNPOW (f o g) (i + j) x` by simp[] >>
  assume_tac involute_funpow_inv >>
  last_x_assum (qspecl_then [`f`, `g`, `s`, `x`, `j`] strip_assume_tac) >>
  `h z = x` by rfs[] >>
  `(y = z) <=> (h y = h z)` by metis_tac[BIJ_DEF, INJ_EQ_11] >>
  `_ = (FUNPOW (f o g) (i + j) x = x)` by fs[] >>
  `_ = ((i + j) MOD p = 0)` by rw[iterate_period_mod] >>
  simp[]
QED

(* Idea: period of (g o f) equals period of (f o g). *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN s ==>
            iterate_period (g o f) x = iterate_period (f o g) x *)
(* Proof:
   Cannot show: LINV (f o g) s = g o f
   see involute_compose_inv
   although there is iterate_involute_compose_inv.

   Note f o g PERMUTES s             by involute_involute_permutes
    and g o f PERMUTES s             by involute_involute_permutes
   Let p = iterate_period (f o g) x,
       q = iterate_period (g o f) x,
   then goal becomes: q = p.

   Note 0 < p /\ 0 < q               by iterate_period_pos
   By iterate_period_thm, this is to show:
   (1) FUNPOW (g o f) p x = x
       Note (0 + p) MOD p = 0        by DIVMOD_ID
         FUNPOW (g o f) p x
       = FUNPOW (f o g) 0 x          by iterate_involute_mod_period
       = x                           by FUNPOW_0
   (2) !m. 0 < m /\ m < p ==> FUNPOW (g o f) m x <> x
       Note ((p - m) + m) MOD p = 0  by DIVMOD_ID
        and p - m < p                by arithmetic
         FUNPOW (g o f) m x
       = FUNPOW (f o g) (p - m) x    by iterate_involute_mod_period
       <> x                          by iterate_period_minimal
*)
Theorem involute_involute_period_inv:
  !f g s x. FINITE s /\ f involute s /\ g involute s /\ x IN s ==>
            iterate_period (g o f) x = iterate_period (f o g) x
Proof
  rpt strip_tac >>
  `f o g PERMUTES s /\ g o f PERMUTES s` by rw[involute_involute_permutes] >>
  qabbrev_tac `p = iterate_period (f o g) x` >>
  qabbrev_tac `q = iterate_period (g o f) x` >>
  `0 < p /\ 0 < q` by metis_tac[iterate_period_pos] >>
  simp[iterate_period_thm, Abbr`q`] >>
  qabbrev_tac `q = iterate_period (g o f) x` >>
  rpt strip_tac >| [
    `(0 + p) MOD p = 0` by rw[] >>
    drule_then strip_assume_tac iterate_involute_mod_period >>
    last_x_assum (qspecl_then [`f`, `g`, `x`, `p`, `0`, `p`] strip_assume_tac) >>
    rfs[],
    `((p - m) + m) MOD p = 0` by rw[] >>
    `p - m < p` by decide_tac >>
    drule_then strip_assume_tac iterate_involute_mod_period >>
    last_x_assum (qspecl_then [`f`, `g`, `x`, `p`, `p - m`, `m`] strip_assume_tac) >>
    rfs[iterate_period_minimal, Abbr`p`]
  ]
QED

(* Idea: when f fixes x, then g fixes x iff (f o g) has period 1 for x. *)

(* Theorem: f involute s /\ g involute s /\ x IN fixes f s /\
            p = iterate_period (f o g) x ==> (p = 1 <=> x IN fixes g s) *)
(* Proof:
   If part: x IN s /\ f x = x ==> g x = x
      Note (f o g) x = x          by iterate_period_eq_1
        so   f (g x) = x          by o_THM
      Thus      g x = x           by BIJ_IS_INJ, f x = x
   Only-if part: x IN s /\ g x = x /\ f x = x ==> p = 1
      Note (f o g) x
          = f (g x)               by o_THM
          = f x                   by g x = x
          = x                     by f x = x
      Thus p = 1                  by iterate_period_eq_1
*)
Theorem involute_involute_fixes_both:
  !f g s p x. f involute s /\ g involute s /\
              x IN fixes f s /\ p = iterate_period (f o g) x ==>
              (p = 1 <=> x IN fixes g s)
Proof
  rw[fixes_def, iterate_period_eq_1, EQ_IMP_THM] >>
  metis_tac[BIJ_IS_INJ]
QED

(* Idea: when f fixes x, then (f o g)^i = f ((f o g)^j) iff (i+j) MOD p = 0. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\
            x IN fixes f s /\ p = iterate_period (f o g) x ==>
            (FUNPOW (f o g) i x = f (FUNPOW (f o g) j x) <=> (i + j) MOD p = 0) *)
(* Proof:
   Note x IN s /\ f x = x         by fixes_element
    and f o g PERMUTES s          by involute_involute_permutes
    and g o f PERMUTES s          by involute_involute_permutes
     so FUNPOW (g o f) i x IN s   by FUNPOW_closure
    and FUNPOW (f o g) j x IN s   by FUNPOW_closure
   also 0 < p                     by iterate_period_pos

       FUNPOW (f o g) i x = f (FUNPOW (f o g) j x)
   <=> FUNPOW (f o g) i (f x) = f (FUNPOW (f o g) j x)  by f x = x, above
   <=> f (FUNPOW (g o f) i x) = f (FUNPOW (f o g) j x)  by iterate_involute_compose_shift
   <=> FUNPOW (g o f) i x = FUNPOW (f o g) j x          by BIJ_DEF, INJ_EQ_11
   <=> (i + j) MOD p = 0                                by iterate_involute_mod_period, 0 < p
*)
Theorem involute_involute_fix_orbit_1:
  !f g s x p i j. FINITE s /\ f involute s /\ g involute s /\
                  x IN fixes f s /\ p = iterate_period (f o g) x ==>
                 (FUNPOW (f o g) i x = f (FUNPOW (f o g) j x) <=>
                  (i + j) MOD p = 0)
Proof
  rpt strip_tac >>
  qabbrev_tac `y = FUNPOW (f o g) j x` >>
  qabbrev_tac `z = FUNPOW (f o g) i x` >>
  `x IN s /\ f x = x` by fs[fixes_element] >>
  qabbrev_tac `t = FUNPOW (g o f) i x` >>
  `f o g PERMUTES s /\ g o f PERMUTES s` by rw[involute_involute_permutes] >>
  `0 < p` by metis_tac[iterate_period_pos] >>
  `y IN s /\ t IN s` by rw[FUNPOW_closure, Abbr`y`, Abbr`t`] >>
  assume_tac iterate_involute_compose_shift >>
  last_x_assum (qspecl_then [`f`, `g`, `s`, `x`, `i`] strip_assume_tac) >>
  `(z = f y) <=> (FUNPOW (f o g) i (f x) = f y)` by metis_tac[] >>
  `_ = (f t = f y)` by rfs[] >>
  `_ = (t = y)` by metis_tac[BIJ_DEF, INJ_EQ_11] >>
  drule_then strip_assume_tac iterate_involute_mod_period >>
  last_x_assum (qspecl_then [`f`, `g`, `x`, `p`, `j`, `i`] strip_assume_tac) >>
  metis_tac[ADD_COMM]
QED

(* Idea: when f fixes x, then (f o g)^i = g ((f o g)^j) iff (i+j+1) MOD p = 0. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\
            x IN fixes f s /\ p = iterate_period (f o g) x ==>
           (FUNPOW (f o g) i x = g (FUNPOW (f o g) j x) <=> (i + j + 1) MOD p = 0) *)
(* Proof:
   Note x IN s /\ f x = x         by fixes_element
    and f o g PERMUTES s          by involute_involute_permutes
   also 0 < p                     by iterate_period_pos

       FUNPOW (f o g) i x = g (FUNPOW (f o g) j x)
   <=> FUNPOW (f o g) i x = g (FUNPOW (f o g) j (f x))   by f x = x, above
   <=> FUNPOW (f o g) i x = g (f (FUNPOW (g o f) j x))   by iterate_involute_compose_shift
   <=> FUNPOW (f o g) i x = (g o f) (FUNPOW (g o f) j x) by o_THM
   <=> FUNPOW (f o g) i x = FUNPOW (g o f) (j + 1) x     by FUNPOW
   <=> (i + j + 1) MOD p = 0                             by iterate_involute_mod_period, 0 < p
*)
Theorem involute_involute_fix_orbit_2:
  !f g s x p i j. FINITE s /\ f involute s /\ g involute s /\
                  x IN fixes f s /\ p = iterate_period (f o g) x ==>
                 (FUNPOW (f o g) i x = g (FUNPOW (f o g) j x) <=>
                  (i + j + 1) MOD p = 0)
Proof
  rpt strip_tac >>
  qabbrev_tac `y = FUNPOW (f o g) j x` >>
  qabbrev_tac `z = FUNPOW (f o g) i x` >>
  `x IN s /\ f x = x` by fs[fixes_element] >>
  `f o g PERMUTES s` by rw[involute_involute_permutes] >>
  `0 < p` by metis_tac[iterate_period_pos] >>
  qabbrev_tac `t = FUNPOW (g o f) j x` >>
  assume_tac iterate_involute_compose_shift >>
  last_x_assum (qspecl_then [`f`, `g`, `s`, `x`, `j`] strip_assume_tac) >>
  `(z = g y) <=> (z = g (FUNPOW (f o g) j (f x)))` by fs[] >>
  `_ = (z = g (f t))` by rfs[] >>
  `_ = (z = (g o f) (FUNPOW (g o f) j x))` by rfs[] >>
  `_ = (z = FUNPOW (g o f) (j + 1) x)` by rfs[FUNPOW_SUC, GSYM ADD1] >>
  assume_tac iterate_involute_mod_period >>
  last_x_assum (qspecl_then [`f`, `g`, `s`, `x`, `p`, `i`, `j+1`] strip_assume_tac) >>
  rfs[]
QED

(* Idea: when f fixes x, and (f o g) has even period p for x,
         then f also fixes (f o g)^(p/2) x. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
            p = iterate_period (f o g) x /\ EVEN p ==>
           (FUNPOW (f o g) (p DIV 2) x) IN fixes f s *)
(* Proof:
   Let h = p DIV 2,
       y = FUNPOW (f o g) h x.
   Note p = h * 2 + p MOD 2        by DIVISION
          = 2 * h + 0              by EVEN_MOD2
          = h + h                  by arithmetic
   Note (f o g) PERMUTES s         by involute_involute_permutes
    and x IN s                     by fixes_element
     so 0 < p                      by iterate_period_pos
    and p MOD p = 0                by DIVMOD_ID, 0 < p

    Now y IN s                     by FUNPOW_closure
   Thus f y = y                    by involute_involute_fix_orbit_1, x IN fixes f s
    ==> y IN fixes f s             by fixes_element
*)
Theorem involute_involute_fix_orbit_fix_even:
  !f g s p x. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
              p = iterate_period (f o g) x /\ EVEN p ==>
              (FUNPOW (f o g) (p DIV 2) x) IN fixes f s
Proof
  rpt strip_tac >>
  qabbrev_tac `h = p DIV 2` >>
  qabbrev_tac `y = FUNPOW (f o g) h x` >>
  `p = h * 2 + p MOD 2` by rw[DIVISION, Abbr`h`] >>
  `_ = 2 * h + 0` by fs[EVEN_MOD2] >>
  `_ = h + h` by decide_tac >>
  `(f o g) PERMUTES s` by rw[involute_involute_permutes] >>
  `x IN s` by fs[fixes_element] >>
  `y IN s` by fs[FUNPOW_closure, Abbr`y`] >>
  `0 < p` by metis_tac[iterate_period_pos] >>
  `p MOD p = 0` by rw[] >>
  drule_then strip_assume_tac involute_involute_fix_orbit_1 >>
  last_x_assum (qspecl_then [`f`, `g`, `x`, `p`, `h`, `h`] strip_assume_tac) >>
  `f y = y` by metis_tac[] >>
  fs[fixes_element]
QED

(* When f fixes x, and (f o g) has odd period p for x,
   then g fixes (f o g)^(p/2) x. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
            p = iterate_period (f o g) x /\ ODD p ==>
           (FUNPOW (f o g) (p DIV 2) x) IN fixes g s *)
(* Proof:
   Let h = p DIV 2,
       y = FUNPOW (f o g) h x.
   Note p = h * 2 + p MOD 2        by DIVISION
          = 2 * h + 1              by ODD_MOD2
          = h + h + 1              by arithmetic
     so 0 < p                      by p = 2 * h + 1
    and p MOD p = 0                by DIVMOD_ID, 0 < p

   Note (f o g) PERMUTES s         by involute_involute_permutes
     so x IN s                     by fixes_element
    and y IN s                     by FUNPOW_closure
   Thus g y = y                    by involute_involute_fix_orbit_2, x IN fixes f s
    ==> y IN fixes g s             by fixes_element
*)
Theorem involute_involute_fix_orbit_fix_odd:
  !f g s p x. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
              p = iterate_period (f o g) x /\ ODD p ==>
              (FUNPOW (f o g) (p DIV 2) x) IN fixes g s
Proof
  rpt strip_tac >>
  qabbrev_tac `h = p DIV 2` >>
  qabbrev_tac `y = FUNPOW (f o g) h x` >>
  `p = h * 2 + p MOD 2` by rw[DIVISION, Abbr`h`] >>
  `_ = 2 * h + 1` by fs[ODD_MOD2] >>
  `_ = h + h + 1` by decide_tac >>
  `p MOD p = 0` by rw[] >>
  `(f o g) PERMUTES s` by rw[involute_involute_permutes] >>
  `x IN s` by fs[fixes_element] >>
  `y IN s` by fs[FUNPOW_closure, Abbr`y`] >>
  drule_then strip_assume_tac involute_involute_fix_orbit_2 >>
  last_x_assum (qspecl_then [`f`, `g`, `x`, `p`, `h`, `h`] strip_assume_tac) >>
  `g y = y` by rfs[Abbr`y`] >>
  fs[fixes_element]
QED

(* Idea: for inverse composition (g o f) with period p from f fixed point, another f fixed point occurs at HALF p for EVEN p. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
            p = iterate_period (g o f) x /\ EVEN p ==> FUNPOW (g o f) (HALF p) x IN fixes f s *)
(* Proof:
   Note x IN s /\ f x = x                      by fixes_element
     so p = iterate_period (f o g) x           by involute_involute_period_inv
   Let y = FUNPOW (f o g) (HALF p) x.
   Then y IN fixes f s                         by involute_involute_fix_orbit_fix_even, [1]
   Let n = HALF p.
   Note (g o f) PERMUTES s                     by involute_involute_permutes
     so FUNPOW (g o f) n x IN s                by FUNPOW_closure, [2]

     y
   = f y                                       by fixes_element
   = f (FUNPOW (f o g) n x)                    by notation
   = f (FUNPOW (f o g) n (f x))                by f x = x
   = f (f (FUNPOW (g o f) n x))                by iterate_involute_compose_shift
   = (f o f) (FUNPOW (g o f) n x)              by composition
   = FUNPOW (g o f) n x                        by f involute s, [2]

   Thus FUNPOW (g o f) n x IN fixes f s        by [1]
*)
Theorem involute_involute_fix_orbit_fix_even_inv:
  !f g s p x. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
              p = iterate_period (g o f) x /\ EVEN p ==> FUNPOW (g o f) (HALF p) x IN fixes f s
Proof
  rpt strip_tac >>
  `x IN s /\ f x = x` by fs[fixes_element] >>
  qabbrev_tac `n = HALF p` >>
  qabbrev_tac `y = FUNPOW (f o g) n x` >>
  assume_tac (involute_involute_period_inv |> SPEC_ALL) >>
  rfs[] >>
  `y IN fixes f s` by simp[involute_involute_fix_orbit_fix_even, Abbr`y`, Abbr`n`] >>
  assume_tac (iterate_involute_compose_shift |> SPEC_ALL) >>
  rfs[] >>
  `FUNPOW (g o f) n x IN s` by fs[involute_involute_permutes, FUNPOW_closure] >>
  `y = f y` by fs[fixes_element] >>
  `_ = f (FUNPOW (f o g) n x)` by simp[Abbr`y`] >>
  `_ = f (f (FUNPOW (g o f) n x))` by metis_tac[] >>
  `_ = FUNPOW (g o f) n x` by fs[] >>
  fs[]
QED

(* Idea: for inverse composition (g o f) with period p from f fixed point, the g fixed point occurs at 1 + HALF p for ODD p. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
               p = iterate_period (g o f) x /\ ODD p ==> FUNPOW (g o f) (1 + HALF p) x IN fixes g s *)
(* Proof:
   Note x IN s /\ f x = x                      by fixes_element
     so p = iterate_period (f o g) x           by involute_involute_period_inv
   Let y = FUNPOW (f o g) (HALF p) x.
   Then y IN fixes g s                         by involute_involute_fix_orbit_fix_odd, [1]
   Let n = HALF p.
     y
   = g y                                       by fixes_element
   = g (FUNPOW (f o g) n x)                    by notation
   = g (FUNPOW (f o g) n (f x))                by f x = x
   = g (f (FUNPOW (g o f) n x))                by iterate_involute_compose_shift
   = (g o f) (FUNPOW (g o f) n x)              by composition
   = FUNPOW (g o f) (SUC n) x                  by FUNPOW_SUC
   = FUNPOW (g o f) (1 + n) x                  by SUC_ONE_ADD

   Thus FUNPOW (g o f) (1 + n) x IN fixes f s  by [1]
*)
Theorem involute_involute_fix_orbit_fix_odd_inv:
  !f g s p x. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
               p = iterate_period (g o f) x /\ ODD p ==> FUNPOW (g o f) (1 + HALF p) x IN fixes g s
Proof
  rpt strip_tac >>
  `x IN s /\ f x = x` by fs[fixes_element] >>
  qabbrev_tac `n = HALF p` >>
  qabbrev_tac `y = FUNPOW (f o g) n x` >>
  assume_tac (involute_involute_period_inv |> SPEC_ALL) >>
  `p = iterate_period (f o g) x` by fs[] >>
  `y IN fixes g s` by simp[involute_involute_fix_orbit_fix_odd, Abbr`y`, Abbr`n`] >>
  assume_tac (iterate_involute_compose_shift |> SPEC_ALL) >>
  `y = g y` by fs[fixes_element] >>
  `_ = g (FUNPOW (f o g) n x)` by simp[Abbr`y`] >>
  `_ = FUNPOW (g o f) (SUC n) x` by rfs[FUNPOW_SUC] >>
  metis_tac[SUC_ONE_ADD]
QED

(* Idea: when f fixes x, and (f o g) has even period p for x,
         then f also fixes (f o g)^(p/2) x, which is not x itself. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
            p = iterate_period (f o g) x /\
            (y = FUNPOW (f o g) (p DIV 2) x) /\
             EVEN p ==> (y IN fixes f s /\ y <> x) *)
(* Proof:
   Note y IN fixes f s          by involute_involute_fix_orbit_fix_even
   Remains to show: y <> x.
   By contradiction, suppose y = x.
   Note x IN s                  by fixes_element
    and f o g PERMUTES s        by involute_involute_permutes
     so 0 < p                   by iterate_period_pos
    ==> p DIV 2 < p             by DIV_LESS, 0 < p
   Thus ~(0 < HALF p)           by iterate_period_minimal, y = x.
     or HALF p = 0              by ~(0 < HALF p)
     so p = 1                   by HALF_EQ_0
   This contradicts EVEN p      by ODD_1, ODD_EVEN
*)
Theorem involute_involute_fix_orbit_fix_even_distinct:
  !f g s p x y. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                p = iterate_period (f o g) x /\
                (y = FUNPOW (f o g) (p DIV 2) x) /\
                EVEN p ==> (y IN fixes f s /\ y <> x)
Proof
  ntac 7 strip_tac >>
  drule_then strip_assume_tac involute_involute_fix_orbit_fix_even >>
  last_x_assum (qspecl_then [`f`, `g`, `p`, `x`] strip_assume_tac) >>
  `y IN fixes f s` by fs[] >>
  (rpt strip_tac >> simp[]) >>
  `x IN s` by fs[fixes_element] >>
  `f o g PERMUTES s` by rw[involute_involute_permutes] >>
  `0 < p` by metis_tac[iterate_period_pos] >>
  `p DIV 2 < p` by rw[DIV_LESS] >>
  `~(0 < HALF p)` by metis_tac[iterate_period_minimal] >>
  `HALF p = 0` by decide_tac >>
  `p = 1` by fs[HALF_EQ_0] >>
  metis_tac[ODD_1, ODD_EVEN]
QED

(* Another version of involute_involute_fix_orbit_fix_even_distinct *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
            p = iterate_period (f o g) x /\
            (y = FUNPOW (f o g) (p DIV 2) x) /\
            EVEN p ==> y IN fixes f s /\ (y = x <=> p = 0) *)
(* Proof:
   When p = 0,
        y = FUNPOW (f o g) 0 x = x   by FUNPOW_0
   When p <> 0,
        This is true                 by involute_involute_fix_orbit_fix_even_distinct
*)
Theorem involute_involute_fix_orbit_fix_even_distinct_iff:
  !f g s p x y. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                p = iterate_period (f o g) x /\
                (y = FUNPOW (f o g) (p DIV 2) x) /\
                 EVEN p ==> y IN fixes f s /\ (y = x <=> p = 0)
Proof
  ntac 7 strip_tac >>
  (Cases_on `p = 0` >> simp[]) >>
  irule involute_involute_fix_orbit_fix_even_distinct >>
  metis_tac[]
QED

(* Idea: when f fixes x, and (f o g) has odd period p for x,
         then g fixes (f o g)^(p/2) x, which, if p <> 1, is not x itself. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
            p = iterate_period (f o g) x /\
            (y = FUNPOW (f o g) (p DIV 2) x) /\
             ODD p ==> y IN fixes g s /\ (1 < p ==> y <> x) *)
(* Proof:
   Note y IN fixes g s           by involute_involute_fix_orbit_fix_odd
   Remains to show: y <> x.
   By contradiction, suppose y = x.
   Then p = 1                    by involute_involute_fix_point
   This contradicts 1 < p        by given
*)
Theorem involute_involute_fix_orbit_fix_odd_distinct:
  !f g s p x y. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                p = iterate_period (f o g) x /\
                (y = FUNPOW (f o g) (p DIV 2) x) /\
                 ODD p ==> y IN fixes g s /\ (1 < p ==> y <> x)
Proof
  ntac 7 strip_tac >>
  drule_then strip_assume_tac involute_involute_fix_orbit_fix_odd >>
  last_x_assum (qspecl_then [`f`, `g`, `p`, `x`] strip_assume_tac) >>
  `y IN fixes g s` by fs[] >>
  (rpt strip_tac >> simp[]) >>
  assume_tac involute_involute_fixes_both >>
  last_x_assum (qspecl_then [`f`, `g`, `s`, `p`, `x`] strip_assume_tac) >>
  `p = 1` by fs[] >>
  decide_tac
QED

(* Another version of involute_involute_fix_orbit_fix_odd_distinct *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
            p = iterate_period (f o g) x /\
            (y = FUNPOW (f o g) (p DIV 2) x) /\
             ODD p ==> y IN fixes g s /\ (y = x <=> p = 1) *)
(* Proof:
   Note y IN fixes g s               by involute_involute_fix_orbit_fix_odd
   When p = 1,
        y = FUNPOW (f o g) 0 x = x   by FUNPOW_0
   When p <> 1, 1 < p,
        Hence true                   by involute_involute_fix_orbit_fix_odd_distinct
*)
Theorem involute_involute_fix_orbit_fix_odd_distinct_iff:
  !f g s p x y. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
                p = iterate_period (f o g) x /\
                (y = FUNPOW (f o g) (p DIV 2) x) /\
                 ODD p ==> y IN fixes g s /\ (y = x <=> p = 1)
Proof
  ntac 7 strip_tac >>
  assume_tac involute_involute_fix_orbit_fix_odd_distinct >>
  last_x_assum (qspecl_then [`f`, `g`, `s`, `p`, `x`, `y`] strip_assume_tac) >>
  (Cases_on `p = 1` >> simp[]) >>
  `x IN s` by fs[fixes_element] >>
  `(f o g) PERMUTES s` by rw[involute_involute_permutes] >>
  `0 < p` by metis_tac[iterate_period_pos] >>
  rfs[]
QED

(* Idea: if f fixes just a single x, then period of (f o g) for x must be odd. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ fixes f s = {x} /\
            p = iterate_period (f o g) x ==> ODD p *)
(* Proof:
   Let y = FUNPOW (f o g) (p DIV 2) x,
   and a = fixes f s.
   By contradiction, suppose ~ODD p.
   Then EVEN p               by ODD_EVEN
   Note x IN a               by IN_SING
   Thus y IN a /\ y <> x     by involute_involute_fix_orbit_fix_even_distinct
    But y = x                by IN_SING
   Hence this is a contradiction.
*)
Theorem involute_involute_fix_sing_period_odd:
  !f g s p x. FINITE s /\ f involute s /\ g involute s /\
              fixes f s = {x} /\ p = iterate_period (f o g) x ==> ODD p
Proof
  spose_not_then strip_assume_tac >>
  qabbrev_tac `p = iterate_period (f o g) x` >>
  qabbrev_tac `y = FUNPOW (f o g) (p DIV 2) x` >>
  drule_then strip_assume_tac involute_involute_fix_orbit_fix_even_distinct >>
  last_x_assum (qspecl_then [`f`, `g`, `p`, `x`, `y`] strip_assume_tac) >>
  qabbrev_tac `a = fixes f s` >>
  `x IN a` by fs[] >>
  `y IN a /\ y <> x` by rfs[ODD_EVEN] >>
  metis_tac[IN_SING]
QED

(* Idea: for j <= p, apply f to the j-th iterate equals to the (p-j)-th iterate. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
            p = iterate_period (f o g) x ==>
            !j. j <= p ==> f (FUNPOW (f o g) j x) = FUNPOW (f o g) (p - j) x *)
(* Proof:
   Note (f o g) PERMUTES s        by involute_involute_permutes
    and x IN s                    by fixes_element
     so 0 < p                     by iterate_period_pos
   Let i = p - j.
   then i + j = p,
     or (i + j) MOD p = 0         by DIVMOD_ID, 0 < p
     so f (FUNPOW (f o g) j x)
      = FUNPOW (f o g) i x        by involute_involute_fix_orbit_1
*)
Theorem involute_involute_fix_iterates_1:
  !f g s p x. FINITE s /\ f involute s /\ g involute s /\
              x IN fixes f s /\ p = iterate_period (f o g) x ==>
              !j. j <= p ==> f (FUNPOW (f o g) j x) = FUNPOW (f o g) (p - j) x
Proof
  rpt strip_tac >>
  `p = p - j + j` by decide_tac >>
  qabbrev_tac `i = p - j` >>
  `f o g PERMUTES s` by rw[involute_involute_permutes] >>
  `0 < p` by metis_tac[fixes_element, iterate_period_pos] >>
  `(i + j) MOD p = 0` by rw[] >>
  drule_then strip_assume_tac involute_involute_fix_orbit_1 >>
  last_x_assum (qspecl_then [`f`, `g`, `x`, `p`, `i`, `j`] strip_assume_tac) >>
  rfs[]
QED

(* Idea: for j < p, apply g to the j-th iterate equals to the (p-1-j)-th iterate. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
            p = iterate_period (f o g) x ==>
            !j. j < p ==> g (FUNPOW (f o g) j x) = FUNPOW (f o g) (p - 1 - j) x *)
(* Proof:
   Note (f o g) PERMUTES s        by involute_involute_permutes
    and x IN s                    by fixes_element
     so 0 < p                     by iterate_period_pos
   Let i = p - (j + 1).
   then i + j + 1 = p,
     or (i + j + 1) MOD p = 0     by DIVMOD_ID, 0 < p
     so g (FUNPOW (f o g) j x)
      = FUNPOW (f o g) i x        by involute_involute_fix_orbit_2
*)
Theorem involute_involute_fix_iterates_2:
  !f g s p x. FINITE s /\ f involute s /\ g involute s /\
              x IN fixes f s /\ p = iterate_period (f o g) x ==>
              !j. j < p ==> g (FUNPOW (f o g) j x) = FUNPOW (f o g) (p - 1 - j) x
Proof
  rpt strip_tac >>
  `p = p - (j + 1) + j + 1` by decide_tac >>
  qabbrev_tac `i = p - (j + 1)` >>
  `f o g PERMUTES s` by rw[involute_involute_permutes] >>
  `0 < p` by metis_tac[fixes_element, iterate_period_pos] >>
  `(i + j + 1) MOD p = 0` by rw[] >>
  drule_then strip_assume_tac involute_involute_fix_orbit_2 >>
  last_x_assum (qspecl_then [`f`, `g`, `x`, `p`, `i`, `j`] strip_assume_tac) >>
  rfs[]
QED

(* Idea: for even period, the only f fixed point is at the midpoint. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
            p = iterate_period (f o g) x /\ EVEN p ==>
            !j. 0 < j /\ j < p ==> (FUNPOW (f o g) j x IN fixes f s <=> j = p DIV 2) *)
(* Proof:
   Note (f o g) PERMUTES s        by involute_involute_permutes
    and x IN s                    by fixes_element
     so 0 < p                     by iterate_period_pos, or just by 0 < j < p
   Let y = FUNPOW (f o g) j x.
   then y IN s                    by FUNPOW_closure, x IN s
   Note j < p, so 0 < p - j < p.
       y IN fixes f s
   <=> f y = y                    by fixes_element
   <=> FUNPOW (f o g) (p - j) x = FUNPOW (f o g) j x
                                  by involute_involute_fix_iterates_1, j < p
   <=> p - j MOD p = j MOD p      by iterate_period_mod_eq
   <=> p - j = j                  by LESS_MOD, p - j < p, j < p
   <=> 2 * j = p                  by arithmetic
   <=> 2 * j = 2 * p DIV 2        by EVEN_HALF, EVEN p
   <=> j = p DIV 2                by EQ_MULT_LCANCEL
*)
Theorem involute_involute_fix_even_period_fix:
  !f g s p x. FINITE s /\ f involute s /\ g involute s /\
              x IN fixes f s /\ p = iterate_period (f o g) x /\ EVEN p ==>
              !j. 0 < j /\ j < p ==>
                  (FUNPOW (f o g) j x IN fixes f s <=> j = p DIV 2)
Proof
  rpt strip_tac >>
  `f o g PERMUTES s` by rw[involute_involute_permutes] >>
  qabbrev_tac `y = FUNPOW (f o g) j x` >>
  `x IN s` by fs[fixes_element] >>
  `y IN s` by fs[FUNPOW_closure, Abbr`y`] >>
  drule_then strip_assume_tac involute_involute_fix_iterates_1 >>
  last_x_assum (qspecl_then [`f`, `g`, `p`, `x`, `j`] strip_assume_tac) >>
  drule_then strip_assume_tac (iterate_period_mod_eq |> ISPEC ``(f:'a -> 'a) o (g:'a -> 'a)``) >>
  last_x_assum (qspecl_then [`g`, `f`, `p`, `x`, `p-j`, `j`] strip_assume_tac) >>
  rfs[] >>
  `p - j < p` by decide_tac >>
  `y IN fixes f s <=> f y = y` by metis_tac[fixes_element] >>
  `_ = ((p - j) MOD p = j MOD p)` by rfs[] >>
  `_ = (p - j = j)` by rw[LESS_MOD] >>
  `_ = (p = 2 * j)` by decide_tac >>
  metis_tac[EVEN_HALF, EQ_MULT_LCANCEL, DECIDE``2 <> 0``]
QED

(* Idea: for odd period, the only g fixed point is at the midpoint. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
            p = iterate_period (f o g) x /\ ODD p ==>
            !j. 0 < j /\ j < p ==> (FUNPOW (f o g) j x IN fixes g s <=> j = p DIV 2) *)
(* Proof:
   Note (f o g) PERMUTES s        by involute_involute_permutes
    and x IN s                    by fixes_element
     so 0 < p                     by iterate_period_pos, or just by 0 < j < p
   Let y = FUNPOW (f o g) j x.
   then y IN s                    by FUNPOW_closure, x IN s
   Note j < p, so 0 < p - 1 - j < p.
       y IN fixes g s
   <=> g y = y                    by fixes_element
   <=> FUNPOW (f o g) (p - 1 - j) x = FUNPOW (f o g) j x
                                  by involute_involute_fix_iterates_2, j < p
   <=> p - 1 - j MOD p = j MOD p  by iterate_period_mod_eq
   <=> p - 1 - j = j              by LESS_MOD, p - 1 - j < p, j < p
   <=> 2 * j + 1 = p                  by arithmetic
   <=> 2 * j + 1 = 2 * p DIV 2 + 1    by ODD_HALF
   <=> j = p DIV 2                    by EQ_MULT_LCANCEL
*)
Theorem involute_involute_fix_odd_period_fix:
  !f g s p x. FINITE s /\ f involute s /\ g involute s /\
              x IN fixes f s /\ p = iterate_period (f o g) x /\ ODD p ==>
              !j. j < p ==> (FUNPOW (f o g) j x IN fixes g s <=> j = p DIV 2)
Proof
  rpt strip_tac >>
  `f o g PERMUTES s` by rw[involute_involute_permutes] >>
  qabbrev_tac `y = FUNPOW (f o g) j x` >>
  `x IN s` by fs[fixes_element] >>
  `y IN s` by fs[FUNPOW_closure, Abbr`y`] >>
  drule_then strip_assume_tac involute_involute_fix_iterates_2 >>
  last_x_assum (qspecl_then [`f`, `g`, `p`, `x`, `j`] strip_assume_tac) >>
  drule_then strip_assume_tac (iterate_period_mod_eq |> ISPEC ``(f:'a -> 'a) o (g:'a -> 'a)``) >>
  last_x_assum (qspecl_then [`g`, `f`, `p`, `x`, `p - 1 -j`, `j`] strip_assume_tac) >>
  rfs[] >>
  `p - 1 - j < p` by decide_tac >>
  `y IN fixes g s <=> g y = y` by metis_tac[fixes_element] >>
  `_ = ((p - 1 - j) MOD p = j MOD p)` by rfs[] >>
  `_ = (p - 1 - j = j)` by rw[LESS_MOD] >>
  `_ = (p = 2 * j + 1)` by decide_tac >>
  metis_tac[ODD_HALF, EQ_MONO_ADD_EQ, EQ_MULT_LCANCEL, DECIDE``2 <> 0``]
QED

(* ------------------------------------------------------------------------- *)
(* Iteration Mate Involution.                                                *)
(* ------------------------------------------------------------------------- *)

(* Idea: an involution for the mapping of fixed points. *)

(* For EVEN period, say 6, orbit:  [x, f x, f^2 x, f^3 x, f^4 x, f^5 x]
   The middle one is slightly right: f^3 x, HALF 6 = 3, which is f^(p-3) x.
   For ODD period, say 7, orbit: [x, f x, f^2 x, f^3 x, f^4 x, f^5 x, f^6 x]
   The middle one is exactly at center: f^3 x, HALF 7 = 3, which is f^(p-1-3) x.

   This means, for p = iterate_period (f o g) x,
   if start from (fixes f s),
      then even period ==> iterate_mate (f o g) x IN fixes f s,
       and odd period ==> iterate_mate (f o g) x IN fixes g s.
   if start from (fixes g s),
      then even period ==> iterate_mate (g o f) x IN fixes g s,
           and iterate_mate (g o f) x = iterate_mate (f o g) x   when even
       and odd period ==> iterate_mate (g o f) x IN fixes f s.
           but iterate_mate (g o f) x <> iterate_mate (f o g) x
           because iterate_mate (g o f) x = FUNPOW (f o g) (1 + HALF p) x
   All these mean:
   if even period, iterate_mate (f o g) (iterate_mate (f o g) x) = x, by 3 + 3 = 6.
   if odd period, to have the same equality, iterate_mate is tricky to define!
*)

(* Define the iterate mate, pairing up with middle iterate, for composite. *)
Definition iterate_mate_def:
    iterate_mate f g x =
      let h = (iterate_period (f o g) x) DIV 2 (* half period *)
       in if f x = x then FUNPOW (f o g) h x (* walk by (f o g) *)
          else if g x = x then FUNPOW (g o f) h x (* walk by (g o f) *)
          else x (* don't care, better just be yourself. *)
End

(* Idea: the mate is an element of the set. *)

(* Theorem: f involute s /\ g involute s /\ x IN s ==> iterate_mate f g x IN s *)
(* Proof:
   Note f o g PERMUTES s          by involute_involute_permutes
    and g o f PERMUTES s          by involute_involute_permutes
   Thus iterate_mate f g x IN s   by iterate_mate_def, FUNPOW_closure
*)
Theorem iterate_mate_element:
  !f g s x. f involute s /\ g involute s /\ x IN s ==>
            iterate_mate f g x IN s
Proof
  rpt strip_tac >>
  `f o g PERMUTES s /\ g o f PERMUTES s` by rw[involute_involute_permutes] >>
  rw[iterate_mate_def, FUNPOW_closure]
QED

(* Idea: the reverse of a mate is the mate itself. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN s ==>
            iterate_mate g f x = iterate_mate f g x *)
(* Proof:
   Let p = iterate_period (f o g) x,
       q = iterate_period (g o f) x.
   Then p = q                         by involute_involute_period_inv

   If f x = x /\ g x = x,
      Then x IN fixes f s             by fixes_element
       and x IN fixes g s             by fixes_element
        so p = 1                      by involute_involute_fixes_both
        iterate_mate g f x
      = FUNPOW (f o g) (HALF q) x     by iterate_mate_def
      = FUNPOW (f o g) 0 x            by q = 1
      = FUNPOW (g o f) 0 x            by FUNPOW_0
      = FUNPOW (g o f) (HALF p) x     by p = 1
      = iterate_mate f g x            by iterate_mate_def
   If f x = x, g x <> x
        iterate_mate g f x
      = FUNPOW (f o g) (HALF q) x     by iterate_mate_def
      = FUNPOW (f o g) (HALF p) x     by q = p
      = iterate_mate f g x            by iterate_mate_def
   If g x = x, f x <> x
        iterate_mate g f x
      = FUNPOW (g o f) (HALF q) x     by iterate_mate_def
      = FUNPOW (g o f) (HALF p) x     by q = p
      = iterate_mate f g x            by iterate_mate_def
*)
Theorem iterate_mate_reverse:
  !f g s x. FINITE s /\ f involute s /\ g involute s /\ x IN s ==>
            iterate_mate g f x = iterate_mate f g x
Proof
  simp[iterate_mate_def] >>
  rpt strip_tac >>
  qabbrev_tac `p = iterate_period (f o g) x` >>
  qabbrev_tac `q = iterate_period (g o f) x` >>
  drule_then strip_assume_tac involute_involute_period_inv >>
  last_x_assum (qspecl_then [`f`, `g`, `x`] strip_assume_tac) >>
  `p = q` by rfs[] >>
  rw[] >>
  qabbrev_tac `h = HALF p` >>
  `x IN fixes f s /\ x IN fixes g s` by fs[fixes_element] >>
  drule_then strip_assume_tac involute_involute_fixes_both >>
  last_x_assum (qspecl_then [`f`, `p`, `x`] strip_assume_tac) >>
  `p = 1` by rw[] >>
  simp[Abbr`h`]
QED

(* Idea: the mate of a mate is itself. *)

(* First, when x IN fixes f s, then prove this situation. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s ==>
            iterate_mate f g (iterate_mate f g x) = x *)
(* Proof:
   Let p = iterate_period (f o g) x, h = HALF p.
   Given x IN fixes f s,
    so x IN s /\ f x = x               by fixes_element
   Let y = FUNPOW (f o g) h x.
   Note (f o g) PERMUTES s             by involute_involute_permutes
     so p = iterate_period (f o g) y   by iterate_period_iterate

   If EVEN p,
      Then y IN fixes f s            by involute_involute_fix_orbit_fix_even
      so y IN s /\ f y = y           by fixes_element
        iterate_mate f g (iterate_mate f g x)
      = iterate_mate f g y           by iterate_mate_def, f x = x
      = FUNPOW (f o g) h y           by iterate_mate_def, f y = y
      = FUNPOW (f o g) h (FUNPOW (f o g) h x)
      = FUNPOW (f o g) (h + h) x     by FUNPOW_ADD
      = FUNPOW (f o g) p x           by EVEN_HALF
      = x                            by iterate_period_property

   If ~EVEN p, then ODD p            by ODD_EVEN
      Then y IN fixes g s            by involute_involute_fix_orbit_fix_odd
      so y IN s /\ g y = y           by fixes_element
      Note p = iterate_period (g o f) y   by involute_involute_period_inv
      If f y = y,
         Then y IN fixes f s         by fixes_element
           so p = 1                  by involute_involute_fixes_both
           iterate_mate f g (iterate_mate f g x)
         = iterate_mate f g y        by iterate_mate_def, f x = x
         = FUNPOW (f o g) h y        by iterate_mate_def, f y = y
         = FUNPOW (f o g) 0 y        by h = HALF 1 = 0
         = y                         by FUNPOW_0
         = FUNPOW (f o g) 0 x        by y = FUNPOW (f o g) h x
         = x
      If f y <> y,
         Note h + h + 1 = p          by ODD_HALF
           so (h + h + 1) MOD p = 0  by DIVMOD_ID, 0 < p
           iterate_mate f g (iterate_mate f g x)
         = iterate_mate f g y        by iterate_mate_def, f x = x
         = FUNPOW (g o f) h y        by iterate_mate_def, f y <> y
         = FUNPOW (f o g) (h + 1) y  by iterate_involute_mod_period
         = FUNPOW (f o g) (h + 1) (FUNPOW (f o g) h x)
         = FUNPOW (f o g) (h + 1 + h) x    by FUNPOW_ADD
         = FUNPOW (f o g) p x        by above
         = x                         by iterate_period_property
*)
Theorem iterate_mate_fixes_mate:
  !f g s x. FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s ==>
            iterate_mate f g (iterate_mate f g x) = x
Proof
  simp[iterate_mate_def] >>
  rpt strip_tac >>
  qabbrev_tac `p = iterate_period (f o g) x` >>
  `x IN s /\ f x = x` by fs[fixes_element] >>
  simp[] >>
  qabbrev_tac `y = FUNPOW (f o g) (HALF p) x` >>
  `(f o g) PERMUTES s` by rw[involute_involute_permutes] >>
  `iterate_period (f o g) y = p` by metis_tac[iterate_period_iterate] >>
  Cases_on `EVEN p` >| [
    `y IN fixes f s` by fs[involute_involute_fix_orbit_fix_even, Abbr`p`, Abbr`y`] >>
    `y IN s /\ f y = y` by fs[fixes_element] >>
    simp[] >>
    qabbrev_tac `h = p DIV 2` >>
    `h + h = p` by rw[EVEN_HALF, Abbr`h`] >>
    `FUNPOW (f o g) h y = FUNPOW (f o g) (h + h) x` by rw[FUNPOW_ADD, Abbr`y`] >>
    `_ = x` by rw[iterate_period_property, Abbr`p`] >>
    simp[],
    `ODD p` by rw[ODD_EVEN] >>
    `y IN fixes g s` by fs[involute_involute_fix_orbit_fix_odd, Abbr`p`, Abbr`y`] >>
    `y IN s /\ g y = y` by fs[fixes_element] >>
    simp[] >>
    drule_then strip_assume_tac involute_involute_period_inv >>
    last_x_assum (qspecl_then [`f`, `g`, `y`] strip_assume_tac) >>
    `p = iterate_period (g o f) y` by rw[Abbr`p`] >>
    (Cases_on `f y = y` >> rfs[]) >| [
      `y IN fixes f s` by rw[fixes_element] >>
      drule_then strip_assume_tac involute_involute_fixes_both >>
      last_x_assum (qspecl_then [`f`, `p`, `y`] strip_assume_tac) >>
      `p = 1` by rw[] >>
      simp[Abbr`y`],
      qabbrev_tac `h = p DIV 2` >>
      `h + h + 1 = p` by rw[ODD_HALF, Abbr`h`] >>
      `(h + h + 1) MOD p = 0` by fs[DIVMOD_ID] >>
      drule_then strip_assume_tac iterate_involute_mod_period >>
      last_x_assum (qspecl_then [`g`, `f`, `y`, `p`, `h`, `h+1`] strip_assume_tac) >>
      `FUNPOW (g o f) h y = FUNPOW (f o g) (h + 1) y` by rfs[] >>
      `_ = FUNPOW (f o g) (h + 1 + h) x` by fs[FUNPOW_ADD, Abbr`y`] >>
      `_ = x` by rfs[iterate_period_property, Abbr`p`] >>
      simp[]
    ]
  ]
QED

(* Idea: the mate of a mate is itself. *)

(* Now, remove x IN fixes f s condition. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN s ==>
            iterate_mate f g (iterate_mate f g x) = x *)
(* Proof:
   If x IN fixes f s,
      Then iterate_mate f g (iterate_mate f g x) = x
                                                  by iterate_mate_fixes_mate
   else if x IN fixes g s,
      Note iterate_mate g f x IN s                by iterate_mate_element
           iterate_mate f g (iterate_mate f g x)
         = iterate_mate f g (iterate_mate g f x)  by iterate_mate_reverse
         = iterate_mate g f (iterate_mate g f x)  by iterate_mate_reverse
         = x                                      by iterate_mate_fixes_mate
   Otherwise, f x <> x and g x <> x               by fixes_element
           iterate_mate f g (iterate_mate f g x)
         = iterate_mate f g x                     by iterate_mate_def
         = x                                      by iterate_mate_def
*)
Theorem iterate_mate_mate:
  !f g s x. FINITE s /\ f involute s /\ g involute s /\ x IN s ==>
            iterate_mate f g (iterate_mate f g x) = x
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac iterate_mate_fixes_mate >>
  Cases_on `x IN fixes f s` >| [
    last_x_assum (qspecl_then [`f`, `g`, `x`] strip_assume_tac) >>
    fs[],
    Cases_on `x IN fixes g s` >| [
      last_x_assum (qspecl_then [`g`, `f`, `x`] strip_assume_tac) >>
      qabbrev_tac `y = iterate_mate g f x` >>
      `y IN s` by rw[iterate_mate_element, Abbr`y`] >>
      drule_then strip_assume_tac iterate_mate_reverse >>
      last_x_assum (qspecl_then [`f`, `g`] strip_assume_tac) >>
      `iterate_mate f g (iterate_mate f g x) = iterate_mate f g y` by rfs[Abbr`y`] >>
      first_x_assum (qspecl_then [`y`] strip_assume_tac) >>
      rfs[],
      `f x <> x /\ g x <> x` by rfs[fixes_element] >>
      simp[iterate_mate_def]
    ]
  ]
QED

(* Idea: if x is a fixed point, its mate is also a fixed point. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\
            x IN (fixes f s UNION fixes g s) ==>
            iterate_mate f g x IN (fixes f s UNION fixes g s) *)
(* Proof:
   Let p = iterate_period (f o g) x, h = HALF p.
   If x IN fixes f s,
      Then x IN s /\ f x = x           by fixes_element
      Let y = FUNPOW (f o g) h x.
        so iterate_mate f g x = y      by iterate_mate_def
      If EVEN p,
         then y IN fixes f s           by involute_involute_fix_orbit_fix_even
      If ~EVEN p, then ODD p           by ODD_EVEN
          and y IN fixes g s           by involute_involute_fix_orbit_fix_odd

   If x IN fixes g s,
      Then x IN s /\ g x = x           by fixes_element
       and p = iterate_period (g o f) x   by involute_involute_period_inv

      If f x = x,
         Let y = FUNPOW (f o g) h x.
           so iterate_mate f g x = y   by iterate_mate_def
          But x IN fixes f s           by fixes_element
           so p = 1                    by involute_involute_fixes_both
          ==> h = 0                    by h = HALF p
         Thus y = x                    by FUNPOW_0
          and x IN fixes g s           by given case

      If f x <> x,
         Let y = FUNPOW (g o h) h x.
           so iterate_mate f g x = y   by iterate_mate_def
         If EVEN p,
            then y IN fixes g s        by involute_involute_fix_orbit_fix_even
         If ~EVEN p, then ODD p        by ODD_EVEN
             and y IN fixes f s        by involute_involute_fix_orbit_fix_odd
*)
Theorem iterate_mate_fixes_mate_fixes:
  !f g s x. FINITE s /\ f involute s /\ g involute s /\
            x IN (fixes f s UNION fixes g s) ==>
            iterate_mate f g x IN (fixes f s UNION fixes g s)
Proof
  simp[iterate_mate_def] >>
  ntac 4 strip_tac >>
  qabbrev_tac `p = iterate_period (f o g) x` >>
  strip_tac >| [
    `x IN s /\ f x = x` by fs[fixes_element] >>
    simp[] >>
    Cases_on `EVEN p` >-
    fs[involute_involute_fix_orbit_fix_even, Abbr`p`] >>
    fs[involute_involute_fix_orbit_fix_odd, ODD_EVEN, Abbr`p`],
    `x IN s /\ (g x = x)` by fs[fixes_element] >>
    simp[] >>
    drule_then strip_assume_tac involute_involute_period_inv >>
    last_x_assum (qspecl_then [`f`, `g`, `x`] strip_assume_tac) >>
    `p = iterate_period (g o f) x` by rw[Abbr`p`] >>
    (Cases_on `f x = x` >> rfs[]) >| [
      `x IN fixes f s` by rw[fixes_element] >>
      drule_then strip_assume_tac involute_involute_fixes_both >>
      last_x_assum (qspecl_then [`f`, `p`, `x`] strip_assume_tac) >>
      `p = 1` by rw[] >>
      simp[],
      Cases_on `EVEN p` >-
      fs[involute_involute_fix_orbit_fix_even, Abbr`p`] >>
      fs[involute_involute_fix_orbit_fix_odd, ODD_EVEN, Abbr`p`]
    ]
  ]
QED

(* Idea: mate is an involution on all the fixes. *)

(* Theorem: FINITE s /\ f involute s /\ g involute s ==>
            (iterate_mate f g) involute ((fixes f s) UNION (fixes g s)) *)
(* Proof:
   This is to show:
   (1) x IN fixes f s UNION fixes g s ==>
      iterate_mate f g x IN fixes f s UNION fixes g s
      This is true                    by iterate_mate_fixes_mate_fixes
   (2) x IN fixes f s UNION fixes g s ==>
       iterate_mate f g (iterate_mate f g x) = x
       Note x IN s                    by fixes_element
       Hence true                     by iterate_mate_mate
*)
Theorem iterate_mate_involute_fixes:
  !f g s. FINITE s /\ f involute s /\ g involute s ==>
          (iterate_mate f g) involute ((fixes f s) UNION (fixes g s))
Proof
  rpt strip_tac >-
  rw[iterate_mate_fixes_mate_fixes] >>
  `x IN s` by fs[fixes_element] >>
  drule_then strip_assume_tac iterate_mate_mate >>
  last_x_assum (qspecl_then [`f`, `g`, `x`] strip_assume_tac) >>
  simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Using direct WHILE.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Idea: a WHILE loop with involutions goes from fixed point to fixed point. *)

(* Note:

involute_involute_fix_odd_period_fix
|- !f g s p x.
          FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
          p = iterate_period (f o g) x /\ ODD p ==>
          !j.
              0 < j /\ j < p ==>
              (FUNPOW (f o g) j x IN fixes g s <=> (j = HALF p))

iterate_while_thm
|- !g b x k.
          (!j. j < k ==> g (FUNPOW b j x)) /\ ~g (FUNPOW b k x) ==>
          (WHILE g b x = FUNPOW b k x)
*)

(* Theorem: FINITE s /\ f involute s /\ g involute s /\ x IN fixes f s /\
            p = iterate_period (f o g) x /\ ODD p ==>
            WHILE (\y. g y <> y) (f o g) x IN fixes g s *)
(* Proof:
   Let b = \y. g y <> y,
   The goal is: WHILE b (f o g) x IN fixes g s

   If p = 1,
   Then x IN fixes g s             by involute_involute_fixes_both
     so ~b x                       by fixes_element
        WHILE b (f o g) x
      = x                          by iterate_while_thm_0, ~b x
    and x IN fixes g s             by above

   If p <> 1,
   Let h = HALF p,
       z = FUNPOW (f o g) h x.
   Then h <> 0                     by HALF_EQ_0, p <> 0, p <> 1
    and h < p                      by HALF_LT, p <> 0
   Note (f o g) PERMUTES s         by involute_involute_permutes
    and p <> 0                     by given ODD p
    and z IN fixes g s             by involute_involute_fix_orbit_fix_odd [1]
   Thus ~b z                       by fixes_element [2]

   Claim: !j. j < h ==> b (FUNPOW (f o g) j x)    [3]
   Proof: Let y = FUNPOW (f o g) j x, to show: b y.
          Note x IN s              by fixes_element
            so y IN s              by FUNPOW_closure
          If j = 0,
          then y = x               by FUNPOW_0
           and y NOTIN fixes g s   by involute_involute_fixes_both, p <> 1
            or b y                 by fixes_element
          If j <> 0,
          then 0 < j /\ j < p      by j < h, h < p
            so y NOTIN fixes g s   by involute_involute_fix_odd_period_fix, j <> h
            or b y                 by fixes_element

   Thus WHILE b (f o g) x = z      by iterate_while_thm, [3], [2]
          and z IN fixes g s       by [1]
*)
Theorem involute_involute_fix_odd_period_fix_while:
  !f g s p x. FINITE s /\ f involute s /\ g involute s /\
              x IN fixes f s /\ p = iterate_period (f o g) x /\ ODD p ==>
              WHILE (\y. g y <> y) (f o g) x IN fixes g s
Proof
  rpt strip_tac >>
  qabbrev_tac `b = \y. g y <> y` >>
  Cases_on `p = 1` >| [
    assume_tac involute_involute_fixes_both >>
    last_x_assum (qspecl_then [`f`, `g`, `s`, `p`, `x`] strip_assume_tac) >>
    `x IN fixes g s` by rfs[] >>
    `~b x` by rfs[fixes_element, Abbr`b`] >>
    simp[iterate_while_thm_0],
    `f o g PERMUTES s` by rw[involute_involute_permutes] >>
    drule_then strip_assume_tac involute_involute_fix_orbit_fix_odd >>
    last_x_assum (qspecl_then [`f`, `g`, `p`, `x`] strip_assume_tac) >>
    qabbrev_tac `h = HALF p` >>
    qabbrev_tac `z = FUNPOW (f o g) h x` >>
    `z IN fixes g s` by rfs[] >>
    `~b z` by rfs[fixes_element, Abbr`b`] >>
    `!j. j < h ==> b (FUNPOW (f o g) j x)` by
  (rpt strip_tac >>
    (Cases_on `j = 0` >> simp[]) >| [
      spose_not_then strip_assume_tac >>
      `x IN fixes g s` by rfs[fixes_element, Abbr`b`] >>
      assume_tac involute_involute_fixes_both >>
      last_x_assum (qspecl_then [`f`, `g`, `s`, `p`, `x`] strip_assume_tac) >>
      rfs[],
      `p <> 0` by metis_tac[EVEN, ODD_EVEN] >>
      `h < p` by rw[HALF_LT, Abbr`h`] >>
      spose_not_then strip_assume_tac >>
      qabbrev_tac `y = FUNPOW (f o g) j x` >>
      `y IN s` by rfs[fixes_element, FUNPOW_closure, Abbr`y`] >>
      `y IN fixes g s` by rfs[fixes_element, Abbr`b`] >>
      drule_then strip_assume_tac involute_involute_fix_odd_period_fix >>
      last_x_assum (qspecl_then [`f`, `g`, `p`, `x`] strip_assume_tac) >>
      `0 < j /\ j < p` by decide_tac >>
      `j = h` by metis_tac[] >>
      decide_tac
    ]) >>
    drule_then strip_assume_tac involute_involute_fix_orbit_fix_odd >>
    last_x_assum (qspecl_then [`f`, `g`, `p`, `x`] strip_assume_tac) >>
    assume_tac iterate_while_thm >>
    last_x_assum (qspecl_then [`b`, `f o g`, `x`, `h`] strip_assume_tac) >>
    rfs[]
  ]
QED


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
