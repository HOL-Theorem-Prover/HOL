(* ------------------------------------------------------------------------- *)
(* Modulo Polynomial Computations in (ZN n) Ring                             *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "computeRing";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory listTheory rich_listTheory arithmeticTheory numberTheory
     combinatoricsTheory dividesTheory gcdTheory logrootTheory;

(* val _ = load "polyFieldModuloTheory"; *)
open polynomialTheory polyWeakTheory polyRingTheory polyFieldTheory;
open polyMonicTheory polyEvalTheory;
open polyDivisionTheory polyFieldDivisionTheory polyFieldModuloTheory;
open ringTheory;

(* val _ = load "polyBinomialTheory"; *)
open polyBinomialTheory;
open ringBinomialTheory;

(* val _ = load "computePolyTheory"; *)
open computeBasicTheory computeOrderTheory computePolyTheory;
open ringInstancesTheory;

val _ = temp_overload_on("SQ", ``\n. n * (n :num)``);
val _ = temp_overload_on("HALF", ``\n. n DIV 2``);
val _ = temp_overload_on("TWICE", ``\n. 2 * n``);

(* ------------------------------------------------------------------------- *)
(* Modulo Polynomial Computations in (ZN n) Ring Documentation               *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
   p +z q     = ZN_poly_add n p q
   c oz p     = ZN_poly_cmult n c p
   p *z q     = ZN_poly_mult n k p q
   sqz p      = ZN_poly_sq n k p
   p **z m    = ZN_poly_exp n k p m

   zweak p    = Weak (ZN n) p
   zchop p    = poly_chop (ZN n) p
   zpX        = poly_shift (ZN n) (poly_one (ZN n)) 1
   zwadd p q  = weak_add (ZN n) p q
   zcmult c p = weak_cmult (ZN n) c p
   zpmult p q = poly_mult (ZN n) p q
   zpmod p q  = poly_mod (ZN n) p q
   zlist n    = GENLIST (K 0) n

   x+ n c      = poly_add (ZN n) zpX (poly_num (ZN n) c)                      -- for (X + |c|) in (ZN n)
   x+^ n c m   = poly_exp (ZN n) (x+ n c) m                                   -- for (X + |c|) ** m in (ZN n)
   x^+ n c m   = poly_add (ZN n) (poly_exp (ZN n) zpX m) (poly_num (ZN n) c)  -- for (X ** m + |c|) in (ZN n)
   x^- n m     = Unity (ZN n) m                                               -- for (X ** m - |1|) in (ZN n)
*)
(* Definitions and Theorems (# are exported):

   Helper Theorems:

   ZN Polynomial Computation:
   ZN_poly_add_def      |- !n p q. p +z q = MAP2 (\x y. (x + y) MOD n) p q
   ZN_poly_cmult_def    |- !n c p. c oz p = MAP (\x. (c * x) MOD n) p
   ZN_slide_def         |- (!n p1 p2. ZN_slide n p1 p2 [] = p1) /\
                            !n p1 p2 h t. ZN_slide n p1 p2 (h::t) = ZN_slide n (h oz p2 +z p1) (turn p2) t
   ZN_poly_mult_def     |- !n k p q. p *z q = ZN_slide n (GENLIST (K 0) k) p q
   ZN_poly_sq_def       |- !n k p. sqz p = p *z p
   ZN_poly_exp_def      |- !p n m k. p **z m = if m = 0 then [1]
                                     else (let q = sqz p **z HALF m in if EVEN m then q else p *z q)
   ZN_poly_special_def  |- !n k m c. ZN_poly_special n k m c = if k = 0 then []
                                     else if k = 1 then [(1 + c) MOD n] else
   (let q = if m MOD k = 0 then [(1 + c) MOD n] else c MOD n::PAD_LEFT 0 (m MOD k) [1] in PAD_RIGHT 0 k q)
   ZN_poly_monomial_def |- !n k c. ZN_poly_monomial n k c = if k = 0 then []
                                   else if k = 1 then [(1 + c) MOD n]
                                   else PAD_RIGHT 0 k [c MOD n; 1]

   Correctness of Polynomial Algorithms:
   ZN_poly_add_zero_zero   |- !n. [] +z [] = []
   ZN_poly_add_alt         |- !n p q. zweak p /\ zweak q /\ (LENGTH p = LENGTH q) ==> (p +z q = p zwadd q)
   ZN_poly_add_length      |- !n p q. (LENGTH p = LENGTH q) ==> (LENGTH (p +z q) = LENGTH q)
   ZN_poly_cmult_alt       |- !n p c. zweak p ==> (c oz p = c zcmult p)
   ZN_poly_cmult_length    |- !n p c. LENGTH (c oz p) = LENGTH p
   ZN_slide_alt            |- !n q p1 p2. 0 < n /\ zweak p1 /\ zweak p2 /\ zweak q /\ (LENGTH p1 = LENGTH p2) ==>
                                          (ZN_slide n p1 p2 q = poly_slide (ZN n) p1 p2 q)
   ZN_slide_length         |- !n q p1 p2. 0 < n /\ zweak p1 /\ zweak p2 /\ zweak q /\ (LENGTH p1 = LENGTH p2) ==>
                                          (LENGTH (ZN_slide n p1 p2 q) = LENGTH p2)
   ZN_poly_mult_alt        |- !n p q. 0 < n /\ zweak p /\ zweak q /\ q <> [] ==>
                                      (let k = LENGTH p in p *z q = unity_mod_mult (ZN n) p q)
   ZN_poly_mult_length     |- !n p q. 0 < n /\ zweak p /\ zweak q /\ q <> [] ==>
                                      (let k = LENGTH p in LENGTH (p *z q) = LENGTH p)
   ZN_poly_sq_alt          |- !n p. 0 < n /\ zweak p /\ p <> [] ==>
                                    (let k = LENGTH p in sqz p = unity_mod_sq (ZN n) p)
   ZN_poly_sq_length       |- !n p. 0 < n /\ zweak p /\ p <> [] ==>
                                    (let k = LENGTH p in LENGTH (sqz p) = LENGTH p)
   ZN_poly_exp_alt         |- !n p m. 1 < n /\ zweak p /\ p <> [] ==>
                                      (let k = LENGTH p in p **z m = unity_mod_exp (ZN n) p m)
   ZN_poly_exp_length      |- !n p. 1 < n /\ zweak p /\ p <> [] ==>
                              !m. 0 < m ==> (let k = LENGTH p in LENGTH (p **z m) = LENGTH p)
   ZN_poly_special_alt     |- !n. 1 < n ==> !k m c. ZN_poly_special n k m c = unity_mod_special (ZN n) k m c
   ZN_poly_special_length  |- !n. 1 < n ==> !k m c. LENGTH (ZN_poly_special n k m c) = k
   ZN_poly_monomial_alt    |- !n. 1 < n ==> !k c. ZN_poly_monomial n k c = unity_mod_monomial (ZN n) k c
   ZN_poly_monomial_length |- !n. 1 < n ==> !k c. LENGTH (ZN_poly_monomial n k c) = k

   Direct Versions of Correctness Theorems:
   ZN_chop_turn_eqn           |- !k n p. 1 < n /\ 1 < k /\ zweak p /\ (LENGTH p = k) ==>
                                         (zchop (turn p) = (p zpmult zpX) zpmod x^- n k)
   ZN_poly_mult_eqn           |- !k n p q. 1 < n /\ 1 < k /\ zweak p /\ zweak q /\
                                           (LENGTH p = k) /\ (LENGTH q = k) ==>
                                           (zchop (p *z q) = (p zpmult q) zpmod x^- n k)
   ZN_poly_sq_eqn             |- !k n p q. 1 < n /\ 1 < k /\ zweak p /\ (LENGTH p = k) ==>
                                           (zchop (sqz p) = (p zpmult p) zpmod x^- n k)
   ZN_poly_exp_eqn            |- !k n p m. 1 < n /\ 1 < k /\ zweak p /\ (LENGTH p = k) ==>
                                           (zchop (p **z m) = poly_exp (ZN n) p m zpmod x^- n k)
   ZN_unity_mod_X_exp_n_add_c |- !k n c. 1 < n /\ 0 < k ==> (x^+ n c n zpmod x^- n k = x^+ n c (n MOD k))

*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* ZN Polynomial Computation under modulus n and unity k = X ** k - |1|      *)
(* ------------------------------------------------------------------------- *)

(* Since (unity k) here just expects the lengths to be k,
   just ensure that this is the case upon operations. *)

(* Define ZN polynomial addition under modulus n (and unity k) *)
val ZN_poly_add_def = Define`
    ZN_poly_add (n:num) (p:num poly) (q:num poly) = MAP2 (\x y. (x + y) MOD n) p q
`;
(* overload ZN polynomial addition *)
val _ = overload_on("+z", ``ZN_poly_add n``);
val _ = set_fixity "+z" (Infixl 500); (* same as + in arithmeticScript.sml *)

(* Define ZN polynomial scalar multiplication under modulus n (and unity k) *)
val ZN_poly_cmult_def = Define`
    ZN_poly_cmult (n:num) (c: num) (p:num poly) = MAP (\x. (c * x) MOD n) p
`;
(* overload ZN polynomial scalar multiplication *)
val _ = overload_on("oz", ``ZN_poly_cmult n``);
val _ = set_fixity "oz" (Infixl 600); (* same as * in arithmeticScript.sml *)

(* Define ZN polynomial partial multiplication under modulus n (and unity k) *)
val ZN_slide_def = Define`
    (ZN_slide (n:num) (p1:num poly) (p2:num poly) [] = p1) /\
    (ZN_slide (n:num) (p1:num poly) (p2:num poly) ((h::t):num poly) =
       ZN_slide n ((h oz p2) +z p1) (turn p2) t)
`;
(* Define ZN polynomial multiplication under modulus n and unity k *)
val ZN_poly_mult_def = Define`
    ZN_poly_mult (n:num) (k:num) (p:num poly) (q:num poly) =
    ZN_slide n (GENLIST (K 0) k) p q
    (* Note LENGTH p = LENGTH q = k, for MOD (unity k) *)
`;
(* overload ZN polynomial multiplication *)
val _ = overload_on("*z", ``ZN_poly_mult n k``);
val _ = set_fixity "*z" (Infixl 600); (* same as * in arithmeticScript.sml *)
val _ = overload_on ("zlist", ``GENLIST (K 0)``);

(*
> EVAL ``ZN_poly_add 5 [1;2] [3;4]``; --> [4; 1]
> EVAL ``let n = 5 in [1;2] +z [3;4]``; --> [4; 1]
> EVAL ``let n = 5 in 3 oz [1;2]``; --> [3; 1]
> EVAL ``let n = 5 in let k = 2 in [1;2] *z [3;4]``; --> [1; 0]
*)

(* Define ZN polynomial square under modulus n and unity k *)
val ZN_poly_sq_def = Define`
    ZN_poly_sq (n:num) (k:num) (p:num poly) = ZN_poly_mult n k p p
    (* Note LENGTH p = k, for MOD (unity k) *)
`;
(* overload ZN polynomial square *)
val _ = overload_on("sqz", ``ZN_poly_sq n k``);

(* Define ZN polynomial exponentiation under modulus n and unity k *)
(*
val ZN_poly_exp_def = Define`
    ZN_poly_exp (n:num) (k:num) (p:num poly) m =
     if m = 0 then (PAD_RIGHT 0 k [1])
     else let q = ZN_poly_exp n k (ZN_poly_sq m k p) (HALF m)
          in if EVEN m then q else (ZN_poly_mult n k p q)
`;
*)
val ZN_poly_exp_def = Define`
    ZN_poly_exp (n:num) (k:num) (p:num poly) m =
     if m = 0 then [1]
     else let q = ZN_poly_exp n k (ZN_poly_sq n k p) (HALF m)
          in if EVEN m then q else (ZN_poly_mult n k p q)
`;
(* overload ZN polynomial exponentiation *)
val _ = overload_on("**z", ``ZN_poly_exp n k``);
val _ = set_fixity "**z" (Infixr 700); (* same as EXP in arithmeticScript.sml *)

(*
> EVAL ``let n = 5 in let k = 4 in [1;1;0;0] **z 2``; --> [1; 2; 1; 0]
> EVAL ``let n = 5 in let k = 4 in [1;1;0;0] **z 3``; --> [1; 3; 3; 1]
> EVAL ``let n = 5 in let k = 4 in [1;1;0;0] **z 4``; --> [2; 4; 1; 4]
*)

(* These are the initial weak polynomials with length equal to k *)

(* Define (X ** m + |c|) MOD (n, unity k) *)
val ZN_poly_special_def = Define`
    ZN_poly_special (n:num) (k:num) m (c:num) =
       if k = 0 then []
       else if k = 1 then [(1 + c) MOD n]
       else (let q = if m MOD k = 0 then [(1 + c) MOD n] else  (c MOD n) :: PAD_LEFT 0 (m MOD k) [1]
              in PAD_RIGHT 0 k q)
`;

(* Define (X + c) MOD (n, unity k) *)
val ZN_poly_monomial_def = Define`
    ZN_poly_monomial (n:num) (k:num) (c:num) =
       if k = 0 then [] else if k = 1 then [(1 + c) MOD n] else PAD_RIGHT 0 k [c MOD n; 1]
`;

(*
> EVAL ``let n = 5 in let k = 3 in (ZN_poly_monomial n k 1) **z n``; --> [1; 0; 1]
> EVAL ``ZN_poly_special 5 3 5 1``; --> [1; 0; 1]
> EVAL ``let n = 5 in let k = 3 in  (ZN_poly_monomial n k 2) **z n``; --> [2; 0; 1]
> EVAL ``ZN_poly_special 5 3 5 2``; --> [2; 0; 1]

> EVAL ``let n = 5 in let k = 3 in  (ZN_poly_monomial n k 1) **z n = ZN_poly_special n k n 1``; --> T
> EVAL ``let n = 5 in let k = 3 in  (ZN_poly_monomial n k 2) **z n = ZN_poly_special n k n 2``; --> T
> EVAL ``let n = 5 in let k = 3 in  (ZN_poly_monomial n k 3) **z n = ZN_poly_special n k n 3``; --> T
> EVAL ``let n = 5 in let k = 3 in  (ZN_poly_monomial n k 4) **z n = ZN_poly_special n k n 4``; --> T
*)

(* ------------------------------------------------------------------------- *)
(* Correctness of Polynomial Algorithms                                      *)
(* ------------------------------------------------------------------------- *)

(* Overloding on (ZN n) polynomials *)
val _ = overload_on("zweak", ``Weak (ZN n)``);
val _ = overload_on("zchop", ``poly_chop (ZN n)``);
val _ = overload_on("zpX", ``poly_shift (ZN n) (poly_one (ZN n)) 1``);
val _ = overload_on("zwadd", ``weak_add (ZN n)``);
val _ = set_fixity "zwadd" (Infixl 500); (* same as add *)
val _ = overload_on("zcmult", ``weak_cmult (ZN n)``);
val _ = set_fixity "zcmult" (Infixl 600); (* same as multiply *)
val _ = overload_on("zpmult", ``poly_mult (ZN n)``);
val _ = set_fixity "zpmult" (Infixl 600); (* same as multiply *)
val _ = overload_on("zpmod", ``poly_mod (ZN n)``);
val _ = set_fixity "zpmod" (Infixl 650); (* same as MOD *)

(* Theorem: [] +z [] = [] *)
(* Proof:
     [] +z []
   = MAP2 (\x y. (x + y) MOD m) [] []   by ZN_poly_add_def
   = []                                 by MAP2
*)
val ZN_poly_add_zero_zero = store_thm(
  "ZN_poly_add_zero_zero",
  ``!n:num. [] +z [] = []``,
  rw_tac std_ss[ZN_poly_add_def, MAP2]);

(* Theorem: zweak p /\ zweak q /\ (LENGTH p = LENGTH q) ==> (p +z q = p zwadd q) *)
(* Proof:
   By ZN_poly_add_def, weak_add_map2, this is to show:
      zweak p /\ zweak q /\ (LENGTH p = LENGTH q) ==>
      MAP2 (\x y. (x + y) MOD n) p q = MAP2 (\x y. (ZN n).sum.op x y) p q
   Note MEM x p ==> x IN (ZN n).carrier     by weak_every_mem
    and MEM y p ==> y IN (ZN n).carrier     by weak_every_mem
    ==> (ZN n).sum.op x y = (x + y) MOD m   by ZN_property
   Thus the maps are equal                  by MAP2_CONG, LENGTH p = LENGTH q
*)
val ZN_poly_add_alt = store_thm(
  "ZN_poly_add_alt",
  ``!(n:num) p q. zweak p /\ zweak q /\ (LENGTH p = LENGTH q) ==> (p +z q = p zwadd q)``,
  rw[ZN_poly_add_def, weak_add_map2] >>
  (irule MAP2_CONG >> simp[]) >>
  metis_tac[weak_every_mem, ZN_property]);

(* Theorem: (LENGTH p = LENGTH q) ==> (LENGTH (p +z q) = LENGTH q) *)
(* Proof:
     LENGTH (p +z q)
   = LENGTH (MAP2 (\x y. (x + y) MOD n) p q)    by ZN_poly_add_def
   = LENGTH q                                   by LENGTH_MAP2, LENGTH p = LENGTH q
*)
val ZN_poly_add_length = store_thm(
  "ZN_poly_add_length",
  ``!(n:num) p q. (LENGTH p = LENGTH q) ==> (LENGTH (p +z q) = LENGTH q)``,
  rw_tac std_ss[ZN_poly_add_def, LENGTH_MAP2]);

(* Theorem: zweak p /\ c < n ==> (c oz p = c zcmult p) *)
(* Proof:
   By ZN_poly_cmult_def, weak_cmult_map, this is to show:
      zweak p ==> MAP (\x. (c * x) MOD n) p = MAP (\x. (ZN n).prod.op c x) p
   Note MEM x p ==> x IN (ZN n).carrier      by weak_every_mem
    ==> (ZN n).prod.op c x = (c * x) MOD n   by ZN_property
   Thus the maps are equal                   by MAP_CONG
*)
val ZN_poly_cmult_alt = store_thm(
  "ZN_poly_cmult_alt",
  ``!(n:num) p c. zweak p ==> (c oz p = c zcmult p)``,
  rpt strip_tac >>
  rw[ZN_poly_cmult_def, weak_cmult_map] >>
  (irule MAP_CONG >> simp[]) >>
  metis_tac[weak_every_mem, ZN_property]);

(* Theorem: LENGTH (c oz p) = LENGTH p *)
(* Proof:
     LENGTH (c oz p)
   = LENGTH (MAP (\x. (c * x) MOD n) p)    by ZN_poly_cmult_def
   = LENGTH p                              by LENGTH_MAP
*)
val ZN_poly_cmult_length = store_thm(
  "ZN_poly_cmult_length",
  ``!(n:num) p c. LENGTH (c oz p) = LENGTH p``,
  rw_tac std_ss[ZN_poly_cmult_def, LENGTH_MAP]);

(* Theorem: 0 < n /\ zweak p1 /\ zweak p2 /\ zweak q /\ (LENGTH p1 = LENGTH p2) ==>
            (ZN_slide n p1 p2 q = poly_slide (ZN n) p1 p2 q) *)
(* Proof:
   By induction on q.
   Base: ZN_slide n p1 p2 [] = poly_slide (ZN n) p1 p2 []
         ZN_slide n p1 p2 []
       = p1                           by ZN_slide_def
       = poly_slide (ZN n) p1 p2 []   by poly_slide_def
   Step: !p1 p2. ZN_slide n p1 p2 q = poly_slide (ZN n) p1 p2 q ==>
         zweak (h::q) ==> ZN_slide n p1 p2 (h::q) = poly_slide (ZN n) p1 p2 (h::q)
       Note h IN (ZN n).carrier /\ zweak q        by weak_cons
       Note Ring (ZN n)                           by ZN_ring, 0 < n
        and LENGTH (h oz p2) = LENGTH p2          by ZN_poly_cmult_length
        and LENGTH (h oz p2 +z p1) = LENGTH p1    by ZN_poly_add_length
        and LENGTH (turn p2) = LENGTH p2          by turn_length
       Note h oz p2 = h zcmult p2                 by ZN_poly_cmult_alt
        ==> zweak (h oz p2)                       by weak_cmult_weak, Ring (ZN n)
       Also h oz p2 +z p1 = (h zcmult p2) zwadd p1   by ZN_poly_add_alt, [1]
        ==> zweak (h oz p2 +z p1)                 by weak_add_weak
        and zweak (turn p2)                       by weak_turn

          ZN_slide n p1 p2 (h::q)
        = ZN_slide n (h oz p2 +z p1) (turn p2) q                by ZN_slide_def
        = poly_slide (ZN n) (h oz p2 +z p1) (turn p2) q         by induction hypothesis
        = poly_slide (ZN n) (h zcmult p2 zwadd p1) (turn p2) q  by [1]
        = poly_slide (ZN n) p1 p2 (h::q)                        by poly_slide_def
*)
val ZN_slide_alt = store_thm(
  "ZN_slide_alt",
  ``!n q p1 p2. 0 < n /\ zweak p1 /\ zweak p2 /\ zweak q /\ (LENGTH p1 = LENGTH p2) ==>
               (ZN_slide n p1 p2 q = poly_slide (ZN n) p1 p2 q)``,
  strip_tac >>
  Induct >-
  rw[ZN_slide_def, poly_slide_def] >>
  rw[ZN_slide_def, poly_slide_def] >>
  `LENGTH (h oz p2) = LENGTH p2` by rw_tac std_ss[ZN_poly_cmult_length] >>
  `LENGTH (h oz p2 +z p1) = LENGTH p1` by rw_tac std_ss[ZN_poly_add_length] >>
  `LENGTH (turn p2) = LENGTH p2` by rw_tac std_ss[turn_length] >>
  `Ring (ZN n)` by rw_tac std_ss[ZN_ring] >>
  `h oz p2 = h zcmult p2` by rw_tac std_ss[ZN_poly_cmult_alt] >>
  `zweak (h oz p2)` by rw_tac std_ss[weak_cmult_weak] >>
  `h oz p2 +z p1 = (h zcmult p2) zwadd p1` by rw_tac std_ss[ZN_poly_add_alt] >>
  `zweak (h oz p2 +z p1)` by metis_tac[weak_add_weak] >>
  `zweak (turn p2)` by rw_tac std_ss[weak_turn] >>
  rw[]);

(* Theorem: 0 < n /\ zweak p1 /\ zweak p2 /\ zweak q /\ (LENGTH p1 = LENGTH p2) ==>
            (LENGTH (ZN_slide n p1 p2 q) = LENGTH p2) *)
(* Proof:
     LENGTH (ZN_slide n p1 p2 q)
   = LENGTH (poly_slide (ZN n) p1 p2 q)         by ZN_slide_alt
   = if q = [] then LENGTH p1 else LENGTH p2    by poly_slide_length, LENGTH p1 <= LENGTH p2
   = LENGTH p2                                  by LENGTH p1 = LENGTH p2
*)
val ZN_slide_length = store_thm(
  "ZN_slide_length",
  ``!(n:num) q p1 p2. 0 < n /\ zweak p1 /\ zweak p2 /\ zweak q /\ (LENGTH p1 = LENGTH p2) ==>
                     (LENGTH (ZN_slide n p1 p2 q) = LENGTH p2)``,
  rw[ZN_slide_alt, poly_slide_length]);

(* Theorem: 0 < n /\ zweak p /\ zweak q /\ q <> [] ==>
            let k = LENGTH p in (p *z q = unity_mod_mult (ZN n) p q) *)
(* Proof:
   Let t = GENLIST (K 0) k.
   Note Ring (ZN n)             by ZN_ring, 0 < n
    and zero_poly (ZN n) t      by zero_poly_genlist_zero, ZN_property
    ==> zweak t                 by zero_poly_weak, Ring (ZN n)
   Also LENGTH t = k            by LENGTH_GENLIST

     p *z q
   = ZN_slide n t p q                           by ZN_poly_mult_def
   = poly_slide (ZN n) t p q                    by ZN_slide_alt
   = poly_slide (ZN n) (poly_zero (ZN n)) p q   by poly_slide_init_zero_poly
   = unity_mod_mult (ZN n) p q                  by unity_mod_mult_def
*)
val ZN_poly_mult_alt = store_thm(
  "ZN_poly_mult_alt",
  ``!n p q. 0 < n /\ zweak p /\ zweak q /\ q <> [] ==>
            let k = LENGTH p in (p *z q = unity_mod_mult (ZN n) p q)``,
  rw_tac std_ss[] >>
  rw[ZN_poly_mult_def, unity_mod_mult_def] >>
  qabbrev_tac `t = GENLIST (K 0) k` >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `zero_poly (ZN n) t` by metis_tac[zero_poly_genlist_zero, ZN_property] >>
  `zweak t` by rw[zero_poly_weak] >>
  `LENGTH t = k` by rw[Abbr`t`] >>
  rw[ZN_slide_alt, Once poly_slide_init_zero_poly]);

(* Theorem: 0 < n /\ zweak p /\ zweak q /\ q <> [] ==>
            let k = LENGTH p in (LENGTH (p *z q) = LENGTH p) *)
(* Proof:
     LENGTH (p *z q)
   = LENGTH (unity_mod_mult (ZN n) p q)      by ZN_poly_mult_alt
   = LENGTH p                                by unity_mod_mult_length, q <> []
*)
val ZN_poly_mult_length = store_thm(
  "ZN_poly_mult_length",
  ``!n p q. 0 < n /\ zweak p /\ zweak q /\ q <> [] ==>
            let k = LENGTH p in (LENGTH (p *z q) = LENGTH p)``,
  metis_tac[ZN_poly_mult_alt, unity_mod_mult_length]);

(* Theorem: 0 < n /\ zweak p /\ p <> [] ==> let k = LENGTH p in (sqz p = unity_mod_sq (ZN n) p) *)
(* Proof:
     sqz p
   = p *z p                          by ZN_poly_sq_def
   = unity_mod_mult (ZN n) p p)      by ZN_poly_mult_alt, p <> []
   = unity_mod_sq (ZN n) p           by unity_mod_sq_def
*)
val ZN_poly_sq_alt = store_thm(
  "ZN_poly_sq_alt",
  ``!n p. 0 < n /\ zweak p /\ p <> [] ==> let k = LENGTH p in (sqz p = unity_mod_sq (ZN n) p)``,
  metis_tac[ZN_poly_sq_def, unity_mod_sq_def, ZN_poly_mult_alt]);

(* Theorem: 0 < n /\ zweak p /\ p <> [] ==> let k = LENGTH p in (LENGTH (sqz p) = LENGTH p) *)
(* Proof:
     LENGTH (sqz p)
   = LENGTH (unity_mod_sq (ZN n) p)      by ZN_poly_sq_alt
   = LENGTH p                            by unity_mod_sq_length
*)
val ZN_poly_sq_length = store_thm(
  "ZN_poly_sq_length",
  ``!n p. 0 < n /\ zweak p /\ p <> [] ==> let k = LENGTH p in (LENGTH (sqz p) = LENGTH p)``,
  metis_tac[ZN_poly_sq_alt, unity_mod_sq_length]);

(* Theorem: 1 < n /\ zweak p /\ p <> [] ==> let k = LENGTH p in (p **z m = unity_mod_exp (ZN n) p m) *)
(* Proof:
   Note Ring (ZN n)                  by ZN_ring, 0 < n
    and poly_one (ZN n) = [1]        by ZN_ids_alt, poly_one, 1 < n

   By complete induction on m.
   If m = 0,
          p **z 0
        = [1]                        by ZN_poly_exp_def
        = poly_one (ZN n)            by above
        = unity_mod_exp (ZN n) p 0   by unity_mod_exp_def
   If m = 1,
      Note ~EVEN 1                   by EVEN, ONE
       and Weak (ZN n) [1]           by ZN_ids_alt, weak_one
       and [1] <> []                 by NOT_NIL_CONS
          p **z 1
        = p *z ((sqz p) **z (HALF 1))    by ZN_poly_exp_def
        = p *z ((sqz p) **z 0)           by arithmetic
        = p *z [1]                       by ZN_poly_exp_def
        = unity_mod_mult (ZN n) p [1]    by ZN_poly_mult_alt
        = unity_mod_mult (ZN n) p (poly_one (ZN n))   by above
        = unity_mod_mult (ZN n) p (unity_mod_exp (ZN n) (unity_mod_sq (ZN n) p) 0)  by unity_mod_exp_def
        = unity_mod_mult (ZN n) p (unity_mod_exp (ZN n) (unity_mod_sq (ZN n) p) (HALF 1)) by MOD_LESS
        = unity_mod_exp (ZN n) p 1       by unity_mod_exp_def
   If m <> 0, m <> 1,
      Then HALF m < m                by DIV_LESS, 0 < m, 1 < 2
       and HALF m <> 0               by HALF_EQ_0, m <> 0, m <> 1
        or 0 < HALF m                by arithmetic, for unity_mod_exp_length
      Let q = unity_mod_sq (ZN n) p.
      Then zweak q                   by unity_mod_sq_weak
       and LENGTH q = LENGTH p       by unity_mod_sq_length
      Thus q <> []                   by LENGTH_NIL

      If EVEN m,
           p **z m
         = sqz p **z (HALF m)                by ZN_poly_exp_def, EVEN m
         = q **z (HALF m)                    by ZN_poly_sq_alt, q <> []
         = unity_mod_exp (ZN n) q (HALF m)   by induction hypothesis
         = unity_mod_exp (ZN n) p m          by unity_mod_exp_def, EVEN m

      If ~EVEN m,
         Let t = unity_mod_exp (ZN n) q (HALF m).
         Then zweak t                by unity_mod_exp_weak
          and LENGTH t = LENGTH q    by unity_mod_exp_length
         Thus t <> []                by LENGTH_NIL
           p **z m
         = p *z (sqz p **z (HALF m))         by ZN_poly_exp_def, ~EVEN m
         = p *z (q **z (HALF m))             by ZN_poly_sq_alt, q <> []
         = p *z t                            by induction hypothesis
         = unity_mod_mult (ZN n) p t         by unity_mod_mult_alt, t <> []
         = unity_mod_exp (ZN n) p n          by unity_mod_exp_def, ~EVEN m
*)
val ZN_poly_exp_alt = store_thm(
  "ZN_poly_exp_alt",
  ``!n p m. 1 < n /\ zweak p /\ p <> [] ==> let k = LENGTH p in (p **z m = unity_mod_exp (ZN n) p m)``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `poly_one (ZN n) = [1]` by metis_tac[ZN_ids_alt, poly_one, DECIDE``1 <> 0``] >>
  qpat_x_assum `p <> []` mp_tac >>
  qpat_x_assum `zweak p` mp_tac >>
  qid_spec_tac `p` >>
  completeInduct_on `m` >>
  rw_tac std_ss[] >>
  Cases_on `m = 0` >-
  rw[Once ZN_poly_exp_def, Once unity_mod_exp_def] >>
  Cases_on `m = 1` >| [
    `~EVEN 1` by metis_tac[EVEN, ONE] >>
    rw[Once ZN_poly_exp_def, Once unity_mod_exp_def] >>
    rw[Once ZN_poly_exp_def, Once unity_mod_exp_def] >>
    `zweak [1]` by metis_tac[ZN_ids_alt, weak_one, DECIDE``1 <> 0``] >>
    `[1] <> []` by rw[] >>
    metis_tac[ZN_poly_mult_alt],
    `HALF m < m` by rw[] >>
    `HALF m <> 0` by metis_tac[HALF_EQ_0] >>
    `0 < HALF m` by decide_tac >>
    qabbrev_tac `q = unity_mod_sq (ZN n) p` >>
    `zweak q` by rw[unity_mod_sq_weak, Abbr`q`] >>
    `LENGTH q = LENGTH p` by rw[unity_mod_sq_length, Abbr`q`] >>
    `q <> []` by metis_tac[LENGTH_NIL] >>
    rw[Once ZN_poly_exp_def, Once unity_mod_exp_def] >-
    metis_tac[ZN_poly_sq_alt] >>
    qabbrev_tac `t = unity_mod_exp (ZN n) q (HALF m)` >>
    `p *z t = unity_mod_mult (ZN n) p t` suffices_by metis_tac[ZN_poly_sq_alt] >>
    `zweak t` by rw[unity_mod_exp_weak, Abbr`t`] >>
    `LENGTH t = LENGTH q` by metis_tac[unity_mod_exp_length, ZN_ids_alt, DECIDE``1 <> 0``] >>
    `t <> []` by metis_tac[LENGTH_NIL] >>
    metis_tac[ZN_poly_mult_alt]
  ]);

(* Theorem: 1 < n /\ zweak p /\ p <> [] ==>
            !m. 0 < m ==> let k = LENGTH p in (LENGTH (p **z m) = LENGTH p) *)
(* Proof:
   Note (ZN n).prod.id = 1, and (ZN n).sum.id = 0   by ZN_ids_alt, 1 < n
     LENGTH (p **z m)
   = LENGTH (unity_mod_exp (ZN n) p m)              by ZN_poly_exp_alt
   = LENGTH p                                       by unity_mod_exp_length, m <> 0
*)
val ZN_poly_exp_length = store_thm(
  "ZN_poly_exp_length",
  ``!n p. 1 < n /\ zweak p /\ p <> [] ==>
   !m. 0 < m ==> let k = LENGTH p in (LENGTH (p **z m) = LENGTH p)``,
  rpt strip_tac >>
  `((ZN n).prod.id = 1) /\ ((ZN n).sum.id = 0)` by metis_tac[ZN_ids_alt] >>
  metis_tac[ZN_poly_exp_alt, unity_mod_exp_length, NOT_ZERO, ONE_NOT_ZERO]);

(* Theorem: 1 < n ==> !k m c. ZN_poly_special n k m c = unity_mod_special (ZN n) k m c *)
(* Proof:
   Note Ring (ZN n)                     by ZN_ring, 0 < n
    and (ZN n).sum.id = 0               by ZN_ids_alt, 1 < n
    and (ZN n).prod.id = 1              by ZN_ids_alt, 1 < n
   Note (ZN n).sum.exp 1 c = c MOD m    by ZN_num, 0 < n
    and (ZN n).sum.op ((ZN n).sum.exp 1 1) ((ZN n).sum.exp 1 c)
      = ((ZN n).sum.exp 1 1) + (ZN n).sum.exp 1 c)) MOD n   by ZN_property
      = (1 MOD n + c MOD n) MOD n       by ZN_num, 0 < n
      = (1 + c) MOD n                   by MOD_PLUS
   If k = 0,
        ZN_poly_special n 0 m c
      = []                              by ZN_poly_special_def
      = poly_zero (ZN n)                by poly_zero
      = unity_mod_special (ZN n) 0 m c  by unity_mod_special_def
   If k = 1,
        ZN_poly_special m 1 n c
      = [(1 + c) MOD n]                 by ZN_poly_special_def
      = [(ZN n).sum.op ((ZN n).sum.exp 1 1) ((ZN n).sum.exp 1 c)]  by above
      = unity_mod_special (ZN n) 1 m c  by unity_mod_special_def
   If k <> 0, k <> 1,
      If k MOD n = 0,
        ZN_poly_special n k m c
      = PAD_RIGHT 0 k [(1 + c) MOD n]   by ZN_poly_special_def
      = PAD_RIGHT (ZN n).sum.id [(ZN n).sum.op ((ZN n).sum.exp 1 1) ((ZN n).sum.exp 1 c)]  by above
      = unity_mod_special (ZN n) k m c  by unity_mod_special_def
      If k MOD n <> 0,
        ZN_poly_special n k m c
      = PAD_RIGHT 0 k
            (c MOD n::PAD_LEFT 0 (m MOD k) [1])  by ZN_poly_special_def
      = PAD_RIGHT (ZN n).sum.id k
            ((ZN n).sum.exp 1 c::PAD_LEFT (ZN n).sum.id (m MOD k) [(ZN n).prod.id])  by above
      = unity_mod_special (ZN n) k m c           by unity_mod_special_def
*)
val ZN_poly_special_alt = store_thm(
  "ZN_poly_special_alt",
  ``!n. 1 < n ==> !k m c. ZN_poly_special n k m c = unity_mod_special (ZN n) k m c``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `((ZN n).prod.id = 1) /\ ((ZN n).sum.id = 0)` by metis_tac[ZN_ids_alt] >>
  `(1 + c) MOD n = (1 MOD n + c MOD n) MOD n` by metis_tac[MOD_PLUS] >>
  rw[ZN_poly_special_def, unity_mod_special_def, ZN_property, ZN_num]);

(* Theorem: 1 < n ==> !k m c. LENGTH (ZN_poly_special n k m c) = k *)
(* Proof:
     LENGTH (ZN_poly_special n k m c)
   = LENGTH (unity_mod_special (ZN n) k m c)   by ZN_poly_special_alt
   = k                                         by unity_mod_special_length
*)
val ZN_poly_special_length = store_thm(
  "ZN_poly_special_length",
  ``!n. 1 < n ==> !k m c. LENGTH (ZN_poly_special n k m c) = k``,
  rw[ZN_poly_special_alt, unity_mod_special_length]);

(* Theorem: 1 < n ==> !k c. ZN_poly_monomial n k c = unity_mod_monomial (ZN n) k c *)
(* Proof:
   Note Ring (ZN n)                     by ZN_ring, 0 < n
    and (ZN n).sum.id = 0               by ZN_ids_alt
    and (ZN n).prod.id = 1              by ZN_ids_alt
   Note (ZN n).sum.exp 1 c = c MOD m    by ZN_num, 0 < n
    and (ZN n).sum.op ((ZN n).sum.exp 1 1) ((ZN n).sum.exp 1 c)
      = ((ZN n).sum.exp 1 1) + (ZN n).sum.exp 1 c)) MOD n   by ZN_property
      = (1 MOD n + c MOD n) MOD n       by ZN_num, 0 < n
      = (1 + c) MOD n                   by MOD_PLUS
   If k = 0,
        ZN_poly_monomial n 0 c
      = []                              by ZN_poly_monomial_def, k = 0
      = poly_zero (ZN n)                by poly_zero
      = unity_mod_monomial (ZN n) 0 c   by unity_mod_monomial_def, k = 0
   If k = 1,
        ZN_poly_monomial n 1 c
      = [(1 + c) MOD n]                 by ZN_poly_monomial_def, k = 1
      = [(ZN n).sum.op ((ZN n).sum.exp 1 1) ((ZN n).sum.exp 1 c)]       by above
      = unity_mod_monomial (ZN n) 1 c   by unity_mod_monomial_def, k = 1
   If k <> 0, k <> 1,
        ZN_poly_monomial n k c
      = PAD_RIGHT 0 k [c MOD n; 1]      by ZN_poly_monomial_def, k <> 0, k <> 1
      = PAD_RIGHT (ZN n).sum.id k [(ZN n).sum.exp 1 c; (ZN n).prod.id]  by above
      = unity_mod_monomial (ZN n) k c   by unity_mod_monomial_def, k <> 0, k <> 1
*)
val ZN_poly_monomial_alt = store_thm(
  "ZN_poly_monomial_alt",
  ``!n. 1 < n ==> !k c. ZN_poly_monomial n k c = unity_mod_monomial (ZN n) k c``,
  rpt strip_tac >>
  `0 < n` by decide_tac >>
  `Ring (ZN n)` by rw[ZN_ring] >>
  `((ZN n).prod.id = 1) /\ ((ZN n).sum.id = 0)` by metis_tac[ZN_ids_alt] >>
  `(1 + c) MOD n = (1 MOD n + c MOD n) MOD n` by metis_tac[MOD_PLUS] >>
  rw[ZN_poly_monomial_def, unity_mod_monomial_def, ZN_property, ZN_num]);

(* Theorem: 1 < n ==> !k c. LENGTH (ZN_poly_monomial n k c) = k *)
(* Proof:
     LENGTH (ZN_poly_monomial n k c)
   = LENGTH (unity_mod_monomial (ZN n) k c)  by ZN_poly_monomial_alt
   = k                                       by unity_mod_monomial_length
*)
val ZN_poly_monomial_length = store_thm(
  "ZN_poly_monomial_length",
  ``!n. 1 < n ==> !k c. LENGTH (ZN_poly_monomial n k c) = k``,
  rw[ZN_poly_monomial_alt, unity_mod_monomial_length]);

(* ------------------------------------------------------------------------- *)
(* Direct Versions of Correctness Theorems                                   *)
(* ------------------------------------------------------------------------- *)

(* Overloading for X + |c| in (ZN n) *)
val _ = overload_on("x+", ``\n c:num. poly_add (ZN n) zpX (poly_num (ZN n) c)``);

(* Overloading for (X + |c|) ** m in (ZN n) *)
val _ = overload_on ("x+^", ``\n c:num m. poly_exp (ZN n) (x+ n c) m``);

(* Overloading for (X ** m + |c|) in (ZN n) *)
val _ = overload_on ("x^+", ``\n c:num m. poly_add (ZN n) (poly_exp (ZN n) zpX m) (poly_num (ZN n) c)``);

(* Overloading for (X ** m - |1|) in (ZN n) *)
val _ = overload_on ("x^-", ``\n m. Unity (ZN n) m``);

(*
chop_turn_eqn;
chop_turn_eqn |> ISPEC ``ZN n``;
val it = |- Ring (ZN n) /\ (ZN n).prod.id <> (ZN n).sum.id ==>
   !p. zweak p /\ 1 < LENGTH p ==> (zchop (turn p) = (p zpmult zpX) zpmod x^- n (LENGTH p)): thm
*)

(* Theorem: 1 < n /\ 1 < k /\ zweak p /\ (LENGTH p = k) ==> (zchop (turn p) = (p zpmult zpX) zpmod (x^- n k)) *)
(* Proof: by chop_turn_eqn *)
val ZN_chop_turn_eqn = store_thm(
  "ZN_chop_turn_eqn",
  ``!k n p. 1 < n /\ 1 < k /\ zweak p /\ (LENGTH p = k) ==> (zchop (turn p) = (p zpmult zpX) zpmod (x^- n k))``,
  metis_tac[chop_turn_eqn, ZN_ring, ZN_ids_alt, DECIDE``(1 < n ==> 0 < n) /\ (0 <> 1)``]);

(*
> unity_mod_mult_eqn |> ISPEC ``ZN n``;
val it = |- Ring (ZN n) /\ (ZN n).prod.id <> (ZN n).sum.id ==>
        !p q. zweak p /\ zweak q /\ 1 < LENGTH p /\ q <> poly_zero (ZN n) ==>
     (zchop (unity_mod_mult (ZN n) p q) = (p zpmult q) zpmod x^- n (LENGTH p)): thm
> ZN_poly_mult_alt |> ISPEC ``n:num``;
val it = |- 0 < n ==> !p q. zweak p /\ zweak q /\ q <> [] ==>
                            (ZN_poly_mult n (LENGTH p) p q = unity_mod_mult (ZN n) p q): thm
*)

(* Theorem: 1 < n /\ 1 < k /\ zweak p /\ zweak q /\ (LENGTH p = k) /\ (LENGTH q = k) ==>
            (zchop (p *z q) = (p zpmult q) zpmod (x^- n k)) *)
(* Proof: by unity_mod_mult_eqn, ZN_poly_mult_alt *)
val ZN_poly_mult_eqn = store_thm(
  "ZN_poly_mult_eqn",
  ``!k n p q. 1 < n /\ 1 < k /\ zweak p /\ zweak q /\ (LENGTH p = k) /\ (LENGTH q = k) ==>
             (zchop (p *z q) = (p zpmult q) zpmod (x^- n k))``,
  rpt strip_tac >>
  `Ring (ZN n) /\ (ZN n).prod.id <> (ZN n).sum.id` by rw[ZN_ring, ZN_ids_alt] >>
  `q <> []` by metis_tac[LENGTH_NIL, DECIDE``1 < k ==> k <> 0``] >>
  metis_tac[unity_mod_mult_eqn, poly_zero, ZN_poly_mult_alt, DECIDE``1 < n ==> 0 < n``]);

(* Theorem: 1 < n /\ 1 < k /\ zweak p /\ (LENGTH p = k) ==> (zchop (sqz p) = (p zpmult p) zpmod (x^- n k)) *)
(* Proof: by ZN_poly_sq_def, ZN_poly_mult_eqn *)
val ZN_poly_sq_eqn = store_thm(
  "ZN_poly_sq_eqn",
  ``!k n p q. 1 < n /\ 1 < k /\ zweak p /\ (LENGTH p = k) ==> (zchop (sqz p) = (p zpmult p) zpmod (x^- n k))``,
  rw_tac std_ss[ZN_poly_sq_def, ZN_poly_mult_eqn]);

(*
> unity_mod_exp_eqn |> ISPEC ``ZN n``;
val it = |- Ring (ZN n) /\ (ZN n).prod.id <> (ZN n).sum.id ==>
   !n' p. zweak p /\ 1 < LENGTH p ==>
     (zchop (unity_mod_exp (ZN n) p n') = poly_exp (ZN n) p n' zpmod x^- n (LENGTH p)): thm
> ZN_poly_exp_alt |> ISPEC ``n:num``;
val it = |- 1 < n ==> !n' p. zweak p /\ p <> [] ==>
     (ZN_poly_exp n (LENGTH p) p n' = unity_mod_exp (ZN n) p n'): thm
*)

(* Theorem: 1 < n /\ 1 < k /\ zweak p /\ (LENGTH p = k) ==>
             (zchop (p **z m) = (poly_exp (ZN n) p m) zpmod (x^- n k)) *)
(* Proof: by unity_mod_exp_eqn, ZN_poly_exp_alt *)
val ZN_poly_exp_eqn = store_thm(
  "ZN_poly_exp_eqn",
  ``!k n p m. 1 < n /\ 1 < k /\ zweak p /\ (LENGTH p = k) ==>
             (zchop (p **z m) = (poly_exp (ZN n) p m) zpmod (x^- n k))``,
  rpt strip_tac >>
  `Ring (ZN n) /\ (ZN n).prod.id <> (ZN n).sum.id` by rw[ZN_ring, ZN_ids_alt] >>
  `p <> []` by metis_tac[LENGTH_NIL, DECIDE``1 < k ==> k <> 0``] >>
  metis_tac[unity_mod_exp_eqn, ZN_poly_exp_alt, DECIDE``1 < n ==> 0 < n``]);

(*
poly_unity_mod_X_exp_n_add_c
poly_unity_mod_X_exp_n_add_c |> ISPEC ``ZN n``;
val it = |- Ring (ZN n) /\ (ZN n).prod.id <> (ZN n).sum.id ==>
         !m. 0 < m ==> !n' c. x^+ n c n' zpmod x^- n m = x^+ n c (n' MOD m): thm
*)

(* Theorem: 1 < n /\ 0 < k ==> (x^+ n c n zpmod x^- n k = x^+ n c (n MOD k)) *)
(* Proof: by poly_unity_mod_X_exp_n_add_c *)
val ZN_unity_mod_X_exp_n_add_c = store_thm(
  "ZN_unity_mod_X_exp_n_add_c",
  ``!k n (c:num). 1 < n /\ 0 < k ==> (x^+ n c n zpmod x^- n k = x^+ n c (n MOD k))``,
  metis_tac[poly_unity_mod_X_exp_n_add_c, ZN_ring, ZN_ids_alt, DECIDE``(1 < n ==> 0 < n) /\ 1 <> 0``]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
