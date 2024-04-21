(* ------------------------------------------------------------------------- *)
(* Applying Group Theory: Group Instances                                    *)
(* ------------------------------------------------------------------------- *)

(*

Group Instances
===============
The important ones:

 Zn -- Addition Modulo n, n > 0.
Z*p -- Multiplication Modulo p, p a prime.
E*n -- Multiplication Modulo n, of order phi(n).

*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "groupInstances";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open prim_recTheory pred_setTheory arithmeticTheory dividesTheory gcdTheory
     numberTheory primeTheory;

open monoidTheory groupTheory groupOrderTheory subgroupTheory;

open groupProductTheory;

(* ------------------------------------------------------------------------- *)
(* Group Instances Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Group Data type:
   The generic symbol for group data is g.
   g.carrier = Carrier set of group
   g.op      = Binary operation of group
   g.id      = Identity element of group
   g.inv     = Inverse operation of group (as monoid_inv g)
*)
(* Overloading (# are temporary):
   Z n       = Zadd n
   Z* n      = Zstar n
*)
(* Definitions and Theorems (# are exported, ! are in computeLib):

   The Group Zn = Addition Modulo n (n > 0):
   Zadd_def      |- !n. Z n = <|carrier := count n; id := 0; op := (\i j. (i + j) MOD n)|>
   Zadd_element  |- !n x. x IN (Z n).carrier <=> x < n
   Zadd_property |- !n. (!x. x IN (Z n).carrier <=> x < n) /\ ((Z n).id = 0) /\
                      (!x y. (Z n).op x y = (x + y) MOD n) /\
                      FINITE (Z n).carrier /\ (CARD (Z n).carrier = n)
   Zadd_carrier  |- !n. (Z n).carrier = count n
   Zadd_carrier_alt  |- !n. (Z n).carrier = {i | i < n}
   Zadd_id       |- !n. (Z n).id = 0
   Zadd_finite   |- !n. FINITE (Z n).carrier
   Zadd_card     |- !n. CARD (Z n).carrier = n
   Zadd_group    |- !n. 0 < n ==> Group (Z n)
   Zadd_finite_group          |- !n. 0 < n ==> FiniteGroup (Z n)
   Zadd_finite_abelian_group  |- !n. 0 < n ==> FiniteAbelianGroup (Z n)
   Zadd_exp      |- !n. 0 < n ==> !x m. (Z n).exp x m = (x * m) MOD n
#! Zadd_eval     |- !n. ((Z n).carrier = count n) /\ (!x y. (Z n).op x y = (x + y) MOD n) /\ ((Z n).id = 0)
#  Zadd_inv      |- !n. 0 < n ==> !x. x < n ==> ((Z n).inv x = (n - x) MOD n)
!  Zadd_inv_compute |- !n x. (Z n).inv x = if 0 < n /\ x < n then (n - x) MOD n else FAIL ((Z n).inv x) bad_element

   The Group Z*p = Multiplication Modulo p (prime p):
   Zstar_def       |- !p. Z* p = <|carrier := residue p; id := 1; op := (\i j. (i * j) MOD p)|>
   Zstar_element   |- !p x. x IN (Z* p).carrier <=> 0 < x /\ x < p
   Zstar_property  |- !p. ((Z* p).carrier = residue p) /\ ((Z* p).id = 1) /\
                          (!x y. (Z* p).op x y = (x * y) MOD p) /\
                          FINITE (Z* p).carrier /\ (0 < p ==> (CARD (Z* p).carrier = p - 1))
   Zstar_carrier   |- !p. (Z* p).carrier = residue p
   Zstar_carrier_alt |- !p. (Z* p).carrier = {i | i <> 0 /\ i < p}
   Zstar_id        |- !p. (Z* p).id = 1
   Zstar_finite    |- !p. FINITE (Z* p).carrier
   Zstar_card      |- !p. 0 < p ==> (CARD (Z* p).carrier = p - 1)
   Zstar_group     |- !p. prime p ==> Group (Z* p)
   Zstar_finite_group         |- !p. prime p ==> FiniteGroup (Z* p)
   Zstar_finite_abelian_group |- !p. prime p ==> FiniteAbelianGroup (Z* p)
   Zstar_exp       |- !p a. prime p /\ a IN (Z* p).carrier ==> !n. (Z* p).exp a n = a ** n MOD p
!  Zstar_eval      |- !p. ((Z* p).carrier = residue p) /\
                          (!x y. (Z* p).op x y = (x * y) MOD p) /\ ((Z* p).id = 1)
!  Zstar_inv       |- !p. prime p ==> !x. 0 < x /\ x < p ==>
                     ((Z* p).inv x = (Z* p).exp x (order (Z* p) x - 1))
   Zstar_inv_compute |- !p x. (Z* p).inv x = if prime p /\ 0 < x /\ x < p
                                            then (Z* p).exp x (order (Z* p) x - 1)
                                            else FAIL ((Z* p).inv x) bad_element

   Euler's generalization of Modulo Multiplicative Group (any modulo n):
   Estar_def       |- !n. Estar n = <|carrier := Euler n; id := 1; op := (\i j. (i * j) MOD n)|>
   Estar_alt       |- !n. Estar n =
                            <|carrier := {i | 0 < i /\ i < n /\ coprime n i}; id := 1;
                                   op := (\i j. (i * j) MOD n)|>
!  Estar_eval      |- !n. (Estar n).carrier = Euler n /\
                          (!x y. (Estar n).op x y = (x * y) MOD n) /\ ((Estar n).id = 1)
   Estar_element   |- !n x. x IN (Estar n).carrier <=> 0 < x /\ x < n /\ coprime n x
   Estar_property  |- !n. ((Estar n).carrier = Euler n) /\ ((Estar n).id = 1) /\
                          (!x y. (Estar n).op x y = (x * y) MOD n) /\
                          FINITE (Estar n).carrier /\ (CARD (Estar n).carrier = totient n)
   Estar_carrier   |- !n. (Estar n).carrier = Euler n
   Estar_carrier_alt |- !n. (Estar n).carrier = {i | 0 < i /\ i < n /\ coprime n i}
   Estar_id        |- !n. (Estar n).id = 1
   Estar_finite    |- !n. FINITE (Estar n).carrier
   Estar_card      |- !n. CARD (Estar n).carrier = totient n
   Estar_card_alt  |- !n. 1 < n ==> (CARD (Estar n).carrier = phi n)
   Estar_group         |- !n. 1 < n ==> Group (Estar n)
   Estar_finite_group  |- !n. 1 < n ==> FiniteGroup (Estar n)
   Estar_finite_abelian_group |- !n. 1 < n ==> FiniteAbelianGroup (Estar n)
   Estar_exp       |- !n a. 1 < n /\ a IN (Estar n).carrier ==> !k. (Estar n).exp a k = a ** k MOD n

   Euler-Fermat Theorem:
   Euler_Fermat_eqn     |- !n a. 1 < n /\ a < n /\ coprime n a ==> (a ** totient n MOD n = 1)
   Euler_Fermat_thm     |- !n a. 1 < n /\ coprime n a ==> (a ** totient n MOD n = 1)
   Euler_Fermat_alt     |- !n a. 1 < n /\ coprime a n ==> a ** totient n MOD n = 1
   Fermat_little_thm    |- !p a. prime p /\ 0 < a /\ a < p ==> (a ** (p - 1) MOD p = 1)
   Fermat_little_eqn    |- !p a. prime p ==> a ** p MOD p = a MOD p
   Estar_inv            |- !n a. 1 < n /\ a < n /\ coprime n a ==>
                                 (Estar n).inv a = a ** (totient n - 1) MOD n
!  Estar_inv_compute    |- !n a. (Estar n).inv a =
                                 if 1 < n /\ a < n /\ coprime n a
                                 then a ** (totient n - 1) MOD n
                                 else FAIL ((Estar n).inv a) bad_element

   The Trivial Group:
   trivial_group_def |- !e. trivial_group e = <|carrier := {e}; id := e; op := (\x y. e)|>
   trivial_group_carrier
                     |- !e. (trivial_group e).carrier = {e}
   trivial_group_id  |- !e. (trivial_group e).id = e
   trivial_group     |- !e. FiniteAbelianGroup (trivial_group e)

   The Function Cyclic Group:
   fn_cyclic_group_def  |- !e f. fn_cyclic_group e f =
         <|carrier := {x | ?n. FUNPOW f n e = x};
                id := e;
                op := (\x y. @z. !xi yi. (FUNPOW f xi e = x) /\ (FUNPOW f yi e = y) ==> (FUNPOW f (xi + yi) e = z))|>
   fn_cyclic_group_alt  |- !e f n. (?k. k <> 0 /\ (FUNPOW f k e = e)) /\
      (n = LEAST k. k <> 0 /\ (FUNPOW f k e = e)) ==>
         ((fn_cyclic_group e f).carrier = {FUNPOW f k e | k < n}) /\
         ((fn_cyclic_group e f).id = e) /\
         !i j. (fn_cyclic_group e f).op (FUNPOW f i e) (FUNPOW f j e) = FUNPOW f ((i + j) MOD n) e
   fn_cyclic_group_carrier              |- !e f. (fn_cyclic_group e f).carrier = { x | ?n. FUNPOW f n e = x }
   fn_cyclic_group_id                   |- !e f. (fn_cyclic_group e f).id = e
   fn_cyclic_group_group                |- !e f. (?n. n <> 0 /\ (FUNPOW f n e = e)) ==> Group (fn_cyclic_group e f)
   fn_cyclic_group_finite_abelian_group |- !e f. (?n. n <> 0 /\ (FUNPOW f n e = e)) ==> FiniteAbelianGroup (fn_cyclic_group e f)
   fn_cyclic_group_finite_group         |- !e f. (?n. n <> 0 /\ (FUNPOW f n e = e)) ==> FiniteGroup (fn_cyclic_group e f)

   The Group of Addition Modulo n:
   add_mod_def      |- !n. add_mod n = <|carrier := {i | i < n}; id := 0; op := (\i j. (i + j) MOD n)|>
   add_mod_element  |- !n x. x IN (add_mod n).carrier <=> x < n
   add_mod_property |- !n. (!x. x IN (add_mod n).carrier <=> x < n) /\
                           ((add_mod n).id = 0) /\
                           (!x y. (add_mod n).op x y = (x + y) MOD n) /\
                           FINITE (add_mod n).carrier /\ (CARD (add_mod n).carrier = n)
   add_mod_carrier  |- !n. (add_mod n).carrier = { i | i < n }
   add_mod_carrier_alt    |- !n. (add_mod n).carrier = count n
   add_mod_id       |- !n. (add_mod n).id = 0
   add_mod_finite   |- !n. FINITE (add_mod n).carrier
   add_mod_card     |- !n. CARD (add_mod n).carrier = n
   add_mod_group    |- !n. 0 < n ==> Group (add_mod n)
   add_mod_abelian_group  |- !n. 0 < n ==> AbelianGroup (add_mod n)
   add_mod_finite_group   |- !n. 0 < n ==> FiniteGroup (add_mod n)
   add_mod_finite_abelian_group |- !n. 0 < n ==> FiniteAbelianGroup (add_mod n)
   add_mod_exp            |- !n. 0 < n ==> !x m. (add_mod n).exp x m = (x * m) MOD n
#! add_mod_eval     |- !n. ((add_mod n).carrier = {i | i < n}) /\
                           (!x y. (add_mod n).op x y = (x + y) MOD n) /\ ((add_mod n).id = 0)
#  add_mod_inv      |- !n. 0 < n ==> !x. x < n ==> ((add_mod n).inv x = (n - x) MOD n)
!  add_mod_inv_compute |- !n x. (add_mod n).inv x = if 0 < n /\ x < n then (n - x) MOD n else FAIL ((add_mod n).inv x) bad_element

   The Group of Multiplication Modulo prime p:
   mult_mod_def     |- !p. mult_mod p = <|carrier := {i | i <> 0 /\ i < p}; id := 1; op := (\i j. (i * j) MOD p)|>
   mult_mod_element      |- !p x. x IN (mult_mod p).carrier <=> x <> 0 /\ x < p
   mult_mod_element_alt  |- !p x. x IN (mult_mod p).carrier <=> 0 < x /\ x < p
   mult_mod_property     |- !p. (!x. x IN (mult_mod p).carrier ==> x <> 0) /\
                                (!x. x IN (mult_mod p).carrier <=> 0 < x /\ x < p) /\
                                ((mult_mod p).id = 1) /\
                                (!x y. (mult_mod p).op x y = (x * y) MOD p) /\
                                FINITE (mult_mod p).carrier /\ (0 < p ==> (CARD (mult_mod p).carrier = p - 1))
   mult_mod_carrier |- !p. (mult_mod p).carrier = { i | i <> 0 /\ i < p }
   mult_mod_carrier_alt    |- !p. (mult_mod p).carrier = residue p
   mult_mod_id      |- !p. (mult_mod p).id = 1
   mult_mod_finite  |- !p. FINITE (mult_mod p).carrier
   mult_mod_card    |- !p. 0 < p ==> (CARD (mult_mod p).carrier = p - 1)
   mult_mod_group   |- !p. prime p ==> Group (mult_mod p)
   mult_mod_abelian_group  |- !p. prime p ==> AbelianGroup (mult_mod p)
   mult_mod_finite_group   |- !p. prime p ==> FiniteGroup (mult_mod p)
   mult_mod_finite_abelian_group  |- !p. prime p ==> FiniteAbelianGroup (mult_mod p)
   mult_mod_exp     |- !p a. prime p /\ a IN (mult_mod p).carrier ==> !n. (mult_mod p).exp a n = a ** n MOD p
#! mult_mod_eval    |- !p. ((mult_mod p).carrier = {i | i <> 0 /\ i < p}) /\
                           (!x y. (mult_mod p).op x y = (x * y) MOD p) /\ ((mult_mod p).id = 1)
#  mult_mod_inv     |- !p. prime p ==> !x. 0 < x /\ x < p ==>
                           ((mult_mod p).inv x = (mult_mod p).exp x (order (mult_mod p) x - 1))
!  mult_mod_inv_compute |- !p x. (mult_mod p).inv x = if prime p /\ 0 < x /\ x < p
                                                 then (mult_mod p).exp x (order (mult_mod p) x - 1)
                                                 else FAIL ((mult_mod p).inv x) bad_element

   ElGamal encryption and decryption -- purely group-theoretic:
   ElGamal_encrypt_def  |- !g y h m k. ElGamal_encrypt g y h m k = (y ** k,h ** k * m)
   ElGamal_decrypt_def  |- !g x a b. ElGamal_decrypt g x (a,b) = |/ (a ** x) * b
   ElGamal_correctness  |- !g. Group g ==> !(y::G) (h::G) (m::G) k x. (h = y ** x) ==>
                               (ElGamal_decrypt g x (ElGamal_encrypt g y h m k) = m)
*)
(* ------------------------------------------------------------------------- *)
(* The Group Zn = Addition Modulo n, for n > 0.                              *)
(* ------------------------------------------------------------------------- *)

(* Define (Zadd n) = Addition Modulo n Group *)
val Zadd_def = zDefine`
  Zadd n : num group =
    <| carrier := count n;
            id := 0;
       (*  inv := (\i. (n - i) MOD n);  -- so that inv 0 = 0 *)
            op := (\i j. (i + j) MOD n)
     |>
`;
(* Use of zDefine to avoid incorporating into computeLib, by default. *)
(* This is the same as add_mod below, using {i | i < n} as carrier. *)

(* Overload Zadd n *)
val _ = temp_overload_on("Z", ``Zadd``);

(*
- type_of ``Z n``;
> val it = ``:num group`` : hol_type
> EVAL ``(Z 7).op 5 6``;
val it = |- (Z 7).op 5 6 = (Z 7).op 5 6: thm

Here, we are putting a finer control on evaluation.
If we had use Define instead of zDefine, this would work.
However, because (Zadd n).inv is an add-on field, that would not work.
We define Zadd_eval and Zadd_inv below, and put them into computeLib.
*)

(* Theorem: Evaluation of Zadd for each record field. *)
(* Proof: by Zadd_def. *)
val Zadd_eval = store_thm(
  "Zadd_eval",
  ``!n. ((Z n).carrier = count n) /\
       (!x y. (Z n).op x y = (x + y) MOD n) /\
       ((Z n).id = 0)``,
  rw_tac std_ss[Zadd_def]);
(* This is later exported to computeLib, with Zadd_inv_compute. *)

(* Theorem: x IN (Z n).carrier <=> x < n *)
(* Proof: by definition, IN_COUNT. *)
val Zadd_element = store_thm(
  "Zadd_element",
  ``!n x. x IN (Z n).carrier <=> x < n``,
  rw[Zadd_def]); (* by IN_COUNT *)

(* Theorem: properties of Zn. *)
(* Proof: by definition. *)
val Zadd_property = store_thm(
  "Zadd_property",
  ``!n. (!x. x IN (Z n).carrier <=> x < n) /\
       ((Z n).id = 0) /\
       (!x y. (Z n).op x y = (x + y) MOD n) /\
       FINITE (Z n).carrier /\
       (CARD (Z n).carrier = n)``,
  rw_tac std_ss[Zadd_def, IN_COUNT, FINITE_COUNT, CARD_COUNT]);

(* Theorem: (Z n).carrier = count n *)
(* Proof: by Zadd_def. *)
Theorem Zadd_carrier:
  !n. (Z n).carrier = count n
Proof
  simp[Zadd_def]
QED

(* Theorem: (Z n).carrier = {i | i < n} *)
(* Proof: by Zadd_carrier. *)
Theorem Zadd_carrier_alt:
  !n. (Z n).carrier = {i | i < n}
Proof
  simp[Zadd_carrier, EXTENSION]
QED

(* Theorem: (Z n).id = 0 *)
(* Proof: by Zadd_def. *)
Theorem Zadd_id:
  !n. (Z n).id = 0
Proof
  simp[Zadd_def]
QED

(* Theorem: FINITE (Z n).carrier *)
(* Proof: by Zadd_property *)
val Zadd_finite = store_thm(
  "Zadd_finite",
  ``!n. FINITE (Z n).carrier``,
  rw[Zadd_property]);

(* Theorem: CARD (Z n).carrier = n *)
(* Proof: by Zadd_property *)
val Zadd_card = store_thm(
  "Zadd_card",
  ``!n. CARD (Z n).carrier = n``,
  rw[Zadd_property]);

(* Theorem: Zn is a group if n > 0. *)
(* Proof: by definitions:
   Associativity: ((x + y) MOD n + z) MOD n = (x + (y + z) MOD n) MOD n
      true by MOD_ADD_ASSOC.
   Inverse: ?y. y < n /\ ((y + x) MOD n = 0)
      If x = 0, let y = 0, true by ZERO_MOD.
      If x <> 0, let y = n - x, true by DIVMOD_ID.
*)
val Zadd_group = store_thm(
  "Zadd_group",
  ``!n. 0 < n ==> Group (Z n)``,
  rw_tac std_ss[group_def_alt, Zadd_property] >| [
    rw_tac std_ss[MOD_ADD_ASSOC],
    Cases_on `x = 0` >| [
      metis_tac[ZERO_MOD, ADD],
      `n - x < n /\ ((n - x) + x = n)` by decide_tac >>
      metis_tac[DIVMOD_ID]
    ]
  ]);

(* Theorem: Zn is a FiniteGroup if n > 0. *)
(* Proof: by Zadd_group and FINITE_Zadd_carrier. *)
val Zadd_finite_group = store_thm(
  "Zadd_finite_group",
  ``!n. 0 < n ==> FiniteGroup (Z n)``,
  rw_tac std_ss[FiniteGroup_def, Zadd_group, Zadd_property]);

(* Theorem: Zn is a finite Abelian group if n > 0. *)
(* Proof: by Zadd_finite_group and arithmetic. *)
val Zadd_finite_abelian_group = store_thm(
  "Zadd_finite_abelian_group",
  ``!n. 0 < n ==> FiniteAbelianGroup (Z n)``,
  rw_tac std_ss[FiniteAbelianGroup_def, AbelianGroup_def, Zadd_property] >-
  rw_tac std_ss[Zadd_group] >>
  rw_tac arith_ss [Zadd_def]);

(* Theorem: 0 < n ==> !x m. (Z n).exp x m = (x * m) MOD n *)
(* Proof:
   Note Group (Z n)        by Zadd_group
   By induction on m.
   Base case: (Z n).exp x 0 = (x * 0) MOD n
        (Z n).exp x 0
      = (Z n).id           by group_exp_0
      = 0                  by Zadd_property
      = (x * 0) MOD n      by MULT
   Step case: (Z n).exp x m = (x * m) MOD n ==>
              (Z n).exp x (SUC m) = (x * SUC m) MOD n
        (Z n).exp x (SUC m)
      = (Z n).op m (Z n).exp x m       by group_exp_SUC
      = (m + (Z n).exp x m) MOD n      by Zadd_property
      = (m + (x * m) MOD n) MOD n      by induction hypothesis
      = (m + x * m) MOD n              by MOD_PLUS, MOD_MOD
      = (x * SUC m) MOD n              by MULT_SUC
*)
val Zadd_exp = store_thm(
  "Zadd_exp",
  ``!n. 0 < n ==> !x m. (Z n).exp x m = (x * m) MOD n``,
  rpt strip_tac >>
  `Group (Z n)` by rw[Zadd_group] >>
  Induct_on `m` >-
  rw[group_exp_0, Zadd_property] >>
  rw_tac std_ss[group_exp_SUC, Zadd_property] >>
  metis_tac[MOD_PLUS, MOD_MOD, MULT_SUC]);

(* Theorem: (Z n).inv x = (n - x) MOD n *)
(* Proof: by MOD_ADD_INV and group_linv_unique. *)
val Zadd_inv = store_thm(
  "Zadd_inv",
  ``!n x. 0 < n /\ x < n ==> ((Z n).inv x = (n - x) MOD n)``,
  rpt strip_tac >>
  `x IN (Z n).carrier /\ (n - x) MOD n IN (Z n).carrier` by rw_tac std_ss[Zadd_property] >>
  `((n - x) MOD n + x) MOD n = 0` by rw_tac std_ss[MOD_ADD_INV] >>
  metis_tac[Zadd_group, group_linv_unique, Zadd_property]);

(* Due to zDefine before, now export the Define to computeLib. *)

(* export simple result *)
val _ = export_rewrites ["Zadd_eval", "Zadd_inv"];
(*
- SIMP_CONV (srw_ss()) [] ``(Z 5).op 3 4``;
> val it = |- (Z 5).op 3 4 = 2 : thm
- SIMP_CONV (srw_ss()) [] ``(Z 5).inv 3``;
> val it = |- (Z 5).inv 3 = 2 : thm
*)

(* Now put these to computeLib *)
val _ = computeLib.add_persistent_funs ["Zadd_eval"];
(*
- EVAL ``(Z 5).op 3 4``;
> val it = |- (Z 5).op 3 4 = 2 : thm
- EVAL ``(Z 5).op 6 8``;
> val it = |- (Z 5).op 6 8 = 4 : thm
*)
(* val _ = computeLib.add_persistent_funs ["Zadd_inv"]; -- cannot put a non-function. *)

(* Theorem: As function, (Z n).inv x = (n - x) MOD n *)
(* Proof: by Zadd_inv. *)
val Zadd_inv_compute = store_thm(
  "Zadd_inv_compute",
  ``!n x. (Z n).inv x = if 0 < n /\ x < n then (n - x) MOD n else FAIL ((Z n).inv x) bad_element``,
  rw_tac std_ss[Zadd_inv, combinTheory.FAIL_DEF]);

val _ = computeLib.add_persistent_funs ["Zadd_inv_compute"];
val _ = computeLib.set_skip (computeLib.the_compset) ``combin$FAIL`` (SOME 0);

(*
- EVAL ``(Z 5).inv 2``;
> val it = |- (Z 5).inv 2 = 3 : thm
- EVAL ``(Z 5).inv 3``;
> val it = |- (Z 5).inv 3 = 2 : thm
- EVAL ``(Z 5).inv 6``;
> val it = |- (Z 5).inv 6 = FAIL ((Z 5).inv 6) bad_element : thm
*)


(* ------------------------------------------------------------------------- *)
(* The Group Z*p = Multiplication Modulo p, for prime p.                     *)
(* ------------------------------------------------------------------------- *)

(* Define Multiplicative Modulo p Group *)
val Zstar_def = zDefine`
  Zstar p : num group =
   <| carrier := residue p;
           id := 1;
       (* inv := MOD_MULT_INV p; *)
           op := (\i j. (i * j) MOD p)
    |>`;
(* Use of zDefine to avoid incorporating into computeLib, by default. *)
(* This is the same as mult_mod below, using { i | i <> 0 /\ i < p } as carrier. *)

(* Overload Zstar n *)
val _ = temp_overload_on("Z*", ``Zstar``);

(*
- type_of ``Z* p``;
> val it = ``:num group`` : hol_type
*)

(* Theorem: Evaluation of Zstar for each record field. *)
(* Proof: by Zstar_def. *)
val Zstar_eval = store_thm(
  "Zstar_eval",
  ``!p. ((Z* p).carrier = residue p) /\
       (!x y. (Z* p).op x y = (x * y) MOD p) /\
       ((Z* p).id = 1)``,
  rw_tac std_ss[Zstar_def]);
(* This is put to computeLib later, together with Zstar_inv_compute. *)

(* Theorem: x IN (Z* p).carrier ==> 0 < x /\ x < p *)
(* Proof: by definition. *)
val Zstar_element = store_thm(
  "Zstar_element",
  ``!p x. x IN (Z* p).carrier <=> 0 < x /\ x < p``,
  rw[Zstar_def, residue_def]);

(* Theorem: properties of Z* p. *)
(* Proof: by definition. *)
val Zstar_property = store_thm(
  "Zstar_property",
  ``!p. ((Z* p).carrier = residue p) /\
       ((Z* p).id = 1) /\
       (!x y. (Z* p).op x y = (x * y) MOD p) /\
       FINITE (Z* p).carrier /\
       (0 < p ==> (CARD (Z* p).carrier = p - 1))``,
  rw[Zstar_def, residue_finite, residue_card]);

(* Theorem: (Z* p).carrier = residue p *)
(* Proof: by Zstar_def. *)
Theorem Zstar_carrier:
  !p. (Z* p).carrier = residue p
Proof
  simp[Zstar_def]
QED

(* Theorem: (Z* p).carrier = {i | 0 < i /\ i < p} *)
(* Proof: by Zstar_carrier, residue_def. *)
Theorem Zstar_carrier_alt:
  !p. (Z* p).carrier = {i | 0 < i /\ i < p}
Proof
  simp[Zstar_carrier, residue_def, EXTENSION]
QED

(* Theorem: (Z* p).id = 1 *)
(* Proof: by Zstar_def. *)
Theorem Zstar_id:
  !p. (Z* p).id = 1
Proof
  simp[Zstar_def]
QED

(* Theorem: FINITE (Z* p).carrier *)
(* Proof: by Zstar_property *)
val Zstar_finite = store_thm(
  "Zstar_finite",
  ``!p. FINITE (Z* p).carrier``,
  rw[Zstar_property]);

(* Theorem: 0 < p ==> (CARD (Z* p).carrier = p - 1) *)
(* Proof: by Zstar_property *)
val Zstar_card = store_thm(
  "Zstar_card",
  ``!p. 0 < p ==> (CARD (Z* p).carrier = p - 1)``,
  rw[Zstar_property]);

(* Theorem: Z* p is a Group for prime p. *)
(* Proof: check definitions.
   Closure: 0 < (x * y) MOD p < p
      true by EUCLID_LEMMA and MOD_LESS.
   Associativity: ((x * y) MOD p * z) MOD p = (x * (y * z) MOD p) MOD p
      true by MOD_MULT_ASSOC.
   Inverse: ?y. (0 < y /\ y < p) /\ ((y * x) MOD p = 1)
      true by MOD_MULT_INV_DEF.
*)
val Zstar_group = store_thm(
  "Zstar_group",
  ``!p. prime p ==> Group (Z* p)``,
  rw_tac std_ss[group_def_alt, Zstar_property, residue_def, GSPECIFICATION, ONE_LT_PRIME] >| [
    `x MOD p <> 0 /\ y MOD p <> 0` by rw_tac arith_ss[] >>
    `(x * y) MOD p <> 0` by metis_tac[EUCLID_LEMMA] >>
    decide_tac,
    rw_tac arith_ss[],
    rw_tac std_ss[PRIME_POS, MOD_MULT_ASSOC],
    metis_tac[MOD_MULT_INV_DEF]
  ]);

(* Theorem: If p is prime, Z*p is a Finite Group. *)
(* Proof: by Zstar_group, FINITE (Z* p).carrier *)
val Zstar_finite_group = store_thm(
  "Zstar_finite_group",
  ``!p. prime p ==> FiniteGroup (Z* p)``,
  rw[FiniteGroup_def, Zstar_group, Zstar_property]);

(* Theorem: If p is prime, Z*p is a Finite Abelian Group. *)
(* Proof:
   Verify all finite Abelian group axioms for Z*p.
*)
val Zstar_finite_abelian_group = store_thm(
  "Zstar_finite_abelian_group",
  ``!p. prime p ==> FiniteAbelianGroup (Z* p)``,
  rw_tac std_ss[FiniteAbelianGroup_def, AbelianGroup_def, Zstar_property, residue_def, GSPECIFICATION] >-
  rw_tac std_ss[Zstar_group] >>
  rw_tac arith_ss[]);

(* Theorem: (Z* p).exp a n = a ** n MOD p *)
(* Proof:
   By induction on n.
   Base case: (Z* p).exp a 0 = a ** 0 MOD p
      (Z* p).exp a 0
    = (Z* p).id                   by group_exp_0
    = 1                           by Zstar_def
    = 1 MOD 1                     by DIVMOD_ID, 0 < 1
    = a ** 0 MOD p                by EXP
   Step case:  (Z* p).exp a n = a ** n MOD p ==> (Z* p).exp a (SUC n) = a ** SUC n MOD p
      (Z* p).exp a (SUC n)
    = a * ((Z* p).exp a n)     by group_exp_SUC
    = a * ((a ** n) MOD p)        by inductive hypothesis
    = (a MOD p) * ((a**n) MOD p)  by a < p, MOD_LESS
    = (a*(a**n)) MOD p            by MOD_TIMES2
    = (a**(SUC n) MOD p           by EXP
*)
val Zstar_exp = store_thm(
  "Zstar_exp",
  ``!p a. prime p /\ a IN (Z* p).carrier ==> !n. (Z* p).exp a n = (a ** n) MOD p``,
  rw[Zstar_def, monoid_exp_def, residue_def] >>
  `0 < p /\ 1 < p` by rw_tac std_ss[PRIME_POS, ONE_LT_PRIME] >>
  Induct_on `n` >-
  rw_tac std_ss[FUNPOW_0, EXP, ONE_MOD] >>
  rw_tac std_ss[FUNPOW_SUC, EXP] >>
  `a MOD p = a` by rw_tac arith_ss[] >>
  metis_tac[MOD_TIMES2]);

(*
- group_order_property |> ISPEC ``(Z* p)``;
> val it = |- FiniteGroup (Z* p) ==> !x. x IN (Z* p).carrier ==>
         0 < order (Z* p) x /\  ((Z* p).exp x (order (Z* p) x) = (Z* p).id) : thm
- EVAL ``order (Z* 5) 1``;
> val it = |- order (Z* 5) 1 = 1 : thm
- EVAL ``order (Z* 5) 2``;
> val it = |- order (Z* 5) 2 = 4 : thm
- EVAL ``order (Z* 5) 3``;
> val it = |- order (Z* 5) 3 = 4 : thm
- EVAL ``order (Z* 5) 4``;
> val it = |- order (Z* 5) 4 = 2 : thm
*)

(* Theorem: (Z* p).inv x = x ** (order (Z* p) x - 1) *)
(* Proof: by group_order_property and group_rinv_unique. *)
val Zstar_inv = store_thm(
  "Zstar_inv",
  ``!p. prime p ==> !x. 0 < x /\ x < p ==> ((Z* p).inv x = (Z* p).exp x (order (Z* p) x - 1))``,
  rpt strip_tac >>
  `x IN residue p` by rw_tac std_ss[residue_def, GSPECIFICATION] >>
  `x IN (Z* p).carrier /\ ((Z* p).id = 1)` by rw_tac std_ss[Zstar_property] >>
  `Group (Z* p)` by rw_tac std_ss[Zstar_group] >>
  `FiniteGroup (Z* p)` by rw_tac std_ss[FiniteGroup_def, Zstar_property] >>
  `0 < order (Z* p) x /\ ((Z* p).exp x (order (Z* p) x) = 1)` by rw_tac std_ss[group_order_property] >>
  `SUC ((order (Z* p) x) - 1) = order (Z* p) x` by rw_tac arith_ss[] >>
  metis_tac[group_rinv_unique, group_exp_SUC, group_exp_element]);

(* val _ = computeLib.add_persistent_funs ["Zstar_inv"]; -- cannot put a non-function. *)

(* Theorem: As function, (Z* p).inv x = x ** (order (Z* p) x - 1) *)
(* Proof: by Zstar_inv. *)
val Zstar_inv_compute = store_thm(
  "Zstar_inv_compute",
  ``!p x. (Z* p).inv x = if prime p /\ 0 < x /\ x < p then (Z* p).exp x (order (Z* p) x - 1)
                           else FAIL ((Z* p).inv x) bad_element``,
  rw_tac std_ss[Zstar_inv, combinTheory.FAIL_DEF]);

(* Now put thse input computeLib for EVAL *)
val _ = computeLib.add_persistent_funs ["Zstar_eval"];
val _ = computeLib.add_persistent_funs ["Zstar_inv_compute"];
val _ = computeLib.set_skip (computeLib.the_compset) ``combin$FAIL`` (SOME 0);

(*
- EVAL ``(Z* 5).op 3 2``;
> val it = |- (Z* 5).op 3 2 = 1 : thm
- EVAL ``(Z* 5).id``;
> val it = |- (Z* 5).id = 1 : thm
- EVAL ``(Z* 5).inv 2``;
> val it = |- (Z* 5).inv 2 = if prime 5 then 3 else FAIL ((Z* 5).inv 2) bad_element : thm
- EVAL ``prime 5``;
> val it = |- prime 5 <=> prime 5 : thm
*)

(* Export these for SIMP_CONV *)
val _ = export_rewrites ["Zstar_eval", "Zstar_inv"];

(*
- SIMP_CONV (srw_ss()) [] ``(Z* 5).op 3 2``;
> val it = |- (Z* 5).op 3 2 = 1 : thm
- SIMP_CONV (srw_ss()) [] ``(Z* 5).id``;
> val it = |- (Z* 5).id = 1 : thm
- SIMP_CONV (srw_ss()) [] ``(Z* 5).inv 2``;
! Uncaught exception:
! UNCHANGED
*)

(* ------------------------------------------------------------------------- *)
(* Euler's generalization of Modulo Multiplicative Group for any modulo n.   *)
(* ------------------------------------------------------------------------- *)

(* Define Multiplicative Modulo n Group *)
val Estar_def = zDefine`
  Estar n : num group =
   <| carrier := Euler n;
           id := 1;
      (*  inv := GCD_MOD_MULT_INV n; *)
           op := (\i j. (i * j) MOD n)
    |>`;

(*
- type_of ``Estar n``;
> val it = ``:num group`` : hol_type
*)

(* Theorem: Estar n =
       <|carrier := {i | 0 < i /\ i < n /\ coprime n i} ; id := 1; op := (\i j. (i * j) MOD n)|>*)
(* Proof: by Estar_def, Euler_def *)
val Estar_alt = store_thm(
  "Estar_alt",
  ``!n. Estar n =
       <|carrier := {i | 0 < i /\ i < n /\ coprime n i} ; id := 1; op := (\i j. (i * j) MOD n)|>``,
  rw[Estar_def, Euler_def]);

(* Theorem: Evaluation of Zstar for each record field. *)
(* Proof: by Etar_def. *)
val Estar_eval = store_thm(
  "Estar_eval[compute]",
  ``!n. ((Estar n).carrier = Euler n) /\
       (!x y. (Estar n).op x y = (x * y) MOD n) /\
       ((Estar n).id = 1)``,
  rw_tac std_ss[Estar_def]);
(* This is put to computeLib, later also Estar_inv_compute. *)

(* Theorem: x IN (Estar n).carrier <=> 0 < x /\ x < n /\ coprime n x *)
(* Proof: by Estar_def, Euler_def *)
val Estar_element = store_thm(
  "Estar_element",
  ``!n x. x IN (Estar n).carrier <=> 0 < x /\ x < n /\ coprime n x``,
  rw[Estar_def, Euler_def]);

(* Theorem: properties of (Estar n). *)
(* Proof: by definition. *)
val Estar_property = store_thm(
  "Estar_property",
  ``!n. ((Estar n).carrier = Euler n) /\
       ((Estar n).id = 1) /\
       (!x y. (Estar n).op x y = (x * y) MOD n) /\
       FINITE (Estar n).carrier /\
       (CARD (Estar n).carrier = totient n)``,
  rw_tac std_ss[Estar_def, totient_def] >>
  rw_tac std_ss[Euler_def] >>
  `{i | 0 < i /\ i < n /\ coprime n i} SUBSET count n` by rw[SUBSET_DEF] >>
  metis_tac[FINITE_COUNT, SUBSET_FINITE]);

(* Theorem: (Estar n).carrier = Euler n *)
(* Proof: by Estar_def. *)
Theorem Estar_carrier:
  !n. (Estar n).carrier = Euler n
Proof
  simp[Estar_def]
QED

(* Theorem: (Estar n).carrier = {i | 0 < i /\ i < n /\ coprime n i } *)
(* Proof: by Estar_carrier, Euler_def. *)
Theorem Estar_carrier_alt:
  !n. (Estar n).carrier = {i | 0 < i /\ i < n /\ coprime n i }
Proof
  simp[Estar_carrier, Euler_def, EXTENSION]
QED

(* Theorem: (Estar n).id = 1 *)
(* Proof: by Estar_def. *)
Theorem Estar_id:
  !n. (Estar n).id = 1
Proof
  simp[Estar_def]
QED

(* Theorem: FINITE (Estar n).carrier *)
(* Proof: by Estar_property *)
val Estar_finite = store_thm(
  "Estar_finite",
  ``!n. FINITE (Estar n).carrier``,
  rw[Estar_property]);

(* Theorem: CARD (Estar n).carrier = totient n *)
(* Proof: by Estar_property *)
val Estar_card = store_thm(
  "Estar_card",
  ``!n. CARD (Estar n).carrier = totient n``,
  rw[Estar_property]);

(* Theorem: CARD (Estar n).carrier = totient n *)
(* Proof: by Estar_card, phi_eq_totient *)
val Estar_card_alt = store_thm(
  "Estar_card_alt",
  ``!n. 1 < n ==> (CARD (Estar n).carrier = phi n)``,
  rw[Estar_card, phi_eq_totient]);

(* Theorem: Estar is a Group *)
(* Proof: check definitions.
   Closure: 1 < n /\ coprime n x /\ coprime n y ==> 0 < (x * y) MOD n < n
      true by MOD_NONZERO_WHEN_GCD_ONE, PRODUCT_WITH_GCD_ONE, MOD_LESS.
   Closure: 1 < n /\ coprime n x /\ coprime n y ==> coprime n ((x * y) MOD n
      true by MOD_WITH_GCD_ONE, PRODUCT_WITH_GCD_ONE.
   Associativity: ((x * y) MOD n * z) MOD n = (x * (y * z) MOD n) MOD n
      true by MOD_MULT_ASSOC.
   Inverse: 1 < n /\ coprime n x ==> ?y. (0 < y /\ y < n /\ coprime n y) /\ ((y * x) MOD n = 1)
      true by GEN_MULT_INV_DEF.
*)
val Estar_group = store_thm(
  "Estar_group",
  ``!n. 1 < n ==> Group (Estar n)``,
  rw_tac std_ss[group_def_alt, Estar_property, Euler_def, GSPECIFICATION, GCD_1] >-
  rw_tac std_ss[MOD_NONZERO_WHEN_GCD_ONE, PRODUCT_WITH_GCD_ONE] >-
  rw_tac arith_ss[] >-
  rw_tac std_ss[MOD_WITH_GCD_ONE, PRODUCT_WITH_GCD_ONE, ONE_LT_POS] >-
  rw_tac std_ss[MOD_MULT_ASSOC, ONE_LT_POS] >>
  metis_tac[GEN_MULT_INV_DEF]);

(* Theorem: Estar is a Finite Group *)
(* Proof: by Estar_group, FINITE (Estar n).carrier. *)
val Estar_finite_group = store_thm(
  "Estar_finite_group",
  ``!n. 1 < n ==> FiniteGroup (Estar n)``,
  rw[FiniteGroup_def, Estar_group, Estar_property]);

(* Theorem: Estar is a Finite Abelian Group *)
(* Proof: by checking definitions. *)
val Estar_finite_abelian_group = store_thm(
  "Estar_finite_abelian_group",
  ``!n. 1 < n ==> FiniteAbelianGroup (Estar n)``,
  rw_tac arith_ss [FiniteAbelianGroup_def, AbelianGroup_def, Estar_group, Estar_property]);

(* Theorem: (Estar n).exp a k = a ** k MOD n *)
(* Proof:
   By induction on k.
   Base case: (Estar n).exp a 0 = a ** 0 MOD n
     (Estar n).exp a 0
   = (Estar n).id                   by group_exp_0
   = 1                              by Estar_def
   = 1 MOD n                        by ONE_MOD
   = a ** 0 MOD n                   by EXP
   Step case: (Estar n).exp a k = a ** k MOD n ==> (Estar n).exp a (SUC k) = a ** SUC k MOD n
     (Estar n).exp a (SUC k)
   = a * (group_exp (Estar n) a k)  by group_exp_SUC
   = a * ((a ** k) MOD n)           by inductive hypothesis
   = (a MOD n) * ((a ** k) MOD n)   by a < n, MOD_LESS
   = (a * (a ** k)) MOD n           by MOD_TIMES2
   = (a ** (SUC k) MOD n            by EXP
*)
val Estar_exp = store_thm(
  "Estar_exp",
  ``!n a. 1 < n /\ a IN (Estar n).carrier ==> !k. (Estar n).exp a k = (a ** k) MOD n``,
  rpt strip_tac >>
  `Group (Estar n)` by rw_tac std_ss[Estar_group] >>
  `0 < n` by decide_tac >>
  Induct_on `k` >| [
    rw_tac std_ss[group_exp_0, EXP, Estar_def],
    rw_tac std_ss[group_exp_SUC, EXP, Estar_def] >>
    `!x. x IN (Estar n).carrier ==> (x MOD n = x)` by rw[Estar_def, Euler_def, residue_def] >>
    metis_tac[MOD_TIMES2]
  ]);

(* ------------------------------------------------------------------------- *)
(* Euler-Fermat Theorem.                                                     *)
(* ------------------------------------------------------------------------- *)

(* Theorem: For all a in Estar n, a ** (totient n) MOD n = 1 *)
(* Proof:
   Since FiniteAbelianGroup (Estar n)        by Estar_finite_abelian_group, 1 < n
     and a IN (Estar n).carrier              by Estar_property, Euler_element
     and (Estar n).id = 1                    by Estar_property
     and CARD (Estar n).carrier = totient n  by Estar_property
     and !k. (Estar n).exp k = a ** k MOD n  by Estar_exp
   Hence a ** (totient n) MOD n = 1          by finite_abelian_Fermat
*)
val Euler_Fermat_eqn = store_thm(
  "Euler_Fermat_eqn",
  ``!n a. 1 < n /\ a < n /\ coprime n a ==> (a ** (totient n) MOD n = 1)``,
  rpt strip_tac >>
  `0 < a` by metis_tac[GCD_0, NOT_ZERO, LESS_NOT_EQ] >>
  metis_tac[Estar_finite_abelian_group, Euler_element, Estar_property, finite_abelian_Fermat, Estar_exp]);

(* Theorem: 1 < n /\ coprime n a ==> (a ** (totient n) MOD n = 1) *)
(* Proof:
   Let b = a MOD n.
   Then b < n            by MOD_LESS, 0 < n
    and coprime n b      by coprime_mod, 0 < n
        a ** totient n MOD n
      = b ** totient n MOD n   by MOD_EXP
      = 1                      by Euler_Fermat_eqn
*)
val Euler_Fermat_thm = store_thm(
  "Euler_Fermat_thm",
  ``!n a. 1 < n /\ coprime n a ==> (a ** (totient n) MOD n = 1)``,
  rpt strip_tac >>
  qabbrev_tac `b = a MOD n` >>
  `b < n` by rw[Abbr`b`] >>
  `coprime n b` by rw[coprime_mod, Abbr`b`] >>
  `a ** totient n MOD n = b ** totient n MOD n` by rw[MOD_EXP, Abbr`b`] >>
  metis_tac[Euler_Fermat_eqn]);

(* Theorem: 1 < n /\ coprime a n ==> (a ** (totient n) MOD n = 1) *)
(* Proof: by Euler_Fermat_thm, GCD_SYM *)
val Euler_Fermat_alt = store_thm(
  "Euler_Fermat_alt",
  ``!n a. 1 < n /\ coprime a n ==> (a ** (totient n) MOD n = 1)``,
  rw[Euler_Fermat_thm, GCD_SYM]);

(* Theorem: For prime p, 0 < a < p ==> a ** (p - 1) MOD p = 1 *)
(* Proof
   Using Z* p:
   Given prime p, 0 < p                      by PRIME_POS
     ==> FiniteAbelianGroup (Z* p)           by Zstar_finite_abelian_group
     and 0 < a < p ==> a IN (Z* p).carrier   by Zstar_def, residue_def
     and CARD (Z* p).carrier = (p - 1)       by Zstar_property
     and !n. (Z* p).exp a n = a ** n MOD p   by Zstar_exp
   Hence a ** (p - 1) MOD p = 1              by finite_abelian_Fermat

   Using Euler_Fermat_thm:
   For prime p,  1 < p                   by ONE_LT_PRIME
       and  gcd p a = 1                  by prime_coprime_all_lt
   Hence  (a ** (totient p) MOD p = 1)   by Euler_Fermat_eqn, 1 < p
   or      a ** (p-1) MOD p = 1          by Euler_card_prime
*)
val Fermat_little_thm = store_thm(
  "Fermat_little_thm",
  ``!p a. prime p /\ 0 < a /\ a < p ==> (a ** (p - 1) MOD p = 1)``,
  rw[ONE_LT_PRIME, prime_coprime_all_lt, Euler_Fermat_eqn, GSYM Euler_card_prime]);

(* Theorem: prime p ==> (a ** p MOD p = a MOD p) *)
(* Proof:
   Note 0 < p             by PRIME_POS
     so p = SUC (p - 1)   by arithmetic
   Let b = a MOD p.
   Then b ** p MOD p = a ** p MOD p    by MOD_EXP, 0 < p
   Thus the goal is: b ** p MOD p = b.
   If b = 0,
        0 ** p MOD p
      = 0 MOD p                        by ZERO_EXP
      = 0                              by ZERO_MOD
   If b <> 0,
      Then 0 < b /\ b < p              by MOD_LESS, 0 < p
        b ** p MOD p
      = (b ** (SUC (p - 1))) MOD p     by above
      = (b * b ** (p - 1)) MOD p       by EXP
      = ((b MOD p) * (b ** (p - 1) MOD p)) MOD p
                                       by MOD_TIMES2
      = ((b MOD p) * 1) MOD p          by Fermat_little_thm
      = b MOD p MOD p                  by MULT_RIGHT_1
      = b MOD p                        by MOD_MOD
      = a MOD p                        by MOD_MOD
      = b                              by notation
*)
val Fermat_little_eqn = store_thm(
  "Fermat_little_eqn",
  ``!p a. prime p ==> (a ** p MOD p = a MOD p)``,
  rpt strip_tac >>
  `0 < p` by rw[PRIME_POS] >>
  qabbrev_tac `b = a MOD p` >>
  `b < p` by rw[Abbr`b`] >>
  `b ** p MOD p = b` suffices_by rw[MOD_EXP, Abbr`b`] >>
  Cases_on `b = 0` >-
  metis_tac[ZERO_EXP, ZERO_MOD, NOT_ZERO_LT_ZERO] >>
  `0 < b` by decide_tac >>
  `b ** (p - 1) MOD p = 1` by rw[Fermat_little_thm] >>
  `p = SUC (p - 1)` by decide_tac >>
  metis_tac[EXP, MOD_TIMES2, MOD_MOD, MULT_RIGHT_1]);

(* Theorem: 1 < n /\ a < n /\ coprime n a ==>
           ((Estar n).inv a = a ** ((totient n) - 1) MOD n) *)
(* Proof:
   Note Group (Estar n)            by Estar_group, 1 < n
    and 0 < a                      by GCD_0, n <> 1
    and a IN (Estar n).carrier     by Estar_element
   Let b = a ** ((totient n) - 1) MOD n.
   The goal becomes: (Estar n).inv a = b.

   Note b = (Estar n).exp a ((totient n) - 1)      by Estar_exp
   Thus b IN (Estar n).carrier                     by group_exp_element
        (Estar n).op a b
      = (a * a ** ((totient n) - 1) MOD n) MOD n   by Estar_property
      = (a * a ** (totient n - 1)) MOD n           by LESS_MOD, MOD_TIMES2, 0 < n
      = (a ** SUC (totient n - 1)) MOD n           by EXP
      = (a ** totient n) MOD n                     by 0 < totient n from Euler_card_bounds
      = 1                                          by Euler_Fermat_eqn
      = (Estar n).id                               by Estar_property
   Therefore b = (Estar n).inv a                   by group_rinv_unique
*)
val Estar_inv = store_thm(
  "Estar_inv",
  ``!n a. 1 < n /\ a < n /\ coprime n a ==>
      ((Estar n).inv a = a ** ((totient n) - 1) MOD n)``,
  rpt strip_tac >>
  `Group (Estar n)` by rw_tac std_ss[Estar_group] >>
  `0 < a` by metis_tac[GCD_0, NOT_ZERO, LESS_NOT_EQ] >>
  `a IN (Estar n).carrier` by rw_tac std_ss[Estar_element] >>
  qabbrev_tac `b = a ** ((totient n) - 1) MOD n` >>
  `b = (Estar n).exp a ((totient n) - 1)` by rw[Estar_exp, Abbr`b`] >>
  `b IN (Estar n).carrier` by rw[] >>
  `(Estar n).op a b = (Estar n).id` by
  (`(Estar n).id = 1` by rw[Estar_property] >>
  `(Estar n).op a b = (a * a ** ((totient n) - 1) MOD n) MOD n` by rw[Estar_property, Abbr`b`] >>
  `_ = (a * a ** (totient n - 1)) MOD n` by metis_tac[LESS_MOD, MOD_TIMES2, ONE_LT_POS] >>
  `_ = (a ** SUC (totient n - 1)) MOD n` by rw[EXP] >>
  `0 < totient n` by rw[Euler_card_bounds] >>
  `SUC (totient n - 1) = totient n` by decide_tac >>
  rw[Euler_Fermat_eqn]) >>
  metis_tac[group_rinv_unique]);

(* Theorem: As function, (Estar n).inv a = a ** (totient n - 1) MOD n) *)
(* Proof: by Estar_inv. *)
val Estar_inv_compute = store_thm(
  "Estar_inv_compute[compute]",
  ``!n a. (Estar n).inv a = if 1 < n /\ a < n /\ coprime n a
                           then a ** ((totient n) - 1) MOD n
                           else FAIL ((Estar n).inv a) bad_element``,
  rw_tac std_ss[Estar_inv, combinTheory.FAIL_DEF]);
(* put in computeLib for Estar inverse computation *)

(*
> EVAL ``(Estar 10).inv 3``;
val it = |- (Estar 10).inv 3 = 7: thm
*)

(* ------------------------------------------------------------------------- *)
(* The following is a rework from Hol/examples/elliptic/groupScript.sml      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The Trivial Group.                                                        *)
(* ------------------------------------------------------------------------- *)

(* The trivial group: {#e} *)
val trivial_group_def = zDefine`
  trivial_group e : 'a group =
   <| carrier := {e};
           id := e;
       (* inv := (\x. e);  *)
           op := (\x y. e)
    |>`;

(*
- type_of ``trivial_group e``;
> val it = ``:'a group`` : hol_type
*)

(* Theorem: (trivial_group e).carrier = {e} *)
(* Proof: by trivial_group_def. *)
Theorem trivial_group_carrier:
  !e. (trivial_group e).carrier = {e}
Proof
  simp[trivial_group_def]
QED

(* Theorem: (trivial_group e).id = e *)
(* Proof: by trivial_group_def. *)
Theorem trivial_group_id:
  !e. (trivial_group e).id = e
Proof
  simp[trivial_group_def]
QED

(* Theorem: {#e} is indeed a group *)
(* Proof: check by definition. *)
val trivial_group = store_thm(
  "trivial_group",
  ``!e. FiniteAbelianGroup (trivial_group e)``,
  rw_tac std_ss[trivial_group_def, FiniteAbelianGroup_def, FiniteGroup_def, AbelianGroup_def, group_def_alt, IN_SING, FINITE_SING, GSPECIFICATION]);

(* ------------------------------------------------------------------------- *)
(* The Function Cyclic Group.                                                *)
(* ------------------------------------------------------------------------- *)

(* Cyclic group of f and e
   = all FUNPOW f by a generator e
   = {e, f e, f f e, f f f e, ... }
*)

val fn_cyclic_group_def = zDefine`
    fn_cyclic_group e f : 'a group =
   <| carrier := { x | ?n. FUNPOW f n e = x };
           id := e; (* Note: next comment must be in one line *)
      (*  inv := (\x. @y. ?yi. (FUNPOW f yi e = y) /\ (!xi. (FUNPOW f xi e = x) ==> (FUNPOW f (xi + yi) e = e)));  *)
           op := (\x y. @z. !xi yi.
                   (FUNPOW f xi e = x) /\ (FUNPOW f yi e = y) ==>
                   (FUNPOW f (xi + yi) e = z))
    |>`;

(*
- type_of ``fn_cyclic_group e f``;
> val it = ``:'a group`` : hol_type
*)

(* Original:

val fn_cyclic_group_def = Define
  `fn_cyclic_group e f : 'a group =
   <| carrier := { x | ?n. FUNPOW f n e = x };
      id := e;
      inv := (\x. @y. ?yi. !xi.
                (FUNPOW f yi e = y) /\
                ((FUNPOW f xi e = x) ==> (FUNPOW f (xi + yi) e = e)));
      mult := (\x y. @z. !xi yi.
                (FUNPOW f xi e = x) /\ (FUNPOW f yi e = y) ==>
                (FUNPOW f (xi + yi) e = z)) |>`;

*)

(* Theorem: alternative characterization of cyclic group:
   If there exists a period k: k <> 0 /\ FUNPOW f k e = e
   Let order n = LEAST such k, then:
   (1) (fn_cyclic_group e f).carrier = { FUNPOW f k e | k < n }
   (2) (fn_cyclic_group e f).id = e)
   (3) !i. (fn_cyclic_group e f).inv (FUNPOW f i e) = FUNPOW f ((n - i MOD n) MOD n) e
   (4) !i j. (fn_cyclic_group e f).op (FUNPOW f i e) (FUNPOW f j e) = FUNPOW f ((i + j) MOD n) e
*)
(* Proof:
   Expand by fn_cyclic_group_def, this is to show:
   (1) 0 < h /\ FUNPOW f h e = e ==> ?k. (FUNPOW f n e = FUNPOW f k e) /\ k < h
       Since (n MOD h) < h                         by MOD_LESS
         and FUNPOW f n e = FUNPOW f (n MOD h) e   by FUNPOW_MOD, 0 < h
       So take k = n MOD h will satisfy the requirements.
   (2) ?n. FUNPOW f n e = FUNPOW f k e
       Just take n = k.
   (3) (@z. !xi yi. (FUNPOW f xi e = FUNPOW f i e) /\ (FUNPOW f yi e = FUNPOW f j e) ==>
                    (FUNPOW f (xi + yi) e = z)) = FUNPOW f ((i + j) MOD h) e
       This comes down to show:
       (1) ?z. !xi yi. (FUNPOW f xi e = FUNPOW f i e) /\ (FUNPOW f yi e = FUNPOW f j e) ==>
                       (FUNPOW f (xi + yi) e = z)
           Let z = FUNPOW f (i + j) e,
           the goal simplifies to: FUNPOW f (xi + yi) e = FUNPOW f (i + j) e
             FUNPOW f (xi + yi) e
           = FUNPOW f xi (FUNPOW f yi e)     by FUNPOW_ADD
           = FUNPOW f xi (FUNPOW f j e)      by given
           = FUNPOW f (xi + j) e             by FUNPOW_ADD
           = FUNPOW f (j + xi) e             by ADD_COMM
           = FUNPOW f j (FUNPOW f xi e)      by FUNPOW_ADD
           = FUNPOW f j (FUNPOW f i e)       by given
           = FUNPOW f (j + i) e              by FUNPOW_ADD
           = FUNPOW f (i + j) e              by ADD_COMM
       (2) z = FUNPOW f ((i + j) MOD h) e
           That is, FUNPOW f (i + j) e = FUNPOW f ((i + j) MOD h) e
           which is true by FUNPOW_MOD
*)
val fn_cyclic_group_alt = store_thm(
  "fn_cyclic_group_alt",
  ``!e f n.
     (?k. k <> 0 /\ (FUNPOW f k e = e)) /\
     (n = LEAST k. k <> 0 /\ (FUNPOW f k e = e)) ==>
     ((fn_cyclic_group e f).carrier = { FUNPOW f k e | k < n }) /\
     ((fn_cyclic_group e f).id = e) /\
  (* (!i. (fn_cyclic_group e f).inv (FUNPOW f i e) = FUNPOW f ((n - i MOD n) MOD n) e) /\ *)
     (!i j. (fn_cyclic_group e f).op (FUNPOW f i e) (FUNPOW f j e) = FUNPOW f ((i + j) MOD n) e)``,
  rpt gen_tac >>
  simp_tac std_ss [whileTheory.LEAST_EXISTS] >>
  Q.SPEC_TAC (`LEAST k. k <> 0 /\ (FUNPOW f k e = e)`,`h`) >>
  gen_tac >>
  strip_tac >>
  `0 < h` by decide_tac >>
  rw[fn_cyclic_group_def, EXTENSION, EQ_IMP_THM] >-
  metis_tac[FUNPOW_MOD, MOD_LESS] >-
  metis_tac[] >>
  normalForms.SELECT_TAC >>
  match_mp_tac (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``) >>
  conj_tac >| [
    qexists_tac `FUNPOW f (i + j) e` >>
    rw[] >>
    metis_tac[FUNPOW_ADD, ADD_COMM],
    rw[] >>
    metis_tac[FUNPOW_MOD]
  ]);

(* Theorem: (fn_cyclic_group e f).carrier = { x | ?n. FUNPOW f n e = x } *)
(* Proof: by fn_cyclic_group_def. *)
Theorem fn_cyclic_group_carrier:
  !e f. (fn_cyclic_group e f).carrier = { x | ?n. FUNPOW f n e = x }
Proof
  simp[fn_cyclic_group_def]
QED

(* Theorem: (fn_cyclic_group e f).id = e *)
(* Proof: by fn_cyclic_group_def. *)
Theorem fn_cyclic_group_id:
  !e f. (fn_cyclic_group e f).id = e
Proof
  simp[fn_cyclic_group_def]
QED

(* Theorem: Group (fn_cyclic_group e f) *)
(* Proof:
   By fn_cyclic_group_alt and group_def_alt.
   This comes down to 2 goals:
   (1) ?n. n <> 0 /\ (FUNPOW f n e = e) ==>
       (?k. k <> 0 /\ (FUNPOW f k e = e)) /\ ((LEAST n. n <> 0 /\ (FUNPOW f n e = e)) =
       LEAST k. k <> 0 /\ (FUNPOW f k e = e))
       This is trivially true.
   (2) Group (fn_cyclic_group e f)
       By group_def_alt, this is to show:
       (1) ?k''. (FUNPOW f ((k + k') MOD h) e = FUNPOW f k'' e) /\ k'' < h
           Let k'' = (k + k') MOD h, this is true by MOD_LESS
       (2) FUNPOW f (((k + k') MOD h + k'') MOD h) e = FUNPOW f ((k + (k' + k'') MOD h) MOD h) e
             ((k + k') MOD h + k'') MOD h
           = ((k + k') MOD h + k'' MOD h) MOD h   by LESS_MOD
           = (k + k' + k'') MOD h                 by MOD_PLUS
           = (k + (k' + k'')) MOD h               by ADD_ASSOC
           = (k MOD h + (k' + k'') MOD h) MOD h   by MOD_PLUS
           = (k + (k' + k'') MOD h) MOD h         by LESS_MOD
       (3) ?k. (e = FUNPOW f k e) /\ k < h
           Take k = 0, then FUNPOW f 0 e = e      by FUNPOW_0
       (4) (fn_cyclic_group e f).op e (FUNPOW f k e) = FUNPOW f k e
           With FUNPOW f 0 e = e                  by FUNPOW_0
            and the given, this is to show:
            FUNPOW f ((0 + k) MOD h) e = FUNPOW f k e
            But (0 + k) MOD h = k MOD h = k       by LESS_MOD
       (5) ?y. (?k. (y = FUNPOW f k e) /\ k < h) /\ ((fn_cyclic_group e f).op y (FUNPOW f k e) = e)
           Let y = FUNPOW f ((h - k) MOD h) e. This is to show:
           (1) ?k'. (FUNPOW f ((h - k) MOD h) e = FUNPOW f k' e) /\ k' < h
               Take k' = (h - k) MOD h < h        by MOD_LESS
           (2) FUNPOW f (((h - k) MOD h + k) MOD h) e = e
                 ((h - k) MOD h + k) MOD h
               = ((h - k) MOD h + (k MOD h)) MOD h   by LESS_MOD
               = (h - k + k) MOD h                   by MOD_PLUS
               = h MOD h                             by arithmetic
               = 0                                   by DIVMOD_ID
               Thus true since FUNPOW f 0 e = e      by FUNPOW_0
*)
val fn_cyclic_group_group = store_thm(
  "fn_cyclic_group_group",
  ``!e f. (?n. n <> 0 /\ (FUNPOW f n e = e)) ==> Group (fn_cyclic_group e f)``,
  rpt gen_tac >>
  disch_then assume_tac >>
  mp_tac (Q.SPECL [`e`,`f`,`LEAST n. n <> 0 /\ (FUNPOW f n e = e)`] fn_cyclic_group_alt) >>
  match_mp_tac (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``) >>
  conj_tac >-
  rw[] >>
  pop_assum mp_tac >>
  simp_tac std_ss [whileTheory.LEAST_EXISTS] >>
  qspec_tac (`LEAST n. n <> 0 /\ (FUNPOW f n e = e)`,`h`) >>
  gen_tac >>
  rpt strip_tac >>
  `0 < h` by decide_tac >>
  rw[group_def_alt] >| [
    rw_tac std_ss[] >>
    qexists_tac `(k + k') MOD h` >>
    metis_tac[MOD_LESS],
    rw_tac std_ss[] >>
    metis_tac[ADD_ASSOC, MOD_PLUS, LESS_MOD],
    metis_tac[FUNPOW_0],
    metis_tac[FUNPOW_0, ADD_CLAUSES, LESS_MOD],
    qexists_tac `FUNPOW f ((h - k) MOD h) e` >>
    rw_tac std_ss[] >-
    metis_tac[MOD_LESS] >>
    metis_tac[LESS_MOD, MOD_PLUS, SUB_ADD, LESS_IMP_LESS_OR_EQ, DIVMOD_ID, FUNPOW_0]
  ]);

(* Theorem: FiniteAbelianGroup (fn_cyclic_group e f) *)
(* Proof:
   Use fn_cyclic_group_alt due to assumption: (?n. n <> 0 /\ (FUNPOW f n e = e))
   By fn_cyclic_group_alt, this comes down to 2 goals:
   (1) ?n. n <> 0 /\ (FUNPOW f n e = e) ==>
       (?k. k <> 0 /\ (FUNPOW f k e = e)) /\ ((LEAST n. n <> 0 /\ (FUNPOW f n e = e)) =
       LEAST k. k <> 0 /\ (FUNPOW f k e = e))
       This is trivially true.
   (2) expand by FiniteAbelianGroup_def, AbelianGroup_def, the goals are:
       (1) Group (fn_cyclic_group e f), true by fn_cyclic_group_group.
       (2) FUNPOW f ((k + k') MOD h) e = FUNPOW f ((k' + k) MOD h) e, true by ADD_COMM
       (3) FINITE {FUNPOW f k e | k < h}, true by FINITE_COUNT_IMAGE
*)
val fn_cyclic_group_finite_abelian_group = store_thm(
  "fn_cyclic_group_finite_abelian_group",
  ``!e f. (?n. n <> 0 /\ (FUNPOW f n e = e)) ==> FiniteAbelianGroup (fn_cyclic_group e f)``,
  rpt gen_tac >>
  (disch_then assume_tac) >>
  mp_tac (Q.SPECL [`e`,`f`,`LEAST n. n <> 0 /\ (FUNPOW f n e = e)`] fn_cyclic_group_alt) >>
  match_mp_tac (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``) >>
  conj_tac >| [
    rw[],
    pop_assum mp_tac >>
    simp_tac std_ss [whileTheory.LEAST_EXISTS] >>
    Q.SPEC_TAC (`LEAST n. n <> 0 /\ (FUNPOW f n e = e)`,`h`) >>
    gen_tac >>
    strip_tac >>
    `0 < h` by decide_tac >>
    strip_tac >>
    rw[FiniteAbelianGroup_def, AbelianGroup_def] >| [
      metis_tac[fn_cyclic_group_group],
      rw_tac std_ss[ADD_COMM],
      rw_tac std_ss[FINITE_COUNT_IMAGE]
    ]
  ]);

(* Theorem: FiniteGroup (fn_cyclic_group e f) *)
(* Proof: by fn_cyclic_group_finite_abelian_group. *)
val fn_cyclic_group_finite_group = store_thm(
  "fn_cyclic_group_finite_group",
  ``!e f. (?n. n <> 0 /\ (FUNPOW f n e = e)) ==> FiniteGroup (fn_cyclic_group e f)``,
  metis_tac[fn_cyclic_group_finite_abelian_group, FiniteAbelianGroup_def, AbelianGroup_def, FiniteGroup_def]);

(* ------------------------------------------------------------------------- *)
(* The Group of Addition Modulo n.                                           *)
(* ------------------------------------------------------------------------- *)

(* Additive Modulo Group *)
val add_mod_def = zDefine`
  add_mod n : num group =
   <| carrier := { i | i < n };
           id := 0;
       (* inv := (\i. (n - i) MOD n); *)
           op := (\i j. (i + j) MOD n)
    |>
`;
(* This group, with modulus n, is taken as the additive group in ZN ring later. *)
(* Evaluation is given later in add_mod_eval and add_mod_inv. *)

(*
- type_of ``add_mod n``;
> val it = ``:num group`` : hol_type
*)

(* Theorem: add_mod evaluation. *)
(* Proof: by add_mod_def. *)
val add_mod_eval = store_thm(
  "add_mod_eval",
  ``!n. ((add_mod n).carrier = {i | i < n}) /\
       (!x y. (add_mod n).op x y = (x + y) MOD n) /\
       ((add_mod n).id = 0)``,
  rw_tac std_ss[add_mod_def]);

(* Now put these to computeLib *)
val _ = computeLib.add_persistent_funs ["add_mod_eval"];
(*
- EVAL ``(add_mod 5).id``;
> val it = |- (add_mod 5).id = 0 : thm
- EVAL ``(add_mod 5).op 3 4``;
> val it = |- (add_mod 5).op 3 4 = 2 : thm
- EVAL ``(add_mod 5).op 6 8``;
> val it = |- (add_mod 5).op 6 8 = 4 : thm
*)
(* Later put add_mod_inv_compute in computeLib. *)

(* Theorem: x IN (add_mod n).carrier <=> x < n *)
(* Proof: by add_mod_def *)
val add_mod_element = store_thm(
  "add_mod_element",
  ``!n x. x IN (add_mod n).carrier <=> x < n``,
  rw[add_mod_def]);

(* Theorem: properties of (add_mod n) *)
(* Proof: by definition. *)
val add_mod_property = store_thm(
  "add_mod_property",
  ``!n. (!x. x IN (add_mod n).carrier <=> x < n) /\
       ((add_mod n).id = 0) /\
       (!x y. (add_mod n).op x y = (x + y) MOD n) /\
       FINITE (add_mod n).carrier /\
       (CARD (add_mod n).carrier = n)``,
  rw_tac std_ss[add_mod_def, GSYM count_def, FINITE_COUNT, CARD_COUNT, IN_COUNT]);

(* Theorem: (add_mod n).carrier = { i | i < n } *)
(* Proof: by add_mod_def. *)
Theorem add_mod_carrier:
  !n. (add_mod n).carrier = { i | i < n }
Proof
  simp[add_mod_def]
QED

(* Theorem: (add_mod n).carrier = count n *)
(* Proof: by add_mod_def. *)
Theorem add_mod_carrier_alt:
  !n. (add_mod n).carrier = count n
Proof
  simp[add_mod_def, EXTENSION]
QED

(* Theorem: (add_mod n).id = 0 *)
(* Proof: by add_mod_def. *)
Theorem add_mod_id:
  !n. (add_mod n).id = 0
Proof
  simp[add_mod_def]
QED

(* Theorem: FINITE (add_mod n).carrier *)
(* Proof: by add_mod_property *)
val add_mod_finite = store_thm(
  "add_mod_finite",
  ``!n. FINITE (add_mod n).carrier``,
  rw[add_mod_property]);

(* Theorem: CARD (add_mod n).carrier = n *)
(* Proof: by add_mod_property *)
val add_mod_card = store_thm(
  "add_mod_card",
  ``!n. CARD (add_mod n).carrier = n``,
  rw[add_mod_property]);

(* Theorem: Additive Modulo Group is a group. *)
(* Proof: check group definitions.
   For associativity,
   to show: x < n /\ y < n /\ z < n ==> ((x + y) MOD n + z) MOD n = (x + (y + z) MOD n) MOD n
   LHS = ((x + y) MOD n + z) MOD n
       = ((x + y) MOD n + z MOD n) MOD n    by LESS_MOD
       = (x + y + z) MOD n                  by MOD_PLUS
       = (x + (y + z)) MOD n                by ADD_ASSOC
       = (x MOD n + (y + z) MOD n) MOD n    by MOD_PLUS
       = (x + (y + z) MOD n) MOD n          by LESS_MOD
       = RHS
   For additive inverse,
   to show: x < n ==> ?y. y < n /\ ((y + x) MOD n = 0)
   If x = 0, take y = 0.        (0 + 0) MOD n = 0 MOD n = 0  by ZERO_MOD
   If x <> 0, take y = n-x. (n - x + x) MOD n = n MOD n = 0  by DIVMOD_ID
*)
val add_mod_group = store_thm(
  "add_mod_group",
  ``!n. 0 < n ==> Group (add_mod n)``,
  rw_tac std_ss[group_def_alt, add_mod_property] >| [
    metis_tac[LESS_MOD, MOD_PLUS, ADD_ASSOC],
    Cases_on `x = 0` >| [
      metis_tac[ZERO_MOD, ADD],
      metis_tac[DIVMOD_ID, DECIDE ``x <> 0 /\ x < n ==> n - x < n /\ (n - x + x = n)``]
    ]
  ]);

(* Theorem: Additive Modulo Group is an Abelian group. *)
(* Proof: by add_mod_group and ADD_COMM. *)
val add_mod_abelian_group = store_thm(
  "add_mod_abelian_group",
  ``!n. 0 < n ==> AbelianGroup (add_mod n)``,
  rw_tac std_ss[AbelianGroup_def, add_mod_group, add_mod_property, ADD_COMM]);

(* Theorem: Additive Modulo Group is a Finite Group. *)
(* Proof: by add_mod_group and add_mod_property. *)
val add_mod_finite_group = store_thm(
  "add_mod_finite_group",
  ``!n. 0 < n ==> FiniteGroup (add_mod n)``,
  rw_tac std_ss[FiniteGroup_def, add_mod_group, add_mod_property]);

(* Theorem: Additive Modulo Group is a Finite Abelian Group. *)
(* Proof: by add_mod_abelian_group and add_mod_property. *)
val add_mod_finite_abelian_group = store_thm(
  "add_mod_finite_abelian_group",
  ``!n. 0 < n ==> FiniteAbelianGroup (add_mod n)``,
  rw_tac std_ss[FiniteAbelianGroup_def, add_mod_abelian_group, add_mod_property]);

(* Theorem: 0 < n ==> !x m. (add_mod n).exp x m = (x * m) MOD n *)
(* Proof:
   By induction on m:
   Base case: (add_mod n).exp x 0 = (x * 0) MOD n
         (add_mod n).exp x 0
       = (add_mod n).id            by group_exp_0
       = 0                         by add_mod_property
       = 0 MOD n                   by ZERO_MOD, 0 < n
       = (x * 0) MOD n             by MULT_0
   Step case: (add_mod n).exp x m = (x * m) MOD n ==>
              (add_mod n).exp x (SUC m) = (x * SUC m) MOD n
         (add_mod n).exp x (SUC m)
       = (add_mod n).op x ((add_mod n).exp x m)   by group_exp_SUC
       = (add_mod n).op x ((x * m) MOD n)         by induction hypothesis
       = (x + ((x * m) MOD n)) MOD n              by add_mod_property
       = (x + x * m) MOD n                        by MOD_PLUS, MOD_MOD
       = (x * SUC m) MOD n                        by MULT_SUC
*)
val add_mod_exp = store_thm(
  "add_mod_exp",
  ``!n. 0 < n ==> !x m. (add_mod n).exp x m = (x * m) MOD n``,
  rpt strip_tac >>
  Induct_on `m` >-
  rw[add_mod_property] >>
  rw_tac std_ss[group_exp_SUC, add_mod_property] >>
  metis_tac[MOD_PLUS, MOD_MOD, MULT_SUC]);

(* Theorem: (add_mod n).inv x = (n - x) MOD n *)
(* Proof: by MOD_ADD_INV and group_linv_unique. *)
val add_mod_inv = store_thm(
  "add_mod_inv",
  ``!n x. 0 < n /\ x < n ==> ((add_mod n).inv x = (n - x) MOD n)``,
  rpt strip_tac >>
  `x IN (add_mod n).carrier /\ (n - x) MOD n IN (add_mod n).carrier` by rw_tac std_ss[add_mod_property] >>
  `((n - x) MOD n + x) MOD n = 0` by rw_tac std_ss[MOD_ADD_INV] >>
  metis_tac[add_mod_group, group_linv_unique, add_mod_property]);

(* Theorem: (add_mod n).inv x = (n - x) MOD n as function *)
(* Proof: by add_mod_inv. *)
val add_mod_inv_compute = store_thm(
  "add_mod_inv_compute",
  ``!n x. (add_mod n).inv x = if 0 < n /\ x < n then (n - x) MOD n else FAIL ((add_mod n).inv x) bad_element``,
  rw_tac std_ss[add_mod_inv, combinTheory.FAIL_DEF]);

(* val _ = computeLib.add_persistent_funs ["add_mod_inv"]; -- cannot put a non-function. *)

(* Function can be put to computeLib *)
val _ = computeLib.add_persistent_funs ["add_mod_inv_compute"];
(* val _ = computeLib.set_skip (computeLib.the_compset) ``combin$FAIL`` (SOME 0); *)

(*
- EVAL ``(add_mod 5).inv 3``;
> val it = |- (add_mod 5).inv 3 = 2 : thm
- EVAL ``(add_mod 5).inv 7``;
> val it = |- (add_mod 5).inv 7 = FAIL ((add_mod 5).inv 7) bad_element : thm
*)

val _ = export_rewrites ["add_mod_eval", "add_mod_inv"];
(*
- SIMP_CONV (srw_ss()) [] ``(add_mod 5).op 3 4``;
> val it = |- (add_mod 5).op 3 4 = 2 : thm
- SIMP_CONV (srw_ss()) [] ``(add_mod 5).id``;
> val it = |- (add_mod 5).id = 0 : thm
- SIMP_CONV (srw_ss()) [] ``(add_mod 5).inv 2``;
> val it = |- (add_mod 5).inv 2 = 3 : thm
*)

(* ------------------------------------------------------------------------- *)
(* The Group of Multiplication Modulo prime p.                               *)
(* ------------------------------------------------------------------------- *)

(* Multiplicative Modulo Group *)
(* This version relies on fermat_little from pure Number Theory! *)
(*
val mult_mod_def = zDefine
  `mult_mod p =
   <| carrier := { i | i <> 0 /\ i < p };
           id := 1;
          inv := (\i. i ** (p - 2) MOD p);
         mult := (\i j. (i * j) MOD p)
    |>`;
*)

(* This version relies on MOD_MULT_INV, using LINEAR_GCD. *)
val mult_mod_def = zDefine`
  mult_mod p : num group =
   <| carrier := { i | i <> 0 /\ i < p };
           id := 1;
       (* inv := (\i. MOD_MULT_INV p i); *)
           op := (\i j. (i * j) MOD p)
    |>
`;
(* This group, with prime modulus, is not used in ZN ring later. *)
(* Evaluation is given later in mult_mod_eval and mult_mod_inv. *)

(*
- type_of ``mult_mod p``;
> val it = ``:num group`` : hol_type
*)

(* Theorem: x IN (mult_mod p).carrier <=> x <> 0 /\ x < p *)
(* Proof: by mult_mod_def *)
val mult_mod_element = store_thm(
  "mult_mod_element",
  ``!p x. x IN (mult_mod p).carrier <=> x <> 0 /\ x < p``,
  rw[mult_mod_def]);

(* Theorem: x IN (mult_mod p).carrier <=> 0 < x /\ x < p *)
(* Proof: by mult_mod_def *)
val mult_mod_element_alt = store_thm(
  "mult_mod_element_alt",
  ``!p x. x IN (mult_mod p).carrier <=> 0 < x /\ x < p``,
  rw[mult_mod_def]);

(* Theorem: properties of (mult_mod p) *)
(* Proof: by definition. *)
val mult_mod_property = store_thm(
  "mult_mod_property",
  ``!p. (!x. x IN (mult_mod p).carrier ==> x <> 0) /\
       (!x. x IN (mult_mod p).carrier <=> 0 < x /\ x < p) /\
       ((mult_mod p).id = 1) /\
       (!x y. (mult_mod p).op x y = (x * y) MOD p) /\
       FINITE (mult_mod p).carrier /\
       (0 < p ==> (CARD (mult_mod p).carrier = p - 1))``,
  rw_tac std_ss[mult_mod_def, GSPECIFICATION, NOT_ZERO_LT_ZERO] >-
  metis_tac[residue_def, residue_finite] >>
  metis_tac[residue_def, residue_card]);

(* Theorem: (mult_mod p).carrier = { i | i <> 0 /\ i < p } *)
(* Proof: by mult_mod_def. *)
Theorem mult_mod_carrier:
  !p. (mult_mod p).carrier = { i | i <> 0 /\ i < p }
Proof
  simp[mult_mod_def]
QED

(* Theorem: (mult_mod p).carrier = residue p *)
(* Proof: by mult_mod_def, residue_def. *)
Theorem mult_mod_carrier_alt:
  !p. (mult_mod p).carrier = residue p
Proof
  simp[mult_mod_def, residue_def, EXTENSION]
QED

(* Theorem: (mult_mod p).id = 1 *)
(* Proof: by mult_mod_def. *)
Theorem mult_mod_id:
  !p. (mult_mod p).id = 1
Proof
  simp[mult_mod_def]
QED

(* Theorem: FINITE (mult_mod p).carrier *)
(* Proof: by mult_mod_property *)
val mult_mod_finite = store_thm(
  "mult_mod_finite",
  ``!p. FINITE (mult_mod p).carrier``,
  rw[mult_mod_property]);

(* Theorem: 0 < p ==> (CARD (mult_mod p).carrier = p - 1) *)
(* Proof: by mult_mod_property *)
val mult_mod_card = store_thm(
  "mult_mod_card",
  ``!p. 0 < p ==> (CARD (mult_mod p).carrier = p - 1)``,
  rw[mult_mod_property]);

(* Theorem: Multiplicative Modulo Group is a group for prime p. *)
(* Proof: check group definitions.
   (1) Closure: prime p /\ x <> 0 /\ x < p /\ y <> 0 /\ y < p ==> (x * y) MOD p <> 0
       By contradiction. Suppose (x * y) MOD p = 0
       Then  x MOD p = 0  or y MOD p = 0   by EUCLID_LEMMA
       i.e         x = 0  or       y = 0   by LESS_MOD
       contradicting x <> 0 and y <> 0.
   (2) Associativity: x < p /\ y < p /\ z < p ==> ((x * y) MOD p * z) MOD p = (x * (y * z) MOD p) MOD p
       True by MOD_MULT_ASSOC, or
       LHS = ((x * y) MOD p * z) MOD p
           = ((x * y) MOD p * z MOD p) MOD p         by MOD_LESS
           = (x * y * z) MOD p                       by MOD_TIMES2
           = (x * (y * z)) MOD p                     by MULT_ASSOC
           = (x MOD p * (y * z) MOD p) MOD p         by MOD_TIMES2
           = (x * (y * z) MOD p) MOD p               by MOD_LESS
           = RHS
   (3) Identity: prime p ==> 1 < p
       True by ONE_LT_PRIME.
   (4) Multiplicative inverse: prime p /\ x <> 0 /\ x < p ==> ?y. (y <> 0 /\ y < p) /\ ((y * x) MOD p = 1)
       True by MOD_MULT_INV_DEF.
*)
val mult_mod_group = store_thm(
  "mult_mod_group",
  ``!p. prime p ==> Group (mult_mod p)``,
  rpt strip_tac >>
  `0 < p` by rw_tac std_ss[PRIME_POS] >>
  rw_tac std_ss[group_def_alt, mult_mod_property] >| [
    metis_tac[EUCLID_LEMMA, LESS_MOD, NOT_ZERO_LT_ZERO],
    rw_tac std_ss[MOD_MULT_ASSOC],
    rw_tac std_ss[ONE_LT_PRIME],
    metis_tac[MOD_MULT_INV_DEF, NOT_ZERO_LT_ZERO]
  ]);

(* Theorem: Multiplicative Modulo Group is an Abelian group for prime p. *)
(* Proof: by mult_mod_group and MULT_COMM. *)
val mult_mod_abelian_group = store_thm(
  "mult_mod_abelian_group",
  ``!p. prime p ==> AbelianGroup (mult_mod p)``,
  rw_tac std_ss[AbelianGroup_def, mult_mod_group, mult_mod_property, MULT_COMM, PRIME_POS]);

(* Theorem: Multiplicative Modulo Group is a Finite Abelian Group for prime p. *)
(* Proof: by mult_mod_group and mult_mod_property. *)
val mult_mod_finite_group = store_thm(
  "mult_mod_finite_group",
  ``!p. prime p ==> FiniteGroup (mult_mod p)``,
  rw_tac std_ss[FiniteGroup_def, mult_mod_group, mult_mod_property]);

(* Theorem: Multiplicative Modulo Group is a Finite Abelian Group for prime p. *)
(* Proof: by mult_mod_abelian_group and mult_mod_property. *)
val mult_mod_finite_abelian_group = store_thm(
  "mult_mod_finite_abelian_group",
  ``!p. prime p ==> FiniteAbelianGroup (mult_mod p)``,
  rw_tac std_ss[FiniteAbelianGroup_def, mult_mod_abelian_group, mult_mod_property]);

(* Theorem: (mult_mod p).exp a n = a ** n MOD p *)
(* Proof:
   By induction on n.
   Base case: (mult_mod p).exp a 0 = a ** 0 MOD p
      (mult_mod p).exp a 0
    = (mult_mod p).id                by group_exp_0
    = 1                              by mult_mod_def
    = 1 MOD 1                        by DIVMOD_ID, 0 < 1
    = a ** 0 MOD p                   by EXP
   Step case:  (mult_mod p).exp a n = a ** n MOD p ==> (mult_mod p).exp a (SUC n) = a ** SUC n MOD p
      (mult_mod p).exp a (SUC n)
    = a * ((mult_mod p).exp a n)     by group_exp_SUC
    = a * ((a ** n) MOD p)           by inductive hypothesis
    = (a MOD p) * ((a ** n) MOD p)   by a < p, MOD_LESS
    = (a * (a ** n)) MOD p           by MOD_TIMES2
    = (a ** (SUC n) MOD p            by EXP
*)
val mult_mod_exp = store_thm(
  "mult_mod_exp",
  ``!p a. prime p /\ a IN (mult_mod p).carrier ==> !n. (mult_mod p).exp a n = (a ** n) MOD p``,
  rw[mult_mod_def, monoid_exp_def, residue_def] >>
  `0 < p /\ 1 < p` by rw_tac std_ss[PRIME_POS, ONE_LT_PRIME] >>
  Induct_on `n` >-
  rw_tac std_ss[FUNPOW_0, EXP, ONE_MOD] >>
  rw_tac std_ss[FUNPOW_SUC, EXP] >>
  `a MOD p = a` by rw_tac arith_ss[] >>
  metis_tac[MOD_TIMES2]);

(* Theorem: due to zDefine before, now export the Define to computeLib. *)
(* Proof: by mult_mod_def. *)
val mult_mod_eval = store_thm(
  "mult_mod_eval",
  ``!p. ((mult_mod p).carrier = { i | i <> 0 /\ i < p }) /\
       (!x y. (mult_mod p).op x y = (x * y) MOD p) /\
       ((mult_mod p).id = 1)``,
  rw_tac std_ss[mult_mod_def]);

(*
- group_order_property |> ISPEC ``(mult_mod p)``;
> val it = |- FiniteGroup (mult_mod p) ==> !x. x IN (mult_mod p).carrier ==>
         0 < order (mult_mod p) x /\ ((mult_mod p).exp x (order (mult_mod p) x) = (mult_mod p).id) : thm
- EVAL ``order (mult_mod 5) 1``;
> val it = |- order (mult_mod 5) 1 = 1 : thm
- EVAL ``order (mult_mod 5) 2``;
> val it = |- order (mult_mod 5) 2 = 4 : thm
- EVAL ``order (mult_mod 5) 3``;
> val it = |- order (mult_mod 5) 3 = 4 : thm
- EVAL ``order (mult_mod 5) 4``;
> val it = |- order (mult_mod 5) 4 = 2 : thm
*)

(* Theorem: (mult_mod p).inv x = x ** (order (mult_mod p) x - 1) *)
(* Proof: by group_order_property and group_rinv_unique. *)
val mult_mod_inv = store_thm(
  "mult_mod_inv",
  ``!p. prime p ==> !x. 0 < x /\ x < p ==> ((mult_mod p).inv x = (mult_mod p).exp x (order (mult_mod p) x - 1))``,
  rpt strip_tac >>
  `x IN (mult_mod p).carrier /\ ((mult_mod p).id = 1)` by rw_tac std_ss[mult_mod_property] >>
  `Group (mult_mod p)` by rw_tac std_ss[mult_mod_group] >>
  `FiniteGroup (mult_mod p)` by rw_tac std_ss[FiniteGroup_def, mult_mod_property] >>
  `0 < order (mult_mod p) x /\ ((mult_mod p).exp x (order (mult_mod p) x) = 1)` by rw_tac std_ss[group_order_property] >>
  `SUC ((order (mult_mod p) x) - 1) = order (mult_mod p) x` by rw_tac arith_ss[] >>
  metis_tac[group_rinv_unique, group_exp_SUC, group_exp_element]);

(* val _ = computeLib.add_persistent_funs ["mult_mod_inv"]; -- cannot put a non-function. *)

(* Theorem: As function, (mult_mod p).inv x = x ** (order (mult_mod p) x - 1) *)
(* Proof: by mult_mod_inv. *)
val mult_mod_inv_compute = store_thm(
  "mult_mod_inv_compute",
  ``!p x. (mult_mod p).inv x = if prime p /\ 0 < x /\ x < p
                            then (mult_mod p).exp x (order (mult_mod p) x - 1)
                            else FAIL ((mult_mod p).inv x) bad_element``,
  rw_tac std_ss[mult_mod_inv, combinTheory.FAIL_DEF]);

(* Now put thse input computeLib for EVAL *)
val _ = computeLib.add_persistent_funs ["mult_mod_eval"];
val _ = computeLib.add_persistent_funs ["mult_mod_inv_compute"];
(* val _ = computeLib.set_skip (computeLib.the_compset) ``combin$FAIL`` (SOME 0); *)

(*
- EVAL ``(mult_mod 5).id``;
> val it = |- (mult_mod 5).id = 1 : thm
- EVAL ``(mult_mod 5).op 3 2``;
> val it = |- (mult_mod 5).op 3 2 = 1 : thm
- EVAL ``(mult_mod 5).inv 2``;
> val it = |- (mult_mod 5).inv 2 = if prime 5 then 3 else FAIL ((mult_mod 5).inv 2) bad_element : thm
- EVAL ``prime 5``;
> val it = |- prime 5 <=> prime 5 : thm

- val _ = computeLib.add_persistent_funs ["PRIME_5"];
- EVAL ``prime 5``;
> val it = |- prime 5 <=> T : thm
- EVAL ``(Z* 5).inv 2``;
> val it = |- (mult_mod 5).inv 2 = 3 : thm
*)

(* Export these for SIMP_CONV *)
val _ = export_rewrites ["mult_mod_eval", "mult_mod_inv"];

(*
- SIMP_CONV (srw_ss()) [] ``(mult_mod 5).id``;
> val it = |- (mult_mod 5).id = 1 : thm
- SIMP_CONV (srw_ss()) [] ``(mult_mod 5).op 3 2``;
> val it = |- (mult_mod 5).op 3 2 = 1 : thm
- SIMP_CONV (srw_ss()) [] ``(mult_mod 5).inv 2``;
! Uncaught exception:
! UNCHANGED
*)

(* ========================================================================= *)
(* Cryptography based on groups                                              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* ElGamal encryption and decryption -- purely group-theoretic.              *)
(* ------------------------------------------------------------------------- *)

(* Define encryption and decryption of ElGamal scheme. *)
val ElGamal_encrypt_def = Define`
  ElGamal_encrypt (g:'a group) (y:'a) (h:'a) (m:'a) (k:num) = (y ** k, (h ** k) * m)
`;

val ElGamal_decrypt_def = Define`
  ElGamal_decrypt (g:'a group) (x:num) (a:'a, b:'a) = ( |/ (a ** x)) * b
`;

(* Theorem: ElGamal decypt can undo ElGamal encrypt. *)
(* Proof:
   This is to show
   ElGamal_decrypt g x (ElGamal_encrypt g y h m k)  = m
   or:     |/ ((y ** k) ** x) * ((y ** x) ** k * m) = m

   |/ ((y ** k) ** x) * ((y ** x) ** k * m)
 = |/ (y ** (k*x)) * (y ** (x*k) * m)      by group_exp_mult
 = ( |/ y) ** (k*x) * (y ** (x*k) * m)     by group_exp_inv
 = ( |/ y) ** (k*x) * (y ** (k*x) * m)     by MULT_COMM (the x*k is not g.op, in exp)
 = (( |/ y) ** (k*x) * y ** (k*x)) * m     by group_assoc
 = ( |/y * y) ** (k*x) * m                 by group_mult_exp
 = #e ** (k*x) * m                         by group_linv, group_rinv
 = #e * m                                  by group_id_exp
 = m                                       by group_lid
*)
val ElGamal_correctness = store_thm(
  "ElGamal_correctness",
  ``!g:'a group. Group g ==> !y h m::G. !k x. (h = y ** x) ==> (ElGamal_decrypt g x (ElGamal_encrypt g y h m k) = m)``,
  rw_tac std_ss[ElGamal_encrypt_def, ElGamal_decrypt_def, RES_FORALL_THM] >>
  `|/ ((y ** k) ** x) * ((y ** x) ** k * m) = |/ (y ** (k*x)) * (y ** (x*k) * m)` by rw_tac std_ss[group_exp_mult] >>
  `_ = ( |/ y)**(k*x) * (y**(x*k) * m)` by rw_tac std_ss[group_exp_inv] >>
  `_ = ( |/ y)**(k*x) * (y**(k*x) * m)` by rw_tac std_ss[MULT_COMM] >>
  `_ = (( |/ y)**(k*x) * y**(k*x)) * m` by rw_tac std_ss[group_assoc, group_inv_element, group_exp_element] >>
  `_ = ( |/y * y)**(k*x) * m` by rw_tac std_ss[group_linv, group_rinv, group_comm_op_exp, group_inv_element] >>
  rw_tac std_ss[group_linv, group_id_exp, group_lid]);

(* ------------------------------------------------------------------------- *)
(* A Group from Sets.                                                        *)
(* ------------------------------------------------------------------------- *)

(* Define symmetric difference for two sets. *)
val symdiff_def = Define`symdiff s1 s2 = (s1 UNION s2) DIFF (s1 INTER s2)`;

(* The Group of set symmetric difference *)
val symdiff_set_def = Define`
  symdiff_set = <| carrier := UNIV;
                       id := EMPTY;
                       op := symdiff |>
`;

(*
> EVAL ``symdiff_set.id``;
val it = |- symdiff_set.id = {}: thm
> EVAL ``symdiff_set.op {1;2;3;4} {1;4;5;6}``;
val it = |- symdiff_set.op {1; 2; 3; 4} {1; 4; 5; 6} = {2; 3; 5; 6}: thm
*)


(* Theorem: symdiff_set is a Group. *)
(* Proof: check definitions. *)
val symdiff_set_group = store_thm(
  "symdiff_set_group",
  ``Group symdiff_set``,
  rw[group_def_alt, symdiff_set_def] >| [
    rw[EXTENSION, symdiff_def] >> metis_tac[],
    rw[EXTENSION, symdiff_def],
    qexists_tac `x` >> rw[EXTENSION, symdiff_def]
  ]);

val _ = export_rewrites ["symdiff_set_group"];

(* Theorem: symdiff_set is an abelian Group. *)
(* Proof: check definitions. *)
val symdiff_set_abelian_group = store_thm(
  "symdiff_set_abelian_group",
  ``AbelianGroup symdiff_set``,
  rw[AbelianGroup_def, symdiff_set_def] >>
  rw[symdiff_def, EXTENSION] >>
  metis_tac[]);

val _ = export_rewrites ["symdiff_set_abelian_group"];

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
