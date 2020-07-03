(* ------------------------------------------------------------------------- *)
(* Applying Monoid Theory: Monoid Instances                                  *)
(* ------------------------------------------------------------------------- *)

(*

Monoid Instances
===============
The important ones:

 Zn -- Addition Modulo n, n > 0.
Z*n -- Multiplication Modulo n, n > 1.

*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "monoidInstances";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* Get dependent theories local *)
(* val _ = load "monoidMapTheory"; *)
open monoidTheory;
open monoidMapTheory; (* for MonoidHomo and MonoidIso *)

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; -- in monoidTheory *) *)
(* (* val _ = load "helperSetTheory"; -- in monoidTheory *) *)
open helperNumTheory helperSetTheory helperFunctionTheory;

(* open dependent theories *)
(* (* val _ = load "dividesTheory"; -- in helperTheory *) *)
(* (* val _ = load "gcdTheory"; -- in helperTheory *) *)
open pred_setTheory arithmeticTheory dividesTheory gcdTheory;
open listTheory; (* for list concatenation example *)

(* val _ = load "logPowerTheory"; *)
open logrootTheory logPowerTheory; (* for LOG_EXACT_EXP *)


(* ------------------------------------------------------------------------- *)
(* Monoid Instances Documentation                                            *)
(* ------------------------------------------------------------------------- *)
(* Monoid Data type:
   The generic symbol for monoid data is g.
   g.carrier = Carrier set of monoid
   g.op      = Binary operation of monoid
   g.id      = Identity element of monoid
*)
(* Definitions and Theorems (# are exported, ! in computeLib):

   The trivial monoid:
   trivial_monoid_def |- !e. trivial_monoid e = <|carrier := {e}; id := e; op := (\x y. e)|>
   trivial_monoid     |- !e. FiniteAbelianMonoid (trivial_monoid e)

   The monoid of addition modulo n:
   plus_mod_def                     |- !n. plus_mod n =
                                           <|carrier := count n;
                                                  id := 0;
                                                  op := (\i j. (i + j) MOD n)|>
   plus_mod_property                |- !n. ((plus_mod n).carrier = count n) /\
                                           ((plus_mod n).op = (\i j. (i + j) MOD n)) /\
                                           ((plus_mod n).id = 0) /\
                                           (!x. x IN (plus_mod n).carrier ==> x < n) /\
                                           FINITE (plus_mod n).carrier /\
                                           (CARD (plus_mod n).carrier = n)
   plus_mod_exp                     |- !n. 0 < n ==> !x k. (plus_mod n).exp x k = (k * x) MOD n
   plus_mod_monoid                  |- !n. 0 < n ==> Monoid (plus_mod n)
   plus_mod_abelian_monoid          |- !n. 0 < n ==> AbelianMonoid (plus_mod n)
   plus_mod_finite                  |- !n. FINITE (plus_mod n).carrier
   plus_mod_finite_monoid           |- !n. 0 < n ==> FiniteMonoid (plus_mod n)
   plus_mod_finite_abelian_monoid   |- !n. 0 < n ==> FiniteAbelianMonoid (plus_mod n)

   The monoid of multiplication modulo n:
   times_mod_def                    |- !n. times_mod n =
                                           <|carrier := count n;
                                                  id := if n = 1 then 0 else 1;
                                                  op := (\i j. (i * j) MOD n)|>
!  times_mod_eval                   |- !n. ((times_mod n).carrier = count n) /\
                                           (!x y. (times_mod n).op x y = (x * y) MOD n) /\
                                           ((times_mod n).id = if n = 1 then 0 else 1)
   times_mod_property               |- !n. ((times_mod n).carrier = count n) /\
                                           ((times_mod n).op = (\i j. (i * j) MOD n)) /\
                                           ((times_mod n).id = if n = 1 then 0 else 1) /\
                                           (!x. x IN (times_mod n).carrier ==> x < n) /\
                                           FINITE (times_mod n).carrier /\
                                           (CARD (times_mod n).carrier = n)
   times_mod_exp                    |- !n. 0 < n ==> !x k. (times_mod n).exp x k = (x MOD n) ** k MOD n
   times_mod_monoid                 |- !n. 0 < n ==> Monoid (times_mod n)
   times_mod_abelian_monoid         |- !n. 0 < n ==> AbelianMonoid (times_mod n)
   times_mod_finite                 |- !n. FINITE (times_mod n).carrier
   times_mod_finite_monoid          |- !n. 0 < n ==> FiniteMonoid (times_mod n)
   times_mod_finite_abelian_monoid  |- !n. 0 < n ==> FiniteAbelianMonoid (times_mod n)

   The Monoid of List concatenation:
   lists_def     |- lists = <|carrier := univ(:'a list); id := []; op := $++ |>
   lists_monoid  |- Monoid lists

   The Monoids from Set:
   set_inter_def             |- set_inter = <|carrier := univ(:'a -> bool); id := univ(:'a); op := $INTER|>
   set_inter_monoid          |- Monoid set_inter
   set_inter_abelian_monoid  |- AbelianMonoid set_inter
   set_union_def             |- set_union = <|carrier := univ(:'a -> bool); id := {}; op := $UNION|>
   set_union_monoid          |- Monoid set_union
   set_union_abelian_monoid  |- AbelianMonoid set_union

   Addition of numbers form a Monoid:
   addition_monoid_def       |- addition_monoid = <|carrier := univ(:num); op := $+; id := 0|>
   addition_monoid_property  |- (addition_monoid.carrier = univ(:num)) /\
                                  (addition_monoid.op = $+) /\ (addition_monoid.id = 0)
   addition_monoid_abelian_monoid  |- AbelianMonoid addition_monoid
   addition_monoid_monoid          |- Monoid addition_monoid

   Multiplication of numbers form a Monoid:
   multiplication_monoid_def       |- multiplication_monoid = <|carrier := univ(:num); op := $*; id := 1|>
   multiplication_monoid_property  |- (multiplication_monoid.carrier = univ(:num)) /\
                                      (multiplication_monoid.op = $* ) /\ (multiplication_monoid.id = 1)
   multiplication_monoid_abelian_monoid   |- AbelianMonoid multiplication_monoid
   multiplication_monoid_monoid           |- Monoid multiplication_monoid

   Powers of a fixed base form a Monoid:
   power_monoid_def            |- !b. power_monoid b =
                                      <|carrier := {b ** j | j IN univ(:num)}; op := $*; id := 1|>
   power_monoid_property       |- !b. ((power_monoid b).carrier = {b ** j | j IN univ(:num)}) /\
                                      ((power_monoid b).op = $* ) /\ ((power_monoid b).id = 1)
   power_monoid_abelian_monoid |- !b. AbelianMonoid (power_monoid b)
   power_monoid_monoid         |- !b. Monoid (power_monoid b)

   Logarithm is an isomorphism:
   power_to_addition_homo  |- !b. 1 < b ==> MonoidHomo (LOG b) (power_monoid b) addition_monoid
   power_to_addition_iso   |- !b. 1 < b ==> MonoidIso (LOG b) (power_monoid b) addition_monoid


*)
(* ------------------------------------------------------------------------- *)
(* The trivial monoid.                                                       *)
(* ------------------------------------------------------------------------- *)

(* The trivial monoid: {#e} *)
val trivial_monoid_def = Define`
  trivial_monoid e :'a monoid =
   <| carrier := {e};
           id := e;
           op := (\x y. e)
    |>
`;

(*
- type_of ``trivial_monoid e``;
> val it = ``:'a monoid`` : hol_type
> EVAL ``(trivial_monoid T).id``;
val it = |- (trivial_monoid T).id <=> T: thm
> EVAL ``(trivial_monoid 8).id``;
val it = |- (trivial_monoid 8).id = 8: thm
*)

(* Theorem: {e} is indeed a monoid *)
(* Proof: check by definition. *)
val trivial_monoid = store_thm(
  "trivial_monoid",
  ``!e. FiniteAbelianMonoid (trivial_monoid e)``,
  rw_tac std_ss[FiniteAbelianMonoid_def, AbelianMonoid_def, Monoid_def, trivial_monoid_def, IN_SING, FINITE_SING]);

(* ------------------------------------------------------------------------- *)
(* The monoid of addition modulo n.                                          *)
(* ------------------------------------------------------------------------- *)

(* Additive Modulo Monoid *)
val plus_mod_def = Define`
  plus_mod n :num monoid =
   <| carrier := count n;
           id := 0;
           op := (\i j. (i + j) MOD n)
    |>
`;
(* This monoid should be upgraded to add_mod, the additive group of ZN ring later. *)

(*
- type_of ``plus_mod n``;
> val it = ``:num monoid`` : hol_type
> EVAL ``(plus_mod 7).op 5 6``;
val it = |- (plus_mod 7).op 5 6 = 4: thm
*)

(* Theorem: properties of (plus_mod n) *)
(* Proof: by plus_mod_def. *)
val plus_mod_property = store_thm(
  "plus_mod_property",
  ``!n. ((plus_mod n).carrier = count n) /\
       ((plus_mod n).op = (\i j. (i + j) MOD n)) /\
       ((plus_mod n).id = 0) /\
       (!x. x IN (plus_mod n).carrier ==> x < n) /\
       (FINITE (plus_mod n).carrier) /\
       (CARD (plus_mod n).carrier = n)``,
  rw[plus_mod_def]);

(* Theorem: 0 < n ==> !x k. (plus_mod n).exp x k = (k * x) MOD n *)
(* Proof:
   Expanding by definitions, this is to show:
   FUNPOW (\j. (x + j) MOD n) k 0 = (k * x) MOD n
   Applyy induction on k.
   Base case: FUNPOW (\j. (x + j) MOD n) 0 0 = (0 * x) MOD n
   LHS = FUNPOW (\j. (x + j) MOD n) 0 0
       = 0                                by FUNPOW_0
       = 0 MOD n                          by ZERO_MOD, 0 < n
       = (0 * x) MOD n                    by MULT
       = RHS
   Step case: FUNPOW (\j. (x + j) MOD n) (SUC k) 0 = (SUC k * x) MOD n
   LHS = FUNPOW (\j. (x + j) MOD n) (SUC k) 0
       = (x + FUNPOW (\j. (x + j) MOD n) k 0) MOD n    by FUNPOW_SUC
       = (x + (k * x) MOD n) MOD n                     by induction hypothesis
       = (x MOD n + (k * x) MOD n) MOD n               by MOD_PLUS, MOD_MOD
       = (x + k * x) MOD n                             by MOD_PLUS, MOD_MOD
       = (k * x + x) MOD n                by ADD_COMM
       = ((SUC k) * x) MOD n              by MULT
       = RHS
*)
val plus_mod_exp = store_thm(
  "plus_mod_exp",
  ``!n. 0 < n ==> !x k. (plus_mod n).exp x k = (k * x) MOD n``,
  rw_tac std_ss[plus_mod_def, monoid_exp_def] >>
  Induct_on `k` >-
  rw[] >>
  rw_tac std_ss[FUNPOW_SUC] >>
  metis_tac[MULT, ADD_COMM, MOD_PLUS, MOD_MOD]);

(* Theorem: Additive Modulo n is a monoid. *)
(* Proof: check group definitions, use MOD_ADD_ASSOC.
*)
val plus_mod_monoid = store_thm(
  "plus_mod_monoid",
  ``!n. 0 < n ==> Monoid (plus_mod n)``,
  rw_tac std_ss[plus_mod_def, Monoid_def, count_def, GSPECIFICATION, MOD_ADD_ASSOC]);

(* Theorem: Additive Modulo n is an Abelian monoid. *)
(* Proof: by plus_mod_monoid and ADD_COMM. *)
val plus_mod_abelian_monoid = store_thm(
  "plus_mod_abelian_monoid",
  ``!n. 0 < n ==> AbelianMonoid (plus_mod n)``,
  rw[plus_mod_monoid, plus_mod_def, AbelianMonoid_def, ADD_COMM]);

(* Theorem: Additive Modulo n carrier is FINITE. *)
(* Proof: by FINITE_COUNT. *)
val plus_mod_finite = store_thm(
  "plus_mod_finite",
  ``!n. FINITE (plus_mod n).carrier``,
  rw[plus_mod_def]);

(* Theorem: Additive Modulo n is a FINITE monoid. *)
(* Proof: by plus_mod_monoid and plus_mod_finite. *)
val plus_mod_finite_monoid = store_thm(
  "plus_mod_finite_monoid",
  ``!n. 0 < n ==> FiniteMonoid (plus_mod n)``,
  rw[FiniteMonoid_def, plus_mod_monoid, plus_mod_finite]);

(* Theorem: Additive Modulo n is a FINITE Abelian monoid. *)
(* Proof: by plus_mod_abelian_monoid and plus_mod_finite. *)
val plus_mod_finite_abelian_monoid = store_thm(
  "plus_mod_finite_abelian_monoid",
  ``!n. 0 < n ==> FiniteAbelianMonoid (plus_mod n)``,
  rw[FiniteAbelianMonoid_def, plus_mod_abelian_monoid, plus_mod_finite]);

(* ------------------------------------------------------------------------- *)
(* The monoid of multiplication modulo n.                                    *)
(* ------------------------------------------------------------------------- *)

(* Multiplicative Modulo Monoid *)
val times_mod_def = zDefine`
  times_mod n :num monoid =
   <| carrier := count n;
           id := if n = 1 then 0 else 1;
           op := (\i j. (i * j) MOD n)
    |>
`;
(* This monoid is taken as the multiplicative monoid of ZN ring later. *)
(* Use of zDefine to avoid incorporating into computeLib, by default. *)
(* Evaluation is given later in times_mod_eval. *)

(*
- type_of ``times_mod n``;
> val it = ``:num monoid`` : hol_type
> EVAL ``(times_mod 7).op 5 6``;
val it = |- (times_mod 7).op 5 6 = 2: thm
*)

(* Theorem: times_mod evaluation. *)
(* Proof: by times_mod_def. *)
val times_mod_eval = store_thm(
  "times_mod_eval[compute]",
  ``!n. ((times_mod n).carrier = count n) /\
       (!x y. (times_mod n).op x y = (x * y) MOD n) /\
       ((times_mod n).id = if n = 1 then 0 else 1)``,
  rw_tac std_ss[times_mod_def]);

(* Theorem: properties of (times_mod n) *)
(* Proof: by times_mod_def. *)
val times_mod_property = store_thm(
  "times_mod_property",
  ``!n. ((times_mod n).carrier = count n) /\
       ((times_mod n).op = (\i j. (i * j) MOD n)) /\
       ((times_mod n).id = if n = 1 then 0 else 1) /\
       (!x. x IN (times_mod n).carrier ==> x < n) /\
       (FINITE (times_mod n).carrier) /\
       (CARD (times_mod n).carrier = n)``,
  rw[times_mod_def]);

(* Theorem: 0 < n ==> !x k. (times_mod n).exp x k = ((x MOD n) ** k) MOD n *)
(* Proof:
   Expanding by definitions, this is to show:
   (1) n = 1 ==> FUNPOW (\j. (x * j) MOD n) k 0 = (x MOD n) ** k MOD n
       or to show: FUNPOW (\j. 0) k 0 = 0       by MOD_1
       Note (\j. 0) = K 0                       by FUN_EQ_THM
        and FUNPOW (K 0) k 0 = 0                by FUNPOW_K
   (2) n <> 1 ==> FUNPOW (\j. (x * j) MOD n) k 1 = (x MOD n) ** k MOD n
       Note 1 < n                               by 0 < n /\ n <> 1
       By induction on k.
       Base: FUNPOW (\j. (x * j) MOD n) 0 1 = (x MOD n) ** 0 MOD n
             FUNPOW (\j. (x * j) MOD n) 0 1
           = 1                                  by FUNPOW_0
           = 1 MOD n                            by ONE_MOD, 1 < n
           = ((x MOD n) ** 0) MOD n             by EXP
       Step: FUNPOW (\j. (x * j) MOD n) (SUC k) 1 = (x MOD n) ** SUC k MOD n
             FUNPOW (\j. (x * j) MOD n) (SUC k) 1
           = (x * FUNPOW (\j. (x * j) MOD n) k 1) MOD n    by FUNPOW_SUC
           = (x * (x MOD n) ** k MOD n) MOD n              by induction hypothesis
           = ((x MOD n) * (x MOD n) ** k MOD n) MOD n      by MOD_TIMES2, MOD_MOD, 0 < n
           = ((x MOD n) * (x MOD n) ** k) MOD n            by MOD_TIMES2, MOD_MOD, 0 < n
           = ((x MOD n) ** SUC k) MOD n                    by EXP
*)
val times_mod_exp = store_thm(
  "times_mod_exp",
  ``!n. 0 < n ==> !x k. (times_mod n).exp x k = ((x MOD n) ** k) MOD n``,
  rw_tac std_ss[times_mod_def, monoid_exp_def] >| [
    `(\j. 0) = K 0` by rw[FUN_EQ_THM] >>
    metis_tac[FUNPOW_K],
    `1 < n` by decide_tac >>
    Induct_on `k` >-
    rw[EXP, ONE_MOD] >>
    `FUNPOW (\j. (x * j) MOD n) (SUC k) 1 = (x * FUNPOW (\j. (x * j) MOD n) k 1) MOD n` by rw_tac std_ss[FUNPOW_SUC] >>
    metis_tac[EXP, MOD_TIMES2, MOD_MOD]
  ]);

(* Theorem: For n > 0, Multiplication Modulo n is a monoid. *)
(* Proof: check monoid definitions, use MOD_MULT_ASSOC. *)
val times_mod_monoid = store_thm(
  "times_mod_monoid",
  ``!n. 0 < n ==> Monoid (times_mod n)``,
  rw_tac std_ss[Monoid_def, times_mod_def, count_def, GSPECIFICATION] >| [
    decide_tac,
    rw[MOD_MULT_ASSOC],
    decide_tac
  ]);

(* Theorem: For n > 0, Multiplication Modulo n is an Abelian monoid. *)
(* Proof: by times_mod_monoid and MULT_COMM. *)
val times_mod_abelian_monoid = store_thm(
  "times_mod_abelian_monoid",
  ``!n. 0 < n ==> AbelianMonoid (times_mod n)``,
  rw[AbelianMonoid_def, times_mod_monoid, times_mod_def, MULT_COMM]);

(* Theorem: Multiplication Modulo n carrier is FINITE. *)
(* Proof: by FINITE_COUNT. *)
val times_mod_finite = store_thm(
  "times_mod_finite",
  ``!n. FINITE (times_mod n).carrier``,
  rw[times_mod_def]);

(* Theorem: For n > 0, Multiplication Modulo n is a FINITE monoid. *)
(* Proof: by times_mod_monoid and times_mod_finite. *)
val times_mod_finite_monoid = store_thm(
  "times_mod_finite_monoid",
  ``!n. 0 < n ==> FiniteMonoid (times_mod n)``,
  rw[times_mod_monoid, times_mod_finite, FiniteMonoid_def]);

(* Theorem: For n > 0, Multiplication Modulo n is a FINITE Abelian monoid. *)
(* Proof: by times_mod_abelian_monoid and times_mod_finite. *)
val times_mod_finite_abelian_monoid = store_thm(
  "times_mod_finite_abelian_monoid",
  ``!n. 0 < n ==> FiniteAbelianMonoid (times_mod n)``,
  rw[times_mod_abelian_monoid, times_mod_finite, FiniteAbelianMonoid_def, AbelianMonoid_def]);

(*

- EVAL ``(plus_mod 5).op 3 4``;
> val it = |- (plus_mod 5).op 3 4 = 2 : thm
- EVAL ``(plus_mod 5).id``;
> val it = |- (plus_mod 5).id = 0 : thm
- EVAL ``(times_mod 5).op 2 3``;
> val it = |- (times_mod 5).op 2 3 = 1 : thm
- EVAL ``(times_mod 5).op 5 3``;
> val it = |- (times_mod 5).id = 1 : thm
*)

(* ------------------------------------------------------------------------- *)
(* The Monoid of List concatenation.                                         *)
(* ------------------------------------------------------------------------- *)

val lists_def = Define`
  lists :'a list monoid =
   <| carrier := UNIV;
           id := [];
           op := list$APPEND
    |>
`;

(*
> EVAL ``lists.op [1;2;3] [4;5]``;
val it = |- lists.op [1; 2; 3] [4; 5] = [1; 2; 3; 4; 5]: thm
*)

(* Theorem: Lists form a Monoid *)
(* Proof: check definition. *)
val lists_monoid = store_thm(
  "lists_monoid",
  ``Monoid lists``,
  rw_tac std_ss[Monoid_def, lists_def, IN_UNIV, GSPECIFICATION, APPEND, APPEND_NIL, APPEND_ASSOC]);

(* after a long while ...

val lists_monoid = store_thm(
  "lists_monoid",
  ``Monoid lists``,
  rw[Monoid_def, lists_def]);
*)

(* ------------------------------------------------------------------------- *)
(* The Monoids from Set.                                                     *)
(* ------------------------------------------------------------------------- *)

(* The Monoid of set intersection *)
val set_inter_def = Define`
  set_inter = <| carrier := UNIV;
                      id := UNIV;
                      op := (INTER) |>
`;

(*
> EVAL ``set_inter.op {1;4;5;6} {5;6;8;9}``;
val it = |- set_inter.op {1; 4; 5; 6} {5; 6; 8; 9} = {5; 6}: thm
*)

(* Theorem: set_inter is a Monoid. *)
(* Proof: check definitions. *)
val set_inter_monoid = store_thm(
  "set_inter_monoid",
  ``Monoid set_inter``,
  rw[Monoid_def, set_inter_def, INTER_ASSOC]);

val _ = export_rewrites ["set_inter_monoid"];

(* Theorem: set_inter is an abelian Monoid. *)
(* Proof: check definitions. *)
val set_inter_abelian_monoid = store_thm(
  "set_inter_abelian_monoid",
  ``AbelianMonoid set_inter``,
  rw[AbelianMonoid_def, set_inter_def, INTER_COMM]);

val _ = export_rewrites ["set_inter_abelian_monoid"];

(* The Monoid of set union *)
val set_union_def = Define`
  set_union = <| carrier := UNIV;
                      id := EMPTY;
                      op := (UNION) |>
`;

(*
> EVAL ``set_union.op {1;4;5;6} {5;6;8;9}``;
val it = |- set_union.op {1; 4; 5; 6} {5; 6; 8; 9} = {1; 4; 5; 6; 8; 9}: thm
*)

(* Theorem: set_union is a Monoid. *)
(* Proof: check definitions. *)
val set_union_monoid = store_thm(
  "set_union_monoid",
  ``Monoid set_union``,
  rw[Monoid_def, set_union_def, UNION_ASSOC]);

val _ = export_rewrites ["set_union_monoid"];

(* Theorem: set_union is an abelian Monoid. *)
(* Proof: check definitions. *)
val set_union_abelian_monoid = store_thm(
  "set_union_abelian_monoid",
  ``AbelianMonoid set_union``,
  rw[AbelianMonoid_def, set_union_def, UNION_COMM]);

val _ = export_rewrites ["set_union_abelian_monoid"];

(* ------------------------------------------------------------------------- *)
(* Addition of numbers form a Monoid                                         *)
(* ------------------------------------------------------------------------- *)

(* Define the number addition monoid *)
val addition_monoid_def = Define`
    addition_monoid =
       <| carrier := univ(:num);
          op := $+;
          id := 0;
        |>
`;

(*
> EVAL ``addition_monoid.op 5 6``;
val it = |- addition_monoid.op 5 6 = 11: thm
*)

(* Theorem: properties of addition_monoid *)
(* Proof: by addition_monoid_def *)
val addition_monoid_property = store_thm(
  "addition_monoid_property",
  ``(addition_monoid.carrier = univ(:num)) /\
   (addition_monoid.op = $+ ) /\
   (addition_monoid.id = 0)``,
  rw[addition_monoid_def]);

(* Theorem: AbelianMonoid (addition_monoid) *)
(* Proof:
   By AbelianMonoid_def, Monoid_def, addition_monoid_def, this is to show:
   (1) ?z. z = x + y. Take z = x + y.
   (2) x + y + z = x + (y + z), true    by ADD_ASSOC
   (3) x + 0 = x /\ 0 + x = x, true     by ADD, ADD_0
   (4) x + y = y + x, true              by ADD_COMM
*)
val addition_monoid_abelian_monoid = store_thm(
  "addition_monoid_abelian_monoid",
  ``AbelianMonoid (addition_monoid)``,
  rw_tac std_ss[AbelianMonoid_def, Monoid_def, addition_monoid_def, GSPECIFICATION, IN_UNIV] >>
  simp[]);

(* Theorem: Monoid (addition_monoid) *)
(* Proof: by addition_monoid_abelian_monoid, AbelianMonoid_def *)
val addition_monoid_monoid = store_thm(
  "addition_monoid_monoid",
  ``Monoid (addition_monoid)``,
  metis_tac[addition_monoid_abelian_monoid, AbelianMonoid_def]);

(* ------------------------------------------------------------------------- *)
(* Multiplication of numbers form a Monoid                                   *)
(* ------------------------------------------------------------------------- *)

(* Define the number multiplication monoid *)
val multiplication_monoid_def = Define`
    multiplication_monoid =
       <| carrier := univ(:num);
          op := $*;
          id := 1;
        |>
`;

(*
> EVAL ``multiplication_monoid.op 5 6``;
val it = |- multiplication_monoid.op 5 6 = 30: thm
*)

(* Theorem: properties of multiplication_monoid *)
(* Proof: by multiplication_monoid_def *)
val multiplication_monoid_property = store_thm(
  "multiplication_monoid_property",
  ``(multiplication_monoid.carrier = univ(:num)) /\
   (multiplication_monoid.op = $* ) /\
   (multiplication_monoid.id = 1)``,
  rw[multiplication_monoid_def]);

(* Theorem: AbelianMonoid (multiplication_monoid) *)
(* Proof:
   By AbelianMonoid_def, Monoid_def, multiplication_monoid_def, this is to show:
   (1) ?z. z = x * y. Take z = x * y.
   (2) x * y * z = x * (y * z), true    by MULT_ASSOC
   (3) x * 1 = x /\ 1 * x = x, true     by MULT, MULT_1
   (4) x * y = y * x, true              by MULT_COMM
*)
val multiplication_monoid_abelian_monoid = store_thm(
  "multiplication_monoid_abelian_monoid",
  ``AbelianMonoid (multiplication_monoid)``,
  rw_tac std_ss[AbelianMonoid_def, Monoid_def, multiplication_monoid_def, GSPECIFICATION, IN_UNIV] >-
  simp[] >>
  simp[]);

(* Theorem: Monoid (multiplication_monoid) *)
(* Proof: by multiplication_monoid_abelian_monoid, AbelianMonoid_def *)
val multiplication_monoid_monoid = store_thm(
  "multiplication_monoid_monoid",
  ``Monoid (multiplication_monoid)``,
  metis_tac[multiplication_monoid_abelian_monoid, AbelianMonoid_def]);

(* ------------------------------------------------------------------------- *)
(* Powers of a fixed base form a Monoid                                      *)
(* ------------------------------------------------------------------------- *)

(* Define the power monoid *)
val power_monoid_def = Define`
    power_monoid (b:num) =
       <| carrier := {b ** j | j IN univ(:num)};
          op := $*;
          id := 1;
        |>
`;

(*
> EVAL ``(power_monoid 2).op (2 ** 3) (2 ** 4)``;
val it = |- (power_monoid 2).op (2 ** 3) (2 ** 4) = 128: thm
*)

(* Theorem: properties of power monoid *)
(* Proof: by power_monoid_def *)
val power_monoid_property = store_thm(
  "power_monoid_property",
  ``!b. ((power_monoid b).carrier = {b ** j | j IN univ(:num)}) /\
       ((power_monoid b).op = $* ) /\
       ((power_monoid b).id = 1)``,
  rw[power_monoid_def]);


(* Theorem: AbelianMonoid (power_monoid b) *)
(* Proof:
   By AbelianMonoid_def, Monoid_def, power_monoid_def, this is to show:
   (1) ?j''. b ** j * b ** j' = b ** j''
       Take j'' = j + j', true         by EXP_ADD
   (2) b ** j * b ** j' * b ** j'' = b ** j * (b ** j' * b ** j'')
       True                            by EXP_ADD, ADD_ASSOC
   (3) ?j. b ** j = 1
       or ?j. (b = 1) \/ (j = 0), true by j = 0.
   (4) b ** j * b ** j' = b ** j' * b ** j
       True                            by EXP_ADD, ADD_COMM
*)
val power_monoid_abelian_monoid = store_thm(
  "power_monoid_abelian_monoid",
  ``!b. AbelianMonoid (power_monoid b)``,
  rw_tac std_ss[AbelianMonoid_def, Monoid_def, power_monoid_def, GSPECIFICATION, IN_UNIV] >-
  metis_tac[EXP_ADD] >-
  rw[EXP_ADD] >-
  metis_tac[] >>
  rw[EXP_ADD]);

(* Theorem: Monoid (power_monoid b) *)
(* Proof: by power_monoid_abelian_monoid, AbelianMonoid_def *)
val power_monoid_monoid = store_thm(
  "power_monoid_monoid",
  ``!b. Monoid (power_monoid b)``,
  metis_tac[power_monoid_abelian_monoid, AbelianMonoid_def]);

(* ------------------------------------------------------------------------- *)
(* Logarithm is an isomorphism from Power Monoid to Addition Monoid          *)
(* ------------------------------------------------------------------------- *)

(* Theorem: 1 < b ==> MonoidHomo (LOG b) (power_monoid b) (addition_monoid) *)
(* Proof:
   By MonoidHomo_def, power_monoid_def, addition_monoid_def, this is to show:
   (1) LOG b (b ** j * b ** j') = LOG b (b ** j) + LOG b (b ** j')
         LOG b (b ** j * b ** j')
       = LOG b (b ** (j + j'))              by EXP_ADD
       = j + j'                             by LOG_EXACT_EXP
       = LOG b (b ** j) + LOG b (b ** j')   by LOG_EXACT_EXP
   (2) LOG b 1 = 0, true                    by LOG_1
*)
val power_to_addition_homo = store_thm(
  "power_to_addition_homo",
  ``!b. 1 < b ==> MonoidHomo (LOG b) (power_monoid b) (addition_monoid)``,
  rw[MonoidHomo_def, power_monoid_def, addition_monoid_def] >-
  rw[LOG_EXACT_EXP, GSYM EXP_ADD] >>
  rw[LOG_1]);

(* Theorem: 1 < b ==> MonoidIso (LOG b) (power_monoid b) (addition_monoid) *)
(* Proof:
   By MonoidIso_def, this is to show:
   (1) MonoidHomo (LOG b) (power_monoid b) addition_monoid
       This is true               by power_to_addition_homo
   (2) BIJ (LOG b) (power_monoid b).carrier addition_monoid.carrier
       By BIJ_DEF, this is to show:
       (1) INJ (LOG b) {b ** j | j IN univ(:num)} univ(:num)
           By INJ_DEF, this is to show:
               LOG b (b ** j) = LOG b (b ** j') ==> b ** j = b ** j'
               LOG b (b ** j) = LOG b (b ** j')
           ==>             j  = j'                by LOG_EXACT_EXP
           ==>         b ** j = b ** j'
       (2) SURJ (LOG b) {b ** j | j IN univ(:num)} univ(:num)
           By SURJ_DEF, this is to show:
              ?y. (?j. y = b ** j) /\ (LOG b y = x)
           Let j = x, y = b ** x, then true       by LOG_EXACT_EXP
*)
val power_to_addition_iso = store_thm(
  "power_to_addition_iso",
  ``!b. 1 < b ==> MonoidIso (LOG b) (power_monoid b) (addition_monoid)``,
  rw[MonoidIso_def] >-
  rw[power_to_addition_homo] >>
  rw_tac std_ss[BIJ_DEF, power_monoid_def, addition_monoid_def] >| [
    rw[INJ_DEF] >>
    rfs[LOG_EXACT_EXP],
    rw[SURJ_DEF] >>
    metis_tac[LOG_EXACT_EXP]
  ]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
