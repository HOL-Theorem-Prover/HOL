(* ------------------------------------------------------------------------- *)
(* Polynomial Package                                                        *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "polynomial";

(* ------------------------------------------------------------------------- *)



(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory;

(* Get dependent theories local *)
(* (* val _ = load "monoidTheory"; *) *)
(* (* val _ = load "groupTheory"; *) *)
(* (* val _ = load "ringTheory"; *) *)
(* (* val _ = load "integralDomainTheory"; *) *)
(* val _ = load "fieldTheory"; *)
open monoidTheory groupTheory ringTheory integralDomainTheory fieldTheory;

(* Instances for examples. *)
(* (* val _ = load "ringInstancesTheory"; *) *)
(* (* val _ = load "fieldInstancesTheory"; *) *)
(* open ringInstancesTheory fieldInstancesTheory; *)

(* Get dependent theories in lib *)
(* (* val _ = load "helperNumTheory"; *) *)
(* (* val _ = load "helperSetTheory"; *) *)
(* open helperNumTheory helperSetTheory; *)

(* open dependent theories *)
(* (* val _ = load "dividesTheory"; *) *)
(* (* val _ = load "gcdTheory"; *) *)
(* open arithmeticTheory dividesTheory gcdTheory; *)


(* ------------------------------------------------------------------------- *)
(* Basic Polynomials Documentation                                           *)
(* ------------------------------------------------------------------------- *)
(*
This package collects the basic definitions in one location, so that we can immediately say:

   |0| = (PolyRing r).sum.id
   |1| = (PolyRing r).prod.id
*)
(* Data type:
   A polynomial is just a list of coefficients from a Ring r.
   A polynomial is "weak" if it can have leading zeroes, i.e. not normalized.
   A normalized polynomial has leading coefficient nonzero, after applying poly_chop.

   Overloads:
   weak        = Weak r
   ||          = weak_pair r
   o           = weak_cmult r
   o           = weak_mult r
   >>          = poly_shift r
   neg         = weak_neg r
   zerop       = zero_poly r
   chop        = poly_chop r
   poly        = Poly r
   deg         = poly_degree r
   eval        = poly_eval r
   root        = poly_root r
   roots       = poly_roots r
   lead        = poly_lead r
   p ' k       = poly_coeff r p k
   PolyRing r  = poly_ring r
   p + q       = (PolyRing r).sum.op p q
   p * q       = (PolyRing r).prod.op p q
   c * p       = poly_cmult r c p
   |0|         = (PolyRing r).sum.id
   |1|         = (PolyRing r).prod.id
   ##          = (PolyRing r).sum.exp |1|
   **          = (PolyRing r).prod.exp
   poly_zero r = (PolyRing r).sum.id
   poly_one r  = (PolyRing r).prod.id
   poly_add r  = (PolyRing r).sum.op
   poly_mult r = (PolyRing r).prod.op
   poly_neg r  = (PolyRing r).sum.inv
   poly_num r  = (PolyRing r).sum.exp (poly_one r)
   poly_exp r  = (PolyRing r).prod.exp
*)
(* Definitions and Theorems (# are exported):

   Polynomial:
#  Weak_def          |- (!r. weak [] <=> T) /\ !r h t. weak (h::t) <=> h IN R /\ weak t
   weak_add_def      |- (!r q. [] || q = q) /\ (!v5 v4 r. (v4::v5) || [] = v4::v5) /\
                         !r qt qh pt ph. (ph::pt) || (qh::qt) = ph + qh::pt || qt
#  weak_cmult_def    |- (!r c. c o [] = []) /\ !r c h t. c o (h::t) = c * h::c o t
#  weak_neg_def      |- (!r. neg [] = []) /\ !r h t. neg (h::t) = -h::neg t
   poly_shift_def    |- (!r n. [] >> n = []) /\ (!v5 v4 r. (v4::v5) >> 0 = v4::v5) /\
                         !v7 v6 r n. (v6::v7) >> SUC n = #0::(v6::v7) >> n
   weak_mult_def     |- (!r q. [] o q = []) /\ !r h t q. (h::t) o q = h o q || t o q >> 1
#  zero_poly_def     |- (!r. zerop [] <=> T) /\ !r h t. zerop (h::t) <=> (h = #0) /\ zerop t
#  poly_chop_def     |- (!r. chop [] = []) /\ !r h t. chop (h::t) = if zerop (h::t) then [] else h::chop t

   Polynomials over a Ring:
#  Poly_def          |- (!r. poly [] <=> T) /\ !r h t. poly (h::t) <=> h IN R /\ poly t /\ ~zerop (h::t)
   poly_ring_def     |- !r. poly_ring r =
                        <|carrier := {p | poly p};
                              sum := <|carrier := {p | poly p}; op := (\p q. chop (p || q)); id := []|>;
                             prod := <|carrier := {p | poly p}; op := (\p q. chop (p o q)); id := chop [#1]|>
                         |>
   poly_ring_ids     |- !r. ( |0| = []) /\ ( |1| = chop [#1])
   poly_add_def      |- !p q. p + q = chop (p || q)
   poly_mult_def     |- !p q. p * q = chop (p o q)
   poly_cmult_def    |- !r c p. c * p = chop (c o p)

   poly_deg_def      |- !r p. deg p = if p = [] then 0 else PRE (LENGTH p)
#  poly_eval_def     |- (!r x. eval [] x = #0) /\ !r h t x. eval (h::t) x = h + eval t x * x
   poly_root_def     |- !r p x. root p x <=> (eval p x = #0)
   poly_roots_def    |- !r p. roots p = {x | x IN R /\ root p x}
   poly_lead_def     |- (!r. lead [] = #0) /\ !r h t. lead (h::t) = LAST (h::t)
#  poly_coeff_def    |- (!r n. [] ' n = #0) /\ !r h t n. (h::t) ' n =
                                     if deg (h::t) < n then #0 else EL n (h::t)

   Basic Theorems:
#  poly_zero              |- |0| = []
   poly_one               |- |1| = if #1 = #0 then [] else [#1]
   poly_zero_poly         |- poly |0|
   poly_deg_less          |- !p n. deg p < n ==> LENGTH p <= n
   poly_deg_le_length     |- !p n. deg p <= n ==> LENGTH p <= SUC n
   poly_roots_member      |- !r p x. x IN roots p <=> x IN R /\ root p x

   Theorems for Polynomials with #1 <> #0:
   poly_of_one_poly       |- !r. Ring r ==> (#1 <> #0 <=> poly [#1])
   poly_one_ne_poly_zero  |- !r. Ring r ==> (#1 <> #0 <=> |1| <> |0|)
   poly_one_eq_poly_zero  |- !r. Ring r ==> (( |1| = |0|) <=> (#1 = #0))
*)

(* ------------------------------------------------------------------------- *)
(* Polynomial -- as a list of ring/field elements.                           *)
(* ------------------------------------------------------------------------- *)

(* A polynomial is represented by a list of coefficients taken from the ring *)
val _ = type_abbrev ("poly", Type `:'a list`);

(* ------------------------------------------------------------------------- *)
(* Weal Polynomials.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Weak Polynomials are not normalized. *)
val Weak_def = Define`
  (Weak (r:'a ring) [] <=> T) /\
  (Weak (r:'a ring) ((h:'a)::(t:'a poly)) <=> (h IN R) /\ Weak r t)
`;
val _ = overload_on ("weak", ``Weak r``);

(* export simple case definition *)
val _ = export_rewrites ["Weak_def"];

(* ------------------------------------------------------------------------- *)
(* Weal Polynomial Pair Addition.                                            *)
(* ------------------------------------------------------------------------- *)

(* Pair addition of weak polynomial *)
val weak_add_def = Define`
  (weak_add (r:'a ring) [] q = q) /\
  (weak_add (r:'a ring) p [] = p) /\
  (weak_add (r:'a ring) (ph:'a :: pt:'a poly) (qh:'a :: qt:'a poly) = ph + qh :: weak_add r pt qt)
`;
(*
> val weak_add_def =
    |- (!r. weak_add r [] [] = []) /\
       (!v9 v8 f. weak_add r [] (v8::v9) = v8::v9) /\
       (!v5 v4 f. weak_add r (v4::v5) [] = v4::v5) /\
       !qt qh pt ph f. weak_add r (ph::pt) (qh::qt) = ph + qh::weak_add r pt qt : thm
*)
val _ = overload_on ("||", ``weak_add r``);
val _ = set_fixity "||" (Infixl 500); (* same as + in arithmeticScript.sml *)

(* the internal definition is modified, so don't export *)
(* val _ = export_rewrites ["weak_add_def"]; *)

(* ------------------------------------------------------------------------- *)
(* Weak Polynomial Scalar Multiplication                                     *)
(* ------------------------------------------------------------------------- *)

(* Scalar multiplication of a polynomial, i.e. c * (polynomial in x) *)
val weak_cmult_def = Define`
  (weak_cmult (r:'a ring) (c:'a) [] = []) /\
  (weak_cmult (r:'a ring) (c:'a) (h:'a :: t:'a poly) = c * h :: weak_cmult r c t)
`;
val _ = overload_on ("o", ``weak_cmult r``);

(* export simple case definition *)
val _ = export_rewrites ["weak_cmult_def"];

(* ------------------------------------------------------------------------- *)
(* Polynomial Negation.                                                      *)
(* ------------------------------------------------------------------------- *)

(* can we define neg directly as (poly_ring).sum.inv ?  Probably not. *)

(* Negation of a polynomial *)
val weak_neg_def = Define`
  (weak_neg (r:'a ring) [] = []) /\
  (weak_neg (r:'a ring) (h:'a :: t) = (- h) :: (weak_neg r t))
`;
(* overloading  *)
val _ = overload_on ("neg", ``weak_neg r``);

(* export simple case definition *)
val _ = export_rewrites ["weak_neg_def"];

(* ------------------------------------------------------------------------- *)
(* Polynomial Shifts                                                         *)
(* ------------------------------------------------------------------------- *)

(* Note: [] >> n = [] is essential for later weak_mult_rzero: p o [] = [] *)
(* Power multiplication of a polynomial, i.e. x^n * (polynomial in x), same as shifting. *)
val poly_shift_def = Define`
  (poly_shift (r:'a ring) [] n = []) /\
  (poly_shift (r:'a ring) (p:'a poly) 0 = p) /\
  (poly_shift (r:'a ring) (p:'a poly) (SUC n) = #0 :: poly_shift r p n)
`;
(*
> val poly_shift_def = |- (!r n. poly_shift r [] n = []) /\
                          (!v5 v4 r. poly_shift r (v4::v5) 0 = v4::v5) /\
                           !v7 v6 r n. poly_shift r (v6::v7) (SUC n) = #0::poly_shift r (v6::v7) n : thm
*)
val _ = overload_on (">>", ``poly_shift r``);
val _ = set_fixity ">>" (Infixr 700);
val _ = add_infix(">>", 700, HOLgrammars.RIGHT);
(* consistent with EXP in arithmeticTheory *)

(* the internal definition is modified, so don't export *)
(* val _ = export_rewrites ["poly_shift_def"]; *)

(* Multiplication of polynomials. This is symbolic polynomial evaluation. *)
val weak_mult_def = Define`
  (weak_mult (r:'a ring) [] (q:'a poly) = []) /\
  (weak_mult (r:'a ring) (h:'a :: t:'a poly) (q:'a poly) = (h o q) || (weak_mult r t q) >> 1)
`;
val _ = overload_on ("o", ``weak_mult r``);

(* export simple case definition *)
val _ = export_rewrites ["weak_mult_def"];

(* ------------------------------------------------------------------------- *)
(* Zero Polynomials - for normalization.                                     *)
(* ------------------------------------------------------------------------- *)

(* Zero polynomial definition *)
(*
val zero_poly_def = Define `zero_poly (r:'a ring) (p:'a poly) = EVERY (\c. c = #0) p`;
*)
(* Zero polynomial definition - recursive *)
val zero_poly_def = Define`
  (zero_poly (r:'a ring) [] <=> T) /\
  (zero_poly (r:'a ring) ((h:'a)::(t:'a poly)) <=> (h = #0) /\ (zero_poly r t))
`;
(* zero_poly is required for checking no division by zerop polynomial. *)
val _ = overload_on ("zerop", ``zero_poly r``);

(* export simple case definition *)
val _ = export_rewrites ["zero_poly_def"];

(* ------------------------------------------------------------------------- *)
(* Polynomial Normalization.                                                 *)
(* ------------------------------------------------------------------------- *)

(* Chopping of a polynomial for normalization (recursive) *)
val poly_chop_def = Define`
   (poly_chop (r:'a ring) [] = []) /\
   (poly_chop (r:'a ring) (h:'a :: t:'a poly) = if zerop (h::t) then [] else (h:: poly_chop r t))
`;
(* overloading  *)
val _ = overload_on ("chop", ``poly_chop r``);

(* Still simple case definition, although this leads to resolving zerop (h::t). But this is useful, use it. *)
val _ = export_rewrites ["poly_chop_def"];

(* ------------------------------------------------------------------------- *)
(* Polynomials over a Ring.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Polynomial p in ring r is either [], or not zerop (h::t). *)
val Poly_def = Define`
  (Poly (r:'a ring) [] <=> T) /\
  (Poly (r:'a ring) ((h:'a)::(t:'a poly)) <=> (h IN R) /\ Poly r t /\ ~ zerop (h::t))
`;
val _ = overload_on ("poly", ``Poly r``);

(* export simple case definition *)
val _ = export_rewrites ["Poly_def"];

(* ------------------------------------------------------------------------- *)
(* Polynomial Ring.                                                          *)
(* ------------------------------------------------------------------------- *)

(* Define ring of polynomials. *)
val poly_ring_def = Define`
  poly_ring (r:'a ring):'a poly ring =
   <| carrier := { p:'a poly | poly p };
          sum := <| carrier := { p:'a poly | poly p };
                         op := (\p q. chop (p || q));
                         id := []
                  |>;
         prod := <| carrier := { p:'a poly | poly p };
                         op := (\p q. chop (p o q));
                         id := chop [#1]
                  |>
    |>
`;
(*
- type_of ``poly_ring r``;
> val it = ``:'a poly ring`` : hol_type
*)

(* overload on R[x] *)
val _ = overload_on ("PolyRing", ``\r. poly_ring r``);

val _ = overload_on ("+", ``(PolyRing r).sum.op``);
val _ = overload_on ("*", ``(PolyRing r).prod.op``);
val _ = overload_on ("|0|", ``(PolyRing r).sum.id``);
val _ = overload_on ("|1|", ``(PolyRing r).prod.id``);

val _ = clear_overloads_on "##";
val _ = overload_on ("##", ``(PolyRing r).sum.exp |1|``);
val _ = overload_on ("**", ``(PolyRing r).prod.exp``);

(* Overloads for polynomial ring operations with parameter r *)
val _ = overload_on("poly_zero", ``\r. (PolyRing r).sum.id``);
val _ = overload_on("poly_one", ``\r. (PolyRing r).prod.id``);
val _ = overload_on("poly_add", ``\r. (PolyRing r).sum.op``);
val _ = overload_on("poly_mult", ``\r. (PolyRing r).prod.op``);
val _ = overload_on("poly_neg", ``\r. (PolyRing r).sum.inv``);
val _ = overload_on("poly_num", ``\r. (PolyRing r).sum.exp (poly_one r)``);
val _ = overload_on("poly_exp", ``\r. (PolyRing r).prod.exp``);

(* Theorem: poly_ring sum.id = |0| and prod.id = |1|. *)
(* Proof: by definition. *)
val poly_ring_ids = store_thm(
  "poly_ring_ids",
  ``!r:'a ring. ( |0| = []) /\ ( |1| = chop [#1])``,
  rw_tac std_ss[poly_ring_def]);

(* Theorem: Definition of p + q. *)
(* Proof: by poly_ring_def. *)
val poly_add_def = store_thm(
  "poly_add_def",
  ``!(p q):'a poly. p + q = chop (p || q)``,
  rw_tac std_ss[poly_ring_def]);

(* Theorem: Definition of p * q. *)
(* Proof: by poly_ring_def. *)
val poly_mult_def = store_thm(
  "poly_mult_def",
  ``!(p q):'a poly. p * q = chop (p o q)``,
  rw_tac std_ss[poly_ring_def]);

(* no export of rewrites to chop. *)
(* val _ = export_rewrites ["poly_add_def", "poly_mult_def"]; *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Scalar Multiplication                                          *)
(* ------------------------------------------------------------------------- *)

(* Scalar multiplication of a polynomial, i.e. c * (polynomial in x) *)
val poly_cmult_def = Define `poly_cmult (r:'a ring) (c:'a) (p:'a poly) = chop (c o p)`;
val _ = overload_on ("*", ``poly_cmult r``);

(* do not want to convert c * p to chop (c o p) always. *)
(* val _ = export_rewrites ["poly_cmult_def"]; *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Degree                                                         *)
(* ------------------------------------------------------------------------- *)

(* Degree of polynomial p, assumed nomralized. *)
val poly_deg_def = Define`
  poly_deg (r:'a ring) (p:'a poly) = if p = [] then 0 else PRE (LENGTH p)
`;
val _ = overload_on ("deg", ``poly_deg r``);

(* no export, no expand to PRE (LENGTH p) *)
(* val _ = export_rewrites ["poly_deg_def"]; *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Evaluation.                                                    *)
(* ------------------------------------------------------------------------- *)

(* Evaluate a polynomial p for a value x: Horner's method *)
(* This form causes a problem:
<<HOL message: more than one resolution of overloading was possible>>
<<HOL message: mk_functional: The following input rows (counting from zero) are inaccessible: 1. They have been ignored.>>

val poly_eval_def = Define`
  (poly_eval (r:'a ring) |0| x = #0) /\
  (poly_eval (r:'a ring) (h:'a :: t:'a poly) x = h + (poly_eval r t x) * x)
`;
*)
val poly_eval_def = Define`
  (poly_eval (r:'a ring) [] x = #0) /\
  (poly_eval (r:'a ring) (h:'a :: t:'a poly) x = h + (poly_eval r t x) * x)
`;
val _ = overload_on ("eval", ``poly_eval r``);

(* export simple case definition *)
val _ = export_rewrites ["poly_eval_def"];

(* ------------------------------------------------------------------------- *)
(* Polynomial Root.                                                          *)
(* ------------------------------------------------------------------------- *)

(* Root x of a polynomial p: p(x) = 0. *)
val poly_root_def = Define `poly_root (r:'a ring) (p:'a poly) (x:'a) = (eval p x = #0)`;

val _ = overload_on ("root", ``poly_root r``);

(* no export of conversion. *)
(* val _ = export_rewrites ["poly_root_def"]; *)

(* ------------------------------------------------------------------------- *)
(* Polynomial Roots as a set.                                                *)
(* ------------------------------------------------------------------------- *)

(* Roots of a polynomial p. *)
val poly_roots_def = Define `poly_roots (r:'a ring) (p:'a poly) = {x | x IN R /\ root p x}`;

val _ = overload_on ("roots", ``poly_roots r``);

(* no export of conversion. *)
(* val _ = export_rewrites ["poly_roots_def"]; *)

(* ------------------------------------------------------------------------- *)
(* Polynomial leading coefficient.                                           *)
(* ------------------------------------------------------------------------- *)

(* Leading coefficient of a polynomial (nonzero if normalized) *)
val poly_lead_def = Define`
  (poly_lead (r:'a ring) [] = #0) /\
  (poly_lead (r:'a ring) (h::t) = LAST (h::t))
`;
val _ = overload_on ("lead", ``poly_lead r``);

(* no export -- don't want expand to LAST every time *)
(* val _ = export_rewrites ["poly_lead_def"]; *)

(* ------------------------------------------------------------------------- *)
(* Polynomial coefficients.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Coefficient of a polynomial term. *)
(* This form has problem:
val poly_coeff_def = Define`
  (poly_coeff (r:'a ring) |0| n = #0) /\
  (poly_coeff (r:'a ring) (h::t:'a poly) n = if deg (h::t) < n then #0 else EL n (h::t))
`;
*)
val poly_coeff_def = Define`
  (poly_coeff (r:'a ring) [] n = #0) /\
  (poly_coeff (r:'a ring) (h::t:'a poly) n = if deg (h::t) < n then #0 else EL n (h::t))
`;
val _ = overload_on ("'", ``poly_coeff r``);
val _ = set_fixity "'" (Infixl 2000);

(* simple case defintion can export. *)
val _ = export_rewrites ["poly_coeff_def"];

(* ------------------------------------------------------------------------- *)
(* Basic Theorems.                                                           *)
(* ------------------------------------------------------------------------- *)

(* Theorem: |0| = []. *)
(* Proof: by poly_ring_def. *)
val poly_zero = store_thm(
  "poly_zero",
  ``|0| = []``,
  rw_tac std_ss[poly_ring_def]);

(* export as right side is simpler. *)
val _ = export_rewrites ["poly_zero"];

(* Theorem: |1| = if #1 = #0 then [] else [#1] *)
(* Prof: by poly_ring_def and poly_chop_def and zero_poly_def.
   If #1 = #0, chop [#0] = []     true by poly_chop_def, zero_poly_def.
   If #1 <> #0, chop [#1] = [#1]  true by poly_chop_def, zero_poly_def.
*)
val poly_one = store_thm(
  "poly_one",
  ``|1| = if #1 = #0 then [] else [#1]``,
  rw_tac std_ss[poly_ring_def, poly_chop_def, zero_poly_def]);

(* no export as right side is more complicated. *)
(* val _ = export_rewrites ["poly_one"]; *)

(* Theorem: poly |0| *)
(* Proof: by Poly_def and poly_zero. *)
val poly_zero_poly = store_thm(
  "poly_zero_poly",
  ``poly |0|``,
  rw[]);

(* Theorem: poly p /\ 0 < n /\ deg p < n <=> lead p <> #0 /\ LENGTH p <= n *)
(* Proof:
   By poly_deg_def, this is to show:
   p <> [] /\ PRE (LENGTH p) < n ==> LENGTH p <= n
   Since p <> [],
      LENGTH p <> 0      by LENGTH_NIL
   or 0 < LENGTH p
   Now,      PRE (LENGTH p) < n
   ==> SUC (PRE (LENGTH p)) < SUC n    by LESS_MONO_EQ
   ==>              LENGTH p < SUC n   by SUC_PRE: 0 < m <=> (SUC (PRE m) = m)
   ==>              LENGTH p <= n      by LESS_LESS_SUC
*)
val poly_deg_less = store_thm(
  "poly_deg_less",
  ``!p n. deg p < n ==> LENGTH p <= n``,
  rw[poly_deg_def]);

(* Theorem: deg p <= n ==> LENGTH p <= SUC n *)
(* Proof:
   If p = [], true by deg [] = 0    by poly_deg_of_zero.
   If p <> [], LENGTH p <> 0        by LENGTH_NIL
                 deg p <= n
         PRE(LENGTH p) <= n         by poly_deg_def
    SUC(PRE(LENGTH p)) <= SUC n     by arithmetic
              LENGTH p <= SUC n     by SUC_PRE
*)
val poly_deg_le_length = store_thm(
  "poly_deg_le_length",
  ``!p n. deg p <= n ==> LENGTH p <= SUC n``,
  rw[poly_deg_def]);

(* Theorem: x IN roots p <=> x IN R /\ root p x *)
(* Proof: by poly_roots_def. *)
val poly_roots_member = store_thm(
  "poly_roots_member",
  ``!r:'a ring. !p x. x IN roots p <=> x IN R /\ root p x``,
  rw[poly_roots_def]);

(* ------------------------------------------------------------------------- *)
(* Theorems for Polynomials with #1 <> #0.                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: #1 <> #0 iff poly [#1] *)
(* Proof: If #1 <> #0,
      weak |1|        by weak_one
      |1| <> |0|      by poly_one_ne_zero
      LAST |1| = #1   by LAST_CONS
               <> #0  by given
   Hence true by poly_def_alt.
   If poly [#1], LAST [#1] <> #0 by poly_one_ne_zero, poly_def_alt
   Hence true by LAST_CONS
*)
val poly_of_one_poly = store_thm(
  "poly_of_one_poly",
  ``!r:'a ring. Ring r ==> (#1 <> #0 <=> poly [#1])``,
  rw[]);

(* Theorem: #1 <> #0 iff |1| <> |0| *)
(* Proof:
   If #1 <> #0,
      |1| = [#1]  by poly_one
            <> [] = |0|  by poly_zero
   If |1| <> |0| but #1 = #0,
      |1| = []     by poly_one
      but |0| = [] by poly_zero
      hence contradiction.
*)
val poly_one_ne_poly_zero = store_thm(
  "poly_one_ne_poly_zero",
  ``!r:'a ring. Ring r ==> (#1 <> #0 <=> |1| <> |0|)``,
  rw[poly_one]);

(* Theorem: |1| = |0| iff #1 = #0 *)
(* Proof: by poly_one_ne_poly_zero. *)
val poly_one_eq_poly_zero = store_thm(
  "poly_one_eq_poly_zero",
  ``!r:'a ring. Ring r ==> (( |1| = |0|) <=> (#1 = #0))``,
  metis_tac[poly_one_ne_poly_zero]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
