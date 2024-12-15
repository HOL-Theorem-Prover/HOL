(* ------------------------------------------------------------------------- *)
(* Vector Space                                                              *)
(* ------------------------------------------------------------------------- *)

(*

Overall Idea:
* Have a list of vectors, called basis.
* Have a list of scalars, called stick. Let sticks r m = set of sticks of length m.
* Given a basis b, with m = LENGTH b, get the (sticks r m).
* Combine stick n IN (sticks r m) and basis into pairs:  ZIP (n, b)
* Turn the list of pairs into a list of vectors by scalar multiplication: MAP op (ZIP (n, b))
* Sum up this list of vectors to give a final vector: VSUM (MAP op (ZIP (n, b)))
  where VSUM [] = |0|
  and   VSUM (h::t) = h || VSUM t
* The set of vectors given by this process is the SpanSpace of the basis.
  SpanSpace r g op b = <| carrier := { VSUM (MAP2 op n, b) | n | n IN (sticks r (LENGTH b)) };
                               op := g.op
                               id := g.id
                        |>
* Then show: !b. VSpace r (SpanSpace r g op b) op
* And show: VSpace r g op = SpanSpace r g op (SET_TO_LIST V), i.e. all vectors can be a basis.
* Thus the set:  s = { b | VSpace r g op = SpanSpace r g op b } is non-empty.
  And  IMAGE CARD s  is a bunch of numbers, none of them zero.
  Let  DIM (VSpace r g op) = MIN_SET (IMAGE CARD { b | VSpace r g op = SpanSpace r g op b })
* By IN_IMAGE, there is a basis b such that CARD b = DIM (VSpace r g op).
* Then show: CARD V = (CARD R) ** DIM (VSpace r g op)
  Possibly, this involves showing n IN (sticks r (LENGTH b)) --> VSUM (MAP op (ZIP (n, b))) is INJ.

*)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "VectorSpace";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory;

open groupTheory fieldTheory;

(* ------------------------------------------------------------------------- *)
(* Vector Space Documentation                                                *)
(* ------------------------------------------------------------------------- *)
(* Overload:
   o       = op
   V       = g.carrier
   |0|     = g.id
   u || v  = g.op u v
   n + m   = stick_add r n m
   n - m   = stick_sub r n m
   $- n    = stick_neg r n
   c * n   = stick_cmult r c n
*)
(* Definitions and Theorems (# are exported):

   Vector Space:
   VSpace_def   |- !r g op. VSpace r g  op <=>
                            Field r /\ AbelianGroup g /\
                            (!a v. a IN R /\ v IN V ==> a o v IN V) /\
                            (!a b v. a IN R /\ b IN R /\ v IN V ==> (a o b o v = (a * b) o v)) /\
                            (!v. v IN V ==> (#1 o v = v)) /\
                            (!a u v. a IN R /\ u IN V /\ v IN V ==> (a o (u || v) = a o u || a o v)) /\
                             !a b v. a IN R /\ b IN R /\ v IN V ==> ((a + b) o v = a o v || b o v)
   Basic Properties:
   vspace_has_field          |- !r op g. VSpace r g op ==> Field r
   vspace_has_abelian_group  |- !r op g. VSpace r g op ==> AbelianGroup g
   vspace_cmult_vector       |- !r op g. VSpace r g op ==> !a v. a IN R /\ v IN V ==> a o v IN V
   vspace_cmult_cmult        |- !r op g. VSpace r g op ==> !a b v. a IN R /\ b IN R /\ v IN V ==>
                                                           (a o b o v = (a * b) o v)
   vspace_cmult_lone         |- !r op g. VSpace r g op ==> !v. v IN V ==> (#1 o v = v)
   vspace_cmult_radd         |- !r op g. VSpace r g op ==> !a u v. a IN R /\ u IN V /\ v IN V ==>
                                                           (a o (u || v) = a o u || a o v)
   vspace_cmult_ladd         |- !r op g. VSpace r g op ==> !a b v. a IN R /\ b IN R /\ v IN V ==>
                                                           ((a + b) o v = a o v || b o v)
   vspace_has_group          |- !r g op. VSpace r g op ==> Group g
   vspace_has_zero           |- !r g op. VSpace r g op ==> |0| IN V
   vspace_vadd_vector        |- !r g op. VSpace r g op ==> !u v. u IN V /\ v IN V ==> u || v IN V
   vspace_vadd_lzero         |- !r g op. VSpace r g op ==> !v. v IN V ==> ( |0| || v = v)
   vspace_vadd_rzero         |- !r g op. VSpace r g op ==> !v. v IN V ==> (v || |0| = v)
   vspace_vadd_comm          |- !r g op. VSpace r g op ==> !u v. u IN V /\ v IN V ==> (u || v = v || u
   vspace_vadd_assoc         |- !r g op. VSpace r g op ==> !u v w. u IN V /\ v IN V /\ w IN V ==>
                                                           (u || v || w = u || (v || w))
   vspace_cmult_lzero        |- !r g op. VSpace r g op ==> !v. v IN V ==> (#0 o v = |0|)
   vspace_cmult_rzero        |- !r g op. VSpace r g op ==> !a. a IN R ==> (a o |0| = |0|)
   vspace_cmult_eq_zero      |- !r g op. VSpace r g op ==> !a v. a IN R /\ v IN V ==>
                                                           ((a o v = |0|) <=> (a = #0) \/ (v = |0|))
   vspace_vsub_eq_zero       |- !r g op. VSpace r g op ==>
                                !u v. u IN V /\ v IN V ==> ((u = v) <=> (u || -#1 o v = |0|))
   vspace_vsub_eq_zero_alt   |- !r g op. VSpace r g op ==>
                                !u v. u IN V /\ v IN V ==> ((u = v) <=> (-#1 o u || v = |0|))
   vspace_vadd_eq_zero       |- !r g op. VSpace r g op ==>
                                !u v. u IN V /\ v IN V ==> ((u || v = |0|) <=> (u = -#1 o v))
   vspace_vadd_eq_zero_alt   |- !r g op. VSpace r g op ==>
                                !u v. u IN V /\ v IN V ==> ((u || v = |0|) <=> (v = -#1 o u))

   Sticks:
   sticks_def      |- !r m. sticks r m = {l | set l SUBSET R /\ (LENGTH l = m)}
   sticks_0        |- !r. sticks r 0 = {[]}
   sticks_suc      |- !r. sticks r (SUC n) = IMAGE (\(e,l). e::l) (R CROSS sticks r n)
   sticks_finite   |- !r. FINITE R ==> !n. FINITE (sticks r n)
   sticks_card     |- !r. FINITE R ==> !n. CARD (sticks r n) = CARD R ** n
   sticks_1        |- !r. sticks r 1 = IMAGE (\c. [c]) R
   sticks_1_member |- !r p. p IN sticks r 1 <=> ?c. c IN R /\ (p = [c])
   sticks_0_member |- !r p. p IN sticks r 0 <=> (p = [])

   Stick Properties:
   stick_length    |- !r l n. l IN sticks r n ==> (LENGTH l = n)
   stick_cons      |- !r l n. l IN sticks r (SUC n) <=> ?h t. h IN R /\ t IN sticks r n /\ (l = h::t)
   stick_all_zero  |- !r g op. VSpace r g op ==> !n. GENLIST (\j. #0) n IN sticks r n
   stick_insert_element
                   |- !r h t n. h IN R /\ t IN sticks r (n - 1) ==>
                      !k. k < n ==> TAKE k t ++ [h] ++ DROP k t IN sticks r n
   stick_components_stick
                   |- !r t n. t IN sticks r n ==> !k. k < n ==>
                              EL k t IN R /\ TAKE k t IN sticks r k /\ DROP (SUC k) t IN sticks r (n - SUC k)
   stick_snoc      |- !r l n. l IN sticks r (SUC n) <=>
                              ?h t. h IN R /\ t IN sticks r n /\ (l = SNOC h t)

   Stick Addition:
   stick_add_def        |- (!r. [] + [] = []) /\ !t' t r h' h. (h::t) + (h'::t') = h + h'::t + t'
   stick_add_nil_nil    |- !r. [] + [] = []
   stick_add_cons_cons  |- !t' t r h' h. (h::t) + (h'::t') = h + h'::t + t'
   stick_add_length     |- !r. Field r ==> !n n1 n2. n1 IN sticks r n /\ n2 IN sticks r n ==>
                                                 n1 + n2 IN sticks r n

   Stick Negation:
   stick_neg_def      |- (!r. $- [] = []) /\ !r h t. $- (h::t) = -h:: $- t
   stick_neg_zero     |- !r. $- [] = []
   stick_neg_cons     |- !r h t. $- (h::t) = -h:: $- t
   stick_neg_length   |- !r. Field r ==> !n n1. n1 IN sticks r n ==> $- n1 IN sticks r n

   Stick Scalar Multiplication:
   stick_cmult_def    |- (!r c. c * [] = []) /\ !r c h t. c * (h::t) = c * h::c * t
   stick_cmult_zero   |- !r c. c * [] = []
   stick_cmult_cons   |- !r c h t. c * (h::t) = c * h::c * t
   stick_cmult_length |- !r. Field r ==> !n c n1. c IN R /\ n1 IN sticks r n ==> c * n1 IN sticks r n

   Stick Subtraction:
   stick_sub_def      |- (!r. [] - [] = []) /\ !t' t r h' h. (h::t) - (h'::t') = h - h'::t - t'
   stick_sub_nil_nil  |- !r. [] - [] = []
   stick_sub_cons_cons|- !t' t r h' h. (h::t) - (h'::t') = h - h'::t - t'
   stick_sub_alt      |- !r. Field r ==> !n n1 n2. n1 IN sticks r n /\ n2 IN sticks r n ==>
                                            (n1 - n2 = n1 + $- n2)
   stick_sub_length   |- !r. Field r ==> !n n1 n2. n1 IN sticks r n /\ n2 IN sticks r n ==>
                                            n1 - n2 IN sticks r n
   stick_eq_property  |- !r. Field r ==> !n n1 n2. n1 IN sticks r n /\ n2 IN sticks r n ==>
                                            ((n1 = n2) <=> !k. k < n ==> (EL k (n1 - n2) = #0))

*)

(* ------------------------------------------------------------------------- *)
(* Vector Space                                                              *)
(* ------------------------------------------------------------------------- *)

(* Vector Space over a Field:
   - a set of scalars (field elements), a set of vectors.
   - vectors have addition, form an abelian group.
   - scalars can multiply into vectors to give vectors.
   - scalars and vectors can distrbute over each other.
*)

(* Axioms of Vector Space *)
val VSpace_def = Define`
  VSpace (r:'a field) (g:'b group) (op:'a -> 'b -> 'b) <=>
     Field r /\ (* scalars from a field *)
     AbelianGroup g /\ (* vectors form a commutative additive group *)
     (!a v. a IN R /\ v IN g.carrier ==> (op a v) IN g.carrier) /\ (* scalar multiplication with vector gives vector *)
     (!a b v. a IN R /\ b IN R /\ v IN g.carrier ==> (op a (op b v) = op (a * b) v)) /\ (* compatibility of scalar multiplication *)
     (!v. v IN g.carrier ==> (op #1 v = v)) /\ (* identity of scalar multiplication *)
     (!a u v. a IN R /\ u IN g.carrier /\ v IN g.carrier ==>
       (op a (g.op u v) = g.op (op a u) (op a v))) /\ (* distribution of scalar over vector *)
     (!a b v. a IN R /\ b IN R /\ v IN g.carrier ==>
       (op (a + b) v = g.op (op a v) (op b v))) (* distribution of vector over scalar *)
`;

(* Overloads for convenience *)
val _ = temp_overload_on ("o", ``(op:'a -> 'b -> 'b)``);
val _ = temp_overload_on ("V", ``(g:'b group).carrier``);
val _ = temp_overload_on ("||", ``(g:'b group).op``);
val _ = temp_overload_on ("|0|", ``(g:'b group).id``);
val _ = set_fixity "||" (Infixl 500); (* same as + in arithmeticScript.sml *)

(*
> VSpace_def;
val it = |- !r g op. VSpace r g op <=>
     Field r /\ AbelianGroup g /\
     (!a v. a IN R /\ v IN V ==> a o v IN V) /\
     (!a b v. a IN R /\ b IN R /\ v IN V ==> (a o b o v = (a * b) o v)) /\
     (!v. v IN V ==> (#1 o v = v)) /\
     (!a u v. a IN R /\ u IN V /\ v IN V ==> (a o (u || v) = a o u || a o v)) /\
     !a b v. a IN R /\ b IN R /\ v IN V ==> ((a + b) o v = a o v || b o v): thm
*)

(* ------------------------------------------------------------------------- *)
(* Basic Properties.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: VSpace r g op ==> Field r *)
val vspace_has_field = save_thm("vspace_has_field",
  VSpace_def |> SPEC_ALL |> (#1 o EQ_IMP_RULE) |> UNDISCH |> CONJUNCTS |> el 1 |> DISCH_ALL |> GEN_ALL);
(* > val vspace_has_field = |- !r op g. VSpace r g op ==> Field r : thm *)

(* Theorem: VSpace r g op ==> AbelianGroup g *)
val vspace_has_abelian_group = save_thm("vspace_has_abelian_group",
  VSpace_def |> SPEC_ALL |> (#1 o EQ_IMP_RULE) |> UNDISCH |> CONJUNCTS |> el 2 |> DISCH_ALL |> GEN_ALL);
(* > val vspace_has_abelian_group = |- !r op g. VSpace r g op ==> AbelianGroup g : thm *)

(* Theorem: VSpace r g op ==> !a v. a IN R /\ v IN V ==> a o v IN V *)
val vspace_cmult_vector = save_thm("vspace_cmult_vector",
  VSpace_def |> SPEC_ALL |> (#1 o EQ_IMP_RULE) |> UNDISCH |> CONJUNCTS |> el 3 |> DISCH_ALL |> GEN_ALL);
(* > val vspace_cmult_vector = |- !r op g. VSpace r g op ==> !a v. a IN R /\ v IN V ==> a o v IN V : thm *)

(* Theorem: VSpace r g op ==> !a b v. a IN R /\ b IN R /\ v IN V ==> (a o b o v = (a * b) o v) *)
val vspace_cmult_cmult = save_thm("vspace_cmult_cmult",
  VSpace_def |> SPEC_ALL |> (#1 o EQ_IMP_RULE) |> UNDISCH |> CONJUNCTS |> el 4 |> DISCH_ALL |> GEN_ALL);
(* > val vspace_cmult_cmult = |- !r op g. VSpace r g op ==>
         !a b v. a IN R /\ b IN R /\ v IN V ==> (a o b o v = (a * b) o v) : thm *)

(* Theorem: VSpace r g op ==> !v. v IN V ==> (#1 o v = v) *)
val vspace_cmult_lone = save_thm("vspace_cmult_lone",
  VSpace_def |> SPEC_ALL |> (#1 o EQ_IMP_RULE) |> UNDISCH |> CONJUNCTS |> el 5 |> DISCH_ALL |> GEN_ALL);
(* > val vspace_cmult_lone = |- !r op g. VSpace r g op ==> !v. v IN V ==> (#1 o v = v) : thm *)

(* Theorem: VSpace r g op ==> !a u v. a IN R /\ u IN V /\ v IN V ==> (a o (u || v) = a o u || a o v) *)
val vspace_cmult_radd = save_thm("vspace_cmult_radd",
  VSpace_def |> SPEC_ALL |> (#1 o EQ_IMP_RULE) |> UNDISCH |> CONJUNCTS |> el 6 |> DISCH_ALL |> GEN_ALL);
(* > val vspace_cmult_radd = |- !r op g. VSpace r g op ==> !a u v. a IN R /\ u IN V /\ v IN V ==>
         (a o (u || v) = a o u || a o v) : thm *)

(* Theorem: VSpace r g op ==> !a b v. a IN R /\ b IN R /\ v IN V ==> ((a + b) o v = a o v || b o v) *)
val vspace_cmult_ladd = save_thm("vspace_cmult_ladd",
  VSpace_def |> SPEC_ALL |> (#1 o EQ_IMP_RULE) |> UNDISCH |> CONJUNCTS |> el 7 |> DISCH_ALL |> GEN_ALL);
(* > val vspace_cmult_ladd = |- !r op g. VSpace r g op ==> !a b v. a IN R /\ b IN R /\ v IN V ==>
         ((a + b) o v = a o v || b o v) : thm *)

(* Theorem: VSpace r g op ==> Group g *)
(* Proof: by vspace_has_abelian_group, AbelianGroup_def. *)
val vspace_has_group = store_thm(
  "vspace_has_group",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> Group g``,
  metis_tac[vspace_has_abelian_group, AbelianGroup_def]);

(* Theorem: VSpace r g op ==> |0| IN V *)
(* Proof: by vspace_has_group, group_id_element. *)
val vspace_has_zero = store_thm(
  "vspace_has_zero",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> |0| IN V``,
  metis_tac[vspace_has_group, group_id_element]);

(* Theorem: VSpace r g op ==> !u v. u IN V /\ v IN V ==> u || v IN V *)
(* Proof: by vspace_has_group, group_op_element. *)
val vspace_vadd_vector = store_thm(
  "vspace_vadd_vector",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !u v. u IN V /\ v IN V ==> u || v IN V``,
  metis_tac[vspace_has_group, group_op_element]);

(* Theorem: VSpace r g op ==> !v. v IN V ==> ( |0| || v = v) *)
(* Proof: by vspace_has_group, group_lid. *)
val vspace_vadd_lzero = store_thm(
  "vspace_vadd_lzero",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !v. v IN V ==> ( |0| || v = v)``,
  metis_tac[vspace_has_group, group_lid]);

(* Theorem: VSpace r g op ==> !v. v IN V ==> (v || |0| = v) *)
(* Proof: by vspace_has_group, group_rid. *)
val vspace_vadd_rzero = store_thm(
  "vspace_vadd_rzero",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !v. v IN V ==> (v || |0| = v)``,
  metis_tac[vspace_has_group, group_rid]);

(* Theorem: VSpace r g op ==> !u v. u IN V /\ v IN V ==> (u || v = v || u) *)
(* Proof: by vspace_has_abelian_group, AbelianGroup_def. *)
val vspace_vadd_comm = store_thm(
  "vspace_vadd_comm",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
    !u v. u IN V /\ v IN V ==> (u || v = v || u)``,
  metis_tac[vspace_has_abelian_group, AbelianGroup_def]);

(* Theorem: VSpace r g op ==> !u v w. u IN V /\ v IN V /\ w IN V ==> (u || v || w = u || (v || w)) *)
(* Proof: by vspace_has_group, group_assoc. *)
val vspace_vadd_assoc = store_thm(
  "vspace_vadd_assoc",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
    !u v w. u IN V /\ v IN V /\ w IN V ==> (u || v || w = u || (v || w))``,
  metis_tac[vspace_has_group, group_assoc]);

(* Theorem: #0 o v = |0| *)
(* Proof:
   v = #1 o v              by vspace_cmult_lone
     = (#0 + #1) o v       by field_add_lzero
     = #0 o v || #1 o v    by vspace_cmult_ladd
     = #0 o v || v         by vspace_cmult_lone
   hence #0 o v = |0|      by group_rid_unique
*)
val vspace_cmult_lzero = store_thm(
  "vspace_cmult_lzero",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !v. v IN V ==> (#0 o v = |0|)``,
  rpt strip_tac >>
  `Field r /\ Group g` by metis_tac[VSpace_def, AbelianGroup_def] >>
  `#0 IN R /\ #1 IN R` by rw[] >>
  `#0 o v IN V` by metis_tac[vspace_cmult_vector] >>
  `v = #1 o v` by metis_tac[vspace_cmult_lone] >>
  `_ = (#0 + #1) o v` by rw[] >>
  `_ = (#0 o v) || (#1 o v)` by rw[vspace_cmult_ladd] >>
  `_ = #0 o v || v` by metis_tac[vspace_cmult_lone] >>
  metis_tac[group_lid_unique]);

(* Theorem: a IN R ==> a o |0| = |0| *)
(* Proof:
     a o |0|
   = a o ( |0| || |0|)      by group_id_id
   = a o |0| || a o |0|    by vspace_cmult_radd
   hence a o |0}= |0|      by group_id_fix
*)
val vspace_cmult_rzero = store_thm(
  "vspace_cmult_rzero",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !a. a IN R ==> (a o |0| = |0|)``,
  rpt strip_tac >>
  `Group g` by metis_tac[vspace_has_group] >>
  `|0| IN V` by rw[] >>
  `a o |0| IN V` by metis_tac[vspace_cmult_vector] >>
  `a o |0| = a o ( |0| || |0|)` by rw[group_id_id] >>
  `_ = a o |0| || a o |0|` by metis_tac[vspace_cmult_radd] >>
  metis_tac[group_id_fix]);

(* Theorem: a IN R /\ v IN V ==> a o v = |0| <=> a = #0  or v = |0| *)
(* Proof:
   If part: a IN R /\ v IN V /\ a o v = |0| ==> a = #0  or v = |0|
   If a = #0, this is trivially true.
   If a <> #0, |/a exists, and |/a * a = #1
   v = #1 o v                 by vspace_cmult_lone
     = ( |/a * a) o v          by field_mult_linv
     = |/a * (a o v)          by vspace_cmult_cmult
     = |/a * |0|              by given
     = |0|                    by vspace_cmult_rzero
   Only-if part: a IN R /\ v IN V /\ a = #0  or v = |0| ==> a o v = |0|
   If a = #0, #0 o v = |0|    by vspace_cmult_lzero
   If v = |0|, a o |0| = |0|  by vspace_cmult_rzero
*)
val vspace_cmult_eq_zero = store_thm(
  "vspace_cmult_eq_zero",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
    !a v. a IN R /\ v IN V ==> ((a o v = |0|) <=> (a = #0) \/ (v = |0|))``,
  rw[EQ_IMP_THM] >| [
    `Field r` by metis_tac[vspace_has_field] >>
    spose_not_then strip_assume_tac >>
    `a IN R+` by rw[field_nonzero_eq] >>
    `|/a IN R` by rw[] >>
    `v = #1 o v` by metis_tac[vspace_cmult_lone] >>
    metis_tac[field_mult_linv, vspace_cmult_cmult, vspace_cmult_rzero],
    metis_tac[vspace_cmult_lzero],
    metis_tac[vspace_cmult_rzero]
  ]);

(* Theorem: u IN V /\ v IN V ==> ((u = v) <=> (u || (- #1) o v = |0|)) *)
(* Proof:
   If part: u = v ==> u || -#1 o v = |0|
         u || -#1 o v
       = u || -#1 o u               by given
       = #1 o u || -#1 o u          by vspace_cmult_lone
       = (#1 + -#1) o u             by vspace_cmult_ladd
       = #0 o u                     by field_add_rneg
       = |0|                        by vspace_cmult_lzero
   Only-if part: u || -#1 o v = |0| ==> u = v
         u
       = u || |0|                   by vspace_vadd_rzero
       = u || #0 o v                by vspace_cmult_lzero
       = u || (-#1 + #1) o v        by field_add_lneg
       = u || (-#1 o v || #1 o v)   by vspace_cmult_ladd
       = u || (-#1 o v || v)        by vspace_cmult_lone
       = (u || -#1 o v) || v        by vspace_vadd_assoc
       = |0| || v                   by given
       = v                          by vspace_vadd_lzero
*)
val vspace_vsub_eq_zero = store_thm(
  "vspace_vsub_eq_zero",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
    !u v. u IN V /\ v IN V ==> ((u = v) <=> (u || (- #1) o v = |0|))``,
  rpt strip_tac >>
  `Field r` by metis_tac[vspace_has_field] >>
  rw[EQ_IMP_THM] >| [
    `u || -#1 o u = (#1 o u) || -#1 o u` by metis_tac[vspace_cmult_lone] >>
    `_ = (#1 + -#1) o u ` by rw[vspace_cmult_ladd] >>
    rw[vspace_cmult_lzero],
    `#1 IN R /\ -#1 IN R` by rw[] >>
    `-#1 o v IN V` by metis_tac[vspace_cmult_vector] >>
    `u = u || #0 o v` by metis_tac[vspace_vadd_rzero, vspace_cmult_lzero] >>
    `_ = u || (-#1 + #1) o v` by rw[] >>
    metis_tac[vspace_cmult_ladd, vspace_cmult_lone, vspace_vadd_assoc, vspace_vadd_lzero]
  ]);

(* Theorem: u IN V /\ v IN V ==> ((u = v) <=> ((- #1) o u || v = |0|)) *)
(* Proof:
   Since -#1 o u IN V                           by vspace_cmult_vector
     and (- #1) o u || v = v || (- #1) o u      by vspace_vadd_comm
   Hence the result follows by exchange of u, v in vspace_vsub_eq_zero.
*)
val vspace_vsub_eq_zero_alt = store_thm(
  "vspace_vsub_eq_zero_alt",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
    !u v. u IN V /\ v IN V ==> ((u = v) <=> ((- #1) o u || v = |0|))``,
  rpt strip_tac >>
  `Field r` by metis_tac[vspace_has_field] >>
  `-#1 IN R` by rw[] >>
  `-#1 o u IN V` by metis_tac[vspace_cmult_vector] >>
  metis_tac[vspace_vsub_eq_zero, vspace_vadd_comm]);

(* Theorem: u IN V /\ v IN V ==> ((u || v = |0|) <=> (u = (- #1) o v)) *)
(* Proof:
   If part: u || v = |0| ==> u = -#1 o v
        u
      = u || |0|                   by vspace_vadd_rzero
      = u || (v || (-#1) o v)      by vspace_vsub_eq_zero
      = (u || v) || (-#1) o v      by vspace_vadd_assoc
      = |0| || (-#1) o v           by given
      = -#1 o v                    by vspace_vadd_lzero
   Only-if part: u = -#1 o v ==> u || v = |0|
        u || v
      = -#1 o v || v               by given
      = |0|                        by vspace_vsub_eq_zero_alt
*)
val vspace_vadd_eq_zero = store_thm(
  "vspace_vadd_eq_zero",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
    !u v. u IN V /\ v IN V ==> ((u || v = |0|) <=> (u = (- #1) o v))``,
  rpt strip_tac >>
  `Field r` by metis_tac[vspace_has_field] >>
  rw[EQ_IMP_THM] >| [
    `-#1 IN R` by rw[] >>
    `-#1 o v IN V` by metis_tac[vspace_cmult_vector] >>
    metis_tac[vspace_vadd_rzero, vspace_vsub_eq_zero, vspace_vadd_assoc, vspace_vadd_lzero],
    rw[GSYM vspace_vsub_eq_zero_alt]
  ]);

(* Theorem: u IN V /\ v IN V ==> ((u || v = |0|) <=> (v = (- #1) o u)) *)
(* Proof:
   Since u || v = v || u                        by vspace_vadd_comm
   Hence the result follows by exchange of u, v in vspace_vadd_eq_zero.
*)
val vspace_vadd_eq_zero_alt = store_thm(
  "vspace_vadd_eq_zero_alt",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
    !u v. u IN V /\ v IN V ==> ((u || v = |0|) <=> (v = (- #1) o u))``,
  metis_tac[vspace_vadd_eq_zero, vspace_vadd_comm]);

(* ------------------------------------------------------------------------- *)
(* Sticks -- a stick is a list of scalars of fixed width.                    *)
(* ------------------------------------------------------------------------- *)

(* Sticks is a set of vectors of length m *)
val sticks_def = Define`
  sticks (r:'a field) (m:num) = { (l:'a list) | (set l) SUBSET R /\ (LENGTH l = m) }
`;

(* Theorem: sticks r 0 = {[]} *)
(* Proof:
   This is to show: set x SUBSET R /\ (LENGTH x = 0) <=> (x = [])
   If part: set x SUBSET R /\ (LENGTH x = 0) ==> (x = [])
     Since LENGHT = 0, x = []   by LENGTH_NIL.
   Only-if part: x = [] ==> set x SUBSET R /\ (LENGTH x = 0)
     set [] = {}                by LIST_TO_SET
     and {} SUBSET R            by EMPTY_SUBSET
    also LENGTH [] = 0          by LENGTH
*)
val sticks_0 = store_thm(
  "sticks_0",
  ``!r:'a field. sticks r 0 = {[]}``,
  rw[sticks_def, EXTENSION, EQ_IMP_THM, LENGTH_NIL]);

(* Theorem: sticks r (SUC n) = IMAGE (\(e,l). e :: l) (R CROSS sticks r n) *)
(* Proof:
   After expanding by definitions, this is to show:
   (1) set (h::l') SUBSET R ==> h IN R /\ set l' SUBSET R
       set (h::l') = h INSERT set l'     by LIST_TO_SET_THM
           h INSERT set l' SUBSET R
       <=> h IN R /\ set l' SUBSET R     by INSERT_SUBSET
   (2) p_1 IN R /\ set p_2 SUBSET R ==> set (p_1::p_2) SUBSET R
           p_1 IN R /\ set p_2 SUBSET R
       <=> p_1 INSERT set p_2 SUBSET R   by INSERT_SUBSET
       <=> set (p_1 :: p_2) SUBSET R     by LIST_TO_SET_THM
*)
val sticks_suc = store_thm(
  "sticks_suc",
  ``!r:'a field. sticks r (SUC n) = IMAGE (\(e,l). e :: l) (R CROSS sticks r n)``,
  rw[sticks_def, EXTENSION, pairTheory.EXISTS_PROD, LENGTH_CONS] >>
  metis_tac[LIST_TO_SET_THM, INSERT_SUBSET]);

(* Theorem: FINITE R ==> !n. FINITE (sticks r n). *)
(* Proof: by induction on n.
   Base case: FINITE (sticks r 0)
     Since sticks r 0 = {[]}                      by sticks_0
     Hence true                                   by FINITE_SING
   Step case: FINITE R /\ FINITE (sticks r n) ==> FINITE (sticks r (SUC n))
       sticks r (SUC n)
     = IMAGE (\(e,l). e::l) (R CROSS sticks r n)  by sticks_suc
     Given FINITE R, and FINITE (sticks r n)      by induction hypothesis
     so    FINITE (R CROSS (sticks r n))          by FINITE_CROSS
     Hence true by IMAGE_FINITE.
*)
val sticks_finite = store_thm(
  "sticks_finite",
  ``!r:'a field. FINITE R ==> !n. FINITE (sticks r n)``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[sticks_0] >>
  rw[sticks_suc]);

(* Theorem: FINITE R ==> CARD (sticks r n) = (CARD R) ** n. *)
(* Proof: by induction on n.
   Base case: CARD (sticks r 0) = CARD R ** 0
     Since sticks r 0 = {[]}                            by sticks_0
     CARD {[]} = 1 = CARD R ** 0                        by CARD_SING, EXP
   Step case: FINITE R /\ CARD (sticks r n) = CARD R ** n ==>
                          CARD (sticks r (SUC n)) = CARD R ** SUC n
     Note that (\(e,l). e::l) x = (\(e,l). e::l) y <=> x = y by LIST_EQ, an injective property.
       CARD (sticks r (SUC n))
     = CARD (IMAGE (\(e,l). e::l) (R CROSS sticks r n)) by sticks_suc
     = CARD (R CROSS sticks r n)                        by CARD_INJ_IMAGE, by injective property above.
     = CARD R * CARD (sticks r n)                       by CARD_CROSS, FINITE R, FINITE (sticks r n)
     = CARD R * (CARD R ** n)                           by induction hypothesis
     = CARD R ** (SUC n)                                by EXP
*)
val sticks_card = store_thm(
  "sticks_card",
  ``!r:'a field. FINITE R ==> !n. CARD (sticks r n) = (CARD R) ** n``,
  rpt strip_tac >>
  Induct_on `n` >-
  rw[sticks_0] >>
  rw[sticks_suc, sticks_finite, CARD_INJ_IMAGE, FINITE_COUNT, CARD_CROSS, pairTheory.FORALL_PROD, EXP]);

(* Theorem: sticks r 1 = IMAGE (\c. [c]) R *)
(* Proof:
   By sticks_def, this is to show:
   (1) set x SUBSET R /\ LENGTH x = 1 ==> ?c. (x = [c]) /\ c IN R
       LENGTH x = 1 ==> ?c. x = [c]     by LENGTH_EQ_1
       Also set [c] = c INSERT set []   by LIST_TO_SET_THM
                    = c INSERT {}       by LIST_TO_SET_THM
                    = {c}               by notation
       That is c IN set [c]             by EXTENSION
       Given set x SUBSET R, c IN R     by SUBSET_DEF
   (2) c IN R ==> set [c] SUBSET R
       Since set [c] = {c}              by above
          so !x. x IN set [c] ==> x = c by IN_SING
       Hence set [c] SUBSER R           by SUBSET_DEF
   (3) LENGTH [c] = 1
        LENGTH [c]
      = LENGTH (c::[])                  by notation
      = SUC (LENGTH [])                 by LENGTH
      = SUC 0                           by LENGTH
      = 1                               by ONE
*)
val sticks_1 = store_thm(
  "sticks_1",
  ``!r:'a field. sticks r 1 = IMAGE (\(c:'a). [c]) R``,
  rw[sticks_def, EXTENSION, EQ_IMP_THM] >| [
    `?c. x = [c]` by rw[GSYM LENGTH_EQ_1] >>
    `c IN set [c]` by rw[LIST_TO_SET_THM] >>
    metis_tac[SUBSET_DEF],
    rw[LIST_TO_SET_THM],
    rw[]
  ]);

(* Theorem: !p. p IN sticks r 1 <=> ?c. c IN R /\ (p = [c]) *)
(* Proof: by sticks_1, IN_IMAGE *)
val sticks_1_member = store_thm(
  "sticks_1_member",
  ``!r:'a field. !p. p IN sticks r 1 <=> ?c. c IN R /\ (p = [c])``,
  rw[sticks_1] >>
  metis_tac[]);

(* Theorem: !p. p IN sticks r 0 <=> (p = []) *)
(* Proof:
      p IN sticks r 0
  <=> p IN {[]}  by sticks_0
  <=> p = []     by IN_SING
*)
val sticks_0_member = store_thm(
  "sticks_0_member",
  ``!r:'a field. !p. p IN sticks r 0 <=> (p = [])``,
  rw[sticks_0]);

(* ------------------------------------------------------------------------- *)
(* Stick Properties.                                                         *)
(* ------------------------------------------------------------------------- *)

(* Theorem: l IN sticks r n ==> LENGTH l = n *)
(* Proof: by sticks_def. *)
val stick_length = store_thm(
  "stick_length",
  ``!r l n. l IN sticks r n ==> (LENGTH l = n)``,
  rw[sticks_def]);

(* Theorem: l IN sticks r (SUC n) <=> (?h t. h IN R /\ t IN sticks r n /\ (l = h::t)) *)
(* Proof: by sticks_suc. *)
val stick_cons = store_thm(
  "stick_cons",
  ``!r:'a field. !(l:'a list) n. l IN sticks r (SUC n) <=>
                                 (?h t. h IN R /\ t IN sticks r n /\ (l = h::t))``,
  rw[sticks_suc, pairTheory.EXISTS_PROD] >>
  metis_tac[]);

(* Define a sticks of length n with all zero *)
(*
val stick_all_zero_def = Define`
  stick_all_zero (r:'a field) n = GENLIST (\j. #0) n
`;
*)

(* Theorem: VSpace r g op ==> !n. (GENLIST (\j. #0) n) IN (sticks r n) *)
(* Proof:
   By induction on n.
   Base case: GENLIST (\j. #0) 0 IN sticks r 0
       GENLIST (\j. #0) 0 = []                  by GENLIST
       sticks r 0 = {[]}                        by sticks_0
       and [] IN {[]}                           by IN_SING
   Step case: GENLIST (\j. #0) n IN sticks r n ==>
              GENLIST (\j. #0) (SUC n) IN sticks r (SUC n)
\         GENLIST (\j. #0) (SUC n)
        = #0 :: GENLIST ((\j. #0) o SUC) n      by GENLIST_CONS
        = #0 :: GENLIST (\j. #0) n              since (\j. #0) o SUC = (\j. #0) by FUN_EQ_THM
        Since #0 IN R                           by field_zero_element
          and GENLIST (\j. #0) n IN sticks r n  by induction hypothesis
           so result IN sticks r (SUC n)        by stick_cons
*)
val stick_all_zero = store_thm(
  "stick_all_zero",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !n. (GENLIST (\j. #0) n) IN (sticks r n)``,
  rpt strip_tac >>
  Induct_on `n` >| [
    rw[] >>
    metis_tac[sticks_0, IN_SING],
    rw[stick_cons] >>
    qexists_tac `#0` >>
    qexists_tac `GENLIST (\j. #0) n` >>
    `Field r` by metis_tac[vspace_has_field] >>
    rw_tac std_ss[GENLIST_CONS, field_zero_element] >>
    `(\j. #0) o SUC = (\j. #0)` by rw[FUN_EQ_THM] >>
    rw[]
  ]);

(* Theorem: h IN R /\ t IN sticks r (n - 1) ==>
            !k. k < n ==> TAKE k t ++ [h] ++ DROP k t IN sticks r n *)
(* Proof: by induction on n.
   Base case: !k. k < 0 ==> ...
     Since k < 0 is F, this is true.
   Step case: k < SUC n ==> TAKE k t ++ [h] ++ DROP k t IN sticks r (SUC n)
     If k = 0,  TAKE 0 t ++ [h] ++ DROP 0 t
              = [] ++ [h] ++ t
              = h::t IN sticks r (SUC n)     by stick_cons
     If k = SUC n' < SUC n, n' < n
        to show: TAKE (SUC n') t ++ [h] ++ DROP (SUC n') t IN sticks r (SUC n)
        Since n' < n, n <> 0,
        or n = SUC j, so t IN sticks r n means
        ?k s. k IN R /\ s IN sticks r j /\ t = k::s    by stick_cons
        and (TAKE n' s ++ [h] ++ DROP n' s) IN sticks r (SUC j)
                                                       by induction hypothesis
          TAKE (SUC n') t ++ [h] ++ DROP (SUC n') t
        = TAKE (SUC n') (k::s) ++ [h] ++ DROP (SUC n') (k::s)
        = (k:: TAKE n' s) ++ [h] ++ DROP n' s          by TAKE_def, DROP_def
        = k:: (TAKE n' s ++ [h] ++ DROP n' s)          by APPEND
        IN sticks r (SUC n)                            by stick_cons, k IN R, induction hypothesis.
*)
val stick_insert_element = store_thm(
  "stick_insert_element",
  ``!r:'a field. !h t n. h IN R /\ t IN sticks r (n - 1) ==>
    !k. k < n ==> TAKE k t ++ [h] ++ DROP k t IN sticks r n``,
  ntac 2 strip_tac >>
  Induct_on `n` >-
  rw[] >>
  rw[] >>
  Cases_on `k` >-
  rw[stick_cons] >>
  rw[] >>
  `n' < n` by decide_tac >>
  `n <> 0` by decide_tac >>
  `?j. n = SUC j` by metis_tac[num_CASES] >>
  `?k s. k IN R /\ s IN sticks r j /\ (t = k::s)` by metis_tac[stick_cons] >>
  `SUC j - 1 = j` by decide_tac >>
  rw[] >>
  `(TAKE n' s ++ [h] ++ DROP n' s) IN sticks r (SUC j)` by rw[] >>
  metis_tac[stick_cons]);

(* Theorem: t IN sticks r n ==> !k. k < n ==>
            EL k t IN R /\ TAKE k t IN sticks r k /\ DROP (SUC k) t IN sticks r (n - (SUC k)) *)
(* Proof:
   By induction on n.
   Base case: !k. k < 0 ==>
              TAKE k t IN sticks r k /\ EL k t IN R /\ DROP (SUC k) t IN sticks r (0 - (SUC k))
     Since k < 0 is F, this is true.
   Step case: t IN sticks r (SUC n) ==> !k. k < SUC n ==>
              EL k t IN R /\ TAKE k t IN sticks r k /\ DROP (SUC k) t IN sticks r (SUC n - SUC k)
     Expanding by stick_cons, this is to show:
     (1) k < SUC n ==> EL k (h::t') IN R
         If k = 0, EL 0 (h::t') = h IN R                          by h IN R from stick_cons
         If k = SUC j < SUC n, EL (SUC j) (h::t') = EL j t' IN R  by induction hypothesis.
     (2) k < SUC n ==> TAKE k (h::t') IN sticks r k
         If k = 0, TAKE 0 (h::t') = [] IN sticks r 0              by sticks_0
         If k = SUC j < SUC n, TAKE (SUC j) (h::t') = TAKE j t' IN sticks r j
                                                                  by stick_cons, induction hypothesis.
     (3) k < SUC n ==> DROP (SUC k) (h::t') IN sticks r (n - k)
         If k = 0, DROP 1 (h::t') = t' IN sticks r n              by stick_cons
         If k = SUC j < SUC n, DROP (SUC j) (h::t') = DROP j t' IN sticks r (n - SUC j)
                                                                  by induction hypothesis
*)
val stick_components_stick = store_thm(
  "stick_components_stick",
  ``!(r:'a field) (t:'a list) n. t IN sticks r n ==>
    !k. k < n ==> EL k t IN R /\ TAKE k t IN sticks r k /\ DROP (SUC k) t IN sticks r (n - (SUC k))``,
  strip_tac >>
  Induct_on `n` >-
  rw[] >>
  `!j k. SUC j < SUC k ==> j < k` by decide_tac >>
  rw[stick_cons] >| [
    Cases_on `k` >> rw[],
    Cases_on `k` >> rw[sticks_0, stick_cons],
    Cases_on `k` >> rw[]
  ]);

(* Theorem: l IN sticks r (SUC n) <=> (?h t. h IN R /\ t IN sticks r n /\ (l = SNOC h t)) *)
(* Proof:
   If part: l IN sticks r (SUC n) ==> ?h t. h IN R /\ t IN sticks r n /\ (l = t ++ [h])
      Since n < SUC n      by LESS_SUC
        and SUC n - SUC n  by arithmetic
         so EL n l IN R /\ TAKE n l IN sticks r n /\
            DROP (SUC n) l IN sticks r 0               by stick_components_stick
      Let h = EL n l, t = TAKE n l, s = DROP (SUC n) l.
      Then s IN sticks r 0 ==> s = []                  by sticks_0, IN_SING
      Also LENGTH l = SUC n                            by stick_length
        so l = t ++ DROP n l        by TAKE_DROP
             = t ++ ([h] ++ s)      by DROP_CONS_EL
             = t ++ ([h] ++ [])     by s = []
             = t ++ [h]             by APPEND_NIL
   Only-if part: h IN R /\ t IN sticks r n ==> t ++ [h] IN sticks r (SUC n)
          h IN R /\ t IN sticks r n
      ==> h IN R /\ set t SUBSET R /\ (LENGTH t = n)              by sticks_def
      ==> set (t ++ [h]) SUBSET R /\ (LENGTH t = n)               by LIST_TO_SET_APPEND, UNION_SUBSET
      ==> set (t ++ [h]) SUBSET R /\ (LENGTH (t ++ [h]) = 1 + n)  by LENGTH_APPEND
      ==> set (t ++ [h]) SUBSET R /\ (LENGTH (t ++ [h]) = SUC n)  by SUC_ONE_ADD
      ==> t ++ [h] IN sticks r (SUC n)                            by sticks_def
*)
val stick_snoc = store_thm(
  "stick_snoc",
  ``!r:'a field. !(l:'a list) n. l IN sticks r (SUC n) <=>
                                (?h t. h IN R /\ t IN sticks r n /\ (l = SNOC h t))``,
  rw[EQ_IMP_THM] >| [
    `n < SUC n /\ (SUC n - SUC n = 0)` by decide_tac >>
    `EL n l IN R /\ TAKE n l IN sticks r n /\ DROP (SUC n) l IN sticks r 0` by metis_tac[stick_components_stick] >>
    qabbrev_tac `h = EL n l` >>
    qabbrev_tac `t = TAKE n l` >>
    qabbrev_tac `s = DROP (SUC n) l` >>
    `s = []` by metis_tac[sticks_0, IN_SING] >>
    `LENGTH l = SUC n` by metis_tac[stick_length] >>
    `l = t ++ DROP n l` by rw[TAKE_DROP, Abbr`t`] >>
    `_ = t ++ ([h] ++ s)` by rw[rich_listTheory.DROP_CONS_EL, Abbr`h`, Abbr`s`] >>
    `_ = t ++ [h]` by rw[] >>
    metis_tac[],
    pop_assum mp_tac >>
    rw[sticks_def]
  ]);

(* ------------------------------------------------------------------------- *)
(* Stick Addition.                                                           *)
(* ------------------------------------------------------------------------- *)

(* Define stick addition by components. *)
val stick_add_def = Define`
  (stick_add (r:'a field) [][] = []) /\
  (stick_add (r:'a field) ((h:'a)::(t:'a list)) ((h':'a)::(t':'a list)) =
                                                (h + h')::(stick_add r t t'))
`;

val _ = temp_overload_on ("+", ``stick_add r``);
(* - stick_add_def;
> val it = |- (!r. [] + [] = []) /\ !t' t r h' h. (h::t) + (h'::t') = h + h'::t + t' : thm *)

val stick_add_nil_nil = save_thm("stick_add_nil_nil", stick_add_def |> CONJUNCTS |> el 1);
(* val stick_add_nil_nil = |- !r. [] + [] = []: thm *)

val stick_add_cons_cons = save_thm("stick_add_cons_cons", stick_add_def |> CONJUNCTS |> el 2);
(* val stick_add_cons_cons = |- !t' t r h' h. (h::t) + (h'::t') = h + h'::t + t': thm *)

(* Adding same-length sticks give another stick of the same length *)

(* Theorem: !n. n1 IN sticks r n /\ n2 IN sticks r n ==> (n1 + n2) IN sticks r n *)
(* Proof: by induction on n.
   Base case: n1 IN sticks r 0 /\ n2 IN sticks r 0 ==> n1 + n2 IN sticks r 0
     Since n1 = [] and n2 = []               by sticks_0, IN_SING
     n1 + n2 = [] + [] = [] IN sticks r 0    by sticks_0, IN_SING.
   Step case: !n1 n2. n1 IN sticks r (SUC n) /\ n2 IN sticks r (SUC n) ==> n1 + n2 IN sticks r (SUC n)
     By stick_cons, this is to show:
     ?h'' t''. h'' IN R /\ t'' IN sticks r n /\ ((h::t) + (h'::t') = h''::t'')
     Let h'' = h + h', t'' = t + t'.
     Then h + h' IN R                        by field_add_element
      and t + t' IN sticks r n               by induction hypothesis
     and (h::t) + (h'::t') = h''::t''        by stick_add_def
*)
val stick_add_length = store_thm(
  "stick_add_length",
  ``!(r:'a field). Field r ==>
    !n n1 n2. n1 IN sticks r n /\ n2 IN sticks r n ==> (n1 + n2) IN sticks r n``,
  ntac 2 strip_tac >>
  Induct >-
  metis_tac[sticks_0, IN_SING, stick_add_def] >>
  rw[stick_cons] >>
  qexists_tac `h + h'` >>
  qexists_tac `t + t'` >>
  rw[stick_add_def]);

(* ------------------------------------------------------------------------- *)
(* Stick Negation.                                                           *)
(* ------------------------------------------------------------------------- *)

(* Define stick addition by components. *)
val stick_neg_def = Define`
  (stick_neg (r:'a field) [] = []) /\
  (stick_neg (r:'a field) ((h:'a)::(t:'a list)) = (-h)::(stick_neg r t))
`;

val _ = temp_overload_on ("-", ``stick_neg r``);
(* - stick_neg_def;
> val it = |- (!r. $- [] = []) /\ !r h t. $- (h::t) = -h:: $- t : thm *)

(* Theorem: $- [] = [] *)
val stick_neg_zero = save_thm("stick_neg_zero", stick_neg_def |> SPEC_ALL |> CONJUNCTS |> el 1 |> DISCH_ALL |> GEN_ALL);
(* val stick_neg_zero = |- !r. $- [] = []: thm *)

(* Theorem: $- (h::t) = -h:: $- t *)
val stick_neg_cons = save_thm("stick_neg_cons", stick_neg_def |> SPEC_ALL |> CONJUNCTS |> el 2 |> DISCH_ALL |> GEN_ALL);
(* val stick_neg_cons = |- !r h t. $- (h::t) = -h:: $- t: thm *)

(* Negating a stick gives another stick of the same length *)

(* Theorem: !n. n1 IN sticks r n ==> ($- n1) IN sticks r n *)
(* Proof: by induction on n.
   Base case: n1 IN sticks r 0 ==> $- n1 IN sticks r 0
     Since n1 = []                       by sticks_0, IN_SING
     $- n1 = $- [] = [] IN sticks r 0    by sticks_0, IN_SING.
   Step case: !n1. n1 IN sticks r (SUC n) ==> $- n1 IN sticks r (SUC n)
     By stick_cons, this is to show:
     ?h' t'. h' IN R /\ t' IN sticks r n /\ ($- (h::t) = h'::t')
     Let h' = -h, t' = $- t.
     Then -h IN R                        by field_neg_element
      and $- t IN sticks r n             by induction hypothesis
     and $- (h::t) = h'::t'              by stick_neg_def
*)
val stick_neg_length = store_thm(
  "stick_neg_length",
  ``!(r:'a field). Field r ==> !n n1. n1 IN sticks r n ==> ($- n1) IN sticks r n``,
  ntac 2 strip_tac >>
  Induct >-
  metis_tac[sticks_0, IN_SING, stick_neg_def] >>
  rw[stick_cons] >>
  qexists_tac `-h` >>
  qexists_tac `$- t` >>
  rw[stick_neg_def]);

(* ------------------------------------------------------------------------- *)
(* Stick Scalar Multiplication.                                              *)
(* ------------------------------------------------------------------------- *)

(* Define stick scalar multiplication by components. *)
val stick_cmult_def = Define`
  (stick_cmult (r:'a field) (c:'a) [] = []) /\
  (stick_cmult (r:'a field) (c:'a) ((h:'a)::(t:'a list)) = (c * h)::(stick_cmult r c t))
`;

val _ = temp_overload_on ("*", ``stick_cmult r``);
(* - stick_cmult_def;
> val it = |- (!r c. c * [] = []) /\ !r c h t. c * (h::t) = c * h::c * t : thm *)

(* Theorem: c * [] = [] *)
val stick_cmult_zero = save_thm("stick_cmult_zero", stick_cmult_def |> SPEC_ALL |> CONJUNCTS |> el 1 |> DISCH_ALL |> GEN_ALL);
(* val stick_cmult_zero = |- !r c. c * [] = []: thm *)

(* Theorem: c * (h::t) = c * h::c * t *)
val stick_cmult_cons = save_thm("stick_cmult_cons", stick_cmult_def |> SPEC_ALL |> CONJUNCTS |> el 2 |> DISCH_ALL |> GEN_ALL);
(* val stick_cmult_cons = |- !r c h t. c * (h::t) = c * h::c * t: thm *)

(* Multiply a stick by a scalar gives another stick of the same length *)

(* Theorem: !n. c IN R /\ n1 IN sticks r n ==> c * n1 IN sticks r n *)
(* Proof: by induction on n.
   Base case: !c n1. c IN R /\ n1 IN sticks r 0 ==> c * n1 IN sticks r 0
     Since n1 = []                         by sticks_0, IN_SING
     c * n1 = c * [] = [] IN sticks r 0    by sticks_0, IN_SING
   Step case: !c n1. c IN R /\ n1 IN sticks r (SUC n) ==> c * n1 IN sticks r (SUC n)
     By stick_cons, this is to show:
     ?h' t'. h' IN R /\ t' IN sticks r n /\ (c * (h::t) = h'::t')
     Let h'' = c * h, t'' = c * t.
     Then c * h IN R                       by field_mult_element
      and c * t IN sticks r n              by induction hypothesis
     and c * (h::t) = h'::t'               by stick_cmult_def
*)
val stick_cmult_length = store_thm(
  "stick_cmult_length",
  ``!(r:'a field). Field r ==> !n c n1. c IN R /\ n1 IN sticks r n ==> (c * n1) IN sticks r n``,
  ntac 2 strip_tac >>
  Induct >-
  metis_tac[sticks_0, IN_SING, stick_cmult_def] >>
  rw[stick_cons] >>
  qexists_tac `c * h` >>
  qexists_tac `c * t` >>
  rw[stick_cmult_def]);

(* ------------------------------------------------------------------------- *)
(* Stick Subtraction.                                                        *)
(* ------------------------------------------------------------------------- *)

(* Define stick subtraction by components. *)
val stick_sub_def = Define`
  (stick_sub (r:'a field) [][] = []) /\
  (stick_sub (r:'a field) ((h:'a)::(t:'a list)) ((h':'a)::(t':'a list)) =
                                                (h - h')::(stick_sub r t t'))
`;

val _ = temp_overload_on ("-", ``stick_sub r``);
(* - stick_sub_def;
> val it = |- (!r. [] - [] = []) /\ !t' t r h' h. (h::t) - (h'::t') = h - h'::t - t' : thm *)

(* Theorem: [] - [] = [] *)
val stick_sub_nil_nil = save_thm("stick_sub_nil_nil", stick_sub_def |> SPEC_ALL |> CONJUNCTS |> el 1 |> DISCH_ALL |> GEN_ALL);
(* val val stick_sub_nil_nil = |- !r. [] - [] = []: thm *)

(* Theorem: (h::t) - (h'::t') = h - h'::t - t' *)
val stick_sub_cons_cons = save_thm("stick_sub_cons_cons", stick_sub_def |> SPEC_ALL |> CONJUNCTS |> el 2 |> DISCH_ALL |> GEN_ALL);
(* val stick_sub_cons_cons = |- !t' t r h' h. (h::t) - (h'::t') = h - h'::t - t': thm *)

(* Theorem: !n. n2. n1 IN sticks r n /\ n2 IN sticks r n ==> n1 - n2 = n1 + $- n2 *)
(* Proof: by induction on n.
   Base case: n1 IN sticks r 0 /\ n2 IN sticks r 0 ==> n1 - n2 = n1 + $- n2
     Since n1 = [] and n2 = []    by sticks_0, IN_SING
       n1 - n2
     = []                         by stick_sub_def
     = [] + []                    by stick_add_def
     = [] + $- []                 by stick_neg_def
   Step case: n1 IN sticks r (SUC n) /\ n2 IN sticks r (SUC n) ==>  n1 - n2 = n1 + $- n2
     By expanding with stick_cons, this is to show:
     (h::t) - (h'::t') = (h::t) + $- (h'::t')
       (h::t) - (h'::t')
     = h - h' :: t - t'           by stick_sub_def
     = h + -h':: t - t'           by field_sub_def
     = h + -h':: t + $-t'         by induction hypothesis
     = (h::t) + (-h'::-t')        by stick_add_def
     = (h::t) + -(h'::t')         by stick_neg_def
*)
val stick_sub_alt = store_thm(
  "stick_sub_alt",
  ``!(r:'a field). Field r ==>
    !n n1 n2. n1 IN sticks r n /\ n2 IN sticks r n ==> (n1 - n2 = n1 + $- n2)``,
  ntac 2 strip_tac >>
  Induct >| [
    rw[] >>
    `(n1 = []) /\ (n2 = [])` by metis_tac[sticks_0, IN_SING] >>
    rw[stick_sub_def, stick_add_def, stick_neg_def],
    rw[stick_cons] >>
    rw[stick_sub_def, stick_add_def, stick_neg_def]
  ]);

(* Subtracting same-length sticks give another stick of the same length *)

(* Theorem: !n. n2. n1 IN sticks r n /\ n2 IN sticks r n ==> (n1 - n2) IN sticks r n *)
(* Proof: by induction on n.
   Base case: n1 IN sticks r 0 /\ n2 IN sticks r 0 ==> n1 - n2 IN sticks r 0
     Since n1 = [] and n2 = []               by sticks_0, IN_SING
     n1 - n2 = [] - [] = [] IN sticks r 0    by sticks_0, IN_SING
   Step case: !n1 n2. n1 IN sticks r (SUC n) /\ n2 IN sticks r (SUC n) ==> n1 - n2 IN sticks r (SUC n)
     By stick_cons, this is to show:
     ?h'' t''. h'' IN R /\ t'' IN sticks r n /\ ((h::t) - (h'::t') = h''::t'')
     Let h'' = h - h', t'' = t - t'.
     Then h - h' IN R                        by field_sub_element
      and t - t' IN sticks r n               by induction hypothesis
     and (h::t) - (h'::t') = h''::t''        by stick_sub_def
   Or:
   n1 - n2 = n1 + $- n2      by stick_sub_alt
   Hence true                by stick_add_length, stick_neg_length.
*)
val stick_sub_length = store_thm(
  "stick_sub_length",
  ``!(r:'a field). Field r ==>
    !n n1 n2. n1 IN sticks r n /\ n2 IN sticks r n ==> (n1 - n2) IN sticks r n``,
  rpt strip_tac >>
  `n1 - n2 = n1 + $- n2` by metis_tac[stick_sub_alt] >>
  rw[stick_add_length, stick_neg_length]);

(* Theorem: !n. n1 IN sticks r n /\ n2 IN sticks r n ==>
                n1 = n2 <=> !k. k < n ==> (EL k (n1 - n2) = #0) *)
(* Proof: by induction on n.
   Base case: !n1 n2. n1 IN sticks r 0 /\ n2 IN sticks r 0 ==>
              ((n1 = n2) <=> !k. k < 0 ==> (EL k (n1 - n2) = #0))
     Since n1 = [] and n2 = []      by sticks_0
     and LENGTH [] = 0              by LENGTH_NIL
     This is trivially true, as no k < 0.
   Step case: !n1 n2. n1 IN sticks r (SUC n) /\ n2 IN sticks r (SUC n) ==>
              ((n1 = n2) <=> !k. k < SUC n ==> (EL k (n1 - n2) = #0))
     By stick_cons, this is to show:
     (h = h') /\ (!k. k < n ==> (EL k (t - t') = #0)) <=> !k. k < SUC n ==> (EL k ((h::t) - (h'::t')) = #0)

     If part: k < SUC n ==> EL k ((h::t) - (h::t)) = #0
       EL k ((h::t) - (h::t))
     = EL k ((h - h) :: (t - t))    by stick_sub_def
     = EL k (#0 :: (t - t))         by field_sub_eq_zero
     If k = 0, EL 0 (#0::(t - t)) is true by EL, HD.
     If k = SUC n', n' < n, EL (SUC n') (#0::(t - t)) = EL n' (t - t) = #0  by induction hypothesis.

     Only-if part: !k. k < SUC n ==> (EL k ((h::t) - (h'::t')) = #0) ==>
                                     (h = h') /\ !k. k < n ==> (EL k (t - t') = #0)
     (h::t) - (h'::t') = (h - h')::(t - t')                                 by stick_sub_def
     If k = 0, EL 0 ((h::t) - (h'::t')) = #0 => h - h' = #0, or h = h'      by field_sub_eq_zero.
     If k = SUC n',
     !n'. n' < n and EL (SUC n') ((h::t) - (h'::t')) = EL n' (t - t') = #0  by induction hypothesis
*)
val stick_eq_property = store_thm(
  "stick_eq_property",
  ``!(r:'a field). Field r ==> !n n1 n2. n1 IN sticks r n /\ n2 IN sticks r n ==>
        ((n1 = n2) <=> (!k. k < n ==> (EL k (n1 - n2) = #0)))``,
  ntac 2 strip_tac >>
  Induct >-
  rw[sticks_0] >>
  rw[stick_cons, EQ_IMP_THM] >| [
    `(h::t) - (h::t) = #0::(t - t)` by rw[stick_sub_def] >>
    rw[] >>
    Cases_on `k` >-
    rw[] >>
    `n' < n` by decide_tac >>
    rw[] >>
    metis_tac[],
    `(h::t) - (h'::t') = h - h'::(t - t')` by rw[stick_sub_def] >>
    `(!k. k < SUC n ==> (EL k ((h::t) - (h'::t')) = #0)) ==>
    (0 < SUC n ==> (EL 0 ((h::t) - (h'::t')) = #0)) /\
    (!k. SUC k < SUC n ==> (EL (SUC k) ((h::t) - (h'::t')) = #0))` by metis_tac[num_CASES] >>
    `EL 0 ((h::t) - (h'::t')) = #0` by rw[] >>
    `h - h' = #0` by metis_tac[EL, HD] >>
    `h = h'` by metis_tac[field_sub_eq_zero] >>
    `!k. k < n ==> (EL (SUC k) ((h::t) - (h::t')) = #0)` by rw[] >>
    `!k. k < n ==> (EL k (t - t') = #0)` by metis_tac[EL, TL] >>
    rw[]
  ]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
