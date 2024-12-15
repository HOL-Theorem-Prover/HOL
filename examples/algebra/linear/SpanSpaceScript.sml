(* ------------------------------------------------------------------------- *)
(* Span Space                                                                *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "SpanSpace";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory listTheory numberTheory combinatoricsTheory;

open VectorSpaceTheory;
open monoidTheory groupTheory fieldTheory;

(* ------------------------------------------------------------------------- *)
(* Span Space Documentation                                                  *)
(* ------------------------------------------------------------------------- *)
(* Overload:
   VSUM    = VectorSum g
   n |o| b = VSUM (MAP2 op n b)
*)
(* Definitions and Theorems (# are exported):

   Basis:
   basis_def              |- (!g. basis g [] <=> T) /\ !g h t. basis g (h::t) <=> h IN V /\ basis g t
   basis_nil              |- !g. basis g [] <=> T
   basis_cons             |- !g h t. basis g (h::t) <=> h IN V /\ basis g t
   basis_member           |- !g b. basis g b <=> !x. MEM x b ==> x IN V
   basis_contract_basis   |- !g b. basis g b ==> !n. basis g (TAKE n b ++ DROP (SUC n) b)
   basis_components_basis |- !g b. basis g b ==> !n. n < LENGTH b ==>
                                   EL n b IN V /\ basis g (TAKE n b) /\ basis g (DROP (SUC n) b)

   Vector Sum:
   VectorSum_def            |- (!g. VSUM [] = |0|) /\ !g h t. VSUM (h::t) = h || VSUM t
   vsum_nil                 |- !g. VSUM [] = |0|
   vsum_cons                |- !g h t. VSUM (h::t) = h || VSUM t
   vsum_basis_stick_vector  |- !r g op. VSpace r g op ==> !b. basis g b ==>
                                 !n. n IN sticks r (LENGTH b) ==> VSUM (MAP2 op n b) IN V
   vsum_basis_stick_add     |- !r g op. VSpace r g op ==> !b. basis g b ==>
                                 !n1 n2. n1 IN sticks r (LENGTH b) /\ n2 IN sticks r (LENGTH b) ==>
                                         (n1 |o| b || (n2 |o| b) = n1 + n2 |o| b)
   vsum_basis_stick_neg     |- !r g op. VSpace r g op ==> !b. basis g b ==>
                                 !n. n IN sticks r (LENGTH b) ==> (-#1 o (n |o| b) = $- n |o| b)
   vsum_basis_stick_cmult   |- !r g op. VSpace r g op ==> !b. basis g b ==>
                   !n. n IN sticks r (LENGTH b) ==> !c. c IN R ==> (c o (n |o| b) = c * n |o| b)
   vsum_basis_stick_zero    |- !r g op. VSpace r g op ==>
                                 !b. basis g b ==> (GENLIST (\j. #0) (LENGTH b) |o| b = |0|)
   vsum_basis_split         |- !r g op. VSpace r g op ==> !b. basis g b ==>
                      !n. n IN sticks r (LENGTH b) ==> !k. k < LENGTH b ==>
     (n |o| b = TAKE k n |o| TAKE k b || EL k n o EL k b || (DROP (SUC k) n |o| DROP (SUC k) b))

   Spanning Space:
   SpanSpace_def        |- !r g op b. SpanSpace r g op b =
                            <|carrier := IMAGE (\n. n |o| b) (sticks r (LENGTH b));
                                   op := $||;
                                   id := |0||>
   vspace_span_property |- !r g op b.
     ((SpanSpace r g op b).carrier = IMAGE (\n. n |o| b) (sticks r (LENGTH b))) /\
     ((SpanSpace r g op b).op = $||) /\
     ((SpanSpace r g op b).id = |0|) /\
     (!n. n IN sticks r (LENGTH b) ==> n |o| b IN (SpanSpace r g op b).carrier) /\
     !v. v IN (SpanSpace r g op b).carrier ==> ?n. n IN sticks r (LENGTH b) /\ (v = n |o| b)
   vspace_span_vector   |- !r g op. VSpace r g op ==> !b. basis g b ==>
                           !x. x IN (SpanSpace r g op b).carrier ==> x IN V
   vspace_span_subspace |- !r g op. VSpace r g op ==> !b. basis g b ==> (SpanSpace r g op b).carrier SUBSET V
   vspace_span_closure  |- !r g op. VSpace r g op ==> !b. basis g b ==>
                           !x y. x IN (SpanSpace r g op b).carrier /\ y IN (SpanSpace r g op b).carrier ==>
                                 x || y IN (SpanSpace r g op b).carrier
   vspace_span_negative |- !r g op. VSpace r g op ==> !b. basis g b ==>
       !x. x IN (SpanSpace r g op b).carrier ==> ?y. y IN (SpanSpace r g op b).carrier /\ (y || x = |0|)
   vspace_span_has_zero |- !r g op. VSpace r g op ==> !b. basis g b ==> |0| IN (SpanSpace r g op b).carrier
   vspace_span_group    |- !r g op. VSpace r g op ==> !b. basis g b ==> Group (SpanSpace r g op b)
   vspace_span_abelian_group  |- !r g op. VSpace r g op ==> !b. basis g b ==> AbelianGroup (SpanSpace r g op b)
   vspace_span_cmult    |- !r g op. VSpace r g op ==> !b. basis g b ==>
                           !c x. c IN R /\ x IN (SpanSpace r g op b).carrier ==> c o x IN (SpanSpace r g op b).carrier
   vspace_span_vspace   |- !r g op. VSpace r g op ==> !b. basis g b ==> VSpace r (SpanSpace r g op b) op
   vspace_zero_stick    |- !r g op. VSpace r g op ==>
                           !b. basis g b ==> ?z. z IN sticks r (LENGTH b) /\ (z |o| b = |0|)
   vspace_stick_zero    |- !r g op. VSpace r g op ==> !b. basis g b ==> !n. n IN sticks r (LENGTH b) /\
                                    (!k. k < LENGTH b ==> (EL k n = #0)) ==> (n |o| b = |0|)
   vspace_basis_stick   |- !r g op. VSpace r g op ==> !b. basis g b ==>
                           !x. MEM x b ==> ?n. n IN sticks r (LENGTH b) /\ (x = n |o| b)
   vsum_stick_add       |- !r g op. VSpace r g op ==> !b. basis g b ==>
                           !n1 n2. n1 IN sticks r (LENGTH b) /\ n2 IN sticks r (LENGTH b) ==>
                                   (n1 + n2 |o| b = n1 |o| b || (n2 |o| b))
   vsum_stick_neg       |- !r g op. VSpace r g op ==> !b. basis g b ==>
                           !n. n IN sticks r (LENGTH b) ==> (g.inv (n |o| b) = $- n |o| b)
   vsum_stick_sub       |- !r g op. VSpace r g op ==> !b. basis g b ==>
                           !n1 n2. n1 IN sticks r (LENGTH b) /\ n2 IN sticks r (LENGTH b) ==>
                                   (n1 - n2 |o| b = n1 |o| b || g.inv (n2 |o| b))
   vsum_stick_cmult     |- !r g op. VSpace r g op ==> !b. basis g b ==>
                           !c n. c IN R /\ n IN sticks r (LENGTH b) ==> (c o (n |o| b) = c * n |o| b)
   vsum_stick_cons      |- !r g op. VSpace r g op ==> !b. basis g b ==>
                           !n. n IN sticks r (LENGTH b) ==>
                           !h v. h IN R /\ v IN V ==> (h o v || (n |o| b) = (h::n) |o| (v::b))
   vsum_stick_snoc      |- !r g op. VSpace r g op ==> !b. basis g b ==>
                           !n. n IN sticks r (LENGTH b) ==>
                           !h v. h IN R /\ v IN V ==> (SNOC h n |o| SNOC v b = h o v || (n |o| b))

   More on SpanSpace:
   vspace_span_cons        |- !r g op. VSpace r g op ==> !b1 b2.  basis g b1 /\ basis g b2 /\
                                       (SpanSpace r g op b1 = SpanSpace r g op b2) ==>
                              !h. h IN V ==> (SpanSpace r g op (h::b1) = SpanSpace r g op (h::b2))
   vspace_span_exchange_two|- !r g op. VSpace r g op ==> !u v. u IN V /\ v IN V ==>
                                       (SpanSpace r g op [u; v] = SpanSpace r g op [v; u])
   vspace_span_exchange    |- !r g op. VSpace r g op ==> !b. basis g b ==> !u v. u IN V /\ v IN V ==>
                                       (SpanSpace r g op (u::v::b) = SpanSpace r g op (v::u::b))
   vspace_span_with_member |- !r g op. VSpace r g op ==> !b. basis g b ==>
                              !v. v IN (SpanSpace r g op b).carrier ==>
                                       (SpanSpace r g op b = SpanSpace r g op (v::b))
   vspace_span_with_zero   |- !r g op. VSpace r g op ==> !b. basis g b ==>
                                       (SpanSpace r g op b = SpanSpace r g op ( |0|::b))
   vspace_span_add_member  |- !r g op. VSpace r g op ==> !b. basis g b ==>
               !h v. h IN (SpanSpace r g op b).carrier /\ v IN (SpanSpace r g op (h::b)).carrier ==>
                     v IN (SpanSpace r g op b).carrier
*)

(* Overloads for convenience *)
val _ = temp_overload_on ("o", ``(op:'a -> 'b -> 'b)``);
val _ = temp_overload_on ("V", ``(g:'b group).carrier``);
val _ = temp_overload_on ("||", ``(g:'b group).op``);
val _ = temp_overload_on ("|0|", ``(g:'b group).id``);
val _ = set_fixity "||" (Infixl 500); (* same as + in arithmeticScript.sml *)

val _ = temp_overload_on ("+", ``stick_add r``);
val _ = temp_overload_on ("-", ``stick_neg r``);
val _ = temp_overload_on ("*", ``stick_cmult r``);
val _ = temp_overload_on ("-", ``stick_sub r``);

(* ------------------------------------------------------------------------- *)
(* Basis, a vector list, for the purpose of spanning a subspace.             *)
(* ------------------------------------------------------------------------- *)

(* Note: pural of basis is bases, singular of bases is basis. *)

(* Basis checks a list of vectors *)
val basis_def = Define`
  (basis (g:'b group) [] <=> T) /\
  (basis (g:'b group) (h::t) <=> (h IN V) /\ basis g t)
`;

(* Theorem: basis g [] = T *)
val basis_nil = save_thm("basis_nil", basis_def |> CONJUNCT1);
(* > val basis_nil = |- !g. basis g [] <=> T : thm *)

(* Theorem: basis g (h::t) = h IN V /\ basis g t *)
val basis_cons = save_thm("basis_cons", basis_def |> CONJUNCT2);
(* > val basis_cons = |- !g h t. basis g (h::t) <=> h IN V /\ basis g t : thm *)

(* Theorem: basis g b <=> !x. MEM x b ==> x IN V *)
(* Proof: by induction on b.
   Base case: basis g [] <=> !x. MEM x [] ==> x IN V
     basis g [] = T          by basis_nil
     MEM x [] = F, hence true implication.
   Step case: !h. basis g (h::b) <=> !x. MEM x (h::b) ==> x IN V
     basis g (h::b) means h IN V /\ basis g b  by basis_cons
     basis g b <=> !x. MEM x b ==> x IN V      by induction hypothesis

     MEM x (h::b)  means (x = h) \/ MEM x b    by MEM
     If x = h, x IN V.
     If MEM x b, still x IN V                  by induction hypothesis
*)
val basis_member = store_thm(
  "basis_member",
  ``!(g:'b group) (b:'b list). basis g b <=> !x. MEM x b ==> x IN V``,
  strip_tac >>
  Induct >-
  rw[basis_nil] >>
  rw[basis_cons] >>
  metis_tac[]);

(* Theorem: basis g b ==> !n. basis g (TAKE n b ++ DROP (SUC n) b)) *)
(* Proof: by induction on b.
   Base case: basis g [] ==> !n. basis g (TAKE n [] ++ DROP (SUC n) [])
       TAKE n [] ++ DROP (SUC n) []
     = [] ++ []                                              by TAKE_def, DROP_def
     = []                                                    by APPEND
     And basis g [] = T                                      by basis_nil
   Step case: !h. basis g (h::b) ==> !n. basis g (TAKE n (h::b) ++ DROP (SUC n) (h::b))
     basis g (h::b) means h IN R /\ basis g b                by basis_cons
     basis g b ==> !n. basis g (TAKE n b ++ DROP (SUC n) b)  by induction hypothesis
     If n = 0, this is to show: basis g ([] ++ DROP 0 b)
       basis g ([] ++ DROP 0 b)
     = basis g ([] ++ b)                                      by DROP
     = basis g b                                              by APPEND
     Otherwise for SUC n, to show: basis g ((h::TAKE (SUC n' - 1) b) ++ DROP (SUC n') b)
       basis g ((h::TAKE (SUC n' - 1) b) ++ DROP (SUC n') b)
     = basis g ((h::TAKE n' b) ++ DROP (SUC n') b)
     = basis g (h::(TAKE n' b ++ DROP (SUC n') b))            by APPEND
     = T if h IN R /\ basis b (TAKE n' b ++ DROP (SUC n') b)  by induction hypothesis, basis_cons
*)
val basis_contract_basis = store_thm(
  "basis_contract_basis",
  ``!(g:'b group) b. basis g b ==> !n. basis g (TAKE n b ++ DROP (SUC n) b)``,
  ntac 3 strip_tac >>
  Induct_on `b` >| [
    rw[basis_nil],
    rw[basis_cons] >>
    Cases_on `n` >| [
      rw[],
      rw[basis_cons]
    ]
  ]);

(* Theorem: basis g b ==> !n. n < LENGTH b ==> TAKE n b IN V /\ EL n b IN V /\ DROP (SUC n) b IN V *)
(* Proof:
   By induction on b.
   Base case: !n. n < LENGTH [] ==> EL n [] IN V /\ basis g (TAKE n []) /\ basis g (DROP (SUC n) [])
      Since n < LENGTH [] = 0 is F, this is true.
   Step case: !h. basis g (h::b) ==> !n. n < LENGTH (h::b) ==>
               EL n (h::b) IN V /\ basis g (TAKE n (h::b)) /\ basis g (DROP (SUC n) (h::b))
      Expanding by basis_cons, this is to show:
      (1) h IN V /\ n < SUC (LENGTH b) ==> EL n (h::b) IN V
          If n = 0, EL 0 (h::b) = h, hence IN V                           by EL, HD
          If n = SUC j < SUC (LENGTH b), EL (SUC j) (h::b) = EL j b IN V  by induction hypothesis.
      (2) h IN V /\ basis g b /\ n < SUC (LENGTH b) ==> basis g (if n = 0 then [] else h::TAKE (n - 1) b)
          If n = 0, basis g [] = T                                        by basis_nil
          If n = SUC j < SUC (LENGTH b), basis g (h::TAKE (n - 1) b) = T  by basis_cons, induction hypothesis.
      (3) h IN V /\ basis g b /\ n < SUC (LENGTH b) ==> basis g (DROP n b)
          If n = 0, basis g (DROP 0 b) = basis g b = T                    by basis_cons
          If n = SUC j < SUC (LENGTH b), basis g (DROP (SUC j) b) = T     by induction hypothesis.
*)
val basis_components_basis = store_thm(
  "basis_components_basis",
  ``!(g:'b group) b. basis g b ==>
    !n. n < LENGTH b ==> (EL n b) IN V /\ basis g (TAKE n b) /\ basis g (DROP (SUC n) b)``,
  ntac 3 strip_tac >>
  Induct_on `b` >| [
    rw[],
    `!j k. SUC j < SUC k ==> j < k` by decide_tac >>
    rw[basis_cons] >| [
      Cases_on `n` >> rw[],
      Cases_on `n` >> rw[basis_def],
      Cases_on `n`>> rw[]
    ]
  ]);

(* ------------------------------------------------------------------------- *)
(* Vector Sum, sum of vectors composed with scalars, for linear combination. *)
(* ------------------------------------------------------------------------- *)

(* Vector SUM of a list of vectors *)
(*
val VectorSum_def = Define`
  (VectorSum (r:'a field) (g:'b group) (op:'a -> 'b -> 'b) [] = |0|) /\
  (VectorSum (r:'a field) (g:'b group) (op:'a -> 'b -> 'b) ((h:'b)::(t:'b list)) = h || VectorSum r g op t)
`;
*)
val VectorSum_def = Define`
  (VectorSum (g:'b group) [] = |0|) /\
  (VectorSum (g:'b group) ((h:'b)::(t:'b list)) = h || VectorSum g t)
`;

(* overloads for convenience *)
val _ = overload_on ("VSUM", ``VectorSum (g:'b group)``);

(* Theorem: VSUM [] = |0| *)
val vsum_nil = save_thm("vsum_nil", VectorSum_def |> CONJUNCT1);
(* > val vsum_nil = |- !g. VSUM [] = |0| : thm *)

(* Theorem: VSUM (h::t) = h || VSUM t *)
val vsum_cons = save_thm("vsum_cons", VectorSum_def |> CONJUNCT2);
(* > val vsum_cons = |- !g h t. VSUM (h::t) = h || VSUM t : thm *)

(* ------------------------------------------------------------------------- *)
(* Linear Combination as vector sum of op with sticks and basis.            *)
(* ------------------------------------------------------------------------- *)

(* overloads linear combination of op *)
val _ = overload_on ("|o|", ``\(n:'a list) (b:'b list). VSUM (MAP2 (op:'a -> 'b -> 'b) n b)``);
val _ = set_fixity "|o|" (Infixl 500); (* same as + in arithmeticScript.sml *)

(* Theorem: basis g b ==> !n. n IN (sticks r (LENGTH b)) ==> n |o| b IN V *)
(* Proof:
   By induction on b:
   Base case: basis g [] /\ n IN sticks r 0 ==> n |o| [] IN V
     n IN sticks r 0 <=> n = []                        by sticks_0, IN_SING
       n |o| []
     = [] |o| []                                       by n = []
     = |0|                                             by vsum_nil, MAP2
     Hence true by |0| IN V                            by vspace_has_zero
   Step case: basis g b ==> !n. n IN sticks r (LENGTH b) ==> VSUM (MAP2 op n b) IN V ==>
              !h. basis g (h::b) ==> !n. n IN sticks r (LENGTH (h::b)) ==> n |o| (h::b) IN V
     basis g (h::b) ==> h IN V /\ basis g b            by basis_cons
     Since n IN sticks r (SUC (LENGTH b))              by LENGTH
     ?k t. k IN R /\ t IN sticks r (LENGTH b) /\ (n = k::t)  by stick_cons
       n |o| (h::b)
     = (k::t) |o| (h::b)                               by n = k::t
     = k o h || t |o| b                                by vsum_cons, MAP2
     Since k o h IN V                                  by vspace_cmult_vector
       and t |o| b IN V                                by induction hypothesis
     Hence k o h || t |o| b IN V                       by vspace_vadd_vector
*)
val vsum_basis_stick_vector = store_thm(
  "vsum_basis_stick_vector",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
   !b. basis g b ==> !n. n IN (sticks r (LENGTH b)) ==> n |o| b IN V``,
  ntac 4 strip_tac >>
  Induct >| [
    rw[] >>
    `n = []` by metis_tac[sticks_0, IN_SING] >>
    rw[vsum_nil] >>
    metis_tac[vspace_has_zero],
    rw[basis_cons, stick_cons] >>
    rw[vsum_cons] >>
    metis_tac[vspace_vadd_vector, vspace_cmult_vector]
  ]);

(* Theorem: basis g b ==>
            !n1 n2. n1 IN (sticks r (LENGTH b)) /\ n2 IN (sticks r (LENGTH b)) ==>
                    ((n1 |o| b) || (n2 |o| b) = (n1 + n2) |o| b) *)
(* Proof:
   By induction on b.
   Base case: n1 IN sticks r 0 /\ n2 IN sticks r 0 ==> n1 |o| [] || (n2 |o| []) = n1 + n2 |o| []
      n1 IN sticks r 0 <=> n1 = []       by sticks_0, IN_SING
      n2 IN sticks r 0 <=> n2 = []       by sticks_0, IN_SING
      Then (n1 + n2) |o| []
         = ([] + []) |o| []              by n1 = [], n2 = []
         = [] |o| []                     by stick_add_def
         = |0|                           by vsum_nil, MAP2
         = |0| || |0|                    by vspace_vadd_lzero
         = (n1 |o| []) || (n2 |o| [])    by n1 = [], n2 = []
   Step case: basis g (h::b) /\ n1 IN sticks r (LENGTH (h::b)) /\ n2 IN sticks r (LENGTH (h::b)) ==>
              ((n1 |o| (h::b)) || (n2 |o|  (h::b)) = (n1 + n2) |o| (h::b))
      basis g (h::b) ==> h IN V /\ basis g b                          by basis_cons
      ?k t. k IN R /\ t IN sticks r (LENGTH b) /\ (n = k::t)          by stick_cons
      ?k' t'. k' IN R /\ t' IN sticks r (LENGTH b) /\ (n' = k'::t')   by stick_cons
      (k::t) |o| (h::b)) = k o h || t |o| b                           by vsum_cons, MAP2
      (k'::t') |o| (h::b)) = k' o h || t' |o| b                       by vsum_cons, MAP2
      The goal is: k1 o h || t1 |o| b || (k1 o h || t1 |o| b) = (k1 + k2) o h || (t1 + t2) |o| b

      Let u1 = k o h, u2 = k' o h
          v1 = t |o| b, v2 = t' |o| b
      Then u1 IN V /\ u2 IN V                           by vspace_cmult_vector
       and v1 IN V /\ v2 IN V                           by vsum_basis_stick_vector
        u1 || v1 || (u2 || v2)
      = u1 || (v1 || (u2 || v2))                        by vspace_vadd_assoc
      = u1 || (v1 || u2 || v2)                          by vspace_vadd_assoc
      = u1 || (u2 || v1 || v2)                          by vspace_vadd_comm
      = u1 || (u2 || (v1 || v2))                        by vspace_vadd_assoc
      = u1 || u2 || (v1 || v2)                          by vspace_vadd_assoc
      = (k1 o h || k2 o h) || (t1 + t2) |o| b           by induction hypothesis
      = (k1 + k2) o h || (t1 + t2) |o| b                by vspace_cmult_ladd
*)
val vsum_basis_stick_add = store_thm(
  "vsum_basis_stick_add",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
   !b. basis g b ==> !n1 n2. n1 IN (sticks r (LENGTH b)) /\ n2 IN (sticks r (LENGTH b)) ==>
      ((n1 |o| b) || (n2 |o| b) = (n1 + n2) |o| b)``,
  ntac 4 strip_tac >>
  Induct >| [
    rw[] >>
    `(n1 = []) /\ (n2 = [])` by metis_tac[sticks_0, IN_SING] >>
    rw[vsum_nil, stick_add_nil_nil] >>
    metis_tac[vspace_vadd_lzero, vspace_has_zero],
    rw[basis_cons, stick_cons] >>
    rw[vsum_cons, stick_add_cons_cons] >>
    qabbrev_tac `u1 = h' o h` >>
    qabbrev_tac `u2 = h'' o h` >>
    qabbrev_tac `v1 = t |o| b` >>
    qabbrev_tac `v2 = t' |o| b` >>
    `u1 IN V /\ u2 IN V` by metis_tac[vspace_cmult_vector] >>
    `v1 IN V /\ v2 IN V` by metis_tac[vsum_basis_stick_vector] >>
    `Group g /\ !x y. x IN V /\ y IN V ==> (x || y = y || x)` by metis_tac[vspace_has_abelian_group, AbelianGroup_def] >>
    `u1 || v1 || (u2 || v2) = u1 || (v1 || (u2 || v2))` by rw[group_assoc] >>
    `_ = u1 || (v1 || u2 || v2)` by rw_tac std_ss[group_assoc] >>
    `_ = u1 || (u2 || v1 || v2)` by rw[] >>
    `_ = u1 || (u2 || (v1 || v2))` by rw_tac std_ss[group_assoc] >>
    `_ = u1 || u2 || (v1 || v2)` by rw[group_assoc] >>
    metis_tac[vspace_cmult_ladd]
  ]);

(* Theorem: basis g b ==> !n. n IN (sticks r (LENGTH b)) ==> -#1 o (n |o| b) = ($- n) |o| b *)
(* Proof:
   By induction on b.
   Base case: n IN sticks r 0 ==> (-#1 o (n |o| []) = ($- n) |o| [])
      n IN sticks r 0 <=> n = []       by sticks_0, IN_SING
        -#1 o (n |o| [])
      = -#1 o ([] |o| [])              by n = []
      = -#1 o |0|                      by vsum_nil, MAP2
      = |0|                            by vspace_cmult_rzero
      = [] |o| []                      by vsum_nil, MAP2
      = ($- []) |o| []                 by stick_neg_zero
      = ($- n) |o| []                  by n = []
   Step case: basis g b ==> !n. n IN sticks r (LENGTH b) ==> (-#1 o (n |o| b) = ($- n) |o| b) ==>
              !h. basis g (h::b) ==> !n. n IN sticks r (LENGTH (h::b)) ==>
                  (-#1 o (n op (h::b)) = ($- n) |o| (h::b))
      h IN V /\ basis g b                   by basis_cons
      ?k t. k IN R /\ t IN sticks r n /\ (n = k::t)
                                            by stick_cons, LENGTH
        -#1 o (n |o| (h::b))
      = -#1 o ((k::t) |o| (h::b))           by n = k::t
      = -#1 o (k o h || t |o| b)            by vsum_cons, MAP2
      = -#1 o (k o h) || -#1 o (t |o| b)    by vspace_cmult_radd
      = -#1 o (k o h) || (($- t) |o| b)     by induction hypothesis
      = (-#1 * k) o h || (($- t) |o| b)     by vspace_cmult_cmult
      = -(#1 * k) o h || (($- t) |o| b)     by field_mult_lneg
      = -k o h || (($- t) |o| b)            by field_mult_lone
      = (-k :: $- t) |o| (h :: b)           by vsum_cons, MAP2
      = ($- n) |o| (h::b))                  by n = k::t
*)
val vsum_basis_stick_neg = store_thm(
  "vsum_basis_stick_neg",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
   !b. basis g b ==> !n. n IN (sticks r (LENGTH b)) ==> (-#1 o (n |o| b) = ($- n) |o| b)``,
  ntac 4 strip_tac >>
  `Field r` by metis_tac[vspace_has_field] >>
  `#1 IN R /\ -#1 IN R` by rw[] >>
  Induct >| [
    rw[] >>
    `n = []` by metis_tac[sticks_0, IN_SING] >>
    rw[vsum_nil, stick_neg_zero] >>
    metis_tac[vspace_cmult_rzero],
    rw[basis_cons, stick_cons] >>
    rw[vsum_cons, stick_neg_cons] >>
    `h' o h IN V` by metis_tac[vspace_cmult_vector] >>
    `t |o| b IN V` by metis_tac[vsum_basis_stick_vector] >>
    metis_tac[vspace_cmult_radd, vspace_cmult_cmult, field_mult_lneg, field_mult_lone]
  ]);

(* Theorem: basis g b ==> !c. c IN R ==> (c o (n |o| b) = (c * n) |o| b) *)
(* Proof:
   By induction on b:
   Base case: n IN sticks r 0 ==> !c. c IN R ==> (c o (n |o| []) = c * n |o| [])
      n IN sticks r 0 <=> n = []          by sticks_0, IN_SING
        c o (n |o| [])
      = c o ([] |o| [])                   by n = []
      = c o |0|                           by vsum_nil, MAP2
      = |0|                               by vspace_cmult_rzero
      = [] |o| []                         by vsum_nil, MAP2
      = (c * []) |o| []                   by stick_cmult_zero
      = (c * n) |o| []                    by n = []
   Step case: !h. basis g (h::b) ==> !n. n IN sticks r (LENGTH (h::b)) ==>
              !c. c IN R ==> (c o (n |o| (h::b)) = c * n |o| (h::b))
      h IN R /\ basis g b                 by basis_cons
      ?k t. k IN R /\ t IN sticks r (LENGTH b) /\ (n = k::t)
                                          by stick_cons
        c o (n |o| (h::b))
      = c o ((k::t) |o| (h::b))           by n = k::t
      = c o (k o h || (t |o| b))          by vsum_cons, MAP2
      = c o (k o h) || c o (t |o| b)      by vspace_cmult_radd
      = (c * k) o h || c o (t |o| b)      by vspace_cmult_cmult
      = (c * k) o h || ((c * t) |o| b)    by induction hypothesis
      = (c * k :: c * t) |o| (h :: b)     by vsum_cons, MAP2
      = (c * (k::t)) |o| (h :: b)         by stick_cmult_cons
      = (c * n) |o| (h::b)                by n = k::t
*)
val vsum_basis_stick_cmult = store_thm(
  "vsum_basis_stick_cmult",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !n. n IN (sticks r (LENGTH b)) ==> !c. c IN R ==> (c o (n |o| b) = (c * n) |o| b)``,
  ntac 4 strip_tac >>
  Induct >| [
    rw[] >>
    `n = []` by metis_tac[sticks_0, IN_SING] >>
    rw[vsum_nil, stick_cmult_zero] >>
    metis_tac[vspace_cmult_rzero],
    rw[basis_cons, stick_cons] >>
    rw[vsum_cons, stick_cmult_cons] >>
    `h' o h IN V` by metis_tac[vspace_cmult_vector] >>
    `t |o| b IN V` by metis_tac[vsum_basis_stick_vector] >>
    metis_tac[vspace_cmult_radd, vspace_cmult_cmult]
  ]);

(* Theorem: basis g b ==> (VSUM (MAP2 op (GENLIST (\j. #0) (LENGTH b)) b) = |0|) *)
(* Proof:
   By induction on b.
   Base case: GENLIST (\j. #0) 0 |o| [] = |0|
       GENLIST (\j. #0) 0 |o| []
     = [] |o| []                    by GENLIST
     = |0|                          by vsum_nil, MAP2
   Step case: basis g b ==> (GENLIST (\j. #0) (LENGTH b) |o| b = |0|) ==>
              !h. basis g (h::b) ==> (GENLIST (\j. #0) (LENGTH (h::b)) |o| (h::b) = |0|)
       basis g (h::b) ==> h IN V /\ basis g b                       by basis_cons
          GENLIST (\j. #0) (LENGTH (h::b)) |o| (h::b)
        = (#0 :: GENLIST ((\j. #0) o SUC) (LENGTH b)) |o| (h::b)    by GENLIST_CONS
        = (#0 :: GENLIST (\j. #0) (LENGTH b)) |o| (h::b)            by FUN_EQ_THM
        = VSUM (#0 o h :: MAP2 op (GENLIST (\j. #0) (LENGTH b)) b)  by MAP2
        = VSUM ( |0| :: MAP2 op (GENLIST (\j. #0) (LENGTH b)) b)    by vspace_cmult_lzero
        = |0| || (GENLIST (\j. #0) (LENGTH b) |o| b)                by vsum_cons
        = |0| || |0|                                                by induction hypothesis
        = |0|                                                       by vspace_vadd_lzero
*)
val vsum_basis_stick_zero = store_thm(
  "vsum_basis_stick_zero",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
   !b. basis g b ==> ((GENLIST (\j. #0) (LENGTH b)) |o| b = |0|)``,
  ntac 4 strip_tac >>
  Induct >-
  rw[vsum_nil] >>
  `(\j. #0) o SUC = (\j. #0)` by rw[FUN_EQ_THM] >>
  rw[basis_cons, GENLIST_CONS] >>
  metis_tac[vspace_cmult_lzero, vsum_cons, vspace_vadd_lzero, vspace_has_zero]);

(* Theorem: A vector sum can split into 3 components
   basis g b ==> !n. n IN sticks r (LENGTH b) ==> !k. k < LENGTH b ==>
   n |o| b = ((TAKE k n) |o| (TAKE k b)) || (EL k n o EL k b) || ((DROP (SUC k) n) |o| (DROP (SUC k) b)) *)
(* Proof:
   By induction on b.
   Base case: !k. k < LENGTH [] ==> ...
     Since k < LENGTH [] = 0 is F, this is true.
   Step case: !h. basis g (h::b) ==>
              !n. n IN sticks r (LENGTH (h::b)) ==> !k. k < LENGTH (h::b) ==>
      n |o| (h::b) =
        TAKE k n |o| TAKE k (h::b) || EL k n o EL k (h::b) || (DROP (SUC k) n |o| DROP (SUC k) (h::b))

     Expanding by basis_cons, stick_cons, vsum_cons, vsum_nil,
     Let v = t |o| b, there are two cases:
     (1) h' o h || v = |0| || h' o h || v
         h' o h IN V        by vspace_cmult_vector
         v IN V             by vspace_span_vector
         Hence true         by vspace_vadd_lzero
     (2) k <> 0 ==> h' o h || v = h' o h || tv || EL k (h'::t) o EL k (h::b) || dv
         where tv = (TAKE (k - 1) t) |o| (TAKE (k - 1) b)
           and dv = (DROP k t) |o| (DROP k b)
         Let k = SUC j, then j = k - 1                    by k <> 0
         Hence  v = tv || EL j t o EL j b || dv           by induction hypothesis
         and    EL (SUC j) (h'::t) = EL j t               by EL_restricted
                EL (SUC j) (h::b) = EL j b                by EL_restricted
         Now    h' o h IN V                               by vspace_cmult_vector
         basis g b ==> EL j b IN V /\
                      basis g (TAKE j b) /\
                      basis g (DROP (SUC j) b)            by basis_components_basis
         sticks r (LENGTH b) ==> EL j t IN R /\
                     TAKE j t IN sticks r j /\
                     DROP (SUC j) t IN sticks r (LENGTH b - SUC j)
                                                          by stick_components_stick
         And  LENGTH (TAKE j b) = j                       by LENGTH_TAKE
              LENGTH (DROP (SUC j) b) = LENGTH b - SUC j  by LENGTH_DROP
         Hence  tv IN V /\ dv IN V                        by vspace_span_vector
         and    EL j t o EL j b IN V                      by vspace_cmult_vector
         Putting  ej = EL j t o EL j b
           h' o h || tv || EL k (h'::t) o EL k (h::b) || dv
         = h' o h || tv || ej || dv
         = h' o h || tv || (ej || dv)                     by group_assoc
         = h' o h || (tv || ej || dv                      by group_assoc
         = h' o h || v                                    by given v
*)
val vsum_basis_split = store_thm(
  "vsum_basis_split",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !n. n IN sticks r (LENGTH b) ==> !k. k < LENGTH b ==>
   (n |o| b =
    ((TAKE k n) |o| (TAKE k b)) || (EL k n o EL k b) || ((DROP (SUC k) n) |o| (DROP (SUC k) b)))``,
  ntac 4 strip_tac >>
  Induct >-
  rw[] >>
  rw[basis_cons, stick_cons] >>
  qabbrev_tac `v = t |o| b` >>
  rw[vsum_cons, vsum_nil, TAKE_def, DROP_def] >| [
    `h' o h IN V` by metis_tac[vspace_cmult_vector] >>
    `v IN V` by metis_tac[vsum_basis_stick_vector] >>
    metis_tac[vspace_vadd_lzero],
    qabbrev_tac `tv = (TAKE (k - 1) t) |o| (TAKE (k - 1) b)` >>
    qabbrev_tac `dv = (DROP k t) |o| (DROP k b)` >>
    `?j. SUC j = k` by metis_tac[num_CASES] >>
    `(j = k - 1) /\ j < LENGTH b` by decide_tac >>
    `v = tv || EL j t o EL j b || dv` by metis_tac[] >>
    `EL (SUC j) (h'::t) = EL j t` by rw[] >>
    `EL (SUC j) (h::b) = EL j b` by rw[] >>
    `h' o h IN V` by metis_tac[vspace_cmult_vector] >>
    `EL j b IN V /\ basis g (TAKE j b) /\ basis g (DROP (SUC j) b)` by rw[basis_components_basis] >>
    `EL j t IN R /\ TAKE j t IN sticks r j /\
    DROP (SUC j) t IN sticks r (LENGTH b - SUC j)` by metis_tac[stick_components_stick] >>
    `LENGTH (TAKE j b) = j` by metis_tac[LENGTH_TAKE, LESS_IMP_LESS_OR_EQ] >>
    `LENGTH (DROP (SUC j) b) = LENGTH b - SUC j` by metis_tac[LENGTH_DROP, LESS_IMP_LESS_OR_EQ] >>
    `tv IN V /\ dv IN V` by metis_tac[vsum_basis_stick_vector] >>
    qabbrev_tac `ej = EL j t o EL j b` >>
    `ej IN V` by metis_tac[vspace_cmult_vector] >>
    `Group g` by metis_tac[vspace_has_group] >>
    `h' o h || tv || EL k (h'::t) o EL k (h::b) || dv = h' o h || tv || ej || dv` by metis_tac[] >>
    rw[group_assoc]
  ]);

(* ------------------------------------------------------------------------- *)
(* Spanning Space, the vector subspace generated by a basis.                 *)
(* ------------------------------------------------------------------------- *)

(* Spanning space by a basis (list of vectors), will be a subgroup of g (the vectors). *)
val SpanSpace_def = Define`
  SpanSpace (r:'a field) (g:'b group) (op:'a -> 'b -> 'b) (b:'b list) :'b group =
    <| carrier := IMAGE (\n. n |o| b) (sticks r (LENGTH b)); (* |o| hides op *)
            op := g.op; (* type: 'b -> 'b -> 'b *)
            id := g.id
     |>
`;

(* Theorem: properties of SpanSpace. *)
(* Proof: by SpanSpace_def. *)
val vspace_span_property = store_thm(
  "vspace_span_property",
  ``!(r:'a field) (g:'b group) op (b:'b list).
   ((SpanSpace r g op b).carrier = IMAGE (\n. n |o| b) (sticks r (LENGTH b))) /\
   ((SpanSpace r g op b).op = g.op) /\ ((SpanSpace r g op b).id = g.id) /\
   (!n. n IN (sticks r (LENGTH b)) ==> (n |o| b) IN (SpanSpace r g op b).carrier) /\
   (!v. v IN (SpanSpace r g op b).carrier ==> ?n. n IN sticks r (LENGTH b) /\ (v = n |o| b))``,
  rw[SpanSpace_def] >>
  metis_tac[]);

(* Theorem: basis g b ==> !x. x IN (SpanSpace r g op b).carrier ==> x IN V  *)
(* Proof:
   By SpanSpace_def and IN_IMAGE, this is to show:
      basis g b ==> !n. n IN sticks r (LENGTH b) ==> n |o| b IN V
   which is true by vsum_basis_stick_vector.
*)
val vspace_span_vector = store_thm(
  "vspace_span_vector",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
   !b. basis g b ==> !x. x IN (SpanSpace r g op b).carrier ==> x IN V``,
  rw[SpanSpace_def] >>
  metis_tac[vsum_basis_stick_vector]);

(* Theorem: basis g b ==> (SpanSpace r g op b).carrier SUBSET V *)
(* Proof: by vspace_span_vector, SUBSET_DEF. *)
val vspace_span_subspace = store_thm(
  "vspace_span_subspace",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
   !b. basis g b ==> (SpanSpace r g op b).carrier SUBSET V``,
  metis_tac[vspace_span_vector, SUBSET_DEF]);

(* Theorem: Closure for Group (SpanSpace r g op b)
            x IN (SpanSpace r g op b).carrier /\ y IN (SpanSpace r g op b).carrier ==>
            x || y IN (SpanSpace r g op b).carrier  *)
(* Proof:
   By SpanSpace_def, and IN_IMAGE, this is to show:
      basis g b /\ n IN sticks r (LENGTH b) /\ n' IN sticks r (LENGTH b) ==>
      ?n''. (n |o| b || (n' |o| b) = n'' |o| b) /\ n'' IN sticks r (LENGTH b)
   Let n'' = n + n' IN sticks r (LENGTH b)        by stick_add_length
    and (n |o| b) || (n' |o| b) = (n + n') |o| b  by vsum_basis_stick_add
*)
val vspace_span_closure = store_thm(
  "vspace_span_closure",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !x y. x IN (SpanSpace r g op b).carrier /\ y IN (SpanSpace r g op b).carrier ==>
           x || y IN (SpanSpace r g op b).carrier``,
  rw[SpanSpace_def] >>
  metis_tac[vspace_has_field, stick_add_length, vsum_basis_stick_add]);

(* Theorem: Inverse for Group (SpanSpace r g op b)
            x IN (SpanSpace r g op b).carrier ==> ?y. y IN (SpanSpace r g op b) /\ (y || x = |0|) *)
(* Proof:
   By SpanSpace_def and IN_IMAGE, this is to show:
      n IN sticks r (LENGTH b) ==>
      ?y. (?n. (y = n |o| b) /\ n IN sticks r (LENGTH b)) /\ (y || (n |o| b) = |0|)
   Let y = (- #1) o (n |o| b)
         = ($- n) op b                         by vsum_basis_stick_neg
   Let n = $- n IN sticks r (LENGTH b)         by stick_neg_length
   Since (n |o| b) IN V                        by vsum_basis_stick_vector
         y = (- #1) o (n |o| b) IN V           by vspace_cmult_vector
     and y || (n |o| b)
       = (- #1) o (n |o| b) || (n |o| b)
       = |0|                                   by vspace_vsub_eq_zero_alt
*)
val vspace_span_negative = store_thm(
  "vspace_span_negative",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !x. x IN (SpanSpace r g op b).carrier ==> ?y. y IN (SpanSpace r g op b).carrier /\ (y || x = |0|)``,
  rw[SpanSpace_def] >>
  qexists_tac `(- #1) o (n |o| b)` >>
  rpt strip_tac >| [
    qexists_tac `$- n` >>
    metis_tac[vsum_basis_stick_neg, stick_neg_length, vspace_has_field],
    metis_tac[vsum_basis_stick_vector, vspace_vsub_eq_zero_alt]
  ]);

(* Theorem: basis g b ==> |0| IN (SpanSpace r g op b).carrier *)
(* Proof:
   By SpanSpace_def and IN_IMAGE, this is to show:
      ?n. ( |0| = n |o| b) /\ n IN sticks r (LENGTH b)
   Let n = GENLIST (\j. #0) (LENGTH b).
   Then n |o| b
      = (GENLIST (\j. #0) (LENGTH b)) |o| b                 by above
      = |0|                                                 by vsum_basis_stick_zero
    and GENLIST (\j. #0) (LENGTH b) IN sticks r (LENGTH b)  by stick_all_zero
*)
val vspace_span_has_zero = store_thm(
  "vspace_span_has_zero",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
   !b. basis g b ==> |0| IN (SpanSpace r g op b).carrier``,
  rw[SpanSpace_def] >>
  qexists_tac `GENLIST (\j. #0) (LENGTH b)` >>
  rpt strip_tac >-
  rw[vsum_basis_stick_zero] >>
  metis_tac[stick_all_zero]);

(* Theorem: basis g b ==> Group (SpanSpace r g op b) *)
(* Proof:
   This is to show the group axioms:
   (1) x, y IN (SpanSpace r g op b).carrier ==> x || y IN (SpanSpace r g op b).carrier
       True by vspace_span_closure.
   (2) x, y, z IN (SpanSpace r g op b).carrier ==> x || y || z = x || (y || z)
       True by group_assoc, vspace_span_vector.
   (3) |0| IN (SpanSpace r g op b).carrier
       True by vspace_span_has_zero.
   (4) x IN (SpanSpace r g op b).carrier ==> |0| || x = x
       True by group_lid,  vspace_span_vector.
   (5) x IN (SpanSpace r g op b).carrier ==> ?y. y IN (SpanSpace r g op b).carrier /\ (y || x = |0|)
       True by vspace_span_negative.
*)
val vspace_span_group = store_thm(
  "vspace_span_group",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==> Group (SpanSpace r g op b)``,
  rw_tac std_ss[group_def_alt] >| [
    metis_tac[vspace_span_closure, vspace_span_property],
    metis_tac[vspace_has_group, group_assoc, vspace_span_vector, vspace_span_property],
    metis_tac[vspace_span_has_zero, vspace_span_property],
    metis_tac[vspace_has_group, group_lid, vspace_span_vector, vspace_span_property],
    metis_tac[vspace_span_negative, vspace_span_property]
  ]);

(* Theorem: basis g b ==> AbelianGroup (SpanSpace r g op b) *)
(* Proof:
   This is to show:
   (1) Group (SpanSpace r g op b), true by vspace_span_group.
   (2) x IN (SpanSpace r g op b).carrier /\ y IN (SpanSpace r g op b).carrier ==> x || y = y || x
       True by vspace_has_abelian_group, vspace_span_vector.
*)
val vspace_span_abelian_group = store_thm(
  "vspace_span_abelian_group",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==> AbelianGroup (SpanSpace r g op b)``,
  rw_tac std_ss[AbelianGroup_def, vspace_span_group] >>
  `AbelianGroup g` by metis_tac[vspace_has_abelian_group] >>
  metis_tac[vspace_span_vector, AbelianGroup_def, vspace_span_property]);

(* Theorem: Scalar Multiplication for SpanSpace
            c IN R /\ x IN (SpanSpace r g op b).carrier ==> c o x IN (SpanSpace r g op b).carrier *)
(* Proof:
   By SpanSpace_def and IN_IMAGE, this is to show:
      ?n'. (c o (n |o| b) = n' |o| b) /\ n' IN sticks r (LENGTH b)
   Let n' = c * n IN sticks r (LENGTH b)      by stick_cmult_length
   Then   n' |o| b
        = (c * n) |o| b                       by n' = c * n
        = c o (n |o| b)                       by vsum_basis_stick_cmult
*)
val vspace_span_cmult = store_thm(
  "vspace_span_cmult",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
     !c x. c IN R /\ x IN (SpanSpace r g op b).carrier ==> c o x IN (SpanSpace r g op b).carrier``,
  rw[SpanSpace_def] >>
  qexists_tac `c * n` >>
  metis_tac[vsum_basis_stick_cmult, stick_cmult_length, vspace_has_field]);

(* Theorem: !b. VSpace r (SpanSpace r g op b) op *)
(* Proof:
   By VSpace_def, this is to show:
   (1) Field r
       True by vspace_has_field.
   (2) AbelianGroup (SpanSpace r g op b)
       True by vspace_span_abelian_group.
   (3) a IN R /\ v IN (SpanSpace r g op b).carrier ==> a o v IN (SpanSpace r g op b).carrier
       True by vspace_span_cmult.
   (4) a IN R /\ b' IN R /\ v IN (SpanSpace r g op b).carrier ==> a o b' o v = (a * b') o v
       True by vspace_span_vector, vspace_cmult_cmult.
   (5) v IN (SpanSpace r g op b).carrier ==> #1 o v = v
       True by vspace_span_vector, vspace_cmult_lone.
   (6) a IN R /\ u, v IN (SpanSpace r g op b).carrier ==> a o (u || v) = (a o u) || (a o v)
       True by vspace_span_vector, vspace_cmult_radd.
   (7) a IN R /\ b' IN R /\ v IN (SpanSpace r g op b).carrier ==> (a + b') o v = (a o v) || (b' o v)
       True by vspace_span_vector, vspace_cmult_ladd.
*)
val vspace_span_vspace = store_thm(
  "vspace_span_vspace",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==> VSpace r (SpanSpace r g op b) op``,
  rpt strip_tac >>
  rw[VSpace_def] >| [
    metis_tac[vspace_has_field],
    rw[vspace_span_abelian_group],
    rw[vspace_span_cmult],
    metis_tac[vspace_span_vector, vspace_cmult_cmult],
    metis_tac[vspace_span_vector, vspace_cmult_lone],
    metis_tac[vspace_span_vector, vspace_cmult_radd, vspace_span_property],
    metis_tac[vspace_span_vector, vspace_cmult_ladd, vspace_span_property]
  ]);

(* Theorem: basis g b ==> ?z. z IN sticks r (LENGTH b) /\ (z |o| b = |0|) *)
(* Proof:
   Let z = GENLIST (\j. #0) (LENGTH b)
   Then z IN sticks r (LENGTH b)     by stick_all_zero
    and z |o| b = |0|                by vsum_basis_stick_zero
*)
val vspace_zero_stick = store_thm(
  "vspace_zero_stick",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
   !b. basis g b ==> ?z. z IN sticks r (LENGTH b) /\ (z |o| b = |0|)``,
  metis_tac[stick_all_zero, vsum_basis_stick_zero]);

(* Theorem: n IN sticks r (LENGTH b) /\ !k. k < LENGTH b ==> (EL k n = #0) ==> n |o| b = |0| *)
(* Proof:
   By induction on b.
   Base case: n IN sticks r 0 ==> n |o| [] = |0|
      n IN sticks r 0 <=> n = []       by sticks_0, IN_SING
        n |o| []
      = [] |o| []                      by n = []
      = |0|                            by vsum_nil, MAP2
   Step case: !h. basis g (h::b) ==> !n. n IN sticks r (LENGTH (h::b)) ==> n |o| (h::b) = |0|
      h IN R /\ basis g b              by basis_cons
      ?k t. k IN R /\ t IN sticks r (LENGTH b) /\ (n = k::t)
                                       by stick_cons
        n |o| (h::b)
      = (k::t) |o| (h::b))             by n = k::t
      = k o h || (t |o| b)             by vsum_cons, MAP2
      Given !k. k < SUC (LENGTH b) ==> (EL k (h'::t) = #0)
        <=> 0 < SUC (LENGTH b) ==> (EL 0 (h'::t) = #0)             case k = 0
        and SUC k < SUC (LENGTH b) ==> (EL (SUC k) (h'::t) = #0)   case k = SUC k
      Now  0 < SUC (LENGTH b)          by SUC_POS, or prim_recTheory.LESS_0
       so  EL 0 (k::t) = k = #0        by EL, HD
      Thus k o h = #0 o h = |0|        by vspace_cmult_lzero
      Also EL (SUC k) (h'::t) = EL k t by EL_restricted
      Thus t |o| b = |0|               by induction hypothesis
      Hence n |o| (h::b)
          = |0| || |0| = |0|           by vspace_vadd_lzero
*)
val vspace_stick_zero = store_thm(
  "vspace_stick_zero",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !n. n IN sticks r (LENGTH b) /\ (!k. k < LENGTH b ==> (EL k n = #0)) ==> (n |o| b = |0|)``,
  ntac 4 strip_tac >>
  Induct >| [
    rw[] >>
    `n = []` by metis_tac[sticks_0, IN_SING] >>
    rw[vsum_nil],
    rw[basis_cons, stick_cons] >>
    rw[vsum_cons] >>
    `EL 0 (h'::t) = h'` by rw[EL] >>
    `(!k. k < SUC (LENGTH b) ==> (EL k (h'::t) = #0)) ==>
    (0 < SUC (LENGTH b) ==> (EL 0 (h'::t) = #0)) /\
    (!k. (SUC k) < SUC (LENGTH b) ==> (EL (SUC k) (h'::t) = #0))` by metis_tac[num_CASES] >>
    `0 < SUC (LENGTH b)` by decide_tac >>
    `h' o h = |0|` by metis_tac[vspace_cmult_lzero] >>
    `!k y. SUC k < SUC y <=> k < y` by decide_tac >>
    `!k h t. EL (SUC k) (h::t) = EL k t` by rw[] >>
    metis_tac[vspace_vadd_lzero, vspace_has_zero]
  ]);

(* Theorem: basis g b ==> !x. MEM x b ==> ?n. n IN sticks r (LENGTH b) /\ (x = n |o| b) *)
(* Proof:
   By induction on b.
   Base case: basis g [] ==> MEM x [] ==> ...
     basis g [] = T               by basis_nil
     MEM x [] = F, hence true     by MEM
   Step case: basis g b ==> !x. MEM x b ==> ?n. n IN sticks r (LENGTH b) /\ (x = n |o| b) ==>
              basis g (h::b) /\ MEM x (h::b) ==> ?n. n IN sticks r (LENGTH (h::b)) /\ (x = n |o| (h::b))
     By basis_cons, this is to show:
     (1) h IN V /\ basis g h ==> ?n. n IN sticks r (SUC (LENGTH b)) /\ (h = n |o| (h::b))
         ?z. z IN sticks r (LENGTH b) /\ (z |o| b = |0|)     by vspace_zero_stick
         Let n = #1::z, #1 with all the rest #0.
         Then #1::z IN sticks r (SUC (LENGTH b))             by stick_cons
           n |o| (h::b)
         = (#1::z) |o| (h::b)                                by n = #1::z
         = VSUM (#1 o h :: MAP2 op z b)                      by MAP2
         = VSUM (h :: MAP2 op z b)                           by vspace_cmult_lone
         = h || (z |o| b)                                    by vsum_cons
         = h || |0|                                          by above property of z
         = h                                                 by vspace_vadd_rzero
     (2) h IN V /\ basis g h /\ MEM x b ==> ?n. n IN sticks r (SUC (LENGTH b)) /\ (x = n |o| (h::b))
         ?t. t IN sticks r (LENGTH b) /\ (x = t |o| b)       by induction hypothesis
         Let n = #0::t, #0 with all the rest #0.
         Then #0::t IN sticks r (SUC (LENGTH b))             by stick_cons
           n |o| (h::b)
         = (#0::t) |o| (h::b)                                by n = #0::t
         = VSUM (#0 o h :: (MAP2 op t b))                    by MAP2
         = VSUM ( |0| :: (MAP2 op t b))                      by vspace_cmult_lzero
         = |0| || (t |o| b)                                  by vsum_cons
         = |0| || x                                          by induction hypothesis
         = x                                                 by vspace_vadd_lzero
*)
val vspace_basis_stick = store_thm(
  "vspace_basis_stick",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !x. MEM x b ==> ?n. n IN sticks r (LENGTH b) /\ (x = n |o| b)``,
  ntac 4 strip_tac >>
  `Field r` by metis_tac[vspace_has_field] >>
  `#0 IN R /\ #1 IN R` by rw[] >>
  Induct >-
  rw[] >>
  rw[basis_cons] >| [
    `?z. z IN sticks r (LENGTH b) /\ (z |o| b = |0|)` by rw[vspace_zero_stick] >>
    qexists_tac `#1::z` >>
    rw[vsum_cons, stick_cons] >>
    metis_tac[vspace_cmult_lone, vspace_vadd_rzero],
    `?t. t IN sticks r (LENGTH b) /\ (x = t |o| b)` by rw[] >>
    qexists_tac `#0::t` >>
    rw[vsum_cons, stick_cons] >>
    metis_tac[vspace_cmult_lzero, vsum_basis_stick_vector, vspace_vadd_lzero]
  ]);

(* Theorem: n1 IN sticks r (LENGTH b) /\ n2 IN sticks r (LENGTH b) ==>
            (n1 + n2) |o| b = (n1 |o| b) || (n2 |o| b) *)
(* Proof: by vsum_basis_stick_add. *)
val vsum_stick_add = store_thm(
  "vsum_stick_add",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !n1 n2. n1 IN sticks r (LENGTH b) /\ n2 IN sticks r (LENGTH b) ==>
            ((n1 + n2) |o| b = (n1 |o| b) || (n2 |o| b))``,
  rw[vsum_basis_stick_add]);

(* Theorem: n IN sticks r (LENGTH b) ==> g.inv (n |o| b) = ($- n) |o| b *)
(* Proof:
   Let v = n |o| b, u = ($- n) |o| b
   This is to show: g.inv v = u
     Now ($- n) IN sticks r (LENGTH b)    by stick_neg_length
      so v IN V and u IN V                by vsum_basis_stick_vector
   Since u = -#1 o v                      by vsum_basis_stick_neg
      so u || v = -#1 o v || v = |0|      by vspace_vsub_eq_zero_alt
    With Group g                          by vspace_has_group
   Hence u = g.inv v                      by group_linv_unique
*)
val vsum_stick_neg = store_thm(
  "vsum_stick_neg",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !n. n IN sticks r (LENGTH b) ==> (g.inv (n |o| b) = ($- n) |o| b)``,
  rpt strip_tac >>
  qabbrev_tac `v = n |o| b` >>
  qabbrev_tac `u = ($- n) |o| b` >>
  `Field r` by metis_tac[vspace_has_field] >>
  `u IN V /\ v IN V` by metis_tac[vsum_basis_stick_vector, stick_neg_length] >>
  `u || v = (-#1 o v) || v` by rw[vsum_basis_stick_neg, Abbr`v`, Abbr`u`] >>
  `_ = |0|` by rw[GSYM vspace_vsub_eq_zero_alt] >>
  metis_tac[group_linv_unique, vspace_has_group]);

(* Theorem: n1 IN sticks r (LENGTH b) /\ n2 IN sticks r (LENGTH b) ==>
            (n1 - n2) |o| b = (n1 |o| b) || g.inv (n2 |o| b) *)
(* Proof:
     (n1 - n2) |o| b
   = (n1 + $- n2) |o| b               by stick_sub_alt
   = (n1 |o| b) || (($- n2) |o| b)    by vsum_stick_add
   = (n1 |o| b) || g.inv (n2 |o| b)   by vsum_stick_neg
*)
val vsum_stick_sub = store_thm(
  "vsum_stick_sub",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !n1 n2. n1 IN sticks r (LENGTH b) /\ n2 IN sticks r (LENGTH b) ==>
            ((n1 - n2) |o| b = (n1 |o| b) || g.inv (n2 |o| b))``,
  rpt strip_tac >>
  `Field r` by metis_tac[vspace_has_field] >>
  `(n1 - n2) |o| b = (n1 + $- n2) |o| b` by metis_tac[stick_sub_alt] >>
  rw[vsum_stick_add, stick_neg_length, GSYM vsum_stick_neg]);

(* Theorem: c IN R /\ n IN sticks r (LENGTH b) ==> c o (n |o| b) = (c * n) |o| b *)
(* Proof: by vsum_basis_stick_cmult. *)
val vsum_stick_cmult = store_thm(
  "vsum_stick_cmult",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !c n. c IN R /\ n IN sticks r (LENGTH b) ==> (c o (n |o| b) = (c * n) |o| b)``,
  rw[vsum_basis_stick_cmult]);


(*
- MAP_SNOC;
> val it = |- !f x l. MAP f (SNOC x l) = SNOC (f x) (MAP f l) : thm
- ZIP SNOC:
val it = |- !x1 x2 l1 l2. (LENGTH l1 = LENGTH l2) ==>
                          (ZIP (SNOC x1 l1,SNOC x2 l2) = SNOC (x1,x2) (ZIP (l1,l2))): thm

- EL_ZIP;
> val it = |- !l1 l2 n. (LENGTH l1 = LENGTH l2) /\ n < LENGTH l1 ==> (EL n (ZIP (l1,l2)) = (EL n l1,EL n l2)) : thm
- EL_SNOC;
> val it = |- !n l. n < LENGTH l ==> !x. EL n (SNOC x l) = EL n l : thm
*)

(* Theorem: basis g b ==> !n. n IN sticks r (LENGTH b) ==>
            !h v. h IN R /\ v IN V ==> ((h o v) || (n |o| b) = (h::n) |o| (v::b)) *)
(* Proof: by vsum_cons, MAP2 *)
val vsum_stick_cons = store_thm(
  "vsum_stick_cons",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
    !n. n IN sticks r (LENGTH b) ==>
    !h v. h IN R /\ v IN V ==> ((h o v) || (n |o| b) = (h::n) |o| (v::b))``,
  rw[vsum_cons]);

(* Theorem: n IN sticks r (LENGTH b) ==> !h v. h IN R /\ v IN V ==>
            (SNOC h n) |o| (SNOC v b) = h o v || (n |o| b) *)
(* Proof:
   By induction on b.
   Base case: n IN sticks r 0 ==> (SNOC h n) |o| (SNOC v []) = h o v || (n |o| [])
      n IN sticks r 0 <=> n = []           by sticks_0, IN_SING
       (SNOC h n) |o| (SNOC v [])
     = (SNOC h []) |o| (SNOC v [])         by n = []
     = [h] |o| [v]                         by SNOC
     = h o v || |0|                        by vsum_cons, MAP2
     = h o v || ([] |o| [])                by vsum_cons, MAP2
     = h o v || (n |o| [])                 by n = []
   Step case: !h. basis g (h::b) ==> !n. n IN sticks r (LENGTH (h::b)) ==>
              !h' v. h' IN R /\ v IN V ==> SNOC h' n |o| SNOC v (h::b) = h' o v || (n |o| (h::b))
     After expanding by basis_cons, stick_cons, SNOC, this is to show:
        (SNOC h'' (h'::t)) |o| (h::SNOC v b) = h'' o v || (h'::t) |o| (h::b)
     Let u = t |o| b  IN V                          by vsum_basis_stick_vector
     and h' o h IN V and h'' o v IN V               by vspace_cmult_vector
       (SNOC h'' (h'::t)) |o| (h::SNOC v b)
     = (h' ::(SNOC h'' t)) |o| (h::SNOC v b))       by SNOC
     = h' o h || (SNOC h'' t) |o| (SNOC v b)        by vsum_cons, MAP2
     = h' o h || (h'' o v || u                      by induction hypothesis
     = h' o h || h'' o v || u                       by vspace_vadd_assoc
     = h'' o v || h' o h || u                       by vspace_vadd_comm
     = h'' o v || ((h' o h || u)                    by vspace_vadd_assoc
     = h'' o v || (h'::t) |o| (h::b)                by vsum_cons, MAP2
*)
val vsum_stick_snoc = store_thm(
  "vsum_stick_snoc",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !n. n IN sticks r (LENGTH b) ==> !h v. h IN R /\ v IN V ==>
   ((SNOC h n) |o| (SNOC v b) = h o v || (n |o| b))``,
  ntac 4 strip_tac >>
  Induct >| [
    rw[] >>
    `n = []` by metis_tac[sticks_0, IN_SING] >>
    rw[vsum_cons],
    rw[basis_cons, stick_cons] >>
    qabbrev_tac `u = t |o| b` >>
    rw[vsum_cons] >>
    `h' o h IN V /\ h'' o v IN V` by metis_tac[vspace_cmult_vector] >>
    `u IN V` by metis_tac[vsum_basis_stick_vector] >>
    metis_tac[vspace_vadd_assoc, vspace_vadd_comm]
  ]);

(* ------------------------------------------------------------------------- *)
(* More on SpanSpace.                                                        *)
(* ------------------------------------------------------------------------- *)

(* Theorem: h IN V /\ SpanSpace r g op b1 = SpanSpace r g op b2 ==>
            SpanSpace r g op (h::b1) = SpanSpace r g op (h::b2) *)
(* Proof:
   By SpanSpace_def, monoid_component_equality, and stick_cons, this is to show:
   (1) h' IN R /\ t IN sticks r (LENGTH b1) ==>
       ?n. ((h'::t) |o| (h::b1) = n |o| (h::b2)) /\
         ?h t. h IN R /\ t IN sticks r (LENGTH b2) /\ (n = h::t)

       ?n'.(n |o| (h::b1) = n' |o| (h::b2)) /\ n' IN sticks r (LENGTH (h::b2))
       Let x = t |o| b1,
       then ?n'. (x = n' |o| b2) /\ n' IN sticks r (LENGTH b2)  by monoid_component_equality
       Let n = h'::n', result follows                           by vsum_cons
   (2) h' IN R /\ t IN sticks r (LENGTH b2) ==>
       ?n. ((h'::t) |o| (h::b2) = n |o| (h::b1)) /\
         ?h t. h IN R /\ t IN sticks r (LENGTH b1) /\ (n = h::t)

       Let x = t |o| b2,
       then ?n'. (x = n' |o| b1) /\ n' IN sticks r (LENGTH b1)  by monoid_component_equality
       Let n = h'::n', result follows                           by vsum_cons
*)
val vspace_span_cons = store_thm(
  "vspace_span_cons",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
     !b1 b2. basis g b1 /\ basis g b2 /\ (SpanSpace r g op b1 = SpanSpace r g op b2) ==>
      !h. h IN V ==> (SpanSpace r g op (h::b1) = SpanSpace r g op (h::b2))``,
  rw[SpanSpace_def, monoid_component_equality, stick_cons, EXTENSION, EQ_IMP_THM] >| [
    qabbrev_tac `x = t |o| b1` >>
    `?n'. (x = n' |o| b2) /\ n' IN sticks r (LENGTH b2)` by metis_tac[] >>
    qexists_tac `h'::n'` >>
    rw[vsum_cons],
    qabbrev_tac `x = t |o| b2` >>
    `?n'. (x = n' |o| b1) /\ n' IN sticks r (LENGTH b1)` by metis_tac[] >>
    qexists_tac `h'::n'` >>
    rw[vsum_cons]
  ]);

(* Theorem: u IN V /\ v IN V ==> (SpanSpace r g op [u; v] = SpanSpace r g op [v; u]) *)
(* Proof:
   Note VSpace r g op ==> AbelianGroup g     by vspace_has_abelian_group
     or Group g /\ !x y. x IN V /\ y IN V ==> (x || y = y || x)  by AbelianGroup_def
     so |0| IN V                             by group_id_element
    and !c. c IN R ==> c o u IN V /\ c o v IN V   by vspace_cmult_vector
   By SpanSpace_def and monoid_component_equality, this is to show:
   (1) n IN sticks r 2 ==> ?n'. (n |o| [u; v] = n' |o| [v; u]) /\ n' IN sticks r 2
       ?h t. h IN R /\ t IN R /\ (n = [h;t]) by stick_cons, sticks_0, IN_SING
       Let n' = [t; h] IN sticks r 2         by stick_cons, sticks_0, IN_SING
       Then n |o| [u; v]
          = [h; t] |o| [u; v]                by n = [h; t]
          = h o u || (t o v || |0|)          by vsum_cons, vsum_nil, MAP2
          = h o u || t o v                   by group_rid
          = t o v || h o u                   by abelian condition
          = t o v || (h o u || |0|)          by group_rid
          = [t; h] |o| [v; u]                by vsum_cons, vsum_nil, MAP2
          = n' |o| [v; u]                    by n' = [t; h]
   (2) n IN sticks r 2 ==> ?n'. (n |o| [v; u] = n' |o| [u; v]) /\ n' IN sticks r 2
       ?h t. h IN R /\ t IN R /\ (n = [h;t]) by stick_cons, sticks_0, IN_SING
       Let n' = [t; h] IN sticks r 2         by stick_cons, sticks_0, IN_SING
       Then n |o| [v; u]
          = [h; t] |o| [v; u]                by n = [h; t]
          = h o v || (t o u || |0|)          by vsum_cons, vsum_nil, MAP2
          = h o v || t o u                   by group_rid
          = t o u || h o v                   by abelian condition
          = t o u || (h o v || |0|)          by group_rid
          = [t; h] |o| [u; v]                by vsum_cons, vsum_nil, MAP2
          = n' |o| [u; v]                    by n' = [t; h]
*)
val vspace_span_exchange_two = store_thm(
  "vspace_span_exchange_two",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
   !u v. u IN V /\ v IN V ==> (SpanSpace r g op [u; v] = SpanSpace r g op [v; u])``,
  rpt strip_tac >>
  `AbelianGroup g` by metis_tac[vspace_has_abelian_group] >>
  `Group g /\ !x y. x IN V /\ y IN V ==> (x || y = y || x)` by metis_tac[AbelianGroup_def] >>
  `|0| IN V` by rw[] >>
  `!c. c IN R ==> c o u IN V /\ c o v IN V` by metis_tac[vspace_cmult_vector] >>
  rw[SpanSpace_def, monoid_component_equality, EXTENSION, EQ_IMP_THM] >| [
    `(2 = SUC 1) /\ (1 = SUC 0)` by decide_tac >>
    `?h t. h IN R /\ t IN R /\ (n = [h;t])` by metis_tac[stick_cons, sticks_0, IN_SING] >>
    qexists_tac `[t;h]` >>
    `[t;h] IN sticks r 2` by metis_tac[stick_cons, sticks_0, IN_SING] >>
    rw[vsum_nil, vsum_cons],
    `(2 = SUC 1) /\ (1 = SUC 0)` by decide_tac >>
    `?h t. h IN R /\ t IN R /\ (n = [h;t])` by metis_tac[stick_cons, sticks_0, IN_SING] >>
    qexists_tac `[t;h]` >>
    `[t;h] IN sticks r 2` by metis_tac[stick_cons, sticks_0, IN_SING] >>
    rw[vsum_nil, vsum_cons]
  ]);
(* First thought is to prove the next one by induction, then exchange_two is the Base case. *)

(* Theorem: SpanSpace r g op (u::v::b) = SpanSpace r g op (v::u::b) *)
(* Proof:
   By SpanSpace_def and monoid_component_equality, this is to show:
   (1) n IN sticks r (SUC (SUC (LENGTH b))) ==>
         ?n'. (n |o| (u::v::b) = n' |o| (v::u::b)) /\ n' IN sticks r (SUC (SUC (LENGTH b)))
       ?x y t. x, y IN R /\ t IN sticks r (LENGTH b) /\ (n = x::y::t)  by stick_cons
       Let n' = y::x::t IN sticks r (SUC (SUC (LENGTH b)))             by stick_cons
       Let w = t |o| b IN V                 by vsum_basis_stick_vector
       and x o u IN V, y o v IN V           by vspace_cmult_vector
       Then  n |o| (u::v::b)
           = (x::y::t) |o| (u::v::b)        by n = x::y::t
           = x o u || (y o v || w)          by vsum_cons, MAP2
           = x o u || y o v || w            by vspace_vadd_assoc
           = y o v || x o u || w            by vspace_vadd_comm
           = y o v || (x o u || w)          by vspace_vadd_assoc
           = (y::x::t) |o| (v::u::b)        by vsum_cons, MAP2
           = n' |o| (v::u::b)               by n' = y::x::t
   (2) n IN sticks r (SUC (SUC (LENGTH b))) ==>
         ?n'. (n |o| (v::u::b) = n' |o| (u::v::b)) /\ n' IN sticks r (SUC (SUC (LENGTH b)))
       ?x y t. x, y IN R /\ t IN sticks r (LENGTH b) /\ (n = x::y::t)  by stick_cons
       Let n' = y::x::t IN sticks r (SUC (SUC (LENGTH b)))             by stick_cons
       Let w = t |o| b IN V                 by vsum_basis_stick_vector
       and x o v IN V, y o u IN V           by vspace_cmult_vector
       Then  n |o| (v::u::b)
           = (x::y::t) |o| (v::u::b)        by n = x::y::t
           = x o v || (y o u || w)          by vsum_cons, MAP2
           = x o v || y o u || w            by vspace_vadd_assoc
           = y o u || x o v || w            by vspace_vadd_comm
           = y o u || (x o v || w)          by vspace_vadd_assoc
           = n' |o| (u::v::b))              by n' = y::x::t
*)
val vspace_span_exchange = store_thm(
  "vspace_span_exchange",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !u v. u IN V /\ v IN V ==> (SpanSpace r g op (u::v::b) = SpanSpace r g op (v::u::b))``,
  rpt strip_tac >>
  rw[SpanSpace_def, monoid_component_equality, EXTENSION, EQ_IMP_THM] >| [
    `?x t1. x IN R /\ t1 IN sticks r (SUC (LENGTH b)) /\ (n = x::t1)` by metis_tac[stick_cons] >>
    `?y t. y IN R /\ t IN sticks r (LENGTH b) /\ (n = x::y::t)` by metis_tac[stick_cons] >>
    qexists_tac `y::x::t` >>
    `y::x::t IN sticks r (SUC (SUC (LENGTH b)))` by metis_tac[stick_cons] >>
    qabbrev_tac `w = t|o| b` >>
    rw[vsum_cons] >>
    `w IN V` by metis_tac[vsum_basis_stick_vector] >>
    `x o u IN V /\ y o v IN V` by metis_tac[vspace_cmult_vector] >>
    metis_tac[vspace_vadd_comm, vspace_vadd_assoc],
    `?x t1. x IN R /\ t1 IN sticks r (SUC (LENGTH b)) /\ (n = x::t1)` by metis_tac[stick_cons] >>
    `?y t. y IN R /\ t IN sticks r (LENGTH b) /\ (n = x::y::t)` by metis_tac[stick_cons] >>
    qexists_tac `y::x::t` >>
    `y::x::t IN sticks r (SUC (SUC (LENGTH b)))` by metis_tac[stick_cons] >>
    qabbrev_tac `w = t |o| b` >>
    rw[vsum_cons] >>
    `w IN V` by metis_tac[vsum_basis_stick_vector] >>
    `x o v IN V /\ y o u IN V` by metis_tac[vspace_cmult_vector] >>
    metis_tac[vspace_vadd_comm, vspace_vadd_assoc]
  ]);

(* Theorem: v IN (SpanSpace r g op b).carrier ==> SpanSpace r g op b = SpanSpace r g op (v::b) *)
(* Proof:
   By SpanSpace_def and monoid_component_equality, this is to show:
   (1) v IN (SpanSpace r g op b).carrier /\ n IN sticks r (LENGTH b) ==>
         ?n'. (n |o| b = n' |o| (v::b)) /\ n' IN sticks r (SUC (LENGTH b))
       Let n' = #0::n IN sticks r (SUC (LENGTH b))     by stick_cons
       Let u = n |o| b IN V                            by vsum_basis_stick_vector
       and v IN V                                      by vspace_span_vector
         n' |o| (v::b)
       = (#0::n) |o| (v::b)                            by n' = #0::n
       = #0 o v || u                                   by vsum_cons
       = |0| || u                                      by vspace_cmult_lzero
       = u                                             by vspace_vadd_lzero
   (2) v IN (SpanSpace r g op b).carrier /\ n IN sticks r (LENGTH b) ==>
         ?n'. (n |o| (v::b) = n' |o| b) /\ n' IN sticks r (LENGTH b)
       ?k t. k IN R /\ t IN sticks r (LENGTH b) /\ (n = k::t)    by stick_cons of n
       ?m. m IN sticks r (LENGTH b) /\ (v = VSUM (MAP2 op m b))  by vspace_span_property of v
       Let mv = m |o| b, with v = mv,
           tv = t |o| b.
       Let n' = k * m + t IN sticks r (LENGTH b)       by stick_cmult_length, stick_add_length
         n' |o| b
       = (k * m + t) |o| b                             by n' = k * m + t
       = (k * m) |o| b) || tv                          by vsum_stick_add
       = k o mv || tv                                  by vsum_stick_cmult
       = k o v || tv                                   by v = mv
       = (k::t) |o| (v::b)                             by vsum_cons, MAP2
       = n |o| (v::b)                                  by n = k::t

   The basic reason is this:
   v IN (SpanSpace r g op b).carrier  means v is some linear combination of vectors in b.
   SpanSpace r g op (v::b) has all linear combinations of v and those in b.
   e.g. u IN (SpanSpace r g op (v::b)).carrier means there is (k::t) IN sticks r SUC (LENGTH b)
   and  u = (k::t) |o| (v::b)
          = (k o v) || (t |o| b)
          = k o (n |o| b) || (t |o| b)
          = (k * n) |o| b) || (t |o| b)
          = (k * n + t) |o| b
   hence u IN (SpanSpace r g op b).carrier

   On the other hand, u IN (SpanSpace r g op b).carrier means
         u = t |o| b    for some t IN sticks r (LENGTH b)
           = |0| || (t |o| b)
           = #0 o v || (t |o| b)
           = (#0::t) |o| (v::b)
   hence u IN (SpanSpace r g op (v::b)).carrier
*)
val vspace_span_with_member = store_thm(
  "vspace_span_with_member",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !v. v IN (SpanSpace r g op b).carrier ==> (SpanSpace r g op b = SpanSpace r g op (v::b))``,
  rpt strip_tac >>
  `Group g` by metis_tac[vspace_has_group] >>
  `Field r` by metis_tac[vspace_has_field] >>
  `#0 IN R` by rw[] >>
  rw[SpanSpace_def, monoid_component_equality, EXTENSION, EQ_IMP_THM] >| [
    qexists_tac `#0::n` >>
    `#0::n IN sticks r (SUC (LENGTH b))` by metis_tac[stick_cons] >>
    qabbrev_tac `u = n |o| b` >>
    rw[vsum_cons] >>
    `v IN V /\ u IN V` by metis_tac[vspace_span_vector, vspace_span_property] >>
    `#0 o v = |0|` by metis_tac[vspace_cmult_lzero] >>
    rw[],
    `?k t. k IN R /\ t IN sticks r (LENGTH b) /\ (n = k::t)` by rw[GSYM stick_cons] >>
    `?m. m IN sticks r (LENGTH b) /\ (v = m |o| b)` by rw[vspace_span_property] >>
    rw[vsum_cons] >>
    qabbrev_tac `mv = m |o| b` >>
    qabbrev_tac `tv = t |o| b` >>
    qexists_tac `k * m + t` >>
    metis_tac[vsum_stick_add, vsum_stick_cmult, stick_cmult_length, stick_add_length]
  ]);

(* Theorem: SpanSpace r g op b = SpanSpace r g op ( |0|::b) *)
(* Proof:
   Since |0| IN (SpanSpace r g op b).carrier  by vspace_span_has_zero
   True by vspace_span_with_member.
*)
val vspace_span_with_zero = store_thm(
  "vspace_span_with_zero",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==>
   !b. basis g b ==> (SpanSpace r g op b = SpanSpace r g op ( |0|::b))``,
  rw[vspace_span_has_zero, vspace_span_with_member]);

(* Theorem: h IN (SpanSpace r g op b).carrier /\ v IN (SpanSpace r g op (h::b)).carrier ==>
            v IN (SpanSpace r g op b).carrier *)
(* Proof:
   By SpanSpace_def, stick_cons, vsum_cons, this is to show:
   n IN sticks r (LENGTH b) /\ t IN sticks r (SUC (LENGTH b)) ==>
     ?n'. (h' o (n |o| b) || (t |o| b) = n' |o| b) /\ n' IN sticks r (LENGTH b)
   Let n' = h' * n + t IN sticks r (LENGTH b)  by stick_cmult_length, stick_add_length
       n' |o| b
     = (h' * n + t) |o| b              by n' = h' * n + t
     = ((h' * n) |o| b) || (t |o| b)   by vsum_stick_add
     = h' o (n |o| b) || u             by vsum_stick_cmult
*)
val vspace_span_add_member = store_thm(
  "vspace_span_add_member",
  ``!(r:'a field) (g:'b group) op. VSpace r g op ==> !b. basis g b ==>
   !h v. h IN (SpanSpace r g op b).carrier /\ v IN (SpanSpace r g op (h::b)).carrier ==>
         v IN (SpanSpace r g op b).carrier``,
  rw[SpanSpace_def, stick_cons] >>
  rw[vsum_cons] >>
  qexists_tac `h' * n + t` >>
  `Field r` by metis_tac[vspace_has_field] >>
  metis_tac[vsum_stick_add, vsum_stick_cmult, stick_cmult_length, stick_add_length]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
