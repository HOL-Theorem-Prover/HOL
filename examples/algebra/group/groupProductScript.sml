(* ------------------------------------------------------------------------- *)
(* Group Theory -- Iterated Product.                                         *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "groupProduct";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory arithmeticTheory numberTheory combinatoricsTheory;

(* Get dependent theories local *)
(* val _ = load "groupTheory"; *)
open groupTheory monoidTheory;

open subgroupTheory;

(* ------------------------------------------------------------------------- *)
(* Iterated Product Documentation                                            *)
(* ------------------------------------------------------------------------- *)
(* Overloading (# is temporary):
   FUN_COMM op f  = !x y z. op (f x) (op (f y) z) = op (f y) (op (f x) z)
#  GPI f s        = GROUP_IMAGE g f s
#  gfun f         = group_fun g f
*)
(* Definitions and Theorems (# are exported):

   Fermat's Little Theorem of Abelian Groups:
   GPROD_SET_IMAGE            |- !g a. Group g /\ a IN G ==> (GPROD_SET g (a * G) = GPROD_SET g G)
   GPROD_SET_REDUCTION_INSERT |- !g s. FiniteAbelianGroup g /\ s SUBSET G ==>
                                 !a x::(G). x NOTIN s ==>
                          (a * x * GPROD_SET g (a * (G DIFF (x INSERT s))) = GPROD_SET g (a * (G DIFF s)))
   GPROD_SET_REDUCTION        |- !g s. FiniteAbelianGroup g /\ s SUBSET G ==>
                       !a::(G). a ** CARD s * GPROD_SET g s * GPROD_SET g (a * (G DIFF s)) = GPROD_SET g G

   Group Factorial:
   GFACT_def              |- !g. GFACT g = GPROD_SET g G
   GFACT_element          |- !g. FiniteAbelianMonoid g ==> GFACT g IN G
   GFACT_identity         |- !g a. FiniteAbelianGroup g /\ a IN G ==> (GFACT g = a ** CARD G * GFACT g)
   finite_abelian_Fermat  |- !g a. FiniteAbelianGroup g /\ a IN G ==> (a ** CARD G = #e)

   Group Iterated Product over a function:
   OP_IMAGE_DEF    |- !op id f s. OP_IMAGE op id f s = ITSET (\e acc. op (f e) acc) s id
   OP_IMAGE_EMPTY  |- !op id f. OP_IMAGE op id f {} = id
   OP_IMAGE_SING   |- !op id f x. OP_IMAGE op id f {x} = op (f x) id
   OP_IMAGE_THM    |- !op id f. (OP_IMAGE op id f {} = id) /\
                                (FUN_COMM op f ==> !s. FINITE s ==>
                      !e. OP_IMAGE op id f (e INSERT s) = op (f e) (OP_IMAGE op id f (s DELETE e)))

   GROUP_IMAGE_DEF          |- !g f s. GPI f s = ITSET (\e acc. f e * acc) s #e
   group_image_as_op_image  |- !g. GPI = OP_IMAGE $* #e
   sum_image_as_op_image    |- SIGMA = OP_IMAGE (\x y. x + y) 0
   prod_image_as_op_image   |- PI = OP_IMAGE (\x y. x * y) 1
   GITSET_AS_ITSET          |- !g. (\s b. GITSET g s b) = ITSET (\e acc. e * acc)
   GPROD_SET_AS_GROUP_IMAGE |- !g. GPROD_SET g = GPI I
   group_image_empty        |- !g f. GPI f {} = #e
   group_fun_def            |- !g f. gfun f <=> !x. x IN G ==> f x IN G
   group_image_sing         |- !g. Monoid g ==> !f. gfun f ==> !x. x IN G ==> (GPI f {x} = f x)

*)


(* ------------------------------------------------------------------------- *)
(* Fermat's Little Theorem of Abelian Groups.                                *)
(* ------------------------------------------------------------------------- *)

(* Theorem: For Group g, a IN G ==> GPROD_SET g a * G = GPROD_SET g G *)
(* Proof:
   This is trivial by group_coset_eq_itself.
*)
val GPROD_SET_IMAGE = store_thm(
  "GPROD_SET_IMAGE",
  ``!g a. Group g /\ a IN G ==> (GPROD_SET g (a * G) = GPROD_SET g G)``,
  rw[group_coset_eq_itself]);

(* ------------------------------------------------------------------------- *)
(* An Invariant Property when reducing GPROD_SET g (IMAGE (\z. a*z) G):
     GPROD_SET g (IMAGE (\z. a*z) G)
   = (a*z) * GPROD_SET g ((IMAGE (\z. a*z) G) DELETE (a*z))
   = a * (GPROD_SET g (z INSERT {})) * GPROD_SET g (IMAGE (\z. a*z) (G DELETE z))
   = a * <building up a GPROD_SET> * <reducing down a GPROD_SET>
   = a*a * <building one more> * <reducing one more>
   = a*a*a * <building one more> * <reducing one more>
   = a**(CARD G) * GPROD_SET g G * GPROD_SET g {}
   = a**(CARD G) * GPROD_SET g G * #e
   = a**(CARD G) * GPROD_SET g G
*)
(* ------------------------------------------------------------------------- *)

(* Theorem: [INSERT for GPROD_SET_REDUCTION]
            (a*x)* GPROD_SET g (coset g (G DIFF (x INSERT t)))
            = GPROD_SET g (coset g (G DIFF t)) *)
(* Proof:
   Essentially this is to prove:
   a * x * GPROD_SET g {a * z | z | z IN G /\ z <> x /\ z NOTIN s} =
           GPROD_SET g {a * z | z | z IN G /\ z NOTIN s}
   Let q = {a * z | z | z IN G /\ z <> x /\ z NOTIN s}
       p = {a * z | z | z IN G /\ z NOTIN s}
   Since p = (a*x) INSERT q   by EXTENSION,
     and (a*x) NOTIN q        by group_lcancel, a NOTIN s.
     and (a*x) IN G           by group_op_element
   RHS = GPROD_SET g p
       = GPROD_SET g ((a*x) INSERT q)            by p = (a*x) INSERT q
       = (a*x) * GPROD_SET g (q DELETE (a*x))    by GPROD_SET_THM
       = (a*x) * GPROD_SET g q                   by DELETE_NON_ELEMENT, (a*x) NOTIN q.
       = LHS
*)
val GPROD_SET_REDUCTION_INSERT = store_thm(
  "GPROD_SET_REDUCTION_INSERT",
  ``!g s. FiniteAbelianGroup g /\ s SUBSET G ==>
   !a x::(G). x NOTIN s ==>
   (a * x * GPROD_SET g (a * (G DIFF (x INSERT s))) = GPROD_SET g (a * (G DIFF s)))``,
  rw[coset_def, IMAGE_DEF, EXTENSION, RES_FORALL_THM] >>
  qabbrev_tac `p = {a * z | z | z IN G /\ z NOTIN s}` >>
  qabbrev_tac `q = {a * z | z | z IN G /\ z <> x /\ z NOTIN s}` >>
  (`p = (a * x) INSERT q` by (rw[EXTENSION, EQ_IMP_THM, Abbr`p`, Abbr`q`] >> metis_tac[])) >>
  `AbelianGroup g /\ Group g /\ FINITE G` by metis_tac[FiniteAbelianGroup_def, AbelianGroup_def] >>
  `!z. z IN G /\ (a * z = a * x) <=> (z = x)` by metis_tac[group_lcancel] >>
  (`(a * x) NOTIN q` by (rw[Abbr`q`] >> metis_tac[])) >>
  (`q SUBSET G` by (rw[EXTENSION, SUBSET_DEF, Abbr`q`] >> rw[])) >>
  `a * x IN G` by rw[] >>
  `AbelianMonoid g` by rw[abelian_group_is_abelian_monoid] >>
  `FINITE q` by metis_tac[SUBSET_FINITE] >>
  metis_tac[GPROD_SET_THM, DELETE_NON_ELEMENT]);

(* Theorem: (a ** n) * <building n-steps GPROD_SET> * <reducing n-steps GPROD_SET> = GPROD_SET g G *)
(* Proof:
   By complete induction on CARD s.
   Case s = {},
     LHS = a ** (CARD s) * (GPROD_SET g s) * GPROD_SET g (a * (G DIFF s))
         = a ** 0 * (GPROD_SET g {}) * GPROD_SET g (a * (G DIFF {}))        by CARD_EMPTY
         = #e * #e * GPROD_SET g (a * G)      by group_exp_0, DIFF_EMPTY, GPROD_SET_EMPTY.
         = GPROD_SET g (a * G)                by group_lid
         = GPROD_SET g G                      by GPROD_SET_IMAGE
         = RHS
   Case s <> {},
     Let x = CHOICE s, t = REST s, so s = x INSERT t, x NOTIN t.
     LHS = a ** (CARD s) * (GPROD_SET g s) * GPROD_SET g (a * (G DIFF s))
         = a ** SUC(CARD t) *
           (GPROD_SET g (x INSERT t)) *
           GPROD_SET g (a * (G DIFF (x INSERT t)))   by CARD s = SUC(CARD t), s = x INSERT t.
         = a ** SUC(CARD t) *
           (x * GPROD_SET g (t DELETE x)) *
           GPROD_SET g (a * (G DIFF (x INSERT t)))   by GPROD_SET_THM
         = a ** SUC(CARD t) *
           (x * GPROD_SET g t) *
           GPROD_SET g (a * (G DIFF (x INSERT t)))   by DELETE_NON_ELEMENT, x NOTIN t.
         = a*a ** (CARD t) *
           x * GPROD_SET g t *
           GPROD_SET g (a * (G DIFF (x INSERT t)))   by group_exp_SUC
         = a ** (CARD t) *
           GPROD_SET g t *
           (a * x) * GPROD_SET g (a * (G DIFF (x INSERT t)))  by Abelian group commuting
         = a ** (CARD t) *
           GPROD_SET g t *
           GPROD_SET g (a * (G DIFF t))   by GPROD_SET_REDUCTION_INSERT
         = RHS                            by induction
*)
val GPROD_SET_REDUCTION = store_thm(
  "GPROD_SET_REDUCTION",
  ``!g s. FiniteAbelianGroup g /\ s SUBSET G ==>
   !a::(G). a ** (CARD s) * (GPROD_SET g s) * GPROD_SET g (a * (G DIFF s)) = GPROD_SET g G``,
  completeInduct_on `CARD s` >>
  pop_assum (assume_tac o SIMP_RULE bool_ss[GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO]) >>
  rw[RES_FORALL_THM] >>
  `AbelianGroup g /\ Group g /\ FINITE G` by metis_tac[FiniteAbelianGroup_def, AbelianGroup_def, FiniteGroup_def] >>
  `AbelianMonoid g` by rw[abelian_group_is_abelian_monoid] >>
  Cases_on `s = {}` >| [
    rw[GPROD_SET_EMPTY] >>
    `GPROD_SET g G IN G` by rw[GPROD_SET_PROPERTY] >>
    rw[GPROD_SET_IMAGE],
    `?x t. (x = CHOICE s) /\ (t = REST s) /\ (s = x INSERT t)` by rw[CHOICE_INSERT_REST] >>
    `x IN G` by metis_tac[CHOICE_DEF, SUBSET_DEF] >>
    `t SUBSET G /\ FINITE t` by metis_tac[REST_SUBSET, SUBSET_TRANS, SUBSET_FINITE] >>
    `x NOTIN t` by metis_tac[CHOICE_NOT_IN_REST] >>
    `(CARD s = SUC(CARD t)) /\ CARD t < CARD s` by rw[CARD_INSERT] >>
    `GPROD_SET g t IN G` by rw[GPROD_SET_PROPERTY] >>
    `GPROD_SET g (a * (G DIFF (x INSERT t))) IN G` by metis_tac[coset_property, DIFF_SUBSET, SUBSET_FINITE, GPROD_SET_PROPERTY] >>
    qabbrev_tac `t' = a * (G DIFF (x INSERT t))` >>
    `a ** CARD s * GPROD_SET g s * GPROD_SET g (a * (G DIFF s)) =
    a ** SUC(CARD t) * GPROD_SET g (x INSERT t) * GPROD_SET g t'` by rw[Abbr`t'`] >>
    `_ = a ** SUC(CARD t) * (x * GPROD_SET g (t DELETE x)) * GPROD_SET g t'` by rw[GPROD_SET_THM] >>
    `_ = a ** SUC(CARD t) * (x * GPROD_SET g t) * GPROD_SET g t'` by metis_tac[DELETE_NON_ELEMENT] >>
    `_ = (a * a ** (CARD t)) * (x * GPROD_SET g t) * GPROD_SET g t'` by rw[group_exp_SUC] >>
    `_ = (a ** (CARD t) * a) * (x * GPROD_SET g t) * GPROD_SET g t'` by metis_tac[AbelianGroup_def, group_exp_element] >>
    `_ = a ** (CARD t) * (a * (x * GPROD_SET g t)) * GPROD_SET g t'` by rw[group_assoc] >>
    `_ = a ** (CARD t) * ((a * x) * GPROD_SET g t) * GPROD_SET g t'` by rw[group_assoc] >>
    `_ = a ** (CARD t) * (GPROD_SET g t * (a * x)) * GPROD_SET g t'` by metis_tac[AbelianGroup_def, group_op_element] >>
    `_ = (a ** (CARD t) * GPROD_SET g t) * (a * x) * GPROD_SET g t'` by rw[group_assoc] >>
    `_ = a ** (CARD t) * GPROD_SET g t * ((a * x) * GPROD_SET g t')` by rw[group_assoc] >>
    `_ = a ** (CARD t) * GPROD_SET g t * GPROD_SET g (a * (G DIFF t))` by metis_tac[GPROD_SET_REDUCTION_INSERT] >>
    rw[]
  ]);

(* Define Group Factorial *)
val GFACT_def = Define`
  GFACT g = GPROD_SET g G
`;

(* Theorem: GFACT g is an element in Group g. *)
(* Proof:
   Since G SUBSET G     by SUBSET_REFL
   This is true by GPROD_SET_PROPERTY:
   !g s. FiniteAbelianMonoid g /\ s SUBSET G ==> GPROD_SET g s IN G : thm
*)
val GFACT_element = store_thm(
  "GFACT_element",
  ``!g. FiniteAbelianMonoid g ==> GFACT g IN G``,
  rw_tac std_ss[FiniteAbelianMonoid_def, GFACT_def, GPROD_SET_PROPERTY, SUBSET_REFL]);

(* Theorem: For FiniteAbelian Group g, a IN G ==> GFACT g = a ** (CARD g) * GFACT g *)
(* Proof:
   Since G SUBSET G  by SUBSET_REFL,
   and G DIFF G = {},
   Put s = G in GPROD_SET_REDUCTION:
       a ** (CARD G) * GPROD_SET g G * GPROD_SET g (a * (G DIFF G)) = GPROD_SET g G
   ==> a ** (CARD G) * GPROD_SET g G * GPROD_SET g (a * {}) = GPROD_SET g G
   ==> a ** (CARD G) * GPROD_SET g G * GPROD_SET g {} = GPROD_SET g G  by coset_empty.
   ==> a ** (CARD G) * GPROD_SET g G * #e = GPROD_SET g G              by GPROD_SET_EMPTY.
   ==> a ** (CARD G) * GPROD_SET g G = GPROD_SET g G                   by group_assoc and group_rid
*)
val GFACT_identity = store_thm(
  "GFACT_identity",
  ``!(g:'a group) a. FiniteAbelianGroup g /\ a IN G ==> (GFACT g = a ** (CARD G) * GFACT g)``,
  rw[GFACT_def] >>
  `G SUBSET G` by rw[] >>
  `G DIFF G = {}` by rw[] >>
  `AbelianGroup g /\ Group g /\ FINITE G` by metis_tac[FiniteAbelianGroup_def, AbelianGroup_def, FiniteGroup_def] >>
  `AbelianMonoid g` by rw[abelian_group_is_abelian_monoid] >>
  `GPROD_SET g G IN G` by rw[GPROD_SET_PROPERTY] >>
  `GPROD_SET g G = a ** (CARD G) * GPROD_SET g G * GPROD_SET g (a * (G DIFF G))` by rw[GPROD_SET_REDUCTION] >>
  `_ = a ** (CARD G) * GPROD_SET g G * GPROD_SET g (a * {})` by rw[] >>
  `_ = a ** (CARD G) * GPROD_SET g G * GPROD_SET g {}` by rw[coset_empty] >>
  `_ = a ** (CARD G) * GPROD_SET g G * #e` by metis_tac[GPROD_SET_EMPTY] >>
  `_ = a ** (CARD G) * GPROD_SET g G` by rw[] >>
  rw[]);

(* Theorem: For FiniteAbelian Group g, a IN G ==> a ** (CARD g) = #e *)
(* Proof:
   Since  a ** (CARD G) * GFACT g = GFACT g    by GFACT_identity
   Hence  a ** (CARD G) = #e                   by group_lid_unique
*)
val finite_abelian_Fermat = store_thm(
  "finite_abelian_Fermat",
  ``!(g:'a group) a. FiniteAbelianGroup g /\ a IN G ==> (a ** (CARD G) = #e)``,
  rpt strip_tac >>
  `AbelianGroup g /\ Group g /\ FINITE G` by metis_tac[FiniteAbelianGroup_def, AbelianGroup_def, FiniteGroup_def] >>
  `AbelianMonoid g` by rw[abelian_group_is_abelian_monoid] >>
  `GFACT g IN G` by rw[GFACT_element] >>
  `a ** (CARD G) * GFACT g = GFACT g` by rw[GFACT_identity] >>
  metis_tac[group_exp_element, group_lid_unique]);


(* ------------------------------------------------------------------------- *)
(* Group Iterated Product over a function.                                   *)
(* ------------------------------------------------------------------------- *)

(*
> show_types := true; ITSET_def; show_types := false;
val it = |- !(s :'a -> bool) (f :'a -> 'b -> 'b) (b :'b).
    ITSET f s b = if FINITE s then if s = ({} :'a -> bool) then b
                                   else ITSET f (REST s) (f (CHOICE s) b)
                  else (ARB :'b): thm

> show_types := true; SUM_IMAGE_DEF; show_types := false;
val it = |- !(f :'a -> num) (s :'a -> bool).
    SIGMA f s = ITSET (\(e :'a) (acc :num). f e + acc) s (0 :num): thm

> ITSET_def |> ISPEC ``s:'b -> bool`` |> ISPEC ``(f:'b -> 'a)`` |> ISPEC ``b:'a``;
val it = |- GITSET g s b = if FINITE s then if s = {} then b else GITSET g (REST s) (CHOICE s * b)
                           else ARB: thm
*)

(* A general iterator for operation (op:'a -> 'a -> 'a) and (id:'a) *)
val OP_IMAGE_DEF = Define `
    OP_IMAGE (op:'a -> 'a -> 'a) (id:'a) (f:'b -> 'a) (s:'b -> bool) = ITSET (\e acc. op (f e) acc) s id
`;

(* Theorem: OP_IMAGE op id f {} = id *)
(* Proof:
     OP_IMAGE op id f {}
   = ITSET (\e acc. op (f e) acc) {} id    by OP_IMAGE_DEF
   = id                                    by ITSET_EMPTY
*)
val OP_IMAGE_EMPTY = store_thm(
  "OP_IMAGE_EMPTY",
  ``!op id f. OP_IMAGE op id f {} = id``,
  rw[OP_IMAGE_DEF, ITSET_EMPTY]);

(* Theorem: OP_IMAGE op id f {x} = op (f x) id *)
(* Proof:
     OP_IMAGE op id f {x}
   = ITSET (\e acc. op (f e) acc) {x} id    by OP_IMAGE_DEF
   = (\e acc. op (f e) acc) x id            by ITSET_SING
   = op (f x) id                            by application
*)
val OP_IMAGE_SING = store_thm(
  "OP_IMAGE_SING",
  ``!op id f x. OP_IMAGE op id f {x} = op (f x) id``,
  rw[OP_IMAGE_DEF, ITSET_SING]);

(*
Now the hard part: show (\e acc. op (f e) acc) is an accumulative function for ITSET.

val SUM_IMAGE_THM = store_thm(
  "SUM_IMAGE_THM",
  ``!f. (SUM_IMAGE f {} = 0) /\
        (!e s. FINITE s ==>
               (SUM_IMAGE f (e INSERT s) =
                f e + SUM_IMAGE f (s DELETE e)))``,
  REPEAT STRIP_TAC THENL [
    SIMP_TAC (srw_ss()) [ITSET_THM, SUM_IMAGE_DEF],
    SIMP_TAC (srw_ss()) [SUM_IMAGE_DEF] THEN
    Q.ABBREV_TAC `g = \e acc. f e + acc` THEN
    Q_TAC SUFF_TAC `ITSET g (e INSERT s) 0 =
                    g e (ITSET g (s DELETE e) 0)` THEN1
       SRW_TAC [][Abbr`g`] THEN
    MATCH_MP_TAC COMMUTING_ITSET_RECURSES THEN
    SRW_TAC [ARITH_ss][Abbr`g`]
  ]);

val PROD_IMAGE_THM = store_thm(
  "PROD_IMAGE_THM",
  ``!f. (PROD_IMAGE f {} = 1) /\
        (!e s. FINITE s ==>
          (PROD_IMAGE f (e INSERT s) = f e * PROD_IMAGE f (s DELETE e)))``,
  REPEAT STRIP_TAC THEN1
    SIMP_TAC (srw_ss()) [ITSET_THM, PROD_IMAGE_DEF] THEN
  SIMP_TAC (srw_ss()) [PROD_IMAGE_DEF] THEN
  Q.ABBREV_TAC `g = \e acc. f e * acc` THEN
  Q_TAC SUFF_TAC `ITSET g (e INSERT s) 1 =
                  g e (ITSET g (s DELETE e) 1)` THEN1 SRW_TAC [][Abbr`g`] THEN
  MATCH_MP_TAC COMMUTING_ITSET_RECURSES THEN
  SRW_TAC [ARITH_ss][Abbr`g`]);

*)

(* Overload a communtative operation *)
val _ = overload_on("FUN_COMM", ``\op f. !x y z. op (f x) (op (f y) z) = op (f y) (op (f x) z)``);

(* Theorem: (OP_IMAGE op id f {} = id)  /\
            (FUN_COMM op f ==> !s. FINITE s ==>
             !e. OP_IMAGE op id f (e INSERT s) = op (f e) (OP_IMAGE op id f (s DELETE e))) *)
(* Proof:
   First goal: P_IMAGE op id f {} = id
      True by OP_IMAGE_EMPTY.
   Second goal: OP_IMAGE op id f (e INSERT s) = op (f e) (OP_IMAGE op id f (s DELETE e)))
      Let g = \e acc. op (f e) acc,
      Then by OP_IMAGE_DEF, the goal is:
      to show: ITSET g (e INSERT s) id = op (f e) (ITSET g (s DELETE e) id)
      or show: ITSET g (e INSERT s) id = g e (ITSET g (s DELETE e) id)
      Given FUN_COMM op f, the is true by COMMUTING_ITSET_RECURSES.
*)
val OP_IMAGE_THM = store_thm(
  "OP_IMAGE_THM",
  ``!op id f. (OP_IMAGE op id f {} = id)  /\
   (FUN_COMM op f ==> !s. FINITE s ==>
    !e. OP_IMAGE op id f (e INSERT s) = op (f e) (OP_IMAGE op id f (s DELETE e)))``,
  rpt strip_tac >-
  rw[OP_IMAGE_EMPTY] >>
  rw[OP_IMAGE_DEF] >>
  qabbrev_tac `g = \e acc. op (f e) acc` >>
  rw[] >>
  rw[COMMUTING_ITSET_RECURSES, Abbr`g`]);

(* A better iterator for group operation over (f:'b -> 'a) *)
val GROUP_IMAGE_DEF = Define `
    GROUP_IMAGE (g:'a group) (f:'b -> 'a) (s:'b -> bool) = ITSET (\e acc. (f e) * acc) s #e
`;

(* overload GROUP_IMAGE *)
val _ = temp_overload_on("GPI", ``GROUP_IMAGE g``);

(*
> GROUP_IMAGE_DEF;
val it = |- !g f s. GPI f s = ITSET (\e acc. f e * acc) s #e: thm
*)

(* Theorem: GPI = OP_IMAGE (g.op) (g.id) *)
(* Proof: by GROUP_IMAGE_DEF, OP_IMAGE_DEF, FUN_EQ_THM *)
val group_image_as_op_image = store_thm(
  "group_image_as_op_image",
  ``!g:'a group. GPI = OP_IMAGE (g.op) (g.id)``,
  rw[GROUP_IMAGE_DEF, OP_IMAGE_DEF, FUN_EQ_THM]);

(* Theorem: SUM_IMAGE = OP_IMAGE (\(x y):num. x + y) 0 *)
(* Proof: by SUM_IMAGE_DEF, OP_IMAGE_DEF, FUN_EQ_THM *)
val sum_image_as_op_image = store_thm(
  "sum_image_as_op_image",
  ``SIGMA = OP_IMAGE (\(x y):num. x + y) 0``,
  rw[SUM_IMAGE_DEF, OP_IMAGE_DEF, FUN_EQ_THM]);

(* Theorem: PROD_IMAGE = OP_IMAGE (\(x y):num. x * y) 1 *)
(* Proof: by PROD_IMAGE_DEF, OP_IMAGE_DEF, FUN_EQ_THM *)
val prod_image_as_op_image = store_thm(
  "prod_image_as_op_image",
  ``PI = OP_IMAGE (\(x y):num. x * y) 1``,
  rw[PROD_IMAGE_DEF, OP_IMAGE_DEF, FUN_EQ_THM]);

(*
val _ = clear_overloads_on("GITSET");
val _ = clear_overloads_on("GPI");
val _ = overload_on("GITSET", ``\g s b. ITSET g.op s b``);
val _ = overload_on("GPI", ``GROUP_IMAGE g``);
*)

(* val _ = overload_on("GITSET", ``\g s b. ITSET g.op s b``); *)

(* Theorem: GITSET g = ITSET (\e acc. g.op e acc) *)
(* Proof:
   Note g.op = (\e acc. e * acc)   by FUN_EQ_THM

     GITSET g s b
   = ITSET g.op s b                by notation
   = ITSET (\e acc. e * acc) s b   by ITSET_CONG

   Hence GITSET g = ITSET (\e acc. g.op e acc)  by FUN_EQ_THM
*)
val GITSET_AS_ITSET = store_thm(
  "GITSET_AS_ITSET",
  ``!g:'a group. GITSET g = ITSET (\e acc. g.op e acc)``,
  rw[FUN_EQ_THM] >>
  `g.op = (\e acc. e * acc)` by rw[FUN_EQ_THM] >>
  `ITSET g.op = ITSET (\e acc. e * acc)` by rw[ITSET_CONG] >>
  rw[]);

(*
> ITSET_def |> ISPEC ``s:'b -> bool`` |> ISPEC ``(g:'a group).op`` |> ISPEC ``b:'a``;
val it = |- GITSET g s b = if FINITE s then if s = {} then b else GITSET g (REST s) (CHOICE s * b)
                           else ARB: thm
*)

(* Theorem: GPROD_SET g = GPI I *)
(* Proof:
   Note g.op = (\e acc. e * acc)    by FUN_EQ_THM

     GPROD_SET g x
   = GITSET g x #e                  by GPROD_SET_def
   = ITSET g.op x #e                by notation
   = ITSET (\e acc. e * acc) x #e   by above
   = GPI I x                        by GROUP_IMAGE_DEF
   Hence GPROD_SET g = GPI I        by FUN_EQ_THM
*)
val GPROD_SET_AS_GROUP_IMAGE = store_thm(
  "GPROD_SET_AS_GROUP_IMAGE",
  ``!g:'a group. GPROD_SET g = GPI I``,
  rw[FUN_EQ_THM] >>
  `g.op = (\e acc. e * acc)` by rw[FUN_EQ_THM] >>
  `ITSET g.op = ITSET (\e acc. e * acc)` by rw[ITSET_CONG] >>
  `GPROD_SET g x = GITSET g x #e` by rw[GPROD_SET_def] >>
  `_ = ITSET (\e acc. e * acc) x #e` by rw[] >>
  `_ = GPI I x` by rw[GROUP_IMAGE_DEF] >>
  rw[]);

(* Theorem: GPI f {} = #e *)
(* Proof
     GPI f {}
   = GROUP_IMAGE g f {}               by notation
   = ITSET (\e acc. f e * acc) {} #e  by GROUP_IMAGE_DEF
   = #e                               by ITSET_EMPTY
*)
val group_image_empty = store_thm(
  "group_image_empty",
  ``!g:'a group. !f. GPI f {} = #e``,
  rw[GROUP_IMAGE_DEF, ITSET_EMPTY]);

(* Define a group function *)
val group_fun_def = Define `
    group_fun (g:'a group) f = !x. x IN G ==> f x IN G
`;

(* overload on group function *)
val _ = temp_overload_on("gfun", ``group_fun g``);

(* Theorem: Monoid g ==> !f. gfun f ==> !x. x IN G ==> (GPI f {x} = f x) *)
(* Proof:
   Note x IN G ==> f x IN G            by group_fun_def
     GPI f {x}
   = GROUP_IMAGE g f {x}               by notation
   = ITSET (\e acc. f e * acc) {x} #e  by GROUP_IMAGE_DEF
   = f x * #e                          by ITSET_SING
   = f x                               by monoid_rid
*)
val group_image_sing = store_thm(
  "group_image_sing",
  ``!g:'a group. Monoid g ==> !f. gfun f ==> !x. x IN G ==> (GPI f {x} = f x)``,
  rw[GROUP_IMAGE_DEF, group_fun_def, ITSET_SING]);


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
