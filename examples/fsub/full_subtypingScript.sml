(* standard prelude *)
open HolKernel boolLib Parse


(* extra theorem-proving oomph from libraries *)
open bossLib metisLib ncLib BasicProvers boolSimps



(* ancestor theories *)
open fsubtypesTheory pred_setTheory
     sortingTheory (* for theorems about permutations *)

val _ = new_theory "full_subtyping"

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 425),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "|-", BreakSpace(1, 0),
                                 BeginFinalBlock(PP.INCONSISTENT, 2),
                                 TM, HardSpace 1, TOK "<:", BreakSpace(1,0)],
                  term_name = "fsubtyping"}

(* define subtyping rules : figure 26-2 *)
val (fsubtyping_rules, fsubtyping_ind, fsubtyping_cases) = Hol_reln`
  (!Gamma ty. wfctxt Gamma /\ ftyFV ty SUBSET cdom Gamma ==>
              Gamma |- ty <: ty) /\
  (!Gamma ty1 ty2 ty3. Gamma |- ty1 <: ty2 /\
                       Gamma |- ty2 <: ty3 ==>
                       Gamma |- ty1 <: ty3) /\
  (!Gamma ty. wfctxt Gamma /\ ftyFV ty SUBSET cdom Gamma ==>
              Gamma |- ty <: Top) /\
  (!Gamma x ty. wfctxt Gamma /\ MEM (x, ty) Gamma ==>
                Gamma |- TyVar x <: ty) /\
  (!Gamma s1 t1 s2 t2.
          Gamma |- t1 <: s1 /\ Gamma |- s2 <: t2 ==>
          Gamma |- Fun s1 s2 <: Fun t1 t2) /\
  (!Gamma x s1 t1 s2 t2.
          ~(x IN ftyFV t1) /\ ~(x IN cdom Gamma) /\
          ftyFV t1 SUBSET cdom Gamma /\
          Gamma |- t1 <: s1 /\
          ((x,t1) :: Gamma) |- s2 <: t2 ==>
          Gamma |- ForallTy x s1 s2 <: ForallTy x t1 t2)
`;

val fsubtyping_swap = store_thm(
  "fsubtyping_swap",
  ``!G t1 t2. G |- t1 <: t2 ==>
              !x y. ctxtswap x y G |- fswap x y t1 <: fswap x y t2``,
  HO_MATCH_MP_TAC fsubtyping_ind THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [][SUBSET_DEF, fsubtyping_rules],
    METIS_TAC [fsubtyping_rules],
    SRW_TAC [][SUBSET_DEF, fsubtyping_rules],
    SRW_TAC [][fsubtyping_rules],
    SRW_TAC [][fsubtyping_rules],
    SRW_TAC [][SUBSET_DEF, fsubtyping_rules]
  ]);

val fsubtyping_wfctxt = store_thm(
  "fsubtyping_wfctxt",
  ``!G t1 t2. G |- t1 <: t2 ==> wfctxt G``,
  HO_MATCH_MP_TAC fsubtyping_ind THEN SRW_TAC [][]);

(* define algorithmic sub-typing, with a depth of derivation parameter *)
val (algn_subtyping_rules, algn_subtyping_ind, algn_subtyping_cases) =
  Hol_reln`
    (!Gamma s. wfctxt Gamma /\ ftyFV s SUBSET cdom Gamma ==>
               algn_subtyping 0 Gamma s Top) /\
    (!Gamma x. wfctxt Gamma /\ x IN cdom Gamma ==>
               algn_subtyping 0 Gamma (TyVar x) (TyVar x)) /\
    (!Gamma x u t n. MEM (x, u) Gamma /\ algn_subtyping n Gamma u t ==>
                     algn_subtyping (n + 1) Gamma (TyVar x) t) /\
    (!Gamma t1 s1 t2 s2 n m.
                 algn_subtyping n Gamma t1 s1 /\
                 algn_subtyping m Gamma s2 t2 ==>
                 algn_subtyping (MAX n m + 1) Gamma (Fun s1 s2) (Fun t1 t2)) /\
    (!Gamma x s1 s2 t1 t2 n.
                 ~(x IN ftyFV t1) /\ ~(x IN cdom Gamma) /\
                 ftyFV t1 SUBSET cdom Gamma /\
                 algn_subtyping n ((x,t1)::Gamma) s2 t2 ==>
                 algn_subtyping (n + 1) Gamma (ForallTy x s1 s2)
                                              (ForallTy x t1 t2))
`;

val algn_subtyping_swap = store_thm(
  "algn_subtyping_swap",
  ``!n G t1 t2. algn_subtyping n G t1 t2 ==>
                !x y. algn_subtyping n (ctxtswap x y G)
                                       (fswap x y t1) (fswap x y t2)``,
  HO_MATCH_MP_TAC algn_subtyping_ind THEN
  SRW_TAC [][algn_subtyping_rules, SUBSET_DEF] THEN
  (* only sa-trans-tvar case remains *)
  MATCH_MP_TAC (List.nth(CONJUNCTS algn_subtyping_rules, 2)) THEN
  Q.EXISTS_TAC `fswap x' y t1` THEN SRW_TAC [][]);

val algn_subtyping_swap1_eqn = store_thm(
  "algn_subtyping_swap1_eqn",
  ``!n G t1 t2 x y. algn_subtyping n G (fswap x y t1) t2 =
                    algn_subtyping n (ctxtswap x y G) t1 (fswap x y t2)``,
  METIS_TAC [algn_subtyping_swap, ctxtswap_inv, fswap_inv]);

val algn_subtyping_wfctxt = store_thm(
  "algn_subtyping_wfctxt",
  ``!n G t1 t2. algn_subtyping n G t1 t2 ==> wfctxt G``,
  HO_MATCH_MP_TAC algn_subtyping_ind THEN SRW_TAC [][]);

val cdom_APPEND = store_thm(
  "cdom_APPEND",
  ``cdom (X ++ Y) = cdom X UNION cdom Y``,
  SRW_TAC [DNF_ss][cdom_MEM, EXTENSION]);
val _ = export_rewrites ["cdom_APPEND"]

val wfctxt_APPEND = store_thm(
  "wfctxt_APPEND",
  ``!X Y. DISJOINT (cdom X) (cdom Y) /\ wfctxt X /\ wfctxt Y ==>
          wfctxt (X ++ Y)``,
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, SUBSET_DEF]);

val ctxtswap_APPEND = store_thm(
  "ctxtswap_APPEND",
  ``!X Y. ctxtswap x y (X ++ Y) = ctxtswap x y X ++ ctxtswap x y Y``,
  Induct THEN SRW_TAC [][]);
val _ = export_rewrites ["ctxtswap_APPEND"]

val cdom_PERM = store_thm(
  "cdom_PERM",
  ``!G1 G2. PERM G1 G2 ==> (cdom G1 = cdom G2)``,
  HO_MATCH_MP_TAC PERM_IND THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, INSERT_COMM]);

(* lemma 28.4.1.1 *)
val algn_subtyping_permutation = store_thm(
  "algn_subtyping_permutation",
  ``!n G t1 t2. algn_subtyping n G t1 t2 ==>
                !D. PERM D G /\ wfctxt D ==>
                    algn_subtyping n D t1 t2``,
  HO_MATCH_MP_TAC algn_subtyping_ind THEN REPEAT CONJ_TAC THENL [
    METIS_TAC [algn_subtyping_rules, cdom_PERM],
    METIS_TAC [algn_subtyping_rules, cdom_PERM],
    METIS_TAC [algn_subtyping_rules, PERM_MEM_EQ],
    METIS_TAC [algn_subtyping_rules],
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (last (CONJUNCTS algn_subtyping_rules)) THEN
    `~(x IN cdom D) /\ ftyFV t1' SUBSET cdom D`
        by METIS_TAC [cdom_PERM] THEN ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][]
  ]);

val strong_algn_subtyping_ind =
    IndDefRules.derive_strong_induction (CONJUNCTS algn_subtyping_rules,
                                         algn_subtyping_ind)

(* lemma 28.4.1.2 *)
val algn_subtyping_weakening = store_thm(
  "algn_subtyping_weakening",
  ``!n G t1 t2. algn_subtyping n G t1 t2 ==>
                !D. DISJOINT (cdom D) (cdom G) /\ wfctxt D ==>
                    algn_subtyping n (D ++ G) t1 t2``,
  HO_MATCH_MP_TAC strong_algn_subtyping_ind THEN REPEAT CONJ_TAC THENL[
    SRW_TAC [][SUBSET_DEF, wfctxt_APPEND, algn_subtyping_rules],
    SRW_TAC [][SUBSET_DEF, wfctxt_APPEND, algn_subtyping_rules],
    METIS_TAC [listTheory.MEM_APPEND, algn_subtyping_rules],
    SRW_TAC [][algn_subtyping_rules],

    (* SA-ALL case *)
    Q_TAC SUFF_TAC
          `!G x s1 s2 t1 t2 n.
              ~(x IN ftyFV t1) /\ ~(x IN cdom G) /\
              (!v. v IN ftyFV t1 ==> v IN cdom G) /\
              algn_subtyping n ((x,t1)::G) s2 t2 /\
              (!D. DISJOINT (cdom D) (cdom ((x,t1)::G)) /\ wfctxt D ==>
                   algn_subtyping n (D ++ (x,t1)::G) s2 t2) ==>
              !D. DISJOINT (cdom D) (cdom G) /\ wfctxt D ==>
                  algn_subtyping (n + 1) (D ++ G)
                                 (ForallTy x s1 s2)
                                 (ForallTy x t1 t2)` THEN1
          SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
    REPEAT STRIP_TAC THEN
    (* generate fresh z *)
    Q_TAC (NEW_TAC "z") `ftyFV t1 UNION cdom G UNION cdom D UNION ftyFV s2
                         UNION ftyFV t2 UNION {x}` THEN

    (* state that types have alpha equivalent forms involving z *)
    `(ForallTy x s1 s2 = ForallTy z s1 (fswap z x s2)) /\
     (ForallTy x t1 t2 = ForallTy z t1 (fswap z x t2))`
        by SRW_TAC [][ForallTy_ALPHA] THEN

    (* by SA-ALL rule if suffices to show (various side conditions drop
       out because z is fresh) ... *)
    Q_TAC SUFF_TAC
          `algn_subtyping n ((z,t1)::(D ++ G)) (fswap z x s2) (fswap z x t2)`
          THEN1 SRW_TAC [][algn_subtyping_rules, SUBSET_DEF] THEN

    `wfctxt G` by METIS_TAC [algn_subtyping_wfctxt, wfctxt_def] THEN

    (* move swaps out, over (z,t1), the z turns into x; the t1 is unchanged
       because z and x are both fresh wrt it, similarly G *)
    Q_TAC SUFF_TAC
          `algn_subtyping n ((x,t1)::ctxtswap z x D ++ G) s2 t2`
          THEN1 SRW_TAC [][algn_subtyping_swap1_eqn, fswap_fresh,
                           ctxtswap_fresh, wfctxt_ctxtFV_cdom] THEN

    (* set up appeal to permutation result *)
    `PERM ((x,t1)::ctxtswap z x D ++ G) (ctxtswap z x D ++ (x,t1)::G)`
       by (SRW_TAC [][PERM_CONS_EQ_APPEND] THEN
           METIS_TAC [PERM_REFL]) THEN

    (* the permuted context is well-formed too: *)
    `DISJOINT (cdom (ctxtswap z x D)) (cdom G)`
       by (FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, EXTENSION] THEN
           METIS_TAC [swapTheory.swapstr_def]) THEN
    `wfctxt ((x,t1) :: ctxtswap z x D ++ G)`
       by SRW_TAC [][SUBSET_DEF, wfctxt_APPEND] THEN

    (* apply permutation result *)
    Q_TAC SUFF_TAC
          `algn_subtyping n (ctxtswap z x D ++ (x,t1)::G) s2 t2`
          THEN1 METIS_TAC [algn_subtyping_permutation] THEN

    (* apply IH ; wfctxt (ctxtswap z x D) drops out *)
    Q_TAC SUFF_TAC
          `DISJOINT (cdom (ctxtswap z x D)) (cdom ((x,t1)::G))`
          THEN1 SRW_TAC [][] THEN

    (* follows easily *)
    FULL_SIMP_TAC (srw_ss()) [DISJOINT_DEF, EXTENSION] THEN
    METIS_TAC [swapTheory.swapstr_def]
  ]);

val _ = export_theory()

