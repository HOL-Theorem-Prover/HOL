(* standard prelude *)
open HolKernel boolLib Parse


(* extra theorem-proving oomph from libraries *)
open bossLib metisLib ncLib BasicProvers boolSimps



(* ancestor theories *)
open fsubtypesTheory pred_setTheory

val _ = new_theory "kernel_subtyping"



(* set up syntax for subtyping judgements *)
val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 425),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "|-", BreakSpace(1, 0),
                                 BeginFinalBlock(PP.INCONSISTENT, 2),
                                 TM, HardSpace 1, TOK "<:", BreakSpace(1,0)],
                  term_name = "fsubtyping"}

(* define subtyping rules *)
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
  (!Gamma x u1 s2 t2.
          ((x,u1) :: Gamma) |- s2 <: t2 ==>
          Gamma |- ForallTy x u1 s2 <: ForallTy x u1 t2)
`;

(* prove that sub-typing relation "respects" permutation *)
val fsubtyping_swap = store_thm(
  "fsubtyping_swap",
  ``!Gamma ty1 ty2.
        Gamma |- ty1 <: ty2 ==>
        ctxtswap x y Gamma |- fswap x y ty1 <: fswap x y ty2``,
  HO_MATCH_MP_TAC fsubtyping_ind THEN
  REPEAT CONJ_TAC THENL [
    (* refl *)  SRW_TAC [][SUBSET_DEF, fsubtyping_rules],
    (* trans *) METIS_TAC [fsubtyping_rules],
    (* top *)   SRW_TAC [][fsubtyping_rules, SUBSET_DEF],
    (* tvar *)  SRW_TAC [][fsubtyping_rules],
    (* fun *)   SRW_TAC [][fsubtyping_rules],
    (* forall *)SRW_TAC [][fsubtyping_rules, SUBSET_DEF]
  ]);

val fsubtyping_wfctxt = store_thm(
  "fsubtyping_wfctxt",
  ``!G ty1 ty2. G |- ty1 <: ty2 ==> wfctxt G``,
  HO_MATCH_MP_TAC fsubtyping_ind THEN SRW_TAC [][]);

val strong_fsubtyping_ind =
    IndDefRules.derive_strong_induction (CONJUNCTS fsubtyping_rules,
                                         fsubtyping_ind)

val fsubtyping_fv_constraint = store_thm(
  "fsubtyping_fv_constraint",
  ``!G ty1 ty2. G |- ty1 <: ty2 ==>
                ftyFV ty1 SUBSET cdom G /\
                ftyFV ty2 SUBSET cdom G``,
  HO_MATCH_MP_TAC strong_fsubtyping_ind THEN
  SRW_TAC [][SUBSET_DEF] THEN
  TRY (IMP_RES_TAC fsubtyping_wfctxt) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [wfctxt_MEM, SUBSET_DEF]);

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
    (!Gamma x u1 s2 t2 n.
                 algn_subtyping n ((x,u1)::Gamma) s2 t2 ==>
                 algn_subtyping (n + 1) Gamma (ForallTy x u1 s2)
                                              (ForallTy x u1 t2))
`;

(* algorithmic sub-typing also respects permutation *)
val algn_subtyping_fswap = store_thm(
  "algn_subtyping_fswap",
  ``!n G ty1 ty2. algn_subtyping n G ty1 ty2 ==>
                  !x y. algn_subtyping n (ctxtswap x y G)
                                         (fswap x y ty1)
                                         (fswap x y ty2)``,
  HO_MATCH_MP_TAC algn_subtyping_ind THEN REPEAT CONJ_TAC THEN
  SRW_TAC [][algn_subtyping_rules] THEN
  METIS_TAC [algn_subtyping_rules, MEM_ctxtswap, fswap_inv,
             swapTheory.swapstr_inverse]);

(* this equivalence applies more often than the one above; it removes
   any permutations that might have appeared on the first argument *)
val algn_subtyping_fswap1_eq = store_thm(
  "algn_subtyping_fswap1_eq",
  ``algn_subtyping n G (fswap x y ty1) ty2 =
    algn_subtyping n (ctxtswap x y G) ty1 (fswap x y ty2)``,
  METIS_TAC [algn_subtyping_fswap, fswap_inv, ctxtswap_inv]);

val algn_subtyping_wfctxt = store_thm(
  "algn_subtyping_wfctxt",
  ``!n G ty1 ty2. algn_subtyping n G ty1 ty2 ==> wfctxt G``,
  HO_MATCH_MP_TAC algn_subtyping_ind THEN SRW_TAC [][]);


(* set up syntax for algorithmic sub-typing relation without the depth
   parameter *)
val _ = remove_rules_for_term "dSUB"

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 425),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "|->", BreakSpace(1, 0),
                                 BeginFinalBlock(PP.INCONSISTENT, 2),
                                 TM, HardSpace 1, TOK "<:", BreakSpace(1,0)],
                  term_name = "alg_subtyping"}

val alg_subtyping_def = Define`
  Gamma |-> s <: t = ?n. algn_subtyping n Gamma s t
`;

val alg_subtyping_fswap1_eq = store_thm(
  "alg_subtyping_fswap1_eq",
  ``Gamma |-> fswap x y ty1 <: ty2 =
    ctxtswap x y Gamma |-> ty1 <: fswap x y ty2``,
  METIS_TAC [alg_subtyping_def, algn_subtyping_fswap1_eq]);

fun derive_rule th0 = let
  val (vs, base) = strip_forall (concl th0)
  val th = UNDISCH_ALL (SPEC_ALL th0)
  val (f, args) = strip_comb (concl th)
  val n = mk_var("n", numSyntax.num)
  val pattern = mk_exists(n, list_mk_comb(f, n::tl args))
  val witness = hd args
  val ex_thm = EXISTS (pattern, witness) th
  val discharged =
      GENL vs (DISCH_ALL (REWRITE_RULE [GSYM alg_subtyping_def] ex_thm))
  val exs_in = SIMP_RULE bool_ss [LEFT_FORALL_IMP_THM,
                                  LEFT_EXISTS_AND_THM,
                                  RIGHT_EXISTS_AND_THM] discharged
in
  REWRITE_RULE [GSYM alg_subtyping_def] exs_in
end

val alg_subtyping_rules = save_thm(
  "alg_subtyping_rules",
  LIST_CONJ (map derive_rule (CONJUNCTS algn_subtyping_rules)));

(* derive the rule induction principle for algorithmic sub-typing *)
val alg_subtyping_ind =
    (Q.GEN `P` o
     SIMP_RULE (srw_ss()) [GSYM alg_subtyping_def] o
     CONV_RULE (RAND_CONV
                  (SWAP_VARS_CONV THENC
                   BINDER_CONV (SWAP_VARS_CONV THENC
                                BINDER_CONV (SWAP_VARS_CONV THENC
                                             BINDER_CONV FORALL_IMP_CONV)))) o
     SIMP_RULE (srw_ss()) [] o
     Q.SPEC `\n G ty1 ty2. P G ty1 ty2`) algn_subtyping_ind

(* likewise for the "cases" or inversion theorem *)
val alg_subtyping_cases =
    (REWRITE_CONV [alg_subtyping_def] THENC
     ONCE_REWRITE_CONV [algn_subtyping_cases] THENC
     SIMP_CONV (srw_ss()) [EXISTS_OR_THM] THENC
     SIMP_CONV (srw_ss())
               (map (INST_TYPE [alpha |-> numSyntax.num])
                    [LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM]) THENC
     REWRITE_CONV [GSYM alg_subtyping_def])
      ``Gamma |-> ty1 <: ty2``

val alg_subtyping_refl (* lemma 28.3.1 *) = store_thm(
  "alg_subtyping_refl",
  ``!ty G. wfctxt G /\ ftyFV ty SUBSET cdom G ==> G |-> ty <: ty``,
  HO_MATCH_MP_TAC fsubty_ind THEN
  SRW_TAC [][alg_subtyping_rules] THEN
  Q_TAC (NEW_TAC "z") `cdom G UNION ftyFV ty UNION ftyFV ty'` THEN
  `ForallTy v ty ty' = ForallTy z ty (fswap z v ty')`
    by SRW_TAC [][ForallTy_ALPHA] THEN
  SRW_TAC [][] THEN
  MATCH_MP_TAC (last (CONJUNCTS alg_subtyping_rules)) THEN
  SRW_TAC [][alg_subtyping_fswap1_eq] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
  METIS_TAC [swapTheory.swapstr_def]);
val _ = export_rewrites ["alg_subtyping_refl"]

val alg_subtyping_top_left = store_thm(
  "alg_subtyping_top_left",
  ``!Gamma t. wfctxt Gamma ==> (Gamma |-> Top <: t = (t = Top))``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM, alg_subtyping_rules] THEN
  ONCE_REWRITE_TAC [alg_subtyping_cases] THEN
  SRW_TAC [][]);
val _ = export_rewrites ["alg_subtyping_top_left"]

val alg_subtyping_tyvar_right0 = prove(
  ``!Gamma ty1 ty2. Gamma |-> ty1 <: ty2 ==>
                    !x. (ty2 = TyVar x) ==>
                        ?y. ty1 = TyVar y``,
  HO_MATCH_MP_TAC alg_subtyping_ind THEN SRW_TAC [][]);
val alg_subtyping_tyvar_right = save_thm(
  "alg_subtyping_tyvar_right",
  SIMP_RULE (bool_ss ++ DNF_ss) [] alg_subtyping_tyvar_right0)

val strong_algn_subtyping_ind =
    IndDefRules.derive_strong_induction (CONJUNCTS algn_subtyping_rules,
                                         algn_subtyping_ind)

val algn_subtyping_ftyFVs_in_ctxt = store_thm(
  "algn_subtyping_ftyFVs_in_ctxt",
  ``!n G ty1 ty2. algn_subtyping n G ty1 ty2 ==>
                  ftyFV ty1 SUBSET cdom G /\ ftyFV ty2 SUBSET cdom G``,
  HO_MATCH_MP_TAC strong_algn_subtyping_ind THEN
  SRW_TAC [][SUBSET_DEF] THEN
  TRY (IMP_RES_TAC algn_subtyping_wfctxt) THEN
  FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN METIS_TAC [cdom_MEM])

val algn_subtyping_swap = store_thm(
  "algn_subtyping_swap",
  ``!n G ty1 ty2.
     algn_subtyping n G ty1 ty2 ==>
     !x y. algn_subtyping n (ctxtswap x y G) (fswap x y ty1) (fswap x y ty2)``,
  HO_MATCH_MP_TAC algn_subtyping_ind THEN
  SRW_TAC [][algn_subtyping_rules] THEN
  MATCH_MP_TAC (List.nth(CONJUNCTS algn_subtyping_rules, 2)) THEN
  Q.EXISTS_TAC `fswap x' y ty1` THEN SRW_TAC [][]);
val algn_subtyping_swap1_eqn = store_thm(
  "algn_subtyping_swap1_eqn",
  ``algn_subtyping n G (fswap x y ty1) ty2 =
    algn_subtyping n (ctxtswap x y G) ty1 (fswap x y ty2)``,
  METIS_TAC [algn_subtyping_swap, ctxtswap_inv, fswap_inv]);


(* important to have this sort of inversion theorem, where you get the
   same bound variable in the "other" position of the relation.  By
   analogy, in the lambda calculus with beta reduction, you have to prove
   that if
     LAM v bod --> t
   then
     ?bod'. (t = LAM v bod') /\ bod --> bod'
   In the lambda calculus, it's always possible to get this v (which
   has to do with the fact that beta reduction doesn't produce extra
   free variables).  In F<:, your x has to satisfy certain constraints.
*)
val algn_subtyping_ForallTy_eqn = store_thm(
  "algn_subtyping_ForallTy_eqn",
  ``~(x IN ftyFV bnd) /\ ~(x IN cdom G) ==>
    (algn_subtyping p G (ForallTy x bnd ty) t =
       wfctxt G /\
       ((t = Top) /\ (p = 0) /\ ftyFV (ForallTy x bnd ty) SUBSET cdom G \/
        (?ty' p0. (t = ForallTy x bnd ty') /\ (p = p0 + 1) /\
                  algn_subtyping p0 ((x,bnd)::G) ty ty')))``,
  SIMP_TAC (srw_ss() ++ DNF_ss ++ SatisfySimps.SATISFY_ss)
           [EQ_IMP_THM, algn_subtyping_rules, algn_subtyping_wfctxt] THEN
  STRIP_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [algn_subtyping_cases])) THEN
  SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) [ForallTy_11] THEN
  Q.EXISTS_TAC `fswap x x' t2` THEN
  `wfctxt ((x',u1)::G)` by METIS_TAC [algn_subtyping_wfctxt] THEN
  FULL_SIMP_TAC (srw_ss()) [algn_subtyping_swap1_eqn] THEN
  `ftyFV t2 SUBSET cdom ((x',u1)::G)`
     by METIS_TAC [algn_subtyping_ftyFVs_in_ctxt] THEN
  Cases_on `x = x'` THEN1 SRW_TAC [][] THEN
  `~(x' IN ftyFV u1) /\ ~(x IN ftyFV t2)`
     by METIS_TAC [SUBSET_DEF, cdom_def, pairTheory.FST, IN_INSERT] THEN
  SRW_TAC [][ctxtswap_fresh, fswap_fresh, wfctxt_ctxtFV_cdom]);

val algn_subtyping_trans = prove(
  ``!n m p Gamma s q t.
         (n = m + p) /\
         algn_subtyping m Gamma s q /\
         algn_subtyping p Gamma q t ==>
         ?r. algn_subtyping r Gamma s t``,
  HO_MATCH_MP_TAC arithmeticTheory.COMPLETE_INDUCTION THEN
  REPEAT STRIP_TAC THEN
  Q.PAT_ASSUM `algn_subtyping m Gamma s q`
              (MP_TAC o ONCE_REWRITE_RULE [algn_subtyping_cases]) THEN
  SRW_TAC [][] THENL [
    METIS_TAC [alg_subtyping_def, alg_subtyping_top_left,
               algn_subtyping_rules],
    METIS_TAC [],
    FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN
    `?r. algn_subtyping r Gamma u t`
       by METIS_TAC [DECIDE ``n + p < n + 1 + p``] THEN
    METIS_TAC [algn_subtyping_rules],
    Q.PAT_ASSUM `algn_subtyping p Gamma (Fun t1 t2) t`
                (MP_TAC o ONCE_REWRITE_RULE [algn_subtyping_cases]) THEN
    SRW_TAC [][] THEN1 METIS_TAC [algn_subtyping_rules,
                                  algn_subtyping_ftyFVs_in_ctxt] THEN
    FULL_SIMP_TAC (srw_ss() ++ DNF_ss) [AND_IMP_INTRO] THEN
    `?r. algn_subtyping r Gamma t1' s1`
        by (FIRST_X_ASSUM MATCH_MP_TAC THEN
            MAP_EVERY Q.EXISTS_TAC [`n'`, `n`, `t1`] THEN
            ASM_SIMP_TAC arith_ss [arithmeticTheory.MAX_DEF]) THEN
    `?r'. algn_subtyping r' Gamma s2 t2'`
        by (FIRST_X_ASSUM MATCH_MP_TAC THEN
            MAP_EVERY Q.EXISTS_TAC [`m'`, `m`, `t2`] THEN
            ASM_SIMP_TAC arith_ss [arithmeticTheory.MAX_DEF]) THEN
    METIS_TAC [algn_subtyping_rules],
    `wfctxt ((x,u1)::Gamma)` by METIS_TAC [algn_subtyping_wfctxt] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    `~(x IN ftyFV u1)` by METIS_TAC [SUBSET_DEF] THEN
    Q.PAT_ASSUM `algn_subtyping p Gamma (ForallTy x u1 t2) t` MP_TAC THEN
    ASM_SIMP_TAC (srw_ss()) [algn_subtyping_ForallTy_eqn] THEN
    SRW_TAC [][] THENL [
      (* case where it's less than Top *)
      IMP_RES_TAC algn_subtyping_ftyFVs_in_ctxt THEN
      FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN METIS_TAC [],
      ALL_TAC
    ] THEN
    SRW_TAC [][ForallTy_11] THEN
    METIS_TAC [DECIDE ``n + p0 < n + 1 + (p0 + 1)``]
  ]);

val alg_subtyping_trans (* lemma 28.3.2 *) = store_thm(
  "alg_subtyping_trans",
  ``!Gamma s q. Gamma |-> s <: q /\ Gamma |-> q <: t ==>
                Gamma |-> s <: t``,
  METIS_TAC [alg_subtyping_def, algn_subtyping_trans]);

val alg_soundcomplete (* theorem 28.3.3 *) = store_thm(
  "alg_soundcomplete",
  ``G |- ty1 <: ty2 = G |-> ty1 <: ty2``,
  EQ_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`ty2`, `ty1`, `G`] THENL [
    HO_MATCH_MP_TAC fsubtyping_ind THEN SRW_TAC [][alg_subtyping_rules] THENL [
      METIS_TAC [alg_subtyping_trans],
      `Gamma |-> ty <: ty`
         by METIS_TAC [alg_subtyping_refl, wfctxt_MEM, SUBSET_DEF] THEN
      METIS_TAC [alg_subtyping_rules]
    ],
    HO_MATCH_MP_TAC alg_subtyping_ind THEN SRW_TAC [][fsubtyping_rules] THEN
    METIS_TAC [fsubtyping_rules, wfctxt_MEM, SUBSET_DEF,
               fsubtyping_wfctxt]
  ]);

val _ = export_theory ();
