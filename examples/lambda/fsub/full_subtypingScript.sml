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
    (!Gamma x s1 s2 t1 t2 m n.
                 algn_subtyping m Gamma t1 s1 /\
                 algn_subtyping n ((x,t1)::Gamma) s2 t2 ==>
                 algn_subtyping (MAX m n + 1) Gamma (ForallTy x s1 s2)
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

val wfctxt_APPEND_down = store_thm(
  "wfctxt_APPEND_down",
  ``!X Y x y z. wfctxt (X ++ (x,y)::Y) /\ ftyFV z SUBSET cdom Y ==>
                wfctxt (X ++ (x,z)::Y)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  METIS_TAC []);

val wfctxt_INSERT = store_thm(
  "wfctxt_INSERT",
  ``!D G v ty.
        wfctxt (D ++ G) /\ ~(v IN cdom D) /\ ~(v IN cdom G) /\
        ftyFV ty SUBSET cdom G ==>
        wfctxt (D ++ (v,ty)::G)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD] THEN
  SRW_TAC [][SUBSET_DEF] THEN METIS_TAC []);

val wfctxt_APPEND_DISJOINT = store_thm(
  "wfctxt_APPEND_DISJOINT",
  ``!X Y. wfctxt (X ++ Y) ==> DISJOINT (cdom X) (cdom Y)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD]);

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

val algn_subtyping_FVs = store_thm(
  "algn_subtyping_FVs",
  ``!n G ty1 ty2. algn_subtyping n G ty1 ty2 ==>
                  ftyFV ty1 SUBSET cdom G /\
                  ftyFV ty2 SUBSET cdom G``,
  HO_MATCH_MP_TAC algn_subtyping_ind THEN SRW_TAC [][] THENL [
    METIS_TAC [cdom_MEM],
    FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN METIS_TAC [],
    FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN METIS_TAC []
  ]);

val strong_algn_subtyping_ind =
    IndDefRules.derive_strong_induction (CONJUNCTS algn_subtyping_rules,
                                         algn_subtyping_ind)

(* lemma 28.4.1.1 *)
val algn_subtyping_permutation = store_thm(
  "algn_subtyping_permutation",
  ``!n G t1 t2. algn_subtyping n G t1 t2 ==>
                !D. PERM D G /\ wfctxt D ==>
                    algn_subtyping n D t1 t2``,
  HO_MATCH_MP_TAC strong_algn_subtyping_ind THEN REPEAT CONJ_TAC THENL [
    METIS_TAC [algn_subtyping_rules, cdom_PERM],
    METIS_TAC [algn_subtyping_rules, cdom_PERM],
    METIS_TAC [algn_subtyping_rules, PERM_MEM_EQ],
    METIS_TAC [algn_subtyping_rules],
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (last (CONJUNCTS algn_subtyping_rules)) THEN
    `wfctxt ((x,t1')::G)` by METIS_TAC [algn_subtyping_wfctxt] THEN
    `~(x IN cdom G) /\ ftyFV t1' SUBSET cdom G`
        by FULL_SIMP_TAC (srw_ss()) [] THEN
    `~(x IN cdom D) /\ ftyFV t1' SUBSET cdom D`
        by METIS_TAC [cdom_PERM] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][]
  ]);

(* lemma 28.4.1.2 *)
val algn_subtyping_weakening = store_thm(
  "algn_subtyping_weakening",
  ``!n G t1 t2. algn_subtyping n G t1 t2 ==>
                !D. wfctxt (D ++ G) ==> algn_subtyping n (D ++ G) t1 t2``,
  HO_MATCH_MP_TAC strong_algn_subtyping_ind THEN REPEAT CONJ_TAC THENL[
    SRW_TAC [][SUBSET_DEF, wfctxt_APPEND, algn_subtyping_rules],
    SRW_TAC [][SUBSET_DEF, wfctxt_APPEND, algn_subtyping_rules],
    METIS_TAC [listTheory.MEM_APPEND, algn_subtyping_rules],
    SRW_TAC [][algn_subtyping_rules],

    (* SA-ALL case *)
    Q_TAC SUFF_TAC
          `!G x s1 s2 t1 t2 m n.
              algn_subtyping m G t1 s1 /\
              (!D. wfctxt (D ++ G) ==> algn_subtyping m (D ++ G) t1 s1) /\
              algn_subtyping n ((x,t1)::G) s2 t2 /\
              (!D. wfctxt (D ++ (x,t1)::G) ==>
                   algn_subtyping n (D ++ (x,t1)::G) s2 t2) ==>
              !D. wfctxt (D ++ G) ==>
                  algn_subtyping (MAX m n + 1) (D ++ G)
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
        by SRW_TAC [][ForallTy_11] THEN

    (* by SA-ALL rule if suffices to show (various side conditions drop
       out because z is fresh) ... *)
    Q_TAC SUFF_TAC
          `algn_subtyping m (D ++ G) t1 s1 /\
           algn_subtyping n ((z,t1)::(D ++ G)) (fswap z x s2) (fswap z x t2)`
          THEN1 SRW_TAC [][algn_subtyping_rules, SUBSET_DEF] THEN

    `wfctxt ((x,t1)::G) /\ wfctxt G` by METIS_TAC [algn_subtyping_wfctxt] THEN
    `~(x IN cdom G) /\ (!v. v IN ftyFV t1 ==> v IN cdom G)`
       by FULL_SIMP_TAC (srw_ss()) [wfctxt_def, SUBSET_DEF] THEN
    `~(x IN ftyFV t1)` by METIS_TAC [] THEN

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
    `wfctxt (ctxtswap z x D ++ G)`
       by (`ctxtswap z x D ++ G = ctxtswap z x (D ++ G)`
              by SRW_TAC [][ctxtswap_fresh, wfctxt_ctxtFV_cdom] THEN
           METIS_TAC [wfctxt_swap]) THEN
    `wfctxt ((x,t1) :: ctxtswap z x D ++ G)`
       by SRW_TAC [][SUBSET_DEF, wfctxt_APPEND] THEN

    (* apply permutation result *)
    Q_TAC SUFF_TAC
          `algn_subtyping n (ctxtswap z x D ++ (x,t1)::G) s2 t2`
          THEN1 METIS_TAC [algn_subtyping_permutation] THEN

    (* apply IH  *)
    Q_TAC SUFF_TAC `wfctxt (ctxtswap z x D ++ (x,t1)::G)`
          THEN1 SRW_TAC [][] THEN

    `ctxtswap z x D ++ (x,t1)::G = ctxtswap z x (D ++ (z,t1)::G)`
       by SRW_TAC [][fswap_fresh, ctxtswap_fresh, wfctxt_ctxtFV_cdom] THEN
    SRW_TAC [][wfctxt_INSERT, SUBSET_DEF]
  ]);

val algn_subtyping_Top_left = store_thm(
  "algn_subtyping_Top_left",
  ``algn_subtyping n G Top t = (t = Top) /\ (n = 0) /\ wfctxt G``,
  ONCE_REWRITE_TAC [algn_subtyping_cases] THEN
  SRW_TAC [][] THEN METIS_TAC []);
val _ = export_rewrites ["algn_subtyping_Top_left"]

val wfctxt_assoc_unique = store_thm(
  "wfctxt_assoc_unique",
  ``!G x y z. wfctxt G /\ MEM (x,y) G /\ MEM (x,z) G ==> (z = y)``,
  Induct THEN ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, cdom_MEM] THEN
  METIS_TAC []);

val algn_subtyping_foralltyleft_inversion = store_thm(
  "algn_subtyping_foralltyleft_inversion",
  ``~(x IN cdom G) /\ ~(x IN ftyFV t1) ==>
    (algn_subtyping n G (ForallTy x t1 t2) t =
     wfctxt G /\
     ((t = Top) /\ (n = 0) /\ ftyFV (ForallTy x t1 t2) SUBSET cdom G \/
      (?t1' t2' m1 m2. (t = ForallTy x t1' t2') /\
                       (n = MAX m1 m2 + 1) /\
                       algn_subtyping m1 G t1' t1 /\
                       algn_subtyping m2 ((x,t1')::G) t2 t2')))``,
  SIMP_TAC (srw_ss() ++ DNF_ss ++ SatisfySimps.SATISFY_ss)
           [EQ_IMP_THM, algn_subtyping_rules, algn_subtyping_wfctxt] THEN
  STRIP_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [algn_subtyping_cases])) THEN
  SRW_TAC[][] THEN DISJ2_TAC THEN
  Cases_on `x = x'` THEN FULL_SIMP_TAC (srw_ss()) [ForallTy_11] THENL [
    METIS_TAC [],
    Q.EXISTS_TAC `fswap x x' t2'` THEN
    SRW_TAC [][algn_subtyping_swap1_eqn] THEN
    `wfctxt G /\ wfctxt ((x',t1')::G)`
       by METIS_TAC [algn_subtyping_wfctxt] THEN
    `~(x' IN cdom G) /\ (!v. v IN ftyFV t1' ==> v IN cdom G)`
       by METIS_TAC [SUBSET_DEF, wfctxt_def] THEN
    `~(x' IN ftyFV t1') /\ ~(x IN ftyFV t1')` by METIS_TAC [] THEN
    `ctxtswap x x' G = G`
       by SRW_TAC [][ctxtswap_fresh, wfctxt_ctxtFV_cdom] THEN
    SRW_TAC [][fswap_fresh] THEN
    `ftyFV t2' SUBSET cdom ((x',t1')::G)`
        by METIS_TAC [algn_subtyping_FVs] THEN
    `~(x IN ftyFV t2')`
        by METIS_TAC [SUBSET_DEF, cdom_def, IN_INSERT, pairTheory.FST] THEN
    METIS_TAC []
  ]);

val lemma28_4_2_0 = prove(
  ``!sz q. (fsize q = sz) ==>
       (!i j G s t. algn_subtyping i G s q /\ algn_subtyping j G q t ==>
                    ?k. algn_subtyping k G s t) /\
       (!i j G D p m n x.
                    algn_subtyping i (D ++ ((x,q) :: G)) m n /\
                    algn_subtyping j G p q ==>
                    ?k. algn_subtyping k (D ++ (x,p) :: G) m n)``,
  HO_MATCH_MP_TAC arithmeticTheory.COMPLETE_INDUCTION THEN
  GEN_TAC THEN
  DISCH_THEN (STRIP_ASSUME_TAC o SIMP_RULE (srw_ss() ++ DNF_ss) []) THEN
  GEN_TAC THEN STRIP_TAC THEN
  (* part 1 *)
  `!i j G s t.
      algn_subtyping i G s q /\ algn_subtyping j G q t ==>
      ?k. algn_subtyping k G s t`
      by (HO_MATCH_MP_TAC arithmeticTheory.COMPLETE_INDUCTION THEN
          GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
          CONV_TAC (LAND_CONV
                    (LAND_CONV
                       (ONCE_REWRITE_CONV [algn_subtyping_cases]))) THEN
          SRW_TAC [][] THENL [
            (* Top case *)
            FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
            METIS_TAC [algn_subtyping_rules],
            (* Tyvar case - 1*)
            METIS_TAC [],
            (* Tyvar case - 2*)
            `?k. algn_subtyping k G u t`
               by METIS_TAC [DECIDE ``n < n + 1``] THEN
            METIS_TAC [algn_subtyping_rules],
            (* Fun case *)
            Q.PAT_ASSUM `algn_subtyping X Y (Fun t1 t2) Z`
                        (MP_TAC o
                         ONCE_REWRITE_RULE [algn_subtyping_cases]) THEN
            SRW_TAC [][] THENL [
              METIS_TAC [algn_subtyping_rules, ftyFV_thm, UNION_SUBSET,
                         algn_subtyping_FVs],
              `fsize t1 < fsize (Fun t1 t2) /\ fsize t2 < fsize (Fun t1 t2)`
                 by SRW_TAC [numSimps.ARITH_ss][fsize_thm] THEN
              `(?k1. algn_subtyping k1 G t1' s1) /\
               (?k2. algn_subtyping k2 G s2 t2')`
                 by METIS_TAC [] THEN
              METIS_TAC [algn_subtyping_rules]
            ],

            (* ForallTy case *)
            `wfctxt G /\ wfctxt ((x,t1)::G)`
               by METIS_TAC [algn_subtyping_wfctxt] THEN
            `~(x IN cdom G) /\ (!v. v IN ftyFV t1 ==> v IN cdom G)`
               by FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
            `~(x IN ftyFV t1)` by METIS_TAC [] THEN
            `ftyFV s1 SUBSET cdom G /\ ftyFV s2 SUBSET cdom ((x,t1)::G)`
               by METIS_TAC [algn_subtyping_FVs] THEN
            `~(x IN ftyFV s1)` by METIS_TAC [SUBSET_DEF] THEN
            Q.PAT_ASSUM `algn_subtyping X Y (ForallTy x t1 t2) Z` MP_TAC THEN
            SRW_TAC [][algn_subtyping_foralltyleft_inversion] THENL [
              FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
              METIS_TAC [],
              SRW_TAC [][ForallTy_11] THEN
              `fsize t1 < fsize (ForallTy x t1 t2) /\
               fsize t2 < fsize (ForallTy x t1 t2)`
                 by SRW_TAC[numSimps.ARITH_ss][fsize_thm] THEN
              `?k1. algn_subtyping k1 G t1' s1` by METIS_TAC [] THEN
              Q_TAC SUFF_TAC
                    `?k2. algn_subtyping k2 ((x,t1')::G) s2 t2'`
                    THEN1 METIS_TAC [] THEN
              Q_TAC SUFF_TAC
                    `?k3. algn_subtyping k3 ((x,t1')::G) s2 t2`
                    THEN1 METIS_TAC [] THEN
              METIS_TAC [listTheory.APPEND]
            ]
          ]) THEN
  (* part 2 *)
  CONJ_TAC THEN1 FIRST_ASSUM ACCEPT_TAC THEN
  HO_MATCH_MP_TAC arithmeticTheory.COMPLETE_INDUCTION THEN
  REPEAT STRIP_TAC THEN
  `ftyFV p SUBSET cdom G` by METIS_TAC [algn_subtyping_FVs] THEN
  `wfctxt (D ++ (x,q)::G)` by METIS_TAC [algn_subtyping_wfctxt] THEN
  `wfctxt (D ++ (x,p)::G)` by METIS_TAC [wfctxt_APPEND_down] THEN
  Q.PAT_ASSUM `algn_subtyping X (D ++ Y :: G) M N` MP_TAC THEN
  Q.ABBREV_TAC `xqctxt = D ++ (x,q) :: G` THEN
  Q.ABBREV_TAC `xpctxt = D ++ (x,p) :: G` THEN
  `cdom xpctxt = cdom xqctxt` by SRW_TAC [][Abbr`xpctxt`, Abbr`xqctxt`] THEN
  CONV_TAC (LAND_CONV
              (ONCE_REWRITE_CONV [algn_subtyping_cases])) THEN
  SRW_TAC [][]THENL [
    (* Top case *)
    Q.EXISTS_TAC `0` THEN SRW_TAC [][algn_subtyping_rules],

    (* tyvar refl case  *)
    Q.EXISTS_TAC `0` THEN SRW_TAC [][algn_subtyping_rules],

    (* tyvar trans case *)
    Cases_on `x = x'` THENL [
      `u = q`
        by (`MEM (x,q) xqctxt` by SRW_TAC [][Abbr`xqctxt`] THEN
            METIS_TAC [wfctxt_assoc_unique]) THEN
      REPEAT VAR_EQ_TAC THEN
      `n' < n' + 1` by DECIDE_TAC THEN
      `?k. algn_subtyping k xpctxt q n` by METIS_TAC [] THEN
      `MEM (x,p) xpctxt` by SRW_TAC [][Abbr`xpctxt`] THEN
      Q_TAC SUFF_TAC
            `?k1. algn_subtyping k1 xpctxt p n`
            THEN1 METIS_TAC [algn_subtyping_rules] THEN
      Q_TAC SUFF_TAC
            `?k2. algn_subtyping k2 xpctxt p q`
            THEN1 METIS_TAC [] THEN
      `xpctxt = (D ++ [(x,p)]) ++ G`
         by ASM_SIMP_TAC bool_ss [GSYM listTheory.APPEND_ASSOC, Abbr`xpctxt`,
                                  listTheory.APPEND] THEN
      METIS_TAC [algn_subtyping_weakening],

      `MEM (x',u) xpctxt`
         by FULL_SIMP_TAC (srw_ss()) [Abbr`xpctxt`, Abbr`xqctxt`] THEN
      METIS_TAC [algn_subtyping_rules, DECIDE ``n' < n' + 1``]
    ],

    (* Fun case *)
    `n' < MAX n' m' + 1 /\ m' < MAX n' m' + 1`
       by SRW_TAC [numSimps.ARITH_ss][arithmeticTheory.MAX_DEF] THEN
    METIS_TAC [algn_subtyping_rules],

    (* Forall case *)
    `n' < MAX m' n' + 1 /\ m' < MAX m' n' + 1`
       by SRW_TAC [numSimps.ARITH_ss][arithmeticTheory.MAX_DEF] THEN
    `?k1. algn_subtyping k1 xpctxt t1 s1` by METIS_TAC [] THEN
    `((x',t1) :: xqctxt = ((x',t1)::D) ++ ((x,q)::G)) /\
     ((x',t1) :: xpctxt = ((x',t1)::D) ++ ((x,p)::G))`
       by SRW_TAC [][Abbr`xqctxt`, Abbr`xpctxt`] THEN
    `?k2. algn_subtyping k2 ((x',t1)::xpctxt) s2 t2`
       by METIS_TAC [] THEN
    METIS_TAC [algn_subtyping_rules]
  ]);

val _ = remove_rules_for_term "dSUB"

val _ = add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                  fixity = Infix(NONASSOC, 425),
                  paren_style = OnlyIfNecessary,
                  pp_elements = [HardSpace 1, TOK "|->", BreakSpace(1, 0),
                                 BeginFinalBlock(PP.INCONSISTENT, 2),
                                 TM, HardSpace 1, TOK "<:", BreakSpace(1,0)],
                  term_name = "alg_subtyping"}

val alg_subtyping_def = Define`
  G |-> ty1 <: ty2 = ?n. algn_subtyping n G ty1 ty2
`;

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

val alg_subtyping_ind = save_thm(
  "alg_subtyping_ind",
    (Q.GEN `P` o
     SIMP_RULE (srw_ss()) [GSYM alg_subtyping_def] o
     CONV_RULE (RAND_CONV
                  (SWAP_VARS_CONV THENC
                   BINDER_CONV (SWAP_VARS_CONV THENC
                                BINDER_CONV (SWAP_VARS_CONV THENC
                                             BINDER_CONV FORALL_IMP_CONV)))) o
     SIMP_RULE (srw_ss()) [] o
     Q.SPEC `\n G ty1 ty2. P G ty1 ty2`) algn_subtyping_ind);

val alg_subtyping_cases = save_thm(
  "alg_subtyping_cases",
    (REWRITE_CONV [alg_subtyping_def] THENC
     ONCE_REWRITE_CONV [algn_subtyping_cases] THENC
     SIMP_CONV (srw_ss()) [EXISTS_OR_THM] THENC
     SIMP_CONV (srw_ss())
               (map (INST_TYPE [alpha |-> numSyntax.num])
                    [LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM]) THENC
     REWRITE_CONV [GSYM alg_subtyping_def])
      ``Gamma |-> ty1 <: ty2``);

val alg_subtyping_swap1_eqn = store_thm(
  "alg_subtyping_swap1_eqn",
  ``G |-> fswap x y ty1 <: ty2 = ctxtswap x y G |-> ty1 <: fswap x y ty2``,
  METIS_TAC [alg_subtyping_def, algn_subtyping_swap1_eqn]);

val alg_subtyping_refl = store_thm(
  "alg_subtyping_refl",
  ``!ty G. wfctxt G /\ ftyFV ty SUBSET cdom G ==> G |-> ty <: ty``,
  HO_MATCH_MP_TAC fsubty_ind THEN
  SRW_TAC [][alg_subtyping_rules] THEN
  Q_TAC (NEW_TAC "z") `cdom G UNION ftyFV ty UNION ftyFV ty'` THEN
  `ForallTy v ty ty' = ForallTy z ty (fswap z v ty')`
     by SRW_TAC [][ForallTy_11] THEN
  SRW_TAC [][] THEN
  MATCH_MP_TAC (last (CONJUNCTS alg_subtyping_rules)) THEN
  SRW_TAC [][alg_subtyping_swap1_eqn] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
  METIS_TAC [swapTheory.swapstr_def]);

val alg_subtyping_trans = store_thm(
  "alg_subtyping_trans",
  ``G |-> ty1 <: ty2 /\ G |-> ty2 <: ty3 ==> G |-> ty1 <: ty3``,
  METIS_TAC [alg_subtyping_def, lemma28_4_2_0]);

val alg_soundcomplete = store_thm(
  "alg_soundcomplete",
  ``G |- ty1 <: ty2 = G |-> ty1 <: ty2``,
  EQ_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`ty2`, `ty1`, `G`] THENL [
    HO_MATCH_MP_TAC fsubtyping_ind THEN
    SRW_TAC [][alg_subtyping_rules] THENL [
      METIS_TAC [alg_subtyping_refl],
      METIS_TAC [alg_subtyping_trans],
      METIS_TAC [wfctxt_MEM, SUBSET_DEF, alg_subtyping_refl,
                 alg_subtyping_rules]
    ],
    HO_MATCH_MP_TAC alg_subtyping_ind THEN
    SRW_TAC [][fsubtyping_rules] THEN
    METIS_TAC [fsubtyping_rules, fsubtyping_wfctxt]
  ]);

val _ = export_theory()

