open HolKernel Parse boolLib

open bossLib ncLib

open ncTheory fixedPointTheory pred_setTheory pred_setLib
open swapTheory BasicProvers

val _ = new_theory "chap2";

val (ctxt_rules, ctxt_indn, ctxt_cases) =  (* p. 10 *)
  Hol_reln`(!s. ctxt (\x. VAR s))                       /\
           (!c. ctxt (\x. CON c))                       /\
           ctxt (\x. x)                                 /\
           (!c1 c2. ctxt c1 /\ ctxt c2 ==>
                    ctxt (\x. c1 x @@ c2 x))            /\
           (!v c.   ctxt c ==> ctxt (\x. LAM v (c x)))`;

val constant_contexts_exist = store_thm(
  "constant_contexts_exist",
  ``!t. ctxt (\x. t)``,
  HO_MATCH_MP_TAC ncTheory.nc_INDUCTION THEN REPEAT STRIP_TAC THEN
  SRW_TAC [][ctxt_rules] THEN
  POP_ASSUM (Q.SPEC_THEN `x` MP_TAC) THEN
  SRW_TAC [][ncTheory.lemma14a] THEN
  `ctxt (\x'. LAM x ((\x'. t) x'))` by SRW_TAC [][ctxt_rules] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val (one_hole_context_rules, one_hole_context_ind, one_hole_context_cases) =
  Hol_reln`one_hole_context (\x.x) /\
           (!x c. one_hole_context c ==> one_hole_context (\t. x @@ c t)) /\
           (!x c. one_hole_context c ==> one_hole_context (\t. c t @@ x)) /\
           (!v c. one_hole_context c ==> one_hole_context (\t. LAM v (c t)))`;

val leftctxt = store_thm(
  "leftctxt",
  ``!z. one_hole_context ($@@ z)``,
  Q_TAC SUFF_TAC `!z. one_hole_context (\t. z @@ (\x. x) t)` THEN1
     SRW_TAC [boolSimps.ETA_ss][] THEN
  SRW_TAC [][one_hole_context_rules]);

val rightctxt_def = Define`rightctxt z = \t. t @@ z`;
val rightctxt_thm = store_thm(
  "rightctxt_thm",
  ``!t z. rightctxt z t = t @@ z``,
  SRW_TAC [][rightctxt_def]);

val rightctxt = store_thm(
  "rightctxt",
  ``!z. one_hole_context (rightctxt z)``,
  Q_TAC SUFF_TAC `!z. one_hole_context (\t. (\x. x) t @@ z)` THEN1
     SRW_TAC [boolSimps.ETA_ss][rightctxt_def] THEN
  SRW_TAC [][one_hole_context_rules]);

val absctxt = store_thm(
  "absctxt",
  ``!v. one_hole_context (LAM v)``,
  Q_TAC SUFF_TAC `!v. one_hole_context (\t. LAM v ((\x. x) t))` THEN1
     SRW_TAC [boolSimps.ETA_ss][] THEN
  SRW_TAC [][one_hole_context_rules]);

val one_hole_is_normal = store_thm(
  "one_hole_is_normal",
  ``!c. one_hole_context c ==> ctxt c``,
  MATCH_MP_TAC one_hole_context_ind THEN SRW_TAC [][ctxt_rules] THEN
  `ctxt (\y. x)` by Q.SPEC_THEN `x` ACCEPT_TAC constant_contexts_exist THEN
  `!c1 c2. ctxt c1 /\ ctxt c2 ==> ctxt (\t. c1 t @@ c2 t)` by
      SRW_TAC [][ctxt_rules] THEN
  POP_ASSUM
  (fn imp =>
      POP_ASSUM (fn cth =>
                    POP_ASSUM (fn th =>
                                  MP_TAC (MATCH_MP imp (CONJ th cth)) THEN
                                  MP_TAC (MATCH_MP imp (CONJ cth th))))) THEN
  SIMP_TAC std_ss []);

val _ = set_fixity "==" (Infix(NONASSOC, 510));
val (lam_eq_rules, lam_eq_indn, lam_eq_cases) = (* p. 13 *)
  Hol_reln`(!x M N. (LAM x M) @@ N == [N/x]M) /\
           (!M. M == M) /\
           (!M N. M == N ==> N == M) /\
           (!M N L. M == N /\ N == L ==> M == L) /\
           (!M N Z. M == N ==> M @@ Z == N @@ Z) /\
           (!M N Z. M == N ==> Z @@ M == Z @@ N) /\
           (!M N x. M == N ==> LAM x M == LAM x N)`;

val _ = app (uncurry set_MLname) [("==_rules", "lam_eq_rules"),
                                  ("==_ind", "lam_eq_indn"),
                                  ("==_cases", "lam_eq_cases")]

val fixed_point_thm = store_thm(  (* p. 14 *)
  "fixed_point_thm",
  ``!f. ?x. f @@ x == x``,
  GEN_TAC THEN Q_TAC (NEW_TAC "x") `FV f` THEN
  Q.ABBREV_TAC `w = (LAM x (f @@ (VAR x @@ VAR x)))` THEN
  Q.EXISTS_TAC `w @@ w` THEN
  `w @@ w == [w/x] (f @@ (VAR x @@ VAR x))` by PROVE_TAC [lam_eq_rules] THEN
  POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC (srw_ss())[ncTheory.ALT_SUB_THM, lemma14b, lam_eq_rules]);

(* properties of substitution - p19 *)

val SUB_TWICE_ONE_VAR = store_thm(
  "SUB_TWICE_ONE_VAR",
  ``!body x y v. [x/v] ([y/v] body) = [[x/v]y / v] body``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN SRW_TAC [][SUB_THM, SUB_VAR] THEN
  Q_TAC (NEW_TAC "newx") `v INSERT FV body UNION FV y UNION FV x'` THEN
  `LAM x body = LAM newx ([VAR newx/x]body)` by SRW_TAC [][ALPHA] THEN
  SRW_TAC [][SUB_THM] THEN
  Cases_on `v IN FV y` THEN SRW_TAC [][SUB_THM, lemma14c, lemma14b]);

val lemma2_11 = store_thm(
  "lemma2_11",
  ``!t u v M N. ~(v = u)  /\ ~(v IN FV M) ==>
                ([M/u] ([N/v] t) = [[M/u]N/v] ([M/u] t))``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN SRW_TAC [][SUB_THM, SUB_VAR, lemma14b] THEN
  Q_TAC (NEW_TAC "newx") `{u;v} UNION FV t UNION FV M UNION FV N` THEN
  `LAM x t = LAM newx ([VAR newx/x] t)` by SRW_TAC [][ALPHA] THEN
  SRW_TAC [][SUB_THM] THEN
  Cases_on `u IN FV N` THENL [
    SRW_TAC [][SUB_THM, lemma14c],
    Q_TAC (fn t =>
              SIMP_TAC (srw_ss()) [lemma14b, ASSUME t]) `~(u IN FV N)` THEN
    FIRST_X_ASSUM (K ALL_TAC o assert (is_forall o concl)) THEN
    SRW_TAC [][SUB_THM]
  ]);

val GENERAL_SUB_COMMUTE = store_thm(
  "GENERAL_SUB_COMMUTE",
  ``!t M N u v w.
       ~(w = u) /\ ~(w IN FV t) /\ ~(w IN FV M) ==>
       ([M/u] ([N/v] t) = [[M/u]N/w]([M/u] ([VAR w/v] t)))``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [][SUB_THM, SUB_VAR] THENL [
    COND_CASES_TAC THEN
    FULL_SIMP_TAC (srw_ss())[SUB_THM, SUB_VAR, lemma14b],

    Q_TAC (NEW_TAC "newx") `{w;u;v} UNION FV t UNION FV M UNION FV N` THEN
    `LAM x t = LAM newx ([VAR newx/x] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    SRW_TAC [][SUB_THM] THEN
    Cases_on `u IN FV N` THENL [
      SRW_TAC [][SUB_THM, lemma14c, LAM_VAR_INJECTIVE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      Cases_on `x IN FV t` THEN
      SRW_TAC [][lemma14c, lemma14b],
      `FV ([M/u] N) = FV N` by PROVE_TAC [lemma14b] THEN
      SRW_TAC [][SUB_THM, LAM_VAR_INJECTIVE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      Cases_on `x IN FV t` THEN
      SRW_TAC [][lemma14c, lemma14b]
    ],

    Q_TAC (NEW_TAC "newx") `{w;u;v} UNION FV t UNION FV M UNION FV N` THEN
    `LAM w t = LAM newx ([VAR newx/w] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    ASM_REWRITE_TAC [] THEN SRW_TAC [][SUB_THM] THEN
    Cases_on `u IN FV N` THENL [
      SRW_TAC [][SUB_THM, lemma14c] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      Cases_on `w IN FV t` THEN
      SRW_TAC [][lemma14c, lemma14b],
      `FV ([M/u] N) = FV N` by PROVE_TAC [lemma14b] THEN
      SRW_TAC [][SUB_THM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      Cases_on `w IN FV t` THEN
      SRW_TAC [][lemma14c, lemma14b]
    ]
  ]);

val NOT_IN_FV_SUB = store_thm(
  "NOT_IN_FV_SUB",
  ``!x t u v. ~(x IN FV u) /\ ~(x IN FV t) ==> ~(x IN FV ([t/v]u))``,
  SRW_TAC [][FV_SUB]);


val ISUB_SUB_COMMUTE = store_thm(
  "ISUB_SUB_COMMUTE",
  ``!R M N x v.
        ~(v IN FV M) /\ ~(v IN FV N) /\ ~(v IN DOM R) /\ ~(v IN FVS R) ==>
        ([N ISUB R/v] ([VAR v/x] M ISUB R) = [N/x] M ISUB R)``,
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [ISUB_def, FVS_def, lemma15a, DOM_def,
                           pairTheory.FORALL_PROD] THEN
  CONV_TAC (RENAME_VARS_CONV ["P", "y"]) THEN
  Q.ABBREV_TAC `Rf = \x. x ISUB R` THEN
  `!t. t ISUB R = Rf t` by SRW_TAC [][] THEN
  FIRST_X_ASSUM (K ALL_TAC o assert (is_eq o concl)) THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC THEN
  Q_TAC (NEW_TAC "u") `{v;y;x} UNION FV M UNION FV N UNION FV P UNION
                       DOM R` THEN
  `[P/y] ([N/x] M) = [[P/y]N/u] ([P/y] ([VAR u/x] M))` by
     SRW_TAC [][GENERAL_SUB_COMMUTE] THEN
  `[Rf ([P/y]N)/v] (Rf ([VAR v/u] ([P/y] ([VAR u/x]M)))) =
   Rf ([[P/y] N/u] ([P/y] ([VAR u/x]M)))` by
     SRW_TAC [][NOT_IN_FV_SUB] THEN
  `[VAR v/u] ([P/y] ([VAR u/x] M)) = [P/y] ([VAR v/x] M)` by
      (Q.SPECL_THEN [`M`,`P`,`VAR v`,`y`,`x`,`u`]
                    MP_TAC GENERAL_SUB_COMMUTE THEN
       SRW_TAC [][lemma14b]) THEN
  POP_ASSUM SUBST_ALL_TAC THEN SRW_TAC [][]);

val lemma2_12 = store_thm( (* p. 19 *)
  "lemma2_12",
  ``(M == M' ==> [N/x]M == [N/x]M') /\
    (N == N' ==> [N/x]M == [N'/x]M) /\
    (M == M' /\ N == N' ==> [N/x]M == [N'/x]M')``,
  Q.SUBGOAL_THEN `(!M M':'a nc. M == M' ==> !N x. [N/x]M == [N/x]M') /\
                  (!N N':'a nc. N == N' ==> !M x. [N/x]M == [N'/x]M)`
     (fn th => STRIP_ASSUME_TAC th THEN SRW_TAC[][])
  THENL [
    CONJ_TAC THENL [
      REPEAT STRIP_TAC THEN
      `LAM x M == LAM x M'` by PROVE_TAC [lam_eq_rules] THEN
      `LAM x M @@ N == LAM x M' @@ N` by PROVE_TAC [lam_eq_rules] THEN
      PROVE_TAC [lam_eq_rules],
      Q_TAC SUFF_TAC `!M N N' x. N == N' ==> [N/x] M == [N'/x]M` THEN1
        SRW_TAC [][] THEN
      HO_MATCH_MP_TAC nc_INDUCTION THEN
      REVERSE (SRW_TAC [][SUB_THM, SUB_VAR]) THEN1
        (Q_TAC (NEW_TAC "y") `x' INSERT FV M UNION FV N UNION FV N'` THEN
         `LAM x M = LAM y ([VAR y/x]M)` by SRW_TAC [][SIMPLE_ALPHA] THEN
         SRW_TAC [][SUB_THM] THEN
         PROVE_TAC [lam_eq_rules]) THEN
      PROVE_TAC [lam_eq_rules]
    ],
    PROVE_TAC [lam_eq_rules]
  ]);

val lemma2_13 = store_thm( (* p.20 *)
  "lemma2_13",
  ``!c n n'. ctxt c ==> (n == n') ==> (c n == c n')``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`n`, `n'`] THEN
  POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `c` THEN
  HO_MATCH_MP_TAC ctxt_indn THEN PROVE_TAC [lam_eq_rules]);

val (lamext_rules, lamext_indn, lamext_cases) = (* p. 21 *)
  Hol_reln`(!x M N. lamext ((LAM x M) @@ N) ([N/x]M)) /\
           (!M. lamext M M) /\
           (!M N. lamext M N ==> lamext N M) /\
           (!M N L. lamext M N /\ lamext N L ==> lamext M L) /\
           (!M N Z. lamext M N ==> lamext (M @@ Z) (N @@ Z)) /\
           (!M N Z. lamext M N ==> lamext (Z @@ M) (Z @@ N)) /\
           (!M N x. lamext M N ==> lamext (LAM x M) (LAM x N)) /\
           (!M N x. ~(x IN FV (M @@ N)) /\
                    lamext (M @@ VAR x) (N @@ VAR x) ==>
                    lamext M N)`

val (lameta_rules, lameta_ind, lameta_cases) = (* p. 21 *)
  Hol_reln`(!x M N. lameta ((LAM x M) @@ N) ([N/x]M)) /\
           (!M. lameta M M) /\
           (!M N. lameta M N ==> lameta N M) /\
           (!M N L. lameta M N /\ lameta N L ==> lameta M L) /\
           (!M N Z. lameta M N ==> lameta (M @@ Z) (N @@ Z)) /\
           (!M N Z. lameta M N ==> lameta (Z @@ M) (Z @@ N)) /\
           (!M N x. lameta M N ==> lameta (LAM x M) (LAM x N)) /\
           (!M x. ~(x IN FV M) ==> lameta (LAM x (M @@ VAR x)) M)`;

val lemma2_14 = store_thm(
  "lemma2_14",
  ``!M N. lameta M N = lamext M N``,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`N`, `M`] THENL [
    (* eta ==> ext *)
    HO_MATCH_MP_TAC lameta_ind THEN REVERSE (REPEAT STRIP_TAC) THEN1
      (MATCH_MP_TAC (last (CONJUNCTS lamext_rules)) THEN
       Q.EXISTS_TAC `x` THEN
       ASM_SIMP_TAC (srw_ss()) [] THEN
       PROVE_TAC [lemma14a, lamext_rules]) THEN
    PROVE_TAC [lamext_rules],
    (* ext ==> eta *)
    HO_MATCH_MP_TAC lamext_indn THEN REVERSE (REPEAT STRIP_TAC) THEN1
      (`lameta (LAM x (M @@ VAR x)) (LAM x (N @@ VAR x))` by
          PROVE_TAC [lameta_rules] THEN
       FULL_SIMP_TAC (srw_ss()) [] THEN
       PROVE_TAC [lameta_rules]) THEN
    PROVE_TAC [lameta_rules]
  ]);

val _ = type_abbrev("termset", ``:'a nc # 'a nc -> bool``)

val beta_f_def =
    Define`beta_f (X:'a termset) =
                    { (LAM x M @@ N, [N/x] M) | T } : 'a termset`;
val beta_f_monotone = store_thm(
  "beta_f_monotone",
  ``monotone beta_f``,
  SIMP_TAC (srw_ss()) [fixedPointTheory.monotone_def, beta_f_def]);

val refl_f_def = Define`refl_f X = { (x,x) | T }`;

val refl_f_monotone = store_thm(
  "refl_f_monotone",
  ``monotone refl_f``,
  SRW_TAC [][monotone_def, refl_f_def]);

val sym_f_def = Define`sym_f X = { (x,y) | (y,x) IN X }`;

val sym_f_monotone = store_thm(
  "sym_f_monotone",
  ``monotone sym_f``,
  SRW_TAC[][monotone_def, sym_f_def, SUBSET_DEF]);

val trans_f_def = Define`trans_f X = { (x,z) | ?y. (x,y) IN X /\ (y,z) IN X }`;
val trans_f_monotone = store_thm(
  "trans_f_monotone",
  ``monotone trans_f``,
  SRW_TAC [][monotone_def, trans_f_def, SUBSET_DEF] THEN PROVE_TAC []);

val congl_f_def =
  Define`congl_f X = { (L,R) | ?M N Z. (L = M @@ Z) /\ (R = N @@ Z) /\
                                       (M,N) IN X }`;
val congl_f_monotone = store_thm(
  "congl_f_monotone",
  ``monotone congl_f``,
  SRW_TAC [][monotone_def, congl_f_def, SUBSET_DEF] THEN PROVE_TAC []);

val congr_f_def =
  Define`congr_f X = { (L,R) | ?M N Z. (L = Z @@ M) /\ (R = Z @@ N) /\
                                       (M,N) IN X }`;
val congr_f_monotone = store_thm(
  "congr_f_monotone",
  ``monotone congr_f``,
  SRW_TAC [][monotone_def, congr_f_def, SUBSET_DEF] THEN PROVE_TAC []);

val congabs_f_def =
  Define`congabs_f X = { (L,R) | ?M N x. (L = LAM x M) /\ (R = LAM x N) /\
                                         (M,N) IN X }`;
val congabs_f_monotone = store_thm(
  "congabs_f_monotone",
  ``monotone congabs_f``,
  SRW_TAC [][monotone_def, congabs_f_def, SUBSET_DEF] THEN PROVE_TAC []);

val stdlam_def =
  Define`stdlam = beta_f ++ congl_f ++ congr_f ++ congabs_f ++
                         refl_f ++ sym_f ++ trans_f`;

val stdlam_monotone = store_thm(
  "stdlam_monotone",
  ``monotone stdlam``,
  SRW_TAC [][stdlam_def] THEN
  PROVE_TAC [fnsum_monotone, beta_f_monotone, congl_f_monotone,
             congr_f_monotone, congabs_f_monotone, refl_f_monotone,
             sym_f_monotone, trans_f_monotone]);


val stdlam_refl = store_thm(
  "stdlam_refl",
  ``!thy. monotone thy ==> !x. (x,x) IN lfp (stdlam ++ thy)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lfp_empty THEN
  ASM_SIMP_TAC (srw_ss()) [fnsum_monotone, stdlam_monotone,
                           fnsum_def, stdlam_def, refl_f_def]);

val stdlam_sym = store_thm(
  "stdlam_sym",
  ``!thy. monotone thy ==>
          !x y. (x,y) IN lfp (stdlam ++ thy) ==>
                (y,x) IN lfp (stdlam ++ thy)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lfp_rule_applied THEN
  Q.EXISTS_TAC `{(x,y)}` THEN
  ASM_SIMP_TAC std_ss [IN_SING, SUBSET_DEF] THEN CONJ_TAC THENL [
    PROVE_TAC [stdlam_monotone, fnsum_monotone],
    ASM_SIMP_TAC (srw_ss()) [fnsum_def, stdlam_def, sym_f_def]
  ]);

val stdlam_trans = store_thm(
  "stdlam_trans",
  ``!thy. monotone thy ==>
          !x y z. (x,y) IN lfp (stdlam ++ thy) /\
                  (y,z) IN lfp (stdlam ++ thy) ==>
                  (x,z) IN lfp (stdlam ++ thy)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lfp_rule_applied THEN
  Q.EXISTS_TAC `{(x,y); (y,z)}` THEN
  ASM_SIMP_TAC (srw_ss()) [SUBSET_DEF, pairTheory.FORALL_PROD,
                           DISJ_IMP_THM, FORALL_AND_THM, fnsum_def,
                           stdlam_monotone, fnsum_monotone] THEN
  ASM_SIMP_TAC (srw_ss()) [stdlam_def, fnsum_def, trans_f_def] THEN
  PROVE_TAC []);

val stdlam_congl = store_thm(
  "stdlam_congl",
  ``!thy. monotone thy ==>
          !x y. (x, y) IN lfp (stdlam ++ thy) ==>
                !z. (x @@ z, y @@ z) IN lfp (stdlam ++ thy)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lfp_rule_applied THEN
  Q.EXISTS_TAC `{(x,y)}` THEN
  ASM_SIMP_TAC (srw_ss()) [SUBSET_DEF, fnsum_monotone, stdlam_monotone] THEN
  SIMP_TAC (srw_ss()) [congl_f_def, stdlam_def, fnsum_def,
                       nc_INJECTIVITY]);

val stdlam_congr = store_thm(
  "stdlam_congr",
  ``!thy. monotone thy ==>
          !x y. (x, y) IN lfp (stdlam ++ thy) ==>
                !z. (z @@ x, z @@ y) IN lfp (stdlam ++ thy)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lfp_rule_applied THEN
  Q.EXISTS_TAC `{(x,y)}` THEN
  ASM_SIMP_TAC (srw_ss()) [SUBSET_DEF, fnsum_monotone, stdlam_monotone] THEN
  SIMP_TAC (srw_ss()) [congr_f_def, stdlam_def, fnsum_def,
                       nc_INJECTIVITY]);

val stdlam_congabs = store_thm(
  "stdlam_congabs",
  ``!thy. monotone thy ==>
          !x y. (x, y) IN lfp (stdlam ++ thy) ==>
                !v. (LAM v x, LAM v y) IN lfp (stdlam ++ thy)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lfp_rule_applied THEN
  Q.EXISTS_TAC `{(x,y)}` THEN
  ASM_SIMP_TAC (srw_ss()) [SUBSET_DEF, fnsum_monotone, stdlam_monotone] THEN
  SIMP_TAC (srw_ss()) [congabs_f_def, stdlam_def, fnsum_def] THEN
  PROVE_TAC []);

val stdlam_beta = store_thm(
  "stdlam_beta",
  ``!thy. monotone thy ==>
          !x M N. ((LAM x M) @@ N, [N/x]M) IN lfp (stdlam ++ thy)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lfp_empty THEN
  ASM_SIMP_TAC (srw_ss()) [fnsum_monotone, stdlam_monotone, fnsum_def] THEN
  SIMP_TAC (srw_ss()) [beta_f_def, stdlam_def, fnsum_def] THEN PROVE_TAC []);

val lampair_ty = ``:'a nc # 'a nc``
val rel_ty = lampair_ty --> bool
val transform_ty = rel_ty --> rel_ty
val munge = INST_TYPE [beta |-> lampair_ty, alpha |-> rel_ty]
val ass = munge fnsum_ASSOC
val comm = munge fnsum_COMM
val fnsum_t = mk_const("fnsum", transform_ty --> transform_ty --> transform_ty)
fun prove_constituent_case th monoths = let
  (* th = equation of form const = f ++ g ++ h ++ i ++ ... *)
  fun leaves acc t =
      if length (#2 (strip_comb t)) > 0 then
        leaves (leaves acc (rand t)) (rand (rator t))
      else t::acc
  val rhs_leaves = leaves [] (rhs (concl th))
  fun mk(t1, t2) = list_mk_comb(fnsum_t, [t1, t2])
  fun listmk ac [] = ac
    | listmk ac (h::t) = listmk (mk(ac,h)) t
  fun mknew t others = let
    val r = listmk (hd others) (tl others)
  in
    mk(t,r)
  end
  fun one_instance t others = let
    val new_eq = TRANS th (EQT_ELIM
                             (AC_CONV(ass, comm)
                                     (mk_eq(rhs (concl th), mknew t others))))
  in
    prove(``lfp ^t SUBSET lfp ^(lhs (concl th))``,
          SUBST_ALL_TAC new_eq THEN
          PROVE_TAC (lfp_fnsum::fnsum_monotone::monoths))
  end

  fun recurse ts otherl =
      case ts of
        [] => []
      | (h::t) => one_instance h (tl otherl) ::
                  recurse t (tl otherl @ [h])
in
  recurse rhs_leaves rhs_leaves
end

val monoths = [beta_f_monotone, congl_f_monotone,
               congr_f_monotone, congabs_f_monotone, refl_f_monotone,
               sym_f_monotone, trans_f_monotone]
val constituents = prove_constituent_case stdlam_def monoths

val stdlam_lameq = store_thm(
  "stdlam_lameq",
  ``!M N. M == N = (M, N) IN lfp stdlam``,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    MAP_EVERY Q.ID_SPEC_TAC [`N`,`M`] THEN
    HO_MATCH_MP_TAC lam_eq_indn THEN REPEAT STRIP_TAC THENL [
      PROVE_TAC [stdlam_beta, empty_monotone, fnsum_empty],
      PROVE_TAC [stdlam_refl, empty_monotone, fnsum_empty],
      PROVE_TAC [stdlam_sym, empty_monotone, fnsum_empty],
      PROVE_TAC [stdlam_trans, empty_monotone, fnsum_empty],
      PROVE_TAC [stdlam_congl, empty_monotone, fnsum_empty],
      PROVE_TAC [stdlam_congr, empty_monotone, fnsum_empty],
      PROVE_TAC [stdlam_congabs, empty_monotone, fnsum_empty]
    ],

    Q_TAC SUFF_TAC `lfp stdlam SUBSET UNCURRY $==` THEN1
      SIMP_TAC std_ss [SUBSET_DEF, pairTheory.FORALL_PROD, SPECIFICATION] THEN
    Q_TAC SUFF_TAC `stdlam (UNCURRY $==) SUBSET UNCURRY $==` THEN1
      PROVE_TAC [lfp_induction, stdlam_monotone] THEN
    SIMP_TAC (srw_ss()) [SUBSET_DEF, pairTheory.FORALL_PROD,
                         stdlam_def, fnsum_def, beta_f_def,
                         congl_f_def, congr_f_def, congabs_f_def, refl_f_def,
                         sym_f_def, trans_f_def] THEN
    SRW_TAC [][SPECIFICATION] THEN PROVE_TAC [lam_eq_rules]
  ]);

val ext_f_def =
  Define`ext_f X = { (M,N) | ?x. (M @@ VAR x, N @@ VAR x) IN X /\
                                 ~(x IN FV (M @@ N)) }`;
val ext_f_monotone = store_thm(
  "ext_f_monotone",
  ``monotone ext_f``,
  SIMP_TAC (srw_ss()) [monotone_def, ext_f_def, SUBSET_DEF] THEN
  PROVE_TAC []);

val eta_f_def =
  Define`eta_f X = { (LAM x (M @@ VAR x), M) | ~(x IN FV M) }`;

val eta_f_monotone = store_thm(
  "eta_f_monotone",
  ``monotone eta_f``,
  SIMP_TAC std_ss [monotone_def, eta_f_def, SUBSET_DEF]);


val ext_eq_eta = store_thm(
  "ext_eq_eta",
  ``lfp (stdlam ++ ext_f) = lfp (stdlam ++ eta_f)``,
  `monotone (stdlam ++ ext_f)`
     by PROVE_TAC [stdlam_monotone, ext_f_monotone, fnsum_monotone] THEN
  `monotone (stdlam ++ eta_f)`
     by PROVE_TAC [stdlam_monotone, eta_f_monotone, fnsum_monotone] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [
    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP lfp_induction) THEN
    SIMP_TAC (srw_ss()) [SUBSET_DEF, fnsum_def, pairTheory.FORALL_PROD,
                         DISJ_IMP_THM, FORALL_AND_THM] THEN
    CONJ_TAC THENL [
      REPEAT STRIP_TAC THEN
      Q_TAC SUFF_TAC
        `(p_1,p_2) IN (stdlam ++ eta_f) (lfp (stdlam ++ eta_f))` THEN1
        PROVE_TAC [lfp_fixedpoint, stdlam_monotone, eta_f_monotone,
                   fnsum_monotone] THEN
      ASM_SIMP_TAC (srw_ss()) [fnsum_def],
      SIMP_TAC (srw_ss())[ext_f_def] THEN
      Q.X_GEN_TAC `M` THEN Q.X_GEN_TAC `N` THEN
      DISCH_THEN (Q.X_CHOOSE_THEN `x` STRIP_ASSUME_TAC) THEN
      `(LAM x (M @@ VAR x), LAM x (N @@ VAR x)) IN lfp (stdlam ++ eta_f)`
         by PROVE_TAC  [stdlam_congabs, eta_f_monotone] THEN
      `(LAM x (M @@ VAR x), M) IN lfp (stdlam ++ eta_f)` by
         (MATCH_MP_TAC lfp_empty THEN
          ASM_SIMP_TAC (srw_ss()) [fnsum_def, eta_f_def] THEN
          PROVE_TAC []) THEN
      POP_ASSUM (fn th =>
        `(M, LAM x (M @@ VAR x)) IN lfp (stdlam ++ eta_f)` by
         PROVE_TAC [eta_f_monotone, stdlam_sym, th]) THEN
      POP_ASSUM (fn th =>
        `(M, LAM x (N @@ VAR x)) IN lfp (stdlam ++ eta_f)` by
        PROVE_TAC [eta_f_monotone, stdlam_trans, th]) THEN
      `(LAM x (N @@ VAR x), N) IN lfp (stdlam ++ eta_f)` by
         (MATCH_MP_TAC lfp_empty THEN
          ASM_SIMP_TAC (srw_ss()) [fnsum_def, eta_f_def] THEN
          PROVE_TAC []) THEN
      PROVE_TAC [stdlam_trans, eta_f_monotone]
    ],

    FIRST_ASSUM (MATCH_MP_TAC o MATCH_MP lfp_induction) THEN
    SIMP_TAC (srw_ss()) [SUBSET_DEF, fnsum_def, pairTheory.FORALL_PROD,
                         DISJ_IMP_THM, FORALL_AND_THM] THEN
    CONJ_TAC THENL [
      REPEAT STRIP_TAC THEN
      Q_TAC SUFF_TAC
        `(p_1,p_2) IN (stdlam ++ ext_f) (lfp (stdlam ++ ext_f))` THEN1
        PROVE_TAC [lfp_fixedpoint, stdlam_monotone, fnsum_monotone,
                   ext_f_monotone] THEN
      ASM_SIMP_TAC std_ss [fnsum_def, IN_UNION],
      ASM_SIMP_TAC (srw_ss()) [eta_f_def, GSYM LEFT_FORALL_IMP_THM] THEN
      CONV_TAC (RENAME_VARS_CONV ["x", "y"]) THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC lfp_rule_applied THEN
      Q.EXISTS_TAC `{((LAM y (x @@ VAR y)) @@ VAR y, x @@ VAR y)}` THEN
      ASM_SIMP_TAC (srw_ss()) [SUBSET_DEF, fnsum_def] THEN
      CONJ_TAC THENL [
        Q_TAC SUFF_TAC `[VAR y/y](x @@ VAR y) = (x @@ VAR y)` THEN1
          PROVE_TAC [stdlam_beta, ext_f_monotone] THEN
        ASM_SIMP_TAC std_ss [lemma14b, SUB_THM],
        ASM_SIMP_TAC (srw_ss()) [ext_f_def] THEN
        PROVE_TAC []
      ]
    ]
  ]);

val lameta_eta_f = store_thm(
  "lameta_eta_f",
  ``!M N. (M,N) IN lfp (stdlam ++ eta_f) = lameta M N``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, FORALL_AND_THM] THEN CONJ_TAC THENL [
    Q_TAC SUFF_TAC `lfp (stdlam ++ eta_f) SUBSET {(M,N) | lameta M N}` THEN1
          (SRW_TAC [][pred_setTheory.SUBSET_DEF] THEN RES_TAC THEN
           FULL_SIMP_TAC (srw_ss()) []) THEN
    Q_TAC SUFF_TAC `(stdlam ++ eta_f) { (M,N) | lameta M N } SUBSET
                    { (M,N) | lameta M N}` THEN1
       PROVE_TAC [lfp_induction, stdlam_monotone, fnsum_monotone,
                  eta_f_monotone] THEN
    SIMP_TAC (srw_ss()) [pred_setTheory.SUBSET_DEF, fnsum_def,
                         pairTheory.FORALL_PROD, stdlam_def,
                         beta_f_def, congl_f_def, congr_f_def, congabs_f_def,
                         refl_f_def, sym_f_def, trans_f_def,
                         DISJ_IMP_THM, FORALL_AND_THM,
                         GSYM LEFT_FORALL_IMP_THM, eta_f_def] THEN
    PROVE_TAC [lameta_rules],
    HO_MATCH_MP_TAC lameta_ind THEN REPEAT STRIP_TAC THENL [
      PROVE_TAC [stdlam_beta, fnsum_monotone, eta_f_monotone],
      PROVE_TAC [stdlam_refl, fnsum_monotone, eta_f_monotone],
      PROVE_TAC [stdlam_sym, fnsum_monotone, eta_f_monotone],
      PROVE_TAC [stdlam_trans, fnsum_monotone, eta_f_monotone],
      PROVE_TAC [stdlam_congl, fnsum_monotone, eta_f_monotone],
      PROVE_TAC [stdlam_congr, fnsum_monotone, eta_f_monotone],
      PROVE_TAC [stdlam_congabs, fnsum_monotone, eta_f_monotone],
      MATCH_MP_TAC lfp_empty THEN
      SRW_TAC [][fnsum_monotone, stdlam_monotone, eta_f_monotone, fnsum_def,
                 eta_f_def] THEN PROVE_TAC []
    ]
  ]);

val consistent_def =
    Define`consistent (thy:'a nc -> 'a nc -> bool) = ?M N. ~thy M N`;

val eqn_thy_def =
    Define`eqn_thy p = \X:'a termset. {p}:'a termset`;

val eqn_thy_monotone = store_thm(
  "eqn_thy_monotone",
  ``!p. monotone (eqn_thy p)``,
  REWRITE_TAC [eqn_thy_def, monotone_def, SUBSET_REFL]);

val stdlam_eqn_thy = store_thm(
  "stdlam_eqn_thy",
  ``!p. p IN lfp (stdlam ++ eqn_thy p)``,
  GEN_TAC THEN MATCH_MP_TAC lfp_empty THEN
  CONJ_TAC THENL [
    PROVE_TAC [stdlam_monotone, eqn_thy_monotone, fnsum_monotone],
    SIMP_TAC std_ss [fnsum_def, eqn_thy_def, IN_UNION, IN_SING]
  ]);

val incompatible_def =
    Define`incompatible x y =
                ~consistent (CURRY (lfp (stdlam ++ eqn_thy (x,y))))`;

val S_def =
    Define`S = LAM "x" (LAM "y" (LAM "z"
                                     ((VAR "x" @@ VAR "z") @@
                                      (VAR "y" @@ VAR "z"))))`;
val K_def = Define`K = LAM "x" (LAM "y" (VAR "x"))`;
val I_def = Define`I = LAM "x" (VAR "x")`;

val omega_def =
    Define`omega = (LAM "x" (VAR "x" @@ VAR "x")) @@
                     (LAM "x" (VAR "x" @@ VAR "x"))`

val SUB_LAM_RWT = store_thm(
  "SUB_LAM_RWT",
  ``!x y v body. [x/y] (LAM v body) =
                 let n = NEW (y INSERT FV x UNION FV body)
                 in
                   LAM n ([x/y]([VAR n/v] body))``,
  SIMP_TAC std_ss [] THEN REPEAT GEN_TAC THEN
  Q_TAC (NEW_TAC "n") `y INSERT FV x UNION FV body` THEN
  Cases_on `y = v` THENL [
    POP_ASSUM SUBST_ALL_TAC THEN Cases_on `v IN FV body` THENL [
      SRW_TAC [][SUB_THM, lemma14b, SUB_TWICE_ONE_VAR, ALPHA],
      ASM_SIMP_TAC std_ss [SUB_THM, lemma14b] THEN
      MATCH_MP_TAC INJECTIVITY_LEMMA3 THEN Q.EXISTS_TAC `n` THEN
      ASM_SIMP_TAC std_ss [lemma14b, lemma14a]
    ],
    `LAM v body = LAM n ([VAR n/v] body)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    ASM_SIMP_TAC std_ss [SUB_THM]
  ]);

val alpha_lemma = prove(
  ``!x y u body.
       ~(y IN FV (LAM x u)) /\ (body = [VAR y/x]u) ==>
       (LAM x u = LAM y body)``,
  PROVE_TAC [ALPHA]);

val stdlam_S = store_thm(
  "stdlam_S",
  ``!thy. monotone thy ==>
          !A B C. (S @@ A @@ B @@ C, (A @@ C) @@ (B @@ C)) IN
                     lfp (stdlam ++ thy)``,
  REPEAT STRIP_TAC THEN
  Q_TAC (NEW_TAC "y") `{"x"; "y"; "z"} UNION FV A UNION FV B UNION FV C` THEN
  Q_TAC (NEW_TAC "z")
        `{y; "x"; "y"; "z"} UNION FV A UNION FV B UNION FV C` THEN
  Q.ABBREV_TAC `S1 = LAM y (LAM z ((A @@ VAR z) @@ (VAR y @@ VAR z)))` THEN
  `(S @@ A, S1) IN lfp (stdlam ++ thy)` by
     (Q_TAC SUFF_TAC `?x M. (S = LAM x M) /\ (S1 = [A/x]M)` THEN1
        PROVE_TAC [stdlam_beta] THEN
      Q.EXISTS_TAC `"x"` THEN SIMP_TAC std_ss [S_def] THEN
      `LAM "y" (LAM "z" ((VAR "x" @@ VAR "z") @@ (VAR "y" @@ VAR "z"))) =
       LAM y (LAM z ((VAR "x" @@ VAR z) @@ (VAR y @@ VAR z)))` by
         ASM_SIMP_TAC (srw_ss()) [SUB_THM, stringTheory.CHR_11,
                                  stringTheory.STRING_11, alpha_lemma] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      ASM_SIMP_TAC (srw_ss()) [SUB_THM, stringTheory.STRING_11,
                               stringTheory.CHR_11]) THEN
  `(S @@ A @@ B @@ C, S1 @@ B @@ C) IN lfp (stdlam ++ thy)` by
     PROVE_TAC [stdlam_congl] THEN
  Q_TAC SUFF_TAC `(S1 @@ B @@ C, A @@ C @@ (B @@ C)) IN lfp(stdlam++thy)` THEN1
    PROVE_TAC [stdlam_trans] THEN
  Q.ABBREV_TAC `S2 = LAM z (A @@ VAR z @@ (B @@ VAR z))` THEN
  `(S1 @@ B, S2) IN lfp (stdlam ++ thy)` by
     (Q_TAC SUFF_TAC `?M. (S1 = LAM y M) /\ (S2 = [B/y]M)` THEN1
        PROVE_TAC [stdlam_beta] THEN
      NTAC 2 (FIRST_X_ASSUM (SUBST_ALL_TAC o SYM)) THEN
      ASM_SIMP_TAC (srw_ss()) [SUB_THM, stringTheory.CHR_11,
                               stringTheory.STRING_11, alpha_lemma,
                               lemma14b]) THEN
  Q_TAC SUFF_TAC `(S2 @@ C, A @@ C @@ (B @@ C)) IN lfp (stdlam ++ thy)` THEN1
      PROVE_TAC [stdlam_trans, stdlam_congl] THEN
  Q_TAC SUFF_TAC `?M. (S2 = LAM z M) /\ (A @@ C @@ (B @@ C) = [C/z]M)` THEN1
      PROVE_TAC [stdlam_beta] THEN
  NTAC 2 (FIRST_X_ASSUM (SUBST_ALL_TAC o SYM)) THEN
  ASM_SIMP_TAC (srw_ss()) [SUB_THM, stringTheory.CHR_11,
                           stringTheory.STRING_11, alpha_lemma,
                           lemma14b]);

val stdlam_K = store_thm(
  "stdlam_K",
  ``!thy. monotone thy ==>
          !A B. (K @@ A @@ B, A) IN lfp (stdlam ++ thy)``,
  REPEAT STRIP_TAC THEN
  Q_TAC (NEW_TAC "x") `{"x"; "y"} UNION FV A UNION FV B` THEN
  Q_TAC (NEW_TAC "y") `{x; "x"; "y"} UNION FV A UNION FV B` THEN
  `K = LAM x (LAM y (VAR x))` by
      (ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
       ASM_SIMP_TAC std_ss [alpha_lemma, K_def, SUB_THM, FV_THM,
                            IN_SING, IN_DELETE, stringTheory.STRING_11,
                            stringTheory.CHR_11]) THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  Q_TAC SUFF_TAC
    `(LAM x (LAM y (VAR x)) @@ A @@ B, (LAM y A) @@ B) IN lfp (stdlam ++ thy)
        /\
     (LAM y A @@ B, A) IN lfp (stdlam ++ thy)`
    THEN1 PROVE_TAC [stdlam_trans] THEN
  CONJ_TAC THENL [
    Q_TAC SUFF_TAC `[A/x](LAM y (VAR x)) = LAM y A` THEN1
      PROVE_TAC [stdlam_beta, stdlam_congl] THEN
    ASM_SIMP_TAC std_ss [FV_THM, SUB_THM],
    Q_TAC SUFF_TAC `[B/y]A = A` THEN1 PROVE_TAC [stdlam_beta] THEN
    ASM_SIMP_TAC std_ss [lemma14b]
  ]);

val stdlam_I = store_thm(
  "stdlam_I",
  ``!thy. monotone thy ==> !A. (I @@ A, A) IN lfp (stdlam ++ thy)``,
  PROVE_TAC [stdlam_beta, I_def, SUB_THM]);

val FV_I = store_thm(
  "FV_I",
  ``FV I = {}``,
  SIMP_TAC std_ss [FV_THM, IN_DELETE, I_def, EXTENSION, NOT_IN_EMPTY,
                   IN_SING]);

val SK_incompatible = store_thm( (* example 2.18, p23 *)
  "SK_incompatible",
  ``incompatible S K``,
  Q_TAC SUFF_TAC `!M N. (M,N) IN lfp (stdlam ++ eqn_thy (S,K))` THEN1
        SRW_TAC [][SPECIFICATION, incompatible_def, consistent_def] THEN
  REPEAT GEN_TAC THEN
  `(S,K) IN lfp (stdlam ++ eqn_thy (S,K))` by PROVE_TAC [stdlam_eqn_thy] THEN
  `!D. (S @@ I @@ (K @@ D) @@ I, K @@ I @@ (K @@ D) @@ I) IN
          lfp (stdlam ++ eqn_thy (S,K))` by
      PROVE_TAC [stdlam_congl, eqn_thy_monotone] THEN
  `!D. (S @@ I @@ (K @@ D) @@ I, I) IN lfp (stdlam ++ eqn_thy(S,K))` by
      PROVE_TAC [stdlam_K, stdlam_congl, eqn_thy_monotone, stdlam_trans,
                 stdlam_I] THEN
  `!D. ((I @@ I) @@ (K @@ D @@ I), I) IN lfp (stdlam ++ eqn_thy(S,K))` by
      PROVE_TAC [stdlam_S, eqn_thy_monotone, stdlam_trans, stdlam_sym] THEN
  `!D. (D, I) IN lfp (stdlam ++ eqn_thy(S,K))` by
      PROVE_TAC [stdlam_I, stdlam_K, eqn_thy_monotone, stdlam_trans,
                 stdlam_sym, stdlam_congl] THEN
  PROVE_TAC [stdlam_trans, stdlam_sym, eqn_thy_monotone]);

val xx_xy_incompatible = store_thm( (* example 2.20, p24 *)
  "xx_xy_incompatible",
  ``~(x = y) ==> incompatible (VAR x @@ VAR x) (VAR x @@ VAR y)``,
  STRIP_TAC THEN
  Q_TAC SUFF_TAC
        `!M N.
            (M,N) IN lfp (stdlam ++ eqn_thy (VAR x @@ VAR x, VAR x @@ VAR y))`
        THEN1 SIMP_TAC std_ss [incompatible_def, consistent_def,
                               SPECIFICATION] THEN
  REPEAT GEN_TAC THEN
  Q.ABBREV_TAC `xx_xy = eqn_thy (VAR x @@ VAR x, VAR x @@ VAR y)` THEN
  `monotone xx_xy` by PROVE_TAC [eqn_thy_monotone] THEN
  `(VAR x @@ VAR x, VAR x @@ VAR y) IN lfp (stdlam ++ xx_xy)` by
     PROVE_TAC [stdlam_eqn_thy] THEN
  `(LAM x (LAM y (VAR x @@ VAR x)), LAM x (LAM y (VAR x @@ VAR y))) IN
     lfp (stdlam ++ xx_xy)` by PROVE_TAC [stdlam_congabs] THEN
  `((LAM x (LAM y (VAR x @@ VAR x))) @@ I,
    (LAM x (LAM y (VAR x @@ VAR y))) @@ I) IN lfp (stdlam ++ xx_xy)` by
     PROVE_TAC [stdlam_congl] THEN
  `(LAM y (I @@ I), (LAM x (LAM y (VAR x @@ VAR x))) @@ I) IN
     lfp (stdlam ++ xx_xy)` by
     (Q_TAC SUFF_TAC `[I/x] (LAM y (VAR x @@ VAR x)) = LAM y (I @@ I)` THEN1
        PROVE_TAC [stdlam_sym, stdlam_beta] THEN
      ASM_SIMP_TAC std_ss [SUB_THM, FV_I, NOT_IN_EMPTY]) THEN
  `(LAM y I, (LAM x (LAM y (VAR x @@ VAR y))) @@ I) IN lfp (stdlam ++ xx_xy)`
     by PROVE_TAC [stdlam_trans, stdlam_I, stdlam_congabs, stdlam_sym] THEN
  `[I/x](LAM y (VAR x @@ VAR y)) = LAM y (I @@ VAR y)` by
      ASM_SIMP_TAC (srw_ss()) [SUB_THM, FV_I] THEN
  `(LAM x (LAM y (VAR x @@ VAR y)) @@ I, LAM y (I @@ VAR y))
      IN lfp (stdlam ++ xx_xy)` by PROVE_TAC [stdlam_beta] THEN
  `(LAM y (I @@ VAR y), LAM y I) IN lfp (stdlam ++ xx_xy)` by
      PROVE_TAC [stdlam_trans, stdlam_sym] THEN
  `(LAM y (VAR y), LAM y I) IN lfp (stdlam ++ xx_xy)` by
      PROVE_TAC [stdlam_congabs, stdlam_I, stdlam_trans, stdlam_sym] THEN
  `!D. ((LAM y (VAR y)) @@ D, (LAM y I) @@ D) IN lfp (stdlam ++ xx_xy)` by
      PROVE_TAC [stdlam_congl] THEN
  `!D. [D/y](VAR y) = D` by SRW_TAC [][SUB_THM] THEN
  `!D. (D, (LAM y I) @@ D) IN lfp (stdlam ++ xx_xy)` by
      PROVE_TAC [stdlam_beta, stdlam_trans, stdlam_sym] THEN
  `!D. [D/y]I = I` by SRW_TAC [][lemma14b, FV_I] THEN
  `!D. (D, I) IN lfp (stdlam ++ xx_xy)` by
      PROVE_TAC [stdlam_beta, stdlam_trans, stdlam_sym] THEN
  PROVE_TAC [stdlam_trans, stdlam_sym]);


val (is_abs_thm, _) = define_recursive_term_function
  `(is_abs (VAR s) = F) /\
   (is_abs (CON k) = F) /\
   (is_abs (t1 @@ t2) = F) /\
   (is_abs (LAM v t) = T)`;
val _ = export_rewrites ["is_abs_thm"]
val _ = prove_vsubst_result is_abs_thm NONE

val (is_comb_thm, _) = define_recursive_term_function
  `(is_comb (VAR s) = F) /\
   (is_comb (CON k) = F) /\
   (is_comb (t1 @@ t2) = T) /\
   (is_comb (LAM v t) = F)`;
val _ = export_rewrites ["is_comb_thm"]
val _ = prove_vsubst_result is_comb_thm NONE

val (is_var_thm, _) = define_recursive_term_function
  `(is_var (VAR s) = T) /\
   (is_var (CON k) = F) /\
   (is_var (t1 @@ t2) = F) /\
   (is_var (LAM v t) = F)`;
val _ = export_rewrites ["is_var_thm"]
val _ = prove_vsubst_result is_var_thm NONE

val (is_const_thm,_) = define_recursive_term_function
  `(is_const (VAR s) = F) /\
   (is_const (CON k) = T) /\
   (is_const (t @@ u) = F) /\
   (is_const (LAM v t) = F)`;
val _ = export_rewrites ["is_const_thm"]
val _ = prove_vsubst_result is_const_thm NONE

val (dest_const_thm, _) =
    define_recursive_term_function `dest_const (CON k:'a nc) = k`;
val _ = export_rewrites ["dest_const_thm"]

val (bnf_thm, _) = define_recursive_term_function
  `(bnf (VAR s) = T) /\
   (bnf (CON k) = T) /\
   (bnf (t1 @@ t2) = bnf t1 /\ bnf t2 /\ ~is_abs t1) /\
   (bnf (LAM v t) = bnf t)`;
val _ = export_rewrites ["bnf_thm"]
val _ = prove_vsubst_result bnf_thm NONE

val (rand_thm, _) = define_recursive_term_function `rand (t1 @@ t2) = t2`;
val _ = export_rewrites ["rand_thm"]

val (rator_thm, _) = define_recursive_term_function `rator (t1 @@ t2) = t1`;
val _ = export_rewrites ["rator_thm"]

val swap_is_const2 = store_thm(
  "swap_is_const2",
  ``is_const t ==> (swap x y t = t)``,
  Q.SPEC_THEN `t` STRUCT_CASES_TAC nc_CASES THEN
  SRW_TAC [][swap_thm, is_const_thm]);

val is_comb_APP_EXISTS = store_thm(
  "is_comb_APP_EXISTS",
  ``!t. is_comb t = (?u v. t = u @@ v)``,
  PROVE_TAC [nc_CASES, is_comb_thm]);

val is_comb_rator_rand = store_thm(
  "is_comb_rator_rand",
  ``!t. is_comb t ==> (rator t @@ rand t = t)``,
  SIMP_TAC (srw_ss()) [is_comb_APP_EXISTS, GSYM LEFT_FORALL_IMP_THM,
                       rator_thm, rand_thm]);

val rand_subst_commutes = store_thm(
  "rand_subst_commutes",
  ``!t u v. is_comb t ==> ([u/v] (rand t) = rand ([u/v] t))``,
  REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [is_comb_APP_EXISTS, SUB_THM, rand_thm]);

val rator_subst_commutes = store_thm(
  "rator_subst_commutes",
  ``!t u x. is_comb t ==> ([u/v] (rator t) = rator ([u/v] t))``,
  SRW_TAC [][is_comb_APP_EXISTS, rator_thm, SUB_THM] THEN
  SRW_TAC [][is_comb_APP_EXISTS, rator_thm, SUB_THM]);


val extra_LAM_DISJOINT = store_thm(
  "extra_LAM_DISJOINT",
  ``(!t v u b t1 t2. ~(t1 @@ t2 = [t/v] (LAM u b))) /\
    (!R u b t1 t2.   ~(t1 @@ t2 = (LAM u b) ISUB R)) /\
    (!t v u b s.     ~(VAR s = [t/v] (LAM u b))) /\
    (!R u b s.       ~(VAR s = (LAM u b) ISUB R))``,
  REPEAT (GEN_TAC ORELSE CONJ_TAC) THENL [
    Q_TAC (NEW_TAC "z") `{u;v} UNION FV t UNION FV b`,
    Q_TAC (NEW_TAC "z") `{u} UNION DOM R UNION FV b UNION FVS R`,
    Q_TAC (NEW_TAC "z") `{s;u;v} UNION FV b UNION FV t`,
    Q_TAC (NEW_TAC "z") `{s;u} UNION DOM R UNION FV b UNION FVS R`
  ] THEN
  `LAM u b = LAM z ([VAR z/u] b)` by SRW_TAC [][SIMPLE_ALPHA] THEN
  SRW_TAC [][SUB_THM, ISUB_LAM]);
val _ = export_rewrites ["extra_LAM_DISJOINT"]

val (enf_thm, _) = define_recursive_term_function
  `(enf (VAR s) = T) /\
   (enf (CON k) = T) /\
   (enf (t @@ u) = enf t /\ enf u) /\
   (enf (LAM v t) = enf t /\ (is_comb t /\ (rand t = VAR v) ==>
                              v IN FV (rator t)))`
val _ = export_rewrites ["enf_thm"]

val swap_eq_var = store_thm(
  "swap_eq_var",
  ``(swap x y t = VAR s) = (t = VAR (swapstr x y s))``,
  Q.SPEC_THEN `t` STRUCT_CASES_TAC nc_CASES THEN
  SRW_TAC [][swap_thm]);

val subst_eq_var = store_thm(
  "subst_eq_var",
  ``([v/u] t = VAR s) = (t = VAR u) /\ (v = VAR s) \/
                        (t = VAR s) /\ ~(u = s)``,
  Q.SPEC_THEN `t` STRUCT_CASES_TAC nc_CASES THEN
  SRW_TAC [][SUB_VAR, SUB_THM] THEN PROVE_TAC []);

val enf_vsubst_invariant = store_thm(
  "enf_vsubst_invariant",
  ``!t v u. enf ([VAR v/u] t) = enf t``,
  HO_MATCH_MP_TAC simple_induction THEN
  SIMP_TAC (srw_ss()) [SUB_THM, enf_thm] THEN CONJ_TAC THENL [
    SRW_TAC [][enf_thm, SUB_VAR],
    MAP_EVERY Q.X_GEN_TAC [`x`, `t`] THEN STRIP_TAC THEN
    MAP_EVERY Q.X_GEN_TAC [`v`, `u`] THEN
    Q_TAC (NEW_TAC "z") `{u;v;x} UNION FV t` THEN
    `LAM x t = LAM z (swap z x t)` by SRW_TAC [][swap_ALPHA] THEN
    SRW_TAC [][SUB_THM, enf_thm, swap_subst_out, swap_thm, swap_eq_var] THEN
    `~(swapstr z x v = x)` by SRW_TAC [][swapstr_def] THEN
    `~(swapstr z x u = x)` by SRW_TAC [][swapstr_def] THEN
    SRW_TAC [boolSimps.CONJ_ss][GSYM rand_subst_commutes, subst_eq_var] THEN
    SRW_TAC [][GSYM rator_subst_commutes, FV_SUB]
  ]);
val _ = export_rewrites ["enf_vsubst_invariant"]

val FV_RENAMING = store_thm(
  "FV_RENAMING",
  ``!R. RENAMING R ==>
        !t. FV (t ISUB R) = IMAGE (RENAME R) (FV t)``,
  HO_MATCH_MP_TAC RENAMING_ind THEN
  SRW_TAC [][RENAME_def, VNAME_DEF, EXTENSION, ISUB_def] THEN EQ_TAC THEN
  SRW_TAC [][FV_SUB] THEN PROVE_TAC []);

val benf_def = Define`benf t = bnf t /\ enf t`;

val I_beta_normal = store_thm(
  "I_beta_normal",
  ``bnf I``,
  SRW_TAC [][I_def, bnf_thm]);
val K_beta_normal = store_thm(
  "K_beta_normal",
  ``bnf K``,
  SRW_TAC [][K_def, bnf_thm]);
val S_beta_normal = store_thm(
  "S_beta_normal",
  ``bnf S``,
  SRW_TAC [][S_def, bnf_thm, is_abs_thm]);

val has_bnf_def = Define`has_bnf t = ?t'. t == t' /\ bnf t'`;

val has_benf_def = Define`has_benf t = ?t'. t == t' /\ benf t'`;


val _ = export_theory()
