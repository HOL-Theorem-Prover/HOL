structure chap2Script =
struct

open HolKernel Parse boolLib

open bossLib binderLib

open pred_setTheory pred_setLib
open termTheory BasicProvers

val _ = augment_srw_ss [rewrites [LET_THM]]
val std_ss = std_ss ++ rewrites [LET_THM]

fun Store_Thm(s, t, tac) = (store_thm(s,t,tac) before
                            export_rewrites [s])

structure Q = struct open Q open OldAbbrevTactics end;

val export_rewrites = export_rewrites "chap2";

val _ = new_theory "chap2";

val (ctxt_rules, ctxt_indn, ctxt_cases) =  (* p. 10 *)
  Hol_reln`(!s. ctxt (\x. VAR s))                       /\
           ctxt (\x. x)                                 /\
           (!c1 c2. ctxt c1 /\ ctxt c2 ==>
                    ctxt (\x. c1 x @@ c2 x))            /\
           (!v c.   ctxt c ==> ctxt (\x. LAM v (c x)))`;

val constant_contexts_exist = store_thm(
  "constant_contexts_exist",
  ``!t. ctxt (\x. t)``,
  HO_MATCH_MP_TAC simple_induction THEN REPEAT STRIP_TAC THEN
  SRW_TAC [][ctxt_rules]);

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
  ASM_SIMP_TAC (srw_ss())[SUB_THM, lemma14b, lam_eq_rules]);

(* properties of substitution - p19 *)

val SUB_TWICE_ONE_VAR = store_thm(
  "SUB_TWICE_ONE_VAR",
  ``!body. [x/v] ([y/v] body) = [[x/v]y / v] body``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN SRW_TAC [][SUB_THM, SUB_VAR] THEN
  Q.EXISTS_TAC `v INSERT FV x UNION FV y` THEN
  SRW_TAC [][SUB_THM] THEN
  Cases_on `v IN FV y` THEN SRW_TAC [][SUB_THM, lemma14c, lemma14b]);

val lemma2_11 = store_thm(
  "lemma2_11",
  ``!t. ~(v = u)  /\ ~(v IN FV M) ==>
        ([M/u] ([N/v] t) = [[M/u]N/v] ([M/u] t))``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `{u;v} UNION FV M UNION FV N` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, lemma14b] THEN
  Cases_on `u IN FV N` THEN SRW_TAC [][SUB_THM, lemma14b, lemma14c]);

val substitution_lemma = save_thm("substitution_lemma", lemma2_11);

val NOT_IN_FV_SUB = store_thm(
  "NOT_IN_FV_SUB",
  ``!x t u v. ~(x IN FV u) /\ ~(x IN FV t) ==> ~(x IN FV ([t/v]u))``,
  SRW_TAC [][FV_SUB]);


val lemma2_12 = store_thm( (* p. 19 *)
  "lemma2_12",
  ``(M == M' ==> [N/x]M == [N/x]M') /\
    (N == N' ==> [N/x]M == [N'/x]M) /\
    (M == M' /\ N == N' ==> [N/x]M == [N'/x]M')``,
  Q.SUBGOAL_THEN `(!M M'. M == M' ==> !N x. [N/x]M == [N/x]M') /\
                  (!N N'. N == N' ==> !M x. [N/x]M == [N'/x]M)`
     (fn th => STRIP_ASSUME_TAC th THEN SRW_TAC[][])
  THENL [
    CONJ_TAC THENL [
      REPEAT STRIP_TAC THEN
      `LAM x M == LAM x M'` by PROVE_TAC [lam_eq_rules] THEN
      `LAM x M @@ N == LAM x M' @@ N` by PROVE_TAC [lam_eq_rules] THEN
      PROVE_TAC [lam_eq_rules],
      Q_TAC SUFF_TAC `!N N' x M. N == N' ==> [N/x] M == [N'/x]M` THEN1
        SRW_TAC [][] THEN
      NTAC 3 GEN_TAC THEN HO_MATCH_MP_TAC nc_INDUCTION2 THEN
      Q.EXISTS_TAC `x INSERT FV N UNION FV N'` THEN
      SRW_TAC [][SUB_THM, SUB_VAR] THEN PROVE_TAC [lam_eq_rules]
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

val consistent_def =
    Define`consistent (thy:term -> term -> bool) = ?M N. ~thy M N`;

val (asmlam_rules, asmlam_ind, asmlam_cases) = Hol_reln`
  (!M N. (M,N) IN eqns ==> asmlam eqns M N) /\
  (!x M N. asmlam eqns (LAM x M @@ N) ([N/x]M)) /\
  (!M. asmlam eqns M M) /\
  (!M N. asmlam eqns M N ==> asmlam eqns N M) /\
  (!M N P. asmlam eqns M N /\ asmlam eqns N P ==> asmlam eqns M P) /\
  (!M M' N. asmlam eqns M M' ==> asmlam eqns (M @@ N) (M' @@ N)) /\
  (!M N N'. asmlam eqns N N' ==> asmlam eqns (M @@ N) (M @@ N')) /\
  (!x M M'. asmlam eqns M M' ==> asmlam eqns (LAM x M) (LAM x M'))
`;

val incompatible_def =
    Define`incompatible x y = ~consistent (asmlam {(x,y)})`

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
  NEW_ELIM_TAC THEN Q.X_GEN_TAC `z` THEN
  Q_TAC (NEW_TAC "n") `{z;y} UNION FV x UNION FV body` THEN
  REPEAT STRIP_TAC THEN
  `LAM v body = LAM z ([VAR z/v] body)` by SRW_TAC [][SIMPLE_ALPHA] THEN
  SRW_TAC [][SUB_THM]);

val alpha_lemma = prove(
  ``!x y u body.
       ~(y IN FV (LAM x u)) /\ (body = [VAR y/x]u) ==>
       (LAM x u = LAM y body)``,
  SRW_TAC [][] THEN SRW_TAC [][SIMPLE_ALPHA]);

val lameq_asmlam = store_thm(
  "lameq_asmlam",
  ``!M N. M == N ==> asmlam eqns M N``,
  HO_MATCH_MP_TAC lam_eq_indn THEN METIS_TAC [asmlam_rules]);

val lameq_S = store_thm(
  "lameq_S",
  ``S @@ A @@ B @@ C == (A @@ C) @@ (B @@ C)``,
  Q_TAC (NEW_TAC "y") `{"x"; "y"; "z"} UNION FV A UNION FV B UNION FV C` THEN
  Q_TAC (NEW_TAC "z")
        `{y; "x"; "y"; "z"} UNION FV A UNION FV B UNION FV C` THEN
  Q.ABBREV_TAC `S1 = LAM y (LAM z ((A @@ VAR z) @@ (VAR y @@ VAR z)))` THEN
  `S @@ A == S1`
     by (Q_TAC SUFF_TAC `?x M. (S = LAM x M) /\ (S1 = [A/x]M)` THEN1
           PROVE_TAC [lam_eq_rules] THEN
         Q.EXISTS_TAC `"x"` THEN SRW_TAC [][S_def] THEN
        `LAM "y" (LAM "z" ((VAR "x" @@ VAR "z") @@ (VAR "y" @@ VAR "z"))) =
         LAM y (LAM z ((VAR "x" @@ VAR z) @@ (VAR y @@ VAR z)))` by
           ASM_SIMP_TAC (srw_ss()) [SUB_THM, alpha_lemma] THEN
        POP_ASSUM SUBST_ALL_TAC THEN
        ASM_SIMP_TAC (srw_ss()) [SUB_THM]) THEN
  `S @@ A @@ B @@ C == S1 @@ B @@ C` by PROVE_TAC [lam_eq_rules] THEN
  Q_TAC SUFF_TAC `S1 @@ B @@ C == A @@ C @@ (B @@ C)` THEN1
    PROVE_TAC [lam_eq_rules] THEN
  Q.ABBREV_TAC `S2 = LAM z (A @@ VAR z @@ (B @@ VAR z))` THEN
  `S1 @@ B == S2` by
     (Q_TAC SUFF_TAC `?M. (S1 = LAM y M) /\ (S2 = [B/y]M)` THEN1
        PROVE_TAC [lam_eq_rules] THEN
      NTAC 2 (FIRST_X_ASSUM (SUBST_ALL_TAC o SYM)) THEN
      ASM_SIMP_TAC (srw_ss()) [SUB_THM, alpha_lemma, lemma14b]) THEN
  Q_TAC SUFF_TAC `S2 @@ C == A @@ C @@ (B @@ C)` THEN1
      PROVE_TAC [lam_eq_rules] THEN
  Q_TAC SUFF_TAC `?M. (S2 = LAM z M) /\ (A @@ C @@ (B @@ C) = [C/z]M)` THEN1
      PROVE_TAC [lam_eq_rules] THEN
  NTAC 2 (FIRST_X_ASSUM (SUBST_ALL_TAC o SYM)) THEN
  ASM_SIMP_TAC (srw_ss()) [SUB_THM, alpha_lemma, lemma14b]);

val lameq_K = store_thm(
  "lameq_K",
  ``K @@ A @@ B == A``,
  Q_TAC (NEW_TAC "x") `{"x"; "y"} UNION FV A UNION FV B` THEN
  Q_TAC (NEW_TAC "y") `{x; "x"; "y"} UNION FV A UNION FV B` THEN
  `K = LAM x (LAM y (VAR x))`
     by SRW_TAC [][K_def, LAM_eq_thm, basic_swapTheory.swapstr_def,
                   stringTheory.CHR_11] THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  Q_TAC SUFF_TAC
    `LAM x (LAM y (VAR x)) @@ A @@ B == (LAM y A) @@ B
        /\
     LAM y A @@ B == A`
    THEN1 PROVE_TAC [lam_eq_rules] THEN
  CONJ_TAC THENL [
    Q_TAC SUFF_TAC `[A/x](LAM y (VAR x)) = LAM y A` THEN1
      PROVE_TAC [lam_eq_rules] THEN
    ASM_SIMP_TAC std_ss [SUB_THM],
    Q_TAC SUFF_TAC `[B/y]A = A` THEN1 PROVE_TAC [lam_eq_rules] THEN
    ASM_SIMP_TAC std_ss [lemma14b]
  ]);

val lameq_I = store_thm(
  "lameq_I",
  ``I @@ A == A``,
  PROVE_TAC [lam_eq_rules, I_def, SUB_THM]);

val FV_I = store_thm("FV_I", ``FV I = {}``, SRW_TAC [][I_def]);

val SK_incompatible = store_thm( (* example 2.18, p23 *)
  "SK_incompatible",
  ``incompatible S K``,
  Q_TAC SUFF_TAC `!M N. asmlam {(S,K)} M N`
        THEN1 SRW_TAC [][incompatible_def, consistent_def] THEN
  REPEAT GEN_TAC THEN
  `asmlam {(S,K)} S K` by PROVE_TAC [asmlam_rules, IN_INSERT] THEN
  `!D. asmlam {(S,K)} (S @@ I @@ (K @@ D) @@ I) (K @@ I @@ (K @@ D) @@ I)`
      by PROVE_TAC [asmlam_rules] THEN
  `!D. asmlam {(S,K)} (S @@ I @@ (K @@ D) @@ I) I`
      by PROVE_TAC [lameq_K, asmlam_rules, lameq_asmlam, lameq_I] THEN
  `!D. asmlam {(S,K)} ((I @@ I) @@ (K @@ D @@ I)) I`
      by PROVE_TAC [lameq_S, asmlam_rules, lameq_asmlam] THEN
  `!D. asmlam {(S,K)} D I`
      by PROVE_TAC [lameq_I, lameq_K, asmlam_rules, lameq_asmlam] THEN
  PROVE_TAC [asmlam_rules]);

val [asmlam_eqn, asmlam_beta, asmlam_refl, asmlam_sym, asmlam_trans,
     asmlam_lcong, asmlam_rcong, asmlam_abscong] =
    CONJUNCTS (SPEC_ALL asmlam_rules)

val xx_xy_incompatible = store_thm( (* example 2.20, p24 *)
  "xx_xy_incompatible",
  ``~(x = y) ==> incompatible (VAR x @@ VAR x) (VAR x @@ VAR y)``,
  STRIP_TAC THEN
  Q_TAC SUFF_TAC
        `!M N.
            asmlam {(VAR x @@ VAR x, VAR x @@ VAR y)} M N`
        THEN1 SIMP_TAC std_ss [incompatible_def, consistent_def] THEN
  REPEAT GEN_TAC THEN
  Q.ABBREV_TAC `xx_xy = asmlam {(VAR x @@ VAR x, VAR x @@ VAR y)}` THEN
  `xx_xy (VAR x @@ VAR x) (VAR x @@ VAR y)`
     by PROVE_TAC [asmlam_rules, IN_INSERT] THEN
  `xx_xy (LAM x (LAM y (VAR x @@ VAR x))) (LAM x (LAM y (VAR x @@ VAR y)))`
     by PROVE_TAC [asmlam_rules] THEN
  `xx_xy ((LAM x (LAM y (VAR x @@ VAR x))) @@ I)
         ((LAM x (LAM y (VAR x @@ VAR y))) @@ I)`
     by PROVE_TAC [asmlam_rules] THEN
  `xx_xy (LAM y (I @@ I)) ((LAM x (LAM y (VAR x @@ VAR x))) @@ I)`
     by (Q_TAC SUFF_TAC `[I/x] (LAM y (VAR x @@ VAR x)) = LAM y (I @@ I)` THEN1
               PROVE_TAC [asmlam_rules] THEN
         ASM_SIMP_TAC std_ss [SUB_THM, FV_I, NOT_IN_EMPTY]) THEN
  `xx_xy (LAM y (I @@ I)) (LAM y I)`
     by PROVE_TAC [asmlam_rules, lameq_I, lameq_asmlam] THEN
  `xx_xy (LAM y I) ((LAM x (LAM y (VAR x @@ VAR y))) @@ I)`
     by METIS_TAC [asmlam_trans, asmlam_sym] THEN
  `[I/x](LAM y (VAR x @@ VAR y)) = LAM y (I @@ VAR y)` by
      ASM_SIMP_TAC (srw_ss()) [SUB_THM, FV_I] THEN
  `xx_xy (LAM x (LAM y (VAR x @@ VAR y)) @@ I) (LAM y (I @@ VAR y))`
      by PROVE_TAC [asmlam_beta] THEN
  `xx_xy (LAM y (I @@ VAR y))  (LAM y I)`
      by METIS_TAC [asmlam_trans, asmlam_sym] THEN
  `xx_xy (LAM y (VAR y)) (LAM y I)`
      by (Q.UNABBREV_TAC `xx_xy` THEN MATCH_MP_TAC asmlam_trans THEN
          Q.EXISTS_TAC `LAM y (I @@ VAR y)` THEN
          METIS_TAC [asmlam_abscong, lameq_I, asmlam_sym, lameq_asmlam]) THEN
  `!D. xx_xy ((LAM y (VAR y)) @@ D) ((LAM y I) @@ D)`
      by PROVE_TAC [asmlam_lcong] THEN
  `!D. [D/y](VAR y) = D` by SRW_TAC [][SUB_THM] THEN
  `!D. xx_xy D ((LAM y I) @@ D)`
      by METIS_TAC [asmlam_beta, asmlam_trans, asmlam_sym] THEN
  `!D. [D/y]I = I` by SRW_TAC [][lemma14b, FV_I] THEN
  `!D. xx_xy D I`
      by PROVE_TAC [asmlam_beta, asmlam_trans, asmlam_sym] THEN
  METIS_TAC [asmlam_trans, asmlam_sym]);

val (is_abs_thm, _) = define_recursive_term_function
  `(is_abs (VAR s) = F) /\
   (is_abs (t1 @@ t2) = F) /\
   (is_abs (LAM v t) = T)`;
val _ = export_rewrites ["is_abs_thm"]

val is_abs_vsubst_invariant = Store_Thm(
  "is_abs_vsubst_invariant",
  ``!t. is_abs ([VAR v/u] t) = is_abs t``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val (is_comb_thm, _) = define_recursive_term_function
  `(is_comb (VAR s) = F) /\
   (is_comb (t1 @@ t2) = T) /\
   (is_comb (LAM v t) = F)`;
val _ = export_rewrites ["is_comb_thm"]

val is_comb_vsubst_invariant = Store_Thm(
  "is_comb_vsubst_invariant",
  ``!t. is_comb ([VAR v/u] t) = is_comb t``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val (is_var_thm, _) = define_recursive_term_function
  `(is_var (VAR s) = T) /\
   (is_var (t1 @@ t2) = F) /\
   (is_var (LAM v t) = F)`;
val _ = export_rewrites ["is_var_thm"]

val is_var_vsubst_invariant = Store_Thm(
  "is_var_vsubst_invariant",
  ``!t. is_var ([VAR v/u] t) = is_var t``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val (bnf_thm, _) = define_recursive_term_function
  `(bnf (VAR s) = T) /\
   (bnf (t1 @@ t2) = bnf t1 /\ bnf t2 /\ ~is_abs t1) /\
   (bnf (LAM v t) = bnf t)`;
val _ = export_rewrites ["bnf_thm"]

val bnf_vsubst_invariant = Store_Thm(
  "bnf_vsubst_invariant",
  ``!t. bnf ([VAR v/u] t) = bnf t``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val _ = augment_srw_ss [rewrites [LAM_eq_thm]]
val (rand_thm, _) = define_recursive_term_function `rand (t1 @@ t2) = t2`;
val _ = export_rewrites ["rand_thm"]

val (rator_thm, _) = define_recursive_term_function `rator (t1 @@ t2) = t1`;
val _ = export_rewrites ["rator_thm"]

val is_comb_APP_EXISTS = store_thm(
  "is_comb_APP_EXISTS",
  ``!t. is_comb t = (?u v. t = u @@ v)``,
  PROVE_TAC [term_CASES, is_comb_thm]);

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

val swap_eq_var = store_thm(
  "swap_eq_var",
  ``(tpm [(x,y)] t = VAR s) = (t = VAR (swapstr x y s))``,
  Q.SPEC_THEN `t` STRUCT_CASES_TAC term_CASES THEN
  SRW_TAC [][basic_swapTheory.swapstr_eq_left]);
val _ = augment_srw_ss [rewrites [swap_eq_var]]

val (enf_thm, _) = define_recursive_term_function
  `(enf (VAR s) = T) /\
   (enf (t @@ u) = enf t /\ enf u) /\
   (enf (LAM v t) = enf t /\ (is_comb t /\ (rand t = VAR v) ==>
                              v IN FV (rator t)))`
val _ = export_rewrites ["enf_thm"]

val subst_eq_var = store_thm(
  "subst_eq_var",
  ``([v/u] t = VAR s) = (t = VAR u) /\ (v = VAR s) \/
                        (t = VAR s) /\ ~(u = s)``,
  Q.SPEC_THEN `t` STRUCT_CASES_TAC term_CASES THEN
  SRW_TAC [][SUB_VAR, SUB_THM] THEN PROVE_TAC []);

val enf_vsubst_invariant = store_thm(
  "enf_vsubst_invariant",
  ``!t. enf ([VAR v/u] t) = enf t``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, enf_thm] THEN
  SRW_TAC [boolSimps.CONJ_ss][GSYM rand_subst_commutes, subst_eq_var] THEN
  SRW_TAC [][GSYM rator_subst_commutes, FV_SUB]);
val _ = export_rewrites ["enf_vsubst_invariant"]

(*val FV_RENAMING = store_thm(
  "FV_RENAMING",
  ``!R. RENAMING R ==>
        !t. FV (t ISUB R) = IMAGE (RENAME R) (FV t)``,
  HO_MATCH_MP_TAC RENAMING_ind THEN
  SRW_TAC [][RENAME_def, VNAME_DEF, EXTENSION, ISUB_def] THEN EQ_TAC THEN
  SRW_TAC [][FV_SUB] THEN PROVE_TAC []);
*)

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
end; (* struct *)
