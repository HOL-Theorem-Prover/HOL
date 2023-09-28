(*---------------------------------------------------------------------------*
 * Beta-equivalence and combinators (Chapter 2 of Hankin [2])
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib;

open pred_setTheory pred_setLib listTheory finite_mapTheory hurdUtils;

open termTheory BasicProvers nomsetTheory binderLib appFOLDLTheory;

val _ = augment_srw_ss [rewrites [LET_THM]]
val std_ss = std_ss ++ rewrites [LET_THM]

fun Store_thm(s, t, tac) = (store_thm(s,t,tac) before
                            export_rewrites [s])

structure NewQ = Q
structure Q = struct open Q open OldAbbrevTactics end;

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
  ``!z. one_hole_context (APP z)``,
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

val (lameq_rules, lameq_indn, lameq_cases) = (* p. 13 *)
  IndDefLib.xHol_reln "lameq"
    `(!x M N. (LAM x M) @@ N == [N/x]M) /\
     (!M. M == M) /\
     (!M N. M == N ==> N == M) /\
     (!M N L. M == N /\ N == L ==> M == L) /\
     (!M N Z. M == N ==> M @@ Z == N @@ Z) /\
     (!M N Z. M == N ==> Z @@ M == Z @@ N) /\
     (!M N x. M == N ==> LAM x M == LAM x N)`;

val lameq_refl = Store_thm(
  "lameq_refl",
  ``M:term == M``,
  SRW_TAC [][lameq_rules]);

val lameq_app_cong = store_thm(
  "lameq_app_cong",
  ``M1 == M2 ==> N1 == N2 ==> M1 @@ N1 == M2 @@ N2``,
  METIS_TAC [lameq_rules]);

val lameq_weaken_cong = store_thm(
  "lameq_weaken_cong",
  ``(M1:term) == M2 ==> N1 == N2 ==> (M1 == N1 <=> M2 == N2)``,
  METIS_TAC [lameq_rules]);

Theorem lameq_SYM = List.nth(CONJUNCTS lameq_rules, 2)

val fixed_point_thm = store_thm(  (* p. 14 *)
  "fixed_point_thm",
  ``!f. ?x. f @@ x == x``,
  GEN_TAC THEN Q_TAC (NEW_TAC "x") `FV f` THEN
  Q.ABBREV_TAC `w = (LAM x (f @@ (VAR x @@ VAR x)))` THEN
  Q.EXISTS_TAC `w @@ w` THEN
  `w @@ w == [w/x] (f @@ (VAR x @@ VAR x))` by PROVE_TAC [lameq_rules] THEN
  POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC (srw_ss())[SUB_THM, lemma14b, lameq_rules]);

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
  ``!x t u v. x NOTIN FV u /\ (x <> v ==> x NOTIN FV t) ==>
              x NOTIN FV ([t/v]u)``,
  SRW_TAC [][FV_SUB] THEN METIS_TAC []);

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
      `LAM x M == LAM x M'` by PROVE_TAC [lameq_rules] THEN
      `LAM x M @@ N == LAM x M' @@ N` by PROVE_TAC [lameq_rules] THEN
      PROVE_TAC [lameq_rules],
      Q_TAC SUFF_TAC `!N N' x M. N == N' ==> [N/x] M == [N'/x]M` THEN1
        SRW_TAC [][] THEN
      NTAC 3 GEN_TAC THEN HO_MATCH_MP_TAC nc_INDUCTION2 THEN
      Q.EXISTS_TAC `x INSERT FV N UNION FV N'` THEN
      SRW_TAC [][SUB_THM, SUB_VAR] THEN PROVE_TAC [lameq_rules]
    ],
    PROVE_TAC [lameq_rules]
  ]);

val lameq_sub_cong = save_thm(
  "lameq_sub_cong",
  REWRITE_RULE [GSYM AND_IMP_INTRO] (last (CONJUNCTS lemma2_12)));

val lemma2_13 = store_thm( (* p.20 *)
  "lemma2_13",
  ``!c n n'. ctxt c ==> (n == n') ==> (c n == c n')``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`n`, `n'`] THEN
  POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `c` THEN
  HO_MATCH_MP_TAC ctxt_indn THEN PROVE_TAC [lameq_rules]);

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
val FV_S = Store_thm(
  "FV_S",
  ``FV S = {}``,
  SRW_TAC [][S_def, EXTENSION] THEN METIS_TAC []);

val K_def = Define`K = LAM "x" (LAM "y" (VAR "x"))`;
val FV_K = Store_thm(
  "FV_K",
  ``FV K = {}``,
  SRW_TAC [][K_def, EXTENSION])

val I_def = Define`I = LAM "x" (VAR "x")`;
val FV_I = Store_thm("FV_I", ``FV I = {}``, SRW_TAC [][I_def]);

Theorem I_alt :
    !s. I = LAM s (VAR s)
Proof
    Q.X_GEN_TAC ‘x’
 >> REWRITE_TAC [I_def, Once EQ_SYM_EQ]
 >> Cases_on ‘x = "x"’ >- rw []
 >> NewQ.ABBREV_TAC ‘u :term = VAR x’
 >> NewQ.ABBREV_TAC ‘y = "x"’
 >> ‘y NOTIN FV u’ by rw [Abbr ‘u’]
 >> Know ‘LAM x u = LAM y ([VAR y/x] u)’
 >- (MATCH_MP_TAC SIMPLE_ALPHA >> art [])
 >> Rewr'
 >> Suff ‘[VAR y/x] u = VAR y’ >- rw []
 >> rw [Abbr ‘u’]
QED

Theorem SUB_I[simp] :
    [N/v] I = I
Proof
    rw [lemma14b]
QED

Theorem ssub_I :
    ssub fm I = I
Proof
    rw [ssub_value]
QED

val Omega_def =
    Define`Omega = (LAM "x" (VAR "x" @@ VAR "x")) @@
                     (LAM "x" (VAR "x" @@ VAR "x"))`
val _ = Unicode.unicode_version {tmnm = "Omega", u = UnicodeChars.Omega}
val FV_Omega = Store_thm(
  "FV_Omega",
  ``FV Omega = {}``,
  SRW_TAC [][Omega_def, EXTENSION]);

val SUB_LAM_RWT = store_thm(
  "SUB_LAM_RWT",
  ``!x y v body. [x/y] (LAM v body) =
                 let n = NEW (y INSERT FV x UNION FV body)
                 in
                   LAM n ([x/y]([VAR n/v] body))``,
  SIMP_TAC std_ss [] THEN REPEAT GEN_TAC THEN
  NEW_ELIM_TAC THEN Q.X_GEN_TAC `z` THEN STRIP_TAC THEN
  `LAM v body = LAM z ([VAR z/v] body)` by SRW_TAC [][SIMPLE_ALPHA] THEN
  SRW_TAC [][]);

val lameq_asmlam = store_thm(
  "lameq_asmlam",
  ``!M N. M == N ==> asmlam eqns M N``,
  HO_MATCH_MP_TAC lameq_indn THEN METIS_TAC [asmlam_rules]);

fun betafy ss =
    simpLib.add_relsimp {refl = GEN_ALL lameq_refl,
                         trans = List.nth(CONJUNCTS lameq_rules, 3),
                         weakenings = [lameq_weaken_cong],
                         subsets = [],
                         rewrs = [hd (CONJUNCTS lameq_rules)]} ss ++
    simpLib.SSFRAG {rewrs = [],
                    ac = [],  convs = [],
                    congs = [lameq_app_cong,
                             SPEC_ALL (last (CONJUNCTS lameq_rules)),
                             lameq_sub_cong],
                    dprocs = [], filter = NONE, name = NONE}

val lameq_S = store_thm(
  "lameq_S",
  ``S @@ A @@ B @@ C == (A @@ C) @@ (B @@ C)``,
  SIMP_TAC (srw_ss()) [S_def] THEN FRESH_TAC THEN
  ASM_SIMP_TAC (betafy (srw_ss())) [lemma14b]);

val lameq_K = store_thm(
  "lameq_K",
  ``K @@ A @@ B == A``,
  REWRITE_TAC [K_def] THEN FRESH_TAC THEN
  ASM_SIMP_TAC (betafy (srw_ss())) [lemma14b]);

val lameq_I = store_thm(
  "lameq_I",
  ``I @@ A == A``,
  PROVE_TAC [lameq_rules, I_def, SUB_THM]);

Theorem I_appstar' :
    !Is. (!e. MEM e Is ==> e = I) ==> I @* Is == I
Proof
    HO_MATCH_MP_TAC SNOC_INDUCT >> rw []
 >> ASM_SIMP_TAC (betafy (srw_ss())) [SNOC_APPEND, SYM appstar_SNOC, lameq_I]
QED

Theorem I_appstar :
    I @* (GENLIST (\i. I) n) == I
Proof
    NewQ.ABBREV_TAC ‘Is = GENLIST (\i. I) n’
 >> MATCH_MP_TAC I_appstar'
 >> rw [Abbr ‘Is’, MEM_GENLIST]
QED

val B_def = Define`B = S @@ (K @@ S) @@ K`;
val FV_B = Store_thm(
  "FV_B",
  ``FV B = {}``,
  SRW_TAC [][B_def]);

val lameq_B = store_thm(
  "lameq_B",
  ``B @@ f @@ g @@ x == f @@ (g @@ x)``,
  SIMP_TAC (betafy (srw_ss())) [lameq_S, lameq_K, B_def]);

val C_def = Define`
  C = S @@ (B @@ B @@ S) @@ (K @@ K)
`;
val FV_C = Store_thm(
  "FV_C",
  ``FV C = {}``,
  SRW_TAC [][C_def]);

val lameq_C = store_thm(
  "lameq_C",
  ``C @@ f @@ x @@ y == f @@ y @@ x``,
  SIMP_TAC (betafy (srw_ss())) [C_def, lameq_S, lameq_K, lameq_B]);

val Y_def = Define`
  Y = LAM "f" (LAM "x" (VAR "f" @@ (VAR "x" @@ VAR "x")) @@
               LAM "x" (VAR "f" @@ (VAR "x" @@ VAR "x")))
`;
val FV_Y = Store_thm(
  "FV_Y",
  ``FV Y = {}``,
  SRW_TAC [][Y_def, EXTENSION] THEN METIS_TAC []);

val Yf_def = Define`
  Yf f = let x = NEW (FV f)
         in
           LAM x (f @@ (VAR x @@ VAR x)) @@
           LAM x (f @@ (VAR x @@ VAR x))
`;

val YYf = store_thm(
  "YYf",
  ``Y @@ f == Yf f``,
  ONCE_REWRITE_TAC [lameq_cases] THEN DISJ1_TAC THEN
  SRW_TAC [boolSimps.DNF_ss][Yf_def, Y_def, LAM_eq_thm] THEN
  DISJ1_TAC THEN NEW_ELIM_TAC THEN SRW_TAC [][SUB_LAM_RWT] THEN
  NEW_ELIM_TAC THEN SRW_TAC [][LAM_eq_thm, supp_fresh]);

val YffYf = store_thm(
  "YffYf",
  ``Yf f == f @@ Yf f``,
  SRW_TAC [][Yf_def] THEN NEW_ELIM_TAC THEN SRW_TAC [][Once lameq_cases] THEN
  DISJ1_TAC THEN MAP_EVERY Q.EXISTS_TAC [`v`, `f @@ (VAR v @@ VAR v)`] THEN
  SRW_TAC [][lemma14b]);

val lameq_Y = store_thm(
  "lameq_Y",
  ``Y @@ f == f @@ (Y @@ f)``,
  METIS_TAC [lameq_rules, YYf, YffYf]);

val Yf_fresh = store_thm(
  "Yf_fresh",
  ``v ∉ FV f ⇒
    (Yf f = LAM v (f @@ (VAR v @@ VAR v)) @@ LAM v (f @@ (VAR v @@ VAR v)))``,
  SRW_TAC [][Yf_def, LET_THM] THEN
  binderLib.NEW_ELIM_TAC THEN SRW_TAC [][LAM_eq_thm, supp_fresh]);

val Yf_SUB = Store_thm(
  "Yf_SUB",
  ``[N/x] (Yf f) = Yf ([N/x] f)``,
  Q_TAC (NEW_TAC "v") `FV f ∪ FV N ∪ {x}` THEN
  `Yf f = LAM v (f @@ (VAR v @@ VAR v)) @@ LAM v (f @@ (VAR v @@ VAR v))`
     by SRW_TAC [][Yf_fresh] THEN
  `Yf ([N/x]f) =
     LAM v ([N/x]f @@ (VAR v @@ VAR v)) @@ LAM v ([N/x]f @@ (VAR v @@ VAR v))`
     by SRW_TAC [][Yf_fresh, NOT_IN_FV_SUB] THEN
  SRW_TAC [][]);

val Yf_11 = Store_thm(
  "Yf_11",
  ``(Yf f = Yf g) = (f = g)``,
  SRW_TAC [][Yf_def, LET_THM] THEN
  NTAC 2 (binderLib.NEW_ELIM_TAC THEN REPEAT STRIP_TAC) THEN
  SRW_TAC [][LAM_eq_thm, EQ_IMP_THM] THEN
  SRW_TAC [][supp_fresh]);

val FV_Yf = Store_thm(
  "FV_Yf",
  ``FV (Yf t) = FV t``,
  SRW_TAC [boolSimps.CONJ_ss][Yf_def, EXTENSION, LET_THM] THEN
  NEW_ELIM_TAC THEN METIS_TAC []);

val Yf_cong = store_thm(
  "Yf_cong",
  ``f == g ⇒ Yf f == Yf g``,
  Q_TAC (NEW_TAC "fv") `FV f ∪ FV g` THEN
  `(Yf f = LAM fv (f @@ (VAR fv @@ VAR fv)) @@
           LAM fv (f @@ (VAR fv @@ VAR fv))) ∧
   (Yf g = LAM fv (g @@ (VAR fv @@ VAR fv)) @@
           LAM fv (g @@ (VAR fv @@ VAR fv)))`
     by SRW_TAC [][Yf_fresh] THEN
  STRIP_TAC THEN ASM_SIMP_TAC (srw_ss()) [] THEN
  METIS_TAC [lameq_rules]);

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

val is_abs_vsubst_invariant = Store_thm(
  "is_abs_vsubst_invariant",
  ``!t. is_abs ([VAR v/u] t) = is_abs t``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val (is_comb_thm, _) = define_recursive_term_function
  `(is_comb (VAR s) = F) /\
   (is_comb (t1 @@ t2) = T) /\
   (is_comb (LAM v t) = F)`;
val _ = export_rewrites ["is_comb_thm"]

val is_comb_vsubst_invariant = Store_thm(
  "is_comb_vsubst_invariant",
  ``!t. is_comb ([VAR v/u] t) = is_comb t``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val (is_var_thm, _) = define_recursive_term_function
  `(is_var (VAR s) = T) /\
   (is_var (t1 @@ t2) = F) /\
   (is_var (LAM v t) = F)`;
val _ = export_rewrites ["is_var_thm"]

val is_var_vsubst_invariant = Store_thm(
  "is_var_vsubst_invariant",
  ``!t. is_var ([VAR v/u] t) = is_var t``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val (bnf_thm, _) = define_recursive_term_function
  `(bnf (VAR s) <=> T) /\
   (bnf (t1 @@ t2) <=> bnf t1 /\ bnf t2 /\ ~is_abs t1) /\
   (bnf (LAM v t) <=> bnf t)`;
val _ = export_rewrites ["bnf_thm"]

val bnf_Omega = Store_thm(
  "bnf_Omega",
  ``~bnf Omega``,
  SRW_TAC [][Omega_def]);
val I_beta_normal = Store_thm(
  "I_beta_normal",
  ``bnf I``,
  SRW_TAC [][I_def]);
val K_beta_normal = Store_thm("K_beta_normal", ``bnf K``, SRW_TAC [][K_def]);
val S_beta_normal = Store_thm("S_beta_normal", ``bnf S``, SRW_TAC [][S_def]);
(* because I have defined them in terms of applications of S and K, C and B
   are not in bnf *)

val Yf_bnf = Store_thm(
  "Yf_bnf",
  ``¬bnf (Yf f)``,
  SRW_TAC [][Yf_def] THEN SRW_TAC [][]);

val bnf_vsubst_invariant = Store_thm(
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

val tpm_eq_var = prove(
  ``(tpm pi t = VAR s) <=> (t = VAR (lswapstr pi⁻¹ s))``,
  SRW_TAC [][pmact_eql]);
val _ = augment_srw_ss [rewrites [tpm_eq_var]]

val (enf_thm, _) = define_recursive_term_function
  `(enf (VAR s) <=> T) /\
   (enf (t @@ u) <=> enf t /\ enf u) /\
   (enf (LAM v t) <=> enf t /\ (is_comb t /\ rand t = VAR v ==>
                                v IN FV (rator t)))`
val _ = export_rewrites ["enf_thm"]

val subst_eq_var = store_thm(
  "subst_eq_var",
  ``[v/u] t = VAR s <=> t = VAR u ∧ v = VAR s ∨ t = VAR s ∧ u ≠ s``,
  Q.SPEC_THEN `t` STRUCT_CASES_TAC term_CASES THEN
  SRW_TAC [][SUB_VAR, SUB_THM] THEN PROVE_TAC []);

val enf_vsubst_invariant = Store_thm(
  "enf_vsubst_invariant",
  ``!t. enf ([VAR v/u] t) = enf t``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, enf_thm] THEN
  SRW_TAC [boolSimps.CONJ_ss][GSYM rand_subst_commutes, subst_eq_var] THEN
  SRW_TAC [][GSYM rator_subst_commutes, FV_SUB]);

val benf_def = Define`benf t <=> bnf t /\ enf t`;


val has_bnf_def = Define`has_bnf t = ?t'. t == t' /\ bnf t'`;

val has_benf_def = Define`has_benf t = ?t'. t == t' /\ benf t'`;

(* FIXME: can ‘(!y. y IN FDOM fm ==> closed (fm ' y))’ be removed? *)
Theorem lameq_ssub_cong :
    !fm. (!y. y IN FDOM fm ==> closed (fm ' y)) /\
          M == N ==> fm ' M == fm ' N
Proof
    HO_MATCH_MP_TAC fmap_INDUCT
 >> rw [FAPPLY_FUPDATE_THM]
 >> Know ‘!y. y IN FDOM fm ==> closed (fm ' y)’
 >- (Q.X_GEN_TAC ‘z’ >> DISCH_TAC \\
    ‘z <> x’ by PROVE_TAC [] \\
     Q.PAT_X_ASSUM ‘!y. y = x \/ y IN FDOM fm ==> P’ (MP_TAC o (Q.SPEC ‘z’)) \\
     RW_TAC std_ss [])
 >> DISCH_TAC
 >> ‘fm ' M == fm ' N’ by PROVE_TAC []
 >> Know ‘(fm |+ (x,y)) ' M = [y/x] (fm ' M)’
 >- (MATCH_MP_TAC ssub_update_apply >> art [])
 >> Rewr'
 >> Know ‘(fm |+ (x,y)) ' N = [y/x] (fm ' N)’
 >- (MATCH_MP_TAC ssub_update_apply >> art [])
 >> Rewr'
 >> ASM_SIMP_TAC (betafy (srw_ss())) []
QED

Theorem lameq_appstar_cong :
    !M N Ns. M == N ==> M @* Ns == N @* Ns
Proof
    NTAC 2 GEN_TAC
 >> HO_MATCH_MP_TAC SNOC_INDUCT >> rw []
 >> ASM_SIMP_TAC (betafy (srw_ss())) [SNOC_APPEND, SYM appstar_SNOC]
QED

val _ = remove_ovl_mapping "Y" {Thy = "chap2", Name = "Y"}

val _ = export_theory()

(* References:

   [2] Hankin, C.: Lambda Calculi: A Guide for Computer Scientists.
       Clarendon Press, Oxford (1994).
 *)
