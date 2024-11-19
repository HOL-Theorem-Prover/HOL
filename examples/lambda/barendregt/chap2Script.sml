(*---------------------------------------------------------------------------*
 * Beta-equivalence and combinators (Chapter 2 of Hankin [2])
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib bossLib BasicProvers;

open pred_setTheory pred_setLib listTheory rich_listTheory finite_mapTheory
     arithmeticTheory string_numTheory hurdUtils pairTheory;

open basic_swapTheory termTheory nomsetTheory binderLib appFOLDLTheory;

val _ = augment_srw_ss [rewrites [LET_THM]]
val std_ss = std_ss ++ rewrites [LET_THM]

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

Inductive lameq :
[~BETA:]
  !x M N. (LAM x M) @@ N == [N/x]M
[~REFL:]
  !M. M == M
[~SYM:]
  !M N. M == N ==> N == M
[~TRANS:]
  !M N L. M == N /\ N == L ==> M == L
[~APPL:]
  !M N Z. M == N ==> M @@ Z == N @@ Z
[~APPR:]
  !M N Z. M == N ==> Z @@ M == Z @@ N
[~ABS:]
  !M N x. M == N ==> LAM x M == LAM x N
End

Theorem lameq_refl[simp] = lameq_REFL

Theorem lameq_tpm:
  ∀M N. M == N ⇒ ∀π. tpm π M == tpm π N
Proof
  Induct_on ‘M == N’ >> simp[tpm_thm, tpm_subst, lameq_BETA] >>
  metis_tac[lameq_rules]
QED

Theorem lameq_ind_genX:
  ∀P f.
    (∀x:α. FINITE (f x)) ∧
    (∀v M N x. v ∉ f x ⇒ P (LAM v M @@ N) ([N/v]M) x) ∧
    (∀M x. P M M x) ∧
    (∀M N x. N == M ∧ (∀y. P N M y) ⇒ P M N x) ∧
    (∀L M N x. L == M ∧ M == N ∧ (∀w. P L M w) ∧ (∀y. P M N y) ⇒ P L N x) ∧
    (∀M N Z x. M == N ∧ (∀y. P M N y) ⇒ P (M @@ Z) (N @@ Z) x) ∧
    (∀M N Z x. M == N ∧ (∀y. P M N y) ⇒ P (Z @@ M) (Z @@ N) x) ∧
    (∀v M N x. M == N ∧ v ∉ f x ∧ (∀y. P M N y) ⇒ P (LAM v M) (LAM v N) x) ⇒
    ∀M N. M == N ⇒ ∀x. P M N x
Proof
  rpt gen_tac >> strip_tac >>
  ‘∀M N. M == N ⇒ ∀π x. P (tpm π M) (tpm π N) x’
    suffices_by metis_tac[pmact_nil] >>
  Induct_on ‘M == N’ >> rw[tpm_subst] >~
  [‘P (LAM (lswapstr π v) _) (LAM _ _) x’]
  >- (Q_TAC (NEW_TAC "z") ‘FV (tpm π M) ∪ FV (tpm π N) ∪ f x’ >>
      ‘LAM (lswapstr π v) (tpm π M) = LAM z (tpm [(z,lswapstr π v)] (tpm π M)) ∧
       LAM (lswapstr π v) (tpm π N) = LAM z (tpm [(z,lswapstr π v)] (tpm π N))’
        by simp[tpm_ALPHA] >>
      simp[] >> first_x_assum irule >> simp[GSYM tpm_CONS, lameq_tpm]) >~
  [‘P (LAM (lswapstr π v) (tpm π M) @@ tpm π N) _ x’]
  >- (Q_TAC (NEW_TAC "z") ‘FV (tpm π M) ∪ FV (tpm π N) ∪ f x’ >>
      ‘LAM (lswapstr π v) (tpm π M) = LAM z (tpm [(z,lswapstr π v)] (tpm π M))’
        by simp[tpm_ALPHA] >>
      simp[] >>
      ‘[tpm π N/z] (tpm [(z,lswapstr π v)] (tpm π M)) =
       [tpm π N/lswapstr π v] (tpm π M)’ suffices_by metis_tac[] >>
      simp[fresh_tpm_subst, lemma15a]) >>
  metis_tac[lameq_tpm]
QED

Theorem lameq_ind_X =
        lameq_ind_genX |> INST_TYPE [alpha |-> “:unit”]
                       |> Q.SPECL [‘λM N u. Q M N’, ‘K X’]
                       |> SRULE[]
                       |> Q.INST[‘Q’ |-> ‘P’]
                       |> Q.GENL [‘P’, ‘X’]

val lameq_app_cong = store_thm(
  "lameq_app_cong",
  ``M1 == M2 ==> N1 == N2 ==> M1 @@ N1 == M2 @@ N2``,
  METIS_TAC [lameq_rules]);

val lameq_weaken_cong = store_thm(
  "lameq_weaken_cong",
  ``(M1:term) == M2 ==> N1 == N2 ==> (M1 == N1 <=> M2 == N2)``,
  METIS_TAC [lameq_rules]);

Theorem fixed_point_thm:
  !f. ?x. f @@ x == x ∧ FV x = FV f
Proof
  GEN_TAC THEN Q_TAC (NEW_TAC "x") `FV f` THEN
  Q.ABBREV_TAC `w = (LAM x (f @@ (VAR x @@ VAR x)))` THEN
  Q.EXISTS_TAC `w @@ w` THEN
  `w @@ w == [w/x] (f @@ (VAR x @@ VAR x))` by PROVE_TAC [lameq_rules] THEN
  POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC (srw_ss())[SUB_THM, lemma14b, lameq_rules] >>
  rw[] >> ASM_SET_TAC[]
QED

(* properties of substitution - p19 *)

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

(* |- M == M' ==> N == N' ==> [N/x] M == [N'/x] M' *)
val lameq_sub_cong = save_thm(
  "lameq_sub_cong",
  REWRITE_RULE [GSYM AND_IMP_INTRO] (last (CONJUNCTS lemma2_12)));

Theorem lameq_isub_cong :
    !ss M N. M == N ==> M ISUB ss == N ISUB ss
Proof
    Induct_on ‘ss’
 >- rw []
 >> simp [FORALL_PROD]
 >> qx_genl_tac [‘P’, ‘v’]
 >> rpt STRIP_TAC
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> MATCH_MP_TAC (cj 1 lemma2_12) >> art []
QED

val lemma2_13 = store_thm( (* p.20 *)
  "lemma2_13",
  ``!c n n'. ctxt c ==> (n == n') ==> (c n == c n')``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`n`, `n'`] THEN
  POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `c` THEN
  HO_MATCH_MP_TAC ctxt_indn THEN PROVE_TAC [lameq_rules]);

Theorem lameq_LAMl_cong :
    !vs M N. M == N ==> LAMl vs M == LAMl vs N
Proof
    Induct_on ‘vs’ >> rw [lameq_ABS]
QED

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

Inductive lameta : (* p. 21 *)
[~BETA:]
  !x M N. lameta ((LAM x M) @@ N) ([N/x]M)
[~REFL:]
  !M. lameta M M
[~SYM:]
  !M N. lameta M N ==> lameta N M
[~TRANS:]
  !M N L. lameta M N /\ lameta N L ==> lameta M L
[~APPL:]
  !M N Z. lameta M N ==> lameta (M @@ Z) (N @@ Z)
[~APPR:]
  !M N Z. lameta M N ==> lameta (Z @@ M) (Z @@ N)
[~ABS:]
  !M N x. lameta M N ==> lameta (LAM x M) (LAM x N)
[~ETA:]
  !M x. ~(x IN FV M) ==> lameta (LAM x (M @@ VAR x)) M
End

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

(* Definition 2.1.30 [1, p.33]: "Let tt be a formal theory with equations as
   formulas. Then tt is consistent (notation Con(tt)) if tt does not prove every
   closed equation. In the opposite case tt is consistent.
 *)
Definition consistent_def :
    consistent (thy:term -> term -> bool) = ?M N. ~thy M N
End

Overload inconsistent = “\thy. ~consistent thy”

Theorem inconsistent_def :
    !thy. inconsistent thy <=> !M N. thy M N
Proof
    rw [consistent_def]
QED

Theorem inconsistent_mono :
    !t1 t2. t1 RSUBSET t2 /\ inconsistent t1 ==> inconsistent t2
Proof
    rw [relationTheory.RSUBSET, inconsistent_def]
QED

(* This is lambda theories (only having beta equivalence, no eta equivalence)
   extended with extra equations as formulas.

   cf. Definition 4.1.1 [1, p.76]. If ‘eqns’ is a set of closed equations,
   then ‘{(M,N) | asmlam eqns M N}’ is the set of closed equations provable
   in lambda + eqns, denoted by ‘eqns^+’ in [1], or ‘asmlam eqns’ here.

 *)
Inductive asmlam :
[~eqn:]
  !M N. (M,N) IN eqns ==> asmlam eqns M N
[~beta:]
  !x M N. asmlam eqns (LAM x M @@ N) ([N/x]M)
[~refl:]
  !M. asmlam eqns M M
[~sym:]
  !M N. asmlam eqns M N ==> asmlam eqns N M
[~trans:]
  !M N P. asmlam eqns M N /\ asmlam eqns N P ==> asmlam eqns M P
[~lcong:]
  !M M' N. asmlam eqns M M' ==> asmlam eqns (M @@ N) (M' @@ N)
[~rcong:]
  !M N N'. asmlam eqns N N' ==> asmlam eqns (M @@ N) (M @@ N')
[~abscong:]
  !x M M'. asmlam eqns M M' ==> asmlam eqns (LAM x M) (LAM x M')
End

Theorem asmlam_subst :
    !M N P x. asmlam eqns M N ==> asmlam eqns ([P/x] M) ([P/x] N)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC asmlam_trans
 >> Q.EXISTS_TAC ‘LAM x N @@ P’
 >> simp [asmlam_rules]
 >> MATCH_MP_TAC asmlam_trans
 >> Q.EXISTS_TAC ‘LAM x M @@ P’
 >> simp [asmlam_rules]
QED

(* Definition 2.1.32 [1, p.33]

   cf. also Definition 2.1.30 (iii): If t is a set of equations, then lambda + t
   is the theory obtained from lambda by adding the equations of t as axioms.
   t is called consistent (notation Con(t)) if Con(lambda + t), or in our words,
  ‘consistent (asmlam T)’.

   This explains why ‘asmlam’ is involved in the definition of ‘incompatible’.
*)
Definition incompatible_def :
    incompatible x y = ~consistent (asmlam {(x,y)})
End

(* NOTE: in termTheory, ‘v # M’ also denotes ‘v NOTIN FV M’ *)
Overload "#" = “incompatible”

val S_def =
    Define`S = LAM "x" (LAM "y" (LAM "z"
                                     ((VAR "x" @@ VAR "z") @@
                                      (VAR "y" @@ VAR "z"))))`;
Theorem FV_S[simp]: FV S = {}
Proof
  SRW_TAC [][S_def, EXTENSION] THEN METIS_TAC []
QED

Definition K_def: K = LAM "x" (LAM "y" (VAR "x"))
End
Theorem FV_K[simp]: FV K = {}
Proof SRW_TAC [][K_def, EXTENSION]
QED

val I_def = Define`I = LAM "x" (VAR "x")`;
Theorem FV_I[simp]: FV I = {}
Proof SRW_TAC [][I_def]
QED

Theorem I_thm :
    !s. I = LAM s (VAR s)
Proof
    rw [I_def, Once EQ_SYM_EQ]
 >> Cases_on ‘s = "x"’ >> rw [LAM_eq_thm]
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

Theorem I_cases :
    !Y t. I = LAM Y t ==> t = VAR Y
Proof
    rw [I_def]
 >> qabbrev_tac ‘X = "x"’
 >> Cases_on ‘X = Y’ >> fs [LAM_eq_thm]
QED

val Omega_def =
    Define`Omega = (LAM "x" (VAR "x" @@ VAR "x")) @@
                     (LAM "x" (VAR "x" @@ VAR "x"))`
val _ = Unicode.unicode_version {tmnm = "Omega", u = UnicodeChars.Omega}
Theorem FV_Omega[simp]: FV Omega = {}
Proof
  SRW_TAC [][Omega_def, EXTENSION]
QED

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
  HO_MATCH_MP_TAC lameq_ind THEN METIS_TAC [asmlam_rules]);

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
  Induct_on ‘Is’ using SNOC_INDUCT >> rw [appstar_SNOC]
  >> ASM_SIMP_TAC (betafy (srw_ss())) [lameq_I]
QED

Theorem I_appstar :
    I @* (GENLIST (\i. I) n) == I
Proof
    qabbrev_tac ‘Is = GENLIST (\i. I) n’
 >> MATCH_MP_TAC I_appstar'
 >> rw [Abbr ‘Is’, MEM_GENLIST]
QED

val B_def = Define`B = S @@ (K @@ S) @@ K`;
Theorem FV_B[simp]:
  FV B = {}
Proof
  SRW_TAC [][B_def]
QED

val lameq_B = store_thm(
  "lameq_B",
  ``B @@ f @@ g @@ x == f @@ (g @@ x)``,
  SIMP_TAC (betafy (srw_ss())) [lameq_S, lameq_K, B_def]);

val C_def = Define`
  C = S @@ (B @@ B @@ S) @@ (K @@ K)
`;
Theorem FV_C[simp]: FV C = {}
Proof SRW_TAC [][C_def]
QED

val lameq_C = store_thm(
  "lameq_C",
  ``C @@ f @@ x @@ y == f @@ y @@ x``,
  SIMP_TAC (betafy (srw_ss())) [C_def, lameq_S, lameq_K, lameq_B]);

val Y_def = Define`
  Y = LAM "f" (LAM "x" (VAR "f" @@ (VAR "x" @@ VAR "x")) @@
               LAM "x" (VAR "f" @@ (VAR "x" @@ VAR "x")))
`;
Theorem FV_Y[simp]: FV Y = {}
Proof SRW_TAC [][Y_def, EXTENSION] THEN METIS_TAC []
QED

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

Theorem Yf_SUB[simp]:
  [N/x] (Yf f) = Yf ([N/x] f)
Proof
  Q_TAC (NEW_TAC "v") ‘FV f ∪ FV N ∪ {x}’ THEN
  ‘Yf f = LAM v (f @@ (VAR v @@ VAR v)) @@ LAM v (f @@ (VAR v @@ VAR v))’
     by SRW_TAC [][Yf_fresh] THEN
  ‘Yf ([N/x]f) =
     LAM v ([N/x]f @@ (VAR v @@ VAR v)) @@ LAM v ([N/x]f @@ (VAR v @@ VAR v))’
     by SRW_TAC [][Yf_fresh, NOT_IN_FV_SUB] THEN
  SRW_TAC [][]
QED

Theorem Yf_11[simp]:
  (Yf f = Yf g) = (f = g)
Proof
  SRW_TAC [][Yf_def, LET_THM] THEN
  NTAC 2 (binderLib.NEW_ELIM_TAC THEN REPEAT STRIP_TAC) THEN
  SRW_TAC [][LAM_eq_thm, EQ_IMP_THM] THEN
  SRW_TAC [][supp_fresh]
QED

Theorem FV_Yf[simp]:
  FV (Yf t) = FV t
Proof
  SRW_TAC [boolSimps.CONJ_ss][Yf_def, EXTENSION, LET_THM] THEN
  NEW_ELIM_TAC THEN METIS_TAC []
QED

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

(* This is Example 2.1.33 [1, p.33] and Example 2.18 [2, p23] *)
Theorem SK_incompatible :
    incompatible S K
Proof
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
  PROVE_TAC [asmlam_rules]
QED

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

Theorem is_abs_vsubst_invariant[simp]:
  !t. is_abs ([VAR v/u] t) = is_abs t
Proof
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]
QED

Theorem is_abs_cases :
    !t. is_abs t <=> ?v t0. t = LAM v t0
Proof
    Q.X_GEN_TAC ‘t’
 >> Q.SPEC_THEN ‘t’ STRUCT_CASES_TAC term_CASES
 >> SRW_TAC [][]
 >> qexistsl_tac [‘v’, ‘t0’] >> REWRITE_TAC []
QED

Theorem is_abs_cases_genX :
    !v t. is_abs t /\ v # t <=> ?t0. t = LAM v t0
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC >- (STRIP_TAC >> rw [is_abs_thm])
 >> rw [is_abs_cases]
 >> fs [FV_thm]
 >> Cases_on ‘v = v'’
 >- (Q.EXISTS_TAC ‘t0’ >> rw [])
 >> Q.EXISTS_TAC ‘[VAR v/v'] t0’
 >> MATCH_MP_TAC SIMPLE_ALPHA >> rw []
QED

Theorem is_abs_appstar[simp]:
  is_abs (M @* Ns) ⇔ is_abs M ∧ (Ns = [])
Proof
  Induct_on ‘Ns’ using SNOC_INDUCT >>
  simp[appstar_SNOC]
QED

Theorem is_abs_LAMl[simp]:
  is_abs (LAMl vs M) ⇔ vs ≠ [] ∨ is_abs M
Proof
  Cases_on ‘vs’ >> simp[]
QED

val (is_comb_thm, _) = define_recursive_term_function
  `(is_comb (VAR s) = F) /\
   (is_comb (t1 @@ t2) = T) /\
   (is_comb (LAM v t) = F)`;
val _ = export_rewrites ["is_comb_thm"]

Theorem is_comb_LAMl[simp] :
    is_comb (LAMl vs M) <=> (vs = []) /\ is_comb M
Proof
  Cases_on `vs` THEN SRW_TAC [][]
QED

Theorem is_comb_vsubst_invariant[simp]:
  !t. is_comb ([VAR v/u] t) = is_comb t
Proof
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]
QED

Theorem EQ_LAML_bodies_permute:
  ∀us vs M N. (LAMl us M = LAMl vs N) ∧ ¬is_abs M ∧ ¬is_abs N ⇒
              ∃pi. N = tpm pi M
Proof
  Induct >> simp[]
  >- metis_tac[pmact_nil] >>
  simp[] >> rpt gen_tac >> rename [‘LAM x (LAMl xs _) = LAMl ys _’] >>
  Cases_on ‘ys’ >> simp[] >- (rw[] >> gvs[]) >>
  rename [‘LAM x (LAMl xs M) = LAM y (LAMl ys N)’] >>
  simp[LAM_eq_thm] >> rw[] >> gvs[tpm_LAMl]
  >- metis_tac[] >>
  first_x_assum drule >> simp[] >> rename [‘tpm [(a,b)] N = _’] >>
  rw[] >> pop_assum (mp_tac o Q.AP_TERM ‘tpm [(a,b)]’) >>
  REWRITE_TAC [pmact_sing_inv] >> metis_tac[pmact_decompose]
QED

val (is_var_thm, _) = define_recursive_term_function
  `(is_var (VAR s) = T) /\
   (is_var (t1 @@ t2) = F) /\
   (is_var (LAM v t) = F)`;
val _ = export_rewrites ["is_var_thm"]

Theorem is_var_vsubst_invariant[simp]:
  !t. is_var ([VAR v/u] t) = is_var t
Proof
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]
QED

Theorem is_var_cases :
    !t. is_var t <=> ?y. t = VAR y
Proof
    Q.X_GEN_TAC ‘t’
 >> Q.SPEC_THEN ‘t’ STRUCT_CASES_TAC term_CASES
 >> SRW_TAC [][]
QED

(* accessor for retrieving ‘y’ from ‘VAR y’ *)
local
    val th1 = prove (“!t. is_var t ==> ?y. t = VAR y”, rw [is_var_cases]);
    val th2 = SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] th1;
in
   (* |- !t. is_var t ==> t = VAR (THE_VAR t) *)
    val THE_VAR_def = new_specification ("THE_VAR_def", ["THE_VAR"], th2);
end;

Theorem THE_VAR_thm[simp] :
    !y. THE_VAR (VAR y) = y
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘t = (VAR y :term)’ >> simp []
 >> ‘is_var t’ by rw [Abbr ‘t’]
 >> Suff ‘VAR (THE_VAR t) = (VAR y :term)’ >- rw []
 >> ASM_SIMP_TAC std_ss [GSYM THE_VAR_def]
QED

Theorem term_cases :
    !t. is_var t \/ is_comb t \/ is_abs t
Proof
    Q.X_GEN_TAC ‘t’
 >> Q.SPEC_THEN ‘t’ STRUCT_CASES_TAC term_CASES
 >> SRW_TAC [][]
QED

Theorem term_cases_disjoint :
    !t. ~(is_comb t /\ is_abs t) /\
        ~(is_comb t /\ is_var t) /\
        ~(is_abs t /\ is_var t)
Proof
    Q.X_GEN_TAC ‘t’
 >> rpt CONJ_TAC
 >| [ (* goal 1 (of 3) *)
      Suff ‘is_abs t ==> ~is_comb t’ >- PROVE_TAC [] \\
      rw [is_abs_cases] >> rw [],
      (* goal 2 (of 3) *)
      Suff ‘is_var t ==> ~is_comb t’ >- PROVE_TAC [] \\
      rw [is_var_cases] >> rw [],
      (* goal 3 (of 3) *)
      Suff ‘is_abs t ==> ~is_var t’ >- PROVE_TAC [] \\
      rw [is_abs_cases] >> rw [] ]
QED

Theorem term_laml_cases:
  ∀X. FINITE X ⇒
      ∀t. (∃s. t = VAR s) ∨ (∃M1 M2. t = M1 @@ M2) ∨
          ∃v vs Body. t = LAM v (LAMl vs Body) ∧ ¬is_abs Body ∧ v ∉ X ∧
                      ¬MEM v vs ∧ ALL_DISTINCT vs ∧ DISJOINT (set vs) X
Proof
  gen_tac >> strip_tac >> ho_match_mp_tac nc_INDUCTION2 >> simp[] >>
  qexists ‘X’ >> simp[] >> rw[] >~
  [‘LAM v (VAR u)’, ‘v ∉ X’]
  >- (qexistsl [‘v’, ‘[]’, ‘VAR u’] >> simp[]) >~
  [‘LAM v (M1 @@ M2)’, ‘v ∉ X’]
  >- (qexistsl [‘v’, ‘[]’, ‘M1 @@ M2’] >> simp[]) >~
  [‘LAM u (LAM v (LAMl vs Body))’, ‘u ∉ X’, ‘v ∉ X’] >>
  Cases_on ‘u = v’ >> gvs[]
  >- (Q_TAC (NEW_TAC "z") ‘u INSERT set vs ∪ FV Body ∪ X’ >>
      ‘z # LAM u (LAMl vs Body)’ by simp[FV_LAMl] >>
      drule_then (qspec_then ‘u’ assume_tac) SIMPLE_ALPHA >> simp[lemma14b] >>
      qexistsl [‘z’, ‘u::vs’, ‘Body’] >> simp[]) >>
  Cases_on ‘MEM u vs’
  >- (Q_TAC (NEW_TAC "z") ‘{u;v} ∪ set vs ∪ FV Body ∪ X’ >>
      ‘z # LAM v (LAMl vs Body)’ by simp[FV_LAMl] >>
      drule_then (qspec_then ‘u’ assume_tac) SIMPLE_ALPHA >>
      simp[lemma14b, FV_LAMl] >>
      qexistsl [‘z’, ‘v::vs’, ‘Body’] >> simp[]) >>
  Q_TAC (NEW_TAC "z") ‘{u;v} ∪ set vs ∪ X ∪ FV Body’ >>
  ‘z # LAM v (LAMl vs Body)’ by simp[FV_LAMl] >>
  drule_then (qspec_then ‘u’ assume_tac) tpm_ALPHA >> simp[] >>
  qexists ‘z’ >> Q.REFINE_EXISTS_TAC ‘x::xs’ >> simp[tpm_LAMl] >>
  irule_at Any EQ_REFL >> simp[DISJOINT_DEF, EXTENSION, MEM_listpm] >>
  qx_gen_tac ‘a’ >> Cases_on ‘a ∈ X’ >> simp[] >>
  Cases_on ‘a = u’ >> gvs[] >>
  Cases_on ‘a = z’ >> gvs[] >>
  gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

val (bnf_thm, _) = define_recursive_term_function
  `(bnf (VAR s) <=> T) /\
   (bnf (t1 @@ t2) <=> bnf t1 /\ bnf t2 /\ ~is_abs t1) /\
   (bnf (LAM v t) <=> bnf t)`;
val _ = export_rewrites ["bnf_thm"]

Theorem bnf_Omega[simp]: ~bnf Omega
Proof SRW_TAC [][Omega_def]
QED

Theorem I_beta_normal[simp]: bnf I
Proof SRW_TAC [][I_def]
QED

Theorem K_beta_normal[simp]: bnf K
Proof SRW_TAC [][K_def]
QED

Theorem S_beta_normal[simp]: bnf S
Proof SRW_TAC [][S_def]
QED
(* because I have defined them in terms of applications of S and K, C and B
   are not in bnf *)

Theorem Yf_bnf[simp]: ¬bnf (Yf f)
Proof
  SRW_TAC [][Yf_def] THEN SRW_TAC [][]
QED

Theorem bnf_vsubst_invariant[simp]:
  !t. bnf ([VAR v/u] t) = bnf t
Proof
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]
QED

Theorem bnf_LAMl[simp]:
  bnf (LAMl vs M) = bnf M
Proof
  Induct_on ‘vs’ >> simp[]
QED

Theorem bnf_appstar[simp]:
  ∀M Ns. bnf (M @* Ns) ⇔ bnf M ∧ (∀N. MEM N Ns ⇒ bnf N) ∧ (is_abs M ⇒ Ns = [])
Proof
  Induct_on ‘Ns’ using listTheory.SNOC_INDUCT >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[]
QED

Theorem bnf_characterisation_X:
  ∀M X. FINITE X ⇒
        (bnf M ⇔
           ∃vs v Ms. DISJOINT (set vs) X ∧ M = LAMl vs (VAR v @* Ms) ∧
                     ALL_DISTINCT vs ∧ ∀M. MEM M Ms ⇒ bnf M)
Proof
  completeInduct_on ‘size M’ >> rw[] >> gvs[GSYM RIGHT_FORALL_IMP_THM] >>
  drule_then (qspec_then ‘M’ strip_assume_tac) term_laml_cases >> simp[] >~
  [‘M1 @@ M2’]
  >- (first_assum $ qspec_then ‘M1’ assume_tac >>
      first_x_assum $ qspec_then ‘M2’ assume_tac >> gs[]>>
      rpt (first_x_assum $ drule_then assume_tac) >>
      simp[] >> iff_tac >> rw[] >>
      gvs[app_eq_appstar_SNOC, LAMl_eq_appstar, DISJ_IMP_THM, FORALL_AND_THM] >>
      dsimp[PULL_EXISTS] >> metis_tac[]) >~
  [‘LAM u $ LAMl us Body’]
  >- (gvs[] >>
      first_x_assum $ qspec_then ‘Body’ mp_tac >> simp[]>>
      disch_then $ qspec_then ‘∅’ mp_tac >> simp[] >>
      disch_then kall_tac >>
      ‘∀xs M. Body = LAMl xs M ⇔ xs = [] ∧ M = Body’
        by (rpt gen_tac >> Cases_on ‘xs’ >> simp[] >- metis_tac[] >>
            strip_tac >> gvs[]) >>
      simp[] >> iff_tac >> rw[]
      >- (qexistsl [‘u::us’, ‘v’, ‘Ms’] >> simp[]) >>
      rename [‘LAM u (LAMl us Body) = LAMl vs (VAR v @* Ms)’] >>
      ‘LAMl vs (VAR v @* Ms) = LAMl (u::us) Body’ by simp[] >>
      drule EQ_LAML_bodies_permute >>
      simp[PULL_EXISTS, tpm_appstar, MEM_listpm_EXISTS])
QED

Theorem bnf_characterisation =
        MATCH_MP bnf_characterisation_X
                 (INST_TYPE [“:α” |-> “:string”] FINITE_EMPTY)
          |> REWRITE_RULE [DISJOINT_EMPTY]

val _ = augment_srw_ss [rewrites [LAM_eq_thm]]
val (rand_thm, _) = define_recursive_term_function `rand (t1 @@ t2) = t2`;
val _ = export_rewrites ["rand_thm"]

val (rator_thm, _) = define_recursive_term_function `rator (t1 @@ t2) = t1`;
val _ = export_rewrites ["rator_thm"]

val is_comb_APP_EXISTS = store_thm(
  "is_comb_APP_EXISTS",
  ``!t. is_comb t = (?u v. t = u @@ v)``,
  PROVE_TAC [term_CASES, is_comb_thm]);

Theorem is_comb_appstar_exists :
    !M. is_comb M <=> ?t args. (M = t @* args) /\ args <> [] /\ ~is_comb t
Proof
    HO_MATCH_MP_TAC simple_induction >> rw []
 >> reverse (Cases_on ‘is_comb M’)
 >- (qexistsl_tac [‘M’, ‘[M']’] >> rw [])
 >> FULL_SIMP_TAC std_ss [GSYM appstar_SNOC]
 >> qexistsl_tac [‘t’, ‘SNOC M' args’] >> rw []
QED

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

Theorem enf_vsubst_invariant[simp]:
  !t. enf ([VAR v/u] t) = enf t
Proof
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, enf_thm] THEN
  SRW_TAC [boolSimps.CONJ_ss][GSYM rand_subst_commutes, subst_eq_var] THEN
  SRW_TAC [][GSYM rator_subst_commutes, FV_SUB]
QED

Definition benf_def:  benf t <=> bnf t /\ enf t
End

Definition has_bnf_def: has_bnf t = ?t'. t == t' /\ bnf t'
End

Definition has_benf_def: has_benf t = ?t'. lameta t t' /\ benf t'
End

Theorem lameq_ssub_cong :
  !M N. M == N ==> ∀fm. fm ' M == fm ' N
Proof
  HO_MATCH_MP_TAC lameq_ind_genX >> qexists ‘fmFV’ >>
  simp[PULL_EXISTS] >> rw[] >>
  simp[ssub_SUBST, lameq_BETA] >> metis_tac[lameq_rules]
QED

Theorem lameq_appstar_cong :
    !M N Ns. M == N ==> M @* Ns == N @* Ns
Proof
  Induct_on ‘Ns’ using SNOC_INDUCT >> rw [appstar_SNOC, lameq_APPL]
QED

Theorem lameq_LAMl_appstar_VAR[simp] :
    !xs. LAMl xs t @* (MAP VAR xs) == t
Proof
    Induct_on ‘xs’ >> rw []
 >> qabbrev_tac ‘M = LAMl xs t’
 >> qabbrev_tac ‘args :term list = MAP VAR xs’
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘M @* args’ >> art []
 >> MATCH_MP_TAC lameq_appstar_cong
 >> rw [Once lameq_cases]
 >> DISJ1_TAC >> qexistsl_tac [‘h’, ‘M’] >> rw []
QED

Theorem lameq_LAMl_appstar_reduce :
    !xs t args. DISJOINT (set xs) (FV t) /\ LENGTH xs = LENGTH args ==>
                LAMl xs t @* args == t
Proof
    Induct_on ‘xs’ >> rw []
 >> Cases_on ‘args’ >- fs []
 >> rw [GSYM appstar_CONS]
 >> qabbrev_tac ‘M = LAMl xs t’
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘M @* t'’
 >> reverse CONJ_TAC
 >- (qunabbrev_tac ‘M’ \\
     FIRST_X_ASSUM MATCH_MP_TAC >> fs [])
 >> MATCH_MP_TAC lameq_appstar_cong
 >> rw [Once lameq_cases] >> DISJ1_TAC
 >> qexistsl_tac [‘h’, ‘M’] >> art []
 >> MATCH_MP_TAC (GSYM lemma14b)
 >> rw [Abbr ‘M’, FV_LAMl]
QED

(* NOTE: The antecedent ‘DISJOINT (set vs) (BIGUION (IMAGE FV (set Ns)))’ is to
   guarantee that the iterate substitution at LHS is equivalent to the
   simultaneous substitution at RHS.
 *)
Theorem lameq_LAMl_appstar_ssub :
    !vs M Ns. ALL_DISTINCT vs /\ (LENGTH vs = LENGTH Ns) /\
              DISJOINT (set vs) (BIGUNION (IMAGE FV (set Ns))) ==>
              LAMl vs M @* Ns == (FEMPTY |++ ZIP (vs,Ns)) ' M
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘L = ZIP (vs,Ns)’
 >> ‘(Ns = MAP SND L) /\ (vs = MAP FST L)’ by rw [Abbr ‘L’, MAP_ZIP]
 >> FULL_SIMP_TAC std_ss []
 >> Q.PAT_X_ASSUM ‘ALL_DISTINCT (MAP FST L)’ MP_TAC
 >> Q.PAT_X_ASSUM ‘DISJOINT (set (MAP FST L)) _’ MP_TAC
 >> KILL_TAC
 >> Q.ID_SPEC_TAC ‘M’
 >> Induct_on ‘L’ >> rw []
 >- (Suff ‘FEMPTY |++ [] = FEMPTY :string |-> term’ >- rw [] \\
     rw [FUPDATE_LIST_EQ_FEMPTY])
 >> qabbrev_tac ‘v = FST h’
 >> qabbrev_tac ‘vs = MAP FST L’
 >> qabbrev_tac ‘N = SND h’
 >> qabbrev_tac ‘Ns = MAP SND L’
 (* RHS rewriting *)
 >> ‘h :: L = [h] ++ L’ by rw [] >> POP_ORW
 >> rw [FUPDATE_LIST_APPEND]
 >> Know ‘FEMPTY |++ [h] |++ L = FEMPTY |++ L |++ [h]’
 >- (MATCH_MP_TAC FUPDATE_LIST_APPEND_COMMUTES \\
     rw [DISJOINT_ALT])
 >> Rewr'
 >> rw [GSYM FUPDATE_EQ_FUPDATE_LIST]
 >> qabbrev_tac ‘fm = FEMPTY |++ L’
 >> FULL_SIMP_TAC std_ss []
 >> ‘FDOM fm = set vs’ by rw [Abbr ‘fm’, FDOM_FUPDATE_LIST]
 >> ‘h = (v,N)’ by rw [Abbr ‘v’, Abbr ‘N’] >> POP_ORW
 (* LHS rewriting *)
 >> Know ‘LAM v (LAMl vs M) @@ N == LAMl vs ([N/v] M)’
 >- (SIMP_TAC (betafy (srw_ss())) [] \\
     Suff ‘[N/v] (LAMl vs M) = LAMl vs ([N/v] M)’ >- rw [lameq_rules] \\
     MATCH_MP_TAC LAMl_SUB \\
     METIS_TAC [])
 >> DISCH_TAC
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘LAMl vs ([N/v] M) @* Ns’
 >> CONJ_TAC >- (MATCH_MP_TAC lameq_appstar_cong >> art [])
 >> Suff ‘(fm |+ (v,N)) ' M = fm ' ([N/v] M)’
 >- (Rewr' >> FIRST_X_ASSUM MATCH_MP_TAC >> rw [DISJOINT_ALT])
 >> Know ‘!n. n < LENGTH vs ==> v # fm ' (EL n vs)’
 >- (rw [Abbr ‘fm’] \\
    ‘LENGTH L = LENGTH vs’ by rw [Abbr ‘vs’, LENGTH_MAP] \\
     Know ‘(FEMPTY |++ L) ' (EL n vs) = EL n Ns’
     >- (MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM \\
         Q.EXISTS_TAC ‘n’ >> rw [] \\
        ‘m <> n’ by rw [] \\
         METIS_TAC [EL_ALL_DISTINCT_EL_EQ]) >> Rewr' \\
     Q.PAT_X_ASSUM ‘!s. _ ==> DISJOINT (set vs) s /\ v NOTIN s’
        (MP_TAC o (Q.SPEC ‘FV (EL n Ns)’)) \\
     Know ‘?x. FV (EL n Ns) = FV x /\ (x = N \/ MEM x Ns)’
     >- (Q.EXISTS_TAC ‘EL n Ns’ >> rw [MEM_EL] \\
         DISJ2_TAC >> Q.EXISTS_TAC ‘n’ >> rw [] \\
         rw [Abbr ‘Ns’, LENGTH_MAP]) \\
     RW_TAC std_ss [])
 >> DISCH_TAC
 (* final stage, applying ssub_update_apply_SUBST *)
 >> MATCH_MP_TAC ssub_update_apply_SUBST
 >> rw [MEM_EL]
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem lameq_LAMl_appstar_ssub_closed :
    !vs M Ns. ALL_DISTINCT vs /\ (LENGTH vs = LENGTH Ns) /\ EVERY closed Ns ==>
              LAMl vs M @* Ns == (FEMPTY |++ ZIP (vs,Ns)) ' M
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC lameq_LAMl_appstar_ssub >> art []
 >> rw [DISJOINT_ALT]
 >> rename1 ‘v # N’
 >> fs [EVERY_MEM, closed_def]
QED

(* NOTE: added ‘DISTINCT vs’ in all cases.

   This proof is now based on the newly added "term_laml_cases".
 *)
Theorem strange_cases :
    !M : term. (?vs M'. (M = LAMl vs M') /\ (size M' = 1) /\ ALL_DISTINCT vs) \/
               (?vs args t.
                         (M = LAMl vs (t @* args)) /\
                         ~(args = []) /\ ~is_comb t /\ ALL_DISTINCT vs)
Proof
    rpt STRIP_TAC
 >> MP_TAC (Q.SPEC ‘M’ (MATCH_MP term_laml_cases
                                (INST_TYPE [“:α” |-> “:string”] FINITE_EMPTY)))
 >> RW_TAC std_ss [DISJOINT_EMPTY]
 >| [ (* goal 1 (of 3) *)
      DISJ1_TAC >> qexistsl_tac [‘[]’, ‘VAR s’] >> rw [],
      (* goal 2 (of 3) *)
      DISJ2_TAC >> reverse (Cases_on ‘is_comb M1’)
      >- (qexistsl_tac [‘[]’, ‘[M2]’, ‘M1’] >> rw []) \\
     ‘?t args. (M1 = t @* args) /\ args <> [] /\ ~is_comb t’
         by METIS_TAC [is_comb_appstar_exists] \\
      qexistsl_tac [‘[]’, ‘SNOC M2 args’, ‘t’] >> rw [],
      (* goal 3 (of 3) *)
     ‘is_var Body \/ is_comb Body’ by METIS_TAC [term_cases]
      >- (DISJ1_TAC >> qexistsl_tac [‘v::vs’, ‘Body’] >> rw [] \\
          fs [is_var_cases]) \\
     ‘?t args. (Body = t @* args) /\ args <> [] /\ ~is_comb t’
         by METIS_TAC [is_comb_appstar_exists] \\
      DISJ2_TAC >> qexistsl_tac [‘v::vs’, ‘args’, ‘t’] >> rw [] ]
QED

val _ = remove_ovl_mapping "Y" {Thy = "chap2", Name = "Y"}

(*---------------------------------------------------------------------------*
 *  More combinators
 *---------------------------------------------------------------------------*)

(* permutator [1, p.247] *)
Definition permutator_def :
    permutator n = let Z = GENLIST n2s (SUC n);
                       z = LAST Z;
                   in
                       LAMl Z (VAR z @* MAP VAR (FRONT Z))
End

Theorem closed_permutator :
    !n. closed (permutator n)
Proof
    rw [closed_def, permutator_def, FV_LAMl]
 >> qabbrev_tac ‘Z = GENLIST n2s (SUC n)’
 >> ‘ALL_DISTINCT Z /\ LENGTH Z = SUC n’ by rw [Abbr ‘Z’, ALL_DISTINCT_GENLIST]
 >> ‘Z <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> qabbrev_tac ‘z = LAST Z’
 >> ‘MEM z Z’ by rw [Abbr ‘z’, MEM_LAST_NOT_NIL]
 >> Suff ‘{z} UNION set (FRONT Z) SUBSET set Z’ >- SET_TAC []
 >> rw [SUBSET_DEF]
 >> rfs [MEM_FRONT_NOT_NIL]
QED

(* |- FV (permutator n) = {} *)
Theorem FV_permutator[simp] =
        REWRITE_RULE [closed_def] closed_permutator |> SPEC_ALL

(* NOTE: The default permutator binding variables can be exchanged to another
   fresh list excluding any given set X.
 *)
Theorem permutator_alt :
    !X n. FINITE X ==>
          ?vs v. LENGTH vs = n /\ ALL_DISTINCT (SNOC v vs) /\
                 DISJOINT X (set (SNOC v vs)) /\
                 permutator n = LAMl vs (LAM v (VAR v @* MAP VAR vs))
Proof
    RW_TAC std_ss [permutator_def]
 >> qabbrev_tac ‘Z = GENLIST n2s (SUC n)’
 >> ‘ALL_DISTINCT Z /\ LENGTH Z = SUC n’ by rw [Abbr ‘Z’, ALL_DISTINCT_GENLIST]
 >> ‘Z <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> qabbrev_tac ‘z = LAST Z’
 >> ‘MEM z Z’ by rw [Abbr ‘z’, MEM_LAST_NOT_NIL]
 >> qabbrev_tac ‘M = VAR z @* MAP VAR (FRONT Z)’
 (* preparing for LAMl_ALPHA_ssub *)
 >> qabbrev_tac ‘Y = NEWS (SUC n) (set Z UNION X)’
 >> ‘FINITE (set Z UNION X)’ by rw []
 >> ‘ALL_DISTINCT Y /\ DISJOINT (set Y) (set Z UNION X) /\ LENGTH Y = SUC n’
       by rw [NEWS_def, Abbr ‘Y’]
 >> fs []
 >> Know ‘LAMl Z M = LAMl Y ((FEMPTY |++ ZIP (Z,MAP VAR Y)) ' M)’
 >- (MATCH_MP_TAC LAMl_ALPHA_ssub >> rw [DISJOINT_SYM] \\
     Suff ‘FV M = set Z’ >- METIS_TAC [DISJOINT_SYM] \\
     rw [Abbr ‘M’, FV_appstar] \\
    ‘Z = SNOC (LAST Z) (FRONT Z)’ by PROVE_TAC [SNOC_LAST_FRONT] \\
     POP_ORW \\
     simp [LIST_TO_SET_SNOC] \\
     rw [Once EXTENSION, MEM_MAP])
 >> Rewr'
 >> ‘Y <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> REWRITE_TAC [GSYM fromPairs_def]
 >> qabbrev_tac ‘fm = fromPairs Z (MAP VAR Y)’
 >> ‘FDOM fm = set Z’ by rw [FDOM_fromPairs, Abbr ‘fm’]
 >> qabbrev_tac ‘y = LAST Y’
 (* postfix for LAMl_ALPHA_ssub *)
 >> ‘!t. LAMl Y t = LAMl (SNOC y (FRONT Y)) t’
       by (ASM_SIMP_TAC std_ss [Abbr ‘y’, SNOC_LAST_FRONT]) >> POP_ORW
 >> REWRITE_TAC [LAMl_SNOC]
 >> Know ‘fm ' M = VAR y @* MAP VAR (FRONT Y)’
 >- (simp [Abbr ‘M’, ssub_appstar] \\
     Know ‘fm ' z = VAR y’
     >- (rw [Abbr ‘fm’, Abbr ‘z’, LAST_EL] \\
         Know ‘fromPairs Z (MAP VAR Y) ' (EL n Z) = EL n (MAP VAR Y)’
         >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw []) >> Rewr' \\
         rw [EL_MAP, Abbr ‘y’, LAST_EL]) >> Rewr' \\
     Suff ‘MAP ($' fm) (MAP VAR (FRONT Z)) = MAP VAR (FRONT Y)’ >- rw [] \\
     rw [LIST_EQ_REWRITE, LENGTH_FRONT] \\
     rename1 ‘i < n’ \\
     simp [EL_MAP, LENGTH_FRONT] \\
     Know ‘MEM (EL i (FRONT Z)) Z’
     >- (rw [MEM_EL] \\
         Q.EXISTS_TAC ‘i’ >> rw [] \\
         MATCH_MP_TAC EL_FRONT >> rw [LENGTH_FRONT, NULL_EQ]) \\
     rw [Abbr ‘fm’] \\
     Know ‘EL i (FRONT Z) = EL i Z’
     >- (MATCH_MP_TAC EL_FRONT >> rw [LENGTH_FRONT, NULL_EQ]) >> Rewr' \\
     Know ‘EL i (FRONT Y) = EL i Y’
     >- (MATCH_MP_TAC EL_FRONT >> rw [LENGTH_FRONT, NULL_EQ]) >> Rewr' \\
     Know ‘fromPairs Z (MAP VAR Y) ' (EL i Z) = EL i (MAP VAR Y)’
     >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw []) >> Rewr' \\
     rw [EL_MAP])
 >> Rewr'
 >> qexistsl_tac [‘FRONT Y’, ‘y’]
 >> rw [LENGTH_FRONT, ALL_DISTINCT_SNOC, SNOC_LAST_FRONT, Abbr ‘y’,
        ALL_DISTINCT_FRONT]
 >> Know ‘ALL_DISTINCT (SNOC (LAST Y) (FRONT Y))’
 >- rw [SNOC_LAST_FRONT]
 >> rw [ALL_DISTINCT_SNOC]
QED

(* TODO: The proof can be simplified using the previous permutator_alt *)
Theorem permutator_thm :
    !n N Ns. LENGTH Ns = n ==> permutator n @* Ns @@ N == N @* Ns
Proof
    RW_TAC std_ss [permutator_def]
 >> qabbrev_tac ‘n = LENGTH Ns’
 >> qabbrev_tac ‘Z = GENLIST n2s (SUC n)’
 >> qabbrev_tac ‘z = LAST Z’
 >> ‘ALL_DISTINCT Z /\ LENGTH Z = SUC n’ by rw [Abbr ‘Z’, ALL_DISTINCT_GENLIST]
 >> ‘Z <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> ‘MEM z Z’ by rw [Abbr ‘z’, MEM_LAST_NOT_NIL]
 >> qabbrev_tac ‘M = VAR z @* MAP VAR (FRONT Z)’
 (* preparing for LAMl_ALPHA_ssub *)
 >> qabbrev_tac ‘Y = NEWS (SUC n) (set Z UNION (BIGUNION (IMAGE FV (set Ns))))’
 >> Know ‘FINITE (set Z UNION (BIGUNION (IMAGE FV (set Ns))))’
 >- (rw [] >> rw [FINITE_FV])
 >> DISCH_TAC
 >> Know ‘ALL_DISTINCT Y /\
          DISJOINT (set Y) (set Z UNION (BIGUNION (IMAGE FV (set Ns)))) /\
          LENGTH Y = SUC n’
 >- (ASM_SIMP_TAC std_ss [NEWS_def, Abbr ‘Y’])
 >> rw []
 (* applying LAMl_ALPHA_ssub *)
 >> Know ‘LAMl Z M = LAMl Y ((FEMPTY |++ ZIP (Z,MAP VAR Y)) ' M)’
 >- (MATCH_MP_TAC LAMl_ALPHA_ssub >> rw [DISJOINT_SYM] \\
     Suff ‘FV M = set Z’ >- METIS_TAC [DISJOINT_SYM] \\
     rw [Abbr ‘M’, FV_appstar] \\
    ‘Z = SNOC (LAST Z) (FRONT Z)’ by PROVE_TAC [SNOC_LAST_FRONT] \\
     POP_ORW \\
     simp [LIST_TO_SET_SNOC] \\
     rw [Once EXTENSION, MEM_MAP] \\
     EQ_TAC >> rw [] >> fs [] \\
     DISJ2_TAC \\
     Q.EXISTS_TAC ‘FV (VAR x)’ >> rw [] \\
     Q.EXISTS_TAC ‘VAR x’ >> rw [])
 >> Rewr'
 >> ‘Y <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> REWRITE_TAC [GSYM fromPairs_def]
 >> qabbrev_tac ‘fm = fromPairs Z (MAP VAR Y)’
 >> ‘FDOM fm = set Z’ by rw [FDOM_fromPairs, Abbr ‘fm’]
 >> qabbrev_tac ‘y = LAST Y’
 (* postfix for LAMl_ALPHA_ssub *)
 >> ‘!t. LAMl Y t = LAMl (SNOC y (FRONT Y)) t’
       by (ASM_SIMP_TAC std_ss [Abbr ‘y’, SNOC_LAST_FRONT]) >> POP_ORW
 >> REWRITE_TAC [LAMl_SNOC]
 >> Know ‘fm ' M = VAR y @* MAP VAR (FRONT Y)’
 >- (simp [Abbr ‘M’, ssub_appstar] \\
     Know ‘fm ' z = VAR y’
     >- (rw [Abbr ‘fm’, Abbr ‘z’, LAST_EL] \\
         Know ‘fromPairs Z (MAP VAR Y) ' (EL n Z) = EL n (MAP VAR Y)’
         >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw []) >> Rewr' \\
         rw [EL_MAP, Abbr ‘y’, LAST_EL]) >> Rewr' \\
     Suff ‘MAP ($' fm) (MAP VAR (FRONT Z)) = MAP VAR (FRONT Y)’ >- rw [] \\
     rw [LIST_EQ_REWRITE, LENGTH_FRONT] \\
     rename1 ‘i < n’ \\
     simp [EL_MAP, LENGTH_FRONT] \\
     Know ‘MEM (EL i (FRONT Z)) Z’
     >- (rw [MEM_EL] \\
         Q.EXISTS_TAC ‘i’ >> rw [] \\
         MATCH_MP_TAC EL_FRONT >> rw [LENGTH_FRONT, NULL_EQ]) \\
     rw [Abbr ‘fm’] \\
     Know ‘EL i (FRONT Z) = EL i Z’
     >- (MATCH_MP_TAC EL_FRONT >> rw [LENGTH_FRONT, NULL_EQ]) >> Rewr' \\
     Know ‘EL i (FRONT Y) = EL i Y’
     >- (MATCH_MP_TAC EL_FRONT >> rw [LENGTH_FRONT, NULL_EQ]) >> Rewr' \\
     Know ‘fromPairs Z (MAP VAR Y) ' (EL i Z) = EL i (MAP VAR Y)’
     >- (MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw []) >> Rewr' \\
     rw [EL_MAP])
 >> Rewr'
 (* stage work *)
 >> qabbrev_tac ‘t = LAM y (VAR y @* MAP VAR (FRONT Y))’
 >> MATCH_MP_TAC lameq_TRANS
 >> Q.EXISTS_TAC ‘((FEMPTY |++ ZIP (FRONT Y,Ns)) ' t) @@ N’
 >> CONJ_TAC
 >- (MATCH_MP_TAC lameq_APPL \\
     MATCH_MP_TAC lameq_LAMl_appstar_ssub \\
     rw [ALL_DISTINCT_FRONT, LENGTH_FRONT] \\
     MATCH_MP_TAC DISJOINT_SUBSET' \\
     Q.EXISTS_TAC ‘set Y’ \\
     reverse CONJ_TAC >- rw [SUBSET_DEF, MEM_FRONT_NOT_NIL] \\
     ONCE_REWRITE_TAC [DISJOINT_SYM] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘x’ >> art [])
 (* cleanup ‘fm’ *)
 >> Q.PAT_X_ASSUM ‘FDOM fm = set Z’ K_TAC
 >> qunabbrev_tac ‘fm’
 (* stage work *)
 >> REWRITE_TAC [GSYM fromPairs_def]
 >> qabbrev_tac ‘fm = fromPairs (FRONT Y) Ns’
 >> ‘FDOM fm = set (FRONT Y)’ by rw [Abbr ‘fm’, FDOM_fromPairs, LENGTH_FRONT]
 >> qunabbrev_tac ‘t’
 >> qabbrev_tac ‘t = VAR y @* MAP VAR (FRONT Y)’
 >> Know ‘fm ' (LAM y t) = LAM y (fm ' t)’
 >- (MATCH_MP_TAC ssub_LAM \\
     simp [Abbr ‘y’, LAST_EL] \\
     CONJ_TAC
     >- (simp [MEM_EL, LENGTH_FRONT, GSYM ADD1] \\
         Q.X_GEN_TAC ‘i’ \\
         ONCE_REWRITE_TAC [DECIDE “P ==> ~Q <=> Q ==> ~P”] \\
         DISCH_TAC \\
         Know ‘EL i (FRONT Y) = EL i Y’
         >- (MATCH_MP_TAC EL_FRONT >> rw [LENGTH_FRONT, NULL_EQ, GSYM ADD1]) \\
         Rewr' \\
         rw [ALL_DISTINCT_EL_IMP]) \\
     Q.X_GEN_TAC ‘y’ \\
     rw [MEM_EL, GSYM ADD1] >> rename1 ‘i < LENGTH (FRONT Y)’ \\
     qunabbrev_tac ‘fm’ \\
     Know ‘fromPairs (FRONT Y) Ns ' (EL i (FRONT Y)) = EL i Ns’
     >- (MATCH_MP_TAC fromPairs_FAPPLY_EL \\
         rw [ALL_DISTINCT_FRONT, LENGTH_FRONT]) >> Rewr' \\
     Know ‘DISJOINT (FV (EL i Ns)) (set Y)’
     >- (FIRST_X_ASSUM MATCH_MP_TAC \\
         Q.EXISTS_TAC ‘EL i Ns’ >> rw [MEM_EL] \\
         Q.EXISTS_TAC ‘i’ >> rfs [LENGTH_FRONT]) \\
     ONCE_REWRITE_TAC [DISJOINT_SYM] \\
     rw [DISJOINT_ALT] \\
     POP_ASSUM MATCH_MP_TAC >> rw [MEM_EL] \\
     Q.EXISTS_TAC ‘n’ >> rw [])
 >> Rewr'
 >> Q.PAT_X_ASSUM ‘FDOM fm = set (FRONT Y)’ K_TAC
 >> simp [Abbr ‘fm’]
 >> ‘FDOM (fromPairs (FRONT Y) Ns) = set (FRONT Y)’
       by rw [FDOM_fromPairs, LENGTH_FRONT]
 >> Know ‘~MEM y (FRONT Y)’
 >- (simp [Abbr ‘y’, MEM_EL, LAST_EL, LENGTH_FRONT, GSYM ADD1] \\
     Q.X_GEN_TAC ‘i’ \\
     ONCE_REWRITE_TAC [DECIDE “P ==> ~Q <=> Q ==> ~P”] \\
     DISCH_TAC \\
     Know ‘EL i (FRONT Y) = EL i Y’
     >- (MATCH_MP_TAC EL_FRONT >> rw [LENGTH_FRONT, NULL_EQ]) >> Rewr' \\
     rw [ALL_DISTINCT_EL_IMP])
 >> DISCH_TAC
 >> simp [Abbr ‘t’, ssub_appstar]
 >> Know ‘MAP ($' (fromPairs (FRONT Y) Ns)) (MAP VAR (FRONT Y)) = Ns’
 >- (rw [LIST_EQ_REWRITE, LENGTH_FRONT] \\
     rw [MAP_MAP_o, LENGTH_FRONT, EL_MAP]
     >- (MATCH_MP_TAC fromPairs_FAPPLY_EL \\
         rw [LENGTH_FRONT, ALL_DISTINCT_FRONT]) \\
     NTAC 2 (POP_ASSUM MP_TAC) \\
     simp [GSYM ADD1, MEM_EL, LENGTH_FRONT] \\
     METIS_TAC [])
 >> Rewr'
 >> Suff ‘N @* Ns = [N/y] (VAR y @* Ns)’
 >- (Rewr' >> rw [lameq_BETA])
 >> simp [appstar_SUB]
 >> Suff ‘MAP [N/y] Ns = Ns’ >- rw []
 >> rw [LIST_EQ_REWRITE, EL_MAP]
 >> rename1 ‘i < n’
 >> MATCH_MP_TAC lemma14b
 >> Know ‘DISJOINT (FV (EL i Ns)) (set Y)’
 >- (FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘EL i Ns’ >> rw [MEM_EL] \\
     Q.EXISTS_TAC ‘i’ >> art [])
 >> ONCE_REWRITE_TAC [DISJOINT_SYM]
 >> rw [DISJOINT_ALT]
 >> POP_ASSUM MATCH_MP_TAC
 >> rw [Abbr ‘y’, MEM_LAST_NOT_NIL]
QED

Definition selector_def :
    selector i n = LAMl (GENLIST n2s n) (VAR (n2s i))
End

Theorem closed_selector :
    !i n. i < n ==> closed (selector i n)
Proof
    rw [closed_def, selector_def, FV_LAMl]
 >> POP_ASSUM MP_TAC >> rw [MEM_GENLIST]
QED

(* |- !i n. i < n ==> FV (selector i n) = {} *)
Theorem FV_selector[simp] = REWRITE_RULE [closed_def] closed_selector

Theorem selector_thm :
    !i n Ns. i < n /\ LENGTH Ns = n ==> selector i n @* Ns == EL i Ns
Proof
    RW_TAC std_ss [selector_def]
 >> qabbrev_tac ‘n = LENGTH Ns’
 >> qabbrev_tac ‘Z = GENLIST n2s n’
 >> ‘ALL_DISTINCT Z /\ LENGTH Z = n’ by rw [Abbr ‘Z’, ALL_DISTINCT_GENLIST]
 >> ‘Z <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> qabbrev_tac ‘z = n2s i’
 >> Know ‘MEM z Z’
 >- (rw [Abbr ‘Z’, Abbr ‘z’, MEM_GENLIST] \\
     Q.EXISTS_TAC ‘i’ >> art [])
 >> DISCH_TAC
 (* preparing for LAMl_ALPHA_ssub *)
 >> qabbrev_tac
     ‘Y = NEWS n (set Z UNION (BIGUNION (IMAGE FV (set Ns))))’
 >> Know ‘FINITE (set Z UNION (BIGUNION (IMAGE FV (set Ns))))’
 >- (rw [] >> rw [FINITE_FV])
 >> DISCH_TAC
 >> Know ‘ALL_DISTINCT Y /\
          DISJOINT (set Y) (set Z UNION (BIGUNION (IMAGE FV (set Ns)))) /\
          LENGTH Y = n’
 >- (ASM_SIMP_TAC std_ss [NEWS_def, Abbr ‘Y’])
 >> rw []
 (* applying LAMl_ALPHA_ssub *)
 >> Know ‘LAMl Z (VAR z) = LAMl Y ((FEMPTY |++ ZIP (Z,MAP VAR Y)) ' (VAR z))’
 >- (MATCH_MP_TAC LAMl_ALPHA_ssub >> rw [] \\
     Q.PAT_X_ASSUM ‘DISJOINT (set Z) (set Y)’ MP_TAC \\
     rw [DISJOINT_ALT])
 >> Rewr'
 >> ‘Y <> []’ by rw [NOT_NIL_EQ_LENGTH_NOT_0]
 >> REWRITE_TAC [GSYM fromPairs_def]
 >> qabbrev_tac ‘fm = fromPairs Z (MAP VAR Y)’
 >> ‘FDOM fm = set Z’ by rw [FDOM_fromPairs, Abbr ‘fm’]
 >> Know ‘fm ' (VAR z) = EL i (MAP VAR Y)’
 >- (rw [ssub_thm] \\
     Know ‘z = EL i Z’
     >- (simp [Abbr ‘Z’, Abbr ‘z’] \\
         fs [LENGTH_GENLIST, EL_GENLIST]) >> Rewr' \\
     qunabbrev_tac ‘fm’ \\
     MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw [])
 >> Rewr'
 (* stage work *)
 >> qabbrev_tac ‘t = EL i (MAP VAR Y)’
 >> Suff ‘EL i Ns = (FEMPTY |++ ZIP (Y,Ns)) ' t’
 >- (Rewr' \\
     MATCH_MP_TAC lameq_LAMl_appstar_ssub >> rw [] \\
     ONCE_REWRITE_TAC [DISJOINT_SYM] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘x’ >> art [])
 (* cleanup ‘fm’ *)
 >> Q.PAT_X_ASSUM ‘FDOM fm = set Z’ K_TAC
 >> qunabbrev_tac ‘fm’
 (* stage work *)
 >> REWRITE_TAC [Once EQ_SYM_EQ, GSYM fromPairs_def]
 >> qabbrev_tac ‘fm = fromPairs Y Ns’
 >> ‘FDOM fm = set Y’ by rw [Abbr ‘fm’, FDOM_fromPairs]
 >> simp [Abbr ‘t’, EL_MAP]
 >> Know ‘MEM (EL i Y) Y’
 >- (rw [MEM_EL] \\
     Q.EXISTS_TAC ‘i’ >> rw [])
 >> Rewr
 >> Q.PAT_X_ASSUM ‘FDOM fm = set Y’ K_TAC
 >> simp [Abbr ‘fm’]
 >> MATCH_MP_TAC fromPairs_FAPPLY_EL >> rw []
QED

(* ----------------------------------------------------------------------
    closed terms and closures of (open or closed) terms, leading into
    B's Chapter 2's section “Solvable and unsolvable terms” p41.

    These definitions are stated again in Chapter 8 as per references
    below.
   ---------------------------------------------------------------------- *)

(* By prefixing a list of abstractions of FVs, any term can be "closed". The
   set ‘closures M’ represent such closures with different order of FVs.
 *)
Definition closures_def :
    closures M = {LAMl vs M | vs | ALL_DISTINCT vs /\ set vs = FV M}
End

Theorem closures_not_empty :
    !M. closures M <> {}
Proof
    Q.X_GEN_TAC ‘M’
 >> rw [GSYM MEMBER_NOT_EMPTY]
 >> Q.EXISTS_TAC ‘LAMl (SET_TO_LIST (FV M)) M’
 >> rw [closures_def]
 >> Q.EXISTS_TAC ‘SET_TO_LIST (FV M)’
 >> rw [SET_TO_LIST_INV]
QED

Theorem closures_of_closed[simp] :
    !M. closed M ==> closures M = {M}
Proof
    rw [closures_def, closed_def]
 >> rw [Once EXTENSION]
QED

Theorem closures_of_open_sing :
    !M v. FV M = {v} ==> closures M = {LAM v M}
Proof
    rw [closures_def, LIST_TO_SET_SING]
 >> rw [Once EXTENSION]
QED

(* ‘closure M’ is just one arbitrary element in ‘closures M’. *)
Overload closure = “\M. CHOICE (closures M)”

Theorem closure_in_closures :
    !M. closure M IN closures M
Proof
    rw [CHOICE_DEF, closures_not_empty]
QED

Theorem closure_idem[simp] :
    !M. closed M ==> closure M = M
Proof
    rw [closures_of_closed]
QED

Theorem closure_open_sing :
    !M v. FV M = {v} ==> closure M = LAM v M
Proof
    rpt STRIP_TAC
 >> ‘closures M = {LAM v M}’ by PROVE_TAC [closures_of_open_sing]
 >> rw []
QED

Theorem closed_closure[simp]:
  closed (closure M)
Proof
  qspec_then ‘M’ assume_tac closure_in_closures >> gvs[closures_def] >>
  simp[closed_def, appFOLDLTheory.FV_LAMl]
QED

(*---------------------------------------------------------------------------*
 * solvable terms and some equivalent definitions
 *---------------------------------------------------------------------------*)

(* 8.3.1 (ii) [1, p.171] *)
Definition solvable_def :
    solvable (M :term) = ?M' Ns. M' IN closures M /\ M' @* Ns == I
End

(* 8.3.1 (i) [1, p.171] *)
Theorem solvable_alt_closed :
    !M. closed M ==> (solvable M <=> ?Ns. M @* Ns == I)
Proof
    rw [solvable_def, closed_def]
QED

(* 8.3.1 (iii) [1, p.171] *)
Overload unsolvable = “\M. ~solvable M”

val _ = export_theory()
val _ = html_theory "chap2";

(* References:

   [1] Barendregt, H.P.: The Lambda Calculus, Its Syntax and Semantics.
       College Publications, London (1984).
   [2] Hankin, C.: Lambda Calculi: A Guide for Computer Scientists.
       Clarendon Press, Oxford (1994).
 *)
