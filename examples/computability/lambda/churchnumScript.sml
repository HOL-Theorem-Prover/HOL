open HolKernel boolLib bossLib Parse binderLib

open chap3Theory
open arithmeticTheory pred_setTheory
open termTheory appFOLDLTheory;
open boolSimps
open normal_orderTheory
open churchboolTheory
open churchpairTheory
open reductionEval
open stepsTheory

fun Store_thm(n,t,tac) = store_thm(n,t,tac) before export_rewrites [n]

val _ = new_theory "churchnum"

val church_def = Define`
  church n = LAM "z" (LAM "s" (FUNPOW (APP (VAR "s")) n (VAR "z")))
`

val church_11 = store_thm(
  "church_11",
  ``(church m = church n) ⇔ (m = n)``,
  SRW_TAC [][church_def, EQ_IMP_THM] THEN
  POP_ASSUM (MP_TAC o Q.AP_TERM `size`) THEN
  SRW_TAC [ARITH_ss][size_funpow, arithmeticTheory.LEFT_ADD_DISTRIB]);
val _ = export_rewrites ["church_11"]

val bnf_church = store_thm(
  "bnf_church",
  ``∀n. bnf (church n)``,
  SRW_TAC [][church_def] THEN
  Induct_on `n` THEN SRW_TAC [][] THEN
  SRW_TAC [][FUNPOW_SUC]);
val _ = export_rewrites ["bnf_church"]

val is_abs_church = Store_thm(
  "is_abs_church",
  ``is_abs (church n)``,
  SRW_TAC [][church_def]);

val church_lameq_11 = Store_thm(
  "church_lameq_11",
  ``(church m == church n) ⇔ (m = n)``,
  SRW_TAC [][EQ_IMP_THM, chap2Theory.lameq_rules] THEN
  `∃Z. church m -β->* Z ∧ church n -β->* Z`
     by METIS_TAC [beta_CR, theorem3_13, prop3_18] THEN
  `church m = church n`
     by METIS_TAC [corollary3_2_1, beta_normal_form_bnf, bnf_church] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val FV_church = store_thm(
  "FV_church",
  ``FV (church n) = {}``,
  SRW_TAC [][church_def] THEN
  `(n = 0) ∨ (∃m. n = SUC m)`
    by METIS_TAC [TypeBase.nchotomy_of ``:num``] THEN
  SRW_TAC [][] THENL [
    SRW_TAC [CONJ_ss] [EXTENSION],
    Q_TAC SUFF_TAC
          `FV (FUNPOW (APP (VAR "s")) (SUC m) (VAR "z")) = {"s"; "z"}`
          THEN1 SRW_TAC [CONJ_ss][pred_setTheory.EXTENSION] THEN
    Induct_on `m` THEN SRW_TAC [][] THENL [
      SRW_TAC [][EXTENSION],
      SRW_TAC [][Once FUNPOW_SUC] THEN
      SRW_TAC [][EXTENSION] THEN METIS_TAC []
    ]
  ]);
val _ = export_rewrites ["FV_church"]

val is_church_def = Define`
  is_church t =
    ∃f z n. f ≠ z ∧ (t = LAM z (LAM f (FUNPOW (APP (VAR f)) n (VAR z))))
`;


val church_is_church = Store_thm(
  "church_is_church",
  ``is_church (church n)``,
  SRW_TAC [][is_church_def, church_def] THEN
  `"z" ≠ "s"` by SRW_TAC [][] THEN METIS_TAC []);

val force_num_def = Define`
  force_num t = if is_church t then (@n. t = church n) else 0
`;

val force_num_church = Store_thm(
  "force_num_church",
  ``force_num (church n) = n``,
  SRW_TAC [][force_num_def]);

val force_num_church_composed = Store_thm(
  "force_num_church_composed",
  ``(force_num o church o f = f) ∧
    (force_num o church = I)``,
  SRW_TAC [][FUN_EQ_THM]);

val tpm_funpow_app = store_thm(
  "tpm_funpow_app",
  ``tpm pi (FUNPOW (APP f) n x) = FUNPOW (APP (tpm pi f)) n (tpm pi x)``,
  Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC]);
val _  = export_rewrites ["tpm_funpow_app"]

val FV_funpow_app = store_thm(
  "FV_funpow_app",
  ``FV (FUNPOW (APP f) n x) ⊆ FV f ∪ FV x``,
  Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC]);

val FV_funpow_app_I = store_thm(
  "FV_funpow_app_I",
  ``v ∈ FV x ⇒ v ∈ FV (FUNPOW (APP f) n x)``,
  Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC]);

val FV_funpow_app_E = store_thm(
  "FV_funpow_app_E",
  ``v ∈ FV (FUNPOW (APP f) n x) ⇒ v ∈ FV f ∨ v ∈ FV x``,
  MATCH_ACCEPT_TAC (REWRITE_RULE [IN_UNION, SUBSET_DEF] FV_funpow_app));

val fresh_funpow_app_I = store_thm(
  "fresh_funpow_app_I",
  ``v ∉ FV f ∧ v ∉ FV x ⇒ v ∉ FV (FUNPOW (APP f) n x)``,
  METIS_TAC [FV_funpow_app_E]);
val _ = export_rewrites ["fresh_funpow_app_I"]

val is_church_church = store_thm(
  "is_church_church",
  ``is_church t ⇒ ∃n. t = church n``,
  SRW_TAC [][is_church_def, church_def] THEN
  Q.EXISTS_TAC `n` THEN SRW_TAC [CONJ_ss][LAM_eq_thm] THEN
  Cases_on `z = "z"` THEN SRW_TAC [CONJ_ss][] THEN
  Cases_on `z = "s"` THEN SRW_TAC [CONJ_ss][]);

Theorem force_num_size:
  is_church t ⇒ (force_num t = size t DIV 2 - 1)
Proof
  SRW_TAC [][force_num_def] THEN
  ‘∃n. t = church n’ by METIS_TAC [is_church_church] THEN
  SRW_TAC [ARITH_ss][church_def, size_funpow]
QED

val SUB_funpow_app = store_thm(
  "SUB_funpow_app",
  ``[M:term/v] (FUNPOW (APP f) n x) = FUNPOW (APP ([M/v]f)) n ([M/v]x)``,
  Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC]);
val _ = export_rewrites ["SUB_funpow_app"]

val church_thm = bstore_thm(
  "church_thm",
  ``church 0 @@ x @@ f == x ∧
    church (SUC n) @@ x @@ f == f @@ (church n @@ x @@ f)``,
  CONJ_TAC THENL [
    SIMP_TAC (bsrw_ss()) [church_def] THEN FRESH_TAC THEN
    ASM_SIMP_TAC (bsrw_ss()) [],

    SIMP_TAC (bsrw_ss()) [church_def] THEN FRESH_TAC THEN
    ASM_SIMP_TAC (bsrw_ss()) [FUNPOW_SUC]
  ]);

val csuc_def = Define`
  csuc = LAM "n" (LAM "z" (LAM "s"
            (VAR "s" @@ (VAR "n" @@ VAR "z" @@ VAR "s"))))
`;
val FV_csuc = Store_thm(
  "FV_csuc",
  ``FV csuc = {}``,
  SRW_TAC [][csuc_def, EXTENSION] THEN METIS_TAC []);
val bnf_csuc = Store_thm(
  "bnf_csuc",
  ``bnf csuc``,
  SRW_TAC [][csuc_def]);

val csuc_behaviour = bstore_thm(
  "csuc_behaviour",
  ``∀n. (csuc @@ (church n)) -n->* church (SUC n)``,
  SIMP_TAC (bsrw_ss()) [csuc_def, church_def, FUNPOW_SUC]);

val church_eq = store_thm(
  "church_eq",
  ``(∀s. church n ≠ VAR s) ∧ (∀M N. church n ≠ M @@ N)``,
  SRW_TAC [][church_def]);
val _ = export_rewrites ["church_eq"]

val natrec_def = Define`
  natrec = LAM "z" (LAM "f" (LAM "n" (
             csnd @@ (VAR "n"
                          @@ (cpair @@ church 0 @@ VAR "z")
                          @@ (LAM "r" (cpair
                                         @@ (csuc @@ (cfst @@ VAR "r"))
                                         @@ (VAR "f" @@ (cfst @@ VAR "r")
                                                     @@ (csnd @@ VAR "r"))))))))
`;

val FV_natrec = Store_thm(
  "FV_natrec",
  ``FV natrec = {}``,
  SRW_TAC [][natrec_def, EXTENSION] THEN METIS_TAC []);
infix |> fun x |> f = f x
val lameq_sub = chap2Theory.lemma2_12 |> CONJUNCTS
                                      |> hd
                                      |> UNDISCH
                                      |> GEN_ALL
                                      |> DISCH_ALL
                                      |> GEN_ALL

val natrec_behaviour = bstore_thm(
  "natrec_behaviour",
  ``natrec @@ z @@ f @@ church 0 == z ∧
    natrec @@ z @@ f @@ church (SUC n) ==
       f @@ church n @@ (natrec @@ z @@ f @@ church n)``,
  CONJ_TAC THENL [
    SIMP_TAC (srw_ss()) [natrec_def] THEN FRESH_TAC THEN
    SRW_TAC [][tpm_fresh, lemma14b] THEN
    ASM_SIMP_TAC (bsrw_ss()) [],

    SIMP_TAC (srw_ss()) [natrec_def] THEN unvarify_tac lameq_sub THEN
    ASM_SIMP_TAC (bsrw_ss()) [] THEN
    Q.MATCH_ABBREV_TAC
      `VAR fs @@ NN0 @@ YY == VAR fs @@ NN1 @@ YY` THEN
    Q_TAC SUFF_TAC `NN0 == NN1` THEN1 SIMP_TAC (bsrw_ss()) [] THEN
    markerLib.UNABBREV_ALL_TAC THEN
    Q.ID_SPEC_TAC `n` THEN Induct THEN ASM_SIMP_TAC (bsrw_ss()) []
  ]);

val cplus_def = Define`
  cplus = LAM "m" (LAM "n" (VAR "m" @@ VAR "n" @@ csuc))
`;

val FV_cplus = Store_thm(
  "FV_cplus",
  ``FV cplus = {}``,
  SRW_TAC [][cplus_def, EXTENSION] THEN METIS_TAC []);
val is_abs_cplus = Store_thm(
  "is_abs_cplus",
  ``is_abs cplus``,
  SRW_TAC [][cplus_def]);

val cplus_behaviour = bstore_thm(
  "cplus_behaviour",
  ``cplus @@ church m @@ church n -n->* church (m + n)``,
  SIMP_TAC (bsrw_ss()) [cplus_def] THEN Induct_on `m` THEN
  ASM_SIMP_TAC (bsrw_ss()) [arithmeticTheory.ADD_CLAUSES]);

val cpred_def = Define`
  cpred = LAM "n" (natrec @@ church 0
                          @@ (LAM "n0" (LAM "r" (VAR "n0")))
                          @@ (VAR "n"))
`;
val FV_cpred = store_thm(
  "FV_cpred",
  ``FV cpred = {}``,
  SRW_TAC [][cpred_def, EXTENSION] THEN
  METIS_TAC []);
val _ = export_rewrites ["FV_cpred"]

val cpred_0 = store_thm(
  "cpred_0",
  ``cpred @@ church 0 -n->* church 0``,
  SIMP_TAC (bsrw_ss()) [cpred_def]);

val cpred_SUC = store_thm(
  "cpred_SUC",
  ``cpred @@ church (SUC n) -n->* church n``,
  SIMP_TAC (bsrw_ss()) [cpred_def]);

val cpred_behaviour = bstore_thm(
  "cpred_behaviour",
  ``cpred @@ church n -n->* church (PRE n)``,
  Cases_on `n` THEN SRW_TAC [][cpred_SUC, cpred_0]);

val cminus_def = Define`
  cminus = LAM "m" (LAM "n" (VAR "n" @@ VAR "m" @@ cpred))
`;
val FV_cminus = Store_thm(
  "FV_cminus",
  ``FV cminus = {}``,
  SRW_TAC [][cminus_def, EXTENSION] THEN METIS_TAC []);
val is_abs_cminus = Store_thm(
  "is_abs_cminus",
  ``is_abs cminus``,
  SRW_TAC [][cminus_def]);

val cminus_behaviour = bstore_thm(
  "cminus_behaviour",
  ``cminus @@ church m @@ church n -n->* church (m - n)``,
  SIMP_TAC (bsrw_ss()) [cminus_def] THEN
  Q.ID_SPEC_TAC `m` THEN Induct_on `n` THEN
  ASM_SIMP_TAC (bsrw_ss()) [DECIDE ``m - SUC n = PRE (m - n)``]);

val cmult_def = Define`
  cmult = LAM "m" (LAM "n" (VAR "m" @@ church 0 @@ (cplus @@ VAR "n")))
`;
val FV_cmult = Store_thm(
  "FV_cmult",
  ``FV cmult = {}``,
  SRW_TAC [][cmult_def, EXTENSION] THEN METIS_TAC []);

val cmult_behaviour = bstore_thm(
  "cmult_behaviour",
  ``cmult @@ church m @@ church n -n->* church (m * n)``,
  SIMP_TAC (bsrw_ss()) [cmult_def] THEN Induct_on `m` THEN
  ASM_SIMP_TAC (bsrw_ss() ++ ARITH_ss) [arithmeticTheory.MULT_CLAUSES]);

(* predicates/relations *)
val cis_zero_def = Define`
  cis_zero = LAM "n" (VAR "n" @@ cB T @@ (LAM "x" (cB F)))
`;
val FV_cis_zero = Store_thm(
  "FV_cis_zero",
  ``FV cis_zero = {}``,
  SRW_TAC [][cis_zero_def, EXTENSION]);
val bnf_cis_zero = Store_thm(
  "bnf_cis_zero",
  ``bnf cis_zero``,
  SRW_TAC [][cis_zero_def]);

val cis_zero_behaviour = bstore_thm(
  "cis_zero_behaviour",
  ``cis_zero @@ church n -n->* cB (n = 0)``,
  Cases_on `n` THEN
  ASM_SIMP_TAC (bsrw_ss()) [cis_zero_def]);

val wh_cis_zero = store_thm(
  "wh_cis_zero",
  ``cis_zero @@ church n -w->* cB (n = 0)``,
  SRW_TAC [][cis_zero_def, church_def] THEN
  ASM_SIMP_TAC (whfy(srw_ss())) [] THEN
  Cases_on `n` THEN SRW_TAC [][FUNPOW_SUC] THEN
  ASM_SIMP_TAC (whfy(srw_ss())) []);

val ceqnat_def = Define`
  ceqnat =
  LAM "n"
    (VAR "n"
       @@ cis_zero
       @@ (LAM "r" (LAM "m"
            (cand @@ (cnot @@ (cis_zero @@ (VAR "m")))
                  @@ (VAR "r" @@ (cpred @@ (VAR "m")))))))
`;
val FV_ceqnat = Store_thm(
  "FV_ceqnat",
  ``FV ceqnat = {}``,
  SRW_TAC [][ceqnat_def, EXTENSION] THEN METIS_TAC []);

Theorem ceqnat_behaviour[betasimp]:
  ceqnat @@ church n @@ church m -n->* cB (n = m)
Proof
  SIMP_TAC (bsrw_ss()) [ceqnat_def] THEN
  Q.ID_SPEC_TAC ‘m’ THEN Induct_on ‘n’ THEN1
    SIMP_TAC (bsrw_ss()) [] THEN
  ASM_SIMP_TAC (bsrw_ss()) [] THEN
  Cases_on ‘m’ THEN SRW_TAC [][]
QED

(* $< 0 = λn. not (is_zero n)
   $< (SUC m) = λn. not (is_zero n) ∧ $< m (PRE n)
*)
val cless_def = Define`
  cless = LAM "m"
            (VAR "m" @@ (LAM "n" (cnot @@ (cis_zero @@ VAR "n")))
                     @@ (LAM "r"
                         (LAM "n" (cand
                                     @@ (cnot @@ (cis_zero @@ VAR "n"))
                                     @@ (VAR "r" @@ (cpred @@ VAR "n"))))))
`;
val FV_cless = Store_thm(
  "FV_cless",
  ``FV cless = {}``,
  SRW_TAC [][cless_def, EXTENSION] THEN METIS_TAC []);
val is_abs_cless = Store_thm(
  "is_abs_cless",
  ``is_abs cless``,
  SRW_TAC [][cless_def]);

val cless_behaviour = bstore_thm(
  "cless_behaviour",
  ``cless @@ church m @@ church n -n->* cB (m < n)``,
  SIMP_TAC (bsrw_ss()) [cless_def] THEN
  Q.ID_SPEC_TAC `n` THEN Induct_on `m` THENL [
    SIMP_TAC (bsrw_ss()) [arithmeticTheory.NOT_ZERO_LT_ZERO],
    ASM_SIMP_TAC (bsrw_ss()) [] THEN
    Cases_on `n` THEN SRW_TAC [][]
  ]);

(* ----------------------------------------------------------------------
    divmod

    Functional presentation would be

     divmod (a,p,q) = if q = 0 then (0,0) else
                      if p < q then (a,p)
                      else divmod (a+1,p-q,q)

    But this is not primitive recursive.  We make it so by passing in
    an extra argument which is the "target" value for the next recursive
    step.  The primitive recursion does nothing until it hits a target
    value, which it then can set up appropriately for the next bit.

    In this setting the "target" is parameter p, which is where the
    recursion is happening.

     divmod 0 (a,p,q) = if p < q then (a,p) else (0,0)
     divmod (SUC n) (a,p,q) =
       if SUC n = p then
         if p < q then (a,p)
         else divmod n (a+1,p-q,q)
       else divmod n (a,p,q)

     We can optimise a little by having q be lifted past the recursion.

   ---------------------------------------------------------------------- *)

val cdivmodt_def = Define`
  cdivmodt = LAM "q"
   (LAM "n"
    (natrec
      @@ cpair
      @@ (LAM "n0" (LAM "r" (LAM "a" (LAM "p"
              (ceqnat @@ (csuc @@ VAR "n0") @@ VAR "p"
                      @@ (cless @@ VAR "p" @@ VAR "q"
                           @@ (cpair @@ VAR "a" @@ VAR "p")
                           @@ (VAR "r" @@
                                 (csuc @@ VAR "a") @@
                                 (cminus @@ VAR "p" @@ VAR "q")))
                      @@ (VAR "r" @@ VAR "a" @@ VAR "p"))))))
      @@ VAR "n"))
`;

val FV_cdivmodt = Store_thm(
  "FV_cdivmodt",
  ``FV cdivmodt = {}``,
  SRW_TAC [][cdivmodt_def, EXTENSION] THEN METIS_TAC []);

val cdivmodt_behaviour = store_thm(
  "cdivmodt_behaviour",
  ``∀p a.
       0 < q ∧ p ≤ n ⇒
       cdivmodt @@ church q @@ church n @@ church a @@ church p -n->*
       cvpr (church (a + p DIV q)) (church (p MOD q))``,
  SIMP_TAC (bsrw_ss()) [cdivmodt_def, cpair_behaviour] THEN
  Induct_on `n` THENL [
    SIMP_TAC (bsrw_ss()) [arithmeticTheory.ZERO_DIV, cpair_behaviour],

    ASM_SIMP_TAC (bsrw_ss()) [] THEN
    REPEAT STRIP_TAC THEN
    Cases_on `p = SUC n` THEN ASM_SIMP_TAC (bsrw_ss()) [] THENL [
      Cases_on `SUC n < q` THEN ASM_SIMP_TAC (bsrw_ss()) [] THENL [
        ASM_SIMP_TAC (bsrw_ss()) [arithmeticTheory.LESS_DIV_EQ_ZERO],
        ASM_SIMP_TAC (bsrw_ss() ++ ARITH_ss) [] THEN
        `(SUC n - q) DIV q = SUC n DIV q - 1`
           by (MP_TAC (Q.INST [`n` |-> `q`, `q` |-> `1`,
                                    `m` |-> `SUC n`]
                                   arithmeticTheory.DIV_SUB) THEN
               SRW_TAC [ARITH_ss][]) THEN
        `(SUC n - q) MOD q = SUC n MOD q`
           by (MP_TAC (Q.INST [`n` |-> `q`, `q` |-> `1`, `m` |-> `SUC n`]
                              arithmeticTheory.MOD_SUB) THEN
               SRW_TAC [ARITH_ss][]) THEN
        SRW_TAC [ARITH_ss][] THEN
        `∀x y. (x = y) ⇒ x == y` by SRW_TAC [][] THEN
        POP_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN
        Q_TAC SUFF_TAC `0 < SUC n DIV q` THEN1 DECIDE_TAC THEN
        SRW_TAC [ARITH_ss][arithmeticTheory.X_LT_DIV]
      ],
      SRW_TAC [ARITH_ss][]
    ]
  ]);

val cdiv_def = Define`
  cdiv =
  LAM "p" (LAM "q"
    (cfst @@ (cdivmodt @@ VAR "q" @@ VAR "p" @@ church 0 @@ VAR "p")))
`
val FV_cdiv = Store_thm(
  "FV_cdiv",
  ``FV cdiv = {}``,
  SIMP_TAC bool_ss [cdiv_def, EXTENSION, NOT_IN_EMPTY] THEN
  SRW_TAC [][FRESH_APP, FRESH_LAM]);

val cdiv_behaviour = bstore_thm(
  "cdiv_behaviour",
  ``0 < q ⇒
      cdiv @@ church p @@ church q -n->* church (p DIV q)``,
  SIMP_TAC (bsrw_ss()) [cdivmodt_behaviour, cdiv_def]);

val cmod_def = Define`
  cmod = LAM "p" (LAM "q"
           (csnd @@ (cdivmodt @@ VAR "q" @@ VAR "p" @@ church 0 @@ VAR "p")))
`;
val FV_cmod = Store_thm(
  "FV_cmod",
  ``FV cmod = {}``,
  SRW_TAC [][cmod_def, EXTENSION] THEN METIS_TAC [])

val cmod_behaviour = bstore_thm(
  "cmod_behaviour",
  ``0 < q ⇒
     cmod @@ church p @@ church q -n->* church (p MOD q)``,
  SIMP_TAC (bsrw_ss()) [cdivmodt_behaviour, cmod_def]);

(* ----------------------------------------------------------------------
    Exponentiation
   ---------------------------------------------------------------------- *)

val cexp_def = Define`
  cexp = LAM "m" (LAM "n" (VAR "n" @@ church 1 @@ (cmult @@ VAR "m")))
`;

Theorem FV_cexp[simp]:
  FV cexp = {}
Proof
  rw[cexp_def,EXTENSION] >> metis_tac[]
QED

val cexp_eqn = brackabs.brackabs_equiv [] cexp_def

Theorem cexp_behaviour:
  cexp @@ m @@ church 0 == church 1 ∧
  cexp @@ m @@ church (SUC n) == cmult @@ m @@ (cexp @@ m @@ church n)
Proof
  asm_simp_tac(bsrw_ss())[cexp_eqn]
QED

Theorem cexp_corr[betasimp]:
  cexp @@ church m @@ church n == church (m**n)
Proof
  Induct_on`n` >>  asm_simp_tac(bsrw_ss())[cexp_behaviour,arithmeticTheory.EXP]
QED

(* ----------------------------------------------------------------------
    Pairs of numbers
   ---------------------------------------------------------------------- *)

val cnvpr_def = Define`
  cnvpr (n,m) = cvpr (church n) (church m)
`;

val bnf_cnvpr = Store_thm(
  "bnf_cnvpr",
  ``bnf (cnvpr p)``,
  Cases_on `p` THEN SRW_TAC [][cnvpr_def]);

val FV_cnvpr = Store_thm(
  "FV_cnvpr",
  ``FV (cnvpr p) = {}``,
  Cases_on `p` THEN SRW_TAC [][cnvpr_def]);

val cfst_cnvpr = bstore_thm(
  "cfst_cnvpr",
  ``cfst @@ cnvpr p -n->* church (FST p)``,
  Cases_on `p` THEN SIMP_TAC (bsrw_ss())[cnvpr_def]);
val csnd_cnvpr = bstore_thm(
  "csnd_cnvpr",
  ``csnd @@ cnvpr p -n->* church (SND p)``,
  Cases_on `p` THEN SIMP_TAC (bsrw_ss())[cnvpr_def]);


(* ----------------------------------------------------------------------
    Numeric pairing
   ---------------------------------------------------------------------- *)

open numpairTheory

(* triangular numbers and the tri⁻¹ function *)
val ctri_def = Define`
  ctri = LAM "n" (natrec @@ church 0
                         @@ (LAM "n0" (cplus @@ (csuc @@ VAR "n0")))
                         @@ VAR "n")
`;

val FV_ctri = Store_thm(
  "FV_ctri",
  ``FV ctri = {}``,
  SRW_TAC [][ctri_def, EXTENSION] THEN METIS_TAC []);

val ctri_behaviour = bstore_thm(
  "ctri_behaviour",
  ``ctri @@ church n -n->* church (tri n)``,
  SIMP_TAC (bsrw_ss()) [ctri_def] THEN
  Induct_on `n` THEN
  ASM_SIMP_TAC (bsrw_ss()) [tri_def]);

(* invtri0
    |- ∀n a.
         invtri0 n a =
         if n < a + 1 then (n,a) else invtri0 (n − (a + 1)) (a + 1) : thm
   make it prim. rec. by using a target parameter, as with divmod
*)

val cinvtri0_def = Define`
  cinvtri0 =
  natrec
    @@ (LAM "n" (LAM "a" (cvpr (VAR "n") (VAR "a"))))
    @@ (LAM "t0" (LAM "r" (LAM "n" (LAM "a"
          (ceqnat @@ (csuc @@ (VAR "t0")) @@ VAR "n"
                  @@ (cless @@ VAR "n" @@ (csuc @@ VAR "a")
                            @@ cvpr (VAR "n") (VAR "a")
                            @@ (VAR "r"
                                    @@ (cminus @@ VAR "n"
                                               @@ (csuc @@ VAR "a"))
                                    @@ (csuc @@ VAR "a")))
                  @@ (VAR "r" @@ VAR "n" @@ VAR "a"))))))
`;
(* have messed my naming up here in order to keep the "n" and "a" of the
   original definition.  "t" is the parameter that is being recursed on,
   and "n" is the target parameter that causes things to happen when t reaches
   it. *)

val FV_cinvtri0 = Store_thm(
  "FV_cinvtri0",
  ``FV cinvtri0 = {}``,
  SRW_TAC [][cinvtri0_def, EXTENSION] THEN METIS_TAC []);

val cinvtri0_behaviour = store_thm(
  "cinvtri0_behaviour",
  ``n ≤ t ⇒
    cinvtri0 @@ church t @@ church n @@ church a -n->*
    cnvpr (invtri0 n a)``,
  SIMP_TAC (bsrw_ss()) [cinvtri0_def] THEN
  Q.ID_SPEC_TAC `n` THEN Q.ID_SPEC_TAC `a` THEN
  Induct_on `t` THENL [
    SIMP_TAC (bsrw_ss()) [] THEN
    ONCE_REWRITE_TAC [invtri0_def] THEN
    SIMP_TAC (srw_ss() ++ ARITH_ss) [cnvpr_def],

    SIMP_TAC (bsrw_ss()) [] THEN
    REPEAT STRIP_TAC THEN Cases_on `n = SUC t` THEN
    ASM_SIMP_TAC (bsrw_ss()) [] THENL [
      Cases_on `t < a` THENL [
        ASM_SIMP_TAC (bsrw_ss()) [] THEN
        ONCE_REWRITE_TAC [invtri0_def] THEN
        SRW_TAC [ARITH_ss][cnvpr_def],

        ASM_SIMP_TAC (bsrw_ss()) [] THEN
        CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [invtri0_def])) THEN
        SRW_TAC [ARITH_ss][] THEN
        `SUC t - (a + 1) = t - a` by DECIDE_TAC THEN
        SRW_TAC [][arithmeticTheory.ADD1]
      ],

      `n ≤ t` by DECIDE_TAC THEN
      ASM_SIMP_TAC (bsrw_ss()) []
    ]
  ]);

val cinvtri_def = Define`
  cinvtri =
  LAM "n" (csnd @@ (cinvtri0 @@ VAR "n" @@ VAR "n" @@ church 0))
`;

val FV_cinvtri = Store_thm(
  "FV_cinvtri",
  ``FV cinvtri = {}``,
  SRW_TAC [][cinvtri_def, EXTENSION] THEN METIS_TAC []);

val cinvtri_behaviour = bstore_thm(
  "cinvtri_behaviour",
  ``cinvtri @@ church n -n->* church (tri⁻¹ n)``,
  SIMP_TAC (bsrw_ss()) [cinvtri_def, cinvtri0_behaviour, invtri_def]);

(* -- The pairing function and fst and snd *)

val cnpair_def = Define`
  cnpair =
  LAM "n" (LAM "m"
    (cplus @@ (ctri @@ (cplus @@ VAR "n" @@ VAR "m")) @@ VAR "m"))
`;

val FV_cnpair = Store_thm(
  "FV_cnpair",
  ``FV cnpair = {}``,
  SRW_TAC [][cnpair_def, EXTENSION] THEN METIS_TAC []);

val cnpair_behaviour = bstore_thm(
  "cnpair_behaviour",
  ``cnpair @@ church n @@ church m -n->* church (n ⊗ m)``,
  SIMP_TAC (bsrw_ss()) [cnpair_def, npair_def]);

(* cnfst *)
val cnfst_def = Define`
  cnfst = LAM "n" (cminus
                     @@ (cplus @@ (ctri @@ (cinvtri @@ VAR "n"))
                               @@ (cinvtri @@ VAR "n"))
                     @@ VAR "n")
`;

val FV_cnfst = Store_thm(
  "FV_cnfst",
  ``FV cnfst = {}``,
  SRW_TAC [][cnfst_def, EXTENSION] THEN METIS_TAC []);

val cnfst_behaviour = bstore_thm(
  "cnfst_behaviour",
  ``cnfst @@ church p -n->* church (nfst p)``,
  SIMP_TAC (bsrw_ss()) [cnfst_def, nfst_def]);

(* cnsnd *)
val cnsnd_def = Define`
  cnsnd = LAM "n" (cminus @@ VAR "n"
                          @@ (ctri @@ (cinvtri @@ VAR "n")))
`;

val FV_cnsnd = Store_thm(
  "FV_cnsnd",
  ``FV cnsnd = {}``,
  SRW_TAC [][cnsnd_def, EXTENSION] THEN METIS_TAC []);

val cnsnd_behaviour = bstore_thm(
  "cnsnd_behaviour",
  ``cnsnd @@ church p -n->* church (nsnd p)``,
  SIMP_TAC (bsrw_ss()) [cnsnd_def, nsnd_def]);

(* ----------------------------------------------------------------------
    cfindleast
   ---------------------------------------------------------------------- *)

val cfindbody_def = Define`
  cfindbody P N k =
    let lp = NEW (FV P ∪ FV k) in
    let nv = NEW (FV P ∪ FV k ∪ {lp})
    in
        Yf (LAM lp (LAM nv (P @@ VAR nv
                              @@ (k @@ VAR nv)
                              @@ (VAR lp @@ (csuc @@ VAR nv))))) @@ N
`;

val fresh_cfindbody = store_thm(
  "fresh_cfindbody",
  ``lp ∉ FV P ∧ lp ∉ FV k ∧ nv ≠ lp ∧ nv ∉ FV P ∧ nv ∉ FV k ⇒
    (cfindbody P N k =
     Yf (LAM lp (LAM nv (P @@ VAR nv @@ (k @@ VAR nv)
                           @@ (VAR lp @@ (csuc @@ VAR nv))))) @@
     N)``,
  SRW_TAC [][LET_THM, cfindbody_def] THEN
  binderLib.NEW_ELIM_TAC THEN REPEAT STRIP_TAC THEN
  binderLib.NEW_ELIM_TAC THEN REPEAT STRIP_TAC THEN
  SRW_TAC [][termTheory.LAM_eq_thm, termTheory.tpm_fresh] THEN
  Cases_on `nv = v` THEN SRW_TAC [][termTheory.tpm_fresh] THEN
  Cases_on `lp = v'` THEN SRW_TAC [][termTheory.tpm_fresh] THEN
  METIS_TAC []);

val cfindbody_SUB = Store_thm(
  "cfindbody_SUB",
  ``[Q/v] (cfindbody P N k) = cfindbody ([Q/v]P) ([Q/v]N) ([Q/v]k)``,
  Q_TAC (NEW_TAC "lp") `FV P ∪ FV k ∪ FV Q ∪ {v}` THEN
  Q_TAC (NEW_TAC "nv") `FV P ∪ FV k ∪ FV Q ∪ {v;lp}` THEN
  `cfindbody P N k = Yf (LAM lp (LAM nv (P @@ VAR nv @@ (k @@ VAR nv)
                                           @@ (VAR lp @@ (csuc @@ VAR nv))))) @@
                     N`
    by SRW_TAC [][fresh_cfindbody] THEN
  `cfindbody ([Q/v]P) ([Q/v]N) ([Q/v]k) =
   Yf (LAM lp (LAM nv ([Q/v]P @@ VAR nv @@ ([Q/v]k @@ VAR nv)
                            @@ (VAR lp @@ (csuc @@ VAR nv))))) @@ [Q/v]N`
    by (MATCH_MP_TAC (GEN_ALL fresh_cfindbody) THEN
        SRW_TAC [][chap2Theory.NOT_IN_FV_SUB]) THEN
  SRW_TAC [][termTheory.lemma14b]);

val cfindbody_thm = store_thm(
  "cfindbody_thm",
  ``cfindbody P N k -w->* P @@ N @@ (k @@ N) @@ cfindbody P (csuc @@ N) k``,
  unvarify_tac head_reductionTheory.whstar_substitutive THEN
  SRW_TAC [][termTheory.lemma14b] THEN
  Q_TAC (NEW_TAC "z") `{Ps; ks}` THEN
  Q_TAC (NEW_TAC "nv") `{Ps; z; ks}` THEN
  `∀N. cfindbody (VAR Ps) N (VAR ks) =
       Yf (LAM z (LAM nv (VAR Ps @@ VAR nv @@ (VAR ks @@ VAR nv)
                              @@ (VAR z @@ (csuc @@ VAR nv)))))
       @@ N`
     by SRW_TAC [][fresh_cfindbody] THEN
  ASM_SIMP_TAC (whfy (srw_ss())) [MATCH_MP relationTheory.RTC_SUBSET
                                           head_reductionTheory.whY2]);

val cfindbody_cong = store_thm(
  "cfindbody_cong",
  ``P == P' ⇒ N == N' ⇒ k == k' ⇒ cfindbody P N k == cfindbody P' N' k'``,
  Q_TAC (NEW_TAC "lp") `FV P ∪ FV P' ∪ FV k ∪ FV k'` THEN
  Q_TAC (NEW_TAC "nv") `FV P ∪ FV P' ∪ FV k ∪ FV k' ∪ {lp}` THEN
  REPEAT STRIP_TAC THEN
  `(cfindbody P N k = Yf (LAM lp (LAM nv (P @@ VAR nv @@ (k @@ VAR nv)
                                         @@ (VAR lp @@ (csuc @@ VAR nv))))) @@
                   N) ∧
   (cfindbody P' N' k' =
      Yf (LAM lp (LAM nv (P' @@ VAR nv @@ (k' @@ VAR nv)
                             @@ (VAR lp @@ (csuc @@ VAR nv))))) @@
      N')`
    by SRW_TAC [][fresh_cfindbody] THEN
  ASM_SIMP_TAC (bsrw_ss()) []);

val bnf_cfindbody = Store_thm(
  "bnf_cfindbody",
  ``¬bnf (cfindbody P N k)``,
  SRW_TAC [][cfindbody_def, LET_THM]);

val FV_cfindbody = Store_thm(
  "FV_cfindbody",
  ``FV (cfindbody P N k) = FV P ∪ FV N ∪ FV k``,
  SRW_TAC [][cfindbody_def, EXTENSION, LET_THM] THEN
  NEW_ELIM_TAC THEN SRW_TAC [][] THEN
  NEW_ELIM_TAC THEN SRW_TAC [][] THEN METIS_TAC []);

val cfindleast_def = Define`
  cfindleast = LAM "P" (LAM "k" (cfindbody (VAR "P") (church 0) (VAR "k")))
`;

val FV_cfindleast = Store_thm(
  "FV_cfindleast",
  ``FV cfindleast = {}``,
  SRW_TAC [][cfindleast_def, pred_setTheory.EXTENSION] THEN METIS_TAC []);

val cfindleast_behaviour = store_thm(
  "cfindleast_behaviour",
  ``cfindleast @@ P @@ k == cfindbody P (church 0) k``,
  SIMP_TAC (bsrw_ss()) [cfindleast_def] THEN
  Q_TAC (NEW_TAC "kk") `FV P ∪ {"P"; "k"}` THEN
  `LAM "k" (cfindbody (VAR "P") (church 0) (VAR "k")) =
   LAM kk (cfindbody (VAR "P") (church 0) (VAR kk))`
     by (`cfindbody (VAR "P") (church 0) (VAR kk) =
           [VAR kk/"k"] (cfindbody (VAR "P") (church 0) (VAR "k"))`
           by SRW_TAC [][termTheory.lemma14b] THEN
         POP_ASSUM SUBST1_TAC THEN
         MATCH_MP_TAC termTheory.SIMPLE_ALPHA THEN SRW_TAC [][]) THEN
  POP_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC (bsrw_ss()) []);

val cfindleast_termI = store_thm(
  "cfindleast_termI",
  ``(∀n. ∃b. P @@ church n == cB b) ∧ P @@ church n == cB T ⇒
    cfindleast @@ P @@ k == k @@ church (LEAST n. P @@ church n == cB T)``,
  STRIP_TAC THEN numLib.LEAST_ELIM_TAC THEN CONJ_TAC THEN1 METIS_TAC [] THEN
  POP_ASSUM (K ALL_TAC) THEN
  SIMP_TAC (bsrw_ss()) [cfindleast_behaviour] THEN
  Q_TAC SUFF_TAC
    `∀p n. p ≤ n ∧
           (∀m. m < n ⇒ ¬(P @@ church m == cB T)) ∧
           P @@ church n == cB T ⇒
           cfindbody P (church p) k == k @@ church n`
    THEN1 METIS_TAC [DECIDE ``0 ≤ n``] THEN
  Induct_on `n - p` THEN REPEAT STRIP_TAC THENL [
    `p = n` by DECIDE_TAC THEN
    ASM_SIMP_TAC (bsrw_ss()) [Once cfindbody_thm],

    `p < n` by DECIDE_TAC THEN
    `∃r. P @@ church p == cB r` by METIS_TAC [] THEN
    `r = F` by (Cases_on `r` THEN METIS_TAC []) THEN
    ASM_SIMP_TAC (bsrw_ss()) [Once cfindbody_thm, Cong cfindbody_cong] THEN
    FIRST_X_ASSUM (fn th => MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] th)) THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);

val cfindbody_11 = Store_thm(
  "cfindbody_11",
  ``(cfindbody P1 N1 k1 = cfindbody P2 N2 k2) ⇔
      (P1 = P2) ∧ (N1 = N2) ∧ (k1 = k2)``,
  Q_TAC (NEW_TAC "lp") `FV P1 ∪ FV P2 ∪ FV k1 ∪ FV k2` THEN
  Q_TAC (NEW_TAC "nv") `FV P1 ∪ FV P2 ∪ FV k1 ∪ FV k2 ∪ {lp}` THEN
  `(cfindbody P1 N1 k1 = Yf (LAM lp (LAM nv (P1 @@ VAR nv @@ (k1 @@ VAR nv)
                                            @@ (VAR lp @@ (csuc @@ VAR nv)))))
                            @@ N1) ∧
   (cfindbody P2 N2 k2 = Yf (LAM lp (LAM nv (P2 @@ VAR nv @@ (k2 @@ VAR nv)
                                            @@ (VAR lp @@ (csuc @@ VAR nv)))))
                            @@ N2)`
      by SRW_TAC [][fresh_cfindbody] THEN
  SRW_TAC [][AC CONJ_ASSOC CONJ_COMM]);

val cfindleast_bnfE = store_thm(
  "cfindleast_bnfE",
  ``(∀n. ∃b. P @@ church n == cB b) ∧
    cfindleast @@ P @@ k == r ∧ bnf r ⇒
    ∃m. (r == k @@ church m) ∧ P @@ church m == cB T ∧
        ∀m₀. m₀ < m ⇒ P @@ church m₀ == cB F``,
  SIMP_TAC (bsrw_ss()) [cfindleast_behaviour] THEN
  REPEAT STRIP_TAC THEN
  `∃N. steps N (cfindbody P (church 0) k) = r`
    by METIS_TAC [nstar_steps, nstar_betastar_bnf,
                  chap3Theory.betastar_lameq_bnf] THEN
  Q_TAC SUFF_TAC
    `∀N cn ct. (steps N (cfindbody P ct k) = r) ⇒
               (∀c0. c0 < cn ⇒ P @@ church c0 == cB F) ⇒
               (ct == church cn) ⇒
               ∃m. (r == k @@ church m) ∧ P @@ church m == cB T ∧
                   ∀m₀. m₀ < m ⇒ P @@ church m₀ == cB F`
    THEN1 METIS_TAC [DECIDE ``¬(x < 0)``, chap2Theory.lameq_refl] THEN
  REPEAT (FIRST_X_ASSUM (fn th => if free_in ``cfindbody`` (concl th) then
                                    ALL_TAC
                                  else NO_TAC)) THEN
  completeInduct_on `N` THEN
  MAP_EVERY Q.X_GEN_TAC [`cn`,`ct`] THEN REPEAT STRIP_TAC THEN
  `cfindbody P ct k -n->* P @@ ct @@ (k @@ ct) @@ (cfindbody P (csuc @@ ct) k)`
     by METIS_TAC [cfindbody_thm, whstar_nstar] THEN
  `∃b. P @@ church cn == cB b` by METIS_TAC [] THEN
  Cases_on `b` THENL [
    `cfindbody P ct k == k @@ church cn`
      by ASM_SIMP_TAC (bsrw_ss()) [] THEN
    `cfindbody P ct k -n->* r` by METIS_TAC [steps_nstar] THEN
    METIS_TAC [nstar_lameq, chap2Theory.lameq_rules],

    `P @@ ct == cB F` by ASM_SIMP_TAC (bsrw_ss()) [] THEN
    POP_ASSUM (STRIP_ASSUME_TAC o
               MATCH_MP (GEN_ALL (CONJUNCT2 whead_tests))) THEN
    `cfindbody P ct k -n->* cfindbody P (csuc @@ ct) k`
      by METIS_TAC [whstar_nstar, relationTheory.RTC_CASES_RTC_TWICE] THEN
    `∃n1. cfindbody P (csuc @@ ct) k = steps n1 (cfindbody P ct k)`
      by METIS_TAC [nstar_steps] THEN
    `¬bnf (cfindbody P (csuc @@ ct) k)` by SRW_TAC [][] THEN
    `n1 < N` by METIS_TAC [DECIDE ``n:num < m ∨ (n = m) ∨ m < n``,
                           bnf_steps_upwards_closed] THEN
    `∃rest. N = rest + n1` by (Q.EXISTS_TAC `N - n1` THEN DECIDE_TAC) THEN
    FULL_SIMP_TAC (srw_ss()) [steps_plus] THEN
    `n1 ≠ 0` by (STRIP_TAC THEN
                 FULL_SIMP_TAC (srw_ss()) [termTheory.APP_acyclic]) THEN
    `rest < rest + n1` by DECIDE_TAC THEN
    POP_ASSUM (fn th1 => FIRST_X_ASSUM (MP_TAC o C MATCH_MP th1)) THEN
    DISCH_THEN (Q.SPECL_THEN [`SUC cn`, `csuc @@ ct`] MP_TAC) THEN
    ASM_SIMP_TAC (bsrw_ss()) [] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN
    `(c0 = cn) ∨ c0 < cn` by DECIDE_TAC THEN SRW_TAC [][]
  ]);

val ceven_def = Define‘
  ceven = LAM "n" (ceqnat @@ church 0 @@ (cmod @@ VAR "n" @@ church 2))
’;

Theorem FV_ceven[simp] :
  FV ceven = ∅
Proof
  simp[EXTENSION, ceven_def]
QED

val ceven_eqn = brackabs.brackabs_equiv [] ceven_def

Theorem ceven_behaviour:
  ceven @@ church n == cB (EVEN n)
Proof
  simp_tac (bsrw_ss()) [ceven_eqn, arithmeticTheory.EVEN_MOD2] >> metis_tac[]
QED

val _ = export_theory()
val _ = html_theory "churchnum";
