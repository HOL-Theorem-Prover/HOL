open HolKernel boolLib bossLib Parse binderLib

open chap3Theory
open pred_setTheory
open termTheory
open boolSimps
open normal_orderTheory
open churchboolTheory
open churchpairTheory
open reductionEval

fun Store_thm(n,t,tac) = store_thm(n,t,tac) before export_rewrites [n]

val _ = new_theory "churchnum"

val _ = set_trace "Unicode" 1

val church_def = Define`
  church n = LAM "z" (LAM "s" (FUNPOW ((@@) (VAR "s")) n (VAR "z")))
`

val FUNPOW_SUC = arithmeticTheory.FUNPOW_SUC

val size_funpow = store_thm(
  "size_funpow",
  ``size (FUNPOW ((@@) f) n x) = (size f + 1) * n + size x``,
  Induct_on `n` THEN
  SRW_TAC [ARITH_ss][FUNPOW_SUC, arithmeticTheory.LEFT_ADD_DISTRIB,
                     arithmeticTheory.MULT_CLAUSES]);

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

val church_lameq_11 = store_thm(
  "church_lameq_11",
  ``(church m == church n) ⇔ (m = n)``,
  SRW_TAC [][EQ_IMP_THM, chap2Theory.lam_eq_rules] THEN
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
          `FV (FUNPOW ((@@) (VAR "s")) (SUC m) (VAR "z")) = {"s"; "z"}`
          THEN1 SRW_TAC [CONJ_ss][pred_setTheory.EXTENSION] THEN
    Induct_on `m` THEN SRW_TAC [][] THENL [
      SRW_TAC [][EXTENSION],
      SRW_TAC [][Once FUNPOW_SUC] THEN
      SRW_TAC [][EXTENSION] THEN METIS_TAC []
    ]
  ]);
val _ = export_rewrites ["FV_church"]

val tpm_funpow_app = store_thm(
  "tpm_funpow_app",
  ``tpm pi (FUNPOW ($@@ f) n x) = FUNPOW ($@@ (tpm pi f)) n (tpm pi x)``,
  Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC]);
val _  = export_rewrites ["tpm_funpow_app"]

val FV_funpow_app = store_thm(
  "FV_funpow_app",
  ``FV (FUNPOW ($@@ f) n x) ⊆ FV f ∪ FV x``,
  Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC]);

val FV_funpow_app_I = store_thm(
  "FV_funpow_app_I",
  ``v ∈ FV x ⇒ v ∈ FV (FUNPOW ((@@) f) n x)``,
  Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC]);

val FV_funpow_app_E = store_thm(
  "FV_funpow_app_E",
  ``v ∈ FV (FUNPOW ((@@) f) n x) ⇒ v ∈ FV f ∨ v ∈ FV x``,
  MATCH_ACCEPT_TAC (REWRITE_RULE [IN_UNION, SUBSET_DEF] FV_funpow_app));

val fresh_funpow_app_I = store_thm(
  "fresh_funpow_app_I",
  ``v ∉ FV f ∧ v ∉ FV x ⇒ v ∉ FV (FUNPOW ((@@) f) n x)``,
  METIS_TAC [FV_funpow_app_E]);
val _ = export_rewrites ["fresh_funpow_app_I"]

val SUB_funpow_app = store_thm(
  "SUB_funpow_app",
  ``[M/v] (FUNPOW ($@@ f) n x) = FUNPOW ($@@ ([M/v]f)) n ([M/v]x)``,
  Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC]);
val _ = export_rewrites ["SUB_funpow_app"]

val church_thm = store_thm(
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

val csuc_behaviour = store_thm(
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

val natrec_behaviour = store_thm(
  "natrec_behaviour",
  ``natrec @@ z @@ f @@ church 0 == z ∧
    natrec @@ z @@ f @@ church (SUC n) == 
       f @@ church n @@ (natrec @@ z @@ f @@ church n)``,
  CONJ_TAC THENL [
    SIMP_TAC (srw_ss()) [natrec_def] THEN FRESH_TAC THEN 
    SRW_TAC [][tpm_fresh, lemma14b] THEN
    ASM_SIMP_TAC (bsrw_ss()) [church_thm, csnd_pair],

    SIMP_TAC (srw_ss()) [natrec_def] THEN unvarify_tac lameq_sub THEN 
    ASM_SIMP_TAC (bsrw_ss()) [] THEN 
    Q.MATCH_ABBREV_TAC 
      `csnd @@ (church (SUC n) @@ Z @@ FF) ==
       VAR fs @@ church n @@ (csnd @@ (church n @@ Z @@ FF))` THEN 
    `∀n. cfst @@ (church n @@ Z @@ FF) == church n`
       by (Induct THEN ASM_SIMP_TAC (bsrw_ss()) [church_thm] THENL [
             SIMP_TAC (bsrw_ss()) [cfst_pair, Abbr`Z`],
             Q.MATCH_ABBREV_TAC `cfst @@ (FF @@ Arg) == church (SUC n)` THEN 
             `∀v. v ∉ FV Arg ⇔ v ≠ zs ∧ v ≠ fs`
                  by (SRW_TAC [][Abbr`Arg`, Abbr`FF`, Abbr`Z`, EQ_IMP_THM] THEN 
                      METIS_TAC []) THEN 
             ASM_SIMP_TAC (bsrw_ss()) [Abbr`FF`, csuc_behaviour, cfst_pair]
           ]) THEN 
    ASM_SIMP_TAC (bsrw_ss()) [church_thm] THEN 
    ASM_SIMP_TAC (bsrw_ss()) [Abbr`FF`, csnd_pair]
  ]);

val cplus_def = Define`
  cplus = LAM "m" (LAM "n" (natrec @@ VAR "n" 
                                   @@ (LAM "m0" (LAM "r" (csuc @@ VAR "r")))
                                   @@ VAR "m"))
`;

val FV_cplus = Store_thm(
  "FV_cplus",
  ``FV cplus = {}``,
  SRW_TAC [][cplus_def, EXTENSION] THEN METIS_TAC []);

val cplus_behaviour = store_thm(
  "cplus_behaviour",
  ``cplus @@ church m @@ church n -n->* church (m + n)``,
  SIMP_TAC (bsrw_ss()) [cplus_def] THEN Induct_on `m` THEN 
  ASM_SIMP_TAC (bsrw_ss()) [natrec_behaviour, csuc_behaviour, 
                            arithmeticTheory.ADD_CLAUSES]);

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
  SIMP_TAC (bsrw_ss()) [natrec_behaviour, cpred_def]);

val cpred_SUC = store_thm(
  "cpred_SUC",
  ``cpred @@ church (SUC n) -n->* church n``,
  SIMP_TAC (bsrw_ss()) [natrec_behaviour, cpred_def]);

val cpred_behaviour = store_thm(
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

val cminus_behaviour = store_thm(
  "cminus_behaviour",
  ``cminus @@ church m @@ church n -n->* church (m - n)``,
  SIMP_TAC (bsrw_ss()) [cminus_def] THEN 
  Q.ID_SPEC_TAC `m` THEN Induct_on `n` THEN
  ASM_SIMP_TAC (bsrw_ss()) [cpred_behaviour, church_thm,
                            DECIDE ``m - SUC n = PRE (m - n)``]);

val cmult_def = Define`
  cmult = LAM "m" (LAM "n" (VAR "m" @@ church 0 @@ (cplus @@ VAR "n")))
`;
val FV_cmult = Store_thm(
  "FV_cmult",
  ``FV cmult = {}``,
  SRW_TAC [][cmult_def, EXTENSION] THEN METIS_TAC []);

val cmult_behaviour = store_thm(
  "cmult_behaviour",
  ``cmult @@ church m @@ church n -n->* church (m * n)``,
  SIMP_TAC (bsrw_ss()) [cmult_def] THEN Induct_on `m` THEN 
  ASM_SIMP_TAC (bsrw_ss() ++ ARITH_ss) [cplus_behaviour, church_thm,
                                        arithmeticTheory.MULT_CLAUSES]);

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

val cis_zero_behaviour = store_thm(
  "cis_zero_behaviour",
  ``cis_zero @@ church n -n->* cB (n = 0)``,
  Cases_on `n` THEN 
  ASM_SIMP_TAC (bsrw_ss()) [cis_zero_def, church_thm]);

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

val lameq_refl = Store_thm(
  "lameq_refl",  
  ``M:term == M``,
  SRW_TAC [][chap2Theory.lam_eq_rules]);

val ceqnat_behaviour = store_thm(
  "ceqnat_behaviour",
  ``ceqnat @@ church n @@ church m -n->* cB (n = m)``,
  SIMP_TAC (bsrw_ss()) [ceqnat_def] THEN 
  Q.ID_SPEC_TAC `m` THEN Induct_on `n` THEN1
    SIMP_TAC (bsrw_ss()) [church_thm, cis_zero_behaviour, 
                          EQ_SYM_EQ] THEN 
  ASM_SIMP_TAC (bsrw_ss()) [cis_zero_behaviour, church_thm,
                            cnot_behaviour, cand_behaviour, 
                            cpred_behaviour] THEN 
  Cases_on `m` THEN SRW_TAC [][])

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

val cless_behaviour = store_thm(
  "cless_behaviour",
  ``cless @@ church m @@ church n -n->* cB (m < n)``,
  SIMP_TAC (bsrw_ss()) [cless_def] THEN 
  Q.ID_SPEC_TAC `n` THEN Induct_on `m` THENL [
    SIMP_TAC (bsrw_ss()) [cnot_behaviour, cis_zero_behaviour, church_thm,
                          arithmeticTheory.NOT_ZERO_LT_ZERO],
    ASM_SIMP_TAC (bsrw_ss()) [cis_zero_behaviour, cnot_behaviour, church_thm,
                              cpred_behaviour, cand_behaviour] THEN 
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
  SIMP_TAC (bsrw_ss()) [cdivmodt_def] THEN Induct_on `n` THENL [
    SIMP_TAC (bsrw_ss()) [arithmeticTheory.ZERO_DIV, 
                          cpair_behaviour, natrec_behaviour,
                          csnd_cvpr],

    ASM_SIMP_TAC (bsrw_ss()) [natrec_behaviour, csuc_behaviour, 
                              ceqnat_behaviour, cless_behaviour, 
                              cminus_behaviour] THEN 

    REPEAT STRIP_TAC THEN 
    Cases_on `p = SUC n` THEN ASM_SIMP_TAC (bsrw_ss()) [cB_behaviour] THENL [
      Cases_on `SUC n < q` THEN ASM_SIMP_TAC (bsrw_ss()) [cB_behaviour] THENL [
        ASM_SIMP_TAC (bsrw_ss()) [arithmeticTheory.LESS_DIV_EQ_ZERO, 
                                  cpair_behaviour],
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

val cdiv_behaviour = store_thm(
  "cdiv_behaviour",
  ``0 < q ⇒ 
      cdiv @@ church p @@ church q -n->* church (p DIV q)``,
  SIMP_TAC (bsrw_ss()) [cdivmodt_behaviour, cdiv_def, cfst_cvpr]);

val cmod_def = Define`
  cmod = LAM "p" (LAM "q" 
           (csnd @@ (cdivmodt @@ VAR "q" @@ VAR "p" @@ church 0 @@ VAR "p")))
`;
val FV_cmod = Store_thm(
  "FV_cmod",
  ``FV cmod = {}``,
  SRW_TAC [][cmod_def, EXTENSION] THEN METIS_TAC [])

val cmod_behaviour = store_thm(
  "cmod_behaviour",
  ``0 < q ⇒ 
     cmod @@ church p @@ church q -n->* church (p MOD q)``,
  SIMP_TAC (bsrw_ss()) [cdivmodt_behaviour, cmod_def, csnd_cvpr]);
                        
val _ = export_theory()

