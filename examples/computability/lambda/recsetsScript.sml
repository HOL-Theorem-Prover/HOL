open HolKernel Parse bossLib boolLib

val _ = new_theory "recsets"

open recfunsTheory reductionEval
open binderLib
open stepsTheory
open churchlistTheory churchDBTheory churchnumTheory churchboolTheory
open normal_orderTheory

fun Store_thm(trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val recursive_def = Define`
  recursive s = ∃M. ∀e. Phi M e = SOME (if e ∈ s then 1 else 0)
`;

val empty_recursive = Store_thm(
  "empty_recursive",
  ``recursive {}``,
  SRW_TAC [][recursive_def, Phi_def] THEN
  Q.EXISTS_TAC `dBnum (fromTerm (LAM v (church 0)))` THEN
  SIMP_TAC (bsrw_ss()) [bnf_bnf_of]);

val univ_recursive = Store_thm(
  "univ_recursive",
  ``recursive UNIV``,
  SRW_TAC [][recursive_def, Phi_def] THEN
  Q.EXISTS_TAC `dBnum (fromTerm (LAM v (church 1)))` THEN
  SIMP_TAC (bsrw_ss()) [bnf_bnf_of]);

val union_recursive_I = Store_thm(
  "union_recursive_I",
  ``recursive s₁ ∧ recursive s₂ ⇒ recursive (s₁ ∪ s₂)``,
  SRW_TAC [][recursive_def] THEN
  SIMP_TAC (srw_ss()) [Phi_def] THEN
  Q.EXISTS_TAC
    `dBnum (fromTerm
      (LAM z (cor @@ (ceqnat @@ (church 1)
                             @@ (UM @@ (cnpair @@ church M @@ VAR z)))
                  @@ (ceqnat @@ (church 1)
                             @@ (UM @@ (cnpair @@ church M' @@ VAR z)))
                  @@ church 1
                  @@ church 0)))` THEN
  Q.X_GEN_TAC `n` THEN
  REPEAT (FIRST_X_ASSUM (Q.SPEC_THEN `n` STRIP_ASSUME_TAC)) THEN
  IMP_RES_TAC PhiSOME_UM_I THEN
  ASM_SIMP_TAC (bsrw_ss()) [cnpair_behaviour,
                            ceqnat_behaviour] THEN
  Cases_on `n ∈ s₁` THEN Cases_on `n ∈ s₂` THEN
  ASM_SIMP_TAC (bsrw_ss()) [cor_behaviour,
                            cB_behaviour,
                            bnf_bnf_of]);

val inter_recursive_I = Store_thm(
  "inter_recursive_I",
  ``recursive s₁ ∧ recursive s₂ ⇒ recursive (s₁ ∩ s₂)``,
  SRW_TAC [][recursive_def] THEN
  SIMP_TAC (srw_ss()) [Phi_def] THEN
  Q.EXISTS_TAC `
    dBnum (fromTerm
      (LAM z (cmult @@ (UM @@ (cnpair @@ church M @@ VAR z))
                    @@ (UM @@ (cnpair @@ church M' @@ VAR z)))))` THEN
  Q.X_GEN_TAC `n` THEN
  REPEAT (FIRST_X_ASSUM (Q.SPEC_THEN `n` STRIP_ASSUME_TAC)) THEN
  IMP_RES_TAC PhiSOME_UM_I THEN
  ASM_SIMP_TAC (bsrw_ss()) [cnpair_behaviour,
                            cmult_behaviour,
                            bnf_bnf_of] THEN
  Cases_on `n ∈ s₁` THEN SRW_TAC [][]);

val compl_recursive_I = store_thm(
  "compl_recursive_I",
  ``recursive s ⇒ recursive (COMPL s)``,
  SRW_TAC [][recursive_def] THEN
  SIMP_TAC (srw_ss()) [Phi_def] THEN
  Q.EXISTS_TAC `
    dBnum (fromTerm
      (LAM z (cminus @@ (church 1)
                     @@ (UM @@ (cnpair @@ church M @@ VAR z)))))` THEN
  Q.X_GEN_TAC `n` THEN
  POP_ASSUM (Q.SPEC_THEN `n` STRIP_ASSUME_TAC) THEN
  IMP_RES_TAC PhiSOME_UM_I THEN
  ASM_SIMP_TAC (bsrw_ss()) [cnpair_behaviour,
                            cminus_behaviour,
                            bnf_bnf_of] THEN
  Cases_on `n ∈ s` THEN SRW_TAC [][]);

val compl_recursive = Store_thm(
  "compl_recursive",
  ``recursive (COMPL s) ⇔ recursive s``,
  METIS_TAC [pred_setTheory.COMPL_COMPL, compl_recursive_I]);

val finite_recursive = Store_thm(
  "finite_recursive",
  ``∀s. FINITE s ==> recursive s``,
  HO_MATCH_MP_TAC pred_setTheory.FINITE_INDUCT THEN
  SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [recursive_def] THEN
  SIMP_TAC (srw_ss()) [Phi_def] THEN
  Q.EXISTS_TAC `
    dBnum (fromTerm
      (LAM z (cor @@ (ceqnat @@ VAR z @@ church e)
                  @@ (ceqnat @@ church 1
                             @@ (UM @@ (cnpair @@ church M @@ VAR z)))
                  @@ church 1
                  @@ church 0)))` THEN
  Q.X_GEN_TAC `n` THEN FIRST_X_ASSUM (Q.SPEC_THEN `n` STRIP_ASSUME_TAC) THEN
  IMP_RES_TAC PhiSOME_UM_I THEN
  ASM_SIMP_TAC (bsrw_ss()) [cnpair_behaviour, ceqnat_behaviour,
                            cor_behaviour] THEN
  Cases_on `n = e` THEN
  ASM_SIMP_TAC (bsrw_ss()) [cB_behaviour, bnf_bnf_of] THEN
  Cases_on `n ∈ s` THEN
  ASM_SIMP_TAC (bsrw_ss()) [cB_behaviour, bnf_bnf_of]);

(* ----------------------------------------------------------------------
    cfindleast
   ---------------------------------------------------------------------- *)

val cfindbody_def = Define`
  cfindbody P n =
    let lp = NEW (FV P) in
    let nv = NEW (FV P ∪ {lp})
    in
        Yf (LAM lp (LAM nv (P @@ VAR nv
                              @@ VAR nv
                              @@ (VAR lp @@ (csuc @@ VAR nv))))) @@ church n
`;

val fresh_cfindbody = store_thm(
  "fresh_cfindbody",
  ``lp ∉ FV P ∧ nv ≠ lp ∧ nv ∉ FV P ⇒
    (cfindbody P n = Yf (LAM lp (LAM nv (P @@ VAR nv @@ VAR nv
                                           @@ (VAR lp @@ (csuc @@ VAR nv))))) @@
                        church n)``,
  SRW_TAC [][LET_THM, cfindbody_def] THEN
  binderLib.NEW_ELIM_TAC THEN REPEAT STRIP_TAC THEN
  binderLib.NEW_ELIM_TAC THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN SRW_TAC [][termTheory.LAM_eq_thm, termTheory.tpm_fresh] THEN
  Cases_on `nv = v` THEN SRW_TAC [][termTheory.tpm_fresh] THEN
  Cases_on `lp = v'` THEN SRW_TAC [][termTheory.tpm_fresh]);

val cfindbody_SUB = store_thm(
  "cfindbody_SUB",
  ``[N/v] (cfindbody P n) = cfindbody ([N/v]P) n``,
  Q_TAC (NEW_TAC "lp") `FV P ∪ FV N ∪ {v}` THEN
  Q_TAC (NEW_TAC "nv") `FV P ∪ FV N ∪ {v;lp}` THEN
  `cfindbody P n = Yf (LAM lp (LAM nv (P @@ VAR nv @@ VAR nv
                                         @@ (VAR lp @@ (csuc @@ VAR nv))))) @@
                    church n`
    by SRW_TAC [][fresh_cfindbody] THEN
  `cfindbody ([N/v]P) n =
   Yf (LAM lp (LAM nv ([N/v]P @@ VAR nv @@ VAR nv
                            @@ (VAR lp @@ (csuc @@ VAR nv))))) @@ church n`
    by (MATCH_MP_TAC (GEN_ALL fresh_cfindbody) THEN
        SRW_TAC [][chap2Theory.NOT_IN_FV_SUB]) THEN
  SRW_TAC [][termTheory.lemma14b]);

val cfindbody_thm = store_thm(
  "cfindbody_thm",
  ``cfindbody P n == P @@ church n @@ church n @@ cfindbody P (n + 1)``,
  Q_TAC (NEW_TAC "z") `FV P` THEN
  Q_TAC (NEW_TAC "nv") `FV P ∪ {z}` THEN
  `∀n. cfindbody P n = Yf (LAM z (LAM nv (P @@ VAR nv @@ VAR nv
                                        @@ (VAR z @@ (csuc @@ VAR nv)))))
                          @@ church n`
     by SRW_TAC [][fresh_cfindbody] THEN
  ASM_SIMP_TAC (bsrw_ss()) [Once chap2Theory.YffYf,
                            csuc_behaviour, arithmeticTheory.ADD1]);

val cfindleast_def = Define`
  cfindleast = LAM "P" (cfindbody (VAR "P") 0)
`;

val cfindleast_termI = store_thm(
  "cfindleast_termI",
  ``(∀n. ∃b. P @@ church n == cB b) ∧ P @@ church n == cB T ⇒
    cfindleast @@ P == church (LEAST n. P @@ church n == cB T)``,
  STRIP_TAC THEN numLib.LEAST_ELIM_TAC THEN CONJ_TAC THEN1 METIS_TAC [] THEN
  POP_ASSUM (K ALL_TAC) THEN
  SIMP_TAC (bsrw_ss()) [cfindleast_def, cfindbody_SUB] THEN
  Q_TAC SUFF_TAC
    `∀p n. p ≤ n ∧
           (∀m. m < n ⇒ ¬(P @@ church m == cB T)) ∧
           P @@ church n == cB T ⇒
           cfindbody P p == church n`
    THEN1 METIS_TAC [DECIDE ``0 ≤ n``] THEN
  Induct_on `n - p` THEN REPEAT STRIP_TAC THENL [
    `p = n` by DECIDE_TAC THEN
    ASM_SIMP_TAC (bsrw_ss()) [Once cfindbody_thm, cB_behaviour],

    `p < n` by DECIDE_TAC THEN
    `∃r. P @@ church p == cB r` by METIS_TAC [] THEN
    `r = F` by (Cases_on `r` THEN METIS_TAC []) THEN
    ASM_SIMP_TAC (bsrw_ss()) [Once cfindbody_thm, cB_behaviour] THEN
    FIRST_X_ASSUM (fn th => MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] th)) THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) []
  ]);

val noreduct_Yf = Store_thm(
  "noreduct_Yf",
  ``(noreduct (Yf f) = SOME (f @@ Yf f)) ∧
    (noreduct (Yf f @@ x) = SOME (f @@ Yf f @@ x))``,
  Q_TAC (NEW_TAC "z") `FV f` THEN
  `Yf f = LAM z (f @@ (VAR z @@ VAR z)) @@ LAM z (f @@ (VAR z @@ VAR z))`
    by SRW_TAC [][chap2Theory.Yf_fresh] THEN
  SRW_TAC [][noreduct_thm, termTheory.lemma14b]);

val lameq_triangle = store_thm(
  "lameq_triangle",
  ``M == N ∧ M == P ∧ bnf N ∧ bnf P ⇒ (N = P)``,
  METIS_TAC [chap3Theory.betastar_lameq_bnf, chap2Theory.lam_eq_rules,
             chap3Theory.bnf_reduction_to_self]);

(* val cfindleast_bnfE = store_thm(
  "cfindleast_bnfE",
  ``(∀n. ∃b. P @@ church n == cB b) ∧
    cfindleast @@ P == r ∧ bnf r ⇒
    ∃m. (r = church m) ∧ P @@ r == cB T ∧
        ∀m₀. m₀ < m ⇒ P @@ church m₀ == cB F``,
  SIMP_TAC (bsrw_ss()) [cfindleast_def, cfindbody_SUB] THEN
  REPEAT STRIP_TAC THEN
  `∃N. steps N (cfindbody P 0) = r`
    by METIS_TAC [nstar_steps, nstar_betastar_bnf,
                  chap3Theory.betastar_lameq_bnf] THEN
  Q_TAC SUFF_TAC
    `∀N cn. (steps N (cfindbody P cn) = r) ⇒
            (∀c0. c0 < cn ⇒ P @@ church c0 == cB F) ⇒
            ∃m. (r = church m) ∧ P @@ r == cB T ∧
                ∀m₀. m₀ < m ⇒ P @@ church m₀ == cB F`
    THEN1 METIS_TAC [DECIDE ``¬(x < 0)``] THEN
  REPEAT (FIRST_X_ASSUM (fn th => if free_in ``cfindbody`` (concl th) then
                                    ALL_TAC
                                  else NO_TAC)) THEN
  completeInduct_on `N` THEN
  Q.X_GEN_TAC `cn` THEN
  Q_TAC (NEW_TAC "lp") `FV P` THEN
  Q_TAC (NEW_TAC "nv") `FV P ∪ {lp}` THEN
  `∀cn.
     cfindbody P cn =
       Yf (LAM lp (LAM nv (P @@ VAR nv @@ VAR nv
                             @@ (VAR lp @@ (csuc @@ VAR nv))))) @@
       church cn`
    by SRW_TAC [][fresh_cfindbody] THEN
  `(N = 0) ∨ ∃N₀. N = SUC N₀` by (Cases_on `N` THEN SRW_TAC [][]) THEN1
     (SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []) THEN
  ASM_SIMP_TAC (srw_ss()) [] THEN
  `(N₀ = 0) ∨ ∃N₁. N₀ = SUC N₁` by (Cases_on `N₀` THEN SRW_TAC [][]) THEN1
     (SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []) THEN
  ASM_SIMP_TAC (srw_ss()) [noreduct_thm, termTheory.lemma14b] THEN
  `(N₁ = 0) ∨ ∃N₂. N₁ = SUC N₂` by (Cases_on `N₁` THEN SRW_TAC [][]) THEN1
     (SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []) THEN
  ASM_SIMP_TAC (srw_ss()) [noreduct_thm, termTheory.lemma14b] THEN
  `∃b. P @@ church cn == cB b` by METIS_TAC [] THEN
  Cases_on `b` THENL [
    Q.MATCH_ABBREV_TAC `(steps N₂ TT = r) ⇒ MINCL ⇒ CONCL` THEN
    `TT == church cn`
      by ASM_SIMP_TAC (bsrw_ss()) [Abbr`TT`, cB_behaviour] THEN
    STRIP_TAC THEN
    `TT -n->* r` by METIS_TAC [steps_nstar] THEN
    `church cn = r` by METIS_TAC [lameq_triangle, bnf_church,
                                  nstar_betastar,
                                  chap3Theory.betastar_lameq_bnf] THEN
    Q.UNABBREV_TAC `CONCL` THEN SRW_TAC [][],

    Q.MATCH_ABBREV_TAC `(steps N₂ (P @@ church cn @@ church cn @@ Loop) = r) ⇒
                        MINCL ⇒ CONCL` THEN
    IMP_RES_TAC whead_tests THEN
    `P @@ church cn @@ church cn @@ Loop -n->* Loop`
      by METIS_TAC [whstar_nstar] THEN
    `∃n2. Loop = steps n2 (P @@ church cn @@ church cn @@ Loop)`
      by METIS_TAC [nstar_steps] THEN
    `¬bnf Loop` by (SRW_TAC [][Abbr`Loop`]) THEN
    REPEAT STRIP_TAC THEN
      `n2 < n1` by METIS_TAC [DECIDE ``n:num < m ∨ (n = m) ∨ m < n``,
                              bnf_steps_upwards_closed] THEN
      `∃rest. n1 = rest + n2` by (Q.EXISTS_TAC `n1 - n2` THEN DECIDE_TAC) THEN






*)

(* an r.e. set is one that can be enumerated.  In this world, I take enumerable
   to mean there exists a function that returns values at successive indices.
*)
val re_def = Define`
  re s = ∃Mi. ∀e. e ∈ s ⇔ ∃j. Phi Mi j = SOME e
`;

(* if a set s is r.e., then there is a machine that terminates on only those
   elements of the set (and fails to terminate on non-members)

   Say the machine we have that enumerates s is Mi.  Then we want one that
   will correctly terminate on element e of s.
   For increasing n, construct the list of n elements corresponding to
   evaluating [Mi 0, Mi 1, Mi 2, ... Mi n] for n steps.  For all the bnfs in
   this list, see if one of them is equal to e.  If so, terminate.
*)
val enum2semibody_def = Define`
  enum2semibody Mi e loop n j =
    LAM loop (LAM n
      (cmem @@ e
            @@ (cmap @@ cforce_num
                     @@ (cfilter
                           @@ cbnf
                           @@ (ctabulate
                                 @@ (csuc @@ VAR n)
                                 @@ (LAM j
                                       (csteps
                                          @@ VAR n
                                          @@ (cdAPP
                                                @@ (cnumdB @@ church Mi)
                                                @@ (cchurch @@ VAR j)))))))
            @@ church 0
            @@ (VAR loop @@ (csuc @@ VAR n))))
`;

val enum2semi_def = Define`
  enum2semi Mi e =
    let loop = NEW (FV e) in
    let n = NEW ({loop} ∪ FV e) in
    let j = NEW {n}
    in
       enum2semibody Mi e loop n j
`;

val FV_enum2semi = Store_thm(
  "FV_enum2semi",
  ``FV (enum2semi n t) = FV t``,
  SRW_TAC [][enum2semi_def, LET_THM, pred_setTheory.EXTENSION,
             enum2semibody_def] THEN
  binderLib.NEW_ELIM_TAC THEN REPEAT GEN_TAC THEN
  binderLib.NEW_ELIM_TAC THEN SRW_TAC [][] THEN
  METIS_TAC []);

val FV_enum2semibody = Store_thm(
  "FV_enum2semibody",
  ``FV (enum2semibody n t x y z) = FV t DELETE x DELETE y``,
  SRW_TAC [][enum2semibody_def, pred_setTheory.EXTENSION] THEN
  METIS_TAC []);

val enum2semi_fresh = prove(
  ``loop ∉ FV e ∧ n ≠ loop ∧ n ∉ FV e ∧ j ≠ n ⇒
     (enum2semi Mi e = enum2semibody Mi e loop n j)``,
  SRW_TAC [][enum2semi_def, LET_THM] THEN
  binderLib.NEW_ELIM_TAC THEN REPEAT STRIP_TAC THEN
  binderLib.NEW_ELIM_TAC THEN REPEAT STRIP_TAC THEN
  binderLib.NEW_ELIM_TAC THEN REPEAT STRIP_TAC THEN
  SRW_TAC [][enum2semibody_def, termTheory.LAM_eq_thm,
             termTheory.tpm_fresh] THEN
  Cases_on `loop = v` THEN SRW_TAC [][] THEN1
    (SRW_TAC [][basic_swapTheory.swapstr_def] THEN METIS_TAC []) THEN
  Cases_on `v = n` THEN SRW_TAC [][] THEN
  Cases_on `loop = n` THEN SRW_TAC [][] THENL [
    Cases_on `loop = j` THEN SRW_TAC [][] THEN
    SRW_TAC [][basic_swapTheory.swapstr_def, termTheory.tpm_fresh] THEN
    METIS_TAC [],

    Cases_on `loop = j` THEN SRW_TAC [][] THEN1
      (SRW_TAC [][basic_swapTheory.swapstr_def, termTheory.tpm_fresh] THEN
       METIS_TAC []) THEN
    Cases_on `v = j` THEN SRW_TAC [][] THEN
    SRW_TAC [][basic_swapTheory.swapstr_def, termTheory.tpm_fresh] THEN
    METIS_TAC []
  ]);

val enum2semi_SUB = store_thm(
  "enum2semi_SUB",
  ``[N/v] (enum2semi n t) = enum2semi n ([N/v]t)``,
  Q_TAC (NEW_TAC "loop") `FV N ∪ {v} ∪ FV t` THEN
  Q_TAC (NEW_TAC "m") `FV N ∪ {v; loop} ∪ FV t` THEN
  Q_TAC (NEW_TAC "j") `FV N ∪ {v;m}` THEN
  `enum2semi n t = enum2semibody n t loop m j`
     by METIS_TAC [enum2semi_fresh] THEN
  `enum2semi n ([N/v]t) = enum2semibody n ([N/v]t) loop m j`
     by (MATCH_MP_TAC enum2semi_fresh THEN
         SRW_TAC [][chap2Theory.NOT_IN_FV_SUB]) THEN
  SRW_TAC [][enum2semibody_def, termTheory.lemma14b]);

val freshlemma = prove(
  ``NEW (FV e) ∉ FV e ∧ NEW (FV e ∪ {NEW (FV e)}) ≠ NEW (FV e) ∧
    NEW (FV e ∪ {NEW (FV e)}) ∉ FV e ∧
    NEW {NEW (FV e ∪ {NEW (FV e)})} ≠ NEW (FV e ∪ {NEW (FV e)})``,
  binderLib.NEW_ELIM_TAC THEN NTAC 2 STRIP_TAC THEN
  binderLib.NEW_ELIM_TAC THEN NTAC 2 STRIP_TAC THEN
  binderLib.NEW_ELIM_TAC);

val enum2semi_eqn =
    enum2semi_fresh
      |> REWRITE_RULE [enum2semibody_def]
      |> UNDISCH
      |> brackabs.brackabs_equiv
          (CONJUNCTS
               (ASSUME ``loop ∉ FV e ∧ n ≠ loop ∧ n ∉ FV e ∧ j ≠ n``))
      |> DISCH_ALL
      |> Q.INST [`j` |-> `NEW {n}`]
      |> Q.INST [`loop` |-> `NEW (FV e)`, `n` |-> `NEW (FV e ∪ {NEW (FV e)})`]
      |> C MP freshlemma

val MEM_GENLIST = prove(
  ``MEM e (GENLIST f n) = ∃i. i < n ∧ (e = f i)``,
  Q.ID_SPEC_TAC `f` THEN
  Induct_on `n` THEN1 SRW_TAC [][rich_listTheory.GENLIST] THEN
  SRW_TAC [][GENLIST_ALT, EQ_IMP_THM] THENL [
    Cases_on `e = f 0` THENL [
      Q.EXISTS_TAC `0` THEN SRW_TAC [][],
      FULL_SIMP_TAC (srw_ss()) [] THEN Q.EXISTS_TAC `SUC i` THEN
      SRW_TAC [][]
    ],
    `∃m. i = SUC m` by METIS_TAC [TypeBase.nchotomy_of ``:num``] THEN
    Q.EXISTS_TAC `m` THEN SRW_TAC [ARITH_ss][]
  ]);

val EXISTS_FILTER = store_thm(
  "EXISTS_FILTER",
  ``EXISTS P (FILTER Q l) = EXISTS (λe. Q e ∧ P e) l``,
  Induct_on `l` THEN SRW_TAC [][]);

val EXISTS_GENLIST = prove(
  ``∀n f. EXISTS P (GENLIST f n) = ∃i. i < n ∧ P (f i)``,
  Induct THEN1 SRW_TAC [][rich_listTheory.GENLIST] THEN
  SRW_TAC [][GENLIST_ALT, EQ_IMP_THM] THENL [
    Q.EXISTS_TAC `0` THEN SRW_TAC [][],
    Q.EXISTS_TAC `SUC i` THEN SRW_TAC [][],
    Cases_on `i` THEN SRW_TAC [][] THEN
    DISJ2_TAC THEN Q.EXISTS_TAC `n'` THEN SRW_TAC [ARITH_ss][]
  ]);

val re_semirecursive1 = prove(
  ``re s ⇒ ∃N. ∀e. e ∈ s ⇔ ∃m. Phi N e = SOME m``,
  SRW_TAC [][re_def] THEN
  Q.EXISTS_TAC
    `dBnum (fromTerm
              (LAM "e" (chap2$Y @@ enum2semi Mi (VAR "e") @@ church 0)))` THEN
  SRW_TAC [][Phi_def, EQ_IMP_THM] THENL [
    SIMP_TAC (bsrw_ss()) [churchDBTheory.cnumdB_behaviour,
                          Once chap2Theory.lameq_Y, enum2semi_SUB] THEN
    `toTerm (numdB Mi) @@ church j -n->* z ∧ bnf z`
       by METIS_TAC [bnf_of_SOME] THEN
    `∃n. steps n (toTerm (numdB Mi) @@ church j) = z`
       by METIS_TAC [stepsTheory.bnf_steps] THEN
    Q.MATCH_ABBREV_TAC
      `∃r. bnf_of (E @@ (chap2$Y @@ E) @@ church 0) = SOME r` THEN
    Q_TAC SUFF_TAC `∀st. st ≤ MAX (j + 1) n ⇒
                         E @@ (chap2$Y @@ E) @@ church st == church 0`
          THEN1 (DISCH_THEN (Q.SPEC_THEN `0` MP_TAC) THEN
                 SIMP_TAC (bsrw_ss()) [bnf_bnf_of]) THEN
    Q_TAC SUFF_TAC
          `∀m st. (m = MAX (j + 1) n - st) ∧
                  st ≤ MAX (j + 1) n ⇒
                  E @@ (chap2$Y @@ E) @@ church st == church 0`
          THEN1 METIS_TAC [] THEN
    Induct THEN REPEAT STRIP_TAC THENL [
      `st = MAX (j + 1) n` by DECIDE_TAC THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      SIMP_TAC (bsrw_ss()) [Abbr`E`, enum2semi_eqn] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      ASM_SIMP_TAC (bsrw_ss() ++ boolSimps.DNF_ss)
                   [ctabulate_cvlist, Cong cvlist_genlist_cong,
                    csuc_behaviour,
                    cchurch_behaviour, cnumdB_behaviour,
                    cdAPP_behaviour, csteps_behaviour,
                    cfilter_cvlist, MEM_GENLIST, cbnf_behaviour,
                    cmap_cvlist, cmem_cvlist, listTheory.MEM_MAP,
                    listTheory.MEM_FILTER, cforce_num_behaviour] THEN
      ASM_SIMP_TAC (srw_ss()) [listTheory.EXISTS_MAP,
                               EXISTS_FILTER, EXISTS_GENLIST] THEN
      Q.MATCH_ABBREV_TAC `cB P @@ church 0 @@ X == church 0` THEN
      Q_TAC SUFF_TAC `P` THEN1
        SIMP_TAC (bsrw_ss()) [cB_behaviour] THEN
      markerLib.UNABBREV_ALL_TAC THEN
      Q.EXISTS_TAC `j` THEN
      SIMP_TAC (bsrw_ss()) [cforce_num_behaviour,
                            ceqnat_behaviour,
                            cbnf_behaviour] THEN
      `steps (MAX (j + 1) n) (toTerm (numdB Mi) @@ church j) = z`
         by (SRW_TAC [][] THEN Cases_on `MAX (j + 1) n = n`
               THEN1 SRW_TAC [][] THEN
             MATCH_MP_TAC bnf_steps_upwards_closed THEN
             FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)
                           [arithmeticTheory.MAX_DEF]) THEN
      SRW_TAC [ARITH_ss][arithmeticTheory.MAX_DEF],

      `st < MAX (j + 1) n` by DECIDE_TAC THEN
      SIMP_TAC (bsrw_ss()) [Abbr`E`, Once enum2semi_eqn] THEN
      ASM_SIMP_TAC (bsrw_ss() ++ boolSimps.DNF_ss)
                   [ctabulate_cvlist, Cong cvlist_genlist_cong,
                    csuc_behaviour,
                    cchurch_behaviour, cnumdB_behaviour,
                    cdAPP_behaviour, csteps_behaviour,
                    cfilter_cvlist, MEM_GENLIST, cbnf_behaviour,
                    cmap_cvlist, cmem_cvlist, listTheory.MEM_MAP,
                    listTheory.MEM_FILTER, cforce_num_behaviour] THEN
      ASM_SIMP_TAC (srw_ss()) [listTheory.EXISTS_MAP,
                               EXISTS_FILTER, EXISTS_GENLIST] THEN
      Q.ABBREV_TAC `MX = MAX (j + 1) n`  THEN
      FIRST_X_ASSUM (Q.SPEC_THEN `SUC st` MP_TAC) THEN
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
      STRIP_TAC THEN
      ASM_SIMP_TAC (bsrw_ss()) [Once chap2Theory.lameq_Y] THEN
      Q.MATCH_ABBREV_TAC `cB P @@ X @@ X == X` THEN
      Cases_on `P` THEN
      ASM_SIMP_TAC (bsrw_ss()) [cB_behaviour]
    ],

    (* other direction: that if our enum2semi function does terminate on an
       x, then x does indeed appear in the enumeration
    *)
    FULL_SIMP_TAC (bsrw_ss())
                  [enum2semi_SUB,
                   Once (MATCH_MP relationTheory.RTC_SINGLE
                                  head_reductionTheory.whY1),
                   Once (MATCH_MP relationTheory.RTC_SINGLE
                                  head_reductionTheory.whY2)] THEN
    FULL_SIMP_TAC (bsrw_ss()) [bnf_steps] THEN
    NTAC 2 (POP_ASSUM MP_TAC) THEN POP_ASSUM (K ALL_TAC) THEN
    Q.MATCH_ABBREV_TAC `(steps n (TT @@ church 0) = z) ⇒ bnf z ⇒ Concl` THEN
    Q_TAC SUFF_TAC
          `∀n t m. (t == church m) ⇒ (steps n (TT @@ t) = z) ∧ bnf z ⇒
                   Concl` THEN1 METIS_TAC [chap2Theory.lameq_refl] THEN
    markerLib.UNABBREV_ALL_TAC THEN
    completeInduct_on `n` THEN
    MAP_EVERY Q.X_GEN_TAC [`t`,`m`] THEN STRIP_TAC THEN
    `lp ∉ FV (church e)` by SRW_TAC [][] THEN
    Q_TAC (NEW_TAC "nm") `{lp}` THEN
    Q_TAC (NEW_TAC "jm") `{nm}` THEN
    `enum2semi Mi (church e) = enum2semibody Mi (church e) lp nm jm`
       by (MATCH_MP_TAC enum2semi_fresh THEN SRW_TAC [][]) THEN
    `(n = 0) ∨ (∃n0. n = SUC n0)`
       by METIS_TAC [TypeBase.nchotomy_of ``:num``]
       THEN1 (SRW_TAC [][enum2semibody_def] THEN
              FULL_SIMP_TAC (srw_ss()) []) THEN
    ASM_SIMP_TAC (srw_ss()) [Once enum2semibody_def, noreduct_thm,
                             termTheory.lemma14b] THEN
    `(n0 = 0) ∨ (∃n1. n0 = SUC n1)`
       by METIS_TAC [TypeBase.nchotomy_of ``:num``]
       THEN1 (SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []) THEN
    ASM_SIMP_TAC (srw_ss()) [noreduct_thm, termTheory.lemma14b] THEN
    Q.MATCH_ABBREV_TAC
      `(steps n1 (BoolTerm @@ church 0 @@ Loop) = z) ∧ bnf z ⇒ Concl` THEN
    `∃b. BoolTerm == cB b`
       by (SIMP_TAC (bsrw_ss()) [Abbr`BoolTerm`] THEN
           ASM_SIMP_TAC (bsrw_ss() ++ boolSimps.DNF_ss)
                        [ctabulate_cvlist, Cong cvlist_genlist_cong,
                         csuc_behaviour,
                         cchurch_behaviour, cnumdB_behaviour,
                         cdAPP_behaviour, csteps_behaviour,
                         cfilter_cvlist, MEM_GENLIST, cbnf_behaviour,
                         cmap_cvlist, cmem_cvlist, listTheory.MEM_MAP,
                         listTheory.MEM_FILTER, cforce_num_behaviour]) THEN
    Cases_on `b` THENL [
      DISCH_THEN (K ALL_TAC) THEN
      Q.UNABBREV_TAC `Concl` THEN
      POP_ASSUM MP_TAC THEN
      SIMP_TAC (bsrw_ss()) [Abbr`BoolTerm`] THEN
      ASM_SIMP_TAC (bsrw_ss() ++ boolSimps.DNF_ss)
                   [ctabulate_cvlist, Cong cvlist_genlist_cong,
                    csuc_behaviour,
                    cchurch_behaviour, cnumdB_behaviour,
                    cdAPP_behaviour, csteps_behaviour,
                    cfilter_cvlist, MEM_GENLIST, cbnf_behaviour,
                    cmap_cvlist, cmem_cvlist, listTheory.MEM_MAP,
                    listTheory.MEM_FILTER, cforce_num_behaviour] THEN
      SIMP_TAC (bsrw_ss()) [listTheory.EXISTS_MAP, EXISTS_FILTER,
                            EXISTS_GENLIST,
                            cchurch_behaviour, cdAPP_behaviour,
                            csteps_behaviour, cbnf_behaviour,
                            cforce_num_behaviour,
                            ceqnat_behaviour] THEN
      METIS_TAC [],

      Q.RM_ABBREV_TAC `BoolTerm` THEN
      IMP_RES_TAC whead_tests THEN
      `BoolTerm @@ church 0 @@ Loop -n->* Loop` by METIS_TAC [whstar_nstar] THEN
      `∃n2. Loop = steps n2 (BoolTerm @@ church 0 @@ Loop)`
         by METIS_TAC [nstar_steps] THEN
      `¬bnf Loop` by (SRW_TAC [][Abbr`Loop`, chap2Theory.Yf_def] THEN
                      SRW_TAC [][]) THEN
      REPEAT STRIP_TAC THEN
      `n2 < n1` by METIS_TAC [DECIDE ``n:num < m ∨ (n = m) ∨ m < n``,
                              bnf_steps_upwards_closed] THEN
      `∃rest. n1 = rest + n2` by (Q.EXISTS_TAC `n1 - n2` THEN DECIDE_TAC) THEN
      FULL_SIMP_TAC (srw_ss()) [steps_plus] THEN
      `steps rest Loop = z` by METIS_TAC [] THEN
      `∃r1. rest = SUC r1`
         by METIS_TAC [TypeBase.nchotomy_of ``:num``, steps_def] THEN
      Q.ABBREV_TAC `EE = enum2semibody Mi (church e) lp nm jm` THEN
      `Loop -n-> EE @@ Yf EE @@ (csuc @@ t)`
         by SRW_TAC [][head_reductionTheory.whY2, Abbr`Loop`, whead_normorder,
                       head_reductionTheory.weak_head_rules] THEN
      `noreduct Loop = SOME (EE @@ Yf EE @@ (csuc @@ t))`
         by FULL_SIMP_TAC (srw_ss()) [noreduct_characterisation] THEN
      `steps r1 (EE @@ Yf EE @@ (csuc @@ t)) = z`
         by FULL_SIMP_TAC (srw_ss()) [ASSUME ``¬bnf Loop``] THEN
      FIRST_X_ASSUM (Q.SPEC_THEN `r1` MP_TAC) THEN
      ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [] THEN
      DISCH_THEN (fn th => MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] th)) THEN
      MAP_EVERY Q.EXISTS_TAC [`csuc @@ t`, `SUC m`] THEN
      ASM_SIMP_TAC (bsrw_ss()) [csuc_behaviour]
    ]
  ]);

val cbnf_of_works1' =
    cbnf_of_works1 |> Q.INST [`M` |-> `toTerm dM`, `N` |-> `toTerm dN`]
                   |> SIMP_RULE (srw_ss()) []

val re_semirecursive2 = prove(
  ``(∀e. e ∈ s ⇔ ∃m. Phi N e = SOME m) ⇒ re s``,
  SRW_TAC [][re_def] THEN
  Q.EXISTS_TAC `
    dBnum (fromTerm (
     LAM "e" (cbnf_ofk @@ (K @@ VAR "e")
                       @@ (cdAPP @@ cDB (numdB N) @@ (cchurch @@ VAR "e")))))
  ` THEN
  SRW_TAC [][EQ_IMP_THM, Phi_def] THENL [
    MAP_EVERY Q.EXISTS_TAC [`e`, `church e`] THEN
    SIMP_TAC (bsrw_ss()) [cchurch_behaviour, cdAPP_behaviour] THEN
    `cbnf_ofk
          @@ (K @@ church e)
          @@ cDB (dAPP (numdB N) (fromTerm (church e))) ==
     K @@ church e @@ cDB (fromTerm z)`
        by (MATCH_MP_TAC cbnf_of_works1' THEN
            ASM_SIMP_TAC (srw_ss()) []) THEN
    ASM_SIMP_TAC (bsrw_ss()) [bnf_bnf_of],

    FULL_SIMP_TAC (bsrw_ss()) [cchurch_behaviour, cdAPP_behaviour] THEN
    IMP_RES_TAC bnf_of_SOME THEN
    `∃M'. (bnf_of (toTerm (dAPP (numdB N) (fromTerm (church j)))) =
           SOME (toTerm M')) ∧
          K @@ church j @@ cDB M' -n->* z`
       by METIS_TAC [cbnf_ofk_works2] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    POP_ASSUM MP_TAC THEN ASM_SIMP_TAC (bsrw_ss()) [] THEN
    STRIP_TAC THEN
    Q_TAC SUFF_TAC `z = church j` THEN1 SRW_TAC [][] THEN
    Q_TAC SUFF_TAC `z -β->* church j` THEN1
       METIS_TAC [chap3Theory.bnf_reduction_to_self] THEN
    METIS_TAC [chap3Theory.betastar_lameq_bnf, bnf_church,
               chap2Theory.lam_eq_rules]
  ]);

val re_semidp = store_thm(
  "re_semidp",
  ``re s ⇔ ∃N. ∀e. e ∈ s ⇔ ∃m. Phi N e = SOME m``,
  METIS_TAC [re_semirecursive1, re_semirecursive2]);

val recursive_re = store_thm(
  "recursive_re",
  ``recursive s ⇒ re s``,
  SRW_TAC [][recursive_def, re_semidp] THEN
  Q.EXISTS_TAC `
    dBnum (fromTerm (
      LAM "e" (cbnf_ofk @@ (LAM "n" (ceqnat @@ church 0
                                            @@ (cforce_num @@ VAR "n")
                                            @@ Ω
                                            @@ VAR "n"))
                        @@ (cdAPP @@ cDB (numdB M)
                                  @@ (cchurch @@ VAR "e")))))
  ` THEN
  FULL_SIMP_TAC (srw_ss()) [Phi_def] THEN
  SIMP_TAC (bsrw_ss()) [cdAPP_behaviour, cchurch_behaviour] THEN
  SRW_TAC [][EQ_IMP_THM] THENL [
    FIRST_X_ASSUM (Q.SPEC_THEN `e` MP_TAC) THEN
    SRW_TAC [][] THEN
    Q.HO_MATCH_ABBREV_TAC
      `∃z. bnf_of (cbnf_ofk @@ KK @@ cDB TT) = SOME z` THEN
    `cbnf_ofk @@ KK @@ cDB TT == KK @@ cDB (fromTerm z)`
       by (MATCH_MP_TAC cbnf_of_works1' THEN
           SRW_TAC [][Abbr`TT`]) THEN
    ASM_SIMP_TAC (bsrw_ss()) [Abbr`KK`, cforce_num_behaviour] THEN
    Q.PAT_ASSUM `1 = force_num z` (SUBST_ALL_TAC o SYM) THEN
    SIMP_TAC (bsrw_ss()) [bnf_bnf_of, ceqnat_behaviour,
                          cB_behaviour],

    IMP_RES_TAC bnf_of_SOME THEN
    IMP_RES_THEN MP_TAC
                 (REWRITE_RULE [GSYM AND_IMP_INTRO] cbnf_ofk_works2) THEN
    ASM_SIMP_TAC (bsrw_ss()) [] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `e` (Q.X_CHOOSE_THEN `zz` MP_TAC)) THEN
    Cases_on `e ∈ s` THEN SRW_TAC [][] THEN
    SIMP_TAC (bsrw_ss()) [cforce_num_behaviour, ceqnat_behaviour,
                          cB_behaviour] THEN
    STRIP_TAC THEN
    `Ω -β->* z` by METIS_TAC [chap3Theory.betastar_lameq_bnf] THEN
    `z = Ω` by METIS_TAC [chap3Theory.Omega_starloops] THEN
    METIS_TAC [chap2Theory.bnf_Omega]
  ]);

(* yet another K - this one is the set of machines that terminate when
   given their own index as input *)
val K_def = Define`
  K = { Mi | ∃z. Phi Mi Mi = SOME z }
`;

val K_re = store_thm(
  "K_re",
  ``re K``,
  SRW_TAC [][K_def, re_semidp] THEN
  Q.EXISTS_TAC
    `dBnum (fromTerm (LAM "e" (UM @@ (cnpair @@ VAR "e" @@ VAR "e"))))` THEN
  GEN_TAC THEN
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [Phi_def])) THEN
  SRW_TAC [][] THEN
  SIMP_TAC (bsrw_ss()) [cnpair_behaviour] THEN
  EQ_TAC THEN1
    (SRW_TAC [][PhiSOME_UM] THEN ASM_SIMP_TAC (bsrw_ss()) [bnf_bnf_of]) THEN
  METIS_TAC [UM_bnf, bnf_of_SOME, nstar_lameq]);

val K_not_recursive = store_thm(
  "K_not_recursive",
  ``¬recursive K``,
  STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [recursive_def, K_def] THEN
  Q.ABBREV_TAC `
   Gbody = LAM "z" (ceqnat @@ church 1
                           @@ (UM @@ (cnpair @@ church M @@ VAR "z"))
                           @@ Ω
                           @@ church 1)
  ` THEN
  Q.ABBREV_TAC `G = dBnum (fromTerm Gbody)` THEN
  `toTerm (numdB G) = Gbody` by SRW_TAC [][Abbr`G`] THEN
  Cases_on `Phi G G` THENL [
    FIRST_ASSUM MP_TAC THEN SIMP_TAC (srw_ss()) [Phi_def] THEN
    ASM_SIMP_TAC (bsrw_ss()) [Abbr`Gbody`, cnpair_behaviour] THEN
    `Phi M G = SOME 0` by SRW_TAC [][] THEN
    `UM @@ church (M ⊗ G) -n->* church 0`
       by FULL_SIMP_TAC (srw_ss()) [PhiSOME_UM] THEN
    ASM_SIMP_TAC (bsrw_ss()) [ceqnat_behaviour, cB_behaviour, bnf_bnf_of],

    FIRST_ASSUM MP_TAC THEN SIMP_TAC (srw_ss()) [Phi_def] THEN
    ASM_SIMP_TAC (bsrw_ss()) [Abbr`Gbody`, cnpair_behaviour] THEN
    `Phi M G = SOME 1` by SRW_TAC [][] THEN
    `UM @@ church (M ⊗ G) -n->* church 1`
       by FULL_SIMP_TAC (srw_ss()) [PhiSOME_UM] THEN
    ASM_SIMP_TAC (bsrw_ss()) [ceqnat_behaviour, cB_behaviour]
  ]);

(* ----------------------------------------------------------------------
    r.e. closure properties
   ---------------------------------------------------------------------- *)


val re_INTER_I = store_thm(
  "re_INTER_I",
  ``re s ∧ re t ⇒ re (s ∩ t)``,
  SRW_TAC [][re_semidp] THEN
  Q.EXISTS_TAC `
    dBnum (fromTerm (LAM "e" (
      cbnf_ofk @@ (K @@ (cbnf_ofk @@ I
                                  @@ (cdAPP @@ cDB (numdB N')
                                            @@ (cchurch @@ VAR "e"))))
               @@ (cdAPP @@ cDB (numdB N) @@ (cchurch @@ VAR "e")))))
  ` THEN
  SIMP_TAC (bsrw_ss()) [Phi_def, cchurch_behaviour, cdAPP_behaviour] THEN
  Q.X_GEN_TAC `e` THEN Cases_on `e ∈ s` THENL [
    `∃z. Phi N e = SOME z` by METIS_TAC [] THEN
    IMP_RES_TAC PhiSOME_cbnf_ofk THEN
    ASM_SIMP_TAC (bsrw_ss()) [] THEN
    Cases_on `e ∈ t` THENL [
      `∃w. Phi N' e = SOME w` by METIS_TAC [] THEN
      FIRST_ASSUM (STRIP_ASSUME_TAC o MATCH_MP (GEN_ALL PhiSOME_cbnf_ofk)) THEN
      ASM_SIMP_TAC (bsrw_ss()) [bnf_bnf_of],

      `Phi N' e = NONE` by METIS_TAC [TypeBase.nchotomy_of ``:'a option``] THEN
      ASM_SIMP_TAC (srw_ss()) [PhiNONE_cbnf_ofk]
    ],

    `Phi N e = NONE` by METIS_TAC [TypeBase.nchotomy_of ``:'a option``] THEN
    ASM_SIMP_TAC (srw_ss()) [PhiNONE_cbnf_ofk]
  ]);

(* val re_UNION_I = store_thm(
  "re_UNION_I",
  ``re s ∧ re t ⇒ re (s ∪ t)``,
  SRW_TAC [][re_semidp] THEN
  Q.EXISTS_TAC `
    dBnum (fromTerm (LAM "e" (
      chap2$Y @@ (LAM "loop" (LAM "n" (
        cor @@ (cbnf @@ (csteps @@ VAR "n"
                                @@ (cdAPP @@ cDB (numdB N)
                                          @@ (cchurch @@ VAR "e"))))
            @@ (cor
                  @@ (cbnf @@ (csteps @@ VAR "n"
                               @@ (cdAPP @@ cDB (numdB N')
                                         @@ (cchurch @@ VAR "e"))))
                  @@ (VAR "loop" @@ (csuc @@ VAR "n"))))))
           @@ church 0)))` THEN
  SIMP_TAC (bsrw_ss())[Phi_def, chap2Theory.YYf,
                       Once chap2Theory.YffYf,
                       cchurch_behaviour, cdAPP_behaviour,
                       cbnf_behaviour] THEN
*)




val _ = export_theory ()
