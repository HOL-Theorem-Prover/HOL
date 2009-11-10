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
      (LAM "e" (cfindleast
        @@ (LAM "n" (cmem
           @@ VAR "e"
           @@ (cmap
                 @@ cforce_num
                 @@ (cfilter
                       @@ cbnf
                       @@ (ctabulate
                             @@ VAR "n"
                             @@ (LAM "j"
                                 (csteps
                                    @@ VAR "n"
                                    @@ (cdAPP
                                          @@ (cnumdB @@ church Mi)
                                          @@ (cchurch @@ VAR "j")))))))))
        @@ I)))
  ` THEN
  SIMP_TAC (bsrw_ss()) [Phi_def, cnumdB_behaviour] THEN
  Q.X_GEN_TAC `e` THEN
  Q.HO_MATCH_ABBREV_TAC
    `e ∈ s ⇔ ∃r. bnf_of (cfindleast @@ P @@ I) = SOME r` THEN
  `∀n. P @@ church n ==
       cB (MEM e (MAP force_num
            (FILTER bnf (GENLIST
                          (λj. steps n (toTerm (numdB Mi) @@ church j))
                          n))))`
     by (SIMP_TAC (bsrw_ss()) [Abbr`P`, ctabulate_cvlist] THEN
         SIMP_TAC (bsrw_ss() ++ boolSimps.DNF_ss)
                  [cfilter_cvlist, MEM_GENLIST,
                   csteps_behaviour, cchurch_behaviour,
                   cdAPP_behaviour, cbnf_behaviour,
                   Cong cvlist_genlist_cong, cmap_cvlist,
                   cmem_cvlist, cforce_num_behaviour,
                   listTheory.MEM_MAP, listTheory.MEM_FILTER] THEN
         SIMP_TAC (bsrw_ss()) [listTheory.EXISTS_MAP, EXISTS_FILTER,
                               EXISTS_GENLIST, cdAPP_behaviour,
                               csteps_behaviour, cchurch_behaviour,
                               cbnf_behaviour, cforce_num_behaviour,
                               ceqnat_behaviour] THEN
         METIS_TAC []) THEN
  `∀n. ∃b. P @@ church n == cB b` by METIS_TAC [] THEN
  Q.RM_ABBREV_TAC `P` THEN
  SRW_TAC [][EQ_IMP_THM, Phi_def] THENL [
    `toTerm (numdB Mi) @@ church j -n->* z ∧ bnf z`
      by METIS_TAC [bnf_of_SOME] THEN
    `∃n. steps n (toTerm (numdB Mi) @@ church j) = z`
      by METIS_TAC [stepsTheory.bnf_steps] THEN
    `steps (MAX (j + 1) n) (toTerm (numdB Mi) @@ church j) = z`
      by (SRW_TAC [][] THEN Cases_on `MAX (j + 1) n = n`
            THEN1 SRW_TAC [][] THEN
          MATCH_MP_TAC bnf_steps_upwards_closed THEN
          FULL_SIMP_TAC (srw_ss() ++ ARITH_ss)
                        [arithmeticTheory.MAX_DEF]) THEN
    `P @@ church (MAX (j + 1) n) == cB T`
      by (ASM_SIMP_TAC (bsrw_ss()) [listTheory.MEM_MAP, listTheory.MEM_FILTER,
                                    MEM_GENLIST] THEN
          METIS_TAC [DECIDE ``j < j + 1``]) THEN
    `cfindleast @@ P @@ I == I @@ church (LEAST n. P @@ church n == cB T)`
      by (MATCH_MP_TAC (GEN_ALL cfindleast_termI) THEN METIS_TAC []) THEN
    ASM_SIMP_TAC (bsrw_ss()) [bnf_bnf_of],

    (* other direction: that if our enum2semi function does terminate on an
       x, then x does indeed appear in the enumeration
    *)
    `cfindleast @@ P @@ I == r ∧ bnf r`
       by METIS_TAC [bnf_of_SOME, nstar_lameq] THEN
    `∃m. P @@ church m == cB T`
       by METIS_TAC [cfindleast_bnfE] THEN
    Q.PAT_ASSUM `P @@ church m == cB T` MP_TAC THEN
    ASM_SIMP_TAC (bsrw_ss()) [listTheory.MEM_MAP, listTheory.MEM_FILTER,
                              MEM_GENLIST] THEN
    METIS_TAC [bnf_steps]
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

val re_UNION_I = store_thm(
  "re_UNION_I",
  ``re s ∧ re t ⇒ re (s ∪ t)``,
  SRW_TAC [][re_semidp] THEN
  Q.EXISTS_TAC `
    dBnum (fromTerm (LAM "e" (
      cfindleast @@ (LAM "n" (
        cor @@ (cbnf @@ (csteps @@ VAR "n" @@ (cdAPP @@ cDB (numdB N)
                                                     @@ (cchurch @@ VAR "e"))))
            @@ (cbnf @@ (csteps @@ VAR "n"
                                @@ (cdAPP @@ cDB (numdB N')
                                          @@ (cchurch @@ VAR "e"))))))
                 @@ I)))` THEN
  SIMP_TAC (bsrw_ss()) [Phi_def, cchurch_behaviour, cdAPP_behaviour] THEN
  Q.X_GEN_TAC `e` THEN
  Q.HO_MATCH_ABBREV_TAC
    `e ∈ s ∨ e ∈ t ⇔ ∃r. bnf_of (cfindleast @@ P @@ I) = SOME r` THEN
  `∀n. P @@ church n == cB (bnf (steps n (toTerm (numdB N) @@ church e)) ∨
                            bnf (steps n (toTerm (numdB N') @@ church e)))`
     by (SIMP_TAC (bsrw_ss()) [Abbr`P`] THEN
         SIMP_TAC (bsrw_ss()) [cbnf_behaviour, csteps_behaviour,
                               cor_behaviour]) THEN
  Q.RM_ABBREV_TAC `P` THEN
  `∀n. ∃b. P @@ church n == cB b` by METIS_TAC [] THEN
  SRW_TAC [][Phi_def, EQ_IMP_THM] THENL [
    `toTerm (numdB N) @@ church e == z ∧ bnf z`
      by METIS_TAC [bnf_of_SOME, nstar_lameq] THEN
    `∃n. bnf (steps n (toTerm (numdB N) @@ church e))`
      by METIS_TAC [bnf_steps] THEN
    `P @@ church n == cB T` by ASM_SIMP_TAC (bsrw_ss()) [] THEN
    `cfindleast @@ P @@ I == I @@ church (LEAST n. P @@ church n == cB T)`
      by (MATCH_MP_TAC (GEN_ALL cfindleast_termI) THEN
          METIS_TAC []) THEN
    ASM_SIMP_TAC (bsrw_ss()) [bnf_bnf_of],

    `toTerm (numdB N') @@ church e == z ∧ bnf z`
      by METIS_TAC [bnf_of_SOME, nstar_lameq] THEN
    `∃n. bnf (steps n (toTerm (numdB N') @@ church e))`
      by METIS_TAC [bnf_steps] THEN
    `P @@ church n == cB T` by ASM_SIMP_TAC (bsrw_ss()) [] THEN
    `cfindleast @@ P @@ I == I @@ church (LEAST n. P @@ church n == cB T)`
      by (MATCH_MP_TAC (GEN_ALL cfindleast_termI) THEN
          METIS_TAC []) THEN
    ASM_SIMP_TAC (bsrw_ss()) [bnf_bnf_of],

    `cfindleast @@ P @@ I == r ∧ bnf r`
      by METIS_TAC [bnf_of_SOME, nstar_lameq] THEN
    `∃n. P @@ church n == cB T` by METIS_TAC [cfindleast_bnfE] THEN
    Q.PAT_ASSUM `P @@ X == cB T` MP_TAC THEN
    ASM_SIMP_TAC (bsrw_ss()) [] THEN
    METIS_TAC [bnf_steps]
  ]);

val _ = export_theory ()
