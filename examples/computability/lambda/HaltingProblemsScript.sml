Theory HaltingProblems
Ancestors
  churchDB churchbool normal_order term chap3 pure_dB
Libs
  binderLib reductionEval

val _ = set_trace "Unicode" 1

fun bsrw_ss() = betafy (srw_ss())
fun Store_thm (trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

(* ----------------------------------------------------------------------
    Halting Problems.

    HP_selfapp is where a diagonalisation is done.  This is usually
    done by saying something like there is no computable function for
    determining if φ_n(n) terminates.  One reads this with "n" as the
    starting point, and this then leading to the use of φ_n to apply
    to it.

    But equally, we know that every f has an index, and this says that
    if you apply an f to its index, then the thing is undecidable.  In
    the λ-calculus setting, the cDB function is the function that
    takes a term to its "index", where here, the "index" is the data
    encoding the function.

    So, this proof is easiest to read as saying, given a term f, it's
    impossible to determine if it applied to its index halts.

    HP_nselfapp is a more traditional looking version, with natural
    numbers as indexes.
   ---------------------------------------------------------------------- *)

Theorem HP_selfapp:
    ¬∃M.
         ∀t. M @@ cDB (fromTerm t) -n->*
             cB (has_bnf (t @@ cDB (fromTerm t)))
Proof
  STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  Q_TAC (NEW_TAC "z") `FV M` THEN
  Q.ABBREV_TAC `G = LAM z (M @@ VAR z @@ Ω @@ cB T)` THEN
  `G @@ cDB (fromTerm G) -β-> M @@ cDB (fromTerm G) @@ Ω @@ cB T`
      by SRW_TAC [][chap3Theory.ccbeta_rwt, lemma14b, Abbr`G`] THEN
  `M @@ cDB (fromTerm G) @@ Ω @@ cB T
      -β->*
   cB (has_bnf (G @@ cDB (fromTerm G))) @@ Ω @@ cB T`
      by SRW_TAC [][chap3Theory.betastar_APPl, nstar_betastar] THEN
  Cases_on `has_bnf (G @@ cDB (fromTerm G))` THEN
  FULL_SIMP_TAC (srw_ss()) [] THENL [
    `cB T @@ Ω @@ cB T -β->* Ω`
       by SRW_TAC [][nstar_betastar, cB_behaviour] THEN
    `G @@ cDB (fromTerm G) -β->* Ω`
       by METIS_TAC [relationTheory.RTC_RULES,
                     relationTheory.RTC_CASES_RTC_TWICE] THEN
    METIS_TAC [Omega_reachable_no_bnf],

    `cB F @@ Ω @@ cB T -β->* cB T`
       by SRW_TAC [][nstar_betastar, cB_behaviour] THEN
    `G @@ cDB (fromTerm G) -β->* cB T`
       by METIS_TAC [relationTheory.RTC_CASES_RTC_TWICE,
                     relationTheory.RTC_RULES] THEN
    `has_bnf (G @@ cDB (fromTerm G))`
       by METIS_TAC [chap3Theory.has_bnf_thm, bnf_cB]
  ]
QED


val _ = temp_overload_on ("φ", ``λn. toTerm (numdB n)``)

Theorem HP_nselfapp:
    ¬∃M. ∀n. M @@ church n -n->* cB (has_bnf (φ n @@ church n))
Proof
  STRIP_TAC THEN
  Q_TAC (NEW_TAC "z") `FV M` THEN
  Q.ABBREV_TAC `G = LAM z (M @@ VAR z @@ Ω @@ cB T)` THEN
  Q.ABBREV_TAC `Gi = dBnum (fromTerm G)` THEN
  Q.ABBREV_TAC `hbnf = has_bnf` THEN
  `G @@ church Gi == cB (has_bnf (G @@ church Gi)) @@ Ω @@ cB T`
     by ASM_SIMP_TAC (bsrw_ss()) [Abbr`G`, Abbr`Gi`, toTerm_thm] THEN
  Cases_on `has_bnf (G @@ church Gi)` THEN
  FULL_SIMP_TAC (bsrw_ss()) [cB_behaviour] THENL [
    `G @@ church Gi -β->* Ω`
       by METIS_TAC [lameq_betaconversion, theorem3_13, beta_CR,
                     Omega_starloops] THEN
    METIS_TAC [Omega_reachable_no_bnf],

    `G @@ church Gi -β->* cB T`
       by METIS_TAC [betastar_lameq_bnf, bnf_cB] THEN
    METIS_TAC [has_bnf_thm, bnf_cB]
  ]
QED

(* Impossibility of determining whether or not arbitrary function applied
   to arbitrary argument will terminate. *)
Theorem HP_fx:
    ¬∃M. ∀f x. M @@ cDB (fromTerm f) @@ x -n->* cB (has_bnf (f @@ x))
Proof
  STRIP_TAC THEN Q_TAC (NEW_TAC "z") `FV M` THEN
  Q.ABBREV_TAC `G = LAM z (M @@ VAR z @@ VAR z)` THEN
  `∀t. G @@ cDB (fromTerm t) -n-> M @@ cDB (fromTerm t) @@ cDB (fromTerm t)`
      by SRW_TAC [][noreduct_characterisation, noreduct_thm, Abbr`G`,
                    lemma14b] THEN
  `∀t. M @@ cDB (fromTerm t) @@ cDB (fromTerm t) -n->*
       cB (has_bnf (t @@ cDB (fromTerm t)))`
      by SRW_TAC [][] THEN
  `∀t. G @@ cDB (fromTerm t) -n->* cB (has_bnf (t @@ cDB (fromTerm t)))`
     by METIS_TAC [relationTheory.RTC_RULES] THEN
  METIS_TAC [HP_selfapp]
QED

(* Impossibility of deciding whether or not an arbitrary term has a β-nf.
   Needs the computability of the encoding function cDB. *)
Theorem HP_bnf:
     ¬∃M. ∀t. M @@ cDB (fromTerm t) -n->* cB (has_bnf t)
Proof
  STRIP_TAC THEN Q_TAC (NEW_TAC "z") `FV M` THEN
  Q.ABBREV_TAC `G = LAM z (M @@ (cdAPP @@ VAR z @@ (ccDB @@ VAR z)))` THEN
  `∀t. G @@ cDB (fromTerm t) -n->* cB (has_bnf (t @@ cDB (fromTerm t)))`
    by (ASM_SIMP_TAC (bsrw_ss()) [Abbr`G`, cdAPP_behaviour,
                                  ccDB_behaviour] THEN
        REPEAT GEN_TAC THEN
        `∀f x. dAPP (fromTerm f) (fromTerm x) = fromTerm (f @@ x)`
           by SRW_TAC [][] THEN
        ASM_SIMP_TAC (betafy bool_ss) [] THEN
        MATCH_MP_TAC nstar_betastar THEN ASM_SIMP_TAC (srw_ss()) []) THEN
  METIS_TAC [HP_selfapp]
QED

