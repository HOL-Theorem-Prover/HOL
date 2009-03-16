(* Church style encoding of de Bruijn terms, giving us 
    "The Power of Reflection"
*)

open HolKernel boolLib bossLib Parse binderLib

open churchnumTheory churchboolTheory pure_dBTheory
open reductionEval pred_setTheory termTheory chap3Theory

val _ = new_theory "churchDB"

val _ = set_trace "Unicode" 1
fun Store_thm (trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val ciDB_def = Define`
  (ciDB (dV i) = VAR "v" @@ church i) ∧
  (ciDB (dAPP M N) = VAR "c" @@ ciDB M @@ ciDB N) ∧
  (ciDB (dABS M) = VAR "a" @@ ciDB M)
`;

val FV_ciDB = store_thm(
  "FV_ciDB",
  ``∀x. x ∈ FV (ciDB t) ⇒ (x = "v") ∨ (x = "c") ∨ (x = "a")``,
  Induct_on `t` THEN SRW_TAC [][ciDB_def] THEN SRW_TAC [][]);
val NOT_IN_FV_ciDB = store_thm(
  "NOT_IN_FV_ciDB",
  ``x ≠ "v" ∧ x ≠ "c" ∧ x ≠ "a" ⇒ x ∉ FV (ciDB t)``,
  METIS_TAC [FV_ciDB]);

val is_abs_ciDB = Store_thm(
  "is_abs_ciDB",  
  ``is_abs (ciDB t) ⇔ F``,
  Induct_on `t` THEN SRW_TAC [][ciDB_def]);

val bnf_ciDB = Store_thm(
  "bnf_ciDB",
  ``bnf (ciDB t)``,
  Induct_on `t` THEN SRW_TAC [][ciDB_def]);

val ciDB_11 = Store_thm(
  "ciDB_11",
  ``(ciDB t1 = ciDB t2) = (t1 = t2)``,
  Q.ID_SPEC_TAC `t2` THEN Induct_on `t1` THEN SRW_TAC [][ciDB_def] THEN 
  Cases_on `t2` THEN SRW_TAC [][ciDB_def]);

val cDB_def = Define`cDB t = LAM "v" (LAM "c" (LAM "a" (ciDB t)))`

val cDB_11 = Store_thm(
  "cDB_11",
  ``(cDB t1 = cDB t2) = (t1 = t2)``,
  SRW_TAC [][cDB_def]);
val FV_cDB = Store_thm(
  "FV_cDB",
  ``FV (cDB t) = {}``,
  SRW_TAC [][cDB_def, EXTENSION] THEN METIS_TAC [FV_ciDB]);
val bnf_cDB = Store_thm(
  "bnf_cDB",
  ``bnf (cDB t)``,
  SRW_TAC [][cDB_def]);

(*
dfv (VAR j) = λi. i = j
dfv (dAPP t1 t2) = λi. dfv t1 i ∨ dfv t2 i
dfv (dABS t) = λi. dfv t (i + 1)
*)

val cdFV_def = Define`
  cdFV = LAM "v" (LAM "t"
           (VAR "t" @@ 
              (LAM "j" (LAM "i" (ceqnat @@ VAR "i" @@ VAR "j"))) @@ 
              (LAM "r1" (LAM "r2" (LAM "i" (cor @@ (VAR "r1" @@ VAR "i") @@ 
                                                   (VAR "r2" @@ VAR "i"))))) @@
              (LAM "r" (LAM "i" (VAR "r" @@ (csuc @@ (VAR "i"))))) @@ 
              (VAR "v")))
`;

val NOT_IN_SUB = prove(
  ``x ∉ FV M ∧ (x ≠ v ⇒ x ∉ FV N) ⇒ x ∉ FV ([M/v]N)``,
  SRW_TAC [][termTheory.FV_SUB] THEN METIS_TAC []);

val FV_cdFV = Store_thm(
  "FV_cdFV",
  ``FV cdFV = {}``,
  SRW_TAC [][cdFV_def, EXTENSION] THEN METIS_TAC []);
val cdFV_behaviour = store_thm(
  "cdFV_behaviour",
  ``∀i. cdFV @@ church i @@ cDB t -n->* cB (i ∈ dFV t)``,
  SIMP_TAC (bsrw_ss()) [cdFV_def, cDB_def] THEN 
  Q.MATCH_ABBREV_TAC 
    `∀i. [Abs/"a"] ([App/"c"] ([Var/"v"] (ciDB t))) @@ church i -β->* 
         cB (i ∈ dFV t)` THEN 
  `FV Var = {}` by (SRW_TAC [][Abbr`Var`, EXTENSION] THEN METIS_TAC []) THEN 
  `FV App = {}` by (SRW_TAC [][Abbr`App`, EXTENSION] THEN METIS_TAC []) THEN 
  `FV Abs = {}` by (SRW_TAC [][Abbr`Abs`, EXTENSION] THEN METIS_TAC []) THEN 
  Induct_on `t` THENL [
    ASM_SIMP_TAC (bsrw_ss()) [ciDB_def] THEN 
    ASM_SIMP_TAC (bsrw_ss()) [ceqnat_behaviour, Abbr`Var`, EQ_SYM_EQ],

    ASM_SIMP_TAC (bsrw_ss()) [ciDB_def] THEN GEN_TAC THEN 
    Q.MATCH_ABBREV_TAC 
      `App @@ arg_t @@ arg_t' @@ church i -β->* 
         cB (i ∈ dFV t ∨ i ∈ dFV t')` THEN
    `FV arg_t = {}`
       by SRW_TAC [][Abbr`arg_t`, EXTENSION, NOT_IN_SUB, NOT_IN_FV_ciDB] THEN 
    `FV arg_t' = {}`
       by SRW_TAC [][Abbr`arg_t'`, EXTENSION, NOT_IN_SUB, NOT_IN_FV_ciDB] THEN 
    ASM_SIMP_TAC (bsrw_ss()) [Abbr`App`, cor_behaviour],

    ASM_SIMP_TAC (bsrw_ss()) [ciDB_def] THEN GEN_TAC THEN 
    Q.MATCH_ABBREV_TAC 
      `Abs @@ arg_t @@ church i -β->* cB (i + 1 ∈ dFV t)` THEN 
    `FV arg_t = {}`
      by SRW_TAC [][Abbr`arg_t`, EXTENSION, NOT_IN_FV_ciDB, NOT_IN_SUB] THEN 
    ASM_SIMP_TAC (bsrw_ss()) [Abbr`Abs`, csuc_behaviour, 
                              arithmeticTheory.ADD1]
  ]);

(* ---------------------------------------------------------------------- 
    The constructors of the type in the λ-calculus
   ---------------------------------------------------------------------- *)

val cdV_def = Define`
  cdV = LAM "n" (LAM "v" (LAM "c" (LAM "a" (VAR "v" @@ VAR "n"))))
`;
val FV_cdV = Store_thm(
  "FV_cdV",
  ``FV cdV = {}``,
  SRW_TAC [][cdV_def, EXTENSION] THEN METIS_TAC []);
val bnf_cdV = Store_thm("bnf_cdV", ``bnf cdV``, SRW_TAC [][cdV_def])
val cdV_behaviour = store_thm(
  "cdV_behaviour",
  ``cdV @@ church n -n->* cDB (dV n)``,
  SIMP_TAC (bsrw_ss()) [cdV_def, cDB_def, ciDB_def]);

val cdAPP_def = Define`
  cdAPP = LAM "M" (LAM "N" (LAM "v" (LAM "c" (LAM "a" 
            (VAR "c" @@ (VAR "M" @@ VAR "v" @@ VAR "c" @@ VAR "a") @@ 
                        (VAR "N" @@ VAR "v" @@ VAR "c" @@ VAR "a"))))))
`
val FV_cdAPP = Store_thm(
  "FV_cdAPP",
  ``FV cdAPP = {}``,
  SRW_TAC [][cdAPP_def, EXTENSION] THEN METIS_TAC []);
val bnf_cdAPP = Store_thm("bnf_cdAPP", ``bnf cdAPP``, SRW_TAC [][cdAPP_def])
val cdAPP_behaviour = store_thm(
  "cdAPP_behaviour",
  ``cdAPP @@ cDB M @@ cDB N -n->* cDB (dAPP M N)``,
  SIMP_TAC (bsrw_ss()) [cdAPP_def] THEN 
  SIMP_TAC (bsrw_ss()) [cDB_def, ciDB_def]);

val cdABS_def = Define`
  cdABS = LAM "M" (LAM "v" (LAM "c" (LAM "a" 
            (VAR "a" @@ (VAR "M" @@ VAR "v" @@ VAR "c" @@ VAR "a")))))
`;
val FV_cdABS = Store_thm(
  "FV_cdABS",
  ``FV cdABS = {}``,
  SRW_TAC [][cdABS_def, EXTENSION] THEN METIS_TAC []);
val bnf_cdABS = Store_thm("bnf_cdABS", ``bnf cdABS``, SRW_TAC [][cdABS_def])
val cdABS_behaviour = store_thm(
  "cdABS_behaviour",
  ``cdABS @@ cDB M -n->* cDB (dABS M)``,
  SIMP_TAC (bsrw_ss()) [cdABS_def] THEN 
  SIMP_TAC (bsrw_ss()) [cDB_def, ciDB_def]);

(* 
val lift_def = Define`
  (lift (dV i) k = if i < k then dV i else dV (i + 1)) /\
  (lift (dAPP s t) k = dAPP (lift s k) (lift t k)) /\
  (lift (dABS s) k = dABS (lift s (k + 1)))
`;
*)

val clift_def = Define`
  clift = 
  LAM "t"
    (VAR "t" 
         @@ (LAM "i" (LAM "k" (cless @@ VAR "i" @@ VAR "k" 
                                     @@ (cdV @@ VAR "i")
                                     @@ (cdV @@ (csuc @@ VAR "i"))))) 
         @@ (LAM "r1" (LAM "r2" (LAM "k"
               (cdAPP @@ (VAR "r1" @@ VAR "k") @@ (VAR "r2" @@ VAR "k")))))
         @@ (LAM "r" (LAM "k"
               (cdABS @@ (VAR "r" @@ (csuc @@ VAR "k"))))))
`;

val FV_clift = Store_thm(
  "FV_clift",
  ``FV clift = {}``,
  SRW_TAC [][clift_def, EXTENSION] THEN METIS_TAC []);

val clift_behaviour = store_thm(
  "clift_behaviour",  
  ``clift @@ cDB M @@ church k -n->* cDB (lift M k)``,
  SIMP_TAC (bsrw_ss()) [clift_def] THEN 
  Q.MATCH_ABBREV_TAC 
    `cDB M @@ Var @@ App @@ Abs @@ church k -β->* cDB (lift M k)` THEN 
  `(FV Var = {}) ∧ (FV App = {}) ∧ (FV Abs = {})` 
     by (SRW_TAC [][Abbr`Var`, Abbr`App`, Abbr`Abs`, EXTENSION] THEN 
         METIS_TAC []) THEN 
  ASM_SIMP_TAC (bsrw_ss()) [cDB_def] THEN 
  Q.ID_SPEC_TAC `k` THEN Induct_on `M` THENL [
    ASM_SIMP_TAC (bsrw_ss()) [ciDB_def] THEN 
    ASM_SIMP_TAC (bsrw_ss()) [Abbr`Var`, cless_behaviour, cdV_behaviour, 
                              csuc_behaviour, arithmeticTheory.ADD1] THEN 
    SRW_TAC [][] THEN 
    SIMP_TAC (bsrw_ss()) [cB_behaviour, cDB_def],

    ASM_SIMP_TAC (bsrw_ss()) [ciDB_def] THEN GEN_TAC THEN 
    Q.MATCH_ABBREV_TAC 
      `App @@ arg1 @@ arg2 @@ church k -β->* result` THEN 
    `(FV arg1 = {}) ∧ (FV arg2 = {})`
       by SRW_TAC [][NOT_IN_FV_ciDB, NOT_IN_SUB, EXTENSION, Abbr`arg1`,
                     Abbr`arg2`] THEN 
    Q.UNABBREV_TAC `result` THEN 
    ASM_SIMP_TAC (bsrw_ss()) [Abbr`App`] THEN 
    SIMP_TAC (srw_ss()) [GSYM cDB_def] THEN 
    ASM_SIMP_TAC (bsrw_ss()) [cdAPP_behaviour] THEN 
    ASM_SIMP_TAC (srw_ss()) [cDB_def, ciDB_def],

    ASM_SIMP_TAC (bsrw_ss()) [ciDB_def] THEN GEN_TAC THEN 
    Q.MATCH_ABBREV_TAC `Abs @@ arg @@ church k -β->* result` THEN 
    Q.UNABBREV_TAC `result` THEN 
    `FV arg = {}` 
      by SRW_TAC [][Abbr`arg`, EXTENSION, NOT_IN_SUB, NOT_IN_FV_ciDB] THEN 
    ASM_SIMP_TAC (bsrw_ss()) [Abbr`Abs`, csuc_behaviour, 
                              arithmeticTheory.ADD1] THEN 
    ASM_SIMP_TAC (bsrw_ss()) [GSYM cDB_def, cdABS_behaviour] THEN 
    SIMP_TAC (srw_ss()) [cDB_def, ciDB_def]
  ]);

open normal_orderTheory

(* this is where a diagonalisation is done.  This is usually done by saying 
   something like there is no computable function for determining if φ_n(n) 
   terminates.  In this statement of the result, it's easiest to read this 
   with "n" is the key, and this then leading to the use of φ_n to apply to 
   it.

   But equally, we know that every f has an index, and this says that if you
   apply an f to its index, then the thing is undecidable.  In the λ-calculus
   setting, the cDB function is the function that takes a term to its "index",
   where here, the "index" is the data encoding the function. 

   Will perhaps add a more traditional looking version with natural numbers 
   too.
*)
val HP_selfapp = store_thm(
  "HP_selfapp",
  ``¬∃M. 
         ∀t. M @@ cDB (fromTerm t) -n->* 
             cB (has_bnf (t @@ cDB (fromTerm t)))``,
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
  ]);

(* Impossibility of determining whether or not arbitrary function applied
   to arbitrary argument will terminate. *)    
val HP_fx = store_thm(
  "HP_fx",
  ``¬∃M. ∀f x. M @@ cDB (fromTerm f) @@ x -n->* cB (has_bnf (f @@ x))``,
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
  METIS_TAC [HP_selfapp]);
  
(* Not yet sure how to show "HP_bnf", that   
     ``¬∃M. ∀t. M @@ cDB (fromTerm t) -n->* cB (has_bnf t)``
*)  

val _ = export_theory()
