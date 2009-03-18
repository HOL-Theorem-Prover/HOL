(* Church style encoding of de Bruijn terms, giving us 
    "The Power of Reflection"
*)

open HolKernel boolLib bossLib Parse binderLib

open churchnumTheory churchboolTheory pure_dBTheory
open reductionEval pred_setTheory termTheory chap3Theory

val _ = new_theory "churchDB"

val _ = set_trace "Unicode" 1
fun Store_thm (trip as (n,t,tac)) = store_thm trip before export_rewrites [n]

val DISJ_IMP_EQ = Store_thm(
  "DISJ_IMP_EQ",
  ``((x = y) ∨ P ⇔ (x ≠ y ⇒ P)) ∧
    (P ∨ (x = y) ⇔ (x ≠ y ⇒ P)) ∧
    (x ≠ y ∨ P ⇔ ((x = y) ⇒ P)) ∧
    (P ∨ x ≠ y ⇔ ((x = y) ⇒ P))``,
  METIS_TAC []);

val ciDB_def = Define`
  (ciDB (dV i) = VAR "v" @@ church i) ∧
  (ciDB (dAPP M N) = VAR "c" @@ ciDB M @@ ciDB N) ∧
  (ciDB (dABS M) = VAR "a" @@ ciDB M)
`;

val FV_ciDB = store_thm(
  "FV_ciDB",
  ``∀x. x ∈ FV (ciDB t) ⇒ (x = "v") ∨ (x = "c") ∨ (x = "a")``,
  Induct_on `t` THEN SRW_TAC [][ciDB_def] THEN METIS_TAC []);
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
  SRW_TAC [][cdFV_def, FV_EMPTY]); 
val cdFV_behaviour = store_thm(
  "cdFV_behaviour",
  ``∀i. cdFV @@ church i @@ cDB t -n->* cB (i ∈ dFV t)``,
  SIMP_TAC (bsrw_ss()) [cdFV_def, cDB_def] THEN 
  Q.MATCH_ABBREV_TAC 
    `∀i. [Abs/"a"] ([App/"c"] ([Var/"v"] (ciDB t))) @@ church i -β->* 
         cB (i ∈ dFV t)` THEN 
  `(FV Var = {}) ∧ (FV App = {}) ∧ (FV Abs = {})` 
      by SRW_TAC [][Abbr`Var`, Abbr`App`, Abbr`Abs`, FV_EMPTY] THEN
  Induct_on `t` THENL [
    ASM_SIMP_TAC (bsrw_ss()) [ciDB_def] THEN 
    ASM_SIMP_TAC (bsrw_ss()) [ceqnat_behaviour, Abbr`Var`, EQ_SYM_EQ],

    ASM_SIMP_TAC (bsrw_ss()) [ciDB_def] THEN GEN_TAC THEN 
    Q.MATCH_ABBREV_TAC 
      `App @@ arg_t @@ arg_t' @@ church i -β->* 
         cB (i ∈ dFV t ∨ i ∈ dFV t')` THEN
    `(FV arg_t = {}) ∧ (FV arg_t' = {})`
       by SRW_TAC [][Abbr`arg_t`, Abbr`arg_t'`, FV_EMPTY, NOT_IN_SUB, 
                     NOT_IN_FV_ciDB] THEN 
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
  SRW_TAC [][cdV_def, FV_EMPTY]);
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
  SRW_TAC [][cdAPP_def, FV_EMPTY]);
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
  SRW_TAC [][cdABS_def, FV_EMPTY]);
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
  SRW_TAC [][clift_def, FV_EMPTY]);

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

(* ----------------------------------------------------------------------
    substitution 
   ---------------------------------------------------------------------- *)

(* (∀s k i. sub s k (dV i) = if i = k then s else dV i) ∧
   (∀s k t u. sub s k (dAPP t u) = dAPP (sub s k t) (sub s k u)) ∧
   ∀s k t. sub s k (dABS t) = dABS (sub (lift s 0) (k + 1) t) *)

val csub_def = Define`
  csub = 
  LAM "s" (LAM "k" (LAM "t"
    (VAR "t" 
      @@ (LAM "i" (LAM "ss" (LAM "kk" 
           (ceqnat @@ VAR "i" @@ VAR "kk" @@ VAR "ss" @@ (cdV @@ VAR "i")))))
      @@ (LAM "r1" (LAM "r2" (LAM "ss" (LAM "kk"
           (cdAPP @@ (VAR "r1" @@ VAR "ss" @@ VAR "kk") 
                  @@ (VAR "r2" @@ VAR "ss" @@ VAR "kk"))))))
      @@ (LAM "r" (LAM "ss" (LAM "kk"
           (cdABS @@ (VAR "r" @@ (clift @@ VAR "ss" @@ church 0) 
                              @@ (csuc @@ VAR "kk"))))))
      @@ VAR "s" @@ VAR "k")))
`;
val FV_csub = Store_thm(
  "FV_csub",
  ``FV csub = {}``,
  SRW_TAC [][csub_def, FV_EMPTY]); 
           
val csub_behaviour = store_thm(
  "csub_behaviour",
  ``csub @@ cDB s @@ church k @@ cDB t -n->* cDB (sub s k t)``,
  SIMP_TAC (bsrw_ss()) [csub_def] THEN 
  Q.SPEC_THEN `t` SUBST_ALL_TAC cDB_def THEN 
  SIMP_TAC (bsrw_ss()) [] THEN 
  Q.MATCH_ABBREV_TAC 
    `[Abs/"a"] ([App/"c"] ([Var/"v"] (ciDB t))) @@ cDB s @@ church k 
       -β->* 
     cDB (sub s k t)` THEN 
  `∀v. v ∉ FV Var ∧ v ∉ FV App ∧ v ∉ FV Abs`
     by SRW_TAC [][Abbr`Var`, Abbr`Abs`, Abbr`App`] THEN
  Q.ABBREV_TAC `Inst = λx. [Abs/"a"] ([App/"c"] ([Var/"v"] x))` THEN 
  FIRST_ASSUM (ASSUME_TAC o GSYM o 
               SIMP_RULE bool_ss [FUN_EQ_THM, markerTheory.Abbrev_def]) THEN 
  ASM_SIMP_TAC bool_ss [] THEN 
  `∀M N. Inst (M @@ N) = Inst M @@ Inst N`
     by SRW_TAC [][Abbr`Inst`] THEN 
  `(Inst (VAR "a") = Abs) ∧ (Inst (VAR "c") = App) ∧ (Inst (VAR "v") = Var) ∧
   (∀n. Inst (church n) = church n)`
     by SRW_TAC [][Abbr`Inst`, lemma14b] THEN 
  MAP_EVERY Q.ID_SPEC_TAC [`s`,`k`] THEN Induct_on `t` THENL [
    ASM_SIMP_TAC (bsrw_ss()) [ciDB_def] THEN 
    SIMP_TAC (bsrw_ss()) [Abbr`Var`, ceqnat_behaviour, cdV_behaviour] THEN 
    REPEAT GEN_TAC THEN Cases_on `n = k` THEN 
    ASM_SIMP_TAC (bsrw_ss()) [cB_behaviour],

    ASM_SIMP_TAC (bsrw_ss()) [ciDB_def] THEN 
    `∀M N P Q. App @@ M @@ N @@ P @@ Q -n->* 
               cdAPP @@ (M @@ P @@ Q) @@ (N @@ P @@ Q)`
      by (Q.UNABBREV_TAC `App` THEN REPEAT GEN_TAC THEN 
          REPEAT (POP_ASSUM (K ALL_TAC)) THEN 
          FRESH_TAC THEN SRW_TAC [NORMSTAR_ss][tpm_fresh]) THEN 
    ASM_SIMP_TAC (bsrw_ss()) [cdAPP_behaviour],

    ASM_SIMP_TAC (bsrw_ss()) [ciDB_def] THEN 
    `∀M N P. Abs @@ M @@ N @@ P -n->* 
             cdABS @@ (M @@ (clift @@ N @@ church 0) @@ (csuc @@ P))`
      by (Q.UNABBREV_TAC `Abs` THEN REPEAT GEN_TAC THEN 
          REPEAT (POP_ASSUM (K ALL_TAC)) THEN FRESH_TAC THEN 
          SRW_TAC [NORMSTAR_ss][tpm_fresh]) THEN 
    ASM_SIMP_TAC (bsrw_ss()) 
                 [clift_behaviour, csuc_behaviour, cdABS_behaviour, 
                  arithmeticTheory.ADD1]
  ]);

val cdLAM_def = Define`
  cdLAM = LAM "v" (LAM "body"
            (cdABS @@ (csub @@ (cdV @@ church 0) 
                            @@ (cplus @@ (VAR "v") @@ church 1)
                            @@ (clift @@ (VAR "body") @@ church 0))))
`;

val FV_cdLAM = Store_thm(
  "FV_cdLAM",
  ``FV cdLAM = {}``,
  SRW_TAC [][FV_EMPTY, cdLAM_def]);

val cdLAM_behaviour = store_thm(
  "cdLAM_behaviour",
  ``cdLAM @@ church i @@ cDB t -n->* cDB (dLAM i t)``,
  SIMP_TAC (bsrw_ss()) [cdLAM_def, cdV_behaviour, cplus_behaviour, 
                        clift_behaviour, csub_behaviour, cdABS_behaviour, 
                        dLAM_def]);
  
(* ---------------------------------------------------------------------- 
    cichurch 

    create the internal structure of a church numeral (what is done by
    FUNPOW in the HOL world)
   ---------------------------------------------------------------------- *)

val cichurch_def = Define`
  cichurch = 
  LAM "n" 
    (VAR "n" 
       @@ (cdV @@ church 1)
       @@ (LAM "r" (cdAPP @@ (cdV @@ church 0) @@ VAR "r")))
`;

val FV_cichurch = Store_thm(
  "FV_cichurch",
  ``FV cichurch = {}``,
  SRW_TAC [][FV_EMPTY, cichurch_def]);

val FUNPOW_SUC = arithmeticTheory.FUNPOW_SUC
val cichurch_behaviour = store_thm(
  "cichurch_behaviour",
  ``cichurch @@ church n -n->* cDB (fromTerm (FUNPOW ((@@) (VAR (n2s 0))) n
                                                     (VAR (n2s 1))))``,
  SIMP_TAC (bsrw_ss()) [cichurch_def, church_behaviour] THEN 
  Induct_on `n` THENL [
    SIMP_TAC (bsrw_ss()) [cdV_behaviour],
    ASM_SIMP_TAC (bsrw_ss()) [FUNPOW_SUC, cdAPP_behaviour, cdV_behaviour]
  ]);

(* ----------------------------------------------------------------------
    cchurch

    Puts the abstractions over the internal church structure, giving an
    encoded church numeral 
   ---------------------------------------------------------------------- *)

val cchurch_def = Define`
  cchurch = LAM "n" (cdABS @@ (cdABS @@ (cichurch @@ VAR "n")))
`;

val FV_cchurch = Store_thm(
  "FV_cchurch",
  ``FV cchurch = {}``,
  SRW_TAC [][FV_EMPTY, cchurch_def]);

val fromTerm_funpow_app = store_thm(
  "fromTerm_funpow_app",
  ``fromTerm (FUNPOW ((@@) f) n x) = 
      FUNPOW (dAPP (fromTerm f)) n (fromTerm x)``,
  Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC]);

val lift_funpow_dAPP = store_thm(
  "lift_funpow_dAPP",
  ``lift (FUNPOW (dAPP f) n x) i = FUNPOW (dAPP (lift f i)) n (lift x i)``,
  Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC]);

val sub_funpow_dAPP = store_thm(
  "sub_funpow_dAPP",
  ``sub M v (FUNPOW (dAPP f) n x) = FUNPOW (dAPP (sub M v f)) n (sub M v x)``,
  Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC]);

val cchurch_behaviour = store_thm(
  "cchurch_behaviour",
  ``cchurch @@ church n -n->* cDB (fromTerm (church n))``,
  SIMP_TAC (bsrw_ss()) [cchurch_def, cichurch_behaviour] THEN 
  SIMP_TAC (bsrw_ss()) [church_def, cdABS_behaviour, fromTerm_funpow_app, 
                        dLAM_def, lift_funpow_dAPP, sub_funpow_dAPP] THEN 
  SIMP_TAC (srw_ss() ++ ARITH_ss) []);

val _ = temp_overload_on ("LAMvca", ``λM. LAM "v" (LAM "c" (LAM "a" M))``)

(* ----------------------------------------------------------------------
    cciDB : the encoded/computing version of ciDB 
   ---------------------------------------------------------------------- *)

val cciDB_def = Define`
  cciDB = LAM "t" 
           (VAR "t" 
             @@ (LAM "i" 
                  (cdAPP @@ (cdV @@ church (s2n "v")) @@ (cchurch @@ VAR "i")))
             @@ (LAM "r1" (LAM "r2"
                    (cdAPP 
                       @@ (cdAPP @@ (cdV @@ church (s2n "c")) @@ VAR "r1")
                       @@ VAR "r2")))
             @@ (LAM "r" 
                    (cdAPP @@ (cdV @@ church (s2n "a")) @@ VAR "r")))
`;

val FV_cciDB = Store_thm(
  "FV_cciDB",
  ``FV cciDB = {}``,
  SRW_TAC [][cciDB_def, FV_EMPTY]);

val cciDB_behaviour = store_thm(
  "cciDB_behaviour",
  ``cciDB @@ cDB dBt -n->* cDB (fromTerm (ciDB dBt))``,
  SIMP_TAC (bsrw_ss()) [cciDB_def, cDB_def] THEN 
  Q.MATCH_ABBREV_TAC 
    `[Abs/"a"] ([App/"c"] ([Var/"v"] (ciDB dBt))) -β->* result` THEN 
  Q.UNABBREV_TAC `result` THEN
  `∀v. v ∉ FV Abs ∧ v ∉ FV App ∧ v ∉ FV Var` 
     by SRW_TAC [][Abbr`App`, Abbr`Abs`, Abbr`Var`] THEN 
  Induct_on `dBt` THENL [
    ASM_SIMP_TAC (bsrw_ss()) [cDB_def, ciDB_def] THEN 
    ASM_SIMP_TAC (bsrw_ss()) [Abbr`Var`, cdV_behaviour, cchurch_behaviour, 
                              cdAPP_behaviour] THEN 
    SRW_TAC [][GSYM cDB_def, GSYM ciDB_def],

    ASM_SIMP_TAC (bsrw_ss()) [cDB_def, ciDB_def] THEN 
    ASM_SIMP_TAC (bsrw_ss()) [Abbr`App`, NOT_IN_FV_ciDB] THEN 
    SIMP_TAC (bsrw_ss()) [cdAPP_behaviour, cdV_behaviour, GSYM cDB_def, 
                          GSYM ciDB_def],

    ASM_SIMP_TAC (bsrw_ss()) [cDB_def, ciDB_def] THEN 
    ASM_SIMP_TAC (bsrw_ss()) [Abbr`Abs`] THEN 
    SIMP_TAC (bsrw_ss()) [GSYM ciDB_def, cdV_behaviour, GSYM cDB_def, 
                          cdAPP_behaviour]
  ]);

(* ----------------------------------------------------------------------
    ccDB : the encoded version of cDB 
   ---------------------------------------------------------------------- *)

val ccDB_def = Define`
  ccDB = LAM "t" (cdLAM @@ church (s2n "v") @@ 
                    (cdLAM @@ church (s2n "c") @@ 
                       (cdLAM @@ church (s2n "a") @@ (cciDB @@ VAR "t"))))
`;
val FV_ccDB = Store_thm(
  "FV_ccDB",
  ``FV ccDB = {}``,
  SRW_TAC [][FV_EMPTY, ccDB_def]);

val ccDB_behaviour = store_thm(
  "ccDB_behaviour",
  ``ccDB @@ (cDB dbt) -n->* cDB (fromTerm (cDB dbt))``,
  SIMP_TAC (bsrw_ss()) [ccDB_def, cciDB_behaviour, cdLAM_behaviour] THEN 
  Q.SPEC_THEN `dbt` ASSUME_TAC cDB_def THEN 
  SRW_TAC [][]);

open normal_orderTheory

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
  
    Will perhaps add a more traditional looking version with natural
    numbers too.
   ---------------------------------------------------------------------- *)

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

(* Impossibility of deciding whether or not an arbitrary term has a β-nf.
   Needs the computability of the encoding function cDB. *)
val HP_bnf = store_thm(
  "HP_bnf",
   ``¬∃M. ∀t. M @@ cDB (fromTerm t) -n->* cB (has_bnf t)``,
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
  METIS_TAC [HP_selfapp]);
  

val _ = export_theory()
