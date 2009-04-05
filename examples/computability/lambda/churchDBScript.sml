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

val NOT_IN_SUB = prove(
  ``x ∉ FV M ∧ (x ≠ v ⇒ x ∉ FV N) ⇒ x ∉ FV ([M/v]N)``,
  SRW_TAC [][termTheory.FV_SUB] THEN METIS_TAC []);

val cDB_thm = store_thm(
  "cDB_thm",
  ``cDB (dV i) @@ v @@ c @@ a == v @@ church i ∧
    cDB (dAPP M N) @@ v @@ c @@ a == c @@ (cDB M @@ v @@ c @@ a) 
                                       @@ (cDB N @@ v @@ c @@ a) ∧
    cDB (dABS M) @@ v @@ c @@ a == a @@ (cDB M @@ v @@ c @@ a)``,
  REPEAT CONJ_TAC THENL [
    SIMP_TAC (bsrw_ss()) [cDB_def] THEN FRESH_TAC THEN 
    SRW_TAC [][NOT_IN_FV_ciDB] THEN 
    ASM_SIMP_TAC (bsrw_ss()) [ciDB_def, tpm_fresh],

    SIMP_TAC (srw_ss()) [cDB_def, ciDB_def] THEN 
    Q_TAC (NEW_TAC "aa") `{"v"; "c"; "a"} ∪ FV v ∪ FV c ∪ FV a` THEN 
    `(LAM "a" (VAR "c" @@ ciDB M @@ ciDB N) = 
        LAM aa (VAR "c" @@ [VAR aa/"a"](ciDB M) @@ [VAR aa/"a"](ciDB N))) ∧
     (LAM "a" (ciDB M) = LAM aa ([VAR aa/"a"](ciDB M))) ∧
     (LAM "a" (ciDB N) = LAM aa ([VAR aa/"a"](ciDB N)))`
       by SRW_TAC [][LAM_eq_thm, NOT_IN_SUB, fresh_tpm_subst, 
                     lemma15b, NOT_IN_FV_ciDB] THEN 
    NTAC 3 (POP_ASSUM SUBST1_TAC) THEN 

    Q_TAC (NEW_TAC "cc") `{"v"; "c"; "a"; aa} ∪ FV v ∪ FV c ∪ FV a` THEN 
    `(LAM "c" (LAM aa (VAR "c" @@ [VAR aa/"a"](ciDB M) 
                               @@ [VAR aa/"a"](ciDB N))) = 
        LAM cc (LAM aa (VAR cc @@ [VAR cc/"c"]([VAR aa/"a"](ciDB M)) 
                               @@ [VAR cc/"c"]([VAR aa/"a"](ciDB N))))) ∧
     (LAM "c" (LAM aa ([VAR aa/"a"] (ciDB M))) = 
        LAM cc (LAM aa ([VAR cc/"c"]([VAR aa/"a"] (ciDB M))))) ∧
     (LAM "c" (LAM aa ([VAR aa/"a"] (ciDB N))) = 
        LAM cc (LAM aa ([VAR cc/"c"]([VAR aa/"a"] (ciDB N)))))`
       by SRW_TAC [][LAM_eq_thm, NOT_IN_SUB, fresh_tpm_subst, 
                     lemma15b, NOT_IN_FV_ciDB] THEN 
    NTAC 3 (POP_ASSUM SUBST1_TAC) THEN 
    ASM_SIMP_TAC (bsrw_ss()) [],

    SIMP_TAC (srw_ss()) [cDB_def, ciDB_def] THEN 
    Q_TAC (NEW_TAC "aa") `{"v"; "c"; "a"} ∪ FV v ∪ FV c ∪ FV a` THEN 
    `(LAM "a" (VAR "a" @@ ciDB M) = LAM aa (VAR aa @@ [VAR aa/"a"](ciDB M))) ∧
     (LAM "a" (ciDB M) = LAM aa ([VAR aa/"a"](ciDB M)))`
       by SRW_TAC [][LAM_eq_thm, NOT_IN_SUB, fresh_tpm_subst, 
                     lemma15b, NOT_IN_FV_ciDB] THEN 
    NTAC 2 (POP_ASSUM SUBST1_TAC) THEN 

    Q_TAC (NEW_TAC "cc") `{"v"; "c"; "a"; aa} ∪ FV v ∪ FV c ∪ FV a` THEN 
    `(LAM "c" (LAM aa (VAR aa @@ [VAR aa/"a"](ciDB M))) = 
        LAM cc (LAM aa (VAR aa @@ [VAR cc/"c"]([VAR aa/"a"](ciDB M))))) ∧
     (LAM "c" (LAM aa ([VAR aa/"a"](ciDB M))) = 
        LAM cc (LAM aa ([VAR cc/"c"]([VAR aa/"a"] (ciDB M)))))`
       by SRW_TAC [][LAM_eq_thm, NOT_IN_SUB, fresh_tpm_subst, 
                     lemma15b, NOT_IN_FV_ciDB] THEN 
    NTAC 2 (POP_ASSUM SUBST1_TAC) THEN 
    ASM_SIMP_TAC (bsrw_ss()) []
  ]);


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

val FV_cdFV = Store_thm(
  "FV_cdFV",
  ``FV cdFV = {}``,
  SRW_TAC [][cdFV_def, FV_EMPTY]); 
val cdFV_behaviour = store_thm(
  "cdFV_behaviour",
  ``∀i. cdFV @@ church i @@ cDB t -n->* cB (i ∈ dFV t)``,
  SIMP_TAC (bsrw_ss()) [cdFV_def] THEN 
  Induct_on `t` THEN 
  ASM_SIMP_TAC (bsrw_ss()) [cDB_thm, ceqnat_behaviour, 
                            cor_behaviour, csuc_behaviour, 
                            arithmeticTheory.ADD1] THEN
  SRW_TAC [][EQ_SYM_EQ]);

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
  Q.ID_SPEC_TAC `k` THEN Induct_on `M` THEN
  ASM_SIMP_TAC (bsrw_ss()) 
               [cDB_thm, cless_behaviour, cdV_behaviour, 
                csuc_behaviour, cdAPP_behaviour, cdABS_behaviour, 
                arithmeticTheory.ADD1] THEN 
  SRW_TAC [][] THEN 
  SIMP_TAC (bsrw_ss()) [cB_behaviour]);

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
  MAP_EVERY Q.ID_SPEC_TAC [`s`, `k`] THEN Induct_on `t` THEN 
  ASM_SIMP_TAC (bsrw_ss()) [cDB_thm, ceqnat_behaviour, cdV_behaviour, 
                            cdAPP_behaviour, cdABS_behaviour, 
                            csuc_behaviour, arithmeticTheory.ADD1, 
                            clift_behaviour] THEN
  SRW_TAC [][] THEN SIMP_TAC (bsrw_ss()) [cB_behaviour])

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
    term recursion operator, termrec
   ---------------------------------------------------------------------- *)

val B_I = store_thm(
  "B_I",
  ``v ∉ FV M ∧ v ∈ FV N ∧ N ≠ VAR v ⇒ 
      (LAM v (M @@ N) == B @@ M @@ (LAM v N))``,
  STRIP_TAC THEN 
  ASM_SIMP_TAC (bsrw_ss()) [chap2Theory.B_def] THEN 
  REWRITE_TAC [chap2Theory.S_def] THEN 
  Q_TAC (NEW_TAC "z") `{"x"; "y"; "z"} ∪ FV M ∪ FV N` THEN 
  `LAM "z" (VAR "x" @@ VAR "z" @@ (VAR "y" @@ VAR "z")) = 
   LAM z (VAR "x" @@ VAR z @@ (VAR "y" @@ VAR z))`
     by SRW_TAC [][LAM_eq_thm] THEN 
  POP_ASSUM SUBST1_TAC THEN 
  Q_TAC (NEW_TAC "y") `{"x"; "y"; z} ∪ FV M ∪ FV N` THEN 
  `LAM "y" (LAM z (VAR "x" @@ VAR z @@ (VAR "y" @@ VAR z))) =
   LAM y (LAM z (VAR "x" @@ VAR z @@ (VAR y @@ VAR z)))`
     by SRW_TAC [][LAM_eq_thm] THEN 
  POP_ASSUM SUBST1_TAC THEN 
  ASM_SIMP_TAC (bsrw_ss()) [] THEN 
  `∀x y. (x = y) ⇒ (x == y)` by SRW_TAC [][] THEN POP_ASSUM MATCH_MP_TAC THEN 
  SRW_TAC [boolSimps.CONJ_ss][LAM_eq_thm, tpm_fresh, NOT_IN_SUB] THEN 
  SRW_TAC [][GSYM fresh_tpm_subst, tpm_flip_args]);

val C_I = store_thm(
  "C_I",
  ``v ∈ FV M ∧ v ∉ FV N ⇒ LAM v (M @@ N) == C @@ (LAM v M) @@ N``,
  STRIP_TAC THEN ASM_SIMP_TAC (bsrw_ss()) [chap2Theory.C_def] THEN 
  REWRITE_TAC [chap2Theory.S_def] THEN 
  Q_TAC (NEW_TAC "z") `{"x"; "y"; "z"} ∪ FV M ∪ FV N` THEN 
  `LAM "z" (VAR "x" @@ VAR "z" @@ (VAR "y" @@ VAR "z")) = 
   LAM z (VAR "x" @@ VAR z @@ (VAR "y" @@ VAR z))`
     by SRW_TAC [][LAM_eq_thm] THEN 
  POP_ASSUM SUBST1_TAC THEN 
  Q_TAC (NEW_TAC "y") `{"x"; "y"; z} ∪ FV M ∪ FV N` THEN 
  `LAM "y" (LAM z (VAR "x" @@ VAR z @@ (VAR "y" @@ VAR z))) =
   LAM y (LAM z (VAR "x" @@ VAR z @@ (VAR y @@ VAR z)))`
     by SRW_TAC [][LAM_eq_thm] THEN 
  POP_ASSUM SUBST1_TAC THEN 
  ASM_SIMP_TAC (bsrw_ss()) [NOT_IN_SUB] THEN 
  `∀x y. (x = y) ⇒ (x == y)` by SRW_TAC [][] THEN POP_ASSUM MATCH_MP_TAC THEN 
  SRW_TAC [boolSimps.CONJ_ss][LAM_eq_thm, tpm_fresh, NOT_IN_SUB] THEN 
  SRW_TAC [][GSYM fresh_tpm_subst, tpm_flip_args]);

val I_I = store_thm(
  "I_I",
  ``LAM x (VAR x) = I``,
  SIMP_TAC (srw_ss()) [LAM_eq_thm, chap2Theory.I_def]);

val K_I = store_thm(
  "K_I", 
  ``v ∉ FV M ⇒ (LAM v M == K @@ M)``,
  STRIP_TAC THEN REWRITE_TAC [chap2Theory.K_def] THEN 
  Q_TAC (NEW_TAC "y") `{"x"; "y"} ∪ FV M` THEN 
  `LAM "y" (VAR "x") = LAM y (VAR "x")` by SRW_TAC [][LAM_eq_thm] THEN 
  POP_ASSUM SUBST1_TAC THEN 
  ASM_SIMP_TAC (bsrw_ss()) [] THEN 
  `∀x y. (x = y) ⇒ (x == y)` by SRW_TAC [][] THEN POP_ASSUM MATCH_MP_TAC THEN 
  SRW_TAC [boolSimps.CONJ_ss][LAM_eq_thm, tpm_fresh, NOT_IN_SUB]);

val S_I = store_thm(
  "S_I",
  ``v ∈ FV M ∧ v ∈ FV N ∧ N ≠ VAR v ⇒ 
    LAM v (M @@ N) == S @@ (LAM v M) @@ (LAM v N)``,
  STRIP_TAC THEN REWRITE_TAC [chap2Theory.S_def] THEN 
  Q_TAC (NEW_TAC "z") `{"x"; "y"; "z"} ∪ FV M ∪ FV N` THEN 
  `LAM "z" (VAR "x" @@ VAR "z" @@ (VAR "y" @@ VAR "z")) = 
   LAM z (VAR "x" @@ VAR z @@ (VAR "y" @@ VAR z))`
     by SRW_TAC [][LAM_eq_thm] THEN 
  POP_ASSUM SUBST1_TAC THEN 
  Q_TAC (NEW_TAC "y") `{"x"; "y"; z} ∪ FV M ∪ FV N` THEN 
  `LAM "y" (LAM z (VAR "x" @@ VAR z @@ (VAR "y" @@ VAR z))) =
   LAM y (LAM z (VAR "x" @@ VAR z @@ (VAR y @@ VAR z)))`
     by SRW_TAC [][LAM_eq_thm] THEN 
  POP_ASSUM SUBST1_TAC THEN 
  ASM_SIMP_TAC (bsrw_ss()) [NOT_IN_SUB] THEN 
  `LAM v (M @@ N) = LAM z ([VAR z/v] (M @@ N))`
     by SRW_TAC [][SIMPLE_ALPHA] THEN 
  SRW_TAC [][]);

val fake_eta = store_thm(
  "fake_eta",
  ``v ∉ FV M ∧ is_abs M ⇒ (LAM v (M @@ VAR v) == M)``,
  STRIP_TAC THEN 
  `∃u M0. M = LAM u M0`
     by (Q.SPEC_THEN `M` FULL_STRUCT_CASES_TAC term_CASES THEN 
         FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC []) THEN 
  ASM_SIMP_TAC (bsrw_ss()) [] THEN 
  FULL_SIMP_TAC (srw_ss()) [] THEN 
  Cases_on `v = u` THEN SRW_TAC [][] THEN RES_TAC THEN 
  `LAM u M0 = LAM v ([VAR v/u] M0)` by SRW_TAC [][SIMPLE_ALPHA] THEN 
  SRW_TAC [][]);


val B_eta = store_thm(
  "B_eta",
  ``LAM v (B @@ VAR v) == B``,
  SIMP_TAC (bsrw_ss()) [chap2Theory.B_def] THEN 
  `S @@ (K @@ S) @@ K =
   LAM "x" (LAM "y" (LAM "z" (VAR "x" @@ VAR "z" @@ (VAR "y" @@ VAR "z")))) @@ 
       (K @@ S) @@ K`
     by SRW_TAC [][chap2Theory.S_def] THEN 
  ASM_SIMP_TAC (bsrw_ss()) [] THEN 
  `∀x y. (x = y) ⇒ x == y` by SRW_TAC [][] THEN 
  POP_ASSUM MATCH_MP_TAC THEN 
  SRW_TAC [][LAM_eq_thm, tpm_fresh]);

val eqn_elim = prove(
  ``(∀Y. X:term == Y ⇔ Z == Y) ⇒ X == Z``,
  METIS_TAC [chap2Theory.lam_eq_rules]);
fun brackabs_equiv ths def = let 
  val (l,r) = dest_eq (concl def)
  val gv = genvar ``:term``
  val t = ``^l == ^gv``
  val th = SIMP_CONV (bsrw_ss()) 
                     ([S_I, K_I, B_I, C_I, fake_eta, B_eta, I_I, def] @ ths)
                     t
in
  MATCH_MP eqn_elim (GEN gv th) 
end
  
val is_abs_cdV = Store_thm(
  "is_abs_cdV",
  ``is_abs cdV``,
  SRW_TAC [][cdV_def]);
val is_abs_cdAPP = Store_thm(
  "is_abs_cdAPP",
  ``is_abs cdAPP``,
  SRW_TAC [][cdAPP_def]);

val termrec_var_def = Define`
  termrec_var = S @@ (B @@ cpair @@ cdV)
                (* λv i. cpair (dV i) (v i) *)
`;
val termrec_var_eta = store_thm(
  "termrec_var_eta",
  ``LAM x (termrec_var @@ VAR x) == termrec_var``,
  SIMP_TAC (bsrw_ss()) [termrec_var_def] THEN 
  REWRITE_TAC [chap2Theory.S_def] THEN 
  SIMP_TAC (bsrw_ss()) [] THEN 
  `∀x y. (x = y) ⇒ x == y` by SRW_TAC [][] THEN 
  POP_ASSUM MATCH_MP_TAC THEN 
  SRW_TAC [boolSimps.CONJ_ss][LAM_eq_thm, tpm_fresh] THEN 
  Cases_on `x = "z"` THEN SRW_TAC [][lemma14b] THEN 
  SRW_TAC [][GSYM fresh_tpm_subst, tpm_fresh]);
  

val termrec_comb_def = Define`
  termrec_comb = 
  LAM "c" (LAM "r1" (LAM "r2" 
    (cpair @@ (cdAPP @@ (cfst @@ VAR "r1") @@ (cfst @@ VAR "r2"))
           @@ (VAR "c" 
                   @@ (cfst @@ VAR "r1") @@ (cfst @@ VAR "r2")
                   @@ (csnd @@ VAR "r1") @@ (csnd @@ VAR "r2")))))
`;
val termrec_comb_eqn = brackabs_equiv [] termrec_comb_def


val termrec_abs_def = Define`
  termrec_abs = 
  LAM "a" (LAM "r" 
    (cpair @@ (cdABS @@ (cfst @@ VAR "r"))
           @@ (VAR "a" @@ (cfst @@ VAR "r") @@ (csnd @@ VAR "r"))))
`;
val termrec_abs_eqn = brackabs_equiv [] termrec_abs_def

val FV_termrec_subs = Store_thm(
  "FV_termrec_subs",
  ``(FV termrec_var = {}) ∧ (FV termrec_comb = {}) ∧ (FV termrec_abs = {})``,
  SRW_TAC [][termrec_var_def, termrec_comb_def, termrec_abs_def, EXTENSION]);

val is_abs_termrecsubs = Store_thm(
  "is_abs_termrecsubs",
  ``is_abs termrec_comb ∧ is_abs termrec_abs``,
  SRW_TAC [][termrec_var_def, termrec_comb_def, termrec_abs_def]);

val fst_termrec_subs = store_thm(
  "fst_termrec_subs",
  ``∀t. cfst @@ (cDB t 
                     @@ (termrec_var @@ v) 
                     @@ (termrec_comb @@ c)
                     @@ (termrec_abs @@ a)) == 
        cDB t``,
  SIMP_TAC (bsrw_ss()) [termrec_var_def, termrec_comb_eqn, termrec_abs_eqn] THEN
  Induct THEN ASM_SIMP_TAC (bsrw_ss()) [cDB_thm, 
                                        churchpairTheory.cfst_pair, 
                                        cdV_behaviour, cdAPP_behaviour, 
                                        cdABS_behaviour]);

val termrec_def = Define`
  termrec = 
  LAM "v" (LAM "c" (LAM "a" (LAM "t"
    (csnd @@ (VAR "t" 
                  @@ (termrec_var @@ VAR "v")
                  @@ (termrec_comb @@ VAR "c")
                  @@ (termrec_abs @@ VAR "a"))))))
`;

val termrec_eqn = brackabs_equiv [termrec_var_eta] termrec_def

val FV_termrec = Store_thm(
  "FV_termrec",
  ``FV termrec = {}``,
  SRW_TAC [][termrec_def, EXTENSION]);

infix |> fun x |> f = f x

val termrec_behaviour = store_thm(
  "termrec_behaviour",
  ``termrec @@ v @@ c @@ a @@ cDB (dV i) == v @@ church i ∧
    termrec @@ v @@ c @@ a @@ cDB (dAPP t u) ==
      c @@ cDB t @@ cDB u 
        @@ (termrec @@ v @@ c @@ a @@ cDB t)
        @@ (termrec @@ v @@ c @@ a @@ cDB u) ∧
    termrec @@ v @@ c @@ a @@ cDB (dABS t) ==
      a @@ cDB t @@ (termrec @@ v @@ c @@ a @@ cDB t)``,
  REPEAT CONJ_TAC THENL [
    SIMP_TAC (bsrw_ss()) [termrec_eqn, cDB_thm, termrec_var_def, 
                          churchpairTheory.csnd_pair],

    SIMP_TAC (bsrw_ss()) [termrec_eqn, cDB_thm] THEN 
    ASSUME_TAC (``termrec_comb @@ c @@ x @@ y == X`` 
                  |> SIMP_CONV (bsrw_ss()) [termrec_comb_eqn]
                  |> Q.GEN `X`
                  |> MATCH_MP eqn_elim 
                  |> Q.GEN `y` |> Q.GEN `x`) THEN 
    ASM_SIMP_TAC (bsrw_ss()) [churchpairTheory.csnd_pair, fst_termrec_subs],
    
    SIMP_TAC (bsrw_ss()) [termrec_eqn, cDB_thm] THEN 
    ASSUME_TAC (``termrec_abs @@ a @@ x == X`` 
                  |> SIMP_CONV (bsrw_ss()) [termrec_abs_eqn]
                  |> Q.GEN `X`
                  |> MATCH_MP eqn_elim 
                  |> Q.GEN `x`) THEN 
    ASM_SIMP_TAC (bsrw_ss()) [churchpairTheory.csnd_pair, fst_termrec_subs]
  ]);

(* ---------------------------------------------------------------------- 
    cis_abs - is a term an abstraction?
   ---------------------------------------------------------------------- *)

val cis_abs_def = Define`
  cis_abs = 
  LAM "t" (VAR "t" @@ (K @@ cB F) @@ (K @@ (K @@ cB F)) @@ (K @@ cB T))
`;

val FV_cis_abs = Store_thm(
  "FV_cis_abs",
  ``FV cis_abs = {}``,
  SRW_TAC [][cis_abs_def])

val FV_toTerm = Store_thm(
  "FV_toTerm",
  ``FV (toTerm d) = dFVs d``,
  SIMP_TAC bool_ss [GSYM dFVs_fromTerm, fromtoTerm]);
val is_abs_cis_abs = Store_thm(
  "is_abs_cis_abs",
  ``is_abs cis_abs``,
  SRW_TAC [][cis_abs_def]);

val cis_abs_behaviour = store_thm(
  "cis_abs_behaviour",
  ``cis_abs @@ cDB t -n->* cB (is_dABS t)``,
  SIMP_TAC (bsrw_ss()) [cis_abs_def] THEN Cases_on `t` THEN 
  SIMP_TAC (bsrw_ss()) [cDB_thm]); 

(* ----------------------------------------------------------------------
    cbnf - is a term in β-nf?
   ---------------------------------------------------------------------- *)

val cbnf_def = Define`
  cbnf = 
  termrec @@ (LAM "i" (cB T))
          @@ (LAM "t1" (LAM "t2" (LAM "r1" (LAM "r2"
                (cand @@ VAR "r1"
                      @@ (cand @@ VAR "r2"
                               @@ (cnot @@ (cis_abs @@ VAR "t1"))))))))
          @@ (LAM "t" (LAM "r" (VAR "r")))
`;

val FV_cbnf = Store_thm(
  "FV_cbnf",
  ``FV cbnf = {}``,
  SRW_TAC [][cbnf_def, EXTENSION]); 

val cbnf_equiv = brackabs_equiv [] cbnf_def
val cbnf_behaviour = store_thm(
  "cbnf_behaviour",
  ``cbnf @@ cDB t -n->* cB (dbnf t)``,
  SIMP_TAC (bsrw_ss()) [cbnf_equiv] THEN 
  Induct_on `t` THEN 
  ASM_SIMP_TAC (bsrw_ss()) [termrec_behaviour, cand_behaviour, 
                            cis_abs_behaviour, cnot_behaviour]);
  
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
  SIMP_TAC (bsrw_ss()) [cichurch_def, cdV_behaviour] THEN 
  Induct_on `n` THEN
  ASM_SIMP_TAC (bsrw_ss()) [church_thm, cdV_behaviour, cdAPP_behaviour,
                            FUNPOW_SUC]);

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
  SIMP_TAC (bsrw_ss()) [cciDB_def, cdV_behaviour] THEN 
  Induct_on `dBt` THEN
  ASM_SIMP_TAC (bsrw_ss()) [cDB_thm, cdV_behaviour, cchurch_behaviour, 
                            cdAPP_behaviour] THEN 
  ASM_SIMP_TAC (bsrw_ss()) [ciDB_def]);

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

(* ---------------------------------------------------------------------- 
    enumerations are computable 
   ---------------------------------------------------------------------- *)

open enumerationsTheory




val cdBnum_def = Define`
  cdBnum = 
  LAM "t" 
    (VAR "t" 
         @@ (cmult @@ church 3)
         @@ (LAM "r1" 
               (B @@ csuc 
                  @@ (B @@ (cmult @@ church 3) 
                        @@ (cnpair @@ VAR "r1"))))
         @@ (B @@ (cplus @@ church 2) @@ (cmult @@ church 3)))
`;

val FV_cdBnum = Store_thm(
  "FV_cdBnum",
  ``FV cdBnum = {}``,
  SRW_TAC [][cdBnum_def]);

val cdBnum_behaviour = store_thm(
  "cdBnum_behaviour",
  ``cdBnum @@ cDB t -n->* church (dBnum t)``,
  SIMP_TAC (bsrw_ss()) [cdBnum_def] THEN Induct_on `t` THEN 
  ASM_SIMP_TAC (bsrw_ss() ++ ARITH_ss) 
               [cDB_thm, dBnum_def, cmult_behaviour, 
                cnpair_behaviour, csuc_behaviour, 
                arithmeticTheory.ADD1, cplus_behaviour]);

val cndbsuc_def = Define`
  cndbsuc = 
  LAM "r" (LAM "n" (LAM "m3" (LAM "d3"
             (cis_zero @@ VAR "m3"
              @@ (cdV @@ VAR "d3")
              @@ (ceqnat @@ VAR "m3" @@ (church 1)
                         @@ (cdAPP @@ (VAR "r" @@ (cnfst @@ VAR "d3"))
                                   @@ (VAR "r" @@ (cnsnd @@ VAR "d3")))
                         @@ (cdABS @@ (VAR "r" @@ VAR "d3")))))
            @@ (cmod @@ VAR "n" @@ church 3)
            @@ (cdiv @@ VAR "n" @@ church 3)))
`;
val FV_cndbsuc = Store_thm(
  "FV_cndbsuc",
  ``FV cndbsuc = {}``,
  SRW_TAC [][cndbsuc_def, EXTENSION]);

val cndbsuc_dV_behaviour = store_thm(
  "cndbsuc_dV_behaviour",
  ``(n MOD 3 = 0) ⇒ 
    cndbsuc @@ r @@ church n -n->* cDB (dV (n DIV 3))``,
  SIMP_TAC (bsrw_ss()) [cndbsuc_def] THEN FRESH_TAC THEN 
  ASM_SIMP_TAC (bsrw_ss()) [tpm_fresh, cmod_behaviour, cis_zero_behaviour, 
                            cB_behaviour, cdiv_behaviour, cdV_behaviour]);


val is_abs_cmoddiv = Store_thm(
  "is_abs_cmoddiv",
  ``is_abs cmod ∧ is_abs cdiv``,
  SRW_TAC [][cmod_def, cdiv_def]);

val cndbsuc_eqn = brackabs_equiv [] cndbsuc_def

val cndbsuc_dAPP_behaviour = store_thm(
  "cndbsuc_dAPP_behaviour",
  ``(n MOD 3 ≠ 0) ∧ (n MOD 3 = 1) ⇒ 
    cndbsuc @@ r @@ church n == 
    cdAPP @@ (r @@ (cnfst @@ church (n DIV 3))) 
          @@ (r @@ (cnsnd @@ church (n DIV 3)))``,
  STRIP_TAC THEN 
  ASM_SIMP_TAC (bsrw_ss()) [cndbsuc_eqn, cmod_behaviour, cis_zero_behaviour, 
                            ceqnat_behaviour, cB_behaviour, cdiv_behaviour]);

val cndbsuc_dABS_behaviour = store_thm(
  "cndbsuc_dABS_behaviour",
  ``(n MOD 3 ≠ 0) ∧ (n MOD 3 ≠ 1) ⇒
    cndbsuc @@ r @@ church n == cdABS @@ (r @@ church (n DIV 3))``,
  STRIP_TAC THEN 
  ASM_SIMP_TAC (bsrw_ss()) [cndbsuc_eqn, cmod_behaviour, cis_zero_behaviour, 
                            ceqnat_behaviour, cB_behaviour, cdiv_behaviour]);
 
val cnumdB0_def = Define`
  cnumdB0 = 
  natrec 
   @@ (LAM "n" (cDB (dV 0)))
   @@ (LAM "c0" (LAM "r" (LAM "n"
       (ceqnat @@ (csuc @@ VAR "c0") @@ (VAR "n")
        @@ (cndbsuc @@ VAR "r" @@ VAR "n")
        @@ (VAR "r" @@ VAR "n")))))
`;
        
val FV_cnumdB0 = Store_thm(
  "FV_cnumdB0",
  ``FV cnumdB0 = {}``,
  SRW_TAC [][cnumdB0_def, EXTENSION])

val cnumdB0_behaviour = store_thm(
  "cnumdB0_behaviour",
  ``n ≤ c ⇒ cnumdB0 @@ church c @@ church n -n->* cDB (numdB n)``,
  Q.ID_SPEC_TAC `n` THEN SIMP_TAC (bsrw_ss()) [cnumdB0_def] THEN 
  Induct_on `c` THEN
  SIMP_TAC (bsrw_ss()) [natrec_behaviour, cdV_behaviour, 
                        csuc_behaviour, cmod_behaviour, cdiv_behaviour, 
                        ceqnat_behaviour] 
  THEN1 SRW_TAC [][Once numdB_def] THEN 
  REPEAT STRIP_TAC THEN Q.ABBREV_TAC `N = SUC c` THEN 
  Cases_on `n = N` THENL [
    SRW_TAC [][] THEN 
    ASM_SIMP_TAC (bsrw_ss()) [cB_behaviour] THEN 
    Cases_on `N MOD 3 = 0` THENL [
      ASM_SIMP_TAC (bsrw_ss()) [cndbsuc_dV_behaviour] THEN 
      ASM_SIMP_TAC (srw_ss()) [Once numdB_def],

      `0 < N` by SRW_TAC [][Abbr`N`] THEN 
      `N DIV 3 < N` 
        by SRW_TAC [ARITH_ss][arithmeticTheory.DIV_LESS] THEN 
      `N DIV 3 ≤ c` by SRW_TAC [ARITH_ss][Abbr`N`] THEN 
      Cases_on `N MOD 3 = 1` THENL [
        ASM_SIMP_TAC (bsrw_ss()) [cndbsuc_dAPP_behaviour, Once numdB_def] THEN 
        `nsnd (N DIV 3) ≤ c ∧ nfst (N DIV 3) ≤ c`
           by (ASSUME_TAC (Q.INST [`n` |-> `N DIV 3`] 
                                  numpairTheory.nsnd_le) THEN
               ASSUME_TAC (Q.INST [`n` |-> `N DIV 3`] 
                                  numpairTheory.nfst_le) THEN
               DECIDE_TAC) THEN 
        ASM_SIMP_TAC (bsrw_ss()) [cnfst_behaviour, cnsnd_behaviour, 
                                  cdAPP_behaviour],

        ASM_SIMP_TAC (bsrw_ss()) [cndbsuc_dABS_behaviour, Once numdB_def, 
                                  cdABS_behaviour]
      ]
    ],

    ASM_SIMP_TAC (bsrw_ss()) [cB_behaviour] THEN 
    `n ≤ c` by SRW_TAC [ARITH_ss][Abbr`N`] THEN 
    ASM_SIMP_TAC (bsrw_ss()) []
  ]);

val cnumdB_def = Define`
  cnumdB = LAM "n" (cnumdB0 @@ VAR "n" @@ VAR "n")
`; 

val FV_cnumdB = Store_thm(
  "FV_cnumdB",
  ``FV cnumdB = {}``,
  SRW_TAC [][cnumdB_def]);

val cnumdB_behaviour = store_thm(
  "cnumdB_behaviour",
  ``cnumdB @@ church n -n->* cDB (numdB n)``,
  SIMP_TAC (bsrw_ss()) [cnumdB_def, cnumdB0_behaviour]);
  
val _ = export_theory()
