(* Church style encoding of de Bruijn terms, giving us
    "The Power of Reflection"
*)

open HolKernel boolLib bossLib Parse binderLib

open churchnumTheory churchboolTheory pure_dBTheory
open reductionEval pred_setTheory termTheory chap3Theory
open normal_orderTheory
open head_reductionTheory
open brackabs

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
val cdFV_behaviour = bstore_thm(
  "cdFV_behaviour",
  ``∀i. cdFV @@ church i @@ cDB t -n->* cB (i ∈ dFV t)``,
  SIMP_TAC (bsrw_ss()) [cdFV_def] THEN
  Induct_on `t` THEN
  ASM_SIMP_TAC (bsrw_ss()) [cDB_thm, arithmeticTheory.ADD1] THEN
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
val cdV_behaviour = bstore_thm(
  "cdV_behaviour",
  ``cdV @@ church n -w->* cDB (dV n)``,
  SIMP_TAC (whfy (srw_ss())) [cdV_def, cDB_def, ciDB_def]);

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
val is_abs_cdAPP = Store_thm(
  "is_abs_cdAPP",
  ``is_abs cdAPP``,
  SRW_TAC [][cdAPP_def]);

val cdAPP_behaviour = bstore_thm(
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
val is_abs_cdABS = Store_thm(
  "is_abs_cdABS",
  ``is_abs cdABS``,
  SRW_TAC [][cdABS_def])
val cdABS_behaviour = bstore_thm(
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
val is_abs_clift = Store_thm(
  "is_abs_clift",
  ``is_abs clift``,
  SRW_TAC [][clift_def]);

val clift_behaviour = bstore_thm(
  "clift_behaviour",
  ``clift @@ cDB M @@ church k -n->* cDB (lift M k)``,
  SIMP_TAC (bsrw_ss()) [clift_def] THEN
  Q.ID_SPEC_TAC `k` THEN Induct_on `M` THEN
  ASM_SIMP_TAC (bsrw_ss()) [cDB_thm, arithmeticTheory.ADD1] THEN
  SRW_TAC [][] THEN SIMP_TAC (bsrw_ss()) []);

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

val csub_behaviour = bstore_thm(
  "csub_behaviour",
  ``csub @@ cDB s @@ church k @@ cDB t -n->* cDB (sub s k t)``,
  SIMP_TAC (bsrw_ss()) [csub_def] THEN
  MAP_EVERY Q.ID_SPEC_TAC [`s`, `k`] THEN Induct_on `t` THEN
  ASM_SIMP_TAC (bsrw_ss()) [cDB_thm, arithmeticTheory.ADD1] THEN
  SRW_TAC [][] THEN SIMP_TAC (bsrw_ss()) [])

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

val cdLAM_behaviour = bstore_thm(
  "cdLAM_behaviour",
  ``cdLAM @@ church i @@ cDB t -n->* cDB (dLAM i t)``,
  SIMP_TAC (bsrw_ss()) [cdLAM_def, dLAM_def]);

(* ----------------------------------------------------------------------
    term recursion operator, termrec
   ---------------------------------------------------------------------- *)


val is_abs_cdV = Store_thm(
  "is_abs_cdV",
  ``is_abs cdV``,
  SRW_TAC [][cdV_def]);

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

val eqn_elim = prove(
  ``(!Y. (X:term == Y) = (Z == Y)) ==> X == Z``,
  STRIP_TAC THEN POP_ASSUM (Q.SPEC_THEN `Z` MP_TAC) THEN
  REWRITE_TAC [chap2Theory.lameq_refl]);


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

val RTC1 = relationTheory.RTC_RULES |> SPEC_ALL |> CONJUNCT2 |> GEN_ALL

val wh_cis_abs = store_thm(
  "wh_cis_abs",
  ``cis_abs @@ cDB t -w->* cB (is_dABS t)``,
  SIMP_TAC (whfy (srw_ss())) [cis_abs_def, bnf_whnf] THEN
  Cases_on `t` THEN
  SIMP_TAC (whfy (srw_ss())) [cDB_def, bnf_whnf, ciDB_def] THEN
  SIMP_TAC (whfy (srw_ss())) [chap2Theory.K_def, bnf_whnf]);


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

val wh_S = store_thm(
  "wh_S",
  ``S @@ f @@ g @@ x -w->* f @@ x @@ (g @@ x)``,
  REWRITE_TAC [chap2Theory.S_def] THEN unvarify_tac whstar_substitutive THEN
  ASM_SIMP_TAC (whfy (srw_ss())) []);

val wh_K = store_thm(
  "wh_K",
  ``K @@ x @@ y -w->* x``,
  REWRITE_TAC [chap2Theory.K_def] THEN unvarify_tac whstar_substitutive THEN
  ASM_SIMP_TAC (whfy (srw_ss())) []);

val wh_B = store_thm(
  "wh_B",
  ``B @@ f @@ g @@ x -w->* f @@ (g @@ x)``,
  unvarify_tac whstar_substitutive THEN
  SIMP_TAC (whfy(srw_ss())) [chap2Theory.B_def, wh_S, wh_K]);

val wh_cdV = store_thm(
  "wh_cdV",
  ``cdV @@ x @@ v @@ c @@ a -w->* v @@ x``,
  unvarify_tac whstar_substitutive THEN REWRITE_TAC [cdV_def] THEN
  FRESH_TAC THEN ASM_SIMP_TAC (whfy(srw_ss())) []);

val wh_cdAPP = store_thm(
  "wh_cdAPP",
  ``cdAPP @@ t1 @@ t2 @@ v @@ c @@ a -w->*
    c @@ (t1 @@ v @@ c @@ a) @@ (t2 @@ v @@ c @@ a)``,
  REWRITE_TAC [cdAPP_def] THEN unvarify_tac whstar_substitutive THEN
  ASM_SIMP_TAC (whfy(srw_ss())) []);

val wh_cdABS = store_thm(
  "wh_cdABS",
  ``cdABS @@ t @@ v @@ c @@ a -w->* a @@ (t @@ v @@ c @@ a)``,
  REWRITE_TAC [cdABS_def] THEN unvarify_tac whstar_substitutive THEN
  ASM_SIMP_TAC (whfy(srw_ss())) []);



open churchpairTheory

val wh_termrec_comb = store_thm(
  "wh_termrec_comb",
  ``termrec_comb @@ t @@ r1 @@ r2 @@ f -w->*
    f @@ (cdAPP @@ (cfst @@ r1) @@ (cfst @@ r2))
      @@ (t @@ (cfst @@ r1) @@ (cfst @@ r2)
            @@ (csnd @@ r1) @@ (csnd @@ r2))``,
  unvarify_tac whstar_substitutive THEN
  REWRITE_TAC [termrec_comb_def] THEN FRESH_TAC THEN
  ASM_SIMP_TAC (whfy (srw_ss())) [tpm_fresh, wh_cpair]);

val wh_termrec_abs = store_thm(
  "wh_termrec_abs",
  ``termrec_abs @@ t @@ r @@ f -w->*
    f @@ (cdABS @@ (cfst @@ r)) @@ (t @@ (cfst @@ r) @@ (csnd @@ r))``,
  REWRITE_TAC [termrec_abs_def] THEN unvarify_tac whstar_substitutive THEN
  ASM_SIMP_TAC (whfy(srw_ss())) [wh_cpair]);

val wh_cbnf = store_thm(
  "wh_cbnf",
  ``(FV M = {}) ∧ M -n->* cDB t ⇒ cbnf @@ M -w->* cB (dbnf t)``,
  SIMP_TAC (whfy (srw_ss())) [cbnf_def, termrec_def, cDB_def, csnd_def] THEN
  STRIP_TAC THEN
  Q.MATCH_ABBREV_TAC
     `M @@ VV @@ (termrec_comb @@ CC) @@ AA @@ cB F -w->* cB (dbnf t)` THEN
  `(FV AA = {}) ∧ (FV CC = {}) ∧ (FV VV = {})`
     by SRW_TAC [][Abbr`AA`, Abbr`VV`, Abbr`CC`, EXTENSION] THEN
  `"v" ∉ FV M` by SRW_TAC [][] THEN
  `∃vM. M -w->* LAM "v" vM ∧ vM -n->* LAM "c" (LAM "a" (ciDB t))`
    by METIS_TAC [normstar_to_abs_wstar] THEN
  ASM_SIMP_TAC (whfy (srw_ss())) [] THEN
  `"c" ∉ FV vM`
    by (STRIP_TAC THEN
        `"c" ∈ FV (LAM "v" vM)` by SRW_TAC [][] THEN
        `"c" ∈ FV M` by METIS_TAC [whstar_FV] THEN
        POP_ASSUM MP_TAC THEN SRW_TAC [][]) THEN
  `∃vcM. vM -w->* LAM "c" vcM ∧ vcM -n->* LAM "a" (ciDB t)`
    by METIS_TAC [normstar_to_abs_wstar] THEN
  ASM_SIMP_TAC (whfy (srw_ss())) [] THEN
  `"a" ∉ FV vcM`
    by (STRIP_TAC THEN
        `"a" ∈ FV (LAM "c" vcM)` by SRW_TAC [][] THEN
        `"a" ∈ FV vM` by METIS_TAC [whstar_FV] THEN
        `"a" ∈ FV (LAM "v" vM)` by SRW_TAC [][] THEN
        `"a" ∈ FV M` by METIS_TAC  [whstar_FV] THEN
        POP_ASSUM MP_TAC THEN SRW_TAC [][]) THEN
  `∃vcaM. vcM -w->* LAM "a" vcaM ∧ vcaM -n->* ciDB t`
    by METIS_TAC [normstar_to_abs_wstar] THEN
  ASM_SIMP_TAC (whfy (srw_ss())) [] THEN
  POP_ASSUM MP_TAC THEN NTAC 8 (POP_ASSUM (K ALL_TAC)) THEN
  REPEAT (FIRST_X_ASSUM (fn th => if mem ``M:term`` (free_vars (concl th)) then
                                    ALL_TAC
                                  else NO_TAC)) THEN
  Q_TAC SUFF_TAC
    `∀t M.
       M -n->* ciDB t ⇒
       [AA/"a"] ([termrec_comb @@ CC/"c"] ([VV/"v"] M)) @@ cB F -w->*
         cB (dbnf t) ∧
       [AA/"a"] ([termrec_comb @@ CC/"c"] ([VV/"v"] M)) @@ cB T
           @@ (K @@ cB F) @@ (K @@ (K @@ cB F)) @@ (K @@ cB T) -w->*
         cB (is_dABS t)`
    THEN1 METIS_TAC [] THEN
  Induct_on `t` THENL [
    REPEAT GEN_TAC THEN SIMP_TAC (srw_ss()) [ciDB_def] THEN STRIP_TAC THEN
    `∃M'. M -w->* VAR "v" @@ M' ∧ M' -n->* church n`
      by METIS_TAC [normstar_to_vheadunary_wstar] THEN
    ASM_SIMP_TAC (whfy (srw_ss())) [] THEN
    Q.UNABBREV_TAC `VV` THEN
    SIMP_TAC (whfy (srw_ss())) [termrec_var_def, wh_S, wh_B, wh_cpair,
                                wh_cB, wh_cdV, wh_K],

    ASM_SIMP_TAC (srw_ss()) [ciDB_def] THEN GEN_TAC THEN STRIP_TAC THEN
    `∃M₁ M₂. M -w->* VAR "c" @@ M₁ @@ M₂ ∧ M₁ -n->* ciDB t ∧
             M₂ -n->* ciDB t'` by METIS_TAC [normstar_to_vheadbinary_wstar] THEN
    ASM_SIMP_TAC (whfy(srw_ss())) [] THEN
    `∀t1 t2 r1 r2.
       CC @@ t1 @@ t2 @@ r1 @@ r2 -w->*
       r1 @@ (cand @@ r2 @@ (cnot @@ (cis_abs @@ t1))) @@ cB F`
       by (Q.UNABBREV_TAC `CC` THEN REPEAT (POP_ASSUM (K ALL_TAC)) THEN
           REPEAT STRIP_TAC THEN unvarify_tac whstar_substitutive THEN
           ASM_SIMP_TAC (whfy (srw_ss())) [wh_cand]) THEN
    ASM_SIMP_TAC (whfy (srw_ss())) [wh_termrec_comb, wh_cB, csnd_def,
                                    wh_cdAPP, wh_K] THEN
    Cases_on `dbnf t` THEN ASM_SIMP_TAC (whfy (srw_ss())) [wh_cB, wh_cand] THEN
    Cases_on `dbnf t'` THEN ASM_SIMP_TAC (whfy (srw_ss())) [wh_cB] THEN
    ASM_SIMP_TAC (whfy (srw_ss())) [cnot_def, cis_abs_def, cfst_def] THEN
    Cases_on `is_dABS t` THEN ASM_SIMP_TAC (whfy (srw_ss())) [wh_cB],

    ASM_SIMP_TAC (srw_ss()) [ciDB_def] THEN GEN_TAC THEN STRIP_TAC THEN
    `∃M0. M -w->* VAR "a" @@ M0 ∧ M0 -n->* ciDB t`
      by METIS_TAC [normstar_to_vheadunary_wstar] THEN
    ASM_SIMP_TAC (whfy(srw_ss())) [] THEN
    `∀t f. AA @@ t @@ f -w->*
           f @@ (cdABS @@ (cfst @@ t))
             @@ ((LAM "t" (LAM "r" (VAR "r"))) @@ (cfst @@ t) @@ (csnd @@ t))`
       by ASM_SIMP_TAC (whfy(srw_ss())) [Abbr`AA`, wh_termrec_abs] THEN
    ASM_SIMP_TAC (whfy(srw_ss())) [wh_cB, csnd_def, wh_cdABS, wh_K]
  ]);


(* ----------------------------------------------------------------------
    cnsub - the computable version of nsub, which has defining equations
       (nsub s k (dV i) = if k < i then dV (i - 1)
                          else if i = k then s else dV i) /\
       (nsub s k (dAPP t u) = dAPP (nsub s k t) (nsub s k u)) /\
       (nsub s k (dABS t) = dABS (nsub (lift s 0) (k + 1) t))
   ---------------------------------------------------------------------- *)

val cnsub_def = Define`
  cnsub =
  LAM "s" (LAM "k" (LAM "t"
   (VAR "t"
        @@ (LAM "i" (LAM "s" (LAM "k"
              (cless @@ VAR "k" @@ VAR "i"  (* if k < i *)
                     @@ (cdV @@ (cminus @@ VAR "i" @@ church 1)) (* then *)
                     @@ (ceqnat @@ VAR "i" @@ VAR "k" (* if i = k *)
                                @@ VAR "s"
                                @@ (cdV @@ VAR "i"))))))
        @@ (LAM "r1" (LAM "r2" (LAM "s" (LAM "k"
              (cdAPP @@ (VAR "r1" @@ VAR "s" @@ VAR "k")
                     @@ (VAR "r2" @@ VAR "s" @@ VAR "k"))))))
        @@ (LAM "r" (LAM "s" (LAM "k"
              (cdABS @@ (VAR "r"
                             @@ (clift @@ VAR "s" @@ church 0)
                             @@ (cplus @@ VAR "k" @@ church 1))))))
        @@ VAR "s" @@ VAR "k")))
`;

val FV_cnsub = Store_thm(
  "FV_cnsub",
  ``FV cnsub = {}``,
  SRW_TAC [][cnsub_def, EXTENSION]);
val is_abs_cnsub = Store_thm(
  "is_abs_cnsub",
  ``is_abs cnsub``,
  SRW_TAC [][cnsub_def]);

val Ccless_eta = prove(
  ``LAM x (C @@ cless @@ VAR x) == C @@ cless``,
  SIMP_TAC (bsrw_ss()) [chap2Theory.C_def] THEN
  SIMP_TAC (bsrw_ss()) [chap2Theory.B_def] THEN
  CONV_TAC (RAND_CONV (SIMP_CONV (bsrw_ss()) [Once chap2Theory.S_def])) THEN
  SIMP_TAC (bsrw_ss()) [] THEN
  `∀x y. (x = y) ⇒ (x == y)` by SRW_TAC [][] THEN
  POP_ASSUM MATCH_MP_TAC THEN
  SRW_TAC [][LAM_eq_thm, tpm_fresh]);

val cnsub_equiv = brackabs_equiv [Ccless_eta] cnsub_def

val cnsub_behaviour = store_thm(
  "cnsub_behaviour",
  ``∀u i t. cnsub @@ cDB t @@ church i @@ cDB u -n->* cDB (nsub t i u)``,
  SIMP_TAC (bsrw_ss()) [cnsub_equiv] THEN
  Induct THEN
  ASM_SIMP_TAC (bsrw_ss()) [cDB_thm, cminus_behaviour, cdV_behaviour,
                            cless_behaviour, ceqnat_behaviour,
                            cdAPP_behaviour, clift_behaviour,
                            cplus_behaviour, cdABS_behaviour] THEN
  SRW_TAC [][] THEN ASM_SIMP_TAC (bsrw_ss()) [cB_behaviour]);

(* ----------------------------------------------------------------------
    norm_reduct - get the normal order reduct, if there is one.
                  If there isn't, just return something unspecified.

      (noreduct (LAM v M) = OPTION_MAP (LAM v) (noreduct M)) ∧
      (noreduct (LAM v M @@ N) = SOME ([N/v]M)) ∧
      (¬is_abs M ⇒ (noreduct (M @@ N) =
                    if bnf M then OPTION_MAP ((@@) M) (noreduct N)
                    else OPTION_MAP (λM'. M' @@ N) (noreduct M))) ∧
      (noreduct (VAR s) = NONE)

    We can ignore all the option_map cruft.
   ---------------------------------------------------------------------- *)

val cnoreduct_def = Define`
  cnoreduct =
  termrec
    @@ (LAM "i" (cdV @@ VAR "i"))
    @@ (LAM "t0" (LAM "t1" (LAM "r0" (LAM "r1"
          (cis_abs @@ VAR "t0"  (* if left term is abstraction *)
                   @@ (cnsub @@ VAR "t1"
                             @@ church 0
                             @@ (termrec @@ I @@ I @@ K @@ VAR "t0"))
                   @@ (cbnf @@ VAR "t0" (* if left term is in bnf *)
                            @@ (cdAPP @@ VAR "t0" @@ VAR "r1")
                            @@ (cdAPP @@ VAR "r0" @@ VAR "t1")))))))
    @@ (LAM "t0" (LAM "r" (cdABS @@ VAR "r")))
`;

val FV_cnoreduct = Store_thm(
  "FV_cnoreduct",
  ``FV cnoreduct = {}``,
  SRW_TAC [][cnoreduct_def, EXTENSION]);

val cnoreduct_equiv = brackabs_equiv [] cnoreduct_def

open dnoreductTheory
val cnoreduct_correct = store_thm(
  "cnoreduct_correct",
  ``∀d. cnoreduct @@ cDB d -n->* if dbnf d then cDB d
                                 else cDB (THE (dnoreduct d))``,
  Q_TAC SUFF_TAC `
    ∀d. (dbnf d ⇒ cnoreduct @@ cDB d -n->* cDB d) ∧
        (¬dbnf d ⇒ cnoreduct @@ cDB d -n->* cDB (THE (dnoreduct d)))
  ` THEN1 METIS_TAC[] THEN
  SIMP_TAC (bsrw_ss()) [cnoreduct_equiv] THEN
  Q.MATCH_ABBREV_TAC
    `∀d. (dbnf d ⇒ termrec @@ cdV @@ COMB @@ ABS @@ cDB d == cDB d) ∧
         (¬dbnf d ⇒
            termrec @@ cdV @@ COMB @@ ABS @@ cDB d ==
            cDB (THE (dnoreduct d)))` THEN
  Induct THEN
  ASM_SIMP_TAC (bsrw_ss()) [termrec_behaviour, cdV_behaviour] THENL [
    Cases_on `is_dABS d` THEN ASM_SIMP_TAC (srw_ss()) [] THENL [
      Cases_on `d` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      ASM_SIMP_TAC (bsrw_ss()) [Abbr`COMB`, cis_abs_behaviour, cB_behaviour,
                                termrec_behaviour, cnsub_behaviour],

      Cases_on `dbnf d` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
        ASM_SIMP_TAC (bsrw_ss()) [Abbr`COMB`, cis_abs_behaviour, cB_behaviour,
                                  cbnf_behaviour, cdAPP_behaviour] THEN
        STRIP_TAC THEN IMP_RES_TAC notbnf_dnoreduct THEN
        SRW_TAC [][],
        IMP_RES_TAC notbnf_dnoreduct THEN
        ASM_SIMP_TAC (bsrw_ss()) [Abbr`COMB`, cis_abs_behaviour, cB_behaviour,
                                  cbnf_behaviour, cdAPP_behaviour]
      ]
    ],

    ASM_SIMP_TAC (bsrw_ss()) [Abbr`ABS`, cdABS_behaviour] THEN
    STRIP_TAC THEN IMP_RES_TAC notbnf_dnoreduct THEN
    SRW_TAC [][]
  ]);


val cnoreduct_behaviour = store_thm(
  "cnoreduct_behaviour",
  ``∀t. ¬bnf t ⇒
           cnoreduct @@ cDB (fromTerm t) -n->*
           cDB (fromTerm (THE (noreduct t)))``,
  SIMP_TAC (bsrw_ss()) [cnoreduct_correct] THEN
  REPEAT STRIP_TAC THEN
  Cases_on `noreduct t` THEN FULL_SIMP_TAC (srw_ss()) [noreduct_bnf]);

val cnoreduct_behaviour' =
    SIMP_RULE (srw_ss()) [] (SPEC ``toTerm d`` cnoreduct_behaviour)

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

val cchurch_behaviour = bstore_thm(
  "cchurch_behaviour",
  ``cchurch @@ church n -n->* cDB (fromTerm (church n))``,
  SIMP_TAC (bsrw_ss()) [cchurch_def, cichurch_behaviour] THEN
  SIMP_TAC (bsrw_ss()) [church_def, cdABS_behaviour, fromTerm_funpow_app,
                        dLAM_def, lift_funpow_dAPP, sub_funpow_dAPP] THEN
  SIMP_TAC (srw_ss() ++ ARITH_ss) []);

(* ----------------------------------------------------------------------
    cdbsize

    computes the size of a term
   ---------------------------------------------------------------------- *)

val cdbsize_def = Define`
  cdbsize =
  LAM "t"
  (VAR "t"
       @@ (K @@ church 1)
       @@ (LAM "r1" (LAM "r2"
              (cplus @@ (cplus @@ VAR "r1" @@ VAR "r2") @@ church 1)))
       @@ (cplus @@ church 1))
`;
val FV_cdbsize = Store_thm(
  "FV_cdbsize",
  ``FV cdbsize = {}``,
  SRW_TAC [][EXTENSION, cdbsize_def]);

val cdbsize_equiv = brackabs_equiv [] cdbsize_def

val cdbsize_behaviour = store_thm(
  "cdbsize_behaviour",
  ``cdbsize @@ cDB t -n->* church (dbsize t)``,
  SIMP_TAC (bsrw_ss()) [cdbsize_equiv] THEN Induct_on `t` THEN
  ASM_SIMP_TAC (bsrw_ss() ++ ARITH_ss) [cDB_thm, cplus_behaviour]);

(* ----------------------------------------------------------------------
    cis_church

    determines if a term is a church numeral
   ---------------------------------------------------------------------- *)

(* cis_varn checks to see if a term is a variable of the given index *)
val cis_varn_def = Define`
  cis_varn = LAM "n" (LAM "t" (VAR "t"
                                   @@ (ceqnat @@ VAR "n")
                                   @@ (K @@ (K @@ cB F))
                                   @@ (K @@ cB F)))
`;

val FV_cis_varn = Store_thm(
  "FV_cis_varn",
  ``FV cis_varn = {}``,
  SRW_TAC [][cis_varn_def, EXTENSION]);

val cis_varn_equiv = brackabs_equiv [] cis_varn_def

val cis_varn_behaviour = store_thm(
  "cis_varn_behaviour",
  ``cis_varn @@ church n @@ cDB t -n->* cB (t = dV n)``,
  SIMP_TAC (bsrw_ss()) [cis_varn_equiv] THEN
  Cases_on `t` THEN
  SIMP_TAC (bsrw_ss()) [cDB_thm, ceqnat_behaviour, EQ_IMP_THM]);

(* cis_ichurch determines if a term is the application of some number of
   dV 0 terms to a dV 1 *)
val cis_ichurch_def = Define`
  cis_ichurch =
  termrec @@ (ceqnat @@ church 1)
          @@ (LAM "t1" (LAM "t2" (LAM "r1" (LAM "r2"
                (cand @@ (cis_varn @@ church 0 @@ VAR "t1")
                      @@ VAR "r2")))))
          @@ (K @@ (K @@ cB F))
`;

val FV_cis_ichurch = Store_thm(
  "FV_cis_ichurch",
  ``FV cis_ichurch = {}``,
  SRW_TAC [][EXTENSION, cis_ichurch_def]);

val cis_ichurch_equiv = brackabs_equiv [] cis_ichurch_def

val cis_ichurch_behaviour = store_thm(
  "cis_ichurch_behaviour",
  ``cis_ichurch @@ cDB t -n->* cB (∃n. t = FUNPOW (dAPP (dV 0)) n (dV 1))``,
  SIMP_TAC (bsrw_ss()) [cis_ichurch_equiv] THEN Induct_on `t` THEN
  ASM_SIMP_TAC (bsrw_ss()) [termrec_behaviour, ceqnat_behaviour,
                            cand_behaviour, cis_varn_behaviour]
  THENL [
    SRW_TAC [][EQ_IMP_THM] THENL [
      Q.EXISTS_TAC `0` THEN SRW_TAC [][],
      Cases_on `n'` THEN FULL_SIMP_TAC (srw_ss()) [FUNPOW_SUC]
    ],

    EQ_TAC THENL [
      SRW_TAC [][] THEN Q.EXISTS_TAC `SUC n` THEN SRW_TAC [][FUNPOW_SUC],
      STRIP_TAC THEN Cases_on `n` THEN
      FULL_SIMP_TAC (srw_ss()) [FUNPOW_SUC] THEN
      METIS_TAC []
    ],

    Cases_on `n` THEN SRW_TAC [][FUNPOW_SUC]
  ]);

val cis_church_def = Define`
  cis_church =
  termrec @@ (K @@ cB F)
          @@ (K @@ (K @@ (K @@ (K @@ cB F))))
          @@ (LAM "t" (LAM "r"
                (termrec @@ (K @@ cB F)
                         @@ (K @@ (K @@ (K @@ (K @@ cB F))))
                         @@ (LAM "t" (LAM "r" (cis_ichurch @@ VAR "t")))
                         @@ VAR "t")))
`;

val FV_cis_church = Store_thm(
  "FV_cis_church",
  ``FV cis_church = {}``,
  SRW_TAC [][cis_church_def, EXTENSION]);

val cis_church_equiv = brackabs_equiv [] cis_church_def

val cis_church_behaviour = store_thm(
  "cis_church_behaviour",
  ``cis_church @@ cDB t -n->* cB (is_church (toTerm t))``,
  SIMP_TAC (bsrw_ss()) [cis_church_equiv] THEN
  Cases_on `t` THEN SIMP_TAC (bsrw_ss()) [termrec_behaviour] THENL [
    SRW_TAC [][is_church_def],
    SRW_TAC [][is_church_def],
    ALL_TAC
  ] THEN
  Q.MATCH_ABBREV_TAC `termrec @@ VV @@ CC @@ AA @@ cDB tt ==
                      cB (is_church (toTerm (dABS tt)))` THEN
  Q.RM_ABBREV_TAC `tt` THEN markerLib.UNABBREV_ALL_TAC THEN
  Cases_on `tt` THEN SIMP_TAC (bsrw_ss()) [termrec_behaviour] THENL [
    Q.MATCH_ABBREV_TAC `¬is_church (toTerm (dABS (dV n)))` THEN
    `s2n (n2s n) + 1 ∉ dFV (dV n)` by SRW_TAC [ARITH_ss][] THEN
    IMP_RES_TAC toTerm_dABS THEN
    SRW_TAC [][is_church_def, LAM_eq_thm],

    Q.MATCH_ABBREV_TAC `¬is_church (toTerm (dABS (dAPP t1 t2)))` THEN
    Q_TAC (NEW_TAC "z") `dFVs (dABS (dAPP t1 t2))` THEN
    FULL_SIMP_TAC (srw_ss()) [GSYM IN_dFV] THEN
    `s2n z + 1 ∉ dFV (dAPP t1 t2)` by SRW_TAC [][] THEN
    POP_ASSUM (ASSUME_TAC o MATCH_MP (GEN_ALL toTerm_dABS)) THEN
    SRW_TAC [][is_church_def, LAM_eq_thm],

    SIMP_TAC (bsrw_ss()) [cis_ichurch_behaviour] THEN
    Q.MATCH_ABBREV_TAC
      `(∃n. t = FUNPOW (dAPP (dV 0)) n (dV 1)) ⇔
       is_church (toTerm (dABS (dABS t)))` THEN
    Q.RM_ABBREV_TAC `t` THEN
    SRW_TAC [][is_church_def, toTerm_eqn, fromTerm_funpow_app] THEN
    SRW_TAC [][dLAM_def] THEN EQ_TAC THENL [
      SRW_TAC [][] THEN
      MAP_EVERY Q.EXISTS_TAC [`n2s 2`, `n2s 3`, `n`] THEN SRW_TAC [][] THEN
      SRW_TAC [][fromTerm_funpow_app] THEN
      Induct_on `n` THEN SRW_TAC [][FUNPOW_SUC],

      SRW_TAC [][] THEN Q.EXISTS_TAC `n` THEN SRW_TAC [ARITH_ss][] THEN
      Induct_on `n` THEN SRW_TAC [ARITH_ss][FUNPOW_SUC]
    ]
  ]);

(* ----------------------------------------------------------------------
    cforceNum
   ---------------------------------------------------------------------- *)

val cforce_num_def = Define`
  cforce_num =
  LAM "t" (cis_church @@ VAR "t"
                      @@ (cminus @@ (cdiv @@ (cdbsize @@ VAR "t") @@ church 2)
                                 @@ church 1)
                      @@ church 0)
`;

val FV_cforce_num = Store_thm(
  "FV_cforce_num",
  ``FV cforce_num = {}``,
  SRW_TAC [][EXTENSION, cforce_num_def]);

val cforce_num_equiv = brackabs_equiv [] cforce_num_def

val dbsize_fromTerm = Store_thm(
  "dbsize_fromTerm",
  ``∀t. dbsize (fromTerm t) = size t``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);

val size_toTerm = save_thm(
  "size_toTerm",
  dbsize_fromTerm |> Q.SPEC `toTerm d` |> REWRITE_RULE [fromtoTerm] |> SYM);
val _ = export_rewrites ["size_toTerm"]

val cforce_num_behaviour = store_thm(
  "cforce_num_behaviour",
  ``cforce_num @@ cDB t -n->* church (force_num (toTerm t))``,
  SIMP_TAC (bsrw_ss()) [cforce_num_equiv, cdbsize_behaviour, cdiv_behaviour,
                        cminus_behaviour, cis_church_behaviour] THEN
  Cases_on `is_church (toTerm t)` THENL [
    ASM_SIMP_TAC (bsrw_ss()) [cB_behaviour, force_num_size],
    ASM_SIMP_TAC (bsrw_ss()) [force_num_def, cB_behaviour]
  ]);

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

(* ----------------------------------------------------------------------
    computable steps function, csteps
   ---------------------------------------------------------------------- *)

val csteps_def = Define`
  csteps =
  LAM "n" (LAM "t"
    (VAR "n" @@ (LAM "u" (VAR "u"))
             @@ (LAM "f" (LAM "u"
                   (cbnf @@ VAR "u"
                         @@ VAR "u"
                         @@ (VAR "f" @@ (cnoreduct @@ VAR "u")))))
             @@ VAR "t"))
`;

val FV_csteps = Store_thm(
  "FV_csteps",
  ``FV csteps = {}``,
  SRW_TAC [][csteps_def, pred_setTheory.EXTENSION]);

open brackabs
val csteps_eqn = brackabs_equiv [] csteps_def

val cnoreduct_behaviour' =
    cnoreduct_behaviour |> Q.SPEC `toTerm t`
                        |> SIMP_RULE (srw_ss()) []

val csteps_behaviour = store_thm(
  "csteps_behaviour",
  ``∀n t.
      csteps @@ church n @@ cDB t -n->* cDB (fromTerm (steps n (toTerm t)))``,
  SIMP_TAC (bsrw_ss()) [csteps_eqn] THEN
  Induct THEN
  ASM_SIMP_TAC (bsrw_ss()) [churchnumTheory.church_thm, cbnf_behaviour] THEN
  Q.X_GEN_TAC `t` THEN Cases_on `dbnf t` THEN
  ASM_SIMP_TAC (bsrw_ss()) [churchboolTheory.cB_behaviour,
                            cnoreduct_behaviour']);

(* ----------------------------------------------------------------------
    Computable version of bnf_of, bringing us pretty well all the way to
    a universal machine
   ---------------------------------------------------------------------- *)

val cbnf_ofk_def = Define`
  cbnf_ofk =
  LAM "k" (LAM "t" (
    cfindleast @@ (LAM "n" (cbnf @@ (csteps @@ VAR "n" @@ VAR "t")))
               @@ (B @@ VAR "k" @@ (C @@ csteps @@ VAR "t"))))
`;

val cbnf_ofk_eqn = brackabs_equiv [] cbnf_ofk_def

val FV_cbnf_ofk = Store_thm(
  "FV_cbnf_ofk",
  ``FV cbnf_ofk = {}``,
  SRW_TAC [][EXTENSION, cbnf_ofk_def]);

val cbnf_of_works1 = store_thm(
  "cbnf_of_works1",
  ``(bnf_of M = SOME N) ⇒
    cbnf_ofk @@ c @@ cDB (fromTerm M) == c @@ cDB (fromTerm N)``,
  STRIP_TAC THEN
  SIMP_TAC (bsrw_ss()) [cbnf_ofk_eqn] THEN
  Q.MATCH_ABBREV_TAC `cfindleast @@ P @@ k == c @@ cDB (fromTerm N)` THEN
  `∀n. P @@ church n == cB (bnf (steps n M))`
     by SIMP_TAC (bsrw_ss()) [Abbr`P`, csteps_behaviour, cbnf_behaviour] THEN
  Q.RM_ABBREV_TAC `P` THEN
  `∀n. ∃b. P @@ church n == cB b` by METIS_TAC [] THEN
  `∃n. (steps n M = N) ∧ bnf N` by METIS_TAC [stepsTheory.bnf_steps] THEN
  `P @@ church n == cB T` by ASM_SIMP_TAC (bsrw_ss()) [] THEN
  `cfindleast @@ P @@ k == k @@ church (LEAST n. P @@ church n == cB T)`
    by METIS_TAC [cfindleast_termI] THEN
  ASM_SIMP_TAC (bsrw_ss()) [Abbr`k`, csteps_behaviour] THEN
  Q_TAC SUFF_TAC `steps (LEAST n. bnf (steps n M)) M = N` THEN1
        SRW_TAC [][] THEN
  numLib.LEAST_ELIM_TAC THEN SRW_TAC [][] THEN
  METIS_TAC [stepsTheory.bnf_steps_upwards_closed,
            DECIDE ``(n:num) < m ∨ (n = m) ∨ m < n``]);

val cbnf_ofk_works2 = store_thm(
  "cbnf_ofk_works2",
  ``cbnf_ofk @@ k @@ cDB M -n->* t' ∧ bnf t' ⇒
    ∃M'. (bnf_of (toTerm M) = SOME (toTerm M')) ∧ k @@ cDB M' -n->* t'``,
  SIMP_TAC (bsrw_ss() ++ boolSimps.CONJ_ss) [cbnf_ofk_eqn] THEN
  Q.MATCH_ABBREV_TAC
    `cfindleast @@ P @@ kk == t' ∧ bnf t' ⇒ CONCL` THEN
  `∀n. P @@ church n == cB (bnf (steps n (toTerm M)))`
     by SIMP_TAC (bsrw_ss()) [Abbr`P`, csteps_behaviour, cbnf_behaviour] THEN
  Q.RM_ABBREV_TAC `P` THEN
  `∀n. ∃b. P @@ church n == cB b` by METIS_TAC [] THEN
  STRIP_TAC THEN
  `∃m. t' == kk @@ church m ∧ P @@ church m == cB T`
     by METIS_TAC [cfindleast_bnfE] THEN
  NTAC 2 (POP_ASSUM MP_TAC) THEN
  ASM_SIMP_TAC (bsrw_ss()) [Abbr`kk`, Abbr`CONCL`, csteps_behaviour,
                            stepsTheory.bnf_steps] THEN
  REPEAT STRIP_TAC THEN
  Q.EXISTS_TAC `fromTerm (steps m (toTerm M))` THEN
  SRW_TAC [][] THEN METIS_TAC []);

val bnfNONE_cbnf_ofk_fails = store_thm(
  "bnfNONE_cbnf_ofk_fails",
  ``(bnf_of M = NONE) ⇒ ¬has_bnf (cbnf_ofk @@ k @@ cDB (fromTerm M))``,
  REPEAT STRIP_TAC THEN
  `∃t'. cbnf_ofk @@ k @@ cDB (fromTerm M) -n->* t' ∧ bnf t'`
     by METIS_TAC [has_bnf_thm, nstar_betastar_bnf] THEN
  IMP_RES_TAC (REWRITE_RULE [GSYM AND_IMP_INTRO] cbnf_ofk_works2) THEN
  FULL_SIMP_TAC (srw_ss()) []);

val _ = overload_on ("cbnf_of", ``cbnf_ofk @@ I``);

val cbnf_of_fails = store_thm(
  "cbnf_of_fails",
  ``(bnf_of M = NONE) ⇔ ¬has_bnf (cbnf_of @@ cDB (fromTerm M))``,
  SRW_TAC [][EQ_IMP_THM, bnfNONE_cbnf_ofk_fails] THEN
  Cases_on `bnf_of M` THEN SRW_TAC [][] THEN
  IMP_RES_TAC cbnf_of_works1 THEN
  `cbnf_ofk @@ I @@ cDB (fromTerm M) == cDB (fromTerm x)`
    by METIS_TAC [chap2Theory.lam_eq_rules, chap2Theory.lameq_I] THEN
  METIS_TAC [bnf_cDB, betastar_lameq_bnf, has_bnf_thm]);

val cbnf_force_num_fails = store_thm(
  "cbnf_force_num_fails",
  ``¬has_bnf (cbnf_ofk @@ cforce_num @@ cDB (fromTerm M)) ⇒
    (bnf_of M = NONE)``,
  REPEAT STRIP_TAC THEN Cases_on `bnf_of M` THEN SRW_TAC [][] THEN
  IMP_RES_TAC cbnf_of_works1 THEN
  POP_ASSUM (Q.SPEC_THEN `cforce_num` MP_TAC) THEN
  SIMP_TAC (bsrw_ss()) [cforce_num_behaviour] THEN
  METIS_TAC [bnf_church, betastar_lameq_bnf, has_bnf_thm]);

val bnf_of_cbnf = store_thm(
  "bnf_of_cbnf",
  ``bnf_of (cbnf_of @@ cDB t) =
    OPTION_MAP (cDB o fromTerm) (bnf_of (toTerm t))``,
  Cases_on `bnf_of (toTerm t)` THENL [
    IMP_RES_TAC bnfNONE_cbnf_ofk_fails THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [bnf_of_NONE],
    IMP_RES_TAC cbnf_of_works1 THEN
    FULL_SIMP_TAC (bsrw_ss()) [bnf_bnf_of]
  ]);

val _ = export_theory()
