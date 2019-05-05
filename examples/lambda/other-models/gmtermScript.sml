(* this is an -*- sml -*- file *)
(* script file establishing a type of lambda-terms on top of the
   GM base.  Does this by defining the predicate "const-free" *)

open HolKernel Parse boolLib bossLib BasicProvers boolSimps NEWLib
open ncTheory swapTheory binderLib

val _ = new_theory "gmterm";

val (constfree_rules, constfree_ind, constfree_cases) = Hol_reln`
  (!s. constfree (nc$VAR s)) /\
  (!M N. constfree M /\ constfree N ==> constfree (M @@ N)) /\
  (!v M. constfree M ==> constfree (LAM v M))
`;

val constfree_swap_I = prove(
  ``!M. constfree M ==> !x y. constfree (swap x y M)``,
  HO_MATCH_MP_TAC constfree_ind THEN SRW_TAC [][constfree_rules]);

Theorem constfree_thm[simp]:
    (constfree (nc$VAR s) = T) /\
    (constfree (M @@ N) ⇔ constfree M /\ constfree N) /\
    (constfree (LAM v M) = constfree M) /\
    (constfree (CON k) = F)
Proof
  REPEAT CONJ_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [constfree_cases])) THEN
  SRW_TAC [][] THEN EQ_TAC THENL [
    SRW_TAC [][LAM_INJ_swap] THEN
    METIS_TAC [lswap_def, constfree_swap_I],
    METIS_TAC []
  ]
QED

val lswap_constfree = prove(
  ``!t. constfree (lswap pi t) = constfree t``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);
val _ = augment_srw_ss [rewrites [lswap_constfree]]

val swap_constfree = prove(
  ``constfree (swap x y t) = constfree t``,
  MP_TAC (Q.INST [`pi` |-> `[(x,y)]`] (SPEC_ALL lswap_constfree)) THEN
  REWRITE_TAC [lswap_def]);
val _ = augment_srw_ss [rewrites [swap_constfree]]

val term_ax = new_type_definition(
  "term",
  prove(``?t : one nc. constfree t``,
        Q.EXISTS_TAC `nc$VAR s` THEN SRW_TAC [][]))

val term_bij = define_new_type_bijections
                 {ABS = "to_term", REP = "from_term",
                  name = "term_bij", tyax = term_ax}

val _ = app (fn s => remove_ovl_mapping s {Name = s, Thy = "nc"})
            ["LAM", "VAR", "CON", "@@", "FV", "SUB", "ABS", "size"]

val VAR_def = Define`VAR s = to_term (nc$VAR s)`
val APP_def = xDefine "APP"
                      `M @@ N = to_term (nc$@@ (from_term M) (from_term N))`
val LAM_def = Define`LAM v t = to_term (nc$LAM v (from_term t))`

val fromto_inverse = prove(
  ``constfree t ==> (from_term (to_term t) = t)``,
  METIS_TAC [term_bij]);

val tofrom_inverse = prove(
  ``to_term (from_term t) = t``,
  SRW_TAC [][term_bij]);
val _ = augment_srw_ss [rewrites [tofrom_inverse]]

val constfree_from_term = prove(
  ``constfree (from_term M)``,
  SRW_TAC [][term_bij]);
val _ = augment_srw_ss [rewrites [constfree_from_term]]

val from_term_11 = prove(
  ``(from_term t = from_term u) = (t = u)``,
  METIS_TAC [term_bij]);

Theorem term_11[simp]:
    ((VAR s = VAR t) = (s = t)) /\
    ((M1 @@ N1 = M2 @@ N2) ⇔ (M1 = M2) /\ (N1 = N2)) /\
    ((LAM v M1 = LAM v M2) ⇔ (M1 = M2))
Proof
  SRW_TAC [][VAR_def, APP_def, LAM_def, EQ_IMP_THM] THEN
  POP_ASSUM (MP_TAC o AP_TERM ``from_term``) THEN
  SRW_TAC [][fromto_inverse] THEN
  FULL_SIMP_TAC (srw_ss()) [from_term_11]
QED

val term_distinct = store_thm(
  "term_distinct",
  ``~(VAR s = M @@ N) /\ ~(VAR s = LAM v t) /\ ~(M @@ N = LAM v t)``,
  SRW_TAC [][VAR_def, APP_def, LAM_def] THEN STRIP_TAC THEN
  POP_ASSUM (MP_TAC o AP_TERM ``from_term``) THEN
  SRW_TAC [][fromto_inverse]);
val _ = export_rewrites ["term_distinct"]

val simple_induction = store_thm(
  "simple_induction",
  ``!P. (!s. P (VAR s)) /\
        (!M N. P M /\ P N ==> P (M @@ N)) /\
        (!v M. P M ==> P (LAM v M)) ==>
        !M. P M``,
  SIMP_TAC (srw_ss())[VAR_def, APP_def, LAM_def] THEN
  GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!M. constfree M ==> P (to_term M)`
        THEN1 (REPEAT STRIP_TAC THEN
               `M = to_term (from_term M)` by METIS_TAC [term_bij] THEN
               POP_ASSUM SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
               SRW_TAC [][term_bij]) THEN
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][] THENL [
    `(M = from_term (to_term M)) /\ (M' = from_term (to_term M'))`
      by METIS_TAC [term_bij] THEN
    NTAC 2 (POP_ASSUM SUBST1_TAC) THEN
    SRW_TAC [][],
    `(M = from_term (to_term M))` by METIS_TAC [term_bij] THEN
    POP_ASSUM SUBST1_TAC THEN SRW_TAC [][]
  ]);

val tpm_def = Define`tpm pi t = to_term (lswap pi (from_term t))`



val tpm_thm = store_thm(
  "tpm_thm",
  ``(tpm pi (VAR s) = VAR (raw_lswapstr pi s)) /\
    (tpm pi (M @@ N) = tpm pi M @@ tpm pi N) /\
    (tpm pi (LAM v M) = LAM (raw_lswapstr pi v) (tpm pi M))``,
  SRW_TAC [][tpm_def, LAM_def, APP_def, VAR_def, fromto_inverse]);
val _ = export_rewrites ["tpm_thm"]

val FV_def = Define`FV t = nc$FV (from_term t)`

val FV_thm = store_thm(
  "FV_thm",
  ``(FV (VAR s) = {s}) /\
    (FV (M @@ N) = FV M UNION FV N) /\
    (FV (LAM v M) = FV M DELETE v)``,
  SRW_TAC [][FV_def, LAM_def, APP_def, VAR_def, fromto_inverse]);
val _ = export_rewrites ["FV_thm"]

val FINITE_FV = store_thm(
  "FINITE_FV",
  ``FINITE (FV t)``,
  SRW_TAC [][FV_def]);
val _ = export_rewrites ["FINITE_FV"]

val constfree_SUB = prove(
  ``!t. constfree t /\ constfree u ==> constfree (nc$SUB u x t)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `x INSERT nc$FV u` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);
val _ = augment_srw_ss [rewrites [constfree_SUB]]

val SUB_def = Define`[N/v] M = to_term (nc$SUB (from_term N) v (from_term M))`;

val SUB_THM = store_thm(
  "SUB_THM",
  ``([u/x] (VAR x) = u) /\
    (~(x = y) ==> ([u/x] (VAR y) = VAR y)) /\
    ([u/x] (s @@ t) = [u/x]s @@ [u/x] t) /\
    ([u/x] (LAM x t) = LAM x t) /\
    (~(x = y) /\ ~(y IN FV u) ==> ([u/x] (LAM y t) = LAM y ([u/x] t)))``,
  SRW_TAC [][FV_def, SUB_def, LAM_def, VAR_def, APP_def,
             fromto_inverse, ncTheory.SUB_THM]);

val SUB_VAR = store_thm(
  "SUB_VAR",
  ``[t/y] (VAR x) = if x = y then t else VAR x``,
  SRW_TAC [][VAR_def, SUB_def, fromto_inverse, SUB_VAR]);

val tpm_NIL = store_thm(
  "tpm_NIL",
  ``!t. tpm [] t = t``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][]);
val _ = export_rewrites ["tpm_NIL"]

Theorem LAM_eq_thm:
    (LAM u M = LAM v N) ⇔ ((u = v) /\ (M = N)) \/
                          (~(u = v) /\ ~(u IN FV N) /\ (M = tpm [(u,v)] N))
Proof
  SRW_TAC [][LAM_def, FV_def, tpm_def, EQ_IMP_THM] THENL [
    POP_ASSUM (MP_TAC o AP_TERM ``from_term``) THEN
    SRW_TAC [][fromto_inverse, LAM_INJ_swap] THENL [
      Cases_on `u = v` THEN FULL_SIMP_TAC (srw_ss()) [lswap_def] THEN
      FIRST_X_ASSUM (MP_TAC o AP_TERM ``to_term``) THEN SRW_TAC [][],
      FULL_SIMP_TAC (srw_ss()) [from_term_11]
    ],
    AP_TERM_TAC THEN SRW_TAC [][fromto_inverse, LAM_INJ_swap,
                                lswap_def]
  ]
QED

Theorem FV_tpm[simp]:
    !t pi v. v ∈ FV (tpm pi t) ⇔ raw_lswapstr (REVERSE pi) v IN FV t
Proof
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][basic_swapTheory.raw_lswapstr_eql]
QED

val tpm_inverse = store_thm(
  "tpm_inverse",
  ``!t pi. (tpm pi (tpm (REVERSE pi) t) = t) /\
           (tpm (REVERSE pi) (tpm pi t) = t)``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);
val _ = export_rewrites ["tpm_inverse"]

val tpm_eqr = store_thm(
  "tpm_eqr",
  ``(t = tpm pi u) = (tpm (REVERSE pi) t = u)``,
  METIS_TAC [tpm_inverse]);

val tpm_eql = store_thm(
  "tpm_eql",
  ``(tpm pi t = u) = (t = tpm (REVERSE pi) u)``,
  METIS_TAC [tpm_inverse]);

val tpm_flip_args = store_thm(
  "tpm_flip_args",
  ``!t. tpm ((y,x)::rest) t = tpm ((x,y)::rest) t``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);

val tpm_APPEND = store_thm(
  "tpm_APPEND",
  ``!t. tpm (p1 ++ p2) t = tpm p1 (tpm p2 t)``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][basic_swapTheory.raw_lswapstr_APPEND]);

val tpm_CONS = store_thm(
  "tpm_CONS",
  ``tpm ((x,y)::pi) t = tpm [(x,y)] (tpm pi t)``,
  SRW_TAC [][GSYM tpm_APPEND]);

val tpm_sing_inv = store_thm(
  "tpm_sing_inv",
  ``tpm [h] (tpm [h] t) = t``,
  ACCEPT_TAC
    (SIMP_RULE list_ss [] (Q.INST [`pi` |-> `[h]`] (SPEC_ALL tpm_inverse))))
val _ = export_rewrites ["tpm_sing_inv"]

val nc_INDUCTION2 = store_thm(
  "nc_INDUCTION2",
  ``!P X. (!x. P (VAR x)) /\
          (!t u. P t /\ P u ==> P (t @@ u)) /\
          (!y u. ~(y IN X) /\ P u ==> P (LAM y u)) /\  FINITE X ==>
          !u. P u``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!u pi. P (tpm pi u)` THEN1 METIS_TAC [tpm_NIL] THEN
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][] THEN
  Q_TAC (NEW_TAC "z") `raw_lswapstr pi v INSERT FV (tpm pi u) UNION X` THEN
  Q_TAC SUFF_TAC `LAM (raw_lswapstr pi v) (tpm pi u) =
                  LAM z (tpm ((z,raw_lswapstr pi v)::pi) u)`
        THEN1 SRW_TAC [][] THEN
  SRW_TAC [][LAM_eq_thm, basic_swapTheory.raw_lswapstr_APPEND] THENL [
    FULL_SIMP_TAC (srw_ss()) [],
    SRW_TAC [][tpm_eqr, tpm_flip_args, tpm_APPEND]
  ]);

val tpm_sing_to_back = store_thm(
  "tpm_sing_to_back",
  ``!t. tpm [(raw_lswapstr p u, raw_lswapstr p v)] (tpm p t) = tpm p (tpm [(u,v)] t)``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][basic_swapTheory.raw_lswapstr_sing_to_back]);

val tpm_subst = store_thm(
  "tpm_subst",
  ``!N. tpm pi ([M/v] N) = [tpm pi M/raw_lswapstr pi v] (tpm pi N)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `v INSERT FV M` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val tpm_subst_out = store_thm(
  "tpm_subst_out",
  ``[M/v] (tpm pi N) =
       tpm pi ([tpm (REVERSE pi) M/raw_lswapstr (REVERSE pi) v] N)``,
  SRW_TAC [][tpm_subst])

val tpm_idfront = store_thm(
  "tpm_idfront",
  ``!t. tpm ((v,v)::rest) t = tpm rest t``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);
val _ = export_rewrites ["tpm_idfront"]

val tpm_fresh = store_thm(
  "tpm_fresh",
  ``!t. ~(x IN FV t) /\ ~(y IN FV t) ==> (tpm [(x,y)] t = t)``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][] THEN
  SRW_TAC [][] THEN SRW_TAC [CONJ_ss][LAM_eq_thm, tpm_flip_args] THEN
  Cases_on `x = v` THEN SRW_TAC [][] THEN
  Cases_on `y = v` THEN SRW_TAC [][] THEN
  FULL_SIMP_TAC (srw_ss()) [tpm_flip_args]);

val tpm_apart = store_thm(
  "tpm_apart",
  ``!t. x IN FV t /\ ~(y IN FV t) ==> ~(tpm [(x,y)] t = t)``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][] THENL [
    METIS_TAC [],
    METIS_TAC [],
    SRW_TAC [][LAM_eq_thm] THEN
    Cases_on `y = v` THEN SRW_TAC [][],
    SRW_TAC [][LAM_eq_thm]
  ]);

val fresh_tpm_subst = store_thm(
  "fresh_tpm_subst",
  ``!M. ~(u IN FV M) ==> (tpm [(u,v)] M = [VAR u/v] M)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val SIMPLE_ALPHA = store_thm(
  "SIMPLE_ALPHA",
  ``~(y IN FV u) ==> !x. LAM x u = LAM y ([VAR y/x] u)``,
  SRW_TAC [][GSYM fresh_tpm_subst] THEN
  SRW_TAC [CONJ_ss][LAM_eq_thm, tpm_flip_args]);

val tpm_ALPHA = store_thm(
  "tpm_ALPHA",
  ``~(v IN FV u) ==> !x. LAM x u = LAM v (tpm [(v,x)] u)``,
  SRW_TAC [][fresh_tpm_subst, SIMPLE_ALPHA]);

val lemma14a = store_thm(
  "lemma14a",
  ``!t. [VAR v/v] t = t``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);
val _ = export_rewrites ["lemma14a"]

val lemma14b = store_thm(
  "lemma14b",
  ``!M. ~(v IN FV M) ==> ([N/v] M = M)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `v INSERT FV N` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

open pred_setTheory

val lemma14c = store_thm(
  "lemma14c",
  ``!t x u. x IN FV u ==> (FV ([t/x]u) = FV t UNION (FV u DELETE x))``,
  NTAC 2 GEN_TAC THEN HO_MATCH_MP_TAC nc_INDUCTION2 THEN
  Q.EXISTS_TAC `x INSERT FV t` THEN
  SRW_TAC [][SUB_THM, SUB_VAR, EXTENSION] THENL [
    Cases_on `x IN FV u'` THEN SRW_TAC [][lemma14b] THEN METIS_TAC [],
    Cases_on `x IN FV u` THEN SRW_TAC [][lemma14b] THEN METIS_TAC [],
    METIS_TAC []
  ]);

val lemma15a = store_thm(
  "lemma15a",
  ``!M. ~(v IN FV M) ==> ([N/v]([VAR v/x]M) = [N/x]M)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{x;v} UNION FV N` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);

val lemma15b = store_thm(
  "lemma15b",
  ``~(v IN FV M) ==> ([VAR u/v]([VAR v/u] M) = M)``,
  SRW_TAC [][lemma15a]);

val FV_SUB = store_thm(
  "FV_SUB",
  ``!t u v. FV ([t/v] u) = if v IN FV u then FV t UNION (FV u DELETE v)
                           else FV u``,
  PROVE_TAC [lemma14b, lemma14c]);

(* ----------------------------------------------------------------------
    iterated substitutions (ugh)
   ---------------------------------------------------------------------- *)

val ISUB_def =
 Define
     `($ISUB t [] = t)
  /\  ($ISUB t ((s,x)::rst) = $ISUB ([s/x]t) rst)`;

val _ = set_fixity "ISUB" (Infixr 501);

val DOM_DEF =
 Define
     `(DOM [] = {})
  /\  (DOM ((x,y)::rst) = {y} UNION DOM rst)`;

val FVS_DEF =
 Define
    `(FVS [] = {})
 /\  (FVS ((t,x)::rst) = FV t UNION FVS rst)`;


val FINITE_DOM = Q.store_thm("FINITE_DOM",
 `!ss. FINITE (DOM ss)`,
Induct THENL [ALL_TAC, Cases]
   THEN RW_TAC std_ss [DOM_DEF, FINITE_EMPTY, FINITE_UNION, FINITE_SING]);
val _ = export_rewrites ["FINITE_DOM"]


val FINITE_FVS = Q.store_thm("FINITE_FVS",
`!ss. FINITE (FVS ss)`,
Induct THENL [ALL_TAC, Cases]
   THEN RW_TAC std_ss [FVS_DEF, FINITE_EMPTY, FINITE_UNION, FINITE_FV]);
val _ = export_rewrites ["FINITE_FVS"]

val ISUB_LAM = store_thm(
  "ISUB_LAM",
  ``!R x. ~(x IN (DOM R UNION FVS R)) ==>
          !t. (LAM x t) ISUB R = LAM x (t ISUB R)``,
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [ISUB_def, pairTheory.FORALL_PROD,
                           DOM_DEF, FVS_DEF, SUB_THM]);

(* ----------------------------------------------------------------------
    size of a term
   ---------------------------------------------------------------------- *)

val size_def = Define`size t = nc$size (from_term t)`;

val size_thm = store_thm(
  "size_thm",
  ``(size (VAR s) = 1) /\
    (size (t @@ u) = size t + size u + 1) /\
    (size (LAM v t) = size t + 1)``,
  SRW_TAC [][size_def, ncTheory.size_thm, fromto_inverse, VAR_def, APP_def,
             LAM_def]);
val _ = export_rewrites ["size_thm"]

val size_tpm = store_thm(
  "size_tpm",
  ``!t. size (tpm pi t) = size t``,
  HO_MATCH_MP_TAC simple_induction THEN
  SRW_TAC [][]);
val _ = export_rewrites ["size_tpm"]

val size_vsubst = store_thm(
  "size_vsubst",
  ``!t. size ([VAR v/u] t) = size t``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{u;v}` THEN
  SRW_TAC [][SUB_THM, SUB_VAR]);
val _ = export_rewrites ["size_vsubst"]

(* ----------------------------------------------------------------------
    proving a recursion theorem
   ---------------------------------------------------------------------- *)
val gm_recursion = prove(
  ``!var app lam.
      ?hom : term -> 'b.
        (!s. hom (VAR s) = var s) /\
        (!t u. hom (t @@ u) = app (hom t) (hom u) t u) /\
        !v t. hom (LAM v t) = lam (\y. hom ([VAR y/v] t))
                                  (\y. [VAR y/v] t)``,
  REPEAT GEN_TAC THEN
  Q.SPECL_THEN [`\k. ARB`, `var`,
                `\rt ru t u. app rt ru (to_term t) (to_term u)`,
                `\rf tf. lam rf (to_term o tf)`] MP_TAC
               (INST_TYPE [alpha |-> ``:one``] nc_RECURSION) THEN
  DISCH_THEN (STRIP_ASSUME_TAC o CONJUNCT1 o CONV_RULE EXISTS_UNIQUE_CONV) THEN
  Q.EXISTS_TAC `hom o from_term` THEN
  SRW_TAC [][VAR_def, APP_def, LAM_def, fromto_inverse,
             combinTheory.o_ABS_R, SUB_def]);

val ABS_def = Define`ABS f = to_term (nc$ABS (from_term o f))`

val ABS_axiom = prove(
  ``gmterm$ABS (\y. [VAR y/v] t) = LAM v t``,
  SRW_TAC [][LAM_def, ABS_def, SUB_def, combinTheory.o_ABS_R,
             fromto_inverse, VAR_def, ncTheory.ABS_DEF]);


val fresh_new_subst0 = prove(
  ``FINITE X ==>
    ((let v = NEW (FV (LAM x u) UNION X) in f v ([VAR v/x] u)) =
     (let v = NEW (FV (LAM x u) UNION X) in f v (tpm [(v,x)] u)))``,
  STRIP_TAC THEN NEW_ELIM_TAC THEN REPEAT STRIP_TAC THEN
  SRW_TAC [][] THEN SRW_TAC [][fresh_tpm_subst]);

val lemma = (SIMP_RULE bool_ss [ABS_axiom, fresh_new_subst0,
                                ASSUME ``FINITE (X:string set)``]o
             Q.INST [`lam'` |-> `lam`] o
             Q.INST [`lam` |->
                        `\r t. let v = NEW (FV (gmterm$ABS t) UNION X)
                               in
                                 lam' (r v) v (t v)`] o
             INST_TYPE [beta |-> alpha] o
             SPEC_ALL) gm_recursion

val term_CASES = store_thm(
  "term_CASES",
  ``!t. (?s. t = VAR s) \/ (?t1 t2. t = t1 @@ t2) \/
        (?v t0. t = LAM v t0)``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][] THEN METIS_TAC []);

val pvh_induction = prove(
  ``!P. (!s. P (VAR s)) /\ (!t u. P t /\ P u ==> P (t @@ u)) /\
        (!v t. (!t'. (size t' = size t) ==> P t') ==> P (LAM v t)) ==>
        !t. P t``,
  REPEAT STRIP_TAC THEN measureInduct_on `size t` THEN
  Q.SPEC_THEN `t` FULL_STRUCT_CASES_TAC term_CASES THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  POP_ASSUM (fn th => FIRST_X_ASSUM MATCH_MP_TAC THEN ASSUME_TAC th) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SRW_TAC [numSimps.ARITH_ss][]);

val swap_RECURSION = store_thm(
  "swap_RECURSION",
  ``swapping rswap rFV /\ FINITE X /\
    (!s. rFV (var s) SUBSET s INSERT X) /\
    (!t' u' t u.
       rFV t' SUBSET FV t UNION X /\ rFV u' SUBSET FV u UNION X ==>
       rFV (app t' u' t u) SUBSET FV t UNION FV u UNION X) /\
    (!t' v t.
       rFV t' SUBSET FV t UNION X ==>
       rFV (lam t' v t) SUBSET FV t DELETE v UNION X) /\
    (!s x y.
       ~(x IN X) /\ ~(y IN X) ==>
       (rswap x y (var s) = var (swapstr x y s))) /\
    (!t t' u u' x y.
       ~(x IN X) /\ ~(y IN X) ==>
       (rswap x y (app t' u' t u) =
        app (rswap x y t') (rswap x y u') (tpm [(x,y)] t) (tpm [(x,y)] u))) /\
    (!t' t x y v.
       ~(x IN X) /\ ~(y IN X) ==>
       (rswap x y (lam t' v t) =
        lam (rswap x y t') (swapstr x y v) (tpm[(x,y)] t))) ==>
    ?hom.
      ((!s. hom (VAR s) = var s) /\
       (!t u. hom (t @@ u) = app (hom t) (hom u) t u) /\
       !v t. ~(v IN X) ==> (hom (LAM v t) = lam (hom t) v t)) /\
      (!t x y.
         ~(x IN X) /\ ~(y IN X) ==>
         (hom (tpm [(x,y)] t) = rswap x y (hom t)))``,
  REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC lemma THEN
  Q.EXISTS_TAC `hom` THEN ASM_SIMP_TAC bool_ss [] THEN
  `!t. rFV (hom t) SUBSET FV t UNION X`
     by (HO_MATCH_MP_TAC pvh_induction THEN ASM_SIMP_TAC (srw_ss()) [] THEN
         REPEAT CONJ_TAC THENL [
           ASM_SIMP_TAC (srw_ss()) [INSERT_UNION_EQ],
           REPEAT STRIP_TAC THEN NEW_ELIM_TAC THEN
           ASM_SIMP_TAC (srw_ss()) [] THEN Q.X_GEN_TAC `u` THEN
           REPEAT STRIP_TAC THENL [
             SRW_TAC [][LET_THM] THEN
             `FV t DELETE v = FV (LAM v t)`  by SRW_TAC [][] THEN
             POP_ASSUM SUBST_ALL_TAC THEN
             `LAM v t = LAM u (tpm [(u,v)] t)` by SRW_TAC [][tpm_ALPHA] THEN
             POP_ASSUM SUBST1_TAC THEN SRW_TAC [][],
             SRW_TAC [][LET_THM]
           ]
         ]) THEN
  ASM_REWRITE_TAC [] THEN
  `!x r. rswap x x r = r` by FULL_SIMP_TAC (srw_ss()) [swapping_def] THEN
  `!t x y. ~(x IN X) /\ ~(y IN X) ==>
           (hom (tpm [(x,y)] t) = rswap x y (hom t))`
     by (HO_MATCH_MP_TAC pvh_induction THEN REPEAT CONJ_TAC THEN
         TRY (SRW_TAC [][] THEN NO_TAC) THEN
         REPEAT STRIP_TAC THEN
         Cases_on `x = y` THEN1 SRW_TAC [][] THEN
         Q_TAC (NEW_TAC "z") `{x;y;v} UNION FV t UNION X` THEN
         `LAM v t = LAM z ([VAR z/v] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
         Q.ABBREV_TAC `M = [VAR z/v] t` THEN
         `size t = size M` by SRW_TAC [][Abbr`M`] THEN
         Q.RM_ABBREV_TAC `M` THEN
         NTAC 2 (POP_ASSUM SUBST_ALL_TAC) THEN
         `hom (tpm [(x,y)] (LAM z M)) = rswap x y (lam (hom M) z M)`
            by (SRW_TAC [][LET_THM] THEN
                NEW_ELIM_TAC THEN ASM_SIMP_TAC bool_ss [] THEN
                Q.X_GEN_TAC `a` THEN
                REVERSE (SRW_TAC [][]) THEN1 SRW_TAC [][] THEN
                Q.MATCH_ABBREV_TAC
                  `lam (rswap a z Y) a (tpm [(a,z)] M') = R` THEN
                Q.UNABBREV_TAC `R` THEN
                `lam (rswap a z Y) a (tpm [(a,z)] M') =
                   lam (rswap a z Y) (swapstr a z z) (tpm [(a,z)] M')`
                  by SRW_TAC [][] THEN
                ` _ = rswap a z (lam Y z M')`
                  by POP_ASSUM (fn th => SRW_TAC [][] THEN ASSUME_TAC th) THEN
                POP_ASSUM SUBST1_TAC THEN
                MATCH_MP_TAC swapping_implies_identity_swap THEN
                Q.EXISTS_TAC `rFV` THEN ASM_REWRITE_TAC [] THEN
                `rFV (lam Y z M') SUBSET FV M' DELETE z UNION X`
                   by (FIRST_ASSUM MATCH_MP_TAC THEN
                       FULL_SIMP_TAC (srw_ss())
                                     [SUBSET_DEF, Abbr`Y`, Abbr`M'`,
                                      swapping_def]) THEN
                Q_TAC SUFF_TAC `~(a IN FV M' DELETE z UNION X) /\
                                ~(z IN FV M' DELETE z UNION X)`
                      THEN1 METIS_TAC [SUBSET_DEF] THEN
                SRW_TAC [][Abbr`M'`]) THEN
         POP_ASSUM SUBST_ALL_TAC THEN REPEAT AP_TERM_TAC THEN
         ASM_SIMP_TAC bool_ss [] THEN NEW_ELIM_TAC THEN
         ASM_REWRITE_TAC [] THEN Q.X_GEN_TAC `a` THEN
         REVERSE (SRW_TAC [][]) THEN1 SRW_TAC [][] THEN
         MATCH_MP_TAC EQ_TRANS THEN
         Q.EXISTS_TAC `rswap a z (lam (hom M) z M)` THEN CONJ_TAC THENL [
           ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
           MATCH_MP_TAC swapping_implies_identity_swap THEN
           Q.EXISTS_TAC `rFV` THEN ASM_REWRITE_TAC [] THEN
           `rFV (lam (hom M) z M) SUBSET FV (LAM z M) UNION X`
             by SRW_TAC [][] THEN
           POP_ASSUM MP_TAC THEN SIMP_TAC (srw_ss()) [SUBSET_DEF] THEN
           METIS_TAC [],
           SRW_TAC [][]
         ]) THEN
  ASM_SIMP_TAC bool_ss [] THEN SRW_TAC [][LET_THM] THEN
  NEW_ELIM_TAC THEN ASM_SIMP_TAC bool_ss [] THEN
  Q.X_GEN_TAC `u` THEN STRIP_TAC THENL [
    `lam (rswap u v (hom t)) u (tpm [(u,v)] t) = rswap u v (lam (hom t) v t)`
       by SRW_TAC [][] THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC swapping_implies_identity_swap THEN
    Q.EXISTS_TAC `rFV` THEN ASM_REWRITE_TAC [] THEN
    `rFV (lam (hom t) v t) SUBSET FV (LAM v t) UNION X`
       by SRW_TAC [][] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [SUBSET_DEF] THEN SRW_TAC [][] THEN
    METIS_TAC [],
    SRW_TAC [][]
  ]);

val term_swapping = store_thm(
  "term_swapping",
  ``swapping (\x y t. tpm [(x,y)] t) FV``,
  SRW_TAC [][swapping_def, tpm_fresh]);
val _ = export_rewrites ["term_swapping"]

val lam_rFV = prove(
  ``(!t' v t. rFV (lam t' v t) SUBSET ((rFV t' UNION FV t) DELETE v) UNION X)
       ==>
    !t' v t. rFV t' SUBSET FV t UNION X ==>
             rFV (lam t' v t) SUBSET (FV t DELETE v) UNION X``,
  SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`t'`, `v`, `t`] ASSUME_TAC) THEN
  REPEAT (POP_ASSUM MP_TAC) THEN
  SRW_TAC [][SUBSET_DEF] THEN METIS_TAC [])
val app_rFV = prove(
  ``(!t' u' t u. rFV (app t' u' t u) SUBSET
                 rFV t' UNION rFV u' UNION FV t UNION FV u UNION X) ==>
    !t' u' t u.
        rFV t' SUBSET FV t UNION X /\ rFV u' SUBSET FV u UNION X ==>
        rFV (app t' u' t u) SUBSET FV t UNION FV u UNION X``,
  SRW_TAC [][] THEN
  FIRST_X_ASSUM (Q.SPECL_THEN [`t'`, `u'`, `t`, `u`] MP_TAC) THEN
  REPEAT (POP_ASSUM MP_TAC) THEN
  SRW_TAC [][SUBSET_DEF] THEN METIS_TAC []);

val swap_RECURSION_improved = save_thm(
  "swap_RECURSION_improved",
  REWRITE_RULE [AND_IMP_INTRO]
               (DISCH_ALL (REWRITE_RULE [UNDISCH lam_rFV, UNDISCH app_rFV]
                                        swap_RECURSION)))

val swap_RECURSION_nosideset = save_thm(
  "swap_RECURSION_nosideset",
  SIMP_RULE (srw_ss()) [] (Q.INST [`X` |-> `{}`] swap_RECURSION_improved))


val _ = export_theory();
