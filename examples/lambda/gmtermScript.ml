(* this is an -*- sml -*- file *)
(* script file establishing a type of lambda-terms on top of the 
   GM base.  Does this by defining the predicate "const-free" *)

open HolKernel Parse boolLib bossLib BasicProvers boolSimps NEWLib
open ncTheory swapTheory

val _ = new_theory "term";

val (constfree_rules, constfree_ind, constfree_cases) = Hol_reln`
  (!s. constfree (nc$VAR s)) /\
  (!M N. constfree M /\ constfree N ==> constfree (nc$@@ M N)) /\
  (!v M. constfree M ==> constfree (nc$LAM v M))
`;

val lswap_constfree = prove(
  ``constfree (lswap pi t) = constfree t``,
  Q_TAC SUFF_TAC `!t. constfree t ==> !pi. constfree (lswap pi t)`
        THEN1 METIS_TAC [lswap_inverse] THEN 
  HO_MATCH_MP_TAC constfree_ind THEN SRW_TAC [][constfree_rules]);
val _ = augment_srw_ss [rewrites [lswap_constfree]]

val swap_constfree = prove(
  ``constfree (swap x y t) = constfree t``,
  MP_TAC (Q.INST [`pi` |-> `[(x,y)]`] lswap_constfree) THEN 
  REWRITE_TAC [lswap_def]);
val _ = augment_srw_ss [rewrites [swap_constfree]]

val constfree_thm = prove(
  ``(constfree (nc$VAR s) = T) /\
    (constfree (nc$CON k) = F) /\
    (constfree (nc$@@ M N) = constfree M /\ constfree N) /\
    (constfree (nc$LAM v M) = constfree M)``,
  REPEAT CONJ_TAC THEN 
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [constfree_cases])) THEN 
  SRW_TAC [][LAM_INJ_swap, EQ_IMP_THM] THEN SRW_TAC [][] THEN 
  METIS_TAC [swap_id]);
val _ = augment_srw_ss [rewrites [constfree_thm]]

val term_ax = new_type_definition(
  "term", 
  prove(``?t : one nc. constfree t``,
        Q.EXISTS_TAC `nc$VAR s` THEN SRW_TAC [][]))

val term_bij = define_new_type_bijections 
                 {ABS = "to_term", REP = "from_term",
                  name = "term_bij", tyax = term_ax}

val _ = map hide ["LAM", "VAR", "CON", "@@", "FV", "SUB"]

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

val term_11 = store_thm(
  "term_11",
  ``((VAR s = VAR t) = (s = t)) /\
    ((M1 @@ N1 = M2 @@ N2) = (M1 = M2) /\ (N1 = N2))``,
  SRW_TAC [][VAR_def, APP_def, EQ_IMP_THM] THEN 
  POP_ASSUM (MP_TAC o AP_TERM ``from_term``) THEN 
  SRW_TAC [][fromto_inverse] THEN 
  FULL_SIMP_TAC (srw_ss()) [from_term_11]);
val _ = export_rewrites ["term_11"]

val term_disjoint = store_thm( 
  "term_disjoint",
  ``~(VAR s = M @@ N) /\ ~(VAR s = LAM v t) /\ ~(M @@ N = LAM v t)``,
  SRW_TAC [][VAR_def, APP_def, LAM_def] THEN STRIP_TAC THEN 
  POP_ASSUM (MP_TAC o AP_TERM ``from_term``) THEN 
  SRW_TAC [][fromto_inverse]);
val _ = export_rewrites ["term_disjoint"]

val strong_constfree_ind = 
    IndDefRules.derive_strong_induction (CONJUNCTS constfree_rules,
                                         constfree_ind)

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
  HO_MATCH_MP_TAC strong_constfree_ind THEN SRW_TAC [][] THENL [
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
  ``(tpm pi (VAR s) = VAR (lswapstr pi s)) /\
    (tpm pi (M @@ N) = tpm pi M @@ tpm pi N) /\
    (tpm pi (LAM v M) = LAM (lswapstr pi v) (tpm pi M))``,
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


val LAM_eq_thm = store_thm(
  "LAM_eq_thm",
  ``(LAM u M = LAM v N) = ((u = v) /\ (M = N)) \/
                          (~(u = v) /\ ~(u IN FV N) /\ (M = tpm [(u,v)] N))``,
  SRW_TAC [][LAM_def, FV_def, tpm_def, EQ_IMP_THM] THENL [
    POP_ASSUM (MP_TAC o AP_TERM ``from_term``) THEN 
    SRW_TAC [][fromto_inverse, LAM_INJ_swap] THENL [
      Cases_on `u = v` THEN FULL_SIMP_TAC (srw_ss()) [lswap_def] THEN 
      FIRST_X_ASSUM (MP_TAC o AP_TERM ``to_term``) THEN SRW_TAC [][],
      FULL_SIMP_TAC (srw_ss()) [from_term_11]
    ],
    AP_TERM_TAC THEN SRW_TAC [][fromto_inverse, LAM_INJ_swap, 
                                lswap_def]
  ]); 

val FV_tpm = store_thm(
  "FV_tpm",
  ``!t pi v. v IN FV (tpm pi t) = lswapstr (REVERSE pi) v IN FV t``,
  HO_MATCH_MP_TAC simple_induction THEN 
  SRW_TAC [][basic_swapTheory.lswapstr_eql]);
val _ = export_rewrites ["FV_tpm"]

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

val tpm_flip_args = store_thm(
  "tpm_flip_args",
  ``!t. tpm ((y,x)::rest) t = tpm ((x,y)::rest) t``,
  HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]);

val tpm_APPEND = store_thm(
  "tpm_APPEND",
  ``!t. tpm (p1 ++ p2) t = tpm p1 (tpm p2 t)``,
  HO_MATCH_MP_TAC simple_induction THEN 
  SRW_TAC [][basic_swapTheory.lswapstr_APPEND]);

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
  Q_TAC (NEW_TAC "z") `lswapstr pi v INSERT FV (tpm pi u) UNION X` THEN 
  Q_TAC SUFF_TAC `LAM (lswapstr pi v) (tpm pi u) = 
                  LAM z (tpm ((z,lswapstr pi v)::pi) u)`
        THEN1 SRW_TAC [][] THEN 
  SRW_TAC [][LAM_eq_thm, basic_swapTheory.lswapstr_APPEND] THENL [
    FULL_SIMP_TAC (srw_ss()) [],
    SRW_TAC [][tpm_eqr, tpm_flip_args, tpm_APPEND]
  ]); 

val tpm_subst = store_thm(
  "tpm_subst",
  ``!N. tpm pi ([M/v] N) = [tpm pi M/lswapstr pi v] (tpm pi N)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN 
  Q.EXISTS_TAC `v INSERT FV M` THEN 
  SRW_TAC [][SUB_THM, SUB_VAR]);

val tpm_subst_out = store_thm(
  "tpm_subst_out",
  ``[M/v] (tpm pi N) = 
       tpm pi ([tpm (REVERSE pi) M/lswapstr (REVERSE pi) v] N)``,
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

val lemma15a = store_thm(
  "lemma15a",
  ``!M. ~(v IN FV M) ==> ([N/v]([VAR v/x]M) = [N/x]M)``,
  HO_MATCH_MP_TAC nc_INDUCTION2 THEN Q.EXISTS_TAC `{x;v} UNION FV N` THEN 
  SRW_TAC [][SUB_THM, SUB_VAR]);

val lemma15b = store_thm(
  "lemma15b",
  ``~(v IN FV M) ==> ([VAR u/v]([VAR v/u] M) = M)``,
  SRW_TAC [][lemma15a]);


val _ = export_theory();

    
  
  
  
