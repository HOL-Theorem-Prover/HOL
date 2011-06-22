open HolKernel Parse boolLib bossLib stringLib

open pred_setTheory

open basic_swapTheory nomsetTheory NEWLib

val _ = new_theory "hol"

fun Store_thm (n,t,tac) = store_thm(n,t,tac) before export_rewrites [n]

(* a theory of higher order logic terms, as modelled in systems such as
   HOL4, Isabelle/HOL and HOL Light *)

(* HOL types *)

val _ = Hol_datatype `hol_type = tyvar of string
                               | tyop of string => hol_type list
`


(*

The big question is how to handle the fact that the binding unit is a
name coupled with a type, and not just a type.  If we define a raw type,
it has to be

*)

val _ = Hol_datatype`raw_holterm = rhvar of string # hol_type
                                 | rhconst of string # hol_type
                                 | rhapp of raw_holterm => raw_holterm
                                 | rhabs of string # hol_type => raw_holterm
`

(* but what is the appropriate notion of permutation on this type?

   It seems clear that it has to be the permutation of atoms that consist of
   names coupled with types *)

val rawpm_def = Define`
  (rawpm ty pi (rhvar nty) = if ty = SND nty then
                               rhvar (lswapstr pi (FST nty), SND nty)
                             else rhvar nty) /\
  (rawpm ty pi (rhconst nty) = rhconst nty) /\
  (rawpm ty pi (rhapp t1 t2) = rhapp (rawpm ty pi t1) (rawpm ty pi t2)) /\
  (rawpm ty pi (rhabs nty t) =
     rhabs (if ty = SND nty then (lswapstr pi (FST nty), SND nty)
            else nty)
           (rawpm ty pi t))
`;
val _ = export_rewrites ["rawpm_def"]

val rawpm_is_perm = Store_thm(
  "rawpm_is_perm",
  ``!ty. is_perm (rawpm ty)``,
  SRW_TAC [][is_perm_def] THENL [
    Induct_on `x` THEN SRW_TAC [][],
    Induct_on `x` THEN SRW_TAC [][lswapstr_APPEND] THEN
    FULL_SIMP_TAC (srw_ss()) [],
    FULL_SIMP_TAC (srw_ss()) [permeq_def, FUN_EQ_THM] THEN
    Induct THEN SRW_TAC [][]
  ]);

val rawpms_differing_types_commute = store_thm(
  "rawpms_differing_types_commute",
  ``~(ty1 = ty2) ==>
    (rawpm ty1 pi1 (rawpm ty2 pi2 t) =
     rawpm ty2 pi2 (rawpm ty1 pi1 t))``,
  Induct_on `t` THEN SRW_TAC [][] THEN METIS_TAC [])

val rawpm_nil = Store_thm(
  "rawpm_nil",
  ``rawpm ty [] t = t``,
  METIS_TAC [is_perm_nil, rawpm_is_perm]);

val rawpm_APPEND = store_thm(
  "rawpm_APPEND",
  ``rawpm ty p1 (rawpm ty p2 t) = rawpm ty (p1 ++ p2) t``,
  METIS_TAC [rawpm_is_perm, is_perm_decompose]);

val rawpm_inverse = Store_thm(
  "rawpm_inverse",
  ``(rawpm ty pi (rawpm ty (REVERSE pi) t) = t) /\
    (rawpm ty (REVERSE pi) (rawpm ty pi t) = t)``,
  METIS_TAC [rawpm_is_perm, is_perm_inverse]);

val rawpm_sing_inv = Store_thm(
  "rawpm_sing_inv",
  ``(rawpm ty [h] (rawpm ty [h] x) = x)``,
  METIS_TAC [rawpm_is_perm, is_perm_sing_inv]);

val rawpm_sing_to_back = store_thm(
  "rawpm_sing_to_back",
  ``rawpm ty [(lswapstr pi a, lswapstr pi b)] (rawpm ty pi t) =
    rawpm ty pi (rawpm ty [(a,b)] t)``,
  METIS_TAC [rawpm_is_perm, is_perm_sing_to_back]);

val allvars_def = Define`
  (allvars ty (rhvar nty) = if ty = SND nty then {FST nty} else {}) /\
  (allvars ty (rhconst nty) = {}) /\
  (allvars ty (rhapp t1 t2) = allvars ty t1 UNION allvars ty t2) /\
  (allvars ty (rhabs nty t) = (if ty = SND nty then {FST nty} else {}) UNION
                              allvars ty t)
`;
val _ = export_rewrites ["allvars_def"]

val IN_allvars_rawpm = Store_thm(
  "IN_allvars_rawpm",
  ``x IN allvars ty (rawpm ty pi t) =
    lswapstr (REVERSE pi) x IN allvars ty t``,
  Induct_on `t` THEN SRW_TAC [][lswapstr_eql] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val allvars_rawpm_diff = Store_thm(
  "allvars_rawpm_diff",
  ``~(ty1 = ty2) ==> (allvars ty1 (rawpm ty2 pi t) = allvars ty1 t)``,
  Induct_on `t` THEN SRW_TAC [][] THEN METIS_TAC []);

val FINITE_allvars = Store_thm(
  "FINITE_allvars",
  ``FINITE (allvars ty t)``,
  Induct_on `t` THEN SRW_TAC [][]);

val allvars_fresh = store_thm(
  "allvars_fresh",
  ``~(u IN allvars ty t) /\ ~(v IN allvars ty t) ==>
    (rawpm ty [(u,v)] t = t)``,
  Induct_on `t` THEN SRW_TAC [][]);

val (aeq_rules, aeq_ind, aeq_cases) = Hol_reln`
  (!v. aeq (rhvar v) (rhvar v)) /\
  (!v. aeq (rhconst v) (rhconst v)) /\
  (!t1 t2 u1 u2. aeq t1 u1 /\ aeq t2 u2 ==>
                 aeq (rhapp t1 t2) (rhapp u1 u2)) /\
  (!v1 v2 u t z.
      ~(z IN allvars ty t) /\ ~(z IN allvars ty u) /\ ~(z = v1) /\
      ~(z = v2) /\ aeq (rawpm ty [(z,v1)] t) (rawpm ty [(z,v2)] u) ==>
      aeq (rhabs (v1,ty) t) (rhabs (v2,ty) u))
`;

val aeq_rawpm = store_thm(
  "aeq_rawpm",
  ``!t u. aeq t u ==> !pi ty. aeq (rawpm ty pi t) (rawpm ty pi u)``,
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][aeq_rules] THEN
  Cases_on `ty = ty'` THENL [
    SRW_TAC [][] THEN
    MATCH_MP_TAC (last (CONJUNCTS aeq_rules)) THEN
    Q.EXISTS_TAC `lswapstr pi z` THEN SRW_TAC [][] THEN
    SRW_TAC [][is_perm_sing_to_back, rawpm_is_perm],
    SRW_TAC [][] THEN
    MATCH_MP_TAC (last (CONJUNCTS aeq_rules)) THEN
    SRW_TAC [][] THEN
    METIS_TAC [rawpms_differing_types_commute]
  ]);

val aeq_rawpml = store_thm(
  "aeq_rawpml",
  ``aeq (rawpm ty pi t1) t2 = aeq t1 (rawpm ty (REVERSE pi) t2)``,
  METIS_TAC [rawpm_inverse, aeq_rawpm]);

val aeq_refl = Store_thm(
  "aeq_refl",
  ``aeq t t``,
  Induct_on `t` THEN SRW_TAC [][aeq_rules] THEN
  Cases_on `p` THEN
  Q_TAC (NEW_TAC "z") `q INSERT allvars r t` THEN
  MATCH_MP_TAC (last (CONJUNCTS aeq_rules)) THEN
  Q.EXISTS_TAC `z` THEN SRW_TAC [][aeq_rawpm]);

val aeq_sym = store_thm(
  "aeq_sym",
  ``!t u. aeq t u ==> aeq u t``,
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][aeq_rules] THEN
  METIS_TAC [aeq_rules]);

val aeq_app = store_thm(
  "aeq_app",
  ``aeq (rhapp t u) z = ?z1 z2. (z = rhapp z1 z2) /\
                                aeq t z1 /\ aeq u z2``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [aeq_cases])) THEN
  SRW_TAC [][]);

val aeq_trans = store_thm(
  "aeq_trans",
  ``!s t u. aeq s t /\ aeq t u ==> aeq s u``,
  Q_TAC SUFF_TAC `!s t. aeq s t ==> !u. aeq t u ==> aeq s u`
        THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][aeq_rules, aeq_app] THEN
  POP_ASSUM MP_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [aeq_cases])) THEN
  SIMP_TAC (srw_ss()) [] THEN
  DISCH_THEN (Q.X_CHOOSE_THEN `v`
              (Q.X_CHOOSE_THEN `s`
               (Q.X_CHOOSE_THEN `z'` STRIP_ASSUME_TAC))) THEN
  SRW_TAC [][] THEN
  Q_TAC (NEW_TAC "d") `{v;v1;v2;z;z'} UNION allvars ty t UNION
                       allvars ty u UNION allvars ty s` THEN
  `!u'. aeq (rawpm ty [(d,z)] (rawpm ty [(z,v2)] u))
            (rawpm ty [(d,z)] u') ==>
        aeq (rawpm ty [(d,z)] (rawpm ty [(z,v1)] t))
            (rawpm ty [(d,z)] u')`
      by SRW_TAC [][aeq_rawpml] THEN
  POP_ASSUM (Q.SPEC_THEN `rawpm ty [(d,z)] u'`
             (ASSUME_TAC o Q.GEN `u'` o
              SIMP_RULE (srw_ss()) [])) THEN
  POP_ASSUM (MP_TAC o
             ONCE_REWRITE_RULE [GSYM rawpm_sing_to_back]) THEN
  SRW_TAC [][allvars_fresh] THEN
  `aeq (rawpm ty [(d,z')] (rawpm ty [(z',v2)] u))
       (rawpm ty [(d,z')] (rawpm ty [(z',v)] s))`
     by SRW_TAC [][Once aeq_rawpml] THEN
  POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM rawpm_sing_to_back]) THEN
  SRW_TAC [][allvars_fresh, swapstr_def] THEN
  METIS_TAC [aeq_rules]);

val fv_def = Define`
  (fv ty (rhvar nty) = if ty = SND nty then {FST nty} else {}) /\
  (fv ty (rhconst nty) = {}) /\
  (fv ty (rhapp t1 t2) = fv ty t1 UNION fv ty t2) /\
  (fv ty (rhabs nty t) =
       if ty = SND nty then fv ty t DELETE FST nty
       else fv ty t)
`;
val _ = export_rewrites ["fv_def"]

val fv_SUBSET_allvars = store_thm(
  "fv_SUBSET_allvars",
  ``!x. x IN fv ty t ==> x IN allvars ty t``,
  Induct_on `t` THEN SRW_TAC [][] THEN SRW_TAC [][]);

val IN_fv_rawpm = store_thm(
  "IN_fv_rawpm",
  ``x IN fv ty (rawpm ty pi t) = lswapstr (REVERSE pi) x IN fv ty t``,
  Induct_on `t` THEN SRW_TAC [][lswapstr_eql] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val fv_rawpm_diff = store_thm(
  "fv_rawpm_diff",
  ``~(ty = ty') ==> (fv ty (rawpm ty' pi t) = fv ty t)``,
  Induct_on `t` THEN SRW_TAC [][] THEN METIS_TAC []);


val aeq_fv = store_thm(
  "aeq_fv",
  ``!t u. aeq t u ==> !ty. fv ty t = fv ty u``,
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][EXTENSION] THEN
  COND_CASES_TAC THENL [
    SRW_TAC [][] THEN
    SRW_TAC [][EXTENSION] THEN
    POP_ASSUM (Q.SPEC_THEN `ty` MP_TAC) THEN
    Cases_on `x = v1` THENL [
      SRW_TAC [][] THEN
      POP_ASSUM (Q.SPEC_THEN `v1` MP_TAC) THEN
      SRW_TAC [][IN_fv_rawpm, swapstr_def] THEN METIS_TAC [fv_SUBSET_allvars],
      ALL_TAC
    ] THEN Cases_on `x = v2` THENL [
      SRW_TAC [][] THEN FIRST_X_ASSUM (Q.SPEC_THEN `v2` MP_TAC) THEN
      SRW_TAC [][IN_fv_rawpm, swapstr_def] THEN METIS_TAC [fv_SUBSET_allvars],
      ALL_TAC
    ] THEN
    Cases_on `z = x` THEN SRW_TAC [][] THENL [
      METIS_TAC [fv_SUBSET_allvars],
      FIRST_X_ASSUM (Q.SPEC_THEN `x` MP_TAC) THEN
      SRW_TAC [][IN_fv_rawpm, swapstr_def]
    ],
    SRW_TAC [][] THEN FIRST_X_ASSUM (Q.SPEC_THEN `ty'` MP_TAC) THEN
    SRW_TAC [][fv_rawpm_diff]
  ]);

val rhabs_respects_aeq = store_thm(
  "rhabs_respects_aeq",
  ``!t u. aeq t u ==> aeq (rhabs v t) (rhabs v u)``,
  SRW_TAC [][] THEN Cases_on `v` THEN
  MATCH_MP_TAC (last (CONJUNCTS aeq_rules)) THEN
  Q_TAC (NEW_TAC "z") `q INSERT allvars r t UNION allvars r u` THEN
  SRW_TAC [][aeq_rawpml] THEN METIS_TAC []);

val alt_aeq_lam = store_thm(
  "alt_aeq_lam",
  ``(!z. ~(z IN allvars ty t1) /\ ~(z IN allvars ty t2) /\ ~(z = u) /\
         ~(z = v) ==>
         aeq (rawpm ty [(u,z)] t1) (rawpm ty [(v,z)] t2)) ==>
    aeq (rhabs (u,ty) t1) (rhabs (v,ty) t2)``,
  STRIP_TAC THEN MATCH_MP_TAC (last (CONJUNCTS aeq_rules)) THEN
  Q_TAC (NEW_TAC "z") `allvars ty t1 UNION allvars ty t2 UNION {u;v}` THEN
  METIS_TAC [rawpm_is_perm, is_perm_flip_args]);

val fresh_swap = store_thm(
  "fresh_swap",
  ``!x y. ~(x IN fv ty t) /\ ~(y IN fv ty t) ==> aeq t (rawpm ty [(x,y)] t)``,
  Induct_on `t` THEN
  ASM_SIMP_TAC (srw_ss()) [aeq_rules, pairTheory.FORALL_PROD] THEN1
    SRW_TAC [][] THEN
  REPEAT GEN_TAC THEN Cases_on `ty = p_2` THENL [
    ASM_SIMP_TAC (srw_ss()) [] THEN
    DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
    MATCH_MP_TAC alt_aeq_lam THEN
    ASM_SIMP_TAC (srw_ss())[aeq_rawpml, IN_allvars_rawpm] THEN
    REPEAT STRIP_TAC THEN
    `~(z IN fv p_2 t)` by METIS_TAC [fv_SUBSET_allvars] THEN
    Cases_on `x = p_1` THEN ASM_SIMP_TAC (srw_ss()) [] THENL [
      FULL_SIMP_TAC (srw_ss()) [is_perm_id] THEN
      SRW_TAC [][] THEN
      Cases_on `y = p_1` THEN SRW_TAC [][] THEN
      CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV
                                        [GSYM rawpm_sing_to_back]))) THEN
      SRW_TAC [][],
      ALL_TAC
    ] THEN
    Cases_on `y = p_1` THEN SRW_TAC [][] THENL [
      FULL_SIMP_TAC (srw_ss()) [] THEN
      CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV
                                        [GSYM rawpm_sing_to_back]))) THEN
      SRW_TAC [][is_perm_flip_args, rawpm_is_perm],
      SRW_TAC [][]
    ],
    SRW_TAC [][rhabs_respects_aeq]
  ]);

val aeq_lam_eqn = store_thm(
  "aeq_lam_eqn",
  ``(aeq (rhabs (n1,ty1) t1) (rhabs (n2,ty2) t2)) =
      (ty1 = ty2) /\
      ((n1 = n2) /\ aeq t1 t2 \/
       ~(n1 = n2) /\ ~(n1 IN fv ty1 t2) /\ aeq t1 (rawpm ty1 [(n1,n2)] t2))``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, DISJ_IMP_THM] THEN REPEAT CONJ_TAC THENL [
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [aeq_cases])) THEN
    SRW_TAC [][] THEN
    `~(z IN fv ty1 t1) /\ ~(z IN fv ty1 t2)`
      by METIS_TAC [fv_SUBSET_allvars] THEN
    Cases_on `n1 = n2` THEN1 FULL_SIMP_TAC (srw_ss()) [aeq_rawpml] THEN
    `~(n1 IN fv ty1 t2)`
       by (STRIP_TAC THEN
           `n1 IN fv ty1 (rawpm ty1 [(z,n2)] t2)`
              by SRW_TAC [][IN_fv_rawpm] THEN
           `n1 IN fv ty1 (rawpm ty1 [(z,n1)] t1)` by METIS_TAC [aeq_fv] THEN
           FULL_SIMP_TAC (srw_ss()) [IN_fv_rawpm]) THEN
    FULL_SIMP_TAC (srw_ss()) [aeq_rawpml] THEN
    Q.PAT_ASSUM `aeq X Y` MP_TAC THEN
    ONCE_REWRITE_TAC [GSYM rawpm_sing_to_back] THEN
    SRW_TAC [][] THEN
    MATCH_MP_TAC aeq_trans THEN
    Q.EXISTS_TAC `rawpm ty1 [(n1,n2)] (rawpm ty1 [(z,n1)] t2)` THEN
    SRW_TAC [][] THEN
    SRW_TAC [][aeq_rawpml, fresh_swap],

    SRW_TAC [][] THENL [
      SRW_TAC [][rhabs_respects_aeq],
      MATCH_MP_TAC alt_aeq_lam THEN SRW_TAC [][aeq_rawpml] THEN
      ONCE_REWRITE_TAC [GSYM rawpm_sing_to_back] THEN
      SRW_TAC [][] THEN
      `~(z IN fv ty1 t2)` by METIS_TAC [fv_SUBSET_allvars] THEN
      MATCH_MP_TAC aeq_trans THEN
      Q.EXISTS_TAC `rawpm ty1 [(n1,n2)] t2` THEN SRW_TAC [][] THEN
      SRW_TAC [][is_perm_flip_args, rawpm_is_perm, fresh_swap,
                 aeq_rawpml]
    ]
  ]);

val aeq_equiv = prove(
  ``!t1 t2. aeq t1 t2 = (aeq t1 = aeq t2)``,
  SRW_TAC [][FUN_EQ_THM] THEN
  METIS_TAC [aeq_refl, aeq_sym, aeq_trans]);

fun mk_def(s,t) =
    {def_name = s ^ "_def", fixity = NONE, fname = s, func = t};


fun m th = SIMP_RULE (bool_ss ++ boolSimps.DNF_ss) [] th

val var_respects = prove(
  ``!v1 v2. (v1 = v2) ==> aeq (rhvar v1) (rhvar v2)``,
  SRW_TAC [][aeq_refl]);
val con_respects = prove(
  ``!nty1 nty2. (nty1 = nty2) ==> aeq (rhconst nty1) (rhconst nty2)``,
  SRW_TAC [][aeq_refl]);
val rhabs_respects = prove(
  ``!v1 v2 t1 t2. (v1 = v2) /\ aeq t1 t2 ==>
                  aeq (rhabs v1 t1) (rhabs v2 t2)``,
  SRW_TAC [][rhabs_respects_aeq]);

val finite_fv = prove(
  ``FINITE (fv ty t)``,
  METIS_TAC [SUBSET_FINITE, SUBSET_DEF, fv_SUBSET_allvars, FINITE_allvars]);

val aeq_fv' = prove(
  ``!ty1 ty2 t1 t2. (ty1 = ty2) /\ aeq t1 t2 ==>
                    (fv ty1 t1 = fv ty2 t2)``,
  SRW_TAC [][aeq_fv]);

val aeq_rawpm' = prove(
  ``!ty1 ty2 pi1 pi2 t u.
        (ty1 = ty2) /\ (pi1 = pi2) /\ aeq t u ==>
        aeq (rawpm ty1 pi1 t) (rawpm ty2 pi2 u)``,
  SRW_TAC [][aeq_rawpm]);

val [FV_thm, simple_induction, FINITE_FV, tpm_thm] =
    quotient.define_quotient_types_full {
      types = [{name = "term", equiv = aeq_equiv}],
      defs = map mk_def [("LAM", ``rhabs``), ("COMB", ``rhapp``),
                         ("VAR", ``rhvar``), ("CONST", ``rhconst``),
                         ("FV", ``fv``), ("tpm", ``rawpm``)],
      tyop_equivs = [],
      tyop_quotients = [],
      tyop_simps = [],
      poly_preserves = [],
      poly_respects = [],
      respects = [rhabs_respects, List.nth(CONJUNCTS aeq_rules, 2),
                  aeq_fv', aeq_rawpm', var_respects, con_respects],
      old_thms = [fv_def, TypeBase.induction_of ``:raw_holterm``,
                  finite_fv, rawpm_def]
}

val FV_thm = save_thm("FV_thm", FV_thm)
val _ = export_rewrites ["FV_thm"]
val simple_induction = save_thm("simple_induction", simple_induction)
val FINITE_FV = save_thm("FINITE_FV", FINITE_FV)
val _ = export_rewrites ["FINITE_FV"]
val tpm_thm = save_thm("tpm_thm", tpm_thm)
val _ = export_rewrites ["tpm_thm"]

val tpm_is_perm = Store_thm(
  "tpm_is_perm",
  ``is_perm (tpm ty)``,
  SRW_TAC [][is_perm_def] THENL [
    Q.ID_SPEC_TAC `x` THEN HO_MATCH_MP_TAC simple_induction THEN
    SRW_TAC [][],
    Q.ID_SPEC_TAC `x` THEN HO_MATCH_MP_TAC simple_induction THEN
    SRW_TAC [][lswapstr_APPEND] THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss()) [],
    FULL_SIMP_TAC (srw_ss()) [FUN_EQ_THM, permeq_def] THEN
    HO_MATCH_MP_TAC simple_induction THEN SRW_TAC [][]
  ]);

val _ = export_theory()




