open HolKernel Parse boolLib bossLib stringLib

open pred_setTheory

open basic_swapTheory nomsetTheory NEWLib

val _ = new_theory "hol"

(* a theory of higher order logic terms, as modelled in systems such as
   HOL4, Isabelle/HOL and HOL Light *)

(* HOL types *)

Datatype:
  hol_type = tyvar string
           | tyop string (hol_type list)
End


(*

The big question is how to handle the fact that the binding unit is a
name coupled with a type, and not just a type.  If we define a raw type,
it has to be

*)


Datatype:
  raw_holterm = rhvar (string # hol_type)
              | rhconst (string # hol_type)
              | rhapp raw_holterm raw_holterm
              | rhabs (string # hol_type) raw_holterm
End

(* but what is the appropriate notion of permutation on this type?

   It seems clear that it has to be the permutation of atoms that consist of
   names coupled with types *)

Definition rawpm_def[simp]:
  (rawpm ty pi (rhvar nty) = if ty = SND nty then
                               rhvar (lswapstr pi (FST nty), SND nty)
                             else rhvar nty) /\
  (rawpm ty pi (rhconst nty) = rhconst nty) /\
  (rawpm ty pi (rhapp t1 t2) = rhapp (rawpm ty pi t1) (rawpm ty pi t2)) /\
  (rawpm ty pi (rhabs nty t) =
     rhabs (if ty = SND nty then (lswapstr pi (FST nty), SND nty)
            else nty)
           (rawpm ty pi t))
End

Theorem rawpm_is_perm:
  !ty. is_pmact (rawpm ty)
Proof
  SRW_TAC [][is_pmact_def]
  >- (Induct_on `x` THEN SRW_TAC [][])
  >- (Induct_on `x` >> rw[pmact_decompose] >> gvs[]) >>
  simp[FUN_EQ_THM] >> Induct >> rw[] >>
  metis_tac[pmact_permeq]
QED

Overload rhpmact = “λty. mk_pmact (rawpm ty)”
Overload rhpm = “λty. pmact (rhpmact ty)”

Theorem rawpm_rhpm:
  rawpm ty = rhpm ty
Proof
  simp[GSYM pmact_bijections, rawpm_is_perm]
QED

Theorem rhpm_thm[simp] = ONCE_REWRITE_RULE [rawpm_rhpm] rawpm_def

Theorem rawpms_differing_types_commute:
  ty1 ≠ ty2 ==>
  rhpm ty1 pi1 (rhpm ty2 pi2 t) = rhpm ty2 pi2 (rhpm ty1 pi1 t)
Proof
  Induct_on `t` THEN SRW_TAC [][] THEN METIS_TAC []
QED

Definition allvars_def[simp]:
  (allvars ty (rhvar nty) = if ty = SND nty then {FST nty} else {}) /\
  (allvars ty (rhconst nty) = {}) /\
  (allvars ty (rhapp t1 t2) = allvars ty t1 UNION allvars ty t2) /\
  (allvars ty (rhabs nty t) = (if ty = SND nty then {FST nty} else {}) UNION
                              allvars ty t)
End

Theorem IN_allvars_rawpm[simp]:
  x IN allvars ty (rhpm ty pi t) <=>
  lswapstr (REVERSE pi) x IN allvars ty t
Proof
  Induct_on `t` >> simp[] >> rw[] >> SRW_TAC [][pmact_eql] >> gs[]
QED

Theorem allvars_rawpm_diff[simp]:
  ty1 ≠ ty2 ==> allvars ty1 (rhpm ty2 pi t) = allvars ty1 t
Proof
  Induct_on `t` THEN SRW_TAC [][] THEN METIS_TAC []
QED

Theorem FINITE_allvars[simp]:
  FINITE (allvars ty t)
Proof
  Induct_on `t` THEN SRW_TAC [][]
QED

Theorem allvars_fresh:
  u ∉ allvars ty t ∧ v ∉ allvars ty t ⇒ rhpm ty [(u,v)] t = t
Proof
  Induct_on `t` THEN SRW_TAC [][]
QED

Inductive aeq:
[~var:]
  (!v. aeq (rhvar v) (rhvar v))
[~const:]
  (!v. aeq (rhconst v) (rhconst v))
[~app:]
  (!t1 t2 u1 u2. aeq t1 u1 /\ aeq t2 u2 ==>
                 aeq (rhapp t1 t2) (rhapp u1 u2))
[~lam:]
  (!v1 v2 u t z ty.
      ~(z IN allvars ty t) /\ ~(z IN allvars ty u) /\ ~(z = v1) /\
      ~(z = v2) /\ aeq (rhpm ty [(z,v1)] t) (rhpm ty [(z,v2)] u) ==>
      aeq (rhabs (v1,ty) t) (rhabs (v2,ty) u))
End

Theorem aeq_rawpm:
  !t u. aeq t u ==> !pi ty. aeq (rhpm ty pi t) (rhpm ty pi u)
Proof
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][aeq_rules] THEN
  Cases_on `ty = ty'`
  >- (rw[] >> irule aeq_lam >>
      qexists ‘lswapstr pi z’ >> rw[pmact_sing_to_back]) >>
  rw[] >> irule aeq_lam >> rw[] >>
  metis_tac [rawpms_differing_types_commute]
QED

Theorem aeq_rawpml:
  aeq (rhpm ty pi t1) t2 = aeq t1 (rhpm ty (REVERSE pi) t2)
Proof
  METIS_TAC [pmact_inverse, aeq_rawpm]
QED

Theorem aeq_refl[simp]:
  aeq t t
Proof
  Induct_on `t` THEN SRW_TAC [][aeq_rules] THEN
  Cases_on `p` THEN
  Q_TAC (NEW_TAC "z") `q INSERT allvars r t` THEN
  MATCH_MP_TAC aeq_lam THEN
  Q.EXISTS_TAC `z` THEN SRW_TAC [][aeq_rawpm]
QED

val aeq_sym = store_thm(
  "aeq_sym",
  ``!t u. aeq t u ==> aeq u t``,
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][aeq_rules] THEN
  METIS_TAC [aeq_rules]);

val aeq_app_rwt = store_thm(
  "aeq_app_rwt",
  ``aeq (rhapp t u) z = ?z1 z2. (z = rhapp z1 z2) /\
                                aeq t z1 /\ aeq u z2``,
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [aeq_cases])) THEN
  SRW_TAC [][]);

Theorem aeq_trans:
  !s t u. aeq s t /\ aeq t u ==> aeq s u
Proof
  Induct_on ‘aeq’ >>
  rw[aeq_rules, aeq_app_rwt] >>
  POP_ASSUM MP_TAC THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [aeq_cases])) THEN
  SIMP_TAC (srw_ss()) [] THEN
  DISCH_THEN (Q.X_CHOOSE_THEN `v`
              (Q.X_CHOOSE_THEN `s`
               (Q.X_CHOOSE_THEN `z'` STRIP_ASSUME_TAC))) THEN
  SRW_TAC [][] THEN
  Q_TAC (NEW_TAC "d") `{v;v1;v2;z;z'} UNION allvars ty t UNION
                       allvars ty u UNION allvars ty s` THEN
  ‘!u'. aeq (rhpm ty [(d,z)] (rhpm ty [(z,v2)] u))
            (rhpm ty [(d,z)] u') ==>
        aeq (rhpm ty [(d,z)] (rhpm ty [(z,v1)] t))
            (rhpm ty [(d,z)] u')’
      by SRW_TAC [][aeq_rawpml] THEN
  POP_ASSUM (Q.SPEC_THEN `rhpm ty [(d,z)] u'`
             (ASSUME_TAC o Q.GEN `u'` o
              SIMP_RULE (srw_ss()) [])) THEN
  POP_ASSUM (MP_TAC o
             ONCE_REWRITE_RULE [GSYM pmact_sing_to_back]) THEN
  SRW_TAC [][allvars_fresh] THEN
  ‘aeq (rhpm ty [(d,z')] (rhpm ty [(z',v2)] u))
       (rhpm ty [(d,z')] (rhpm ty [(z',v)] s))’
     by SRW_TAC [][Once aeq_rawpml] THEN
  POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [GSYM pmact_sing_to_back]) THEN
  SRW_TAC [][allvars_fresh] THEN
  METIS_TAC [aeq_rules]
QED

Definition fv_def[simp]:
  (fv ty (rhvar nty) = if ty = SND nty then {FST nty} else {}) /\
  (fv ty (rhconst nty) = {}) /\
  (fv ty (rhapp t1 t2) = fv ty t1 UNION fv ty t2) /\
  (fv ty (rhabs nty t) =
       if ty = SND nty then fv ty t DELETE FST nty
       else fv ty t)
End

Theorem fv_SUBSET_allvars:
  !x. x IN fv ty t ==> x IN allvars ty t
Proof
  Induct_on `t` THEN SRW_TAC [][] THEN SRW_TAC [][]
QED

val IN_fv_rawpm = store_thm(
  "IN_fv_rawpm",
  ``x IN fv ty (rhpm ty pi t) ⇔ lswapstr (REVERSE pi) x IN fv ty t``,
  Induct_on `t` THEN SRW_TAC [][pmact_eql] THEN
  FULL_SIMP_TAC (srw_ss()) []);

val fv_rawpm_diff = store_thm(
  "fv_rawpm_diff",
  ``~(ty = ty') ==> (fv ty (rhpm ty' pi t) = fv ty t)``,
  Induct_on `t` THEN SRW_TAC [][] THEN METIS_TAC []);

Theorem aeq_fv:
  !t u. aeq t u ==> !ty. fv ty t = fv ty u
Proof
  HO_MATCH_MP_TAC aeq_ind THEN SRW_TAC [][EXTENSION] THEN
  COND_CASES_TAC THENL [
    SRW_TAC [][] THEN
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
  ]
QED

Theorem rhabs_respects_aeq:
  !t u. aeq t u ==> aeq (rhabs v t) (rhabs v u)
Proof
  SRW_TAC [][] THEN Cases_on `v` THEN
  MATCH_MP_TAC (last (CONJUNCTS aeq_rules)) THEN
  Q_TAC (NEW_TAC "z") `q INSERT allvars r t UNION allvars r u` THEN
  SRW_TAC [][aeq_rawpml] THEN METIS_TAC []
QED

Theorem alt_aeq_lam:
  (!z. ~(z IN allvars ty t1) /\ ~(z IN allvars ty t2) /\ ~(z = u) /\
       ~(z = v) ==>
       aeq (rhpm ty [(u,z)] t1) (rhpm ty [(v,z)] t2)) ==>
  aeq (rhabs (u,ty) t1) (rhabs (v,ty) t2)
Proof
  STRIP_TAC THEN MATCH_MP_TAC (last (CONJUNCTS aeq_rules)) THEN
  Q_TAC (NEW_TAC "z") `allvars ty t1 UNION allvars ty t2 UNION {u;v}` THEN
  METIS_TAC [rawpm_is_perm, pmact_flip_args]
QED

Theorem fresh_swap:
  !x y. x ∉ fv ty t ∧ y ∉ fv ty t ⇒ aeq t (rhpm ty [(x,y)] t)
Proof
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
      FULL_SIMP_TAC (srw_ss()) [pmact_id] THEN
      SRW_TAC [][] THEN
      Cases_on `y = p_1` THEN SRW_TAC [][] THEN
      CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV
                                        [GSYM pmact_sing_to_back]))) THEN
      SRW_TAC [][],
      ALL_TAC
    ] THEN
    Cases_on `y = p_1` THEN SRW_TAC [][] THENL [
      FULL_SIMP_TAC (srw_ss()) [] THEN
      CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV
                                        [GSYM pmact_sing_to_back]))) THEN
      SRW_TAC [][pmact_flip_args],
      SRW_TAC [][]
    ],
    SRW_TAC [][rhabs_respects_aeq]
  ]
QED

Theorem aeq_lam_eqn:
  aeq (rhabs (n1,ty1) t1) (rhabs (n2,ty2) t2) ⇔
    ty1 = ty2 ∧
    (n1 = n2 ∧ aeq t1 t2 \/
     n1 ≠ n2 ∧ n1 ∉ fv ty1 t2 ∧ aeq t1 (rhpm ty1 [(n1,n2)] t2))
Proof
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, DISJ_IMP_THM] THEN REPEAT CONJ_TAC THENL [
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [aeq_cases])) THEN
    SRW_TAC [][] THEN
    `~(z IN fv ty1 t1) /\ ~(z IN fv ty1 t2)`
      by METIS_TAC [fv_SUBSET_allvars] THEN
    Cases_on `n1 = n2` THEN1 FULL_SIMP_TAC (srw_ss()) [aeq_rawpml] THEN
    `~(n1 IN fv ty1 t2)`
       by (STRIP_TAC THEN
           `n1 IN fv ty1 (rhpm ty1 [(z,n2)] t2)`
              by SRW_TAC [][IN_fv_rawpm] THEN
           `n1 IN fv ty1 (rhpm ty1 [(z,n1)] t1)` by METIS_TAC [aeq_fv] THEN
           FULL_SIMP_TAC (srw_ss()) [IN_fv_rawpm]) THEN
    FULL_SIMP_TAC (srw_ss()) [aeq_rawpml] THEN
    Q.PAT_X_ASSUM `aeq X Y` MP_TAC THEN
    ONCE_REWRITE_TAC [GSYM pmact_sing_to_back] THEN
    SRW_TAC [][] THEN
    MATCH_MP_TAC aeq_trans THEN
    Q.EXISTS_TAC `rhpm ty1 [(n1,n2)] (rhpm ty1 [(z,n1)] t2)` THEN
    SRW_TAC [][] THEN
    SRW_TAC [][aeq_rawpml, fresh_swap],

    SRW_TAC [][] THENL [
      SRW_TAC [][rhabs_respects_aeq],
      MATCH_MP_TAC alt_aeq_lam THEN SRW_TAC [][aeq_rawpml] THEN
      ONCE_REWRITE_TAC [GSYM pmact_sing_to_back] THEN
      SRW_TAC [][] THEN
      `~(z IN fv ty1 t2)` by METIS_TAC [fv_SUBSET_allvars] THEN
      MATCH_MP_TAC aeq_trans THEN
      Q.EXISTS_TAC `rhpm ty1 [(n1,n2)] t2` THEN SRW_TAC [][] THEN
      SRW_TAC [][pmact_flip_args, fresh_swap, aeq_rawpml]
    ]
  ]
QED

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

val aeq_rawpm0 = prove(
  ``!ty1 ty2 pi1 pi2 t u.
        (ty1 = ty2) /\ (pi1 = pi2) /\ aeq t u ==>
        aeq (rhpm ty1 pi1 t) (rhpm ty2 pi2 u)``,
  SRW_TAC [][aeq_rawpm]);

val aeq_rawpm' = SRULE [GSYM rawpm_rhpm] aeq_rawpm0

val [FV_thm, simple_induction, FINITE_FV, raw_tpm_thm(*, tpm_is_pmact*)] =
    quotient.define_quotient_types_full {
      types = [{name = "term", equiv = aeq_equiv}],
      defs = map mk_def [("LAM", ``rhabs``), ("COMB", ``rhapp``),
                         ("VAR", ``rhvar``), ("CONST", ``rhconst``),
                         ("FV", ``fv``), ("raw_tpm", ``rawpm``)],
      tyop_equivs = [],
      tyop_quotients = [],
      tyop_simps = [],
      poly_preserves = [],
      poly_respects = [],
      respects = [rhabs_respects, List.nth(CONJUNCTS aeq_rules, 2),
                  aeq_fv', aeq_rawpm', var_respects, con_respects],
      old_thms = [fv_def, TypeBase.induction_of ``:raw_holterm``,
                  finite_fv, rawpm_def(*, rawpm_is_perm*)]
}

Theorem FV_thm[simp] = FV_thm
Theorem simple_induction = simple_induction
Theorem FINITE_FV[simp] = FINITE_FV
Theorem raw_tpm_thm[simp] = raw_tpm_thm

Theorem tpm_is_perm:
  is_pmact (raw_tpm ty)
Proof
  SRW_TAC [][is_pmact_def] THENL [
    Q.ID_SPEC_TAC `x` THEN HO_MATCH_MP_TAC simple_induction THEN
    SRW_TAC [][],
    Q.ID_SPEC_TAC `x` THEN HO_MATCH_MP_TAC simple_induction THEN
    SRW_TAC [][pmact_decompose] THEN SRW_TAC [][] THEN
    gs[],
    simp[FUN_EQ_THM] >> Induct using simple_induction >>
    SRW_TAC [][] >> metis_tac[pmact_permeq]
  ]
QED

val _ = export_theory()




