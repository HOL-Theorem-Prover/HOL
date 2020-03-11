open HolKernel Parse boolLib bossLib;

open full_ltlTheory arithmeticTheory automaton_formulaTheory xprop_logicTheory prop_logicTheory
     infinite_pathTheory symbolic_semi_automatonTheory listTheory pred_setTheory
     rich_listTheory pairTheory numLib listLib rltlTheory computeLib relationTheory
     tuerk_tacticsLib congLib Travrules congToolsLibTheory

open Sanity;

val _ = new_theory "temporal_deep_simplificationsLib";
val _ = ParseExtras.temp_loose_equality()

val PROP_LOGIC_EQUIVALENT_LIST_AS_SET_def = Define
   `PROP_LOGIC_EQUIVALENT_LIST_AS_SET =
         LIST_AS_SET_CONGRUENCE_RELATION PROP_LOGIC_EQUIVALENT`;

Theorem PROP_LOGIC_EQUIVALENT_REFL :
    !x. PROP_LOGIC_EQUIVALENT x x
Proof
    SIMP_TAC std_ss [PROP_LOGIC_EQUIVALENT_def]
QED

Theorem PROP_LOGIC_EQUIVALENT_TRANS :
    !x y z. PROP_LOGIC_EQUIVALENT x y /\ PROP_LOGIC_EQUIVALENT y z ==>
            PROP_LOGIC_EQUIVALENT x z
Proof
    SIMP_TAC std_ss [PROP_LOGIC_EQUIVALENT_def]
QED

val PROP_LOGIC_EQUIVALENT_STATE = Define
   `PROP_LOGIC_EQUIVALENT_STATE s p1 p2 = (P_SEM s p1 = P_SEM s p2)`;

val PROP_LOGIC_EQUIVALENT_congs =
  store_thm (
    "PROP_LOGIC_EQUIVALENT_congs",

    ``(!p1 p1'. PROP_LOGIC_EQUIVALENT p1 p1' ==>
                (P_IS_CONTRADICTION p1 = P_IS_CONTRADICTION p1')) /\
      (!p1 p1'. PROP_LOGIC_EQUIVALENT p1 p1' ==>
                (P_IS_TAUTOLOGY p1 = P_IS_TAUTOLOGY p1')) /\
      (!p1 p1' p2 p2'. PROP_LOGIC_EQUIVALENT p1 p1' ==>
                       PROP_LOGIC_EQUIVALENT p2 p2' ==>
                (PROP_LOGIC_EQUIVALENT p1 p2 = PROP_LOGIC_EQUIVALENT p1' p2')) /\
      (!p p' s s'. PROP_LOGIC_EQUIVALENT p p' ==>
                   (s = s') ==>
                   (P_SEM s p = P_SEM s' p')) /\
      (!p1 p1'. PROP_LOGIC_EQUIVALENT p1 p1' ==>
                PROP_LOGIC_EQUIVALENT (P_NOT p1) (P_NOT p1')) /\
      (!p1 p2 p1' p2'. PROP_LOGIC_EQUIVALENT p1 p1' ==>
                       PROP_LOGIC_EQUIVALENT p2 p2' ==>
                       ((PROP_LOGIC_EQUIVALENT p1 p2) = (PROP_LOGIC_EQUIVALENT p1' p2'))) /\
      (!p1 p2 p1' p2'. PROP_LOGIC_EQUIVALENT p1 p1' ==>
                       PROP_LOGIC_EQUIVALENT p2 p2' ==>
                       PROP_LOGIC_EQUIVALENT (P_AND(p1, p2)) (P_AND(p1', p2'))) /\
      (!p1 p2 p1' p2'. PROP_LOGIC_EQUIVALENT p1 p1' ==>
                       PROP_LOGIC_EQUIVALENT p2 p2' ==>
                       PROP_LOGIC_EQUIVALENT (P_OR(p1, p2)) (P_OR(p1', p2'))) /\
      (!p1 p2 p1' p2'. PROP_LOGIC_EQUIVALENT p1 p1' ==>
                       PROP_LOGIC_EQUIVALENT p2 p2' ==>
                       PROP_LOGIC_EQUIVALENT (P_IMPL(p1, p2)) (P_IMPL(p1', p2'))) /\
      (!c c' p1 p2 p1' p2'.
                       PROP_LOGIC_EQUIVALENT c c' ==>
                       PROP_LOGIC_EQUIVALENT p1 p1' ==>
                       PROP_LOGIC_EQUIVALENT p2 p2' ==>
                       PROP_LOGIC_EQUIVALENT (P_COND(c, p1, p2)) (P_COND(c', p1', p2'))) /\
      (!p1 p2 p1' p2'. PROP_LOGIC_EQUIVALENT p1 p1' ==>
                       PROP_LOGIC_EQUIVALENT p2 p2' ==>
                       PROP_LOGIC_EQUIVALENT (P_EQUIV(p1, p2)) (P_EQUIV(p1', p2'))) /\

      (!p1 p1' l l'. PROP_LOGIC_EQUIVALENT p1 p1' ==>
                     (l = l') ==>
                     (PROP_LOGIC_EQUIVALENT (P_FORALL l p1)
                                            (P_FORALL l' p1'))) /\
      (!p1 p1' l l'. PROP_LOGIC_EQUIVALENT p1 p1' ==>
                     (l = l') ==>
                     (PROP_LOGIC_EQUIVALENT (P_EXISTS l p1)
                                            (P_EXISTS l' p1'))) /\
      (!p p' f. PROP_LOGIC_EQUIVALENT p p' ==>
                PROP_LOGIC_EQUIVALENT (P_VAR_RENAMING f p) (P_VAR_RENAMING f p'))``,

    SIMP_TAC std_ss [PROP_LOGIC_EQUIVALENT_def, P_SEM_THM,
                     P_SEM___VAR_RENAMING___NOT_INJ, P_IS_CONTRADICTION_def,
                     P_IS_TAUTOLOGY_def,
                     P_FORALL_SEM, P_EXISTS_SEM]);


val PROP_LOGIC_EQUIVALENT_list_congs =
  store_thm (
    "PROP_LOGIC_EQUIVALENT_list_congs",

    ``(!l l'. PROP_LOGIC_EQUIVALENT_LIST_AS_SET l l' ==>
              PROP_LOGIC_EQUIVALENT (P_BIGAND l) (P_BIGAND l')) /\
      (!l l'. PROP_LOGIC_EQUIVALENT_LIST_AS_SET l l' ==>
              PROP_LOGIC_EQUIVALENT (P_BIGOR l) (P_BIGOR l'))``,

    REWRITE_TAC[PROP_LOGIC_EQUIVALENT_LIST_AS_SET_def] THEN
    REPEAT STRIP_TAC THEN (
      Induct_on `l` THEN Induct_on `l'` THENL [
        REWRITE_TAC[PROP_LOGIC_EQUIVALENT_REFL],
        REWRITE_TAC[LIST_AS_SET_CONGRUENCE_RELATION_REWRITES],
        REWRITE_TAC[LIST_AS_SET_CONGRUENCE_RELATION_REWRITES],

        FULL_SIMP_TAC list_ss [LIST_AS_SET_CONGRUENCE_RELATION_def,
          PROP_LOGIC_EQUIVALENT_def, P_BIGAND_SEM, P_BIGOR_SEM] THEN
        METIS_TAC[]
      ]
    ));



val PROP_LOGIC_EQUIVALENT_rewrites =
  store_thm (
    "PROP_LOGIC_EQUIVALENT_rewrites",

    ``(PROP_LOGIC_EQUIVALENT (P_NOT P_TRUE) P_FALSE) /\
      (PROP_LOGIC_EQUIVALENT (P_NOT P_FALSE) P_TRUE) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_NOT(P_NOT p)) p) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_AND(p, p)) p) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_OR(p, p)) p) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_AND(p, P_NOT p)) P_FALSE) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_AND(P_NOT p, p)) P_FALSE) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_OR(p, P_NOT p)) P_TRUE) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_OR(P_NOT p, p)) P_TRUE) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_AND(p, P_TRUE)) p) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_AND(p, P_FALSE)) P_FALSE) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_OR(p, P_FALSE)) p) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_OR(p, P_TRUE)) P_TRUE) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_AND(P_TRUE, p)) p) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_AND(P_FALSE, p)) P_FALSE) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_OR(P_FALSE, p)) p) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_OR(P_TRUE, p)) P_TRUE) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_IMPL(P_FALSE, p)) P_TRUE) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_IMPL(P_TRUE, p)) p) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_IMPL(p, p)) P_TRUE) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_IMPL(p, P_NOT p)) (P_NOT p)) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_IMPL(P_NOT p, p)) p) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_IMPL(p, P_FALSE)) (P_NOT p)) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_IMPL(p, P_TRUE)) P_TRUE) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_EQUIV(p, p)) P_TRUE) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_EQUIV(p, P_NOT p)) P_FALSE) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_EQUIV(P_NOT p, p)) P_FALSE) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_EQUIV(p, P_FALSE)) (P_NOT p)) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_EQUIV(p, P_TRUE)) p) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_EQUIV(P_FALSE, p)) (P_NOT p)) /\
      (!p. PROP_LOGIC_EQUIVALENT (P_EQUIV(P_TRUE, p)) p) /\

      (!p1 p2 p3. PROP_LOGIC_EQUIVALENT (P_AND(P_AND(p1, p2), p3)) (P_AND(p1, P_AND(p2, p3)))) /\
      (!p1 p2 p3. PROP_LOGIC_EQUIVALENT (P_OR(P_OR(p1, p2), p3)) (P_OR(p1, P_OR(p2, p3)))) /\
      (!p1 p2. PROP_LOGIC_EQUIVALENT (P_AND(p1, P_AND(P_NOT p1, p2))) P_FALSE) /\
      (!p1 p2. PROP_LOGIC_EQUIVALENT (P_AND(p1, P_AND(p2, P_NOT p1))) P_FALSE) /\
      (!p1 p2. PROP_LOGIC_EQUIVALENT (P_AND(p1, P_AND(p1, p2))) (P_AND(p1,p2))) /\
      (!p1 p2. PROP_LOGIC_EQUIVALENT (P_AND(p1, P_AND(p2, p1))) (P_AND(p1,p2))) /\
      (!p1 p2. PROP_LOGIC_EQUIVALENT (P_OR(p1, P_OR(P_NOT p1, p2))) P_TRUE) /\
      (!p1 p2. PROP_LOGIC_EQUIVALENT (P_OR(p1, P_OR(p2, P_NOT p1))) P_TRUE) /\
      (!p1 p2. PROP_LOGIC_EQUIVALENT (P_OR(p1, P_OR(p1, p2))) (P_OR(p1,p2))) /\
      (!p1 p2. PROP_LOGIC_EQUIVALENT (P_OR(p1, P_OR(p2, p1))) (P_OR(p1,p2))) /\
      (!p1 p2. PROP_LOGIC_EQUIVALENT (P_COND(P_FALSE, p1, p2)) p2) /\
      (!p1 p2. PROP_LOGIC_EQUIVALENT (P_COND(P_TRUE, p1, p2)) p1) /\
      (!p1 p2 c. PROP_LOGIC_EQUIVALENT (P_COND(P_NOT c, p1, p2))
                                       (P_COND(c, p2, p1))) /\


      (!p. (PROP_LOGIC_EQUIVALENT (P_NOT p) P_FALSE) = (PROP_LOGIC_EQUIVALENT p P_TRUE)) /\
      (!p. (PROP_LOGIC_EQUIVALENT (P_NOT p) P_TRUE) = (PROP_LOGIC_EQUIVALENT p P_FALSE)) /\
      (!p. (PROP_LOGIC_EQUIVALENT P_FALSE (P_NOT p)) = (PROP_LOGIC_EQUIVALENT p P_TRUE)) /\
      (!p. (PROP_LOGIC_EQUIVALENT P_TRUE (P_NOT p)) = (PROP_LOGIC_EQUIVALENT p P_FALSE)) /\

      (!c p p1 p2.
      PROP_LOGIC_EQUIVALENT (P_COND (c, P_EQUIV (p, p1), P_EQUIV (p, p2)))     (P_EQUIV (p, (P_COND (c, p1,p2))))) /\
      (!c p p1 p2.
      PROP_LOGIC_EQUIVALENT (P_COND (c, P_EQUIV (p1, p), P_EQUIV (p2, p)))     (P_EQUIV ((P_COND (c, p1,p2)), p))) /\

      (!c p p1 p2.
      PROP_LOGIC_EQUIVALENT (P_COND (c, P_AND (p, p1), P_AND (p, p2)))
      (P_AND (p, (P_COND (c, p1,p2))))) /\
      (!c p p1 p2.
      PROP_LOGIC_EQUIVALENT (P_COND (c, P_AND (p1, p), P_AND (p2, p)))
      (P_AND ((P_COND (c, p1,p2)), p))) /\

      (!c p1 p2.
      PROP_LOGIC_EQUIVALENT (P_COND (c, P_NOT p1, P_NOT p2))
                             (P_NOT (P_COND(c, p1, p2)))) /\

      (!c p p1 p2.
      PROP_LOGIC_EQUIVALENT (P_COND (c, P_OR (p, p1), P_OR (p, p2)))
      (P_OR (p, (P_COND (c, p1,p2))))) /\
      (!c p p1 p2.
      PROP_LOGIC_EQUIVALENT (P_COND (c, P_OR (p1, p), P_OR (p2, p)))
      (P_OR ((P_COND (c, p1,p2)), p))) /\

      (!c p p1 p2.
      PROP_LOGIC_EQUIVALENT (P_COND (c, P_IMPL (p, p1), P_IMPL (p, p2)))
      (P_IMPL (p, (P_COND (c, p1,p2))))) /\
      (!c p p1 p2.
      PROP_LOGIC_EQUIVALENT (P_COND (c, P_IMPL (p1, p), P_IMPL (p2, p)))
      (P_IMPL ((P_COND (c, p1,p2)), p)))
      ``,

    SIMP_TAC std_ss [PROP_LOGIC_EQUIVALENT_def, P_SEM_THM] THEN
    REPEAT STRIP_TAC THEN METIS_TAC[]);




val PROP_LOGIC_EQUIVALENT___EXISTS___rewrites =
  store_thm (
    "PROP_LOGIC_EQUIVALENT___EXISTS___rewrites",

    ``(!l:'a list. (PROP_LOGIC_EQUIVALENT (P_EXISTS l P_TRUE) P_TRUE)) /\
      (!l:'a list. (PROP_LOGIC_EQUIVALENT (P_EXISTS l P_FALSE) P_FALSE)) /\

      (!p. (PROP_LOGIC_EQUIVALENT (P_EXISTS [] p) p)) /\
      (!l:'a list p1 p2. (PROP_LOGIC_EQUIVALENT (P_EXISTS l (P_OR (p1, p2))) (P_OR (P_EXISTS l p1, P_EXISTS l p2))))``,

      SIMP_TAC std_ss [PROP_LOGIC_EQUIVALENT_def, P_EXISTS_def,
        GSYM FORALL_AND_THM] THEN
      Induct_on `l` THENL [
        SIMP_TAC std_ss [P_EXISTS_def],

        ASM_SIMP_TAC std_ss [P_EXISTS_def, P_SEM_THM, P_ASSIGN_TRUE_FALSE___EVAL] THEN
        PROVE_TAC[]
      ]);



val PROP_LOGIC_EQUIVALENT_nnf_rewrites =
  store_thm (
    "PROP_LOGIC_EQUIVALENT_nnf_rewrites",

    ``(!p1 p2. PROP_LOGIC_EQUIVALENT (P_NOT (P_AND(p1, p2))) (P_OR (P_NOT p1, P_NOT p2))) /\
      (!p1 p2. PROP_LOGIC_EQUIVALENT (P_NOT (P_OR(p1, p2))) (P_AND (P_NOT p1, P_NOT p2))) /\
      (!p1 p2. PROP_LOGIC_EQUIVALENT (P_NOT (P_IMPL(p1, p2))) (P_AND (p1, P_NOT p2))) /\
      (!p1 p2 c. PROP_LOGIC_EQUIVALENT (P_NOT (P_COND(c, p1, p2))) (P_COND(c, P_NOT p1, P_NOT p2))) /\
      (!p1 p2. PROP_LOGIC_EQUIVALENT (P_NOT (P_EQUIV(p1, p2))) (P_EQUIV (P_NOT p1, p2)))``,

    SIMP_TAC std_ss [PROP_LOGIC_EQUIVALENT_def, P_SEM_THM] THEN
    METIS_TAC[]);


val PROP_LOGIC_EQUIVALENT_dnf_rewrites =
  store_thm (
    "PROP_LOGIC_EQUIVALENT_dnf_rewrites",
      ``(!p1 p2 p3. PROP_LOGIC_EQUIVALENT (P_AND (P_OR(p1, p2), p3)) (P_OR (P_AND (p1, p3), P_AND (p2, p3)))) /\
        (!p1 p2 p3. PROP_LOGIC_EQUIVALENT (P_AND (p3, P_OR(p1, p2))) (P_OR (P_AND (p1, p3), P_AND (p2, p3))))``,

    SIMP_TAC std_ss [PROP_LOGIC_EQUIVALENT_def, P_SEM_THM] THEN
    METIS_TAC[]);

val LIST_AS_SET_CONGRUENCE_RELATION___PROP_LOGIC_EQUIVALENT_def =
    Define
     `LIST_AS_SET_CONGRUENCE_RELATION___PROP_LOGIC_EQUIVALENT =
      LIST_AS_SET_CONGRUENCE_RELATION PROP_LOGIC_EQUIVALENT`;

val XPROP_LOGIC_EQUIVALENT_LIST_AS_SET_def =
  Define `XPROP_LOGIC_EQUIVALENT_LIST_AS_SET =
          LIST_AS_SET_CONGRUENCE_RELATION XPROP_LOGIC_EQUIVALENT`

val XPROP_LOGIC_EQUIVALENT_REFL =
  store_thm (
    "XPROP_LOGIC_EQUIVALENT_REFL",

    ``!x. XPROP_LOGIC_EQUIVALENT x x``,

    SIMP_TAC std_ss [XPROP_LOGIC_EQUIVALENT_def]);

val XPROP_LOGIC_EQUIVALENT_TRANS =
  store_thm (
    "XPROP_LOGIC_EQUIVALENT_TRANS",

    ``!x y z. (XPROP_LOGIC_EQUIVALENT x y /\ XPROP_LOGIC_EQUIVALENT y z) ==>
              XPROP_LOGIC_EQUIVALENT x z``,

    SIMP_TAC std_ss [XPROP_LOGIC_EQUIVALENT_def]);



val XPROP_LOGIC_EQUIVALENT_congs =
  store_thm (
    "XPROP_LOGIC_EQUIVALENT_congs",

    ``(!p1 p1' p2 p2'. XPROP_LOGIC_EQUIVALENT p1 p1' ==>
                       XPROP_LOGIC_EQUIVALENT p2 p2' ==>
                (XPROP_LOGIC_EQUIVALENT p1 p2 = XPROP_LOGIC_EQUIVALENT p1' p2')) /\
      (!p p' s1 s2 s1' s2'. XPROP_LOGIC_EQUIVALENT p p' ==>
                   (s1 = s1') ==>
                   (s2 = s2') ==>
                   (XP_SEM p (s1, s2) = XP_SEM p' (s1', s2'))) /\
      (!p1 p1'. XPROP_LOGIC_EQUIVALENT p1 p1' ==>
                XPROP_LOGIC_EQUIVALENT (XP_NOT p1) (XP_NOT p1')) /\
      (!p1 p2 p1' p2'. XPROP_LOGIC_EQUIVALENT p1 p1' ==>
                       XPROP_LOGIC_EQUIVALENT p2 p2' ==>
                       ((XPROP_LOGIC_EQUIVALENT p1 p2) = (XPROP_LOGIC_EQUIVALENT p1' p2'))) /\
      (!p1 p2 p1' p2'. XPROP_LOGIC_EQUIVALENT p1 p1' ==>
                       XPROP_LOGIC_EQUIVALENT p2 p2' ==>
                       XPROP_LOGIC_EQUIVALENT (XP_AND(p1, p2)) (XP_AND(p1', p2'))) /\
      (!p1 p2 p1' p2'. XPROP_LOGIC_EQUIVALENT p1 p1' ==>
                       XPROP_LOGIC_EQUIVALENT p2 p2' ==>
                       XPROP_LOGIC_EQUIVALENT (XP_OR(p1, p2)) (XP_OR(p1', p2'))) /\
      (!p1 p2 p1' p2'. XPROP_LOGIC_EQUIVALENT p1 p1' ==>
                       XPROP_LOGIC_EQUIVALENT p2 p2' ==>
                       XPROP_LOGIC_EQUIVALENT (XP_IMPL(p1, p2)) (XP_IMPL(p1', p2'))) /\
      (!c c' p1 p2 p1' p2'.
                       XPROP_LOGIC_EQUIVALENT c c' ==>
                       XPROP_LOGIC_EQUIVALENT p1 p1' ==>
                       XPROP_LOGIC_EQUIVALENT p2 p2' ==>
                       XPROP_LOGIC_EQUIVALENT (XP_COND(c, p1, p2)) (XP_COND(c', p1', p2'))) /\
      (!p1 p2 p1' p2'. XPROP_LOGIC_EQUIVALENT p1 p1' ==>
                       XPROP_LOGIC_EQUIVALENT p2 p2' ==>
                       XPROP_LOGIC_EQUIVALENT (XP_EQUIV(p1, p2)) (XP_EQUIV(p1', p2'))) /\
      (!p1 p1'. PROP_LOGIC_EQUIVALENT p1 p1' ==>
                XPROP_LOGIC_EQUIVALENT (XP_NEXT p1) (XP_NEXT p1')) /\
      (!p1 p1'. PROP_LOGIC_EQUIVALENT p1 p1' ==>
                XPROP_LOGIC_EQUIVALENT (XP_CURRENT p1) (XP_CURRENT p1')) /\
      (!p1 p1' l l'.
                XPROP_LOGIC_EQUIVALENT p1 p1' ==>
                (l = l') ==>
                XPROP_LOGIC_EQUIVALENT (XP_NEXT_EXISTS l p1) (XP_NEXT_EXISTS l' p1')) /\
      (!p1 p1' l l'.
                XPROP_LOGIC_EQUIVALENT p1 p1' ==>
                (l = l') ==>
                XPROP_LOGIC_EQUIVALENT (XP_CURRENT_EXISTS l p1) (XP_CURRENT_EXISTS l' p1')) /\
      (!p1 p1' l l'.
                XPROP_LOGIC_EQUIVALENT p1 p1' ==>
                (l = l') ==>
                XPROP_LOGIC_EQUIVALENT (XP_NEXT_FORALL l p1) (XP_NEXT_FORALL l' p1')) /\
      (!p1 p1' l l'.
                XPROP_LOGIC_EQUIVALENT p1 p1' ==>
                (l = l') ==>
                XPROP_LOGIC_EQUIVALENT (XP_CURRENT_FORALL l p1) (XP_CURRENT_FORALL l' p1')) /\
      (!p p' f. XPROP_LOGIC_EQUIVALENT p p' ==>
                XPROP_LOGIC_EQUIVALENT (XP_VAR_RENAMING f p) (XP_VAR_RENAMING f p'))``,

    SIMP_TAC std_ss [XPROP_LOGIC_EQUIVALENT_def, XP_SEM_THM, XP_SEM___VAR_RENAMING___NOT_INJ, PROP_LOGIC_EQUIVALENT_def,
    XP_SEM___XP_NEXT, XP_SEM___XP_CURRENT,
    XP_NEXT_EXISTS_SEM, XP_NEXT_FORALL_SEM, XP_CURRENT_EXISTS_SEM,
    XP_CURRENT_FORALL_SEM]);



val XPROP_LOGIC_EQUIVALENT___EXISTS___basic_rewrites =
  prove (
    ``(!l:'a list. (XPROP_LOGIC_EQUIVALENT (XP_NEXT_EXISTS l XP_TRUE) XP_TRUE)) /\
      (!l:'a list. (XPROP_LOGIC_EQUIVALENT (XP_NEXT_EXISTS l XP_FALSE) XP_FALSE)) /\

      (!p. (XPROP_LOGIC_EQUIVALENT (XP_NEXT_EXISTS [] p) p)) /\
      (!l:'a list p1 p2. (XPROP_LOGIC_EQUIVALENT (XP_NEXT_EXISTS l (XP_OR (p1, p2))) (XP_OR (XP_NEXT_EXISTS l p1, XP_NEXT_EXISTS l p2)))) /\

      (!l:'a list. (XPROP_LOGIC_EQUIVALENT (XP_CURRENT_EXISTS l XP_TRUE) XP_TRUE)) /\
      (!l:'a list. (XPROP_LOGIC_EQUIVALENT (XP_CURRENT_EXISTS l XP_FALSE) XP_FALSE)) /\

      (!p. (XPROP_LOGIC_EQUIVALENT (XP_CURRENT_EXISTS [] p) p)) /\
      (!l:'a list p1 p2. (XPROP_LOGIC_EQUIVALENT (XP_CURRENT_EXISTS l (XP_OR (p1, p2))) (XP_OR (XP_CURRENT_EXISTS l p1, XP_CURRENT_EXISTS l p2))))``,

      SIMP_TAC std_ss [XPROP_LOGIC_EQUIVALENT_def, XP_CURRENT_EXISTS_def,
        XP_NEXT_EXISTS_def, GSYM FORALL_AND_THM] THEN
      Induct_on `l` THENL [
        SIMP_TAC std_ss [XP_CURRENT_EXISTS_def, XP_NEXT_EXISTS_def],

        ASM_SIMP_TAC std_ss [XP_CURRENT_EXISTS_def, XP_NEXT_EXISTS_def, XP_SEM_THM, XP_ASSIGN_TRUE_FALSE___EVAL] THEN
        PROVE_TAC[]
      ]);


val XPROP_LOGIC_EQUIVALENT___EXISTS___assign_rewrites =
  prove (``!V1 V2 V1' V2' p.
      XPROP_LOGIC_EQUIVALENT (XP_ASSIGN_TRUE V1 V2 (XP_ASSIGN_TRUE V1' V2' p))
                            (XP_ASSIGN_TRUE (V1 UNION V1') (V2 UNION V2') p) /\
      XPROP_LOGIC_EQUIVALENT (XP_ASSIGN_FALSE V1 V2 (XP_ASSIGN_FALSE V1' V2' p))
                            (XP_ASSIGN_FALSE (V1 UNION V1') (V2 UNION V2') p)``,

  SIMP_TAC std_ss [XPROP_LOGIC_EQUIVALENT_def, XP_ASSIGN_TRUE_SEM, XP_ASSIGN_FALSE_SEM, UNION_ASSOC] THEN
  REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN
  SIMP_TAC std_ss [EXTENSION, IN_DIFF, IN_UNION] THEN
  METIS_TAC[]);


val XPROP_LOGIC_EQUIVALENT___EXISTS___assign_exists_rewrites =
  prove (``
!l V p.
XPROP_LOGIC_EQUIVALENT (XP_ASSIGN_TRUE EMPTY V (XP_CURRENT_EXISTS l p))
                       (XP_CURRENT_EXISTS l (XP_ASSIGN_TRUE EMPTY V p)) /\
XPROP_LOGIC_EQUIVALENT (XP_ASSIGN_FALSE EMPTY V (XP_CURRENT_EXISTS l p))
                       (XP_CURRENT_EXISTS l (XP_ASSIGN_FALSE EMPTY V p)) /\
XPROP_LOGIC_EQUIVALENT (XP_ASSIGN_TRUE V EMPTY (XP_NEXT_EXISTS l p))
                       (XP_NEXT_EXISTS l (XP_ASSIGN_TRUE V EMPTY p)) /\
XPROP_LOGIC_EQUIVALENT (XP_ASSIGN_FALSE V EMPTY (XP_NEXT_EXISTS l p))
                       (XP_NEXT_EXISTS l (XP_ASSIGN_FALSE V EMPTY p))``,

SIMP_TAC std_ss [XPROP_LOGIC_EQUIVALENT_def] THEN
Induct_on `l` THENL [
  SIMP_TAC std_ss [XP_CURRENT_EXISTS_def, XP_NEXT_EXISTS_def],

  ASM_SIMP_TAC std_ss [XP_CURRENT_EXISTS_def, XP_ASSIGN_TRUE_FALSE___EVAL,
    XP_CURRENT_EXISTS_SEM, XP_SEM_THM, XP_ASSIGN_TRUE_SEM,
    XP_ASSIGN_FALSE_SEM, UNION_EMPTY, DIFF_EMPTY, XP_NEXT_EXISTS_SEM]
]);


val XPROP_LOGIC_EQUIVALENT___EXISTS___rewrites =
  save_thm ("XPROP_LOGIC_EQUIVALENT___EXISTS___rewrites",
            LIST_CONJ [XPROP_LOGIC_EQUIVALENT___EXISTS___basic_rewrites,
                       XPROP_LOGIC_EQUIVALENT___EXISTS___assign_rewrites,
                       XPROP_LOGIC_EQUIVALENT___EXISTS___assign_exists_rewrites])



val XPROP_LOGIC_EQUIVALENT_list_congs =
  store_thm (
    "XPROP_LOGIC_EQUIVALENT_list_congs",

    ``(!l l'. XPROP_LOGIC_EQUIVALENT_LIST_AS_SET l l' ==>
              XPROP_LOGIC_EQUIVALENT (XP_BIGAND l) (XP_BIGAND l')) /\
      (!l l'. XPROP_LOGIC_EQUIVALENT_LIST_AS_SET l l' ==>
              XPROP_LOGIC_EQUIVALENT (XP_BIGOR l) (XP_BIGOR l'))``,

    REWRITE_TAC[XPROP_LOGIC_EQUIVALENT_LIST_AS_SET_def] THEN
    REPEAT STRIP_TAC THEN (
      Induct_on `l` THEN Induct_on `l'` THENL [
        REWRITE_TAC[XPROP_LOGIC_EQUIVALENT_REFL],
        REWRITE_TAC[LIST_AS_SET_CONGRUENCE_RELATION_REWRITES],
        REWRITE_TAC[LIST_AS_SET_CONGRUENCE_RELATION_REWRITES],

        FULL_SIMP_TAC list_ss [LIST_AS_SET_CONGRUENCE_RELATION_def,
          XPROP_LOGIC_EQUIVALENT_def, XP_BIGAND_SEM, XP_BIGOR_SEM] THEN
        METIS_TAC[]
      ]
    ));


val XPROP_LOGIC_EQUIVALENT_rewrites =
  store_thm (
    "XPROP_LOGIC_EQUIVALENT_rewrites",

    ``(XPROP_LOGIC_EQUIVALENT (XP_NOT XP_TRUE) XP_FALSE) /\
      (XPROP_LOGIC_EQUIVALENT (XP_NOT XP_FALSE) XP_TRUE) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_NOT(XP_NOT p)) p) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_AND(p, p)) p) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_OR(p, p)) p) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_AND(p, XP_NOT p)) XP_FALSE) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_AND(XP_NOT p, p)) XP_FALSE) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_OR(p, XP_NOT p)) XP_TRUE) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_OR(XP_NOT p, p)) XP_TRUE) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_AND(p, XP_TRUE)) p) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_AND(p, XP_FALSE)) XP_FALSE) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_OR(p, XP_FALSE)) p) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_OR(p, XP_TRUE)) XP_TRUE) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_AND(XP_TRUE, p)) p) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_AND(XP_FALSE, p)) XP_FALSE) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_OR(XP_FALSE, p)) p) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_OR(XP_TRUE, p)) XP_TRUE) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_IMPL(XP_FALSE, p)) XP_TRUE) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_IMPL(XP_TRUE, p)) p) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_IMPL(p, p)) XP_TRUE) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_IMPL(p, XP_NOT p)) (XP_NOT p)) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_IMPL(XP_NOT p, p)) p) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_IMPL(p, XP_FALSE)) (XP_NOT p)) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_IMPL(p, XP_TRUE)) XP_TRUE) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_EQUIV(p, p)) XP_TRUE) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_EQUIV(p, XP_NOT p)) XP_FALSE) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_EQUIV(XP_NOT p, p)) XP_FALSE) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_EQUIV(p, XP_FALSE)) (XP_NOT p)) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_EQUIV(p, XP_TRUE)) p) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_EQUIV(XP_FALSE, p)) (XP_NOT p)) /\
      (!p. XPROP_LOGIC_EQUIVALENT (XP_EQUIV(XP_TRUE, p)) p) /\
      (!p1 p2 p3. XPROP_LOGIC_EQUIVALENT (XP_AND(XP_AND(p1, p2), p3)) (XP_AND(p1, XP_AND(p2, p3)))) /\
      (!p1 p2 p3. XPROP_LOGIC_EQUIVALENT (XP_OR(XP_OR(p1, p2), p3)) (XP_OR(p1, XP_OR(p2, p3)))) /\
      (!p1 p2. XPROP_LOGIC_EQUIVALENT (XP_AND(p1, XP_AND(XP_NOT p1, p2))) XP_FALSE) /\
      (!p1 p2. XPROP_LOGIC_EQUIVALENT (XP_AND(p1, XP_AND(p2, XP_NOT p1))) XP_FALSE) /\
      (!p1 p2. XPROP_LOGIC_EQUIVALENT (XP_AND(p1, XP_AND(p1, p2))) (XP_AND(p1,p2))) /\
      (!p1 p2. XPROP_LOGIC_EQUIVALENT (XP_AND(p1, XP_AND(p2, p1))) (XP_AND(p1,p2))) /\
      (!p1 p2. XPROP_LOGIC_EQUIVALENT (XP_OR(p1, XP_OR(XP_NOT p1, p2))) XP_TRUE) /\
      (!p1 p2. XPROP_LOGIC_EQUIVALENT (XP_OR(p1, XP_OR(p2, XP_NOT p1))) XP_TRUE) /\
      (!p1 p2. XPROP_LOGIC_EQUIVALENT (XP_OR(p1, XP_OR(p1, p2))) (XP_OR(p1,p2))) /\
      (!p1 p2. XPROP_LOGIC_EQUIVALENT (XP_OR(p1, XP_OR(p2, p1))) (XP_OR(p1,p2))) /\
      (!p1 p2. XPROP_LOGIC_EQUIVALENT (XP_COND(XP_FALSE, p1, p2)) p2) /\
      (!p1 p2. XPROP_LOGIC_EQUIVALENT (XP_COND(XP_TRUE, p1, p2)) p1) /\
      (!p1 p2 c. XPROP_LOGIC_EQUIVALENT (XP_COND(XP_NOT c, p1, p2))
                                        (XP_COND(c, p2, p1))) /\

      (!c p p1 p2.
      XPROP_LOGIC_EQUIVALENT (XP_COND (c, XP_EQUIV (p, p1), XP_EQUIV (p, p2)))     (XP_EQUIV (p, (XP_COND (c, p1,p2))))) /\
      (!c p p1 p2.
      XPROP_LOGIC_EQUIVALENT (XP_COND (c, XP_EQUIV (p1, p), XP_EQUIV (p2, p)))     (XP_EQUIV ((XP_COND (c, p1,p2)), p))) /\

      (!c p p1 p2.
      XPROP_LOGIC_EQUIVALENT (XP_COND (c, XP_AND (p, p1), XP_AND (p, p2)))
      (XP_AND (p, (XP_COND (c, p1,p2))))) /\
      (!c p p1 p2.
      XPROP_LOGIC_EQUIVALENT (XP_COND (c, XP_AND (p1, p), XP_AND (p2, p)))
      (XP_AND ((XP_COND (c, p1,p2)), p))) /\

      (!c p1 p2.
      XPROP_LOGIC_EQUIVALENT (XP_COND (c, XP_NOT p1, XP_NOT p2))
                             (XP_NOT (XP_COND(c, p1, p2)))) /\

      (!c p p1 p2.
      XPROP_LOGIC_EQUIVALENT (XP_COND (c, XP_OR (p, p1), XP_OR (p, p2)))
      (XP_OR (p, (XP_COND (c, p1,p2))))) /\
      (!c p p1 p2.
      XPROP_LOGIC_EQUIVALENT (XP_COND (c, XP_OR (p1, p), XP_OR (p2, p)))
      (XP_OR ((XP_COND (c, p1,p2)), p))) /\

      (!c p p1 p2.
      XPROP_LOGIC_EQUIVALENT (XP_COND (c, XP_IMPL (p, p1), XP_IMPL (p, p2)))
      (XP_IMPL (p, (XP_COND (c, p1,p2))))) /\
      (!c p p1 p2.
      XPROP_LOGIC_EQUIVALENT (XP_COND (c, XP_IMPL (p1, p), XP_IMPL (p2, p)))
      (XP_IMPL ((XP_COND (c, p1,p2)), p)))``,

    SIMP_TAC std_ss [XPROP_LOGIC_EQUIVALENT_def, XP_SEM_THM] THEN
    METIS_TAC[]);



val XPROP_LOGIC_EQUIVALENT_nnf_rewrites =
  store_thm (
    "XPROP_LOGIC_EQUIVALENT_nnf_rewrites",

    ``(!p1 p2. XPROP_LOGIC_EQUIVALENT (XP_NOT (XP_AND(p1, p2))) (XP_OR (XP_NOT p1, XP_NOT p2))) /\
      (!p1 p2. XPROP_LOGIC_EQUIVALENT (XP_NOT (XP_OR(p1, p2))) (XP_AND (XP_NOT p1, XP_NOT p2))) /\
      (!p1 p2. XPROP_LOGIC_EQUIVALENT (XP_NOT (XP_IMPL(p1, p2))) (XP_AND (p1, XP_NOT p2))) /\
      (!p1 p2 c. XPROP_LOGIC_EQUIVALENT (XP_NOT (XP_COND(c, p1, p2))) (XP_COND(c, XP_NOT p1, XP_NOT p2))) /\
      (!p1 p2. XPROP_LOGIC_EQUIVALENT (XP_NOT (XP_EQUIV(p1, p2))) (XP_EQUIV (XP_NOT p1, p2)))``,

    SIMP_TAC std_ss [XPROP_LOGIC_EQUIVALENT_def, XP_SEM_THM] THEN
    METIS_TAC[]);


val XPROP_LOGIC_EQUIVALENT_dnf_rewrites =
  store_thm (
    "XPROP_LOGIC_EQUIVALENT_dnf_rewrites",
      ``(!p1 p2 p3. XPROP_LOGIC_EQUIVALENT (XP_AND (XP_OR(p1, p2), p3)) (XP_OR (XP_AND (p1, p3), XP_AND (p2, p3)))) /\
        (!p1 p2 p3. XPROP_LOGIC_EQUIVALENT (XP_AND (p3, XP_OR(p1, p2))) (XP_OR (XP_AND (p1, p3), XP_AND (p2, p3))))``,

    SIMP_TAC std_ss [XPROP_LOGIC_EQUIVALENT_def, XP_SEM_THM] THEN
    METIS_TAC[]);

val LTL_EQUIVALENT_REFL =
  store_thm (
    "LTL_EQUIVALENT_REFL",

    ``!x. LTL_EQUIVALENT x x``,

    SIMP_TAC std_ss [LTL_EQUIVALENT_def]);

val LTL_EQUIVALENT_TRANS =
  store_thm (
    "LTL_EQUIVALENT_TRANS",

    ``!x y z. (LTL_EQUIVALENT x y /\ LTL_EQUIVALENT y z) ==>
              LTL_EQUIVALENT x z``,

    SIMP_TAC std_ss [LTL_EQUIVALENT_def]);



val LTL_EQUIVALENT_congs =
  store_thm (
    "LTL_EQUIVALENT_congs",

    ``(!l1 l1'. LTL_EQUIVALENT l1 l1' ==>
                (LTL_IS_CONTRADICTION l1 = LTL_IS_CONTRADICTION l1')) /\
      (!l1 l1' l2 l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       (LTL_EQUIVALENT_INITIAL l1 l2 =
                        LTL_EQUIVALENT_INITIAL l1' l2')) /\
      (!l1 l1'. LTL_EQUIVALENT l1 l1' ==>
                (LTL_IS_TAUTOLOGY l1 = LTL_IS_TAUTOLOGY l1')) /\
      (!l1 l1'. LTL_EQUIVALENT l1 l1' ==>
                LTL_EQUIVALENT (LTL_NOT l1) (LTL_NOT l1')) /\
      (!l t w l' t' w'. LTL_EQUIVALENT l l' ==>
                        (t = t') ==>
                        (w = w') ==>
                       ((LTL_SEM_TIME t w l) = (LTL_SEM_TIME t' w' l'))) /\
      (!l w l' w'. LTL_EQUIVALENT l l' ==>
                   (w = w') ==>
                   ((LTL_SEM w l) = (LTL_SEM w' l'))) /\
      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       ((LTL_EQUIVALENT l1 l2) = (LTL_EQUIVALENT l1' l2'))) /\
      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_AND(l1, l2)) (LTL_AND(l1', l2'))) /\
      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_OR(l1, l2)) (LTL_OR(l1', l2'))) /\
      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_IMPL(l1, l2)) (LTL_IMPL(l1', l2'))) /\
      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_EQUIV(l1, l2)) (LTL_EQUIV(l1', l2'))) /\

      (!p p'.          PROP_LOGIC_EQUIVALENT p p' ==>
                       LTL_EQUIVALENT (LTL_PROP p) (LTL_PROP p')) /\
      (!l     l'     . LTL_EQUIVALENT l l' ==>
                       LTL_EQUIVALENT (LTL_NEXT l) (LTL_NEXT l')) /\
      (!l     l'     . LTL_EQUIVALENT l l' ==>
                       LTL_EQUIVALENT (LTL_PSNEXT l) (LTL_PSNEXT l')) /\
      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_SUNTIL(l1, l2)) (LTL_SUNTIL(l1', l2'))) /\
      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_PSUNTIL(l1, l2)) (LTL_PSUNTIL(l1', l2'))) /\
      (!l     l'     . LTL_EQUIVALENT l l' ==>
                       LTL_EQUIVALENT (LTL_ALWAYS l) (LTL_ALWAYS l')) /\
      (!l     l'     . LTL_EQUIVALENT l l' ==>
                       LTL_EQUIVALENT (LTL_EVENTUAL l) (LTL_EVENTUAL l')) /\
      (!l     l'     . LTL_EQUIVALENT l l' ==>
                       LTL_EQUIVALENT (LTL_PALWAYS l) (LTL_PALWAYS l')) /\
      (!l     l'     . LTL_EQUIVALENT l l' ==>
                       LTL_EQUIVALENT (LTL_PEVENTUAL l) (LTL_PEVENTUAL l')) /\
      (!l     l'     . LTL_EQUIVALENT l l' ==>
                       LTL_EQUIVALENT (LTL_PNEXT l) (LTL_PNEXT l')) /\

      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_UNTIL(l1, l2)) (LTL_UNTIL(l1', l2'))) /\

      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_BEFORE(l1, l2)) (LTL_BEFORE(l1', l2'))) /\

      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_SBEFORE(l1, l2)) (LTL_SBEFORE(l1', l2'))) /\
      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_WHILE(l1, l2)) (LTL_WHILE(l1', l2'))) /\
      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_SWHILE(l1, l2)) (LTL_SWHILE(l1', l2'))) /\

      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_PUNTIL(l1, l2)) (LTL_PUNTIL(l1', l2'))) /\

      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_PBEFORE(l1, l2)) (LTL_PBEFORE(l1', l2'))) /\

      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_PSBEFORE(l1, l2)) (LTL_PSBEFORE(l1', l2'))) /\
      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_PWHILE(l1, l2)) (LTL_PWHILE(l1', l2'))) /\
      (!l1 l2 l1' l2'. LTL_EQUIVALENT l1 l1' ==>
                       LTL_EQUIVALENT l2 l2' ==>
                       LTL_EQUIVALENT (LTL_PSWHILE(l1, l2)) (LTL_PSWHILE(l1', l2'))) /\
      (!l l' f. LTL_EQUIVALENT l l' ==>
                LTL_EQUIVALENT (LTL_VAR_RENAMING f l) (LTL_VAR_RENAMING f l'))``,

    SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_SEM_THM,
                     PROP_LOGIC_EQUIVALENT_def,
                     LTL_UNTIL_def, LTL_BEFORE_def,
                     LTL_SBEFORE_def, LTL_WHILE_def,
                     LTL_SWHILE_def, LTL_PUNTIL_def, LTL_PBEFORE_def,
                     LTL_PSBEFORE_def, LTL_PWHILE_def,
                     LTL_PSWHILE_def,
                     LTL_SEM_TIME___VAR_RENAMING___NOT_INJ,
                     LTL_IS_TAUTOLOGY_def, LTL_IS_CONTRADICTION_def,
                     LTL_EQUIVALENT_INITIAL_def]);

val LTL_EQUIVALENT_bool_rewrites =
  store_thm (
    "LTL_EQUIVALENT_bool_rewrites",

    ``(LTL_EQUIVALENT (LTL_NOT LTL_TRUE) LTL_FALSE) /\
      (LTL_EQUIVALENT (LTL_NOT LTL_FALSE) LTL_TRUE) /\
      (!l. LTL_EQUIVALENT (LTL_NOT(LTL_NOT l)) l) /\
      (!l. LTL_EQUIVALENT (LTL_AND(l, l)) l) /\
      (!l. LTL_EQUIVALENT (LTL_OR(l, l)) l) /\
      (!l. LTL_EQUIVALENT (LTL_AND(l, LTL_NOT l)) LTL_FALSE) /\
      (!l. LTL_EQUIVALENT (LTL_AND(LTL_NOT l, l)) LTL_FALSE) /\
      (!l. LTL_EQUIVALENT (LTL_OR(l, LTL_NOT l)) LTL_TRUE) /\
      (!l. LTL_EQUIVALENT (LTL_OR(LTL_NOT l, l)) LTL_TRUE) /\
      (!l. LTL_EQUIVALENT (LTL_AND(l, LTL_TRUE)) l) /\
      (!l. LTL_EQUIVALENT (LTL_AND(l, LTL_FALSE)) LTL_FALSE) /\
      (!l. LTL_EQUIVALENT (LTL_OR(l, LTL_FALSE)) l) /\
      (!l. LTL_EQUIVALENT (LTL_OR(LTL_TRUE, l)) LTL_TRUE) /\
      (!l. LTL_EQUIVALENT (LTL_AND(LTL_TRUE, l)) l) /\
      (!l. LTL_EQUIVALENT (LTL_AND(LTL_FALSE, l)) LTL_FALSE) /\
      (!l. LTL_EQUIVALENT (LTL_OR(LTL_FALSE, l)) l) /\
      (!l. LTL_EQUIVALENT (LTL_OR(LTL_TRUE, l)) LTL_TRUE) /\
      (!l. LTL_EQUIVALENT (LTL_IMPL(LTL_FALSE, l)) LTL_TRUE) /\
      (!l. LTL_EQUIVALENT (LTL_IMPL(LTL_TRUE, l)) l) /\
      (!l. LTL_EQUIVALENT (LTL_IMPL(l, l)) LTL_TRUE) /\
      (!l. LTL_EQUIVALENT (LTL_IMPL(l, LTL_NOT l)) (LTL_NOT l)) /\
      (!l. LTL_EQUIVALENT (LTL_IMPL(LTL_NOT l, l)) l) /\
      (!l. LTL_EQUIVALENT (LTL_IMPL(l, LTL_FALSE)) (LTL_NOT l)) /\
      (!l. LTL_EQUIVALENT (LTL_IMPL(l, LTL_TRUE)) LTL_TRUE) /\
      (!l. LTL_EQUIVALENT (LTL_EQUIV(l, l)) LTL_TRUE) /\
      (!l. LTL_EQUIVALENT (LTL_EQUIV(l, LTL_NOT l)) LTL_FALSE) /\
      (!l. LTL_EQUIVALENT (LTL_EQUIV(LTL_NOT l, l)) LTL_FALSE) /\
      (!l. LTL_EQUIVALENT (LTL_EQUIV(l, LTL_FALSE)) (LTL_NOT l)) /\
      (!l. LTL_EQUIVALENT (LTL_EQUIV(l, LTL_TRUE)) l) /\
      (!l. LTL_EQUIVALENT (LTL_EQUIV(LTL_FALSE, l)) (LTL_NOT l)) /\
      (!l. LTL_EQUIVALENT (LTL_EQUIV(LTL_TRUE, l)) l) /\
      (!p. LTL_EQUIVALENT (LTL_NOT(LTL_PROP p)) (LTL_PROP (P_NOT p))) /\
      (!p1 p2. LTL_EQUIVALENT (LTL_AND(LTL_PROP p1, LTL_PROP p2)) (LTL_PROP (P_AND (p1, p2)))) /\
      (!p1 p2. LTL_EQUIVALENT (LTL_OR(LTL_PROP p1, LTL_PROP p2)) (LTL_PROP (P_OR (p1, p2)))) /\
      (!p1 p2. LTL_EQUIVALENT (LTL_IMPL(LTL_PROP p1, LTL_PROP p2)) (LTL_PROP (P_IMPL (p1, p2)))) /\
      (!p1 p2. LTL_EQUIVALENT (LTL_EQUIV(LTL_PROP p1, LTL_PROP p2)) (LTL_PROP (P_EQUIV (p1, p2)))) /\
      (!l1 l2 l3. LTL_EQUIVALENT (LTL_AND(LTL_AND(l1, l2), l3)) (LTL_AND(l1, LTL_AND(l2, l3)))) /\
      (!l1 l2 l3. LTL_EQUIVALENT (LTL_OR(LTL_OR(l1, l2), l3)) (LTL_OR(l1, LTL_OR(l2, l3)))) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_AND(l1, LTL_AND(LTL_NOT l1, l2))) LTL_FALSE) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_AND(l1, LTL_AND(l2, LTL_NOT l1))) LTL_FALSE) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_AND(l1, LTL_AND(l1, l2))) (LTL_AND(l1,l2))) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_AND(l1, LTL_AND(l2, l1))) (LTL_AND(l1,l2))) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_OR(l1, LTL_OR(LTL_NOT l1, l2))) LTL_TRUE) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_OR(l1, LTL_OR(l2, LTL_NOT l1))) LTL_TRUE) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_OR(l1, LTL_OR(l1, l2))) (LTL_OR(l1,l2))) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_OR(l1, LTL_OR(l2, l1))) (LTL_OR(l1,l2)))``,

    REWRITE_TAC[LTL_EQUIVALENT_def, LTL_SEM_THM, P_SEM_THM] THEN
    SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_SEM_THM, P_SEM_THM] THEN
    METIS_TAC[]);



val LTL_EQUIVALENT_simple_nnf_rewrites =
  prove(
    ``(!l. LTL_EQUIVALENT (LTL_NOT(LTL_ALWAYS l)) (LTL_EVENTUAL (LTL_NOT l))) /\
      (!l. LTL_EQUIVALENT (LTL_NOT(LTL_EVENTUAL l)) (LTL_ALWAYS (LTL_NOT l))) /\
      (!l. LTL_EQUIVALENT (LTL_NOT(LTL_PALWAYS l)) (LTL_PEVENTUAL (LTL_NOT l))) /\
      (!l. LTL_EQUIVALENT (LTL_NOT(LTL_PEVENTUAL l)) (LTL_PALWAYS (LTL_NOT l))) /\
      (!l. LTL_EQUIVALENT (LTL_NOT(LTL_NEXT l)) (LTL_NEXT (LTL_NOT l))) /\
      (!l. LTL_EQUIVALENT (LTL_NOT(LTL_PSNEXT l)) (LTL_PNEXT (LTL_NOT l))) /\
      (!l. LTL_EQUIVALENT (LTL_NOT(LTL_PNEXT l)) (LTL_PSNEXT (LTL_NOT l))) /\

      (!l1 l2. LTL_EQUIVALENT (LTL_NOT(LTL_AND (l1, l2))) (LTL_OR (LTL_NOT l1, LTL_NOT l2))) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_NOT(LTL_OR (l1, l2))) (LTL_AND (LTL_NOT l1, LTL_NOT l2))) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_NOT(LTL_EQUIV (l1, l2))) (LTL_EQUIV (LTL_NOT l1, l2))) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_NOT(LTL_IMPL (l1, l2))) (LTL_AND (l1, LTL_NOT l2))) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_EQUIV (LTL_NOT l1, LTL_NOT l2)) (LTL_EQUIV (l1, l2))) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_NOT(LTL_SUNTIL (l1, l2))) (LTL_BEFORE (LTL_NOT l1, l2))) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_NOT(LTL_PSUNTIL (l1, l2))) (LTL_PBEFORE (LTL_NOT l1, l2))) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_NOT(LTL_BEFORE (l1, l2))) (LTL_SUNTIL (LTL_NOT l1, l2))) /\
      (!l1 l2. LTL_EQUIVALENT (LTL_NOT(LTL_PBEFORE (l1, l2))) (LTL_PSUNTIL (LTL_NOT l1, l2)))``,

    `!t. (~(t > 0)) = (t = 0)` by DECIDE_TAC THEN
    `!t. (~(t = 0)) = (t > 0)` by DECIDE_TAC THEN
    ASM_SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_SEM_THM, LTL_BEFORE_def,
      LTL_PBEFORE_def] THEN
    METIS_TAC[]);


val LTL_EQUIVALENT_until_sbefore_nnf_rewrites =
  prove (
      ``(!l1:'a ltl l2. LTL_EQUIVALENT (LTL_NOT(LTL_UNTIL (l1, l2))) (LTL_SBEFORE (LTL_NOT l1, l2))) /\
      (!l1:'a ltl l2. LTL_EQUIVALENT (LTL_NOT(LTL_SBEFORE (l1, l2))) (LTL_UNTIL (LTL_NOT l1, l2)))``,

      Tactical.REVERSE LEFT_CONJ_TAC THEN1 (
        REPEAT STRIP_TAC THEN
        Q_SPECL_NO_ASSUM 0 [`LTL_NOT l1`, `l2`] THEN
        FULL_SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_SEM_THM, LTL_SBEFORE_def,
          LTL_UNTIL_def] THEN
        REPEAT STRIP_TAC THEN
        Q_SPECL_NO_ASSUM 0 [`t`, `w`] THEN
        METIS_TAC[]
      ) THEN

      SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_SEM_TIME_def] THEN
      REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC[REWRITE_RULE [LTL_EQUIVALENT_def] LTL_WEAK_UNTIL___ALTERNATIVE_DEF] THEN
      REWRITE_TAC[LTL_SBEFORE_def] THEN
      SIMP_TAC std_ss [LTL_SEM_THM] THEN
      METIS_TAC[]);



val LTL_EQUIVALENT_puntil_psbefore_nnf_rewrites =
  prove (
      ``(!l1:'a ltl l2. LTL_EQUIVALENT (LTL_NOT(LTL_PUNTIL (l1, l2))) (LTL_PSBEFORE (LTL_NOT l1, l2))) /\
      (!l1:'a ltl l2. LTL_EQUIVALENT (LTL_NOT(LTL_PSBEFORE (l1, l2))) (LTL_PUNTIL (LTL_NOT l1, l2)))``,

      Tactical.REVERSE LEFT_CONJ_TAC THEN1 (
        REPEAT STRIP_TAC THEN
        Q_SPECL_NO_ASSUM 0 [`LTL_NOT l1`, `l2`] THEN
        FULL_SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_SEM_THM, LTL_PSBEFORE_def,
          LTL_PUNTIL_def] THEN
        REPEAT STRIP_TAC THEN
        Q_SPECL_NO_ASSUM 0 [`t`, `w`] THEN
        METIS_TAC[]
      ) THEN

      SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_SEM_TIME_def] THEN
      REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC[REWRITE_RULE [LTL_EQUIVALENT_def] LTL_PAST_WEAK_UNTIL___ALTERNATIVE_DEF] THEN
      REWRITE_TAC[LTL_PSBEFORE_def] THEN
      SIMP_TAC std_ss [LTL_SEM_THM] THEN
      METIS_TAC[]);



val LTL_EQUIVALENT_nnf_rewrites =
  save_thm("LTL_EQUIVALENT_nnf_rewrites",
  LIST_CONJ [
    LTL_EQUIVALENT_simple_nnf_rewrites,
    LTL_EQUIVALENT_until_sbefore_nnf_rewrites,
    LTL_EQUIVALENT_puntil_psbefore_nnf_rewrites]);



val LTL_EQUIVALENT_true_false_rewrites =
  store_thm (
    "LTL_EQUIVALENT_true_false_rewrites",
    ``(LTL_EQUIVALENT (LTL_ALWAYS LTL_TRUE) LTL_TRUE) /\
      (LTL_EQUIVALENT (LTL_ALWAYS LTL_FALSE) LTL_FALSE) /\
      (LTL_EQUIVALENT (LTL_EVENTUAL LTL_TRUE) LTL_TRUE) /\
      (LTL_EQUIVALENT (LTL_EVENTUAL LTL_FALSE) LTL_FALSE) /\
      (LTL_EQUIVALENT (LTL_NEXT LTL_TRUE) LTL_TRUE) /\
      (LTL_EQUIVALENT (LTL_NEXT LTL_FALSE) LTL_FALSE) /\
      (LTL_EQUIVALENT (LTL_PALWAYS LTL_TRUE) LTL_TRUE) /\
      (LTL_EQUIVALENT (LTL_PALWAYS LTL_FALSE) LTL_FALSE) /\
      (LTL_EQUIVALENT (LTL_PEVENTUAL LTL_TRUE) LTL_TRUE) /\
      (LTL_EQUIVALENT (LTL_PEVENTUAL LTL_FALSE) LTL_FALSE) /\
      (LTL_EQUIVALENT (LTL_PNEXT LTL_TRUE) LTL_TRUE) /\
      (LTL_EQUIVALENT (LTL_PNEXT LTL_FALSE) LTL_INIT) /\
      (LTL_EQUIVALENT (LTL_PSNEXT LTL_TRUE) (LTL_NOT LTL_INIT)) /\
      (LTL_EQUIVALENT (LTL_PSNEXT LTL_FALSE) LTL_FALSE) /\

      (!l. LTL_EQUIVALENT (LTL_SUNTIL(LTL_FALSE, l)) l) /\
      (!l. LTL_EQUIVALENT (LTL_SUNTIL(l, LTL_TRUE)) LTL_TRUE) /\
      (!l. LTL_EQUIVALENT (LTL_SUNTIL(l, LTL_FALSE)) LTL_FALSE) /\
      (!l. LTL_EQUIVALENT (LTL_UNTIL(LTL_FALSE, l)) l) /\
      (!l. LTL_EQUIVALENT (LTL_UNTIL(l, LTL_TRUE)) LTL_TRUE) /\

      (!l. LTL_EQUIVALENT (LTL_PSUNTIL(LTL_FALSE, l)) l) /\
      (!l. LTL_EQUIVALENT (LTL_PSUNTIL(l, LTL_TRUE)) LTL_TRUE) /\
      (!l. LTL_EQUIVALENT (LTL_PSUNTIL(l, LTL_FALSE)) LTL_FALSE) /\
      (!l. LTL_EQUIVALENT (LTL_PUNTIL(LTL_FALSE, l)) l) /\
      (!l. LTL_EQUIVALENT (LTL_PUNTIL(l, LTL_TRUE)) LTL_TRUE) /\

      (!l. LTL_EQUIVALENT (LTL_SBEFORE(LTL_TRUE, l)) (LTL_NOT l)) /\
      (!l. LTL_EQUIVALENT (LTL_SBEFORE(LTL_FALSE, l)) LTL_FALSE) /\
      (!l. LTL_EQUIVALENT (LTL_SBEFORE(l, LTL_TRUE)) LTL_FALSE) /\
      (!l. LTL_EQUIVALENT (LTL_PSBEFORE(LTL_TRUE, l)) (LTL_NOT l)) /\
      (!l. LTL_EQUIVALENT (LTL_PSBEFORE(LTL_FALSE, l)) LTL_FALSE) /\
      (!l. LTL_EQUIVALENT (LTL_PSBEFORE(l, LTL_TRUE)) LTL_FALSE) /\

      (!l. LTL_EQUIVALENT (LTL_BEFORE(LTL_TRUE, l)) (LTL_NOT l)) /\
      (!l. LTL_EQUIVALENT (LTL_BEFORE(l, LTL_TRUE)) LTL_FALSE) /\
      (!l. LTL_EQUIVALENT (LTL_BEFORE(l, LTL_FALSE)) LTL_TRUE) /\
      (!l. LTL_EQUIVALENT (LTL_PBEFORE(LTL_TRUE, l)) (LTL_NOT l)) /\
      (!l. LTL_EQUIVALENT (LTL_PBEFORE(l, LTL_TRUE)) LTL_FALSE) /\
      (!l. LTL_EQUIVALENT (LTL_PBEFORE(l, LTL_FALSE)) LTL_TRUE)``,

    Q.SUBGOAL_THEN `!t. ?k. t <= k` STRIP_ASSUME_TAC THEN1 (
      GEN_TAC THEN EXISTS_TAC ``SUC t`` THEN DECIDE_TAC
    ) THEN
    Q.SUBGOAL_THEN `!t. ?k. k <= t` STRIP_ASSUME_TAC THEN1 (
      GEN_TAC THEN EXISTS_TAC ``0`` THEN DECIDE_TAC
    ) THEN
    `!t. t > 0 = ~(t = 0)` by DECIDE_TAC THEN
    Q.SUBGOAL_THEN `!t k. ((!j. ~(t <= j) \/ ~(j < k)) = (k <= t))` STRIP_ASSUME_TAC THEN1 (
      REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
        CCONTR_TAC THEN
        `(t < k) /\ (t <= t)` by DECIDE_TAC THEN
        PROVE_TAC[],

        DECIDE_TAC
      ]
    ) THEN
    Q.SUBGOAL_THEN `!t k. ((!j. ~(j <= t) \/ ~(k < j)) = (t <= k))` STRIP_ASSUME_TAC THEN1 (
      REPEAT WEAKEN_HD_TAC THEN
      REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
        CCONTR_TAC THEN
        `(k < t) /\ (t <= t)` by DECIDE_TAC THEN
        PROVE_TAC[],

        DECIDE_TAC
      ]
    ) THEN
    `!t k. (t <= k /\ k <= t) = (t = k)` by DECIDE_TAC THEN
    ASM_SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_SEM_THM, FORALL_AND_THM, GREATER_EQ, LTL_UNTIL_def, LTL_PUNTIL_def, LTL_BEFORE_def, LTL_PBEFORE_def] THEN
    METIS_TAC[]);

val LTL_EQUIVALENT_simple_homogeneous_conj_disj_rewrites =
  prove (
    ``(*LTL_NEXT*)
      (!l1 l2. (LTL_EQUIVALENT (LTL_AND (LTL_NEXT l1, LTL_NEXT l2)) (LTL_NEXT (LTL_AND(l1,l2))))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_NEXT l1, LTL_AND(LTL_NEXT l2, l3))) (LTL_AND(LTL_NEXT (LTL_AND(l1,l2)), l3)))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_NEXT l1, LTL_AND(l3, LTL_NEXT l2))) (LTL_AND(LTL_NEXT (LTL_AND(l1,l2)), l3)))) /\
      (!l1 l2. (LTL_EQUIVALENT (LTL_OR (LTL_NEXT l1, LTL_NEXT l2)) (LTL_NEXT (LTL_OR(l1,l2))))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_NEXT l1, LTL_OR(LTL_NEXT l2, l3))) (LTL_OR(LTL_NEXT (LTL_OR(l1,l2)), l3)))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_NEXT l1, LTL_OR(l3, LTL_NEXT l2))) (LTL_OR(LTL_NEXT (LTL_OR(l1,l2)), l3)))) /\

      (*LTL_PNEXT*)
      (!l1 l2. (LTL_EQUIVALENT (LTL_AND (LTL_PNEXT l1, LTL_PNEXT l2)) (LTL_PNEXT (LTL_AND(l1,l2))))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_PNEXT l1, LTL_AND(LTL_PNEXT l2, l3))) (LTL_AND(LTL_PNEXT (LTL_AND(l1,l2)), l3)))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_PNEXT l1, LTL_AND(l3, LTL_PNEXT l2))) (LTL_AND(LTL_PNEXT (LTL_AND(l1,l2)), l3)))) /\
      (!l1 l2. (LTL_EQUIVALENT (LTL_OR (LTL_PNEXT l1, LTL_PNEXT l2)) (LTL_PNEXT (LTL_OR(l1,l2))))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_PNEXT l1, LTL_OR(LTL_PNEXT l2, l3))) (LTL_OR(LTL_PNEXT (LTL_OR(l1,l2)), l3)))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_PNEXT l1, LTL_OR(l3, LTL_PNEXT l2))) (LTL_OR(LTL_PNEXT (LTL_OR(l1,l2)), l3)))) /\

      (*LTL_PSNEXT*)
      (!l1 l2. (LTL_EQUIVALENT (LTL_AND (LTL_PSNEXT l1, LTL_PSNEXT l2)) (LTL_PSNEXT (LTL_AND(l1,l2))))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_PSNEXT l1, LTL_AND(LTL_PSNEXT l2, l3))) (LTL_AND(LTL_PSNEXT (LTL_AND(l1,l2)), l3)))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_PSNEXT l1, LTL_AND(l3, LTL_PSNEXT l2))) (LTL_AND(LTL_PSNEXT (LTL_AND(l1,l2)), l3)))) /\
      (!l1 l2. (LTL_EQUIVALENT (LTL_OR (LTL_PSNEXT l1, LTL_PSNEXT l2)) (LTL_PSNEXT (LTL_OR(l1,l2))))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_PSNEXT l1, LTL_OR(LTL_PSNEXT l2, l3))) (LTL_OR(LTL_PSNEXT (LTL_OR(l1,l2)), l3)))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_PSNEXT l1, LTL_OR(l3, LTL_PSNEXT l2))) (LTL_OR(LTL_PSNEXT (LTL_OR(l1,l2)), l3)))) /\


      (*LTL_ALWAYS*)
      (!l1 l2. (LTL_EQUIVALENT (LTL_AND (LTL_ALWAYS l1, LTL_ALWAYS l2)) (LTL_ALWAYS (LTL_AND(l1,l2))))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_ALWAYS l1, LTL_AND(LTL_ALWAYS l2, l3))) (LTL_AND(LTL_ALWAYS (LTL_AND(l1,l2)), l3)))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_ALWAYS l1, LTL_AND(l3, LTL_ALWAYS l2))) (LTL_AND(LTL_ALWAYS (LTL_AND(l1,l2)), l3)))) /\

      (*LTL_PALWAYS*)
      (!l1 l2. (LTL_EQUIVALENT (LTL_AND (LTL_PALWAYS l1, LTL_PALWAYS l2)) (LTL_PALWAYS (LTL_AND(l1,l2))))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_PALWAYS l1, LTL_AND(LTL_PALWAYS l2, l3))) (LTL_AND(LTL_PALWAYS (LTL_AND(l1,l2)), l3)))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_PALWAYS l1, LTL_AND(l3, LTL_PALWAYS l2))) (LTL_AND(LTL_PALWAYS (LTL_AND(l1,l2)), l3)))) /\

      (*LTL_EVENTUAL*)
      (!l1 l2. (LTL_EQUIVALENT (LTL_OR (LTL_EVENTUAL l1, LTL_EVENTUAL l2)) (LTL_EVENTUAL (LTL_OR(l1,l2))))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_EVENTUAL l1, LTL_OR(LTL_EVENTUAL l2, l3))) (LTL_OR(LTL_EVENTUAL (LTL_OR(l1,l2)), l3)))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_EVENTUAL l1, LTL_OR(l3, LTL_EVENTUAL l2))) (LTL_OR(LTL_EVENTUAL (LTL_OR(l1,l2)), l3)))) /\

      (*LTL_PEVENTUAL*)
      (!l1 l2. (LTL_EQUIVALENT (LTL_OR (LTL_PEVENTUAL l1, LTL_PEVENTUAL l2)) (LTL_PEVENTUAL (LTL_OR(l1,l2))))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_PEVENTUAL l1, LTL_OR(LTL_PEVENTUAL l2, l3))) (LTL_OR(LTL_PEVENTUAL (LTL_OR(l1,l2)), l3)))) /\
      (!l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_PEVENTUAL l1, LTL_OR(l3, LTL_PEVENTUAL l2))) (LTL_OR(LTL_PEVENTUAL (LTL_OR(l1,l2)), l3)))) /\

      (*LTL_SUNTIL OR*)
      (!l l1 l2. (LTL_EQUIVALENT (LTL_OR (LTL_SUNTIL (l, l1), LTL_SUNTIL (l, l2))) (LTL_SUNTIL (l, (LTL_OR(l1,l2)))))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_SUNTIL (l, l1), LTL_OR(LTL_SUNTIL (l, l2), l3))) (LTL_OR(LTL_SUNTIL (l, (LTL_OR(l1,l2))), l3)))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_SUNTIL (l, l1), LTL_OR(l3, LTL_SUNTIL (l, l2)))) (LTL_OR(LTL_SUNTIL (l, (LTL_OR(l1,l2))), l3)))) /\

      (*LTL_UNTIL OR*)
      (!l l1 l2. (LTL_EQUIVALENT (LTL_OR (LTL_UNTIL (l, l1), LTL_UNTIL (l, l2))) (LTL_UNTIL (l, (LTL_OR(l1,l2)))))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_UNTIL (l, l1), LTL_OR(LTL_UNTIL (l, l2), l3))) (LTL_OR(LTL_UNTIL (l, (LTL_OR(l1,l2))), l3)))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_UNTIL (l, l1), LTL_OR(l3, LTL_UNTIL (l, l2)))) (LTL_OR(LTL_UNTIL (l, (LTL_OR(l1,l2))), l3)))) /\

      (*LTL_PSUNTIL OR*)
      (!l l1 l2. (LTL_EQUIVALENT (LTL_OR (LTL_PSUNTIL (l, l1), LTL_PSUNTIL (l, l2))) (LTL_PSUNTIL (l, (LTL_OR(l1,l2)))))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_PSUNTIL (l, l1), LTL_OR(LTL_PSUNTIL (l, l2), l3))) (LTL_OR(LTL_PSUNTIL (l, (LTL_OR(l1,l2))), l3)))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_PSUNTIL (l, l1), LTL_OR(l3, LTL_PSUNTIL (l, l2)))) (LTL_OR(LTL_PSUNTIL (l, (LTL_OR(l1,l2))), l3)))) /\

      (*LTL_PUNTIL OR*)
      (!l l1 l2. (LTL_EQUIVALENT (LTL_OR (LTL_PUNTIL (l, l1), LTL_PUNTIL (l, l2))) (LTL_PUNTIL (l, (LTL_OR(l1,l2)))))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_PUNTIL (l, l1), LTL_OR(LTL_PUNTIL (l, l2), l3))) (LTL_OR(LTL_PUNTIL (l, (LTL_OR(l1,l2))), l3)))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_PUNTIL (l, l1), LTL_OR(l3, LTL_PUNTIL (l, l2)))) (LTL_OR(LTL_PUNTIL (l, (LTL_OR(l1,l2))), l3)))) /\

      (*LTL_SBEFORE OR*)
      (!l l1 l2. (LTL_EQUIVALENT (LTL_OR (LTL_SBEFORE (l1, l), LTL_SBEFORE (l2, l))) (LTL_SBEFORE (LTL_OR(l1,l2), l)))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_SBEFORE (l1, l), LTL_OR(LTL_SBEFORE (l2, l), l3))) (LTL_OR(LTL_SBEFORE ((LTL_OR(l1,l2)), l), l3)))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_SBEFORE (l1, l), LTL_OR(l3, LTL_SBEFORE (l2, l)))) (LTL_OR(LTL_SBEFORE ((LTL_OR(l1,l2)), l), l3)))) /\

      (*LTL_PSBEFORE OR*)
      (!l l1 l2. (LTL_EQUIVALENT (LTL_OR (LTL_PSBEFORE (l1, l), LTL_PSBEFORE (l2, l))) (LTL_PSBEFORE (LTL_OR(l1,l2), l)))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_PSBEFORE (l1, l), LTL_OR(LTL_PSBEFORE (l2, l), l3))) (LTL_OR(LTL_PSBEFORE ((LTL_OR(l1,l2)), l), l3)))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_PSBEFORE (l1, l), LTL_OR(l3, LTL_PSBEFORE (l2, l)))) (LTL_OR(LTL_PSBEFORE ((LTL_OR(l1,l2)), l), l3))))``,

    SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_SEM_THM, P_SEM_THM, LTL_UNTIL_def, LTL_PUNTIL_def, LTL_PBEFORE_def,
      LTL_BEFORE_def] THEN
    METIS_TAC[]);

val LTL_SEM_TIME_and_or_not = prove (
  ``!t v l1 l2.
      (LTL_SEM_TIME t v (LTL_NOT l1) <=> ~(LTL_SEM_TIME t v l1)) /\
      (LTL_SEM_TIME t v (LTL_AND (l1, l2)) <=> LTL_SEM_TIME t v l1 /\ LTL_SEM_TIME t v l2) /\
      (LTL_SEM_TIME t v (LTL_OR (l1, l2)) <=> LTL_SEM_TIME t v l1 \/ LTL_SEM_TIME t v l2)``,
    SIMP_TAC std_ss [LTL_SEM_THM]);

val LTL_EQUIVALENT_and_until_homogeneous_conj_disj_rewrites =
  prove (
    ``(!(l:'a ltl) l1 l2. (LTL_EQUIVALENT (LTL_AND (LTL_SUNTIL (l1, l), LTL_SUNTIL (l2, l))) (LTL_SUNTIL ((LTL_AND(l1,l2)), l)))) /\
      (!(l:'a ltl) l1 l2. (LTL_EQUIVALENT (LTL_AND (LTL_PSUNTIL (l1, l), LTL_PSUNTIL (l2, l))) (LTL_PSUNTIL ((LTL_AND(l1,l2)), l)))) /\
      (!(l:'a ltl) l1 l2. (LTL_EQUIVALENT (LTL_AND (LTL_UNTIL (l1, l), LTL_UNTIL (l2, l))) (LTL_UNTIL ((LTL_AND(l1,l2)), l)))) /\
      (!(l:'a ltl) l1 l2. (LTL_EQUIVALENT (LTL_AND (LTL_PUNTIL (l1, l), LTL_PUNTIL (l2, l))) (LTL_PUNTIL ((LTL_AND(l1,l2)), l))))``,


    SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_SEM_THM, LTL_PUNTIL_def, LTL_UNTIL_def] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      `?mink. mink = MIN k k'` by METIS_TAC[] THEN
      EXISTS_TAC ``mink:num`` THEN
      SIMP_ALL_TAC std_ss [MIN_DEF] THEN
      REPEAT STRIP_TAC THENL [
        ASM_SIMP_TAC arith_ss [],
        METIS_TAC[],
        `j < k` by DECIDE_TAC THEN PROVE_TAC[],
        `j < k'` by DECIDE_TAC THEN PROVE_TAC[]
      ],

      PROVE_TAC[],
      PROVE_TAC[],

      `?maxk. maxk = MAX k k'` by METIS_TAC[] THEN
      EXISTS_TAC ``maxk:num`` THEN
      SIMP_ALL_TAC std_ss [MAX_DEF] THEN
      REPEAT STRIP_TAC THENL [
        ASM_SIMP_TAC arith_ss [],
        METIS_TAC[],
        `k < j` by DECIDE_TAC THEN PROVE_TAC[],
        `k' < j` by DECIDE_TAC THEN PROVE_TAC[]
      ],

      PROVE_TAC[],
      PROVE_TAC[],

      DISJ1_TAC THEN
      `?mink. mink = MIN k k'` by METIS_TAC[] THEN
      EXISTS_TAC ``mink:num`` THEN
      SIMP_ALL_TAC std_ss [MIN_DEF] THEN
      REPEAT STRIP_TAC THENL [
        ASM_SIMP_TAC arith_ss [],
        METIS_TAC[],
        `j < k` by DECIDE_TAC THEN PROVE_TAC[],
        `j < k'` by DECIDE_TAC THEN PROVE_TAC[]
      ],


      DISJ1_TAC THEN
      EXISTS_TAC ``k:num`` THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THENL [
        PROVE_TAC[],
        `j >= t` by DECIDE_TAC THEN PROVE_TAC[]
      ],

      DISJ1_TAC THEN
      EXISTS_TAC ``k:num`` THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THENL [
        `j >= t` by DECIDE_TAC THEN PROVE_TAC[],
        PROVE_TAC[]
      ],

      PROVE_TAC[],
      PROVE_TAC[],
      PROVE_TAC[],
      PROVE_TAC[],
      PROVE_TAC[],

      DISJ1_TAC THEN
      `?maxk. maxk = MAX k k'` by METIS_TAC[] THEN
      EXISTS_TAC ``maxk:num`` THEN
      SIMP_ALL_TAC std_ss [MAX_DEF] THEN
      REPEAT STRIP_TAC THENL [
        ASM_SIMP_TAC arith_ss [],
        METIS_TAC[],
        `k < j` by DECIDE_TAC THEN PROVE_TAC[],
        `k' < j` by DECIDE_TAC THEN PROVE_TAC[]
      ],

      DISJ1_TAC THEN
      EXISTS_TAC ``k:num`` THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THENL [
        PROVE_TAC[],
        `k <= t` by DECIDE_TAC THEN PROVE_TAC[]
      ],

      DISJ1_TAC THEN
      EXISTS_TAC ``k:num`` THEN
      PROVE_TAC[],

      PROVE_TAC[],
      PROVE_TAC[],
      PROVE_TAC[],
      PROVE_TAC[],
      PROVE_TAC[]
    ]);


val LTL_EQUIVALENT_and_until2_homogeneous_conj_disj_rewrites =
  prove (``
    (!l (l1:'a ltl) l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_SUNTIL (l1, l), LTL_AND(LTL_SUNTIL (l2, l), l3))) (LTL_AND(LTL_SUNTIL ((LTL_AND(l1,l2)), l), l3)))) /\
    (!l (l1:'a ltl) l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_SUNTIL (l1, l), LTL_AND(l3, LTL_SUNTIL (l2, l)))) (LTL_AND(LTL_SUNTIL ((LTL_AND(l1,l2)), l), l3)))) /\

    (!l (l1:'a ltl) l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_UNTIL (l1, l), LTL_AND(LTL_UNTIL (l2, l), l3))) (LTL_AND(LTL_UNTIL ((LTL_AND(l1,l2)), l), l3)))) /\
    (!l (l1:'a ltl) l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_UNTIL (l1, l), LTL_AND(l3, LTL_UNTIL (l2, l)))) (LTL_AND(LTL_UNTIL ((LTL_AND(l1,l2)), l), l3)))) /\

    (!l (l1:'a ltl) l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_PSUNTIL (l1, l), LTL_AND(LTL_PSUNTIL (l2, l), l3))) (LTL_AND(LTL_PSUNTIL ((LTL_AND(l1,l2)), l), l3)))) /\
    (!l (l1:'a ltl) l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_PSUNTIL (l1, l), LTL_AND(l3, LTL_PSUNTIL (l2, l)))) (LTL_AND(LTL_PSUNTIL ((LTL_AND(l1,l2)), l), l3)))) /\

    (!l (l1:'a ltl) l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_PUNTIL (l1, l), LTL_AND(LTL_PUNTIL (l2, l), l3))) (LTL_AND(LTL_PUNTIL ((LTL_AND(l1,l2)), l), l3)))) /\
    (!l (l1:'a ltl) l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_PUNTIL (l1, l), LTL_AND(l3, LTL_PUNTIL (l2, l)))) (LTL_AND(LTL_PUNTIL ((LTL_AND(l1,l2)), l), l3))))``,

    ASSUME_TAC (GSYM (SIMP_RULE std_ss [LTL_EQUIVALENT_def, LTL_SEM_TIME_and_or_not] LTL_EQUIVALENT_and_until_homogeneous_conj_disj_rewrites)) THEN
    ASM_SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_SEM_TIME_and_or_not] THEN
    REPEAT STRIP_TAC THEN
    REPEAT BOOL_EQ_STRIP_TAC);


(*to prove similar rules for before, we can use the already existing stuff :-) *)
val ltl_equivalent_preorder =
    mk_preorder (LTL_EQUIVALENT_TRANS, LTL_EQUIVALENT_REFL);

val ltl_CS = CSFRAG
   {rewrs  = [LTL_EQUIVALENT_bool_rewrites, LTL_EQUIVALENT_true_false_rewrites,
              LTL_EQUIVALENT_and_until_homogeneous_conj_disj_rewrites,
              LTL_EQUIVALENT_and_until2_homogeneous_conj_disj_rewrites,
              LTL_EQUIVALENT_simple_homogeneous_conj_disj_rewrites,
              LTL_EQUIVALENT_nnf_rewrites,
      GSYM LTL_TRUE_def, GSYM LTL_FALSE_def],
    relations = [ltl_equivalent_preorder],
    dprocs = [],
    congs  = [LTL_EQUIVALENT_congs]};
val ltl_cs = mk_congset [ltl_CS];


(*LTL_BEFORE OR*)
val LTL_EQUIVALENT_before_homogeneous_conj_disj_rewrites =
  prove (``
      (!l l1 l2. (LTL_EQUIVALENT (LTL_OR (LTL_BEFORE (l1, l), LTL_BEFORE (l2, l))) (LTL_BEFORE (LTL_OR(l1,l2), l)))) /\
      (!l l1 l2. (LTL_EQUIVALENT (LTL_OR (LTL_PBEFORE (l1, l), LTL_PBEFORE (l2, l))) (LTL_PBEFORE (LTL_OR(l1,l2), l)))) /\
      (!l l1 l2. (LTL_EQUIVALENT (LTL_AND (LTL_SBEFORE (l, l1), LTL_SBEFORE (l, l2))) (LTL_SBEFORE (l, (LTL_OR(l1,l2)))))) /\
      (!l l1 l2. (LTL_EQUIVALENT (LTL_AND (LTL_BEFORE (l, l1), LTL_BEFORE (l, l2))) (LTL_BEFORE (l, (LTL_OR(l1,l2)))))) /\
      (!l l1 l2. (LTL_EQUIVALENT (LTL_AND (LTL_PSBEFORE (l, l1), LTL_PSBEFORE (l, l2))) (LTL_PSBEFORE (l, (LTL_OR(l1,l2)))))) /\
      (!l l1 l2. (LTL_EQUIVALENT (LTL_AND (LTL_PBEFORE (l, l1), LTL_PBEFORE (l, l2))) (LTL_PBEFORE (l, (LTL_OR(l1,l2)))))) /\

      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_BEFORE (l1, l), LTL_OR(LTL_BEFORE (l2, l), l3))) (LTL_OR(LTL_BEFORE ((LTL_OR(l1,l2)), l), l3)))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_BEFORE (l1, l), LTL_OR(l3, LTL_BEFORE (l2, l)))) (LTL_OR(LTL_BEFORE ((LTL_OR(l1,l2)), l), l3)))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_PBEFORE (l1, l), LTL_OR(LTL_PBEFORE (l2, l), l3))) (LTL_OR(LTL_PBEFORE ((LTL_OR(l1,l2)), l), l3)))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_OR (LTL_PBEFORE (l1, l), LTL_OR(l3, LTL_PBEFORE (l2, l)))) (LTL_OR(LTL_PBEFORE ((LTL_OR(l1,l2)), l), l3)))) /\

      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_BEFORE (l, l1), LTL_AND(LTL_BEFORE (l, l2), l3))) (LTL_AND(LTL_BEFORE (l, (LTL_OR(l1,l2))), l3)))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_BEFORE (l, l1), LTL_AND(l3, LTL_BEFORE (l, l2)))) (LTL_AND(LTL_BEFORE (l, (LTL_OR(l1,l2))), l3)))) /\

      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_SBEFORE (l, l1), LTL_AND(LTL_SBEFORE (l, l2), l3))) (LTL_AND(LTL_SBEFORE (l, (LTL_OR(l1,l2))), l3)))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_SBEFORE (l, l1), LTL_AND(l3, LTL_SBEFORE (l, l2)))) (LTL_AND(LTL_SBEFORE (l, (LTL_OR(l1,l2))), l3)))) /\

      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_PSBEFORE (l, l1), LTL_AND(LTL_PSBEFORE (l, l2), l3))) (LTL_AND(LTL_PSBEFORE (l, (LTL_OR(l1,l2))), l3)))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_PSBEFORE (l, l1), LTL_AND(l3, LTL_PSBEFORE (l, l2)))) (LTL_AND(LTL_PSBEFORE (l, (LTL_OR(l1,l2))), l3)))) /\

      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_PBEFORE (l, l1), LTL_AND(LTL_PBEFORE (l, l2), l3))) (LTL_AND(LTL_PBEFORE (l, (LTL_OR(l1,l2))), l3)))) /\
      (!l l1 l2 l3. (LTL_EQUIVALENT (LTL_AND (LTL_PBEFORE (l, l1), LTL_AND(l3, LTL_PBEFORE (l, l2)))) (LTL_AND(LTL_PBEFORE (l, (LTL_OR(l1,l2))), l3))))``,


    ONCE_ASM_REWRITE_TAC [prove (``!l1 l2. LTL_EQUIVALENT l1 l2 = (LTL_EQUIVALENT (LTL_NOT l1) (LTL_NOT l2))``, SIMP_TAC std_ss [LTL_EQUIVALENT_def, LTL_SEM_THM])] THEN
    CONGRUENCE_SIMP_TAC ltl_cs std_ss []);




val LTL_EQUIVALENT_homogeneous_conj_disj_rewrites =
  save_thm("LTL_EQUIVALENT_homogeneous_conj_disj_rewrites",
  LIST_CONJ [
    LTL_EQUIVALENT_simple_homogeneous_conj_disj_rewrites,
    LTL_EQUIVALENT_and_until_homogeneous_conj_disj_rewrites,
    LTL_EQUIVALENT_and_until2_homogeneous_conj_disj_rewrites,
    LTL_EQUIVALENT_before_homogeneous_conj_disj_rewrites]);


val _ = export_theory();
