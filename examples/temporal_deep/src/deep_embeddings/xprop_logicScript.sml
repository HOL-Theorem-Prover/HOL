open HolKernel Parse boolLib bossLib;

open pred_setTheory listTheory pairTheory prop_logicTheory containerTheory
     tuerk_tacticsLib set_lemmataTheory temporal_deep_mixedTheory;

open Sanity;

val _ = hide "S";
val _ = hide "I";

val _ = new_theory "xprop_logic";
val _ = ParseExtras.temp_loose_equality()

Datatype :
  xprop_logic = XP_PROP 'a                         (* atomic proposition *)
              | XP_NEXT_PROP 'a                    (* X atomic proposition *)
              | XP_TRUE                            (* true *)
              | XP_NOT  xprop_logic                (* negation *)
              | XP_AND (xprop_logic # xprop_logic) (* conjunction *)
End

Theorem xprop_logic_induct = Q.GEN `P`
   (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2)) ==> (A ==> B1)``)
     (SIMP_RULE std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P x ==> Q(x,y)) = !x. P x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P y ==> Q(x,y)) = !y. P y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P`,`\(f1,f2). P f1 /\ P f2`]
         (TypeBase.induction_of ``:'a xprop_logic``))));

val XP_USED_CURRENT_VARS_def = Define
  `(XP_USED_CURRENT_VARS (XP_TRUE) = EMPTY) /\
   (XP_USED_CURRENT_VARS (XP_PROP p) = {p}) /\
   (XP_USED_CURRENT_VARS (XP_NEXT_PROP p) = EMPTY) /\
   (XP_USED_CURRENT_VARS (XP_NOT b) = XP_USED_CURRENT_VARS b) /\
   (XP_USED_CURRENT_VARS (XP_AND(b1,b2)) =
      (XP_USED_CURRENT_VARS b1) UNION (XP_USED_CURRENT_VARS b2))`;

val XP_USED_X_VARS_def = Define
  `(XP_USED_X_VARS (XP_TRUE) = EMPTY) /\
   (XP_USED_X_VARS (XP_PROP p) = EMPTY) /\
   (XP_USED_X_VARS (XP_NEXT_PROP p) = {p}) /\
   (XP_USED_X_VARS (XP_NOT b) = XP_USED_X_VARS b) /\
   (XP_USED_X_VARS (XP_AND(b1,b2)) = (XP_USED_X_VARS b1) UNION (XP_USED_X_VARS b2))`;

val XP_USED_VARS_def = Define
   `XP_USED_VARS b = (XP_USED_CURRENT_VARS b) UNION (XP_USED_X_VARS b)`;

val XP_VAR_RENAMING_def = Define
  `(XP_VAR_RENAMING (f:'a->'b) (XP_TRUE) = XP_TRUE) /\
   (XP_VAR_RENAMING f (XP_PROP p) = (XP_PROP (f p))) /\
   (XP_VAR_RENAMING f (XP_NEXT_PROP p) = (XP_NEXT_PROP (f p))) /\
   (XP_VAR_RENAMING f (XP_NOT b) = XP_NOT (XP_VAR_RENAMING f b)) /\
   (XP_VAR_RENAMING f (XP_AND(b1,b2)) = XP_AND(XP_VAR_RENAMING f b1, XP_VAR_RENAMING f b2))`;

(*=============================================================================
= Semantic
=============================================================================*)

val XP_SEM_def =
 Define
  `(XP_SEM (XP_TRUE) (s1:'a set, s2:'a set) = T) /\
   (XP_SEM (XP_PROP p) (s1, s2) = (p IN s1)) /\
   (XP_SEM (XP_NEXT_PROP p) (s1, s2) = (p IN s2)) /\
   (XP_SEM (XP_NOT b) (s1, s2) = ~(XP_SEM b (s1, s2))) /\
   (XP_SEM (XP_AND (b1,b2)) (s1, s2) = ((XP_SEM b1 (s1, s2)) /\ (XP_SEM b2 (s1, s2))))`;

(*=============================================================================
= Syntactic Sugar and elementary lemmata
=============================================================================*)

(******************************************************************************
* Propositional logic with X
******************************************************************************)
val XP_FALSE_def = Define
   `XP_FALSE = XP_NOT(XP_TRUE)`;

val XP_OR_def = Define
   `XP_OR(b1, b2) = XP_NOT(XP_AND(XP_NOT b1, XP_NOT b2))`;

val XP_IMPL_def = Define
   `XP_IMPL(b1, b2) = XP_OR(XP_NOT b1, b2)`;

val XP_COND_def = Define
   `XP_COND(c, f1, f2) = XP_AND(XP_IMPL(c, f1), XP_IMPL(XP_NOT c, f2))`;

val XP_EQUIV_def = Define
   `XP_EQUIV(b1, b2) = XP_AND(XP_IMPL(b1, b2),XP_IMPL(b2, b1))`;

val XPROP_LOGIC_EQUIVALENT_def = Define
   `XPROP_LOGIC_EQUIVALENT b1 b2 = !s1 s2. (XP_SEM b1 (s1, s2)) = (XP_SEM b2 (s1, s2))`;

(* conversion from prop_logic to xprop_logic (next version) *)
val XP_NEXT_def = Define
  `(XP_NEXT (P_TRUE) = XP_TRUE) /\
   (XP_NEXT (P_PROP p) = XP_NEXT_PROP p) /\
   (XP_NEXT (P_NOT b) = XP_NOT (XP_NEXT b)) /\
   (XP_NEXT (P_AND(b1,b2)) = (XP_AND((XP_NEXT b1),(XP_NEXT b2))))`;

(* conversion from prop_logic to xprop_logic (current version) *)
val XP_CURRENT_def = Define
  `(XP_CURRENT (P_TRUE) = XP_TRUE) /\
   (XP_CURRENT (P_PROP p) = XP_PROP p) /\
   (XP_CURRENT (P_NOT b) = XP_NOT (XP_CURRENT b)) /\
   (XP_CURRENT (P_AND(b1,b2)) = (XP_AND((XP_CURRENT b1),(XP_CURRENT b2))))`;

val XP_BIGOR_def = Define
  `(XP_BIGOR [] = XP_FALSE) /\
   (XP_BIGOR (s::S) = XP_OR (s, XP_BIGOR S))`;

val XP_BIGAND_def = Define
  `(XP_BIGAND [] = XP_TRUE) /\
   (XP_BIGAND (s::l) = XP_AND (s, XP_BIGAND l))`;

val XP_BIGCOND_def = Define
  `(XP_BIGCOND [] = XP_FALSE) /\
   (XP_BIGCOND ((c,b)::l) = XP_COND (c, b, XP_BIGCOND l))`;

val XP_PROP_SET_MODEL_def = Define
  `XP_PROP_SET_MODEL S1 S2 S' =
        (XP_AND(XP_CURRENT(P_PROP_SET_MODEL S1 S'),
                      XP_NEXT(P_PROP_SET_MODEL S2 S')))`;


val XP_PROP_SET_MODEL_CURRENT_def = Define
  `XP_PROP_SET_MODEL_CURRENT f S' =
        XP_BIGOR (SET_TO_LIST (IMAGE (\S.
            (XP_AND(XP_NEXT(P_PROP_SET_MODEL S S'),
                          XP_CURRENT(P_PROP_SET_MODEL (f (S INTER S')) S'))))
            (POW S')))`;

val XP_PROP_SET_MODEL_NEXT_def = Define
  `XP_PROP_SET_MODEL_NEXT f S' =
        XP_BIGOR (SET_TO_LIST (IMAGE (\S.
            (XP_AND(XP_CURRENT(P_PROP_SET_MODEL S S'),
                          XP_NEXT(P_PROP_SET_MODEL (f (S INTER S')) S'))))
            (POW S')))`;


val XP_NEXT_THM =
  store_thm (
    "XP_NEXT_THM",

    ``((XP_NEXT P_TRUE) = XP_TRUE) /\
    ((XP_NEXT P_FALSE) = XP_FALSE) /\
    ((XP_NEXT (P_PROP p)) = XP_NEXT_PROP p) /\
    ((XP_NEXT (P_NOT b)) = XP_NOT (XP_NEXT b)) /\
    ((XP_NEXT (P_AND(b1, b2))) = XP_AND (XP_NEXT b1, XP_NEXT b2)) /\
    ((XP_NEXT (P_OR(b1, b2))) = XP_OR (XP_NEXT b1, XP_NEXT b2)) /\
    ((XP_NEXT (P_IMPL(b1, b2))) = XP_IMPL (XP_NEXT b1, XP_NEXT b2)) /\
    ((XP_NEXT (P_EQUIV(b1, b2))) = XP_EQUIV (XP_NEXT b1, XP_NEXT b2)) /\
    ((XP_NEXT (P_BIGAND l)) = XP_BIGAND (MAP XP_NEXT l)) /\
    ((XP_NEXT (P_BIGOR l)) = XP_BIGOR (MAP XP_NEXT l))``,

    SIMP_TAC std_ss [XP_NEXT_def, XP_FALSE_def, P_FALSE_def, P_OR_def, XP_OR_def,
      P_IMPL_def, XP_IMPL_def, XP_EQUIV_def, P_EQUIV_def] THEN
    Induct_on `l` THENL [
      SIMP_TAC list_ss [P_BIGAND_def, XP_BIGAND_def, XP_NEXT_def, XP_BIGOR_def, P_BIGOR_def, P_FALSE_def, XP_FALSE_def],
      ASM_SIMP_TAC list_ss [P_BIGAND_def, XP_BIGAND_def, XP_NEXT_def, P_BIGOR_def, XP_BIGOR_def, XP_OR_def, P_OR_def]
    ]);


val XP_CURRENT_THM =
  store_thm (
    "XP_CURRENT_THM",

    ``((XP_CURRENT P_TRUE) = XP_TRUE) /\
    ((XP_CURRENT P_FALSE) = XP_FALSE) /\
    ((XP_CURRENT (P_PROP p)) = XP_PROP p) /\
    ((XP_CURRENT (P_NOT b)) = XP_NOT (XP_CURRENT b)) /\
    ((XP_CURRENT (P_AND(b1, b2))) = XP_AND (XP_CURRENT b1, XP_CURRENT b2)) /\
    ((XP_CURRENT (P_OR(b1, b2))) = XP_OR (XP_CURRENT b1, XP_CURRENT b2)) /\
    ((XP_CURRENT (P_IMPL(b1, b2))) = XP_IMPL (XP_CURRENT b1, XP_CURRENT b2)) /\
    ((XP_CURRENT (P_EQUIV(b1, b2))) = XP_EQUIV (XP_CURRENT b1, XP_CURRENT b2)) /\
    ((XP_CURRENT (P_BIGAND l)) = XP_BIGAND (MAP XP_CURRENT l)) /\
    ((XP_CURRENT (P_BIGOR l)) = XP_BIGOR (MAP XP_CURRENT l))``,

    SIMP_TAC std_ss [XP_CURRENT_def, XP_FALSE_def, P_FALSE_def, P_OR_def, XP_OR_def,
      P_IMPL_def, XP_IMPL_def, XP_EQUIV_def, P_EQUIV_def] THEN
    Induct_on `l` THENL [
      SIMP_TAC list_ss [P_BIGAND_def, XP_BIGAND_def, XP_CURRENT_def, XP_BIGOR_def, P_BIGOR_def, P_FALSE_def, XP_FALSE_def],
      ASM_SIMP_TAC list_ss [P_BIGAND_def, XP_BIGAND_def, XP_CURRENT_def, P_BIGOR_def, XP_BIGOR_def, XP_OR_def, P_OR_def]
    ]);



val XP_SEM_THM =
 store_thm
  ("XP_SEM_THM",
     ``!s1 s2 b1 b2 b c p.
       (XP_SEM XP_TRUE (s1,s2)) /\
      ~(XP_SEM XP_FALSE (s1,s2)) /\
       (XP_SEM (XP_PROP p) (s1,s2) = p IN s1) /\
       (XP_SEM (XP_NEXT_PROP p) (s1,s2) = p IN s2) /\
       (XP_SEM (XP_NOT b) (s1,s2) = ~XP_SEM b (s1,s2)) /\
       (XP_SEM (XP_AND (b1,b2)) (s1,s2) =
        (XP_SEM b1 (s1,s2) /\ XP_SEM b2 (s1,s2))) /\
       (XP_SEM (XP_OR (b1,b2)) (s1,s2) = XP_SEM b1 (s1,s2) \/ XP_SEM b2 (s1,s2)) /\
       (XP_SEM (XP_IMPL (b1,b2)) (s1,s2) = (~XP_SEM b1 (s1,s2) \/ XP_SEM b2 (s1,s2))) /\
       (XP_SEM (XP_EQUIV (b1,b2)) (s1,s2) = (XP_SEM b1 (s1,s2) = XP_SEM b2 (s1,s2))) /\
       (XP_SEM (XP_COND (c, b1, b2)) (s1,s2) = (XP_SEM (XP_AND(c, b1)) (s1,s2) \/ XP_SEM (XP_AND(XP_NOT c, b2)) (s1,s2)))``,

   SIMP_TAC std_ss [XP_FALSE_def, XP_OR_def, XP_IMPL_def, XP_EQUIV_def, XP_SEM_def, XP_COND_def] THEN
   REPEAT STRIP_TAC THEN PROVE_TAC[]
);



val XP_USED_VARS___DIRECT_DEF =
 store_thm
  ("XP_USED_VARS___DIRECT_DEF",
   ``!p b b1 b2.
      (XP_USED_VARS (XP_TRUE) = EMPTY) /\
      (XP_USED_VARS (XP_PROP p) = {p}) /\
      (XP_USED_VARS (XP_NEXT_PROP p) = {p}) /\
      (XP_USED_VARS (XP_NOT b) = XP_USED_VARS b) /\
      (XP_USED_VARS (XP_AND(b1,b2)) = ((XP_USED_VARS b1) UNION (XP_USED_VARS b2)))``,

     SIMP_TAC std_ss [XP_USED_VARS_def, XP_USED_CURRENT_VARS_def, XP_USED_X_VARS_def,
       UNION_EMPTY, EXTENSION, IN_UNION] THEN
     PROVE_TAC[]);


val XP_BIGAND___XP_USED_VARS =
 store_thm
  ("XP_BIGAND___XP_USED_VARS",

  ``(!l:'a xprop_logic list. (XP_USED_X_VARS (XP_BIGAND l) =
        LIST_BIGUNION (MAP (\xp. XP_USED_X_VARS xp) l))) /\
    (!l:'a xprop_logic list. (XP_USED_CURRENT_VARS (XP_BIGAND l) =
      LIST_BIGUNION (MAP (\xp. XP_USED_CURRENT_VARS xp) l))) /\
    (!l:'a xprop_logic list. (XP_USED_VARS (XP_BIGAND l) =
      LIST_BIGUNION (MAP (\xp. XP_USED_VARS xp) l)))``,

  SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN
  Induct_on `l` THENL [
    SIMP_TAC list_ss [XP_BIGAND_def, XP_USED_X_VARS_def,
                      XP_USED_CURRENT_VARS_def,
                      XP_USED_VARS_def,
                      LIST_BIGUNION_def,
                      UNION_EMPTY],

    SIMP_ALL_TAC list_ss [XP_BIGAND_def, XP_USED_X_VARS_def,
                      XP_USED_CURRENT_VARS_def,
                      XP_USED_VARS_def,
                      LIST_BIGUNION_def,
                      UNION_EMPTY, EXTENSION, IN_UNION] THEN
    ASM_SIMP_TAC std_ss [] THEN
    REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN
    PROVE_TAC[]
  ]);


val XP_NEXT___XP_USED_VARS=
 store_thm
  ("XP_NEXT___XP_USED_VARS",
   ``!p. (XP_USED_VARS (XP_NEXT p) = (P_USED_VARS p)) /\
         (XP_USED_X_VARS (XP_NEXT p) = (P_USED_VARS p)) /\
         (XP_USED_CURRENT_VARS (XP_NEXT p) = EMPTY)``,

   INDUCT_THEN prop_logic_induct STRIP_ASSUME_TAC THEN
   ASM_REWRITE_TAC[XP_NEXT_def,
               XP_USED_CURRENT_VARS_def,
               XP_USED_VARS_def,
               XP_USED_X_VARS_def,
               UNION_EMPTY,
               P_USED_VARS_def] THEN
   METIS_TAC[]);


val XP_CURRENT___XP_USED_VARS=
 store_thm
  ("XP_CURRENT___XP_USED_VARS",
   ``!p. (XP_USED_VARS (XP_CURRENT p) = (P_USED_VARS p)) /\
         (XP_USED_X_VARS (XP_CURRENT p) = EMPTY) /\
         (XP_USED_CURRENT_VARS (XP_CURRENT p) = (P_USED_VARS p))``,

   INDUCT_THEN prop_logic_induct STRIP_ASSUME_TAC THEN
   ASM_REWRITE_TAC[XP_CURRENT_def,
               XP_USED_CURRENT_VARS_def,
               XP_USED_VARS_def,
               XP_USED_X_VARS_def,
               UNION_EMPTY,
               P_USED_VARS_def] THEN
   METIS_TAC[]);



val XP_USED_VARS_EVAL =
 store_thm
  ("XP_USED_VARS_EVAL",
   ``!p c b b1 b2 P. (
    (XP_USED_VARS (XP_TRUE) = {}) /\
    (XP_USED_VARS (XP_FALSE) = {}) /\
    (XP_USED_VARS (XP_PROP p) = {p}) /\
    (XP_USED_VARS (XP_NEXT_PROP p) = {p}) /\
    (XP_USED_VARS (XP_CURRENT P) = P_USED_VARS P) /\
    (XP_USED_VARS (XP_NEXT P) = P_USED_VARS P) /\
    (XP_USED_VARS (XP_NOT b) = XP_USED_VARS b) /\
    (XP_USED_VARS (XP_AND(b1, b2)) = XP_USED_VARS b1 UNION XP_USED_VARS b2) /\
    (XP_USED_VARS (XP_OR(b1, b2)) = XP_USED_VARS b1 UNION XP_USED_VARS b2) /\
    (XP_USED_VARS (XP_COND(c, b1, b2)) = XP_USED_VARS c UNION XP_USED_VARS b1 UNION XP_USED_VARS b2) /\
    (XP_USED_VARS (XP_IMPL(b1, b2)) = XP_USED_VARS b1 UNION XP_USED_VARS b2) /\
    (XP_USED_VARS (XP_EQUIV(b1, b2)) = XP_USED_VARS b1 UNION XP_USED_VARS b2) /\
    (XP_USED_CURRENT_VARS (XP_TRUE) = {}) /\
    (XP_USED_CURRENT_VARS (XP_FALSE) = {}) /\
    (XP_USED_CURRENT_VARS (XP_PROP p) = {p}) /\
    (XP_USED_CURRENT_VARS (XP_NEXT_PROP p) = {}) /\
    (XP_USED_CURRENT_VARS (XP_CURRENT P) = P_USED_VARS P) /\
    (XP_USED_CURRENT_VARS (XP_NEXT P) = {}) /\
    (XP_USED_CURRENT_VARS (XP_NOT b) = XP_USED_CURRENT_VARS b) /\
    (XP_USED_CURRENT_VARS (XP_AND(b1, b2)) = XP_USED_CURRENT_VARS b1 UNION XP_USED_CURRENT_VARS b2) /\
    (XP_USED_CURRENT_VARS (XP_OR(b1, b2)) = XP_USED_CURRENT_VARS b1 UNION XP_USED_CURRENT_VARS b2) /\
    (XP_USED_CURRENT_VARS (XP_COND(c, b1, b2)) = XP_USED_CURRENT_VARS c UNION XP_USED_CURRENT_VARS b1 UNION XP_USED_CURRENT_VARS b2) /\
    (XP_USED_CURRENT_VARS (XP_IMPL(b1, b2)) = XP_USED_CURRENT_VARS b1 UNION XP_USED_CURRENT_VARS b2) /\
    (XP_USED_CURRENT_VARS (XP_EQUIV(b1, b2)) = XP_USED_CURRENT_VARS b1 UNION XP_USED_CURRENT_VARS b2) /\
    (XP_USED_X_VARS (XP_TRUE) = {}) /\
    (XP_USED_X_VARS (XP_FALSE) = {}) /\
    (XP_USED_X_VARS (XP_PROP p) = {}) /\
    (XP_USED_X_VARS (XP_NEXT_PROP p) = {p}) /\
    (XP_USED_X_VARS (XP_CURRENT P) = {}) /\
    (XP_USED_X_VARS (XP_NEXT P) = P_USED_VARS P) /\
    (XP_USED_X_VARS (XP_NOT b) = XP_USED_X_VARS b) /\
    (XP_USED_X_VARS (XP_AND(b1, b2)) = XP_USED_X_VARS b1 UNION XP_USED_X_VARS b2) /\
    (XP_USED_X_VARS (XP_OR(b1, b2)) = XP_USED_X_VARS b1 UNION XP_USED_X_VARS b2) /\
    (XP_USED_X_VARS (XP_COND(c, b1, b2)) = XP_USED_X_VARS c UNION XP_USED_X_VARS b1 UNION XP_USED_X_VARS b2) /\
    (XP_USED_X_VARS (XP_IMPL(b1, b2)) = XP_USED_X_VARS b1 UNION XP_USED_X_VARS b2) /\
    (XP_USED_X_VARS (XP_EQUIV(b1, b2)) = XP_USED_X_VARS b1 UNION XP_USED_X_VARS b2)
   )``,

  REWRITE_TAC[XP_USED_VARS_def,
    XP_USED_X_VARS_def, XP_USED_CURRENT_VARS_def, UNION_EMPTY,
    XP_FALSE_def, XP_OR_def, XP_IMPL_def, XP_EQUIV_def,
    XP_NEXT___XP_USED_VARS, XP_CURRENT___XP_USED_VARS,
    XP_COND_def] THEN
  SIMP_TAC std_ss [EXTENSION, IN_UNION] THEN PROVE_TAC[]);



val XP_SEM___XP_NEXT =
 store_thm
  ("XP_SEM___XP_NEXT",

  ``!p s1 s2. (XP_SEM (XP_NEXT p) (s1, s2)) = (P_SEM s2 p)``,

  INDUCT_THEN prop_logic_induct ASSUME_TAC THENL [
     REWRITE_TAC[XP_NEXT_def, XP_SEM_THM, P_SEM_THM],

     REWRITE_TAC[XP_NEXT_def, XP_SEM_THM, P_SEM_THM],

     REWRITE_TAC[XP_NEXT_def, XP_SEM_THM, P_SEM_THM] THEN
     METIS_TAC[],

     REWRITE_TAC[XP_NEXT_def, XP_SEM_THM, P_SEM_THM] THEN
     METIS_TAC[]
  ]);


val XP_SEM___XP_CURRENT =
 store_thm
  ("XP_SEM___XP_CURRENT",

  ``!p s1 s2. (XP_SEM (XP_CURRENT p) (s1, s2)) = (P_SEM s1 p)``,

  INDUCT_THEN prop_logic_induct ASSUME_TAC THENL [
     REWRITE_TAC[XP_CURRENT_def, XP_SEM_THM, P_SEM_THM],

     REWRITE_TAC[XP_CURRENT_def, XP_SEM_THM, P_SEM_THM],

     REWRITE_TAC[XP_CURRENT_def, XP_SEM_THM, P_SEM_THM] THEN
     METIS_TAC[],

     REWRITE_TAC[XP_CURRENT_def, XP_SEM_THM, P_SEM_THM] THEN
     METIS_TAC[]
  ]);


val XP_BIGAND_SEM =
 store_thm
  ("XP_BIGAND_SEM",

    ``!l S1 S2. (XP_SEM (XP_BIGAND l) (S1,S2)) = (!e. (IS_EL e l) ==> XP_SEM e (S1,S2))``,

    Induct_on `l` THEN
    SIMP_TAC list_ss [XP_SEM_THM, XP_BIGAND_def] THEN
    PROVE_TAC[]);


val XP_BIGOR_SEM =
 store_thm
  ("XP_BIGOR_SEM",

    ``!l S1 S2. (XP_SEM (XP_BIGOR l) (S1,S2)) = (?e. (IS_EL e l) /\ XP_SEM e (S1,S2))``,

    Induct_on `l` THEN
    SIMP_TAC list_ss [XP_SEM_THM, XP_BIGOR_def] THEN
    PROVE_TAC[]);



val IS_CURRENT_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_def =
Define
`(IS_CURRENT_POSITIVE_PROP_FORMULA_SUBSET S XP_TRUE = T) /\
  (IS_CURRENT_POSITIVE_PROP_FORMULA_SUBSET S (XP_PROP a) = T) /\
  (IS_CURRENT_POSITIVE_PROP_FORMULA_SUBSET S (XP_NEXT_PROP a) = T) /\
  (IS_CURRENT_POSITIVE_PROP_FORMULA_SUBSET S (XP_NOT p') = IS_CURRENT_NEGATIVE_PROP_FORMULA_SUBSET S p') /\
  (IS_CURRENT_POSITIVE_PROP_FORMULA_SUBSET S (XP_AND(p', p'')) = (
    IS_CURRENT_POSITIVE_PROP_FORMULA_SUBSET S p' /\
    IS_CURRENT_POSITIVE_PROP_FORMULA_SUBSET S p'')) /\
  (IS_CURRENT_NEGATIVE_PROP_FORMULA_SUBSET S XP_TRUE = T) /\
  (IS_CURRENT_NEGATIVE_PROP_FORMULA_SUBSET S (XP_PROP a) = (~(a IN S))) /\
  (IS_CURRENT_NEGATIVE_PROP_FORMULA_SUBSET S (XP_NEXT_PROP a) = T) /\
  (IS_CURRENT_NEGATIVE_PROP_FORMULA_SUBSET S (XP_NOT p') = IS_CURRENT_POSITIVE_PROP_FORMULA_SUBSET S p') /\
  (IS_CURRENT_NEGATIVE_PROP_FORMULA_SUBSET S (XP_AND(p', p'')) = (
    IS_CURRENT_NEGATIVE_PROP_FORMULA_SUBSET S p' /\
    IS_CURRENT_NEGATIVE_PROP_FORMULA_SUBSET S p''))`;


val IS_CURRENT_POSITIVE_PROP_FORMULA_def =
Define
`IS_CURRENT_POSITIVE_PROP_FORMULA p =
  IS_CURRENT_POSITIVE_PROP_FORMULA_SUBSET UNIV p`;

val IS_CURRENT_NEGATIVE_PROP_FORMULA_def =
Define
`IS_CURRENT_NEGATIVE_PROP_FORMULA p =
  IS_CURRENT_NEGATIVE_PROP_FORMULA_SUBSET UNIV p`;



val IS_NEXT_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_def =
Define
`(IS_NEXT_POSITIVE_PROP_FORMULA_SUBSET S XP_TRUE = T) /\
  (IS_NEXT_POSITIVE_PROP_FORMULA_SUBSET S (XP_PROP a) = T) /\
  (IS_NEXT_POSITIVE_PROP_FORMULA_SUBSET S (XP_NEXT_PROP a) = T) /\
  (IS_NEXT_POSITIVE_PROP_FORMULA_SUBSET S (XP_NOT p') = IS_NEXT_NEGATIVE_PROP_FORMULA_SUBSET S p') /\
  (IS_NEXT_POSITIVE_PROP_FORMULA_SUBSET S (XP_AND(p', p'')) = (
    IS_NEXT_POSITIVE_PROP_FORMULA_SUBSET S p' /\
    IS_NEXT_POSITIVE_PROP_FORMULA_SUBSET S p'')) /\
  (IS_NEXT_NEGATIVE_PROP_FORMULA_SUBSET S XP_TRUE = T) /\
  (IS_NEXT_NEGATIVE_PROP_FORMULA_SUBSET S (XP_PROP a) = T) /\
  (IS_NEXT_NEGATIVE_PROP_FORMULA_SUBSET S (XP_NEXT_PROP a) = (~(a IN S))) /\
  (IS_NEXT_NEGATIVE_PROP_FORMULA_SUBSET S (XP_NOT p') = IS_NEXT_POSITIVE_PROP_FORMULA_SUBSET S p') /\
  (IS_NEXT_NEGATIVE_PROP_FORMULA_SUBSET S (XP_AND(p', p'')) = (
    IS_NEXT_NEGATIVE_PROP_FORMULA_SUBSET S p' /\
    IS_NEXT_NEGATIVE_PROP_FORMULA_SUBSET S p''))`;


val IS_NEXT_POSITIVE_PROP_FORMULA_def =
Define
`IS_NEXT_POSITIVE_PROP_FORMULA p =
  IS_NEXT_POSITIVE_PROP_FORMULA_SUBSET UNIV p`;

val IS_NEXT_NEGATIVE_PROP_FORMULA_def =
Define
`IS_NEXT_NEGATIVE_PROP_FORMULA p =
  IS_NEXT_NEGATIVE_PROP_FORMULA_SUBSET UNIV p`;



val IS_CURRENT_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_SEM =
 store_thm
  ("IS_CURRENT_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_SEM",
   ``!p V V' S S'. ((IS_CURRENT_POSITIVE_PROP_FORMULA_SUBSET V p /\ XP_SEM p (S, S') /\ V' SUBSET V) ==>
        (XP_SEM p ((S UNION V'), S'))) /\
      ((IS_CURRENT_NEGATIVE_PROP_FORMULA_SUBSET V p /\ XP_SEM p ((S UNION V'), S') /\ V' SUBSET V) ==>
        (XP_SEM p (S, S')))``,

    INDUCT_THEN xprop_logic_induct ASSUME_TAC THEN
    REWRITE_TAC[IS_CURRENT_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_def, XP_SEM_def, IN_UNION] THENL [
        PROVE_TAC[SUBSET_DEF],
        PROVE_TAC[],
        PROVE_TAC[],
        PROVE_TAC[]
    ]);


val IS_CURRENT_POSITIVE_NEGATIVE_PROP_FORMULA_SEM =
 store_thm
  ("IS_CURRENT_POSITIVE_NEGATIVE_PROP_FORMULA_SEM",
   ``!p S S' S''. ((IS_CURRENT_POSITIVE_PROP_FORMULA p /\ XP_SEM p (S, S'') /\ S SUBSET S') ==>
        (XP_SEM p (S', S''))) /\
      ((IS_CURRENT_NEGATIVE_PROP_FORMULA p /\ XP_SEM p (S', S'') /\ S SUBSET S') ==>
        (XP_SEM p (S, S'')))``,

    REWRITE_TAC[IS_CURRENT_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_def,
        IS_CURRENT_POSITIVE_PROP_FORMULA_def,
        IS_CURRENT_NEGATIVE_PROP_FORMULA_def] THEN
    REPEAT GEN_TAC THEN
    Cases_on `S SUBSET S'` THEN ASM_REWRITE_TAC[] THEN
    `?V'. V' = S' DIFF S` by PROVE_TAC[] THEN
    `S' = S UNION V'` by (ASM_SIMP_TAC std_ss [UNION_DEF, DIFF_DEF,
        GSPECIFICATION, EXTENSION] THEN PROVE_TAC[SUBSET_DEF]) THEN
    PROVE_TAC[IS_CURRENT_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_SEM,
        SUBSET_UNIV]);




val IS_NEXT_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_SEM =
 store_thm
  ("IS_NEXT_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_SEM",
   ``!p V V' S S'. ((IS_NEXT_POSITIVE_PROP_FORMULA_SUBSET V p /\ XP_SEM p (S', S) /\ V' SUBSET V) ==>
        (XP_SEM p (S', (S UNION V')))) /\
      ((IS_NEXT_NEGATIVE_PROP_FORMULA_SUBSET V p /\ XP_SEM p (S', (S UNION V')) /\ V' SUBSET V) ==>
        (XP_SEM p (S', S)))``,

    INDUCT_THEN xprop_logic_induct ASSUME_TAC THEN
    REWRITE_TAC[IS_NEXT_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_def, XP_SEM_def, IN_UNION] THENL [
        PROVE_TAC[],
        PROVE_TAC[SUBSET_DEF],
        PROVE_TAC[],
        PROVE_TAC[]
    ]);




val IS_NEXT_POSITIVE_NEGATIVE_PROP_FORMULA_SEM =
 store_thm
  ("IS_NEXT_POSITIVE_NEGATIVE_PROP_FORMULA_SEM",
   ``!p S S' S''. ((IS_NEXT_POSITIVE_PROP_FORMULA p /\ XP_SEM p (S'', S) /\ S SUBSET S') ==>
        (XP_SEM p (S'', S'))) /\
      ((IS_NEXT_NEGATIVE_PROP_FORMULA p /\ XP_SEM p (S'', S') /\ S SUBSET S') ==>
        (XP_SEM p (S'', S)))``,

    REWRITE_TAC[IS_NEXT_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_def,
        IS_NEXT_POSITIVE_PROP_FORMULA_def,
        IS_NEXT_NEGATIVE_PROP_FORMULA_def] THEN
    REPEAT GEN_TAC THEN
    Cases_on `S SUBSET S'` THEN ASM_REWRITE_TAC[] THEN
    `?V'. V' = S' DIFF S` by PROVE_TAC[] THEN
    `S' = S UNION V'` by (ASM_SIMP_TAC std_ss [UNION_DEF, DIFF_DEF,
        GSPECIFICATION, EXTENSION] THEN PROVE_TAC[SUBSET_DEF]) THEN
    PROVE_TAC[IS_NEXT_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_SEM,
        SUBSET_UNIV]);


val XP_ASSIGN_TRUE_def =
Define
`(XP_ASSIGN_TRUE V V' (XP_PROP p) = (if p IN V then XP_TRUE else XP_PROP p)) /\
  (XP_ASSIGN_TRUE V V' (XP_NEXT_PROP p) = (if p IN V' then XP_TRUE else XP_NEXT_PROP p)) /\
  (XP_ASSIGN_TRUE V V' XP_TRUE = XP_TRUE) /\
  (XP_ASSIGN_TRUE V V' (XP_NOT b) = XP_NOT(XP_ASSIGN_TRUE V V' b)) /\
  (XP_ASSIGN_TRUE V V' (XP_AND(b1,b2)) = XP_AND (
        XP_ASSIGN_TRUE V V' b1,
        XP_ASSIGN_TRUE V V' b2))`;

val XP_ASSIGN_FALSE_def =
Define
`(XP_ASSIGN_FALSE V V' (XP_PROP p) = (if p IN V then XP_FALSE else XP_PROP p)) /\
  (XP_ASSIGN_FALSE V V' (XP_NEXT_PROP p) = (if p IN V' then XP_FALSE else XP_NEXT_PROP p)) /\
  (XP_ASSIGN_FALSE V V' XP_TRUE = XP_TRUE) /\
  (XP_ASSIGN_FALSE V V' (XP_NOT b) = XP_NOT(XP_ASSIGN_FALSE V V' b)) /\
  (XP_ASSIGN_FALSE V V' (XP_AND(b1,b2)) = XP_AND (
        XP_ASSIGN_FALSE V V' b1,
        XP_ASSIGN_FALSE V V' b2))`;

val XP_ASSIGN_TRUE_SEM =
 store_thm
  ("XP_ASSIGN_TRUE_SEM",

    ``!p s s' V V'. XP_SEM (XP_ASSIGN_TRUE V V' p) (s, s') =
        XP_SEM p ((s UNION V), (s' UNION V'))``,

    INDUCT_THEN xprop_logic_induct ASSUME_TAC THEN
    ASM_REWRITE_TAC[XP_ASSIGN_TRUE_def, XP_SEM_def] THEN
    REWRITE_TAC[IN_UNION] THENL [
        Cases_on `a IN V`,
        Cases_on `a IN V'`
    ] THEN
    REWRITE_TAC[XP_SEM_def]
);


val XP_ASSIGN_FALSE_SEM =
 store_thm
  ("XP_ASSIGN_FALSE_SEM",

    ``!p s s' V V'. XP_SEM (XP_ASSIGN_FALSE V V' p) (s, s') =
        XP_SEM p ((s DIFF V), (s' DIFF V'))``,

    INDUCT_THEN xprop_logic_induct ASSUME_TAC THEN
    ASM_REWRITE_TAC[XP_ASSIGN_FALSE_def, XP_SEM_def] THEN
    REWRITE_TAC[IN_DIFF] THENL [
        Cases_on `a IN V`,
        Cases_on `a IN V'`
    ] THEN
    REWRITE_TAC[XP_SEM_THM]);


val XP_CURRENT_EXISTS_def =
Define
`(XP_CURRENT_EXISTS [] p = p) /\
  (XP_CURRENT_EXISTS (v::l) p = XP_CURRENT_EXISTS l (XP_OR(XP_ASSIGN_TRUE {v} {} p, XP_ASSIGN_FALSE {v} {} p)))`;

val XP_NEXT_EXISTS_def =
Define
`(XP_NEXT_EXISTS [] p = p) /\
  (XP_NEXT_EXISTS (v::l) p = XP_NEXT_EXISTS l (XP_OR(XP_ASSIGN_TRUE {} {v} p, XP_ASSIGN_FALSE {} {v} p)))`;


val XP_CURRENT_FORALL_def =
Define
`(XP_CURRENT_FORALL l p = XP_NOT (XP_CURRENT_EXISTS l (XP_NOT p)))`;


val XP_NEXT_FORALL_def =
Define
`(XP_NEXT_FORALL l p = XP_NOT (XP_NEXT_EXISTS l (XP_NOT p)))`;


val XP_CURRENT_EXISTS_SEM =
 store_thm
  ("XP_CURRENT_EXISTS_SEM",

    ``!s s' l p. (XP_SEM (XP_CURRENT_EXISTS l p) (s, s') =
        (?l'. (l' SUBSET (LIST_TO_SET l)) /\ (XP_SEM p (((s DIFF (LIST_TO_SET l)) UNION l'), s'))))``,

    Induct_on `l` THENL [
        SIMP_TAC list_ss [LIST_TO_SET_THM, SUBSET_EMPTY, XP_CURRENT_EXISTS_def, UNION_EMPTY,
            DIFF_EMPTY],

        ASM_SIMP_TAC list_ss [XP_CURRENT_EXISTS_def, LIST_TO_SET_THM, XP_SEM_THM, XP_ASSIGN_TRUE_SEM,
            XP_ASSIGN_FALSE_SEM] THEN
        REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
            EXISTS_TAC ``h INSERT l'`` THEN
            REPEAT STRIP_TAC THENL [
                FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT] THEN PROVE_TAC[],

                `s DIFF (h INSERT LIST_TO_SET l) UNION (h INSERT l') =
                s DIFF LIST_TO_SET l UNION l' UNION {h}` by
                (SIMP_TAC std_ss [INSERT_DEF, UNION_DEF, DIFF_DEF, GSPECIFICATION, EXTENSION,
                    NOT_IN_EMPTY] THEN
                PROVE_TAC[]) THEN
                FULL_SIMP_TAC std_ss [UNION_EMPTY]
            ],

            EXISTS_TAC ``l' DELETE h`` THEN
            REPEAT STRIP_TAC THENL [
                FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_DELETE, IN_INSERT],

                `s DIFF (h INSERT LIST_TO_SET l) UNION (l' DELETE h) =
                s DIFF LIST_TO_SET l UNION l' DIFF {h}` by
                    (SIMP_TAC std_ss [INSERT_DEF, UNION_DEF, DIFF_DEF, GSPECIFICATION, EXTENSION,
                        NOT_IN_EMPTY, DELETE_DEF] THEN
                    PROVE_TAC[]) THEN
                FULL_SIMP_TAC std_ss [DIFF_EMPTY]
            ],

            EXISTS_TAC ``l' DELETE h`` THEN
            REPEAT STRIP_TAC THENL [
                FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT, IN_DELETE] THEN PROVE_TAC[],

                `(s DIFF LIST_TO_SET l UNION (l' DELETE h) UNION {h} =
                s DIFF (h INSERT LIST_TO_SET l) UNION l') \/
                (s DIFF LIST_TO_SET l UNION (l' DELETE h) DIFF {h} =
                s DIFF (h INSERT LIST_TO_SET l) UNION l')` by
                    (SIMP_TAC std_ss [INSERT_DEF, UNION_DEF, DIFF_DEF, GSPECIFICATION, EXTENSION,
                        NOT_IN_EMPTY, DELETE_DEF] THEN
                    METIS_TAC[]) THEN
                FULL_SIMP_TAC std_ss [UNION_EMPTY, DIFF_EMPTY]
            ]
        ]
    ]);


val XP_NEXT_EXISTS_SEM =
 store_thm
  ("XP_NEXT_EXISTS_SEM",

    ``!s s' l p. (XP_SEM (XP_NEXT_EXISTS l p) (s', s) =
        (?l'. (l' SUBSET (LIST_TO_SET l)) /\ (XP_SEM p (s', ((s DIFF (LIST_TO_SET l)) UNION l')))))``,

    Induct_on `l` THENL [
        SIMP_TAC list_ss [LIST_TO_SET_THM, SUBSET_EMPTY, XP_NEXT_EXISTS_def, UNION_EMPTY,
            DIFF_EMPTY],

        ASM_SIMP_TAC list_ss [XP_NEXT_EXISTS_def, LIST_TO_SET_THM, XP_SEM_THM, XP_ASSIGN_TRUE_SEM,
            XP_ASSIGN_FALSE_SEM] THEN
        REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
            EXISTS_TAC ``h INSERT l'`` THEN
            REPEAT STRIP_TAC THENL [
                FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT] THEN PROVE_TAC[],

                `s DIFF (h INSERT LIST_TO_SET l) UNION (h INSERT l') =
                s DIFF LIST_TO_SET l UNION l' UNION {h}` by
                (SIMP_TAC std_ss [INSERT_DEF, UNION_DEF, DIFF_DEF, GSPECIFICATION, EXTENSION,
                    NOT_IN_EMPTY] THEN
                PROVE_TAC[]) THEN
                FULL_SIMP_TAC std_ss [UNION_EMPTY]
            ],

            EXISTS_TAC ``l' DELETE h`` THEN
            REPEAT STRIP_TAC THENL [
                FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_DELETE, IN_INSERT],

                `s DIFF (h INSERT LIST_TO_SET l) UNION (l' DELETE h) =
                s DIFF LIST_TO_SET l UNION l' DIFF {h}` by
                    (SIMP_TAC std_ss [INSERT_DEF, UNION_DEF, DIFF_DEF, GSPECIFICATION, EXTENSION,
                        NOT_IN_EMPTY, DELETE_DEF] THEN
                    PROVE_TAC[]) THEN
                FULL_SIMP_TAC std_ss [DIFF_EMPTY]
            ],

            EXISTS_TAC ``l' DELETE h`` THEN
            REPEAT STRIP_TAC THENL [
                FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT, IN_DELETE] THEN PROVE_TAC[],

                `(s DIFF LIST_TO_SET l UNION (l' DELETE h) UNION {h} =
                s DIFF (h INSERT LIST_TO_SET l) UNION l') \/
                (s DIFF LIST_TO_SET l UNION (l' DELETE h) DIFF {h} =
                s DIFF (h INSERT LIST_TO_SET l) UNION l')` by
                    (SIMP_TAC std_ss [INSERT_DEF, UNION_DEF, DIFF_DEF, GSPECIFICATION, EXTENSION,
                        NOT_IN_EMPTY, DELETE_DEF] THEN
                    METIS_TAC[]) THEN
                FULL_SIMP_TAC std_ss [UNION_EMPTY, DIFF_EMPTY]
            ]
        ]
    ]);


val XP_CURRENT_FORALL_SEM =
 store_thm
  ("XP_CURRENT_FORALL_SEM",

    ``!s s' l p. (XP_SEM (XP_CURRENT_FORALL l p) (s, s')) =
        (!l'. (l' SUBSET (LIST_TO_SET l)) ==> (XP_SEM p (((s DIFF (LIST_TO_SET l)) UNION l'), s')))``,

    REWRITE_TAC[XP_CURRENT_FORALL_def, XP_SEM_THM, XP_CURRENT_EXISTS_SEM] THEN
    PROVE_TAC[]);


val XP_NEXT_FORALL_SEM =
 store_thm
  ("XP_NEXT_FORALL_SEM",

    ``!s s' l p. (XP_SEM (XP_NEXT_FORALL l p) (s, s')) =
        (!l'. (l' SUBSET (LIST_TO_SET l)) ==> (XP_SEM p (s, ((s' DIFF (LIST_TO_SET l)) UNION l'))))``,

    REWRITE_TAC[XP_NEXT_FORALL_def, XP_SEM_THM, XP_NEXT_EXISTS_SEM] THEN
    PROVE_TAC[]);



(*****************************************************************************
 * Variable renamings
 *****************************************************************************)
val FINITE___XP_USED_CURRENT_VARS =
 store_thm
  ("FINITE___XP_USED_CURRENT_VARS",

  ``!p. FINITE(XP_USED_CURRENT_VARS p)``,

  INDUCT_THEN xprop_logic_induct ASSUME_TAC THENL [
      REWRITE_TAC[XP_USED_CURRENT_VARS_def, FINITE_SING],
      REWRITE_TAC[XP_USED_CURRENT_VARS_def, FINITE_EMPTY],
      REWRITE_TAC[XP_USED_CURRENT_VARS_def, FINITE_EMPTY],
      ASM_REWRITE_TAC[XP_USED_CURRENT_VARS_def],
      ASM_REWRITE_TAC[XP_USED_CURRENT_VARS_def, FINITE_UNION]
  ]);


val FINITE___XP_USED_X_VARS =
 store_thm
  ("FINITE___XP_USED_X_VARS",

  ``!p. FINITE(XP_USED_X_VARS p)``,

  INDUCT_THEN xprop_logic_induct ASSUME_TAC THENL [
      REWRITE_TAC[XP_USED_X_VARS_def, FINITE_EMPTY],
      REWRITE_TAC[XP_USED_X_VARS_def, FINITE_SING],
      REWRITE_TAC[XP_USED_X_VARS_def, FINITE_EMPTY],
      ASM_REWRITE_TAC[XP_USED_X_VARS_def],
      ASM_REWRITE_TAC[XP_USED_X_VARS_def, FINITE_UNION]
  ]);


val FINITE___XP_USED_VARS =
 store_thm
  ("FINITE___XP_USED_VARS",

  ``!p. FINITE(XP_USED_VARS p)``,

  REWRITE_TAC[XP_USED_VARS_def, FINITE___XP_USED_X_VARS, FINITE___XP_USED_CURRENT_VARS, FINITE_UNION]);


val XP_VAR_RENAMING___USED_CURRENT_VARS =
 store_thm
  ("XP_VAR_RENAMING___USED_CURRENT_VARS",

   ``!a f. (XP_USED_CURRENT_VARS (XP_VAR_RENAMING f a) =
       (IMAGE f (XP_USED_CURRENT_VARS a)))``,

   INDUCT_THEN xprop_logic_induct ASSUME_TAC THENL [

      SIMP_TAC std_ss [XP_USED_CURRENT_VARS_def,
                  XP_VAR_RENAMING_def,
                  IMAGE_DEF,
                  EXTENSION,
                  GSPECIFICATION,
                  IN_SING,
                  EXISTS_PROD],

      REWRITE_TAC [XP_USED_CURRENT_VARS_def, XP_VAR_RENAMING_def, IMAGE_EMPTY],                                         REWRITE_TAC [XP_USED_CURRENT_VARS_def, XP_VAR_RENAMING_def, IMAGE_EMPTY],
      ASM_REWRITE_TAC [XP_USED_CURRENT_VARS_def, XP_VAR_RENAMING_def],
      ASM_REWRITE_TAC [XP_USED_CURRENT_VARS_def, XP_VAR_RENAMING_def, IMAGE_UNION]
   ]);


val XP_VAR_RENAMING___USED_X_VARS =
 store_thm
  ("XP_VAR_RENAMING___USED_X_VARS",

   ``!a f. (XP_USED_X_VARS (XP_VAR_RENAMING f a) =
       (IMAGE f (XP_USED_X_VARS a)))``,

   INDUCT_THEN xprop_logic_induct ASSUME_TAC THENL [

      REWRITE_TAC [XP_USED_X_VARS_def, XP_VAR_RENAMING_def, IMAGE_EMPTY],

      SIMP_TAC std_ss [XP_USED_X_VARS_def,
                  XP_VAR_RENAMING_def,
                  IMAGE_DEF,
                  EXTENSION,
                  GSPECIFICATION,
                  IN_SING],

      REWRITE_TAC [XP_USED_X_VARS_def, XP_VAR_RENAMING_def, IMAGE_EMPTY],
      ASM_REWRITE_TAC [XP_USED_X_VARS_def, XP_VAR_RENAMING_def],
      ASM_REWRITE_TAC [XP_USED_X_VARS_def, XP_VAR_RENAMING_def, IMAGE_UNION]
   ]);


val XP_VAR_RENAMING___USED_VARS =
 store_thm
  ("XP_VAR_RENAMING___USED_VARS",

   ``!a f. (XP_USED_VARS (XP_VAR_RENAMING f a) =
       (IMAGE f (XP_USED_VARS a)))``,

   REWRITE_TAC[XP_USED_VARS_def, IMAGE_UNION,
               XP_VAR_RENAMING___USED_CURRENT_VARS, XP_VAR_RENAMING___USED_X_VARS]);



val XP_USED_VARS_INTER_SUBSET_THM =
 store_thm
  ("XP_USED_VARS_INTER_SUBSET_THM",
   ``!b S s1 s2.
      (((XP_USED_X_VARS b) SUBSET S) ==>
       ((XP_SEM b (s1, s2)) = (XP_SEM b (s1, s2 INTER S)))) /\

      (((XP_USED_CURRENT_VARS b) SUBSET S) ==>
       ((XP_SEM b (s1, s2)) = (XP_SEM b (s1 INTER S, s2))))``,

   INDUCT_THEN xprop_logic_induct ASSUME_TAC THENL [
     SIMP_TAC std_ss [XP_USED_X_VARS_def, XP_USED_CURRENT_VARS_def, EMPTY_SUBSET, XP_SEM_def, IN_INTER,
        SUBSET_DEF, IN_SING],

     SIMP_TAC std_ss [XP_USED_X_VARS_def, XP_USED_CURRENT_VARS_def, EMPTY_SUBSET, XP_SEM_def, IN_INTER,
        SUBSET_DEF, IN_SING],

     SIMP_TAC std_ss [XP_SEM_def],
     ASM_SIMP_TAC std_ss [XP_SEM_def, XP_USED_X_VARS_def, XP_USED_CURRENT_VARS_def],

     ASM_SIMP_TAC std_ss [XP_SEM_def, XP_USED_X_VARS_def, XP_USED_CURRENT_VARS_def, UNION_SUBSET] THEN
     PROVE_TAC[]
   ]);


val XP_USED_VARS_INTER_THM =
 store_thm
  ("XP_USED_VARS_INTER_THM",
   ``!b s1 s2.
       ((XP_SEM b (s1, s2)) = (XP_SEM b (s1 INTER (XP_USED_CURRENT_VARS b), s2 INTER (XP_USED_X_VARS b))))``,

   PROVE_TAC[XP_USED_VARS_INTER_SUBSET_THM, SUBSET_REFL]);


val XP_USED_VARS_INTER_SUBSET_BOTH_THM =
 store_thm
  ("XP_USED_VARS_INTER_SUBSET_BOTH_THM",
   ``!b S s1 s2.
      ((XP_USED_VARS b) SUBSET S) ==>
      ((XP_SEM b (s1, s2)) = (XP_SEM b (s1 INTER S, s2 INTER S)))``,

    REWRITE_TAC[XP_USED_VARS_def, UNION_SUBSET] THEN
    METIS_TAC[XP_USED_VARS_INTER_SUBSET_THM]);


val XP_SEM___VAR_RENAMING___NOT_INJ =
  store_thm (
    "XP_SEM___VAR_RENAMING___NOT_INJ",
      ``!p f s1 s2. XP_SEM (XP_VAR_RENAMING f p) (s1, s2) = XP_SEM p
        ((\x. f x IN s1), (\x. f x IN s2))``,

    INDUCT_THEN xprop_logic_induct ASSUME_TAC THEN (
      ASM_SIMP_TAC std_ss [XP_VAR_RENAMING_def, XP_SEM_def, IN_ABS]
    ));

val XP_SEM___VAR_RENAMING =
 store_thm
  ("XP_SEM___VAR_RENAMING",
   ``!p f s1 s2. (INJ f (s1 UNION s2 UNION XP_USED_VARS p) UNIV) ==> ((XP_SEM p (s1,s2)) = (XP_SEM (XP_VAR_RENAMING f p) (IMAGE f s1, IMAGE f s2)))``,

   INDUCT_THEN xprop_logic_induct ASSUME_TAC THEN REPEAT STRIP_TAC THENL [
      SIMP_ALL_TAC std_ss [INJ_DEF, IMAGE_DEF, IN_UNIV, IN_UNION, XP_SEM_def, XP_VAR_RENAMING_def, GSPECIFICATION,
        XP_USED_VARS_def, XP_USED_CURRENT_VARS_def, IN_SING] THEN
      PROVE_TAC[],

      SIMP_ALL_TAC std_ss [INJ_DEF, IMAGE_DEF, IN_UNIV, IN_UNION, XP_SEM_def, XP_VAR_RENAMING_def, GSPECIFICATION,
        XP_USED_VARS_def, XP_USED_X_VARS_def, IN_SING] THEN
      PROVE_TAC[],

      SIMP_TAC std_ss [XP_SEM_def, XP_VAR_RENAMING_def],

      FULL_SIMP_TAC std_ss [XP_SEM_def, XP_VAR_RENAMING_def, XP_USED_VARS_def, XP_USED_CURRENT_VARS_def,
        XP_USED_X_VARS_def],

      FULL_SIMP_TAC std_ss [XP_SEM_def, XP_VAR_RENAMING_def, XP_USED_VARS_def, XP_USED_CURRENT_VARS_def,
        XP_USED_X_VARS_def] THEN
      SUBGOAL_TAC `(s1 UNION s2 UNION (XP_USED_CURRENT_VARS p UNION XP_USED_X_VARS p)) SUBSET
             (s1 UNION s2 UNION (XP_USED_CURRENT_VARS p UNION XP_USED_CURRENT_VARS p' UNION
              (XP_USED_X_VARS p UNION XP_USED_X_VARS p'))) /\

             (s1 UNION s2 UNION (XP_USED_CURRENT_VARS p' UNION XP_USED_X_VARS p')) SUBSET
             (s1 UNION s2 UNION (XP_USED_CURRENT_VARS p UNION XP_USED_CURRENT_VARS p' UNION
              (XP_USED_X_VARS p UNION XP_USED_X_VARS p')))` THEN1 (

        SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
        PROVE_TAC[]
      ) THEN
      PROVE_TAC[INJ_SUBSET, SUBSET_REFL]
   ]);


val XP_VAR_RENAMING_EVAL =
 store_thm
  ("XP_VAR_RENAMING_EVAL",
   ``!p f b b1 b2. (
    (XP_VAR_RENAMING f (XP_TRUE) = XP_TRUE) /\
    (XP_VAR_RENAMING f (XP_FALSE) = XP_FALSE) /\
    (XP_VAR_RENAMING f (XP_PROP p) = (XP_PROP (f p))) /\
    (XP_VAR_RENAMING f (XP_NEXT_PROP p) = (XP_NEXT_PROP (f p))) /\
    (XP_VAR_RENAMING f (XP_NOT b) = XP_NOT(XP_VAR_RENAMING f b)) /\
    (XP_VAR_RENAMING f (XP_AND(b1, b2)) = XP_AND(XP_VAR_RENAMING f b1, XP_VAR_RENAMING f b2)) /\
    (XP_VAR_RENAMING f (XP_OR(b1, b2)) = XP_OR(XP_VAR_RENAMING f b1, XP_VAR_RENAMING f b2)) /\
    (XP_VAR_RENAMING f (XP_IMPL(b1, b2)) = XP_IMPL(XP_VAR_RENAMING f b1, XP_VAR_RENAMING f b2)) /\
    (XP_VAR_RENAMING f (XP_EQUIV(b1, b2)) = XP_EQUIV(XP_VAR_RENAMING f b1, XP_VAR_RENAMING f  b2))
   )``,

  REWRITE_TAC[XP_VAR_RENAMING_def, XP_FALSE_def, XP_OR_def, XP_IMPL_def, XP_EQUIV_def]);


val XP_PROP_SET_MODEL_SEM =
 store_thm
  ("XP_PROP_SET_MODEL_SEM",
    ``!S1 S2 S' T1 T2. FINITE S' ==> ((XP_SEM (XP_PROP_SET_MODEL S1 S2 S') (T1,T2)) = ((T1 INTER S' = S1 INTER S') /\ (T2 INTER S' = S2 INTER S')))``,

    REWRITE_TAC[XP_PROP_SET_MODEL_def, XP_SEM_THM,
        XP_SEM___XP_CURRENT, XP_SEM___XP_NEXT] THEN
    PROVE_TAC[P_PROP_SET_MODEL_SEM]);


val XP_PROP_SET_MODEL_CURRENT_SEM =
 store_thm
  ("XP_PROP_SET_MODEL_CURRENT_SEM",
    ``!f S' T1 T2. FINITE S' ==> ((XP_SEM (XP_PROP_SET_MODEL_CURRENT f S') (T1,T2)) = ((T1 INTER S') = (f (T2 INTER S') INTER S')))``,

    REWRITE_TAC[XP_PROP_SET_MODEL_CURRENT_def, XP_SEM_THM,
        XP_BIGOR_SEM] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [FINITE_POW_IFF, IMAGE_FINITE,
        MEM_SET_TO_LIST, IN_IMAGE, GSYM LEFT_EXISTS_AND_THM,
        XP_SEM_THM, XP_SEM___XP_CURRENT, XP_SEM___XP_NEXT,
        P_PROP_SET_MODEL_SEM, IN_POW
        ] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL  [
        ASM_REWRITE_TAC[],

        EXISTS_TAC ``T2 INTER S'`` THEN
        ASM_REWRITE_TAC[INTER_INTER_ABSORPTION,
            INTER_SUBSET]
    ]);


val XP_PROP_SET_MODEL_NEXT_SEM =
 store_thm
  ("XP_PROP_SET_MODEL_NEXT_SEM",
    ``!f S' T1 T2. FINITE S' ==> ((XP_SEM (XP_PROP_SET_MODEL_NEXT f S') (T1,T2)) = ((T2 INTER S') = (f (T1 INTER S') INTER S')))``,

    REWRITE_TAC[XP_PROP_SET_MODEL_NEXT_def, XP_SEM_THM,
        XP_BIGOR_SEM] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [FINITE_POW_IFF, IMAGE_FINITE,
        MEM_SET_TO_LIST, IN_IMAGE, GSYM LEFT_EXISTS_AND_THM,
        XP_SEM_THM, XP_SEM___XP_CURRENT, XP_SEM___XP_NEXT,
        P_PROP_SET_MODEL_SEM, IN_POW
        ] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL  [
        ASM_REWRITE_TAC[],

        EXISTS_TAC ``T1 INTER S'`` THEN
        ASM_REWRITE_TAC[INTER_INTER_ABSORPTION,
            INTER_SUBSET]
    ]);




val XP_ASSIGN_TRUE_FALSE___XP_USED_VARS =
  store_thm ("XP_ASSIGN_TRUE_FALSE___XP_USED_VARS",
    ``!xp v1 v2.
    (XP_USED_CURRENT_VARS (XP_ASSIGN_TRUE v1 v2 xp) =
    XP_USED_CURRENT_VARS xp DIFF v1) /\
    (XP_USED_X_VARS (XP_ASSIGN_TRUE v1 v2 xp) =
    XP_USED_X_VARS xp DIFF v2) /\
    (XP_USED_CURRENT_VARS (XP_ASSIGN_FALSE v1 v2 xp) =
    XP_USED_CURRENT_VARS xp DIFF v1) /\
    (XP_USED_X_VARS (XP_ASSIGN_FALSE v1 v2 xp) =
    XP_USED_X_VARS xp DIFF v2)``,

    INDUCT_THEN xprop_logic_induct ASSUME_TAC THENL [
      REWRITE_TAC [XP_ASSIGN_TRUE_def, XP_ASSIGN_FALSE_def] THEN
      REPEAT GEN_TAC THEN
      Cases_on `a IN v1` THEN (
        ASM_SIMP_TAC std_ss [XP_USED_VARS_EVAL, EXTENSION, IN_DIFF,
          IN_SING, NOT_IN_EMPTY] THEN
        PROVE_TAC[]
      ),


      REWRITE_TAC [XP_ASSIGN_TRUE_def, XP_ASSIGN_FALSE_def] THEN
      REPEAT GEN_TAC THEN
      Cases_on `a IN v2` THEN (
        ASM_SIMP_TAC std_ss [XP_USED_VARS_EVAL, EXTENSION, IN_DIFF,
          IN_SING, NOT_IN_EMPTY] THEN
        PROVE_TAC[]
      ),

      SIMP_TAC std_ss [XP_ASSIGN_TRUE_def, XP_USED_VARS_EVAL, EMPTY_DIFF,
                       XP_ASSIGN_FALSE_def],

      ASM_SIMP_TAC std_ss [XP_ASSIGN_TRUE_def, XP_ASSIGN_FALSE_def, XP_USED_VARS_EVAL],

      ASM_SIMP_TAC std_ss [XP_ASSIGN_TRUE_def, XP_ASSIGN_FALSE_def, XP_USED_VARS_EVAL, UNION_OVER_DIFF]
    ]);


val XP_ASSIGN_TRUE_FALSE___EVAL =
  store_thm ("XP_ASSIGN_TRUE_FALSE___EVAL",
    ``(XP_ASSIGN_TRUE V V' (XP_PROP p) = (if p IN V then XP_TRUE else XP_PROP p)) /\
      (XP_ASSIGN_TRUE V V' (XP_NEXT_PROP p) = (if p IN V' then XP_TRUE else XP_NEXT_PROP p)) /\
      (XP_ASSIGN_TRUE V V' XP_TRUE = XP_TRUE) /\
      (XP_ASSIGN_TRUE V V' XP_FALSE = XP_FALSE) /\
      (XP_ASSIGN_TRUE V V' (XP_NOT b) = XP_NOT(XP_ASSIGN_TRUE V V' b)) /\
      (XP_ASSIGN_TRUE V V' (XP_AND(b1,b2)) = XP_AND (XP_ASSIGN_TRUE V V' b1, XP_ASSIGN_TRUE V V' b2)) /\
      (XP_ASSIGN_TRUE V V' (XP_OR(b1,b2)) = XP_OR (XP_ASSIGN_TRUE V V' b1, XP_ASSIGN_TRUE V V' b2)) /\
      (XP_ASSIGN_TRUE V V' (XP_IMPL(b1,b2)) = XP_IMPL (XP_ASSIGN_TRUE V V' b1, XP_ASSIGN_TRUE V V' b2)) /\
      (XP_ASSIGN_TRUE V V' (XP_COND(c, b1,b2)) = XP_COND (XP_ASSIGN_TRUE V V' c, XP_ASSIGN_TRUE V V' b1, XP_ASSIGN_TRUE V V' b2)) /\
      (XP_ASSIGN_TRUE V V' (XP_EQUIV (b1,b2)) = XP_EQUIV (XP_ASSIGN_TRUE V V' b1, XP_ASSIGN_TRUE V V' b2)) /\

      (XP_ASSIGN_FALSE V V' (XP_PROP p) = (if p IN V then XP_FALSE else XP_PROP p)) /\
      (XP_ASSIGN_FALSE V V' (XP_NEXT_PROP p) = (if p IN V' then XP_FALSE else XP_NEXT_PROP p)) /\
      (XP_ASSIGN_FALSE V V' XP_TRUE = XP_TRUE) /\
      (XP_ASSIGN_FALSE V V' XP_FALSE = XP_FALSE) /\
      (XP_ASSIGN_FALSE V V' (XP_NOT b) = XP_NOT(XP_ASSIGN_FALSE V V' b)) /\
      (XP_ASSIGN_FALSE V V' (XP_AND(b1,b2)) = XP_AND (XP_ASSIGN_FALSE V V' b1, XP_ASSIGN_FALSE V V' b2)) /\
      (XP_ASSIGN_FALSE V V' (XP_OR(b1,b2)) = XP_OR (XP_ASSIGN_FALSE V V' b1, XP_ASSIGN_FALSE V V' b2)) /\
      (XP_ASSIGN_FALSE V V' (XP_IMPL(b1,b2)) = XP_IMPL (XP_ASSIGN_FALSE V V' b1, XP_ASSIGN_FALSE V V' b2)) /\
      (XP_ASSIGN_FALSE V V' (XP_COND(c, b1,b2)) = XP_COND (XP_ASSIGN_FALSE V V' c, XP_ASSIGN_FALSE V V' b1, XP_ASSIGN_FALSE V V' b2)) /\
      (XP_ASSIGN_FALSE V V' (XP_EQUIV(b1,b2)) = XP_EQUIV (XP_ASSIGN_FALSE V V' b1, XP_ASSIGN_FALSE V V' b2))``,

  SIMP_TAC std_ss [XP_ASSIGN_TRUE_def, XP_ASSIGN_FALSE_def, XP_FALSE_def, XP_EQUIV_def, XP_IMPL_def, XP_OR_def, XP_COND_def]);


val XP_EXISTS___XP_USED_VARS =
  store_thm ("XP_EXISTS___XP_USED_VARS",
    ``!l p.
      (XP_USED_CURRENT_VARS (XP_CURRENT_EXISTS l p) =
      XP_USED_CURRENT_VARS p DIFF (LIST_TO_SET l)) /\
      (XP_USED_X_VARS (XP_CURRENT_EXISTS l p) =
      XP_USED_X_VARS p) /\
      (XP_USED_X_VARS (XP_NEXT_EXISTS l p) =
      XP_USED_X_VARS p DIFF (LIST_TO_SET l)) /\
      (XP_USED_CURRENT_VARS (XP_NEXT_EXISTS l p) =
      XP_USED_CURRENT_VARS p)``,

  Induct_on `l` THENL [
    SIMP_TAC std_ss [XP_CURRENT_EXISTS_def, LIST_TO_SET_THM, DIFF_EMPTY,
      XP_NEXT_EXISTS_def],

    ASM_SIMP_TAC std_ss [XP_CURRENT_EXISTS_def, XP_NEXT_EXISTS_def,
      LIST_TO_SET_THM, DIFF_EMPTY,
      XP_USED_VARS_EVAL, XP_ASSIGN_TRUE_FALSE___XP_USED_VARS] THEN
    SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_DIFF, IN_SING, IN_INSERT] THEN
    PROVE_TAC[]
  ])


val XP_FORALL___XP_USED_VARS =
  store_thm ("XP_FORALL___XP_USED_VARS",
    ``!l p.
      (XP_USED_CURRENT_VARS (XP_CURRENT_FORALL l p) =
      XP_USED_CURRENT_VARS p DIFF (LIST_TO_SET l)) /\
      (XP_USED_X_VARS (XP_CURRENT_FORALL l p) =
      XP_USED_X_VARS p) /\
      (XP_USED_X_VARS (XP_NEXT_FORALL l p) =
      XP_USED_X_VARS p DIFF (LIST_TO_SET l)) /\
      (XP_USED_CURRENT_VARS (XP_NEXT_FORALL l p) =
      XP_USED_CURRENT_VARS p)``,

  SIMP_TAC std_ss [XP_CURRENT_FORALL_def, XP_NEXT_FORALL_def,
    XP_USED_VARS_EVAL, XP_EXISTS___XP_USED_VARS]);


val XP_BIGOR___XP_USED_VARS =
  store_thm ("XP_BIGOR___XP_USED_VARS",
  ``!l. (XP_USED_CURRENT_VARS (XP_BIGOR l) = LIST_BIGUNION (MAP (\xp. XP_USED_CURRENT_VARS xp) l)) /\
    (XP_USED_X_VARS (XP_BIGOR l) = LIST_BIGUNION (MAP (\xp. XP_USED_X_VARS xp) l)) /\
    (XP_USED_VARS (XP_BIGOR l) = LIST_BIGUNION (MAP (\xp. XP_USED_VARS xp) l))``,

  Induct_on `l` THENL [
    SIMP_TAC list_ss [XP_BIGOR_def, XP_USED_VARS_EVAL, LIST_BIGUNION_def],
    ASM_SIMP_TAC list_ss [XP_BIGOR_def, XP_USED_VARS_EVAL, LIST_BIGUNION_def]
  ]);


val XP_CURRENT_NEXT___ASSIGN_TRUE_FALSE =
  store_thm (
    "XP_CURRENT_NEXT___ASSIGN_TRUE_FALSE",
  ``!p V.
      (XP_CURRENT (P_ASSIGN_TRUE V p) = XP_ASSIGN_TRUE V EMPTY (XP_CURRENT p)) /\
      (XP_NEXT (P_ASSIGN_TRUE V p) = XP_ASSIGN_TRUE EMPTY V (XP_NEXT p)) /\

      (XP_CURRENT (P_ASSIGN_FALSE V p) = XP_ASSIGN_FALSE V EMPTY (XP_CURRENT p)) /\
      (XP_NEXT (P_ASSIGN_FALSE V p) = XP_ASSIGN_FALSE EMPTY V (XP_NEXT p))``,

INDUCT_THEN prop_logic_induct ASSUME_TAC THEN (
  ASM_SIMP_TAC std_ss [P_ASSIGN_TRUE_def, P_ASSIGN_FALSE_def, XP_ASSIGN_TRUE_def,
    XP_ASSIGN_FALSE_def, XP_CURRENT_THM, XP_NEXT_THM, COND_RATOR, COND_RAND]
))



val XP_CURRENT_NEXT___EXISTS =
  store_thm (
    "XP_CURRENT_NEXT___EXISTS",
  ``!p l.
      (XP_CURRENT (P_EXISTS l p) = XP_CURRENT_EXISTS l (XP_CURRENT p)) /\
      (XP_NEXT (P_EXISTS l p) = XP_NEXT_EXISTS l (XP_NEXT p))``,

    Induct_on `l` THENL [
      SIMP_TAC std_ss [P_EXISTS_def, XP_CURRENT_EXISTS_def, XP_NEXT_EXISTS_def],

      ASM_SIMP_TAC std_ss [P_EXISTS_def, XP_CURRENT_EXISTS_def, XP_NEXT_EXISTS_def,
        XP_NEXT_THM, XP_CURRENT_NEXT___ASSIGN_TRUE_FALSE,
        XP_CURRENT_THM]
    ]);

val XP_CURRENT_NEXT___FORALL =
  store_thm (
    "XP_CURRENT_NEXT___FORALL",

    ``!l p.
      (XP_CURRENT (P_FORALL l p) = XP_CURRENT_FORALL l (XP_CURRENT p)) /\
      (XP_NEXT (P_FORALL l p) = XP_NEXT_FORALL l (XP_NEXT p))``,

    SIMP_TAC std_ss [P_FORALL_def, XP_CURRENT_FORALL_def, XP_NEXT_FORALL_def,
      XP_CURRENT_NEXT___EXISTS, XP_NEXT_THM, XP_CURRENT_THM]
)




val _ = export_theory();
