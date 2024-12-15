open HolKernel Parse boolLib bossLib;

open full_ltlTheory arithmeticTheory automaton_formulaTheory xprop_logicTheory prop_logicTheory
     infinite_pathTheory tuerk_tacticsLib symbolic_semi_automatonTheory
     listTheory pred_setTheory temporal_deep_mixedTheory
     pred_setTheory rich_listTheory set_lemmataTheory pairTheory
     ltl_to_automaton_formulaTheory numLib listLib rltlTheory
     rltl_to_ltlTheory psl_to_rltlTheory PSLPathTheory UnclockedSemanticsTheory
     ProjectionTheory symbolic_kripke_structureTheory
     temporal_deep_simplificationsLibTheory;

open Sanity;

val _ = hide "S";
val _ = hide "I";

(* This theory contains lemmata and definitions used by
  translationsLib. Most of these are simple correlars from
  the lemmata in the specialised translation theories. In contrast
  to the lemmata proved in these theories, the lemmata proved in
  this theory are not of general interest. They are just
  used as helpers for temporalLib.

  Ideally they would be proved in translationsLib. However, then
  the proofs would be redone every time, the library is used. *)

val _ = new_theory "translationsLib";
val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj"]
val list_ss = list_ss -* ["lift_disj_eq", "lift_imp_disj"]

(* Helper theorems for the rewrite translation of LTL to gen. Buechi *)
Theorem LTL_TO_GEN_BUECHI___TRANSLATION_THM___MAX :
    !x l DS pf sv.
      ((pf = FST(LTL_TO_GEN_BUECHI l T x)) /\
       (DS = SND(LTL_TO_GEN_BUECHI l T x)) /\
       LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv) ==>
      (!i. LTL_SEM i l = A_SEM i (LTL_TO_GEN_BUECHI_DS___A_NDET DS pf sv))
Proof
    METIS_TAC [LTL_TO_GEN_BUECHI_THM, LTL_TO_GEN_BUECHI_DS___SEM___MAX]
QED

Theorem LTL_TO_GEN_BUECHI___TRANSLATION_THM___MIN :
    !x l DS pf sv.
      ((pf = FST(LTL_TO_GEN_BUECHI l x T)) /\
       (DS = SND(LTL_TO_GEN_BUECHI l x T)) /\
       LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv) ==>
      (!i. LTL_SEM i l = A_SEM i (LTL_TO_GEN_BUECHI_DS___A_UNIV DS pf sv))
Proof
    METIS_TAC [LTL_TO_GEN_BUECHI_THM, LTL_TO_GEN_BUECHI_DS___SEM___MIN]
QED

(* Specicalised version
   |- !DS p.
          LTL_TO_GEN_BUECHI_DS___SEM DS ==>
          LTL_TO_GEN_BUECHI_DS___SEM
            (ltl_to_gen_buechi_ds DS.SN DS.S0 (P_USED_VARS p UNION DS.IV)
               DS.R DS.FC ((LTL_PROP p,T,T,(\sv. p)) INSERT DS.B))
 *)
Theorem CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PROP___eval =
    SIMP_RULE list_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
                       EXTEND_LTL_TO_GEN_BUECHI_DS_def,
                       UNION_SING]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PROP;

(* |- !b1 b2 DS l pf.
          LTL_TO_GEN_BUECHI_DS___SEM DS ==>
          (l,b1,b2,pf) IN DS.B ==>
          LTL_TO_GEN_BUECHI_DS___SEM
            (ltl_to_gen_buechi_ds DS.SN DS.S0 DS.IV DS.R DS.FC
               ((LTL_NOT l,b2,b1,(\sv. P_NOT (pf sv))) INSERT DS.B))
 *)
Theorem CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT___eval =
    SIMP_RULE list_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
                       EXTEND_LTL_TO_GEN_BUECHI_DS_def, UNION_SING, UNION_EMPTY,
                       GSYM AND_IMP_INTRO]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT;

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_AND___eval = save_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_AND___eval",
    let
      val thm = SIMP_RULE list_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
                       EXTEND_LTL_TO_GEN_BUECHI_DS_def, UNION_SING, UNION_EMPTY
                      ] CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_AND;
      val thm = ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] thm
    in
      thm
    end);

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_OR___eval = save_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_OR___eval",
    let
      val thm = SIMP_RULE list_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
                       EXTEND_LTL_TO_GEN_BUECHI_DS_def, UNION_SING, UNION_EMPTY
                      ] CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_OR;
      val thm = ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] thm
    in
      thm
    end);

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_EQUIV___eval = save_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_EQUIV___eval",
    let
      val thm = SIMP_RULE list_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
                       EXTEND_LTL_TO_GEN_BUECHI_DS_def, UNION_SING, UNION_EMPTY
                      ] CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_EQUIV;
      val thm = ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] thm
    in
      thm
    end);

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NEXT___eval = save_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NEXT___eval",
      SIMP_RULE list_ss [EXTEND_LTL_TO_GEN_BUECHI_DS_def, UNION_SING, UNION_EMPTY,
                         GSYM AND_IMP_INTRO]
                CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NEXT);

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSNEXT___eval = save_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSNEXT___eval",
    SIMP_RULE list_ss [EXTEND_LTL_TO_GEN_BUECHI_DS_def, UNION_SING, UNION_EMPTY,
                       GSYM AND_IMP_INTRO]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSNEXT);

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PNEXT___eval = save_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PNEXT___eval",
    SIMP_RULE list_ss [EXTEND_LTL_TO_GEN_BUECHI_DS_def, UNION_SING, UNION_EMPTY,
                       GSYM AND_IMP_INTRO]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PNEXT);

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_SUNTIL___eval = save_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_SUNTIL___eval",
    let
      val thm = SIMP_RULE list_ss [EXTEND_LTL_TO_GEN_BUECHI_DS_def, UNION_SING, UNION_EMPTY]
                          CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_SUNTIL;
      val thm = ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] thm
    in
      thm
    end);

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSUNTIL___eval = save_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSUNTIL___eval",
    let
      val thm = SIMP_RULE list_ss [EXTEND_LTL_TO_GEN_BUECHI_DS_def, UNION_SING, UNION_EMPTY]
                          CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSUNTIL;
      val thm = ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] thm
    in
      thm
    end);

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_BEFORE___eval = save_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_BEFORE___eval",
    let
      val thm = SIMP_RULE list_ss [EXTEND_LTL_TO_GEN_BUECHI_DS_def, UNION_SING, UNION_EMPTY]
                          CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_BEFORE;
      val thm = ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] thm
    in
      thm
    end);

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PBEFORE___eval = save_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PBEFORE___eval",
    let
      val thm = SIMP_RULE list_ss [EXTEND_LTL_TO_GEN_BUECHI_DS_def, UNION_SING, UNION_EMPTY]
                          CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PBEFORE;
      val thm = ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] thm
    in
      thm
    end);

(* forget bindings specicalised version *)
val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PROP___forget_eval = save_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PROP___forget_eval",
    SIMP_RULE list_ss [EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
                       EXTEND_LTL_TO_GEN_BUECHI_DS_def,
                       UNION_EMPTY,
                       EMPTY_LTL_TO_GEN_BUECHI_DS_def,
                       ltl_to_gen_buechi_ds_REWRITES]
      (prove (``!b1 b2 p.
          LTL_TO_GEN_BUECHI_DS___SEM
            (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS EMPTY_LTL_TO_GEN_BUECHI_DS
                {(LTL_PROP p,b1,b2,(\sv. p))} (P_USED_VARS p))``,
          METIS_TAC[CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PROP,
                    LTL_TO_GEN_BUECHI_DS___SEM___WEAKEN_BINDING,
                    EMPTY_LTL_TO_GEN_BUECHI_DS___SEM])));

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT___forget_eval =
  prove (``
    !b1 b2 DS l pf.
            LTL_TO_GEN_BUECHI_DS___SEM DS ==>
            (DS.B = {(l,b2,b1,pf)}) ==>
            LTL_TO_GEN_BUECHI_DS___SEM
              (LTL_TO_GEN_BUECHI_DS___SET_BINDINGS DS
                  {(LTL_NOT l,b1,b2,(\sv. P_NOT (pf sv)))})``,

    REPEAT STRIP_TAC THEN
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT___eval THEN
    Q_SPECL_NO_ASSUM 0 [`b2`, `b1`, `DS`, `l`, `pf`] THEN
    UNDISCH_HD_TAC THEN
    ASM_SIMP_TAC std_ss [IN_SING, LTL_TO_GEN_BUECHI_DS___SET_BINDINGS_def] THEN
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN
    SIMP_TAC std_ss [ltl_to_gen_buechi_ds_REWRITES, SUBSET_DEF, IN_SING, IN_INSERT]);

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT___forget_eval = save_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT___forget_eval",
    SIMP_RULE std_ss [LTL_TO_GEN_BUECHI_DS___SET_BINDINGS_def]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NOT___forget_eval);

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_AND___forget_eval =
  prove (``
    !b1 b2 DS1 DS2 l1 l2 pf1 pf2.
            LTL_TO_GEN_BUECHI_DS___SEM DS1 ==>
            LTL_TO_GEN_BUECHI_DS___SEM DS2 ==>
            (DS1.B = {(l1,b1,b2,pf1)}) ==>
            (DS2.B = {(l2,b1,b2,pf2)}) ==>
            LTL_TO_GEN_BUECHI_DS___SEM
              (LTL_TO_GEN_BUECHI_DS___SET_BINDINGS
                  (LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2)
                  {(LTL_AND (l1, l2), b1,b2,(\sv. P_AND(pf1 sv, pf2 (\n. sv (n + DS1.SN)))))})``,

    REPEAT STRIP_TAC THEN
    `?DS'. LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2 = DS'` by METIS_TAC[] THEN
    SUBGOAL_TAC `(l1,b1,b2,pf1) IN DS'.B /\
                 (l2,b1,b2,(\sv. pf2 (\n. sv (n + DS1.SN)))) IN DS'.B` THEN1 (
      GSYM_NO_TAC 0 (*DS'*) THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___PRODUCT_def,
        ltl_to_gen_buechi_ds_REWRITES, IN_SING, IN_UNION, IMAGE_SING]
    ) THEN
    `LTL_TO_GEN_BUECHI_DS___SEM DS'` by
      METIS_TAC[LTL_TO_GEN_BUECHI_DS___PRODUCT___SEM___THM] THEN
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_AND___eval THEN
    Q_SPECL_NO_ASSUM 0 [`DS'`, `b1`,`b2`, `b1`, `b2`, `l1`, `l2`, `pf1`, `(\sv. pf2 (\n. sv (n + DS1.SN)))`] THEN
    UNDISCH_HD_TAC THEN
    ASM_REWRITE_TAC[LTL_TO_GEN_BUECHI_DS___SET_BINDINGS_def] THEN
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN
    SIMP_TAC std_ss [SUBSET_DEF, IN_SING, IN_INSERT, ltl_to_gen_buechi_ds_REWRITES]);

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_AND___forget_eval = save_thm
  ("CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_AND___forget_eval",
    SIMP_RULE std_ss [LTL_TO_GEN_BUECHI_DS___SET_BINDINGS_def,
                      ltl_to_gen_buechi_ds_REWRITES, LTL_TO_GEN_BUECHI_DS___PRODUCT_def]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_AND___forget_eval);

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_OR___forget_eval =
  prove (``
    !b1 b2 DS1 DS2 l1 l2 pf1 pf2.
            LTL_TO_GEN_BUECHI_DS___SEM DS1 ==>
            LTL_TO_GEN_BUECHI_DS___SEM DS2 ==>
            (DS1.B = {(l1,b1,b2,pf1)}) ==>
            (DS2.B = {(l2,b1,b2,pf2)}) ==>
            LTL_TO_GEN_BUECHI_DS___SEM
              (LTL_TO_GEN_BUECHI_DS___SET_BINDINGS
                  (LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2)
                  {(LTL_OR (l1, l2), b1,b2,(\sv. P_OR(pf1 sv, pf2 (\n. sv (n + DS1.SN)))))})``,

    REPEAT STRIP_TAC THEN
    `?DS'. LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2 = DS'` by METIS_TAC[] THEN
    SUBGOAL_TAC `(l1,b1,b2,pf1) IN DS'.B /\
                 (l2,b1,b2,(\sv. pf2 (\n. sv (n + DS1.SN)))) IN DS'.B` THEN1 (
      GSYM_NO_TAC 0 (*DS'*) THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___PRODUCT_def,
        ltl_to_gen_buechi_ds_REWRITES, IN_SING, IN_UNION, IMAGE_SING]
    ) THEN
    `LTL_TO_GEN_BUECHI_DS___SEM DS'` by
      METIS_TAC[LTL_TO_GEN_BUECHI_DS___PRODUCT___SEM___THM] THEN
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_OR___eval THEN
    Q_SPECL_NO_ASSUM 0 [`DS'`, `b1`, `b2`, `b1`, `b2`, `l1`, `l2`, `pf1`, `(\sv. pf2 (\n. sv (n + DS1.SN)))`] THEN
    UNDISCH_HD_TAC THEN
    ASM_REWRITE_TAC[LTL_TO_GEN_BUECHI_DS___SET_BINDINGS_def] THEN
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN
    SIMP_TAC std_ss [ltl_to_gen_buechi_ds_REWRITES, SUBSET_DEF, IN_SING, IN_INSERT]);

Theorem CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_OR___forget_eval =
    SIMP_RULE std_ss [LTL_TO_GEN_BUECHI_DS___SET_BINDINGS_def,
                      ltl_to_gen_buechi_ds_REWRITES, LTL_TO_GEN_BUECHI_DS___PRODUCT_def]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_OR___forget_eval;

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_EQUIV___forget_eval =
  prove (``
    !b1 b2 DS1 DS2 l1 l2 pf1 pf2.
            LTL_TO_GEN_BUECHI_DS___SEM DS1 ==>
            LTL_TO_GEN_BUECHI_DS___SEM DS2 ==>
            (DS1.B = {(l1,T,T,pf1)}) ==>
            (DS2.B = {(l2,T,T,pf2)}) ==>
            LTL_TO_GEN_BUECHI_DS___SEM
              (LTL_TO_GEN_BUECHI_DS___SET_BINDINGS
                  (LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2)
                  {(LTL_EQUIV (l1, l2),b1,b2,(\sv. P_EQUIV(pf1 sv, pf2 (\n. sv (n + DS1.SN)))))})``,

    REPEAT STRIP_TAC THEN
    `?DS'. LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2 = DS'` by METIS_TAC[] THEN
    SUBGOAL_TAC `(l1,T,T,pf1) IN DS'.B /\
                 (l2,T,T,(\sv. pf2 (\n. sv (n + DS1.SN)))) IN DS'.B` THEN1 (
      GSYM_NO_TAC 0 (*DS'*) THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___PRODUCT_def,
        ltl_to_gen_buechi_ds_REWRITES, IN_SING, IN_UNION, IMAGE_SING]
    ) THEN
    `LTL_TO_GEN_BUECHI_DS___SEM DS'` by
      METIS_TAC[LTL_TO_GEN_BUECHI_DS___PRODUCT___SEM___THM] THEN
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_EQUIV THEN
    Q_SPECL_NO_ASSUM 0 [`DS'`, `l1`, `l2`, `pf1`, `(\sv. pf2 (\n. sv (n + DS1.SN)))`] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 ASM_REWRITE_TAC[] THEN
    `LTL_TO_GEN_BUECHI_DS___SEM
            (EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS DS'
               {(LTL_EQUIV (l1,l2),b1,b2,
                 (\sv.
                    P_EQUIV (pf1 sv,(\sv. pf2 (\n. sv (n + DS1.SN))) sv)))}
               {})` by METIS_TAC[LTL_TO_GEN_BUECHI_DS___SEM___WEAKEN_BINDING] THEN
    UNDISCH_HD_TAC THEN
    ASM_REWRITE_TAC[LTL_TO_GEN_BUECHI_DS___SET_BINDINGS_def,
      EXTEND_IV_BINDING_LTL_TO_GEN_BUECHI_DS_def,
      EXTEND_LTL_TO_GEN_BUECHI_DS_def] THEN
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN
    SIMP_TAC list_ss [ltl_to_gen_buechi_ds_REWRITES, SUBSET_DEF,
                      IN_SING, IN_INSERT, IN_UNION, UNION_EMPTY]);

Theorem CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_EQUIV___forget_eval =
    SIMP_RULE std_ss [LTL_TO_GEN_BUECHI_DS___SET_BINDINGS_def,
                      ltl_to_gen_buechi_ds_REWRITES, LTL_TO_GEN_BUECHI_DS___PRODUCT_def]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_EQUIV___forget_eval;

Theorem CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NEXT___forget_eval :
    !b1 b2 DS l pf.
            LTL_TO_GEN_BUECHI_DS___SEM DS ==>
            (DS.B = {(l,b1,b2,pf)}) ==>
            LTL_TO_GEN_BUECHI_DS___SEM
              (ltl_to_gen_buechi_ds (DS.SN + 1) DS.S0 DS.IV
              ((\sv. XP_EQUIV (XP_PROP (sv DS.SN),XP_NEXT (pf sv)))::DS.R)
              DS.FC {(LTL_NEXT l,b1,b2,(\sv. P_PROP (sv DS.SN)))})
Proof
    REPEAT STRIP_TAC THEN
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_NEXT___eval THEN
    Q_SPECL_NO_ASSUM 0 [`b1`,`b2`, `DS`, `l`, `pf`] THEN
    UNDISCH_HD_TAC THEN
    ASM_SIMP_TAC std_ss [IN_SING] THEN
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN
    SIMP_TAC std_ss [ltl_to_gen_buechi_ds_REWRITES, SUBSET_DEF, IN_SING, IN_INSERT]
QED

Theorem CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSNEXT___forget_eval :
    !b1 b2 DS l pf.
            LTL_TO_GEN_BUECHI_DS___SEM DS ==>
            (DS.B = {(l,b1,b2,pf)}) ==>
            LTL_TO_GEN_BUECHI_DS___SEM
              (ltl_to_gen_buechi_ds (DS.SN + 1) ((DS.SN,F)::DS.S0) DS.IV
              ((\sv. XP_EQUIV (XP_NEXT_PROP (sv DS.SN),XP_CURRENT (pf sv)))::DS.R)
              DS.FC {(LTL_PSNEXT l,b1,b2,(\sv. P_PROP (sv DS.SN)))})
Proof
    REPEAT STRIP_TAC THEN
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSNEXT___eval THEN
    Q_SPECL_NO_ASSUM 0 [`b1`, `b2`, `DS`, `l`, `pf`] THEN
    UNDISCH_HD_TAC THEN
    ASM_SIMP_TAC std_ss [IN_SING] THEN
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN
    SIMP_TAC std_ss [ltl_to_gen_buechi_ds_REWRITES, SUBSET_DEF, IN_SING, IN_INSERT]
QED

Theorem CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PNEXT___forget_eval :
    !b1 b2 DS l pf.
            LTL_TO_GEN_BUECHI_DS___SEM DS ==>
            (DS.B = {(l,b1,b2,pf)}) ==>
            LTL_TO_GEN_BUECHI_DS___SEM
              (ltl_to_gen_buechi_ds (DS.SN + 1) ((DS.SN,F)::DS.S0) DS.IV
              ((\sv. XP_EQUIV (XP_NEXT_PROP (sv DS.SN),XP_CURRENT (P_NOT (pf sv))))::DS.R)
              DS.FC {(LTL_PNEXT l,b1,b2,(\sv. P_NOT (P_PROP (sv DS.SN))))})
Proof
    REPEAT STRIP_TAC THEN
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PNEXT___eval THEN
    Q_SPECL_NO_ASSUM 0 [`b1`, `b2`, `DS`, `l`, `pf`] THEN
    UNDISCH_HD_TAC THEN
    ASM_SIMP_TAC std_ss [IN_SING] THEN
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN
    SIMP_TAC std_ss [ltl_to_gen_buechi_ds_REWRITES, SUBSET_DEF, IN_SING, IN_INSERT]
QED

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_SUNTIL___forget_eval = prove (``
    !b1 b2 DS1 DS2 l1 l2 pf1 pf2 DS'.
           (LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2 = DS') ==>
            LTL_TO_GEN_BUECHI_DS___SEM DS1 ==>
            LTL_TO_GEN_BUECHI_DS___SEM DS2 ==>
            (DS1.B = {(l1,b1,b2,pf1)}) ==>
            (DS2.B = {(l2,b1,b2,pf2)}) ==>
            LTL_TO_GEN_BUECHI_DS___SEM
              (ltl_to_gen_buechi_ds (DS'.SN + 1) DS'.S0 DS'.IV
                ((\sv.
                    XP_EQUIV
                      (XP_PROP (sv DS'.SN),
                        XP_OR
                          (XP_CURRENT ((\sv. pf2 (\n. sv (n + DS1.SN))) sv),
                          XP_AND
                            (XP_CURRENT (pf1 sv),XP_NEXT_PROP (sv DS'.SN)))))::
                      DS'.R)
                ((if b1 then
                    [(\sv.
                        P_IMPL
                          (P_PROP (sv DS'.SN),
                            (\sv. pf2 (\n. sv (n + DS1.SN))) sv))]
                  else
                    []) <> DS'.FC)
                {(LTL_SUNTIL (l1,l2),b1,b2,(\sv. P_PROP (sv DS'.SN)))})``,

    REPEAT STRIP_TAC THEN
    SUBGOAL_TAC `(l1,b1,b2,pf1) IN DS'.B /\
                 (l2,b1,b2,(\sv. pf2 (\n. sv (n + DS1.SN)))) IN DS'.B` THEN1 (
      GSYM_NO_TAC 4 (*DS'*) THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___PRODUCT_def,
        ltl_to_gen_buechi_ds_REWRITES, IN_SING, IN_UNION, IMAGE_SING]
    ) THEN
    `LTL_TO_GEN_BUECHI_DS___SEM DS'` by
      METIS_TAC[LTL_TO_GEN_BUECHI_DS___PRODUCT___SEM___THM] THEN
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_SUNTIL___eval THEN
    Q_SPECL_NO_ASSUM 0 [`b1`, `b2`, `b1`, `b2`, `b1`, `DS'`, `l1`, `l2`, `pf1`,
                        `(\sv. pf2 (\n. sv (n + DS1.SN)))`] THEN
    UNDISCH_HD_TAC THEN
    ASM_REWRITE_TAC[LTL_TO_GEN_BUECHI_DS___SET_BINDINGS_def] THEN
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN
    SIMP_TAC std_ss [SUBSET_DEF, IN_SING, IN_INSERT, ltl_to_gen_buechi_ds_REWRITES]);

Theorem CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_SUNTIL___forget_eval =
    SIMP_RULE std_ss [ltl_to_gen_buechi_ds_REWRITES, LTL_TO_GEN_BUECHI_DS___PRODUCT_def]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_SUNTIL___forget_eval;

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSUNTIL___forget_eval = prove (``
    !b1 b2 DS1 DS2 l1 l2 pf1 pf2 DS'.
            (LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2 = DS') ==>
            LTL_TO_GEN_BUECHI_DS___SEM DS1 ==>
            LTL_TO_GEN_BUECHI_DS___SEM DS2 ==>
            (DS1.B = {(l1,b1,b2,pf1)}) ==>
            (DS2.B = {(l2,b1,b2,pf2)}) ==>
            LTL_TO_GEN_BUECHI_DS___SEM
              (ltl_to_gen_buechi_ds (DS'.SN + 1) ((DS'.SN,F)::DS'.S0) DS'.IV
              ((\sv.
                  XP_EQUIV
                    (XP_NEXT_PROP (sv DS'.SN),
                    XP_OR
                      (XP_CURRENT ((\sv. pf2 (\n. sv (n + DS1.SN))) sv),
                        XP_AND (XP_CURRENT (pf1 sv),XP_PROP (sv DS'.SN)))))::
                  DS'.R) DS'.FC
              {(LTL_PSUNTIL (l1,l2),b1,b2,
                (\sv.
                  P_OR
                    ((\sv. pf2 (\n. sv (n + DS1.SN))) sv,
                      P_AND (pf1 sv,P_PROP (sv DS'.SN)))))})``,

    REPEAT STRIP_TAC THEN
    SUBGOAL_TAC `(l1,b1,b2,pf1) IN DS'.B /\
                 (l2,b1,b2,(\sv. pf2 (\n. sv (n + DS1.SN)))) IN DS'.B` THEN1 (
      GSYM_NO_TAC 4 (*DS'*) THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___PRODUCT_def,
        ltl_to_gen_buechi_ds_REWRITES, IN_SING, IN_UNION, IMAGE_SING]
    ) THEN
    `LTL_TO_GEN_BUECHI_DS___SEM DS'` by
      METIS_TAC[LTL_TO_GEN_BUECHI_DS___PRODUCT___SEM___THM] THEN
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSUNTIL___eval THEN
    Q_SPECL_NO_ASSUM 0 [`b1`, `b2`, `b1`, `b2`, `DS'`, `l1`, `l2`, `pf1`,
                        `(\sv. pf2 (\n. sv (n + DS1.SN)))`] THEN
    UNDISCH_HD_TAC THEN
    ASM_REWRITE_TAC[LTL_TO_GEN_BUECHI_DS___SET_BINDINGS_def] THEN
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN
    SIMP_TAC std_ss [SUBSET_DEF, IN_SING, IN_INSERT, ltl_to_gen_buechi_ds_REWRITES]);

Theorem CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSUNTIL___forget_eval =
    SIMP_RULE std_ss [ltl_to_gen_buechi_ds_REWRITES, LTL_TO_GEN_BUECHI_DS___PRODUCT_def]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PSUNTIL___forget_eval;

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_BEFORE___forget_eval = prove (``
    !b1 b2 DS1 DS2 l1 l2 pf1 pf2 DS'.
            (LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2 = DS') ==>
            LTL_TO_GEN_BUECHI_DS___SEM DS1 ==>
            LTL_TO_GEN_BUECHI_DS___SEM DS2 ==>
            (DS1.B = {(l1,b1,b2,pf1)}) ==>
            (DS2.B = {(l2,b2,b1,pf2)}) ==>
            LTL_TO_GEN_BUECHI_DS___SEM
              (ltl_to_gen_buechi_ds (DS'.SN + 1) DS'.S0 DS'.IV
              ((\sv.
                  XP_EQUIV
                    (XP_PROP (sv DS'.SN),
                    XP_OR
                      (XP_CURRENT ((\sv. pf2 (\n. sv (n + DS1.SN))) sv),
                        XP_AND
                          (XP_CURRENT (P_NOT (pf1 sv)),XP_NEXT_PROP (sv DS'.SN)))))::
                  DS'.R)
              ((if ~b2 then
                  []
                else
                  [(\sv.
                      P_IMPL
                        (P_PROP (sv DS'.SN),
                        (\sv. pf2 (\n. sv (n + DS1.SN))) sv))]) <> DS'.FC)
              {(LTL_BEFORE (l1,l2),b1,b2,(\sv. P_NOT (P_PROP (sv DS'.SN))))})``,

    REPEAT STRIP_TAC THEN
    SUBGOAL_TAC `(l1,b1,b2,pf1) IN DS'.B /\
                 (l2,b2,b1,(\sv. pf2 (\n. sv (n + DS1.SN)))) IN DS'.B` THEN1 (
      GSYM_NO_TAC 4 (*DS'*) THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___PRODUCT_def,
        ltl_to_gen_buechi_ds_REWRITES, IN_SING, IN_UNION, IMAGE_SING]
    ) THEN
    `LTL_TO_GEN_BUECHI_DS___SEM DS'` by
      METIS_TAC[LTL_TO_GEN_BUECHI_DS___PRODUCT___SEM___THM] THEN
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_BEFORE___eval THEN
    Q_SPECL_NO_ASSUM 0 [`b1`,`b2`,`b2`,`b1`,`b2`, `DS'`, `l1`, `l2`, `pf1`, `(\sv. pf2 (\n. sv (n + DS1.SN)))`] THEN
    UNDISCH_HD_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN
    SIMP_TAC std_ss [SUBSET_DEF, IN_SING, IN_INSERT, ltl_to_gen_buechi_ds_REWRITES]);


Theorem CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_BEFORE___forget_eval =
    SIMP_RULE std_ss [ltl_to_gen_buechi_ds_REWRITES, LTL_TO_GEN_BUECHI_DS___PRODUCT_def]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_BEFORE___forget_eval;

val CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PBEFORE___forget_eval = prove (``
    !b1 b2 DS1 DS2 l1 l2 pf1 pf2 DS'.
            (LTL_TO_GEN_BUECHI_DS___PRODUCT DS1 DS2 = DS') ==>
            LTL_TO_GEN_BUECHI_DS___SEM DS1 ==>
            LTL_TO_GEN_BUECHI_DS___SEM DS2 ==>
            (DS1.B = {(l1,b1,b2,pf1)}) ==>
            (DS2.B = {(l2,b2,b1,pf2)}) ==>
            LTL_TO_GEN_BUECHI_DS___SEM
               (ltl_to_gen_buechi_ds (DS'.SN + 1) ((DS'.SN,F)::DS'.S0) DS'.IV
                ((\sv.
                    XP_EQUIV
                      (XP_NEXT_PROP (sv DS'.SN),
                        XP_OR
                          (XP_CURRENT ((\sv. pf2 (\n. sv (n + DS1.SN))) sv),
                          XP_AND (XP_CURRENT (P_NOT (pf1 sv)),XP_PROP (sv DS'.SN)))))::
                      DS'.R) DS'.FC
                {(LTL_PBEFORE (l1,l2),b1,b2,
                  (\sv.
                      P_NOT (P_OR
                        ((\sv. pf2 (\n. sv (n + DS1.SN))) sv,
                          P_AND (P_NOT (pf1 sv),P_PROP (sv DS'.SN))))))})``,

    REPEAT STRIP_TAC THEN
    SUBGOAL_TAC `(l1,b1,b2,pf1) IN DS'.B /\
                 (l2,b2,b1,(\sv. pf2 (\n. sv (n + DS1.SN)))) IN DS'.B` THEN1 (
      GSYM_NO_TAC 4 (*DS'*) THEN
      ASM_SIMP_TAC std_ss [LTL_TO_GEN_BUECHI_DS___PRODUCT_def,
        ltl_to_gen_buechi_ds_REWRITES, IN_SING, IN_UNION, IMAGE_SING]
    ) THEN
    `LTL_TO_GEN_BUECHI_DS___SEM DS'` by
      METIS_TAC[LTL_TO_GEN_BUECHI_DS___PRODUCT___SEM___THM] THEN
    ASSUME_TAC CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PBEFORE___eval THEN
    Q_SPECL_NO_ASSUM 0 [`b1`, `b2`, `b2`, `b1`, `DS'`, `l1`, `l2`, `pf1`, `(\sv. pf2 (\n. sv (n + DS1.SN)))`] THEN
    UNDISCH_HD_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LTL_TO_GEN_BUECHI_DS___SEM___REMOVE_BINDINGS THEN
    SIMP_TAC std_ss [SUBSET_DEF, IN_SING, IN_INSERT, ltl_to_gen_buechi_ds_REWRITES]);

Theorem CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PBEFORE___forget_eval =
    SIMP_RULE std_ss [ltl_to_gen_buechi_ds_REWRITES, LTL_TO_GEN_BUECHI_DS___PRODUCT_def]
              CONSTRUCTION_LTL_TO_GEN_BUECHI_DS___CASE_PBEFORE___forget_eval;

Theorem LTL_TO_GEN_BUECHI_DS___SEM___MAX___eval :
     !DS l l' pf a.
         LTL_TO_GEN_BUECHI_DS___SEM DS ==>
         (LTL_EQUIVALENT l l') ==>
         (l',T, a, pf) IN DS.B ==> !sv. (
         LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv ==>
         !i.
           LTL_SEM i l = A_SEM i (LTL_TO_GEN_BUECHI_DS___A_NDET DS pf sv))
Proof
    METIS_TAC[LTL_TO_GEN_BUECHI_DS___SEM___MAX, LTL_SEM_def, LTL_EQUIVALENT_def]
QED

Theorem LTL_TO_GEN_BUECHI_DS___SEM___MIN___eval :
    !DS l l' pf a.
         LTL_TO_GEN_BUECHI_DS___SEM DS ==>
         (LTL_EQUIVALENT l l') ==>
         (l',a, T,pf) IN DS.B ==> !sv. (
         LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv ==>
         !i.
           LTL_SEM i l = A_SEM i (LTL_TO_GEN_BUECHI_DS___A_UNIV DS pf sv))
Proof
    METIS_TAC [LTL_TO_GEN_BUECHI_DS___SEM___MIN, LTL_SEM_def, LTL_EQUIVALENT_def]
QED

Theorem LTL_TO_GEN_BUECHI_DS___KS_SEM___MAX___eval :
    !DS l l' pf a.
         LTL_TO_GEN_BUECHI_DS___SEM DS ==>
         (LTL_EQUIVALENT l l') ==>
         (l',T, a,pf) IN DS.B ==>
       !sv. LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv ==>
         !M.
           LTL_KS_SEM M l = A_KS_SEM M (LTL_TO_GEN_BUECHI_DS___A_NDET DS pf sv)
Proof
    METIS_TAC [LTL_TO_GEN_BUECHI_DS___KS_SEM___MAX, LTL_KS_SEM_def,
               LTL_EQUIVALENT_def, LTL_SEM_def]
QED

Theorem LTL_TO_GEN_BUECHI_DS___KS_SEM___MIN___eval :
    !DS l l' pf a.
         LTL_TO_GEN_BUECHI_DS___SEM DS ==>
         (LTL_EQUIVALENT l l') ==>
         (l',a,T,pf) IN DS.B ==>
       !sv. LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv ==>
         !M.
           LTL_KS_SEM M l = A_KS_SEM M (LTL_TO_GEN_BUECHI_DS___A_UNIV DS pf sv)
Proof
    METIS_TAC [LTL_TO_GEN_BUECHI_DS___KS_SEM___MIN, LTL_KS_SEM_def,
               LTL_SEM_def, LTL_EQUIVALENT_def]
QED

Theorem LTL_TO_GEN_BUECHI_DS___KS_SEM___KRIPKE_STRUCTURE___eval :
    !DS l l' pf a.
         LTL_TO_GEN_BUECHI_DS___SEM DS ==>
         (LTL_EQUIVALENT l l') ==>
         (l',a,T,pf) IN DS.B ==> !M sv. (
         IS_ELEMENT_ITERATOR sv DS.SN
           (DS.IV UNION SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS M) ==> (
           LTL_KS_SEM M l =  IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE
            (SYMBOLIC_KRIPKE_STRUCTURE_PRODUCT M
               (symbolic_kripke_structure
                  (P_AND
                     (LTL_TO_GEN_BUECHI_DS___INITIAL_STATES DS sv,
                      P_NOT (pf sv))) (XP_BIGAND (MAP (\xp. xp sv) DS.R))))
            (MAP (\x. x sv) DS.FC)))
Proof
      REPEAT STRIP_TAC THEN
      ASSUME_TAC (GSYM LTL_TO_GEN_BUECHI_DS___KS_SEM___KRIPKE_STRUCTURE) THEN
      Q_SPECL_NO_ASSUM 0 [`DS`, `l'`, `pf`, `sv`, `M`, `a`] THEN
      UNDISCH_HD_TAC THEN ASM_SIMP_TAC std_ss [] THEN DISCH_TAC THEN WEAKEN_HD_TAC THEN
      FULL_SIMP_TAC std_ss [LTL_KS_SEM_def, LTL_SEM_def, LTL_EQUIVALENT_def]
QED

Theorem LTL_TO_GEN_BUECHI_DS___SEM___CONTRADICTION___KRIPKE_STRUCTURE___eval :
    !DS l l' pf a.
         LTL_TO_GEN_BUECHI_DS___SEM DS ==>
         (LTL_EQUIVALENT l l') ==>
         (l',T,a,pf) IN DS.B ==> !sv. (LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv ==> (
           LTL_IS_CONTRADICTION l = IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE
               (symbolic_kripke_structure
                  (P_AND
                     (LTL_TO_GEN_BUECHI_DS___INITIAL_STATES DS sv,
                      pf sv)) (XP_BIGAND (MAP (\xp. xp sv) DS.R)))
            (MAP (\x. x sv) DS.FC)))
Proof
      REPEAT STRIP_TAC THEN
      ASSUME_TAC (GSYM LTL_TO_GEN_BUECHI_DS___SEM___CONTRADICTION___KRIPKE_STRUCTURE) THEN
      Q_SPECL_NO_ASSUM 0 [`DS`, `l'`, `pf`, `sv`, `a`] THEN
      UNDISCH_HD_TAC THEN ASM_SIMP_TAC std_ss [] THEN DISCH_TAC THEN WEAKEN_HD_TAC THEN
      FULL_SIMP_TAC std_ss [LTL_IS_CONTRADICTION_def, LTL_SEM_def, LTL_EQUIVALENT_def]
QED

Theorem LTL_TO_GEN_BUECHI_DS___SEM___EQUIVALENT___KRIPKE_STRUCTURE___eval :
    !DS l1 l2 l' pf a.
         LTL_TO_GEN_BUECHI_DS___SEM DS ==>
         (LTL_EQUIVALENT (LTL_EVENTUAL (LTL_NOT (LTL_EQUIV(l1, l2)))) l') ==>
         (l',T, a,pf) IN DS.B ==> !sv. (LTL_TO_GEN_BUECHI_DS___IS_ELEMENT_ITERATOR DS sv ==> (
           LTL_EQUIVALENT l1 l2 = IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE
               (symbolic_kripke_structure
                  (P_AND
                     (LTL_TO_GEN_BUECHI_DS___INITIAL_STATES DS sv,
                      pf sv)) (XP_BIGAND (MAP (\xp. xp sv) DS.R)))
            (MAP (\x. x sv) DS.FC)))
Proof
      REPEAT STRIP_TAC THEN
      ASSUME_TAC (GSYM LTL_TO_GEN_BUECHI_DS___SEM___CONTRADICTION___KRIPKE_STRUCTURE___eval) THEN
      Q_SPECL_NO_ASSUM 0 [`DS`, `l'`, `l'`, `pf`, `a`] THEN
      UNDISCH_HD_TAC THEN ASM_SIMP_TAC std_ss [LTL_EQUIVALENT_def] THEN DISCH_TAC THEN WEAKEN_HD_TAC THEN
      FULL_SIMP_TAC std_ss [LTL_IS_CONTRADICTION_def, LTL_EQUIVALENT_def, LTL_SEM_THM] THEN
      GSYM_NO_TAC 2 THEN
      ASM_SIMP_TAC std_ss [] THEN
      PROVE_TAC[]
QED

Theorem IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE_cong :
    !S0 R fc S0' R' fc'.
    (PROP_LOGIC_EQUIVALENT S0 S0') ==>
    (XPROP_LOGIC_EQUIVALENT R R') ==>
    (PROP_LOGIC_EQUIVALENT_LIST_AS_SET fc fc') ==>
    (IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE (symbolic_kripke_structure S0 R) fc =
    IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE (symbolic_kripke_structure S0' R') fc')
Proof
    SIMP_TAC std_ss [PROP_LOGIC_EQUIVALENT_def,
                     XPROP_LOGIC_EQUIVALENT_def,
                     symbolic_kripke_structure_REWRITES,
                     IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE_def,
                     IS_FAIR_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def,
                     IS_FAIR_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def,
                     IS_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE_def,
                     PROP_LOGIC_EQUIVALENT_LIST_AS_SET_def,
                     congToolsLibTheory.LIST_AS_SET_CONGRUENCE_RELATION_def] THEN
    METIS_TAC[]
QED

Theorem IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE___VAR_RENAMING___eval :
    !f k fc. COND_IMP_EQ (INJ f (SYMBOLIC_KRIPKE_STRUCTURE_USED_VARS k UNION
                                 LIST_BIGUNION (MAP P_USED_VARS fc)) UNIV)
            (IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE k fc)
            (IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE
               (SYMBOLIC_KRIPKE_STRUCTURE_VAR_RENAMING f k) (MAP (P_VAR_RENAMING f) fc))
Proof
    SIMP_TAC std_ss [COND_IMP_EQ___REWRITE,
                     IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE___IDENTIFY_VARIABLES,
                     IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE___VAR_RENAMING]
QED

Theorem IS_ELEMENT_ITERATOR___ID :
    !S n0. IS_ELEMENT_ITERATOR (\n:num. n) n0 S =
           RES_FORALL S (\n. n >= n0)
Proof
    SIMP_TAC std_ss [IS_ELEMENT_ITERATOR_def, IMP_DISJ_THM,
                    NOT_LESS, GREATER_EQ, RES_FORALL_THM] THEN
    PROVE_TAC[]
QED

Theorem INJ___ADD_FUNC :
    !S f n:num. INJ (\x. f x + n) S UNIV = INJ f S UNIV
Proof
    SIMP_TAC std_ss [INJ_DEF, IN_UNIV]
QED

val POS_START_def = Define `
   (POS_START n [] h = 0) /\
   (POS_START n (h'::l) h = (if (h = h') then (SUC n) else (POS_START (SUC n) l h)))`;

Theorem POS_START_NOT_FOUND :
    !n l h. ((POS_START n l h = 0) = ~(MEM h l))
Proof
    Induct_on `l` THENL
  [ SIMP_TAC list_ss [POS_START_def],
    ASM_SIMP_TAC list_ss [POS_START_def] THEN
    REPEAT GEN_TAC THEN
    Cases_on `h' = h` THENL [
      ASM_SIMP_TAC arith_ss [],
    ASM_REWRITE_TAC[] ] ]
QED

Theorem POS_START_FOUND :
    !n l h. MEM h l ==> (POS_START n l h > n) /\ (EL ((PRE (POS_START n l h)) - n) l = h)
Proof
    Induct_on `l` THENL [
      SIMP_TAC list_ss [],

      ASM_SIMP_TAC list_ss [POS_START_def] THEN
      REPEAT GEN_TAC THEN
      Cases_on `h' = h` THENL [
        ASM_SIMP_TAC list_ss [],

        ASM_SIMP_TAC list_ss [] THEN
        STRIP_TAC THEN
        Q_SPECL_NO_ASSUM 2 [`SUC n`, `h'`] THEN
        UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL [
          ASM_SIMP_TAC arith_ss [],
          Cases_on `(POS_START (SUC n) l h')` THEN (
            SIMP_ALL_TAC arith_ss []
          ) THEN
          Cases_on `n'` THEN SIMP_ALL_TAC arith_ss [] THEN
          `SUC n'' - n = SUC (n'' - n)` by DECIDE_TAC THEN
          ASM_SIMP_TAC list_ss [] ] ] ]
QED

Theorem POS_START_RANGE :
    !n l h. (POS_START n l h > n) \/ (POS_START n l h = 0)
Proof
    PROVE_TAC[POS_START_FOUND, POS_START_NOT_FOUND]
QED

Theorem INJ_POS_START___MP_HELPER :
    !l S n. (!s. s IN S ==> MEM s l) ==>
            (ALL_DISTINCT l ==> INJ (\x. PRE (POS_START n l x)) S UNIV)
Proof
SIMP_TAC std_ss [INJ_DEF, IN_UNIV] THEN
Induct_on `l` THENL [
  SIMP_TAC list_ss [IMP_DISJ_THM, MEMBER_NOT_EMPTY, NOT_IN_EMPTY],

  SIMP_TAC list_ss [POS_START_def] THEN
  REPEAT STRIP_TAC THEN
  Q_SPECL_NO_ASSUM 6 [`S DELETE h`, `SUC n`] THEN
  UNDISCH_HD_TAC THEN
  `(!s. s IN S /\ ~(s = h) ==> MEM s l)` by METIS_TAC[] THEN
  ASM_REWRITE_TAC [IN_DELETE] THEN
  Cases_on `x = h` THEN Cases_on `x' = h` THENL [
    ASM_REWRITE_TAC[],

    `(POS_START (SUC n) l x' > SUC n)` by
      PROVE_TAC[POS_START_FOUND] THEN
    FULL_SIMP_TAC arith_ss [],

    `(POS_START (SUC n) l x > SUC n)` by
      PROVE_TAC[POS_START_FOUND] THEN
    FULL_SIMP_TAC arith_ss [],
    FULL_SIMP_TAC std_ss [] ] ]
QED

Theorem PRE_POS_START___REWRITES :
    !n h. (PRE (POS_START n [] h) = 0) /\
          (!n h h' l. (PRE (POS_START n (h'::l) h)) =
                      (if (h' = h) then n else PRE (POS_START (SUC n) l h)))
Proof
    SIMP_TAC std_ss [POS_START_def, COND_RAND]
QED

Theorem NUM_FINITE_INJ_EXISTS :
    !S. FINITE S ==> ?f:'a -> num. INJ f S UNIV
Proof
  REPEAT STRIP_TAC THEN
  SUBGOAL_TAC `INFINITE (UNIV:num set)` THEN1 (
    SIMP_TAC std_ss [INFINITE_UNIV] THEN
    EXISTS_TAC ``\x. SUC x`` THEN
    SIMP_TAC arith_ss [] THEN
    EXISTS_TAC ``0:num`` THEN
    SIMP_TAC arith_ss []
  ) THEN
  MP_TAC (Q.SPECL [`S`, `EMPTY`]
    (INST_TYPE [beta |-> num] temporal_deep_mixedTheory.FINITE_INJ_EXISTS)) THEN
  ASM_SIMP_TAC std_ss [FINITE_EMPTY, DISJOINT_EMPTY]
QED

Theorem RES_FORALL_INSERT :
    !x xs P. RES_FORALL (x INSERT xs) P <=> P x /\ RES_FORALL xs P
Proof
    SIMP_TAC std_ss [res_quanTheory.RES_FORALL, IN_INSERT, DISJ_IMP_THM, FORALL_AND_THM] THEN
    METIS_TAC[]
QED

val _ = export_theory();
