structure ibmLib :> ibmLib =
struct

(*
quietdec := true;

val home_dir = (concat Globals.HOLDIR "/examples/temporal_deep/");
loadPath := (concat home_dir "src/deep_embeddings") ::
            (concat home_dir "src/translations") ::
            (concat home_dir "src/tools") ::
            (concat home_dir "src/model_check") ::
            (concat hol_dir "examples/PSL/path") ::
            (concat hol_dir "examples/PSL/1.1/official-semantics") :: !loadPath;

map load
 ["full_ltlTheory", "arithmeticTheory", "automaton_formulaTheory", "xprop_logicTheory", "prop_logicTheory",
  "infinite_pathTheory", "tuerk_tacticsLib", "symbolic_semi_automatonTheory", "listTheory", "pred_setTheory",
  "pred_setTheory", "rich_listTheory", "set_lemmataTheory", "temporal_deep_mixedTheory",
  "pairTheory", "symbolic_kripke_structureTheory",
  "numLib", "semi_automatonTheory", "omega_automatonTheory",
  "omega_automaton_translationsTheory", "ctl_starTheory",
  "ltl_to_automaton_formulaTheory", "containerTheory",
  "psl_to_rltlTheory", "rltl_to_ltlTheory", "temporal_deep_simplificationsLib", "congLib", "ibmTheory",
  "psl_lemmataTheory", "translationsLib", "modelCheckLib",
  "Travrules", "SyntacticSugarTheory", "RewritesTheory"];
*)

open HolKernel boolLib bossLib
     full_ltlTheory arithmeticTheory automaton_formulaTheory xprop_logicTheory
     prop_logicTheory
     infinite_pathTheory tuerk_tacticsLib symbolic_semi_automatonTheory listTheory pred_setTheory
     pred_setTheory rich_listTheory set_lemmataTheory temporal_deep_mixedTheory pairTheory symbolic_kripke_structureTheory
     numLib semi_automatonTheory omega_automatonTheory
     omega_automaton_translationsTheory ctl_starTheory
     ltl_to_automaton_formulaTheory containerTheory
     psl_to_rltlTheory rltl_to_ltlTheory temporal_deep_simplificationsLib congLib ibmTheory computeLib psl_lemmataTheory translationsLib
     modelCheckLib Travrules SyntacticSugarTheory RewritesTheory;

(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)

val UF_KS_SEM___cong =
  prove (
    ``!f f'. UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f f' ==>
        !K. UF_KS_SEM K f = UF_KS_SEM K f'``,

SIMP_TAC std_ss [UF_KS_SEM_def, UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def] THEN
METIS_TAC[CONVERT_PATH_LTL_PSL___IS_INFINITE_TOP_BOTTOM_FREE]);


val P_USED_VARS___P_BIGOR___EVAL =
  prove (``!n0 n1. P_USED_VARS (P_BIGOR (MAP P_PROP (INTERVAL_LIST n0 n1))) = (INTERVAL_SET n0 n1)``,

  ONCE_REWRITE_TAC[EXTENSION] THEN
  SIMP_TAC std_ss [P_BIGOR___P_USED_VARS,
    MAP_MAP_o, combinTheory.o_DEF, P_USED_VARS_def,
    IN_INTERVAL_SET, IN_LIST_BIGUNION,
    MEM_MAP, IN_SING, MEM_INTERVAL_LIST,
    GSYM LEFT_EXISTS_AND_THM]);


val PROBLEM_TO_KRIPKE_STRUCTURE___eval =
  store_simp_thm ("PROBLEM_TO_KRIPKE_STRUCTURE___eval",
    ``!A i0 s0 p psl psl' sv. (sv =
          (\(n :num).
             (2 :num) * (2 :num) ** (SUC s0 - i0) + s0 + (3 :num) + n)) ==>
           (i0 <= s0) ==>
           (A.S = (INTERVAL_SET (SUC i0) s0)) ==>
           (SEMI_AUTOMATON_USED_VARS A SUBSET (INTERVAL_SET 0 s0)) ==>
           (P_USED_VARS p SUBSET (INTERVAL_SET 0 s0)) ==>
            UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE psl psl' ==>
            F_CLOCK_SERE_FREE psl' ==>
           (F_USED_VARS psl' SUBSET (INTERVAL_SET 0 i0)) ==>

           !a DS l' pf.
           LTL_EQUIVALENT
            (LTL_EQUIV
              (LTL_ALWAYS
                  (LTL_EVENTUAL
                    (LTL_PROP
                        (P_NOT
                          (P_BIGOR
                              (MAP P_PROP
                                (INTERVAL_LIST
                                    (SUC (SUC s0) + 2 ** SUC (s0 - i0))
                                    (SUC (SUC s0) + 2 ** SUC (s0 - i0) +
                                    PRE (2 ** SUC (s0 - i0))))))))), PSL_TO_LTL psl')) l' ==>
           LTL_TO_GEN_BUECHI_DS___SEM DS ==>
           (l',a,T,pf) IN DS.B ==>
           DS.IV SUBSET INTERVAL_SET 0 (2 * 2**(SUC s0 - i0) + s0 + 2) ==>
          !S0 R.
          ((P_AND
            (P_FORALL (INTERVAL_LIST (SUC i0) (SUC s0))
               (P_EQUIV
                  (P_AND (P_EQUIV (P_PROP (SUC s0),P_NOT p),A.S0),
                   VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING
                     (INTERVAL_LIST (SUC i0) (SUC s0)) (SUC (SUC s0))
                     (SUC i0))),
             P_AND
               (P_NOT
                  (P_BIGOR
                     (MAP P_PROP
                        (INTERVAL_LIST (SUC (SUC s0) + 2 ** SUC (s0 - i0))
                           (PRE (2 ** SUC (s0 - i0)) +
                            (SUC (SUC s0) + 2 ** SUC (s0 - i0)))))),
                P_AND
                  (LTL_TO_GEN_BUECHI_DS___INITIAL_STATES DS sv,
                   P_NOT (pf sv))))) = S0) ==>

          (
          (XP_AND
            (XP_NEXT_FORALL (INTERVAL_LIST (SUC i0) (SUC s0))
               (XP_EQUIV
                  (XP_NEXT
                     (VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING
                        (INTERVAL_LIST (SUC i0) (SUC s0)) (SUC (SUC s0))
                        (SUC i0)),
                   XP_CURRENT_EXISTS (INTERVAL_LIST (SUC i0) (SUC s0))
                     (XP_AND
                        (XP_EQUIV
                           (XP_NEXT_PROP (SUC s0),
                            XP_OR (XP_PROP (SUC s0),XP_NEXT (P_NOT p))),
                         XP_AND
                           (A.R,
                            XP_CURRENT
                              (VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING
                                 (INTERVAL_LIST (SUC i0) (SUC s0))
                                 (SUC (SUC s0)) (SUC i0))))))),
             XP_AND
               (XP_NEXT_FORALL (INTERVAL_LIST (SUC i0) (SUC s0))
                  (XP_EQUIV
                     (XP_NEXT
                        (P_VAR_RENAMING
                                          (\n.
                                             (if n >= SUC (SUC s0) then
                                                n + 2 ** SUC (s0 - i0)
                                              else
                                                n))
                          (VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING
                              (INTERVAL_LIST (SUC i0) (SUC s0))
                              (SUC (SUC s0)) (SUC i0))),
                      XP_CURRENT_EXISTS (INTERVAL_LIST (SUC i0) (SUC s0))
                        (XP_AND
                           (XP_EQUIV
                              (XP_NEXT_PROP (SUC s0),
                               XP_OR (XP_PROP (SUC s0),XP_NEXT (P_NOT p))),
                            XP_AND
                              (A.R,
                               XP_AND
                                 (XP_NEXT (P_PROP (SUC s0)),
                                  XP_COND
                                    (XP_BIGOR
                                       (MAP XP_PROP
                                          (INTERVAL_LIST
                                             (SUC (SUC s0) +
                                              2 ** SUC (s0 - i0))
                                             (PRE (2 ** SUC (s0 - i0)) +
                                              (SUC (SUC s0) +
                                               2 ** SUC (s0 - i0))))),
                                     XP_CURRENT
                                       (P_VAR_RENAMING
                                          (\n.
                                             (if n >= SUC (SUC s0) then
                                                n + 2 ** SUC (s0 - i0)
                                              else
                                                n))
                                        (VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING
                                             (INTERVAL_LIST (SUC i0)
                                                (SUC s0)) (SUC (SUC s0))
                                             (SUC i0))),
                                     XP_CURRENT
                                       (VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING
                                          (INTERVAL_LIST (SUC i0) (SUC s0))
                                          (SUC (SUC s0)) (SUC i0))))))))),
                          XP_BIGAND (MAP (\xp. xp sv) DS.R)))) = R) ==>
        ((IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE
            (symbolic_kripke_structure S0 R) (MAP (\x. x sv) DS.FC))
        =

      (!K. (A_KS_SEM K (A_UNIV (A,ACCEPT_COND_G p))) =
      UF_KS_SEM K psl))``,

      REPEAT STRIP_TAC THEN
      `!K. UF_KS_SEM K psl = UF_KS_SEM K psl'` by METIS_TAC [UF_KS_SEM___cong] THEN
      ASM_SIMP_TAC std_ss [] THEN

      MATCH_MP_TAC PROBLEM_TO_KRIPKE_STRUCTURE THEN
      Q_TAC EXISTS_TAC `i0` THEN
      Q_TAC EXISTS_TAC `s0` THEN
      Q_TAC EXISTS_TAC `l'` THEN
      Q_TAC EXISTS_TAC `pf` THEN
      Q_TAC EXISTS_TAC `a` THEN
      ASM_REWRITE_TAC[UNION_SUBSET, ETA_THM] THEN
      REPEAT STRIP_TAC THENL [

        UNDISCH_NO_TAC 11 (*SEMI_AUTOMATON_USED_VARS*) THEN
        UNDISCH_NO_TAC 12 (*i0 <= s0*) THEN
        ASM_SIMP_TAC std_ss [SEMI_AUTOMATON_USED_VARS_def, SUBSET_DEF, IN_UNION, IN_INTERVAL_SET, SEMI_AUTOMATON_USED_INPUT_VARS_def,
        IN_DIFF] THEN
        REPEAT WEAKEN_HD_TAC THEN
        REPEAT STRIP_TAC THEN
        RES_TAC,

        FULL_SIMP_TAC std_ss [LTL_EQUIVALENT_INITIAL_def, LTL_SEM_def,
                              LTL_EQUIVALENT_def],

        METIS_TAC[PROP_LOGIC_EQUIVALENT_def],
        METIS_TAC[XPROP_LOGIC_EQUIVALENT_def]
      ]
    );



val PROBLEM_TO_KRIPKE_STRUCTURE___TOTAL___eval =
  store_simp_thm ("PROBLEM_TO_KRIPKE_STRUCTURE___TOTAL___eval",
    ``!A i0 s0 p psl psl' sv.
           IS_TOTAL_SYMBOLIC_SEMI_AUTOMATON A ==>
           (sv = \n:num. 2**(s0 - i0) + s0 + 1 + n) ==>
           (i0 <= s0) ==>
           (A.S = (INTERVAL_SET (SUC i0) s0)) ==>
           (SEMI_AUTOMATON_USED_VARS A SUBSET (INTERVAL_SET 0 s0)) ==>
           (P_USED_VARS p SUBSET (INTERVAL_SET 0 s0)) ==>
            UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE psl psl' ==>
           F_CLOCK_SERE_FREE psl' ==>
           (F_USED_VARS psl' SUBSET (INTERVAL_SET 0 i0)) ==>
           !a DS l' pf.
            LTL_EQUIVALENT
              (LTL_EQUIV
                (LTL_ALWAYS
                  (LTL_PROP
                    (P_FORALL (INTERVAL_LIST (SUC i0) s0)
                        (P_IMPL
                          (VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING
                            (INTERVAL_LIST (SUC i0) s0) (SUC s0) (SUC i0),
                            p)))), PSL_TO_LTL psl')) l' ==>
           LTL_TO_GEN_BUECHI_DS___SEM DS ==>
           (l',a,T,pf) IN DS.B ==>
           DS.IV SUBSET INTERVAL_SET 0 (2**(s0 - i0) + s0) ==>
           !S0 R.

          ((P_AND
            (P_FORALL (INTERVAL_LIST (SUC i0) s0)
               (P_EQUIV
                  (A.S0,
                   VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING
                     (INTERVAL_LIST (SUC i0) s0) (SUC s0) (SUC i0))),
             P_AND
               (LTL_TO_GEN_BUECHI_DS___INITIAL_STATES DS sv,P_NOT (pf sv)))) = S0) /\
          ((XP_AND
            (XP_NEXT_FORALL (INTERVAL_LIST (SUC i0) s0)
               (XP_EQUIV
                  (XP_NEXT
                     (VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING
                        (INTERVAL_LIST (SUC i0) s0) (SUC s0) (SUC i0)),
                   XP_CURRENT_EXISTS (INTERVAL_LIST (SUC i0) s0)
                     (XP_AND
                        (A.R,
                         XP_CURRENT
                           (VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING
                              (INTERVAL_LIST (SUC i0) s0) (SUC s0)
                              (SUC i0)))))),
             XP_BIGAND (MAP (\xp. xp sv) DS.R))) = R)
        ==>

      ((IS_EMPTY_FAIR_SYMBOLIC_KRIPKE_STRUCTURE
          (symbolic_kripke_structure S0 R) (MAP (\x. x sv) DS.FC))
        =

      (!K.
      ((A_KS_SEM K (A_UNIV (A,ACCEPT_COND_G p))) =
      UF_KS_SEM K psl)))``,

      REPEAT STRIP_TAC THEN
      `!K. UF_KS_SEM K psl = UF_KS_SEM K psl'` by METIS_TAC [UF_KS_SEM___cong] THEN
      ASM_SIMP_TAC std_ss [] THEN

      MATCH_MP_TAC PROBLEM_TO_KRIPKE_STRUCTURE___TOTAL THEN
      Q_TAC EXISTS_TAC `i0` THEN
      Q_TAC EXISTS_TAC `s0` THEN
      Q_TAC EXISTS_TAC `l'` THEN
      Q_TAC EXISTS_TAC `pf` THEN
      Q_TAC EXISTS_TAC `a` THEN
      ASM_REWRITE_TAC[UNION_SUBSET, ETA_THM] THEN
      REPEAT STRIP_TAC THENL [

        UNDISCH_NO_TAC 11 (*SEMI_AUTOMATON_USED_VARS*) THEN
        UNDISCH_NO_TAC 12 (*i0 <= s0*) THEN
        ASM_SIMP_TAC std_ss [SEMI_AUTOMATON_USED_VARS_def, SUBSET_DEF, IN_UNION, IN_INTERVAL_SET, SEMI_AUTOMATON_USED_INPUT_VARS_def,
        IN_DIFF] THEN
        REPEAT WEAKEN_HD_TAC THEN
        REPEAT STRIP_TAC THEN
        RES_TAC,

        FULL_SIMP_TAC std_ss [LTL_EQUIVALENT_INITIAL_def, LTL_SEM_def,
                              LTL_EQUIVALENT_def],

        METIS_TAC[PROP_LOGIC_EQUIVALENT_def],
        METIS_TAC[XPROP_LOGIC_EQUIVALENT_def]
      ]);






val VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING___P_USED_VARS =
  prove (``
!i:num j:num. (i <= j) ==> (P_USED_VARS (
VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING
                            (INTERVAL_LIST i j) (SUC j) i) =
INTERVAL_SET i (SUC j+PRE (2 ** SUC (j - i))))``,


SIMP_TAC std_ss [GSYM VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING___HASHTABLE_LIST,
  VAR_RENAMING_HASHTABLE_LIST___P_USED_VARS, LIST_TO_SET___INTERVAL_LIST,
  UNION_EMPTY] THEN
REPEAT STRIP_TAC THEN
`(\x. SET_BINARY_ENCODING_SHIFT i (SUC j) x) =
 SET_BINARY_ENCODING_SHIFT i (SUC j)` by SIMP_TAC std_ss [FUN_EQ_THM] THEN

ASM_SIMP_TAC std_ss [SET_BINARY_ENCODING_SHIFT___IMAGE_THM] THEN
SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_INTERVAL_SET] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
ASM_SIMP_TAC arith_ss []);





fun prepare_input_automaton A =
  let
    val s0 = rand (rand(rator (rator A)))
    val suc_i0 = rand (rator (rand(rator (rator A))))
    val i0 = term_of_int ((int_of_term suc_i0) - 1);


    val i0_le_s0_term = ``(i0:num) <= (s0:num)``;
    val i0_le_s0_term = subst [
      mk_var ("i0", num) |-> i0,
      mk_var ("s0", num) |-> s0] i0_le_s0_term;
    val i0_le_s0  = DECIDE i0_le_s0_term

    val state_vars_term = ``(A:num symbolic_semi_automaton).S = INTERVAL_SET (SUC i0) s0``;
    val state_vars_term = subst [
      mk_var ("A", ``:num symbolic_semi_automaton``) |-> A,
      mk_var ("i0", num) |-> i0,
      mk_var ("s0", num) |-> s0] state_vars_term;
    val state_vars = EQT_ELIM (SIMP_CONV std_ss [symbolic_semi_automaton_REWRITES] state_vars_term)


    val used_vars_term = ``SEMI_AUTOMATON_USED_VARS A SUBSET INTERVAL_SET 0 s0``;
    val used_vars_term = subst [
      mk_var ("A", ``:num symbolic_semi_automaton``) |-> A,
      mk_var ("s0", num) |-> s0] used_vars_term;
    val used_vars = (EQT_ELIM (SIMP_CONV std_ss [SEMI_AUTOMATON_USED_VARS___DIRECT_DEF, SUBSET_DEF, IN_UNION,
     IN_SING, XP_USED_VARS_EVAL, IN_INTERVAL_SET, DISJ_IMP_THM,
     P_USED_VARS_EVAL, symbolic_semi_automaton_REWRITES, NOT_IN_EMPTY] used_vars_term))
  in
    (s0, i0, i0_le_s0, state_vars, used_vars)
  end;


fun prepare_ctl p s0 =
  let
    val used_vars_term = ``P_USED_VARS p SUBSET INTERVAL_SET 0 s0``;
    val used_vars_term = subst [
      mk_var ("p", ``:num prop_logic``) |-> p,
      mk_var ("s0", num) |-> s0] used_vars_term;
    val used_vars = EQT_ELIM (SIMP_CONV std_ss [SEMI_AUTOMATON_USED_VARS___DIRECT_DEF, SUBSET_DEF, IN_UNION,
     IN_SING, XP_USED_VARS_EVAL, IN_INTERVAL_SET, DISJ_IMP_THM, NOT_IN_EMPTY,
     P_USED_VARS_EVAL, symbolic_semi_automaton_REWRITES] used_vars_term)
  in
    used_vars
  end;



val PSL_EQUIVALENT_congs =
  store_thm (
    "PSL_EQUIVALENT_congs",

    ``(!f f'. UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f f' ==>
              UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE (F_NOT f) (F_NOT f')) /\

      (!f1 f1' f2 f2'.
              UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f1 f1' ==>
              UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f2 f2' ==>
              UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE (F_AND (f1, f2)) (F_AND (f1', f2'))) /\

      (!f f'. UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f f' ==>
              UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE (F_NEXT f) (F_NEXT f')) /\

      (!f1 f1' f2 f2'.
              UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f1 f1' ==>
              UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f2 f2' ==>
              UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE (F_UNTIL (f1, f2)) (F_UNTIL (f1', f2'))) /\

      (!f f' r.
              UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f f' ==>
              UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE (F_SUFFIX_IMP (r, f)) (F_SUFFIX_IMP (r, f'))) /\

      (!f f' c.
              UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f f' ==>
              UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE (F_U_CLOCK c f) (F_U_CLOCK c f')) /\

      (!f f' c.
              UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f f' ==>
              UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE (F_W_CLOCK c f) (F_W_CLOCK c f'))``,

    SIMP_TAC std_ss [UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def,
      UnclockedSemanticsTheory.UF_SEM_def, F_U_CLOCK_def, F_W_CLOCK_def,
      F_W_def, F_G_def, F_F_def, F_OR_def] THEN
    REPEAT STRIP_TAC THENL [
      METIS_TAC[IS_INFINITE_TOP_BOTTOM_FREE_PATH___COMPLEMENT],
      METIS_TAC[IS_INFINITE_TOP_BOTTOM_FREE_PATH___RESTN],
      METIS_TAC[IS_INFINITE_TOP_BOTTOM_FREE_PATH___RESTN],
      METIS_TAC[IS_INFINITE_TOP_BOTTOM_FREE_PATH___RESTN],
      METIS_TAC[IS_INFINITE_TOP_BOTTOM_FREE_PATH___RESTN],

      METIS_TAC[IS_INFINITE_TOP_BOTTOM_FREE_PATH___RESTN, IS_INFINITE_TOP_BOTTOM_FREE_PATH___COMPLEMENT]
    ]);


val PSL_EQUIVALENT_rewrites =
  store_thm (
    "PSL_EQUIVALENT_rewrites",

    ``!f. UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE (F_NOT (F_NOT f)) f``,

    SIMP_TAC std_ss [UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def,
      UnclockedSemanticsTheory.UF_SEM_def,
      RewritesPropertiesTheory.COMPLEMENT_COMPLEMENT]);


val UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CLOCK_BOOL_BIGCAT___EVAL =
 prove (
``(!f:'a fl b c.
   UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE
    (F_CLOCK_COMP c (F_SUFFIX_IMP (S_BOOL_BIGCAT [b], f)))
    (F_W_CLOCK c (F_NOT (F_AND (F_NOT (F_NOT (F_STRONG_BOOL b)), F_NOT (F_CLOCK_COMP c f)))))
  ) /\
  (!f:'a fl b1 b2 l c. UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE
    (F_CLOCK_COMP c (F_SUFFIX_IMP (S_BOOL_BIGCAT (b1::b2::l), f)))
    (F_W_CLOCK c (F_NOT (F_AND (
        F_NOT (F_NOT (F_STRONG_BOOL b1)), F_NOT (F_NOT
                 (F_U_CLOCK c
                    (F_NEXT
                       (F_U_CLOCK c
                          (F_NOT (F_CLOCK_COMP c (F_SUFFIX_IMP (S_BOOL_BIGCAT (b2::l), f)))))))))))))``,

  ASSUME_TAC  UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CLOCK_BOOL_BIGCAT THEN
  ASSUME_TAC UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CLOCK_BOOL THEN
  FULL_SIMP_TAC std_ss [UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def] THEN
  FULL_SIMP_TAC std_ss [F_CLOCK_COMP_def, F_WEAK_X_def, F_IMPLIES_def, F_OR_def]);


val UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___BOOL_BIGCAT___EVAL =
REWRITE_RULE [SyntacticSugarTheory.F_IMPLIES_def, SyntacticSugarTheory.F_OR_def] UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___BOOL_BIGCAT;



val psl_equivalent_preorder =
    mk_preorder (UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___TRANS,                             UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___REFL);
val psl_CS = CSFRAG
   {rewrs  = [PSL_EQUIVALENT_rewrites,
    UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CLOCK_BOOL_BIGCAT___EVAL,
    UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___BOOL_BIGCAT___EVAL],
    relations = [psl_equivalent_preorder],
    dprocs = [],
    congs  = [PSL_EQUIVALENT_congs]};
val psl_cs = mk_congset [psl_CS];

val F_SUFFIX_IMP___S_BOOL_BIGCAT_def = Define
  `F_SUFFIX_IMP___S_BOOL_BIGCAT l f = F_SUFFIX_IMP (S_BOOL_BIGCAT l, f)`



fun prepare_psl psl i0 =
  let

    val eval_thm = (REWRITE_CONV [GSYM F_SUFFIX_IMP___S_BOOL_BIGCAT_def] THENC RESTR_EVAL_CONV [``F_SUFFIX_IMP___S_BOOL_BIGCAT``] THENC
    REWRITE_CONV [F_SUFFIX_IMP___S_BOOL_BIGCAT_def]) psl;
    val eval_term = rhs (concl eval_thm);
    val equiv_thm = CONGRUENCE_SIMP_CONV ``UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE`` psl_cs std_ss [] eval_term
    val equiv_thm = (CONV_RULE (RATOR_CONV (ONCE_REWRITE_CONV [GSYM eval_thm]))) equiv_thm
    val equiv_thm = (CONV_RULE (RAND_CONV EVAL_CONV)) equiv_thm

    val eval_term = rand (concl equiv_thm);

    val cs_free_term = mk_comb (``F_CLOCK_SERE_FREE:num fl -> bool``, eval_term);
    val cs_free_thm = EQT_ELIM ((REWRITE_CONV [F_CLOCK_SERE_FREE_def, ProjectionTheory.F_CLOCK_FREE_def, F_SERE_FREE_def]) cs_free_term)


    val used_vars_term = ``F_USED_VARS psl SUBSET INTERVAL_SET 0 i0``;
    val used_vars_term = subst [
      mk_var ("psl", ``:num fl``) |-> eval_term,
      mk_var ("i0", num) |-> i0] used_vars_term;
    val used_vars = EQT_ELIM ((SIMP_CONV std_ss [F_USED_VARS_def, SUBSET_DEF, IN_UNION,
     IN_SING, XP_USED_VARS_EVAL, IN_INTERVAL_SET, DISJ_IMP_THM,
     B_USED_VARS_def, NOT_IN_EMPTY]) used_vars_term)

    val psl_to_ltl_term = mk_comb (``PSL_TO_LTL:num fl -> num ltl``, eval_term);
    val psl_to_ltl = EVAL psl_to_ltl_term
  in
    (eval_term, equiv_thm, cs_free_thm, used_vars, psl_to_ltl)
  end;


(*
val s0_cs = new_compset [P_ASSIGN_TRUE_FALSE___EVAL, IN_SING]
val prop_logic_equivalent_trans_thm = prove (
  ``!p1 p2 p3.
      PROP_LOGIC_EQUIVALENT p1 p2 ==>
      PROP_LOGIC_EQUIVALENT p2 p3 ==>
      PROP_LOGIC_EQUIVALENT p1 p3``,
  SIMP_TAC std_ss [PROP_LOGIC_EQUIVALENT_def]);


fun reduce_S0 S0_thm =
  let
    val thm =  CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [P_EXISTS_def])) S0_thm
    val changed = not ((concl thm) = (concl S0_thm));
  in
    if changed then
        let
          val thm = CONV_RULE (RAND_CONV (CBV_CONV s0_cs)) thm
          val thm = CONV_RULE (RAND_CONV (DEPTH_CONV (reduceLib.RED_CONV))) thm

          val equiv = CONGRUENCE_SIMP_CONV ``PROP_LOGIC_EQUIVALENT:'a prop_logic -> 'a prop_logic -> bool`` prop_logic_nnf_cs std_ss [] (rand (concl thm))

          val new_thm = MATCH_MP prop_logic_equivalent_trans_thm thm
          val new_thm = MATCH_MP new_thm equiv
          val new_thm = reduce_S0 new_thm
        in
          new_thm
        end
    else
      thm
  end;


val r_cs = new_compset [XP_ASSIGN_TRUE_FALSE___EVAL, IN_SING, NOT_IN_EMPTY]
val xprop_logic_equivalent_trans_thm = prove (
  ``!p1 p2 p3.
      XPROP_LOGIC_EQUIVALENT p1 p2 ==>
      XPROP_LOGIC_EQUIVALENT p2 p3 ==>
      XPROP_LOGIC_EQUIVALENT p1 p3``,
  SIMP_TAC std_ss [XPROP_LOGIC_EQUIVALENT_def]);


fun reduce_R R_thm =
  let
    val thm =  CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [XP_CURRENT_EXISTS_def] THENC ONCE_REWRITE_CONV [XP_NEXT_EXISTS_def])) R_thm
    val changed = not ((concl thm) = (concl R_thm));
  in
    if changed then
        let
          val thm = CONV_RULE (RAND_CONV (CBV_CONV r_cs)) thm
          val thm = CONV_RULE (RAND_CONV (DEPTH_CONV (reduceLib.RED_CONV))) thm

          val equiv = CONGRUENCE_SIMP_CONV ``XPROP_LOGIC_EQUIVALENT:'a xprop_logic -> 'a xprop_logic -> bool`` xprop_logic_nnf_cs std_ss [] (rand (concl thm))

          val new_thm = MATCH_MP xprop_logic_equivalent_trans_thm thm
          val new_thm = MATCH_MP new_thm equiv
          val new_thm = reduce_R new_thm
          val _ = print "STEP\n";
        in
          thm
        end
    else
      thm
  end;



fun num_compset () =
  let open computeLib
      val compset = bool_compset()
      val _ = add_thms numeral_redns compset
      val _ = add_conv (numSyntax.div_tm, 2, cbv_DIV_CONV) compset
      val _ = add_conv (numSyntax.mod_tm, 2, cbv_MOD_CONV) compset
  in
    compset
  end;

val r_cs = reduceLib.num_compset ()
val _ = add_thms [XP_ASSIGN_TRUE_FALSE___EVAL, IN_SING, NOT_IN_EMPTY, XP_CURRENT_EXISTS_def, XP_NEXT_EXISTS_def] r_cs

fun reduce_R thm =
  let
    val thm = CONV_RULE (RAND_CONV (CBV_CONV r_cs)) thm
  in
    thm
  end



val t = mk_thm ([], ``XPROP_LOGIC_EQUIVALENT A B``)
fun testCONV t = mk_thm ([], mk_eq (t, mk_var ("XXXXXXXXXXXX", type_of t)));

CONV_RULE (RAND_CONV (testCONV)) t

val x =  time (reduce_R) R_thm

val t = ``XP_ASSIGN_FALSE {5} {} (XP_PROP 72)``
(CBV_CONV r_cs) t
*)


fun ibm_to_ks A p psl =
  let
    val thm = PROBLEM_TO_KRIPKE_STRUCTURE___eval;

    val (s0, i0, i0_le_s0, state_vars, semi_automaton_used_vars) =
      prepare_input_automaton A
    val (psl', equiv_thm, cs_free_thm, psl_used_vars, psl_to_ltl) = prepare_psl psl i0

    val thm = ISPECL [A, i0, s0, p, psl, psl'] thm;
    val thm = MP thm i0_le_s0;
    val thm = MP thm state_vars;
    val thm = MP thm semi_automaton_used_vars;
    val thm = MP thm (prepare_ctl p s0);
    val thm = MP thm equiv_thm
    val thm = MP thm cs_free_thm
    val thm = MP thm psl_used_vars

    val thm = SIMP_RULE arith_ss [psl_to_ltl] thm

    val ltl_term =
      let
        val t = snd (strip_forall (concl thm))
        val t = rand (rator (rand (rator t)))
      in
        t
      end

    val (l', ltl_equiv, ds_thm, ds, pf, b1, b2) = ltl2omega_internal true false true ltl_term
    val a = if b1 then ``T:bool`` else ``F:bool``;
    val thm = ISPECL [a, ds, l', pf] thm;
    val thm = MP thm ltl_equiv;
    val thm = MP thm ds_thm;

    val imp_term = rand (rator (concl thm))
    val imp_thm = EQT_ELIM (REWRITE_CONV [ltl_to_gen_buechi_ds_REWRITES, IN_SING] imp_term)
    val thm = MP thm imp_thm


    val imp_term = rand (rator (concl thm))
    val imp_thm = EQT_ELIM (SIMP_CONV arith_ss [ltl_to_gen_buechi_ds_REWRITES, P_USED_VARS___P_BIGOR___EVAL, SUBSET_DEF,
    IN_INTERVAL_SET, IN_INSERT, NOT_IN_EMPTY,
    IN_UNION] imp_term)
    val thm = MP thm imp_thm

    (*evaluate INTERVAL_LISTS*)
    val i_term = ``INTERVAL_LIST (SUC i0) (SUC s0)``
    val i_term = subst [
      mk_var ("i0", num) |-> i0,
      mk_var ("s0", num) |-> s0] i_term;
    val i_term = rhs (concl (REDUCE_CONV i_term))
    val i1_thm = SIMP_CONV std_ss [INTERVAL_LIST_THM] i_term

    val i_term = ``(INTERVAL_LIST (SUC (SUC s0) + 2 ** SUC (s0 - i0))
                                  (PRE (2 ** SUC (s0 - i0)) +
                                  (SUC (SUC s0) + 2 ** SUC (s0 - i0))))``;
    val i_term = subst [
      mk_var ("i0", num) |-> i0,
      mk_var ("s0", num) |-> s0] i_term;
    val i_term = rhs (concl (REDUCE_CONV i_term))
    val i2_thm = SIMP_CONV std_ss [INTERVAL_LIST_THM] i_term


    val i_term = ``VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING
                              (INTERVAL_LIST (SUC i0) (SUC s0))
                              (SUC (SUC s0)) (SUC i0)``;
    val i_term = subst [
      mk_var ("i0", num) |-> i0,
      mk_var ("s0", num) |-> s0] i_term;
    val i_term = rhs (concl ((REDUCE_CONV THENC REWRITE_CONV [i1_thm]) i_term))
    val i3_thm = SIMP_CONV std_ss [VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING_def] i_term


    val thm = SIMP_RULE list_ss [ltl_to_gen_buechi_ds_REWRITES,
     LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def,
     symbolic_semi_automaton_REWRITES,
     P_BIGOR_def, i1_thm, i2_thm, i3_thm, P_BIGAND_def, XP_BIGAND_def,
     XP_BIGOR_def, P_VAR_RENAMING_EVAL, XP_NEXT_THM, XP_CURRENT_THM] thm
  in
    thm
  end;


fun make_total_thm A =
  let
    val t = liteLib.mk_icomb (``IS_TOTAL_SYMBOLIC_SEMI_AUTOMATON:'a symbolic_semi_automaton -> bool``, A);
  in
    mk_oracle_thm "TotalityAssumed" ([], t)
  end;



val P_USED_VARS___P_FORALL___IMPL =
  prove (``
      !l p P. (!x. x IN P_USED_VARS p ==> P x) ==>
              (!x. x IN P_USED_VARS (P_FORALL l p) ==> P x)``,
  SIMP_TAC std_ss [P_FORALL___P_USED_VARS, IN_DIFF]);

fun ibm_to_ks_total A p psl total_thm =
  let
    val thm = PROBLEM_TO_KRIPKE_STRUCTURE___TOTAL___eval;

    val (s0, i0, i0_le_s0, state_vars, semi_automaton_used_vars) =
      prepare_input_automaton A
    val (psl', equiv_thm, cs_free_thm, psl_used_vars, psl_to_ltl) = prepare_psl psl i0

    val thm = ISPECL [A, i0, s0, p, psl, psl'] thm;
    val thm = MP thm total_thm;
    val thm = MP thm i0_le_s0;
    val thm = MP thm state_vars;
    val thm = MP thm semi_automaton_used_vars;
    val thm = MP thm (prepare_ctl p s0);

    val thm = MP thm equiv_thm
    val thm = MP thm cs_free_thm
    val thm = MP thm psl_used_vars

    val thm = SIMP_RULE arith_ss [psl_to_ltl] thm

    val ltl_term =
      let
        val t = snd (strip_forall (concl thm))
        val t = rand (rator (rand (rator t)))
      in
        t
      end

    val (l', ltl_equiv, ds_thm, ds, pf, b1, b2) = ltl2omega_internal true false true ltl_term
    val a = if b1 then ``T:bool`` else ``F:bool``;
    val thm = ISPECL [a, ds, l', pf] thm;
    val thm = MP thm ltl_equiv;
    val thm = MP thm ds_thm;

    val imp_term = rand (rator (concl thm))
    val imp_thm = EQT_ELIM (REWRITE_CONV [ltl_to_gen_buechi_ds_REWRITES, IN_SING] imp_term)
    val thm = MP thm imp_thm


    val imp_term = rand (rator (concl thm))
    val imp_thm = SIMP_CONV arith_ss [ltl_to_gen_buechi_ds_REWRITES, SUBSET_DEF,
    IN_INTERVAL_SET, IN_INSERT, NOT_IN_EMPTY, P_USED_VARS_EVAL,
    IN_UNION, DISJ_IMP_THM] imp_term
    val imp2_thm =
      HO_PART_MATCH (fn t => rand t) P_USED_VARS___P_FORALL___IMPL (rhs (concl imp_thm))
    val imp2_thm = SIMP_RULE std_ss [P_USED_VARS_EVAL,
      IN_UNION, DISJ_IMP_THM, IN_SING] imp2_thm
    val (i, j) = let
        val imp2_term = rand (rator (concl (imp2_thm)))
        val interval_term = rand (rator (rator (rand (rand (rand (rator (snd (strip_forall (imp2_term)))))))));
        val j = rand (interval_term)
        val i = rand (rator (interval_term))
      in
        (i, j)
      end;
    val P_USED_VARS___VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING___EVAL =
      SIMP_RULE std_ss [] (SPECL [i, j] VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING___P_USED_VARS);
    val imp2_thm =
      SIMP_RULE std_ss [P_USED_VARS___VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING___EVAL,
      IN_INTERVAL_SET] imp2_thm

    val imp_thm = REWRITE_RULE [imp2_thm] imp_thm
    val thm = MP thm imp_thm


    (*evaluate INTERVAL_LISTS*)
    val i_term = ``INTERVAL_LIST (SUC i0) s0``
    val i_term = subst [
      mk_var ("i0", num) |-> i0,
      mk_var ("s0", num) |-> s0] i_term;
    val i_term = rhs (concl (REDUCE_CONV i_term))
    val i1_thm = SIMP_CONV std_ss [INTERVAL_LIST_THM] i_term

    val i_term = ``VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING
                              (INTERVAL_LIST (SUC i0) s0)
                              (SUC s0) (SUC i0)``;
    val i_term = subst [
      mk_var ("i0", num) |-> i0,
      mk_var ("s0", num) |-> s0] i_term;
    val i_term = rhs (concl ((REDUCE_CONV THENC REWRITE_CONV [i1_thm]) i_term))
    val i2_thm = SIMP_CONV std_ss [VAR_RENAMING_HASHTABLE_LIST___BINARY_ENCODING_def] i_term


    val thm = SIMP_RULE list_ss [ltl_to_gen_buechi_ds_REWRITES,
     LTL_TO_GEN_BUECHI_DS___INITIAL_STATES_def,
     symbolic_semi_automaton_REWRITES,
     P_BIGOR_def, i1_thm, i2_thm, P_BIGAND_def, XP_BIGAND_def,
     XP_BIGOR_def, P_VAR_RENAMING_EVAL, XP_NEXT_THM, XP_CURRENT_THM,
     XP_CURRENT_NEXT___FORALL, XP_CURRENT_NEXT___EXISTS] thm
  in
    thm
  end;


fun ibm_to_ks_total_cheat A p psl =
  ibm_to_ks_total A p psl (make_total_thm A);

fun ibm_to_ks_clock A p psl =
  let
    val psl_nc = liteLib.mk_icomb (``(F_CLOCK_COMP:'a bexp -> 'a fl -> 'a fl) B_TRUE``, psl);
    val thm = ibm_to_ks A p psl_nc;
    val thm = REWRITE_RULE [GSYM F_KS_SEM___TO___UF_KS_SEM] thm;
  in
    thm
  end;


fun ibm_to_ks_clock_total A p psl total_thm =
  let
    val psl_nc = liteLib.mk_icomb (``(F_CLOCK_COMP:'a bexp -> 'a fl -> 'a fl) B_TRUE``, psl);
    val thm = ibm_to_ks_total A p psl_nc total_thm;
    val thm = REWRITE_RULE [GSYM F_KS_SEM___TO___UF_KS_SEM] thm;
  in
    thm
  end;

fun ibm_to_ks_clock_total_cheat A p psl =
  let
    val psl_nc = liteLib.mk_icomb (``(F_CLOCK_COMP:'a bexp -> 'a fl -> 'a fl) B_TRUE``, psl);
    val thm = ibm_to_ks_total_cheat A p psl_nc;
    val thm = REWRITE_RULE [GSYM F_KS_SEM___TO___UF_KS_SEM] thm;
  in
    thm
  end;


fun model_check_ibm total A p psl =
    let
      val _ = print "Translating problem to kripke structure ...\n";
      val thm = if total then ibm_to_ks_total_cheat A p psl else ibm_to_ks A p psl;
      val ks_term = lhs (concl thm);
      val _ = print "Running SMV ...\n";
      val erg = modelCheckFairEmptyness ks_term thm;
      val _ = print "Done!\n";
      val thm = if erg then (SOME (mk_thm ([], rand (concl thm)))) else NONE
    in
      thm
    end

end


