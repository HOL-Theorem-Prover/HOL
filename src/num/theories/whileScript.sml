(*===========================================================================*)
(* Define WHILE loops, give Hoare rules, and define LEAST operator as a      *)
(* binder.                                                                   *)
(*===========================================================================*)

structure whileScript =
struct

open HolKernel boolLib Parse Prim_rec simpLib boolSimps metisLib
     combinTheory prim_recTheory arithmeticTheory BasicProvers
     optionTheory

val _ = new_theory "while";

fun INDUCT_TAC g = INDUCT_THEN numTheory.INDUCTION ASSUME_TAC g;

val cond_lemma = prove(
  ``(if ~p then q else r) = (if p then r else q)``,
  Q.ASM_CASES_TAC `p` THEN ASM_REWRITE_TAC []);

(* ----------------------------------------------------------------------
    Existence of WHILE
   ---------------------------------------------------------------------- *)

val ITERATION = Q.store_thm
("ITERATION",
  `!P g. ?f. !x. f x = if P x then x else f (g x)`,
  REPEAT GEN_TAC THEN
  Q.EXISTS_TAC `\x. if ?n. P (FUNPOW g n x) then
                      FUNPOW g (@n. P (FUNPOW g n x) /\
                                    !m.  m < n ==> ~P (FUNPOW g m x)) x
                    else ARB` THEN BETA_TAC THEN
  GEN_TAC THEN COND_CASES_TAC THENL [
    POP_ASSUM STRIP_ASSUME_TAC THEN
    COND_CASES_TAC THENL [
      SELECT_ELIM_TAC THEN CONJ_TAC THENL [
        Q.EXISTS_TAC `0` THEN
        ASM_REWRITE_TAC [FUNPOW, NOT_LESS_0],
        Q.X_GEN_TAC `m` THEN REPEAT STRIP_TAC THEN
        Q.SUBGOAL_THEN `m = 0` (fn th => REWRITE_TAC [th, FUNPOW]) THEN
        Q.SPEC_THEN `m` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC)
                    num_CASES THEN
        REWRITE_TAC [] THEN
        FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
        ASM_REWRITE_TAC [FUNPOW, LESS_0]
      ],
      SELECT_ELIM_TAC THEN
      CONJ_TAC THENL [
        Q.SPEC_THEN `\n. P (FUNPOW g n x)` (IMP_RES_TAC o BETA_RULE) WOP THEN
        METIS_TAC [],
        Q.X_GEN_TAC `m` THEN REPEAT STRIP_TAC THEN
        Q.SUBGOAL_THEN `?p. m = SUC p` (CHOOSE_THEN SUBST_ALL_TAC) THENL [
          Q.SPEC_THEN `m` (REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC)
                      num_CASES THEN
          FULL_SIMP_TAC bool_ss [FUNPOW] THEN METIS_TAC [],
          ALL_TAC
        ] THEN
        FULL_SIMP_TAC bool_ss [FUNPOW] THEN
        Q.SUBGOAL_THEN `?n. P (FUNPOW g n (g x))`
                       (fn th => REWRITE_TAC [th]) THEN1 METIS_TAC [] THEN
        POP_ASSUM (Q.SPEC_THEN `SUC m` (ASSUME_TAC o GEN_ALL o
                                        SIMP_RULE bool_ss [FUNPOW,
                                                           LESS_MONO_EQ])) THEN
        SELECT_ELIM_TAC THEN CONJ_TAC THENL [
          METIS_TAC [],
          Q.X_GEN_TAC `m` THEN REPEAT STRIP_TAC THEN
          METIS_TAC [LESS_LESS_CASES]
        ]
      ]
    ],
    POP_ASSUM (ASSUME_TAC o SIMP_RULE bool_ss []) THEN
    FIRST_ASSUM (ASSUME_TAC o SIMP_RULE bool_ss [FUNPOW] o
                 GEN_ALL o SPEC ``SUC n``) THEN
    ASM_REWRITE_TAC [] THEN METIS_TAC [FUNPOW]
  ]);


(*---------------------------------------------------------------------------*)
(*  WHILE = |- !P g x. WHILE P g x = if P x then WHILE P g (g x) else x      *)
(*---------------------------------------------------------------------------*)

val WHILE = new_specification
 ("WHILE", ["WHILE"],
  (CONV_RULE (BINDER_CONV SKOLEM_CONV THENC SKOLEM_CONV) o GEN_ALL o
   REWRITE_RULE [o_THM, cond_lemma] o
   SPEC ``$~ o P : 'a -> bool``) ITERATION);


val WHILE_INDUCTION = Q.store_thm
("WHILE_INDUCTION",
 `!B C R.
     WF R /\ (!s. B s ==> R (C s) s)
     ==> !P. (!s. (B s ==> P (C s)) ==> P s) ==> !v. P v`,
 METIS_TAC [relationTheory.WF_INDUCTION_THM]);


val HOARE_SPEC_DEF = new_definition
 ("HOARE_SPEC_DEF",
 ``HOARE_SPEC P C Q = !s. P s ==> Q (C s)``);

(*---------------------------------------------------------------------------
       The while rule from Hoare logic, total correctness version.
 ---------------------------------------------------------------------------*)

val WHILE_RULE = Q.store_thm
("WHILE_RULE",
 `!R B C.
     WF R /\ (!s. B s ==> R (C s) s)
      ==>
        HOARE_SPEC (\s. P s /\ B s) C P
     (*------------------------------------------*) ==>
        HOARE_SPEC P (WHILE B C) (\s. P s /\ ~B s)`,
 REPEAT GEN_TAC THEN STRIP_TAC
  THEN REWRITE_TAC [HOARE_SPEC_DEF] THEN BETA_TAC THEN DISCH_TAC
  THEN MP_TAC (SPEC_ALL WHILE_INDUCTION) THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN HO_MATCH_MP_TAC (* recInduct *)
  THEN METIS_TAC [WHILE]);


(*---------------------------------------------------------------------------*)
(* LEAST number satisfying a predicate.                                      *)
(*---------------------------------------------------------------------------*)

val LEAST_DEF = new_definition(
  "LEAST_DEF",
  ``LEAST P = WHILE ($~ o P) SUC 0``);

val _ = set_fixity "LEAST" Binder;

val LEAST_INTRO = store_thm(
  "LEAST_INTRO",
  ``!P x. P x ==> P ($LEAST P)``,
  GEN_TAC THEN SIMP_TAC (srw_ss()) [LEAST_DEF] THEN
  Q_TAC SUFF_TAC `!m n. P (m + n) ==> P (WHILE ($~ o P) SUC n)`
  THENL [
    SRW_TAC [][] THEN
    FIRST_X_ASSUM (Q.SPECL_THEN [`x`,`0`] MP_TAC) THEN
    ASM_SIMP_TAC bool_ss [ADD_CLAUSES],
    ALL_TAC
  ] THEN
  INDUCT_TAC THENL [
    ONCE_REWRITE_TAC [WHILE] THEN
    ASM_SIMP_TAC bool_ss [ADD_CLAUSES, o_THM],
    ONCE_REWRITE_TAC [WHILE] THEN
    SRW_TAC [][ADD_CLAUSES] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC bool_ss [ADD_CLAUSES]
  ]);

val LESS_LEAST = store_thm(
  "LESS_LEAST",
  ``!P m. m < $LEAST P ==> ~ P m``,
  GEN_TAC THEN
  Q.ASM_CASES_TAC `?x. P x` THENL [
    POP_ASSUM STRIP_ASSUME_TAC THEN
    REWRITE_TAC [LEAST_DEF] THEN
    Q_TAC SUFF_TAC `!y n. n + y < WHILE ($~ o P) SUC n ==> ~P(n + y)` THENL [
      STRIP_TAC THEN GEN_TAC THEN
      POP_ASSUM (Q.SPECL_THEN [`m`, `0`] MP_TAC) THEN
      SIMP_TAC bool_ss [ADD_CLAUSES],
      ALL_TAC
    ] THEN
    INDUCT_TAC THENL [
      ONCE_REWRITE_TAC [WHILE] THEN SRW_TAC [][LESS_REFL, ADD_CLAUSES],
      GEN_TAC THEN
      Q.SUBGOAL_THEN `n + SUC y = SUC n + y` SUBST_ALL_TAC THEN1
        SRW_TAC [][ADD_CLAUSES] THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      RULE_ASSUM_TAC (ONCE_REWRITE_RULE [WHILE]) THEN
      Q.ASM_CASES_TAC `P n` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
      Q.SUBGOAL_THEN `SUC n + y = n + SUC y` SUBST_ALL_TAC THEN1
        SRW_TAC [][ADD_CLAUSES] THEN
      METIS_TAC [LESS_ADD_SUC, LESS_TRANS, LESS_REFL]
    ],
    METIS_TAC []
  ]);

val FULL_LEAST_INTRO = store_thm(
  "FULL_LEAST_INTRO",
  ``!x. P x ==> P ($LEAST P) /\ $LEAST P <= x``,
  METIS_TAC [LEAST_INTRO, NOT_LESS, LESS_LEAST]);

val LEAST_ELIM = store_thm(
  "LEAST_ELIM",
  ``!Q P. (?n. P n) /\ (!n. (!m. m < n ==> ~ P m) /\ P n ==> Q n) ==>
          Q ($LEAST P)``,
  METIS_TAC [LEAST_INTRO, LESS_LEAST]);

val LEAST_EXISTS = store_thm
  ("LEAST_EXISTS",
   ``!p. (?n. p n) = (p ($LEAST p) /\ !n. n < $LEAST p ==> ~p n)``,
   GEN_TAC
   THEN MATCH_MP_TAC EQ_TRANS
   THEN Q.EXISTS_TAC `?n. p n /\ (!m. m < n ==> ~p m)`
   THEN CONJ_TAC
   THENL [(Tactical.REVERSE EQ_TAC THEN1 METIS_TAC [])
          THEN REPEAT STRIP_TAC
          THEN CCONTR_TAC
          THEN (SUFF_TAC ``!n : num. ~p n`` THEN1 METIS_TAC [])
          THEN HO_MATCH_MP_TAC COMPLETE_INDUCTION
          THEN METIS_TAC [],
          (Tactical.REVERSE EQ_TAC THEN1 METIS_TAC [])
          THEN STRIP_TAC
          THEN METIS_TAC [LESS_LEAST, LEAST_INTRO]]);

val LEAST_EXISTS_IMP = store_thm
  ("LEAST_EXISTS_IMP",
   ``!p. (?n. p n) ==> (p ($LEAST p) /\ !n. n < $LEAST p ==> ~p n)``,
   REWRITE_TAC [LEAST_EXISTS]);

val LEAST_EQ = store_thm(
  "LEAST_EQ",
  ``((LEAST n. n = x) = x) /\ ((LEAST n. x = n) = x)``,
  CONJ_TAC THEN
  Q.SPEC_THEN `\n. n = x` (MATCH_MP_TAC o BETA_RULE) LEAST_ELIM THEN
  SIMP_TAC (srw_ss()) []);
val _ = export_rewrites ["LEAST_EQ"]

(* ----------------------------------------------------------------------
    OWHILE ("option while") which returns SOME result if the loop
    terminates, NONE otherwise.
   ---------------------------------------------------------------------- *)


val OWHILE_def = new_definition(
  "OWHILE_def",
  ``OWHILE G f s = if ?n. ~ G (FUNPOW f n s) then
                     SOME (FUNPOW f (LEAST n. ~ G (FUNPOW f n s)) s)
                   else NONE``)

fun LEAST_ELIM_TAC (asl, w) = let
  val least_terms = find_terms (fn t => total rator t = SOME ``(LEAST)``) w
  val tbc = TRY_CONV BETA_CONV
  fun doit t =
    if free_in t w then
      CONV_TAC (UNBETA_CONV t) THEN
      MATCH_MP_TAC LEAST_ELIM THEN
      CONV_TAC
        (FORK_CONV
           (BINDER_CONV tbc, (* ?n. P n *)
            BINDER_CONV      (* !n. (!m. m < n ==> ~P m) /\ P n ==> Q n *)
              (FORK_CONV
                 (FORK_CONV
                    (BINDER_CONV (RAND_CONV (RAND_CONV tbc)), (* !m.... *)
                     tbc), (* P n *)
                    tbc))))
    else NO_TAC
in
  FIRST (map doit least_terms)
end (asl, w)


val OWHILE_THM = store_thm(
  "OWHILE_THM",
  ``OWHILE G f (s:'a) = if G s then OWHILE G f (f s) else SOME s``,
  SIMP_TAC (srw_ss()) [OWHILE_def] THEN
  ASM_CASES_TAC ``(G:'a ->bool) s`` THENL [
    ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC ``?n. ~ (G:'a->bool) (FUNPOW f n s)`` THENL [
      ASM_REWRITE_TAC [] THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      Q.SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THEN1
        (STRIP_TAC THEN FULL_SIMP_TAC (srw_ss()) []) THEN
      Q.SUBGOAL_THEN `?m. n = SUC m` STRIP_ASSUME_TAC THEN1
        (Q.SPEC_THEN `n` FULL_STRUCT_CASES_TAC num_CASES THEN
         FULL_SIMP_TAC (srw_ss()) []) THEN
      Q.SUBGOAL_THEN `?n. ~G(FUNPOW f n (f s))` ASSUME_TAC THEN1
        (Q.EXISTS_TAC `m` THEN FULL_SIMP_TAC (srw_ss()) [FUNPOW]) THEN
      POP_ASSUM (fn th => REWRITE_TAC [th]) THEN
      SRW_TAC [][] THEN
      LEAST_ELIM_TAC THEN FULL_SIMP_TAC (srw_ss()) [FUNPOW] THEN CONJ_TAC THEN1
        (Q.EXISTS_TAC `SUC m` THEN SRW_TAC [][FUNPOW]) THEN
      Q.X_GEN_TAC `N` THEN STRIP_TAC THEN
      LEAST_ELIM_TAC THEN CONJ_TAC THEN1 METIS_TAC [] THEN
      REWRITE_TAC [] THEN
      Q.X_GEN_TAC `M` THEN STRIP_TAC THEN
      Q_TAC SUFF_TAC `N = SUC M` THEN1 SIMP_TAC (srw_ss()) [FUNPOW] THEN
      Q.SPECL_THEN [`N`, `SUC M`] STRIP_ASSUME_TAC LESS_LESS_CASES THENL [
        (* N < SUC M *)
        Q.SUBGOAL_THEN `(N = 0) \/ (?N0. N = SUC N0)` STRIP_ASSUME_TAC THEN1
          METIS_TAC [num_CASES] THEN
        FULL_SIMP_TAC (srw_ss()) [LESS_MONO_EQ, FUNPOW] THEN
        METIS_TAC [],
        (* SUC M < N *)
        RES_TAC THEN FULL_SIMP_TAC (srw_ss()) [FUNPOW]
      ],

      FULL_SIMP_TAC (srw_ss()) [] THEN
      POP_ASSUM (Q.SPEC_THEN `SUC n` (ASSUME_TAC o Q.GEN `n`)) THEN
      FULL_SIMP_TAC (srw_ss()) [FUNPOW]
    ],

    ASM_REWRITE_TAC [] THEN
    Q.SUBGOAL_THEN `?n. ~G(FUNPOW f n s)` ASSUME_TAC THEN1
      (Q.EXISTS_TAC `0` THEN SRW_TAC [][]) THEN
    ASM_REWRITE_TAC [optionTheory.SOME_11] THEN
    LEAST_ELIM_TAC THEN ASM_REWRITE_TAC [] THEN
    Q.X_GEN_TAC `N` THEN STRIP_TAC THEN
    Q_TAC SUFF_TAC `N = 0` THEN1 SRW_TAC [][] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
    ASM_SIMP_TAC (srw_ss()) [] THEN METIS_TAC [NOT_ZERO_LT_ZERO]
  ]);

val OWHILE_EQ_NONE = store_thm(
  "OWHILE_EQ_NONE",
  ``(OWHILE G f (s:'a) = NONE) <=> !n. G (FUNPOW f n s)``,
  SRW_TAC [][OWHILE_def] THEN FULL_SIMP_TAC (srw_ss()) []);

val OWHILE_ENDCOND = store_thm(
  "OWHILE_ENDCOND",
  ``(OWHILE G f (s:'a) = SOME s') ==> ~G s'``,
  SRW_TAC [][OWHILE_def] THEN LEAST_ELIM_TAC THEN METIS_TAC []);

val OWHILE_WHILE = store_thm(
  "OWHILE_WHILE",
  ``(OWHILE G f s = SOME s') ==> (WHILE G f s = s')``,
  SIMP_TAC (srw_ss()) [OWHILE_def] THEN
  STRIP_TAC THEN
  SRW_TAC [][] THEN LEAST_ELIM_TAC THEN CONJ_TAC THEN1 METIS_TAC [] THEN
  REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN
  Q.X_GEN_TAC `n` THEN MAP_EVERY Q.ID_SPEC_TAC [`s`, `n`] THEN
  INDUCT_TAC THENL [
    ONCE_REWRITE_TAC [WHILE] THEN SRW_TAC [][],
    SRW_TAC [][FUNPOW] THEN
    ONCE_REWRITE_TAC [WHILE] THEN
    Q.SUBGOAL_THEN `G s` (fn th => REWRITE_TAC [th]) THEN1
      (FIRST_X_ASSUM (Q.SPEC_THEN `0` MP_TAC) THEN
       SRW_TAC [][prim_recTheory.LESS_0]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN SRW_TAC [][] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `SUC m` MP_TAC) THEN
    SRW_TAC [][FUNPOW, LESS_MONO_EQ]
  ]);

val OWHILE_INV_IND = store_thm(
  "OWHILE_INV_IND",
  ``!G f s. P s /\ (!x. P x /\ G x ==> P (f x)) ==>
            !s'. (OWHILE G f s = SOME s') ==> P s'``,
  SIMP_TAC (srw_ss()) [OWHILE_def] THEN REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [][] THEN
  LEAST_ELIM_TAC THEN CONJ_TAC THEN1 METIS_TAC [] THEN
  REWRITE_TAC [] THEN POP_ASSUM (K ALL_TAC) THEN Q.X_GEN_TAC `n` THEN
  Q.UNDISCH_THEN `P s` MP_TAC THEN REWRITE_TAC [AND_IMP_INTRO] THEN
  MAP_EVERY Q.ID_SPEC_TAC [`s`, `n`] THEN INDUCT_TAC THENL [
    SRW_TAC [][],
    SRW_TAC [][FUNPOW] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM (fn th => Q.SPEC_THEN `0` MP_TAC th THEN
                            Q.SPEC_THEN `SUC m` (MP_TAC o Q.GEN `m`) th) THEN
    SRW_TAC [][LESS_MONO_EQ, FUNPOW, LESS_0]
  ]);

val _ =
 computeLib.add_persistent_funs
   [("WHILE",WHILE),
    ("LEAST_DEF",LEAST_DEF)];

val _ = export_theory();

end
