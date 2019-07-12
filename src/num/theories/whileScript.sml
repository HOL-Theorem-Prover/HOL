(*===========================================================================*)
(* Define WHILE loops, give Hoare rules, and define LEAST operator as a      *)
(* binder.                                                                   *)
(*===========================================================================*)

open HolKernel boolLib Parse Prim_rec simpLib boolSimps metisLib
     combinTheory prim_recTheory arithmeticTheory BasicProvers
     optionTheory

val _ = new_theory "while";

local open OpenTheoryMap
  val ns = ["While"]
in
  fun ot0 x y = OpenTheory_const_name{const={Thy="while",Name=x},name=(ns,y)}
  fun ot x = ot0 x x
end

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
val _ = ot0 "WHILE" "while"

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

val _ = ot0 "LEAST" "least"
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

val LEAST_T = store_thm(
  "LEAST_T[simp]",
  ``(LEAST x. T) = 0``,
  DEEP_INTRO_TAC LEAST_ELIM THEN SIMP_TAC (srw_ss()) [] THEN
  Q.X_GEN_TAC `n` THEN STRIP_TAC THEN SPOSE_NOT_THEN ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [NOT_ZERO_LT_ZERO] THEN METIS_TAC[]);

Theorem LEAST_LESS_EQ[simp]:
  (LEAST x. y <= x) = y
Proof
  DEEP_INTRO_TAC LEAST_ELIM >> SRW_TAC [][]
  >- (Q.EXISTS_TAC ‘y’ >> SIMP_TAC (srw_ss()) [LESS_EQ_REFL]) >>
  FULL_SIMP_TAC (srw_ss()) [LESS_OR_EQ] >> RES_TAC >>
  FULL_SIMP_TAC (srw_ss()) []
QED

(* ----------------------------------------------------------------------
    OLEAST ("option LEAST") returns NONE if the argument is a predicate
    that is everywhere false.  Otherwise it returns SOME n, where n is the
    least number making the predicate true.
   ---------------------------------------------------------------------- *)

val OLEAST_def = new_definition(
  "OLEAST_def",
  ``(OLEAST) P = if ?n. P n then SOME (LEAST n. P n) else NONE``)
val _ = set_fixity "OLEAST" Binder

val OLEAST_INTRO = store_thm(
  "OLEAST_INTRO",
  ``((!n. ~ P n) ==> Q NONE) /\
    (!n. P n /\ (!m. m < n ==> ~P m) ==> Q (SOME n)) ==>
    Q ((OLEAST) P)``,
  STRIP_TAC THEN SIMP_TAC (srw_ss()) [OLEAST_def] THEN SRW_TAC [][] THENL [
    DEEP_INTRO_TAC LEAST_ELIM THEN METIS_TAC [],
    FULL_SIMP_TAC (srw_ss()) []
  ]);

val OLEAST_EQNS = store_thm(
  "OLEAST_EQNS",
  ``((OLEAST n. n = x) = SOME x) /\
    ((OLEAST n. x = n) = SOME x) /\
    ((OLEAST n. F) = NONE) /\
    ((OLEAST n. T) = SOME 0)``,
  REPEAT STRIP_TAC THEN DEEP_INTRO_TAC OLEAST_INTRO THEN SRW_TAC [][] THEN
  METIS_TAC [arithmeticTheory.NOT_ZERO_LT_ZERO]);
val _ = export_rewrites ["OLEAST_EQNS"]

val OLEAST_EQ_NONE = Q.store_thm(
  "OLEAST_EQ_NONE[simp]",
  ‘((OLEAST) P = NONE) <=> !n. ~P n’,
  DEEP_INTRO_TAC OLEAST_INTRO >> SRW_TAC [][] >> METIS_TAC[]);

val OLEAST_EQ_SOME = Q.store_thm(
  "OLEAST_EQ_SOME",
  ‘((OLEAST) P = SOME n) <=> P n /\ !m. m < n ==> ~P m’,
  DEEP_INTRO_TAC OLEAST_INTRO >>
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM] >> REPEAT STRIP_TAC >>
  METIS_TAC[NOT_LESS, LESS_EQUAL_ANTISYM]);

(* ----------------------------------------------------------------------
    OWHILE ("option while") which returns SOME result if the loop
    terminates, NONE otherwise.
   ---------------------------------------------------------------------- *)


val OWHILE_def = new_definition(
  "OWHILE_def",
  ``OWHILE G f s = if ?n. ~ G (FUNPOW f n s) then
                     SOME (FUNPOW f (LEAST n. ~ G (FUNPOW f n s)) s)
                   else NONE``)

val LEAST_ELIM_TAC = DEEP_INTRO_TAC LEAST_ELIM

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
      DEEP_INTROk_TAC LEAST_ELIM
        (FULL_SIMP_TAC (srw_ss()) [FUNPOW] THEN CONJ_TAC THEN1
          (Q.EXISTS_TAC `SUC m` THEN SRW_TAC [][FUNPOW])) THEN
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

val IF_SOME_EQ_SOME_LEMMA = prove(
  ``!b (x:'a) y. ((if b then SOME x else NONE) = SOME y) <=> b /\ (x = y)``,
  Cases THEN
  FULL_SIMP_TAC bool_ss [optionTheory.NOT_NONE_SOME,optionTheory.SOME_11]);

val OWHILE_IND = store_thm(
  "OWHILE_IND",
  ``!P G (f:'a->'a).
      (!s. ~(G s) ==> P s s) /\
      (!s1 s2. G s1 /\ P (f s1) s2 ==> P s1 s2) ==>
      !s1 s2. (OWHILE G f s1 = SOME s2) ==> P s1 s2``,
  SIMP_TAC bool_ss [OWHILE_def,IF_SOME_EQ_SOME_LEMMA] THEN REPEAT STRIP_TAC
  THEN (Q.SPEC `\n. ~G (FUNPOW f n s1)` LEAST_EXISTS_IMP
      |> SIMP_RULE bool_ss [PULL_EXISTS] |> IMP_RES_TAC)
  THEN NTAC 2 (POP_ASSUM MP_TAC)
  THEN Q.SPEC_TAC (`($LEAST (\n. ~G (FUNPOW f n s1)))`,`k`)
  THEN Q.SPEC_TAC (`s1`,`s1`)
  THEN Induct_on `k` THEN FULL_SIMP_TAC bool_ss [FUNPOW]
  THEN REPEAT STRIP_TAC
  THEN Q.PAT_ASSUM `!xx yy. bb` MATCH_MP_TAC
  THEN STRIP_TAC THEN1
   (`0 < SUC k` by REWRITE_TAC [prim_recTheory.LESS_0]
    THEN RES_TAC THEN FULL_SIMP_TAC bool_ss [FUNPOW])
  THEN FULL_SIMP_TAC bool_ss [AND_IMP_INTRO]
  THEN Q.PAT_ASSUM `!s1. bb /\ bbb ==> bbbb` MATCH_MP_TAC
  THEN FULL_SIMP_TAC bool_ss [] THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC prim_recTheory.LESS_MONO THEN RES_TAC
  THEN FULL_SIMP_TAC bool_ss [FUNPOW]);

val _ =
 computeLib.add_persistent_funs
   ["WHILE"
   ,"LEAST_DEF"];

val _ = export_theory();
