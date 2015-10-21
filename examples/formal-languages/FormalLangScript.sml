(*****************************************************************************)
(* Formal Language Theory                                                    *)
(*                                                                           *)
(* A formal language is a set of strings over an alphabet. The notion of     *)
(* 'a list exactly captures such strings. We define the following language   *)
(* operations: concatenation, iterated concatenation, and Kleene Star. We    *)
(* prove a collection of lemmas about these operations, including Arden's    *)
(* lemma.                                                                    *)
(*****************************************************************************)


(*===========================================================================*)
(*   Load and open context theories and proof support (lists and sets).      *)
(*===========================================================================*)

open HolKernel boolLib bossLib Parse;
open pred_setLib pred_setTheory arithmeticTheory listTheory;

val _ = new_theory "FormalLang";

(*---------------------------------------------------------------------------*)
(* Basic simplification support                                              *)
(*---------------------------------------------------------------------------*)

val APPEND_EQNS = LIST_CONJ [APPEND,APPEND_NIL,APPEND_eq_NIL];

val basic_ss = list_ss ++ PRED_SET_ss ++ rewrites [APPEND_EQNS];


(*---------------------------------------------------------------------------*)
(* A language is a set of strings over an alphabet. A string is represented  *)
(* by an 'a list.                                                            *)
(*---------------------------------------------------------------------------*)

val _ = type_abbrev ("lang", ``:'a list set``);

(*---------------------------------------------------------------------------*)
(* Binary language concatenation. Right infix                                *)
(*---------------------------------------------------------------------------*)

val dot_def =
 Define
  `$dot A B = {x ++ y | x IN A /\ y IN B}`;

val _ = set_fixity "dot" (Infixr 675);

(*---------------------------------------------------------------------------*)
(* Some lemmas about language concatenation.                                 *)
(*---------------------------------------------------------------------------*)

val IN_dot = Q.store_thm
("IN_dot",
`!w A B. w IN (A dot B) = ?u v. (w = u ++ v) /\ u IN A /\ v IN B`,
 RW_TAC basic_ss [dot_def]);

val DOT_EMPTYSET = Q.store_thm
("DOT_EMPTYSET",
`!A. (A dot {} = {}) /\ ({} dot A = {})`,
 RW_TAC basic_ss [dot_def,EXTENSION]);

val DOT_EMPTYSTRING = Q.store_thm
("DOT_EMPTYSTRING",
`!A. (A dot {[]} = A) /\ ({[]} dot A = A)`,
 RW_TAC basic_ss [dot_def,EXTENSION]);

val STRCAT_IN_dot = Q.store_thm
("STRCAT_IN_dot",
`!a b A B. a IN A /\ b IN B ==> (a ++ b) IN (A dot B)`,
 METIS_TAC[IN_dot]);

val EMPTY_IN_DOT = Q.store_thm
("EMPTY_IN_DOT",
`!A B. [] IN (A dot B) = [] IN A /\ [] IN B`,
 METIS_TAC [IN_dot,APPEND_EQNS]);

val DOT_ASSOC = Q.store_thm
("DOT_ASSOC",
`!A B C. A dot (B dot C) = (A dot B) dot C`,
 RW_TAC basic_ss [EXTENSION,IN_dot] THEN METIS_TAC [APPEND_ASSOC]);

val DOT_UNION_LDISTRIB = Q.store_thm
("DOT_UNION_LDISTRIB",
`!A B C. A dot (B UNION C) = (A dot B) UNION (A dot C)`,
 RW_TAC basic_ss [EXTENSION,IN_dot] THEN METIS_TAC []);

val DOT_UNION_RDISTRIB = Q.store_thm
("DOT_UNION_RDISTRIB",
`!A B C. (A UNION B) dot C = (A dot C) UNION (B dot C)`,
 RW_TAC basic_ss [EXTENSION,IN_dot] THEN METIS_TAC []);

val DOT_MONO = Q.store_thm
("DOT_MONO",
`!A B C D. A SUBSET C /\ B SUBSET D ==> (A dot B) SUBSET (C dot D)`,
 RW_TAC basic_ss [SUBSET_DEF,IN_dot] THEN METIS_TAC []);

(*---------------------------------------------------------------------------*)
(* Iterated language concatenation.                                          *)
(*---------------------------------------------------------------------------*)

val DOTn_def =
  Define
    `(DOTn A 0 = {[]}) /\
     (DOTn A (SUC n) = A dot (DOTn A n))`;

val DOTn_RIGHT = Q.store_thm
("DOTn_RIGHT",
`!n A. A dot DOTn A n = DOTn A n dot A`,
 Induct THEN RW_TAC basic_ss [DOTn_def] THENL
 [RW_TAC basic_ss [EXTENSION,IN_dot],
  METIS_TAC [DOT_ASSOC]]);

val SUBSET_DOTn = Q.store_thm
("SUBSET_DOTn",
`!A. A SUBSET DOTn A (SUC 0)`,
 RW_TAC basic_ss [SUBSET_DEF,DOTn_def,IN_dot]);

val EMPTY_IN_DOTn_ZERO = Q.store_thm
("EMPTY_IN_DOTn_ZERO",
`!x A. x IN DOTn A 0 = (x = [])`,
 RW_TAC basic_ss [DOTn_def]);

val STRCAT_IN_DOTn_SUC = Q.store_thm
("STRCAT_IN_DOTn_SUC",
 `!a b A n. (a IN A /\ b IN DOTn A n) \/ (a IN DOTn A n /\ b IN A)
          ==> (a ++ b) IN DOTn A (SUC n)`,
 RW_TAC basic_ss [DOTn_def] THEN METIS_TAC [STRCAT_IN_dot,DOTn_RIGHT]);

val STRCAT_IN_DOTn_ADD = Q.store_thm
("STRCAT_IN_DOTn_ADD",
`!m n a b A.
    a IN DOTn A m /\ b IN DOTn A n ==> (a ++ b) IN DOTn A (m + n)`,
 Induct THEN RW_TAC basic_ss [DOTn_def] THEN
 FULL_SIMP_TAC basic_ss [IN_dot] THEN
 `(v ++ b) IN DOTn A (m + n)` by METIS_TAC [] THEN
 METIS_TAC [STRCAT_IN_DOTn_SUC,APPEND_ASSOC,DECIDE``SUC(m+n) = n + SUC m``]);

val DOTn_EMPTYSET = Q.store_thm
("DOTn_EMPTYSET",
`!n. DOTn {} n = if n=0 then {[]} else {}`,
 Induct THEN RW_TAC basic_ss [DOTn_def,DOT_EMPTYSET]);

val DOTn_EMPTYSTRING = Q.store_thm
("DOTn_EMPTYSTRING",
`!n. DOTn {[]} n = {[]}`,
 Induct THEN RW_TAC basic_ss [DOTn_def,dot_def,EXTENSION] THEN
 METIS_TAC[APPEND_EQNS]);

val EMPTY_IN_DOTn = Q.store_thm
("EMPTY_IN_DOTn",
`!n. ([] IN DOTn A n) <=> (n=0) \/ ([] IN A)`,
 Induct THEN RW_TAC basic_ss [DOTn_def,EMPTY_IN_DOT] THEN METIS_TAC[]);

val DOTn_UNION = Q.store_thm
("DOTn_UNION",
`!n x A B. x IN DOTn A n ==> x IN DOTn (A UNION B) n`,
 Induct THEN RW_TAC basic_ss [DOTn_def,IN_dot] THEN METIS_TAC[]);

val DOTn_DIFF = Q.store_thm
("DOTn_DIFF",
`!n x A B. x IN DOTn (A DIFF B) n ==> x IN DOTn A n`,
 Induct THEN RW_TAC basic_ss [DOTn_def,IN_dot] THEN METIS_TAC[]);

(*---------------------------------------------------------------------------*)
(* This lemma can be extended so that k is as large or small as possible. It *)
(* says that a word in A^n is either empty or can be split into k non-empty  *)
(* pieces.                                                                   *)
(*---------------------------------------------------------------------------*)

val DOTn_EMPTYSTRING_FREE = Q.store_thm
("DOTn_EMPTYSTRING_FREE",
`!n A w. w IN DOTn A n ==>
     (w = []) \/
     ?k. w IN DOTn (A DELETE []) k`,
 Induct THEN RW_TAC basic_ss [DOTn_def,IN_dot] THEN
 RES_TAC THEN Cases_on `u` THEN RW_TAC basic_ss [] THEN
 `h::t IN (A DELETE [])` by RW_TAC basic_ss [] THENL
 [METIS_TAC [SUBSET_DOTn,SUBSET_DEF],
  METIS_TAC [STRCAT_IN_DOTn_SUC,APPEND_EQNS]]);

(*---------------------------------------------------------------------------*)
(* Kleene star                                                               *)
(*---------------------------------------------------------------------------*)

val KSTAR_def =
 Define
   `KSTAR(L:'a lang) = BIGUNION {DOTn L n | n IN UNIV}`;

val IN_KSTAR = Q.store_thm
("IN_KSTAR",
 `x IN KSTAR(L) = ?n. x IN DOTn L n`,
  RW_TAC basic_ss [KSTAR_def,BIGUNION] THEN
  RW_TAC basic_ss [SPECIFICATION] THEN
  METIS_TAC[]);

val KSTAR_EMPTYSET = Q.store_thm
("KSTAR_EMPTYSET",
`KSTAR {} = {[]}`,
 RW_TAC basic_ss [EXTENSION,IN_KSTAR,DOTn_EMPTYSET] THEN
 EQ_TAC THEN RW_TAC basic_ss [] THENL
 [Cases_on `n` THEN FULL_SIMP_TAC basic_ss [],
  METIS_TAC [IN_INSERT]]);

val EMPTY_IN_KSTAR = Q.store_thm
("EMPTY_IN_KSTAR",
`!A. [] IN (KSTAR A)`,
 RW_TAC basic_ss [IN_KSTAR] THEN METIS_TAC [DOTn_def,IN_INSERT]);

val KSTAR_SING = Q.store_thm
("KSTAR_SING",
`!x. x IN (KSTAR {x})`,
 RW_TAC basic_ss [IN_KSTAR] THEN
 Q.EXISTS_TAC `SUC 0` THEN
 RW_TAC basic_ss [DOTn_def,IN_dot]);

val SUBSET_KSTAR = Q.store_thm
("SUBSET_KSTAR",
`!A. A SUBSET KSTAR(A)`,
 RW_TAC basic_ss [SUBSET_DEF,IN_KSTAR] THEN
 Q.EXISTS_TAC `SUC 0` THEN
 RW_TAC basic_ss [DOTn_def,IN_dot]);

val SUBSET_KSTAR_DOT = Q.store_thm
("SUBSET_KSTAR_DOT",
`!A B. B SUBSET (KSTAR A) dot B`,
 RW_TAC basic_ss [SUBSET_DEF,IN_KSTAR,IN_dot] THEN
 MAP_EVERY Q.EXISTS_TAC [`[]`,`x`] THEN
 RW_TAC basic_ss [] THEN METIS_TAC [DOTn_def,IN_INSERT]);

val STRCAT_IN_KSTAR = Q.store_thm
("STRCAT_IN_KSTAR",
`!u v A B.
    u IN A /\ v IN KSTAR(A) dot B ==> (u ++ v) IN KSTAR(A) dot B`,
 RW_TAC list_ss [IN_KSTAR,IN_dot] THEN
 MAP_EVERY Q.EXISTS_TAC [`u++u'`,`v'`] THEN
 RW_TAC list_ss [APPEND_ASSOC] THEN
 Q.EXISTS_TAC `SUC n` THEN RW_TAC std_ss [DOTn_def] THEN
 METIS_TAC [STRCAT_IN_dot]);

val KSTAR_EQ_INTRO = Q.store_thm
("KSTAR_EQ_INTRO",
`!A B. (!n. DOTn A n = DOTn B n) ==> (KSTAR A = KSTAR B)`,
 RW_TAC basic_ss [EXTENSION,IN_KSTAR]);

val IN_KSTAR_LIST = Q.store_thm
("IN_KSTAR_LIST",
 `!s A. s IN KSTAR A <=> ?wlist. EVERY (\w. w IN A) wlist /\ (s = FLAT wlist)`,
 RW_TAC list_ss [IN_KSTAR,EQ_IMP_THM] THENL
 [POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `s`
    THEN Induct_on `n` THEN RW_TAC list_ss []
    THENL
     [FULL_SIMP_TAC list_ss [EMPTY_IN_DOTn_ZERO] THEN RW_TAC list_ss []
         THEN Q.EXISTS_TAC `[]` THEN RW_TAC list_ss [],
      FULL_SIMP_TAC list_ss [DOTn_def,IN_dot]
          THEN RW_TAC list_ss [] THEN RES_TAC
          THEN Q.EXISTS_TAC `u::wlist` THEN RW_TAC list_ss []],
  Induct_on `wlist` THEN FULL_SIMP_TAC list_ss []
    THENL [METIS_TAC [EMPTY_IN_DOTn],
           RW_TAC list_ss [] THEN RES_TAC
             THEN Q.EXISTS_TAC `SUC n`
             THEN RW_TAC list_ss [DOTn_def] THEN METIS_TAC[IN_dot]]]);

(*---------------------------------------------------------------------------*)
(* Some more complex equalities                                              *)
(*---------------------------------------------------------------------------*)

val lang_ss = basic_ss ++
               rewrites [IN_KSTAR, IN_dot, DOTn_def,
                         DOT_EMPTYSET,DOT_EMPTYSTRING, DOTn_EMPTYSTRING,
                         KSTAR_SING,KSTAR_EMPTYSET,EMPTY_IN_KSTAR];

val KSTAR_EQ_EPSILON_UNION_DOT = Q.store_thm
("KSTAR_EQ_EPSILON_UNION_DOT",
`!A. KSTAR A = {[]} UNION (A dot KSTAR A)`,
 RW_TAC lang_ss [EXTENSION,EQ_IMP_THM] THENL
  [Cases_on `n`
    THENL [METIS_TAC[EMPTY_IN_DOTn_ZERO],
           FULL_SIMP_TAC lang_ss [] THEN METIS_TAC[]],
   METIS_TAC [EMPTY_IN_DOTn_ZERO],
   METIS_TAC [STRCAT_IN_DOTn_SUC]]);

val IN_KSTAR_THM = Q.store_thm("IN_KSTAR_THM",
`!w L. w IN KSTAR L = (w = []) \/ ?w1 w2. (w = w1++w2) /\ w1 IN L /\ w2 IN KSTAR L`,
 RW_TAC list_ss [Once KSTAR_EQ_EPSILON_UNION_DOT,IN_UNION, IN_SING,IN_dot]);

val KSTAR_EQ_KSTAR_UNION = Q.store_thm
("KSTAR_EQ_KSTAR_UNION",
`!A. KSTAR A = KSTAR ({[]} UNION A)`,
 RW_TAC lang_ss [EXTENSION,EQ_IMP_THM] THENL
 [METIS_TAC [DOTn_UNION,UNION_COMM],
  POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `x` THEN
   Induct_on `n` THEN RW_TAC lang_ss [] THENL
   [METIS_TAC [EMPTY_IN_DOTn_ZERO],
    METIS_TAC [APPEND_EQNS],
    METIS_TAC [STRCAT_IN_DOTn_SUC,APPEND_EQNS]]]);

val KSTAR_DOT_KSTAR = Q.store_thm
("KSTAR_DOT_KSTAR",
`!A. (KSTAR A dot KSTAR A) = KSTAR A`,
 RW_TAC lang_ss [EXTENSION,EQ_IMP_THM] THENL
 [METIS_TAC [STRCAT_IN_DOTn_ADD],
  Cases_on `n` THEN FULL_SIMP_TAC lang_ss[] THENL
  [METIS_TAC [APPEND_eq_NIL,EMPTY_IN_DOTn_ZERO],
   METIS_TAC [SUBSET_DOTn,SUBSET_DEF]]]);

val KSTAR_KSTAR_EQ_KSTAR = Q.store_thm
("KSTAR_KSTAR_EQ_KSTAR",
`!A. KSTAR(KSTAR A) = KSTAR A`,
 RW_TAC lang_ss [EXTENSION,EQ_IMP_THM] THENL
 [POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `x` THEN
   Induct_on `n` THEN RW_TAC lang_ss [] THEN
   METIS_TAC [EMPTY_IN_DOTn_ZERO,STRCAT_IN_DOTn_ADD],
  METIS_TAC [SUBSET_KSTAR,IN_KSTAR,SUBSET_DEF]]);

val DOT_KSTAR_EQ_KSTAR_DOT = Q.store_thm
("DOT_KSTAR_EQ_KSTAR_DOT",
`!A. (A dot KSTAR A) = (KSTAR A dot A)`,
 RW_TAC lang_ss [EXTENSION,EQ_IMP_THM] THENL
 [`(u++v) IN (DOTn A n dot A)` by METIS_TAC [DOTn_RIGHT,EXTENSION,IN_dot],
  `(u++v) IN (A dot DOTn A n)` by METIS_TAC [DOTn_RIGHT,EXTENSION,IN_dot]]
 THEN METIS_TAC [IN_dot]);

val lemma = Q.prove
(`(!n. DOTn (A dot B) n dot A = A dot DOTn (B dot A) n)
   ==> (KSTAR (A dot B) dot A = A dot KSTAR(B dot A))`,
 RW_TAC lang_ss [EXTENSION] THEN METIS_TAC[]);

val KSTAR_DOT_SHIFT = Q.store_thm
("KSTAR_DOT_SHIFT",
`!A. KSTAR (A dot B) dot A = A dot KSTAR(B dot A)`,
 GEN_TAC THEN MATCH_MP_TAC lemma THEN
 Induct THEN RW_TAC lang_ss [] THEN METIS_TAC [DOT_ASSOC]);

val DOT_SQUARED_SUBSET = Q.store_thm
("DOT_SQUARED_SUBSET",
`!L. (L dot L) SUBSET L ==> (L dot KSTAR L) SUBSET L`,
 RW_TAC lang_ss [SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] THEN
 NTAC 2 (POP_ASSUM MP_TAC) THEN MAP_EVERY Q.ID_SPEC_TAC [`v`, `u`] THEN
 Induct_on `n` THEN RW_TAC lang_ss [] THEN
 METIS_TAC [DOT_ASSOC]);

val KSTAR_UNION = Q.store_thm
("KSTAR_UNION",
`!A B. KSTAR (A UNION B) = KSTAR(KSTAR A dot B) dot KSTAR A`,
 RW_TAC lang_ss [EXTENSION,EQ_IMP_THM] THENL
 [POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `x` THEN Induct_on `n` THENL
  [METIS_TAC [EMPTY_IN_DOTn_ZERO,APPEND_EQNS],
   SIMP_TAC basic_ss [DOTn_def,DOTn_RIGHT] THEN RW_TAC lang_ss [] THENL
   [`?u1 u2. (u = u1 ++ u2) /\ (?m. u1 IN DOTn (KSTAR A dot B) m) /\
             ?k. u2 IN DOTn A k` by METIS_TAC[] THEN
     METIS_TAC [APPEND_ASSOC,STRCAT_IN_DOTn_SUC],
   `?u1 u2. (u = u1 ++ u2) /\ (?m. u1 IN DOTn (KSTAR A dot B) m) /\
            ?k. u2 IN DOTn A k` by METIS_TAC[] THEN
     Q.EXISTS_TAC `u1 ++ (u2 ++ v)` THEN Q.EXISTS_TAC `[]` THEN
     RW_TAC lang_ss [APPEND_ASSOC] THENL
     [`u2 ++ v IN (KSTAR A dot B)` by (RW_TAC lang_ss [] THEN METIS_TAC[])
        THEN METIS_TAC [APPEND_ASSOC,STRCAT_IN_DOTn_SUC],
      METIS_TAC [EMPTY_IN_DOTn_ZERO]]]]
   ,
   REPEAT (POP_ASSUM MP_TAC) THEN MAP_EVERY Q.ID_SPEC_TAC [`v`, `u`, `n`]
   THEN Induct_on `n'` THEN RW_TAC lang_ss [] THENL
   [POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `u` THEN
     Induct_on`n` THEN RW_TAC lang_ss [] THENL
     [METIS_TAC [EMPTY_IN_DOTn_ZERO],
      METIS_TAC [IN_UNION,APPEND_ASSOC,STRCAT_IN_DOTn_ADD,
                 STRCAT_IN_DOTn_SUC,DOTn_UNION]],
    `u' ++ v' IN DOTn A n' dot A` by METIS_TAC [IN_dot,DOTn_RIGHT] THEN
    FULL_SIMP_TAC lang_ss [] THEN
    METIS_TAC [IN_UNION,APPEND_ASSOC,STRCAT_IN_DOTn_ADD,
               STRCAT_IN_DOTn_SUC,DOTn_UNION]]]);

(*===========================================================================*)
(* Arden's Lemma.                                                            *)
(*===========================================================================*)

val LENGTH_LESS = Q.store_thm
("LENGTH_LESS",
`!u x v. (x = u++v) /\ ~(u = []) ==> LENGTH v < LENGTH x`,
 Cases_on `u` THEN RW_TAC list_ss []);

val lemma = Q.prove
(`!A B X. (!n. (DOTn A n dot B) SUBSET X) ==> KSTAR(A) dot B SUBSET X`,
 RW_TAC basic_ss [SUBSET_DEF,IN_KSTAR,IN_dot] THEN METIS_TAC []);

(*---------------------------------------------------------------------------*)
(* Although Arden's Lemma doesn't directly mention machines, it can be used  *)
(* to map DFAs to equivalent regular languages.                              *)
(*---------------------------------------------------------------------------*)

val ARDENS_LEMMA = Q.store_thm
("ARDENS_LEMMA",
 `!A B X:'a lang.
    ~([] IN A) /\ (X = (A dot X) UNION B) ==> (X = KSTAR(A) dot B)`,
 REPEAT STRIP_TAC THEN RW_TAC basic_ss [SET_EQ_SUBSET] THENL
 [REWRITE_TAC [SUBSET_DEF] THEN GEN_TAC THEN
  measureInduct_on `LENGTH x` THEN
  Cases_on `LENGTH x` THENL
  [FULL_SIMP_TAC basic_ss [LENGTH_NIL,EMPTY_IN_DOT] THEN RW_TAC std_ss []
   THENL [METIS_TAC [EMPTY_IN_KSTAR],METIS_TAC [EMPTY_IN_DOT,IN_UNION]],
   STRIP_TAC THEN
   `x IN A dot X \/ x IN B` by METIS_TAC [IN_UNION] THENL
   [`?u v. (x = u ++ v) /\ u IN A /\ v IN X` by METIS_TAC [IN_dot] THEN
    `~(u = [])` by METIS_TAC [] THEN
    `LENGTH v < LENGTH x` by METIS_TAC [LENGTH_LESS] THEN
    `v IN KSTAR A dot B` by METIS_TAC [] THEN METIS_TAC [STRCAT_IN_KSTAR]
    ,
    METIS_TAC [SUBSET_DEF,SUBSET_KSTAR_DOT]]]
  ,
  MATCH_MP_TAC lemma THEN Induct THENL
  [RW_TAC basic_ss [DOTn_def,SUBSET_DEF,dot_def] THEN METIS_TAC [IN_UNION],
   `A dot (DOTn A n dot B) SUBSET (A dot X)`
      by METIS_TAC [DOT_MONO,SUBSET_REFL] THEN
   SIMP_TAC std_ss [DOTn_def,GSYM DOT_ASSOC] THEN
   METIS_TAC [IN_UNION,SUBSET_DEF]]]);

val _ = export_theory();
