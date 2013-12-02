(* file HS/FIN/tcScript.sml, created 1/23/13, revised 9/30, author F.L.Morris *)

(* A theory to support implementation of Warshall's algorithm for transitive *)
(* closure. Relations are represented as set-valued finite maps, but no      *)
(* particular representation is presumed for the sets or maps themselves.    *)
(* Accompanying tcTacs will offer a conversion to work with either set [...] *)
(* sets and fmap [...] fmaps, only needing an equality-decider conversion    *)
(* for elements/arguments, or (prefeably) with FMAPAL fmaps & ENUMERAL sets, *)
(* needing a conversion reducing a three-valued "toto" ordering, for which   *)
(* see totoTheory, totoTacs, and also enumeralTheory/Tacs, fmapalTheory/Tacs.*)

structure tcScript = struct

(* app load ["pred_setLib", "pred_setTheory", "relationTheory", "pairTheory",
"optionTheory", "TotalDefn", "bossLib", "finite_mapTheory", "numLib", "intLib",
"totoTheory"]; *) (* totoTheory only for definiton of type 'a reln *)

open HolKernel boolLib Parse bossLib;
val _ = set_trace "Unicode" 0;
open pred_setLib pred_setTheory relationTheory pairTheory optionTheory;
open Defn TotalDefn combinTheory PairRules;
open PairRules pairLib listTheory finite_mapTheory totoTheory;

val _ = new_theory "tc";

(* My habitual abbreviations: *)

val AR = ASM_REWRITE_TAC [];
fun ulist x = [x];
fun rrs th = REWRITE_RULE [SPECIFICATION] th;
val _ = intLib.deprecate_int (); (* because intLib gets loaded now (9/13) *)

val _ = Defn.def_suffix := ""; (* replacing default "_def" *)

(* *************************************************************** *)

val _ = set_fixity "^|" (Infixl 650);
val _ = set_fixity "|^" (Infixl 650);
val _ = set_fixity "^|^" (Infixl 650);

(* Restriction of a relation to a subset of its domain, range, or both:
^|, |^, ^|^ respectively. "RESTRICT" has been taken for mysterious purposes
by the original relationTheory, and "DRESTRICT" by finite_mapTheory.  *)

val DRESTR = xDefine "DRESTR"
`((R:'a reln) ^| (s:'a set)) a b = a IN s /\ R a b`;

val DRESTR_IN = store_thm ("DRESTR_IN",
``!R:'a reln s a. (R ^| s) a = if a IN s then R a else {}``,
REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN REWRITE_TAC [DRESTR] THEN
GEN_TAC THEN Cases_on `a IN s` THEN AR THEN
REWRITE_TAC [rrs NOT_IN_EMPTY]);

val RRESTR = xDefine "RRESTR"
`((R:'a reln) |^ (s:'a set)) a b = b IN s /\ R a b`;

(* restriction Both fore and aft *)

val BRESTR = xDefine "BRESTR" `(R:'a reln) ^|^ s = R ^| s |^ s`;

val DRESTR_EMPTY = store_thm ("DRESTR_EMPTY",
``!R:'a reln. R ^| {} = REMPTY``,
GEN_TAC THEN REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [DRESTR_IN, NOT_IN_EMPTY, EMPTY_REL_DEF] THEN
REWRITE_TAC [rrs NOT_IN_EMPTY]);

val DRESTR_RDOM = store_thm ("DRESTR_RDOM",
``!R:'a reln. R ^| (RDOM R) = R``,
GEN_TAC THEN REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [DRESTR_IN, IN_RDOM] THEN
COND_CASES_TAC THENL
[REFL_TAC
,UNDISCH_THEN ``~?y. (R:'a reln) x y``
              (REWRITE_TAC o ulist o CONV_RULE NOT_EXISTS_CONV) THEN
 REWRITE_TAC [rrs NOT_IN_EMPTY]]);

val REMPTY_RRESTR = store_thm ("REMPTY_RRESTR",
``!s. REMPTY:'a reln |^ s = REMPTY``,
GEN_TAC THEN REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [RRESTR, EMPTY_REL_DEF]);

val O_REMPTY_O = store_thm ("O_REMPTY_O",
``(!R:'a reln. R O REMPTY = REMPTY) /\
  (!R:'a reln. REMPTY O R = REMPTY)``,
CONJ_TAC THEN GEN_TAC THEN REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [EMPTY_REL_DEF, O_DEF]);

(* Define subTC, the invariant for an arrayless form of the
   Floyd-Warshall algorithm, in as low-level and symmetrical a way as
   possible, with an eye to using (R)TC induction principles. *)

val subTC = Define`subTC (R:'a reln) s x y =
  R x y \/ ?a b. (R ^|^ s)^* a b /\ a IN s /\ b IN s /\ R x a /\ R b y`;

(* Definition as first conceived becomes a theorem: *)
(* Outer ^| s is meant just to trim off (x,x) pairs for x NOTIN s, and we
   need a lemma about that: *)

val RTC_trim_lem = BETA_RULE (prove (
``!R:'a reln s y y'. (\x. x IN s) y' /\ (R ^|^ s)^* y' y ==> (\x. x IN s) y``,
REPEAT GEN_TAC THEN MATCH_MP_TAC RTC_lifts_invariants THEN BETA_TAC THEN
REWRITE_TAC [BRESTR, DRESTR, RRESTR] THEN REPEAT STRIP_TAC THEN AR));

(* RTC_trim_lem = |- !R s y y'. y' IN s /\ (R ^|^ s)^* y' y ==> y IN s *)

val subTC_thm = store_thm ("subTC_thm",
``!R:'a reln s. subTC R s = R RUNION (R O ((R ^|^ s)^* ^| s) O R)``,
REPEAT GEN_TAC THEN REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [subTC, O_DEF, RUNION, DRESTR] THEN
EQ_TAC THEN STRIP_TAC THEN AR THEN DISJ2_TAC THENL
[EXISTS_TAC ``b:'a`` THEN AR THEN
 EXISTS_TAC ``a:'a`` THEN AR
,EXISTS_TAC ``y':'a`` THEN EXISTS_TAC ``y:'a`` THEN AR THEN
 IMP_RES_TAC RTC_trim_lem]);

val subTC_EMPTY = store_thm ("subTC_EMPTY",
``!R:'a reln. subTC R {} = R``,
GEN_TAC THEN REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [subTC_thm, BRESTR, DRESTR_EMPTY, O_REMPTY_O, REMPTY_RRESTR,
             EMPTY_REL_DEF, RUNION]);

(* Dec 14 new departure: figure out what is bigger or equal (in fact equal)
   to (R ^|^ (a INSERT s))^* because that's the only way I know to use a
   transitive closure hypothesis. *)

(* seemingly needs to be proved in two stages, one with RTC_STRONG_INDUCT,
   one with RTC_STRONG_INDUCT_RIGHT1 *)

val NOT_IN_RTC_EQ = prove (
``!R:'a reln s p q. (p NOTIN s \/ q NOTIN s) /\ (R ^|^ s)^* p q ==> (p = q)``,
REPEAT GEN_TAC THEN CONV_TAC ANTE_CONJ_CONV THEN STRIP_TAC THENL
[ONCE_REWRITE_TAC [RTC_CASES1], ONCE_REWRITE_TAC [RTC_CASES2]] THEN
 CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN AR THEN
 CONV_TAC NOT_EXISTS_CONV THEN GEN_TAC THEN
 ASM_REWRITE_TAC [BRESTR, DRESTR, RRESTR]);

val RTC_INSERT_MONO = prove (
``!R:'a reln s a w z. (R ^|^ s)^* w z ==> (R ^|^ (a INSERT s))^* w z``,
REPEAT GEN_TAC THEN MATCH_MP_TAC RTC_MONOTONE THEN
REPEAT GEN_TAC THEN REWRITE_TAC [BRESTR, DRESTR, RRESTR, IN_INSERT] THEN
STRIP_TAC THEN AR);

val RTC_INSERT_RIGHT_IMP = prove (
``!R:'a reln s a w z. (R ^|^ (a INSERT s))^* w z ==>
(R ^|^ s)^* w z \/ ((a = z) \/ ?y. y IN s /\ R a y /\ (R ^|^ s)^* y z)``,
REPEAT GEN_TAC THEN
Cases_on `a IN s`
THEN1 (IMP_RES_THEN SUBST1_TAC ABSORPTION_RWT THEN
       DISCH_THEN (REWRITE_TAC o ulist)) THEN
SUBGOAL_THEN ``(R:'a reln ^|^ s)^* w z \/
                  ((a = z) \/ ?y. y IN s /\ R a y /\ (R ^|^ s)^* y z) =
         (\w z. (R ^|^ s)^* w z \/
                  ((a = z) \/ ?y. y IN s /\ R a y /\ (R ^|^ s)^* y z)) w z``
SUBST1_TAC THEN1 (BETA_TAC THEN REFL_TAC) THEN
MATCH_MP_TAC RTC_STRONG_INDUCT THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
ASM_REWRITE_TAC [RTC_REFL] THENL
 [Cases_on `x = a` THENL
  [DISJ2_TAC THEN Cases_on `y IN s` THENL
   [DISJ2_TAC THEN EXISTS_TAC ``y:'a`` THEN AR THEN
    Q.UNDISCH_TAC `(R ^|^ (a INSERT s)) x y` THEN
    ASM_REWRITE_TAC [BRESTR, DRESTR, RRESTR] THEN STRIP_TAC THEN AR
   ,DISJ1_TAC THEN Q.SUBGOAL_THEN `z = y` ASSUME_TAC THENL
    [IMP_RES_TAC NOT_IN_RTC_EQ THEN Cases_on `a = y` THEN AR
    ,Cases_on `a = y` THEN1 AR THEN
     Q.SUBGOAL_THEN `x = y` (ASM_REWRITE_TAC o ulist o SYM) THEN
     Q.SUBGOAL_THEN `y NOTIN a INSERT s` ASSUME_TAC
     THEN1 (ASM_REWRITE_TAC [IN_INSERT] THEN
            Q.UNDISCH_THEN `a <> y` (ACCEPT_TAC o GSYM)) THEN
     MATCH_MP_TAC (Q.SPECL [`R`, `a INSERT s`] NOT_IN_RTC_EQ) THEN
     CONJ_TAC THENL [AR, IMP_RES_TAC RTC_SINGLE]
   ]]
  ,Cases_on `y = a` THENL
   [DISJ2_TAC THEN
    DISJ1_TAC THEN Q.SUBGOAL_THEN `y = z` (ASM_REWRITE_TAC o ulist o SYM) THEN
    MATCH_MP_TAC NOT_IN_RTC_EQ THEN
    Q.EXISTS_TAC `R` THEN Q.EXISTS_TAC `s` THEN AR
   ,DISJ1_TAC THEN
    ONCE_REWRITE_TAC [RTC_CASES1] THEN DISJ2_TAC THEN Q.EXISTS_TAC `y` THEN
    AR THEN Q.UNDISCH_TAC `(R ^|^ (a INSERT s)) x y` THEN
    ASM_REWRITE_TAC [BRESTR, DRESTR, RRESTR, IN_INSERT]
   ]]
  ,DISJ2_TAC THEN DISJ2_TAC THEN Q.EXISTS_TAC `y'` THEN AR
 ]);

val RTC_INSERT_LEFT_IMP = prove (
``!R:'a reln s a w z. (R ^|^ (a INSERT s))^* w z ==>
   (R ^|^ s)^* w z \/ ((a = w) \/ ?x. x IN s /\ (R ^|^ s)^* w x /\ R x a)``,
REPEAT GEN_TAC THEN
Cases_on `a IN s`
THEN1 (IMP_RES_THEN SUBST1_TAC ABSORPTION_RWT THEN
       DISCH_THEN (REWRITE_TAC o ulist)) THEN
SUBGOAL_THEN ``(R:'a reln ^|^ s)^* w z \/
                  ((a = w) \/ ?x. x IN s /\ (R ^|^ s)^* w x /\ R x a) =
         (\w z. (R ^|^ s)^* w z \/
                  ((a = w) \/ ?x. x IN s /\ (R ^|^ s)^* w x /\ R x a)) w z``
SUBST1_TAC THEN1 (BETA_TAC THEN REFL_TAC) THEN
MATCH_MP_TAC RTC_STRONG_INDUCT_RIGHT1 THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
ASM_REWRITE_TAC [RTC_REFL] THENL
 [Cases_on `z = a` THENL
  [DISJ2_TAC THEN Cases_on `y IN s` THENL
   [DISJ2_TAC THEN EXISTS_TAC ``y:'a`` THEN AR THEN
    Q.UNDISCH_TAC `(R ^|^ (a INSERT s)) y z` THEN
    ASM_REWRITE_TAC [BRESTR, DRESTR, RRESTR] THEN STRIP_TAC THEN AR
   ,DISJ1_TAC THEN Q.SUBGOAL_THEN `x = y` ASSUME_TAC THENL
    [IMP_RES_TAC NOT_IN_RTC_EQ THEN Cases_on `a = y` THEN AR
    ,Cases_on `a = y` THEN1 AR THEN
     Q.SUBGOAL_THEN `y = z` (ASM_REWRITE_TAC o ulist) THEN
     Q.SUBGOAL_THEN `y NOTIN a INSERT s` ASSUME_TAC
     THEN1 (ASM_REWRITE_TAC [IN_INSERT] THEN
            Q.UNDISCH_THEN `a <> y` (ACCEPT_TAC o GSYM)) THEN
     MATCH_MP_TAC (Q.SPECL [`R`, `a INSERT s`] NOT_IN_RTC_EQ) THEN
     CONJ_TAC THENL [AR, IMP_RES_TAC RTC_SINGLE]
   ]]
  ,Cases_on `y = a` THENL
   [DISJ2_TAC THEN
    DISJ1_TAC THEN Q.SUBGOAL_THEN `x = y` (ASM_REWRITE_TAC o ulist) THEN
    MATCH_MP_TAC NOT_IN_RTC_EQ THEN
    Q.EXISTS_TAC `R` THEN Q.EXISTS_TAC `s` THEN AR
   ,DISJ1_TAC THEN
    ONCE_REWRITE_TAC [RTC_CASES2] THEN DISJ2_TAC THEN Q.EXISTS_TAC `y` THEN
    AR THEN Q.UNDISCH_TAC `(R ^|^ (a INSERT s)) y z` THEN
    ASM_REWRITE_TAC [BRESTR, DRESTR, RRESTR, IN_INSERT]
   ]]
  ,DISJ2_TAC THEN DISJ2_TAC THEN Q.EXISTS_TAC `x'` THEN AR
 ]);

val RTC_INSERT = store_thm ("RTC_INSERT",
``!R:'a reln s a w z. (R ^|^ (a INSERT s))^* w z <=>
(R ^|^ s)^* w z \/ ((a = w) \/ ?x. x IN s /\ (R ^|^ s)^* w x /\ R x a) /\
                   ((a = z) \/ ?y. y IN s /\ R a y /\ (R ^|^ s)^* y z)``,
REPEAT GEN_TAC THEN EQ_TAC THENL
[DISCH_TAC THEN CONV_TAC (REWR_CONV LEFT_OR_OVER_AND) THEN CONJ_TAC THENL
 [MATCH_MP_TAC RTC_INSERT_LEFT_IMP THEN AR
 ,MATCH_MP_TAC RTC_INSERT_RIGHT_IMP THEN AR
 ]
,STRIP_TAC THENL
 [IMP_RES_TAC RTC_INSERT_MONO THEN AR
 ,Q.UNDISCH_THEN `a = z` (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
  Q.UNDISCH_THEN `a = w`
            (CONV_TAC o RATOR_CONV o RAND_CONV o REWR_CONV o SYM) THEN
  REWRITE_TAC [BRESTR, RRESTR, DRESTR, IN_INSERT, RTC_REFL]
 ,ONCE_REWRITE_TAC [RTC_CASES1] THEN
  DISJ2_TAC THEN Q.EXISTS_TAC `y` THEN CONJ_TAC THENL
  [Q.UNDISCH_THEN `a = w` (SUBST1_TAC o SYM) THEN
   ASM_REWRITE_TAC [BRESTR, RRESTR, DRESTR, IN_INSERT]
  ,IMP_RES_TAC RTC_INSERT_MONO THEN AR
  ]
 ,Q.UNDISCH_THEN `a = z` (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
  ONCE_REWRITE_TAC [RTC_CASES2] THEN
  DISJ2_TAC THEN Q.EXISTS_TAC `x` THEN CONJ_TAC THENL
  [IMP_RES_TAC RTC_INSERT_MONO THEN AR
  ,ASM_REWRITE_TAC [BRESTR, RRESTR, DRESTR, IN_INSERT]
  ]
 ,MATCH_MP_TAC (REWRITE_RULE [transitive_def] (Q.SPEC `R` RTC_TRANSITIVE)) THEN
  Q.EXISTS_TAC `a` THEN CONJ_TAC THENL
  [ONCE_REWRITE_TAC [RTC_CASES2] THEN
   DISJ2_TAC THEN Q.EXISTS_TAC `x` THEN CONJ_TAC THENL
   [IMP_RES_TAC RTC_INSERT_MONO THEN AR
   ,ASM_REWRITE_TAC [BRESTR, RRESTR, DRESTR, IN_INSERT]
   ]
  ,ONCE_REWRITE_TAC [RTC_CASES1] THEN
   DISJ2_TAC THEN Q.EXISTS_TAC `y` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC [BRESTR, RRESTR, DRESTR, IN_INSERT]
   ,IMP_RES_TAC RTC_INSERT_MONO THEN AR
]]]]);

val NOT_EQ_RTC_IN = prove (
``!R:'a reln s p q. p <> q \/ q <> p ==> (R ^|^ s)^* p q ==> p IN s /\ q IN s``,
REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN
REWRITE_TAC [DE_MORGAN_THM, NOT_IMP] THEN REPEAT STRIP_TAC THENL
[ALL_TAC, CONV_TAC (REWR_CONV EQ_SYM_EQ),
 ALL_TAC, CONV_TAC (REWR_CONV EQ_SYM_EQ)] THEN
MATCH_MP_TAC (Q.SPECL [`R`, `s`] NOT_IN_RTC_EQ) THEN AR);

val RTC_IN_LR = prove (
``(!R:'a reln s p q. p IN s /\ (R ^|^ s)^* p q ==> q IN s)``,
REPEAT STRIP_TAC THEN
Cases_on `q IN s` THEN1 AR THEN
IMP_RES_TAC NOT_IN_RTC_EQ THEN
Q.UNDISCH_THEN `p = q` (SUBST1_TAC o SYM) THEN AR);

val RTC_IN_RL = prove (
``(!R:'a reln s p q. q IN s /\ (R ^|^ s)^* p q ==> p IN s)``,
REPEAT STRIP_TAC THEN
Cases_on `p IN s` THEN1 AR THEN
IMP_RES_TAC NOT_IN_RTC_EQ THEN
Q.UNDISCH_THEN `p = q` SUBST1_TAC THEN AR);

val RTC_subTC1 = prove (
``!R:'a reln s a w x. R w x /\ (R ^|^ (a INSERT s))^* x a ==>
                      subTC R s w a``,
REPEAT GEN_TAC THEN REWRITE_TAC [subTC, RTC_INSERT] THEN STRIP_TAC THENL
[Cases_on `a = x` THEN1 AR THEN
 DISJ2_TAC THEN IMP_RES_TAC RTC_CASES2
 THEN1 (Q.UNDISCH_TAC `a <> x` THEN AR) THEN
 IMP_RES_TAC NOT_EQ_RTC_IN THEN
 IMP_RES_TAC RTC_IN_LR THEN
 Q.EXISTS_TAC `x` THEN Q.EXISTS_TAC `u` THEN
 Q.UNDISCH_TAC `(R ^|^ s) u a` THEN
 ASM_REWRITE_TAC [BRESTR, DRESTR, RRESTR]
,AR
,DISJ2_TAC THEN Q.EXISTS_TAC `x` THEN Q.EXISTS_TAC `x'` THEN
 IMP_RES_TAC RTC_IN_RL THEN AR
]);

val RTC_subTC2 = prove (
``!R:'a reln s a y z. (R ^|^ (a INSERT s))^* a y /\ R y z ==>
                      subTC R s a z``,
REPEAT GEN_TAC THEN REWRITE_TAC [subTC, RTC_INSERT] THEN STRIP_TAC THENL
[Cases_on `a = y` THEN1 AR THEN
 DISJ2_TAC THEN IMP_RES_TAC RTC_CASES1 THEN
 IMP_RES_TAC NOT_EQ_RTC_IN THEN
 IMP_RES_TAC RTC_IN_RL THEN
 Q.EXISTS_TAC `u` THEN Q.EXISTS_TAC `y` THEN
 Q.UNDISCH_TAC `(R ^|^ s) a u` THEN
 ASM_REWRITE_TAC [BRESTR, DRESTR, RRESTR]
,AR
,DISJ2_TAC THEN Q.EXISTS_TAC `y'` THEN Q.EXISTS_TAC `y` THEN
 IMP_RES_TAC RTC_IN_LR THEN AR
]);

(* The big lemma: what enlarging s by one does to subTC R x *)

val subTC_INSERT = store_thm ("subTC_INSERT",
``!R:'a reln s q x y. subTC R (q INSERT s) x y <=>
   subTC R s x y \/ subTC R s x q /\ subTC R s q y``,
REPEAT GEN_TAC THEN EQ_TAC THENL
[CONV_TAC (LAND_CONV (REWRITE_CONV [subTC])) THEN
 REWRITE_TAC [DISJ_IMP_THM] THEN CONJ_TAC THENL
 [DISCH_TAC THEN ASM_REWRITE_TAC [subTC]
 ,REPEAT (CONV_TAC LEFT_IMP_EXISTS_CONV THEN GEN_TAC) THEN
  Cases_on `q IN s`
  THEN1 (IMP_RES_THEN SUBST1_TAC ABSORPTION_RWT THEN
         STRIP_TAC THEN DISJ1_TAC THEN REWRITE_TAC [subTC] THEN
         DISJ2_TAC THEN Q.EXISTS_TAC `a` THEN Q.EXISTS_TAC `b` THEN AR) THEN
  STRIP_TAC THEN
  Cases_on `a = q` THENL
  [DISJ2_TAC THEN CONJ_TAC THENL
   [Q.UNDISCH_THEN `a = q` (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [subTC]
   ,MATCH_MP_TAC RTC_subTC2 THEN Q.EXISTS_TAC `b` THEN AR THEN
    Q.UNDISCH_THEN `a = q`
    (CONV_TAC o RATOR_CONV o RAND_CONV o REWR_CONV o SYM) THEN AR
   ]
  ,Q.SUBGOAL_THEN `a IN s` ASSUME_TAC THEN1 IMP_RES_TAC IN_INSERT THEN
   Cases_on `b = q` THENL
   [DISJ2_TAC THEN CONJ_TAC THENL
    [MATCH_MP_TAC RTC_subTC1 THEN Q.EXISTS_TAC `a` THEN AR THEN
     Q.UNDISCH_THEN `b = q`
     (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN AR
    ,Q.UNDISCH_THEN `b = q` (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC [subTC]
    ]
   ,Q.SUBGOAL_THEN `b IN s` ASSUME_TAC THEN1 IMP_RES_TAC IN_INSERT THEN
    Cases_on `(R ^|^ s)^* a b`
    THEN1 (DISJ1_TAC THEN ASM_REWRITE_TAC [subTC] THEN DISJ2_TAC THEN
           Q.EXISTS_TAC `a` THEN Q.EXISTS_TAC `b` THEN AR) THEN
    Q.UNDISCH_TAC `(R ^|^ (q INSERT s))^* a b` THEN
    REWRITE_TAC [RTC_INSERT] THEN
    STRIP_TAC THENL
    [Q.UNDISCH_TAC `a <> q` THEN Q.UNDISCH_THEN `q = a` (REWRITE_TAC o ulist)
    ,Q.UNDISCH_TAC `a <> q` THEN AR
    ,Q.UNDISCH_TAC `b <> q` THEN AR
    ,DISJ2_TAC THEN CONJ_TAC THEN ASM_REWRITE_TAC [subTC] THEN DISJ2_TAC THENL
     [Q.EXISTS_TAC `a` THEN Q.EXISTS_TAC `x'` THEN AR
     ,Q.EXISTS_TAC `y'` THEN Q.EXISTS_TAC `b` THEN AR
 ]]]]]
,REWRITE_TAC [DISJ_IMP_THM] THEN REWRITE_TAC [subTC] THEN CONJ_TAC THENL
 [STRIP_TAC THEN1 AR THEN DISJ2_TAC THEN
  Q.EXISTS_TAC `a` THEN Q.EXISTS_TAC `b` THEN
  IMP_RES_TAC RTC_INSERT_MONO THEN ASM_REWRITE_TAC [IN_INSERT]
 ,STRIP_TAC THEN DISJ2_TAC THENL
  [Q.EXISTS_TAC `q` THEN Q.EXISTS_TAC `q` THEN
   ASM_REWRITE_TAC [IN_INSERT, RTC_REFL]
  ,Q.EXISTS_TAC `q` THEN Q.EXISTS_TAC `b` THEN ASM_REWRITE_TAC [IN_INSERT] THEN
   ONCE_REWRITE_TAC [RTC_CASES1] THEN DISJ2_TAC THEN
   Q.EXISTS_TAC `a` THEN IMP_RES_TAC RTC_INSERT_MONO THEN
   ASM_REWRITE_TAC [BRESTR, DRESTR, RRESTR, IN_INSERT]
  ,Q.EXISTS_TAC `a` THEN Q.EXISTS_TAC `q` THEN ASM_REWRITE_TAC [IN_INSERT] THEN
   ONCE_REWRITE_TAC [RTC_CASES2] THEN DISJ2_TAC THEN
   Q.EXISTS_TAC `b` THEN IMP_RES_TAC RTC_INSERT_MONO THEN
   ASM_REWRITE_TAC [BRESTR, DRESTR, RRESTR, IN_INSERT]
  ,Q.EXISTS_TAC `a` THEN Q.EXISTS_TAC `b'` THEN ASM_REWRITE_TAC [IN_INSERT] THEN
   MATCH_MP_TAC (REWRITE_RULE [transitive_def] RTC_TRANSITIVE) THEN
   Q.EXISTS_TAC `q` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC [RTC_CASES2] THEN DISJ2_TAC THEN
    Q.EXISTS_TAC `b` THEN IMP_RES_TAC RTC_INSERT_MONO THEN
    ASM_REWRITE_TAC [BRESTR, DRESTR, RRESTR, IN_INSERT]
   ,ONCE_REWRITE_TAC [RTC_CASES1] THEN DISJ2_TAC THEN
    Q.EXISTS_TAC `a'` THEN IMP_RES_TAC RTC_INSERT_MONO THEN
    ASM_REWRITE_TAC [BRESTR, DRESTR, RRESTR, IN_INSERT]
]]]]);

val subTC_RDOM = store_thm ("subTC_RDOM",
``!R:'a reln. subTC R (RDOM R) = R^+``,
GEN_TAC THEN REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN EQ_TAC THENL
[REWRITE_TAC [subTC, DISJ_IMP_THM] THEN
 CONJ_TAC THEN1 MATCH_ACCEPT_TAC TC_SUBSET THEN
 STRIP_TAC THEN
 MATCH_MP_TAC EXTEND_RTC_TC THEN Q.EXISTS_TAC `a` THEN AR THEN
 ONCE_REWRITE_TAC [RTC_CASES2] THEN DISJ2_TAC THEN Q.EXISTS_TAC `b` THEN
 AR THEN Q.UNDISCH_TAC `(R ^|^ RDOM R)^* a b` THEN
 MATCH_MP_TAC RTC_MONOTONE THEN
 REWRITE_TAC [BRESTR, DRESTR, RRESTR] THEN REPEAT STRIP_TAC THEN AR
,MATCH_MP_TAC TC_INDUCT THEN REWRITE_TAC [subTC] THEN
 REPEAT STRIP_TAC 
 THEN1 AR THEN DISJ2_TAC THENL
 [Q.EXISTS_TAC `y` THEN Q.EXISTS_TAC `y` THEN
  ASM_REWRITE_TAC [RTC_REFL, IN_RDOM] THEN Q.EXISTS_TAC `z` THEN AR
 ,Q.EXISTS_TAC `y` THEN Q.EXISTS_TAC `b` THEN
  ASM_REWRITE_TAC [IN_RDOM] THEN CONJ_TAC THENL
  [ONCE_REWRITE_TAC [RTC_CASES1] THEN DISJ2_TAC THEN Q.EXISTS_TAC `a` THEN
   ASM_REWRITE_TAC [DRESTR, BRESTR, RRESTR, IN_RDOM]
  ,ALL_TAC
  ] THEN Q.EXISTS_TAC `a` THEN AR
 ,Q.EXISTS_TAC `a` THEN Q.EXISTS_TAC `y` THEN
  ASM_REWRITE_TAC [IN_RDOM] THEN CONJ_TAC THENL
  [ONCE_REWRITE_TAC [RTC_CASES2] THEN DISJ2_TAC THEN Q.EXISTS_TAC `b` THEN
   ASM_REWRITE_TAC [DRESTR, BRESTR, RRESTR, IN_RDOM]
  ,ALL_TAC
  ] THEN Q.EXISTS_TAC `z` THEN AR
 ,Q.EXISTS_TAC `a` THEN Q.EXISTS_TAC `b'` THEN
  ASM_REWRITE_TAC [IN_RDOM] THEN
  MATCH_MP_TAC (REWRITE_RULE [transitive_def] RTC_TRANSITIVE) THEN
  Q.EXISTS_TAC `y` THEN CONJ_TAC THENL
  [ONCE_REWRITE_TAC [RTC_CASES2] THEN DISJ2_TAC THEN Q.EXISTS_TAC `b` THEN
   ASM_REWRITE_TAC [DRESTR, BRESTR, RRESTR, IN_RDOM] THEN
   Q.EXISTS_TAC `a'` THEN AR
  ,ONCE_REWRITE_TAC [RTC_CASES1] THEN DISJ2_TAC THEN Q.EXISTS_TAC `a'` THEN
   ASM_REWRITE_TAC [DRESTR, BRESTR, RRESTR, IN_RDOM] THEN
   Q.EXISTS_TAC `a'` THEN AR
]]]);

(* following corollary suggests how we want to compute. *)

val subTC_INSERT_COR = store_thm ("subTC_INSERT_COR",
``!R:'a reln s x a. subTC R (x INSERT s) a =
   if x IN subTC R s a then subTC R s a UNION subTC R s x else subTC R s a``,
REPEAT GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
REWRITE_TAC [SPECIFICATION, subTC_INSERT, COND_RATOR, rrs IN_UNION] THEN
tautLib.TAUT_TAC);

val RDOM_EMPTY = prove (
``!R:'a reln. (RDOM R = {}) ==> (R = REMPTY) /\ (!s. subTC R s = REMPTY)``,
GEN_TAC THEN CONV_TAC (LAND_CONV FUN_EQ_CONV) THEN
REWRITE_TAC [RDOM_DEF, rrs NOT_IN_EMPTY] THEN
CONV_TAC (ONCE_DEPTH_CONV NOT_EXISTS_CONV) THEN STRIP_TAC THEN
CONJ_TAC THEN REPEAT GEN_TAC THEN
REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
ASM_REWRITE_TAC [subTC, EMPTY_REL_DEF]);

(* *************************************************************** *)
(* Define the mapping by which set-valued finite maps represent    *)
(* binary relations of finite RDOM, and a one-sided inverse.       *)
(* *************************************************************** *)

val FMAP_TO_RELN = Define
`FMAP_TO_RELN (f:'a |-> 'a set) x = if x IN FDOM f then f ' x else {}`;

val RELN_TO_FMAP = Define`RELN_TO_FMAP (R:'a reln) = FUN_FMAP R (RDOM R)`;

val RDOM_SUBSET_FDOM = store_thm ("RDOM_SUBSET_FDOM",
``!f:'a |-> 'a set. RDOM (FMAP_TO_RELN f) SUBSET FDOM f``,
GEN_TAC THEN
REWRITE_TAC [SUBSET_DEF, IN_RDOM, FMAP_TO_RELN] THEN
Cases_on `x IN FDOM f` THEN ASM_REWRITE_TAC [rrs NOT_IN_EMPTY]);

val FINITE_RDOM = store_thm ("FINITE_RDOM",
``!f:'a |-> 'a set. FINITE (RDOM (FMAP_TO_RELN f))``,
GEN_TAC THEN MP_TAC (SPEC_ALL RDOM_SUBSET_FDOM) THEN
MATCH_MP_TAC SUBSET_FINITE THEN MATCH_ACCEPT_TAC FDOM_FINITE);

val FDOM_RDOM = store_thm ("FDOM_RDOM",
``!R:'a reln. FINITE (RDOM R) ==> (FDOM (RELN_TO_FMAP R) = RDOM R)``,
REPEAT STRIP_TAC THEN
IMP_RES_TAC (INST_TYPE [beta |-> ``:'a set``] FUN_FMAP_DEF) THEN
ASM_REWRITE_TAC [RELN_TO_FMAP]);

val RELN_TO_FMAP_TO_RELN_ID = store_thm ("RELN_TO_FMAP_TO_RELN_ID",
``!R:'a reln. FINITE (RDOM R) ==> (FMAP_TO_RELN (RELN_TO_FMAP R) = R)``,
REPEAT STRIP_TAC THEN IMP_RES_TAC FDOM_RDOM THEN
CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
REWRITE_TAC [FMAP_TO_RELN] THEN
COND_CASES_TAC THENL
[REWRITE_TAC [RELN_TO_FMAP] THEN
 IMP_RES_TAC (INST_TYPE [beta |-> ``:'a set``] FUN_FMAP_DEF) THEN
 Q.UNDISCH_TAC `x IN FDOM (RELN_TO_FMAP R)` THEN AR THEN DISCH_TAC THEN
 RES_TAC THEN AR
,CONV_TAC (REWR_CONV EQ_SYM_EQ) THEN
 Q.UNDISCH_TAC `x NOTIN FDOM (RELN_TO_FMAP R)` THEN
 ASM_REWRITE_TAC [IN_RDOM, GSYM SUBSET_EMPTY, SUBSET_DEF, NOT_IN_EMPTY,
             IN_RDOM] THEN
 REWRITE_TAC [SPECIFICATION] THEN
 CONV_TAC (LAND_CONV NOT_EXISTS_CONV) THEN REWRITE_TAC []]);

(* *** Now we may start to think about a conversion (actually two combined
  under one name, one relying on pred_set.UNION_CONV and linear lists, the
  other, which shoud be a somewhat nippier performer, making use of
  an ENERMERAL-valued FMAPAL, but both following Warshall's algorithm
  as closely as their data structures will permit) for TC.
  Decided here not to call it "Floyd-Warshall algorithm", as Floyd's
  addition was specifically for computing shortest paths from real
  matrices represented edge-weighted graphs, rather than just transitive
  closure of a relation, which Warshall had covered. Most likely, using
  fmaps to real instead of finite sets, we could imitate
  Floyd if there were any demand for it. *** *)

val RDOM_subTC = store_thm ("RDOM_subTC",
``!R:'a reln s. RDOM (subTC R s) = RDOM R``,
REPEAT GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
REWRITE_TAC [RDOM_DEF, subTC] THEN EQ_TAC THEN STRIP_TAC THENL
[Q.EXISTS_TAC `y` THEN AR
,Q.EXISTS_TAC `a` THEN AR
,Q.EXISTS_TAC `y` THEN AR]);

val NOT_IN_RDOM = store_thm ("NOT_IN_RDOM",
``!Q:'a reln x. (Q x = {}) <=> x NOTIN RDOM Q``,
REPEAT GEN_TAC THEN REWRITE_TAC [RDOM_DEF, SPECIFICATION] THEN
CONV_TAC (LAND_CONV FUN_EQ_CONV) THEN REWRITE_TAC [rrs NOT_IN_EMPTY] THEN
CONV_TAC (LAND_CONV FORALL_NOT_CONV) THEN AR);

(* Break out the function to be used by TC_ITER  *)

val TC_MOD = Define
`TC_MOD (x:'a) (rx:'a set) (ra:'a set) = if x IN ra then ra UNION rx else ra`;

val TC_MOD_EMPTY_ID = store_thm ("TC_MOD_EMPTY_ID",
``!x:'a ra:'a set. TC_MOD x {} = I``,
REPEAT GEN_TAC THEN CONV_TAC FUN_EQ_CONV THEN RW_TAC (srw_ss ()) [TC_MOD]);

val I_o_f  = store_thm ("I_o_f", ``!f:'a |-> 'b. I o_f f = f``,
RW_TAC (srw_ss ()) [fmap_EXT]);

val subTC_MAX_RDOM = store_thm ("subTC_MAX_RDOM",
``!R:'a reln s x. x NOTIN RDOM R ==> (subTC R (x INSERT s) = subTC R s)``,
REPEAT STRIP_TAC THEN REPEAT (CONV_TAC FUN_EQ_CONV THEN GEN_TAC) THEN
REWRITE_TAC [subTC_INSERT] THEN
`x NOTIN RDOM (subTC R s)` by METIS_TAC [RDOM_subTC] THEN
METIS_TAC [RDOM_DEF, SPECIFICATION]);

val subTC_SUPERSET_RDOM = store_thm ("subTC_SUPERSET_RDOM",
``!R:'a reln s. FINITE s ==>  (subTC R (RDOM R UNION s) = subTC R (RDOM R))``,
GEN_TAC THEN CONV_TAC (TOP_DEPTH_CONV FUN_EQ_CONV) THEN
HO_MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
[REWRITE_TAC [UNION_EMPTY]
,REPEAT STRIP_TAC THEN
 `RDOM R UNION (e INSERT s) = (e INSERT RDOM R) UNION s`
 by (RW_TAC (srw_ss ()) [EXTENSION, IN_UNION, IN_INSERT, DISJ_ASSOC] THEN
     CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV DISJ_COMM))) THEN REFL_TAC) THEN
 AR THEN Cases_on `e IN RDOM R` THENL
 [IMP_RES_THEN (ASM_REWRITE_TAC o ulist) ABSORPTION_RWT
 ,IMP_RES_TAC subTC_MAX_RDOM THEN ASM_REWRITE_TAC [INSERT_UNION]
]]);

val subTC_FDOM = store_thm ("subTC_FDOM", ``!g R:'a reln.
(subTC R (RDOM R) = FMAP_TO_RELN g) ==> (subTC R (FDOM g) = subTC R (RDOM R))``,
REPEAT STRIP_TAC THEN
Q.SUBGOAL_THEN `RDOM R SUBSET FDOM g` 
(SUBST1_TAC o GSYM o REWRITE_RULE [SUBSET_UNION_ABSORPTION]) THENL
[Q.SUBGOAL_THEN `RDOM (subTC R (RDOM R)) = RDOM R` (SUBST1_TAC o SYM)
 THEN1 MATCH_ACCEPT_TAC RDOM_subTC THEN
 ASM_REWRITE_TAC [RDOM_SUBSET_FDOM] 
,MATCH_MP_TAC subTC_SUPERSET_RDOM THEN MATCH_ACCEPT_TAC FDOM_FINITE
]);

val SUBSET_FDOM_LEM = store_thm ("SUBSET_FDOM_LEM",
``!R:'a reln s f. (subTC R s = FMAP_TO_RELN f) ==> RDOM R SUBSET FDOM f``,
REPEAT STRIP_TAC THEN
Q.SUBGOAL_THEN `RDOM R = RDOM (subTC R s)` SUBST1_TAC
THEN1 MATCH_ACCEPT_TAC (GSYM RDOM_subTC) THEN AR THEN
MATCH_ACCEPT_TAC RDOM_SUBSET_FDOM);

(* Following is what seems needed: and now it needs a name. *)

val subTC_FDOM_RDOM = store_thm ("subTC_FDOM_RDOM",
``!R:'a reln f. (subTC R (FDOM f) = FMAP_TO_RELN f) ==>
                (subTC R (RDOM R) = FMAP_TO_RELN f)``,
REPEAT STRIP_TAC THEN
Q.SUBGOAL_THEN `subTC R (FDOM f) = subTC R (RDOM R)`
(ASM_REWRITE_TAC o ulist o SYM) THEN
Q.SUBGOAL_THEN `FDOM f = RDOM R UNION FDOM f`
(fn eq => SUBST1_TAC eq THEN MATCH_MP_TAC subTC_SUPERSET_RDOM THEN
 MATCH_ACCEPT_TAC FDOM_FINITE) THEN
Q.SUBGOAL_THEN `RDOM R SUBSET FDOM f` MP_TAC
THEN1 (MATCH_MP_TAC SUBSET_FDOM_LEM THEN Q.EXISTS_TAC `FDOM f` THEN AR) THEN
RW_TAC bool_ss [SUBSET_DEF, IN_UNION, EXTENSION] THEN METIS_TAC []
);

(* We will use fmapalTheory.o_f_bt_map to compute the o_f in the following
   lemma, but proving the lemma is another story. *)

val TC_MOD_LEM = store_thm ("TC_MOD_LEM",
``!R:'a reln s x f. x IN FDOM f /\ (subTC R s = FMAP_TO_RELN f) ==>
  (subTC R (x INSERT s) = FMAP_TO_RELN (TC_MOD x (f ' x) o_f f))``,
REPEAT STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
ASM_REWRITE_TAC [FMAP_TO_RELN, GSYM o_f_FDOM, subTC_INSERT_COR] THEN
Cases_on `x' IN FDOM f` THEN
ASM_REWRITE_TAC [EXTENSION] THENL
[IMP_RES_THEN (REWRITE_TAC o ulist)
  (REWRITE_RULE [GSYM o_f_FDOM] (Q.SPEC `TC_MOD x (f ' x)`
    (INST_TYPE [beta |-> ``:'a set``, gamma |-> ``:'a set``] o_f_DEF))) THEN
 GEN_TAC THEN CONV_TAC (RAND_CONV (REWR_CONV SPECIFICATION)) THEN
 RW_TAC bool_ss [TC_MOD, SPECIFICATION, UNION_EMPTY]
,RW_TAC (srw_ss ()) []
]);

(* Define the recursion over RDOM R *)

val TC_ITER = Define
`(TC_ITER [] (r:'a|->'a set) = r) /\
 (TC_ITER (x :: d) r = TC_ITER d (TC_MOD x (r ' x) o_f r))`;

val TC_ITER_THM = store_thm ("TC_ITER_THM",
``!R:'a reln d f s. (s UNION set d = FDOM f) /\
                    (subTC R s = FMAP_TO_RELN f) ==>
                    (TC R = FMAP_TO_RELN (TC_ITER d f))``,
GEN_TAC THEN Induct THENL
[REPEAT GEN_TAC THEN REWRITE_TAC [LIST_TO_SET_THM, UNION_EMPTY] THEN
 CONV_TAC ANTE_CONJ_CONV THEN DISCH_THEN SUBST1_TAC THEN
 DISCH_THEN (MP_TAC o MATCH_MP subTC_FDOM_RDOM) THEN
 REWRITE_TAC [TC_ITER, subTC_RDOM]
,REPEAT STRIP_TAC THEN
 Q.SUBGOAL_THEN `h IN FDOM f` ASSUME_TAC THENL
 [Q.UNDISCH_THEN `s UNION set (h::d) = FDOM f` (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [IN_UNION, IN_LIST_TO_SET, MEM]
 ,Q.SUBGOAL_THEN `(h INSERT s) UNION set d = FDOM f` ASSUME_TAC THENL
  [Q.UNDISCH_THEN `s UNION set (h::d) = FDOM f` (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [LIST_TO_SET_THM, INSERT_UNION_EQ] THEN
   CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV UNION_COMM)) THEN
   REWRITE_TAC [INSERT_UNION_EQ]
  ,IMP_RES_TAC TC_MOD_LEM THEN
   `(h INSERT s) UNION set d = FDOM (TC_MOD h (f ' h) o_f f)` by
   ASM_REWRITE_TAC [FDOM_o_f] THEN
   RES_TAC THEN ASM_REWRITE_TAC [TC_ITER]
]]]);
(* ********* not used?
val TC_COMPUTE = Define
`TC_COMPUTE (f:'a|->'a set) = TC_ITER (SET_TO_LIST (FDOM f)) f`;

val TC_COMPUTE_THM = store_thm ("TC_COMPUTE_THM",
``!f:'a|->'a set. FMAP_TO_RELN (TC_COMPUTE f) = (FMAP_TO_RELN f)^+``,
RW_TAC bool_ss [TC_COMPUTE] THEN
MATCH_MP_TAC (GSYM TC_ITER_THM) THEN Q.EXISTS_TAC `{}` THEN
SUBST1_TAC (MATCH_MP SET_TO_LIST_INV (ISPEC ``f:'a|->'a set`` FDOM_FINITE)) THEN
REWRITE_TAC [UNION_EMPTY, subTC_EMPTY]);

(* might could write the conversion now? *)
*********** *)

val _ = export_theory ();
val _ = print_theory "-";

end; (* struct *)

