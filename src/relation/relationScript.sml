(*---------------------------------------------------------------------------*
 * A theory about relations, taken as functions of type 'a->'a->bool.        *
 * We treat various kinds of closure (reflexive, transitive, r&t)            *
 * and wellfoundedness to start. A few other notions, like inverse image,    *
 * are also defined.                                                         *
 *---------------------------------------------------------------------------*)

structure relationScript =
struct

open HolKernel Parse boolLib QLib tautLib mesonLib Rsyntax simpLib boolSimps;

local open combinTheory in end;

val _ = new_theory "relation";

(*---------------------------------------------------------------------------*)
(* Closures                                                                  *)
(*---------------------------------------------------------------------------*)

val TC_DEF = Q.new_definition
  ("TC_DEF",
   `TC (R:'a->'a->bool) a b =
     !P.(!x y. R x y ==> P x y) /\
        (!x y z. P x y /\ P y z ==> P x z)  ==> P a b`);

val RTC_DEF = new_definition(
  "RTC_DEF",
  ``RTC (R : 'a -> 'a -> bool) a b =
      !P.  (!x. P x x) /\
           (!x y z. R x y /\ P y z ==> P x z) ==>
           P a b``);

val RC_DEF = new_definition(
  "RC_DEF",
  ``RC (R:'a->'a->bool) x y = (x = y) \/ R x y``);

val SC_DEF = new_definition(
  "SC_DEF",
  ``SC (R:'a->'a->bool) x y = R x y \/ R y x``);

val EQC_DEF = new_definition(
  "EQC_DEF",
  ``EQC (R:'a->'a->bool) = RC (TC (SC R))``);

(* corresponding properties of relations *)
val transitive_def =
Q.new_definition
("transitive_def",
   `transitive (R:'a->'a->bool) = !x y z. R x y /\ R y z ==> R x z`);

val reflexive_def = new_definition(
  "reflexive_def",
  ``reflexive (R:'a->'a->bool) = !x. R x x``);

val symmetric_def = new_definition(
  "symmetric_def",
  ``symmetric (R:'a->'a->bool) = !x y. R x y = R y x``);

val equivalence_def = new_definition(
  "equivalence_def",
  ``equivalence (R:'a->'a->bool) = reflexive R /\ symmetric R /\
                                   transitive R``);

val SC_SYMMETRIC = store_thm(
  "SC_SYMMETRIC",
  ``!R. symmetric (SC R)``,
  REWRITE_TAC [symmetric_def, SC_DEF] THEN MESON_TAC []);

val TC_TRANSITIVE = Q.store_thm("TC_TRANSITIVE",
 `!R:'a->'a->bool. transitive(TC R)`,
REWRITE_TAC[transitive_def,TC_DEF]
 THEN REPEAT STRIP_TAC
 THEN RES_TAC THEN ASM_MESON_TAC[]);

val RTC_INDUCT = store_thm(
  "RTC_INDUCT",
  ``!R P. (!x. P x x) /\ (!x y z. R x y /\ P y z ==> P x z) ==>
          (!x (y:'a). RTC R x y ==> P x y)``,
  REWRITE_TAC [RTC_DEF] THEN MESON_TAC []);

val TC_RULES = store_thm(
  "TC_RULES",
  ``!R. (!x (y:'a). R x y ==> TC R x y) /\
        (!x y z. TC R x y /\ TC R y z ==> TC R x z)``,
  REWRITE_TAC [TC_DEF] THEN REPEAT STRIP_TAC THENL [
    ASM_MESON_TAC [],
    FIRST_ASSUM MATCH_MP_TAC THEN RES_TAC THEN ASM_MESON_TAC []
  ]);

val RTC_RULES = store_thm(
  "RTC_RULES",
  ``!R. (!x. RTC R (x:'a) x) /\ (!x y z. R x y /\ RTC R y z ==> RTC R x z)``,
  REWRITE_TAC [RTC_DEF] THEN MESON_TAC []);

val RTC_STRONG_INDUCT = store_thm(
  "RTC_STRONG_INDUCT",
  ``!R P. (!x. P x x) /\ (!x y z. R x y /\ RTC R y z /\ P y z ==> P x z) ==>
          (!x (y:'a). RTC R x y ==> P x y)``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ((CONV_RULE (SIMP_CONV bool_ss [RTC_RULES]) o
                 Q.SPECL [`R`, `\u v. RTC R u v /\ P u v`]) RTC_INDUCT) THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC [RTC_RULES]);

val RTC_RTC = store_thm(
  "RTC_RTC",
  ``!R (x:'a) y. RTC R x y ==> !z. RTC R y z ==> RTC R x z``,
  GEN_TAC THEN HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN MESON_TAC [RTC_RULES]);

val RTC_TRANSITIVE = store_thm(
  "RTC_TRANSITIVE",
  ``!R:'a->'a->bool. transitive (RTC R)``,
  REWRITE_TAC [transitive_def] THEN MESON_TAC [RTC_RTC]);

val RTC_REFLEXIVE = store_thm(
  "RTC_REFLEXIVE",
  ``!R:'a->'a->bool. reflexive (RTC R)``,
  MESON_TAC [reflexive_def, RTC_RULES]);

val RC_REFLEXIVE = store_thm(
  "RC_REFLEXIVE",
  ``!R:'a->'a->bool. reflexive (RC R)``,
  MESON_TAC [reflexive_def, RC_DEF]);

val symmetric_RC = store_thm(
  "symmetric_RC",
  ``!R. symmetric (RC R) = symmetric R``,
  REWRITE_TAC [symmetric_def, RC_DEF] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_MESON_TAC []);



val TC_SUBSET = Q.store_thm("TC_SUBSET",
`!R x (y:'a). R x y ==> TC R x y`,
REWRITE_TAC[TC_DEF] THEN MESON_TAC[]);

val RTC_SUBSET = store_thm(
  "RTC_SUBSET",
  ``!R (x:'a) y. R x y ==> RTC R x y``,
  MESON_TAC [RTC_RULES]);

val RC_SUBSET = store_thm(
  "RC_SUBSET",
  ``!R (x:'a) y. R x y ==> RC R x y``,
  MESON_TAC [RC_DEF]);

val RC_RTC = store_thm(
  "RC_RTC",
  ``!R (x:'a) y. RC R x y ==> RTC R x y``,
  MESON_TAC [RC_DEF, RTC_RULES]);

val tc = ``tc : ('a -> 'a -> bool) -> ('a -> 'a -> bool)``
val tc_left_asm =
  ``tc = \R a b. !P. (!x y. R x y ==> P x y) /\
                     (!x y z. R x y /\ P y z ==> P x z) ==>
                     P a b``;
val tc_right_asm =
  ``tc = \R a b. !P. (!x y. R x y ==> P x y) /\
                     (!x y z. P x y /\ R y z ==> P x z) ==>
                     P a b``;

val tc_left_rules0 = prove(
  ``^tc_left_asm ==> (!x y. R x y ==> tc R x y) /\
                     (!x y z. R x y /\ tc R y z ==> tc R x z)``,
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN BETA_TAC THEN MESON_TAC []);
val tc_left_rules = UNDISCH tc_left_rules0

val tc_right_rules = UNDISCH (prove(
  ``^tc_right_asm ==> (!x y. R x y ==> tc R x y) /\
                      (!x y z. tc R x y /\ R y z ==> tc R x z)``,
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN BETA_TAC THEN MESON_TAC []));

val tc_left_ind = TAC_PROOF(
  ([tc_left_asm],
   ``!R P. (!x y. R x y ==> P x y) /\
           (!x y z. R x y /\ P y z ==> P x z) ==>
           (!x y. tc R x y ==> P x y)``),
  ASM_REWRITE_TAC [] THEN BETA_TAC THEN MESON_TAC []);

val tc_right_ind = TAC_PROOF(
  ([tc_right_asm],
   ``!R P. (!x y. R x y ==> P x y) /\
           (!x y z. P x y /\ R y z ==> P x z) ==>
           (!x y. tc R x y ==> P x y)``),
  ASM_REWRITE_TAC [] THEN BETA_TAC THEN MESON_TAC []);

val tc_left_twice = TAC_PROOF(
  ([tc_left_asm],
   ``!R x y. ^tc R x y ==> !z. tc R y z ==> tc R x z``),
  GEN_TAC THEN
  HO_MATCH_MP_TAC tc_left_ind THEN MESON_TAC [tc_left_rules]);
val tc_right_twice = TAC_PROOF(
  ([tc_right_asm],
   ``!R x y. ^tc R x y ==> !z. tc R z x ==> tc R z y``),
  GEN_TAC THEN HO_MATCH_MP_TAC tc_right_ind THEN MESON_TAC [tc_right_rules]);


val TC_INDUCT = Q.store_thm("TC_INDUCT",
`!(R:'a->'a->bool) P.
   (!x y. R x y ==> P x y) /\
   (!x y z. P x y /\ P y z ==> P x z)
   ==> !u v. (TC R) u v ==> P u v`,
REWRITE_TAC[TC_DEF] THEN MESON_TAC[]);

val tc_left_TC = TAC_PROOF(
  ([tc_left_asm],
   ``!R x y. tc R x y = TC R x y``),
  GEN_TAC THEN
  SIMP_TAC bool_ss [FORALL_AND_THM, EQ_IMP_THM] THEN CONJ_TAC THENL [
    HO_MATCH_MP_TAC tc_left_ind THEN MESON_TAC [TC_RULES],
    HO_MATCH_MP_TAC TC_INDUCT THEN MESON_TAC [tc_left_twice, tc_left_rules]
  ]);
val tc_right_TC = TAC_PROOF(
  ([tc_right_asm],
   ``!R x y. tc R x y = TC R x y``),
  GEN_TAC THEN
  SIMP_TAC bool_ss [FORALL_AND_THM, EQ_IMP_THM] THEN CONJ_TAC THENL [
    HO_MATCH_MP_TAC tc_right_ind THEN MESON_TAC [TC_RULES],
    HO_MATCH_MP_TAC TC_INDUCT THEN MESON_TAC [tc_right_twice, tc_right_rules]
  ]);

val tc_left_exists = SIMP_PROVE bool_ss [] ``?tc. ^tc_left_asm``;
val tc_right_exists = SIMP_PROVE bool_ss [] ``?tc. ^tc_right_asm``;

val TC_INDUCT_LEFT1 = save_thm(
  "TC_INDUCT_LEFT1",
  CHOOSE(tc, tc_left_exists) (REWRITE_RULE [tc_left_TC] tc_left_ind));
val TC_INDUCT_RIGHT1 = save_thm(
  "TC_INDUCT_RIGHT1",
  CHOOSE(tc, tc_right_exists) (REWRITE_RULE [tc_right_TC] tc_right_ind));

val TC_INDUCT_TAC =
 let val tc_thm = TC_INDUCT
     fun tac (asl,w) =
      let val {Bvar=u,Body} = dest_forall w
          val {Bvar=v,Body} = dest_forall Body
          val {ant,conseq} = dest_imp Body
          val (TC,[R,u',v']) = strip_comb ant
          val {Name = "TC",...} = dest_const TC
          val _ = assert (aconv u) u'
          val _ = assert (aconv v) v'
          val P = list_mk_abs([u,v], conseq)
          val tc_thm' = BETA_RULE(ISPEC P (ISPEC R tc_thm))
      in MATCH_MP_TAC tc_thm' (asl,w)
      end
      handle _ => raise HOL_ERR{origin_structure = "<top-level>",
                     origin_function = "TC_INDUCT_TAC",
                     message = "Unanticipated term structure"}
 in tac
 end;

val TC_STRONG_INDUCT0 = prove(
  ``!R P. (!x y. R x y ==> P x y) /\
          (!x y z. P x y /\ P y z /\ TC R x y /\ TC R y z ==> P x z) ==>
          (!u v. TC R u v ==> P u v /\ TC R u v)``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN TC_INDUCT_TAC THEN
  ASM_MESON_TAC [TC_RULES]);

val TC_STRONG_INDUCT = store_thm(
  "TC_STRONG_INDUCT",
  ``!R P. (!x y. R x y ==> P x y) /\
          (!x y z. P x y /\ P y z /\ TC R x y /\ TC R y z ==> P x z) ==>
          (!u v. TC R u v ==> P u v)``,
  REPEAT STRIP_TAC THEN IMP_RES_TAC TC_STRONG_INDUCT0);

val TC_STRONG_INDUCT_LEFT1_0 = prove(
  ``!R P. (!x y. R x y ==> P x y) /\
          (!x y z. R x y /\ P y z /\ TC R y z ==> P x z) ==>
          (!u v. TC R u v ==> P u v /\ TC R u v)``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN HO_MATCH_MP_TAC TC_INDUCT_LEFT1 THEN
  ASM_MESON_TAC [TC_RULES]);
val TC_STRONG_INDUCT_RIGHT1_0 = prove(
  ``!R P. (!x y. R x y ==> P x y) /\
          (!x y z. P x y /\ TC R x y /\ R y z ==> P x z) ==>
          (!u v. TC R u v ==> P u v /\ TC R u v)``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN HO_MATCH_MP_TAC TC_INDUCT_RIGHT1 THEN
  ASM_MESON_TAC [TC_RULES]);

val TC_STRONG_INDUCT_LEFT1 = store_thm(
  "TC_STRONG_INDUCT_LEFT1",
  ``!R P. (!x y. R x y ==> P x y) /\
          (!x y z. R x y /\ P y z /\ TC R y z ==> P x z) ==>
          (!u v. TC R u v ==> P u v)``,
  REPEAT STRIP_TAC THEN IMP_RES_TAC TC_STRONG_INDUCT_LEFT1_0);
val TC_STRONG_INDUCT_RIGHT1 = store_thm(
  "TC_STRONG_INDUCT_RIGHT1",
  ``!R P. (!x y. R x y ==> P x y) /\
          (!x y z. P x y /\ TC R x y /\ R y z ==> P x z) ==>
          (!u v. TC R u v ==> P u v)``,
  REPEAT STRIP_TAC THEN IMP_RES_TAC TC_STRONG_INDUCT_RIGHT1_0);

val TC_RTC = store_thm(
  "TC_RTC",
  ``!R (x:'a) y. TC R x y ==> RTC R x y``,
  GEN_TAC THEN TC_INDUCT_TAC THEN MESON_TAC [RTC_RULES, RTC_RTC]);

val RTC_TC_RC = store_thm(
  "RTC_TC_RC",
  ``!R (x:'a) y. RTC R x y ==> RC R x y \/ TC R x y``,
  GEN_TAC THEN HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
  REPEAT STRIP_TAC THENL [
    REWRITE_TAC [RC_DEF],
    FULL_SIMP_TAC bool_ss [RC_DEF] THEN ASM_MESON_TAC [TC_RULES],
    ASM_MESON_TAC [TC_RULES]
  ]);

val TC_RC_EQNS = store_thm(
  "TC_RC_EQNS",
  ``!R:'a->'a->bool. (RC (TC R) = RTC R) /\ (TC (RC R) = RTC R)``,
  REPEAT STRIP_TAC THEN
  CONV_TAC (Q.X_FUN_EQ_CONV `u`) THEN GEN_TAC THEN
  CONV_TAC (Q.X_FUN_EQ_CONV `v`) THEN GEN_TAC THEN
  EQ_TAC THENL [
    REWRITE_TAC [RC_DEF] THEN MESON_TAC [TC_RTC, RTC_RULES],
    Q.ID_SPEC_TAC `v` THEN Q.ID_SPEC_TAC `u` THEN
    HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN
    SIMP_TAC bool_ss [RC_DEF] THEN MESON_TAC [TC_RULES],
    Q.ID_SPEC_TAC `v` THEN Q.ID_SPEC_TAC `u` THEN
    HO_MATCH_MP_TAC TC_INDUCT THEN MESON_TAC [RC_RTC, RTC_RTC],
    Q.ID_SPEC_TAC `v` THEN Q.ID_SPEC_TAC `u` THEN
    HO_MATCH_MP_TAC RTC_INDUCT THEN MESON_TAC [TC_RULES, RC_DEF]
  ]);

val RTC_INDUCT_RIGHT1 = store_thm(
  "RTC_INDUCT_RIGHT1",
  ``!R P. (!x. P x x) /\
          (!x y z. P x y /\ R y z ==> P x z) ==>
          (!x y. RTC R x y ==> P x y)``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q.SUBGOAL_THEN `!x y. RTC R x y = RC (TC R) x y`
    (fn th => ASM_REWRITE_TAC [th])
  THENL[
    REWRITE_TAC [TC_RC_EQNS],
    ALL_TAC
  ] THEN ASM_SIMP_TAC bool_ss [RC_DEF, DISJ_IMP_THM, FORALL_AND_THM] THEN
  HO_MATCH_MP_TAC TC_INDUCT_RIGHT1 THEN ASM_MESON_TAC []);

val RTC_RULES_RIGHT1 = store_thm(
  "RTC_RULES_RIGHT1",
  ``!R. (!x. RTC R x x) /\ (!x y z. RTC R x y /\ R y z ==> RTC R x z)``,
  SIMP_TAC bool_ss [RTC_RULES] THEN GEN_TAC THEN
  Q_TAC SUFF_TAC
        `!x y. RTC R x y ==> !z. R y z ==> RTC R x z`
        THEN1 MESON_TAC [] THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN MESON_TAC [RTC_RULES]);

val RTC_STRONG_INDUCT_RIGHT1 = store_thm(
  "RTC_STRONG_INDUCT_RIGHT1",
  ``!R P. (!x. P x x) /\
          (!x y z. P x y /\ RTC R x y /\ R y z ==> P x z) ==>
          (!x y. RTC R x y ==> P x y)``,
  REPEAT STRIP_TAC THEN
  Q_TAC SUFF_TAC `P x y /\ RTC R x y` THEN1 MESON_TAC [] THEN
  Q.UNDISCH_THEN `RTC R x y` MP_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`y`, `x`] THEN
  HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
  ASM_MESON_TAC [RTC_RULES_RIGHT1]);


val EXTEND_RTC_TC = store_thm(
  "EXTEND_RTC_TC",
  ``!R x y z. R x y /\ RTC R y z ==> TC R x z``,
  GEN_TAC THEN
  Q_TAC SUFF_TAC `!y z. RTC R y z ==> !x. R x y ==> TC R x z` THEN1
        MESON_TAC [] THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN
  MESON_TAC [TC_RULES]);

val reflexive_RC_identity = store_thm(
  "reflexive_RC_identity",
  ``!R. reflexive R ==> (RC R = R)``,
  SIMP_TAC bool_ss [reflexive_def, RC_DEF, FUN_EQ_THM] THEN MESON_TAC []);

val symmetric_SC_identity = store_thm(
  "symmetric_SC_identity",
  ``!R. symmetric R ==> (SC R = R)``,
  SIMP_TAC bool_ss [symmetric_def, SC_DEF, FUN_EQ_THM]);

val transitive_TC_identity = store_thm(
  "transitive_TC_identity",
  ``!R. transitive R ==> (TC R = R)``,
  SIMP_TAC bool_ss [transitive_def, FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM,
                    TC_RULES] THEN GEN_TAC THEN STRIP_TAC THEN
  HO_MATCH_MP_TAC TC_INDUCT THEN ASM_MESON_TAC []);

val RC_IDEM = store_thm(
  "RC_IDEM",
  ``!R:'a->'a->bool.  RC (RC R) = RC R``,
  SIMP_TAC bool_ss [RC_REFLEXIVE, reflexive_RC_identity]);

val SC_IDEM = store_thm(
  "SC_IDEM",
  ``!R:'a->'a->bool. SC (SC R) = SC R``,
  SIMP_TAC bool_ss [SC_SYMMETRIC, symmetric_SC_identity]);

val TC_IDEM = store_thm(
  "TC_IDEM",
  ``!R:'a->'a->bool.  TC (TC R) = TC R``,
  SIMP_TAC bool_ss [TC_TRANSITIVE, transitive_TC_identity]);

val RC_MOVES_OUT = store_thm(
  "RC_MOVES_OUT",
  ``!R. (SC (RC R) = RC (SC R)) /\ (RC (RC R) = RC R) /\
        (TC (RC R) = RC (TC R))``,
  REWRITE_TAC [TC_RC_EQNS, RC_IDEM] THEN
  SIMP_TAC bool_ss [SC_DEF, RC_DEF, FUN_EQ_THM] THEN MESON_TAC []);

val symmetric_TC = store_thm(
  "symmetric_TC",
  ``!R. symmetric R ==> symmetric (TC R)``,
  REWRITE_TAC [symmetric_def] THEN GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC bool_ss [EQ_IMP_THM, FORALL_AND_THM] THEN CONJ_TAC THENL [
    HO_MATCH_MP_TAC TC_INDUCT,
    CONV_TAC SWAP_VARS_CONV THEN HO_MATCH_MP_TAC TC_INDUCT
  ] THEN ASM_MESON_TAC [TC_RULES]);


val EQC_EQUIVALENCE = store_thm(
  "EQC_EQUIVALENCE",
  ``!R. equivalence (EQC R)``,
  REWRITE_TAC [equivalence_def, EQC_DEF, RC_REFLEXIVE, symmetric_RC] THEN
  MESON_TAC [symmetric_TC, TC_RC_EQNS, TC_TRANSITIVE, SC_SYMMETRIC]);

val EQC_IDEM = store_thm(
  "EQC_IDEM",
  ``!R:'a->'a->bool. EQC(EQC R) = EQC R``,
  SIMP_TAC bool_ss [EQC_DEF, RC_MOVES_OUT, symmetric_SC_identity,
                    symmetric_TC, SC_SYMMETRIC, TC_IDEM]);


val RTC_IDEM = store_thm(
  "RTC_IDEM",
  ``!R:'a->'a->bool.  RTC (RTC R) = RTC R``,
  SIMP_TAC bool_ss [GSYM TC_RC_EQNS, RC_MOVES_OUT, TC_IDEM]);

val RTC_CASES1 = store_thm(
  "RTC_CASES1",
  ``!R (x:'a) y.  RTC R x y = (x = y) \/ ?u. R x u /\ RTC R u y``,
  SIMP_TAC bool_ss [EQ_IMP_THM, FORALL_AND_THM] THEN CONJ_TAC THENL [
    GEN_TAC THEN HO_MATCH_MP_TAC RTC_INDUCT THEN MESON_TAC [RTC_RULES],
    MESON_TAC [RTC_RULES]
  ]);

val RTC_CASES2 = store_thm(
  "RTC_CASES2",
  ``!R (x:'a) y.  RTC R x y = (x = y) \/ ?u. RTC R x u /\ R u y``,
  SIMP_TAC bool_ss [EQ_IMP_THM, FORALL_AND_THM] THEN CONJ_TAC THENL [
    GEN_TAC THEN HO_MATCH_MP_TAC RTC_INDUCT THEN MESON_TAC [RTC_RULES],
    MESON_TAC [RTC_RULES, RTC_SUBSET, RTC_RTC]
  ]);

val RTC_CASES_RTC_TWICE = store_thm(
  "RTC_CASES_RTC_TWICE",
  ``!R (x:'a) y. RTC R x y = ?u. RTC R x u /\ RTC R u y``,
  SIMP_TAC bool_ss [EQ_IMP_THM, FORALL_AND_THM] THEN CONJ_TAC THENL [
    GEN_TAC THEN HO_MATCH_MP_TAC RTC_INDUCT THEN MESON_TAC [RTC_RULES],
    MESON_TAC [RTC_RULES, RTC_SUBSET, RTC_RTC]
  ]);

val TC_CASES1 =
Q.store_thm
("TC_CASES1",
  `!R x z. TC R x z ==> R x z \/ ?y:'a. R x y /\ TC R y z`,
GEN_TAC
 THEN TC_INDUCT_TAC
 THEN MESON_TAC [REWRITE_RULE[transitive_def] TC_TRANSITIVE, TC_SUBSET]);

val TC_CASES2 =
Q.store_thm
("TC_CASES2",
    `!R x z. TC R x z ==> R x z \/ ?y:'a. TC R x y /\ R y z`,
GEN_TAC
 THEN TC_INDUCT_TAC
 THEN MESON_TAC [REWRITE_RULE[transitive_def] TC_TRANSITIVE, TC_SUBSET]);

val TC_MONOTONE = store_thm(
  "TC_MONOTONE",
  ``!R Q. (!x y. R x y ==> Q x y) ==> (!x y. TC R x y ==> TC Q x y)``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN TC_INDUCT_TAC THEN
  ASM_MESON_TAC [TC_RULES]);

val RTC_MONOTONE = store_thm(
  "RTC_MONOTONE",
  ``!R Q. (!x y. R x y ==> Q x y) ==> (!x y. RTC R x y ==> RTC Q x y)``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN HO_MATCH_MP_TAC RTC_INDUCT THEN
  ASM_MESON_TAC [RTC_RULES]);

val EQC_INDUCTION = store_thm(
  "EQC_INDUCTION",
  ``!R P. (!x y. R x y ==> P x y) /\
          (!x. P x x) /\
          (!x y. P x y ==> P y x) /\
          (!x y z. P x y /\ P y z ==> P x z) ==>
          (!x y. EQC R x y ==> P x y)``,
  REWRITE_TAC [EQC_DEF] THEN REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC bool_ss [RC_DEF] THEN
  Q.PAT_ASSUM `TC R x y` MP_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`y`, `x`] THEN
  HO_MATCH_MP_TAC TC_INDUCT THEN REWRITE_TAC [SC_DEF] THEN
  ASM_MESON_TAC []);

val ALT_equivalence = store_thm(
  "ALT_equivalence",
  ``!R. equivalence R = !x y. R x y = (R x = R y)``,
  REWRITE_TAC [equivalence_def, reflexive_def, symmetric_def,
               transitive_def, FUN_EQ_THM, EQ_IMP_THM] THEN
  MESON_TAC []);


(*---------------------------------------------------------------------------*
 * Wellfounded relations. Wellfoundedness: Every non-empty set has an        *
 * R-minimal element. Applications of wellfoundedness to specific types      *
 * (numbers, lists, etc.) can be found in the respective theories.           *
 *---------------------------------------------------------------------------*)

val WF_DEF =
Q.new_definition
 ("WF_DEF", `WF R = !B. (?w:'a. B w) ==> ?min. B min /\ !b. R b min ==> ~B b`);

(*---------------------------------------------------------------------------*)
(* Misc. proof tools, from pre-automation days.                              *)
(*---------------------------------------------------------------------------*)

val USE_TAC = IMP_RES_THEN(fn th => ONCE_REWRITE_TAC[th]);

val NNF_CONV =
   let val DE_MORGAN = REWRITE_CONV
                        [TAUT `~(x==>y) = (x /\ ~y)`,
                         TAUT `~x \/ y = (x ==> y)`,DE_MORGAN_THM]
       val QUANT_CONV = NOT_EXISTS_CONV ORELSEC NOT_FORALL_CONV
   in REDEPTH_CONV (QUANT_CONV ORELSEC CHANGED_CONV DE_MORGAN)
   end;

val NNF_TAC = CONV_TAC NNF_CONV;


(*---------------------------------------------------------------------------*
 *                                                                           *
 * WELL FOUNDED INDUCTION                                                    *
 *                                                                           *
 * Proof: For RAA, assume there's a z s.t. ~P z. By wellfoundedness,         *
 * there's a minimal object w s.t. ~P w. (P holds of all objects "less"      *
 * than w.) By the other assumption, i.e.,                                   *
 *                                                                           *
 *   !x. (!y. R y x ==> P y) ==> P x,                                        *
 *                                                                           *
 * P w holds, QEA.                                                           *
 *                                                                           *
 *---------------------------------------------------------------------------*)

val WF_INDUCTION_THM =
Q.store_thm("WF_INDUCTION_THM",
`!(R:'a->'a->bool).
   WF R ==> !P. (!x. (!y. R y x ==> P y) ==> P x) ==> !x. P x`,
GEN_TAC THEN REWRITE_TAC[WF_DEF]
 THEN DISCH_THEN (fn th => GEN_TAC THEN (MP_TAC (Q.SPEC `\x:'a. ~P x` th)))
 THEN BETA_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN CONV_TAC CONTRAPOS_CONV
 THEN NNF_TAC THEN STRIP_TAC THEN RES_TAC
 THEN Q.EXISTS_TAC`min` THEN ASM_REWRITE_TAC[]);


val INDUCTION_WF_THM = Q.store_thm("INDUCTION_WF_THM",
`!R:'a->'a->bool.
     (!P. (!x. (!y. R y x ==> P y) ==> P x) ==> !x. P x) ==> WF R`,
GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[WF_DEF] THEN GEN_TAC THEN
 CONV_TAC CONTRAPOS_CONV THEN NNF_TAC THEN
 DISCH_THEN (fn th => POP_ASSUM (MATCH_MP_TAC o BETA_RULE o Q.SPEC`\w. ~B w`)
                      THEN ASSUME_TAC th) THEN GEN_TAC THEN
 CONV_TAC CONTRAPOS_CONV THEN NNF_TAC
 THEN POP_ASSUM MATCH_ACCEPT_TAC);

val WF_EQ_INDUCTION_THM = Q.store_thm("WF_EQ_INDUCTION_THM",
 `!R:'a->'a->bool.
     WF R = !P. (!x. (!y. R y x ==> P y) ==> P x) ==> !x. P x`,
GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [IMP_RES_TAC WF_INDUCTION_THM, IMP_RES_TAC INDUCTION_WF_THM]);


(*---------------------------------------------------------------------------
 * A tactic for doing wellfounded induction. Lifted and adapted from
 * John Harrison's definition of WO_INDUCT_TAC in the wellordering library.
 *---------------------------------------------------------------------------*)

val _ = Parse.hide "C";

val WF_INDUCT_TAC =
 let val wf_thm0 = CONV_RULE (ONCE_DEPTH_CONV ETA_CONV)
                   (REWRITE_RULE [TAUT`A==>B==>C = A/\B==>C`]
                      (CONV_RULE (ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV)
                          WF_INDUCTION_THM))
      val [R,P] = fst(strip_forall(concl wf_thm0))
      val wf_thm1 = GENL [P,R](SPEC_ALL wf_thm0)
   fun tac (asl,w) =
    let val {Rator,Rand} = dest_comb w
        val {Name = "!",...} = dest_const Rator
        val thi = ISPEC Rand wf_thm1
        fun eqRand t = Term.compare(Rand,t) = EQUAL
        val thf = CONV_RULE(ONCE_DEPTH_CONV
                              (BETA_CONV o assert (eqRand o rator))) thi
    in MATCH_MP_TAC thf (asl,w)
    end
    handle _ => raise HOL_ERR{origin_structure = "<top-level>",
                    origin_function = "WF_INDUCT_TAC",
                    message = "Unanticipated term structure"}
 in tac
 end;


val ex_lem = Q.prove(`!x. (?y. y = x) /\ ?y. x=y`,
GEN_TAC THEN CONJ_TAC THEN Q.EXISTS_TAC`x` THEN REFL_TAC);

val WF_NOT_REFL = Q.store_thm("WF_NOT_REFL",
`!R x y. WF R ==> R x y ==> ~(x=y)`,
REWRITE_TAC[WF_DEF]
  THEN REPEAT GEN_TAC
  THEN DISCH_THEN (MP_TAC o Q.SPEC`\x. x=y`)
  THEN BETA_TAC THEN REWRITE_TAC[ex_lem]
  THEN STRIP_TAC
  THEN Q.UNDISCH_THEN `x=y` SUBST_ALL_TAC
  THEN DISCH_TAC THEN RES_TAC);


(*---------------------------------------------------------------------------
 * Some combinators for wellfounded relations.
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * The empty relation is wellfounded.
 *---------------------------------------------------------------------------*)

val EMPTY_REL_DEF =
Q.new_definition
        ("EMPTY_REL_DEF", `EMPTY_REL (x:'a) (y:'a) = F`);

val WF_Empty =
Q.store_thm
  ("WF_EMPTY_REL",
   `WF (EMPTY_REL:'a->'a->bool)`,
REWRITE_TAC[EMPTY_REL_DEF,WF_DEF]);


(*---------------------------------------------------------------------------
 * Subset: if R is a WF relation and P is a subrelation of R, then
 * P is a wellfounded relation.
 *---------------------------------------------------------------------------*)

val WF_SUBSET = Q.store_thm("WF_SUBSET",
`!(R:'a->'a->bool) P.
  WF R /\ (!x y. P x y ==> R x y) ==> WF P`,
REWRITE_TAC[WF_DEF]
 THEN REPEAT STRIP_TAC
 THEN RES_TAC
 THEN Q.EXISTS_TAC`min`
 THEN ASM_REWRITE_TAC[]
 THEN GEN_TAC
 THEN DISCH_TAC
 THEN REPEAT RES_TAC);


(*---------------------------------------------------------------------------
 * The transitive closure of a wellfounded relation is wellfounded.
 * I got the clue about the witness from Peter Johnstone's book:
 * "Notes on Logic and Set Theory". An alternative proof that Bernhard
 * Schaetz showed me uses well-founded induction then case analysis. In that
 * approach, the IH must be quantified over all sets, so that we can
 * specialize it later to an extension of B.
 *---------------------------------------------------------------------------*)

val WF_TC = Q.store_thm("WF_TC",
`!R:'a->'a->bool. WF R ==> WF(TC R)`,
GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[WF_DEF]
 THEN NNF_TAC THEN DISCH_THEN (Q.X_CHOOSE_THEN `B` MP_TAC)
 THEN DISCH_THEN (fn th =>
       Q.EXISTS_TAC`\m:'a. ?a z. B a /\ TC R a m /\ TC R m z /\ B z`
       THEN BETA_TAC THEN CONJ_TAC THEN STRIP_ASSUME_TAC th)
 THENL
 [RES_TAC THEN RES_TAC THEN MAP_EVERY Q.EXISTS_TAC[`b`,  `b'`,  `w`]
   THEN ASM_REWRITE_TAC[],
  Q.X_GEN_TAC`m` THEN STRIP_TAC THEN Q.UNDISCH_TAC`TC R (a:'a) m`
   THEN DISCH_THEN(fn th => STRIP_ASSUME_TAC
              (CONJ th (MATCH_MP TC_CASES2 th)))
   THENL
   [ Q.EXISTS_TAC`a` THEN ASM_REWRITE_TAC[] THEN RES_TAC
     THEN MAP_EVERY Q.EXISTS_TAC [`b'`, `z`] THEN ASM_REWRITE_TAC[],
     Q.EXISTS_TAC`y` THEN ASM_REWRITE_TAC[]
     THEN MAP_EVERY Q.EXISTS_TAC[`a`,`z`] THEN ASM_REWRITE_TAC[]
     THEN IMP_RES_TAC TC_SUBSET]
   THEN
   IMP_RES_TAC(REWRITE_RULE[transitive_def] TC_TRANSITIVE)]);


(*---------------------------------------------------------------------------
 * Inverse image theorem: mapping into a wellfounded relation gives a
 * derived well founded relation. A "size" mapping, like "length" for
 * lists is such a relation.
 *
 * Proof.
 * f is total and maps from one n.e. set (Alpha) into another (Beta which is
 * "\y. ?x:'a. Alpha x /\ (f x = y)"). Since the latter is n.e.
 * and has a wellfounded relation R on it, it has an R-minimal element
 * (call it "min"). There exists an x:'a s.t. f x = min. Such an x is an
 * R1-minimal element of Alpha (R1 is our derived ordering.) Why is x
 * R1-minimal in Alpha? Well, if there was a y:'a s.t. R1 y x, then f y
 * would not be in Beta (being less than f x, i.e., min). If f y wasn't in
 * Beta, then y couldn't be in Alpha.
 *---------------------------------------------------------------------------*)

val inv_image_def =
Q.new_definition
("inv_image_def",
   `inv_image R (f:'a->'b) = \x y. R (f x) (f y):bool`);


val WF_inv_image = Q.store_thm("WF_inv_image",
`!R (f:'a->'b). WF R ==> WF (inv_image R f)`,
REPEAT GEN_TAC
  THEN REWRITE_TAC[inv_image_def,WF_DEF] THEN BETA_TAC
  THEN DISCH_THEN (fn th => Q.X_GEN_TAC`Alpha` THEN STRIP_TAC THEN MP_TAC th)
  THEN Q.SUBGOAL_THEN`?w:'b. (\y. ?x:'a. Alpha x /\ (f x = y)) w` MP_TAC
  THENL
  [ BETA_TAC
     THEN MAP_EVERY Q.EXISTS_TAC[`f(w:'a)`,`w`]
     THEN ASM_REWRITE_TAC[],
    DISCH_THEN (fn th => DISCH_THEN (MP_TAC o C MATCH_MP th)) THEN BETA_TAC
     THEN NNF_TAC
     THEN REPEAT STRIP_TAC
     THEN Q.EXISTS_TAC`x`
     THEN ASM_REWRITE_TAC[]
     THEN GEN_TAC
     THEN DISCH_THEN (ANTE_RES_THEN (MP_TAC o Q.SPEC`b`))
     THEN REWRITE_TAC[]]);


(*---------------------------------------------------------------------------
 * Now the WF recursion theorem. Based on Tobias Nipkow's Isabelle development
 * of wellfounded recursion, which itself is a generalization of Mike
 * Gordon's HOL development of the primitive recursion theorem.
 *---------------------------------------------------------------------------*)

val RESTRICT_DEF =
Q.new_definition
("RESTRICT_DEF",
   `RESTRICT (f:'a->'b) R (x:'a) = \y:'a. if R y x then f y else ARB`);


(*---------------------------------------------------------------------------
 * Obvious, but crucially useful. Unary case. Handling the n-ary case might
 * be messy!
 *---------------------------------------------------------------------------*)

val RESTRICT_LEMMA = Q.store_thm("RESTRICT_LEMMA",
`!(f:'a->'b) R (y:'a) (z:'a).
    R y z ==> (RESTRICT f R z y = f y)`,
REWRITE_TAC [RESTRICT_DEF] THEN BETA_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC
THEN ASM_REWRITE_TAC[]);


(*---------------------------------------------------------------------------
 * Two restricted functions are equal just when they are equal on each
 * element of their domain.
 *---------------------------------------------------------------------------*)

val CUTS_EQ = Q.prove(
`!R f g (x:'a).
   (RESTRICT f R x = RESTRICT g R x)
    = !y:'a. R y x ==> (f y:'b = g y)`,
REPEAT GEN_TAC THEN REWRITE_TAC[RESTRICT_DEF]
 THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC THEN EQ_TAC
 THENL
 [ CONV_TAC RIGHT_IMP_FORALL_CONV THEN GEN_TAC
   THEN DISCH_THEN (MP_TAC o Q.SPEC`y`) THEN COND_CASES_TAC THEN REWRITE_TAC[],
   DISCH_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN RES_TAC
   THEN ASM_REWRITE_TAC[]]);


val EXPOSE_CUTS_TAC =
   BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC
     THEN REWRITE_TAC[CUTS_EQ]
     THEN REPEAT STRIP_TAC;


(*---------------------------------------------------------------------------
 * The set of approximations to the function being defined, restricted to
 * being R-parents of x. This has the consequence (approx_ext):
 *
 *    approx R M x f = !w. f w = ((R w x) => (M (RESTRICT f R w w) | (@v. T))
 *
 *---------------------------------------------------------------------------*)

val approx_def =
Q.new_definition
  ("approx_def",
   `approx R M x (f:'a->'b) = (f = RESTRICT (\y. M (RESTRICT f R y) y) R x)`);

(* This could, in fact, be the definition. *)
val approx_ext =
BETA_RULE(ONCE_REWRITE_RULE[RESTRICT_DEF]
    (CONV_RULE (ONCE_DEPTH_CONV (Q.X_FUN_EQ_CONV`w`)) approx_def));

val approx_SELECT0 =
  Q.GEN`g` (Q.SPEC`g`
     (BETA_RULE(Q.ISPEC `\f:'a->'b. approx R M x f` boolTheory.SELECT_AX)));

val approx_SELECT1 = CONV_RULE FORALL_IMP_CONV  approx_SELECT0;


(*---------------------------------------------------------------------------
 * Choose an approximation for R and M at x. Thus it is a
 * kind of "lookup" function, associating partial functions with arguments.
 * One can easily prove
 *  (?g. approx R M x g) ==>
 *    (!w. the_fun R M x w = ((R w x) => (M (RESTRICT (the_fun R M x) R w) w)
 *                                    |  (@v. T)))
 *---------------------------------------------------------------------------*)

val the_fun_def =
Q.new_definition
("the_fun_def",
  `the_fun R M x = @f:'a->'b. approx R M x f`);

val approx_the_fun0 = ONCE_REWRITE_RULE [GSYM the_fun_def] approx_SELECT0;
val approx_the_fun1 = ONCE_REWRITE_RULE [GSYM the_fun_def] approx_SELECT1;
val approx_the_fun2 = SUBS [Q.SPECL[`R`,`M`,`x`,`the_fun R M x`] approx_ext]
                           approx_the_fun1;

val the_fun_rw1 = Q.prove(
 `(?g:'a->'b. approx R M x g)
      ==>
  !w. R w x
       ==>
     (the_fun R M x w = M (RESTRICT (the_fun R M x) R w) w)`,
 DISCH_THEN (MP_TAC o MP approx_the_fun2) THEN
 DISCH_THEN (fn th => GEN_TAC THEN MP_TAC (SPEC_ALL th))
 THEN COND_CASES_TAC
 THEN ASM_REWRITE_TAC[]);

val the_fun_rw2 = Q.prove(
 `(?g:'a->'b. approx R M x g)  ==> !w. ~R w x ==> (the_fun R M x w = ARB)`,
DISCH_THEN (MP_TAC o MP approx_the_fun2) THEN
 DISCH_THEN (fn th => GEN_TAC THEN MP_TAC (SPEC_ALL th))
 THEN COND_CASES_TAC
 THEN ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------
 * Define a recursion operator for wellfounded relations. This takes the
 * (canonical) function obeying the recursion for all R-ancestors of x:
 *
 *    \p. R p x => the_fun (TC R) (\f v. M (f%R,v) v) x p | Arb
 *
 * as the function made available for M to use, along with x. Notice that the
 * function unrolls properly for each R-ancestor, but only gets applied
 * "parentwise", i.e., you can't apply it to any old ancestor, just to a
 * parent. This holds recursively, which is what the theorem we eventually
 * prove is all about.
 *---------------------------------------------------------------------------*)

val WFREC_DEF =
Q.new_definition
("WFREC_DEF",
  `WFREC R (M:('a->'b) -> ('a->'b)) =
     \x. M (RESTRICT (the_fun (TC R) (\f v. M (RESTRICT f R v) v) x) R x) x`);


(*---------------------------------------------------------------------------
 * Two approximations agree on their common domain.
 *---------------------------------------------------------------------------*)

val APPROX_EQUAL_BELOW = Q.prove(
`!R M f g u v.
  WF R /\ transitive R /\
  approx R M u f /\ approx R M v g
  ==> !x:'a. R x u ==> R x v
             ==> (f x:'b = g x)`,
REWRITE_TAC[approx_ext] THEN REPEAT GEN_TAC THEN STRIP_TAC
  THEN WF_INDUCT_TAC THEN Q.EXISTS_TAC`R`
  THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC
  THEN REPEAT COND_CASES_TAC THEN RES_TAC
  THEN EXPOSE_CUTS_TAC
  THEN ASM_REWRITE_TAC[]
  THEN RULE_ASSUM_TAC (REWRITE_RULE[TAUT`A==>B==>C==>D = A/\B/\C==>D`,
                                    transitive_def])
  THEN FIRST_ASSUM MATCH_MP_TAC
  THEN RES_TAC THEN ASM_REWRITE_TAC[]);

val AGREE_BELOW =
   REWRITE_RULE[TAUT`A==>B==>C==>D = B/\C/\A==>D`]
    (CONV_RULE (DEPTH_CONV RIGHT_IMP_FORALL_CONV) APPROX_EQUAL_BELOW);


(*---------------------------------------------------------------------------
 * A specialization of AGREE_BELOW
 *---------------------------------------------------------------------------*)

val RESTRICT_FUN_EQ = Q.prove(
`!R M f (g:'a->'b) u v.
     WF R /\
     transitive R   /\
     approx R M u f /\
     approx R M v g /\
     R v u
     ==> (RESTRICT f R v = g)`,
REWRITE_TAC[RESTRICT_DEF,transitive_def] THEN REPEAT STRIP_TAC
  THEN CONV_TAC (Q.X_FUN_EQ_CONV`w`) THEN BETA_TAC THEN GEN_TAC
  THEN COND_CASES_TAC (* on R w v *)
  THENL [ MATCH_MP_TAC AGREE_BELOW THEN REPEAT Q.ID_EX_TAC
            THEN RES_TAC THEN ASM_REWRITE_TAC[transitive_def],
          Q.UNDISCH_TAC`approx R M v (g:'a->'b)`
            THEN DISCH_THEN(fn th =>
                   ASM_REWRITE_TAC[REWRITE_RULE[approx_ext]th])]);


(*---------------------------------------------------------------------------
 * Every x has an approximation. This is the crucial theorem.
 *---------------------------------------------------------------------------*)

val EXISTS_LEMMA = Q.prove(
`!R M. WF R /\ transitive R ==> !x. ?f:'a->'b. approx R M x f`,
REPEAT GEN_TAC THEN STRIP_TAC
  THEN WF_INDUCT_TAC
  THEN Q.EXISTS_TAC`R` THEN ASM_REWRITE_TAC[] THEN GEN_TAC
  THEN DISCH_THEN  (* Adjust IH by applying Choice *)
    (ASSUME_TAC o Q.GEN`y` o Q.DISCH`R (y:'a) (x:'a)`
                o (fn th => REWRITE_RULE[GSYM the_fun_def] th)
                o SELECT_RULE o UNDISCH o Q.ID_SPEC)
  THEN Q.EXISTS_TAC`\p. R p x => M (the_fun R M p) p | ARB` (* witness *)
  THEN REWRITE_TAC[approx_ext] THEN BETA_TAC THEN GEN_TAC
  THEN COND_CASES_TAC
  THEN ASM_REWRITE_TAC[boolTheory.ARB_DEF]
  THEN EXPOSE_CUTS_TAC
  THEN RES_THEN (SUBST1_TAC o REWRITE_RULE[approx_def])     (* use IH *)
  THEN REWRITE_TAC[CUTS_EQ]
  THEN Q.X_GEN_TAC`v` THEN BETA_TAC THEN DISCH_TAC
  THEN RULE_ASSUM_TAC(REWRITE_RULE[transitive_def]) THEN RES_TAC
  THEN ASM_REWRITE_TAC[]
  THEN EXPOSE_CUTS_TAC
  THEN MATCH_MP_TAC RESTRICT_FUN_EQ
  THEN MAP_EVERY Q.EXISTS_TAC[`M`,`w`]
  THEN ASM_REWRITE_TAC[transitive_def]
  THEN RES_TAC);


val the_fun_unroll = Q.prove(
 `!R M x (w:'a).
     WF R /\ transitive R
       ==> R w x
        ==> (the_fun R M x w:'b = M (RESTRICT (the_fun R M x) R w) w)`,
REPEAT GEN_TAC THEN DISCH_TAC
  THEN Q.ID_SPEC_TAC`w`
  THEN MATCH_MP_TAC the_fun_rw1
  THEN MATCH_MP_TAC EXISTS_LEMMA
  THEN POP_ASSUM ACCEPT_TAC);

(*---------------------------------------------------------------------------
 * Unrolling works for any R M and x, hence it works for "TC R" and
 * "\f v. M (f % R,v) v".
 *---------------------------------------------------------------------------*)

val the_fun_TC0 =
  BETA_RULE
   (REWRITE_RULE[MATCH_MP WF_TC (Q.ASSUME`WF (R:'a->'a->bool)`),
                 TC_TRANSITIVE]
     (Q.SPECL[`TC R`,`\f v. M (RESTRICT f R v) v`,`x`] the_fun_unroll));


(*---------------------------------------------------------------------------
 * There's a rewrite rule that simplifies this mess.
 *---------------------------------------------------------------------------*)
val TC_RESTRICT_LEMMA = Q.prove(
 `!(f:'a->'b) R w. RESTRICT (RESTRICT f (TC R) w) R w = RESTRICT f R w`,
REPEAT GEN_TAC
  THEN REWRITE_TAC[RESTRICT_DEF]
  THEN CONV_TAC (Q.X_FUN_EQ_CONV`p`)
  THEN BETA_TAC THEN GEN_TAC
  THEN COND_CASES_TAC
  THENL [IMP_RES_TAC TC_SUBSET, ALL_TAC]
  THEN ASM_REWRITE_TAC[]);

val the_fun_TC = REWRITE_RULE[TC_RESTRICT_LEMMA] the_fun_TC0;


(*---------------------------------------------------------------------------
 * WFREC R M behaves as a fixpoint operator should.
 *---------------------------------------------------------------------------*)

val WFREC_THM = Q.store_thm
("WFREC_THM",
  `!R. !M:('a -> 'b) -> ('a -> 'b).
      WF R ==> !x. WFREC R M x = M (RESTRICT (WFREC R M) R x) x`,
REPEAT STRIP_TAC THEN REWRITE_TAC[WFREC_DEF]
  THEN EXPOSE_CUTS_TAC THEN BETA_TAC
  THEN IMP_RES_TAC TC_SUBSET
  THEN USE_TAC the_fun_TC
  THEN EXPOSE_CUTS_TAC
  THEN MATCH_MP_TAC AGREE_BELOW
  THEN MAP_EVERY Q.EXISTS_TAC [`TC R`, `\f v. M (RESTRICT f R v) v`, `x`, `y`]
  THEN IMP_RES_TAC WF_TC
  THEN ASSUME_TAC(SPEC_ALL TC_TRANSITIVE)
  THEN IMP_RES_TAC TC_SUBSET THEN POP_ASSUM (K ALL_TAC)
  THEN ASM_REWRITE_TAC[]
  THEN REPEAT CONJ_TAC
  THENL [ RULE_ASSUM_TAC(REWRITE_RULE[transitive_def]) THEN RES_TAC,
          ALL_TAC,ALL_TAC]
  THEN MATCH_MP_TAC approx_the_fun1
  THEN MATCH_MP_TAC EXISTS_LEMMA
  THEN ASM_REWRITE_TAC[]);


(*---------------------------------------------------------------------------*
 * This is what is used by TFL.                                              *
 *---------------------------------------------------------------------------*)

val WFREC_COROLLARY =
 Q.store_thm("WFREC_COROLLARY",
  `!M R (f:'a->'b).
        (f = WFREC R M) ==> WF R ==> !x. f x = M (RESTRICT f R x) x`,
REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[WFREC_THM]);


(*---------------------------------------------------------------------------*
 * The usual phrasing of the wellfounded recursion theorem.                  *
 *---------------------------------------------------------------------------*)

val WF_RECURSION_THM = Q.store_thm("WF_RECURSION_THM",
`!R. WF R ==> !M. ?!f:'a->'b. !x. f x = M (RESTRICT f R x) x`,
GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN CONV_TAC EXISTS_UNIQUE_CONV
THEN CONJ_TAC THENL
[Q.EXISTS_TAC`WFREC R M` THEN MATCH_MP_TAC WFREC_THM THEN POP_ASSUM ACCEPT_TAC,
 REPEAT STRIP_TAC THEN CONV_TAC (Q.X_FUN_EQ_CONV`w`) THEN WF_INDUCT_TAC
 THEN Q.EXISTS_TAC`R` THEN CONJ_TAC THENL
 [ FIRST_ASSUM ACCEPT_TAC,
   GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN
   AP_TERM_TAC THEN REWRITE_TAC[CUTS_EQ] THEN GEN_TAC THEN
   FIRST_ASSUM MATCH_ACCEPT_TAC]]);


(*---------------------------------------------------------------------------*)
(* The wellfounded part of a relation. Defined inductively.                  *)
(*---------------------------------------------------------------------------*)

val WFP_DEF = Q.new_definition
  ("WFP_DEF",
   `WFP R a = !P. (!x. (!y. R y x ==> P y) ==> P x) ==> P a`);

val WFP_RULES = Q.store_thm
   ("WFP_RULES",
    `!R x. (!y. R y x ==> WFP R y) ==> WFP R x`,
    REWRITE_TAC [WFP_DEF] THEN MESON_TAC []);

val WFP_INDUCT = Q.store_thm
   ("WFP_INDUCT",
    `!R P. (!x. (!y. R y x ==> P y) ==> P x) ==> !x. WFP R x ==> P x`,
    REWRITE_TAC [WFP_DEF] THEN MESON_TAC []);

val WFP_CASES = Q.store_thm
  ("WFP_CASES",
   `!R x. WFP R x = !y. R y x ==> WFP R y`,
   REPEAT STRIP_TAC THEN EQ_TAC
    THENL [Q.ID_SPEC_TAC `x` THEN HO_MATCH_MP_TAC WFP_INDUCT, ALL_TAC]
    THEN MESON_TAC [WFP_RULES]);

(* ------------------------------------------------------------------------- *)
(* Wellfounded part induction, strong version.                               *)
(* ------------------------------------------------------------------------- *)

val WFP_STRONG_INDUCT = Q.store_thm
  ("WFP_STRONG_INDUCT",
   `!R. (!x. WFP R x /\ (!y. R y x ==> P y) ==> P x)
          ==>
        !x. WFP R x ==> P x`,
 REPEAT GEN_TAC THEN STRIP_TAC
   THEN ONCE_REWRITE_TAC[TAUT `a ==> b = a ==> a /\ b`]
   THEN HO_MATCH_MP_TAC WFP_INDUCT THEN ASM_MESON_TAC[WFP_RULES]);


(* ------------------------------------------------------------------------- *)
(* A relation is wellfounded iff WFP is the whole universe.                  *)
(* ------------------------------------------------------------------------- *)

val WF_EQ_WFP = Q.store_thm
("WF_EQ_WFP",
 `!R. WF R = !x. WFP R x`,
 GEN_TAC THEN EQ_TAC THENL
 [REWRITE_TAC [WF_EQ_INDUCTION_THM] THEN MESON_TAC [WFP_RULES],
  DISCH_TAC THEN MATCH_MP_TAC (SPEC_ALL INDUCTION_WF_THM)
    THEN GEN_TAC THEN MP_TAC (SPEC_ALL WFP_STRONG_INDUCT)
    THEN ASM_REWRITE_TAC []]);


(* ----------------------------------------------------------------------
    inverting a relation
   ---------------------------------------------------------------------- *)

val inv_DEF = new_definition(
  "inv_DEF",
  ``inv (R:'a->'a->bool) x y = R y x``);

val inv_inv = store_thm(
  "inv_inv",
  ``!R. inv (inv R) = R``,
  SIMP_TAC bool_ss [FUN_EQ_THM, inv_DEF]);

val inv_RC = store_thm(
  "inv_RC",
  ``!R. inv (RC R) = RC (inv R)``,
  SIMP_TAC bool_ss [RC_DEF, inv_DEF, FUN_EQ_THM] THEN MESON_TAC []);

val inv_SC = store_thm(
  "inv_SC",
  ``!R. (inv (SC R) = SC R) /\ (SC (inv R) = SC R)``,
  SIMP_TAC bool_ss [inv_DEF, SC_DEF, FUN_EQ_THM] THEN MESON_TAC []);

val inv_TC = store_thm(
  "inv_TC",
  ``!R. inv (TC R) = TC (inv R)``,
  GEN_TAC THEN SIMP_TAC bool_ss [FUN_EQ_THM, inv_DEF, EQ_IMP_THM,
                                 FORALL_AND_THM] THEN
  CONJ_TAC THENL [
    CONV_TAC SWAP_VARS_CONV,
    ALL_TAC
  ] THEN HO_MATCH_MP_TAC TC_INDUCT THEN
  MESON_TAC [inv_DEF, TC_RULES]);

val inv_EQC = store_thm(
  "inv_EQC",
  ``!R. (inv (EQC R) = EQC R) /\ (EQC (inv R) = EQC R)``,
  SIMP_TAC bool_ss [EQC_DEF, inv_TC, inv_SC, inv_RC]);

val inv_MOVES_OUT = store_thm(
  "inv_MOVES_OUT",
  ``!R. (inv (inv R) = R) /\ (SC (inv R) = SC R) /\
        (RC (inv R) = inv (RC R)) /\ (TC (inv R) = inv (TC R)) /\
        (RTC (inv R) = inv (RTC R)) /\ (EQC (inv R) = EQC R)``,
  SIMP_TAC bool_ss [GSYM TC_RC_EQNS, EQC_DEF, inv_TC, inv_SC, inv_inv, inv_RC])

val reflexive_inv = store_thm(
  "reflexive_inv",
  ``!R. reflexive (inv R) = reflexive R``,
  SIMP_TAC bool_ss [inv_DEF, reflexive_def]);

val symmetric_inv = store_thm(
  "symmetric_inv",
  ``!R. symmetric (inv R) = symmetric R``,
  SIMP_TAC bool_ss [inv_DEF, symmetric_def] THEN MESON_TAC []);

val transitive_inv = store_thm(
  "transitive_inv",
  ``!R. transitive (inv R) = transitive R``,
  SIMP_TAC bool_ss [inv_DEF, transitive_def] THEN MESON_TAC []);

val symmetric_inv_identity = store_thm(
  "symmetric_inv_identity",
  ``!R. symmetric R ==> (inv R = R)``,
  SIMP_TAC bool_ss [inv_DEF, symmetric_def, FUN_EQ_THM]);

val equivalence_inv_identity = store_thm(
  "equivalence_inv_identity",
  ``!R. equivalence R ==> (inv R = R)``,
  SIMP_TAC bool_ss [equivalence_def, symmetric_inv_identity]);

val _ = export_theory();

end
