(*---------------------------------------------------------------------------*
 * A theory about relations, taken as functions of type 'a->'a->bool.        *
 * This is not well-fleshed-out currently. We just treat transitive closure  *
 * and wellfoundedness to start. A few other notions, like inverse image,    *
 * are also defined.                                                         *
 *---------------------------------------------------------------------------*)

structure relationScript =
struct

open HolKernel Parse boolLib QLib tautLib mesonLib Rsyntax simpLib boolSimps;
infix ORELSE ORELSEC THEN THENL |->;

val _ = new_theory "relation";


val TC_DEF =
Q.new_definition
("TC_DEF",
 `TC (R:'a->'a->bool) a b =
    !P.(!x y. R x y ==> P x y) /\
       (!x y z. P x y /\ P y z ==> P x z)
       ==> P a b`);

val RTC_DEF = new_definition(
  "RTC_DEF",
  ``RTC (R : 'a -> 'a -> bool) a b =
      !P.  (!x. P x x) /\
           (!x y z. R x y /\ P y z ==> P x z) ==>
           P a b``);

val RC_DEF = new_definition(
  "RC_def",
  ``RC (R:'a->'a->bool) x y = (x = y) \/ R x y``);

val transitive_def =
Q.new_definition
("transitive_def",
   `transitive (R:'a->'a->bool) = !x y z. R x y /\ R y z ==> R x z`);

val reflexive_def = new_definition(
  "reflexive_def",
  ``reflexive (R:'a->'a->bool) = !x. R x x``);


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

val nice_tc_asm =
  ``tc = \R a b. !P. (!x y. R x y ==> P x y) /\
                     (!x y z. R x y /\ P y z ==> P x z) ==>
                     P a b``;

val tc_rules0 = prove(
  ``^nice_tc_asm ==> (!x y. R x y ==> tc R x y) /\
                     (!x y z. R x y /\ tc R y z ==> tc R x z)``,
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN BETA_TAC THEN MESON_TAC []);
val tc_rules = UNDISCH tc_rules0

val tc_ind0 = prove(
  ``^nice_tc_asm ==>
    !R P. (!x y. R x y ==> P x y) /\
          (!x y z. R x y /\ P y z ==> P x z) ==>
          (!x y. tc R x y ==> P x y)``,
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN BETA_TAC THEN MESON_TAC []);
val tc_ind = UNDISCH tc_ind0

val tc_twice0 = prove(
  ``^nice_tc_asm ==>
    !R x y. tc R x y ==> !z. tc R y z ==> tc R x z``,
  STRIP_TAC THEN GEN_TAC THEN HO_MATCH_MP_TAC tc_ind THEN
  MESON_TAC [tc_rules]);
val tc_twice = UNDISCH tc_twice0

val TC_INDUCT = Q.store_thm("TC_INDUCT",
`!(R:'a->'a->bool) P.
   (!x y. R x y ==> P x y) /\
   (!x y z. P x y /\ P y z ==> P x z)
   ==> !u v. (TC R) u v ==> P u v`,
REWRITE_TAC[TC_DEF] THEN MESON_TAC[]);

val tc_TC0 = prove(
  ``^nice_tc_asm ==> !R x y. tc R x y = TC R x y``,
  STRIP_TAC THEN GEN_TAC THEN
  SIMP_TAC bool_ss [FORALL_AND_THM, EQ_IMP_THM] THEN CONJ_TAC THENL [
    HO_MATCH_MP_TAC tc_ind THEN MESON_TAC [TC_RULES],
    HO_MATCH_MP_TAC TC_INDUCT THEN MESON_TAC [tc_twice, tc_rules]
  ]);
val tc_TC = UNDISCH tc_TC0

val tc_exists = SIMP_PROVE bool_ss [] ``?tc. ^nice_tc_asm``;

val TC_INDUCT_LEFT1_0 = REWRITE_RULE [tc_TC] tc_ind

val TC_INDUCT_LEFT1 = save_thm(
  "TC_INDUCT_LEFT1",
  CHOOSE(``tc:('a -> 'a -> bool) -> 'a -> 'a -> bool``, tc_exists)
        TC_INDUCT_LEFT1_0);

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

val TC_STRONG_INDUCT_LEFT1 = store_thm(
  "TC_STRONG_INDUCT_LEFT1",
  ``!R P. (!x y. R x y ==> P x y) /\
          (!x y z. R x y /\ P y z /\ TC R y z ==> P x z) ==>
          (!u v. TC R u v ==> P u v)``,
  REPEAT STRIP_TAC THEN IMP_RES_TAC TC_STRONG_INDUCT_LEFT1_0);

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

val RC_IDEM = store_thm(
  "RC_IDEM",
  ``!R:'a->'a->bool.  RC (RC R) = RC R``,
  GEN_TAC THEN
  CONV_TAC (Q.X_FUN_EQ_CONV `u`) THEN GEN_TAC THEN
  CONV_TAC (Q.X_FUN_EQ_CONV `v`) THEN GEN_TAC THEN
  SIMP_TAC bool_ss [RC_DEF] THEN MESON_TAC []);

val TC_IDEM = store_thm(
  "TC_IDEM",
  ``!R:'a->'a->bool.  TC (TC R) = TC R``,
  GEN_TAC THEN
  CONV_TAC (Q.X_FUN_EQ_CONV `u`) THEN GEN_TAC THEN
  CONV_TAC (Q.X_FUN_EQ_CONV `v`) THEN GEN_TAC THEN
  EQ_TAC THEN Q.ID_SPEC_TAC `v` THEN Q.ID_SPEC_TAC `u` THEN
  HO_MATCH_MP_TAC TC_INDUCT THEN MESON_TAC [TC_RULES]);

val RTC_IDEM = store_thm(
  "RTC_IDEM",
  ``!R:'a->'a->bool.  RTC (RTC R) = RTC R``,
  GEN_TAC THEN
  CONV_TAC (Q.X_FUN_EQ_CONV `u`) THEN GEN_TAC THEN
  CONV_TAC (Q.X_FUN_EQ_CONV `v`) THEN GEN_TAC THEN
  EQ_TAC THEN Q.ID_SPEC_TAC `v` THEN Q.ID_SPEC_TAC `u` THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN MESON_TAC [RTC_RULES, RTC_RTC]);

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

(*---------------------------------------------------------------------------*
 * Wellfounded relations. Applications of wellfoundedness to specific types  *
 * (numbers, lists, etc.) can be found in the respective theories.           *
 *---------------------------------------------------------------------------*)

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
 * Wellfoundedness: Every non-empty set has an R-minimal element.            *
 *---------------------------------------------------------------------------*)

val WF_DEF =
Q.new_definition
 ("WF_DEF", `WF R = !B. (?w:'a. B w) ==> ?min. B min /\ !b. R b min ==> ~B b`);


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


val INDUCTION_WF_THM = Q.prove(
`!R:'a->'a->bool.
     (!P. (!x. (!y. R y x ==> P y) ==> P x) ==> !x. P x) ==> WF R`,
GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[WF_DEF] THEN GEN_TAC THEN
 CONV_TAC CONTRAPOS_CONV THEN NNF_TAC THEN
 DISCH_THEN (fn th => POP_ASSUM (MATCH_MP_TAC o BETA_RULE o Q.SPEC`\w. ~B w`)
                      THEN ASSUME_TAC th) THEN GEN_TAC THEN
 CONV_TAC CONTRAPOS_CONV THEN NNF_TAC
 THEN POP_ASSUM MATCH_ACCEPT_TAC);


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


val ex_lem = Q.prove(
`!x. (?y. y = x) /\ ?y. x=y`,
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


val _ = export_theory();

end;
