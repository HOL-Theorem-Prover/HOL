(*---------------------------------------------------------------------------*
 * A theory about relations, taken as functions of type 'a->'a->bool.        *
 * We treat various kinds of closure (reflexive, transitive, r&t)            *
 * and wellfoundedness to start. A few other notions, like inverse image,    *
 * are also defined.                                                         *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib BasicProvers;

open QLib tautLib mesonLib metisLib simpLib boolSimps combinTheory;

(* mention satTheory to work around dependency-analysis flaw in Holmake;
   satTheory is a dependency of BasicProvers, but without explicit mention
   here, Holmake will not rebuild relationTheory when satTheory changes. *)
local open satTheory in end;

val _ = new_theory "relation";

(*---------------------------------------------------------------------------*)
(* Basic properties of relations.                                            *)
(*---------------------------------------------------------------------------*)

val transitive_def =
Q.new_definition
("transitive_def",
   `transitive (R:'a->'a->bool) = !x y z. R x y /\ R y z ==> R x z`);
val _ = OpenTheoryMap.OpenTheory_const_name
          {const={Thy="relation",Name="transitive"},
           name=(["Relation"],"transitive")}

val reflexive_def = new_definition(
  "reflexive_def",
  ``reflexive (R:'a->'a->bool) = !x. R x x``);
val _ = OpenTheoryMap.OpenTheory_const_name
          {const={Thy="relation",Name="reflexive"},
           name=(["Relation"],"reflexive")}

val irreflexive_def = new_definition(
  "irreflexive_def",
  ``irreflexive (R:'a->'a->bool) = !x. ~R x x``);
val _ = OpenTheoryMap.OpenTheory_const_name
          {const={Thy="relation",Name="irreflexive"},
           name=(["Relation"],"irreflexive")}

val symmetric_def = new_definition(
  "symmetric_def",
  ``symmetric (R:'a->'a->bool) = !x y. R x y = R y x``);

val antisymmetric_def = new_definition(
  "antisymmetric_def",
  ``antisymmetric (R:'a->'a->bool) = !x y. R x y /\ R y x ==> (x = y)``);

val equivalence_def = new_definition(
  "equivalence_def",
  “equivalence (R:'a->'a->bool) <=> reflexive R /\ symmetric R /\ transitive R”
);

val total_def = new_definition(
  "total_def",
  ``total (R:'a->'a->bool) = !x y. R x y \/ R y x``);

val trichotomous = new_definition(
  "trichotomous",
  ``trichotomous (R:'a->'a->bool) = !a b. R a b \/ R b a \/ (a = b)``);

(*---------------------------------------------------------------------------*)
(* Closures                                                                  *)
(*---------------------------------------------------------------------------*)

(* The TC and RTC suffixes are tighter than function application.  This
   means that
      inv R^+
   is the inverse of the transitive closure, and you need parentheses to
   write the transitive closure of the inverse:
      (inv R)^+
*)
val TC_DEF = Q.new_definition
  ("TC_DEF",
   `TC (R:'a->'a->bool) a b =
     !P.(!x y. R x y ==> P x y) /\
        (!x y z. P x y /\ P y z ==> P x z)  ==> P a b`);
val _ = add_rule { fixity = Suffix 2100,
                   block_style = (AroundEachPhrase, (Portable.CONSISTENT,0)),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "^+"],
                   term_name = "TC" }
val _ = Unicode.unicode_version {u = Unicode.UChar.sup_plus, tmnm = "TC"}
val _ = TeX_notation {hol = Unicode.UChar.sup_plus,
                      TeX = ("\\HOLTokenSupPlus{}", 1)}
val _ = TeX_notation {hol = "^+", TeX = ("\\HOLTokenSupPlus{}", 1)}
val _ = OpenTheoryMap.OpenTheory_const_name
          {const={Thy="relation",Name="TC"},
           name=(["Relation"],"transitiveClosure")}


Inductive RTC:
  (!x. RTC R x x)
    /\
  (!x y z. R x y /\ RTC R y z ==> RTC R x z)
End
val _ = add_rule { fixity = Suffix 2100,
                   block_style = (AroundEachPhrase, (Portable.CONSISTENT,0)),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "^*"],
                   term_name = "RTC" }
val _ = Unicode.unicode_version {u = UTF8.chr 0xA673, tmnm = "RTC"}
val _ = TeX_notation {hol = UTF8.chr 0xA673, TeX = ("\\HOLTokenSupStar{}", 1)}
val _ = TeX_notation {hol = "^*", TeX = ("\\HOLTokenSupStar{}", 1)}

val RC_DEF = new_definition(
  "RC_DEF",
  ``RC (R:'a->'a->bool) x y <=> (x = y) \/ R x y``);

val SC_DEF = new_definition(
  "SC_DEF",
  ``SC (R:'a->'a->bool) x y <=> R x y \/ R y x``);

val EQC_DEF = new_definition(
  "EQC_DEF",
  ``EQC (R:'a->'a->bool) = RC (TC (SC R))``);
val _ = add_rule { fixity = Suffix 2100,
                   block_style = (AroundEachPhrase, (Portable.CONSISTENT,0)),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK "^="],
                   term_name = "EQC" }


val SC_SYMMETRIC = store_thm(
  "SC_SYMMETRIC",
  ``!R. symmetric (SC R)``,
  REWRITE_TAC [symmetric_def, SC_DEF] THEN MESON_TAC []);

Theorem TC_TRANSITIVE[simp]:
  !R:'a->'a->bool. transitive(TC R)
Proof
 REWRITE_TAC[transitive_def,TC_DEF]
 THEN REPEAT STRIP_TAC
 THEN RES_TAC THEN ASM_MESON_TAC[]
QED

Theorem RTC_INDUCT:
  !R P. (!x. P x x) /\ (!x y z. R x y /\ P y z ==> P x z) ==>
        (!x (y:'a). RTC R x y ==> P x y)
Proof
  MESON_TAC [RTC_ind] (* differs only in choice of induction variable "P" *)
QED

val TC_RULES = store_thm(
  "TC_RULES",
  ``!R. (!x (y:'a). R x y ==> TC R x y) /\
        (!x y z. TC R x y /\ TC R y z ==> TC R x z)``,
  REWRITE_TAC [TC_DEF] THEN REPEAT STRIP_TAC THENL [
    ASM_MESON_TAC [],
    FIRST_ASSUM MATCH_MP_TAC THEN RES_TAC THEN ASM_MESON_TAC []
  ]);

Theorem RTC_RULES = RTC_rules;
Theorem RTC_REFL[simp]:
  RTC R x x
Proof REWRITE_TAC [RTC_RULES]
QED

Theorem RTC_SINGLE[simp]:
  !R x y. R x y ==> RTC R x y
Proof
  PROVE_TAC [RTC_RULES]
QED

Theorem RTC_STRONG_INDUCT[rule_induction]:
  !R P. (!x. P x x) /\ (!x y z. R x y /\ RTC R y z /\ P y z ==> P x z) ==>
        (!x (y:'a). RTC R x y ==> P x y)
Proof
  ASM_MESON_TAC [RTC_strongind]
QED

val RTC_RTC = store_thm(
  "RTC_RTC",
  ``!R (x:'a) y. RTC R x y ==> !z. RTC R y z ==> RTC R x z``,
  GEN_TAC THEN HO_MATCH_MP_TAC RTC_STRONG_INDUCT THEN MESON_TAC [RTC_RULES]);

Theorem RTC_TRANSITIVE[simp]: !R:'a->'a->bool. transitive (RTC R)
Proof REWRITE_TAC [transitive_def] THEN MESON_TAC [RTC_RTC]
QED
Theorem transitive_RTC = RTC_TRANSITIVE

val RTC_TRANS = store_thm(
  "RTC_TRANS",
  ``R^* x y /\ R^* y z ==> R^* x z``,
  METIS_TAC[RTC_TRANSITIVE, transitive_def]);

Theorem RTC_REFLEXIVE[simp]: !R:'a->'a->bool. reflexive (RTC R)
Proof MESON_TAC [reflexive_def, RTC_RULES]
QED
Theorem reflexive_RTC = RTC_REFLEXIVE

Theorem RTC_BRACKETS_RTC_EQN:
  (!x y. R1 x y ==> R2 x y) /\ (!x y. R2 x y ==> RTC R1 x y) ==>
  (RTC R2 = RTC R1)
Proof
  strip_tac >> SIMP_TAC bool_ss [FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM] >>
  conj_tac >> Induct_on ‘RTC’ >> simp_tac (srw_ss()) [] >>
  METIS_TAC[RTC_RTC, RTC_RULES]
QED

Theorem RC_REFLEXIVE[simp]:
  !R:'a->'a->bool. reflexive (RC R)
Proof MESON_TAC [reflexive_def, RC_DEF]
QED
Theorem reflexive_RC = RC_REFLEXIVE

Theorem RC_REFL[simp]:
  RC R x x
Proof
  MESON_TAC [RC_DEF]
QED

Theorem RC_lifts_monotonicities:
  (!x y. R x y ==> R (f x) (f y)) ==> !x y. RC R x y ==> RC R (f x) (f y)
Proof METIS_TAC [RC_DEF]
QED

Theorem RC_MONOTONE[mono]: (!x y. R x y ==> Q x y) ==> RC R x y ==> RC Q x y
Proof
  STRIP_TAC THEN REWRITE_TAC [RC_DEF] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC [] THEN RES_TAC THEN ASM_REWRITE_TAC []
QED

Theorem RC_lifts_invariants:
  (!x y. P x /\ R x y ==> P y) ==> (!x y. P x /\ RC R x y ==> P y)
Proof METIS_TAC [RC_DEF]
QED

Theorem RC_lifts_equalities:
  (!x y. R x y ==> (f x = f y)) ==> (!x y. RC R x y ==> (f x = f y))
Proof METIS_TAC [RC_DEF]
QED

val SC_lifts_monotonicities = store_thm(
  "SC_lifts_monotonicities",
  ``(!x y. R x y ==> R (f x) (f y)) ==> !x y. SC R x y ==> SC R (f x) (f y)``,
  METIS_TAC [SC_DEF]);

val SC_lifts_equalities = store_thm(
  "SC_lifts_equalities",
  ``(!x y. R x y ==> (f x = f y)) ==> !x y. SC R x y ==> (f x = f y)``,
  METIS_TAC [SC_DEF]);

val SC_MONOTONE = store_thm(
  "SC_MONOTONE[mono]",
  ``(!x:'a y. R x y ==> Q x y) ==> SC R x y ==> SC Q x y``,
  STRIP_TAC THEN REWRITE_TAC [SC_DEF] THEN STRIP_TAC THEN RES_TAC THEN
  ASM_REWRITE_TAC [])

val symmetric_RC = store_thm(
  "symmetric_RC",
  ``!R. symmetric (RC R) = symmetric R``,
  REWRITE_TAC [symmetric_def, RC_DEF] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN ASM_MESON_TAC []);
val _ = export_rewrites ["symmetric_RC"]

val antisymmetric_RC = store_thm(
  "antisymmetric_RC",
  ``!R. antisymmetric (RC R) = antisymmetric R``,
  SRW_TAC [][antisymmetric_def, RC_DEF] THEN PROVE_TAC []);
val _ = export_rewrites ["antisymmetric_RC"]

val transitive_RC = store_thm(
  "transitive_RC",
  ``!R. transitive R ==> transitive (RC R)``,
  SRW_TAC [][transitive_def, RC_DEF] THEN PROVE_TAC []);

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
      let val (u,Body) = dest_forall w
          val (v,Body) = dest_forall Body
          val (ant,conseq) = dest_imp Body
          val (TC, R, u', v') = case strip_comb ant of
              (TC, [R, u', v']) => (TC, R, u', v')
            | _ => raise Match
          val _ = assert (equal "TC") (fst (dest_const TC))
          val _ = assert (aconv u) u'
          val _ = assert (aconv v) v'
          val P = list_mk_abs([u,v], conseq)
          val tc_thm' = BETA_RULE(ISPEC P (ISPEC R tc_thm))
      in MATCH_MP_TAC tc_thm' (asl,w)
      end
      handle _ => raise mk_HOL_ERR "<top-level>" "TC_INDUCT_TAC"
                                   "Unanticipated term structure"
 in tac
 end;

val TC_STRONG_INDUCT0 = prove(
  ``!R P. (!x y. R x y ==> P x y) /\
          (!x y z. P x y /\ P y z /\ TC R x y /\ TC R y z ==> P x z) ==>
          (!u v. TC R u v ==> P u v /\ TC R u v)``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN TC_INDUCT_TAC THEN
  ASM_MESON_TAC [TC_RULES]);

Theorem TC_STRONG_INDUCT[rule_induction]:
  !R P. (!x y. R x y ==> P x y) /\
        (!x y z. P x y /\ P y z /\ TC R x y /\ TC R y z ==> P x z) ==>
        (!u v. TC R u v ==> P u v)
Proof REPEAT STRIP_TAC THEN IMP_RES_TAC TC_STRONG_INDUCT0
QED

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

(* can get inductive principles for properties which do not hold generally
  but only for particular cases of x or y in TC R x y *)

fun tc_ind_alt_tacs tc_ind_thm tq =
  REPEAT STRIP_TAC THEN
  POP_ASSUM (ASSUME_TAC o Ho_Rewrite.REWRITE_RULE [BETA_THM]
    o Q.SPEC tq o GEN_ALL o MATCH_MP (REORDER_ANTS rev tc_ind_thm)) THEN
  VALIDATE (POP_ASSUM (ACCEPT_TAC o UNDISCH)) THEN
  POP_ASSUM (K ALL_TAC) THEN REPEAT STRIP_TAC THEN
  TRY COND_CASES_TAC THEN
  FULL_SIMP_TAC bool_ss [TC_SUBSET] THEN
  RES_TAC THEN IMP_RES_TAC TC_RULES ;

val TC_INDUCT_ALT_LEFT = Q.store_thm ("TC_INDUCT_ALT_LEFT",
  `!R Q. (!x. R x b ==> Q x) /\ (!x y. R x y /\ Q y ==> Q x) ==>
    !a. TC R a b ==> Q a`,
  tc_ind_alt_tacs TC_INDUCT_LEFT1 `\x y. if y = b then Q x else TC R x y`) ;

val TC_INDUCT_ALT_RIGHT = Q.store_thm ("TC_INDUCT_ALT_RIGHT",
  `!R Q. (!y. R a y ==> Q y) /\ (!x y. Q x /\ R x y ==> Q y) ==>
    !b. TC R a b ==> Q b`,
  tc_ind_alt_tacs TC_INDUCT_RIGHT1 `\x y. if x = a then Q y else TC R x y`) ;

val TC_lifts_monotonicities = store_thm(
  "TC_lifts_monotonicities",
  ``(!x y. R x y ==> R (f x) (f y)) ==>
    !x y. TC R x y ==> TC R (f x) (f y)``,
  STRIP_TAC THEN HO_MATCH_MP_TAC TC_INDUCT THEN
  METIS_TAC [TC_RULES]);

val TC_lifts_invariants = store_thm(
  "TC_lifts_invariants",
  ``(!x y. P x /\ R x y ==> P y) ==> (!x y. P x /\ TC R x y ==> P y)``,
  STRIP_TAC THEN
  Q_TAC SUFF_TAC `!x y. TC R x y ==> P x ==> P y` THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC TC_INDUCT THEN METIS_TAC []);

val TC_lifts_equalities = store_thm(
  "TC_lifts_equalities",
  ``(!x y. R x y ==> (f x = f y)) ==> (!x y. TC R x y ==> (f x = f y))``,
  STRIP_TAC THEN HO_MATCH_MP_TAC TC_INDUCT THEN METIS_TAC []);

(* generalisation of above results *)
val TC_lifts_transitive_relations = store_thm(
  "TC_lifts_transitive_relations",
  ``(!x y. R x y ==> Q (f x) (f y)) /\ transitive Q ==>
    (!x y. TC R x y ==> Q (f x) (f y))``,
  STRIP_TAC THEN HO_MATCH_MP_TAC TC_INDUCT THEN METIS_TAC [transitive_def]);

val TC_implies_one_step = Q.store_thm(
"TC_implies_one_step",
`!x y . R^+ x y /\ x <> y ==> ?z. R x z /\ x <> z`,
REWRITE_TAC [GSYM AND_IMP_INTRO] THEN
HO_MATCH_MP_TAC TC_INDUCT THEN
SRW_TAC [SatisfySimps.SATISFY_ss][] THEN
PROVE_TAC []);

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

Theorem TC_LEFT1_I:
  !x y z. R x y /\ TC R y z ==> TC R x z
Proof
  METIS_TAC[TC_RULES]
QED

Theorem TC_RIGHT1_I:
  !x y z. TC R x y /\ R y z ==> TC R x z
Proof
  METIS_TAC[TC_RULES]
QED

(* can get inductive principles for properties which do not hold generally
  but only for particular cases of x or y in RTC R x y *)

Theorem RTC_ALT_DEF:
  !R a b. RTC R a b <=> !Q. Q b /\ (!x y. R x y /\ Q y ==> Q x) ==> Q a
Proof
  REWRITE_TAC [EQ_IMP_THM] THEN CONV_TAC (REDEPTH_CONV FORALL_AND_CONV) THEN
  CONJ_TAC THEN1 (GEN_TAC THEN Induct_on `RTC` THEN METIS_TAC[]) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN (Q.SPEC_THEN `\z. RTC R z b` (MATCH_MP_TAC o BETA_RULE)) THEN
  METIS_TAC[RTC_RULES]
QED

val RTC_ALT_INDUCT = Q.store_thm ("RTC_ALT_INDUCT",
  `!R Q b. Q b /\ (!x y. R x y /\ Q y ==> Q x) ==> !x. RTC R x b ==> Q x`,
  REWRITE_TAC [RTC_ALT_DEF] THEN REPEAT STRIP_TAC THEN RES_TAC) ;

val RTC_ALT_RIGHT_DEF = Q.store_thm ("RTC_ALT_RIGHT_DEF",
  `!R a b. RTC R a b = !Q. Q a /\ (!y z. Q y /\ R y z ==> Q z) ==> Q b`,
  REWRITE_TAC [RTC_ALT_DEF] THEN REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
  FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `$~ o Q`) THEN
  REV_FULL_SIMP_TAC bool_ss [combinTheory.o_THM] THEN RES_TAC) ;

val RTC_ALT_RIGHT_INDUCT = Q.store_thm ("RTC_ALT_RIGHT_INDUCT",
  `!R Q a. Q a /\ (!y z. Q y /\ R y z ==> Q z) ==> !z. RTC R a z ==> Q z`,
  REWRITE_TAC [RTC_ALT_RIGHT_DEF] THEN REPEAT STRIP_TAC THEN RES_TAC) ;

val RTC_INDUCT_RIGHT1 = store_thm(
  "RTC_INDUCT_RIGHT1",
  ``!R P. (!x. P x x) /\
          (!x y z. P x y /\ R y z ==> P x z) ==>
          (!x y. RTC R x y ==> P x y)``,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (irule o MATCH_MP (REORDER_ANTS rev RTC_ALT_RIGHT_INDUCT)) THEN
  ASM_REWRITE_TAC []) ;

val RTC_RULES_RIGHT1 = store_thm(
  "RTC_RULES_RIGHT1",
  ``!R. (!x. RTC R x x) /\ (!x y z. RTC R x y /\ R y z ==> RTC R x z)``,
  REWRITE_TAC [RTC_ALT_RIGHT_DEF] THEN
  REPEAT STRIP_TAC THEN RES_TAC THEN RES_TAC) ;

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


val EXTEND_RTC_TC_EQN = store_thm(
  "EXTEND_RTC_TC_EQN",
  ``!R x z. TC R x z = ?y. (R x y /\ RTC R y z)``,
  GEN_TAC THEN
  Q_TAC SUFF_TAC `!x z. TC R x z ==> ?y. R x y /\ RTC R y z` THEN1
        MESON_TAC [EXTEND_RTC_TC] THEN
  HO_MATCH_MP_TAC TC_INDUCT THEN
  PROVE_TAC[RTC_RULES, RTC_TRANSITIVE, transitive_def,
              RTC_RULES_RIGHT1]);

Theorem EXTEND_RTC_TC_RIGHT1:
  !R x y z. RTC R x y /\ R y z ==> TC R x z
Proof
  GEN_TAC THEN
  Q_TAC SUFF_TAC `!x y. RTC R x y ==> !z. R y z ==> TC R x z` THEN1
        MESON_TAC [] THEN
  HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 THEN
  MESON_TAC [TC_RULES]
QED

Theorem EXTEND_RTC_TC_RIGHT1_EQN:
  !R x z. TC R x z = ?y. (RTC R x y /\ R y z)
Proof
  GEN_TAC THEN
  Q_TAC SUFF_TAC `!x z. TC R x z ==> ?y. RTC R x y /\ R y z` THEN1
        MESON_TAC [EXTEND_RTC_TC_RIGHT1] THEN
  HO_MATCH_MP_TAC TC_INDUCT_RIGHT1 THEN
  PROVE_TAC[RTC_RULES, RTC_TRANSITIVE, transitive_def,
              RTC_RULES_RIGHT1]
QED

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
val _ = export_rewrites ["RC_IDEM"]

val SC_IDEM = store_thm(
  "SC_IDEM",
  ``!R:'a->'a->bool. SC (SC R) = SC R``,
  SIMP_TAC bool_ss [SC_SYMMETRIC, symmetric_SC_identity]);
val _ = export_rewrites ["SC_IDEM"]

val TC_IDEM = store_thm(
  "TC_IDEM",
  ``!R:'a->'a->bool.  TC (TC R) = TC R``,
  SIMP_TAC bool_ss [TC_TRANSITIVE, transitive_TC_identity]);
val _ = export_rewrites ["TC_IDEM"]

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

val reflexive_TC = store_thm(
  "reflexive_TC",
  ``!R. reflexive R ==> reflexive (TC R)``,
  PROVE_TAC [reflexive_def,TC_SUBSET]);

val EQC_EQUIVALENCE = store_thm(
  "EQC_EQUIVALENCE",
  ``!R. equivalence (EQC R)``,
  REWRITE_TAC [equivalence_def, EQC_DEF, RC_REFLEXIVE, symmetric_RC] THEN
  MESON_TAC [symmetric_TC, TC_RC_EQNS, TC_TRANSITIVE, SC_SYMMETRIC]);
val _ = export_rewrites ["EQC_EQUIVALENCE"]

val EQC_IDEM = store_thm(
  "EQC_IDEM",
  ``!R:'a->'a->bool. EQC(EQC R) = EQC R``,
  SIMP_TAC bool_ss [EQC_DEF, RC_MOVES_OUT, symmetric_SC_identity,
                    symmetric_TC, SC_SYMMETRIC, TC_IDEM]);
val _ = export_rewrites ["EQC_IDEM"]


val RTC_IDEM = store_thm(
  "RTC_IDEM",
  ``!R:'a->'a->bool.  RTC (RTC R) = RTC R``,
  SIMP_TAC bool_ss [GSYM TC_RC_EQNS, RC_MOVES_OUT, TC_IDEM]);
val _ = export_rewrites ["RTC_IDEM"]

val RTC_CASES1 = store_thm(
  "RTC_CASES1",
  ``!R (x:'a) y.  RTC R x y <=> (x = y) \/ ?u. R x u /\ RTC R u y``,
  SIMP_TAC bool_ss [EQ_IMP_THM, FORALL_AND_THM] THEN CONJ_TAC THENL [
    GEN_TAC THEN HO_MATCH_MP_TAC RTC_INDUCT THEN MESON_TAC [RTC_RULES],
    MESON_TAC [RTC_RULES]
  ]);

val RTC_CASES_TC = store_thm(
  "RTC_CASES_TC",
  ``!R x y. R^* x y <=> (x = y) \/ R^+ x y``,
  METIS_TAC [EXTEND_RTC_TC_EQN, RTC_CASES1]);

val RTC_CASES2 = store_thm(
  "RTC_CASES2",
  ``!R (x:'a) y. RTC R x y <=> (x = y) \/ ?u. RTC R x u /\ R u y``,
  SIMP_TAC bool_ss [EQ_IMP_THM, FORALL_AND_THM] THEN CONJ_TAC THENL [
    GEN_TAC THEN HO_MATCH_MP_TAC RTC_INDUCT THEN MESON_TAC [RTC_RULES],
    MESON_TAC [RTC_RULES, RTC_SUBSET, RTC_RTC]
  ]);

val RTC_CASES_RTC_TWICE = store_thm(
  "RTC_CASES_RTC_TWICE",
  ``!R (x:'a) y. RTC R x y <=> ?u. RTC R x u /\ RTC R u y``,
  SIMP_TAC bool_ss [EQ_IMP_THM, FORALL_AND_THM] THEN CONJ_TAC THENL [
    GEN_TAC THEN HO_MATCH_MP_TAC RTC_INDUCT THEN MESON_TAC [RTC_RULES],
    MESON_TAC [RTC_RULES, RTC_SUBSET, RTC_RTC]
  ]);

val TC_CASES1_E =
Q.store_thm
("TC_CASES1_E",
  `!R x z. TC R x z ==> R x z \/ ?y:'a. R x y /\ TC R y z`,
GEN_TAC
 THEN TC_INDUCT_TAC
 THEN MESON_TAC [REWRITE_RULE[transitive_def] TC_TRANSITIVE, TC_SUBSET]);

val TC_CASES1 = store_thm(
  "TC_CASES1",
  ``TC R x z <=> R x z \/ ?y:'a. R x y /\ TC R y z``,
  MESON_TAC[TC_RULES, TC_CASES1_E])

val TC_CASES2_E =
Q.store_thm
("TC_CASES2_E",
    `!R x z. TC R x z ==> R x z \/ ?y:'a. TC R x y /\ R y z`,
GEN_TAC
 THEN TC_INDUCT_TAC
 THEN MESON_TAC [REWRITE_RULE[transitive_def] TC_TRANSITIVE, TC_SUBSET]);

val TC_CASES2 = store_thm(
  "TC_CASES2",
  ``TC R x z <=> R x z \/ ?y:'a. TC R x y /\ R y z``,
  MESON_TAC [TC_RULES, TC_CASES2_E]);

val TC_MONOTONE = store_thm(
  "TC_MONOTONE[mono]",
  ``(!x y. R x y ==> Q x y) ==> TC R x y ==> TC Q x y``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`y`, `x`] THEN
  TC_INDUCT_TAC THEN ASM_MESON_TAC [TC_RULES]);

val RTC_MONOTONE = store_thm(
  "RTC_MONOTONE[mono]",
  ``(!x y. R x y ==> Q x y) ==> RTC R x y ==> RTC Q x y``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`y`, `x`] THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN ASM_MESON_TAC [RTC_RULES]);

val EQC_INDUCTION = store_thm(
  "EQC_INDUCTION",
  ``!R P. (!x y. R x y ==> P x y) /\
          (!x. P x x) /\
          (!x y. P x y ==> P y x) /\
          (!x y z. P x y /\ P y z ==> P x z) ==>
          (!x y. EQC R x y ==> P x y)``,
  REWRITE_TAC [EQC_DEF] THEN REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC bool_ss [RC_DEF] THEN
  Q.PAT_X_ASSUM `TC _ x y` MP_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`y`, `x`] THEN
  HO_MATCH_MP_TAC TC_INDUCT THEN REWRITE_TAC [SC_DEF] THEN
  ASM_MESON_TAC []);

val EQC_REFL = store_thm(
  "EQC_REFL",
  ``!R x. EQC R x x``,
  SRW_TAC [][EQC_DEF, RC_DEF]);
val _ = export_rewrites ["EQC_REFL"]

val EQC_R = store_thm(
  "EQC_R",
  ``!R x y. R x y ==> EQC R x y``,
  SRW_TAC [][EQC_DEF, RC_DEF] THEN
  DISJ2_TAC THEN MATCH_MP_TAC TC_SUBSET THEN
  SRW_TAC [][SC_DEF]);

val EQC_SYM = store_thm(
  "EQC_SYM",
  ``!R x y. EQC R x y ==> EQC R y x``,
  SRW_TAC [][EQC_DEF, RC_DEF] THEN
  Q.SUBGOAL_THEN `symmetric (TC (SC R))` ASSUME_TAC THEN1
     SRW_TAC [][SC_SYMMETRIC, symmetric_TC] THEN
  PROVE_TAC [symmetric_def]);

val EQC_TRANS = store_thm(
  "EQC_TRANS",
  ``!R x y z. EQC R x y /\ EQC R y z ==> EQC R x z``,
  REPEAT GEN_TAC THEN
  Q_TAC SUFF_TAC `transitive (EQC R)` THEN1 PROVE_TAC [transitive_def] THEN
  SRW_TAC [][EQC_DEF, transitive_RC, TC_TRANSITIVE])

val transitive_EQC = Q.store_thm(
"transitive_EQC",
`transitive (EQC R)`,
PROVE_TAC [transitive_def,EQC_TRANS]);

val symmetric_EQC = Q.store_thm(
"symmetric_EQC",
`symmetric (EQC R)`,
PROVE_TAC [symmetric_def,EQC_SYM]);

val reflexive_EQC = Q.store_thm(
"reflexive_EQC",
`reflexive (EQC R)`,
PROVE_TAC [reflexive_def,EQC_REFL]);

Theorem EQC_MOVES_IN[simp]:
  !R. (EQC (RC R) = EQC R) /\ (EQC (SC R) = EQC R) /\ (EQC (TC R) = EQC R)
Proof
  SRW_TAC [][EQC_DEF,RC_MOVES_OUT,SC_IDEM] THEN
  AP_TERM_TAC THEN
  SRW_TAC [][FUN_EQ_THM] THEN
  REVERSE EQ_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`x'`,`x`] THEN
  HO_MATCH_MP_TAC TC_INDUCT THEN1 (SRW_TAC [][SC_DEF] THEN
                                   PROVE_TAC [TC_RULES,SC_DEF]) THEN
  REVERSE (SRW_TAC [][SC_DEF]) THEN1
   PROVE_TAC [TC_RULES,SC_DEF] THEN
  Q.MATCH_ASSUM_RENAME_TAC `R^+ a b` THEN
  POP_ASSUM MP_TAC THEN
  MAP_EVERY Q.ID_SPEC_TAC [`b`,`a`] THEN
  HO_MATCH_MP_TAC TC_INDUCT THEN
  SRW_TAC [][SC_DEF] THEN
  PROVE_TAC [TC_RULES,SC_DEF]
QED

Theorem STRONG_EQC_INDUCTION[rule_induction]:
  !R P. (!x y. R x y ==> P x y) /\
        (!x. P x x) /\
        (!x y. EQC R x y /\ P x y ==> P y x) /\
        (!x y z. P x y /\ P y z /\ EQC R x y /\ EQC R y z ==> P x z)
      ==>
        !x y. EQC R x y ==> P x y
Proof
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!x y. EQC R x y ==> EQC R x y /\ P x y`
   THEN1 PROVE_TAC [] THEN
  HO_MATCH_MP_TAC EQC_INDUCTION THEN
  PROVE_TAC [EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS]
QED

val ALT_equivalence = store_thm(
  "ALT_equivalence",
  ``!R. equivalence R = !x y. R x y = (R x = R y)``,
  REWRITE_TAC [equivalence_def, reflexive_def, symmetric_def,
               transitive_def, FUN_EQ_THM, EQ_IMP_THM] THEN
  MESON_TAC []);

val EQC_MONOTONE = store_thm(
  "EQC_MONOTONE[mono]",
  ``(!x y. R x y ==> R' x y) ==> EQC R x y ==> EQC R' x y``,
  STRIP_TAC THEN MAP_EVERY Q.ID_SPEC_TAC [`y`, `x`] THEN
  HO_MATCH_MP_TAC STRONG_EQC_INDUCTION THEN
  METIS_TAC [EQC_R, EQC_TRANS, EQC_SYM, EQC_REFL]);

val RTC_EQC = store_thm(
  "RTC_EQC",
  ``!x y. RTC R x y ==> EQC R x y``,
  HO_MATCH_MP_TAC RTC_INDUCT THEN METIS_TAC [EQC_R, EQC_REFL, EQC_TRANS]);

val RTC_lifts_monotonicities = store_thm(
  "RTC_lifts_monotonicities",
  ``(!x y. R x y ==> R (f x) (f y)) ==>
    !x y. R^* x y ==> R^* (f x) (f y)``,
  STRIP_TAC THEN HO_MATCH_MP_TAC RTC_INDUCT THEN SRW_TAC [][] THEN
  METIS_TAC [RTC_RULES]);

val RTC_lifts_reflexive_transitive_relations = Q.store_thm(
  "RTC_lifts_reflexive_transitive_relations",
  `(!x y. R x y ==> Q (f x) (f y)) /\ reflexive Q /\ transitive Q ==>
   !x y. R^* x y ==> Q (f x) (f y)`,
  STRIP_TAC THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN
  FULL_SIMP_TAC bool_ss [reflexive_def,transitive_def] THEN
  METIS_TAC []);

val RTC_lifts_equalities = Q.store_thm(
  "RTC_lifts_equalities",
  `(!x y. R x y ==> (f x = f y)) ==> !x y. R^* x y ==> (f x = f y)`,
  STRIP_TAC THEN
  HO_MATCH_MP_TAC RTC_lifts_reflexive_transitive_relations THEN
  ASM_SIMP_TAC bool_ss [reflexive_def,transitive_def]);

val RTC_lifts_invariants = Q.store_thm(
  "RTC_lifts_invariants",
  `(!x y. P x /\ R x y ==> P y) ==> !x y. P x /\ R^* x y ==> P y`,
  STRIP_TAC THEN
  REWRITE_TAC [Once CONJ_COMM] THEN
  REWRITE_TAC [GSYM AND_IMP_INTRO] THEN
  HO_MATCH_MP_TAC RTC_INDUCT THEN
  METIS_TAC []);

(*---------------------------------------------------------------------------*
 * Wellfounded relations. Wellfoundedness: Every non-empty set has an        *
 * R-minimal element. Applications of wellfoundedness to specific types      *
 * (numbers, lists, etc.) can be found in the respective theories.           *
 *---------------------------------------------------------------------------*)

val WF_DEF =
Q.new_definition
 ("WF_DEF", `WF R = !B. (?w:'a. B w) ==> ?min. B min /\ !b. R b min ==> ~B b`);
val _ = OpenTheoryMap.OpenTheory_const_name
          {const={Thy="relation",Name="WF"},name=(["Relation"],"wellFounded")}

(*---------------------------------------------------------------------------*)
(* Misc. proof tools, from pre-automation days.                              *)
(*---------------------------------------------------------------------------*)

val USE_TAC = IMP_RES_THEN(fn th => ONCE_REWRITE_TAC[th]);

val NNF_CONV =
   let val DE_MORGAN = REWRITE_CONV
                        [TAUT `~(x==>y) = (x /\ ~y)`,
                         TAUT `~x \/ y <=> (x ==> y)`,DE_MORGAN_THM]
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
                   (REWRITE_RULE [TAUT`A==>B==>C <=> A/\B==>C`]
                      (CONV_RULE (ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV)
                          WF_INDUCTION_THM))
      val [R,P] = fst(strip_forall(concl wf_thm0))
      val wf_thm1 = GENL [P,R](SPEC_ALL wf_thm0)
   fun tac (asl,w) =
    let val (Rator,Rand) = dest_comb w
        val _ = assert (equal "!") (fst (dest_const Rator))
        val thi = ISPEC Rand wf_thm1
        fun eqRand t = Term.compare(Rand,t) = EQUAL
        val thf = CONV_RULE(ONCE_DEPTH_CONV
                              (BETA_CONV o assert (eqRand o rator))) thi
    in MATCH_MP_TAC thf (asl,w)
    end
    handle _ => raise mk_HOL_ERR "" "WF_INDUCT_TAC"
                      "Unanticipated term structure"
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
  THEN Q.UNDISCH_THEN `min=y` SUBST_ALL_TAC
  THEN DISCH_TAC THEN RES_TAC);

(* delete this or the previous if we abbreviate irreflexive *)
val WF_irreflexive = store_thm(
  "WF_irreflexive",
  ``WF R ==> irreflexive R``,
  METIS_TAC [WF_NOT_REFL, irreflexive_def]);

(*---------------------------------------------------------------------------
 * Some combinators for wellfounded relations.
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * The empty relation is wellfounded.
 *---------------------------------------------------------------------------*)

val EMPTY_REL_DEF =
Q.new_definition
        ("EMPTY_REL_DEF", `EMPTY_REL (x:'a) (y:'a) = F`);
val _ = export_rewrites ["EMPTY_REL_DEF"]
Overload REMPTY = ``EMPTY_REL``
val _ = Unicode.unicode_version {u = UnicodeChars.emptyset ^ UnicodeChars.sub_r,
                                 tmnm = "EMPTY_REL"}


val WF_EMPTY_REL =
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
              (CONJ th (MATCH_MP TC_CASES2_E th)))
   THENL
   [ Q.EXISTS_TAC`a` THEN ASM_REWRITE_TAC[] THEN RES_TAC
     THEN MAP_EVERY Q.EXISTS_TAC [`b'`, `z`] THEN ASM_REWRITE_TAC[],
     Q.EXISTS_TAC`y` THEN ASM_REWRITE_TAC[]
     THEN MAP_EVERY Q.EXISTS_TAC[`a`,`z`] THEN ASM_REWRITE_TAC[]
     THEN IMP_RES_TAC TC_SUBSET]
   THEN
   IMP_RES_TAC(REWRITE_RULE[transitive_def] TC_TRANSITIVE)]);

val WF_TC_EQN = store_thm(
  "WF_TC_EQN",
  ``WF (R^+) <=> WF R``,
  METIS_TAC [WF_TC, TC_SUBSET, WF_SUBSET]);

val WF_noloops = store_thm(
  "WF_noloops",
  ``WF R ==> TC R x y ==> x <> y``,
  METIS_TAC [WF_NOT_REFL, WF_TC_EQN]);

val WF_antisymmetric = store_thm(
  "WF_antisymmetric",
  ``WF R ==> antisymmetric R``,
  REWRITE_TAC [antisymmetric_def] THEN STRIP_TAC THEN
  MAP_EVERY Q.X_GEN_TAC [`a`, `b`] THEN
  STRIP_TAC THEN Q_TAC SUFF_TAC `TC R a a` THEN1 METIS_TAC [WF_noloops] THEN
  METIS_TAC [TC_RULES]);

(*---------------------------------------------------------------------------
 * If `f x` remains unchanged in relation `R'` and `f x` always satisfy `P`,
 * and there is a mapping `g` such that `R' x y ==> R (f x) (g x) (g y)`, then
 * to prove `WF R'`, it is sufficient to prove that `P (f x) ==> WF (R (f x))`.
 *---------------------------------------------------------------------------*)
Theorem WF_PULL:
  !P f R g R'.
    (!x. P (f x) ==> WF (R (f x))) /\
    (!x y. R' x y ==> P (f x) /\ f x = f y /\ R (f x) (g x) (g y)) ==>
    WF R'
Proof
  rw_tac(srw_ss())[WF_DEF] >>
  Cases_on `?w'. P (f w') /\ B w'`
  >- (
    POP_ASSUM STRIP_ASSUME_TAC >>
    FIRST_X_ASSUM drule >>
    Q.PAT_X_ASSUM `B w` (K ALL_TAC) >>
    DISCH_THEN $ Q.SPEC_THEN
      `\x. ?y. x = g y /\ B y /\ P (f y) /\ f y = f w'`
      (ASSUME_TAC o SIMP_RULE bool_ss [PULL_EXISTS]) >>
    FIRST_X_ASSUM (dxrule_then dxrule) >>
    METIS_TAC[]) >>
  METIS_TAC[]
QED

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

val inv_image_thm = save_thm(
  "inv_image_thm",
  SIMP_RULE bool_ss [FUN_EQ_THM] inv_image_def)
val _ = export_rewrites ["inv_image_thm"]

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

val total_inv_image = store_thm(
  "total_inv_image",
  ``!R f. total R ==> total (inv_image R f)``,
  SRW_TAC[][total_def, inv_image_def]);
val _ = export_rewrites ["total_inv_image"]

val reflexive_inv_image = store_thm(
  "reflexive_inv_image",
  ``!R f. reflexive R ==> reflexive (inv_image R f)``,
  SRW_TAC[][reflexive_def, inv_image_def]);
val _ = export_rewrites ["reflexive_inv_image"]

val symmetric_inv_image = store_thm(
  "symmetric_inv_image",
  ``!R f. symmetric R ==> symmetric (inv_image R f)``,
  SRW_TAC[][symmetric_def, inv_image_def]);
val _ = export_rewrites ["symmetric_inv_image"]

val transitive_inv_image = store_thm(
  "transitive_inv_image",
  ``!R f. transitive R ==> transitive (inv_image R f)``,
  SRW_TAC[][transitive_def, inv_image_def] THEN METIS_TAC[]);
val _ = export_rewrites ["transitive_inv_image"]

(*---------------------------------------------------------------------------
 * Now the WF recursion theorem. Based on Tobias Nipkow's Isabelle development
 * of wellfounded recursion, which itself is a generalization of Mike
 * Gordon's HOL development of the primitive recursion theorem.
 *---------------------------------------------------------------------------*)

(* NOTE: Now RESTRICT is based on the new combinTheory.RESTRICTION

   :('a -> 'b) -> ('a -> 'a -> bool) -> 'a -> 'a -> 'b
 *)
val RESTRICT = new_definition
  ("RESTRICT", “RESTRICT (f :'a->'b) R (x :'a) = RESTRICTION (\y. R y x) f”);

(* The old definition of RESTRICT now becomes a theorem *)
Theorem RESTRICT_DEF :
    !(f :'a->'b) R x. RESTRICT f R x = \y. if R y x then f y else ARB
Proof
    SRW_TAC[][RESTRICT, FUN_EQ_THM, RESTRICTION, IN_DEF]
QED

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

Triviality the_fun_rw1:
 (?g:'a->'b. approx R M x g)
      ==>
  !w. R w x
       ==>
     (the_fun R M x w = M (RESTRICT (the_fun R M x) R w) w)
Proof
 DISCH_THEN (MP_TAC o MP approx_the_fun2) THEN
 DISCH_THEN (fn th => GEN_TAC THEN MP_TAC (SPEC_ALL th))
 THEN COND_CASES_TAC
 THEN ASM_REWRITE_TAC[]
QED

Triviality the_fun_rw2:
   (?g:'a->'b. approx R M x g)  ==> !w. ~R w x ==> (the_fun R M x w = ARB)
Proof
 DISCH_THEN (MP_TAC o MP approx_the_fun2) THEN
 DISCH_THEN (fn th => GEN_TAC THEN MP_TAC (SPEC_ALL th))
 THEN COND_CASES_TAC
 THEN ASM_REWRITE_TAC[]
QED

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
  THEN RULE_ASSUM_TAC (REWRITE_RULE[TAUT`A==>B==>C==>D <=> A/\B/\C==>D`,
                                    transitive_def])
  THEN FIRST_ASSUM MATCH_MP_TAC
  THEN RES_TAC THEN ASM_REWRITE_TAC[]);

Triviality AGREE_BELOW =
   REWRITE_RULE[TAUT`A==>B==>C==>D <=> B/\C/\A==>D`]
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
  THENL [ MATCH_MP_TAC AGREE_BELOW THEN REPEAT ID_EX_TAC
            THEN RES_TAC THEN ASM_REWRITE_TAC[transitive_def],
          Q.UNDISCH_TAC`approx R M v (g:'a->'b)`
            THEN DISCH_THEN(fn th =>
                   ASM_REWRITE_TAC[REWRITE_RULE[approx_ext]th])]);


(*---------------------------------------------------------------------------
 * Every x has an approximation. This is the crucial theorem.
 *---------------------------------------------------------------------------*)

Theorem EXISTS_LEMMA[local]:
  !R M. WF R /\ transitive R ==> !x. ?f:'a->'b. approx R M x f
Proof
REPEAT GEN_TAC >> STRIP_TAC
  >> WF_INDUCT_TAC
  >> Q.EXISTS_TAC`R` >> ASM_REWRITE_TAC[] >> GEN_TAC
  >> DISCH_THEN  (* Adjust IH by applying Choice *)
       (ASSUME_TAC o Q.GEN`y` o Q.DISCH`R (y:'a) (x:'a)`
                   o (fn th => REWRITE_RULE[GSYM the_fun_def] th)
                   o SELECT_RULE o UNDISCH o Q.ID_SPEC)
  >> Q.EXISTS_TAC`\p. if R p x then M (the_fun R M p) p else ARB` (* witness *)
  >> REWRITE_TAC[approx_ext] >> BETA_TAC >> GEN_TAC
  >> COND_CASES_TAC
  >> ASM_REWRITE_TAC[]
  >> EXPOSE_CUTS_TAC
  >> RES_THEN (SUBST1_TAC o REWRITE_RULE[approx_def])     (* use IH *)
  >> REWRITE_TAC[CUTS_EQ]
  >> Q.X_GEN_TAC`v` >> BETA_TAC >> DISCH_TAC
  >> RULE_ASSUM_TAC(REWRITE_RULE[transitive_def]) >> RES_TAC
  >> ASM_REWRITE_TAC[]
  >> EXPOSE_CUTS_TAC
  >> MATCH_MP_TAC RESTRICT_FUN_EQ
  >> MAP_EVERY Q.EXISTS_TAC[`M`,`w`]
  >> ASM_REWRITE_TAC[transitive_def]
  >> RES_TAC
QED


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
   THEN ONCE_REWRITE_TAC[TAUT `a ==> b <=> a ==> a /\ b`]
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

(*---------------------------------------------------------------------------*)
(* A formalization of some of the results in                                 *)
(*                                                                           *)
(*   "Inductive Invariants for Nested Recursion",                            *)
(*    Sava Krsti\'{c} and John Matthews,                                     *)
(*    TPHOLs 2003, LNCS vol. 2758, pp. 253-269.                              *)
(*                                                                           *)
(*---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------*)
(* Definition. P is an "inductive invariant" of the functional M with        *)
(* respect to the wellfounded relation R.                                    *)
(*---------------------------------------------------------------------------*)

val INDUCTIVE_INVARIANT_DEF =
 Q.new_definition
 ("INDUCTIVE_INVARIANT_DEF",
  `INDUCTIVE_INVARIANT R P M =
      !f x. (!y. R y x ==> P y (f y)) ==> P x (M f x)`);

(*---------------------------------------------------------------------------*)
(* Definition. P is an inductive invariant of the functional M on set D with *)
(* respect to the wellfounded relation R.                                    *)
(*---------------------------------------------------------------------------*)

val INDUCTIVE_INVARIANT_ON_DEF =
 Q.new_definition
 ("INDUCTIVE_INVARIANT_ON_DEF",
  `INDUCTIVE_INVARIANT_ON R D P M =
      !f x. D x /\ (!y. D y ==> R y x ==> P y (f y)) ==> P x (M f x)`);

(*---------------------------------------------------------------------------*)
(* The key theorem, corresponding to theorem 1 of the paper.                 *)
(*---------------------------------------------------------------------------*)

val INDUCTIVE_INVARIANT_WFREC = Q.store_thm
("INDUCTIVE_INVARIANT_WFREC",
 `!R P M. WF R /\ INDUCTIVE_INVARIANT R P M ==> !x. P x (WFREC R M x)`,
 REPEAT GEN_TAC THEN STRIP_TAC
   THEN IMP_RES_THEN HO_MATCH_MP_TAC WF_INDUCTION_THM
   THEN FULL_SIMP_TAC bool_ss [INDUCTIVE_INVARIANT_DEF]
   THEN METIS_TAC [WFREC_THM,RESTRICT_DEF]);

Theorem TFL_INDUCTIVE_INVARIANT_WFREC:
  !f R P M x. (f = WFREC R M) /\ WF R /\ INDUCTIVE_INVARIANT R P M ==> P x (f x)
Proof PROVE_TAC [INDUCTIVE_INVARIANT_WFREC]
QED

val lem =
  INDUCTIVE_INVARIANT_WFREC |> Q.SPEC ‘R’ |> Q.SPEC ‘\x y. D x ==> P x y’
                            |> REWRITE_RULE[INDUCTIVE_INVARIANT_DEF]
                            |> BETA_RULE

Theorem INDUCTIVE_INVARIANT_ON_WFREC:
  !R P M D x. WF R /\ INDUCTIVE_INVARIANT_ON R D P M /\ D x ==>
              P x (WFREC R M x)
Proof
 SIMP_TAC bool_ss [INDUCTIVE_INVARIANT_ON_DEF] THEN PROVE_TAC [lem]
QED


Theorem TFL_INDUCTIVE_INVARIANT_ON_WFREC:
  !f R D P M x.
     f = WFREC R M /\ WF R /\ INDUCTIVE_INVARIANT_ON R D P M /\ D x ==>
     P x (f x)
Proof PROVE_TAC [INDUCTIVE_INVARIANT_ON_WFREC]
QED

local val lem =
  GEN_ALL
    (REWRITE_RULE []
      (BETA_RULE
           (Q.INST [`P` |-> `\a b. (M (WFREC R M) a = b) /\
                                   (WFREC R M a = b) /\ P a b`]
            (SPEC_ALL INDUCTIVE_INVARIANT_ON_WFREC))))
in
val IND_FIXPOINT_ON_LEMMA = Q.prove
(`!R D M P x.
  WF R /\ D x /\
  (!f x. D x /\ (!y. D y /\ R y x ==> P y (WFREC R M y) /\ (f y = WFREC R M y))
         ==> P x (WFREC R M x) /\ (M f x = WFREC R M x))
  ==>
   (M (WFREC R M) x = WFREC R M x) /\ P x (WFREC R M x)`,
 REPEAT GEN_TAC THEN STRIP_TAC
   THEN MATCH_MP_TAC lem
   THEN ID_EX_TAC
   THEN ASM_REWRITE_TAC [INDUCTIVE_INVARIANT_ON_DEF]
   THEN METIS_TAC [])
end;

(*---------------------------------------------------------------------------*)
(* End of Krstic/Matthews results                                            *)
(*---------------------------------------------------------------------------*)


(* ----------------------------------------------------------------------
    inverting a relation
   ---------------------------------------------------------------------- *)

val inv_DEF = new_definition(
  "inv_DEF",
  ``inv (R:'a->'b->bool) x y = R y x``);
val _ = export_rewrites ["inv_DEF"]
(* superscript suffix T, for "transpose" *)
val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                   fixity = Suffix 2100,
                   paren_style = OnlyIfNecessary,
                   pp_elements = [TOK (UTF8.chr 0x1D40)],
                   term_name = "relinv"}
Overload relinv = ``inv``
val _ = TeX_notation { hol = (UTF8.chr 0x1D40),
                       TeX = ("\\HOLTokenRInverse{}", 1) }

Theorem inv_inv[simp]:
  !R. inv (inv R) = R
Proof SIMP_TAC bool_ss [FUN_EQ_THM, inv_DEF]
QED

val inv_RC = store_thm(
  "inv_RC",
  ``!R. inv (RC R) = RC (inv R)``,
  SIMP_TAC bool_ss [RC_DEF, inv_DEF, FUN_EQ_THM] THEN MESON_TAC []);

Theorem inv_SC[simp]:
  !R. (inv (SC R) = SC R) /\ (SC (inv R) = SC R)
Proof
  SIMP_TAC bool_ss [inv_DEF, SC_DEF, FUN_EQ_THM] THEN MESON_TAC []
QED

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

Theorem inv_EQC[simp]:
  !R. (inv (EQC R) = EQC R) /\ (EQC (inv R) = EQC R)
Proof
  SIMP_TAC bool_ss [EQC_DEF, inv_TC, inv_SC, inv_RC]
QED

val inv_MOVES_OUT = store_thm(
  "inv_MOVES_OUT",
  ``!R. (inv (inv R) = R) /\ (SC (inv R) = SC R) /\
        (RC (inv R) = inv (RC R)) /\ (TC (inv R) = inv (TC R)) /\
        (RTC (inv R) = inv (RTC R)) /\ (EQC (inv R) = EQC R)``,
  SIMP_TAC bool_ss [GSYM TC_RC_EQNS, EQC_DEF, inv_TC, inv_SC, inv_inv, inv_RC])

Theorem reflexive_inv[simp]:
  !R. reflexive (inv R) = reflexive R
Proof SIMP_TAC bool_ss [inv_DEF, reflexive_def]
QED

Theorem irreflexive_inv[simp]:
  !R. irreflexive (inv R) = irreflexive R
Proof
  SRW_TAC [][irreflexive_def, inv_DEF]
QED

Theorem symmetric_inv[simp]:
  !R. symmetric (inv R) = symmetric R
Proof
  SIMP_TAC bool_ss [inv_DEF, symmetric_def] THEN MESON_TAC []
QED

Theorem antisymmetric_inv[simp]:
  !R. antisymmetric (inv R) = antisymmetric R
Proof
  SRW_TAC [][antisymmetric_def, inv_DEF] THEN PROVE_TAC []
QED

Theorem transitive_inv[simp]:
  !R. transitive (inv R) = transitive R
Proof
  SIMP_TAC bool_ss [inv_DEF, transitive_def] THEN MESON_TAC []
QED

val symmetric_inv_identity = store_thm(
  "symmetric_inv_identity",
  ``!R. symmetric R ==> (inv R = R)``,
  SIMP_TAC bool_ss [inv_DEF, symmetric_def, FUN_EQ_THM]);

val equivalence_inv_identity = store_thm(
  "equivalence_inv_identity",
  ``!R. equivalence R ==> (inv R = R)``,
  SIMP_TAC bool_ss [equivalence_def, symmetric_inv_identity]);

(* ----------------------------------------------------------------------
    properties of relations, and set-like operations on relations from
    Lockwood Morris
  ---------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------
    Involutions (functions whose square is the identity)
  ---------------------------------------------------------------------- *)


val INVOL_DEF = new_definition(
  "INVOL_DEF",
  ``INVOL (f:'z->'z) = (f o f = I)``);

val INVOL = store_thm(
  "INVOL",
  ``!f:'z->'z. INVOL f = (!x. f (f x) = x)``,
  SRW_TAC [] [FUN_EQ_THM, INVOL_DEF]);

val INVOL_ONE_ONE = store_thm (
  "INVOL_ONE_ONE",
  ``!f:'z->'z. INVOL f ==> (!a b. (f a = f b) = (a = b))``,
  PROVE_TAC [INVOL]);

val INVOL_ONE_ENO = store_thm (
  "INVOL_ONE_ENO",
  ``!f:'z->'z. INVOL f ==> (!a b. (f a = b) = (a = f b))``,
  PROVE_TAC [INVOL]);

(* logical negation is an involution. *)
val NOT_INVOL = store_thm (
  "NOT_INVOL",
  ``INVOL (~)``,
  REWRITE_TAC [INVOL, NOT_CLAUSES]);

(* ----------------------------------------------------------------------
    Idempotent functions are those where f o f = f
   ---------------------------------------------------------------------- *)

val IDEM_DEF = new_definition(
  "IDEM_DEF",
  ``IDEM (f:'z->'z) = (f o f = f)``);

val IDEM = store_thm (
  "IDEM",
  ``!f:'z->'z. IDEM f = (!x. f (f x) = f x)``,
  SRW_TAC [][IDEM_DEF, FUN_EQ_THM]);

(* set up Id as a synonym for equality... *)
Overload Id = “(=)”

(*  but prefer = as the printing form when with two arguments *)
Overload "=" = “(=)”

(* code below even sets things up so that Id is preferred printing form when
   an equality term does not have two arguments.  It causes grief in
   parsing though - another project for the future maybe.
val _ = remove_termtok {term_name = "=", tok = "="}
val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 2)),
                   fixity = Infix(NONASSOC, 100),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [HardSpace 1, TOK "=", BreakSpace(1,0)],
                   term_name = "Id"}
*)

(* inv is an involution, which we know from theorem inv_inv above *)
val inv_INVOL = store_thm(
  "inv_INVOL",
  ``INVOL inv``,
  REWRITE_TAC [INVOL, inv_inv]);

(* ----------------------------------------------------------------------
    composition of two relations, written O (Isabelle/HOL notation)
   ---------------------------------------------------------------------- *)

(* This way 'round by analogy with function composition, where the
   second argument to composition acts on the "input" first.  This is also
   consistent with the way this constant is defined in Isabelle/HOL. *)
val O_DEF = new_definition(
  "O_DEF",
  ``(O) R1 R2 (x:'g) (z:'k) = ?y:'h. R2 x y /\ R1 y z``);
val _ = set_fixity "O" (Infixr 800)
val _ = Unicode.unicode_version {u = UTF8.chr 0x2218 ^ UnicodeChars.sub_r,
                                 tmnm = "O"}
val _ = TeX_notation { hol = UTF8.chr 0x2218 ^ UnicodeChars.sub_r,
                       TeX = ("\\HOLTokenRCompose{}", 1) }

val inv_O = store_thm(
  "inv_O",
  ``!R R'. inv (R O R') = inv R' O inv R``,
  SRW_TAC [][FUN_EQ_THM, O_DEF, inv_DEF] THEN PROVE_TAC []);

(* ----------------------------------------------------------------------
    relational inclusion, analog of SUBSET
   ---------------------------------------------------------------------- *)

val RSUBSET = new_definition(
  "RSUBSET",
  ``(RSUBSET) R1 R2 = !x y. R1 x y ==> R2 x y``);
val _ = set_fixity "RSUBSET" (Infix(NONASSOC, 450));
val _ = OpenTheoryMap.OpenTheory_const_name
          {const={Thy="relation",Name="RSUBSET"},
           name=(["Relation"],"subrelation")}
val _ = Unicode.unicode_version {u = UnicodeChars.subset ^ UnicodeChars.sub_r,
                                 tmnm = "RSUBSET"}
val _ = TeX_notation { hol = UnicodeChars.subset ^ UnicodeChars.sub_r,
                       TeX = ("\\HOLTokenRSubset{}", 1) }

val irreflexive_RSUBSET = store_thm(
  "irreflexive_RSUBSET",
  ``!R1 R2. irreflexive R2 /\ R1 RSUBSET R2 ==> irreflexive R1``,
  SRW_TAC [][irreflexive_def, RSUBSET] THEN PROVE_TAC []);

(* ----------------------------------------------------------------------
    relational union
   ---------------------------------------------------------------------- *)

val RUNION = new_definition(
  "RUNION",
  ``(RUNION) R1 R2 x y <=> R1 x y \/ R2 x y``);
val _ = set_fixity "RUNION" (Infixl 500)
val _ = OpenTheoryMap.OpenTheory_const_name
          {const={Thy="relation",Name="RUNION"},name=(["Relation"],"union")}

val RUNION_COMM = store_thm(
  "RUNION_COMM",
  ``R1 RUNION R2 = R2 RUNION R1``,
  SRW_TAC [][RUNION, FUN_EQ_THM] THEN PROVE_TAC []);

val RUNION_ASSOC = store_thm(
  "RUNION_ASSOC",
  ``R1 RUNION (R2 RUNION R3) = (R1 RUNION R2) RUNION R3``,
  SRW_TAC [][RUNION, FUN_EQ_THM] THEN PROVE_TAC []);

val _ = Unicode.unicode_version {u = UnicodeChars.union ^ UnicodeChars.sub_r,
                                 tmnm = "RUNION"}
val _ = TeX_notation { hol = UnicodeChars.union ^ UnicodeChars.sub_r,
                       TeX = ("\\HOLTokenRUnion{}", 1) }

(* ----------------------------------------------------------------------
    relational intersection
   ---------------------------------------------------------------------- *)

val RINTER = new_definition(
  "RINTER",
  ``(RINTER) R1 R2 x y <=> R1 x y /\ R2 x y``);
val _ = set_fixity "RINTER" (Infixl 600)
val _ = OpenTheoryMap.OpenTheory_const_name
          {const={Thy="relation",Name="RINTER"},name=(["Relation"],"intersect")}
val _ = Unicode.unicode_version {u = UnicodeChars.inter ^ UnicodeChars.sub_r,
                                 tmnm = "RINTER"}
val _ = TeX_notation { hol = UnicodeChars.inter ^ UnicodeChars.sub_r,
                       TeX = ("\\HOLTokenRInter{}", 1) }

val RINTER_COMM = store_thm(
  "RINTER_COMM",
  ``R1 RINTER R2 = R2 RINTER R1``,
  SRW_TAC [][RINTER, FUN_EQ_THM] THEN PROVE_TAC []);

val RINTER_ASSOC = store_thm(
  "RINTER_ASSOC",
  ``R1 RINTER (R2 RINTER R3) = (R1 RINTER R2) RINTER R3``,
  SRW_TAC [][RINTER, FUN_EQ_THM] THEN PROVE_TAC []);

val antisymmetric_RINTER = Q.store_thm(
  "antisymmetric_RINTER",
  `(antisymmetric R1 ==> antisymmetric (R1 RINTER R2)) /\
   (antisymmetric R2 ==> antisymmetric (R1 RINTER R2))`,
  SRW_TAC [][antisymmetric_def,RINTER]);
val _ = export_rewrites ["antisymmetric_RINTER"]

val transitive_RINTER = Q.store_thm(
  "transitive_RINTER",
  `transitive R1 /\ transitive R2 ==> transitive (R1 RINTER R2)`,
  SRW_TAC [SatisfySimps.SATISFY_ss][transitive_def,RINTER]);
val _ = export_rewrites ["transitive_RINTER"]

Theorem RTC_RINTER:
  !R1 R2 x y. RTC (R1 RINTER R2) x y ==> ((RTC R1) RINTER (RTC R2)) x y
Proof
  ntac 2 gen_tac >>
  match_mp_tac RTC_INDUCT >>
  asm_simp_tac(srw_ss())[RINTER] >>
  METIS_TAC[RTC_CASES1]
QED

(* ----------------------------------------------------------------------
    relational complement
   ---------------------------------------------------------------------- *)

val RCOMPL = new_definition(
  "RCOMPL",
  ``RCOMPL R x y = ~R x y``);

(* ----------------------------------------------------------------------
    theorems about reflexive, symmetric and transitive predicates in
    terms of particular relational-subsets
   ---------------------------------------------------------------------- *)

val reflexive_Id_RSUBSET = store_thm(
  "reflexive_Id_RSUBSET",
  ``!R. reflexive R = (Id RSUBSET R)``,
  SRW_TAC [][RSUBSET, reflexive_def]);

val symmetric_inv_RSUBSET = store_thm(
  "symmetric_inv_RSUBSET",
  ``symmetric R = (inv R RSUBSET R)``,
  SRW_TAC [][symmetric_def, inv_DEF, RSUBSET] THEN PROVE_TAC []);

val transitive_O_RSUBSET = store_thm(
  "transitive_O_RSUBSET",
  ``transitive R = (R O R RSUBSET R)``,
  SRW_TAC [][transitive_def, O_DEF, RSUBSET] THEN PROVE_TAC []);

(* ----------------------------------------------------------------------
    various sorts of orders
   ---------------------------------------------------------------------- *)

val PreOrder = new_definition(
  "PreOrder",
  ``PreOrder R <=> reflexive R /\ transitive R``);

(* The following definition follows Rob Arthan's idea of staying mum,
   for the most general notion of (partial) order, about whether the
   relation is to be reflexive, irreflexive, or something in
   between. *)

val Order = new_definition(
  "Order",
  ``Order (Z:'g->'g->bool) <=> antisymmetric Z /\ transitive Z``);

val WeakOrder = new_definition(
  "WeakOrder",
  ``WeakOrder (Z:'g->'g->bool) <=>
                       reflexive Z /\ antisymmetric Z /\ transitive Z``);

val StrongOrder = new_definition(
  "StrongOrder",
  ``StrongOrder (Z:'g->'g->bool) <=> irreflexive Z /\ transitive Z``);

val irrefl_trans_implies_antisym = store_thm(
  "irrefl_trans_implies_antisym",
  ``!R. irreflexive R /\ transitive R ==> antisymmetric R``,
  SRW_TAC [][antisymmetric_def, transitive_def, irreflexive_def] THEN
  METIS_TAC []);

val StrongOrd_Ord = store_thm(
  "StrongOrd_Ord",
  ``!R. StrongOrder R ==> Order R``,
  SRW_TAC [][StrongOrder, Order, irrefl_trans_implies_antisym]);

val WeakOrd_Ord = store_thm(
  "WeakOrd_Ord",
  ``!R. WeakOrder R ==> Order R``,
  SRW_TAC [][WeakOrder, Order]);

val WeakOrder_EQ = store_thm(
  "WeakOrder_EQ",
  ``!R. WeakOrder R ==> !y z. (y = z) <=> R y z /\ R z y``,
  SRW_TAC [][WeakOrder, reflexive_def, antisymmetric_def] THEN PROVE_TAC []);

val RSUBSET_ANTISYM = store_thm(
  "RSUBSET_ANTISYM",
  ``!R1 R2. R1 RSUBSET R2 /\ R2 RSUBSET R1 ==> (R1 = R2)``,
  SRW_TAC [][RSUBSET, FUN_EQ_THM] THEN PROVE_TAC []);

val RSUBSET_antisymmetric = store_thm(
  "RSUBSET_antisymmetric",
  ``antisymmetric (RSUBSET)``,
  REWRITE_TAC [antisymmetric_def, RSUBSET_ANTISYM]);

val RSUBSET_WeakOrder = store_thm(
  "RSUBSET_WeakOrder",
  ``WeakOrder (RSUBSET)``,
  SRW_TAC [][WeakOrder, reflexive_def, antisymmetric_def, transitive_def,
             RSUBSET, FUN_EQ_THM] THEN
  PROVE_TAC []);

val EqIsBothRSUBSET = save_thm(
  "EqIsBothRSUBSET",
  MATCH_MP WeakOrder_EQ RSUBSET_WeakOrder)
(* |- !y z. (y = z) = y RSUBSET z /\ z RSUBSET y *)

(* ----------------------------------------------------------------------
    STRORD makes an order strict (or "strong")
   ---------------------------------------------------------------------- *)

val STRORD = new_definition(
  "STRORD",
  ``STRORD R a b <=> R a b /\ ~(a = b)``);

val STRORD_AND_NOT_Id = store_thm(
  "STRORD_AND_NOT_Id",
  ``STRORD R = R RINTER (RCOMPL Id)``,
  SRW_TAC [][STRORD, RINTER, RCOMPL, FUN_EQ_THM]);

(* the corresponding "UNSTRORD", which makes an order weak is just RC *)

val RC_OR_Id = store_thm(
  "RC_OR_Id",
  ``RC R = R RUNION Id``,
  SRW_TAC [][RC_DEF, RUNION, FUN_EQ_THM] THEN PROVE_TAC []);

val RC_Weak = store_thm(
  "RC_Weak",
  ``Order R = WeakOrder (RC R)``,
  SRW_TAC [][Order, WeakOrder, EQ_IMP_THM, transitive_RC] THEN
  FULL_SIMP_TAC (srw_ss()) [transitive_def, RC_DEF, antisymmetric_def] THEN
  PROVE_TAC []);

val STRORD_Strong = store_thm(
  "STRORD_Strong",
  ``!R. Order R = StrongOrder (STRORD R)``,
  SRW_TAC [][Order, StrongOrder, STRORD, antisymmetric_def, transitive_def,
             irreflexive_def] THEN PROVE_TAC []);

val STRORD_RC = store_thm(
  "STRORD_RC",
  ``!R. StrongOrder R ==> (STRORD (RC R) = R)``,
  SRW_TAC [][StrongOrder, STRORD, RC_DEF, irreflexive_def, antisymmetric_def,
             transitive_def, FUN_EQ_THM] THEN PROVE_TAC []);

val RC_STRORD = store_thm(
  "RC_STRORD",
  ``!R. WeakOrder R ==> (RC (STRORD R) = R)``,
  SRW_TAC [][WeakOrder, STRORD, RC_DEF, reflexive_def, antisymmetric_def,
             transitive_def, FUN_EQ_THM] THEN PROVE_TAC []);

val IDEM_STRORD = store_thm(
  "IDEM_STRORD",
  ``IDEM STRORD``,
  SRW_TAC [][STRORD, IDEM, FUN_EQ_THM] THEN PROVE_TAC []);

val IDEM_RC = store_thm(
  "IDEM_RC",
  ``IDEM RC``,
  SRW_TAC [][IDEM, RC_IDEM]);

val IDEM_SC = store_thm(
  "IDEM_SC",
  ``IDEM SC``,
  SRW_TAC [][IDEM, SC_IDEM]);

val IDEM_TC = store_thm(
  "IDEM_TC",
  ``IDEM TC``,
  SRW_TAC [][IDEM, TC_IDEM]);

val IDEM_RTC = store_thm(
  "IDEM_RTC",
  ``IDEM RTC``,
  SRW_TAC [][IDEM, RTC_IDEM]);

val trichotomous_STRORD = store_thm(
  "trichotomous_STRORD",
  ``trichotomous (STRORD R) <=> trichotomous R``,
  SRW_TAC [][STRORD, trichotomous] THEN METIS_TAC[]);
val _ = export_rewrites ["trichotomous_STRORD"]

val trichotomous_RC = store_thm(
  "trichotomous_RC",
  ``trichotomous (RC R) <=> trichotomous R``,
  SRW_TAC [][RC_DEF, trichotomous] THEN METIS_TAC[]);
val _ = export_rewrites ["trichotomous_RC"]

(* ----------------------------------------------------------------------
    We may define notions of linear (i.e., total) order, but in the
    absence of numbers I don't see much to prove about them.
   ---------------------------------------------------------------------- *)

val LinearOrder = new_definition(
  "LinearOrder",
  ``LinearOrder (R:'a->'a->bool) <=> Order R /\ trichotomous R``);

val StrongLinearOrder = new_definition(
  "StrongLinearOrder",
  ``StrongLinearOrder (R:'a->'a->bool) <=> StrongOrder R /\ trichotomous R``);

val WeakLinearOrder = new_definition(
  "WeakLinearOrder",
  ``WeakLinearOrder (R:'a->'a->bool) <=> WeakOrder R /\ trichotomous R``);

val WeakLinearOrder_dichotomy = store_thm(
  "WeakLinearOrder_dichotomy",
   ``!R:'a->'a->bool. WeakLinearOrder R <=>
                      WeakOrder R /\ (!a b. R a b \/ R b a)``,
   SRW_TAC [][WeakLinearOrder, trichotomous] THEN
   PROVE_TAC [WeakOrder_EQ]);

(* ----------------------------------------------------------------------
    other stuff (inspired by Isabelle's Relation theory)
   ---------------------------------------------------------------------- *)

val diag_def = new_definition(
  "diag_def",
  ``diag A x y <=> (x = y) /\ x IN A``);

(* properties of O *)

val O_ASSOC = store_thm(
  "O_ASSOC",
  ``R1 O (R2 O R3) = (R1 O R2) O R3``,
  SRW_TAC [][O_DEF, FUN_EQ_THM] THEN PROVE_TAC []);

val Id_O = store_thm(
  "Id_O",
  ``Id O R = R``,
  SRW_TAC [][O_DEF, FUN_EQ_THM])
val _ = export_rewrites ["Id_O"]

val O_Id = store_thm(
  "O_Id",
  ``R O Id = R``,
  SRW_TAC [][O_DEF, FUN_EQ_THM]);
val _ = export_rewrites ["O_Id"]

val O_MONO = store_thm(
  "O_MONO",
  ``R1 RSUBSET R2 /\ S1 RSUBSET S2 ==> (R1 O S1) RSUBSET (R2 O S2)``,
  SRW_TAC [][RSUBSET, O_DEF] THEN PROVE_TAC []);

val inv_Id = store_thm(
  "inv_Id",
  ``inv Id = Id``,
  SRW_TAC [][FUN_EQ_THM, inv_DEF, EQ_SYM_EQ]);

val inv_diag = store_thm(
  "inv_diag",
  ``inv (diag A) = diag A``,
  SRW_TAC [][FUN_EQ_THM, inv_DEF, diag_def] THEN PROVE_TAC []);

(* domain of a relation *)
(* if I just had UNIONs and the like around, I could prove great things like
     RDOM (R RUNION R') = RDOM R UNION RDOM R'
   I can still prove x IN RDOM (R1 RUNION R2) = x IN RDOM R1 \/ x IN RDOM R2
   though.
*)
val RDOM_DEF = new_definition(
  "RDOM_DEF",
  ``RDOM R x = ?y. R x y``);

val IN_RDOM = store_thm(
  "IN_RDOM",
  ``x IN RDOM R <=> ?y. R x y``,
  SRW_TAC [][RDOM_DEF, IN_DEF]);

(* range of a relation *)
val RRANGE_DEF = new_definition(
  "RRANGE",
  ``RRANGE R y = ?x. R x y``);

val IN_RRANGE = store_thm(
  "IN_RRANGE",
  ``y IN RRANGE R <=> ?x. R x y``,
  SRW_TAC [][RRANGE_DEF, IN_DEF]);

val IN_RDOM_RUNION = store_thm(
  "IN_RDOM_RUNION",
  ``x IN RDOM (R1 RUNION R2) <=> x IN RDOM R1 \/ x IN RDOM R2``,
  SIMP_TAC (srw_ss()) [RDOM_DEF, RUNION, boolTheory.IN_DEF, EXISTS_OR_THM]);

(* top and bottom elements of RSUBSET lattice *)
val RUNIV = new_definition(
  "RUNIV",
  ``RUNIV x y = T``);
val _ = export_rewrites ["RUNIV"]
val _ = OpenTheoryMap.OpenTheory_const_name
          {const={Thy="relation",Name="RUNIV"},name=(["Relation"],"universe")}
val _ = Unicode.unicode_version {
  u = UnicodeChars.universal_set ^ UnicodeChars.sub_r,
  tmnm = "RUNIV"}


val RUNIV_SUBSET = store_thm(
  "RUNIV_SUBSET",
  ``(RUNIV RSUBSET R <=> (R = RUNIV)) /\
    (R RSUBSET RUNIV)``,
  SRW_TAC [][RSUBSET, FUN_EQ_THM]);
val _ = export_rewrites ["RUNIV_SUBSET"]

val REMPTY_SUBSET = store_thm(
  "REMPTY_SUBSET",
  ``REMPTY RSUBSET R /\
    (R RSUBSET REMPTY <=> (R = REMPTY))``,
  SRW_TAC [][RSUBSET, FUN_EQ_THM]);
val _ = export_rewrites ["REMPTY_SUBSET"]

(* ----------------------------------------------------------------------
    Restrictions on relations

    In theory there are 3 flavours of restriction, each taking a relation
    and a set.

    1. restricting the domain of a relation (perhaps the most natural,
       gets to be RRESTRICT below)
    2. restricting the range of a relation
    3. restricting both, forcing the relation to be 'a -> 'a -> bool

    In addition, it might be nice to have notation for removal of just
    one element in each flavour, which can be expressed as restriction
    to the complement of the singleton set containing that element.

   ---------------------------------------------------------------------- *)

val RRESTRICT_DEF = new_definition(
  "RRESTRICT_DEF",
  ``RRESTRICT R s (x:'a) (y:'b) <=> R x y /\ x IN s``);
val _ = export_rewrites ["RRESTRICT_DEF"]

val IN_RDOM_RRESTRICT = store_thm(
  "IN_RDOM_RRESTRICT",
  ``x IN RDOM (RRESTRICT (R:'a -> 'b -> bool) s) <=> x IN RDOM R /\ x IN s``,
  SIMP_TAC bool_ss [boolTheory.IN_DEF, RDOM_DEF, RRESTRICT_DEF] THEN
  METIS_TAC[])
val _ = export_rewrites ["IN_RDOM_RRESTRICT"]

val RDOM_DELETE_DEF = new_definition(
  "RDOM_DELETE_DEF",
  ``RDOM_DELETE R x u v <=> R u v /\ u <> x``);
val _ = export_rewrites ["RDOM_DELETE_DEF"]

(* this syntax is compatible (easily confused) with that for finite maps *)
val _ = set_fixity "\\\\" (Infixl 600)
Overload "\\\\" =  “RDOM_DELETE”

val IN_RDOM_DELETE = store_thm(
  "IN_RDOM_DELETE",
  ``x IN RDOM (R \\ k) <=> x IN RDOM R /\ x <> k``,
  SIMP_TAC bool_ss [boolTheory.IN_DEF, RDOM_DEF, RDOM_DELETE_DEF] THEN
  METIS_TAC[]);
val _ = export_rewrites ["IN_RDOM_DELETE"]




(*===========================================================================*)
(* Some notions from Term Rewriting Systems, leading to simple results about *)
(* things like confluence and normalisation                                  *)
(*===========================================================================*)

val diamond_def = new_definition(
  "diamond_def",
  ``diamond (R:'a->'a->bool) = !x y z. R x y /\ R x z ==> ?u. R y u /\ R z u``)

val rcdiamond_def = new_definition( (* reflexive closure half diamond *)
  "rcdiamond_def",
  ``rcdiamond (R:'a->'a->bool) =
      !x y z. R x y /\ R x z ==> ?u. RC R y u /\ RC R z u``);

val CR_def = new_definition( (* Church-Rosser *)
  "CR_def",
  ``CR R = diamond (RTC R)``);

val WCR_def = new_definition( (* weakly Church-Rosser *)
  "WCR_def",
  ``WCR R = !x y z. R x y /\ R x z ==> ?u. RTC R y u /\ RTC R z u``);

val SN_def = new_definition( (* strongly normalising *)
  "SN_def",
  ``SN R = WF (inv R)``);

val nf_def = new_definition( (* normal-form *)
  "nf_def",
  ``nf R x = !y. ~R x y``)

(* results *)

(* that proving rcdiamond R is equivalent to establishing diamond (RC R) *)
val rcdiamond_diamond = store_thm(
  "rcdiamond_diamond",
  ``!R. rcdiamond R = diamond (RC R)``,
  SRW_TAC [][rcdiamond_def, diamond_def, RC_DEF] THEN
  METIS_TAC []); (* PROVE_TAC can't cope with this *)

val diamond_RC_diamond = store_thm(
  "diamond_RC_diamond",
  ``!R. diamond R ==> diamond (RC R)``,
  SRW_TAC [][diamond_def, RC_DEF] THEN METIS_TAC []);

val diamond_TC_diamond = store_thm(
  "diamond_TC_diamond",
  ``!R. diamond R ==> diamond (TC R)``,
  REWRITE_TAC [diamond_def] THEN GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC
        `!x y. TC R x y ==> !z. TC R x z ==> ?u. TC R y u /\ TC R z u` THEN1
        METIS_TAC [] THEN
  HO_MATCH_MP_TAC TC_INDUCT_LEFT1 THEN
  Q.SUBGOAL_THEN
    `!x y. TC R x y ==> !z. R x z ==> ?u. TC R y u /\ TC R z u`
    ASSUME_TAC
  THENL [
    HO_MATCH_MP_TAC TC_INDUCT_LEFT1 THEN PROVE_TAC [TC_RULES],
    ALL_TAC (* METIS_TAC very slow in comparison on line above *)
  ] THEN PROVE_TAC [TC_RULES]);

val RTC_eq_TCRC = prove(
  ``RTC R = TC (RC R)``,
  REWRITE_TAC [TC_RC_EQNS]);

val establish_CR = store_thm(
  "establish_CR",
  ``!R. (rcdiamond R ==> CR R) /\ (diamond R ==> CR R)``,
  REWRITE_TAC [CR_def, RTC_eq_TCRC] THEN
  PROVE_TAC [diamond_RC_diamond, rcdiamond_diamond, diamond_TC_diamond]);

fun (g by tac) =
    Q.SUBGOAL_THEN g STRIP_ASSUME_TAC THEN1 tac

val Newmans_lemma = store_thm(
  "Newmans_lemma",
  ``!R. WCR R /\ SN R ==> CR R``,
  REPEAT STRIP_TAC THEN
  `WF (TC (inv R))` by PROVE_TAC [WF_TC, SN_def] THEN
  REWRITE_TAC [CR_def, diamond_def] THEN
  POP_ASSUM (HO_MATCH_MP_TAC o MATCH_MP WF_INDUCTION_THM) THEN
  SRW_TAC [][inv_MOVES_OUT, inv_DEF] THEN
  `(x = y) \/ ?y1. R x y1 /\ RTC R y1 y` by PROVE_TAC [RTC_CASES1] THENL [
    SRW_TAC [][] THEN PROVE_TAC [RTC_RULES],
    ALL_TAC
  ] THEN
  `(x = z) \/ ?z1. R x z1 /\ RTC R z1 z` by PROVE_TAC [RTC_CASES1] THENL [
    SRW_TAC [][] THEN PROVE_TAC [RTC_RULES],
    ALL_TAC
  ] THEN
  `?x0. RTC R y1 x0 /\ RTC R z1 x0` by PROVE_TAC [WCR_def] THEN
  `TC R x y1 /\ TC R x z1` by PROVE_TAC [TC_RULES] THEN
  `?y2. RTC R y y2 /\ RTC R x0 y2` by PROVE_TAC [] THEN
  `?z2. RTC R z z2 /\ RTC R x0 z2` by PROVE_TAC [] THEN
  `TC R x x0` by PROVE_TAC [EXTEND_RTC_TC] THEN
  PROVE_TAC [RTC_RTC]);

Theorem RUNION_RTC_MONOTONE :
    !R1 x y. RTC R1 x y ==> !R2. RTC (R1 RUNION R2) x y
Proof
  GEN_TAC THEN HO_MATCH_MP_TAC RTC_INDUCT THEN
  PROVE_TAC [RTC_RULES, RUNION]
QED

Theorem RTC_RUNION :
    !R1 R2. RTC (RTC R1 RUNION RTC R2) = RTC (R1 RUNION R2)
Proof
  REPEAT GEN_TAC THEN
  Q_TAC SUFF_TAC
    `(!x y. RTC (RTC R1 RUNION RTC R2) x y ==> RTC (R1 RUNION R2) x y) /\
     (!x y. RTC (R1 RUNION R2) x y ==> RTC (RTC R1 RUNION RTC R2) x y)` THEN1
    (SIMP_TAC (srw_ss()) [FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM] THEN
     PROVE_TAC []) THEN CONJ_TAC
  THEN HO_MATCH_MP_TAC RTC_INDUCT THENL [
    CONJ_TAC THENL [
      PROVE_TAC [RTC_RULES],
      MAP_EVERY Q.X_GEN_TAC [`x`,`y`,`z`] THEN REPEAT STRIP_TAC THEN
      `RTC R1 x y \/ RTC R2 x y` by PROVE_TAC [RUNION] THEN
      PROVE_TAC [RUNION_RTC_MONOTONE, RTC_RTC, RUNION_COMM]
    ],
    CONJ_TAC THENL [
      PROVE_TAC [RTC_RULES],
      MAP_EVERY Q.X_GEN_TAC [`x`,`y`,`z`] THEN REPEAT STRIP_TAC THEN
      `R1 x y \/ R2 x y` by PROVE_TAC [RUNION] THEN
      PROVE_TAC [RTC_RULES, RUNION]
    ]
  ]
QED

(* ‘RINSERT’ inserts one more element into an existing relation *)
val RINSERT = new_definition ("RINSERT",
   “RINSERT R a b = \x y. R x y \/ (x = a /\ y = b)”);

Theorem RINSERT_IDEM :
    !R a b. (RINSERT R a b) a b
Proof
    SRW_TAC [] [RINSERT]
QED

Theorem RSUBSET_RINSERT :
    !R a b. R RSUBSET (RINSERT R a b)
Proof
    SRW_TAC [] [RSUBSET, RINSERT]
QED

val _ = export_theory();
