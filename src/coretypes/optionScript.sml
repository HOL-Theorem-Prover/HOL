(* =======================================================================*)
(* FILE         : optionScript.sml                                        *)
(* DESCRIPTION  : Creates a theory of SML like options                    *)
(* WRITES FILES : option.th                                               *)
(*                                                                        *)
(* AUTHOR       : (c) D. Syme 1988                                        *)
(* DATE         : 95.04.25                                                *)
(* REVISED      : (Konrad Slind) Oct 9.97 to eliminate usage of           *)
(*                recursive types package. Follows the development of     *)
(*                Elsa Gunter in her formalization of partial functions.  *)
(*                                                                        *)
(*                Dec.1998, in order to fit in with Datatype scheme       *)
(* =======================================================================*)

open HolKernel Parse boolLib metisLib;

(*---------------------------------------------------------------------------
     Make sure that sumTheory and oneTheory is loaded.
 ---------------------------------------------------------------------------*)

local open sumTheory oneTheory relationTheory in end;
open simpLib BasicProvers

(* ---------------------------------------------------------------------*)
(* Create the new theory                                                *)
(* ---------------------------------------------------------------------*)

val _ = new_theory "option";

(*---------------------------------------------------------------------------*
 * Define the new type. The representing type is 'a + one. The development   *
 * is adapted from Elsa Gunter's development of an option type in her        *
 * holML formalization (she called it "lift").                               *
 *---------------------------------------------------------------------------*)

val option_TY_DEF =
 new_type_definition
  ("option",
   prove(Term`?x:'a + one. (\x.T) x`,
          BETA_TAC THEN EXISTS_TAC“x:'a + one” THEN ACCEPT_TAC TRUTH));

local
  open OpenTheoryMap
  val ns = ["Data","Option"]
  val _ = OpenTheory_tyop_name{tyop={Thy="option",Tyop="option"},name=(ns,"option")}
in
  fun ot0 x y = OpenTheory_const_name{const={Thy="option",Name=x},name=(ns,y)}
  fun ot x = ot0 x x
end

(*---------------------------------------------------------------------------*
 *  val option_REP_ABS_DEF =                                                 *
 *     |- (!a. option_ABS (option_REP a) = a) /\                             *
 *        (!r. (\x. T) r = option_REP (option_ABS r) = r)                    *
 *---------------------------------------------------------------------------*)

val option_REP_ABS_DEF =
     define_new_type_bijections
     {name = "option_REP_ABS_DEF",
      ABS = "option_ABS", REP = "option_REP",
      tyax = option_TY_DEF};

fun reduce thm = REWRITE_RULE[](BETA_RULE thm);

(*---------------------------------------------------------------------------*
 * option_ABS_ONE_ONE = |- !r r'. (option_ABS r = option_ABS r') = r = r'    *
 * option_ABS_ONTO = |- !a. ?r. a = option_ABS r                             *
 * option_REP_ONE_ONE = |- !a a'. (option_REP a = option_REP a') = a = a'    *
 * option_REP_ONTO = |- !r. ?a. r = option_REP a                             *
 *---------------------------------------------------------------------------*)

val option_ABS_ONE_ONE = reduce(prove_abs_fn_one_one option_REP_ABS_DEF);
val option_ABS_ONTO    = reduce(prove_abs_fn_onto option_REP_ABS_DEF);
val option_REP_ONE_ONE = prove_rep_fn_one_one option_REP_ABS_DEF;
val option_REP_ONTO    = reduce(prove_rep_fn_onto option_REP_ABS_DEF);

val SOME_DEF = new_definition("SOME_DEF",Term`!x. SOME x = option_ABS(INL x)`);
val NONE_DEF = new_definition("NONE_DEF",Term`NONE = option_ABS(INR one)`);
val _ = ot0 "SOME" "some"
val _ = ot0 "NONE" "none"

val option_Axiom = store_thm (
  "option_Axiom",
  Term`!e f:'a -> 'b. ?fn. (fn NONE = e) /\ (!x. fn (SOME x) = f x)`,
  REPEAT GEN_TAC THEN
  PURE_REWRITE_TAC[SOME_DEF,NONE_DEF] THEN
  STRIP_ASSUME_TAC
     (BETA_RULE
        (ISPECL [“\x. f x”, “\x:one.(e:'b)”]
         (INST_TYPE [Type.beta |-> Type`:one`]
          sumTheory.sum_Axiom))) THEN
  EXISTS_TAC “\x:'a option. h(option_REP x):'b” THEN BETA_TAC THEN
  ASM_REWRITE_TAC[reduce option_REP_ABS_DEF]);

val option_induction = store_thm (
  "option_induction",
  Term`!P. P NONE /\ (!a. P (SOME a)) ==> !x. P x`,
  GEN_TAC THEN PURE_REWRITE_TAC [SOME_DEF, NONE_DEF] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM (CONJUNCT1 option_REP_ABS_DEF)] THEN
  SPEC_TAC (Term`option_REP (x:'a option)`, Term`s:'a + one`) THEN
  HO_MATCH_MP_TAC sumTheory.sum_INDUCT THEN
  ONCE_REWRITE_TAC [oneTheory.one] THEN ASM_REWRITE_TAC []);

val option_nchotomy = save_thm(
  "option_nchotomy",
  prove_cases_thm option_induction
    |> hd
    |> CONV_RULE (RENAME_VARS_CONV ["opt"] THENC
                  BINDER_CONV (RAND_CONV (RENAME_VARS_CONV ["x"]))))

val [option_case_def] = Prim_rec.define_case_constant option_Axiom
val _ = ot0 "option_case" "case"
val _ = overload_on("case", ``option_CASE``)

Theorem FORALL_OPTION:
  (!opt. P opt) <=> P NONE /\ !x. P (SOME x)
Proof METIS_TAC [option_induction]
QED

Theorem EXISTS_OPTION:
  (?opt. P opt) = P NONE \/ ?x. P (SOME x)
Proof METIS_TAC [option_nchotomy]
QED

val SOME_11 = store_thm("SOME_11",
  Term`!x y :'a. (SOME x = SOME y) <=> (x=y)`,
  REWRITE_TAC [SOME_DEF,option_ABS_ONE_ONE,sumTheory.INR_INL_11]);
val _ = export_rewrites ["SOME_11"]

val (NOT_NONE_SOME,NOT_SOME_NONE) =
 let val thm = TAC_PROOF(([], Term`!x:'a. ~(NONE = SOME x)`),
                  REWRITE_TAC [SOME_DEF,NONE_DEF,
                               option_ABS_ONE_ONE,sumTheory.INR_neq_INL])
 in
   (save_thm("NOT_NONE_SOME", thm),
    save_thm("NOT_SOME_NONE", GSYM thm))
  end;
val _ = export_rewrites ["NOT_NONE_SOME"]
        (* only need one because simplifier automatically flips the equality
           for us *)


val OPTION_MAP_DEF = Prim_rec.new_recursive_definition
 {name="OPTION_MAP_DEF",
  rec_axiom=option_Axiom,
  def =
  Term`(OPTION_MAP (f:'a->'b) (SOME x) = SOME (f x)) /\
       (OPTION_MAP f NONE = NONE)`};
val _ = export_rewrites ["OPTION_MAP_DEF"]
val _ = computeLib.add_persistent_funs ["OPTION_MAP_DEF"]
val _ = ot0 "OPTION_MAP" "map"

val IS_SOME_DEF = Prim_rec.new_recursive_definition
  {name="IS_SOME_DEF",
   rec_axiom=option_Axiom,
   def = Term`(IS_SOME (SOME x) = T) /\ (IS_SOME NONE = F)`};
val _ = ot0 "IS_SOME" "isSome"

val IS_NONE_DEF = Prim_rec.new_recursive_definition {
  name = "IS_NONE_DEF",
  rec_axiom = option_Axiom,
  def = Term`(IS_NONE (SOME x) = F) /\ (IS_NONE NONE = T)`};
val _ = ot0 "IS_NONE" "isNone"

val THE_DEF = Prim_rec.new_recursive_definition
  {name="THE_DEF",
   rec_axiom=option_Axiom,
   def = Term `THE (SOME x) = x`};
val _ = ot0 "THE" "the"

val OPTION_MAP2_DEF = Q.new_definition(
  "OPTION_MAP2_DEF",
  `OPTION_MAP2 f x y =
     if IS_SOME x /\ IS_SOME y
     then SOME (f (THE x) (THE y))
     else NONE`);

val OPTION_JOIN_DEF = Prim_rec.new_recursive_definition
  {name = "OPTION_JOIN_DEF",
   rec_axiom = option_Axiom,
   def = Term`(OPTION_JOIN NONE = NONE) /\
              (OPTION_JOIN (SOME x) = x)`};
val _ = ot0 "OPTION_JOIN" "join"

val option_rws =
    [IS_SOME_DEF, THE_DEF, IS_NONE_DEF, option_nchotomy,
     NOT_NONE_SOME,NOT_SOME_NONE, SOME_11, option_case_def,
     OPTION_MAP_DEF, OPTION_JOIN_DEF];

val OPTION_MAP2_THM = Q.store_thm("OPTION_MAP2_THM",
  `(OPTION_MAP2 f (SOME x) (SOME y) = SOME (f x y)) /\
   (OPTION_MAP2 f (SOME x) NONE = NONE) /\
   (OPTION_MAP2 f NONE (SOME y) = NONE) /\
   (OPTION_MAP2 f NONE NONE = NONE)`,
  REWRITE_TAC (OPTION_MAP2_DEF::option_rws));
val _ = export_rewrites ["OPTION_MAP2_THM"];
val _ = overload_on("lift2", ``OPTION_MAP2``)
val _ = overload_on("OPTION_MAP2", ``OPTION_MAP2``)
val _ = computeLib.add_persistent_funs ["OPTION_MAP2_THM"]

val option_rws = OPTION_MAP2_THM::option_rws;

val ex1_rw = prove(Term`!x. (?y. x = y) /\ (?y. y = x)`,
   GEN_TAC THEN CONJ_TAC THEN EXISTS_TAC (Term`x`) THEN REFL_TAC);

fun OPTION_CASES_TAC t = STRUCT_CASES_TAC (ISPEC t option_nchotomy);

val IS_SOME_EXISTS = store_thm("IS_SOME_EXISTS",
  ``!opt. IS_SOME opt <=> ?x. opt = SOME x``,
  GEN_TAC THEN (Q_TAC OPTION_CASES_TAC`opt`) THEN
  SRW_TAC[][IS_SOME_DEF])

val IS_NONE_EQ_NONE = Q.store_thm(
  "IS_NONE_EQ_NONE",
  `!x. IS_NONE x = (x = NONE)`,
    GEN_TAC
    THEN OPTION_CASES_TAC “(x :'a option)”
    THEN ASM_REWRITE_TAC option_rws
);

val NOT_IS_SOME_EQ_NONE = Q.store_thm(
  "NOT_IS_SOME_EQ_NONE",
  `!x. ~(IS_SOME x) = (x = NONE)`,
    GEN_TAC
    THEN OPTION_CASES_TAC “(x :'a option)”
    THEN ASM_REWRITE_TAC option_rws
);

val IS_SOME_EQ_EXISTS = Q.prove(
 `!x. IS_SOME x = (?v. x = SOME v)`,
    GEN_TAC
    THEN OPTION_CASES_TAC “(x :'a option)”
    THEN ASM_REWRITE_TAC (ex1_rw::option_rws)
);


val IS_SOME_IMP_SOME_THE_CANCEL = Q.prove(
`!x:'a option. IS_SOME x ==> (SOME (THE x) = x)`,
    GEN_TAC
    THEN OPTION_CASES_TAC “(x :'a option)”
    THEN ASM_REWRITE_TAC option_rws
);

val option_case_ID = Q.store_thm(
  "option_case_ID",
  `!x:'a option. option_CASE x NONE SOME = x`,
    GEN_TAC
    THEN OPTION_CASES_TAC “(x :'a option)”
    THEN ASM_REWRITE_TAC option_rws
);

val IS_SOME_option_case_SOME = Q.prove(
`!x:'a option. IS_SOME x ==> (option_CASE x e SOME = x)`,
    GEN_TAC
    THEN OPTION_CASES_TAC “(x :'a option)”
    THEN ASM_REWRITE_TAC option_rws
);

val option_case_SOME_ID = Q.store_thm(
  "option_case_SOME_ID",
  `!x:'a option. (option_CASE x x SOME = x)`,
    GEN_TAC
    THEN OPTION_CASES_TAC “(x :'a option)”
    THEN ASM_REWRITE_TAC option_rws
);

val IS_SOME_option_case = Q.prove(
`!x:'a option. IS_SOME x ==> (option_CASE x e (f:'a->'b) = f (THE x))`,
    GEN_TAC
    THEN OPTION_CASES_TAC “(x :'a option)”
    THEN ASM_REWRITE_TAC option_rws
);


val IS_NONE_option_case = Q.prove(
`!x:'a option. IS_NONE x ==> (option_CASE x e f = (e:'b))`,
    GEN_TAC
    THEN OPTION_CASES_TAC “(x :'a option)”
    THEN ASM_REWRITE_TAC option_rws
);


val option_CLAUSES = save_thm("option_CLAUSES",
     LIST_CONJ ([SOME_11,THE_DEF,NOT_NONE_SOME,NOT_SOME_NONE]@
                (CONJUNCTS IS_SOME_DEF)@
                [IS_NONE_EQ_NONE,
                 NOT_IS_SOME_EQ_NONE,
                 IS_SOME_IMP_SOME_THE_CANCEL,
                 option_case_ID,
                 option_case_SOME_ID,
                 IS_NONE_option_case,
                 IS_SOME_option_case,
                 IS_SOME_option_case_SOME]@
                 CONJUNCTS option_case_def@
                 CONJUNCTS OPTION_MAP_DEF@
                 CONJUNCTS OPTION_JOIN_DEF));

val option_case_compute = Q.store_thm
("option_case_compute",
 `option_CASE (x:'a option) (e:'b) f =
  if IS_SOME x then f (THE x) else e`,
    OPTION_CASES_TAC “(x :'a option)”
    THEN ASM_REWRITE_TAC option_rws);

val IF_EQUALS_OPTION = store_thm(
  "IF_EQUALS_OPTION",
  ``(((if P then SOME x else NONE) = NONE) <=> ~P) /\
    (((if P then NONE else SOME x) = NONE) <=> P) /\
    (((if P then SOME x else NONE) = SOME y) <=> P /\ (x = y)) /\
    (((if P then NONE else SOME x) = SOME y) <=> ~P /\ (x = y))``,
  SRW_TAC [][]);
val _ = export_rewrites ["IF_EQUALS_OPTION"]

val IF_NONE_EQUALS_OPTION = store_thm(
  "IF_NONE_EQUALS_OPTION",
  ``(((if P then X else NONE) = NONE) <=> (P ==> IS_NONE X)) /\
    (((if P then NONE else X) = NONE) <=> (IS_SOME X ==> P)) /\
    (((if P then X else NONE) = SOME x) <=> P /\ (X = SOME x)) /\
    (((if P then NONE else X) = SOME x) <=> ~P /\ (X = SOME x))``,
  OPTION_CASES_TAC“X:'a option” THEN SRW_TAC [](option_rws));
val _ = export_rewrites ["IF_NONE_EQUALS_OPTION"]

(* ----------------------------------------------------------------------
    OPTION_MAP theorems
   ---------------------------------------------------------------------- *)

val OPTION_MAP_EQ_SOME = Q.store_thm(
  "OPTION_MAP_EQ_SOME",
  `!f (x:'a option) y.
         (OPTION_MAP f x = SOME y) = ?z. (x = SOME z) /\ (y = f z)`,
  REPEAT GEN_TAC THEN OPTION_CASES_TAC “x:'a option” THEN
  simpLib.SIMP_TAC boolSimps.bool_ss
    [SOME_11, NOT_NONE_SOME, NOT_SOME_NONE, OPTION_MAP_DEF] THEN
  mesonLib.MESON_TAC []);
val _ = export_rewrites ["OPTION_MAP_EQ_SOME"]

val OPTION_MAP_EQ_NONE = Q.store_thm(
  "OPTION_MAP_EQ_NONE",
  `!f x.  (OPTION_MAP f x = NONE) = (x = NONE)`,
  REPEAT GEN_TAC THEN OPTION_CASES_TAC “x:'a option” THEN
  REWRITE_TAC [option_CLAUSES]);

val OPTION_MAP_EQ_NONE_both_ways = Q.store_thm(
  "OPTION_MAP_EQ_NONE_both_ways",
  `((OPTION_MAP f x = NONE) = (x = NONE)) /\
   ((NONE = OPTION_MAP f x) = (x = NONE))`,
  REWRITE_TAC [OPTION_MAP_EQ_NONE] THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ])) THEN
  REWRITE_TAC [OPTION_MAP_EQ_NONE]);
val _ = export_rewrites ["OPTION_MAP_EQ_NONE_both_ways"]

val OPTION_MAP_COMPOSE = store_thm(
  "OPTION_MAP_COMPOSE",
  ``OPTION_MAP f (OPTION_MAP g (x:'a option)) = OPTION_MAP (f o g) x``,
  OPTION_CASES_TAC ``x:'a option`` THEN SRW_TAC [][]);

val OPTION_MAP_CONG = store_thm(
  "OPTION_MAP_CONG",
  ``!opt1 opt2 f1 f2.
      (opt1 = opt2) /\ (!x. (opt2 = SOME x) ==> (f1 x = f2 x)) ==>
      (OPTION_MAP f1 opt1 = OPTION_MAP f2 opt2)``,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  Q.SPEC_THEN `opt2` FULL_STRUCT_CASES_TAC option_nchotomy THEN
  REWRITE_TAC [OPTION_MAP_DEF, SOME_11] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC [SOME_11])
val _ = DefnBase.export_cong "OPTION_MAP_CONG"

val IS_SOME_MAP = Q.store_thm ("IS_SOME_MAP",
  `IS_SOME (OPTION_MAP f x) = IS_SOME (x : 'a option)`,
  OPTION_CASES_TAC “x:'a option” THEN
  REWRITE_TAC [IS_SOME_DEF, OPTION_MAP_DEF]) ;

(* and one about OPTION_JOIN *)

val OPTION_JOIN_EQ_SOME = Q.store_thm(
  "OPTION_JOIN_EQ_SOME",
  `!(x:'a option option) y. (OPTION_JOIN x = SOME y) = (x = SOME (SOME y))`,
  GEN_TAC THEN
  Q.SUBGOAL_THEN `(x = NONE) \/ (?z. x = SOME z)` STRIP_ASSUME_TAC THENL [
    MATCH_ACCEPT_TAC option_nchotomy,
    ALL_TAC,
    ALL_TAC
  ] THEN ASM_REWRITE_TAC option_rws THEN
  OPTION_CASES_TAC “z:'a option” THEN
  ASM_REWRITE_TAC option_rws);

(* and some about OPTION_MAP2 *)

val OPTION_MAP2_SOME = Q.store_thm(
  "OPTION_MAP2_SOME",
  `(OPTION_MAP2 f (o1:'a option) (o2:'b option) = SOME v) <=>
   (?x1 x2. (o1 = SOME x1) /\ (o2 = SOME x2) /\ (v = f x1 x2))`,
  OPTION_CASES_TAC “o1:'a option” THEN
  OPTION_CASES_TAC “o2:'b option” THEN
  SRW_TAC [][EQ_IMP_THM]);
val _ = export_rewrites["OPTION_MAP2_SOME"];

val OPTION_MAP2_NONE = Q.store_thm(
  "OPTION_MAP2_NONE",
  `(OPTION_MAP2 f (o1:'a option) (o2:'b option) = NONE) <=> (o1 = NONE) \/ (o2 = NONE)`,
  OPTION_CASES_TAC “o1:'a option” THEN
  OPTION_CASES_TAC “o2:'b option” THEN
  SRW_TAC [][]);
val _ = export_rewrites["OPTION_MAP2_NONE"];

val OPTION_MAP2_cong = store_thm("OPTION_MAP2_cong",
  ``!x1 x2 y1 y2 f1 f2.
       (x1 = x2) /\ (y1 = y2) /\
       (!x y. (x2 = SOME x) /\ (y2 = SOME y) ==> (f1 x y = f2 x y)) ==>
       (OPTION_MAP2 f1 x1 y1 = OPTION_MAP2 f2 x2 y2)``,
  SRW_TAC [][] THEN
  Q.SPEC_THEN `x1` FULL_STRUCT_CASES_TAC option_nchotomy THEN
  Q.ISPEC_THEN `y1` FULL_STRUCT_CASES_TAC option_nchotomy THEN
  SRW_TAC [][]);
val _ = DefnBase.export_cong "OPTION_MAP2_cong";

val OPTION_MAP_CASE = store_thm("OPTION_MAP_CASE",
  ``OPTION_MAP f (x:'a option) = option_CASE x NONE (SOME o f)``,
  OPTION_CASES_TAC “x:'a option” THEN
  REWRITE_TAC [combinTheory.o_THM, option_CLAUSES]) ;

(* similarly have
``OPTION_JOIN f = option_CASE x NONE I`` ;
``OPTION_BIND x f = option_CASE x NONE f`` ;
*)

(* ----------------------------------------------------------------------
    The Option Monad

    A monad with a zero (NONE)

     * OPTION_BIND        - monadic bind operation for options
                            nice syntax is
                              do
                                v <- opn1;
                                opn2
                              od
                            where opn2 may refer to v
     * OPTION_IGNORE_BIND - bind that ignores the passed parameter, with
                            nice syntax looking like
                              do
                                opn1 ;
                                opn2
                              od
     * OPTION_GUARD       - checks a predicate and either gives a
                            successful unit value, or failure (NONE)
                            nice syntax would be
                                do
                                  assert(some condition);
                                  ...
                                od
     * OPTION_CHOICE      - tries one operation, and if it fails, tries
                            the second.  Nice syntax would be opn1 ++ opn2

   ---------------------------------------------------------------------- *)

val OPTION_BIND_def = Prim_rec.new_recursive_definition
  {name="OPTION_BIND_def",
   rec_axiom=option_Axiom,
   def = Term`(OPTION_BIND NONE f = NONE) /\
              (OPTION_BIND (SOME x) f = f x)`}
val _= export_rewrites ["OPTION_BIND_def"]
val _ = computeLib.add_persistent_funs["OPTION_BIND_def"];

val OPTION_BIND_cong = Q.store_thm(
  "OPTION_BIND_cong",
  `!o1 o2 f1 f2.
     (o1:'a option = o2) /\ (!x. (o2 = SOME x) ==> (f1 x = f2 x)) ==>
     (OPTION_BIND o1 f1 = OPTION_BIND o2 f2)`,
  simpLib.SIMP_TAC (srw_ss()) [FORALL_OPTION]);
val _ = DefnBase.export_cong "OPTION_BIND_cong"

val OPTION_BIND_EQUALS_OPTION = Q.store_thm(
  "OPTION_BIND_EQUALS_OPTION",
  `((OPTION_BIND (p:'a option) f = NONE) <=>
       (p = NONE) \/ ?x. (p = SOME x) /\ (f x = NONE)) /\
   ((OPTION_BIND p f = SOME y) <=> ?x. (p = SOME x) /\ (f x = SOME y))`,
  OPTION_CASES_TAC ``p:'a option`` THEN SRW_TAC [][]);
val _ = export_rewrites ["OPTION_BIND_EQUALS_OPTION"]

val IS_SOME_BIND = Q.store_thm ("IS_SOME_BIND",
  `IS_SOME (OPTION_BIND x g) ==> IS_SOME (x : 'a option)`,
  OPTION_CASES_TAC “x:'a option” THEN
  REWRITE_TAC [IS_SOME_DEF, OPTION_BIND_def]) ;

Theorem OPTION_BIND_SOME:
  !opt:'a option. OPTION_BIND opt SOME = opt
Proof
  GEN_TAC >> OPTION_CASES_TAC “opt: 'a option” >> REWRITE_TAC[OPTION_BIND_def]
QED

val OPTION_IGNORE_BIND_def = new_definition(
  "OPTION_IGNORE_BIND_def",
  ``OPTION_IGNORE_BIND m1 m2 = OPTION_BIND m1 (K m2)``);

val OPTION_IGNORE_BIND_thm = store_thm(
  "OPTION_IGNORE_BIND_thm",
  ``(OPTION_IGNORE_BIND NONE m = NONE) /\
    (OPTION_IGNORE_BIND (SOME v) m = m)``,
  SRW_TAC[][OPTION_IGNORE_BIND_def]);
val _ = export_rewrites ["OPTION_IGNORE_BIND_thm"]
val _ = computeLib.add_persistent_funs ["OPTION_IGNORE_BIND_thm"]

val OPTION_IGNORE_BIND_EQUALS_OPTION = store_thm(
  "OPTION_IGNORE_BIND_EQUALS_OPTION[simp]",
  ``((OPTION_IGNORE_BIND (m1:'a option) m2 = NONE) <=>
       (m1 = NONE) \/ (m2 = NONE)) /\
    ((OPTION_IGNORE_BIND m1 m2 = SOME y) <=>
       ?x. (m1 = SOME x) /\ (m2 = SOME y))``,
  OPTION_CASES_TAC ``m1:'a option`` THEN SRW_TAC [][]);

val OPTION_GUARD_def = Prim_rec.new_recursive_definition {
  name = "OPTION_GUARD_def",
  rec_axiom = boolTheory.boolAxiom,
  def = ``(OPTION_GUARD T = SOME ()) /\
          (OPTION_GUARD F = NONE)``};
val _ = export_rewrites ["OPTION_GUARD_def"]
val _ = computeLib.add_persistent_funs ["OPTION_GUARD_def"]
(* suggest overloading this to assert when used with other monad syntax. *)

val OPTION_GUARD_COND = store_thm(
  "OPTION_GUARD_COND",
  ``OPTION_GUARD b = if b then SOME () else NONE``,
  ASM_CASES_TAC ``b:bool`` THEN ASM_REWRITE_TAC [OPTION_GUARD_def])

val OPTION_GUARD_EQ_THM = store_thm(
  "OPTION_GUARD_EQ_THM",
  ``((OPTION_GUARD b = SOME ()) <=> b) /\
    ((OPTION_GUARD b = NONE) <=> ~b)``,
  Cases_on `b` THEN SRW_TAC[][]);
val _ = export_rewrites ["OPTION_GUARD_EQ_THM"]

val OPTION_CHOICE_def = Prim_rec.new_recursive_definition
  {name = "OPTION_CHOICE_def",
   rec_axiom = option_Axiom,
   def = ``(OPTION_CHOICE NONE m2 = m2) /\
           (OPTION_CHOICE (SOME x) m2 = SOME x)``}
val _ = export_rewrites ["OPTION_CHOICE_def"]
val _ = computeLib.add_persistent_funs ["OPTION_CHOICE_def"]

val OPTION_CHOICE_EQ_NONE = store_thm(
  "OPTION_CHOICE_EQ_NONE",
  ``(OPTION_CHOICE (m1:'a option) m2 = NONE) <=> (m1 = NONE) /\ (m2 = NONE)``,
  OPTION_CASES_TAC ``m1:'a option`` THEN SRW_TAC[][]);

val OPTION_CHOICE_NONE = store_thm(
  "OPTION_CHOICE_NONE[simp]",
  ``OPTION_CHOICE (m1:'a option) NONE = m1``,
  OPTION_CASES_TAC ``m1:'a option`` THEN SRW_TAC[][]);

val OPTION_MCOMP_def = Q.new_definition ("OPTION_MCOMP_def",
  `OPTION_MCOMP g f m = OPTION_BIND (f m) g`) ;

val o_THM = combinTheory.o_THM ;

(* OPTION_MCOMP is the composition operator in the
  Kleisli category of the option monad *)
val OPTION_MCOMP_ASSOC = store_thm
  ("OPTION_MCOMP_ASSOC",
   ``OPTION_MCOMP f (OPTION_MCOMP g (h : 'a -> 'b option)) =
     OPTION_MCOMP (OPTION_MCOMP f g) h``,
   REWRITE_TAC [OPTION_MCOMP_def, FUN_EQ_THM, o_THM]
     THEN GEN_TAC THEN OPTION_CASES_TAC ``h x : 'b option``
     THEN REWRITE_TAC [OPTION_BIND_def, o_THM, OPTION_MCOMP_def]);

(* SOME is the UNIT function of the option monad,
  and the identity arrow in the Kleisli category *)
val OPTION_MCOMP_ID = store_thm
  ("OPTION_MCOMP_ID",
   ``(OPTION_MCOMP g SOME = g) /\ (OPTION_MCOMP SOME f = f : 'a -> 'b option)``,
   REWRITE_TAC [OPTION_MCOMP_def, OPTION_BIND_def, FUN_EQ_THM, o_THM]
     THEN GEN_TAC THEN OPTION_CASES_TAC ``f x : 'b option``
     THEN REWRITE_TAC [OPTION_BIND_def]);


(* ----------------------------------------------------------------------
    OPTION_APPLY
   ---------------------------------------------------------------------- *)

val OPTION_APPLY_def = Prim_rec.new_recursive_definition
  {name = "OPTION_APPLY_def",
   rec_axiom = option_Axiom,
   def = ``(OPTION_APPLY NONE x = NONE) /\
           (OPTION_APPLY (SOME f) x = OPTION_MAP f x)``}
val _ = export_rewrites ["OPTION_APPLY_def"]

val _ = set_mapped_fixity { fixity = Infixl 500,
                            term_name = "APPLICATIVE_FAPPLY",
                            tok = "<*>" }
val _ = overload_on ("APPLICATIVE_FAPPLY", ``OPTION_APPLY``)

(* this could be the definition of OPTION_MAP2/lift2 *)
val OPTION_APPLY_MAP2 = store_thm(
  "OPTION_APPLY_MAP2",
  ``OPTION_MAP f (x:'a option) <*> (y:'b option) = OPTION_MAP2 f x y``,
  OPTION_CASES_TAC ``x:'a option`` THEN SRW_TAC[][] THEN
  OPTION_CASES_TAC ``y:'b option`` THEN SRW_TAC[][]);

(* monadic "laws" - first is clause 2 of definition above, so omitted below *)
val SOME_SOME_APPLY = store_thm(
  "SOME_SOME_APPLY",
  ``SOME f <*> SOME x = SOME (f x)``,
  SRW_TAC[][]);

val SOME_APPLY_PERMUTE = store_thm(
  "SOME_APPLY_PERMUTE",
  ``(f:('a -> 'b) option)  <*> (SOME x) = SOME (\f. f x) <*> f``,
  OPTION_CASES_TAC ``f:('a -> 'b) option`` THEN SRW_TAC[][]);

val OPTION_APPLY_o = store_thm(
  "OPTION_APPLY_o",
  ``SOME $o <*> (f:('b->'c)option) <*> (g:('a->'b) option) <*> (x:'a option) =
    f <*> (g <*> x)``,
  OPTION_CASES_TAC ``f:('b->'c)option`` THEN SRW_TAC[][] THEN
  OPTION_CASES_TAC ``g:('a->'b)option`` THEN SRW_TAC[][] THEN
  OPTION_CASES_TAC ``x:'a option`` THEN SRW_TAC[][]);



(* ----------------------------------------------------------------------
    OPTREL - lift a relation on 'a, 'b to 'a option, 'b option
   ---------------------------------------------------------------------- *)

val OPTREL_def = new_definition("OPTREL_def",
  ``OPTREL R x y <=>
      (x = NONE) /\ (y = NONE) \/
      ?x0 y0. (x = SOME x0) /\ (y = SOME y0) /\ R x0 y0``);

val OPTREL_MONO = store_thm(
  "OPTREL_MONO",
  ``(!x:'a y:'b. P x y ==> Q x y) ==> (OPTREL P x y ==> OPTREL Q x y)``,
  BasicProvers.SRW_TAC [][OPTREL_def] THEN BasicProvers.SRW_TAC [][SOME_11]);
val _ = IndDefLib.export_mono "OPTREL_MONO"

val OPTREL_refl = store_thm(
"OPTREL_refl",
``(!x. R x x) ==> !x. OPTREL R x x``,
STRIP_TAC THEN GEN_TAC
THEN OPTION_CASES_TAC ``x:'a option``
THEN ASM_REWRITE_TAC(OPTREL_def::option_rws)
THEN PROVE_TAC[])
val _ = export_rewrites["OPTREL_refl"]

Theorem OPTREL_eq[simp]:
  OPTREL (=) = (=)
Proof
   REWRITE_TAC[FUN_EQ_THM] >> rpt strip_tac >> Q.RENAME_TAC [‘OPTREL _ x y’] >>
   MAP_EVERY OPTION_CASES_TAC [“x:'a option”, “y:'a option”] >>
   simpLib.SIMP_TAC bool_ss (OPTREL_def::option_rws) >> METIS_TAC[]
QED

Theorem OPTREL_SOME:
  (!R x y. OPTREL R (SOME x) y <=> ?z. (y = SOME z) /\ R x z) /\
  (!R x y. OPTREL R x (SOME y) <=> ?z. (x = SOME z) /\ R z y)
Proof
  SRW_TAC[][OPTREL_def]
QED

val OPTREL_O_lemma = Q.prove(
  `!R1 R2 l1 l2.
     OPTREL (R1 O R2) l1 l2 <=> ?l3. OPTREL R2 l1 l3 /\ OPTREL R1 l3 l2`,
  SRW_TAC [][OPTREL_def,EQ_IMP_THM,relationTheory.O_DEF,PULL_EXISTS] >>
  FULL_SIMP_TAC (srw_ss()) [PULL_EXISTS] >> METIS_TAC[]);

Theorem OPTREL_O:
  !R1 R2. OPTREL (R1 O R2) = OPTREL R1 O OPTREL R2
Proof
  SRW_TAC[][FUN_EQ_THM,OPTREL_O_lemma,relationTheory.O_DEF]
QED

(* ----------------------------------------------------------------------
    some (Hilbert choice "lifted" to the option type)

    some P = NONE, when P is everywhere false.
      otherwise
    some P = SOME x ensuring P x.

    This constant saves pain when confronted with the possibility of
    writing
      if ?x. P x then f (@x. P x) else ...

    Instead one can write
      case (some x. P x) of SOME x -> f x || NONE -> ...
    and avoid having to duplicate the P formula.
   ---------------------------------------------------------------------- *)

val some_def = new_definition(
  "some_def",
  ``some P = if ?x. P x then SOME (@x. P x) else NONE``);

val some_intro = store_thm(
  "some_intro",
  ``(!x. P x ==> Q (SOME x)) /\ ((!x. ~P x) ==> Q NONE) ==> Q (some P)``,
  SRW_TAC [][some_def] THEN METIS_TAC []);

val some_elim = store_thm(
  "some_elim",
  ``Q (some P) ==> (?x. P x /\ Q (SOME x)) \/ ((!x. ~P x) /\ Q NONE)``,
  SRW_TAC [][some_def] THEN METIS_TAC []);
val _ = set_fixity "some" Binder

val some_F = store_thm(
  "some_F",
  ``(some x. F) = NONE``,
  DEEP_INTRO_TAC some_intro THEN SRW_TAC [][]);
val _ = export_rewrites ["some_F"]

val some_EQ = store_thm(
  "some_EQ",
  ``((some x. x = y) = SOME y) /\ ((some x. y = x) = SOME y)``,
  CONJ_TAC THEN DEEP_INTRO_TAC some_intro THEN SRW_TAC [][]);
val _ = export_rewrites ["some_EQ"]

val option_case_cong =
  save_thm("option_case_cong",
      Prim_rec.case_cong_thm option_nchotomy option_case_def);

val OPTION_ALL_def = Prim_rec.new_recursive_definition {
  def = ``(OPTION_ALL P NONE <=> T) /\ (OPTION_ALL P (SOME (x:'a)) <=> P x)``,
  name = "OPTION_ALL_def",
  rec_axiom = option_Axiom };
val _ = export_rewrites ["OPTION_ALL_def"]
val _ = computeLib.add_persistent_funs ["OPTION_ALL_def"]

val OPTION_ALL_MONO = store_thm(
  "OPTION_ALL_MONO",
  ``(!x:'a. P x ==> P' x) ==> OPTION_ALL P opt ==> OPTION_ALL P' opt``,
  Q.SPEC_THEN `opt` STRUCT_CASES_TAC option_nchotomy THEN
  REWRITE_TAC [OPTION_ALL_def] THEN REPEAT STRIP_TAC THEN RES_TAC);
val _ = IndDefLib.export_mono "OPTION_ALL_MONO"

val OPTION_ALL_CONG = store_thm(
  "OPTION_ALL_CONG[defncong]",
  ``!opt opt' P P'.
       (opt = opt') /\ (!x. (opt' = SOME x) ==> (P x <=> P' x)) ==>
       (OPTION_ALL P opt <=> OPTION_ALL P' opt')``,
  simpLib.SIMP_TAC (srw_ss()) [FORALL_OPTION]);

val option_case_eq = Q.store_thm(
  "option_case_eq",
  ‘(option_CASE (opt:'a option) nc sc = v) <=>
   ((opt = NONE) /\ (nc = v) \/ ?x. (opt = SOME x) /\ (sc x = v))’,
  OPTION_CASES_TAC “opt:'a option” THEN SRW_TAC[][EQ_SYM_EQ, option_case_def]);

val S = PP.add_string and NL = PP.NL and B = PP.block PP.CONSISTENT 0

val option_Induct = save_thm("option_Induct",
  ONCE_REWRITE_RULE [boolTheory.CONJ_SYM] option_induction);
val option_CASES = save_thm("option_CASES",
  ONCE_REWRITE_RULE [boolTheory.DISJ_SYM] option_nchotomy);

val _ = TypeBase.export
  [TypeBasePure.mk_datatype_info_no_simpls
     {ax=TypeBasePure.ORIG option_Axiom,
      case_def=option_case_def,
      case_cong=option_case_cong,
      case_eq = option_case_eq,
      induction=TypeBasePure.ORIG option_induction,
      nchotomy=option_nchotomy,
      size=NONE,
      encode=NONE,
      fields=[],
      accessors=[],
      updates=[],
      destructors=[THE_DEF],
      recognizers=[IS_NONE_DEF,IS_SOME_DEF],
      lift=SOME(mk_var("optionSyntax.lift_option",
                       “:'type -> ('a -> 'term) -> 'a option -> 'term”)),
      one_one=SOME SOME_11,
      distinct=SOME NOT_NONE_SOME}];

val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME (fn _ => B[
    S "val _ = let open computeLib",                            NL,
    S "        in add_funs (map lazyfy_thm",                    NL,
    S "               [NOT_NONE_SOME,NOT_SOME_NONE,SOME_11,",   NL,
    S "                option_case_def, ",                      NL,
    S "                IS_SOME_DEF,IS_NONE_DEF,THE_DEF,",       NL,
    S "                OPTION_JOIN_DEF])",                      NL,
    S "        end;"])};

val datatype_option = store_thm(
  "datatype_option",
  ``DATATYPE (option (NONE:'a option) (SOME:'a -> 'a option))``,
  REWRITE_TAC [DATATYPE_TAG_THM])

val _ = BasicProvers.export_rewrites
          ["THE_DEF",
           "IS_SOME_DEF", "IS_NONE_EQ_NONE", "NOT_IS_SOME_EQ_NONE",
           "option_case_ID", "option_case_SOME_ID", "option_case_def",
           "OPTION_JOIN_DEF"];

val _ = export_theory();
