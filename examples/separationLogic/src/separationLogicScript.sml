open HolKernel Parse boolLib bossLib;

(*
quietdec := true;

loadPath :=
       (concat [Globals.HOLDIR, "/examples/separationLogic/src"]) ::
       !loadPath;

map load ["finite_mapTheory", "relationTheory", "congLib", "sortingTheory",
   "rich_listTheory", "generalHelpersTheory", "latticeTheory", "containerTheory",
   "bagTheory"];
show_assums := true;
*)

open generalHelpersTheory finite_mapTheory relationTheory bagTheory pred_setTheory congLib sortingTheory
   listTheory rich_listTheory arithmeticTheory operatorTheory optionTheory latticeTheory
   containerTheory boolSimps ConseqConv markerTheory
open quantHeuristicsLib quantHeuristicsArgsLib

(*
open Sanity
quietdec := false;
*)

val _ = new_theory "separationLogic"


(******************************************************************************)
(* Define separation combinators and algebras                                 *)
(******************************************************************************)

val _ = type_abbrev("bin_option_function",
   Type `:('a option -> 'a option -> 'a option)`);


val OPTION_IS_LEFT_CANCELLATIVE_def = Define `
      OPTION_IS_LEFT_CANCELLATIVE (f:'a bin_option_function) =
      (!x1 x2 x3. ((f x1 x2 = f x1 x3) /\ IS_SOME (f x1 x2)) ==> (x2 = x3))`

val OPTION_IS_RIGHT_CANCELLATIVE_def = Define `
      OPTION_IS_RIGHT_CANCELLATIVE (f:'a bin_option_function) =
      (!x1 x2 x3. ((f x2 x1 = f x3 x1) /\ IS_SOME (f x2 x1)) ==> (x2 = x3))`


val IS_SEPARATION_ALGEBRA_def = Define `
   IS_SEPARATION_ALGEBRA f u =
   (!x. f NONE x = NONE) /\
   (!x. (f (SOME u) (SOME x) = (SOME x))) /\
   COMM f /\ ASSOC f /\
   OPTION_IS_LEFT_CANCELLATIVE f`


val IS_SEPARATION_COMBINATOR_def = Define `
   IS_SEPARATION_COMBINATOR f =

   (!x. f NONE x = NONE) /\
   (!x. ?u. f (SOME u) (SOME x) = (SOME x)) /\
   COMM f /\ ASSOC f /\
   OPTION_IS_LEFT_CANCELLATIVE f`




(* -------------------------------------------------------------------------- *)
(* Rewrites and lemmata about separation combinators and algebras             *)
(* -------------------------------------------------------------------------- *)

val IS_SEPARATION_ALGEBRA___COMBINATOR_DEF = store_thm ("IS_SEPARATION_ALGEBRA___COMBINATOR_DEF",
   ``!f u. IS_SEPARATION_ALGEBRA f u <=>
           ((IS_SEPARATION_COMBINATOR f) /\
            (!x. (f (SOME u) (SOME x) = SOME x)))``,

   SIMP_TAC std_ss [IS_SEPARATION_ALGEBRA_def, IS_SEPARATION_COMBINATOR_def] THEN
   METIS_TAC[]);

val IS_SEPARATION_ALGEBRA___IS_COMBINATOR = store_thm ("IS_SEPARATION_ALGEBRA___IS_COMBINATOR",
   ``!f u. IS_SEPARATION_ALGEBRA f u ==> IS_SEPARATION_COMBINATOR f``,
   SIMP_TAC std_ss [IS_SEPARATION_ALGEBRA___COMBINATOR_DEF]);


val IS_SEPARATION_COMBINATOR___NEURAL_ELEMENT_IDEMPOTENT =
   store_thm ("IS_SEPARATION_COMBINATOR___NEURAL_ELEMENT_IDEMPOTENT",
``!f. IS_SEPARATION_COMBINATOR f ==>
!x u. (f (SOME u) (SOME x) = (SOME x)) ==> (f (SOME u) (SOME u) = SOME u)``,

SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_def] THEN
REPEAT STRIP_TAC THEN
`OPTION_IS_RIGHT_CANCELLATIVE f` by METIS_TAC[OPTION_IS_LEFT_CANCELLATIVE_def, OPTION_IS_RIGHT_CANCELLATIVE_def, COMM_DEF] THEN
POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [OPTION_IS_RIGHT_CANCELLATIVE_def]) THEN
Q.EXISTS_TAC `SOME x` THEN
FULL_SIMP_TAC std_ss [ASSOC_SYM]);



val IS_SEPARATION_COMBINATOR___NEURAL_ELEMENT_IS_NEUTRAL =
   store_thm ("IS_SEPARATION_COMBINATOR___NEURAL_ELEMENT_IS_NEUTRAL",
``!f. IS_SEPARATION_COMBINATOR f ==>

!x1 x2 x3 u. (((f (SOME u) (SOME x1) = (SOME x1)) /\
          (f (SOME u) (SOME x2) = (SOME x3))) ==>
(x3 = x2))``,

REPEAT STRIP_TAC THEN
`f (SOME u) (SOME u) = SOME u` by METIS_TAC[IS_SEPARATION_COMBINATOR___NEURAL_ELEMENT_IDEMPOTENT] THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_def] THEN
`f (SOME u) (SOME x2) = f (SOME u) (SOME x3)` by
   METIS_TAC[ASSOC_DEF, option_CLAUSES] THEN
`SOME x2 = SOME x3` by METIS_TAC[OPTION_IS_LEFT_CANCELLATIVE_def, option_CLAUSES] THEN
FULL_SIMP_TAC std_ss []);



val IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_def =
Define `IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f uf =
   (!x. (f (SOME (uf x)) (SOME x) = (SOME x)))`

val IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR_def =
Define `IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR f uf =
   (IS_SEPARATION_COMBINATOR f /\
    IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f uf)`;


val IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_THM = store_thm (
"IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_THM",

``!f uf. IS_SEPARATION_COMBINATOR f ==>
(IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f uf =
   (!x. (f (SOME (uf x)) (SOME x) = (SOME x))) /\ (!x. (f (SOME x) (SOME (uf x)) = (SOME x))) /\
   (!x1 x2 x3. (f (SOME (uf x1)) (SOME x2) = (SOME x3)) = ((x2 = x3) /\ (uf x1 = uf x2))) /\
   (!x1 x2 x3. (f (SOME x2) (SOME (uf x1)) = (SOME x3)) = ((x2 = x3) /\ (uf x1 = uf x2))) /\
   (!x. f (SOME (uf x)) (SOME (uf x)) = SOME (uf x)) /\
   (!x y. (f (SOME x) (SOME y) = SOME x) = (y = uf x)) /\
   (!x y. (f (SOME y) (SOME x) = SOME x) = (y = uf x)))``,


   REPEAT STRIP_TAC THEN
   Tactical.REVERSE EQ_TAC THEN1 (
      SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_def]
   ) THEN
   STRIP_TAC THEN
   HO_MATCH_MP_TAC (
   prove (``(((P1 uf) /\ (P2 uf) /\ (P3 uf) /\ (P4 uf)) /\
            ((P1 uf ==> Q1 uf) /\
            (P2 uf ==> Q2 uf) /\
            (P4 uf ==> Q4 uf)))  ==>

           ((P1 uf) /\ (Q1 uf) /\ (P2 uf) /\ (Q2 uf) /\ (P3 uf) /\ (P4 uf) /\ (Q4 uf))``, METIS_TAC[])) THEN
   FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_def] THEN
   Tactical.REVERSE CONJ_TAC THEN1 METIS_TAC[IS_SEPARATION_COMBINATOR_def, COMM_DEF] THEN
   REPEAT STRIP_TAC THENL [
      `(f (SOME (uf x1)) (SOME x1) = SOME x1) /\ (f (SOME (uf x2)) (SOME x2) = SOME x2)` by ALL_TAC THEN1 (
         bossLib.UNABBREV_ALL_TAC THEN METIS_TAC[]
      ) THEN
      EQ_TAC THENL [
         STRIP_TAC THEN
         `x3 = x2` by METIS_TAC[IS_SEPARATION_COMBINATOR___NEURAL_ELEMENT_IS_NEUTRAL] THEN
         FULL_SIMP_TAC std_ss [] THEN
         METIS_TAC[IS_SEPARATION_COMBINATOR_def,
            OPTION_IS_LEFT_CANCELLATIVE_def, COMM_DEF, option_CLAUSES],

         METIS_TAC[]
      ],

      METIS_TAC[IS_SEPARATION_COMBINATOR___NEURAL_ELEMENT_IDEMPOTENT],

      EQ_TAC THENL [
         STRIP_TAC THEN
         ONCE_REWRITE_TAC [GSYM SOME_11] THEN
         `OPTION_IS_LEFT_CANCELLATIVE f`  by FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_def] THEN
         POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [OPTION_IS_LEFT_CANCELLATIVE_def]) THEN
         Q.EXISTS_TAC `SOME x` THEN
         ASM_SIMP_TAC std_ss [] THEN
         METIS_TAC[COMM_DEF, IS_SEPARATION_COMBINATOR_def],

         METIS_TAC[COMM_DEF, IS_SEPARATION_COMBINATOR_def]
      ]
   ]);


val IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR_THM = store_thm (
"IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR_THM",

``!f uf.(IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR f uf =
   IS_SEPARATION_COMBINATOR f /\
   (!x. (f (SOME (uf x)) (SOME x) = (SOME x))) /\ (!x. (f (SOME x) (SOME (uf x)) = (SOME x))) /\
   (!x1 x2 x3. (f (SOME (uf x1)) (SOME x2) = (SOME x3)) = ((x2 = x3) /\ (uf x1 = uf x2))) /\
   (!x1 x2 x3. (f (SOME x2) (SOME (uf x1)) = (SOME x3)) = ((x2 = x3) /\ (uf x1 = uf x2))) /\
   (!x. f (SOME (uf x)) (SOME (uf x)) = SOME (uf x)) /\
   (!x y. (f (SOME x) (SOME y) = SOME x) = (y = uf x)) /\
   (!x y. (f (SOME y) (SOME x) = SOME x) = (y = uf x)))``,

   REWRITE_TAC [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR_def] THEN
   REPEAT GEN_TAC THEN
   Cases_on `IS_SEPARATION_COMBINATOR f` THEN ASM_REWRITE_TAC[] THEN
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_THM]);


val IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_11 = store_thm (
"IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_11",
``!f uf1 uf2. IS_SEPARATION_COMBINATOR f /\
   IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f uf1 /\
   IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f uf2 ==>
   (uf1 = uf2)``,

SIMP_TAC std_ss [FUN_EQ_THM, IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_def] THEN
REPEAT STRIP_TAC THEN

ONCE_REWRITE_TAC [GSYM SOME_11] THEN
`OPTION_IS_LEFT_CANCELLATIVE f`  by FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_def] THEN
POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [OPTION_IS_LEFT_CANCELLATIVE_def]) THEN
Q.EXISTS_TAC `SOME x` THEN
ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[COMM_DEF, IS_SEPARATION_COMBINATOR_def, option_CLAUSES]);



val IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_EQS =
store_thm ("IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_EQS",
``!f uf s1 s2 s3.
     (IS_SEPARATION_COMBINATOR f /\
      IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f uf /\
      (f (SOME s1) (SOME s2) = SOME s3)) ==>

((uf s1 = uf s2) /\ (uf s1 = uf s3) /\ (uf s2 = uf s3))``,


REPEAT GEN_TAC THEN STRIP_TAC THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_def,
            IS_SEPARATION_COMBINATOR_def] THEN
`f (SOME s1) (SOME s2) = f (SOME (uf s1)) (SOME s3)` by
   PROVE_TAC[ASSOC_DEF] THEN
`f (SOME s1) (SOME s2) = f (SOME (uf s2)) (SOME s3)` by
   PROVE_TAC[ASSOC_DEF, COMM_DEF] THEN
`SOME s3 = f (SOME (uf s3)) (SOME s3)` by PROVE_TAC[] THEN
`OPTION_IS_RIGHT_CANCELLATIVE f` by
   METIS_TAC[OPTION_IS_RIGHT_CANCELLATIVE_def,
        OPTION_IS_LEFT_CANCELLATIVE_def, COMM_DEF] THEN
METIS_TAC[OPTION_IS_RIGHT_CANCELLATIVE_def,
     option_CLAUSES]);



val IS_SEPARATION_COMBINATOR_HALF_EXPAND_THM = store_thm ("IS_SEPARATION_COMBINATOR_HALF_EXPAND_THM",
``!f. IS_SEPARATION_COMBINATOR f =

   (!x. f x NONE = NONE) /\
   (!x. f NONE x = NONE) /\
   (?uf. IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f uf) /\
   COMM f /\ ASSOC f /\
   OPTION_IS_LEFT_CANCELLATIVE f /\
   OPTION_IS_RIGHT_CANCELLATIVE f``,


REPEAT STRIP_TAC THEN
Tactical.REVERSE EQ_TAC THEN1 (
   SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_def, IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_def] THEN
   METIS_TAC[]
) THEN
STRIP_TAC THEN
POP_ASSUM (fn thm => ASSUME_TAC thm THEN MP_TAC thm) THEN
SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_def] THEN
REPEAT STRIP_TAC THENL [
   PROVE_TAC[COMM_DEF],

   SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_def] THEN
   METIS_TAC[],

   METIS_TAC [OPTION_IS_LEFT_CANCELLATIVE_def, OPTION_IS_RIGHT_CANCELLATIVE_def, COMM_DEF]
]);



val IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_IMP = store_thm (
"IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_IMP",
``!f. IS_SEPARATION_COMBINATOR f ==>
(?uf. IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR f uf)``,

SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_HALF_EXPAND_THM,
    IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___WITH_COMBINATOR_def]);




val IS_SEPARATION_COMBINATOR_EXPAND_THM = store_thm ("IS_SEPARATION_COMBINATOR_EXPAND_THM",
``!f.   IS_SEPARATION_COMBINATOR f =

   (!x. f x NONE = NONE) /\
   (!x. f NONE x = NONE) /\
   (?uf. (!x. (f (SOME (uf x)) (SOME x) = (SOME x))) /\ (!x. (f (SOME x) (SOME (uf x)) = (SOME x))) /\
      (!x1 x2 x3. (f (SOME (uf x1)) (SOME x2) = (SOME x3)) = ((x2 = x3) /\ (uf x1 = uf x2))) /\
      (!x1 x2 x3. (f (SOME x2) (SOME (uf x1)) = (SOME x3)) = ((x2 = x3) /\ (uf x1 = uf x2))) /\
      (!x. f (SOME (uf x)) (SOME (uf x)) = SOME (uf x)) /\
      (!x y. (f (SOME x) (SOME y) = SOME x) = (y = uf x)) /\
      (!x y. (f (SOME y) (SOME x) = SOME x) = (y = uf x))) /\
   COMM f /\ ASSOC f /\
   OPTION_IS_LEFT_CANCELLATIVE f /\
   OPTION_IS_RIGHT_CANCELLATIVE f``,

REPEAT STRIP_TAC THEN
Tactical.REVERSE (EQ_TAC THEN STRIP_TAC) THEN1 (
   ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_def]
) THEN
ASM_SIMP_TAC std_ss [GSYM IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_THM] THEN
METIS_TAC[IS_SEPARATION_COMBINATOR_HALF_EXPAND_THM]
);





val IS_SEPARATION_ALGEBRA_HALF_EXPAND_THM = store_thm ("IS_SEPARATION_ALGEBRA_HALF_EXPAND_THM",
``!f u. IS_SEPARATION_ALGEBRA f u =

   (!x. f x NONE = NONE) /\
   (!x. f NONE x = NONE) /\
   (IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f (K u)) /\
   COMM f /\ ASSOC f /\
   OPTION_IS_LEFT_CANCELLATIVE f /\
   OPTION_IS_RIGHT_CANCELLATIVE f``,


REPEAT STRIP_TAC THEN
Tactical.REVERSE EQ_TAC THEN1 (
   SIMP_TAC std_ss [IS_SEPARATION_ALGEBRA_def, IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_def]
) THEN
STRIP_TAC THEN
IMP_RES_TAC IS_SEPARATION_ALGEBRA___IS_COMBINATOR THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_HALF_EXPAND_THM,
   IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_def,
   IS_SEPARATION_ALGEBRA_def]);



val IS_SEPARATION_ALGEBRA_EXPAND_THM = store_thm ("IS_SEPARATION_ALGEBRA_EXPAND_THM",
``!f u. IS_SEPARATION_ALGEBRA f u =

   (!x. f x NONE = NONE) /\
   (!x. f NONE x = NONE) /\
   (!x. (f (SOME u) (SOME x) = (SOME x))) /\
   (!x. (f (SOME x) (SOME u) = (SOME x))) /\
   (f (SOME u) (SOME u) = SOME u) /\
   (!x y. (f (SOME x) (SOME y) = SOME x) = (y = u)) /\
   (!x y. (f (SOME y) (SOME x) = SOME x) = (y = u)) /\
   COMM f /\ ASSOC f /\
   OPTION_IS_LEFT_CANCELLATIVE f /\
   OPTION_IS_RIGHT_CANCELLATIVE f``,

REPEAT STRIP_TAC THEN
Tactical.REVERSE (EQ_TAC THEN STRIP_TAC) THEN1 (
   ASM_SIMP_TAC std_ss [IS_SEPARATION_ALGEBRA_def]
) THEN
IMP_RES_TAC IS_SEPARATION_ALGEBRA___IS_COMBINATOR THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_ALGEBRA_HALF_EXPAND_THM,
   IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_THM]);


val asl_emp_def = Define `asl_emp f = \u. ?x:'a. f (SOME (u:'a)) (SOME x) = (SOME x)`

val asl_star_def = Define `
asl_star = (\(f:'a option -> 'a option -> 'a option) P Q x. ?p q. (SOME x = f (SOME p) (SOME q)) /\ (p IN P) /\ (q IN Q))`


val asl_emp_ALGEBRA = store_thm ("asl_emp_ALGEBRA",
``!f u. IS_SEPARATION_ALGEBRA f u ==>
     (asl_emp f = {u})``,

SIMP_TAC std_ss [IS_SEPARATION_ALGEBRA_EXPAND_THM, asl_emp_def,
   EXTENSION, IN_SING, IN_ABS]);


val IS_SEPARATION_ALGEBRA_NEUTRAL_ELEMENT_FUNCTION_THM = store_thm (
"IS_SEPARATION_ALGEBRA_NEUTRAL_ELEMENT_FUNCTION_THM",

``!f u uf . IS_SEPARATION_ALGEBRA f u ==>
(IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f uf = (uf = K u))``,

SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_def,
   IS_SEPARATION_ALGEBRA_EXPAND_THM, FUN_EQ_THM]);


val IS_SEPARATION_ALGEBRA___ALT_DEF = store_thm (
"IS_SEPARATION_ALGEBRA___ALT_DEF",

``!f u . IS_SEPARATION_ALGEBRA f u =
(IS_SEPARATION_COMBINATOR f /\
(!uf. IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f uf = (uf = K u)))``,

REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
   PROVE_TAC[IS_SEPARATION_ALGEBRA___IS_COMBINATOR],
   PROVE_TAC[IS_SEPARATION_ALGEBRA_NEUTRAL_ELEMENT_FUNCTION_THM],

   FULL_SIMP_TAC std_ss [IS_SEPARATION_ALGEBRA_def, IS_SEPARATION_COMBINATOR_def,
      IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_def] THEN
   SIMP_TAC std_ss [FUN_EQ_THM]
]);


val IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___asl_emp = store_thm (
"IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION___asl_emp",
``
!f uf.
(IS_SEPARATION_COMBINATOR f /\
IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f uf) ==>

(asl_emp f = (IMAGE uf UNIV))``,

REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f uf` MP_TAC THEN
ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_THM] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [EXTENSION, IN_IMAGE, IN_UNIV,
   asl_emp_def, IN_ABS]);



(******************************************************************************)
(* BIN_OPTION_MAP                                                             *)
(******************************************************************************)

val BIN_OPTION_MAP_def = Define `
   (BIN_OPTION_MAP (f:'a -> 'a -> 'a) c NONE x = NONE) /\
   (BIN_OPTION_MAP f c x NONE = NONE) /\
   (BIN_OPTION_MAP f c (SOME x1) (SOME x2) =
      if (~(c x1 x2)) then NONE else
      SOME (f x1 x2))`;


val BIN_OPTION_MAP_THM = store_thm ("BIN_OPTION_MAP_THM",

``  (BIN_OPTION_MAP f c (SOME x1) (SOME x2) =
      if (~(c x1 x2)) then NONE else
      SOME (f x1 x2)) /\
  (BIN_OPTION_MAP f c NONE x = NONE) /\
  (BIN_OPTION_MAP f c x NONE = NONE) /\
  ((BIN_OPTION_MAP f c s1 s2 = SOME x3) = (?x1 x2. (s1 = SOME x1) /\ (s2 = SOME x2) /\ (c x1 x2) /\ (x3 = f x1 x2))) /\
  ((BIN_OPTION_MAP f c s1 s2 = NONE) = ((s1 = NONE) \/ (s2 = NONE) \/ ~(c (THE s1) (THE s2)))) /\
  (RIGHT_ID (BIN_OPTION_MAP f c) s1 = (IS_SOME s1 /\ (RIGHT_ID f (THE s1)) /\ !x2. c x2 (THE s1))) /\
  (LEFT_ID (BIN_OPTION_MAP f c) s1 = ((IS_SOME s1) /\ (LEFT_ID f (THE s1)) /\ !x2. c (THE s1) x2)) /\
  (COMM (BIN_OPTION_MAP f c) =
   ((COMM c) /\
   !x1 x2. c x1 x2 ==> (f x1 x2 = f x2 x1))) /\
  (ASSOC (BIN_OPTION_MAP f c) =
   (!x1 x2 x3.
      (c x2 x3 /\ c x1 (f x2 x3) = c x1 x2 /\ c (f x1 x2) x3) /\
      ((c x2 x3 /\ c x1 (f x2 x3)) ==> (f x1 (f x2 x3) = f (f x1 x2) x3)))) /\
  (OPTION_IS_LEFT_CANCELLATIVE (BIN_OPTION_MAP f c) =
   (!x1 x2 x3. (c x1 x2 /\ c x1 x3 /\ (f x1 x2 = f x1 x3)) ==> (x2 = x3))) /\
  (OPTION_IS_RIGHT_CANCELLATIVE (BIN_OPTION_MAP f c) =
   (!x1 x2 x3. (c x2 x1 /\ c x3 x1 /\ (f x2 x1 = f x3 x1)) ==> (x2 = x3))) /\
  (IS_SOME (BIN_OPTION_MAP f c s1 s2) =
   ((IS_SOME s1) /\ (IS_SOME s2) /\ c (THE s1) (THE s2)))``,

REPEAT STRIP_TAC THENL [
   SIMP_TAC std_ss [BIN_OPTION_MAP_def],

   Cases_on `x` THEN
   SIMP_TAC std_ss [BIN_OPTION_MAP_def],

   Cases_on `x` THEN
   SIMP_TAC std_ss [BIN_OPTION_MAP_def],

   Cases_on `s1` THEN Cases_on `s2` THEN
   SIMP_TAC std_ss [BIN_OPTION_MAP_def, COND_RAND, COND_RATOR] THEN
   METIS_TAC[],

   Cases_on `s1` THEN Cases_on `s2` THEN
   SIMP_TAC std_ss [BIN_OPTION_MAP_def, COND_RAND, COND_RATOR] THEN
   METIS_TAC[],

   Cases_on `s1` THENL [
      SIMP_TAC std_ss [RIGHT_ID_DEF] THEN
      Q.EXISTS_TAC `SOME y` THEN
      SIMP_TAC std_ss [BIN_OPTION_MAP_def],

      SIMP_TAC std_ss [RIGHT_ID_DEF] THEN
      EQ_TAC THENL [
         REPEAT STRIP_TAC THENL [
            POP_ASSUM (MP_TAC o (Q.SPEC `SOME x'`)) THEN
            SIMP_TAC std_ss [BIN_OPTION_MAP_def, COND_RAND, COND_RATOR],

            POP_ASSUM (MP_TAC o (Q.SPEC `SOME x2`)) THEN
            SIMP_TAC std_ss [BIN_OPTION_MAP_def, COND_RAND, COND_RATOR]
         ],

         REPEAT STRIP_TAC THEN
         Cases_on `x'` THEN
         SIMP_TAC std_ss [BIN_OPTION_MAP_def, COND_RAND, COND_RATOR] THEN
         METIS_TAC[]
      ]
   ],


   Cases_on `s1` THENL [
      SIMP_TAC std_ss [LEFT_ID_DEF] THEN
      Q.EXISTS_TAC `SOME y` THEN
      SIMP_TAC std_ss [BIN_OPTION_MAP_def],

      SIMP_TAC std_ss [LEFT_ID_DEF] THEN
      EQ_TAC THENL [
         REPEAT STRIP_TAC THENL [
            POP_ASSUM (MP_TAC o (Q.SPEC `SOME x'`)) THEN
            SIMP_TAC std_ss [BIN_OPTION_MAP_def, COND_RAND, COND_RATOR],

            POP_ASSUM (MP_TAC o (Q.SPEC `SOME x2`)) THEN
            SIMP_TAC std_ss [BIN_OPTION_MAP_def, COND_RAND, COND_RATOR]
         ],

         REPEAT STRIP_TAC THEN
         Cases_on `x'` THEN
         SIMP_TAC std_ss [BIN_OPTION_MAP_def, COND_RAND, COND_RATOR] THEN
         METIS_TAC[]
      ]
   ],


   SIMP_TAC std_ss [COMM_DEF] THEN
   EQ_TAC THEN STRIP_TAC THENL [
      SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN
      REPEAT GEN_TAC THEN
      Q.PAT_ASSUM `!x y. P x y` (fn thm => MP_TAC (Q.SPECL [`SOME x1`, `SOME x2`] thm)) THEN
      ASM_SIMP_TAC std_ss [BIN_OPTION_MAP_def] THEN
      Cases_on `c x1 x2` THEN Cases_on `c x2 x1` THEN
      ASM_SIMP_TAC std_ss [],

      Cases_on `x` THEN
      Cases_on `y` THEN
      ASM_SIMP_TAC std_ss [BIN_OPTION_MAP_def]
   ],


   SIMP_TAC std_ss [ASSOC_DEF] THEN
   EQ_TAC THEN STRIP_TAC THENL [
      REPEAT GEN_TAC THEN
      Q.PAT_ASSUM `!x y z. P x y z` (fn thm => MP_TAC (Q.SPECL [`SOME x1`, `SOME x2`, `SOME x3`] thm)) THEN
      ASM_SIMP_TAC std_ss [BIN_OPTION_MAP_def] THEN
      Cases_on `c x1 x2` THEN Cases_on `c x2 x3` THEN
      Cases_on `c (f x1 x2) x3` THEN Cases_on `c x1 (f x2 x3)` THEN
      ASM_SIMP_TAC std_ss [BIN_OPTION_MAP_def],

      Cases_on `x` THEN
      Cases_on `y` THEN
      Cases_on `z` THEN
      ASM_SIMP_TAC std_ss [BIN_OPTION_MAP_def] THENL [
         METIS_TAC[BIN_OPTION_MAP_def],
         METIS_TAC[BIN_OPTION_MAP_def],

         Cases_on `c x x''` THEN Cases_on `c x' x` THEN
         Cases_on `c x' (f x x'')` THEN Cases_on `c (f x' x) x''` THEN
         ASM_SIMP_TAC std_ss [BIN_OPTION_MAP_def] THEN
         METIS_TAC[]
      ]
   ],


   SIMP_TAC std_ss [OPTION_IS_LEFT_CANCELLATIVE_def] THEN
   EQ_TAC THEN STRIP_TAC THENL [
      REPEAT GEN_TAC THEN
      Q.PAT_ASSUM `!x y z. P x y z` (fn thm => MP_TAC (Q.SPECL [`SOME x1`, `SOME x2`, `SOME x3`] thm)) THEN
      ASM_SIMP_TAC std_ss [BIN_OPTION_MAP_def],

      Cases_on `x1` THEN
      Cases_on `x2` THEN
      Cases_on `x3` THEN
      ASM_SIMP_TAC std_ss [BIN_OPTION_MAP_def] THEN
      Cases_on `c x x'` THEN Cases_on `c x x''` THEN
      ASM_SIMP_TAC std_ss [] THEN
      METIS_TAC[]
   ],


   SIMP_TAC std_ss [OPTION_IS_RIGHT_CANCELLATIVE_def] THEN
   EQ_TAC THEN STRIP_TAC THENL [
      REPEAT GEN_TAC THEN
      Q.PAT_ASSUM `!x y z. P x y z` (fn thm => MP_TAC (Q.SPECL [`SOME x1`, `SOME x2`, `SOME x3`] thm)) THEN
      ASM_SIMP_TAC std_ss [BIN_OPTION_MAP_def],

      Cases_on `x1` THEN
      Cases_on `x2` THEN
      Cases_on `x3` THEN
      ASM_SIMP_TAC std_ss [BIN_OPTION_MAP_def] THEN
      Cases_on `c x' x` THEN Cases_on `c x'' x` THEN
      ASM_SIMP_TAC std_ss [] THEN
      METIS_TAC[]
   ],


   Cases_on `s1` THEN Cases_on `s2` THEN
   SIMP_TAC std_ss [BIN_OPTION_MAP_def, COND_RAND, COND_RATOR]
]);


val BIN_OPTION_MAP_ALL_DEF_def = Define `BIN_OPTION_MAP_ALL_DEF f = BIN_OPTION_MAP f (K (K T))`

val BIN_OPTION_MAP_ALL_DEF_THM = save_thm ("BIN_OPTION_MAP_ALL_DEF_THM",
   let
      val thm0 = Q.GEN `c` BIN_OPTION_MAP_THM;
      val thm1 = Q.SPEC `K (K T)` thm0;
      val thm2 = REWRITE_RULE [GSYM BIN_OPTION_MAP_ALL_DEF_def] thm1;
      val thm3 = SIMP_RULE std_ss [prove (``COMM (K (K T))``, SIMP_TAC std_ss [COMM_DEF]), GSYM COMM_DEF, GSYM ASSOC_DEF] thm2;
   in
      thm3
   end);




(******************************************************************************)
(* Monoid                                                                     *)
(******************************************************************************)

val ASL_IS_SEPARATE_def = Define `
   ASL_IS_SEPARATE (f:'a option -> 'a option -> 'a option) x1 x2 = IS_SOME (f (SOME x1) (SOME x2))`;


val ASL_IS_SUBSTATE_def = Define `
   ASL_IS_SUBSTATE (f:'a option -> 'a option -> 'a option) s0 s2 = ?s1. f (SOME s0) (SOME s1) = (SOME s2)`;


val ASL_IS_SUBSTATE_INTRO = store_thm ("ASL_IS_SUBSTATE_INTRO",
``!f. IS_SEPARATION_COMBINATOR f ==> !x1 x2 x.
   (f (SOME x1) (SOME x2) = SOME x) ==>
   (ASL_IS_SUBSTATE f x1 x /\ ASL_IS_SUBSTATE f x2 x)``,

SIMP_TAC std_ss [ASL_IS_SUBSTATE_def, IS_SEPARATION_COMBINATOR_def, COMM_DEF] THEN
METIS_TAC[]);


val ASL_IS_SUBSTATE___IS_PREORDER = store_thm ("ASL_IS_SUBSTATE___IS_PREORDER",
``!f. IS_SEPARATION_COMBINATOR f ==>
PreOrder (ASL_IS_SUBSTATE f)``,

SIMP_TAC std_ss [PreOrder, reflexive_def, transitive_def, ASL_IS_SUBSTATE_def,
   IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
REPEAT STRIP_TAC THENL [
   METIS_TAC[],

   Q.PAT_ASSUM `X = SOME z` (ASSUME_TAC o GSYM) THEN
   Q.PAT_ASSUM `X = SOME y` (ASSUME_TAC o GSYM) THEN
   FULL_SIMP_TAC std_ss [ASSOC_SYM] THEN
   Cases_on `f (SOME s1) (SOME s1')` THEN (
      METIS_TAC[]
   )
]);


val ASL_IS_SUBSTATE___REFL = store_thm ("ASL_IS_SUBSTATE___REFL",
``!f s. IS_SEPARATION_COMBINATOR f ==> ASL_IS_SUBSTATE f s s``,
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [ASL_IS_SUBSTATE_def,
   IS_SEPARATION_COMBINATOR_EXPAND_THM]);

val ASL_IS_SUBSTATE___TRANS = store_thm ("ASL_IS_SUBSTATE___TRANS",
``!f s1 s2 s3. IS_SEPARATION_COMBINATOR f ==>
   (ASL_IS_SUBSTATE f s1 s2 /\ ASL_IS_SUBSTATE f s2 s3 ==>
    ASL_IS_SUBSTATE f s1 s3)``,
METIS_TAC[ASL_IS_SUBSTATE___IS_PREORDER, PreOrder, transitive_def]);


val ASL_OPTION_IS_SUBSTATE_def = Define `
   ASL_OPTION_IS_SUBSTATE (f:'a option -> 'a option -> 'a option) s0 s2 = ?s1. f s0 s1 = s2`;


val ASL_OPTION_IS_SUBSTATE_THM = store_thm ("ASL_OPTION_IS_SUBSTATE_THM",
``(!f s0 s2. (ASL_IS_SUBSTATE f s0 s2 ==> ASL_OPTION_IS_SUBSTATE f (SOME s0) (SOME s2))) /\
  (!f s0 s2. IS_SEPARATION_COMBINATOR f ==>
   (ASL_OPTION_IS_SUBSTATE f (SOME s0) (SOME s2) = ASL_IS_SUBSTATE f s0 s2))``,

SIMP_TAC std_ss [ASL_OPTION_IS_SUBSTATE_def, ASL_IS_SUBSTATE_def, IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
REPEAT STRIP_TAC THENL [
   PROVE_TAC[],
   METIS_TAC[option_CLAUSES]
]);


val ASL_OPTION_IS_SUBSTATE___IS_PREORDER = store_thm ("ASL_OPTION_IS_SUBSTATE___IS_PREORDER",
``!f. IS_SEPARATION_COMBINATOR f ==>
PreOrder (ASL_OPTION_IS_SUBSTATE f)``,

SIMP_TAC std_ss [PreOrder, reflexive_def, transitive_def, ASL_OPTION_IS_SUBSTATE_def,
   IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
REPEAT STRIP_TAC THENL [
   Cases_on `x` THENL [
      ASM_REWRITE_TAC[],
      METIS_TAC[]
   ],

   METIS_TAC[ASSOC_DEF]
]);



val ASL_OPTION_IS_SUBSTATE___MONOID_COMPATIBLE = store_thm ("ASL_OPTION_IS_SUBSTATE___MONOID_COMPATIBLE",
``!f x1 x2 y1 y2.
(IS_SEPARATION_COMBINATOR f /\ (ASL_OPTION_IS_SUBSTATE f y1 y2) /\
(ASL_OPTION_IS_SUBSTATE f x1 x2)) ==>
ASL_OPTION_IS_SUBSTATE f (f x1 y1) (f x2 y2)``,

SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM, ASL_OPTION_IS_SUBSTATE_def,
GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
GSYM LEFT_FORALL_IMP_THM] THEN
METIS_TAC[COMM_DEF, ASSOC_DEF]);



val COMM_MONOID_def = Define `
   COMM_MONOID f e = MONOID f e /\ COMM f`;


val COMM_MONOID_THM = store_thm ("COMM_MONOID_THM",
   ``COMM_MONOID f e = ASSOC f /\ COMM f /\ LEFT_ID f e``,

SIMP_TAC std_ss [COMM_MONOID_def, MONOID_DEF] THEN
EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
FULL_SIMP_TAC std_ss [LEFT_ID_DEF, RIGHT_ID_DEF] THEN
METIS_TAC[COMM_DEF]);


val IS_COMM_MONOID___asl_star_emp = store_thm ("IS_COMM_MONOID___asl_star_emp",
``!f. IS_SEPARATION_COMBINATOR f ==>
(COMM_MONOID (asl_star f) (asl_emp f))``,

REWRITE_TAC [COMM_MONOID_THM] THEN
REPEAT STRIP_TAC THENL [
   SIMP_TAC std_ss [ASSOC_DEF, asl_star_def,
      IN_ABS, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   SIMP_TAC std_ss [] THEN
   REPEAT GEN_TAC THEN EQ_TAC THENL [
      STRIP_TAC THEN
      Q.EXISTS_TAC `THE (f (SOME p) (SOME p'))` THEN
      Q.EXISTS_TAC `q'` THEN
      Q.EXISTS_TAC `p` THEN
      Q.EXISTS_TAC `p'` THEN
      FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
      `IS_SOME (f (SOME p) (SOME p'))` by METIS_TAC[optionTheory.option_CLAUSES, ASSOC_SYM] THEN
      ASM_SIMP_TAC std_ss [optionTheory.option_CLAUSES] THEN
      METIS_TAC[ASSOC_DEF],


      STRIP_TAC THEN
      Q.EXISTS_TAC `p'` THEN
      Q.EXISTS_TAC `THE (f (SOME q') (SOME q))` THEN
      Q.EXISTS_TAC `q'` THEN
      Q.EXISTS_TAC `q` THEN
      FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
      `IS_SOME (f (SOME q') (SOME q))` by METIS_TAC[optionTheory.option_CLAUSES, COMM_DEF, ASSOC_SYM] THEN
      ASM_SIMP_TAC std_ss [optionTheory.option_CLAUSES] THEN
      METIS_TAC[COMM_DEF, ASSOC_DEF]
   ],


   FULL_SIMP_TAC std_ss [COMM_DEF, asl_star_def, IS_SEPARATION_COMBINATOR_EXPAND_THM,
      FUN_EQ_THM] THEN
   METIS_TAC[],

   FULL_SIMP_TAC std_ss [LEFT_ID_DEF, asl_star_def, asl_emp_def, IN_ABS, EXTENSION,
      GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
   METIS_TAC[]
]);



(******************************************************************************)
(* Example: Separation algebra for finite maps                                *)
(* (used for later, more elaborate examples)                                  *)
(******************************************************************************)

val DISJOINT_FMAP_UNION_def = Define `
DISJOINT_FMAP_UNION =
BIN_OPTION_MAP FUNION (\m1 m2. DISJOINT (FDOM m1) (FDOM m2))`


val DISJOINT_FMAP_UNION___REWRITE_helper = prove (
   ``!x1 x2. COMM (DISJOINT_FMAP_UNION:('a |-> 'b) bin_option_function) /\
   ((DISJOINT_FMAP_UNION:('a |-> 'b) bin_option_function (SOME x1) (SOME x2) = (SOME x1)) = (x2 = FEMPTY)) /\
   ((DISJOINT_FMAP_UNION (SOME x1) (SOME x2) = (SOME x2)) = (x1 = FEMPTY))``,

SIMP_TAC std_ss [FORALL_AND_THM] THEN
MATCH_MP_TAC (prove (``(((A /\ B) ==> C) /\ A /\ B) ==> (A /\ B /\ C)``, METIS_TAC[])) THEN
REPEAT CONJ_TAC THENL [
   METIS_TAC[COMM_DEF],

   SIMP_TAC std_ss [DISJOINT_FMAP_UNION_def, BIN_OPTION_MAP_THM] THEN
   SIMP_TAC std_ss [COMM_DEF] THEN
   METIS_TAC[DISJOINT_SYM, FUNION_COMM],

   SIMP_TAC std_ss [DISJOINT_FMAP_UNION_def, BIN_OPTION_MAP_THM, COND_RAND, COND_RATOR] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
      MP_TAC (Q.SPECL [`x1`, `x2`, `FEMPTY`] FUNION_EQ) THEN
      ASM_SIMP_TAC std_ss [FUNION_FEMPTY_2, FDOM_FEMPTY,
         DISJOINT_EMPTY],

      ASM_SIMP_TAC std_ss [FUNION_FEMPTY_2, FDOM_FEMPTY,
         DISJOINT_EMPTY]
   ]
]);


val DISJOINT_FMAP_UNION___REWRITE = store_thm ("DISJOINT_FMAP_UNION___REWRITE",
``(DISJOINT_FMAP_UNION (SOME x1) (SOME x2) =
   (if ~DISJOINT (FDOM x1) (FDOM x2) then
      NONE
    else
      SOME (FUNION x1 x2))) /\ (DISJOINT_FMAP_UNION NONE x = NONE) /\
       (DISJOINT_FMAP_UNION x NONE = NONE) /\
       ((DISJOINT_FMAP_UNION s1 s2 = SOME x3) =
   ?x1 x2.
     (s1 = SOME x1) /\ (s2 = SOME x2) /\
     DISJOINT (FDOM x1) (FDOM x2) /\ (x3 = FUNION x1 x2)) /\
       ((DISJOINT_FMAP_UNION s1 s2 = NONE) =
   (s1 = NONE) \/ (s2 = NONE) \/
   ~DISJOINT (FDOM (THE s1)) (FDOM (THE s2))) /\
   ((DISJOINT_FMAP_UNION (SOME x1) (SOME x2) = (SOME x1)) = (x2 = FEMPTY)) /\
   ((DISJOINT_FMAP_UNION (SOME x1) (SOME x2) = (SOME x2)) = (x1 = FEMPTY)) /\
       (COMM DISJOINT_FMAP_UNION) /\
       (ASSOC DISJOINT_FMAP_UNION) /\
       (OPTION_IS_LEFT_CANCELLATIVE DISJOINT_FMAP_UNION) /\
       (OPTION_IS_RIGHT_CANCELLATIVE DISJOINT_FMAP_UNION) /\
       (IS_SOME (DISJOINT_FMAP_UNION s1 s2) =
   IS_SOME s1 /\ IS_SOME s2 /\
   DISJOINT (FDOM (THE s1)) (FDOM (THE s2)))``,

REWRITE_TAC [DISJOINT_FMAP_UNION___REWRITE_helper] THEN
SIMP_TAC std_ss [DISJOINT_FMAP_UNION_def, BIN_OPTION_MAP_THM, FDOM_FUNION,
   DISJOINT_UNION_BOTH, COMM_DEF, COND_RAND, COND_RATOR] THEN
REPEAT STRIP_TAC THENL [
   METIS_TAC[DISJOINT_SYM],
   METIS_TAC[FUNION_ASSOC],
   METIS_TAC[FUNION_EQ],
   METIS_TAC[FUNION_EQ, FUNION_COMM, DISJOINT_SYM]
]);


val DISJOINT_FMAP_UNION___CANCELLATIVE = store_thm ("DISJOINT_FMAP_UNION___CANCELLATIVE",
``((DISJOINT_FMAP_UNION (SOME x1) (SOME x2) = (SOME x)) /\
   (DISJOINT_FMAP_UNION (SOME x1) (SOME x2') = (SOME x)) ==>
   (x2' = x2)) /\
  ((DISJOINT_FMAP_UNION (SOME x1) (SOME x2) = (SOME x)) /\
   (DISJOINT_FMAP_UNION (SOME x1') (SOME x2) = (SOME x)) ==>
   (x1' = x1))``,
`OPTION_IS_RIGHT_CANCELLATIVE (DISJOINT_FMAP_UNION:('a |-> 'b) bin_option_function) /\
 OPTION_IS_LEFT_CANCELLATIVE (DISJOINT_FMAP_UNION:('a |-> 'b) bin_option_function)` by
     SIMP_TAC std_ss [DISJOINT_FMAP_UNION___REWRITE] THEN
REPEAT (POP_ASSUM (MP_TAC)) THEN
REWRITE_TAC [OPTION_IS_RIGHT_CANCELLATIVE_def, OPTION_IS_LEFT_CANCELLATIVE_def] THEN
METIS_TAC[optionTheory.option_CLAUSES]);


val IS_SEPARATION_ALGEBRA___FINITE_MAP = store_thm ("IS_SEPARATION_ALGEBRA___FINITE_MAP",
``IS_SEPARATION_ALGEBRA DISJOINT_FMAP_UNION FEMPTY``,
SIMP_TAC std_ss [IS_SEPARATION_ALGEBRA_def,
   DISJOINT_FMAP_UNION___REWRITE]);


val DISJOINT_FMAP_UNION___FEMPTY = store_thm ("DISJOINT_FMAP_UNION___FEMPTY",
``(!x. DISJOINT_FMAP_UNION (SOME FEMPTY) x = x) /\
  (!x. DISJOINT_FMAP_UNION x (SOME FEMPTY) = x)``,
REPEAT STRIP_TAC THEN
Cases_on `x` THEN
SIMP_TAC std_ss [DISJOINT_FMAP_UNION___REWRITE]);


val DISJOINT_FMAP_UNION___EQ_FEMPTY = store_thm ("DISJOINT_FMAP_UNION___EQ_FEMPTY",
``!x y. (DISJOINT_FMAP_UNION x y = (SOME FEMPTY)) =
        (x = SOME FEMPTY) /\ (y = SOME FEMPTY)``,

Cases_on `x` THEN
Cases_on `y` THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [DISJOINT_FMAP_UNION___REWRITE, FUNION_EQ_FEMPTY,
   FDOM_FEMPTY, DISJOINT_EMPTY]);


val IS_SEPARATION_COMBINATOR___FINITE_MAP = store_thm ("IS_SEPARATION_COMBINATOR___FINITE_MAP",
``IS_SEPARATION_COMBINATOR DISJOINT_FMAP_UNION``,

PROVE_TAC [IS_SEPARATION_ALGEBRA___IS_COMBINATOR,
   IS_SEPARATION_ALGEBRA___FINITE_MAP]);


val ASL_IS_SEPARATE___BIN_OPTION_MAP = store_thm ("ASL_IS_SEPARATE___BIN_OPTION_MAP",
``!f c x1 x2. (ASL_IS_SEPARATE (BIN_OPTION_MAP f c) x1 x2) = (c x1 x2)``,
SIMP_TAC std_ss [ASL_IS_SEPARATE_def, BIN_OPTION_MAP_THM]);

val ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION =
store_thm ("ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION",
``!s1 s2.
ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s1 s2 =
(FDOM s1 SUBSET FDOM s2 /\
(!x. x IN FDOM s1 ==> (s1 ' x = s2 ' x)))
``,

SIMP_TAC std_ss [ASL_IS_SUBSTATE_def,
       DISJOINT_FMAP_UNION_def,
       BIN_OPTION_MAP_THM,
       FUNION_DEF, COND_RATOR,
       COND_RAND] THEN
REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
   Q.PAT_ASSUM `X = s2` (ASSUME_TAC o GSYM) THEN
   ASM_SIMP_TAC std_ss [FUNION_DEF, SUBSET_UNION],


   Q.EXISTS_TAC `DRESTRICT s2 (COMPL (FDOM s1))` THEN
   FULL_SIMP_TAC std_ss [DRESTRICT_DEF, DISJOINT_DEF,
          EXTENSION, NOT_IN_EMPTY, IN_INTER,
          IN_COMPL, GSYM fmap_EQ_THM,
          FUNION_DEF, IN_UNION, SUBSET_DEF,
          DISJ_IMP_THM] THEN
   METIS_TAC[]
]);


val ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___IS_PREORDER =
store_thm ("ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___IS_PREORDER",

``PreOrder (ASL_IS_SUBSTATE DISJOINT_FMAP_UNION)``,

MATCH_MP_TAC ASL_IS_SUBSTATE___IS_PREORDER THEN
REWRITE_TAC [IS_SEPARATION_COMBINATOR___FINITE_MAP]);


val ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___TRANS =
    save_thm ("ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___TRANS",
CONJUNCT2 (
REWRITE_RULE[PreOrder, transitive_def] ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___IS_PREORDER));


val ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___REFL =
    save_thm ("ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___REFL",
CONJUNCT1 (
REWRITE_RULE[PreOrder, reflexive_def] ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___IS_PREORDER));



val ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FEMPTY =
store_thm ("ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FEMPTY",

``!s. ASL_IS_SUBSTATE DISJOINT_FMAP_UNION FEMPTY s``,

SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION,
       FDOM_FEMPTY, NOT_IN_EMPTY, EMPTY_SUBSET]);


val ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FUNION =
store_thm ("ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FUNION",

``!s s1 s2.
DISJOINT (FDOM s1) (FDOM s2) ==>

(ASL_IS_SUBSTATE DISJOINT_FMAP_UNION (FUNION s1 s2) s =

(ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s1 s /\
 ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s2 s))``,

SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION,
       FDOM_FUNION, IN_UNION, DISJ_IMP_THM,
       FORALL_AND_THM, UNION_SUBSET,
       FUNION_DEF, DISJOINT_DEF, EXTENSION,
       NOT_IN_EMPTY, IN_INTER] THEN
METIS_TAC[]);



val ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FUNION_2 =
store_thm ("ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION___FUNION_2",
``!s1 s2. ASL_IS_SUBSTATE DISJOINT_FMAP_UNION s1 (FUNION s1 s2)``,
SIMP_TAC std_ss [ASL_IS_SUBSTATE___DISJOINT_FMAP_UNION,
   FUNION_DEF, SUBSET_UNION]);


val asl_emp_DISJOINT_FMAP_UNION = store_thm ("asl_emp_DISJOINT_FMAP_UNION",
``asl_emp (DISJOINT_FMAP_UNION) = {FEMPTY}``,
MATCH_MP_TAC asl_emp_ALGEBRA THEN
REWRITE_TAC [IS_SEPARATION_ALGEBRA___FINITE_MAP]);



(******************************************************************************)
(* Basic separation logic definitions and rewrites                            *)
(******************************************************************************)

val asl_septraction_def = Define `
asl_septraction f P Q = \s.
?s1 s2. (SOME s2 = f (SOME s1) (SOME s)) /\ (s1 IN P) /\ (s2 IN Q)`;

val asl_magic_wand_def = Define `
asl_magic_wand f P Q = \s.
!s1 s2. ((SOME s2 = f (SOME s1) (SOME s)) /\ (s1 IN P)) ==> (s2 IN Q)`;

val asl_true_def = Define `asl_true = UNIV`;
val asl_false_def = Define `asl_false = EMPTY`;
val fasl_star_def = Define `fasl_star f = BIN_OPTION_MAP_ALL_DEF (asl_star f)`;


val asl_exists_def =
 Define `asl_exists = \P:'a->('b -> bool). \s. ?x. (s IN P x)`;
val _ = set_fixity "asl_exists" Binder;

val asl_forall_def =
 Define `asl_forall = \P:'a->('b -> bool). \s. !x. (s IN P x)`;
val _ = set_fixity "asl_forall" Binder

val asl_neg_def =
 Define `asl_neg = \P:('a -> bool). \s. ~(s IN P)`;

val asl_and_def =
 Define `asl_and = \P:('a set) Q:('a set). \s. (s IN P /\ s IN Q)`;

val asl_or_def =
 Define `asl_or = \P:('a set) Q:('a set). \s. (s IN P \/ s IN Q)`;

val asl_imp_def =
 Define `asl_imp = \P:('a set) Q:('a set). \s. (s IN P ==> s IN Q)`;

val asl_cond_def =
 Define `asl_cond = \X P:('a set) Q:('a set). \s. (if s IN X then s IN P else s IN Q)`;

val asl_trivial_cond_def =
 Define `asl_trivial_cond = \c P. if c then P else asl_false`

val asl_and_intro = store_thm ("asl_and_intro",
``(\s. P s /\ Q s) = asl_and P Q``,
SIMP_TAC std_ss [asl_and_def, IN_DEF]);


val asl_bigand_list_def = Define `
   asl_bigand_list l =  FOLDR asl_and asl_true l`

val asl_bigand_list_REWRITE = store_thm ("asl_bigand_list_REWRITE",
``      (asl_bigand_list [] =  asl_true) /\
   (asl_bigand_list (h::l) =  asl_and h (asl_bigand_list l))``,

SIMP_TAC list_ss [asl_bigand_list_def, FOLDR_APPEND]);


val asl_bigand_list_THM = store_thm ("asl_bigand_list_THM",
``asl_bigand_list l = \s. EVERY (\P. P s) l``,

ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
Induct_on `l` THENL [
   SIMP_TAC list_ss [asl_bigand_list_def, asl_true_def, UNIV_DEF],
   FULL_SIMP_TAC list_ss [asl_bigand_list_def, asl_and_def, IN_DEF]
]);


val ASL_BOOL___PRED_SET_REWRITES = store_thm ("ASL_BOOL___PRED_SET_REWRITES",
   ``(asl_neg = COMPL) /\
      (asl_and = $INTER) /\
      (asl_or = $UNION) /\
      (asl_true = UNIV) /\
      (asl_false = EMPTY) /\
      ((!x. x IN (asl_imp s t)) = (s SUBSET t)) /\
      ((asl_exists s. P s) = BIGUNION (IMAGE P UNIV)) /\
      ((asl_forall s. P s) = BIGINTER (IMAGE P UNIV))``,

SIMP_TAC std_ss [asl_neg_def, asl_and_def, asl_or_def,
   asl_true_def, asl_false_def, SUBSET_DEF, asl_imp_def,
   IN_ABS, asl_cond_def] THEN
REPEAT STRIP_TAC THENL [
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   SIMP_TAC std_ss [EXTENSION, IN_ABS, IN_COMPL],

   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_ABS],

   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_ABS],

   SIMP_TAC std_ss [EXTENSION] THEN
   SIMP_TAC std_ss [asl_exists_def, IN_ABS,
      IN_BIGUNION, IN_IMAGE, IN_UNIV] THEN
   METIS_TAC[],

   SIMP_TAC std_ss [EXTENSION] THEN
   SIMP_TAC std_ss [asl_forall_def, IN_ABS,
      IN_BIGINTER, IN_IMAGE, IN_UNIV] THEN
   METIS_TAC[]
]);



val asl_and_INTRO_COND = store_thm ("asl_and_INTRO_COND",
``!c P. (if c then P else asl_false) = asl_and (K c) P``,

Cases_on `c` THEN
SIMP_TAC std_ss [asl_and_def, combinTheory.K_DEF, IN_ABS,
       IN_ABS3, asl_false_def, EMPTY_DEF]);


val asl_exists___GSYM_REWRITE = store_thm ("asl_exists___GSYM_REWRITE",
``(\s. ?x. P x s) = (asl_exists x. P x)``,
SIMP_TAC std_ss [asl_exists_def, IN_DEF]);



val asl_exists___asl_star_THM = store_thm ("asl_exists___asl_star_THM",
``!f P Q.
((asl_exists x. asl_star f (P x) Q) = (asl_star f (asl_exists x. (P x)) Q)) /\
((asl_exists x. asl_star f Q (P x)) = (asl_star f Q (asl_exists x. (P x))))``,

SIMP_TAC std_ss [asl_exists_def, asl_star_def, IN_ABS] THEN
SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
SIMP_TAC std_ss [FUN_EQ_THM] THEN
REPEAT STRIP_TAC THEN (
   EQ_TAC THEN STRIP_TAC THEN      METIS_TAC[]
));


val asl_exists_ELIM = store_thm ("asl_exists_ELIM",
``!P. (asl_exists x. P) = P``,
SIMP_TAC std_ss[EXTENSION, asl_exists_def, IN_ABS]);


val SWAP_asl_exists_THM = store_thm ("SWAP_asl_exists_THM",
   ``!P. (asl_exists x y. P x y) = (asl_exists y x. P x y)``,

SIMP_TAC std_ss [FUN_EQ_THM, asl_exists_def, IN_ABS] THEN
METIS_TAC[]);


val asl_exists___asl_and_THM = store_thm ("asl_exists___asl_and_THM",
``!P Q.
((asl_exists x. asl_and (P x) Q) = (asl_and (asl_exists x. (P x)) Q)) /\
((asl_exists x. asl_and Q (P x)) = (asl_and Q (asl_exists x. (P x))))``,

SIMP_TAC std_ss [asl_exists_def, asl_and_def, IN_ABS] THEN
METIS_TAC[]);


val asl_exists___asl_or_THM = store_thm ("asl_exists___asl_or_THM",
``!P Q.
((asl_exists x. asl_or (P x) (Q x)) = (asl_or (asl_exists x. (P x)) (asl_exists x. (Q x))))``,
SIMP_TAC std_ss [asl_exists_def, asl_or_def, IN_ABS] THEN
METIS_TAC[]);


val fasl_star_REWRITE = save_thm ("fasl_star_REWRITE",
   let
      val thm = (GEN ``f:'a ->'a ->'a`` BIN_OPTION_MAP_ALL_DEF_THM);
      val thm2 = ISPEC ``asl_star f`` thm;
      val thm3 = REWRITE_RULE [GSYM fasl_star_def] thm2;
   in
      thm3
   end);

val fasl_star_DIRECT_DEF = store_thm ("fasl_star_DIRECT_DEF",
``(fasl_star f NONE Qopt = NONE) /\
  (fasl_star f Popt NONE = NONE) /\
  (fasl_star f (SOME P) (SOME Q) = SOME (asl_star f P Q))``,
SIMP_TAC std_ss [fasl_star_REWRITE]);

val asl_star___PROPERTIES = save_thm ("asl_star___PROPERTIES",
SIMP_RULE std_ss [COMM_MONOID_def, MONOID_DEF,
   LEFT_ID_DEF, RIGHT_ID_DEF] IS_COMM_MONOID___asl_star_emp);


val asl_star___swap = store_thm ("asl_star___swap",
``!f p1 p2 p3. IS_SEPARATION_COMBINATOR f ==>
  (asl_star f p1 (asl_star f p2 p3) =
   asl_star f p2 (asl_star f p1 p3))``,
METIS_TAC[ASSOC_DEF, COMM_DEF, asl_star___PROPERTIES]);

val asl_false___asl_star_THM = store_thm ("asl_false___asl_star_THM",
``(asl_star f x asl_false = asl_false) /\
   (asl_star f asl_false x = asl_false)``,

SIMP_TAC std_ss [EXTENSION, asl_star_def, IN_ABS, asl_false_def, NOT_IN_EMPTY]);


val asl_true___asl_star_THM = store_thm ("asl_true___asl_star_THM",
``IS_SEPARATION_COMBINATOR f ==>
(asl_star f asl_true asl_true = asl_true)``,

SIMP_TAC std_ss [EXTENSION, asl_star_def, IN_ABS, asl_true_def, IN_UNIV,
       IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `x` THEN
Q.EXISTS_TAC `uf x` THEN
ASM_REWRITE_TAC[]);


val asl_trivial_cond_TF = store_thm ("asl_trivial_cond_TF",
``(!P. (asl_trivial_cond T P = P)) /\
  (!P. ((asl_trivial_cond F P) = asl_false))``,
SIMP_TAC std_ss [asl_trivial_cond_def]);

val asl_trivial_cond___INTRO = store_thm ("asl_trivial_cond___INTRO",
``!c P. c ==> (P = asl_trivial_cond c P)``,
SIMP_TAC std_ss [asl_trivial_cond_def]);


val asl_trivial_cond___asl_false = store_thm ("asl_trivial_cond___asl_false",
``!c. (asl_trivial_cond c asl_false = asl_false)``,
SIMP_TAC std_ss [asl_trivial_cond_def]);


val asl_trivial_cond___asl_star = store_thm ("asl_trivial_cond___asl_star",
``(!f c p1 p2. asl_star f (asl_trivial_cond c p1) p2 =
               asl_trivial_cond c (asl_star f p1 p2)) /\
  (!f c p1 p2. asl_star f p1 (asl_trivial_cond c p2) =
               asl_trivial_cond c (asl_star f p1 p2))``,
SIMP_TAC std_ss [asl_trivial_cond_def, COND_RAND, COND_RATOR,
   asl_false___asl_star_THM]);


val asl_trivial_cond___asl_trivial_cond = store_thm ("asl_trivial_cond___asl_trivial_cond",
``!c1 c2 p.
      asl_trivial_cond c1 (asl_trivial_cond c2 p) =
      asl_trivial_cond (c1 /\ c2) p``,
SIMP_TAC std_ss [asl_trivial_cond_def] THEN
METIS_TAC[]);


val asl_bigstar_list_def = Define `
   asl_bigstar_list f l =  FOLDR (asl_star f) (asl_emp f) l`

val asl_bigstar_list_REWRITE = store_thm ("asl_bigstar_list_REWRITE",
``(!f. (asl_bigstar_list f [] =  asl_emp f)) /\
  (!f h l. (asl_bigstar_list f (h::l) =  asl_star f h (asl_bigstar_list f l)))``,
SIMP_TAC list_ss [asl_bigstar_list_def, FOLDR_APPEND]);


val asl_bigstar_list_SNOC = store_thm ("asl_bigstar_list_SNOC",
``!f h l. IS_SEPARATION_COMBINATOR f ==>
   (asl_bigstar_list f (SNOC h l) =  asl_star f (asl_bigstar_list f l) h)``,
Induct_on `l` THEN
ASM_SIMP_TAC list_ss [asl_bigstar_list_REWRITE,
   REWRITE_RULE [ASSOC_DEF] asl_star___PROPERTIES]);


val asl_bigstar_list_APPEND = store_thm ("asl_bigstar_list_APPEND",
``!f l1 l2. IS_SEPARATION_COMBINATOR f ==>
   (asl_bigstar_list f (l1++l2) =  asl_star f (asl_bigstar_list f l1) (asl_bigstar_list f l2))``,

Induct_on `l1` THENL [
   SIMP_TAC list_ss [asl_bigstar_list_REWRITE] THEN
   METIS_TAC[asl_star___PROPERTIES],

   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC list_ss [asl_bigstar_list_REWRITE] THEN
   IMP_RES_TAC asl_star___PROPERTIES THEN
   METIS_TAC[COMM_DEF, ASSOC_DEF]
]);


val asl_bigstar_list_FLATTEN = store_thm ("asl_bigstar_list_FLATTEN",
``!f l0 l1 l2. IS_SEPARATION_COMBINATOR f ==>
   (asl_bigstar_list f (l0 ++(asl_bigstar_list f l1)::l2) =  asl_bigstar_list f (l0 ++ l1++l2))``,

SIMP_TAC std_ss [asl_bigstar_list_APPEND, asl_bigstar_list_REWRITE] THEN
REPEAT STRIP_TAC THEN
IMP_RES_TAC asl_star___PROPERTIES THEN
METIS_TAC[COMM_DEF, ASSOC_DEF]
);


val asl_bigstar_list_false = store_thm ("asl_bigstar_list_false",
``!f L. MEM (asl_false) L ==> (asl_bigstar_list f L = asl_false)``,
GEN_TAC THEN Induct_on `L` THEN
ASM_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM, asl_bigstar_list_REWRITE,
            asl_false___asl_star_THM]);


val asl_bigstar_def = Define `
   asl_bigstar f b =  if (FINITE_BAG b) then asl_bigstar_list f (BAG_TO_LIST b) else asl_false`

val asl_bigstar_list_PERM = store_thm ("asl_bigstar_list_PERM",
``!f l1 l2.
IS_SEPARATION_COMBINATOR f /\
(PERM l1 l2) ==>
(asl_bigstar_list f l1 = asl_bigstar_list f l2)``,

SIMP_TAC std_ss [asl_bigstar_list_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] FOLDR_PERM) THEN
IMP_RES_TAC asl_star___PROPERTIES THEN
ASM_REWRITE_TAC[]);


val asl_bigstar_list_REVERSE = store_thm ("asl_bigstar_list_REVERSE",
``!f l.
IS_SEPARATION_COMBINATOR f ==>
(asl_bigstar_list f (REVERSE l) = asl_bigstar_list f l)``,
METIS_TAC[asl_bigstar_list_PERM, PERM_REVERSE]);


val asl_star___PROPERTIES___EVAL = store_thm ("asl_star___PROPERTIES___EVAL",
``!f. IS_SEPARATION_COMBINATOR f ==>
      (!P1 P2 P3. (asl_star f (asl_star f P1 P2) P3 =
         asl_star f P1 (asl_star f P2 P3))) /\
      (!P. asl_star f (asl_emp f) P = P) /\
      (!P. asl_star f P (asl_emp f) = P) /\
      (!P. asl_star f asl_false P = asl_false) /\
      (!P. asl_star f P asl_false = asl_false) /\
      (!P. asl_bigstar_list f [P] = P) /\
      (asl_bigstar_list f [] = asl_emp f) /\
      (!P1 P2 PL. asl_bigstar_list f (P1::P2::PL) =
     asl_star f P1 (asl_bigstar_list f (P2::PL)))``,

      SIMP_TAC std_ss [asl_star___PROPERTIES, asl_false___asl_star_THM,
    asl_bigstar_list_REWRITE] THEN
      METIS_TAC[asl_star___PROPERTIES, ASSOC_DEF])


val asl_bigstar_EMPTY = store_thm ("asl_bigstar_EMPTY",
``!f. (asl_bigstar f {| |} = asl_emp f)``,
SIMP_TAC list_ss [asl_bigstar_def, FINITE_BAG_THM,
        BAG_TO_LIST_THM, asl_bigstar_list_def]);



val asl_bigstar_REWRITE = store_thm ("asl_bigstar_REWRITE",
``!f. IS_SEPARATION_COMBINATOR f ==>
((asl_bigstar f {| |} = asl_emp f) /\
(!b e. (asl_bigstar f (BAG_INSERT e b) = asl_star f e (asl_bigstar f b))))``,

REPEAT STRIP_TAC THENL [
   SIMP_TAC list_ss [asl_bigstar_def, FINITE_BAG_THM,
      BAG_TO_LIST_THM, asl_bigstar_list_def],

   SIMP_TAC list_ss [asl_bigstar_def, FINITE_BAG_THM] THEN
   Tactical.REVERSE (Cases_on `(FINITE_BAG b)`) THEN1 (
      ASM_SIMP_TAC std_ss [asl_false___asl_star_THM]
   ) THEN
   ASM_REWRITE_TAC[GSYM asl_bigstar_list_REWRITE] THEN
   MATCH_MP_TAC asl_bigstar_list_PERM THEN
   ASM_SIMP_TAC std_ss [GSYM PERM_LIST_TO_BAG, LIST_TO_BAG_def,
      BAG_TO_LIST_INV, FINITE_BAG_THM]
]);



val asl_bigstar_INTRO = store_thm ("asl_bigstar_INTRO",
``!f. IS_SEPARATION_COMBINATOR f ==>
((!e. asl_star f e (asl_emp f) = (asl_bigstar f (BAG_INSERT e {| |}))) /\
(!b e. asl_star f e (asl_bigstar f b) = (asl_bigstar f (BAG_INSERT e b))))``,

SIMP_TAC std_ss [asl_bigstar_REWRITE]);



val asl_bigstar_UNION = store_thm ("asl_bigstar_UNION",
``!f. IS_SEPARATION_COMBINATOR f ==>
(!b1 b2. (asl_bigstar f (BAG_UNION b1 b2) = asl_star f (asl_bigstar f b1) (asl_bigstar f b2)))``,

SIMP_TAC std_ss [asl_bigstar_def, FINITE_BAG_UNION] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `FINITE_BAG b1`) THEN1 (
   ASM_SIMP_TAC std_ss [asl_false___asl_star_THM]
) THEN
Tactical.REVERSE (Cases_on `FINITE_BAG b2`) THEN1 (
   ASM_SIMP_TAC std_ss [asl_false___asl_star_THM]
) THEN
ASM_SIMP_TAC std_ss [GSYM asl_bigstar_list_APPEND] THEN
MATCH_MP_TAC asl_bigstar_list_PERM THEN
ASM_SIMP_TAC std_ss [GSYM PERM_LIST_TO_BAG, LIST_TO_BAG_def,
   BAG_TO_LIST_INV, FINITE_BAG_THM, LIST_TO_BAG_APPEND,
   FINITE_BAG_UNION]);



val asl_bigstar_FLATTEN = store_thm ("asl_bigstar_FLATTEN",
``!f.
IS_SEPARATION_COMBINATOR f ==>
(!b1 b2. (asl_bigstar f (BAG_INSERT (asl_bigstar f b1) b2) =
asl_bigstar f (BAG_UNION b1 b2)))``,

SIMP_TAC std_ss [asl_bigstar_UNION, asl_bigstar_REWRITE]);



val asl_bigstar_list___DEF2 = store_thm ("asl_bigstar_list___DEF2",
``!f l. IS_SEPARATION_COMBINATOR f ==>
(asl_bigstar_list f l = asl_bigstar f (LIST_TO_BAG l))``,

Induct_on `l` THEN (
   ASM_SIMP_TAC std_ss [asl_bigstar_list_REWRITE, asl_bigstar_REWRITE,
      LIST_TO_BAG_def]
));


val asl_bool_REWRITES = store_thm ("asl_bool_REWRITES",
``($! asl_true) /\
  ($? asl_true) /\
  ~($! asl_false) /\
  ~($? asl_false) /\
  ((K T) = asl_true) /\
  ((\x. T) = asl_true) /\
  ((K F) = asl_false) /\
  ((\x. F) = asl_false) /\
  (asl_and asl_false p = asl_false) /\
  (asl_and p asl_false = asl_false) /\
  (asl_and asl_true p = p) /\
  (asl_and p asl_true = p) /\
  (asl_or asl_false p = p) /\
  (asl_or p asl_false = p) /\
  (asl_or asl_true p = asl_true) /\
  (asl_or p asl_true = asl_true)``,

ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [asl_true_def, IN_UNIV, asl_false_def,
   NOT_IN_EMPTY, asl_and_def, IN_ABS, asl_or_def] THEN
SIMP_TAC std_ss [IN_DEF, UNIV_DEF, EMPTY_DEF]);


val asl_bool_EVAL = store_thm ("asl_bool_EVAL",
``(asl_true x) /\ (x IN asl_true) /\
  ~(asl_false x) /\ ~(x IN asl_false) /\
  ((K c) x = c) /\ (x IN (K c) = c) /\
  ((asl_and p1 p2) x = (x IN p1) /\ (x IN p2)) /\
  (x IN (asl_and p1 p2) = (x IN p1) /\ (x IN p2)) /\
  ((asl_or p1 p2) x = (x IN p1) \/ (x IN p2)) /\
  (x IN (asl_or p1 p2) = (x IN p1) \/ (x IN p2)) /\
  ((asl_imp p1 p2) x = ((x IN p1) ==> (x IN p2))) /\
  (x IN (asl_imp p1 p2) = ((x IN p1) ==> (x IN p2))) /\
  ((asl_neg p) x = (~(x IN p))) /\
  (x IN (asl_neg p) = (~(x IN p))) /\
  ((asl_forall y. (qp y)) x = (!y. x IN (qp y))) /\
  (x IN (asl_forall y. (qp y)) = (!y. x IN (qp y))) /\
  ((asl_exists y. (qp y)) x = (?y. x IN (qp y))) /\
  (x IN (asl_exists y. (qp y)) = (?y. x IN (qp y))) /\
  (x IN asl_trivial_cond c p = c /\ x IN p) /\
  (asl_trivial_cond c p x = c /\ x IN p)``,

SIMP_TAC std_ss [asl_true_def, asl_false_def, asl_and_def,
  asl_or_def, IN_DEF, EMPTY_DEF, UNIV_DEF,
  asl_imp_def, asl_neg_def, asl_forall_def,
  asl_exists_def, asl_trivial_cond_def] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR]);

val NOT_IN_asl_false = store_thm ("NOT_IN_asl_false",
``!x. ~(x IN asl_false)``, REWRITE_TAC[asl_bool_EVAL])


val asl_bigstar_list___WEAKEN = store_thm ("asl_bigstar_list___WEAKEN",
``!f l1 l2. ((LENGTH l1 = LENGTH l2) /\
      (EVERY (\(P1, P2). !s. P1 s ==> P2 s) (ZIP(l1,l2)))) ==>

(!s. asl_bigstar_list f l1 s ==> asl_bigstar_list f l2 s)``,

Induct_on `l2` THEN1 (
   SIMP_TAC list_ss [LENGTH_NIL]
) THEN
Cases_on `l1` THEN SIMP_TAC list_ss [] THEN
SIMP_TAC std_ss [asl_bigstar_list_REWRITE, asl_star_def] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `p` THEN
Q.EXISTS_TAC `q` THEN
ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[IN_DEF]);


val asl_exists_list_def = Define `
asl_exists_list = \L P s. ?l. (LENGTH l = LENGTH L) /\ s IN P l`

val asl_exists_list___ELIM = store_thm ("asl_exists_list___ELIM",
``asl_exists_list L P = $asl_exists (\l. asl_trivial_cond (LENGTH l = LENGTH L) (P l))``,
SIMP_TAC std_ss [asl_exists_list_def, asl_trivial_cond_def, asl_exists_def,
   EXTENSION, COND_RAND, COND_RATOR, IN_ABS, asl_bool_EVAL])


val asl_exists_list___REWRITE = store_thm ("asl_exists_list___REWRITE",
``(!P. asl_exists_list [] P = P []) /\
  (!e es P. asl_exists_list (e::es) P =
     asl_exists x. (asl_exists_list es (\l. P (x::l))))``,
SIMP_TAC list_ss [asl_exists_list_def, EXTENSION, IN_ABS,
   asl_bool_EVAL, asl_exists_def, LENGTH_EQ_NUM,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM]);


(******************************************************************************)
(* Precise                                                                    *)
(******************************************************************************)

val _ = hide "ASL_IS_PRECISE";
val ASL_IS_PRECISE_def = Define `
   ASL_IS_PRECISE (f:'a option -> 'a option -> 'a option) (p:'a set) =
   !x y1 y2. (y1 IN p /\ y2 IN p /\ ASL_IS_SUBSTATE f y1 x /\ ASL_IS_SUBSTATE f y2 x)==> (y1 = y2)`;

val ASL_IS_PRECISE_IN_STATE_def = Define `
   ASL_IS_PRECISE_IN_STATE (f:'a option -> 'a option -> 'a option) (p:'a set) x =
   !y1 y2. (y1 IN p /\ y2 IN p /\ ASL_IS_SUBSTATE f y1 x /\ ASL_IS_SUBSTATE f y2 x)==> (y1 = y2)`;

val ASL_IS_PRECISE___IN_STATE___THM = store_thm ("ASL_IS_PRECISE___IN_STATE___THM",
   ``ASL_IS_PRECISE f p = !x. ASL_IS_PRECISE_IN_STATE f p x``,
SIMP_TAC std_ss [ASL_IS_PRECISE_def, ASL_IS_PRECISE_IN_STATE_def]);


val ASL_IS_PRECISE___SING = store_thm ("ASL_IS_PRECISE___SING",
``!p f. SING p ==> ASL_IS_PRECISE f p``,

SIMP_TAC std_ss [ASL_IS_PRECISE_def, SING_DEF, GSYM LEFT_FORALL_IMP_THM,
IN_SING]);


val IS_PRECISE___CHARACTERISATION = store_thm ("IS_PRECISE___CHARACTERISATION",
``!f p.
IS_SEPARATION_COMBINATOR f ==>

(ASL_IS_PRECISE f p =
!X. ~(X = EMPTY) ==> (
(asl_star f (BIGINTER X) p =
     BIGINTER (IMAGE (\x. asl_star f x p) X))))``,


SIMP_TAC std_ss [asl_star_def, IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [IN_ABS, IN_UNIV, ASL_IS_SEPARATE_def, IN_BIGINTER, NOT_IN_EMPTY,
   IN_IMAGE, ASL_IS_PRECISE_def, ASL_IS_SUBSTATE_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
   EQ_TAC THEN REPEAT STRIP_TAC THEN1 (
      METIS_TAC[]
   ) THEN
   RES_TAC THEN

   Q.EXISTS_TAC `p'` THEN
   Q.EXISTS_TAC `q` THEN
   ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN
   `?p' q. (SOME x' = f (SOME p') (SOME q)) /\ p' IN P /\ q IN p` by METIS_TAC[] THEN
   `q = q'` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `!x y1 y2. Z x y1 y2` MATCH_MP_TAC THEN
      ASM_SIMP_TAC std_ss [] THEN
      Q.EXISTS_TAC `x'` THEN
      Q.EXISTS_TAC `p'` THEN
      Q.EXISTS_TAC `p''` THEN
      METIS_TAC[COMM_DEF]
   ) THEN
   `p' = p''` by METIS_TAC[OPTION_IS_RIGHT_CANCELLATIVE_def, optionTheory.option_CLAUSES] THEN
   ASM_REWRITE_TAC[],


   Q.PAT_ASSUM `!X x. P X x` MP_TAC THEN
   SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
   Q.EXISTS_TAC `{{s1};{s1'}}` THEN
   Q.EXISTS_TAC `{s1}` THEN
   SIMP_TAC std_ss [IN_INSERT, NOT_IN_EMPTY, DISJ_IMP_THM, FORALL_AND_THM, GSYM LEFT_EXISTS_IMP_THM] THEN
   Q.EXISTS_TAC `x` THEN
   STRIP_TAC THEN
   `s1 = s1'` by METIS_TAC[COMM_DEF] THEN
   METIS_TAC[OPTION_IS_RIGHT_CANCELLATIVE_def, option_CLAUSES]
]);



val asl_star___ASL_IS_PRECISE = store_thm ("asl_star___ASL_IS_PRECISE",
``!f p1 p2.
(IS_SEPARATION_COMBINATOR f /\
ASL_IS_PRECISE f p1 /\ ASL_IS_PRECISE f p2) ==>

ASL_IS_PRECISE f (asl_star f p1 p2)``,

ASM_REWRITE_TAC[IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
SIMP_TAC std_ss [ASL_IS_PRECISE_def, ASL_IS_SUBSTATE_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
GSYM LEFT_EXISTS_IMP_THM, GSYM LEFT_FORALL_IMP_THM, asl_star_def, IN_ABS, ASSOC_SYM] THEN
REPEAT STRIP_TAC THEN
REPEAT (Q.PAT_ASSUM `X = SOME x` MP_TAC) THEN
ASM_REWRITE_TAC[] THEN
Cases_on `f (SOME q) (SOME s1)` THEN1 ASM_SIMP_TAC std_ss [] THEN
Cases_on `f (SOME q') (SOME s1')` THEN1 ASM_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN
`p' = p` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `!x y1 y2. X x y1 y2` (K ALL_TAC) THEN
   Q.PAT_ASSUM `!x y1 y2. X x y1 y2` MATCH_MP_TAC THEN
   Q.EXISTS_TAC `x` THEN
   Q.EXISTS_TAC `x''` THEN
   Q.EXISTS_TAC `x'` THEN
   ASM_REWRITE_TAC[]
) THEN
`SOME x' = SOME x''` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `OPTION_IS_LEFT_CANCELLATIVE f` (MATCH_MP_TAC o REWRITE_RULE [OPTION_IS_LEFT_CANCELLATIVE_def]) THEN
   Q.EXISTS_TAC `SOME p` THEN
   ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[]
) THEN
`q' = q` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `!x y1 y2. X x y1 y2` MATCH_MP_TAC THEN
   Q.EXISTS_TAC `x'` THEN
   Q.EXISTS_TAC `s1'` THEN
   Q.EXISTS_TAC `s1` THEN
   ASM_REWRITE_TAC[]
) THEN
METIS_TAC[]);





(******************************************************************************)
(* Cross-products of separation combinators                                   *)
(******************************************************************************)

val PRODUCT_SEPARATION_COMBINATOR_def = Define `
   (PRODUCT_SEPARATION_COMBINATOR (f1:'a bin_option_function) (f2:'b bin_option_function) NONE _ = NONE) /\
   (PRODUCT_SEPARATION_COMBINATOR f1 f2 _ NONE = NONE) /\
   (PRODUCT_SEPARATION_COMBINATOR f1 f2 (SOME (x1,x2)) (SOME (y1,y2)) =
      let z1 = f1 (SOME x1) (SOME y1) in
      let z2 = f2 (SOME x2) (SOME y2) in
      if (IS_SOME z1 /\ IS_SOME z2) then
         SOME (THE z1, THE z2)
      else
         NONE)`;


val PRODUCT_SEPARATION_COMBINATOR_REWRITE = store_thm ("PRODUCT_SEPARATION_COMBINATOR_REWRITE",
``(PRODUCT_SEPARATION_COMBINATOR f1 f2 X NONE = NONE) /\
(PRODUCT_SEPARATION_COMBINATOR f1 f2 NONE X = NONE) /\
(PRODUCT_SEPARATION_COMBINATOR f1 f2 (SOME x) (SOME y) =
   let z1 = f1 (SOME (FST x)) (SOME (FST y)) in
   let z2 = f2 (SOME (SND x)) (SOME (SND y)) in
   if (IS_SOME z1 /\ IS_SOME z2) then
      SOME (THE z1, THE z2)
   else
      NONE) /\
((PRODUCT_SEPARATION_COMBINATOR f1 f2 (SOME x) (SOME y) = SOME z) =
   (f1 (SOME (FST x)) (SOME (FST y)) = SOME (FST z)) /\
   (f2 (SOME (SND x)) (SOME (SND y)) =  SOME (SND z)))
``,

REPEAT STRIP_TAC THENL [
   Cases_on `X` THEN1 (
      SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_def]
   ) THEN
   Cases_on `x` THEN
   SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_def],

   Cases_on `X` THEN
   SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_def],

   Cases_on `x` THEN Cases_on `y` THEN
   SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_def],


   Cases_on `x` THEN Cases_on `y` THEN Cases_on `z` THEN (
      SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_def]
   ) THEN
   SIMP_TAC std_ss [LET_THM, COND_RAND, COND_RATOR] THEN
   METIS_TAC[option_CLAUSES]
]);



val PRODUCT_SEPARATION_COMBINATOR_THM = store_thm ("PRODUCT_SEPARATION_COMBINATOR_THM",
``!f1 f2.
IS_SEPARATION_COMBINATOR f1 /\
IS_SEPARATION_COMBINATOR f2 ==>
IS_SEPARATION_COMBINATOR (PRODUCT_SEPARATION_COMBINATOR f1 f2)``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_def] THEN
`!x. (PRODUCT_SEPARATION_COMBINATOR f1 f2 NONE x = NONE) /\
       (PRODUCT_SEPARATION_COMBINATOR f1 f2 x NONE = NONE)` by ALL_TAC THEN1 (

   SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_REWRITE]
) THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN

REPEAT STRIP_TAC THENL [
   `?x1 x2. x = (x1, x2)` by ALL_TAC THEN1 (
      Cases_on `x` THEN
      SIMP_TAC std_ss []
   ) THEN
   Q.EXISTS_TAC `(uf x1, uf' x2)` THEN
   ASM_SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_def, LET_THM],


   SIMP_TAC std_ss [COMM_DEF] THEN
   REPEAT GEN_TAC THEN
   Cases_on `x` THEN Cases_on `y` THEN (
      ASM_SIMP_TAC std_ss []
   ) THEN
   Cases_on `x` THEN
   Cases_on `x'` THEN
   SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_def] THEN
   METIS_TAC[COMM_DEF],


   SIMP_TAC std_ss [ASSOC_DEF] THEN
   Cases_on `x` THEN Cases_on `y` THEN Cases_on `z` THEN (
      ASM_SIMP_TAC std_ss []
   ) THEN
   Cases_on `x` THEN
   Cases_on `x'` THEN
   Cases_on `x''` THEN
   ASM_SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_def, LET_THM,
      COND_RAND, COND_RATOR] THEN
   ASM_SIMP_TAC std_ss [COND_EXPAND_IMP, option_CLAUSES] THEN
   REPEAT STRIP_TAC THENL [
      METIS_TAC[ASSOC_DEF, NONE_IS_NOT_SOME],
      METIS_TAC[ASSOC_DEF, NONE_IS_NOT_SOME],

      Cases_on `IS_SOME (f1 (SOME q') (SOME q))` THEN (
         METIS_TAC[ASSOC_DEF, NONE_IS_NOT_SOME, option_CLAUSES]
      ),

      Cases_on `IS_SOME (f2 (SOME r') (SOME r))` THEN (
         METIS_TAC[ASSOC_DEF, NONE_IS_NOT_SOME, option_CLAUSES]
      ),

      Cases_on `IS_SOME (f1 (SOME q') (SOME q))` THEN (
         METIS_TAC[ASSOC_DEF, NONE_IS_NOT_SOME, option_CLAUSES]
      ),

      Cases_on `IS_SOME (f2 (SOME r') (SOME r))` THEN (
         METIS_TAC[ASSOC_DEF, NONE_IS_NOT_SOME, option_CLAUSES]
      ),

      METIS_TAC[ASSOC_DEF],
      METIS_TAC[ASSOC_DEF],
      METIS_TAC[ASSOC_DEF],
      METIS_TAC[ASSOC_DEF]
   ],


   SIMP_TAC std_ss [OPTION_IS_LEFT_CANCELLATIVE_def] THEN
   Cases_on `x1` THEN Cases_on `x2` THEN Cases_on `x3` THEN (
      ASM_SIMP_TAC std_ss []
   ) THEN
   `?x1 x2 y1 y2 z1 z2.
      (x = (x1, x2)) /\ (x' = (y1, y2)) /\ (x'' = (z1, z2))` by METIS_TAC[pairTheory.PAIR] THEN
   ASM_SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_def,
      LET_THM, COND_RAND, COND_RATOR] THEN
   SIMP_TAC std_ss [COND_EXPAND_IMP, option_CLAUSES, DISJ_IMP_THM,
      NOT_NONE_IS_SOME] THEN
   STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN
   `!X Y. (IS_SOME X /\ IS_SOME Y) ==> ((THE X = THE Y) = (X = Y))` by ALL_TAC THEN1 (
      METIS_TAC[option_CLAUSES]
   ) THEN
   METIS_TAC[OPTION_IS_LEFT_CANCELLATIVE_def, option_CLAUSES]
]);



val PRODUCT_SEPARATION_COMBINATOR___NEUTRAL_ELEMENT_FUNCTION = store_thm (
"PRODUCT_SEPARATION_COMBINATOR___NEUTRAL_ELEMENT_FUNCTION",
``
!f1 f2 uf1 uf2 uf.
(IS_SEPARATION_COMBINATOR f1 /\
IS_SEPARATION_COMBINATOR f2 /\
IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f1 uf1 /\
IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION f2 uf2 /\
IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION (PRODUCT_SEPARATION_COMBINATOR f1 f2) uf) ==>

(!x1 x2. ((uf (x1,x2)) = ((uf1 x1), (uf2 x2))))``,

REPEAT STRIP_TAC THEN
REPEAT (Q.PAT_ASSUM `IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION X Y` MP_TAC) THEN
ASM_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_THM] THEN
SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_REWRITE,
   IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_def,
   PAIR_FORALL_THM, COND_RAND, COND_RATOR, LET_THM] THEN
REPEAT STRIP_TAC THEN
`?y1 y2. uf (x1, x2) = (y1, y2)` by PROVE_TAC[pairTheory.PAIR] THEN
Q.PAT_ASSUM `!x1 x2. P x1 x2` (MP_TAC o (Q.SPECL [`x1`, `x2`])) THEN
ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[option_CLAUSES])



val PRODUCT_SEPARATION_COMBINATOR___ALGEBRA_THM = store_thm ("PRODUCT_SEPARATION_COMBINATOR___ALGEBRA_THM",
``!f1 f2 u1 u2.
IS_SEPARATION_ALGEBRA f1 u1 /\
IS_SEPARATION_ALGEBRA f2 u2 ==>
IS_SEPARATION_ALGEBRA (PRODUCT_SEPARATION_COMBINATOR f1 f2) (u1,u2)``,

REPEAT STRIP_TAC THEN
REWRITE_TAC [IS_SEPARATION_ALGEBRA___ALT_DEF] THEN
CONJ_TAC THEN1 (
   FULL_SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_THM,
   IS_SEPARATION_ALGEBRA___ALT_DEF]
) THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_NEUTRAL_ELEMENT_FUNCTION_def,
   PRODUCT_SEPARATION_COMBINATOR_REWRITE,
   IS_SEPARATION_ALGEBRA_EXPAND_THM, FUN_EQ_THM] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
   METIS_TAC[pairTheory.PAIR],
   ASM_SIMP_TAC std_ss []
]);



val ASL_IS_SUBSTATE___PRODUCT_SEPARATION_COMBINATOR =
store_thm("ASL_IS_SUBSTATE___PRODUCT_SEPARATION_COMBINATOR",
``!f1 f2 s1 s2.
ASL_IS_SUBSTATE (PRODUCT_SEPARATION_COMBINATOR f1 f2) s1 s2 =
ASL_IS_SUBSTATE f1 (FST s1) (FST s2) /\
ASL_IS_SUBSTATE f2 (SND s1) (SND s2)``,

Cases_on `s1` THEN
Cases_on `s2` THEN
SIMP_TAC std_ss [ASL_IS_SUBSTATE_def,
       PRODUCT_SEPARATION_COMBINATOR_REWRITE,
       PAIR_EXISTS_THM,
       LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM]);



val ID_SEPARATION_COMBINATOR_def = Define `
   ID_SEPARATION_COMBINATOR = BIN_OPTION_MAP (\x' y'. x') ($=)`

val ID_SEPARATION_COMBINATOR___THMS = store_thm ("ID_SEPARATION_COMBINATOR___THMS",
``(IS_SEPARATION_COMBINATOR ID_SEPARATION_COMBINATOR) /\
   (asl_emp ID_SEPARATION_COMBINATOR = UNIV) /\
   (asl_star ID_SEPARATION_COMBINATOR = $INTER) /\
   (ASL_IS_SEPARATE ID_SEPARATION_COMBINATOR = $=) /\
   (ASL_IS_SUBSTATE ID_SEPARATION_COMBINATOR = $=) /\
   (ASL_IS_PRECISE_IN_STATE ID_SEPARATION_COMBINATOR = (K (K T))) /\
   (ASL_IS_PRECISE ID_SEPARATION_COMBINATOR = K T)
``,

SIMP_TAC std_ss [ID_SEPARATION_COMBINATOR_def] THEN
REPEAT STRIP_TAC THENL [
   SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_def, BIN_OPTION_MAP_THM,
      COMM_DEF] THEN
   METIS_TAC[],

   SIMP_TAC std_ss [EXTENSION] THEN
   SIMP_TAC std_ss [asl_emp_def, IN_UNIV, IN_ABS, BIN_OPTION_MAP_THM],

   SIMP_TAC std_ss [Ntimes FUN_EQ_THM 2] THEN
   SIMP_TAC std_ss [EXTENSION, asl_star_def, IN_INTER, IN_ABS,
      BIN_OPTION_MAP_THM],

   SIMP_TAC std_ss [Ntimes FUN_EQ_THM 2] THEN
   SIMP_TAC std_ss [ASL_IS_SEPARATE_def, BIN_OPTION_MAP_THM],

   SIMP_TAC std_ss [Ntimes FUN_EQ_THM 2] THEN
   SIMP_TAC std_ss [ASL_IS_SUBSTATE_def, BIN_OPTION_MAP_THM],

   SIMP_TAC std_ss [Ntimes FUN_EQ_THM 2] THEN
   SIMP_TAC std_ss [ASL_IS_PRECISE_IN_STATE_def, BIN_OPTION_MAP_THM,
      ASL_IS_SUBSTATE_def],

   SIMP_TAC std_ss [Ntimes FUN_EQ_THM 2] THEN
   SIMP_TAC std_ss [ASL_IS_PRECISE_def, BIN_OPTION_MAP_THM,
      ASL_IS_SUBSTATE_def]
]);


val asl_inl_def = Define `asl_inl f1 f2 x = \X. ((FST X) IN x) /\ ((SND X) IN (asl_emp f2))`
val asl_inr_def = Define `asl_inr f1 f2 x = \X. ((SND X) IN x) /\ ((FST X) IN (asl_emp f1))`


val asl_in_11 = store_thm ("asl_in_11",
   ``IS_SEPARATION_COMBINATOR f1 /\ IS_SEPARATION_COMBINATOR f2 ==>
      (((asl_inl f1 f2 x1 = asl_inl f1 f2 x2) = (x1 = x2)) /\
      ((asl_inr f1 f2 x1 = asl_inr f1 f2 x2) = (x1 = x2)))``,

SIMP_TAC std_ss [asl_inl_def, asl_inr_def, EXTENSION, IN_ABS,
   asl_emp_def, IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
STRIP_TAC THEN
SIMP_TAC std_ss [GSYM EXTENSION] THEN
ASM_SIMP_TAC std_ss [PAIR_FORALL_THM] THEN
METIS_TAC[EXTENSION]);


val PRODUCT_SEPARATION_COMBINATOR___asl_emp = store_thm (
"PRODUCT_SEPARATION_COMBINATOR___asl_emp",
``!f1 f2.
asl_emp (PRODUCT_SEPARATION_COMBINATOR f1 f2) =
(\s. FST s IN asl_emp f1 /\ SND s IN asl_emp f2)``,

SIMP_TAC std_ss [asl_emp_def,
   PRODUCT_SEPARATION_COMBINATOR_REWRITE,
   IN_ABS, PAIR_EXISTS_THM, FUN_EQ_THM] THEN
METIS_TAC[]);


val PRODUCT_SEPARATION_COMBINATOR___asl_in_emp = store_thm (
"PRODUCT_SEPARATION_COMBINATOR___asl_in_emp",
``!f1 f2.
(((asl_inl f1 f2 (asl_emp f1)) = asl_emp (PRODUCT_SEPARATION_COMBINATOR f1 f2)) /\
((asl_inr f1 f2 (asl_emp f2)) = asl_emp (PRODUCT_SEPARATION_COMBINATOR f1 f2)))``,

SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR___asl_emp,
   asl_inr_def, asl_inl_def] THEN
METIS_TAC[]);




val PRODUCT_SEPARATION_COMBINATOR___asl_true = store_thm (
"PRODUCT_SEPARATION_COMBINATOR___asl_true",
``!f1 f2.
(IS_SEPARATION_COMBINATOR f1 /\
IS_SEPARATION_COMBINATOR f2) ==>

((asl_star (PRODUCT_SEPARATION_COMBINATOR f1 f2)
(asl_inl f1 f2 UNIV) (asl_inr f1 f2 UNIV) = UNIV) /\
(asl_star (PRODUCT_SEPARATION_COMBINATOR f1 f2)
UNIV (asl_inr f1 f2 UNIV) = UNIV) /\
(asl_star (PRODUCT_SEPARATION_COMBINATOR f1 f2)
(asl_inl f1 f2 UNIV) UNIV = UNIV))
``,

SIMP_TAC std_ss [asl_star_def, IN_UNIV, asl_inl_def, asl_inr_def,
   IN_ABS, asl_emp_def] THEN
SIMP_TAC std_ss [EXTENSION, IN_UNIV, IN_ABS, PAIR_EXISTS_THM,
   PAIR_FORALL_THM] THEN
SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_REWRITE] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
ASM_SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
METIS_TAC[]);



val PRODUCT_SEPARATION_COMBINATOR___asl_false = store_thm (
"PRODUCT_SEPARATION_COMBINATOR___asl_false",
``!f1 f2.
((asl_inl f1 f2 {} = {}) /\ (asl_inr f1 f2 {} = {}))``,

SIMP_TAC std_ss [asl_inl_def, asl_inr_def, NOT_IN_EMPTY, EXTENSION,
   IN_ABS]);



val PRODUCT_SEPARATION_COMBINATOR___asl_in_star = store_thm (
"PRODUCT_SEPARATION_COMBINATOR___asl_in_star",
``!f1 f2 X Y.
(IS_SEPARATION_COMBINATOR f1 /\
IS_SEPARATION_COMBINATOR f2) ==>

((asl_star (PRODUCT_SEPARATION_COMBINATOR f1 f2) (asl_inl f1 f2 X) (asl_inl f1 f2 Y) =
asl_inl f1 f2 (asl_star f1 X Y)) /\
(asl_star (PRODUCT_SEPARATION_COMBINATOR f1 f2) (asl_inr f1 f2 X) (asl_inr f1 f2 Y) =
asl_inr f1 f2 (asl_star f2 X Y)))``,


SIMP_TAC std_ss [EXTENSION, asl_star_def, IN_ABS] THEN
SIMP_TAC std_ss [asl_inl_def, asl_inr_def, IN_ABS] THEN
SIMP_TAC std_ss [PAIR_EXISTS_THM, PAIR_FORALL_THM,
   PRODUCT_SEPARATION_COMBINATOR_REWRITE, asl_emp_def, IN_ABS] THEN
SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
METIS_TAC[]);



val IS_SOME___PRODUCT_SEPARATION_COMBINATOR = store_thm
("IS_SOME___PRODUCT_SEPARATION_COMBINATOR",
``!f1 f2 s1 s2. IS_SOME (PRODUCT_SEPARATION_COMBINATOR f1 f2 s1 s2) =
   IS_SOME s1 /\ IS_SOME s2 /\
   (IS_SOME (f1 (SOME (FST (THE s1))) (SOME (FST (THE s2)))) /\
    IS_SOME (f2 (SOME (SND (THE s1))) (SOME (SND (THE s2)))))``,
Cases_on `s1` THEN Cases_on `s2` THEN
SIMP_TAC std_ss [PRODUCT_SEPARATION_COMBINATOR_REWRITE,
       LET_THM, COND_NONE_SOME_REWRITES]);



(******************************************************************************)
(* Defining actions / localality                                              *)
(******************************************************************************)



(* -------------------------------------------------------------------------- *)
(* First a order on sets of states                                            *)
(* -------------------------------------------------------------------------- *)

val fasl_order_def = Define `
   (fasl_order x' NONE = T) /\
   (fasl_order NONE (SOME x) = F) /\
   (fasl_order (SOME x) (SOME y) = (x SUBSET y))`

val fasl_order_THM = store_thm ("fasl_order_THM",
   ``(fasl_order NONE x = (x = NONE)) /\
     (fasl_order x NONE) /\
     (fasl_order x (SOME s2) = (?s1. (x = SOME s1) /\ (s1 SUBSET s2))) /\
     (fasl_order (SOME s1) x = (x = NONE) \/ (?s2. (x = SOME s2) /\ (s1 SUBSET s2)))``,

Cases_on `x` THEN SIMP_TAC std_ss [fasl_order_def]);


val fasl_order_THM2 = store_thm ("fasl_order_THM2",
   ``(fasl_order NONE x = (x = NONE)) /\
      (fasl_order x NONE) /\
      (fasl_order x (SOME s2) = (?s1. (x = SOME s1) /\ (s1 SUBSET s2))) /\
     (fasl_order (SOME s1) x = (!s2. (x = SOME s2) ==> (s1 SUBSET s2)))``,

Cases_on `x` THEN SIMP_TAC std_ss [fasl_order_def]);


val fasl_order_EVAL = store_thm ("fasl_order_EVAL",
``!x y. fasl_order x y =
   (!y'. (SOME y' = y) ==> ?x'. (x = SOME x') /\ (x' SUBSET y'))``,
Cases_on `y` THEN SIMP_TAC std_ss [fasl_order_THM2]);


val fasl_order_IS_WEAK_ORDER = store_thm ("fasl_order_IS_WEAK_ORDER",
``WeakOrder (fasl_order)``,

SIMP_TAC std_ss [WeakOrder, antisymmetric_def, reflexive_def, transitive_def] THEN
REPEAT STRIP_TAC THENL [
   Cases_on `x` THEN
   SIMP_TAC std_ss [fasl_order_def, SUBSET_REFL],

   Cases_on `x` THEN Cases_on `y` THEN
   FULL_SIMP_TAC std_ss [fasl_order_def] THEN
   METIS_TAC[SUBSET_ANTISYM],

   Cases_on `x` THEN Cases_on `y` THEN Cases_on `z` THEN
   FULL_SIMP_TAC std_ss [fasl_order_def] THEN
   METIS_TAC[SUBSET_TRANS]
]);



val fasl_order_REFL = store_thm ("fasl_order_REFL",
``!x. fasl_order x x``,
Cases_on `x` THEN
SIMP_TAC std_ss [fasl_order_def, SUBSET_REFL]);


val fasl_order_TRANSITIVE = store_thm ("fasl_order_TRANSITIVE",
``!x1 x2 x3. fasl_order x1 x2 /\ fasl_order x2 x3 ==> fasl_order x1 x3``,
METIS_TAC[fasl_order_IS_WEAK_ORDER, WeakOrder, transitive_def])



val SUP_fasl_order_def = Define `
   SUP_fasl_order M = if (NONE IN M) then NONE else SOME (BIGUNION (IMAGE THE M))`;


val SUP_fasl_order_THM = store_thm ("SUP_fasl_order_THM",

``!M. IS_SUPREMUM fasl_order UNIV M (SUP_fasl_order M)``,

SIMP_TAC std_ss [IS_SUPREMUM_def, IS_UPPER_BOUND_def, IN_UNIV,
   SUP_fasl_order_def] THEN
GEN_TAC THEN
Cases_on `NONE IN M` THEN1 (
   ASM_SIMP_TAC std_ss [fasl_order_THM]
) THEN
ASM_SIMP_TAC std_ss [fasl_order_THM, SUBSET_DEF,
   IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THENL [
   `?s1. m = SOME s1` by ALL_TAC THEN1 (
      Cases_on `m` THEN
      FULL_SIMP_TAC std_ss []
   ) THEN
   Q.EXISTS_TAC `s1` THEN
   ASM_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `m` THEN
   ASM_SIMP_TAC std_ss [],

   Cases_on `b` THEN ASM_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THEN
   `?s1. x'' = SOME s1` by ALL_TAC THEN1 (
      Cases_on `x''` THEN
      FULL_SIMP_TAC std_ss []
   ) THEN
   `fasl_order (SOME s1) (SOME x)` by METIS_TAC[] THEN
   FULL_SIMP_TAC std_ss [fasl_order_THM, SUBSET_DEF]
]);


val SUP_fasl_order___SING = store_thm ("SUP_fasl_order___SING",
   ``!s. SUP_fasl_order {s} = s``,

Cases_on `s` THEN
SIMP_TAC std_ss [SUP_fasl_order_def, IN_SING, IMAGE_INSERT, IMAGE_EMPTY,
       BIGUNION_INSERT, BIGUNION_EMPTY, UNION_EMPTY]);



val BIGSUP_fasl_order_THM = store_thm ("BIGSUP_fasl_order_THM",
``BIGSUP fasl_order UNIV M = SOME (SUP_fasl_order M)``,

MATCH_MP_TAC BIGSUP_THM THEN
SIMP_TAC std_ss [SUP_fasl_order_THM, rest_WeakOrder_THM] THEN
PROVE_TAC[fasl_order_IS_WEAK_ORDER, WeakOrder]);

val SOME___SUP_fasl_order = store_thm ("SOME___SUP_fasl_order",
   ``!M x. (SUP_fasl_order M = SOME x) =
          ((!m. m IN M ==> IS_SOME m) /\ (x = BIGUNION (IMAGE THE M)))``,

SIMP_TAC std_ss [SUP_fasl_order_def, COND_RAND, COND_RATOR] THEN
METIS_TAC[option_CLAUSES])


val IS_SOME___SUP_fasl_order = store_thm ("IS_SOME___SUP_fasl_order",
   ``!M. IS_SOME (SUP_fasl_order M) = (!m. m IN M ==> IS_SOME m)``,

SIMP_TAC std_ss [IS_SOME_EXISTS, SOME___SUP_fasl_order]);


val NONE___SUP_fasl_order = store_thm ("NONE___SUP_fasl_order",
``(SUP_fasl_order M = NONE) = (NONE IN M)``,
SIMP_TAC std_ss [SUP_fasl_order_def, COND_RATOR, COND_RAND]);


val INF_fasl_order_def = Define `
   INF_fasl_order M =
      if !x. x IN M ==> (x = NONE) then
        NONE
      else
        SOME (BIGINTER (IMAGE THE ((\x. IS_SOME x) INTER M)))`;


val INF_fasl_order_THM = store_thm ("INF_fasl_order_THM",

``!M. IS_INFIMUM fasl_order UNIV M (INF_fasl_order M)``,

SIMP_TAC std_ss [IS_INFIMUM_def, IS_LOWER_BOUND_def,
   IN_UNIV, INF_fasl_order_def] THEN
GEN_TAC THEN
Cases_on `!x. x IN M ==> (x = NONE)` THEN1 (
   ASM_SIMP_TAC std_ss [fasl_order_THM]
) THEN
ASM_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THENL [
   Cases_on `m` THENL [
      REWRITE_TAC [fasl_order_THM],

      SIMP_TAC std_ss [fasl_order_THM, SUBSET_DEF,
         IN_BIGINTER, IN_IMAGE, IN_ABS, IN_INTER, GSYM LEFT_FORALL_IMP_THM] THEN
      SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
      GEN_TAC THEN
      Q.EXISTS_TAC `SOME x` THEN
      ASM_SIMP_TAC std_ss []
   ],

   `?b'. b = SOME b'` by ALL_TAC THEN1 (
      Cases_on `b` THEN SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC std_ss [fasl_order_THM] THEN
      METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC std_ss [fasl_order_THM, SUBSET_DEF, IN_BIGINTER,
      IN_IMAGE, IN_INTER, IN_ABS, GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   `fasl_order b x'` by RES_TAC THEN
   POP_ASSUM MP_TAC THEN
   FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, fasl_order_THM, SUBSET_DEF]
]);


val BIGINF_fasl_order_THM = store_thm ("BIGINF_fasl_order_THM",
``BIGINF fasl_order UNIV M = SOME (INF_fasl_order M)``,

MATCH_MP_TAC BIGINF_THM THEN
SIMP_TAC std_ss [INF_fasl_order_THM, rest_WeakOrder_THM] THEN
PROVE_TAC[fasl_order_IS_WEAK_ORDER, WeakOrder]);


val SOME___INF_fasl_order = store_thm ("SOME___INF_fasl_order",
   ``!M x. (INF_fasl_order M = SOME x) =
          (?e. SOME e IN M /\ (x = BIGINTER (IMAGE THE ((\x. IS_SOME x) INTER M))))``,

SIMP_TAC std_ss [INF_fasl_order_def, COND_RAND, COND_RATOR] THEN
METIS_TAC[option_CLAUSES])


val IS_SOME___INF_fasl_order = store_thm ("IS_SOME___INF_fasl_order",
   ``!M. IS_SOME (INF_fasl_order M) = (?e. SOME e IN M)``,
SIMP_TAC std_ss [IS_SOME_EXISTS, SOME___INF_fasl_order]);


val SUP_fasl_order___EQ_INSERT_DIVERGE =
store_thm ("SUP_fasl_order___EQ_INSERT_DIVERGE",
``!aS1 aS2.
((SOME EMPTY INSERT aS2) = (SOME EMPTY INSERT aS1)) ==>
(SUP_fasl_order aS1 = SUP_fasl_order aS2)``,

Tactical.REVERSE (`
   !aS. SUP_fasl_order aS = SUP_fasl_order (SOME EMPTY INSERT aS)` by ALL_TAC) THEN1 (
   METIS_TAC[]
) THEN

SIMP_TAC std_ss [SUP_fasl_order_def,
   IN_IMAGE, IN_INSERT, IMAGE_INSERT,
   BIGUNION_INSERT, UNION_EMPTY, LEFT_AND_OVER_OR,
   EXISTS_OR_THM]);




(* -------------------------------------------------------------------------- *)
(* Local actions                                                              *)
(* -------------------------------------------------------------------------- *)

val _ = type_abbrev("asl_action", Type `:'a -> ('a -> bool) option`);

val ASL_IS_LOCAL_ACTION_def = Define `
   ASL_IS_LOCAL_ACTION f op =
      !s1 s2. ASL_IS_SEPARATE f s1 s2 ==>
         fasl_order (op (THE (f (SOME s1) (SOME s2))))
                (fasl_star f (op s1) (SOME {s2}))`;


val TRANS_REL_TO_TRANS_FUNC_def = Define `
   (TRANS_REL_TO_TRANS_FUNC R s = if R (SOME s) NONE then NONE else (SOME (\s'. R (SOME s) (SOME s'))))`


val TRANS_REL_IS_SAFE_STATE_def = Define `
   TRANS_REL_IS_SAFE_STATE R s = ~(R (SOME s) NONE)`


val TRANS_REL_SAFETY_MONOTONICITY_def = Define `
   TRANS_REL_SAFETY_MONOTONICITY f R =
      !s1 s2. (ASL_IS_SUBSTATE f s1 s2 /\ TRANS_REL_IS_SAFE_STATE R s1) ==>
             TRANS_REL_IS_SAFE_STATE R s2`


val TRANS_REL_FRAME_PROPERTY_def = Define `
   TRANS_REL_FRAME_PROPERTY f R =
      !s1 s2 s s'. ((SOME s = f (SOME s1) (SOME s2)) /\ TRANS_REL_IS_SAFE_STATE R s1 /\
               (R (SOME s) (SOME s'))) ==>
              ?s1'. (SOME s' = f (SOME s1') (SOME s2)) /\ (R (SOME s1) (SOME s1'))`;


val LOCALITY_CHARACTERISATION_REL = store_thm ("LOCALITY_CHARACTERISATION_REL",

``!f R.
((ASL_IS_LOCAL_ACTION f (TRANS_REL_TO_TRANS_FUNC R)) =
(TRANS_REL_SAFETY_MONOTONICITY f R /\
 TRANS_REL_FRAME_PROPERTY f R))``,

REWRITE_TAC [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION_def, ASL_IS_SEPARATE_def, IS_SOME_EXISTS, GSYM LEFT_FORALL_IMP_THM,
   TRANS_REL_TO_TRANS_FUNC_def, TRANS_REL_SAFETY_MONOTONICITY_def, TRANS_REL_IS_SAFE_STATE_def,
   TRANS_REL_FRAME_PROPERTY_def, ASL_IS_SUBSTATE_def] THEN
REPEAT STRIP_TAC THEN EQ_TAC THENL [
   REPEAT STRIP_TAC THENL [
      Q.PAT_ASSUM `!s1 s2 y. P s1 s2 y` (MP_TAC o Q.SPECL [`s1`, `s1'`, `s2`]) THEN
      FULL_SIMP_TAC std_ss [fasl_order_THM, fasl_star_REWRITE,
         COND_RAND, COND_RATOR],


      Q.PAT_ASSUM `!s1 s2 y. P s1 s2 y` (MP_TAC o Q.SPECL [`s1`, `s2`, `s`]) THEN
      ASM_SIMP_TAC std_ss [fasl_star_def, BIN_OPTION_MAP_ALL_DEF_THM,
         asl_star_def, IN_SING, IN_ABS] THEN
      SIMP_TAC std_ss [COND_RAND, COND_RATOR, fasl_order_THM, SUBSET_DEF, IN_ABS] THEN
      METIS_TAC[]
   ],


   REPEAT STRIP_TAC THEN
   Cases_on `R (SOME s1) NONE` THEN (
      ASM_SIMP_TAC std_ss [fasl_star_REWRITE, fasl_order_THM]
   ) THEN
   `~(R (SOME y) NONE)` by METIS_TAC[] THEN
   ASM_SIMP_TAC std_ss [asl_star_def, IN_ABS, IN_SING, fasl_order_THM, SUBSET_DEF]
]);



val TRANS_FUNC_TO_TRANS_REL_def = Define
   `TRANS_FUNC_TO_TRANS_REL f =
      \s1 s2. if s1 = NONE then (s2 = NONE) else
            if f (THE s1) = NONE then (s2 = NONE) else
            (IS_SOME s2 /\ ((THE s2) IN (THE (f (THE s1)))))`

val TRANS_REL_TRANS_STATE_CONV_INV = store_thm ("TRANS_REL_TRANS_STATE_CONV_INV",
``TRANS_REL_TO_TRANS_FUNC (TRANS_FUNC_TO_TRANS_REL f) = f``,

SIMP_TAC std_ss [TRANS_FUNC_TO_TRANS_REL_def,
            TRANS_REL_TO_TRANS_FUNC_def,
            FUN_EQ_THM] THEN
Cases_on `f x` THEN SIMP_TAC std_ss [] THEN
SIMP_TAC std_ss [FUN_EQ_THM, IN_DEF]);



val TRANS_FUNC_SAFETY_MONOTONICITY_def =
   Define `TRANS_FUNC_SAFETY_MONOTONICITY f (op:'a asl_action) =
      !s1 s2. ASL_IS_SUBSTATE f s1 s2 /\ IS_SOME (op s1) ==>
            IS_SOME (op s2)`;


val TRANS_FUNC_FRAME_PROPERTY_def =
   Define `TRANS_FUNC_FRAME_PROPERTY f op =

      !s1 s2 s3 v1 v3 t. ((f (SOME s1) (SOME s2) = SOME s3) /\
                   (op s1 = SOME v1) /\ (op s3 = SOME v3) /\ (t IN v3))==>
         ?t'. (SOME t = f (SOME t') (SOME s2)) /\ (t' IN v1)`



val LOCALITY_CHARACTERISATION = store_thm ("LOCALITY_CHARACTERISATION",

   ``!f op. (ASL_IS_LOCAL_ACTION f op =
      TRANS_FUNC_SAFETY_MONOTONICITY f op /\
      TRANS_FUNC_FRAME_PROPERTY f op)``,

REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC [GSYM TRANS_REL_TRANS_STATE_CONV_INV] THEN
ASM_SIMP_TAC std_ss [LOCALITY_CHARACTERISATION_REL] THEN
SIMP_TAC std_ss [TRANS_REL_TRANS_STATE_CONV_INV] THEN
BINOP_TAC THENL [
   SIMP_TAC std_ss [TRANS_REL_SAFETY_MONOTONICITY_def,
      TRANS_REL_IS_SAFE_STATE_def, TRANS_FUNC_TO_TRANS_REL_def,
      TRANS_FUNC_SAFETY_MONOTONICITY_def,
      NOT_NONE_IS_SOME],


   SIMP_TAC std_ss [TRANS_REL_FRAME_PROPERTY_def,
      TRANS_REL_IS_SAFE_STATE_def, TRANS_FUNC_TO_TRANS_REL_def,
      TRANS_FUNC_FRAME_PROPERTY_def, NOT_NONE_SOME, IS_SOME_EXISTS] THEN
   HO_MATCH_MP_TAC (prove (``(!x1 x2 x3. (P x1 x2 x3 = Q x1 x2 x3)) ==>
                  ((!x1 x2 x3. (P x1 x2 x3)) = (!x1 x2 x3. Q x1 x2 x3))``, METIS_TAC[])) THEN
   REPEAT GEN_TAC THEN
   Cases_on `f (SOME s1) (SOME s2) = SOME s3` THEN ASM_SIMP_TAC std_ss [] THEN
   Cases_on `op s1` THEN SIMP_TAC std_ss [] THEN
   Cases_on `op s3` THEN SIMP_TAC std_ss []
]);




val TRANS_FUNC_SAFETY_MONOTONICITY_REWRITE = store_thm (
"TRANS_FUNC_SAFETY_MONOTONICITY_REWRITE",

``TRANS_FUNC_SAFETY_MONOTONICITY f op =
   !s1 s2 s3. ((f (SOME s1) (SOME s2) = SOME s3) /\ (IS_SOME (op s1))) ==> IS_SOME (op s3)``,

SIMP_TAC std_ss [TRANS_FUNC_SAFETY_MONOTONICITY_def, ASL_IS_SUBSTATE_def,
   GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
PROVE_TAC[]);


val ASL_IS_LOCAL_ACTION___ALTERNATIVE_DEF = save_thm ("ASL_IS_LOCAL_ACTION___ALTERNATIVE_DEF",
SIMP_RULE std_ss [TRANS_FUNC_SAFETY_MONOTONICITY_REWRITE,
   TRANS_FUNC_FRAME_PROPERTY_def]
LOCALITY_CHARACTERISATION);


val ASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF = store_thm ("ASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF",
   ``!f op.
    ASL_IS_LOCAL_ACTION f op =
    !s1 s2 s3 v1.
      (f (SOME s1) (SOME s2) = SOME s3) /\ (ASL_IS_SUBSTATE f s1 s3) /\ (op s1 = SOME v1) ==> (?v3. (op s3 = SOME v3) /\ (!t. t IN v3 ==>
      ?t'. (SOME t = f (SOME t') (SOME s2)) /\ t' IN v1))``,

SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ALTERNATIVE_DEF] THEN
REPEAT GEN_TAC THEN
EQ_TAC THEN STRIP_TAC THENL [
   REPEAT STRIP_TAC THEN
   `?v3. op s3 = SOME v3` by PROVE_TAC[IS_SOME_EXISTS] THEN
   ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[],

   SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
   REPEAT STRIP_TAC THENL [
      `ASL_IS_SUBSTATE f s1 s3` by METIS_TAC[ASL_IS_SUBSTATE_def] THEN
      METIS_TAC[],

      `ASL_IS_SUBSTATE f s1 s3` by METIS_TAC[ASL_IS_SUBSTATE_def] THEN
      METIS_TAC[SOME_11]
   ]
]);


val HOARE_TRIPLE_def = Define `
   HOARE_TRIPLE (P:'a set) f (Q:'a set) = (!s. s IN P ==> fasl_order (f s) (SOME Q))`


val HOARE_TRIPLE_REWRITE = store_thm ("HOARE_TRIPLE_REWRITE",
``HOARE_TRIPLE P f Q = 
  (!s. s IN P ==> ?S. (f s = SOME S) /\ S SUBSET Q)``,
SIMP_TAC std_ss [HOARE_TRIPLE_def, fasl_order_THM]);


val fasl_action_order_def = Define `fasl_action_order f g =
!P Q. HOARE_TRIPLE P g Q ==> HOARE_TRIPLE P f Q`;


val fasl_action_order_POINTWISE_DEF = store_thm ("fasl_action_order_POINTWISE_DEF",
``!a1 a2.
(fasl_action_order a1 a2 =
!s. fasl_order (a1 s) (a2 s))``,

ASSUME_TAC fasl_order_IS_WEAK_ORDER THEN
FULL_SIMP_TAC std_ss [fasl_action_order_def, HOARE_TRIPLE_def, WeakOrder] THEN
REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
   Cases_on `a2 s` THEN1 SIMP_TAC std_ss [fasl_order_THM] THEN
   Q.PAT_ASSUM `!P Q. X P Q` (MP_TAC o Q.SPECL [`{s}`, `x`]) THEN
   FULL_SIMP_TAC std_ss[IN_SING, reflexive_def],

   PROVE_TAC[transitive_def]
]);


val fasl_action_order_IS_WEAK_ORDER = store_thm ("fasl_action_order_IS_WEAK_ORDER",
``WeakOrder fasl_action_order``,

ASSUME_TAC fasl_order_IS_WEAK_ORDER THEN
FULL_SIMP_TAC std_ss [WeakOrder, reflexive_def, fasl_action_order_POINTWISE_DEF,
   antisymmetric_def, transitive_def] THEN
METIS_TAC[]);


val fasl_action_order_TRANSITIVE = store_thm ("fasl_action_order_TRANSITIVE",
``!a1 a2 a3. fasl_action_order a1 a2 /\ fasl_action_order a2 a3 ==>
        fasl_action_order a1 a3``,
PROVE_TAC [fasl_action_order_IS_WEAK_ORDER, WeakOrder, transitive_def]);


val ASL_IS_LOCAL_ACTION___HOARE_TRIPLE = store_thm ("ASL_IS_LOCAL_ACTION___HOARE_TRIPLE",
   ``!f a. (
      ASL_IS_LOCAL_ACTION f a =
      (!P Q. (HOARE_TRIPLE P a Q ==>
             (!x. HOARE_TRIPLE (asl_star f P x) a (asl_star f Q x)))))``,

SIMP_TAC std_ss [HOARE_TRIPLE_def, fasl_order_THM, ASL_IS_LOCAL_ACTION_def,
   ASL_IS_SEPARATE_def, IS_SOME_EXISTS, GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [asl_star_def, IN_ABS, SUBSET_DEF] THEN
   `fasl_order (a s) (fasl_star f (a p) (SOME {q}))` by METIS_TAC[] THEN
   `?p'. (a p = SOME p') /\ !x. x IN p' ==> x IN Q` by METIS_TAC[] THEN
   FULL_SIMP_TAC std_ss [fasl_star_REWRITE, fasl_order_THM,
      asl_star_def, IN_SING, IN_ABS, SUBSET_DEF] THEN
   METIS_TAC[],

   Cases_on `a s1` THEN (
      ASM_SIMP_TAC std_ss [fasl_star_REWRITE, fasl_order_THM]
   ) THEN
   Q.PAT_ASSUM `!P Q. X P Q` (MP_TAC o Q.SPECL [`{s1}`, `x`]) THEN
   ASM_SIMP_TAC std_ss [IN_SING, SUBSET_REFL, asl_star_def,
      IN_ABS, SUBSET_DEF] THEN
   SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
   Q.EXISTS_TAC `{s2}` THEN
   Q.EXISTS_TAC `y` THEN
   ASM_SIMP_TAC std_ss [IN_SING]
])



(* -------------------------------------------------------------------------- *)
(* Lattice of local actions                                                   *)
(* -------------------------------------------------------------------------- *)

val SUP_fasl_action_order_def = Define `
   SUP_fasl_action_order M = \x. SUP_fasl_order (IMAGE (\f. f x) M)`;

val SUP_fasl_action_order_REWRITE = store_thm ("SUP_fasl_action_order_REWRITE",
``!actions. SUP_fasl_action_order actions = \s.
      if !a. a IN actions ==> IS_SOME (a s) then
        SOME (BIGUNION (IMAGE (\a. THE (a s)) actions))
      else
        NONE``,

SIMP_TAC std_ss [SUP_fasl_action_order_def,
   SUP_fasl_order_def, IN_IMAGE, GSYM IMAGE_COMPOSE,
   combinTheory.o_DEF] THEN
METIS_TAC[NOT_IS_SOME_EQ_NONE]);


val SUP_fasl_action_order_THM = store_thm ("SUP_fasl_action_order_THM",

``!M. IS_SUPREMUM fasl_action_order UNIV M (SUP_fasl_action_order M)``,

ASSUME_TAC SUP_fasl_order_THM THEN
FULL_SIMP_TAC std_ss [IS_SUPREMUM_def,
   IS_UPPER_BOUND_def, IN_UNIV,
   fasl_action_order_POINTWISE_DEF,
   SUP_fasl_action_order_def,
   FORALL_AND_THM] THEN
REPEAT STRIP_TAC THENL [
   Q.PAT_ASSUM `!M m. m IN M ==> fasl_order m (SUP_fasl_order M)` MATCH_MP_TAC THEN
   SIMP_TAC std_ss [IN_IMAGE] THEN
   METIS_TAC[],

   Q.PAT_ASSUM `!M m. X M m ==> fasl_order (SUP_fasl_order M) m` MATCH_MP_TAC THEN
   SIMP_TAC std_ss [IN_IMAGE] THEN
   METIS_TAC[]
]);




val BIGSUP_fasl_action_order_THM = store_thm ("BIGSUP_fasl_action_order_THM",
``BIGSUP fasl_action_order UNIV M = SOME (SUP_fasl_action_order M)``,

MATCH_MP_TAC BIGSUP_THM THEN
SIMP_TAC std_ss [SUP_fasl_action_order_THM, rest_WeakOrder_THM] THEN
PROVE_TAC[fasl_action_order_IS_WEAK_ORDER, WeakOrder]);



val SOME___SUP_fasl_action_order = store_thm ("SOME___SUP_fasl_action_order",
   ``!OP s x. (SUP_fasl_action_order OP s = SOME x) = ((!op. op IN OP ==> IS_SOME (op s)) /\
       (x = BIGUNION (IMAGE THE (IMAGE (\f. f s) OP))))``,

SIMP_TAC std_ss [SUP_fasl_action_order_def, SOME___SUP_fasl_order,
   IN_IMAGE, GSYM LEFT_FORALL_IMP_THM]);


val IS_SOME___SUP_fasl_action_order = store_thm ("IS_SOME___SUP_fasl_action_order",
  ``!OP s. (IS_SOME (SUP_fasl_action_order OP s)) = (!op. op IN OP ==> IS_SOME (op s))``,
SIMP_TAC std_ss [SOME___SUP_fasl_action_order, IS_SOME_EXISTS]);


val NONE___SUP_fasl_action_order = store_thm (
"NONE___SUP_fasl_action_order",
``!OP s. (SUP_fasl_action_order OP s = NONE) = (?op. op IN OP /\ (op s = NONE))``,
REWRITE_TAC[NONE_IS_NOT_SOME, IS_SOME___SUP_fasl_action_order] THEN
SIMP_TAC std_ss []);


val SUP_fasl_action_order_LOCAL = store_thm ("SUP_fasl_action_order_LOCAL",
``!OP f.
(!op. op IN OP ==> ASL_IS_LOCAL_ACTION f op) ==>
ASL_IS_LOCAL_ACTION f (SUP_fasl_action_order OP)``,

SIMP_TAC std_ss [LOCALITY_CHARACTERISATION, IMP_CONJ_THM, FORALL_AND_THM] THEN
REPEAT STRIP_TAC THENL [
   SIMP_TAC std_ss [TRANS_FUNC_SAFETY_MONOTONICITY_REWRITE,
      IS_SOME___SUP_fasl_action_order] THEN
   FULL_SIMP_TAC std_ss [TRANS_FUNC_SAFETY_MONOTONICITY_REWRITE] THEN
   METIS_TAC[],


   ASM_SIMP_TAC std_ss [TRANS_FUNC_FRAME_PROPERTY_def,
      SOME___SUP_fasl_action_order,
      IN_BIGUNION, IN_IMAGE, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
   REPEAT STRIP_TAC THEN
   HO_MATCH_MP_TAC (prove (``(?t' f'. P t' f') ==> ?f' t'. P t' f'``, METIS_TAC[])) THEN
   Q.EXISTS_TAC `f'` THEN
   `?v1 v3. (f' s1 = SOME v1) /\ (f' s3 = SOME v3)` by METIS_TAC[option_CLAUSES] THEN
   FULL_SIMP_TAC std_ss [] THEN

   `TRANS_FUNC_FRAME_PROPERTY f f'` by RES_TAC THEN
   POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [TRANS_FUNC_FRAME_PROPERTY_def]) THEN
   METIS_TAC[]
]);



val fasl_order___SUP_fasl_action_order = store_thm ("fasl_order___SUP_fasl_action_order",
``!X s P.
   fasl_order (SUP_fasl_action_order X s) (SOME P) =
   (!x. x IN X ==> ?p. (x s = SOME p) /\ (p SUBSET P))``,

SIMP_TAC std_ss [fasl_order_THM,
   SOME___SUP_fasl_action_order, SUBSET_DEF,
   IN_BIGUNION, IN_IMAGE, GSYM LEFT_EXISTS_AND_THM,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM,
   IS_SOME_EXISTS] THEN
METIS_TAC[option_CLAUSES]);



val fasl_action_order___SUP_fasl_action_order =
store_thm ("fasl_action_order___SUP_fasl_action_order",
``!OP a2. fasl_action_order (SUP_fasl_action_order OP) a2 =
     (!a1. a1 IN OP ==> fasl_action_order a1 a2)``,

SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF,
   GSYM RIGHT_FORALL_IMP_THM] THEN
REPEAT GEN_TAC THEN
HO_MATCH_MP_TAC (prove (``(!s. (X s = !a1. Y a1 s)) ==>
   ((!s. X s) = (!a1 s. Y a1 s))``, METIS_TAC[])) THEN
GEN_TAC THEN
Cases_on `a2 s` THEN SIMP_TAC std_ss [fasl_order_THM2] THEN
SIMP_TAC std_ss [SOME___SUP_fasl_action_order,
   IS_SOME_EXISTS, SUBSET_DEF, IN_BIGUNION, GSYM LEFT_FORALL_IMP_THM] THEN
SIMP_TAC std_ss [IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
METIS_TAC[option_CLAUSES]);



val fasl_action_order___SUP_fasl_action_order___IMPL =
store_thm ("fasl_action_order___SUP_fasl_action_order___IMPL",
``!OP a1. (!s. ?a2. a2 IN OP /\ fasl_order (a1 s) (a2 s)) ==>
     fasl_action_order a1 (SUP_fasl_action_order OP)``,

SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF,
   GSYM RIGHT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `s`) THEN
Cases_on `a1 s` THENL [
   FULL_SIMP_TAC std_ss [fasl_order_THM2, NONE___SUP_fasl_action_order] THEN
   Q.EXISTS_TAC `a2` THEN
   ASM_REWRITE_TAC[],

   FULL_SIMP_TAC std_ss [fasl_order_THM2, SOME___SUP_fasl_action_order, SUBSET_DEF,
      IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `a2` THEN
   `?s2. a2 s = SOME s2` by METIS_TAC[IS_SOME_EXISTS] THEN
   FULL_SIMP_TAC std_ss []
]);



val SUP_fasl_action_order___SING = store_thm (
"SUP_fasl_action_order___SING",
``!a. SUP_fasl_action_order {a:'a asl_action} = a``,

ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC std_ss [SUP_fasl_action_order_def,
  SUP_fasl_order_def, IN_SING,
  IN_IMAGE, COND_RAND, COND_RATOR,
  IMAGE_INSERT, IMAGE_EMPTY,
  BIGUNION_EMPTY, BIGUNION_INSERT,
  UNION_EMPTY] THEN
GEN_TAC THEN
Cases_on `a x` THEN
SIMP_TAC std_ss []);



val HOARE_INFERENCE___SUP_fasl_action_order = store_thm (
 "HOARE_INFERENCE___SUP_fasl_action_order",
``HOARE_TRIPLE P (SUP_fasl_action_order M) Q =
  (!m. m IN M ==> (HOARE_TRIPLE P m Q))``,
SIMP_TAC std_ss [HOARE_TRIPLE_def,
   fasl_order_THM2, SOME___SUP_fasl_action_order,
   SUBSET_DEF, IN_BIGUNION, IN_IMAGE,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN (
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   FULL_SIMP_TAC std_ss [IS_SOME_EXISTS]
));


val INF_fasl_action_order_def = Define `
   INF_fasl_action_order M = \x. INF_fasl_order (IMAGE (\f. f x) M)`;


val INF_fasl_action_order_REWRITE = store_thm ("INF_fasl_action_order_REWRITE",
``!actions. INF_fasl_action_order actions = \s.
      if ?a. a IN actions /\ IS_SOME (a s) then
        SOME (BIGINTER (IMAGE THE (IS_SOME INTER IMAGE (\a. a s) actions)))
      else
        NONE``,

SIMP_TAC std_ss [INF_fasl_action_order_def,
   INF_fasl_order_def, IN_IMAGE, GSYM IMAGE_COMPOSE,
   combinTheory.o_DEF, GSYM LEFT_FORALL_IMP_THM, ETA_THM] THEN
METIS_TAC[NOT_IS_SOME_EQ_NONE]);



val INF_fasl_action_order_THM = store_thm ("INF_fasl_action_order_THM",

``!M. IS_INFIMUM fasl_action_order UNIV M (INF_fasl_action_order M)``,

ASSUME_TAC INF_fasl_order_THM THEN
FULL_SIMP_TAC std_ss [IS_INFIMUM_def,
   IS_LOWER_BOUND_def, IN_UNIV,
   fasl_action_order_POINTWISE_DEF,
   INF_fasl_action_order_def,
   FORALL_AND_THM] THEN
REPEAT STRIP_TAC THENL [
   Q.PAT_ASSUM `!M m. m IN M ==> fasl_order (INF_fasl_order M) m` MATCH_MP_TAC THEN
   SIMP_TAC std_ss [IN_IMAGE] THEN
   METIS_TAC[],

   Q.PAT_ASSUM `!M m. X M m ==> fasl_order m (INF_fasl_order M)` MATCH_MP_TAC THEN
   SIMP_TAC std_ss [IN_IMAGE] THEN
   METIS_TAC[]
]);




val BIGINF_fasl_action_order_THM = store_thm ("BIGINF_fasl_action_order_THM",
``BIGINF fasl_action_order UNIV M = SOME (INF_fasl_action_order M)``,

MATCH_MP_TAC BIGINF_THM THEN
SIMP_TAC std_ss [INF_fasl_action_order_THM, rest_WeakOrder_THM] THEN
PROVE_TAC[fasl_action_order_IS_WEAK_ORDER, WeakOrder]);



val SOME___INF_fasl_action_order = store_thm ("SOME___INF_fasl_action_order",
   ``!OP s x. (INF_fasl_action_order OP s = SOME x) = ((?op. op IN OP /\ IS_SOME (op s)) /\
       (x =  BIGINTER (IMAGE THE ((\x. IS_SOME x) INTER IMAGE (\f. f s) OP))))``,

SIMP_TAC std_ss [INF_fasl_action_order_def, SOME___INF_fasl_order,
   IN_IMAGE] THEN
METIS_TAC[option_CLAUSES]
);


val IS_SOME___INF_fasl_action_order = store_thm ("IS_SOME___INF_fasl_action_order",
   ``!OP s. (IS_SOME (INF_fasl_action_order OP s)) = (?op. op IN OP /\ IS_SOME (op s))``,
SIMP_TAC std_ss [SOME___INF_fasl_action_order, IS_SOME_EXISTS]);

val NONE___INF_fasl_action_order = store_thm ("NONE___INF_fasl_action_order",
  ``!OP s. (INF_fasl_action_order OP s = NONE) = (!op. op IN OP ==> (op s = NONE))``,
REWRITE_TAC[NONE_IS_NOT_SOME, IS_SOME___INF_fasl_action_order] THEN
PROVE_TAC[]);



val INF_fasl_action_order_LOCAL = store_thm ("INF_fasl_action_order_LOCAL",
``!OP f. (IS_SEPARATION_COMBINATOR f /\
(!op. op IN OP ==> ASL_IS_LOCAL_ACTION f op)) ==>
ASL_IS_LOCAL_ACTION f (INF_fasl_action_order OP)``,


SIMP_TAC std_ss [LOCALITY_CHARACTERISATION, IMP_CONJ_THM, FORALL_AND_THM] THEN
REPEAT STRIP_TAC THENL [
   SIMP_TAC std_ss [TRANS_FUNC_SAFETY_MONOTONICITY_REWRITE,
      IS_SOME___INF_fasl_action_order] THEN
   FULL_SIMP_TAC std_ss [TRANS_FUNC_SAFETY_MONOTONICITY_REWRITE] THEN
   METIS_TAC[],


   ASM_SIMP_TAC std_ss [TRANS_FUNC_FRAME_PROPERTY_def,
      SOME___INF_fasl_action_order, IN_BIGINTER, IN_IMAGE, IN_INTER,
      IN_ABS, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   `!g. (IS_SOME (g s1) /\ (g IN OP)) ==>
      ?t'. (SOME t = f (SOME t') (SOME s2)) /\ t' IN (THE (g s1))` by ALL_TAC THEN1 (
      REPEAT STRIP_TAC THEN
      `IS_SOME (g s3)` by METIS_TAC[TRANS_FUNC_SAFETY_MONOTONICITY_REWRITE] THEN
      `?v1 v3. (g s1 = SOME v1) /\ (g s3 = SOME v3) /\ (t IN v3)` by ALL_TAC THEN1 (
         RES_TAC THEN
         FULL_SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
         METIS_TAC[option_CLAUSES]
      ) THEN
      `TRANS_FUNC_FRAME_PROPERTY f g` by RES_TAC THEN
      POP_ASSUM (MATCH_MP_TAC o REWRITE_RULE [TRANS_FUNC_FRAME_PROPERTY_def]) THEN
      Q.EXISTS_TAC `s1` THEN
      ASM_SIMP_TAC std_ss []
   ) THEN

   `?t'. SOME t = f (SOME t') (SOME s2)` by METIS_TAC[] THEN
   Q.EXISTS_TAC `t'` THEN
   ASM_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THEN

   `?t''. (SOME t = f (SOME t'') (SOME s2)) /\ (t'' IN (THE (f' s1)))` by METIS_TAC[] THEN
   Tactical.REVERSE (`t' = t''` by ALL_TAC) THEN1 (
      ASM_REWRITE_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
   ONCE_REWRITE_TAC [GSYM SOME_11] THEN
   Q.PAT_ASSUM `OPTION_IS_RIGHT_CANCELLATIVE f` (MATCH_MP_TAC o REWRITE_RULE [OPTION_IS_RIGHT_CANCELLATIVE_def]) THEN
   Q.EXISTS_TAC `SOME s2` THEN
   METIS_TAC[option_CLAUSES]
]);






val ASL_IS_LOCAL_ACTION___FAILING_FUNCTION = store_thm ("ASL_IS_LOCAL_ACTION___FAILING_FUNCTION",
``!f. ASL_IS_LOCAL_ACTION f (K NONE)``,

SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION_def, fasl_star_REWRITE, fasl_order_THM]
);


val fasl_action_order___IS_COMPLETE_LATTICE = store_thm ("fasl_action_order___IS_COMPLETE_LATTICE",
``!f.
IS_SEPARATION_COMBINATOR f ==>
IS_COMPLETE_LATTICE fasl_action_order (ASL_IS_LOCAL_ACTION f)``,

REPEAT GEN_TAC THEN DISCH_TAC THEN
SIMP_TAC std_ss [IS_COMPLETE_LATTICE_def] THEN
`rest_WeakOrder (ASL_IS_LOCAL_ACTION f) fasl_action_order` by METIS_TAC[fasl_action_order_IS_WEAK_ORDER,
   rest_WeakOrder_THM] THEN
ASM_REWRITE_TAC[SUBSET_DEF, IS_SOME_EXISTS] THEN
`rest_antisymmetric (ASL_IS_LOCAL_ACTION f) fasl_action_order` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [rest_WeakOrder_def]
) THEN
REPEAT STRIP_TAC THENL [
   Q.EXISTS_TAC `INF_fasl_action_order M` THEN
   MATCH_MP_TAC BIGINF_UNIV_IMP THEN
   ASM_SIMP_TAC std_ss [BIGINF_fasl_action_order_THM, IN_DEF] THEN
   MATCH_MP_TAC INF_fasl_action_order_LOCAL THEN
   FULL_SIMP_TAC std_ss [IN_DEF],


   Q.EXISTS_TAC `SUP_fasl_action_order M` THEN
   MATCH_MP_TAC BIGSUP_UNIV_IMP THEN
   ASM_SIMP_TAC std_ss [BIGSUP_fasl_action_order_THM, IN_DEF] THEN
   MATCH_MP_TAC SUP_fasl_action_order_LOCAL THEN
   FULL_SIMP_TAC std_ss [IN_DEF]
]);



val fasl_action_order___IS_NON_EMPTY_COMPLETE_LATTICE = store_thm ("fasl_action_order___IS_NON_EMPTY_COMPLETE_LATTICE",
``!f.
IS_SEPARATION_COMBINATOR f ==>
IS_NON_EMPTY_COMPLETE_LATTICE fasl_action_order (ASL_IS_LOCAL_ACTION f)``,

REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [IS_NON_EMPTY_COMPLETE_LATTICE_def] THEN
CONJ_TAC THENL [
   METIS_TAC[fasl_action_order___IS_COMPLETE_LATTICE],

   SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_DEF] THEN
   METIS_TAC[ASL_IS_LOCAL_ACTION___FAILING_FUNCTION]
]);



val fasl_action_order___IS_COMPLETE_LATTICE___UNIV = store_thm ("fasl_action_order___IS_COMPLETE_LATTICE___UNIV",
``IS_COMPLETE_LATTICE fasl_action_order UNIV``,

SIMP_TAC std_ss [IS_COMPLETE_LATTICE_def, SUBSET_UNIV] THEN
`rest_WeakOrder UNIV fasl_action_order` by METIS_TAC[fasl_action_order_IS_WEAK_ORDER,
   rest_WeakOrder_THM] THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF, IS_SOME_EXISTS,
BIGINF_fasl_action_order_THM, BIGSUP_fasl_action_order_THM]);


val fasl_action_order___IS_NON_EMPTY_COMPLETE_LATTICE___UNIV = store_thm ("fasl_action_order___IS_NON_EMPTY_COMPLETE_LATTICE___UNIV",
``
IS_NON_EMPTY_COMPLETE_LATTICE fasl_action_order UNIV``,

SIMP_TAC std_ss [IS_NON_EMPTY_COMPLETE_LATTICE_def, UNIV_NOT_EMPTY, fasl_action_order___IS_COMPLETE_LATTICE___UNIV]);


val fasl_order___IS_NON_EMPTY_COMPLETE_LATTICE = store_thm ("fasl_order___IS_NON_EMPTY_COMPLETE_LATTICE",
``IS_NON_EMPTY_COMPLETE_LATTICE fasl_order UNIV``,

SIMP_TAC std_ss [IS_NON_EMPTY_COMPLETE_LATTICE_def,
   IS_COMPLETE_LATTICE_def, UNIV_NOT_EMPTY,
   SUBSET_UNIV, rest_WeakOrder_THM,
   fasl_order_IS_WEAK_ORDER, BIGINF_fasl_order_THM,
   BIGSUP_fasl_order_THM]);



(******************************************************************************)
(* best local actions                                                         *)
(******************************************************************************)

val best_local_action_def = Define `
   best_local_action f P1 P2 s =
      let set = \p. ?s0 s1. ((SOME s) = f (SOME s0) (SOME s1)) /\ (s1 IN P1) /\ (p = fasl_star f (SOME P2) (SOME {s0})) in
      INF_fasl_order set`

val best_local_action_IS_LOCAL = store_thm ("best_local_action_IS_LOCAL",
``!f P1 P2.
IS_SEPARATION_COMBINATOR f ==>
ASL_IS_LOCAL_ACTION f (best_local_action f P1 P2)``,

ONCE_REWRITE_TAC [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION_def, ASL_IS_SEPARATE_def,
   IS_SOME_EXISTS, GSYM LEFT_FORALL_IMP_THM,
   best_local_action_def, LET_THM, IN_ABS,
   fasl_star_def, BIN_OPTION_MAP_ALL_DEF_THM,
   INF_fasl_order_def] THEN
REPEAT STRIP_TAC THEN
Cases_on `!s0 s1'. ~(SOME y = f (SOME s0) (SOME s1')) \/ ~(s1' IN P1)` THENL [
   ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR, fasl_order_THM,
      BIN_OPTION_MAP_ALL_DEF_THM] THEN
   CCONTR_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN
   FULL_SIMP_TAC std_ss [] THEN
   Q.PAT_ASSUM `!s0 s1. P s0 s1` (MP_TAC o Q.SPECL [`THE (f (SOME (s0:'a)) (SOME (s2:'a)))`, `s1'`]) THEN
   `SOME y = f (f (SOME s0) (SOME s2)) (SOME s1')` by METIS_TAC[COMM_DEF, ASSOC_DEF] THEN
   ASM_SIMP_TAC std_ss [] THEN
   Cases_on `f (SOME s0) (SOME s2)` THEN
   METIS_TAC[option_CLAUSES],


   ASM_REWRITE_TAC[] THEN
   ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR, BIN_OPTION_MAP_ALL_DEF_THM,
      fasl_order_THM, SUBSET_DEF, IN_BIGINTER, IN_IMAGE, IN_INTER, IN_ABS, asl_star_def,
      IN_SING] THEN
   MATCH_MP_TAC (prove (``(~A ==> B) ==> (A \/ B)``, PROVE_TAC[])) THEN
   STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN
   CONJ_TAC THEN1 METIS_TAC[] THEN
   SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_FORALL_IMP_THM, IN_ABS] THEN
   FULL_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THEN
   `?p. (SOME x = f (SOME p) (f (SOME s0') (SOME s2))) /\ p IN P2` by ALL_TAC THEN1 (
       `f (SOME s0) (SOME s1') = f (f (SOME s0') (SOME s2)) (SOME s1'')` by METIS_TAC[COMM_DEF, ASSOC_DEF] THEN
      Cases_on `f (SOME s0') (SOME s2)` THEN1 (
         METIS_TAC[option_CLAUSES]
      ) THEN
      Q.PAT_ASSUM `!s0 s1. P s0 s1` MATCH_MP_TAC THEN
      METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC std_ss [] THEN
   Cases_on `f (SOME p) (SOME s0')` THEN1 (
      METIS_TAC[option_CLAUSES, ASSOC_DEF, COMM_DEF]
   ) THEN
   Q.EXISTS_TAC `x'` THEN
   REPEAT STRIP_TAC THEN1 (
      METIS_TAC[option_CLAUSES, ASSOC_DEF, COMM_DEF]
   ) THEN
   Q.PAT_ASSUM `X = SOME x'` (ASSUME_TAC o GSYM) THEN
   ONCE_ASM_REWRITE_TAC[] THEN

   Q.PAT_ASSUM `!s0 s1. P s0 s1` (MP_TAC o Q.SPECL [`THE (f (SOME (s0'':'a)) (SOME (s2:'a)))`, `s1'''`]) THEN
   Cases_on `f (SOME s0'') (SOME s2)` THEN1 (
      METIS_TAC[option_CLAUSES, COMM_DEF, ASSOC_DEF]
   ) THEN
   MATCH_MP_TAC (prove (``(A /\ (B ==> C)) ==> ((A ==> B) ==> C)``, PROVE_TAC[])) THEN
   CONJ_TAC THENL [
      Q.PAT_ASSUM `X = SOME x''` (ASSUME_TAC o GSYM) THEN
      Q.PAT_ASSUM `f (X) Y = f (SOME s0) (SOME s1')` (ASSUME_TAC o GSYM) THEN
      FULL_SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC std_ss [ASSOC_SYM, COMM_DEF],

      STRIP_TAC THEN
      Q.EXISTS_TAC `p'` THEN
      Q.PAT_ASSUM `X = SOME x''` (ASSUME_TAC o GSYM) THEN
      FULL_SIMP_TAC std_ss [] THEN
      Q.PAT_ASSUM `f (SOME p') X = f Y Z` MP_TAC THEN
      FULL_SIMP_TAC std_ss [ASSOC_DEF] THEN
      STRIP_TAC THEN
      Q.PAT_ASSUM `OPTION_IS_RIGHT_CANCELLATIVE f` (MATCH_MP_TAC o REWRITE_RULE [OPTION_IS_RIGHT_CANCELLATIVE_def]) THEN
      Q.EXISTS_TAC `SOME s2` THEN
      Q.PAT_ASSUM `SOME x = X` (ASSUME_TAC o GSYM) THEN
      METIS_TAC[option_CLAUSES]
   ]
]);



val best_local_action_SPEC = store_thm ("best_local_action_SPEC",
``!f P1 P2.
IS_SEPARATION_COMBINATOR f ==>
HOARE_TRIPLE P1 (best_local_action f P1 P2) P2``,

SIMP_TAC std_ss [HOARE_TRIPLE_def, best_local_action_def, LET_THM,
   IN_ABS, GSYM LEFT_FORALL_IMP_THM, fasl_star_def,
   BIN_OPTION_MAP_ALL_DEF_THM, COND_RAND, COND_RATOR,
   fasl_order_THM, INF_fasl_order_def, IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
REPEAT STRIP_TAC THEN1 (
   Q.EXISTS_TAC `uf s` THEN
   Q.EXISTS_TAC `s` THEN
   ASM_SIMP_TAC std_ss []
) THEN

SIMP_TAC std_ss [SUBSET_DEF, IN_BIGINTER,
   IN_IMAGE, IN_INTER, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM] THEN
SIMP_TAC std_ss [asl_star_def, IN_ABS, IN_SING] THEN
GEN_TAC THEN
SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
Q.EXISTS_TAC `uf s` THEN
Q.EXISTS_TAC `s` THEN
ASM_SIMP_TAC std_ss []);




val best_local_action_BEST = store_thm ("best_local_action_BEST",
``!f P1 P2.
IS_SEPARATION_COMBINATOR f ==>

(!g. (ASL_IS_LOCAL_ACTION f g /\
     HOARE_TRIPLE P1 g P2) ==> fasl_action_order g (best_local_action f P1 P2))``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [HOARE_TRIPLE_def,
   fasl_order_THM, fasl_action_order_def,
   INF_fasl_order_def,
   best_local_action_def, LET_THM, IN_ABS, fasl_star_def,
   BIN_OPTION_MAP_ALL_DEF_THM, GSYM LEFT_FORALL_IMP_THM,
   ASL_IS_LOCAL_ACTION_def, ASL_IS_SEPARATE_def, IS_SOME_EXISTS] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR, FORALL_AND_THM, IMP_CONJ_THM] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!s. s IN P ==> X s` MP_TAC THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGINTER, IN_IMAGE, IN_INTER, IN_ABS] THEN
SIMP_TAC std_ss [GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN

`?s0 s1. (SOME s = f (SOME s0) (SOME s1)) /\ s1 IN P1` by METIS_TAC[] THEN

`fasl_order (g s) (BIN_OPTION_MAP_ALL_DEF (asl_star f) (g s1) (SOME {s0}))` by
   METIS_TAC[IS_SEPARATION_COMBINATOR_def, COMM_DEF] THEN
`?t. (g s1 = SOME t) /\ t SUBSET P2` by METIS_TAC[] THEN
FULL_SIMP_TAC std_ss [BIN_OPTION_MAP_ALL_DEF_THM, fasl_order_THM] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!s. s IN P ==> X s` (MP_TAC o Q.SPEC `s`) THEN
ASM_SIMP_TAC std_ss [] THEN
DISCH_TAC THEN POP_ASSUM HO_MATCH_MP_TAC THEN
REPEAT STRIP_TAC THEN
`fasl_order (g s) (BIN_OPTION_MAP_ALL_DEF (asl_star f) (g s1'') (SOME {s0'}))` by
   METIS_TAC[IS_SEPARATION_COMBINATOR_def, COMM_DEF] THEN
`?t'. (g s1'' = SOME t') /\ t' SUBSET P2` by METIS_TAC[] THEN
FULL_SIMP_TAC std_ss [BIN_OPTION_MAP_ALL_DEF_THM, fasl_order_THM] THEN
`x IN asl_star f t' {s0'}` by METIS_TAC[option_CLAUSES, SUBSET_DEF] THEN
POP_ASSUM MP_TAC THEN
SIMP_TAC std_ss [asl_star_def, IN_ABS, IN_SING] THEN
METIS_TAC[SUBSET_DEF]);


val best_local_action_THM = save_thm ("best_local_action_THM",

SIMP_RULE std_ss [GSYM FORALL_AND_THM, GSYM IMP_CONJ_THM]
(LIST_CONJ [best_local_action_IS_LOCAL, best_local_action_SPEC, best_local_action_BEST])
);




val best_local_action___ALTERNATIVE_DEF = store_thm ("best_local_action___ALTERNATIVE_DEF",
``
!f P1 P2.
IS_SEPARATION_COMBINATOR f ==>

(BIGSUP fasl_action_order UNIV (\g. ASL_IS_LOCAL_ACTION f g /\ HOARE_TRIPLE P1 g P2) =
 SOME (best_local_action f P1 P2))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC BIGSUP_THM THEN
CONJ_TAC THEN1 (
   ASSUME_TAC fasl_action_order_IS_WEAK_ORDER THEN
   FULL_SIMP_TAC std_ss [WeakOrder, antisymmetric_def,
      rest_antisymmetric_def]
) THEN

SIMP_TAC std_ss [IS_SUPREMUM_def,
   IS_UPPER_BOUND_def, IN_UNIV, IN_ABS] THEN
CONJ_TAC THEN1 (
   METIS_TAC[best_local_action_BEST]
) THEN
REPEAT STRIP_TAC THEN
POP_ASSUM MATCH_MP_TAC THEN
METIS_TAC [best_local_action_THM]);





val quant_best_local_action_def = Define `
   quant_best_local_action f qP1 qP2 =
   INF_fasl_action_order (\g. ?x. g = best_local_action f (qP1 x) (qP2 x))`

val quant_best_local_action_REWRITE = store_thm ("quant_best_local_action_REWRITE",
   ``quant_best_local_action f qP1 qP2 s = 
     (let set p =
            ?x s0 s1.
              (SOME s = f (SOME s0) (SOME s1)) /\ s1 IN (qP1 x) /\
              (p = fasl_star f (SOME (qP2 x)) (SOME {s0}))
      in
        INF_fasl_order set)``,
   SIMP_TAC std_ss [INF_fasl_action_order_def, quant_best_local_action_def,
       best_local_action_def, IMAGE_ABS, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
       LET_THM] THEN
   SIMP_TAC std_ss [INF_fasl_order_def, IN_ABS,
      GSYM LEFT_FORALL_IMP_THM, COND_NONE_SOME_REWRITES_EQ] THEN
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC[EXTENSION] THEN

   SIMP_TAC std_ss [INTER_ABS, IN_BIGINTER, IN_ABS, IN_IMAGE,
      GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT GEN_TAC THEN
   Q.ABBREV_TAC `cond = \x''. !s0' s1'.
                (f (SOME s0) (SOME s1) = f (SOME s0') (SOME s1')) /\
                s1' IN qP1 x'' ==>
                (fasl_star f (SOME (qP2 x'')) (SOME {s0'}) = NONE)` THEN
   `!x''. (!s0' s1'.
                (f (SOME s0) (SOME s1) = f (SOME s0') (SOME s1')) /\
                s1' IN qP1 x'' ==>
                (fasl_star f (SOME (qP2 x'')) (SOME {s0'}) = NONE)) =
          cond x''` by (Q.UNABBREV_TAC `cond` THEN SIMP_TAC std_ss []) THEN
   ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC (std_ss++CONJ_ss) [COND_NONE_SOME_REWRITES, IN_BIGINTER, 
      IN_IMAGE, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_IMP_THM] THEN
   REDEPTH_CONSEQ_CONV_TAC (K FORALL_EQ___CONSEQ_CONV) THEN
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
   UNABBREV_ALL_TAC THEN
   METIS_TAC[NOT_NONE_IS_SOME]);


val quant_best_local_action_THM = store_thm ("quant_best_local_action_THM",
``!f qP1 qP2.
   IS_SEPARATION_COMBINATOR f ==>

(       ASL_IS_LOCAL_ACTION f (quant_best_local_action f qP1 qP2) /\

   (!x. HOARE_TRIPLE (qP1 x) (quant_best_local_action f qP1 qP2) (qP2 x)) /\

   (!g.
      (ASL_IS_LOCAL_ACTION f g /\ !x. HOARE_TRIPLE (qP1 x) g (qP2 x)) ==>
      fasl_action_order g (quant_best_local_action f qP1 qP2)))``,

REPEAT GEN_TAC THEN STRIP_TAC THEN

ASM_SIMP_TAC std_ss [quant_best_local_action_def] THEN
REPEAT STRIP_TAC THENL [
   MATCH_MP_TAC (SIMP_RULE std_ss [AND_IMP_INTRO] INF_fasl_action_order_LOCAL) THEN
   ASM_SIMP_TAC std_ss [IN_ABS, GSYM LEFT_FORALL_IMP_THM] THEN
   METIS_TAC[best_local_action_THM],


   SIMP_TAC std_ss [HOARE_TRIPLE_def, fasl_order_THM, INF_fasl_action_order_def,
       INF_fasl_order_def, IN_IMAGE,
       COND_RAND, COND_RATOR, IN_ABS] THEN
   SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
   REPEAT STRIP_TAC THEN
   SIMP_TAC std_ss [LEFT_EXISTS_AND_THM] THEN
   CONJ_TAC THEN1 (
      SIMP_TAC std_ss [best_local_action_def, LET_THM, IN_ABS, COND_RAND, COND_RATOR,
         GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, fasl_star_def,
         BIN_OPTION_MAP_ALL_DEF_THM, INF_fasl_order_def] THEN
      FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
      METIS_TAC[]
   ) THEN

   SIMP_TAC std_ss [SUBSET_DEF, IN_BIGINTER, IN_IMAGE, IN_INTER, IN_ABS] THEN
   SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
   SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN

   REPEAT STRIP_TAC THEN
   POP_ASSUM (ASSUME_TAC o (Q.SPEC `x`)) THEN
   `IS_SOME (best_local_action f (qP1 x) (qP2 x) s)` by ALL_TAC THEN1 (
      SIMP_TAC std_ss [best_local_action_def, LET_THM, IN_ABS, COND_RAND, COND_RATOR,
         INF_fasl_order_def] THEN
      SIMP_TAC std_ss [GSYM LEFT_EXISTS_AND_THM, fasl_star_def, BIN_OPTION_MAP_ALL_DEF_THM] THEN
      FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
      Q.EXISTS_TAC `uf s` THEN
      Q.EXISTS_TAC `s` THEN
      ASM_REWRITE_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [] THEN

   `HOARE_TRIPLE (qP1 x) (best_local_action f (qP1 x) (qP2 x)) (qP2 x)` by
      METIS_TAC[best_local_action_SPEC] THEN
   FULL_SIMP_TAC std_ss [IS_SOME_EXISTS, HOARE_TRIPLE_def] THEN
   POP_ASSUM (MP_TAC o Q.SPEC `s`) THEN
   FULL_SIMP_TAC std_ss [fasl_order_def, SUBSET_DEF],



   ASSUME_TAC (Q.SPEC `\g. ?x:'b. g = best_local_action f (qP1 x) (qP2 x)` INF_fasl_action_order_THM) THEN
   Q.ABBREV_TAC `h = (INF_fasl_action_order (\g. ?x:'b. g = best_local_action f (qP1 x) (qP2 x)))` THEN
   FULL_SIMP_TAC std_ss [IS_INFIMUM_def, IS_LOWER_BOUND_def, IN_ABS, IN_UNIV,
      GSYM LEFT_FORALL_IMP_THM] THEN
   Q.PAT_ASSUM `!b. X b ==> Y b` MATCH_MP_TAC THEN
   METIS_TAC[best_local_action_BEST]
]);


val quant_best_local_action___ALTERNATIVE_DEF = store_thm ("quant_best_local_action___ALTERNATIVE_DEF",
``!f P1 P2.
  IS_SEPARATION_COMBINATOR f ==>

(BIGSUP fasl_action_order UNIV (\g. ASL_IS_LOCAL_ACTION f g /\ !x. HOARE_TRIPLE (qP1 x) g (qP2 x)) =
 SOME (quant_best_local_action f qP1 qP2))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC BIGSUP_THM THEN
CONJ_TAC THEN1 (
   ASSUME_TAC fasl_action_order_IS_WEAK_ORDER THEN
   FULL_SIMP_TAC std_ss [WeakOrder, antisymmetric_def,
      rest_antisymmetric_def]
) THEN
SIMP_TAC std_ss [IS_SUPREMUM_def,
   IS_UPPER_BOUND_def, IN_UNIV, IN_ABS] THEN
ASM_SIMP_TAC std_ss [quant_best_local_action_THM]);


val fasl_action_order____quant_best_local_action =
store_thm ("fasl_action_order____quant_best_local_action",
``!f qP1 qP2 g.
     IS_SEPARATION_COMBINATOR f /\
     ASL_IS_LOCAL_ACTION f g /\
     (!x. HOARE_TRIPLE (qP1 x) g (qP2 x)) ==>
       fasl_action_order g (quant_best_local_action f qP1 qP2)``,
METIS_TAC[quant_best_local_action_THM]);



val quant_best_local_action___QUANT_ELIM = store_thm ("quant_best_local_action___QUANT_ELIM",
``quant_best_local_action f (K P) (K Q) = best_local_action f P Q``,

ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
SIMP_TAC std_ss [quant_best_local_action_REWRITE,
       best_local_action_def]);



val SOME___best_local_action = store_thm ("SOME___best_local_action",
``
(best_local_action f P1 P2 s = SOME Q) =
(?s0 s1. (SOME s = f (SOME s0) (SOME s1)) /\ s1 IN P1) /\
(Q = (\x. (!s0 s1.
     (SOME s = f (SOME s0) (SOME s1)) /\ s1 IN P1 ==>
     x IN asl_star f P2 {s0})))``,

SIMP_TAC std_ss [best_local_action_def, LET_THM,
       INF_fasl_order_def, IN_ABS,
       GSYM LEFT_FORALL_IMP_THM, fasl_star_REWRITE,
       COND_NONE_SOME_REWRITES] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [IN_BIGINTER, IN_IMAGE, IN_INTER, IN_ABS,
       GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
METIS_TAC[]);



val IS_SOME___best_local_action = store_thm ("IS_SOME___best_local_action",
``
IS_SOME (best_local_action f P1 P2 s) =
(?s0 s1. (SOME s = f (SOME s0) (SOME s1)) /\ s1 IN P1)``,

SIMP_TAC std_ss [IS_SOME_EXISTS, SOME___best_local_action]);


val NONE___best_local_action = store_thm ("NONE___best_local_action",
``
(best_local_action f P1 P2 s = NONE) =
(!s0 s1. (s1 IN P1) ==> ~(SOME s = f (SOME s0) (SOME s1)))``,

REWRITE_TAC[NONE_IS_NOT_SOME, IS_SOME___best_local_action] THEN
SIMP_TAC std_ss [] THEN
METIS_TAC[]);





val SOME___quant_best_local_action = store_thm ("SOME___quant_best_local_action",
``
(quant_best_local_action f P1 P2 s = SOME Q) =
(
(?arg s0 s1. (SOME s = f (SOME s0) (SOME s1)) /\ (s1 IN (P1 arg))) /\
(Q = (\x. !arg s0 s1.
          (f (SOME s0) (SOME s1) = SOME s) /\ s1 IN P1 arg ==>
          x IN asl_star f (P2 arg) {s0})))``,


SIMP_TAC std_ss [quant_best_local_action_REWRITE, LET_THM,
       SOME___INF_fasl_order, IN_ABS, fasl_star_REWRITE,
       GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
       BIGINTER_ABS, IMAGE_ABS, INTER_ABS,
       GSYM LEFT_FORALL_IMP_THM] THEN
METIS_TAC[]);



val IS_SOME___quant_best_local_action = store_thm ("IS_SOME___quant_best_local_action",
``
(IS_SOME (quant_best_local_action f P1 P2 s)) =
(?arg s0 s1. (SOME s = f (SOME s0) (SOME s1)) /\ (s1 IN (P1 arg)))``,

SIMP_TAC std_ss [IS_SOME_EXISTS,
       SOME___quant_best_local_action]);




val NONE___quant_best_local_action = store_thm ("NONE___quant_best_local_action",
``
(quant_best_local_action f P1 P2 s = NONE) =
(!arg s0 s1. (s1 IN (P1 arg)) ==> ~(SOME s = f (SOME s0) (SOME s1)))``,

REWRITE_TAC[NONE_IS_NOT_SOME, IS_SOME___quant_best_local_action] THEN
SIMP_TAC std_ss [] THEN
METIS_TAC[]);


val quant_best_local_action_EQ_IMPL = store_thm ("quant_best_local_action_EQ_IMPL",
``!f qP1 qQ1 qP2 qQ2.
(?g1 g2. (!arg. ((qP1 (g1 arg) = qP2 arg) /\ (qQ1 (g1 arg) = qQ2 arg))) /\
         (!arg. ((qP2 (g2 arg) = qP1 arg) /\ (qQ2 (g2 arg) = qQ1 arg)))) ==>

(quant_best_local_action f qP1 qQ1 =
 quant_best_local_action f qP2 qQ2)``,

SIMP_TAC std_ss [quant_best_local_action_REWRITE, FUN_EQ_THM, LET_THM] THEN
REPEAT STRIP_TAC THEN
AP_TERM_TAC THEN 
ONCE_REWRITE_TAC[FUN_EQ_THM] THEN SIMP_TAC std_ss [] THEN
METIS_TAC[]);



val best_local_action___false_pre = store_thm ("best_local_action___false_pre",
``best_local_action f (asl_false) Q = K NONE``,

ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC std_ss [best_local_action_def, asl_false_def, NOT_IN_EMPTY,
       LET_THM, INF_fasl_order_def, IN_ABS]);


val best_local_action___false_post = store_thm ("best_local_action___false_post",
``best_local_action f P (asl_false) = \s.
   if (?s0 s1. (SOME s = f (SOME s0) (SOME s1)) /\ (s1 IN P)) then SOME {} else NONE``,

ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC std_ss [best_local_action_def, LET_THM,
       fasl_star_REWRITE, asl_star_def,
       asl_false_def, NOT_IN_EMPTY,
       INF_fasl_order_def, IN_ABS] THEN

SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM,
   COND_NONE_SOME_REWRITES_EQ, EXTENSION,
   NOT_IN_EMPTY, IN_BIGINTER, IN_IMAGE,
   IN_INTER, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `EMPTY` THEN
Q.EXISTS_TAC `s0` THEN
Q.EXISTS_TAC `s1` THEN
ASM_SIMP_TAC std_ss [NOT_IN_EMPTY]);



val best_local_action___pre_and_cond = store_thm (
   "best_local_action___pre_and_cond",
``best_local_action f (asl_and (K c) pre) post =
  if c then best_local_action f pre post else K NONE``,
Cases_on `c` THEN (
   SIMP_TAC std_ss [asl_bool_REWRITES, best_local_action___false_pre]
));


val quant_best_local_action___false_pre = store_thm ("quant_best_local_action___false_pre",
``quant_best_local_action f (\x. asl_false) Qq = K NONE``,

ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC std_ss [quant_best_local_action_REWRITE, asl_false_def, NOT_IN_EMPTY,
       LET_THM, INF_fasl_order_def, IN_ABS]);




(******************************************************************************)
(* Intuitionistic predicates                                                  *)
(******************************************************************************)

val ASL_IS_INTUITIONISTIC_def = Define `
   ASL_IS_INTUITIONISTIC f P = (asl_star f P UNIV = P)`;

val ASL_INTUITIONISTIC_NEGATION_def = Define
   `ASL_INTUITIONISTIC_NEGATION f P =
   \s. !s'. ASL_IS_SEPARATE f s s' ==> ~(THE (f (SOME s) (SOME s')) IN P)`

val ASL_INTUITIONISTIC_NEGATION_REWRITE = store_thm ("ASL_INTUITIONISTIC_NEGATION_REWRITE",
   ``!f P. ASL_INTUITIONISTIC_NEGATION f P =
        \s1. (!s2. ASL_IS_SUBSTATE f s1 s2 ==> ~(s2 IN P))``,
SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_def, ASL_IS_SEPARATE_def, IS_SOME_EXISTS,
   GSYM LEFT_FORALL_IMP_THM, ASL_IS_SUBSTATE_def, FUN_EQ_THM] THEN
METIS_TAC[]);


val ASL_INTUITIONISTIC_NEGATION___IS_INTUITIONISTIC = store_thm ("ASL_INTUITIONISTIC_NEGATION___IS_INTUITIONISTIC",
``
!f P. IS_SEPARATION_COMBINATOR f /\ ASL_IS_INTUITIONISTIC f P ==>
ASL_IS_INTUITIONISTIC f (ASL_INTUITIONISTIC_NEGATION f P)``,


SIMP_TAC std_ss [ASL_IS_INTUITIONISTIC_def, asl_star_def, IN_UNIV,
   ASL_INTUITIONISTIC_NEGATION_REWRITE, IN_ABS, EXTENSION] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
   REPEAT STRIP_TAC THEN
   `ASL_IS_SUBSTATE f p x` by ALL_TAC THEN1 (
      SIMP_TAC std_ss [ASL_IS_SUBSTATE_def] THEN
      PROVE_TAC[]
   ) THEN
   `transitive (ASL_IS_SUBSTATE f)` by METIS_TAC[ASL_IS_SUBSTATE___IS_PREORDER, PreOrder] THEN
   METIS_TAC[transitive_def],

   FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
   Q.EXISTS_TAC `x` THEN
   Q.EXISTS_TAC `uf x` THEN
   ASM_SIMP_TAC std_ss []
]);


val ASL_IS_INTUITIONISTIC___TRUE_FALSE = store_thm ("ASL_IS_INTUITIONISTIC___TRUE_FALSE",

``!f. IS_SEPARATION_COMBINATOR f ==> (

   (ASL_IS_INTUITIONISTIC f asl_false) /\ (ASL_IS_INTUITIONISTIC f asl_true) /\
   (ASL_INTUITIONISTIC_NEGATION f asl_false = asl_true) /\
   (ASL_INTUITIONISTIC_NEGATION f asl_true = asl_false))``,

SIMP_TAC std_ss [ASL_BOOL___PRED_SET_REWRITES,
   ASL_IS_INTUITIONISTIC_def, asl_star_def, NOT_IN_EMPTY, EXTENSION, IN_ABS,
   IN_UNIV, ASL_INTUITIONISTIC_NEGATION_def, ASL_IS_SEPARATE_def, IS_SEPARATION_COMBINATOR_EXPAND_THM,
   IS_SOME_EXISTS] THEN
METIS_TAC[]);




val ASL_IS_INTUITIONISTIC___REWRITE = store_thm ("ASL_IS_INTUITIONISTIC___REWRITE",

``!f. IS_SEPARATION_COMBINATOR f ==>
   !P. (ASL_IS_INTUITIONISTIC f P =
   !s1 s2. (s1 IN P /\ ASL_IS_SUBSTATE f s1 s2) ==> (s2 IN P))``,

SIMP_TAC std_ss [ASL_IS_INTUITIONISTIC_def, EXTENSION] THEN
SIMP_TAC std_ss [asl_star_def, IN_ABS, IN_UNIV, ASL_IS_SUBSTATE_def,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
EQ_TAC THEN1    METIS_TAC[] THEN
REPEAT STRIP_TAC THEN
EQ_TAC THEN1 METIS_TAC[] THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
METIS_TAC[]);



val ASL_IS_INTUITIONISTIC___AND = store_thm ("ASL_IS_INTUITIONISTIC___AND",

``!f p1 p2. (IS_SEPARATION_COMBINATOR f /\
       ASL_IS_INTUITIONISTIC f p1 /\ ASL_IS_INTUITIONISTIC f p2)==>

   (ASL_IS_INTUITIONISTIC f (asl_and p1 p2))``,


REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `IS_SEPARATION_COMBINATOR f` ASSUME_TAC THEN
FULL_SIMP_TAC std_ss [ASL_IS_INTUITIONISTIC___REWRITE] THEN
SIMP_TAC std_ss [asl_and_def, IN_ABS] THEN
METIS_TAC[]);



val ASL_IS_INTUITIONISTIC___OR = store_thm ("ASL_IS_INTUITIONISTIC___OR",

``!f p1 p2. (IS_SEPARATION_COMBINATOR f /\
       ASL_IS_INTUITIONISTIC f p1 /\ ASL_IS_INTUITIONISTIC f p2)==>

   (ASL_IS_INTUITIONISTIC f (asl_or p1 p2))``,


REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `IS_SEPARATION_COMBINATOR f` ASSUME_TAC THEN
FULL_SIMP_TAC std_ss [ASL_IS_INTUITIONISTIC___REWRITE] THEN
SIMP_TAC std_ss [asl_or_def, IN_ABS] THEN
METIS_TAC[]);



val ASL_INTUITIONISTIC_NEGATION_IMP =
store_thm ("ASL_INTUITIONISTIC_NEGATION_IMP",
``!f p. IS_SEPARATION_COMBINATOR f /\ ASL_IS_INTUITIONISTIC f p ==>
(!x. x IN p ==> ~(x IN (ASL_INTUITIONISTIC_NEGATION f p)))``,

SIMP_TAC (std_ss++CONJ_ss) [ASL_INTUITIONISTIC_NEGATION_REWRITE,
   ASL_IS_INTUITIONISTIC___REWRITE, EXTENSION, IN_ABS] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `x` THEN
PROVE_TAC[ASL_IS_SUBSTATE___REFL]);


val ASL_INTUITIONISTIC_NEGATION_NEGATION_IMP =
store_thm ("ASL_INTUITIONISTIC_NEGATION_NEGATION_IMP",
``!f p. IS_SEPARATION_COMBINATOR f /\ ASL_IS_INTUITIONISTIC f p ==>
(!x. x IN p ==> x IN (ASL_INTUITIONISTIC_NEGATION f (ASL_INTUITIONISTIC_NEGATION f p)))``,

SIMP_TAC (std_ss++CONJ_ss) [ASL_INTUITIONISTIC_NEGATION_REWRITE,
   ASL_IS_INTUITIONISTIC___REWRITE, EXTENSION, IN_ABS] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `s2` THEN
PROVE_TAC[ASL_IS_SUBSTATE___REFL]);





(******************************************************************************)
(* Definitions of common local actions                                        *)
(******************************************************************************)

val asla_materialisation_def = Define `
   asla_materialisation f p =
      best_local_action f (asl_emp f) p`;


val asla_materialisation_THM = store_thm ("asla_materialisation_THM",
``!f P q. IS_SEPARATION_COMBINATOR f ==>
(asla_materialisation f P q =
   SOME (asl_star f P {q}))``,

SIMP_TAC std_ss [asla_materialisation_def, best_local_action_def, LET_THM,
   INF_fasl_order_def, IN_ABS, GSYM LEFT_FORALL_IMP_THM,
   ASL_IS_SUBSTATE_def, GSYM RIGHT_FORALL_IMP_THM,
   asl_emp_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   fasl_star_REWRITE] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
`~(!x. ~(uf x = uf q))` by METIS_TAC[] THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

SIMP_TAC std_ss [EXTENSION] THEN
SIMP_TAC std_ss [IN_BIGINTER, IN_INTER, IN_IMAGE, IN_ABS,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM] THEN
METIS_TAC[]);


val asla_annihilation_def = Define `
   asla_annihilation f p =
      best_local_action f p (asl_emp f)`;


val asla_annihilation_THM = store_thm ("asla_annihilation_THM",
``!f P q. (IS_SEPARATION_COMBINATOR f)==>
(asla_annihilation f P q =
   if (!s0 s1. ~(s1 IN P) \/ ~(SOME q = f (SOME s0) (SOME s1))) then NONE else SOME (\x. (!s0 s1. (SOME q = f (SOME s0) (SOME s1)) /\ s1 IN P ==> (s0 = x))))``,

SIMP_TAC std_ss [asla_annihilation_def, best_local_action_def, LET_THM,
   INF_fasl_order_def, IN_ABS, GSYM LEFT_FORALL_IMP_THM,
   ASL_IS_SUBSTATE_def, GSYM RIGHT_FORALL_IMP_THM,
   fasl_star_REWRITE] THEN
REPEAT STRIP_TAC THEN
MP_TAC (Q.SPEC `f` IS_COMM_MONOID___asl_star_emp) THEN
ASM_REWRITE_TAC[COMM_MONOID_THM, LEFT_ID_DEF] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [fasl_star_REWRITE, IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN

MATCH_MP_TAC (prove (``((X = X') /\ (~X' ==> (XX = XX'))) ==> ((if X then NONE else SOME XX) = (if X' then NONE else SOME XX'))``, Cases_on `X` THEN Cases_on `X'` THEN SIMP_TAC std_ss [])) THEN
SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_ABS] THEN
REPEAT STRIP_TAC THEN1 METIS_TAC[] THEN

SIMP_TAC std_ss [IN_BIGINTER, IN_INTER, IN_IMAGE, IN_ABS,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, IN_SING] THEN
PROVE_TAC[]);


val ASL_IS_LOCAL_ACTION___materialisation_annihilation =
store_thm ("ASL_IS_LOCAL_ACTION___materialisation_annihilation",
``!f p. IS_SEPARATION_COMBINATOR f ==>
   (ASL_IS_LOCAL_ACTION f (asla_materialisation f p) /\
    ASL_IS_LOCAL_ACTION f (asla_annihilation f p))``,
SIMP_TAC std_ss [asla_annihilation_def, asla_materialisation_def,
       best_local_action_THM]);


val asla_annihilation_PRECISE_IN_STATE_THM = store_thm ("asla_annihilation_PRECISE_IN_STATE_THM",
``!f P q. IS_SEPARATION_COMBINATOR f ==>
(asla_annihilation f P q =
   let (v = \s0. ?s1. s1 IN P /\ (SOME q = f (SOME s0) (SOME s1))) in
   if (v = EMPTY) then NONE else 
   if SING v then SOME v else SOME EMPTY)``,

SIMP_TAC std_ss [asla_annihilation_THM, LET_THM, EXTENSION, 
   NOT_IN_EMPTY, IN_ABS, SING_DEF, IN_SING] THEN
SIMP_TAC std_ss [COND_NONE_SOME_REWRITES_EQ, COND_NONE_SOME_REWRITES] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR, EXTENSION,
   IN_ABS, NOT_IN_EMPTY, COND_EXPAND_IMP] THEN
REPEAT STRIP_TAC THEN (
   METIS_TAC[]
));

val asla_annihilation_PRECISE_IN_STATE_THM_2 = store_thm ("asla_annihilation_PRECISE_IN_STATE_THM_2",
``!f P q. IS_SEPARATION_COMBINATOR f ==>
(asla_annihilation f P q =
   let (v = \s0. ?s1. s1 IN P /\ (SOME q = f (SOME s0) (SOME s1))) in
   if (v = EMPTY) then NONE else 
   if ASL_IS_PRECISE_IN_STATE f P q then SOME v else SOME EMPTY)``,

SIMP_TAC (std_ss++boolSimps.LET_ss) [asla_annihilation_PRECISE_IN_STATE_THM] THEN
REPEAT STRIP_TAC THEN
Q.ABBREV_TAC `v = (\s0. ?s1. s1 IN P /\ (SOME q = f (SOME s0) (SOME s1)))` THEN
Cases_on `v = EMPTY` THEN ASM_REWRITE_TAC[] THEN
ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR, COND_EXPAND_IMP] THEN
SIMP_TAC std_ss [ASL_IS_PRECISE_IN_STATE_def,
   SING_DEF, IN_ABS, IN_SING] THEN
REPEAT STRIP_TAC THENL [
   `?x. x IN v` by METIS_TAC[MEMBER_NOT_EMPTY] THEN
   Q.EXISTS_TAC `x` THEN
   Q.UNABBREV_TAC `v` THEN
   ASM_SIMP_TAC std_ss [SET_EQ_SUBSET, SUBSET_DEF, IN_SING] THEN
   FULL_SIMP_TAC std_ss [IN_ABS] THEN
   REPEAT STRIP_TAC THEN
   `s1' = s1` by METIS_TAC[ASL_IS_SUBSTATE_INTRO] THEN
   `OPTION_IS_RIGHT_CANCELLATIVE f` by FULL_SIMP_TAC std_ss [
            IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
   METIS_TAC [OPTION_IS_RIGHT_CANCELLATIVE_def,
      optionTheory.option_CLAUSES],

   Q.PAT_ASSUM `v = X` MP_TAC THEN
   FULL_SIMP_TAC std_ss [ASL_IS_SUBSTATE_def] THEN
   `s1 IN v /\ s1' IN v` by ALL_TAC THEN1 (
      UNABBREV_ALL_TAC THEN
      SIMP_TAC std_ss [IN_ABS] THEN
      `COMM f` by FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
      METIS_TAC[COMM_DEF]
) THEN
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [IN_SING] THEN
   `OPTION_IS_RIGHT_CANCELLATIVE f` by FULL_SIMP_TAC std_ss [
            IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
   METIS_TAC [OPTION_IS_RIGHT_CANCELLATIVE_def,
      optionTheory.option_CLAUSES]
]);



val asla_annihilation_PRECISE_THM = store_thm ("asla_annihilation_PRECISE_THM",
``!f P q. (IS_SEPARATION_COMBINATOR f /\ ASL_IS_PRECISE f P)==>
(asla_annihilation f P q =
   let (v = \s0. ?s1. s1 IN P /\ (SOME q = f (SOME s0) (SOME s1))) in
   if (v = EMPTY) then NONE else SOME v)``,

SIMP_TAC std_ss [asla_annihilation_PRECISE_IN_STATE_THM_2,
   ASL_IS_PRECISE___IN_STATE___THM]);


(* example of a non-local action  and divergence for local actions *)
val ASL_IS_LOCAL_ACTION___simple_heap_examples = store_thm ("ASL_IS_LOCAL_ACTION___simple_heap_examples",
``~(ASL_IS_LOCAL_ACTION DISJOINT_FMAP_UNION (\h. if (h = FEMPTY) then SOME {h} else NONE)) /\
   (ASL_IS_LOCAL_ACTION DISJOINT_FMAP_UNION (\h. if (h = FEMPTY) then SOME {h} else SOME {}))
``,
SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ALTERNATIVE_DEF, 
   COND_NONE_SOME_REWRITES, DISJOINT_FMAP_UNION___FEMPTY, IN_SING] THEN
SIMP_TAC (std_ss++boolSimps.COND_elim_ss) [NOT_IN_EMPTY, IN_SING,
   DISJOINT_FMAP_UNION___EQ_FEMPTY] THEN
METIS_TAC[NOT_EQ_FEMPTY_FUPDATE]);


val asla_skip_def = Define `
   asla_skip = \s. SOME {s}`;

val ASL_IS_LOCAL_ACTION___asla_skip = store_thm ("ASL_IS_LOCAL_ACTION___asla_skip",
``!f. ASL_IS_LOCAL_ACTION f  asla_skip``,

SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ALTERNATIVE_DEF,
   asla_skip_def, IN_SING]);


val asla_assume_def = Define `asla_assume f P =
   \s. if (s IN P) then SOME {s} else
       if (s IN ASL_INTUITIONISTIC_NEGATION f P) then SOME {} else
          NONE`;

val asla_assert_def = Define `asla_assert f P =
   \s. if (s IN P) then SOME {s} else NONE`


val asla_assume_assert_def = Define `
   asla_assume_assert aa f P = \s. if (s IN P) then SOME {s} else
                  if (aa /\ s IN ASL_INTUITIONISTIC_NEGATION f P) then SOME {} else
                  NONE`

val asla_assume_assert_THM = store_thm ("asla_assume_assert_THM",
``(asla_assume_assert T = asla_assume) /\
  (asla_assume_assert F = asla_assert)``,
SIMP_TAC std_ss [FUN_EQ_THM, asla_assert_def,
                 asla_assume_def, asla_assume_assert_def]);


val ASL_IS_LOCAL_ACTION___asla_assume_assert = store_thm ("ASL_IS_LOCAL_ACTION___asla_assume_assert",
``!c f P. IS_SEPARATION_COMBINATOR f /\ ASL_IS_INTUITIONISTIC f P ==>
ASL_IS_LOCAL_ACTION f  (asla_assume_assert c f P)``,

SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ALTERNATIVE_EXT_DEF,
   asla_assume_assert_def] THEN
REPEAT STRIP_TAC THEN
Cases_on `s3 IN P` THENL [
   `~(s1 IN ASL_INTUITIONISTIC_NEGATION f P)` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_REWRITE,
        IN_ABS] THEN
      METIS_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [IN_SING] THEN
   Q.PAT_ASSUM `X = v1` (ASSUME_TAC o GSYM) THEN
   ASM_SIMP_TAC std_ss [IN_SING],


   `~(s1 IN P)` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `ASL_IS_INTUITIONISTIC f P` MP_TAC THEN
      FULL_SIMP_TAC std_ss [ASL_IS_INTUITIONISTIC___REWRITE] THEN
      METIS_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [] THEN
   `ASL_IS_INTUITIONISTIC f (ASL_INTUITIONISTIC_NEGATION f P)` by
      METIS_TAC[ASL_INTUITIONISTIC_NEGATION___IS_INTUITIONISTIC] THEN
   POP_ASSUM MP_TAC THEN
   Q.PAT_ASSUM `X = v1` (ASSUME_TAC o GSYM) THEN
   FULL_SIMP_TAC std_ss [ASL_IS_INTUITIONISTIC___REWRITE, NOT_IN_EMPTY] THEN
   METIS_TAC[]
]);



val ASL_IS_LOCAL_ACTION___asla_assume = store_thm ("ASL_IS_LOCAL_ACTION___asla_assume",
``!f P. IS_SEPARATION_COMBINATOR f /\ ASL_IS_INTUITIONISTIC f P ==>
ASL_IS_LOCAL_ACTION f  (asla_assume f P)``,
SIMP_TAC std_ss [GSYM asla_assume_assert_THM, ASL_IS_LOCAL_ACTION___asla_assume_assert]);


val ASL_IS_LOCAL_ACTION___asla_assert = store_thm ("ASL_IS_LOCAL_ACTION___asla_assert",
``!f P. IS_SEPARATION_COMBINATOR f /\ ASL_IS_INTUITIONISTIC f P ==>
ASL_IS_LOCAL_ACTION f  (asla_assert f P)``,
SIMP_TAC std_ss [GSYM asla_assume_assert_THM, ASL_IS_LOCAL_ACTION___asla_assume_assert]);




val IS_SOME___asla_assume = store_thm ("IS_SOME___asla_assume",
``!f P s. IS_SOME (asla_assume f P s) =
     (s IN P \/ s IN ASL_INTUITIONISTIC_NEGATION f P)``,
SIMP_TAC std_ss [asla_assume_def] THEN
Cases_on `s IN P` THEN ASM_SIMP_TAC std_ss [] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR]);


val NONE___asla_assume = store_thm ("NONE___asla_assume",
``!f P s. (asla_assume f P s = NONE) =
     (~(s IN P) /\ ~(s IN ASL_INTUITIONISTIC_NEGATION f P))``,
SIMP_TAC std_ss [asla_assume_def] THEN
Cases_on `s IN P` THEN ASM_SIMP_TAC std_ss [] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR] THEN
METIS_TAC[]);


val asla_check_def = Define `
   asla_check f (a1:'a asl_action) (a2:'a asl_action) = \s:'a. if
      ?s1 s2. (SOME s = f (SOME s1) (SOME s2)) /\ IS_SOME (a1 s1) /\ IS_SOME (a2 s2)
      then SOME {s} else NONE`;

val ASL_IS_LOCAL_ACTION___asla_check = store_thm ("ASL_IS_LOCAL_ACTION___asla_check",
``!f a1 a2. IS_SEPARATION_COMBINATOR f /\ ASL_IS_LOCAL_ACTION f a1 ==>
ASL_IS_LOCAL_ACTION f  (asla_check f a1 a2)``,

SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ALTERNATIVE_DEF,
    asla_check_def, COND_RAND, COND_RATOR, IN_SING,
    IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `X = SOME s3` (ASSUME_TAC o GSYM) THEN
ASM_SIMP_TAC std_ss [] THEN
`f (f (SOME s1') (SOME s2')) (SOME s2) =
  f (f (SOME s1') (SOME s2)) (SOME s2')` by METIS_TAC[COMM_DEF, ASSOC_DEF] THEN
Cases_on `f (SOME s1') (SOME s2)` THEN1 (
   METIS_TAC[option_CLAUSES]
) THEN
Q.EXISTS_TAC `x` THEN
Q.EXISTS_TAC `s2'` THEN
Q.PAT_ASSUM `X = SOME x` (ASSUME_TAC o GSYM) THEN
ASM_SIMP_TAC std_ss [] THEN

Q.PAT_ASSUM `!s1 s2 s3. P s1 s2 s3 ==> IS_SOME (a1 s3)` MATCH_MP_TAC THEN
METIS_TAC[]);


val asla_diverge_def = Define `
   asla_diverge = \s. SOME {}`


val ASL_IS_LOCAL_ACTION___asla_diverge = store_thm ("ASL_IS_LOCAL_ACTION___asla_diverge",
``!f. ASL_IS_LOCAL_ACTION f  asla_diverge``,

SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION_def, asla_diverge_def, fasl_star_REWRITE,
   fasl_order_THM, EMPTY_SUBSET]);

val fasl_action_order_diverge = store_thm ("fasl_action_order_diverge",
``!act. fasl_action_order act asla_diverge =
   (act = asla_diverge)``,

SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF, asla_diverge_def,
   fasl_order_THM, SUBSET_EMPTY] THEN
SIMP_TAC std_ss [FUN_EQ_THM]);


val asla_fail_def = Define `asla_fail = \s. NONE`

val ASL_IS_LOCAL_ACTION___asla_fail = store_thm ("ASL_IS_LOCAL_ACTION___asla_fail",
``!f. ASL_IS_LOCAL_ACTION f  asla_fail``,

SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION_def, asla_fail_def, fasl_star_REWRITE,
   fasl_order_THM]);


val asla_seq_def = Define `
   asla_seq (a1:'a asl_action) (a2:'a asl_action) = \s.
      if a1 s = NONE then NONE else
      SUP_fasl_order (IMAGE a2 (THE (a1 s)))`;


val SOME___asla_seq = store_thm ("SOME___asla_seq",
``(asla_seq a1 a2 s = SOME x) =
   (?s1. (a1 s = SOME s1) /\ (!e. e IN s1 ==> IS_SOME (a2 e)) /\
   (x = (BIGUNION (IMAGE THE (IMAGE a2 s1)))))``,

SIMP_TAC std_ss [asla_seq_def, COND_RAND, COND_RATOR] THEN
Cases_on `a1 s` THEN ASM_SIMP_TAC std_ss [] THEN
SIMP_TAC std_ss [SUP_fasl_order_def, COND_RAND, COND_RATOR,
   IN_IMAGE] THEN
METIS_TAC[option_CLAUSES]);


val IS_SOME___asla_seq = store_thm ("IS_SOME___asla_seq",
``IS_SOME (asla_seq a1 a2 s) =
   ?s1. (a1 s = SOME s1) /\ (!e. e IN s1 ==> IS_SOME (a2 e))``,

SIMP_TAC std_ss [IS_SOME_EXISTS, SOME___asla_seq]);


val NONE___asla_seq = store_thm ("NONE___asla_seq",
``(asla_seq a1 a2 s = NONE) =
 !s1. (a1 s = SOME s1) ==> (?e. e IN s1 /\ (a2 e = NONE))``,

REWRITE_TAC[GSYM NOT_IS_SOME_EQ_NONE,
       IS_SOME___asla_seq] THEN
SIMP_TAC std_ss [] THEN
METIS_TAC[]);




val ASL_IS_LOCAL_ACTION___asla_seq = store_thm ("ASL_IS_LOCAL_ACTION___asla_seq",
``!f a1 a2. (ASL_IS_LOCAL_ACTION f a1 /\
        ASL_IS_LOCAL_ACTION f a2)  ==>
ASL_IS_LOCAL_ACTION f  (asla_seq a1 a2)``,


SIMP_TAC std_ss [LOCALITY_CHARACTERISATION] THEN
REPEAT STRIP_TAC THENL [
   SIMP_TAC std_ss [TRANS_FUNC_SAFETY_MONOTONICITY_REWRITE,
      IS_SOME___asla_seq] THEN
   REPEAT STRIP_TAC THEN
   `?s1. a1 s3 = SOME s1` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [TRANS_FUNC_SAFETY_MONOTONICITY_REWRITE] THEN
      METIS_TAC[option_CLAUSES]
   ) THEN
   ASM_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THEN

   `?t'. (SOME e = f (SOME t') (SOME s2)) /\ t' IN s1'` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `TRANS_FUNC_FRAME_PROPERTY f a1`
         (HO_MATCH_MP_TAC o (REWRITE_RULE [TRANS_FUNC_FRAME_PROPERTY_def])) THEN
      Q.EXISTS_TAC `s1` THEN
      ASM_SIMP_TAC std_ss []
   ) THEN
   `IS_SOME (a2 t')` by METIS_TAC[] THEN
   FULL_SIMP_TAC std_ss [TRANS_FUNC_SAFETY_MONOTONICITY_REWRITE] THEN
   METIS_TAC[option_CLAUSES],


   SIMP_TAC std_ss [TRANS_FUNC_FRAME_PROPERTY_def,
      SOME___asla_seq] THEN
   REPEAT STRIP_TAC THEN

   (*get rid of v1 v3*)
   Q.PAT_ASSUM `v1 = X` (fn thm => FULL_SIMP_TAC std_ss [thm]) THEN
   Q.PAT_ASSUM `v3 = X` (fn thm => FULL_SIMP_TAC std_ss [thm]) THEN
   FULL_SIMP_TAC std_ss [
      prove (``!x a s. ((x IN BIGUNION (IMAGE THE (IMAGE a s))) = (?e. x IN THE (a e) /\ e IN s))``,
         SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, GSYM LEFT_EXISTS_AND_THM,
            GSYM RIGHT_EXISTS_AND_THM] THEN
         METIS_TAC[]
      )] THEN


   `?a2e. a2 e = SOME a2e` by METIS_TAC[option_CLAUSES] THEN
   FULL_SIMP_TAC std_ss [] THEN


   `?e'. (SOME e = f (SOME e') (SOME s2)) /\ e' IN s1'` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `TRANS_FUNC_FRAME_PROPERTY f a1`
         (HO_MATCH_MP_TAC o (REWRITE_RULE [TRANS_FUNC_FRAME_PROPERTY_def])) THEN
      Q.EXISTS_TAC `s1` THEN
      ASM_SIMP_TAC std_ss []
   ) THEN

   `?a2e'. a2 e' = SOME a2e'` by METIS_TAC[option_CLAUSES] THEN
   `?e''. (SOME t = f (SOME e'') (SOME s2)) /\ e'' IN a2e'` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `TRANS_FUNC_FRAME_PROPERTY f a2`
         (HO_MATCH_MP_TAC o (REWRITE_RULE [TRANS_FUNC_FRAME_PROPERTY_def])) THEN
      Q.EXISTS_TAC `e'` THEN
      Q.EXISTS_TAC `e` THEN
      ASM_SIMP_TAC std_ss []
   ) THEN

   Q.EXISTS_TAC `e''` THEN
   ASM_SIMP_TAC std_ss [] THEN
   Q.EXISTS_TAC `e'` THEN
   ASM_SIMP_TAC std_ss []
]);

val asla_seq_skip = store_thm ("asla_seq_skip",
``(asla_seq asla_skip a = a) /\
   (asla_seq a asla_skip = a)``,

SIMP_TAC std_ss [asla_seq_def, asla_skip_def, IMAGE_DEF, IN_SING] THEN
ONCE_REWRITE_TAC [FUN_EQ_THM]  THEN
SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THENL [
   Cases_on `a x` THENL [
      ASM_SIMP_TAC std_ss [SUP_fasl_order_def, COND_RAND, COND_RATOR,
         GSPECIFICATION],

      ASM_SIMP_TAC std_ss [SUP_fasl_order_def, COND_RAND, COND_RATOR,
         GSPECIFICATION, EXTENSION, IN_BIGUNION, IN_IMAGE] THEN
      METIS_TAC[]
   ],

   Cases_on `a x` THEN ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [SUP_fasl_order_def, GSPECIFICATION] THEN
   ONCE_REWRITE_TAC [EXTENSION] THEN
   SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, GSPECIFICATION,
      GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      IN_SING]
]);


val asla_seq___ASSOC = store_thm ("asla_seq___ASSOC",
``ASSOC asla_seq``,

SIMP_TAC std_ss [ASSOC_DEF, asla_seq_def, FUN_EQ_THM] THEN
REPEAT STRIP_TAC THEN
Cases_on `x x'` THEN SIMP_TAC std_ss [] THEN
Cases_on `SUP_fasl_order (IMAGE y x'')` THEN1 (
   POP_ASSUM MP_TAC THEN
   ASM_REWRITE_TAC [NONE_IS_NOT_SOME, IS_SOME___SUP_fasl_order] THEN
   SIMP_TAC std_ss [IN_IMAGE, SUP_fasl_order_def] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [prove (``((if X then NONE else SOME Y) = NONE) = X``, SIMP_TAC std_ss [COND_RAND, COND_RATOR])] THEN
   Q.EXISTS_TAC `x'''` THEN
   ASM_SIMP_TAC std_ss []
) THEN

FULL_SIMP_TAC std_ss [SOME___SUP_fasl_order, IN_IMAGE, GSYM LEFT_FORALL_IMP_THM] THEN
`(IMAGE (\s. (if y s = NONE then NONE else
  SUP_fasl_order (IMAGE z (THE (y s))))) x'') =
  (IMAGE (\s. (SUP_fasl_order (IMAGE z (THE (y s))))) x'')` by ALL_TAC THEN1 (

   REWRITE_TAC [EXTENSION] THEN
   SIMP_TAC std_ss [IN_IMAGE] THEN
   DEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
   SIMP_TAC std_ss [COND_RAND, COND_RATOR] THEN
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
   METIS_TAC[NONE_IS_NOT_SOME]
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN


SIMP_TAC std_ss [SUP_fasl_order_def, IN_IMAGE, COND_RAND, COND_RATOR,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, IN_BIGUNION] THEN
REWRITE_TAC [COND_EXPAND_IMP] THEN
CONJ_TAC THEN1 METIS_TAC[] THEN
SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN1 METIS_TAC[] THEN
SIMP_TAC std_ss [GSYM IMAGE_COMPOSE, combinTheory.o_DEF] THEN

`(IMAGE (\s. THE (if ?x. (NONE = z x) /\ x IN THE (y s) then  NONE else
       SOME (BIGUNION (IMAGE (\x. THE (z x)) (THE (y s)))))) x'') =
  (IMAGE (\s. (BIGUNION (IMAGE (\x. THE (z x)) (THE (y s))))) x'')` by ALL_TAC THEN1 (

   REWRITE_TAC [EXTENSION] THEN
   SIMP_TAC std_ss [IN_IMAGE] THEN
   DEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
   SIMP_TAC std_ss [COND_RAND, COND_RATOR] THEN
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
   METIS_TAC[NONE_IS_NOT_SOME]
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, GSYM LEFT_EXISTS_AND_THM,
   GSYM RIGHT_EXISTS_AND_THM] THEN
METIS_TAC[]);



val asla_seq___SUP_fasl_action_order = store_thm ("asla_seq___SUP_fasl_action_order",
``!M1 M2. ~(M2 = EMPTY) ==>
(asla_seq (SUP_fasl_action_order M1) (SUP_fasl_action_order M2) =
 SUP_fasl_action_order (\a. ?a1 a2. (a1 IN M1) /\ (a2 IN M2) /\
              (a = asla_seq a1 a2)))``,

REPEAT GEN_TAC THEN STRIP_TAC THEN
SIMP_TAC std_ss [asla_seq_def, fasl_action_order_def,
       NONE___SUP_fasl_action_order] THEN
ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR, NONE___SUP_fasl_action_order,
       IN_ABS, GSYM LEFT_EXISTS_AND_THM] THEN
SIMP_TAC std_ss [COND_EXPAND_IMP] THEN
REPEAT STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [GSYM pred_setTheory.MEMBER_NOT_EMPTY] THEN
   Q.EXISTS_TAC `op` THEN Q.EXISTS_TAC `x'` THEN
   ASM_SIMP_TAC std_ss [],


   ASM_SIMP_TAC std_ss [
      SUP_fasl_action_order_def, SUP_fasl_order_def,
      IN_IMAGE, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
      COND_NONE_SOME_REWRITES] THEN
   FULL_SIMP_TAC (std_ss++CONJ_ss) [
      GSYM IMP_DISJ_THM, IN_BIGUNION, IN_IMAGE,
      GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
   SIMP_TAC std_ss [COND_NONE_SOME_REWRITES_EQ] THEN
   CONJ_TAC THEN1 METIS_TAC[] THEN
   STRIP_TAC THEN
   ONCE_REWRITE_TAC[EXTENSION] THEN
   SIMP_TAC std_ss [
      IN_BIGUNION, IN_IMAGE, IN_ABS, GSYM RIGHT_EXISTS_AND_THM] THEN
   SIMP_TAC std_ss [COND_RAND, COND_RATOR, IN_BIGUNION, IN_IMAGE,
          IN_ABS, GSYM RIGHT_EXISTS_AND_THM] THEN
   METIS_TAC[]
]);


val SUP_fasl_action_order___EMPTY = store_thm (
"SUP_fasl_action_order___EMPTY",
``SUP_fasl_action_order EMPTY = asla_diverge``,

SIMP_TAC std_ss [SUP_fasl_action_order_def, IMAGE_EMPTY,
       SUP_fasl_order_def, NOT_IN_EMPTY,
       BIGUNION_EMPTY, asla_diverge_def]);


val asla_seq___SUP_fasl_action_order___left = store_thm ("asla_seq___SUP_fasl_action_order___left",
``!M a2.
(asla_seq (SUP_fasl_action_order M ) a2 =
 SUP_fasl_action_order (\a. ?a1. (a1 IN M) /\ (a = asla_seq a1 a2)))``,

REPEAT STRIP_TAC THEN
CONV_TAC (LHS_CONV (RAND_CONV (REWR_CONV (GSYM SUP_fasl_action_order___SING)))) THEN

SIMP_TAC std_ss [asla_seq___SUP_fasl_action_order, NOT_SING_EMPTY,
   IN_SING]);


val asla_seq___SUP_fasl_action_order___right = store_thm ("asla_seq___SUP_fasl_action_order___right",
``!M a1. ~(M = EMPTY) ==>
(asla_seq a1 (SUP_fasl_action_order M) =
 SUP_fasl_action_order (\a. ?a2. (a2 IN M) /\ (a = asla_seq a1 a2)))``,

REPEAT STRIP_TAC THEN
CONV_TAC (LHS_CONV (RATOR_CONV (RAND_CONV (REWR_CONV (GSYM SUP_fasl_action_order___SING))))) THEN
ASM_SIMP_TAC std_ss [asla_seq___SUP_fasl_action_order, IN_SING]);




val asla_big_seq_def = Define
`(asla_big_seq [] = asla_skip) /\
  (asla_big_seq (h::l) = asla_seq h (asla_big_seq l))`;



val ASL_IS_LOCAL_ACTION___asla_big_seq = store_thm ("ASL_IS_LOCAL_ACTION___asla_big_seq",
``!f l. (EVERY (ASL_IS_LOCAL_ACTION f) l)  ==>
ASL_IS_LOCAL_ACTION f  (asla_big_seq l)``,

Induct_on `l` THENL [
   SIMP_TAC std_ss [asla_big_seq_def,
      ASL_IS_LOCAL_ACTION___asla_skip],

   SIMP_TAC list_ss [asla_big_seq_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC ASL_IS_LOCAL_ACTION___asla_seq THEN
   ASM_SIMP_TAC std_ss []
]);


val asla_big_seq_APPEND = store_thm ("asla_big_seq_APPEND",
``asla_big_seq (l1++l2) =
   asla_big_seq ((asla_big_seq l1)::l2)``,

Induct_on `l1` THENL [
   SIMP_TAC list_ss [asla_big_seq_def, asla_seq_skip],

   ASSUME_TAC asla_seq___ASSOC THEN
   FULL_SIMP_TAC list_ss [asla_big_seq_def, asla_seq_skip,
      ASSOC_DEF]
]);


val asla_repeat_def = Define `
   (asla_repeat a 0 = asla_skip) /\
   (asla_repeat a (SUC n) = asla_seq a (asla_repeat a n))`


val ASL_IS_LOCAL_ACTION___asla_repeat = store_thm ("ASL_IS_LOCAL_ACTION___asla_repeat",
``!f a n. (ASL_IS_LOCAL_ACTION f a)  ==>
ASL_IS_LOCAL_ACTION f  (asla_repeat a n)``,

Induct_on `n` THENL [
   SIMP_TAC std_ss [asla_repeat_def, ASL_IS_LOCAL_ACTION___asla_skip],

   REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC std_ss [asla_repeat_def] THEN
   MATCH_MP_TAC ASL_IS_LOCAL_ACTION___asla_seq THEN
   ASM_SIMP_TAC std_ss []
]);



val asla_repeat___SYM = store_thm ("asla_repeat___SYM",
``!a n. asla_seq (asla_repeat a n) a = asla_seq a (asla_repeat a n)``,
Induct_on `n` THEN (
   ASM_SIMP_TAC std_ss [asla_repeat_def, asla_seq_skip,
     REWRITE_RULE [ASSOC_SYM] asla_seq___ASSOC]
));


val asla_repeat___SYM_DEF = store_thm (
"asla_repeat___SYM_DEF",
``(!a. asla_repeat a 0 = asla_skip) /\
  (!a n. asla_repeat a (SUC n) = asla_seq (asla_repeat a n) a)``,
SIMP_TAC std_ss [asla_repeat_def, asla_repeat___SYM]);



val asla_kleene_star_def = Define `
   asla_kleene_star a =
   SUP_fasl_action_order {asla_repeat a n | n IN UNIV}`


val ASL_IS_LOCAL_ACTION___asla_kleene_star = store_thm ("ASL_IS_LOCAL_ACTION___asla_kleene_star",
``!f a. (ASL_IS_LOCAL_ACTION f a)  ==>
ASL_IS_LOCAL_ACTION f  (asla_kleene_star a)``,

SIMP_TAC std_ss [asla_kleene_star_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC SUP_fasl_action_order_LOCAL THEN
SIMP_TAC std_ss [GSPECIFICATION, IN_UNIV, GSYM LEFT_FORALL_IMP_THM] THEN
ASM_SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___asla_repeat]);



val asla_choice_def = Define `
   asla_choice = SUP_fasl_action_order`

val asla_choice_REWRITE = save_thm ("asla_choice_REWRITE",
REWRITE_CONV [asla_choice_def, SUP_fasl_action_order_def] ``asla_choice actions``);


val ASL_IS_LOCAL_ACTION___asla_choice = save_thm ("ASL_IS_LOCAL_ACTION___asla_choice",
   REWRITE_RULE [GSYM asla_choice_def] SUP_fasl_action_order_LOCAL);


val asla_bin_choice_def = Define `
   asla_bin_choice a1 a2 = asla_choice {a1;a2}`

val ASL_IS_LOCAL_ACTION___asla_bin_choice = store_thm ("ASL_IS_LOCAL_ACTION___asla_bin_choice",
``!f a1 a2. (ASL_IS_LOCAL_ACTION f a1 /\
        ASL_IS_LOCAL_ACTION f a2)  ==>
ASL_IS_LOCAL_ACTION f  (asla_bin_choice a1 a2)``,

   REPEAT STRIP_TAC THEN
   SIMP_TAC std_ss [asla_bin_choice_def] THEN
   MATCH_MP_TAC ASL_IS_LOCAL_ACTION___asla_choice THEN
   ASM_SIMP_TAC std_ss [IN_SING, NOT_IN_EMPTY, IN_INSERT, DISJ_IMP_THM]
);


val asla_bin_choice_THM = store_thm ("asla_bin_choice_THM",
``asla_bin_choice a1 a2 = \s. if (a1 s = NONE) \/ (a2 s = NONE) then
            NONE
              else
            (SOME ((THE (a1 s)) UNION (THE (a2 s))))``,

SIMP_TAC std_ss [asla_bin_choice_def, asla_choice_def,
   SUP_fasl_action_order_REWRITE,
   IMAGE_INSERT, IMAGE_EMPTY,
   IN_INSERT, NOT_IN_EMPTY, BIGUNION_INSERT,
   BIGUNION_EMPTY, UNION_EMPTY] THEN
METIS_TAC[NOT_IS_SOME_EQ_NONE]);


val asla_seq_diverge = store_thm ("asla_seq_diverge",
``(asla_seq asla_diverge x = asla_diverge) /\
  ((asla_seq x asla_diverge s = SOME X) = (IS_SOME (x s) /\ (X = EMPTY))) /\
  ((asla_seq x asla_diverge s = NONE) = (x s = NONE)) /\
  ((SOME X = asla_seq x asla_diverge s) = (IS_SOME (x s) /\ (X = EMPTY))) /\
  ((NONE = asla_seq x asla_diverge s) = (x s = NONE))``,


SIMP_TAC std_ss [asla_seq_def, asla_diverge_def,
       IMAGE_EMPTY, SUP_fasl_order_def,
       NOT_IN_EMPTY, BIGUNION_EMPTY,
       COND_NONE_SOME_REWRITES] THEN
SIMP_TAC std_ss [EXTENSION] THEN
SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
       NOT_IN_EMPTY] THEN
Cases_on `x s` THEN
SIMP_TAC std_ss []);


val asla_seq_diverge_2 = store_thm ("asla_seq_diverge_2",
``(asla_seq x asla_diverge = asla_diverge) =
  !s. IS_SOME (x s)``,

SIMP_TAC std_ss [asla_diverge_def, FUN_EQ_THM] THEN
SIMP_TAC std_ss [GSYM asla_diverge_def, asla_seq_diverge]);



(******************************************************************************)
(* Predicates                                                                 *)
(******************************************************************************)


val asl_predicate_def =
 Hol_datatype
`asl_predicate = asl_pred_prim of (('state option -> 'state option -> 'state option) -> 'state set)
         | asl_pred_true
         | asl_pred_false
         | asl_pred_neg of asl_predicate
         | asl_pred_and of asl_predicate => asl_predicate
         | asl_pred_or of asl_predicate => asl_predicate`;



val EVAL_asl_predicate_def = Define `
   (EVAL_asl_predicate f (asl_pred_prim pp) =
       if ASL_IS_INTUITIONISTIC f (pp f) then pp f else asl_false) /\
   (EVAL_asl_predicate f asl_pred_true = asl_true) /\
   (EVAL_asl_predicate f asl_pred_false = asl_false) /\
   (EVAL_asl_predicate f (asl_pred_neg p) =
      ASL_INTUITIONISTIC_NEGATION f
       (EVAL_asl_predicate f p)) /\
   (EVAL_asl_predicate f (asl_pred_and p1 p2) =
      asl_and (EVAL_asl_predicate f p1) (EVAL_asl_predicate f p2)) /\
   (EVAL_asl_predicate f (asl_pred_or p1 p2) =
      asl_or (EVAL_asl_predicate f p1) (EVAL_asl_predicate f p2))`




val ASL_IS_INTUITIONISTIC___EVAL_asl_predicate =
    store_thm ("ASL_IS_INTUITIONISTIC___EVAL_asl_predicate",
``!f p. IS_SEPARATION_COMBINATOR f ==>
   ASL_IS_INTUITIONISTIC f (EVAL_asl_predicate f p)``,

Induct_on `p` THEN
SIMP_TAC std_ss [EVAL_asl_predicate_def] THEN
REPEAT STRIP_TAC THEN (
   ASM_SIMP_TAC std_ss [COND_RATOR, COND_RAND,
         ASL_IS_INTUITIONISTIC___TRUE_FALSE,
         ASL_INTUITIONISTIC_NEGATION___IS_INTUITIONISTIC,
         ASL_IS_INTUITIONISTIC___AND,
         ASL_IS_INTUITIONISTIC___OR]
));


val EQUIV_asl_predicate_def = Define `
   EQUIV_asl_predicate f p1 p2 =
   (EVAL_asl_predicate f p1 = EVAL_asl_predicate f p2)`

val asl_pred_bigand_def = Define `
       (asl_pred_bigand [] = asl_pred_true)
    /\ (asl_pred_bigand [p] = p) /\
       (asl_pred_bigand (p1::p2::L) =
   asl_pred_and p1 (asl_pred_bigand (p2::L)))`;




val EVAL_asl_predicate___pred_bigand =
store_thm ("EVAL_asl_predicate___pred_bigand",
``(EVAL_asl_predicate f (asl_pred_bigand []) = asl_true) /\
(EVAL_asl_predicate f (asl_pred_bigand (p::L)) =
 asl_and (EVAL_asl_predicate f p) (EVAL_asl_predicate f (asl_pred_bigand L)))``,

Cases_on `L` THEN
SIMP_TAC std_ss [asl_pred_bigand_def, EVAL_asl_predicate_def,
   asl_bool_REWRITES]);






val asl_predicate_IS_DECIDED_IN_STATE_def = Define `
   asl_predicate_IS_DECIDED_IN_STATE f s c =
   (s IN (EVAL_asl_predicate f c) \/
    s IN (EVAL_asl_predicate f (asl_pred_neg c)))`;


val asl_predicate_IS_DECIDED_IN_STATE___EXPAND_REWRITE = store_thm (
"asl_predicate_IS_DECIDED_IN_STATE___EXPAND_REWRITE",
``IS_SEPARATION_COMBINATOR f ==>
  (asl_predicate_IS_DECIDED_IN_STATE f s c =
   (s IN (EVAL_asl_predicate f c) /\
    ~(s IN (EVAL_asl_predicate f (asl_pred_neg c)))) \/
   (~(s IN (EVAL_asl_predicate f c)) /\
    s IN (EVAL_asl_predicate f (asl_pred_neg c))))``,
SIMP_TAC std_ss [asl_predicate_IS_DECIDED_IN_STATE_def,
   EVAL_asl_predicate_def] THEN
METIS_TAC[ASL_INTUITIONISTIC_NEGATION_IMP,
   ASL_IS_INTUITIONISTIC___EVAL_asl_predicate]);


val asl_predicate_IS_DECIDED_def = Define `
   asl_predicate_IS_DECIDED f P c =
   (!s. s IN P ==> (s IN (EVAL_asl_predicate f c) \/
          s IN (EVAL_asl_predicate f (asl_pred_neg c))))`;




val asl_predicate_IS_DECIDED_IN_STATE_NEGATION = store_thm ("asl_predicate_IS_DECIDED_IN_STATE_NEGATION",
``!f c s.
(IS_SEPARATION_COMBINATOR f /\ (asl_predicate_IS_DECIDED_IN_STATE f s c)) ==>
asl_predicate_IS_DECIDED_IN_STATE f s (asl_pred_neg c)``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [asl_predicate_IS_DECIDED_IN_STATE_def,
   EVAL_asl_predicate_def] THEN
Q.ABBREV_TAC `pp = EVAL_asl_predicate f c` THEN

`ASL_IS_INTUITIONISTIC f pp` by METIS_TAC[ASL_IS_INTUITIONISTIC___EVAL_asl_predicate] THEN
DISJ2_TAC THEN
POP_ASSUM MP_TAC THEN
FULL_SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_REWRITE, IN_ABS,
            ASL_IS_INTUITIONISTIC___REWRITE] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `s2` THEN
`PreOrder (ASL_IS_SUBSTATE f)` by METIS_TAC[ASL_IS_SUBSTATE___IS_PREORDER] THEN
FULL_SIMP_TAC std_ss [PreOrder, reflexive_def, transitive_def] THEN
METIS_TAC[]);



val asl_predicate_IS_DECIDED_IN_STATE___REWRITE =
store_thm ("asl_predicate_IS_DECIDED_IN_STATE___REWRITE",

``!f s c.
   IS_SEPARATION_COMBINATOR f ==>
(asl_predicate_IS_DECIDED_IN_STATE f s c =
 !s'. ASL_IS_SUBSTATE f s s' ==>
      (s IN EVAL_asl_predicate f c =
       s' IN EVAL_asl_predicate f c))``,

SIMP_TAC std_ss [asl_predicate_IS_DECIDED_IN_STATE_def,
       EVAL_asl_predicate_def] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_REWRITE,
            IN_ABS] THEN
Q.ABBREV_TAC `P = EVAL_asl_predicate f c` THEN
`ASL_IS_INTUITIONISTIC f P` by
 METIS_TAC[ASL_IS_INTUITIONISTIC___EVAL_asl_predicate] THEN
POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC std_ss [ASL_IS_INTUITIONISTIC___REWRITE] THEN
METIS_TAC[]);





val asl_predicate_IS_DECIDED_NEGATION = store_thm ("asl_predicate_IS_DECIDED_NEGATION",
``!P f c.
(IS_SEPARATION_COMBINATOR f /\ (asl_predicate_IS_DECIDED f P c)) ==>
asl_predicate_IS_DECIDED f P (asl_pred_neg c)``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [asl_predicate_IS_DECIDED_def,
            GSYM asl_predicate_IS_DECIDED_IN_STATE_def] THEN
PROVE_TAC[asl_predicate_IS_DECIDED_IN_STATE_NEGATION]);





val asl_predicate_IS_DECIDED_IN_STATE___pred_true =
store_thm ("asl_predicate_IS_DECIDED_IN_STATE___pred_true",
``!f s. asl_predicate_IS_DECIDED_IN_STATE f s asl_pred_true``,

SIMP_TAC std_ss [asl_predicate_IS_DECIDED_IN_STATE_def,
       EVAL_asl_predicate_def, asl_true_def,
       IN_UNIV]);


val asl_predicate_IS_DECIDED_IN_STATE___pred_false =
store_thm ("asl_predicate_IS_DECIDED_IN_STATE___pred_false",
``!f s. asl_predicate_IS_DECIDED_IN_STATE f s asl_pred_false``,

SIMP_TAC std_ss [asl_predicate_IS_DECIDED_IN_STATE_def,
       EVAL_asl_predicate_def, asl_false_def,
       NOT_IN_EMPTY, IN_ABS,
       ASL_INTUITIONISTIC_NEGATION_REWRITE]);




val asl_predicate_IS_DECIDED_IN_STATE___pred_and =
store_thm ("asl_predicate_IS_DECIDED_IN_STATE___pred_and",
``!p1 p2 f s.
(asl_predicate_IS_DECIDED_IN_STATE f s p1 /\
 asl_predicate_IS_DECIDED_IN_STATE f s p2) ==>
asl_predicate_IS_DECIDED_IN_STATE f s (asl_pred_and p1 p2)``,

SIMP_TAC std_ss [asl_predicate_IS_DECIDED_IN_STATE_def,
       EVAL_asl_predicate_def, IN_ABS,
       ASL_INTUITIONISTIC_NEGATION_REWRITE] THEN
REPEAT GEN_TAC THEN
Q.ABBREV_TAC `pe1 = EVAL_asl_predicate f p1` THEN
Q.ABBREV_TAC `pe2 = EVAL_asl_predicate f p2` THEN
SIMP_TAC std_ss [asl_and_def, IN_ABS] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss []);


val asl_predicate_IS_DECIDED_IN_STATE___pred_or =
store_thm ("asl_predicate_IS_DECIDED_IN_STATE___pred_or",
``!p1 p2 f s.
(asl_predicate_IS_DECIDED_IN_STATE f s p1 /\
 asl_predicate_IS_DECIDED_IN_STATE f s p2) ==>
asl_predicate_IS_DECIDED_IN_STATE f s (asl_pred_or p1 p2)``,

SIMP_TAC std_ss [asl_predicate_IS_DECIDED_IN_STATE_def,
       EVAL_asl_predicate_def, IN_ABS,
       ASL_INTUITIONISTIC_NEGATION_REWRITE] THEN
REPEAT GEN_TAC THEN
Q.ABBREV_TAC `pe1 = EVAL_asl_predicate f p1` THEN
Q.ABBREV_TAC `pe2 = EVAL_asl_predicate f p2` THEN
SIMP_TAC std_ss [asl_or_def, IN_ABS] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss []);




val asl_predicate_IS_DECIDED_IN_STATE___pred_neg_is_neg =
store_thm ("asl_predicate_IS_DECIDED_IN_STATE___pred_neg_is_neg",
``!f s p.
IS_SEPARATION_COMBINATOR f /\ asl_predicate_IS_DECIDED_IN_STATE f s p ==>
(s IN EVAL_asl_predicate f (asl_pred_neg p) =
 ~(s IN EVAL_asl_predicate f p))``,

SIMP_TAC std_ss [asl_predicate_IS_DECIDED_IN_STATE_def,
   DISJ_IMP_THM, EVAL_asl_predicate_def,
   ASL_INTUITIONISTIC_NEGATION_REWRITE, IN_ABS] THEN
METIS_TAC[ASL_IS_SUBSTATE___REFL]);



val asl_predicate_IS_DECIDED___asl_true =
 store_thm ("asl_predicate_IS_DECIDED___asl_true",

``!f P.
asl_predicate_IS_DECIDED f P (asl_pred_true)``,

SIMP_TAC std_ss [asl_predicate_IS_DECIDED_def,
       EVAL_asl_predicate_def, asl_true_def,
       IN_UNIV]);



val asl_predicate_IS_DECIDED___asl_pred_and =
 store_thm ("asl_predicate_IS_DECIDED___asl_pred_and",

``!f P Q1 Q2.
(asl_predicate_IS_DECIDED f P Q1 /\ asl_predicate_IS_DECIDED f P Q2) ==>
asl_predicate_IS_DECIDED f P (asl_pred_and Q1 Q2)``,

SIMP_TAC std_ss [asl_predicate_IS_DECIDED_def,
       EVAL_asl_predicate_def] THEN
REPEAT STRIP_TAC THEN
Q.ABBREV_TAC `q1 = EVAL_asl_predicate f Q1` THEN
Q.ABBREV_TAC `q2 = EVAL_asl_predicate f Q2` THEN
FULL_SIMP_TAC std_ss [asl_and_def, ASL_INTUITIONISTIC_NEGATION_REWRITE, IN_ABS] THEN
METIS_TAC[]);




val asl_predicate_IS_DECIDED___asl_pred_bigand =
store_thm ("asl_predicate_IS_DECIDED___asl_pred_bigand",
``!f P pL.
EVERY (\P'. asl_predicate_IS_DECIDED f P P') pL ==>
asl_predicate_IS_DECIDED f P (asl_pred_bigand pL)``,

REPEAT GEN_TAC THEN
Induct_on `pL` THEN1 (
   SIMP_TAC list_ss [asl_predicate_IS_DECIDED___asl_true,
           asl_pred_bigand_def]
) THEN

Cases_on `pL` THEN1 (
   SIMP_TAC list_ss [asl_pred_bigand_def]
) THEN

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC list_ss [asl_pred_bigand_def] THEN
MATCH_MP_TAC asl_predicate_IS_DECIDED___asl_pred_and THEN
ASM_REWRITE_TAC[]);


val EVAL_asl_predicate___asl_pred_bigand = store_thm (
"EVAL_asl_predicate___asl_pred_bigand",
``EVAL_asl_predicate f (asl_pred_bigand L) =
  asl_bigand_list (MAP (EVAL_asl_predicate f ) L)``,

Induct_on `L` THENL [
   SIMP_TAC list_ss [asl_bigand_list_def,
           asl_pred_bigand_def,
           EVAL_asl_predicate_def],


   Cases_on `L` THEN1 (
      SIMP_TAC list_ss [asl_bigand_list_THM,
         asl_pred_bigand_def,
         EVAL_asl_predicate_def] THEN
      SIMP_TAC std_ss [FUN_EQ_THM]
   ) THEN
   FULL_SIMP_TAC std_ss [asl_bigand_list_THM,
          asl_pred_bigand_def,
          EVAL_asl_predicate_def] THEN
   SIMP_TAC std_ss [FUN_EQ_THM] THEN
   SIMP_TAC list_ss [asl_and_def, IN_DEF]
]);




(******************************************************************************)
(* Programs                                                                   *)
(******************************************************************************)


(* -------------------------------------------------------------------------- *)
(* Prim commands                                                              *)
(* -------------------------------------------------------------------------- *)

val asl_prim_command_def =
 Hol_datatype
`asl_prim_command = asl_pc_shallow_command of (('state option -> 'state option -> 'state option) -> 'state asl_action)`


val asl_prim_command_11 = fetch "-" "asl_prim_command_11";
val asl_pc_assume_def  = Define `asl_pc_assume P = asl_pc_shallow_command (\f. asla_assume f (EVAL_asl_predicate f P))`
val asl_pc_assert_def  = Define `asl_pc_assert P = asl_pc_shallow_command (\f. asla_assert f (EVAL_asl_predicate f P))`
val asl_pc_skip_def    = Define `asl_pc_skip     = asl_pc_shallow_command (K asla_skip)`;
val asl_pc_fail_def    = Define `asl_pc_fail     = asl_pc_shallow_command (K asla_fail)`;
val asl_pc_diverge_def = Define `asl_pc_diverge  = asl_pc_shallow_command (K asla_diverge)`;


val asl_pc_assume_true___skip = store_thm (
"asl_pc_assume_true___skip",
``asl_pc_assume asl_pred_true = asl_pc_skip``,
SIMP_TAC std_ss [asl_pc_skip_def, asl_pc_assume_def,
       asl_prim_command_11, asla_assume_def,
       EVAL_asl_predicate_def, asl_bool_EVAL,
       asla_skip_def] THEN
SIMP_TAC std_ss [FUN_EQ_THM]);


val asl_pc_assume_false___diverge = store_thm (
"asl_pc_assume_false___diverge",
``asl_pc_assume asl_pred_false = asl_pc_diverge``,
SIMP_TAC std_ss [asl_pc_diverge_def,
       asl_pc_assume_def,
       asl_prim_command_11, asla_assume_def,
       EVAL_asl_predicate_def, asl_bool_EVAL,
       asla_diverge_def, IN_ABS,
       ASL_INTUITIONISTIC_NEGATION_REWRITE] THEN
SIMP_TAC std_ss [FUN_EQ_THM]);


val EVAL_asl_prim_command_def = Define `
   EVAL_asl_prim_command f (asl_pc_shallow_command sc) =
      if (ASL_IS_LOCAL_ACTION f (sc f)) then sc f else asla_fail`


val EVAL_asl_prim_command_THM = store_thm ("EVAL_asl_prim_command_THM",
``(IS_SEPARATION_COMBINATOR f  ==>
  (EVAL_asl_prim_command f (asl_pc_assume p) =
      asla_assume f (EVAL_asl_predicate f p))) /\
  (IS_SEPARATION_COMBINATOR f  ==>
  (EVAL_asl_prim_command f (asl_pc_assert p) =
      asla_assert f (EVAL_asl_predicate f p))) /\
  (EVAL_asl_prim_command f asl_pc_diverge = asla_diverge) /\
  (EVAL_asl_prim_command f asl_pc_fail = asla_fail) /\
  (EVAL_asl_prim_command f asl_pc_skip = asla_skip) /\
  (EVAL_asl_prim_command f (asl_pc_shallow_command sc) =
      if (ASL_IS_LOCAL_ACTION f (sc f)) then sc f else asla_fail)``,

SIMP_TAC std_ss [EVAL_asl_prim_command_def,
       asl_pc_skip_def, ASL_IS_LOCAL_ACTION___asla_skip,
       asl_pc_fail_def, ASL_IS_LOCAL_ACTION___asla_fail,
       asl_pc_diverge_def, ASL_IS_LOCAL_ACTION___asla_diverge,
       asl_pc_assume_def, asl_pc_assert_def,
       ASL_IS_LOCAL_ACTION___asla_assert,
       ASL_IS_LOCAL_ACTION___asla_assume,
       ASL_IS_INTUITIONISTIC___EVAL_asl_predicate]);



val ASL_IS_LOCAL_ACTION___EVAL_asl_prim_command = store_thm ("ASL_IS_LOCAL_ACTION___EVAL_asl_prim_command",
``!f c.
ASL_IS_LOCAL_ACTION f (EVAL_asl_prim_command f c)``,

Cases_on `c` THEN
SIMP_TAC std_ss [EVAL_asl_prim_command_def, COND_RAND, COND_RATOR,
       ASL_IS_LOCAL_ACTION___asla_fail]);


(* -------------------------------------------------------------------------- *)
(* Atomic actions                                                             *)
(* -------------------------------------------------------------------------- *)

val asl_atomic_action_def =
 Hol_datatype
`asl_atomic_action = asl_aa_pc of 'state asl_prim_command
              |   asl_aa_check of 'state asl_prim_command => 'state asl_prim_command
              |   asl_aa_prolaag of 'lock
              |   asl_aa_verhoog of 'lock`


val asl_atomic_action_11 = fetch "-" "asl_atomic_action_11";
val asl_atomic_action_distinct = fetch "-" "asl_atomic_action_distinct";


val ASL_ATOMIC_ACTION_SEM_def = Define `
(ASL_ATOMIC_ACTION_SEM (f, lock_env) (asl_aa_pc pc) = EVAL_asl_prim_command f pc) /\

(ASL_ATOMIC_ACTION_SEM (f, lock_env) (asl_aa_check pc1 pc2) = (asla_check f (EVAL_asl_prim_command f pc1) (EVAL_asl_prim_command f pc2))) /\

(ASL_ATOMIC_ACTION_SEM (f, lock_env) (asl_aa_prolaag l) =
asla_materialisation f (lock_env l)) /\

(ASL_ATOMIC_ACTION_SEM (f, lock_env) (asl_aa_verhoog l) =
asla_annihilation f (lock_env l))`;


val ASL_IS_LOCAL_ACTION___ASL_ATOMIC_ACTION_SEM = store_thm ("ASL_IS_LOCAL_ACTION___ASL_ATOMIC_ACTION_SEM",
``!f lock_env aa.
IS_SEPARATION_COMBINATOR f ==>
ASL_IS_LOCAL_ACTION f (ASL_ATOMIC_ACTION_SEM (f, lock_env) aa)``,

REPEAT STRIP_TAC THEN
Cases_on `aa` THEN SIMP_TAC std_ss [ASL_ATOMIC_ACTION_SEM_def] THENL [
   ASM_SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___EVAL_asl_prim_command],

   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC ASL_IS_LOCAL_ACTION___asla_check THEN
   ASM_SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___EVAL_asl_prim_command],

   ASM_SIMP_TAC std_ss [best_local_action_THM, asla_materialisation_def],
   ASM_SIMP_TAC std_ss [best_local_action_THM, asla_annihilation_def]
]);


val ASL_IS_PRIM_COMMAND_ATOMIC_ACTION_def = Define `
   (ASL_IS_PRIM_COMMAND_ATOMIC_ACTION (asl_aa_pc _)= T) /\
   (ASL_IS_PRIM_COMMAND_ATOMIC_ACTION _ = F)`

val ASL_IS_PRIM_COMMAND_ATOMIC_ACTION_EXISTS = store_thm (
   "ASL_IS_PRIM_COMMAND_ATOMIC_ACTION_EXISTS",
   ``ASL_IS_PRIM_COMMAND_ATOMIC_ACTION aa = ?pc. aa = asl_aa_pc pc``,

Cases_on `aa` THEN
SIMP_TAC std_ss [ASL_IS_PRIM_COMMAND_ATOMIC_ACTION_def, asl_atomic_action_11,
   asl_atomic_action_distinct]);



val ASL_GET_PRIM_COMMAND_ATOMIC_ACTION_def = Define `
   (ASL_GET_PRIM_COMMAND_ATOMIC_ACTION (asl_aa_pc pc)= pc)`

val ASL_IS_CHECK_ATOMIC_ACTION_def = Define `
   (ASL_IS_CHECK_ATOMIC_ACTION (asl_aa_check pc1 pc2) = T) /\
   (ASL_IS_CHECK_ATOMIC_ACTION _ = F)`;

val ASL_IS_LOCK_ATOMIC_ACTION_def = Define `
   (ASL_IS_LOCK_ATOMIC_ACTION L (asl_aa_prolaag l) = (l IN L)) /\
   (ASL_IS_LOCK_ATOMIC_ACTION L (asl_aa_verhoog l) = (l IN L)) /\
   (ASL_IS_LOCK_ATOMIC_ACTION _ _ = F)`

val ASL_IS_SING_LOCK_ATOMIC_ACTION_def = Define `
   ASL_IS_SING_LOCK_ATOMIC_ACTION l =
   ASL_IS_LOCK_ATOMIC_ACTION {l}`;

val ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE = save_thm ("ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE",
   let
      val thm = SPEC_ALL ASL_IS_LOCK_ATOMIC_ACTION_def;
      val thm2 = Q.GEN `L` thm;
      val thm3 = Q.GEN `v0` thm2;
      val thm4 = Q.SPECL [`{l'}`, `{l'}`] thm3;
      val thm5 = REWRITE_RULE [GSYM ASL_IS_SING_LOCK_ATOMIC_ACTION_def, IN_SING] thm4;
   in
      thm5
   end);

val ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE2 = store_thm ("ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE2",
   ``ASL_IS_SING_LOCK_ATOMIC_ACTION l aa =
      ((aa = asl_aa_prolaag l) \/ (aa = asl_aa_verhoog l))``,

Cases_on `aa` THEN
SIMP_TAC std_ss [ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE,
   asl_atomic_action_distinct, asl_atomic_action_11]);



val asl_aa_skip_def = Define `asl_aa_skip = asl_aa_pc asl_pc_skip`;
val asl_aa_diverge_def = Define `asl_aa_diverge = asl_aa_pc asl_pc_diverge`;
val asl_aa_fail_def = Define `asl_aa_fail = asl_aa_pc asl_pc_fail`;



(* -------------------------------------------------------------------------- *)
(* Traces                                                                     *)
(* -------------------------------------------------------------------------- *)

val _ = type_abbrev("asl_trace",
   Type `:('lock, 'state) asl_atomic_action list`);

val ASL_TRACE_SEM_def =
   Define `ASL_TRACE_SEM xenv t = asla_big_seq (MAP (ASL_ATOMIC_ACTION_SEM xenv) t)`;

val ASL_IS_LOCAL_ACTION___ASL_TRACE_SEM = store_thm ("ASL_IS_LOCAL_ACTION___ASL_TRACE_SEM",
``!f lock_env t.
IS_SEPARATION_COMBINATOR f ==>
ASL_IS_LOCAL_ACTION f (ASL_TRACE_SEM (f, lock_env) t)``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [ASL_TRACE_SEM_def] THEN
MATCH_MP_TAC ASL_IS_LOCAL_ACTION___asla_big_seq THEN
SIMP_TAC std_ss [EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
ASM_SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ASL_ATOMIC_ACTION_SEM]);


val ASL_TRACE_SEM_REWRITE = store_thm ("ASL_TRACE_SEM_REWRITE",
``(ASL_TRACE_SEM xenv [] = asla_skip) /\
  (ASL_TRACE_SEM xenv (aa::t) = asla_seq (ASL_ATOMIC_ACTION_SEM xenv aa) (ASL_TRACE_SEM xenv t))``,

SIMP_TAC list_ss [ASL_TRACE_SEM_def, asla_big_seq_def]);


val ASL_TRACE_SEM_APPEND = store_thm ("ASL_TRACE_SEM_APPEND",
``(ASL_TRACE_SEM xenv (t1++t2) = asla_seq (ASL_TRACE_SEM xenv t1) (ASL_TRACE_SEM xenv t2))``,

SIMP_TAC list_ss [ASL_TRACE_SEM_def, asla_big_seq_APPEND,
   asla_big_seq_def]);


val ASL_TRACE_SEM_diverge = store_thm ("ASL_TRACE_SEM_diverge",
``!xenv t. ASL_TRACE_SEM xenv (asl_aa_diverge::t) = \s. SOME {}``,

Cases_on `xenv` THEN
ASM_SIMP_TAC std_ss [FUN_EQ_THM, ASL_TRACE_SEM_REWRITE, asla_seq_def,
   ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM,
   asl_aa_diverge_def,
   asla_diverge_def, IMAGE_EMPTY,
   SUP_fasl_order_def,
   NOT_IN_EMPTY, BIGUNION_EMPTY]);


val asla_seq___ACTION_ORDER = store_thm ("asla_seq___ACTION_ORDER",
``!a1 a2 b1 b2.
(fasl_action_order a1 b1 /\
fasl_action_order a2 b2) ==>
fasl_action_order (asla_seq a1 a2) (asla_seq b1 b2)``,

SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [asla_seq_def] THEN
Cases_on `b1 s = NONE` THEN1 (
   ASM_SIMP_TAC std_ss [fasl_order_THM]
) THEN
`?vb1. b1 s = SOME vb1` by ALL_TAC THEN1 (
   Cases_on `b1 s` THEN FULL_SIMP_TAC std_ss []
) THEN
`?va1. (a1 s = SOME va1) /\ (va1 SUBSET vb1)` by ALL_TAC THEN1 (
   `fasl_order (a1 s) (b1 s)` by PROVE_TAC[] THEN
   POP_ASSUM MP_TAC THEN
   REPEAT (Q.PAT_ASSUM `!s. X s` (K ALL_TAC)) THEN
   ASM_SIMP_TAC std_ss [fasl_order_THM, GSYM LEFT_FORALL_IMP_THM]
) THEN
FULL_SIMP_TAC std_ss [SUP_fasl_order_def] THEN
Cases_on `NONE IN IMAGE b2 vb1` THEN1 (
   ASM_SIMP_TAC std_ss [fasl_order_THM]
) THEN
`~(NONE IN IMAGE a2 va1)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [IN_IMAGE] THEN
   CCONTR_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN
   `b2 x = NONE` by ALL_TAC THEN1 (
      METIS_TAC[fasl_order_THM, option_CLAUSES]
   ) THEN
   METIS_TAC[SUBSET_DEF]
) THEN
ASM_REWRITE_TAC[] THEN

FULL_SIMP_TAC std_ss [fasl_order_THM, SUBSET_DEF, IN_BIGUNION, IN_IMAGE,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `x'` THEN
`?va2. a2 x' = SOME va2` by ALL_TAC THEN1 (
   Cases_on `a2 x'` THENL [
      METIS_TAC[],
      FULL_SIMP_TAC std_ss []
   ]
) THEN
`?vb2. (b2 x' = SOME vb2) /\ (va2 SUBSET vb2)` by ALL_TAC THEN1 (
   Cases_on `b2 x'` THEN1 METIS_TAC[] THEN

   `fasl_order (a2 x') (b2 x')` by PROVE_TAC[] THEN
   POP_ASSUM MP_TAC THEN
   REPEAT (Q.PAT_ASSUM `!s. X s` (K ALL_TAC)) THEN
   ASM_SIMP_TAC std_ss [fasl_order_THM]
) THEN
FULL_SIMP_TAC std_ss [SUBSET_DEF]);



val asla_seq___STAR_ORDER = store_thm ("asla_seq___STAR_ORDER",
``!a1 a2 q1 q2 s1 s2 s f.
(IS_SEPARATION_COMBINATOR f /\
 fasl_order (a1 s1) q1 /\
 fasl_order (a2 s2) q2 /\
 (SOME s = f (SOME s1) (SOME s2)) /\
 ASL_IS_LOCAL_ACTION f a1 /\
 ASL_IS_LOCAL_ACTION f a2) ==>

fasl_order ((asla_seq a1 a2) s)  (fasl_star f q1 q2)``,


Cases_on `q1` THEN SIMP_TAC std_ss [fasl_star_REWRITE, fasl_order_THM] THEN
Cases_on `q2` THEN SIMP_TAC std_ss [fasl_star_REWRITE, fasl_order_THM] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [SOME___asla_seq, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   ASL_IS_LOCAL_ACTION___ALTERNATIVE_DEF, IS_SOME_EXISTS,
   GSYM LEFT_FORALL_IMP_THM] THEN
`COMM f` by METIS_TAC[IS_SEPARATION_COMBINATOR_def] THEN
`?a1s. a1 s = SOME a1s` by METIS_TAC[] THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE, asl_star_def,
   IN_ABS, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
`!e. e IN a1s ==> ?e'. (SOME e = f (SOME e') (SOME s2)) /\ (e' IN s1')` by ALL_TAC THEN1 (
   METIS_TAC[]
) THEN

MATCH_MP_TAC (prove (``(A /\ (A ==> B)) ==> (A /\ B)``, METIS_TAC[])) THEN
CONJ_TAC THEN1 METIS_TAC[COMM_DEF] THEN

REPEAT STRIP_TAC THEN
`?a2x. a2 x''' = SOME a2x` by METIS_TAC[] THEN
`?e'. (SOME x''' = f (SOME e') (SOME s2)) /\ (e' IN s1')` by METIS_TAC[] THEN

Q.PAT_ASSUM `!s1 s2 s3. P s1 s2 s3` (MP_TAC (*a2*) o Q.SPECL [`s2`, `e'`, `x'''`, `s1''`, `a2x`, `x''`]) THEN
`f (SOME s2) (SOME e') = f (SOME e') (SOME s2)` by METIS_TAC[COMM_DEF]  THEN
FULL_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `e'` THEN
Q.EXISTS_TAC `t'` THEN
METIS_TAC[SUBSET_DEF, COMM_DEF]);



val ASL_TRACE_ZIP_def = tDefine "ASL_TRACE_ZIP"
   `(ASL_TRACE_ZIP [] t = {t}) /\
   (ASL_TRACE_ZIP t [] = {t}) /\
   (ASL_TRACE_ZIP (aa1::t1) (aa2::t2) =
      (let z1 = IMAGE (\x. aa1::x) (ASL_TRACE_ZIP t1 (aa2::t2)) in
       let z2 = IMAGE (\x. aa2::x) (ASL_TRACE_ZIP (aa1::t1) t2) in
       let z3 = z1 UNION z2 in
       if (ASL_IS_PRIM_COMMAND_ATOMIC_ACTION aa1 /\
           ASL_IS_PRIM_COMMAND_ATOMIC_ACTION aa2) then
      IMAGE (\x. (asl_aa_check (ASL_GET_PRIM_COMMAND_ATOMIC_ACTION aa1) (ASL_GET_PRIM_COMMAND_ATOMIC_ACTION aa2))::x) z3 else
      z3))`

   (WF_REL_TAC `measure (\(l1, l2). LENGTH l1 + LENGTH l2)` THEN
   SIMP_TAC list_ss [])


val ASL_TRACE_ZIP_PRIME_def = Define
   `(ASL_TRACE_ZIP_PRIME [] t = {t}) /\
   (ASL_TRACE_ZIP_PRIME t [] = {t}) /\
   (ASL_TRACE_ZIP_PRIME (aa1::t1) (aa2::t2) =
      (let z1 = IMAGE (\x. aa1::x) (ASL_TRACE_ZIP t1 (aa2::t2)) in
       let z2 = IMAGE (\x. aa2::x) (ASL_TRACE_ZIP (aa1::t1) t2) in
       z1 UNION z2))`;


val ASL_TRACE_ZIP_THM = store_thm ("ASL_TRACE_ZIP_THM",
``      (ASL_TRACE_ZIP_PRIME [] t = {t}) /\
   (ASL_TRACE_ZIP_PRIME t [] = {t}) /\
   (ASL_TRACE_ZIP_PRIME (aa1::t1) (aa2::t2) =
      (let z1 = IMAGE (\x. aa1::x) (ASL_TRACE_ZIP t1 (aa2::t2)) in
       let z2 = IMAGE (\x. aa2::x) (ASL_TRACE_ZIP (aa1::t1) t2) in
       z1 UNION z2)) /\
   (ASL_TRACE_ZIP [] t = {t}) /\
   (ASL_TRACE_ZIP t [] = {t}) /\
   (ASL_TRACE_ZIP ((asl_aa_pc pc1)::t1) ((asl_aa_pc pc2)::t2) =
      IMAGE (\x. (asl_aa_check pc1 pc2)::x)
         (ASL_TRACE_ZIP_PRIME ((asl_aa_pc pc1)::t1) ((asl_aa_pc pc2)::t2))) /\
   ((~(ASL_IS_PRIM_COMMAND_ATOMIC_ACTION aa1 /\
        ASL_IS_PRIM_COMMAND_ATOMIC_ACTION aa2)) ==>
   (ASL_TRACE_ZIP (aa1::t1) (aa2::t2) =
      (ASL_TRACE_ZIP_PRIME (aa1::t1) (aa2::t2))))``,

Cases_on `t` THEN
SIMP_TAC std_ss [ASL_TRACE_ZIP_def, ASL_TRACE_ZIP_PRIME_def,
   ASL_IS_PRIM_COMMAND_ATOMIC_ACTION_def,
   ASL_GET_PRIM_COMMAND_ATOMIC_ACTION_def, LET_THM, DISJ_IMP_THM]);


val ASL_TRACE_ZIP___REWRITE = store_thm ("ASL_TRACE_ZIP___REWRITE",
``(ASL_TRACE_ZIP [] t = {t}) /\
  (ASL_TRACE_ZIP t [] = {t}) /\
  (ASL_TRACE_ZIP (aa1::t1) (aa2::t2) =
    (let z1 = IMAGE (\x. aa1::x) (ASL_TRACE_ZIP t1 (aa2::t2)) in
     let z2 = IMAGE (\x. aa2::x) (ASL_TRACE_ZIP (aa1::t1) t2) in
     let z3 = z1 UNION z2 in
       if (ASL_IS_PRIM_COMMAND_ATOMIC_ACTION aa1 /\
           ASL_IS_PRIM_COMMAND_ATOMIC_ACTION aa2) then
      IMAGE (\x. (asl_aa_check (ASL_GET_PRIM_COMMAND_ATOMIC_ACTION aa1) (ASL_GET_PRIM_COMMAND_ATOMIC_ACTION aa2))::x) z3 else
      z3))``,
SIMP_TAC std_ss [ASL_TRACE_ZIP_def, ASL_TRACE_ZIP_THM]);



val ASL_TRACE_SEM___check = store_thm ("ASL_TRACE_SEM___check",
``!f lock_env pc1 pc2 t s.
ASL_TRACE_SEM (f, lock_env) (asl_aa_check pc1 pc2::t) s =
(if (?s1 s2. (SOME s = f (SOME s1) (SOME s2)) /\
   IS_SOME (EVAL_asl_prim_command f pc1 s1) /\
   IS_SOME (EVAL_asl_prim_command f pc2 s2))  then
   ASL_TRACE_SEM (f, lock_env) t s else NONE)``,

REPEAT GEN_TAC THEN
Q.MATCH_ABBREV_TAC `
   ASL_TRACE_SEM (f, lock_env) (asl_aa_check pc1 pc2::t) s =
   (if c then ASL_TRACE_SEM (f, lock_env) t s else NONE)` THEN
`(!s1 s2.
    SOME s <> f (SOME s1) (SOME s2) \/
    (EVAL_asl_prim_command f pc1 s1 = NONE) \/
    (EVAL_asl_prim_command f pc2 s2 = NONE)) = ~c` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `c` THEN SIMP_TAC std_ss []
) THEN
ASM_SIMP_TAC list_ss [ASL_TRACE_SEM_def, ASL_ATOMIC_ACTION_SEM_def,
   asla_big_seq_def, asla_check_def, asla_seq_def] THEN
REPEAT STRIP_TAC THEN
Cases_on `c` THEN
ASM_REWRITE_TAC[] THEN
SIMP_TAC std_ss [IMAGE_INSERT, IMAGE_EMPTY,
       SUP_fasl_order___SING]);



val ASL_TRACE_ZIP___SEM_COMM = store_thm ("ASL_TRACE_ZIP___SEM_COMM",
``!xenv t t1 t2. IS_SEPARATION_COMBINATOR (FST xenv) ==>
        (t IN (ASL_TRACE_ZIP t1 t2) ==>
   ?t'. t' IN (ASL_TRACE_ZIP t2 t1) /\
        (ASL_TRACE_SEM xenv t' = ASL_TRACE_SEM xenv t))``,

GEN_TAC THEN
Cases_on `IS_SEPARATION_COMBINATOR (FST xenv)` THEN ASM_REWRITE_TAC[] THEN
Induct_on `t1` THEN1 (
   SIMP_TAC std_ss [ASL_TRACE_ZIP_THM, IN_SING]
) THEN
Induct_on `t2` THEN1 (
   SIMP_TAC std_ss [ASL_TRACE_ZIP_THM, IN_SING]
) THEN
SIMP_TAC std_ss [ASL_TRACE_ZIP_def, LET_THM] THEN
REPEAT GEN_TAC THEN
Q.ABBREV_TAC `AAC =
      (ASL_IS_PRIM_COMMAND_ATOMIC_ACTION h /\
      ASL_IS_PRIM_COMMAND_ATOMIC_ACTION h')` THEN
`ASL_IS_PRIM_COMMAND_ATOMIC_ACTION h' /\ ASL_IS_PRIM_COMMAND_ATOMIC_ACTION h = AAC` by METIS_TAC[] THEN
ASM_SIMP_TAC std_ss [] THEN
POP_ASSUM MP_TAC THEN
Q.SPEC_TAC (`t`, `t`) THEN
Q.SPEC_TAC (`h`, `h`) THEN
Q.SPEC_TAC (`h'`, `h'`) THEN
Q.SPEC_TAC (`AAC`, `AAC`) THEN
POP_ASSUM (K ALL_TAC) THEN
HO_MATCH_MP_TAC (prove (``((!h h' t. X F h h' t) /\ (!h h'. ((!t. X F h h' t) ==> ((!t. Y T h h' t ==> X T h h' t))))) ==> (!AAC:bool h h' t. Y AAC h h' t ==> X AAC h h' t)``,
REPEAT STRIP_TAC THEN Cases_on `AAC` THEN METIS_TAC[])) THEN
REWRITE_TAC [] THEN
CONJ_TAC THEN1 (
   SIMP_TAC std_ss [IN_UNION, IN_IMAGE] THEN
   REPEAT STRIP_TAC THENL [
      RES_TAC THEN
      Q.EXISTS_TAC `h'::t'` THEN
      ASM_SIMP_TAC list_ss [ASL_TRACE_SEM_def, asla_big_seq_def] THEN
      ASM_SIMP_TAC std_ss [GSYM ASL_TRACE_SEM_def],

      RES_TAC THEN
      Q.EXISTS_TAC `h::t'` THEN
      ASM_SIMP_TAC list_ss [ASL_TRACE_SEM_def, asla_big_seq_def] THEN
      ASM_SIMP_TAC std_ss [GSYM ASL_TRACE_SEM_def]
   ]
) THEN

NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
REPEAT GEN_TAC THEN
Q.ABBREV_TAC `Z1 = IMAGE (\x. h'::x) (ASL_TRACE_ZIP t1 (h::t2)) UNION
     IMAGE (\x. h::x) (ASL_TRACE_ZIP (h'::t1) t2)` THEN
Q.ABBREV_TAC `Z2 = IMAGE (\x. h::x) (ASL_TRACE_ZIP t2 (h'::t1)) UNION
       IMAGE (\x. h'::x) (ASL_TRACE_ZIP (h::t2) t1)` THEN

SIMP_TAC std_ss [ASL_IS_PRIM_COMMAND_ATOMIC_ACTION_EXISTS] THEN
STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
ASM_SIMP_TAC std_ss [ASL_GET_PRIM_COMMAND_ATOMIC_ACTION_def, IN_IMAGE] THEN
STRIP_TAC THEN
RES_TAC THEN
Q.EXISTS_TAC `asl_aa_check pc' pc::t'` THEN
ASM_SIMP_TAC list_ss [ASL_TRACE_SEM_REWRITE] THEN
AP_THM_TAC THEN AP_TERM_TAC THEN

Cases_on `xenv` THEN
FULL_SIMP_TAC std_ss [ASL_ATOMIC_ACTION_SEM_def, asla_check_def,
   IS_SEPARATION_COMBINATOR_EXPAND_THM, FUN_EQ_THM] THEN
GEN_TAC THEN
MATCH_MP_TAC (
   prove (``(C = C') ==> ((if C then X else Y) = (if C' then X else Y))``, SIMP_TAC std_ss [])) THEN
METIS_TAC[COMM_DEF]);



val ASL_TRACE_SEM___PARALLEL_DECOMPOSITION = store_thm ("ASL_TRACE_SEM___PARALLEL_DECOMPOSITION",
``!f lock_env q1 q2 s s1 s2 t1 t2 t .
(IS_SEPARATION_COMBINATOR f /\
fasl_order (ASL_TRACE_SEM (f, lock_env) t1 s1) q1 /\
fasl_order (ASL_TRACE_SEM (f, lock_env) t2 s2) q2 /\
(t IN (ASL_TRACE_ZIP t1 t2)) /\
(SOME s = f (SOME s1) (SOME s2))) ==>

fasl_order (ASL_TRACE_SEM (f, lock_env) t s) (fasl_star f q1 q2)``,


NTAC 2 GEN_TAC THEN
Cases_on `IS_SEPARATION_COMBINATOR f` THEN ASM_REWRITE_TAC[] THEN
Induct_on `t1` THEN1 (
   (*t1 empty*)
   SIMP_TAC std_ss [ASL_TRACE_ZIP_THM, IN_SING,
      fasl_star_REWRITE] THEN
   REPEAT GEN_TAC THEN
   Q.ABBREV_TAC `la = ASL_TRACE_SEM (f,lock_env) t2` THEN

   `(q1 = NONE) \/ (?vq1. q1 = SOME vq1)` by (Cases_on `q1` THEN SIMP_TAC std_ss []) THEN1 (
      ASM_SIMP_TAC std_ss [fasl_star_REWRITE, fasl_order_THM]
   ) THEN
   `(q2 = NONE) \/ (?vq2. q2 = SOME vq2)` by (Cases_on `q2` THEN SIMP_TAC std_ss []) THEN1 (
      ASM_SIMP_TAC std_ss [fasl_star_REWRITE, fasl_order_THM]
   ) THEN

   `ASL_IS_LOCAL_ACTION f la` by METIS_TAC[ASL_IS_LOCAL_ACTION___ASL_TRACE_SEM] THEN
   ASM_SIMP_TAC std_ss [ASL_TRACE_SEM_REWRITE, asla_skip_def, fasl_order_THM,
              INSERT_SUBSET, EMPTY_SUBSET] THEN
   STRIP_TAC THEN
   Q.PAT_ASSUM `ASL_IS_LOCAL_ACTION f la` (MP_TAC o
                   Q.SPECL [`s2`, `s1`] o
                   REWRITE_RULE [ASL_IS_LOCAL_ACTION_def]) THEN
   `f (SOME s2) (SOME s1) = SOME s` by PROVE_TAC[IS_SEPARATION_COMBINATOR_def, COMM_DEF] THEN
   Q.PAT_ASSUM `SOME s = X` (K ALL_TAC) THEN
   ASM_SIMP_TAC std_ss [ASL_IS_SEPARATE_def] THEN
   SIMP_TAC std_ss [fasl_order_THM, fasl_star_REWRITE,
          GSYM LEFT_FORALL_IMP_THM] THEN
   SIMP_TAC std_ss [asl_star_def, SUBSET_DEF, IN_ABS, IN_SING] THEN
   METIS_TAC[IS_SEPARATION_COMBINATOR_def, COMM_DEF, SUBSET_DEF]
) THEN
Induct_on `t2` THEN1 (
   POP_ASSUM (K ALL_TAC) (*Induct Hypothesis not needed*) THEN
   (*t2 empty*)
   SIMP_TAC std_ss [ASL_TRACE_ZIP_THM, IN_SING,
      fasl_star_REWRITE] THEN
   REPEAT GEN_TAC THEN
   Q.ABBREV_TAC `la = ASL_TRACE_SEM (f,lock_env) (h::t1)` THEN
   `(q1 = NONE) \/ (?vq1. q1 = SOME vq1)` by (Cases_on `q1` THEN SIMP_TAC std_ss []) THEN1 (
      ASM_SIMP_TAC std_ss [fasl_star_REWRITE, fasl_order_THM]
   ) THEN
   `(q2 = NONE) \/ (?vq2. q2 = SOME vq2)` by (Cases_on `q2` THEN SIMP_TAC std_ss []) THEN1 (
      ASM_SIMP_TAC std_ss [fasl_star_REWRITE, fasl_order_THM]
   ) THEN

   `ASL_IS_LOCAL_ACTION f la` by METIS_TAC[ASL_IS_LOCAL_ACTION___ASL_TRACE_SEM] THEN
   ASM_SIMP_TAC list_ss [fasl_order_THM, ASL_TRACE_SEM_def, asla_big_seq_def, asla_skip_def,
      asl_star_def, SUBSET_DEF, IN_ABS, IN_SING, fasl_star_REWRITE] THEN
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM,
      LOCALITY_CHARACTERISATION] THEN
   `?las. la s = SOME las` by ALL_TAC THEN1 (
      REWRITE_TAC[GSYM IS_SOME_EXISTS] THEN
      Q.PAT_ASSUM `TRANS_FUNC_SAFETY_MONOTONICITY f la` (MATCH_MP_TAC o REWRITE_RULE[TRANS_FUNC_SAFETY_MONOTONICITY_REWRITE]) THEN
      Q.EXISTS_TAC `s1` THEN
      Q.EXISTS_TAC `s2` THEN
      ASM_SIMP_TAC std_ss []
   ) THEN
   ASM_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `TRANS_FUNC_FRAME_PROPERTY f la` (MP_TAC o Q.SPECL [`s1`, `s2`, `s`, `s1'`, `las`, `x`] o REWRITE_RULE[TRANS_FUNC_FRAME_PROPERTY_def]) THEN
   ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[]
) THEN

REPEAT GEN_TAC THEN
`(q1 = NONE) \/ (?vq1. q1 = SOME vq1)` by (Cases_on `q1` THEN SIMP_TAC std_ss []) THEN1 (
   ASM_SIMP_TAC std_ss [fasl_star_REWRITE, fasl_order_THM]
) THEN
`(q2 = NONE) \/ (?vq2. q2 = SOME vq2)` by (Cases_on `q2` THEN SIMP_TAC std_ss []) THEN1 (
   ASM_SIMP_TAC std_ss [fasl_star_REWRITE, fasl_order_THM]
) THEN

ASM_SIMP_TAC std_ss [ASL_TRACE_ZIP_def, LET_THM] THEN
REPEAT STRIP_TAC THEN
Q.ABBREV_TAC `z3 = IMAGE (\x. h'::x) (ASL_TRACE_ZIP t1 (h::t2)) UNION
              IMAGE (\x. h::x) (ASL_TRACE_ZIP (h'::t1) t2)` THEN

(*forget about the check. It evaluates to skip anyhow*)
Tactical.REVERSE (`!t3. t3 IN z3 ==> (fasl_order (ASL_TRACE_SEM (f,lock_env) t3 s)
      (fasl_star f (SOME vq1) (SOME vq2)))` by ALL_TAC) THEN1 (

   Cases_on `~ASL_IS_PRIM_COMMAND_ATOMIC_ACTION h'` THEN1 METIS_TAC[] THEN
   Cases_on `~ASL_IS_PRIM_COMMAND_ATOMIC_ACTION h` THEN1 METIS_TAC[] THEN
   FULL_SIMP_TAC std_ss [ASL_IS_PRIM_COMMAND_ATOMIC_ACTION_EXISTS] THEN
   FULL_SIMP_TAC std_ss [ASL_GET_PRIM_COMMAND_ATOMIC_ACTION_def, IN_IMAGE] THEN
   ASM_SIMP_TAC std_ss [ASL_TRACE_SEM___check, COND_RAND, COND_RATOR] THEN

   SIMP_TAC std_ss [fasl_star_REWRITE, fasl_order_THM] THEN
   Q.EXISTS_TAC `s1` THEN
   Q.EXISTS_TAC `s2` THEN
   ASM_REWRITE_TAC[] THEN
   Q.PAT_ASSUM `fasl_order X (SOME vq1)` MP_TAC THEN
   Q.PAT_ASSUM `fasl_order X (SOME vq2)` MP_TAC THEN
   ASM_SIMP_TAC list_ss [ASL_TRACE_SEM_def, fasl_order_THM,
      asla_big_seq_def, SOME___asla_seq, ASL_ATOMIC_ACTION_SEM_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC std_ss []
) THEN
Q.PAT_ASSUM `t IN X` (K ALL_TAC) THEN

(*second conjunct,
    ((ASL_ATOMIC_ACTION_SEM (env,lock_env) h) = la1)
    ((ASL_TRACE_SEM (env,lock_env) x) = la2)
    ((ASL_TRACE_SEM (env,lock_env) t2) = la3)

   REPEAT STRIP_TAC THEN

   Q.ABBREV_TAC `la1 = (ASL_ATOMIC_ACTION_SEM (env,lock_env) h)`
   Q.ABBREV_TAC `la2 = (ASL_TRACE_SEM (env,lock_env) x)`
   Q.ABBREV_TAC `la3 = (ASL_TRACE_SEM (env,lock_env) t2)`
       ((ASL_TRACE_SEM (env,lock_env) t2) = la3)

*)

Q.UNABBREV_TAC `z3` THEN
ASM_SIMP_TAC std_ss [IN_UNION, IN_IMAGE, DISJ_IMP_THM, FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM,
    ASL_TRACE_SEM_REWRITE] THEN

Tactical.REVERSE (
`!la1 la2 la3 vq1 vq2 s s1 s2. (
   (ASL_IS_LOCAL_ACTION f la1) /\
   (ASL_IS_LOCAL_ACTION f la2) /\
   (ASL_IS_LOCAL_ACTION f la3) /\
   (SOME s = f (SOME s1) (SOME s2)) /\
   (fasl_order ((asla_seq la1 la3) s2) (SOME vq2)) /\
   (!s' s2' q2. fasl_order (la3 s2') q2 /\
             (SOME s' = f (SOME s1) (SOME s2')) ==>
      fasl_order (la2 s') (fasl_star f (SOME vq1) q2)))

==>
   (fasl_order ((asla_seq la1 la2) s) (fasl_star f (SOME vq1) (SOME vq2)))` by ALL_TAC) THEN1 (

   REPEAT STRIP_TAC THENL [
      `COMM (fasl_star f)` by ALL_TAC THEN1 (
         SIMP_TAC std_ss [fasl_star_REWRITE] THEN
         METIS_TAC[IS_COMM_MONOID___asl_star_emp, COMM_MONOID_THM]
      ) THEN
      `fasl_star f (SOME vq1) (SOME vq2) =
        fasl_star f (SOME vq2) (SOME vq1)` by METIS_TAC[COMM_DEF] THEN
      ASM_REWRITE_TAC[] THEN
      Q.PAT_ASSUM `!la1 la2. P la1 la2` MATCH_MP_TAC THEN
      Q.EXISTS_TAC `ASL_TRACE_SEM (f,lock_env) t1` THEN
      Q.EXISTS_TAC `s2` THEN
      Q.EXISTS_TAC `s1` THEN
      FULL_SIMP_TAC std_ss [ASL_TRACE_SEM_REWRITE] THEN
      REPEAT STRIP_TAC THENL [
         METIS_TAC[ASL_IS_LOCAL_ACTION___ASL_ATOMIC_ACTION_SEM],
         METIS_TAC[ASL_IS_LOCAL_ACTION___ASL_TRACE_SEM],
         METIS_TAC[ASL_IS_LOCAL_ACTION___ASL_TRACE_SEM],
         METIS_TAC[IS_SEPARATION_COMBINATOR_def, COMM_DEF],

         Q.PAT_ASSUM `!h2'' q1'. P h2'' q1'` (K ALL_TAC) THEN
         `fasl_star f (SOME vq2) q2' = fasl_star f q2' (SOME vq2)` by METIS_TAC[COMM_DEF] THEN
         ASM_REWRITE_TAC[] THEN

         Q.PAT_ASSUM `!h2'' q1'. P h2'' q1'` HO_MATCH_MP_TAC THEN
         Q.EXISTS_TAC `s2'` THEN
         Q.EXISTS_TAC `s2` THEN
         Q.EXISTS_TAC `h::t2` THEN
         ASM_SIMP_TAC std_ss [ASL_TRACE_SEM_REWRITE] THEN
         METIS_TAC[IS_SEPARATION_COMBINATOR_def, COMM_DEF]
      ],


      Q.PAT_ASSUM `!la1 la2. P la1 la2` MATCH_MP_TAC THEN
      Q.EXISTS_TAC `ASL_TRACE_SEM (f,lock_env) t2` THEN
      Q.EXISTS_TAC `s1` THEN
      Q.EXISTS_TAC `s2` THEN
      FULL_SIMP_TAC std_ss [ASL_TRACE_SEM_REWRITE] THEN
      REPEAT STRIP_TAC THENL [
         METIS_TAC[ASL_IS_LOCAL_ACTION___ASL_ATOMIC_ACTION_SEM],
         METIS_TAC[ASL_IS_LOCAL_ACTION___ASL_TRACE_SEM],
         METIS_TAC[ASL_IS_LOCAL_ACTION___ASL_TRACE_SEM],

         Q.PAT_ASSUM `!h2'' q1'. P h2'' q1'` HO_MATCH_MP_TAC THEN
         Q.EXISTS_TAC `h'` THEN
         Q.EXISTS_TAC `s1` THEN
         Q.EXISTS_TAC `s2'` THEN
         ASM_SIMP_TAC std_ss []
      ]
   ]
) THEN



Q.PAT_ASSUM `IS_SEPARATION_COMBINATOR f` MP_TAC THEN
REPEAT (POP_ASSUM (K ALL_TAC)) THEN
REPEAT STRIP_TAC THEN

`?vq3. (la1 s2 = SOME vq3) /\
      (!s. s IN vq3 ==> IS_SOME (la3 s)) /\
      (BIGUNION (IMAGE THE (IMAGE la3 vq3)) SUBSET vq2)` by ALL_TAC THEN1 (
FULL_SIMP_TAC std_ss [fasl_order_THM, SOME___asla_seq] THEN
METIS_TAC[]) THEN

SIMP_TAC std_ss [fasl_star_REWRITE, fasl_order_THM, asl_star_def,
   SUBSET_DEF, IN_ABS, SOME___asla_seq, GSYM LEFT_EXISTS_AND_THM,
   GSYM RIGHT_EXISTS_AND_THM] THEN

`?vq4. (la1 s = SOME vq4) /\ (!x. x IN vq4 ==> ?x0. (SOME x = f (SOME s1) (SOME x0)) /\ (x0 IN vq3))` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `ASL_IS_LOCAL_ACTION f la1` MP_TAC THEN
   ASM_SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ALTERNATIVE_DEF, IS_SOME_EXISTS,
      GSYM LEFT_EXISTS_IMP_THM, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM  `!s1 s2 s3 y. P s1 s2 s3 y ==> (?y. la1 s3 = SOME y)` (
      MP_TAC o Q.SPECL [`s2`, `s1`, `s`]) THEN
   `f (SOME s2) (SOME s1) = f (SOME s1) (SOME s2)` by METIS_TAC[IS_SEPARATION_COMBINATOR_def, COMM_DEF] THEN
   ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM  `!s1 s2 s3 y. P s1 s2 s3 y` (
      MP_TAC o Q.SPECL [`s2`, `s1`, `s`, `vq3`, `y`, `x`]) THEN
   ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN
   METIS_TAC[IS_SEPARATION_COMBINATOR_def, COMM_DEF]
) THEN
FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN

ASM_SIMP_TAC std_ss [fasl_star_REWRITE, fasl_order_THM, SUBSET_DEF, SOME___asla_seq,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, IN_BIGUNION, IN_IMAGE,
   GSYM LEFT_FORALL_IMP_THM, asl_star_def, IN_ABS] THEN

HO_MATCH_MP_TAC (prove (``(!e. (P e /\ !x. Q x e)) ==> ((!e. P e) /\ (!x e. Q x e))``, METIS_TAC[])) THEN
GEN_TAC THEN
Cases_on `x' IN vq4` THEN ASM_REWRITE_TAC[] THEN

`?x0. (SOME x' = f (SOME s1) (SOME x0)) /\ x0 IN vq3` by METIS_TAC[] THEN
`?vq5. la3 x0 = SOME vq5` by METIS_TAC[IS_SOME_EXISTS] THEN
`fasl_order (la3 x0) (SOME vq5)` by ASM_SIMP_TAC std_ss [fasl_order_THM, SUBSET_REFL] THEN
`fasl_order (la2 x') (fasl_star f (SOME vq1) (SOME vq5))` by METIS_TAC[] THEN
POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC std_ss [fasl_star_REWRITE, fasl_order_THM, GSYM LEFT_FORALL_IMP_THM,
   SUBSET_DEF, asl_star_def, IN_ABS] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (`!q. q IN vq5 ==> q IN vq2` by ALL_TAC) THEN1 METIS_TAC[] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!x x''. P x x''` MATCH_MP_TAC THEN
Q.EXISTS_TAC `x0` THEN
ASM_SIMP_TAC std_ss []);






(* -------------------------------------------------------------------------- *)
(* Synchroniced traces                                                         *)
(* -------------------------------------------------------------------------- *)

val ASL_TRACE_GET_LOCKS_def = Define `
   ASL_TRACE_GET_LOCKS L = FILTER (ASL_IS_LOCK_ATOMIC_ACTION L)`

val ASL_TRACE_GET_LOCKS_REWRITE = store_thm ("ASL_TRACE_GET_LOCKS_REWRITE",
   ``(ASL_TRACE_GET_LOCKS L [] = []) /\
      (ASL_IS_LOCK_ATOMIC_ACTION L e ==> (ASL_TRACE_GET_LOCKS L (e::t) = e::ASL_TRACE_GET_LOCKS L t)) /\
      (~(ASL_IS_LOCK_ATOMIC_ACTION L e) ==> (ASL_TRACE_GET_LOCKS L (e::t) = ASL_TRACE_GET_LOCKS L t)) /\
      (ASL_TRACE_GET_LOCKS L (t1++t2) = ASL_TRACE_GET_LOCKS L t1 ++ ASL_TRACE_GET_LOCKS L t2) /\
      (ASL_TRACE_GET_LOCKS {} t = [])``,

SIMP_TAC list_ss [ASL_TRACE_GET_LOCKS_def, FILTER_APPEND] THEN
Induct_on `t` THENL [
   SIMP_TAC list_ss [],

   Cases_on `h` THEN
   ASM_SIMP_TAC list_ss [ASL_IS_LOCK_ATOMIC_ACTION_def, NOT_IN_EMPTY]
]);


val ASL_TRACE_GET_SING_LOCKS_def = Define `
   ASL_TRACE_GET_SING_LOCKS l = ASL_TRACE_GET_LOCKS {l}`

val ASL_TRACE_GET_SING_LOCKS_REWRITE = store_thm ("ASL_TRACE_GET_SING_LOCKS_REWRITE",
   ``(ASL_TRACE_GET_SING_LOCKS l [] = []) /\
      (ASL_IS_SING_LOCK_ATOMIC_ACTION l e ==> (ASL_TRACE_GET_SING_LOCKS l (e::t) = e::ASL_TRACE_GET_SING_LOCKS l t)) /\
      (~(ASL_IS_SING_LOCK_ATOMIC_ACTION l e) ==> (ASL_TRACE_GET_SING_LOCKS l (e::t) = ASL_TRACE_GET_SING_LOCKS l t)) /\
      (ASL_TRACE_GET_SING_LOCKS l (t1++t2) = ASL_TRACE_GET_SING_LOCKS l t1 ++ ASL_TRACE_GET_SING_LOCKS l t2)``,

SIMP_TAC list_ss [ASL_TRACE_GET_SING_LOCKS_def,
   ASL_TRACE_GET_LOCKS_REWRITE, ASL_IS_SING_LOCK_ATOMIC_ACTION_def]);


val ASL_TRACE_REMOVE_LOCKS_def = Define `
   ASL_TRACE_REMOVE_LOCKS L = FILTER (\x. ~ (ASL_IS_LOCK_ATOMIC_ACTION L x))`


val ASL_TRACE_REMOVE_LOCKS_REWRITE = store_thm ("ASL_TRACE_REMOVE_LOCKS_REWRITE",
``
(!L. ASL_TRACE_REMOVE_LOCKS L [] = []) /\
(!L h t. ASL_TRACE_REMOVE_LOCKS L (h::t) =
   if (ASL_IS_LOCK_ATOMIC_ACTION L h) then ASL_TRACE_REMOVE_LOCKS L t else
      h::(ASL_TRACE_REMOVE_LOCKS L t)) /\
(!L t1 t2. ASL_TRACE_REMOVE_LOCKS L (t1 ++ t2) =
         ASL_TRACE_REMOVE_LOCKS L t1 ++ ASL_TRACE_REMOVE_LOCKS L t2)``,

SIMP_TAC list_ss [ASL_TRACE_REMOVE_LOCKS_def, FILTER_APPEND] THEN
METIS_TAC[]);


val ASL_TRACE_GET_REMOVE_LOCKS = store_thm ("ASL_TRACE_GET_REMOVE_LOCKS",
``!L L' t. (ASL_TRACE_GET_LOCKS L (ASL_TRACE_REMOVE_LOCKS L' t) =
        ASL_TRACE_GET_LOCKS (L DIFF L') t) /\
        (ASL_TRACE_REMOVE_LOCKS L' (ASL_TRACE_GET_LOCKS L t) =
        ASL_TRACE_GET_LOCKS (L DIFF L') t) /\
        (ASL_TRACE_GET_LOCKS L (ASL_TRACE_GET_LOCKS L' t) =
        ASL_TRACE_GET_LOCKS (L INTER L') t) /\
        (ASL_TRACE_REMOVE_LOCKS L (ASL_TRACE_REMOVE_LOCKS L' t) =
        ASL_TRACE_REMOVE_LOCKS (L UNION L') t)``,

SIMP_TAC std_ss [ASL_TRACE_REMOVE_LOCKS_def, ASL_TRACE_GET_LOCKS_def,
   FILTER_FILTER] THEN
REPEAT GEN_TAC THEN
REPEAT CONJ_TAC THEN (
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SIMP_TAC std_ss [FUN_EQ_THM] THEN
   Cases_on `x` THEN
   SIMP_TAC std_ss [ASL_IS_LOCK_ATOMIC_ACTION_def, IN_DIFF, IN_UNION, IN_INTER] THEN
   METIS_TAC[]
));


val ASL_TRACE_IS_LOCK_SYNCHRONISED_def = Define `
   ASL_TRACE_IS_LOCK_SYNCHRONISED l t =
      LIST_STAR [asl_aa_prolaag l;asl_aa_verhoog l] (ASL_TRACE_GET_LOCKS {l} t)`;

val ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_def = Define `
   ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l t =
      ((ASL_TRACE_GET_LOCKS {l} t) = LIST_NUM_STAR n [asl_aa_prolaag l;asl_aa_verhoog l])`;

val ASL_TRACE_IS_LOCK_SYNCHRONISED___NUM = store_thm ("ASL_TRACE_IS_LOCK_SYNCHRONISED___NUM",
``      ASL_TRACE_IS_LOCK_SYNCHRONISED l t =
      ?n. ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l t``,

SIMP_TAC std_ss [ASL_TRACE_IS_LOCK_SYNCHRONISED_def, ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_def,
   LIST_STAR_def]);


val ASL_TRACE_IS_SYNCHRONISED_def = Define `
   ASL_TRACE_IS_SYNCHRONISED t =
   !l. ASL_TRACE_IS_LOCK_SYNCHRONISED l t`


val ASL_TRACE_IS_LOCK_FREE_def = Define `
   ASL_TRACE_IS_LOCK_FREE L t =
   EVERY (\a. ~(ASL_IS_LOCK_ATOMIC_ACTION L a)) t`;


val ASL_TRACE_IS_LOCK_FREE_REWRITE = store_thm ("ASL_TRACE_IS_LOCK_FREE_REWRITE",
   ``(ASL_TRACE_IS_LOCK_FREE L []) /\
      (ASL_TRACE_IS_LOCK_FREE L (h::l) =
      (~(ASL_IS_LOCK_ATOMIC_ACTION L h) /\ ASL_TRACE_IS_LOCK_FREE L l)) /\
      (ASL_TRACE_IS_LOCK_FREE L (l1++l2) =
      (ASL_TRACE_IS_LOCK_FREE L l1 /\ ASL_TRACE_IS_LOCK_FREE L l2)) /\
      (ASL_IS_LOCK_ATOMIC_ACTION {x} a =
       ASL_IS_SING_LOCK_ATOMIC_ACTION x a)``,

SIMP_TAC list_ss [ASL_TRACE_IS_LOCK_FREE_def, ASL_IS_SING_LOCK_ATOMIC_ACTION_def]);


(* -------------------------------------------------------------------------- *)
(* Proto traces / program definitions                                         *)
(* -------------------------------------------------------------------------- *)

val asl_proto_trace_def =
 Hol_datatype
  `asl_proto_trace =
             asl_pt_prim_command of 'state asl_prim_command
           |      asl_pt_seq of asl_proto_trace => asl_proto_trace
           |      asl_pt_procedure_call of 'name => 'arg
           |      asl_pt_parallel of asl_proto_trace => asl_proto_trace
           |      asl_pt_lock_declaration of 'lock => asl_proto_trace
           |      asl_pt_critical_section of 'lock => asl_proto_trace`;

val asl_proto_trace_size_def = fetch "-" "asl_proto_trace_size_def";
val asl_proto_trace_11 = fetch "-" "asl_proto_trace_11";
val asl_proto_trace_distinct = fetch "-" "asl_proto_trace_distinct";


val _ = type_abbrev ("asl_program", Type `:('a, 'b, 'c, 'd) asl_proto_trace set`);


(* ------------------------------------ *)
(* Some simple programs / proto traces  *)
(* ------------------------------------ *)

val asl_pt_skip_def = Define `asl_pt_skip = asl_pt_prim_command (asl_pc_skip)`;
val asl_pt_diverge_def = Define `asl_pt_diverge = asl_pt_prim_command (asl_pc_diverge)`;


val asl_prog_prim_command_def = Define `asl_prog_prim_command pc = {asl_pt_prim_command pc}`;
val asl_prog_skip_def = Define `asl_prog_skip = asl_prog_prim_command asl_pc_skip`;
val asl_prog_diverge_def = Define `asl_prog_diverge = asl_prog_prim_command (asl_pc_diverge)`;
val asl_prog_assume_def = Define `asl_prog_assume P = asl_prog_prim_command (asl_pc_assume P)`;
val asl_prog_assert_def = Define `asl_prog_assert P = asl_prog_prim_command (asl_pc_assert P)`;
val asl_prog_fail_def = Define `asl_prog_fail = asl_prog_prim_command asl_pc_fail`;
val asl_prog_best_local_action_def = Define `asl_prog_best_local_action P Q = asl_prog_prim_command (asl_pc_shallow_command (\f. best_local_action f P Q))`
val asl_prog_quant_best_local_action_def = Define `asl_prog_quant_best_local_action qP qQ = asl_prog_prim_command (asl_pc_shallow_command (\f. quant_best_local_action f qP qQ))`

val asl_prog_seq_def = Define `asl_prog_seq p1 p2 =
   \pt. ?pt1 pt2. (pt = asl_pt_seq pt1 pt2) /\ pt1 IN p1 /\ pt2 IN (asl_pt_diverge INSERT p2)`;


val asl_prog_choice_def = Define `asl_prog_choice = $UNION`;


val asl_prog_seq_choice = store_thm ("asl_prog_seq_choice",
``!P1 P2 P3.
(asl_prog_seq (asl_prog_choice P1 P2) P3 =
 asl_prog_choice (asl_prog_seq P1 P3) (asl_prog_seq P2 P3)) /\

(asl_prog_seq P3 (asl_prog_choice P1 P2) =
 asl_prog_choice (asl_prog_seq P3 P1) (asl_prog_seq P3 P2))``,

SIMP_TAC std_ss [asl_prog_choice_def, asl_prog_seq_def, EXTENSION] THEN
SIMP_TAC std_ss [IN_ABS, IN_UNION, IN_INSERT, GSYM EXISTS_OR_THM] THEN
REPEAT STRIP_TAC THEN (
   REDEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) []
));


val asl_prog_repeat_num_def = Define `
(asl_prog_repeat_num 0 p = asl_prog_skip) /\
(asl_prog_repeat_num (SUC n) p =
\pt. ?pt1 pt2. (pt = asl_pt_seq pt1 pt2) /\ pt1 IN p /\
               pt2 IN asl_prog_repeat_num n p)`;

val asl_prog_ndet_def = Define `asl_prog_ndet (pset:('a, 'b, 'c, 'd) asl_program set) =
             BIGUNION pset`;

val asl_prog_block_def = Define `(asl_prog_block [] = asl_prog_skip) /\
              (asl_prog_block [p1] = p1) /\
              (asl_prog_block (p1::p2::L) = asl_prog_seq p1 (asl_prog_block (p2::L)))`;


val asl_prog_kleene_star_def = Define `asl_prog_kleene_star p =
\pt. ?n. pt IN asl_prog_repeat_num n p`;

val asl_prog_procedure_call_def = Define `asl_prog_procedure_call p arg = {asl_pt_procedure_call p arg}`;

val asl_prog_parallel_def = Define `asl_prog_parallel p1 p2 =
\pt. ?pt1 pt2. (pt = asl_pt_parallel pt1 pt2) /\ pt1 IN p1 /\ pt2 IN p2`;

val asl_prog_lock_declaration_def = Define `asl_prog_lock_declaration l p =
IMAGE (asl_pt_lock_declaration l) p`;

val asl_prog_critical_section_def = Define `asl_prog_critical_section l p =
IMAGE (asl_pt_critical_section l) p`;

val asl_prog_cond_critical_section_def = Define `asl_prog_cond_critical_section l c p =
asl_prog_critical_section l (asl_prog_seq
            (asl_prog_prim_command (asl_pc_assume c))
            p)`;


val asl_prog_choose_constants_def = Define `
asl_prog_choose_constants prog expL =

asl_prog_ndet
(IMAGE (\constL.
asl_prog_seq
   (asl_prog_prim_command (asl_pc_assume (asl_pred_bigand
      (MAP (\x. asl_pred_prim (\f s. (FST x) s = SOME (SND x)))
      (ZIP (expL, constL))))))
   (prog constL))
 (\l. LENGTH l = LENGTH expL))`;



val asl_prog_ext_procedure_call_def = Define `
(asl_prog_ext_procedure_call name (ref_argL, val_argL)) =
asl_prog_choose_constants
   (\constL.(asl_prog_procedure_call name (ref_argL, constL)))
   val_argL`;


val asl_prog_ext_parallel_procedure_call_def = Define `
asl_prog_ext_parallel_procedure_call name1 (ref_argL1, val_argL1)
                  name2 (ref_argL2, val_argL2) =

asl_prog_choose_constants
   (\constL1. asl_prog_choose_constants (\constL2.
          (asl_prog_parallel
        (asl_prog_procedure_call name1 (ref_argL1, constL1))
        (asl_prog_procedure_call name2 (ref_argL2, constL2))))
          val_argL2)
   val_argL1`;


val asl_procedure_call_preserve_names_wrapper_def = Define `
    asl_procedure_call_preserve_names_wrapper ref_args val_args c =
   \ (arg_refL, arg_valL).
    asl_and (K (LIST_UNROLL_GIVEN_ELEMENT_NAMES arg_valL val_args /\
           LIST_UNROLL_GIVEN_ELEMENT_NAMES arg_refL ref_args))
       (c (arg_refL, arg_valL))`;


val asl_prog_best_local_action___ALTERNATIVE_DEF = store_thm ("asl_prog_best_local_action___ALTERNATIVE_DEF",
``asl_prog_best_local_action P Q = asl_prog_quant_best_local_action (K P) (K Q)``,
SIMP_TAC std_ss [asl_prog_best_local_action_def, asl_prog_quant_best_local_action_def,
       quant_best_local_action___QUANT_ELIM]);


val asl_procedure_call_preserve_names_wrapper_ELIM =
store_thm ("asl_procedure_call_preserve_names_wrapper_ELIM",
``!ref_args val_args c x.
((LENGTH ref_args = LENGTH (FST x)) /\
 (LENGTH val_args = LENGTH (SND x))) ==>
(asl_procedure_call_preserve_names_wrapper ref_args val_args c x =
 c x)``,
REPEAT STRIP_TAC THEN
Cases_on `x` THEN
ASM_SIMP_TAC std_ss [asl_procedure_call_preserve_names_wrapper_def,
   LIST_UNROLL_GIVEN_ELEMENT_NAMES_def, asl_bool_REWRITES]);


val asl_prog_cond_def = Define `
   asl_prog_cond c pTrue pFalse =
      asl_prog_choice
         (asl_prog_seq
            (asl_prog_prim_command (asl_pc_assume c))
            pTrue
         )
         (asl_prog_seq
            (asl_prog_prim_command (asl_pc_assume (asl_pred_neg c)))
            pFalse
         )`;

val asl_prog_while_def = Define `
   asl_prog_while c p =
      asl_prog_seq
         (asl_prog_kleene_star
            (asl_prog_seq
               (asl_prog_prim_command (asl_pc_assume c))
               p
            ))
         (asl_prog_prim_command (asl_pc_assume (asl_pred_neg c)))`;


val asl_prog_forall_def = Define `
   asl_prog_forall body =
      BIGUNION (IMAGE body UNIV)`;


val asl_prog_assume_true = store_thm (
"asl_prog_assume_true",
``((asl_prog_assume asl_pred_true) = (asl_prog_skip))``,
SIMP_TAC std_ss [asl_prog_assume_def,
   asl_prog_skip_def, asl_pc_assume_true___skip]);

val asl_prog_assume_false = store_thm (
"asl_prog_assume_false",
``(asl_prog_assume asl_pred_false) = (asl_prog_diverge)``,
SIMP_TAC std_ss [asl_prog_assume_def,
   asl_prog_diverge_def, asl_pc_assume_false___diverge]);


val asl_prog_aquire_lock_def =
Define `asl_prog_aquire_lock c P =
   asl_prog_seq
   (asl_prog_prim_command (asl_pc_shallow_command
        (\f. asla_materialisation f P)))
   (asl_prog_prim_command (asl_pc_assume c))`;


val asl_prog_release_lock_def =
Define `asl_prog_release_lock P =
   (asl_prog_prim_command (asl_pc_shallow_command
        (\f. asla_annihilation f P)))`;



val asl_prog_best_local_action___false_pre =
store_thm ("asl_prog_best_local_action___false_pre",
``asl_prog_best_local_action asl_false Q = asl_prog_fail``,
SIMP_TAC std_ss [asl_prog_best_local_action_def,
       asl_prog_fail_def, asl_pc_fail_def,
       asl_prog_prim_command_def, asla_fail_def,
       best_local_action___false_pre,
       combinTheory.K_DEF]);


val asl_prog_quant_best_local_action___false_pre =
store_thm ("asl_prog_quant_best_local_action___false_pre",
``asl_prog_quant_best_local_action (\x. asl_false) Qq =
  asl_prog_fail``,

SIMP_TAC std_ss [asl_prog_quant_best_local_action_def,
       asl_prog_fail_def, asl_pc_fail_def, asla_fail_def,
       quant_best_local_action___false_pre,
       combinTheory.K_DEF]);



val asl_prog_prim_command_11 = store_thm ("asl_prog_prim_command_11",
``(asl_prog_prim_command pc1 = asl_prog_prim_command pc2) =
  (pc1 = pc2)``,
SIMP_TAC std_ss [EXTENSION, asl_prog_prim_command_def, IN_SING] THEN
METIS_TAC[asl_proto_trace_11]);



val asl_prog_quant_best_local_action___EQ_IMPL =
store_thm ("asl_prog_quant_best_local_action___EQ_IMPL",
``!f qP1 qP2 qQ1 qQ2 c1 c2.

((!x. ~(c1 x) ==> (qP1 x = asl_false)) /\
 (!x. ~(c2 x) ==> (qP2 x = asl_false)) /\
 (!y. c2 y ==> ?x. (y = f x) /\ c1 x) /\
 ((?x. ~(c1 x)) = (?x. ~(c2 x))) /\
 (!arg. c1 arg ==>
   ((qP1 arg = qP2 (f arg)) /\ (qQ1 arg = qQ2 (f arg)))))

 ==>

(asl_prog_quant_best_local_action qP1 qQ1 =
asl_prog_quant_best_local_action qP2 qQ2)
``,


REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [asl_prog_quant_best_local_action_def,
       asl_prog_prim_command_11,
       asl_prim_command_11] THEN
SIMP_TAC std_ss [FUN_EQ_THM] THEN
SIMP_TAC std_ss [quant_best_local_action_def] THEN
REPEAT GEN_TAC THEN
AP_THM_TAC THEN AP_TERM_TAC THEN
ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC std_ss [] THEN
METIS_TAC[best_local_action___false_pre]);




(* ------------------------------------ *)
(* Comments                             *)
(* ------------------------------------ *)

val asl_comment_loop_invariant_def = Define `
asl_comment_loop_invariant x p = p`

val asl_comment_block_spec_def = Define `
asl_comment_block_spec x p = p`

val asl_comment_loop_spec_def = Define `
asl_comment_loop_spec x p = p`

val asl_comment_loop_unroll_def = Define `
asl_comment_loop_unroll (x:num) p = p`

val asl_comment_location_def = Define `
asl_comment_location (x:label list) p = p`

val asl_comment_location_string_def = Define `
asl_comment_location_string (x:string) p = p`

val asl_comment_location2_def = Define `
asl_comment_location2 (x:label list) p = p`

val asl_comment_location2_THM = store_thm ("asl_comment_location2_THM",
``asl_comment_location2 = asl_comment_location``,
SIMP_TAC std_ss [FUN_EQ_THM, asl_comment_location2_def,
 asl_comment_location_def])

val asl_comment_assert_def = Define `
asl_comment_assert (qP:'e -> 'd set) = asl_prog_skip:('a,'b','c,'d) asl_program`;

val asl_comment_abstraction_def = Define `
asl_comment_abstraction (x:label) p = p`


val comments_thmL = [asl_comment_location_def,
      asl_comment_location2_def,
      asl_comment_location_string_def,
      asl_comment_loop_invariant_def,
      asl_comment_abstraction_def,
      asl_comment_loop_spec_def,
      asl_comment_loop_unroll_def,
      asl_comment_block_spec_def];
val asl_comments_ELIM = save_thm ("asl_comments_ELIM",
LIST_CONJ comments_thmL);

val asl_comments_TF_ELIM = save_thm ("asl_comments_TF_ELIM",
let
   val thmL = map (CONV_RULE (RESORT_FORALL_CONV rev)) comments_thmL;
   val thmLT = map (ISPEC T) thmL
   val thmLF = map (ISPEC F) thmL
in
   LIST_CONJ (append thmLT thmLF)
end);
val _ = export_rewrites ["asl_comments_TF_ELIM"]


(* ------------------------------------ *)
(* Program traces                       *)
(* ------------------------------------ *)

val ASL_PROTO_TRACES_EVAL_PROC_def_term_frag =
`
   (ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_prim_command pc) = {[asl_aa_pc pc]}) /\
   (ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_seq p1 p2) =
      {t1 ++ t2 | t1 IN ASL_PROTO_TRACES_EVAL_PROC n penv p1 /\ t2 IN ASL_PROTO_TRACES_EVAL_PROC n penv p2}) /\

   (ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_parallel p1 p2) =
      BIGUNION {ASL_TRACE_ZIP t1 t2 | t1 IN (ASL_PROTO_TRACES_EVAL_PROC n penv p1) /\ t2 IN (ASL_PROTO_TRACES_EVAL_PROC n penv p2)}) /\

   (ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_lock_declaration l p) =
      IMAGE (\t. ASL_TRACE_REMOVE_LOCKS {l} ([asl_aa_verhoog l]++t++[asl_aa_prolaag l])) ((ASL_PROTO_TRACES_EVAL_PROC n penv p) INTER (ASL_TRACE_IS_LOCK_SYNCHRONISED l))) /\

   (ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_critical_section l p) =
      IMAGE (\t. [asl_aa_prolaag l]++t++[asl_aa_verhoog l]) (ASL_PROTO_TRACES_EVAL_PROC n penv p)) /\

   (ASL_PROTO_TRACES_EVAL_PROC 0 penv (asl_pt_procedure_call name arg) =
      if ~(name IN (FDOM penv)) then {[asl_aa_fail]} else {}) /\

   (ASL_PROTO_TRACES_EVAL_PROC (SUC n) penv (asl_pt_procedure_call name arg) =
    if ~(name IN (FDOM penv)) then {[asl_aa_fail]} else (
    BIGUNION (IMAGE (ASL_PROTO_TRACES_EVAL_PROC n penv) ((penv ' name) arg))))`;



(*
val ASL_PROTO_TRACES_EVAL_PROC_defn = Defn.Hol_defn "ASL_PROTO_TRACES_EVAL_PROC" ASL_PROTO_TRACES_EVAL_PROC_def_term_frag;

Defn.tgoal ASL_PROTO_TRACES_EVAL_PROC_defn
*)



val ASL_PROTO_TRACES_EVAL_PROC_def = tDefine "ASL_PROTO_TRACES_EVAL_PROC"
ASL_PROTO_TRACES_EVAL_PROC_def_term_frag

(Q.EXISTS_TAC `(measure (\n. n))  LEX
     (measure (\(X, p). asl_proto_trace_size (K 0) (K 0) (K 0) (K 0) p))` THEN
CONJ_TAC THENL [
   MATCH_MP_TAC pairTheory.WF_LEX THEN
   REWRITE_TAC[prim_recTheory.WF_measure],

   SIMP_TAC arith_ss [pairTheory.LEX_DEF_THM, prim_recTheory.measure_thm,
      asl_proto_trace_size_def]
]);


val ASL_PROTO_TRACES_EVAL_def = Define `
   ASL_PROTO_TRACES_EVAL penv prog =
   \t. ?n. t IN (ASL_PROTO_TRACES_EVAL_PROC n penv prog)`;


val ASL_PROGRAM_TRACES_PROC_def = Define `
   ASL_PROGRAM_TRACES_PROC n penv prog =
      BIGUNION (IMAGE (ASL_PROTO_TRACES_EVAL_PROC n penv) prog)`;

val ASL_PROGRAM_TRACES_def = Define `
   ASL_PROGRAM_TRACES penv prog =
      BIGUNION (IMAGE (ASL_PROTO_TRACES_EVAL penv) prog)`;


val ASL_PROGRAM_TRACES_PROC_IN_THM2 = store_thm ("ASL_PROGRAM_TRACES_PROC_IN_THM2",
``ASL_PROGRAM_TRACES_PROC n penv prog =
   \t. ?pt. (pt IN prog) /\ (t IN ASL_PROTO_TRACES_EVAL_PROC n penv pt)``,

SIMP_TAC std_ss [ASL_PROGRAM_TRACES_PROC_def, EXTENSION,
   IN_ABS, IN_BIGUNION, IN_IMAGE] THEN
PROVE_TAC[]);

val ASL_PROGRAM_TRACES_IN_THM2 = store_thm ("ASL_PROGRAM_TRACES_IN_THM2",
``ASL_PROGRAM_TRACES penv prog =
   \t. ?pt. (pt IN prog) /\ (t IN ASL_PROTO_TRACES_EVAL penv pt)``,

SIMP_TAC std_ss [ASL_PROGRAM_TRACES_def, EXTENSION,
   IN_ABS, IN_BIGUNION, IN_IMAGE] THEN
PROVE_TAC[]);


val ASL_PROGRAM_TRACES_IN_THM3 = store_thm ("ASL_PROGRAM_TRACES_IN_THM3",
``ASL_PROGRAM_TRACES penv prog =
   \t. ?pt n. (pt IN prog) /\ (t IN ASL_PROTO_TRACES_EVAL_PROC n penv pt)``,

SIMP_TAC std_ss [EXTENSION, ASL_PROGRAM_TRACES_IN_THM2, IN_ABS,
   ASL_PROTO_TRACES_EVAL_def] THEN
METIS_TAC[]);


val ASL_PROGRAM_TRACES_IN_THM4 = store_thm ("ASL_PROGRAM_TRACES_IN_THM4",
``ASL_PROGRAM_TRACES penv prog =
   \t. ?n. (t IN ASL_PROGRAM_TRACES_PROC n penv prog)``,

SIMP_TAC std_ss [ASL_PROGRAM_TRACES_IN_THM3,
   ASL_PROGRAM_TRACES_PROC_IN_THM2, IN_ABS] THEN
METIS_TAC[]);






val ASL_PROTO_TRACES_EVAL_PROC_THM = store_thm ("ASL_PROTO_TRACES_EVAL_PROC_THM",
``
   (ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_prim_command pc) = {[asl_aa_pc pc]}) /\
   (ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_seq p1 p2) =
      {t1 ++ t2 | t1 IN ASL_PROTO_TRACES_EVAL_PROC n penv p1 /\ t2 IN ASL_PROTO_TRACES_EVAL_PROC n penv p2}) /\
   (ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_parallel p1 p2) =
      BIGUNION {ASL_TRACE_ZIP t1 t2 | t1 IN (ASL_PROTO_TRACES_EVAL_PROC n penv p1) /\ t2 IN (ASL_PROTO_TRACES_EVAL_PROC n penv p2)}) /\

   (ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_lock_declaration l p) =
      IMAGE (\t. ASL_TRACE_REMOVE_LOCKS {l} ([asl_aa_verhoog l]++t++[asl_aa_prolaag l])) ((ASL_PROTO_TRACES_EVAL_PROC n penv p) INTER (ASL_TRACE_IS_LOCK_SYNCHRONISED l))) /\

   (ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_critical_section l p) =
      IMAGE (\t. [asl_aa_prolaag l]++t++[asl_aa_verhoog l]) (ASL_PROTO_TRACES_EVAL_PROC n penv p)) /\

   (ASL_PROTO_TRACES_EVAL_PROC 0 penv (asl_pt_procedure_call name arg) =
      if ~(name IN (FDOM penv)) then {[asl_aa_fail]} else {}) /\

   (ASL_PROTO_TRACES_EVAL_PROC (SUC n) penv (asl_pt_procedure_call name arg) =
    if ~(name IN (FDOM penv)) then {[asl_aa_fail]} else (ASL_PROGRAM_TRACES_PROC n penv ((penv ' name) arg)))``,

SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_def] THEN
Cases_on `n` THEN
SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_def,
ASL_PROGRAM_TRACES_PROC_def] THEN
METIS_TAC[]);



val ASL_PROTO_TRACES_EVAL_PROC_IN_THM = store_thm ("ASL_PROTO_TRACES_EVAL_PROC_IN_THM",
``
   ((t IN (ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_prim_command pc))) = (t = [asl_aa_pc pc])) /\
   (t IN (ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_seq p1 p2)) =
      ?t1 t2. (t = t1 ++ t2) /\ t1 IN ASL_PROTO_TRACES_EVAL_PROC n penv p1 /\ t2 IN ASL_PROTO_TRACES_EVAL_PROC n penv p2) /\
   (t IN (ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_parallel p1 p2)) =
      ?t1 t2. (t IN ASL_TRACE_ZIP t1 t2) /\ (t1 IN (ASL_PROTO_TRACES_EVAL_PROC n penv p1)) /\ (t2 IN (ASL_PROTO_TRACES_EVAL_PROC n penv p2))) /\

   (t IN (ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_lock_declaration l p)) =
      ?t'. (t = ASL_TRACE_REMOVE_LOCKS {l} ([asl_aa_verhoog l]++t'++[asl_aa_prolaag l])) /\
        t' IN (ASL_PROTO_TRACES_EVAL_PROC n penv p) /\ ASL_TRACE_IS_LOCK_SYNCHRONISED l t') /\

   (t IN (ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_critical_section l p)) =
   ?t'. (t = [asl_aa_prolaag l]++t'++[asl_aa_verhoog l]) /\
        (t' IN ASL_PROTO_TRACES_EVAL_PROC n penv p)) /\

   (t IN (ASL_PROTO_TRACES_EVAL_PROC 0 penv (asl_pt_procedure_call name arg)) =
      (~(name IN (FDOM penv)) /\ (t= [asl_aa_fail]))) /\

   (t IN (ASL_PROTO_TRACES_EVAL_PROC (SUC n) penv (asl_pt_procedure_call name arg)) =
   (if ~(name IN (FDOM penv)) then (t= [asl_aa_fail]) else
    (t IN (ASL_PROGRAM_TRACES_PROC n penv ((penv ' name) arg)))))``,


SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_THM, IN_SING,
   GSPECIFICATION, PAIR_EXISTS_THM, IN_UNION,
   IN_BIGUNION, IN_IMAGE, IN_INTER, NOT_IN_EMPTY] THEN
REPEAT STRIP_TAC THENL [
   METIS_TAC[],
   SIMP_TAC std_ss [IN_DEF],
   SIMP_TAC std_ss [COND_RAND, COND_RATOR, IN_SING, NOT_IN_EMPTY],
   SIMP_TAC std_ss [COND_RAND, COND_RATOR, IN_SING]
]);



val ASL_PROTO_TRACES_EVAL_PROC_SUBSET_SUC = store_thm ("ASL_PROTO_TRACES_EVAL_PROC_SUBSET_SUC",
``!n penv p. (ASL_PROTO_TRACES_EVAL_PROC n penv p) SUBSET
          (ASL_PROTO_TRACES_EVAL_PROC (SUC n) penv p)``,

REWRITE_TAC [SUBSET_DEF] THEN
completeInduct_on `n` THEN
Induct_on `p` THEN (
   ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM]
) THENL [
   METIS_TAC[],

   REPEAT GEN_TAC THEN
   Cases_on `n` THEN (
      SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM]
   ) THEN
   Cases_on `n' IN FDOM penv` THEN ASM_REWRITE_TAC[] THEN
   `n'' < SUC n''` by DECIDE_TAC THEN
   SIMP_TAC std_ss [ASL_PROGRAM_TRACES_PROC_IN_THM2,
      IN_ABS] THEN
   METIS_TAC[],

   METIS_TAC[],
   METIS_TAC[],
   METIS_TAC[]
]);




val ASL_PROTO_TRACES_EVAL_PROC_SUBSET = store_thm ("ASL_PROTO_TRACES_EVAL_PROC_SUBSET",
``!n m penv p.
   (n <= m) ==>
(ASL_PROTO_TRACES_EVAL_PROC n penv p) SUBSET
          (ASL_PROTO_TRACES_EVAL_PROC m penv p)``,

REPEAT STRIP_TAC THEN
`?n':num. m = (n + n')` by METIS_TAC[LESS_EQUAL_ADD] THEN
FULL_SIMP_TAC std_ss [] THEN
REPEAT (POP_ASSUM (K ALL_TAC)) THEN
Induct_on `n'` THENL [
   SIMP_TAC std_ss [SUBSET_REFL],

   SIMP_TAC std_ss [ADD_CLAUSES] THEN
   METIS_TAC[SUBSET_TRANS, ASL_PROTO_TRACES_EVAL_PROC_SUBSET_SUC]
]);


val ASL_PROGRAM_TRACES_PROC_SUBSET = store_thm ("ASL_PROGRAM_TRACES_PROC_SUBSET",

``!n m penv p.
   (n <= m) ==>
(ASL_PROGRAM_TRACES_PROC n penv p) SUBSET
(ASL_PROGRAM_TRACES_PROC m penv p)``,

SIMP_TAC std_ss [ASL_PROGRAM_TRACES_PROC_IN_THM2, SUBSET_DEF, IN_ABS] THEN
METIS_TAC[ASL_PROTO_TRACES_EVAL_PROC_SUBSET, SUBSET_DEF]);



val ASL_PROTO_TRACES_EVAL_IN_THM = store_thm ("ASL_PROTO_TRACES_EVAL_IN_THM",
``
   ((t IN (ASL_PROTO_TRACES_EVAL penv (asl_pt_prim_command pc))) = (t = [asl_aa_pc pc])) /\
   (t IN (ASL_PROTO_TRACES_EVAL penv (asl_pt_seq p1 p2)) =
      ?t1 t2. (t = t1 ++ t2) /\ t1 IN ASL_PROTO_TRACES_EVAL penv p1 /\ t2 IN ASL_PROTO_TRACES_EVAL penv p2) /\

   (t IN (ASL_PROTO_TRACES_EVAL penv (asl_pt_parallel p1 p2)) =
      ?t1 t2. (t IN ASL_TRACE_ZIP t1 t2) /\ (t1 IN (ASL_PROTO_TRACES_EVAL penv p1)) /\ (t2 IN (ASL_PROTO_TRACES_EVAL penv p2))) /\

   (t IN (ASL_PROTO_TRACES_EVAL penv (asl_pt_lock_declaration l p)) =
      ?t'. (t = ASL_TRACE_REMOVE_LOCKS {l} ([asl_aa_verhoog l]++t'++[asl_aa_prolaag l])) /\
        t' IN (ASL_PROTO_TRACES_EVAL penv p) /\ ASL_TRACE_IS_LOCK_SYNCHRONISED l t') /\

   (t IN (ASL_PROTO_TRACES_EVAL penv (asl_pt_critical_section l p)) =
   ?t'. (t = [asl_aa_prolaag l]++t'++[asl_aa_verhoog l]) /\
        (t' IN ASL_PROTO_TRACES_EVAL penv p)) /\

   (t IN (ASL_PROTO_TRACES_EVAL penv (asl_pt_procedure_call name arg)) =
    if (~(name IN FDOM penv)) then (t = [asl_aa_fail]) else
    (t IN ASL_PROGRAM_TRACES penv ((penv ' name) arg)))``,



SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_def,
   IN_ABS, ASL_PROTO_TRACES_EVAL_PROC_IN_THM] THEN
REPEAT STRIP_TAC THENL [
   EQ_TAC THEN1 METIS_TAC[] THEN
   STRIP_TAC THEN
   Q.EXISTS_TAC `MAX n n'` THEN
   Q.EXISTS_TAC `t1` THEN
   Q.EXISTS_TAC `t2` THEN
   `(n <= MAX n n') /\ (n' <= MAX n n')` by SIMP_TAC std_ss [] THEN
   METIS_TAC[ASL_PROTO_TRACES_EVAL_PROC_SUBSET, SUBSET_DEF],


   EQ_TAC THEN1 METIS_TAC[] THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `MAX n n'` THEN
   Q.EXISTS_TAC `t1` THEN
   Q.EXISTS_TAC `t2` THEN
   ASM_SIMP_TAC std_ss [] THEN
   `(n <= MAX n n') /\ (n' <= MAX n n')` by SIMP_TAC std_ss [] THEN
   METIS_TAC[ASL_PROTO_TRACES_EVAL_PROC_SUBSET, SUBSET_DEF],


   METIS_TAC[],
   METIS_TAC[],


   SIMP_TAC std_ss [ASL_PROGRAM_TRACES_IN_THM2, IN_ABS,
      ASL_PROTO_TRACES_EVAL_def,
      GSYM RIGHT_EXISTS_AND_THM] THEN
   Cases_on `~(name IN FDOM penv)` THEN ASM_REWRITE_TAC[] THEN1 (
      EQ_TAC THENL [
         SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN
         GEN_TAC THEN
         Cases_on `n` THEN (
            ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM]
         ),

         STRIP_TAC THEN
         Q.EXISTS_TAC `0` THEN
         ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM]
      ]
   ) THEN
   HO_MATCH_MP_TAC (prove (``((~(P 0)) /\ (!n. P (SUC n) = ?x. Q x n)) ==> ((?n. P n) = (?x n. Q x n))``, REPEAT STRIP_TAC THEN EQ_TAC THENL [
      STRIP_TAC THEN Cases_on `n` THEN METIS_TAC[],
      METIS_TAC[]
   ])) THEN
   ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_THM,
      ASL_PROGRAM_TRACES_PROC_IN_THM2, IN_ABS, NOT_IN_EMPTY]
]);



val ASL_PROTO_TRACES_EVAL_THM = save_thm ("ASL_PROTO_TRACES_EVAL_THM",
let
   val thm1 = Q.GEN `t` ASL_PROTO_TRACES_EVAL_IN_THM;
   val thm2 = prove (``(\t. if C then P t else Q t) = (if C then (\t. P t) else (\t. Q t))``, METIS_TAC[]);
   val thm3 = prove (``(!t. ~(t IN X)) = (X = {})``, SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY]);
   val thm4 = SIMP_RULE std_ss [FORALL_AND_THM, IN_ABS2, IN_ABS3, IN_ABS_SING,
      thm2, thm3] thm1;
in
   thm4
end);


val ASL_PROGRAM_TRACES_PROC_IN_THM = store_thm ("ASL_PROGRAM_TRACES_PROC_IN_THM",
``
   (~(t IN (ASL_PROGRAM_TRACES_PROC n penv {}))) /\
   ((t IN (ASL_PROGRAM_TRACES_PROC n penv (asl_prog_prim_command pc))) = (t = [asl_aa_pc pc])) /\
   (t IN (ASL_PROGRAM_TRACES_PROC n penv (asl_prog_seq p1 p2)) =
      ?t1 t2. (t = t1 ++ t2) /\ t1 IN (ASL_PROGRAM_TRACES_PROC n penv p1) /\ t2 IN ([asl_aa_diverge] INSERT ASL_PROGRAM_TRACES_PROC n penv p2)) /\

   (t IN (ASL_PROGRAM_TRACES_PROC n penv (asl_prog_choice p1 p2)) =
      (t IN ((ASL_PROGRAM_TRACES_PROC n penv p1) UNION (ASL_PROGRAM_TRACES_PROC n penv p2)))) /\

   (t IN (ASL_PROGRAM_TRACES_PROC n penv (asl_prog_kleene_star p)) =
      t IN (IMAGE (\t. t ++ [asl_aa_skip]) (LIST_SET_STAR (ASL_PROGRAM_TRACES_PROC n penv p)))) /\

   (t IN (ASL_PROGRAM_TRACES_PROC n penv (asl_prog_parallel p1 p2)) =
      ?t1 t2. (t IN ASL_TRACE_ZIP t1 t2) /\ (t1 IN (ASL_PROGRAM_TRACES_PROC n penv p1)) /\ (t2 IN (ASL_PROGRAM_TRACES_PROC n penv p2))) /\

   (t IN (ASL_PROGRAM_TRACES_PROC n penv (asl_prog_lock_declaration l p)) =
      ?t'. (t = ASL_TRACE_REMOVE_LOCKS {l} ([asl_aa_verhoog l]++t'++[asl_aa_prolaag l])) /\
   t' IN (ASL_PROGRAM_TRACES_PROC n penv p) /\ ASL_TRACE_IS_LOCK_SYNCHRONISED l t') /\

   (t IN (ASL_PROGRAM_TRACES_PROC n penv (asl_prog_critical_section l p)) =
   ?t'. (t = [asl_aa_prolaag l]++t'++[asl_aa_verhoog l]) /\
   (t' IN ASL_PROGRAM_TRACES_PROC n penv p)) /\

   (t IN (ASL_PROGRAM_TRACES_PROC 0 penv (asl_prog_procedure_call name arg)) =
    (~(name IN FDOM penv)) /\ (t = [asl_aa_fail])) /\

   (t IN (ASL_PROGRAM_TRACES_PROC (SUC n) penv (asl_prog_procedure_call name arg)) =
    if (~(name IN FDOM penv)) then (t = [asl_aa_fail]) else
    t IN ASL_PROGRAM_TRACES_PROC n penv ((penv ' name) arg))``,

SIMP_TAC std_ss [ASL_PROGRAM_TRACES_PROC_def, IN_BIGUNION, IN_IMAGE,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THENL [
   SIMP_TAC std_ss [NOT_IN_EMPTY],


   SIMP_TAC std_ss [asl_prog_prim_command_def, IN_SING,
      ASL_PROTO_TRACES_EVAL_PROC_IN_THM],

   SIMP_TAC std_ss [asl_prog_seq_def, IN_ABS,
      GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      ASL_PROTO_TRACES_EVAL_PROC_IN_THM,
      IN_INSERT] THEN
   SIMP_TAC list_ss [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
          EXISTS_OR_THM, ASL_PROTO_TRACES_EVAL_PROC_IN_THM,
          asl_pt_diverge_def, GSYM asl_aa_diverge_def,
          IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
   METIS_TAC[],


   SIMP_TAC std_ss [IN_UNION, IN_BIGUNION,
      IN_IMAGE, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      asl_prog_choice_def] THEN
   METIS_TAC[],


   SIMP_TAC std_ss [asl_prog_kleene_star_def, IN_ABS,
      GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      asl_prog_repeat_num_def, LIST_SET_STAR_def] THEN
   HO_MATCH_MP_TAC (prove (``(!n. ((?x. P x n) = (?t'. Q t' n))) ==>
((?x n. P x n) = (?t' n. Q t' n))``, METIS_TAC[])) THEN
   Q.SPEC_TAC (`t`, `t`) THEN
   Induct_on `n'` THENL [
      SIMP_TAC list_ss [asl_prog_repeat_num_def, LIST_NUM_SET_STAR_def,
      IN_SING, asl_prog_skip_def, asl_prog_prim_command_def,
    ASL_PROTO_TRACES_EVAL_PROC_IN_THM, asl_aa_skip_def],

      SIMP_TAC list_ss [asl_prog_repeat_num_def, LIST_NUM_SET_STAR_def,
    IN_ABS, GSPECIFICATION, GSYM LEFT_EXISTS_AND_THM,
    GSYM RIGHT_EXISTS_AND_THM, PAIR_EXISTS_THM, IN_BIGUNION,
    IN_IMAGE] THEN
      SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM, GSYM LEFT_EXISTS_AND_THM,
    GSYM RIGHT_EXISTS_AND_THM] THEN
      GEN_TAC THEN
      HO_MATCH_MP_TAC (prove (``
    (!t1 pt1. ((?pt2 t2. P pt1 pt2 t1 t2) = (?x2. Q t1 x2 pt1))) ==>
    ((?pt1 pt2 t1 t2. P pt1 pt2 t1 t2) = (?x1 x2 x. Q x1 x2 x))``, METIS_TAC[])) THEN
      REPEAT GEN_TAC THEN
      Cases_on `x IN p` THEN ASM_REWRITE_TAC[] THEN
      Cases_on `x1 IN ASL_PROTO_TRACES_EVAL_PROC n penv x` THEN ASM_REWRITE_TAC[] THEN
      Tactical.REVERSE (Cases_on `?t2. t = x1 ++ t2`) THEN1 (
    FULL_SIMP_TAC std_ss [] THEN
    METIS_TAC[APPEND_ASSOC]
      ) THEN
      FULL_SIMP_TAC std_ss [APPEND_11, GSYM APPEND_ASSOC]
   ],


   SIMP_TAC std_ss [asl_prog_parallel_def, IN_ABS,
      GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      ASL_PROTO_TRACES_EVAL_PROC_IN_THM] THEN
   METIS_TAC[],


   SIMP_TAC std_ss [asl_prog_lock_declaration_def, IN_IMAGE,
      GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      ASL_PROTO_TRACES_EVAL_PROC_IN_THM] THEN
   METIS_TAC[],


   SIMP_TAC std_ss [asl_prog_critical_section_def,
      IN_IMAGE, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      ASL_PROTO_TRACES_EVAL_PROC_IN_THM] THEN
   METIS_TAC[],


   SIMP_TAC std_ss [asl_prog_procedure_call_def, IN_SING,
      IN_IMAGE, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      ASL_PROTO_TRACES_EVAL_PROC_IN_THM, IN_BIGUNION],

  SIMP_TAC std_ss [asl_prog_procedure_call_def, IN_SING,
      IN_IMAGE, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      ASL_PROTO_TRACES_EVAL_PROC_IN_THM, IN_BIGUNION,
      ASL_PROGRAM_TRACES_PROC_def]
]);




val ASL_PROGRAM_TRACES_PROC_THM = save_thm ("ASL_PROGRAM_TRACES_PROC_THM",
let
   val thm1 = Q.GEN `t` ASL_PROGRAM_TRACES_PROC_IN_THM;
   val thm2 = prove (``(\t. if C then P t else Q t) = (if C then (\t. P t) else (\t. Q t))``, METIS_TAC[]);
   val thm3 = prove (``(!t. ~(t IN X)) = (X = {})``, SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY]);
   val thm4 = SIMP_RULE std_ss [FORALL_AND_THM, IN_ABS2, IN_ABS3, IN_ABS_SING,
      thm2, thm3] thm1;
in
   thm4
end);


val ASL_PROGRAM_TRACES_PROC_SING_THM = store_thm ("ASL_PROGRAM_TRACES_PROC_SING_THM",
   ``ASL_PROGRAM_TRACES_PROC n penv {pt} =
      ASL_PROTO_TRACES_EVAL_PROC n penv pt``,

ONCE_REWRITE_TAC[EXTENSION] THEN
SIMP_TAC std_ss [ASL_PROGRAM_TRACES_PROC_def,
   IN_BIGUNION, IN_IMAGE, IN_SING]);


val ASL_PROGRAM_TRACES___PROC_THM = store_thm ("ASL_PROGRAM_TRACES___PROC_THM",
``ASL_PROGRAM_TRACES penv prog =
   \t. ?n. t IN ASL_PROGRAM_TRACES_PROC n penv prog``,

SIMP_TAC std_ss [ASL_PROGRAM_TRACES_def,
   ASL_PROGRAM_TRACES_PROC_def] THEN
ONCE_REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   IN_UNIV, ASL_PROTO_TRACES_EVAL_def, IN_ABS] THEN
METIS_TAC[]);




val ASL_PROGRAM_TRACES_IN_THM = store_thm ("ASL_PROGRAM_TRACES_IN_THM",
``
   (~(t IN (ASL_PROGRAM_TRACES penv {}))) /\
   ((t IN (ASL_PROGRAM_TRACES penv (asl_prog_prim_command pc))) = (t = [asl_aa_pc pc])) /\
   (t IN (ASL_PROGRAM_TRACES penv (asl_prog_seq p1 p2)) =
      ?t1 t2. (t = t1 ++ t2) /\ t1 IN ASL_PROGRAM_TRACES penv p1 /\ t2 IN [asl_aa_diverge] INSERT ASL_PROGRAM_TRACES penv p2) /\

   (t IN (ASL_PROGRAM_TRACES penv (asl_prog_choice p1 p2)) =
      (t IN ((ASL_PROGRAM_TRACES penv p1) UNION (ASL_PROGRAM_TRACES penv p2)))) /\

   (t IN (ASL_PROGRAM_TRACES penv (asl_prog_kleene_star p)) =
      t IN (IMAGE (\t. t ++ [asl_aa_skip]) (LIST_SET_STAR (ASL_PROGRAM_TRACES penv p)))) /\

   (t IN (ASL_PROGRAM_TRACES penv (asl_prog_parallel p1 p2)) =
      ?t1 t2. (t IN ASL_TRACE_ZIP t1 t2) /\ (t1 IN (ASL_PROGRAM_TRACES penv p1)) /\ (t2 IN (ASL_PROGRAM_TRACES penv p2))) /\

   (t IN (ASL_PROGRAM_TRACES penv (asl_prog_lock_declaration l p)) =
      ?t'. (t = ASL_TRACE_REMOVE_LOCKS {l} ([asl_aa_verhoog l]++t'++[asl_aa_prolaag l])) /\
   t' IN (ASL_PROGRAM_TRACES penv p) /\ ASL_TRACE_IS_LOCK_SYNCHRONISED l t') /\

   (t IN (ASL_PROGRAM_TRACES penv (asl_prog_critical_section l p)) =
   ?t'. (t = [asl_aa_prolaag l]++t'++[asl_aa_verhoog l]) /\
   (t' IN ASL_PROGRAM_TRACES penv p)) /\

   (t IN (ASL_PROGRAM_TRACES penv (asl_prog_procedure_call name arg)) =
    if (~(name IN FDOM penv)) then (t = [asl_aa_fail]) else
    t IN ASL_PROGRAM_TRACES penv ((penv ' name) arg))``,


REPEAT CONJ_TAC THENL [
   SIMP_TAC std_ss [ASL_PROGRAM_TRACES___PROC_THM,
      ASL_PROGRAM_TRACES_PROC_IN_THM, IN_ABS],

   SIMP_TAC std_ss [ASL_PROGRAM_TRACES___PROC_THM,
      ASL_PROGRAM_TRACES_PROC_IN_THM, IN_ABS],

   SIMP_TAC std_ss [ASL_PROGRAM_TRACES_IN_THM2, asl_prog_seq_def,
      ASL_PROTO_TRACES_EVAL_IN_THM, IN_ABS, GSYM LEFT_EXISTS_AND_THM,
      GSYM RIGHT_EXISTS_AND_THM, IN_INSERT,
      LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR,
      EXISTS_OR_THM,
      ASL_PROTO_TRACES_EVAL_IN_THM, asl_pt_diverge_def,
      GSYM asl_aa_diverge_def] THEN
   METIS_TAC[],


   SIMP_TAC std_ss [ASL_PROGRAM_TRACES_def, asl_prog_choice_def,
      IMAGE_UNION, BIGUNION_UNION],


   SIMP_TAC std_ss [ASL_PROGRAM_TRACES_IN_THM2, asl_prog_kleene_star_def,
      IN_ABS, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      IN_IMAGE, LIST_SET_STAR_def] THEN

   HO_MATCH_MP_TAC (prove (``(!n. ((?x. P x n) = (?t'. Q t' n))) ==>
      ((?x n. P x n) = (?t' n. Q t' n))``, METIS_TAC[])) THEN
   Q.SPEC_TAC (`t`, `t`) THEN
   Induct_on `n` THENL [
      SIMP_TAC list_ss [asl_prog_repeat_num_def, LIST_NUM_SET_STAR_def,
         IN_SING, asl_prog_skip_def, asl_prog_prim_command_def,
         ASL_PROTO_TRACES_EVAL_IN_THM, asl_aa_skip_def],

      SIMP_TAC list_ss [asl_prog_repeat_num_def, LIST_NUM_SET_STAR_def,
         IN_ABS, GSPECIFICATION, GSYM LEFT_EXISTS_AND_THM,
         GSYM RIGHT_EXISTS_AND_THM, PAIR_EXISTS_THM,
         ASL_PROTO_TRACES_EVAL_IN_THM,
         IN_IMAGE] THEN
      METIS_TAC[APPEND_ASSOC]
   ],


   SIMP_TAC std_ss [ASL_PROGRAM_TRACES_IN_THM2,
      asl_prog_parallel_def, IN_ABS,
      GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      ASL_PROTO_TRACES_EVAL_IN_THM] THEN
   METIS_TAC[],


   SIMP_TAC std_ss [ASL_PROGRAM_TRACES___PROC_THM,
      ASL_PROGRAM_TRACES_PROC_IN_THM, IN_ABS] THEN
   METIS_TAC[],

   SIMP_TAC std_ss [ASL_PROGRAM_TRACES___PROC_THM,
      ASL_PROGRAM_TRACES_PROC_IN_THM, IN_ABS] THEN
   METIS_TAC[],

   SIMP_TAC std_ss [ASL_PROGRAM_TRACES_IN_THM2,
      asl_prog_procedure_call_def, IN_ABS,
      GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      ASL_PROTO_TRACES_EVAL_IN_THM, IN_SING]
]);



val ASL_PROGRAM_TRACES_THM = save_thm ("ASL_PROGRAM_TRACES_THM",
let
   val thm1 = Q.GEN `t` ASL_PROGRAM_TRACES_IN_THM;
   val thm2 = prove (``(\t. if C then P t else Q t) = (if C then (\t. P t) else (\t. Q t))``, METIS_TAC[]);
   val thm3 = prove (``(!t. ~(t IN X)) = (X = {})``, SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY]);
   val thm4 = SIMP_RULE std_ss [FORALL_AND_THM, IN_ABS2, IN_ABS3, IN_ABS_SING,
      thm2, thm3] thm1;
in
   thm4
end);



val ASL_PROGRAM_TRACES___prog_ndet = store_thm ("ASL_PROGRAM_TRACES___prog_ndet",
``!penv pset.
ASL_PROGRAM_TRACES penv (asl_prog_ndet pset) =
BIGUNION (IMAGE (\prog. ASL_PROGRAM_TRACES penv prog) pset)``,


REWRITE_TAC [EXTENSION] THEN
SIMP_TAC std_ss [ASL_PROGRAM_TRACES_def, IN_BIGUNION, IN_IMAGE,
       asl_prog_ndet_def, GSYM RIGHT_EXISTS_AND_THM,
       GSYM LEFT_EXISTS_AND_THM] THEN
PROVE_TAC[]);



val ASL_PROGRAM_TRACES___EQ_EMPTY = store_thm (
"ASL_PROGRAM_TRACES___EQ_EMPTY",
``!penv prog.
(ASL_PROGRAM_TRACES penv prog = EMPTY) =
(!pt. pt IN prog ==> (ASL_PROTO_TRACES_EVAL penv pt = EMPTY))``,


SIMP_TAC std_ss [ASL_PROGRAM_TRACES_def, BIGUNION_EQ_EMPTY, IMAGE_EQ_EMPTY] THEN
REPEAT GEN_TAC THEN
Cases_on `prog = EMPTY` THEN (
   ASM_SIMP_TAC std_ss [NOT_IN_EMPTY]
) THEN
REWRITE_TAC [Once EXTENSION] THEN
SIMP_TAC std_ss [IN_IMAGE, IN_SING, NOT_IN_EMPTY,
   EQ_IMP_THM, GSYM LEFT_FORALL_IMP_THM, FORALL_AND_THM] THEN
REPEAT STRIP_TAC THEN
`?pt. pt IN prog`  by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY] THEN
   METIS_TAC[]
) THEN
Q.EXISTS_TAC `pt` THEN
ASM_SIMP_TAC std_ss []);




(******************************************************************************)
(* Synchronising / lock balancing                                             *)
(******************************************************************************)

val ASL_TRACE_REMOVE_CHECKS_def = Define `
   ASL_TRACE_REMOVE_CHECKS = FILTER (\x. ~ (ASL_IS_CHECK_ATOMIC_ACTION x))`

val ASL_TRACE_REMOVE_CHECKS_APPEND = store_thm ("ASL_TRACE_REMOVE_CHECKS_APPEND",
``      !t1 t2. ASL_TRACE_REMOVE_CHECKS (t1 ++ t2) =
         ASL_TRACE_REMOVE_CHECKS t1 ++ ASL_TRACE_REMOVE_CHECKS t2``,
SIMP_TAC std_ss [ASL_TRACE_REMOVE_CHECKS_def, FILTER_APPEND]);

val ASL_LOCK_INTRO_LOCAL_ACTION_ORDER = store_thm("ASL_LOCK_INTRO_LOCAL_ACTION_ORDER",
``!f la P. (IS_SEPARATION_COMBINATOR f /\ ASL_IS_LOCAL_ACTION f la /\
       ASL_IS_PRECISE f P) ==>

fasl_action_order
la (asla_big_seq [asla_annihilation f P; la; asla_materialisation f P])``,

SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF] THEN
REPEAT STRIP_TAC THEN
Cases_on `asla_big_seq [asla_annihilation f P; la; asla_materialisation f P] s` THEN1 (
   SIMP_TAC std_ss [fasl_order_THM]
) THEN
FULL_SIMP_TAC std_ss [asla_big_seq_def, asla_seq_skip] THEN
FULL_SIMP_TAC std_ss [SOME___asla_seq, IS_SOME___asla_seq] THEN

SIMP_TAC std_ss [fasl_order_THM] THEN
Q.PAT_ASSUM `IS_SEPARATION_COMBINATOR f` ASSUME_TAC THEN
Q.PAT_ASSUM `ASL_IS_PRECISE f P` ASSUME_TAC THEN
FULL_SIMP_TAC std_ss [asla_annihilation_PRECISE_THM, COND_RAND, COND_RATOR,
   asla_materialisation_THM, LET_THM] THEN

Q.PAT_ASSUM `x = X` (K ALL_TAC) THEN
Q.PAT_ASSUM `X = s1` (ASSUME_TAC o GSYM) THEN
FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY, IN_ABS, GSYM LEFT_FORALL_IMP_THM] THEN

`?lax. la x = SOME lax` by METIS_TAC[] THEN

`?las. la s = SOME las` by ALL_TAC THEN1 (
   REWRITE_TAC [GSYM IS_SOME_EXISTS] THEN
   FULL_SIMP_TAC std_ss [LOCALITY_CHARACTERISATION, TRANS_FUNC_SAFETY_MONOTONICITY_REWRITE] THEN
   Q.PAT_ASSUM `!s1 s2 s3. X s1 s2 ==> IS_SOME (la s3)` MATCH_MP_TAC THEN
   Q.EXISTS_TAC `x` THEN
   Q.EXISTS_TAC `s1'` THEN
   ASM_SIMP_TAC std_ss [IS_SOME_EXISTS] THEN
   METIS_TAC[]
) THEN


ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE, GSYM LEFT_EXISTS_AND_THM,
   GSYM RIGHT_EXISTS_AND_THM, IN_ABS] THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `x` THEN
Q.EXISTS_TAC `s1'` THEN
ASM_SIMP_TAC std_ss [asla_seq_def, SUP_fasl_order_def, IN_IMAGE, asla_materialisation_THM] THEN

ASM_SIMP_TAC std_ss [IN_BIGUNION, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   IN_IMAGE, asla_materialisation_THM, asl_star_def, IN_ABS, IN_SING] THEN

FULL_SIMP_TAC std_ss [LOCALITY_CHARACTERISATION] THEN
Q.PAT_ASSUM `TRANS_FUNC_FRAME_PROPERTY f la` (MP_TAC o Q.SPECL [`x`, `s1'`, `s`, `lax`, `las`, `x'`] o REWRITE_RULE [TRANS_FUNC_FRAME_PROPERTY_def]) THEN

ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[IS_SEPARATION_COMBINATOR_def, COMM_DEF]);




val ASL_TRACE_APPEND_ACTION_ORDER = store_thm ("ASL_TRACE_APPEND_ACTION_ORDER",
``!xenv t0 t1 t0' t1'.
(fasl_action_order (ASL_TRACE_SEM xenv t0) (ASL_TRACE_SEM xenv t0') /\
fasl_action_order (ASL_TRACE_SEM xenv t1) (ASL_TRACE_SEM xenv t1')) ==>

fasl_action_order (ASL_TRACE_SEM xenv (t0 ++ t1))
           (ASL_TRACE_SEM xenv (t0' ++ t1'))``,

SIMP_TAC std_ss [ASL_TRACE_SEM_def, MAP_APPEND,
   asla_big_seq_APPEND] THEN
SIMP_TAC std_ss [asla_big_seq_def] THEN
METIS_TAC[asla_seq___ACTION_ORDER]);





val ASL_TRACE_IS_LOCK_BALANCED_LOCK_def = Define `
   ASL_TRACE_IS_LOCK_BALANCED_LOCK l t =
      (LIST_ELEM_COUNT (asl_aa_prolaag l) t =
       LIST_ELEM_COUNT (asl_aa_verhoog l) t)`

val ASL_TRACE_IS_LOCK_BALANCED_def = Define `
   ASL_TRACE_IS_LOCK_BALANCED t =
      !l. ASL_TRACE_IS_LOCK_BALANCED_LOCK l t`


val ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_def = Define `
   (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n [] = (n = 0)) /\

   (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n ((asl_aa_prolaag l')::t) =
      if (l = l') then
         ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l (SUC n) t
      else
         ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n t
   ) /\

   (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l 0 ((asl_aa_verhoog l')::t) =
      ~(l = l') /\ ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l 0 t) /\

   (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l (SUC n) ((asl_aa_verhoog l')::t) =
      if (l = l') then
         ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n t
      else
         ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l (SUC n) t
   ) /\

   (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n (_::t) =
         ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n t)
   `;



val ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM =
   store_thm ("ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM",

``      (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n [] = (n = 0)) /\
   ((~ASL_IS_SING_LOCK_ATOMIC_ACTION l aa) ==>
      (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n (aa::t) =
      ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n t)) /\

   (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n ((asl_aa_prolaag l)::t) =
      ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l (SUC n) t) /\

   ((ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n ((asl_aa_verhoog l)::t)) =
   (~(n = 0) /\ ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l (PRE n) t))``,

Cases_on `n` THEN
SIMP_TAC arith_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_def] THEN
Cases_on `aa` THEN
SIMP_TAC std_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_def,
   ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE]);



val ASL_TRACE_IS_STRONG_LOCK_BALANCED_def = Define `
   ASL_TRACE_IS_STRONG_LOCK_BALANCED t =
      !l. ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l 0 t`



val ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___COUNT =
   store_thm ("ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___COUNT",

``!n l t. ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n t ==>
       (LIST_ELEM_COUNT (asl_aa_verhoog l) t =
   (LIST_ELEM_COUNT (asl_aa_prolaag l) t) + n)``,

Induct_on `t` THENL [
   SIMP_TAC std_ss [LIST_ELEM_COUNT_THM,
      ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM],

   REPEAT GEN_TAC THEN
   Cases_on `ASL_IS_SING_LOCK_ATOMIC_ACTION l h` THENL [
      FULL_SIMP_TAC std_ss [ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE2,
         LIST_ELEM_COUNT_THM, asl_atomic_action_distinct,
         ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM] THENL [

         REPEAT STRIP_TAC THEN
         RES_TAC THEN
         ASM_SIMP_TAC std_ss [ADD_CLAUSES],


         Cases_on `n` THEN SIMP_TAC arith_ss [] THEN
         REPEAT STRIP_TAC THEN
         RES_TAC THEN
         ASM_SIMP_TAC arith_ss []
      ],

      FULL_SIMP_TAC std_ss [LIST_ELEM_COUNT_THM,
         ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE2,
         ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM]
   ]
]);



val ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___STRONG =
   store_thm ("ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___STRONG",

``!l t. ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l 0 t ==>
      ASL_TRACE_IS_LOCK_BALANCED_LOCK l t``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___COUNT THEN
FULL_SIMP_TAC std_ss [ASL_TRACE_IS_LOCK_BALANCED_LOCK_def]);



val ASL_TRACE_IS_STRONG_LOCK_BALANCED___STRONG =
   store_thm ("ASL_TRACE_IS_STRONG_LOCK_BALANCED___STRONG",

``!t. ASL_TRACE_IS_STRONG_LOCK_BALANCED t ==>
      ASL_TRACE_IS_LOCK_BALANCED t``,

REWRITE_TAC [ASL_TRACE_IS_STRONG_LOCK_BALANCED_def,
   ASL_TRACE_IS_LOCK_BALANCED_def] THEN
PROVE_TAC[ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___STRONG]);




val ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_11 = store_thm ("ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_11",
``!l m1 m2 t.
   ((ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l m1 t) /\
   (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l m2 t)) ==>
   (m1 = m2)``,

Induct_on `t` THENL [
   SIMP_TAC std_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM],

   REPEAT GEN_TAC THEN
   Cases_on `~ASL_IS_SING_LOCK_ATOMIC_ACTION l h` THEN1 (
      ASM_SIMP_TAC std_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM] THEN
      METIS_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE2,
      ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM] THENL [
      REPEAT STRIP_TAC THEN
      `SUC m1 = SUC m2` by RES_TAC THEN
      FULL_SIMP_TAC std_ss [],


      Cases_on `m1` THEN Cases_on `m2` THEN SIMP_TAC arith_ss [] THEN
      METIS_TAC[]
   ]
]);



val ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___APPEND =
   store_thm ("ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___APPEND",

``!l n m t1 t2.
    ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l m t1 ==>
    (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n (t1++t2) =
     (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l (n-m) t2 /\ (m <= n)))``,

Induct_on `t1` THEN1 (
   SIMP_TAC list_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM]
) THEN
REPEAT GEN_TAC THEN
Cases_on `~(ASL_IS_SING_LOCK_ATOMIC_ACTION l h)` THEN1 (
   ASM_SIMP_TAC list_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM]
) THEN
FULL_SIMP_TAC std_ss [ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE2] THENL [
   ASM_SIMP_TAC list_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM] THEN
   `((SUC n - SUC m) = (n - m)) /\
     ((SUC m <= SUC n) = (m <= n))` by SIMP_TAC arith_ss[] THEN
   METIS_TAC[],

   ASM_SIMP_TAC list_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM] THEN
   Cases_on `m` THEN SIMP_TAC arith_ss [] THEN
   Cases_on `n` THEN SIMP_TAC arith_ss [] THEN
   METIS_TAC[]
]);


val ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___APPEND_MP =
   store_thm ("ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___APPEND_MP",

``!l n m t1 t2.
    (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l m t1 /\
    ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l (n-m) t2 /\ (m <= n)) ==>
    (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n (t1++t2))``,

METIS_TAC[ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___APPEND]);


val ASL_TRACE_IS_LOCK_FREE___GET_LOCKS = store_thm ("ASL_TRACE_IS_LOCK_FREE___GET_LOCKS",
   ``!L t. ASL_TRACE_IS_LOCK_FREE L t =
      (ASL_TRACE_GET_LOCKS L t = [])``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [ASL_TRACE_IS_LOCK_FREE_def, ASL_TRACE_GET_LOCKS_def] THEN
Induct_on `t` THENL [
   SIMP_TAC list_ss [],
   ASM_SIMP_TAC list_ss [COND_RAND, COND_RATOR]
]);


val ASL_TRACE_IS_LOCK_FREE___REMOVE_LOCKS = store_thm ("ASL_TRACE_IS_LOCK_FREE___REMOVE_LOCKS",
   ``!L t. ASL_TRACE_IS_LOCK_FREE L t =
      (ASL_TRACE_REMOVE_LOCKS L t = t)``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [ASL_TRACE_IS_LOCK_FREE_def, ASL_TRACE_REMOVE_LOCKS_def] THEN
Induct_on `t` THENL [
   SIMP_TAC list_ss [],

   ASM_SIMP_TAC list_ss [COND_RAND, COND_RATOR] THEN
   GEN_TAC THEN
   CCONTR_TAC THEN
   FULL_SIMP_TAC std_ss [] THEN
   `MEM h (FILTER (\x. ~ASL_IS_LOCK_ATOMIC_ACTION L x) t)` by ASM_SIMP_TAC list_ss [] THEN
   FULL_SIMP_TAC std_ss [MEM_FILTER]
]);



val ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_REWRITE = store_thm ("ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_REWRITE",
``(!l t. ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED 0 l t = ASL_TRACE_IS_LOCK_FREE {l} t) /\
  (!n l. ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l [] = (n = 0)) /\
  (!aa n l t. ~(ASL_IS_SING_LOCK_ATOMIC_ACTION l aa) ==>
          (ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l (aa::t) =
           ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l t)) /\
  (!aa1 aa2 n l t. ~(ASL_IS_SING_LOCK_ATOMIC_ACTION l aa2) ==>
          (ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l (aa1::aa2::t) =
           ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l (aa1::t))) /\

  (!n l t. ~(ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l (asl_aa_verhoog l::t))) /\
  (!n l. ~(ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l [asl_aa_prolaag l])) /\

  (!n l t. ~(ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l (asl_aa_prolaag l::asl_aa_prolaag l::t))) /\

  (!n l t. (ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED (SUC n) l (asl_aa_prolaag l::asl_aa_verhoog l::t)) =
       (ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l t))``,



SIMP_TAC list_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_def,
      LIST_NUM_STAR_def,
      ASL_TRACE_GET_LOCKS_def, ASL_IS_SING_LOCK_ATOMIC_ACTION_def,
      ASL_TRACE_IS_LOCK_FREE___GET_LOCKS] THEN
SIMP_TAC std_ss [GSYM FORALL_AND_THM] THEN
Cases_on `n` THEN (
   SIMP_TAC list_ss [LIST_NUM_STAR_def,
      GSYM ASL_IS_SING_LOCK_ATOMIC_ACTION_def,
      ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE2,
      asl_atomic_action_distinct]
));


val ASL_TRACE_IS_LOCK_SYNCHRONISED_REWRITE = store_thm ("ASL_TRACE_IS_LOCK_SYNCHRONISED_REWRITE",
`` (!l. ASL_TRACE_IS_LOCK_SYNCHRONISED l []) /\
   (!aa l t. ~(ASL_IS_SING_LOCK_ATOMIC_ACTION l aa) ==>
          (ASL_TRACE_IS_LOCK_SYNCHRONISED l (aa::t) =
           ASL_TRACE_IS_LOCK_SYNCHRONISED l t)) /\
   (!aa1 aa2 l t. ~(ASL_IS_SING_LOCK_ATOMIC_ACTION l aa2) ==>
          (ASL_TRACE_IS_LOCK_SYNCHRONISED l (aa1::aa2::t) =
           ASL_TRACE_IS_LOCK_SYNCHRONISED l (aa1::t))) /\

   (!t l. ~(ASL_TRACE_IS_LOCK_SYNCHRONISED l (asl_aa_verhoog l::t))) /\
   (!l. ~(ASL_TRACE_IS_LOCK_SYNCHRONISED l [asl_aa_prolaag l])) /\

   (!t l. ~(ASL_TRACE_IS_LOCK_SYNCHRONISED l (asl_aa_prolaag l::asl_aa_prolaag l::t))) /\

   (!t l. (ASL_TRACE_IS_LOCK_SYNCHRONISED l (asl_aa_prolaag l::asl_aa_verhoog l::t)) =
         (ASL_TRACE_IS_LOCK_SYNCHRONISED l t))``,

SIMP_TAC list_ss [ASL_TRACE_IS_LOCK_SYNCHRONISED___NUM,
   ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_REWRITE] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
   Cases_on `n` THENL [
      FULL_SIMP_TAC list_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_REWRITE,
         ASL_TRACE_IS_LOCK_FREE_def, ASL_IS_LOCK_ATOMIC_ACTION_def, IN_SING],

      FULL_SIMP_TAC std_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_REWRITE] THEN
      METIS_TAC[]
   ],

   Q.EXISTS_TAC `SUC n` THEN
   ASM_SIMP_TAC std_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_REWRITE]
]);



val ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___APPEND = store_thm (
   "ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___APPEND",
``
!n1 n2 l t1 t2.
(ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n1 l t1 /\
 ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n2 l t2) ==>
ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED (n1+n2) l (t1++t2)``,

SIMP_TAC std_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_def,
   ASL_TRACE_GET_LOCKS_def, FILTER_APPEND, LIST_NUM_STAR_APPEND]
);




val ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___SUC = store_thm (
   "ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___SUC",
``
!n l t.
ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED (SUC n) l t =
?t0 t1 t2. ASL_TRACE_IS_LOCK_FREE {l} t0 /\
          ASL_TRACE_IS_LOCK_FREE {l} t1 /\
      ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l t2 /\
      (t = t0 ++ [asl_aa_prolaag l]++t1++[asl_aa_verhoog l]++t2)``,


ONCE_REWRITE_TAC [EQ_IMP_THM] THEN
SIMP_TAC std_ss [FORALL_AND_THM] THEN
Tactical.REVERSE CONJ_TAC THEN1 (
   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC list_ss [ASL_TRACE_IS_LOCK_FREE___GET_LOCKS,
      ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_def,
      ASL_TRACE_GET_LOCKS_def, FILTER_APPEND,
      ASL_IS_LOCK_ATOMIC_ACTION_def, IN_SING,
      LIST_NUM_STAR_def]
) THEN

REPEAT STRIP_TAC THEN
`?t0 u1. (t = t0 ++ [asl_aa_prolaag l] ++ u1) /\
      (ASL_TRACE_IS_LOCK_FREE {l} t0) /\
      ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED (SUC n) l (asl_aa_prolaag l::u1)` by ALL_TAC THEN1 (
   Induct_on `t` THENL [
      SIMP_TAC list_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_def,
         ASL_TRACE_GET_LOCKS_def, LIST_NUM_STAR_def],

      REPEAT STRIP_TAC THEN
      Cases_on `ASL_IS_SING_LOCK_ATOMIC_ACTION l h` THENL [
         FULL_SIMP_TAC std_ss [ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE2] THENL [
            Q.EXISTS_TAC `[]` THEN
            Q.EXISTS_TAC `t` THEN
            FULL_SIMP_TAC list_ss [ASL_TRACE_IS_LOCK_FREE_def],

            FULL_SIMP_TAC std_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_REWRITE]
         ],

         FULL_SIMP_TAC std_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_REWRITE] THEN
         Q.EXISTS_TAC `h::t0` THEN
         Q.EXISTS_TAC `u1` THEN
         FULL_SIMP_TAC list_ss [ASL_TRACE_IS_LOCK_FREE_def, ASL_IS_SING_LOCK_ATOMIC_ACTION_def]
      ]
   ]
) THEN

Q.EXISTS_TAC `t0` THEN
ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC, APPEND_11] THEN

(*t is not needed any more*)
Q.PAT_ASSUM `t = X` (K ALL_TAC) THEN
Q.PAT_ASSUM `ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED (SUC n) l t` (K ALL_TAC) THEN

Induct_on `u1` THENL [
   SIMP_TAC list_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_REWRITE],

   REPEAT STRIP_TAC THEN
   Cases_on `ASL_IS_SING_LOCK_ATOMIC_ACTION l h` THENL [
      FULL_SIMP_TAC std_ss [ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE2] THENL [
         FULL_SIMP_TAC std_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_REWRITE],

         Q.EXISTS_TAC `[]` THEN
         Q.EXISTS_TAC `u1` THEN
         FULL_SIMP_TAC list_ss [ASL_TRACE_IS_LOCK_FREE_def, ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_REWRITE]
      ],

      FULL_SIMP_TAC std_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_REWRITE] THEN
      Q.EXISTS_TAC `h::t1` THEN
      Q.EXISTS_TAC `t2` THEN
      FULL_SIMP_TAC list_ss [ASL_TRACE_IS_LOCK_FREE_def, ASL_IS_SING_LOCK_ATOMIC_ACTION_def]
   ]
]);




val ASL_TRACE_LOCK_FLAT_def = Define `
   (ASL_TRACE_LOCK_FLAT l [] = []) /\
   (ASL_TRACE_LOCK_FLAT l [t] = t) /\
   (ASL_TRACE_LOCK_FLAT l (t1::t2::L) =
      t1++((asl_aa_prolaag l)::t2)++((asl_aa_verhoog l)::(ASL_TRACE_LOCK_FLAT l L)))`;

val ASL_TRACE_INV_LOCK_FLAT_def = Define `
   ASL_TRACE_INV_LOCK_FLAT l tl =
      (asl_aa_verhoog l::ASL_TRACE_LOCK_FLAT l tl ++
         [asl_aa_prolaag l])`

val ASL_TRACE_INV_LOCK_FLAT_REWRITE = store_thm ("ASL_TRACE_INV_LOCK_FLAT_REWRITE",
``     (ASL_TRACE_INV_LOCK_FLAT l [] = [asl_aa_verhoog l; asl_aa_prolaag l]) /\
   (ASL_TRACE_INV_LOCK_FLAT l [t] = [asl_aa_verhoog l]++ t ++[asl_aa_prolaag l]) /\
   (ASL_TRACE_INV_LOCK_FLAT l (t1::t2::L) =
      (((asl_aa_verhoog l)::t1)++((asl_aa_prolaag l)::t2) ++ (ASL_TRACE_INV_LOCK_FLAT l L)))``,

SIMP_TAC list_ss [ASL_TRACE_INV_LOCK_FLAT_def, ASL_TRACE_LOCK_FLAT_def] THEN
SIMP_TAC std_ss [GSYM APPEND_ASSOC, APPEND_11, APPEND]);


val ASL_TRACE_INV_LOCK_FLAT___APPEND = store_thm ("ASL_TRACE_INV_LOCK_FLAT___APPEND",
``(ASL_TRACE_INV_LOCK_FLAT l (t1::t2::L) =
      ((ASL_TRACE_INV_LOCK_FLAT l [t1]) ++ t2 ++ (ASL_TRACE_INV_LOCK_FLAT l L)))``,

SIMP_TAC list_ss [ASL_TRACE_INV_LOCK_FLAT_def, ASL_TRACE_LOCK_FLAT_def] THEN
SIMP_TAC std_ss [GSYM APPEND_ASSOC, APPEND_11, APPEND]);


val ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_CHARACTERISATION = store_thm ("ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_CHARACTERISATION",

   ``!n l t. ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l t =
      ?tl. (t =  ASL_TRACE_LOCK_FLAT l tl) /\ (LENGTH tl = SUC (2*n)) /\
            EVERY (ASL_TRACE_IS_LOCK_FREE {l}) tl``,

Induct_on `n` THENL [
   SIMP_TAC list_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_REWRITE,
      LENGTH_EQ_NUM_compute, GSYM LEFT_EXISTS_AND_THM,
      GSYM RIGHT_EXISTS_AND_THM,
      ASL_TRACE_LOCK_FLAT_def],

   `2* SUC n = (SUC (SUC (2*n)))` by DECIDE_TAC THEN
   ASM_SIMP_TAC list_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___SUC,
      GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, LENGTH_EQ_NUM] THEN
   REPEAT (POP_ASSUM (K ALL_TAC)) THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Q.EXISTS_TAC `t0` THEN
      Q.EXISTS_TAC `t1` THEN
      Q.EXISTS_TAC `h` THEN
      Q.EXISTS_TAC `l'` THEN
      ASM_SIMP_TAC std_ss [ASL_TRACE_LOCK_FLAT_def,
         GSYM APPEND_ASSOC, APPEND_11, APPEND],

      Q.EXISTS_TAC `h` THEN
      Q.EXISTS_TAC `h'` THEN
      Q.EXISTS_TAC `h''` THEN
      Q.EXISTS_TAC `l'''` THEN
      ASM_SIMP_TAC std_ss [ASL_TRACE_LOCK_FLAT_def,
         GSYM APPEND_ASSOC, APPEND_11, APPEND]
   ]
]);



val ASL_TRACE_IS_LOCK_FREE___COUNT = store_thm ("ASL_TRACE_IS_LOCK_FREE___COUNT",
``!l t. ASL_TRACE_IS_LOCK_FREE {l} t =
((LIST_ELEM_COUNT (asl_aa_prolaag l) t = 0) /\
(LIST_ELEM_COUNT (asl_aa_verhoog l) t = 0))``,

Induct_on `t` THENL [
   SIMP_TAC list_ss [ASL_TRACE_IS_LOCK_FREE_def,
      LIST_ELEM_COUNT_THM],

   FULL_SIMP_TAC list_ss [ASL_TRACE_IS_LOCK_FREE_def,
      LIST_ELEM_COUNT_DEF, COND_RAND, COND_RATOR,
      GSYM ASL_IS_SING_LOCK_ATOMIC_ACTION_def,
      ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE2] THEN
   METIS_TAC[]
]);


val LIST_ELEM_COUNT___GET_LOCKS = store_thm ("LIST_ELEM_COUNT___GET_LOCKS",
``
((LIST_ELEM_COUNT (asl_aa_prolaag l) (ASL_TRACE_GET_LOCKS {l} t)) =
  (LIST_ELEM_COUNT (asl_aa_prolaag l) t)) /\
((LIST_ELEM_COUNT (asl_aa_verhoog l) (ASL_TRACE_GET_LOCKS {l} t)) =
  (LIST_ELEM_COUNT (asl_aa_verhoog l) t))``,

Induct_on `t` THENL [
   SIMP_TAC list_ss [ASL_TRACE_GET_LOCKS_def],

   Cases_on `h` THEN
   FULL_SIMP_TAC list_ss [ASL_TRACE_GET_LOCKS_def,
      ASL_IS_LOCK_ATOMIC_ACTION_def, LIST_ELEM_COUNT_THM,
      asl_atomic_action_distinct, IN_SING, COND_RAND, COND_RATOR,
      asl_atomic_action_11]
]);


val LIST_ELEM_COUNT___LIST_NUM_STAR = store_thm ("LIST_ELEM_COUNT___LIST_NUM_STAR",

``!e l n. LIST_ELEM_COUNT e (LIST_NUM_STAR n l) = n * (LIST_ELEM_COUNT e l)``,

Induct_on `n` THENL [
   SIMP_TAC list_ss [LIST_NUM_STAR_def, LIST_ELEM_COUNT_THM],
   ASM_SIMP_TAC arith_ss [LIST_NUM_STAR_def, LIST_ELEM_COUNT_THM, MULT]
]);


val ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___COUNT = store_thm ("ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___COUNT",
   ``!l n t. ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l t ==>
((LIST_ELEM_COUNT (asl_aa_prolaag l) t = n) /\
(LIST_ELEM_COUNT (asl_aa_verhoog l) t = n))``,

ONCE_REWRITE_TAC [GSYM LIST_ELEM_COUNT___GET_LOCKS] THEN
SIMP_TAC std_ss  [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_def,
   LIST_ELEM_COUNT___LIST_NUM_STAR, LIST_ELEM_COUNT_THM,
   asl_atomic_action_distinct]);




val ASL_TRACE_IS_SYNCHRONISED___IMPLIES___LOCK_BALANCED = store_thm ("ASL_TRACE_IS_SYNCHRONISED___IMPLIES___LOCK_BALANCED",
   ``!l t. ASL_TRACE_IS_LOCK_SYNCHRONISED l t ==> ASL_TRACE_IS_LOCK_BALANCED_LOCK l t``,

SIMP_TAC std_ss [ASL_TRACE_IS_LOCK_SYNCHRONISED___NUM,
   GSYM LEFT_FORALL_IMP_THM,
   ASL_TRACE_IS_LOCK_BALANCED_def,
   ASL_TRACE_IS_LOCK_BALANCED_LOCK_def] THEN
METIS_TAC[ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___COUNT])


val ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___GET_LOCKS = store_thm (
 "ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___GET_LOCKS",

``!l n t. ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n (ASL_TRACE_GET_LOCKS {l} t) =
    ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n t``,

REWRITE_TAC [ASL_TRACE_GET_LOCKS_def, GSYM ASL_IS_SING_LOCK_ATOMIC_ACTION_def] THEN
Induct_on `t` THEN1 (
   SIMP_TAC list_ss []
) THEN
ASM_SIMP_TAC list_ss [COND_RAND, COND_RATOR,
   ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM] THEN
ASM_SIMP_TAC std_ss [ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE2,
   DISJ_IMP_THM, FORALL_AND_THM,
   ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM]);





val ASL_TRACE_IS_SYNCHRONISED___IMPLIES___STRONG_LOCK_BALANCED = store_thm ("ASL_TRACE_IS_SYNCHRONISED___IMPLIES___STRONG_LOCK_BALANCED",
   ``!l t. ASL_TRACE_IS_LOCK_SYNCHRONISED l t ==> ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l 0 t``,

ONCE_REWRITE_TAC [GSYM ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___GET_LOCKS] THEN
SIMP_TAC std_ss [ASL_TRACE_IS_LOCK_SYNCHRONISED_def,
   LIST_STAR_def, GSYM LEFT_FORALL_IMP_THM] THEN
HO_MATCH_MP_TAC (prove (``(!l n. Q l n) ==> (!l t n. ((P t l n) ==> Q l n))``, METIS_TAC[])) THEN
GEN_TAC THEN
Induct_on `n` THEN (
   ASM_SIMP_TAC list_ss [LIST_NUM_STAR_def, ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM]
));



val ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___REMOVE_LOCKS_1 = store_thm ("ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___REMOVE_LOCKS_1",

``!L l t. (l IN L) ==> ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED 0 l (ASL_TRACE_REMOVE_LOCKS L t)``,

SIMP_TAC list_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_def,
   ASL_TRACE_GET_REMOVE_LOCKS, LIST_NUM_STAR_def] THEN
REPEAT STRIP_TAC THEN
`{l} DIFF L = {}` by ASM_SIMP_TAC std_ss [EXTENSION, IN_SING, IN_DIFF, NOT_IN_EMPTY] THEN
ASM_SIMP_TAC std_ss [ASL_TRACE_GET_LOCKS_REWRITE]);





val ASL_TRACE_IS_LOCK_FREE___REMOVE_LOCKS_IMPL =
   store_thm ("ASL_TRACE_IS_LOCK_FREE___REMOVE_LOCKS_IMPL",
``!L1 L2 t.  ASL_TRACE_IS_LOCK_FREE L1 t ==>
      ASL_TRACE_IS_LOCK_FREE L1 (ASL_TRACE_REMOVE_LOCKS L2 t)``,

SIMP_TAC list_ss [ASL_TRACE_IS_LOCK_FREE_def,
   ASL_TRACE_REMOVE_LOCKS_def] THEN
Induct_on `t` THENL [
   SIMP_TAC list_ss [],
   ASM_SIMP_TAC list_ss [COND_RAND, COND_RATOR]
]);



val ASL_TRACE_IS_LOCK_FREE___REMOVE_LOCKS_2 =
   store_thm ("ASL_TRACE_IS_LOCK_FREE___REMOVE_LOCKS_2",
``!L t. ASL_TRACE_IS_LOCK_FREE L (ASL_TRACE_REMOVE_LOCKS L t)``,

SIMP_TAC list_ss [ASL_TRACE_IS_LOCK_FREE_def,
   ASL_TRACE_REMOVE_LOCKS_def] THEN
Induct_on `t` THENL [
   SIMP_TAC list_ss [],
   ASM_SIMP_TAC list_ss [COND_RAND, COND_RATOR]
]);



val ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___REMOVE_LOCKS_2 = store_thm ("ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___REMOVE_LOCKS_2",

``!L l t n. ~(l IN L) ==>
(ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l (ASL_TRACE_REMOVE_LOCKS L t) =
 (ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l t))``,

SIMP_TAC list_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_def,
   ASL_TRACE_GET_REMOVE_LOCKS, LIST_NUM_STAR_def] THEN
REPEAT STRIP_TAC THEN
`{l} DIFF L = {l}` by ALL_TAC THEN1 (
   ASM_SIMP_TAC std_ss [EXTENSION, IN_SING, IN_DIFF] THEN
   METIS_TAC[]
) THEN
ASM_SIMP_TAC std_ss []);



val ASL_TRACE_IS_LOCK_SYNCHRONISED___REMOVE_LOCKS = store_thm ("ASL_TRACE_IS_LOCK_SYNCHRONISED___REMOVE_LOCKS",

``!L l t. (ASL_TRACE_IS_LOCK_SYNCHRONISED l t) ==> ASL_TRACE_IS_LOCK_SYNCHRONISED l (ASL_TRACE_REMOVE_LOCKS L t)``,

SIMP_TAC std_ss [ASL_TRACE_IS_LOCK_SYNCHRONISED___NUM] THEN
REPEAT STRIP_TAC THEN
Cases_on `l IN L` THENL [
   METIS_TAC[ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___REMOVE_LOCKS_1],
   METIS_TAC[ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___REMOVE_LOCKS_2]
]);



(*Lemma 21*)
val ASL_TRACE_SYNCHRONISED_ACTION_ORDER = store_thm ("ASL_TRACE_SYNCHRONISED_ACTION_ORDER",
``!xenv l t.
(ASL_TRACE_IS_LOCK_SYNCHRONISED l t /\
 IS_SEPARATION_COMBINATOR (FST xenv) /\
 ASL_IS_PRECISE (FST xenv) ((SND xenv) l)) ==>

fasl_action_order
   (ASL_TRACE_SEM xenv (ASL_TRACE_REMOVE_LOCKS {l} t))
   (ASL_TRACE_SEM xenv (((asl_aa_verhoog l) :: t)++[asl_aa_prolaag l]))``,


SIMP_TAC std_ss [ASL_TRACE_IS_LOCK_SYNCHRONISED___NUM] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_CHARACTERISATION] THEN
SIMP_TAC std_ss [GSYM ASL_TRACE_INV_LOCK_FLAT_def] THEN

Q.PAT_ASSUM `t = X` (K ALL_TAC) THEN
Q.PAT_ASSUM `EVERY X tl` MP_TAC THEN
Q.PAT_ASSUM `LENGTH tl = X` MP_TAC THEN

SIMP_TAC std_ss [AND_IMP_INTRO, GSYM CONJ_ASSOC] THEN
Q.SPEC_TAC (`tl`, `tl`) THEN
`?f lock_env. xenv = (f, lock_env)` by (Cases_on `xenv` THEN FULL_SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC std_ss [] THEN

completeInduct_on `n` THEN
`(n:num = 0) \/ (?m:num. n = SUC m)` by (Cases_on `n` THEN SIMP_TAC std_ss []) THENL [
   FULL_SIMP_TAC list_ss [LENGTH_EQ_NUM_compute, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_FORALL_IMP_THM] THEN
   SIMP_TAC std_ss [ASL_TRACE_INV_LOCK_FLAT_REWRITE,
      ASL_TRACE_LOCK_FLAT_def, ASL_TRACE_IS_LOCK_FREE___REMOVE_LOCKS] THEN
   REPEAT STRIP_TAC THEN
   SIMP_TAC list_ss [ASL_TRACE_SEM_def, ASL_ATOMIC_ACTION_SEM_def, asla_big_seq_def, asla_big_seq_APPEND] THEN
   SIMP_TAC std_ss [GSYM asla_big_seq_def] THEN
   MATCH_MP_TAC ASL_LOCK_INTRO_LOCAL_ACTION_ORDER THEN

   ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [GSYM ASL_TRACE_SEM_def] THEN
   ASM_SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___ASL_TRACE_SEM],


   FULL_SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   `?tl0 tl1 tl2. (tl = tl0::tl1::tl2) /\ (LENGTH tl2 = SUC (2 * m))` by ALL_TAC THEN1 (
      `LENGTH tl = SUC (SUC (SUC (2 * m)))` by DECIDE_TAC THEN
      POP_ASSUM MP_TAC THEN
      SIMP_TAC list_ss [LENGTH_EQ_NUM, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
         GSYM LEFT_FORALL_IMP_THM]
   ) THEN
   Q.PAT_ASSUM `!m' tl. P m' tl` (fn thm =>
      MP_TAC (Q.SPECL [`0`, `[tl0]`] thm) THEN
      MP_TAC (Q.SPECL [`m`, `tl2`] thm)
   ) THEN
   FULL_SIMP_TAC list_ss [ASL_TRACE_IS_LOCK_FREE___REMOVE_LOCKS,
      ASL_TRACE_REMOVE_LOCKS_def, ASL_TRACE_LOCK_FLAT_def,
      FILTER_APPEND, ASL_IS_LOCK_ATOMIC_ACTION_def, IN_SING] THEN

   ASM_SIMP_TAC std_ss [GSYM ASL_TRACE_REMOVE_LOCKS_def, ASL_TRACE_INV_LOCK_FLAT___APPEND,
      GSYM APPEND_ASSOC] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC ASL_TRACE_APPEND_ACTION_ORDER THEN
   ASM_SIMP_TAC std_ss [] THEN
   MATCH_MP_TAC ASL_TRACE_APPEND_ACTION_ORDER THEN
   ASM_SIMP_TAC std_ss [] THEN
   SIMP_TAC std_ss [fasl_action_order_def]
]);





val ASL_TRACE_ZIP___COUNT = store_thm ("ASL_TRACE_ZIP___COUNT",

``!t aa t1 t2. (t IN (ASL_TRACE_ZIP t1 t2))
 ==> ((LIST_ELEM_COUNT aa t >= LIST_ELEM_COUNT aa t1 + LIST_ELEM_COUNT aa t2) /\
      (~(ASL_IS_CHECK_ATOMIC_ACTION aa) ==>
       (LIST_ELEM_COUNT aa t = LIST_ELEM_COUNT aa t1 + LIST_ELEM_COUNT aa t2)))``,

Induct_on `t1` THEN1 (
   SIMP_TAC list_ss [ASL_TRACE_ZIP_THM, IN_SING, LIST_ELEM_COUNT_THM]
) THEN
Induct_on `t2` THEN1 (
   SIMP_TAC list_ss [ASL_TRACE_ZIP_THM, IN_SING, LIST_ELEM_COUNT_THM]
) THEN
SIMP_TAC std_ss [ASL_TRACE_ZIP_def, LET_THM] THEN
REPEAT GEN_TAC THEN
Q.ABBREV_TAC `AAC =
      (ASL_IS_PRIM_COMMAND_ATOMIC_ACTION h' /\
      ASL_IS_PRIM_COMMAND_ATOMIC_ACTION h)` THEN
Q.ABBREV_TAC `Z = IMAGE (\x. h'::x) (ASL_TRACE_ZIP t1 (h::t2)) UNION
       IMAGE (\x. h::x) (ASL_TRACE_ZIP (h'::t1) t2)` THEN
STRIP_TAC THEN
Tactical.REVERSE (`!u. u IN Z ==>
    (LIST_ELEM_COUNT aa u >=
    LIST_ELEM_COUNT aa (h'::t1) + LIST_ELEM_COUNT aa (h::t2) /\
    (~ASL_IS_CHECK_ATOMIC_ACTION aa ==>
     (LIST_ELEM_COUNT aa u =
      LIST_ELEM_COUNT aa (h'::t1) + LIST_ELEM_COUNT aa (h::t2))))` by ALL_TAC) THEN1 (
   Cases_on `AAC` THENL [
      FULL_SIMP_TAC list_ss [IN_IMAGE] THEN
      RES_TAC THEN
      REPEAT STRIP_TAC THENL [
         `LIST_ELEM_COUNT aa (asl_aa_check (ASL_GET_PRIM_COMMAND_ATOMIC_ACTION h') (ASL_GET_PRIM_COMMAND_ATOMIC_ACTION h)::x) >=
         LIST_ELEM_COUNT aa x` by ALL_TAC THEN1 (
            SIMP_TAC list_ss [LIST_ELEM_COUNT_DEF, COND_RAND, COND_RATOR]
         ) THEN
         DECIDE_TAC,


         `LIST_ELEM_COUNT aa (asl_aa_check (ASL_GET_PRIM_COMMAND_ATOMIC_ACTION h') (ASL_GET_PRIM_COMMAND_ATOMIC_ACTION h)::x) =
         LIST_ELEM_COUNT aa x` by ALL_TAC THEN1 (
            SIMP_TAC list_ss [LIST_ELEM_COUNT_DEF, COND_RAND, COND_RATOR] THEN
            Q.PAT_ASSUM `~(ASL_IS_CHECK_ATOMIC_ACTION aa)` MP_TAC THEN
            Cases_on `aa` THEN
            SIMP_TAC std_ss [ASL_IS_CHECK_ATOMIC_ACTION_def,
               asl_atomic_action_distinct]
         ) THEN
         ASM_SIMP_TAC std_ss []
      ],

      FULL_SIMP_TAC std_ss []
   ]
) THEN

bossLib.UNABBREV_ALL_TAC THEN
SIMP_TAC list_ss [IN_IMAGE, IN_UNION, DISJ_IMP_THM,
   FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
Q.PAT_ASSUM `t IN X` (K ALL_TAC) THEN
CONJ_TAC THENL [
   GEN_TAC THEN STRIP_TAC THEN
   Q.PAT_ASSUM `!t aa t2. t IN ASL_TRACE_ZIP t1 t2 ==> X aa t t2`
      (MP_TAC o Q.SPECL [`x`, `aa`, `h::t2`]) THEN
   ASM_SIMP_TAC std_ss [] THEN
   Cases_on `h' = aa` THEN (
      ASM_SIMP_TAC arith_ss [LIST_ELEM_COUNT_THM]
   ),

   GEN_TAC THEN STRIP_TAC THEN
   Q.PAT_ASSUM `!h t aa. t IN ASL_TRACE_ZIP (h::t1) t2 ==> X aa t h`
      (MP_TAC o Q.SPECL [`h'`, `x`, `aa`]) THEN
   ASM_SIMP_TAC std_ss [] THEN
   Cases_on `h = aa` THEN (
      ASM_SIMP_TAC arith_ss [LIST_ELEM_COUNT_THM]
   )
]);


val ASL_TRACE_ZIP___LOCK_BALANCED_LOCK = store_thm ("ASL_TRACE_ZIP___LOCK_BALANCED_LOCK",

``!l t t1 t2. ((t IN (ASL_TRACE_ZIP t1 t2)) /\ (ASL_TRACE_IS_LOCK_BALANCED_LOCK l t1) /\
   (ASL_TRACE_IS_LOCK_BALANCED_LOCK l t2))
 ==> (ASL_TRACE_IS_LOCK_BALANCED_LOCK l t)``,

   SIMP_TAC std_ss [ASL_TRACE_IS_LOCK_BALANCED_LOCK_def] THEN
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC ASL_TRACE_ZIP___COUNT THEN
   ASM_SIMP_TAC std_ss [ASL_IS_CHECK_ATOMIC_ACTION_def]
);


val ASL_TRACE_ZIP___IN_CONS_NO_CHECK = store_thm ("ASL_TRACE_ZIP___IN_CONS_NO_CHECK",
``!aa t1 t2 t.

   ~(ASL_IS_CHECK_ATOMIC_ACTION aa) ==>
(
   (aa::t IN ASL_TRACE_ZIP t1 t2) =
   ~(~(t1 = []) /\ ~(t2 = []) /\ ASL_IS_PRIM_COMMAND_ATOMIC_ACTION (HD t1)
      /\ ASL_IS_PRIM_COMMAND_ATOMIC_ACTION (HD t2)) /\
   ((~(t1 = []) /\ (aa = HD t1) /\ (t IN ASL_TRACE_ZIP (TL t1) t2)) \/
   (~(t2 = [])) /\ (aa = HD t2) /\ (t IN ASL_TRACE_ZIP t1 (TL t2))))``,

Cases_on `t1` THEN1 (
   SIMP_TAC list_ss [ASL_TRACE_ZIP_THM, IN_SING] THEN
   Cases_on `t2` THEN SIMP_TAC list_ss []
) THEN
Cases_on `t2` THEN1 (
   SIMP_TAC list_ss [ASL_TRACE_ZIP_THM, IN_SING] THEN
   Cases_on `t1` THEN SIMP_TAC list_ss []
) THEN
SIMP_TAC list_ss [ASL_TRACE_ZIP_def, LET_THM, COND_RAND, COND_RATOR,
   IN_IMAGE,       ASL_IS_CHECK_ATOMIC_ACTION_def] THEN
SIMP_TAC std_ss [COND_EXPAND_IMP, FORALL_AND_THM, ASL_IS_CHECK_ATOMIC_ACTION_def] THEN
SIMP_TAC list_ss [IN_UNION, IN_IMAGE, AND_IMP_INTRO,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM]);




val ASL_TRACE_ZIP___STRONG_LOCK_BALANCED_LOCK = store_thm ("ASL_TRACE_ZIP___STRONG_LOCK_BALANCED_LOCK",

``!l t n1 n2 t1 t2. ((t IN (ASL_TRACE_ZIP t1 t2)) /\
   (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n1 t1) /\
   (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l n2 t2))
 ==> (ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l (n1+n2) t)``,

Induct_on `t1` THEN1 (
   SIMP_TAC std_ss [ASL_TRACE_ZIP_THM, IN_SING, ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM]
) THEN
Induct_on `t2` THEN1 (
   SIMP_TAC std_ss [ASL_TRACE_ZIP_THM, IN_SING, ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM]
) THEN
SIMP_TAC std_ss [ASL_TRACE_ZIP_def, LET_THM] THEN
REPEAT GEN_TAC THEN
Q.ABBREV_TAC `aa_cond = ASL_IS_PRIM_COMMAND_ATOMIC_ACTION h' /\
       ASL_IS_PRIM_COMMAND_ATOMIC_ACTION h` THEN
Q.ABBREV_TAC `z = IMAGE (\x. h'::x) (ASL_TRACE_ZIP t1 (h::t2)) UNION
       IMAGE (\x. h::x) (ASL_TRACE_ZIP (h'::t1) t2)` THEN
REPEAT STRIP_TAC THEN

Tactical.REVERSE (`!t. t IN z ==> ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l (n1 + n2) t` by ALL_TAC) THEN1 (
   Cases_on `aa_cond` THEN (
      FULL_SIMP_TAC list_ss [IN_IMAGE, ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM,
         ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE]
   )
) THEN
Q.PAT_ASSUM `t IN X` (K ALL_TAC) THEN
bossLib.UNABBREV_ALL_TAC THEN
SIMP_TAC std_ss [IN_UNION, IN_IMAGE, DISJ_IMP_THM, FORALL_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THENL [
   Cases_on `~(ASL_IS_SING_LOCK_ATOMIC_ACTION l h')` THEN1 (
      FULL_SIMP_TAC std_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM] THEN
      METIS_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE2] THEN FULL_SIMP_TAC std_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM] THENL [
      METIS_TAC[ADD_CLAUSES],

      Cases_on `n1` THEN FULL_SIMP_TAC arith_ss [] THEN
      `PRE (n2 + SUC n) = (n + n2)` by DECIDE_TAC THEN
      METIS_TAC[]
   ],


   Cases_on `~(ASL_IS_SING_LOCK_ATOMIC_ACTION l h)` THEN1 (
      FULL_SIMP_TAC std_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM] THEN
      METIS_TAC[]
   ) THEN
   FULL_SIMP_TAC std_ss [ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE2] THEN FULL_SIMP_TAC std_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM] THENL [
      METIS_TAC[ADD_CLAUSES],

      Cases_on `n2` THEN FULL_SIMP_TAC arith_ss [] THEN
      `PRE (n1 + SUC n) = (n1 + n)` by DECIDE_TAC THEN
      METIS_TAC[]
   ]
]);

val ASL_TRACE_ZIP___EMPTY = store_thm ("ASL_TRACE_ZIP___EMPTY",

``!t1 t2. [] IN (ASL_TRACE_ZIP t1 t2) ==> (t1 = []) /\ (t2 = [])``,

Induct_on `t1` THEN1 (
   SIMP_TAC std_ss [ASL_TRACE_ZIP_THM, IN_SING]
) THEN
Cases_on `t2` THEN1 (
   SIMP_TAC list_ss [ASL_TRACE_ZIP_THM, IN_SING]
) THEN
SIMP_TAC list_ss [ASL_TRACE_ZIP_def, LET_THM, COND_RAND, COND_RATOR,
   IN_IMAGE, IN_UNION]);



val ASL_TRACE_ZIP___FILTER = store_thm ("ASL_TRACE_ZIP___FILTER",
``!P. (!pc1 pc2. ~(P (asl_aa_check pc1 pc2))) ==>
(!t t1 t2.
((t IN ASL_TRACE_ZIP t1 t2) ==>
?t'. (t' IN ASL_TRACE_ZIP (FILTER P t1) (FILTER P t2)) /\
     (FILTER P t = FILTER P t')))``,


GEN_TAC THEN STRIP_TAC THEN
Induct_on `t1` THEN1 (
   SIMP_TAC list_ss [ASL_TRACE_ZIP_THM, IN_SING,
      FILTER_IDEM]
) THEN
Induct_on `t2` THEN1 (
   SIMP_TAC list_ss [ASL_TRACE_ZIP_THM, IN_SING] THEN
   SIMP_TAC list_ss [COND_RATOR, COND_RAND, FILTER_IDEM]
) THEN

SIMP_TAC std_ss [ASL_TRACE_ZIP_def, LET_THM] THEN
REPEAT GEN_TAC THEN
Q.ABBREV_TAC `aa_cond = ASL_IS_PRIM_COMMAND_ATOMIC_ACTION h' /\
            ASL_IS_PRIM_COMMAND_ATOMIC_ACTION h` THEN
Q.ABBREV_TAC `z = IMAGE (\x. h'::x) (ASL_TRACE_ZIP t1 (h::t2)) UNION
       IMAGE (\x. h::x) (ASL_TRACE_ZIP (h'::t1) t2)` THEN
Tactical.REVERSE (`!t. t IN z ==> ?t'.
      t' IN ASL_TRACE_ZIP (FILTER P (h'::t1)) (FILTER P (h::t2)) /\
      (FILTER P t = FILTER P t')` by ALL_TAC) THEN1 (

   Cases_on `aa_cond` THEN ASM_REWRITE_TAC[] THEN
   FULL_SIMP_TAC list_ss [IN_IMAGE, GSYM LEFT_FORALL_IMP_THM]
) THEN
bossLib.UNABBREV_ALL_TAC THEN
SIMP_TAC std_ss [IN_UNION, IN_IMAGE, DISJ_IMP_THM, FORALL_AND_THM,
   GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THENL [
   Cases_on `P h'` THEN ASM_SIMP_TAC std_ss [FILTER_COND_REWRITE] THEN
   `?t'. t' IN ASL_TRACE_ZIP (FILTER P t1) (FILTER P (h::t2)) /\
         (FILTER P x = FILTER P t')` by METIS_TAC[] THEN
   Q.ABBREV_TAC `t3 = FILTER P t1` THEN
   Q.ABBREV_TAC `t4 = FILTER P (h::t2)` THEN
   NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
   Q.PAT_ASSUM `!h t. X h t` (K ALL_TAC) THEN
   Q.PAT_ASSUM `!t t2. X t t2` (K ALL_TAC) THEN
   Cases_on `t4` THEN1 (
      FULL_SIMP_TAC std_ss [ASL_TRACE_ZIP_THM, IN_SING,
         FILTER_COND_REWRITE]
   ) THEN
   ASM_SIMP_TAC std_ss [ASL_TRACE_ZIP_def, LET_THM,
      COND_RAND, COND_RATOR] THEN
   HO_MATCH_MP_TAC (
      prove (``(((?t''. Q t'') ==> (?t''. P t'')) /\ (?t''. Q t'')) ==> (?t''. if C' then P t'' else Q t'')``,
         METIS_TAC[])) THEN
   CONJ_TAC THEN1 (
      ASM_SIMP_TAC std_ss [IN_IMAGE, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, FILTER_COND_REWRITE]
   ) THEN
   ASM_SIMP_TAC std_ss [IN_UNION, IN_IMAGE, RIGHT_AND_OVER_OR,
      EXISTS_OR_THM, GSYM LEFT_EXISTS_AND_THM, FILTER_COND_REWRITE,
      CONS_11] THEN
   DISJ1_TAC THEN METIS_TAC[],



   Cases_on `P h` THEN ASM_SIMP_TAC std_ss [FILTER_COND_REWRITE] THEN
   `?t'. t' IN ASL_TRACE_ZIP (FILTER P (h'::t1)) (FILTER P (t2)) /\
         (FILTER P x = FILTER P t')` by METIS_TAC[] THEN
   Q.ABBREV_TAC `t3 = FILTER P (h'::t1)` THEN
   Q.ABBREV_TAC `t4 = FILTER P t2` THEN
   NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
   Q.PAT_ASSUM `!h t. X h t` (K ALL_TAC) THEN
   Q.PAT_ASSUM `!t t2. X t t2` (K ALL_TAC) THEN
   Cases_on `t3` THEN1 (
      FULL_SIMP_TAC std_ss [ASL_TRACE_ZIP_THM, IN_SING,
         FILTER_COND_REWRITE]
   ) THEN
   ASM_SIMP_TAC std_ss [ASL_TRACE_ZIP_def, LET_THM,
      COND_RAND, COND_RATOR] THEN
   HO_MATCH_MP_TAC (
      prove (``(((?t''. Q t'') ==> (?t''. P t'')) /\ (?t''. Q t'')) ==> (?t''. if C' then P t'' else Q t'')``,
         METIS_TAC[])) THEN
   CONJ_TAC THEN1 (
      ASM_SIMP_TAC std_ss [IN_IMAGE, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, FILTER_COND_REWRITE]
   ) THEN
   ASM_SIMP_TAC std_ss [IN_UNION, IN_IMAGE, RIGHT_AND_OVER_OR,
      EXISTS_OR_THM, GSYM LEFT_EXISTS_AND_THM, FILTER_COND_REWRITE,
      CONS_11] THEN
   DISJ2_TAC THEN METIS_TAC[]
]);


val ASL_TRACE_ZIP___FILTER2 = store_thm ("ASL_TRACE_ZIP___FILTER2",
``!P. (!pc1 pc2. ~(P (asl_aa_check pc1 pc2))) /\
   (!pc1. ~(P (asl_aa_pc pc1))) ==>

(!t t1 t2.
((t IN ASL_TRACE_ZIP t1 t2) ==>
(FILTER P t IN ASL_TRACE_ZIP (FILTER P t1) (FILTER P t2))))``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPEC `P` ASL_TRACE_ZIP___FILTER) THEN
ASM_SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
Q.EXISTS_TAC `t` THEN
Q.EXISTS_TAC `t1` THEN
Q.EXISTS_TAC `t2` THEN
ASM_SIMP_TAC std_ss [] THEN
STRIP_TAC THEN
Tactical.REVERSE (`!t1 t2 t.
(t IN ASL_TRACE_ZIP (FILTER P t1) (FILTER P t2)) ==>
(FILTER P t = t)` by ALL_TAC) THEN1 (
   METIS_TAC[]
) THEN

NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
Induct_on `t1` THEN1 (
   SIMP_TAC list_ss [ASL_TRACE_ZIP_THM, IN_SING, FILTER_IDEM]
) THEN
Induct_on `t2` THEN1 (
   SIMP_TAC list_ss [ASL_TRACE_ZIP_THM, IN_SING, FILTER_IDEM] THEN
   SIMP_TAC list_ss [COND_RATOR, COND_RAND, FILTER_IDEM]
) THEN
REPEAT GEN_TAC THEN
Cases_on `~(P h')` THEN1 (
   METIS_TAC[FILTER_COND_REWRITE]
) THEN
Cases_on `~(P h)` THEN1 (
   PROVE_TAC[FILTER_COND_REWRITE]
) THEN
`~ASL_IS_PRIM_COMMAND_ATOMIC_ACTION h` by ALL_TAC THEN1 (
   Cases_on `h` THEN
   SIMP_TAC std_ss [ASL_IS_PRIM_COMMAND_ATOMIC_ACTION_def] THEN
   METIS_TAC[]
) THEN
NTAC 3 (POP_ASSUM MP_TAC) THEN
SIMP_TAC std_ss [FILTER_COND_REWRITE, ASL_TRACE_ZIP_def, LET_THM] THEN
SIMP_TAC list_ss [IN_UNION, IN_IMAGE, DISJ_IMP_THM, GSYM LEFT_FORALL_IMP_THM] THEN
METIS_TAC[FILTER_COND_REWRITE]);


val ASL_TRACE_ZIP___GET_LOCKS = store_thm ("ASL_TRACE_ZIP___GET_LOCKS",
``!L t t1 t2.
(t IN ASL_TRACE_ZIP t1 t2) ==>
(ASL_TRACE_GET_LOCKS L t IN ASL_TRACE_ZIP (ASL_TRACE_GET_LOCKS L t1) (ASL_TRACE_GET_LOCKS L t2))``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [ASL_TRACE_GET_LOCKS_def] THEN
MATCH_MP_TAC (SIMP_RULE std_ss [GSYM RIGHT_FORALL_IMP_THM,
   AND_IMP_INTRO] ASL_TRACE_ZIP___FILTER2) THEN
ASM_REWRITE_TAC[ASL_IS_LOCK_ATOMIC_ACTION_def]);





val LENGTH_LOCK_TRACE = store_thm ("LENGTH_LOCK_TRACE",
``!l t. (EVERY (ASL_IS_SING_LOCK_ATOMIC_ACTION l) t) ==>
   (LENGTH t = LIST_ELEM_COUNT (asl_aa_prolaag l) t + LIST_ELEM_COUNT (asl_aa_verhoog l) t)``,

Induct_on `t` THEN (
   ASM_SIMP_TAC list_ss [LIST_ELEM_COUNT_THM, ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE2,
      LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM,
      asl_atomic_action_distinct, ADD_CLAUSES]
));


val LENGTH_STRONG_BALANCED_LOCK_TRACE =
   store_thm ("LENGTH_STRONG_BALANCED_LOCK_TRACE",
``!l m t.
ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l m t /\
(EVERY (ASL_IS_SING_LOCK_ATOMIC_ACTION l) t) ==>
?n. (LENGTH t + m = 2*n)``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC LENGTH_LOCK_TRACE THEN
IMP_RES_TAC ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___COUNT THEN
FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `(LIST_ELEM_COUNT (asl_aa_prolaag l) t + m)` THEN
DECIDE_TAC);




val ASL_TRACE_ZIP___STRONG_LOCK_BALANCED_SYNCHRONISED =
   store_thm ("ASL_TRACE_ZIP___STRONG_LOCK_BALANCED_SYNCHRONISED",

``
!l t t1 t2.
((t IN ASL_TRACE_ZIP t1 t2) /\
ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l 0 t1 /\
ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l 0 t2 /\
ASL_TRACE_IS_LOCK_SYNCHRONISED l t) ==>

(ASL_TRACE_IS_LOCK_SYNCHRONISED l t1 /\ ASL_TRACE_IS_LOCK_SYNCHRONISED l t2)``,


ONCE_ASM_REWRITE_TAC [GSYM ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___GET_LOCKS,
   ASL_TRACE_IS_LOCK_SYNCHRONISED_def, LIST_STAR_def] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN

`(ASL_TRACE_GET_LOCKS {l} t IN ASL_TRACE_ZIP (ASL_TRACE_GET_LOCKS {l} t1) (ASL_TRACE_GET_LOCKS {l} t2))` by ALL_TAC THEN1 (
   METIS_TAC  [ASL_TRACE_ZIP___GET_LOCKS]
) THEN
Q.ABBREV_TAC `ft = ASL_TRACE_GET_LOCKS {l} t` THEN
Q.ABBREV_TAC `ft1 = ASL_TRACE_GET_LOCKS {l} t1` THEN
Q.ABBREV_TAC `ft2 = ASL_TRACE_GET_LOCKS {l} t2` THEN
`(ASL_TRACE_GET_LOCKS {l} ft1 = ft1) /\ (ASL_TRACE_GET_LOCKS {l} ft2 = ft2) /\
  (ASL_TRACE_GET_LOCKS {l} ft = ft) /\
  (EVERY (ASL_IS_LOCK_ATOMIC_ACTION {l}) ft1) /\
  (EVERY (ASL_IS_LOCK_ATOMIC_ACTION {l}) ft2) /\
  EVERY (ASL_IS_LOCK_ATOMIC_ACTION {l}) ft` by ALL_TAC THEN1 (
   bossLib.UNABBREV_ALL_TAC THEN
   SIMP_TAC list_ss [ASL_IS_LOCK_ATOMIC_ACTION_def, ASL_TRACE_GET_LOCKS_def,
      EVERY_FILTER, FILTER_IDEM]
) THEN
FULL_SIMP_TAC std_ss [GSYM ASL_IS_SING_LOCK_ATOMIC_ACTION_def,
   GSYM ASL_TRACE_GET_SING_LOCKS_def] THEN
`?n1 n2. (LENGTH ft1 = 2*n1) /\ (LENGTH ft2 = 2*n2)` by ALL_TAC THEN1 (
   IMP_RES_TAC LENGTH_STRONG_BALANCED_LOCK_TRACE THEN
   FULL_SIMP_TAC arith_ss [] THEN
   METIS_TAC[]
) THEN
NTAC 2 (POP_ASSUM MP_TAC) THEN
REPEAT (Q.PAT_ASSUM `EVERY X Y` MP_TAC) THEN
REPEAT (Q.PAT_ASSUM `ASL_TRACE_GET_SING_LOCKS l X = X` MP_TAC) THEN
Q.PAT_ASSUM `ft IN X` MP_TAC THEN
Q.PAT_ASSUM `LIST_STAR X Y` MP_TAC THEN
REPEAT (Q.PAT_ASSUM `ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l 0 x` MP_TAC) THEN
REPEAT (POP_ASSUM (K ALL_TAC)) THEN
SIMP_TAC std_ss [AND_IMP_INTRO, GSYM CONJ_ASSOC] THEN
Q.SPEC_TAC (`ft1`, `ft1`) THEN
Q.SPEC_TAC (`ft2`, `ft2`) THEN
Q.SPEC_TAC (`ft`, `ft`) THEN
Q.SPEC_TAC (`n1`, `n1`) THEN
Q.SPEC_TAC (`n2`, `n2`) THEN

Induct_on `n1` THEN1 (
   FULL_SIMP_TAC list_ss [LENGTH_EQ_NUM,
      ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM,
      ASL_TRACE_ZIP_THM, IN_SING, LIST_STAR_REWRITE,
      ASL_TRACE_GET_SING_LOCKS_REWRITE] THEN
   PROVE_TAC[]
) THEN
Induct_on `n2` THEN1 (
   SIMP_TAC list_ss [LENGTH_EQ_NUM,ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM,
      ASL_TRACE_ZIP_THM, IN_SING, LIST_STAR_REWRITE,
      ASL_TRACE_GET_SING_LOCKS_REWRITE]
) THEN
`(2*SUC n1) = SUC (SUC (2*n1))` by DECIDE_TAC THEN
`(2*SUC n2) = SUC (SUC (2*n2))` by DECIDE_TAC THEN
ASM_REWRITE_TAC[] THEN
SIMP_TAC std_ss [LENGTH_EQ_NUM, GSYM LEFT_EXISTS_AND_THM,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
REWRITE_TAC [ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE2,
   LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM,
   EVERY_DEF] THEN
SIMP_TAC list_ss [FORALL_AND_THM, ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM,
   ASL_TRACE_GET_SING_LOCKS_REWRITE,
   ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE] THEN
REPEAT CONJ_TAC THEN
REPEAT GEN_TAC THEN STRIP_TAC THENL [
   Q.PAT_ASSUM `!ft ft2 ft1. X ft ft2 ft1` (K ALL_TAC) THEN
   Q.PAT_ASSUM `!n2 ft ft2 ft1. X n2 ft ft2 ft1` (K ALL_TAC) THEN
   SIMP_TAC list_ss [LIST_STAR_REWRITE, asl_atomic_action_distinct] THEN
   `?ft'. ft = asl_aa_prolaag l::asl_aa_prolaag l::ft'` by ALL_TAC THEN1 (
      FULL_SIMP_TAC list_ss [ASL_TRACE_ZIP_THM, ASL_IS_PRIM_COMMAND_ATOMIC_ACTION_def,
    LET_THM, IN_UNION, IN_IMAGE]
   ) THEN
   FULL_SIMP_TAC list_ss [LIST_STAR_REWRITE, asl_atomic_action_distinct],



   `LIST_STAR [asl_aa_prolaag l; asl_aa_verhoog l]
      (asl_aa_prolaag l::asl_aa_verhoog l::l''') =
    LIST_STAR [asl_aa_prolaag l; asl_aa_verhoog l] l'''` by SIMP_TAC list_ss [LIST_STAR_REWRITE] THEN
   ASM_REWRITE_TAC[] THEN
   Q.PAT_ASSUM `!ft ft2 ft1. X ft ft2 ft1` (MATCH_MP_TAC) THEN
   Q.PAT_ASSUM `!n2 ft ft2 ft1. X n2 ft ft2 ft1` (K ALL_TAC) THEN
   ASM_SIMP_TAC list_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM,
      ASL_TRACE_GET_SING_LOCKS_REWRITE, ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE] THEN
   FULL_SIMP_TAC list_ss [ASL_TRACE_ZIP_THM, ASL_IS_PRIM_COMMAND_ATOMIC_ACTION_def, LET_THM,
      IN_IMAGE, IN_UNION] THEN
   FULL_SIMP_TAC list_ss [LIST_STAR_REWRITE, asl_atomic_action_distinct,
      ASL_TRACE_ZIP___IN_CONS_NO_CHECK, ASL_IS_CHECK_ATOMIC_ACTION_def,
      ASL_IS_PRIM_COMMAND_ATOMIC_ACTION_def] THEN
   Q.EXISTS_TAC `x'` THEN
   Q.PAT_ASSUM `ft = X` ASSUME_TAC THEN
   FULL_SIMP_TAC list_ss [ASL_TRACE_GET_SING_LOCKS_REWRITE,
      ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE],



   `LIST_STAR [asl_aa_prolaag l; asl_aa_verhoog l]
      (asl_aa_prolaag l::asl_aa_verhoog l::l'') =
    LIST_STAR [asl_aa_prolaag l; asl_aa_verhoog l] l''` by SIMP_TAC list_ss [LIST_STAR_REWRITE] THEN
   ASM_REWRITE_TAC[] THEN
   Q.PAT_ASSUM `!ft ft2 ft1. X ft ft2 ft1` (K ALL_TAC) THEN
   Q.PAT_ASSUM `!n2 ft ft2 ft1. X n2 ft ft2 ft1` (MATCH_MP_TAC) THEN
   Q.EXISTS_TAC `SUC n2` THEN
   ASM_SIMP_TAC list_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM,
      ASL_TRACE_GET_SING_LOCKS_REWRITE, ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE] THEN
   FULL_SIMP_TAC list_ss [ASL_TRACE_ZIP_THM, ASL_IS_PRIM_COMMAND_ATOMIC_ACTION_def, LET_THM,
      IN_IMAGE, IN_UNION] THEN
   FULL_SIMP_TAC list_ss [LIST_STAR_REWRITE, asl_atomic_action_distinct,
      ASL_TRACE_ZIP___IN_CONS_NO_CHECK, ASL_IS_CHECK_ATOMIC_ACTION_def,
      ASL_IS_PRIM_COMMAND_ATOMIC_ACTION_def] THEN
   Q.EXISTS_TAC `x'` THEN
   Q.PAT_ASSUM `ft = X` ASSUME_TAC THEN
   FULL_SIMP_TAC list_ss [ASL_TRACE_GET_SING_LOCKS_REWRITE,
      ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE],



   `?x'. (ft = asl_aa_prolaag l::asl_aa_verhoog l::x') /\
    ((x' IN ASL_TRACE_ZIP l''
       (asl_aa_prolaag l::asl_aa_verhoog l::l''')) \/
    (x' IN ASL_TRACE_ZIP (asl_aa_prolaag l::asl_aa_verhoog l::l'') l'''))` by ALL_TAC THEN1 (


      Q.PAT_ASSUM `!ft ft2 ft1. X ft ft2 ft1` (K ALL_TAC) THEN
      Q.PAT_ASSUM `!n2 ft ft2 ft1. X n2 ft ft2 ft1` (K ALL_TAC) THEN
      FULL_SIMP_TAC list_ss [ASL_TRACE_ZIP_THM, ASL_IS_PRIM_COMMAND_ATOMIC_ACTION_def, LET_THM,
    IN_IMAGE, IN_UNION] THEN
      FULL_SIMP_TAC list_ss [LIST_STAR_REWRITE, asl_atomic_action_distinct,
    ASL_TRACE_ZIP___IN_CONS_NO_CHECK, ASL_IS_CHECK_ATOMIC_ACTION_def,
    ASL_IS_PRIM_COMMAND_ATOMIC_ACTION_def]
   ) THENL [
      `LIST_STAR [asl_aa_prolaag l; asl_aa_verhoog l]
    (asl_aa_prolaag l::asl_aa_verhoog l::l'') =
      LIST_STAR [asl_aa_prolaag l; asl_aa_verhoog l] l''` by SIMP_TAC list_ss [LIST_STAR_REWRITE] THEN
      ASM_REWRITE_TAC[] THEN
      Q.PAT_ASSUM `!ft ft2 ft1. X ft ft2 ft1` (K ALL_TAC) THEN
      Q.PAT_ASSUM `!n2 ft ft2 ft1. X n2 ft ft2 ft1` (MATCH_MP_TAC) THEN
      Q.EXISTS_TAC `SUC n2` THEN
      Q.EXISTS_TAC `x'` THEN
      FULL_SIMP_TAC list_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM,
    ASL_TRACE_GET_SING_LOCKS_REWRITE, ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE,
    LIST_STAR_REWRITE],


      `LIST_STAR [asl_aa_prolaag l; asl_aa_verhoog l]
    (asl_aa_prolaag l::asl_aa_verhoog l::l''') =
      LIST_STAR [asl_aa_prolaag l; asl_aa_verhoog l] l'''` by SIMP_TAC list_ss [LIST_STAR_REWRITE] THEN
      ASM_REWRITE_TAC[] THEN
      Q.PAT_ASSUM `!ft ft2 ft1. X ft ft2 ft1` (MATCH_MP_TAC) THEN
      Q.PAT_ASSUM `!n2 ft ft2 ft1. X n2 ft ft2 ft1` (K ALL_TAC) THEN
      Q.EXISTS_TAC `x'` THEN
      FULL_SIMP_TAC list_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM,
    ASL_TRACE_GET_SING_LOCKS_REWRITE, ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE,
    LIST_STAR_REWRITE]
   ]
]);






val ASL_TRACE_ZIP___SIMPLE_APPEND = store_thm ("ASL_TRACE_ZIP___SIMPLE_APPEND",
``!t1 t2. ?t. t IN (ASL_TRACE_ZIP t1 t2) /\ (ASL_TRACE_REMOVE_CHECKS t = ASL_TRACE_REMOVE_CHECKS (t1++t2))``,

Induct_on `t1` THEN1 (
   SIMP_TAC list_ss [ASL_TRACE_ZIP_THM, IN_SING]
) THEN
Cases_on `t2` THEN1 (
   SIMP_TAC list_ss [ASL_TRACE_ZIP_THM, IN_SING]
) THEN

SIMP_TAC list_ss [ASL_TRACE_ZIP_def, LET_THM] THEN
REPEAT GEN_TAC THEN
Q.ABBREV_TAC `aa_cond = ASL_IS_PRIM_COMMAND_ATOMIC_ACTION h' /\
            ASL_IS_PRIM_COMMAND_ATOMIC_ACTION h` THEN
Q.ABBREV_TAC `X = IMAGE (\x. h'::x) (ASL_TRACE_ZIP t1 (h::t)) UNION
    IMAGE (\x. h::x) (ASL_TRACE_ZIP (h'::t1) t)` THEN
Tactical.REVERSE (`?u. u IN X /\
(ASL_TRACE_REMOVE_CHECKS u =
 ASL_TRACE_REMOVE_CHECKS (h'::(t1 ++ h::t)))` by ALL_TAC) THEN1 (

   Cases_on `aa_cond` THEN (
      FULL_SIMP_TAC list_ss [IN_IMAGE,
         GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
         ASL_TRACE_REMOVE_CHECKS_def,
         ASL_IS_CHECK_ATOMIC_ACTION_def] THEN
      METIS_TAC[]
   )
) THEN

bossLib.UNABBREV_ALL_TAC THEN
SIMP_TAC list_ss [IN_UNION, IN_IMAGE, EXISTS_OR_THM,
   RIGHT_AND_OVER_OR, GSYM LEFT_EXISTS_AND_THM] THEN
DISJ1_TAC THEN
SIMP_TAC std_ss [ASL_TRACE_REMOVE_CHECKS_def, FILTER, COND_RAND, COND_RATOR] THEN
SIMP_TAC list_ss [GSYM ASL_TRACE_REMOVE_CHECKS_def] THEN
METIS_TAC[]
)



val ASL_TRACE_IS_LOCK_FREE___REMOVE_CHECKS = store_thm ("ASL_TRACE_IS_LOCK_FREE___REMOVE_CHECKS",
 ``!L t.
      ASL_TRACE_IS_LOCK_FREE L (ASL_TRACE_REMOVE_CHECKS t) =
      ASL_TRACE_IS_LOCK_FREE L t``,

Induct_on `t` THENL [
   SIMP_TAC list_ss [ASL_TRACE_REMOVE_CHECKS_def],

   Cases_on `h` THEN
   FULL_SIMP_TAC list_ss [ASL_IS_CHECK_ATOMIC_ACTION_def,
      ASL_IS_LOCK_ATOMIC_ACTION_def, ASL_TRACE_IS_LOCK_FREE_def,
      ASL_TRACE_REMOVE_CHECKS_def]
]);






val ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___ASL_TRACE_REMOVE_CHECKS =
   store_thm ("ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___ASL_TRACE_REMOVE_CHECKS",
``!n l t.
ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l (ASL_TRACE_REMOVE_CHECKS t) =
ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n l t``,

SIMP_TAC std_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_def, ASL_TRACE_GET_LOCKS_def, ASL_TRACE_REMOVE_CHECKS_def,
   FILTER_FILTER, GSYM ASL_IS_SING_LOCK_ATOMIC_ACTION_def] THEN
REPEAT GEN_TAC THEN
MATCH_MP_TAC (prove (``(A = B) ==> ((A = C) = (B = C))``, SIMP_TAC std_ss [])) THEN
AP_THM_TAC THEN AP_TERM_TAC THEN
REWRITE_TAC [FUN_EQ_THM] THEN
Cases_on `x` THEN (
   SIMP_TAC std_ss [ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE, ASL_IS_CHECK_ATOMIC_ACTION_def]
));



val ASL_TRACE_ZIP___NON_EMPTY = store_thm ("ASL_TRACE_ZIP___NON_EMPTY",
``!t1 t2. ?t. t IN (ASL_TRACE_ZIP t1 t2) /\
   (!n1 n2 l.
   ((ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n1 l t1 /\
    ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n2 l t2) ==> ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED (n1+n2) l t))``,

REPEAT STRIP_TAC THEN
ASSUME_TAC (Q.SPECL [`t1`, `t2`] ASL_TRACE_ZIP___SIMPLE_APPEND) THEN
FULL_SIMP_TAC std_ss [] THEN
Q.EXISTS_TAC `t` THEN
ONCE_REWRITE_TAC[GSYM ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___ASL_TRACE_REMOVE_CHECKS] THEN
ASM_SIMP_TAC std_ss [ASL_TRACE_REMOVE_CHECKS_APPEND] THEN
METIS_TAC[ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___APPEND]);





val ASL_PROTO_TRACES_EVAL___STRONG_LOCK_BALANCED = store_thm ("ASL_PROTO_TRACES_EVAL___STRONG_LOCK_BALANCED",

``!penv pt t. t IN ASL_PROTO_TRACES_EVAL penv pt ==>
             ASL_TRACE_IS_STRONG_LOCK_BALANCED t``,

SIMP_TAC std_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_def,
   ASL_PROTO_TRACES_EVAL_def, IN_ABS,
   GSYM LEFT_FORALL_IMP_THM] THEN

completeInduct_on `n` THEN
Induct_on `pt` THEN (
   ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM]
) THENL [
   SIMP_TAC std_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM,
      ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE],

   FULL_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___APPEND_MP THEN
   SIMP_TAC std_ss [] THEN
   METIS_TAC[],


   `!l. ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK l 0 [asl_aa_fail:('c, 'd) asl_atomic_action]` by ALL_TAC THEN1 (
      SIMP_TAC std_ss [
         ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM,
         ASL_IS_SING_LOCK_ATOMIC_ACTION_REWRITE,
         asl_aa_fail_def]
   ) THEN
   Cases_on `n` THEN1 (
      ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM]
   ) THEN
   SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM,
      ASL_PROGRAM_TRACES_PROC_IN_THM2, IN_ABS] THEN
   `n' < SUC n'` by DECIDE_TAC THEN
   METIS_TAC[],


   FULL_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM, GSYM
      ASL_TRACE_IS_LOCK_BALANCED_LOCK_def] THEN
   METIS_TAC[ASL_TRACE_ZIP___STRONG_LOCK_BALANCED_LOCK, ADD_CLAUSES],


   SIMP_TAC list_ss [GSYM LEFT_FORALL_IMP_THM,
      ASL_TRACE_REMOVE_LOCKS_REWRITE,
      ASL_IS_LOCK_ATOMIC_ACTION_def, IN_SING] THEN
   ONCE_REWRITE_TAC [GSYM ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___GET_LOCKS] THEN
   SIMP_TAC std_ss [ASL_TRACE_GET_REMOVE_LOCKS] THEN
   REPEAT STRIP_TAC THEN
   Cases_on `l' = l` THENL [
      `{l} DIFF {l} = {}` by ALL_TAC THEN1 (
         SIMP_TAC std_ss [EXTENSION, IN_DIFF, NOT_IN_EMPTY]
      ) THEN
      ASM_SIMP_TAC std_ss [ASL_TRACE_GET_LOCKS_REWRITE,
         ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM],

      `{l'} DIFF {l} = {l'}` by ALL_TAC THEN1 (
         SIMP_TAC std_ss [EXTENSION, IN_DIFF, IN_SING] THEN
         METIS_TAC[]
      ) THEN
      ASM_SIMP_TAC std_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___GET_LOCKS] THEN
      METIS_TAC[]
   ],



   SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   Cases_on `l = l'` THENL [
      ASM_SIMP_TAC list_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM] THEN
      MATCH_MP_TAC ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___APPEND_MP THEN
      Q.EXISTS_TAC `0` THEN
      ASM_SIMP_TAC std_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK_THM],

      ONCE_REWRITE_TAC[GSYM ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___GET_LOCKS] THEN
      ASM_SIMP_TAC list_ss [ASL_TRACE_GET_LOCKS_def,
         FILTER_APPEND, ASL_IS_LOCK_ATOMIC_ACTION_def, IN_SING] THEN
      SIMP_TAC std_ss [GSYM ASL_TRACE_GET_LOCKS_def,
         ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___GET_LOCKS] THEN
      METIS_TAC[]
   ]
]);


val ASL_PROTO_TRACES_EVAL_PROC___STRONG_LOCK_BALANCED = store_thm ("ASL_PROTO_TRACES_EVAL_PROC___STRONG_LOCK_BALANCED",

``!penv pt t n. t IN ASL_PROTO_TRACES_EVAL_PROC n penv pt ==>
             ASL_TRACE_IS_STRONG_LOCK_BALANCED t``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_PROTO_TRACES_EVAL___STRONG_LOCK_BALANCED THEN
SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_def, IN_ABS] THEN
METIS_TAC[]);




val ASL_PROTO_TRACES_EVAL___LOCK_BALANCED = store_thm ("ASL_PROTO_TRACES_EVAL___LOCK_BALANCED",

``!penv prog t. t IN ASL_PROTO_TRACES_EVAL penv prog ==>
             ASL_TRACE_IS_LOCK_BALANCED t``,


REPEAT STRIP_TAC THEN
REWRITE_TAC [ASL_TRACE_IS_LOCK_BALANCED_def] THEN
GEN_TAC THEN
MATCH_MP_TAC ASL_TRACE_IS_STRONG_LOCK_BALANCED_LOCK___STRONG THEN
IMP_RES_TAC ASL_PROTO_TRACES_EVAL___STRONG_LOCK_BALANCED THEN
FULL_SIMP_TAC std_ss [ASL_TRACE_IS_STRONG_LOCK_BALANCED_def]);


val ASL_PROTO_TRACES_EVAL_PROC___LOCK_BALANCED = store_thm ("ASL_PROTO_TRACES_EVAL_PROC___LOCK_BALANCED",

``!penv prog n t. t IN ASL_PROTO_TRACES_EVAL_PROC n penv prog ==>
             ASL_TRACE_IS_LOCK_BALANCED t``,


REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_PROTO_TRACES_EVAL___LOCK_BALANCED THEN
SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_def, IN_ABS] THEN
METIS_TAC[]);


val ASL_TRACE_IS_LOCK_SYNCHRONISED___BALANCED_APPEND =
   store_thm ("ASL_TRACE_IS_LOCK_SYNCHRONISED___BALANCED_APPEND",

``!l t1 t2.
    ASL_TRACE_IS_LOCK_BALANCED_LOCK l t1 ==>
    (ASL_TRACE_IS_LOCK_SYNCHRONISED l (t1 ++ t2) = (ASL_TRACE_IS_LOCK_SYNCHRONISED l t1 /\ ASL_TRACE_IS_LOCK_SYNCHRONISED l t2))``,


SIMP_TAC std_ss [ASL_TRACE_IS_LOCK_BALANCED_LOCK_def,
   ASL_TRACE_IS_LOCK_SYNCHRONISED_def, LIST_STAR_def, GSYM LEFT_FORALL_IMP_THM,
   ASL_TRACE_GET_LOCKS_REWRITE] THEN
ONCE_REWRITE_TAC [GSYM LIST_ELEM_COUNT___GET_LOCKS] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE EQ_TAC THEN1 (
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `n + n'` THEN
   ASM_SIMP_TAC std_ss [LIST_NUM_STAR_APPEND]
) THEN
STRIP_TAC THEN
Q.ABBREV_TAC `tl1 = ASL_TRACE_GET_LOCKS {l} t1` THEN
Q.ABBREV_TAC `tl2 = ASL_TRACE_GET_LOCKS {l} t2` THEN
NTAC 2 (POP_ASSUM (K ALL_TAC)) THEN
REPEAT (POP_ASSUM MP_TAC) THEN
Q.SPEC_TAC (`tl2`, `tl2`) THEN
Q.SPEC_TAC (`tl1`, `tl1`) THEN
Induct_on `n` THENL [
   SIMP_TAC list_ss [LIST_NUM_STAR_def, LIST_ELEM_COUNT_THM] THEN
   Q.EXISTS_TAC `0` THEN
   SIMP_TAC std_ss [LIST_NUM_STAR_def],

   SIMP_TAC list_ss [LIST_NUM_STAR_def] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
   Cases_on `tl1 = []` THEN1 (
      FULL_SIMP_TAC list_ss [LIST_ELEM_COUNT_THM] THEN
      Q.EXISTS_TAC `SUC n` THEN
      SIMP_TAC list_ss [LIST_NUM_STAR_def]
   ) THEN
   `?tl1'. tl1 =  asl_aa_prolaag l::asl_aa_verhoog l:: tl1'` by ALL_TAC THEN1 (
      Cases_on `tl1` THEN FULL_SIMP_TAC list_ss [] THEN
      Cases_on `t` THEN FULL_SIMP_TAC list_ss [LIST_ELEM_COUNT_THM,
         asl_atomic_action_distinct]
   ) THEN
   FULL_SIMP_TAC list_ss [LIST_ELEM_COUNT_THM, asl_atomic_action_distinct] THEN
   `(?n. tl1' = LIST_NUM_STAR n [asl_aa_prolaag l; asl_aa_verhoog l]) /\
     (?n. tl2 = LIST_NUM_STAR n [asl_aa_prolaag l; asl_aa_verhoog l])` by METIS_TAC[] THEN
   ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THENL [
      Q.EXISTS_TAC `SUC n'` THEN
      SIMP_TAC list_ss [LIST_NUM_STAR_def],

      Q.EXISTS_TAC `n''` THEN
      REWRITE_TAC[]
   ]
]);


val ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___APPEND2 =
   store_thm ("ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___APPEND2",

   ``!n1 m l t1 t2.
    ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED m l (t1 ++ t2) /\
    ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n1 l t1 ==>
   ?n2. (m = n1 + n2) /\ (ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n2 l t2)``,


SIMP_TAC std_ss [ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED_def, ASL_TRACE_GET_LOCKS_REWRITE] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `ASL_TRACE_GET_LOCKS {l} t1 = X` (K ALL_TAC) THEN
POP_ASSUM MP_TAC THEN
Q.ABBREV_TAC `t3 = ASL_TRACE_GET_LOCKS {l} t2` THEN
POP_ASSUM (K ALL_TAC) THEN
Q.SPEC_TAC (`t3`, `t3`) THEN
Q.SPEC_TAC (`m`, `m`) THEN
Q.SPEC_TAC (`n2`, `n2`) THEN
Induct_on `n1` THENL [
   SIMP_TAC list_ss [LIST_NUM_STAR_def],

   Cases_on `m` THEN (
      SIMP_TAC list_ss [LIST_NUM_STAR_def, ADD_CLAUSES]
   ) THEN
   METIS_TAC[]
]);




val ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___APPEND3 =
   store_thm ("ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___APPEND3",

``!m n2 l t1 t2.
    ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED m l (t1 ++ t2) /\
    ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n2 l t2 ==>
    ?n1. (m = n1 + n2) /\ ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED n1 l t1``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC (SIMP_RULE std_ss [ASL_TRACE_IS_LOCK_SYNCHRONISED___NUM]  ASL_TRACE_IS_SYNCHRONISED___IMPLIES___LOCK_BALANCED) THEN

`ASL_TRACE_IS_LOCK_BALANCED_LOCK l t1` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [ASL_TRACE_IS_LOCK_BALANCED_LOCK_def,
      LIST_ELEM_COUNT_THM] THEN
   DECIDE_TAC
) THEN
`ASL_TRACE_IS_LOCK_SYNCHRONISED l t1` by METIS_TAC[ASL_TRACE_IS_LOCK_SYNCHRONISED___BALANCED_APPEND,
      ASL_TRACE_IS_LOCK_SYNCHRONISED___NUM] THEN
FULL_SIMP_TAC std_ss [ASL_TRACE_IS_LOCK_SYNCHRONISED___NUM] THEN
Tactical.REVERSE (`m = n + n2` by ALL_TAC) THEN1 (
   Q.EXISTS_TAC `n` THEN
   ASM_REWRITE_TAC[]
) THEN

IMP_RES_TAC ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___COUNT THEN
FULL_SIMP_TAC arith_ss [LIST_ELEM_COUNT_THM]);



val ASL_TRACE_IS_LOCK_SYNCHRONISED___APPEND =
   store_thm ("ASL_TRACE_IS_LOCK_SYNCHRONISED___APPEND",

``(!l t1 t2.
    (ASL_TRACE_IS_LOCK_SYNCHRONISED l (t1 ++ t2) /\
    ASL_TRACE_IS_LOCK_SYNCHRONISED l t1 ==>
    ASL_TRACE_IS_LOCK_SYNCHRONISED l t2)) /\
   (!l t1 t2.
   (ASL_TRACE_IS_LOCK_SYNCHRONISED l (t1 ++ t2) /\
    ASL_TRACE_IS_LOCK_SYNCHRONISED l t2 ==>
    ASL_TRACE_IS_LOCK_SYNCHRONISED l t1)) /\
   (!l t1 t2.
    (ASL_TRACE_IS_LOCK_SYNCHRONISED l t1 /\
    ASL_TRACE_IS_LOCK_SYNCHRONISED l t2) ==>
    ASL_TRACE_IS_LOCK_SYNCHRONISED l (t1++t2))``,

SIMP_TAC std_ss [ASL_TRACE_IS_LOCK_SYNCHRONISED___NUM] THEN
REPEAT STRIP_TAC THENL [
   METIS_TAC[ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___APPEND2],
   METIS_TAC[ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___APPEND3],
   METIS_TAC[ASL_TRACE_IS_NUM_LOCK_SYNCHRONISED___APPEND]
]);




(******************************************************************************)
(* Program semantic                                                           *)
(******************************************************************************)

val ASL_TRACE_SET_SEM_def = Define `
   ASL_TRACE_SET_SEM xenv ts =
   SUP_fasl_action_order (IMAGE (ASL_TRACE_SEM xenv) ts)`


val ASL_PROGRAM_SEM_def = Define `
   ASL_PROGRAM_SEM xenv penv prog =
   ASL_TRACE_SET_SEM xenv (ASL_PROGRAM_TRACES penv prog)`;

val ASL_PROGRAM_SEM_PROC_def = Define `
   ASL_PROGRAM_SEM_PROC n xenv penv prog =
   ASL_TRACE_SET_SEM xenv (ASL_PROGRAM_TRACES_PROC n penv prog)`;


val SUP_fasl_order___BIGUNION = store_thm ("SUP_fasl_order___BIGUNION",

``!M. SUP_fasl_order (BIGUNION M) =
SUP_fasl_order (IMAGE SUP_fasl_order M)``,

SIMP_TAC std_ss [SUP_fasl_order_def, IN_BIGUNION, IN_IMAGE, COND_RAND, COND_RATOR] THEN
GEN_TAC THEN
Cases_on `?s. NONE IN s /\ s IN M` THEN ASM_REWRITE_TAC[] THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
FULL_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
SIMP_TAC std_ss [SUP_fasl_order_def, COND_RAND, COND_RATOR,
   IN_BIGUNION, IN_IMAGE,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
METIS_TAC[]);


val SUP_fasl_action_order___BIGUNION = store_thm ("SUP_fasl_action_order___BIGUNION",

``!M. SUP_fasl_action_order (BIGUNION M) =
SUP_fasl_action_order (IMAGE SUP_fasl_action_order M)``,

SIMP_TAC std_ss [SUP_fasl_action_order_def,
   SUP_fasl_order___BIGUNION,
   IMAGE_BIGUNION, GSYM IMAGE_COMPOSE] THEN
Tactical.REVERSE (`!x. SUP_fasl_order o IMAGE (\f:'a -> ('b -> bool) option. f x) =
  ((\f. f x) o SUP_fasl_action_order)` by ALL_TAC) THEN1 (
   METIS_TAC[]
) THEN
SIMP_TAC std_ss [FUN_EQ_THM, SUP_fasl_action_order_def]);




val ASL_PROGRAM_SEM___PROC_THM = store_thm ("ASL_PROGRAM_SEM___PROC_THM",
``ASL_PROGRAM_SEM xenv penv prog =
   SUP_fasl_action_order (\x. ?n. x=ASL_PROGRAM_SEM_PROC n xenv penv prog)``,

SIMP_TAC std_ss [ASL_PROGRAM_SEM_def] THEN
`ASL_PROGRAM_TRACES penv prog =
  BIGUNION (\tt. ?n. tt = \t. t IN ASL_PROGRAM_TRACES_PROC n penv prog)` by ALL_TAC THEN1 (
   REWRITE_TAC[Once EXTENSION] THEN
   SIMP_TAC std_ss [ASL_PROGRAM_TRACES___PROC_THM,
      IN_ABS, IN_BIGUNION, GSYM LEFT_EXISTS_AND_THM,
      GSYM RIGHT_EXISTS_AND_THM]
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN
SIMP_TAC std_ss [IMAGE_BIGUNION, ASL_TRACE_SET_SEM_def,
   SUP_fasl_action_order___BIGUNION,
   IMAGE_ABS, ASL_PROGRAM_SEM_PROC_def,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,    IMAGE_ABS2,
   IN_ABS]);



val ASL_PROGRAM_SEM_PROC___PROTO_TRACE_SPLIT = store_thm ("ASL_PROGRAM_SEM_PROC___PROTO_TRACE_SPLIT",
``ASL_PROGRAM_SEM_PROC n xenv penv prog =
  SUP_fasl_action_order (IMAGE (\pt. ASL_PROGRAM_SEM_PROC n xenv penv {pt}) prog)``,

   SIMP_TAC std_ss [ASL_PROGRAM_SEM_PROC_def,
      ASL_TRACE_SET_SEM_def] THEN
   `ASL_PROGRAM_TRACES_PROC n penv prog =
   BIGUNION (IMAGE (\pt. ASL_PROGRAM_TRACES_PROC n penv {pt}) prog)` by ALL_TAC THEN1 (
      REWRITE_TAC[Once EXTENSION] THEN
      SIMP_TAC std_ss [ASL_PROGRAM_TRACES_PROC_def,
         IN_ABS, IN_BIGUNION, GSYM LEFT_EXISTS_AND_THM,
         GSYM RIGHT_EXISTS_AND_THM, IN_IMAGE, IN_SING]
   ) THEN
   ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

   SIMP_TAC std_ss [IMAGE_BIGUNION, SUP_fasl_action_order___BIGUNION,
      GSYM IMAGE_COMPOSE, combinTheory.o_DEF]
);


val ASL_PROGRAM_SEM_PROC___fasl_action_order =
store_thm ("ASL_PROGRAM_SEM_PROC___fasl_action_order",
``!n m xenv penv prog.  n <= m ==>
   fasl_action_order
   (ASL_PROGRAM_SEM_PROC n xenv penv prog)
   (ASL_PROGRAM_SEM_PROC m xenv penv prog)``,

SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF,
   ASL_PROGRAM_SEM_PROC_def, ASL_TRACE_SET_SEM_def, SUP_fasl_action_order_def,
   SUP_fasl_order_def] THEN
REPEAT STRIP_TAC THEN
Q.ABBREV_TAC `x1 = IMAGE (\f. f s)
  (IMAGE (ASL_TRACE_SEM xenv) (ASL_PROGRAM_TRACES_PROC n penv prog))` THEN
Q.ABBREV_TAC `x2 = IMAGE (\f. f s)
  (IMAGE (ASL_TRACE_SEM xenv) (ASL_PROGRAM_TRACES_PROC m penv prog))` THEN
Tactical.REVERSE (`x1 SUBSET x2` by ALL_TAC) THEN1 (
   Cases_on `NONE IN x1` THEN1 (
      FULL_SIMP_TAC std_ss [SUBSET_DEF, fasl_order_THM]
   ) THEN
   FULL_SIMP_TAC std_ss [fasl_order_THM2, COND_RAND, COND_RATOR,
      SUBSET_DEF, IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
   METIS_TAC[]
) THEN
Q.UNABBREV_TAC `x1` THEN Q.UNABBREV_TAC `x2` THEN
MATCH_MP_TAC IMAGE_SUBSET THEN
MATCH_MP_TAC IMAGE_SUBSET THEN
MATCH_MP_TAC ASL_PROGRAM_TRACES_PROC_SUBSET THEN
ASM_REWRITE_TAC[]);


val ASL_IS_EQUIV_PENV_PROC_def = Define `
   ASL_IS_EQUIV_PENV_PROC m penv penv' =
   (((FDOM penv) = (FDOM penv')) /\
   (!proc. proc IN (FDOM penv) ==>
   (!arg. (ASL_PROGRAM_TRACES_PROC m penv (asl_prog_procedure_call proc arg)) =
      (ASL_PROGRAM_TRACES_PROC m penv' (asl_prog_procedure_call proc arg)))))`


val ASL_IS_EQUIV_PENV_PROC___ZERO = store_thm ("ASL_IS_EQUIV_PENV_PROC___ZERO",
   ``ASL_IS_EQUIV_PENV_PROC 0 penv penv' =
   ((FDOM penv) = (FDOM penv'))``,

SIMP_TAC std_ss [ASL_IS_EQUIV_PENV_PROC_def,
   ASL_PROGRAM_TRACES_PROC_IN_THM, EXTENSION,
   IN_ABS, asl_prog_procedure_call_def, IN_SING,
   ASL_PROTO_TRACES_EVAL_PROC_IN_THM] THEN
METIS_TAC[]);

val ASL_PROTO_TRACES_EVAL_PROC___EQUIV_PENV_PROC = store_thm ("ASL_PROTO_TRACES_EVAL_PROC___EQUIV_PENV_PROC",
``!penv penv' pt m.
ASL_IS_EQUIV_PENV_PROC m penv penv' ==>

((ASL_PROTO_TRACES_EVAL_PROC m penv pt) =
(ASL_PROTO_TRACES_EVAL_PROC m penv' pt))``,


REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC [EXTENSION] THEN
Induct_on `pt` THEN (
   ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM]
) THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [ASL_IS_EQUIV_PENV_PROC_def] THEN
Cases_on `n IN FDOM penv` THENL [
   RES_TAC THEN
   FULL_SIMP_TAC std_ss [ASL_PROGRAM_TRACES_PROC_IN_THM2,
      asl_prog_procedure_call_def, IN_SING] THEN
   FULL_SIMP_TAC std_ss [EXTENSION, IN_ABS],

   `~(n IN FDOM penv')` by METIS_TAC[] THEN
   Cases_on `m` THEN
   ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM]
]);



val ASL_PROGRAM_SEM_PROC___EQUIV_PENV_PROC = store_thm ("ASL_PROGRAM_SEM_PROC___EQUIV_PENV_PROC",
``!penv penv' xenv prog m.

ASL_IS_EQUIV_PENV_PROC m penv penv' ==>
((ASL_PROGRAM_SEM_PROC m xenv penv prog) =
(ASL_PROGRAM_SEM_PROC m xenv penv' prog))``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [ASL_PROGRAM_SEM_PROC_def,
   ASL_PROGRAM_TRACES_PROC_IN_THM2] THEN
METIS_TAC[ASL_PROTO_TRACES_EVAL_PROC___EQUIV_PENV_PROC]);


val ASL_IS_EQUIV_PENV_PROC___equivalence = store_thm ("ASL_IS_EQUIV_PENV_PROC___equivalence",
   ``equivalence (ASL_IS_EQUIV_PENV_PROC n)``,

SIMP_TAC std_ss [equivalence_def, reflexive_def, ASL_IS_EQUIV_PENV_PROC_def,
   symmetric_def, transitive_def] THEN
METIS_TAC[]);



val ASL_IS_LOCAL_ACTION___ASL_TRACE_SET_SEM = store_thm ("ASL_IS_LOCAL_ACTION___ASL_TRACE_SET_SEM",
``!xenv ts.
IS_SEPARATION_COMBINATOR (FST xenv) ==>
ASL_IS_LOCAL_ACTION (FST xenv) (ASL_TRACE_SET_SEM xenv ts)``,

Cases_on `xenv` THEN
SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM,
   ASL_TRACE_SET_SEM_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC SUP_fasl_action_order_LOCAL THEN

SIMP_TAC std_ss [IN_IMAGE, GSYM LEFT_FORALL_IMP_THM] THEN
METIS_TAC[ASL_IS_LOCAL_ACTION___ASL_TRACE_SEM]);




val ASL_IS_LOCAL_ACTION___ASL_PROGRAM_SEM = store_thm ("ASL_IS_LOCAL_ACTION___ASL_PROGRAM_SEM",
``!xenv penv prog.
IS_SEPARATION_COMBINATOR (FST xenv) ==>

ASL_IS_LOCAL_ACTION (FST xenv)
   (ASL_PROGRAM_SEM xenv penv prog)``,

SIMP_TAC std_ss [ASL_PROGRAM_SEM_def,
   ASL_IS_LOCAL_ACTION___ASL_TRACE_SET_SEM]);




val ASL_PROGRAM_SEM___prim_command = store_thm (
"ASL_PROGRAM_SEM___prim_command",
``ASL_PROGRAM_SEM xenv penv (asl_prog_prim_command pc) =
  ASL_ATOMIC_ACTION_SEM xenv (asl_aa_pc pc)``,

ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC list_ss [ASL_PROGRAM_SEM_def, ASL_PROGRAM_TRACES_THM,
       ASL_TRACE_SET_SEM_def, SUP_fasl_action_order_def,
       SUP_fasl_order_def,
       ASL_TRACE_SEM_def, asla_big_seq_def,
       asla_seq_skip, IN_SING,
       IMAGE_DEF, GSPECIFICATION,
       BIGUNION] THEN
GEN_TAC THEN
Cases_on `ASL_ATOMIC_ACTION_SEM xenv (asl_aa_pc pc) x` THEN1 REWRITE_TAC[] THEN
SIMP_TAC std_ss [EXTENSION, GSPECIFICATION]);


val ASL_PROGRAM_SEM___fail = store_thm (
"ASL_PROGRAM_SEM___fail",
``ASL_PROGRAM_SEM xenv penv (asl_prog_fail) =
  asla_fail``,

Cases_on `xenv` THEN
SIMP_TAC std_ss [asl_prog_fail_def, ASL_PROGRAM_SEM___prim_command,
       ASL_ATOMIC_ACTION_SEM_def, EVAL_asl_prim_command_THM]);



val ASL_PROGRAM_SEM___skip = store_thm (
"ASL_PROGRAM_SEM___skip",
``ASL_PROGRAM_SEM xenv penv (asl_prog_skip) =
  asla_skip``,

Cases_on `xenv` THEN
SIMP_TAC std_ss [asl_prog_skip_def, ASL_PROGRAM_SEM___prim_command,
       ASL_ATOMIC_ACTION_SEM_def, EVAL_asl_prim_command_THM]);


val ASL_PROGRAM_SEM___diverge = store_thm (
"ASL_PROGRAM_SEM___diverge",
``ASL_PROGRAM_SEM xenv penv (asl_prog_diverge) =
  asla_diverge``,

Cases_on `xenv` THEN
SIMP_TAC std_ss [asl_prog_diverge_def, ASL_PROGRAM_SEM___prim_command,
       ASL_ATOMIC_ACTION_SEM_def, EVAL_asl_prim_command_THM]);



val ASL_PROGRAM_SEM___assume = store_thm (
"ASL_PROGRAM_SEM___assume",
``!xenv penv P.
  IS_SEPARATION_COMBINATOR (FST xenv) ==>
  (ASL_PROGRAM_SEM xenv penv (asl_prog_assume P) =
   asla_assume (FST xenv) (EVAL_asl_predicate (FST xenv) P))``,

Cases_on `xenv` THEN
SIMP_TAC std_ss [asl_prog_assume_def,
   ASL_PROGRAM_SEM___prim_command, ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM]);


val ASL_PROGRAM_SEM___assert = store_thm (
"ASL_PROGRAM_SEM___assert",
``!xenv penv P.
  IS_SEPARATION_COMBINATOR (FST xenv) ==>
  (ASL_PROGRAM_SEM xenv penv (asl_prog_assert P) =
   asla_assert (FST xenv) (EVAL_asl_predicate (FST xenv) P))``,

Cases_on `xenv` THEN
SIMP_TAC std_ss [asl_prog_assert_def,
   ASL_PROGRAM_SEM___prim_command, ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM]);


val ASL_PROGRAM_SEM___prog_quant_best_local_action = store_thm (
"ASL_PROGRAM_SEM___prog_quant_best_local_action",
``!xenv penv qP qQ.
   IS_SEPARATION_COMBINATOR (FST xenv) ==>
   (ASL_PROGRAM_SEM xenv penv (asl_prog_quant_best_local_action qP qQ) =
    (quant_best_local_action (FST xenv) qP qQ))``,

Cases_on `xenv` THEN
SIMP_TAC std_ss [asl_prog_quant_best_local_action_def,
   ASL_PROGRAM_SEM___prim_command,
   ASL_ATOMIC_ACTION_SEM_def, EVAL_asl_prim_command_THM,
   quant_best_local_action_THM]);


val ASL_PROGRAM_SEM___prog_seq = store_thm ("ASL_PROGRAM_SEM___prog_seq",
``!xenv penv prog1 prog2.
(ASL_PROGRAM_SEM xenv penv (asl_prog_seq prog1 prog2) =
asla_seq (ASL_PROGRAM_SEM xenv penv prog1) (ASL_PROGRAM_SEM xenv penv prog2))``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [ASL_PROGRAM_SEM_def, ASL_TRACE_SET_SEM_def,
       SUP_fasl_action_order_def, asla_seq_def,
       SUP_fasl_order_def,
       COND_NONE_SOME_REWRITES,
       GSYM IMAGE_COMPOSE, combinTheory.o_DEF] THEN
ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [] THEN
Cases_on `NONE IN
       IMAGE (\x'. ASL_TRACE_SEM xenv x' x)
    (ASL_PROGRAM_TRACES penv (asl_prog_seq prog1 prog2))` THENL [

   ASM_SIMP_TAC std_ss [COND_NONE_SOME_REWRITES] THEN
   MATCH_MP_TAC (prove (``(~A ==> B) ==> (A \/ B)``, PROVE_TAC[])) THEN
   STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [IN_IMAGE, ASL_PROGRAM_TRACES_IN_THM,
          IN_BIGUNION, GSYM RIGHT_EXISTS_AND_THM,
          ASL_TRACE_SEM_APPEND] THEN
   SIMP_TAC std_ss [COND_RATOR, COND_RAND] THEN
   Cases_on `xenv` THEN
   `?X. ASL_TRACE_SEM (q,r) t1 x = SOME X` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `t2 IN X` (K ALL_TAC) THEN
      FULL_SIMP_TAC std_ss [IN_INSERT, ASL_TRACE_SEM_diverge,
             asla_diverge_def] THEN
      Cases_on `ASL_TRACE_SEM (q,r) t1 x` THENL [
     METIS_TAC[],
     SIMP_TAC std_ss []
      ]
   ) THEN
   FULL_SIMP_TAC std_ss [asla_seq_def, SUP_fasl_order_def,
          COND_NONE_SOME_REWRITES] THEN
   FULL_SIMP_TAC std_ss [IN_IMAGE] THEN
   Q.EXISTS_TAC `x'` THEN
   Q.EXISTS_TAC `t1` THEN
   Cases_on `t1 = [asl_aa_diverge]` THEN1 (
      FULL_SIMP_TAC std_ss [ASL_TRACE_SEM_diverge, asla_diverge_def] THEN
      METIS_TAC[NOT_IN_EMPTY]
   ) THEN
   Cases_on `t2 = [asl_aa_diverge]` THEN1 (
      FULL_SIMP_TAC std_ss [ASL_TRACE_SEM_diverge, asla_diverge_def]
   ) THEN
   FULL_SIMP_TAC std_ss [IN_INSERT] THEN
   Q.EXISTS_TAC `t2` THEN
   ASM_REWRITE_TAC[],




   ASM_SIMP_TAC std_ss [COND_NONE_SOME_REWRITES, EXTENSION] THEN
   FULL_SIMP_TAC std_ss [IN_IMAGE, COND_NONE_SOME_REWRITES,
          IN_BIGUNION, GSYM RIGHT_FORALL_OR_THM,
          ASL_PROGRAM_TRACES_IN_THM,
          IN_INSERT, GSYM RIGHT_EXISTS_AND_THM,
          LEFT_OR_OVER_AND,
          RIGHT_OR_OVER_AND,
          FORALL_AND_THM,
          ASL_TRACE_SEM_APPEND,
          ASL_TRACE_SEM_diverge,
          asla_seq_diverge] THEN
   FULL_SIMP_TAC std_ss [asla_diverge_def, asla_seq_def,
          COND_NONE_SOME_REWRITES, SUP_fasl_order_def,
          IN_IMAGE] THEN
   REPEAT STRIP_TAC THENL [
      METIS_TAC[],
      METIS_TAC[],


      EQ_TAC THENL [
    STRIP_TAC THEN
    Cases_on `ASL_TRACE_SEM xenv x''' x` THEN1 METIS_TAC[] THEN
    FULL_SIMP_TAC std_ss [] THEN
    Q.PAT_ASSUM `x' IN THE Y` MP_TAC THEN
    `~?x'''.
       (NONE = ASL_TRACE_SEM xenv x''' x'') /\
       x''' IN ASL_PROGRAM_TRACES penv prog2` by METIS_TAC[optionTheory.option_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    FULL_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
    STRIP_TAC THEN
    Q.EXISTS_TAC `x'''` THEN
    Q.EXISTS_TAC `x'''''` THEN
    ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR, IN_BIGUNION, IN_IMAGE,
               GSYM RIGHT_EXISTS_AND_THM] THEN
    METIS_TAC[optionTheory.option_CLAUSES],





    SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN
    Cases_on `t1 = [asl_aa_diverge]` THEN1 (
       ASM_SIMP_TAC std_ss [ASL_TRACE_SEM_diverge, asla_diverge_def,
             NOT_IN_EMPTY, IMAGE_EMPTY, BIGUNION_EMPTY]
    ) THEN
    Cases_on `t2 = [asl_aa_diverge]` THEN1 (
       ASM_SIMP_TAC std_ss [ASL_TRACE_SEM_diverge, asla_diverge_def,
             GSYM IMAGE_COMPOSE, combinTheory.o_DEF,
             COND_RATOR, COND_RAND, IN_BIGUNION,
             IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
             NOT_IN_EMPTY] THEN
       METIS_TAC[]
    ) THEN
    HO_MATCH_MP_TAC (
    prove (``(C /\ D ==> ~CC) /\ (((x IN THE B) /\ C /\ D) ==> E) ==>
    ((x IN THE (if CC then A else B) /\ C /\ D) ==> E)``, METIS_TAC[])) THEN
    CONJ_TAC THEN1 METIS_TAC[] THEN

    ASM_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
    REPEAT STRIP_TAC THEN
    Q.EXISTS_TAC `x''` THEN
    Q.EXISTS_TAC `t1` THEN
    ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR, IN_BIGUNION, IN_IMAGE,
               GSYM RIGHT_EXISTS_AND_THM] THEN
    METIS_TAC[]
     ]
   ]
]);


val ASL_PROGRAM_SEM___asl_prog_critical_section =
store_thm ("ASL_PROGRAM_SEM___asl_prog_critical_section",
``!f lock_env penv l prog.
  IS_SEPARATION_COMBINATOR f ==>
(
ASL_PROGRAM_SEM (f,lock_env) penv (asl_prog_critical_section l prog) =
ASL_PROGRAM_SEM (f,lock_env) penv (asl_prog_block [
   asl_prog_prim_command (asl_pc_shallow_command (\f. asla_materialisation f (lock_env l)));
   prog;
   asl_prog_prim_command (asl_pc_shallow_command (\f. asla_annihilation f (lock_env l)))]))``,


SIMP_TAC std_ss [asl_prog_block_def, ASL_PROGRAM_SEM___prog_seq] THEN
SIMP_TAC std_ss [asl_prog_critical_section_def, ASL_PROGRAM_SEM_def, ASL_TRACE_SET_SEM_def] THEN
SIMP_TAC std_ss [IMAGE_ABS, ASL_PROGRAM_TRACES_def,
   IN_BIGUNION, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, asl_prog_prim_command_def,
   ASL_PROTO_TRACES_EVAL_IN_THM, IN_SING, IN_ABS_SING,
   IN_INSERT, IN_ABS, ASL_TRACE_SEM_APPEND] THEN
REPEAT STRIP_TAC THEN
Q.MATCH_ABBREV_TAC
   `SUP_fasl_action_order M1 =
    asla_seq (SUP_fasl_action_order M2)
      (asla_seq (SUP_fasl_action_order M3)
       (SUP_fasl_action_order M4))` THEN
`~(M4 = EMPTY)` by PROVE_TAC [NOT_EMPTY_SING] THEN
`(M3 = EMPTY) = (M1 = EMPTY)` by ALL_TAC THEN1 (
   Q.UNABBREV_TAC `M1` THEN Q.UNABBREV_TAC `M3` THEN
   SIMP_TAC std_ss [EXTENSION] THEN
   SIMP_TAC std_ss [IN_ABS, NOT_IN_EMPTY] THEN
   PROVE_TAC[]
) THEN
Cases_on `(M3 = EMPTY)` THEN1 (
   FULL_SIMP_TAC std_ss [SUP_fasl_action_order___EMPTY, asla_seq_diverge,
          asla_seq_diverge_2, IS_SOME___SUP_fasl_action_order] THEN
   Q.UNABBREV_TAC `M2` THEN
   ASM_SIMP_TAC std_ss [ASL_TRACE_SEM_REWRITE, asla_seq_skip, IN_SING,
         ASL_ATOMIC_ACTION_SEM_def, EVAL_asl_prim_command_THM,
         asla_materialisation_THM, COND_RAND, COND_RATOR,
         asla_fail_def, ASL_IS_LOCAL_ACTION___materialisation_annihilation]
) THEN
`~((\a. ?a1 a2. a1 IN M3 /\ a2 IN M4 /\ (a = asla_seq a1 a2)) = EMPTY)` by ALL_TAC THEN1 (
   SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_ABS] THEN
   ASM_SIMP_TAC std_ss [pred_setTheory.MEMBER_NOT_EMPTY,
         LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM]
) THEN
ASM_SIMP_TAC std_ss [asla_seq___SUP_fasl_action_order] THEN
NTAC 3 (POP_ASSUM (K ALL_TAC)) THEN
AP_TERM_TAC THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
Q.UNABBREV_TAC `M1` THEN Q.UNABBREV_TAC `M2` THEN
Q.UNABBREV_TAC `M3` THEN Q.UNABBREV_TAC `M4` THEN
ASM_SIMP_TAC std_ss [IN_ABS, IN_SING, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, ASL_TRACE_SEM_REWRITE, asla_seq_skip,
   ASL_ATOMIC_ACTION_SEM_def, EVAL_asl_prim_command_THM,
   asla_annihilation_def, asla_materialisation_def,
   best_local_action_THM, REWRITE_RULE [ASSOC_DEF] asla_seq___ASSOC] THEN
METIS_TAC[]);



val ASL_PROGRAM_SEM___prog_block = store_thm ("ASL_PROGRAM_SEM___prog_block",
``(ASL_PROGRAM_SEM xenv penv (asl_prog_block []) = asla_skip) /\
  (ASL_PROGRAM_SEM xenv penv (asl_prog_block (h::L)) =
   asla_seq (ASL_PROGRAM_SEM xenv penv h) (ASL_PROGRAM_SEM xenv penv (asl_prog_block L)))``,


Cases_on `L` THEN
SIMP_TAC std_ss [asl_prog_block_def, ASL_PROGRAM_SEM___skip,
       asla_seq_skip,
       ASL_PROGRAM_SEM___prog_seq]);



val ASL_PROGRAM_SEM___prog_seq___blocks =
store_thm ("ASL_PROGRAM_SEM___prog_seq___blocks",
``
ASL_PROGRAM_SEM xenv penv (asl_prog_seq (asl_prog_block b1) (asl_prog_block b2)) =
ASL_PROGRAM_SEM xenv penv (asl_prog_block (b1++b2))
``,

Induct_on `b1` THENL [
   SIMP_TAC list_ss [ASL_PROGRAM_SEM___prog_seq,
          asl_prog_block_def,
          ASL_PROGRAM_SEM___skip,
          asla_seq_skip],

   ASSUME_TAC asla_seq___ASSOC THEN
   FULL_SIMP_TAC list_ss [ASL_PROGRAM_SEM___prog_block,
           ASL_PROGRAM_SEM___prog_seq,
           ASSOC_SYM]
]);



val ASL_PROGRAM_SEM___prog_block_append =
store_thm ("ASL_PROGRAM_SEM___prog_block_append",
``!xenv penv L1 L2.
  ASL_PROGRAM_SEM xenv penv (asl_prog_block (L1++L2)) =
  asla_seq
     (ASL_PROGRAM_SEM xenv penv (asl_prog_block L1))
     (ASL_PROGRAM_SEM xenv penv (asl_prog_block L2))``,
Induct_on `L1` THEN1 (
   SIMP_TAC list_ss [ASL_PROGRAM_SEM___prog_block, asla_seq_skip]
) THEN
ASM_SIMP_TAC list_ss [ASL_PROGRAM_SEM___prog_block,
  REWRITE_RULE [ASSOC_DEF] asla_seq___ASSOC]);



val ASL_PROGRAM_SEM___block_flatten =
store_thm ("ASL_PROGRAM_SEM___block_flatten",
``!xenv penv L1 L2 L3.
  ASL_PROGRAM_SEM xenv penv (asl_prog_block (L1++(asl_prog_block L2::L3))) =
  ASL_PROGRAM_SEM xenv penv (asl_prog_block (L1++L2++L3))``,
SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_block_append,
   ASL_PROGRAM_SEM___prog_block,
   REWRITE_RULE [ASSOC_DEF] asla_seq___ASSOC]);




val ASL_PROGRAM_SEM___prog_ndet = store_thm ("ASL_PROGRAM_SEM___prog_ndet",
``!xenv penv pset.
ASL_PROGRAM_SEM xenv penv (asl_prog_ndet pset) =
SUP_fasl_action_order (IMAGE (\p. ASL_PROGRAM_SEM xenv penv p) pset)``,

SIMP_TAC std_ss [ASL_PROGRAM_SEM_def, ASL_PROGRAM_TRACES___prog_ndet,
       ASL_TRACE_SET_SEM_def, SUP_fasl_action_order___BIGUNION,
       IMAGE_BIGUNION, GSYM IMAGE_COMPOSE,
       combinTheory.o_DEF]);


val ASL_PROGRAM_SEM___prog_forall = store_thm ("ASL_PROGRAM_SEM___prog_forall",
``ASL_PROGRAM_SEM xenv penv (asl_prog_forall M) =
  SUP_fasl_action_order (IMAGE (\p. ASL_PROGRAM_SEM xenv penv p) (IMAGE M UNIV))``,

SIMP_TAC std_ss [asl_prog_forall_def, GSYM asl_prog_ndet_def,
   ASL_PROGRAM_SEM___prog_ndet]);





val ASL_PROGRAM_SEM___prog_choice = store_thm ("ASL_PROGRAM_SEM___prog_choice",
``ASL_PROGRAM_SEM xenv penv (asl_prog_choice p1 p2) =
  asla_bin_choice (ASL_PROGRAM_SEM xenv penv p1) (ASL_PROGRAM_SEM xenv penv p2)``,

SIMP_TAC std_ss [ASL_PROGRAM_SEM_def, ASL_PROGRAM_TRACES_THM,
       asla_bin_choice_def, ASL_TRACE_SET_SEM_def,
       asla_choice_def, IMAGE_UNION] THEN
SIMP_TAC std_ss [prove (``A UNION B = BIGUNION {A;B}``,
         SIMP_TAC std_ss [Once EXTENSION, IN_UNION, IN_BIGUNION,
                IN_INSERT, NOT_IN_EMPTY] THEN
         METIS_TAC[])] THEN
SIMP_TAC std_ss [SUP_fasl_action_order___BIGUNION, IMAGE_INSERT,
       IMAGE_EMPTY]);




val ASL_PROGRAM_SEM___prog_repeat = store_thm (
"ASL_PROGRAM_SEM___prog_repeat",
``
(ASL_PROGRAM_SEM xenv penv (asl_prog_repeat_num 0 prog) = asla_skip) /\
(ASL_PROGRAM_SEM xenv penv (asl_prog_repeat_num (SUC n) prog) =
   asla_seq (ASL_PROGRAM_SEM xenv penv prog)
        (ASL_PROGRAM_SEM xenv penv (asl_prog_repeat_num n prog)))``,

SIMP_TAC std_ss [asl_prog_repeat_num_def, ASL_PROGRAM_SEM___skip] THEN
SIMP_TAC std_ss [ASL_PROGRAM_SEM_def, ASL_TRACE_SET_SEM_def] THEN
Cases_on `ASL_PROGRAM_TRACES penv prog = EMPTY` THEN1 (
   Q.MATCH_ABBREV_TAC `
       SUP_fasl_action_order (IMAGE (ASL_TRACE_SEM xenv) pt1) =
       asla_seq (SUP_fasl_action_order (IMAGE (ASL_TRACE_SEM xenv) pt2)) a` THEN
   Tactical.REVERSE (`pt1 = EMPTY` by ALL_TAC) THEN1 (
      ASM_SIMP_TAC std_ss [IMAGE_EMPTY,
    SUP_fasl_action_order___EMPTY, asla_seq_diverge]
   ) THEN
   UNABBREV_ALL_TAC THEN
   FULL_SIMP_TAC std_ss [ASL_PROGRAM_TRACES___EQ_EMPTY, IN_ABS,
      GSYM LEFT_FORALL_IMP_THM,
      ASL_PROTO_TRACES_EVAL_THM, NOT_IN_EMPTY] THEN
   SIMP_TAC std_ss [GSYM EMPTY_DEF]
) THEN

Q.MATCH_ABBREV_TAC `SUP_fasl_action_order A1 =
   asla_seq (SUP_fasl_action_order A2) (SUP_fasl_action_order A3)` THEN
`~(A3 = EMPTY)` by ALL_TAC THEN1 (

    UNABBREV_ALL_TAC THEN
    SIMP_TAC std_ss [IMAGE_EQ_EMPTY] THEN
    Induct_on `n` THEN1 (
       SIMP_TAC std_ss [asl_prog_repeat_num_def,
     asl_prog_skip_def, ASL_PROGRAM_TRACES_THM,
     NOT_EMPTY_INSERT]
    ) THEN
    FULL_SIMP_TAC std_ss [asl_prog_repeat_num_def,
       ASL_PROGRAM_TRACES___EQ_EMPTY, IN_ABS,
       GSYM LEFT_EXISTS_AND_THM] THEN
    Q.EXISTS_TAC `pt` THEN Q.EXISTS_TAC `pt'` THEN
    FULL_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_THM,
       EXTENSION, NOT_IN_EMPTY, IN_ABS] THEN
    METIS_TAC[]
) THEN

ASM_SIMP_TAC std_ss [asla_seq___SUP_fasl_action_order] THEN
AP_TERM_TAC THEN
ONCE_REWRITE_TAC[EXTENSION] THEN
UNABBREV_ALL_TAC THEN
SIMP_TAC std_ss [IN_ABS, ASL_PROGRAM_TRACES_def,
   IN_IMAGE, IN_BIGUNION, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM,
   GSYM RIGHT_EXISTS_AND_THM, ASL_PROTO_TRACES_EVAL_IN_THM,
   ASL_TRACE_SEM_APPEND] THEN
METIS_TAC[]);


val ASL_PROGRAM_SEM___prog_repeat___asla_repeat = store_thm (
"ASL_PROGRAM_SEM___prog_repeat___asla_repeat",
``!xenv penv n prog.
  ASL_PROGRAM_SEM xenv penv (asl_prog_repeat_num n prog) =
  asla_repeat (ASL_PROGRAM_SEM xenv penv prog) n``,
Induct_on `n` THEN (
   ASM_SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_repeat,
       asla_repeat_def]
));




val ASL_PROGRAM_SEM___prog_kleene_star = store_thm ("ASL_PROGRAM_SEM___prog_kleene_star",
``
ASL_PROGRAM_SEM xenv penv (asl_prog_kleene_star prog) =
SUP_fasl_action_order (IMAGE (\n. ASL_PROGRAM_SEM xenv penv (asl_prog_repeat_num n prog)) UNIV)``,

ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC std_ss [ASL_PROGRAM_SEM_def,
       ASL_TRACE_SET_SEM_def, asl_prog_kleene_star_def,
       SUP_fasl_action_order_def, SUP_fasl_order_def,
       COND_NONE_SOME_REWRITES_EQ, IN_IMAGE, IN_UNIV,
       GSYM RIGHT_EXISTS_AND_THM,
       COND_NONE_SOME_REWRITES] THEN
REPEAT STRIP_TAC THENL [
   SIMP_TAC std_ss [ASL_PROGRAM_TRACES_def, IN_BIGUNION,
          IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
          IN_ABS] THEN
   METIS_TAC[],


   ONCE_REWRITE_TAC[EXTENSION] THEN
   SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_ABS,
          GSYM RIGHT_EXISTS_AND_THM,
          GSYM LEFT_EXISTS_AND_THM, IN_UNIV] THEN
   `!n. ~?x'. (NONE = ASL_TRACE_SEM xenv x' x) /\
          x' IN ASL_PROGRAM_TRACES penv (asl_prog_repeat_num n prog)` by
      METIS_TAC[] THEN
   ASM_REWRITE_TAC[] THEN (POP_ASSUM (K ALL_TAC)) THEN

   SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, IN_ABS,
          GSYM RIGHT_EXISTS_AND_THM,
          GSYM LEFT_EXISTS_AND_THM,
          ASL_PROGRAM_TRACES_def] THEN
   METIS_TAC[]
]);


val ASL_PROGRAM_SEM___prog_kleene_star___asla_kleene_star = store_thm ("ASL_PROGRAM_SEM___prog_kleene_star___asla_kleene_star",
``ASL_PROGRAM_SEM xenv penv (asl_prog_kleene_star prog) =
  asla_kleene_star (ASL_PROGRAM_SEM xenv penv prog)``,

SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_kleene_star,
   asla_kleene_star_def, ASL_PROGRAM_SEM___prog_repeat___asla_repeat] THEN
AP_TERM_TAC THEN
SIMP_TAC std_ss [EXTENSION, IN_IMAGE, IN_UNIV, GSPECIFICATION]);


val ASL_PROGRAM_SEM___prog_assume___neg_true = store_thm (
"ASL_PROGRAM_SEM___prog_assume___neg_true",
``!xenv penv. IS_SEPARATION_COMBINATOR (FST xenv) ==> (
  ASL_PROGRAM_SEM xenv penv
    (asl_prog_assume (asl_pred_neg asl_pred_true)) = asla_diverge)``,
SIMP_TAC std_ss [ASL_PROGRAM_SEM___assume,
   EVAL_asl_predicate_def,
   ASL_IS_INTUITIONISTIC___TRUE_FALSE,
   asla_assume_def, asl_bool_EVAL,
   asla_diverge_def]);


val ASL_PROGRAM_SEM___prog_assume___neg_false = store_thm (
"ASL_PROGRAM_SEM___prog_assume___neg_false",
``!xenv penv. IS_SEPARATION_COMBINATOR (FST xenv) ==> (
  ASL_PROGRAM_SEM xenv penv
    (asl_prog_assume (asl_pred_neg asl_pred_false)) = asla_skip)``,
SIMP_TAC std_ss [ASL_PROGRAM_SEM___assume,
   EVAL_asl_predicate_def,
   ASL_IS_INTUITIONISTIC___TRUE_FALSE,
   asla_assume_def, asl_bool_EVAL,
   asla_skip_def]);



val ASL_PROGRAM_SEM___asl_prog_cond_critical_section = store_thm (
"ASL_PROGRAM_SEM___asl_prog_cond_critical_section",
``!xenv penv l c prog.
IS_SEPARATION_COMBINATOR (FST xenv) ==>
(ASL_PROGRAM_SEM xenv penv
   (asl_prog_cond_critical_section l c prog) =
 ASL_PROGRAM_SEM xenv penv
   (asl_prog_block
    [asl_prog_aquire_lock c ((SND xenv) l);
     prog;
     asl_prog_release_lock ((SND xenv) l)]))``,

REPEAT STRIP_TAC THEN
`?f lock_env. xenv = (f, lock_env)` by (Cases_on `xenv` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC std_ss [asl_prog_cond_critical_section_def,
            ASL_PROGRAM_SEM___asl_prog_critical_section,
            asl_prog_aquire_lock_def, asl_prog_release_lock_def,
            asl_prog_block_def, ASL_PROGRAM_SEM___prog_seq,
            REWRITE_RULE [ASSOC_DEF] asla_seq___ASSOC]);




val ASL_PROGRAM_SEM___prog_seq___prog_cond =
store_thm ("ASL_PROGRAM_SEM___prog_seq___prog_cond",
``
(ASL_PROGRAM_SEM xenv penv
      (asl_prog_seq (asl_prog_cond c pT pF) prog))
=
(ASL_PROGRAM_SEM xenv penv
      (asl_prog_cond c (asl_prog_seq pT prog) (asl_prog_seq pF prog)))``,



SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_seq,
       asl_prog_cond_def,
       ASL_PROGRAM_SEM___prog_choice] THEN

ASSUME_TAC asla_seq___ASSOC THEN
FULL_SIMP_TAC std_ss [ASSOC_DEF] THEN

Q.ABBREV_TAC `a1 = (asla_seq
       (ASL_PROGRAM_SEM xenv penv
          (asl_prog_prim_command (asl_pc_assume c)))
       (ASL_PROGRAM_SEM xenv penv pT))` THEN
Q.ABBREV_TAC `a2 = (asla_seq
       (ASL_PROGRAM_SEM xenv penv
          (asl_prog_prim_command (asl_pc_assume (asl_pred_neg c))))
       (ASL_PROGRAM_SEM xenv penv pF))` THEN
Q.ABBREV_TAC `a3 = (ASL_PROGRAM_SEM xenv penv prog)` THEN


SIMP_TAC std_ss [asla_seq_def, asla_bin_choice_def,
       asla_choice_def,
       SUP_fasl_action_order_def,
       SUP_fasl_order_def,
       IN_IMAGE, IN_INSERT, NOT_IN_EMPTY,
       EXISTS_OR_THM,
       RIGHT_AND_OVER_OR,
       LEFT_AND_OVER_OR,
       COND_NONE_SOME_REWRITES] THEN
ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
GEN_TAC THEN
Cases_on `a1 x` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `a2 x` THEN ASM_SIMP_TAC std_ss [] THEN

SIMP_TAC std_ss [COND_NONE_SOME_REWRITES_EQ] THEN
REPEAT STRIP_TAC THENL [
   ASM_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE,
          GSYM RIGHT_EXISTS_AND_THM,
          IN_INSERT, NOT_IN_EMPTY,
          RIGHT_AND_OVER_OR,
          LEFT_AND_OVER_OR, EXISTS_OR_THM],


   ONCE_REWRITE_TAC[EXTENSION] THEN
   ASM_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE,
          GSYM LEFT_EXISTS_AND_THM,
          IN_INSERT, NOT_IN_EMPTY,
          RIGHT_AND_OVER_OR,
          LEFT_AND_OVER_OR, EXISTS_OR_THM,
          GSYM RIGHT_EXISTS_AND_THM] THEN
   ONCE_REWRITE_TAC [
      prove (``(if c then p else q) = (if ~c then q else p)``, METIS_TAC[])] THEN
   ASM_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE,
         GSYM RIGHT_EXISTS_AND_THM]
]);






(* ------------------------------------ *)
(* Program Hoare triples                *)
(* ------------------------------------ *)

val ASL_PROGRAM_HOARE_TRIPLE_def = Define `
   ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog Q =
   HOARE_TRIPLE P (ASL_PROGRAM_SEM xenv penv prog) Q`


val ASL_PROGRAM_HOARE_TRIPLE_REWRITE = store_thm ("ASL_PROGRAM_HOARE_TRIPLE_REWRITE",
``!xenv penv P Q p.
ASL_PROGRAM_HOARE_TRIPLE xenv penv P p Q =
(!s t. (s IN P /\ t IN ASL_PROGRAM_TRACES penv p) ==>
   (?s'. (ASL_TRACE_SEM xenv t s = SOME s') /\ (s' SUBSET Q)))``,

SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_def,
   HOARE_TRIPLE_def, fasl_order___SUP_fasl_action_order,
   ASL_PROGRAM_SEM_def, IN_IMAGE, GSYM LEFT_FORALL_IMP_THM,
   GSYM RIGHT_FORALL_IMP_THM, ASL_TRACE_SET_SEM_def] THEN
METIS_TAC[]);



val ASL_PROGRAM_HOARE_TRIPLE_PROC_def = Define `
   ASL_PROGRAM_HOARE_TRIPLE_PROC n xenv penv P prog Q =
   HOARE_TRIPLE P (ASL_PROGRAM_SEM_PROC n xenv penv prog) Q`


val ASL_PROGRAM_HOARE_TRIPLE___PROC_THM = store_thm ("ASL_PROGRAM_HOARE_TRIPLE___PROC_THM",
``ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog Q =
   !n. ASL_PROGRAM_HOARE_TRIPLE_PROC n xenv penv P prog Q``,

SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_HOARE_TRIPLE_PROC_def,
   ASL_PROGRAM_SEM___PROC_THM, HOARE_TRIPLE_def,
   fasl_order_THM, SOME___SUP_fasl_action_order, IN_ABS,
   GSYM LEFT_FORALL_IMP_THM] THEN
HO_MATCH_MP_TAC (prove (``(!s. (X s = !n. Y s n)) ==> ((!s. X s) = (!n s. Y s n))``, METIS_TAC[])) THEN
GEN_TAC THEN
Cases_on `s IN P` THEN ASM_REWRITE_TAC[] THEN
Tactical.REVERSE (Cases_on `!n. IS_SOME (ASL_PROGRAM_SEM_PROC n xenv penv prog s)`) THEN1 (
   ASM_REWRITE_TAC[] THEN
   FULL_SIMP_TAC std_ss [] THEN
   Q.EXISTS_TAC `n` THEN
   ASM_SIMP_TAC std_ss []
) THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   IN_ABS, GSYM LEFT_FORALL_IMP_THM] THEN
METIS_TAC[option_CLAUSES]);


val ASL_PROGRAM_HOARE_TRIPLE_PROC_REWRITE = store_thm ("ASL_PROGRAM_HOARE_TRIPLE_PROC_REWRITE",
``!n xenv penv P Q p.
ASL_PROGRAM_HOARE_TRIPLE_PROC n xenv penv P p Q =
(!s t. (s IN P /\ t IN ASL_PROGRAM_TRACES_PROC n penv p) ==>
   (?s'. (ASL_TRACE_SEM xenv t s = SOME s') /\ (s' SUBSET Q)))``,

SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_PROC_def,
   HOARE_TRIPLE_def, fasl_order___SUP_fasl_action_order,
   ASL_PROGRAM_SEM_PROC_def, IN_IMAGE, GSYM LEFT_FORALL_IMP_THM,
   GSYM RIGHT_FORALL_IMP_THM, ASL_TRACE_SET_SEM_def] THEN
METIS_TAC[]);




(******************************************************************************)
(* Conditional Hoare Triples                                                  *)
(******************************************************************************)

val COND_HOARE_TRIPLE_def = Define `
   COND_HOARE_TRIPLE (Pcond,P) f (Qcond,Q) =
   ((Pcond /\ Qcond) ==> HOARE_TRIPLE P f Q)`;

val COND_HOARE_TRIPLE_TRUE = store_thm ("COND_HOARE_TRIPLE_TRUE",
``COND_HOARE_TRIPLE (T,P) f (T,Q) =
  HOARE_TRIPLE P f Q``,
SIMP_TAC std_ss [COND_HOARE_TRIPLE_def]);


val COND_HOARE_TRIPLE_REWRITE = store_thm (
   "COND_HOARE_TRIPLE_REWRITE",
``COND_HOARE_TRIPLE P f Q =
  ((FST P /\ FST Q) ==>HOARE_TRIPLE (SND P) f (SND Q))``,
Cases_on `P` THEN Cases_on `Q` THEN
SIMP_TAC std_ss [COND_HOARE_TRIPLE_def]);



val COND_PROP___STRONG_EXISTS_def = Define
`COND_PROP___STRONG_EXISTS P =
 ((!x. FST (P x)), asl_exists x. (SND (P x)))`;



val COND_PROP___STRONG_EXISTS___SWAP = store_thm (
"COND_PROP___STRONG_EXISTS___SWAP",
``!X.
COND_PROP___STRONG_EXISTS (\x1. COND_PROP___STRONG_EXISTS (\x2. X x1 x2)) =
COND_PROP___STRONG_EXISTS (\x2. COND_PROP___STRONG_EXISTS (\x1. X x1 x2))``,

SIMP_TAC std_ss [COND_PROP___STRONG_EXISTS_def, asl_exists_def, IN_ABS] THEN
METIS_TAC[]);


val COND_PROP___STRONG_EXISTS___UNION = store_thm (
"COND_PROP___STRONG_EXISTS___UNION",
``!X.
COND_PROP___STRONG_EXISTS (\x1. COND_PROP___STRONG_EXISTS (\x2. X x1 x2)) =
COND_PROP___STRONG_EXISTS (\x. X (FST x) (SND x))``,

SIMP_TAC std_ss [COND_PROP___STRONG_EXISTS_def, asl_exists_def, IN_ABS] THEN
QUANT_INSTANTIATE_TAC [pair_default_qp]);



val COND_PROP___STRONG_EXISTS___ELIM = store_thm (
"COND_PROP___STRONG_EXISTS___ELIM",
``!X. COND_PROP___STRONG_EXISTS (\x. X) = X``,
SIMP_TAC std_ss [COND_PROP___STRONG_EXISTS_def, asl_exists_def, IN_ABS3]);


val COND_HOARE_TRIPLE___STRONG_COND_EXISTS___PRE_IMPL =
store_thm ("COND_HOARE_TRIPLE___STRONG_COND_EXISTS___PRE_IMPL",
``!P f Q.
(!x. COND_HOARE_TRIPLE (P x) f Q) ==>
(COND_HOARE_TRIPLE (COND_PROP___STRONG_EXISTS P) f Q)``,

SIMP_TAC std_ss [COND_PROP___STRONG_EXISTS_def,
   COND_HOARE_TRIPLE_REWRITE, GSYM LEFT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, HOARE_TRIPLE_def, asl_bool_EVAL] THEN
METIS_TAC[]);



val COND_HOARE_TRIPLE___STRONG_COND_EXISTS___POST_IMPL =
store_thm ("COND_HOARE_TRIPLE___STRONG_COND_EXISTS___POST_IMPL",
``!P f Q.
(?x. COND_HOARE_TRIPLE P f (Q x)) ==>
(COND_HOARE_TRIPLE P f (COND_PROP___STRONG_EXISTS Q))``,

SIMP_TAC std_ss [COND_PROP___STRONG_EXISTS_def,
  COND_HOARE_TRIPLE_REWRITE, GSYM LEFT_EXISTS_AND_THM,
  GSYM LEFT_FORALL_IMP_THM, HOARE_TRIPLE_def, asl_bool_EVAL, asl_exists_def] THEN
SIMP_TAC std_ss [fasl_order_THM] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
Q.PAT_ASSUM `!x'. x' IN SND P ==> X x'` (MP_TAC o Q.SPEC `s`) THEN
ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM, SUBSET_DEF, IN_ABS] THEN
METIS_TAC[]);



val asl_cond_star_def = Define
`asl_cond_star f P1 P2 =
 (FST P1 /\ FST P2, asl_star f (SND P1) (SND P2))`;


val COND_PROP___WEAK_IMP_def = Define `
COND_PROP___WEAK_IMP P1 P2 =
(!x. (FST P1 /\ FST P2 /\ x IN SND P1) ==> (x IN SND P2))`;


val COND_PROP___IMP_def = Define `
COND_PROP___IMP P1 P2 =
(!x. (FST P1 /\ x IN SND P1) ==> (FST P2 /\ x IN SND P2))`;


val COND_PROP___STRONG_IMP_def = Define `
COND_PROP___STRONG_IMP P1 P2 =
((FST P1 ==> FST P2) /\
 (FST P1 /\ FST P2 ==> (SND P1 = SND P2)))`;


val COND_PROP___STRONG_IMP_IMP = store_thm ("COND_PROP___STRONG_IMP_IMP",
``!P1 P2.
COND_PROP___STRONG_IMP P1 P2 ==>
COND_PROP___IMP P1 P2``,

SIMP_TAC std_ss [COND_PROP___IMP_def, COND_PROP___STRONG_IMP_def] THEN
METIS_TAC[]);



val COND_PROP___EQUIV_def = Define `
COND_PROP___EQUIV P1 P2 =
(COND_PROP___IMP P1 P2 /\ COND_PROP___IMP P2 P1)`;


val COND_PROP___STRONG_EQUIV_def = Define `
COND_PROP___STRONG_EQUIV P1 P2 =
(COND_PROP___STRONG_IMP P1 P2 /\ COND_PROP___STRONG_IMP P2 P1)`;


val COND_PROP___STRONG_EQUIV___SYM = store_thm(
"COND_PROP___STRONG_EQUIV___SYM",
``!P1 P2. COND_PROP___STRONG_EQUIV P1 P2 = COND_PROP___STRONG_EQUIV P2 P1``,
  SIMP_TAC std_ss [COND_PROP___STRONG_EQUIV_def] THEN PROVE_TAC[]
);



val COND_PROP___EQUIV_REWRITE = store_thm(
"COND_PROP___EQUIV_REWRITE",
``!P1 P2. COND_PROP___EQUIV P1 P2 =
     (!x. (FST P1 /\ x IN SND P1) = (FST P2 /\ x IN SND P2))``,
SIMP_TAC std_ss [COND_PROP___EQUIV_def, COND_PROP___IMP_def] THEN
PROVE_TAC[]);




val COND_PROP___STRONG_EQUIV_REWRITE =  store_thm(
"COND_PROP___STRONG_EQUIV_REWRITE",
``!P1 P2. COND_PROP___STRONG_EQUIV P1 P2 =
     ((FST P1 = FST P2) /\ ((FST P1 /\ FST P2) ==> (SND P1 = SND P2)))``,
SIMP_TAC std_ss [COND_PROP___STRONG_EQUIV_def, COND_PROP___STRONG_IMP_def] THEN
METIS_TAC[]);



val COND_PROP___STRONG_EQUIV_IMP = store_thm (
"COND_PROP___STRONG_EQUIV_IMP",
``!P1 P2. COND_PROP___STRONG_EQUIV P1 P2 ==> COND_PROP___EQUIV P1 P2``,
SIMP_TAC std_ss [COND_PROP___STRONG_EQUIV_REWRITE, COND_PROP___EQUIV_REWRITE] THEN
METIS_TAC[]);




val COND_HOARE_TRIPLE___COND_PROP_IMP = store_thm (
"COND_HOARE_TRIPLE___COND_PROP_IMP",
``!P1 P2 prog Q.
COND_PROP___IMP P1 P2 ==>
(COND_HOARE_TRIPLE P2 prog Q ==> COND_HOARE_TRIPLE P1 prog Q)``,

Cases_on `P1` THEN Cases_on `P2` THEN Cases_on `Q` THEN
SIMP_TAC std_ss [COND_HOARE_TRIPLE_def,
  COND_PROP___IMP_def, IN_ABS, HOARE_TRIPLE_def] THEN
METIS_TAC[]);



val COND_HOARE_TRIPLE___COND_PROP_STRONG_IMP___POST =
store_thm ("COND_HOARE_TRIPLE___COND_PROP_STRONG_IMP___POST",
``!P prog Q1 Q2.
COND_PROP___STRONG_IMP Q1 Q2 ==>
(COND_HOARE_TRIPLE P prog Q2 ==> COND_HOARE_TRIPLE P prog Q1)``,

Cases_on `Q1` THEN Cases_on `Q2` THEN Cases_on `P` THEN
SIMP_TAC std_ss [COND_HOARE_TRIPLE_def,
       COND_PROP___STRONG_IMP_def]);



val COND_PROP___STRONG_EXISTS___COND_PROP___STRONG_IMP = store_thm (
"COND_PROP___STRONG_EXISTS___COND_PROP___STRONG_IMP",
``(!x. COND_PROP___STRONG_IMP (P x) (P' x)) ==>
COND_PROP___STRONG_IMP
  (COND_PROP___STRONG_EXISTS P)
  (COND_PROP___STRONG_EXISTS P')``,
SIMP_TAC std_ss [COND_PROP___STRONG_EXISTS_def,
       COND_PROP___STRONG_IMP_def]);



val COND_HOARE_TRIPLE___COND_PROP_EQUIV = store_thm (
"COND_HOARE_TRIPLE___COND_PROP_EQUIV",
``!P1 P2 prog Q.
COND_PROP___EQUIV P1 P2 ==>
(COND_HOARE_TRIPLE P1 prog Q =
 COND_HOARE_TRIPLE P2 prog Q)``,

METIS_TAC[COND_HOARE_TRIPLE___COND_PROP_IMP,
     COND_PROP___EQUIV_def]);


val COND_PROP___IMP___REFL = store_thm ("COND_PROP___IMP___REFL",
``!p. COND_PROP___IMP p p``,
SIMP_TAC std_ss [COND_PROP___IMP_def]);


val COND_PROP___IMP___REFL___COMPUTE = store_thm ("COND_PROP___IMP___REFL___COMPUTE",
``!p1 p2. (p1 = p2) ==>
COND_PROP___IMP p1 p2``,
SIMP_TAC std_ss [COND_PROP___IMP_def]);


val COND_PROP___IMP___TRANS = store_thm ("COND_PROP___IMP___TRANS",
``!p1 p2 p3. COND_PROP___IMP p1 p2 ==> (COND_PROP___IMP p2 p3 ==> COND_PROP___IMP p1 p3)``,
SIMP_TAC std_ss [COND_PROP___IMP_def] THEN
METIS_TAC[]);



val COND_PROP___EQUIV___REFL = store_thm ("COND_PROP___EQUIV___REFL",
``!p. COND_PROP___EQUIV p p``,
SIMP_TAC std_ss [COND_PROP___EQUIV_def, COND_PROP___IMP___REFL]);



val COND_PROP___EQUIV___REFL___COMPUTE = store_thm ("COND_PROP___EQUIV___REFL___COMPUTE",
``!p1 p2. (p1 = p2) ==> COND_PROP___EQUIV p1 p2``,
SIMP_TAC std_ss [COND_PROP___EQUIV___REFL]);



val COND_PROP___EQUIV___TRANS = store_thm ("COND_PROP___EQUIV___TRANS",
``!p1 p2 p3. COND_PROP___EQUIV p1 p2 ==> (COND_PROP___EQUIV p2 p3 ==>
        COND_PROP___EQUIV p1 p3)``,
SIMP_TAC std_ss [COND_PROP___EQUIV_def] THEN
METIS_TAC[COND_PROP___IMP___TRANS]);


val COND_PROP___EQUIV_IMP___COMPUTE = store_thm (
"COND_PROP___EQUIV_IMP___COMPUTE",
``!p1 p2. COND_PROP___EQUIV p1 p2 ==>
     COND_PROP___IMP p1 p2``,
SIMP_TAC std_ss [COND_PROP___EQUIV_def]);



val COND_PROP___STRONG_IMP___REFL = store_thm ("COND_PROP___STRONG_IMP___REFL",
``!p. COND_PROP___STRONG_IMP p p``,
SIMP_TAC std_ss [COND_PROP___STRONG_IMP_def]);


val COND_PROP___STRONG_IMP___REFL___COMPUTE = store_thm ("COND_PROP___STRONG_IMP___REFL___COMPUTE",
``!p1 p2. (p1 = p2) ==>
COND_PROP___STRONG_IMP p1 p2``,
SIMP_TAC std_ss [COND_PROP___STRONG_IMP_def]);


val COND_PROP___STRONG_IMP___TRANS = store_thm ("COND_PROP___STRONG_IMP___TRANS",
``!p1 p2 p3. COND_PROP___STRONG_IMP p1 p2 ==>
        (COND_PROP___STRONG_IMP p2 p3 ==>
        COND_PROP___STRONG_IMP p1 p3)``,
SIMP_TAC std_ss [COND_PROP___STRONG_IMP_def] THEN
METIS_TAC[]);



val COND_PROP___STRONG_EQUIV___REFL = store_thm ("COND_PROP___STRONG_EQUIV___REFL",
``!p. COND_PROP___STRONG_EQUIV p p``,
SIMP_TAC std_ss [COND_PROP___STRONG_EQUIV_def,
       COND_PROP___STRONG_IMP___REFL]);


val COND_PROP___STRONG_EQUIV___REFL___COMPUTE = store_thm ("COND_PROP___STRONG_EQUIV___REFL___COMPUTE",
``!p1 p2. (p1 = p2) ==>
COND_PROP___STRONG_EQUIV p1 p2``,
SIMP_TAC std_ss [COND_PROP___STRONG_EQUIV___REFL]);



val COND_PROP___STRONG_EQUIV___TRANS = store_thm ("COND_PROP___STRONG_EQUIV___TRANS",
``!p1 p2 p3. COND_PROP___STRONG_EQUIV p1 p2 ==>
        (COND_PROP___STRONG_EQUIV p2 p3 ==>
        COND_PROP___STRONG_EQUIV p1 p3)``,
SIMP_TAC std_ss [COND_PROP___STRONG_EQUIV_def] THEN
METIS_TAC[COND_PROP___STRONG_IMP___TRANS]);


val COND_PROP___STRONG_EQUIV_IMP___COMPUTE = store_thm (
"COND_PROP___STRONG_EQUIV_IMP___COMPUTE",
``!p1 p2. COND_PROP___STRONG_EQUIV p1 p2 ==>
     COND_PROP___STRONG_IMP p1 p2``,
SIMP_TAC std_ss [COND_PROP___STRONG_EQUIV_def]);



val cond_prop_false_def = Define `cond_prop_false = (F, asl_false)`

val COND_PROP___EXISTS_def = Define
`$COND_PROP___EXISTS P = (T, \s. ?x. (FST (P x)) /\ s IN (SND (P x)))`

val _ = set_fixity "COND_PROP___EXISTS" Binder


val COND_PROP___EXISTS___ELIM = store_thm ("COND_PROP___EXISTS___ELIM",
``!P. COND_PROP___EQUIV (COND_PROP___EXISTS x. P) P``,
SIMP_TAC std_ss [COND_PROP___EXISTS_def, COND_PROP___EQUIV_def,
       COND_PROP___IMP_def, IN_ABS]);


val COND_PROP___EXISTS___COND_PROP_FALSE = store_thm ("COND_PROP___EXISTS___COND_PROP_FALSE",
``COND_PROP___EQUIV (COND_PROP___EXISTS x. cond_prop_false) cond_prop_false``,
SIMP_TAC std_ss [COND_PROP___EXISTS___ELIM]);



val COND_HOARE_TRIPLE___COND_EXISTS =
store_thm ("COND_HOARE_TRIPLE___COND_EXISTS",
``!P prog Q. ((COND_HOARE_TRIPLE (COND_PROP___EXISTS x. P x) prog Q) =
         (!x. COND_HOARE_TRIPLE (P x) prog Q))``,
SIMP_TAC std_ss [COND_PROP___EXISTS_def, COND_HOARE_TRIPLE_REWRITE,
  GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM,
  HOARE_TRIPLE_def, IN_ABS] THEN
METIS_TAC[]);





val COND_PROP___ADD_COND_def = Define
`COND_PROP___ADD_COND c P = (c /\ FST P, SND P)`;


val COND_HOARE_TRIPLE___ADD_COND =
store_thm ("COND_HOARE_TRIPLE___ADD_COND",
``!c P prog Q.
(COND_HOARE_TRIPLE (COND_PROP___ADD_COND c P) prog Q) =
(c ==> (COND_HOARE_TRIPLE P prog Q))
``,

SIMP_TAC std_ss [COND_PROP___ADD_COND_def,
       COND_HOARE_TRIPLE_REWRITE] THEN
METIS_TAC[]);



val COND_HOARE_TRIPLE___cond_prop_false =
store_thm ("COND_HOARE_TRIPLE___cond_prop_false",
``!prog Q. COND_HOARE_TRIPLE (cond_prop_false) prog Q``,
SIMP_TAC std_ss [COND_HOARE_TRIPLE_REWRITE,
       cond_prop_false_def]);



val COND_PROP_OR_def = Define `COND_PROP_OR p1 p2 =
(FST p1 /\ FST p2, asl_or (SND p1) (SND p2))`;


val COND_PROP_OR___cond_prop_false = store_thm (
"COND_PROP_OR___cond_prop_false",
``COND_PROP___IMP Q cond_prop_false ==>
  ((COND_PROP___IMP (COND_PROP_OR P Q) P) /\
   (COND_PROP___IMP (COND_PROP_OR Q P) P))``,

SIMP_TAC std_ss [COND_PROP_OR_def, cond_prop_false_def,
   asl_bool_REWRITES, COND_PROP___IMP_def, asl_bool_EVAL] THEN
METIS_TAC[]);



val COND_HOARE_TRIPLE___COND_PROP_OR =
store_thm ("COND_HOARE_TRIPLE___COND_PROP_OR",
``!P1 P2 prog Q.
(COND_HOARE_TRIPLE P1 prog Q /\ COND_HOARE_TRIPLE P2 prog Q) ==>
 COND_HOARE_TRIPLE (COND_PROP_OR P1 P2) prog Q``,

SIMP_TAC std_ss [COND_HOARE_TRIPLE_REWRITE,
   COND_PROP_OR_def, HOARE_TRIPLE_def, IN_ABS, asl_bool_EVAL] THEN
METIS_TAC[]);



val COND_PROP___IMP___ADD_COND = store_thm ("COND_PROP___IMP___ADD_COND",
``!p1 p2 c. COND_PROP___IMP p1 p2 ==>
       COND_PROP___IMP (COND_PROP___ADD_COND c p1)
             (COND_PROP___ADD_COND c p2)``,
SIMP_TAC std_ss [COND_PROP___IMP_def, COND_PROP___ADD_COND_def] THEN
METIS_TAC[]);



val COND_PROP___EQUIV___ADD_COND = store_thm ("COND_PROP___EQUIV___ADD_COND",
``!p1 p2 c. COND_PROP___EQUIV p1 p2 ==>
       COND_PROP___EQUIV (COND_PROP___ADD_COND c p1)
               (COND_PROP___ADD_COND c p2)``,
SIMP_TAC std_ss [COND_PROP___EQUIV_def, COND_PROP___IMP___ADD_COND]);


val COND_PROP___IMP___EXISTS = store_thm ("COND_PROP___IMP___EXISTS",
``!p1 p2. (!x. COND_PROP___IMP (p1 x) (p2 x)) ==>
     (COND_PROP___IMP (COND_PROP___EXISTS x. p1 x)
            (COND_PROP___EXISTS x. p2 x))``,
SIMP_TAC std_ss [COND_PROP___EXISTS_def, COND_PROP___IMP_def, IN_ABS] THEN
METIS_TAC[]);


val COND_PROP___EQUIV___EXISTS = store_thm ("COND_PROP___EQUIV___EXISTS",
``!p1 p2. (!x. COND_PROP___EQUIV (p1 x) (p2 x)) ==>
     (COND_PROP___EQUIV (COND_PROP___EXISTS x. p1 x)
              (COND_PROP___EXISTS x. p2 x))``,
SIMP_TAC std_ss [COND_PROP___EQUIV_def, COND_PROP___IMP___EXISTS]);




val COND_PROP___STRONG_EQUIV___cond_star = store_thm (
"COND_PROP___STRONG_EQUIV___cond_star",
``!f p1 p1' p2 p2'.
  (COND_PROP___STRONG_EQUIV p1 p1' /\
   COND_PROP___STRONG_EQUIV p2 p2') ==>

  COND_PROP___STRONG_EQUIV
     (asl_cond_star f p1 p2) (asl_cond_star f p1' p2')``,
SIMP_TAC std_ss [COND_PROP___STRONG_EQUIV_REWRITE, asl_cond_star_def]);


val asl_cond_star___COND_PROP___STRONG_EXISTS = store_thm (
"asl_cond_star___COND_PROP___STRONG_EXISTS",
``(!f qP Q.
  (asl_cond_star f (COND_PROP___STRONG_EXISTS (\x. qP x)) Q =
   COND_PROP___STRONG_EXISTS (\x. asl_cond_star f (qP x) Q))) /\
  (!f P qQ.
  (asl_cond_star f P (COND_PROP___STRONG_EXISTS (\x. qQ x)) =
   COND_PROP___STRONG_EXISTS (\x. asl_cond_star f P (qQ x))))``,

SIMP_TAC std_ss [asl_cond_star_def, COND_PROP___STRONG_EXISTS_def,
   FORALL_AND_THM, asl_exists___asl_star_THM]);


val asl_cond_star___COND_PROP___STRONG_EXISTS___BOTH = store_thm (
"asl_cond_star___COND_PROP___STRONG_EXISTS___BOTH",
``!f qP qQ.
  (asl_cond_star f (COND_PROP___STRONG_EXISTS (\x. qP x))
         (COND_PROP___STRONG_EXISTS (\x. qQ x))) =
   COND_PROP___STRONG_EXISTS (\x. asl_cond_star f (qP (FST x)) (qQ (SND x)))``,

SIMP_TAC std_ss [asl_cond_star_def, COND_PROP___STRONG_EXISTS_def,
   FORALL_AND_THM, IN_ABS, PAIR_EXISTS_THM,
   asl_exists_def, asl_star_def, PAIR_FORALL_THM] THEN
METIS_TAC[]);



val COND_PROP___ADD_COND___true =
store_thm ("COND_PROP___ADD_COND___true",
``!p. COND_PROP___ADD_COND T p = p``,
SIMP_TAC std_ss [COND_PROP___ADD_COND_def]);


val COND_PROP___ADD_COND___false =  store_thm (
"COND_PROP___ADD_COND___false",
``!p. COND_PROP___EQUIV (COND_PROP___ADD_COND F p)  cond_prop_false``,
SIMP_TAC std_ss [COND_PROP___ADD_COND_def, cond_prop_false_def, COND_PROP___EQUIV_REWRITE]);


val COND_PROP___ADD_COND___COND_PROP_FALSE = store_thm (
"COND_PROP___ADD_COND___COND_PROP_FALSE",
``!c. COND_PROP___EQUIV (COND_PROP___ADD_COND c cond_prop_false) cond_prop_false``,
SIMP_TAC std_ss [COND_PROP___ADD_COND_def, cond_prop_false_def, COND_PROP___EQUIV_REWRITE]);


val COND_PROP___ADD_COND___ADD_COND =
store_thm ("COND_PROP___ADD_COND___ADD_COND",
``!p c1 c2.
  ((COND_PROP___ADD_COND c1 (COND_PROP___ADD_COND c2 p)) =
    COND_PROP___ADD_COND (c1 /\ c2) p)``,
SIMP_TAC std_ss [COND_PROP___ADD_COND_def, CONJ_ASSOC]);


val COND_PROP___ADD_COND___EXISTS =
store_thm ("COND_PROP___ADD_COND___EXISTS",
``!p c.
  COND_PROP___EQUIV
  (COND_PROP___ADD_COND c (COND_PROP___EXISTS x. (p x)))
  (COND_PROP___EXISTS x. (COND_PROP___ADD_COND c (p x)))``,

REPEAT GEN_TAC THEN
SIMP_TAC std_ss [COND_PROP___EXISTS_def,
   COND_PROP___ADD_COND_def,
   COND_PROP___EQUIV_REWRITE,
   IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, CONJ_ASSOC]);



val COND_PROP___EXISTS___ADD_COND =
store_thm ("COND_PROP___EXISTS___ADD_COND",
``!p c x_const. (!x. c x ==> (x = x_const)) ==>
  (COND_PROP___EQUIV
   (COND_PROP___EXISTS x. (COND_PROP___ADD_COND (c x) (p x)))
   (COND_PROP___ADD_COND (c x_const) (p x_const)))``,

REPEAT GEN_TAC THEN
SIMP_TAC std_ss [COND_PROP___EXISTS_def, COND_PROP___ADD_COND_def,
   FORALL_AND_THM, IN_ABS, COND_PROP___IMP_def, COND_PROP___EQUIV_def] THEN
METIS_TAC[]);






(******************************************************************************)
(* Inference rules                                                            *)
(******************************************************************************)

val ASL_INFERENCE___EMPTY = store_thm("ASL_INFERENCE___EMPTY",
   ``ASL_PROGRAM_HOARE_TRIPLE xenv penv P {} Q``,

SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
   ASL_PROGRAM_TRACES_THM, NOT_IN_EMPTY]);


val ASL_INFERENCE_FRAME = store_thm    ("ASL_INFERENCE_FRAME",
``!xenv penv P prog Q.
(IS_SEPARATION_COMBINATOR (FST xenv) /\
ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog Q) ==>
!x. ASL_PROGRAM_HOARE_TRIPLE xenv penv
(asl_star (FST xenv) P x)
prog
(asl_star (FST xenv) Q x)``,

REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_def] THEN
`ASL_IS_LOCAL_ACTION (FST xenv) (ASL_PROGRAM_SEM xenv penv prog)` by ALL_TAC THEN1 (
   MATCH_MP_TAC ASL_IS_LOCAL_ACTION___ASL_PROGRAM_SEM THEN
   ASM_REWRITE_TAC[]
) THEN
FULL_SIMP_TAC std_ss [ASL_IS_LOCAL_ACTION___HOARE_TRIPLE]);




val ASL_INFERENCE_STRENGTHEN = store_thm ("ASL_INFERENCE_STRENGTHEN",
``!xenv penv P1 P2 prog Q1 Q2.
(P2 SUBSET P1 /\ Q1 SUBSET Q2 /\
ASL_PROGRAM_HOARE_TRIPLE xenv penv P1 prog Q1) ==>
ASL_PROGRAM_HOARE_TRIPLE xenv penv P2 prog Q2``,

SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_def,
HOARE_TRIPLE_def, fasl_order_THM, SUBSET_DEF] THEN
METIS_TAC[]);



val ASL_INFERENCE_COMBINE_UNION = store_thm    ("ASL_INFERENCE_COMBINE_UNION",
``!xenv penv PQ prog.
(!P Q. (P,Q) IN PQ ==> ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog Q) ==>
ASL_PROGRAM_HOARE_TRIPLE xenv penv
(BIGUNION (IMAGE FST PQ)) prog (BIGUNION (IMAGE SND PQ))``,

SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
   IN_BIGUNION, IN_IMAGE, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_EXISTS_AND_THM,
   PAIR_FORALL_THM, SUBSET_DEF, PAIR_EXISTS_THM] THEN
METIS_TAC[]);



val ASL_INFERENCE_COMBINE_INTER = store_thm    ("ASL_INFERENCE_COMBINE_INTER",
``!xenv penv PQ prog.
((!P Q. (P,Q) IN PQ ==> ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog Q) /\
(~(PQ = {}))) ==>
ASL_PROGRAM_HOARE_TRIPLE xenv penv
(BIGINTER (IMAGE FST PQ)) prog (BIGINTER (IMAGE SND PQ))``,

SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_def,
HOARE_TRIPLE_def, fasl_order_THM, IN_BIGINTER, IN_IMAGE, GSYM LEFT_EXISTS_AND_THM,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
`?P Q. (P,Q) IN PQ` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY] THEN
   Cases_on `x` THEN METIS_TAC[]
) THEN
`s IN P` by (RES_TAC THEN FULL_SIMP_TAC std_ss []) THEN
RES_TAC THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGINTER, IN_IMAGE,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN

`?P2 Q2. (x' = (P2,Q2)) /\ (s IN P2)` by ALL_TAC THEN1 (
   Cases_on `x'` THEN
   RES_TAC THEN
   FULL_SIMP_TAC std_ss []
) THEN
FULL_SIMP_TAC std_ss [] THEN
RES_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
METIS_TAC[SUBSET_DEF]);



val ASL_INFERENCE_prog_prim_command = store_thm ("ASL_INFERENCE_prog_prim_command",
``!xenv penv P pc Q.
(!s. s IN P ==> ?s'. (EVAL_asl_prim_command (FST xenv) pc s = SOME s') /\ s' SUBSET Q) ==>

ASL_PROGRAM_HOARE_TRIPLE xenv penv
P (asl_prog_prim_command pc) Q``,


SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
   ASL_PROGRAM_TRACES_IN_THM,
   ASL_TRACE_SEM_REWRITE, asla_seq_skip] THEN
Cases_on `xenv` THEN
SIMP_TAC std_ss [ASL_ATOMIC_ACTION_SEM_def]);



val ASL_INFERENCE_prog_skip = store_thm   ("ASL_INFERENCE_prog_skip",
``!xenv penv P.
ASL_PROGRAM_HOARE_TRIPLE xenv penv
P asl_prog_skip P``,

REPEAT STRIP_TAC THEN
REWRITE_TAC [asl_prog_skip_def] THEN
MATCH_MP_TAC ASL_INFERENCE_prog_prim_command THEN
SIMP_TAC std_ss [EVAL_asl_prim_command_THM,
   asla_skip_def, SUBSET_DEF, IN_SING]);


val ASL_INFERENCE_prog_seq_diverge = store_thm ("ASL_INFERENCE_prog_seq_diverge",
``!xenv penv prog P Q.
ASL_PROGRAM_HOARE_TRIPLE xenv penv
P (asl_prog_seq asl_prog_diverge prog) Q``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [
   ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
   ASL_PROGRAM_TRACES_THM,
   asla_seq_def, IN_ABS,
   asl_prog_diverge_def,
   GSYM asl_aa_diverge_def,
   INSERT_INSERT, IN_SING] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC list_ss [EMPTY_SUBSET,
   ASL_TRACE_SEM_diverge]);


val ASL_INFERENCE_prog_diverge = store_thm     ("ASL_INFERENCE_prog_diverge",
``!xenv penv P Q.
ASL_PROGRAM_HOARE_TRIPLE xenv penv
P asl_prog_diverge Q``,

REPEAT STRIP_TAC THEN
REWRITE_TAC [asl_prog_diverge_def] THEN
MATCH_MP_TAC ASL_INFERENCE_prog_prim_command THEN
SIMP_TAC std_ss [EVAL_asl_prim_command_THM,
asla_diverge_def, EMPTY_SUBSET]);


val ASL_INFERENCE_prog_quant_best_local_action = store_thm ("ASL_INFERENCE_prog_quant_best_local_action",
``!xenv penv qP qQ arg.
(IS_SEPARATION_COMBINATOR (FST xenv)) ==>
ASL_PROGRAM_HOARE_TRIPLE xenv penv
(qP arg) (asl_prog_quant_best_local_action qP qQ) (qQ arg)``,


REPEAT STRIP_TAC THEN
REWRITE_TAC [asl_prog_quant_best_local_action_def] THEN
MATCH_MP_TAC ASL_INFERENCE_prog_prim_command THEN
Q.ABBREV_TAC `f = (FST xenv)` THEN
MP_TAC (ISPECL [``f:'a bin_option_function``, ``qP:'e -> 'a -> bool``, ``qQ:'e -> 'a -> bool``] quant_best_local_action_THM) THEN
FULL_SIMP_TAC std_ss [HOARE_TRIPLE_def, fasl_order_THM,
            EVAL_asl_prim_command_THM])


val ASL_INFERENCE_prog_quant_best_local_action2 = store_thm ("ASL_INFERENCE_prog_quant_best_local_action2",
``!xenv penv P Q qP qQ.
(IS_SEPARATION_COMBINATOR (FST xenv)) ==>

(?arg. ASL_PROGRAM_HOARE_TRIPLE xenv penv P
     (asl_prog_best_local_action (qP arg) (qQ arg)) Q) ==>

ASL_PROGRAM_HOARE_TRIPLE xenv penv P
    (asl_prog_quant_best_local_action qP qQ) Q``,

REPEAT GEN_TAC THEN STRIP_TAC THEN
`?f lenv. xenv = (f,lenv)` by (Cases_on `xenv` THEN SIMP_TAC std_ss []) THEN
FULL_SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_def,
   asl_prog_best_local_action_def, asl_prog_quant_best_local_action_def,
   ASL_PROGRAM_SEM___prim_command, ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM, best_local_action_THM,
   quant_best_local_action_THM] THEN
SIMP_TAC std_ss [HOARE_TRIPLE_def, fasl_order_THM,
   GSYM LEFT_FORALL_IMP_THM, SOME___best_local_action,
   SOME___quant_best_local_action, SUBSET_DEF, IN_ABS] THEN
METIS_TAC[]);



val ASL_INFERENCE_prog_seq_STRONG = store_thm ("ASL_INFERENCE_prog_seq_STRONG",
``!xenv penv P R p1 p2.
 ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_seq p1 p2) R =
 (?Q. ASL_PROGRAM_HOARE_TRIPLE xenv penv P p1 Q /\
      ASL_PROGRAM_HOARE_TRIPLE xenv penv Q p2 R)``,


SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_def,
       ASL_PROGRAM_SEM___prog_seq] THEN
REPEAT STRIP_TAC THEN
Q.ABBREV_TAC `a1 = ASL_PROGRAM_SEM xenv penv p1` THEN
Q.ABBREV_TAC `a2 = ASL_PROGRAM_SEM xenv penv p2` THEN
SIMP_TAC std_ss [HOARE_TRIPLE_def, fasl_order_THM,
   SOME___asla_seq, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, SUBSET_DEF, IN_BIGUNION,
   IN_IMAGE, GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
EQ_TAC THEN REPEAT STRIP_TAC THENL [
   Q.EXISTS_TAC `BIGUNION (IMAGE (THE o a1) P)` THEN
   SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_FORALL_IMP_THM] THEN
   HO_MATCH_MP_TAC (prove 
      (``(!e. (X e /\ !x. Y x e)) ==> ((!e. X e) /\ (!x x'. Y x x'))``, METIS_TAC[])) THEN
   GEN_TAC THEN
   Cases_on `x IN P` THEN ASM_REWRITE_TAC[] THEN
   Q.PAT_ASSUM `!s. s IN P ==> X s` (MP_TAC o Q.SPEC `x`) THEN
   ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THENL [
      Q.EXISTS_TAC `x` THEN
      ASM_SIMP_TAC std_ss [],

      METIS_TAC[option_CLAUSES]
   ],


   Q.PAT_ASSUM `!s. s IN P ==> X s` (MP_TAC o Q.SPEC `s`) THEN
   ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN
   GEN_TAC THEN STRIP_TAC THEN
   HO_MATCH_MP_TAC (prove 
      (``(!e. (X e /\ !x. Y x e)) ==> ((!e. X e) /\ (!x x'. Y x x'))``, METIS_TAC[])) THEN
   GEN_TAC THEN
   Cases_on `x' IN s1` THEN ASM_REWRITE_TAC[] THEN
   Q.PAT_ASSUM `!s. s IN Q ==> X s` (MP_TAC o Q.SPEC `x'`) THEN
   ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM]
]);


val ASL_INFERENCE_prog_seq = store_thm ("ASL_INFERENCE_prog_seq",
``!xenv penv P Q R p1 p2.
(ASL_PROGRAM_HOARE_TRIPLE xenv penv P p1 Q /\
 ASL_PROGRAM_HOARE_TRIPLE xenv penv Q p2 R) ==>
 ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_seq p1 p2) R``,

METIS_TAC[ASL_INFERENCE_prog_seq_STRONG]);



val ASL_INFERENCE_prog_choice_STRONG = store_thm("ASL_INFERENCE_prog_choice_STRONG",
``!xenv penv P Q p1 p2.
ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_choice p1 p2) Q =
(ASL_PROGRAM_HOARE_TRIPLE xenv penv P p1 Q /\
 ASL_PROGRAM_HOARE_TRIPLE xenv penv P p2 Q)``,

SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
   ASL_PROGRAM_TRACES_IN_THM, IN_UNION] THEN
METIS_TAC[]);


val ASL_INFERENCE_prog_choice = store_thm ("ASL_INFERENCE_prog_choice",
``!xenv penv P Q p1 p2.
(ASL_PROGRAM_HOARE_TRIPLE xenv penv P p1 Q /\
 ASL_PROGRAM_HOARE_TRIPLE xenv penv P p2 Q) ==>
 ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_choice p1 p2) Q``,

SIMP_TAC std_ss [ASL_INFERENCE_prog_choice_STRONG]);



val ASL_INFERENCE_prog_kleene_star_STRONG = store_thm ("ASL_INFERENCE_prog_kleene_star_STRONG",
``!xenv penv P p.
ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_kleene_star p) P =
ASL_PROGRAM_HOARE_TRIPLE xenv penv P p P``,

SIMP_TAC std_ss [
   ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___prog_kleene_star___asla_kleene_star,
   asla_kleene_star_def,
   HOARE_INFERENCE___SUP_fasl_action_order, GSPECIFICATION,
   IN_UNIV, GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT GEN_TAC THEN
Q.ABBREV_TAC `ps = ASL_PROGRAM_SEM xenv penv p` THEN
EQ_TAC THEN REPEAT STRIP_TAC THEN1 (
   Q.PAT_ASSUM `!n. X n` (MP_TAC o Q.SPEC `SUC 0`) THEN
   REWRITE_TAC [asla_repeat_def, asla_seq_skip]
) THEN

Induct_on `n` THENL [
  SIMP_TAC std_ss [asla_repeat_def, HOARE_TRIPLE_def, asla_skip_def,
     fasl_order_THM, IN_SING, SUBSET_DEF],

  FULL_SIMP_TAC std_ss [asla_repeat_def, HOARE_TRIPLE_def,
     fasl_order_THM, SOME___asla_seq, GSYM RIGHT_EXISTS_AND_THM,
     GSYM LEFT_EXISTS_AND_THM, SUBSET_DEF, IN_BIGUNION, IN_IMAGE, IN_ABS,
     GSYM LEFT_FORALL_IMP_THM] THEN
  REPEAT STRIP_TAC THEN
  Q.PAT_ASSUM `!s. s IN P ==> ?s1. (ps s = SOME s1) /\ XXX` (MP_TAC o Q.SPEC `s`) THEN
  ASM_SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM] THEN
  METIS_TAC[option_CLAUSES]
]);



val ASL_INFERENCE_prog_kleene_star = store_thm ("ASL_INFERENCE_prog_kleene_star",
``!xenv penv P p.
ASL_PROGRAM_HOARE_TRIPLE xenv penv P p P ==>
ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_kleene_star p) P``,

METIS_TAC[ASL_INFERENCE_prog_kleene_star_STRONG]);



val ASL_PROGRAM_SEM___PARALLEL_DECOMPOSITION = store_thm ("ASL_PROGRAM_SEM___PARALLEL_DECOMPOSITION",
``!xenv penv q1 q2 s s1 s2 p1 p2.
IS_SEPARATION_COMBINATOR (FST xenv) /\
fasl_order (ASL_PROGRAM_SEM xenv penv p1 s1) q1 /\
fasl_order (ASL_PROGRAM_SEM xenv penv p2 s2) q2 /\
(SOME s = (FST xenv) (SOME s1) (SOME s2)) ==>

fasl_order (ASL_PROGRAM_SEM xenv penv (asl_prog_parallel p1 p2) s) 
           (fasl_star (FST xenv) q1 q2)``,

REPEAT STRIP_TAC THEN
Cases_on `(q1 = NONE) \/ (q2 = NONE)` THEN1 (
   FULL_SIMP_TAC std_ss [fasl_order_THM, fasl_star_REWRITE]
) THEN
`?q1v q2v. (q1 = SOME q1v) /\ (q2 = SOME q2v)` by ALL_TAC THEN1 (
   Cases_on `q1` THEN Cases_on `q2` THEN 
   FULL_SIMP_TAC std_ss []
) THEN
FULL_SIMP_TAC std_ss [ASL_PROGRAM_SEM_def, ASL_TRACE_SET_SEM_def,
   fasl_order___SUP_fasl_action_order, fasl_star_REWRITE,
   IN_IMAGE, GSYM LEFT_FORALL_IMP_THM, ASL_PROGRAM_TRACES_IN_THM,
   GSYM fasl_order_THM] THEN
REPEAT STRIP_TAC THEN
Cases_on `xenv` THEN
FULL_SIMP_TAC std_ss [GSYM fasl_star_REWRITE] THEN
MATCH_MP_TAC ASL_TRACE_SEM___PARALLEL_DECOMPOSITION THEN
METIS_TAC[]);


val ASL_INFERENCE_prog_parallel = store_thm ("ASL_INFERENCE_prog_parallel",
``!xenv penv P1 P2 Q1 Q2 p1 p2.
(IS_SEPARATION_COMBINATOR (FST xenv) /\
 ASL_PROGRAM_HOARE_TRIPLE xenv penv P1 p1 Q1 /\
 ASL_PROGRAM_HOARE_TRIPLE xenv penv P2 p2 Q2) ==>

ASL_PROGRAM_HOARE_TRIPLE xenv penv (asl_star (FST xenv) P1 P2)
   (asl_prog_parallel p1 p2) (asl_star (FST xenv) Q1 Q2)``,

SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_def, HOARE_TRIPLE_def,
   GSYM fasl_star_REWRITE] THEN
SIMP_TAC std_ss [asl_star_def, IN_ABS] THEN
METIS_TAC[ASL_PROGRAM_SEM___PARALLEL_DECOMPOSITION]);



val ASL_INFERENCE_prog_lock_declaration = store_thm    ("ASL_INFERENCE_prog_lock_declaration",
``!f lock_env penv P Q R l p.
(IS_SEPARATION_COMBINATOR f /\
ASL_PROGRAM_HOARE_TRIPLE (f, lock_env) penv P p Q /\
((lock_env l) = R) /\
(ASL_IS_PRECISE f R)) ==>

ASL_PROGRAM_HOARE_TRIPLE (f, lock_env) penv (asl_star f P R)
 (asl_prog_lock_declaration l p) (asl_star f Q R)``,

SIMP_TAC list_ss [ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
   ASL_PROGRAM_TRACES_IN_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM,
   ASL_TRACE_REMOVE_LOCKS_REWRITE,
   ASL_IS_LOCK_ATOMIC_ACTION_def, IN_SING] THEN
REPEAT STRIP_TAC THEN

Tactical.REVERSE (`?s'.
      (ASL_TRACE_SEM (f,lock_env)
       (asl_aa_verhoog l::t' ++ [asl_aa_prolaag l]) s =
       SOME s') /\ s' SUBSET asl_star f Q (lock_env l)` by ALL_TAC) THEN1 (


   MP_TAC (Q.SPECL [`(f,lock_env)`, `l`, `t'`] ASL_TRACE_SYNCHRONISED_ACTION_ORDER) THEN
   ASM_SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF,
      GSYM LEFT_EXISTS_IMP_THM] THEN
   Q.EXISTS_TAC `s` THEN
   ASM_SIMP_TAC std_ss [fasl_order_THM,
      GSYM LEFT_FORALL_IMP_THM] THEN
   METIS_TAC[SUBSET_TRANS]
) THEN

SIMP_TAC list_ss [ASL_TRACE_SEM_REWRITE,
   ASL_TRACE_SEM_APPEND, asla_seq_skip] THEN

ASM_SIMP_TAC std_ss [SOME___asla_seq, GSYM LEFT_EXISTS_AND_THM, GSYM
   RIGHT_EXISTS_AND_THM, ASL_ATOMIC_ACTION_SEM_def] THEN

`?p. (asla_annihilation f (lock_env l) s = SOME p) /\ (p SUBSET P)` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [asla_annihilation_PRECISE_THM, LET_THM, COND_RAND, COND_RATOR,
      asl_star_def, IN_ABS, SUBSET_DEF, GSYM LEFT_FORALL_IMP_THM] THEN
   CONJ_TAC THENL [
      SIMP_TAC std_ss [EXTENSION, IN_ABS, NOT_IN_EMPTY] THEN
      METIS_TAC[],

      REPEAT STRIP_TAC THEN
      `s1 = q` by ALL_TAC THEN1 (
         Q.PAT_ASSUM `ASL_IS_PRECISE f (lock_env l)` (MATCH_MP_TAC o
         SIMP_RULE std_ss [ASL_IS_PRECISE_def]) THEN
         Q.EXISTS_TAC `s` THEN
         ASM_SIMP_TAC std_ss [ASL_IS_SUBSTATE_def] THEN
         METIS_TAC[IS_SEPARATION_COMBINATOR_def, COMM_DEF]
      ) THEN
      FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
      `x = p'` by METIS_TAC[
      OPTION_IS_RIGHT_CANCELLATIVE_def, COMM_DEF, option_CLAUSES] THEN
      METIS_TAC[]
   ]
) THEN
ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
   asla_materialisation_THM] THEN
CONJ_TAC THEN1 (
   REPEAT STRIP_TAC THEN
   `e IN P` by METIS_TAC[SUBSET_DEF] THEN
   RES_TAC THEN
   ASM_SIMP_TAC std_ss []
) THEN
SIMP_TAC std_ss [GSYM LEFT_FORALL_IMP_THM,
   asl_star_def, IN_ABS, IN_SING,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
`?s'. (ASL_TRACE_SEM (f,lock_env) t' x'' = SOME s') /\ (s' SUBSET Q)` by METIS_TAC[SUBSET_DEF] THEN
Q.EXISTS_TAC `x'` THEN
Q.EXISTS_TAC `p''` THEN
FULL_SIMP_TAC std_ss [] THEN
METIS_TAC[IS_SEPARATION_COMBINATOR_def, COMM_DEF, SUBSET_DEF]);






val ASL_INFERENCE_prog_critical_section = store_thm  ("ASL_INFERENCE_prog_critical_section",
``!f lock_env penv l p P Q R.
(IS_SEPARATION_COMBINATOR f /\
((lock_env l) = R) /\
ASL_PROGRAM_HOARE_TRIPLE (f, lock_env) penv (asl_star f P R)
 p (asl_star f Q R) /\
(ASL_IS_PRECISE f R)) ==>

ASL_PROGRAM_HOARE_TRIPLE (f, lock_env) penv P (asl_prog_critical_section l p) Q``,


SIMP_TAC list_ss [ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
   ASL_PROGRAM_TRACES_IN_THM,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM,
   ASL_TRACE_REMOVE_LOCKS_REWRITE,
   ASL_IS_LOCK_ATOMIC_ACTION_def, IN_SING] THEN
REPEAT STRIP_TAC THEN

ASM_SIMP_TAC std_ss [ASL_TRACE_SEM_REWRITE,
   ASL_TRACE_SEM_APPEND, asla_seq_skip] THEN
ASM_SIMP_TAC std_ss [
   SOME___asla_seq, GSYM LEFT_EXISTS_AND_THM,
   ASL_ATOMIC_ACTION_SEM_def,
   asla_materialisation_THM] THEN
SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM] THEN

MATCH_MP_TAC (prove (``
   (!e. e IN X ==> ?q. (Y e = SOME q) /\ (q SUBSET Q))

   ==>
   ((!e. e IN X ==> IS_SOME (Y e)) /\
   (!x x''. (x IN (THE (Y x'')) /\ x'' IN X) ==> x IN Q))``,

   REPEAT STRIP_TAC THENL [
      RES_TAC THEN ASM_SIMP_TAC std_ss [],
      RES_TAC THEN FULL_SIMP_TAC std_ss [SUBSET_DEF]
   ]
)) THEN

ASM_SIMP_TAC std_ss [asl_star_def, IN_ABS, IN_SING] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [SOME___asla_seq, asla_annihilation_PRECISE_THM,
   LET_THM, GSYM LEFT_EXISTS_AND_THM] THEN
SIMP_TAC std_ss [COND_RAND, COND_RATOR, EXTENSION, NOT_IN_EMPTY, IN_ABS] THEN

`?s1. (ASL_TRACE_SEM (f,lock_env) t' e = SOME s1) /\
       s1 SUBSET asl_star f Q (lock_env l)` by ALL_TAC THEN1 (

   Q.PAT_ASSUM `!s' t. X s' t` MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [asl_star_def, IN_ABS] THEN
   Q.EXISTS_TAC `s` THEN
   Q.EXISTS_TAC `p'` THEN
   METIS_TAC[IS_SEPARATION_COMBINATOR_def, COMM_DEF, SUBSET_DEF]
) THEN
ASM_SIMP_TAC std_ss [] THEN
CONJ_TAC THEN1 (
   Q.PAT_ASSUM `s1 SUBSET X` MP_TAC THEN
   SIMP_TAC std_ss [SUBSET_DEF, asl_star_def, IN_ABS] THEN
   METIS_TAC[]
) THEN
SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `x IN X` MP_TAC THEN
ASM_SIMP_TAC std_ss [asla_annihilation_PRECISE_THM, LET_THM, COND_RAND, COND_RATOR,
   IN_ABS] THEN
`~((\s0. ?s1. s1 IN lock_env l /\ (SOME x' = f (SOME s0) (SOME s1))) = {})` by ALL_TAC THEN1 (
   SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY, IN_ABS] THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, asl_star_def, IN_ABS] THEN
   METIS_TAC[]
) THEN
ASM_REWRITE_TAC[] THEN POP_ASSUM (K ALL_TAC) THEN

STRIP_TAC THEN
FULL_SIMP_TAC std_ss [SUBSET_DEF, asl_star_def, IN_ABS] THEN
`?p q. (SOME x' = f (SOME p) (SOME q)) /\ p IN Q /\ q IN lock_env l` by METIS_TAC[] THEN

`s1' = q` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `ASL_IS_PRECISE f X` (MATCH_MP_TAC o REWRITE_RULE [ASL_IS_PRECISE_def]) THEN
   Q.EXISTS_TAC `x'` THEN
   ASM_SIMP_TAC std_ss [ASL_IS_SUBSTATE_def] THEN
   METIS_TAC[IS_SEPARATION_COMBINATOR_def, COMM_DEF]
) THEN
`p'' = x` by ALL_TAC THEN1 (
   FULL_SIMP_TAC std_ss [IS_SEPARATION_COMBINATOR_EXPAND_THM] THEN
   METIS_TAC[OPTION_IS_RIGHT_CANCELLATIVE_def, option_CLAUSES]
) THEN
FULL_SIMP_TAC std_ss []);




val ASL_INFERENCE_asl_quant = store_thm  ("ASL_INFERENCE_asl_quant",

``(ASL_PROGRAM_HOARE_TRIPLE xenv penv (asl_exists x. P x) p Q' =
(!x. ASL_PROGRAM_HOARE_TRIPLE xenv penv (P x) p Q')) /\

(ASL_PROGRAM_HOARE_TRIPLE xenv penv P' p (asl_forall x. Q x) =
(!x. ASL_PROGRAM_HOARE_TRIPLE xenv penv P' p (Q x))) /\

((?x. ASL_PROGRAM_HOARE_TRIPLE xenv penv (P x) p Q') ==>
(ASL_PROGRAM_HOARE_TRIPLE xenv penv (asl_forall x. P x) p Q')) /\

((?x. ASL_PROGRAM_HOARE_TRIPLE xenv penv P' p (Q x)) ==>
(ASL_PROGRAM_HOARE_TRIPLE xenv penv P' p (asl_exists x. Q x)))``,


SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
   asl_exists_def, IN_ABS, GSYM LEFT_EXISTS_AND_THM,
   GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM,
   asl_forall_def] THEN
REPEAT STRIP_TAC THENL [
   METIS_TAC[],


   SIMP_TAC std_ss [SUBSET_DEF, IN_ABS] THEN
   EQ_TAC THEN1 METIS_TAC[] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `!x s t. X x s t` (MP_TAC o Q.GEN `x'` o (Q.SPECL [`x'`, `s`, `t`])) THEN
   ASM_SIMP_TAC std_ss [] THEN
   Cases_on `ASL_TRACE_SEM xenv t s` THEN (
      SIMP_TAC std_ss []
   ),

   FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_ABS] THEN
   METIS_TAC[]
]);



val ASL_INFERENCE_asl_bool = store_thm  ("ASL_INFERENCE_asl_bool",
``
(ASL_PROGRAM_HOARE_TRIPLE xenv penv (asl_or P1 P2)  p Q =
 ASL_PROGRAM_HOARE_TRIPLE xenv penv P1  p Q /\
 ASL_PROGRAM_HOARE_TRIPLE xenv penv P2  p Q) /\
(ASL_PROGRAM_HOARE_TRIPLE xenv penv P  p (asl_and Q1 Q2) =
 ASL_PROGRAM_HOARE_TRIPLE xenv penv P  p Q1 /\
 ASL_PROGRAM_HOARE_TRIPLE xenv penv P  p Q2)``,

SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
   asl_and_def, SUBSET_DEF, IN_ABS, IMP_CONJ_THM,
   FORALL_AND_THM, asl_or_def] THEN
SIMP_TAC std_ss [GSYM SUBSET_DEF] THEN
REPEAT STRIP_TAC THEN1 (
   METIS_TAC[]
) THEN
EQ_TAC THEN1 METIS_TAC[] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
METIS_TAC[]);





val ASL_INFERENCE_assume = store_thm ("ASL_INFERENCE_assume",
``!xenv penv P c.
  IS_SEPARATION_COMBINATOR (FST xenv) /\
 asl_predicate_IS_DECIDED (FST xenv) P c ==>
   (ASL_PROGRAM_HOARE_TRIPLE xenv penv P
      (asl_prog_prim_command (asl_pc_assume c))
      (asl_and P (EVAL_asl_predicate (FST xenv) c)))``,

SIMP_TAC std_ss [asl_predicate_IS_DECIDED_def,
   GSYM asl_prog_assume_def, ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___assume, HOARE_TRIPLE_def,
   fasl_order_THM, EVAL_asl_predicate_def,
   asla_assume_def] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss) [SUBSET_DEF, IN_SING,
   NOT_IN_EMPTY, asl_bool_EVAL] THEN
METIS_TAC[]);



val ASL_INFERENCE_assume_seq = store_thm ("ASL_INFERENCE_assume_seq",
``!xenv penv P prog Q c.
  IS_SEPARATION_COMBINATOR (FST xenv) /\
 asl_predicate_IS_DECIDED (FST xenv) P c /\
  (ASL_PROGRAM_HOARE_TRIPLE xenv penv (asl_and P (EVAL_asl_predicate (FST xenv) c))
     prog Q) ==>

  (ASL_PROGRAM_HOARE_TRIPLE xenv penv P
      (asl_prog_seq (asl_prog_prim_command (asl_pc_assume c)) prog)
      Q)``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_INFERENCE_prog_seq THEN
Q.EXISTS_TAC `asl_and P (EVAL_asl_predicate (FST xenv) c)` THEN
ASM_SIMP_TAC std_ss [ASL_INFERENCE_assume]);


val ASL_INFERENCE_assert = store_thm ("ASL_INFERENCE_assert",
``!xenv penv P c.
  IS_SEPARATION_COMBINATOR (FST xenv) /\
  (!s. s IN P ==> s IN (EVAL_asl_predicate (FST xenv) c)) ==>
   (ASL_PROGRAM_HOARE_TRIPLE xenv penv P
      (asl_prog_prim_command (asl_pc_assert c))
      (asl_and P (EVAL_asl_predicate (FST xenv) c)))``,

REPEAT GEN_TAC THEN
`?lock_env f. xenv = (f,lock_env)` by ALL_TAC THEN1 (
   Cases_on `xenv` THEN SIMP_TAC std_ss []
) THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
   ASL_PROGRAM_TRACES_IN_THM, ASL_TRACE_SEM_REWRITE,
   asla_seq_skip] THEN
SIMP_TAC std_ss [ASL_ATOMIC_ACTION_SEM_def] THEN
ASM_SIMP_TAC std_ss [EVAL_asl_prim_command_THM, asla_assert_def,
   asl_predicate_IS_DECIDED_def, GSYM FORALL_AND_THM,
   EVAL_asl_predicate_def] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN
FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_SING, asl_and_def, IN_ABS]);



val ASL_INFERENCE_assert_seq = store_thm ("ASL_INFERENCE_assert_seq",
``!xenv penv P prog Q c.
  IS_SEPARATION_COMBINATOR (FST xenv) /\

  (!s. s IN P ==> s IN (EVAL_asl_predicate (FST xenv) c)) /\
  (ASL_PROGRAM_HOARE_TRIPLE xenv penv (asl_and P (EVAL_asl_predicate (FST xenv) c))
     prog Q) ==>

  (ASL_PROGRAM_HOARE_TRIPLE xenv penv P
      (asl_prog_seq (asl_prog_prim_command (asl_pc_assert c)) prog)
      Q)``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_INFERENCE_prog_seq THEN
Q.EXISTS_TAC `asl_and P (EVAL_asl_predicate (FST xenv) c)` THEN
ASM_SIMP_TAC std_ss [ASL_INFERENCE_assert]);



val ASL_INFERENCE_prog_cond = store_thm  ("ASL_INFERENCE_prog_cond",
``!xenv penv c P Q pTrue pFalse.
(ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_seq (asl_prog_assume c) pTrue) Q) /\
(ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_seq (asl_prog_assume (asl_pred_neg c)) pFalse) Q) ==>

ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_cond c pTrue pFalse) Q``,

REWRITE_TAC [asl_prog_cond_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_INFERENCE_prog_choice THEN
FULL_SIMP_TAC std_ss [asl_prog_assume_def]);



val ASL_INFERENCE_prog_cond_critical_section = store_thm  ("ASL_INFERENCE_prog_cond_critical_section",

``!f lock_env penv l c p P Q R.
(IS_SEPARATION_COMBINATOR f /\
((lock_env l) = R) /\
 asl_predicate_IS_DECIDED f (asl_star f P R) c /\
ASL_PROGRAM_HOARE_TRIPLE (f, lock_env) penv (asl_and (asl_star f P R) (EVAL_asl_predicate f c))
 p (asl_star f Q R) /\
(ASL_IS_PRECISE f R)) ==>

ASL_PROGRAM_HOARE_TRIPLE (f, lock_env) penv P (asl_prog_cond_critical_section l c p) Q``,

REWRITE_TAC[asl_prog_cond_critical_section_def] THEN
CONSEQ_REWRITE_TAC (
  [ASL_INFERENCE_prog_seq, ASL_INFERENCE_prog_critical_section], [], []) THEN
REPEAT STRIP_TAC THEN
Q.EXISTS_TAC `R` THEN ASM_REWRITE_TAC[] THEN
Q.EXISTS_TAC `asl_and (asl_star f P R) (EVAL_asl_predicate f c)` THEN
ASM_SIMP_TAC std_ss [] THEN
METIS_TAC[ASL_INFERENCE_assume, pairTheory.FST]);



val ASL_INFERENCE_prog_while = store_thm  ("ASL_INFERENCE_prog_while",
``!xenv penv c P p.
(asl_predicate_IS_DECIDED (FST xenv) P c /\
 IS_SEPARATION_COMBINATOR (FST xenv) /\
(ASL_PROGRAM_HOARE_TRIPLE xenv penv (asl_and P (EVAL_asl_predicate (FST xenv) c)) p P)) ==>

ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_while c p) (asl_and P (EVAL_asl_predicate (FST xenv) (asl_pred_neg c)))``,


REWRITE_TAC [asl_prog_while_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_INFERENCE_prog_seq THEN
Q.EXISTS_TAC `P` THEN
REPEAT STRIP_TAC THENL [
   MATCH_MP_TAC ASL_INFERENCE_prog_kleene_star THEN
   MATCH_MP_TAC ASL_INFERENCE_prog_seq THEN
   Q.EXISTS_TAC `asl_and P (EVAL_asl_predicate (FST xenv) c)` THEN
   ASM_SIMP_TAC std_ss [ASL_INFERENCE_assume],

   IMP_RES_TAC asl_predicate_IS_DECIDED_NEGATION THEN
   ASM_SIMP_TAC std_ss [ASL_INFERENCE_assume]
]);



val ASL_INFERENCE_prog_forall = store_thm  ("ASL_INFERENCE_prog_forall",
``!xenv penv P Q body.
(!d. ASL_PROGRAM_HOARE_TRIPLE xenv penv P (body d) Q) =
ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_forall body) Q``,


SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
   asl_prog_forall_def, ASL_PROGRAM_TRACES_def, IN_BIGUNION, IN_IMAGE,
   GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM, IN_UNIV] THEN
METIS_TAC[]);





val ASL_INFERENCE_prog_procedure_call = store_thm  ("ASL_INFERENCE_prog_procedure_call",
``!xenv penv P Q name arg.
(name IN (FDOM penv)) ==>

((ASL_PROGRAM_HOARE_TRIPLE xenv penv P (penv ' name arg) Q) =
(ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_procedure_call name arg) Q))``,


SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM_def, ASL_PROGRAM_TRACES_THM]);




val ASL_INFERENCE___choose_constants___NIL =
store_thm ("ASL_INFERENCE___choose_constants___NIL",
``!f lock_env penv P prog prog2 Q.
IS_SEPARATION_COMBINATOR f ==>
(ASL_PROGRAM_HOARE_TRIPLE (f, lock_env) penv P (asl_prog_seq (asl_prog_choose_constants prog []) prog2) Q =
 ASL_PROGRAM_HOARE_TRIPLE (f, lock_env) penv P (asl_prog_seq (prog []) prog2) Q)``,

SIMP_TAC list_ss [asl_prog_choose_constants_def, LENGTH_NIL,
   IMAGE_ABS, IN_ABS, asl_pred_bigand_def, asl_prog_ndet_def,
   BIGUNION_SING, IN_ABS_SING] THEN
SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_def, ASL_PROGRAM_SEM___prog_seq,
   ASL_PROGRAM_SEM___prim_command, ASL_ATOMIC_ACTION_SEM_def,
   EVAL_asl_prim_command_THM, asla_assume_def,
   EVAL_asl_predicate_def, asl_bool_EVAL] THEN
SIMP_TAC std_ss  [asla_seq_skip, GSYM asla_skip_def]);



val ASL_INFERENCE___choose_constants___ONE =
store_thm ("ASL_INFERENCE___choose_constants___ONE",
``!f lock_env penv P prog prog2 Q e L c.
IS_SEPARATION_COMBINATOR f /\
(!s. s IN P ==> (e s = SOME c)) /\
(!s1 s2. (e s1 = SOME c) /\ ASL_IS_SUBSTATE f s1 s2 ==> (e s2 = SOME c)) ==>
(ASL_PROGRAM_HOARE_TRIPLE (f, lock_env) penv P
   (asl_prog_seq (asl_prog_choose_constants prog (e::L)) prog2) Q =
 ASL_PROGRAM_HOARE_TRIPLE (f, lock_env) penv P
   (asl_prog_seq (asl_prog_choose_constants (\L. prog (c::L)) L) prog2) Q)``,

SIMP_TAC list_ss [asl_prog_choose_constants_def, IMAGE_ABS,
   LENGTH_EQ_NUM, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, asl_pred_bigand_def,
   ASL_PROGRAM_HOARE_TRIPLE_def,
   HOARE_TRIPLE_def, ASL_PROGRAM_SEM___prog_seq] THEN
REPEAT STRIP_TAC THEN
CONSEQ_CONV_TAC (K FORALL_EQ___CONSEQ_CONV) THEN
GEN_TAC THEN Cases_on `s IN P` THEN ASM_REWRITE_TAC[] THEN
MATCH_MP_TAC (prove (``(p s = p' s) ==>
   ((fasl_order ((asla_seq p a) s) Q) = (fasl_order ((asla_seq p' a) s) Q))``, SIMP_TAC std_ss [asla_seq_def])) THEN
SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_ndet,
   IMAGE_ABS, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
   SUP_fasl_action_order_def] THEN
MATCH_MP_TAC SUP_fasl_order___EQ_INSERT_DIVERGE THEN

ONCE_REWRITE_TAC[EXTENSION] THEN
GEN_TAC THEN EQ_TAC THEN
SIMP_TAC std_ss [IN_INSERT, IN_ABS, DISJ_IMP_THM, GSYM LEFT_FORALL_IMP_THM] THENL [
   REPEAT STRIP_TAC THEN
   DISJ2_TAC THEN
   Q.EXISTS_TAC `c` THEN Q.EXISTS_TAC `L'` THEN
   ASM_SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_seq] THEN
   MATCH_MP_TAC (prove (``(a1 s = a1' s) ==> (asla_seq a1 a2 s = asla_seq a1' a2 s)``,
      SIMP_TAC std_ss [asla_seq_def])) THEN

   ASM_SIMP_TAC std_ss [ASL_PROGRAM_SEM___prim_command,
      ASL_ATOMIC_ACTION_SEM_def, EVAL_asl_prim_command_THM] THEN
   Q.ABBREV_TAC `restPred = MAP (\x. asl_pred_prim (\f s. FST x s = SOME (SND x))) (ZIP (L,L'))` THEN
   ASM_SIMP_TAC std_ss [EVAL_asl_predicate___pred_bigand,
      ASL_IS_INTUITIONISTIC___REWRITE, IN_ABS,
      EVAL_asl_predicate_def, asla_assume_def] THEN
   ASM_REWRITE_TAC[] THEN
   ASM_SIMP_TAC std_ss [IN_ABS, ASL_INTUITIONISTIC_NEGATION_REWRITE,
      asl_bool_EVAL] THEN
   METIS_TAC[],


   REPEAT STRIP_TAC THEN
   Q.ABBREV_TAC `restPred = MAP (\x. asl_pred_prim (\f s. FST x s = SOME (SND x))) (ZIP (L,l'))` THEN
   Tactical.REVERSE (Cases_on `h = c`) THENL [
      DISJ1_TAC THEN
      SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_seq] THEN
      MATCH_MP_TAC (prove (``(a1 s = SOME EMPTY) ==> (asla_seq a1 a2 s = SOME EMPTY)``,
    SIMP_TAC std_ss [asla_seq_def, IMAGE_EMPTY, SUP_fasl_order_def,
       NOT_IN_EMPTY, BIGUNION_EMPTY])) THEN
      ASM_SIMP_TAC std_ss [ASL_PROGRAM_SEM___prim_command,
    ASL_ATOMIC_ACTION_SEM_def, EVAL_asl_prim_command_THM,
    EVAL_asl_predicate___pred_bigand] THEN
      ASM_SIMP_TAC std_ss [asla_assume_def, EVAL_asl_predicate_def,
    ASL_IS_INTUITIONISTIC___REWRITE, IN_ABS, asl_bool_EVAL] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC std_ss [IN_ABS, ASL_INTUITIONISTIC_NEGATION_REWRITE,
    asl_bool_EVAL, COND_RAND, COND_RATOR] THEN
      REPEAT STRIP_TAC THEN
      `e s2 = SOME c` by PROVE_TAC[] THEN
      ASM_SIMP_TAC std_ss [],


      DISJ2_TAC THEN
      Q.EXISTS_TAC `l'` THEN
      ASM_SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_seq] THEN
      MATCH_MP_TAC (prove (``(a1 s = a1' s) ==> (asla_seq a1 a2 s = asla_seq a1' a2 s)``,
    SIMP_TAC std_ss [asla_seq_def])) THEN

      ASM_SIMP_TAC std_ss [ASL_PROGRAM_SEM___prim_command,
    ASL_ATOMIC_ACTION_SEM_def, EVAL_asl_prim_command_THM] THEN
      ASM_SIMP_TAC std_ss [EVAL_asl_predicate___pred_bigand,
    ASL_IS_INTUITIONISTIC___REWRITE, IN_ABS,
    EVAL_asl_predicate_def, asla_assume_def] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC std_ss [IN_ABS, ASL_INTUITIONISTIC_NEGATION_REWRITE,
    asl_bool_EVAL] THEN
      PROVE_TAC[]
   ]
]);




val ASL_INFERENCE___choose_constants___LIST =
store_thm ("ASL_INFERENCE___choose_constants___LIST",
``!f lock_env penv P Q L2 prog2 cL prog L1.
IS_SEPARATION_COMBINATOR f /\
(LENGTH cL = LENGTH L1) /\
EVERY (\ (e,c).
   (!s. s IN P ==> (e s = SOME c)) /\
   (!s1 s2. (e s1 = SOME c) /\ ASL_IS_SUBSTATE f s1 s2 ==> (e s2 = SOME c)))
   (ZIP (L1, cL)) ==>

(ASL_PROGRAM_HOARE_TRIPLE (f, lock_env) penv P
   (asl_prog_seq (asl_prog_choose_constants prog (L1++L2)) prog2) Q =
ASL_PROGRAM_HOARE_TRIPLE (f, lock_env) penv P
   (asl_prog_seq (asl_prog_choose_constants (\L. prog (cL++L)) L2) prog2) Q)``,

NTAC 7 GEN_TAC THEN
Induct_on `L1` THEN1 (
   SIMP_TAC list_ss [LENGTH_NIL, ETA_THM]
) THEN
REPEAT STRIP_TAC THEN
Cases_on `cL` THEN FULL_SIMP_TAC list_ss [] THEN


MP_TAC (Q.SPECL [`f`, `lock_env`, `penv`, `P`, `prog`, `prog2`, `Q`, `h`, `L1++L2`, `h'`]
       ASL_INFERENCE___choose_constants___ONE) THEN
ASM_SIMP_TAC std_ss [] THEN ASM_REWRITE_TAC[] THEN
SIMP_TAC std_ss [] THEN
DISCH_TAC THEN (POP_ASSUM (K ALL_TAC)) THEN

Q.PAT_ASSUM `!cL prog. (X ==> (Y <=> Z))` (MP_TAC o Q.SPECL [`t`]) THEN
ASM_REWRITE_TAC[] THEN
SIMP_TAC std_ss []);





val ASL_INFERENCE___choose_constants =
store_thm ("ASL_INFERENCE___choose_constants",
``!f lock_env penv P Q L cL prog prog2.
IS_SEPARATION_COMBINATOR f /\
(LENGTH cL = LENGTH L) /\
EVERY (\ (e,c).
   (!s. s IN P ==> (e s = SOME c)) /\
   (!s1 s2. (e s1 = SOME c) /\ ASL_IS_SUBSTATE f s1 s2 ==> (e s2 = SOME c)))
   (ZIP (L, cL)) ==>

(ASL_PROGRAM_HOARE_TRIPLE (f, lock_env) penv P
   (asl_prog_seq (asl_prog_choose_constants prog L) prog2) Q =
ASL_PROGRAM_HOARE_TRIPLE (f, lock_env) penv P
   (asl_prog_seq (prog cL) prog2) Q)``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`f`, `lock_env`, `penv`, `P`, `Q`, `[]`, `prog2`, `cL`, `prog`, `L`]
ASL_INFERENCE___choose_constants___LIST) THEN
ASM_SIMP_TAC list_ss [ASL_INFERENCE___choose_constants___NIL]);







(******************************************************************************)
(* Strongest post, weakest preconditions                                      *)
(******************************************************************************)

val asl_slp_opt_def = Define `
asl_slp_opt xenv penv P prog =
let Qset = (\Q. ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog Q) in
if Qset = EMPTY then NONE else SOME (BIGINTER Qset)`;


val asl_slp_opt_THM = store_thm ("asl_slp_opt_THM",
``!xenv penv P prog slp.
     ((ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog slp) /\
      (!Q. (ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog Q) ==>
      (slp SUBSET Q))) = (SOME slp = asl_slp_opt xenv penv P prog)``,

REPEAT STRIP_TAC THEN
EQ_TAC THEN STRIP_TAC THENL [
   ASM_SIMP_TAC std_ss [asl_slp_opt_def, EXTENSION, IN_BIGINTER,
      IN_ABS, LET_THM, NOT_IN_EMPTY] THEN
   CONJ_TAC THEN1 METIS_TAC[] THEN
   METIS_TAC[SUBSET_DEF],

   FULL_SIMP_TAC std_ss [asl_slp_opt_def, LET_THM] THEN
   Q.PAT_ASSUM `X = slp` (ASSUME_TAC o GSYM) THEN
   FULL_SIMP_TAC std_ss [GSYM MEMBER_NOT_EMPTY, IN_ABS] THEN
   CONJ_TAC THENL [
       FULL_SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
      SUBSET_DEF, IN_BIGINTER, IN_ABS] THEN
       METIS_TAC[SOME_11],

       REPEAT STRIP_TAC THEN
       SIMP_TAC std_ss [SUBSET_DEF, IN_BIGINTER, IN_ABS] THEN
       METIS_TAC[]
   ]
]);



val ASL_INFERENCE_slp = store_thm ("ASL_INFERENCE_slp",
``!xenv penv P Q p1 p2.   
   (ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_seq p1 p2) Q =
    (?slp. (asl_slp_opt xenv penv P p1 = SOME slp) /\
    ASL_PROGRAM_HOARE_TRIPLE xenv penv slp p2 Q))``,

SIMP_TAC std_ss [ASL_INFERENCE_prog_seq_STRONG] THEN
REPEAT STRIP_TAC THEN
Cases_on `asl_slp_opt xenv penv P p1` THEN1 (
   FULL_SIMP_TAC std_ss [asl_slp_opt_def, LET_THM,
         EXTENSION, NOT_IN_EMPTY, IN_ABS]
) THEN
FULL_SIMP_TAC std_ss [GSYM asl_slp_opt_THM] THEN
EQ_TAC THEN STRIP_TAC THENL [
   MATCH_MP_TAC ASL_INFERENCE_STRENGTHEN THEN
   METIS_TAC[SUBSET_REFL],

   METIS_TAC[]
]);


val ASL_INFERENCE_slp___IMP = store_thm ("ASL_INFERENCE_slp___IMP",

``!xenv penv P Q p1 p2 slp.
   ((asl_slp_opt xenv penv P p1 = SOME slp) /\
    ASL_PROGRAM_HOARE_TRIPLE xenv penv slp p2 Q) ==>

   (ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_seq p1 p2) Q)``,

METIS_TAC[ASL_INFERENCE_slp]);



val asl_slp_opt___asl_false = store_thm ("asl_slp_opt___asl_false",
``asl_slp_opt xenv penv (asl_false) P = SOME (asl_false)``,

SIMP_TAC std_ss [asl_slp_opt_def, ASL_PROGRAM_HOARE_TRIPLE_REWRITE, asl_false_def,
       NOT_IN_EMPTY, LET_THM, EXTENSION, IN_ABS, IN_BIGINTER] THEN
GEN_TAC THEN
Q.EXISTS_TAC `EMPTY` THEN
REWRITE_TAC [NOT_IN_EMPTY]);



val asl_slp_opt___EMPTY_PROG = store_thm ("asl_slp_opt___EMPTY_PROG",
``asl_slp_opt xenv penv P {} = SOME (asl_false)``,

SIMP_TAC std_ss [asl_slp_opt_def, ASL_PROGRAM_HOARE_TRIPLE_REWRITE, ASL_PROGRAM_TRACES_def,
       IMAGE_EMPTY, BIGUNION_EMPTY, NOT_IN_EMPTY,
       LET_THM, EXTENSION, IN_ABS, IN_BIGINTER, asl_false_def] THEN
GEN_TAC THEN
Q.EXISTS_TAC `EMPTY` THEN
REWRITE_TAC [NOT_IN_EMPTY]);


val asl_prog_ndet___HOARE_TRIPLE = store_thm ("asl_prog_ndet___HOARE_TRIPLE",
``ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_ndet pset) Q =
(!prog. prog IN pset ==> ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog Q)``,


SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
       ASL_PROGRAM_TRACES___prog_ndet, IN_BIGUNION,
       IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
METIS_TAC[]);



val asl_slp_opt___prog_ndet = store_thm ("asl_slp_opt___prog_ndet",
``
!xenv penv P pset.
asl_slp_opt xenv penv P (asl_prog_ndet pset) =
if (!prog. (prog IN pset) ==> IS_SOME (asl_slp_opt xenv penv P prog)) then
SOME (BIGUNION (IMAGE (\prog. THE (asl_slp_opt xenv penv P prog)) pset))
else
NONE``,

SIMP_TAC std_ss [COND_RATOR, COND_RAND, COND_EXPAND_IMP] THEN
Tactical.REVERSE (REPEAT STRIP_TAC) THEN1 (
   FULL_SIMP_TAC std_ss [asl_slp_opt_def, ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
         ASL_PROGRAM_TRACES___prog_ndet, LET_THM, COND_RAND, COND_RATOR] THEN
   FULL_SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY] THEN
   FULL_SIMP_TAC std_ss [IN_ABS, IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
   METIS_TAC[]
) THEN

SIMP_TAC std_ss [asl_slp_opt_def, asl_prog_ndet___HOARE_TRIPLE, LET_THM] THEN
SIMP_TAC std_ss [LET_THM, COND_RATOR, COND_RAND, EXTENSION] THEN
SIMP_TAC std_ss [IN_ABS, NOT_IN_EMPTY] THEN
MATCH_MP_TAC (prove (``(A /\ (A ==> B)) ==> (A /\ B)``, PROVE_TAC[])) THEN
CONJ_TAC THEN1 (
   Q.EXISTS_TAC `UNIV` THEN
   FULL_SIMP_TAC std_ss [asl_slp_opt_def, ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
          LET_THM, COND_RAND, COND_RATOR, EXTENSION, NOT_IN_EMPTY, IN_ABS,
          SUBSET_UNIV] THEN
   METIS_TAC[]
) THEN
STRIP_TAC THEN

SIMP_TAC std_ss [IN_BIGINTER, IN_ABS, IN_BIGUNION, IN_IMAGE, COND_RATOR, COND_RAND,
       GSYM RIGHT_EXISTS_AND_THM] THEN
GEN_TAC THEN
HO_MATCH_MP_TAC (prove (``((!prog s. (B s prog \/ C s prog) ==> ~(P prog)) /\ (A = ?s prog. (C s prog))) ==>
             (A = (?s prog. if P prog then B s prog else C s prog))``, METIS_TAC[])) THEN
CONJ_TAC THEN1 METIS_TAC[] THEN

SIMP_TAC std_ss [IN_BIGINTER, IN_ABS] THEN
Tactical.REVERSE (EQ_TAC THEN STRIP_TAC) THEN1 (
   METIS_TAC[]
) THEN

`x' IN (BIGUNION (IMAGE (\prog. THE (asl_slp_opt xenv penv P prog)) pset))` by ALL_TAC THEN1 (
   Q.PAT_ASSUM `!P'. X P'` MATCH_MP_TAC THEN
   REPEAT STRIP_TAC THEN
   `?slp. asl_slp_opt xenv penv P prog = SOME slp` by ALL_TAC THEN1 (
      RES_TAC THEN
      FULL_SIMP_TAC std_ss [IS_SOME_EXISTS]
   ) THEN
   `ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog slp` by PROVE_TAC[asl_slp_opt_THM] THEN
   MATCH_MP_TAC ASL_INFERENCE_STRENGTHEN THEN
   Q.EXISTS_TAC `P` THEN
   Q.EXISTS_TAC `slp` THEN
   ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `prog` THEN
   ASM_SIMP_TAC std_ss []
) THEN
FULL_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE] THEN
Q.EXISTS_TAC `prog` THEN
ASM_SIMP_TAC std_ss [] THEN
REPEAT STRIP_TAC THEN
`asl_slp_opt xenv penv P prog = SOME s` by ALL_TAC THEN1 (
   RES_TAC THEN
   FULL_SIMP_TAC std_ss [IS_SOME_EXISTS]
) THEN
FULL_SIMP_TAC std_ss [GSYM asl_slp_opt_THM] THEN
`s SUBSET P'` by PROVE_TAC[] THEN
FULL_SIMP_TAC std_ss [SUBSET_DEF]);




val asl_slp_opt___prog_assume = store_thm ("asl_slp_opt___prog_assume",
``!xenv penv P c. 
  IS_SEPARATION_COMBINATOR (FST xenv) ==>

  (asl_slp_opt xenv penv P (asl_prog_assume c) = 
   if (asl_predicate_IS_DECIDED (FST xenv) P c) then
   SOME (asl_and P (EVAL_asl_predicate (FST xenv) c)) else NONE)``,

SIMP_TAC std_ss [asl_slp_opt_def, ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___assume, HOARE_TRIPLE_def,
   fasl_order_THM, asla_assume_def] THEN
REPEAT STRIP_TAC THEN
Q.ABBREV_TAC `cc = EVAL_asl_predicate (FST xenv) c` THEN
SIMP_TAC (std_ss++LIFT_COND_ss) [] THEN
ASM_SIMP_TAC std_ss [COND_EXPAND_IMP, asl_predicate_IS_DECIDED_def,
   FORALL_AND_THM, EMPTY_SUBSET, SUBSET_DEF, IN_SING,
   EVAL_asl_predicate_def, LET_THM] THEN

Q.HO_MATCH_ABBREV_TAC `Y1 /\ (Y2 ==> (qset = Y3))` THEN
MAP_EVERY Q.UNABBREV_TAC [`Y1`, `Y2`, `Y3`] THEN
CONJ_TAC THEN STRIP_TAC THENL [
   `qset = \Q. asl_and P cc SUBSET Q` by ALL_TAC THEN1 (
       Q.UNABBREV_TAC `qset` THEN
       SIMP_TAC std_ss [EXTENSION, IN_ABS, SUBSET_DEF, asl_bool_EVAL] THEN
       METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC std_ss [EXTENSION, IN_ABS, IN_BIGINTER, NOT_IN_EMPTY,
       SUBSET_DEF] THEN
   METIS_TAC[],

   Q.UNABBREV_TAC `qset` THEN
   SIMP_TAC std_ss [EXTENSION, IN_ABS, NOT_IN_EMPTY] THEN
   METIS_TAC[]
]);


val ASL_INFERENCE_assume_seq_STRONG = store_thm ("ASL_INFERENCE_assume_seq_STRONG",
``!xenv penv P prog Q c.
  IS_SEPARATION_COMBINATOR (FST xenv) ==>

 (ASL_PROGRAM_HOARE_TRIPLE xenv penv P
    (asl_prog_seq (asl_prog_prim_command (asl_pc_assume c)) prog) Q =
  (asl_predicate_IS_DECIDED (FST xenv) P c /\
   ASL_PROGRAM_HOARE_TRIPLE xenv penv
     (asl_and P (EVAL_asl_predicate (FST xenv) c)) prog Q))``,

SIMP_TAC std_ss [ASL_INFERENCE_slp,
   asl_slp_opt___prog_assume, GSYM asl_prog_assume_def]);


val asl_slp_opt___prog_seq = store_thm ("asl_slp_opt___prog_seq",
``!xenv penv P p1 p2. 
  IS_SEPARATION_COMBINATOR (FST xenv) ==>

  (asl_slp_opt xenv penv P (asl_prog_seq p1 p2) = 
   let P1_opt = asl_slp_opt xenv penv P p1 in
   if IS_SOME P1_opt then 
      asl_slp_opt xenv penv (THE P1_opt) p2
   else NONE)``,

REPEAT STRIP_TAC THEN
Cases_on `asl_slp_opt xenv penv P p1` THEN1 (
   FULL_SIMP_TAC std_ss [asl_slp_opt_def,
      ASL_INFERENCE_prog_seq_STRONG, LET_THM, EXTENSION, 
      IN_ABS, NOT_IN_EMPTY]
) THEN
FULL_SIMP_TAC std_ss [GSYM asl_slp_opt_THM, LET_THM] THEN
Cases_on `asl_slp_opt xenv penv x p2` THEN1 (
   FULL_SIMP_TAC std_ss [asl_slp_opt_def,
      ASL_INFERENCE_prog_seq_STRONG,
      LET_THM, EXTENSION, IN_ABS, NOT_IN_EMPTY] THEN
   METIS_TAC[ASL_INFERENCE_STRENGTHEN, SUBSET_REFL]
) THEN
   
FULL_SIMP_TAC std_ss [GSYM asl_slp_opt_THM,
   ASL_INFERENCE_prog_seq_STRONG] THEN
METIS_TAC[ASL_INFERENCE_STRENGTHEN, SUBSET_REFL]);




val asl_wlp_def = Define `
asl_wlp xenv penv prog Q =
BIGUNION (\P. ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog Q)`

val asl_wlp_THM = store_thm ("asl_wlp_THM",
   ``!xenv penv Q prog wlp.
       ((ASL_PROGRAM_HOARE_TRIPLE xenv penv wlp prog Q) /\
        (!P. (ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog Q) ==>
          (P SUBSET wlp))) = (wlp = asl_wlp xenv penv prog Q)``,

REPEAT STRIP_TAC THEN
EQ_TAC THEN STRIP_TAC THENL [
   FULL_SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_REWRITE, asl_wlp_def,
      EXTENSION, IN_BIGUNION, IN_ABS] THEN
   GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Q.EXISTS_TAC `{x}` THEN
      SIMP_TAC std_ss [IN_SING] THEN
      METIS_TAC[],

      `s SUBSET wlp` by METIS_TAC[] THEN
      FULL_SIMP_TAC std_ss [SUBSET_DEF]
   ],


   ASM_SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_REWRITE,
      asl_wlp_def, IN_BIGUNION, IN_ABS, SUBSET_DEF] THEN
   REPEAT STRIP_TAC THENL [
      METIS_TAC[],

      Q.EXISTS_TAC `{x}` THEN
      SIMP_TAC std_ss [IN_SING] THEN
      METIS_TAC[]
   ]
]);






val ASL_INFERENCE_wlp = store_thm ("ASL_INFERENCE_wlp",

``!xenv penv P Q p1 p2.
   (ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_seq p1 p2) Q =
   ASL_PROGRAM_HOARE_TRIPLE xenv penv P p1 (asl_wlp xenv penv p2 Q))``,

REPEAT STRIP_TAC THEN
Tactical.REVERSE EQ_TAC THENL [
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC ASL_INFERENCE_prog_seq THEN
   Q.EXISTS_TAC `asl_wlp xenv penv p2 Q` THEN
   ASM_REWRITE_TAC[] THEN
   METIS_TAC[asl_wlp_THM],


   FULL_SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_def,
      ASL_PROGRAM_SEM___prog_seq, asl_wlp_def,
      HOARE_TRIPLE_def, fasl_order_THM, SOME___asla_seq,
      GSYM LEFT_EXISTS_AND_THM, IN_IMAGE,
      GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM,
      asl_wlp_def, SUBSET_DEF, IN_BIGUNION, IN_ABS] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `!s. s IN P ==> X` (MP_TAC o Q.SPEC `s`) THEN
   ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   ASM_SIMP_TAC std_ss [] THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `s1'` THEN
   ASM_SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC THEN
   METIS_TAC[option_CLAUSES]
]);



val ASL_INFERENCE_wlp___IMP = store_thm ("ASL_INFERENCE_wlp___IMP",
``!xenv penv P Q p1 p2.
    ASL_PROGRAM_HOARE_TRIPLE xenv penv P p1 (asl_wlp xenv penv p2 Q) ==>
    ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_seq p1 p2) Q``,

METIS_TAC[ASL_INFERENCE_wlp]);



val asl_wlp___prog_seq = store_thm ("asl_wlp___prog_seq",
``!xenv penv Q p1 p2. 
  IS_SEPARATION_COMBINATOR (FST xenv) ==>

  (asl_wlp xenv penv (asl_prog_seq p1 p2) Q = 
   asl_wlp xenv penv p1 (asl_wlp xenv penv p2 Q))``,

REPEAT STRIP_TAC THEN
Q.ABBREV_TAC `wlp2 = asl_wlp xenv penv p2 Q` THEN
Q.ABBREV_TAC `wlp1 = asl_wlp xenv penv p1 wlp2` THEN
FULL_SIMP_TAC std_ss [GSYM asl_wlp_THM,
   ASL_INFERENCE_prog_seq_STRONG] THEN
FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def] THEN
METIS_TAC[ASL_INFERENCE_STRENGTHEN, SUBSET_REFL]);



val asl_wlp___prog_asssume = store_thm ("asl_wlp___prog_assume",
``!xenv penv Q c. 
  IS_SEPARATION_COMBINATOR (FST xenv) ==>

  (asl_wlp xenv penv (asl_prog_assume c) Q = 
   \s. s IN EVAL_asl_predicate (FST xenv) (asl_pred_neg c) \/
       (s IN Q /\ s IN EVAL_asl_predicate (FST xenv) c))``,

SIMP_TAC std_ss [asl_wlp_def,
   ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___assume,
   HOARE_TRIPLE_def, fasl_order_THM,
   asla_assume_def] THEN
SIMP_TAC std_ss [EXTENSION, IN_BIGUNION] THEN
REPEAT STRIP_TAC THEN
SIMP_TAC (std_ss++LIFT_COND_ss) [IN_ABS, SUBSET_DEF, IN_SING, NOT_IN_EMPTY,
   EVAL_asl_predicate_def] THEN
EQ_TAC THENL [
   STRIP_TAC THEN
   Q.PAT_ASSUM `!s'. X s'` (MP_TAC o Q.SPEC `x`) THEN
   ASM_SIMP_TAC std_ss [COND_EXPAND_OR, DISJ_IMP_THM],

   DISCH_TAC THEN
   Q.EXISTS_TAC `{x}` THEN
   SIMP_TAC std_ss [IN_SING, COND_EXPAND_IMP, AND_IMP_INTRO,
      FORALL_AND_THM] THEN
   FULL_SIMP_TAC std_ss [] THEN
   METIS_TAC[ASL_INTUITIONISTIC_NEGATION_IMP,
      ASL_IS_INTUITIONISTIC___EVAL_asl_predicate]
]);



(******************************************************************************)
(* Program abstractions                                                       *)
(******************************************************************************)


val ASL_PROGRAM_IS_ABSTRACTION_def = Define `
    ASL_PROGRAM_IS_ABSTRACTION xenv penv prog1 prog2 =
    fasl_action_order (ASL_PROGRAM_SEM xenv penv prog1)
            (ASL_PROGRAM_SEM xenv penv prog2)`;

val ASL_PROGRAM_IS_ABSTRACTION___ALTERNATIVE_DEF = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___ALTERNATIVE_DEF",

``ASL_PROGRAM_IS_ABSTRACTION xenv penv prog1 prog2 =
  !P Q. ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog2 Q ==>
   ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog1 Q``,

SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
       ASL_PROGRAM_HOARE_TRIPLE_def,
       fasl_action_order_def]);



val ASL_PROGRAM_IS_ABSTRACTION___IS_PREORDER = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___IS_PREORDER",
``PreOrder (ASL_PROGRAM_IS_ABSTRACTION xenv penv)``,

SIMP_TAC std_ss [PreOrder, reflexive_def, transitive_def,
       ASL_PROGRAM_IS_ABSTRACTION___ALTERNATIVE_DEF]);



val ASL_PROGRAM_IS_ABSTRACTION___REFL = store_thm ("ASL_PROGRAM_IS_ABSTRACTION___REFL",
``!xenv penv p. ASL_PROGRAM_IS_ABSTRACTION xenv penv p p``,
SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___ALTERNATIVE_DEF]);


val ASL_PROGRAM_IS_ABSTRACTION___TRANSITIVE = store_thm ("ASL_PROGRAM_IS_ABSTRACTION___TRANSITIVE",
``!xenv penv p1 p2 p3.
    ASL_PROGRAM_IS_ABSTRACTION xenv penv p1 p2 ==>
    ASL_PROGRAM_IS_ABSTRACTION xenv penv p2 p3 ==>
    ASL_PROGRAM_IS_ABSTRACTION xenv penv p1 p3``,
SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___ALTERNATIVE_DEF]);


val ASL_PROGRAM_IS_ABSTRACTION___SEM_REFL = store_thm ("ASL_PROGRAM_IS_ABSTRACTION___SEM_REFL",
``!xenv penv p1 p2.
(ASL_PROGRAM_SEM xenv penv p1 = ASL_PROGRAM_SEM xenv penv p2) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv p1 p2``,

SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___ALTERNATIVE_DEF,
       ASL_PROGRAM_HOARE_TRIPLE_def]);


val COND_HOARE_TRIPLE_ABSTRACTION___INTRO = store_thm (
"COND_HOARE_TRIPLE_ABSTRACTION___INTRO",
``!xenv penv P prog1 Q prog2.
ASL_PROGRAM_IS_ABSTRACTION xenv penv prog1 prog2 ==>
COND_HOARE_TRIPLE P (ASL_PROGRAM_SEM xenv penv prog2) Q ==>
COND_HOARE_TRIPLE P (ASL_PROGRAM_SEM xenv penv prog1) Q``,

Cases_on `P` THEN Cases_on `Q` THEN
SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___ALTERNATIVE_DEF,
   COND_HOARE_TRIPLE_def, ASL_PROGRAM_HOARE_TRIPLE_def]);



val ASL_PROGRAM_IS_ABSTRACTION___diverge =
store_thm ("ASL_PROGRAM_IS_ABSTRACTION___diverge",
``!xenv penv prog.
   ASL_PROGRAM_IS_ABSTRACTION xenv penv
    asl_prog_diverge prog``,
SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
   fasl_action_order_POINTWISE_DEF,
   ASL_PROGRAM_SEM___diverge, asla_diverge_def,
   fasl_order_THM2, EMPTY_SUBSET]);



val ASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action",
``!xenv penv P prog Q.
 IS_SEPARATION_COMBINATOR (FST xenv) ==>

(ASL_PROGRAM_IS_ABSTRACTION xenv penv prog (asl_prog_quant_best_local_action P Q) =
(!arg. ASL_PROGRAM_HOARE_TRIPLE xenv penv (P arg) prog (Q arg)))``,

REPEAT GEN_TAC THEN
`?f lock_env. xenv = (f, lock_env)` by (Cases_on `xenv` THEN SIMP_TAC std_ss []) THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
       asl_prog_quant_best_local_action_def,
       ASL_PROGRAM_HOARE_TRIPLE_def,
       ASL_PROGRAM_SEM___prim_command,
       ASL_ATOMIC_ACTION_SEM_def,
       EVAL_asl_prim_command_THM] THEN
REPEAT STRIP_TAC THEN
MP_TAC (ISPECL [``f:'a bin_option_function``,
      ``P :'e -> 'a -> bool``,
      ``Q :'e -> 'a -> bool``] quant_best_local_action_THM) THEN
ASM_SIMP_TAC std_ss [fasl_action_order_def] THEN
REPEAT STRIP_TAC THEN
METIS_TAC[ASL_IS_LOCAL_ACTION___ASL_PROGRAM_SEM, pairTheory.FST]);



val ASL_PROGRAM_IS_ABSTRACTION___best_local_action = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___best_local_action",
``!xenv penv P prog Q.
 IS_SEPARATION_COMBINATOR (FST xenv) ==>
(ASL_PROGRAM_IS_ABSTRACTION xenv penv prog (asl_prog_best_local_action P Q) =
 ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog Q)``,

REPEAT STRIP_TAC THEN
MP_TAC (Q.SPECL [`xenv`, `penv`, `K P`, `prog`, `K Q`] ASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action) THEN
ASM_SIMP_TAC std_ss [GSYM asl_prog_best_local_action___ALTERNATIVE_DEF]);





val ASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action2 = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action2",
``!xenv penv P prog Q.
 IS_SEPARATION_COMBINATOR (FST xenv) ==>
(ASL_PROGRAM_IS_ABSTRACTION xenv penv prog (asl_prog_quant_best_local_action P Q) =
 (!arg. ASL_PROGRAM_IS_ABSTRACTION xenv penv prog (asl_prog_best_local_action (P arg) (Q arg))))``,


METIS_TAC[ASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action,
     ASL_PROGRAM_IS_ABSTRACTION___best_local_action]);





val ASLA_PROGRAM_IS_ABSTRACTION___DIVERGE_THM1 =
store_thm ("ASLA_PROGRAM_IS_ABSTRACTION___DIVERGE_THM1",
``!xenv penv prog prog'.
(ASL_PROGRAM_SEM xenv penv prog = asla_diverge) ==>

 (ASL_PROGRAM_IS_ABSTRACTION xenv penv prog prog')``,

SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF, asla_diverge_def,
            fasl_order_THM, EMPTY_SUBSET] THEN
GEN_TAC THEN
Cases_on `ASL_PROGRAM_SEM xenv penv prog' s` THEN
SIMP_TAC std_ss []);




val ASLA_PROGRAM_IS_ABSTRACTION___DIVERGE_THM2 =
store_thm ("ASLA_PROGRAM_IS_ABSTRACTION___DIVERGE_THM2",
``!xenv penv prog prog'.
(ASL_PROGRAM_SEM xenv penv prog' = asla_diverge) /\
(ASL_PROGRAM_IS_ABSTRACTION xenv penv prog prog') ==>

(ASL_PROGRAM_SEM xenv penv prog = asla_diverge)``,


SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `X = asla_diverge` ASSUME_TAC THEN
FULL_SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF, asla_diverge_def,
            fasl_order_THM, SUBSET_EMPTY] THEN
ASM_SIMP_TAC std_ss [FUN_EQ_THM]);





val ASL_PROGRAM_IS_ABSTRACTION___seq = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___seq",
``!xenv penv prog1 prog1' prog2 prog2'.
(ASL_PROGRAM_IS_ABSTRACTION xenv penv prog1 prog1' /\
ASL_PROGRAM_IS_ABSTRACTION xenv penv prog2 prog2') ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv (asl_prog_seq prog1 prog2) (asl_prog_seq prog1' prog2')``,


REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
            ASL_PROGRAM_SEM___prog_seq] THEN
METIS_TAC[asla_seq___ACTION_ORDER]);




val ASL_PROGRAM_IS_ABSTRACTION___parallel =
store_thm ("ASL_PROGRAM_IS_ABSTRACTION___parallel",
``!xenv penv p1 p2 qP1 qP2 qQ1 qQ2.
(IS_SEPARATION_COMBINATOR (FST xenv)) /\
ASL_PROGRAM_IS_ABSTRACTION xenv penv p1 (asl_prog_quant_best_local_action qP1 qQ1) /\
ASL_PROGRAM_IS_ABSTRACTION xenv penv p2 (asl_prog_quant_best_local_action qP2 qQ2) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv (asl_prog_parallel p1 p2)
 (asl_prog_quant_best_local_action
    (\ (a1, a2). asl_star (FST xenv) (qP1 a1) (qP2 a2))
    (\ (a1, a2). asl_star (FST xenv) (qQ1 a1) (qQ2 a2)))``,

REPEAT GEN_TAC THEN
Cases_on `IS_SEPARATION_COMBINATOR (FST xenv)` THEN ASM_REWRITE_TAC[] THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action] THEN
REPEAT STRIP_TAC THEN
`?a1 a2. arg = (a1, a2)` by (Cases_on `arg` THEN SIMP_TAC std_ss []) THEN
ASM_SIMP_TAC std_ss [] THEN
MATCH_MP_TAC ASL_INFERENCE_prog_parallel THEN
ASM_SIMP_TAC std_ss []);



val ASL_PROGRAM_IS_ABSTRACTION___block = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___block",
``!xenv penv p1 pL p1' pL'.
ASL_PROGRAM_IS_ABSTRACTION xenv penv p1 p1' ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv (asl_prog_block pL) (asl_prog_block pL') ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv (asl_prog_block (p1::pL))
                  (asl_prog_block (p1'::pL'))``,

SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
       ASL_PROGRAM_SEM___prog_block] THEN
METIS_TAC[asla_seq___ACTION_ORDER]);




val ASL_PROGRAM_IS_ABSTRACTION___choice = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___choice",
``!xenv penv prog1 prog1' prog2 prog2'.
(ASL_PROGRAM_IS_ABSTRACTION xenv penv prog1 prog1' /\
ASL_PROGRAM_IS_ABSTRACTION xenv penv prog2 prog2') ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv (asl_prog_choice prog1 prog2) (asl_prog_choice prog1' prog2')``,


REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
            ASL_PROGRAM_SEM___prog_choice] THEN
Q.ABBREV_TAC `a1 = ASL_PROGRAM_SEM xenv penv prog1` THEN
Q.ABBREV_TAC `a1' = ASL_PROGRAM_SEM xenv penv prog1'` THEN
Q.ABBREV_TAC `a2 = ASL_PROGRAM_SEM xenv penv prog2` THEN
Q.ABBREV_TAC `a2' = ASL_PROGRAM_SEM xenv penv prog2'` THEN

FULL_SIMP_TAC std_ss [fasl_action_order_POINTWISE_DEF,
            asla_bin_choice_THM] THEN
GEN_TAC THEN
REPEAT (Q.PAT_ASSUM `!s. X s` (MP_TAC o Q.SPEC `s`)) THEN
Cases_on `a1' s` THEN1 SIMP_TAC std_ss [fasl_order_THM] THEN
Cases_on `a2' s` THEN1 SIMP_TAC std_ss [fasl_order_THM] THEN

SIMP_TAC std_ss [fasl_order_THM, GSYM LEFT_FORALL_IMP_THM,
       SUBSET_DEF, IN_UNION] THEN
METIS_TAC[]);



val ASL_PROGRAM_IS_ABSTRACTION___cond = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___cond",
``!xenv penv c prog1 prog1' prog2 prog2'.
ASL_PROGRAM_IS_ABSTRACTION xenv penv prog1 prog1' ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv prog2 prog2' ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv (asl_prog_cond c prog1 prog2) (asl_prog_cond c prog1' prog2')``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [asl_prog_cond_def] THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___choice THEN
CONJ_TAC THEN (
   MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___seq THEN
   ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___REFL]
));



val ASL_PROGRAM_IS_ABSTRACTION___repeat = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___repeat",
``!xenv penv n prog prog'.
ASL_PROGRAM_IS_ABSTRACTION xenv penv prog prog' ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv (asl_prog_repeat_num n prog)
                  (asl_prog_repeat_num n prog')``,

REPEAT STRIP_TAC THEN
Induct_on `n` THEN1 (
   SIMP_TAC std_ss [asl_prog_repeat_num_def,
      ASL_PROGRAM_IS_ABSTRACTION___REFL]
) THEN
SIMP_TAC std_ss [
   ASL_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_SEM___prog_repeat,
   GSYM ASL_PROGRAM_SEM___prog_seq] THEN
SIMP_TAC std_ss [GSYM ASL_PROGRAM_IS_ABSTRACTION_def] THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___seq THEN
ASM_REWRITE_TAC[]);



val ASL_PROGRAM_IS_ABSTRACTION___kleene_star = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___kleene_star",
``!xenv penv prog prog'.
ASL_PROGRAM_IS_ABSTRACTION xenv penv prog prog' ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv (asl_prog_kleene_star prog) (asl_prog_kleene_star prog')``,

SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_SEM___prog_kleene_star,
   fasl_action_order___SUP_fasl_action_order,
   IN_IMAGE, IN_UNIV, GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC fasl_action_order___SUP_fasl_action_order___IMPL THEN
SIMP_TAC std_ss [IN_IMAGE, IN_UNIV, GSYM LEFT_EXISTS_AND_THM] THEN
GEN_TAC THEN Q.EXISTS_TAC `n` THEN
Q.SPEC_TAC (`s`, `s`) THEN
SIMP_TAC std_ss [GSYM fasl_action_order_POINTWISE_DEF] THEN
CONV_TAC (DEPTH_CONV ETA_CONV) THEN
FULL_SIMP_TAC std_ss [GSYM ASL_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_IS_ABSTRACTION___repeat]);



val ASL_PROGRAM_IS_ABSTRACTION___while = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___while",
``!xenv penv c prog prog'.
ASL_PROGRAM_IS_ABSTRACTION xenv penv prog prog' ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv (asl_prog_while c prog) (asl_prog_while c prog')``,

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [asl_prog_while_def] THEN
CONSEQ_REWRITE_TAC ([ASL_PROGRAM_IS_ABSTRACTION___seq,
           ASL_PROGRAM_IS_ABSTRACTION___kleene_star], [], []) THEN
ASM_REWRITE_TAC[ASL_PROGRAM_IS_ABSTRACTION___REFL]);




val ASL_PROGRAM_IS_ABSTRACTION___while_bla = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___while_bla",
``!xenv penv P c prog.
(asl_predicate_IS_DECIDED (FST xenv) P c /\
 IS_SEPARATION_COMBINATOR (FST xenv) /\
 ASL_PROGRAM_HOARE_TRIPLE xenv penv (asl_and P (EVAL_asl_predicate (FST xenv) c)) prog P) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv (asl_prog_while c prog)
                  (asl_prog_best_local_action P (asl_and P (EVAL_asl_predicate (FST xenv) (asl_pred_neg c))))``,


REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___best_local_action] THEN
MATCH_MP_TAC ASL_INFERENCE_prog_while THEN
ASM_REWRITE_TAC[]);





val ASL_PROGRAM_IS_ABSTRACTION___ndet_1 = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___ndet_1",
``!xenv penv pset prog.
(!prog'. prog' IN pset ==> ASL_PROGRAM_IS_ABSTRACTION xenv penv prog' prog) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv (asl_prog_ndet pset) prog``,


SIMP_TAC std_ss [
   ASL_PROGRAM_IS_ABSTRACTION_def,
   asl_prog_forall_def, GSYM asl_prog_ndet_def,
   ASL_PROGRAM_SEM___prog_ndet,
   fasl_action_order_POINTWISE_DEF,
   GSYM RIGHT_FORALL_IMP_THM] THEN
REPEAT GEN_TAC THEN
SIMP_TAC std_ss [Once SWAP_FORALL_THM] THEN
SIMP_TAC std_ss [Once (GSYM LEFT_EXISTS_IMP_THM)] THEN
Q.EXISTS_TAC `s` THEN
Cases_on `ASL_PROGRAM_SEM xenv penv prog s` THEN (
   SIMP_TAC std_ss [fasl_order_THM2]
) THEN
REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [SOME___SUP_fasl_action_order,
   IN_IMAGE, GSYM LEFT_FORALL_IMP_THM, SUBSET_DEF,
   IN_BIGUNION, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN (
   RES_TAC THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF]
));



val ASL_PROGRAM_IS_ABSTRACTION___ndet_2 = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___ndet_2",
``!xenv penv pset prog prog'.
(prog' IN pset /\ ASL_PROGRAM_IS_ABSTRACTION xenv penv prog prog') ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv prog (asl_prog_ndet pset)``,

SIMP_TAC std_ss [
   ASL_PROGRAM_IS_ABSTRACTION_def,
   asl_prog_forall_def, GSYM asl_prog_ndet_def,
   ASL_PROGRAM_SEM___prog_ndet,
   fasl_action_order_POINTWISE_DEF] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!s. X s` (MP_TAC o Q.SPEC `s`) THEN
Cases_on `ASL_PROGRAM_SEM xenv penv prog s` THENL [
   SIMP_TAC std_ss [fasl_order_THM2, NONE___SUP_fasl_action_order,
      IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM] THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `prog'` THEN
   ASM_SIMP_TAC std_ss [],

   SIMP_TAC std_ss [fasl_order_THM2, SOME___SUP_fasl_action_order,
      SUBSET_DEF, IN_BIGUNION, IN_IMAGE, IN_ABS, GSYM RIGHT_EXISTS_AND_THM,
      GSYM LEFT_EXISTS_AND_THM, GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   Q.EXISTS_TAC `prog'` THEN
   RES_TAC THEN
   FULL_SIMP_TAC std_ss [IS_SOME_EXISTS]
]);




val ASL_PROGRAM_IS_ABSTRACTION___ndet = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___ndet",
``!xenv penv pset pset'.
(!prog. prog IN pset ==> (?prog'. (prog' IN pset') /\
  ASL_PROGRAM_IS_ABSTRACTION xenv penv prog prog')) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv (asl_prog_ndet pset)
                  (asl_prog_ndet pset')``,

METIS_TAC[ASL_PROGRAM_IS_ABSTRACTION___ndet_1,
     ASL_PROGRAM_IS_ABSTRACTION___ndet_2]);




val ASL_PROGRAM_IS_ABSTRACTION___forall = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___forall",
``!xenv penv body body'.
(!arg. ASL_PROGRAM_IS_ABSTRACTION xenv penv (body arg) (body' arg)) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv (asl_prog_forall body)
                  (asl_prog_forall body')``,


REPEAT STRIP_TAC THEN
REWRITE_TAC [asl_prog_forall_def, GSYM asl_prog_ndet_def] THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___ndet THEN
SIMP_TAC std_ss [IN_IMAGE, IN_UNIV, GSYM LEFT_FORALL_IMP_THM,
       GSYM LEFT_EXISTS_AND_THM] THEN
GEN_TAC THEN
Q.EXISTS_TAC `x` THEN
ASM_REWRITE_TAC[]);


val ASL_INFERENCE_prog_while_frame = store_thm  ("ASL_INFERENCE_prog_while_frame",
``!xenv penv c P Q p pL.

IS_SEPARATION_COMBINATOR (FST xenv) /\
(!x. (ASL_PROGRAM_HOARE_TRIPLE xenv penv (P x)
   (asl_prog_block ((asl_prog_assume (asl_pred_neg c))::pL)) (Q x))) /\
(!x. (ASL_PROGRAM_HOARE_TRIPLE xenv penv (P x)
   (asl_prog_block [(asl_prog_assume c);p;
    (asl_prog_quant_best_local_action P Q)]) (Q x))) ==>
(!x. ASL_PROGRAM_HOARE_TRIPLE xenv penv (P x)
      (asl_prog_block ((asl_prog_while c p)::pL)) (Q x))``,


REWRITE_TAC [asl_prog_while_def,
   ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___prog_block,
   ASL_PROGRAM_SEM___prog_seq,
   GSYM asl_prog_assume_def,
   ASL_PROGRAM_SEM___prog_kleene_star] THEN
SIMP_TAC std_ss [asla_seq___SUP_fasl_action_order___left,
   IN_ABS, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, IN_UNIV,
   HOARE_INFERENCE___SUP_fasl_action_order,
   GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Induct_on `n` THEN1 (
   ASM_SIMP_TAC std_ss [asl_prog_repeat_num_def,
      ASL_PROGRAM_SEM___skip, asla_seq_skip]
) THEN
FULL_SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_repeat,
   REWRITE_RULE [ASSOC_SYM] asla_seq___ASSOC,
   asla_seq_skip,
   ASL_PROGRAM_SEM___prog_seq] THEN
GEN_TAC THEN
Q.MATCH_ABBREV_TAC `HOARE_TRIPLE (P x)
  (asla_seq p1 (asla_seq p2 (asla_seq p3 p4))) (Q x)` THEN
Q.ABBREV_TAC `p12 = asla_seq p1 p2` THEN
Q.ABBREV_TAC `p34 = asla_seq p3 p4` THEN
FULL_SIMP_TAC std_ss [REWRITE_RULE [ASSOC_DEF] asla_seq___ASSOC] THEN

Q.ABBREV_TAC `P12 = asl_prog_seq (asl_prog_assume c) p` THEN
`p12 = ASL_PROGRAM_SEM xenv penv P12` by ALL_TAC THEN1 (
   MAP_EVERY Q.UNABBREV_TAC [`P12`, `p12`] THEN
   ASM_SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_seq]
) THEN
Q.ABBREV_TAC `P34 = asl_prog_block (
     (asl_prog_repeat_num n P12)::
     (asl_prog_assume (asl_pred_neg c))::pL)` THEN
`p34 = ASL_PROGRAM_SEM xenv penv P34` by ALL_TAC THEN1 (
   MAP_EVERY Q.UNABBREV_TAC [`P34`, `p34`] THEN
   ASM_SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_block]
) THEN
FULL_SIMP_TAC std_ss [GSYM ASL_PROGRAM_SEM___prog_seq,
   GSYM ASL_PROGRAM_HOARE_TRIPLE_def] THEN

Tactical.REVERSE (`ASL_PROGRAM_IS_ABSTRACTION xenv penv
    (asl_prog_seq P12 P34) (asl_prog_seq P12 (asl_prog_quant_best_local_action P Q))` by ALL_TAC) THEN1 (
   FULL_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___ALTERNATIVE_DEF]
) THEN

MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___seq THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___REFL,
   ASL_PROGRAM_IS_ABSTRACTION___quant_best_local_action]);


val ASL_INFERENCE_prog_while_unroll = store_thm  ("ASL_INFERENCE_prog_while_unroll",
``!xenv penv c P Q p pL.

 (IS_SEPARATION_COMBINATOR (FST xenv) /\
 (ASL_PROGRAM_HOARE_TRIPLE xenv penv P
   (asl_prog_block ((asl_prog_assume (asl_pred_neg c))::pL)) Q) /\
 (ASL_PROGRAM_HOARE_TRIPLE xenv penv P
      (asl_prog_block ((asl_prog_assume c)::p::(asl_prog_while c p)::pL)) Q)) ==>
 (ASL_PROGRAM_HOARE_TRIPLE xenv penv P
      (asl_prog_block ((asl_prog_while c p)::pL)) Q)``,


REWRITE_TAC [asl_prog_while_def,
   ASL_PROGRAM_HOARE_TRIPLE_def,
   ASL_PROGRAM_SEM___prog_block,
   ASL_PROGRAM_SEM___prog_seq,
   GSYM asl_prog_assume_def,
   ASL_PROGRAM_SEM___prog_kleene_star] THEN
SIMP_TAC std_ss [REWRITE_RULE [ASSOC_DEF] asla_seq___ASSOC,
   asla_seq___SUP_fasl_action_order___right,
   IMAGE_EQ_EMPTY, UNIV_NOT_EMPTY] THEN
SIMP_TAC std_ss [
   asla_seq___SUP_fasl_action_order___left,
   IN_ABS, IN_IMAGE, GSYM RIGHT_EXISTS_AND_THM,
   GSYM LEFT_EXISTS_AND_THM, IN_UNIV,
   HOARE_INFERENCE___SUP_fasl_action_order,
   GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
Cases_on `n` THENL [
   ASM_SIMP_TAC std_ss [asl_prog_repeat_num_def,
      ASL_PROGRAM_SEM___skip, asla_seq_skip],

   FULL_SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_repeat,
      REWRITE_RULE [ASSOC_SYM] asla_seq___ASSOC,
      asla_seq_skip, ASL_PROGRAM_SEM___prog_seq]
]);



val ASL_PROGRAM_IS_ABSTRACTION___assume_and = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___assume_and",
``!xenv penv P1 P2.
IS_SEPARATION_COMBINATOR (FST xenv) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv
   (asl_prog_assume (asl_pred_and P1 P2))
   (asl_prog_seq
     (asl_prog_assume P1)
     (asl_prog_assume P2))``,

SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_SEM___prog_seq, ASL_PROGRAM_SEM___assume,
   EVAL_asl_predicate_def, fasl_action_order_POINTWISE_DEF] THEN
SIMP_TAC std_ss [asla_assume_def, asl_bool_EVAL, asla_seq_def] THEN
REPEAT STRIP_TAC THEN
Tactical.REVERSE (Cases_on `s IN EVAL_asl_predicate (FST xenv) P1`) THEN1 (
   ASM_SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_REWRITE, IN_ABS,
      COND_NONE_SOME_REWRITES, asl_bool_EVAL] THEN
   Cases_on `?s2. ASL_IS_SUBSTATE (FST xenv) s s2 /\
        s2 IN EVAL_asl_predicate (FST xenv) P1` THEN1 (
      ASM_REWRITE_TAC[fasl_order_THM]
   ) THEN
   FULL_SIMP_TAC std_ss [GSYM IMP_DISJ_THM, fasl_order_THM2, EMPTY_SUBSET]
) THEN
ASM_SIMP_TAC std_ss [IMAGE_INSERT, IMAGE_EMPTY, SUP_fasl_order___SING] THEN
Cases_on `s IN EVAL_asl_predicate (FST xenv) P2` THEN1 (
   ASM_SIMP_TAC std_ss [fasl_order_THM2, SUBSET_REFL]
) THEN
ASM_SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_REWRITE, IN_ABS,
      COND_NONE_SOME_REWRITES, asl_bool_EVAL] THEN
Cases_on `!s2. ASL_IS_SUBSTATE (FST xenv) s s2 ==>
          s2 NOTIN EVAL_asl_predicate (FST xenv) P2` THEN (
   ASM_SIMP_TAC std_ss [fasl_order_THM, SUBSET_REFL]
));


val ASL_PROGRAM_IS_ABSTRACTION___assume_and___LOST_INFORMATION = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___assume_and___LOST_INFORMATION",
``!xenv penv P1 P2 s.
IS_SEPARATION_COMBINATOR (FST xenv) /\ 
asl_predicate_IS_DECIDED_IN_STATE (FST xenv) s P1 /\
(s IN EVAL_asl_predicate (FST xenv) P1 ==> 
 asl_predicate_IS_DECIDED_IN_STATE (FST xenv) s P2) ==>

    (ASL_PROGRAM_SEM xenv penv 
       (asl_prog_seq (asl_prog_assume P1) (asl_prog_assume P2)) s =
     ASL_PROGRAM_SEM xenv penv
       (asl_prog_assume (asl_pred_and P1 P2)) s)
   ``,

SIMP_TAC (std_ss++CONJ_ss) [ASL_PROGRAM_SEM___prog_seq,
   ASL_PROGRAM_SEM___assume,
   EVAL_asl_predicate_def, asl_predicate_IS_DECIDED_IN_STATE___EXPAND_REWRITE] THEN
REPEAT GEN_TAC THEN
Q.ABBREV_TAC `p1 = EVAL_asl_predicate (FST xenv) P1` THEN
Q.ABBREV_TAC `p2 = EVAL_asl_predicate (FST xenv) P2` THEN

Cases_on `IS_SEPARATION_COMBINATOR (FST xenv)` THEN ASM_REWRITE_TAC[] THEN

`(!s. s IN ASL_INTUITIONISTIC_NEGATION (FST xenv) p1 ==>
      s IN ASL_INTUITIONISTIC_NEGATION (FST xenv) (asl_and p1 p2)) /\
 (!s. s IN ASL_INTUITIONISTIC_NEGATION (FST xenv) p2 ==>
      s IN ASL_INTUITIONISTIC_NEGATION (FST xenv) (asl_and p1 p2)) /\
 (!s. s IN p1 /\ s IN p2 ==>
      ~(s IN ASL_INTUITIONISTIC_NEGATION (FST xenv) (asl_and p1 p2)))` by ALL_TAC THEN1 (

   ASM_SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_REWRITE,
      IN_ABS, asl_bool_EVAL] THEN
   METIS_TAC[ASL_IS_SUBSTATE___REFL]
) THEN


ASM_SIMP_TAC (std_ss++CONJ_ss) [asla_assume_def, asl_bool_EVAL,
   LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, DISJ_IMP_THM] THEN

SIMP_TAC std_ss [SOME___asla_seq, IN_SING,
    BIGUNION_INSERT, BIGUNION_EMPTY, IMAGE_INSERT,
   IMAGE_EMPTY, UNION_EMPTY, NOT_IN_EMPTY]
);



val ASL_PROGRAM_IS_ABSTRACTION___assume_or = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___assume_or",
``!xenv penv P1 P2.
IS_SEPARATION_COMBINATOR (FST xenv) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv
   (asl_prog_assume (asl_pred_or P1 P2))
   (asl_prog_choice
     (asl_prog_assume P1)
     (asl_prog_assume P2))``,

SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_SEM___prog_choice, ASL_PROGRAM_SEM___assume,
   EVAL_asl_predicate_def, fasl_action_order_POINTWISE_DEF,
   IMAGE_INSERT, IMAGE_EMPTY, asla_bin_choice_def,
   asla_choice_def, SUP_fasl_action_order_def, SUP_fasl_order_def,
   IN_INSERT, NOT_IN_EMPTY, BIGUNION_EMPTY, BIGUNION_INSERT,
   NONE___asla_assume] THEN
SIMP_TAC std_ss [asla_assume_def, asl_bool_EVAL, IN_ABS] THEN
REPEAT STRIP_TAC THEN
Cases_on `s IN EVAL_asl_predicate (FST xenv) P1` THEN1 (
   ASM_SIMP_TAC std_ss [fasl_order_THM2, UNION_EMPTY,
      COND_NONE_SOME_REWRITES, SUBSET_DEF, IN_SING, IN_UNION]
) THEN
Cases_on `s IN EVAL_asl_predicate (FST xenv) P2` THEN1 (
   ASM_SIMP_TAC std_ss [UNION_EMPTY, fasl_order_THM2, SUBSET_REFL]
) THEN
ASM_SIMP_TAC std_ss [UNION_EMPTY, COND_NONE_SOME_REWRITES] THEN
Q.MATCH_ABBREV_TAC `fasl_order (if cond1 then SOME EMPTY else NONE)
                (if cond2 then NONE else SOME X)` THEN
ASM_SIMP_TAC std_ss [COND_RAND, COND_RATOR, fasl_order_THM2, SUBSET_REFL] THEN
MATCH_MP_TAC (prove (``(~A ==> B) ==> (A \/ B)``, METIS_TAC[])) THEN
Q.UNABBREV_TAC `cond1` THEN
Q.UNABBREV_TAC `cond2` THEN
SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_REWRITE, IN_ABS, asl_bool_EVAL]);


val ASL_PROGRAM_IS_ABSTRACTION___assume_neg_neg = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___assume_neg_neg",
``!xenv penv P.
IS_SEPARATION_COMBINATOR (FST xenv) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv
   (asl_prog_assume (asl_pred_neg (asl_pred_neg P)))
   (asl_prog_assume P)``,

SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_SEM___assume,
   EVAL_asl_predicate_def, fasl_action_order_POINTWISE_DEF] THEN
REPEAT STRIP_TAC THEN
Q.ABBREV_TAC `p = EVAL_asl_predicate (FST xenv) P` THEN
`ASL_IS_INTUITIONISTIC (FST xenv) p` by METIS_TAC [ASL_IS_INTUITIONISTIC___EVAL_asl_predicate] THEN
SIMP_TAC std_ss [asla_assume_def, IN_ABS] THEN
Cases_on `s IN p` THEN1 (
   ASM_SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_NEGATION_IMP] THEN
   SIMP_TAC std_ss [fasl_order_THM2, SUBSET_REFL]
) THEN
Q.ABBREV_TAC `pp = ASL_INTUITIONISTIC_NEGATION (FST xenv) p` THEN
Tactical.REVERSE (Cases_on `s IN pp`) THEN1 (
   ASM_SIMP_TAC std_ss [fasl_order_THM]
) THEN
`ASL_IS_INTUITIONISTIC (FST xenv) pp` by
   METIS_TAC [ASL_INTUITIONISTIC_NEGATION___IS_INTUITIONISTIC] THEN
ASM_SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_NEGATION_IMP,
   ASL_INTUITIONISTIC_NEGATION_IMP, fasl_order_THM, SUBSET_REFL]);



val ASL_PROGRAM_IS_ABSTRACTION___assume_neg_and = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___assume_neg_and",
``!xenv penv P1 P2.
IS_SEPARATION_COMBINATOR (FST xenv) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv
   (asl_prog_assume (asl_pred_neg (asl_pred_and P1 P2)))
   (asl_prog_assume (asl_pred_or (asl_pred_neg P1) (asl_pred_neg P2)))``,

SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_SEM___assume,
   EVAL_asl_predicate_def, fasl_action_order_POINTWISE_DEF] THEN
REPEAT STRIP_TAC THEN
Q.ABBREV_TAC `p1 = EVAL_asl_predicate (FST xenv) P1` THEN
Q.ABBREV_TAC `p2 = EVAL_asl_predicate (FST xenv) P2` THEN
`ASL_IS_INTUITIONISTIC (FST xenv) p1` by METIS_TAC [ASL_IS_INTUITIONISTIC___EVAL_asl_predicate] THEN
`ASL_IS_INTUITIONISTIC (FST xenv) p2` by METIS_TAC [ASL_IS_INTUITIONISTIC___EVAL_asl_predicate] THEN
Q.ABBREV_TAC `p12 = asl_or (ASL_INTUITIONISTIC_NEGATION (FST xenv) p1)
            (ASL_INTUITIONISTIC_NEGATION (FST xenv) p2)` THEN
SIMP_TAC std_ss [asla_assume_def, IN_ABS] THEN
Cases_on `s IN p12` THEN1 (
   Tactical.REVERSE (`s IN ASL_INTUITIONISTIC_NEGATION (FST xenv) (asl_and p1 p2)` by ALL_TAC) THEN1 (
      ASM_SIMP_TAC std_ss [fasl_order_THM, SUBSET_REFL]
   ) THEN
   Q.UNABBREV_TAC `p12` THEN
   FULL_SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_REWRITE, asl_bool_EVAL,
      IN_ABS]
) THEN
Tactical.REVERSE (Cases_on `s IN ASL_INTUITIONISTIC_NEGATION (FST xenv) p12`) THEN (
   ASM_SIMP_TAC std_ss [fasl_order_THM, SUBSET_EMPTY]
) THEN
Tactical.REVERSE (`~(s IN ASL_INTUITIONISTIC_NEGATION (FST xenv) (asl_and p1 p2)) /\
s IN (ASL_INTUITIONISTIC_NEGATION (FST xenv)
      (ASL_INTUITIONISTIC_NEGATION (FST xenv) (asl_and p1 p2)))` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss []
) THEN
Q.UNABBREV_TAC `p12` THEN
FULL_SIMP_TAC std_ss [asl_bool_EVAL, ASL_INTUITIONISTIC_NEGATION_REWRITE,
   IN_ABS] THEN
MATCH_MP_TAC (prove (``((B ==> A) /\ B) ==> (A /\ B)``, PROVE_TAC[])) THEN
CONJ_TAC THEN1 (
   SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
   Q.EXISTS_TAC `s` THEN
   ASM_SIMP_TAC std_ss [ASL_IS_SUBSTATE___REFL]
) THEN
REPEAT STRIP_TAC THEN
`?s3. ASL_IS_SUBSTATE (FST xenv) s2'' s3 /\ s3 IN p1` by METIS_TAC[] THEN
`ASL_IS_SUBSTATE (FST xenv) s s3` by PROVE_TAC[ASL_IS_SUBSTATE___TRANS] THEN

`?s4. ASL_IS_SUBSTATE (FST xenv) s3 s4 /\ s4 IN p2` by METIS_TAC[] THEN
Q.EXISTS_TAC `s4` THEN

`ASL_IS_SUBSTATE (FST xenv) s2'' s4` by PROVE_TAC[ASL_IS_SUBSTATE___TRANS] THEN

Q.PAT_ASSUM `ASL_IS_INTUITIONISTIC f p1` MP_TAC THEN
ASM_SIMP_TAC std_ss [ASL_IS_INTUITIONISTIC___REWRITE] THEN
METIS_TAC[]);




val ASL_PROGRAM_IS_ABSTRACTION___assume_neg_or = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___assume_neg_or",
``!xenv penv P1 P2.
IS_SEPARATION_COMBINATOR (FST xenv) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv
   (asl_prog_assume (asl_pred_neg (asl_pred_or P1 P2)))
   (asl_prog_assume (asl_pred_and (asl_pred_neg P1) (asl_pred_neg P2)))``,

SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_SEM___assume,
   EVAL_asl_predicate_def, fasl_action_order_POINTWISE_DEF] THEN
REPEAT STRIP_TAC THEN
Q.ABBREV_TAC `p1 = EVAL_asl_predicate (FST xenv) P1` THEN
Q.ABBREV_TAC `p2 = EVAL_asl_predicate (FST xenv) P2` THEN
`ASL_IS_INTUITIONISTIC (FST xenv) p1` by METIS_TAC [ASL_IS_INTUITIONISTIC___EVAL_asl_predicate] THEN
`ASL_IS_INTUITIONISTIC (FST xenv) p2` by METIS_TAC [ASL_IS_INTUITIONISTIC___EVAL_asl_predicate] THEN
Q.ABBREV_TAC `p12 = asl_and (ASL_INTUITIONISTIC_NEGATION (FST xenv) p1)
            (ASL_INTUITIONISTIC_NEGATION (FST xenv) p2)` THEN
SIMP_TAC std_ss [asla_assume_def, IN_ABS] THEN
Cases_on `s IN p12` THEN1 (
   Tactical.REVERSE (`s IN ASL_INTUITIONISTIC_NEGATION (FST xenv) (asl_or p1 p2)` by ALL_TAC) THEN1 (
      ASM_SIMP_TAC std_ss [fasl_order_THM, SUBSET_REFL]
   ) THEN
   Q.UNABBREV_TAC `p12` THEN
   FULL_SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_REWRITE, asl_bool_EVAL, IN_ABS]
) THEN
Tactical.REVERSE (Cases_on `s IN ASL_INTUITIONISTIC_NEGATION (FST xenv) p12`) THEN (
   ASM_SIMP_TAC std_ss [fasl_order_THM, SUBSET_EMPTY]
) THEN
Tactical.REVERSE (`~(s IN ASL_INTUITIONISTIC_NEGATION (FST xenv) (asl_or p1 p2)) /\
s IN (ASL_INTUITIONISTIC_NEGATION (FST xenv)
      (ASL_INTUITIONISTIC_NEGATION (FST xenv) (asl_or p1 p2)))` by ALL_TAC) THEN1 (
   ASM_SIMP_TAC std_ss []
) THEN
Q.UNABBREV_TAC `p12` THEN
SIMP_TAC std_ss [asl_bool_EVAL, ASL_INTUITIONISTIC_NEGATION_REWRITE, IN_ABS] THEN
MATCH_MP_TAC (prove (``((B ==> A) /\ B) ==> (A /\ B)``, PROVE_TAC[])) THEN
CONJ_TAC THEN1 (
   SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
   Q.EXISTS_TAC `s` THEN
   ASM_SIMP_TAC std_ss [ASL_IS_SUBSTATE___REFL]
) THEN
Q.PAT_ASSUM `s NOTIN X` (K ALL_TAC) THEN
FULL_SIMP_TAC std_ss [ASL_INTUITIONISTIC_NEGATION_REWRITE, IN_ABS, asl_bool_EVAL] THEN
METIS_TAC[]);






val ASL_PROGRAM_SEM_EQUIV___prog_critical_section = store_thm (
"ASL_PROGRAM_SEM_EQUIV___prog_critical_section",
``!xenv penv l p p'.
 (IS_SEPARATION_COMBINATOR (FST xenv) /\
 (ASL_PROGRAM_SEM xenv penv p = ASL_PROGRAM_SEM xenv penv p')) ==>
 (ASL_PROGRAM_SEM xenv penv (asl_prog_critical_section l p) =
  ASL_PROGRAM_SEM xenv penv (asl_prog_critical_section l p'))``,

Cases_on `xenv` THEN
SIMP_TAC std_ss [ASL_PROGRAM_SEM___asl_prog_critical_section,
       asl_prog_block_def, ASL_PROGRAM_SEM___prog_seq]);


val ASL_PROGRAM_SEM_EQUIV___prog_critical_section___cond = store_thm (
"ASL_PROGRAM_SEM_EQUIV___prog_critical_section___cond",
``!xenv penv l p.
 IS_SEPARATION_COMBINATOR (FST xenv) ==>
 (ASL_PROGRAM_SEM xenv penv (asl_prog_critical_section l p) =
  ASL_PROGRAM_SEM xenv penv (asl_prog_cond_critical_section l asl_pred_true p))``,

SIMP_TAC std_ss [asl_prog_cond_critical_section_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_PROGRAM_SEM_EQUIV___prog_critical_section THEN
ASM_SIMP_TAC std_ss [asl_pc_assume_true___skip, ASL_PROGRAM_SEM___prog_seq,
           ASL_PROGRAM_SEM___skip, GSYM asl_prog_skip_def,
           asla_seq_skip]);


val ASL_PROGRAM_IS_ABSTRACTION___prog_critical_section = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___prog_critical_section",
``!xenv penv l p.
 IS_SEPARATION_COMBINATOR (FST xenv) ==>
 ASL_PROGRAM_IS_ABSTRACTION xenv penv
   (asl_prog_critical_section l p)
   (asl_prog_cond_critical_section l asl_pred_true p)``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___SEM_REFL THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_SEM_EQUIV___prog_critical_section___cond]);



val ASL_PROGRAM_IS_ABSTRACTION___asl_prog_cond_critical_section = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___asl_prog_cond_critical_section",
``!xenv penv l c prog P.
IS_SEPARATION_COMBINATOR (FST xenv) /\
(P = ((SND xenv) l)) ==>
ASL_PROGRAM_IS_ABSTRACTION xenv penv
   (asl_prog_cond_critical_section l c prog)
   (asl_prog_block
    [asl_prog_aquire_lock c P;
     prog;
     asl_prog_release_lock P])``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___SEM_REFL THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_SEM___asl_prog_cond_critical_section]);




val ASL_PROGRAM_HOARE_TRIPLE_ABSTRACTION___INTRO = store_thm (
"ASL_PROGRAM_HOARE_TRIPLE_ABSTRACTION___INTRO",
``
!xenv penv P prog1 Q prog2.
ASL_PROGRAM_IS_ABSTRACTION xenv penv prog1 prog2 ==>
ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog2 Q ==>
ASL_PROGRAM_HOARE_TRIPLE xenv penv P prog1 Q``,

SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION___ALTERNATIVE_DEF]);


val ASL_PROGRAM_IS_ABSTRACTION___fail = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___fail",
``!xenv penv p. ASL_PROGRAM_IS_ABSTRACTION xenv penv p asl_prog_fail``,

SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
       ASL_PROGRAM_SEM___fail,
       fasl_action_order_POINTWISE_DEF,
       asla_fail_def,
       fasl_order_THM]);



val ASL_PROGRAM_IS_ABSTRACTION___block_intro = store_thm (
"ASL_PROGRAM_IS_ABSTRACTION___block_intro",
``ASL_PROGRAM_IS_ABSTRACTION xenv penv p1 (asl_prog_block [p2]) =
  ASL_PROGRAM_IS_ABSTRACTION xenv penv p1 p2``,

SIMP_TAC std_ss [asl_prog_block_def]);




val ASL_PROGRAM_SEM___prog_seq___prog_cond =
store_thm ("ASL_PROGRAM_SEM___prog_seq___prog_cond",
``
(ASL_PROGRAM_SEM xenv penv
      (asl_prog_seq (asl_prog_cond c pT pF) prog))
=
(ASL_PROGRAM_SEM xenv penv
      (asl_prog_cond c (asl_prog_seq pT prog) (asl_prog_seq pF prog)))``,



SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_seq,
       asl_prog_cond_def,
       ASL_PROGRAM_SEM___prog_choice] THEN

ASSUME_TAC asla_seq___ASSOC THEN
FULL_SIMP_TAC std_ss [ASSOC_DEF] THEN

Q.ABBREV_TAC `a1 = (asla_seq
       (ASL_PROGRAM_SEM xenv penv
          (asl_prog_prim_command (asl_pc_assume c)))
       (ASL_PROGRAM_SEM xenv penv pT))` THEN
Q.ABBREV_TAC `a2 = (asla_seq
       (ASL_PROGRAM_SEM xenv penv
          (asl_prog_prim_command (asl_pc_assume (asl_pred_neg c))))
       (ASL_PROGRAM_SEM xenv penv pF))` THEN
Q.ABBREV_TAC `a3 = (ASL_PROGRAM_SEM xenv penv prog)` THEN


SIMP_TAC std_ss [asla_seq_def, asla_bin_choice_def,
       asla_choice_def,
       SUP_fasl_action_order_def,
       SUP_fasl_order_def,
       IN_IMAGE, IN_INSERT, NOT_IN_EMPTY,
       EXISTS_OR_THM,
       RIGHT_AND_OVER_OR,
       LEFT_AND_OVER_OR,
       COND_NONE_SOME_REWRITES] THEN
ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
GEN_TAC THEN
Cases_on `a1 x` THEN ASM_SIMP_TAC std_ss [] THEN
Cases_on `a2 x` THEN ASM_SIMP_TAC std_ss [] THEN

SIMP_TAC std_ss [COND_NONE_SOME_REWRITES_EQ] THEN
REPEAT STRIP_TAC THENL [
   ASM_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE,
          GSYM RIGHT_EXISTS_AND_THM,
          IN_INSERT, NOT_IN_EMPTY,
          RIGHT_AND_OVER_OR,
          LEFT_AND_OVER_OR, EXISTS_OR_THM],


   ONCE_REWRITE_TAC[EXTENSION] THEN
   ASM_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE,
          GSYM LEFT_EXISTS_AND_THM,
          IN_INSERT, NOT_IN_EMPTY,
          RIGHT_AND_OVER_OR,
          LEFT_AND_OVER_OR, EXISTS_OR_THM,
          GSYM RIGHT_EXISTS_AND_THM] THEN
   ONCE_REWRITE_TAC [
      prove (``(if c then p else q) = (if ~c then q else p)``, METIS_TAC[])] THEN
   ASM_SIMP_TAC std_ss [IN_BIGUNION, IN_IMAGE,
         GSYM RIGHT_EXISTS_AND_THM]
]);



val ASL_INFERENCE_prog_cond_seq = store_thm  ("ASL_INFERENCE_prog_cond_seq",
``!xenv penv c P Q pTrue pFalse p_seq.
(ASL_PROGRAM_HOARE_TRIPLE xenv penv P
    (asl_prog_seq (asl_prog_assume c) (asl_prog_seq pTrue p_seq)) Q) /\
(ASL_PROGRAM_HOARE_TRIPLE xenv penv P
    (asl_prog_seq (asl_prog_assume (asl_pred_neg c))
         (asl_prog_seq pFalse p_seq)) Q) ==>

ASL_PROGRAM_HOARE_TRIPLE xenv penv P (asl_prog_seq (asl_prog_cond c pTrue pFalse) p_seq) Q``,



REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [ASL_PROGRAM_HOARE_TRIPLE_def,
       ASL_PROGRAM_SEM___prog_seq___prog_cond] THEN
SIMP_TAC std_ss [GSYM ASL_PROGRAM_HOARE_TRIPLE_def] THEN
MATCH_MP_TAC ASL_INFERENCE_prog_cond THEN
ASM_REWRITE_TAC[]);




val ASL_PROGRAM_IS_ABSTRACTION___block_flatten =
store_thm ("ASL_PROGRAM_IS_ABSTRACTION___block_flatten",

``!xenv penv L1 L2 L3.
  ASL_PROGRAM_IS_ABSTRACTION xenv penv (asl_prog_block (L1++(asl_prog_block L2::L3)))
  (asl_prog_block (L1++L2++L3))``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_PROGRAM_IS_ABSTRACTION___SEM_REFL THEN
SIMP_TAC std_ss [ASL_PROGRAM_SEM___block_flatten]);






(******************************************************************************)
(* Eliminating recursion & environments / Specifications                      *)
(******************************************************************************)

val ASL_PROTO_TRACES_EVAL_PROC___TO___ASL_PROGRAM_TRACES = store_thm (
   "ASL_PROTO_TRACES_EVAL_PROC___TO___ASL_PROGRAM_TRACES",
``!n (pt:('a, 'b, 'c, 'd) asl_proto_trace) penv.
   ?prog:('a, 'b, 'c, 'd) asl_program. !m penv'.
   (FDOM penv = FDOM penv') ==>
   (ASL_PROGRAM_TRACES_PROC m penv' prog = ASL_PROTO_TRACES_EVAL_PROC n penv pt)``,

ONCE_REWRITE_TAC [EXTENSION] THEN
completeInduct_on `n` THEN
REPEAT GEN_TAC THEN
Induct_on `pt` THENL [
   GEN_TAC THEN
   Q.EXISTS_TAC `asl_prog_prim_command a` THEN
   SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM,
      ASL_PROGRAM_TRACES_PROC_IN_THM, IN_ABS,
      asl_prog_prim_command_def, IN_SING],

   FULL_SIMP_TAC std_ss [] THEN
   Q.ABBREV_TAC `prog2 = (\pt. ?pt1 pt2. (pt = asl_pt_seq pt1 pt2) /\ pt1 IN prog /\ pt2 IN prog')`  THEN
   Q.EXISTS_TAC `prog2` THEN
   REPEAT GEN_TAC THEN
   `ASL_PROGRAM_TRACES_PROC m penv' prog2 =
   \t. ?t1 t2.
     (t = t1 ++ t2) /\
     t1 IN ASL_PROGRAM_TRACES_PROC m penv' prog /\
     t2 IN ASL_PROGRAM_TRACES_PROC m penv' prog'` by ALL_TAC THEN1 (
      ONCE_REWRITE_TAC [EXTENSION] THEN
      Q.UNABBREV_TAC `prog2` THEN
      ASM_SIMP_TAC std_ss [ASL_PROGRAM_TRACES_PROC_def,
            IN_BIGUNION, IN_IMAGE, IN_ABS,
            GSYM RIGHT_EXISTS_AND_THM,
            ASL_PROTO_TRACES_EVAL_PROC_IN_THM,
            GSYM LEFT_EXISTS_AND_THM] THEN
      METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC std_ss [IN_ABS, ASL_PROTO_TRACES_EVAL_PROC_IN_THM],


   REPEAT GEN_TAC THEN
   Cases_on `~(n' IN FDOM penv)` THEN1 (
      REPEAT STRIP_TAC THEN
      Q.EXISTS_TAC `asl_prog_procedure_call n' a` THEN
      Cases_on `n` THEN Cases_on `m` THEN (
         ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM,
         ASL_PROGRAM_TRACES_PROC_IN_THM] THEN
         METIS_TAC[]
      )
   ) THEN
   Cases_on `n` THEN1 (
      Q.EXISTS_TAC `{}` THEN
      FULL_SIMP_TAC std_ss [ASL_PROGRAM_TRACES_PROC_THM,
         ASL_PROTO_TRACES_EVAL_PROC_IN_THM, NOT_IN_EMPTY]
   ) THEN
   Q.PAT_ASSUM `!m. m < SUC n'' ==> Q m` (ASSUME_TAC o Q.SPEC `n''`) THEN
   FULL_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM] THEN
   Q.EXISTS_TAC `\pt. ?pt' prog. (pt' IN penv ' n' a) /\ (!m penv'. (FDOM penv = FDOM penv') ==>
      (ASL_PROTO_TRACES_EVAL_PROC n'' penv pt' =
      ASL_PROGRAM_TRACES_PROC m penv' prog)) /\ (pt IN prog)` THEN
   FULL_SIMP_TAC std_ss [ASL_PROGRAM_TRACES_PROC_IN_THM2, IN_ABS,
      EXTENSION] THEN
   FULL_SIMP_TAC std_ss [GSYM EXTENSION] THEN
   METIS_TAC[],


   FULL_SIMP_TAC std_ss [] THEN
   Q.EXISTS_TAC `asl_prog_parallel prog prog'` THEN
   ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM,
      ASL_PROGRAM_TRACES_PROC_IN_THM] THEN
   METIS_TAC[],


   FULL_SIMP_TAC std_ss [] THEN
   GEN_TAC THEN
   Q.EXISTS_TAC `asl_prog_lock_declaration l prog` THEN
   ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM,
      ASL_PROGRAM_TRACES_PROC_IN_THM] THEN
   METIS_TAC[],


   FULL_SIMP_TAC std_ss [] THEN
   GEN_TAC THEN
   Q.EXISTS_TAC `asl_prog_critical_section l prog` THEN
   ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM,
      ASL_PROGRAM_TRACES_PROC_IN_THM] THEN
   METIS_TAC[]
]);






val ASL_EQUIV_PENV_PROC_def = Define `
   ASL_EQUIV_PENV_PROC n (penv:'c |-> ('a -> ('a, 'b, 'c, 'd) asl_program)) =
   FUN_FMAP (\proc. \arg. @prog. !m
(penv':'c |-> ('a -> ('a, 'b, 'c, 'd) asl_program)). (FDOM penv = FDOM penv') ==>
      (ASL_PROGRAM_TRACES_PROC m penv' prog =
      ASL_PROTO_TRACES_EVAL_PROC n penv (asl_pt_procedure_call proc arg)))
      (FDOM penv)`


val ASL_EQUIV_PENV_PROC_THM = store_thm ("ASL_EQUIV_PENV_PROC_THM",
``(!n penv. FDOM (ASL_EQUIV_PENV_PROC n penv) = FDOM penv) /\
(!n penv penv' proc arg m. ((proc IN FDOM penv) /\ (FDOM penv' = FDOM penv)) ==> ((ASL_PROGRAM_TRACES_PROC m penv'
 ((ASL_EQUIV_PENV_PROC n penv) ' proc arg)) = ASL_PROGRAM_TRACES_PROC n penv (asl_prog_procedure_call proc arg)))``,

CONJ_TAC THEN1 (
   SIMP_TAC std_ss [ASL_EQUIV_PENV_PROC_def, FDOM_FINITE, FUN_FMAP_DEF]
) THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [ASL_EQUIV_PENV_PROC_def, FDOM_FINITE, FUN_FMAP_DEF] THEN
SELECT_ELIM_TAC THEN
REPEAT STRIP_TAC THENL [
   METIS_TAC[ASL_PROTO_TRACES_EVAL_PROC___TO___ASL_PROGRAM_TRACES],

   SIMP_TAC std_ss [ASL_PROGRAM_TRACES_PROC_SING_THM, asl_prog_procedure_call_def] THEN
   Q.PAT_ASSUM `!m penv'. X m penv'` MATCH_MP_TAC THEN
   ASM_SIMP_TAC std_ss [ASL_EQUIV_PENV_PROC_def, FDOM_FINITE, FUN_FMAP_DEF]
]);



val ASL_EQUIV_PENV_PROC___PROTO_TRACES = store_thm ("ASL_EQUIV_PENV_PROC___PROTO_TRACES",
``!n penv pt. (ASL_PROTO_TRACES_EVAL (ASL_EQUIV_PENV_PROC n penv)
 pt) = ASL_PROTO_TRACES_EVAL_PROC n penv pt``,


ONCE_REWRITE_TAC[EXTENSION] THEN
Induct_on `pt` THENL [
   SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_IN_THM,
      ASL_PROTO_TRACES_EVAL_PROC_IN_THM],

   ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_IN_THM,
      ASL_PROTO_TRACES_EVAL_PROC_IN_THM],

   SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_def, IN_ABS] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THENL [
      STRIP_TAC THEN
      Cases_on `n''` THEN1 (
         Cases_on `n'` THEN
         FULL_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM,
            ASL_EQUIV_PENV_PROC_THM]
      ) THEN
      FULL_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM,
            ASL_EQUIV_PENV_PROC_THM] THEN
      Cases_on `~(n IN FDOM penv)` THEN FULL_SIMP_TAC std_ss [] THENL [
         Cases_on `n'` THEN
         FULL_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM,
            ASL_EQUIV_PENV_PROC_THM],

         FULL_SIMP_TAC std_ss [asl_prog_procedure_call_def,
            ASL_PROGRAM_TRACES_PROC_SING_THM]
      ],

      REPEAT STRIP_TAC THEN
      Q.EXISTS_TAC `SUC n'` THEN (
         ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM,
               ASL_EQUIV_PENV_PROC_THM,
               asl_prog_procedure_call_def,
               ASL_PROGRAM_TRACES_PROC_SING_THM]
      ) THEN
      STRIP_TAC THEN
      Cases_on `n'` THEN (
         FULL_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_PROC_IN_THM]
      )
   ],


   ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_IN_THM,
      ASL_PROTO_TRACES_EVAL_PROC_IN_THM],


   ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_IN_THM,
      ASL_PROTO_TRACES_EVAL_PROC_IN_THM],

   ASM_SIMP_TAC std_ss [ASL_PROTO_TRACES_EVAL_IN_THM,
      ASL_PROTO_TRACES_EVAL_PROC_IN_THM]
]);





val ASL_EQUIV_PENV_PROC___PROGRAM_TRACES = store_thm ("ASL_EQUIV_PENV_PROC___PROGRAM_TRACES",
``(!n penv prog. (ASL_PROGRAM_TRACES (ASL_EQUIV_PENV_PROC n penv)
 prog) = ASL_PROGRAM_TRACES_PROC n penv prog) /\
(!n penv proc arg. (proc IN FDOM penv) ==> ((ASL_PROGRAM_TRACES penv
 ((ASL_EQUIV_PENV_PROC n penv) ' proc arg)) = ASL_PROGRAM_TRACES_PROC n penv (asl_prog_procedure_call proc arg)))``,


CONJ_TAC THENL [
   SIMP_TAC std_ss [ASL_PROGRAM_TRACES_IN_THM2,
      ASL_EQUIV_PENV_PROC___PROTO_TRACES,
      ASL_PROGRAM_TRACES_PROC_IN_THM2],

   ONCE_REWRITE_TAC[EXTENSION] THEN
   SIMP_TAC std_ss [ASL_PROGRAM_TRACES___PROC_THM, IN_ABS,
      ASL_EQUIV_PENV_PROC_THM]
]);




val ASL_EQUIV_PENV_PROC___PROGRAM_SEM = store_thm ("ASL_EQUIV_PENV_PROC___PROGRAM_SEM",
``(!n xenv penv prog. (ASL_PROGRAM_SEM xenv (ASL_EQUIV_PENV_PROC n penv)
 prog) = ASL_PROGRAM_SEM_PROC n xenv penv prog)``,

SIMP_TAC std_ss [ASL_PROGRAM_SEM_def, ASL_EQUIV_PENV_PROC___PROGRAM_TRACES,
   ASL_PROGRAM_SEM_PROC_def]);




val ASL_IS_EQUIV_PENV_PROC___EXISTS_THM = store_thm ("ASL_IS_EQUIV_PENV_PROC___EXISTS_THM",
``!n penv. ASL_IS_EQUIV_PENV_PROC n (ASL_EQUIV_PENV_PROC n penv) penv``,

SIMP_TAC std_ss [ASL_IS_EQUIV_PENV_PROC_def, ASL_EQUIV_PENV_PROC_THM] THEN
REPEAT STRIP_TAC THEN
Cases_on `n` THEN (
   SIMP_TAC std_ss [ASL_PROGRAM_TRACES_PROC_THM, ASL_EQUIV_PENV_PROC_THM]
));


val asl_prog_IS_RESOURCE_FREE_def = Define `
asl_prog_IS_RESOURCE_FREE prog =
!f lock_env lock_env' penv.
ASL_PROGRAM_SEM (f, lock_env)  penv prog =
ASL_PROGRAM_SEM (f, lock_env') penv prog`


val asl_prog_IS_PROCCALL_FREE_def = Define `
asl_prog_IS_PROCCALL_FREE prog =
!xenv penv penv'.
ASL_PROGRAM_SEM xenv penv  prog =
ASL_PROGRAM_SEM xenv penv' prog`


val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE_def = Define `
asl_prog_IS_RESOURCE_AND_PROCCALL_FREE prog =
!f lock_env penv lock_env' penv'.
ASL_PROGRAM_SEM (f, lock_env) penv  prog =
ASL_PROGRAM_SEM (f, lock_env') penv' prog`


val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___ALTERNATIVE_DEF =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___ALTERNATIVE_DEF",
``asl_prog_IS_RESOURCE_AND_PROCCALL_FREE prog =
(asl_prog_IS_RESOURCE_FREE prog /\
 asl_prog_IS_PROCCALL_FREE prog)``,

SIMP_TAC std_ss [asl_prog_IS_RESOURCE_FREE_def,
   asl_prog_IS_PROCCALL_FREE_def,
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE_def,
   PAIR_FORALL_THM] THEN
METIS_TAC[]);



val asl_prog_IS_PROCCALL_FREE___PROC = store_thm (
"asl_prog_IS_PROCCALL_FREE___PROC",
``asl_prog_IS_PROCCALL_FREE prog ==>
!n m xenv penv penv'.
ASL_PROGRAM_SEM_PROC n xenv penv  prog =
ASL_PROGRAM_SEM_PROC m xenv penv' prog``,

SIMP_TAC std_ss [GSYM ASL_EQUIV_PENV_PROC___PROGRAM_SEM,
   asl_prog_IS_PROCCALL_FREE_def]);




val ASL_PROCEDURE_SPEC_def = Define `
   ASL_PROCEDURE_SPEC xenv penv specs =
    !name abst. MEM (name,abst) specs ==>
    !arg. ASL_PROGRAM_IS_ABSTRACTION xenv penv (asl_prog_procedure_call name arg) (abst arg)`;


val ASL_PROCEDURE_SPEC___wellformed_spec_def = Define
`ASL_PROCEDURE_SPEC___wellformed_spec penv specs =
 EVERY (\x. (FST x IN FDOM penv) /\
       (!arg. asl_prog_IS_PROCCALL_FREE ((SND x) arg))) specs`


val ASL_PROCEDURE_SPEC___ASL_EQUIV_PENV_INTRO =
store_thm ("ASL_PROCEDURE_SPEC___ASL_EQUIV_PENV_INTRO",
``!xenv penv specs.
  (ASL_PROCEDURE_SPEC___wellformed_spec penv specs) ==>
  (ASL_PROCEDURE_SPEC xenv penv specs =
   !n. ASL_PROCEDURE_SPEC xenv (ASL_EQUIV_PENV_PROC n penv) specs)``,

SIMP_TAC std_ss [ASL_PROCEDURE_SPEC_def,
   ASL_PROGRAM_IS_ABSTRACTION_def, ASL_PROCEDURE_SPEC___wellformed_spec_def,
   EVERY_MEM] THEN
REPEAT STRIP_TAC THEN
HO_MATCH_MP_TAC (prove (``
(!arg name abst. X name abst ==> (Y arg name abst = !n. Z n arg name abst)) ==>
((!name abst. (X name abst ==> !arg. Y arg name abst)) =
 (!n name abst. (X name abst) ==> !arg. Z n arg name abst))``, METIS_TAC[])) THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN
FULL_SIMP_TAC std_ss [] THEN
`!n. ASL_PROGRAM_SEM xenv (ASL_EQUIV_PENV_PROC n penv) (abst arg) =
     ASL_PROGRAM_SEM xenv penv (abst arg)` by PROVE_TAC[asl_prog_IS_PROCCALL_FREE_def] THEN
FULL_SIMP_TAC std_ss [] THEN
Q.ABBREV_TAC `a2 = (ASL_PROGRAM_SEM xenv penv (abst arg))` THEN
ASM_SIMP_TAC std_ss [ASL_EQUIV_PENV_PROC___PROGRAM_SEM,
   ASL_PROGRAM_SEM___PROC_THM, fasl_action_order___SUP_fasl_action_order,
   IN_ABS, GSYM LEFT_FORALL_IMP_THM]);




val ASL_INFERENCE___PROCEDURE_SPEC = store_thm  ("ASL_INFERENCE___PROCEDURE_SPEC",
``!xenv penv specs.
(ASL_PROCEDURE_SPEC___wellformed_spec penv specs /\
(!penv'. (ASL_PROCEDURE_SPEC xenv penv' specs ==>
(!name abst. MEM (name,abst) specs ==>
       !arg. ASL_PROGRAM_IS_ABSTRACTION xenv penv'
       ((penv ' name) arg) (abst arg))))) ==>
ASL_PROCEDURE_SPEC xenv penv specs``,


REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [ASL_PROCEDURE_SPEC___ASL_EQUIV_PENV_INTRO] THEN
Induct_on `n` THEN1 (
   SIMP_TAC std_ss [ASL_PROCEDURE_SPEC_def,
      ASL_PROGRAM_IS_ABSTRACTION_def,
      ASL_EQUIV_PENV_PROC___PROGRAM_TRACES,
      ASL_PROGRAM_SEM_def, ASL_PROGRAM_TRACES_PROC_THM] THEN
   REPEAT STRIP_TAC THEN
   `name IN FDOM penv` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [ASL_PROCEDURE_SPEC___wellformed_spec_def,
    EVERY_MEM] THEN
      RES_TAC THEN
      FULL_SIMP_TAC std_ss []
   ) THEN
   ASM_SIMP_TAC std_ss [GSYM EMPTY_DEF, ASL_TRACE_SET_SEM_def, IMAGE_EMPTY,
     fasl_action_order___SUP_fasl_action_order, NOT_IN_EMPTY]
) THEN
Q.PAT_ASSUM `!penv'. X` (MP_TAC o Q.SPEC `ASL_EQUIV_PENV_PROC n penv`) THEN
ASM_SIMP_TAC std_ss [ASL_EQUIV_PENV_PROC_THM,
  ASL_PROCEDURE_SPEC_def, GSYM RIGHT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!name abst arg. X` (MP_TAC o Q.SPECL [`name`, `abst`, `arg`]) THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_SEM_def, ASL_EQUIV_PENV_PROC___PROGRAM_TRACES,
   ASL_PROGRAM_TRACES_PROC_THM] THEN
FULL_SIMP_TAC std_ss [ASL_PROCEDURE_SPEC___wellformed_spec_def,
   EVERY_MEM] THEN
RES_TAC THEN
FULL_SIMP_TAC std_ss [GSYM ASL_PROGRAM_SEM_PROC_def] THEN
PROVE_TAC[asl_prog_IS_PROCCALL_FREE___PROC]);


val ASL_proc_specs_penv_def = Define `
    ASL_proc_specs_penv penv proc_specs =
      penv |++ (MAP (\x. (FST x, FST (SND x))) proc_specs)`

val ASL_proc_specs_spec_def = Define `
    ASL_proc_specs_spec proc_specs =
      MAP (\x. (FST x, SND (SND x))) proc_specs`;

val FDOM_ASL_proc_specs_penv = store_thm (
"FDOM_ASL_proc_specs_penv",
``FDOM (ASL_proc_specs_penv penv proc_specs) =
  FDOM penv UNION (LIST_TO_SET (MAP FST proc_specs))``,

SIMP_TAC std_ss [ASL_proc_specs_penv_def,
   FDOM_FUPDATE_LIST, MAP_MAP_o,
   combinTheory.o_DEF, ETA_THM]);



val ASL_INFERENCE___PROCEDURE_SPEC = store_thm  ("ASL_INFERENCE___PROCEDURE_SPEC",
``!xenv penv specs P.
(ASL_PROCEDURE_SPEC___wellformed_spec penv specs /\
(!n. (P (ASL_EQUIV_PENV_PROC n penv))) /\
(!penv'. (P penv' /\ ASL_PROCEDURE_SPEC xenv penv' specs ==>
(!name abst. MEM (name,abst) specs ==>
       !arg. ASL_PROGRAM_IS_ABSTRACTION xenv penv'
       ((penv ' name) arg) (abst arg))))) ==>
ASL_PROCEDURE_SPEC xenv penv specs``,


REPEAT STRIP_TAC THEN
ASM_SIMP_TAC std_ss [ASL_PROCEDURE_SPEC___ASL_EQUIV_PENV_INTRO] THEN
Induct_on `n` THEN1 (
   SIMP_TAC std_ss [ASL_PROCEDURE_SPEC_def,
      ASL_PROGRAM_IS_ABSTRACTION_def,
      ASL_EQUIV_PENV_PROC___PROGRAM_TRACES,
      ASL_PROGRAM_SEM_def, ASL_PROGRAM_TRACES_PROC_THM] THEN
   REPEAT STRIP_TAC THEN
   `name IN FDOM penv` by ALL_TAC THEN1 (
      FULL_SIMP_TAC std_ss [ASL_PROCEDURE_SPEC___wellformed_spec_def,
    EVERY_MEM] THEN
      RES_TAC THEN
      FULL_SIMP_TAC std_ss []
   ) THEN
   ASM_SIMP_TAC std_ss [GSYM EMPTY_DEF, ASL_TRACE_SET_SEM_def, IMAGE_EMPTY,
     fasl_action_order___SUP_fasl_action_order, NOT_IN_EMPTY]
) THEN
Q.PAT_ASSUM `!penv'. X` (MP_TAC o Q.SPEC `ASL_EQUIV_PENV_PROC n penv`) THEN
ASM_SIMP_TAC std_ss [ASL_EQUIV_PENV_PROC_THM,
  ASL_PROCEDURE_SPEC_def, GSYM RIGHT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
Q.PAT_ASSUM `!name abst arg. X` (MP_TAC o Q.SPECL [`name`, `abst`, `arg`]) THEN
ASM_SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def,
   ASL_PROGRAM_SEM_def, ASL_EQUIV_PENV_PROC___PROGRAM_TRACES,
   ASL_PROGRAM_TRACES_PROC_THM] THEN
FULL_SIMP_TAC std_ss [ASL_PROCEDURE_SPEC___wellformed_spec_def,
   EVERY_MEM] THEN
RES_TAC THEN
FULL_SIMP_TAC std_ss [GSYM ASL_PROGRAM_SEM_PROC_def] THEN
PROVE_TAC[asl_prog_IS_PROCCALL_FREE___PROC]);


val ASL_proc_specs_penv_def = Define `
    ASL_proc_specs_penv penv proc_specs =
      penv |++ (MAP (\x. (FST x, FST (SND x))) proc_specs)`

val ASL_proc_specs_spec_def = Define `
    ASL_proc_specs_spec proc_specs =
      MAP (\x. (FST x, SND (SND x))) proc_specs`;

val FDOM_ASL_proc_specs_penv = store_thm (
"FDOM_ASL_proc_specs_penv",
``FDOM (ASL_proc_specs_penv penv proc_specs) =
  FDOM penv UNION (LIST_TO_SET (MAP FST proc_specs))``,

SIMP_TAC std_ss [ASL_proc_specs_penv_def,
   FDOM_FUPDATE_LIST, MAP_MAP_o,
   combinTheory.o_DEF, ETA_THM]);



val ASL_SPECIFICATION_def = Define `
    ASL_SPECIFICATION f lock_decls proc_specs =
    let real_proc_specs = MAP SND (FILTER FST proc_specs) in
    let assume_proc_specs = MAP SND (FILTER (\x. ~(FST x)) proc_specs) in
    let all_proc_specs = MAP SND proc_specs in
    (!penv.
   ASL_PROCEDURE_SPEC (f, LIST_TO_FUN lock_decls)
   (ASL_proc_specs_penv penv real_proc_specs)
   (ASL_proc_specs_spec assume_proc_specs) ==>

   ASL_PROCEDURE_SPEC (f, LIST_TO_FUN lock_decls)
   (ASL_proc_specs_penv penv real_proc_specs)
   (ASL_proc_specs_spec real_proc_specs))`;




val ASL_INFERENCE___SPECIFICATION = store_thm (
"ASL_INFERENCE___SPECIFICATION",
``!f lock_decls specs.
EVERY (\x. !arg. asl_prog_IS_PROCCALL_FREE (SND (SND (SND x)) arg)) specs /\
ALL_DISTINCT (MAP FST (MAP SND specs)) ==>

(!penv.
EVERY (\x. !arg.
   ASL_PROGRAM_IS_ABSTRACTION (f,LIST_TO_FUN lock_decls) penv
      (asl_prog_procedure_call (FST (SND x)) arg)
      (SND (SND (SND x)) arg)) specs ==>
EVERY (\x. !arg. FST x ==> (
   ASL_PROGRAM_IS_ABSTRACTION (f,LIST_TO_FUN lock_decls) penv
      (asl_comment_location_string (FST (SND x)) ((FST (SND (SND x))) arg)) (SND (SND (SND x)) arg))) specs) ==>

ASL_SPECIFICATION f lock_decls specs``,

SIMP_TAC std_ss [ASL_SPECIFICATION_def,
   asl_comment_location_string_def, LET_THM] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC ASL_INFERENCE___PROCEDURE_SPEC THEN
Q.EXISTS_TAC `\penv'. ASL_PROCEDURE_SPEC (f,LIST_TO_FUN lock_decls)
   penv' (ASL_proc_specs_spec (MAP SND (FILTER (\x. ~FST x) specs)))` THEN
REPEAT CONJ_TAC THENL [
   FULL_SIMP_TAC std_ss [ASL_PROCEDURE_SPEC___wellformed_spec_def,
      FDOM_ASL_proc_specs_penv, IN_LIST_TO_SET,
      EVERY_MEM, ASL_proc_specs_spec_def, MEM_MAP,
      GSYM LEFT_FORALL_IMP_THM, IN_UNION, MEM_FILTER] THEN
   PROVE_TAC[],


   Q.PAT_ASSUM `ASL_PROCEDURE_SPEC X Y Z` MP_TAC THEN
   SIMP_TAC std_ss [ASL_PROCEDURE_SPEC_def] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_ASSUM `!name abst. X name abst` (MP_TAC o Q.SPECL [`name`, `abst`]) THEN
   ASM_SIMP_TAC std_ss [GSYM LEFT_EXISTS_IMP_THM] THEN
   Q.EXISTS_TAC `arg` THEN
   Q.ABBREV_TAC `penv' = (ASL_proc_specs_penv penv (MAP SND (FILTER FST specs)))` THEN
   `asl_prog_IS_PROCCALL_FREE (abst arg)` by ALL_TAC THEN1 (
      Q.PAT_ASSUM `EVERY P specs` MP_TAC THEN
      Q.PAT_ASSUM `MEM X Y` MP_TAC THEN
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      SIMP_TAC std_ss [EVERY_MEM, GSYM RIGHT_FORALL_IMP_THM, GSYM LEFT_EXISTS_IMP_THM,
    ASL_proc_specs_spec_def, MEM_MAP, MEM_FILTER, GSYM RIGHT_EXISTS_AND_THM] THEN
      METIS_TAC[]
   ) THEN
   SIMP_TAC std_ss [ASL_PROGRAM_IS_ABSTRACTION_def] THEN
   Q.MATCH_ABBREV_TAC `(fasl_action_order a11 a12) ==>
             (fasl_action_order a21 a22)` THEN
   `a22 = a12` by ALL_TAC THEN1 (
      UNABBREV_ALL_TAC THEN
      METIS_TAC[asl_prog_IS_PROCCALL_FREE_def]
   ) THEN
   `fasl_action_order a21 a11` by ALL_TAC THEN1 (
      UNABBREV_ALL_TAC THEN
      SIMP_TAC std_ss [ASL_EQUIV_PENV_PROC___PROGRAM_SEM,
     ASL_PROGRAM_SEM___PROC_THM] THEN
      MATCH_MP_TAC fasl_action_order___SUP_fasl_action_order___IMPL THEN
      SIMP_TAC std_ss [IN_ABS, GSYM LEFT_EXISTS_AND_THM] THEN
      GEN_TAC THEN Q.EXISTS_TAC `n` THEN
      REWRITE_TAC[fasl_order_REFL]
   ) THEN
   PROVE_TAC[fasl_action_order_TRANSITIVE],


   Q.PAT_ASSUM `ASL_PROCEDURE_SPEC X Y Z` (K ALL_TAC) THEN
   FULL_SIMP_TAC std_ss [ASL_proc_specs_penv_def,
      LIST_TO_FMAP___ALL_DISTINCT,
      ASL_PROCEDURE_SPEC_def, EVERY_MEM,
      ASL_proc_specs_spec_def, MEM_MAP,
      GSYM LEFT_FORALL_IMP_THM, MEM_FILTER] THEN
   REPEAT STRIP_TAC THEN
   `(penv |++
    MAP (\x. (FST x,FST (SND x))) (MAP SND (FILTER FST specs))) '
     (FST (SND y)) = FST (SND (SND y))` by ALL_TAC THEN1 (

      MATCH_MP_TAC FUPDATE_LIST_APPLY___ALL_DISTINCT THEN
      CONJ_TAC THENL [
     Q.PAT_ASSUM `ALL_DISTINCT X` MP_TAC THEN
     REPEAT (POP_ASSUM (K ALL_TAC)) THEN
     SIMP_TAC std_ss [MEM_MAP, MAP_MAP_o,
         combinTheory.o_DEF] THEN
     Induct_on `specs` THEN
     ASM_SIMP_TAC list_ss [COND_RAND, COND_RATOR, MEM_FILTER,
         MEM_MAP] THEN
     PROVE_TAC[],


     SIMP_TAC std_ss [MEM_MAP, GSYM RIGHT_EXISTS_AND_THM, MEM_FILTER] THEN
     Q.EXISTS_TAC `y` THEN
     ASM_REWRITE_TAC[]
      ]
   ) THEN
   ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[]
]);


val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prim_command =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prim_command",
``!c. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_prog_prim_command c)``,
SIMP_TAC std_ss [asl_prog_IS_RESOURCE_AND_PROCCALL_FREE_def,
ASL_PROGRAM_SEM___prim_command, ASL_ATOMIC_ACTION_SEM_def]);


val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___SIMPLE_REWRITES =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___SIMPLE_REWRITES",
``asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_prog_best_local_action P Q) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_prog_quant_best_local_action qP qQ) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_prog_release_lock P) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE asl_prog_skip /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_comment_assert qP) /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE asl_prog_fail /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE asl_prog_diverge``,

REWRITE_TAC[asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prim_command,
asl_prog_best_local_action_def, asl_prog_quant_best_local_action_def,
asl_prog_release_lock_def, asl_comment_assert_def,
asl_prog_skip_def, asl_prog_fail_def, asl_prog_diverge_def]);



val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___comments =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___comments",
``(!c p. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_comment_location c p) =
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE p) /\
  (!c p. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_comment_location_string c p) =
    asl_prog_IS_RESOURCE_AND_PROCCALL_FREE p) /\
  (!c p. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_comment_location2 c p) =
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE p) /\
  (!c p. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_comment_abstraction c p) =
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE p) /\
  (!c p. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_comment_block_spec c p) =
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE p) /\
  (!c p. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_comment_loop_spec c p) =
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE p) /\
  (!n p. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_comment_loop_unroll n p) =
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE p) /\
  (!c p. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_comment_loop_invariant c p) =
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE p)``,
REWRITE_TAC[asl_comments_ELIM]);





val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_seq =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_seq",
``!prog1 prog2.
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE prog1 /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE prog2 ==>
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE
    (asl_prog_seq prog1 prog2)``,

SIMP_TAC std_ss [asl_prog_IS_RESOURCE_AND_PROCCALL_FREE_def,
   ASL_PROGRAM_SEM___prog_seq] THEN
METIS_TAC[]);



val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_block =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_block",
``!L. EVERY asl_prog_IS_RESOURCE_AND_PROCCALL_FREE L ==>
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_prog_block L)``,

Induct_on `L` THEN1 (
  SIMP_TAC list_ss [asl_prog_block_def,
          asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___SIMPLE_REWRITES]
) THEN
Cases_on `L` THEN1 SIMP_TAC list_ss [asl_prog_block_def] THEN
FULL_SIMP_TAC list_ss [asl_prog_block_def, asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_seq]);



val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_cond =
store_thm("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_cond",
``!p1 p2 c.
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE p1 /\
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE p2 ==>
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE
    (asl_prog_cond c p1 p2)``,

SIMP_TAC std_ss [asl_prog_IS_RESOURCE_AND_PROCCALL_FREE_def,
   asl_prog_cond_def, ASL_PROGRAM_SEM___prog_choice,
   ASL_PROGRAM_SEM___prog_seq, ASL_PROGRAM_SEM___prim_command,
   ASL_ATOMIC_ACTION_SEM_def] THEN
METIS_TAC[]);


val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_repeat_num =
store_thm("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_repeat_num",
``!n p. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE p ==>
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_prog_repeat_num n p)``,

SIMP_TAC std_ss [asl_prog_IS_RESOURCE_AND_PROCCALL_FREE_def] THEN
Induct_on `n` THEN (
   SIMP_TAC std_ss [ASL_PROGRAM_SEM___prog_repeat]
) THEN
METIS_TAC[]);


val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_kleene_star =
store_thm("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_kleene_star",
``!p. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE p ==>
      asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_prog_kleene_star p)``,

REPEAT STRIP_TAC THEN
IMP_RES_TAC asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_repeat_num THEN
FULL_SIMP_TAC std_ss [asl_prog_IS_RESOURCE_AND_PROCCALL_FREE_def,
   ASL_PROGRAM_SEM___prog_kleene_star] THEN
REPEAT STRIP_TAC THEN
AP_TERM_TAC THEN
AP_THM_TAC THEN
AP_TERM_TAC THEN
SIMP_TAC std_ss [FUN_EQ_THM] THEN
METIS_TAC[]);


val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_while =
store_thm("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_while",
``!p c. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE p ==>
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_prog_while c p)``,

EXT_CONSEQ_REWRITE_TAC [] [asl_prog_while_def] ([], [
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_seq,
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_kleene_star,
   asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prim_command], []));



val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_aquire_lock =
store_thm("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_aquire_lock",
``!c P. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_prog_aquire_lock c P)``,
REPEAT GEN_TAC THEN
REWRITE_TAC [asl_prog_aquire_lock_def] THEN
MATCH_MP_TAC asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_seq THEN
REWRITE_TAC [asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prim_command]);



val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_forall =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_forall",
``!body.
  ((!arg. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (body arg)) ==>
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_prog_forall body))``,

SIMP_TAC std_ss [asl_prog_IS_RESOURCE_AND_PROCCALL_FREE_def,
   ASL_PROGRAM_SEM___prog_forall, IMAGE_ABS, IN_ABS, IN_UNIV,
   GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
AP_TERM_TAC THEN
METIS_TAC[]);


val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_ndet =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_ndet",
``!pset.
  ((!p. p IN pset ==> asl_prog_IS_RESOURCE_AND_PROCCALL_FREE p) ==>
  asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_prog_ndet pset))``,

SIMP_TAC std_ss [asl_prog_IS_RESOURCE_AND_PROCCALL_FREE_def,
   ASL_PROGRAM_SEM___prog_ndet, IMAGE_ABS, IN_ABS, IN_UNIV,
   GSYM RIGHT_EXISTS_AND_THM] THEN
REPEAT STRIP_TAC THEN
AP_TERM_TAC THEN
METIS_TAC[]);



val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_choose_constants =
store_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_choose_constants",
``!body expL.
(!argL. asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (body argL)) ==>
asl_prog_IS_RESOURCE_AND_PROCCALL_FREE (asl_prog_choose_constants body expL)``,

SIMP_TAC std_ss [asl_prog_choose_constants_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_ndet THEN
SIMP_TAC std_ss [IN_IMAGE, IN_ABS, GSYM LEFT_FORALL_IMP_THM] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_seq THEN
ASM_SIMP_TAC std_ss [asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prim_command]);



val asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___ASL_REWRITES =
  save_thm ("asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___ASL_REWRITES",
  LIST_CONJ (map GEN_ALL [
    asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prim_command,
    asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___SIMPLE_REWRITES,
    asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_seq,
    asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_block,
    asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_cond,
    asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_aquire_lock,
    asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_forall,
    asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_ndet,
    asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_choose_constants,
    asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_repeat_num,
    asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_kleene_star,
    asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___prog_while,
    asl_prog_IS_RESOURCE_AND_PROCCALL_FREE___comments]))

val _ = export_theory();
