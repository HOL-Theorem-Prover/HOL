open bossLib 
open deepMatchesLib
open deepMatchesTheory
open deepMatchesSyntax
open pred_setTheory
open constrFamiliesLib
open stringTheory 
open pred_setLib

(* Introducing case expressions *)

val t = ``case x of (NONE, []) => 0``
val t' = convert_case t 
val thm_t = PMATCH_INTRO_CONV t

(* check that SIMP works *)
val thm_t' = PMATCH_REMOVE_ARB_CONV t'
val thm_t' = PMATCH_SIMP_CONV t'

		    
(* more fancy *)
val t = ``case x of 
   (NONE, []) => 0
 | (SOME 2, []) => 2
 | (SOME 3, (x :: xs)) => 3 + x
 | (SOME _, (x :: xs)) => x``
val t' = convert_case t 
val thm_t = PMATCH_INTRO_CONV t

val thm_t' = PMATCH_REMOVE_ARB_CONV t'
val thm_t' = PMATCH_SIMP_CONV t'

(* Playing around with some examples *)

val example1 = ``
  CASE (a,x,xs) OF [
    ||. (NONE,4,[]) ~> 0;
    || x. (NONE,x,[]) when x < 10 ~> x;
    || x. (NONE,x,[2]) ~> x;
    || (x,v18). (NONE,x,[v18]) ~> 3;
    || (x,v12,v16,v17). (NONE,x,v12::v16::v17) ~> 3;
    || (y,x,z,zs). (SOME y,x,[z]) ~> x + 5 + z;
    || (y,v23,v24). (SOME y,0,v23::v24) ~> (v23 + y);
    || (y,z,v23). (SOME y,SUC z,[v23]) when y > 5 ~> 3;
    || (y,z). (SOME y,SUC z,[1; 2]) ~> y + z
  ]``;

val example2 = ``PMATCH (h::t)
  [PMATCH_ROW (\_ . []) (\_. T) (\_. x);
   PMATCH_ROW (\_. [2]) (\_. T) (\_. x); 
   PMATCH_ROW (\v18. [v18]) (\v18. T) (\v18. 3);
   PMATCH_ROW (\ (v12,v16,v17). (v12::v16::v17))
              (\ (v12,v16,v17). T)
              (\ (v12,v16,v17). 3);
   PMATCH_ROW (\_. [2; 4; 3]) (\_. T) (\_. 3 + x)]``

val example3 = ``
  CASE (NONE,x,xs) OF [
    || x. (NONE,x,[]) ~> x;
    || x. (NONE,x,[2]) ~> x;
    || (x,v18). (NONE,x,[v18]) ~> 3;
    || (x,v12,v16,v17). (NONE,x,v12::v16::v17) ~> 3;
    || (y,x). (y,x,[2; 4; 3]) when (x > 5) ~> (3 + x)
  ]``;


(* turn off pretty printer *)

set_trace "use pmatch_pp" 0;
example1;
set_trace "use pmatch_pp" 1;
example1;


PMATCH_SIMP_CONV example1 
PMATCH_SIMP_CONV example2
PMATCH_SIMP_CONV example3

set_goal ([], ``^example1 = XXX``);

e (Cases_on `a`)
e (SIMP_TAC (std_ss++PMATCH_SIMP_ss) [])
e (Cases_on `xs`)
e (CONV_TAC (DEPTH_CONV PMATCH_SIMP_CONV))

proofManagerLib.restart ()

e (Cases_on `xs`)
e (CONV_TAC (DEPTH_CONV PMATCH_SIMP_CONV))

proofManagerLib.restart ()

e (Cases_on `x`)
e (SIMP_TAC (std_ss++PMATCH_SIMP_ss) [])
e (Cases_on `xs`)

proofManagerLib.rotate 1
e (SIMP_TAC (std_ss++PMATCH_SIMP_ss) [])

proofManagerLib.drop ()


(**************************************)
(* Playing around with parsing        *)
(**************************************)

(* set parsing of case expression to deep ones *)
set_trace "parse deep cases" 1;

val ex1 = ``case (x, y, z) of 
    (x, [], NONE) => x
  | (x, [], SOME y) => x+y
  | (_, z::zs, _) => z``

(* there are new features as well. Multiple
   occurences of the same variable in a pattern are fine *)

val ex2 = ``case (x, y) of 
    (x, x) => T
  | _ => F``


(* let's prove that this really behaves as expected.
   Notice that here the simpset-fragments for
   PMATCH picks out information from the context to
   simplify the PMATCH. *)

val ex2_thm = prove (``^ex2 = (x = y)``,

SIMP_TAC (std_ss++PMATCH_SIMP_ss) [] THEN
Cases_on `x=y` THEN (
  ASM_SIMP_TAC (std_ss++PMATCH_SIMP_ss) []
))


(**************************************)
(* PMATCH has necessary congruences   *)
(* theorems to use for recursive defs *)
(**************************************)

val my_d_def = Define
  `my_d xx = CASE xx OF [
    || x.  (x, []) when x > 3 ~> x;
    || x.  (x, []) ~> 0;
    || (x, y, ys). (x, y::ys) ~> my_d (x + y, ys)]`

val my_d_thms = store_thm ("my_d_thms",
``(!x. x > 3 ==> (my_d (x, []) = x)) /\ 
  (!x. x <= 3 ==> (my_d (x, []) = 0)) /\ 
  (!x y ys. my_d (x, y::ys) = my_d (x + y, ys))``,

REPEAT STRIP_TAC THEN (
  ASM_SIMP_TAC (arith_ss++PMATCH_SIMP_ss) [Once my_d_def]
));

(* Let's prove it via lifting *)
val my_d_thms2 = store_thm ("my_d_thms2",
``(!x. x > 3 ==> (my_d (x, []) = x)) /\ 
  (!x. x <= 3 ==> (my_d (x, []) = 0)) /\ 
  (!x y ys. my_d (x, y::ys) = my_d (x + y, ys))``,

REPEAT STRIP_TAC THEN (
  ASM_SIMP_TAC (arith_ss++PMATCH_LIFT_BOOL_ss) [Once my_d_def]
))

(* This lifting is also automated as a rule*)
val my_d_thms3 = PMATCH_TO_TOP_RULE my_d_def

(* The result is not as nice, but often useful

 val my_d_thms3 =
   |- (∀x. x > 3 ⇒ (my_d (x,[]) = x)) ∧
   (∀x. ¬(x > 3) ⇒ (my_d (x,[]) = 0)) ∧
   (∀x y ys. my_d (x,y::ys) = my_d (x + y,ys)) ∧
   ∀xx. (∀x. xx ≠ (x,[])) ∧ (∀x y ys. xx ≠ (x,y::ys)) ⇒ (my_d xx = ARB):
   thm
*)

(*********************************)
(* Compiling                     *)
(*********************************)

val _ = Datatype `
  tree = Empty
       | Red tree 'a tree
       | Black tree 'a tree`;

val balance_black_def = Define `balance_black a n b =
   CASE (a,b) OF [
       || (a,x,b,y,c,d). (Red (Red a x b) y c,d) ~>
            (Red (Black a x b) y (Black c n d));
       || (a,x,b,y,c,d). (Red a x (Red b y c),d) ~>
            (Red (Black a x b) y (Black c n d));
       || (a,b,y,c,z,d). (a,Red (Red b y c) z d) ~>
            (Red (Black a n b) y (Black c z d));
       || (a,b,y,c,z,d). (a,Red b y (Red c z d)) ~>
            (Red (Black a n b) y (Black c z d));
       || other. other ~> (Black a n b)
     ]`

(* try to compile to a tree inside the logic *)
val balance_black_dectree_def = CONV_RULE
  (TOP_SWEEP_CONV (PMATCH_CASE_SPLIT_CONV (fn _ => 0))) 
  balance_black_def

open stringTheory
val string_match_def = Define `string_match s x =
   CASE (s, x) OF [
       || x. ("SUC", x) ~> SUC x;
       || x. ("DOUBLE", x) ~> (x * 2);
       || (s, x). (s, x) ~> x
     ]`

val string_match_dectree_def = CONV_RULE
  (TOP_SWEEP_CONV (PMATCH_CASE_SPLIT_CONV (fn _ => 0))) 
  string_match_def


(*********************************)
(* Constructor families          *)
(*********************************)

val list_REVCASE_def = Define `
  list_REVCASE l c_nil c_snoc =
    (if l = [] then c_nil else (
     c_snoc (LAST l) (BUTLAST l)))`

val list_REVCASE_THM = prove (``
  ((list_REVCASE [] c_nil c_snoc) = c_nil) /\
  ((list_REVCASE (SNOC x xs) c_nil c_snoc) = c_snoc x xs)``,
SIMP_TAC list_ss [list_REVCASE_def, rich_listTheory.NOT_SNOC_NIL])

val c_nil = mk_constructor ``[]:'a list`` []
val c_snoc = mk_constructor ``SNOC: 'a -> 'a list -> 'a list`` 
   ["x", "xs"]

val cl = mk_constructorList true [c_nil, c_snoc]

val cf = mk_constructorFamily (cl, ``list_REVCASE``,
  SIMP_TAC list_ss [rich_listTheory.NOT_SNOC_NIL] THEN
  REPEAT STRIP_TAC THENL [
    ASSUME_TAC (Q.SPEC `x` listTheory.SNOC_CASES) THEN
    FULL_SIMP_TAC std_ss [list_REVCASE_THM],

    PROVE_TAC [listTheory.SNOC_CASES]
  ]
)

val t = ``CASE l OF [
  ||. [] ~> 0;
  || (x, xs). SNOC x xs ~> x
  ]``


(*********************************)
(* Using non-injective patterns  *)
(*********************************)

(* Normally patterns should be injective.
   However, the tools even work, if they are not.
   The following definition defines cardinality
   of sets in a simple case and more advanced. *)

val simple_card_def = Define `
  simple_card s = CASE s OF [
    ||. {} ~> SOME 0;
    || x. {x} ~> SOME 1;
    || (x, y). {x; y} ~> SOME 2;
    || s. s ~> NONE
  ]`;

val simple_card_THM_AUX = PMATCH_TO_TOP_RULE simple_card_def;

val simple_card_ALT_DEF = prove (``simple_card s =
  if (INFINITE s \/ CARD s > 2) then NONE else SOME (CARD s)``,

Tactical.REVERSE (Cases_on `FINITE s`) THEN1 (
  MP_TAC (Q.SPEC `s` (el 4 (CONJUNCTS simple_card_THM_AUX))) THEN
  MATCH_MP_TAC (prove (``(A /\ (B ==> C)) ==> ((A ==> B) ==> C)``, PROVE_TAC[])) THEN
  CONJ_TAC THEN1 (
    CCONTR_TAC THEN
    FULL_SIMP_TAC std_ss [] THEN
    FULL_SIMP_TAC std_ss [FINITE_INSERT, FINITE_EMPTY]
  ) THEN
  ASM_SIMP_TAC std_ss []
) THEN

Cases_on `s` THEN1 (
  SIMP_TAC std_ss [CARD_EMPTY, simple_card_THM_AUX, FINITE_EMPTY]
) THEN
Cases_on `t` THEN1 (
  SIMP_TAC std_ss [CARD_SING, simple_card_THM_AUX, FINITE_SING]
) THEN
Cases_on `t'` THEN1 (
  MP_TAC (Q.SPEC `{x;x'}` (el 3 (CONJUNCTS simple_card_THM_AUX))) THEN
  MATCH_MP_TAC (prove (``(A /\ (B ==> C)) ==> ((A ==> B) ==> C)``, PROVE_TAC[])) THEN
  CONJ_TAC THEN1 (
    FULL_SIMP_TAC std_ss [EXTENSION, IN_INSERT, NOT_IN_EMPTY] THEN
    METIS_TAC[]
  ) THEN
  REPEAT STRIP_TAC THEN
  Q.PAT_ASSUM `{x;x'} = _` (K ALL_TAC) THEN
  FULL_SIMP_TAC std_ss [FINITE_SING, CARD_INSERT, IN_INSERT,
    NOT_IN_EMPTY, CARD_SING]
) THEN1 (
  FULL_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [IN_INSERT, CARD_INSERT, FINITE_INSERT] THEN
  MP_TAC (Q.SPEC `x INSERT x' INSERT x'' INSERT t` (el 4 (CONJUNCTS simple_card_THM_AUX))) THEN
  MATCH_MP_TAC (prove (``(A /\ (B ==> C)) ==> ((A ==> B) ==> C)``, PROVE_TAC[])) THEN
  CONJ_TAC THEN1 (
    FULL_SIMP_TAC std_ss [EXTENSION, IN_INSERT, NOT_IN_EMPTY, IN_UNION] THEN
    METIS_TAC[]
  ) THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [] THEN
  Cases_on `FINITE t` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC arith_ss [CARD_INSERT, FINITE_INSERT, IN_INSERT]
));



val CARD2_defn = Defn.Hol_defn "CARD2" `
  CARD2 s = CASE s OF [
    ||. {} ~> 0;
    || (x, s'). x INSERT s' when (FINITE s' /\ ~(x IN s')) ~>
        SUC (CARD2 s');
    || s'. s' ~> 0
  ]`

val (CARD2_def, _) = Defn.tprove (CARD2_defn,
  Q.EXISTS_TAC `measure CARD` THEN
  SIMP_TAC std_ss [prim_recTheory.WF_measure,
    pred_setTheory.FINITE_INSERT] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC std_ss [prim_recTheory.measure_thm,
    pred_setTheory.CARD_INSERT]
)

val CARD2_AUX_DEFS = PMATCH_TO_TOP_RULE CARD2_def

val CARD2_EMPTY = store_thm ("CARD2_EMPTY",
  ``CARD2 {} = 0``,
REWRITE_TAC [CARD2_AUX_DEFS])

val CARD2_INFINITE = store_thm ("CARD2_INFINITE",
  ``!s. INFINITE s ==> (CARD2 s = 0)``,

REPEAT STRIP_TAC THEN
MATCH_MP_TAC (el 3 (BODY_CONJUNCTS CARD2_AUX_DEFS)) THEN
Cases_on `s = {}` THEN (
  REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
));

val CARD2_EQ = store_thm ("CARD2_EQ",
  ``!s. FINITE s ==> (CARD2 s = CARD s)``,

Induct_on `CARD s` THEN1 (
  REPEAT STRIP_TAC THEN
  `s = {}` by PROVE_TAC [CARD_EQ_0] THEN
  Q.PAT_ASSUM `0 = _` (K ALL_TAC) THEN
  ASM_REWRITE_TAC [CARD_EMPTY, CARD2_EMPTY]
) THEN
REPEAT STRIP_TAC THEN
Cases_on `s` THEN1 (
  FULL_SIMP_TAC arith_ss [CARD_EMPTY]
) THEN
Q.PAT_ASSUM `v = X` (ASSUME_TAC o GSYM) THEN
FULL_SIMP_TAC std_ss [FINITE_INSERT, CARD_INSERT] THEN

MP_TAC (Q.ISPEC `x INSERT t` (el 2 (CONJUNCTS CARD2_AUX_DEFS))) THEN
MATCH_MP_TAC (prove (``(A /\ (B ==> C)) ==> ((A ==> B) ==> C)``, PROVE_TAC[])) THEN
CONJ_TAC THEN1 (
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] THEN
  PROVE_TAC[]
) THEN
STRIP_TAC THEN
`CARD (x' INSERT s') = CARD (x INSERT t)` by PROVE_TAC[] THEN
POP_ASSUM MP_TAC THEN
Q.PAT_ASSUM `x INSERT t = _` (K ALL_TAC) THEN
ASM_SIMP_TAC std_ss [CARD_INSERT])


