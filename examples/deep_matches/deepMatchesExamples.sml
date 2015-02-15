open bossLib 
open deepMatchesLib
open deepMatchesTheory
open deepMatchesSyntax

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

REPEAT STRIP_TAC THENL [
  ASM_SIMP_TAC (std_ss++PMATCH_SIMP_ss) [my_d_def],

  ASM_SIMP_TAC (arith_ss++PMATCH_SIMP_ss) [my_d_def],

  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [my_d_def])) THEN
  SIMP_TAC (std_ss ++ PMATCH_SIMP_ss) []
])

(* Let's prove it via lifting *)
val my_d_thms2 = store_thm ("my_d_thms2",
``(!x. x > 3 ==> (my_d (x, []) = x)) /\ 
  (!x. x <= 3 ==> (my_d (x, []) = 0)) /\ 
  (!x y ys. my_d (x, y::ys) = my_d (x + y, ys))``,

REPEAT STRIP_TAC THEN (
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [my_d_def])) THEN
  ASM_SIMP_TAC (arith_ss++PMATCH_LIFT_BOOL_ss) []
))

