(* ========================================================================= *)
(* HOL NORMALIZATION FUNCTIONS.                                              *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

signature normalForms =
sig

include Abbrev
type ssdata  = simpLib.ssdata
type simpset = simpLib.simpset
  
(* ------------------------------------------------------------------------- *)
(* Replace genvars with variants on `v`.                                     *)
(*                                                                           *)
(* Example:                                                                  *)
(*   ?%%genvar%%20744 %%genvar%%20745 %%genvar%%20746.                       *)
(*     (%%genvar%%20744 \/ %%genvar%%20745 \/ ~%%genvar%%20746) /\           *)
(*     (%%genvar%%20746 \/ ~%%genvar%%20744) /\                              *)
(*     (%%genvar%%20746 \/ ~%%genvar%%20745) /\ (~q \/ ~%%genvar%%20745) /\  *)
(*     (r \/ ~%%genvar%%20745) /\ (%%genvar%%20745 \/ q \/ ~r) /\            *)
(*     (q \/ ~p \/ ~%%genvar%%20744) /\ (p \/ ~q \/ ~%%genvar%%20744) /\     *)
(*     (%%genvar%%20744 \/ ~p \/ ~q) /\ (%%genvar%%20744 \/ p \/ q) /\       *)
(*     %%genvar%%20746                                                       *)
(*   =                                                                       *)
(*   ?v v1 v2.                                                               *)
(*     (v \/ v1 \/ ~v2) /\ (v2 \/ ~v) /\ (v2 \/ ~v1) /\ (q \/ ~v1) /\        *)
(*     (r \/ ~v1) /\ (v1 \/ ~q \/ ~r) /\ (q \/ ~p \/ ~v) /\                  *)
(*     (p \/ ~q \/ ~v) /\ (v \/ ~p \/ ~q) /\ (v \/ p \/ q) /\ v2             *)
(* ------------------------------------------------------------------------- *)

val readable_vars      : term -> term
val READABLE_VARS_CONV : conv

(* ------------------------------------------------------------------------- *)
(* Conversion to combinators {S,K,I}.                                        *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (?f. !y. f y = y + 1)                                                   *)
(*   =                                                                       *)
(*   $? (S (K $!) (S (S (K S) (S (K (S (K $=))) I)) (K (S $+ (K 1)))))       *)
(* ------------------------------------------------------------------------- *)

val SKI_CONV : conv

(* ------------------------------------------------------------------------- *)
(* Conversion to combinators {S,K,I,C,o}.                                    *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (?f. !y. f y = y + 1)                                                   *)
(*   =                                                                       *)
(*   $? ($! o C (S o $o $= o I) (C $+ 1))                                    *)
(* ------------------------------------------------------------------------- *)

val SKICo_CONV : conv
  
(* ------------------------------------------------------------------------- *)
(* Beta reduction and simplifying boolean rewrites.                          *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (!x y. P x \/ (P y /\ F)) ==> ?z. P z                                   *)
(*   =                                                                       *)
(*   (!x. P x) ==> ?z. P z                                                   *)
(* ------------------------------------------------------------------------- *)

val simplify_ss   : simpset             (* pure + BOOL *)
val SIMPLIFY_CONV : conv
  
(* ------------------------------------------------------------------------- *)
(* Negation normal form.                                                     *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (!x. P x) ==> ((?y. Q y) = ?z. P z /\ Q z)                              *)
(*   =                                                                       *)
(*   ((?y. Q y) /\ (?z. P z /\ Q z) \/ (!y. ~Q y) /\ !z. ~P z \/ ~Q z) \/    *)
(*   ?x. ~P x                                                                *)
(* ------------------------------------------------------------------------- *)

val PURE_NNF_CONV' : conv -> conv       (* takes a 'leaf conversion' *)
val PURE_NNF_CONV  : conv
val NNF_CONV'      : conv -> conv       (* takes a 'leaf conversion' *)
val NNF_CONV       : conv
  
(* ------------------------------------------------------------------------- *)
(* Skolemization.                                                            *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (!x. (?y. Q y \/ !z. ~P z \/ ~Q z) \/ ~P x)                             *)
(*   =                                                                       *)
(*   ?y. !x. (Q (y x) \/ !z. ~P z \/ ~Q z) \/ ~P x                           *)
(* ------------------------------------------------------------------------- *)

val SKOLEMIZE_CONV : conv

(* ------------------------------------------------------------------------- *)
(* A basic tautology prover and simplifier for clauses                       *)
(*                                                                           *)
(* Examples:                                                                 *)
(*   TAUTOLOGY_CONV:   p \/ r \/ ~p \/ ~q   =  T                             *)
(*   CONTRACT_CONV:    (p \/ r) \/ p \/ ~q  =  p \/ r \/ ~q                  *)
(* ------------------------------------------------------------------------- *)

val TAUTOLOGY_CONV : conv
val CONTRACT_CONV : conv
  
(* ------------------------------------------------------------------------- *)
(* Conjunctive Normal Form.                                                  *)
(*                                                                           *)
(* Example:                                                                  *)
(*  (!x. P x ==> ?y z. Q y \/ ~?z. P z \/ Q z)                               *)
(*  =                                                                        *)
(*  ?y. (!x x'. Q (y x) \/ ~P x' \/ ~P x) /\ !x x'. Q (y x) \/ ~Q x' \/ ~P x *)
(* ------------------------------------------------------------------------- *)

val tautology_checking : bool ref
val PURE_CNF_CONV  : conv
val CNF_CONV'      : conv -> conv       (* takes a 'leaf conversion' *)
val CNF_CONV       : conv
  
(* ------------------------------------------------------------------------- *)
(* Disjunctive Normal Form.                                                  *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (!x. P x ==> ?y z. Q y \/ ~?z. P z \/ Q z)                              *)
(*   =                                                                       *)
(*   !x z. (?y. Q y) \/ (?y. ~P (z y) /\ ~Q (z y)) \/ ~P x                   *)
(* ------------------------------------------------------------------------- *)

val DNF_CONV'      : conv -> conv       (* takes a 'leaf conversion' *)
val DNF_CONV       : conv

(* ------------------------------------------------------------------------- *)
(* Definitional negation normal form                                         *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (~(p = ~(q = r)) = ~(~(p = q) = r))                                     *)
(*   =                                                                       *)
(*   ((p = (q = r)) = ((p = ~q) = ~r))                                       *)
(* ------------------------------------------------------------------------- *)

val DEF_NNF_CONV : conv
  
(* ------------------------------------------------------------------------- *)
(* Definitional conjunctive normal form                                      *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (~(p = ~(q = r)) = ~(~(p = q) = r))                                     *)
(*   =                                                                       *)
(*   ?v v' v'' v''' v''''.                                                   *)
(*     (v''' \/ ~v' \/ ~v'''') /\ (v' \/ ~v''' \/ ~v'''') /\                 *)
(*     (v'''' \/ ~v' \/ ~v''') /\ (v'''' \/ v' \/ v''') /\                   *)
(*     (r \/ ~v'' \/ ~v''') /\ (v'' \/ ~r \/ ~v''') /\                       *)
(*     (v''' \/ ~v'' \/ ~r) /\ (v''' \/ v'' \/ r) /\ (q \/ ~p \/ ~v'') /\    *)
(*     (p \/ ~q \/ ~v'') /\ (v'' \/ ~p \/ ~q) /\ (v'' \/ p \/ q) /\          *)
(*     (v \/ p \/ ~v') /\ (~p \/ ~v \/ ~v') /\ (v' \/ p \/ ~v) /\            *)
(*     (v' \/ ~p \/ v) /\ (r \/ q \/ ~v) /\ (~q \/ ~r \/ ~v) /\              *)
(*     (v \/ q \/ ~r) /\ (v \/ ~q \/ r) /\ v''''                             *)
(* ------------------------------------------------------------------------- *)

val DEF_CNF_CONV : conv

(* ------------------------------------------------------------------------- *)
(* Removes leading existential quantifiers from a theorem.                   *)
(*                                                                           *)
(* Examples:                                                                 *)
(*   EXISTENTIAL_CONST_RULE   ``a``   |- ?x. P x y z                         *)
(*   ---->  [a = @x. P x y z] |- P a y                                       *)
(*                                                                           *)
(*   EXISTENTIAL_CONST_RULE   ``a y z``   |- ?x. P x y                       *)
(*   ---->  [a = \y z. @x. P x y z] |- P (a y z) y                           *)
(*                                                                           *)
(* NEW_CONST_RULE creates a new variable as the argument to                  *)
(* EXISTENTIAL_CONST_RULE, and CLEANUP_CONSTS_RULE tries to eliminate        *)
(* as many of these new equality assumptions as possible.                    *)
(* ------------------------------------------------------------------------- *)

val EXISTENTIAL_CONST_RULE : term -> rule
val NEW_CONST_RULE         : rule
val CLEANUP_CONSTS_RULE    : rule

(* ------------------------------------------------------------------------- *)
(* Eliminates some lambdas to make terms "as first-order as possible".       *)
(*                                                                           *)
(* Example:  ((\x. f x z) = g z)  =  !x. f x z = g z x                       *)
(* ------------------------------------------------------------------------- *)

val DELAMB_CONV : conv
  
(* ------------------------------------------------------------------------- *)
(* Eliminating Hilbert's epsilon operator.                                   *)
(*                                                                           *)
(* Example:                                                                  *)
(*                                                                           *)
(*   ((?n. f n = 0) ==> (f n = 0)) ==> 3 < n                                 *)
(*   ---------------------------------------  SELECT_TAC                     *)
(*               3 < @n. f n = 0                                             *)
(* ------------------------------------------------------------------------- *)

val SELECT_TAC : tactic

(* ------------------------------------------------------------------------- *)
(* Lifting conditionals through function applications.                       *)
(*                                                                           *)
(* Example:  f (if x then y else z)  =  (if x then f y else f z)             *)
(* ------------------------------------------------------------------------- *)

val cond_lift_SS  : ssdata
val cond_lift_ss  : simpset      (* pure + cond_lift *)

(* ------------------------------------------------------------------------- *)
(* Converting boolean connectives to conditionals.                           *)
(*                                                                           *)
(* Example:  x /\ ~(y ==> ~z)  =  (if x then (if y then z else F) else F)    *)
(* ------------------------------------------------------------------------- *)

val condify_SS    : ssdata
val condify_ss    : simpset      (* pure + condify *)
  
end
