(* ========================================================================= *)
(* HOL NORMALIZATION FUNCTIONS.                                              *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

signature normalForms =
sig

include Abbrev
type ssfrag  = simpLib.ssfrag
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

val prettify_vars      : term -> term
val PRETTIFY_VARS_CONV : conv

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
(* Prenex Normal Form.                                                       *)
(* ------------------------------------------------------------------------- *)

val PRENEX_CONV      : conv
val ANTI_PRENEX_CONV : conv

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
(* Definitional Negation Normal Form                                         *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (~(p = ~(q = r)) = ~(~(p = q) = r))                                     *)
(*   =                                                                       *)
(*   ((p = (q = r)) = ((p = ~q) = ~r))                                       *)
(* ------------------------------------------------------------------------- *)

val DEF_NNF_CONV : conv

(* ------------------------------------------------------------------------- *)
(* Definitional Conjunctive Normal Form                                      *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (~(p = ~(q = r)) = ~(~(p = q) = r))                                     *)
(*   =                                                                       *)
(*   ?v v1 v2 v3 v4.                                                         *)
(*     (v4 \/ v1 \/ v3) /\ (v4 \/ ~v1 \/ ~v3) /\ (v1 \/ ~v3 \/ ~v4) /\       *)
(*     (v3 \/ ~v1 \/ ~v4) /\ (v3 \/ v2 \/ ~r) /\ (v3 \/ ~v2 \/ r) /\         *)
(*     (v2 \/ r \/ ~v3) /\ (~r \/ ~v2 \/ ~v3) /\ (v2 \/ p \/ ~q) /\          *)
(*     (v2 \/ ~p \/ q) /\ (p \/ q \/ ~v2) /\ (~q \/ ~p \/ ~v2) /\            *)
(*     (v1 \/ p \/ v) /\ (v1 \/ ~p \/ ~v) /\ (p \/ ~v \/ ~v1) /\             *)
(*     (v \/ ~p \/ ~v1) /\ (v \/ q \/ r) /\ (v \/ ~q \/ ~r) /\               *)
(*     (q \/ ~r \/ ~v) /\ (r \/ ~q \/ ~v) /\ v4                              *)
(* ------------------------------------------------------------------------- *)

val PURE_DEF_CNF_CONV    : conv         (* Introduces definitions *)
val CLEANUP_DEF_CNF_CONV : conv         (* Converts defns to CNF *)
val DEF_CNF_CONV         : conv         (* NNF + PURE + CLEANUP *)

val ORACLE_PURE_DEF_CNF_CONV : conv     (* Simply asserts the conversion thm *)
val ORACLE_DEF_CNF_CONV      : conv     (* NNF + ORACLE_PURE + CLEANUP *)

(* ------------------------------------------------------------------------- *)
(* Removes leading existential quantifiers from a theorem, by introducing a  *)
(* new skolem constant with an appropriate assumption.                       *)
(*                                                                           *)
(* Examples:                                                                 *)
(*   SKOLEM_CONST_RULE   ``a``   |- ?x. P x y z                              *)
(*   ---->  [a = @x. P x y z] |- P a y                                       *)
(*                                                                           *)
(*   SKOLEM_CONST_RULE   ``a y z``   |- ?x. P x y                            *)
(*   ---->  [a = \y z. @x. P x y z] |- P (a y z) y                           *)
(*                                                                           *)
(* NEW_SKOLEM_CONST generates an argument for SKOLEM_CONST_RULE, and         *)
(* NEW_SKOLEM_CONST_RULE puts the two functions together.                    *)
(* CLEANUP_SKOLEM_CONSTS_RULE tries to eliminate as many 'skolem             *)
(* assumptions' as possible.                                                 *)
(* ------------------------------------------------------------------------- *)

val SKOLEM_CONST_RULE          : term -> rule
val NEW_SKOLEM_CONST           : thm -> term
val NEW_SKOLEM_CONST_RULE      : rule
val CLEANUP_SKOLEM_CONSTS_RULE : rule

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
(* Remove all Abbrev terms from a goal by rewriting them away (Abbrev = I)   *)
(* ------------------------------------------------------------------------- *)

val REMOVE_ABBR_TAC : tactic

(* ------------------------------------------------------------------------- *)
(* Lifting conditionals through function applications.                       *)
(*                                                                           *)
(* Example:  f (if x then y else z)  =  (if x then f y else f z)             *)
(* ------------------------------------------------------------------------- *)

val cond_lift_SS : ssfrag
val cond_lift_ss : simpset      (* pure + cond_lift *)

(* ------------------------------------------------------------------------- *)
(* Converting boolean connectives to conditionals.                           *)
(*                                                                           *)
(* Example:  x /\ ~(y ==> ~z)  =  (if x then (if y then z else F) else F)    *)
(* ------------------------------------------------------------------------- *)

val condify_SS : ssfrag
val condify_ss : simpset      (* pure + condify *)

(* ------------------------------------------------------------------------- *)
(* Definitional CNF minimizing number of clauses.                            *)
(*                                                                           *)
(* Example:                                                                  *)
(* |- (p /\ q /\ r) \/ (s /\ t /\ u)                                         *)
(*    -->                                                                    *)
(* ([``d``],                                                                 *)
(*   [[.] |- (d \/ s) /\ (d \/ t) /\ (d \/ u),                               *)
(*    [.] |- (d \/ ~p \/ ~q \/ ~r) /\ (~d \/ p) /\ (~d \/ q) /\ (~d \/ r)])  *)
(*                                                                           *)
(* where the assumption [.] in both theorems is d = (p /\ q /\ r).           *)
(* ------------------------------------------------------------------------- *)

val MIN_CNF : thm list -> term list * thm list

end
