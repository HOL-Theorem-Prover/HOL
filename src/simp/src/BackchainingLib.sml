structure BackchainingLib :> BackchainingLib =
struct

open HolKernel Parse Drule ConseqConv simpLib Conv Tactic Tactical boolSyntax boolTheory

local

fun RESTRICTED_RES_CANON_WITH_MARK thm = let
  val _ = dest_imp_only (snd (strip_forall (concl thm)))

  (* Mark thm so it does not get changed below*)
  val thm' = CONV_RULE (STRIP_QUANT_CONV (RAND_CONV (markerLib.stmark_term))) thm
in
  List.map GEN_ALL (IMP_CANON thm')
end handle HOL_ERR _ => [];

fun RES_ALL_PRECONDS_WITH_MARK asms results [] = results
  | RES_ALL_PRECONDS_WITH_MARK asms results (thm::thms) =
  if is_imp_only (snd (strip_forall (concl thm))) then
  let
     val new_thms  = mapfilter (MATCH_MP thm) asms
  in
     RES_ALL_PRECONDS_WITH_MARK asms results (append new_thms thms)
  end else let
    val thm' = CONV_RULE (STRIP_QUANT_CONV (REWR_CONV markerTheory.stmarker_def)) thm
    val is_old = List.exists (fn thm'' => aconv (concl thm') (concl thm'')) results
    val results' = if is_old then results else thm'::results
  in
    RES_ALL_PRECONDS_WITH_MARK asms results' thms
  end handle HOL_ERR _ =>
    RES_ALL_PRECONDS_WITH_MARK asms results thms

in

fun BACKCHAIN_THEN ttac input_thms = let
  val thms0 = Lib.flatten (List.map BODY_CONJUNCTS input_thms)
  val thms1 = Lib.flatten (List.map RESTRICTED_RES_CANON_WITH_MARK thms0)
in
  Tactical.ASSUM_LIST (fn asms =>
    ttac (RES_ALL_PRECONDS_WITH_MARK asms [] thms1))
end

end


fun BACKCHAIN_EVERY_THEN ttac =
  BACKCHAIN_THEN (fn thms => EVERY (List.map (fn thm => (TRY (ttac thm))) thms))

val BACKCHAIN_ASSUME_TAC =
  BACKCHAIN_EVERY_THEN STRIP_ASSUME_TAC

val BACKCHAIN_MP_TAC =
  BACKCHAIN_EVERY_THEN MP_TAC

val BACKCHAIN_TAC =
  BACKCHAIN_THEN (fn thms => ConseqConv.CONSEQ_REWRITE_TAC (thms, [], []))


fun BC_SIMP_TAC ss gthms thms' =
  BACKCHAIN_THEN (fn thms => SIMP_TAC ss (thms @ thms')) gthms

fun ASM_BC_SIMP_TAC ss gthms thms' =
  BACKCHAIN_THEN (fn thms => ASM_SIMP_TAC ss (thms @ thms')) gthms

fun FULL_BC_SIMP_TAC ss gthms thms' =
  BACKCHAIN_THEN (fn thms => FULL_SIMP_TAC ss (thms @ thms')) gthms


(************************************************************)
(* Some demo

val R_def = Define `R x y = (x:num) > y`

val R1 = prove (``R x y ==> x <= x' /\ y' <= y ==> R x' y'``,
  SIMP_TAC arith_ss [R_def])

(* As a first simple test prove just R1 again. *)

``R x y ==> x <= x' /\ y' <= y ==> R x' y'``,

REPEAT STRIP_TAC THEN

(* METIS does of course the trick.
METIS_TAC[R1]
*)

(* Conditional rewriting does not manage to do it
ASM_SIMP_TAC std_ss [R1]

It needs to solve the following precondition

?y x. R x y /\ x <= x' /\ y' <= y

in order to apply the conditional rewrite. This however, requires
instantiating x and, which it does not manage. Even using tools
like QI_ss does not help since two vars need instantiating at once.

set_trace "simplifier" 1
ASM_SIMP_TAC (std_ss++QI_ss) [R1]
*)

(* One can of course apply the rule manually backwards using MATCH_MP_TAC.

val R1' = IRULE_CANON R1
MATCH_MP_TAC R1'

This is however applicable only at toplevel. Consequence rewrites are handy,
but easily loop.

ConseqConv.ONCE_CONSEQ_REWRITE_TAC ([R1'], [], []) THEN
ConseqConv.ONCE_CONSEQ_REWRITE_TAC ([R1'], [], []) THEN
ConseqConv.ONCE_CONSEQ_REWRITE_TAC ([R1'], [], [])

ConseqConv.CONSEQ_REWRITE_TAC ([R1'], [], [])

*)

(* IMP_RES_TAC works in this simple case, but often produces a lot of clutter (see later)

IMP_RES_TAC R1

*)

(* So lets try the new stuff. *)

BACKCHAIN_TAC [R1]
BACKCHAIN_MP_TAC [R1]
BACKCHAIN_ASSUME_TAC [R1]
ASM_BC_SIMP_TAC std_ss [R1] []


Now let's look at more interesting examples:

``R x y ==> x <= 10 /\ x < 20 /\ x' > 15 /\ y' <= 20 /\ 21 <= y ==>
  (R x' y' /\ R 10 y' /\ (x < 12))``,

STRIP_TAC THEN STRIP_TAC

(* No IMP_RES_TAC produces a lot of not useful stuff.
   More importantly, the real interesting instances are not produced!
 *)
IMP_RES_TAC R1

(* Metis fails as well, since some arithmetic reasoning is needed *)
METIS_TAC[R1]

(* MATCH_MP_TAC is painful since it requires splitting the goal,
   BACKCHAIN_TAC is more handy. *)

BACKCHAIN_TAC [R1]
DECIDE_TAC

(* Combined with the simplifier, it is immediately solved *)
ASM_BC_SIMP_TAC arith_ss [R1] []


(* This is useful, if some goals cannot be solved completely.

``R x y /\ x <= 10 /\ x < 20 /\ x' > 15 /\ y' <= 20 /\ 21 <= y ==>
  (R x' y' /\ QQ x y y' /\ R 5 x' /\ (x < 12))``,


STRIP_TAC
ASM_BC_SIMP_TAC arith_ss [R1] []


One can use more interesting preconditions as well.

val R2 = prove (``(R x y \/ x > y \/ y < x) ==> x <= x' /\ y' <= y ==> R x' y'``,
  SIMP_TAC arith_ss [R_def])


``6 > 5 /\ 10 < x /\ 10 < x' /\ 30 < x /\ y <= 20 /\ x < 100 /\ 100 <= x' ==>
  R x' y /\ QQ x' y``,

STRIP_TAC

(* Now there are multiple theorems produced. BACKCHAIN_TAC picks the wrong
   instantiation and one cannot solve the resulting goal :-( *)
BACKCHAIN_TAC [R2] THEN
ASM_SIMP_TAC arith_ss []

(* If one instead checks all possible instances, it can be solved *)
BACKCHAIN_MP_TAC [R2] THEN
ASM_SIMP_TAC arith_ss []

(* XXX *)
IMP_RES_THEN MP_TAC R2

(* In combination with conditional rewriting, this leads to a nice user experience
   neither cluttering the state nor picking unsuited instances. *)

ASM_BC_SIMP_TAC arith_ss [R2] []

*)
*)


end
