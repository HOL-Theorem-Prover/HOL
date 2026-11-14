(* ========================================================================= *)
(* FILE          : hh05_relationScript.sml                                   *)
(* DESCRIPTION   : HolyHammer examples: relations and closures               *)
(*                                                                           *)
(* Every proof below was found by calling the hammer at the point marked     *)
(* (* hh *); the tactic that follows is the verified, minimised proof that   *)
(* HolyHammer printed.  See README.md for how to replay the calls.           *)
(* ========================================================================= *)
Theory hh05_relation
Ancestors
  relation

(* -------------------------------------------------------------------------
   relationTheory is large: hundreds of facts about closures (RTC, TC, EQC),
   well-foundedness and confluence, many of them with names that are hard
   to guess (EXTEND_RTC_TC_RIGHT1?  rpreserves_symmetric_RTC?).  This is
   where a hammer earns its keep: you state what you need and it finds the
   library fact, or a short combination of facts, that proves it.

   In all of these examples the hammer needed one or two library facts.
   Several are not literal library statements but variants (arguments
   reordered, an implication instead of an equivalence, an extra
   assumption), mirroring the style of the CoqHammer test suite.
   ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
   Reflexive-transitive and transitive closure
   ------------------------------------------------------------------------- *)

Theorem rtc_compose:
  RTC R x y /\ RTC R y z ==> RTC R x z
Proof
  (* hh *)
  metis_tac [RTC_TRANS]
QED

Theorem rtc_mono_imp:
  (!x y. R x y ==> Q x y) ==> RTC R x y ==> RTC Q x y
Proof
  (* hh *)
  metis_tac [RTC_MONOTONE]
QED

Theorem tc_imp_rtc:
  TC R x y ==> RTC R x y
Proof
  (* hh *)
  metis_tac [TC_RTC]
QED

Theorem rtc_eq_or_tc:
  RTC R x y ==> x = y \/ TC R x y
Proof
  (* hh *)
  metis_tac [RTC_CASES_TC]
QED

(* A typical "which way round was that lemma stated?" goal: the library
   has several right/left extension lemmas for RTC and TC. *)
Theorem rtc_then_step:
  RTC R x y /\ R y z ==> TC R x z
Proof
  (* hh *)
  metis_tac [EXTEND_RTC_TC_RIGHT1]
QED

Theorem rtc_of_rtc:
  RTC (RTC R) = RTC R
Proof
  (* hh *)
  metis_tac [RTC_IDEM]
QED

Theorem transitive_tc_is_self:
  transitive R ==> TC R = R
Proof
  (* hh *)
  metis_tac [transitive_TC_identity]
QED

(* -------------------------------------------------------------------------
   Symmetry and equivalence relations
   ------------------------------------------------------------------------- *)

(* The proof goes through the general "RTC preserves properties"
   machinery, which you would be unlikely to find by browsing. *)
Theorem symmetric_rtc:
  symmetric R ==> symmetric (RTC R)
Proof
  (* hh *)
  metis_tac [rpreserves_symmetric_RTC, rpreserves_def]
QED

Theorem eqc_is_equivalence:
  equivalence (EQC R)
Proof
  (* hh *)
  metis_tac [EQC_EQUIVALENCE]
QED

Theorem equivalence_join:
  equivalence R /\ R x y /\ R z y ==> R x z
Proof
  (* hh *)
  metis_tac [ALT_equivalence]
QED

Theorem inv_involutive:
  inv (inv R) = R
Proof
  (* hh *)
  metis_tac [inv_inv]
QED

(* -------------------------------------------------------------------------
   Well-foundedness
   ------------------------------------------------------------------------- *)

Theorem wf_tc:
  WF R ==> WF (TC R)
Proof
  (* hh *)
  metis_tac [WF_TC_EQN]
QED

Theorem wf_smaller:
  WF R /\ (!x y. Q x y ==> R x y) ==> WF Q
Proof
  (* hh *)
  metis_tac [WF_SUBSET]
QED

Theorem wf_irreflexive:
  WF R ==> ~R x x
Proof
  (* hh *)
  metis_tac [WF_NOT_REFL]
QED

(* -------------------------------------------------------------------------
   Confluence: the diamond property lifts to the reflexive-transitive
   closure, which is the definition of Church-Rosser (CR_def).
   ------------------------------------------------------------------------- *)

Theorem diamond_rtc:
  diamond R ==> diamond (RTC R)
Proof
  (* hh *)
  metis_tac [CR_def, establish_CR]
QED
