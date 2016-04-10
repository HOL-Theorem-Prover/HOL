signature mg = sig
  type pat = Abbrev.term Abbrev.quotation
  type matcher = string * pat * bool

  (* name and match whole assumption *)
  val a     : string -> pat -> matcher

  (* match whole assumption *)
  val ua    : pat -> matcher
  val au    : pat -> matcher

  (* name and match assumption subterm *)
  val ab    : string -> pat -> matcher
  val ba    : string -> pat -> matcher

  (* match assumption subterm *)
  val uab   : pat -> matcher
  val uba   : pat -> matcher
  val aub   : pat -> matcher
  val abu   : pat -> matcher
  val bau   : pat -> matcher
  val bua   : pat -> matcher

  (* match whole conclusion *)
  val c     : pat -> matcher

  (* match conclusion subterm *)
  val cb    : pat -> matcher
  val bc    : pat -> matcher

  (* match whole assumption or conclusion *)
  val ac    : pat -> matcher
  val ca    : pat -> matcher

  (* match assumption or conclusion subterm *)
  val acb   : pat -> matcher
  val abc   : pat -> matcher
  val bca   : pat -> matcher
  val cba   : pat -> matcher
  val cab   : pat -> matcher
  val bac   : pat -> matcher
end

signature match_goal =
sig

include Abbrev

type matcher = string * term quotation *  bool

(*
name of assumption     pattern          whole term?
string               * term quotation * bool

semantics of names:
(any normal string, e.g., "H") - must be an assumption
"_" -> must be assumption, but don't care about its name - can match other different or same
"H2" -> must be an assumption, must be different from "H"
"H" -> must be an assumption, and the same one as "H"
"?" -> must be the conclusion
"" -> match anything, don't care about name or previous matches
*)

(*
semantics of whole term boolean:
  - if true then the match must be of the whole assumption/conclusion
  - otherwise, match any subterm (i.e., like Coq's context patterns)
*)

(*
semantics of pattern variables:
  2 kinds of variable:
  - free variable in goal
  - unification variable
      - by convention, must end, and not start, with an underscore
  assume all free variables cannot be mistaken for unification variables
    (if attempting to bind a non-unification variable, the match will fail)
*)

(*
semantics of matcher list with a tactic (match_case):
Iterate over matchers, all must match:
1. Parse quotation in context of goal (and check no free vars ending with _)
2. Attempt to match the appropriate part of the goal with the pattern (keep track which match)
   - if failed, backtrack within current matcher;
   - if no assumptions match, backtrack to previous matcher
3. Go to the next matcher
4. When all matchers are done:
   - Introduce abbreviations for all unification variables
   - Try running the tactic
     - if it fails: undo abbreviations, backtrack
     - if it succeeds: undo abbreviations, done

semantics of (matcher list * thms_tactic) list:
Iterate over list, taking first thing that works.
*)

type mg_tactic = (string -> thm) * (string -> term) -> tactic

val match1_tac : matcher * mg_tactic -> tactic

val match_tac : matcher list * mg_tactic -> tactic

val match_all_tac : (matcher list * mg_tactic) list -> tactic

(* TODO: maybe these should be elsewhere *)
val kill_asm : thm -> tactic
val drule_thm : thm -> thm -> tactic
(* -- *)

structure mg : mg

end
