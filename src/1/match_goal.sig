signature match_goal =
sig

include Abbrev

datatype name =
    Assumption of string option
  | Conclusion
  | Anything

type pattern = term quotation
type matcher = name * pattern * bool (* whole term? *)

(*
semantics of names:
Assumption (SOME s)
  - must be an assumption
  - must be the same as any other assumptions called s
  - must be different from any other assumptions not called s
Assumption NONE
  - must be an assumption
Conclusion
  - must be the conclusion
Anything
  (no constraints)
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

val first_match_tac : (matcher list * mg_tactic) list -> tactic

(* TODO: maybe these should be elsewhere *)
val kill_asm : thm -> tactic
val drule_thm : thm -> thm -> tactic
(* -- *)

structure mg : sig
  (* name and match whole assumption *)
  val a     : string -> pattern -> matcher

  (* match whole assumption *)
  val ua    : pattern -> matcher
  val au    : pattern -> matcher

  (* name and match assumption subterm *)
  val ab    : string -> pattern -> matcher
  val ba    : string -> pattern -> matcher

  (* match assumption subterm *)
  val uab   : pattern -> matcher
  val uba   : pattern -> matcher
  val aub   : pattern -> matcher
  val abu   : pattern -> matcher
  val bau   : pattern -> matcher
  val bua   : pattern -> matcher

  (* match whole conclusion *)
  val c     : pattern -> matcher

  (* match conclusion subterm *)
  val cb    : pattern -> matcher
  val bc    : pattern -> matcher

  (* match whole assumption or conclusion *)
  val ac    : pattern -> matcher
  val ca    : pattern -> matcher

  (* match assumption or conclusion subterm *)
  val acb   : pattern -> matcher
  val abc   : pattern -> matcher
  val bca   : pattern -> matcher
  val cba   : pattern -> matcher
  val cab   : pattern -> matcher
  val bac   : pattern -> matcher
end

end
