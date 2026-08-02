(* Given the enclosing Theorem's statement quote, parse it against the
   live HOL Context and return it as the initial goal (step 0, no
   assumptions).  Loaded AFTER HOL is initialised so Parse.Term is
   available. *)

val () = LSPExtension.goalStateAtPos :=
  (fn (_: LSPExtension.hover_context,
       {name, quote, ...}: LSPExtension.theorem_context) =>
    case Lib.total Parse.Term [QUOTE quote] of
      NONE => NONE
    | SOME tm =>
      SOME {theorem = name, step = 0,
            goals = [{asms = [], goal = Parse.term_to_string tm}]})
