signature goalFrag =
sig
include Abbrev

type goalstate
type frag_tactic = goalstate -> goalstate

val new_goal_list : goal list -> goalstate
val new_goal      : goal -> goalstate
val finish_list   : goalstate -> thm list
val finish        : goalstate -> thm
val top_goal      : goalstate -> goal
val top_goals     : goalstate -> goal list

val expand          : tactic -> frag_tactic
val expandf         : tactic -> frag_tactic
val expand_list     : list_tactic -> frag_tactic
val expand_listf    : list_tactic -> frag_tactic
val open_paren      : frag_tactic
val open_first      : frag_tactic
val open_head_goal  : frag_tactic
val open_last_goal  : frag_tactic
val open_nth_goal   : int -> frag_tactic
val open_null_ok    : frag_tactic
val open_repeat     : frag_tactic
val open_select_lt  : frag_tactic
val open_split_lt   : int -> frag_tactic
val open_tacs_to_lt : frag_tactic
val open_then1      : frag_tactic
val open_first_lt   : frag_tactic
val next_select_lt  : frag_tactic
val next_first      : frag_tactic
val next_split_lt   : frag_tactic
val next_tacs_to_lt : frag_tactic
val close_first     : frag_tactic
val close_paren     : frag_tactic
val close_repeat    : frag_tactic
val close_first_lt  : frag_tactic

val pp_goalstate    : goalstate Parse.pprinter

end

(* ----------------------------------------------------------------------
    Overview
   ----------------------------------------------------------------------

    goalFrag implements an interactive proof manager that lets the user
    build up tactic combinator expressions piecewise.  Each user-level
    move either applies an ordinary tactic at the current focus, or
    "opens"/"closes" a fragment representing one of the standard tactic
    combinators (THEN1, FIRST/ORELSE, REPEAT, NTH_GOAL, FIRST_LT, etc.).

    Internally a goalstate is a pair (n, t) where t is a tree of partial
    combinator applications (a goaltree, defined in goalFrag.sml) and n
    is the current open-paren depth.  The leaves of the tree are
    Base (gs, v) nodes carrying actual subgoals together with the
    list_validation that turns proven theorems for those goals back into
    theorems for their parent.  Other constructors record combinators
    that are currently open:

      - Parallel : a [t1, t2, ...]-style block, with one subtree per
        subgoal at the time the paren was opened.
      - Stashed  : goals parked aside while the user works on something
        else; the stash_kind says how to reassemble on close (Then1,
        TacsToLT, NthGoal).
      - Try      : an in-progress ORELSE/FIRST attempt, holding the
        running branch and the original goals to fall back to.  Failure
        is captured as a Failed exn in a 'a handled wrapper rather than
        propagated, so combinators can recover.
      - Repeat   : an in-progress REPEAT, with a log closure that knows
        how to relaunch the body on residual subgoals.
      - Done     : a branch the user has signalled is finished (used to
        terminate Try/Repeat without yet collapsing the combinator).

    Navigation is via apply / apply1 / applyN, which descend through the
    "active" child of each combinator (the tail of a Stashed, the
    Running side of a Try/Repeat, every child of a Parallel) to reach
    the Base that an expand should mutate, or to find the combinator
    layer that a next_/close_ should rewrite.

    The tactic-application primitives are:

      - expand / expandf      : apply a tactic at the focused Base.
      - expand_list / expand_listf : apply a list_tactic.

    The non-f forms wrap with Tactical.VALID / VALID_LT.

    The combinator surface mirrors familiar tacticals.  Each open_X
    builds the appropriate node and bumps n; next_X advances state
    inside an open combinator; close_X collapses it back to a Base and
    decrements n:

      - open_paren / close_paren : ( ... ) over a list of subgoals.
      - open_then1 / close_paren : t1 >- t2 (THEN1).  Close raises if
        the first subgoal isn't fully discharged.
      - open_first / next_first / close_first : ORELSE / FIRST.
      - open_repeat / close_repeat : REPEAT.
      - open_tacs_to_lt / next_tacs_to_lt / close_paren : a sequence of
        tactics, one per subgoal, presented as a list_tactic.  Close
        raises on a length mismatch.
      - open_nth_goal i / open_head_goal / open_last_goal / close_paren
        : focus a single subgoal, splicing the rest back on close.
      - open_split_lt i / next_split_lt / close_paren : split the goal
        list at i and work on each half in turn.
      - open_select_lt / next_select_lt / close_paren : SELECT_LT --
        attempt a tactic on every subgoal in parallel, partitioning into
        successes and failures.
      - open_first_lt / close_first_lt : FIRST_LT -- apply to the first
        subgoal where the tactic succeeds, leaving the rest unchanged.
      - open_null_ok / close_paren : like open_paren but tolerates an
        empty current goal list.

    The boundary operations are:

      - new_goal / new_goal_list : start from a goal (or list).
      - finish / finish_list     : close all open parens, then extract
        the proven theorem(s); raises if subgoals remain.
      - top_goal / top_goals     : harvest the user-visible "current"
        subgoals from the active leaves of the tree.
      - pp_goalstate             : pretty-printer mirroring goalStack's
        display logic, including subgoal eliding and the size-based
        raw_terminal fallback.

    The overall design is essentially a zipper-like representation of a
    partially-elaborated tactic expression, with all validation plumbing
    carried inside the tree so that finish can reconstruct a real
    theorem from the user's stepwise edits.
   ---------------------------------------------------------------------- *)
