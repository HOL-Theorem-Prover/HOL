## `set_goal`

``` hol4
proofManagerLib.set_goal : term list * term -> unit
```

------------------------------------------------------------------------

Initializes the subgoal package with a new goal.

The function `set_goal` initializes the subgoal management package. A
proof state of the package consists of either a goal stack and a
justification stack if a proof is in progress, or a theorem if a proof
has just been completed. `set_goal` sets a new proof state consisting of
an empty justification stack and a goal stack with the given goal as its
sole goal. The goal is printed.

### Failure

Fails unless all terms in the goal are of type `bool`.

### Example

``` hol4
- set_goal([], Term `(HD[1;2;3] = 1) /\ (TL[1;2;3] = [2;3])`);
> val it =
    Proof manager status: 1 proof.
    1. Incomplete:
         Initial goal:
         (HD [1; 2; 3] = 1) /\ (TL [1; 2; 3] = [2; 3])

     : proofs
```

Starting an interactive proof session with the subgoal package.

The subgoal package implements a simple framework for interactive
goal-directed proof. When conducting a proof that involves many subgoals
and tactics, the user must keep track of all the justifications and
compose them in the correct order. While this is feasible even in large
proofs, it is tedious. The subgoal package provides a way of building
and traversing the tree of subgoals top-down, stacking the
justifications and applying them properly.

The package maintains a proof state consisting of either a goal stack of
outstanding goals and a justification stack, or a theorem. Tactics are
used to expand the current goal (the one on the top of the goal stack)
into subgoals and justifications. These are pushed onto the goal stack
and justification stack, respectively, to form a new proof state.
Several preceding proof states are saved and can be returned to if a
mistake is made in the proof. The goal stack is divided into levels, a
new level being created each time a tactic is successfully applied to
give new subgoals. Alternatively a list-tactic can process the entire
list of goals of the current level to change that level (rather than
creating a new level). The subgoals of the current level may be
considered in any order. Levels of the goal stack may be collapsed so
that subgoals of a previous level appear as part of of the current
level.

If a tactic solves the current goal (returns an empty subgoal list),
then its justification is used to prove a corresponding theorem. This
theorem is then incorporated into the justification of the parent goal.
If the subgoal was the last subgoal of the level, the level is removed
and the parent goal is proved using its (new) justification. This
process is repeated until a level with unproven subgoals is reached. The
next goal on the goal stack then becomes the current goal. If all the
subgoals are proved, the resulting proof state consists of the theorem
proved by the justifications. This theorem may be accessed and saved.

### See also

[`proofManagerLib.set_goal`](#proofManagerLib.set_goal),
[`proofManagerLib.restart`](#proofManagerLib.restart),
[`proofManagerLib.backup`](#proofManagerLib.backup),
[`proofManagerLib.redo`](#proofManagerLib.redo),
[`proofManagerLib.restore`](#proofManagerLib.restore),
[`proofManagerLib.save`](#proofManagerLib.save),
[`proofManagerLib.set_backup`](#proofManagerLib.set_backup),
[`proofManagerLib.expand`](#proofManagerLib.expand),
[`proofManagerLib.expandf`](#proofManagerLib.expandf),
[`proofManagerLib.expand_list`](#proofManagerLib.expand_list),
[`proofManagerLib.flatn`](#proofManagerLib.flatn),
[`proofManagerLib.p`](#proofManagerLib.p),
[`proofManagerLib.top_thm`](#proofManagerLib.top_thm),
[`proofManagerLib.top_goal`](#proofManagerLib.top_goal)
