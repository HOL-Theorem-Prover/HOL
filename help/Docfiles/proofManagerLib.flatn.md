## `flatn`

``` hol4
proofManagerLib.flatn : int -> unit
```

------------------------------------------------------------------------

Flattens the tree structure of subgoals on the subgoal package goal
stack.

The function `flatn` is part of the subgoal package. For a general
description of the subgoal package, see `set_goal`.

The `flatn` function's basic step of operation is to take the the
current list of sub-goals and concatenate it with the previous list of
subgoals (excluding the first of that list, from which the current list
was obtained). The numeric argument passed to `flatn` specifies how many
times this operation is to be performed.

### Failure

Raises the `NO_PROOFS` exception if there is no current proof
manipulated by the subgoal package.

If `n` is too large, or negative, the result will be a flat list of all
subgoals.

To view, reorder, or attack simultaneously, current and previously
obtained subgoals.

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
[`proofManagerLib.p`](#proofManagerLib.p),
[`proofManagerLib.top_thm`](#proofManagerLib.top_thm),
[`proofManagerLib.top_goal`](#proofManagerLib.top_goal)
