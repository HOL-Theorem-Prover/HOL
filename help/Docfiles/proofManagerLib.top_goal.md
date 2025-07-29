## `top_goal`

``` hol4
proofManagerLib.top_goal : unit -> goal
```

------------------------------------------------------------------------

Returns the current goal of the subgoal package.

The function `top_goal` is part of the subgoal package. It returns the
top goal of the goal stack in the current proof state. For a description
of the subgoal package, see `set_goal`.

### Failure

A call to `top_goal` will fail if there are no unproven goals. This
could be because no goal has been set using `set_goal` or because the
last goal set has been completely proved.

Examining the proof state after a proof fails.

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
