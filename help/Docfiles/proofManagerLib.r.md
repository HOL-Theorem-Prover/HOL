## `r`

``` hol4
proofManagerLib.r : int -> unit
```

------------------------------------------------------------------------

Reorders the subgoals on top of the subgoal package goal stack.

The function `r` is part of the subgoal package. The name `rotate` may
also be used to access the same function. For a general description of
the subgoal package, see `set_goal`.

The `r` function's basic step of operation is to take the first element
of the current list of sub-goals and move it to the end of the same
list. The numeric argument passed to `r` specifies how many times this
operation is to be performed.

### Failure

Raises the `NO_PROOFS` exception if there is no current proof
manipulated by the subgoal package. Raises a `HOL_ERR` if the current
goal state only has one sub-goal, or if the argument passed to `r` is
negative.

Interactively attacking subgoals in a different order to that generated
by the subgoal package.

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
