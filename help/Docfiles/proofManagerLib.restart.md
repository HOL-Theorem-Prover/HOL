## `restart`

``` hol4
proofManagerLib.restart : unit -> proof
```

------------------------------------------------------------------------

Returns the proof state to the initial goal.

The function `restart` is part of the subgoal package. A call to
`restart` clears the proof history and returns to the initial goal.
After a call to `restart`, the proof state is the same as it was after
the inital call to `set_goal` (or `g`). For a description of the subgoal
package, see `set_goal`.

### Failure

The function `restart` only fails if no goalstack is being managed.

Restarting an interactive proof.

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
