## `forget_history`

``` hol4
proofManagerLib.forget_history : unit -> unit
```

------------------------------------------------------------------------

Clears the proof history.

The function `forget_history` is part of the subgoal package. A call to
`forget_history` clears the history of saved proof states. Subsequent
calls to `backup` or `restart` will behave as if the initial goal was
the state at the time of the call to `forget_history`. For a description
of the subgoal package, see `set_goal`.

### Failure

The function `forget_history` only fails if no goalstack is being
managed.

Hiding an automatic preprocessing phase of a proof before handing it to
the user.

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
