## `g`

``` hol4
proofManagerLib.g : term quotation -> proofs
```

------------------------------------------------------------------------

Initializes the subgoal package with a new goal which has no
assumptions.

The call

``` hol4
   g `tm`
```

is equivalent to

``` hol4
   set_goal([],Term`tm`)
```

and clearly more convenient if a goal has no assumptions. For a
description of the subgoal package, see `set_goal`.

### Failure

Fails unless the argument term has type `bool`.

### Example

``` hol4
- g `(HD[1;2;3] = 1) /\ (TL[1;2;3] = [2;3])`;
> val it =
    Proof manager status: 1 proof.
    1. Incomplete:
         Initial goal:
         (HD [1; 2; 3] = 1) /\ (TL [1; 2; 3] = [2; 3])



    : GoalstackPure.proofs
```

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
