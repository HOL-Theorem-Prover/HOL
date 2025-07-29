## `redo`

``` hol4
proofManagerLib.redo : unit -> proof
```

------------------------------------------------------------------------

Restores the proof state, redoing the effects of a previous expansion.

The function `redo` is part of the subgoal package. It may be
abbreviated by the function `rd`. It undoes the action of `backup`,
returning to a state after an undone state change (caused by calls to
`expand`, `rotate` and similar functions). The function that caused the
original state change is not re-run; only the final state is restored.
Any regular state change will cause the redo stack to be discarded.

### Failure

The function `redo` will fail if the redo list is empty.

### Example

``` hol4
- g `(HD[1;2;3] = 1) /\ (TL[1;2;3] = [2;3])`;
> val it =
    Proof manager status: 1 proof.
    1. Incomplete:
         Initial goal:
         (HD [1; 2; 3] = 1) /\ (TL [1; 2; 3] = [2; 3])

     : proofs

- e CONJ_TAC;
OK..
2 subgoals:
> val it =
    TL [1; 2; 3] = [2; 3]


    HD [1; 2; 3] = 1

2 subgoals
     : proof

- backup();
> val it =
    Initial goal:

    (HD [1; 2; 3] = 1) /\ (TL [1; 2; 3] = [2; 3])

     : proof

- redo();
> val it =
    TL [1; 2; 3] = [2; 3]


    HD [1; 2; 3] = 1

2 subgoals
     : proof
```

Back tracking in a goal-directed proof to undo errors or try different
tactics.

### See also

[`proofManagerLib.set_goal`](#proofManagerLib.set_goal),
[`proofManagerLib.restart`](#proofManagerLib.restart),
[`proofManagerLib.b`](#proofManagerLib.b),
[`proofManagerLib.backup`](#proofManagerLib.backup),
[`proofManagerLib.rd`](#proofManagerLib.rd),
[`proofManagerLib.redo`](#proofManagerLib.redo),
[`proofManagerLib.restore`](#proofManagerLib.restore),
[`proofManagerLib.save`](#proofManagerLib.save),
[`proofManagerLib.set_backup`](#proofManagerLib.set_backup),
[`proofManagerLib.expand`](#proofManagerLib.expand),
[`proofManagerLib.expandf`](#proofManagerLib.expandf),
[`proofManagerLib.p`](#proofManagerLib.p),
[`proofManagerLib.top_thm`](#proofManagerLib.top_thm),
[`proofManagerLib.top_goal`](#proofManagerLib.top_goal)
