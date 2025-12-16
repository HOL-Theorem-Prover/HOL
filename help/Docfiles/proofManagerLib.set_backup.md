## `set_backup`

``` hol4
proofManagerLib.set_backup : int -> unit
```

------------------------------------------------------------------------

Limits the number of proof states saved on the subgoal package backup
list.

The assignable variable `set_backup` is initially set to 12. Its value
is one less than the maximum number of proof states that may be saved on
the backup list. Adding a new proof state (by, for example, a call to
`expand`) after the maximum is reached causes the earliest proof state
on the list to be discarded. For a description of the subgoal package,
see `set_goal`.

### Example

``` hol4
- set_backup 0;
()  unit

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

     :proof

- e (REWRITE_TAC[listTheory.HD]);
OK..

Goal proved.
|- HD [1; 2; 3] = 1

Remaining subgoals:
> val it =
    TL [1; 2; 3] = [2; 3]

     : proof

- b();
> val it =
    TL [1; 2; 3] = [2; 3]


    HD [1; 2; 3] = 1

     : proof

- b();
! Uncaught exception:
! CANT_BACKUP_ANYMORE
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
