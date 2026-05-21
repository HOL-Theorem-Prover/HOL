## `ORELSE_LT`

``` hol4
op Tactical.ORELSE_LT : list_tactic * list_tactic -> list_tactic
```

------------------------------------------------------------------------

Applies first list-tactic, and if it fails, applies the second instead.

If `ltac1` and `ltac2` are list-tactics, `ltac1 ORELSE_LT ltac2` is a
list-tactic which applies `ltac1` to a goal list, and if it fails,
applies `ltac2` to the goals.

### Failure

The application of `ORELSE_LT` to a pair of list-tactics never fails.
The resulting list-tactic fails if both `ltac1` and `ltac2` fail when
applied to the relevant goals.

### See also

[`Tactical.ORELSE`](#Tactical.ORELSE),
[`Tactical.THEN_LT`](#Tactical.THEN_LT)
