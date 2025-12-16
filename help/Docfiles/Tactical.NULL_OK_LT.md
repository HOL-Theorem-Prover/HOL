## `NULL_OK_LT`

``` hol4
Tactical.NULL_OK_LT : list_tactic -> list_tactic
```

------------------------------------------------------------------------

Makes a list-tactic succeed with no effect when applied to the empty
goal list.

For any list-tactic `ltac`, the application `NULL_OK_LT ltac` gives a
new list-tactic which has the same effect as `ltac` when applied to a
non-empty goal list. Applied to the empty goal list it succeeds with no
effect.

### Failure

The application of `NULL_OK_LT` to a list-tactic `ltac` never fails. The
resulting list-tactic fails if applied to a non-empty goal list on which
`ltac` fails.

### See also

[`Tactical.ALL_LT`](#Tactical.ALL_LT),
[`Tactical.THENL`](#Tactical.THENL)
