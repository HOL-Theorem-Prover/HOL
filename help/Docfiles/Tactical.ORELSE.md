## `ORELSE`

``` hol4
op Tactical.ORELSE : tactic * tactic -> tactic
```

------------------------------------------------------------------------

Applies first tactic, and if it fails, applies the second instead.

If `T1` and `T2` are tactics, `T1 ORELSE T2` is a tactic which applies
`T1` to a goal, and if it fails, applies `T2` to the goal instead.

### Failure

The application of `ORELSE` to a pair of tactics never fails. The
resulting tactic fails if both `T1` and `T2` fail when applied to the
relevant goal.

### See also

[`Tactical.EVERY`](#Tactical.EVERY),
[`Tactical.FIRST`](#Tactical.FIRST), [`Tactical.IF`](#Tactical.IF),
[`Tactical.THEN`](#Tactical.THEN)
