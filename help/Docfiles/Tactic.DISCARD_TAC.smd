## `DISCARD_TAC`

``` hol4
Tactic.DISCARD_TAC : thm_tactic
```

------------------------------------------------------------------------

Discards a theorem already present in a goal's assumptions.

When applied to a theorem `A' |- s` and a goal, `DISCARD_TAC` checks
that `s` is simply `T` (true), or already exists (up to
alpha-conversion) in the assumption list of the goal. In either case,
the tactic has no effect. Otherwise, it fails.

``` hol4
    A ?- t
   ========  DISCARD_TAC (A' |- s)
    A ?- t
```

### Failure

Fails if the above conditions are not met, i.e. the theorem's conclusion
is not `T` or already in the assumption list (up to alpha-conversion).

### See also

[`Tactical.POP_ASSUM`](#Tactical.POP_ASSUM),
[`Tactical.POP_ASSUM_LIST`](#Tactical.POP_ASSUM_LIST)
