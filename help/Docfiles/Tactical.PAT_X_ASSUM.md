## `PAT_X_ASSUM`

``` hol4
Tactical.PAT_X_ASSUM : term -> thm_tactic -> tactic
```

------------------------------------------------------------------------

Finds the first assumption that matches the term argument, applies the
theorem tactic to it, and removes this assumption.

The tactic

``` hol4
   PAT_X_ASSUM tm ttac ([A1, ..., An], g)
```

finds the first `Ai` which matches `tm` using higher-order pattern
matching in the sense of `ho_match_term`. Free variables in the pattern
that are also free in the assumptions or the goal must not be bound by
the match. In effect, these variables are being treated as local
constants.

### Failure

Fails if the term doesn't match any of the assumptions, or if the
theorem-tactic fails when applied to the first assumption that does
match the term.

### See also

[`Tactical.PAT_ASSUM`](#Tactical.PAT_ASSUM),
[`Tactical.ASSUM_LIST`](#Tactical.ASSUM_LIST),
[`Tactical.EVERY`](#Tactical.EVERY),
[`Tactical.EVERY_ASSUM`](#Tactical.EVERY_ASSUM),
[`Tactical.FIRST`](#Tactical.FIRST),
[`Tactical.MAP_EVERY`](#Tactical.MAP_EVERY),
[`Tactical.MAP_FIRST`](#Tactical.MAP_FIRST),
[`Thm_cont.UNDISCH_THEN`](#Thm_cont.UNDISCH_THEN),
[`Term.match_term`](#Term.match_term)
