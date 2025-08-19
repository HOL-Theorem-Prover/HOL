## `FIRST_ASSUM`

``` hol4
Tactical.FIRST_ASSUM : (thm_tactic -> tactic)
```

------------------------------------------------------------------------

Maps a theorem-tactic over the assumptions, applying first successful
tactic.

The tactic

``` hol4
   FIRST_ASSUM ttac ([A1; ...; An], g)
```

has the effect of applying the first tactic which can be produced by
`ttac` from the `ASSUME`d assumptions `(A1 |- A1)`, ..., `(An |- An)`
and which succeeds when applied to the goal. Failures of `ttac` to
produce a tactic are ignored.

### Failure

Fails if `ttac (Ai |- Ai)` fails for every assumption `Ai`, or if the
assumption list is empty, or if all the tactics produced by `ttac` fail
when applied to the goal.

### Example

The tactic

``` hol4
   FIRST_ASSUM (fn asm => CONTR_TAC asm  ORELSE  ACCEPT_TAC asm)
```

searches the assumptions for either a contradiction or the desired
conclusion. The tactic

``` hol4
   FIRST_ASSUM MATCH_MP_TAC
```

searches the assumption list for an implication whose conclusion matches
the goal, reducing the goal to the antecedent of the corresponding
instance of this implication.

### Comments

By default, the assumption list is printed in reverse order, with the
head of the list printed last. To process the assumption list in the
opposite order, use `LAST_ASSUM`

### See also

[`Tactical.FIRST_X_ASSUM`](#Tactical.FIRST_X_ASSUM),
[`Tactical.LAST_ASSUM`](#Tactical.LAST_ASSUM),
[`Tactical.ASSUM_LIST`](#Tactical.ASSUM_LIST),
[`Tactical.EVERY`](#Tactical.EVERY),
[`Tactical.EVERY_ASSUM`](#Tactical.EVERY_ASSUM),
[`Tactical.FIRST`](#Tactical.FIRST),
[`Tactical.MAP_EVERY`](#Tactical.MAP_EVERY),
[`Tactical.MAP_FIRST`](#Tactical.MAP_FIRST)
