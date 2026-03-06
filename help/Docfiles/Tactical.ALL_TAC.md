## `ALL_TAC`

``` hol4
Tactical.ALL_TAC : tactic
```

------------------------------------------------------------------------

Passes on a goal unchanged.

`ALL_TAC` applied to a goal `g` simply produces the subgoal list `[g]`.
It is the identity for the `THEN` tactical.

### Failure

Never fails.

### Example

The tactic

``` hol4
   INDUCT_THEN numTheory.INDUCTION THENL [ALL_TAC, tac]
```

applied to a goal `g`, applies `INDUCT_THEN numTheory.INDUCTION` to `g`
to give a basis and step subgoal; it then returns the basis unchanged,
along with the subgoals produced by applying `tac` to the step.

Used to write tacticals such as `REPEAT`. Also, it is often used as a
place-holder in building compound tactics using tacticals such as
`THENL`.

### See also

[`Prim_rec.INDUCT_THEN`](#Prim_rec.INDUCT_THEN),
[`Tactical.NO_TAC`](#Tactical.NO_TAC),
[`Tactical.REPEAT`](#Tactical.REPEAT),
[`Tactical.THENL`](#Tactical.THENL)
