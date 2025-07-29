## `GEN_VALIDATE`

``` hol4
Tactical.GEN_VALIDATE : bool -> tactic -> tactic
```

------------------------------------------------------------------------

Where a tactic requires assumptions to be in the goal, add those
assumptions as new subgoals.

See `VALIDATE`, which is implemented as `GEN_VALIDATE true`.

Suppose `tac` applied to the goal `(asl,g)` produces a justification
that creates a theorem `A |- g'`. Then `GEN_VALIDATE false` adds new
subgoals for members of `A`, regardless of whether they are present in
`asl`.

### Failure

Fails by design if `tac`, when applied to a goal, produces a proof which
is invalid on account of proving a theorem whose conclusion differs from
that of the goal.

Also fails if `tac` fails when applied to the given goal.

### Example

For example, where theorem `uthr'` is `[p', q] |- r`

``` hol4
1 subgoal:
val it =

r
------------------------------------
  0.  p
  1.  q

> e (VALIDATE (ACCEPT_TAC uthr')) ;
OK..
1 subgoal:
val it =

p'
------------------------------------
  p
:
   proof
```

but, instead of that,

``` hol4
> e (GEN_VALIDATE false (ACCEPT_TAC uthr')) ;
OK..
2 subgoals:
val it =

q
------------------------------------
  0.  p
  1.  q


p'
------------------------------------
  0.  p
  1.  q
```

Use `GEN_VALIDATE false` rather than `VALIDATE` when programming
compound tactics if you want to know what the resulting subgoals will
be, regardless of what the assumptions of the goal are.

### See also

[`Tactical.VALID`](#Tactical.VALID),
[`Tactical.VALIDATE`](#Tactical.VALIDATE),
[`Tactical.ADD_SGS_TAC`](#Tactical.ADD_SGS_TAC)
