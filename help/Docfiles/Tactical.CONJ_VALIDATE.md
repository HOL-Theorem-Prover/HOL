## `CONJ_VALIDATE`

``` hol4
Tactical.CONJ_VALIDATE : tactic -> tactic
```

------------------------------------------------------------------------

Adds requirement to prove assumptions that would make a tactic invalid.

A call to `CONJ_VALIDATE tac g` behaves the same as `tac g` if this
tactic application is valid (meaning that when the tactic's validation
function is applied to the resulting sub-goals, the generated theorem
has no more assumptions than the original goal).

If the tactic's application is not valid because the resulting theorem
has the wrong conclusion, `CONJ_VALIDATE tac g` will fail. If the
resulting theorem has hypotheses not present in the goal state, then
these hypotheses are added to the new goals as new proof obligations.
The way in which this addition is done depends on how many subgoals
`tac` generated when applied to `g`.

If `tac` completely solves `g` (though in an invalid way), the excess
hypotheses `h1...hn` are bundled into a big conjunction and this becomes
the one remaining goal. If `tac g` results in more than one new goal,
then `CONJ_VALIDATE tac g` will produce one extra goal, consisting of a
conjunction of hypotheses, as above. Finally, if `tac g` produces
exactly one new goal to prove, and if the new goal's assumptions are a
subset of the original goal's, `CONJ_VALIDATE tac g` will do the same,
but with the conjunction of extra hypotheses to prove conjoined to that
one goal's conclusion. If there is one new goal, but its assumptions are
not a subset, then a separate sub-goal is generated.

### Failure

A call `CONJ_VALIDATE tac g` will fail if `tac g` fails, or if `tac g`'s
validation function produces a theorem whose conclusion is not the same
as `g`'s conclusion.

### Comments

`CONJ_VALIDATE` performs the same role as `VALIDATE` but tries to
preserve the property of having a single successor goal in its argument
tactics; when it does generate extra sub-goals, it also generates only
one such.

Because `CONJ_VALIDATE` prefers to generate just one sub-goal, the
result may be a state where one ends up having to prove a hypothesis in
a weaker context (with fewer assumptions) to hand than if `VALIDATE` had
been used.

### See also

[`Tactical.VALIDATE`](#Tactical.VALIDATE)
