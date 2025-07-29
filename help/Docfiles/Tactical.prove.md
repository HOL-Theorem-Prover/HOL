## `prove`

``` hol4
Tactical.prove : term * tactic -> thm
```

------------------------------------------------------------------------

Attempts to prove a boolean term using the supplied tactic.

When applied to a term-tactic pair `(tm,tac)`, the function `prove`
attempts to prove the goal `?- tm`, that is, the term `tm` with no
assumptions, using the tactic `tac`. If `prove` succeeds, it returns the
corresponding theorem `A |- tm`, where the assumption list `A` may not
be empty if the tactic is invalid; `prove` has no inbuilt
validity-checking.

### Failure

Fails if the term is not of type `bool` (and so cannot possibly be the
conclusion of a theorem), or if the tactic cannot solve the goal.

### See also

[`Tactical.TAC_PROOF`](#Tactical.TAC_PROOF)
