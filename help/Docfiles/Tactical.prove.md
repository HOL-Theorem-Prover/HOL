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

By default this function calls `TAC_PROOF` (*q.v.*) with a wrapper that augments that underlying function’s error-reporting, but this call is made via a user-updatable reference. This means there are contexts in which this function may, for example, automatically assert all terms it is passed as theorems using `mk_thm`.

### Comments

To emulate interactive use and its variations, `prove` is appropriate; to get fixed behaviour, use `TAC_PROOF`.

### Failure

Fails if the term is not of type `bool` (and so cannot possibly be the
conclusion of a theorem), or if the tactic does not solve the goal.

### See also

[`Tactical.prove_goal`](#Tactical.prove_goal), [`Tactical.set_prover`](#Tactical.set_prover), [`Tactical.TAC_PROOF`](#Tactical.TAC_PROOF).
