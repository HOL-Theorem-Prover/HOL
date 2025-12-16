## `ANTE_CONJ_CONV`

``` hol4
Conv.ANTE_CONJ_CONV : conv
```

------------------------------------------------------------------------

Eliminates a conjunctive antecedent in favour of implication.

When applied to a term of the form `(t1 /\ t2) ==> t`, the conversion
`ANTE_CONJ_CONV` returns the theorem:

``` hol4
   |- (t1 /\ t2 ==> t) = (t1 ==> t2 ==> t)
```

### Failure

Fails if applied to a term not of the form `"(t1 /\ t2) ==> t"`.

Somewhat ad-hoc, but can be used (with `CONV_TAC`) to transform a goal
of the form `?- (P /\ Q) ==> R` into the subgoal `?- P ==> (Q ==> R)`,
so that only the antecedent `P` is moved into the assumptions by
`DISCH_TAC`.

### See also

[`Tactic.CONV_TAC`](#Tactic.CONV_TAC),
[`Tactic.DISCH_TAC`](#Tactic.DISCH_TAC)
