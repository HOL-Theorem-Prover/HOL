## `AND_PEXISTS_CONV`

``` hol4
PairRules.AND_PEXISTS_CONV : conv
```

------------------------------------------------------------------------

Moves a paired existential quantification outwards through a
conjunction.

When applied to a term of the form `(?p. t) /\ (?p. u)`, where no
variables in `p` are free in either `t` or `u`, `AND_PEXISTS_CONV`
returns the theorem:

``` hol4
   |- (?p. t) /\ (?p. u) = (?p. t /\ u)
```

### Failure

`AND_PEXISTS_CONV` fails if it is applied to a term not of the form
`(?p. t) /\ (?p. u)`, or if it is applied to a term `(?p. t) /\ (?p. u)`
in which variables from `p` are free in either `t` or `u`.

### See also

[`Conv.AND_EXISTS_CONV`](#Conv.AND_EXISTS_CONV),
[`PairRules.PEXISTS_AND_CONV`](#PairRules.PEXISTS_AND_CONV),
[`PairRules.LEFT_AND_PEXISTS_CONV`](#PairRules.LEFT_AND_PEXISTS_CONV),
[`PairRules.RIGHT_AND_PEXISTS_CONV`](#PairRules.RIGHT_AND_PEXISTS_CONV)
