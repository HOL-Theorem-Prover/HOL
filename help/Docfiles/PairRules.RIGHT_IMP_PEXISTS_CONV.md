## `RIGHT_IMP_PEXISTS_CONV`

``` hol4
PairRules.RIGHT_IMP_PEXISTS_CONV : conv
```

------------------------------------------------------------------------

Moves a paired existential quantification of the consequent outwards
through an implication.

When applied to a term of the form `t ==> (?p. u)`,
`RIGHT_IMP_PEXISTS_CONV` returns the theorem:

``` hol4
   |- t ==> (?p. u) = (?p'. t ==> (u[p'/p]))
```

where `p'` is a primed variant of the pair `p` that does not contain any
variables that appear free in the input term.

### Failure

Fails if applied to a term not of the form `t ==> (?p. u)`.

### See also

[`Conv.RIGHT_IMP_EXISTS_CONV`](#Conv.RIGHT_IMP_EXISTS_CONV),
[`PairRules.PEXISTS_IMP_CONV`](#PairRules.PEXISTS_IMP_CONV),
[`PairRules.LEFT_IMP_PFORALL_CONV`](#PairRules.LEFT_IMP_PFORALL_CONV)
