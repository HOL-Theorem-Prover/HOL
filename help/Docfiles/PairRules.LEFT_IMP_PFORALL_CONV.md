## `LEFT_IMP_PFORALL_CONV`

``` hol4
PairRules.LEFT_IMP_PFORALL_CONV : conv
```

------------------------------------------------------------------------

Moves a paired universal quantification of the antecedent outwards
through an implication.

When applied to a term of the form `(!p. t) ==> u`, the conversion
`LEFT_IMP_PFORALL_CONV` returns the theorem:

``` hol4
   |- (!p. t) ==> u = (?p'. t[p'/p] ==> u)
```

where `p'` is a primed variant of the pair `p` that does not contain any
variables that appear free in the input term.

### Failure

Fails if applied to a term not of the form `(!p. t) ==> u`.

### See also

[`Conv.LEFT_IMP_FORALL_CONV`](#Conv.LEFT_IMP_FORALL_CONV),
[`PairRules.PEXISTS_IMP_CONV`](#PairRules.PEXISTS_IMP_CONV),
[`PairRules.RIGHT_IMP_PFORALL_CONV`](#PairRules.RIGHT_IMP_PFORALL_CONV)
