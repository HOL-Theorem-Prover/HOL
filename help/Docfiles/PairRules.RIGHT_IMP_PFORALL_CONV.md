## `RIGHT_IMP_PFORALL_CONV`

``` hol4
PairRules.RIGHT_IMP_PFORALL_CONV : conv
```

------------------------------------------------------------------------

Moves a paired universal quantification of the consequent outwards
through an implication.

When applied to a term of the form `t ==> (!p. u)`, the conversion
`RIGHT_IMP_FORALL_CONV` returns the theorem:

``` hol4
   |- t ==> (!p. u) = (!p'. t ==> (u[p'/p]))
```

where `p'` is a primed variant of the pair `p` that does not contain any
variables that appear free in the input term.

### Failure

Fails if applied to a term not of the form `t ==> (!p. u)`.

### See also

[`Conv.RIGHT_IMP_FORALL_CONV`](#Conv.RIGHT_IMP_FORALL_CONV),
[`PairRules.PFORALL_IMP_CONV`](#PairRules.PFORALL_IMP_CONV),
[`PairRules.LEFT_IMP_PEXISTS_CONV`](#PairRules.LEFT_IMP_PEXISTS_CONV)
