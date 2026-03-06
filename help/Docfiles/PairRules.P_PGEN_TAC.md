## `P_PGEN_TAC`

``` hol4
PairRules.P_PGEN_TAC : (term -> tactic)
```

------------------------------------------------------------------------

Specializes a goal with the given paired structure of variables.

When applied to a paired structure of variables `p'`, and a goal
`A ?- !p. t`, the tactic `P_PGEN_TAC` returns the goal `A ?- t[p'/p]`.

``` hol4
     A ?- !p. t
   ==============  P_PGEN_TAC "p'"
    A ?- t[p'/x]
```

### Failure

Fails unless the goal's conclusion is a paired universal quantification
and the term a paired structure of variables of the appropriate type. It
also fails if any of the variables of the supplied structure occurs free
in either the assumptions or (initial) conclusion of the goal.

### See also

[`Tactic.X_GEN_TAC`](#Tactic.X_GEN_TAC),
[`PairRules.FILTER_PGEN_TAC`](#PairRules.FILTER_PGEN_TAC),
[`PairRules.PGEN`](#PairRules.PGEN),
[`PairRules.PGENL`](#PairRules.PGENL),
[`PairRules.PSPEC`](#PairRules.PSPEC),
[`PairRules.PSPECL`](#PairRules.PSPECL),
[`PairRules.PSPEC_ALL`](#PairRules.PSPEC_ALL),
[`PairRules.PSPEC_TAC`](#PairRules.PSPEC_TAC)
