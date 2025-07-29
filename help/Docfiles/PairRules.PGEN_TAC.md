## `PGEN_TAC`

``` hol4
PairRules.PGEN_TAC : tactic
```

------------------------------------------------------------------------

Strips the outermost paired universal quantifier from the conclusion of
a goal.

When applied to a goal `A ?- !p. t`, the tactic `PGEN_TAC` reduces it to
`A ?- t[p'/p]` where `p'` is a variant of the paired variable structure
`p` chosen to avoid clashing with any variables free in the goal's
assumption list. Normally `p'` is just `p`.

``` hol4
     A ?- !p. t
   ==============  PGEN_TAC
    A ?- t[p'/p]
```

### Failure

Fails unless the goal's conclusion is a paired universally
quantification.

### See also

[`Tactic.GEN_TAC`](#Tactic.GEN_TAC),
[`PairRules.FILTER_PGEN_TAC`](#PairRules.FILTER_PGEN_TAC),
[`PairRules.PGEN`](#PairRules.PGEN),
[`PairRules.PGENL`](#PairRules.PGENL),
[`PairRules.PSPEC`](#PairRules.PSPEC),
[`PairRules.PSPECL`](#PairRules.PSPECL),
[`PairRules.PSPEC_ALL`](#PairRules.PSPEC_ALL),
[`PairRules.PSPEC_TAC`](#PairRules.PSPEC_TAC),
[`PairRules.PSTRIP_TAC`](#PairRules.PSTRIP_TAC),
[`PairRules.P_PGEN_TAC`](#PairRules.P_PGEN_TAC)
