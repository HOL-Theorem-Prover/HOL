## `FILTER_PGEN_TAC`

``` hol4
PairRules.FILTER_PGEN_TAC : (term -> tactic)
```

------------------------------------------------------------------------

Strips off a paired universal quantifier, but fails for a given
quantified pair.

When applied to a term `q` and a goal `A ?- !p. t`, the tactic
`FILTER_PGEN_TAC` fails if the quantified pair `p` is the same as `p`,
but otherwise advances the goal in the same way as `PGEN_TAC`,
i.e. returns the goal `A ?- t[p'/p]` where `p'` is a variant of `p`
chosen to avoid clashing with any variables free in the goal's
assumption list. Normally `p'` is just `p`.

``` hol4
     A ?- !p. t
   ==============  FILTER_PGEN_TAC "q"
    A ?- t[p'/p]
```

### Failure

Fails if the goal's conclusion is not a paired universal quantifier or
the quantified pair is equal to the given term.

### See also

[`Tactic.FILTER_GEN_TAC`](#Tactic.FILTER_GEN_TAC),
[`PairRules.PGEN`](#PairRules.PGEN),
[`PairRules.PGEN_TAC`](#PairRules.PGEN_TAC),
[`PairRules.PGENL`](#PairRules.PGENL),
[`PairRules.PSPEC`](#PairRules.PSPEC),
[`PairRules.PSPECL`](#PairRules.PSPECL),
[`PairRules.PSPEC_ALL`](#PairRules.PSPEC_ALL),
[`PairRules.PSPEC_TAC`](#PairRules.PSPEC_TAC),
[`PairRules.PSTRIP_TAC`](#PairRules.PSTRIP_TAC)
