## `PSELECT_RULE`

``` hol4
PairRules.PSELECT_RULE : (thm -> thm)
```

------------------------------------------------------------------------

Introduces a paired epsilon term in place of a paired existential
quantifier.

The inference rule `PSELECT_RULE` expects a theorem asserting the
existence of a pair `p` such that `t` holds. The equivalent assertion
that the epsilon term `@p.t` denotes a pair `p` for which `t` holds is
returned as a theorem.

``` hol4
       A |- ?p. t
   ------------------  PSELECT_RULE
    A |- t[(@p.t)/p]
```

### Failure

Fails if applied to a theorem the conclusion of which is not a paired
existential quantifier.

### See also

[`Drule.SELECT_RULE`](#Drule.SELECT_RULE),
[`PairRules.PCHOOSE`](#PairRules.PCHOOSE),
[`PairRules.PSELECT_CONV`](#PairRules.PSELECT_CONV),
[`PairRules.PEXISTS_CONV`](#PairRules.PEXISTS_CONV),
[`PairRules.PSELECT_ELIM`](#PairRules.PSELECT_ELIM),
[`PairRules.PSELECT_INTRO`](#PairRules.PSELECT_INTRO)
