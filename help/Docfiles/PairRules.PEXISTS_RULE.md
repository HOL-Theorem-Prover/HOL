## `PEXISTS_RULE`

``` hol4
PairRules.PEXISTS_RULE : (thm -> thm)
```

------------------------------------------------------------------------

Introduces a paired existential quantification in place of a paired
choice.

The inference rule `PEXISTS_RULE` expects a theorem asserting that
`(@p. t)` denotes a pair for which `t` holds. The equivalent assertion
that there exists a `p` for which `t` holds is returned.

``` hol4
    A |- t[(@p. t)/p]
   ------------------  PEXISTS_RULE
       A |- ?p. t
```

### Failure

Fails if applied to a theorem the conclusion of which is not of the form
`(t[(@p.t)/p])`.

### See also

[`PairRules.PEXISTS_CONV`](#PairRules.PEXISTS_CONV),
[`PairRules.PSELECT_RULE`](#PairRules.PSELECT_RULE),
[`PairRules.PSELECT_CONV`](#PairRules.PSELECT_CONV),
[`PairRules.PSELECT_INTRO`](#PairRules.PSELECT_INTRO),
[`PairRules.PSELECT_ELIM`](#PairRules.PSELECT_ELIM)
