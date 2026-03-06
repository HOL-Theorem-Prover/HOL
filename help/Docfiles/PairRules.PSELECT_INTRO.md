## `PSELECT_INTRO`

``` hol4
PairRules.PSELECT_INTRO : (thm -> thm)
```

------------------------------------------------------------------------

Introduces an epsilon term.

`PSELECT_INTRO` takes a theorem with an applicative conclusion, say
`P x`, and returns a theorem with the epsilon term `$@ P` in place of
the original operand `x`.

``` hol4
     A |- P x
   --------------  PSELECT_INTRO
    A |- P($@ P)
```

The returned theorem asserts that `$@ P` denotes some value at which `P`
holds.

### Failure

Fails if the conclusion of the theorem is not an application.

### Comments

This function is exactly the same as `SELECT_INTRO`, it is duplicated in
the pair library for completeness.

### See also

[`Drule.SELECT_INTRO`](#Drule.SELECT_INTRO),
[`PairRules.PEXISTS`](#PairRules.PEXISTS),
[`PairRules.PSELECT_CONV`](#PairRules.PSELECT_CONV),
[`PairRules.PSELECT_ELIM`](#PairRules.PSELECT_ELIM),
[`PairRules.PSELECT_RULE`](#PairRules.PSELECT_RULE)
