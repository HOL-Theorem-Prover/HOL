## `PSPEC_PAIR`

``` hol4
PairRules.PSPEC_PAIR : thm -> term * thm
```

------------------------------------------------------------------------

Specializes the conclusion of a theorem, returning the chosen variant.

When applied to a theorem `A |- !p. t`, the inference rule `PSPEC_PAIR`
returns the term `q'` and the theorem `A |- t[q'/p]`, where `q'` is a
variant of `p` chosen to avoid free variable capture.

``` hol4
     A |- !p. t
   --------------  PSPEC_PAIR
    A |- t[q'/q]
```

### Failure

Fails unless the theorem's conclusion is a paired universal
quantification.

### Comments

This rule is very similar to plain `PSPEC`, except that it returns the
variant chosen, which may be useful information under some
circumstances.

### See also

[`Drule.SPEC_VAR`](#Drule.SPEC_VAR),
[`PairRules.PGEN`](#PairRules.PGEN),
[`PairRules.PGENL`](#PairRules.PGENL),
[`PairRules.PGEN_TAC`](#PairRules.PGEN_TAC),
[`PairRules.PSPEC`](#PairRules.PSPEC),
[`PairRules.PSPECL`](#PairRules.PSPECL),
[`PairRules.PSPEC_ALL`](#PairRules.PSPEC_ALL)
