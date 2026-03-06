## `PEXISTENCE`

``` hol4
PairRules.PEXISTENCE : (thm -> thm)
```

------------------------------------------------------------------------

Deduces paired existence from paired unique existence.

When applied to a theorem with a paired unique-existentially quantified
conclusion, `EXISTENCE` returns the same theorem with normal paired
existential quantification over the same pair.

``` hol4
    A |- ?!p. t
   -------------  PEXISTENCE
    A |- ?p. t
```

### Failure

Fails unless the conclusion of the theorem is a paired
unique-existential quantification.

### See also

[`Conv.EXISTENCE`](#Conv.EXISTENCE),
[`PairRules.PEXISTS_UNIQUE_CONV`](#PairRules.PEXISTS_UNIQUE_CONV)
