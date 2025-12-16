## `PART_PMATCH`

``` hol4
PairRules.PART_PMATCH : ((term -> term) -> thm -> term -> thm)
```

------------------------------------------------------------------------

Instantiates a theorem by matching part of it to a term.

When applied to a 'selector' function of type `term -> term`, a theorem
and a term:

``` hol4
   PART_MATCH fn (A |- !p1...pn. t) tm
```

the function `PART_PMATCH` applies `fn` to `t'` (the result of
specializing universally quantified pairs in the conclusion of the
theorem), and attempts to match the resulting term to the argument term
`tm`. If it succeeds, the appropriately instantiated version of the
theorem is returned.

### Failure

Fails if the selector function `fn` fails when applied to the
instantiated theorem, or if the match fails with the term it has
provided.

### See also

[`Drule.PART_MATCH`](#Drule.PART_MATCH)
