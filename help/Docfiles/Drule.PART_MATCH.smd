## `PART_MATCH`

``` hol4
Drule.PART_MATCH : (term -> term) -> thm -> term -> thm
```

------------------------------------------------------------------------

Instantiates a theorem by matching part of it to a term.

When applied to a 'selector' function of type `term -> term`, a theorem
and a term:

``` hol4
   PART_MATCH fn (A |- !x1...xn. t) tm
```

the function `PART_MATCH` applies `fn` to `t'` (the result of
specializing universally quantified variables in the conclusion of the
theorem), and attempts to match the resulting term to the argument term
`tm`. If it succeeds, the appropriately instantiated version of the
theorem is returned.

### Failure

Fails if the selector function `fn` fails when applied to the
instantiated theorem, or if the match fails with the term it has
provided.

Since `PART_MATCH` will not instantiate variables which appear in the
hypotheses of the given theorem, it fails if the attempted match would
require instantiating these variables. To allow instantiation of these
variables, use `PART_MATCH_A`.

### Example

Suppose that we have the following theorem:

``` hol4
   th = |- !x. x==>x
```

then the following:

``` hol4
   PART_MATCH (fst o dest_imp) th "T"
```

results in the theorem:

``` hol4
   |- T ==> T
```

because the selector function picks the antecedent of the implication
(the inbuilt specialization gets rid of the universal quantifier), and
matches it to `T`.

### See also

[`Drule.PART_MATCH'`](#Drule..BQHIIUJXBNHIJTHRIH),
[`Drule.PART_MATCH_A`](#Drule.PART_MATCH_A),
[`Thm.INST_TYPE`](#Thm.INST_TYPE),
[`Drule.INST_TY_TERM`](#Drule.INST_TY_TERM),
[`Term.match_term`](#Term.match_term)
