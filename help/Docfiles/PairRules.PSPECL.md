## `PSPECL`

``` hol4
PairRules.PSPECL : (term list -> thm -> thm)
```

------------------------------------------------------------------------

Specializes zero or more pairs in the conclusion of a theorem.

When applied to a term list `[q1;...;qn]` and a theorem
`A |- !p1...pn. t`, the inference rule `SPECL` returns the theorem
`A |- t[q1/p1]...[qn/pn]`, where the substitutions are made sequentially
left-to-right in the same way as for `PSPEC`.

``` hol4
       A |- !p1...pn. t
   --------------------------  SPECL "[q1;...;qn]"
     A |- t[q1/p1]...[qn/pn]
```

It is permissible for the term-list to be empty, in which case the
application of `PSPECL` has no effect.

### Failure

Fails unless each of the terms is of the same type as that of the
appropriate quantified variable in the original theorem. Fails if the
list of terms is longer than the number of quantified pairs in the
theorem.

### See also

[`Drule.SPECL`](#Drule.SPECL), [`PairRules.PGEN`](#PairRules.PGEN),
[`PairRules.PGENL`](#PairRules.PGENL),
[`PairRules.PGEN_TAC`](#PairRules.PGEN_TAC),
[`PairRules.PSPEC`](#PairRules.PSPEC),
[`PairRules.PSPEC_ALL`](#PairRules.PSPEC_ALL),
[`PairRules.PSPEC_TAC`](#PairRules.PSPEC_TAC)
