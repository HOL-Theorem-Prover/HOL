## `PGENL`

``` hol4
PairRules.PGENL : (term list -> thm -> thm)
```

------------------------------------------------------------------------

Generalizes zero or more pairs in the conclusion of a theorem.

When applied to a list of paired variable structures `[p1;...;pn]` and a
theorem `A |- t`, the inference rule `PGENL` returns the theorem
`A |- !p1...pn. t`, provided none of the constituent variables from any
of the pairs `pi` occur free in the assumptions.

``` hol4
         A |- t
   ------------------  PGENL "[p1;...;pn]"       [where no pi is free in A]
    A |- !p1...pn. t
```

### Failure

Fails unless all the terms in the list are paired structures of
variables, none of the variables from which are free in the assumption
list.

### See also

[`Thm.GENL`](#Thm.GENL), [`PairRules.PGEN`](#PairRules.PGEN),
[`PairRules.PGEN_TAC`](#PairRules.PGEN_TAC),
[`PairRules.PSPEC`](#PairRules.PSPEC),
[`PairRules.PSPECL`](#PairRules.PSPECL),
[`PairRules.PSPEC_ALL`](#PairRules.PSPEC_ALL),
[`PairRules.PSPEC_TAC`](#PairRules.PSPEC_TAC)
