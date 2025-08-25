## `LIST_MK_PEXISTS`

``` hol4
PairRules.LIST_MK_PEXISTS : (term list -> thm -> thm)
```

------------------------------------------------------------------------

Multiply existentially quantifies both sides of an equation using the
given pairs.

When applied to a list of terms `[p1;...;pn]`, where the `pi` are all
paired structures of variables, and a theorem `A |- t1 = t2`, the
inference rule `LIST_MK_PEXISTS` existentially quantifies both sides of
the equation using the pairs given, none of the variables in the pairs
should be free in the assumption list.

``` hol4
                A |- t1 = t2
   --------------------------------------  LIST_MK_PEXISTS ["x1";...;"xn"]
    A |- (?x1...xn. t1) = (?x1...xn. t2)
```

### Failure

Fails if any term in the list is not a paired structure of variables, or
if any variable is free in the assumption list, or if the theorem is not
equational.

### See also

[`Drule.LIST_MK_EXISTS`](#Drule.LIST_MK_EXISTS),
[`PairRules.PEXISTS_EQ`](#PairRules.PEXISTS_EQ),
[`PairRules.MK_PEXISTS`](#PairRules.MK_PEXISTS)
