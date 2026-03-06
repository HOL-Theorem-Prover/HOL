## `PSELECT_EQ`

``` hol4
PairRules.PSELECT_EQ : (term -> thm -> thm)
```

------------------------------------------------------------------------

Applies epsilon abstraction to both terms of an equation.

When applied to a paired structure of variables `p` and a theorem whose
conclusion is equational:

``` hol4
    A |- t1 = t2
```

the inference rule `PSELECT_EQ` returns the theorem:

``` hol4
    A |- (@p. t1) = (@p. t2)
```

provided no variable in `p` is free in the assumptions.

``` hol4
         A |- t1 = t2
   --------------------------  SELECT_EQ "p"      [where p is not free in A]
    A |- (@p. t1) = (@p. t2)
```

### Failure

Fails if the conclusion of the theorem is not an equation, of if `p` is
not a paired structure of variables, or if any variable in `p` is free
in `A`.

### See also

[`Drule.SELECT_EQ`](#Drule.SELECT_EQ),
[`PairRules.PFORALL_EQ`](#PairRules.PFORALL_EQ),
[`PairRules.PEXISTS_EQ`](#PairRules.PEXISTS_EQ)
