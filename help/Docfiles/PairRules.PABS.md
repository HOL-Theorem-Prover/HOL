## `PABS`

``` hol4
PairRules.PABS : (term -> thm -> thm)
```

------------------------------------------------------------------------

Paired abstraction of both sides of an equation.

``` hol4
         A |- t1 = t2
   ------------------------  ABS "p"            [Where p is not free in A]
    A |- (\p.t1) = (\p.t2)
```

### Failure

If the theorem is not an equation, or if any variable in the paired
structure of variables `p` occurs free in the assumptions `A`.

EXAMPLE

``` hol4
- PABS (Term `(x:'a,y:'b)`) (REFL (Term `(x:'a,y:'b)`));
> val it = |- (\(x,y). (x,y)) = (\(x,y). (x,y)) : thm
```

### See also

[`Thm.ABS`](#Thm.ABS), [`PairRules.PABS_CONV`](#PairRules.PABS_CONV),
[`PairRules.PETA_CONV`](#PairRules.PETA_CONV),
[`PairRules.PEXT`](#PairRules.PEXT),
[`PairRules.MK_PABS`](#PairRules.MK_PABS)
