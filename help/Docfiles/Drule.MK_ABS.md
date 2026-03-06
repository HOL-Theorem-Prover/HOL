## `MK_ABS`

``` hol4
Drule.MK_ABS : (thm -> thm)
```

------------------------------------------------------------------------

Abstracts both sides of an equation.

When applied to a theorem `A |- !x. t1 = t2`, whose conclusion is a
universally quantified equation, `MK_ABS` returns the theorem
`A |- \x. t1 = \x. t2`.

``` hol4
        A |- !x. t1 = t2
   --------------------------  MK_ABS
    A |- (\x. t1) = (\x. t2)
```

### Failure

Fails unless the theorem is a (singly) universally quantified equation.

### See also

[`Thm.ABS`](#Thm.ABS), [`jrhUtils.HALF_MK_ABS`](#jrhUtils.HALF_MK_ABS),
[`Thm.MK_COMB`](#Thm.MK_COMB), [`Drule.MK_EXISTS`](#Drule.MK_EXISTS)
