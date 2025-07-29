## `HALF_MK_ABS`

``` hol4
jrhUtils.HALF_MK_ABS : (thm -> thm)
```

------------------------------------------------------------------------

Converts a function definition to lambda-form.

When applied to a theorem `A |- !x. t1 x = t2`, whose conclusion is a
universally quantified equation, `HALF_MK_ABS` returns the theorem
`A |- t1 = \x. t2`.

``` hol4
    A |- !x. t1 x = t2
   --------------------  HALF_MK_ABS            [where x is not free in t1]
    A |- t1 = (\x. t2)
```

### Failure

Fails unless the theorem is a singly universally quantified equation
whose left-hand side is a function applied to the quantified variable,
or if the variable is free in that function.

### See also

[`Drule.ETA_CONV`](#Drule.ETA_CONV), [`Drule.MK_ABS`](#Drule.MK_ABS),
[`Thm.MK_COMB`](#Thm.MK_COMB), [`Drule.MK_EXISTS`](#Drule.MK_EXISTS)
