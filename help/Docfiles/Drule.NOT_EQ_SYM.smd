## `NOT_EQ_SYM`

``` hol4
Drule.NOT_EQ_SYM : (thm -> thm)
```

------------------------------------------------------------------------

Swaps left-hand and right-hand sides of a negated equation.

When applied to a theorem `A |- ~(t1 = t2)`, the inference rule
`NOT_EQ_SYM` returns the theorem `A |- ~(t2 = t1)`.

``` hol4
    A |- ~(t1 = t2)
   -----------------  NOT_EQ_SYM
    A |- ~(t2 = t1)
```

### Failure

Fails unless the theorem's conclusion is a negated equation.

### See also

[`Conv.DEPTH_CONV`](#Conv.DEPTH_CONV), [`Thm.REFL`](#Thm.REFL),
[`Thm.SYM`](#Thm.SYM)
