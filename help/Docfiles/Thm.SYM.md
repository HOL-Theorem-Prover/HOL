## `SYM`

``` hol4
Thm.SYM : thm -> thm
```

------------------------------------------------------------------------

Swaps left-hand and right-hand sides of an equation.

When applied to a theorem `A |- t1 = t2`, the inference rule `SYM`
returns `A |- t2 = t1`.

``` hol4
    A |- t1 = t2
   --------------  SYM
    A |- t2 = t1
```

### Failure

Fails unless the theorem is equational.

### See also

[`Conv.GSYM`](#Conv.GSYM), [`Drule.NOT_EQ_SYM`](#Drule.NOT_EQ_SYM),
[`Thm.REFL`](#Thm.REFL), [`Tacic.SYM_TAC`](#Tacic.SYM_TAC)
