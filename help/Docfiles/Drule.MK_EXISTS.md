## `MK_EXISTS`

``` hol4
Drule.MK_EXISTS : (thm -> thm)
```

------------------------------------------------------------------------

Existentially quantifies both sides of a universally quantified
equational theorem.

When applied to a theorem `A |- !x. t1 = t2`, the inference rule
`MK_EXISTS` returns the theorem `A |- (?x. t1) = (?x. t2)`.

``` hol4
       A |- !x. t1 = t2
   --------------------------  MK_EXISTS
    A |- (?x. t1) = (?x. t2)
```

### Failure

Fails unless the theorem is a singly universally quantified equation.

### See also

[`Thm.AP_TERM`](#Thm.AP_TERM), [`Drule.EXISTS_EQ`](#Drule.EXISTS_EQ),
[`Thm.GEN`](#Thm.GEN), [`Drule.LIST_MK_EXISTS`](#Drule.LIST_MK_EXISTS),
[`Drule.MK_ABS`](#Drule.MK_ABS)
