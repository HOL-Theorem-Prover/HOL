## `EXT`

``` hol4
Drule.EXT : thm -> thm
```

------------------------------------------------------------------------

Derives equality of functions from extensional equivalence.

When applied to a theorem `A |- !x. t1 x = t2 x`, the inference rule
`EXT` returns the theorem `A |- t1 = t2`.

``` hol4
    A |- !x. t1 x = t2 x
   ----------------------  EXT          [where x is not free in t1 or t2]
        A |- t1 = t2
```

### Failure

Fails if the theorem does not have the form indicated above, or if the
variable `x` is free in either of the functions `t1` or `t2`.

### Comments

This rule is expressed as an equivalence in the theorem
`boolTheory.FUN_EQ_THM`.

### See also

[`Thm.AP_THM`](#Thm.AP_THM), [`Drule.ETA_CONV`](#Drule.ETA_CONV),
[`Conv.FUN_EQ_CONV`](#Conv.FUN_EQ_CONV)
