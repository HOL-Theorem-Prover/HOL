## `hyp`

``` hol4
Thm.hyp : thm -> term list
```

------------------------------------------------------------------------

Returns the hypotheses of a theorem.

When applied to a theorem `A |- t`, the function `hyp` returns `A`, the
list of hypotheses of the theorem.

### Failure

Never fails.

### Comments

The order in which hypotheses are returned can not be relied on.

### See also

[`Thm.dest_thm`](#Thm.dest_thm), [`Thm.concl`](#Thm.concl)
