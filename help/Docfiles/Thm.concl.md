## `concl`

``` hol4
Thm.concl : thm -> term
```

------------------------------------------------------------------------

Returns the conclusion of a theorem.

When applied to a theorem `A |- t`, the function `concl` returns `t`.

### Failure

Never fails.

### See also

[`Thm.dest_thm`](#Thm.dest_thm), [`Thm.hyp`](#Thm.hyp)
