## `REFL`

``` hol4
Thm.REFL : conv
```

------------------------------------------------------------------------

Returns theorem expressing reflexivity of equality.

`REFL` maps any term `t` to the corresponding theorem `|- t = t`.

### Failure

Never fails.

### See also

[`Conv.ALL_CONV`](#Conv.ALL_CONV), [`Tactic.REFL_TAC`](#Tactic.REFL_TAC)
