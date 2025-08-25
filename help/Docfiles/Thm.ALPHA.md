## `ALPHA`

``` hol4
Thm.ALPHA : term -> term -> thm
```

------------------------------------------------------------------------

Proves equality of alpha-equivalent terms.

When applied to a pair of terms `t1` and `t1'` which are
alpha-equivalent, `ALPHA` returns the theorem `|- t1 = t1'`.

``` hol4
   -------------  ALPHA  t1  t1'
    |- t1 = t1'
```

### Failure

Fails unless the terms provided are alpha-equivalent.

### See also

[`Term.aconv`](#Term.aconv), [`Drule.ALPHA_CONV`](#Drule.ALPHA_CONV),
[`Drule.GEN_ALPHA_CONV`](#Drule.GEN_ALPHA_CONV)
