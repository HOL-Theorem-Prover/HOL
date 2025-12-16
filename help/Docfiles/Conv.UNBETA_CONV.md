## `UNBETA_CONV`

``` hol4
Conv.UNBETA_CONV : term -> conv
```

------------------------------------------------------------------------

Returns a reversed instance of beta-reduction.

`UNBETA_CONV t1 t2` returns a theorem of the form

``` hol4
   |- t2 = (\v. t') t1
```

The choice of `v` and the nature of `t'` depend on whether or `t1` is a
variable. If so, then `v` will be `t1` and `t'` will be `t2`. Otherwise,
`v` will be generated with `genvar` and `t'` will be the result of
substituting `v` for `t1`, wherever it occurs.

### Failure

Never fails.

### Comments

Very useful for setting up a higher-order match by hand. The use of
`genvar` is predicated on the assumption that it will later be
eliminated through the application of the function term to some other
argument.

### See also

[`Thm.BETA_CONV`](#Thm.BETA_CONV)
