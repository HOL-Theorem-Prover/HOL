## `mk_simpset`

``` hol4
simpLib.mk_simpset : ssfrag list -> simpset
```

------------------------------------------------------------------------

Creates a simpset by combining a list of `ssfrag` values.

This function creates a `simpset` value by repeatedly adding (as per the
`++` operator) `simpset` fragment values to the base `empty_ss`.

### Failure

Never fails.

Creates simpsets, which are a necessary argument to any simplification
function.

### See also

[`simpLib.++`](#simpLib..KAL), [`simpLib.rewrites`](#simpLib.rewrites),
[`simpLib.SIMP_CONV`](#simpLib.SIMP_CONV)
