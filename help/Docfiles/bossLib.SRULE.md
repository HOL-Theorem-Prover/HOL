## `SRULE`

``` hol4
bossLib.SRULE : thm list -> thm -> thm
```

------------------------------------------------------------------------

Simplification with standard simpset as a derived rule

A call to `SRULE ths th` simplifies the theorem `th` using the standard
simpset (accessible through a call to `srw_ss()`) and the theorems
`ths`, returning the simplified theorem.

The implementation of `SRULE` is

``` hol4
   fun SRULE ths th = SIMP_RULE (srw_ss()) ths th
```

The fact that this definition is not eta-reduced means that partial
applications of `SRULE` will continue to pick up the current value of
`srw_ss()` when they are eventually fully applied, rather than bake in
the value from the time of the partial application.

### Failure

Should never fail.

### See also

[`Conv.CONV_RULE`](#Conv.CONV_RULE),
[`simpLib.SIMP_RULE`](#simpLib.SIMP_RULE),
[`BasicProvers.srw_ss`](#BasicProvers.srw_ss)
