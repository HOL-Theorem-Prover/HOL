## `rewrites`

``` hol4
bossLib.rewrites : thm list -> ssfrag
```

------------------------------------------------------------------------

Creates an `ssfrag` value consisting of the given theorems as rewrites.

### Failure

Never fails.

### Example

Instead of writing the simpler `SIMP_CONV std_ss thmlist`, one could
write

``` hol4
   SIMP_CONV (std_ss ++ rewrites thmlist) []
```

More plausibly, `rewrites` can be used to create commonly used `ssfrag`
values containing a great number of rewrites. This is how the basic
system's various `ssfrag` values are constructed where those values
consist only of rewrite theorems.

### See also

[`bossLib.++`](#bossLib..KAL),
[`simpLib.mk_simpset`](#simpLib.mk_simpset),
[`simpLib.SSFRAG`](#simpLib.SSFRAG),
[`bossLib.SIMP_CONV`](#bossLib.SIMP_CONV)
