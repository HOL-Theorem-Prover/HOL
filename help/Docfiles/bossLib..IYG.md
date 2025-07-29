## `&&`

``` hol4
op bossLib.&& : simpset * thm list -> simpset
```

------------------------------------------------------------------------

Infix operator for adding theorems into a simpset.

It is occasionally necessary to extend an existing simpset `ss` with a
collection `rwlist` of new rewrite rules. To achieve this, one applies
the `&&` function via `ss && rwlist`.

### Failure

Never fails.

### Example

``` hol4
- open bossLib;
... <output elided> ...
- val ss = boolSimps.bool_ss && pairTheory.pair_rws;
> val ss = <simpset> : simpset
```

### Comments

Of limited applicability since most of the tactics for rewriting already
include this functionality. However, applications of `ZAP_TAC` can
benefit.

### See also

[`simpLib.++`](#simpLib..KAL),
[`simpLib.SIMP_CONV`](#simpLib.SIMP_CONV),
[`bossLib.RW_TAC`](#bossLib.RW_TAC)
