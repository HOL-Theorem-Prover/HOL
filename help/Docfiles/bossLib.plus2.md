## `++`

``` hol4
op bossLib.++ : simpset * ssfrag -> simpset
```

------------------------------------------------------------------------

Infix operator for augmenting simpsets with `ssfrag` values.

The `++` function combines its two arguments and creates a new simpset.
This is a way of creating simpsets that are tailored to the particular
simplification task at hand.

### Failure

Never fails.

### Example

Here we add the `UNWIND_ss` `ssfrag` value to the `pure_ss` simpset to
exploit the former's point-wise elimination conversions.

``` hol4
- SIMP_CONV (pureSimps.pure_ss ++ boolSimps.UNWIND_ss) []
            (Term`!x. x ==> (?y. P(x,y) /\ (y = 5))`);

> val it = |- (!x. x ==> (?y. P (x,y) /\ (y = 5))) = P (T,5) : thm
```

### See also

[`simpLib.mk_simpset`](#simpLib.mk_simpset),
[`simpLib.rewrites`](#simpLib.rewrites),
[`simpLib.SIMP_CONV`](#simpLib.SIMP_CONV),
[`pureSimps.pure_ss`](#pureSimps.pure_ss)
