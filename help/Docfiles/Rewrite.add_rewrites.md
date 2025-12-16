## `add_rewrites`

``` hol4
Rewrite.add_rewrites : rewrites -> thm list -> rewrites
```

------------------------------------------------------------------------

Add theorems to a collection of rewrite rules.

The function `add_rewrites` processes each element in a list of theorems
and adds the resulting rewrite rules to a value of type `rewrites`.

### Failure

Never fails.

### Example

``` hol4
- load "pairTheory"; open pairTheory;
  add_rewrites empty_rewrites (PAIR_MAP_THM::pair_rws);

> val it =
    |- (f ## g) (x,y) = (f x,g y);
    |- (FST x,SND x) = x;
    |- FST (x,y) = x;
    |- SND (x,y) = y
    Number of rewrite rules = 4
     : rewrites
```

For building bespoke rewrite rule sets.

### See also

[`Rewrite.bool_rewrites`](#Rewrite.bool_rewrites),
[`Rewrite.empty_rewrites`](#Rewrite.empty_rewrites),
[`Rewrite.implicit_rewrites`](#Rewrite.implicit_rewrites),
[`Rewrite.GEN_REWRITE_CONV`](#Rewrite.GEN_REWRITE_CONV),
[`Rewrite.GEN_REWRITE_RULE`](#Rewrite.GEN_REWRITE_RULE),
[`Rewrite.GEN_REWRITE_TAC`](#Rewrite.GEN_REWRITE_TAC)
