## `NORMEQ_ss`

``` hol4
boolSimps.NORMEQ_ss : ssfrag
```

------------------------------------------------------------------------

A simpset fragment that reorients equalities.

The `NORMEQ_ss` simpset fragment embodies a conversion that flips terms
of the form `l = r` when `l` contains no free variables, and `r`
contains at least one variable. To flip an equality is to rewrite it so
that `l = r` becomes `r = l`.

### Failure

As a static value, this cannot fail.

### Example

In this example, the simplifier flips the `3 = x` term, making it useful
as a rewrite when attacking the consequent of the implication.

``` hol4
   SIMP_CONV (bool_ss ++ boolSimps.NORMEQ_ss) [] ``(3 = x) ==> x + 1 < y``;
   > val it =
      |- (3 = x) ==> x + 1 < y <=> (x = 3) ==> 3 + 1 < y : thm
```

### See also

[`simpLib.SIMP_CONV`](#simpLib.SIMP_CONV)
