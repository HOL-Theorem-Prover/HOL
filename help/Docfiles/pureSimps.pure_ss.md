## `pure_ss`

``` hol4
pureSimps.pure_ss : simpset
```

------------------------------------------------------------------------

A simpset containing only the conditional rewrite generator and no
additional rewrites.

This simpset sits at the root of the simpset hierarchy. It contains no
rewrites, congruences, conversions or decision procedures. Instead it
contains just the code which converts theorems passed to it as context
into (possibly conditional) rewrites.

Simplification with `pure_ss` is analogous to rewriting with
`PURE_REWRITE_TAC` and others. The only difference is that the theorems
passed to `SIMP_TAC pure_ss` are interpreted as conditional rewrite
rules. Though the `pure_ss` can't take advantage of extra contextual
information garnered through congruences, it can still discharge side
conditions. (This is demonstrated in the examples below.)

### Failure

Can't fail, as it is not a functional value.

### Example

The theorem `ADD_EQ_SUB` from `arithmeticTheory` states that

``` hol4
   |- !m n p. n <= p ==> ((m + n = p) = m = p - n)
```

We can use this result to make progress with the following goal in
conjunction with `pure_ss` in a way that no form of `REWRITE_TAC` could:

``` hol4
   - ASM_SIMP_TAC pure_ss [ADD_EQ_SUB] ([“x <= y”], “z + x = y”);
   > val it = ([([`x <= y`], `z = y - x`)], fn) : tactic_result
```

This example illustrates the way in which the simplifier can do
conditional rewriting. However, the lack of the congruence for
implications means that using `pure_ss` will not be able to discharge
the side condition in the goal below:

``` hol4
   - SIMP_TAC pure_ss [ADD_EQ_SUB] ([], “x <= y ==> (z + x = y)”);
   > val it = ([([], `x <= y ==> (z + x = y)`)], fn) : tactic_result
```

As `bool_ss` has the relevant congruence included, it does make progress
in the same situation:

``` hol4
   - SIMP_TAC bool_ss [ADD_EQ_SUB] ([], “x <= y ==> (z + x = y)”);
   > val it = ([([], `x <= y ==> (z = y - x)`)], fn) : tactic_result
```

The `pure_ss` simpset might be used in the most delicate simplification
situations, or, mimicking the way it is used within the distribution
itself, as a basis for the construction of other simpsets.

### Comments

There is also a `pureSimps.PURE_ss` `ssfrag` value. Its usefulness is
questionable.

### See also

[`boolSimps.bool_ss`](#boolSimps.bool_ss),
[`Rewrite.PURE_REWRITE_TAC`](#Rewrite.PURE_REWRITE_TAC),
[`simpLib.SIMP_CONV`](#simpLib.SIMP_CONV),
[`simpLib.SIMP_TAC`](#simpLib.SIMP_TAC)
