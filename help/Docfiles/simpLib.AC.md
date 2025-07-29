## `AC`

``` hol4
simpLib.AC : thm -> thm -> thm
```

------------------------------------------------------------------------

Packages associativity and commutativity theorems for use in the
simplifier.

The `AC` function combines an associativity and commutativity theorem.
The resulting theorem can be passed to the simplifier as if a rewrite,
but will rather be used by the simplifier as the basis for performing
AC-normalisation.

The theorems can be combined in either order, can be partly generalised,
and need not express associativity in any particular direction from left
to right.

### Failure

`AC` never fails, but if applied to theorems that are not of the
required form, the simplifier will raise an exception when it attempts
to use the result.

### Example

``` hol4
- SIMP_CONV bool_ss [AC ADD_COMM ADD_ASSOC] ``3 + x + y + 1``;
> val it = |- 3 + x + y + 1 = x + (y + (1 + 3)) : thm

- SIMP_CONV bool_ss [AC (GSYM ADD_ASSOC) ADD_COMM] ``x + 1 + y + 3``;
> val it = |- x + 1 + y + 3 = x + (y + (1 + 3)) : thm
```

### See also

[`simpLib.SSFRAG`](#simpLib.SSFRAG)
