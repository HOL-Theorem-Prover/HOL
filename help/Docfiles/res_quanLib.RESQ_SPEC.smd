## `RESQ_SPEC`

``` hol4
res_quanLib.RESQ_SPEC : term -> thm -> thm
```

------------------------------------------------------------------------

Specializes the conclusion of a possibly-restricted universally
quantified theorem.

When applied to a term `u` and a theorem `A |- !x::P. t`, `RESQ_SPEC`
returns the theorem `A, u IN P |- t[u/x]`. If necessary, variables will
be renamed prior to the specialization to ensure that `u` is free for
`x` in `t`, that is, no variables free in `u` become bound after
substitution.

``` hol4
      A |- !x::P. t
   ---------------------  RESQ_SPEC "u"
    A, u IN P |- t[u/x]
```

Additionally, if the input theorem is a standard universal
quantification, then RESQ_SPEC behaves like SPEC.

### Failure

Fails if the theorem's conclusion is not restricted universally
quantified, or if type instantiation fails.

### Example

The following example shows how `RESQ_SPEC` renames bound variables if
necessary, prior to substitution: a straightforward substitution would
result in the clearly invalid theorem `(\y. 0 < y) y |- y = y`.

``` hol4
   > val th = RESQ_GEN ``x:num`` ``\y. 0 < y`` (REFL ``x:num``);
   val th = |- !x :: \y. 0 < y. x = x : thm

   > RESQ_SPEC ``y:num`` th;
   val it = (\y'. 0 < y') y |- y = y : thm
```

### See also

[`res_quanLib.RESQ_HALF_SPECL`](#res_quanLib.RESQ_HALF_SPECL),
[`res_quanLib.RESQ_SPECL`](#res_quanLib.RESQ_SPECL)
