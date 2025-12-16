## `RESQ_SPEC`

``` hol4
res_quanTools.RESQ_SPEC : (term -> thm -> thm)
```

------------------------------------------------------------------------

Specializes the conclusion of a restricted universally quantified
theorem.

When applied to a term `u` and a theorem `A |- !x::P. t`, `RESQ_SPEC`
returns the theorem `A, P u |- t[u/x]`. If necessary, variables will be
renamed prior to the specialization to ensure that `u` is free for `x`
in `t`, that is, no variables free in `u` become bound after
substitution.

``` hol4
      A |- !x::P. t
   ------------------  RESQ_SPEC "u"
    A, P u |- t[u/x]
```

### Failure

Fails if the theorem's conclusion is not restricted universally
quantified, or if type instantiation fails.

### Example

The following example shows how `RESQ_SPEC` renames bound variables if
necessary, prior to substitution: a straightforward substitution would
result in the clearly invalid theorem `(\y. 0 < y)y |- y = y`.

``` hol4
   #let th = RESQ_GEN "x:num" "\y.0<y" (REFL "x:num");;
   th = |- !x :: \y. 0 < y. x = x

   #RESQ_SPEC "y:num" th;;
   (\y'. 0 < y')y |- y = y
```

### See also

[`res_quanTools.RESQ_SPECL`](#res_quanTools.RESQ_SPECL)
