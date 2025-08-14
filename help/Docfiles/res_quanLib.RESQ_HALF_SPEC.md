## `RESQ_HALF_SPEC`

``` hol4
res_quanLib.RESQ_HALF_SPEC : thm -> thm
```

------------------------------------------------------------------------

Strip a restricted universal quantification in the conclusion of a
theorem.

When applied to a theorem `A |- !x::P. t`, the derived inference rule
`RESQ_HALF_SPEC` returns the theorem `A |- !x. x IN P ==> t`, i.e., it
transforms the restricted universal quantification to its underlying
semantic representation.

``` hol4
      A |- !x::P. t
   --------------------  RESQ_HALF_SPEC
    A |- !x. x IN P ==> t
```

### Failure

Fails if the theorem's conclusion is not a restricted universal
quantification.

### See also

[`res_quanLib.RESQ_SPEC`](#res_quanLib.RESQ_SPEC)
