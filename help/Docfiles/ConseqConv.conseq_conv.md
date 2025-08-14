## `conseq_conv`

``` hol4
ConseqConv.type conseq_conv
```

------------------------------------------------------------------------

A type for functions that given a term produce a theorem with an
implication at the top level.

Classical conversions (see `Conv`) convert a given term `t` to a term
`eqt` that is equal to `t`. For a boolean term `t`, it is however
sometimes useful not to preserve equivalence, but to either strengthen
`t` to `st` or to weaken it to `wt`. The type `conseq_conv` is used for
ML functions that perform these operations. These ML Functions are
called `consequence conversions` in the following.

Given a consequence conversion `CONSEQ_CONV` and a term `t`, then
`CONSEQ_CONV` can either fail with an `HOL_ERR`-exception, raise an
`UNCHANGED`-exception or produce a theorem of one of the following
forms:

``` hol4
   1. st ==> t
   2. t ==> wt
   3. t = eqt
```

### Example

Examples of simple consequence conversion are `TRUE_CONSEQ_CONV` and
`FALSE_CONSEQ_CONV`.

### See also

[`ConseqConv.directed_conseq_conv`](#ConseqConv.directed_conseq_conv),
[`ConseqConv.TRUE_FALSE_REFL_CONSEQ_CONV`](#ConseqConv.TRUE_FALSE_REFL_CONSEQ_CONV)
