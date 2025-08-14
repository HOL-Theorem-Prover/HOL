## `CHANGED_CONSEQ_CONV`

``` hol4
ConseqConv.CHANGED_CONSEQ_CONV : (conseq_conv -> conseq_conv)
```

------------------------------------------------------------------------

Makes a consequence conversion fail if applying it leaves a term
unchanged.

If `c` is a consequence conversion that maps a term ``` ``t`` ``` to a
theorem `|- t = t'`, `|- t' ==> t` or `|- t ==> t'`, where `t'` is
alpha-equivalent to `t`, or if `c` raises the `UNCHANGED` exception when
applied to ``` ``t`` ```, then `CHANGED_CONSEQ_CONV c` fails when
applied to the term ``` ``t`` ```. Otherwise, `CHANGED_CONSEQ_CONV c`
behaves like `c`.

### See also

[`Conv.CHANGED_CONV`](#Conv.CHANGED_CONV),
[`ConseqConv.QCHANGED_CONSEQ_CONV`](#ConseqConv.QCHANGED_CONSEQ_CONV)
