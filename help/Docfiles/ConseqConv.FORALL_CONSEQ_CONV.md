## `FORALL_CONSEQ_CONV`

``` hol4
ConseqConv.FORALL_CONSEQ_CONV : (conseq_conv -> conseq_conv)
```

------------------------------------------------------------------------

Applies a consequence conversion to the body of a universally-quantified
term.

If `c` is a consequence conversion that maps a term ``` ``t x`` ``` to a
theorem `|- t x = t' x`, `|- t' x ==> t x` or `|- t x ==> t' x`, then
`FORALL_CONSEQ_CONV c` maps ``` ``!x. t x`` ``` to
`|- !x. t x = !x. t' x`, `|- !x. t' x ==> !x. t x` or
`|- !x. t x ==> !x. t' x`, respectively.

### Failure

`FORALL_CONSEQ_CONV c t` fails, if `t` is not an all-quantified term or
if `c` fails on the body of `t`.

### See also

[`Conv.QUANT_CONV`](#Conv.QUANT_CONV),
[`ConseqConv.EXISTS_CONSEQ_CONV`](#ConseqConv.EXISTS_CONSEQ_CONV),
[`ConseqConv.QUANT_CONSEQ_CONV`](#ConseqConv.QUANT_CONSEQ_CONV)
