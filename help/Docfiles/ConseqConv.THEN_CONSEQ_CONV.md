## `THEN_CONSEQ_CONV`

``` hol4
ConseqConv.THEN_CONSEQ_CONV : (conseq_conv -> conseq_conv -> conseq_conv)
```

------------------------------------------------------------------------

Applies two consequence conversions in sequence.

`THEN_CONSEQ_CONV cc1 cc2` corresponds to `c1 THENC c2` for classical
conversions. Thus, if `cc1` returns `|- t' ==> t` when applied to `t`,
and `cc2` returns `|- t'' ==> t'` when applied to `t'`, then
`(THEN_CONSEQ_CONV cc1 cc2) t` returns `|- t'' ==> t`.
`THEN_CONSEQ_CONV` can handle weakening as well: If `cc1` returns
`|- t ==> t'` when applied to `t`, and `cc2` returns `|- t' ==> t''`
when applied to `t'`, then `(THEN_CONSEQ_CONV cc1 cc2) t` returns
`|- t ==> t''`. Finally, if `cc1` returns `|- t = t'` when applied to
`t`, and `cc2` returns `|- t' = t''` when applied to `t'`, then
`(THEN_CONSEQ_CONV cc1 cc2) t` returns `|- t = t''`. If one of the
conversions returns an equation, while the other returns an implication,
the needed implication is automatically deduced.

### See also

[`Conv.THENC`](#Conv.THENC),
[`ConseqConv.EVERY_CONSEQ_CONV`](#ConseqConv.EVERY_CONSEQ_CONV)
