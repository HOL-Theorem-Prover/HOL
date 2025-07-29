## `STRENGTHEN_CONSEQ_CONV_RULE`

``` hol4
ConseqConv.STRENGTHEN_CONSEQ_CONV_RULE : directed_conseq_conv -> thm -> thm
```

------------------------------------------------------------------------

Tries to strengthen the antecedent of a theorem consisting of an
implication.

Given a theorem of the form `|- A ==> C` and a directed consequence
conversion `c` a call of `STRENGTHEN_CONSEQ_CONV_RULE c thm` tries to
strengthen `A` to a predicate `sA` using `c`. If it succeeds it returns
the theorem `|- sA ==> C`.

### See also

[`ConseqConv.WEAKEN_CONSEQ_CONV_RULE`](#ConseqConv.WEAKEN_CONSEQ_CONV_RULE)
